import Mtg.Engine
import Mtg.Demo.Render
import Mtg.Demo.RenderTests
import Mtg.Demo.WelcomeDecks

/-!
# Mtg.Demo

Console demonstration of `Mtg.Engine`. Default mode runs a scripted game with a
heuristic agent using The Hobbit Welcome Decks. Repeat `--name NAME` and
`--deck COLOR` once per player (paired in order; default Chandra red and Nissa
green). Pass `--interactive` to play as the first named player against
heuristic-controlled opponents, or `--multiplayer` to issue every player's
actions from the console. `--decides NAME` names the player who chooses who
takes the first turn (CR 103.1); by default one player is chosen at random
using `--seed`. In interactive modes that player uses `first <name>` before
opening hands are drawn, unless a heuristic opponent is deciding and chooses
to go first. `visible` prints only information that player can see; `--visible`
starts in that view. `--input FILE` runs commands from the file first, then
reads from the console. Lines that start with `--` are additional flags
instead of commands; when `--output` is a different file those flags are
written first. `--output FILE` writes accepted game-state commands
(from the file or the console) to that file. Incorrect commands and session
commands such as `state` and `quit` are omitted. When `--input` and
`--output` are the same file, those flags and commands are replayed and new
accepted console commands are appended. `autopay` is recorded as the individual
`tap` and `pay` commands it performs. `attach <id>` attaches an Equipment
you control when a spell asks you to. After scripted input is exhausted, a
cost with only one legal payment is paid automatically (`tap`, `pay`,
`sacrifice`) and a unique legal target is announced automatically as a
`target` command.
-/

open Mtg.Engine
open Mtg.Engine.Game
open Mtg.Demo
open Mtg.Demo.Render

def usage : String :=
  "Mtg.Demo — demonstration of the Mtg.Engine rules engine

Usage:
  lake exe mtg-demo [--auto | --interactive | --multiplayer] [--visible]
                    [--decides NAME] [--input FILE] [--output FILE]
                    [--seed N] [--fuel N]
                    [--name NAME --deck COLOR]...

Options:
  --auto          Run a heuristic game (default)
  --interactive   Play as the first named player; others are heuristic
  --multiplayer   Control every player from the console
  --visible       With --interactive or --multiplayer, hide information the
                  acting player cannot see
  --decides NAME  Player who chooses who takes the first turn (CR 103.1);
                  default is a random player using --seed
  --input FILE    With --interactive or --multiplayer, run these commands
                  first, then read from the console. Lines that start
                  with -- are additional flags instead of commands
  --output FILE   With --interactive or --multiplayer, write accepted
                  game-state commands (from --input and from the console)
                  to this file. Flags from --input are written first when
                  this path is different from --input. Incorrect commands and session commands
                  such as state and quit are omitted.
                  The same path as --input replays that file and appends
                  new commands. Unique automatic cost payments are written
                  as tap, pay, and sacrifice commands
  --seed N        RNG seed (default 20260807)
  --fuel N        Maximum heuristic actions (default 800)
  --name NAME     Player name (repeat once per player)
  --deck COLOR    That player's Hobbit Welcome Deck (repeat once per player)
  --help          Show this help

COLOR is white, blue, black, red, or green (also W, U, B, R, G). Repeat
`--name` and `--deck` the same number of times; they pair in order. Default
is Chandra (red) and Nissa (green). A game needs at least two players
(CR 100.1). Decklists:
https://magic.wizards.com/en/news/announcements/the-hobbit-welcome-decks

The engine follows the Magic: The Gathering Comprehensive Rules
effective 7 August 2026.

At the start of a game, one player is chosen to decide who takes the
first turn (CR 103.1). `--decides NAME` names that player; the default
is a random player chosen using --seed. In --interactive, the first
named player chooses with `first <name>` when they are deciding; a
heuristic opponent otherwise chooses to go first. In --multiplayer,
the deciding player chooses with `first <name>`. In --auto, the
deciding player (heuristic) chooses to go first.
"

/-- A named player and the Hobbit Welcome Deck they sit with. -/
structure DemoPlayer where
  name : String
  color : Color
deriving Repr, Inhabited, DecidableEq

/-- Default table: Chandra (red) and Nissa (green). -/
def defaultDemoPlayers : Array DemoPlayer := #[
  { name := "Chandra", color := .red },
  { name := "Nissa", color := .green }
]

/-- Seat list from named players and their Welcome Deck colors. -/
def seatsFromPlayers (players : Array DemoPlayer) : Array Seat :=
  players.map (fun p => { name := p.name, deck := hobbitDeck p.color })

/-- Default seats: Chandra red, Nissa green. -/
def demoSeats : Array Seat := seatsFromPlayers defaultDemoPlayers

/-- First listed player of the same name, ignoring case. -/
def duplicatePlayerName? (players : Array DemoPlayer) : Option String :=
  Id.run do
    for i in [0:players.size] do
      let lower := players[i]!.name.map Char.toLower
      for j in [i+1:players.size] do
        if players[j]!.name.map Char.toLower == lower then
          return some players[i]!.name
    return none

/-- Pair `--name` / `--deck` flags into seats, or the default two-player table. -/
def playersFromFlags (names : Array String) (decks : Array Color) :
    Except String (Array DemoPlayer) := do
  if names.isEmpty && decks.isEmpty then
    return defaultDemoPlayers
  if names.size != decks.size then
    throw s!"--name and --deck must be given the same number of times (got {names.size} names and {decks.size} decks)"
  if names.size < 2 then
    throw "A game needs at least two players (CR 100.1)"
  let players := names.mapIdx (fun i n => { name := n, color := decks[i]! })
  match duplicatePlayerName? players with
  | some name => throw s!"Duplicate player name: {name}"
  | none => return players

/-- `startingPlayer` is the seat that takes the first turn after CR 103.1. -/
def demoConfig (seed : UInt64) (startingPlayer : Option Nat := some 0)
    (players : Array DemoPlayer := defaultDemoPlayers) : StartConfig := {
  seats := seatsFromPlayers players
  format := .limited
  seed := seed
  startingPlayer := startingPlayer
}

/-- Usage for the CR 103.1 `first` command, listing legal player names. -/
def firstUsage (seats : Array Seat) : String :=
  let names := String.intercalate " or " (seats.toList.map (·.name))
  s!"usage: first <name> ({names})"

/-- Drop empty tokens from a command line. -/
def commandTokens (tokens : List String) : List String :=
  tokens.filter (fun t => !t.isEmpty)

/-- Seat index of a player name, ignoring case. -/
def parsePlayerName (seats : Array Seat) (name : String) : Except String Nat :=
  let lower := name.map Char.toLower
  match seats.findIdx? (fun s => s.name.map Char.toLower == lower) with
  | some i => .ok i
  | none => .error s!"No player named {name}"

/-- Seat index of the player who takes the first turn (CR 103.1). -/
def parseFirstPlayer (seats : Array Seat) (tokens : List String) : Except String Nat :=
  match commandTokens tokens with
  | [name] => parsePlayerName seats name
  | _ => .error (firstUsage seats)

/-- Who decides who takes the first turn (CR 103.1). `none` means the RNG
picks a seat from `players` using `seed`. -/
def assignDecider (players : Array DemoPlayer) (seed : UInt64) (specified : Option Nat) : Nat :=
  match specified with
  | some i => i
  | none =>
    match players.size with
    | 0 => 0
    | n =>
      let (_, r) := (Rng.ofSeed seed).next
      r.toNat % n

/-- True when the console user issues `first <name>` for this decider. -/
def humanChoosesFirst (interactive : Bool) (multiplayer : Bool) (decider : Nat) : Bool :=
  interactive && (multiplayer || decider == 0)

/-- Console line naming the player who chooses who takes the first turn. -/
def describeFirstChooser (players : Array DemoPlayer) (decider : Nat) (atRandom : Bool) : String :=
  let name := players[decider]!.name
  if atRandom then
    s!"{name} is chosen at random to decide who takes the first turn (CR 103.1)."
  else
    s!"{name} will choose who takes the first turn (CR 103.1)."

/-- Heuristic deciders always take the first turn themselves. -/
def heuristicChoseToGoFirst (name : String) : String :=
  s!"{name} chooses to take the first turn."

/-- Print the CR 103.1 chooser, and either the heuristic's choice or `first` usage. -/
def printFirstChooser (players : Array DemoPlayer) (decider : Nat)
    (atRandom : Bool) (agentChooses : Bool) : IO Unit := do
  IO.println (describeFirstChooser players decider atRandom)
  if agentChooses then
    IO.println (heuristicChoseToGoFirst players[decider]!.name)
  else
    for p in players do
      IO.println s!"  first {p.name}"
  IO.println ""

#guard
  match parsePlayerName demoSeats "Chandra" with
  | .ok 0 => true
  | _ => false

#guard
  match parsePlayerName demoSeats "nissa" with
  | .ok 1 => true
  | _ => false

#guard
  match parsePlayerName demoSeats "Frodo" with
  | .error msg => msg == "No player named Frodo"
  | .ok _ => false

#guard assignDecider defaultDemoPlayers 1 (some 1) == 1
#guard assignDecider defaultDemoPlayers 1 (some 0) == 0
#guard assignDecider defaultDemoPlayers 1 none == assignDecider defaultDemoPlayers 1 none
#guard assignDecider defaultDemoPlayers 1 none < 2

#guard
  let picks := (List.range 64).map (fun n =>
    assignDecider defaultDemoPlayers (UInt64.ofNat n) none)
  picks.all (fun i => i < 2) && picks.any (fun i => i == 0) && picks.any (fun i => i == 1)

#guard humanChoosesFirst true false 0
#guard !humanChoosesFirst true false 1
#guard humanChoosesFirst true true 1
#guard !humanChoosesFirst false false 0
#guard !humanChoosesFirst false true 0

#guard describeFirstChooser defaultDemoPlayers 0 true ==
  "Chandra is chosen at random to decide who takes the first turn (CR 103.1)."
#guard describeFirstChooser defaultDemoPlayers 1 false ==
  "Nissa will choose who takes the first turn (CR 103.1)."
#guard heuristicChoseToGoFirst "Nissa" == "Nissa chooses to take the first turn."

#guard firstUsage demoSeats == "usage: first <name> (Chandra or Nissa)"

#guard
  match parseFirstPlayer demoSeats ["Chandra"] with
  | .ok 0 => true
  | _ => false

#guard
  match parseFirstPlayer demoSeats ["nissa"] with
  | .ok 1 => true
  | _ => false

#guard
  match parseFirstPlayer demoSeats ["Nissa"] with
  | .ok 1 => true
  | _ => false

#guard
  match parseFirstPlayer demoSeats ["Frodo"] with
  | .error msg => msg == "No player named Frodo"
  | .ok _ => false

#guard
  match parseFirstPlayer demoSeats [] with
  | .error msg => msg == firstUsage demoSeats
  | .ok _ => false

#guard
  match parseFirstPlayer demoSeats ["Chandra", "Nissa"] with
  | .error msg => msg == firstUsage demoSeats
  | .ok _ => false

#guard
  match Start.start (demoConfig 1 (some 1)) with
  | .ok g =>
    g.startingPlayer == ⟨1⟩ &&
    g.pending == .declareMulligan ⟨1⟩ &&
    g.actor == some ⟨1⟩ &&
    (g.player ⟨1⟩).name == "Nissa" &&
    g.log.any (· == "Starting player: Nissa")
  | .error _ => false

#guard
  match Start.start (demoConfig 1) with
  | .ok g =>
    g.startingPlayer == ⟨0⟩ &&
    g.pending == .declareMulligan ⟨0⟩
  | .error _ => false

#guard demoSeats[0]!.deck.any (fun c => c.name == "Smaug, the Great Calamity")
#guard demoSeats[1]!.deck.any (fun c => c.name == "Elvish Archdruid")

def elspethJace : Array DemoPlayer := #[
  { name := "Elspeth", color := .white },
  { name := "Jace", color := .blue }
]

def elspethJaceLiliana : Array DemoPlayer := #[
  { name := "Elspeth", color := .white },
  { name := "Jace", color := .blue },
  { name := "Liliana", color := .black }
]

#guard (seatsFromPlayers elspethJace)[0]!.name == "Elspeth"
#guard (seatsFromPlayers elspethJace)[1]!.name == "Jace"
#guard (seatsFromPlayers elspethJace)[0]!.deck.any (fun c => c.name == "Bofur, Reliable Guardian")
#guard (seatsFromPlayers elspethJace)[1]!.deck.any (fun c => c.name == "Bilbo Baggins, Burglar")
#guard (seatsFromPlayers #[
    { name := "Liliana", color := .black },
    { name := "Chandra", color := .red }])[0]!.deck.any
  (fun c => c.name == "Gollum, Silent Slinker")
#guard (seatsFromPlayers #[
    { name := "Liliana", color := .black },
    { name := "Chandra", color := .red }])[1]!.deck.any
  (fun c => c.name == "Smaug, the Great Calamity")
#guard (seatsFromPlayers #[
    { name := "Nissa", color := .green },
    { name := "Elspeth", color := .white }])[0]!.deck.any
  (fun c => c.name == "Elvish Archdruid")
#guard firstUsage (seatsFromPlayers elspethJaceLiliana) ==
  "usage: first <name> (Elspeth or Jace or Liliana)"
#guard describeFirstChooser elspethJaceLiliana 2 true ==
  "Liliana is chosen at random to decide who takes the first turn (CR 103.1)."
#guard
  let picks := (List.range 64).map (fun n =>
    assignDecider elspethJaceLiliana (UInt64.ofNat n) none)
  picks.all (fun i => i < 3) &&
    picks.any (fun i => i == 0) &&
    picks.any (fun i => i == 1) &&
    picks.any (fun i => i == 2)
#guard (duplicatePlayerName? defaultDemoPlayers).isNone
#guard duplicatePlayerName? #[
    { name := "Jace", color := .blue },
    { name := "jace", color := .white }] == some "Jace"

#guard
  match playersFromFlags #[] #[] with
  | .ok ps => ps == defaultDemoPlayers
  | .error _ => false

#guard
  match playersFromFlags #["Elspeth", "Jace"] #[.white, .blue] with
  | .ok ps => ps == elspethJace
  | .error _ => false

#guard
  match playersFromFlags #["Elspeth"] #[.white] with
  | .error msg => msg == "A game needs at least two players (CR 100.1)"
  | .ok _ => false

#guard
  match playersFromFlags #["Elspeth", "Jace"] #[.white] with
  | .error msg =>
    msg == "--name and --deck must be given the same number of times (got 2 names and 1 decks)"
  | .ok _ => false

#guard
  match playersFromFlags #["Jace", "jace"] #[.blue, .white] with
  | .error msg => msg == "Duplicate player name: Jace"
  | .ok _ => false

#guard
  match Start.start (demoConfig 1 (some 0) elspethJaceLiliana) with
  | .ok g =>
    g.players.size == 3 &&
    (g.player ⟨0⟩).name == "Elspeth" &&
    (g.player ⟨1⟩).name == "Jace" &&
    (g.player ⟨2⟩).name == "Liliana" &&
    g.objects.any (fun o => o.name == "Bofur, Reliable Guardian") &&
    g.objects.any (fun o => o.name == "Bilbo Baggins, Burglar") &&
    g.objects.any (fun o => o.name == "Gollum, Silent Slinker") &&
    !g.objects.any (fun o => o.name == "Smaug, the Great Calamity")
  | .error _ => false

#guard
  match Start.start (demoConfig 1 (some 0) #[
      { name := "Elspeth", color := .white },
      { name := "Liliana", color := .black }]) with
  | .ok g =>
    g.objects.any (fun o => o.name == "Bofur, Reliable Guardian") &&
    g.objects.any (fun o => o.name == "Gollum, Silent Slinker") &&
    !g.objects.any (fun o => o.name == "Smaug, the Great Calamity")
  | .error _ => false

def printLog (g : Game) (startIdx : Nat) (viewer : Option PlayerId := none) : IO Nat := do
  for line in newLog g startIdx viewer do
    IO.println s!"  {line}"
  return g.log.size

/-- Print each zone whose occupants, battlefield status, or stack targets
changed. -/
def printChangedZones (before after : Game) (viewer : Option PlayerId := none) : IO Unit := do
  for z in changedZones before after do
    for line in (zoneBlock after z viewer).splitOn "\n" do
      IO.println s!"  {line}"

/-- Print each player's life total when it changed. -/
def printChangedLife (before after : Game) : IO Unit := do
  for pl in changedLifeTotals before after do
    IO.println s!"  {lifeLine pl}"

/-- Print each player's mana pool when it changed. -/
def printChangedMana (before after : Game) : IO Unit := do
  for pl in changedManaPools before after do
    IO.println s!"  {manaLine pl}"

/-- Print the locked-in cost while it still needs to be paid (CR 601.2h). -/
def printPendingCost (g : Game) : IO Unit := do
  match pendingCostLine g with
  | some line => IO.println s!"  {line}"
  | none => pure ()

/-- Print how much combat damage each creature must assign and to whom. -/
def printCombatAssignment (g : Game) : IO Unit := do
  match combatDamageAssignmentBlock g with
  | some block =>
    for line in block.splitOn "\n" do
      IO.println s!"  {line}"
  | none => pure ()

/-- Print which legendary permanents the acting player may keep. -/
def printLegendRule (g : Game) : IO Unit := do
  match legendRuleBlock g with
  | some block =>
    for line in block.splitOn "\n" do
      IO.println s!"  {line}"
  | none => pure ()

/-- Print which triggered abilities the acting player must put on the stack. -/
def printTriggerOrder (g : Game) : IO Unit := do
  match triggerOrderBlock g with
  | some block =>
    for line in block.splitOn "\n" do
      IO.println s!"  {line}"
  | none => pure ()

/-- Pending cost, combat-damage assignment, legend-rule, or trigger order. -/
def printPendingPrompt (g : Game) : IO Unit := do
  printPendingCost g
  printCombatAssignment g
  printLegendRule g
  printTriggerOrder g

/-- Print log, zone, life, mana, and pending-prompt updates after a step. -/
def refreshAfterStep (before after : Game) (seen : Nat)
    (viewer : Option PlayerId := none) : IO Nat := do
  let seen ← printLog after seen viewer
  printChangedZones before after viewer
  printChangedLife before after
  printChangedMana before after
  printPendingPrompt after
  return seen

def printState (g : Game) (viewer : Option PlayerId := none) : IO Unit := do
  IO.println ""
  IO.println (snapshot g viewer)
  IO.println ""

def printEngineBanner : IO Unit := do
  IO.println Mtg.Engine.identification
  IO.println s!"Rules source: {Rules.sourceUrl}"
  IO.println ""

/-- Announce which Hobbit Welcome Deck each player is using. -/
def printDeckAssignments (players : Array DemoPlayer) : IO Unit := do
  for p in players do
    IO.println s!"{p.name} uses the {p.color.englishName} Hobbit Welcome Deck."
  IO.println ""

/-- Create the demo game after the starting player is known (CR 103.1). -/
def startGame (seed : UInt64) (startingPlayer : Option Nat := some 0)
    (players : Array DemoPlayer := defaultDemoPlayers) : IO Game := do
  match Start.start (demoConfig seed startingPlayer players) with
  | .error e =>
    IO.eprintln s!"Failed to start game: {e}"
    throw (IO.userError e)
  | .ok g => return g

/-- Print the opening log and board after the game has started. -/
def printOpening (g : Game) (viewer : Option PlayerId := none) : IO Unit := do
  let _ ← printLog g 0 viewer
  printState g viewer

/-- Start a demo game and print the opening snapshot. The starting player is
the seat chosen under CR 103.1. Banner, decks, and the chooser announcement
are printed first. -/
def startDemo (seed : UInt64) (startingPlayer : Option Nat := some 0)
    (viewer : Option PlayerId := none)
    (players : Array DemoPlayer := defaultDemoPlayers) : IO Game := do
  let g ← startGame seed startingPlayer players
  printOpening g viewer
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
      seen ← refreshAfterStep g g' seen
      g := g'
  printState g
  match g.result with
  | some (.won p) => IO.println s!"Winner: {g.player p |>.name}"
  | some .draw => IO.println "The game is a draw."
  | none => IO.println s!"Stopped after {fuel} actions (turn {g.turnNumber})."

def helpInteractive (controlAll : Bool := false)
    (you : String := "the first player") : String :=
  let viewWho := if controlAll then "the acting player" else you
  s!"Commands:
  help                 Show this help
  first <name>         Choose who takes the first turn (CR 103.1)
  state                Print the board
  visible              Print only information {viewWho} can see (CR 400.2)
  visible on           Use {viewWho}'s view for state and later updates
  visible off          Show full information in state and later updates
  keep                 Keep this opening hand (CR 103.5)
  keep <id>            Choose which legendary permanent to keep (CR 704.5j)
  stack <id> [id...]   Put waiting triggered abilities on the stack in that source order (CR 603.3b)
  mulligan             Declare a mulligan; taken after all declarations
  bottom <id> [id...]  Put cards on the bottom after a mulligan
  pass                 Pass priority
  pay                  Pay a proposed spell or ability's cost (CR 601.2h)
  autopay              Tap mana sources and pay the current cost (CR 601.2g–h)
  pay-extra            Pay extra generic mana as an additional cost (CR 601.2b)
  sacrifice <id>       Sacrifice a creature or artifact to pay a cost, a creature a resolved trigger requires, or a creature as a resolving effect
  sacrifice            Choose to sacrifice as an additional cost (CR 601.2b)
  play <id>            Play a land
  tap <id> [id...] [color]  Tap listed permanents for mana (optional W/U/B/R/G)
  activate <id> [n]    Begin activating an ability (permanent, hand, or graveyard; then tap for mana and pay). n is 1-based when a card has more than one
  mode <n>             Choose a mode for a modal spell or ability (CR 601.2b / 700.2)
  cast <id>            Begin casting a spell (CR 601.2a)
  cast <id> adventure  Cast an adventurer card as its Adventure (CR 715.3)
  target <id|name|opponent> [n] ...  Announce every target of one “target” word together (CR 601.2c); n is damage when dividing (CR 601.2d)
  scry                 Finish scrying; keep looked-at cards on top
  scry top <id>...     Put listed cards on top (last = new top); rest go to the bottom
  scry bottom <id>...  Put listed cards on the bottom (first = new bottom); rest stay on top
  scry top <id>... bottom <id>...  Choose both piles and their orders (CR 701.20)
  discard <id>         Discard a card; if you do, draw (CR 701.9)
  attach <id>          Attach that Equipment you control
  decline              Decline an optional discard, attach, or choose no target
  attack               Attack with every creature that can
  attack <id> [id...]  Attack with the listed creatures
  noattack             Declare no attackers
  block                Block each attacker with a legal unused blocker
  block <b> <a> [...]  Assign listed blocker/attacker pairs
  noblock              Declare no blockers
  assign               Use the default combat damage assignment (CR 510.1)
  assign <s> <t> <n> [...]  Divide combat damage: source, creature or defending player, amount (CR 510.1c–d)
  concede              Concede
  quit                 Exit
"

#guard ((helpInteractive false).splitOn "visible").length > 1
#guard ((helpInteractive false).splitOn "the first player can see").length > 1
#guard ((helpInteractive false "Chandra").splitOn "Chandra can see").length > 1
#guard ((helpInteractive true).splitOn "the acting player can see").length > 1
#guard ((helpInteractive false).splitOn "tap <id> [id...]").length > 1
#guard ((helpInteractive false).splitOn "scry bottom").length > 1
#guard ((helpInteractive false).splitOn "scry top").length > 1
#guard ((helpInteractive false).splitOn "target <id|name|opponent>").length > 1
#guard ((helpInteractive false).splitOn "together").length > 1
#guard ((helpInteractive false).splitOn "CR 601.2d").length > 1
#guard ((helpInteractive false).splitOn "mode <n>").length > 1
#guard ((helpInteractive false).splitOn "cast <id> adventure").length > 1
#guard ((helpInteractive false).splitOn "activate <id> [n]").length > 1
#guard ((helpInteractive false).splitOn "CR 715.3").length > 1
#guard ((helpInteractive false).splitOn "assign <s> <t> <n>").length > 1
#guard ((helpInteractive false).splitOn "defending player").length > 1
#guard ((helpInteractive false).splitOn "first <name>").length > 1
#guard ((helpInteractive false).splitOn "CR 103.1").length > 1
#guard ((helpInteractive false).splitOn "keep <id>").length > 1
#guard ((helpInteractive false).splitOn "CR 704.5j").length > 1
#guard ((helpInteractive false).splitOn "stack <id>").length > 1
#guard ((helpInteractive false).splitOn "CR 603.3b").length > 1
#guard ((helpInteractive false).splitOn "discard <id>").length > 1
#guard ((helpInteractive false).splitOn "attach <id>").length > 1
#guard ((helpInteractive false).splitOn "decline").length > 1
#guard ((helpInteractive false).splitOn "optional discard, attach").length > 1
#guard ((helpInteractive false).splitOn "choose no target").length > 1
#guard ((helpInteractive false).splitOn "pay-extra").length > 1
#guard ((helpInteractive false).splitOn "autopay").length > 1
#guard ((helpInteractive false).splitOn "CR 601.2g").length > 1
#guard ((helpInteractive false).splitOn "CR 601.2b").length > 1
#guard ((helpInteractive false).splitOn "resolved trigger requires").length > 1
#guard (usage.splitOn "--input FILE").length > 1
#guard (usage.splitOn "--output FILE").length > 1
#guard (usage.splitOn "additional flags instead of commands").length > 1
#guard (usage.splitOn "Flags from --input are written first").length > 1
#guard (usage.splitOn "replays that file and appends").length > 1
#guard (usage.splitOn "Unique automatic cost payments").length > 1
#guard (usage.splitOn "Incorrect commands and session commands").length > 1
#guard (usage.splitOn "such as state and quit").length > 1
#guard (usage.splitOn "--name NAME").length > 1
#guard (usage.splitOn "--deck COLOR").length > 1
#guard (usage.splitOn "--decides NAME").length > 1
#guard (usage.splitOn "random player").length > 1
#guard (usage.splitOn "white, blue, black, red, or green").length > 1
#guard (usage.splitOn "first <name>").length > 1
#guard (usage.splitOn "CR 103.1").length > 1

def helpChooseFirst : String :=
  "Commands:
  help                 Show this help
  first <name>         Choose who takes the first turn (CR 103.1)
  quit                 Exit
"

#guard (helpChooseFirst.splitOn "first <name>").length > 1
#guard (helpChooseFirst.splitOn "CR 103.1").length > 1
#guard (helpChooseFirst.splitOn "quit").length > 1

/-- Object ids print as `#12`; accept that form or a bare decimal. -/
def parseObjectId? (token : String) : Option ObjectId :=
  let digits :=
    match token.toList with
    | '#' :: rest => String.ofList rest
    | cs => String.ofList cs
  digits.toNat?.map (fun n => ⟨n⟩)

/-- Parse a mana type from a letter (`G`) or English name (`green`). -/
def parseManaType? (token : String) : Option ManaType :=
  match token.map Char.toLower with
  | "w" | "white" => some (.colored .white)
  | "u" | "blue" => some (.colored .blue)
  | "b" | "black" => some (.colored .black)
  | "r" | "red" => some (.colored .red)
  | "g" | "green" => some (.colored .green)
  | "c" | "colorless" => some .colorless
  | _ => none

#guard parseManaType? "G" == some (.colored .green)
#guard parseManaType? "white" == some (.colored .white)
#guard (parseManaType? "12").isNone

/-- Parse one or more object identifiers from command tokens. -/
def parseObjectIds (tokens : List String) (usage : String) : Except String (Array ObjectId) :=
  go (commandTokens tokens) #[]
where
  go : List String → Array ObjectId → Except String (Array ObjectId)
    | [], acc => if acc.isEmpty then .error usage else .ok acc
    | t :: rest, acc =>
      match parseObjectId? t with
      | none => .error usage
      | some id => go rest (acc.push id)

/-- Parse a single object id, or `usage` if the tokens are not exactly one id. -/
def parseRequiredObjectId (tokens : List String) (usage : String) : Except String ObjectId :=
  match commandTokens tokens with
  | [arg] =>
    match parseObjectId? arg with
    | none => throw usage
    | some id => return id
  | _ => throw usage

/-- The object `id`, or `"no such object"`. -/
def requireObject (g : Game) (id : ObjectId) : Except String GameObject :=
  match g.findObject? id with
  | none => throw "no such object"
  | some o => return o

/-- Parse a single existing object id and apply `action`. -/
def applyObjectCommand (g : Game) (p : PlayerId) (tokens : List String)
    (usage : String) (action : ObjectId → Action) : Except String Game := do
  let id ← parseRequiredObjectId tokens usage
  let _ ← requireObject g id
  g.apply p (action id)

/-- Split `tokens` at the first `kw`. `none` means the keyword was absent. -/
def splitAtKeyword (kw : String) (tokens : List String) : List String × Option (List String) :=
  go [] tokens
where
  go (acc : List String) : List String → List String × Option (List String)
    | [] => (acc.reverse, none)
    | t :: rest =>
      if t == kw then (acc.reverse, some rest)
      else go (t :: acc) rest

#guard splitAtKeyword "bottom" ["1", "2", "bottom", "3"] == (["1", "2"], some ["3"])
#guard splitAtKeyword "bottom" ["1", "2"] == (["1", "2"], none)
#guard splitAtKeyword "bottom" ["bottom", "3"] == ([], some ["3"])

/-- Attackers for an interactive `attack` command. Omitted ids mean every
creature that currently can attack. -/
def attackerIdsForCommand (g : Game) (tokens : List String) : Except String (Array ObjectId) :=
  let tokens := commandTokens tokens
  if tokens.isEmpty then
    .ok (g.battlefield.filter (g.canAttack) |>.map (·.id))
  else
    parseObjectIds tokens "usage: attack [id ...]"

def applyAttack (g : Game) (p : PlayerId) (tokens : List String) : Except String Game := do
  let ids ← attackerIdsForCommand g tokens
  for id in ids do
    if (g.findObject? id).isNone then
      throw "no such object"
  g.apply p (.declareAttackers ids)

#guard parseObjectId? "12" == some ⟨12⟩
#guard parseObjectId? "#12" == some ⟨12⟩
#guard (parseObjectId? "x").isNone
#guard
  match parseObjectIds ["3", "#7"] "usage: attack [id ...]" with
  | .ok ids => ids == #[⟨3⟩, ⟨7⟩]
  | .error _ => false
#guard
  match parseObjectIds ["x"] "usage: attack [id ...]" with
  | .error msg => msg == "usage: attack [id ...]"
  | .ok _ => false
#guard
  match parseObjectIds [] "usage: attack [id ...]" with
  | .error _ => true
  | .ok _ => false

#guard
  match attackerIdsForCommand Tests.readyToDeclareAttackers [] with
  | .ok ids => ids.size == 2
  | .error _ => false

#guard
  let g := Tests.readyToDeclareAttackers
  let bears := Tests.namedPermanent g "Grizzly Bears"
  match applyAttack g ⟨0⟩ [toString bears.id] with
  | .ok g' =>
    (Tests.namedPermanent g' "Grizzly Bears").status.attacking &&
    !(Tests.namedPermanent g' "Gray Ogre").status.attacking
  | .error _ => false

#guard
  match applyAttack Tests.readyToDeclareAttackers ⟨0⟩ ["99999"] with
  | .error msg => msg == "no such object"
  | .ok _ => false

#guard
  match applyAttack Tests.readyToDeclareAttackers ⟨0⟩ ["nope"] with
  | .error msg => msg == "usage: attack [id ...]"
  | .ok _ => false

/-- Pair unused legal blockers with attackers. A creature with menace is
covered only when two blockers can be assigned (CR 702.111b); leftover
blockers then cover attackers that do not have menace. A bare `block`
covers as many attacks as possible. -/
def greedyBlockAssignments (g : Game) : Array (ObjectId × ObjectId) :=
  Id.run do
    let attackers := g.battlefield.filter (·.status.attacking)
    let defender := g.opponent g.activePlayer
    let mut unused := g.battlefield.filter (fun b =>
      b.isCreature && b.controlledBy defender && !b.status.tapped)
    let mut blocked : Array ObjectId := #[]
    let mut asgn : Array (ObjectId × ObjectId) := #[]
    for a in attackers do
      if g.hasMenace a then
        let able := unused.filter (fun b => g.canBlock b a)
        if able.size >= 2 then
          let b1 := able[0]!
          let b2 := able[1]!
          unused := unused.filter (fun b => b.id != b1.id && b.id != b2.id)
          asgn := asgn.push (b1.id, a.id) |>.push (b2.id, a.id)
          blocked := blocked.push a.id
    for b in unused do
      match attackers.find? (fun a =>
        !blocked.contains a.id && !g.hasMenace a && g.canBlock b a) with
      | some a =>
        blocked := blocked.push a.id
        asgn := asgn.push (b.id, a.id)
      | none => pure ()
    return asgn

def blockUsage : String := "usage: block [blocker attacker ...]"

/-- Parse blocker/attacker id pairs. An odd token count is a usage error. -/
def parseBlockAssignments (tokens : List String) : Except String (Array (ObjectId × ObjectId)) := do
  let ids ← parseObjectIds tokens blockUsage
  if ids.size % 2 != 0 then
    throw blockUsage
  let mut asgn : Array (ObjectId × ObjectId) := #[]
  for i in [0:ids.size / 2] do
    asgn := asgn.push (ids[2 * i]!, ids[2 * i + 1]!)
  return asgn

/-- Blockers for an interactive `block` command. Omitted ids mean a greedy
covering of unblocked attackers. -/
def blockAssignmentsForCommand (g : Game) (tokens : List String) :
    Except String (Array (ObjectId × ObjectId)) :=
  let tokens := commandTokens tokens
  if tokens.isEmpty then
    .ok (greedyBlockAssignments g)
  else
    parseBlockAssignments tokens

def applyBlock (g : Game) (p : PlayerId) (tokens : List String) : Except String Game := do
  let asgn ← blockAssignmentsForCommand g tokens
  for (blocker, attacker) in asgn do
    if (g.findObject? blocker).isNone || (g.findObject? attacker).isNone then
      throw "no such object"
  g.apply p (.declareBlockers asgn)

#guard
  match parseBlockAssignments ["3", "#7"] with
  | .ok asgn => asgn == #[(⟨3⟩, ⟨7⟩)]
  | .error _ => false

#guard
  match parseBlockAssignments ["1", "2", "#3", "4"] with
  | .ok asgn => asgn == #[(⟨1⟩, ⟨2⟩), (⟨3⟩, ⟨4⟩)]
  | .error _ => false

#guard
  match parseBlockAssignments ["12"] with
  | .error msg => msg == blockUsage
  | .ok _ => false

#guard
  match parseBlockAssignments ["x", "1"] with
  | .error msg => msg == blockUsage
  | .ok _ => false

#guard
  match blockAssignmentsForCommand Tests.readyToDeclareBlockers [] with
  | .ok asgn =>
    let g := Tests.readyToDeclareBlockers
    asgn == #[(
      (Tests.namedPermanent g "Grizzly Bears").id,
      (Tests.namedPermanent g "Gray Ogre").id)]
  | .error _ => false

#guard
  let g := Tests.readyToDeclareBlockers
  let bears := Tests.namedPermanent g "Grizzly Bears"
  let ogre := Tests.namedPermanent g "Gray Ogre"
  match applyBlock g ⟨1⟩ [toString bears.id, toString ogre.id] with
  | .ok g' =>
    (Tests.namedPermanent g' "Grizzly Bears").status.blocking == #[ogre.id]
  | .error _ => false

#guard
  match applyBlock Tests.readyToDeclareBlockers ⟨1⟩ [] with
  | .ok g' =>
    (Tests.namedPermanent g' "Grizzly Bears").status.blocking ==
      #[(Tests.namedPermanent g' "Gray Ogre").id]
  | .error _ => false

#guard
  match applyBlock Tests.readyToDeclareBlockers ⟨1⟩ ["99999", "1"] with
  | .error msg => msg == "no such object"
  | .ok _ => false

#guard
  match applyBlock Tests.readyToDeclareBlockers ⟨1⟩ ["nope"] with
  | .error msg => msg == blockUsage
  | .ok _ => false

#guard
  match applyBlock Tests.readyToDeclareAttackers ⟨0⟩ [] with
  | .error msg => msg == "Not time to declare blockers"
  | .ok _ => false

#guard
  match blockAssignmentsForCommand Tests.ogreVsCrusherReadyToBlock [] with
  | .ok asgn => asgn.isEmpty
  | .error _ => false

#guard
  let g := Tests.ogreVsCrusherReadyToBlock
  match applyBlock g ⟨1⟩ [
      toString (Tests.namedPermanent g "Olog-hai Crusher").id,
      toString (Tests.namedPermanent g "Gray Ogre").id] with
  | .error msg => Tests.mentions msg "cannot block"
  | .ok _ => false

#guard
  match applyBlock Tests.ogreVsCrusherReadyToBlock ⟨1⟩ [] with
  | .ok g' =>
    (Tests.namedPermanent g' "Olog-hai Crusher").status.blocking.isEmpty &&
      !(Tests.namedPermanent g' "Gray Ogre").status.blocked
  | .error _ => false

#guard
  match applyBlock Tests.ogreVsCrusherAndGoblinReadyToBlock ⟨1⟩ [] with
  | .ok g' =>
    (Tests.namedPermanent g' "Olog-hai Crusher").status.blocking ==
      #[(Tests.namedPermanent g' "Gray Ogre").id]
  | .error _ => false

def assignUsage : String := "usage: assign [source target amount ...]"

/-- Add `amt` from `src` to creature `tgt` in an accumulating assignment list. -/
def pushCombatAmount (acc : Array CreatureCombatAssignment) (src tgt : ObjectId) (amt : Int) :
    Array CreatureCombatAssignment :=
  match acc.findIdx? (fun a => a.source == src) with
  | none => acc.push { source := src, toCreatures := #[(tgt, amt)] }
  | some i =>
    let a := acc[i]!
    acc.set! i { a with toCreatures := a.toCreatures.push (tgt, amt) }

/-- Add `amt` from `src` to the defending player. -/
def pushCombatPlayerAmount (acc : Array CreatureCombatAssignment) (src : ObjectId) (amt : Int) :
    Array CreatureCombatAssignment :=
  match acc.findIdx? (fun a => a.source == src) with
  | none => acc.push { source := src, toPlayer := amt }
  | some i =>
    let a := acc[i]!
    acc.set! i { a with toPlayer := a.toPlayer + amt }

/-- True when `token` names the defending player, or `opponent` while the
attacking player is assigning (CR 510.1a / 702.19). -/
def isDefendingPlayerToken (g : Game) (p : PlayerId) (token : String) : Bool :=
  let lower := token.map Char.toLower
  let defender := g.opponent g.activePlayer
  lower == (g.player defender).name.map Char.toLower ||
    (p == g.activePlayer && lower == "opponent")

/-- Parse source/target/amount triples. An empty list means the default legal
assignment (CR 510.1c–d). `target` may be a creature id or the defending
player. -/
def parseCombatAssignments (g : Game) (p : PlayerId) (tokens : List String) :
    Except String (Array CreatureCombatAssignment) :=
  go (commandTokens tokens) #[]
where
  go : List String → Array CreatureCombatAssignment →
      Except String (Array CreatureCombatAssignment)
    | [], acc => .ok acc
    | srcTok :: tgtTok :: amtTok :: rest, acc =>
      match parseObjectId? srcTok, amtTok.toInt? with
      | some src, some amt =>
        match parseObjectId? tgtTok with
        | some tgt => go rest (pushCombatAmount acc src tgt amt)
        | none =>
          if isDefendingPlayerToken g p tgtTok then
            go rest (pushCombatPlayerAmount acc src amt)
          else .error assignUsage
      | _, _ => .error assignUsage
    | _, _ => .error assignUsage

def applyAssign (g : Game) (p : PlayerId) (tokens : List String) : Except String Game := do
  let asgns ← parseCombatAssignments g p tokens
  for a in asgns do
    if (g.findObject? a.source).isNone then
      throw "no such object"
    for (tid, _) in a.toCreatures do
      if (g.findObject? tid).isNone then
        throw "no such object"
  g.apply p (.assignCombatDamage asgns)

def parsedOneCombatTriple : Bool :=
  match parseCombatAssignments Tests.started ⟨0⟩ ["3", "#7", "2"] with
  | .ok asgns => asgns == #[{ source := ⟨3⟩, toCreatures := #[(⟨7⟩, 2)] }]
  | .error _ => false

#guard parsedOneCombatTriple

def parsedTwoAmountsSameSource : Bool :=
  match parseCombatAssignments Tests.started ⟨0⟩ ["1", "2", "3", "1", "4", "0"] with
  | .ok asgns =>
    asgns == #[{ source := ⟨1⟩, toCreatures := #[(⟨2⟩, 3), (⟨4⟩, 0)] }]
  | .error _ => false

#guard parsedTwoAmountsSameSource

#guard
  match parseCombatAssignments Tests.started ⟨0⟩ [] with
  | .ok asgns => asgns.isEmpty
  | .error _ => false

#guard
  match parseCombatAssignments Tests.started ⟨0⟩ ["1", "2"] with
  | .error msg => msg == assignUsage
  | .ok _ => false

#guard
  match parseCombatAssignments Tests.giantReadyToAssign ⟨0⟩ ["3", "Nissa", "2"] with
  | .ok asgns => asgns == #[{ source := ⟨3⟩, toPlayer := 2 }]
  | .error _ => false

#guard
  match parseCombatAssignments Tests.giantReadyToAssign ⟨0⟩ ["3", "opponent", "2"] with
  | .ok asgns => asgns == #[{ source := ⟨3⟩, toPlayer := 2 }]
  | .error _ => false

#guard
  match parseCombatAssignments Tests.giantReadyToAssign ⟨0⟩ ["3", "Chandra", "2"] with
  | .error msg => msg == assignUsage
  | .ok _ => false

#guard
  match parseCombatAssignments Tests.bearsBlockingTwoOgresReady ⟨1⟩
      ["3", "opponent", "2"] with
  | .error msg => msg == assignUsage
  | .ok _ => false

#guard
  match parseCombatAssignments Tests.started ⟨0⟩ ["3", "1", "2", "3", "Nissa", "1"] with
  | .ok asgns =>
    asgns == #[{ source := ⟨3⟩, toCreatures := #[(⟨1⟩, 2)], toPlayer := 1 }]
  | .error _ => false

#guard
  match applyAssign Tests.giantReadyToAssign ⟨0⟩ [] with
  | .ok g' =>
    g'.pending == .none &&
    (g'.battlefield.filter (fun o => o.name == "Llanowar Elves")).size == 1
  | .error _ => false

#guard
  let g := Tests.giantReadyToAssign
  let giant := Tests.namedPermanent g "Hill Giant"
  let elves := g.battlefield.filter (fun o => o.name == "Llanowar Elves")
  match applyAssign g ⟨0⟩
      [toString giant.id, toString elves[0]!.id, "1",
        toString giant.id, toString elves[1]!.id, "2"] with
  | .ok g' => (g'.battlefield.filter (fun o => o.name == "Llanowar Elves")).isEmpty
  | .error _ => false

#guard
  let g := Tests.giantReadyToAssign
  let giant := Tests.namedPermanent g "Hill Giant"
  let g := g.setObject { giant with status := giant.status.grantUntilEot Keyword.trample }
  let giant := Tests.namedPermanent g "Hill Giant"
  let elves := g.battlefield.filter (fun o => o.name == "Llanowar Elves")
  match applyAssign g ⟨0⟩
      [toString giant.id, toString elves[0]!.id, "1",
        toString giant.id, toString elves[1]!.id, "1",
        toString giant.id, "Nissa", "1"] with
  | .ok g' =>
    (g'.player ⟨1⟩).life == 19 &&
    (g'.battlefield.filter (fun o => o.name == "Llanowar Elves")).isEmpty &&
    g'.log.any (fun s => Tests.mentions s "tramples for 1 to Nissa")
  | .error _ => false

#guard
  match applyAssign Tests.readyToDeclareBlockers ⟨0⟩ [] with
  | .error msg => msg == "Not time to assign combat damage (CR 510.1)"
  | .ok _ => false

def stackUsage : String := "usage: stack <id> [id...]"

/-- Put waiting triggered abilities on the stack in the listed source order
(CR 603.3b). -/
def applyStack (g : Game) (p : PlayerId) (tokens : List String) : Except String Game := do
  let ids ← parseObjectIds tokens stackUsage
  g.apply p (.stackTriggers ids)

def bottomUsage : String := "usage: bottom <id> [id ...]"

/-- Cards to put on the bottom for an interactive `bottom` command. -/
def applyBottom (g : Game) (p : PlayerId) (tokens : List String) : Except String Game := do
  let ids ← parseObjectIds tokens bottomUsage
  for id in ids do
    if (g.findObject? id).isNone then
      throw "no such object"
  g.apply p (.putOnBottom ids)

#guard
  match applyBottom Tests.afterChandraMulligan ⟨0⟩
      [toString Tests.chandraBottomCard.id] with
  | .ok g' => (g'.player ⟨0⟩).hand.size == 6
  | .error _ => false

#guard
  match applyBottom Tests.afterChandraMulligan ⟨0⟩ ["99999"] with
  | .error msg => msg == "no such object"
  | .ok _ => false

#guard
  match applyBottom Tests.afterChandraMulligan ⟨0⟩ ["nope"] with
  | .error msg => msg == bottomUsage
  | .ok _ => false

#guard
  match applyBottom Tests.afterChandraMulligan ⟨0⟩ [] with
  | .error msg => msg == bottomUsage
  | .ok _ => false

#guard
  match applyBottom Tests.drawnHands ⟨0⟩
      [toString (Tests.drawnHands.player ⟨0⟩).hand[0]!] with
  | .error msg => msg == "Not time to put cards on the bottom (CR 103.5)"
  | .ok _ => false

def visibleUsage : String := "usage: visible [on|off]"

/-- `none` prints the first listed player's view once; `some true/false` turns
follow mode on or off. -/
def applyVisible (tokens : List String) : Except String (Option Bool) :=
  match commandTokens tokens with
  | [] => .ok none
  | ["on"] => .ok (some true)
  | ["off"] => .ok (some false)
  | _ => .error visibleUsage

#guard
  match applyVisible [] with
  | .ok none => true
  | _ => false

#guard
  match applyVisible ["on"] with
  | .ok (some true) => true
  | _ => false

#guard
  match applyVisible ["off"] with
  | .ok (some false) => true
  | _ => false

#guard
  match applyVisible ["nope"] with
  | .error msg => msg == visibleUsage
  | .ok _ => false

#guard
  match applyVisible ["on", "off"] with
  | .error msg => msg == visibleUsage
  | .ok _ => false

/-- The first listed player's viewpoint when follow mode is on; omniscient
otherwise. -/
def humanView (playerView : Bool) : Option PlayerId :=
  if playerView then some ⟨0⟩ else none

#guard (humanView false).isNone
#guard humanView true == some ⟨0⟩

/-- Hidden-information view. Interactive mode always follows the first listed
player; multiplayer follows the player who must act. -/
def currentView (g : Game) (playerView : Bool) (controlAll : Bool) : Option PlayerId :=
  if !playerView then none
  else if controlAll then g.actor
  else some ⟨0⟩

#guard (currentView Tests.nissaDraw true false) == some ⟨0⟩
#guard (currentView Tests.nissaDraw true true) == some ⟨1⟩
#guard (currentView Tests.nissaDraw false true).isNone
#guard (currentView Tests.drawnHands true true) == some ⟨0⟩

/-- Who the console should issue the next action as. -/
def actingPlayer (g : Game) : Except String PlayerId :=
  match g.actor with
  | some p => .ok p
  | none => .error "No player has an action"

#guard
  match actingPlayer Tests.drawnHands with
  | .ok p => p == ⟨0⟩
  | .error _ => false

#guard
  match actingPlayer Tests.nissaDraw with
  | .ok p => p == ⟨1⟩
  | .error _ => false

#guard
  match actingPlayer Tests.readyToDeclareBlockers with
  | .ok p => p == ⟨1⟩
  | .error _ => false

#guard
  match actingPlayer Tests.afterChandraDeclaresMulligan with
  | .ok p => p == ⟨1⟩
  | .error _ => false

def tapUsage : String := "usage: tap <id> [id ...] [color]"

/-- Color to tap `o` for when the player did not name one. -/
def defaultTapMana (g : Game) (p : PlayerId) (o : GameObject) : Option ManaType :=
  match (g.manaAbilitiesOf o)[0]? with
  | none => none
  | some first =>
    if o.printed.tapAddAnyColorEqualToPower then
      match g.proposedSpell with
      | some prop =>
        some ((g.preferredManaType p o (g.manaAbilitiesOf o) prop.cost
          (g.proposedAllowsElfRestricted prop)
          (g.proposedAllowsInstRestricted prop)).getD (.colored .green))
      | none => some (.colored .green)
    else some first

/-- Tap each listed permanent for mana. A trailing color letter applies to all. -/
def applyTap (g : Game) (p : PlayerId) (tokens : List String) : Except String Game := do
  let tokens := commandTokens tokens
  let (idTokens, chosen) :=
    match tokens.reverse with
    | t :: rest =>
      match parseManaType? t with
      | some m => (rest.reverse, some m)
      | none => (tokens, none)
    | [] => (tokens, none)
  let ids ← parseObjectIds idTokens tapUsage
  let mut jobs : Array (ObjectId × ManaType) := #[]
  for id in ids do
    match g.findObject? id with
    | none => throw "no such object"
    | some o =>
      match chosen with
      | some m =>
        if !(g.manaAbilitiesOf o).contains m then
          throw s!"{o.name} cannot produce {m}"
        jobs := jobs.push (id, m)
      | none =>
        match defaultTapMana g p o with
        | none => throw s!"{o.name} has no mana ability"
        | some m => jobs := jobs.push (id, m)
  let mut g := g
  for (id, m) in jobs do
    g := (← g.apply p (.tapForMana id m))
  return g

#guard
  match applyTap Tests.baubleReady ⟨0⟩ [] with
  | .error msg => msg == tapUsage
  | .ok _ => false

#guard
  match applyTap Tests.baubleReady ⟨0⟩ ["nope"] with
  | .error msg => msg == tapUsage
  | .ok _ => false

#guard
  match applyTap Tests.baubleReady ⟨0⟩ ["99999"] with
  | .error msg => msg == "no such object"
  | .ok _ => false

#guard
  let g := Tests.baubleReady
  let bauble := Tests.baubleSource g
  match applyTap g ⟨0⟩ [toString bauble.id] with
  | .error msg => Tests.mentions msg "has no mana ability"
  | .ok _ => false

#guard
  let g := Tests.withMountain
  let mtn := Tests.lastPermanent g
  match applyTap g ⟨0⟩ [toString mtn.id] with
  | .ok g' =>
    (Tests.lastPermanent g').status.tapped &&
    (g'.player ⟨0⟩).manaPool.canPay (ManaCost.ofColor .red)
  | .error _ => false

#guard
  let g := Tests.archAndElves
  let arch := Tests.namedPermanent g "Elvish Archdruid"
  match applyTap g ⟨0⟩ [toString arch.id] with
  | .ok g' =>
    (Tests.namedPermanent g' "Elvish Archdruid").status.tapped &&
    (g'.player ⟨0⟩).manaPool.green == 2 &&
    g'.log.any (fun s => Tests.mentions s "green ×2")
  | .error _ => false

#guard
  let g := Tests.baubleReady
  let lands := (g.permanentsOf ⟨0⟩).filter (·.printed.isLand)
  lands.size == 2 &&
  match applyTap g ⟨0⟩ [toString lands[0]!.id, s!"{lands[1]!.id.raw}"] with
  | .ok g' =>
    (g'.battlefield.filter (fun o => o.printed.isLand && o.status.tapped)).size == 2 &&
    (g'.player ⟨0⟩).manaPool.canPay (ManaCost.ofGeneric 2)
  | .error _ => false

#guard
  let g := Tests.proposedBauble
  let lands := (g.permanentsOf ⟨0⟩).filter (·.printed.isLand)
  lands.size == 2 &&
  match applyTap g ⟨0⟩ [toString lands[0]!.id, toString lands[1]!.id] with
  | .ok g' =>
    g'.pending == .activateManaAbilities ⟨0⟩ &&
    (g'.player ⟨0⟩).manaPool.canPay (ManaCost.ofGeneric 2) &&
    (g'.battlefield.filter (fun o => o.printed.isLand && o.status.tapped)).size == 2
  | .error _ => false

#guard
  let g := Tests.withMountain
  let mtn := Tests.lastPermanent g
  match applyTap g ⟨0⟩ [toString mtn.id, toString mtn.id] with
  | .error msg => Tests.mentions msg "already tapped"
  | .ok _ => false

def playUsage : String := "usage: play <id>"

/-- Play the named land from a zone the player is allowed to play from. -/
def applyPlay (g : Game) (p : PlayerId) (tokens : List String) : Except String Game :=
  applyObjectCommand g p tokens playUsage .playLand

#guard
  match applyPlay Tests.afterDraw ⟨0⟩ [] with
  | .error msg => msg == playUsage
  | .ok _ => false

#guard
  match applyPlay Tests.afterDraw ⟨0⟩ ["nope"] with
  | .error msg => msg == playUsage
  | .ok _ => false

#guard
  match applyPlay Tests.afterDraw ⟨0⟩ ["1", "2"] with
  | .error msg => msg == playUsage
  | .ok _ => false

#guard
  match applyPlay Tests.afterDraw ⟨0⟩ ["99999"] with
  | .error msg => msg == "no such object"
  | .ok _ => false

#guard
  let g := Tests.afterDraw
  match (g.handObjects ⟨0⟩).find? (·.printed.isLand) with
  | none => false
  | some land =>
    match applyPlay g ⟨0⟩ [toString land.id] with
    | .ok g' =>
      (g'.player ⟨0⟩).landsPlayedThisTurn == 1 &&
      g'.battlefield.any (fun o => o.name == land.name)
    | .error _ => false

def activateUsage : String := "usage: activate <id> [n]"

/-- Activate a non-mana activated ability of the named object (a permanent,
a card in hand, or a card in a graveyard). `n` is the 1-based index of the
printed activated ability; omit it to activate the first. -/
def applyActivate (g : Game) (p : PlayerId) (tokens : List String) : Except String Game := do
  match commandTokens tokens with
  | [arg] =>
    match parseObjectId? arg with
    | none => throw activateUsage
    | some id =>
      let _ ← requireObject g id
      g.apply p (.activate id 0)
  | [arg, ntok] =>
    match parseObjectId? arg, ntok.toNat? with
    | none, _ => throw activateUsage
    | _, none => throw activateUsage
    | _, some 0 => throw activateUsage
    | some id, some n =>
      let _ ← requireObject g id
      g.apply p (.activate id (n - 1))
  | _ => throw activateUsage

def sacrificeUsage : String := "usage: sacrifice <id>"

/-- After `pay`, sacrifice the named creature or artifact to finish activating
or casting. With no id, choose the sacrifice option of an additional cost
(CR 601.2b). With an id, also sacrifice a creature a resolved trigger requires. -/
def applySacrifice (g : Game) (p : PlayerId) (tokens : List String) : Except String Game := do
  match commandTokens tokens with
  | [] =>
    match g.pending with
    | .chooseAdditionalCost _ => g.apply p (.chooseAdditionalCost false)
    | _ => throw sacrificeUsage
  | [_] => applyObjectCommand g p tokens sacrificeUsage .sacrifice
  | _ => throw sacrificeUsage

def payExtraUsage : String := "usage: pay-extra"

/-- Pay extra generic mana rather than sacrifice, as an additional cost
(CR 601.2b). -/
def applyPayExtra (g : Game) (p : PlayerId) (tokens : List String) : Except String Game := do
  match commandTokens tokens with
  | [] => g.apply p (.chooseAdditionalCost true)
  | _ => throw payExtraUsage

#guard
  match applyPayExtra Tests.stirChooseAdditional ⟨0⟩ [] with
  | .ok g' =>
    g'.pending == .chooseTargets ⟨0⟩ &&
    g'.log.any (fun s => Tests.mentions s "chooses to pay {4} as an additional cost")
  | .error _ => false

#guard
  match applyPayExtra Tests.stirChooseAdditional ⟨0⟩ ["extra"] with
  | .error msg => msg == payExtraUsage
  | .ok _ => false

#guard
  match applySacrifice Tests.stirChooseAdditional ⟨0⟩ [] with
  | .ok g' =>
    match g'.proposedSpell with
    | some prop => prop.needsSacrificeOther
    | none => false
  | .error _ => false

#guard
  match applyActivate Tests.baubleReady ⟨0⟩ [] with
  | .error msg => msg == activateUsage
  | .ok _ => false

#guard
  match applyActivate Tests.baubleReady ⟨0⟩ ["nope"] with
  | .error msg => msg == activateUsage
  | .ok _ => false

#guard
  match applyActivate Tests.baubleReady ⟨0⟩ ["1", "nope"] with
  | .error msg => msg == activateUsage
  | .ok _ => false

#guard
  match applyActivate Tests.baubleReady ⟨0⟩ ["1", "0"] with
  | .error msg => msg == activateUsage
  | .ok _ => false

#guard
  match applyActivate Tests.baubleReady ⟨0⟩ ["1", "2", "3"] with
  | .error msg => msg == activateUsage
  | .ok _ => false

#guard
  match applyActivate Tests.baubleReady ⟨0⟩ ["99999"] with
  | .error msg => msg == "no such object"
  | .ok _ => false

#guard
  let g := Tests.baubleReady
  match (g.permanentsOf ⟨0⟩).find? (·.printed.isLand) with
  | none => false
  | some land =>
    match applyActivate g ⟨0⟩ [toString land.id] with
    | .error msg => Tests.mentions msg "has no activated ability"
    | .ok _ => false

#guard
  let g := Tests.baubleReady
  let bauble := Tests.baubleSource g
  match applyActivate g ⟨0⟩ [toString bauble.id] with
  | .ok g' =>
    g'.pending == .activateManaAbilities ⟨0⟩ &&
    g'.log.any (fun s => Tests.mentions s "begins activating Wayfarer's Bauble")
  | .error _ => false

#guard
  let g := Tests.baubleReady
  let bauble := Tests.baubleSource g
  match applyActivate g ⟨0⟩ [toString bauble.id, "1"] with
  | .ok g' => g'.pending == .activateManaAbilities ⟨0⟩
  | .error _ => false

#guard
  let g := Tests.baubleReady
  let bauble := Tests.baubleSource g
  match applyActivate g ⟨0⟩ [toString bauble.id, "2"] with
  | .error msg => Tests.mentions msg "has no such activated ability"
  | .ok _ => false

#guard
  let g := Tests.dunedainReady
  let blade := Tests.namedPermanent g "Dúnedain Blade"
  match applyActivate g ⟨0⟩ [toString blade.id] with
  | .ok g' => g'.pending == .chooseTargets ⟨0⟩
  | .error _ => false

#guard
  let g := Tests.dunedainReady
  let blade := Tests.namedPermanent g "Dúnedain Blade"
  match applyActivate g ⟨0⟩ [toString blade.id, "2"] with
  | .ok g' =>
    g'.pending == .chooseTargets ⟨0⟩ &&
    g'.log.any (fun s => Tests.mentions s "begins activating Dúnedain Blade")
  | .error _ => false

#guard
  let g := Tests.baubleReady
  let bauble := Tests.baubleSource g
  match applyActivate g ⟨0⟩ [s!"{bauble.id.raw}"] with
  | .ok g' => g'.stack.size == 1
  | .error _ => false

#guard
  let g := Tests.hunterReady
  let hunter := Tests.hunterSource g
  match applyActivate g ⟨0⟩ [toString hunter.id] with
  | .ok g' =>
    g'.pending == .activateManaAbilities ⟨0⟩ &&
    g'.log.any (fun s => Tests.mentions s "begins activating Snowslope Hunter")
  | .error _ => false

#guard
  match applySacrifice Tests.hunterReady ⟨0⟩ [] with
  | .error msg => msg == sacrificeUsage
  | .ok _ => false

#guard
  match applySacrifice Tests.hunterReady ⟨0⟩ ["nope"] with
  | .error msg => msg == sacrificeUsage
  | .ok _ => false

#guard
  match applySacrifice Tests.hunterReady ⟨0⟩ ["1", "2"] with
  | .error msg => msg == sacrificeUsage
  | .ok _ => false

#guard
  let g := Tests.hunterReady
  match applySacrifice g ⟨0⟩ [toString (Tests.hunterFodder g).id] with
  | .error msg => Tests.mentions msg "Not time to sacrifice"
  | .ok _ => false

#guard
  let g := Tests.paidHunter
  match applySacrifice g ⟨0⟩ ["99999"] with
  | .error msg => msg == "no such object"
  | .ok _ => false

#guard
  let g := Tests.paidHunter
  let fodder := Tests.hunterFodder g
  match applySacrifice g ⟨0⟩ [toString fodder.id] with
  | .ok g' =>
    g'.pending == .none &&
    g'.log.any (fun s => Tests.mentions s "sacrifices Raging Goblin") &&
    g'.log.any (fun s => Tests.mentions s "activates Snowslope Hunter")
  | .error _ => false

#guard
  let g := Tests.paidClub
  let fodder := Tests.clubFodder g
  match applySacrifice g ⟨0⟩ [toString fodder.id] with
  | .ok g' =>
    g'.pending == .none &&
    g'.log.any (fun s => Tests.mentions s "sacrifices Raging Goblin") &&
    g'.log.any (fun s => Tests.mentions s "casts Improvised Club")
  | .error _ => false

#guard
  let g := Tests.bladeMustSac
  let bears := Tests.namedPermanent g "Grizzly Bears"
  match applySacrifice g ⟨1⟩ [toString bears.id] with
  | .ok g' =>
    g'.pending == .none &&
    g'.log.any (fun s => Tests.mentions s "sacrifices Grizzly Bears")
  | .error _ => false

def modeUsage : String := "usage: mode <n>"

/-- Choose a mode of a modal spell or ability (CR 601.2b). Modes are 1-indexed. -/
def applyMode (g : Game) (p : PlayerId) (tokens : List String) : Except String Game := do
  match commandTokens tokens with
  | [arg] =>
    match arg.toNat? with
    | none => throw modeUsage
    | some 0 => throw modeUsage
    | some n => g.apply p (.chooseMode (n - 1))
  | _ => throw modeUsage

#guard
  match applyMode Tests.proposedCratermaker ⟨0⟩ [] with
  | .error msg => msg == modeUsage
  | .ok _ => false

#guard
  match applyMode Tests.proposedCratermaker ⟨0⟩ ["nope"] with
  | .error msg => msg == modeUsage
  | .ok _ => false

#guard
  match applyMode Tests.proposedCratermaker ⟨0⟩ ["0"] with
  | .error msg => msg == modeUsage
  | .ok _ => false

#guard
  match applyMode Tests.proposedCratermaker ⟨0⟩ ["1", "2"] with
  | .error msg => msg == modeUsage
  | .ok _ => false

#guard
  match applyMode Tests.proposedCratermaker ⟨0⟩ ["1"] with
  | .ok g' =>
    g'.pending == .chooseTargets ⟨0⟩ &&
    g'.log.any (fun s => Tests.mentions s "chooses a mode")
  | .error _ => false

#guard
  match applyMode Tests.proposedCratermaker ⟨0⟩ ["2"] with
  | .error msg => Tests.mentions msg "requires a target"
  | .ok _ => false

#guard
  let g := Tests.cratermakerDestroyReady
  let src := Tests.cratermakerSource g
  match applyActivate g ⟨0⟩ [toString src.id] with
  | .error _ => false
  | .ok g' =>
    match applyMode g' ⟨0⟩ ["2"] with
    | .ok g'' =>
      g''.pending == .chooseTargets ⟨0⟩ &&
      (g''.object! g''.stack.back!.objectId).abilityEffect ==
        some .destroyTargetColorlessNonland
    | .error _ => false

def castUsage : String := "usage: cast <id> [adventure]"

/-- Begin casting the named spell (CR 601.2a), or its Adventure (CR 715.3).
Targets are announced later with `target` (CR 601.2c). -/
def applyCast (g : Game) (p : PlayerId) (tokens : List String) : Except String Game := do
  match commandTokens tokens with
  | [_] => applyObjectCommand g p tokens castUsage .cast
  | [arg, "adventure"] =>
    match parseObjectId? arg with
    | none => throw castUsage
    | some id =>
      let _ ← requireObject g id
      g.apply p (.castAdventure id)
  | _ => throw castUsage

#guard
  match applyCast Tests.boltSetup ⟨0⟩ [] with
  | .error msg => msg == castUsage
  | .ok _ => false

#guard
  match applyCast Tests.boltSetup ⟨0⟩ ["nope"] with
  | .error msg => msg == castUsage
  | .ok _ => false

#guard
  match applyCast Tests.boltSetup ⟨0⟩ ["1", "2"] with
  | .error msg => msg == castUsage
  | .ok _ => false

#guard
  match applyCast Tests.boltSetup ⟨0⟩ ["1", "2", "3"] with
  | .error msg => msg == castUsage
  | .ok _ => false

#guard
  match applyCast Tests.boltSetup ⟨0⟩ ["99999"] with
  | .error msg => msg == "no such object"
  | .ok _ => false

#guard
  match applyCast Tests.boltSetup ⟨0⟩ [toString Tests.boltInHand.id] with
  | .ok g' =>
    g'.pending == .chooseTargets ⟨0⟩ &&
    g'.stack.back!.targets.isEmpty &&
    g'.log.any (fun s => Tests.mentions s "begins casting Lightning Bolt") &&
    g'.log.any (fun s => Tests.mentions s "must choose a target (CR 601.2c)")
  | .error _ => false

#guard
  match applyCast Tests.giftSetup ⟨0⟩
      [toString (Tests.handCardNamed Tests.giftSetup ⟨0⟩ "Gift of Strands").id] with
  | .ok g' =>
    g'.pending == .chooseTargets ⟨0⟩ &&
    g'.stack.back!.targets.isEmpty &&
    g'.log.any (fun s => Tests.mentions s "begins casting Gift of Strands")
  | .error _ => false

#guard
  match applyCast Tests.smaugSetup ⟨0⟩
      [toString (Tests.handCardNamed Tests.smaugSetup ⟨0⟩ "Smaug, the Great Calamity").id,
        "adventure"] with
  | .ok g' =>
    g'.pending == .chooseTargets ⟨0⟩ &&
    (g'.object! g'.stack.back!.objectId).name == "Spew Flame" &&
    g'.log.any (fun s => Tests.mentions s "begins casting Spew Flame")
  | .error _ => false

#guard
  match applyCast Tests.beornSetup ⟨0⟩
      [toString (Tests.handCardNamed Tests.beornSetup ⟨0⟩ "Beorn, Reluctant Host").id,
        "adventure"] with
  | .ok g' =>
    g'.pending == .activateManaAbilities ⟨0⟩ &&
    (g'.object! g'.stack.back!.objectId).name == "Till and Tend" &&
    (g'.object! g'.stack.back!.objectId).isAdventureSpell &&
    g'.log.any (fun s => Tests.mentions s "begins casting Till and Tend")
  | .error _ => false

#guard
  match applyCast Tests.fireOfOrthancSetup ⟨0⟩
      [toString (Tests.handCardNamed Tests.fireOfOrthancSetup ⟨0⟩ "Fire of Orthanc").id] with
  | .ok g' =>
    g'.pending == .chooseTargets ⟨0⟩ &&
    g'.stack.back!.targets.isEmpty &&
    g'.log.any (fun s => Tests.mentions s "begins casting Fire of Orthanc") &&
    g'.log.any (fun s => Tests.mentions s "must choose a target (CR 601.2c)")
  | .error _ => false

#guard
  match applyCast Tests.bilbosDeadlySliceSetup ⟨0⟩
      [toString (Tests.handCardNamed Tests.bilbosDeadlySliceSetup ⟨0⟩
        "Bilbo's Deadly Slice").id] with
  | .ok g' =>
    g'.pending == .chooseTargets ⟨0⟩ &&
    g'.stack.back!.targets.isEmpty &&
    g'.log.any (fun s => Tests.mentions s "begins casting Bilbo's Deadly Slice") &&
    g'.log.any (fun s => Tests.mentions s "must choose a target (CR 601.2c)")
  | .error _ => false

#guard
  match applyCast Tests.boltSetup ⟨0⟩ [toString Tests.boltInHand.id, "adventure"] with
  | .error msg => Tests.mentions msg "has no Adventure"
  | .ok _ => false

def targetUsage : String := "usage: target <id|name|opponent>"
def sequentialTargetUsage : String :=
  "Choose each instance of the word \"target\" in a separate target command (CR 601.2c)"
def divideTargetUsage : String := "usage: target <id|name|opponent> [amount] ..."

/-- Parse a CR 601.2c target: a permanent, graveyard-card, or stack-spell id,
a player name, or `opponent`. Card names match a current legal target. -/
def parseTarget (g : Game) (p : PlayerId) (token : String) : Except String Target := do
  let key := token.trimAscii.copy
  let lower := key.map Char.toLower
  if lower == "opponent" then
    return Target.player (g.opponent p)
  match g.players.find? (fun pl => pl.name.map Char.toLower == lower) with
  | some pl => return Target.player pl.id
  | none =>
    match parseObjectId? key with
    | some id =>
      match g.findObject? id with
      | none => throw "no such object"
      | some o =>
        match o.zone with
        | .graveyard _ | .stack => return Target.card id
        | _ => return Target.permanent id
    | none =>
      match g.objectAwaitingTargets with
      | none => throw targetUsage
      | some obj =>
        let named := (g.legalProposedTargets p obj).filter (fun t =>
          match t with
          | .player pid => (g.player pid).name.map Char.toLower == lower
          | .permanent oid | .card oid =>
            match g.findObject? oid with
            | some o => o.name.map Char.toLower == lower
            | none => false)
        match named.back? with
        | some t => return t
        | none => throw targetUsage

/-- Parse target/amount pairs for a divided-damage announcement (CR 601.2d). -/
def parseTargetAmountPairs (g : Game) (p : PlayerId) (tokens : List String) :
    Except String (Array (Target × Nat)) :=
  go tokens #[]
where
  go : List String → Array (Target × Nat) → Except String (Array (Target × Nat))
    | [], acc => if acc.isEmpty then .error divideTargetUsage else .ok acc
    | t :: n :: rest, acc =>
      match n.toNat? with
      | none => .error divideTargetUsage
      | some amt => do
        let tgt ← parseTarget g p t
        go rest (acc.push (tgt, amt))
    | _ :: [], _ => .error divideTargetUsage

/-- Announce every target of the current instance of the word “target”
(CR 601.2c), or every target of a divided-damage ability (CR 601.2d).
Further instances of the word use a later `target` command. “One or two
target creatures” uses one command with one or two names. -/
def applyTarget (g : Game) (p : PlayerId) (tokens : List String) : Except String Game := do
  let tokens := commandTokens tokens
  if g.announcingDividedDamage then
    match tokens with
    | [arg] =>
      let t ← parseTarget g p arg
      g.apply p (.target t)
    | _ =>
      let pairs ← parseTargetAmountPairs g p tokens
      g.apply p (.divideDamage pairs)
  else if g.announcingSameWordMultiTargets then
    match tokens with
    | [] => throw targetUsage
    | [arg] =>
      let t ← parseTarget g p arg
      g.apply p (.target t)
    | args =>
      let ts ← args.foldlM (fun acc arg => do
        let t ← parseTarget g p arg
        pure (acc.push t)) #[]
      g.apply p (.targets ts)
  else
    match tokens with
    | [arg] =>
      let t ← parseTarget g p arg
      g.apply p (.target t)
    | _ :: _ :: _ => throw sequentialTargetUsage
    | _ => throw targetUsage

#guard
  match applyTarget Tests.proposedBolt ⟨0⟩ [] with
  | .error msg => msg == targetUsage
  | .ok _ => false

#guard
  match applyTarget Tests.proposedBolt ⟨0⟩ ["nope"] with
  | .error msg => msg == targetUsage
  | .ok _ => false

#guard
  match applyTarget Tests.proposedBolt ⟨0⟩ ["1", "2"] with
  | .error msg => msg == sequentialTargetUsage
  | .ok _ => false

#guard
  match applyTarget Tests.proposedBolt ⟨0⟩ ["99999"] with
  | .error msg => msg == "no such object"
  | .ok _ => false

#guard
  match applyTarget Tests.proposedBolt ⟨0⟩ ["opponent"] with
  | .ok g' =>
    g'.pending == .activateManaAbilities ⟨0⟩ &&
    g'.stack.back!.targets == #[Target.player ⟨1⟩] &&
    g'.log.any (fun s => Tests.mentions s "chooses Nissa as a target (CR 601.2c)")
  | .error _ => false

#guard
  match applyTarget Tests.proposedBolt ⟨0⟩ ["Nissa"] with
  | .ok g' => g'.stack.back!.targets == #[Target.player ⟨1⟩]
  | .error _ => false

#guard
  let g := Tests.giftSetup
  let gid := (Tests.handCardNamed g ⟨0⟩ "Gift of Strands").id
  let tid := (Tests.namedPermanent g "Grizzly Bears").id
  match applyCast g ⟨0⟩ [toString gid] with
  | .error _ => false
  | .ok g' =>
    match applyTarget g' ⟨0⟩ [toString tid] with
    | .ok g'' =>
      g''.pending == .activateManaAbilities ⟨0⟩ &&
      g''.stack.back!.targets == #[Target.permanent tid]
    | .error _ => false

#guard
  let g := Tests.quarrelSetup
  let qid := (Tests.handCardNamed g ⟨0⟩ "Quarrel").id
  let src := (Tests.namedPermanent g "Llanowar Elves").id
  let dest := (Tests.namedPermanent g "Grizzly Bears").id
  match applyCast g ⟨0⟩ [toString qid] with
  | .error _ => false
  | .ok g' =>
    match applyTarget g' ⟨0⟩ ["Llanowar Elves"] with
    | .error _ => false
    | .ok g'' =>
      g''.pending == .chooseTargets ⟨0⟩ &&
      g''.stack.back!.targets == #[Target.permanent src] &&
      match applyTarget g'' ⟨0⟩ [toString dest] with
      | .ok g''' =>
        g'''.pending == .activateManaAbilities ⟨0⟩ &&
        g'''.stack.back!.targets == #[Target.permanent src, Target.permanent dest]
      | .error _ => false

#guard
  let g := Tests.smiteSetup
  match applyCast g ⟨0⟩ [toString (Tests.handCardNamed g ⟨0⟩ "Smite the Deathless").id] with
  | .ok g' =>
    g'.pending == .chooseTargets ⟨0⟩ &&
    g'.log.any (fun s => Tests.mentions s "begins casting Smite the Deathless") &&
    g'.log.any (fun s => Tests.mentions s "must choose a target (CR 601.2c)")
  | .error _ => false

#guard
  match applyTarget Tests.gandalfEntered ⟨0⟩ [] with
  | .error msg => msg == divideTargetUsage
  | .ok _ => false

#guard
  match applyTarget Tests.gandalfEntered ⟨0⟩ ["opponent"] with
  | .ok g' =>
    g'.pending == .none &&
    g'.stack.back!.targets == #[Target.player ⟨1⟩] &&
    g'.stack.back!.dividedDamage == #[3] &&
    g'.log.any (fun s => Tests.mentions s "chooses Nissa to be dealt 3 damage")
  | .error _ => false

#guard
  match applyTarget Tests.gandalfSplitSetup ⟨0⟩
      ["opponent", "2", toString (Tests.namedPermanent Tests.gandalfSplitSetup "Grizzly Bears").id, "1"] with
  | .ok g' =>
    g'.pending == .none &&
    g'.stack.back!.dividedDamage == #[2, 1] &&
    (g'.player ⟨1⟩).life == 20
  | .error _ => false

#guard
  match applyTarget Tests.gandalfEntered ⟨0⟩ ["opponent", "2"] with
  | .error msg => Tests.mentions msg "Must assign all remaining damage"
  | .ok _ => false

#guard
  match applyTarget Tests.proposedQuarrel ⟨0⟩ ["Llanowar Elves", "Grizzly Bears"] with
  | .error msg => msg == sequentialTargetUsage
  | .ok _ => false

#guard
  match applyTarget Tests.gazeProposed ⟨0⟩ ["Grizzly Bears"] with
  | .ok g' =>
    g'.pending == .activateManaAbilities ⟨0⟩ &&
      g'.stack.back!.targets ==
        #[Target.permanent (Tests.namedPermanent g' "Grizzly Bears").id]
  | .error _ => false

#guard
  match applyTarget Tests.gazeProposed ⟨0⟩ ["Grizzly Bears", "Gray Ogre"] with
  | .ok g' =>
    g'.pending == .activateManaAbilities ⟨0⟩ &&
      g'.stack.back!.targets ==
        #[Target.permanent (Tests.namedPermanent g' "Grizzly Bears").id,
          Target.permanent (Tests.namedPermanent g' "Gray Ogre").id]
  | .error _ => false

#guard
  match applyTarget Tests.gazeOneTarget ⟨0⟩ ["Gray Ogre"] with
  | .error msg => Tests.mentions msg "Not time to choose targets"
  | .ok _ => false

#guard
  match applyCast Tests.meagerMealSetup ⟨0⟩
      [toString (Tests.handCardNamed Tests.meagerMealSetup ⟨0⟩
        "Gollum, Silent Slinker").id, "adventure"] with
  | .ok g' =>
    g'.pending == .chooseTargets ⟨0⟩ &&
    (g'.object! g'.stack.back!.objectId).name == "Meager Meal" &&
    g'.log.any (fun s => Tests.mentions s "begins casting Meager Meal") &&
    g'.log.any (fun s => Tests.mentions s "must choose a target (CR 601.2c)")
  | .error _ => false

#guard
  match applyTarget Tests.proposedMeagerMeal ⟨0⟩ ["Chandra"] with
  | .error msg => Tests.mentions msg "Illegal target"
  | .ok _ => false

#guard
  match applyTarget Tests.proposedMeagerMeal ⟨0⟩ ["opponent"] with
  | .error msg => Tests.mentions msg "Illegal target"
  | .ok _ => false

#guard
  match applyTarget Tests.proposedMeagerMeal ⟨0⟩ ["Grizzly Bears", "Chandra"] with
  | .error msg => msg == sequentialTargetUsage
  | .ok _ => false

#guard
  match applyTarget Tests.proposedMeagerMeal ⟨0⟩ ["Grizzly Bears"] with
  | .ok g' =>
    g'.pending == .chooseTargets ⟨0⟩ &&
    g'.stack.back!.targets ==
      #[Target.permanent (Tests.namedPermanent g' "Grizzly Bears").id] &&
    match applyTarget g' ⟨0⟩ ["Chandra"] with
    | .ok g'' =>
      g''.pending == .activateManaAbilities ⟨0⟩ &&
      g''.stack.back!.targets ==
        #[Target.permanent (Tests.namedPermanent g'' "Grizzly Bears").id,
          Target.player ⟨0⟩]
    | .error _ => false
  | .error _ => false

#guard
  match Tests.proposedMeagerMeal.apply ⟨0⟩ .decline with
  | .ok g' =>
    g'.pending == .chooseTargets ⟨0⟩ &&
    g'.stack.back!.targets.isEmpty &&
    g'.log.any (fun s => Tests.mentions s "chooses no target") &&
    match applyTarget g' ⟨0⟩ ["opponent"] with
    | .ok g'' =>
      g''.pending == .activateManaAbilities ⟨0⟩ &&
      g''.stack.back!.targets == #[Target.player ⟨1⟩]
    | .error _ => false
  | .error _ => false

#guard
  match applyTarget Tests.gandalfEntered ⟨0⟩ ["opponent", "x"] with
  | .error msg => msg == divideTargetUsage
  | .ok _ => false

#guard
  match applyMode Tests.proposedWarg ⟨0⟩ [] with
  | .error msg => msg == modeUsage
  | .ok _ => false

#guard
  match applyMode Tests.proposedWarg ⟨0⟩ ["nope"] with
  | .error msg => msg == modeUsage
  | .ok _ => false

#guard
  match applyMode Tests.proposedWarg ⟨0⟩ ["0"] with
  | .error msg => msg == modeUsage
  | .ok _ => false

#guard
  match applyMode Tests.proposedWarg ⟨0⟩ ["1", "2"] with
  | .error msg => msg == modeUsage
  | .ok _ => false

#guard
  match applyMode Tests.proposedWarg ⟨0⟩ ["3"] with
  | .error msg => Tests.mentions msg "No such mode"
  | .ok _ => false

#guard
  match applyMode Tests.proposedWarg ⟨0⟩ ["1"] with
  | .ok g' =>
    g'.pending == .chooseTargets ⟨0⟩ &&
    g'.stack.back!.chosenMode == some 0 &&
    g'.log.any (fun s => Tests.mentions s "chooses mode 1")
  | .error _ => false

#guard
  match applyMode Tests.proposedWarg ⟨0⟩ ["2"] with
  | .ok g' =>
    g'.pending == .chooseTargets ⟨0⟩ &&
    g'.stack.back!.chosenMode == some 1
  | .error _ => false

def scryUsage : String := "usage: scry [top <id> ...] [bottom <id> ...]"

/-- Finish a pending scry (CR 701.20). Bare `scry` keeps the looked-at cards
on top in their current order. `scry top <ids>` puts those cards on top
(last = new top) and the rest on the bottom in their current relative order.
`scry bottom <ids>` puts those cards on the bottom (first = new bottom) and
the rest stay on top in their current relative order. Both piles may be
listed to choose each order. -/
def applyScry (g : Game) (p : PlayerId) (tokens : List String) : Except String Game := do
  match g.pending with
  | .scry q n =>
    if p != q then
      throw s!"Only {(g.player q).name} may scry"
    let looked := g.scryLookedIds p n
    let tokens := commandTokens tokens
    match tokens with
    | [] => g.apply p (.scry looked #[])
    | "bottom" :: rest =>
      let ids ← parseObjectIds rest scryUsage
      for id in ids do
        if (g.findObject? id).isNone then
          throw "no such object"
      let top := looked.filter (fun id => !ids.contains id)
      g.apply p (.scry top ids)
    | "top" :: rest =>
      let (topToks, botRest) := splitAtKeyword "bottom" rest
      let topIds ← parseObjectIds topToks scryUsage
      for id in topIds do
        if (g.findObject? id).isNone then
          throw "no such object"
      let bottomIds ←
        match botRest with
        | none => pure (looked.filter (fun id => !topIds.contains id))
        | some [] => pure #[]
        | some ts =>
          let ids ← parseObjectIds ts scryUsage
          for id in ids do
            if (g.findObject? id).isNone then
              throw "no such object"
          pure ids
      g.apply p (.scry topIds bottomIds)
    | _ => throw scryUsage
  | _ => throw "Not time to scry (CR 701.20)"

#guard
  match applyScry Tests.giftScrying ⟨0⟩ [] with
  | .ok g' => g'.pending == .none && g'.hasPriority ⟨0⟩
  | .error _ => false

#guard
  match applyScry Tests.giftSetup ⟨0⟩ [] with
  | .error msg => Tests.mentions msg "Not time to scry"
  | .ok _ => false

#guard
  match applyScry Tests.giftScrying ⟨0⟩ ["keep"] with
  | .error msg => msg == scryUsage
  | .ok _ => false

#guard
  match applyScry Tests.giftKnownScrying ⟨0⟩ ["top"] with
  | .error msg => msg == scryUsage
  | .ok _ => false

#guard
  let g := Tests.giftKnownScrying
  let looked := g.scryLookedIds ⟨0⟩ 2
  match looked[0]?, looked[1]? with
  | some forest, some elves =>
    match applyScry g ⟨0⟩ ["top", toString elves, toString forest] with
    | .ok g' =>
      (g'.object! (g'.player ⟨0⟩).library.back!).name == "Forest" &&
        g'.log.any (fun s => Tests.mentions s "puts Forest on top of their library")
    | .error _ => false
  | _, _ => false

#guard
  let g := Tests.giftKnownScrying
  let looked := g.scryLookedIds ⟨0⟩ 2
  match looked[0]?, looked[1]? with
  | some forest, some elves =>
    match applyScry g ⟨0⟩ ["top", toString forest, "bottom", toString elves] with
    | .ok g' =>
      (g'.object! (g'.player ⟨0⟩).library.back!).name == "Forest" &&
        (g'.object! (g'.player ⟨0⟩).library[0]!).name == "Llanowar Elves"
    | .error _ => false
  | _, _ => false

#guard
  let g := Tests.giftKnownScrying
  let looked := g.scryLookedIds ⟨0⟩ 2
  match looked[0]? with
  | some forest =>
    match applyScry g ⟨0⟩ ["top", toString forest] with
    | .ok g' =>
      (g'.object! (g'.player ⟨0⟩).library.back!).name == "Forest" &&
        (g'.object! (g'.player ⟨0⟩).library[0]!).name == "Llanowar Elves"
    | .error _ => false
  | none => false

def discardUsage : String := "usage: discard <id>"

/-- Discard the named card from hand for a pending “may discard, then draw”. -/
def applyDiscard (g : Game) (p : PlayerId) (tokens : List String) : Except String Game :=
  applyObjectCommand g p tokens discardUsage .discard

def declineUsage : String := "usage: decline"

/-- Decline an optional discard, attach, or choose no target for an “up to one”
instance of the word “target” (CR 115.1c / 601.2c). -/
def applyDecline (g : Game) (p : PlayerId) (tokens : List String) : Except String Game := do
  match commandTokens tokens with
  | [] => g.apply p .decline
  | _ => throw declineUsage

def attachUsage : String := "usage: attach <id>"

/-- Attach the named Equipment you control to the creature waiting for one. -/
def applyAttach (g : Game) (p : PlayerId) (tokens : List String) : Except String Game :=
  applyObjectCommand g p tokens attachUsage (fun id => .choosePermanents #[id])

#guard
  match applyDiscard Tests.spearMayDiscard ⟨0⟩ [] with
  | .error msg => msg == discardUsage
  | .ok _ => false

#guard
  match applyDiscard Tests.spearMayDiscard ⟨0⟩ ["nope"] with
  | .error msg => msg == discardUsage
  | .ok _ => false

#guard
  match applyDiscard Tests.spearMayDiscard ⟨0⟩ ["1", "2"] with
  | .error msg => msg == discardUsage
  | .ok _ => false

#guard
  match applyDiscard Tests.spearMayDiscard ⟨0⟩ ["99999"] with
  | .error msg => msg == "no such object"
  | .ok _ => false

#guard
  let g := Tests.spearKnownMayDiscard
  let forest := Tests.handCardNamed g ⟨0⟩ "Forest"
  match applyDiscard g ⟨0⟩ [toString forest.id] with
  | .ok g' =>
    g'.pending == .none &&
    g'.log.any (fun s => Tests.mentions s "discards Forest")
  | .error _ => false

#guard
  match applyDecline Tests.spearMayDiscard ⟨0⟩ ["extra"] with
  | .error msg => msg == declineUsage
  | .ok _ => false

#guard
  match applyDecline Tests.spearMayDiscard ⟨0⟩ [] with
  | .ok g' =>
    g'.pending == .none &&
    g'.log.any (fun s => Tests.mentions s "declines to discard")
  | .error _ => false

#guard
  match applyDecline Tests.proposedMeagerMeal ⟨0⟩ [] with
  | .ok g' =>
    g'.pending == .chooseTargets ⟨0⟩ &&
    g'.stack.back!.targets.isEmpty &&
    g'.log.any (fun s => Tests.mentions s "chooses no target")
  | .error _ => false

#guard
  match applyAttach Tests.vowMayAttach ⟨0⟩ [] with
  | .error msg => msg == attachUsage
  | .ok _ => false

#guard
  match applyAttach Tests.vowMayAttach ⟨0⟩ ["nope"] with
  | .error msg => msg == attachUsage
  | .ok _ => false

#guard
  match applyAttach Tests.vowMayAttach ⟨0⟩ ["1", "2"] with
  | .error msg => msg == attachUsage
  | .ok _ => false

#guard
  match applyAttach Tests.vowMayAttach ⟨0⟩ ["99999"] with
  | .error msg => msg == "no such object"
  | .ok _ => false

#guard
  match applyAttach Tests.spearMayDiscard ⟨0⟩
      [toString (Tests.namedPermanent Tests.spearMayDiscard "Ragged Short Spear").id] with
  | .error msg => Tests.mentions msg "Not time to choose permanents"
  | .ok _ => false

#guard
  match applyAttach Tests.vowMayAttach ⟨1⟩
      [toString (Tests.namedPermanent Tests.vowMayAttach "Ragged Short Spear").id] with
  | .error msg => Tests.mentions msg "Only Chandra may attach Equipment"
  | .ok _ => false

#guard
  match applyAttach Tests.vowMayAttach ⟨0⟩
      [toString (Tests.namedPermanent Tests.vowMayAttach "Bofur, Reliable Guardian").id] with
  | .error msg => Tests.mentions msg "is not an Equipment you control"
  | .ok _ => false

#guard
  let g := Tests.vowMayAttach
  let spear := Tests.namedPermanent g "Ragged Short Spear"
  match applyAttach g ⟨0⟩ [toString spear.id] with
  | .ok g' =>
    g'.pending == .none &&
    (Tests.namedPermanent g' "Ragged Short Spear").attachedTo ==
      some (Tests.namedPermanent g' "Bofur, Reliable Guardian").id &&
    g'.log.any (fun s => Tests.mentions s "attaches to Bofur")
  | .error _ => false

#guard
  match applyDecline Tests.vowMayAttach ⟨0⟩ [] with
  | .ok g' =>
    g'.pending == .none &&
    (Tests.namedPermanent g' "Ragged Short Spear").attachedTo.isNone &&
    g'.log.any (fun s => Tests.mentions s "declines to attach Equipment")
  | .error _ => false

/-- Game-changing interactive commands. `help`/`state`/`visible`/`quit` are
handled by the console loop. Actions are issued as `p`. -/
def keepUsage : String := "usage: keep [<id>]"

/-- Keep an opening hand, or choose which legendary permanent to keep
(CR 103.5 / 704.5j). -/
def applyKeep (g : Game) (p : PlayerId) (tokens : List String) : Except String Game := do
  match g.pending, commandTokens tokens with
  | .chooseLegend _ _ _, [_] =>
    applyObjectCommand g p tokens keepUsage .keepLegend
  | .chooseLegend _ _ _, _ => throw keepUsage
  | _, [] => g.apply p .keep
  | _, _ => throw keepUsage

/-- Game after `autopay`, and the `tap`/`pay` lines that produced it. -/
structure AutopayResult where
  game : Game
  commands : Array String

/-- Accepted `tap` line for one mana ability so `--output` can replay it. -/
def tapCommand (id : ObjectId) (m : ManaType) : String :=
  s!"tap {id} {m.letter}"

#guard tapCommand ⟨12⟩ (.colored .red) == "tap #12 R"
#guard tapCommand ⟨3⟩ .colorless == "tap #3 C"

def autopayUsage : String := "usage: autopay"

/-- Whether the locked-in cost is payable from the current pool. -/
def canPayProposed (g : Game) (p : PlayerId) (prop : ProposedSpell) : Bool :=
  (g.player p).manaPool.canPay prop.cost
    (g.proposedAllowsElfRestricted prop)
    (g.proposedAllowsInstRestricted prop)

/-- Activate mana abilities chosen by the heuristic, then pay (CR 601.2g–h).
Fails without changing the game if the cost cannot be paid. -/
def applyAutopaySteps (g : Game) (p : PlayerId) (fuel : Nat) (cmds : Array String) :
    Except String AutopayResult := do
  match fuel with
  | 0 => throw "Could not finish paying the cost"
  | n + 1 =>
    match g.pending with
    | .activateManaAbilities caster =>
      if caster != p then
        throw s!"Only {(g.player caster).name} may pay (CR 601.2h)"
      match Agent.chooseManaPayment g p with
      | some (.tapForMana id m) =>
        let g ← applyTap g p [toString id, m.letter]
        applyAutopaySteps g p n (cmds.push (tapCommand id m))
      | some .pay =>
        match g.proposedSpell with
        | some prop =>
          if !canPayProposed g p prop then
            throw s!"{(g.player p).name} cannot pay {prop.cost}"
          let g ← g.apply p .pay
          return { game := g, commands := cmds.push "pay" }
        | none =>
          let g ← g.apply p .pay
          return { game := g, commands := cmds.push "pay" }
      | _ =>
        match g.proposedSpell with
        | some prop => throw s!"{(g.player p).name} cannot pay {prop.cost}"
        | none => throw "No spell or ability is waiting to be paid for (CR 601.2h)"
    | .chooseMode _ => throw "Choose a mode first (CR 601.2b)"
    | .chooseTargets _ => throw "Choose a target first (CR 601.2c)"
    | .chooseAdditionalCost _ => throw "Choose an additional cost first (CR 601.2b)"
    | _ => throw "No spell or ability is waiting to be paid for (CR 601.2h)"

/-- Tap necessary mana sources (heuristic colors) and pay the current cost. -/
def applyAutopay (g : Game) (p : PlayerId) (tokens : List String) :
    Except String AutopayResult :=
  match commandTokens tokens with
  | [] => applyAutopaySteps g p ((g.manaSources p).size + 1) #[]
  | _ => .error autopayUsage

/-- Issue `autopay` as the player who currently must act. -/
def applyAutopayAsActor (g : Game) (tokens : List String) : Except String AutopayResult := do
  let p ← actingPlayer g
  applyAutopay g p tokens

#guard
  match applyAutopay Tests.targetedBolt ⟨0⟩ ["extra"] with
  | .error msg => msg == autopayUsage
  | .ok _ => false

#guard
  match applyAutopay Tests.drawnHands ⟨0⟩ [] with
  | .error msg => msg == "No spell or ability is waiting to be paid for (CR 601.2h)"
  | .ok _ => false

#guard
  match applyAutopay Tests.proposedBolt ⟨0⟩ [] with
  | .error msg => Tests.mentions msg "Choose a target first"
  | .ok _ => false

#guard
  match applyAutopay Tests.proposedOgre ⟨0⟩ [] with
  | .error msg => Tests.mentions msg "cannot pay"
  | .ok _ => false

#guard
  match applyAutopay Tests.targetedBolt ⟨0⟩ [] with
  | .ok r =>
    r.commands == #[tapCommand Tests.boltMountain.id (.colored .red), "pay"] &&
      r.game.pending == .none &&
      r.game.proposedSpell.isNone &&
      (r.game.player ⟨0⟩).manaPool.isEmpty &&
      r.game.log.any (fun s => Tests.mentions s "casts Lightning Bolt")
  | .error _ => false

#guard
  match applyAutopay Tests.tappedForBolt ⟨0⟩ [] with
  | .ok r =>
    r.commands == #["pay"] &&
      r.game.log.any (fun s => Tests.mentions s "casts Lightning Bolt")
  | .error _ => false

#guard
  match applyAutopay Tests.proposedVisionary ⟨0⟩ [] with
  | .ok r =>
    r.commands == #["pay"] &&
      r.game.log.any (fun s => Tests.mentions s "casts Elvish Visionary")
  | .error _ => false

#guard
  let g := Tests.proposedBauble
  let lands := (g.permanentsOf ⟨0⟩).filter (·.printed.isLand)
  lands.size == 2 &&
  match applyAutopay g ⟨0⟩ [] with
  | .ok r =>
    r.commands ==
      #[tapCommand lands[0]!.id (.colored .red),
        tapCommand lands[1]!.id (.colored .red), "pay"] &&
      r.game.pending == .none &&
      r.game.log.any (fun s => Tests.mentions s "activates Wayfarer's Bauble")
  | .error _ => false

#guard
  let g0 := Tests.weavemasterElfSetup.emptyManaPools
  let elves := Tests.handCardNamed g0 ⟨0⟩ "Llanowar Elves"
  match g0.apply ⟨0⟩ (.cast elves.id) with
  | .error _ => false
  | .ok proposed =>
    let w := Tests.namedPermanent proposed "Woodland Weavemaster"
    match applyAutopay proposed ⟨0⟩ [] with
    | .ok r =>
      r.commands == #[tapCommand w.id (.colored .green), "pay"] &&
        (Tests.namedPermanent r.game "Woodland Weavemaster").status.tapped &&
        r.game.log.any (fun s => Tests.mentions s "casts Llanowar Elves")
    | .error _ => false

#guard
  match applyAutopay Tests.forestFirstBolt ⟨0⟩ [] with
  | .ok r =>
    let mountain := Tests.namedPermanent Tests.forestFirstBolt "Mountain"
    r.commands == #[tapCommand mountain.id (.colored .red), "pay"] &&
      (Tests.namedPermanent r.game "Forest").status.tapped == false &&
      r.game.log.any (fun s => Tests.mentions s "casts Lightning Bolt")
  | .error _ => false

#guard
  match applyAutopay Tests.weavemasterForestGrowth ⟨0⟩ [] with
  | .ok r =>
    let forest := Tests.namedPermanent Tests.weavemasterForestGrowth "Forest"
    r.commands == #[tapCommand forest.id (.colored .green), "pay"] &&
      (Tests.namedPermanent r.game "Woodland Weavemaster").status.tapped == false &&
      r.game.log.any (fun s => Tests.mentions s "casts Giant Growth")
  | .error _ => false

#guard
  match applyAutopay Tests.delightedHalflingForestGrowth ⟨0⟩ [] with
  | .ok r =>
    let forest := Tests.namedPermanent Tests.delightedHalflingForestGrowth "Forest"
    r.commands == #[tapCommand forest.id (.colored .green), "pay"] &&
      (Tests.namedPermanent r.game "Delighted Halfling").status.tapped == false &&
      r.game.log.any (fun s => Tests.mentions s "casts Giant Growth")
  | .error _ => false

#guard
  match applyAutopay Tests.delightedHalflingGrowth ⟨0⟩ [] with
  | .error msg =>
    Tests.mentions msg "cannot pay" &&
      !(Tests.namedPermanent Tests.delightedHalflingGrowth "Delighted Halfling").status.tapped
  | .ok _ => false

def applyInteractiveAction (g : Game) (p : PlayerId) (cmd : String) (args : List String) :
    Except String Game :=
  match cmd with
  | "keep" => applyKeep g p args
  | "stack" => applyStack g p args
  | "mulligan" => g.apply p .takeMulligan
  | "bottom" => applyBottom g p args
  | "pass" => g.apply p .pass
  | "pay" => g.apply p .pay
  | "autopay" => applyAutopay g p args |>.map (·.game)
  | "pay-extra" => applyPayExtra g p args
  | "sacrifice" => applySacrifice g p args
  | "concede" => g.apply p .concede
  | "attack" => applyAttack g p args
  | "noattack" => g.apply p (.declareAttackers #[])
  | "block" => applyBlock g p args
  | "noblock" => g.apply p (.declareBlockers #[])
  | "assign" => applyAssign g p args
  | "play" => applyPlay g p args
  | "activate" => applyActivate g p args
  | "mode" => applyMode g p args
  | "tap" => applyTap g p args
  | "cast" => applyCast g p args
  | "target" => applyTarget g p args
  | "scry" => applyScry g p args
  | "discard" => applyDiscard g p args
  | "attach" => applyAttach g p args
  | "decline" => applyDecline g p args
  | _ => .error s!"Unknown command: {cmd}"

/-- Issue a console command as the player who currently must act. -/
def applyInteractiveAsActor (g : Game) (cmd : String) (args : List String) : Except String Game := do
  let p ← actingPlayer g
  applyInteractiveAction g p cmd args

/-- Apply a game-state command. `autopay` expands to the `tap`/`pay` lines
that `--output` should record. -/
def applyLoggedAction (g : Game) (cmd : String) (args : List String) (line : String) :
    Except String (Game × Array String) := do
  if cmd == "autopay" then
    let r ← applyAutopayAsActor g args
    return (r.game, r.commands)
  else
    let g' ← applyInteractiveAsActor g cmd args
    return (g', #[line])

#guard
  match applyInteractiveAsActor Tests.drawnHands "keep" [] with
  | .ok g' => (g'.player ⟨0⟩).keptOpeningHand && g'.actor == some ⟨1⟩
  | .error _ => false

#guard
  match applyKeep Tests.drawnHands ⟨0⟩ ["1"] with
  | .error msg => msg == keepUsage
  | .ok _ => false

#guard
  match applyKeep Tests.twoBofursSBA ⟨0⟩ [] with
  | .error msg => msg == keepUsage
  | .ok _ => false

#guard
  match Tests.twoBofursSBA.pending with
  | .chooseLegend _ _ ids =>
    match applyInteractiveAsActor Tests.twoBofursSBA "keep" [toString ids[0]!] with
    | .ok g' =>
      (g'.battlefield.filter (·.name == "Bofur, Reliable Guardian")).size == 1 &&
      g'.log.any (fun s => Tests.mentions s "704.5j")
    | .error _ => false
  | _ => false

#guard
  match applyStack Tests.twoAttercopsLandPending ⟨0⟩ [] with
  | .error msg => msg == stackUsage
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
  match applyInteractiveAsActor Tests.afterChandraDeclaresMulligan "keep" [] with
  | .ok g' => (g'.player ⟨1⟩).keptOpeningHand
  | .error _ => false

#guard
  match applyInteractiveAsActor Tests.nissaDraw "pass" [] with
  | .ok g' => g'.hasPriority ⟨0⟩ && g'.actor == some ⟨0⟩
  | .error _ => false

#guard
  match applyInteractiveAsActor Tests.nissaDraw "concede" [] with
  | .ok g' =>
    match g'.result with
    | some (.won p) => p == ⟨0⟩
    | _ => false
  | .error _ => false

#guard
  match applyInteractiveAsActor Tests.proposedBolt "target" ["opponent"] with
  | .ok g' =>
    g'.pending == .activateManaAbilities ⟨0⟩ &&
    g'.stack.back!.targets == #[Target.player ⟨1⟩]
  | .error _ => false

#guard
  match applyInteractiveAsActor Tests.guttersnipeBoltSetup "cast"
      [toString (Tests.handCardNamed Tests.guttersnipeBoltSetup ⟨0⟩ "Lightning Bolt").id] with
  | .ok g' =>
    g'.pending == .chooseTargets ⟨0⟩ &&
    g'.log.any (fun s => Tests.mentions s "begins casting Lightning Bolt")
  | .error _ => false

#guard
  match applyInteractiveAsActor Tests.paidGuttersnipeBolt "pass" [] with
  | .ok g1 =>
    match applyInteractiveAsActor g1 "pass" [] with
    | .ok g' =>
      (g'.player ⟨1⟩).life == 18 &&
      g'.stack.size == 1 &&
      (g'.object! g'.stack.back!.objectId).name == "Lightning Bolt"
    | .error _ => false
  | .error _ => false

#guard
  match applyInteractiveAsActor Tests.hospitalityLandPlayed "target"
      [toString (Tests.namedPermanent Tests.hospitalityLandPlayed "Grizzly Bears").id] with
  | .ok g' =>
    g'.pending == .none &&
    g'.hasPriority ⟨0⟩ &&
    g'.stack.back!.targets ==
      #[Target.permanent (Tests.namedPermanent g' "Grizzly Bears").id]
  | .error _ => false

#guard
  match applyInteractiveAsActor Tests.gandalfEntered "target" ["opponent"] with
  | .ok g' =>
    g'.pending == .none &&
    g'.stack.back!.dividedDamage == #[3]
  | .error _ => false

#guard
  match applyInteractiveAsActor Tests.titanEntered "target" ["opponent"] with
  | .ok g' =>
    g'.pending == .none &&
    g'.stack.back!.dividedDamage == #[3]
  | .error _ => false

#guard
  match applyInteractiveAsActor Tests.titanAttackDeclared "target" ["opponent"] with
  | .ok g' =>
    g'.pending == .none &&
    g'.stack.back!.dividedDamage == #[3]
  | .error _ => false

#guard
  let sid := Tests.paidBolt.stack.back!.objectId
  match parseTarget Tests.paidBolt ⟨0⟩ (toString sid) with
  | .ok (Target.card id) => id == sid
  | _ => false

#guard
  match applyTarget Tests.proposedDecree ⟨1⟩
      [toString Tests.paidBolt.stack.back!.objectId] with
  | .ok g' =>
    g'.pending == .activateManaAbilities ⟨1⟩ &&
    g'.stack.back!.targets == #[Target.card Tests.paidBolt.stack.back!.objectId] &&
    g'.log.any (fun s => Tests.mentions s "chooses Lightning Bolt as a target (CR 601.2c)")
  | .error _ => false

#guard
  match applyTarget Tests.proposedDecree ⟨1⟩ ["Lightning Bolt"] with
  | .ok g' =>
    g'.stack.back!.targets == #[Target.card Tests.paidBolt.stack.back!.objectId]
  | .error _ => false

#guard
  match applyInteractiveAsActor Tests.proposedDecree "target"
      [toString Tests.paidBolt.stack.back!.objectId] with
  | .ok g' =>
    g'.stack.back!.targets == #[Target.card Tests.paidBolt.stack.back!.objectId]
  | .error _ => false

#guard
  match applyTarget Tests.elkEntered ⟨0⟩
      [toString (Tests.namedGraveyardCard Tests.elkEntered ⟨0⟩ "Llanowar Elves").id] with
  | .ok g' =>
    g'.pending == .none &&
    g'.hasPriority ⟨0⟩ &&
    g'.stack.back!.targets ==
      #[Target.card (Tests.namedGraveyardCard Tests.elkEntered ⟨0⟩ "Llanowar Elves").id]
  | .error _ => false

#guard
  match applyTarget Tests.elkEntered ⟨0⟩ ["Llanowar Elves"] with
  | .ok g' =>
    g'.stack.back!.targets ==
      #[Target.card (Tests.namedGraveyardCard Tests.elkEntered ⟨0⟩ "Llanowar Elves").id]
  | .error _ => false

#guard
  match applyInteractiveAsActor Tests.elkEntered "target"
      [toString (Tests.namedGraveyardCard Tests.elkEntered ⟨0⟩ "Llanowar Elves").id] with
  | .ok g' =>
    g'.pending == .none &&
    g'.hasPriority ⟨0⟩ &&
    g'.stack.back!.targets ==
      #[Target.card (Tests.namedGraveyardCard g' ⟨0⟩ "Llanowar Elves").id]
  | .error _ => false

#guard
  match applyInteractiveAsActor Tests.elkEntered "target" ["Llanowar Elves"] with
  | .ok g' =>
    g'.stack.back!.targets ==
      #[Target.card (Tests.namedGraveyardCard Tests.elkEntered ⟨0⟩ "Llanowar Elves").id]
  | .error _ => false

#guard
  match applyInteractiveAsActor Tests.elkEntered "decline" [] with
  | .error msg => Tests.mentions msg "requires a target"
  | .ok _ => false

#guard
  match applyInteractiveAsActor Tests.elkAttackDeclared "target" ["Llanowar Elves"] with
  | .ok g' =>
    g'.pending == .none &&
    g'.stack.back!.targets ==
      #[Target.card (Tests.namedGraveyardCard Tests.elkAttackDeclared ⟨0⟩ "Llanowar Elves").id]
  | .error _ => false

#guard
  match applyInteractiveAsActor Tests.titanPumpReady "activate"
      [toString (Tests.titanSource Tests.titanPumpReady).id] with
  | .ok g' =>
    g'.pending == .activateManaAbilities ⟨0⟩ &&
    g'.log.any (fun s => Tests.mentions s "begins activating Inferno Titan")
  | .error _ => false

#guard
  match applyInteractiveAsActor Tests.passageReady "activate"
      [toString (Tests.passageSource Tests.passageReady).id] with
  | .ok g' =>
    g'.pending == .chooseTargets ⟨0⟩ &&
    g'.log.any (fun s => Tests.mentions s "begins activating Rogue's Passage")
  | .error _ => false

#guard
  let g := Tests.dunedainReady
  let blade := Tests.namedPermanent g "Dúnedain Blade"
  let bears := Tests.namedPermanent g "Grizzly Bears"
  match applyActivate g ⟨0⟩ [toString blade.id] with
  | .error _ => false
  | .ok g' =>
    match applyTarget g' ⟨0⟩ [toString bears.id] with
    | .error msg => Tests.mentions msg "Illegal target"
    | .ok _ => false

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
  match applyInteractiveAsActor Tests.dunedainReady "activate"
      [toString (Tests.namedPermanent Tests.dunedainReady "Dúnedain Blade").id, "2"] with
  | .ok g' =>
    g'.pending == .chooseTargets ⟨0⟩ &&
    g'.log.any (fun s => Tests.mentions s "begins activating Dúnedain Blade")
  | .error _ => false

#guard
  match applyInteractiveAsActor Tests.oliphauntCycleReady "activate"
      [toString (Tests.handCardNamed Tests.oliphauntCycleReady ⟨0⟩ "Oliphaunt").id] with
  | .ok g' =>
    g'.pending == .activateManaAbilities ⟨0⟩ &&
    g'.log.any (fun s => Tests.mentions s "begins activating Oliphaunt")
  | .error _ => false

#guard
  match applyInteractiveAsActor Tests.galionAttackDeclared "target"
      [toString (Tests.namedPermanent Tests.galionAttackDeclared "Llanowar Elves").id] with
  | .ok g' =>
    g'.pending == .none &&
    g'.hasPriority ⟨0⟩ &&
    g'.stack.back!.targets ==
      #[Target.permanent (Tests.namedPermanent g' "Llanowar Elves").id]
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
  match applyInteractiveAsActor Tests.oliphauntAttackDeclared "target"
      [toString (Tests.namedPermanent Tests.oliphauntAttackDeclared "Gray Ogre").id] with
  | .ok g' =>
    g'.pending == .none &&
    g'.hasPriority ⟨0⟩ &&
    g'.stack.back!.targets ==
      #[Target.permanent (Tests.namedPermanent g' "Gray Ogre").id]
  | .error _ => false

#guard
  match applyInteractiveAsActor Tests.oliphauntAttackDeclared "decline" [] with
  | .error msg => Tests.mentions msg "requires a target"
  | .ok _ => false

#guard
  match applyInteractiveAsActor Tests.hospitalityAnimateSetup "activate"
      [toString (Tests.namedPermanent Tests.hospitalityAnimateSetup "Beorn's Hospitality").id] with
  | .ok g' =>
    g'.pending == .activateManaAbilities ⟨0⟩ &&
    g'.log.any (fun s => Tests.mentions s "begins activating Beorn's Hospitality")
  | .error _ => false

#guard
  match applyInteractiveAsActor Tests.readyToDeclareBlockers "block" [] with
  | .ok g' =>
    (Tests.namedPermanent g' "Grizzly Bears").status.blocking ==
      #[(Tests.namedPermanent g' "Gray Ogre").id]
  | .error _ => false

#guard
  match applyInteractiveAsActor Tests.ogreVsCrusherReadyToBlock "block" [] with
  | .ok g' =>
    (Tests.namedPermanent g' "Olog-hai Crusher").status.blocking.isEmpty &&
      !(Tests.namedPermanent g' "Gray Ogre").status.blocked
  | .error _ => false

#guard
  match applyInteractiveAsActor Tests.ogreVsCrusherAndGoblinReadyToBlock "block" [] with
  | .ok g' =>
    (Tests.namedPermanent g' "Olog-hai Crusher").status.blocking ==
      #[(Tests.namedPermanent g' "Gray Ogre").id]
  | .error _ => false

#guard
  match blockAssignmentsForCommand Tests.gollumVsOneBearReadyToBlock [] with
  | .ok asgn => asgn.isEmpty
  | .error _ => false

#guard
  match applyInteractiveAsActor Tests.gollumVsOneBearReadyToBlock "block" [] with
  | .ok g' =>
    (Tests.namedPermanent g' "Grizzly Bears").status.blocking.isEmpty &&
      !(Tests.namedPermanent g' "Gollum, Silent Slinker").status.blocked
  | .error _ => false

#guard
  match blockAssignmentsForCommand Tests.gollumVsTwoBearsReadyToBlock [] with
  | .ok asgn =>
    let g := Tests.gollumVsTwoBearsReadyToBlock
    let gollum := Tests.namedPermanent g "Gollum, Silent Slinker"
    asgn.size == 2 && asgn.all (fun (_, a) => a == gollum.id)
  | .error _ => false

#guard
  match applyInteractiveAsActor Tests.gollumVsTwoBearsReadyToBlock "block" [] with
  | .ok g' =>
    (Tests.namedPermanent g' "Gollum, Silent Slinker").status.blocked &&
      (g'.battlefield.filter (fun o =>
        o.name == "Grizzly Bears" && o.status.blocking ==
          #[(Tests.namedPermanent g' "Gollum, Silent Slinker").id])).size == 2
  | .error _ => false

#guard
  match blockAssignmentsForCommand Tests.gollumAndOgreVsOneBearReadyToBlock [] with
  | .ok asgn =>
    let g := Tests.gollumAndOgreVsOneBearReadyToBlock
    asgn == #[(
      (Tests.namedPermanent g "Grizzly Bears").id,
      (Tests.namedPermanent g "Gray Ogre").id)]
  | .error _ => false

#guard
  match applyInteractiveAsActor Tests.gollumAndOgreVsOneBearReadyToBlock "block" [] with
  | .ok g' =>
    (Tests.namedPermanent g' "Grizzly Bears").status.blocking ==
      #[(Tests.namedPermanent g' "Gray Ogre").id] &&
      !(Tests.namedPermanent g' "Gollum, Silent Slinker").status.blocked
  | .error _ => false

#guard
  match applyInteractiveAsActor Tests.readyToDeclareAttackers "noattack" [] with
  | .ok g' => !(g'.battlefield.any (·.status.attacking))
  | .error _ => false

#guard
  match applyInteractiveAsActor Tests.giftScrying "scry" [] with
  | .ok g' => g'.pending == .none && g'.hasPriority ⟨0⟩
  | .error _ => false

#guard
  match applyInteractiveAsActor Tests.spearMayDiscard "decline" [] with
  | .ok g' => g'.pending == .none && g'.hasPriority ⟨0⟩
  | .error _ => false

#guard
  match applyInteractiveAsActor Tests.vowMayAttach "attach"
      [toString (Tests.namedPermanent Tests.vowMayAttach "Ragged Short Spear").id] with
  | .ok g' =>
    g'.pending == .none &&
    g'.hasPriority ⟨0⟩ &&
    (Tests.namedPermanent g' "Ragged Short Spear").attachedTo ==
      some (Tests.namedPermanent g' "Bofur, Reliable Guardian").id &&
    g'.log.any (fun s => Tests.mentions s "attaches to Bofur")
  | .error _ => false

#guard
  match applyInteractiveAsActor Tests.vowMayAttach "decline" [] with
  | .ok g' =>
    g'.pending == .none &&
    g'.hasPriority ⟨0⟩ &&
    (Tests.namedPermanent g' "Ragged Short Spear").attachedTo.isNone &&
    g'.log.any (fun s => Tests.mentions s "declines to attach Equipment")
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
  match applyInteractiveAsActor Tests.guideSetup "cast"
      [toString (Tests.handCardNamed Tests.guideSetup ⟨0⟩ "Galadhrim Guide").id] with
  | .ok g' =>
    g'.pending == .activateManaAbilities ⟨0⟩ &&
      g'.log.any (fun s => Tests.mentions s "begins casting Galadhrim Guide")
  | .error _ => false

#guard
  match applyInteractiveAsActor Tests.guideScrying "scry" [] with
  | .ok g' =>
    g'.pending == .none && g'.hasPriority ⟨0⟩ &&
      g'.battlefield.any (fun o => o.name == "Galadhrim Guide")
  | .error _ => false

#guard
  match applyInteractiveAsActor Tests.lookoutScrying "scry" [] with
  | .ok g' =>
    g'.pending == .none && g'.hasPriority ⟨0⟩ &&
      g'.battlefield.any (fun o => o.name == "Lothlórien Lookout")
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

#guard
  match applyInteractiveAsActor Tests.visionarySetup "cast"
      [toString (Tests.handCardNamed Tests.visionarySetup ⟨0⟩ "Elvish Visionary").id] with
  | .ok g' =>
    g'.pending == .activateManaAbilities ⟨0⟩ &&
      g'.log.any (fun s => Tests.mentions s "begins casting Elvish Visionary")
  | .error _ => false

#guard
  match applyInteractiveAsActor Tests.visionaryKnownLib "pass" [] with
  | .ok g1 =>
    match applyInteractiveAsActor g1 "pass" [] with
    | .ok g' =>
      g'.stack.isEmpty &&
      g'.log.any (fun s => Tests.mentions s "draws Forest") &&
      (g'.handObjects ⟨0⟩).any (fun o => o.name == "Forest")
    | .error _ => false
  | .error _ => false

#guard
  match applyInteractiveAsActor Tests.woodElvesSetup "cast"
      [toString (Tests.handCardNamed Tests.woodElvesSetup ⟨0⟩ "Wood Elves").id] with
  | .ok g' =>
    g'.pending == .activateManaAbilities ⟨0⟩ &&
      g'.log.any (fun s => Tests.mentions s "begins casting Wood Elves")
  | .error _ => false

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
  let g := Tests.weavemasterReady
  let w := Tests.namedPermanent g "Woodland Weavemaster"
  match applyTap g ⟨0⟩ [toString w.id] with
  | .ok g' =>
    (Tests.namedPermanent g' "Woodland Weavemaster").status.tapped &&
      (g'.player ⟨0⟩).manaPool.elfGreen == 1 &&
      (g'.player ⟨0⟩).manaPool.canPay (ManaCost.ofColor .green) true
  | .error _ => false

#guard
  let g := Tests.weavemasterReady
  let w := Tests.namedPermanent g "Woodland Weavemaster"
  match applyTap g ⟨0⟩ [toString w.id, "W"] with
  | .ok g' =>
    (g'.player ⟨0⟩).manaPool.elfWhite == 1 &&
      (g'.player ⟨0⟩).manaPool.green == 0
  | .error _ => false

#guard
  match applyInteractiveAsActor Tests.weavemasterElfSetup "cast"
      [toString (Tests.handCardNamed Tests.weavemasterElfSetup ⟨0⟩ "Llanowar Elves").id] with
  | .ok g' =>
    g'.pending == .activateManaAbilities ⟨0⟩ &&
      g'.log.any (fun s => Tests.mentions s "begins casting Llanowar Elves")
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
  match applyInteractiveAsActor Tests.attercopLandPlayed "pass" [] with
  | .ok g1 =>
    match applyInteractiveAsActor g1 "pass" [] with
    | .ok g' =>
      g'.power (Tests.namedPermanent g' "Attercop") == 3 &&
        g'.toughness (Tests.namedPermanent g' "Attercop") == 2 &&
        g'.log.any (fun s => Tests.mentions s "Attercop gets +1/+1 until end of turn")
    | .error _ => false
  | .error _ => false

#guard
  match applyInteractiveAsActor Tests.weavemasterAttackDeclared "pass" [] with
  | .ok g' =>
    !(Tests.namedPermanent g' "Woodland Weavemaster").status.tapped &&
      (Tests.namedPermanent g' "Woodland Weavemaster").status.attacking
  | .error _ => false

#guard
  match applyInteractiveAsActor Tests.pathmakerSetup "cast"
      [toString (Tests.handCardNamed Tests.pathmakerSetup ⟨0⟩ "Mirkwood Pathmaker").id] with
  | .ok g' =>
    g'.pending == .activateManaAbilities ⟨0⟩ &&
      g'.log.any (fun s => Tests.mentions s "begins casting Mirkwood Pathmaker")
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
  match applyInteractiveAsActor Tests.archAndElves "tap"
      [toString (Tests.namedPermanent Tests.archAndElves "Elvish Archdruid").id] with
  | .ok g' =>
    (g'.player ⟨0⟩).manaPool.green == 2 &&
      (Tests.namedPermanent g' "Elvish Archdruid").status.tapped &&
      g'.log.any (fun s => Tests.mentions s "taps Elvish Archdruid for green ×2")
  | .error _ => false

#guard
  match applyInteractiveAsActor Tests.proposedWarg "mode" ["1"] with
  | .ok g' =>
    g'.pending == .chooseTargets ⟨0⟩ &&
    g'.stack.back!.chosenMode == some 0
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
  match applyInteractiveAsActor Tests.giantReadyToAssign "assign" [] with
  | .ok g' =>
    g'.pending == .none &&
    g'.log.any (fun s => Tests.mentions s "Hill Giant deals 3 combat damage")
  | .error _ => false

#guard
  let g := Tests.giftKnownScrying
  let looked := g.scryLookedIds ⟨0⟩ 2
  match looked[0]?, looked[1]? with
  | some forest, some elves =>
    match applyInteractiveAsActor g "scry" ["top", toString elves, toString forest] with
    | .ok g' => (g'.object! (g'.player ⟨0⟩).library.back!).name == "Forest"
    | .error _ => false
  | _, _ => false

#guard
  match applyInteractiveAsActor Tests.drawnHands "xyzzy" [] with
  | .error msg => msg == "Unknown command: xyzzy"
  | .ok _ => false

#guard
  match applyInteractiveAsActor Tests.targetedBolt "autopay" [] with
  | .ok g' =>
    g'.pending == .none &&
      g'.log.any (fun s => Tests.mentions s "casts Lightning Bolt")
  | .error _ => false

#guard
  match applyLoggedAction Tests.targetedBolt "autopay" [] "autopay" with
  | .ok (g', cmds) =>
    cmds == #[tapCommand Tests.boltMountain.id (.colored .red), "pay"] &&
      g'.log.any (fun s => Tests.mentions s "casts Lightning Bolt")
  | .error _ => false

#guard
  match applyLoggedAction Tests.drawnHands "keep" [] "keep" with
  | .ok (_, cmds) => cmds == #["keep"]
  | .error _ => false

#guard
  match applyLoggedAction Tests.proposedOgre "autopay" [] "autopay" with
  | .error msg => Tests.mentions msg "cannot pay"
  | .ok _ => false

/-- A line that starts with `--` is additional flags, not a game command. -/
def isFlagLine (s : String) : Bool :=
  s.startsWith "--"

#guard isFlagLine "--visible"
#guard isFlagLine "--seed 42"
#guard isFlagLine "--name Elspeth --deck white"
#guard !isFlagLine "keep"
#guard !isFlagLine "first Chandra"
#guard !isFlagLine "visible"

/-- Flags and remaining commands from an `--input` file. -/
structure InputScript where
  flags : List String
  commands : List String

/-- Split trimmed non-empty lines into flag lines and commands. -/
def inputScriptFromLines (lines : Array String) : InputScript :=
  let trimmed := lines.toList.map (fun s => s.trimAscii.copy) |>.filter (fun s => !s.isEmpty)
  {
    flags := trimmed.filter isFlagLine
    commands := trimmed.filter (fun s => !isFlagLine s)
  }

/-- Non-empty trimmed commands from an input file (one command per line).
Flag lines that start with `--` are omitted. -/
def commandsFromLines (lines : Array String) : List String :=
  (inputScriptFromLines lines).commands

/-- Command-line tokens from flag lines in `--input`. -/
def flagTokens (flagLines : List String) : List String :=
  flagLines.foldl (fun acc line => acc ++ commandTokens (line.splitOn " ")) []

#guard commandsFromLines #["keep", "pass"] == ["keep", "pass"]
#guard commandsFromLines #["  keep  ", "", "pass"] == ["keep", "pass"]
#guard commandsFromLines #["", "  \t  "] == []
#guard commandsFromLines #["keep\r", "bottom 3 4"] == ["keep", "bottom 3 4"]
#guard commandsFromLines #["--visible", "keep", "pass"] == ["keep", "pass"]
#guard (inputScriptFromLines #["--visible", "keep", "pass"]).flags == ["--visible"]
#guard (inputScriptFromLines #["--visible", "keep", "pass"]).commands == ["keep", "pass"]
#guard (inputScriptFromLines #["--seed 42", "--name Elspeth", "keep"]).flags ==
  ["--seed 42", "--name Elspeth"]
#guard (inputScriptFromLines #["keep", "--visible", "pass"]).flags == ["--visible"]
#guard (inputScriptFromLines #["keep", "--visible", "pass"]).commands == ["keep", "pass"]
#guard (inputScriptFromLines #["  --visible  ", "", "keep"]).flags == ["--visible"]
#guard flagTokens ["--visible"] == ["--visible"]
#guard flagTokens ["--seed 42", "--visible"] == ["--seed", "42", "--visible"]
#guard flagTokens ["--name Elspeth --deck white"] ==
  ["--name", "Elspeth", "--deck", "white"]
#guard flagTokens ["--decides", "Nissa"] == ["--decides", "Nissa"]
#guard flagTokens [] == []

/-- Load `--input` flags and commands, or empty lists when no file was given. -/
def loadInputScript (inputFile : Option String) : IO (Except String InputScript) := do
  match inputFile with
  | none => return .ok { flags := [], commands := [] }
  | some path =>
    try
      let lines ← IO.FS.lines path
      return .ok (inputScriptFromLines lines)
    catch e =>
      return .error s!"Failed to read input file {path}: {e}"

/-- True when `--input` and `--output` name the same file. -/
def sameInputOutput (inputFile outputFile : Option String) : Bool :=
  match inputFile, outputFile with
  | some i, some o => i == o
  | _, _ => false

#guard sameInputOutput (some "session.txt") (some "session.txt")
#guard !sameInputOutput (some "opening.txt") (some "session.txt")
#guard !sameInputOutput none (some "session.txt")
#guard !sameInputOutput (some "session.txt") none
#guard !sameInputOutput none none

/-- Write flags from `--input` at the start of `--output` only when they are
different files. Same-file sessions already contain those lines. -/
def shouldWriteInputFlags (sameFile : Bool) (flags : List String) : Bool :=
  !sameFile && !flags.isEmpty

#guard shouldWriteInputFlags false ["--visible"]
#guard shouldWriteInputFlags false ["--seed 42", "--visible"]
#guard !shouldWriteInputFlags true ["--visible"]
#guard !shouldWriteInputFlags false []
#guard !shouldWriteInputFlags true []

/-- When input and output are the same file, commands already loaded from the
file stay there; only new console commands are appended. -/
def shouldRecordCommand (sameFile : Bool) (fromInput : Bool) : Bool :=
  !(sameFile && fromInput)

#guard shouldRecordCommand false false
#guard shouldRecordCommand false true
#guard shouldRecordCommand true false
#guard !shouldRecordCommand true true

/-- Inspection and session commands never change the game, so they are not
written to `--output`. -/
def isNonStateCommand (cmd : String) : Bool :=
  match cmd with
  | "help" | "state" | "visible" | "quit" | "exit" => true
  | _ => false

#guard isNonStateCommand "state"
#guard isNonStateCommand "quit"
#guard isNonStateCommand "exit"
#guard isNonStateCommand "help"
#guard isNonStateCommand "visible"
#guard !isNonStateCommand "keep"
#guard !isNonStateCommand "pass"
#guard !isNonStateCommand "first"
#guard !isNonStateCommand "play"

/-- Write a command to `--output` only when it was accepted as a game action
and is not already stored because `--input` is the same path. Incorrect
commands and session commands such as `state` and `quit` are omitted. -/
def shouldWriteOutput (sameFile fromInput accepted : Bool) (cmd : String) : Bool :=
  accepted && !isNonStateCommand cmd && shouldRecordCommand sameFile fromInput

#guard shouldWriteOutput false false true "keep"
#guard shouldWriteOutput false false true "first"
#guard shouldWriteOutput false false true "target"
#guard shouldWriteOutput false true true "pass"
#guard shouldWriteOutput true false true "keep"
#guard !shouldWriteOutput false false true "state"
#guard !shouldWriteOutput false false true "quit"
#guard !shouldWriteOutput false false true "exit"
#guard !shouldWriteOutput false false true "help"
#guard !shouldWriteOutput false false true "visible"
#guard !shouldWriteOutput false false false "keep"
#guard !shouldWriteOutput false false false "first"
#guard !shouldWriteOutput true true true "keep"

/-- Next console command: remaining file lines first, then stdin. File lines
are echoed after the prompt so a replay looks like a typed session. -/
def nextCommandLine (pending : List String) : IO (String × List String) := do
  match pending with
  | line :: rest =>
    IO.println line
    return (line, rest)
  | [] =>
    let stdin ← IO.getStdin
    return ((← stdin.getLine).trimAscii.copy, [])

/-- Next command from `--input` or the console. The third result is whether
the line came from the input file. -/
def nextSessionCommand (pending : List String) :
    IO (String × List String × Bool) := do
  let fromInput := !pending.isEmpty
  let (line, rest) ← nextCommandLine pending
  return (line, rest, fromInput)

/-- Open `--output` for writing, or `none` when no file was given. `append`
keeps existing contents (used when the file is also `--input`). -/
def openOutputFile (outputFile : Option String) (append : Bool := false) :
    IO (Except String (Option IO.FS.Handle)) := do
  match outputFile with
  | none => return .ok none
  | some path =>
    try
      let mode := if append then IO.FS.Mode.append else IO.FS.Mode.write
      let h ← IO.FS.Handle.mk path mode
      return .ok (some h)
    catch e =>
      return .error s!"Failed to write output file {path}: {e}"

/-- Append a command to the `--output` file, if any. -/
def recordCommand (output : Option IO.FS.Handle) (line : String) : IO Unit := do
  match output with
  | none => pure ()
  | some h =>
    h.putStrLn line
    h.flush

/-- Append an accepted game-state command to `--output`, unless it is already
in the file because `--input` is the same path. -/
def recordAcceptedCommand (output : Option IO.FS.Handle)
    (sameFile fromInput : Bool) (line : String) : IO Unit := do
  if shouldWriteOutput sameFile fromInput true ((line.splitOn " ").headD "") then
    recordCommand output line

/-- Write flags read from `--input` to `--output` when they are different files. -/
def recordInputFlags (output : Option IO.FS.Handle) (sameFile : Bool)
    (flags : List String) : IO Unit := do
  if shouldWriteInputFlags sameFile flags then
    for line in flags do
      recordCommand output line

/-- Whether a player with priority has a legal action that affects the game
other than passing or conceding. Mana abilities count even when their mana
would not currently be useful, since tapping their source changes the game. -/
def hasGameStatePriorityAction (g : Game) (p : PlayerId) : Bool :=
  if !g.hasPriority p then false
  else
    let available := g.availableMana p
    let playable := g.handObjects p ++ g.exiledPlayable p
    let canPlayLand :=
      g.canPlayLand p && playable.any (fun o => o.printed.isLand)
    let canCast := playable.any (fun o =>
      g.canCast p o &&
        available.canPay o.printed.manaCost
          (allowElfRestricted := o.hasSubtype "Elf") &&
        match o.printed.additionalCostOrPayGeneric with
        | none => true
        | some n =>
          !(g.sacrificeCreatureOrArtifactChoices p o.id).isEmpty ||
            available.canPay (o.printed.manaCost.addGeneric n)
              (allowElfRestricted := o.hasSubtype "Elf"))
    let canCastAdventure := playable.any (fun o =>
      g.canCastAdventure p o &&
        match o.printed.adventure with
        | some adv => available.canPay adv.manaCost
        | none => false)
    let canActivate := g.objects.any (fun o =>
      (g.activatedAbilitiesOf o).any (fun ab =>
        g.canActivate p o ab &&
          (g.availableManaExcept p (if ab.cost.tap then some o.id else none)).canPay
            ab.cost.mana (allowElfRestricted := o.hasSubtype "Elf")))
    canPlayLand || !(g.manaSources p).isEmpty || canCast || canCastAdventure || canActivate

/-- Whether bit `i` of `mask` is set. -/
def maskBit (mask i : Nat) : Bool :=
  ((mask >>> i) &&& 1) == 1

/-- Elements of `xs` whose index bit is set in `mask`. -/
def subsetFromMask {α : Type} (xs : Array α) (mask : Nat) : Array α :=
  Id.run do
    let mut acc : Array α := #[]
    for i in [0:xs.size] do
      if maskBit mask i then
        match xs[i]? with
        | some x => acc := acc.push x
        | none => pure ()
    return acc

/-- True when every source in `a` also appears (by id) in `b`. -/
def payingSourceSubset (a b : Array (GameObject × Array ManaType)) : Bool :=
  a.all (fun (oa, _) => b.any (fun (ob, _) => oa.id == ob.id))

/-- Pool after tapping `src` for `t`, including spending restrictions. -/
def poolAfterTap (g : Game) (pool : ManaPool) (src : GameObject) (t : ManaType) :
    ManaPool :=
  pool.add t (g.manaFromTap src t)
    (elfRestricted := src.printed.tapAddAnyColorEqualToPower)
    (instRestricted := src.printed.tapAddAnyColorForInstantOrSorcery)

/-- Whether tapping every source in `sources` can pay `cost` for some
type assignment. -/
def canPayTappingAll (g : Game) (pool : ManaPool) (cost : ManaCost)
    (allowElf allowInst : Bool) : List (GameObject × Array ManaType) → Bool
  | [] => pool.canPay cost allowElf allowInst
  | (src, types) :: rest =>
    types.any (fun t =>
      canPayTappingAll g (poolAfterTap g pool src t) cost allowElf allowInst rest)

/-- Unique source set that can pay when there are too many sources to
enumerate every subset. Recognizes a single sufficient source, or that
every source is required. -/
def uniquePayingSourceSetLarge (g : Game) (pool : ManaPool) (cost : ManaCost)
    (allowElf allowInst : Bool) (sources : Array (GameObject × Array ManaType)) :
    Option (Array (GameObject × Array ManaType)) :=
  Id.run do
    let mut singles : Array (GameObject × Array ManaType) := #[]
    for src in sources do
      if canPayTappingAll g pool cost allowElf allowInst [src] then
        singles := singles.push src
    if singles.size == 1 then
      return some singles
    if singles.size > 1 then
      return none
    if !canPayTappingAll g pool cost allowElf allowInst sources.toList then
      return none
    for i in [0:sources.size] do
      let rest := sources.extract 0 i ++ sources.extract (i + 1) sources.size
      if canPayTappingAll g pool cost allowElf allowInst rest.toList then
        return none
    return some sources

/-- The unique inclusion-minimal set of sources that can pay `cost`, if any. -/
def uniquePayingSourceSet (g : Game) (pool : ManaPool) (cost : ManaCost)
    (allowElf allowInst : Bool) (sources : Array (GameObject × Array ManaType)) :
    Option (Array (GameObject × Array ManaType)) :=
  let n := sources.size
  if n > 20 then
    uniquePayingSourceSetLarge g pool cost allowElf allowInst sources
  else
    let limit := 1 <<< n
    Id.run do
      let mut best : Option (Array (GameObject × Array ManaType)) := none
      for mask in [1:limit] do
        let sub := subsetFromMask sources mask
        if canPayTappingAll g pool cost allowElf allowInst sub.toList then
          match best with
          | none => best := some sub
          | some prev =>
            if payingSourceSubset sub prev then
              best := some sub
            else if payingSourceSubset prev sub then
              pure ()
            else
              return none
      return best

/-- True when the locked-in mana cost has exactly one legal payment. -/
def hasUniqueManaPayment (g : Game) : Bool :=
  match g.pending, g.proposedSpell with
  | .activateManaAbilities p, some prop =>
    if !g.canPayLife p prop.payLife then false
    else if !g.sourceStillPayable prop then false
    else if prop.needsSacrificeOther &&
        (g.sacrificeCreatureOrArtifactChoices p
          (prop.sourceId.getD prop.spellId)).isEmpty then
      false
    else
      let pool := (g.player p).manaPool
      let allowElf := g.proposedAllowsElfRestricted prop
      let allowInst := g.proposedAllowsInstRestricted prop
      pool.canPay prop.cost allowElf allowInst ||
        (uniquePayingSourceSet g pool prop.cost allowElf allowInst
          (g.manaSourcesForProposed p prop)).isSome
  | _, _ => false

/-- `sacrifice <id>` when exactly one permanent can pay that cost. -/
def uniqueSacrificeCommand (g : Game) : Option String :=
  match g.pending with
  | .sacrificePermanent p sourceId =>
    let choices := g.sacrificeCreatureOrArtifactChoices p sourceId
    match choices[0]? with
    | some o => if choices.size == 1 then some s!"sacrifice {o.id}" else none
    | none => none
  | _ => none

/-- Automatically pay a cost only after scripted input is exhausted and
there is only one legal way to pay it. -/
def shouldAutoPay (g : Game) (pending : List String) : Bool :=
  pending.isEmpty && (hasUniqueManaPayment g || (uniqueSacrificeCommand g).isSome)

/-- Apply the unique payment via `autopay` or `sacrifice`, and the `--output`
lines that record it. -/
def autoPayStep? (g : Game) (pending : List String) :
    Option (Except String (Game × Array String)) :=
  if !shouldAutoPay g pending then none
  else
    match uniqueSacrificeCommand g with
    | some line =>
      let parts := line.splitOn " "
      some (applyInteractiveAsActor g (parts.headD "") (parts.drop 1) |>.map
        (fun g' => (g', #[line])))
    | none =>
      some (applyAutopayAsActor g [] |>.map (fun r => (r.game, r.commands)))

#guard shouldAutoPay Tests.targetedBolt []
#guard !shouldAutoPay Tests.targetedBolt ["pay"]
#guard !shouldAutoPay Tests.started []
#guard !shouldAutoPay Tests.proposedOgre []
#guard !shouldAutoPay Tests.paidHunter []
#guard shouldAutoPay Tests.tappedForBolt []
#guard shouldAutoPay Tests.proposedHunter []
#guard shouldAutoPay Tests.targetedClub []
#guard shouldAutoPay Tests.proposedBauble []
#guard
  let g := Tests.addUntappedLand Tests.targetedBolt Catalog.mountain
  !shouldAutoPay g []
#guard
  let g := Tests.addUntappedLand Tests.targetedBolt Catalog.forest
  shouldAutoPay g []
#guard shouldAutoPay Tests.paidClub []

#guard (autoPayStep? Tests.targetedBolt ["pay"]).isNone
#guard
  match autoPayStep? Tests.targetedBolt [], applyAutopay Tests.targetedBolt ⟨0⟩ [] with
  | some (.ok (g', cmds)), .ok r =>
    cmds == r.commands && g'.pending == .none &&
      cmds == #[tapCommand Tests.boltMountain.id (.colored .red), "pay"] &&
      g'.log.any (fun s => Tests.mentions s "casts Lightning Bolt")
  | _, _ => false
#guard
  match autoPayStep? Tests.paidClub [] with
  | some (.ok (g', cmds)) =>
    cmds == #[s!"sacrifice {(Tests.clubFodder Tests.paidClub).id}"] &&
      g'.pending == .none &&
      g'.log.any (fun s => Tests.mentions s "casts Improvised Club")
  | _ => false

/-- Automatically pass only after scripted input is exhausted and priority
offers no other legal game-state action. -/
def shouldAutoPass (g : Game) (pending : List String) : Bool :=
  pending.isEmpty &&
    match g.actor with
    | some p => g.hasPriority p && !hasGameStatePriorityAction g p
    | none => false

#guard shouldAutoPass Tests.started []
#guard !shouldAutoPass Tests.started ["pass"]
#guard !shouldAutoPass { Tests.started with step := .precombatMain } []
#guard !shouldAutoPass Tests.drawnHands []

/-- Automatically declare no attackers after scripted input is exhausted when
there are no creatures that can legally attack. -/
def shouldAutoNoAttack (g : Game) (pending : List String) : Bool :=
  pending.isEmpty && g.pending == .declareAttackers &&
    !(g.battlefield.any g.canAttack)

#guard
  let g := { Tests.readyToDeclareAttackers with
    objects := Tests.readyToDeclareAttackers.objects.map (fun o =>
      { o with status := { o.status with tapped := true } }) }
  shouldAutoNoAttack g []
#guard
  let g := { Tests.readyToDeclareAttackers with
    objects := Tests.readyToDeclareAttackers.objects.map (fun o =>
      { o with status := { o.status with tapped := true } }) }
  !shouldAutoNoAttack g ["noattack"]
#guard !shouldAutoNoAttack Tests.readyToDeclareAttackers []

/-- Whether the defending player has any legal non-empty blocker declaration.
An attacker that requires multiple blockers can be blocked only when enough
individually eligible creatures are available. -/
def hasLegalBlock (g : Game) : Bool :=
  g.battlefield.any (fun attacker =>
    attacker.status.attacking &&
      let eligible := g.battlefield.filter (fun blocker => g.canBlock blocker attacker) |>.size
      eligible >= max 1 (g.minBlockersRequired attacker))

/-- Automatically declare no blockers after scripted input is exhausted when
that is the only legal declaration. -/
def shouldAutoNoBlock (g : Game) (pending : List String) : Bool :=
  pending.isEmpty && g.pending == .declareBlockers && !hasLegalBlock g

#guard
  let g := { Tests.readyToDeclareBlockers with
    objects := Tests.readyToDeclareBlockers.objects.map (fun o =>
      if o.controlledBy ⟨1⟩ then
        { o with status := { o.status with tapped := true } }
      else o) }
  shouldAutoNoBlock g []
#guard
  let g := { Tests.readyToDeclareBlockers with
    objects := Tests.readyToDeclareBlockers.objects.map (fun o =>
      if o.controlledBy ⟨1⟩ then
        { o with status := { o.status with tapped := true } }
      else o) }
  !shouldAutoNoBlock g ["noblock"]
#guard !shouldAutoNoBlock Tests.readyToDeclareBlockers []
#guard shouldAutoNoBlock Tests.gollumVsOneBearReadyToBlock []

/-- The unique legal target while announcing targets (CR 601.2c / 603.3d). -/
def soleLegalTarget? (g : Game) : Option Target :=
  match g.actor with
  | none => none
  | some p =>
    match g.pending with
    | .chooseTargets _ =>
      match g.objectAwaitingTargets with
      | none => none
      | some obj =>
        let legal := g.legalProposedTargets p obj
        if legal.size == 1 then legal[0]? else none
    | _ => none

/-- Token for a `target` command so `--output` can replay the announcement. -/
def targetCommandArg (g : Game) (p : PlayerId) : Target → String
  | .player pid =>
    if pid == g.opponent p then "opponent" else (g.player pid).name
  | .permanent id | .card id => toString id

/-- Accepted `target` line written for an automatically chosen target. -/
def targetCommand (g : Game) (p : PlayerId) (t : Target) : String :=
  s!"target {targetCommandArg g p t}"

/-- Automatically announce the only legal target after scripted input is
exhausted. -/
def shouldAutoTarget (g : Game) (pending : List String) : Bool :=
  pending.isEmpty && (soleLegalTarget? g).isSome

#guard shouldAutoTarget Tests.proposedSmite []
#guard !shouldAutoTarget Tests.proposedSmite ["target opponent"]
#guard !shouldAutoTarget Tests.proposedBolt []
#guard !shouldAutoTarget Tests.proposedPassage []
#guard !shouldAutoTarget Tests.started []
#guard shouldAutoTarget Tests.proposedEquip []
#guard shouldAutoTarget Tests.hospitalityLandPlayed []
#guard shouldAutoTarget Tests.galionAttackDeclared []
#guard !shouldAutoTarget Tests.galionAloneDeclared []
#guard targetCommand Tests.proposedBolt ⟨0⟩ (Target.player ⟨1⟩) == "target opponent"
#guard targetCommand Tests.proposedBolt ⟨0⟩ (Target.player ⟨0⟩) == "target Chandra"
#guard
  let tid := (Tests.namedPermanent Tests.proposedSmite "Grizzly Bears").id
  soleLegalTarget? Tests.proposedSmite == some (Target.permanent tid) &&
    targetCommand Tests.proposedSmite ⟨0⟩ (Target.permanent tid) == s!"target {tid}"
#guard
  match applyTarget Tests.proposedSmite ⟨0⟩
      [targetCommandArg Tests.proposedSmite ⟨0⟩
        (Target.permanent (Tests.namedPermanent Tests.proposedSmite "Grizzly Bears").id)] with
  | .ok g' =>
    g'.stack.back!.targets ==
      #[Target.permanent (Tests.namedPermanent Tests.proposedSmite "Grizzly Bears").id]
  | .error _ => false

/-- Apply the unique legal target and the `--output` line that records it. -/
def autoTargetStep? (g : Game) (pending : List String) :
    Option (Except String (Game × String)) :=
  if !shouldAutoTarget g pending then none
  else
    match g.actor, soleLegalTarget? g with
    | some p, some t =>
      some (g.apply p (.target t) |>.map (fun g' => (g', targetCommand g p t)))
    | _, _ => some (.error "no actor or unique legal target")

#guard (autoTargetStep? Tests.proposedBolt []).isNone
#guard (autoTargetStep? Tests.proposedSmite ["target opponent"]).isNone
#guard
  let tid := (Tests.namedPermanent Tests.proposedSmite "Grizzly Bears").id
  match autoTargetStep? Tests.proposedSmite [] with
  | some (.ok (g', cmd)) =>
    cmd == s!"target {tid}" &&
      g'.stack.back!.targets == #[Target.permanent tid] &&
      g'.log.any (fun s => Tests.mentions s "chooses Grizzly Bears as a target (CR 601.2c)")
  | _ => false
#guard
  let tid := (Tests.namedPermanent Tests.hospitalityLandPlayed "Grizzly Bears").id
  match autoTargetStep? Tests.hospitalityLandPlayed [] with
  | some (.ok (g', cmd)) =>
    cmd == s!"target {tid}" &&
      g'.stack.back!.targets == #[Target.permanent tid]
  | _ => false
#guard
  let tid := (Tests.namedPermanent Tests.proposedSmite "Grizzly Bears").id
  match autoTargetStep? Tests.proposedSmite [] with
  | some (.ok (_, cmd)) =>
    let parts := cmd.splitOn " "
    match applyInteractiveAsActor Tests.proposedSmite (parts.headD "") (parts.drop 1) with
    | .ok g' => g'.stack.back!.targets == #[Target.permanent tid]
    | .error _ => false
  | _ => false

/-- CR 103.1: the deciding player chooses who takes the first turn. Returns
the seat index and remaining `--input` lines, or `none` if the user quits.
The chooser announcement is printed first by `printFirstChooser`. -/
partial def chooseStartingPlayer (seats : Array Seat) (decider : Nat)
    (controlAll : Bool) (pending : List String)
    (output : Option IO.FS.Handle) (sameFile : Bool := false) :
    IO (Option (Nat × List String)) := do
  let mut pending := pending
  let mut chosen : Option Nat := none
  let prompt :=
    if controlAll then
      s!"mtg ({seats[decider]!.name})> "
    else
      "mtg> "
  while chosen.isNone do
    IO.print prompt
    (← IO.getStdout).flush
    let (line, rest, fromInput) ← nextSessionCommand pending
    pending := rest
    if line.isEmpty then
      continue
    let parts := line.splitOn " "
    let cmd := parts.headD ""
    match cmd with
    | "quit" | "exit" =>
      IO.println "Goodbye."
      return none
    | "help" =>
      IO.println helpChooseFirst
    | "first" =>
      match parseFirstPlayer seats (parts.drop 1) with
      | .error e => IO.println s!"! {e}"
      | .ok idx =>
        recordAcceptedCommand output sameFile fromInput line
        chosen := some idx
    | _ =>
      IO.println "! Choose who takes the first turn (CR 103.1): first <name>"
  match chosen with
  | some idx => return some (idx, pending)
  | none => return none

partial def interactiveLoop (g : Game) (startVisible : Bool := false)
    (controlAll : Bool := false) (pending : List String := [])
    (output : Option IO.FS.Handle := none) (sameFile : Bool := false) :
    IO Unit := do
  let mut g := g
  let mut seen := g.log.size
  let mut playerView := startVisible
  let mut lastActor : Option PlayerId := g.actor
  let mut pending := pending
  let you : PlayerId := ⟨0⟩
  let youName := (g.player you).name
  IO.println (helpInteractive controlAll youName)
  while !g.over do
    -- Interactive: let the heuristic play every other seat until you must act.
    if !controlAll then
      while !g.over && (match g.actor with | some p => p != you | none => false) do
        let actorName :=
          match g.actor with
          | some p => (g.player p).name
          | none => "Agent"
        match Agent.step g with
        | .error e =>
          IO.println s!"{actorName} could not act: {e}"
          break
        | .ok g' =>
          seen ← refreshAfterStep g g' seen (humanView playerView)
          g := g'
    if g.over then break
    if controlAll && g.actor != lastActor then
      match g.actor with
      | some p =>
        IO.println s!"{g.player p |>.name} to act."
        if playerView then
          printState g (some p)
      | none => pure ()
      lastActor := g.actor
    if let some step := autoTargetStep? g pending then
      match step with
      | .error e =>
        let who := match g.actor with | some p => (g.player p).name | none => "Player"
        IO.println s!"{who} could not automatically target: {e}"
      | .ok (g', line) =>
        recordAcceptedCommand output sameFile false line
        seen ← refreshAfterStep g g' seen (currentView g' playerView controlAll)
        g := g'
      continue
    if let some step := autoPayStep? g pending then
      match step with
      | .error e =>
        let who := match g.actor with | some p => (g.player p).name | none => "Player"
        IO.println s!"{who} could not automatically pay: {e}"
      | .ok (g', cmds) =>
        for line in cmds do
          recordAcceptedCommand output sameFile false line
        seen ← refreshAfterStep g g' seen (currentView g' playerView controlAll)
        g := g'
      continue
    if shouldAutoNoAttack g pending then
      let some p := g.actor | continue
      match g.apply p (.declareAttackers #[]) with
      | .error e =>
        IO.println s!"{(g.player p).name} could not automatically declare no attackers: {e}"
      | .ok g' =>
        recordAcceptedCommand output sameFile false "noattack"
        seen ← refreshAfterStep g g' seen (currentView g' playerView controlAll)
        g := g'
      continue
    if shouldAutoNoBlock g pending then
      let some p := g.actor | continue
      match g.apply p (.declareBlockers #[]) with
      | .error e =>
        IO.println s!"{(g.player p).name} could not automatically declare no blockers: {e}"
      | .ok g' =>
        recordAcceptedCommand output sameFile false "noblock"
        seen ← refreshAfterStep g g' seen (currentView g' playerView controlAll)
        g := g'
      continue
    if shouldAutoPass g pending then
      let some p := g.actor | continue
      match g.apply p .pass with
      | .error e =>
        IO.println s!"{(g.player p).name} could not automatically pass: {e}"
      | .ok g' =>
        recordAcceptedCommand output sameFile false "pass"
        seen ← refreshAfterStep g g' seen (currentView g' playerView controlAll)
        g := g'
      continue
    let prompt :=
      if controlAll then
        match g.actor with
        | some p => s!"mtg ({g.player p |>.name})> "
        | none => "mtg> "
      else
        "mtg> "
    IO.print prompt
    (← IO.getStdout).flush
    let (line, rest, fromInput) ← nextSessionCommand pending
    pending := rest
    if line.isEmpty then
      continue
    let parts := line.splitOn " "
    let cmd := parts.headD ""
    match cmd with
    | "quit" | "exit" =>
      IO.println "Goodbye."
      return
    | "help" => IO.println (helpInteractive controlAll youName)
    | "first" =>
      IO.println "! Starting player already chosen (CR 103.1)"
    | "state" => printState g (currentView g playerView controlAll)
    | "visible" =>
      match applyVisible (parts.drop 1) with
      | .error e => IO.println s!"! {e}"
      | .ok none =>
        match currentView g true controlAll with
        | some p => printState g (some p)
        | none => printState g (some you)
      | .ok (some on) =>
        playerView := on
        if on then
          let who :=
            match currentView g true controlAll with
            | some p => (g.player p).name
            | none => youName
          IO.println s!"Showing only information {who} can see."
          printState g (currentView g true controlAll)
        else
          IO.println "Showing full game information."
    | _ =>
      match applyLoggedAction g cmd (parts.drop 1) line with
      | .error e => IO.println s!"! {e}"
      | .ok (g', recorded) =>
        for rec in recorded do
          recordAcceptedCommand output sameFile fromInput rec
        seen ← refreshAfterStep g g' seen (currentView g' playerView controlAll)
        g := g'
        if g.over then
          printState g (currentView g playerView controlAll)
  match g.result with
  | some (.won p) => IO.println s!"Winner: {g.player p |>.name}"
  | some .draw => IO.println "The game is a draw."
  | none => pure ()

/-- Parse a Hobbit Welcome Deck color name or letter. -/
def parseWelcomeDeck (token : String) : Except String Color :=
  match token.map Char.toLower with
  | "w" | "white" => .ok .white
  | "u" | "blue" => .ok .blue
  | "b" | "black" => .ok .black
  | "r" | "red" => .ok .red
  | "g" | "green" => .ok .green
  | _ => .error s!"Unknown Welcome Deck: {token} (white, blue, black, red, or green)"

#guard
  match parseWelcomeDeck "white" with
  | .ok .white => true
  | _ => false

#guard
  match parseWelcomeDeck "U" with
  | .ok .blue => true
  | _ => false

#guard
  match parseWelcomeDeck "gold" with
  | .error msg => msg == "Unknown Welcome Deck: gold (white, blue, black, red, or green)"
  | .ok _ => false

structure DemoOptions where
  interactive : Bool
  multiplayer : Bool
  playerView : Bool
  seed : UInt64
  fuel : Nat
  inputFile : Option String
  outputFile : Option String
  players : Array DemoPlayer
  /-- Seat who chooses who takes the first turn (CR 103.1). `none` is random. -/
  decides : Option Nat

/-- Raw flag values before player-name validation. `seed` / `fuel` are `none`
until those flags appear, so input-file flags can fill the defaults. -/
structure DemoFlagValues where
  interactive : Bool
  multiplayer : Bool
  playerView : Bool
  seed : Option UInt64
  fuel : Option Nat
  inputFile : Option String
  outputFile : Option String
  names : Array String
  decks : Array Color
  decidesName : Option String
  /-- True when `--auto`, `--interactive`, or `--multiplayer` was given. -/
  modeSet : Bool

/-- Parse flag tokens without checking that `--input` / `--visible` have a mode. -/
def parseFlagList (args : List String) : Except String DemoFlagValues :=
  Id.run do
    let mut interactive := false
    let mut multiplayer := false
    let mut playerView := false
    let mut seed : Option UInt64 := none
    let mut fuel : Option Nat := none
    let mut inputFile : Option String := none
    let mut outputFile : Option String := none
    let mut names : Array String := #[]
    let mut decks : Array Color := #[]
    let mut decidesName : Option String := none
    let mut modeSet := false
    let mut rest := args
    while !rest.isEmpty do
      match rest with
      | "--" :: xs =>
        rest := xs
      | "--help" :: _ => return .error "help"
      | "--auto" :: xs =>
        interactive := false
        multiplayer := false
        modeSet := true
        rest := xs
      | "--interactive" :: xs =>
        interactive := true
        multiplayer := false
        modeSet := true
        rest := xs
      | "--multiplayer" :: xs =>
        interactive := true
        multiplayer := true
        modeSet := true
        rest := xs
      | "--visible" :: xs =>
        playerView := true
        rest := xs
      | "--decides" :: name :: xs =>
        if name.startsWith "--" then
          return .error "Missing player name for --decides"
        else
          decidesName := some name
          rest := xs
      | "--decides" :: [] => return .error "Missing player name for --decides"
      | "--input" :: path :: xs =>
        if path.startsWith "--" then
          return .error "Missing input file path"
        else
          inputFile := some path
          rest := xs
      | "--input" :: [] => return .error "Missing input file path"
      | "--output" :: path :: xs =>
        if path.startsWith "--" then
          return .error "Missing output file path"
        else
          outputFile := some path
          rest := xs
      | "--output" :: [] => return .error "Missing output file path"
      | "--seed" :: n :: xs =>
        match n.toNat? with
        | none => return .error s!"Bad seed: {n}"
        | some v =>
          seed := some (UInt64.ofNat v)
          rest := xs
      | "--fuel" :: n :: xs =>
        match n.toNat? with
        | none => return .error s!"Bad fuel: {n}"
        | some v =>
          fuel := some v
          rest := xs
      | "--name" :: name :: xs =>
        if name.startsWith "--" then
          return .error "Missing player name"
        else
          names := names.push name
          rest := xs
      | "--name" :: [] => return .error "Missing player name"
      | "--deck" :: color :: xs =>
        if color.startsWith "--" then
          return .error "Missing Welcome Deck color"
        else
          match parseWelcomeDeck color with
          | .error e => return .error e
          | .ok c =>
            decks := decks.push c
            rest := xs
      | "--deck" :: [] => return .error "Missing Welcome Deck color"
      | x :: _ => return .error s!"Unknown argument: {x}"
      | [] => break
    return .ok {
      interactive := interactive
      multiplayer := multiplayer
      playerView := playerView
      seed := seed
      fuel := fuel
      inputFile := inputFile
      outputFile := outputFile
      names := names
      decks := decks
      decidesName := decidesName
      modeSet := modeSet
    }

/-- Merge CLI flags with additional flags from `--input`. File flags override
mode, seed, fuel, players, and `--decides` when present. `--visible` is
enabled if either side sets it. `--input` / `--output` stay on the CLI. -/
def mergeFlagValues (cli file : DemoFlagValues) : DemoFlagValues :=
  {
    interactive := if file.modeSet then file.interactive else cli.interactive
    multiplayer := if file.modeSet then file.multiplayer else cli.multiplayer
    playerView := cli.playerView || file.playerView
    seed :=
      match file.seed with
      | some s => some s
      | none => cli.seed
    fuel :=
      match file.fuel with
      | some n => some n
      | none => cli.fuel
    inputFile := cli.inputFile
    outputFile := cli.outputFile
    names := if file.names.isEmpty then cli.names else file.names
    decks := if file.decks.isEmpty then cli.decks else file.decks
    decidesName :=
      match file.decidesName with
      | some n => some n
      | none => cli.decidesName
    modeSet := file.modeSet || cli.modeSet
  }

/-- Apply defaults and reject illegal flag combinations. -/
def finishOptions (v : DemoFlagValues) : Except String DemoOptions :=
  if v.playerView && !v.interactive then
    .error "--visible requires --interactive or --multiplayer"
  else if v.inputFile.isSome && !v.interactive then
    .error "--input requires --interactive or --multiplayer"
  else if v.outputFile.isSome && !v.interactive then
    .error "--output requires --interactive or --multiplayer"
  else
    match playersFromFlags v.names v.decks with
    | .error e => .error e
    | .ok players =>
      let seed := v.seed.getD 20260807
      let fuel := v.fuel.getD 800
      match v.decidesName with
      | none =>
        .ok {
          interactive := v.interactive
          multiplayer := v.multiplayer
          playerView := v.playerView
          seed := seed
          fuel := fuel
          inputFile := v.inputFile
          outputFile := v.outputFile
          players := players
          decides := none
        }
      | some name =>
        match parsePlayerName (seatsFromPlayers players) name with
        | .error e => .error e
        | .ok i =>
          .ok {
            interactive := v.interactive
            multiplayer := v.multiplayer
            playerView := v.playerView
            seed := seed
            fuel := fuel
            inputFile := v.inputFile
            outputFile := v.outputFile
            players := players
            decides := some i
          }

def parseArgs (args : List String) : Except String DemoOptions :=
  match parseFlagList args with
  | .error e => .error e
  | .ok v => finishOptions v

/-- Parse the command line together with additional flags from `--input`. -/
def parseArgsWithFlags (args flagLines : List String) : Except String DemoOptions :=
  match parseFlagList args with
  | .error e => .error e
  | .ok cli =>
    match parseFlagList (flagTokens flagLines) with
    | .error e => .error e
    | .ok file => finishOptions (mergeFlagValues cli file)

#guard
  match parseArgs ["--interactive", "--visible"] with
  | .ok opt => opt.interactive && !opt.multiplayer && opt.playerView
  | _ => false

#guard
  match parseArgs ["--interactive"] with
  | .ok opt => opt.interactive && !opt.multiplayer && !opt.playerView
  | _ => false

#guard
  match parseArgs ["--multiplayer"] with
  | .ok opt => opt.interactive && opt.multiplayer && !opt.playerView
  | _ => false

#guard
  match parseArgs ["--multiplayer", "--visible"] with
  | .ok opt => opt.interactive && opt.multiplayer && opt.playerView
  | _ => false

#guard
  match parseArgs ["--interactive", "--multiplayer"] with
  | .ok opt => opt.interactive && opt.multiplayer
  | _ => false

#guard
  match parseArgs ["--multiplayer", "--interactive"] with
  | .ok opt => opt.interactive && !opt.multiplayer
  | _ => false

#guard
  match parseArgs ["--visible"] with
  | .error msg => msg == "--visible requires --interactive or --multiplayer"
  | .ok _ => false

#guard
  match parseArgs ["--interactive"] with
  | .ok opt => opt.inputFile.isNone
  | _ => false

#guard
  match parseArgs ["--interactive", "--input", "opening.txt"] with
  | .ok opt => opt.interactive && !opt.multiplayer && opt.inputFile == some "opening.txt"
  | _ => false

#guard
  match parseArgs ["--multiplayer", "--input", "opening.txt"] with
  | .ok opt => opt.interactive && opt.multiplayer && opt.inputFile == some "opening.txt"
  | _ => false

#guard
  match parseArgs ["--input", "opening.txt"] with
  | .error msg => msg == "--input requires --interactive or --multiplayer"
  | .ok _ => false

#guard
  match parseArgs ["--auto", "--input", "opening.txt"] with
  | .error msg => msg == "--input requires --interactive or --multiplayer"
  | .ok _ => false

#guard
  match parseArgs ["--interactive", "--input"] with
  | .error msg => msg == "Missing input file path"
  | .ok _ => false

#guard
  match parseArgs ["--interactive", "--input", "--visible"] with
  | .error msg => msg == "Missing input file path"
  | .ok _ => false

#guard
  match parseArgs ["--interactive"] with
  | .ok opt => opt.outputFile.isNone
  | _ => false

#guard
  match parseArgs ["--interactive", "--output", "session.txt"] with
  | .ok opt => opt.interactive && !opt.multiplayer && opt.outputFile == some "session.txt"
  | _ => false

#guard
  match parseArgs ["--multiplayer", "--output", "session.txt"] with
  | .ok opt => opt.interactive && opt.multiplayer && opt.outputFile == some "session.txt"
  | _ => false

#guard
  match parseArgs ["--interactive", "--input", "opening.txt", "--output", "session.txt"] with
  | .ok opt => opt.inputFile == some "opening.txt" && opt.outputFile == some "session.txt"
  | _ => false

#guard
  match parseArgs ["--interactive", "--input", "session.txt", "--output", "session.txt"] with
  | .ok opt =>
    opt.inputFile == some "session.txt" && opt.outputFile == some "session.txt" &&
    sameInputOutput opt.inputFile opt.outputFile
  | _ => false

#guard
  match parseArgs ["--multiplayer", "--input", "session.txt", "--output", "session.txt"] with
  | .ok opt =>
    opt.interactive && opt.multiplayer &&
    sameInputOutput opt.inputFile opt.outputFile
  | _ => false

#guard
  match parseArgs ["--output", "session.txt"] with
  | .error msg => msg == "--output requires --interactive or --multiplayer"
  | .ok _ => false

#guard
  match parseArgs ["--auto", "--output", "session.txt"] with
  | .error msg => msg == "--output requires --interactive or --multiplayer"
  | .ok _ => false

#guard
  match parseArgs ["--interactive", "--output"] with
  | .error msg => msg == "Missing output file path"
  | .ok _ => false

#guard
  match parseArgs ["--interactive", "--output", "--visible"] with
  | .error msg => msg == "Missing output file path"
  | .ok _ => false

#guard
  match parseArgs [] with
  | .ok opt => opt.players == defaultDemoPlayers && opt.decides.isNone
  | _ => false

#guard
  match parseArgs [
      "--name", "Elspeth", "--deck", "white",
      "--name", "Jace", "--deck", "blue"] with
  | .ok opt => opt.players == elspethJace
  | _ => false

#guard
  match parseArgs [
      "--name", "Elspeth", "--name", "Jace", "--name", "Liliana",
      "--deck", "W", "--deck", "U", "--deck", "B"] with
  | .ok opt => opt.players == elspethJaceLiliana
  | _ => false

#guard
  match parseArgs ["--name", "Nissa", "--deck", "green", "--name", "Chandra", "--deck", "r"] with
  | .ok opt =>
    opt.players.size == 2 &&
    opt.players[0]!.name == "Nissa" && opt.players[0]!.color == .green &&
    opt.players[1]!.name == "Chandra" && opt.players[1]!.color == .red
  | _ => false

#guard
  match parseArgs ["--auto", "--name", "Liliana", "--deck", "black",
      "--name", "Nissa", "--deck", "green"] with
  | .ok opt =>
    !opt.interactive &&
    opt.players[0]!.name == "Liliana" && opt.players[0]!.color == .black &&
    opt.players[1]!.name == "Nissa" && opt.players[1]!.color == .green
  | _ => false

#guard
  match parseArgs ["--interactive", "--name", "Elspeth", "--deck", "W",
      "--name", "Chandra", "--deck", "r"] with
  | .ok opt =>
    opt.interactive &&
    opt.players[0]!.name == "Elspeth" && opt.players[0]!.color == .white &&
    opt.players[1]!.name == "Chandra" && opt.players[1]!.color == .red
  | _ => false

#guard
  match parseArgs ["--deck", "gold", "--name", "Elspeth", "--name", "Jace", "--deck", "blue"] with
  | .error msg => msg == "Unknown Welcome Deck: gold (white, blue, black, red, or green)"
  | .ok _ => false

#guard
  match parseArgs ["--name"] with
  | .error msg => msg == "Missing player name"
  | .ok _ => false

#guard
  match parseArgs ["--deck"] with
  | .error msg => msg == "Missing Welcome Deck color"
  | .ok _ => false

#guard
  match parseArgs ["--name", "--interactive"] with
  | .error msg => msg == "Missing player name"
  | .ok _ => false

#guard
  match parseArgs ["--deck", "--seed", "1"] with
  | .error msg => msg == "Missing Welcome Deck color"
  | .ok _ => false

#guard
  match parseArgs ["--name", "Elspeth", "--deck", "white"] with
  | .error msg => msg == "A game needs at least two players (CR 100.1)"
  | .ok _ => false

#guard
  match parseArgs ["--name", "Elspeth", "--name", "Jace", "--deck", "white"] with
  | .error msg =>
    msg == "--name and --deck must be given the same number of times (got 2 names and 1 decks)"
  | .ok _ => false

#guard
  match parseArgs ["--name", "Jace", "--deck", "blue", "--name", "jace", "--deck", "white"] with
  | .error msg => msg == "Duplicate player name: Jace"
  | .ok _ => false

#guard
  match parseArgs ["--chandra", "white"] with
  | .error msg => msg == "Unknown argument: --chandra"
  | .ok _ => false

#guard
  match parseArgs ["--decides", "Nissa"] with
  | .ok opt => !opt.interactive && opt.decides == some 1 && opt.players == defaultDemoPlayers
  | _ => false

#guard
  match parseArgs ["--decides", "chandra"] with
  | .ok opt => opt.decides == some 0
  | _ => false

#guard
  match parseArgs ["--interactive", "--decides", "Nissa"] with
  | .ok opt => opt.interactive && !opt.multiplayer && opt.decides == some 1
  | _ => false

#guard
  match parseArgs ["--multiplayer", "--decides", "Chandra"] with
  | .ok opt => opt.interactive && opt.multiplayer && opt.decides == some 0
  | _ => false

#guard
  match parseArgs [
      "--name", "Elspeth", "--deck", "white",
      "--name", "Jace", "--deck", "blue",
      "--decides", "Jace"] with
  | .ok opt => opt.players == elspethJace && opt.decides == some 1
  | _ => false

#guard
  match parseArgs [
      "--decides", "Liliana",
      "--name", "Elspeth", "--name", "Jace", "--name", "Liliana",
      "--deck", "W", "--deck", "U", "--deck", "B"] with
  | .ok opt => opt.players == elspethJaceLiliana && opt.decides == some 2
  | _ => false

#guard
  match parseArgs ["--decides", "Frodo"] with
  | .error msg => msg == "No player named Frodo"
  | .ok _ => false

#guard
  match parseArgs [
      "--name", "Elspeth", "--deck", "white",
      "--name", "Jace", "--deck", "blue",
      "--decides", "Nissa"] with
  | .error msg => msg == "No player named Nissa"
  | .ok _ => false

#guard
  match parseArgs ["--decides"] with
  | .error msg => msg == "Missing player name for --decides"
  | .ok _ => false

#guard
  match parseArgs ["--decides", "--seed", "1"] with
  | .error msg => msg == "Missing player name for --decides"
  | .ok _ => false

#guard
  match parseArgsWithFlags ["--interactive", "--input", "opening.txt"] [] with
  | .ok opt => opt.interactive && opt.inputFile == some "opening.txt" && !opt.playerView
  | _ => false

#guard
  match parseArgsWithFlags
      ["--interactive", "--input", "opening.txt"] ["--visible"] with
  | .ok opt => opt.interactive && opt.playerView && opt.inputFile == some "opening.txt"
  | _ => false

#guard
  match parseArgsWithFlags
      ["--interactive", "--input", "opening.txt"] ["--seed 42"] with
  | .ok opt => opt.seed == 42 && opt.interactive
  | _ => false

#guard
  match parseArgsWithFlags
      ["--interactive", "--seed", "99", "--input", "opening.txt"] ["--seed 42"] with
  | .ok opt => opt.seed == 42
  | _ => false

#guard
  match parseArgsWithFlags
      ["--interactive", "--input", "opening.txt"] ["--fuel 12"] with
  | .ok opt => opt.fuel == 12
  | _ => false

#guard
  match parseArgsWithFlags ["--input", "opening.txt"] ["--interactive"] with
  | .ok opt => opt.interactive && !opt.multiplayer && opt.inputFile == some "opening.txt"
  | _ => false

#guard
  match parseArgsWithFlags
      ["--interactive", "--input", "opening.txt"] ["--multiplayer"] with
  | .ok opt => opt.interactive && opt.multiplayer
  | _ => false

#guard
  match parseArgsWithFlags ["--input", "opening.txt"] [] with
  | .error msg => msg == "--input requires --interactive or --multiplayer"
  | .ok _ => false

#guard
  match parseArgsWithFlags
      ["--interactive", "--input", "a.txt", "--output", "b.txt"]
      ["--output c.txt", "--input d.txt", "--visible"] with
  | .ok opt =>
    opt.inputFile == some "a.txt" && opt.outputFile == some "b.txt" && opt.playerView
  | _ => false

#guard
  match parseArgsWithFlags
      ["--interactive", "--input", "opening.txt"]
      ["--name Elspeth --deck white", "--name Jace --deck blue"] with
  | .ok opt => opt.players == elspethJace
  | _ => false

#guard
  match parseArgsWithFlags
      ["--interactive", "--name", "Chandra", "--deck", "red",
        "--name", "Nissa", "--deck", "green", "--input", "opening.txt"]
      ["--name Elspeth --deck white", "--name Jace --deck blue"] with
  | .ok opt => opt.players == elspethJace
  | _ => false

#guard
  match parseArgsWithFlags
      ["--interactive", "--input", "opening.txt"] ["--decides Nissa"] with
  | .ok opt => opt.decides == some 1
  | _ => false

#guard
  match parseArgsWithFlags ["--interactive"] ["--chandra"] with
  | .error msg => msg == "Unknown argument: --chandra"
  | .ok _ => false

def printUsageError (e : String) : IO UInt32 := do
  if e == "help" then
    IO.println usage
    return 0
  else
    IO.eprintln e
    IO.println usage
    return 1

def main (args : List String) : IO UInt32 := do
  match parseFlagList args with
  | .error e =>
    printUsageError e
  | .ok cli =>
    match (← loadInputScript cli.inputFile) with
    | .error e =>
      IO.eprintln e
      return 1
    | .ok script =>
      match parseArgsWithFlags args script.flags with
      | .error e =>
        printUsageError e
      | .ok opt =>
        let pending := script.commands
        let sameFile := sameInputOutput opt.inputFile opt.outputFile
        match (← openOutputFile opt.outputFile sameFile) with
        | .error e =>
          IO.eprintln e
          return 1
        | .ok output =>
          recordInputFlags output sameFile script.flags
          printEngineBanner
          printDeckAssignments opt.players
          let decider := assignDecider opt.players opt.seed opt.decides
          let humanChooses := humanChoosesFirst opt.interactive opt.multiplayer decider
          printFirstChooser opt.players decider opt.decides.isNone (!humanChooses)
          if opt.interactive then
            match (←
              if humanChooses then
                chooseStartingPlayer (seatsFromPlayers opt.players) decider
                  opt.multiplayer pending output sameFile
              else
                pure (some (decider, pending))) with
            | none => return 0
            | some (startIdx, pending) =>
              let g ← startGame opt.seed (some startIdx) opt.players
              printOpening g (currentView g opt.playerView opt.multiplayer)
              interactiveLoop g opt.playerView opt.multiplayer pending output sameFile
              return 0
          else
            let g ← startDemo opt.seed (some decider) (players := opt.players)
            runAuto g opt.fuel
            return 0
