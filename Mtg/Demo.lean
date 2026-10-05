import Mtg.Engine.Agent
import Mtg.Engine.Catalog
import Mtg.Engine.Game
import Mtg.Engine.Rules
import Mtg.Demo.DeckList
import Mtg.Demo.Render
import Mtg.Demo.WelcomeDecks

/-!
# Mtg.Demo

Console demonstration of `Mtg.Engine`. Default mode runs a scripted game with a
heuristic agent using The Hobbit Welcome Decks. Repeat `--name NAME` and
`--deck COLOR` or `--deck FILE` once per player (paired in order; default
Chandra red and Nissa green). COLOR is a Welcome Deck; FILE is a text deck
list whose card names are in the supported catalog. Pass `--interactive` to
play as the first named player against
heuristic-controlled opponents, or `--multiplayer` to issue every player's
actions from the console. `--decides NAME` names the player who chooses who
takes the first turn (CR 103.1); by default one player is chosen at random
using `--seed`. In interactive modes that player uses `first <name>` before
opening hands are drawn, unless a heuristic opponent is deciding and chooses
to go first. `visible` prints only information that player can see; `--visible`
starts in that view. `--norandom` stops the engine from shuffling or
rolling; the demo asks for each random result (`shuffle`, `order`, `pick`,
`random`, `flip`). `--constructed` treats the game as constructed play
(CR 100.2a); otherwise it is limited play (CR 100.2b). `--input FILE` runs
commands from the file first, then
reads from the console. Lines that start with `--` are additional flags
instead of commands; when `--output` is a different file those flags are
written first. `--output FILE` writes accepted game-state commands
(from the file or the console) to that file. Incorrect commands and session
commands such as `state` and `quit` are omitted. When `--input` and
`--output` are the same file, those flags and commands are replayed and new
accepted console commands are appended. `autopay` is recorded as the individual
`tap` and `pay` commands it performs. `your turn`, `my turn`, `main phase`,
and `attack step` keep passing until the named step (or until a player must
take a non-pass action). Those shortcuts and `ignore` only pass for the
player who issued them; other players may still act. Other players'
pass-until shortcuts (recorded as `pass` sequences) do not interrupt those
commands. `ignore` keeps passing until your next main phase and is not
interrupted at all. Those shortcuts are recorded as the individual `pass`
commands they perform. `your turn`, `my turn`, `main phase`, and `ignore`
use `noattack` when declaring attackers; `noblock` is used when that is the
only legal declaration. `attach <id>` attaches an Equipment
you control when a spell asks you to. After scripted input is exhausted, a
cost with only one legal payment is paid automatically (`tap`, `pay`,
`sacrifice`) and a unique legal target is announced automatically as a
`target` command. `--check` replays `--input FILE` without reading the
console and exits successfully only when every command is legal and the
game ends (a winner or a draw).
-/

open Mtg.Engine
open Mtg.Engine.Catalog
open Mtg.Engine.Game
open Mtg.Demo
open Mtg.Demo.Render

def usage : String :=
  "Mtg.Demo — demonstration of the Mtg.Engine rules engine

Usage:
  lake exe mtg-demo [--auto | --interactive | --multiplayer] [--visible]
                    [--norandom] [--constructed] [--decides NAME]
                    [--input FILE] [--output FILE] [--check] [--seed N] [--fuel N]
                    [--name NAME --deck COLOR|FILE]...

Options:
  --auto          Run a heuristic game (default)
  --interactive   Play as the first named player; others are heuristic
  --multiplayer   Control every player from the console
  --visible       With --interactive or --multiplayer, hide information the
                  acting player cannot see
  --norandom      Never shuffle or roll; ask for each random result
  --constructed   Treat the game as constructed play (CR 100.2a); default
                  is limited play (CR 100.2b)
  --decides NAME  Player who chooses who takes the first turn (CR 103.1);
                  default is a random player using --seed (or a prompt
                  with --norandom)
  --input FILE    With --interactive, --multiplayer, or --norandom, run
                  these commands first, then read from the console. Lines
                  that start with -- are additional flags instead of commands
  --output FILE   With --interactive, --multiplayer, or --norandom, write
                  accepted game-state commands (from --input and from the console)
                  to this file. Flags from --input are written first when
                  this path is different from --input. Incorrect commands and session commands
                  such as state and quit are omitted.
                  The same path as --input replays that file and appends
                  new commands. Unique automatic cost payments are written
                  as tap, pay, and sacrifice commands. Pass-until shortcuts
                  (your turn, my turn, main phase, attack step, ignore) are written
                  as the individual pass commands they perform. your turn,
                  my turn, main phase, and ignore use noattack when declaring
                  attackers. your turn, my turn, main phase, attack step, and ignore
                  only pass for the player who issued them.
                  Other players' pass-until shortcuts do not interrupt a pending shortcut;
                  ignore is never interrupted
  --check         With --input FILE, replay those commands without reading
                  the console. Exit 0 only if every command is legal and
                  the game ends (a winner or a draw). Unused commands
                  after the game ends are an error
  --seed N        RNG seed (default 20260807); unused with --norandom
  --fuel N        Maximum heuristic actions (default 800)
  --name NAME     Player name (repeat once per player)
  --deck COLOR    That player's Hobbit Welcome Deck (repeat once per player)
  --deck FILE     Deck list of supported catalog cards (repeat once per player)
  --help          Show this help

COLOR is white, blue, black, red, or green (also W, U, B, R, G). FILE is a
text file of card names from the supported catalog (optional `N` or `Nx`
counts; `#` comments; `Sideboard` lines ignored). Repeat `--name` and
`--deck` the same number of times; they pair in order. Default is Chandra
(red) and Nissa (green). A game needs at least two players (CR 100.1).
Decklists:
https://magic.wizards.com/en/news/announcements/the-hobbit-welcome-decks

The engine follows the Magic: The Gathering Comprehensive Rules
effective 25 September 2026.

At the start of a game, one player is chosen to decide who takes the
first turn (CR 103.1). `--decides NAME` names that player; the default
is a random player chosen using --seed. `--norandom` asks who was
chosen instead of rolling. `--constructed` validates decks as
constructed play (CR 100.2a); the default is limited play (CR 100.2b).
In --interactive, the first
named player chooses with `first <name>` when they are deciding; a
heuristic opponent otherwise chooses to go first. In --multiplayer,
the deciding player chooses with `first <name>`. In --auto, the
deciding player (heuristic) chooses to go first.
"

/-- A Welcome Deck color or a path to a text deck list. -/
inductive DemoDeck where
  | welcome (color : Color)
  | file (path : String)
deriving Repr, Inhabited, DecidableEq

/-- A named player and the deck they sit with. -/
structure DemoPlayer where
  name : String
  deck : DemoDeck
deriving Repr, Inhabited, DecidableEq

/-- Default table: Chandra (red) and Nissa (green). -/
def defaultDemoPlayers : Array DemoPlayer := #[
  { name := "Chandra", deck := .welcome .red },
  { name := "Nissa", deck := .welcome .green }
]

/-- Cards for a Welcome Deck. File decks are empty until `loadSeats`. -/
def cardsFor (d : DemoDeck) : Array CardDef :=
  match d with
  | .welcome c => hobbitDeck c
  | .file _ => #[]

/-- Seat list from named players. File decks resolve later via `loadSeats`. -/
def seatsFromPlayers (players : Array DemoPlayer) : Array Seat :=
  players.map (fun p => { name := p.name, deck := cardsFor p.deck })

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
def playersFromFlags (names : Array String) (decks : Array DemoDeck) :
    Except String (Array DemoPlayer) := do
  if names.isEmpty && decks.isEmpty then
    return defaultDemoPlayers
  if names.size != decks.size then
    throw s!"--name and --deck must be given the same number of times (got {names.size} names and {decks.size} decks)"
  if names.size < 2 then
    throw "A game needs at least two players (CR 100.1)"
  let players := names.mapIdx (fun i n => { name := n, deck := decks[i]! })
  match duplicatePlayerName? players with
  | some name => throw s!"Duplicate player name: {name}"
  | none => return players

/-- Constructed play (CR 100.2a) when `--constructed` is set; otherwise limited. -/
def demoFormat (constructed : Bool) : Format :=
  if constructed then .constructed else .limited

/-- `startingPlayer` is the seat that takes the first turn after CR 103.1. -/
def demoConfig (seed : UInt64) (startingPlayer : Option Nat := some 0)
    (players : Array DemoPlayer := defaultDemoPlayers)
    (norandom : Bool := false) (constructed : Bool := false) : StartConfig := {
  seats := seatsFromPlayers players
  format := demoFormat constructed
  seed := seed
  startingPlayer := startingPlayer
  norandom := norandom
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

def elspethJace : Array DemoPlayer := #[
  { name := "Elspeth", deck := .welcome .white },
  { name := "Jace", deck := .welcome .blue }
]

def elspethJaceLiliana : Array DemoPlayer := #[
  { name := "Elspeth", deck := .welcome .white },
  { name := "Jace", deck := .welcome .blue },
  { name := "Liliana", deck := .welcome .black }
]

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

/-- Print each line of an optional multi-line block indented by two spaces. -/
def printIndentedBlock (block? : Option String) : IO Unit := do
  match block? with
  | some block =>
    for line in block.splitOn "\n" do
      IO.println s!"  {line}"
  | none => pure ()

/-- Print the locked-in cost while it still needs to be paid (CR 601.2h). -/
def printPendingCost (g : Game) : IO Unit :=
  printIndentedBlock (pendingCostLine g)

/-- Print how much combat damage each creature must assign and to whom. -/
def printCombatAssignment (g : Game) : IO Unit :=
  printIndentedBlock (combatDamageAssignmentBlock g)

/-- Print which legendary permanents the acting player may keep. -/
def printLegendRule (g : Game) : IO Unit :=
  printIndentedBlock (legendRuleBlock g)

/-- Print which triggered abilities the acting player must put on the stack. -/
def printTriggerOrder (g : Game) : IO Unit :=
  printIndentedBlock (triggerOrderBlock g)

/-- Lines listing objects the host must name for a `--norandom` result. -/
def randomChoiceLines (g : Game) (ids : Array ObjectId) : String :=
  String.intercalate "\n"
    (ids.toList.map (fun id =>
      match g.findObject? id with
      | some o => s!"  {o.id} {o.name}"
      | none => s!"  {id}"))

/-- Prompt for a pending random event (`--norandom`). -/
def randomPromptBlock (g : Game) : Option String :=
  match g.pendingRandom? with
  | none => none
  | some (.shuffleLibrary p) =>
    let lib := (g.player p).library
    some <|
      s!"{(g.player p).name} shuffles their library. Provide the new order (bottom first).\n" ++
      "  shuffle            keep the current order\n" ++
      "  shuffle <id>...\n" ++
      randomChoiceLines g lib
  | some (.orderInto ids dest) =>
    some <|
      s!"Provide the random order of these cards into {zoneLabel g dest} (first listed = first / bottom).\n" ++
      "  order              keep their current order\n" ++
      "  order <id>...\n" ++
      randomChoiceLines g ids
  | some (.chooseObject ids) =>
    some <|
      "Choose which object the random event selected.\n" ++
      "  pick <id>\n" ++
      randomChoiceLines g ids
  | some (.chooseIndex n) =>
    if n == 2 then
      some "Coin toss: flip heads  or  flip tails  (also random 0 / random 1)"
    else
      some s!"Choose a number from 0 to {n - 1}: random <n>"

/-- Pending cost, combat-damage assignment, legend-rule, trigger order, or
a `--norandom` result. -/
def printPendingPrompt (g : Game) : IO Unit := do
  printPendingCost g
  printCombatAssignment g
  printLegendRule g
  printTriggerOrder g
  printIndentedBlock (randomPromptBlock g)

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
  IO.println s!"Mtg.Engine ({Rules.identification})"
  IO.println s!"Rules source: {Rules.sourceUrl}"
  IO.println ""

/-- Announce which deck each player is using. -/
def deckAssignmentLine (p : DemoPlayer) : String :=
  match p.deck with
  | .welcome c => s!"{p.name} uses the {c.englishName} Hobbit Welcome Deck."
  | .file path => s!"{p.name} uses the deck list {path}."

def printDeckAssignments (players : Array DemoPlayer) : IO Unit := do
  for p in players do
    IO.println (deckAssignmentLine p)
  IO.println ""

/-- Load Welcome Decks and any `--deck` files into seats. -/
def loadSeats (players : Array DemoPlayer) : IO (Except String (Array Seat)) := do
  let mut seats : Array Seat := #[]
  for p in players do
    match p.deck with
    | .welcome c =>
      seats := seats.push { name := p.name, deck := hobbitDeck c }
    | .file path =>
      match (← loadDeckListFile path) with
      | .error e => return .error e
      | .ok (cards, sideboard) =>
        seats := seats.push { name := p.name, deck := cards, sideboard }
  return .ok seats

/-- Create the demo game after the starting player is known (CR 103.1). -/
def startGame (seed : UInt64) (startingPlayer : Option Nat := some 0)
    (seats : Array Seat := demoSeats) (norandom : Bool := false)
    (constructed : Bool := false) : IO Game := do
  match Start.start { seats, format := demoFormat constructed, seed, startingPlayer, norandom } with
  | .error e =>
    IO.eprintln s!"Failed to start game: {e}"
    throw (IO.userError e)
  | .ok g => return g

/-- Print the opening log and board after the game has started. -/
def printOpening (g : Game) (viewer : Option PlayerId := none) : IO Unit := do
  let _ ← printLog g 0 viewer
  printState g viewer
  printPendingPrompt g

/-- Start a demo game and print the opening snapshot. The starting player is
the seat chosen under CR 103.1. Banner, decks, and the chooser announcement
are printed first. -/
def startDemo (seed : UInt64) (startingPlayer : Option Nat := some 0)
    (viewer : Option PlayerId := none)
    (seats : Array Seat := demoSeats) (norandom : Bool := false)
    (constructed : Bool := false) : IO Game := do
  let g ← startGame seed startingPlayer seats norandom constructed
  printOpening g viewer
  return g

def helpInteractive (controlAll : Bool := false)
    (you : String := "the first player") : String :=
  let viewWho := if controlAll then "the acting player" else you
  s!"Commands:
  help                 Show this help
  first <name>         Choose who takes the first turn (CR 103.1)
  shuffle [id...]      Supply a library shuffle (bottom first); no ids keeps the current order
  order [id...]        Supply the order of cards for a random rearrangement
  pick <id>            Choose the object selected by a random event
  random <n>           Supply a 0-based index for a random roll
  flip heads|tails     Supply a coin toss
  state                Print the board
  visible              Print only information {viewWho} can see (CR 400.2)
  visible on           Use {viewWho}'s view for state and later updates
  visible off          Show full information in state and later updates
  keep                 Keep this opening hand (CR 103.5)
  keep <id>            Choose which legendary permanent to keep (CR 704.5j)
  stack <id> [id...]   Put waiting triggered abilities on the stack in that source order (CR 603.3b)
  mulligan             Declare a mulligan; taken after all declarations (CR 103.5 / 103.5c)
  bottom <id> [id...]  Put cards on the bottom after a mulligan
  pass                 Pass priority
  your turn            Pass until combat of the next turn if that turn is not yours (only you pass; uses noattack)
  my turn              Pass until the main phase of the next turn if that turn is yours (only you pass; uses noattack)
  main phase           Pass until the next main phase (only you pass; uses noattack)
  attack step          Pass until the next declare attackers step (only you pass)
  ignore               Pass until your next main phase (never interrupted; only you pass; uses noattack)
  pay                  Pay a proposed spell or ability's cost (CR 601.2h)
  autopay              Tap mana sources and pay the current cost (CR 601.2g–h)
  pay-extra            Pay extra generic mana as an additional cost (CR 601.2b)
  sacrifice <id>       Sacrifice a creature or artifact to pay a cost, a creature a resolved trigger requires, or a creature as a resolving effect
  sacrifice            Choose to sacrifice as an additional cost (CR 601.2b)
  play <id>            Play a land
  tap <id> [id...] [color]  Tap listed permanents for mana (optional W/U/B/R/G)
  mana <id> <n> <mana> [id...]  Activate mana ability n (1-based) of a permanent, adding the listed mana (e.g. WWU); list the permanents or cards that pay its sacrifice or discard cost
  activate <id> [n]    Begin activating an ability (permanent, hand, or graveyard; then tap for mana and pay). n is 1-based when a card has more than one
  mode <n>             Choose a mode for a modal spell or ability (CR 601.2b / 700.2)
  x <n>                Choose a value for X (CR 107.3a / 601.2b)
  cast <id>            Begin casting a spell (CR 601.2a)
  cast <id> adventure  Cast an adventurer card as its Adventure (CR 715.3)
  cast <id> sneak <attacker>  Cast for the sneak cost, returning that unblocked attacker to hand
  target <id|name|opponent> [n] ...  Announce every target of one “target” word together (CR 601.2c); n is damage when dividing (CR 601.2d)
  scry                 Finish scrying; keep looked-at cards on top
  scry top <id>...     Put listed cards on top (last = new top); rest go to the bottom
  scry bottom <id>...  Put listed cards on the bottom (first = new bottom); rest stay on top
  scry top <id>... bottom <id>...  Choose both piles and their orders (CR 701.20)
  surveil              Finish surveilling; keep looked-at cards on top
  surveil top <id>...  Keep listed cards on top (last = new top); rest go to the graveyard
  surveil graveyard <id>...  Put listed cards into the graveyard in that order; rest stay on top
  surveil top <id>... graveyard <id>...  Choose both piles and their orders (CR 701.25)
  convoke <id> [id...]  Tap those creatures to help pay for the spell (CR 702.51)
  improvise <id> [id...]  Tap those artifacts to help pay for the spell (CR 702.126)
  proliferate [id|name|opponent ...]  Give each chosen permanent and player another counter of each kind it has (CR 701.34)
  discard <id>         Discard a card (CR 701.9), or pay an additional cost
  discard              Choose to discard as an additional cost (CR 601.2b)
  attach <id>          Attach that Equipment you control
  connive              Have the entering Villain connive (Baron Strucker)
  decline              Decline an optional discard, attach, cast, put, connive, or choose no target
  accept               Agree to an optional action offered while an effect resolves
  choose <id> [id...]  Choose cards or permanents an effect asks for
  attack               Attack with every creature that can
  attack <id> [id...]  Attack with the listed creatures
  attack [id...] [at] <name|opponent>  Attack those (or all that can) at that player
  attack <id> [at] <name> <id> [at] <name> ...  Each listed creature attacks that player
  attack <id> at <planeswalker id>  Attack that planeswalker
  name <card name>     Name a card when asked (Meddling Mage)
  noattack             Declare no attackers
  block                Block each attacker with a legal unused blocker
  block <b> <a> [...]  Assign listed blocker/attacker pairs
  noblock              Declare no blockers
  assign               Use the default combat damage assignment (CR 510.1)
  assign <s> <t> <n> [...]  Divide combat damage: source, creature or defending player, amount (CR 510.1c–d)
  concede              Concede
  quit                 Exit
"

def helpChooseFirst : String :=
  "Commands:
  help                 Show this help
  first <name>         Choose who takes the first turn (CR 103.1)
  quit                 Exit
"

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

/-- Parse a single natural number, or `usage` if the tokens are not exactly one. -/
def parseNatArg (tokens : List String) (usage : String) : Except String Nat :=
  match commandTokens tokens with
  | [arg] =>
    match arg.toNat? with
    | none => throw usage
    | some n => return n
  | _ => throw usage

/-- The object `id`, or `"no such object"`. -/
def requireObject (g : Game) (id : ObjectId) : Except String GameObject :=
  match g.findObject? id with
  | none => throw "no such object"
  | some o => return o

/-- Throw `"no such object"` unless every listed object exists. -/
def requireObjects (g : Game) (ids : Array ObjectId) : Except String Unit :=
  ids.forM (fun id => discard (requireObject g id))

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

def attackUsage : String := "usage: attack [id ...] [at] <name|opponent|planeswalker id> ..."

/-- True when `token` names a player or `opponent`. -/
def isAttackDefenderToken (g : Game) (token : String) : Bool :=
  let lower := token.map Char.toLower
  lower == "opponent" || g.players.any (fun pl => pl.name.map Char.toLower == lower)

/-- Parse who is being attacked: a player name or `opponent`. -/
def parseAttackDefender (g : Game) (p : PlayerId) (token : String) : Except String PlayerId :=
  let lower := token.map Char.toLower
  if lower == "opponent" then
    return g.opponent p
  else
    match g.players.find? (fun pl => pl.name.map Char.toLower == lower) with
    | none => throw attackUsage
    | some pl => g.resolveAttackDestination p (some pl.id)

/-- Where an `attack` command sends a creature: a player, or a planeswalker
that player controls (CR 506.3). -/
abbrev AttackDest := PlayerId × Option ObjectId

/-- Parse an `at` destination: a player, `opponent`, or a planeswalker id. -/
def parseAttackDest (g : Game) (p : PlayerId) (token : String) : Except String AttackDest :=
  match parseObjectId? token with
  | some id =>
    match g.findObject? id with
    | some pw =>
      if pw.isOnBattlefield && pw.printed.isPlaneswalker then
        .ok (pw.controller.getD pw.owner, some id)
      else .error s!"{pw.name} is not a planeswalker on the battlefield"
    | none => .error attackUsage
  | none => (parseAttackDefender g p token).map (·, none)

/-- Attackers for an interactive `attack` command. Omitted ids mean every
creature that currently can attack. -/
def attackerIdsForCommand (g : Game) (tokens : List String) : Except String (Array ObjectId) :=
  let tokens := commandTokens tokens
  if tokens.isEmpty then
    .ok (g.battlefield.filter (g.canAttack) |>.map (·.id))
  else
    parseObjectIds tokens attackUsage

/-- Split `attack` tokens into per-creature destinations. A player name or
`at <name|opponent|planeswalker id>` applies to the preceding ids (or to
every creature that can attack if none were listed). Later pairs may name a
different player or planeswalker (CR 508.1). -/
def parseAttackCommand (g : Game) (p : PlayerId) (tokens : List String) :
    Except String (Array (ObjectId × Option AttackDest)) :=
  let tokens := commandTokens tokens
  go tokens #[] #[] none
where
  flush (ids : Array ObjectId) (dest : Option AttackDest)
      (acc : Array (ObjectId × Option AttackDest)) :
      Array (ObjectId × Option AttackDest) :=
    ids.foldl (fun a id => a.push (id, dest)) acc
  go : List String → Array ObjectId → Array (ObjectId × Option AttackDest) →
      Option AttackDest → Except String (Array (ObjectId × Option AttackDest))
    | [], pending, acc, defaultDest =>
      if pending.isEmpty && acc.isEmpty then
        .ok ((g.battlefield.filter (g.canAttack) |>.map (·.id)).map (fun id =>
          (id, defaultDest)))
      else if pending.isEmpty then
        .ok acc
      else
        .ok (flush pending defaultDest acc)
    | "at" :: rest, pending, acc, defaultDest =>
      match rest with
      | [] => .error attackUsage
      | name :: rest' =>
        match parseAttackDest g p name with
        | .error e => .error e
        | .ok dest =>
          if pending.isEmpty then
            if acc.isEmpty then go rest' #[] acc (some dest)
            else .error attackUsage
          else
            go rest' #[] (flush pending (some dest) acc) defaultDest
    | t :: rest, pending, acc, defaultDest =>
      if isAttackDefenderToken g t then
        match parseAttackDefender g p t with
        | .error e => .error e
        | .ok dest =>
          if pending.isEmpty then go rest #[] acc (some (dest, none))
          else go rest #[] (flush pending (some (dest, none)) acc) defaultDest
      else
        match parseObjectId? t with
        | none => .error attackUsage
        | some id => go rest (pending.push id) acc defaultDest

def applyAttack (g : Game) (p : PlayerId) (tokens : List String) : Except String Game := do
  let attacks ← parseAttackCommand g p tokens
  let ids := attacks.map (·.1)
  let each := attacks.map (fun a => a.2.map (·.1))
  let pws := attacks.map (fun a => a.2.bind (·.2))
  requireObjects g ids
  g.apply p (.declareAttackers ids none each pws)

/-- Pair unused legal blockers with attackers. A creature with menace is
covered only when two blockers can be assigned (CR 702.111b); leftover
blockers then cover attackers that do not have menace. A bare `block`
covers as many attacks as possible. -/
def greedyBlockAssignments (g : Game) : Array (ObjectId × ObjectId) :=
  Id.run do
    let defender := g.currentBlockersPlayer
    let attackers := g.battlefield.filter (fun a =>
      a.status.attacking && a.status.attackingWhom.getD defender == defender)
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
  requireObjects g (asgn.flatMap (fun (blocker, attacker) => #[blocker, attacker]))
  g.apply p (.declareBlockers asgn)

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
  let dests :=
    let ps := g.defendingPlayers
    if ps.isEmpty then #[g.defendingPlayer] else ps
  dests.any (fun d => lower == (g.player d).name.map Char.toLower) ||
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
  requireObjects g
    (asgns.flatMap (fun a => #[a.source] ++ a.toCreatures.map (·.1)))
  g.apply p (.assignCombatDamage asgns)

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
  requireObjects g ids
  g.apply p (.putOnBottom ids)

def visibleUsage : String := "usage: visible [on|off]"

/-- `none` prints the first listed player's view once; `some true/false` turns
follow mode on or off. -/
def applyVisible (tokens : List String) : Except String (Option Bool) :=
  match commandTokens tokens with
  | [] => .ok none
  | ["on"] => .ok (some true)
  | ["off"] => .ok (some false)
  | _ => .error visibleUsage

/-- The first listed player's viewpoint when follow mode is on; omniscient
otherwise. -/
def humanView (playerView : Bool) : Option PlayerId :=
  if playerView then some ⟨0⟩ else none

/-- Hidden-information view. Interactive mode always follows the first listed
player; multiplayer follows the player who must act. -/
def currentView (g : Game) (playerView : Bool) (controlAll : Bool) : Option PlayerId :=
  if !playerView then none
  else if controlAll then g.actor
  else some ⟨0⟩

/-- Acting player for auto-step error messages. -/
def actorDisplayName (g : Game) (fallback := "Player") : String :=
  match g.actor with
  | some p => (g.player p).name
  | none => fallback

/-- Who the console should issue the next action as. -/
def actingPlayer (g : Game) : Except String PlayerId :=
  match g.actor with
  | some p => .ok p
  | none => .error "No player has an action"

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

def manaUsage : String := "usage: mana <id> <ability number> <mana letters> [id ...]"

/-- Activate one mana ability, naming every mana it adds (CR 605.3). -/
def applyManaAbility (g : Game) (p : PlayerId) (tokens : List String) : Except String Game := do
  match commandTokens tokens with
  | idTok :: nTok :: manaTok :: rest =>
    let some id := parseObjectId? idTok | throw manaUsage
    let some n := nTok.toNat? | throw manaUsage
    if n == 0 then throw manaUsage
    let mana ← manaTok.toList.toArray.mapM (fun c =>
      match parseManaType? (String.singleton c) with
      | some m => pure m
      | none => throw manaUsage)
    let costIds ← if rest.isEmpty then pure #[] else parseObjectIds rest manaUsage
    g.apply p (.activateManaAbility id (n - 1) mana costIds)
  | _ => throw manaUsage

def playUsage : String := "usage: play <id>"

/-- Play the named land from a zone the player is allowed to play from. -/
def applyPlay (g : Game) (p : PlayerId) (tokens : List String) : Except String Game :=
  applyObjectCommand g p tokens playUsage .playLand

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
    match g.pending, g.proposedSpell.bind (fun prop => g.findObject? prop.spellId) with
    | .chooseAdditionalCost _, some spell =>
      if spell.printed.additionalCostOrPayGeneric.isSome then
        g.apply p (.chooseAdditionalCost false)
      else throw sacrificeUsage
    | _, _ => throw sacrificeUsage
  | [_] => applyObjectCommand g p tokens sacrificeUsage .sacrifice
  | _ => throw sacrificeUsage

def payExtraUsage : String := "usage: pay-extra"

/-- Pay extra generic mana rather than sacrifice or discard, as an additional
cost (CR 601.2b). -/
def applyPayExtra (g : Game) (p : PlayerId) (tokens : List String) : Except String Game := do
  match commandTokens tokens with
  | [] => g.apply p (.chooseAdditionalCost true)
  | _ => throw payExtraUsage

def modeUsage : String := "usage: mode <n>"

/-- Choose a mode of a modal spell or ability (CR 601.2b). Modes are 1-indexed. -/
def applyMode (g : Game) (p : PlayerId) (tokens : List String) : Except String Game := do
  match ← parseNatArg tokens modeUsage with
  | 0 => throw modeUsage
  | n => g.apply p (.chooseMode (n - 1))

def xUsage : String := "usage: x <n>"

/-- Choose a value for `{X}` (CR 107.3a / 601.2b). -/
def applyX (g : Game) (p : PlayerId) (tokens : List String) : Except String Game := do
  g.apply p (.chooseX (← parseNatArg tokens xUsage))

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
  | [arg, "sneak", attacker] =>
    match parseObjectId? arg, parseObjectId? attacker with
    | some id, some a => g.apply p (.castWithSneak id a)
    | _, _ => throw castUsage
  | _ => throw castUsage

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

/-- Convoke (CR 702.51): `convoke <id> ...` taps those creatures to pay for
the spell being cast. -/
def applyConvoke (g : Game) (p : PlayerId) (tokens : List String) : Except String Game := do
  let ids ← parseObjectIds (commandTokens tokens) "usage: convoke <id> ..."
  requireObjects g ids
  g.apply p (.choosePermanents ids)

/-- Proliferate once (CR 701.34): `proliferate` chooses nothing;
`proliferate <id|player> ...` gives each another counter of each kind. -/
def applyProliferate (g : Game) (p : PlayerId) (tokens : List String) : Except String Game := do
  let ts ← (commandTokens tokens).foldlM (fun acc arg => do
    let t ← parseTarget g p arg
    pure (acc.push t)) #[]
  g.apply p (.targets ts)

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
      requireObjects g ids
      let top := looked.filter (fun id => !ids.contains id)
      g.apply p (.scry top ids)
    | "top" :: rest =>
      let (topToks, botRest) := splitAtKeyword "bottom" rest
      let topIds ← parseObjectIds topToks scryUsage
      requireObjects g topIds
      let bottomIds ←
        match botRest with
        | none => pure (looked.filter (fun id => !topIds.contains id))
        | some [] => pure #[]
        | some ts =>
          let ids ← parseObjectIds ts scryUsage
          requireObjects g ids
          pure ids
      g.apply p (.scry topIds bottomIds)
    | _ => throw scryUsage
  | .surveil _ _ => throw "You are surveilling, not scrying; use surveil (CR 701.25)"
  | _ => throw "Not time to scry (CR 701.20)"

def surveilUsage : String := "usage: surveil [top <id> ...] [graveyard <id> ...]"

/-- Finish a pending surveil (CR 701.25). Bare `surveil` keeps the looked-at
cards on top in their current order. `surveil graveyard <ids>` puts those
cards into the graveyard in that order and the rest stay on top in their
current relative order. `surveil top <ids>` keeps those cards on top
(last = new top) and puts the rest into the graveyard. Both piles may be
listed to choose each order. -/
def applySurveil (g : Game) (p : PlayerId) (tokens : List String) : Except String Game := do
  match g.pending with
  | .surveil q n =>
    if p != q then
      throw s!"Only {(g.player q).name} may surveil"
    let looked := g.scryLookedIds p n
    match commandTokens tokens with
    | [] => g.apply p (.surveil looked #[])
    | "graveyard" :: rest =>
      let ids ← parseObjectIds rest surveilUsage
      requireObjects g ids
      g.apply p (.surveil (looked.filter (fun id => !ids.contains id)) ids)
    | "top" :: rest =>
      let (topToks, gyRest) := splitAtKeyword "graveyard" rest
      let topIds ← parseObjectIds topToks surveilUsage
      requireObjects g topIds
      let graveyardIds ←
        match gyRest with
        | none => pure (looked.filter (fun id => !topIds.contains id))
        | some [] => pure #[]
        | some ts =>
          let ids ← parseObjectIds ts surveilUsage
          requireObjects g ids
          pure ids
      g.apply p (.surveil topIds graveyardIds)
    | _ => throw surveilUsage
  | .scry _ _ => throw "You are scrying, not surveilling; use scry (CR 701.20)"
  | _ => throw "Not time to surveil (CR 701.25)"

def discardUsage : String := "usage: discard <id>"

/-- Discard the named card from hand, or with no id choose the discard option
of an additional cost (CR 601.2b). -/
def applyDiscard (g : Game) (p : PlayerId) (tokens : List String) : Except String Game :=
  match commandTokens tokens with
  | [] =>
    match g.pending, g.proposedSpell.bind (fun prop => g.findObject? prop.spellId) with
    | .chooseAdditionalCost _, some spell =>
      if spell.printed.additionalCostDiscardOrPayGeneric.isSome then
        g.apply p (.chooseAdditionalCost false)
      else throw discardUsage
    | _, _ => throw discardUsage
  | [_] => applyObjectCommand g p tokens discardUsage .discard
  | _ => throw discardUsage

def declineUsage : String := "usage: decline"
def conniveUsage : String := "usage: connive"

/-- Decline an optional discard, attach, cast, put-from-hand, connive, or choose no
target for an “up to one” instance of the word “target” (CR 115.1c / 601.2c). -/
def applyDecline (g : Game) (p : PlayerId) (tokens : List String) : Except String Game := do
  match commandTokens tokens with
  | [] => g.apply p .decline
  | _ => throw declineUsage

def acceptUsage : String := "usage: accept"
def chooseUsage : String := "usage: choose <id> ..."

/-- Agree to an optional action offered while an effect resolves. -/
def applyAccept (g : Game) (p : PlayerId) (tokens : List String) : Except String Game := do
  match commandTokens tokens with
  | [] => g.apply p .accept
  | _ => throw acceptUsage

/-- Choose cards or permanents for a choice made while an effect resolves. -/
def applyChoose (g : Game) (p : PlayerId) (tokens : List String) : Except String Game := do
  let ids ← parseObjectIds (commandTokens tokens) chooseUsage
  requireObjects g ids
  g.apply p (.choosePermanents ids)

/-- Have the entering Villain connive (Baron Strucker; MSH 422). -/
def applyConniveChoice (g : Game) (p : PlayerId) (tokens : List String) : Except String Game := do
  match commandTokens tokens with
  | [] => g.apply p .haveVillainConnive
  | _ => throw conniveUsage

def attachUsage : String := "usage: attach <id>"

/-- Attach the named Equipment you control to the creature waiting for one. -/
def applyAttach (g : Game) (p : PlayerId) (tokens : List String) : Except String Game :=
  applyObjectCommand g p tokens attachUsage (fun id => .choosePermanents #[id])

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

def autopayUsage : String := "usage: autopay"

/-- Whether the locked-in cost is payable from the current pool. -/
def canPayProposed (g : Game) (p : PlayerId) (prop : ProposedSpell) : Bool :=
  (g.player p).manaPool.canPay prop.cost
    (g.proposedAllowsElfRestricted prop)
    (g.proposedAllowsInstRestricted prop)

/-- Activate mana abilities chosen by the heuristic, then pay (CR 601.2g–h).
Taps noncreatures before creatures when both help, and prefers colorless
when that type can be spent. Hidden Lair taps for `{U}` or `{B}` when that
ability is live and the color is needed. Fails without changing the game
if the cost cannot be paid. -/
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
    | .chooseX _ => throw "Choose a value for X first (CR 107.3a / 601.2b)"
    | .chooseTargets _ => throw "Choose a target first (CR 601.2c)"
    | .chooseAdditionalCost _ => throw "Choose an additional cost first (CR 601.2b)"
    | _ => throw "No spell or ability is waiting to be paid for (CR 601.2h)"

/-- Tap necessary mana sources (noncreatures first; colorless if usable) and
pay the current cost. Hidden Lair contributes `{U}` or `{B}` when that
ability can be activated. -/
def applyAutopay (g : Game) (p : PlayerId) (tokens : List String) :
    Except String AutopayResult :=
  match commandTokens tokens with
  | [] => applyAutopaySteps g p ((g.manaSources p).size + 1) #[]
  | _ => .error autopayUsage

/-- Issue `autopay` as the player who currently must act. -/
def applyAutopayAsActor (g : Game) (tokens : List String) : Except String AutopayResult := do
  let p ← actingPlayer g
  applyAutopay g p tokens

def shuffleUsage : String := "usage: shuffle [id ...]"
def orderUsage : String := "usage: order [id ...]"
def pickUsage : String := "usage: pick <id>"
def randomIndexUsage : String := "usage: random <n>"
def flipUsage : String := "usage: flip heads|tails"

/-- Apply a `--norandom` result as the current actor; any actor is accepted. -/
def applyAsAnyActor (g : Game) (action : Action) : Except String Game :=
  match g.actor with
  | some p => g.apply p action
  | none =>
    if g.players.isEmpty then .error "No random event is waiting for a result"
    else g.apply ⟨0⟩ action

def applySupplyOrder (g : Game) (ids : Array ObjectId) : Except String Game :=
  applyAsAnyActor g (.supplyOrder ids)

def applySupplyIndex (g : Game) (i : Nat) : Except String Game :=
  applyAsAnyActor g (.supplyIndex i)

/-- `shuffle` / `order` with no ids keep the current order. -/
def applySuppliedOrder (g : Game) (tokens : List String) (usage : String) :
    Except String Game := do
  let tokens := commandTokens tokens
  if tokens.isEmpty then
    applySupplyOrder g #[]
  else
    let ids ← parseObjectIds tokens usage
    applySupplyOrder g ids

/-- `shuffle` with no ids keeps the current library order. -/
def applyShuffle (g : Game) (tokens : List String) : Except String Game :=
  applySuppliedOrder g tokens shuffleUsage

/-- `order` with no ids keeps the current relative order. -/
def applyOrder (g : Game) (tokens : List String) : Except String Game :=
  applySuppliedOrder g tokens orderUsage

def applyPick (g : Game) (tokens : List String) : Except String Game := do
  let id ← parseRequiredObjectId tokens pickUsage
  applySupplyOrder g #[id]

def applyRandomIndex (g : Game) (tokens : List String) : Except String Game := do
  applySupplyIndex g (← parseNatArg tokens randomIndexUsage)

def applyFlip (g : Game) (tokens : List String) : Except String Game := do
  match commandTokens tokens with
  | ["heads"] | ["head"] => applySupplyIndex g 0
  | ["tails"] | ["tail"] => applySupplyIndex g 1
  | _ => throw flipUsage

/-- Whether the defending player has any legal non-empty blocker declaration.
An attacker that requires multiple blockers can be blocked only when enough
individually eligible creatures are available. -/
def hasLegalBlock (g : Game) : Bool :=
  g.battlefield.any (fun attacker =>
    attacker.status.attacking &&
      let eligible := g.battlefield.filter (fun blocker => g.canBlock blocker attacker) |>.size
      eligible >= max 1 (g.minBlockersRequired attacker))

/-- Target a pass-until shortcut stops at. -/
inductive PassUntilTarget where
  | nextTurnCombat
  | nextTurnMain
  | nextMain
  | nextDeclareAttackers
deriving DecidableEq, Repr

/-- Game after a pass-until shortcut, and the primitive lines `--output` records. -/
structure PassUntilResult where
  game : Game
  commands : Array String

def yourTurnUsage : String := "usage: your turn"
def myTurnUsage : String := "usage: my turn"
def mainPhaseUsage : String := "usage: main phase"
def attackStepUsage : String := "usage: attack step"

/-- The player who will be active on the next turn. -/
def nextTurnPlayer (g : Game) : PlayerId :=
  g.nextLiving g.activePlayer

/-- Whether `g` has reached the snapshot target from `startTurn` / `startStep`. -/
def reachedPassUntil (g : Game) (startTurn : Nat) (startStep : Step) :
    PassUntilTarget → Bool
  | .nextTurnCombat =>
    g.turnNumber > startTurn && g.step.isCombatPhase
  | .nextTurnMain =>
    g.turnNumber > startTurn && g.step.isMainPhase
  | .nextMain =>
    g.step.isMainPhase && !(g.turnNumber == startTurn && g.step == startStep)
  | .nextDeclareAttackers =>
    g.step == .declareAttackers &&
      !(g.turnNumber == startTurn && g.step == startStep)

/-- `your turn`, `my turn`, and `main phase` declare no attackers even when
creatures can attack. `attack step` still stops so attackers can be chosen. -/
def passUntilSkipsAttackers : PassUntilTarget → Bool
  | .nextDeclareAttackers => false
  | _ => true

/-- A primitive command the shortcut may issue without asking. `pass` when
someone has priority; `noattack` when `alwaysNoAttack` is set (`your turn`,
`my turn`, `main phase`, `ignore`) or when that is the sole legal declaration;
`noblock` only when that is the sole legal combat declaration (same rule as
the automatic console steps). `forceEmptyCombat` treats empty combat as
passing because another player accepted a pending shortcut. -/
def passUntilCommand? (g : Game) (forceEmptyCombat := false)
    (alwaysNoAttack := false) : Option String :=
  match g.pending, g.actor with
  | .none, some p =>
    if g.hasPriority p then some "pass" else none
  | .declareAttackers, some _ =>
    if forceEmptyCombat || alwaysNoAttack || !(g.battlefield.any g.canAttack) then
      some "noattack" else none
  | .declareBlockers, some _ =>
    if forceEmptyCombat || !hasLegalBlock g then some "noblock" else none
  | _, _ => none

/-- Apply one recorded pass-until line as the current actor. -/
def applyPassUntilLine (g : Game) (line : String) : Except String Game := do
  let p ← actingPlayer g
  match line with
  | "pass" => g.apply p .pass
  | "noattack" => g.apply p (.declareAttackers #[])
  | "noblock" => g.apply p (.declareBlockers #[])
  | _ => throw s!"Unknown pass-until command: {line}"

/-- Fuel for crossing a few turns of priority windows and empty combat. -/
def passUntilFuel : Nat := 200

/-- Kind of pending pass-until goal stored by the console and `--check` replay. -/
inductive PassUntilKind where
  | named (target : PassUntilTarget)
  | ignore
deriving DecidableEq, Repr

/-- A shortcut that stays active until its target, unless an interruptible
goal is cancelled by another player's non-pass action. -/
structure PassUntilGoal where
  issuer : PlayerId
  startTurn : Nat
  startStep : Step
  kind : PassUntilKind
deriving DecidableEq, Repr

def PassUntilGoal.uninterruptible (goal : PassUntilGoal) : Bool :=
  match goal.kind with
  | .ignore => true
  | .named _ => false

def passUntilGoalAt (g : Game) (p : PlayerId) (kind : PassUntilKind) : PassUntilGoal :=
  { issuer := p, startTurn := g.turnNumber, startStep := g.step, kind }

def ignoreUsage : String := "usage: ignore"

/-- True when `g` is a main phase of the issuer that is not the starting step. -/
def reachedIgnore (g : Game) (goal : PassUntilGoal) : Bool :=
  g.step.isMainPhase && g.activePlayer == goal.issuer &&
    !(g.turnNumber == goal.startTurn && g.step == goal.startStep)

def reachedPassUntilGoal (g : Game) (goal : PassUntilGoal) : Bool :=
  match goal.kind with
  | .named t => reachedPassUntil g goal.startTurn goal.startStep t
  | .ignore => reachedIgnore g goal

/-- Only issue pass-until commands as `issuer`; other players may still act. -/
def issuerPassUntilCommand? (g : Game) (issuer : PlayerId)
    (forceEmptyCombat := false) (alwaysNoAttack := false) : Option String :=
  match g.actor with
  | some p =>
    if p == issuer then
      passUntilCommand? g forceEmptyCombat (alwaysNoAttack := alwaysNoAttack)
    else none
  | none => none

/-- `ignore` only issues commands as the issuer; other players may still act. -/
def ignoreCommand? (g : Game) (issuer : PlayerId) (forceEmptyCombat := false) : Option String :=
  issuerPassUntilCommand? g issuer forceEmptyCombat (alwaysNoAttack := true)

def passUntilGoalCommand? (g : Game) (goal : PassUntilGoal)
    (forceEmptyCombat := false) : Option String :=
  match goal.kind with
  | .named t =>
    issuerPassUntilCommand? g goal.issuer forceEmptyCombat
      (alwaysNoAttack := passUntilSkipsAttackers t)
  | .ignore => ignoreCommand? g goal.issuer forceEmptyCombat

/-- Error when `passUntilFuel` runs out before this goal is reached. -/
def PassUntilKind.fuelError : PassUntilKind → String
  | .named _ => "Could not finish passing to that step"
  | .ignore => "Could not finish passing to your next main phase"

/-- Keep issuing the goal's commands (`pass`, and empty combat declarations
where the goal allows them) until the goal is reached, the game ends, or no
command can be issued. Every pass-until shortcut only issues commands as the
issuer, so another player can act. A named goal with nothing done yet errors
because a player must take a non-pass action; `ignore` stops quietly. -/
def applyPassUntilGoalSteps (g : Game) (goal : PassUntilGoal) (fuel : Nat)
    (cmds : Array String) (forceEmptyCombat := false) :
    Except String PassUntilResult :=
  match fuel with
  | 0 => throw goal.kind.fuelError
  | n + 1 =>
    if g.over || reachedPassUntilGoal g goal then
      .ok { game := g, commands := cmds }
    else
      match passUntilGoalCommand? g goal forceEmptyCombat with
      | none =>
        match goal.kind with
        | .named _ =>
          if cmds.isEmpty then
            .error "A player must take an action other than pass"
          else
            .ok { game := g, commands := cmds }
        | .ignore => .ok { game := g, commands := cmds }
      | some line =>
        match applyPassUntilLine g line with
        | .error e =>
          if cmds.isEmpty then .error e
          else .ok { game := g, commands := cmds }
        | .ok g' => applyPassUntilGoalSteps g' goal n (cmds.push line) forceEmptyCombat

def applyPassUntil (g : Game) (p : PlayerId) (target : PassUntilTarget)
    (forceEmptyCombat := false) : Except String PassUntilResult :=
  applyPassUntilGoalSteps g (passUntilGoalAt g p (.named target)) passUntilFuel #[]
    forceEmptyCombat

/-- `your turn`: pass until combat of the next turn, when that turn is not
the issuer's. Only the issuer passes; other players may still act. -/
def applyYourTurn (g : Game) (p : PlayerId) (tokens : List String)
    (forceEmptyCombat := false) : Except String PassUntilResult := do
  match commandTokens tokens with
  | ["turn"] =>
    if nextTurnPlayer g == p then
      throw "The next turn is yours"
    else
      applyPassUntil g p .nextTurnCombat forceEmptyCombat
  | _ => throw yourTurnUsage

/-- `my turn`: pass until the main phase of the next turn, when that turn
is the issuer's. Only the issuer passes; other players may still act. -/
def applyMyTurn (g : Game) (p : PlayerId) (tokens : List String)
    (forceEmptyCombat := false) : Except String PassUntilResult := do
  match commandTokens tokens with
  | ["turn"] =>
    if nextTurnPlayer g != p then
      throw "The next turn is not yours"
    else
      applyPassUntil g p .nextTurnMain forceEmptyCombat
  | _ => throw myTurnUsage

/-- `main phase`: pass until the next main phase. Only the issuer passes;
other players may still act. -/
def applyMainPhase (g : Game) (p : PlayerId) (tokens : List String)
    (forceEmptyCombat := false) : Except String PassUntilResult := do
  match commandTokens tokens with
  | ["phase"] => applyPassUntil g p .nextMain forceEmptyCombat
  | _ => throw mainPhaseUsage

/-- `attack step`: pass until the next declare attackers step. Only the
issuer passes; other players may still act. -/
def applyAttackStep (g : Game) (p : PlayerId) (tokens : List String)
    (forceEmptyCombat := false) : Except String PassUntilResult := do
  match commandTokens tokens with
  | ["step"] => applyPassUntil g p .nextDeclareAttackers forceEmptyCombat
  | _ => throw attackStepUsage

/-- `ignore`: pass until the issuer's next main phase. Stops when another
player must act so they can take that action; the console loop resumes
passing for the issuer afterward. Other players' actions never cancel this
goal. -/
def applyIgnore (g : Game) (p : PlayerId) (tokens : List String)
    (forceEmptyCombat := false) : Except String PassUntilResult := do
  match commandTokens tokens with
  | [] =>
    applyPassUntilGoalSteps g (passUntilGoalAt g p .ignore) passUntilFuel #[]
      forceEmptyCombat
  | _ => throw ignoreUsage

def shortcutKind? (cmd : String) (args : List String) : Option PassUntilKind :=
  match cmd, commandTokens args with
  | "your", ["turn"] => some (.named .nextTurnCombat)
  | "my", ["turn"] => some (.named .nextTurnMain)
  | "main", ["phase"] => some (.named .nextMain)
  | "attack", ["step"] => some (.named .nextDeclareAttackers)
  | "ignore", [] => some .ignore
  | _, _ => none

/-- Two-word shortcuts that expand to `pass` (and empty combat declarations). -/
def isPassShortcut (cmd : String) (args : List String) : Bool :=
  (shortcutKind? cmd args).isSome

/-- First word of a pass-until shortcut, including incomplete `your` / `my` /
`main` so usage errors are reported. `attack` is only a shortcut with `step`. -/
def isPassShortcutCmd (cmd : String) (args : List String) : Bool :=
  cmd == "your" || cmd == "my" || cmd == "main" || cmd == "ignore" ||
    (cmd == "attack" && commandTokens args == ["step"])

def applyPassShortcut (g : Game) (p : PlayerId) (cmd : String) (args : List String)
    (forceEmptyCombat := false) : Except String PassUntilResult := do
  match cmd with
  | "your" => applyYourTurn g p args forceEmptyCombat
  | "my" => applyMyTurn g p args forceEmptyCombat
  | "main" => applyMainPhase g p args forceEmptyCombat
  | "attack" => applyAttackStep g p args forceEmptyCombat
  | "ignore" => applyIgnore g p args forceEmptyCombat
  | _ => throw s!"Unknown command: {cmd}"

/-- Issue a pass-until shortcut as the player who currently must act. -/
def applyPassShortcutAsActor (g : Game) (cmd : String) (args : List String)
    (forceEmptyCombat := false) : Except String PassUntilResult := do
  let p ← actingPlayer g
  applyPassShortcut g p cmd args forceEmptyCombat

/-- `pass` / empty combat declarations, or a pass-until shortcut that expands
to those commands. These do not cancel another player's interruptible shortcut. -/
def isPassSequenceCommand (cmd : String) (args : List String) : Bool :=
  cmd == "pass" || cmd == "noattack" || cmd == "noblock" || isPassShortcut cmd args

def isPassSequenceAction : Action → Bool
  | .pass => true
  | .declareAttackers ids => ids.isEmpty
  | .declareBlockers ids => ids.isEmpty
  | _ => false

def activePassUntilGoals (g : Game) (goals : Array PassUntilGoal) : Array PassUntilGoal :=
  if g.over then #[]
  else goals.filter (fun goal => !reachedPassUntilGoal g goal)

def upsertPassUntilGoal (goals : Array PassUntilGoal) (goal : PassUntilGoal) :
    Array PassUntilGoal :=
  goals.filter (fun existing => existing.issuer != goal.issuer) |>.push goal

/-- Drop interruptible goals issued by anyone other than `actor`. `ignore`
never drops. -/
def interruptPassUntilGoals (goals : Array PassUntilGoal) (actor : PlayerId) :
    Array PassUntilGoal :=
  goals.filter (fun goal => goal.uninterruptible || goal.issuer == actor)

def otherPlayerHasPassUntilGoal (goals : Array PassUntilGoal) (actor : PlayerId) : Bool :=
  goals.any (fun goal => goal.issuer != actor)

def resumablePassUntilGoal? (g : Game) (goals : Array PassUntilGoal) : Option PassUntilGoal :=
  goals.find? (fun goal => (passUntilGoalCommand? g goal).isSome)

/-- Update stored shortcuts after a command: pass sequences keep other
players' goals, other actions cancel interruptible ones, and a new shortcut
is recorded when its target is not yet reached. -/
def goalsAfterCommand (before after : Game) (actor : PlayerId) (cmd : String)
    (args : List String) (goals : Array PassUntilGoal) : Array PassUntilGoal :=
  let goals := activePassUntilGoals after goals
  let goals :=
    if isPassSequenceCommand cmd args then goals
    else interruptPassUntilGoals goals actor
  match shortcutKind? cmd args with
  | none => goals
  | some kind =>
    let goal := passUntilGoalAt before actor kind
    if !after.over && !reachedPassUntilGoal after goal then
      upsertPassUntilGoal goals goal
    else
      goals.filter (fun existing => existing.issuer != actor)

/-- Resume one stored shortcut as far as it can go without asking. -/
def resumePassUntilGoal (g : Game) (goal : PassUntilGoal) :
    Except String PassUntilResult :=
  applyPassUntilGoalSteps g goal passUntilFuel #[]

def applyInteractiveAction (g : Game) (p : PlayerId) (cmd : String) (args : List String) :
    Except String Game :=
  match cmd with
  | "keep" => applyKeep g p args
  | "stack" => applyStack g p args
  | "mulligan" => g.apply p .takeMulligan
  | "bottom" => applyBottom g p args
  | "pass" => g.apply p .pass
  | "your" => applyYourTurn g p args |>.map (·.game)
  | "my" => applyMyTurn g p args |>.map (·.game)
  | "main" => applyMainPhase g p args |>.map (·.game)
  | "ignore" => applyIgnore g p args |>.map (·.game)
  | "pay" =>
    match g.pending with
    | .payOrLetCounter _ _ _ | .payWard _ _ (.genericMana _)
    | .payWard _ _ (.discardOrPay _) =>
      g.apply p .payGeneric
    | _ => g.apply p .pay
  | "autopay" => applyAutopay g p args |>.map (·.game)
  | "pay-extra" => applyPayExtra g p args
  | "sacrifice" => applySacrifice g p args
  | "concede" => g.apply p .concede
  | "attack" =>
    match commandTokens args with
    | ["step"] => applyAttackStep g p args |>.map (·.game)
    | _ => applyAttack g p args
  | "noattack" => g.apply p (.declareAttackers #[])
  | "block" => applyBlock g p args
  | "noblock" => g.apply p (.declareBlockers #[])
  | "assign" => applyAssign g p args
  | "play" => applyPlay g p args
  | "activate" => applyActivate g p args
  | "mode" => applyMode g p args
  | "x" => applyX g p args
  | "tap" => applyTap g p args
  | "mana" => applyManaAbility g p args
  | "cast" => applyCast g p args
  | "target" => applyTarget g p args
  | "scry" => applyScry g p args
  | "surveil" => applySurveil g p args
  | "proliferate" => applyProliferate g p args
  | "convoke" => applyConvoke g p args
  | "improvise" => applyConvoke g p args
  | "discard" => applyDiscard g p args
  | "attach" => applyAttach g p args
  | "connive" => applyConniveChoice g p args
  | "decline" => applyDecline g p args
  | "accept" => applyAccept g p args
  | "choose" => applyChoose g p args
  | "name" =>
    match args with
    | [] => .error "usage: name <card name>"
    | _ => g.apply p (.chooseName (" ".intercalate args))
  | "shuffle" => applyShuffle g args
  | "order" => applyOrder g args
  | "pick" => applyPick g args
  | "random" => applyRandomIndex g args
  | "flip" => applyFlip g args
  | _ => .error s!"Unknown command: {cmd}"

/-- Issue a console command as the player who currently must act. -/
def applyInteractiveAsActor (g : Game) (cmd : String) (args : List String) : Except String Game := do
  let p ← actingPlayer g
  applyInteractiveAction g p cmd args

/-- Apply a game-state command. `autopay` expands to the `tap`/`pay` lines
that `--output` should record. Pass-until shortcuts expand to the `pass`
lines (and `noattack` / `noblock`) rather than the shortcut text.
`your turn`, `my turn`, `main phase`, and `ignore` use `noattack` when
declaring attackers. `forceEmptyCombat` is set when another player's pending
shortcut is being accepted, so empty combat declarations count as passing. -/
def applyLoggedAction (g : Game) (cmd : String) (args : List String) (line : String)
    (forceEmptyCombat := false) : Except String (Game × Array String) := do
  if cmd == "autopay" then
    let r ← applyAutopayAsActor g args
    return (r.game, r.commands)
  else if isPassShortcutCmd cmd args then
    let r ← applyPassShortcutAsActor g cmd args forceEmptyCombat
    return (r.game, r.commands)
  else
    let g' ← applyInteractiveAsActor g cmd args
    return (g', #[line])

/-- A line that starts with `--` is additional flags, not a game command. -/
def isFlagLine (s : String) : Bool :=
  s.startsWith "--"

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

/-- Write flags from `--input` at the start of `--output` only when they are
different files. Same-file sessions already contain those lines. -/
def shouldWriteInputFlags (sameFile : Bool) (flags : List String) : Bool :=
  !sameFile && !flags.isEmpty

/-- When input and output are the same file, commands already loaded from the
file stay there; only new console commands are appended. -/
def shouldRecordCommand (sameFile : Bool) (fromInput : Bool) : Bool :=
  !(sameFile && fromInput)

/-- Inspection and session commands never change the game, so they are not
written to `--output`. -/
def isNonStateCommand (cmd : String) : Bool :=
  match cmd with
  | "help" | "state" | "visible" | "quit" | "exit" => true
  | _ => false

/-- Session commands that do not change the game and may appear in a check
script. `quit` / `exit` stop a live session, so they fail a completeness check. -/
def isCheckSkipCommand (cmd : String) : Bool :=
  cmd == "help" || cmd == "state" || cmd == "visible"

/-- Consume `first <name>` when the console user would choose the starting
player (CR 103.1). Session-only lines before that command are ignored. -/
def takeStartingPlayer (seats : Array Seat) (humanChooses : Bool) (decider : Nat)
    (commands : List String) : Except String (Nat × List String) :=
  if !humanChooses then
    .ok (decider, commands)
  else
    match commands with
    | [] => .error "Missing first <name> (CR 103.1)"
    | line :: rest =>
      let parts := line.splitOn " "
      let cmd := parts.headD ""
      if isCheckSkipCommand cmd then
        takeStartingPlayer seats humanChooses decider rest
      else if cmd == "quit" || cmd == "exit" then
        .error "Game is not complete"
      else if cmd == "first" then
        match parseFirstPlayer seats (parts.drop 1) with
        | .error e => .error e
        | .ok idx => .ok (idx, rest)
      else
        .error "Choose who takes the first turn (CR 103.1): first <name>"

/-- Replay scripted game-state commands. Fails on an illegal command, leftover
commands after the game ends, `quit`, or an unfinished game. Pass-until
shortcuts stay active: other players' pass sequences do not cancel them,
and `ignore` is never cancelled. -/
def replayCompleteGameGo (g : Game) (commands : List String)
    (goals : Array PassUntilGoal) (fuel : Nat) : Except String Game :=
  match fuel with
  | 0 => .error "Could not finish replay"
  | n + 1 =>
    let goals := activePassUntilGoals g goals
    if g.over then
      match commands with
      | [] => .ok g
      | line :: rest =>
        if isCheckSkipCommand ((line.splitOn " ").headD "") then
          replayCompleteGameGo g rest goals n
        else
          .error s!"Unused command after the game ended: {line}"
    else
      let resumeLine :=
        match resumablePassUntilGoal? g goals with
        | some goal => passUntilGoalCommand? g goal
        | none => none
      match resumeLine with
      | some line =>
        match applyPassUntilLine g line with
        | .error e => .error s!"Invalid command `{line}`: {e}"
        | .ok g' => replayCompleteGameGo g' commands goals n
      | none =>
        match commands with
        | [] => .error "Game is not complete"
        | line :: rest =>
          let cmd := (line.splitOn " ").headD ""
          let args := (line.splitOn " ").drop 1
          if isCheckSkipCommand cmd then
            replayCompleteGameGo g rest goals n
          else if cmd == "quit" || cmd == "exit" then
            .error "Game is not complete"
          else if cmd == "first" then
            .error "Starting player already chosen (CR 103.1)"
          else
            match actingPlayer g with
            | .error e => .error s!"Invalid command `{line}`: {e}"
            | .ok actor =>
              let accept := otherPlayerHasPassUntilGoal goals actor
              match applyLoggedAction g cmd args line accept with
              | .error e => .error s!"Invalid command `{line}`: {e}"
              | .ok (g', _) =>
                replayCompleteGameGo g' rest
                  (goalsAfterCommand g g' actor cmd args goals) n

/-- Replay scripted game-state commands. Fails on an illegal command, leftover
commands after the game ends, `quit`, or an unfinished game. -/
def replayCompleteGame (g : Game) (commands : List String) : Except String Game :=
  replayCompleteGameGo g commands #[] (commands.length * 8 + passUntilFuel)

/-- One-line result used by `--check`. -/
def describeCheckResult (g : Game) : String :=
  match g.result with
  | some (.won p) => s!"Winner: {g.player p |>.name}"
  | some .draw => "The game is a draw."
  | none => "Game is not complete"

/-- Print the finished game's result: the winner or a draw. -/
def printResult (g : Game) : IO Unit :=
  match g.result with
  | some (.won p) => IO.println s!"Winner: {g.player p |>.name}"
  | some .draw => IO.println "The game is a draw."
  | none => pure ()

/-- Write a command to `--output` only when it was accepted as a game action
and is not already stored because `--input` is the same path. Incorrect
commands and session commands such as `state` and `quit` are omitted. -/
def shouldWriteOutput (sameFile fromInput accepted : Bool) (cmd : String) : Bool :=
  accepted && !isNonStateCommand cmd && shouldRecordCommand sameFile fromInput

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
        g.canPayAnnouncedAdditional p o available)
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

/-- Whether tapping every source in `sources` can pay `cost` for some
type assignment. -/
def canPayTappingAll (g : Game) (pool : ManaPool) (cost : ManaCost)
    (allowElf allowInst : Bool) (sources : List (GameObject × Array ManaType)) :
    Bool :=
  g.canPayFromSources pool cost allowElf allowInst sources

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
    else if prop.needsDiscardCard && (g.player p).hand.isEmpty then
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

/-- `discard <id>` when exactly one card can pay a discard additional cost. -/
def uniqueDiscardCommand (g : Game) : Option String :=
  match g.pending with
  | .discardForAdditionalCost p =>
    let hand := (g.player p).hand
    match hand[0]? with
    | some id => if hand.size == 1 then some s!"discard {id}" else none
    | none => none
  | _ => none

/-- Automatically pay a cost only after scripted input is exhausted and
there is only one legal way to pay it. -/
def shouldAutoPay (g : Game) (pending : List String) : Bool :=
  pending.isEmpty &&
    (hasUniqueManaPayment g || (uniqueSacrificeCommand g).isSome ||
      (uniqueDiscardCommand g).isSome)

/-- Apply the unique payment via `autopay` or `sacrifice`, and the `--output`
lines that record it. -/
def autoPayStep? (g : Game) (pending : List String) :
    Option (Except String (Game × Array String)) :=
  if !shouldAutoPay g pending then none
  else
    match uniqueSacrificeCommand g <|> uniqueDiscardCommand g with
    | some line =>
      let parts := line.splitOn " "
      some (applyInteractiveAsActor g (parts.headD "") (parts.drop 1) |>.map
        (fun g' => (g', #[line])))
    | none =>
      some (applyAutopayAsActor g [] |>.map (fun r => (r.game, r.commands)))

/-- Automatically pass only after scripted input is exhausted and priority
offers no other legal game-state action. -/
def shouldAutoPass (g : Game) (pending : List String) : Bool :=
  pending.isEmpty &&
    match g.actor with
    | some p => g.hasPriority p && !hasGameStatePriorityAction g p
    | none => false

/-- Automatically declare no attackers after scripted input is exhausted when
there are no creatures that can legally attack. -/
def shouldAutoNoAttack (g : Game) (pending : List String) : Bool :=
  pending.isEmpty && g.pending == .declareAttackers &&
    !(g.battlefield.any g.canAttack)

/-- Automatically declare no blockers after scripted input is exhausted when
that is the only legal declaration. -/
def shouldAutoNoBlock (g : Game) (pending : List String) : Bool :=
  pending.isEmpty && g.pending == .declareBlockers && !hasLegalBlock g

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

/-- Apply the unique legal target and the `--output` line that records it. -/
def autoTargetStep? (g : Game) (pending : List String) :
    Option (Except String (Game × String)) :=
  if !shouldAutoTarget g pending then none
  else
    match g.actor, soleLegalTarget? g with
    | some p, some t =>
      some (g.apply p (.target t) |>.map (fun g' => (g', targetCommand g p t)))
    | _, _ => some (.error "no actor or unique legal target")

/-- Shared REPL for `first <name>` / `decides <name>` prompts. -/
partial def promptUntilChosen (prompt helpText usage verb : String)
    (parse : List String → Except String Nat) (pending : List String)
    (output : Option IO.FS.Handle) (sameFile : Bool) :
    IO (Option (Nat × List String)) := do
  let mut pending := pending
  let mut chosen : Option Nat := none
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
      IO.println helpText
    | _ =>
      if cmd == verb then
        match parse (parts.drop 1) with
        | .error e => IO.println s!"! {e}"
        | .ok idx =>
          recordAcceptedCommand output sameFile fromInput line
          chosen := some idx
      else
        IO.println s!"! {usage}"
  match chosen with
  | some idx => return some (idx, pending)
  | none => return none

/-- Record accepted auto-step commands and reprint the updated game. -/
def recordAndRefresh (output : Option IO.FS.Handle) (sameFile : Bool)
    (g g' : Game) (seen : Nat) (playerView controlAll : Bool)
    (cmds : Array String) : IO Nat := do
  for line in cmds do
    recordAcceptedCommand output sameFile false line
  refreshAfterStep g g' seen (currentView g' playerView controlAll)

/-- Apply a unique automatic action and format the failure message. -/
def applyAutoAction (g : Game) (p : PlayerId) (action : Action)
    (failVerb : String) : Except String Game :=
  match g.apply p action with
  | .error e => .error s!"{(g.player p).name} could not automatically {failVerb}: {e}"
  | .ok g' => .ok g'

/-- CR 103.1: the deciding player chooses who takes the first turn. Returns
the seat index and remaining `--input` lines, or `none` if the user quits.
The chooser announcement is printed first by `printFirstChooser`. -/
partial def chooseStartingPlayer (seats : Array Seat) (decider : Nat)
    (controlAll : Bool) (pending : List String)
    (output : Option IO.FS.Handle) (sameFile : Bool := false) :
    IO (Option (Nat × List String)) :=
  let prompt :=
    if controlAll then
      s!"mtg ({seats[decider]!.name})> "
    else
      "mtg> "
  promptUntilChosen prompt helpChooseFirst
    "Choose who takes the first turn (CR 103.1): first <name>"
    "first" (parseFirstPlayer seats) pending output sameFile

partial def interactiveLoop (g : Game) (startVisible : Bool := false)
    (controlAll : Bool := false) (pending : List String := [])
    (output : Option IO.FS.Handle := none) (sameFile : Bool := false) :
    IO Unit := do
  let mut g := g
  let mut seen := g.log.size
  let mut playerView := startVisible
  let mut lastActor : Option PlayerId := g.actor
  let mut pending := pending
  let mut passUntilGoals : Array PassUntilGoal := #[]
  let you : PlayerId := ⟨0⟩
  let youName := (g.player you).name
  IO.println (helpInteractive controlAll youName)
  while !g.over do
    -- Interactive: let the heuristic play every other seat until you must act.
    if !controlAll then
      while !g.over && g.pendingRandom?.isNone &&
          (match g.actor with | some p => p != you | none => false) do
        passUntilGoals := activePassUntilGoals g passUntilGoals
        if (resumablePassUntilGoal? g passUntilGoals).isSome then
          break
        let actorName :=
          match g.actor with
          | some p => (g.player p).name
          | none => "Agent"
        let actorId :=
          match g.actor with
          | some p => p
          | none => you
        let chosen :=
          match g.actor with
          | some p => Agent.choose g p
          | none => none
        if !isPassSequenceAction (chosen.getD .pass) then
          passUntilGoals := interruptPassUntilGoals passUntilGoals actorId
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
        IO.println s!"{actorDisplayName g} could not automatically target: {e}"
      | .ok (g', line) =>
        seen ← recordAndRefresh output sameFile g g' seen playerView controlAll #[line]
        g := g'
      continue
    if let some step := autoPayStep? g pending then
      match step with
      | .error e =>
        IO.println s!"{actorDisplayName g} could not automatically pay: {e}"
      | .ok (g', cmds) =>
        seen ← recordAndRefresh output sameFile g g' seen playerView controlAll cmds
        g := g'
      continue
    if shouldAutoNoAttack g pending then
      let some p := g.actor | continue
      match applyAutoAction g p (.declareAttackers #[]) "declare no attackers" with
      | .error e => IO.println e
      | .ok g' =>
        seen ← recordAndRefresh output sameFile g g' seen playerView controlAll #["noattack"]
        g := g'
      continue
    if shouldAutoNoBlock g pending then
      let some p := g.actor | continue
      match applyAutoAction g p (.declareBlockers #[]) "declare no blockers" with
      | .error e => IO.println e
      | .ok g' =>
        seen ← recordAndRefresh output sameFile g g' seen playerView controlAll #["noblock"]
        g := g'
      continue
    passUntilGoals := activePassUntilGoals g passUntilGoals
    match resumablePassUntilGoal? g passUntilGoals with
    | some goal =>
      match resumePassUntilGoal g goal with
      | .error e =>
        IO.println s!"! {e}"
        passUntilGoals := passUntilGoals.filter (fun existing => existing != goal)
      | .ok r =>
        if !r.commands.isEmpty then
          seen ← recordAndRefresh output sameFile g r.game seen playerView controlAll r.commands
          g := r.game
          continue
    | none => pure ()
    if shouldAutoPass g pending then
      let some p := g.actor | continue
      match applyAutoAction g p .pass "pass" with
      | .error e => IO.println e
      | .ok g' =>
        seen ← recordAndRefresh output sameFile g g' seen playerView controlAll #["pass"]
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
      match actingPlayer g with
      | .error e => IO.println s!"! {e}"
      | .ok actor =>
        let args := parts.drop 1
        let accept := otherPlayerHasPassUntilGoal passUntilGoals actor
        match applyLoggedAction g cmd args line accept with
        | .error e => IO.println s!"! {e}"
        | .ok (g', recorded) =>
          for rec in recorded do
            recordAcceptedCommand output sameFile fromInput rec
          seen ← refreshAfterStep g g' seen (currentView g' playerView controlAll)
          passUntilGoals := goalsAfterCommand g g' actor cmd args passUntilGoals
          g := g'
          if g.over then
            printState g (currentView g playerView controlAll)
  printResult g

/-- Heuristic game. When `--norandom` leaves a random event pending, the host
supplies the result from `--input` or the console. -/
partial def runAuto (g : Game) (fuel : Nat)
    (pending : List String := [])
    (output : Option IO.FS.Handle := none)
    (sameFile : Bool := false) : IO Unit := do
  let mut g := g
  let mut seen := g.log.size
  let mut remaining := fuel
  let mut pending := pending
  while remaining > 0 && !g.over do
    if g.pendingRandom?.isSome then
      IO.print "mtg> "
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
      | "help" =>
        IO.println (helpInteractive false)
      | "state" => printState g
      | _ =>
        match applyLoggedAction g cmd (parts.drop 1) line with
        | .error e => IO.println s!"! {e}"
        | .ok (g', recorded) =>
          for rec in recorded do
            recordAcceptedCommand output sameFile fromInput rec
          seen ← refreshAfterStep g g' seen
          g := g'
      continue
    remaining := remaining - 1
    match Agent.step g with
    | .error e =>
      IO.println s!"Agent stopped: {e}"
      break
    | .ok g' =>
      seen ← refreshAfterStep g g' seen
      g := g'
  printState g
  if g.result.isSome then
    printResult g
  else
    IO.println s!"Stopped after {fuel} actions (turn {g.turnNumber})."

/-- Parse a Hobbit Welcome Deck color name or letter. -/
def parseWelcomeDeck (token : String) : Except String Color :=
  match token.map Char.toLower with
  | "w" | "white" => .ok .white
  | "u" | "blue" => .ok .blue
  | "b" | "black" => .ok .black
  | "r" | "red" => .ok .red
  | "g" | "green" => .ok .green
  | _ => .error s!"Unknown Welcome Deck: {token} (white, blue, black, red, or green)"

/-- A path token: has an extension or a directory separator. -/
def looksLikeDeckFile (token : String) : Bool :=
  token.contains '.' || token.contains '/' || token.contains '\\'

/-- A Welcome Deck color, or a deck list file path. -/
def parseDemoDeck (token : String) : Except String DemoDeck :=
  match parseWelcomeDeck token with
  | .ok c => .ok (.welcome c)
  | .error _ =>
    if looksLikeDeckFile token then .ok (.file token)
    else
      .error s!"Unknown Welcome Deck: {token} (white, blue, black, red, or green, or a deck list file)"

structure DemoOptions where
  interactive : Bool
  multiplayer : Bool
  playerView : Bool
  norandom : Bool
  /-- Constructed play (CR 100.2a) when true; limited play (CR 100.2b) otherwise. -/
  constructed : Bool
  seed : UInt64
  fuel : Nat
  inputFile : Option String
  outputFile : Option String
  /-- Replay `--input` and require a finished legal game. -/
  check : Bool
  players : Array DemoPlayer
  /-- Seat who chooses who takes the first turn (CR 103.1). `none` is random. -/
  decides : Option Nat

/-- Raw flag values before player-name validation. `seed` / `fuel` are `none`
until those flags appear, so input-file flags can fill the defaults. -/
structure DemoFlagValues where
  interactive : Bool
  multiplayer : Bool
  playerView : Bool
  norandom : Bool
  constructed : Bool
  seed : Option UInt64
  fuel : Option Nat
  inputFile : Option String
  outputFile : Option String
  check : Bool
  names : Array String
  decks : Array DemoDeck
  decidesName : Option String
  /-- True when `--auto`, `--interactive`, or `--multiplayer` was given. -/
  modeSet : Bool

/-- Parse flag tokens without checking that `--input` / `--visible` have a mode. -/
def parseFlagList (args : List String) : Except String DemoFlagValues :=
  Id.run do
    let mut interactive := false
    let mut multiplayer := false
    let mut playerView := false
    let mut norandom := false
    let mut constructed := false
    let mut seed : Option UInt64 := none
    let mut fuel : Option Nat := none
    let mut inputFile : Option String := none
    let mut outputFile : Option String := none
    let mut check := false
    let mut names : Array String := #[]
    let mut decks : Array DemoDeck := #[]
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
      | "--norandom" :: xs =>
        norandom := true
        rest := xs
      | "--constructed" :: xs =>
        constructed := true
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
      | "--check" :: xs =>
        check := true
        rest := xs
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
      | "--deck" :: token :: xs =>
        if token.startsWith "--" then
          return .error "Missing Welcome Deck color or deck list file"
        else
          match parseDemoDeck token with
          | .error e => return .error e
          | .ok d =>
            decks := decks.push d
            rest := xs
      | "--deck" :: [] => return .error "Missing Welcome Deck color or deck list file"
      | x :: _ => return .error s!"Unknown argument: {x}"
      | [] => break
    return .ok {
      interactive := interactive
      multiplayer := multiplayer
      playerView := playerView
      norandom := norandom
      constructed := constructed
      seed := seed
      fuel := fuel
      inputFile := inputFile
      outputFile := outputFile
      check := check
      names := names
      decks := decks
      decidesName := decidesName
      modeSet := modeSet
    }

/-- Merge CLI flags with additional flags from `--input`. File flags override
mode, seed, fuel, players, and `--decides` when present. `--visible`,
`--norandom`, and `--constructed` are enabled if either side sets them.
`--input` / `--output` stay on the CLI. -/
def mergeFlagValues (cli file : DemoFlagValues) : DemoFlagValues :=
  {
    interactive := if file.modeSet then file.interactive else cli.interactive
    multiplayer := if file.modeSet then file.multiplayer else cli.multiplayer
    playerView := cli.playerView || file.playerView
    norandom := cli.norandom || file.norandom
    constructed := cli.constructed || file.constructed
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
    check := cli.check || file.check
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
  -- `--check` replays every player's commands, so it is multiplayer unless
  -- `--interactive` or `--multiplayer` already selected a mode.
  let interactive := if v.check && !v.interactive then true else v.interactive
  let multiplayer := if v.check && !v.interactive then true else v.multiplayer
  if v.check && v.inputFile.isNone then
    .error "--check requires --input"
  else if v.playerView && !interactive then
    .error "--visible requires --interactive or --multiplayer"
  else if v.inputFile.isSome && !interactive && !v.norandom then
    .error "--input requires --interactive or --multiplayer"
  else if v.outputFile.isSome && !interactive && !v.norandom then
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
          interactive := interactive
          multiplayer := multiplayer
          playerView := v.playerView
          norandom := v.norandom
          constructed := v.constructed
          seed := seed
          fuel := fuel
          inputFile := v.inputFile
          outputFile := v.outputFile
          check := v.check
          players := players
          decides := none
        }
      | some name =>
        match parsePlayerName (seatsFromPlayers players) name with
        | .error e => .error e
        | .ok i =>
          .ok {
            interactive := interactive
            multiplayer := multiplayer
            playerView := v.playerView
            norandom := v.norandom
            constructed := v.constructed
            seed := seed
            fuel := fuel
            inputFile := v.inputFile
            outputFile := v.outputFile
            check := v.check
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

/-- Start a demo game from an `--input` script and require that the
replay is a valid, complete game. -/
def checkCompleteGame (opt : DemoOptions) (seats : Array Seat) (commands : List String) :
    Except String Game := do
  let decider := assignDecider opt.players opt.seed opt.decides
  let humanChooses := humanChoosesFirst opt.interactive opt.multiplayer decider
  let (startIdx, rest) ← takeStartingPlayer seats humanChooses decider commands
  let g ← Start.start {
    seats
    format := demoFormat opt.constructed
    seed := opt.seed
    startingPlayer := some startIdx
    norandom := opt.norandom }
  replayCompleteGame g rest

/-- Usage for reporting who was chosen at random to decide (CR 103.1). -/
def decidesUsage (players : Array DemoPlayer) : String :=
  let names := String.intercalate " or " (players.toList.map (·.name))
  s!"usage: decides <name> ({names})"

def helpChooseDecider (players : Array DemoPlayer) : String :=
  s!"Commands:
  help                 Show this help
  decides <name>       Who was chosen at random to decide who takes the first turn
  quit                 Exit

{decidesUsage players}
"

def parseDecider (players : Array DemoPlayer) (tokens : List String) : Except String Nat :=
  match commandTokens tokens with
  | [name] => parsePlayerName (seatsFromPlayers players) name
  | _ => .error (decidesUsage players)

/-- `--norandom` without `--decides`: ask who the random CR 103.1 chooser was. -/
partial def chooseDecider (players : Array DemoPlayer) (pending : List String)
    (output : Option IO.FS.Handle) (sameFile : Bool := false) :
    IO (Option (Nat × List String)) := do
  IO.println "Who is chosen at random to decide who takes the first turn (CR 103.1)?"
  for p in players do
    IO.println s!"  decides {p.name}"
  IO.println ""
  promptUntilChosen "mtg> " (helpChooseDecider players) (decidesUsage players)
    "decides" (parseDecider players) pending output sameFile

def printUsageError (e : String) : IO UInt32 := do
  if e == "help" then
    IO.println usage
    return 0
  else
    IO.eprintln e
    IO.println usage
    return 1

/-- Replay `--input` and exit 0 only when it is a valid complete game. -/
def runCheck (opt : DemoOptions) (commands : List String) : IO UInt32 := do
  match (← loadSeats opt.players) with
  | .error e =>
    IO.eprintln e
    return 1
  | .ok seats =>
    match checkCompleteGame opt seats commands with
    | .error e =>
      IO.eprintln e
      return 1
    | .ok g =>
      IO.println (describeCheckResult g)
      return 0

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
        if opt.check then
          runCheck opt script.commands
        else
          let pending := script.commands
          let sameFile := sameInputOutput opt.inputFile opt.outputFile
          match (← openOutputFile opt.outputFile sameFile) with
          | .error e =>
            IO.eprintln e
            return 1
          | .ok output =>
            match (← loadSeats opt.players) with
            | .error e =>
              IO.eprintln e
              return 1
            | .ok seats =>
              recordInputFlags output sameFile script.flags
              printEngineBanner
              printDeckAssignments opt.players
              match (←
                if opt.norandom && opt.decides.isNone then
                  chooseDecider opt.players pending output sameFile
                else
                  pure (some (assignDecider opt.players opt.seed opt.decides, pending))) with
              | none => return 0
              | some (decider, pending) =>
                let humanChooses :=
                  humanChoosesFirst opt.interactive opt.multiplayer decider
                let atRandom := opt.decides.isNone
                printFirstChooser opt.players decider atRandom (!humanChooses)
                if opt.interactive then
                  match (←
                    if humanChooses then
                      chooseStartingPlayer seats decider
                        opt.multiplayer pending output sameFile
                    else
                      pure (some (decider, pending))) with
                  | none => return 0
                  | some (startIdx, pending) =>
                    let g ← startGame opt.seed (some startIdx) seats opt.norandom
                      opt.constructed
                    printOpening g (currentView g opt.playerView opt.multiplayer)
                    interactiveLoop g opt.playerView opt.multiplayer pending output sameFile
                    return 0
                else
                  let g ←
                    startDemo opt.seed (some decider) (seats := seats)
                      (norandom := opt.norandom)
                      (constructed := opt.constructed)
                  runAuto g opt.fuel pending output sameFile
                  return 0
