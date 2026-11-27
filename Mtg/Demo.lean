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
effective 6 November 2026.

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
      | some o => s!"  {o.id} {g.nameWithToken o}"
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
  | some (.orderInto ids dest _) =>
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

/-- Create the demo game and RNG after the starting player is known (CR 103.1). -/
def startGameWithRng (seed : UInt64) (startingPlayer : Option Nat := some 0)
    (seats : Array Seat := demoSeats) (norandom : Bool := false)
    (constructed : Bool := false) : IO (Game × Rng) := do
  match Start.startWithRng { seats, format := demoFormat constructed, seed, startingPlayer, norandom } with
  | .error e =>
    IO.eprintln s!"Failed to start game: {e}"
    throw (IO.userError e)
  | .ok (g, rng) => return (g, rng)

/-- Create the demo game after the starting player is known (CR 103.1). -/
def startGame (seed : UInt64) (startingPlayer : Option Nat := some 0)
    (seats : Array Seat := demoSeats) (norandom : Bool := false)
    (constructed : Bool := false) : IO Game :=
  (·.1) <$> startGameWithRng seed startingPlayer seats norandom constructed

/-- Print the opening log and board after the game has started. -/
def printOpening (g : Game) (viewer : Option PlayerId := none) : IO Unit := do
  let _ ← printLog g 0 viewer
  printState g viewer
  printPendingPrompt g

/-- Start a demo game, print the opening snapshot, and return the game and RNG. -/
def startDemoWithRng (seed : UInt64) (startingPlayer : Option Nat := some 0)
    (viewer : Option PlayerId := none)
    (seats : Array Seat := demoSeats) (norandom : Bool := false)
    (constructed : Bool := false) : IO (Game × Rng) := do
  let (g, rng) ← startGameWithRng seed startingPlayer seats norandom constructed
  printOpening g viewer
  return (g, rng)

/-- Start a demo game and print the opening snapshot. The starting player is
the seat chosen under CR 103.1. Banner, decks, and the chooser announcement
are printed first. -/
def startDemo (seed : UInt64) (startingPlayer : Option Nat := some 0)
    (viewer : Option PlayerId := none)
    (seats : Array Seat := demoSeats) (norandom : Bool := false)
    (constructed : Bool := false) : IO Game :=
  (·.1) <$> startDemoWithRng seed startingPlayer viewer seats norandom constructed

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
  cast <id> adventure  Cast an adventurer card as its Adventure (CR 716.3)
  cast <id> sneak <attacker>  Cast for the sneak cost, returning that unblocked attacker to hand
  cast <id> beam <creature>   Cast from graveyard for its beam me up cost, returning that creature to hand
  target <id|name|opponent> [n] ...  Announce every target of one “target” word together (CR 601.2c); n is damage when dividing (CR 601.2d)
  scry                 Finish scrying; keep looked-at cards on top
  scry top <id>...     Put listed cards on top (last = new top); rest go to the bottom
  scry bottom <id>...  Put listed cards on the bottom (first = new bottom); rest stay on top
  scry top <id>... bottom <id>...  Choose both piles and their orders (CR 701.22)
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
    g.resolveAttackDestination p none
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
      if pw.isOnBattlefield && g.isPlaneswalker pw then
        .ok (pw.controller.getD pw.owner, some id)
      else .error s!"{g.nameWithToken pw} is not a planeswalker on the battlefield"
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
      a.status.attacking && g.defendingPlayerOf a == defender)
    let mut unused := g.battlefield.filter (fun b =>
      g.isCreature b && g.controlledBy b defender && !b.status.tapped)
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
    acc.set! i {
      source := a.source
      toCreatures := a.toCreatures.push (tgt, amt)
      toPlayer := a.toPlayer }

/-- Add `amt` from `src` to the defending player. -/
def pushCombatPlayerAmount (acc : Array CreatureCombatAssignment) (src : ObjectId) (amt : Int) :
    Array CreatureCombatAssignment :=
  match acc.findIdx? (fun a => a.source == src) with
  | none => acc.push { source := src, toPlayer := amt }
  | some i =>
    let a := acc[i]!
    acc.set! i {
      source := a.source
      toCreatures := a.toCreatures
      toPlayer := a.toPlayer + amt }

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

/-- Put waiting triggered abilities on the stack in the listed order
(CR 603.3b), accepting 0-based trigger indices or `#<id>` source ids. -/
def applyStack (g : Game) (p : PlayerId) (tokens : List String) : Except String Game := do
  let toks := commandTokens tokens
  let ids ← parseObjectIds toks stackUsage
  let mine := g.waitingTriggersOf p
  let allPlainIndices :=
    !toks.any (·.startsWith "#") && ids.all (·.raw < mine.size)
  let order : Array Nat :=
    if allPlainIndices then ids.map (·.raw)
    else Id.run do
      let mut used : Array Nat := #[]
      let mut out : Array Nat := #[]
      for id in ids do
        let mut found : Option Nat := none
        for i in [0:mine.size] do
          if found.isNone && !used.contains i && mine[i]!.source.id == id then
            found := some i
        match found with
        | some i =>
          used := used.push i
          out := out.push i
        | none =>
          out := out.push mine.size
      return out
  g.apply p (.stackTriggers order)

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
    let hasPowerScaledAnyColor :=
      (g.activatedAbilitiesOf o).any fun ab =>
        ab.manaProduction?.any fun mp =>
          match mp.spec with
          | .oneOf .anyColor (.objectStat .power .this) => true
          | _ => false
    if hasPowerScaledAnyColor then
      match g.proposedSpell with
      | some prop =>
        some ((g.preferredManaType p o (g.manaAbilitiesOf o) prop.cost
          (spend := g.proposedManaSpend prop)).getD (.colored .green))
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
          throw s!"{g.nameWithToken o} cannot produce {m}"
        jobs := jobs.push (id, m)
      | none =>
        match defaultTapMana g p o with
        | none => throw s!"{g.nameWithToken o} has no mana ability"
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
printed activated ability; omit it to activate the first non-mana ability. -/
def applyActivate (g : Game) (p : PlayerId) (tokens : List String) : Except String Game := do
  match commandTokens tokens with
  | [arg] =>
    match parseObjectId? arg with
    | none => throw activateUsage
    | some id =>
      let o ← requireObject g id
      let abs := g.activatedAbilitiesOf o
      let idx := ((List.range abs.size).find? (fun i => !Game.isManaActivation abs[i]!)).getD 0
      g.apply p (.activate id idx)
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
      let hasSac := ((g.additionalChoiceCostFor? spell (g.baseCard spell)).getD #[]).any fun cs =>
        cs.items.any fun | .sacrifice .. => true | _ => false
      if hasSac then
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

/-- Begin casting the named spell (CR 601.2a), or its Adventure (CR 716.3).
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
  | [arg, "beam", creature] =>
    match parseObjectId? arg, parseObjectId? creature with
    | some id, some c => g.apply p (.castWithBeamMeUp id c)
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
            | some o => (g.name o).map Char.toLower == lower
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

/-- Finish a pending scry (CR 701.22). Bare `scry` keeps the looked-at cards
on top in their current order. `scry top <ids>` puts those cards on top
(last = new top) and the rest on the bottom in their current relative order.
`scry bottom <ids>` puts those cards on the bottom (first = new bottom) and
the rest stay on top in their current relative order. Both piles may be
listed to choose each order. -/
def applyScry (g : Game) (p : PlayerId) (tokens : List String) : Except String Game := do
  match g.pending with
  | .scry q n _ =>
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
  | .surveil .. => throw "You are surveilling, not scrying; use surveil (CR 701.25)"
  | _ => throw "Not time to scry (CR 701.22)"

def surveilUsage : String := "usage: surveil [top <id> ...] [graveyard <id> ...]"

/-- Finish a pending surveil (CR 701.25). Bare `surveil` keeps the looked-at
cards on top in their current order. `surveil graveyard <ids>` puts those
cards into the graveyard in that order and the rest stay on top in their
current relative order. `surveil top <ids>` keeps those cards on top
(last = new top) and puts the rest into the graveyard. Both piles may be
listed to choose each order. -/
def applySurveil (g : Game) (p : PlayerId) (tokens : List String) : Except String Game := do
  match g.pending with
  | .surveil q n _ =>
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
  | .scry .. => throw "You are scrying, not surveilling; use scry (CR 701.22)"
  | _ => throw "Not time to surveil (CR 701.25)"

def discardUsage : String := "usage: discard <id>"

/-- Discard the named card from hand, or with no id choose the discard option
of an additional cost (CR 601.2b). -/
def applyDiscard (g : Game) (p : PlayerId) (tokens : List String) : Except String Game :=
  match commandTokens tokens with
  | [] =>
    match g.pending, g.proposedSpell.bind (fun prop => g.findObject? prop.spellId) with
    | .chooseAdditionalCost _, some spell =>
      let hasDisc := ((g.additionalChoiceCostFor? spell (g.baseCard spell)).getD #[]).any fun cs =>
        cs.items.any fun | .discard .. => true | _ => false
      if hasDisc then
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
  (g.player p).manaPool.canPay prop.cost (spend := g.proposedManaSpend prop)

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
      | some (.activateManaAbility id abilityIdx mana #[]) =>
        let letters := String.join (mana.toList.map ManaType.letter)
        let cmd := s!"mana {id} {abilityIdx + 1} {letters}"
        let g ← applyManaAbility g p [toString id, toString (abilityIdx + 1), letters]
        applyAutopaySteps g p n (cmds.push cmd)
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
    | .payOrLetCounter _ _ _ =>
      g.apply p .payGeneric
    | .payWard _ _ cost _ =>
      let hasManaOption :=
        (cost.isManaOnly && cost.mana.includesManaPayment) ||
          cost.items.any fun
            | .or choices => choices.any fun ch => ch.isManaOnly && ch.mana.includesManaPayment
            | _ => false
      if hasManaOption then g.apply p .payGeneric else g.apply p .pay
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
    (goals : Array PassUntilGoal) (fuel : Nat)
    (norandom : Bool := false) (rng : Rng := Rng.ofSeed 1) : Except String Game :=
  match fuel with
  | 0 => .error "Could not finish replay"
  | n + 1 =>
    let (rng, g) := if norandom then (rng, g) else g.resolvePendingRandom rng
    let goals := activePassUntilGoals g goals
    if g.over then
      match commands with
      | [] => .ok g
      | line :: rest =>
        if isCheckSkipCommand ((line.splitOn " ").headD "") then
          replayCompleteGameGo g rest goals n norandom rng
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
        | .ok g' =>
          let (rng, g') := if norandom then (rng, g') else g'.resolvePendingRandom rng
          replayCompleteGameGo g' commands goals n norandom rng
      | none =>
        match commands with
        | [] => .error "Game is not complete"
        | line :: rest =>
          let cmd := (line.splitOn " ").headD ""
          let args := (line.splitOn " ").drop 1
          if isCheckSkipCommand cmd then
            replayCompleteGameGo g rest goals n norandom rng
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
                let (rng, g') := if norandom then (rng, g') else g'.resolvePendingRandom rng
                replayCompleteGameGo g' rest
                  (goalsAfterCommand g g' actor cmd args goals) n norandom rng

/-- Replay scripted game-state commands. Fails on an illegal command, leftover
commands after the game ends, `quit`, or an unfinished game. -/
def replayCompleteGame (g : Game) (commands : List String)
    (norandom : Bool := false) (rng : Rng := Rng.ofSeed 1) : Except String Game :=
  replayCompleteGameGo g commands #[] (commands.length * 8 + passUntilFuel) norandom rng

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

/-- Remove one symbol from `cost` using a single convoke (`colors? = some cols`)
or improvise (`colors? = none`) tap, returning all distinct single-symbol
reductions a player can achieve (CR 702.51a / 702.126a). -/
private def convokeImproviseStepCosts (cost : ManaCost) (colors? : Option ColorSet) :
    Array ManaCost := Id.run do
  let syms := cost.symbols
  let without (i : Nat) : Array ManaSymbol :=
    syms.extract 0 i ++ syms.extract (i + 1) syms.size
  let mut out : Array ManaCost := #[]
  if let some colors := colors? then
    let mut seenSyms : Array ManaSymbol := #[]
    for i in [0:syms.size] do
      let s := syms[i]!
      let matchesCol :=
        match s with
        | .colored c => colors.contains c
        | .hybrid a b => colors.contains a || colors.contains b
        | .twobrid c => colors.contains c
        | _ => false
      if matchesCol && !seenSyms.contains s then
        seenSyms := seenSyms.push s
        out := out.push { symbols := without i }
  if let some i := syms.findIdx? (fun | .generic n => n > 0 | _ => false) then
    if let .generic n := syms[i]! then
      let reduced : ManaCost :=
        if n == 1 then { symbols := without i }
        else { symbols := syms.set! i (.generic (n - 1)) }
      out := out.push reduced
  return out

/-- Whether `p` can pay `cost` for spell `spellObj` (`face`) using pool + plain
mana sources plus Convoke (untapped creatures, CR 702.51a) and/or Improvise
(untapped artifacts, CR 702.126a). -/
private partial def canPaySpellCostWithConvokeImprovise (g : Game) (p : PlayerId)
    (spellObj : GameObject) (face : CardDef) (cost : ManaCost)
    (fromHand : Bool := spellObj.zone == .hand p)
    (excludeIds : Array ObjectId := #[])
    (castFromZone : Option ZoneKind := none) : Bool :=
  if g.canPaySpellCostFromSources p spellObj cost
      (fromHand := fromHand) (excludeIds := excludeIds) (castFromZone := castFromZone) then
    true
  else
    let stackDummy : GameObject :=
      { spellObj with
        id := noSourceSentinelId
        zone := .stack
        controller := some p
        printed := face
        status :=
          if face.name == "" then { spellObj.status with faceDown := true }
          else { spellObj.status with faceDown := false } }
    let hasConvoke :=
      KeywordAbility.hasConvoke face.keywords ||
        KeywordAbility.hasConvoke (g.currentKeywords stackDummy)
    let hasImprovise := g.spellHasImprovise face p (spellObj? := some stackDummy)
    if !hasConvoke && !hasImprovise then false
    else
      let manaSrcIds : Array ObjectId := (g.manaSources p).map (·.1.id)
      let rawHelpers : Array (ObjectId × Option ColorSet × Bool) :=
        g.objects.filterMap fun o =>
          if o.isOnBattlefield && !o.status.tapped && !excludeIds.contains o.id &&
              g.controlledBy o p then
            let isConv := hasConvoke && g.isCreature o
            let isImp := hasImprovise && g.isArtifact o
            if isConv then some (o.id, some (g.colors o), manaSrcIds.contains o.id)
            else if isImp then some (o.id, none, manaSrcIds.contains o.id)
            else none
          else none
      if rawHelpers.isEmpty then false
      else
        -- Put constrained colored convokers first and pure-generic helpers last.
        let helperRank (h : ObjectId × Option ColorSet × Bool) : Nat :=
          match h.2.1 with
          | none => 100
          | some cs =>
            let n := Color.all.foldl (fun acc c => if cs.contains c then acc + 1 else acc) 0
            if n == 0 then 90 else n
        let helpers := rawHelpers.qsort (fun a b => helperRank a < helperRank b)
        let rec dfs (idx : Nat) (curCost : ManaCost) (curExcl : Array ObjectId)
            (budget : Nat) : Bool × Nat :=
          if g.canPaySpellCostFromSources p spellObj curCost
              (fromHand := fromHand) (excludeIds := curExcl) (castFromZone := castFromZone) then
            (true, budget)
          else if idx ≥ helpers.size || budget == 0 then
            (false, budget)
          else
            let (oid, cols?, isManaSrc) := helpers[idx]!
            let nextExcl := if isManaSrc then curExcl.push oid else curExcl
            let stepCosts := convokeImproviseStepCosts curCost cols?
            let (hitTap, remBudget) :=
              stepCosts.foldl (fun (found, b) c' =>
                if found || b == 0 then (found, b)
                else dfs (idx + 1) c' nextExcl (b - 1)) (false, budget)
            if hitTap || remBudget == 0 then (hitTap, remBudget)
            else if isManaSrc || stepCosts.isEmpty then
              dfs (idx + 1) curCost curExcl remBudget
            else (false, remBudget)
        let (hit, rem) := dfs 0 cost excludeIds 256
        hit || rem == 0

/-- Maximum generic cost reduction a legal target of spell `face` can provide
(mirroring `Casting.applyTargetCostReductions`, CR 601.2c,f). -/
private def maxSpellTargetGenericReduction (g : Game) (p : PlayerId) (o : GameObject)
    (face : CardDef) : Nat :=
  let tcs := g.evalLayer3 o
  let faceStatics :=
    if tcs.isEmpty then face.staticAbilities
    else HasTextChange.applyTextChanges tcs face.staticAbilities
  let hasTargetRed := faceStatics.any fun
    | .costModifier cond? .thisSpell (.reduceGeneric amt) =>
      cond?.any Condition.mentionsTarget || amt.mentionsTarget
    | _ => false
  if !hasTargetRed then 0
  else
    let tgts : Array Target :=
      if isModalSpellFace face then
        (effectiveSpellModes face).foldl (fun acc e =>
          let m := g.expandEachOpponentEffect p (if tcs.isEmpty then e else TextChange.applyEffect tcs e)
          if g.spellModeIsChoosable p m (some o.id) then
            acc ++ g.legalEffectTargets p m (some o.id)
          else acc) #[]
      else
        g.legalTargetsForFace p face none tcs (some o.id)
    tgts.foldl (fun best tgt =>
      match tgt with
      | .permanent _ =>
        let spellEnv : EvalEnv :=
          { controller := p
            sourceId := some o.id
            targetSlots := #[#[tgt]] }
        let red := faceStatics.foldl (fun acc ab =>
          match ab with
          | .costModifier cond? .thisSpell (.reduceGeneric amt) =>
            if (cond?.any Condition.mentionsTarget || amt.mentionsTarget) &&
                cond?.all (EvalExpr.evalCondition g spellEnv) then
              acc + (EvalExpr.evalValue g spellEnv amt).toNat
            else acc
          | _ => acc) 0
        max best red
      | _ => best) 0

/-- Maximum generic cost reduction a legal target of activated ability `ab` on `o`
can provide (`nActTarget + nEquip`, mirroring `Casting.applyTargetCostReductions`,
CR 602.2b / 601.2c,f). -/
private def maxAbilityTargetGenericReduction (g : Game) (p : PlayerId) (o : GameObject)
    (ab : ActivatedAbility) : Nat :=
  let targetReds := ab.costReductions.filter (·.mentionsTarget)
  let anyEquipTargetRed := g.battlefield.any fun perm =>
    (g.staticAbilities perm).any fun
      | .costModifier _ (.abilities _ _ _ (some _) none) (.reduceGeneric _) => true
      | _ => false
  if targetReds.isEmpty && !anyEquipTargetRed then 0
  else
    let legalTgts : Array Target :=
      if ab.isEquipWorthy && ab.effect.targetSpec == .creatureYouControl then
        g.legalTargetsForSpec p .worthyCreatureYouControl (some o.id)
      else
        match ab.equipSubtype? with
        | some t =>
          if ab.effect.targetSpec == .creatureYouControl then
            g.legalTargetsForSpec p (.creatureYouControlSubtype t) (some o.id)
          else
            ab.allModes.foldl (fun acc m =>
              if g.modeIsChoosable p m (some o.id) then
                acc ++ g.legalEffectTargets p (g.expandEachOpponentEffect p m) (some o.id)
              else acc) #[]
        | none =>
          ab.allModes.foldl (fun acc m =>
            if g.modeIsChoosable p m (some o.id) then
              acc ++ g.legalEffectTargets p (g.expandEachOpponentEffect p m) (some o.id)
            else acc) #[]
    legalTgts.foldl (fun best tgt =>
      match tgt with
      | .permanent oid =>
        match g.findObject? oid with
        | some tgtO =>
          let nActTarget :=
            if targetReds.isEmpty then 0
            else EvalExpr.evalActivationCostReductions g p (some o.id) targetReds #[tgt]
          let oEnv : EvalEnv :=
            { controller := (g.controllerOf tgtO).getD tgtO.owner, sourceId := some tgtO.id }
          let nEquip :=
            (g.staticAbilities tgtO).foldl (fun acc sab =>
              match sab with
              | .costModifier cond? (.abilities act tag? sc (some tgtPred) none) (.reduceGeneric amt) =>
                let tagOk := match tag? with
                  | none => true
                  | some t => ab.tag? == some t || (match t with | .equip _ => ab.isEquip | _ => false)
                let srcOk := EvalExpr.evalObjectPred g oEnv (.live o) sc.pred
                if tagOk && srcOk &&
                    EvalExpr.matchesPlayerFilter g oEnv act p &&
                    cond?.all (EvalExpr.evalCondition g oEnv) &&
                    EvalExpr.evalObjectPred g oEnv (.live tgtO) tgtPred then
                  acc + (EvalExpr.evalValue g oEnv amt).toNat
                else acc
              | _ => acc) 0
          max best (nActTarget + nEquip)
        | none => best
      | _ => best) 0

/-- Announced-additional-cost affordability helper for `hasGameStatePriorityAction`
accounting for Convoke/Improvise and target-dependent generic cost reductions. -/
private def canPayAnnouncedAdditionalForPriority (g : Game) (p : PlayerId)
    (spellObj : GameObject) (face : CardDef) (targetRed : Nat)
    (origPerm : Option PlayPermission := none)
    (explicitAltCost : Bool := false) (flashback : Option Bool := none)
    (fromHand : Bool := spellObj.zone == .hand p)
    (castFromZone : Option ZoneKind := none)
    (payObj : GameObject := spellObj) : Bool :=
  match g.additionalChoiceCostFor? spellObj face with
  | none => true
  | some branches =>
    let env : EvalEnv := { controller := p, sourceId := some spellObj.id }
    branches.any fun branch =>
      branch.items.all fun item =>
        match item with
        | .mana m =>
          let cost :=
            (g.playManaCost { spellObj with controller := some p } face m
              (origPerm := origPerm) (flashback := flashback)
              (explicitAltCost := explicitAltCost)
              (useImplicitPermissions := false)).reduceGeneric targetRed
          canPaySpellCostWithConvokeImprovise g p payObj face cost
            (fromHand := fromHand) (castFromZone := castFromZone)
        | .behold quality =>
          (g.permanentsOf p).any (fun perm => g.hasSubtype perm quality) ||
            (g.player p).hand.any (fun id =>
              id != spellObj.id &&
                (g.findObject? id).any (fun card => isDiscardableCard card && g.hasSubtype card quality))
        | .sacrifice _ (.filter pred) =>
          (g.permanentsOf p).any (fun perm =>
            perm.id != spellObj.id && EvalExpr.evalObjectPred g env (.live perm) pred)
        | .discard _ .hand =>
          (g.discardableHandIds p).any (fun id => id != spellObj.id)
        | .discard _ (.matching pred) =>
          (g.discardableHandIds p).any (fun id =>
            id != spellObj.id && (g.findObject? id).any (fun c => EvalExpr.evalObjectPred g env (.live c) pred))
        | _ => true

/-- Whether a player with priority has a legal action that affects the game
other than passing or conceding. Mana abilities count even when their mana
would not currently be useful, since tapping their source changes the game. -/
def hasGameStatePriorityAction (g : Game) (p : PlayerId) : Bool :=
  if !g.hasPriority p then false
  else
    let gyPlayable : Array GameObject :=
      (g.player p).graveyard.filterMap fun id =>
        (g.findObject? id).bind fun o => if g.mayPlayFromGraveyard p o then some o else none
    let libTopPlayable : Array GameObject :=
      match (g.player p).library.back?.bind g.findObject? with
      | some o => if g.mayPlayFromLibraryTop p o then #[o] else #[]
      | none => #[]
    let playable := g.handObjects p ++ g.exiledPlayable p ++ gyPlayable ++ libTopPlayable
    let canPlayLand :=
      g.canPlayLand p && playable.any (g.mayPlayLand p)
    let unblockedAttackers : Array GameObject :=
      if g.canCastForSneak p then
        g.objects.filter fun att =>
          att.isOnBattlefield && g.isCreature att && g.controlledBy att p &&
            att.status.attacking && !att.status.blocked
      else #[]
    let canCast := playable.any (fun o =>
      let rawFace := g.baseCard o
      let kwFace := { rawFace with keywords := g.currentKeywords o }
      let casterObj := { o with controller := some p }
      let frontOk :=
        g.canCastFrontFace p o &&
          (let targetRed := maxSpellTargetGenericReduction g p o rawFace
           let payOk (cost : ManaCost) (perm? : Option PlayPermission := none) : Bool :=
             canPaySpellCostWithConvokeImprovise g p o rawFace (cost.reduceGeneric targetRed)
               (fromHand := o.zone == .hand p) (castFromZone := some o.zone.kind) &&
               canPayAnnouncedAdditionalForPriority g p o rawFace targetRed (origPerm := perm?)
                 (fromHand := o.zone == .hand p) (castFromZone := some o.zone.kind)
           if o.zone == .exile then
             let perms := g.playPermissionsFor p o
             let nullPerm : Option PlayPermission :=
               if g.mayCastExiledBySource p o then some { player := p, anyMana := true } else none
             perms.any (fun pm =>
               (pm.ignoreTiming || g.timingAllowsCast p rawFace (card? := some o)) &&
                 (!pm.payLifeEqualManaValue || g.canPayLife p (g.objectManaValue o)) &&
                 payOk (g.playManaCost casterObj rawFace (origPerm := some pm)
                   (useImplicitPermissions := false)) (some pm)) ||
               ((perms.isEmpty || g.mayCastExiledBySource p o) &&
                 g.timingAllowsCast p rawFace (card? := some o) &&
                 payOk (g.playManaCost casterObj rawFace (origPerm := nullPerm)
                   (useImplicitPermissions := false)) nullPerm)
           else
             payOk (g.playManaCost casterObj rawFace (useImplicitPermissions := false)))
      let sneakOk :=
        if unblockedAttackers.isEmpty || g.splitSecondOnStack || g.combatLocksNonManaAbilities ||
            g.opponentsCantCastOnActiveTurn p || g.cantCastSpellsThisTurn p then
          false
        else
          match kwFace.sneakCost with
          | none => false
          | some sc =>
            let fromGy := o.zone == .graveyard o.owner
            let isFb := fromGy && (kwFace.flashback.isSome || g.flashbackUntilEot o)
            if isFb || !g.mayPlay p o || !g.graveyardCastThresholdMet p o.id rawFace then false
            else
              let sneakPerms : Array (Option PlayPermission) :=
                if o.zone == .exile then
                  let clean := (g.playPermissionsFor p o).filter fun pm =>
                    !pm.withoutManaCost && !pm.payLifeEqualManaValue &&
                      pm.prepareSource.all fun src =>
                        (g.findObject? src).any fun perm =>
                          perm.isOnBattlefield && perm.status.prepared && g.controlledBy perm p
                  let base := clean.map some
                  if g.mayCastExiledBySource p o then
                    base.push (some { player := p, anyMana := true })
                  else if base.isEmpty && (g.playPermissionsFor p o).isEmpty then #[none]
                  else base
                else #[none]
              let sneakFace := { rawFace with manaCost := sc }
              unblockedAttackers.any fun att =>
                sneakPerms.any fun perm? =>
                  (g.validateFrontFaceCast p o rawFace
                    (sneakCost := some sc) (sneakAttacker := some att.id)
                    (origPermOverride := perm?)).isOk &&
                    let gSneak := g.probeAfterSneakReturn p o.id att.id
                    let targetRed := maxSpellTargetGenericReduction gSneak p o sneakFace
                    let cost :=
                      (gSneak.playManaCost casterObj sneakFace (origPerm := perm?)
                        (flashback := some false) (explicitAltCost := true)
                        (useImplicitPermissions := false)).reduceGeneric targetRed
                    canPaySpellCostWithConvokeImprovise gSneak p o sneakFace cost
                      (fromHand := o.zone == .hand p) (castFromZone := some o.zone.kind) &&
                      canPayAnnouncedAdditionalForPriority gSneak p o sneakFace targetRed
                        (origPerm := perm?) (explicitAltCost := true) (flashback := some false)
                        (fromHand := o.zone == .hand p) (castFromZone := some o.zone.kind)
      let morphOk :=
        let preparedBlocksMorph :=
          o.zone == .exile &&
            ((g.playPermissionFor? p o (face? := some rawFace)).bind (·.prepareSource)).isSome &&
            g.canCastFrontFace p o
        kwFace.kicker.isNone && !preparedBlocksMorph && g.canCastMorphFaceDown p o &&
          let morphObj :=
            { o with
              id := noSourceSentinelId
              controller := some p
              printed := morphSpellFace
              adventurerCard := none
              status := { o.status with faceDown := true } }
          let targetRed := maxSpellTargetGenericReduction g p morphObj morphSpellFace
          let payMorph (perm? : Option PlayPermission) : Bool :=
            let cost :=
              (g.playManaCost morphObj morphSpellFace
                (origPerm := perm?) (flashback := some false)
                (explicitAltCost := true) (useImplicitPermissions := false)).reduceGeneric targetRed
            canPaySpellCostWithConvokeImprovise g p morphObj morphSpellFace cost
              (fromHand := o.zone == .hand p) (castFromZone := some o.zone.kind)
          if o.zone == .exile then
            let perms := g.playPermissionsFor p o
            let cleanPerms :=
              perms.filter fun pm =>
                !pm.withoutManaCost && !pm.payLifeEqualManaValue && pm.prepareSource.isNone &&
                  (pm.ignoreTiming || g.timingAllowsCast p morphSpellFace)
            let nullPerm : Option PlayPermission :=
              if g.mayCastExiledBySource p o then some { player := p, anyMana := true } else none
            cleanPerms.any (fun pm => payMorph (some pm)) ||
              ((perms.isEmpty || g.mayCastExiledBySource p o) &&
                g.timingAllowsCast p morphSpellFace && payMorph nullPerm)
          else
            payMorph none
      let impendingOk :=
        match kwFace.morph, kwFace.impending, kwFace.kicker with
        | none, some (_, alt), none =>
          let fromGraveyard := o.zone == .graveyard o.owner
          let isFlashbackCast := fromGraveyard && (kwFace.flashback.isSome || g.flashbackUntilEot o)
          let preparedBlocksImpending :=
            o.zone == .exile &&
              ((g.playPermissionFor? p o (face? := some rawFace)).bind (·.prepareSource)).isSome
          !isFlashbackCast && !preparedBlocksImpending && g.canCastFrontFace p o &&
            let impFace := { rawFace with manaCost := alt }
            let targetRed := maxSpellTargetGenericReduction g p o impFace
            let payImpending (perm? : Option PlayPermission) : Bool :=
              let cost :=
                (g.playManaCost casterObj impFace
                  (origPerm := perm?) (flashback := some false)
                  (explicitAltCost := true) (useImplicitPermissions := false)).reduceGeneric targetRed
              canPaySpellCostWithConvokeImprovise g p o impFace cost
                (fromHand := o.zone == .hand p) (castFromZone := some o.zone.kind) &&
                canPayAnnouncedAdditionalForPriority g p o impFace targetRed
                  (origPerm := perm?) (explicitAltCost := true) (flashback := some false)
                  (fromHand := o.zone == .hand p) (castFromZone := some o.zone.kind)
            let perms := g.playPermissionsFor p o
            let hasNullSummoner := o.zone == .exile && g.mayCastExiledBySource p o
            if perms.isEmpty && !hasNullSummoner then
              g.timingAllowsCast p impFace (card? := some o) && payImpending none
            else
              let cleanPerms :=
                perms.filter fun pm =>
                  !pm.withoutManaCost && !pm.payLifeEqualManaValue && pm.prepareSource.isNone &&
                    (pm.ignoreTiming || g.timingAllowsCast p impFace (card? := some o))
              let nullPerm : Option PlayPermission :=
                if hasNullSummoner then some { player := p, anyMana := true } else none
              cleanPerms.any (fun pm => payImpending (some pm)) ||
                (hasNullSummoner && g.timingAllowsCast p impFace (card? := some o) && payImpending nullPerm)
        | _, _, _ => false
      frontOk || sneakOk || morphOk || impendingOk)
    let canCastAdventure := playable.any (fun o =>
      g.canCastAdventure p o &&
        match (g.baseCard o).adventure with
        | some adv =>
          let face := adv.toCardDef
          let advObj :=
            { o with
              id := noSourceSentinelId
              controller := some p
              printed := face
              adventurerCard := some o.printed
              status := { o.status with faceDown := false } }
          let casterObj := { o with controller := some p }
          let targetRed := maxSpellTargetGenericReduction g p casterObj face
          let payAdv (cost : ManaCost) (perm? : Option PlayPermission := none) : Bool :=
            canPaySpellCostWithConvokeImprovise g p advObj face (cost.reduceGeneric targetRed)
              (fromHand := o.zone == .hand p) (castFromZone := some o.zone.kind) &&
              canPayAnnouncedAdditionalForPriority g p o face targetRed (origPerm := perm?)
                (fromHand := o.zone == .hand p) (castFromZone := some o.zone.kind)
                (payObj := advObj)
          if o.zone == .exile then
            let advPerms := (g.playPermissionsFor p o).filter (!·.fromAdventure)
            let nullPerm : Option PlayPermission :=
              if g.mayCastExiledBySource p o then some { player := p, anyMana := true } else none
            advPerms.any (fun pm =>
              (pm.ignoreTiming || g.timingAllowsCast p face (card? := some o)) &&
                (!pm.payLifeEqualManaValue || g.canPayLife p face.manaValue) &&
                payAdv (g.playManaCost casterObj face (origPerm := some pm)
                  (useImplicitPermissions := false)) (some pm)) ||
              ((advPerms.isEmpty || g.mayCastExiledBySource p o) &&
                g.timingAllowsCast p face (card? := some o) &&
                payAdv (g.playManaCost casterObj face (origPerm := nullPerm)
                  (useImplicitPermissions := false)) nullPerm)
          else
            payAdv (g.playManaCost casterObj face (useImplicitPermissions := false))
        | none => false)
    let canActivate := g.objects.any (fun o =>
      let abs := g.activatedAbilitiesOf o
      (List.range abs.size).any (fun idx =>
        let ab := abs[idx]!
        let isTurnFaceUp := o.status.faceDown && ab.isTurnFaceUp
        let rawManaCost := if isTurnFaceUp then ab.cost.mana else g.activationManaCost p ab (some o)
        let targetRed := if isTurnFaceUp then 0 else maxAbilityTargetGenericReduction g p o ab
        let manaCost := rawManaCost.reduceGeneric targetRed
        let excludeIds := if !isTurnFaceUp && ab.cost.tap then #[o.id] else #[]
        g.canActivate p o ab (idx? := some idx) &&
          g.canPayAbilityCostFromSources p o ab manaCost
            (isTurnFaceUp := isTurnFaceUp) (excludeIds := excludeIds)))
    canPlayLand || !(g.manaSources p).isEmpty || g.hasUsableNonPlainManaAbility p ||
      g.hasUsableZeroOutputTapManaAbility p || canCast || canCastAdventure || canActivate

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
    (sources : List (GameObject × Array ManaType))
    (spend : ManaSpend := {}) (prop? : Option ProposedSpell := none) : Bool :=
  g.canPayFromSources pool cost sources spend (prop? := prop?)

/-- Material spell-mana outcome tracked by `hasUniqueManaPayment`:
`SpellRiderSpec` riders, Treasure-spent, *Path of Ancestry* scry provenance,
and all `ManaSpentPred` / `ValueExpr.manaSpent` attributes (CR 106.6 / 614.1c). -/
structure SpellManaOutcome where
  cantBeCountered : Bool := false
  gainsHaste : Bool := false
  extraPlusOneCounters : Nat := 0
  fromTreasure : Bool := false
  ancestryScry : Bool := false
  /-- Tracked `ManaSpentPred.fromSource` source IDs that contributed mana. -/
  fromSources : Array ObjectId := #[]
  /-- Tracked `ManaSpentPred.ofColor` colors that were spent. -/
  spentColors : Array Color := #[]
  /-- Total mana units spent when `ManaSpentPred.amount` or `ValueExpr.manaSpent` matters. -/
  spentAmount : Nat := 0
  /-- Distinct colors spent when `ManaSpentPred.colorCount` matters. -/
  spentColorCount : Nat := 0
  /-- Tracked `ManaSpentPred.withRider` riders present in spent units. -/
  explicitRiders : Array SpellRiderSpec := #[]
deriving BEq, Repr, Inhabited

/-- Summary of which `ManaSpentPred` / `ValueExpr.manaSpent` attributes are
referenced by the proposed spell, live objects in active zones, or delayed
triggers (CR 106.6 / 400.7d). -/
structure ManaSpentInterest where
  fromTreasure : Bool := false
  fromSourceIds : Array ObjectId := #[]
  colors : Array Color := #[]
  anyAmount : Bool := false
  anyColorCount : Bool := false
  riders : Array SpellRiderSpec := #[]
deriving BEq, Repr, Inhabited

def ManaSpentInterest.isEmpty (i : ManaSpentInterest) : Bool :=
  !i.fromTreasure && i.fromSourceIds.isEmpty && i.colors.isEmpty &&
    !i.anyAmount && !i.anyColorCount && i.riders.isEmpty

private def pushUnique {α : Type} [BEq α] (xs : Array α) (x : α) : Array α :=
  if xs.contains x then xs else xs.push x

def ManaSpentInterest.merge (a b : ManaSpentInterest) : ManaSpentInterest :=
  { fromTreasure := a.fromTreasure || b.fromTreasure
    fromSourceIds := b.fromSourceIds.foldl pushUnique a.fromSourceIds
    colors := b.colors.foldl pushUnique a.colors
    anyAmount := a.anyAmount || b.anyAmount
    anyColorCount := a.anyColorCount || b.anyColorCount
    riders := b.riders.foldl pushUnique a.riders }

/-- Whether spending mana with a `.cantBeCountered` rider changes the outcome of
paying for `prop?` by granting `.uncounterableThisCast` (CR 106.6). -/
def cantBeCounteredRiderMatters (g : Game) (spend : ManaSpend)
    (prop? : Option ProposedSpell := none) : Bool :=
  spend.spell &&
    match prop? with
    | none => true
    | some prop =>
      prop.kind == .spell && !(g.findObject? prop.spellId).any g.uncounterableThisCast

/-- Whether spending mana with a creature-spell rider (`.gainsHaste` or
`.entersWithPlusOneCounters`) changes the outcome of paying for `prop?`
(CR 106.6 / 614.1c). -/
def creatureSpellRiderMatters (g : Game) (spend : ManaSpend)
    (prop? : Option ProposedSpell := none) : Bool :=
  spend.spell && spend.hasType .creature &&
    match prop? with
    | none => true
    | some prop =>
      prop.kind == .spell && (g.findObject? prop.spellId).any g.isCreature

private def manaSpentPredInterest (owner? : Option ObjectId) : ManaSpentPred → ManaSpentInterest
  | .fromTreasure => { fromTreasure := true }
  | .fromSource =>
    { fromSourceIds := match owner? with | some id => #[id] | none => #[] }
  | .ofColor c => { colors := #[c] }
  | .amount _ _ => { anyAmount := true }
  | .colorCount _ _ => { anyColorCount := true }
  | .withRider r => { riders := #[r] }

mutual
private partial def valExprInterest (owner? : Option ObjectId) : ValueExpr → ManaSpentInterest
  | .manaSpent oe => ManaSpentInterest.merge { anyAmount := true } (objExprInterest owner? oe)
  | .binary _ lhs rhs => ManaSpentInterest.merge (valExprInterest owner? lhs) (valExprInterest owner? rhs)
  | .objectStat _ oe
  | .counterCount _ oe
  | .aggregate _ _ oe
  | .basicLandTypeCount oe
  | .cardTypeCount oe
  | .subtypeCount _ oe
  | .colorCountAmong oe
  | .manaSymbols _ oe => objExprInterest owner? oe
  | .playerMetric _ who => playerExprInterest owner? who
  | .maxControlled who pred =>
    ManaSpentInterest.merge (playerFilterInterest owner? who) (objPredInterest owner? pred)
  | .const _ | .chosenX | .eventAmount | .stepMetric _ _ | .chosenNumberOnSource => {}

private partial def playerFilterInterest (owner? : Option ObjectId) (pf : PlayerFilter) :
    ManaSpentInterest :=
  playerPredInterest owner? pf.pred

private partial def playerPredInterest (owner? : Option ObjectId) : PlayerPred → ManaSpentInterest
  | .all ps | .anyOf ps => ps.foldl (fun acc p => acc.merge (playerPredInterest owner? p)) {}
  | .not p => playerPredInterest owner? p
  | .metric _ _ rhs => valExprInterest owner? rhs
  | .controls f minCnt =>
    ManaSpentInterest.merge (objFilterInterest owner? f) (valExprInterest owner? minCnt)
  | .matchesExpr who => playerExprInterest owner? who
  | .any | .hasDesignation _ | .isMonarch | .isActivePlayer | .isDefendingPlayer
  | .isSeat _ | .thatPlayer => {}

private partial def playerExprInterest (owner? : Option ObjectId) : PlayerExpr → ManaSpentInterest
  | .controllerOf oe | .ownerOf oe => objExprInterest owner? oe
  | .matching _ pred => playerPredInterest owner? pred
  | .chosenBy chooser _ filter =>
    ManaSpentInterest.merge (playerExprInterest owner? chooser) (playerFilterInterest owner? filter)
  | .you | .activePlayer | .defendingPlayer | .monarch | .target _
  | .triggerPlayer _ | .stepPlayers _ => {}

private partial def zoneOwnerInterest (owner? : Option ObjectId) : ZoneOwnerSpec → ManaSpentInterest
  | .any => {}
  | .matching pf => playerFilterInterest owner? pf
  | .ofPlayer who => playerExprInterest owner? who

private partial def zoneSetInterest (owner? : Option ObjectId) (zs : ZoneSetSpec) :
    ManaSpentInterest :=
  zoneOwnerInterest owner? zs.owner

private partial def objFilterInterest (owner? : Option ObjectId) (f : ObjectFilter) :
    ManaSpentInterest :=
  ManaSpentInterest.merge (zoneSetInterest owner? f.zones) (objPredInterest owner? f.pred)

private partial def combatRoleInterest (owner? : Option ObjectId) : CombatRolePred → ManaSpentInterest
  | .attackingPlayer who => playerExprInterest owner? who
  | .blockingObject att => objExprInterest owner? att
  | .attacking | .attackingAlone | .blocking | .blocked | .unblocked => {}

private partial def objOrPlayerInterest (owner? : Option ObjectId) :
    ObjectOrPlayerExpr → ManaSpentInterest
  | .object oe => objExprInterest owner? oe
  | .player who => playerExprInterest owner? who
  | .either oe who => ManaSpentInterest.merge (objExprInterest owner? oe) (playerExprInterest owner? who)

private partial def recipFilterInterest (owner? : Option ObjectId) :
    RecipientFilter → ManaSpentInterest
  | .player pf => playerFilterInterest owner? pf
  | .object f => objFilterInterest owner? f
  | .playerOrObject pf f =>
    ManaSpentInterest.merge (playerFilterInterest owner? pf) (objFilterInterest owner? f)
  | .any => {}

private partial def objExprInterest (owner? : Option ObjectId) : ObjectExpr → ManaSpentInterest
  | .topOfLibrary who cnt =>
    ManaSpentInterest.merge (playerExprInterest owner? who) (valExprInterest owner? cnt)
  | .inZones zs pred =>
    ManaSpentInterest.merge (zoneSetInterest owner? zs) (objPredInterest owner? pred)
  | .filter oe pred => ManaSpentInterest.merge (objExprInterest owner? oe) (objPredInterest owner? pred)
  | .extremum _ _ oe | .targetsOf oe | .linkedExile oe => objExprInterest owner? oe
  | .union oes => oes.foldl (fun acc oe => acc.merge (objExprInterest owner? oe)) {}
  | .diff a b => ManaSpentInterest.merge (objExprInterest owner? a) (objExprInterest owner? b)
  | .this | .target _ | .allTargets | .attachedHost | .triggerSubject
  | .stepObjects _ | .costPaidObjects => {}

private partial def objPredInterest (owner? : Option ObjectId) : ObjectPred → ManaSpentInterest
  | .all ps | .any ps => ps.foldl (fun acc p => acc.merge (objPredInterest owner? p)) {}
  | .not p => objPredInterest owner? p
  | .stat _ _ rhs | .counterCount _ _ rhs => valExprInterest owner? rhs
  | .combatRole role => combatRoleInterest owner? role
  | .controlledBy pf | .ownedBy pf => playerFilterInterest owner? pf
  | .attachedTo oe | .shares _ oe => objExprInterest owner? oe
  | .hasAttachment f => objFilterInterest owner? f
  | .targets tgt => objOrPlayerInterest owner? tgt
  | .dealtDamageThisTurn _ recip? _ => recip?.map (recipFilterInterest owner?) |>.getD {}
  | .receivedCounterThisTurn _ byP? => byP?.map (playerFilterInterest owner?) |>.getD {}
  | .hasType _ | .hasSupertype _ | .hasSubtype _ | .hasColor _ | .colorCount _ _
  | .named _ | .hasKeyword _ | .statParity _ _ | .isToken _ | .isFaceDown _ | .isCopy _
  | .isCommander | .isKind _ | .tapped _ | .phasedOut _ | .hasDesignation _
  | .sameAs _ | .otherThan _ | .wasCast | .castFrom _ | .enteredThisTurn
  | .attackedThisTurn | .wasDealtDamageThisTurn | .putIntoGraveyardFromBattlefieldThisTurn
  | .chosenAnchorIs _ => {}
end

private def countRangeInterest (owner? : Option ObjectId) : ExprCountRange → ManaSpentInterest
  | .exact n | .upTo n => valExprInterest owner? n
  | .between lo hi => ManaSpentInterest.merge (valExprInterest owner? lo) (valExprInterest owner? hi)
  | .anyNumber => {}

private def eventPatInterest (owner? : Option ObjectId) : EventPattern → ManaSpentInterest
  | .permanentEntered p | .permanentDied p _ | .permanentLeftBattlefield p
  | .attackedWith p _ | .castSpell p | .discardedCard p | .permanentReturnedToHand p =>
    objPredInterest owner? p
  | .drewCard _ | .milledCard _ | .gainedLife _ | .lostLife _
  | .dealtDamage _ _ | .activatedLoyalty | .beheld _ | .proliferated | .facedDilemma _ => {}

private def eventHistoryInterest (owner? : Option ObjectId) : EventHistoryPred → ManaSpentInterest
  | .scriedThisTurn who | .surveilledThisTurn who => playerFilterInterest owner? who
  | .eventOccurredThisTurn who pat | .eventOccurredLastTurn who pat =>
    ManaSpentInterest.merge (playerFilterInterest owner? who) (eventPatInterest owner? pat)
  | .firstResolutionThisTurn | .nthResolutionThisTurn _ | .optionalOnceUnusedThisTurn => {}

private def durInterest (owner? : Option ObjectId) : DurationExpr → ManaSpentInterest
  | .untilNextTurnOf who | .untilEndOfNextTurnOf who => playerExprInterest owner? who
  | .whileOnBattlefield oe | .untilLeavesBattlefield oe
  | .whileHasCounter oe _ | .whileInZone oe _ | .whileTapped oe => objExprInterest owner? oe
  | .untilEndOfTurn | .untilEndOfCombat | .untilEndOfStepOrPhase _
  | .untilStepOrPhase _ | .indefinite => {}

private partial def condInterest (owner? : Option ObjectId) : Condition → ManaSpentInterest
  | .castPred (.manaSpentMatches mp _) => manaSpentPredInterest owner? mp
  | .castPred _ => {}
  | .cmp _ lhs rhs => ManaSpentInterest.merge (valExprInterest owner? lhs) (valExprInterest owner? rhs)
  | .exists oe | .allShare oe _ => objExprInterest owner? oe
  | .forAll oe pred => ManaSpentInterest.merge (objExprInterest owner? oe) (objPredInterest owner? pred)
  | .playerPred who pred =>
    ManaSpentInterest.merge (playerExprInterest owner? who) (playerPredInterest owner? pred)
  | .turnHistory hp => eventHistoryInterest owner? hp
  | .all cs | .any cs => cs.foldl (fun acc c => acc.merge (condInterest owner? c)) {}
  | .not c => condInterest owner? c
  | .stepSucceeded _ | .duringStep _ | .duringPhase _ | .isYourTurn | .isNight => {}

private def costCountInterest (owner? : Option ObjectId) : CostCountSpec → ManaSpentInterest
  | .count n | .totalPowerAtLeast n | .totalManaValueAtLeast n
  | .totalManaSymbolsAtLeast _ n => valExprInterest owner? n
  | .anyNumber => {}

private def selfOrFilterInterest (owner? : Option ObjectId) : SelfOrFilter → ManaSpentInterest
  | .self => {}
  | .filter pred => objPredInterest owner? pred

private def discardTargetInterest (owner? : Option ObjectId) : DiscardCostTarget → ManaSpentInterest
  | .matching pred => objPredInterest owner? pred
  | .self | .hand | .random => {}

private def counterTargetInterest (owner? : Option ObjectId) : CounterCostTarget → ManaSpentInterest
  | .filter pred => objPredInterest owner? pred
  | .self | .payer => {}

mutual
private partial def costItemInterest (owner? : Option ObjectId) : CostItem → ManaSpentInterest
  | .tapObjects cnt f =>
    ManaSpentInterest.merge (costCountInterest owner? cnt) (objPredInterest owner? f)
  | .payLife amt | .waterbend amt => valExprInterest owner? amt
  | .sacrifice cnt what | .removeCounters cnt _ what | .returnToHand cnt what =>
    ManaSpentInterest.merge (costCountInterest owner? cnt) (selfOrFilterInterest owner? what)
  | .discard cnt what =>
    ManaSpentInterest.merge (costCountInterest owner? cnt) (discardTargetInterest owner? what)
  | .exile cnt zs what _ | .putOnLibrary cnt zs what _ =>
    (costCountInterest owner? cnt)
      |>.merge (zoneSetInterest owner? zs)
      |>.merge (selfOrFilterInterest owner? what)
  | .putCounters cnt _ tgt =>
    ManaSpentInterest.merge (valExprInterest owner? cnt) (counterTargetInterest owner? tgt)
  | .or choices => choices.foldl (fun acc c => acc.merge (costSpecInterest owner? c)) {}
  | .mana _ | .loyalty _ | .tapSelf | .untapSelf | .behold _ => {}

private partial def costSpecInterest (owner? : Option ObjectId) (cs : CostSpec) :
    ManaSpentInterest :=
  cs.items.foldl (fun acc item => acc.merge (costItemInterest owner? item)) {}
end

private def groupConstraintInterest (owner? : Option ObjectId) :
    GroupTargetConstraint → ManaSpentInterest
  | .totalManaValueAtMost cap => valExprInterest owner? cap
  | .shareCharacteristic _ | .distinctControllers | .distinctNames | .distinctCardTypes => {}

private def recipPredInterest (owner? : Option ObjectId) : RecipientPred → ManaSpentInterest
  | .filtered op pf =>
    ManaSpentInterest.merge (objPredInterest owner? op) (playerFilterInterest owner? pf)
  | .any | .otherThan _ => {}

private partial def targetDomainInterest (owner? : Option ObjectId) :
    TargetDomain → ManaSpentInterest
  | .object zs pred =>
    ManaSpentInterest.merge (zoneSetInterest owner? zs) (objPredInterest owner? pred)
  | .player pf => playerFilterInterest owner? pf
  | .anyTarget rp => recipPredInterest owner? rp
  | .stackAbility ctrl sp =>
    ManaSpentInterest.merge (playerFilterInterest owner? ctrl) (objPredInterest owner? sp)
  | .anyOf ds => ds.foldl (fun acc d => acc.merge (targetDomainInterest owner? d)) {}

private def targetSlotInterest (owner? : Option ObjectId) (s : TargetSlot) : ManaSpentInterest :=
  (targetDomainInterest owner? s.domain)
    |>.merge (s.division?.map (fun (_, v) => valExprInterest owner? v) |>.getD {})
    |>.merge (s.groupConstraint?.map (groupConstraintInterest owner?) |>.getD {})
    |>.merge (s.forEach?.map (playerFilterInterest owner?) |>.getD {})
    |>.merge (s.altDomainIf?.map (fun (c, d) =>
      ManaSpentInterest.merge (condInterest owner? c) (targetDomainInterest owner? d)) |>.getD {})

private def targetSpecInterest (owner? : Option ObjectId) (ts : TargetSpec) : ManaSpentInterest :=
  let sI := ts.slots.foldl (fun acc s => acc.merge (targetSlotInterest owner? s)) {}
  ts.crossSlotConstraints.foldl (fun acc c =>
    match c.relation with
    | .distinct => acc
    | .group gc => acc.merge (groupConstraintInterest owner? gc)) sI

private def qualityFilterInterest (owner? : Option ObjectId) : QualityFilter → ManaSpentInterest
  | .objectPred p => objPredInterest owner? p
  | .color _ | .cardType _ | .subtype _ | .multicolored => {}

private def protQualityInterest (owner? : Option ObjectId) : ProtectionQuality → ManaSpentInterest
  | .quality p => objPredInterest owner? p
  | .color _ | .cardType _ | .chosenCardType | .subtype _
  | .everything | .allColors | .colorless => {}

private def kwInterest (owner? : Option ObjectId) : KeywordAbility → ManaSpentInterest
  | .hexproof fq? => fq?.map (qualityFilterInterest owner?) |>.getD {}
  | .ward c | .kicker c | .flashback c | .morph c | .impending _ c | .sneak c | .beamMeUp c =>
    costSpecInterest owner? c
  | .protection pq => protQualityInterest owner? pq
  | .landwalk p => objPredInterest owner? p
  | .affinity f => objFilterInterest owner? f
  | .equip f c => ManaSpentInterest.merge (objPredInterest owner? f) (costSpecInterest owner? c)
  | .cycling f? c =>
    ManaSpentInterest.merge (f?.map (objPredInterest owner?) |>.getD {}) (costSpecInterest owner? c)
  | .simple .sunburst => { anyColorCount := true }
  | .simple _ | .toxic _ | .gift _ | .crew _ | .teamwork _ => {}

private def turnOwnerInterest (owner? : Option ObjectId) : TurnOwnerSpec → ManaSpentInterest
  | .player who => playerFilterInterest owner? who
  | .controllerOf oe => objExprInterest owner? oe

private def attackTargetInterest (owner? : Option ObjectId) : AttackTargetFilter → ManaSpentInterest
  | .any => {}
  | .player who | .playerOrPlaneswalker who => playerFilterInterest owner? who

private def targetSubjInterest (owner? : Option ObjectId) : TargetSubjectFilter → ManaSpentInterest
  | .object p => objPredInterest owner? p
  | .playerOrPermanent => {}

private def zoneEndpointInterest (owner? : Option ObjectId) : ZoneEndpointSpec → ManaSpentInterest
  | .inZones zs => zoneSetInterest owner? zs
  | .any | .notIn _ => {}

private partial def trigPatInterest (owner? : Option ObjectId) : TriggerPattern → ManaSpentInterest
  | .zoneChange subj fz tz _ act? =>
    (objPredInterest owner? subj)
      |>.merge (zoneEndpointInterest owner? fz)
      |>.merge (zoneEndpointInterest owner? tz)
      |>.merge (act?.map (playerFilterInterest owner?) |>.getD {})
  | .createTokens who tp =>
    ManaSpentInterest.merge (playerFilterInterest owner? who) (objPredInterest owner? tp)
  | .sacrifice who subj =>
    ManaSpentInterest.merge (playerFilterInterest owner? who) (objPredInterest owner? subj)
  | .drawCard who _ | .gainLife who | .loseLife who | .playerAction who _ =>
    playerFilterInterest owner? who
  | .discard who cp _ =>
    ManaSpentInterest.merge (playerFilterInterest owner? who) (objPredInterest owner? cp)
  | .becomesTapped subj _ _ _ | .becomesUntapped subj | .phasesOut subj
  | .blocks subj | .becomesBlocked subj | .spellCountered subj
  | .stackObjectResolves subj _ | .abilityTriggers subj =>
    objPredInterest owner? subj
  | .becomesUnattached att host =>
    ManaSpentInterest.merge (objPredInterest owner? att) (objPredInterest owner? host)
  | .controlLost subj fc =>
    ManaSpentInterest.merge (objPredInterest owner? subj) (playerFilterInterest owner? fc)
  | .putCounters putter? _ subj =>
    ManaSpentInterest.merge (putter?.map (playerFilterInterest owner?) |>.getD {})
      (objPredInterest owner? subj)
  | .attacks att tgt _ _ _ _ =>
    ManaSpentInterest.merge (objPredInterest owner? att) (attackTargetInterest owner? tgt)
  | .damageDealt src recip _ _ _ =>
    ManaSpentInterest.merge (objPredInterest owner? src) (recipFilterInterest owner? recip)
  | .castSpell caster sp _ manaSpent? _ _ tgt? =>
    (playerFilterInterest owner? caster)
      |>.merge (objPredInterest owner? sp)
      |>.merge (manaSpent?.map (manaSpentPredInterest owner?) |>.getD {})
      |>.merge (tgt?.map (recipFilterInterest owner?) |>.getD {})
  | .activateAbility act src _ =>
    ManaSpentInterest.merge (playerFilterInterest owner? act) (objPredInterest owner? src)
  | .becomesTarget subj byC _ =>
    ManaSpentInterest.merge (targetSubjInterest owner? subj) (playerFilterInterest owner? byC)
  | .stepBegins _ whoseTurn => turnOwnerInterest owner? whoseTurn
  | .whenCond inner cond =>
    ManaSpentInterest.merge (trigPatInterest owner? inner) (condInterest owner? cond)
  | .or a b => ManaSpentInterest.merge (trigPatInterest owner? a) (trigPatInterest owner? b)

private def staticSubjInterest (owner? : Option ObjectId) : StaticSubject → ManaSpentInterest
  | .self => {}
  | .matching f => objFilterInterest owner? f

private def tagInterest (owner? : Option ObjectId) : ActivationMechanicTag → ManaSpentInterest
  | .equip (some p) => objPredInterest owner? p
  | .equip none | .cycling _ | .boast | .powerUp | .exhaust | .crew _ | .station => {}

private def staticPlayerRuleInterest (owner? : Option ObjectId) :
    StaticPlayerRule → ManaSpentInterest
  | .maxHandSize w _ | .additionalLands w _ | .cantGainLife w
  | .cantLoseGame w | .cantWinGame w | .lifeTotalCantChange w
  | .gainDesignation w _ | .controlPlayer w
  | .dontLoseForZeroLife w | .cantAttack w => playerFilterInterest owner? w
  | .cantSacrifice w p =>
    ManaSpentInterest.merge (playerFilterInterest owner? w) (objPredInterest owner? p)
  | .hexproof w fq? =>
    ManaSpentInterest.merge (playerFilterInterest owner? w)
      (fq?.map (qualityFilterInterest owner?) |>.getD {})
  | .protectionFrom w q =>
    ManaSpentInterest.merge (playerFilterInterest owner? w) (protQualityInterest owner? q)
  | .cantCastSpells w sp =>
    ManaSpentInterest.merge (playerFilterInterest owner? w) (objPredInterest owner? sp)
  | .activateAsThoughHaste w sc =>
    ManaSpentInterest.merge (playerFilterInterest owner? w) (objFilterInterest owner? sc)
  | .extraAbilityActivation tag sc _ =>
    ManaSpentInterest.merge (tagInterest owner? tag) (objFilterInterest owner? sc)
  | .forbidAbilityActivation w tag =>
    ManaSpentInterest.merge (playerFilterInterest owner? w) (tagInterest owner? tag)

private def staticPlayRuleInterest (owner? : Option ObjectId) : StaticPlayRule → ManaSpentInterest
  | .lookAtTopOfLibrary w => playerFilterInterest owner? w
  | .mayPlayFrom w _ p _ _ _ _ _ _ _ _ | .castAsThoughFlash w p _ _
  | .nextSpellCantBeCountered w p | .activateLoyaltyAsInstant w p =>
    ManaSpentInterest.merge (playerFilterInterest owner? w) (objPredInterest owner? p)
  | .spellCantBeCountered p? => p?.map (objPredInterest owner?) |>.getD {}
  | .castRestriction c => condInterest owner? c
  | .mayBeginOnBattlefield | .canBeCommander => {}

private def staticCombatRuleInterest (owner? : Option ObjectId) :
    StaticCombatRule → ManaSpentInterest
  | .cantAttack s | .cantAttackAlone s | .attacksEachCombatIfAble s | .attackDespiteDefender s
  | .maxAttackersPerPermanent s _ | .cantBeBlocked s
  | .minBlockers s _ | .maxBlockers s _ | .assignNegativePowerAsPositive s =>
    staticSubjInterest owner? s
  | .cantAttackUnless s c =>
    ManaSpentInterest.merge (staticSubjInterest owner? s) (condInterest owner? c)
  | .attackTax ap df cs =>
    (objPredInterest owner? ap)
      |>.merge (playerFilterInterest owner? df)
      |>.merge (costSpecInterest owner? cs)
  | .attackPlaneswalkerTax ap pp cs =>
    (objPredInterest owner? ap)
      |>.merge (objPredInterest owner? pp)
      |>.merge (costSpecInterest owner? cs)
  | .cantAttackPlayer ap df pw? =>
    (objPredInterest owner? ap)
      |>.merge (playerFilterInterest owner? df)
      |>.merge (pw?.map (objPredInterest owner?) |>.getD {})
  | .cantBlock s c? =>
    ManaSpentInterest.merge (staticSubjInterest owner? s) (c?.map (condInterest owner?) |>.getD {})
  | .cantBlockMatching bp ap =>
    ManaSpentInterest.merge (objPredInterest owner? bp) (objPredInterest owner? ap)
  | .cantBeBlockedBy s bp =>
    ManaSpentInterest.merge (staticSubjInterest owner? s) (objPredInterest owner? bp)
  | .assignCombatDamageByToughness sc _ => objFilterInterest owner? sc

private def staticTriggerRuleInterest (owner? : Option ObjectId) :
    StaticTriggerRule → ManaSpentInterest
  | .extraTrigger sc _ ev? =>
    ManaSpentInterest.merge (objFilterInterest owner? sc)
      (ev?.map (eventPatInterest owner?) |>.getD {})
  | .suppressEnteringTriggers sc => objFilterInterest owner? sc

private def staticGameRuleInterest (owner? : Option ObjectId) : StaticGameRule → ManaSpentInterest
  | .doesntUntapDuringUntapStep s c? =>
    ManaSpentInterest.merge (staticSubjInterest owner? s) (c?.map (condInterest owner?) |>.getD {})
  | .cantBecomeUntapped s | .mayChooseNotToUntap s | .cantBeBeamedUp s =>
    staticSubjInterest owner? s
  | .cantBeTargetedBy s sp _ _ =>
    ManaSpentInterest.merge (staticSubjInterest owner? s) (objPredInterest owner? sp)
  | .lockNonManaDuringPhase _ w | .legendRuleDisabled w => playerFilterInterest owner? w
  | .planeswalkersSurviveZeroLoyalty sc | .cantHaveCountersPutOn sc _ | .cantPhaseIn sc =>
    objFilterInterest owner? sc

private def costTargetInterest (owner? : Option ObjectId) : CostTargetSpec → ManaSpentInterest
  | .thisSpell => {}
  | .spells caster pred _ _ _ =>
    ManaSpentInterest.merge (playerFilterInterest owner? caster) (objPredInterest owner? pred)
  | .abilities act tag? sc tgt? _ =>
    (playerFilterInterest owner? act)
      |>.merge (tag?.map (tagInterest owner?) |>.getD {})
      |>.merge (objFilterInterest owner? sc)
      |>.merge (tgt?.map (objPredInterest owner?) |>.getD {})

private def costModInterest (owner? : Option ObjectId) : CostModification → ManaSpentInterest
  | .reduceGeneric v | .increaseGeneric v => valExprInterest owner? v
  | .alternativeFree => {}

private partial def ruleModInterest (owner? : Option ObjectId) : RuleModification → ManaSpentInterest
  | .player r => staticPlayerRuleInterest owner? r
  | .play r => staticPlayRuleInterest owner? r
  | .combat r => staticCombatRuleInterest owner? r
  | .trigger r => staticTriggerRuleInterest owner? r
  | .game r => staticGameRuleInterest owner? r
  | .costMod tgt mod _ =>
    ManaSpentInterest.merge (costTargetInterest owner? tgt) (costModInterest owner? mod)
  | .all rules => rules.foldl (fun acc r => acc.merge (ruleModInterest owner? r)) {}

private def destOwnerInterest (owner? : Option ObjectId) : DestOwnerSpec → ManaSpentInterest
  | .player who => playerExprInterest owner? who
  | .controller | .owner => {}

private def destZoneInterest (owner? : Option ObjectId) : DestZoneSpec → ManaSpentInterest
  | .battlefield u | .hand u => destOwnerInterest owner? u
  | .library u pos _ =>
    let posI := match pos with | .fromTop off => valExprInterest owner? off | _ => {}
    ManaSpentInterest.merge (destOwnerInterest owner? u) posI
  | .graveyard | .exile => {}

private def grantPlayPermInterest (owner? : Option ObjectId) (gp : GrantPlayPermSpec) :
    ManaSpentInterest :=
  (durInterest owner? gp.duration)
    |>.merge (gp.maxTotalManaValue?.map (valExprInterest owner?) |>.getD {})
    |>.merge (gp.condition?.map (condInterest owner?) |>.getD {})
    |>.merge (gp.filter?.map (objPredInterest owner?) |>.getD {})

private def delayedReturnInterest (owner? : Option ObjectId) : DelayedReturnSpec → ManaSpentInterest
  | .immediately _ u | .atNextEndStep _ u | .returnThenExileAtEndStep _ u =>
    destOwnerInterest owner? u
  | .returnIfThenExileAtEndStep p _ u =>
    ManaSpentInterest.merge (objPredInterest owner? p) (destOwnerInterest owner? u)

private def moveChoiceInterest (owner? : Option ObjectId) (ch : MoveChoiceSpec) :
    ManaSpentInterest :=
  let chooserI := match ch.chooser with | .player w => playerExprInterest owner? w | _ => {}
  chooserI
    |>.merge (countRangeInterest owner? ch.count)
    |>.merge (ch.filter?.map (objPredInterest owner?) |>.getD {})
    |>.merge (ch.groupConstraint?.map (groupConstraintInterest owner?) |>.getD {})
    |>.merge (ch.unlessMatching?.map (objPredInterest owner?) |>.getD {})

private def moveModsInterest (owner? : Option ObjectId) (mods : MoveMods) : ManaSpentInterest :=
  let base :=
    (mods.attachTo?.map (objExprInterest owner?) |>.getD {})
      |>.merge (mods.delayedReturn?.map (delayedReturnInterest owner?) |>.getD {})
      |>.merge (mods.grantPlayPerm?.map (grantPlayPermInterest owner?) |>.getD {})
      |>.merge (mods.choice?.map (moveChoiceInterest owner?) |>.getD {})
  let withCnt := mods.enterCounters.foldl (fun acc (_, v) => acc.merge (valExprInterest owner? v)) base
  mods.enterKeywords.foldl (fun acc kw => acc.merge (kwInterest owner? kw)) withCnt

private def enterModsInterest (owner? : Option ObjectId) (mods : EnterMods) : ManaSpentInterest :=
  let delayedI :=
    match mods.delayedAction? with
    | some (.sacrificeAtEndStepUnless cond) => condInterest owner? cond
    | _ => {}
  let base :=
    (mods.attachTo?.map (objExprInterest owner?) |>.getD {})
      |>.merge delayedI
  let withCnt := mods.counters.foldl (fun acc (_, v) => acc.merge (valExprInterest owner? v)) base
  mods.grantKeywordsUntilEot.foldl (fun acc kw => acc.merge (kwInterest owner? kw)) withCnt

private def recipExprInterest (owner? : Option ObjectId) : RecipientExpr → ManaSpentInterest
  | .objects oe => objExprInterest owner? oe
  | .players who => playerExprInterest owner? who
  | .both oe who => ManaSpentInterest.merge (objExprInterest owner? oe) (playerExprInterest owner? who)
  | .targetSlot _ | .allTargets => {}

private def damageOpInterest (owner? : Option ObjectId) : DamageOp → ManaSpentInterest
  | .deal src to amt _ =>
    (objExprInterest owner? src)
      |>.merge (recipExprInterest owner? to)
      |>.merge (valExprInterest owner? amt)
  | .fight a b _ =>
    ManaSpentInterest.merge (objExprInterest owner? a) (objExprInterest owner? b)

private def lifeOpInterest (owner? : Option ObjectId) : LifeOp → ManaSpentInterest
  | .gain w a | .lose w a | .set w a =>
    ManaSpentInterest.merge (playerExprInterest owner? w) (valExprInterest owner? a)

private def counterModeInterest (owner? : Option ObjectId) : CounterModifyMode → ManaSpentInterest
  | .put _ cnt | .distribute _ cnt => valExprInterest owner? cnt
  | .remove _ cnt => countRangeInterest owner? cnt
  | .moveAll fromObj _ | .moveOne fromObj _
  | .copyFromLki fromObj | .copyMissingKeywords fromObj => objExprInterest owner? fromObj
  | .double _ | .putAnotherOfChosen => {}

private def permOpInterest (owner? : Option ObjectId) : PermanentOp → ManaSpentInterest
  | .modifyCounters mode oe ch? =>
    (counterModeInterest owner? mode)
      |>.merge (objExprInterest owner? oe)
      |>.merge (ch?.map (moveChoiceInterest owner?) |>.getD {})
  | .setTapped oe _ ch? | .assimilate oe ch? =>
    ManaSpentInterest.merge (objExprInterest owner? oe)
      (ch?.map (moveChoiceInterest owner?) |>.getD {})
  | .attach a b _ => ManaSpentInterest.merge (objExprInterest owner? a) (objExprInterest owner? b)
  | .phaseOut oe p? =>
    ManaSpentInterest.merge (objExprInterest owner? oe)
      (p?.map (playerExprInterest owner?) |>.getD {})
  | .transform oe | .turnFaceUp oe | .setDesignation oe _ _ => objExprInterest owner? oe

private def manaPaletteInterest (owner? : Option ObjectId) : ManaPoolPalette → ManaSpentInterest
  | .commanderColorIdentity who => playerExprInterest owner? who
  | .colorsAmong oe | .typesLandsCouldProduce oe => objExprInterest owner? oe
  | .explicit _ | .anyColor | .chosenColorOnSource => {}

private def manaProdInterest (owner? : Option ObjectId) (prod : ManaProductionSpec) :
    ManaSpentInterest :=
  match prod.spec with
  | .sequence items =>
    items.foldl (fun acc (_, v) => acc.merge (valExprInterest owner? v)) {}
  | .oneOf pal amt | .combination pal amt =>
    ManaSpentInterest.merge (manaPaletteInterest owner? pal) (valExprInterest owner? amt)
  | .colorAmong pal _ => manaPaletteInterest owner? pal

private def playerOpInterest (owner? : Option ObjectId) : PlayerOp → ManaSpentInterest
  | .drawCards w amt | .scry w amt | .surveil w amt | .amass w _ amt | .discover w amt =>
    ManaSpentInterest.merge (playerExprInterest owner? w) (valExprInterest owner? amt)
  | .empowerPlaneswalker _ amt => valExprInterest owner? amt
  | .proliferate w amt tgt? =>
    (playerExprInterest owner? w)
      |>.merge (valExprInterest owner? amt)
      |>.merge (tgt?.map (objExprInterest owner?) |>.getD {})
  | .addMana w prod =>
    ManaSpentInterest.merge (playerExprInterest owner? w) (manaProdInterest owner? prod)
  | .explore oe | .connive oe => objExprInterest owner? oe
  | .shuffle w | .temptWithRing w => playerExprInterest owner? w
  | .setStatus w _ cond? =>
    ManaSpentInterest.merge (playerExprInterest owner? w)
      (cond?.map (condInterest owner?) |>.getD {})
  | .choose w kind =>
    let kI := match kind with
      | .keyword ks => ks.foldl (fun acc kw => acc.merge (kwInterest owner? kw)) {}
      | .creatureType | .oddOrEven | .playerWithMostLife => {}
    ManaSpentInterest.merge (playerExprInterest owner? w) kI
  | .inspectLibrary spec =>
    let srcI := match spec.source with
      | .topCards w cnt _ | .millCards w cnt =>
        ManaSpentInterest.merge (playerExprInterest owner? w) (valExprInterest owner? cnt)
      | .revealUntil w pred cnt _ =>
        (playerExprInterest owner? w)
          |>.merge (objPredInterest owner? pred)
          |>.merge (valExprInterest owner? cnt)
      | .allButBottom w | .outsideTheGame w _ => playerExprInterest owner? w
    let actI := match spec.action with
      | .takeMatching pred cnt dest mods _ _ =>
        (objPredInterest owner? pred)
          |>.merge (countRangeInterest owner? cnt)
          |>.merge (destZoneInterest owner? dest)
          |>.merge (moveModsInterest owner? mods)
      | .splitIntoPiles sp ch _ d1 d2 _ =>
        (playerExprInterest owner? sp)
          |>.merge (playerExprInterest owner? ch)
          |>.merge (destZoneInterest owner? d1)
          |>.merge (destZoneInterest owner? d2)
      | .distributeEachOpponent dest mods | .moveAll dest mods =>
        ManaSpentInterest.merge (destZoneInterest owner? dest) (moveModsInterest owner? mods)
      | .none => {}
    (playerExprInterest owner? spec.chooser).merge srcI |>.merge actI
  | .searchLibrary spec =>
    let secI :=
      match spec.secondDest? with
      | none => {}
      | some (d2, m2) =>
        ManaSpentInterest.merge (destZoneInterest owner? d2) (moveModsInterest owner? m2)
    (playerExprInterest owner? spec.searcher)
      |>.merge (zoneSetInterest owner? spec.zones)
      |>.merge (objPredInterest owner? spec.filter)
      |>.merge (countRangeInterest owner? spec.count)
      |>.merge (spec.groupConstraint?.map (groupConstraintInterest owner?) |>.getD {})
      |>.merge (destZoneInterest owner? spec.dest)
      |>.merge (moveModsInterest owner? spec.mods)
      |>.merge secI
      |>.merge (spec.untapIf?.map (condInterest owner?) |>.getD {})
  | .reveal w oe cnt? =>
    (playerExprInterest owner? w)
      |>.merge (objExprInterest owner? oe)
      |>.merge (cnt?.map (countRangeInterest owner?) |>.getD {})

private def turnOpInterest (owner? : Option ObjectId) : TurnOp → ManaSpentInterest
  | .extraTurn w rule? =>
    ManaSpentInterest.merge (playerExprInterest owner? w)
      (rule?.map (ruleModInterest owner?) |>.getD {})
  | .extraPhase _ _ | .extraStep _ _ => {}

private def stackOpInterest (owner? : Option ObjectId) : StackOp → ManaSpentInterest
  | .counterStack oe _ _ | .chooseNewTargets oe _ => objExprInterest owner? oe
  | .copyStackObject oe copies _ =>
    ManaSpentInterest.merge (objExprInterest owner? oe) (valExprInterest owner? copies)
  | .mayCastOrPlay oe perm =>
    ManaSpentInterest.merge (objExprInterest owner? oe) (grantPlayPermInterest owner? perm)

private def forEachInterest (owner? : Option ObjectId) : ForEachSpec → ManaSpentInterest
  | .eachPlayer pf => playerFilterInterest owner? pf
  | .eachObject oe => objExprInterest owner? oe
  | .repeatTimes cnt => valExprInterest owner? cnt
  | .eachTargetSlot => {}

mutual
private partial def copyModInterest (owner? : Option ObjectId) :
    CopyModification → ManaSpentInterest
  | .addKeywords ks => ks.foldl (fun acc kw => acc.merge (kwInterest owner? kw)) {}
  | .addAbilities gas => gas.foldl (fun acc ga => acc.merge (grantedAbilityInterest owner? ga)) {}
  | .setName _ | .setBasePT _ _ | .addSupertypes _ | .addTypes _
  | .addSubtypes _ | .replaceCreatureSubtypes _ | .addColors _ | .removeSupertype _ => {}

private partial def tokenSpecInterest (owner? : Option ObjectId) : TokenSpec → ManaSpentInterest
  | .predefined _ => {}
  | .custom cs =>
    let base :=
      (cs.power?.map (valExprInterest owner?) |>.getD {})
        |>.merge (cs.toughness?.map (valExprInterest owner?) |>.getD {})
    let withKw := cs.keywords.foldl (fun acc kw => acc.merge (kwInterest owner? kw)) base
    cs.abilities.foldl (fun acc ga => acc.merge (grantedAbilityInterest owner? ga)) withKw
  | .copyOf oe cmods =>
    cmods.foldl (fun acc cm => acc.merge (copyModInterest owner? cm)) (objExprInterest owner? oe)

private partial def staticRepInterest (owner? : Option ObjectId) :
    StaticReplacementSpec → ManaSpentInterest
  | .entersTapped subj unlessCond? =>
    ManaSpentInterest.merge (staticSubjInterest owner? subj)
      (unlessCond?.map (condInterest owner?) |>.getD {})
  | .entersTappedUnlessPay cost => costSpecInterest owner? cost
  | .entersWithCounters subj _ cnt _ =>
    ManaSpentInterest.merge (staticSubjInterest owner? subj) (valExprInterest owner? cnt)
  | .asEntersMayCopy f dur mods _ =>
    let base := ManaSpentInterest.merge (objFilterInterest owner? f) (durInterest owner? dur)
    mods.foldl (fun acc cm => acc.merge (copyModInterest owner? cm)) base
  | .exileInsteadOfDying sc bt? =>
    ManaSpentInterest.merge (objFilterInterest owner? sc)
      (bt?.map (tokenSpecInterest owner?) |>.getD {})
  | .multiplyTokens who _ | .extraDraw who _ _ | .unspentManaBecomesColorless who =>
    playerFilterInterest owner? who
  | .extraTokenWith who tp tok _ | .replaceTokens who tp tok =>
    (playerFilterInterest owner? who)
      |>.merge (objPredInterest owner? tp)
      |>.merge (tokenSpecInterest owner? tok)
  | .extraDrawOnConnive who sc _ =>
    ManaSpentInterest.merge (playerFilterInterest owner? who) (objFilterInterest owner? sc)
  | .modifyCountersPut sc _ byP? _ _ =>
    ManaSpentInterest.merge (objFilterInterest owner? sc)
      (byP?.map (playerFilterInterest owner?) |>.getD {})
  | .preventDamage subj amt? =>
    ManaSpentInterest.merge (staticSubjInterest owner? subj)
      (amt?.map (valExprInterest owner?) |>.getD {})
  | .preventDamageToPlayer who amt? =>
    ManaSpentInterest.merge (playerFilterInterest owner? who)
      (amt?.map (valExprInterest owner?) |>.getD {})
  | .modifyDamage sc _ recip _ addAmt =>
    (objFilterInterest owner? sc)
      |>.merge (recipFilterInterest owner? recip)
      |>.merge (valExprInterest owner? addAmt)
  | .healOtherDamageWhenDealt subj => staticSubjInterest owner? subj
  | .entersUntapped sc | .entersTappedAndAttacking sc | .saveFromDestroyRemoveCounters sc _ =>
    objFilterInterest owner? sc
  | .all specs => specs.foldl (fun acc s => acc.merge (staticRepInterest owner? s)) {}
  | .entersWithDesignation _ | .asEntersChoose _
  | .exileOnLeaveStack | .entersTappedAndAttackingSameDefender => {}

private partial def contModInterest (owner? : Option ObjectId) :
    ContinuousModification → ManaSpentInterest
  | .grantKeywords ks | .loseKeywords ks =>
    ks.foldl (fun acc kw => acc.merge (kwInterest owner? kw)) {}
  | .grantActivated abs => abs.foldl (fun acc ab => acc.merge (actInterest owner? ab)) {}
  | .grantTriggered abs => abs.foldl (fun acc ab => acc.merge (trigInterest owner? ab)) {}
  | .grantStatic sas => sas.foldl (fun acc sa => acc.merge (staticInterest owner? sa)) {}
  | .copyActivatedFrom sc => objFilterInterest owner? sc
  | .setBasePT p? t? =>
    ManaSpentInterest.merge (p?.map (valExprInterest owner?) |>.getD {})
      (t?.map (valExprInterest owner?) |>.getD {})
  | .modifyPT p t => ManaSpentInterest.merge (valExprInterest owner? p) (valExprInterest owner? t)
  | .gainControl who => playerExprInterest owner? who
  | .exchangeControl oe => objExprInterest owner? oe
  | .becomeCopyOf oe mods =>
    mods.foldl (fun acc cm => acc.merge (copyModInterest owner? cm)) (objExprInterest owner? oe)
  | .applyRule rule => ruleModInterest owner? rule
  | .all mods => mods.foldl (fun acc m => acc.merge (contModInterest owner? m)) {}
  | .modifyTypes _ | .addAllCreatureTypes | .modifyColors _ | .loseAllAbilities => {}

private partial def staticInterest (owner? : Option ObjectId) : StaticAbility → ManaSpentInterest
  | .characteristicDefining (.setPT p? t?) =>
    ManaSpentInterest.merge (p?.map (valExprInterest owner?) |>.getD {})
      (t?.map (valExprInterest owner?) |>.getD {})
  | .characteristicDefining _ => {}
  | .continuous cond? sc mod =>
    (cond?.map (condInterest owner?) |>.getD {})
      |>.merge (objFilterInterest owner? sc)
      |>.merge (contModInterest owner? mod)
  | .ruleModifying cond? rule =>
    ManaSpentInterest.merge (cond?.map (condInterest owner?) |>.getD {})
      (ruleModInterest owner? rule)
  | .costModifier cond? appliesTo mod =>
    (cond?.map (condInterest owner?) |>.getD {})
      |>.merge (costTargetInterest owner? appliesTo)
      |>.merge (costModInterest owner? mod)
  | .replacement cond? spec =>
    ManaSpentInterest.merge (cond?.map (condInterest owner?) |>.getD {})
      (staticRepInterest owner? spec)
  | .enchantRestriction slot => targetSlotInterest owner? slot

private partial def effectInterest (owner? : Option ObjectId) (eff : Effect) : ManaSpentInterest :=
  ManaSpentInterest.merge (targetSpecInterest owner? eff.targets) (instrInterest owner? eff.body)

private partial def actInterest (owner? : Option ObjectId) (ab : ActivatedAbility) :
    ManaSpentInterest :=
  let base :=
    (costSpecInterest owner? ab.cost)
      |>.merge (effectInterest owner? ab.effect)
      |>.merge (ab.condition?.map (condInterest owner?) |>.getD {})
      |>.merge (ab.tag?.map (tagInterest owner?) |>.getD {})
  ab.costReductions.foldl (fun acc r =>
    acc
      |>.merge (valExprInterest owner? r.amount)
      |>.merge (r.condition?.map (condInterest owner?) |>.getD {})) base

private partial def trigInterest (owner? : Option ObjectId) (ab : TriggeredAbility) :
    ManaSpentInterest :=
  if ab.isManaSpentCastScry then {}
  else
    (trigPatInterest owner? ab.pattern)
      |>.merge (ab.interveningIf?.map (condInterest owner?) |>.getD {})
      |>.merge (effectInterest owner? ab.effect)

private partial def grantedAbilityInterest (owner? : Option ObjectId) :
    GrantedAbility → ManaSpentInterest
  | .keyword kw => kwInterest owner? kw
  | .activated ab => actInterest owner? ab
  | .triggered ab => trigInterest owner? ab
  | .static sa => staticInterest owner? sa

private partial def instrInterest (owner? : Option ObjectId) : Instruction → ManaSpentInterest
  | .noop => {}
  | .seq steps => steps.foldl (fun acc s => acc.merge (instrInterest owner? s)) {}
  | .bind _ step cont => ManaSpentInterest.merge (instrInterest owner? step) (instrInterest owner? cont)
  | .ifCond cond t e =>
    (condInterest owner? cond)
      |>.merge (instrInterest owner? t)
      |>.merge (instrInterest owner? e)
  | .optional who cost? y n _ =>
    (playerExprInterest owner? who)
      |>.merge (cost?.map (costSpecInterest owner?) |>.getD {})
      |>.merge (instrInterest owner? y)
      |>.merge (instrInterest owner? n)
  | .unlessPays payer cost u =>
    (playerExprInterest owner? payer)
      |>.merge (costSpecInterest owner? cost)
      |>.merge (instrInterest owner? u)
  | .chooseModes spec =>
    let base :=
      (valExprInterest owner? spec.minModes)
        |>.merge (valExprInterest owner? spec.maxModes)
        |>.merge (spec.altCountIf?.map (fun (c, lo, hi) =>
          (condInterest owner? c)
            |>.merge (valExprInterest owner? lo)
            |>.merge (valExprInterest owner? hi)) |>.getD {})
    spec.modes.foldl (fun acc m => acc.merge (effectInterest owner? m)) base
  | .forEach iter _ body =>
    ManaSpentInterest.merge (forEachInterest owner? iter) (instrInterest owner? body)
  | .queueReflexiveTrigger ab => trigInterest owner? ab
  | .installEffect op =>
    match op with
    | .applyContinuous dur oe mod =>
      (durInterest owner? dur)
        |>.merge (objExprInterest owner? oe)
        |>.merge (contModInterest owner? mod)
    | .applyRule dur rule =>
      ManaSpentInterest.merge (durInterest owner? dur) (ruleModInterest owner? rule)
    | .applyReplacement dur spec =>
      ManaSpentInterest.merge (durInterest owner? dur) (staticRepInterest owner? spec)
    | .createDelayedTrigger spec =>
      (trigPatInterest owner? spec.pattern)
        |>.merge (durInterest owner? spec.duration)
        |>.merge (spec.interveningIf?.map (condInterest owner?) |>.getD {})
        |>.merge (effectInterest owner? spec.effect)
  | .moveZone oe dest _ mods =>
    (objExprInterest owner? oe)
      |>.merge (destZoneInterest owner? dest)
      |>.merge (moveModsInterest owner? mods)
  | .create op =>
    match op with
    | .tokens who cnt spec mods =>
      (playerExprInterest owner? who)
        |>.merge (valExprInterest owner? cnt)
        |>.merge (tokenSpecInterest owner? spec)
        |>.merge (enterModsInterest owner? mods)
    | .emblem who emb =>
      let sI := emb.staticAbilities.foldl (fun acc sa => acc.merge (staticInterest owner? sa))
        (playerExprInterest owner? who)
      let tI := emb.triggeredAbilities.foldl (fun acc ab => acc.merge (trigInterest owner? ab)) sI
      emb.activatedAbilities.foldl (fun acc ab => acc.merge (actInterest owner? ab)) tI
  | .permanent op => permOpInterest owner? op
  | .damage op => damageOpInterest owner? op
  | .life op => lifeOpInterest owner? op
  | .player op => playerOpInterest owner? op
  | .turn op => turnOpInterest owner? op
  | .stack op => stackOpInterest owner? op
end

/-- Aggregate all `ManaSpentPred` and `ValueExpr.manaSpent` interests across the
proposed spell, all live objects in active zones (battlefield, command, stack,
hand, graveyard, exile, library), waiting triggers, and `g.delayedTriggers`
(CR 106.6 / 400.7d). -/
def spellManaSpentInterest (g : Game) (spend : ManaSpend)
    (prop? : Option ProposedSpell := none) : ManaSpentInterest :=
  if !spend.spell then {}
  else Id.run do
    let mut acc : ManaSpentInterest := {}
    let cardFaceInterest (oid : Option ObjectId) (cd : CardDef) : ManaSpentInterest := Id.run do
      let mut res : ManaSpentInterest := {}
      if let some sa := cd.spellAbility then
        res := res.merge (effectInterest oid sa.effect)
        for ac in sa.additionalCosts do
          res := res.merge (costSpecInterest oid ac.cost)
      for kw in cd.keywords do
        res := res.merge (kwInterest oid kw)
      for ab in cd.allActivatedAbilities do
        res := res.merge (actInterest oid ab)
      for ab in cd.triggeredAbilities do
        res := res.merge (trigInterest oid ab)
      for sa in cd.staticAbilities do
        res := res.merge (staticInterest oid sa)
      return res
    match prop? with
    | none =>
      acc := { acc with fromTreasure := true }
    | some prop =>
      if prop.kind != .spell then return {}
      if let some spell := g.findObject? prop.spellId then
        let bc := g.baseCard spell
        let oid := some spell.id
        if let some eff := g.currentSpellEffect spell then
          acc := acc.merge (effectInterest oid eff)
        else if isModalSpellFace bc then
          for m in g.evalSpellModes prop.caster spell do
            acc := acc.merge (effectInterest oid m)
        for ac in g.additionalCostsFor spell bc do
          acc := acc.merge (costSpecInterest oid ac.cost)
        for kw in bc.keywords do
          acc := acc.merge (kwInterest oid kw)
        for kw in g.currentKeywords spell do
          acc := acc.merge (kwInterest oid kw)
        for ab in bc.allActivatedAbilities do
          acc := acc.merge (actInterest oid ab)
        for ab in g.activatedAbilitiesOf spell do
          acc := acc.merge (actInterest oid ab)
        for ab in bc.triggeredAbilities do
          acc := acc.merge (trigInterest oid ab)
        for ab in g.triggeredAbilities spell do
          acc := acc.merge (trigInterest oid ab)
        for sa in bc.staticAbilities do
          acc := acc.merge (staticInterest oid sa)
        for sa in g.staticAbilities spell do
          acc := acc.merge (staticInterest oid sa)
        if let some back := bc.otherFace then
          acc := acc.merge (cardFaceInterest oid back)
    for o in g.objects do
      if !o.status.phasedOut then
        let oid := some o.id
        if o.isOnBattlefield || o.zone == .command then
          for kw in g.currentKeywords o do
            acc := acc.merge (kwInterest oid kw)
          for ab in g.activatedAbilitiesOf o do
            acc := acc.merge (actInterest oid ab)
          for ab in g.triggeredAbilities o do
            acc := acc.merge (trigInterest oid ab)
          for sa in g.staticAbilities o do
            acc := acc.merge (staticInterest oid sa)
        else
          let zk := o.zone.kind
          for ab in g.activatedAbilitiesOf o do
            if ab.activeZones.contains zk then
              acc := acc.merge (actInterest oid ab)
          for ab in (g.baseCard o).allActivatedAbilities do
            if ab.activeZones.contains zk then
              acc := acc.merge (actInterest oid ab)
          for ab in g.triggeredAbilities o do
            if ab.activeZones.contains zk then
              acc := acc.merge (trigInterest oid ab)
          for ab in (g.baseCard o).triggeredAbilities do
            if ab.activeZones.contains zk then
              acc := acc.merge (trigInterest oid ab)
          if o.zone == .stack then
            let srcOid := o.sourceId.orElse fun () => oid
            if let some eff := o.abilityEffect then
              acc := acc.merge (effectInterest srcOid eff)
            if let some tab := o.triggeredAbility then
              acc := acc.merge (trigInterest srcOid tab)
            if let some eff := g.currentSpellEffect o then
              acc := acc.merge (effectInterest oid eff)
            for kw in g.currentKeywords o do
              acc := acc.merge (kwInterest oid kw)
            for sa in g.staticAbilities o do
              acc := acc.merge (staticInterest oid sa)
    for w in g.waitingTriggers do
      let srcOid := some w.source.id
      acc := acc.merge (trigInterest srcOid w.ability)
      if let some eff := w.abilityEffect then
        acc := acc.merge (effectInterest srcOid eff)
    for dt in g.delayedTriggers do
      if let some instr := dt.instruction? then
        acc := acc.merge (instrInterest (dt.source.map (·.id)) instr)
    for (_, eff) in g.activeEffects do
      match eff with
      | .layered sc (.abilities add _) d =>
        if g.durationActive d then
          let srcOid? := match sc with | .objects #[oid] => some oid | _ => none
          for kw in add.keywords do
            acc := acc.merge (kwInterest srcOid? kw)
          for sa in add.staticAbilities do
            acc := acc.merge (staticInterest srcOid? sa)
          for ab in add.triggeredAbilities do
            acc := acc.merge (trigInterest srcOid? ab)
      | .layered sc (.copy card) d =>
        if g.durationActive d then
          let srcOid? := match sc with | .objects #[oid] => some oid | _ => none
          acc := acc.merge (cardFaceInterest srcOid? card)
          if let some back := card.otherFace then
            acc := acc.merge (cardFaceInterest srcOid? back)
      | _ => pure ()
    return acc

/-- Whether spending mana from a Treasure changes the outcome of paying for
`prop?` (CR 106.6 / 111.10a). -/
def treasureManaMatters (g : Game) (spend : ManaSpend)
    (prop? : Option ProposedSpell := none) : Bool :=
  (spellManaSpentInterest g spend prop?).fromTreasure

/-- Whether `srcId` has *Path of Ancestry*'s mana-spent scry trigger, delegating
to `Core.isAncestrySourceId` (CR 106.6 / 608.2h / 702.26d). -/
def isAncestrySourceId (g : Game) (srcId : ObjectId) : Bool :=
  g.isAncestrySourceId srcId

/-- Whether spending mana from a *Path of Ancestry* source changes the outcome
of paying for `prop?` by triggering its scry 1 (CR 106.6). -/
def ancestryManaMatters (g : Game) (spend : ManaSpend)
    (prop? : Option ProposedSpell := none) : Bool :=
  spend.spell && spend.hasType .creature &&
    match prop? with
    | none => true
    | some prop =>
      prop.kind == .spell &&
        match g.findObject? prop.spellId with
        | none => false
        | some spell =>
          let liveCmds := g.objects.filter (fun o => o.owner == prop.caster && o.isCommander)
          let cmdTypes :=
            if !liveCmds.isEmpty then
              liveCmds.foldl (fun acc o => acc ++ (g.subtypes o).filter CardSubtype.isCreatureType) #[]
            else
              (g.player prop.caster).commanderCreatureTypes
          g.isCreature spell &&
            !g.ancestryManaSpentOn spell.id &&
            (g.subtypes spell).any (fun sub => sub.isCreatureType && cmdTypes.contains sub)

/-- Material spell-mana outcome produced by spending `spentUnits` on `prop?`
(CR 106.6 / 614.1c). -/
def spellManaOutcome (g : Game) (spend : ManaSpend)
    (prop? : Option ProposedSpell) (spentUnits : Array ManaUnit) : SpellManaOutcome :=
  let interest := spellManaSpentInterest g spend prop?
  let cbcMatters := cantBeCounteredRiderMatters g spend prop?
  let crMatters := creatureSpellRiderMatters g spend prop?
  let trMatters := interest.fromTreasure
  let ancMatters := ancestryManaMatters g spend prop?
  let colorCount : Nat :=
    if !interest.anyColorCount then 0
    else
      (spentUnits.foldl (fun (acc : Array Color) u =>
        match u.mana with
        | .colored c => if acc.contains c then acc else acc.push c
        | .colorless => acc) #[]).size
  { cantBeCountered := cbcMatters && spentUnits.any (·.hasRider .cantBeCountered)
    gainsHaste := crMatters && spentUnits.any (·.hasRider .gainsHaste)
    extraPlusOneCounters :=
      if !crMatters then 0
      else
        spentUnits.foldl (fun acc u =>
          acc + u.allRiders.foldl (fun s r =>
            match r with
            | .entersWithPlusOneCounters n => s + n
            | _ => s) 0) 0
    fromTreasure := trMatters && spentUnits.any (·.fromTreasure)
    ancestryScry := ancMatters && spentUnits.any (fun u => u.source.any g.isAncestrySourceId)
    fromSources :=
      interest.fromSourceIds.filter (fun sid => spentUnits.any (·.source == some sid))
    spentColors :=
      interest.colors.filter (fun c => spentUnits.any (·.mana == .colored c))
    spentAmount := if interest.anyAmount then spentUnits.size else 0
    spentColorCount := colorCount
    explicitRiders :=
      interest.riders.filter (fun r => spentUnits.any (·.hasRider r)) }

/-- Whether activating non-plain mana ability `d` on `o` can change the material
spell-mana outcome relative to `outcome0` for `prop` (CR 106.6 / 614.1c). -/
def manaAbilityDefCanChangeOutcome (g : Game) (spend : ManaSpend)
    (prop : ProposedSpell) (o : GameObject) (d : ManaAbilityDef)
    (outcome0 : SpellManaOutcome) : Bool :=
  if d.extraEffect?.isSome || d.modeChoices.any (·.output?.isNone) then
    true
  else
  let interest := spellManaSpentInterest g spend (some prop)
  let cbcMatters := cantBeCounteredRiderMatters g spend (some prop)
  let crMatters := creatureSpellRiderMatters g spend (some prop)
  let ancMatters := ancestryManaMatters g spend (some prop)
  let hasTwobrid := prop.cost.symbols.any (fun | .twobrid _ => true | _ => false)
  let p := (g.controllerOf o).getD o.owner
  let spendsPoolMana := (g.manaAbilityEffectiveCost p o d).includesManaPayment
  let anyOutcomeMatters := cbcMatters || crMatters || ancMatters || !interest.isEmpty
  if spendsPoolMana && anyOutcomeMatters && !(g.player p).manaPool.units.isEmpty then
    true
  else
  let checkVariant (prodTypes : Array ManaType) (restr : Option ManaSpendRestriction)
      (riders : Array SpellRiderSpec) (srcId? : Option ObjectId) (isTr : Bool) : Bool :=
    !prodTypes.isEmpty && g.restrictionAllowsProposed restr prop &&
      let allRiders : Array SpellRiderSpec :=
        let fromRestr := match restr with | some r => r.riders | none => #[]
        riders.foldl (fun acc r => if acc.contains r then acc else acc.push r) fromRestr
      let hasCbc := allRiders.contains .cantBeCountered
      let hasHaste := allRiders.contains .gainsHaste
      let hasCounters := allRiders.any (fun | .entersWithPlusOneCounters n => n > 0 | _ => false)
      let isAnc := srcId?.any g.isAncestrySourceId
      let hasHybridOrTwobridDisplace :=
        prop.cost.symbols.any fun
          | .hybrid a b => prodTypes.contains (.colored a) || prodTypes.contains (.colored b)
          | .twobrid c => prodTypes.contains (.colored c)
          | _ => false
      let canDisplaceRiderTier :=
        restr.isSome || !allRiders.isEmpty || hasHybridOrTwobridDisplace || spendsPoolMana
      let addsAttr :=
        (hasCbc && !outcome0.cantBeCountered && cbcMatters) ||
        (hasHaste && !outcome0.gainsHaste && crMatters) ||
        (hasCounters && crMatters) ||
        (isTr && !outcome0.fromTreasure && interest.fromTreasure) ||
        (isAnc && !outcome0.ancestryScry && ancMatters) ||
        (srcId?.any (fun sid =>
          interest.fromSourceIds.contains sid && !outcome0.fromSources.contains sid)) ||
        interest.colors.any (fun c =>
          !outcome0.spentColors.contains c && prodTypes.contains (.colored c)) ||
        (interest.anyColorCount &&
          prodTypes.any (fun | .colored _ => true | .colorless => false)) ||
        (interest.anyAmount && hasTwobrid && hasHybridOrTwobridDisplace) ||
        interest.riders.any (fun r =>
          allRiders.contains r && !outcome0.explicitRiders.contains r)
      let displacesAttr :=
        prop.cost.includesManaPayment &&
          ((outcome0.cantBeCountered && !hasCbc && canDisplaceRiderTier) ||
           (outcome0.gainsHaste && !hasHaste && canDisplaceRiderTier) ||
           (outcome0.extraPlusOneCounters > 0 && !hasCounters && canDisplaceRiderTier) ||
           (outcome0.fromTreasure && !isTr && canDisplaceRiderTier) ||
           (outcome0.ancestryScry && !isAnc) ||
           outcome0.fromSources.any (fun sid => srcId? != some sid) ||
           outcome0.spentColors.any (fun c => prodTypes.any (· != .colored c)) ||
           (interest.anyColorCount && outcome0.spentColorCount > 0) ||
           (interest.anyAmount && hasTwobrid && (hasHybridOrTwobridDisplace || spendsPoolMana)) ||
           outcome0.explicitRiders.any (fun r =>
             !allRiders.contains r && canDisplaceRiderTier))
      addsAttr || displacesAttr
  let isTr := g.hasSubtype o .treasure
  let variants : Array (Array ManaType × Option ManaSpendRestriction × Array SpellRiderSpec) :=
    if d.modeChoices.isEmpty then
      #[(d.output.producibleTypes, d.restriction, d.riders)]
    else
      d.modeChoices.filterMap fun m =>
        m.output?.map fun out => (out.producibleTypes, m.restriction, m.riders)
  let mainFlips :=
    variants.any fun (pts, restr, riders) =>
      checkVariant pts restr riders (some o.id) isTr
  if mainFlips then true
  else
    let producesAny := variants.any (fun (pts, _, _) => !pts.isEmpty)
    if o.isOnBattlefield && g.hasSubtype o .mountain && d.tap && producesAny then
      (g.mountainExtraRedEntriesThisTurn p).any fun (n, src?) =>
        n > 0 && checkVariant #[.colored .red] none #[] src? false
    else false

/-- Compare two post-payment leftover `ManaPool`s as multisets of `ManaUnit`s
(CR 106.4 / 106.6). -/
private def sameLeftoverPool (a b : ManaPool) : Bool :=
  let ua := a.units
  let ub := b.units
  ua.size == ub.size &&
    ua.all (fun x => (ua.filter (· == x)).size == (ub.filter (· == x)).size)

/-- Enumerate plain `{T}` mana choices across all usable plain `{T}` abilities
on `o`, keeping up to `maxZeroReps` zero-requirement colored representatives per
ability (`0` retains all colors) so `ManaOutput.combination` / multi-mana
leftover differences and coexisting plain vs rider/restricted abilities on one
permanent are preserved without exponential branching. -/
private def plainTapChoicesForUniqueness (g : Game) (o : GameObject) (types : Array ManaType)
    (cost : ManaCost) (maxZeroReps : Nat) (prop? : Option ProposedSpell := none) :
    Array TapManaChoice :=
  let p := (g.controllerOf o).getD o.owner
  let defs := g.manaAbilityDefs o
  let activeProp? := prop? <|> g.proposedSpell
  let sinceIdx := (g.targetProposalCheckpoint?.map (·.eventsSize)).getD g.events.size
  let tapPrereqOk : Bool :=
    !o.status.tapped &&
      !(g.hasSummoningSickness o && !(g.isCreature o && g.activatesAsThoughHaste p)) &&
      (match activeProp? with
       | none => true
       | some prop =>
         !((prop.tapSource && prop.sourceId == some o.id &&
             !g.sourceTappedForCost o.id (some prop.spellId) sinceIdx) ||
           prop.teamworkCreatures.contains o.id))
  if !tapPrereqOk then
    g.tapChoicesForSource o types cost (prop? := prop?)
  else Id.run do
    let isTreasure := g.hasSubtype o .treasure
    let mut out : Array TapManaChoice := #[]
    for i in [0 : defs.size] do
      let d := defs[i]!
      if g.isPlainTapManaAbilityDef p o d && g.manaAbilityDefUsable p o d then
        let extraSample := g.extraMountainRedFromTap o #[.colorless]
        let spendOk :=
          match activeProp? with
          | none => true
          | some prop =>
            g.restrictionAllowsProposed d.restriction prop ||
              (!extraSample.isEmpty && g.restrictionAllowsProposed none prop)
        if spendOk then
          let dedupTs (ts : Array ManaType) : Array ManaType := Id.run do
            let allowed := ts.filter types.contains
            if maxZeroReps == 0 then return allowed
            let mut acc : Array ManaType := #[]
            let mut zeroCnt : Nat := 0
            for t in allowed do
              match t with
              | .colored c =>
                if cost.symbolsIncludingColor c == 0 then
                  if zeroCnt < maxZeroReps then
                    zeroCnt := zeroCnt + 1
                    acc := acc.push t
                else
                  acc := acc.push t
              | .colorless =>
                acc := acc.push t
            return acc
          let tuples : Array (Array ManaType) :=
            match d.output with
            | .fixed m =>
              if !m.isEmpty && m.any types.contains then #[m] else #[]
            | other => other.allChoices dedupTs
          for tup in tuples do
            if !tup.isEmpty then
              let extra := g.extraMountainRedUnitsFromTap o tup
              let dup :=
                out.any (fun ch =>
                  ch.baseAdded == tup && ch.extraRed == extra &&
                    ch.restriction == d.restriction && ch.riders == d.riders)
              if !dup then
                out := out.push {
                  abilityIdx := i
                  baseAdded := tup
                  extraRed := extra
                  restriction := d.restriction
                  riders := d.riders
                  source := some o.id
                  fromTreasure := isTreasure
                }
    return out

/-- Whether tapping one or more cost-preserving extra plain sources in
`allSources \ baseIds` alongside `minSubBlocks` on top of `initPool` can change
`SpellManaOutcome` away from `outcome0` (handling permuted `minSub` orders,
interleaved extra positions, and single-source / multi-source rider / Treasure /
*Path of Ancestry* additions or displacements; CR 106.6). -/
private partial def canExtraPlainSourcesChangeOutcome (g : Game) (initPool : ManaPool)
    (minSubBlocks : Array (Array ManaUnit)) (cost : ManaCost)
    (allSources : Array (GameObject × Array ManaType))
    (baseIds : Array ObjectId) (spend : ManaSpend)
    (prop? : Option (PlayerId × ProposedSpell)) (outcome0 : SpellManaOutcome) : Bool :=
  let activeProp? := prop?.map (·.2)
  let interest := spellManaSpentInterest g spend activeProp?
  let cbcMatters := cantBeCounteredRiderMatters g spend activeProp?
  let crMatters := creatureSpellRiderMatters g spend activeProp?
  let trMatters := interest.fromTreasure
  let ancMatters := ancestryManaMatters g spend activeProp?
  let extraEntries : Array (GameObject × Array TapManaChoice) :=
    allSources.filterMap fun (src, types) =>
      if baseIds.contains src.id then none
      else if !prop?.all (fun (p, prop) => g.tapPreservesPostManaCosts p prop (baseIds.push src.id)) then
        none
      else
        let cs := plainTapChoicesForUniqueness g src types cost 0 activeProp?
        if cs.isEmpty then none else some (src, cs)
  if extraEntries.isEmpty then false
  else
    let flips (extraBlocks : Array (Array ManaUnit)) : Bool :=
      let checkBlocks (blocks : Array (Array ManaUnit)) : Bool :=
        let units := blocks.foldl (fun acc blk => acc ++ blk) initPool.units
        match ({ units } : ManaPool).payUnits? cost spend with
        | some (_, spent) => spellManaOutcome g spend activeProp? spent != outcome0
        | none => false
      let testBaseWithSingleExtra (base : Array (Array ManaUnit)) (ex : Array ManaUnit) : Bool :=
        if base.isEmpty then checkBlocks #[ex]
        else
          let k := base.size
          (List.range (k + 1)).any fun pos =>
            checkBlocks (base.extract 0 pos ++ #[ex] ++ base.extract pos k)
      -- Deduplicated multiset-permutation DFS over `blocks`, calling `onPerm` on each distinct
      -- ordering. Fails closed (`true`) if `budget` is exhausted before all distinct orderings
      -- are checked so `hasUniqueManaPayment` never autopays across an unsampled order.
      let anyDistinctPermWithinBudget (blocks : Array (Array ManaUnit)) (budget : Nat)
          (onPerm : Array (Array ManaUnit) → Bool) : Bool :=
        let n := blocks.size
        let rec go (chosen : Array (Array ManaUnit)) (usedMask : Nat) (rem : Nat) : Bool × Nat :=
          if rem == 0 then
            (true, 0)
          else if chosen.size == n then
            (onPerm chosen, rem - 1)
          else Id.run do
            let mut r := rem
            let mut tried : Array (Array ManaUnit) := #[]
            for i in [0:n] do
              if !maskBit usedMask i then
                let blk := blocks[i]!
                if !tried.contains blk then
                  tried := tried.push blk
                  let (hit, r') := go (chosen.push blk) (usedMask ||| (1 <<< i)) r
                  if hit then return (true, r')
                  r := r'
            return (false, r)
        (go #[] 0 budget).1
      if extraBlocks.size == 1 then
        let ex := extraBlocks[0]!
        if minSubBlocks.size ≤ 1 then
          testBaseWithSingleExtra minSubBlocks ex
        else
          anyDistinctPermWithinBudget minSubBlocks 128 (fun base => testBaseWithSingleExtra base ex)
      else
        anyDistinctPermWithinBudget (minSubBlocks ++ extraBlocks) 128 checkBlocks
    -- 1. Fast exact single-source check (across `minSub` orders and interleaved slots).
    let singleFlips :=
      extraEntries.any fun (_, cs) => cs.any fun ch => flips #[(ch.applyToPool {}).units]
    if singleFlips then true
    else
      -- Choice helpers for greedy multi-source boost/displace passes.
      let choiceRiders (ch : TapManaChoice) : Array SpellRiderSpec :=
        let fromRestr := match ch.restriction with | some r => r.riders | none => #[]
        ch.riders.foldl (fun acc r => if acc.contains r then acc else acc.push r) fromRestr
      let choiceHasCbc (ch : TapManaChoice) : Bool := (choiceRiders ch).contains .cantBeCountered
      let choiceHasHaste (ch : TapManaChoice) : Bool := (choiceRiders ch).contains .gainsHaste
      let choiceHasCounters (ch : TapManaChoice) : Bool :=
        (choiceRiders ch).any (fun | .entersWithPlusOneCounters n => n > 0 | _ => false)
      let choiceHasSource (ch : TapManaChoice) (sid : ObjectId) : Bool :=
        ch.source == some sid || ch.extraRed.any (·.source == some sid)
      let choiceIsAnc (ch : TapManaChoice) : Bool :=
        ch.source.any g.isAncestrySourceId ||
          ch.extraRed.any (fun u => u.source.any g.isAncestrySourceId)
      let choiceHasColor (ch : TapManaChoice) (c : Color) : Bool :=
        ch.baseAdded.contains (.colored c) || ch.extraRed.any (·.mana == .colored c)
      let choiceHasColored (ch : TapManaChoice) : Bool :=
        ch.baseAdded.any (fun | .colored _ => true | .colorless => false) ||
          ch.extraRed.any (fun u => match u.mana with | .colored _ => true | .colorless => false)
      let manaOrderRank : ManaType → Nat
        | .colorless => 6
        | .colored .white => 5
        | .colored .blue => 4
        | .colored .black => 3
        | .colored .red => 2
        | .colored .green => 1
      let neededTypesInit : Array ManaType :=
        cost.symbols.foldl (fun acc sym =>
          match sym with
          | .colored c => acc.push (.colored c)
          | .colorless => acc.push .colorless
          | .hybrid a b => acc.push (.colored a) |>.push (.colored b)
          | .twobrid c => acc.push (.colored c)
          | .generic _ | .x => acc) #[]
      let greedyPass (keepChoice : TapManaChoice → Bool) : Bool := Id.run do
        let mut remNeeded := neededTypesInit
        let scoreChoice (ch : TapManaChoice) : Nat :=
          let restrScore :=
            match ch.restriction with
            | some r => if r.isNarrow then 4000 else 3000
            | none => 0
          let needHits :=
            ch.baseAdded.foldl (fun acc t => if remNeeded.contains t then acc + 1 else acc) 0
          let orderBonus :=
            ch.baseAdded.foldl (fun acc t => max acc (manaOrderRank t)) 0
          restrScore + needHits * 100 + ch.totalSize * 10 + orderBonus
        let mut cands : Array (Nat × GameObject × TapManaChoice) := #[]
        for (src, cs) in extraEntries do
          let mut best? : Option (Nat × TapManaChoice) := none
          for ch in cs do
            if keepChoice ch then
              let sc := scoreChoice ch
              match best? with
              | none => best? := some (sc, ch)
              | some (bestSc, _) => if sc > bestSc then best? := some (sc, ch)
          if let some (sc, ch) := best? then
            cands := cands.push (sc, src, ch)
        let sorted := cands.qsort (fun a b => a.1 > b.1)
        let mut extraBlocks : Array (Array ManaUnit) := #[]
        let mut usedIds := baseIds
        for (_, src, ch0) in sorted do
          let mut chosen := ch0
          if let some (_, cs) := extraEntries.find? (fun e => e.1.id == src.id) then
            let mut bestSc := scoreChoice ch0
            for ch in cs do
              if keepChoice ch then
                let sc := scoreChoice ch
                if sc > bestSc then
                  bestSc := sc
                  chosen := ch
          let nextIds := usedIds.push src.id
          if prop?.all (fun (p, prop) => g.tapPreservesPostManaCosts p prop nextIds) then
            usedIds := nextIds
            extraBlocks := extraBlocks.push (chosen.applyToPool {}).units
            for t in chosen.baseAdded do
              if let some idx := remNeeded.findIdx? (· == t) then
                remNeeded := remNeeded.eraseIdxIfInBounds idx
            if flips extraBlocks then
              return true
        return false
      let greedyFlips : Bool :=
        (outcome0.cantBeCountered && greedyPass (fun ch => !choiceHasCbc ch)) ||
        (outcome0.gainsHaste && greedyPass (fun ch => !choiceHasHaste ch)) ||
        (outcome0.extraPlusOneCounters > 0 && greedyPass (fun ch => !choiceHasCounters ch)) ||
        (outcome0.fromTreasure && greedyPass (fun ch => !ch.fromTreasure)) ||
        (outcome0.ancestryScry && greedyPass (fun ch => !choiceIsAnc ch)) ||
        (cbcMatters && !outcome0.cantBeCountered && greedyPass choiceHasCbc) ||
        (crMatters && !outcome0.gainsHaste && greedyPass choiceHasHaste) ||
        (crMatters && greedyPass choiceHasCounters) ||
        (trMatters && !outcome0.fromTreasure && greedyPass (fun ch => ch.fromTreasure)) ||
        (ancMatters && !outcome0.ancestryScry && greedyPass choiceIsAnc) ||
        interest.fromSourceIds.any (fun sid =>
          if outcome0.fromSources.contains sid then greedyPass (fun ch => !choiceHasSource ch sid)
          else greedyPass (fun ch => choiceHasSource ch sid)) ||
        interest.colors.any (fun c =>
          if outcome0.spentColors.contains c then greedyPass (fun ch => !choiceHasColor ch c)
          else greedyPass (fun ch => choiceHasColor ch c)) ||
        (interest.anyColorCount &&
          (greedyPass choiceHasColored ||
           greedyPass (fun ch => ch.baseAdded.contains .colorless) ||
           Color.all.any (fun c => greedyPass (fun ch => choiceHasColor ch c)))) ||
        (interest.anyAmount &&
          cost.symbols.any (fun | .twobrid _ => true | _ => false) &&
          cost.symbols.any (fun
            | .twobrid c => greedyPass (fun ch => choiceHasColor ch c)
            | .hybrid a b =>
              greedyPass (fun ch => choiceHasColor ch a) ||
                greedyPass (fun ch => choiceHasColor ch b)
            | _ => false)) ||
        interest.riders.any (fun r =>
          if outcome0.explicitRiders.contains r then
            greedyPass (fun ch => !(choiceRiders ch).contains r)
          else
            greedyPass (fun ch => (choiceRiders ch).contains r))
      if greedyFlips then true
      else
        -- 3. Bounded DFS over extra-source combinations for subtle multi-source interactions.
        let maxDepth := min extraEntries.size (max 2 cost.manaValue)
        let rec dfs (idx depth : Nat) (curExtra : Array (Array ManaUnit))
            (usedIds : Array ObjectId) (budget : Nat) : Bool × Nat :=
          if budget == 0 then (false, 0)
          else if depth ≥ maxDepth || idx ≥ extraEntries.size then (false, budget)
          else
            let (src, cs) := extraEntries[idx]!
            let nextIds := usedIds.push src.id
            let (hitTake, remBudget) :=
              if prop?.all (fun (p, prop) => g.tapPreservesPostManaCosts p prop nextIds) then
                cs.foldl (fun (found, b) ch =>
                  if found || b == 0 then (found, b)
                  else
                    let nextExtra := curExtra.push (ch.applyToPool {}).units
                    if flips nextExtra then (true, b - 1)
                    else dfs (idx + 1) (depth + 1) nextExtra nextIds (b - 1)) (false, budget)
              else (false, budget)
            if hitTake || remBudget == 0 then (hitTake, remBudget)
            else dfs (idx + 1) depth curExtra usedIds remBudget
        let (hit, remBudget) := dfs 0 0 #[] baseIds 256
        hit || remBudget == 0

/-- Whether tapping `minSub` in an alternative order can change either the
leftover `ManaPool` or `SpellManaOutcome` relative to `(left0, out0)` when
`blocks.size ≥ 2` and `!left0.units.isEmpty` (CR 106.4 / 106.6). -/
private partial def minSubOrderFlips (g : Game) (initPool : ManaPool)
    (blocks : Array (Array ManaUnit)) (cost : ManaCost) (spend : ManaSpend)
    (activeProp? : Option ProposedSpell) (left0 : ManaPool)
    (out0 : SpellManaOutcome) : Bool :=
  let testOrder (perm : Array (Array ManaUnit)) : Bool :=
    let u := perm.foldl (fun acc blk => acc ++ blk) initPool.units
    match ({ units := u } : ManaPool).payUnits? cost spend with
    | none => true
    | some (lp', su') =>
      let ro' := spellManaOutcome g spend activeProp? su'
      ro' != out0 || !sameLeftoverPool lp' left0
  let k := blocks.size
  if k < 2 || left0.units.isEmpty then false
  else if k ≤ 4 then
    let rec permSearch (chosen : Array (Array ManaUnit)) (usedMask : Nat) : Bool :=
      if chosen.size == k then
        testOrder chosen
      else
        (List.range k).any fun i =>
          if maskBit usedMask i then false
          else permSearch (chosen.push blocks[i]!) (usedMask ||| (1 <<< i))
    permSearch #[] 0
  else Id.run do
    if testOrder blocks.reverse then return true
    for j in [0:k] do
      let bj := blocks[j]!
      let rest := blocks.extract 0 j ++ blocks.extract (j + 1) k
      if j > 0 && testOrder (#[bj] ++ rest) then return true
      if j + 1 < k && testOrder (rest.push bj) then return true
    let mut swaps := 0
    for i in [0:k] do
      for j in [i + 1:k] do
        if blocks[i]! != blocks[j]! && swaps < 64 then
          swaps := swaps + 1
          let swapped := (blocks.set! i blocks[j]!).set! j blocks[i]!
          if testOrder swapped then return true
    return false

/-- Whether tapping `minSub` yields a single `(leftoverPool, spellManaOutcome)`
outcome across tap orders and choices, and no additional cost-preserving source
subset in `allSources` can change any material `SpellManaOutcome` attribute on
`cost` (CR 106.4 / 106.6 / 614.1c). -/
private partial def uniqueSubsetHasUniqueOutcome (g : Game) (pool : ManaPool) (cost : ManaCost)
    (allSources minSub : Array (GameObject × Array ManaType))
    (spend : ManaSpend := {})
    (prop? : Option (PlayerId × ProposedSpell) := none) : Bool :=
  let activeProp? := prop?.map (·.2)
  let interest := spellManaSpentInterest g spend activeProp?
  let anyOutcomeMatters :=
    cantBeCounteredRiderMatters g spend activeProp? ||
      creatureSpellRiderMatters g spend activeProp? ||
      ancestryManaMatters g spend activeProp? ||
      !interest.isEmpty
  let minSubIds := minSub.map (·.1.id)
  let hasExtraPlain : Bool :=
    allSources.any fun (src, _) =>
      !minSubIds.contains src.id &&
        prop?.all (fun (p, prop) => g.tapPreservesPostManaCosts p prop (minSubIds.push src.id))
  let needReps : Bool := anyOutcomeMatters && hasExtraPlain
  let minUnits := Game.minManaUnitsForCost cost
  let roughMaxAdded : Nat :=
    minSub.foldl (fun acc (src, types) =>
      let cs := plainTapChoicesForUniqueness g src types cost 1 activeProp?
      acc + cs.foldl (fun m (ch : TapManaChoice) => max m ch.totalSize) 0) 0
  let maxZeroReps : Nat :=
    if anyOutcomeMatters || !pool.units.isEmpty || pool.total + roughMaxAdded > minUnits then 0
    else 1
  let srcArr : Array (GameObject × Array TapManaChoice × Nat) := minSub.map fun (src, types) =>
    let cs := plainTapChoicesForUniqueness g src types cost maxZeroReps activeProp?
    let maxOut := cs.foldl (fun m (ch : TapManaChoice) => max m ch.totalSize) 0
    (src, cs, maxOut)
  let sufMax : Array Nat := Id.run do
    let mut out := Array.replicate (srcArr.size + 1) 0
    let mut i := srcArr.size
    while i > 0 do
      i := i - 1
      out := out.set! i (srcArr[i]!.2.2 + out[i + 1]!)
    return out
  let sameBlockSeq (a b : Array (Array ManaUnit)) : Bool :=
    a.size == b.size &&
      (List.range a.size).all fun i =>
        sameLeftoverPool { units := a[i]! } { units := b[i]! }
  let rec collect (curPool : ManaPool) (addedBlocks : Array (Array ManaUnit)) (idx : Nat)
      (outcomes : Array (ManaPool × SpellManaOutcome)) (repAdded : Array (Array (Array ManaUnit)))
      (repOverflow : Bool) (budget : Nat) :
      Array (ManaPool × SpellManaOutcome) × Array (Array (Array ManaUnit)) × Bool × Nat :=
    if outcomes.size ≥ 2 || repOverflow || budget == 0 then
      (outcomes, repAdded, repOverflow, budget)
    else if idx ≥ srcArr.size then
      match curPool.payUnits? cost spend with
      | none => (outcomes, repAdded, repOverflow, budget - 1)
      | some (leftPool, spentUnits) =>
        let rOut := spellManaOutcome g spend activeProp? spentUnits
        if addedBlocks.size ≥ 2 && !leftPool.units.isEmpty &&
            minSubOrderFlips g pool addedBlocks cost spend activeProp? leftPool rOut then
          (outcomes, repAdded, true, budget - 1)
        else
          let (repAdded, repOverflow) :=
            if !needReps || repAdded.any (fun a => sameBlockSeq a addedBlocks) then
              (repAdded, repOverflow)
            else if repAdded.size < 64 then
              (repAdded.push addedBlocks, repOverflow)
            else
              (repAdded, true)
          if outcomes.any (fun (lp, ro) => ro == rOut && sameLeftoverPool lp leftPool) then
            (outcomes, repAdded, repOverflow, budget - 1)
          else
            (outcomes.push (leftPool, rOut), repAdded, repOverflow, budget - 1)
    else if curPool.total + sufMax[idx]! < minUnits then
      (outcomes, repAdded, repOverflow, budget)
    else
      let (_, cs, _) := srcArr[idx]!
      cs.foldl (fun (acc, reps, ov, b) (ch : TapManaChoice) =>
        if acc.size ≥ 2 || ov || b == 0 then (acc, reps, ov, b)
        else
          let blk := (ch.applyToPool {}).units
          collect (ch.applyToPool curPool) (addedBlocks.push blk) (idx + 1) acc reps ov b)
        (outcomes, repAdded, repOverflow, budget)
  let (outcomes, repAdded, repOverflow, remBudget) := collect pool #[] 0 #[] #[] false 4096
  if remBudget == 0 || repOverflow then false
  else
    match outcomes with
    | #[(_, outcome0)] =>
      if !needReps then true
      else if repAdded.isEmpty then false
      else
        !repAdded.any fun minSubBlocks =>
          canExtraPlainSourcesChangeOutcome g pool minSubBlocks cost allSources minSubIds
            spend prop? outcome0
    | _ => false

/-- Unique source set that can pay when there are too many sources to
enumerate every subset. Recognizes a single sufficient source, or that
every source is required. -/
def uniquePayingSourceSetLarge (g : Game) (pool : ManaPool) (cost : ManaCost)
    (sources : Array (GameObject × Array ManaType))
    (spend : ManaSpend := {})
    (prop? : Option (PlayerId × ProposedSpell) := none) :
    Option (Array (GameObject × Array ManaType)) :=
  let subOk (sub : Array (GameObject × Array ManaType)) : Bool :=
    canPayTappingAll g pool cost sub.toList spend (prop? := prop?.map (·.2)) &&
      prop?.all (fun (p, prop) => g.tapPreservesPostManaCosts p prop (sub.map (·.1.id)))
  let anySubsetOk (sub : Array (GameObject × Array ManaType)) : Bool :=
    match prop? with
    | some (p, prop) =>
      g.hasCostPreservingPaymentSubset pool cost sub spend (some (p, prop))
    | none =>
      canPayTappingAll g pool cost sub.toList spend
  let checkOutcome (cand? : Option (Array (GameObject × Array ManaType))) :=
    cand?.filter (fun minSub =>
      uniqueSubsetHasUniqueOutcome g pool cost sources minSub spend prop?)
  Id.run do
    let mut singles : Array (Nat × (GameObject × Array ManaType)) := #[]
    for i in [0:sources.size] do
      let src := sources[i]!
      if subOk #[src] then
        singles := singles.push (i, src)
    if singles.size == 1 then
      let (idx, src) := singles[0]!
      let rest := sources.extract 0 idx ++ sources.extract (idx + 1) sources.size
      if !anySubsetOk rest then
        return checkOutcome (some #[src])
      else
        return none
    if singles.size > 1 then
      return none
    if !subOk sources then
      return none
    for i in [0:sources.size] do
      let rest := sources.extract 0 i ++ sources.extract (i + 1) sources.size
      if anySubsetOk rest then
        return none
    return checkOutcome (some sources)

/-- The unique inclusion-minimal set of sources that can pay `cost`, if any. -/
def uniquePayingSourceSet (g : Game) (pool : ManaPool) (cost : ManaCost)
    (sources : Array (GameObject × Array ManaType))
    (spend : ManaSpend := {})
    (prop? : Option (PlayerId × ProposedSpell) := none) :
    Option (Array (GameObject × Array ManaType)) :=
  let n := sources.size
  if n > 20 then
    uniquePayingSourceSetLarge g pool cost sources spend prop?
  else
    let limit := 1 <<< n
    Id.run do
      let mut best : Option (Array (GameObject × Array ManaType)) := none
      for mask in [1:limit] do
        let sub := subsetFromMask sources mask
        if canPayTappingAll g pool cost sub.toList spend (prop? := prop?.map (·.2)) &&
            prop?.all (fun (p, prop) => g.tapPreservesPostManaCosts p prop (sub.map (·.1.id))) then
          match best with
          | none => best := some sub
          | some prev =>
            if payingSourceSubset sub prev then
              best := some sub
            else if payingSourceSubset prev sub then
              pure ()
            else
              return none
      return best.filter (fun minSub =>
        uniqueSubsetHasUniqueOutcome g pool cost sources minSub spend prop?)

/-- True when the locked-in mana cost has exactly one legal payment. -/
def hasUniqueManaPayment (g : Game) : Bool :=
  match g.pending, g.proposedSpell with
  | .activateManaAbilities p, some prop =>
    if !g.canPayLife p prop.payLife then false
    else if !g.sourceStillPayable prop then false
    else if !g.tapPreservesPostManaCosts p prop #[] then false
    else
      let canConvokeOrImprovise : Bool :=
        prop.kind == .spell && prop.cost.includesManaPayment &&
          match g.findObject? prop.spellId with
          | none => false
          | some spell =>
            let hasConvoke := KeywordAbility.hasConvoke (g.currentKeywords spell)
            let hasImprovise := g.spellHasImprovise (g.baseCard spell) p (spellObj? := some spell)
            (hasConvoke || hasImprovise) &&
              (g.permanentsOf p).any (fun o =>
                !o.status.tapped && !prop.teamworkCreatures.contains o.id &&
                  ((hasConvoke && g.isCreature o &&
                      (Game.convokePayOne prop.cost (g.colors o)).isSome) ||
                    (hasImprovise && g.isArtifact o && prop.cost.genericCount > 0)))
      if canConvokeOrImprovise then false
      else
        let pool := (g.player p).manaPool
        let spend := g.proposedManaSpend prop
        let sources := g.manaSourcesForProposed p prop
        let interest := spellManaSpentInterest g spend (some prop)
        let anyOutcomeMatters :=
          cantBeCounteredRiderMatters g spend (some prop) ||
            creatureSpellRiderMatters g spend (some prop) ||
            ancestryManaMatters g spend (some prop) ||
            !interest.isEmpty
        let includePoolSpend := anyOutcomeMatters
        match pool.payUnits? prop.cost spend with
        | some (_, spent0) =>
          let handManaObjs :=
            (g.player p).hand.filterMap fun id =>
              (g.findObject? id).bind fun o =>
                if !(g.activatedAbilitiesOf o).isEmpty then some o else none
          let gyManaObjs :=
            (g.player p).graveyard.filterMap fun id =>
              (g.findObject? id).bind fun o =>
                if !(g.activatedAbilitiesOf o).isEmpty then some o else none
          let manaObjs := g.permanentsOf p ++ handManaObjs ++ gyManaObjs
          let tapReady (o : GameObject) (d : ManaAbilityDef) : Bool :=
            !d.tap ||
              (!o.status.tapped &&
                !(g.hasSummoningSickness o && !(g.isCreature o && g.activatesAsThoughHaste p)))
          if !anyOutcomeMatters then
            !(g.hasUsableNonPlainManaAbility p (some prop) (includePoolSpending := false) &&
              manaObjs.any (fun o =>
                (g.manaAbilityDefs o).any (fun d =>
                  !g.isPlainTapManaAbilityDef p o d &&
                    g.manaAbilityDefUsable p o d &&
                    tapReady o d &&
                    (d.extraEffect?.isSome || d.modeChoices.any (·.output?.isNone)))))
          else
            let outcome0 := spellManaOutcome g spend (some prop) spent0
            let plainFlips :=
              canExtraPlainSourcesChangeOutcome g pool #[] prop.cost sources #[]
                spend (some (p, prop)) outcome0
            let nonPlainFlips :=
              g.hasUsableNonPlainManaAbility p (some prop) (includePoolSpending := includePoolSpend) &&
                manaObjs.any (fun o =>
                  (g.manaAbilityDefs o).any (fun d =>
                    !g.isPlainTapManaAbilityDef p o d &&
                      g.manaAbilityDefUsable p o d &&
                      tapReady o d &&
                      manaAbilityDefCanChangeOutcome g spend prop o d outcome0))
            !plainFlips && !nonPlainFlips
        | none =>
          !g.hasUsableNonPlainManaAbility p (some prop) (includePoolSpending := includePoolSpend) &&
            (uniquePayingSourceSet g pool prop.cost sources spend (some (p, prop))).isSome
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
    let hand := g.discardableHandIds p
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
    (output : Option IO.FS.Handle := none) (sameFile : Bool := false)
    (norandom : Bool := false) (rng : Rng := Rng.ofSeed 1) :
    IO Unit := do
  let mut g := g
  let mut rng := rng
  let mut seen := g.log.size
  let mut playerView := startVisible
  let mut lastActor : Option PlayerId := g.actor
  let mut pending := pending
  let mut passUntilGoals : Array PassUntilGoal := #[]
  let you : PlayerId := ⟨0⟩
  let youName := (g.player you).name
  IO.println (helpInteractive controlAll youName)
  while !g.over do
    if !norandom && g.pendingRandom?.isSome then
      let (rng', g') := g.resolvePendingRandom rng
      rng := rng'
      seen ← refreshAfterStep g g' seen (currentView g' playerView controlAll)
      g := g'
      continue
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
          let (rng', g') := if norandom then (rng, g') else g'.resolvePendingRandom rng
          rng := rng'
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
        let (rng', g') := if norandom then (rng, g') else g'.resolvePendingRandom rng
        rng := rng'
        seen ← recordAndRefresh output sameFile g g' seen playerView controlAll #[line]
        g := g'
      continue
    if let some step := autoPayStep? g pending then
      match step with
      | .error e =>
        IO.println s!"{actorDisplayName g} could not automatically pay: {e}"
      | .ok (g', cmds) =>
        let (rng', g') := if norandom then (rng, g') else g'.resolvePendingRandom rng
        rng := rng'
        seen ← recordAndRefresh output sameFile g g' seen playerView controlAll cmds
        g := g'
      continue
    if shouldAutoNoAttack g pending then
      let some p := g.actor | continue
      match applyAutoAction g p (.declareAttackers #[]) "declare no attackers" with
      | .error e => IO.println e
      | .ok g' =>
        let (rng', g') := if norandom then (rng, g') else g'.resolvePendingRandom rng
        rng := rng'
        seen ← recordAndRefresh output sameFile g g' seen playerView controlAll #["noattack"]
        g := g'
      continue
    if shouldAutoNoBlock g pending then
      let some p := g.actor | continue
      match applyAutoAction g p (.declareBlockers #[]) "declare no blockers" with
      | .error e => IO.println e
      | .ok g' =>
        let (rng', g') := if norandom then (rng, g') else g'.resolvePendingRandom rng
        rng := rng'
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
          let (rng', g') := if norandom then (rng, r.game) else r.game.resolvePendingRandom rng
          rng := rng'
          seen ← recordAndRefresh output sameFile g g' seen playerView controlAll r.commands
          g := g'
          continue
    | none => pure ()
    if shouldAutoPass g pending then
      let some p := g.actor | continue
      match applyAutoAction g p .pass "pass" with
      | .error e => IO.println e
      | .ok g' =>
        let (rng', g') := if norandom then (rng, g') else g'.resolvePendingRandom rng
        rng := rng'
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
          let (rng', g') := if norandom then (rng, g') else g'.resolvePendingRandom rng
          rng := rng'
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
    (sameFile : Bool := false)
    (norandom : Bool := false) (rng : Rng := Rng.ofSeed 1) : IO Unit := do
  let mut g := g
  let mut rng := rng
  let mut seen := g.log.size
  let mut remaining := fuel
  let mut pending := pending
  while remaining > 0 && !g.over do
    if !norandom && g.pendingRandom?.isSome then
      let (rng', g') := g.resolvePendingRandom rng
      rng := rng'
      seen ← refreshAfterStep g g' seen
      g := g'
      continue
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
      let (rng', g') := if norandom then (rng, g') else g'.resolvePendingRandom rng
      rng := rng'
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
  let (g, rng) ← Start.startWithRng {
    seats
    format := demoFormat opt.constructed
    seed := opt.seed
    startingPlayer := some startIdx
    norandom := opt.norandom }
  replayCompleteGame g rest opt.norandom rng

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
                    let (g, rng) ← startGameWithRng opt.seed (some startIdx) seats opt.norandom
                      opt.constructed
                    printOpening g (currentView g opt.playerView opt.multiplayer)
                    interactiveLoop g opt.playerView opt.multiplayer pending output sameFile
                      opt.norandom rng
                    return 0
                else
                  let (g, rng) ←
                    startDemoWithRng opt.seed (some decider) (seats := seats)
                      (norandom := opt.norandom)
                      (constructed := opt.constructed)
                  runAuto g opt.fuel pending output sameFile opt.norandom rng
                  return 0
