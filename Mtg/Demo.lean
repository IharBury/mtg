import Mtg.Engine
import Mtg.Demo.Render
import Mtg.Demo.RenderTests
import Mtg.Demo.WelcomeDecks

/-!
# Mtg.Demo

Console demonstration of `Mtg.Engine`. Default mode runs a scripted two-player
game with a heuristic agent using The Hobbit Welcome Decks. Pass `--interactive`
to play Chandra against the agent-controlled Nissa, or `--multiplayer` to issue
every player's actions from the console. In either interactive mode, choose who
takes the first turn with `first <name>` (CR 103.1) before opening hands are
drawn. `visible` prints only information that player can see; `--visible` starts
in that view. `--input FILE` runs commands from the file first, then reads from
the console. `--output FILE` writes every command (from the file or the console)
to that file.
-/

open Mtg.Engine
open Mtg.Engine.Game
open Mtg.Demo
open Mtg.Demo.Render

def usage : String :=
  "Mtg.Demo — demonstration of the Mtg.Engine rules engine

Usage:
  lake exe mtg-demo [--auto | --interactive | --multiplayer] [--visible]
                    [--input FILE] [--output FILE] [--seed N] [--fuel N]

Options:
  --auto          Run a heuristic two-player game (default)
  --interactive   Play as Chandra; Nissa is heuristic-controlled
  --multiplayer   Control both players from the console
  --visible       With --interactive or --multiplayer, hide information the
                  acting player cannot see
  --input FILE    With --interactive or --multiplayer, run these commands
                  first, then read from the console
  --output FILE   With --interactive or --multiplayer, write every command
                  (from --input and from the console) to this file
  --seed N        RNG seed (default 20260807)
  --fuel N        Maximum heuristic actions (default 800)
  --help          Show this help

Chandra uses the red Hobbit Welcome Deck and Nissa uses the green one
(40 cards, limited construction). Decklists:
https://magic.wizards.com/en/news/announcements/the-hobbit-welcome-decks

The engine follows the Magic: The Gathering Comprehensive Rules
effective 7 August 2026.

In --interactive and --multiplayer, choose who takes the first turn
(CR 103.1) with `first <name>` before opening hands are drawn.
"

def demoSeats : Array Seat := #[
  { name := "Chandra", deck := hobbitRed },
  { name := "Nissa", deck := hobbitGreen }
]

/-- Auto mode uses Chandra as the starting player. Interactive modes pass the
seat chosen at the console (CR 103.1). -/
def demoConfig (seed : UInt64) (startingPlayer : Option Nat := some 0) : StartConfig := {
  seats := demoSeats
  format := .limited
  seed := seed
  startingPlayer := startingPlayer
}

/-- Usage for the CR 103.1 `first` command, listing legal player names. -/
def firstUsage (seats : Array Seat) : String :=
  let names := String.intercalate " or " (seats.toList.map (·.name))
  s!"usage: first <name> ({names})"

/-- Seat index of the player who takes the first turn (CR 103.1). -/
def parseFirstPlayer (seats : Array Seat) (tokens : List String) : Except String Nat :=
  match tokens.filter (fun t => !t.isEmpty) with
  | [name] =>
    let lower := name.map Char.toLower
    match seats.findIdx? (fun s => s.name.map Char.toLower == lower) with
    | some i => .ok i
    | none => .error s!"No player named {name}"
  | _ => .error (firstUsage seats)

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

def printLog (g : Game) (startIdx : Nat) (viewer : Option PlayerId := none) : IO Nat := do
  for line in newLog g startIdx viewer do
    IO.println s!"  {line}"
  return g.log.size

/-- Print each zone whose occupants or battlefield status changed. -/
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

def printState (g : Game) (viewer : Option PlayerId := none) : IO Unit := do
  IO.println ""
  IO.println (snapshot g viewer)
  IO.println ""

def printEngineBanner : IO Unit := do
  IO.println Mtg.Engine.identification
  IO.println s!"Rules source: {Rules.sourceUrl}"
  IO.println ""

/-- Create the demo game after the starting player is known (CR 103.1). -/
def startGame (seed : UInt64) (startingPlayer : Option Nat := some 0) : IO Game := do
  match Start.start (demoConfig seed startingPlayer) with
  | .error e =>
    IO.eprintln s!"Failed to start game: {e}"
    throw (IO.userError e)
  | .ok g => return g

/-- Print the opening log and board after the game has started. -/
def printOpening (g : Game) (viewer : Option PlayerId := none) : IO Unit := do
  let _ ← printLog g 0 viewer
  printState g viewer

/-- Start a demo game and print the opening snapshot. Auto mode uses Chandra
as the starting player. -/
def startDemo (seed : UInt64) (startingPlayer : Option Nat := some 0)
    (viewer : Option PlayerId := none) : IO Game := do
  printEngineBanner
  let g ← startGame seed startingPlayer
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
      seen ← printLog g' seen
      printChangedZones g g'
      printChangedLife g g'
      printChangedMana g g'
      g := g'
  printState g
  match g.result with
  | some (.won p) => IO.println s!"Winner: {g.player p |>.name}"
  | some .draw => IO.println "The game is a draw."
  | none => IO.println s!"Stopped after {fuel} actions (turn {g.turnNumber})."

def helpInteractive (controlAll : Bool := false) : String :=
  let viewWho := if controlAll then "the acting player" else "Chandra"
  s!"Commands:
  help                 Show this help
  first <name>         Choose who takes the first turn (CR 103.1)
  state                Print the board
  visible              Print only information {viewWho} can see (CR 400.2)
  visible on           Use {viewWho}'s view for state and later updates
  visible off          Show full information in state and later updates
  keep                 Keep this opening hand (CR 103.5)
  mulligan             Declare a mulligan; taken after all declarations
  bottom <id> [id...]  Put cards on the bottom after a mulligan
  pass                 Pass priority
  pay                  Pay a proposed spell or ability's cost (CR 601.2h)
  sacrifice <id>       After pay, sacrifice a creature or artifact to finish activating
  play <id>            Play a land
  tap <id> [id...]     Tap listed permanents for their first mana abilities
  activate <id>        Begin activating a permanent's ability (then tap for mana and pay)
  mode <n>             Choose a mode for a modal spell or ability (CR 601.2b / 700.2)
  cast <id>            Begin casting a spell (CR 601.2a)
  target <id|name|opponent>  Announce a target (CR 601.2c)
  scry                 Finish scrying; keep looked-at cards on top
  scry top <id>...     Put listed cards on top (last = new top); rest go to the bottom
  scry bottom <id>...  Put listed cards on the bottom (first = new bottom); rest stay on top
  scry top <id>... bottom <id>...  Choose both piles and their orders (CR 701.20)
  discard <id>         Discard a card; if you do, draw (CR 701.9)
  decline              Decline an optional discard
  attack               Attack with every creature that can
  attack <id> [id...]  Attack with the listed creatures
  noattack             Declare no attackers
  block                Block each attacker with a legal unused blocker
  block <b> <a> [...]  Assign listed blocker/attacker pairs
  noblock              Declare no blockers
  assign               Use the default combat damage assignment (CR 510.1)
  assign <s> <t> <n> [...]  Divide combat damage: source, creature, amount (CR 510.1c–d)
  concede              Concede
  quit                 Exit
"

#guard ((helpInteractive false).splitOn "visible").length > 1
#guard ((helpInteractive false).splitOn "Chandra can see").length > 1
#guard ((helpInteractive true).splitOn "the acting player can see").length > 1
#guard ((helpInteractive false).splitOn "tap <id> [id...]").length > 1
#guard ((helpInteractive false).splitOn "scry bottom").length > 1
#guard ((helpInteractive false).splitOn "scry top").length > 1
#guard ((helpInteractive false).splitOn "target <id|name|opponent>").length > 1
#guard ((helpInteractive false).splitOn "mode <n>").length > 1
#guard ((helpInteractive false).splitOn "assign <s> <t> <n>").length > 1
#guard ((helpInteractive false).splitOn "first <name>").length > 1
#guard ((helpInteractive false).splitOn "CR 103.1").length > 1
#guard ((helpInteractive false).splitOn "discard <id>").length > 1
#guard ((helpInteractive false).splitOn "decline").length > 1
#guard (usage.splitOn "--input FILE").length > 1
#guard (usage.splitOn "--output FILE").length > 1
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

/-- Parse one or more object identifiers from command tokens. -/
def parseObjectIds (tokens : List String) (usage : String) : Except String (Array ObjectId) :=
  go (tokens.filter (fun t => !t.isEmpty)) #[]
where
  go : List String → Array ObjectId → Except String (Array ObjectId)
    | [], acc => if acc.isEmpty then .error usage else .ok acc
    | t :: rest, acc =>
      match parseObjectId? t with
      | none => .error usage
      | some id => go rest (acc.push id)

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
  let tokens := tokens.filter (fun t => !t.isEmpty)
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

/-- Pair each unused legal blocker with the first still-unblocked attacker
it can block. A bare `block` covers as many attacks as possible. -/
def greedyBlockAssignments (g : Game) : Array (ObjectId × ObjectId) :=
  Id.run do
    let attackers := g.battlefield.filter (·.status.attacking)
    let defender := g.opponent g.activePlayer
    let candidates := g.battlefield.filter (fun b =>
      b.isCreature && b.controlledBy defender && !b.status.tapped)
    let mut blocked : Array ObjectId := #[]
    let mut asgn : Array (ObjectId × ObjectId) := #[]
    for b in candidates do
      match attackers.find? (fun a => !blocked.contains a.id && g.canBlock b a) with
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
  let tokens := tokens.filter (fun t => !t.isEmpty)
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

def assignUsage : String := "usage: assign [source target amount ...]"

/-- Add `amt` from `src` to creature `tgt` in an accumulating assignment list. -/
def pushCombatAmount (acc : Array CreatureCombatAssignment) (src tgt : ObjectId) (amt : Int) :
    Array CreatureCombatAssignment :=
  match acc.findIdx? (fun a => a.source == src) with
  | none => acc.push { source := src, toCreatures := #[(tgt, amt)] }
  | some i =>
    let a := acc[i]!
    acc.set! i { a with toCreatures := a.toCreatures.push (tgt, amt) }

/-- Parse source/target/amount triples. An empty list means the default legal
assignment (CR 510.1c–d). -/
def parseCombatAssignments (tokens : List String) :
    Except String (Array CreatureCombatAssignment) :=
  go (tokens.filter (fun t => !t.isEmpty)) #[]
where
  go : List String → Array CreatureCombatAssignment →
      Except String (Array CreatureCombatAssignment)
    | [], acc => .ok acc
    | srcTok :: tgtTok :: amtTok :: rest, acc =>
      match parseObjectId? srcTok, parseObjectId? tgtTok, amtTok.toInt? with
      | some src, some tgt, some amt => go rest (pushCombatAmount acc src tgt amt)
      | _, _, _ => .error assignUsage
    | _, _ => .error assignUsage

def applyAssign (g : Game) (p : PlayerId) (tokens : List String) : Except String Game := do
  let asgns ← parseCombatAssignments tokens
  for a in asgns do
    if (g.findObject? a.source).isNone then
      throw "no such object"
    for (tid, _) in a.toCreatures do
      if (g.findObject? tid).isNone then
        throw "no such object"
  g.apply p (.assignCombatDamage asgns)

def parsedOneCombatTriple : Bool :=
  match parseCombatAssignments ["3", "#7", "2"] with
  | .ok asgns => asgns == #[{ source := ⟨3⟩, toCreatures := #[(⟨7⟩, 2)] }]
  | .error _ => false

#guard parsedOneCombatTriple

def parsedTwoAmountsSameSource : Bool :=
  match parseCombatAssignments ["1", "2", "3", "1", "4", "0"] with
  | .ok asgns =>
    asgns == #[{ source := ⟨1⟩, toCreatures := #[(⟨2⟩, 3), (⟨4⟩, 0)] }]
  | .error _ => false

#guard parsedTwoAmountsSameSource

#guard
  match parseCombatAssignments [] with
  | .ok asgns => asgns.isEmpty
  | .error _ => false

#guard
  match parseCombatAssignments ["1", "2"] with
  | .error msg => msg == assignUsage
  | .ok _ => false

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
  match applyAssign Tests.readyToDeclareBlockers ⟨0⟩ [] with
  | .error msg => msg == "Not time to assign combat damage (CR 510.1)"
  | .ok _ => false

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

/-- `none` prints Chandra's view once; `some true/false` turns follow mode on or off. -/
def applyVisible (tokens : List String) : Except String (Option Bool) :=
  match tokens.filter (fun t => !t.isEmpty) with
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

/-- Chandra's viewpoint when follow mode is on; omniscient otherwise. -/
def chandraView (playerView : Bool) : Option PlayerId :=
  if playerView then some ⟨0⟩ else none

#guard (chandraView false).isNone
#guard chandraView true == some ⟨0⟩

/-- Hidden-information view. Chandra-vs-agent always follows Chandra;
multiplayer follows the player who must act. -/
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

def tapUsage : String := "usage: tap <id> [id ...]"

/-- Tap each listed permanent for its first mana ability. -/
def applyTap (g : Game) (p : PlayerId) (tokens : List String) : Except String Game := do
  let ids ← parseObjectIds tokens tapUsage
  let mut jobs : Array (ObjectId × ManaType) := #[]
  for id in ids do
    match g.findObject? id with
    | none => throw "no such object"
    | some o =>
      match o.printed.manaAbilities[0]? with
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
def applyPlay (g : Game) (p : PlayerId) (tokens : List String) : Except String Game := do
  let tokens := tokens.filter (fun t => !t.isEmpty)
  match tokens with
  | [arg] =>
    match parseObjectId? arg with
    | none => throw playUsage
    | some id =>
      match g.findObject? id with
      | none => throw "no such object"
      | some _ => g.apply p (.playLand id)
  | _ => throw playUsage

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

def activateUsage : String := "usage: activate <id>"

/-- Activate the first non-mana activated ability of the named permanent. -/
def applyActivate (g : Game) (p : PlayerId) (tokens : List String) : Except String Game := do
  let tokens := tokens.filter (fun t => !t.isEmpty)
  match tokens with
  | [arg] =>
    match parseObjectId? arg with
    | none => throw activateUsage
    | some id =>
      match g.findObject? id with
      | none => throw "no such object"
      | some o =>
        match o.printed.activatedAbilities[0]? with
        | none => throw s!"{o.name} has no activated ability"
        | some _ => g.apply p (.activate id 0)
  | _ => throw activateUsage

def sacrificeUsage : String := "usage: sacrifice <id>"

/-- After `pay`, sacrifice the named creature or artifact to finish activating. -/
def applySacrifice (g : Game) (p : PlayerId) (tokens : List String) : Except String Game := do
  let tokens := tokens.filter (fun t => !t.isEmpty)
  match tokens with
  | [arg] =>
    match parseObjectId? arg with
    | none => throw sacrificeUsage
    | some id =>
      match g.findObject? id with
      | none => throw "no such object"
      | some _ => g.apply p (.sacrifice id)
  | _ => throw sacrificeUsage

#guard
  match applyActivate Tests.baubleReady ⟨0⟩ [] with
  | .error msg => msg == activateUsage
  | .ok _ => false

#guard
  match applyActivate Tests.baubleReady ⟨0⟩ ["nope"] with
  | .error msg => msg == activateUsage
  | .ok _ => false

#guard
  match applyActivate Tests.baubleReady ⟨0⟩ ["1", "2"] with
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

def modeUsage : String := "usage: mode <n>"

/-- Choose a mode of a modal spell or ability (CR 601.2b). Modes are 1-indexed. -/
def applyMode (g : Game) (p : PlayerId) (tokens : List String) : Except String Game := do
  let tokens := tokens.filter (fun t => !t.isEmpty)
  match tokens with
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

def castUsage : String := "usage: cast <id>"

/-- Begin casting the named spell (CR 601.2a). Targets are announced later
with `target` (CR 601.2c). -/
def applyCast (g : Game) (p : PlayerId) (tokens : List String) : Except String Game := do
  let tokens := tokens.filter (fun t => !t.isEmpty)
  match tokens with
  | [arg] =>
    match parseObjectId? arg with
    | none => throw castUsage
    | some id =>
      match g.findObject? id with
      | none => throw "no such object"
      | some _ => g.apply p (.cast id)
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

def targetUsage : String := "usage: target <id|name|opponent>"

/-- Parse a CR 601.2c target: a permanent id, a player name, or `opponent`. -/
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
      | some _ => return Target.permanent id
    | none => throw targetUsage

/-- Announce the chosen target for a proposed spell (CR 601.2c). -/
def applyTarget (g : Game) (p : PlayerId) (tokens : List String) : Except String Game := do
  let tokens := tokens.filter (fun t => !t.isEmpty)
  match tokens with
  | [arg] =>
    let t ← parseTarget g p arg
    g.apply p (.target t)
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
  | .error msg => msg == targetUsage
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
    let tokens := tokens.filter (fun t => !t.isEmpty)
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
def applyDiscard (g : Game) (p : PlayerId) (tokens : List String) : Except String Game := do
  let tokens := tokens.filter (fun t => !t.isEmpty)
  match tokens with
  | [arg] =>
    match parseObjectId? arg with
    | none => throw discardUsage
    | some id =>
      match g.findObject? id with
      | none => throw "no such object"
      | some _ => g.apply p (.discard id)
  | _ => throw discardUsage

def declineUsage : String := "usage: decline"

/-- Decline an optional discard. -/
def applyDecline (g : Game) (p : PlayerId) (tokens : List String) : Except String Game := do
  let tokens := tokens.filter (fun t => !t.isEmpty)
  match tokens with
  | [] => g.apply p .decline
  | _ => throw declineUsage

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

/-- Game-changing interactive commands. `help`/`state`/`visible`/`quit` are
handled by the console loop. Actions are issued as `p`. -/
def applyInteractiveAction (g : Game) (p : PlayerId) (cmd : String) (args : List String) :
    Except String Game :=
  match cmd with
  | "keep" => g.apply p .keep
  | "mulligan" => g.apply p .takeMulligan
  | "bottom" => applyBottom g p args
  | "pass" => g.apply p .pass
  | "pay" => g.apply p .pay
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
  | "decline" => applyDecline g p args
  | _ => .error s!"Unknown command: {cmd}"

/-- Issue a console command as the player who currently must act. -/
def applyInteractiveAsActor (g : Game) (cmd : String) (args : List String) : Except String Game := do
  let p ← actingPlayer g
  applyInteractiveAction g p cmd args

#guard
  match applyInteractiveAsActor Tests.drawnHands "keep" [] with
  | .ok g' => (g'.player ⟨0⟩).keptOpeningHand && g'.actor == some ⟨1⟩
  | .error _ => false

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
  match applyInteractiveAsActor Tests.hospitalityLandPlayed "target"
      [toString (Tests.namedPermanent Tests.hospitalityLandPlayed "Grizzly Bears").id] with
  | .ok g' =>
    g'.pending == .none &&
    g'.hasPriority ⟨0⟩ &&
    g'.stack.back!.targets ==
      #[Target.permanent (Tests.namedPermanent g' "Grizzly Bears").id]
  | .error _ => false

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
  match applyInteractiveAsActor Tests.proposedWarg "mode" ["1"] with
  | .ok g' =>
    g'.pending == .chooseTargets ⟨0⟩ &&
    g'.stack.back!.chosenMode == some 0
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

/-- Non-empty trimmed commands from an input file (one command per line). -/
def commandsFromLines (lines : Array String) : List String :=
  lines.toList.map (fun s => s.trimAscii.copy) |>.filter (fun s => !s.isEmpty)

#guard commandsFromLines #["keep", "pass"] == ["keep", "pass"]
#guard commandsFromLines #["  keep  ", "", "pass"] == ["keep", "pass"]
#guard commandsFromLines #["", "  \t  "] == []
#guard commandsFromLines #["keep\r", "bottom 3 4"] == ["keep", "bottom 3 4"]

/-- Load `--input` commands, or `[]` when no file was given. -/
def pendingCommands (inputFile : Option String) : IO (Except String (List String)) := do
  match inputFile with
  | none => return .ok []
  | some path =>
    try
      let lines ← IO.FS.lines path
      return .ok (commandsFromLines lines)
    catch e =>
      return .error s!"Failed to read input file {path}: {e}"

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

/-- Open `--output` for writing, or `none` when no file was given. -/
def openOutputFile (outputFile : Option String) : IO (Except String (Option IO.FS.Handle)) := do
  match outputFile with
  | none => return .ok none
  | some path =>
    try
      let h ← IO.FS.Handle.mk path .write
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

/-- CR 103.1: before opening hands, choose who takes the first turn. Returns
the seat index and remaining `--input` lines, or `none` if the user quits. -/
partial def chooseStartingPlayer (pending : List String)
    (output : Option IO.FS.Handle) : IO (Option (Nat × List String)) := do
  IO.println "At the start of a game, choose who takes the first turn (CR 103.1)."
  for seat in demoSeats do
    IO.println s!"  first {seat.name}"
  IO.println ""
  let mut pending := pending
  let mut chosen : Option Nat := none
  while chosen.isNone do
    IO.print "mtg> "
    (← IO.getStdout).flush
    let (line, rest) ← nextCommandLine pending
    pending := rest
    if line.isEmpty then
      continue
    recordCommand output line
    let parts := line.splitOn " "
    let cmd := parts.headD ""
    match cmd with
    | "quit" | "exit" =>
      IO.println "Goodbye."
      return none
    | "help" =>
      IO.println helpChooseFirst
    | "first" =>
      match parseFirstPlayer demoSeats (parts.drop 1) with
      | .error e => IO.println s!"! {e}"
      | .ok idx => chosen := some idx
    | _ =>
      IO.println "! Choose who takes the first turn (CR 103.1): first <name>"
  match chosen with
  | some idx => return some (idx, pending)
  | none => return none

partial def interactiveLoop (g : Game) (startVisible : Bool := false)
    (controlAll : Bool := false) (pending : List String := [])
    (output : Option IO.FS.Handle := none) : IO Unit := do
  let mut g := g
  let mut seen := g.log.size
  let mut playerView := startVisible
  let mut lastActor : Option PlayerId := g.actor
  let mut pending := pending
  let chandra : PlayerId := ⟨0⟩
  let nissa : PlayerId := ⟨1⟩
  IO.println (helpInteractive controlAll)
  while !g.over do
    -- Chandra-vs-agent: let the heuristic play Nissa until Chandra must act.
    if !controlAll then
      while !g.over && g.actor == some nissa do
        match Agent.step g with
        | .error e =>
          IO.println s!"Nissa could not act: {e}"
          break
        | .ok g' =>
          seen ← printLog g' seen (chandraView playerView)
          printChangedZones g g' (chandraView playerView)
          printChangedLife g g'
          printChangedMana g g'
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
    let prompt :=
      if controlAll then
        match g.actor with
        | some p => s!"mtg ({g.player p |>.name})> "
        | none => "mtg> "
      else
        "mtg> "
    IO.print prompt
    (← IO.getStdout).flush
    let (line, rest) ← nextCommandLine pending
    pending := rest
    if line.isEmpty then
      continue
    recordCommand output line
    let parts := line.splitOn " "
    let cmd := parts.headD ""
    match cmd with
    | "quit" | "exit" =>
      IO.println "Goodbye."
      return
    | "help" => IO.println (helpInteractive controlAll)
    | "first" =>
      IO.println "! Starting player already chosen (CR 103.1)"
    | "state" => printState g (currentView g playerView controlAll)
    | "visible" =>
      match applyVisible (parts.drop 1) with
      | .error e => IO.println s!"! {e}"
      | .ok none =>
        match currentView g true controlAll with
        | some p => printState g (some p)
        | none => printState g (some chandra)
      | .ok (some on) =>
        playerView := on
        if on then
          let who :=
            match currentView g true controlAll with
            | some p => (g.player p).name
            | none => "Chandra"
          IO.println s!"Showing only information {who} can see."
          printState g (currentView g true controlAll)
        else
          IO.println "Showing full game information."
    | _ =>
      match applyInteractiveAsActor g cmd (parts.drop 1) with
      | .error e => IO.println s!"! {e}"
      | .ok g' =>
        seen ← printLog g' seen (currentView g' playerView controlAll)
        printChangedZones g g' (currentView g' playerView controlAll)
        printChangedLife g g'
        printChangedMana g g'
        g := g'
        if g.over then
          printState g (currentView g playerView controlAll)
  match g.result with
  | some (.won p) => IO.println s!"Winner: {g.player p |>.name}"
  | some .draw => IO.println "The game is a draw."
  | none => pure ()

structure DemoOptions where
  interactive : Bool
  multiplayer : Bool
  playerView : Bool
  seed : UInt64
  fuel : Nat
  inputFile : Option String
  outputFile : Option String

def parseArgs (args : List String) : Except String DemoOptions :=
  Id.run do
    let mut interactive := false
    let mut multiplayer := false
    let mut playerView := false
    let mut seed : UInt64 := 20260807
    let mut fuel : Nat := 800
    let mut inputFile : Option String := none
    let mut outputFile : Option String := none
    let mut rest := args
    while !rest.isEmpty do
      match rest with
      | "--" :: xs =>
        rest := xs
      | "--help" :: _ => return .error "help"
      | "--auto" :: xs =>
        interactive := false
        multiplayer := false
        rest := xs
      | "--interactive" :: xs =>
        interactive := true
        multiplayer := false
        rest := xs
      | "--multiplayer" :: xs =>
        interactive := true
        multiplayer := true
        rest := xs
      | "--visible" :: xs =>
        playerView := true
        rest := xs
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
    if playerView && !interactive then
      return .error "--visible requires --interactive or --multiplayer"
    if inputFile.isSome && !interactive then
      return .error "--input requires --interactive or --multiplayer"
    if outputFile.isSome && !interactive then
      return .error "--output requires --interactive or --multiplayer"
    return .ok {
      interactive := interactive
      multiplayer := multiplayer
      playerView := playerView
      seed := seed
      fuel := fuel
      inputFile := inputFile
      outputFile := outputFile
    }

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

def main (args : List String) : IO UInt32 := do
  match parseArgs args with
  | .error "help" =>
    IO.println usage
    return 0
  | .error e =>
    IO.eprintln e
    IO.println usage
    return 1
  | .ok opt =>
    match (← pendingCommands opt.inputFile) with
    | .error e =>
      IO.eprintln e
      return 1
    | .ok pending =>
      match (← openOutputFile opt.outputFile) with
      | .error e =>
        IO.eprintln e
        return 1
      | .ok output =>
        if opt.interactive then
          printEngineBanner
          match (← chooseStartingPlayer pending output) with
          | none => return 0
          | some (startIdx, pending) =>
            let g ← startGame opt.seed (some startIdx)
            printOpening g (currentView g opt.playerView opt.multiplayer)
            interactiveLoop g opt.playerView opt.multiplayer pending output
            return 0
        else
          let g ← startDemo opt.seed
          runAuto g opt.fuel
          return 0
