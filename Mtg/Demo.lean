import Mtg.Engine
import Mtg.Demo.WelcomeDecks

/-!
# Mtg.Demo

Console demonstration of `Mtg.Engine`. Default mode runs a scripted two-player
game with a heuristic agent using The Hobbit Welcome Decks. Pass `--interactive`
to play Chandra against the agent-controlled Nissa. In interactive mode, `visible`
prints only information Chandra can see; `--visible` starts in that player view.
-/

open Mtg.Engine
open Mtg.Engine.Game
open Mtg.Engine.Render
open Mtg.Demo

def usage : String :=
  "Mtg.Demo — demonstration of the Mtg.Engine rules engine

Usage:
  lake exe mtg-demo [--auto | --interactive] [--visible] [--seed N] [--fuel N]

Options:
  --auto          Run a heuristic two-player game (default)
  --interactive   Play as Chandra; Nissa is heuristic-controlled
  --visible       With --interactive, hide information Chandra cannot see
  --seed N        RNG seed (default 20260807)
  --fuel N        Maximum heuristic actions (default 800)
  --help          Show this help

Chandra uses the red Hobbit Welcome Deck and Nissa uses the green one
(40 cards, limited construction). Decklists:
https://magic.wizards.com/en/news/announcements/the-hobbit-welcome-decks

The engine follows the Magic: The Gathering Comprehensive Rules
effective 7 August 2026.
"

def demoConfig (seed : UInt64) : StartConfig := {
  seats := #[
    { name := "Chandra", deck := hobbitRed },
    { name := "Nissa", deck := hobbitGreen }
  ]
  format := .limited
  seed := seed
  startingPlayer := some 0
}

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

def startDemo (seed : UInt64) (viewer : Option PlayerId := none) : IO Game := do
  match Start.start (demoConfig seed) with
  | .error e =>
    IO.eprintln s!"Failed to start game: {e}"
    throw (IO.userError e)
  | .ok g =>
    IO.println Mtg.Engine.identification
    IO.println s!"Rules source: {Rules.sourceUrl}"
    IO.println ""
    let _ ← printLog g 0 viewer
    printState g viewer
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

def helpInteractive : String :=
  "Commands:
  help                 Show this help
  state                Print the board
  visible              Print only information Chandra can see (CR 400.2)
  visible on           Use Chandra's view for state and later updates
  visible off          Show full information in state and later updates
  keep                 Keep this opening hand (CR 103.5)
  mulligan             Declare a mulligan; taken after all declarations
  bottom <id> [id...]  Put cards on the bottom after a mulligan
  pass                 Pass priority
  pay                  Pay a proposed spell or ability's cost (CR 601.2h)
  sacrifice <id>       After pay, sacrifice a creature or artifact to finish activating
  play <id>            Play a land
  tap <id>             Tap a permanent for its first mana ability
  activate <id>        Begin activating a permanent's ability (then tap for mana and pay)
  cast <id>            Begin casting a spell (then tap for mana and pay)
  attack               Attack with every creature that can
  attack <id> [id...]  Attack with the listed creatures
  noattack             Declare no attackers
  block                Block each attacker with a legal unused blocker
  block <b> <a> [...]  Assign listed blocker/attacker pairs
  noblock              Declare no blockers
  concede              Concede
  quit                 Exit
"

#guard (helpInteractive.splitOn "visible").length > 1
#guard (helpInteractive.splitOn "Chandra can see").length > 1

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
      b.printed.isCreature && b.controlledBy defender && !b.status.tapped)
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
    (Tests.namedPermanent g' "Grizzly Bears").status.blocking == some ogre.id
  | .error _ => false

#guard
  match applyBlock Tests.readyToDeclareBlockers ⟨1⟩ [] with
  | .ok g' =>
    (Tests.namedPermanent g' "Grizzly Bears").status.blocking ==
      some (Tests.namedPermanent g' "Gray Ogre").id
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

partial def interactiveLoop (g : Game) (startVisible : Bool := false) : IO Unit := do
  let mut g := g
  let mut seen := g.log.size
  let mut playerView := startVisible
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
        seen ← printLog g' seen (chandraView playerView)
        printChangedZones g g' (chandraView playerView)
        printChangedLife g g'
        printChangedMana g g'
        g := g'
    if g.over then break
    IO.print "mtg> "
    (← IO.getStdout).flush
    let stdin ← IO.getStdin
    let line := (← stdin.getLine).trimAscii.copy
    if line.isEmpty then
      continue
    let parts := line.splitOn " "
    let cmd := parts.headD ""
    let arg := parts.drop 1 |>.headD ""
    let act : Except String Game :=
      match cmd with
      | "help" => .ok g
      | "state" => .ok g
      | "visible" => .ok g
      | "quit" | "exit" => .ok g
      | "keep" => g.apply chandra .keep
      | "mulligan" => g.apply chandra .takeMulligan
      | "bottom" => applyBottom g chandra (parts.drop 1)
      | "pass" => g.apply chandra .pass
      | "pay" => g.apply chandra .pay
      | "sacrifice" => applySacrifice g chandra (parts.drop 1)
      | "concede" => g.apply chandra .concede
      | "attack" => applyAttack g chandra (parts.drop 1)
      | "noattack" => g.apply chandra (.declareAttackers #[])
      | "block" => applyBlock g chandra (parts.drop 1)
      | "noblock" => g.apply chandra (.declareBlockers #[])
      | "play" =>
        match parseObjectId? arg with
        | none => .error "usage: play <id>"
        | some id => g.apply chandra (.playLand id)
      | "activate" => applyActivate g chandra (parts.drop 1)
      | "tap" =>
        match parseObjectId? arg with
        | none => .error "usage: tap <id>"
        | some id =>
          match g.findObject? id with
          | none => .error "no such object"
          | some o =>
            match o.printed.manaAbilities[0]? with
            | none => .error s!"{o.name} has no mana ability"
            | some m => g.apply chandra (.tapForMana id m)
      | "cast" =>
        match parseObjectId? arg with
        | none => .error "usage: cast <id>"
        | some id =>
          match g.findObject? id with
          | none => .error "no such object"
          | some o =>
            let tgt :=
              match o.printed.spellEffect with
              | some (.dealDamage _) => some (Target.player (g.opponent chandra))
              | some (.pump _ _) =>
                (g.permanentsOf chandra).filter (·.printed.isCreature) |>.back?
                  |>.map (fun c => Target.permanent c.id)
              | none => none
            g.apply chandra (.cast id tgt)
      | _ => .error s!"Unknown command: {cmd}"
    match cmd with
    | "quit" | "exit" =>
      IO.println "Goodbye."
      return
    | "help" => IO.println helpInteractive
    | "state" => printState g (chandraView playerView)
    | "visible" =>
      match applyVisible (parts.drop 1) with
      | .error e => IO.println s!"! {e}"
      | .ok none => printState g (some chandra)
      | .ok (some on) =>
        playerView := on
        if on then
          IO.println "Showing only information Chandra can see."
          printState g (some chandra)
        else
          IO.println "Showing full game information."
    | _ =>
      match act with
      | .error e => IO.println s!"! {e}"
      | .ok g' =>
        seen ← printLog g' seen (chandraView playerView)
        printChangedZones g g' (chandraView playerView)
        printChangedLife g g'
        printChangedMana g g'
        g := g'
        if g.over then
          printState g (chandraView playerView)
  match g.result with
  | some (.won p) => IO.println s!"Winner: {g.player p |>.name}"
  | some .draw => IO.println "The game is a draw."
  | none => pure ()

def parseArgs (args : List String) : Except String (Bool × Bool × UInt64 × Nat) :=
  Id.run do
    let mut interactive := false
    let mut playerView := false
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
      | "--visible" :: xs =>
        playerView := true
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
    if playerView && !interactive then
      return .error "--visible requires --interactive"
    return .ok (interactive, playerView, seed, fuel)

#guard
  match parseArgs ["--interactive", "--visible"] with
  | .ok (true, true, _, _) => true
  | _ => false

#guard
  match parseArgs ["--interactive"] with
  | .ok (true, false, _, _) => true
  | _ => false

#guard
  match parseArgs ["--visible"] with
  | .error msg => msg == "--visible requires --interactive"
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
  | .ok (interactive, playerView, seed, fuel) =>
    let g ← startDemo seed (chandraView (interactive && playerView))
    if interactive then
      interactiveLoop g playerView
    else
      runAuto g fuel
    return 0
