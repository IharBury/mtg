import Mtg.Engine
import Mtg.Demo.Render
import Mtg.Demo.RenderTests
import Mtg.Demo.WelcomeDecks

/-!
# Mtg.Demo

Console demonstration of `Mtg.Engine`. Default mode runs a scripted two-player
game with a heuristic agent using The Hobbit Welcome Decks. Pass `--interactive`
to play Chandra against the agent-controlled Nissa, or `--multiplayer` to issue
every player's actions from the console. In either interactive mode, `visible`
prints only information that player can see; `--visible` starts in that view.
`--input FILE` runs commands from the file first, then reads from the console.
`--output FILE` writes every command (from the file or the console) to that file.
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

def helpInteractive (controlAll : Bool := false) : String :=
  let viewWho := if controlAll then "the acting player" else "Chandra"
  s!"Commands:
  help                 Show this help
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

#guard ((helpInteractive false).splitOn "visible").length > 1
#guard ((helpInteractive false).splitOn "Chandra can see").length > 1
#guard ((helpInteractive true).splitOn "the acting player can see").length > 1
#guard ((helpInteractive false).splitOn "tap <id> [id...]").length > 1
#guard (usage.splitOn "--input FILE").length > 1
#guard (usage.splitOn "--output FILE").length > 1

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

def castUsage : String := "usage: cast <id>"

/-- Begin casting the named spell. Damage spells target the opponent; pump
spells target one of the caster's creatures. -/
def applyCast (g : Game) (p : PlayerId) (tokens : List String) : Except String Game := do
  let tokens := tokens.filter (fun t => !t.isEmpty)
  match tokens with
  | [arg] =>
    match parseObjectId? arg with
    | none => throw castUsage
    | some id =>
      match g.findObject? id with
      | none => throw "no such object"
      | some o =>
        let tgt :=
          match o.printed.spellEffect with
          | some (.dealDamage _) => some (Target.player (g.opponent p))
          | some (.pump _ _) =>
            (g.permanentsOf p).filter (·.printed.isCreature) |>.back?
              |>.map (fun c => Target.permanent c.id)
          | none => none
        g.apply p (.cast id tgt)
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
  match applyCast Tests.boltSetup ⟨0⟩ ["99999"] with
  | .error msg => msg == "no such object"
  | .ok _ => false

#guard
  match applyCast Tests.boltSetup ⟨0⟩ [toString Tests.boltInHand.id] with
  | .ok g' =>
    g'.pending == .activateManaAbilities ⟨0⟩ &&
    g'.log.any (fun s => Tests.mentions s "begins casting Lightning Bolt")
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
  | "play" => applyPlay g p args
  | "activate" => applyActivate g p args
  | "tap" => applyTap g p args
  | "cast" => applyCast g p args
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
  match applyInteractiveAsActor Tests.readyToDeclareBlockers "block" [] with
  | .ok g' =>
    (Tests.namedPermanent g' "Grizzly Bears").status.blocking ==
      some (Tests.namedPermanent g' "Gray Ogre").id
  | .error _ => false

#guard
  match applyInteractiveAsActor Tests.readyToDeclareAttackers "noattack" [] with
  | .ok g' => !(g'.battlefield.any (·.status.attacking))
  | .error _ => false

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
        let g ← startDemo opt.seed (chandraView (opt.interactive && opt.playerView))
        if opt.interactive then
          interactiveLoop g opt.playerView opt.multiplayer pending output
        else
          runAuto g opt.fuel
        return 0
