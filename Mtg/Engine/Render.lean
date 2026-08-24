import Mtg.Engine.Game

/-!
# Text rendering of a game for the console demo.
-/

namespace Mtg.Engine.Render

open Mtg.Engine
open Mtg.Engine.Game

/-- Owner and controller of an object (CR 108.3, 110.2). Permanents always
have both; the demo prints them so a shared battlefield is unambiguous. -/
def controlClause (g : Game) (o : GameObject) : String :=
  let owned := s!"owned by {g.player o.owner |>.name}"
  match o.controller with
  | some p => s!" ({owned}, controlled by {g.player p |>.name})"
  | none => s!" ({owned}, no controller)"

def objectLine (g : Game) (o : GameObject) : String :=
  let tap := if o.status.tapped then " (tapped)" else ""
  let atk := if o.status.attacking then " *attacking*" else ""
  let blk :=
    match o.status.blocking with
    | some _ => " *blocking*"
    | none => ""
  let pt :=
    if o.printed.isCreature then s!" {o.power}/{o.toughness}" else ""
  let dmg :=
    if o.status.damage > 0 then s!" dmg:{o.status.damage}" else ""
  s!"{o.id} {o.name}{pt}{controlClause g o}{tap}{atk}{blk}{dmg}"

def handLine (g : Game) (id : ObjectId) : String :=
  match g.findObject? id with
  | none => s!"{id} (missing)"
  | some o => s!"{o.id} {o.printed.summary}"

def playerBlock (g : Game) (pl : Player) : String :=
  let marker := if pl.id == g.activePlayer then " (active)" else ""
  let bf := (g.permanentsOf pl.id).toList.map (objectLine g)
  let bfText := if bf.isEmpty then "  (none)" else String.intercalate "\n  " bf
  let hand := pl.hand.toList.map (handLine g)
  let handText := if hand.isEmpty then "  (empty)" else String.intercalate "\n  " hand
  String.intercalate "\n" [
    s!"{pl.name}{marker} — life {pl.life} — library {pl.library.size} — GY {pl.graveyard.size} — mana {pl.manaPool}",
    s!"  Hand ({pl.hand.size}):",
    "  " ++ handText,
    "  Battlefield:",
    "  " ++ bfText
  ]

def stackBlock (g : Game) : String :=
  if g.stack.isEmpty then "Stack: (empty)"
  else
    let lines := g.stack.toList.reverse.map (fun e =>
      match g.findObject? e.objectId with
      | some o => s!"  {o.name} (controlled by {g.player e.controller |>.name})"
      | none => "  (missing)")
    "Stack (top first):\n" ++ String.intercalate "\n" lines

def header (g : Game) : String :=
  let pending :=
    match g.pending with
    | .none => ""
    | .declareAttackers => " [declare attackers]"
    | .declareBlockers => " [declare blockers]"
  let result :=
    match g.result with
    | none => ""
    | some (.won p) => s!"  RESULT: {g.player p |>.name} wins"
    | some .draw => "  RESULT: draw"
  s!"Turn {g.turnNumber} · {g.step} · priority: {g.player g.priority |>.name}{pending}{result}"

def snapshot (g : Game) : String :=
  let players := g.players.toList.map (playerBlock g)
  String.intercalate "\n\n" (header g :: stackBlock g :: players)

/-- New log lines starting at `startIdx`. -/
def newLog (g : Game) (startIdx : Nat) : Array String :=
  g.log.extract startIdx g.log.size

/-- Current life total, matching the snapshot's `life N` fragment. -/
def lifeLine (pl : Player) : String :=
  s!"{pl.name} — life {pl.life}"

/-- Players whose life totals differ between two game states. -/
def changedLifeTotals (before after : Game) : Array Player :=
  after.players.filter (fun pl => (before.player pl.id).life != pl.life)

/-- Player-facing name of a zone, using seat names rather than `Player N`. -/
def zoneLabel (g : Game) : Zone → String
  | .library p => s!"{g.player p |>.name}'s library"
  | .hand p => s!"{g.player p |>.name}'s hand"
  | .graveyard p => s!"{g.player p |>.name}'s graveyard"
  | .battlefield => "battlefield"
  | .stack => "stack"
  | .exile => "exile"
  | .command => "command"
  | .ante => "ante"

/-- Object identities currently occupying `z`, in zone order. -/
def zoneObjectIds (g : Game) : Zone → Array ObjectId
  | .library p => (g.player p).library
  | .hand p => (g.player p).hand
  | .graveyard p => (g.player p).graveyard
  | .stack => g.stack.map (fun e => e.objectId)
  | .battlefield => g.battlefield.map (·.id)
  | .exile => g.objects.filter (fun o => o.zone == .exile) |>.map (·.id)
  | .command => g.objects.filter (fun o => o.zone == .command) |>.map (·.id)
  | .ante => g.objects.filter (fun o => o.zone == .ante) |>.map (·.id)

/-- Every zone the demo tracks, in a stable print order. -/
def allZones (g : Game) : Array Zone :=
  Id.run do
    let mut zs : Array Zone := #[]
    for pl in g.players do
      zs := zs.push (.library pl.id)
      zs := zs.push (.hand pl.id)
      zs := zs.push (.graveyard pl.id)
    return zs.push .battlefield |>.push .stack |>.push .exile |>.push .command |>.push .ante

/-- Visible battlefield lines, including tap/combat/damage status (CR 110.5). -/
def battlefieldView (g : Game) : Array String :=
  g.battlefield.map (objectLine g)

/-- Zones whose occupants, order, or (for the battlefield) visible status
differ between two game states. Tapping or untapping a land does not move it,
but it does change the battlefield (CR 110.5 / 502.2), so the demo reprints
that zone. -/
def changedZones (before after : Game) : Array Zone :=
  (allZones after).filter (fun z =>
    match z with
    | .battlefield => battlefieldView before != battlefieldView after
    | _ => zoneObjectIds before z != zoneObjectIds after z)

def zoneLine (g : Game) (z : Zone) (id : ObjectId) : String :=
  match g.findObject? id with
  | none => s!"{id} (missing)"
  | some o =>
    match z with
    | .hand _ => handLine g id
    | .battlefield => objectLine g o
    | .stack =>
      let ctrl :=
        match o.controller with
        | some p => s!" (controlled by {g.player p |>.name})"
        | none => ""
      s!"{o.id} {o.name}{ctrl}"
    | _ => s!"{o.id} {o.name}"

/-- Current contents of `z`. Libraries are hidden, so only their size is shown. -/
def zoneBlock (g : Game) (z : Zone) : String :=
  let ids := zoneObjectIds g z
  let shown :=
    match z with
    | .stack => ids.reverse
    | _ => ids
  let title := s!"zone {zoneLabel g z} ({shown.size})"
  match z with
  | .library _ => title
  | _ =>
    if shown.isEmpty then s!"{title}: (empty)"
    else
      let lines := shown.toList.map (zoneLine g z)
      title ++ ":\n  " ++ String.intercalate "\n  " lines

end Mtg.Engine.Render
