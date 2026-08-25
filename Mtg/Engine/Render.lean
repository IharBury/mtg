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

/-- Keywords and abilities printed after a card's name (and P/T). -/
def faceExtras (c : CardDef) : String :=
  let s := c.keywordsAndAbilities
  if s.isEmpty then "" else s!" {s}"

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
  s!"{o.id} {o.name}{pt}{faceExtras o.printed}{controlClause g o}{tap}{atk}{blk}{dmg}"

def handLine (g : Game) (id : ObjectId) : String :=
  match g.findObject? id with
  | none => s!"{id} (missing)"
  | some o => s!"{o.id} {o.printed.summary}"

/-- Whether `viewer` may look at card faces in `z` (CR 400.2, 401.2, 402.2).
`none` is omniscient: public zones and hands are shown, but libraries stay
face-down even to their owner. -/
def canSeeZoneFaces (viewer : Option PlayerId) : Zone → Bool
  | .library _ => false
  | .hand p =>
    match viewer with
    | none => true
    | some v => v == p
  | .battlefield | .graveyard _ | .stack | .exile | .command | .ante => true

def playerBlock (g : Game) (pl : Player) (viewer : Option PlayerId := none) : String :=
  let marker := if pl.id == g.activePlayer then " (active)" else ""
  let bf := (g.permanentsOf pl.id).toList.map (objectLine g)
  let bfText := if bf.isEmpty then "  (none)" else String.intercalate "\n  " bf
  let handText :=
    if canSeeZoneFaces viewer (.hand pl.id) then
      let hand := pl.hand.toList.map (handLine g)
      if hand.isEmpty then "  (empty)" else String.intercalate "\n  " hand
    else
      "  (hidden)"
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
      | some o => s!"  {o.name}{faceExtras o.printed} (controlled by {g.player e.controller |>.name})"
      | none => "  (missing)")
    "Stack (top first):\n" ++ String.intercalate "\n" lines

def header (g : Game) (viewer : Option PlayerId := none) : String :=
  let viewTag :=
    match viewer with
    | none => ""
    | some p => s!" [{g.player p |>.name}'s view]"
  let pending :=
    match g.pending with
    | .none => ""
    | .declareAttackers => " [declare attackers]"
    | .declareBlockers => " [declare blockers]"
    | .activateManaAbilities _ => " [activate mana abilities (CR 601.2g)]"
    | .declareMulligan p =>
      s!" [mulligan: {g.player p |>.name} may keep or mulligan (CR 103.5)]"
    | .putOnBottom p n =>
      let cards := if n == 1 then "1 card" else s!"{n} cards"
      s!" [mulligan: {g.player p |>.name} puts {cards} on the bottom (CR 103.5)]"
  let result :=
    match g.result with
    | none => ""
    | some (.won p) => s!"  RESULT: {g.player p |>.name} wins"
    | some .draw => "  RESULT: draw"
  if g.openingHandsPending then
    s!"Opening hands{viewTag}{pending}{result}"
  else
    s!"Turn {g.turnNumber} · {g.step} · priority: {g.player g.priority |>.name}{viewTag}{pending}{result}"

def snapshot (g : Game) (viewer : Option PlayerId := none) : String :=
  let players := g.players.toList.map (fun pl => playerBlock g pl viewer)
  String.intercalate "\n\n" (header g viewer :: stackBlock g :: players)

/-- Hide draws and library-bottoming that `viewer` is not allowed to see
(CR 401.2, 402.2, 103.5). Other log lines are public. -/
def redactLogLine (g : Game) (viewer : PlayerId) (line : String) : String :=
  Id.run do
    for pl in g.players do
      if pl.id != viewer then
        let drawPrefix := s!"{pl.name} draws "
        if line.startsWith drawPrefix then
          return s!"{pl.name} draws a card"
        let bottomPrefix := s!"{pl.name} puts "
        let bottomSuffix := " on the bottom of their library"
        if line.startsWith bottomPrefix && line.endsWith bottomSuffix then
          return s!"{pl.name} puts a card on the bottom of their library"
    return line

/-- New log lines starting at `startIdx`, optionally redacted for `viewer`. -/
def newLog (g : Game) (startIdx : Nat) (viewer : Option PlayerId := none) : Array String :=
  let lines := g.log.extract startIdx g.log.size
  match viewer with
  | none => lines
  | some p => lines.map (redactLogLine g p)

/-- Current life total, matching the snapshot's `life N` fragment. -/
def lifeLine (pl : Player) : String :=
  s!"{pl.name} — life {pl.life}"

/-- Players whose life totals differ between two game states. -/
def changedLifeTotals (before after : Game) : Array Player :=
  after.players.filter (fun pl => (before.player pl.id).life != pl.life)

/-- Current mana pool, matching the snapshot's `mana {pool}` fragment. -/
def manaLine (pl : Player) : String :=
  s!"{pl.name} — mana {pl.manaPool}"

/-- Players whose mana pools differ between two game states. -/
def changedManaPools (before after : Game) : Array Player :=
  after.players.filter (fun pl => (before.player pl.id).manaPool != pl.manaPool)

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

/-- Permanents grouped by controller, in seat order (CR 110.2). Empty groups
are omitted. Permanents with no controller are listed last. -/
def battlefieldGroups (g : Game) : Array (String × Array GameObject) :=
  Id.run do
    let mut groups : Array (String × Array GameObject) := #[]
    for pl in g.players do
      let ps := g.permanentsOf pl.id
      if !ps.isEmpty then
        groups := groups.push (pl.name, ps)
    let uncontrolled := g.battlefield.filter (fun o => o.controller.isNone)
    if !uncontrolled.isEmpty then
      groups := groups.push ("(no controller)", uncontrolled)
    return groups

/-- Shared-zone battlefield lines grouped under each controller's name. -/
def battlefieldGroupLines (g : Game) : List String :=
  Id.run do
    let mut lines : Array String := #[]
    for (label, os) in battlefieldGroups g do
      lines := lines.push s!"{label}:"
      for o in os do
        lines := lines.push s!"  {objectLine g o}"
    return lines.toList

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
      s!"{o.id} {o.name}{faceExtras o.printed}{ctrl}"
    | _ => s!"{o.id} {o.name}{faceExtras o.printed}"

/-- Current contents of `z`. Hidden zones show only their size (CR 400.2). -/
def zoneBlock (g : Game) (z : Zone) (viewer : Option PlayerId := none) : String :=
  let ids := zoneObjectIds g z
  let shown :=
    match z with
    | .stack => ids.reverse
    | _ => ids
  let title := s!"zone {zoneLabel g z} ({shown.size})"
  if !canSeeZoneFaces viewer z then
    title
  else if shown.isEmpty then
    s!"{title}: (empty)"
  else
    let lines :=
      match z with
      | .battlefield => battlefieldGroupLines g
      | _ => shown.toList.map (zoneLine g z)
    title ++ ":\n  " ++ String.intercalate "\n  " lines

end Mtg.Engine.Render
