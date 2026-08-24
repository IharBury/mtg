import Mtg.Engine.Game

/-!
# Text rendering of a game for the console demo.
-/

namespace Mtg.Engine.Render

open Mtg.Engine
open Mtg.Engine.Game

def objectLine (o : GameObject) : String :=
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
  s!"{o.id} {o.name}{pt}{tap}{atk}{blk}{dmg}"

def handLine (g : Game) (id : ObjectId) : String :=
  match g.findObject? id with
  | none => s!"{id} (missing)"
  | some o => s!"{o.id} {o.printed.summary}"

def playerBlock (g : Game) (pl : Player) : String :=
  let marker := if pl.id == g.activePlayer then " (active)" else ""
  let bf := (g.permanentsOf pl.id).toList.map objectLine
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

end Mtg.Engine.Render
