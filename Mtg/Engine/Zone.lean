/-!
# Zones (CR 400)

A zone is a place where objects can be during a game. There are normally
seven zones: library, hand, battlefield, graveyard, stack, exile, and
command. Some older cards also use the ante zone.
-/

namespace Mtg.Engine

/-- Identifier for a player, used as an index into `Game.players` (CR 102). -/
structure PlayerId where
  idx : Nat
deriving DecidableEq, Repr, Hashable, Inhabited, BEq

instance : ToString PlayerId where
  toString p := s!"Player {p.idx}"

/-- Unique identity of an in-game object. Moving zones assigns a new id (CR 400.7). -/
structure ObjectId where
  raw : Nat
deriving DecidableEq, Repr, Hashable, Inhabited, BEq

instance : ToString ObjectId where
  toString o := s!"#{o.raw}"

/-- The zones of the game (CR 400.1). -/
inductive Zone where
  /-- Per-player hidden zone; the player’s deck at the start of the game (CR 401). -/
  | library (owner : PlayerId)
  /-- Per-player hidden zone of drawn cards (CR 402). -/
  | hand (owner : PlayerId)
  /-- Shared public zone; objects here are permanents (CR 403). -/
  | battlefield
  /-- Per-player public discard pile (CR 404). -/
  | graveyard (owner : PlayerId)
  /-- Shared public zone of pending spells and abilities (CR 405). -/
  | stack
  /-- Shared public holding area (CR 406). -/
  | exile
  /-- Shared public zone for commanders, emblems, schemes, etc. (CR 408). -/
  | command
  /-- Legacy “for keeps” zone (CR 407). -/
  | ante
deriving DecidableEq, Repr, Inhabited, BEq

namespace Zone

/-- Graveyard, battlefield, stack, exile, ante, and command are public (CR 400.2). -/
def isPublic : Zone → Bool
  | .library _ | .hand _ => false
  | .battlefield | .graveyard _ | .stack | .exile | .command | .ante => true

/-- Library and hand are hidden even if every card happens to be revealed (CR 400.2). -/
def isHidden (z : Zone) : Bool := !z.isPublic

/-- Each player has their own library, hand, and graveyard (CR 400.1). -/
def isOwned : Zone → Bool
  | .library _ | .hand _ | .graveyard _ => true
  | _ => false

def owner? : Zone → Option PlayerId
  | .library p | .hand p | .graveyard p => some p
  | _ => none

def englishName : Zone → String
  | .library p => s!"{p}'s library"
  | .hand p => s!"{p}'s hand"
  | .battlefield => "battlefield"
  | .graveyard p => s!"{p}'s graveyard"
  | .stack => "stack"
  | .exile => "exile"
  | .command => "command"
  | .ante => "ante"

instance : ToString Zone where
  toString := englishName

#guard (Zone.hand ⟨0⟩).isHidden
#guard Zone.battlefield.isPublic
#guard !(Zone.stack.isOwned)

end Zone

end Mtg.Engine
