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
abbrev Zone := Option (Option PlayerId × Bool × Bool)

namespace Zone

@[match_pattern] abbrev zoneKind (k : Option (Option PlayerId × Bool × Bool) := none) : Zone := k

/-- Per-player hidden zone; the player’s deck at the start of the game (CR 401). -/
@[match_pattern] abbrev library (owner : PlayerId) : Zone :=
  .zoneKind (some (some owner, false, false))
/-- Per-player hidden zone of drawn cards (CR 402). -/
@[match_pattern] abbrev hand (owner : PlayerId) : Zone :=
  .zoneKind (some (some owner, false, true))
/-- Per-player public discard pile (CR 404). -/
@[match_pattern] abbrev graveyard (owner : PlayerId) : Zone :=
  .zoneKind (some (some owner, true, false))
/-- Cards a player owns outside the game, such as their sideboard
(CR 400.11b). Not a zone; these cards aren't in the game. -/
@[match_pattern] abbrev outside (owner : PlayerId) : Zone :=
  .zoneKind (some (some owner, true, true))
/-- Shared public zone; objects here are permanents (CR 403). -/
@[match_pattern] abbrev battlefield : Zone :=
  .zoneKind (some (none, false, false))
/-- Shared public zone of pending spells and abilities (CR 405). -/
@[match_pattern] abbrev stack : Zone :=
  .zoneKind (some (none, false, true))
/-- Shared public holding area (CR 406). -/
@[match_pattern] abbrev exile : Zone :=
  .zoneKind (some (none, true, false))
/-- Shared public zone for commanders, emblems, schemes, etc. (CR 408). -/
@[match_pattern] abbrev command : Zone :=
  .zoneKind (some (none, true, true))
/-- Legacy “for keeps” zone (CR 407). -/
@[match_pattern] abbrev ante : Zone :=
  .zoneKind none

/-- Graveyard, battlefield, stack, exile, ante, and command are public (CR 400.2). -/
def isPublic : Zone → Bool
  | .library _ | .hand _ | .outside _ => false
  | .battlefield | .graveyard _ | .stack | .exile | .command | .ante => true

/-- Library and hand are hidden even if every card happens to be revealed (CR 400.2). -/
def isHidden (z : Zone) : Bool := !z.isPublic

/-- Each player has their own library, hand, and graveyard (CR 400.1). -/
def isOwned : Zone → Bool
  | .library _ | .hand _ | .graveyard _ => true
  | _ => false

def owner? : Zone → Option PlayerId
  | .library p | .hand p | .graveyard p | .outside p => some p
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
  | .outside p => s!"outside the game ({p})"

instance : ToString Zone where
  toString := englishName

#guard (Zone.hand ⟨0⟩).isHidden
#guard Zone.battlefield.isPublic
#guard !(Zone.stack.isOwned)

end Zone

end Mtg.Engine
