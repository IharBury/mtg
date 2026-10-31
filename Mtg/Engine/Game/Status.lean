import Mtg.Engine.Card.CardDef
import Mtg.Engine.Card.Counter
import Mtg.Engine.Deck
import Mtg.Engine.Mana
import Mtg.Engine.Rng
import Mtg.Engine.Rules
import Mtg.Engine.Turn
import Mtg.Engine.Zone

/-!
# Permanent status (CR 110.5)

The `Status` a permanent carries: tapping, damage, combat state, counters,
until-end-of-turn effects, and the `untilEotFields` table cleanup folds to
clear them (CR 514.3).
-/

namespace Mtg.Engine

/-- What an attacking creature is attacking (CR 508.1b / 506.3). -/
inductive AttackTarget where
  | player (p : PlayerId)
  | planeswalker (pw : ObjectId)
  | battle (b : ObjectId)            -- non-goal today (508.1b)
deriving DecidableEq, Repr, Inhabited, BEq

/-- Permanent status (CR 110.5) and designations (CR 400.7 / 701.54b). -/
structure Status where
  tapped : Bool := false
  damage : Int := 0
  summoningSick : Bool := true
  attacking : Bool := false
  /-- Player, planeswalker, or battle this creature is attacking (CR 508.1b / 506.3).
  Set with `attacking`. -/
  attackingTarget : Option AttackTarget := none
  /-- Attacking creatures this creature is blocking (CR 509.1a / 510.1d). -/
  blocking : Array ObjectId := #[]
  /-- Set when this attacker becomes blocked (CR 509.1h). Remains true even if
  every blocking creature leaves combat. -/
  blocked : Bool := false
  /-- Counters carried by this object (CR 122.1). -/
  counters : CounterBag := #[]
  /-- This permanent is prepared (Reality Fracture). -/
  prepared : Bool := false
  /-- Phased out (CR 702.26). Treated as though it does not exist. -/
  phasedOut : Bool := false
  /-- Host this Aura or Equipment phased out with. -/
  phasedWith : Option ObjectId := none
  /-- The Mind Stone (or similar) has been harnessed. -/
  harnessed : Bool := false
  /-- This permanent is currently showing its back face (MSH modal DFC). -/
  transformed : Bool := false
  /-- Odd/even choice (Gollum). `none` until chosen; `some true` is odd. -/
  chosenOdd : Option Bool := none
  /-- Creature type chosen as this permanent entered (Unexpected Party). -/
  chosenCreatureType : Option CardSubtype := none
  /-- Color chosen as this permanent entered (Room of Refuge). -/
  chosenColor : Option Color := none
  /-- Card name chosen as this permanent entered (Meddling Mage). -/
  chosenName : Option String := none
  /-- Face down (morph, CR 702.37). A 2/2 creature with no abilities. -/
  faceDown : Bool := false
  /-- Goaded for as long as this flag remains (CR 701.15b). -/
  goaded : Bool := false
  /-- Players currently goading this permanent (CR 701.15b). -/
  goadedBy : Array PlayerId := #[]
  /-- Players whose goad designation on this permanent ends as their next turn
  begins (CR 701.15a). -/
  goadedUntilNextTurnOf : Array PlayerId := #[]
  /-- Anchor word chosen as this permanent entered the battlefield (CR 614.12 / 700.2). -/
  chosenAnchor : Option String := none
  /-- Card type chosen as this permanent entered (Serra's Emissary). -/
  chosenCardType : Option CardType := none
deriving Repr, Inhabited, BEq

namespace Status

/-- Count of `k` counters on `s` (CR 122.1). -/
@[inline] def counterCount (s : Status) (k : CounterKind) : Nat :=
  s.counters.count k

@[inline] def plusOnePlusOne (s : Status) : Nat := s.counters.count .plusOnePlusOne
@[inline] def minusOneMinusOne (s : Status) : Nat := s.counters.count .minusOneMinusOne
@[inline] def loyaltyCounters (s : Status) : Nat := s.counters.count .loyalty
@[inline] def hope (s : Status) : Nat := s.counters.count .hope
@[inline] def charge (s : Status) : Nat := s.counters.count .charge
@[inline] def stun (s : Status) : Nat := s.counters.count .stun
@[inline] def hone (s : Status) : Nat := s.counters.count .hone
@[inline] def shadow (s : Status) : Nat := s.counters.count .shadow
@[inline] def shield (s : Status) : Nat := s.counters.count .shield
@[inline] def finality (s : Status) : Nat := s.counters.count .finality
@[inline] def plan (s : Status) : Nat := s.counters.count .plan
@[inline] def lore (s : Status) : Nat := s.counters.count .lore
@[inline] def indestructibleCounters (s : Status) : Nat := s.counters.count .indestructible
@[inline] def lifelinkCounters (s : Status) : Nat := s.counters.count .lifelink
@[inline] def influence (s : Status) : Nat := s.counters.count .influence
@[inline] def burden (s : Status) : Nat := s.counters.count .burden
@[inline] def quest (s : Status) : Nat := s.counters.count .quest
@[inline] def invasion (s : Status) : Nat := s.counters.count .invasion
@[inline] def trampleCounters (s : Status) : Nat := s.counters.count .trample
@[inline] def story (s : Status) : Nat := s.counters.count .story
@[inline] def time (s : Status) : Nat := s.counters.count .time
@[inline] def poison (s : Status) : Nat := s.counters.count .poison

@[inline] def keywordCounters (s : Status) : KeywordCounters :=
  { haste := s.counters.count .haste
    vigilance := s.counters.count .vigilance
    flying := s.counters.count .flying
    menace := s.counters.count .menace
    reach := s.counters.count .reach
    deathtouch := s.counters.count .deathtouch
    firstStrike := s.counters.count .firstStrike
    doubleStrike := s.counters.count .doubleStrike }

/-- True when this permanent has a counter (CR 122.1). -/
def hasCounters (s : Status) : Bool :=
  s.counters.any (fun (_, n) => n > 0)

/-- Snapshot of all non-zero counter kinds on `s` as a `CounterBag` (CR 122.1). -/
def toCounterBag (s : Status) : CounterBag :=
  s.counters.canonical

/-- Replace the counter fields of `s` with the counts in `bag` (CR 122.1). -/
def withCounterBag (s : Status) (bag : CounterBag) : Status :=
  { s with counters := bag.canonical }

/-- Add all counters in `bag` to `s` (CR 122.1). -/
def addCounterBag (s : Status) (bag : CounterBag) : Status :=
  { s with counters := s.counters.merge bag }

/-- The planeswalker `s` is attacking, if any (CR 506.3 / 508.1b). -/
def attackingPlaneswalker? (s : Status) : Option ObjectId :=
  match s.attackingTarget with
  | some (.planeswalker pw) => some pw
  | _ => none

/-- The player `s` is directly attacking, if any (CR 508.1b). -/
def attackingPlayer? (s : Status) : Option PlayerId :=
  match s.attackingTarget with
  | some (.player p) => some p
  | _ => none

end Status

#guard
  let s : Status := ({ damage := 3 } : Status).withCounterBag #[(.plusOnePlusOne, 2)]
  s.hasCounters && s.plusOnePlusOne == 2
#guard !({} : Status).hasCounters

end Mtg.Engine
