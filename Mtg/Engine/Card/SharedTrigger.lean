import Mtg.Engine.Card.PermanentAction
import Mtg.Engine.Card.SpellResolution
import Mtg.Engine.Card.TriggerEvent

/-!
# Shared trigger options and selector helpers (CR 603)

Helper enums and intervening-condition options used by triggered abilities.
-/

namespace Mtg.Engine

/-- How many counters `amass` puts on the Army. `.fixed` uses `n`. -/
inductive AmassAmount where
  /-- The `n` argument. -/
  | fixed
  /-- This creature's power, as it last existed. -/
  | sourcePower
  /-- Excess damage an earlier step recorded. Zero excess amasses nothing. -/
  | notedExcess
  /-- The power an earlier step recorded when it destroyed a creature.
  No destruction amasses nothing. -/
  | notedPower
deriving Repr, Inhabited, BEq, DecidableEq

/-- Who `SharedTrigger.connive` makes connive. -/
inductive ConniveSubject where
  /-- The trigger's source. -/
  | source
  /-- The announced target of this kind. -/
  | target (kind : EffectTargetKind)
  /-- The Villain that caused this trigger. You may have it connive.
  Already chosen this turn does nothing. A Villain that will not connive
  is reported. -/
  | enteringVillain
deriving Repr, Inhabited, BEq

/-- Who discards for `SharedTrigger.opponentDiscards`. -/
inductive OpponentDiscard where
  /-- Each opponent. -/
  | each
  /-- The announced opponent. -/
  | target
deriving Repr, Inhabited, BEq, DecidableEq

/-- An intervening “if” or trigger condition (CR 603.2 / 603.4). -/
inductive InterveningCondition where
  /-- “while you control a creature with power ≥ n” (e.g. Ferocious). -/
  | youControlCreatureWithPower (n : Int)
  /-- “if you gained `n` or more life this turn”. -/
  | gainedLifeAtLeast (n : Nat)
  /-- “another creature you control with power ≤ n”. -/
  | anotherCreaturePowerAtMost (n : Int)
  | none
  /-- “if it isn't a token” (the source, as it last existed). -/
  | sourceNotToken
  /-- “if two or more creatures died this turn”. -/
  | twoCreaturesDiedThisTurn
  /-- “if an opponent was dealt noncombat damage last turn”. -/
  | opponentDealtNoncombatDamageLastTurn
  /-- “if you've drawn three or more cards this turn”. -/
  | drewThreeThisTurn
  /-- “if you didn't cast a spell this turn”. -/
  | castNoSpellThisTurn
  /-- “if you've activated a loyalty ability this turn”. -/
  | activatedLoyaltyThisTurn
  /-- “if you cast it”. -/
  | sourceWasCast
  /-- “if it had counters on it” (the object that caused the trigger). -/
  | causeHadCounters
  /-- “if this has counters on it”. -/
  | sourceHasCounters
deriving Repr, Inhabited, BEq, DecidableEq

/-- Backward-compatible alias for `InterveningCondition` (CR 603.4). -/
abbrev FraCondition := InterveningCondition

/-- Optional intervening conditions and wording filters for `triggered` (CR 603). -/
structure SharedTriggerOpts where
  onceEachTurn : Bool := false
  /-- Intervening or event-threshold condition (CR 603.2 / 603.4). -/
  condition : InterveningCondition := .none
  /-- Subtype filter watched by the trigger event. -/
  subtype : Option String := none
  allowsZeroTargets : Bool := false
  /-- Drop targeting from the shared effect (e.g. Guttersnipe). -/
  untargeted : Bool := false
  /-- The ability's printed sentence, when its wording isn't built from the
  event and resolution (Reality Fracture). -/
  printed : String := ""
  /-- The other permanent must be legendary (“another legendary Elf”). -/
  anotherLegendary : Bool := false
deriving Repr, Inhabited, BEq

namespace SharedTriggerOpts

def youControlCreatureWithPower (o : SharedTriggerOpts) : Option Int :=
  match o.condition with
  | .youControlCreatureWithPower n => some n
  | _ => none

def gainedLifeAtLeast (o : SharedTriggerOpts) : Option Nat :=
  match o.condition with
  | .gainedLifeAtLeast n => some n
  | _ => none

def anotherCreaturePowerAtMost (o : SharedTriggerOpts) : Option Int :=
  match o.condition with
  | .anotherCreaturePowerAtMost n => some n
  | _ => none

def fraCondition (o : SharedTriggerOpts) : InterveningCondition :=
  match o.condition with
  | .youControlCreatureWithPower _ | .gainedLifeAtLeast _ | .anotherCreaturePowerAtMost _ => .none
  | c => c

def thisOrNontokenSubtype (o : SharedTriggerOpts) : Option String := o.subtype
def thisOrAnotherSubtype (o : SharedTriggerOpts) : Option String := o.subtype
def anotherSubtypeOrEquipment (o : SharedTriggerOpts) : Option String := o.subtype
def watchedSubtype (o : SharedTriggerOpts) : Option String := o.subtype

/-- Ferocious intervening condition (power 4 or greater). -/
def ferocious : SharedTriggerOpts :=
  { condition := .youControlCreatureWithPower 4 }

/-- “This ability triggers only once each turn.” -/
def once : SharedTriggerOpts :=
  { onceEachTurn := true }

/-- Shared effect has targeting; this printed ability does not. -/
def noTarget : SharedTriggerOpts :=
  { untargeted := true }

end SharedTriggerOpts

end Mtg.Engine
