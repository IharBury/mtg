import Mtg.Engine.Card.Definition.Selector

/-!
# Costs

A payment in an activated ability or an additional cost (CR 601.2b / 602.1).
-/

namespace Mtg.Engine

/-- A payment in an activated-ability or additional cost (CR 601.2b / 602.1). -/
inductive Cost where
  | mana : List ManaSymbol → Cost
  /-- Pay that much life (CR 118.3). -/
  | life : Nat → Cost
  /-- Sacrifice every selected permanent (CR 701.17). -/
  | sacrifice : Selector → Cost
  /-- Sacrifice that many permanents matching the selector (CR 701.17).
  Use this to sacrifice one of a set; `sacrifice` would take all of them. -/
  | sacrificeCount : Selector → Nat → Cost
  /-- The `{T}` tap symbol (CR 107.5 / 302.6). Affected by summoning
  sickness. -/
  | tapSymbol
  /-- Discard a selected card (CR 701.9 / 702.29). -/
  | discard : Selector → Cost
  /-- Pay one of the listed costs. -/
  | or : List Cost → Cost
deriving Repr, Inhabited, BEq

namespace Cost

def manaCost : List Cost → ManaCost
  | [] => ManaCost.empty
  | .mana syms :: rest =>
    { symbols := (syms : ManaCost).symbols ++ (manaCost rest).symbols }
  | _ :: rest => manaCost rest

def lifePaid : List Cost → Nat
  | [] => 0
  | .life n :: rest => n + lifePaid rest
  | _ :: rest => lifePaid rest

def isSacArtifactOrCreature : Cost → Bool
  | .sacrificeCount s 1 => s.shape.types.eqTypes [.artifact, .creature]
  | .or cs =>
    cs.any fun
      | .sacrificeCount s 1 => s.shape.types.eqTypes [.artifact, .creature]
      | _ => false
  | _ => false

def sacrificesArtifactOrCreature : List Cost → Bool
  | [] => false
  | c :: rest => isSacArtifactOrCreature c || sacrificesArtifactOrCreature rest

def isSacOneCreature : Cost → Bool
  | .sacrificeCount s 1 => s.shape.types.eqTypes [.creature]
  | _ => false

/-- True when a cost sacrifices one creature and not an artifact-or-creature. -/
def sacrificesOneCreature : List Cost → Bool
  | [] => false
  | c :: rest =>
    (isSacOneCreature c && !isSacArtifactOrCreature c) || sacrificesOneCreature rest

def orPayGeneric? : List Cost → Option Nat
  | [] => none
  | .or cs :: rest =>
    match cs.findSome? fun
      | .mana [.generic n] => some n
      | _ => none with
    | some n => some n
    | none => orPayGeneric? rest
  | _ :: rest => orPayGeneric? rest

def hasTapSymbol : List Cost → Bool
  | [] => false
  | .tapSymbol :: _ => true
  | _ :: rest => hasTapSymbol rest

/-- True when a cost sacrifices this object. -/
def sacrificesThis : List Cost → Bool
  | [] => false
  | .sacrifice s :: rest =>
    (s == .this || s == .source .this) || sacrificesThis rest
  | _ :: rest => sacrificesThis rest

/-- Sacrifice one legendary artifact as part of the cost. -/
def sacrificesLegendaryArtifact (costs : List Cost) : Bool :=
  costs.any fun
    | .sacrificeCount s 1 =>
      s == .intersection [.zone .battlefield, .cardType .artifact, .supertype .legendary]
    | _ => false

/-- Sacrifice one artifact as part of the cost. -/
def sacrificesArtifact (costs : List Cost) : Bool :=
  costs.any fun
    | .sacrificeCount s 1 => s == .intersection [.zone .battlefield, .cardType .artifact]
    | _ => false

/-- Sacrifice another permanent you control of a printed subtype. -/
def sacrificeAnotherSubtype? : List Cost → Option String
  | [] => none
  | .sacrificeCount s 1 :: rest =>
    s.shape.anotherSubtypeYouControl.orElse fun _ =>
      sacrificeAnotherSubtype? rest
  | _ :: rest => sacrificeAnotherSubtype? rest

/-- True when a cost discards this object. -/
def discardsThis : List Cost → Bool
  | [] => false
  | .discard s :: rest =>
    (s == .this || s == .source .this) || discardsThis rest
  | _ :: rest => discardsThis rest

/-- This object's controller chooses one card they own in a hand. -/
def discardsOneCardFromHand : Selector → Bool
  | .selected (.controller .this) (.range (.nat 1) (.nat 1))
      (.intersection [.zone .hand, .owner (.controller .this)]) => true
  | _ => false

/-- `Discard a card or pay {N}` as one cost. -/
def discardOrPayGeneric? : List Cost → Option Nat
  | [.or [.discard s, .mana [.generic n]]] =>
    if discardsOneCardFromHand s && n != 0 then some n else none
  | _ => none

/-- True when a cost discards one card from hand, not this card. -/
def discardsACard : List Cost → Bool
  | [] => false
  | .discard s :: rest => discardsOneCardFromHand s || discardsACard rest
  | _ :: rest => discardsACard rest

end Cost

end Mtg.Engine
