import Mtg.Engine.Card.CardDef
import Mtg.Engine.Card.Keywords
import Mtg.Engine.Card.SpellEffects
import Mtg.Engine.Card.TriggeredAbility
import Mtg.Engine.Mana
import Mtg.Engine.TypeLine

/-!
# Traditional card definitions

A printed card as a list of `CardPart`s: name, mana cost, type line,
abilities, and (for adventurer cards) an `alternative` face. Compiles to
`CardDef` so the engine and existing catalogs stay unchanged.
-/

namespace Mtg.Engine

/-- How many objects a `.targets` selector may choose. -/
inductive Range where
  | range : Nat → Nat → Range
deriving Repr, Inhabited, BEq

/-- A constraint on a set of selected objects, not on each object alone. -/
inductive SetPredicate where
  /-- The objects share a card type with each other. -/
  | shareCardType
deriving Repr, Inhabited, BEq

/-- Whom or what a spell or ability refers to (CR 109.5 / 113.7 / 115.1). -/
inductive Selector where
  /-- This spell or ability (CR 113.7). -/
  | this
  /-- The source of the given object (CR 113.7). -/
  | source : Selector → Selector
  /-- The controller of the given object (CR 109.5). -/
  | controller : Selector → Selector
  /-- A numbered target matching the given selector (CR 115.1). Later
  effects may refer to it with `targetReference`. -/
  | target : Nat → Selector → Selector
  /-- Numbered targets matching the given selector, with a count range. -/
  | targets : Nat → Range → Selector → Selector
  /-- Numbered targets matching the given selector, with a count range
  and extra constraints that apply to the set as a whole. -/
  | targetSet : Nat → Range → Selector → List SetPredicate → Selector
  /-- Objects that do not match the given selector. -/
  | not : Selector → Selector
  /-- The target previously declared with `target` of this number. -/
  | targetReference : Nat → Selector
  /-- The object bound by `forEach` of this number. -/
  | var : Nat → Selector
  /-- Choose objects matching the given selector at resolution, with a
  count range (not targeting; CR 608.2d). -/
  | selected : Range → Selector → Selector
  /-- Every object targeted by anything matching the given selector
  (CR 115.1 / 608.2b). -/
  | allTargets : Selector → Selector
  | intersection : List Selector → Selector
  | all
  | cardType : CardType → Selector
  | union : List Selector → Selector
  /-- A permanent (CR 110.1). -/
  | permanent
  /-- Objects whose controller is the given player. -/
  | controlled : Selector → Selector
  /-- A tapped permanent (CR 110.5). -/
  | tapped
  /-- Printed subtype (CR 205.3). -/
  | subtype : CardSubtype → Selector
  /-- A spell on the stack (CR 112.1). -/
  | spell
  /-- A player (CR 102). -/
  | player
  /-- Opponents of the given player (CR 102.2). -/
  | opponent : Selector → Selector
  /-- The owner of the given object (CR 108.3). -/
  | owner : Selector → Selector
  /-- A permanent attacking objects matching the given selector (CR 508). -/
  | attacking : Selector → Selector
  /-- A token (CR 111.1). -/
  | token
  /-- A nonland permanent (CR 110.4). -/
  | nonland
  /-- The object of the numbered action. -/
  | wasObjectOfAction : Nat → Selector
  /-- The object a replacement effect is replacing. -/
  | replacingObject : Nat → Selector
  /-- An object created by the numbered action. -/
  | wasCreatedByAction : Nat → Selector
deriving Repr, Inhabited, BEq

namespace Selector

/-- Card types a selector allows. `any` means the selector does not mention type. -/
inductive TypeSet where
  | any
  | oneOf (ts : List CardType)
deriving Repr, Inhabited, BEq

namespace TypeSet

def intersect : TypeSet → TypeSet → TypeSet
  | .any, s | s, .any => s
  | .oneOf a, .oneOf b => .oneOf (a.filter b.contains)

def union : TypeSet → TypeSet → TypeSet
  | .any, _ | _, .any => .any
  | .oneOf a, .oneOf b =>
    .oneOf (a ++ b.filter (fun t => !a.contains t))

def contains (s : TypeSet) (t : CardType) : Bool :=
  match s with
  | .any => true
  | .oneOf ts => ts.contains t

/-- True when `s` is exactly the listed types, ignoring order. -/
def eqTypes (s : TypeSet) (ts : List CardType) : Bool :=
  match s with
  | .any => false
  | .oneOf us => us.all ts.contains && ts.all us.contains

end TypeSet

/-- Flattened constraints implied by a selector, so `.intersection` / `.union`
lists compile without depending on conjunct order. -/
structure Shape where
  sameController : Bool := false
  opponentControls : Bool := false
  mustBePermanent : Bool := false
  tapped : Bool := false
  attacking : Bool := false
  token : Bool := false
  nontoken : Bool := false
  other : Bool := false
  subtype : Option String := none
  types : TypeSet := .any
  isSpell : Bool := false
  nonland : Bool := false
  shareCardType : Bool := false
deriving Repr, Inhabited, BEq

namespace Shape

def meet (a b : Shape) : Shape :=
  { sameController := a.sameController || b.sameController
    opponentControls := a.opponentControls || b.opponentControls
    mustBePermanent := a.mustBePermanent || b.mustBePermanent
    tapped := a.tapped || b.tapped
    attacking := a.attacking || b.attacking
    token := a.token || b.token
    nontoken := a.nontoken || b.nontoken
    other := a.other || b.other
    subtype := a.subtype.orElse fun _ => b.subtype
    types := a.types.intersect b.types
    isSpell := a.isSpell || b.isSpell
    nonland := a.nonland || b.nonland
    shareCardType := a.shareCardType || b.shareCardType }

def join (a b : Shape) : Shape :=
  { sameController := a.sameController && b.sameController
    opponentControls := a.opponentControls && b.opponentControls
    mustBePermanent := a.mustBePermanent && b.mustBePermanent
    tapped := a.tapped && b.tapped
    attacking := a.attacking && b.attacking
    token := a.token && b.token
    nontoken := a.nontoken && b.nontoken
    other := a.other && b.other
    subtype :=
      match a.subtype, b.subtype with
      | some x, some y => if x == y then some x else none
      | _, _ => none
    types := a.types.union b.types
    isSpell := a.isSpell && b.isSpell
    nonland := a.nonland && b.nonland
    shareCardType := a.shareCardType && b.shareCardType }

/-- True when this shape is a tapped creature (optional permanent conjunct). -/
def tappedCreature (s : Shape) : Bool :=
  s.tapped && s.types.eqTypes [.creature]

/-- True when this shape is a Dwarf. -/
def dwarf (s : Shape) : Bool :=
  s.subtype == some "Dwarf"

/-- True when this shape is an attacking nontoken creature. -/
def attackingNontokenCreature (s : Shape) : Bool :=
  s.attacking && s.nontoken && s.types.eqTypes [.creature]

/-- True when this shape is other creatures. -/
def otherCreatures (s : Shape) : Bool :=
  s.other && s.types.eqTypes [.creature]

/-- Negate a constraint-shaped selector. `.not` of a land type is nonland;
`.not` of a token is nontoken. -/
def negate (s : Shape) : Shape :=
  if s.types.eqTypes [.land] then { nonland := true }
  else if s.token then { nontoken := true }
  else {}

end Shape

def shape : Selector → Shape
  | .all => {}
  | .permanent => { mustBePermanent := true }
  | .controlled (.controller .this) => { sameController := true }
  | .controlled (.opponent _) => { opponentControls := true }
  | .controlled _ => {}
  | .tapped => { tapped := true }
  | .attacking _ => { attacking := true }
  | .token => { token := true }
  | .subtype st => { subtype := some st.toString }
  | .cardType t => { types := .oneOf [t] }
  | .spell => { isSpell := true }
  | .nonland => { nonland := true }
  | .not .this => { other := true }
  | .not s => s.shape.negate
  | .intersection fs => fs.foldl (fun acc f => acc.meet f.shape) {}
  | .union [] => {}
  | .union (f :: fs) => fs.foldl (fun acc g => acc.join g.shape) f.shape
  | .this | .source _ | .controller _ | .opponent _ | .owner _ | .target _ _
  | .targets _ _ _ | .targetSet _ _ _ _ | .targetReference _ | .var _
  | .selected _ _ | .allTargets _ | .player
  | .wasObjectOfAction _ | .replacingObject _ | .wasCreatedByAction _ => {}

/-- Apply set-wide predicates onto an object-level shape. -/
def applySetPredicates (s : Shape) : List SetPredicate → Shape
  | [] => s
  | .shareCardType :: rest =>
    applySetPredicates { s with shareCardType := true } rest

/-- Shape used for targeting: unwrap `target` / `targets` / `targetSet`
and fold in set predicates. -/
def targetingShape : Selector → Shape
  | .target _ among => among.shape
  | .targets _ _ among => among.shape
  | .targetSet _ _ among preds => applySetPredicates among.shape preds
  | s => s.shape

/-- Compile a selector to a targeting shape the engine already understands. -/
def toTargetKind (f : Selector) : EffectTargetKind :=
  let s := f.targetingShape
  if s.isSpell then .spell
  else if s.nonland && s.shareCardType then .twoNonlandsSharingType
  else if s.nonland then .nonland
  else if s.opponentControls && s.types.eqTypes [.creature] then .oppCreature
  else if s.sameController then
    if s.types.eqTypes [.artifact, .creature] then .artifactOrCreatureYouControl
    else if s.types.eqTypes [.creature] then .creatureYouControl
    else if s.types.eqTypes [.artifact] then .artifactYouControl
    else .permanent
  else if s.types.eqTypes [.creature] then .creature
  else if s.types.eqTypes [.artifact] then .artifact
  else .permanent

/-- The constraint a targeting selector matches, if it announces targets. -/
def among? : Selector → Option Selector
  | .target _ among => some among
  | .targets _ _ among => some among
  | .targetSet _ _ among _ => some among
  | _ => none

/-- Any object. -/
def any : Selector := .all

/-- A land (CR 305). -/
def land : Selector := .cardType .land

def toTargeting (s : Selector) : EffectTargeting :=
  match s.among? with
  | some _ => .of s.toTargetKind
  | none => .of .none

end Selector

/-- A payment in an activated-ability or additional cost (CR 601.2b / 602.1). -/
inductive Cost where
  | mana : List ManaSymbol → Cost
  /-- Pay that much life (CR 118.3). -/
  | life : Nat → Cost
  /-- Sacrifice a selected permanent (CR 701.17). -/
  | sacrifice : Selector → Cost
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
  | .sacrifice s => s.shape.types.eqTypes [.artifact, .creature]
  | .or cs =>
    cs.any fun
      | .sacrifice s => s.shape.types.eqTypes [.artifact, .creature]
      | _ => false
  | _ => false

def sacrificesArtifactOrCreature : List Cost → Bool
  | [] => false
  | c :: rest => isSacArtifactOrCreature c || sacrificesArtifactOrCreature rest

def orPayGeneric? : List Cost → Option Nat
  | [] => none
  | .or cs :: rest =>
    match cs.findSome? fun
      | .mana [.generic n] => some n
      | _ => none with
    | some n => some n
    | none => orPayGeneric? rest
  | _ :: rest => orPayGeneric? rest

end Cost

/-- A limit on how often an activated ability may be activated. -/
inductive ActivationRestriction where
  | onceEachTurn
deriving Repr, Inhabited, BEq

/-- Where an `ordinal` count starts. -/
inductive CountFrom where
  /-- From the start of the turn. -/
  | turnStart
deriving Repr, Inhabited, BEq

/-- When a continuous effect ends, when a triggered ability fires, or
what a replacement effect intercepts. -/
inductive Trigger where
  | endOfGame
  | endOfTurn
  /-- Whenever the selected object attacks, restricted by the given
  selector. -/
  | attack : Selector → Selector → Trigger
  /-- When the selected object enters. -/
  | enter : Selector → Trigger
  /-- Whenever the selected player draws a card matching the given
  selector. -/
  | draw : Selector → Selector → Trigger
  /-- The nth occurrence of the inner trigger, counted from the given
  point. -/
  | ordinal : Nat → CountFrom → Trigger → Trigger
  /-- Whenever the selected object deals combat damage to objects matching
  the given selector. -/
  | combatDamage : Selector → Selector → Trigger
  /-- The selected object would be put into a graveyard (CR 614). -/
  | putToGraveyard : Selector → Trigger
  /-- The first selector blocks the second (CR 509). -/
  | block : Selector → Selector → Trigger
  /-- When the selected object or objects die (CR 700.4). -/
  | die : Selector → Trigger
  /-- When objects matching the selector die at the same time, with
  set-wide predicates (CR 700.4 / 603.2d). -/
  | dieSimultaneously : Selector → List SetPredicate → Trigger
deriving Repr, Inhabited, BEq

/-- Kind of counter placed by `putCounter` (CR 122.1). -/
inductive CounterKind where
  /-- A +1/+1 counter. -/
  | plusOnePlusOne
deriving Repr, Inhabited, BEq

-- Printed abilities, continuous effects, and actions are mutually inductive:
-- an activated ability has an action, and a continuous effect may grant an
-- ability.
mutual
/-- A keyword or other printed ability on a card or granted by an effect. -/
inductive Ability where
  | keyword : Keyword → Ability
  | activated : List Cost → CardAction → Ability
  /-- An activated ability that may be used that many times, counted from
  the given point. -/
  | activatedTimes : Nat → CountFrom → List Cost → CardAction → Ability
  | triggered : Trigger → CardAction → Ability
  | static : ContinuousEffect → Ability
  | reduceCost : Selector → List Cost → Ability
  /-- Restrict how often or when the inner ability may be used. -/
  | restrict : ActivationRestriction → Ability → Ability
deriving Repr, Inhabited, BEq

/-- A continuous effect granted by a spell or ability. -/
inductive ContinuousEffect where
  | gainAbility : Selector → Ability → ContinuousEffect
  | addPowerToughness : Selector → Int → Int → ContinuousEffect
  /-- Apply the given continuous effects only when the selector matches
  anything. -/
  | ifAny : Selector → List ContinuousEffect → ContinuousEffect
  | reduceCost : Selector → List Cost → ContinuousEffect
  /-- An additional cost to cast the selected spell (CR 601.2b). -/
  | additionalCost : Selector → List Cost → ContinuousEffect
  /-- Replace the trigger with the given actions (CR 614). -/
  | replace : Trigger → List CardAction → ContinuousEffect
  /-- The selected trigger is forbidden (CR 509 / 614). -/
  | forbid : Trigger → ContinuousEffect
  /-- The selected player may cast the selected card without paying its
  mana cost. -/
  | canCastWithoutPayingManaCost : Selector → Selector → ContinuousEffect
deriving Repr, Inhabited, BEq

/-- What a spell or ability does. `CardAction` is the printed-card name for
this tree; player input uses `Action` in `Game`. -/
inductive CardAction where
  | continuous : List ContinuousEffect → Trigger → CardAction
  | tap : Selector → CardAction
  | untap : Selector → CardAction
  | dealDamage : Selector → Selector → Nat → CardAction
  | draw : Selector → Nat → CardAction
  | scry : Selector → Nat → CardAction
  | sequence : List CardAction → CardAction
  | forEach : Nat → CardAction → CardAction
  /-- Perform the given actions only when the selector matches anything. -/
  | ifAny : Selector → List CardAction → CardAction
  | optional : CardAction → CardAction
  | attach : Selector → Selector → CardAction
  /-- Choose one of the given modes (CR 700.2). -/
  | chooseMode : List CardAction → CardAction
  /-- Counter the selected spell (CR 701.5). -/
  | counter : Selector → CardAction
  /-- The given player may pay the cost to prevent the action. -/
  | preventable : Selector → List Cost → CardAction → CardAction
  /-- The selected player discards that many cards. -/
  | discard : Selector → Nat → CardAction
  /-- Put that many counters of the given kind on the selected object. -/
  | putCounter : Selector → CounterKind → Nat → CardAction
  /-- Exile the selected object. -/
  | exile : Selector → CardAction
  /-- Cast the selected card without paying its mana cost. -/
  | cast : Selector → CardAction
  /-- Exchange control of the selected objects. -/
  | exchangeControl : Selector → CardAction
  /-- Destroy the selected permanent (CR 701.7). -/
  | destroy : Selector → CardAction
  /-- The selected player chooses one or more of the listed actions. -/
  | playerSelectAction : Selector → Range → List CardAction → CardAction
  /-- Put the selected object on top of its owner's library. -/
  | putOnTopOfLibrary : Selector → CardAction
  /-- Put the selected object on the bottom of its owner's library. -/
  | putOnBottomOfLibrary : Selector → CardAction
  /-- Number this action so later clauses can refer to it. -/
  | actionId : Nat → CardAction → CardAction
deriving Repr, Inhabited, BEq
end

namespace ContinuousEffect

def selector : ContinuousEffect → Selector
  | .gainAbility who _ => who
  | .addPowerToughness who _ _ => who
  | .ifAny _ (inner :: _) => selector inner
  | .ifAny _ [] => .this
  | .reduceCost who _ => who
  | .additionalCost who _ => who
  | .replace _ _ => .this
  | .forbid _ => .this
  | .canCastWithoutPayingManaCost _ who => who

/-- Combined +P/+T if every effect is `addPowerToughness`. -/
def addedPT? : List ContinuousEffect → Option (Int × Int)
  | [] => some (0, 0)
  | .addPowerToughness _ p t :: rest =>
    match addedPT? rest with
    | some (p', t') => some (p + p', t + t')
    | none => none
  | .gainAbility _ _ :: _ => none
  | .ifAny _ _ :: _ => none
  | .reduceCost _ _ :: _ => none
  | .additionalCost _ _ :: _ => none
  | .replace _ _ :: _ => none
  | .forbid _ :: _ => none
  | .canCastWithoutPayingManaCost _ _ :: _ => none

/-- First declared `target` or `targets`, if any. -/
def targetingSelector? (effects : List ContinuousEffect) : Option Selector :=
  effects.findSome? fun e =>
    match e.selector.among? with
    | some _ => some e.selector
    | none => none

/-- First constraint-shaped selector, if any. -/
def massSelector? (effects : List ContinuousEffect) : Option Selector :=
  effects.findSome? fun e =>
    match e.selector with
    | .this | .source _ | .controller _ | .opponent _ | .owner _ | .target _ _ | .targets _ _ _
    | .targetSet _ _ _ _ | .targetReference _ | .var _ | .selected _ _
    | .allTargets _ | .spell | .player
    | .wasObjectOfAction _ | .replacingObject _ | .wasCreatedByAction _ => none
    | s => some s

end ContinuousEffect

namespace CardAction

/-- Until-end-of-turn keyword grants implied by `continuous` effects. -/
def grantedKeywords : List ContinuousEffect → Keywords
  | [] => Keywords.none
  | .gainAbility _ (.keyword k) :: rest =>
    k.toKeywords.merge (grantedKeywords rest)
  | _ :: rest => grantedKeywords rest

/-- Mass +P/+T on creatures you control. -/
def creaturesYouControlPumpEffect (p t : Int) (asAbility : Bool) : Effect :=
  if asAbility then Effect.abilityCreaturesYouControlGet p t
  else Effect.creaturesYouControlGet p t

/-- Keyword grants, optionally targeted. -/
def grantKeywordsEffect (sel : Option Selector) (effects : List ContinuousEffect)
    (asAbility : Bool) : Effect :=
  let kws := grantedKeywords effects
  let targeting :=
    match sel with
    | some s => s.toTargeting
    | none => .of .none
  if asAbility then
    Effect.mkAbility targeting (.onPermanent (.grantKeywords kws))
  else
    Effect.mkSpell targeting (.onPermanent (.grantKeywords kws)) (castKind := .pump)

/-- Compile a `continuous` action, optionally wrapped in targeting. -/
def continuousEffect (sel : Option Selector) (effects : List ContinuousEffect)
    (asAbility : Bool) : Effect :=
  match ContinuousEffect.addedPT? effects with
  | some (p, t) =>
    match sel with
    | some s =>
      let targeting := s.toTargeting
      if asAbility then
        Effect.mkAbility targeting (.onPermanent (.pump p t))
      else
        Effect.mkSpell targeting (.onPermanent (.pump p t)) (castKind := .pump)
    | none => creaturesYouControlPumpEffect p t asAbility
  | none => grantKeywordsEffect sel effects asAbility

/-- Compile a mass action. Creatures you control getting +P/+T
is the shape Dwarven Provisioner prints. -/
def massEffect (among : Selector) (effects : List ContinuousEffect) (asAbility : Bool) : Effect :=
  match ContinuousEffect.addedPT? effects, among.shape with
  | some (p, t), s =>
    if s.sameController && s.types.eqTypes [.creature] then
      creaturesYouControlPumpEffect p t asAbility
    else
      continuousEffect none effects asAbility
  | none, _ =>
    continuousEffect none effects asAbility

/-- Apply `maxTargets` / `allowsZeroTargets` from a selector onto a compiled effect. -/
def withTargetCounts (e : Effect) (sel : Selector) (asAbility : Bool) : Effect :=
  match sel with
  | .targets _ (.range lo hi) _
  | .targetSet _ (.range lo hi) _ _ =>
    if asAbility then e
    else
      { e with
        maxTargets := if hi ≤ 1 then e.maxTargets else hi
        allowsZeroTargets := e.allowsZeroTargets || lo == 0 }
  | _ => e

/-- Source of this ability gets +P/+T. -/
def leftoverSourcePump? : List ContinuousEffect → Option (Int × Int)
  | [.addPowerToughness (.source .this) p t] => some (p, t)
  | _ => none

def compileContinuous (effects : List ContinuousEffect) (asAbility : Bool) : Effect :=
  match leftoverSourcePump? effects with
  | some (p, t) => Effect.sourceGets p t
  | none =>
    match ContinuousEffect.targetingSelector? effects with
    | some sel =>
      withTargetCounts (continuousEffect (some sel) effects asAbility) sel asAbility
    | none =>
      match ContinuousEffect.massSelector? effects with
      | some among => massEffect among effects asAbility
      | none => continuousEffect none effects asAbility

def compileTap (s : Selector) (asAbility : Bool) : Effect :=
  match s.among? with
  | some _ =>
    let e :=
      if asAbility then
        Effect.mkAbility s.toTargeting (Resolution.ofSpell .tapTargets)
      else
        Effect.mkSpell s.toTargeting .tapTargets (castKind := .pump)
    withTargetCounts e s asAbility
  | none =>
    if asAbility then
      Effect.mkAbility (.of .none) (Resolution.ofSpell .tapTargets)
    else
      Effect.mkSpell (.of .none) .tapTargets (castKind := .pump)

def compileUntap (s : Selector) (asAbility : Bool) : Effect :=
  match s.among? with
  | some _ =>
    if asAbility then
      Effect.mkAbility s.toTargeting (.onPermanent .untap)
    else
      Effect.mkSpell s.toTargeting (.onPermanent .untap) (castKind := .pump)
  | none =>
    if asAbility then
      Effect.mkAbility (.of .none) (.onPermanent .untap)
    else
      Effect.mkSpell (.of .none) (.onPermanent .untap) (castKind := .pump)

def compileDamage (s : Selector) (n : Nat) (asAbility : Bool) : Effect :=
  match s.among? with
  | some _ =>
    if asAbility then
      Effect.mkAbility s.toTargeting (.onPermanent (.dealDamage n))
        (castKind := .creatureDamage)
    else
      Effect.mkSpell s.toTargeting (.onPermanent (.dealDamage n))
        (castKind := .creatureDamage)
  | none =>
    if asAbility then
      Effect.mkAbility (.of .none) (.onPermanent (.dealDamage n))
        (castKind := .creatureDamage)
    else
      Effect.mkSpell (.of .none) (.onPermanent (.dealDamage n))
        (castKind := .creatureDamage)

/-- Untap a creature you control, +P/+T on that target, and maybe attach
if the target is a Dwarf. -/
def leftoverUntapPumpAttach? : CardAction → Option (Int × Int)
  | .sequence [
      .untap ut,
      .continuous effects _,
      .ifAny among [.optional (.attach _eq _to)]
    ] =>
    let youControlCreature :=
      match ut.among? with
      | some who =>
        let s := who.shape
        s.sameController && s.types.eqTypes [.creature]
      | none => false
    if youControlCreature && among.shape.dwarf then
      ContinuousEffect.addedPT? effects
    else none
  | _ => none

/-- Draw, then discard a card. -/
def leftoverDrawDiscard? : CardAction → Option Nat
  | .sequence [.draw _who n, .discard _p 1] => some n
  | _ => none

/-- Counter a spell; exile a permanent spell and allow a free cast. -/
def leftoverCounterExile? : CardAction → Bool
  | .sequence [
      .actionId _ (.counter _),
      .continuous (.replace (.putToGraveyard _) _ :: _) _
    ] => true
  | _ => false

/-- Compile `continuous` effects, reading targeting from `target`
and mass application from constraint selectors. -/
def compile (action : CardAction) (asAbility : Bool) : Effect :=
  match leftoverUntapPumpAttach? action with
  | some (p, t) => Effect.untapPumpMaybeAttach p t
  | none =>
    if leftoverCounterExile? action then Effect.counterExilePermanentMayCast
    else
      match leftoverDrawDiscard? action with
      | some n => Effect.drawThenDiscard n
      | none =>
        match action with
        | .continuous effects _duration => compileContinuous effects asAbility
        | .tap s => compileTap s asAbility
        | .untap s => compileUntap s asAbility
        | .dealDamage _source victim n => compileDamage victim n asAbility
        | .draw _who n => Effect.draw n
        | .scry _who n => Effect.scry n
        | .sequence (a :: _) => compile a asAbility
        | .sequence [] => continuousEffect none [] asAbility
        | .forEach _ inner => compile inner asAbility
        | .ifAny _ (a :: _) => compile a asAbility
        | .ifAny _ [] => continuousEffect none [] asAbility
        | .optional inner => compile inner asAbility
        | .attach _ _ => Effect.untapPumpMaybeAttach 0 0
        | .chooseMode (a :: _) => compile a asAbility
        | .chooseMode [] => continuousEffect none [] asAbility
        | .counter _ => Effect.counterSpell
        | .preventable _ costs (.counter _) =>
          Effect.counterUnlessPays (ManaCost.manaValue (Cost.manaCost costs))
        | .preventable _ _ inner => compile inner asAbility
        | .discard _ n => Effect.drawThenDiscard n
        | .putCounter _ _ _ => continuousEffect none [] asAbility
        | .exile _ => continuousEffect none [] asAbility
        | .cast _ => continuousEffect none [] asAbility
        | .exchangeControl _ => Effect.exchangeControlSharingType
        | .destroy _ => Effect.destroyCreature
        | .playerSelectAction _ _
            [.putOnTopOfLibrary _, .putOnBottomOfLibrary _] =>
          Effect.putOnTopOrBottom
        | .playerSelectAction _ _ (a :: _) => compile a asAbility
        | .playerSelectAction _ _ [] => continuousEffect none [] asAbility
        | .putOnTopOfLibrary _ => Effect.putOnTopOrBottom
        | .putOnBottomOfLibrary _ => Effect.putOnTopOrBottom
        | .actionId _ inner => compile inner asAbility

/-- Modes of a “Choose one” action. -/
def leftoverModes? : CardAction → Option (Array Effect)
  | .chooseMode as => some ((as.map fun a => compile a false).toArray)
  | _ => none

/-- Compile to a spell-shaped `Effect`. -/
def toEffect (action : CardAction) : Effect :=
  compile action false

/-- Compile to an activated-ability `Effect`. -/
def toAbilityEffect (action : CardAction) : Effect :=
  compile action true

end CardAction

namespace Ability

/-- Compile an `.activated` ability; `none` for a keyword. -/
def activatedAbility (costs : List Cost) (action : CardAction)
    (onceEachTurn : Bool := false) : ActivatedAbility :=
  { cost := { mana := Cost.manaCost costs, payLife := Cost.lifePaid costs }
    effect := action.toAbilityEffect
    onceEachTurn }

def toActivatedAbility? : Ability → Option ActivatedAbility
  | .activated costs action => some (activatedAbility costs action)
  | .activatedTimes 1 .turnStart costs action =>
    some (activatedAbility costs action true)
  | .activatedTimes _ _ costs action => some (activatedAbility costs action)
  | .restrict .onceEachTurn (.activated costs action) =>
    some (activatedAbility costs action true)
  | _ => none

/-- Compile a `.triggered` ability. -/
def toTriggeredAbility? : Ability → Option TriggeredAbility
  | .triggered (.attack .this .all) (.continuous effects _duration) =>
    match ContinuousEffect.addedPT? effects with
    | some (1, 1) => some TriggeredAbility.onAttackPumpForEachOtherCreature
    | _ => none
  | .triggered (.enter .this) (.draw (.controller .this) n) =>
    some (TriggeredAbility.onEnterDraw n)
  | .triggered
      (.ordinal 2 .turnStart (.draw (.controller .this) .all))
      (.putCounter (.source .this) .plusOnePlusOne 1) =>
    some TriggeredAbility.onDrawSecondPlusOne
  | .triggered (.draw (.controller .this) .all)
      (.putCounter (.source .this) .plusOnePlusOne 1) =>
    some TriggeredAbility.onDrawPlusOne
  | .triggered (.combatDamage .this .player)
      (.sequence [.draw (.controller .this) 1, .discard (.controller .this) 1]) =>
    some TriggeredAbility.onCombatDamageToPlayerLoot
  | .triggered (.die .this) (.continuous effects _duration) =>
    match ContinuousEffect.targetingSelector? effects, ContinuousEffect.addedPT? effects with
    | some sel, some (p, t) =>
      if sel.toTargetKind == .oppCreature then
        some (TriggeredAbility.onDiesOppCreatureGets p t)
      else none
    | _, _ => none
  | .triggered (.dieSimultaneously among _) (.scry _ n) =>
    if among.shape.otherCreatures then
      some (TriggeredAbility.onOneOrMoreOtherCreaturesDieScry n)
    else none
  | _ => none

end Ability

/-- One printed characteristic or ability of a card face. -/
inductive CardPart where
  | name : String → CardPart
  /-- Printed symbols; `ManaCost` is the engine structure, this list is the
  prototype spelling (`.manaCost [.mono .white]`). -/
  | manaCost : List ManaSymbol → CardPart
  | type : CardType → CardPart
  | supertype : CardSupertype → CardPart
  | subtype : CardSubtype → CardPart
  | power : Nat → CardPart
  | toughness : Nat → CardPart
  | ability : Ability → CardPart
  | alternative : List CardPart → CardPart
  /-- The spelled-out actions this part performs, in order. -/
  | actions : List CardAction → CardPart
deriving Repr, Inhabited, BEq

/-- A traditional (non-token, non-DFC-only) printed card. -/
inductive TraditionalCardDefinition where
  | card : List CardPart → TraditionalCardDefinition
deriving Repr, Inhabited, BEq

/-- Accumulator for one face of a `TraditionalCardDefinition`. -/
structure CardFace where
  name : String := ""
  manaCost : ManaCost := ManaCost.empty
  types : Array CardType := #[]
  supertypes : Array Supertype := #[]
  subtypes : Array Subtype := #[]
  power : Option Int := none
  toughness : Option Int := none
  keywords : Keywords := Keywords.none
  action : Option CardAction := none
  alternatives : Array (List CardPart) := #[]
  activatedAbilities : Array ActivatedAbility := #[]
  triggeredAbilities : Array TriggeredAbility := #[]
  costReductionIfTargetTapped : Nat := 0
  costReductionIfTargetAttackingNontoken : Nat := 0
  additionalCostSacrificeArtifactOrCreature : Bool := false
  additionalCostOrPayGeneric : Option Nat := none
deriving Inhabited

namespace CardFace

def applyReduceCost (assign : CardFace → Nat → CardFace) (b : CardFace)
    (e : ContinuousEffect) : CardFace :=
  match e with
  | .reduceCost _ costs =>
    assign b (ManaCost.manaValue (Cost.manaCost costs))
  | _ => b

def applyContinuousEffect (b : CardFace) : ContinuousEffect → CardFace
  | .gainAbility _ _ => b
  | .addPowerToughness _ _ _ => b
  | .ifAny among inners =>
    if among.shape.tappedCreature then
      inners.foldl
        (applyReduceCost fun b n =>
          { b with costReductionIfTargetTapped := b.costReductionIfTargetTapped + n })
        b
    else if among.shape.attackingNontokenCreature then
      inners.foldl
        (applyReduceCost fun b n =>
          { b with
            costReductionIfTargetAttackingNontoken :=
              b.costReductionIfTargetAttackingNontoken + n })
        b
    else b
  | .replace _ _ => b
  | .forbid (.block who .this) =>
    if who == .any then
      { b with keywords := b.keywords.merge Keyword.cantBeBlocked.toKeywords }
    else b
  | .forbid _ => b
  | .canCastWithoutPayingManaCost _ _ => b
  | .additionalCost _ cs =>
    { b with
      additionalCostSacrificeArtifactOrCreature :=
        b.additionalCostSacrificeArtifactOrCreature ||
          Cost.sacrificesArtifactOrCreature cs
      additionalCostOrPayGeneric :=
        b.additionalCostOrPayGeneric.orElse (fun _ => Cost.orPayGeneric? cs) }
  | .reduceCost _ costs =>
    { b with
      costReductionIfTargetTapped :=
        b.costReductionIfTargetTapped + ManaCost.manaValue (Cost.manaCost costs) }

def applyAbility (b : CardFace) : Ability → CardFace
  | .keyword k => { b with keywords := b.keywords.merge k.toKeywords }
  | .activated costs action =>
    { b with
      activatedAbilities :=
        b.activatedAbilities.push (Ability.activatedAbility costs action) }
  | .activatedTimes n from_ costs action =>
    match (Ability.activatedTimes n from_ costs action).toActivatedAbility? with
    | some ab => { b with activatedAbilities := b.activatedAbilities.push ab }
    | none => b
  | .restrict r a =>
    match Ability.restrict r a |>.toActivatedAbility? with
    | some ab => { b with activatedAbilities := b.activatedAbilities.push ab }
    | none => applyAbility b a
  | .triggered w action =>
    match (Ability.triggered w action).toTriggeredAbility? with
    | some t => { b with triggeredAbilities := b.triggeredAbilities.push t }
    | none => b
  | .static e => applyContinuousEffect b e
  | .reduceCost _ costs =>
    { b with
      costReductionIfTargetTapped :=
        b.costReductionIfTargetTapped + ManaCost.manaValue (Cost.manaCost costs) }

def apply (b : CardFace) : CardPart → CardFace
  | .name n => { b with name := n }
  | .manaCost c => { b with manaCost := (c : ManaCost) }
  | .type t => { b with types := b.types.push t }
  | .supertype s => { b with supertypes := b.supertypes.push s }
  | .subtype s => { b with subtypes := b.subtypes.push s.toString }
  | .power n => { b with power := some n }
  | .toughness n => { b with toughness := some n }
  | .ability a => applyAbility b a
  | .alternative parts => { b with alternatives := b.alternatives.push parts }
  | .actions as =>
    { b with
      action :=
        match as with
        | [a] => some a
        | as => some (.sequence as) }

def ofParts (parts : List CardPart) : CardFace :=
  parts.foldl apply {}

def toAdventure (b : CardFace) : AdventureFace := {
  name := b.name
  manaCost := b.manaCost
  types := if b.types.isEmpty then #[.sorcery] else b.types
  subtypes := if b.subtypes.isEmpty then #["Adventure"] else b.subtypes
  oracleText :=
    match b.action with
    | some a => a.toEffect.phrase
    | none => ""
  spellEffect := b.action.map (·.toEffect)
}

end CardFace

namespace TraditionalCardDefinition

/-- Compile printed parts to the engine `CardDef`. When `oracleText` is
omitted, keywords and the Adventure face are reconstructed so the card
still has ability text. -/
def toCardDef (d : TraditionalCardDefinition) (oracleText : String := "") : CardDef :=
  match d with
  | .card parts =>
    let b := CardFace.ofParts parts
    let adventure :=
      match b.alternatives[0]? with
      | some alt => some (CardFace.ofParts alt).toAdventure
      | none => none
    let generated :=
      let kw :=
        let s := toString b.keywords
        if s.isEmpty then [] else [s]
      let adv :=
        match adventure with
        | none => []
        | some a =>
          let typeLine := formatTypeLine #[] a.types a.subtypes
          let effect :=
            match a.spellEffect with
            | some e => e.phrase
            | none => a.oracleText
          ["//ADV//", s!"{a.name} {a.manaCost}", typeLine, effect]
      String.intercalate "\n" (kw ++ adv)
    {
      name := b.name
      manaCost := b.manaCost
      types := b.types
      subtypes := b.subtypes
      supertypes := b.supertypes
      power := b.power
      toughness := b.toughness
      keywords := b.keywords
      spellModes :=
        match b.action with
        | some a => (CardAction.leftoverModes? a).getD #[]
        | none => #[]
      spellEffect :=
        match b.action with
        | some a =>
          if (CardAction.leftoverModes? a).isSome then none
          else some a.toEffect
        | none => none
      activatedAbilities := b.activatedAbilities
      triggeredAbilities := b.triggeredAbilities
      costReductionIfTargetTapped := b.costReductionIfTargetTapped
      costReductionIfTargetAttackingNontoken := b.costReductionIfTargetAttackingNontoken
      additionalCostSacrificeArtifactOrCreature :=
        b.additionalCostSacrificeArtifactOrCreature
      additionalCostOrPayGeneric := b.additionalCostOrPayGeneric
      adventure := adventure
      oracleText := if oracleText.isEmpty then generated else oracleText
    }

instance : Coe TraditionalCardDefinition CardDef where
  coe d := d.toCardDef

end TraditionalCardDefinition

#guard Selector.among? (.allTargets .this) == none

-- Concerted Care: target artifact or creature you control gains hexproof
-- and indestructible until end of turn.
#guard
  let action : CardAction :=
    .continuous
      [
        .gainAbility
          (.target
            1
            (.intersection [
              .permanent,
              .union [.cardType .artifact, .cardType .creature],
              .controlled (.controller .this)]))
          (.keyword .hexproof),
        .gainAbility (.targetReference 1) (.keyword .indestructible)]
      .endOfTurn
  action.toEffect == Effect.grantHexproofIndestructible

#guard Selector.toTargetKind
  (.intersection [
    .permanent,
    .union [.cardType .artifact, .cardType .creature],
    .controlled (.controller .this)])
  == .artifactOrCreatureYouControl

#guard Selector.toTargetKind
  (.intersection [
    .controlled (.controller .this),
    .union [.cardType .creature, .cardType .artifact],
    .permanent])
  == .artifactOrCreatureYouControl

-- Dwarven Provisioner: {3}{W}: creatures you control get +1/+1 until end of turn.
#guard
  let action : CardAction :=
    .continuous
      [.addPowerToughness
        (.intersection [
          .permanent,
          .cardType .creature,
          .controlled (.controller .this)])
        1 1]
      .endOfTurn
  action.toAbilityEffect == Effect.abilityCreaturesYouControlGet 1 1

#guard
  match
    (Ability.activated
      [.mana [.generic 3, .mono .white]]
      (.continuous
        [.addPowerToughness
          (.intersection [
            .permanent,
            .cardType .creature,
            .controlled (.controller .this)])
          1 1]
        .endOfTurn)).toActivatedAbility? with
  | some ab =>
    ab.cost.mana == ManaCost.ofGenericAndColor 3 .white &&
      ab.effect == Effect.abilityCreaturesYouControlGet 1 1
  | none => false

-- Gaze in Wonder: tap one or two target creatures.
#guard
  let action : CardAction :=
    .tap (.targets 1 (.range 1 2) (.intersection [.permanent, .cardType .creature]))
  action.toEffect == Effect.tapOneOrTwoCreatures

-- Magnificent End: 5 damage to target creature; {3} less if that target is tapped.
#guard
  let action : CardAction :=
    .dealDamage
      .this
      (.target 1 (.intersection [.permanent, .cardType .creature]))
      5
  action.toEffect == Effect.dealDamageToCreature 5

#guard Selector.shape
  (.intersection [.permanent, .cardType .creature, .tapped]) |>.tappedCreature

#guard
  (TraditionalCardDefinition.card [
    .name "Magnificent End",
    .manaCost [.generic 4, .mono .white],
    .type .instant,
    .ability (
      .static
        (.ifAny
          (.intersection [
            .allTargets .this,
            .permanent,
            .cardType .creature,
            .tapped])
          [.reduceCost .this [.mana [.generic 3]]])),
    .actions [
      .dealDamage
        .this
        (.target 1 (.intersection [.permanent, .cardType .creature]))
        5]
  ]).toCardDef.costReductionIfTargetTapped == 3

-- Eagle of the Great Shelf: whenever this attacks, +1/+1 (per other creature leftover).
#guard
  match
    (Ability.triggered
      (.attack .this .all)
      (.continuous [.addPowerToughness (.source .this) 1 1] .endOfTurn)).toTriggeredAbility? with
  | some ab => ab == TriggeredAbility.onAttackPumpForEachOtherCreature
  | none => false

-- Vow to Erebor: untap target creature you control, +2/+2, maybe attach if Dwarf.
#guard Selector.toTargetKind
  (.intersection [
    .permanent,
    .cardType .creature,
    .controlled (.controller .this)])
  == .creatureYouControl

#guard Selector.shape (.subtype .dwarf) |>.dwarf

#guard
  let action : CardAction :=
    .sequence [
      .untap
        (.target
          1
          (.intersection [
            .permanent,
            .cardType .creature,
            .controlled (.controller .this)])),
      .continuous [.addPowerToughness (.targetReference 1) 2 2] .endOfTurn,
      .ifAny
        (.intersection [.targetReference 1, .subtype .dwarf])
        [
          .optional
            (.attach
              (.selected
                (.range 1 1)
                (.intersection [
                  .permanent,
                  .subtype .equipment,
                  .controlled (.controller .this)]))
              (.targetReference 1))
        ]]
  action.toEffect == Effect.untapPumpMaybeAttach 2 2

-- Bilbo Baggins, Burglar: enters, draw a card; Adventure scry 2.
#guard
  match
    (Ability.triggered
      (.enter .this)
      (.draw (.controller .this) 1)).toTriggeredAbility? with
  | some ab => ab == TriggeredAbility.onEnterDraw 1
  | none => false

#guard
  let action : CardAction := .scry (.controller .this) 2
  action.toEffect == Effect.scry 2

-- Lakeshore Apothecary: draw your second card, +1/+1 counter.
#guard
  match
    (Ability.triggered
      (.ordinal 2 .turnStart (.draw (.controller .this) .all))
      (.putCounter (.source .this) .plusOnePlusOne 1)).toTriggeredAbility? with
  | some ab => ab == TriggeredAbility.onDrawSecondPlusOne
  | none => false

-- Confusticate and Bebother: choose counter-unless or loot.
#guard
  let action : CardAction :=
    .chooseMode [
      .preventable (.controller (.targetReference 1)) [.mana [.generic 4]]
        (.counter (.target 1 .spell)),
      .sequence [
        .draw (.controller .this) 2,
        .discard (.controller .this) 1]]
  CardAction.leftoverModes? action ==
    some #[Effect.counterUnlessPays 4, Effect.drawThenDiscard 2]

-- Ravenhill Flock: whenever you draw, +1/+1 counter.
#guard
  match
    (Ability.triggered
      (.draw (.controller .this) .all)
      (.putCounter (.source .this) .plusOnePlusOne 1)).toTriggeredAbility? with
  | some ab => ab == TriggeredAbility.onDrawPlusOne
  | none => false

-- Thranduil's Decree: counter; exile a permanent spell and maybe cast it.
#guard
  (TraditionalCardDefinition.card [
    .actions [
      .actionId 1 (.counter (.target 1 .spell)),
      .continuous
        [.replace
          (.putToGraveyard (.wasObjectOfAction 1))
          [.actionId 2 (.exile (.replacingObject 1)),
            .continuous
              [.canCastWithoutPayingManaCost (.controller .this) (.wasCreatedByAction 2)]
              .endOfGame]]
        .endOfGame]
  ]).toCardDef.spellEffect == some Effect.counterExilePermanentMayCast

-- Bilbo, Luckwearer: combat damage loot; Adventure exchanges control.
#guard
  match
    (Ability.triggered
      (.combatDamage .this .player)
      (.sequence [
        .draw (.controller .this) 1,
        .discard (.controller .this) 1])).toTriggeredAbility? with
  | some ab => ab == TriggeredAbility.onCombatDamageToPlayerLoot
  | none => false

#guard
  (TraditionalCardDefinition.card [
    .ability (.static (.forbid (.block .any .this)))
  ]).toCardDef.keywords.cantBeBlocked

#guard
  let action : CardAction :=
    .exchangeControl
      (.targetSet
        1
        (.range 2 2)
        (.intersection [.permanent, .not .land])
        [.shareCardType])
  action.toEffect == Effect.exchangeControlSharingType

#guard Selector.toTargetKind
  (.targetSet
    1
    (.range 2 2)
    (.intersection [.permanent, .not .land])
    [.shareCardType])
  == .twoNonlandsSharingType

-- Uneasy Partings: {1} less if the target is an attacking nontoken creature;
-- owner puts it on top or bottom.
#guard Selector.shape
  (.intersection [
    .allTargets .this,
    .permanent,
    .cardType .creature,
    .attacking .all,
    .not .token]) |>.attackingNontokenCreature

#guard
  (TraditionalCardDefinition.card [
    .ability (
      .static
        (.ifAny
          (.intersection [
            .allTargets .this,
            .permanent,
            .cardType .creature,
            .attacking .all,
            .not .token])
          [.reduceCost .this [.mana [.generic 1]]])),
    .actions [
      .playerSelectAction (.owner (.targetReference 1)) (.range 1 1)
        [.putOnTopOfLibrary
          (.target 1 (.intersection [.permanent, .cardType .creature])),
          .putOnBottomOfLibrary (.targetReference 1)]]
  ]).toCardDef.costReductionIfTargetAttackingNontoken == 1

#guard
  let action : CardAction :=
    .playerSelectAction (.owner (.targetReference 1)) (.range 1 1)
      [.putOnTopOfLibrary
        (.target 1 (.intersection [.permanent, .cardType .creature])),
        .putOnBottomOfLibrary (.targetReference 1)]
  action.toEffect == Effect.putOnTopOrBottom

-- Front Porch Sentries: dies, -1/-1 to an opponent's creature.
#guard Selector.toTargetKind
  (.intersection [
    .permanent,
    .cardType .creature,
    .controlled (.opponent (.controller .this))])
  == .oppCreature

#guard
  match
    (Ability.triggered
      (.die .this)
      (.continuous
        [.addPowerToughness
          (.target
            1
            (.intersection [
              .permanent,
              .cardType .creature,
              .controlled (.opponent (.controller .this))]))
          (-1) (-1)]
        .endOfTurn)).toTriggeredAbility? with
  | some ab => ab == TriggeredAbility.onDiesOppCreatureGets (-1) (-1)
  | none => false

-- Great Fierce Bee: one or more other creatures die, scry 1.
#guard Selector.shape
  (.intersection [.not .this, .permanent, .cardType .creature]) |>.otherCreatures

#guard
  match
    (Ability.triggered
      (.dieSimultaneously (.intersection [.not .this, .permanent, .cardType .creature]) [])
      (.scry (.controller .this) 1)).toTriggeredAbility? with
  | some ab => ab == TriggeredAbility.onOneOrMoreOtherCreaturesDieScry 1
  | none => false

-- Stir Up Trouble: sacrifice an artifact or creature or pay {4}; destroy.
#guard
  let action : CardAction :=
    .destroy (.target 1 (.intersection [.permanent, .cardType .creature]))
  action.toEffect == Effect.destroyCreature

#guard
  (TraditionalCardDefinition.card [
    .ability (.static (
      .additionalCost .this
        [.or [
          .sacrifice
            (.intersection [
              .permanent,
              .union [.cardType .artifact, .cardType .creature]]),
          .mana [.generic 4]]])),
    .actions [
      .destroy (.target 1 (.intersection [.permanent, .cardType .creature]))]
  ]).toCardDef.additionalCostSacrificeArtifactOrCreature

#guard
  (TraditionalCardDefinition.card [
    .ability (.static (
      .additionalCost .this
        [.or [
          .sacrifice
            (.intersection [
              .permanent,
              .union [.cardType .artifact, .cardType .creature]]),
          .mana [.generic 4]]]))
  ]).toCardDef.additionalCostOrPayGeneric == some 4

-- Desolation Prowler: pay 2 life, +2/+2, once each turn.
#guard
  match
    (Ability.activatedTimes 1 .turnStart
        [.life 2]
        (.continuous [.addPowerToughness (.source .this) 2 2] .endOfTurn)).toActivatedAbility? with
  | some ab =>
    ab.effect == Effect.sourceGets 2 2 && ab.cost.payLife == 2 && ab.onceEachTurn
  | none => false

end Mtg.Engine
