import Mtg.Engine.Card.Definition.Parts

/-!
# Continuous effects

Projections of a `ContinuousEffect`, and the compilers for a continuous
action, a tap, an untap, and damage.
-/

namespace Mtg.Engine

/-- Convert a Value to an Int if constant. -/
def valToInt? : Value → Option Int
  | .int p => some p
  | .x | .count _ | .totalPower _ | .greatestManaValue _ | .greatestToughness _
  | .greatestPower _ | .product _ _ | .variable _ | .remainder _ _
  | .greatestManaSpent _ | .excessDamageOfActionWithId _ => none

/-- Convert a Value to a Nat if it is a non-negative constant. -/
def valToNat? : Value → Option Nat
  | .int n => if n ≥ 0 then some n.toNat else none
  | .x | .count _ | .totalPower _ | .greatestManaValue _ | .greatestToughness _
  | .greatestPower _ | .product _ _ | .variable _ | .remainder _ _
  | .greatestManaSpent _ | .excessDamageOfActionWithId _ => none

/-- This object, or the source of this ability (CR 113.7). -/
def isThisOrItsSource : Selector → Bool
  | .this | .source .this => true
  | _ => false

/-- The number of lands this object's controller controls. -/
def isLandsYouControlCount : Value → Bool
  | .count among => among.shape.landYouControl
  | _ => false

/-- The number of creature permanents this object's controller controls.
Another, a subtype, a power threshold, or a status such as tapped is a
different count. -/
def isCreaturesYouControlCount : Value → Bool
  | .count among =>
    let s := among.shape
    s.mustBePermanent && s.sameController && !s.other && !s.opponentControls &&
      s.types.eqTypes [.creature] && s.subtype.isNone && s.powerAtLeast.isNone &&
      !s.tapped && !s.flying && !s.attacking && !s.token && !s.nontoken
  | _ => false

/-- `setPower` of this object to the number of creatures you control. -/
def setsPowerToCreaturesYouControl : ContinuousEffect → Bool
  | .setPower who v => isThisOrItsSource who && isCreaturesYouControlCount v
  | _ => false

/-- `setPower` when `power` is true, otherwise `setToughness`, of this object
to the number of lands you control. -/
def setsCharacteristicToLandsYouControl (power : Bool) : ContinuousEffect → Bool
  | .setPower who v => power && isThisOrItsSource who && isLandsYouControlCount v
  | .setToughness who v => !power && isThisOrItsSource who && isLandsYouControlCount v
  | _ => false

/-- A gained static ability that sets power or toughness to the number of
lands you control. -/
def grantsLandsCharacteristic (power : Bool) : ContinuousEffect → Bool
  | .gainAbility who (.static e) =>
    isThisOrItsSource who && setsCharacteristicToLandsYouControl power e
  | _ => false

namespace ContinuousEffect

def selector : ContinuousEffect → Selector
  | .gainAbility who _ => who
  | .if _ (inner :: _) => selector inner
  | .if _ [] => .this
  | .reduceCost who _ | .reduceCostWithX who _ _ => who
  | .additionalCost who _ | .alternativeCost who _ | .replaceCost who _ => who
  | .replace _ _ => .this
  | .forbid _ => .this
  | .canCastWithoutPayingManaCost _ who => who
  | .canPlay _ card => card
  | .setBasePower who _ | .setBaseToughness who _ => who
  | .gainType who _ => who
  | .gainSubtype who _ => who
  | .gainAllSubtypes who _ => who
  | .setPower who _ | .setToughness who _ => who
  | .addPower who _ | .addToughness who _ => who
  | .increaseLandPlayLimit who _ => who
  | .canBeCastAsThoughWithFlashIf card _ => card
  | .doesntUntap who => who
  | .cantAttackUnlessPays who _ _ => who
  | .removeAllAbilities who => who

/-- Combined integer +P/+T when every effect is `addPower` or `addToughness`.
A side that is absent is zero. Any other effect, or a non-integer value, is
`none`. -/
def addedPT? : List ContinuousEffect → Option (Int × Int)
  | [] => some (0, 0)
  | .addPower _ v :: rest =>
    match valToInt? v, addedPT? rest with
    | some p, some (p', t') => some (p + p', t')
    | _, _ => none
  | .addToughness _ v :: rest =>
    match valToInt? v, addedPT? rest with
    | some t, some (p', t') => some (p', t + t')
    | _, _ => none
  | _ :: _ => none

/-- Integer power and toughness from `addPower` and `addToughness`.
Other effects are ignored. `none` when neither is present, or when a power
or toughness value is not an integer. -/
def foundAddedPT? (effects : List ContinuousEffect) : Option (Int × Int) :=
  match effects.foldl step (some ((0, 0), false)) with
  | some ((p, t), true) => some (p, t)
  | _ => none
where
  step (acc : Option ((Int × Int) × Bool)) (e : ContinuousEffect) :
      Option ((Int × Int) × Bool) :=
    match acc with
    | none => none
    | some ((p, t), seen) =>
      match e with
      | .addPower _ v =>
        match valToInt? v with
        | some dp => some ((p + dp, t), true)
        | none => none
      | .addToughness _ v =>
        match valToInt? v with
        | some dt => some ((p, t + dt), true)
        | none => none
      | _ => some ((p, t), seen)

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
    | .this | .source _ | .controller _ | .caster | .opponent _ | .owner _ | .target _ _ | .targets _ _ _
    | .targetSet _ _ _ _ | .targetReference _ | .selected _ _ _
    | .spell | .ability | .abilityWithId _ | .permanentSpell | .hasTarget _ | .isTargetOf _ | .keywordAbility _
    | .player
    | .wasObjectOfAction _ | .wasArgumentOfTrigger _ _ | .replacingObject | .wasCreatedByAction _
    | .affectedByAction _
    | .hostOf _ | .wasObjectSince _ _
    | .zone .graveyard | .zone .library | .zone .hand | .zone .exile
    | .zone .stack | .zone .command | .supertype _
    | .variable _ | .topOfLibrary _ _ => none
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
  | .targets _ (.range (.int (.ofNat lo)) (.int (.ofNat hi))) _
  | .targetSet _ (.range (.int (.ofNat lo)) (.int (.ofNat hi))) _ _ =>
    if asAbility then e
    else
      { e with
        maxTargets := if hi ≤ 1 then e.maxTargets else hi
        allowsZeroTargets := e.allowsZeroTargets || lo == 0 }
  | _ => e

/-- Source of this ability gets +P/+T. -/
def leftoverSourcePump? (effects : List ContinuousEffect) : Option (Int × Int) :=
  match effects with
  | [] => none
  | _ =>
    match ContinuousEffect.addedPT? effects with
    | some pt =>
      if effects.all fun e =>
        match e with
        | .addPower (.source .this) _ | .addToughness (.source .this) _ => true
        | _ => false
      then some pt
      else none
    | none => none

/-- Target creature gets +P/+T (Giant Growth, Dark Deed). -/
def leftoverTargetPump? (effects : List ContinuousEffect) : Option (Int × Int) :=
  match ContinuousEffect.addedPT? effects, ContinuousEffect.targetingSelector? effects with
  | some (p, t), some sel =>
    if sel.toTargetKind == .creature then some (p, t) else none
  | _, _ => none

/-- You may play an additional land this turn. -/
def leftoverIncreaseLandPlayLimit? : List ContinuousEffect → Bool
  | [.increaseLandPlayLimit who (Value.int 1)] =>
    who == .controller .this
  | _ => false

/-- Until end of turn, objects selected by `sel` lose all abilities.
A numbered target uses the announced permanent. Any other selector is
matched when the effect resolves. -/
def removeAllAbilitiesEffect (sel : Selector) (asAbility : Bool) : Effect :=
  if sel.among?.isSome then
    let targeting := sel.toTargeting
    if asAbility then
      Effect.mkAbility targeting (.onPermanent .removeAllAbilities)
    else
      Effect.mkSpell targeting (.onPermanent .removeAllAbilities) (castKind := .pump)
  else
    let phrase := "Selected objects lose all abilities until end of turn"
    if asAbility then
      Effect.mkAbility ({}) (.removeAllAbilities sel) (phraseOverride := some phrase)
    else
      { spellCastKind := .pump
        resolution := .removeAllAbilities sel
        phrase }

def compileContinuousBase (effects : List ContinuousEffect) (asAbility : Bool) : Effect :=
  if leftoverIncreaseLandPlayLimit? effects then
    Effect.playAdditionalLandThisTurn
  else
  match leftoverSourcePump? effects with
  | some (p, t) => Effect.sourceGets p t
  | none =>
    match leftoverTargetPump? effects with
    | some (p, t) =>
      if asAbility then
        match ContinuousEffect.targetingSelector? effects with
        | some sel =>
          withTargetCounts (continuousEffect (some sel) effects true) sel true
        | none => continuousEffect none effects true
      else Effect.pump p t
    | none =>
      match ContinuousEffect.targetingSelector? effects with
      | some sel =>
        withTargetCounts (continuousEffect (some sel) effects asAbility) sel asAbility
      | none =>
        match ContinuousEffect.massSelector? effects with
        | some among => massEffect among effects asAbility
        | none => continuousEffect none effects asAbility

def compileContinuous (effects : List ContinuousEffect) (asAbility : Bool) : Effect :=
  match effects.findSome? fun e =>
      match e with
      | .removeAllAbilities sel => some sel
      | _ => none with
  | some sel =>
    let rest := effects.filter fun e =>
      match e with
      | .removeAllAbilities _ => false
      | _ => true
    let removeE := removeAllAbilitiesEffect sel asAbility
    if rest.isEmpty then removeE
    else
      let restE := compileContinuousBase rest asAbility
      { removeE with
        resolution := .sequence [removeE.resolution, restE.resolution]
        targeting := if removeE.requiresTarget then removeE.targeting else restE.targeting
        maxTargets := if removeE.requiresTarget then removeE.maxTargets else restE.maxTargets
        allowsZeroTargets := removeE.allowsZeroTargets || restE.allowsZeroTargets
        phrase :=
          if restE.phrase.isEmpty then removeE.phrase
          else s!"{removeE.phrase}. {restE.phrase}" }
  | none => compileContinuousBase effects asAbility

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
  if Selector.leftoverAnyTarget? s then
    if asAbility then Effect.dealDamageToAny n else Effect.dealDamage n
  else
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

end CardAction

end Mtg.Engine
