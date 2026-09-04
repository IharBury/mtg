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

/-- A payment in an activated-ability cost (CR 602.1). -/
inductive Cost where
  | mana : List ManaSymbol → Cost
deriving Repr, Inhabited, BEq

namespace Cost

def manaCost : List Cost → ManaCost
  | [] => ManaCost.empty
  | .mana syms :: rest =>
    { symbols := (syms : ManaCost).symbols ++ (manaCost rest).symbols }

end Cost

/-- How many objects a `.targets` selector may choose. -/
inductive Range where
  | range : Nat → Nat → Range
deriving Repr, Inhabited, BEq

/-- Whom or what a spell or ability refers to (CR 109.5 / 113.7 / 115.1). -/
inductive Selector where
  /-- This spell or ability (CR 113.7). -/
  | this
  /-- The source of the given object (CR 113.7). -/
  | source : Selector → Selector
  /-- The controller of the given object (CR 109.5). -/
  | controller : Selector → Selector
  /-- A numbered target matching `among` (CR 115.1). Later effects may
  refer to it with `targetReference`. -/
  | target : Nat → Selector → Selector
  /-- Numbered targets matching `among`, with a count range. -/
  | targets : Nat → Range → Selector → Selector
  /-- The target previously declared with `target` of this number. -/
  | targetReference : Nat → Selector
  /-- The object bound by `forEach` of this number. -/
  | var : Nat → Selector
  /-- Choose objects from `among` at resolution, with a count range
  (not targeting; CR 608.2d). -/
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
  | controlledBy : Selector → Selector
  /-- A tapped permanent (CR 110.5). -/
  | tapped
  /-- Printed subtype (CR 205.3). -/
  | subtype : CardSubtype → Selector
deriving Repr, Inhabited, BEq

namespace Selector

/-- Card types a filter allows. `any` means the filter does not mention type. -/
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
  mustBePermanent : Bool := false
  tapped : Bool := false
  subtype : Option String := none
  types : TypeSet := .any
deriving Repr, Inhabited, BEq

namespace Shape

def meet (a b : Shape) : Shape :=
  { sameController := a.sameController || b.sameController
    mustBePermanent := a.mustBePermanent || b.mustBePermanent
    tapped := a.tapped || b.tapped
    subtype := a.subtype.orElse fun _ => b.subtype
    types := a.types.intersect b.types }

def join (a b : Shape) : Shape :=
  { sameController := a.sameController && b.sameController
    mustBePermanent := a.mustBePermanent && b.mustBePermanent
    tapped := a.tapped && b.tapped
    subtype :=
      match a.subtype, b.subtype with
      | some x, some y => if x == y then some x else none
      | _, _ => none
    types := a.types.union b.types }

/-- True when this shape is a tapped creature (optional permanent conjunct). -/
def tappedCreature (s : Shape) : Bool :=
  s.tapped && s.types.eqTypes [.creature]

/-- True when this shape is a Dwarf. -/
def dwarf (s : Shape) : Bool :=
  s.subtype == some "Dwarf"

end Shape

def shape : Selector → Shape
  | .all => {}
  | .permanent => { mustBePermanent := true }
  | .controlledBy (.controller .this) => { sameController := true }
  | .controlledBy _ => {}
  | .tapped => { tapped := true }
  | .subtype st => { subtype := some st.toString }
  | .cardType t => { types := .oneOf [t] }
  | .intersection fs => fs.foldl (fun acc f => acc.meet f.shape) {}
  | .union [] => {}
  | .union (f :: fs) => fs.foldl (fun acc g => acc.join g.shape) f.shape
  | .this | .source _ | .controller _ | .target _ _ | .targets _ _ _
  | .targetReference _ | .var _ | .selected _ _ | .allTargets _ => {}

/-- Compile a selector to a targeting shape the engine already understands. -/
def toTargetKind (f : Selector) : EffectTargetKind :=
  let s := f.shape
  if s.sameController then
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
  | _ => none

def toTargeting (s : Selector) : EffectTargeting :=
  match s.among? with
  | some among => .of among.toTargetKind
  | none => .of .none

end Selector

/-- When a continuous effect ends, or when a triggered ability fires. -/
inductive Trigger where
  | endOfGame
  | endOfTurn
  /-- Whenever the selected object attacks, restricted by `among`. -/
  | attack : Selector → Selector → Trigger
  /-- When the selected object enters. -/
  | enter : Selector → Trigger
deriving Repr, Inhabited, BEq

/-- A condition that gates a printed ability or clause. -/
inductive Condition where
  /-- `who` has a target among the objects described by `among`. -/
  | hasTargetIn : Selector → Selector → Condition
  /-- The given object has the given subtype. -/
  | hasSubtype : Selector → CardSubtype → Condition
deriving Repr, Inhabited, BEq

-- Printed abilities, continuous effects, and actions are mutually inductive:
-- an activated ability has an action, and a continuous effect may grant an
-- ability.
mutual
/-- A keyword or other printed ability on a card or granted by an effect. -/
inductive Ability where
  | keyword : Keyword → Ability
  | activated : List Cost → CardAction → Ability
  | triggered : Trigger → CardAction → Ability
  | static : List ContinuousEffect → Ability
  | conditional : Condition → Ability → Ability
  | reduceCost : Selector → List Cost → Ability
deriving Repr, Inhabited, BEq

/-- A continuous effect granted by a spell or ability. -/
inductive ContinuousEffect where
  | gainAbility : Selector → Ability → ContinuousEffect
  | addPowerToughness : Selector → Int → Int → ContinuousEffect
  | conditional : Condition → List ContinuousEffect → ContinuousEffect
  | reduceCost : Selector → List Cost → ContinuousEffect
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
  | conditional : Condition → CardAction → CardAction
  | optional : CardAction → CardAction
  | attach : Selector → Selector → CardAction
deriving Repr, Inhabited, BEq
end

namespace ContinuousEffect

def selector : ContinuousEffect → Selector
  | .gainAbility who _ => who
  | .addPowerToughness who _ _ => who
  | .conditional _ (inner :: _) => selector inner
  | .conditional _ [] => .this
  | .reduceCost who _ => who

/-- Combined +P/+T if every effect is `addPowerToughness`. -/
def addedPT? : List ContinuousEffect → Option (Int × Int)
  | [] => some (0, 0)
  | .addPowerToughness _ p t :: rest =>
    match addedPT? rest with
    | some (p', t') => some (p + p', t + t')
    | none => none
  | .gainAbility _ _ :: _ => none
  | .conditional _ _ :: _ => none
  | .reduceCost _ _ :: _ => none

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
    | .this | .source _ | .controller _ | .target _ _ | .targets _ _ _
    | .targetReference _ | .var _ | .selected _ _ | .allTargets _ => none
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
  | .targets _ (.range lo hi) _ =>
    if asAbility then e
    else
      { e with
        maxTargets := if hi ≤ 1 then e.maxTargets else hi
        allowsZeroTargets := e.allowsZeroTargets || lo == 0 }
  | _ => e

def compileContinuous (effects : List ContinuousEffect) (asAbility : Bool) : Effect :=
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
      .forEach _n (.conditional (.hasSubtype _who st) (.optional (.attach _eq _to)))
    ] =>
    let youControlCreature :=
      match ut.among? with
      | some among =>
        let s := among.shape
        s.sameController && s.types.eqTypes [.creature]
      | none => false
    if youControlCreature && st == .dwarf then
      ContinuousEffect.addedPT? effects
    else none
  | _ => none

/-- Compile `continuous` effects, reading targeting from `target`
and mass application from constraint selectors. -/
def compile (action : CardAction) (asAbility : Bool) : Effect :=
  match leftoverUntapPumpAttach? action with
  | some (p, t) => Effect.untapPumpMaybeAttach p t
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
    | .conditional _ inner => compile inner asAbility
    | .optional inner => compile inner asAbility
    | .attach _ _ => Effect.untapPumpMaybeAttach 0 0

/-- Compile to a spell-shaped `Effect`. -/
def toEffect (action : CardAction) : Effect :=
  compile action false

/-- Compile to an activated-ability `Effect`. -/
def toAbilityEffect (action : CardAction) : Effect :=
  compile action true

end CardAction

namespace Ability

/-- Compile an `.activated` ability; `none` for a keyword. -/
def toActivatedAbility? : Ability → Option ActivatedAbility
  | .activated costs action =>
    some {
      cost := { mana := Cost.manaCost costs }
      effect := action.toAbilityEffect
    }
  | _ => none

/-- Compile a `.triggered` ability. -/
def toTriggeredAbility? : Ability → Option TriggeredAbility
  | .triggered (.attack .this .all) (.continuous effects _duration) =>
    match ContinuousEffect.addedPT? effects with
    | some (1, 1) => some TriggeredAbility.onAttackPumpForEachOtherCreature
    | _ => none
  | .triggered (.enter .this) (.draw (.controller .this) n) =>
    some (TriggeredAbility.onEnterDraw n)
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
  | action : CardAction → CardPart
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
deriving Inhabited

namespace CardFace

def applyContinuousEffect (b : CardFace) : ContinuousEffect → CardFace
  | .gainAbility _ _ => b
  | .addPowerToughness _ _ _ => b
  | .conditional (.hasTargetIn .this among) inners =>
    if among.shape.tappedCreature then inners.foldl applyContinuousEffect b else b
  | .conditional _ inners => inners.foldl applyContinuousEffect b
  | .reduceCost _ costs =>
    { b with
      costReductionIfTargetTapped :=
        b.costReductionIfTargetTapped + ManaCost.manaValue (Cost.manaCost costs) }

def applyAbility (b : CardFace) : Ability → CardFace
  | .keyword k => { b with keywords := b.keywords.merge k.toKeywords }
  | .activated costs action =>
    { b with
      activatedAbilities :=
        b.activatedAbilities.push {
          cost := { mana := Cost.manaCost costs }
          effect := action.toAbilityEffect
        } }
  | .triggered w action =>
    match (Ability.triggered w action).toTriggeredAbility? with
    | some t => { b with triggeredAbilities := b.triggeredAbilities.push t }
    | none => b
  | .static effects => effects.foldl applyContinuousEffect b
  | .conditional (.hasTargetIn .this among) inner =>
    if among.shape.tappedCreature then applyAbility b inner else b
  | .conditional _ inner => applyAbility b inner
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
  | .action a => { b with action := some a }

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
      spellEffect := b.action.map (·.toEffect)
      activatedAbilities := b.activatedAbilities
      triggeredAbilities := b.triggeredAbilities
      costReductionIfTargetTapped := b.costReductionIfTargetTapped
      adventure := adventure
      oracleText := if oracleText.isEmpty then generated else oracleText
    }

instance : Coe TraditionalCardDefinition CardDef where
  coe d := d.toCardDef

end TraditionalCardDefinition

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
              .controlledBy (.controller .this)]))
          (.keyword .hexproof),
        .gainAbility (.targetReference 1) (.keyword .indestructible)]
      .endOfTurn
  action.toEffect == Effect.grantHexproofIndestructible

#guard Selector.toTargetKind
  (.intersection [
    .permanent,
    .union [.cardType .artifact, .cardType .creature],
    .controlledBy (.controller .this)])
  == .artifactOrCreatureYouControl

#guard Selector.toTargetKind
  (.intersection [
    .controlledBy (.controller .this),
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
          .controlledBy (.controller .this)])
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
            .controlledBy (.controller .this)])
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
        [.conditional
          (.hasTargetIn .this
            (.intersection [.permanent, .cardType .creature, .tapped]))
          [.reduceCost .this [.mana [.generic 3]]]]),
    .action (
      .dealDamage
        .this
        (.target 1 (.intersection [.permanent, .cardType .creature]))
        5)
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
    .controlledBy (.controller .this)])
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
            .controlledBy (.controller .this)])),
      .continuous [.addPowerToughness (.targetReference 1) 2 2] .endOfTurn,
      .forEach 1 (.conditional
        (.hasSubtype (.var 1) .dwarf)
        (.optional
          (.attach (.selected (.range 1 1)
            (.intersection [
              .permanent,
              .subtype .equipment,
              .controlledBy (.controller .this)]))
            (.var 1))))]
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

end Mtg.Engine
