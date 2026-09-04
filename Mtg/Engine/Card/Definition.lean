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

-- A selector may mention a filter (`.target`, `.targets`, `.filtered`), and a
-- filter may mention a selector (`.controller`).
mutual
/-- Whom or what a spell or ability refers to (CR 109.5 / 113.7 / 115.1). -/
inductive Selector where
  /-- This spell or ability (CR 113.7). -/
  | this
  /-- The controller of the given object (CR 109.5). -/
  | controllerOf : Selector → Selector
  /-- A numbered target matching `filter` (CR 115.1). Later effects may
  refer to it with `targetReference`. -/
  | target : Nat → Filter → Selector
  /-- Numbered targets matching `filter`, with a count range. -/
  | targets : Nat → Range → Filter → Selector
  /-- The target previously declared with `target` of this number. -/
  | targetReference : Nat → Selector
  /-- Every object matching `filter` (not targeted). -/
  | filtered : Filter → Selector
deriving Repr, Inhabited, BEq

/-- Whom or what a spell or ability may target or affect (CR 115.1). -/
inductive Filter where
  | and : List Filter → Filter
  | any
  | cardType : CardType → Filter
  | or : List Filter → Filter
  /-- A permanent (CR 110.1). -/
  | permanent
  /-- Objects whose controller is the given player. -/
  | controller : Selector → Filter
  /-- A tapped permanent (CR 110.5). -/
  | tapped
  /-- Printed subtype (CR 205.3). -/
  | subtype : CardSubtype → Filter
deriving Repr, Inhabited, BEq
end

namespace Filter

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

/-- Flattened constraints implied by a filter, so `.and` / `.or` lists
compile without depending on conjunct order. -/
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

def shape : Filter → Shape
  | .any => {}
  | .permanent => { mustBePermanent := true }
  | .controller (.controllerOf .this) => { sameController := true }
  | .controller _ => {}
  | .tapped => { tapped := true }
  | .subtype st => { subtype := some st.toString }
  | .cardType t => { types := .oneOf [t] }
  | .and fs => fs.foldl (fun acc f => acc.meet f.shape) {}
  | .or [] => {}
  | .or (f :: fs) => fs.foldl (fun acc g => acc.join g.shape) f.shape

/-- Compile a filter to a targeting shape the engine already understands. -/
def toTargetKind (f : Filter) : EffectTargetKind :=
  let s := f.shape
  if s.sameController then
    if s.types.eqTypes [.artifact, .creature] then .artifactOrCreatureYouControl
    else if s.types.eqTypes [.creature] then .creatureYouControl
    else if s.types.eqTypes [.artifact] then .artifactYouControl
    else .permanent
  else if s.types.eqTypes [.creature] then .creature
  else if s.types.eqTypes [.artifact] then .artifact
  else .permanent

end Filter

/-- How many objects matching `filter` a spell or ability may target. -/
structure TargetSelector where
  minimumTargets : Nat := 1
  maximumTargets : Nat := 1
  filter : Filter := .any
deriving Repr, Inhabited, BEq

namespace TargetSelector

def toTargeting (s : TargetSelector) : EffectTargeting :=
  .of s.filter.toTargetKind

end TargetSelector

/-- When a continuous effect ends. -/
inductive Trigger where
  | endOfGame
  | endOfTurn
deriving Repr, Inhabited, BEq

/-- A condition that gates a printed ability or clause. -/
inductive Condition where
  /-- `who` has a target among the objects described by `among`. -/
  | hasTargetIn : Selector → Selector → Condition
  /-- The given object matches `filter`. -/
  | matches : Selector → Filter → Condition
deriving Repr, Inhabited, BEq

/-- When a triggered ability fires. -/
inductive When where
  /-- Whenever the selected object attacks. -/
  | attack : Selector → When
  /-- When the selected object enters. -/
  | enter : Selector → When
deriving Repr, Inhabited, BEq

namespace Selector

/-- Targeting implied by a selector, if it announces targets. -/
def asTargetSelector? : Selector → Option TargetSelector
  | .target _n f => some { filter := f }
  | .targets _n (.range lo hi) f =>
    some { minimumTargets := lo, maximumTargets := hi, filter := f }
  | _ => none

end Selector

-- Printed abilities, continuous effects, and actions are mutually inductive:
-- an activated ability has an action, and a continuous effect may grant an
-- ability.
mutual
/-- A keyword or other printed ability on a card or granted by an effect. -/
inductive Ability where
  | keyword : Keyword → Ability
  | activated : List Cost → CardAction → Ability
  | triggered : When → CardAction → Ability
  | static : Ability → Ability
  | conditional : Condition → Ability → Ability
  | reduceCost : Selector → List Cost → Ability
deriving Repr, Inhabited, BEq

/-- A continuous effect granted by a spell or ability. -/
inductive ContinuousEffect where
  | gainAbility : Selector → Ability → ContinuousEffect
  | addPowerToughness : Selector → Int → Int → ContinuousEffect
deriving Repr, Inhabited, BEq

/-- What a spell or ability does. `CardAction` is the printed-card name for
this tree; player input uses `Action` in `Game`. -/
inductive CardAction where
  | continuous : List ContinuousEffect → Trigger → CardAction
  | tap : Selector → CardAction
  | untap : Selector → CardAction
  | dealDamage : Selector → Selector → Nat → CardAction
  | draw : Nat → CardAction
  | scry : Nat → CardAction
  | sequence : List CardAction → CardAction
  | conditional : Condition → CardAction → CardAction
  | optional : CardAction → CardAction
  | attach : Selector → Selector → CardAction
deriving Repr, Inhabited, BEq
end

namespace ContinuousEffect

def selector : ContinuousEffect → Selector
  | .gainAbility who _ => who
  | .addPowerToughness who _ _ => who

/-- Combined +P/+T if every effect is `addPowerToughness`. -/
def addedPT? : List ContinuousEffect → Option (Int × Int)
  | [] => some (0, 0)
  | .addPowerToughness _ p t :: rest =>
    match addedPT? rest with
    | some (p', t') => some (p + p', t + t')
    | none => none
  | .gainAbility _ _ :: _ => none

/-- First declared `target`, if any. -/
def targetingSelector? (effects : List ContinuousEffect) : Option TargetSelector :=
  effects.findSome? fun e => e.selector.asTargetSelector?

/-- First `filtered` set, if any. -/
def massFilter? (effects : List ContinuousEffect) : Option Filter :=
  effects.findSome? fun e =>
    match e.selector with
    | .filtered f => some f
    | _ => none

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
def grantKeywordsEffect (sel : Option TargetSelector) (effects : List ContinuousEffect)
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
def continuousEffect (sel : Option TargetSelector) (effects : List ContinuousEffect)
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

/-- Compile a mass (`filtered`) action. Creatures you control getting +P/+T
is the shape Dwarven Provisioner prints. -/
def filteredEffect (f : Filter) (effects : List ContinuousEffect) (asAbility : Bool) : Effect :=
  match ContinuousEffect.addedPT? effects, f.shape with
  | some (p, t), s =>
    if s.sameController && s.types.eqTypes [.creature] then
      creaturesYouControlPumpEffect p t asAbility
    else
      continuousEffect none effects asAbility
  | none, _ =>
    continuousEffect none effects asAbility

/-- Apply `maxTargets` / `allowsZeroTargets` from a selector onto a compiled effect. -/
def withTargetCounts (e : Effect) (sel : TargetSelector) (asAbility : Bool) : Effect :=
  if asAbility then e
  else
    { e with
      maxTargets :=
        if sel.maximumTargets ≤ 1 then e.maxTargets else sel.maximumTargets
      allowsZeroTargets := e.allowsZeroTargets || sel.minimumTargets == 0 }

def compileContinuous (effects : List ContinuousEffect) (asAbility : Bool) : Effect :=
  match ContinuousEffect.targetingSelector? effects with
  | some sel =>
    withTargetCounts (continuousEffect (some sel) effects asAbility) sel asAbility
  | none =>
    match ContinuousEffect.massFilter? effects with
    | some f => filteredEffect f effects asAbility
    | none => continuousEffect none effects asAbility

def compileTap (s : Selector) (asAbility : Bool) : Effect :=
  match s.asTargetSelector? with
  | some sel =>
    let e :=
      if asAbility then
        Effect.mkAbility sel.toTargeting (Resolution.ofSpell .tapTargets)
      else
        Effect.mkSpell sel.toTargeting .tapTargets (castKind := .pump)
    withTargetCounts e sel asAbility
  | none =>
    if asAbility then
      Effect.mkAbility (.of .none) (Resolution.ofSpell .tapTargets)
    else
      Effect.mkSpell (.of .none) .tapTargets (castKind := .pump)

def compileUntap (s : Selector) (asAbility : Bool) : Effect :=
  match s.asTargetSelector? with
  | some sel =>
    if asAbility then
      Effect.mkAbility sel.toTargeting (.onPermanent .untap)
    else
      Effect.mkSpell sel.toTargeting (.onPermanent .untap) (castKind := .pump)
  | none =>
    if asAbility then
      Effect.mkAbility (.of .none) (.onPermanent .untap)
    else
      Effect.mkSpell (.of .none) (.onPermanent .untap) (castKind := .pump)

def compileDamage (s : Selector) (n : Nat) (asAbility : Bool) : Effect :=
  match s.asTargetSelector? with
  | some sel =>
    if asAbility then
      Effect.mkAbility sel.toTargeting (.onPermanent (.dealDamage n))
        (castKind := .creatureDamage)
    else
      Effect.mkSpell sel.toTargeting (.onPermanent (.dealDamage n))
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
      .conditional (.matches _ df) (.optional (.attach _ _))
    ] =>
    let youControlCreature :=
      match ut.asTargetSelector? with
      | some t =>
        let s := t.filter.shape
        s.sameController && s.types.eqTypes [.creature]
      | none => false
    if youControlCreature && df.shape.dwarf then
      ContinuousEffect.addedPT? effects
    else none
  | _ => none

/-- Compile `continuous` effects, reading targeting from `target`
and mass application from `filtered`. -/
def compile (action : CardAction) (asAbility : Bool) : Effect :=
  match leftoverUntapPumpAttach? action with
  | some (p, t) => Effect.untapPumpMaybeAttach p t
  | none =>
    match action with
    | .continuous effects _duration => compileContinuous effects asAbility
    | .tap s => compileTap s asAbility
    | .untap s => compileUntap s asAbility
    | .dealDamage _source victim n => compileDamage victim n asAbility
    | .draw n => Effect.draw n
    | .scry n => Effect.scry n
    | .sequence (a :: _) => compile a asAbility
    | .sequence [] => continuousEffect none [] asAbility
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
  | .triggered (.attack .this) (.continuous effects _duration) =>
    match ContinuousEffect.addedPT? effects with
    | some (1, 1) => some TriggeredAbility.onAttackPumpForEachOtherCreature
    | _ => none
  | .triggered (.enter .this) (.draw n) =>
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
  | .static inner => applyAbility b inner
  | .conditional (.hasTargetIn .this (.filtered f)) inner =>
    if f.shape.tappedCreature then applyAbility b inner else b
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
            (.and [
              .permanent,
              .or [.cardType .artifact, .cardType .creature],
              .controller (.controllerOf .this)]))
          (.keyword .hexproof),
        .gainAbility (.targetReference 1) (.keyword .indestructible)]
      .endOfTurn
  action.toEffect == Effect.grantHexproofIndestructible

#guard Filter.toTargetKind
  (.and [
    .permanent,
    .or [.cardType .artifact, .cardType .creature],
    .controller (.controllerOf .this)])
  == .artifactOrCreatureYouControl

#guard Filter.toTargetKind
  (.and [
    .controller (.controllerOf .this),
    .or [.cardType .creature, .cardType .artifact],
    .permanent])
  == .artifactOrCreatureYouControl

-- Dwarven Provisioner: {3}{W}: creatures you control get +1/+1 until end of turn.
#guard
  let action : CardAction :=
    .continuous
      [.addPowerToughness
        (.filtered
          (.and [
            .permanent,
            .cardType .creature,
            .controller (.controllerOf .this)]))
        1 1]
      .endOfTurn
  action.toAbilityEffect == Effect.abilityCreaturesYouControlGet 1 1

#guard
  match
    (Ability.activated
      [.mana [.generic 3, .mono .white]]
      (.continuous
        [.addPowerToughness
          (.filtered
            (.and [
              .permanent,
              .cardType .creature,
              .controller (.controllerOf .this)]))
          1 1]
        .endOfTurn)).toActivatedAbility? with
  | some ab =>
    ab.cost.mana == ManaCost.ofGenericAndColor 3 .white &&
      ab.effect == Effect.abilityCreaturesYouControlGet 1 1
  | none => false

-- Gaze in Wonder: tap one or two target creatures.
#guard
  let action : CardAction :=
    .tap (.targets 1 (.range 1 2) (.and [.permanent, .cardType .creature]))
  action.toEffect == Effect.tapOneOrTwoCreatures

-- Magnificent End: 5 damage to target creature; {3} less if that target is tapped.
#guard
  let action : CardAction :=
    .dealDamage
      .this
      (.target 1 (.and [.permanent, .cardType .creature]))
      5
  action.toEffect == Effect.dealDamageToCreature 5

#guard Filter.shape
  (.and [.permanent, .cardType .creature, .tapped]) |>.tappedCreature

#guard
  (TraditionalCardDefinition.card [
    .name "Magnificent End",
    .manaCost [.generic 4, .mono .white],
    .type .instant,
    .ability (
      .static
        (.conditional
          (.hasTargetIn .this
            (.filtered (.and [.permanent, .cardType .creature, .tapped])))
          (.reduceCost .this [.mana [.generic 3]]))),
    .action (
      .dealDamage
        .this
        (.target 1 (.and [.permanent, .cardType .creature]))
        5)
  ]).toCardDef.costReductionIfTargetTapped == 3

-- Eagle of the Great Shelf: whenever this attacks, +1/+1 (per other creature leftover).
#guard
  match
    (Ability.triggered
      (.attack .this)
      (.continuous [.addPowerToughness .this 1 1] .endOfTurn)).toTriggeredAbility? with
  | some ab => ab == TriggeredAbility.onAttackPumpForEachOtherCreature
  | none => false

-- Vow to Erebor: untap target creature you control, +2/+2, maybe attach if Dwarf.
#guard Filter.toTargetKind
  (.and [
    .permanent,
    .cardType .creature,
    .controller (.controllerOf .this)])
  == .creatureYouControl

#guard Filter.shape (.subtype .dwarf) |>.dwarf

#guard
  let action : CardAction :=
    .sequence [
      .untap
        (.target
          1
          (.and [
            .permanent,
            .cardType .creature,
            .controller (.controllerOf .this)])),
      .continuous [.addPowerToughness (.targetReference 1) 2 2] .endOfTurn,
      .conditional
        (.matches (.targetReference 1) (.subtype .dwarf))
        (.optional
          (.attach
            (.filtered
              (.and [
                .permanent,
                .subtype .equipment,
                .controller (.controllerOf .this)]))
            (.targetReference 1)))]
  action.toEffect == Effect.untapPumpMaybeAttach 2 2

-- Bilbo Baggins, Burglar: enters, draw a card; Adventure scry 2.
#guard
  match (Ability.triggered (.enter .this) (.draw 1)).toTriggeredAbility? with
  | some ab => ab == TriggeredAbility.onEnterDraw 1
  | none => false

#guard
  let action : CardAction := .scry 2
  action.toEffect == Effect.scry 2

end Mtg.Engine
