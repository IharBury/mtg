import Mtg.Engine.Card.CardDef
import Mtg.Engine.Card.Keywords
import Mtg.Engine.Card.PermanentAction
import Mtg.Engine.Card.SpellEffects
import Mtg.Engine.Card.TriggeredAbility
import Mtg.Engine.Mana
import Mtg.Engine.TypeLine

/-!
# Selectors

`Selector.Shape` flattens a `Selector` so intersection and union lists
compile without depending on conjunct order. Targeting helpers read that
shape into an `EffectTargetKind`.
-/

namespace Mtg.Engine

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
  flying : Bool := false
  attacking : Bool := false
  token : Bool := false
  nontoken : Bool := false
  other : Bool := false
  subtype : Option String := none
  types : TypeSet := .any
  isSpell : Bool := false
  nonland : Bool := false
  shareCardType : Bool := false
  powerAtLeast : Option Int := none
  powerAtMost : Option Int := none
  hasPlusOneCounter : Bool := false
  diedThisTurn : Bool := false
  putIntoGraveyardThisTurn : Bool := false
  /-- Only objects of a chosen creature type. -/
  chosenCreatureType : Bool := false
deriving Repr, Inhabited, BEq

namespace Shape

def meet (a b : Shape) : Shape :=
  { sameController := a.sameController || b.sameController
    opponentControls := a.opponentControls || b.opponentControls
    mustBePermanent := a.mustBePermanent || b.mustBePermanent
    tapped := a.tapped || b.tapped
    flying := a.flying || b.flying
    attacking := a.attacking || b.attacking
    token := a.token || b.token
    nontoken := a.nontoken || b.nontoken
    other := a.other || b.other
    subtype := a.subtype.orElse fun _ => b.subtype
    types := a.types.intersect b.types
    isSpell := a.isSpell || b.isSpell
    nonland := a.nonland || b.nonland
    shareCardType := a.shareCardType || b.shareCardType
    powerAtLeast :=
      match a.powerAtLeast, b.powerAtLeast with
      | some x, some y => some (max x y)
      | x, y => x.orElse fun _ => y
    powerAtMost :=
      match a.powerAtMost, b.powerAtMost with
      | some x, some y => some (min x y)
      | x, y => x.orElse fun _ => y
    hasPlusOneCounter := a.hasPlusOneCounter || b.hasPlusOneCounter
    diedThisTurn := a.diedThisTurn || b.diedThisTurn
    putIntoGraveyardThisTurn :=
      a.putIntoGraveyardThisTurn || b.putIntoGraveyardThisTurn
    chosenCreatureType := a.chosenCreatureType || b.chosenCreatureType }

def join (a b : Shape) : Shape :=
  { sameController := a.sameController && b.sameController
    opponentControls := a.opponentControls && b.opponentControls
    mustBePermanent := a.mustBePermanent && b.mustBePermanent
    tapped := a.tapped && b.tapped
    flying := a.flying && b.flying
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
    shareCardType := a.shareCardType && b.shareCardType
    powerAtLeast :=
      match a.powerAtLeast, b.powerAtLeast with
      | some x, some y => if x == y then some x else none
      | _, _ => none
    powerAtMost :=
      match a.powerAtMost, b.powerAtMost with
      | some x, some y => if x == y then some x else none
      | _, _ => none
    hasPlusOneCounter := a.hasPlusOneCounter && b.hasPlusOneCounter
    diedThisTurn := a.diedThisTurn && b.diedThisTurn
    putIntoGraveyardThisTurn :=
      a.putIntoGraveyardThisTurn && b.putIntoGraveyardThisTurn
    chosenCreatureType := a.chosenCreatureType && b.chosenCreatureType }

/-- True when this shape is a tapped creature (optional permanent conjunct). -/
def tappedCreature (s : Shape) : Bool :=
  s.tapped && s.types.eqTypes [.creature]

/-- True when this shape is a creature with flying. -/
def flyingCreature (s : Shape) : Bool :=
  s.flying && s.types.eqTypes [.creature]

/-- True when this shape is another creature you control. -/
def anotherCreatureYouControl (s : Shape) : Bool :=
  s.other && s.sameController && s.types.eqTypes [.creature]

/-- True when this shape is a land you control. -/
def landYouControl (s : Shape) : Bool :=
  s.sameController && s.types.eqTypes [.land]

/-- True when this shape is an artifact you control. -/
def artifactYouControl (s : Shape) : Bool :=
  s.sameController && s.types.eqTypes [.artifact]

/-- True when this shape is another artifact you control. -/
def anotherArtifactYouControl (s : Shape) : Bool :=
  s.other && s.sameController && s.types.eqTypes [.artifact]

/-- True when this shape is another Elf you control. -/
def anotherElfYouControl (s : Shape) : Bool :=
  s.other && s.sameController && s.subtype == some "Elf"

/-- The named subtype when this shape is another of that subtype you control. -/
def anotherSubtypeYouControl (s : Shape) : Option String :=
  if s.other && s.sameController then s.subtype else none

/-- True when this shape is a Dwarf. -/
def dwarf (s : Shape) : Bool :=
  s.subtype == some "Dwarf"

/-- True when this shape is an attacking creature. -/
def attackingCreature (s : Shape) : Bool :=
  s.attacking && s.types.eqTypes [.creature]

/-- True when this shape is an attacking nontoken creature. -/
def attackingNontokenCreature (s : Shape) : Bool :=
  s.attacking && s.nontoken && s.types.eqTypes [.creature]

/-- True when this shape is other creatures. -/
def otherCreatures (s : Shape) : Bool :=
  s.other && s.types.eqTypes [.creature]

/-- True when this shape is a creature you control with power 4 or greater
(Ferocious). -/
def ferocious (s : Shape) : Bool :=
  s.sameController && s.types.eqTypes [.creature] && s.powerAtLeast == some 4

/-- True when this shape is a creature that died this turn. -/
def diedThisTurnCreature (s : Shape) : Bool :=
  s.diedThisTurn && s.types.eqTypes [.creature]

/-- Negate a constraint-shaped selector. `.not` of a land type is nonland;
`.not` of a token is nontoken. -/
def negate (s : Shape) : Shape :=
  if s.types.eqTypes [.land] then { nonland := true }
  else if s.token then { nontoken := true }
  else {}

end Shape

def shape : Selector → Shape
  | .all => {}
  | .zone .battlefield => { mustBePermanent := true }
  | .controlled (.controller .this) => { sameController := true }
  | .controlled (.opponent _) => { opponentControls := true }
  | .controlled _ => {}
  | .tapped => { tapped := true }
  | .keyword .flying => { flying := true }
  | .keyword _ => {}
  | .keywordAbility _ => {}
  | .powerAtLeast (.int n) => { powerAtLeast := some n }
  | .powerAtLeast _ => {}
  | .powerAtMost (.int n) => { powerAtMost := some n }
  | .powerAtMost _ => {}
  | .hasCounter .plusOnePlusOne => { hasPlusOneCounter := true }
  | .hasCounter _ => {}
  | .attacking _ => { attacking := true }
  | .blocking _ => {}
  | .token => { token := true }
  | .subtype st => { subtype := some st.toString }
  | .cardType t => { types := .oneOf [t] }
  | .spell => { isSpell := true }
  | .ability => {}
  | .abilityWithId _ => {}
  | .permanentSpell => { isSpell := true }
  | .hasTarget _ => {}
  | .isTargetOf _ => {}
  | .not .this => { other := true }
  | .not s => s.shape.negate
  | .intersection fs => fs.foldl (fun acc f => acc.meet f.shape) {}
  | .union [] => {}
  | .union (f :: fs) => fs.foldl (fun acc g => acc.join g.shape) f.shape
  | .this | .source _ | .controller _ | .caster | .opponent _ | .owner _ | .target _ _
  | .targets _ _ _ | .targetSet _ _ _ _ | .targetReference _
  | .selected _ _ _ | .player => {}
  | .wasObjectSince (.putToGraveyard _) .turnStart =>
    { putIntoGraveyardThisTurn := true }
  | .wasObjectSince _ _ | .wasObjectOfAction _ | .wasArgumentOfTrigger _ _ | .replacingObject
  | .wasCreatedByAction _ | .affectedByAction _ | .hostOf _ | .zone _
  | .supertype _
  | .variable _ | .topOfLibrary _ _ => {}
  | .hasCreatureTypeChosenByAction _ => { chosenCreatureType := true }
  | .manaValueAtMost _ | .castFromZone _ => {}

/-- Apply set-wide predicates onto an object-level shape. -/
def applySetPredicates (s : Shape) : List SetPredicate → Shape
  | [] => s
  | .shareCardType :: rest =>
    applySetPredicates { s with shareCardType := true } rest
  | .countAtLeast _ :: rest | .totalPowerAtLeast _ :: rest =>
    applySetPredicates s rest

/-- Shape used for targeting: unwrap `target` / `targets` / `targetSet`
and fold in set predicates. -/
def targetingShape : Selector → Shape
  | .target _ among => among.shape
  | .targets _ _ among => among.shape
  | .targetSet _ _ among preds => applySetPredicates among.shape preds
  | s => s.shape

/-- True when this selector includes “noncreature” (`.not` of creature). -/
def includesNoncreature : Selector → Bool
  | .not (.cardType .creature) => true
  | .intersection (f :: fs) =>
    includesNoncreature f || includesNoncreature (.intersection fs)
  | _ => false

/-- Compile a selector to a targeting shape the engine already understands. -/
def toTargetKind (f : Selector) : EffectTargetKind :=
  let s := f.targetingShape
  if s.isSpell then .spell
  else if s.nonland && s.shareCardType then .twoNonlandsSharingType
  else if s.nonland then .nonland
  else if s.opponentControls && s.types.eqTypes [.creature] then
    match s.powerAtMost with
    | some n => .oppCreaturePowerAtMost n
    | none => .oppCreature
  else if s.sameController then
    if s.other && s.types.eqTypes [.creature] then .anotherCreatureYouControl
    else if s.types.eqTypes [.artifact, .creature] then .artifactOrCreatureYouControl
    else if s.types.eqTypes [.creature] then
      match s.powerAtMost with
      | some n => .creatureYouControlPowerAtMost n
      | none => .creatureYouControl
    else if s.types.eqTypes [.artifact] then .artifactYouControl
    else .permanent
  else if s.flying && s.types.eqTypes [.creature] then .creatureWithFlying
  else if
      (match f with
        | .target _ among | .targets _ _ among | .targetSet _ _ among _ =>
          among.includesNoncreature
        | _ => f.includesNoncreature) &&
        s.types.eqTypes [.artifact, .enchantment] then
    .noncreatureArtifactOrEnchantment
  else if s.types.eqTypes [.artifact, .enchantment] then .artifactOrEnchantment
  else if s.types.eqTypes [.artifact, .land] then .artifactOrLand
  else if s.types.eqTypes [.creature] then
    match s.powerAtMost with
    | some n => .creaturePowerAtMost n
    | none =>
      match s.powerAtLeast with
      | some n => .creaturePowerAtLeast n
      | none => .creature
  else if s.types.eqTypes [.artifact] then .artifact
  else .permanent

/-- The constraint a targeting selector matches, if it announces targets. -/
def among? : Selector → Option Selector
  | .target _ among => some among
  | .targets _ _ among => some among
  | .targetSet _ _ among _ => some among
  | _ => none

/-- The number of a `.target`, `.targets`, or `.targetSet` selector. -/
def targetNumber? : Selector → Option Nat
  | .target n _ => some n
  | .targets n _ _ => some n
  | .targetSet n _ _ _ => some n
  | _ => none

/-- True when two selectors do not share a target number. Unnumbered
selectors do not conflict. -/
def leftoverDistinctTargetNumbers (a b : Selector) : Bool :=
  match targetNumber? a, targetNumber? b with
  | some n, some m => n != m
  | _, _ => true

/-- True when this targeting selector is “any target”. -/
def leftoverAnyTarget? (s : Selector) : Bool :=
  s.among? == some .all || s == .all

/-- Any object. -/
def any : Selector := .all

/-- A land (CR 305). -/
def land : Selector := .cardType .land

/-- True when this selector includes `.zone .library`. -/
def includesInLibrary : Selector → Bool
  | .zone .library => true
  | .intersection (f :: fs) =>
    includesInLibrary f || includesInLibrary (.intersection fs)
  | _ => false

/-- True when this selector names a numbered target so a later clause can
refer to that chosen object. -/
def includesTargetReference : Selector → Bool
  | .targetReference _ => true
  | .intersection (f :: fs) =>
    includesTargetReference f || includesTargetReference (.intersection fs)
  | .union (f :: fs) =>
    includesTargetReference f || includesTargetReference (.union fs)
  | .not s => includesTargetReference s
  | _ => false

/-- The same objects, with every declared target turned into a
`targetReference`. A target number is declared once. -/
def referenceTargets : Selector → Selector
  | .this => .this
  | .source s => .source (referenceTargets s)
  | .controller s => .controller (referenceTargets s)
  | .caster => .caster
  | .target n _ => .targetReference n
  | .targets n _ _ => .targetReference n
  | .targetSet n _ _ _ => .targetReference n
  | .not s => .not (referenceTargets s)
  | .targetReference n => .targetReference n
  | .selected who range among =>
    .selected (referenceTargets who) range (referenceTargets among)
  | .intersection ss => .intersection (ss.map referenceTargets)
  | .all => .all
  | .cardType t => .cardType t
  | .union ss => .union (ss.map referenceTargets)
  | .zone z => .zone z
  | .controlled s => .controlled (referenceTargets s)
  | .tapped => .tapped
  | .keyword k => .keyword k
  | .keywordAbility k => .keywordAbility k
  | .powerAtLeast v => .powerAtLeast v
  | .powerAtMost v => .powerAtMost v
  | .hasCounter k => .hasCounter k
  | .subtype st => .subtype st
  | .spell => .spell
  | .ability => .ability
  | .abilityWithId n => .abilityWithId n
  | .permanentSpell => .permanentSpell
  | .hasTarget s => .hasTarget (referenceTargets s)
  | .isTargetOf s => .isTargetOf (referenceTargets s)
  | .player => .player
  | .opponent s => .opponent (referenceTargets s)
  | .owner s => .owner (referenceTargets s)
  | .attacking s => .attacking (referenceTargets s)
  | .blocking s => .blocking (referenceTargets s)
  | .token => .token
  | .wasObjectOfAction n => .wasObjectOfAction n
  | .wasArgumentOfTrigger id n => .wasArgumentOfTrigger id n
  | .replacingObject => .replacingObject
  | .wasCreatedByAction n => .wasCreatedByAction n
  | .affectedByAction n => .affectedByAction n
  | .hostOf s => .hostOf (referenceTargets s)
  | .wasObjectSince a b => .wasObjectSince a b
  | .supertype st => .supertype st
  | .variable n => .variable n
  | .topOfLibrary s n => .topOfLibrary (referenceTargets s) n
  | .hasCreatureTypeChosenByAction n => .hasCreatureTypeChosenByAction n
  | .manaValueAtMost v => .manaValueAtMost v
  | .castFromZone z => .castFromZone z

#guard
  (Selector.target 1 (.intersection [.zone .battlefield, .cardType .creature])).referenceTargets ==
    .targetReference 1

#guard
  (Selector.intersection [
    .zone .battlefield,
    .cardType .creature,
    .controlled (.target 1 .player)]).referenceTargets ==
    .intersection [
      .zone .battlefield,
      .cardType .creature,
      .controlled (.targetReference 1)]

/-- True when this selector includes the Basic supertype. -/
def includesBasic : Selector → Bool
  | .supertype .basic => true
  | .intersection (f :: fs) => includesBasic f || includesBasic (.intersection fs)
  | _ => false

/-- True when this selector includes the Legendary supertype. -/
def includesLegendary : Selector → Bool
  | .supertype .legendary => true
  | .intersection (f :: fs) =>
    includesLegendary f || includesLegendary (.intersection fs)
  | _ => false

/-- True when this selector includes the land card type. -/
def includesLand : Selector → Bool
  | .cardType .land => true
  | .intersection (f :: fs) => includesLand f || includesLand (.intersection fs)
  | _ => false

/-- True when this selector includes the graveyard zone. -/
def includesInGraveyard : Selector → Bool
  | .zone .graveyard => true
  | .intersection (f :: fs) =>
    includesInGraveyard f || includesInGraveyard (.intersection fs)
  | .target _ among | .targets _ _ among => includesInGraveyard among
  | _ => false

/-- True when this selector names an argument of a numbered trigger. -/
def includesWasArgumentOfTrigger : Selector → Bool
  | .wasArgumentOfTrigger _ _ => true
  | .intersection (f :: fs) =>
    includesWasArgumentOfTrigger f || includesWasArgumentOfTrigger (.intersection fs)
  | _ => false

/-- The target constraint of a `hasTarget` conjunct, if any. -/
def leftoverHasTarget? : Selector → Option Selector
  | .hasTarget dest => some dest
  | .intersection (f :: fs) =>
    match leftoverHasTarget? f with
    | some dest => some dest
    | none => leftoverHasTarget? (.intersection fs)
  | _ => none

/-- The keyword of a `keywordAbility` conjunct, if any. -/
def leftoverKeywordAbility? : Selector → Option Keyword
  | .keywordAbility k => some k
  | .intersection (f :: fs) =>
    match leftoverKeywordAbility? f with
    | some k => some k
    | none => leftoverKeywordAbility? (.intersection fs)
  | _ => none

/-- True when this selector includes an object that is a target of something
(CR 115.1). -/
def includesIsTargetOf : Selector → Bool
  | .isTargetOf _ => true
  | .intersection (f :: fs) =>
    includesIsTargetOf f || includesIsTargetOf (.intersection fs)
  | _ => false

/-- True when this selector is a target of an argument of a numbered trigger. -/
def leftoverIsTargetOfThisSpell? : Selector → Bool
  | .isTargetOf (.wasArgumentOfTrigger _ _) => true
  | .intersection (f :: fs) =>
    leftoverIsTargetOfThisSpell? f || leftoverIsTargetOfThisSpell? (.intersection fs)
  | _ => false

/-- True when this selector is “the object of a put-to-graveyard event
since the start of the turn”. -/
def wasObjectOfPutToGraveyardThisTurn? : Selector → Bool
  | .wasObjectSince (.putToGraveyard _) .turnStart => true
  | .intersection (f :: fs) =>
    wasObjectOfPutToGraveyardThisTurn? f ||
      wasObjectOfPutToGraveyardThisTurn? (.intersection fs)
  | _ => false

/-- True when this selector includes `.spell`. -/
def includesSpell : Selector → Bool
  | .spell | .permanentSpell => true
  | .intersection (f :: fs) => includesSpell f || includesSpell (.intersection fs)
  | _ => false

/-- True when this selector is a noncreature spell you cast. -/
def youCastNoncreatureSpell (s : Selector) : Bool :=
  s.shape.sameController && includesSpell s && includesNoncreature s

/-- True when this selector is any spell you cast, with no further
restriction. -/
def anySpellYouCast (s : Selector) : Bool :=
  let sh := s.shape
  includesSpell s && sh.isSpell && sh.sameController && !sh.opponentControls &&
    !sh.mustBePermanent && sh.subtype.isNone && sh.types == .any &&
    !sh.nonland && !includesNoncreature s

/-- True when this selector is a noncreature spell an opponent casts. -/
def opponentCastsNoncreatureSpell (s : Selector) : Bool :=
  s.shape.opponentControls && includesSpell s && includesNoncreature s

/-- True when this selector is another Villain you control. -/
def anotherVillainYouControl (s : Selector) : Bool :=
  s.shape.other && s.shape.sameController && s.shape.subtype == some "Villain"

/-- True when this selector is another Villain and/or artifact you control. -/
def anotherVillainOrArtifactYouControl : Selector → Bool
  | .union fs =>
    let villain := fs.any anotherVillainYouControl
    let artifact := fs.any fun a => a.shape.anotherArtifactYouControl
    villain && artifact
  | s =>
    anotherVillainYouControl s || s.shape.anotherArtifactYouControl

/-- Printed subtype mentioned by this selector, if any. -/
def includedSubtype? : Selector → Option String
  | .subtype st => some st.toString
  | .intersection (f :: fs) => (includedSubtype? f).orElse fun _ => includedSubtype? (.intersection fs)
  | _ => none

/-- Printed subtypes mentioned by this selector, including unions, in order. -/
def includedSubtypes : Selector → List String
  | .subtype st => [st.toString]
  | .union fs => fs.flatMap includedSubtypes
  | .intersection fs => fs.flatMap includedSubtypes
  | .target _ among | .targets _ _ among => includedSubtypes among
  | _ => []

/-- Another permanent you control that is `subtype` or Equipment. -/
def anotherSubtypeOrEquipment? (s : Selector) : Option String :=
  if s.shape.other && s.shape.sameController && s.shape.mustBePermanent then
    match s.includedSubtypes with
    | [st, "Equipment"] => some st
    | _ => none
  else none

/-- A basic land card in a library. -/
def basicLandInLibrary (s : Selector) : Bool :=
  includesInLibrary s && includesLand s && includesBasic s

/-- A legendary creature card in a library, with no further subtype. -/
def legendaryCreatureInLibrary (s : Selector) : Bool :=
  s.includesInLibrary && s.includesLegendary && !s.includesLand &&
    s.includedSubtype?.isNone && s.shape.types.eqTypes [.creature]

/-- The constraint a `selected` choice matches. -/
def selectedAmong? : Selector → Option Selector
  | .selected _ _ among => some among
  | _ => none

def toTargeting (s : Selector) : EffectTargeting :=
  match s.among? with
  | some _ => .of s.toTargetKind
  | none => .of .none

/-- `you control a legendary creature`, as a condition reads it. -/
def aLegendaryCreatureYouControl : Selector :=
  .intersection [.zone .battlefield, .cardType .creature, .supertype .legendary, .controlled (.controller .this)]

/-- Permanents of these subtypes that this object's controller controls, and
whether `other` excludes this object: `Goblins and Orcs you control`. -/
def subtypesYouControl? : Selector → Option (Array String × Bool)
  | .intersection [.zone .battlefield, kinds, .controlled (.controller .this)] =>
    (subtypeNames? kinds).map (·, false)
  | .intersection [.not .this, .zone .battlefield, kinds, .controlled (.controller .this)] =>
    (subtypeNames? kinds).map (·, true)
  | _ => none
where
  subtypeNames? : Selector → Option (Array String)
    | .subtype st => some #[st.toString]
    | .union kinds =>
      (kinds.mapM fun
        | Selector.subtype st => some st.toString
        | _ => none).map List.toArray
    | _ => none

end Selector

end Mtg.Engine
