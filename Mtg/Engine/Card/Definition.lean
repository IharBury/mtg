import Mtg.Engine.Card.CardDef
import Mtg.Engine.Card.Keywords
import Mtg.Engine.Card.PermanentAction
import Mtg.Engine.Card.SpellEffects
import Mtg.Engine.Card.TriggeredAbility
import Mtg.Engine.Mana
import Mtg.Engine.TypeLine

/-!
# Traditional card definitions

A printed card as a list of `CardPart`s: name, mana cost, type line,
abilities, and (for adventurer cards) an `alternative` face. Compiles to
`CardDef` so the engine and existing catalogs stay unchanged.

Remaining supported catalog cards that are not yet in this syntax, and
the constructors they need, are listed in `TraditionalSyntaxGaps.md`.
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
  diedThisTurn : Bool := false
  putIntoGraveyardThisTurn : Bool := false
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
    diedThisTurn := a.diedThisTurn || b.diedThisTurn
    putIntoGraveyardThisTurn :=
      a.putIntoGraveyardThisTurn || b.putIntoGraveyardThisTurn }

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
    diedThisTurn := a.diedThisTurn && b.diedThisTurn
    putIntoGraveyardThisTurn :=
      a.putIntoGraveyardThisTurn && b.putIntoGraveyardThisTurn }

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
  | .permanent => { mustBePermanent := true }
  | .controlled (.controller .this) => { sameController := true }
  | .controlled (.opponent _) => { opponentControls := true }
  | .controlled _ => {}
  | .tapped => { tapped := true }
  | .keyword .flying => { flying := true }
  | .keyword _ => {}
  | .keywordAbility _ => {}
  | .powerAtLeast (.int n) | .powerAtLeast (.nat n) => { powerAtLeast := some n }
  | .powerAtLeast _ => {}
  | .attacking _ => { attacking := true }
  | .blocking _ => {}
  | .token => { token := true }
  | .subtype st => { subtype := some st.toString }
  | .cardType t => { types := .oneOf [t] }
  | .spell => { isSpell := true }
  | .permanentSpell => { isSpell := true }
  | .hasTarget _ => {}
  | .isTargetOf _ => {}
  | .not .this => { other := true }
  | .not s => s.shape.negate
  | .intersection fs => fs.foldl (fun acc f => acc.meet f.shape) {}
  | .union [] => {}
  | .union (f :: fs) => fs.foldl (fun acc g => acc.join g.shape) f.shape
  | .this | .source _ | .controller _ | .opponent _ | .owner _ | .target _ _
  | .targets _ _ _ | .targetSet _ _ _ _ | .targetReference _
  | .selected _ _ _ | .player => {}
  | .wasObjectSince (.putToGraveyard _) .turnStart =>
    { putIntoGraveyardThisTurn := true }
  | .wasObjectSince _ _ | .wasObjectOfAction _ | .wasObjectOfThisTrigger | .replacingObject
  | .wasCreatedByAction _ | .hostOf _ | .inGraveyard | .inLibrary | .inHand
  | .inExile | .supertype _
  | .variable _ | .topOfLibrary _ => {}

/-- Apply set-wide predicates onto an object-level shape. -/
def applySetPredicates (s : Shape) : List SetPredicate → Shape
  | [] => s
  | .shareCardType :: rest =>
    applySetPredicates { s with shareCardType := true } rest
  | .countAtLeast _ :: rest => applySetPredicates s rest

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
  else if s.opponentControls && s.types.eqTypes [.creature] then .oppCreature
  else if s.sameController then
    if s.other && s.types.eqTypes [.creature] then .anotherCreatureYouControl
    else if s.types.eqTypes [.artifact, .creature] then .artifactOrCreatureYouControl
    else if s.types.eqTypes [.creature] then .creatureYouControl
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

/-- True when this selector includes `inLibrary`. -/
def includesInLibrary : Selector → Bool
  | .inLibrary => true
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
  | .inGraveyard => true
  | .intersection (f :: fs) =>
    includesInGraveyard f || includesInGraveyard (.intersection fs)
  | .target _ among | .targets _ _ among => includesInGraveyard among
  | _ => false

/-- True when this selector is the object of this triggered ability. -/
def includesWasObjectOfThisTrigger : Selector → Bool
  | .wasObjectOfThisTrigger => true
  | .intersection (f :: fs) =>
    includesWasObjectOfThisTrigger f || includesWasObjectOfThisTrigger (.intersection fs)
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

/-- True when this selector is a target of this trigger's object. -/
def leftoverIsTargetOfThisSpell? : Selector → Bool
  | .isTargetOf .wasObjectOfThisTrigger => true
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

/-- A basic land card in a library. -/
def basicLandInLibrary (s : Selector) : Bool :=
  includesInLibrary s && includesLand s && includesBasic s

/-- The constraint a `selected` choice matches. -/
def selectedAmong? : Selector → Option Selector
  | .selected _ _ among => some among
  | _ => none

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

end Cost

/-- A boolean check used by a conditional effect or action. -/
inductive Condition where
  /-- True when any object matching the selector exists. -/
  | any : Selector → Condition
  /-- True when at least that many objects match the selector. -/
  | countAtLeast : Selector → Nat → Condition
  /-- True when any target of the first selector matches the second
  (CR 115.1 / 601.2c). -/
  | targetsIncludeAny : Selector → Selector → Condition
  /-- True when any object matching the selector has the given subtype
  (CR 205.3). -/
  | anySubtype : Selector → CardSubtype → Condition
  /-- True when the first trigger has not occurred since the second. -/
  | didNotHappen : Trigger → Trigger → Condition
  /-- True when the first trigger has occurred since the second. -/
  | happened : Trigger → Trigger → Condition
  /-- True when the selected player could cast a sorcery
  (CR 307.1 / 117.1a). -/
  | timeToCastSorcery : Selector → Condition
  /-- True when it is the selected player's turn (CR 500.1). -/
  | turn : Selector → Condition
  /-- True when both conditions hold. -/
  | and : Condition → Condition → Condition
deriving Repr, Inhabited, BEq

/-- Status a permanent has as it enters the battlefield (CR 110.5). -/
inductive CardState where
  /-- The permanent enters tapped. -/
  | tapped
  /-- The permanent enters attacking (CR 508.4a). -/
  | attacking
  /-- The permanent enters under the selected player's control (CR 110.2). -/
  | controlled : Selector → CardState
deriving Repr, Inhabited, BEq

-- Printed abilities, continuous effects, and actions are mutually inductive:
-- an activated ability has an action, and a continuous effect may grant an
-- ability.
mutual
/-- A keyword or other printed ability on a card or granted by an effect. -/
inductive Ability where
  | keyword : Keyword → Ability
  /-- A keyword ability that is printed with a cost, e.g. Equip {2}. -/
  | keywordWithCost : Keyword → List Cost → Ability
  /-- A keyword ability that is printed with a subtype and a cost, e.g.
  Equip Human {1} (CR 702.6). -/
  | keywordWithSubtypeAndCost : Keyword → CardSubtype → Cost → Ability
  /-- A keyword ability that is printed with a target, e.g. Enchant
  creature (CR 702.5). The `Nat` numbers the target so later clauses can
  refer to it. -/
  | keywordWithTarget : Keyword → Nat → Selector → Ability
  /-- A keyword ability printed with a resolution, e.g. a Saga chapter
  (CR 714.2). -/
  | keywordWithEffect : Keyword → List CardAction → Ability
  | activated : List Cost → CardAction → Ability
  /-- An activated ability that may be used only when the condition holds. -/
  | activatedIf : Condition → List Cost → CardAction → Ability
  /-- Number this ability so later clauses can refer to it. -/
  | abilityId : Nat → Ability → Ability
  | triggered : Trigger → CardAction → Ability
  | static : ContinuousEffect → Ability
deriving Repr, Inhabited, BEq

/-- A continuous effect granted by a spell or ability. -/
inductive ContinuousEffect where
  | gainAbility : Selector → Ability → ContinuousEffect
  | addPowerToughness : Selector → Value → Value → ContinuousEffect
  /-- Apply the given continuous effects only when the condition holds. -/
  | if : Condition → List ContinuousEffect → ContinuousEffect
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
  /-- The selected player may play the selected card. -/
  | canPlay : Selector → Selector → ContinuousEffect
  /-- The first object's base power and toughness become those of the
  second object. -/
  | setBasePowerToughnessFrom : Selector → Selector → ContinuousEffect
  /-- The selected object gains the given card type in addition to its
  other types (CR 205.1 / 613.1). -/
  | gainType : Selector → CardType → ContinuousEffect
  /-- The selected object gains the given subtype in addition to its other
  types (CR 205.3 / 613.1). -/
  | gainSubtype : Selector → CardSubtype → ContinuousEffect
  /-- The selected object has all subtypes of the given card type
  (CR 205.3 / 702.72). -/
  | gainAllSubtypes : Selector → CardType → ContinuousEffect
  /-- The selected object's power and toughness are each equal to the
  number of objects matching the second selector. -/
  | setPowerToughnessEqualToCount : Selector → Selector → ContinuousEffect
  /-- The selected objects get the given power and toughness for each
  object matching the second selector. -/
  | addPowerToughnessPer : Selector → Selector → Value → Value → ContinuousEffect
  /-- The selected player may play that many additional lands on each of
  their turns (CR 305.2b). -/
  | increaseLandPlayLimit : Selector → Value → ContinuousEffect
deriving Repr, Inhabited, BEq

/-- What a spell or ability does. `CardAction` is the printed-card name for
this tree; player input uses `Action` in `Game`. -/
inductive CardAction where
  | continuous : List ContinuousEffect → Trigger → CardAction
  | tap : Selector → CardAction
  | untap : Selector → CardAction
  /-- The selected source deals the given amount of damage to the selected
  objects. The amount may be a printed number or a computed value. -/
  | dealDamage : Selector → Selector → Value → CardAction
  /-- The selected player divides that much damage from the source among
  the selected objects (CR 601.2d). -/
  | divideDamage : Selector → Selector → Selector → Value → CardAction
  | draw : Selector → Value → CardAction
  | scry : Selector → Value → CardAction
  | sequence : List CardAction → CardAction
  /-- Perform the given actions only when the condition holds. -/
  | if : Condition → List CardAction → CardAction
  /-- Perform the first actions when the condition holds, otherwise the
  second (an “if … instead …” replacement). -/
  | ifElse : Condition → List CardAction → List CardAction → CardAction
  | optional : CardAction → CardAction
  | attach : Selector → Selector → CardAction
  /-- Choose one of the given modes (CR 700.2). -/
  | chooseMode : List CardAction → CardAction
  /-- The selected player chooses one of the given modes. Each mode has an
  ID, a condition under which it may be chosen, and the actions it
  performs (CR 700.2 / 700.2e). -/
  | chooseModeRestricted : Selector → List (Nat × Condition × List CardAction) → CardAction
  /-- Counter the selected spell (CR 701.5). -/
  | counter : Selector → CardAction
  /-- The given player may pay the cost to prevent the action. -/
  | preventable : Selector → List Cost → CardAction → CardAction
  /-- The selected player may pay the given cost. If they do, perform the
  given actions (CR 118.1 / 608.2d). -/
  | optionalPayFor : Selector → List Cost → List CardAction → CardAction
  /-- The selected player discards that many cards. -/
  | discard : Selector → Value → CardAction
  /-- Put that many counters of the given kind on the selected object. -/
  | putCounter : Selector → CounterKind → Nat → CardAction
  /-- Exile the selected object. -/
  | exile : Selector → CardAction
  /-- Exchange control of the selected objects. -/
  | exchangeControl : Selector → CardAction
  /-- Destroy the selected permanent (CR 701.7). -/
  | destroy : Selector → CardAction
  /-- The selected player gains that much life (CR 118.3). -/
  | gainLife : Selector → Value → CardAction
  /-- The selected player chooses one or more of the listed actions. -/
  | playerSelectAction : Selector → Range → List CardAction → CardAction
  /-- Put the selected object on top of its owner's library. -/
  | putOnTopOfLibrary : Selector → CardAction
  /-- Put the selected object on the bottom of its owner's library. -/
  | putOnBottomOfLibrary : Selector → CardAction
  /-- Put the selected objects into their owner's library at the given
  ordinal position from the top (CR 401.4). `1` is the top card;
  `2` is second from the top. -/
  | putIntoLibraryFromTop : Selector → Value → CardAction
  /-- Number this action so later clauses can refer to it. -/
  | actionId : Nat → CardAction → CardAction
  /-- The selected player loses that much life (CR 118.3). -/
  | loseLife : Selector → Value → CardAction
  /-- The controller sacrifices the selected object (CR 701.17). -/
  | sacrifice : Selector → CardAction
  /-- Return the selected object to its owner's hand. -/
  | returnToHand : Selector → CardAction
  /-- Put the selected object onto the battlefield. -/
  | putOntoBattlefield : Selector → CardAction
  /-- Put the selected object onto the battlefield in the given states
  (CR 110.5). -/
  | putOntoBattlefieldInState : Selector → List CardState → CardAction
  /-- Search the selected player's library. Nested actions may move or
  choose cards from that library while they are visible, then shuffle
  (CR 701.19). Nested `holdOutInLibrary` keeps selected cards in the
  library but out of the shuffle; act on them after this action.
  Nested `putOnTopOfLibrary` would be shuffled in. -/
  | searchLibraryThenShuffle : Selector → List CardAction → CardAction
  /-- Temporarily exclude the selected cards from a library shuffle.
  Held-out cards are still in the library, but not at the top, bottom,
  or among the shuffled cards. -/
  | holdOutInLibrary : Selector → CardAction
  /-- Bind the selected objects to this numbered variable. -/
  | defineVariable : Nat → Selector → CardAction
  /-- Execute the given actions for each of the given objects, binding the
  numbered variable to the current object. -/
  | forEachVariable : Nat → Selector → List CardAction → CardAction
  /-- Reveal the selected object (CR 701.19a). -/
  | reveal : Selector → CardAction
  /-- The first selected object deals damage equal to its power to the
  second (CR 701.13). -/
  | dealDamageEqualToPower : Selector → Selector → CardAction
  /-- The selected objects fight (CR 701.12). -/
  | fight : Selector → Selector → CardAction
  /-- The first selected player chooses a color. The second selected
  player adds X mana of that color. -/
  | addManaAnyColor : Selector → Selector → Value → CardAction
  /-- The first selected player chooses a color. The second selected
  player adds X mana of that color, where X is the third selected
  object's power. -/
  | addManaAnyColorEqualToPower : Selector → Selector → Selector → CardAction
  /-- The selected player adds mana matching the listed symbols, all at
  once (CR 106.4). To let the player choose among symbols, use
  `playerSelectAction`. To add any color, use
  `addManaAnyColor`. -/
  | addMana : Selector → List ManaSymbol → CardAction
  /-- The selected object or player performs a keyword action (CR 701),
  e.g. recruit, amass Goblins 1, or connive 1. -/
  | keyword : Selector → Keyword → CardAction
  /-- The selected player creates that many tokens with the given
  characteristics, entering in the given states (CR 111, CR 110.5).
  An empty state list is the usual “enters as a new object” case. -/
  | createTokens (who : Selector) (n : Value) (parts : List CardPart)
      (states : List CardState := []) : CardAction
  /-- The selected player mills that many cards (CR 701.13). -/
  | mill : Selector → Value → CardAction
  /-- The selected player surveils that many cards (CR 701.53). -/
  | surveil : Selector → Value → CardAction
  /-- The selected player copies the selected spell or ability and may
  choose new targets for the copy (CR 707). -/
  | copyWithNewTargets : Selector → Selector → CardAction
  /-- Perform the action this replacement effect is replacing (CR 614). -/
  | keepReplacedAction
  /-- Heal all damage marked on the selected object. -/
  | healAllDamage : Selector → CardAction
deriving Repr, Inhabited, BEq

/-- One printed characteristic or ability of a card face, or of a token
created by `CardAction.createTokens`. -/
inductive CardPart where
  | name : String → CardPart
  /-- Printed symbols; `ManaCost` is the engine structure, this list is the
  prototype spelling (`.manaCost [.mono .white]`). -/
  | manaCost : List ManaSymbol → CardPart
  | type : CardType → CardPart
  | supertype : CardSupertype → CardPart
  | subtype : CardSubtype → CardPart
  /-- Color indicator (CR 107.13 / 202.2e). Tokens without a mana cost use
  this for their color; colorless tokens omit it. -/
  | colorIndicator : List Color → CardPart
  | power : Nat → CardPart
  | toughness : Nat → CardPart
  | ability : Ability → CardPart
  | alternative : List CardPart → CardPart
  /-- The spelled-out actions this part performs, in order. -/
  | actions : List CardAction → CardPart
deriving Repr, Inhabited, BEq
end

/-! Predefined token characteristics from CR 111.10. -/
namespace PredefinedToken

/-- Printed Treasure token characteristics (CR 111.10a). -/
def treasureToken : List CardPart := [
  .type .artifact,
  .subtype .treasure,
  .ability
    (.activated
      [.tapSymbol, .sacrifice .this]
      (.addManaAnyColor (.controller .this) (.controller .this) 1))
]

/-- Printed Food token characteristics (CR 111.10b). -/
def foodToken : List CardPart := [
  .type .artifact,
  .subtype .food,
  .ability
    (.activated
      [.mana [.generic 2], .tapSymbol, .sacrifice .this]
      (.gainLife (.controller .this) 3))
]

end PredefinedToken

/-- Convert a Value to an Int if constant. -/
def valToInt? : Value → Option Int
  | .int p => some p
  | .nat p => some (Int.ofNat p)
  | .x | .greatestManaValue _ | .greatestToughness _ | .greatestPower _ => none

/-- Convert a Value to a Nat if it is a non-negative constant. -/
def valToNat? : Value → Option Nat
  | .nat n => some n
  | .int n => if n ≥ 0 then some n.toNat else none
  | .x | .greatestManaValue _ | .greatestToughness _ | .greatestPower _ => none

namespace ContinuousEffect

def selector : ContinuousEffect → Selector
  | .gainAbility who _ => who
  | .addPowerToughness who _ _ => who
  | .if _ (inner :: _) => selector inner
  | .if _ [] => .this
  | .reduceCost who _ => who
  | .additionalCost who _ => who
  | .replace _ _ => .this
  | .forbid _ => .this
  | .canCastWithoutPayingManaCost _ who => who
  | .canPlay _ card => card
  | .setBasePowerToughnessFrom who _ => who
  | .gainType who _ => who
  | .gainSubtype who _ => who
  | .gainAllSubtypes who _ => who
  | .setPowerToughnessEqualToCount who _ => who
  | .addPowerToughnessPer who _ _ _ => who
  | .increaseLandPlayLimit who _ => who

/-- Combined +P/+T if every effect is `addPowerToughness`. -/
def addedPT? : List ContinuousEffect → Option (Int × Int)
  | [] => some (0, 0)
  | .addPowerToughness _ vp vt :: rest =>
    match valToInt? vp, valToInt? vt, addedPT? rest with
    | some p, some t, some (p', t') => some (p + p', t + t')
    | _, _, _ => none
  | .gainAbility _ _ :: _ => none
  | .if _ _ :: _ => none
  | .reduceCost _ _ :: _ => none
  | .additionalCost _ _ :: _ => none
  | .replace _ _ :: _ => none
  | .forbid _ :: _ => none
  | .canCastWithoutPayingManaCost _ _ :: _ => none
  | .canPlay _ _ :: _ => none
  | .setBasePowerToughnessFrom _ _ :: _ => none
  | .gainType _ _ :: _ => none
  | .gainSubtype _ _ :: _ => none
  | .gainAllSubtypes _ _ :: _ => none
  | .setPowerToughnessEqualToCount _ _ :: _ => none
  | .addPowerToughnessPer _ _ _ _ :: _ => none
  | .increaseLandPlayLimit _ _ :: _ => none

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
    | .targetSet _ _ _ _ | .targetReference _ | .selected _ _ _
    | .spell | .permanentSpell | .hasTarget _ | .isTargetOf _ | .keywordAbility _
    | .player
    | .wasObjectOfAction _ | .wasObjectOfThisTrigger | .replacingObject | .wasCreatedByAction _
    | .hostOf _ | .inGraveyard | .wasObjectSince _ _ | .inLibrary | .inHand
    | .inExile | .supertype _
    | .variable _ | .topOfLibrary _ => none
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
  | .targets _ (.range (.nat lo) (.nat hi)) _
  | .targetSet _ (.range (.nat lo) (.nat hi)) _ _ =>
    if asAbility then e
    else
      { e with
        maxTargets := if hi ≤ 1 then e.maxTargets else hi
        allowsZeroTargets := e.allowsZeroTargets || lo == 0 }
  | _ => e

/-- Source of this ability gets +P/+T. -/
def leftoverSourcePump? : List ContinuousEffect → Option (Int × Int)
  | [.addPowerToughness (.source .this) vp vt] =>
    match valToInt? vp, valToInt? vt with
    | some p, some t => some (p, t)
    | _, _ => none
  | _ => none

/-- Target creature gets +P/+T (Giant Growth, Dark Deed). -/
def leftoverTargetPump? (effects : List ContinuousEffect) : Option (Int × Int) :=
  match ContinuousEffect.addedPT? effects, ContinuousEffect.targetingSelector? effects with
  | some (p, t), some sel =>
    if sel.toTargetKind == .creature then some (p, t) else none
  | _, _ => none

/-- You may play an additional land this turn. -/
def leftoverIncreaseLandPlayLimit? : List ContinuousEffect → Bool
  | [.increaseLandPlayLimit who (Value.nat 1)] =>
    who == .controller .this
  | _ => false

def compileContinuous (effects : List ContinuousEffect) (asAbility : Bool) : Effect :=
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

/-- Untap a creature you control, +P/+T on that target, and maybe attach
if the target is a Dwarf. -/
def leftoverUntapPumpAttach? : CardAction → Option (Int × Int)
  | .sequence [
      .untap ut,
      .continuous effects _,
      .if (.anySubtype _ .dwarf) [.optional (.attach _eq _to)]
    ] =>
    let youControlCreature :=
      match ut.among? with
      | some who =>
        let s := who.shape
        s.sameController && s.types.eqTypes [.creature]
      | none => false
    if youControlCreature then
      ContinuousEffect.addedPT? effects
    else none
  | _ => none

/-- Untap another target creature you control; if it has the given subtype,
put a +1/+1 counter on it. -/
def leftoverUntapPlusOneIfSubtype? : CardAction → Option String
  | .sequence [
      .untap ut,
      .if (.anySubtype _ st) [.putCounter _ .plusOnePlusOne 1]
    ] =>
    match ut.among? with
    | some who =>
      if who.shape.anotherCreatureYouControl then some st.toString else none
    | none => none
  | _ => none

/-- Draw, then discard a card. -/
def leftoverDrawDiscard? : CardAction → Option Nat
  | .sequence [.draw _who (.nat n), .discard _p 1] => some n
  | _ => none

/-- Put a +1/+1 counter on up to one target creature; a target player gains
that much life. -/
def leftoverPlusOneAndGainLife? : CardAction → Option Nat
  | .sequence [
      .putCounter sel .plusOnePlusOne 1,
      .gainLife who (.nat n)
    ] =>
    let upToOneCreature :=
      match sel with
      | .targets n (.range 0 1) among =>
        among.shape.types.eqTypes [.creature] &&
          match who with
          | .target m .player => n != m
          | _ => true
      | _ => false
    let playerTarget :=
      match who with
      | .target _ .player => true
      | _ => false
    if upToOneCreature && playerTarget then some n else none
  | _ => none

/-- Counter a spell; exile a permanent spell and allow a free cast. -/
def leftoverCounterExile? : CardAction → Bool
  | .sequence [
      .actionId _ (.counter _),
      .continuous (.replace (.putToGraveyard _) _ :: _) _
    ] => true
  | _ => false

/-- Duration “until the end of your next turn” (CR 611.2a). -/
def leftoverUntilEndOfYourNextTurn? : Trigger → Bool
  | .sequence [.turnStart, .endOfPlayerTurn who] =>
    who == .controller .this
  | _ => false

/-- Exile the top card; you may play it until the end of your next turn. -/
def leftoverExileTopPlayUntilEndOfNextTurn? : CardAction → Bool
  | .sequence [
      .actionId id (.exile (.topOfLibrary who)),
      .continuous [.canPlay permit (.wasCreatedByAction created)] duration
    ] =>
    id == created &&
      who == .controller .this &&
      permit == .controller .this &&
      leftoverUntilEndOfYourNextTurn? duration
  | _ => false

/-- Attach this Equipment to target creature you control. -/
def leftoverEquipAttach? : CardAction → Bool
  | .attach .this sel =>
    match sel.among? with
    | some among =>
      let s := among.shape
      s.sameController && s.types.eqTypes [.creature]
    | none => false
  | _ => false

/-- Equip `Subtype {cost}` when the attach target names a subtype. -/
def leftoverEquipSubtype? : CardAction → Option String
  | .attach .this sel =>
    if leftoverEquipAttach? (.attach .this sel) then
      match sel.among? with
      | some among => among.includedSubtype?
      | none => none
    else none
  | _ => none

/-- Target creature gets +P/+T; if it would die this turn, exile it instead. -/
def leftoverPumpAndExileIfDies? : CardAction → Option (Int × Int)
  | .continuous effects _ =>
    let pt :=
      effects.findSome? fun e =>
        match e with
        | .addPowerToughness _ vp vt =>
          match valToInt? vp, valToInt? vt with
          | some p, some t => some (p, t)
          | _, _ => none
        | _ => none
    let replacesDie :=
      effects.any fun e =>
        match e with
        | .replace (.putToGraveyard _) _ => true
        | _ => false
    if replacesDie then pt else none
  | _ => none

/-- Target creature gets +P/+T and gains lifelink. -/
def leftoverPumpAndLifelink? : CardAction → Option (Int × Int)
  | .continuous effects _ =>
    let pt :=
      effects.findSome? fun e =>
        match e with
        | .addPowerToughness _ vp vt =>
          match valToInt? vp, valToInt? vt with
          | some p, some t => some (p, t)
          | _, _ => none
        | _ => none
    let lifelink :=
      effects.any fun e =>
        match e with
        | .gainAbility _ (.keyword .lifelink) => true
        | _ => false
    if lifelink then pt else none
  | _ => none

/-- Creatures target player controls get +P/+T. -/
def leftoverCreaturesTargetPlayerGet? : CardAction → Option (Int × Int)
  | .continuous effects _ =>
    match ContinuousEffect.addedPT? effects, ContinuousEffect.massSelector? effects with
    | some (p, t), some among =>
      match among with
      | .intersection fs =>
        let creature := fs.any fun
          | .cardType .creature => true
          | _ => false
        let targetPlayer := fs.any fun
          | .controlled (.target _ .player) => true
          | _ => false
        if creature && targetPlayer then some (p, t) else none
      | _ => none
    | _, _ => none
  | _ => none

/-- Target player draws cards and loses life. -/
def leftoverTargetPlayerDrawLoseLife? : CardAction → Option (Nat × Nat)
  | .sequence [.draw (.target _ .player) (.nat cards), .loseLife _ (.nat life)] =>
    some (cards, life)
  | _ => none

/-- You draw cards and lose life. -/
def leftoverDrawLoseLifeSelf? : CardAction → Option (Nat × Nat)
  | .sequence [
      .draw (.controller .this) (.nat cards),
      .loseLife (.controller .this) (.nat life)
    ] =>
    some (cards, life)
  | _ => none

/-- Draw a card, lose 1 life, then amass Goblins `n`. -/
def leftoverDrawLoseLifeThenAmass? : CardAction → Option Nat
  | .sequence [
      .draw (.controller .this) 1,
      .loseLife (.controller .this) 1,
      .keyword (.controller .this) (.amass .goblin (.nat n))
    ] => some n
  | _ => none

/-- Return up to one creature card from your graveyard, then amass Goblins `n`. -/
def leftoverReturnCreatureFromGyThenAmass? : CardAction → Option Nat
  | .sequence [.returnToHand sel, .keyword (.controller .this) (.amass .goblin (.nat n))] =>
    match sel with
    | .targets _ (.range 0 1) among | .target _ among =>
      if among.shape.types.eqTypes [.creature] && among.includesInGraveyard then
        some n
      else none
    | _ => none
  | _ => none

/-- Target creature gets +P/+T and gains keywords. -/
def leftoverPumpAndGrantKeywords? : CardAction → Option (Int × Int × Keywords)
  | .continuous effects _ =>
    let pt :=
      effects.findSome? fun e =>
        match e with
        | .addPowerToughness _ vp vt =>
          match valToInt? vp, valToInt? vt with
          | some p, some t => some (p, t)
          | _, _ => none
        | _ => none
    let kws := grantedKeywords effects
    match pt with
    | some (p, t) =>
      if kws == Keywords.none then none else some (p, t, kws)
    | none => none
  | _ => none

/-- True when a selector names a controller or a target (not “all creatures”). -/
def namesControllerOrTarget : Selector → Bool
  | .controlled _ | .target _ _ | .targets _ _ _ | .targetSet _ _ _ _
  | .targetReference _ | .selected _ _ _ => true
  | .not s => namesControllerOrTarget s
  | .intersection (f :: fs) => namesControllerOrTarget f || namesControllerOrTarget (.intersection fs)
  | .union (f :: fs) => namesControllerOrTarget f || namesControllerOrTarget (.union fs)
  | _ => false

/-- All creatures get +P/+T (not only yours, and not a targeted player's). -/
def leftoverAllCreaturesGet? : CardAction → Option (Int × Int)
  | .continuous effects _ =>
    match ContinuousEffect.addedPT? effects, ContinuousEffect.massSelector? effects with
    | some (p, t), some among =>
      let s := among.shape
      if s.types.eqTypes [.creature] && !s.sameController &&
          !namesControllerOrTarget among then
        some (p, t)
      else none
    | _, _ => none
  | _ => none

/-- Target creature gets +P/+T, then you draw a card. -/
def leftoverPumpThenDraw? : CardAction → Option (Int × Int)
  | .sequence [.continuous effects _, .draw (.controller .this) 1] =>
    match ContinuousEffect.addedPT? effects, ContinuousEffect.targetingSelector? effects with
    | some (p, t), some sel =>
      if sel.toTargetKind == .creature then some (p, t) else none
    | _, _ => none
  | _ => none

/-- Target creature gains vigilance and can't be blocked; draw a card. -/
def leftoverGrantVigilanceUnblockable? : CardAction → Bool
  | .sequence [.continuous effects _, .draw (.controller .this) 1] =>
    let vigil := grantedKeywords effects |>.vigilance
    let unblockable :=
      effects.any fun
        | .forbid (.block .any sel) =>
          match sel with
          | .target _ among => among.shape.types.eqTypes [.creature]
          | .targetReference _ => true
          | _ =>
            match sel.among? with
            | some among => among.shape.types.eqTypes [.creature]
            | none => false
        | _ => false
    vigil && unblockable
  | _ => false

/-- Target creature gets +P/+T, then exile the top card and play it until
the end of your next turn. -/
def leftoverPumpThenExileTopPlay? : CardAction → Option (Int × Int)
  | .sequence [
      .continuous effects _,
      .actionId id (.exile (.topOfLibrary who)),
      .continuous [.canPlay permit (.wasCreatedByAction created)] duration
    ] =>
    if leftoverExileTopPlayUntilEndOfNextTurn?
        (.sequence [
          .actionId id (.exile (.topOfLibrary who)),
          .continuous [.canPlay permit (.wasCreatedByAction created)] duration
        ]) then
      leftoverTargetPump? effects
    else none
  | _ => none

/-- Target creature can't be blocked this turn. -/
def leftoverTargetCantBeBlocked? : CardAction → Bool
  | .continuous [.forbid (.block .any sel)] _ =>
    match sel with
    | .target _ among => among.shape.types.eqTypes [.creature]
    | _ =>
      match sel.among? with
      | some among => among.shape.types.eqTypes [.creature]
      | none => false
  | _ => false

/-- Tap target creature, then scry and draw. -/
def leftoverTapScryDraw? : CardAction → Option (Nat × Nat)
  | .sequence [.tap sel, .scry _ (.nat scryN), .draw _ (.nat drawN)] =>
    if sel.toTargetKind == .creature then some (scryN, drawN) else none
  | _ => none

/-- Return target spell to its owner's hand, then draw a card. -/
def leftoverReturnSpellDraw? : CardAction → Bool
  | .sequence [.returnToHand sel, .draw _ 1] => sel.toTargetKind == .spell
  | _ => false

/-- Destroy target artifact or enchantment; you gain life. -/
def leftoverDestroyArtEnchGainLife? : CardAction → Option Nat
  | .sequence [.destroy sel, .gainLife _ (.nat n)] =>
    if sel.toTargetKind == .artifactOrEnchantment then some n else none
  | _ => none

/-- Destroy target artifact or land; creatures without flying can't block. -/
def leftoverDestroyArtOrLandNonflyers? : CardAction → Bool
  | .sequence [
      .destroy sel,
      .continuous [.forbid (.block (.not (.keyword .flying)) _)] _
    ] =>
    sel.toTargetKind == .artifactOrLand
  | _ => false

/-- Target creature becomes an artifact and gains indestructible. -/
def leftoverBecomeArtifactIndestructible? : CardAction → Bool
  | .continuous effects _ =>
    let becomesArtifact :=
      effects.any fun
        | .gainType sel .artifact => sel.toTargetKind == .creature
        | _ => false
    becomesArtifact && (grantedKeywords effects).indestructible
  | _ => false

/-- Put a +1/+1 counter on target creature; it gains lifelink and
indestructible. -/
def leftoverPlusOneLifelinkIndestructible? : CardAction → Bool
  | .sequence [.putCounter sel .plusOnePlusOne 1, .continuous effects _] =>
    let kws := grantedKeywords effects
    sel.toTargetKind == .creature && kws.lifelink && kws.indestructible
  | _ => false

/-- A creature you control deals damage equal to its power to an opponent's
creature. -/
def leftoverCreatureYouControlDealsPowerToOppCreature? : CardAction → Bool
  | .dealDamageEqualToPower src dest =>
    src.toTargetKind == .creatureYouControl && dest.toTargetKind == .oppCreature
  | _ => false

/-- Put a +1/+1 counter on a creature you control; it gains trample and
hexproof. -/
def leftoverPlusOnePlusOneTrampleHexproof? : CardAction → Bool
  | .sequence [
      .putCounter sel .plusOnePlusOne 1,
      .continuous effects _
    ] =>
    let youControlCreature :=
      match sel.among? with
      | some who =>
        let s := who.shape
        s.sameController && s.types.eqTypes [.creature]
      | none => false
    let kws := grantedKeywords effects
    youControlCreature && kws.trample && kws.hexproof
  | _ => false

/-- Put +1/+1 counters on a creature you control; it gains vigilance. -/
def leftoverPlusOneVigilance? : CardAction → Option Nat
  | .sequence [
      .putCounter sel .plusOnePlusOne n,
      .continuous effects _
    ] =>
    let youControlCreature :=
      match sel.among? with
      | some who =>
        let s := who.shape
        s.sameController && s.types.eqTypes [.creature]
      | none => false
    let kws := grantedKeywords effects
    if youControlCreature && kws.vigilance then some n else none
  | _ => none

/-- Become a creature of the given subtype with P/T equal to lands you
control. -/
def leftoverBecomeSubtypeWithLandsPT? : CardAction → Option String
  | .continuous effects _ =>
    let subtype :=
      effects.findSome? fun
        | .gainSubtype _ st => some st.toString
        | _ => none
    let becomesCreature :=
      effects.any fun
        | .gainType _ .creature => true
        | _ => false
    let landsPT :=
      effects.any fun
        | .setPowerToughnessEqualToCount _ among =>
          among.shape.landYouControl
        | _ => false
    if becomesCreature && landsPT then subtype else none
  | _ => none

/-- Spend this mana only on Elf spells and activated abilities of Elf
sources. -/
def leftoverElfRestrictedSpend? : Trigger → Bool
  | .not
      (.or
        (.castSpell (.subtype .elf))
        (.activateAbility (.subtype .elf))) => true
  | _ => false

/-- Spend this mana only to cast an instant or sorcery spell. -/
def leftoverInstantOrSorcerySpend? : Trigger → Bool
  | .not (.castSpell among) =>
    among.shape.types.eqTypes [.instant, .sorcery]
  | .not (.or (.castSpell a) (.castSpell b)) =>
    (a == .cardType .instant && b == .cardType .sorcery) ||
      (a == .cardType .sorcery && b == .cardType .instant)
  | _ => false

/-- Tap and add mana of any color equal to this object's power, spendable
only on Elf spells and Elf sources. -/
def leftoverTapAddAnyColorEqualToPower? (costs : List Cost) : CardAction → Bool
  | .sequence [
      .actionId id (.addManaAnyColorEqualToPower chooser gainer power),
      .continuous [.forbid (.spendManaCreatedByAction spendId restriction)] _
    ] =>
    id == spendId &&
      leftoverElfRestrictedSpend? restriction &&
      Cost.hasTapSymbol costs &&
      chooser == .controller .this &&
      gainer == .controller .this &&
      (power == .this || power == .source .this)
  | _ => false

/-- `{T}: Add` one mana of any color, spendable only on instant and
sorcery spells. -/
def leftoverTapAddAnyColorForInstantOrSorcery? (costs : List Cost) : CardAction → Bool
  | .sequence [
      .actionId id (.addManaAnyColor chooser gainer 1),
      .continuous [.forbid (.spendManaCreatedByAction spendId restriction)] _
    ] =>
    id == spendId &&
      leftoverInstantOrSorcerySpend? restriction &&
      costs == [.tapSymbol] &&
      chooser == .controller .this &&
      gainer == .controller .this
  | _ => false

/-- Mana produced when this symbol is added to a pool (CR 106.4). -/
def addedManaType? : ManaSymbol → Option ManaType
  | .colored c => some (.colored c)
  | .colorless => some .colorless
  | .generic _ | .hybrid _ _ | .monoOrDouble _ | .monoOrColorless _
  | .phyrexianMono _ | .phyrexianGeneric | .phyrexianHybrid _ _ | .x | .snow =>
    none

/-- Types added by a list of symbols, or `none` if any symbol is not
addable mana. -/
def addedManaTypes? (syms : List ManaSymbol) : Option (Array ManaType) :=
  let ts := syms.filterMap addedManaType?
  if ts.length == syms.length then some ts.toArray else none

/-- One `addMana` option: `who` adds a single listed type. -/
def leftoverAddManaOne? (who : Selector) : CardAction → Option ManaType
  | .addMana gainer [sym] =>
    if gainer == who then addedManaType? sym else none
  | _ => none

/-- `{T}: Add` the listed types, all at once (Llanowar Elves). -/
def leftoverTapAddMana? (costs : List Cost) (action : CardAction) :
    Option (Array ManaType) :=
  match action with
  | .addMana who syms =>
    if costs == [.tapSymbol] && who == .controller .this then
      addedManaTypes? syms
    else none
  | _ => none

/-- `{T}: Add {A} or {B}` as a tap-only mana ability. Each listed action
must be `addMana` of one symbol; the player chooses one. -/
def leftoverTapAddOneOf? (costs : List Cost) : CardAction → Option (Array ManaType)
  | .playerSelectAction who (.range 1 1) actions =>
    if costs == [.tapSymbol] && who == .controller .this && actions.length >= 2 then
      let ts := actions.filterMap (leftoverAddManaOne? who)
      if ts.length == actions.length then some ts.toArray else none
    else none
  | _ => none

/-- Add one mana of any color. -/
def leftoverAddAnyColor? : CardAction → Bool
  | .addManaAnyColor _ _ 1 => true
  | _ => false

/-- Replacement “this enters tapped”. -/
def leftoverEntersTapped? : List CardAction → Bool
  | [.putOntoBattlefieldInState obj [.tapped]] =>
    obj == .this || obj == .source .this
  | _ => false

/-- Heal all marked damage on this, then perform the replaced action. -/
def leftoverHealThenKeepReplaced? : List CardAction → Bool
  | [.healAllDamage who, .keepReplacedAction] =>
    who == .this || who == .source .this
  | _ => false

/-- Put +1/+1 counters on a targeted creature you control, optionally of
listed subtypes. -/
def leftoverPlusOneOnTarget? : CardAction → Option Effect
  | .putCounter sel .plusOnePlusOne n =>
    match sel.among? with
    | some among =>
      if among.shape.sameController && among.shape.types.eqTypes [.creature] then
        some (Effect.plusOneOnTarget n among.includedSubtypes.toArray)
      else none
    | none => none
  | _ => none

/-- Set another creature you control's base P/T equal to this source. -/
def leftoverSetOtherBasePT? : List ContinuousEffect → Bool
  | [.setBasePowerToughnessFrom who (.source .this)] =>
    match who with
    | .targets _ (.range 0 1) among => among.shape.anotherCreatureYouControl
    | _ => false
  | _ => false

/-- Nested search actions: put a basic land onto the battlefield tapped,
or reveal a found card and put it into hand. -/
def leftoverSearchActions? : List CardAction → Option Effect
  | [.putOntoBattlefieldInState sel [.tapped]] =>
    match sel.selectedAmong? with
    | some among =>
      if among.basicLandInLibrary then some Effect.searchBasicLandTapped else none
    | none => none
  | [.defineVariable id sel, .reveal (.variable id'), .returnToHand (.variable id'')] =>
    if id == id' && id == id'' then
      match sel.selectedAmong? with
      | some among =>
        if among.basicLandInLibrary then some Effect.searchBasicLandToHand
        else
          match among.includedSubtype? with
          | some t =>
            if among.includesInLibrary then some (Effect.searchLandTypeToHand t) else none
          | none => none
      | none => none
    else none
  | [
      .defineVariable id sel,
      .reveal (.variable id'),
      .putOntoBattlefieldInState
        (.selected _ (.range 1 1) (.variable id'')) [.tapped],
      .returnToHand (.variable id''')
    ] =>
    if id == id' && id == id'' && id == id''' then
      match sel.selectedAmong? with
      | some among =>
        if among.basicLandInLibrary then some Effect.searchTwoBasicsSplit else none
      | none => none
    else none
  | _ => none

/-- Search a library, act on the found cards, then shuffle. -/
def leftoverSearchLibraryThenShuffle? : CardAction → Option Effect
  | .searchLibraryThenShuffle _ actions => leftoverSearchActions? actions
  | _ => none

/-- Each player sacrifices a creature they choose. -/
def leftoverEachPlayerSacrificesCreature? : CardAction → Bool
  | .forEachVariable n among [
      .sacrifice
        (.selected chooser (.range 1 1) sacAmong)
    ] =>
    among == .player &&
      chooser == .variable n &&
      sacAmong.shape.types.eqTypes [.creature]
  | _ => false

/-- Each opponent loses N life and you gain N life. -/
def leftoverEachOpponentLoseLifeYouGain? : CardAction → Option Nat
  | .sequence [.loseLife dest (.nat n), .gainLife who (.nat m)] =>
    if who == .controller .this && n == m then
      match dest with
      | .opponent (.controller .this) => some n
      | _ => none
    else none
  | _ => none

/-- Owner puts the targeted opponent creature into their library second
from the top or on the bottom, then up to one target creature you control
connives. -/
def leftoverOwnerPutsLibraryThenConnive? : CardAction → Bool
  | .sequence [
      .playerSelectAction chooser (.range 1 1)
        [.putIntoLibraryFromTop t1 2, .putOnBottomOfLibrary t2],
      .keyword who (.connive (.nat 1))
    ] =>
    match t1 with
    | .target n among =>
      t2 == .targetReference n &&
        among.toTargetKind == .oppCreature &&
        chooser == .owner (.targetReference n) &&
        match who with
        | .targets _ (.range 0 1) dest =>
          dest.shape.sameController && dest.shape.types.eqTypes [.creature]
        | _ => false
    | _ => false
  | _ => false

/-- Put +1/+1 counters on each other permanent you control of a subtype. -/
def leftoverPlusOneOnEachOtherSubtype? : CardAction → Option Effect
  | .putCounter sel .plusOnePlusOne n =>
    if sel.among?.isNone then
      match sel.shape.anotherSubtypeYouControl with
      | some st => some (Effect.plusOneOnEachOtherSubtype st n)
      | none => none
    else none
  | _ => none

/-- Sacrifice one matching permanent the player chooses, not every match. -/
def leftoverSacrificeOneArtifact? : Selector → Bool
  | .selected _ (.range 1 1) among => among.shape.types.eqTypes [.artifact]
  | _ => false

/-- You may sacrifice an artifact or discard a card. If you do, draw. -/
def leftoverMaySacArtifactOrDiscardDraw? : CardAction → Option Nat
  | .sequence [
      .optional
        (.actionId id
          (.playerSelectAction _ (.range 1 1) [
            .sacrifice sac,
            .discard _ 1])),
      .if (.happened (.actionWithId id') _) [.draw _ (.nat n)]
    ] =>
    if id == id' && leftoverSacrificeOneArtifact? sac then some n else none
  | _ => none

/-- Draw three cards, then discard two unless you discard an artifact. -/
def leftoverDrawThreeDiscardUnlessArtifact? : CardAction → Option Bool
  | .sequence [
      .draw _ 3,
      .preventable who [.discard art] (.discard _ 2)
    ] =>
    if who == .controller .this && art.shape.types.eqTypes [.artifact] then
      some true
    else none
  | _ => none

/-- Choose up to two: return an artifact, creature, enchantment, or land
card from your graveyard to your hand. -/
def leftoverReturnUpToTwoGyModal? : CardAction → Option Bool
  | .playerSelectAction _ (.range 0 2) modes =>
    let gyReturns :=
      modes.all fun
        | .returnToHand sel => Selector.includesInGraveyard sel
        | _ => false
    if modes.length == 4 && gyReturns then some true else none
  | _ => none

/-- Target player gains life, searches a basic land onto the battlefield
tapped, and you put a +1/+1 counter on up to one creature. -/
def leftoverGainLifeSearchBasicPlusOne? : CardAction → Option Nat
  | .sequence [
      .gainLife who (.nat n),
      .searchLibraryThenShuffle _ actions,
      .putCounter sel .plusOnePlusOne 1
    ] =>
    let playerNum : Option Nat :=
      match who with
      | .target n .player => some n
      | _ => none
    let player := playerNum.isSome || who == .player
    let searchOk := leftoverSearchActions? actions == some Effect.searchBasicLandTapped
    let creatureNum : Option Nat :=
      match sel with
      | .targets n (.range 0 1) among =>
        if among.shape.types.eqTypes [.creature] then some n else none
      | .target n among =>
        if among.shape.types.eqTypes [.creature] then some n else none
      | _ => none
    let numsOk :=
      match playerNum, creatureNum with
      | some p, some c => p != c
      | _, _ => creatureNum.isSome
    if player && searchOk && numsOk then some n else none
  | _ => none

/-- Source gets +P/+0 and creatures you control gain trample. -/
def leftoverSourceGetsAndTeamTrample? : List ContinuousEffect → Option Int
  | effects =>
    let pt :=
      effects.findSome? fun
        | .addPowerToughness (.source .this) vp vt =>
          match valToInt? vp, valToInt? vt with
          | some p, some t => if t == 0 then some p else none
          | _, _ => none
        | _ => none
    let trample :=
      effects.any fun
        | .gainAbility among (.keyword .trample) =>
          among.shape.sameController && among.shape.types.eqTypes [.creature]
        | _ => false
    if trample then pt else none

/-- Put a +1/+1 counter on target creature; it gains lifelink. -/
def leftoverPlusOneAndLifelinkTarget? : CardAction → Bool
  | .sequence [.putCounter sel .plusOnePlusOne 1, .continuous effects _] =>
    let kws := grantedKeywords effects
    sel.toTargetKind == .creature && kws.lifelink && !kws.indestructible
  | _ => false

/-- Choose tap or untap target nonland permanent. -/
def leftoverTapOrUntapNonland? : List CardAction → Bool
  | [.tap s1, .untap s2] | [.untap s1, .tap s2] =>
    s1.toTargetKind == .nonland && s2.toTargetKind == .nonland
  | _ => false

/-- Choose tap target opponent creature or untap target creature you
control. -/
def leftoverTapOppOrUntapYours? : List CardAction → Bool
  | [.tap s1, .untap s2] =>
    s1.toTargetKind == .oppCreature && s2.toTargetKind == .creatureYouControl
  | [.untap s1, .tap s2] =>
    s1.toTargetKind == .creatureYouControl && s2.toTargetKind == .oppCreature
  | _ => false

/-- Choose: +1/+1 on up to two creatures, or return an artifact or
enchantment card from your graveyard. -/
def leftoverPlusOnesOrReturnArtEnch? : List CardAction → Bool
  | [a, b] =>
    let plusOnes (x : CardAction) : Option Nat :=
      match x with
      | .putCounter (.targets n (.range 0 2) among) .plusOnePlusOne 1 =>
        if among.shape.types.eqTypes [.creature] then some n else none
      | _ => none
    let ret (x : CardAction) : Option Nat :=
      match x with
      | .returnToHand (.target n among) =>
        if Selector.includesInGraveyard among &&
            (among.toTargetKind == .artifactOrEnchantment ||
              among.toTargetKind == .permanent) then
          some n
        else none
      | _ => none
    match plusOnes a, ret b with
    | some n, some m => n != m
    | _, _ =>
      match plusOnes b, ret a with
      | some n, some m => n != m
      | _, _ => false
  | _ => false

/-- Attach target Equipment you control to up to one target creature you
control. -/
def leftoverAttachTargetEquipment? : CardAction → Bool
  | .attach eq cre =>
    let destOk (dest : Selector) : Bool :=
      dest.shape.sameController && dest.shape.types.eqTypes [.creature]
    match eq.among?, cre with
    | some among, .targets _ (.range 0 1) dest =>
      Selector.leftoverDistinctTargetNumbers eq cre &&
        among.shape.sameController &&
        among.includedSubtype? == some "Equipment" &&
        destOk dest
    | some among, .target _ dest =>
      Selector.leftoverDistinctTargetNumbers eq cre &&
        among.shape.sameController &&
        among.includedSubtype? == some "Equipment" &&
        destOk dest
    | _, _ => false
  | _ => false

/-- Battlefield states that are exactly tapped (CR 110.5). -/
def leftoverTappedOnly : List CardState → Bool
  | [.tapped] => true
  | _ => false

/-- Battlefield states that are tapped and attacking (order-independent). -/
def leftoverTappedAndAttacking : List CardState → Bool
  | [.tapped, .attacking] => true
  | [.attacking, .tapped] => true
  | _ => false

/-- True when the condition is that this object's host is legendary. -/
def leftoverHostIsLegendary : Condition → Bool
  | .any (.intersection fs) =>
    fs.contains (.hostOf .this) && fs.contains (.supertype .legendary)
  | _ => false

/-- Battlefield states that are exactly tapped under the selected object's
owner's control (order-independent). -/
def leftoverTappedUnderOwner (obj : Selector) : List CardState → Bool
  | [.tapped, .controlled who] => who == .owner obj
  | [.controlled who, .tapped] => who == .owner obj
  | _ => false

/-- Exile then return the same objects tapped under their owner's control. -/
def leftoverExileThenReturnTapped? : CardAction → Option Selector
  | .sequence [
      .actionId id (.exile sel),
      .putOntoBattlefieldInState (.wasCreatedByAction id') states
    ] =>
    if id == id' && leftoverTappedUnderOwner (.wasCreatedByAction id') states then
      some sel
    else none
  | _ => none

/-- Find, reveal, and hold out a basic land while searching so shuffle
does not mix it back in. -/
def leftoverSearchBasicHoldOut? : List CardAction → Option Nat
  | [.defineVariable id sel, .reveal (.variable id'), .holdOutInLibrary (.variable id'')] =>
    if id == id' && id == id'' then
      match sel.selectedAmong? with
      | some among => if among.basicLandInLibrary then some id else none
      | none => none
    else none
  | _ => none

/-- Search a basic land, hold it out, shuffle, then put that card on top. -/
def leftoverSearchBasicOnTop? : CardAction → Bool
  | .sequence [
      .searchLibraryThenShuffle _ actions,
      .putOnTopOfLibrary (.variable id)
    ] => leftoverSearchBasicHoldOut? actions == some id
  | _ => false

/-- Keyword actions that compile to a named `Effect`. -/
def leftoverKeywordAction? : Keyword → Option Effect
  | .recruit => some Effect.recruit
  | .amass .goblin (.nat n) => some (Effect.amassGoblins n)
  | .amass .orc (.nat n) => some (Effect.ofTrigger (.amassOrcs n))
  | .connive (.nat 1) => some Effect.connive
  | _ => none

/-- Flattened token characteristics used to recover a `TokenKind`. -/
structure TokenParts where
  name : String := ""
  types : List CardType := []
  subtypes : List String := []
  colors : ColorSet := {}
  power : Option Nat := none
  toughness : Option Nat := none
  keywords : Keywords := Keywords.none
deriving Repr, Inhabited, BEq

def collectTokenParts (parts : List CardPart) : TokenParts :=
  parts.foldl
    (fun acc p =>
      match p with
      | .name n => { acc with name := n }
      | .type t => { acc with types := acc.types ++ [t] }
      | .subtype s => { acc with subtypes := acc.subtypes ++ [s.toString] }
      | .colorIndicator cs =>
        { acc with colors := cs.foldl ColorSet.insert acc.colors }
      | .power n => { acc with power := some n }
      | .toughness n => { acc with toughness := some n }
      | .ability (.keyword k) =>
        { acc with keywords := acc.keywords.merge k.toKeywords }
      | _ => acc)
    {}

/-- True when the collected color indicator is exactly that color. -/
def leftoverIsColor (p : TokenParts) (c : Color) : Bool :=
  p.colors == ColorSet.singleton c

/-- The selected player is this object's controller (“you create”). -/
def leftoverYou : Selector → Bool
  | .controller .this => true
  | _ => false

/-- Destroy target creature, then surveil 1. -/
def leftoverDestroyCreatureSurveil? : CardAction → Bool
  | .sequence [.destroy sel, .surveil who 1] =>
    sel.toTargetKind == .creature && leftoverYou who
  | _ => false

/-- Printed Redwing token: legendary 1/1 blue Bird Scout with flying and
“Whenever Redwing attacks, surveil 1.” -/
def leftoverRedwingToken? (parts : List CardPart) : Bool :=
  let p := collectTokenParts parts
  let legendary :=
    parts.any fun
      | .supertype .legendary => true
      | _ => false
  let attackSurveil :=
    parts.any fun
      | .ability (.triggered (.attack .this .all) (.surveil who 1)) =>
        leftoverYou who
      | _ => false
  p.name == "Redwing" && legendary && p.types.contains .creature &&
    p.subtypes.contains "Bird" && p.subtypes.contains "Scout" &&
    leftoverIsColor p .blue && p.power == some 1 && p.toughness == some 1 &&
    p.keywords.flying && attackSurveil

/-- This object or its source, for spell-shaped keyword compile. -/
def leftoverThis : Selector → Bool
  | .this | .source .this => true
  | _ => false

/-- The source of this ability on the stack (CR 113.7), not the ability itself. -/
def leftoverSourceThis : Selector → Bool
  | .source .this => true
  | _ => false

/-- Opponents of this object's controller. -/
def leftoverOpponents : Selector → Bool
  | .opponent who => leftoverYou who
  | _ => false

/-- A numbered target that is a creature you control. -/
def leftoverCreatureYouControlTarget? : Selector → Bool
  | .target _ among =>
    among.shape.sameController && among.shape.types.eqTypes [.creature]
  | _ => false

/-- The host of Equipment you control (an equipped creature you control). -/
def leftoverEquippedCreatureYouControl : Selector → Bool
  | .hostOf among =>
    among.shape.sameController && among.includedSubtype? == some "Equipment"
  | _ => false

/-- Match printed token characteristics to a modeled `TokenKind`. -/
def leftoverTokenKind? (parts : List CardPart) : Option TokenKind :=
  let p := collectTokenParts parts
  let has (st : String) : Bool := p.subtypes.contains st
  if has "Treasure" then some .treasure
  else if has "Food" then some .food
  else if has "Clue" then some .clue
  else if p.name == "Vibranium" then some .vibranium
  else if p.types.contains .creature then
    match p.power, p.toughness with
    | some 2, some 2 =>
      if has "Dwarf" && leftoverIsColor p .red then some .dwarf
      else if has "Wolf" then some .wolf
      else if has "Bear" then some .bear
      else if has "Robot" && has "Villain" then some .robotVillain22
      else none
    | some 1, some 1 =>
      if has "Spirit" && p.keywords.flying && leftoverIsColor p .white then
        some .spirit
      else if has "Human" && has "Soldier" then some .humanSoldier
      else if has "Soldier" && leftoverIsColor p .white then some .soldier11white
      else if has "Elf" then some .elf
      else if has "Squirrel" then some .squirrel11green
      else if has "Insect" then some .insect11green
      else if p.name == "Moloid" then some .moloid
      else none
    | some 3, some 2 =>
      if has "Hero" && p.keywords.vigilance && leftoverIsColor p .white then
        some .hero32vigilance
      else none
    | some 2, some 1 =>
      if has "Villain" && p.keywords.menace && leftoverIsColor p .black then
        some .villain21menace
      else none
    | some 4, some 4 =>
      if has "Bird" && has "Soldier" && p.keywords.flying then some .birdSoldier
      else none
    | some 3, some 1 =>
      if has "Wall" && p.keywords.defender then some .wall
      else none
    | some 6, some 6 =>
      if has "Dragon" && p.keywords.flying then some .dragon
      else none
    | some 6, some 5 =>
      if p.keywords.hexproof then some .leviathan65hexproof
      else none
    | some 0, some 4 =>
      if has "Wall" && p.keywords.defender then some .wall04defender
      else none
    | some 3, some 3 =>
      if p.name == "Doombot" || (has "Robot" && has "Villain") then some .doombot
      else none
    | _, _ => none
  else none

/-- `createTokens` for this controller, with a known token kind. -/
def leftoverCreateTokensKindN? : CardAction → Option (TokenKind × Nat)
  | .createTokens who n parts [] =>
    if leftoverYou who then
      match leftoverTokenKind? parts, valToNat? n with
      | some k, some n => some (k, n)
      | _, _ => none
    else none
  | _ => none

/-- Create `n` Spirit tokens, tapped, optionally also attacking. -/
def leftoverCreateTappedSpirits (n : Nat) (attacking : Bool) : CardAction → Bool
  | .createTokens who k parts states =>
    leftoverYou who && valToNat? k == some n && leftoverTokenKind? parts == some .spirit &&
      (if attacking then leftoverTappedAndAttacking states
       else leftoverTappedOnly states)
  | _ => false

/-- If the equipped creature is legendary, create tapped-and-attacking
Spirits; otherwise create tapped Spirits. -/
def leftoverIfElseCreateSpiritsForEquipped? : CardAction → Bool
  | .ifElse cond [th] [el] =>
    leftoverHostIsLegendary cond &&
      leftoverCreateTappedSpirits 2 true th &&
      leftoverCreateTappedSpirits 2 false el
  | _ => false

/-- Create tokens, then creatures you control get +P/+T. -/
def leftoverCreateThenTeamPump? : CardAction → Option Effect
  | .sequence [.createTokens who n parts [], .continuous effects _] =>
    match leftoverTokenKind? parts, valToNat? n, ContinuousEffect.addedPT? effects,
        ContinuousEffect.massSelector? effects with
    | some kind, some n, some (p, t), some among =>
      if leftoverYou who && among.shape.sameController &&
          among.shape.types.eqTypes [.creature] then
        some (Effect.createTokensThenTeamPump kind n p t)
      else none
    | _, _, _, _ => none
  | _ => none

/-- Grant “whenever this deals combat damage to a player, create a Treasure”. -/
def leftoverGrantCombatDamageCreateTreasure? : List ContinuousEffect → Bool
  | [.gainAbility sel (.triggered (.combatDamage who dest) action)] =>
    (who == .this || who == .source .this) && dest == .player &&
      sel.toTargetKind == .creature &&
      leftoverCreateTokensKindN? action == some (.treasure, 1)
  | _ => false

/-- Creatures you control gain keywords until end of turn. -/
def leftoverTeamGain? (effects : List ContinuousEffect) : Option Keywords :=
  match ContinuousEffect.massSelector? effects with
  | some among =>
    let kws := grantedKeywords effects
    if among.shape.sameController && among.shape.types.eqTypes [.creature] &&
        kws != Keywords.none then
      some kws
    else none
  | none => none

/-- Matching subtypes you control gain menace until end of turn. -/
def leftoverSubtypesGainMenace? (effects : List ContinuousEffect) :
    Option (Array String) :=
  match ContinuousEffect.massSelector? effects with
  | some among =>
    let kws := grantedKeywords effects
    let sts := among.includedSubtypes
    if among.shape.sameController && kws.menace &&
        kws == Keyword.menace.toKeywords && !sts.isEmpty then
      some sts.toArray
    else none
  | none => none

/-- Choose: +1/+1 on a Wolf you control, or create a Treasure. -/
def leftoverWolfPlusOneOrTreasure? : List CardAction → Bool
  | [a, b] =>
    let plusWolf (x : CardAction) : Bool :=
      match x with
      | .putCounter sel .plusOnePlusOne 1 =>
        let s := sel.targetingShape
        s.sameController && s.subtype == some "Wolf"
      | _ => false
    let treasure (x : CardAction) : Bool :=
      leftoverCreateTokensKindN? x == some (.treasure, 1)
    (plusWolf a && treasure b) || (plusWolf b && treasure a)
  | _ => false

/-- Choose: create a Food or a Treasure. -/
def leftoverCreateFoodOrTreasure? : List CardAction → Bool
  | [a, b] =>
    let kind (x : CardAction) : Option TokenKind :=
      match leftoverCreateTokensKindN? x with
      | some (k, 1) => some k
      | _ => none
    match kind a, kind b with
    | some .food, some .treasure | some .treasure, some .food => true
    | _, _ => false
  | _ => false

/-- Sacrifice another creature or artifact the player chooses. -/
def leftoverSacrificeAnotherCreatureOrArtifact? : Selector → Bool
  | .selected _ (.range 1 1) among =>
    among.shape.other && among.shape.sameController &&
      (among.shape.types.eqTypes [.creature, .artifact] ||
        among.shape.types.eqTypes [.artifact, .creature])
  | _ => false

/-- You may sacrifice another creature or artifact. If you do, draw and
create a Treasure. -/
def leftoverMaySacDrawTreasure? : CardAction → Bool
  | .sequence [
      .optional (.actionId id (.sacrifice sel)),
      .if (.happened (.actionWithId id') _)
        [.draw _ 1, .createTokens who 1 parts []]
    ] =>
    id == id' && leftoverSacrificeAnotherCreatureOrArtifact? sel &&
      leftoverYou who && leftoverTokenKind? parts == some .treasure
  | .sequence [
      .optional (.actionId id (.sacrifice sel)),
      .if (.happened (.actionWithId id') _)
        [.createTokens who 1 parts [], .draw _ 1]
    ] =>
    id == id' && leftoverSacrificeAnotherCreatureOrArtifact? sel &&
      leftoverYou who && leftoverTokenKind? parts == some .treasure
  | _ => false

/-- Creature cards in this object's controller's graveyard. -/
def leftoverYourGyCreatures? : Selector → Bool
  | .intersection fs =>
    fs.any (fun s => s == .inGraveyard) &&
      fs.any (fun
        | .cardType .creature => true
        | _ => false) &&
      fs.any (fun
        | .owner (.controller .this) => true
        | _ => false)
  | _ => false

/-- Return a targeted permanent card from your graveyard that was put
there this turn. -/
def leftoverEnterReturnGyPermanentThisTurn? : CardAction → Bool
  | .returnToHand sel =>
    match sel.among? with
    | some among =>
      among.includesInGraveyard && among.shape.mustBePermanent &&
        among.wasObjectOfPutToGraveyardThisTurn?
    | none => false
  | _ => false

/-- Return target creature card from your graveyard to your hand. -/
def leftoverEnterReturnCreatureFromGyToHand? : CardAction → Bool
  | .returnToHand (.target _ among) => leftoverYourGyCreatures? among
  | _ => false

/-- Return up to one targeted nonland, nontoken permanent. -/
def leftoverEnterReturnNonlandNontoken? : CardAction → Bool
  | .returnToHand (.targets _ (.range 0 1) among) =>
    among.shape.nonland && among.shape.nontoken
  | _ => false

/-- This fights up to one other target creature. -/
def leftoverEnterFightUpToOne? : CardAction → Bool
  | .fight src dest =>
    (src == .this || src == .source .this) &&
      match dest with
      | .targets _ (.range 0 1) among =>
        among.shape.other && among.shape.types.eqTypes [.creature]
      | _ => false
  | _ => false

/-- You may sacrifice another creature. When you do, destroy target
nonland permanent an opponent controls. -/
def leftoverEnterMaySacAnotherThenDestroyOppNonland? : CardAction → Bool
  | .sequence [
      .optional (.actionId id (.sacrifice (.selected _ (.range 1 1) among))),
      .if (.happened (.actionWithId id') _) [.destroy sel]
    ] =>
    id == id' && among.shape.other && among.shape.sameController &&
      among.shape.types.eqTypes [.creature] &&
      sel.targetingShape.nonland && sel.targetingShape.opponentControls
  | _ => false

/-- +1/+1 on each other creature you control; you gain 1 life for each of
those creatures. -/
def leftoverPlusOneEachOtherGainLife? : CardAction → Bool
  | .sequence [
      .putCounter sel .plusOnePlusOne 1,
      .forEachVariable _ among [.gainLife who 1]
    ]
  | .sequence [
      .forEachVariable _ among [.gainLife who 1],
      .putCounter sel .plusOnePlusOne 1
    ] =>
    leftoverYou who &&
      sel.shape.anotherCreatureYouControl &&
      among.shape.anotherCreatureYouControl
  | _ => false

/-- Target attacking creature gains flying. -/
def leftoverGrantFlyingToAttacking? : CardAction → Bool
  | .continuous effects _ =>
    let kws := grantedKeywords effects
    kws.flying &&
      match ContinuousEffect.targetingSelector? effects with
      | some sel => sel.targetingShape.attackingCreature
      | none => false
  | _ => false

/-- Those creatures (targets of this spell) gain flying. -/
def leftoverGrantFlyingToThose? : List ContinuousEffect → Bool
  | [.gainAbility who (.keyword .flying)] =>
    who.leftoverIsTargetOfThisSpell? &&
      who.shape.mustBePermanent &&
      who.shape.types.eqTypes [.creature]
  | _ => false

/-- This mode has not been chosen this turn by any player. -/
def leftoverModeUnchosenThisTurn? (id : Nat) : Condition → Bool
  | .didNotHappen (.modeWithIdChosen chooser id') .turnStart =>
    chooser == .player && id == id'
  | _ => false

/-- Alliance modes: add {G}{G}{G}; +1/+1 on each creature you control;
scry 2, then draw. Each mode must be unchosen this turn. -/
def leftoverAllianceModes? (who : Selector) :
    List (Nat × Condition × List CardAction) → Bool
  | [
      (id1, c1, [.addMana gainer [.mono .green, .mono .green, .mono .green]]),
      (id2, c2, [.putCounter sel .plusOnePlusOne 1]),
      (id3, c3, [.sequence [.scry _ 2, .draw _ 1]])
    ] =>
    leftoverYou who && leftoverYou gainer &&
      id1 != id2 && id2 != id3 && id1 != id3 &&
      leftoverModeUnchosenThisTurn? id1 c1 &&
      leftoverModeUnchosenThisTurn? id2 c2 &&
      leftoverModeUnchosenThisTurn? id3 c3 &&
      sel.shape.sameController &&
      sel.shape.types.eqTypes [.creature]
  | _ => false

/-- Target creature or land. -/
def leftoverCreatureOrLandTarget? (s : Selector) : Bool :=
  s.targetingShape.types.eqTypes [.creature, .land]

/-- Exile the object of this triggered ability from a graveyard, then you
may play it until the end of your next turn. -/
def leftoverExileGyPlayUntilNextTurn? : CardAction → Bool
  | .optional
      (.sequence [
        .actionId id (.exile among),
        .continuous [.canPlay permit (.wasCreatedByAction created)] duration
      ]) =>
    id == created && leftoverYou permit &&
      among.includesInGraveyard && among.includesWasObjectOfThisTrigger &&
      leftoverUntilEndOfYourNextTurn? duration
  | _ => false

/-- Copy that spell or ability; you may choose new targets. -/
def leftoverCopyWithNewTargets? : CardAction → Bool
  | .copyWithNewTargets who what =>
    leftoverYou who && what.includesWasObjectOfThisTrigger
  | _ => false

/-- Sacrifice an artifact or discard a nonland card. -/
def leftoverSacrificeArtifactOrDiscardNonlandCost? : List Cost → Bool
  | [] => false
  | .or cs :: rest =>
    let sacArt :=
      cs.any fun
        | .sacrificeCount s 1 => s.shape.types.eqTypes [.artifact]
        | .sacrifice s => s.shape.types.eqTypes [.artifact]
        | _ => false
    let discNonland :=
      cs.any fun
        | .discard s => s.shape.nonland
        | _ => false
    (sacArt && discNonland) || leftoverSacrificeArtifactOrDiscardNonlandCost? rest
  | _ :: rest => leftoverSacrificeArtifactOrDiscardNonlandCost? rest

/-- You may sacrifice an artifact or discard a nonland card. If you do,
deal 2 damage to any target. -/
def leftoverEnterMaySacOrDiscardNonlandThenDamage? : CardAction → Bool
  | .optionalPayFor who costs [.dealDamage _ dest (.nat 2)] =>
    leftoverYou who &&
      leftoverSacrificeArtifactOrDiscardNonlandCost? costs &&
      Selector.leftoverAnyTarget? dest
  | _ => false

/-- Other permanents you control of a subtype get +P/+T per matching object. -/
def leftoverOtherSubtypeGetPowerPerArtifactToken?
    (who among : Selector) (vp vt : Value) : Option String :=
  match valToInt? vp, valToInt? vt with
  | some 1, some 0 =>
    if among.shape.token && among.shape.sameController &&
        among.shape.types.eqTypes [.artifact] then
      who.shape.anotherSubtypeYouControl
    else none
  | _, _ => none

/-- You may pay {1}. If you do, target creature with haste can't be
blocked this turn except by creatures with haste. -/
def leftoverMayPayHasteUnblockable? : CardAction → Bool
  | .optionalPayFor who [.mana [.generic 1]] [.continuous effects _] =>
    leftoverYou who &&
      match effects with
      | [.forbid (.block (.not (.keyword .haste)) dest)] =>
        dest.targetingShape.types.eqTypes [.creature]
      | _ => false
  | _ => false

/-- +P/+T on this as long as your graveyard has creature cards. With
`gainAllSubtypes` of creature, also all creature types. -/
def leftoverGetsIfGyCreatureCards?
    (among : Selector) (inners : List ContinuousEffect) : Option StaticAbility :=
  if leftoverYourGyCreatures? among then
    match inners with
    | [.addPowerToughness who vp vt] =>
      match valToInt? vp, valToInt? vt with
      | some p, some t =>
        if leftoverThis who then
          some (.getsIfGyCreatureCards 2 p t)
        else none
      | _, _ => none
    | [.addPowerToughness who vp vt, .gainAllSubtypes typesWho .creature]
    | [.gainAllSubtypes typesWho .creature, .addPowerToughness who vp vt] =>
      match valToInt? vp, valToInt? vt with
      | some p, some t =>
        if leftoverThis who && leftoverThis typesWho then
          some (.getsAndAllTypesIfGyCreatureCards 2 p t)
        else none
      | _, _ => none
    | _ => none
  else none

/-- Target opponent as a numbered target. -/
def leftoverTargetOpponent? : Selector → Bool
  | .target _ (.opponent _) => true
  | _ => false

/-- Target player as a numbered target. -/
def leftoverTargetPlayer? : Selector → Bool
  | .target _ .player => true
  | _ => false

/-- Objects milled by the numbered action that also match `pred`. -/
def leftoverMilledBy (id : Nat) (pred : Selector → Bool) : Selector → Bool
  | .intersection fs =>
    fs.any (fun s => s == .wasObjectOfAction id) && fs.any pred
  | _ => false

/-- Instant or sorcery cards. -/
def leftoverInstantOrSorceryFilter : Selector → Bool
  | s => s.shape.types.eqTypes [.instant, .sorcery]

/-- Land cards. -/
def leftoverLandFilter : Selector → Bool
  | s => s == .cardType .land || s.shape.types.eqTypes [.land]

/-- A permanent card (among milled cards). -/
def leftoverPermanentCardFilter : Selector → Bool
  | .permanent => true
  | _ => false

/-- A subtype card or an enchantment card. -/
def leftoverSubtypeOrEnchantment? : Selector → Option String
  | .union fs =>
    if fs.any (fun s => s == .cardType .enchantment) then
      fs.findSome? fun s =>
        match s with
        | .subtype st => some st.toString
        | _ => none
    else none
  | _ => none

/-- The printed subtype among milled cards, if that is the only filter. -/
def leftoverMilledSubtype? (id : Nat) : Selector → Option String
  | .intersection fs =>
    if fs.any (fun s => s == .wasObjectOfAction id) then
      fs.findSome? fun s =>
        match s with
        | .subtype st => some st.toString
        | _ => none
    else none
  | _ => none

/-- Chosen cards from among those milled by `id`. -/
def leftoverSelectedMilled? (id : Nat) (pred : Selector → Bool) :
    Selector → Option (Nat × Nat)
  | .selected _ (.range (.nat lo) (.nat hi)) among =>
    if leftoverMilledBy id pred among then some (lo, hi) else none
  | .targets _ (.range (.nat lo) (.nat hi)) among =>
    if leftoverMilledBy id pred among then some (lo, hi) else none
  | _ => none

/-- Mill n, then put an instant or sorcery card from among them into hand. -/
def leftoverMillThenPutInstantOrSorcery? : CardAction → Option Nat
  | .sequence [.actionId id (.mill who (.nat n)), .returnToHand sel] =>
    match leftoverSelectedMilled? id leftoverInstantOrSorceryFilter sel with
    | some (lo, 1) =>
      if leftoverYou who && lo ≤ 1 then some n else none
    | _ => none
  | _ => none

/-- Mill n, then put up to `max` land cards from among them into hand. -/
def leftoverMillThenPutLands? : CardAction → Option (Nat × Nat)
  | .sequence [.actionId id (.mill who (.nat n)), .returnToHand sel] =>
    match leftoverSelectedMilled? id leftoverLandFilter sel with
    | some (0, max) =>
      if leftoverYou who then some (n, max) else none
    | _ => none
  | _ => none

/-- Mill n, then put all instant and sorcery cards from among them into hand. -/
def leftoverMillThenPutAllInstantsOrSorceries? : CardAction → Option Nat
  | .sequence [.actionId id (.mill who (.nat n)), .returnToHand among] =>
    if leftoverYou who && leftoverMilledBy id leftoverInstantOrSorceryFilter among then
      some n
    else none
  | _ => none

/-- Mill n, you may put a permanent card from among them into hand, gain life. -/
def leftoverMillThenPutPermanentGainLife? : CardAction → Option (Nat × Nat)
  | .sequence [
      .actionId id (.mill who (.nat n)),
      .optional (.returnToHand sel),
      .gainLife gainer (.nat life)
    ] =>
    match leftoverSelectedMilled? id leftoverPermanentCardFilter sel with
    | some (lo, 1) =>
      if leftoverYou who && leftoverYou gainer && lo ≤ 1 then some (n, life) else none
    | _ => none
  | _ => none

/-- Mill n, you may put a subtype or enchantment card from among them into hand. -/
def leftoverMillThenPutSubtypeOrEnchantment? : CardAction → Option (Nat × String)
  | .sequence [
      .actionId id (.mill who (.nat n)),
      .optional (.returnToHand (.selected _ (.range (.nat lo) 1) among))
    ] =>
    if leftoverYou who && lo ≤ 1 then
      match among with
      | .intersection fs =>
        if fs.any (fun s => s == .wasObjectOfAction id) then
          fs.findSome? leftoverSubtypeOrEnchantment? |>.map (fun st => (n, st))
        else none
      | _ => none
    else none
  | .sequence [
      .actionId id (.mill who (.nat n)),
      .optional (.returnToHand (.targets _ (.range (.nat lo) 1) among))
    ] =>
    if leftoverYou who && lo ≤ 1 then
      match among with
      | .intersection fs =>
        if fs.any (fun s => s == .wasObjectOfAction id) then
          fs.findSome? leftoverSubtypeOrEnchantment? |>.map (fun st => (n, st))
        else none
      | _ => none
    else none
  | _ => none

/-- Mill-then-put sequences that compile to a named `Effect`. -/
def leftoverMillThenPutCompiled? (action : CardAction) : Option Effect :=
  match leftoverMillThenPutPermanentGainLife? action with
  | some (n, life) => some (Effect.millThenPutPermanentGainLife n life)
  | none =>
    match leftoverMillThenPutSubtypeOrEnchantment? action with
    | some (n, st) => some (Effect.millThenPutSubtypeOrEnchantment n st)
    | none =>
      match leftoverMillThenPutLands? action with
      | some (n, max) => some (Effect.millThenPutLands n max)
      | none =>
        match leftoverMillThenPutInstantOrSorcery? action with
        | some n => some (Effect.millThenPutInstantOrSorcery n)
        | none =>
          leftoverMillThenPutAllInstantsOrSorceries? action |>.map
            Effect.millThenPutAllInstantsOrSorceries

/-- Mill n, then put all cards of a subtype from among them into hand. -/
def leftoverMillThenSubtypeToHand? : CardAction → Option (Nat × String)
  | .sequence [.actionId id (.mill who (.nat n)), .returnToHand among] =>
    if leftoverYou who then
      leftoverMilledSubtype? id among |>.map (fun st => (n, st))
    else none
  | _ => none

/-- Combat-damage destination is a player, or a player or battle. -/
def leftoverPlayerOrBattle : Selector → Bool
  | .player => true
  | .union fs =>
    fs.any (fun s => s == .player) &&
      fs.any (fun s => s == .cardType .battle)
  | _ => false

/-- Another nontoken Hero you control enters: create a Soldier or team pump. -/
def leftoverNontokenHeroModal? (among : Selector) : List CardAction → Bool
  | [a, b] =>
    let soldier (x : CardAction) : Bool :=
      leftoverCreateTokensKindN? x == some (.soldier11white, 1)
    let pump (x : CardAction) : Bool :=
      match x with
      | .continuous effects _ =>
        ContinuousEffect.addedPT? effects == some (1, 1) &&
          match ContinuousEffect.massSelector? effects with
          | some s => s.shape.sameController && s.shape.types.eqTypes [.creature]
          | none => false
      | _ => false
    among.shape.other && among.shape.nontoken && among.shape.sameController &&
      among.shape.subtype == some "Hero" &&
      ((soldier a && pump b) || (soldier b && pump a))
  | _ => false

/-- Lose 1 life and create a Treasure (second spell each turn). -/
def leftoverLoseLifeCreateTreasure? : CardAction → Bool
  | .sequence [.loseLife who 1, .createTokens c 1 parts []] =>
    leftoverYou who && leftoverYou c && leftoverTokenKind? parts == some .treasure
  | .sequence [.createTokens c 1 parts [], .loseLife who 1] =>
    leftoverYou who && leftoverYou c && leftoverTokenKind? parts == some .treasure
  | _ => false

/-- You may draw a card for each artifact you control. If you do, each
opponent draws a card. -/
def leftoverMayDrawPerArtifactOppsDraw? : CardAction → Bool
  | .optional
      (.sequence [
        .forEachVariable _ among [.draw who 1],
        .draw dest 1
      ]) =>
    leftoverYou who && among.shape.artifactYouControl && leftoverOpponents dest
  | _ => false

/-- Artifact spells you cast. -/
def leftoverArtifactSpellsYouCast? : Selector → Bool
  | s => s.shape.isSpell && s.shape.types.eqTypes [.artifact] && s.shape.sameController

/-- Artifact spells you cast this turn cost that much less. -/
def leftoverArtifactSpellsCostLessThisTurn? : CardAction → Option Nat
  | .continuous [.reduceCost who costs] .endOfTurn =>
    let n := ManaCost.manaValue (Cost.manaCost costs)
    if n != 0 && leftoverArtifactSpellsYouCast? who then some n else none
  | _ => none

/-- This deals X damage to target opponent, where X is the greatest mana
value among artifacts you control. -/
def leftoverChapterDealXDamageToTargetOpponentGreatestArtifactMv? :
    CardAction → Bool
  | .dealDamage src dest (.greatestManaValue among) =>
    leftoverThis src && leftoverTargetOpponent? dest && among.shape.artifactYouControl
  | _ => false

/-- Saga-chapter leftovers that compile to a named `Effect`. -/
def leftoverChapterCompiled? (action : CardAction) : Option Effect :=
  if leftoverMayDrawPerArtifactOppsDraw? action then
    some Effect.mayDrawPerArtifactOppsDraw
  else
    match leftoverArtifactSpellsCostLessThisTurn? action with
    | some n => some (Effect.artifactSpellsCostLessThisTurn n)
    | none =>
      if leftoverChapterDealXDamageToTargetOpponentGreatestArtifactMv? action then
        some Effect.chapterDealXDamageToTargetOpponentGreatestArtifactMv
      else none

/-- Compile printed Saga-chapter actions. -/
def leftoverChapterEffect? (actions : List CardAction) : Option Effect :=
  leftoverChapterCompiled?
    (match actions with
      | [a] => a
      | as => .sequence as)

/-- Continuous leftovers that compile to a named `Effect`. -/
def leftoverContinuousCompiled? : CardAction → Option Effect
  | .continuous effects _ =>
    if leftoverGrantCombatDamageCreateTreasure? effects then
      some Effect.grantCombatDamageCreateTreasure
    else
      match leftoverSubtypesGainMenace? effects with
      | some sts => some (Effect.subtypesGainMenace sts)
      | none => leftoverTeamGain? effects |>.map Effect.teamGain
  | _ => none

/-- Sequence leftovers that compile to a named `Effect` without taking
only the first action. -/
def leftoverCompiled? (action : CardAction) : Option Effect :=
  leftoverChapterCompiled? action |>.orElse fun _ =>
  if leftoverOwnerPutsLibraryThenConnive? action then
    some Effect.ownerPutsLibraryThenConnive
  else
  (leftoverMillThenPutCompiled? action).orElse fun _ =>
  (leftoverCreateThenTeamPump? action).orElse fun _ =>
  (leftoverContinuousCompiled? action).orElse fun _ =>
  match leftoverDrawLoseLifeThenAmass? action with
  | some n => some (Effect.drawLoseLifeThenAmass n)
  | none =>
    match leftoverReturnCreatureFromGyThenAmass? action with
    | some n => some (Effect.returnCreatureFromGyThenAmass n)
    | none =>
      match leftoverTapScryDraw? action with
      | some (scryN, drawN) => some (Effect.tapScryDraw scryN drawN)
      | none =>
        if leftoverReturnSpellDraw? action then some Effect.returnSpellDraw
        else if leftoverDestroyArtOrLandNonflyers? action then
          some Effect.destroyArtifactOrLandNonflyersCantBlock
        else if leftoverDestroyCreatureSurveil? action then
          some Effect.destroyCreatureSurveil
        else if leftoverBecomeArtifactIndestructible? action then
          some Effect.becomeArtifactGainIndestructible
        else if leftoverPlusOneLifelinkIndestructible? action then
          some Effect.plusOneLifelinkIndestructible
        else if leftoverGrantVigilanceUnblockable? action then
          some Effect.grantVigilanceUnblockable
        else
          match leftoverPumpThenExileTopPlay? action with
          | some (p, t) => some (Effect.pumpThenExileTopPlay p t)
          | none =>
            match leftoverDestroyArtEnchGainLife? action with
            | some n => some (Effect.destroyArtifactOrEnchantmentGainLife n)
            | none =>
              match leftoverMaySacArtifactOrDiscardDraw? action with
              | some n => some (Effect.maySacArtifactOrDiscardDraw n)
              | none =>
                match leftoverDrawThreeDiscardUnlessArtifact? action with
                | some _ => some Effect.drawThreeDiscardUnlessArtifact
                | none =>
                  match leftoverReturnUpToTwoGyModal? action with
                  | some _ => some Effect.returnUpToTwoGyModal
                  | none =>
                    match leftoverGainLifeSearchBasicPlusOne? action with
                    | some n => some (Effect.gainLifeSearchBasicPlusOne n)
                    | none =>
                      leftoverPlusOneOnEachOtherSubtype? action

/-- Enters-the-battlefield actions that compile to a named trigger. -/
def leftoverEnterThisAction? : CardAction → Option TriggeredAbility
  | .createTokens who n parts states =>
    match valToNat? n with
    | some n =>
      if leftoverYou who then
        if states == [] then
          if n == 1 && leftoverRedwingToken? parts then
            some (TriggeredAbility.onEnter Effect.enterCreateRedwing)
          else
            leftoverTokenKind? parts |>.map (fun k => TriggeredAbility.onEnterCreateTokens k n)
        else if leftoverTappedOnly states then
          leftoverTokenKind? parts |>.map (fun k => TriggeredAbility.onEnterCreateTokens k n true)
        else none
      else none
    | none => none
  | .sequence [
      .actionId id (.createTokens who n parts []),
      .attach .this (.wasCreatedByAction id')
    ] =>
    if id == id' && n == 1 && leftoverYou who then
      leftoverTokenKind? parts |>.map TriggeredAbility.onEnterCreateThenAttach
    else none
  | .playerSelectAction who (.range 1 1) actions =>
    if leftoverYou who && leftoverCreateFoodOrTreasure? actions then
      some TriggeredAbility.onEnterCreateFoodOrTreasure
    else none
  | .keyword who .recruit =>
    if leftoverYou who then some TriggeredAbility.onEnterRecruit else none
  | .keyword who (.amass .goblin (.nat n)) =>
    if leftoverYou who then some (TriggeredAbility.onEnterAmassGoblins n) else none
  | .keyword who (.connive (.nat 1)) =>
    if leftoverSourceThis who then some TriggeredAbility.onEnterConnive else none
  | .sequence [
      .actionId id (.returnToHand sel),
      .if (.happened (.actionWithId id') _)
        [.putCounter (.source .this) .plusOnePlusOne 1]
    ] =>
    if id == id' then
      match sel with
      | .targets _ (.range 0 1) among =>
        if among.shape.other && among.shape.sameController then
          some TriggeredAbility.onEnterReturnOtherPlusOne
        else none
      | _ => none
    else none
  | .sequence [
      .gainLife _ (.nat n),
      .optional search
    ] =>
    if leftoverSearchBasicOnTop? search then
      some (TriggeredAbility.onEnterGainLifeSearchBasicOnTop n)
    else none
  | .sequence [
      .draw (.controller .this) 1,
      .if (.any among) [.gainLife _ 2]
    ] =>
    if among.shape.other && among.shape.sameController &&
        among.shape.subtype == some "Hero" then
      some TriggeredAbility.onEnterDrawGainLifeIfAnotherHero
    else none
  | .sequence [
      .putCounter sel .plusOnePlusOne 1,
      .if (.anySubtype among .hero)
        [.putCounter _ .plusOnePlusOne 1]
    ] =>
    -- “If that creature is another Hero”: the extra counter is about the
    -- chosen target, and must not fire when that target is the source.
    if (sel.toTargetKind == .creature || sel.toTargetKind == .creatureYouControl) &&
        among.shape.other && among.includesTargetReference then
      some TriggeredAbility.onEnterPlusOneOrTwoIfAnotherHero
    else none
  | .sequence [
      .actionId id (.keyword who (.amass .goblin (.nat n))),
      .attach .this (.wasObjectOfAction id')
    ] =>
    if id == id' && leftoverYou who then
      some (TriggeredAbility.onEnterAmassThenAttach n)
    else none
  | action =>
    match leftoverMillThenSubtypeToHand? action with
    | some (n, st) => some (TriggeredAbility.onEnterMillThenSubtypeToHand n st)
    | none =>
      if leftoverMaySacDrawTreasure? action then
        some TriggeredAbility.onEnterMaySacDrawTreasure
      else if leftoverEnterReturnGyPermanentThisTurn? action then
        some (TriggeredAbility.onEnter Effect.enterReturnGyPermanentThisTurn)
      else if leftoverEnterReturnCreatureFromGyToHand? action then
        some TriggeredAbility.onEnterReturnCreatureFromGyToHand
      else if leftoverEnterReturnNonlandNontoken? action then
        some (TriggeredAbility.onEnter Effect.enterReturnNonlandNontoken)
      else if leftoverEnterFightUpToOne? action then
        some (TriggeredAbility.onEnter Effect.enterFightUpToOne)
      else if leftoverEnterMaySacAnotherThenDestroyOppNonland? action then
        some (TriggeredAbility.onEnter Effect.enterMaySacAnotherThenDestroyOppNonland)
      else if leftoverEnterMaySacOrDiscardNonlandThenDamage? action then
        some (TriggeredAbility.onEnter Effect.enterMaySacOrDiscardNonlandThenDamage)
      else none

/-- Enters-the-battlefield library searches. -/
def leftoverEnterSearch? : List CardAction → Option TriggeredAbility
  | [.putOntoBattlefield sel] =>
    match sel.selectedAmong? with
    | some among =>
      if among.includesInLibrary && among.includedSubtype? == some "Forest" then
        some TriggeredAbility.onEnterSearchForest
      else none
    | none => none
  | [.defineVariable id sel, .reveal (.variable id'), .returnToHand (.variable id'')] =>
    if id == id' && id == id'' then
      match sel.selectedAmong? with
      | some among =>
        if among.basicLandInLibrary then
          some TriggeredAbility.onEnterSearchBasicToHand
        else none
      | none => none
    else none
  | _ => none

/-- Compile `continuous` effects, reading targeting from `target`
and mass application from constraint selectors. -/
def compile (action : CardAction) (asAbility : Bool) : Effect :=
  match leftoverCompiled? action with
  | some e => e
  | none =>
  match leftoverSearchLibraryThenShuffle? action with
  | some e => e
  | none =>
  match leftoverPlusOneOnTarget? action with
  | some e => e
  | none =>
  match leftoverUntapPumpAttach? action with
  | some (p, t) => Effect.untapPumpMaybeAttach p t
  | none =>
    if leftoverCreatureYouControlDealsPowerToOppCreature? action then
      Effect.creatureYouControlDealsPowerToOppCreature
    else if leftoverPlusOnePlusOneTrampleHexproof? action then
      Effect.plusOnePlusOneTrampleHexproof
    else
    match leftoverBecomeSubtypeWithLandsPT? action with
    | some subtype => Effect.becomeSubtypeWithLandsPT subtype
    | none =>
    if leftoverCounterExile? action then Effect.counterExilePermanentMayCast
    else if leftoverExileTopPlayUntilEndOfNextTurn? action then
      Effect.exileTopPlayUntilEndOfNextTurn
    else if leftoverEquipAttach? action then Effect.attachToTargetCreatureYouControl
    else
      match leftoverDrawDiscard? action with
      | some n =>
        if asAbility then Effect.abilityDrawThenDiscard n
        else Effect.drawThenDiscard n
      | none =>
        match leftoverPlusOneAndGainLife? action with
        | some n => Effect.plusOneUpToOneAndPlayerGainsLife n
        | none =>
          match leftoverPumpAndExileIfDies? action with
          | some (p, t) => Effect.pumpAndExileIfDies p t
          | none =>
            match leftoverPumpAndLifelink? action with
            | some (p, t) => Effect.pumpAndLifelink p t
            | none =>
              match leftoverPumpAndGrantKeywords? action with
              | some (p, t, k) =>
                if asAbility then
                  match action with
                  | .continuous effects _ =>
                    match ContinuousEffect.targetingSelector? effects with
                    | some sel =>
                      if sel.targetingShape.anotherCreatureYouControl then
                        Effect.anotherYouControlGetsAndGrant p t k
                      else Effect.pumpAndGrantKeywords p t k
                    | none => Effect.pumpAndGrantKeywords p t k
                  | _ => Effect.pumpAndGrantKeywords p t k
                else Effect.pumpAndGrantKeywords p t k
              | none =>
              match leftoverPumpThenDraw? action with
              | some (p, t) => Effect.pumpThenDraw p t
              | none =>
              match leftoverCreaturesTargetPlayerGet? action with
              | some (p, t) => Effect.creaturesTargetPlayerGet p t
              | none =>
              match leftoverAllCreaturesGet? action with
              | some (p, t) => Effect.allCreaturesGet p t
              | none =>
              if leftoverTargetCantBeBlocked? action then
                Effect.targetCantBeBlockedThisTurn
              else
                match leftoverDrawLoseLifeSelf? action with
                | some (cards, life) => Effect.drawAndLoseLife cards life
                | none =>
                match leftoverTargetPlayerDrawLoseLife? action with
                | some (cards, life) => Effect.targetPlayerDrawLoseLife cards life
                | none =>
                  match action with
                  | .continuous effects _duration => compileContinuous effects asAbility
                  | .tap s => compileTap s asAbility
                  | .untap s => compileUntap s asAbility
                  | .dealDamage _source victim (.nat n) => compileDamage victim n asAbility
                  | .dealDamage _source victim (.int n) =>
                    if n >= 0 then compileDamage victim n.toNat asAbility
                    else continuousEffect none [] asAbility
                  | .dealDamage _ _ _ =>
                    continuousEffect none [] asAbility
                  | .divideDamage _who _source victim n =>
                    match valToNat? n with
                    | some n => compileDamage victim n asAbility
                    | none => continuousEffect none [] asAbility
                  | .draw _who n =>
                    match valToNat? n with
                    | some n =>
                      if asAbility then Effect.abilityDraw n else Effect.draw n
                    | none => continuousEffect none [] asAbility
                  | .scry _who n =>
                    match valToNat? n with
                    | some n => Effect.scry n
                    | none => continuousEffect none [] asAbility
                  | .sequence (a :: _) => compile a asAbility
                  | .sequence [] => continuousEffect none [] asAbility
                  | .if _ (a :: _) => compile a asAbility
                  | .if _ [] => continuousEffect none [] asAbility
                  | .ifElse _ (a :: _) _ => compile a asAbility
                  | .ifElse _ [] (a :: _) => compile a asAbility
                  | .ifElse _ [] [] => continuousEffect none [] asAbility
                  | .optional inner => compile inner asAbility
                  | .attach _ _ => Effect.untapPumpMaybeAttach 0 0
                  | .chooseMode (a :: _) => compile a asAbility
                  | .chooseMode [] => continuousEffect none [] asAbility
                  | .chooseModeRestricted _ ((_, _, a :: _) :: _) =>
                    compile a asAbility
                  | .chooseModeRestricted _ _ =>
                    continuousEffect none [] asAbility
                  | .counter _ => Effect.counterSpell
                  | .preventable _ costs (.counter _) =>
                    Effect.counterUnlessPays (ManaCost.manaValue (Cost.manaCost costs))
                  | .preventable _ _ inner => compile inner asAbility
                  | .optionalPayFor _ _ (a :: _) => compile a asAbility
                  | .optionalPayFor _ _ [] => continuousEffect none [] asAbility
                  | .discard _ n =>
                    match valToNat? n with
                    | some n => Effect.drawThenDiscard n
                    | none => continuousEffect none [] asAbility
                  | .putCounter (.source .this) .plusOnePlusOne n =>
                    Effect.putPlusOnePlusOneOnSource n
                  | .putCounter _ _ _ => continuousEffect none [] asAbility
                  | .exile _ => continuousEffect none [] asAbility
                  | .exchangeControl _ => Effect.exchangeControlSharingType
                  | .destroy s =>
                    if s.toTargetKind == .creatureWithFlying then
                      Effect.destroyCreatureWithFlying
                    else if asAbility && s.toTargetKind == .noncreatureArtifactOrEnchantment then
                      Effect.destroyTargetNoncreatureArtOrEnch
                    else if asAbility && s.toTargetKind == .artifactOrEnchantment then
                      Effect.destroyTargetArtifactOrEnchantment
                    else if asAbility && s.toTargetKind == .permanent then
                      Effect.destroyTargetPermanent
                    else
                      match s.toTargetKind with
                      | .creaturePowerAtLeast n => Effect.destroyCreaturePowerAtLeast n
                      | _ => Effect.destroyCreature
                  | .gainLife _ n =>
                    match valToNat? n with
                    | some n => Effect.gainLife n
                    | none => continuousEffect none [] asAbility
                  | .playerSelectAction _ _ actions =>
                    match actions with
                    | [.putOnTopOfLibrary _, .putOnBottomOfLibrary _] =>
                      Effect.putOnTopOrBottom
                    | a :: _ => compile a asAbility
                    | [] => continuousEffect none [] asAbility
                  | .putOnTopOfLibrary _ => Effect.putOnTopOrBottom
                  | .putOnBottomOfLibrary _ => Effect.putOnTopOrBottom
                  | .putIntoLibraryFromTop _ 1 => Effect.putOnTopOrBottom
                  | .putIntoLibraryFromTop _ _ =>
                    continuousEffect none [] asAbility
                  | .actionId _ inner => compile inner asAbility
                  | .loseLife _ _ => continuousEffect none [] asAbility
                  | .sacrifice _ => continuousEffect none [] asAbility
                  | .returnToHand _ => Effect.returnFromGraveyardToHand
                  | .putOntoBattlefield _ => continuousEffect none [] asAbility
                  | .putOntoBattlefieldInState _ _ => continuousEffect none [] asAbility
                  | .searchLibraryThenShuffle _ _ =>
                    continuousEffect none [] asAbility
                  | .holdOutInLibrary _ => continuousEffect none [] asAbility
                  | .defineVariable _ _ => continuousEffect none [] asAbility
                  | .forEachVariable _ _ _ => continuousEffect none [] asAbility
                  | .reveal _ => continuousEffect none [] asAbility
                  | .dealDamageEqualToPower _ _ | .fight _ _ =>
                    continuousEffect none [] asAbility
                  | .addManaAnyColor chooser gainer n =>
                    if leftoverAddAnyColor? (.addManaAnyColor chooser gainer n) then
                      Effect.addAnyColor
                    else
                      continuousEffect none [] asAbility
                  | .addManaAnyColorEqualToPower _ _ _ =>
                    continuousEffect none [] asAbility
                  | .addMana _ syms =>
                    match addedManaTypes? syms with
                    | some types => Effect.addMana types
                    | none => continuousEffect none [] asAbility
                  | .keyword who k =>
                    match leftoverKeywordAction? k with
                    | some e =>
                      match k with
                      | .connive (.nat 1) =>
                        let ok :=
                          if asAbility then leftoverSourceThis who else leftoverThis who
                        if ok then e else continuousEffect none [] asAbility
                      | _ => e
                    | none => continuousEffect none [] asAbility
                  | .createTokens _ n parts states =>
                    match leftoverTokenKind? parts, valToNat? n with
                    | some kind, some n =>
                      if states == [] then
                        if asAbility then Effect.abilityCreateTokens kind n
                        else Effect.createTokens kind n
                      else if leftoverTappedOnly states then
                        Effect.createTappedTokens kind n
                      else continuousEffect none [] asAbility
                    | _, _ => continuousEffect none [] asAbility
                  | .mill who n =>
                    match valToNat? n with
                    | some n =>
                      if leftoverTargetPlayer? who then Effect.millPlayer n
                      else continuousEffect none [] asAbility
                    | none => continuousEffect none [] asAbility
                  | .surveil who n =>
                    match valToNat? n with
                    | some n =>
                      if leftoverYou who then Effect.scry n
                      else continuousEffect none [] asAbility
                    | none => continuousEffect none [] asAbility
                  | .copyWithNewTargets _ _ =>
                    continuousEffect none [] asAbility
                  | .keepReplacedAction | .healAllDamage _ =>
                    continuousEffect none [] asAbility

/-- Modes of a “Choose one” action. -/
def leftoverModes? : CardAction → Option (Array Effect)
  | .chooseMode as =>
    some ((as.map fun a => compile a false).toArray)
  | .chooseModeRestricted _ modes =>
    some ((modes.map fun (_, _, as) => compile (.sequence as) false).toArray)
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
  let cyclingBasic :=
    Cost.discardsThis costs &&
      CardAction.leftoverSearchLibraryThenShuffle? action ==
        some Effect.searchBasicLandToHand
  { cost :=
      { mana := Cost.manaCost costs
        payLife := Cost.lifePaid costs
        tap := Cost.hasTapSymbol costs
        sacrificeSource := Cost.sacrificesThis costs
        sacrificeAnotherCreatureOrArtifact := Cost.sacrificesArtifactOrCreature costs
        discardSource := Cost.discardsThis costs
        sacrificeAnotherSubtype := Cost.sacrificeAnotherSubtype? costs
        sacrificeArtifactOrDiscardNonland :=
          CardAction.leftoverSacrificeArtifactOrDiscardNonlandCost? costs }
    effect :=
      if cyclingBasic then Effect.searchLandTypeToHand "Basic land"
      else action.toAbilityEffect
    onceEachTurn
    activateFromHand := Cost.discardsThis costs }

def toActivatedAbility? : Ability → Option ActivatedAbility
  | .keywordWithCost .equip costs =>
    some {
      cost := { mana := Cost.manaCost costs }
      effect := Effect.attachToTargetCreatureYouControl
      onlyAsSorcery := true }
  | .keywordWithSubtypeAndCost .equip st cost =>
    some {
      cost := { mana := Cost.manaCost [cost] }
      effect := Effect.attachToTargetCreatureYouControl
      onlyAsSorcery := true
      equipSubtype := some st.toString }
  | .keywordWithCost (.typecycling supertypes types subtypes) costs =>
    some {
      cost := { mana := Cost.manaCost costs, discardSource := true }
      effect := Effect.searchLandTypeToHand (Keyword.typecyclingPhrase supertypes types subtypes)
      activateFromHand := true }
  | .activatedIf (.countAtLeast among n) costs action =>
    if CardAction.leftoverYourGyCreatures? among && n == 2 then
      some { activatedAbility costs action with onlyIfGyCreaturesAtLeast := 2 }
    else none
  | .activated costs action => some (activatedAbility costs action)
  | .activatedIf (.didNotHappen (.abilityWithIdActivated _) .turnStart) costs action =>
    some (activatedAbility costs action true)
  | .activatedIf (.timeToCastSorcery _) costs
      action@(.returnToHand (.intersection [.inGraveyard, .source .this])) =>
    some { activatedAbility costs action with
      onlyAsSorcery := true
      activateFromGraveyard := true }
  | .activatedIf (.timeToCastSorcery _) costs action =>
    some { activatedAbility costs action with
      onlyAsSorcery := true
      equipSubtype := CardAction.leftoverEquipSubtype? action }
  | .activatedIf
      (.and (.turn _) (.didNotHappen (.abilityWithIdActivated _) .turnStart))
      costs action =>
    some { activatedAbility costs action true with onlyDuringYourTurn := true }
  | .activatedIf (.turn _) costs action =>
    some { activatedAbility costs action with onlyDuringYourTurn := true }
  | .abilityId _ inner => toActivatedAbility? inner
  | _ => none

/-- Keyword actions on a trigger compile to a named `TriggeredAbility`. -/
def leftoverKeywordTriggered? (w : Trigger) (who : Selector) (k : Keyword) :
    Option TriggeredAbility :=
  match k with
  | .connive (.nat 1) =>
    match w with
    | .enter .this =>
      if CardAction.leftoverSourceThis who then some TriggeredAbility.onEnterConnive
      else none
    | .attack .this .all =>
      if CardAction.leftoverSourceThis who then some TriggeredAbility.onAttackConnive
      else none
    | .combatStart p =>
      if CardAction.leftoverYou p &&
          CardAction.leftoverCreatureYouControlTarget? who then
        some TriggeredAbility.onCombatTargetYouControlConnives
      else none
    | .attack among .all =>
      if CardAction.leftoverEquippedCreatureYouControl among &&
          CardAction.leftoverEquippedCreatureYouControl who then
        some TriggeredAbility.onEquippedCreatureYouControlAttacksConnive
      else none
    | _ => none
  | _ =>
    if !CardAction.leftoverYou who then none
    else
      match w, k with
      | .enter .this, .recruit => some TriggeredAbility.onEnterRecruit
      | .die .this, .recruit => some TriggeredAbility.onDiesRecruit
      | .enter .this, .amass .goblin (.nat n) => some (TriggeredAbility.onEnterAmassGoblins n)
      | .die .this, .amass .goblin (.nat n) => some (TriggeredAbility.onDiesAmassGoblins n)
      | .or (.enter .this) (.attack .this .all), .recruit =>
        some TriggeredAbility.onEnterOrAttackRecruit
      | .or (.enter .this) (.attack .this .all), .amass .goblin (.nat n) =>
        some (TriggeredAbility.onEnterOrAttackAmassGoblins n)
      | .attackSimultaneously among dest _, .amass .goblin (.nat n) =>
        if dest == .all && among.shape.sameController then
          some (TriggeredAbility.onYouAttackAmassGoblins n)
        else none
      | .castSpell among, .amass .goblin (.nat n) =>
        if Selector.youCastNoncreatureSpell among then
          some (TriggeredAbility.onCastNoncreatureAmassGoblins n)
        else none
      | .ordinal 1 .turnStart (.castSpell among), .recruit =>
        if Selector.opponentCastsNoncreatureSpell among then
          some TriggeredAbility.onOpponentCastsFirstNoncreatureRecruit
        else none
      | .leaveGraveyard among, .amass .goblin (.nat n) =>
        if CardAction.leftoverYourGyCreatures? among then
          some (TriggeredAbility.onCreatureCardLeavesYourGyAmassGoblins n)
        else none
      | _, _ => none

/-- Compile a `.triggered` ability. -/
def toTriggeredAbility? : Ability → Option TriggeredAbility
  | .triggered (.attack .this .all) (.continuous effects _duration) =>
    if CardAction.leftoverSetOtherBasePT? effects then
      some TriggeredAbility.onAttackSetOtherBasePT
    else
      match CardAction.leftoverPumpAndGrantKeywords? (.continuous effects .endOfTurn) with
      | some (2, 0, kws) =>
        match ContinuousEffect.targetingSelector? effects with
        | some sel =>
          if kws.trample && sel.targetingShape.anotherCreatureYouControl then
            some TriggeredAbility.onAttackOtherGets2AndTrample
          else none
        | none => none
      | _ =>
        match ContinuousEffect.addedPT? effects with
        | some (1, 1) => some TriggeredAbility.onAttackPumpForEachOtherCreature
        | _ =>
          let kws := CardAction.grantedKeywords effects
          match ContinuousEffect.targetingSelector? effects with
          | some sel =>
            if kws != Keywords.none && sel.targetingShape.attackingCreature then
              some (TriggeredAbility.onAttackTargetGainsKeywords kws)
            else none
          | none => none
  | .triggered (.attack .this .all) (.if (.any among) [.gainLife _ (.nat n)]) =>
    if among.shape.ferocious then
      some (TriggeredAbility.onAttackFerociousGainLife n)
    else none
  | .triggered (.attack .this .all) (.if (.any among) [.continuous effects _]) =>
    if among.shape.ferocious then
      match CardAction.leftoverSourceGetsAndTeamTrample? effects with
      | some p => some (TriggeredAbility.onAttackFerociousSourceGetsAndTeamTrample p)
      | none =>
        match CardAction.leftoverSourcePump? effects with
        | some (p, t) => some (TriggeredAbility.onAttackFerociousSourceGets p t)
        | none => none
    else none
  | .triggered (.attack .this .all) (.if (.any among) [.putCounter sel .plusOnePlusOne 1]) =>
    if among.shape.ferocious &&
        sel.shape.sameController && sel.shape.types.eqTypes [.creature] then
      some TriggeredAbility.onAttackFerociousPlusOneEach
    else none
  | .triggered (.attack .this .all) (.scry _ (.nat n)) =>
    some (TriggeredAbility.onAttackScry n)
  | .triggered (.attack .this .all) (.surveil who (.nat n)) =>
    if CardAction.leftoverYou who then
      some (TriggeredAbility.onAttackScry n)
    else none
  | .triggered (.block _ src) (.dealDamage dealer dest (.nat 1)) =>
    if src == .this && dealer == .this && dest == .blocking .this then
      some TriggeredAbility.onBecomesBlockedDeal1ToBlockers
    else none
  | .triggered (.castSpell among) (.dealDamage _ (.opponent _) (.nat n)) =>
    if among.shape.types.eqTypes [.instant, .sorcery] && among.shape.sameController then
      some (TriggeredAbility.onCastInstantOrSorceryDealDamageToEachOpponent n)
    else none
  | .triggered (.castSpell among) (.putCounter sel .plusOnePlusOne 1) =>
    if Selector.youCastNoncreatureSpell among &&
        sel.shape.other && sel.shape.sameController &&
        sel.shape.types.eqTypes [.creature] then
      some (TriggeredAbility.onCasting Effect.castingPlusOneEachOther)
    else none
  | .triggered (.castSpell among)
      (.if (.targetsIncludeAny _ creatureSel)
        [.putCounter (.source .this) .plusOnePlusOne 1]) =>
    if among.shape.sameController && Selector.includesSpell among &&
        creatureSel.shape.sameController &&
        creatureSel.shape.types.eqTypes [.creature] then
      some (TriggeredAbility.onCasting Effect.castingPlusOneThis)
    else none
  | .triggered (.enter .this) (.draw (.controller .this) (.nat n)) =>
    some (TriggeredAbility.onEnterDraw n)
  | .triggered (.enter .this) (.scry _ (.nat n)) =>
    some (TriggeredAbility.onEnterScry n)
  | .triggered (.enter .this) (.surveil who (.nat n)) =>
    if CardAction.leftoverYou who then
      some (TriggeredAbility.onEnterSurveil n)
    else none
  | .triggered (.enter .this) (.gainLife _ (.nat n)) =>
    some (TriggeredAbility.onEnterGainLife n)
  | .triggered (.enter .this)
      (.sequence [
        .actionId id (.exile (.topOfLibrary who)),
        .continuous [.canPlay permit (.wasCreatedByAction created)] duration
      ]) =>
    if CardAction.leftoverExileTopPlayUntilEndOfNextTurn?
        (.sequence [
          .actionId id (.exile (.topOfLibrary who)),
          .continuous [.canPlay permit (.wasCreatedByAction created)] duration
        ]) then
      some TriggeredAbility.onEnterExileTop
    else none
  | .triggered (.enter .this) (.searchLibraryThenShuffle _ actions) =>
    CardAction.leftoverEnterSearch? actions
  | .triggered (.enter .this) (.continuous effects _duration) =>
    match ContinuousEffect.targetingSelector? effects, ContinuousEffect.addedPT? effects with
    | some sel, some (p, t) =>
      if sel.toTargetKind == .creature then
        some (TriggeredAbility.onEnterTargetGets p t)
      else none
    | _, _ =>
      match CardAction.leftoverPumpAndGrantKeywords? (.continuous effects .endOfTurn) with
      | some (p, 0, kws) =>
        if kws.firstStrike then
          match ContinuousEffect.massSelector? effects with
          | some among =>
            if among.shape.sameController && among.shape.types.eqTypes [.creature] then
              some (TriggeredAbility.onEnterCreaturesYouControlGetAndFirstStrike p)
            else none
          | none => none
        else none
      | _ =>
        let kws := CardAction.grantedKeywords effects
        if kws != Keywords.none &&
            effects.any (fun e => ContinuousEffect.selector e == .hostOf .this) then
          some (TriggeredAbility.onEnterEnchanted (.grantKeywords kws))
        else none
  | .triggered (.enter .this) (.putCounter sel .plusOnePlusOne 1) =>
    if sel.toTargetKind == .creature then
      some TriggeredAbility.onEnterPlusOneOnCreature
    else none
  | .triggered (.enter .this) (.attach .this sel) =>
    match sel.among? with
    | some among =>
      let s := among.shape
      if s.sameController && s.types.eqTypes [.creature] then
        if Selector.includesLegendary among then
          some TriggeredAbility.onEnterAttachToLegendary
        else
          match s.subtype with
          | some st => some (TriggeredAbility.onEnterAttachToSubtype st)
          | none => some TriggeredAbility.onEnterAttachToCreatureYouControl
      else none
    | none => none
  | .triggered (.enter .this) (.sequence [.attach .this sel, .untap _]) =>
    match sel.among? with
    | some among =>
      let s := among.shape
      if s.sameController && s.types.eqTypes [.creature] then
        some (TriggeredAbility.onEnterAttachThen PermanentAction.untap)
      else none
    | none => none
  | .triggered (.enter .this) (.sequence [.attach .this sel, .continuous effects _]) =>
    match sel.among? with
    | some among =>
      let s := among.shape
      let kws := CardAction.grantedKeywords effects
      if s.sameController && s.types.eqTypes [.creature] && kws != Keywords.none then
        some (TriggeredAbility.onEnterAttachThen (.grantKeywords kws))
      else none
    | none => none
  | .triggered
      (.ordinal 2 .turnStart (.draw (.controller .this) .all))
      (.putCounter (.source .this) .plusOnePlusOne 1) =>
    some TriggeredAbility.onDrawSecondPlusOne
  | .triggered
      (.ordinal 2 .turnStart (.draw (.controller .this) .all))
      action =>
    if CardAction.leftoverPlusOneAndLifelinkTarget? action then
      some TriggeredAbility.onDrawSecondPlusOneLifelink
    else
      match CardAction.leftoverCreateTokensKindN? action with
      | some (kind, 1) => some (TriggeredAbility.onYouDrawSecondCreateTokens kind)
      | _ =>
        match CardAction.leftoverEachOpponentLoseLifeYouGain? action with
        | some 1 => some (TriggeredAbility.onResource Effect.resourceSecondDrawDrain)
        | _ =>
          match action with
          | .mill who (.nat n) =>
            if CardAction.leftoverTargetPlayer? who then
              some (TriggeredAbility.onDrawSecondMillPlayer n)
            else none
          | .putCounter sel .plusOnePlusOne 1 =>
            if sel.toTargetKind == .creature then
              some (TriggeredAbility.onResource Effect.resourceSecondDrawPlusOneTarget)
            else none
          | _ => none
  | .triggered (.draw (.controller .this) .all)
      (.putCounter (.source .this) .plusOnePlusOne 1) =>
    some TriggeredAbility.onDrawPlusOne
  | .triggered (.combatDamage .this .player)
      (.sequence [.draw (.controller .this) 1, .discard (.controller .this) 1]) =>
    some TriggeredAbility.onCombatDamageToPlayerLoot
  | .triggered (.combatDamage .this .player) (.draw _ (.nat n)) =>
    some (TriggeredAbility.onCombatDamageDraw n)
  | .triggered (.combatDamage among .player)
      (.putCounter (.source .this) .plusOnePlusOne 2) =>
    if among.shape.sameController && among.shape.subtype == some "Hero" then
      some (TriggeredAbility.onWatch Effect.watchHeroesDamagePlusTwo)
    else none
  | .triggered (.die .this) (.continuous effects _duration) =>
    match ContinuousEffect.targetingSelector? effects, ContinuousEffect.addedPT? effects with
    | some sel, some (p, t) =>
      if sel.toTargetKind == .oppCreature then
        some (TriggeredAbility.onDiesOppCreatureGets p t)
      else none
    | _, _ => none
  | .triggered (.die .this) (.draw _ (.nat n)) =>
    some (TriggeredAbility.onDiesDraw n)
  | .triggered (.die .this) (.dealDamageEqualToPower _ dest) =>
    if dest.toTargetKind == .oppCreature then
      some TriggeredAbility.onDiesDealDamageEqualToPowerToOppCreature
    else none
  | .triggered (.dieSimultaneously among _) (.scry _ (.nat n)) =>
    if among.shape.otherCreatures then
      some (TriggeredAbility.onOneOrMoreOtherCreaturesDieScry n)
    else none
  | .triggered (.enter .this)
      (.sacrifice
        (.selected (.target _ (.opponent _)) _
          (.intersection [
            .permanent,
            .cardType .creature,
            .controlled (.targetReference _)]))) =>
    some TriggeredAbility.onEnterTargetOpponentSacrificesCreature
  | .triggered (.enter .this)
      (.forEachVariable n among actions) =>
    if CardAction.leftoverEachPlayerSacrificesCreature? (.forEachVariable n among actions) then
      some TriggeredAbility.onEnterEachPlayerSacrificesCreature
    else none
  | .triggered (.enter .this)
      (.sequence [
        .exile
          (.targets _
            (.range 0 1)
            (.intersection [.inGraveyard, .owner (.opponent _)])),
        .loseLife (.opponent _) (.nat n)]) =>
    some (TriggeredAbility.onEnterExileOppGyCardOppsLoseLife n)
  | .triggered (.enter .this) (.discard (.opponent _) 1) =>
    some TriggeredAbility.onEnterEachOpponentDiscards
  | .triggered (.enter .this)
      (.divideDamage _ _ (.targets _ (.range 1 (.nat maxTargets)) _) (.nat amount)) =>
    some (TriggeredAbility.onEnterDealDividedDamage amount maxTargets)
  | .triggered
      (.or (.enter .this) (.attack .this .all))
      (.divideDamage _ _ (.targets _ (.range 1 (.nat maxTargets)) _) (.nat amount)) =>
    some (TriggeredAbility.onEnterOrAttackDealDividedDamage amount maxTargets)
  | .triggered (.enter .this)
      (.sequence [
        .optional (.actionId id (.discard _ 1)),
        .if (.happened (.actionWithId id') _) [.draw _ (.nat n)]]) =>
    if id == id' then some (TriggeredAbility.onEnterMayDiscardDraw n) else none
  | .triggered (.enter among) (.putCounter sel .plusOnePlusOne 1) =>
    if among.shape.landYouControl && sel.toTargetKind == .creatureYouControl then
      some TriggeredAbility.onLandYouControlEntersPlusOnePlusOne
    else if among == .this && sel.toTargetKind == .creature then
      some TriggeredAbility.onEnterPlusOneOnCreature
    else if among.shape.anotherArtifactYouControl &&
        (sel == .source .this || sel == .this) then
      some TriggeredAbility.onAnotherArtifactEntersPlusOne
    else none
  | .triggered (.enter among) (.draw (.controller .this) 1) =>
    if among.includedSubtype? == some "Equipment" && among.shape.sameController then
      some TriggeredAbility.onEquipmentYouControlEntersDraw
    else if among.shape.artifactYouControl then
      some TriggeredAbility.onArtifactYouControlEntersDraw
    else none
  | .triggered (.enter among) (.continuous effects _duration) =>
    if among.shape.anotherElfYouControl then
      match CardAction.leftoverSourcePump? effects with
      | some (1, 1) => some TriggeredAbility.onAnotherElfYouControlEntersGets1
      | _ => none
    else if Selector.anotherVillainYouControl among then
      match CardAction.leftoverPumpAndGrantKeywords? (.continuous effects .endOfTurn) with
      | some (1, 0, kws) =>
        if kws.lifelink then
          some (TriggeredAbility.onWatch Effect.watchVillainPlusOneLifelink)
        else none
      | _ => none
    else if among.shape.landYouControl then
      match CardAction.leftoverSourcePump? effects with
      | some (p, t) => some (TriggeredAbility.onLandYouControlEntersGets p t)
      | none => none
    else none
  | .triggered (.enter .this) (.chooseMode modes) =>
    if CardAction.leftoverTapOrUntapNonland? modes then
      some TriggeredAbility.onEnterTapOrUntapNonland
    else if CardAction.leftoverPlusOnesOrReturnArtEnch? modes then
      some (TriggeredAbility.onEnter Effect.enterPlusOnesOrReturnArtEnch)
    else none
  | .triggered (.enter .this) action =>
    if CardAction.leftoverAttachTargetEquipment? action then
      some TriggeredAbility.onEnterAttachTargetEquipment
    else
    match CardAction.leftoverUntapPlusOneIfSubtype? action with
    | some st => some (TriggeredAbility.onEnterUntapOtherPlusOneIfSubtype st)
    | none =>
      match CardAction.leftoverExileThenReturnTapped? action with
      | some sel =>
        match sel with
        | .targets _ (.range 0 3) among =>
          if among.shape.landYouControl then
            some TriggeredAbility.onEnterExileLandsThenReturnTapped
          else none
        | _ => none
      | none =>
        match CardAction.leftoverMaySacArtifactOrDiscardDraw? action with
        | some 1 => some TriggeredAbility.onEnterMaySacArtifactOrDiscardDraw
        | _ =>
          CardAction.leftoverEnterThisAction? action
  | .triggered (.enter among) (.chooseModeRestricted who modes) =>
    if among.shape.anotherCreatureYouControl &&
        CardAction.leftoverAllianceModes? who modes then
      some TriggeredAbility.onAnotherCreatureYouControlEntersAlliance
    else none
  | .triggered (.enter among) (.chooseMode modes) =>
    if among.shape.landYouControl && CardAction.leftoverTapOppOrUntapYours? modes then
      some TriggeredAbility.onLandYouControlEntersTapOrUntap
    else if CardAction.leftoverNontokenHeroModal? among modes then
      some (TriggeredAbility.onWatch Effect.watchNontokenHeroModal)
    else none
  | .triggered (.enter among) action =>
    match CardAction.leftoverPlusOneVigilance? action with
    | some 2 =>
      if among.shape.landYouControl then
        some TriggeredAbility.onLandYouControlEntersPlusOneVigilance
      else none
    | _ =>
      match action with
      | .dealDamage _ dest (.nat 1) =>
        let opp :=
          dest == .opponent (.controller .this) ||
            match dest with
            | .target _ .player => true
            | .target _ (.opponent _) => true
            | _ => false
        if Selector.anotherVillainOrArtifactYouControl among && opp then
          some (TriggeredAbility.onWatch Effect.watchVillainOrArtifactDamage)
        else none
      | .draw (.controller .this) 1 =>
        if among.includedSubtype? == some "Equipment" && among.shape.sameController then
          some TriggeredAbility.onEquipmentYouControlEntersDraw
        else if among.shape.artifactYouControl then
          some TriggeredAbility.onArtifactYouControlEntersDraw
        else none
      | .sequence [.draw (.controller .this) 1, .putCounter sel .plusOnePlusOne 1] =>
        if among.shape.landYouControl &&
            (sel == .source .this || sel == .this) then
          some TriggeredAbility.onLandYouControlEntersDrawPlusOneSource
        else none
      | .createTokens who n parts [] =>
        if among.shape.landYouControl && CardAction.leftoverYou who then
          match valToNat? n with
          | some n =>
            CardAction.leftoverTokenKind? parts |>.map
              (fun k => TriggeredAbility.onLandYouControlEntersCreateTokens k n)
          | none => none
        else none
      | _ =>
        if Selector.anotherVillainYouControl among &&
            CardAction.leftoverAttachTargetEquipment? action then
          some (TriggeredAbility.onWatch Effect.watchVillainAttachEquipment)
        else none
  | .triggered (.attack .this .all) action =>
    match CardAction.leftoverExileThenReturnTapped? action with
    | some sel =>
      match sel with
      | .targets _ (.range 0 1) among =>
        if among.shape.nontoken &&
            (among.shape.types.eqTypes [.artifact, .creature] ||
              among.shape.types.eqTypes [.creature] ||
              among.shape.types.eqTypes [.artifact]) then
          some (TriggeredAbility.onThisAttack Effect.thisAttackBlinkNontoken)
        else none
      | _ => none
    | none =>
      match action with
      | .keyword who k => leftoverKeywordTriggered? (.attack .this .all) who k
      | _ => none
  | .triggered (.attackSimultaneously among dest _)
      (.if (.any ferociousSel) [action]) =>
    if dest == .all && among.shape.sameController && ferociousSel.shape.ferocious then
      match CardAction.leftoverDrawLoseLifeSelf? action with
      | some (1, 1) => some TriggeredAbility.onYouAttackFerociousDrawLoseLife
      | _ => none
    else none
  | .triggered (.attackSimultaneously among dest _) (.draw (.controller .this) 1) =>
    if among.shape.sameController then
      if among.shape.subtype == some "Merfolk" then
        if dest == .player then
          some (TriggeredAbility.onWatch Effect.watchMerfolkAttackDraw)
        else none
      else if dest == .all then
        some TriggeredAbility.onYouAttackDraw
      else none
    else none
  | .triggered (.combatStart who) (.if (.any among) [.putCounter sel .plusOnePlusOne 1]) =>
    if who == .controller .this && among.shape.ferocious &&
        (sel == .source .this || sel == .this) then
      some TriggeredAbility.onYourBeginCombatFerociousPlusOne
    else none
  | .triggered w (.keyword who k) => leftoverKeywordTriggered? w who k
  | .triggered (.die .this) (.createTokens who n parts []) =>
    if CardAction.leftoverYou who then
      match valToNat? n with
      | some n =>
        CardAction.leftoverTokenKind? parts |>.map (fun k => TriggeredAbility.onDiesCreateTokens k n)
      | none => none
    else none
  | .triggered (.die among) (.loseLife sel 1) =>
    if among.shape.token && among.shape.sameController &&
        CardAction.leftoverTargetOpponent? sel then
      some TriggeredAbility.onYouSacrificeTokenOppLosesLife
    else none
  | .triggered (.combatDamage .this .player) (.chooseMode modes) =>
    if CardAction.leftoverWolfPlusOneOrTreasure? modes then
      some TriggeredAbility.onCombatDamageWolfPlusOneOrTreasure
    else none
  | .triggered (.combatDamage among dest) (.createTokens who n parts []) =>
    if CardAction.leftoverYou who && CardAction.leftoverPlayerOrBattle dest &&
        among.shape.sameController then
      match CardAction.leftoverTokenKind? parts, among.includedSubtype?, valToNat? n with
      | some kind, some st, some n =>
        some (TriggeredAbility.onSubtypeYouControlCombatDamageCreateTokens st kind n)
      | _, _, _ => none
    else none
  | .triggered (.attack (.hostOf .this) .all) action =>
    if CardAction.leftoverIfElseCreateSpiritsForEquipped? action then
      some TriggeredAbility.onEquippedAttacksCreateSpirits
    else none
  | .triggered (.ordinal 2 .turnStart (.castSpell among)) action =>
    if (among == .spell || among == .all) &&
        CardAction.leftoverLoseLifeCreateTreasure? action then
      some TriggeredAbility.onPlayerCastsSecondSpellLoseLifeCreateTreasure
    else none
  | .triggered (.castSpell among) (.createTokens who n parts []) =>
    if among.shape.sameController && among.shape.subtype == some "Villain" &&
        n == 1 && CardAction.leftoverYou who &&
        CardAction.leftoverTokenKind? parts == some .villain21menace then
      some (TriggeredAbility.onCasting Effect.castingVillainToken)
    else none
  | .triggered (.or (.enter .this) (.attack .this .all)) action =>
    if CardAction.leftoverPlusOneEachOtherGainLife? action then
      some TriggeredAbility.onEnterOrAttackPlusOneEachOtherGainLife
    else none
  | .triggered (.attackSimultaneously among dest preds) action =>
    if dest == .player && among.shape.sameController &&
        among.shape.types.eqTypes [.creature] &&
        preds == [.countAtLeast 2] &&
        CardAction.leftoverGrantFlyingToAttacking? action then
      some TriggeredAbility.onAttackWithTwoOrMoreGrantFlying
    else none
  | .triggered (.or (.enter .this) (.enter among)) (.createTokens who n parts []) =>
    if CardAction.leftoverYou who then
      match among.shape.anotherSubtypeYouControl, CardAction.leftoverTokenKind? parts,
          valToNat? n with
      | some st, some kind, some n =>
        some (TriggeredAbility.onThisOrAnotherSubtypeEntersCreateTokens st kind n)
      | _, _, _ => none
    else none
  | .triggered (.castSpell among) (.tap sel) =>
    if Selector.youCastNoncreatureSpell among &&
        CardAction.leftoverCreatureOrLandTarget? sel then
      some (TriggeredAbility.onCasting Effect.castingTapCreatureOrLand)
    else none
  | .triggered (.castSpell among)
      (.sequence [
        copy,
        .putCounter (.source .this) .plusOnePlusOne 2]) =>
    if CardAction.leftoverCopyWithNewTargets? copy &&
        among.shape.types.eqTypes [.instant, .sorcery] &&
        among.shape.sameController &&
        match Selector.leftoverHasTarget? among with
        | some dest => dest.shape.types.eqTypes [.artifact, .land]
        | none => false then
      some (TriggeredAbility.onCasting Effect.castingCopyIfArtifactOrLand)
    else none
  | .triggered (.castSpell among) (.continuous effects _) =>
    match Selector.leftoverHasTarget? among with
    | some dest =>
      if among.shape.sameController && Selector.includesSpell among &&
          dest.shape.mustBePermanent &&
          dest.shape.types.eqTypes [.creature] &&
          CardAction.leftoverGrantFlyingToThose? effects then
        some (TriggeredAbility.onCasting Effect.castingTargetsGainFlying)
      else none
    | none => none
  | .triggered (.castSpell among) action =>
    if Selector.youCastNoncreatureSpell among &&
        CardAction.leftoverMayPayHasteUnblockable? action then
      some (TriggeredAbility.onCasting Effect.castingMayPayHasteUnblockable)
    else none
  | .triggered (.discard who) action =>
    if CardAction.leftoverYou who &&
        CardAction.leftoverExileGyPlayUntilNextTurn? action then
      some (TriggeredAbility.onResource Effect.resourceDiscardExilePlay)
    else none
  | .triggered (.returnToHand among) action =>
    if among.shape.other && among.shape.sameController &&
        among.shape.nonland && !among.shape.nontoken &&
        match action with
        | .putCounter (.source .this) .plusOnePlusOne 1 => true
        | _ => false then
      some (TriggeredAbility.onWatch Effect.watchJusticeBounce)
    else none
  | _ => none

end Ability

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
  costReductionIfTargetAttacking : Nat := 0
  costReductionIfCreatureDied : Nat := 0
  costReductionIfYouControl : Option (Nat × String) := none
  additionalCostSacrificeArtifactOrCreature : Bool := false
  additionalCostOrPayGeneric : Option Nat := none
  extraLandIfOtherSubtype : Option String := none
  staticAbilities : Array StaticAbility := #[]
  tapAddMana : Array ManaType := #[]
  tapAddAnyColorEqualToPower : Bool := false
  tapAddAnyColorForInstantOrSorcery : Bool := false
  tapAddOneOf : Array ManaType := #[]
  entersTapped : Bool := false
  colorIndicator : Option ColorSet := none
  sagaChapters : Array SagaChapter := #[]
deriving Inhabited

namespace CardFace

def hostBonus (enchanted : Bool) (p t : Int) (k : Keywords) : StaticAbility :=
  if enchanted then
    if k == Keywords.none then .enchantedCreatureGets p t
    else .enchantedCreatureGetsAndHas p t k
  else if k == Keywords.none then
    .equippedCreatureGets p t
  else if p == 0 && t == 0 then
    .equippedCreatureHasKeywords k
  else
    .equippedCreatureGetsAndHas p t k

def mergeHostBonus (prev : StaticAbility) (p t : Int) (k : Keywords)
    (enchanted : Bool) : Option StaticAbility :=
  if enchanted then
    match prev with
    | .enchantedCreatureGets p0 t0 =>
      some (hostBonus true (p0 + p) (t0 + t) k)
    | .enchantedCreatureGetsAndHas p0 t0 k0 =>
      some (hostBonus true (p0 + p) (t0 + t) (k0.merge k))
    | _ => none
  else
    match prev with
    | .equippedCreatureGets p0 t0 =>
      some (hostBonus false (p0 + p) (t0 + t) k)
    | .equippedCreatureHasKeywords k0 =>
      some (hostBonus false p t (k0.merge k))
    | .equippedCreatureGetsAndHas p0 t0 k0 =>
      some (hostBonus false (p0 + p) (t0 + t) (k0.merge k))
    | _ => none

def pushHostBonus (b : CardFace) (p t : Int) (k : Keywords) : CardFace :=
  let enchanted := b.types.contains .enchantment
  match b.staticAbilities.back? with
  | some prev =>
    match mergeHostBonus prev p t k enchanted with
    | some merged =>
      { b with staticAbilities := b.staticAbilities.pop.push merged }
    | none =>
      { b with staticAbilities := b.staticAbilities.push (hostBonus enchanted p t k) }
  | none =>
    { b with staticAbilities := b.staticAbilities.push (hostBonus enchanted p t k) }

def applyReduceCost (assign : CardFace → Nat → CardFace) (b : CardFace)
    (e : ContinuousEffect) : CardFace :=
  match e with
  | .reduceCost _ costs =>
    assign b (ManaCost.manaValue (Cost.manaCost costs))
  | _ => b

/-- Cost-reduction leftovers implied by a selector-shaped condition. -/
def applyIfShape (b : CardFace) (s : Selector.Shape)
    (inners : List ContinuousEffect) : CardFace :=
  if s.tappedCreature then
    inners.foldl
      (applyReduceCost fun b n =>
        { b with costReductionIfTargetTapped := b.costReductionIfTargetTapped + n })
      b
  else if s.attackingNontokenCreature then
    inners.foldl
      (applyReduceCost fun b n =>
        { b with
          costReductionIfTargetAttackingNontoken :=
            b.costReductionIfTargetAttackingNontoken + n })
      b
  else if s.attackingCreature then
    inners.foldl
      (applyReduceCost fun b n =>
        { b with
          costReductionIfTargetAttacking :=
            b.costReductionIfTargetAttacking + n })
      b
  else if s.diedThisTurnCreature then
    inners.foldl
      (applyReduceCost fun b n =>
        { b with
          costReductionIfCreatureDied := b.costReductionIfCreatureDied + n })
      b
  else b

/-- Extra land plays while you control another of a subtype. -/
def extraLandIfOtherSubtype? (among : Selector) (inners : List ContinuousEffect)
    : Option String :=
  match inners with
  | [.increaseLandPlayLimit who (Value.nat 1)] =>
    if who == .controller .this then among.shape.anotherSubtypeYouControl
    else none
  | _ => none

/-- This has haste as long as you control another of a subtype. -/
def leftoverHasteIfOtherSubtype? (among : Selector) (inners : List ContinuousEffect)
    : Option String :=
  match inners with
  | [.gainAbility who (.keyword .haste)] =>
    if who == .this || who == .source .this then
      among.shape.anotherSubtypeYouControl
    else none
  | _ => none

/-- Equip abilities you activate that target this, reduced by that much. -/
def leftoverEquipAbilitiesTargetingThisCostLess? (who : Selector) (costs : List Cost)
    : Option Nat :=
  let n := ManaCost.manaValue (Cost.manaCost costs)
  if n != 0 &&
      Selector.leftoverKeywordAbility? who == some .equip &&
      Selector.leftoverHasTarget? who == some .this &&
      who.shape.sameController then
    some n
  else none

def applyContinuousEffect (b : CardFace) : ContinuousEffect → CardFace
  | .gainAbility (.hostOf .this) (.keyword k) =>
    pushHostBonus b 0 0 k.toKeywords
  | .gainAbility sel (.keyword k) =>
    let s := sel.shape
    if s.attacking && s.token && s.sameController then
      { b with staticAbilities := b.staticAbilities.push (.attackingTokensHave k.toKeywords) }
    else if k == .trample && sel.includedSubtype? == some "Army" && s.sameController then
      { b with staticAbilities := b.staticAbilities.push .armiesYouControlHaveTrample }
    else b
  | .gainAbility _ _ => b
  | .addPowerToughness (.hostOf .this) vp vt =>
    match valToInt? vp, valToInt? vt with
    | some p, some t => pushHostBonus b p t Keywords.none
    | _, _ => b
  | .addPowerToughness sel vp vt =>
    match valToInt? vp, valToInt? vt with
    | some p, some t =>
      let s := sel.shape
      if s.other && s.sameController && s.types.eqTypes [.creature] then
        { b with
          staticAbilities :=
            b.staticAbilities.push
              (.otherCreaturesGet sel.includedSubtypes.toArray p t) }
      else if s.opponentControls && s.types.eqTypes [.creature] then
        { b with
          staticAbilities := b.staticAbilities.push (.opponentsCreaturesGet p t) }
      else b
    | _, _ => b
  | .if (.any among) inners =>
    match extraLandIfOtherSubtype? among inners with
    | some t => { b with extraLandIfOtherSubtype := some t }
    | none =>
        match leftoverHasteIfOtherSubtype? among inners with
      | some t =>
        { b with
          staticAbilities :=
            b.staticAbilities.push (.hasteIfYouControlOtherSubtype t) }
      | none =>
          if Selector.includesLegendary among && among.shape.sameController &&
              among.shape.types.eqTypes [.creature] then
            inners.foldl
              (applyReduceCost fun b n =>
                { b with
                  activatedAbilities :=
                    b.activatedAbilities.map fun ab =>
                      { ab with
                        costReductionIfYouControlLegendary :=
                          ab.costReductionIfYouControlLegendary + n } })
              b
          else applyIfShape b among.shape inners
  | .if (.targetsIncludeAny _ among) inners => applyIfShape b among.shape inners
  | .if (.anySubtype among st) inners =>
    match inners with
    | [.increaseLandPlayLimit who (Value.nat 1)] =>
      if who == .controller .this && among.shape.other &&
          among.shape.sameController then
        { b with extraLandIfOtherSubtype := some st.toString }
      else b
    | _ =>
      if among.shape.sameController then
        inners.foldl
          (applyReduceCost fun b n =>
            { b with costReductionIfYouControl := some (n, st.toString) })
          b
      else b
  | .if (.didNotHappen _ _) _ => b
  | .if (.happened (.die who) .turnStart) inners =>
    applyIfShape b { who.shape with diedThisTurn := true } inners
  | .if (.happened (.putCountersSimultaneously who .plusOnePlusOne) .turnStart)
      [.gainAbility flyingWho (.keyword .flying)] =>
    if (who == .this || who == .source .this) &&
        (flyingWho == .this || flyingWho == .source .this) then
      { b with staticAbilities := b.staticAbilities.push .flyingIfPlusOneThisTurn }
    else b
  | .if (.happened _ _) _ => b
  | .if (.timeToCastSorcery _) _ => b
  | .if (.turn _) _ => b
  | .if (.and _ _) _ => b
  | .if (.countAtLeast among n) inners =>
    if n == 2 then
      match CardAction.leftoverGetsIfGyCreatureCards? among inners with
      | some ab => { b with staticAbilities := b.staticAbilities.push ab }
      | none => b
    else b
  | .replace (.enter who) actions =>
    if (who == .this || who == .source .this) &&
        CardAction.leftoverEntersTapped? actions then
      { b with entersTapped := true }
    else b
  | .replace (.damage src who) actions =>
    if (who == .this || who == .source .this) && src == .all &&
        CardAction.leftoverHealThenKeepReplaced? actions then
      { b with staticAbilities := b.staticAbilities.push .healOtherDamageWhenDealt }
    else b
  | .replace (.combatDamage _ _) _ => b
  | .replace _ _ => b
  | .forbid
      (.or
        (.attack who dest)
        (.block blocker blocked)) =>
    if who.shape.flying && (dest == .controller .this || dest == .this) &&
        blocker.shape.flying && blocked.shape.sameController &&
        blocked.shape.types.eqTypes [.creature] then
      { b with
        staticAbilities := b.staticAbilities.push .flyingCantAttackYouOrBlockYours }
    else b
  | .forbid (.attack _ _) =>
    b
  | .forbid (.block .this .all) =>
    { b with staticAbilities := b.staticAbilities.push (.cantBlockUnlessYouControl #[]) }
  | .forbid (.block who .this) =>
    if who == .any then
      { b with keywords := { b.keywords with cantBeBlocked := true } }
    else if who == .token then
      { b with staticAbilities := b.staticAbilities.push .cantBeBlockedByTokens }
    else b
  | .forbid _ => b
  | .canCastWithoutPayingManaCost _ _ => b
  | .canPlay _ _ => b
  | .setBasePowerToughnessFrom _ _ => b
  | .gainType _ _ => b
  | .gainSubtype _ _ => b
  | .gainAllSubtypes _ _ => b
  | .setPowerToughnessEqualToCount who among =>
    if (who == .this || who == .source .this) && among.shape.landYouControl then
      { b with
        staticAbilities :=
          b.staticAbilities.push .powerToughnessEqualLandsYouControl }
    else b
  | .addPowerToughnessPer who among p t =>
    match CardAction.leftoverOtherSubtypeGetPowerPerArtifactToken? who among p t with
    | some st =>
      { b with
        staticAbilities :=
          b.staticAbilities.push (.otherSubtypeGetPowerPerArtifactToken st) }
    | none => b
  | .increaseLandPlayLimit _ _ => b
  | .additionalCost _ cs =>
    { b with
      additionalCostSacrificeArtifactOrCreature :=
        b.additionalCostSacrificeArtifactOrCreature ||
          Cost.sacrificesArtifactOrCreature cs
      additionalCostOrPayGeneric :=
        b.additionalCostOrPayGeneric.orElse (fun _ => Cost.orPayGeneric? cs) }
  | .reduceCost who costs =>
    match leftoverEquipAbilitiesTargetingThisCostLess? who costs with
    | some n =>
      { b with
        staticAbilities :=
          b.staticAbilities.push (.equipAbilitiesTargetingThisCostLess n) }
    | none =>
      { b with
        costReductionIfTargetTapped :=
          b.costReductionIfTargetTapped + ManaCost.manaValue (Cost.manaCost costs) }

def applyAbility (b : CardFace) : Ability → CardFace
  | .keyword k => { b with keywords := b.keywords.merge k.toKeywords }
  | .keywordWithCost k costs =>
    match (Ability.keywordWithCost k costs).toActivatedAbility? with
    | some ab => { b with activatedAbilities := b.activatedAbilities.push ab }
    | none => b
  | .keywordWithSubtypeAndCost k st cost =>
    match (Ability.keywordWithSubtypeAndCost k st cost).toActivatedAbility? with
    | some ab => { b with activatedAbilities := b.activatedAbilities.push ab }
    | none => b
  | .keywordWithTarget _ _ _ => b
  | .keywordWithEffect k actions =>
    match k with
    | .chapter n =>
      match CardAction.leftoverChapterEffect? actions with
      | some e =>
        { b with
          sagaChapters :=
            b.sagaChapters.push (SagaChapter.of (toRomanNumeral n) e.phrase e) }
      | none => b
    | _ => b
  | .activated costs action =>
    if CardAction.leftoverTapAddAnyColorEqualToPower? costs action then
      { b with tapAddAnyColorEqualToPower := true }
    else if CardAction.leftoverTapAddAnyColorForInstantOrSorcery? costs action then
      { b with tapAddAnyColorForInstantOrSorcery := true }
    else
      match CardAction.leftoverTapAddMana? costs action with
      | some types => { b with tapAddMana := types }
      | none =>
        match CardAction.leftoverTapAddOneOf? costs action with
        | some types => { b with tapAddOneOf := types }
        | none =>
          { b with
            activatedAbilities :=
              b.activatedAbilities.push (Ability.activatedAbility costs action) }
  | .activatedIf cond costs action =>
    match (Ability.activatedIf cond costs action).toActivatedAbility? with
    | some ab => { b with activatedAbilities := b.activatedAbilities.push ab }
    | none => b
  | .abilityId n a =>
    match (Ability.abilityId n a).toActivatedAbility? with
    | some ab => { b with activatedAbilities := b.activatedAbilities.push ab }
    | none => applyAbility b a
  | .triggered w action =>
    match (Ability.triggered w action).toTriggeredAbility? with
    | some t => { b with triggeredAbilities := b.triggeredAbilities.push t }
    | none => b
  | .static e => applyContinuousEffect b e

def apply (b : CardFace) : CardPart → CardFace
  | .name n => { b with name := n }
  | .manaCost c => { b with manaCost := (c : ManaCost) }
  | .type t => { b with types := b.types.push t }
  | .supertype s => { b with supertypes := b.supertypes.push s }
  | .subtype s => { b with subtypes := b.subtypes.push s.toString }
  | .colorIndicator cs =>
    { b with
      colorIndicator :=
        if cs.isEmpty then none
        else some (cs.foldl ColorSet.insert ColorSet.empty) }
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
      costReductionIfTargetAttacking := b.costReductionIfTargetAttacking
      costReductionIfCreatureDied := b.costReductionIfCreatureDied
      costReductionIfYouControl := b.costReductionIfYouControl
      additionalCostSacrificeArtifactOrCreature :=
        b.additionalCostSacrificeArtifactOrCreature
      additionalCostOrPayGeneric := b.additionalCostOrPayGeneric
      extraLandIfOtherSubtype := b.extraLandIfOtherSubtype
      staticAbilities := b.staticAbilities
      tapAddMana := b.tapAddMana
      tapAddAnyColorEqualToPower := b.tapAddAnyColorEqualToPower
      tapAddAnyColorForInstantOrSorcery := b.tapAddAnyColorForInstantOrSorcery
      tapAddOneOf := b.tapAddOneOf
      entersTapped := b.entersTapped
      colorIndicator := b.colorIndicator
      adventure := adventure
      saga :=
        if b.sagaChapters.isEmpty then none
        else
          let final :=
            b.sagaChapters.foldl (fun acc ch =>
              ch.chapterNumbers.foldl (fun acc n => max acc n) acc) 0
          some { sacrificeAfter := toRomanNumeral final, chapters := b.sagaChapters }
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
        (Value.int 1) (Value.int 1)]
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
            .controlled (.controller .this)]) (Value.int 1) (Value.int 1)]
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
      (.nat 5)
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
        (.if
          (.targetsIncludeAny
            .this
            (.intersection [
              .permanent,
              .cardType .creature,
              .tapped]))
          [.reduceCost .this [.mana [.generic 3]]])),
    .actions [
      .dealDamage
        .this
        (.target 1 (.intersection [.permanent, .cardType .creature]))
        (.nat 5)]
  ]).toCardDef.costReductionIfTargetTapped == 3

-- Eagle of the Great Shelf: whenever this attacks, +1/+1 (per other creature leftover).
#guard
  match
    (Ability.triggered
      (.attack .this .all)
      (.continuous [.addPowerToughness (.source .this) (Value.int 1) (Value.int 1)] .endOfTurn)).toTriggeredAbility? with
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
      .continuous [.addPowerToughness (.targetReference 1) (Value.int 2) (Value.int 2)] .endOfTurn,
      .if
        (.anySubtype (.targetReference 1) .dwarf)
        [
          .optional
            (.attach
              (.selected
                (.controller .this)
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

#guard CardAction.toEffect (.scry (.controller .this) 2) == Effect.scry 2

#guard valToNat? (3 : Value) == some 3
#guard (valToNat? Value.x).isNone
#guard (valToNat? (Value.greatestPower .this)).isNone
#guard (valToNat? (Value.greatestToughness .this)).isNone
#guard Range.range Value.x 1 != Range.range 0 1
#guard Range.any != Range.range 0 0
#guard Range.from Value.x != Range.from 1
#guard Range.from 1 != Range.range 1 1
#guard
  let drawX : CardAction := .draw (.controller .this) .x
  let millPower : CardAction :=
    .mill (.controller .this)
      (.greatestPower
        (.intersection [
          .permanent,
          .cardType .creature,
          .controlled (.controller .this)]))
  let tokens : CardAction :=
    .createTokens (.controller .this) 1 PredefinedToken.treasureToken [.tapped]
  drawX != .draw (.controller .this) 1 &&
    millPower != .mill (.controller .this) 1 &&
    tokens ==
      .createTokens (.controller .this) 1 PredefinedToken.treasureToken [.tapped]

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

-- Thirst for Knowledge: discard two unless you discard an artifact card.
#guard
  CardAction.leftoverDrawThreeDiscardUnlessArtifact?
    (.sequence [
      .draw (.controller .this) 3,
      .preventable
        (.controller .this)
        [.discard (.cardType .artifact)]
        (.discard (.controller .this) 2)]) == some true

#guard
  CardAction.leftoverDrawThreeDiscardUnlessArtifact?
    (.sequence [
      .draw (.controller .this) 3,
      .playerSelectAction
        (.controller .this)
        (.range 1 1)
        [
          .discard (.intersection [.cardType .artifact]) 1,
          .discard (.controller .this) 2]]) |>.isNone

#guard
  CardAction.leftoverDrawThreeDiscardUnlessArtifact?
    (.sequence [
      .draw (.controller .this) 3,
      .preventable
        (.controller .this)
        [.discard .this]
        (.discard (.controller .this) 2)]) |>.isNone

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
          (.putToGraveyard (.intersection [.wasObjectOfAction 1, .permanentSpell]))
          [.actionId 2 (.exile (.replacingObject)),
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
    .permanent,
    .cardType .creature,
    .attacking .all,
    .not .token]) |>.attackingNontokenCreature

#guard
  (TraditionalCardDefinition.card [
    .ability (
      .static
        (.if
          (.targetsIncludeAny
            .this
            (.intersection [
              .permanent,
              .cardType .creature,
              .attacking .all,
              .not .token]))
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
              .controlled (.opponent (.controller .this))])) (Value.int (-1)) (Value.int (-1))]
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
          .sacrificeCount
            (.intersection [
              .permanent,
              .union [.cardType .artifact, .cardType .creature]])
            1,
          .mana [.generic 4]]])),
    .actions [
      .destroy (.target 1 (.intersection [.permanent, .cardType .creature]))]
  ]).toCardDef.additionalCostSacrificeArtifactOrCreature

#guard
  (TraditionalCardDefinition.card [
    .ability (.static (
      .additionalCost .this
        [.or [
          .sacrificeCount
            (.intersection [
              .permanent,
              .union [.cardType .artifact, .cardType .creature]])
            1,
          .mana [.generic 4]]]))
  ]).toCardDef.additionalCostOrPayGeneric == some 4

-- Improvised Club: sacrifice one artifact or creature as an additional cost.
#guard
  (TraditionalCardDefinition.card [
    .ability (.static (
      .additionalCost .this
        [.sacrificeCount
          (.intersection [
            .permanent,
            .union [.cardType .artifact, .cardType .creature]])
          1]))
  ]).toCardDef.additionalCostSacrificeArtifactOrCreature

-- Kingpin's Enforcers: {2}{B}, sacrifice an artifact or creature: draw a card.
#guard
  match
    (Ability.activated
      [.mana [.generic 2, .mono .black],
        .sacrificeCount
          (.intersection [
            .permanent,
            .union [.cardType .artifact, .cardType .creature]])
          1]
      (.draw (.controller .this) 1)).toActivatedAbility? with
  | some ab =>
    ab.cost.sacrificeAnotherCreatureOrArtifact &&
      ab.cost.mana == ManaCost.ofGenericAndColor 2 .black &&
      ab.effect == Effect.abilityDraw 1
  | none => false

-- Sacrifice another Goblin is `sacrificeCount` 1, not `sacrifice` (all of them).
#guard
  match
    (Ability.activated
      [.tapSymbol,
        .sacrificeCount
          (.intersection [
            .not .this,
            .permanent,
            .subtype .goblin,
            .controlled (.controller .this)])
          1]
      (.addMana (.controller .this) [.mono .black, .mono .red])).toActivatedAbility? with
  | some ab =>
      ab.cost.tap &&
      ab.cost.sacrificeAnotherSubtype == some "Goblin" &&
      ab.effect == Effect.addMana #[.colored .black, .colored .red]
  | none => false

#guard
  match
    (Ability.activated
      [.tapSymbol,
        .sacrifice
          (.intersection [
            .not .this,
            .permanent,
            .subtype .goblin,
            .controlled (.controller .this)])]
      (.addMana (.controller .this) [.mono .black, .mono .red])).toActivatedAbility? with
  | some ab => ab.cost.sacrificeAnotherSubtype.isNone
  | none => false

-- Desolation Prowler: pay 2 life, +2/+2, once each turn.
#guard
  match
    (Ability.abilityId 1
      (.activatedIf
        (.didNotHappen (.abilityWithIdActivated 1) .turnStart)
        [.life 2]
        (.continuous [.addPowerToughness (.source .this) (Value.int 2) (Value.int 2)] .endOfTurn))).toActivatedAbility? with
  | some ab =>
    ab.effect == Effect.sourceGets 2 2 && ab.cost.payLife == 2 && ab.onceEachTurn
  | none => false

-- Ravening Warg: Ferocious attack, gain 2 life.
#guard Selector.shape
  (.intersection [
    .permanent,
    .cardType .creature,
    .controlled (.controller .this),
    .powerAtLeast (Value.int 4)]) |>.ferocious

#guard
  match
    (Ability.triggered
      (.attack .this .all)
      (.if
        (.any
          (.intersection [
            .permanent,
            .cardType .creature,
            .controlled (.controller .this),
            .powerAtLeast (Value.int 4)]))
        [.gainLife (.controller .this) 2])).toTriggeredAbility? with
  | some ab => ab == TriggeredAbility.onAttackFerociousGainLife 2
  | none => false

-- Meager Meal: +1/+1 on up to one target creature; target player gains 2 life.
#guard
  let action : CardAction :=
    .sequence [
      .putCounter
        (.targets 1 (.range 0 1) (.intersection [.permanent, .cardType .creature]))
        .plusOnePlusOne
        1,
      .gainLife (.target 2 .player) 2]
  action.toEffect == Effect.plusOneUpToOneAndPlayerGainsLife 2

#guard
  CardAction.leftoverPlusOneAndGainLife?
    (.sequence [
      .putCounter
        (.targets 1 (.range 0 1) (.intersection [.permanent, .cardType .creature]))
        .plusOnePlusOne
        1,
      .gainLife (.target 1 .player) 2]) |>.isNone

#guard
  CardAction.leftoverPlusOnesOrReturnArtEnch?
    [
      .putCounter
        (.targets 1 (.range 0 2) (.intersection [.permanent, .cardType .creature]))
        .plusOnePlusOne
        1,
      .returnToHand
        (.target
          2
          (.intersection [
            .inGraveyard,
            .union [.cardType .artifact, .cardType .enchantment],
            .owner (.controller .this)]))]

#guard
  !CardAction.leftoverPlusOnesOrReturnArtEnch?
    [
      .putCounter
        (.targets 1 (.range 0 2) (.intersection [.permanent, .cardType .creature]))
        .plusOnePlusOne
        1,
      .returnToHand
        (.target
          1
          (.intersection [
            .inGraveyard,
            .union [.cardType .artifact, .cardType .enchantment],
            .owner (.controller .this)]))]

#guard
  CardAction.leftoverAttachTargetEquipment?
    (.attach
      (.target
        1
        (.intersection [
          .permanent,
          .subtype .equipment,
          .controlled (.controller .this)]))
      (.targets
        2
        (.range 0 1)
        (.intersection [
          .permanent,
          .cardType .creature,
          .controlled (.controller .this)])))

#guard
  !CardAction.leftoverAttachTargetEquipment?
    (.attach
      (.target
        1
        (.intersection [
          .permanent,
          .subtype .equipment,
          .controlled (.controller .this)]))
      (.targets
        1
        (.range 0 1)
        (.intersection [
          .permanent,
          .cardType .creature,
          .controlled (.controller .this)])))

-- Dreaded Bat-Cloud: {3} less if a creature died this turn.
#guard
  let s : Selector.Shape := { Selector.shape (.cardType .creature) with diedThisTurn := true }
  s.diedThisTurnCreature

#guard
  (TraditionalCardDefinition.card [
    .ability (
      .static
        (.if
          (.happened (.die (.cardType .creature)) .turnStart)
          [.reduceCost .this [.mana [.generic 3]]]))
  ]).toCardDef.costReductionIfCreatureDied == 3

-- Crude Bent Blade: ETB opponent sacrifices; equipped +2/+1; Equip {2}.
#guard
  match
    (Ability.triggered
      (.enter .this)
      (.sacrifice
        (.selected
          (.target 1 (.opponent (.controller .this)))
          (.range 1 1)
          (.intersection [
            .permanent,
            .cardType .creature,
            .controlled (.targetReference 1)])))).toTriggeredAbility? with
  | some ab => ab == TriggeredAbility.onEnterTargetOpponentSacrificesCreature
  | none => false

#guard
  (TraditionalCardDefinition.card [
    .ability (.static (.addPowerToughness (.hostOf .this) (Value.int 2) (Value.int 1)))
  ]).toCardDef.staticAbilities == #[.equippedCreatureGets 2 1]

#guard
  let action : CardAction :=
    .attach
      .this
      (.target
        1
        (.intersection [
          .permanent,
          .cardType .creature,
          .controlled (.controller .this)]))
  action.toAbilityEffect == Effect.attachToTargetCreatureYouControl

#guard Keyword.equip.toKeywords == Keywords.none
#guard Keyword.enchant.toKeywords == Keywords.none
#guard Keyword.recruit.toKeywords == Keywords.none
#guard (Keyword.amass .goblin (.nat 1)).toKeywords == Keywords.none
#guard (Keyword.connive (.nat 1)).toKeywords == Keywords.none
#guard (Keyword.chapter 1).toKeywords == Keywords.none
#guard toString Keyword.recruit == "recruit"
#guard toString (Keyword.amass .goblin (.nat 1)) == "amass Goblins 1"
#guard toString (Keyword.amass .orc (.nat 2)) == "amass Orcs 2"
#guard toString (Keyword.connive (.nat 1)) == "connive 1"
#guard toString (Keyword.connive (.nat 2)) == "connive 2"
#guard toString (Keyword.chapter 1) == "chapter I"
#guard toString (Keyword.chapter 3) == "chapter III"
#guard (Keyword.typecycling [] [] [.halfling]).toKeywords == Keywords.none
#guard toString (Keyword.typecycling [] [] [.halfling]) == "Halflingcycling"
#guard (Keyword.typecycling [.basic] [.land] []).toKeywords == Keywords.none
#guard toString (Keyword.typecycling [.basic] [.land] []) ==
  "Basic landcycling"
#guard toString (Keyword.typecycling [] [.land] []) == "landcycling"
#guard Keyword.typecyclingPhrase [] [] [.halfling] == "Halfling"
#guard Keyword.typecyclingPhrase [.basic] [.land] [] == "Basic land"

#guard
  let c :=
    (TraditionalCardDefinition.card [
      .type .enchantment,
      .subtype .aura,
      .ability (
        .keywordWithTarget
          .enchant
          1
          (.intersection [.permanent, .cardType .creature]))
    ]).toCardDef
  c.isAura && c.keywords == Keywords.none && c.activatedAbilities.isEmpty

#guard
  match
    (Ability.keywordWithCost .equip [.mana [.generic 2]]).toActivatedAbility? with
  | some ab =>
    ab.onlyAsSorcery &&
      ab.effect == Effect.attachToTargetCreatureYouControl &&
      ab.cost.mana == ManaCost.ofGeneric 2
  | none => false

#guard
  let c :=
    (TraditionalCardDefinition.card [
      .ability (.keywordWithCost .equip [.mana [.generic 2]])
    ]).toCardDef
  c.activatedAbilities.size == 1 &&
    c.activatedAbilities[0]!.onlyAsSorcery &&
    c.activatedAbilities[0]!.effect == Effect.attachToTargetCreatureYouControl &&
    c.activatedAbilities[0]!.cost.mana == ManaCost.ofGeneric 2

#guard
  match
    (Ability.keywordWithSubtypeAndCost
      .equip .human (.mana [.generic 1])).toActivatedAbility? with
  | some ab =>
    ab.onlyAsSorcery &&
      ab.equipSubtype == some "Human" &&
      ab.effect == Effect.attachToTargetCreatureYouControl &&
      ab.cost.mana == ManaCost.ofGeneric 1
  | none => false

#guard
  let c :=
    (TraditionalCardDefinition.card [
      .ability
        (.keywordWithSubtypeAndCost .equip .human (.mana [.generic 1]))
    ]).toCardDef
  c.activatedAbilities.size == 1 &&
    c.activatedAbilities[0]!.onlyAsSorcery &&
    c.activatedAbilities[0]!.equipSubtype == some "Human" &&
    c.activatedAbilities[0]!.effect == Effect.attachToTargetCreatureYouControl &&
    c.activatedAbilities[0]!.cost.mana == ManaCost.ofGeneric 1

#guard
  match
    (Ability.keywordWithCost
      (.typecycling [] [] [.halfling])
      [.mana [.generic 4]]).toActivatedAbility? with
  | some ab =>
    ab.activateFromHand &&
      ab.cost.discardSource &&
      ab.cost.mana == ManaCost.ofGeneric 4 &&
      ab.effect == Effect.searchLandTypeToHand "Halfling"
  | none => false

#guard
  let c :=
    (TraditionalCardDefinition.card [
      .ability
        (.keywordWithCost (.typecycling [] [] [.halfling]) [.mana [.generic 4]])
    ]).toCardDef
  c.activatedAbilities.size == 1 &&
    c.activatedAbilities[0]!.activateFromHand &&
    c.activatedAbilities[0]!.cost.discardSource &&
    c.activatedAbilities[0]!.effect == Effect.searchLandTypeToHand "Halfling"

#guard
  match
    (Ability.keywordWithCost
      (.typecycling [.basic] [.land] [])
      [.mana [.generic 2]]).toActivatedAbility? with
  | some ab =>
    ab.activateFromHand &&
      ab.cost.discardSource &&
      ab.cost.mana == ManaCost.ofGeneric 2 &&
      ab.effect == Effect.searchLandTypeToHand "Basic land"
  | none => false

#guard
  let c :=
    (TraditionalCardDefinition.card [
      .ability
        (.keywordWithCost
          (.typecycling [.basic] [.land] [])
          [.mana [.generic 2]])
    ]).toCardDef
  c.activatedAbilities.size == 1 &&
    c.activatedAbilities[0]!.activateFromHand &&
    c.activatedAbilities[0]!.cost.discardSource &&
    c.activatedAbilities[0]!.effect == Effect.searchLandTypeToHand "Basic land"

-- Gollum the Abandoned: can't block; ETB exile GY; return from GY.
#guard
  (TraditionalCardDefinition.card [
    .ability (.static (.forbid (.block .this .any)))
  ]).toCardDef.staticAbilities == #[.cantBlockUnlessYouControl #[]]

#guard
  match
    (Ability.triggered
      (.enter .this)
      (.sequence [
        .exile
          (.targets 1 (.range 0 1) (.intersection [.inGraveyard, .owner (.opponent (.controller .this))])),
        .loseLife (.opponent (.controller .this)) 2])).toTriggeredAbility? with
  | some ab => ab == TriggeredAbility.onEnterExileOppGyCardOppsLoseLife 2
  | none => false

#guard
  match
    (Ability.activatedIf
      (.timeToCastSorcery (.controller .this))
      [.mana [.generic 2],
        .sacrificeCount
          (.intersection [
            .permanent,
            .union [.cardType .artifact, .cardType .creature]])
          1]
      (.returnToHand (.intersection [.inGraveyard, .source .this]))).toActivatedAbility? with
  | some ab =>
    ab.onlyAsSorcery &&
      ab.activateFromGraveyard &&
      ab.effect == Effect.returnFromGraveyardToHand &&
      ab.cost.mana == ManaCost.ofGeneric 2 &&
      ab.cost.sacrificeAnotherCreatureOrArtifact
  | none => false

-- Gnashing of Teeth / Reverent Howl modes.
#guard
  let action : CardAction :=
    .continuous
      [.addPowerToughness
        (.target 1 (.intersection [.permanent, .cardType .creature])) (Value.int (-5)) (Value.int (-5)),
        .replace
          (.putToGraveyard (.targetReference 1))
          [.exile (.replacingObject)]]
      .endOfTurn
  action.toEffect == Effect.pumpAndExileIfDies (-5) (-5)

#guard
  let action : CardAction :=
    .continuous
      [.addPowerToughness
        (.intersection [
          .permanent,
          .cardType .creature,
          .controlled (.target 1 .player)]) (Value.int (-1)) (Value.int (-1))]
      .endOfTurn
  action.toEffect == Effect.creaturesTargetPlayerGet (-1) (-1)

#guard
  let action : CardAction :=
    .chooseMode [
      .continuous
        [.addPowerToughness
          (.target 1 (.intersection [.permanent, .cardType .creature])) (Value.int (-5)) (Value.int (-5)),
          .replace
            (.putToGraveyard (.targetReference 1))
            [.exile (.replacingObject)]]
        .endOfTurn,
      .continuous
        [.addPowerToughness
          (.intersection [
            .permanent,
            .cardType .creature,
            .controlled (.target 2 .player)]) (Value.int (-1)) (Value.int (-1))]
        .endOfTurn]
  CardAction.leftoverModes? action ==
    some #[Effect.pumpAndExileIfDies (-5) (-5), Effect.creaturesTargetPlayerGet (-1) (-1)]

#guard
  let action : CardAction :=
    .sequence [.draw (.target 1 .player) 2, .loseLife (.targetReference 1) 2]
  action.toEffect == Effect.targetPlayerDrawLoseLife 2 2

#guard
  let action : CardAction :=
    .continuous
      [.addPowerToughness
        (.target 1 (.intersection [.permanent, .cardType .creature])) (Value.int 2) (Value.int 2),
        .gainAbility (.targetReference 1) (.keyword .lifelink)]
      .endOfTurn
  action.toEffect == Effect.pumpAndLifelink 2 2

-- Stony-Voiced Goblins: each opponent discards a card.
#guard
  match
    (Ability.triggered
      (.enter .this)
      (.discard (.opponent (.controller .this)) 1)).toTriggeredAbility? with
  | some ab => ab == TriggeredAbility.onEnterEachOpponentDiscards
  | none => false

-- Spew Flame: 5 damage to target creature.
#guard
  let action : CardAction :=
    .dealDamage
      .this
      (.target 1 (.intersection [.permanent, .cardType .creature]))
      (.nat 5)
  action.toEffect == Effect.dealDamageToCreature 5

-- Gandalf, Spark Starter: enters, 3 damage divided among one to three targets.
#guard
  match
    (Ability.triggered
      (.enter .this)
      (.divideDamage
        (.controller .this)
        (.source .this)
        (.targets 1 (.range 1 3) .all)
        3)).toTriggeredAbility? with
  | some ab => ab == TriggeredAbility.onEnterDealDividedDamage 3 3
  | none => false

-- Ragged Short Spear: enters, you may discard a card. If you do, draw two.
#guard
  match
    (Ability.triggered
      (.enter .this)
      (.sequence [
        .optional
          (.actionId 1 (.discard (.controller .this) 1)),
        .if (.happened (.actionWithId 1) .gameStart) [.draw (.controller .this) 2]])).toTriggeredAbility? with
  | some ab => ab == TriggeredAbility.onEnterMayDiscardDraw 2
  | none => false

#guard
  (TraditionalCardDefinition.card [
    .ability (.static (.addPowerToughness (.hostOf .this) (Value.int 2) (Value.int 0)))
  ]).toCardDef.staticAbilities == #[.equippedCreatureGets 2 0]

-- Snowslope Hunter: sacrifice another creature or artifact; exile top; your turn, once.
#guard
  let action : CardAction :=
    .sequence [
      .actionId 1 (.exile (.topOfLibrary (.controller .this))),
      .continuous
        [.canPlay (.controller .this) (.wasCreatedByAction 1)]
        (.sequence [.turnStart, .endOfPlayerTurn (.controller .this)])]
  action.toAbilityEffect == Effect.exileTopPlayUntilEndOfNextTurn

#guard
  !(CardAction.leftoverExileTopPlayUntilEndOfNextTurn?
    (.sequence [
      .actionId 1 (.exile (.topOfLibrary (.controller .this))),
      .continuous
        [.canPlay (.controller .this) (.wasCreatedByAction 1)]
        .endOfTurn]))

#guard
  match
    (Ability.abilityId 1
      (.activatedIf
        (.and
          (.turn (.controller .this))
          (.didNotHappen (.abilityWithIdActivated 1) .turnStart))
        [.sacrificeCount
          (.intersection [
            .not .this,
            .permanent,
            .union [.cardType .artifact, .cardType .creature]])
          1]
        (.sequence [
          .actionId 1 (.exile (.topOfLibrary (.controller .this))),
          .continuous
            [.canPlay (.controller .this) (.wasCreatedByAction 1)]
            (.sequence [.turnStart, .endOfPlayerTurn (.controller .this)])]))).toActivatedAbility? with
  | some ab =>
    ab.onlyDuringYourTurn &&
      ab.onceEachTurn &&
      ab.cost.sacrificeAnotherCreatureOrArtifact &&
      ab.effect == Effect.exileTopPlayUntilEndOfNextTurn
  | none => false

#guard
  match
    (Ability.activatedIf
      (.turn (.controller .this))
      [.life 3]
      (.keyword (.source .this) (.connive (.nat 1)))).toActivatedAbility? with
  | some ab =>
    ab.onlyDuringYourTurn &&
      !ab.onceEachTurn &&
      ab.cost.payLife == 3 &&
      ab.effect == Effect.connive
  | none => false

#guard
  match
    (Ability.activatedIf
      (.turn (.controller .this))
      [.life 3]
      (.keyword .this (.connive (.nat 1)))).toActivatedAbility? with
  | some ab => ab.effect != Effect.connive
  | none => true

#guard
  (TraditionalCardDefinition.card [
    .ability
      (.static
        (.addPowerToughness
          (.intersection [
            .permanent,
            .cardType .creature,
            .controlled (.opponent (.controller .this))]) (Value.int (-1)) (Value.int (-1))))
  ]).toCardDef.staticAbilities == #[.opponentsCreaturesGet (-1) (-1)]

-- Guardian of the Halls: put three +1/+1 counters on this creature.
#guard
  let action : CardAction := .putCounter (.source .this) .plusOnePlusOne 3
  action.toAbilityEffect == Effect.putPlusOnePlusOneOnSource 3

-- Quarrel: a creature you control deals damage equal to its power.
#guard Selector.toTargetKind
  (.intersection [
    .permanent,
    .cardType .creature,
    .controlled (.controller .this)])
  == .creatureYouControl

#guard Selector.toTargetKind
  (.intersection [
    .permanent,
    .cardType .creature,
    .controlled (.opponent (.controller .this))])
  == .oppCreature

#guard
  let action : CardAction :=
    .dealDamageEqualToPower
      (.target
        1
        (.intersection [
          .permanent,
          .cardType .creature,
          .controlled (.controller .this)]))
      (.target
        2
        (.intersection [
          .permanent,
          .cardType .creature,
          .controlled (.opponent (.controller .this))]))
  action.toEffect == Effect.creatureYouControlDealsPowerToOppCreature

-- Galion: attack, set another creature's base P/T.
#guard Selector.shape
  (.intersection [
    .not .this,
    .permanent,
    .cardType .creature,
    .controlled (.controller .this)]) |>.anotherCreatureYouControl

#guard
  match
    (Ability.triggered
      (.attack .this .all)
      (.continuous
        [.setBasePowerToughnessFrom
          (.targets
            1
            (.range 0 1)
            (.intersection [
              .not .this,
              .permanent,
              .cardType .creature,
              .controlled (.controller .this)]))
          (.source .this)]
        .endOfTurn)).toTriggeredAbility? with
  | some ab => ab == TriggeredAbility.onAttackSetOtherBasePT
  | none => false

-- Warg Tactics: destroy a flyer, or +1/+1, trample, and hexproof.
#guard Selector.shape
  (.intersection [
    .permanent,
    .cardType .creature,
    .keyword .flying]) |>.flyingCreature

#guard Selector.toTargetKind
  (.intersection [
    .permanent,
    .cardType .creature,
    .keyword .flying])
  == .creatureWithFlying

#guard
  let action : CardAction :=
    .destroy
      (.target
        1
        (.intersection [
          .permanent,
          .cardType .creature,
          .keyword .flying]))
  action.toEffect == Effect.destroyCreatureWithFlying

#guard
  let action : CardAction :=
    .sequence [
      .putCounter
        (.target
          1
          (.intersection [
            .permanent,
            .cardType .creature,
            .controlled (.controller .this)]))
        .plusOnePlusOne
        1,
      .continuous
        [.gainAbility (.targetReference 1) (.keyword .trample),
          .gainAbility (.targetReference 1) (.keyword .hexproof)]
        .endOfTurn]
  action.toEffect == Effect.plusOnePlusOneTrampleHexproof

#guard
  let action : CardAction :=
    .chooseMode [
      .destroy
        (.target
          1
          (.intersection [
            .permanent,
            .cardType .creature,
            .keyword .flying])),
      .sequence [
        .putCounter
          (.target
            2
            (.intersection [
              .permanent,
              .cardType .creature,
              .controlled (.controller .this)]))
          .plusOnePlusOne
          1,
        .continuous
          [.gainAbility (.targetReference 2) (.keyword .trample),
            .gainAbility (.targetReference 2) (.keyword .hexproof)]
          .endOfTurn]]
  CardAction.leftoverModes? action ==
    some #[Effect.destroyCreatureWithFlying, Effect.plusOnePlusOneTrampleHexproof]

-- Beorn's Hospitality: landfall +1/+1; become a Bear with lands P/T.
#guard Selector.shape
  (.intersection [
    .permanent,
    .cardType .land,
    .controlled (.controller .this)]) |>.landYouControl

#guard
  match
    (Ability.triggered
      (.enter
        (.intersection [
          .permanent,
          .cardType .land,
          .controlled (.controller .this)]))
      (.putCounter
        (.target
          1
          (.intersection [
            .permanent,
            .cardType .creature,
            .controlled (.controller .this)]))
        .plusOnePlusOne
        1)).toTriggeredAbility? with
  | some ab => ab == TriggeredAbility.onLandYouControlEntersPlusOnePlusOne
  | none => false

#guard
  let action : CardAction :=
    .continuous
      [.gainType .this .creature,
        .gainSubtype .this .bear,
        .setPowerToughnessEqualToCount
          .this
          (.intersection [
            .permanent,
            .cardType .land,
            .controlled (.controller .this)])]
      .endOfGame
  action.toAbilityEffect == Effect.becomeSubtypeWithLandsPT "Bear"

-- Woodland Weavemaster: another Elf enters +1/+1; tap for any color equal to power.
#guard Selector.shape
  (.intersection [
    .not .this,
    .permanent,
    .subtype .elf,
    .controlled (.controller .this)]) |>.anotherElfYouControl

#guard
  match
    (Ability.triggered
      (.enter
        (.intersection [
          .not .this,
          .permanent,
          .subtype .elf,
          .controlled (.controller .this)]))
      (.continuous [.addPowerToughness (.source .this) (Value.int 1) (Value.int 1)] .endOfTurn)).toTriggeredAbility? with
  | some ab => ab == TriggeredAbility.onAnotherElfYouControlEntersGets1
  | none => false

#guard
  (TraditionalCardDefinition.card [
    .ability (
      .activated
        [.tapSymbol]
        (.sequence [
          .actionId 1
          (.addManaAnyColorEqualToPower
            (.controller .this)
            (.controller .this)
            .this),
          .continuous
            [.forbid
              (.spendManaCreatedByAction 1
                (.not
                  (.or
                    (.castSpell (.subtype .elf))
                    (.activateAbility (.subtype .elf)))))]
            .endOfTurn]))
  ]).toCardDef.tapAddAnyColorEqualToPower

#guard
  let action : CardAction :=
    .continuous
      [.addPowerToughness
        (.target 1 (.intersection [.permanent, .cardType .creature])) (Value.int 3) (Value.int 3)]
      .endOfTurn
  action.toEffect == Effect.pump 3 3

#guard
  let action : CardAction :=
    .sequence [
      .draw (.controller .this) 2,
      .loseLife (.controller .this) 2]
  action.toEffect == Effect.drawAndLoseLife 2 2

#guard
  let action : CardAction :=
    .continuous
      [.addPowerToughness
        (.intersection [.permanent, .cardType .creature]) (Value.int (-4)) (Value.int (-4))]
      .endOfTurn
  action.toEffect == Effect.allCreaturesGet (-4) (-4)

#guard
  match
    (Ability.triggered
      (.enter .this)
      (.scry (.controller .this) 2)).toTriggeredAbility? with
  | some ab => ab == TriggeredAbility.onEnterScry 2
  | none => false

#guard
  match
    (Ability.triggered
      (.die .this)
      (.draw (.controller .this) 1)).toTriggeredAbility? with
  | some ab => ab == TriggeredAbility.onDiesDraw 1
  | none => false

#guard
  (TraditionalCardDefinition.card [
    .ability
      (.static
        (.setPowerToughnessEqualToCount
          .this
          (.intersection [
            .permanent,
            .cardType .land,
            .controlled (.controller .this)])))
  ]).toCardDef.staticAbilities == #[.powerToughnessEqualLandsYouControl]

#guard
  let action : CardAction :=
    .sequence [
      .continuous
        [.addPowerToughness
          (.target 1 (.intersection [.permanent, .cardType .creature])) (Value.int (-4)) (Value.int 0)]
        .endOfTurn,
      .draw (.controller .this) 1]
  action.toEffect == Effect.pumpThenDraw (-4) 0

#guard
  (TraditionalCardDefinition.card [
    .ability (
      .static
        (.if
          (.targetsIncludeAny
            .this
            (.intersection [
              .permanent,
              .cardType .creature,
              .attacking .all]))
          [.reduceCost .this [.mana [.generic 2]]]))
  ]).toCardDef.costReductionIfTargetAttacking == 2

#guard
  (TraditionalCardDefinition.card [
    .ability (
      .static
        (.if
          (.anySubtype (.controlled (.controller .this)) .villain)
          [.reduceCost .this [.mana [.generic 1]]]))
  ]).toCardDef.costReductionIfYouControl == some (1, "Villain")

#guard
  let action : CardAction :=
    .continuous [.increaseLandPlayLimit (.controller .this) (Value.nat 1)] .endOfTurn
  action.toEffect == Effect.playAdditionalLandThisTurn

#guard
  let s :=
    Selector.shape
      (.intersection [
        .not .this,
        .permanent,
        .subtype .elf,
        .controlled (.controller .this)])
  s.anotherSubtypeYouControl == some "Elf"

#guard
  (TraditionalCardDefinition.card [
    .ability (
      .static
        (.if
          (.any
            (.intersection [
              .not .this,
              .permanent,
              .subtype .elf,
              .controlled (.controller .this)]))
          [.increaseLandPlayLimit (.controller .this) (Value.nat 1)]))
  ]).toCardDef.extraLandIfOtherSubtype == some "Elf"

#guard
  match
    (Ability.triggered
      (.enter
        (.intersection [
          .permanent,
          .cardType .land,
          .controlled (.controller .this)]))
      (.sequence [
        .putCounter
          (.target
            1
            (.intersection [
              .permanent,
              .cardType .creature,
              .controlled (.controller .this)]))
          .plusOnePlusOne
          2,
        .continuous
          [.gainAbility (.targetReference 1) (.keyword .vigilance)]
          .endOfTurn])).toTriggeredAbility? with
  | some ab => ab == TriggeredAbility.onLandYouControlEntersPlusOneVigilance
  | none => false

#guard
  match
    (Ability.triggered
      (.enter .this)
      (.continuous
        [.addPowerToughness
          (.target 1 (.intersection [.permanent, .cardType .creature])) (Value.int 2) (Value.int 0)]
        .endOfTurn)).toTriggeredAbility? with
  | some ab => ab == TriggeredAbility.onEnterTargetGets 2 0
  | none => false

#guard
  match
    (Ability.triggered
      (.enter .this)
      (.putCounter
        (.target 1 (.intersection [.permanent, .cardType .creature]))
        .plusOnePlusOne
        1)).toTriggeredAbility? with
  | some ab => ab == TriggeredAbility.onEnterPlusOneOnCreature
  | none => false

#guard
  match
    (Ability.triggered
      (.attack .this .all)
      (.continuous
        [.gainAbility
          (.target
            1
            (.intersection [
              .permanent,
              .cardType .creature,
              .attacking .all]))
          (.keyword .firstStrike)]
        .endOfTurn)).toTriggeredAbility? with
  | some ab => ab == TriggeredAbility.onAttackTargetGainsKeywords Keyword.firstStrike
  | none => false

#guard
  match
    (Ability.triggered
      (.or (.enter .this) (.attack .this .all))
      (.divideDamage
        (.controller .this)
        .this
        (.targets 1 (.range 1 3) .all)
        3)).toTriggeredAbility? with
  | some ab => ab == TriggeredAbility.onEnterOrAttackDealDividedDamage 3 3
  | none => false

#guard
  match
    (Ability.triggered
      (.die .this)
      (.dealDamageEqualToPower
        .this
        (.target
          1
          (.intersection [
            .permanent,
            .cardType .creature,
            .controlled (.opponent (.controller .this))])))).toTriggeredAbility? with
  | some ab => ab == TriggeredAbility.onDiesDealDamageEqualToPowerToOppCreature
  | none => false

#guard
  match
    (Ability.triggered
      (.enter .this)
      (.sequence [
        .attach
          .this
          (.target
            1
            (.intersection [
              .permanent,
              .cardType .creature,
              .controlled (.controller .this)])),
        .untap (.targetReference 1)])).toTriggeredAbility? with
  | some ab => ab == TriggeredAbility.onEnterAttachThen PermanentAction.untap
  | none => false

#guard
  (TraditionalCardDefinition.card [
    .ability (.static (.forbid (.block .token .this)))
  ]).toCardDef.staticAbilities == #[.cantBeBlockedByTokens]

#guard
  let action : CardAction :=
    .sequence [.draw (.controller .this) 1, .discard (.controller .this) 1]
  action.toAbilityEffect == Effect.abilityDrawThenDiscard 1

#guard
  let action : CardAction := .returnToHand .this
  action.toAbilityEffect == Effect.returnFromGraveyardToHand

#guard
  (TraditionalCardDefinition.card [
    .type .enchantment,
    .ability (.static (.addPowerToughness (.hostOf .this) (Value.int 3) (Value.int 3)))
  ]).toCardDef.staticAbilities == #[.enchantedCreatureGets 3 3]

#guard
  let action : CardAction := .draw (.controller .this) 2
  action.toAbilityEffect == Effect.abilityDraw 2

#guard
  (TraditionalCardDefinition.card [
    .ability (.activated [.sacrifice .this] (.draw (.controller .this) 2))
  ]).toCardDef.activatedAbilities[0]!.cost.sacrificeSource

#guard Selector.basicLandInLibrary
  (.intersection [.inLibrary, .cardType .land, .supertype .basic])

#guard Selector.includesInLibrary .inLibrary
#guard !Selector.includesInLibrary .inHand
#guard !Selector.includesInLibrary .inExile
#guard Selector.inHand != .inExile
#guard (Selector.shape .inHand) == {}
#guard (Selector.shape .inExile) == {}

#guard
  let action : CardAction :=
    .searchLibraryThenShuffle
      (.controller .this)
      [
        .defineVariable 1
          (.selected
            (.controller .this)
            (.range 1 1)
            (.intersection [
              .inLibrary,
              .cardType .land,
              .supertype .basic])),
        .reveal (.variable 1),
        .returnToHand (.variable 1)]
  action.toAbilityEffect == Effect.searchBasicLandToHand

#guard
  let action : CardAction :=
    .searchLibraryThenShuffle
      (.controller .this)
      [
        .putOntoBattlefieldInState
          (.selected
            (.controller .this)
            (.range 1 1)
            (.intersection [.inLibrary, .cardType .land, .supertype .basic]))
          [.tapped]]
  action.toAbilityEffect == Effect.searchBasicLandTapped

#guard
  match
    (Ability.triggered
      (.enter .this)
      (.searchLibraryThenShuffle
        (.controller .this)
        [
          .putOntoBattlefield
            (.selected
              (.controller .this)
              (.range 1 1)
              (.intersection [.inLibrary, .subtype .forest]))])).toTriggeredAbility? with
  | some ab => ab == TriggeredAbility.onEnterSearchForest
  | none => false

#guard
  match
    (Ability.triggered
      (.enter .this)
      (.searchLibraryThenShuffle
        (.controller .this)
        [
          .defineVariable 1
            (.selected
              (.controller .this)
              (.range 1 1)
              (.intersection [
                .inLibrary,
                .cardType .land,
                .supertype .basic])),
          .reveal (.variable 1),
          .returnToHand (.variable 1)])).toTriggeredAbility? with
  | some ab => ab == TriggeredAbility.onEnterSearchBasicToHand
  | none => false

-- Old Thrush: hold the found land out of the shuffle, then put it on top.
#guard
  match
    (Ability.triggered
      (.enter .this)
      (.sequence [
        .gainLife (.controller .this) 2,
        .optional
          (.sequence [
            .searchLibraryThenShuffle
              (.controller .this)
              [
                .defineVariable 1
                  (.selected
                    (.controller .this)
                    (.range 1 1)
                    (.intersection [
                      .inLibrary,
                      .cardType .land,
                      .supertype .basic])),
                .reveal (.variable 1),
                .holdOutInLibrary (.variable 1)],
            .putOnTopOfLibrary (.variable 1)])])).toTriggeredAbility? with
  | some ab => ab == TriggeredAbility.onEnterGainLifeSearchBasicOnTop 2
  | none => false

#guard
  (Ability.triggered
    (.enter .this)
    (.sequence [
      .gainLife (.controller .this) 2,
      .optional
        (.searchLibraryThenShuffle
          (.controller .this)
          [
            .defineVariable 1
              (.selected
                (.controller .this)
                (.range 1 1)
                (.intersection [
                  .inLibrary,
                  .cardType .land,
                  .supertype .basic])),
            .reveal (.variable 1),
            .putOnTopOfLibrary (.variable 1)])])).toTriggeredAbility?.isNone

#guard
  (Ability.triggered
    (.enter .this)
    (.sequence [
      .gainLife (.controller .this) 2,
      .optional
        (.sequence [
          .searchLibraryThenShuffle
            (.controller .this)
            [
              .defineVariable 1
                (.selected
                  (.controller .this)
                  (.range 1 1)
                  (.intersection [
                    .inLibrary,
                    .cardType .land,
                    .supertype .basic])),
              .reveal (.variable 1)],
          .putOnTopOfLibrary (.variable 1)])])).toTriggeredAbility?.isNone

-- Little Bear: flash; enter, untap another creature you control, +1/+1 if Bear.
#guard Selector.toTargetKind
  (.intersection [
    .not .this,
    .permanent,
    .cardType .creature,
    .controlled (.controller .this)])
  == .anotherCreatureYouControl

#guard
  match
    (Ability.triggered
      (.enter .this)
      (.sequence [
        .untap
          (.target
            1
            (.intersection [
              .not .this,
              .permanent,
              .cardType .creature,
              .controlled (.controller .this)])),
        .if
          (.anySubtype (.targetReference 1) .bear)
          [.putCounter (.targetReference 1) .plusOnePlusOne 1]])).toTriggeredAbility? with
  | some ab => ab == TriggeredAbility.onEnterUntapOtherPlusOneIfSubtype "Bear"
  | none => false

-- Wakandan Royal Guard: extra counters only if the target is another Hero,
-- not when the source targets itself.
#guard
  match
    (Ability.triggered
      (.enter .this)
      (.sequence [
        .putCounter
          (.target 1 (.intersection [.permanent, .cardType .creature]))
          .plusOnePlusOne
          1,
        .if
          (.anySubtype (.intersection [.targetReference 1, .not .this]) .hero)
          [.putCounter (.targetReference 1) .plusOnePlusOne 1]])).toTriggeredAbility? with
  | some ab => ab == TriggeredAbility.onEnterPlusOneOrTwoIfAnotherHero
  | none => false

#guard
  match
    (Ability.triggered
      (.enter .this)
      (.sequence [
        .putCounter
          (.target 1 (.intersection [.permanent, .cardType .creature]))
          .plusOnePlusOne
          1,
        .if
          (.anySubtype (.intersection [.not .this, .targetReference 1]) .hero)
          [.putCounter (.targetReference 1) .plusOnePlusOne 1]])).toTriggeredAbility? with
  | some ab => ab == TriggeredAbility.onEnterPlusOneOrTwoIfAnotherHero
  | none => false

#guard
  (Ability.triggered
    (.enter .this)
    (.sequence [
      .putCounter
        (.target 1 (.intersection [.permanent, .cardType .creature]))
        .plusOnePlusOne
        1,
      .if
        (.anySubtype (.targetReference 1) .hero)
        [.putCounter (.targetReference 1) .plusOnePlusOne 1]])).toTriggeredAbility?.isNone

#guard
  (Ability.triggered
    (.enter .this)
    (.sequence [
      .putCounter
        (.target 1 (.intersection [.permanent, .cardType .creature]))
        .plusOnePlusOne
        1,
      .if
        (.anySubtype (.not .this) .hero)
        [.putCounter (.targetReference 1) .plusOnePlusOne 1]])).toTriggeredAbility?.isNone

-- Dual land: enters tapped; tap-add one of two colors; counters on a typed creature.
#guard
  (TraditionalCardDefinition.card [
    .ability (
      .static
        (.replace
          (.enter .this)
          [.putOntoBattlefieldInState .this [.tapped]]))
  ]).toCardDef.entersTapped

#guard
  (TraditionalCardDefinition.card [
    .ability (
      .activated
        [.tapSymbol]
        (.playerSelectAction
          (.controller .this)
          (.range 1 1)
          [
            .addMana (.controller .this) [.mono .green],
            .addMana (.controller .this) [.mono .blue]]))
  ]).toCardDef.tapAddOneOf == #[.colored .green, .colored .blue]

#guard
  let action : CardAction :=
    .addMana (.controller .this) [.mono .black, .mono .red]
  action.toAbilityEffect == Effect.addMana #[.colored .black, .colored .red]

#guard Selector.includedSubtypes
  (.union [.subtype .goblin, .subtype .orc]) == ["Goblin", "Orc"]

#guard
  let action : CardAction :=
    .putCounter
      (.target
        1
        (.intersection [
          .permanent,
          .cardType .creature,
          .subtype .elf,
          .controlled (.controller .this)]))
      .plusOnePlusOne
      2
  action.toAbilityEffect == Effect.plusOneOnTarget 2 #["Elf"]

#guard
  let action : CardAction :=
    .putCounter
      (.target
        1
        (.intersection [
          .permanent,
          .cardType .creature,
          .union [.subtype .goblin, .subtype .orc],
          .controlled (.controller .this)]))
      .plusOnePlusOne
      2
  action.toAbilityEffect == Effect.plusOneOnTarget 2 #["Goblin", "Orc"]

#guard
  match
    (Ability.activatedIf
      (.timeToCastSorcery (.controller .this))
      [
        .mana [.generic 2, .mono .green, .mono .blue],
        .tapSymbol,
        .sacrifice .this]
      (.putCounter
        (.target
          1
          (.intersection [
            .permanent,
            .cardType .creature,
            .subtype .elf,
            .controlled (.controller .this)]))
        .plusOnePlusOne
        2)).toActivatedAbility? with
  | some ab =>
    ab.onlyAsSorcery &&
      ab.cost.tap &&
      ab.cost.sacrificeSource &&
      ab.cost.mana == ManaCost.ofGenericAndColors 2 [.green, .blue] &&
      ab.effect == Effect.plusOneOnTarget 2 #["Elf"]
  | none => false

#guard
  match
    (Ability.activated
      [.mana [.generic 4], .discard .this]
      (.searchLibraryThenShuffle
        (.controller .this)
        [
          .defineVariable 1
            (.selected
              (.controller .this)
              (.range 1 1)
              (.intersection [.inLibrary, .subtype .halfling])),
          .reveal (.variable 1),
          .returnToHand (.variable 1)])).toActivatedAbility? with
  | some ab =>
    ab.cost.discardSource &&
      ab.activateFromHand &&
      ab.cost.mana == ManaCost.ofGeneric 4 &&
      ab.effect == Effect.searchLandTypeToHand "Halfling"
  | none => false

#guard
  (TraditionalCardDefinition.card [
    .ability (.activated [.tapSymbol] (.addMana (.controller .this) [.mono .green]))
  ]).toCardDef.tapAddMana == #[.colored .green]

#guard
  let action : CardAction := .dealDamage .this (.target 1 .all) (.nat 3)
  action.toEffect == Effect.dealDamage 3

#guard
  Selector.toTargetKind
    (.union [.cardType .artifact, .cardType .enchantment])
  == .artifactOrEnchantment

#guard
  let action : CardAction :=
    .destroy
      (.target 1 (.union [.cardType .artifact, .cardType .enchantment]))
  action.toAbilityEffect == Effect.destroyTargetArtifactOrEnchantment

#guard
  let action : CardAction := .destroy (.target 1 .permanent)
  action.toAbilityEffect == Effect.destroyTargetPermanent

#guard
  let action : CardAction :=
    .addManaAnyColor
      (.controller .this)
      (.controller .this)
      1
  action.toAbilityEffect == Effect.addAnyColor

#guard
  match
    (Ability.triggered
      (.enter .this)
      (.sequence [
        .actionId 1 (.exile (.topOfLibrary (.controller .this))),
        .continuous
          [.canPlay (.controller .this) (.wasCreatedByAction 1)]
          (.sequence [.turnStart, .endOfPlayerTurn (.controller .this)])])).toTriggeredAbility? with
  | some ab => ab == TriggeredAbility.onEnterExileTop
  | none => false

#guard
  match
    (Ability.triggered
      (.enter
        (.intersection [
          .permanent,
          .cardType .artifact,
          .controlled (.controller .this)]))
      (.draw (.controller .this) 1)).toTriggeredAbility? with
  | some ab => ab == TriggeredAbility.onArtifactYouControlEntersDraw
  | none => false

#guard
  match
    (Ability.triggered
      (.enter
        (.intersection [
          .not .this,
          .permanent,
          .cardType .artifact,
          .controlled (.controller .this)]))
      (.putCounter (.source .this) .plusOnePlusOne 1)).toTriggeredAbility? with
  | some ab => ab == TriggeredAbility.onAnotherArtifactEntersPlusOne
  | none => false

#guard
  match
    (Ability.triggered
      (.attack .this .all)
      (.if
        (.any
          (.intersection [
            .permanent,
            .cardType .creature,
            .controlled (.controller .this),
            .powerAtLeast (Value.int 4)]))
        [.continuous [.addPowerToughness (.source .this) (Value.int 2) (Value.int 2)] .endOfTurn])).toTriggeredAbility? with
  | some ab => ab == TriggeredAbility.onAttackFerociousSourceGets 2 2
  | none => false

#guard
  match
    (Ability.triggered
      (.combatStart (.controller .this))
      (.if
        (.any
          (.intersection [
            .permanent,
            .cardType .creature,
            .controlled (.controller .this),
            .powerAtLeast (Value.int 4)]))
        [.putCounter (.source .this) .plusOnePlusOne 1])).toTriggeredAbility? with
  | some ab => ab == TriggeredAbility.onYourBeginCombatFerociousPlusOne
  | none => false

#guard
  (Ability.triggered
    (.combatStart (.opponent (.controller .this)))
    (.if
      (.any
        (.intersection [
          .permanent,
          .cardType .creature,
          .controlled (.controller .this),
          .powerAtLeast (Value.int 4)]))
      [.putCounter (.source .this) .plusOnePlusOne 1])).toTriggeredAbility?.isNone

#guard
  (Ability.triggered
    (.combatStart (.controller .this))
    (.putCounter (.source .this) .plusOnePlusOne 1)).toTriggeredAbility?.isNone

#guard
  match
    (Ability.triggered
      (.attack .this .all)
      (.continuous
        [
          .addPowerToughness
            (.target
              1
              (.intersection [
                .not .this,
                .permanent,
                .cardType .creature,
                .controlled (.controller .this)])) (Value.int 2) (Value.int 0),
          .gainAbility (.targetReference 1) (.keyword .trample)]
        .endOfTurn)).toTriggeredAbility? with
  | some ab => ab == TriggeredAbility.onAttackOtherGets2AndTrample
  | none => false

#guard
  match
    (Ability.triggered
      (.enter .this)
      (.continuous
        [
          .addPowerToughness
            (.intersection [
              .permanent,
              .cardType .creature,
              .controlled (.controller .this)]) (Value.int 1) (Value.int 0),
          .gainAbility
            (.intersection [
              .permanent,
              .cardType .creature,
              .controlled (.controller .this)])
            (.keyword .firstStrike)]
        .endOfTurn)).toTriggeredAbility? with
  | some ab => ab == TriggeredAbility.onEnterCreaturesYouControlGetAndFirstStrike 1
  | none => false

#guard
  match
    (Ability.triggered
      (.enter .this)
      (.forEachVariable 1 .player [
        .sacrifice
          (.selected
            (.variable 1)
            (.range 1 1)
            (.intersection [
              .permanent,
              .cardType .creature,
              .controlled (.variable 1)]))])).toTriggeredAbility? with
  | some ab => ab == TriggeredAbility.onEnterEachPlayerSacrificesCreature
  | none => false

-- Sacrifice an artifact is `selected` 1, not every artifact you control.
#guard
  CardAction.leftoverMaySacArtifactOrDiscardDraw?
    (.sequence [
      .optional
        (.actionId 1
          (.playerSelectAction
            (.controller .this)
            (.range 1 1)
            [
              .sacrifice
                (.selected
                  (.controller .this)
                  (.range 1 1)
                  (.intersection [
                    .permanent,
                    .cardType .artifact,
                    .controlled (.controller .this)])),
              .discard (.controller .this) 1])),
      .if (.happened (.actionWithId 1) .gameStart) [.draw (.controller .this) 1]]) == some 1

#guard
  CardAction.leftoverMaySacArtifactOrDiscardDraw?
    (.sequence [
      .optional
        (.actionId 1
          (.playerSelectAction
            (.controller .this)
            (.range 1 1)
            [
              .sacrifice
                (.intersection [
                  .permanent,
                  .cardType .artifact,
                  .controlled (.controller .this)]),
              .discard (.controller .this) 1])),
      .if (.happened (.actionWithId 1) .gameStart) [.draw (.controller .this) 1]]) |>.isNone

#guard
  match
    (Ability.triggered
      (.block .all .this)
      (.dealDamage .this (.blocking .this) (.nat 1))).toTriggeredAbility? with
  | some ab => ab == TriggeredAbility.onBecomesBlockedDeal1ToBlockers
  | none => false

#guard
  match
    (Ability.triggered
      (.castSpell
        (.intersection [
          .union [.cardType .instant, .cardType .sorcery],
          .controlled (.controller .this)]))
      (.dealDamage .this (.opponent (.controller .this)) (.nat 2))).toTriggeredAbility? with
  | some ab => ab == TriggeredAbility.onCastInstantOrSorceryDealDamageToEachOpponent 2
  | none => false

#guard
  (Ability.triggered
    (.castSpell (.union [.cardType .instant, .cardType .sorcery]))
    (.dealDamage .this (.opponent (.controller .this)) (.nat 2))).toTriggeredAbility?.isNone

#guard
  match
    (Ability.triggered
      (.enter .this)
      (.attach
        .this
        (.target
          1
          (.intersection [
            .permanent,
            .cardType .creature,
            .controlled (.controller .this),
            .supertype .legendary])))).toTriggeredAbility? with
  | some ab => ab == TriggeredAbility.onEnterAttachToLegendary
  | none => false

#guard
  (TraditionalCardDefinition.card [
    .type .artifact,
    .ability (.static (.gainAbility (.hostOf .this) (.keyword .indestructible)))
  ]).toCardDef.staticAbilities == #[.equippedCreatureHasKeywords Keyword.indestructible]

#guard
  (TraditionalCardDefinition.card [
    .type .enchantment,
    .ability (.static (.addPowerToughness (.hostOf .this) (Value.int 1) (Value.int 0))),
    .ability (.static (.gainAbility (.hostOf .this) (.keyword .haste)))
  ]).toCardDef.staticAbilities ==
    #[.enchantedCreatureGetsAndHas 1 0 Keyword.haste]

#guard
  match
    (Ability.keywordWithCost (.typecycling [] [] [.mountain]) [.mana [.generic 1]]).toActivatedAbility? with
  | some ab =>
    ab.activateFromHand &&
      ab.cost.discardSource &&
      ab.effect == Effect.searchLandTypeToHand "Mountain"
  | none => false

#guard Selector.toTargetKind
  (.intersection [
    .permanent,
    .union [.cardType .artifact, .cardType .land]])
  == .artifactOrLand

#guard Selector.toTargetKind
  (.intersection [
    .permanent,
    .cardType .creature,
    .powerAtLeast (Value.int 4)])
  == .creaturePowerAtLeast 4

#guard
  let action : CardAction :=
    .sequence [
      .tap
        (.target 1 (.intersection [.permanent, .cardType .creature])),
      .scry (.controller .this) 1,
      .draw (.controller .this) 1]
  action.toEffect == Effect.tapScryDraw 1 1

#guard
  let action : CardAction :=
    .sequence [
      .returnToHand (.target 1 .spell),
      .draw (.controller .this) 1]
  action.toEffect == Effect.returnSpellDraw

#guard
  let action : CardAction :=
    .sequence [
      .destroy
        (.target
          1
          (.intersection [
            .permanent,
            .union [.cardType .artifact, .cardType .enchantment]])),
      .gainLife (.controller .this) 2]
  action.toEffect == Effect.destroyArtifactOrEnchantmentGainLife 2

#guard
  let action : CardAction :=
    .sequence [
      .destroy
        (.target
          1
          (.intersection [
            .permanent,
            .union [.cardType .artifact, .cardType .land]])),
      .continuous
        [.forbid (.block (.not (.keyword .flying)) .all)]
        .endOfTurn]
  action.toEffect == Effect.destroyArtifactOrLandNonflyersCantBlock

#guard
  let action : CardAction :=
    .destroy
      (.target
        1
        (.intersection [
          .permanent,
          .cardType .creature,
          .powerAtLeast (Value.int 4)]))
  action.toEffect == Effect.destroyCreaturePowerAtLeast 4

#guard
  let action : CardAction :=
    .continuous
      [
        .gainType
          (.target 1 (.intersection [.permanent, .cardType .creature]))
          .artifact,
        .gainAbility (.targetReference 1) (.keyword .indestructible)]
      .endOfTurn
  action.toEffect == Effect.becomeArtifactGainIndestructible

#guard
  let action : CardAction :=
    .sequence [
      .putCounter
        (.target 1 (.intersection [.permanent, .cardType .creature]))
        .plusOnePlusOne
        1,
      .continuous
        [
          .gainAbility (.targetReference 1) (.keyword .lifelink),
          .gainAbility (.targetReference 1) (.keyword .indestructible)]
        .endOfTurn]
  action.toEffect == Effect.plusOneLifelinkIndestructible

#guard
  let action : CardAction :=
    .continuous
      [
        .addPowerToughness
          (.target
            1
            (.intersection [
              .not .this,
              .permanent,
              .cardType .creature,
              .controlled (.controller .this)])) (Value.int 2) (Value.int 0),
        .gainAbility (.targetReference 1) (.keyword .hexproof)]
      .endOfTurn
  action.toAbilityEffect == Effect.anotherYouControlGetsAndGrant 2 0 Keyword.hexproof

#guard
  match
    (Ability.triggered
      (.attackSimultaneously
        (.intersection [
          .permanent,
          .cardType .creature,
          .controlled (.controller .this)])
        .all
        [])
      (.draw (.controller .this) 1)).toTriggeredAbility? with
  | some ab => ab == TriggeredAbility.onYouAttackDraw
  | none => false

#guard
  match
    (Ability.triggered
      (.attackSimultaneously
        (.intersection [
          .permanent,
          .cardType .creature,
          .subtype .merfolk,
          .controlled (.controller .this)])
        .player
        [])
      (.draw (.controller .this) 1)).toTriggeredAbility? with
  | some ab => ab == TriggeredAbility.onWatch Effect.watchMerfolkAttackDraw
  | none => false

#guard
  (Ability.triggered
    (.attackSimultaneously
      (.intersection [
        .permanent,
        .cardType .creature,
        .subtype .merfolk,
        .controlled (.controller .this)])
      .all
      [])
    (.draw (.controller .this) 1)).toTriggeredAbility?.isNone

#guard
  (Ability.triggered
    (.attackSimultaneously
      (.intersection [
        .permanent,
        .cardType .creature,
        .controlled (.controller .this)])
      .player
      [])
    (.draw (.controller .this) 1)).toTriggeredAbility?.isNone

#guard
  match
    (Ability.triggered
      (.attackSimultaneously
        (.intersection [
          .permanent,
          .cardType .creature,
          .controlled (.controller .this)])
        .player
        [.countAtLeast 2])
      (.continuous
        [
          .gainAbility
            (.target
              1
              (.intersection [
                .permanent,
                .cardType .creature,
                .attacking .all,
                .not (.keyword .flying)]))
            (.keyword .flying)]
        .endOfTurn)).toTriggeredAbility? with
  | some ab => ab == TriggeredAbility.onAttackWithTwoOrMoreGrantFlying
  | none => false

#guard
  (Ability.triggered
    (.attackSimultaneously
      (.intersection [
        .permanent,
        .cardType .creature,
        .controlled (.controller .this)])
      .player
      [])
    (.continuous
      [
        .gainAbility
          (.target
            1
            (.intersection [
              .permanent,
              .cardType .creature,
              .attacking .all,
              .not (.keyword .flying)]))
          (.keyword .flying)]
      .endOfTurn)).toTriggeredAbility?.isNone

#guard
  match
    (Ability.triggered
      (.enter .this)
      (.continuous
        [.gainAbility (.hostOf .this) (.keyword .firstStrike)]
        .endOfTurn)).toTriggeredAbility? with
  | some ab => ab == TriggeredAbility.onEnterEnchanted (.grantKeywords Keyword.firstStrike)
  | none => false

#guard
  match
    (Ability.triggered
      (.enter .this)
      (.sequence [
        .attach
          .this
          (.target
            1
            (.intersection [
              .permanent,
              .cardType .creature,
              .controlled (.controller .this)])),
        .continuous
          [.gainAbility (.hostOf .this) (.keyword .indestructible)]
          .endOfTurn])).toTriggeredAbility? with
  | some ab =>
    ab == TriggeredAbility.onEnterAttachThen (.grantKeywords Keyword.indestructible)
  | none => false

#guard
  (TraditionalCardDefinition.card [
    .ability
      (.static
        (.addPowerToughness
          (.intersection [
            .not .this,
            .permanent,
            .cardType .creature,
            .controlled (.controller .this)]) (Value.int 1) (Value.int 1)))
  ]).toCardDef.staticAbilities == #[.otherCreaturesGet #[] 1 1]

#guard
  match
    (Ability.activatedIf
      (.timeToCastSorcery (.controller .this))
      [.mana [.generic 1]]
      (.attach
        .this
        (.target
          1
          (.intersection [
            .permanent,
            .cardType .creature,
            .controlled (.controller .this),
            .subtype .human])))).toActivatedAbility? with
  | some ab =>
    ab.onlyAsSorcery &&
      ab.equipSubtype == some "Human" &&
      ab.effect == Effect.attachToTargetCreatureYouControl
  | none => false

#guard
  match
    (Ability.activated
      [.mana [.generic 2], .discard .this]
      (.searchLibraryThenShuffle
        (.controller .this)
        [
          .defineVariable 1
            (.selected
              (.controller .this)
              (.range 1 1)
              (.intersection [
                .inLibrary,
                .cardType .land,
                .supertype .basic])),
          .reveal (.variable 1),
          .returnToHand (.variable 1)])).toActivatedAbility? with
  | some ab =>
    ab.activateFromHand &&
      ab.cost.discardSource &&
      ab.effect == Effect.searchLandTypeToHand "Basic land"
  | none => false

#guard
  match
    (Ability.triggered
      (.attack .this .all)
      (.if
        (.any
          (.intersection [
            .permanent,
            .cardType .creature,
            .controlled (.controller .this),
            .powerAtLeast (Value.int 4)]))
        [
          .continuous
            [
              .addPowerToughness (.source .this) (Value.int 1) (Value.int 0),
              .gainAbility
                (.intersection [
                  .permanent,
                  .cardType .creature,
                  .controlled (.controller .this)])
                (.keyword .trample)]
            .endOfTurn])).toTriggeredAbility? with
  | some ab => ab == TriggeredAbility.onAttackFerociousSourceGetsAndTeamTrample 1
  | none => false

#guard
  CardAction.leftoverGrantVigilanceUnblockable?
    (.sequence [
      .continuous
        [
          .gainAbility
            (.target 1 (.intersection [.permanent, .cardType .creature]))
            (.keyword .vigilance),
          .forbid
            (.block
              .any
              (.targetReference 1))]
        .endOfTurn,
      .draw (.controller .this) 1]) == true

#guard
  CardAction.leftoverPumpThenExileTopPlay?
    (.sequence [
      .continuous
        [
          .addPowerToughness
            (.target 1 (.intersection [.permanent, .cardType .creature])) (Value.int 3) (Value.int 1)]
        .endOfTurn,
      .actionId 1 (.exile (.topOfLibrary (.controller .this))),
      .continuous
        [.canPlay (.controller .this) (.wasCreatedByAction 1)]
        (.sequence [.turnStart, .endOfPlayerTurn (.controller .this)])]) == some (3, 1)

-- Exile then return tapped under owner's control (Gandalf / Mighty Thor).
#guard
  CardAction.leftoverExileThenReturnTapped?
    (.sequence [
      .actionId 1
        (.exile
          (.targets
            1
            (.range 0 3)
            (.intersection [
              .permanent,
              .cardType .land,
              .controlled (.controller .this)]))),
      .putOntoBattlefieldInState
        (.wasCreatedByAction 1)
        [
          .tapped,
          .controlled (.owner (.wasCreatedByAction 1))]])
  |>.isSome

#guard
  CardAction.leftoverExileThenReturnTapped?
    (.sequence [
      .actionId 1
        (.exile
          (.targets
            1
            (.range 0 3)
            (.intersection [
              .permanent,
              .cardType .land,
              .controlled (.controller .this)]))),
      .putOntoBattlefieldInState (.wasCreatedByAction 1) [.tapped]])
  |>.isNone

#guard
  CardAction.leftoverExileThenReturnTapped?
    (.sequence [
      .actionId 1 (.exile (.targets 1 (.range 0 3) .permanent)),
      .putOntoBattlefieldInState
        (.wasCreatedByAction 1)
        [
          .tapped,
          .controlled (.controller .this)]])
  |>.isNone

#guard
  match
    (Ability.triggered
      (.enter .this)
      (.sequence [
        .actionId 1
          (.exile
            (.targets
              1
              (.range 0 3)
              (.intersection [
                .permanent,
                .cardType .land,
                .controlled (.controller .this)]))),
        .putOntoBattlefieldInState
          (.wasCreatedByAction 1)
          [
            .tapped,
            .controlled (.owner (.wasCreatedByAction 1))]])).toTriggeredAbility? with
  | some ab => ab == TriggeredAbility.onEnterExileLandsThenReturnTapped
  | none => false

#guard
  match
    (Ability.triggered (.enter .this) (.keyword (.controller .this) .recruit)).toTriggeredAbility? with
  | some ab => ab == TriggeredAbility.onEnterRecruit
  | none => false

#guard
  (Ability.triggered (.enter .this) (.keyword .all .recruit)).toTriggeredAbility?.isNone

#guard
  match
    (Ability.triggered (.enter .this) (.keyword (.source .this) (.connive (.nat 1)))).toTriggeredAbility? with
  | some ab => ab == TriggeredAbility.onEnterConnive
  | none => false

#guard
  (Ability.triggered (.enter .this) (.keyword .this (.connive (.nat 1)))).toTriggeredAbility?.isNone

#guard
  (Ability.triggered (.enter .this) (.keyword (.controller .this) (.connive (.nat 1)))).toTriggeredAbility?.isNone

#guard
  match
    (Ability.triggered (.attack .this .all) (.keyword (.source .this) (.connive (.nat 1)))).toTriggeredAbility? with
  | some ab => ab == TriggeredAbility.onAttackConnive
  | none => false

#guard
  (Ability.triggered (.attack .this .all) (.keyword .this (.connive (.nat 1)))).toTriggeredAbility?.isNone

#guard
  match
    (Ability.triggered
      (.combatStart (.controller .this))
      (.keyword
        (.target
          1
          (.intersection [
            .permanent,
            .cardType .creature,
            .controlled (.controller .this)]))
        (.connive (.nat 1)))).toTriggeredAbility? with
  | some ab => ab == TriggeredAbility.onCombatTargetYouControlConnives
  | none => false

#guard
  (Ability.triggered
    (.combatStart (.opponent (.controller .this)))
    (.keyword
      (.target
        1
        (.intersection [
          .permanent,
          .cardType .creature,
          .controlled (.controller .this)]))
      (.connive (.nat 1)))).toTriggeredAbility?.isNone

#guard
  match
    (Ability.triggered
      (.attack
        (.hostOf
          (.intersection [
            .permanent,
            .subtype .equipment,
            .controlled (.controller .this)]))
        .all)
      (.keyword
        (.hostOf
          (.intersection [
            .permanent,
            .subtype .equipment,
            .controlled (.controller .this)]))
        (.connive (.nat 1)))).toTriggeredAbility? with
  | some ab => ab == TriggeredAbility.onEquippedCreatureYouControlAttacksConnive
  | none => false

#guard
  match
    (Ability.triggered
      (.ordinal 2 .turnStart (.draw (.controller .this) .all))
      (.createTokens (.controller .this) 1 [
        .type .creature, .subtype .villain, .colorIndicator [.black],
        .power 2, .toughness 1, .ability (.keyword .menace)])).toTriggeredAbility? with
  | some ab => ab == TriggeredAbility.onYouDrawSecondCreateTokens .villain21menace
  | none => false

#guard
  match
    (Ability.triggered
      (.ordinal 2 .turnStart (.draw (.controller .this) .all))
      (.sequence [
        .loseLife (.opponent (.controller .this)) 1,
        .gainLife (.controller .this) 1])).toTriggeredAbility? with
  | some ab => ab == TriggeredAbility.onResource Effect.resourceSecondDrawDrain
  | none => false

#guard
  match
    (Ability.triggered
      (.enter
        (.intersection [
          .not .this,
          .permanent,
          .subtype .villain,
          .controlled (.controller .this)]))
      (.attach
        (.targets
          1
          (.range 0 1)
          (.intersection [
            .permanent,
            .subtype .equipment,
            .controlled (.controller .this)]))
        (.target
          2
          (.intersection [
            .permanent,
            .cardType .creature,
            .controlled (.controller .this)])))).toTriggeredAbility? with
  | some ab => ab == TriggeredAbility.onWatch Effect.watchVillainAttachEquipment
  | none => false

#guard CardAction.toEffect (.putIntoLibraryFromTop .this 1) == Effect.putOnTopOrBottom

#guard
  !CardAction.leftoverOwnerPutsLibraryThenConnive?
    (.sequence [
      .playerSelectAction (.owner (.targetReference 1)) (.range 1 1)
        [.putOnTopOfLibrary
          (.target
            1
            (.intersection [
              .permanent,
              .cardType .creature,
              .controlled (.opponent (.controller .this))])),
          .putOnBottomOfLibrary (.targetReference 1)],
      .keyword
        (.targets
          2
          (.range 0 1)
          (.intersection [
            .permanent,
            .cardType .creature,
            .controlled (.controller .this)]))
        (.connive (.nat 1))])

#guard
  CardAction.leftoverOwnerPutsLibraryThenConnive?
    (.sequence [
      .playerSelectAction (.owner (.targetReference 1)) (.range 1 1)
        [.putIntoLibraryFromTop
          (.target
            1
            (.intersection [
              .permanent,
              .cardType .creature,
              .controlled (.opponent (.controller .this))]))
          2,
          .putOnBottomOfLibrary (.targetReference 1)],
      .keyword
        (.targets
          2
          (.range 0 1)
          (.intersection [
            .permanent,
            .cardType .creature,
            .controlled (.controller .this)]))
        (.connive (.nat 1))])

#guard
  CardAction.toEffect
    (.sequence [
      .playerSelectAction (.owner (.targetReference 1)) (.range 1 1)
        [.putIntoLibraryFromTop
          (.target
            1
            (.intersection [
              .permanent,
              .cardType .creature,
              .controlled (.opponent (.controller .this))]))
          2,
          .putOnBottomOfLibrary (.targetReference 1)],
      .keyword
        (.targets
          2
          (.range 0 1)
          (.intersection [
            .permanent,
            .cardType .creature,
            .controlled (.controller .this)]))
        (.connive (.nat 1))]) == Effect.ownerPutsLibraryThenConnive

#guard
  match
    (Ability.triggered (.die .this) (.keyword (.controller .this) .recruit)).toTriggeredAbility? with
  | some ab => ab == TriggeredAbility.onDiesRecruit
  | none => false

#guard
  match
    (Ability.triggered
      (.enter .this)
      (.keyword (.controller .this) (.amass .goblin (.nat 1)))).toTriggeredAbility? with
  | some ab => ab == TriggeredAbility.onEnterAmassGoblins 1
  | none => false

#guard
  match
    (Ability.triggered
      (.die .this)
      (.keyword (.controller .this) (.amass .goblin (.nat 4)))).toTriggeredAbility? with
  | some ab => ab == TriggeredAbility.onDiesAmassGoblins 4
  | none => false

#guard
  match
    (Ability.triggered
      (.castSpell
        (.intersection [
          .spell,
          .not (.cardType .creature),
          .controlled (.controller .this)]))
      (.keyword (.controller .this) (.amass .goblin (.nat 1)))).toTriggeredAbility? with
  | some ab => ab == TriggeredAbility.onCastNoncreatureAmassGoblins 1
  | none => false

#guard
  match
    (Ability.triggered
      (.attackSimultaneously
        (.intersection [
          .permanent,
          .cardType .creature,
          .controlled (.controller .this)])
        .all
        [])
      (.keyword (.controller .this) (.amass .goblin (.nat 2)))).toTriggeredAbility? with
  | some ab => ab == TriggeredAbility.onYouAttackAmassGoblins 2
  | none => false

#guard
  match
    (Ability.triggered
      (.ordinal 1 .turnStart
        (.castSpell
          (.intersection [
            .spell,
            .not (.cardType .creature),
            .controlled (.opponent (.controller .this))])))
      (.keyword (.controller .this) .recruit)).toTriggeredAbility? with
  | some ab => ab == TriggeredAbility.onOpponentCastsFirstNoncreatureRecruit
  | none => false

#guard
  match
    (Ability.triggered
      (.enter .this)
      (.sequence [
        .actionId 1 (.keyword (.controller .this) (.amass .goblin (.nat 1))),
        .attach .this (.wasObjectOfAction 1)])).toTriggeredAbility? with
  | some ab => ab == TriggeredAbility.onEnterAmassThenAttach 1
  | none => false

#guard
  (Ability.triggered
    (.enter .this)
    (.sequence [
      .keyword (.controller .this) (.amass .goblin (.nat 1)),
      .attach
        .this
        (.intersection [
          .permanent,
          .subtype .army,
          .controlled (.controller .this)])])).toTriggeredAbility?.isNone

#guard
  (Ability.triggered
    (.enter .this)
    (.sequence [
      .actionId 1 (.keyword (.controller .this) (.amass .goblin (.nat 1))),
      .attach .this (.wasObjectOfAction 2)])).toTriggeredAbility?.isNone

#guard
  CardAction.leftoverDrawLoseLifeThenAmass?
    (.sequence [
      .draw (.controller .this) 1,
      .loseLife (.controller .this) 1,
      .keyword (.controller .this) (.amass .goblin (.nat 2))]) == some 2

#guard
  CardAction.toEffect
    (.sequence [
      .draw (.controller .this) 1,
      .loseLife (.controller .this) 1,
      .keyword (.controller .this) (.amass .goblin (.nat 2))]) == Effect.drawLoseLifeThenAmass 2

#guard
  CardAction.toEffect
    (.sequence [
      .returnToHand
        (.targets
          1
          (.range 0 1)
          (.intersection [
            .inGraveyard,
            .cardType .creature,
            .owner (.controller .this)])),
      .keyword (.controller .this) (.amass .goblin (.nat 3))]) == Effect.returnCreatureFromGyThenAmass 3

#guard CardAction.toEffect (.keyword (.controller .this) .recruit) == Effect.recruit
#guard CardAction.toEffect (.keyword (.controller .this) (.amass .goblin (.nat 1))) == Effect.amassGoblins 1
#guard CardAction.toEffect (.keyword .this (.connive (.nat 1))) == Effect.connive
#guard CardAction.toEffect (.keyword (.source .this) (.connive (.nat 1))) == Effect.connive
#guard CardAction.toAbilityEffect (.keyword (.source .this) (.connive (.nat 1))) == Effect.connive
#guard CardAction.toAbilityEffect (.keyword .this (.connive (.nat 1))) != Effect.connive
#guard CardAction.leftoverSourceThis (.source .this)
#guard !CardAction.leftoverSourceThis .this

#guard CardAction.leftoverTokenKind? PredefinedToken.treasureToken == some TokenKind.treasure
#guard CardAction.leftoverTokenKind? PredefinedToken.foodToken == some TokenKind.food
#guard CardAction.leftoverTokenKind?
  [.type .creature, .subtype .dwarf, .colorIndicator [.red], .power 2, .toughness 2] ==
  some TokenKind.dwarf
#guard CardAction.leftoverTokenKind?
  [.type .creature, .subtype .spirit, .colorIndicator [.white], .power 1, .toughness 1,
    .ability (.keyword .flying)] ==
  some TokenKind.spirit
#guard CardAction.leftoverTokenKind?
  [.type .creature, .subtype .hero, .colorIndicator [.white], .power 3, .toughness 2,
    .ability (.keyword .vigilance)] ==
  some TokenKind.hero32vigilance
#guard CardAction.leftoverTokenKind?
  [.type .creature, .subtype .villain, .colorIndicator [.black], .power 2, .toughness 1,
    .ability (.keyword .menace)] ==
  some TokenKind.villain21menace
#guard CardAction.leftoverTokenKind?
  [.type .creature, .subtype .soldier, .colorIndicator [.white], .power 1, .toughness 1] ==
  some TokenKind.soldier11white

#guard
  CardAction.toEffect
    (.createTokens (.controller .this) 2 [
      .type .creature, .subtype .hero, .colorIndicator [.white], .power 3, .toughness 2,
      .ability (.keyword .vigilance)]) ==
    Effect.createTokens .hero32vigilance 2

#guard
  CardAction.toAbilityEffect
    (.createTokens (.controller .this) 1 PredefinedToken.treasureToken) ==
    Effect.abilityCreateTokens .treasure 1

#guard
  match
    (Ability.triggered
      (.enter .this)
      (.createTokens (.controller .this) 1 PredefinedToken.treasureToken)).toTriggeredAbility? with
  | some ab => ab == TriggeredAbility.onEnterCreateTokens .treasure 1
  | none => false

#guard
  CardAction.toAbilityEffect
    (.createTokens (.controller .this) 1 PredefinedToken.treasureToken [.tapped]) ==
    Effect.createTappedTokens .treasure 1

#guard
  match
    (Ability.triggered
      (.enter .this)
      (.createTokens (.controller .this) 1 PredefinedToken.treasureToken
        [.tapped])).toTriggeredAbility? with
  | some ab => ab == TriggeredAbility.onEnterCreateTokens .treasure 1 true
  | none => false

#guard
  match
    (Ability.triggered
      (.enter .this)
      (.playerSelectAction
        (.controller .this)
        (.range 1 1)
        [
          .createTokens (.controller .this) 1 PredefinedToken.foodToken,
          .createTokens (.controller .this) 1 PredefinedToken.treasureToken])).toTriggeredAbility? with
  | some ab => ab == TriggeredAbility.onEnterCreateFoodOrTreasure
  | none => false

#guard
  (Ability.triggered
    (.enter .this)
    (.chooseMode [
      .createTokens (.controller .this) 1 PredefinedToken.foodToken,
      .createTokens (.controller .this) 1 PredefinedToken.treasureToken])).toTriggeredAbility?
    |>.isNone

#guard
  match
    (Ability.triggered
      (.attack (.hostOf .this) .all)
      (.ifElse
        (.any (.intersection [.hostOf .this, .supertype .legendary]))
        [.createTokens (.controller .this) 2
          [.type .creature, .subtype .spirit, .colorIndicator [.white], .power 1, .toughness 1,
            .ability (.keyword .flying)]
          [.tapped, .attacking]]
        [.createTokens (.controller .this) 2
          [.type .creature, .subtype .spirit, .colorIndicator [.white], .power 1, .toughness 1,
            .ability (.keyword .flying)]
          [.tapped]])).toTriggeredAbility? with
  | some ab => ab == TriggeredAbility.onEquippedAttacksCreateSpirits
  | none => false

#guard
  match
    (Ability.triggered
      (.die .this)
      (.createTokens (.controller .this) 1 [
        .type .creature, .subtype .villain, .colorIndicator [.black], .power 2, .toughness 1,
        .ability (.keyword .menace)])).toTriggeredAbility? with
  | some ab => ab == TriggeredAbility.onDiesCreateTokens .villain21menace 1
  | none => false

#guard
  match
    (Ability.triggered
      (.enter .this)
      (.sequence [
        .actionId 1
          (.createTokens (.controller .this) 1 [
            .type .creature, .subtype .dwarf, .colorIndicator [.red], .power 2, .toughness 2]),
        .attach .this (.wasCreatedByAction 1)])).toTriggeredAbility? with
  | some ab => ab == TriggeredAbility.onEnterCreateThenAttach .dwarf
  | none => false

#guard
  CardAction.toEffect
    (.sequence [
      .createTokens (.controller .this) 1 [
        .type .creature, .subtype .villain, .colorIndicator [.black], .power 2, .toughness 1,
        .ability (.keyword .menace)],
      .continuous
        [.addPowerToughness
          (.intersection [
            .permanent,
            .cardType .creature,
            .controlled (.controller .this)]) (Value.int 1) (Value.int 0)]
        .endOfTurn]) ==
    Effect.createTokensThenTeamPump .villain21menace 1 1 0

#guard
  match
    (Ability.triggered
      (.or (.enter .this) (.attack .this .all))
      (.keyword (.controller .this) (.amass .goblin (.nat 3)))).toTriggeredAbility? with
  | some ab => ab == TriggeredAbility.onEnterOrAttackAmassGoblins 3
  | none => false

#guard
  (TraditionalCardDefinition.card [
    .ability (
      .static
        (.gainAbility
          (.intersection [
            .permanent,
            .subtype .army,
            .controlled (.controller .this)])
          (.keyword .trample)))
  ]).toCardDef.staticAbilities == #[.armiesYouControlHaveTrample]

#guard CardAction.toAbilityEffect
  (.mill (.target 1 .player) 3) == Effect.millPlayer 3

#guard
  (TraditionalCardDefinition.card [
    .ability (
      .activated
        [.tapSymbol]
        (.sequence [
          .actionId 1
            (.addManaAnyColor (.controller .this) (.controller .this) 1),
          .continuous
            [.forbid
              (.spendManaCreatedByAction 1
                (.not
                  (.castSpell
                    (.union [.cardType .instant, .cardType .sorcery]))))]
            .endOfTurn]))
  ]).toCardDef.tapAddAnyColorForInstantOrSorcery

#guard
  CardAction.toEffect
    (.sequence [
      .actionId 1 (.mill (.controller .this) 2),
      .optional
        (.returnToHand
          (.selected
            (.controller .this)
            (.range 0 1)
            (.intersection [.wasObjectOfAction 1, .permanent]))),
      .gainLife (.controller .this) 2]) ==
    Effect.millThenPutPermanentGainLife 2 2

#guard
  CardAction.toAbilityEffect
    (.sequence [
      .actionId 1 (.mill (.controller .this) 4),
      .optional
        (.returnToHand
          (.selected
            (.controller .this)
            (.range 1 1)
            (.intersection [
              .wasObjectOfAction 1,
              .union [.subtype .hero, .cardType .enchantment]])))]) ==
    Effect.millThenPutSubtypeOrEnchantment 4 "Hero"

#guard
  CardAction.toEffect
    (.sequence [
      .actionId 1 (.mill (.controller .this) 4),
      .returnToHand
        (.selected
          (.controller .this)
          (.range 0 2)
          (.intersection [.wasObjectOfAction 1, .cardType .land]))]) ==
    Effect.millThenPutLands 4 2

#guard
  match
    (Ability.triggered
      (.ordinal 2 .turnStart (.draw (.controller .this) .all))
      (.mill (.target 1 .player) 3)).toTriggeredAbility? with
  | some ab => ab == TriggeredAbility.onDrawSecondMillPlayer 3
  | none => false

#guard
  match
    (Ability.triggered
      (.enter
        (.intersection [
          .permanent,
          .cardType .land,
          .controlled (.controller .this)]))
      (.createTokens (.controller .this) 1 [
        .type .creature, .subtype .elf, .colorIndicator [.green],
        .power 1, .toughness 1])).toTriggeredAbility? with
  | some ab => ab == TriggeredAbility.onLandYouControlEntersCreateTokens .elf 1
  | none => false

#guard
  match
    (Ability.triggered
      (.enter .this)
      (.sequence [
        .actionId 1 (.mill (.controller .this) 4),
        .returnToHand
          (.intersection [.wasObjectOfAction 1, .subtype .elf])])).toTriggeredAbility? with
  | some ab => ab == TriggeredAbility.onEnterMillThenSubtypeToHand 4 "Elf"
  | none => false

#guard CardAction.toEffect
  (.surveil (.controller .this) 2) == Effect.scry 2

#guard
  CardAction.toEffect
    (.sequence [
      .destroy
        (.target 1 (.intersection [.permanent, .cardType .creature])),
      .surveil (.controller .this) 1]) ==
    Effect.destroyCreatureSurveil

#guard
  match
    (Ability.triggered
      (.enter .this)
      (.surveil (.controller .this) 2)).toTriggeredAbility? with
  | some ab => ab == TriggeredAbility.onEnterSurveil 2
  | none => false

#guard
  match
    (Ability.triggered
      (.enter .this)
      (.createTokens (.controller .this) 1 [
        .name "Redwing",
        .type .creature,
        .supertype .legendary,
        .subtype .bird,
        .subtype .scout,
        .colorIndicator [.blue],
        .power 1,
        .toughness 1,
        .ability (.keyword .flying),
        .ability
          (.triggered
            (.attack .this .all)
            (.surveil (.controller .this) 1))])).toTriggeredAbility? with
  | some ab => ab == TriggeredAbility.onEnter Effect.enterCreateRedwing
  | none => false

#guard
  let action : CardAction :=
    .searchLibraryThenShuffle
      (.controller .this)
      [
        .defineVariable 1
          (.selected
            (.controller .this)
            (.range 0 2)
            (.intersection [
              .inLibrary,
              .cardType .land,
              .supertype .basic])),
        .reveal (.variable 1),
        .putOntoBattlefieldInState
          (.selected (.controller .this) (.range 1 1) (.variable 1))
          [.tapped],
        .returnToHand (.variable 1)]
  action.toAbilityEffect == Effect.searchTwoBasicsSplit

#guard
  let action : CardAction :=
    .searchLibraryThenShuffle
      (.controller .this)
      [
        .defineVariable 1
          (.selected
            (.controller .this)
            (.range 0 2)
            (.intersection [
              .inLibrary,
              .cardType .land,
              .supertype .basic])),
        .reveal (.variable 1),
        .putOntoBattlefieldInState
          (.selected (.controller .this) (.range 0 1) (.variable 1))
          [.tapped],
        .returnToHand (.variable 1)]
  action.toAbilityEffect != Effect.searchTwoBasicsSplit

#guard
  let action : CardAction :=
    .searchLibraryThenShuffle
      (.controller .this)
      [
        .defineVariable 1
          (.selected
            (.controller .this)
            (.range 1 1)
            (.intersection [.inLibrary, .subtype .plan])),
        .reveal (.variable 1),
        .returnToHand (.variable 1)]
  action.toAbilityEffect == Effect.searchLandTypeToHand "Plan"

#guard
  let action : CardAction :=
    .destroy
      (.target
        1
        (.intersection [
          .permanent,
          .union [.cardType .artifact, .cardType .enchantment],
          .not (.cardType .creature)]))
  action.toAbilityEffect == Effect.destroyTargetNoncreatureArtOrEnch

#guard
  match
    (Ability.triggered
      (.enter .this)
      (.returnToHand
        (.target
          1
          (.intersection [
            .inGraveyard,
            .permanent,
            .owner (.controller .this),
            .wasObjectSince (.putToGraveyard .all) .turnStart])))).toTriggeredAbility? with
  | some ab => ab == TriggeredAbility.onEnter Effect.enterReturnGyPermanentThisTurn
  | none => false

#guard
  (Ability.triggered
    (.enter .this)
    (.returnToHand
      (.target
        1
        (.intersection [
          .inGraveyard,
          .permanent,
          .owner (.controller .this)])))).toTriggeredAbility?.isNone

-- Dying this turn is not “put into a graveyard from anywhere this turn”.
#guard
  (Ability.triggered
    (.enter .this)
    (.returnToHand
      (.target
        1
        (.intersection [
          .inGraveyard,
          .permanent,
          .owner (.controller .this),
          .wasObjectSince (.die .all) .turnStart])))).toTriggeredAbility?.isNone

-- Since the start of the game is not this turn.
#guard
  (Ability.triggered
    (.enter .this)
    (.returnToHand
      (.target
        1
        (.intersection [
          .inGraveyard,
          .permanent,
          .owner (.controller .this),
          .wasObjectSince (.putToGraveyard .all) .gameStart])))).toTriggeredAbility?.isNone

#guard
  match
    (Ability.triggered
      (.enter .this)
      (.fight
        .this
        (.targets
          1
          (.range 0 1)
          (.intersection [
            .not .this,
            .permanent,
            .cardType .creature])))).toTriggeredAbility? with
  | some ab => ab == TriggeredAbility.onEnter Effect.enterFightUpToOne
  | none => false

#guard
  (Ability.triggered
    (.enter .this)
    (.dealDamageEqualToPower
      .this
      (.targets
        1
        (.range 0 1)
        (.intersection [
          .not .this,
          .permanent,
          .cardType .creature])))).toTriggeredAbility?.isNone

#guard
  (Ability.triggered
    (.enter .this)
    (.dealDamage
      .this
      (.targets
        1
        (.range 0 1)
        (.intersection [
          .not .this,
          .permanent,
          .cardType .creature]))
      (.nat 3))).toTriggeredAbility?.isNone

#guard
  let others : Selector :=
    .intersection [
      .not .this,
      .permanent,
      .cardType .creature,
      .controlled (.controller .this)]
  match
    (Ability.triggered
      (.or (.enter .this) (.attack .this .all))
      (.sequence [
        .putCounter others .plusOnePlusOne 1,
        .forEachVariable 1 others [.gainLife (.controller .this) 1]])).toTriggeredAbility? with
  | some ab => ab == TriggeredAbility.onEnterOrAttackPlusOneEachOtherGainLife
  | none => false

-- A flat 1 life is not 1 life for each other creature.
#guard
  (Ability.triggered
    (.or (.enter .this) (.attack .this .all))
    (.sequence [
      .putCounter
        (.intersection [
          .not .this,
          .permanent,
          .cardType .creature,
          .controlled (.controller .this)])
        .plusOnePlusOne
        1,
      .gainLife (.controller .this) 1])).toTriggeredAbility?.isNone

-- 2 life for each is not 1 life for each.
#guard
  let others : Selector :=
    .intersection [
      .not .this,
      .permanent,
      .cardType .creature,
      .controlled (.controller .this)]
  (Ability.triggered
    (.or (.enter .this) (.attack .this .all))
    (.sequence [
      .putCounter others .plusOnePlusOne 1,
      .forEachVariable 1 others [.gainLife (.controller .this) 2]])).toTriggeredAbility?.isNone

-- Including this creature is not each other creature.
#guard
  let yours : Selector :=
    .intersection [
      .permanent,
      .cardType .creature,
      .controlled (.controller .this)]
  (Ability.triggered
    (.or (.enter .this) (.attack .this .all))
    (.sequence [
      .putCounter yours .plusOnePlusOne 1,
      .forEachVariable 1 yours [.gainLife (.controller .this) 1]])).toTriggeredAbility?.isNone

#guard
  match
    (Ability.triggered
      (.ordinal 2 .turnStart (.draw (.controller .this) .all))
      (.putCounter
        (.target 1 (.intersection [.permanent, .cardType .creature]))
        .plusOnePlusOne
        1)).toTriggeredAbility? with
  | some ab => ab == TriggeredAbility.onResource Effect.resourceSecondDrawPlusOneTarget
  | none => false

#guard
  match
    (Ability.triggered
      (.castSpell
        (.intersection [
          .spell,
          .not (.cardType .creature),
          .controlled (.controller .this)]))
      (.tap
        (.target
          1
          (.union [.cardType .creature, .cardType .land])))).toTriggeredAbility? with
  | some ab => ab == TriggeredAbility.onCasting Effect.castingTapCreatureOrLand
  | none => false

#guard
  (TraditionalCardDefinition.card [
    .ability
      (.static
        (.addPowerToughness
          (.intersection [
            .not .this,
            .permanent,
            .cardType .creature,
            .subtype .villain,
            .controlled (.controller .this)]) (Value.int 2) (Value.int 1)))
  ]).toCardDef.staticAbilities == #[.otherCreaturesGet #["Villain"] 2 1]

#guard
  (TraditionalCardDefinition.card [
    .ability
      (.static
        (.addPowerToughnessPer
          (.intersection [
            .not .this,
            .permanent,
            .cardType .creature,
            .subtype .dwarf,
            .controlled (.controller .this)])
          (.intersection [
            .permanent,
            .token,
            .cardType .artifact,
            .controlled (.controller .this)]) (Value.int 1) (Value.int 0)))
  ]).toCardDef.staticAbilities == #[.otherSubtypeGetPowerPerArtifactToken "Dwarf"]

#guard
  (TraditionalCardDefinition.card [
    .ability
      (.static
        (.if
          (.any
            (.intersection [
              .permanent,
              .token,
              .cardType .artifact,
              .controlled (.controller .this)]))
          [
            .addPowerToughness
              (.intersection [
                .not .this,
                .permanent,
                .cardType .creature,
                .subtype .dwarf,
                .controlled (.controller .this)]) (Value.int 1) (Value.int 0)]))
  ]).toCardDef.staticAbilities != #[.otherSubtypeGetPowerPerArtifactToken "Dwarf"]

#guard
  (TraditionalCardDefinition.card [
    .ability
      (.static
        (.if
          (.countAtLeast
            (.intersection [
              .inGraveyard,
              .cardType .creature,
              .owner (.controller .this)])
            2)
          [.addPowerToughness .this (Value.int 2) (Value.int 1)]))
  ]).toCardDef.staticAbilities == #[.getsIfGyCreatureCards 2 2 1]

#guard
  (TraditionalCardDefinition.card [
    .ability
      (.static
        (.if
          (.any
            (.intersection [
              .inGraveyard,
              .cardType .creature,
              .owner (.controller .this)]))
          [.addPowerToughness .this (Value.int 2) (Value.int 1)]))
  ]).toCardDef.staticAbilities == #[]

-- One creature card is not enough (Killmonger needs two or more).
#guard
  (TraditionalCardDefinition.card [
    .ability
      (.static
        (.if
          (.countAtLeast
            (.intersection [
              .inGraveyard,
              .cardType .creature,
              .owner (.controller .this)])
            1)
          [.addPowerToughness .this (Value.int 2) (Value.int 1)]))
  ]).toCardDef.staticAbilities == #[]

#guard
  (TraditionalCardDefinition.card [
    .ability
      (.static
        (.if
          (.countAtLeast
            (.intersection [
              .inGraveyard,
              .cardType .creature,
              .owner (.controller .this)])
            2)
          [
            .addPowerToughness .this (Value.int 2) (Value.int 2),
            .gainAllSubtypes .this .creature]))
  ]).toCardDef.staticAbilities == #[.getsAndAllTypesIfGyCreatureCards 2 2 2]

#guard
  (TraditionalCardDefinition.card [
    .ability
      (.static
        (.if
          (.countAtLeast
            (.intersection [
              .inGraveyard,
              .cardType .creature,
              .owner (.controller .this)])
            2)
          [.addPowerToughness .this (Value.int 2) (Value.int 2)]))
  ]).toCardDef.staticAbilities == #[.getsIfGyCreatureCards 2 2 2]

#guard
  (TraditionalCardDefinition.card [
    .ability
      (.static
        (.if
          (.countAtLeast
            (.intersection [
              .inGraveyard,
              .cardType .creature,
              .owner (.controller .this)])
            2)
          [
            .addPowerToughness .this (Value.int 2) (Value.int 2),
            .gainSubtype .this .elf]))
  ]).toCardDef.staticAbilities == #[]

#guard
  (TraditionalCardDefinition.card [
    .ability
      (.static
        (.if
          (.countAtLeast
            (.intersection [
              .inGraveyard,
              .cardType .creature,
              .owner (.controller .this)])
            2)
          [
            .addPowerToughness .this (Value.int 2) (Value.int 2),
            .gainAllSubtypes .this .artifact]))
  ]).toCardDef.staticAbilities == #[]

#guard
  (TraditionalCardDefinition.card [
    .ability
      (.static
        (.if
          (.any
            (.intersection [
              .inGraveyard,
              .cardType .creature,
              .owner (.controller .this)]))
          [
            .addPowerToughness .this (Value.int 2) (Value.int 2),
            .gainAllSubtypes .this .creature]))
  ]).toCardDef.staticAbilities == #[]

#guard
  (TraditionalCardDefinition.card [
    .ability
      (.static
        (.if
          (.any
            (.intersection [
              .inGraveyard,
              .cardType .creature,
              .owner (.controller .this)]))
          [.addPowerToughness .this (Value.int 2) (Value.int 2)]))
  ]).toCardDef.staticAbilities == #[]

-- One creature card is not enough (Undercover Skrull needs two or more).
#guard
  (TraditionalCardDefinition.card [
    .ability
      (.static
        (.if
          (.countAtLeast
            (.intersection [
              .inGraveyard,
              .cardType .creature,
              .owner (.controller .this)])
            1)
          [
            .addPowerToughness .this (Value.int 2) (Value.int 2),
            .gainAllSubtypes .this .creature]))
  ]).toCardDef.staticAbilities == #[]

#guard
  (TraditionalCardDefinition.card [
    .ability
      (.static
        (.if
          (.countAtLeast
            (.intersection [
              .inGraveyard,
              .cardType .creature,
              .owner (.controller .this)])
            1)
          [.addPowerToughness .this (Value.int 2) (Value.int 2)]))
  ]).toCardDef.staticAbilities == #[]

#guard
  (TraditionalCardDefinition.card [
    .ability
      (.static
        (.if
          (.happened (.putCountersSimultaneously .this .plusOnePlusOne) .turnStart)
          [.gainAbility .this (.keyword .flying)]))
  ]).toCardDef.staticAbilities == #[.flyingIfPlusOneThisTurn]

-- Putting counters on any object is not enough (Beast is this creature).
#guard
  (TraditionalCardDefinition.card [
    .ability
      (.static
        (.if
          (.happened (.putCountersSimultaneously .all .plusOnePlusOne) .turnStart)
          [.gainAbility .this (.keyword .flying)]))
  ]).toCardDef.staticAbilities == #[]

-- Since the start of the game is not this turn.
#guard
  (TraditionalCardDefinition.card [
    .ability
      (.static
        (.if
          (.happened (.putCountersSimultaneously .this .plusOnePlusOne) .gameStart)
          [.gainAbility .this (.keyword .flying)]))
  ]).toCardDef.staticAbilities == #[]

#guard
  (TraditionalCardDefinition.card [
    .ability
      (.static
        (.if
          (.happened (.putToGraveyard .this) .turnStart)
          [.gainAbility .this (.keyword .flying)]))
  ]).toCardDef.staticAbilities == #[]

-- Dying (being put into a graveyard from the battlefield) is not enough.
#guard
  (TraditionalCardDefinition.card [
    .ability
      (.static
        (.if
          (.happened (.die .this) .turnStart)
          [.gainAbility .this (.keyword .flying)]))
  ]).toCardDef.staticAbilities == #[]

-- Galadriel, Light of Valinor: you choose modes unchosen this turn by
-- any player. Unrestricted `chooseMode` does not compile to Alliance.
#guard
  let you : Selector := .controller .this
  let among : Selector :=
    .intersection [
      .not .this,
      .permanent,
      .cardType .creature,
      .controlled you]
  let unchosen (id : Nat) : Condition :=
    .didNotHappen (.modeWithIdChosen .player id) .turnStart
  let modes : List (Nat × Condition × List CardAction) :=
    [
      (1, unchosen 1,
        [.addMana you [.mono .green, .mono .green, .mono .green]]),
      (2, unchosen 2,
        [.putCounter
          (.intersection [
            .permanent,
            .cardType .creature,
            .controlled you])
          .plusOnePlusOne
          1]),
      (3, unchosen 3,
        [.sequence [.scry you 2, .draw you 1]])]
  match
    (Ability.triggered (.enter among) (.chooseModeRestricted you modes)
      ).toTriggeredAbility? with
  | some ab => ab == TriggeredAbility.onAnotherCreatureYouControlEntersAlliance
  | none => false

#guard
  let you : Selector := .controller .this
  let among : Selector :=
    .intersection [
      .not .this,
      .permanent,
      .cardType .creature,
      .controlled you]
  let modes : List CardAction :=
    [
      .addMana you [.mono .green, .mono .green, .mono .green],
      .putCounter
        (.intersection [
          .permanent,
          .cardType .creature,
          .controlled you])
        .plusOnePlusOne
        1,
      .sequence [.scry you 2, .draw you 1]]
  (Ability.triggered (.enter among) (.chooseMode modes)).toTriggeredAbility?.isNone

-- An opponent choosing is not you.
#guard
  let you : Selector := .controller .this
  let among : Selector :=
    .intersection [
      .not .this,
      .permanent,
      .cardType .creature,
      .controlled you]
  let unchosen (id : Nat) : Condition :=
    .didNotHappen (.modeWithIdChosen .player id) .turnStart
  let modes : List (Nat × Condition × List CardAction) :=
    [
      (1, unchosen 1,
        [.addMana you [.mono .green, .mono .green, .mono .green]]),
      (2, unchosen 2,
        [.putCounter
          (.intersection [
            .permanent,
            .cardType .creature,
            .controlled you])
          .plusOnePlusOne
          1]),
      (3, unchosen 3,
        [.sequence [.scry you 2, .draw you 1]])]
  (Ability.triggered (.enter among)
    (.chooseModeRestricted (.opponent you) modes)).toTriggeredAbility?.isNone

-- Only you having chosen the mode is not any player.
#guard
  let you : Selector := .controller .this
  let among : Selector :=
    .intersection [
      .not .this,
      .permanent,
      .cardType .creature,
      .controlled you]
  let unchosenYou (id : Nat) : Condition :=
    .didNotHappen (.modeWithIdChosen you id) .turnStart
  let modes : List (Nat × Condition × List CardAction) :=
    [
      (1, unchosenYou 1,
        [.addMana you [.mono .green, .mono .green, .mono .green]]),
      (2, unchosenYou 2,
        [.putCounter
          (.intersection [
            .permanent,
            .cardType .creature,
            .controlled you])
          .plusOnePlusOne
          1]),
      (3, unchosenYou 3,
        [.sequence [.scry you 2, .draw you 1]])]
  (Ability.triggered (.enter among)
    (.chooseModeRestricted you modes)).toTriggeredAbility?.isNone

-- Since the start of the game is not this turn.
#guard
  let you : Selector := .controller .this
  let among : Selector :=
    .intersection [
      .not .this,
      .permanent,
      .cardType .creature,
      .controlled you]
  let unchosenGame (id : Nat) : Condition :=
    .didNotHappen (.modeWithIdChosen .player id) .gameStart
  let modes : List (Nat × Condition × List CardAction) :=
    [
      (1, unchosenGame 1,
        [.addMana you [.mono .green, .mono .green, .mono .green]]),
      (2, unchosenGame 2,
        [.putCounter
          (.intersection [
            .permanent,
            .cardType .creature,
            .controlled you])
          .plusOnePlusOne
          1]),
      (3, unchosenGame 3,
        [.sequence [.scry you 2, .draw you 1]])]
  (Ability.triggered (.enter among)
    (.chooseModeRestricted you modes)).toTriggeredAbility?.isNone

-- The same mode ID on every choice is not three Alliance modes.
#guard
  let you : Selector := .controller .this
  let among : Selector :=
    .intersection [
      .not .this,
      .permanent,
      .cardType .creature,
      .controlled you]
  let unchosen1 : Condition :=
    .didNotHappen (.modeWithIdChosen .player 1) .turnStart
  let modes : List (Nat × Condition × List CardAction) :=
    [
      (1, unchosen1,
        [.addMana you [.mono .green, .mono .green, .mono .green]]),
      (1, unchosen1,
        [.putCounter
          (.intersection [
            .permanent,
            .cardType .creature,
            .controlled you])
          .plusOnePlusOne
          1]),
      (1, unchosen1,
        [.sequence [.scry you 2, .draw you 1]])]
  (Ability.triggered (.enter among)
    (.chooseModeRestricted you modes)).toTriggeredAbility?.isNone

-- Night Nurse: only graveyard permanents put there this turn.
-- Justice: bounce-watch is return-to-hand, includes tokens.
-- Arnim Zola: activate only if two or more creature cards in the graveyard.
-- Moonstone: discard trigger, that discarded card, not any put-to-graveyard.
-- Fin Fang Foom: copy that spell with new targets if it targets an artifact or land.
#guard
  match
    (Ability.triggered
      (.returnToHand
        (.intersection [
          .not .this,
          .permanent,
          .not (.cardType .land),
          .controlled (.controller .this)]))
      (.putCounter (.source .this) .plusOnePlusOne 1)).toTriggeredAbility? with
  | some ab => ab == TriggeredAbility.onWatch Effect.watchJusticeBounce
  | none => false

#guard
  (Ability.triggered
    (.putToGraveyard
      (.intersection [
        .not .this,
        .permanent,
        .not (.cardType .land),
        .controlled (.controller .this)]))
    (.putCounter (.source .this) .plusOnePlusOne 1)).toTriggeredAbility?.isNone

#guard
  (Ability.triggered
    (.returnToHand
      (.intersection [
        .not .this,
        .permanent,
        .not (.cardType .land),
        .not .token,
        .controlled (.controller .this)]))
    (.putCounter (.source .this) .plusOnePlusOne 1)).toTriggeredAbility?.isNone

#guard
  match
    (Ability.activatedIf
      (.countAtLeast
        (.intersection [
          .inGraveyard,
          .cardType .creature,
          .owner (.controller .this)])
        2)
      [.mana [.generic 3], .tapSymbol]
      (.createTokens
        (.controller .this)
        1
        [
          .type .creature, .subtype .villain, .colorIndicator [.black],
          .power 2, .toughness 1, .ability (.keyword .menace)]
        [.tapped])).toActivatedAbility? with
  | some ab => ab.onlyIfGyCreaturesAtLeast == 2
  | none => false

#guard
  (Ability.activatedIf
    (.any
      (.intersection [
        .inGraveyard,
        .cardType .creature,
        .owner (.controller .this)]))
    [.mana [.generic 3], .tapSymbol]
    (.createTokens
      (.controller .this)
      1
      [
        .type .creature, .subtype .villain, .colorIndicator [.black],
        .power 2, .toughness 1, .ability (.keyword .menace)]
      [.tapped])).toActivatedAbility?.isNone

#guard
  (Ability.activatedIf
    (.countAtLeast
      (.intersection [
        .inGraveyard,
        .cardType .creature,
        .owner (.controller .this)])
      1)
    [.mana [.generic 3], .tapSymbol]
    (.createTokens
      (.controller .this)
      1
      [
        .type .creature, .subtype .villain, .colorIndicator [.black],
        .power 2, .toughness 1, .ability (.keyword .menace)]
      [.tapped])).toActivatedAbility?.isNone

#guard
  match
    (Ability.activated
      [.mana [.generic 3], .tapSymbol]
      (.createTokens
        (.controller .this)
        1
        [
          .type .creature, .subtype .villain, .colorIndicator [.black],
          .power 2, .toughness 1, .ability (.keyword .menace)]
        [.tapped])).toActivatedAbility? with
  | some ab => ab.onlyIfGyCreaturesAtLeast == 0
  | none => false

#guard
  let action : CardAction :=
    .optional
      (.sequence [
        .actionId 1
          (.exile (.intersection [
            .inGraveyard,
            .wasObjectOfThisTrigger,
            .owner (.controller .this)])),
        .continuous
          [.canPlay (.controller .this) (.wasCreatedByAction 1)]
          (.sequence [.turnStart, .endOfPlayerTurn (.controller .this)])])
  match (Ability.triggered (.discard (.controller .this)) action).toTriggeredAbility? with
  | some ab => ab == TriggeredAbility.onResource Effect.resourceDiscardExilePlay
  | none => false

#guard
  let action : CardAction :=
    .optional
      (.sequence [
        .actionId 1
          (.exile (.intersection [.inGraveyard, .owner (.controller .this)])),
        .continuous
          [.canPlay (.controller .this) (.wasCreatedByAction 1)]
          (.sequence [.turnStart, .endOfPlayerTurn (.controller .this)])])
  (Ability.triggered (.discard (.controller .this)) action).toTriggeredAbility?.isNone

#guard
  let action : CardAction :=
    .optional
      (.sequence [
        .actionId 1
          (.exile (.intersection [
            .inGraveyard,
            .wasObjectSince (.discard (.controller .this)) .turnStart,
            .owner (.controller .this)])),
        .continuous
          [.canPlay (.controller .this) (.wasCreatedByAction 1)]
          (.sequence [.turnStart, .endOfPlayerTurn (.controller .this)])])
  (Ability.triggered (.discard (.controller .this)) action).toTriggeredAbility?.isNone

#guard
  let action : CardAction :=
    .optional
      (.sequence [
        .actionId 1
          (.exile (.intersection [
            .inGraveyard,
            .wasObjectOfThisTrigger,
            .owner (.controller .this)])),
        .continuous
          [.canPlay (.controller .this) (.wasCreatedByAction 1)]
          (.sequence [.turnStart, .endOfPlayerTurn (.controller .this)])])
  (Ability.triggered (.putToGraveyard (.owner (.controller .this))) action
    ).toTriggeredAbility?.isNone

#guard
  match
    (Ability.triggered
      (.castSpell
        (.intersection [
          .spell,
          .union [.cardType .instant, .cardType .sorcery],
          .controlled (.controller .this),
          .hasTarget (.union [.cardType .artifact, .cardType .land])]))
      (.sequence [
        .copyWithNewTargets (.controller .this) .wasObjectOfThisTrigger,
        .putCounter (.source .this) .plusOnePlusOne 2])).toTriggeredAbility? with
  | some ab => ab == TriggeredAbility.onCasting Effect.castingCopyIfArtifactOrLand
  | none => false

#guard
  (Ability.triggered
    (.castSpell
      (.intersection [
        .spell,
        .union [.cardType .instant, .cardType .sorcery],
        .controlled (.controller .this)]))
    (.if
      (.targetsIncludeAny
        (.intersection [
          .spell,
          .union [.cardType .instant, .cardType .sorcery],
          .controlled (.controller .this)])
        (.union [.cardType .artifact, .cardType .land]))
      [.putCounter (.source .this) .plusOnePlusOne 2])).toTriggeredAbility?.isNone

#guard
  (Ability.triggered
    (.castSpell
      (.intersection [
        .spell,
        .union [.cardType .instant, .cardType .sorcery],
        .controlled (.controller .this)]))
    (.sequence [
      .copyWithNewTargets (.controller .this) .wasObjectOfThisTrigger,
      .putCounter (.source .this) .plusOnePlusOne 2])).toTriggeredAbility?.isNone

#guard
  (Ability.triggered
    (.castSpell
      (.intersection [
        .spell,
        .union [.cardType .instant, .cardType .sorcery],
        .controlled (.controller .this),
        .hasTarget (.union [.cardType .artifact, .cardType .land])]))
    (.sequence [
      .copyWithNewTargets (.controller .this) .all,
      .putCounter (.source .this) .plusOnePlusOne 2])).toTriggeredAbility?.isNone

#guard
  (Ability.triggered
    (.castSpell
      (.intersection [
        .spell,
        .union [.cardType .instant, .cardType .sorcery],
        .controlled (.controller .this),
        .hasTarget (.cardType .creature)]))
    (.sequence [
      .copyWithNewTargets (.controller .this) .wasObjectOfThisTrigger,
      .putCounter (.source .this) .plusOnePlusOne 2])).toTriggeredAbility?.isNone

#guard
  (Ability.triggered
    (.castSpell
      (.intersection [
        .spell,
        .union [.cardType .instant, .cardType .sorcery],
        .controlled (.controller .this),
        .hasTarget (.union [.cardType .artifact, .cardType .land])]))
    (.putCounter (.source .this) .plusOnePlusOne 2)).toTriggeredAbility?.isNone

-- Speed: you may pay {1}; if you do, haste-except-haste.
#guard
  match
    (Ability.triggered
      (.castSpell
        (.intersection [
          .spell,
          .not (.cardType .creature),
          .controlled (.controller .this)]))
      (.optionalPayFor
        (.controller .this)
        [.mana [.generic 1]]
        [
          .continuous
            [
              .forbid
                (.block
                  (.not (.keyword .haste))
                  (.target
                    1
                    (.intersection [
                      .permanent,
                      .cardType .creature,
                      .keyword .haste])))]
            .endOfTurn])).toTriggeredAbility? with
  | some ab => ab == TriggeredAbility.onCasting Effect.castingMayPayHasteUnblockable
  | none => false

-- Paying is required (the restrict alone is not Speed).
#guard
  (Ability.triggered
    (.castSpell
      (.intersection [
        .spell,
        .not (.cardType .creature),
        .controlled (.controller .this)]))
    (.continuous
      [
        .forbid
          (.block
            (.not (.keyword .haste))
            (.target
              1
              (.intersection [
                .permanent,
                .cardType .creature,
                .keyword .haste])))]
      .endOfTurn)).toTriggeredAbility?.isNone

-- An opponent paying is not you.
#guard
  (Ability.triggered
    (.castSpell
      (.intersection [
        .spell,
        .not (.cardType .creature),
        .controlled (.controller .this)]))
    (.optionalPayFor
      (.opponent (.controller .this))
      [.mana [.generic 1]]
      [
        .continuous
          [
            .forbid
              (.block
                (.not (.keyword .haste))
                (.target
                  1
                  (.intersection [
                    .permanent,
                    .cardType .creature,
                    .keyword .haste])))]
          .endOfTurn])).toTriggeredAbility?.isNone

-- {2} is not {1}.
#guard
  (Ability.triggered
    (.castSpell
      (.intersection [
        .spell,
        .not (.cardType .creature),
        .controlled (.controller .this)]))
    (.optionalPayFor
      (.controller .this)
      [.mana [.generic 2]]
      [
        .continuous
          [
            .forbid
              (.block
                (.not (.keyword .haste))
                (.target
                  1
                  (.intersection [
                    .permanent,
                    .cardType .creature,
                    .keyword .haste])))]
          .endOfTurn])).toTriggeredAbility?.isNone

-- Drawing if paid is not the haste restrict.
#guard
  (Ability.triggered
    (.castSpell
      (.intersection [
        .spell,
        .not (.cardType .creature),
        .controlled (.controller .this)]))
    (.optionalPayFor
      (.controller .this)
      [.mana [.generic 1]]
      [.draw (.controller .this) 1])).toTriggeredAbility?.isNone

-- Bullseye: discard a nonland card, not any card.
#guard
  let sacArt : Cost :=
    .sacrificeCount
      (.intersection [
        .permanent,
        .cardType .artifact,
        .controlled (.controller .this)])
      1
  match
    (Ability.triggered
      (.enter .this)
      (.optionalPayFor
        (.controller .this)
        [.or [sacArt, .discard (.not (.cardType .land))]]
        [.dealDamage .this (.target 2 .all) (.nat 2)])).toTriggeredAbility? with
  | some ab => ab == TriggeredAbility.onEnter Effect.enterMaySacOrDiscardNonlandThenDamage
  | none => false

#guard
  let sacArt : Cost :=
    .sacrificeCount
      (.intersection [
        .permanent,
        .cardType .artifact,
        .controlled (.controller .this)])
      1
  (Ability.triggered
    (.enter .this)
    (.optionalPayFor
      (.controller .this)
      [.or [sacArt, .discard .all]]
      [.dealDamage .this (.target 2 .all) (.nat 2)])).toTriggeredAbility?.isNone

#guard
  let sacArt : Cost :=
    .sacrificeCount
      (.intersection [
        .permanent,
        .cardType .artifact,
        .controlled (.controller .this)])
      1
  match
    (Ability.activated
      [.mana [.generic 3], .tapSymbol, .or [sacArt, .discard (.not (.cardType .land))]]
      (.dealDamage .this (.target 1 .all) (.nat 2))).toActivatedAbility? with
  | some ab => ab.cost.sacrificeArtifactOrDiscardNonland
  | none => false

#guard
  let sacArt : Cost :=
    .sacrificeCount
      (.intersection [
        .permanent,
        .cardType .artifact,
        .controlled (.controller .this)])
      1
  match
    (Ability.activated
      [.mana [.generic 3], .tapSymbol, .or [sacArt, .discard .all]]
      (.dealDamage .this (.target 1 .all) (.nat 2))).toActivatedAbility? with
  | some ab => !ab.cost.sacrificeArtifactOrDiscardNonland
  | none => false

#guard
  (TraditionalCardDefinition.card [
    .ability
      (.static
        (.forbid
          (.or
            (.attack
              (.intersection [.permanent, .cardType .creature, .keyword .flying])
              (.controller .this))
            (.block
              (.intersection [.permanent, .cardType .creature, .keyword .flying])
              (.intersection [
                .permanent,
                .cardType .creature,
                .controlled (.controller .this)])))))
  ]).toCardDef.staticAbilities == #[.flyingCantAttackYouOrBlockYours]

-- Storm: a spell that hasTarget a creature; those creatures (targets of
-- this spell) gain flying.
#guard
  match
    (Ability.triggered
      (.castSpell
        (.intersection [
          .spell,
          .controlled (.controller .this),
          .hasTarget
            (.intersection [
              .permanent,
              .cardType .creature])]))
      (.continuous
        [
          .gainAbility
            (.intersection [
              .permanent,
              .cardType .creature,
              .isTargetOf .wasObjectOfThisTrigger])
            (.keyword .flying)]
        .endOfTurn)).toTriggeredAbility? with
  | some ab => ab == TriggeredAbility.onCasting Effect.castingTargetsGainFlying
  | none => false

#guard
  (Ability.triggered
    (.castSpell (.intersection [.spell, .controlled (.controller .this)]))
    (.if
      (.targetsIncludeAny
        .this
        (.intersection [.permanent, .cardType .creature]))
      [
        .continuous
          [
            .gainAbility
              (.intersection [.permanent, .cardType .creature])
              (.keyword .flying)]
          .endOfTurn])).toTriggeredAbility?.isNone

#guard
  (Ability.triggered
    (.castSpell
      (.intersection [
        .spell,
        .controlled (.controller .this),
        .hasTarget
          (.intersection [
            .permanent,
            .cardType .creature])]))
    (.continuous
      [
        .gainAbility
          (.intersection [
            .permanent,
            .cardType .creature,
            .wasObjectOfThisTrigger])
          (.keyword .flying)]
      .endOfTurn)).toTriggeredAbility?.isNone

#guard
  (Ability.triggered
    (.castSpell
      (.intersection [
        .spell,
        .controlled (.controller .this),
        .hasTarget
          (.intersection [
            .permanent,
            .cardType .creature])]))
    (.continuous
      [
        .gainAbility
          (.intersection [.permanent, .cardType .creature])
          (.keyword .flying)]
      .endOfTurn)).toTriggeredAbility?.isNone

#guard
  (Ability.triggered
    (.castSpell
      (.intersection [
        .spell,
        .controlled (.controller .this)]))
    (.continuous
      [
        .gainAbility
          (.intersection [
            .permanent,
            .cardType .creature,
            .isTargetOf .wasObjectOfThisTrigger])
          (.keyword .flying)]
      .endOfTurn)).toTriggeredAbility?.isNone

#guard
  (Ability.triggered
    (.castSpell
      (.intersection [
        .spell,
        .controlled (.controller .this),
        .hasTarget
          (.intersection [
            .permanent,
            .cardType .artifact])]))
    (.continuous
      [
        .gainAbility
          (.intersection [
            .permanent,
            .cardType .creature,
            .isTargetOf .wasObjectOfThisTrigger])
          (.keyword .flying)]
      .endOfTurn)).toTriggeredAbility?.isNone

-- Attack-only is not enough (Storm also forbids blocking).
#guard
  (TraditionalCardDefinition.card [
    .ability
      (.static
        (.forbid
          (.attack
            (.intersection [.permanent, .cardType .creature, .keyword .flying])
            (.controller .this))))
  ]).toCardDef.staticAbilities == #[]

-- Blocking-only is not enough (Storm also forbids attacking).
#guard
  (TraditionalCardDefinition.card [
    .ability
      (.static
        (.forbid
          (.block
            (.intersection [.permanent, .cardType .creature, .keyword .flying])
            (.intersection [
              .permanent,
              .cardType .creature,
              .controlled (.controller .this)]))))
  ]).toCardDef.staticAbilities == #[]

-- Wolverine: heal all damage on this, then keep the replaced damage event.
#guard
  (TraditionalCardDefinition.card [
    .ability
      (.static
        (.replace
          (.damage .all .this)
          [.healAllDamage .this, .keepReplacedAction]))
  ]).toCardDef.staticAbilities == #[.healOtherDamageWhenDealt]

-- Empty replacement is not enough (must heal then keep the damage).
#guard
  (TraditionalCardDefinition.card [
    .ability (.static (.replace (.damage .all .this) []))
  ]).toCardDef.staticAbilities == #[]

#guard
  (TraditionalCardDefinition.card [
    .ability
      (.static
        (.replace
          (.damage .all .this)
          [.keepReplacedAction]))
  ]).toCardDef.staticAbilities == #[]

#guard
  (TraditionalCardDefinition.card [
    .ability
      (.static
        (.replace
          (.damage .all .this)
          [.healAllDamage .this]))
  ]).toCardDef.staticAbilities == #[]

#guard
  (TraditionalCardDefinition.card [
    .ability
      (.static
        (.replace
          (.damage .all .this)
          [.keepReplacedAction, .healAllDamage .this]))
  ]).toCardDef.staticAbilities == #[]

#guard
  (TraditionalCardDefinition.card [
    .ability
      (.static
        (.replace
          (.combatDamage .all .this)
          [.healAllDamage .this, .keepReplacedAction]))
  ]).toCardDef.staticAbilities == #[]

-- Dwarven Mauler: Equip abilities you activate that target this cost {2} less.
#guard Selector.leftoverKeywordAbility?
  (Selector.keywordAbility .equip) == some .equip

#guard Selector.leftoverKeywordAbility? (.keyword .equip) |>.isNone

#guard
  (TraditionalCardDefinition.card [
    .ability
      (.static
        (.reduceCost
          (.intersection [
            Selector.keywordAbility .equip,
            .hasTarget .this,
            .controlled (.controller .this)])
          [.mana [.generic 2]]))
  ]).toCardDef.staticAbilities == #[.equipAbilitiesTargetingThisCostLess 2]

-- Objects with Equip are not Equip abilities.
#guard
  (TraditionalCardDefinition.card [
    .ability
      (.static
        (.reduceCost
          (.intersection [
            .keyword .equip,
            .hasTarget .this,
            .controlled (.controller .this)])
          [.mana [.generic 2]]))
  ]).toCardDef.staticAbilities == #[]

-- Missing hasTarget is not enough (must target this).
#guard
  (TraditionalCardDefinition.card [
    .ability
      (.static
        (.reduceCost
          (.intersection [
            Selector.keywordAbility .equip,
            .controlled (.controller .this)])
          [.mana [.generic 2]]))
  ]).toCardDef.staticAbilities == #[]

#guard
  (TraditionalCardDefinition.card [
    .ability
      (.static
        (.reduceCost
          (.intersection [
            Selector.keywordAbility .equip,
            .hasTarget .player,
            .controlled (.controller .this)])
          [.mana [.generic 2]]))
  ]).toCardDef.staticAbilities == #[]

-- Missing you-activate is not enough.
#guard
  (TraditionalCardDefinition.card [
    .ability
      (.static
        (.reduceCost
          (.intersection [
            Selector.keywordAbility .equip,
            .hasTarget .this])
          [.mana [.generic 2]]))
  ]).toCardDef.staticAbilities == #[]

#guard
  (TraditionalCardDefinition.card [
    .ability
      (.static
        (.reduceCost
          (.intersection [
            Selector.keywordAbility .flying,
            .hasTarget .this,
            .controlled (.controller .this)])
          [.mana [.generic 2]]))
  ]).toCardDef.staticAbilities == #[]

-- Reducing this object's costs is not Equip-targeting-this.
#guard
  (TraditionalCardDefinition.card [
    .ability (.static (.reduceCost .this [.mana [.generic 2]]))
  ]).toCardDef.staticAbilities == #[]

-- Along the Crooked Way: creature card leaves your graveyard, amass Goblins.
#guard
  match
    (Ability.triggered
      (.leaveGraveyard
        (.intersection [
          .inGraveyard,
          .cardType .creature,
          .owner (.controller .this)]))
      (.keyword (.controller .this) (.amass .goblin (.nat 1)))).toTriggeredAbility? with
  | some ab => ab == TriggeredAbility.onCreatureCardLeavesYourGyAmassGoblins 1
  | none => false

-- Opponent's graveyard is not yours.
#guard
  (Ability.triggered
    (.leaveGraveyard
      (.intersection [
        .inGraveyard,
        .cardType .creature,
        .owner (.opponent (.controller .this))]))
    (.keyword (.controller .this) (.amass .goblin (.nat 1)))).toTriggeredAbility?.isNone

-- Instant cards leaving the graveyard are not creature cards.
#guard
  (Ability.triggered
    (.leaveGraveyard
      (.intersection [
        .inGraveyard,
        .cardType .instant,
        .owner (.controller .this)]))
    (.keyword (.controller .this) (.amass .goblin (.nat 1)))).toTriggeredAbility?.isNone

-- Enter: return target creature card from your graveyard.
#guard
  match
    (Ability.triggered
      (.enter .this)
      (.returnToHand
        (.target
          1
          (.intersection [
            .inGraveyard,
            .cardType .creature,
            .owner (.controller .this)])))).toTriggeredAbility? with
  | some ab => ab == TriggeredAbility.onEnterReturnCreatureFromGyToHand
  | none => false

-- Up-to-one is not a required target creature card.
#guard
  (Ability.triggered
    (.enter .this)
    (.returnToHand
      (.targets
        1
        (.range 0 1)
        (.intersection [
          .inGraveyard,
          .cardType .creature,
          .owner (.controller .this)])))).toTriggeredAbility?.isNone

-- Goblins and Orcs you control gain menace.
#guard
  CardAction.toAbilityEffect
    (.continuous
      [.gainAbility
        (.intersection [
          .permanent,
          .union [.subtype .goblin, .subtype .orc],
          .controlled (.controller .this)])
        (.keyword .menace)]
      .endOfTurn) ==
  Effect.subtypesGainMenace #["Goblin", "Orc"]

-- Flying instead of menace is not subtypesGainMenace.
#guard
  CardAction.toAbilityEffect
    (.continuous
      [.gainAbility
        (.intersection [
          .permanent,
          .union [.subtype .goblin, .subtype .orc],
          .controlled (.controller .this)])
        (.keyword .flying)]
      .endOfTurn) !=
  Effect.subtypesGainMenace #["Goblin", "Orc"]

-- Opponent's Goblins and Orcs are not yours.
#guard
  CardAction.toAbilityEffect
    (.continuous
      [.gainAbility
        (.intersection [
          .permanent,
          .union [.subtype .goblin, .subtype .orc],
          .controlled (.opponent (.controller .this))])
        (.keyword .menace)]
      .endOfTurn) !=
  Effect.subtypesGainMenace #["Goblin", "Orc"]

-- Creatures you control (no subtype) still leftover to teamGain.
#guard
  CardAction.toAbilityEffect
    (.continuous
      [.gainAbility
        (.intersection [
          .permanent,
          .cardType .creature,
          .controlled (.controller .this)])
        (.keyword .menace)]
      .endOfTurn) ==
  Effect.teamGain Keyword.menace.toKeywords

-- Armor Wars I: you may draw per artifact; if you do, each opponent draws.
#guard
  CardAction.leftoverMayDrawPerArtifactOppsDraw?
    (.optional
      (.sequence [
        .forEachVariable 1
          (.intersection [
            .permanent,
            .cardType .artifact,
            .controlled (.controller .this)])
          [.draw (.controller .this) 1],
        .draw (.opponent (.controller .this)) 1
      ]))

-- Not optional is not enough.
#guard
  !CardAction.leftoverMayDrawPerArtifactOppsDraw?
    (.sequence [
      .forEachVariable 1
        (.intersection [
          .permanent,
          .cardType .artifact,
          .controlled (.controller .this)])
        [.draw (.controller .this) 1],
      .draw (.opponent (.controller .this)) 1
    ])

-- Creatures you control are not artifacts.
#guard
  !CardAction.leftoverMayDrawPerArtifactOppsDraw?
    (.optional
      (.sequence [
        .forEachVariable 1
          (.intersection [
            .permanent,
            .cardType .creature,
            .controlled (.controller .this)])
          [.draw (.controller .this) 1],
        .draw (.opponent (.controller .this)) 1
      ]))

-- Missing opponent draw is not enough.
#guard
  !CardAction.leftoverMayDrawPerArtifactOppsDraw?
    (.optional
      (.forEachVariable 1
        (.intersection [
          .permanent,
          .cardType .artifact,
          .controlled (.controller .this)])
        [.draw (.controller .this) 1]))

-- Each player drawing is not each opponent.
#guard
  !CardAction.leftoverMayDrawPerArtifactOppsDraw?
    (.optional
      (.sequence [
        .forEachVariable 1
          (.intersection [
            .permanent,
            .cardType .artifact,
            .controlled (.controller .this)])
          [.draw (.controller .this) 1],
        .draw .player 1
      ]))

-- Armor Wars II: artifact spells you cast this turn cost {1} less.
#guard
  CardAction.leftoverArtifactSpellsCostLessThisTurn?
    (.continuous
      [
        .reduceCost
          (.intersection [
            .spell,
            .cardType .artifact,
            .controlled (.controller .this)])
          [.mana [.generic 1]]
      ]
      .endOfTurn) == some 1

-- Lasting cost reduction is not this turn.
#guard
  CardAction.leftoverArtifactSpellsCostLessThisTurn?
    (.continuous
      [
        .reduceCost
          (.intersection [
            .spell,
            .cardType .artifact,
            .controlled (.controller .this)])
          [.mana [.generic 1]]
      ]
      .endOfGame) |>.isNone

-- Creature spells are not artifact spells.
#guard
  CardAction.leftoverArtifactSpellsCostLessThisTurn?
    (.continuous
      [
        .reduceCost
          (.intersection [
            .spell,
            .cardType .creature,
            .controlled (.controller .this)])
          [.mana [.generic 1]]
      ]
      .endOfTurn) |>.isNone

-- Artifact permanents are not artifact spells.
#guard
  CardAction.leftoverArtifactSpellsCostLessThisTurn?
    (.continuous
      [
        .reduceCost
          (.intersection [
            .permanent,
            .cardType .artifact,
            .controlled (.controller .this)])
          [.mana [.generic 1]]
      ]
      .endOfTurn) |>.isNone

-- Armor Wars III: this deals X to target opponent, X = greatest artifact MV.
#guard
  CardAction.leftoverChapterDealXDamageToTargetOpponentGreatestArtifactMv?
    (.dealDamage
      .this
      (.target 1 (.opponent (.controller .this)))
      (.greatestManaValue
        (.intersection [
          .permanent,
          .cardType .artifact,
          .controlled (.controller .this)])))

-- Target player is not target opponent.
#guard
  !CardAction.leftoverChapterDealXDamageToTargetOpponentGreatestArtifactMv?
    (.dealDamage
      .this
      (.target 1 .player)
      (.greatestManaValue
        (.intersection [
          .permanent,
          .cardType .artifact,
          .controlled (.controller .this)])))

-- Greatest mana value among creatures is not artifacts.
#guard
  !CardAction.leftoverChapterDealXDamageToTargetOpponentGreatestArtifactMv?
    (.dealDamage
      .this
      (.target 1 (.opponent (.controller .this)))
      (.greatestManaValue
        (.intersection [
          .permanent,
          .cardType .creature,
          .controlled (.controller .this)])))

-- Literal damage is not computed greatest-mana-value damage.
#guard
  !CardAction.leftoverChapterDealXDamageToTargetOpponentGreatestArtifactMv?
    (.dealDamage .this (.target 1 (.opponent (.controller .this))) (.nat 3))

#guard
  CardAction.leftoverChapterEffect?
    [
      .optional
        (.sequence [
          .forEachVariable 1
            (.intersection [
              .permanent,
              .cardType .artifact,
              .controlled (.controller .this)])
            [.draw (.controller .this) 1],
          .draw (.opponent (.controller .this)) 1
        ])
    ] == some Effect.mayDrawPerArtifactOppsDraw

#guard
  CardAction.leftoverChapterEffect?
    [
      .continuous
        [
          .reduceCost
            (.intersection [
              .spell,
              .cardType .artifact,
              .controlled (.controller .this)])
            [.mana [.generic 1]]
        ]
        .endOfTurn
    ] == some (Effect.artifactSpellsCostLessThisTurn 1)

#guard
  CardAction.leftoverChapterEffect?
    [
      .dealDamage
        .this
        (.target 1 (.opponent (.controller .this)))
        (.greatestManaValue
          (.intersection [
            .permanent,
            .cardType .artifact,
            .controlled (.controller .this)]))
    ] == some Effect.chapterDealXDamageToTargetOpponentGreatestArtifactMv

-- Armor Wars chapters compile to a three-chapter Saga sacrificed after III.
#guard
  match
    (TraditionalCardDefinition.card [
      .subtype .saga,
      .ability
        (.keywordWithEffect
          (.chapter 1)
          [
            .optional
              (.sequence [
                .forEachVariable 1
                  (.intersection [
                    .permanent,
                    .cardType .artifact,
                    .controlled (.controller .this)])
                  [.draw (.controller .this) 1],
                .draw (.opponent (.controller .this)) 1
              ])
          ]),
      .ability
        (.keywordWithEffect
          (.chapter 2)
          [
            .continuous
              [
                .reduceCost
                  (.intersection [
                    .spell,
                    .cardType .artifact,
                    .controlled (.controller .this)])
                  [.mana [.generic 1]]
              ]
              .endOfTurn
          ]),
      .ability
        (.keywordWithEffect
          (.chapter 3)
          [
            .dealDamage
              .this
              (.target 1 (.opponent (.controller .this)))
              (.greatestManaValue
                (.intersection [
                  .permanent,
                  .cardType .artifact,
                  .controlled (.controller .this)]))
          ])
    ]).toCardDef.saga with
  | some s =>
    s.sacrificeAfter == "III" && s.chapters.size == 3 &&
      s.chapters[0]!.roman == "I" &&
      s.chapters[1]!.roman == "II" &&
      s.chapters[2]!.roman == "III" &&
      s.chapters[2]!.chapterEffect ==
        some Effect.chapterDealXDamageToTargetOpponentGreatestArtifactMv
  | none => false

-- Uncompiled chapter actions do not produce a Saga.
#guard
  (TraditionalCardDefinition.card [
    .subtype .saga,
    .ability (.keywordWithEffect (.chapter 1) [.draw (.controller .this) 1])
  ]).toCardDef.saga.isNone

end Mtg.Engine
