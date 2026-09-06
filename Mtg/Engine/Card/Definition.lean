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

-- Selectors may ask who was the subject of a trigger, and triggers name
-- selectors, so the two inductives are mutual.
mutual
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
  /-- The given player chooses objects matching the given selector at
  resolution, with a count range (not targeting; CR 608.2d). -/
  | selected : Selector → Range → Selector → Selector
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
  /-- An object with the given keyword (CR 702). -/
  | keyword : Keyword → Selector
  /-- Objects with power at least this value (CR 208). -/
  | powerAtLeast : Int → Selector
  /-- Printed subtype (CR 205.3). -/
  | subtype : CardSubtype → Selector
  /-- A spell on the stack (CR 112.1). -/
  | spell
  /-- A permanent spell (CR 110.4 / 112.1). -/
  | permanentSpell
  /-- A player (CR 102). -/
  | player
  /-- Opponents of the given player (CR 102.2). -/
  | opponent : Selector → Selector
  /-- The owner of the given object (CR 108.3). -/
  | owner : Selector → Selector
  /-- A permanent attacking objects matching the given selector (CR 508). -/
  | attacking : Selector → Selector
  /-- Permanents blocking the given permanents (CR 509). -/
  | blocking : Selector → Selector
  /-- A token (CR 111.1). -/
  | token
  /-- The object of the numbered action. -/
  | wasObjectOfAction : Nat → Selector
  /-- The object a replacement effect is replacing. -/
  | replacingObject : Nat → Selector
  /-- An object created by the numbered action. -/
  | wasCreatedByAction : Nat → Selector
  /-- The permanent the given object is attached to (CR 301.5 / 303.4). -/
  | hostOf : Selector → Selector
  /-- An object in a graveyard (CR 404). -/
  | inGraveyard
  /-- An object in a library (CR 401). -/
  | inDeck
  /-- Objects with the given supertype (CR 205.4). -/
  | supertype : CardSupertype → Selector
  /-- Objects bound to this numbered variable. -/
  | variable : Nat → Selector
  /-- The top card of the selected player's library (CR 401). -/
  | topOfLibrary : Selector → Selector
deriving Repr, Inhabited, BEq

/-- When a continuous effect ends, when a triggered ability fires, or
what a replacement effect intercepts. -/
inductive Trigger where
  | endOfGame
  | endOfTurn
  /-- From the start of the turn (a window bound for `happened`). -/
  | turnStart
  /-- From the start of the game (a window bound for `happened`). -/
  | gameStart
  /-- Whenever the selected object attacks, restricted by the given
  selector. -/
  | attack : Selector → Selector → Trigger
  /-- When the selected object enters. -/
  | enter : Selector → Trigger
  /-- Whenever the selected player draws a card matching the given
  selector. -/
  | draw : Selector → Selector → Trigger
  /-- The nth occurrence of the inner trigger, counted from the given
  window. -/
  | ordinal : Nat → Trigger → Trigger → Trigger
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
  /-- The numbered ability was activated (CR 602.2). -/
  | abilityWithIdActivated : Nat → Trigger
  /-- The numbered action occurred. -/
  | actionWithId : Nat → Trigger
  /-- Mana created by the numbered action is spent to pay for the given
  event (CR 106.10). -/
  | spendManaCreatedByAction : Nat → Trigger → Trigger
  /-- A spell matching the selector is cast (CR 601). -/
  | castSpell : Selector → Trigger
  /-- An activated ability of a source matching the selector is activated
  (CR 602). -/
  | activateAbility : Selector → Trigger
  /-- The given trigger does not occur. -/
  | not : Trigger → Trigger
  /-- Either trigger occurs. -/
  | or : Trigger → Trigger → Trigger
deriving Repr, Inhabited, BEq
end

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
    diedThisTurn := a.diedThisTurn || b.diedThisTurn }

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
    diedThisTurn := a.diedThisTurn && b.diedThisTurn }

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
  | .powerAtLeast n => { powerAtLeast := some n }
  | .attacking _ => { attacking := true }
  | .blocking _ => {}
  | .token => { token := true }
  | .subtype st => { subtype := some st.toString }
  | .cardType t => { types := .oneOf [t] }
  | .spell => { isSpell := true }
  | .permanentSpell => { isSpell := true }
  | .not .this => { other := true }
  | .not s => s.shape.negate
  | .intersection fs => fs.foldl (fun acc f => acc.meet f.shape) {}
  | .union [] => {}
  | .union (f :: fs) => fs.foldl (fun acc g => acc.join g.shape) f.shape
  | .this | .source _ | .controller _ | .opponent _ | .owner _ | .target _ _
  | .targets _ _ _ | .targetSet _ _ _ _ | .targetReference _
  | .selected _ _ _ | .player
  | .wasObjectOfAction _ | .replacingObject _ | .wasCreatedByAction _
  | .hostOf _ | .inGraveyard | .inDeck | .supertype _ | .variable _ | .topOfLibrary _ => {}

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
    if s.other && s.types.eqTypes [.creature] then .anotherCreatureYouControl
    else if s.types.eqTypes [.artifact, .creature] then .artifactOrCreatureYouControl
    else if s.types.eqTypes [.creature] then .creatureYouControl
    else if s.types.eqTypes [.artifact] then .artifactYouControl
    else .permanent
  else if s.flying && s.types.eqTypes [.creature] then .creatureWithFlying
  else if s.types.eqTypes [.artifact, .enchantment] then .artifactOrEnchantment
  else if s.types.eqTypes [.creature] then .creature
  else if s.types.eqTypes [.artifact] then .artifact
  else .permanent

/-- The constraint a targeting selector matches, if it announces targets. -/
def among? : Selector → Option Selector
  | .target _ among => some among
  | .targets _ _ among => some among
  | .targetSet _ _ among _ => some among
  | _ => none

/-- True when this targeting selector is “any target”. -/
def leftoverAnyTarget? (s : Selector) : Bool :=
  s.among? == some .all || s == .all

/-- Any object. -/
def any : Selector := .all

/-- A land (CR 305). -/
def land : Selector := .cardType .land

/-- True when this selector includes `inDeck`. -/
def includesInDeck : Selector → Bool
  | .inDeck => true
  | .intersection (f :: fs) => includesInDeck f || includesInDeck (.intersection fs)
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
def basicLandInDeck (s : Selector) : Bool :=
  includesInDeck s && includesLand s && includesBasic s

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
  /-- Sacrifice a selected permanent (CR 701.17). -/
  | sacrifice : Selector → Cost
  /-- Sacrifice that many permanents matching the selector (CR 701.17). -/
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
  | .sacrifice s => s.shape.types.eqTypes [.artifact, .creature]
  | .sacrificeCount s 1 => s.shape.types.eqTypes [.artifact, .creature]
  | .or cs =>
    cs.any fun
      | .sacrifice s => s.shape.types.eqTypes [.artifact, .creature]
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

/-- True when a cost discards this object. -/
def discardsThis : List Cost → Bool
  | [] => false
  | .discard s :: rest =>
    (s == .this || s == .source .this) || discardsThis rest
  | _ :: rest => discardsThis rest

end Cost

/-- Kind of counter placed by `putCounter` (CR 122.1). -/
inductive CounterKind where
  /-- A +1/+1 counter. -/
  | plusOnePlusOne
deriving Repr, Inhabited, BEq

/-- A boolean check used by a conditional effect or action. -/
inductive Condition where
  /-- True when any object matching the selector exists. -/
  | any : Selector → Condition
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
  /-- A keyword ability that is printed with a target, e.g. Enchant
  creature (CR 702.5). The `Nat` numbers the target so later clauses can
  refer to it. -/
  | keywordWithTarget : Keyword → Nat → Selector → Ability
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
  | addPowerToughness : Selector → Int → Int → ContinuousEffect
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
  /-- The selected object's power and toughness are each equal to the
  number of objects matching the second selector. -/
  | setPowerToughnessEqualToCount : Selector → Selector → ContinuousEffect
  /-- The selected player may play that many additional lands on each of
  their turns (CR 305.2b). -/
  | increaseLandPlayLimit : Selector → Nat → ContinuousEffect
deriving Repr, Inhabited, BEq

/-- What a spell or ability does. `CardAction` is the printed-card name for
this tree; player input uses `Action` in `Game`. -/
inductive CardAction where
  | continuous : List ContinuousEffect → Trigger → CardAction
  | tap : Selector → CardAction
  | untap : Selector → CardAction
  | dealDamage : Selector → Selector → Nat → CardAction
  /-- The selected player divides that much damage from the source among
  the selected objects (CR 601.2d). -/
  | divideDamage : Selector → Selector → Selector → Nat → CardAction
  | draw : Selector → Nat → CardAction
  | scry : Selector → Nat → CardAction
  | sequence : List CardAction → CardAction
  /-- Perform the given actions only when the condition holds. -/
  | if : Condition → List CardAction → CardAction
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
  /-- Exchange control of the selected objects. -/
  | exchangeControl : Selector → CardAction
  /-- Destroy the selected permanent (CR 701.7). -/
  | destroy : Selector → CardAction
  /-- The selected player gains that much life (CR 118.3). -/
  | gainLife : Selector → Nat → CardAction
  /-- The selected player chooses one or more of the listed actions. -/
  | playerSelectAction : Selector → Range → List CardAction → CardAction
  /-- Put the selected object on top of its owner's library. -/
  | putOnTopOfLibrary : Selector → CardAction
  /-- Put the selected object on the bottom of its owner's library. -/
  | putOnBottomOfLibrary : Selector → CardAction
  /-- Number this action so later clauses can refer to it. -/
  | actionId : Nat → CardAction → CardAction
  /-- The selected player loses that much life (CR 118.3). -/
  | loseLife : Selector → Nat → CardAction
  /-- The controller sacrifices the selected object (CR 701.17). -/
  | sacrifice : Selector → CardAction
  /-- Return the selected object to its owner's hand. -/
  | returnToHand : Selector → CardAction
  /-- Put the selected object onto the battlefield. -/
  | putOntoBattlefield : Selector → CardAction
  /-- Put the selected object onto the battlefield in the given state
  (CR 110.5). -/
  | putOntoBattlefieldInState : Selector → CardState → CardAction
  /-- Search the selected player's library. Nested actions may move or
  choose cards from that library while they are visible, then shuffle
  (CR 701.19). -/
  | searchLibraryThenShuffle : Selector → List CardAction → CardAction
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
  /-- The first selected player chooses a color. The second selected
  player adds X mana of that color. -/
  | addManaAnyColor : Selector → Selector → Nat → CardAction
  /-- The first selected player chooses a color. The second selected
  player adds X mana of that color, where X is the third selected
  object's power. -/
  | addManaAnyColorEqualToPower : Selector → Selector → Selector → CardAction
  /-- The selected player adds mana matching the listed symbols, all at
  once (CR 106.4). To let the player choose among symbols, use
  `playerSelectAction`. To add any color, use
  `addManaAnyColor`. -/
  | addMana : Selector → List ManaSymbol → CardAction
deriving Repr, Inhabited, BEq
end

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
  | .setPowerToughnessEqualToCount who _ => who
  | .increaseLandPlayLimit who _ => who

/-- Combined +P/+T if every effect is `addPowerToughness`. -/
def addedPT? : List ContinuousEffect → Option (Int × Int)
  | [] => some (0, 0)
  | .addPowerToughness _ p t :: rest =>
    match addedPT? rest with
    | some (p', t') => some (p + p', t + t')
    | none => none
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
  | .setPowerToughnessEqualToCount _ _ :: _ => none
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
    | .spell | .permanentSpell | .player
    | .wasObjectOfAction _ | .replacingObject _ | .wasCreatedByAction _
    | .hostOf _ | .inGraveyard | .inDeck | .supertype _ | .variable _ | .topOfLibrary _ => none
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

/-- Target creature gets +P/+T (Giant Growth, Dark Deed). -/
def leftoverTargetPump? (effects : List ContinuousEffect) : Option (Int × Int) :=
  match ContinuousEffect.addedPT? effects, ContinuousEffect.targetingSelector? effects with
  | some (p, t), some sel =>
    if sel.toTargetKind == .creature then some (p, t) else none
  | _, _ => none

/-- You may play an additional land this turn. -/
def leftoverIncreaseLandPlayLimit? : List ContinuousEffect → Bool
  | [.increaseLandPlayLimit who 1] =>
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
  | .sequence [.draw _who n, .discard _p 1] => some n
  | _ => none

/-- Put a +1/+1 counter on up to one target creature; a target player gains
that much life. -/
def leftoverPlusOneAndGainLife? : CardAction → Option Nat
  | .sequence [
      .putCounter sel .plusOnePlusOne 1,
      .gainLife who n
    ] =>
    let upToOneCreature :=
      match sel with
      | .targets _ (.range 0 1) among => among.shape.types.eqTypes [.creature]
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

/-- Exile the top card; you may play it until the end of your next turn. -/
def leftoverExileTopPlayUntilEndOfNextTurn? : CardAction → Bool
  | .sequence [
      .actionId id (.exile (.topOfLibrary who)),
      .continuous [.canPlay permit (.wasCreatedByAction created)] _
    ] =>
    id == created &&
      who == .controller .this &&
      permit == .controller .this
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

/-- Target creature gets +P/+T; if it would die this turn, exile it instead. -/
def leftoverPumpAndExileIfDies? : CardAction → Option (Int × Int)
  | .continuous effects _ =>
    let pt :=
      effects.findSome? fun
        | .addPowerToughness _ p t => some (p, t)
        | _ => none
    let replacesDie :=
      effects.any fun
        | .replace (.putToGraveyard _) _ => true
        | _ => false
    if replacesDie then pt else none
  | _ => none

/-- Target creature gets +P/+T and gains lifelink. -/
def leftoverPumpAndLifelink? : CardAction → Option (Int × Int)
  | .continuous effects _ =>
    let pt :=
      effects.findSome? fun
        | .addPowerToughness _ p t => some (p, t)
        | _ => none
    let lifelink :=
      effects.any fun
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
  | .sequence [.draw (.target _ .player) cards, .loseLife _ life] => some (cards, life)
  | _ => none

/-- You draw cards and lose life. -/
def leftoverDrawLoseLifeSelf? : CardAction → Option (Nat × Nat)
  | .sequence [.draw (.controller .this) cards, .loseLife (.controller .this) life] =>
    some (cards, life)
  | _ => none

/-- Target creature gets +P/+T and gains keywords. -/
def leftoverPumpAndGrantKeywords? : CardAction → Option (Int × Int × Keywords)
  | .continuous effects _ =>
    let pt :=
      effects.findSome? fun
        | .addPowerToughness _ p t => some (p, t)
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
  | [.putOntoBattlefieldInState obj .tapped] =>
    obj == .this || obj == .source .this
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
  | [.putOntoBattlefieldInState sel .tapped] =>
    match sel.selectedAmong? with
    | some among =>
      if among.basicLandInDeck then some Effect.searchBasicLandTapped else none
    | none => none
  | [.defineVariable id sel, .reveal (.variable id'), .returnToHand (.variable id'')] =>
    if id == id' && id == id'' then
      match sel.selectedAmong? with
      | some among =>
        if among.basicLandInDeck then some Effect.searchBasicLandToHand
        else
          match among.includedSubtype? with
          | some t =>
            if among.includesInDeck then some (Effect.searchLandTypeToHand t) else none
          | none => none
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

/-- Enters-the-battlefield library searches. -/
def leftoverEnterSearch? : List CardAction → Option TriggeredAbility
  | [.putOntoBattlefield sel] =>
    match sel.selectedAmong? with
    | some among =>
      if among.includesInDeck && among.includedSubtype? == some "Forest" then
        some TriggeredAbility.onEnterSearchForest
      else none
    | none => none
  | [.defineVariable id sel, .reveal (.variable id'), .returnToHand (.variable id'')] =>
    if id == id' && id == id'' then
      match sel.selectedAmong? with
      | some among =>
        if among.basicLandInDeck then
          some TriggeredAbility.onEnterSearchBasicToHand
        else none
      | none => none
    else none
  | _ => none

/-- Compile `continuous` effects, reading targeting from `target`
and mass application from constraint selectors. -/
def compile (action : CardAction) (asAbility : Bool) : Effect :=
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
              | some (p, t, k) => Effect.pumpAndGrantKeywords p t k
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
                  | .dealDamage _source victim n => compileDamage victim n asAbility
                  | .divideDamage _who _source victim n => compileDamage victim n asAbility
                  | .draw _who n =>
                    if asAbility then Effect.abilityDraw n else Effect.draw n
                  | .scry _who n => Effect.scry n
                  | .sequence (a :: _) => compile a asAbility
                  | .sequence [] => continuousEffect none [] asAbility
                  | .if _ (a :: _) => compile a asAbility
                  | .if _ [] => continuousEffect none [] asAbility
                  | .optional inner => compile inner asAbility
                  | .attach _ _ => Effect.untapPumpMaybeAttach 0 0
                  | .chooseMode (a :: _) => compile a asAbility
                  | .chooseMode [] => continuousEffect none [] asAbility
                  | .counter _ => Effect.counterSpell
                  | .preventable _ costs (.counter _) =>
                    Effect.counterUnlessPays (ManaCost.manaValue (Cost.manaCost costs))
                  | .preventable _ _ inner => compile inner asAbility
                  | .discard _ n => Effect.drawThenDiscard n
                  | .putCounter (.source .this) .plusOnePlusOne n =>
                    Effect.putPlusOnePlusOneOnSource n
                  | .putCounter _ _ _ => continuousEffect none [] asAbility
                  | .exile _ => continuousEffect none [] asAbility
                  | .exchangeControl _ => Effect.exchangeControlSharingType
                  | .destroy s =>
                    if s.toTargetKind == .creatureWithFlying then
                      Effect.destroyCreatureWithFlying
                    else if asAbility && s.toTargetKind == .artifactOrEnchantment then
                      Effect.destroyTargetArtifactOrEnchantment
                    else if asAbility && s.toTargetKind == .permanent then
                      Effect.destroyTargetPermanent
                    else Effect.destroyCreature
                  | .gainLife _ n => Effect.gainLife n
                  | .playerSelectAction _ _ actions =>
                    match actions with
                    | [.putOnTopOfLibrary _, .putOnBottomOfLibrary _] =>
                      Effect.putOnTopOrBottom
                    | a :: _ => compile a asAbility
                    | [] => continuousEffect none [] asAbility
                  | .putOnTopOfLibrary _ => Effect.putOnTopOrBottom
                  | .putOnBottomOfLibrary _ => Effect.putOnTopOrBottom
                  | .actionId _ inner => compile inner asAbility
                  | .loseLife _ _ => continuousEffect none [] asAbility
                  | .sacrifice _ => continuousEffect none [] asAbility
                  | .returnToHand _ => Effect.returnFromGraveyardToHand
                  | .putOntoBattlefield _ => continuousEffect none [] asAbility
                  | .putOntoBattlefieldInState _ _ => continuousEffect none [] asAbility
                  | .searchLibraryThenShuffle _ _ =>
                    continuousEffect none [] asAbility
                  | .defineVariable _ _ => continuousEffect none [] asAbility
                  | .forEachVariable _ _ _ => continuousEffect none [] asAbility
                  | .reveal _ => continuousEffect none [] asAbility
                  | .dealDamageEqualToPower _ _ =>
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
  { cost :=
      { mana := Cost.manaCost costs
        payLife := Cost.lifePaid costs
        tap := Cost.hasTapSymbol costs
        sacrificeSource := Cost.sacrificesThis costs
        sacrificeAnotherCreatureOrArtifact := Cost.sacrificesArtifactOrCreature costs
        discardSource := Cost.discardsThis costs }
    effect := action.toAbilityEffect
    onceEachTurn
    activateFromHand := Cost.discardsThis costs }

def toActivatedAbility? : Ability → Option ActivatedAbility
  | .keywordWithCost .equip costs =>
    some {
      cost := { mana := Cost.manaCost costs }
      effect := Effect.attachToTargetCreatureYouControl
      onlyAsSorcery := true }
  | .keywordWithCost (.subtypecycling st) costs =>
    some {
      cost := { mana := Cost.manaCost costs, discardSource := true }
      effect := Effect.searchLandTypeToHand st.toString
      activateFromHand := true }
  | .activated costs action => some (activatedAbility costs action)
  | .activatedIf (.didNotHappen (.abilityWithIdActivated _) .turnStart) costs action =>
    some (activatedAbility costs action true)
  | .activatedIf (.timeToCastSorcery _) costs
      action@(.returnToHand (.intersection [.inGraveyard, .source .this])) =>
    some { activatedAbility costs action with
      onlyAsSorcery := true
      activateFromGraveyard := true }
  | .activatedIf (.timeToCastSorcery _) costs action =>
    some { activatedAbility costs action with onlyAsSorcery := true }
  | .activatedIf
      (.and (.turn _) (.didNotHappen (.abilityWithIdActivated _) .turnStart))
      costs action =>
    some { activatedAbility costs action true with onlyDuringYourTurn := true }
  | .abilityId _ inner => toActivatedAbility? inner
  | _ => none

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
  | .triggered (.attack .this .all) (.if (.any among) [.gainLife _ n]) =>
    if among.shape.ferocious then
      some (TriggeredAbility.onAttackFerociousGainLife n)
    else none
  | .triggered (.attack .this .all) (.if (.any among) [.continuous effects _]) =>
    if among.shape.ferocious then
      match CardAction.leftoverSourcePump? effects with
      | some (p, t) => some (TriggeredAbility.onAttackFerociousSourceGets p t)
      | none => none
    else none
  | .triggered (.attack .this .all) (.scry _ n) =>
    some (TriggeredAbility.onAttackScry n)
  | .triggered (.block _ src) (.dealDamage dealer dest 1) =>
    if src == .this && dealer == .this && dest == .blocking .this then
      some TriggeredAbility.onBecomesBlockedDeal1ToBlockers
    else none
  | .triggered (.castSpell among) (.dealDamage _ (.opponent _) n) =>
    if among.shape.types.eqTypes [.instant, .sorcery] && among.shape.sameController then
      some (TriggeredAbility.onCastInstantOrSorceryDealDamageToEachOpponent n)
    else none
  | .triggered (.enter .this) (.draw (.controller .this) n) =>
    some (TriggeredAbility.onEnterDraw n)
  | .triggered (.enter .this) (.scry _ n) =>
    some (TriggeredAbility.onEnterScry n)
  | .triggered (.enter .this) (.gainLife _ n) =>
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
      | _ => none
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
  | .triggered (.combatDamage .this .player) (.draw _ n) =>
    some (TriggeredAbility.onCombatDamageDraw n)
  | .triggered (.die .this) (.continuous effects _duration) =>
    match ContinuousEffect.targetingSelector? effects, ContinuousEffect.addedPT? effects with
    | some sel, some (p, t) =>
      if sel.toTargetKind == .oppCreature then
        some (TriggeredAbility.onDiesOppCreatureGets p t)
      else none
    | _, _ => none
  | .triggered (.die .this) (.draw _ n) =>
    some (TriggeredAbility.onDiesDraw n)
  | .triggered (.die .this) (.dealDamageEqualToPower _ dest) =>
    if dest.toTargetKind == .oppCreature then
      some TriggeredAbility.onDiesDealDamageEqualToPowerToOppCreature
    else none
  | .triggered (.dieSimultaneously among _) (.scry _ n) =>
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
        .loseLife (.opponent _) n]) =>
    some (TriggeredAbility.onEnterExileOppGyCardOppsLoseLife n)
  | .triggered (.enter .this) (.discard (.opponent _) 1) =>
    some TriggeredAbility.onEnterEachOpponentDiscards
  | .triggered (.enter .this)
      (.divideDamage _ _ (.targets _ (.range 1 maxTargets) _) amount) =>
    some (TriggeredAbility.onEnterDealDividedDamage amount maxTargets)
  | .triggered
      (.or (.enter .this) (.attack .this .all))
      (.divideDamage _ _ (.targets _ (.range 1 maxTargets) _) amount) =>
    some (TriggeredAbility.onEnterOrAttackDealDividedDamage amount maxTargets)
  | .triggered (.enter .this)
      (.sequence [
        .optional (.actionId id (.discard _ 1)),
        .if (.happened (.actionWithId id') _) [.draw _ n]]) =>
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
    if among.shape.artifactYouControl then
      some TriggeredAbility.onArtifactYouControlEntersDraw
    else none
  | .triggered (.enter among) (.continuous effects _duration) =>
    if among.shape.anotherElfYouControl then
      match CardAction.leftoverSourcePump? effects with
      | some (1, 1) => some TriggeredAbility.onAnotherElfYouControlEntersGets1
      | _ => none
    else if among.shape.landYouControl then
      match CardAction.leftoverSourcePump? effects with
      | some (p, t) => some (TriggeredAbility.onLandYouControlEntersGets p t)
      | none => none
    else none
  | .triggered (.enter .this) action =>
    match CardAction.leftoverUntapPlusOneIfSubtype? action with
    | some st => some (TriggeredAbility.onEnterUntapOtherPlusOneIfSubtype st)
    | none => none
  | .triggered (.enter among) action =>
    match CardAction.leftoverPlusOneVigilance? action with
    | some 2 =>
      if among.shape.landYouControl then
        some TriggeredAbility.onLandYouControlEntersPlusOneVigilance
      else none
    | _ => none
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
  costReductionIfTargetAttacking : Nat := 0
  costReductionIfCreatureDied : Nat := 0
  costReductionIfYouControl : Option (Nat × String) := none
  additionalCostSacrificeArtifactOrCreature : Bool := false
  additionalCostOrPayGeneric : Option Nat := none
  extraLandIfOtherSubtype : Option String := none
  staticAbilities : Array StaticAbility := #[]
  tapAddMana : Array ManaType := #[]
  tapAddAnyColorEqualToPower : Bool := false
  tapAddOneOf : Array ManaType := #[]
  entersTapped : Bool := false
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
  | [.increaseLandPlayLimit who 1] =>
    if who == .controller .this then among.shape.anotherSubtypeYouControl
    else none
  | _ => none

def applyContinuousEffect (b : CardFace) : ContinuousEffect → CardFace
  | .gainAbility (.hostOf .this) (.keyword k) =>
    pushHostBonus b 0 0 k.toKeywords
  | .gainAbility _ _ => b
  | .addPowerToughness (.hostOf .this) p t =>
    pushHostBonus b p t Keywords.none
  | .addPowerToughness _ _ _ => b
  | .if (.any among) inners =>
    match extraLandIfOtherSubtype? among inners with
    | some t => { b with extraLandIfOtherSubtype := some t }
    | none => applyIfShape b among.shape inners
  | .if (.targetsIncludeAny _ among) inners => applyIfShape b among.shape inners
  | .if (.anySubtype among st) inners =>
    match inners with
    | [.increaseLandPlayLimit who 1] =>
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
  | .if (.happened _ _) _ => b
  | .if (.timeToCastSorcery _) _ => b
  | .if (.turn _) _ => b
  | .if (.and _ _) _ => b
  | .replace (.enter who) actions =>
    if (who == .this || who == .source .this) &&
        CardAction.leftoverEntersTapped? actions then
      { b with entersTapped := true }
    else b
  | .replace _ _ => b
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
  | .setPowerToughnessEqualToCount who among =>
    if (who == .this || who == .source .this) && among.shape.landYouControl then
      { b with
        staticAbilities :=
          b.staticAbilities.push .powerToughnessEqualLandsYouControl }
    else b
  | .increaseLandPlayLimit _ _ => b
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
  | .keywordWithCost k costs =>
    match (Ability.keywordWithCost k costs).toActivatedAbility? with
    | some ab => { b with activatedAbilities := b.activatedAbilities.push ab }
    | none => b
  | .keywordWithTarget _ _ _ => b
  | .activated costs action =>
    if CardAction.leftoverTapAddAnyColorEqualToPower? costs action then
      { b with tapAddAnyColorEqualToPower := true }
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
      tapAddOneOf := b.tapAddOneOf
      entersTapped := b.entersTapped
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
          (.putToGraveyard (.intersection [.wasObjectOfAction 1, .permanentSpell]))
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

-- Desolation Prowler: pay 2 life, +2/+2, once each turn.
#guard
  match
    (Ability.abilityId 1
      (.activatedIf
        (.didNotHappen (.abilityWithIdActivated 1) .turnStart)
        [.life 2]
        (.continuous [.addPowerToughness (.source .this) 2 2] .endOfTurn))).toActivatedAbility? with
  | some ab =>
    ab.effect == Effect.sourceGets 2 2 && ab.cost.payLife == 2 && ab.onceEachTurn
  | none => false

-- Ravening Warg: Ferocious attack, gain 2 life.
#guard Selector.shape
  (.intersection [
    .permanent,
    .cardType .creature,
    .controlled (.controller .this),
    .powerAtLeast 4]) |>.ferocious

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
            .powerAtLeast 4]))
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
    .ability (.static (.addPowerToughness (.hostOf .this) 2 1))
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
#guard (Keyword.subtypecycling .halfling).toKeywords == Keywords.none
#guard toString (Keyword.subtypecycling .halfling) == "Halflingcycling"

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
    (Ability.keywordWithCost
      (.subtypecycling .halfling)
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
        (.keywordWithCost (.subtypecycling .halfling) [.mana [.generic 4]])
    ]).toCardDef
  c.activatedAbilities.size == 1 &&
    c.activatedAbilities[0]!.activateFromHand &&
    c.activatedAbilities[0]!.cost.discardSource &&
    c.activatedAbilities[0]!.effect == Effect.searchLandTypeToHand "Halfling"

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
        .sacrifice
          (.intersection [
            .permanent,
            .union [.cardType .artifact, .cardType .creature]])]
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
        (.target 1 (.intersection [.permanent, .cardType .creature]))
        (-5) (-5),
        .replace
          (.putToGraveyard (.targetReference 1))
          [.exile (.replacingObject 1)]]
      .endOfTurn
  action.toEffect == Effect.pumpAndExileIfDies (-5) (-5)

#guard
  let action : CardAction :=
    .continuous
      [.addPowerToughness
        (.intersection [
          .permanent,
          .cardType .creature,
          .controlled (.target 1 .player)])
        (-1) (-1)]
      .endOfTurn
  action.toEffect == Effect.creaturesTargetPlayerGet (-1) (-1)

#guard
  let action : CardAction :=
    .chooseMode [
      .continuous
        [.addPowerToughness
          (.target 1 (.intersection [.permanent, .cardType .creature]))
          (-5) (-5),
          .replace
            (.putToGraveyard (.targetReference 1))
            [.exile (.replacingObject 1)]]
        .endOfTurn,
      .continuous
        [.addPowerToughness
          (.intersection [
            .permanent,
            .cardType .creature,
            .controlled (.target 1 .player)])
          (-1) (-1)]
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
        (.target 1 (.intersection [.permanent, .cardType .creature]))
        2 2,
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
      5
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
    .ability (.static (.addPowerToughness (.hostOf .this) 2 0))
  ]).toCardDef.staticAbilities == #[.equippedCreatureGets 2 0]

-- Snowslope Hunter: sacrifice another creature or artifact; exile top; your turn, once.
#guard
  let action : CardAction :=
    .sequence [
      .actionId 1 (.exile (.topOfLibrary (.controller .this))),
      .continuous
        [.canPlay (.controller .this) (.wasCreatedByAction 1)]
        .endOfTurn]
  action.toAbilityEffect == Effect.exileTopPlayUntilEndOfNextTurn

#guard
  match
    (Ability.abilityId 1
      (.activatedIf
        (.and
          (.turn (.controller .this))
          (.didNotHappen (.abilityWithIdActivated 1) .turnStart))
        [.sacrifice
          (.intersection [
            .not .this,
            .permanent,
            .union [.cardType .artifact, .cardType .creature]])]
        (.sequence [
          .actionId 1 (.exile (.topOfLibrary (.controller .this))),
          .continuous
            [.canPlay (.controller .this) (.wasCreatedByAction 1)]
            .endOfTurn]))).toActivatedAbility? with
  | some ab =>
    ab.onlyDuringYourTurn &&
      ab.onceEachTurn &&
      ab.cost.sacrificeAnotherCreatureOrArtifact &&
      ab.effect == Effect.exileTopPlayUntilEndOfNextTurn
  | none => false

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
      (.continuous [.addPowerToughness (.source .this) 1 1] .endOfTurn)).toTriggeredAbility? with
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
        (.target 1 (.intersection [.permanent, .cardType .creature]))
        3 3]
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
        (.intersection [.permanent, .cardType .creature])
        (-4) (-4)]
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
          (.target 1 (.intersection [.permanent, .cardType .creature]))
          (-4) 0]
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
    .continuous [.increaseLandPlayLimit (.controller .this) 1] .endOfTurn
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
          [.increaseLandPlayLimit (.controller .this) 1]))
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
          (.target 1 (.intersection [.permanent, .cardType .creature]))
          2 0]
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
    .ability (.static (.addPowerToughness (.hostOf .this) 3 3))
  ]).toCardDef.staticAbilities == #[.enchantedCreatureGets 3 3]

#guard
  let action : CardAction := .draw (.controller .this) 2
  action.toAbilityEffect == Effect.abilityDraw 2

#guard
  (TraditionalCardDefinition.card [
    .ability (.activated [.sacrifice .this] (.draw (.controller .this) 2))
  ]).toCardDef.activatedAbilities[0]!.cost.sacrificeSource

#guard Selector.basicLandInDeck
  (.intersection [.inDeck, .cardType .land, .supertype .basic])

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
              .inDeck,
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
            (.intersection [.inDeck, .cardType .land, .supertype .basic]))
          .tapped]
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
              (.intersection [.inDeck, .subtype .forest]))])).toTriggeredAbility? with
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
                .inDeck,
                .cardType .land,
                .supertype .basic])),
          .reveal (.variable 1),
          .returnToHand (.variable 1)])).toTriggeredAbility? with
  | some ab => ab == TriggeredAbility.onEnterSearchBasicToHand
  | none => false

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

-- Dual land: enters tapped; tap-add one of two colors; counters on a typed creature.
#guard
  (TraditionalCardDefinition.card [
    .ability (
      .static
        (.replace
          (.enter .this)
          [.putOntoBattlefieldInState .this .tapped]))
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
              (.intersection [.inDeck, .subtype .halfling])),
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
  let action : CardAction := .dealDamage .this (.target 1 .all) 3
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
          .endOfTurn])).toTriggeredAbility? with
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
            .powerAtLeast 4]))
        [.continuous [.addPowerToughness (.source .this) 2 2] .endOfTurn])).toTriggeredAbility? with
  | some ab => ab == TriggeredAbility.onAttackFerociousSourceGets 2 2
  | none => false

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
                .controlled (.controller .this)]))
            2 0,
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
              .controlled (.controller .this)])
            1 0,
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

#guard
  match
    (Ability.triggered
      (.block .all .this)
      (.dealDamage .this (.blocking .this) 1)).toTriggeredAbility? with
  | some ab => ab == TriggeredAbility.onBecomesBlockedDeal1ToBlockers
  | none => false

#guard
  match
    (Ability.triggered
      (.castSpell
        (.intersection [
          .union [.cardType .instant, .cardType .sorcery],
          .controlled (.controller .this)]))
      (.dealDamage .this (.opponent (.controller .this)) 2)).toTriggeredAbility? with
  | some ab => ab == TriggeredAbility.onCastInstantOrSorceryDealDamageToEachOpponent 2
  | none => false

#guard
  (Ability.triggered
    (.castSpell (.union [.cardType .instant, .cardType .sorcery]))
    (.dealDamage .this (.opponent (.controller .this)) 2)).toTriggeredAbility?.isNone

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
    .ability (.static (.addPowerToughness (.hostOf .this) 1 0)),
    .ability (.static (.gainAbility (.hostOf .this) (.keyword .haste)))
  ]).toCardDef.staticAbilities ==
    #[.enchantedCreatureGetsAndHas 1 0 Keyword.haste]

#guard
  match
    (Ability.keywordWithCost (.subtypecycling .mountain) [.mana [.generic 1]]).toActivatedAbility? with
  | some ab =>
    ab.activateFromHand &&
      ab.cost.discardSource &&
      ab.effect == Effect.searchLandTypeToHand "Mountain"
  | none => false

end Mtg.Engine
