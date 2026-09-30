import Mtg.Engine.Card.Definition.Cost

/-!
# Printed card parts

`Condition`, `CardState`, and the mutually inductive `Ability`,
`ContinuousEffect`, `CardAction`, and `CardPart`. An activated ability has
an action, and a continuous effect may grant an ability.

`PredefinedToken` is the printed characteristics of Treasure and Food
(CR 111.10).
-/

namespace Mtg.Engine

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
  /-- True when the selected player has an enduring story. -/
  | enduringStory : Selector → Condition
  /-- True when both conditions hold. -/
  | and : Condition → Condition → Condition
  /-- True when the condition does not hold. -/
  | not : Condition → Condition
  /-- True when the first value is less than the second. -/
  | less : Value → Value → Condition
  /-- True when the first value is less than or equal to the second. -/
  | lessOrEqual : Value → Value → Condition
  /-- True when the first value is greater than the second. -/
  | greater : Value → Value → Condition
  /-- True when the first value is greater than or equal to the second. -/
  | greaterOrEqual : Value → Value → Condition
  /-- True when the two values are equal. -/
  | equal : Value → Value → Condition
deriving Repr, Inhabited, BEq

/-- Status a permanent has as it enters the battlefield (CR 110.5). -/
inductive CardState where
  /-- The permanent enters tapped. -/
  | tapped
  /-- The permanent enters attacking (CR 508.4a). -/
  | attacking
  /-- The permanent enters under the selected player's control (CR 110.2). -/
  | controlled : Selector → CardState
  /-- The permanent enters attached to the selected object (CR 303.4f). -/
  | attachedTo : Selector → CardState
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
  /-- A keyword ability that grants another ability. `∞ — [ability]`
  (CR 702.186) is `keywordWithAbility .infinity`: as long as this
  permanent is harnessed, it has that ability. -/
  | keywordWithAbility : Keyword → Ability → Ability
  | activated : List Cost → CardAction → Ability
  /-- An activated ability that may be used only when the condition holds. -/
  | activatedIf : Condition → List Cost → CardAction → Ability
  /-- An activated ability that may be used only when the condition holds,
  together with a static effect of that ability. The static effect is part
  of the ability, so `.this` in it is this ability. -/
  | activatedWithStaticIf : Condition → List Cost → CardAction → ContinuousEffect → Ability
  /-- An activated ability that functions while this card is in a graveyard
  (CR 113.6) and may be used only when the condition holds. -/
  | graveyardActivatedIf : Condition → List Cost → CardAction → Ability
  /-- Number this ability so later clauses can refer to it. -/
  | abilityId : Nat → Ability → Ability
  | triggered : Trigger → CardAction → Ability
  /-- Fires for the trigger only while the condition holds. The condition is
  checked when the trigger event occurs (CR 603.2). It is not an intervening
  “if” (CR 603.4 / 608.2a), so it is not checked again when the ability
  resolves. Printed “while …” uses this; `CardAction.if` is the resolution
  check. -/
  | triggeredWhile : Trigger → Condition → CardAction → Ability
  | static : ContinuousEffect → Ability
  /-- A static ability that functions while this spell is on the stack
  (CR 604.2), e.g. a cost reduction. -/
  | stackStatic : ContinuousEffect → Ability
  /-- A static ability that functions in every zone (CR 113.6), including
  before this card is put onto the stack. -/
  | everywhereStatic : ContinuousEffect → Ability
deriving Repr, Inhabited, BEq

/-- A continuous effect granted by a spell or ability. -/
inductive ContinuousEffect where
  | gainAbility : Selector → Ability → ContinuousEffect
  /-- Apply the given continuous effects only when the condition holds. -/
  | if : Condition → List ContinuousEffect → ContinuousEffect
  | reduceCost : Selector → List Cost → ContinuousEffect
  /-- Reduce the cost of the selected spell by `costs`, substituting `{X}`
  with the given value (CR 601.2f / 107.3). -/
  | reduceCostWithX : Selector → List Cost → Value → ContinuousEffect
  /-- An additional cost to cast the selected spell (CR 601.2b). -/
  | additionalCost : Selector → List Cost → ContinuousEffect
  /-- You may pay `costs` rather than pay the cost of the selected ability
  (CR 118.9). This is an alternative cost, not a cost reduction (CR 118.7). -/
  | alternativeCost : Selector → List Cost → ContinuousEffect
  /-- Replace the trigger with the given actions (CR 614). -/
  | replace : Trigger → List CardAction → ContinuousEffect
  /-- The selected trigger is forbidden (CR 509 / 614). -/
  | forbid : Trigger → ContinuousEffect
  /-- The selected player may cast the selected card without paying its
  mana cost. -/
  | canCastWithoutPayingManaCost : Selector → Selector → ContinuousEffect
  /-- The selected player may play the selected card. -/
  | canPlay : Selector → Selector → ContinuousEffect
  /-- The selected object's base power becomes the given value. -/
  | setBasePower : Selector → Value → ContinuousEffect
  /-- The selected object's base toughness becomes the given value. -/
  | setBaseToughness : Selector → Value → ContinuousEffect
  /-- The selected object gains the given card type in addition to its
  other types (CR 205.1 / 613.1). -/
  | gainType : Selector → CardType → ContinuousEffect
  /-- The selected object gains the given subtype in addition to its other
  types (CR 205.3 / 613.1). -/
  | gainSubtype : Selector → CardSubtype → ContinuousEffect
  /-- The selected object has all subtypes of the given card type
  (CR 205.3 / 702.72). -/
  | gainAllSubtypes : Selector → CardType → ContinuousEffect
  /-- The selected object's power becomes the given value. -/
  | setPower : Selector → Value → ContinuousEffect
  /-- The selected object's toughness becomes the given value. -/
  | setToughness : Selector → Value → ContinuousEffect
  /-- The selected objects get additional power equal to the given value. -/
  | addPower : Selector → Value → ContinuousEffect
  /-- The selected objects get additional toughness equal to the given value. -/
  | addToughness : Selector → Value → ContinuousEffect
  /-- The selected player may play that many additional lands on each of
  their turns (CR 305.2b). -/
  | increaseLandPlayLimit : Selector → Value → ContinuousEffect
  /-- The selected spell may be cast as though it had flash when the condition
  holds (CR 601.3 / 702.8). `you` in that condition is `Selector.caster`,
  the player who would cast the spell, not necessarily its controller or
  owner. The spell does not gain the flash keyword. -/
  | canBeCastAsThoughWithFlashIf : Selector → Condition → ContinuousEffect
  /-- The selected permanent doesn't untap during its controller's untap
  step (CR 502.3). -/
  | doesntUntap : Selector → ContinuousEffect
  /-- Objects matching the first selector can't attack the second unless
  their controller pays `costs` for each of them. -/
  | cantAttackUnlessPays : Selector → Selector → List Cost → ContinuousEffect
  /-- The selected objects lose all abilities (CR 613.1f).
  Abilities added by a later effect still apply. A static ability generates
  this effect while its source is on the battlefield (CR 611.3a). A resolving
  spell or ability applies it until end of turn to the objects that match
  when it resolves (CR 611.2a / 611.2c). -/
  | removeAllAbilities : Selector → ContinuousEffect
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
  /-- The selected player chooses whether to perform the action.
  Printed “you may” is `.controller .this`. “That player may” is that player. -/
  | optional : Selector → CardAction → CardAction
  | attach : Selector → Selector → CardAction
  /-- Choose that many distinct modes (CR 700.2). Each mode is chosen at most once.
  `range 1 1` is “choose one”. `range 1 2` is “choose one or both”. -/
  | chooseUniqueModes : Range → List CardAction → CardAction
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
  | putCounter : Selector → CounterKind → Value → CardAction
  /-- Remove that many counters of the given kind from the selected object. -/
  | removeCounter : Selector → CounterKind → Value → CardAction
  /-- Remove every counter from the selected object. -/
  | removeAllCounters : Selector → CardAction
  /-- Exile the selected object. -/
  | exile : Selector → CardAction
  /-- Exile the selected objects until the second permanent leaves the
  battlefield. They return under their owner's control (CR 610.3). The
  return is a one-shot effect of the spell or ability that exiled them,
  not a triggered ability. -/
  | exileUntil : Selector → Selector → CardAction
  /-- Exile the selected objects face down (CR 406.3). -/
  | exileFaceDown : Selector → CardAction
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
  /-- Number this action so later clauses can refer to it.
  The number is unique among action ids in a `TraditionalCardDefinition`.
  It is not a target number. -/
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
  /-- Bind the selected objects to this numbered selector variable. -/
  | defineSelectorVariable : Nat → Selector → CardAction
  /-- Record this value under the numbered variable. The value is computed
  when the action resolves, so a later `Value.variable` sees that result
  after the objects it measured have changed zones. -/
  | defineValueVariable : Nat → Value → CardAction
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
  /-- The selected player chooses one of the listed mana symbols and adds
  that many mana of the chosen symbol. -/
  | addManaOfOneColor : Selector → List ManaSymbol → Value → CardAction
  /-- The selected player adds that much mana in any combination of the
  listed colors (CR 106.4). Each mana may be a different color. -/
  | addManaInAnyCombination : Selector → List ManaSymbol → Value → CardAction
  /-- The selected player adds mana matching the listed symbols, all at
  once (CR 106.4). To let the player choose among symbols, use
  `playerSelectAction`. To add one chosen color, use
  `addManaOfOneColor`. To add mana in any combination of colors, use
  `addManaInAnyCombination`. -/
  | addMana : Selector → List ManaSymbol → CardAction
  /-- The selected object or player performs a keyword action (CR 701),
  e.g. recruit, amass Goblins 1, connive 1, behold an Elf, or harness
  this permanent. -/
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
  /-- Shuffle the selected object into its owner's library (CR 701.20). -/
  | shuffleIntoOwnersLibrary : Selector → CardAction
  /-- Look at the selected cards (CR 701.16). -/
  | lookAt : Selector → CardAction
  /-- Put the selected cards on the bottom of their owner's library in a
  random order (CR 401.4). -/
  | putOnLibraryBottomInRandomOrder : Selector → CardAction
  /-- The selected player chooses an existing creature type (CR 205.3m).
  Number it with `actionId` so `Selector.hasCreatureTypeChosenByAction` can
  refer to the choice. -/
  | chooseCreatureType : Selector → CardAction
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
  this for their color. An empty list is colorless (CR 105.2c). -/
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
      (.addManaOfOneColor (.controller .this) ManaSymbol.anyColor 1))
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

end Mtg.Engine
