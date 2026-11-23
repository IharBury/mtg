import Mtg.Engine.Card.Counter
import Mtg.Engine.Card.Effect
import Mtg.Engine.Card.TriggerPattern

/-!
# Unified triggered abilities (CR 113.3c / 603 / 605.1b / 700.1 / 714.2b,d)

Helpers, reusable CR 603.4 condition constructors, modal inspection, structural
CR 605.1b `isManaAbility`, and CR 714.2b/d Saga chapter helpers for the unified
`TriggeredAbility` defined in `Mtg/Engine/Card/Ability.lean`.
-/

namespace Mtg.Engine

namespace TriggeredAbility

/-- English for “divided as you choose among …” (CR 601.2d). -/
def dividedAmong (maxTargets : Nat) : String :=
  if maxTargets == 3 then "one, two, or three targets"
  else if maxTargets == 1 then "one target"
  else s!"up to {maxTargets} targets"

/-! ### Reusable CR 603.4 / 603.2 `Condition` constructors -/

/-- `"you control a creature with power ≥ n"` (Ferocious = 4). -/
def condControlCreaturePowerAtLeast (n : Int) : Condition :=
  .exists (.inZones .battlefield (.all #[
    .hasType .creature, .controlledBy .you, .stat .power .ge (.const n)]))

/-- `"you gained n or more life this turn"`. -/
def condGainedLifeAtLeast (n : Nat) : Condition :=
  .cmp .ge (.playerMetric .lifeGainedThisTurn .you) (.const n)

/-- `"you've drawn n or more cards this turn"`. -/
def condDrawnAtLeast (n : Nat) : Condition :=
  .cmp .ge (.playerMetric .cardsDrawnThisTurn .you) (.const n)

/-- `"you didn't cast a spell this turn"`. -/
def condCastNoSpellThisTurn : Condition :=
  .cmp .eq (.playerMetric .spellsCastThisTurn .you) (.const 0)

/-- `"two or more creatures died this turn"` (`n = 2`) or `"three or more ..."` (`n = 3`). -/
def condCreaturesDiedThisTurn (n : Nat) : Condition :=
  .turnHistory (.eventOccurredThisTurn .any (.permanentDied (.hasType .creature) n))

/-- `"an opponent was dealt noncombat damage last turn"`. -/
def condOpponentDealtNoncombatDamageLastTurn : Condition :=
  .turnHistory (.eventOccurredLastTurn .opponent (.dealtDamage false true))

/-- `"you've activated a loyalty ability this turn"`. -/
def condActivatedLoyaltyThisTurn : Condition :=
  .turnHistory (.eventOccurredThisTurn .you .activatedLoyalty)

/-- `"it isn't a token"` (the source object). -/
def condSourceNotToken : Condition :=
  Condition.thisMatches (.isToken false)

/-- `"you cast it"` (the source object). -/
def condSourceWasCast : Condition :=
  Condition.thisMatches .wasCast

/-- `"this permanent has counters on it"`. -/
def condSourceHasCounters : Condition :=
  Condition.thisMatches (.counterCount none .ge (.const 1))

/-- `"it had counters on it"` (the triggering subject). -/
def condTriggerSubjectHadCounters : Condition :=
  Condition.triggerSubjectMatches (.counterCount none .ge (.const 1))

/-- CR 702.176a: `"this permanent's impending cost was paid and it has a time counter on it"`. -/
def condImpendingPaidWithTimeCounter : Condition :=
  .all #[
    .castPred (.impendingPaid .this),
    .cmp .ge (.counterCount (some .time) .this) (.const 1)]

/-- `"its power is greater than this creature's power or its toughness is greater than this creature's toughness"`. -/
def condTriggerSubjectGreaterPT : Condition :=
  .all #[
    .exists .triggerSubject,
    .any #[
      .cmp .gt (.objectStat .power .triggerSubject) (.objectStat .power .this),
      .cmp .gt (.objectStat .toughness .triggerSubject) (.objectStat .toughness .this)]]

/-- `"you control five or more other Forests"`. -/
def condFiveOtherForests : Condition :=
  .cmp .ge
    (.aggregate .count .one (.inZones .battlefield (.all #[
      .otherThan .triggerSubject, .hasSubtype (.literal .forest), .controlledBy .you])))
    (.const 5)

/-- `"you control six or more lands"`. -/
def condControlLandsAtLeast (n : Nat) : Condition :=
  .cmp .ge
    (.aggregate .count .one (.inZones .battlefield (.all #[
      .hasType .land, .controlledBy .you])))
    (.const n)

/-- `"this creature isn't prepared"`. -/
def condSourceNotPrepared : Condition :=
  Condition.thisMatches (.not (.hasDesignation .prepared))

/-- `"you don't control a planeswalker"`. -/
def condControlNoPlaneswalker : Condition :=
  .not (.exists (.inZones .battlefield (.all #[.hasType .planeswalker, .controlledBy .you])))

/-- `"this creature is equipped"` (supports CR 608.2h LKI when source departed). -/
def condSourceIsEquipped : Condition :=
  Condition.thisMatches (.hasAttachment { zones := .battlefield, pred := .hasSubtype (.literal .equipment) })

/-- `"an artifact entered the battlefield under your control this turn"`. -/
def condArtifactEnteredThisTurn : Condition :=
  .turnHistory (.eventOccurredThisTurn .you (.permanentEntered (.hasType .artifact)))

/-- `"you control another Hero"`. -/
def condControlAnotherSubtype (sub : CardSubtype) : Condition :=
  .exists (.inZones .battlefield (.all #[
    .otherThan .this, .hasSubtype (.literal sub), .controlledBy .you]))

/-- `"you have fewer than n cards in hand"`. -/
def condHandSizeLessThan (n : Nat) : Condition :=
  .cmp .lt (.playerMetric .handSize .you) (.const n)

/-- `"you attacked with a {sub} or a {sub} entered under your control this turn"`. -/
def condAttackedOrEnteredSubtype (sub : CardSubtype) : Condition :=
  .any #[
    .turnHistory (.eventOccurredThisTurn .you (.attackedWith (.hasSubtype (.literal sub)) 1)),
    .turnHistory (.eventOccurredThisTurn .you (.permanentEntered (.hasSubtype (.literal sub))))]

/-- `"you're the monarch"`. -/
def condYouAreMonarch : Condition :=
  .playerPred .you .isMonarch

/-- `"this permanent is harnessed"` (CR 702.186 `∞`). -/
def condSourceHarnessed : Condition :=
  Condition.thisMatches (.hasDesignation .harnessed)

/-! ### Direct projections & modal helpers on `TriggeredAbility` -/

/-- Top-level `ModalSpec` carried in `ab.effect.body`, if any (CR 603.3c / 700.2). -/
def modalSpec? (ab : TriggeredAbility) : Option ModalSpec :=
  ab.effect.modalSpec?

/-- Modes of a modal triggered ability (`#[]` when non-modal). -/
def modeEffects (ab : TriggeredAbility) : Array Effect :=
  match ab.modalSpec? with
  | some spec => spec.modes
  | none => #[]

/-- True when this triggered ability is modal (`Instruction.chooseModes` in `ab.effect.body`). -/
def isModal (ab : TriggeredAbility) : Bool :=
  !ab.modeEffects.isEmpty

/-- Construct a modal triggered ability folding modes into `Instruction.chooseModes`. -/
def mkModal (pattern : TriggerPattern) (modes : Array Effect)
    (word? : Option TriggerWord := none)
    (grouping : BatchGrouping := .perOccurrence)
    (interveningIf? : Option Condition := none)
    (activeZones : Array ZoneKind := #[.battlefield])
    (limit : TriggerLimit := .unlimited)
    (minModes : ValueExpr := .const 1)
    (maxModes : ValueExpr := .const 1)
    (allowRepeat : Bool := false)
    (chooseAtResolution : Bool := false)
    (unusedThisTurn : Bool := false)
    (unusedEver : Bool := false) : TriggeredAbility :=
  { word := word?.getD pattern.defaultWord
    pattern
    grouping
    interveningIf?
    activeZones
    limit
    effect := {
      body := .chooseModes {
        minModes, maxModes, allowRepeat, chooseAtResolution, unusedThisTurn, unusedEver, modes
      }
    } }

/-- Whom this triggered ability may target (CR 115.1 / 603.3d). -/
def targetSpec (ab : TriggeredAbility) : TargetSpec :=
  ab.effect.targets

/-- True when putting this ability on the stack requires choosing a target. -/
def requiresTarget (ab : TriggeredAbility) : Bool :=
  ab.effect.requiresTarget

/-- True when zero targets is a legal announcement (CR 115.1c / 603.3d). -/
def allowsZeroTargets (ab : TriggeredAbility) : Bool :=
  ab.effect.allowsZeroTargets

/-- Upper bound on targets for announcements. -/
def maxTargets (ab : TriggeredAbility) : Nat :=
  ab.effect.maxTargetCount

/-- Divided-damage `(amount, maxTargets)`, if any (CR 601.2d). -/
def dividedDamage? (ab : TriggeredAbility) : Option (Nat × Nat) :=
  ab.effect.dividedDamage?

/-- True when this ability has `"This ability triggers only once each turn."` (CR 603.2h). -/
def onceEachTurn (ab : TriggeredAbility) : Bool :=
  ab.limit == .onceEachTurn

/-- True when this ability has `"Do this only once each turn."` (MSH 69). -/
def optionalOnceEachTurn (ab : TriggeredAbility) : Bool :=
  ab.limit == .optionalOnceEachTurn

/-- The N in an `"Nth time each turn"` limit, if any. -/
def nthEachTurn? (ab : TriggeredAbility) : Option Nat :=
  match ab.limit with
  | .nthEachTurn n => some n
  | _ => none

/-- Exact CR 603.10a–f look-back flag computed from `ab.pattern`. -/
def usesLookBack (ab : TriggeredAbility) : Bool :=
  ab.pattern.usesLookBack

/-- CR 603.3b part 2 flag: true iff this trigger's condition is another ability triggering. -/
def isAnotherAbilityTriggering (ab : TriggeredAbility) : Bool :=
  ab.pattern.isAnotherAbilityTriggering

/-- True when `ab.pattern` matches `pat` directly or as one of its `.or` disjuncts
(unwrapping any `.whenCond` guard). -/
def firesOn (ab : TriggeredAbility) (pat : TriggerPattern) : Bool :=
  ab.pattern.flattenOr.any fun p =>
    p == pat || match p with
      | .whenCond inner _ => inner == pat
      | _ => false

/-- CR 605.1b: true iff this triggered ability is a mana ability:
1. It doesn't require a target (CR 115.6);
2. It triggers from the activation or resolution of an activated mana ability or
   from mana being added to a player's mana pool;
3. It could add mana to a player's mana pool when it resolves.
(Unlike CR 605.1a, CR 605.1b has no library-movement exclusion, and CR 605.1
classifies any ability meeting 605.1b as a mana ability regardless of other
effects it generates.) -/
def isManaAbility (ab : TriggeredAbility) : Bool :=
  let effs : Array Effect := if ab.modeEffects.isEmpty then #[ab.effect] else ab.modeEffects
  !effs.any (fun e => !e.targetSpec.isEmpty) &&
    ab.pattern.triggersOnActivatedManaAbilityOrManaAdded &&
    effs.any (fun e => e.couldAddMana)

/-- Chapter numbers if this triggered ability is a Saga chapter ability (CR 714.2b). -/
def chapterNumbers? (ab : TriggeredAbility) : Option (Array Nat) :=
  match ab.grouping with
  | .counterThreshold .lore chapters => if chapters.isEmpty then none else some chapters
  | _ => none

/-- True when this triggered ability is a Saga chapter ability (CR 714.2). -/
def isSagaChapter (ab : TriggeredAbility) : Bool :=
  ab.chapterNumbers?.isSome

/-- Greatest chapter number across an array of triggered abilities (CR 714.2d). -/
def finalChapterNumberOf (abs : Array TriggeredAbility) : Nat :=
  abs.foldl (fun acc ab =>
    match ab.chapterNumbers? with
    | some ns => ns.foldl max acc
    | none => acc) 0

/-- Pattern for Path of Ancestry's delayed mana-spent commander creature-type scry trigger. -/
def manaSpentCastCommanderCreaturePattern : TriggerPattern :=
  let allZones : ZoneSetSpec :=
    { zones := #[.library, .hand, .battlefield, .graveyard, .stack, .exile, .command], owner := .any }
  .castSpell .you
    (.all #[.hasType .creature, .shares .creatureType (.inZones allZones (.all #[.isCommander, .ownedBy .you]))])
    (manaSpent? := some .fromSource)

/-- True when `ab` is a mana-spent commander creature-type scry trigger (Path of Ancestry). -/
def isManaSpentCastScry (ab : TriggeredAbility) : Bool :=
  ab.pattern == manaSpentCastCommanderCreaturePattern

end TriggeredAbility

end Mtg.Engine
