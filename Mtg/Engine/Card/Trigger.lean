import Mtg.Engine.Card.Counter
import Mtg.Engine.Card.Effect
import Mtg.Engine.Card.TriggerPattern

/-!
# Unified triggered abilities (CR 113.3c / 603 / 605.1b / 700.1 / 714.2b,d)

Helpers, reusable CR 603.4 condition constructors, modal inspection, structural
CR 605.1b `isManaAbility`, CR 714.2b/d Saga chapter helpers, and the transitional
Phase-9 `SharedTrigger` effect builders for the unified `TriggeredAbility`
defined in `Mtg/Engine/Card/Ability.lean`.
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
    (headerPhrase : String := "")
    (minModes : ValueExpr := .const 1)
    (maxModes : ValueExpr := .const 1)
    (allowRepeat : Bool := false)
    (unusedThisTurn : Bool := false) : TriggeredAbility :=
  { word := word?.getD pattern.defaultWord
    pattern
    grouping
    interveningIf?
    activeZones
    limit
    effect := {
      body := .chooseModes {
        minModes, maxModes, allowRepeat, unusedThisTurn, modes
      }
      phrase := headerPhrase
    } }

/-- Leftover shared trigger payload this ability resolves, when present. -/
def shared (ab : TriggeredAbility) : SharedTrigger :=
  ab.effect.asTrigger?.getD (.draw 0)

/-- Transitional legacy Trigger-DSL `Resolution` for this triggered ability. -/
def resolution (ab : TriggeredAbility) : TriggerResolution :=
  ab.effect.resolution

/-- Targeting of this triggered ability. -/
def targeting (ab : TriggeredAbility) : EffectTargeting :=
  ab.effect.targeting

/-- Whom this triggered ability may target (CR 115.1 / 603.3d). -/
def targetSpec (ab : TriggeredAbility) : TargetSpec :=
  ab.effect.targeting.spec

/-- True when putting this ability on the stack requires choosing a target. -/
def requiresTarget (ab : TriggeredAbility) : Bool :=
  ab.effect.requiresTarget

/-- True when zero targets is a legal announcement (CR 115.1c / 603.3d). -/
def allowsZeroTargets (ab : TriggeredAbility) : Bool :=
  ab.effect.allowsZeroTargets

/-- Upper bound on targets for single-slot announcements (`0` = spec default). -/
def maxTargets (ab : TriggeredAbility) : Nat :=
  ab.effect.maxTargets

/-- Divided-damage `(amount, maxTargets)`, if any (CR 601.2d). -/
def dividedDamage? (ab : TriggeredAbility) : Option (Nat × Nat) :=
  ab.effect.dividedDamage

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

namespace SharedTrigger

/-- Shift all `Resolution.createTokens` legacy token indices by `offset` (for `.mayTo`). -/
private partial def shiftLegacyTokens (offset : Nat) : Resolution → Resolution
  | r =>
    if offset == 0 then r
    else
      match r with
      | .createTokens idx amt tapped who note => .createTokens (idx + offset) amt tapped who note
      | .sequence rs => .sequence (rs.map (shiftLegacyTokens offset))
      | .«if» c d => .«if» c (shiftLegacyTokens offset d)
      | .ifElse c a b => .ifElse c (shiftLegacyTokens offset a) (shiftLegacyTokens offset b)
      | .may a b h => .may (shiftLegacyTokens offset a) (shiftLegacyTokens offset b) h
      | .or rs => .or (rs.map (shiftLegacyTokens offset))
      | .chooseModes ms h => .chooseModes (ms.map (shiftLegacyTokens offset)) h
      | .queueReflexive d => .queueReflexive (shiftLegacyTokens offset d)
      | .revealLibrary w d p => .revealLibrary w (shiftLegacyTokens offset d) p
      | .revealFromHand w d => .revealFromHand w (shiftLegacyTokens offset d)
      | other => other

/-- Build the unified `Effect` (targeting, zero-target/max-target/divided-damage
metadata, transitional Trigger-DSL `resolution?`, and `legacyTokens`) for a
`SharedTrigger` payload. -/
def toEffect (s : SharedTrigger) : Effect :=
  let base : Effect :=
    match s with
    | .scry n => { resolution? := some (.scry (.fixed n)) }
    | .draw n => { resolution? := some (.draw (.fixed n)) }
    | .createTokens tokIdx n tapped =>
      { resolution? := some (.createTokens tokIdx (.fixed n) tapped) }
    | .amass n subtype amount attachSource =>
      let resolved : TriggeredAbility.NumberSelector :=
        match amount with
        | .fixed => .fixed n
        | .sourcePower => .lastKnownPower
        | .notedExcess => .notedExcess
        | .notedPower => .notedPower
      { resolution? := some (.amass resolved subtype attachSource) }
    | .recruit who => { resolution? := some (.recruit who) }
    | .dividedDamage amount maxTargets =>
      { targeting := .of .anyTarget,
        dividedDamage := some (amount, maxTargets), resolution? := some .dividedDamage }
    | .gainLife n => { resolution? := some (.gainLife (.fixed n)) }
    | .connive who =>
      match who with
      | .source => { resolution? := some (.connive .source) }
      | .target kind => { targeting := .of kind, resolution? := some (.connive .target) }
      | .enteringVillain => { resolution? := some (.connive .enteringVillain) }
    | .exileUntilLeaves kind =>
      { targeting := .of kind, resolution? := some (.exile .target .untilSourceLeaves) }
    | .damageEachOpponent n =>
      { targeting := .of .opponent, resolution? := some (.dealDamage (.fixed n) (.player .eachOpponent)) }
    | .attachTo kind =>
      { targeting := .of kind, resolution? := some (.attach .source .target) }
    | .opponentSacrificesCreature =>
      { targeting := .of .opponent,
        resolution? := some (.sacrifice .opponentChosenCreature) }
    | .exileTop => { resolution? := some (.exile .top .playUntilNextTurn) }
    | .discard n => { resolution? := some (.discard (.cards n)) }
    | .mayTo can thenDo =>
      let left := toEffect can
      let right := toEffect thenDo
      let rightRes := shiftLegacyTokens left.legacyTokens.size right.resolution
      { targeting :=
          if left.targeting.spec.isEmpty then right.targeting else left.targeting
        allowsZeroTargets := left.allowsZeroTargets || right.allowsZeroTargets
        maxTargets :=
          if left.targeting.spec.isEmpty then right.maxTargets else left.maxTargets
        dividedDamage :=
          match left.dividedDamage with
          | some d => some d
          | none => right.dividedDamage
        resolution? := some (.may left.resolution rightRes .ifYouDo)
        legacyTokens := left.legacyTokens ++ right.legacyTokens }
    | .may action =>
      let inner := toEffect action
      { inner with resolution? := some (.may inner.resolution (.sequence [])) }
    | .opponentDiscards n who =>
      match who with
      | .each => { resolution? := some (.discard (.cards n .eachOpponent)) }
      | .target =>
        { targeting := .of .opponent, resolution? := some (.discard (.cards n (.target .opponent))) }
    | .millPlayer n =>
      { targeting := .of .player, resolution? := some (.mill (.fixed n) (.target .player)) }
    | .investigate => { resolution? := some .investigate }
    | .pumpCause p t => { resolution? := some (.pump (.fixed p) (.fixed t) .cause) }
    | .searchLibrary => { resolution? := some (.searchLibrary (.put .forest)) }
    | .searchBasicLandToHand =>
      { resolution? := some (.searchLibrary (.returnToHand .basicLand)) }
    | .eachPlayerSacrificesCreature =>
      { resolution? := some (.sacrifice .eachPlayersCreature) }
    | .exileTarget kind =>
      { targeting := .of kind, resolution? := some (.exile .target .leaveTrigger) }
    | .returnCreatureFromGyToHand =>
      { targeting := .of .creatureCardInYourGraveyard,
        resolution? := some (.returnToHand .graveyardCard) }
    | .plusOneEachYouControl which =>
      { resolution? := some (.putCounters (.ofKind .plusOnePlusOne) (.youControl which)) }
    | .honeEachEquipment => { resolution? := some .honeEachEquipment }
    | .plusOneEachOtherGainLife =>
      { resolution? := some (.sequence
          [.putCounters (.ofKind .plusOnePlusOne) .eachOther,
           .gainLife .perOtherCreature]) }
    | .becomePT p t => { resolution? := some (.becomePT (.fixed p) (.fixed t)) }
    | .pumpTargetPerPlains =>
      { targeting := .of .creatureYouControl, resolution? := some (.pump .perPlains .perPlains .target) }
    | .mayDiscardHandDraw n =>
      { resolution? := some (.may (.discard .hand) (.draw (.fixed n)) .ifYouDo) }
    | .pumpByLookedAt => { resolution? := some (.pump .perLookedAt .perLookedAt .source) }
    | .pumpGreatestPower => { resolution? := some (.pump .greatestPower (.fixed 0) .source) }
    | .pumpForEachOtherCreature =>
      { resolution? := some (.pump .perOtherCreature .perOtherCreature .source) }
    | .damageBlockers n => { resolution? := some (.dealDamage (.fixed n) .blockers) }
    | .returnLinkedExile => { resolution? := some (.put .linkedExile) }
    | .createThenAttach tokIdx =>
      { resolution? := some (.sequence [.createTokens tokIdx (.fixed 1) false, .attach .source .createdToken]) }
    | .gainLifeSearchBasicOnTop n =>
      { resolution? := some (.sequence [.gainLife (.fixed n), .searchLibrary (.put .basicLandOnTop)]) }
    | .addMana types => { resolution? := some (.addMana types) }
    | .createAxe attach =>
      { resolution? := some
          (.createTokens 0 (.fixed 1) false
            (note := if attach then .attachReflexive else .none))
        legacyTokens := #[.axe] }
    | .tapOppOrUntapYours =>
      { resolution? := some (.or [.tap .target, .untap]) }
    | .gainControlOppUntilEot =>
      { targeting := .of .oppCreature, resolution? := some (.gainControl .untilEndOfTurn) }
    | .payReturnFromGy =>
      { resolution? := some (.may
          (.pay (CostSpec.ofMana { symbols := #[.generic 1, .colored .green, .colored .blue] }))
          (.returnToHand .source) .ifYouDo) }
    | .targetOpponentLosesLife n =>
      { targeting := .of .opponent, resolution? := some (.loseLife (.fixed n) (.target .opponent)) }
    | .drawXDiscard n =>
      { resolution? := some (.sequence
          [.draw .equalToManaSpent, .«if» .manaSpent (.discard (.cards n))]) }
    | .ringTempts => { resolution? := some .ringTempts }
    | .setOtherBasePT =>
      { targeting := .of .anotherCreatureYouControl, allowsZeroTargets := true,
        resolution? := some (.setBasePT .equalSourcePower .equalSourceToughness) }
    | .returnElfGainLife =>
      { targeting := .of .elfInYourGraveyard
        resolution? := some (.sequence
          [.returnToHand .graveyardCard, .gainLife .equalToTargetPower]) }
    | .damageFromLastKnownPower =>
      { targeting := .of .oppCreature,
        resolution? := some (.dealDamage .lastKnownPower .permanent) }
    | .mayPayGenericDraw n plusOne =>
      { resolution? := some (
          if plusOne then
            .may (.pay (CostSpec.ofGeneric n))
              (.sequence [.putCounters (.ofKind .plusOnePlusOne) .source, .draw (.fixed 1)]) .ifYouDo
          else
            .may (.pay (CostSpec.ofGeneric n)) (.draw (.fixed 1)) .ifYouDo) }
    | .drawThenBottomIfNoLegendary =>
      { resolution? := some (.sequence
          [.draw (.fixed 1), .«if» (.not (.atLeast (.count .legendaryCreaturesYouControl) (.fixed 1))) (.putOnLibrary .bottom .cardFromHand)]) }
    | .removeHopeDrawSac =>
      { resolution? := some (.sequence
          [.removeCounters .hope .source, .«if» .removedHope (.draw (.fixed 1)), .«if» (.not .hopeOnSource) (.sequence [.sacrifice .source, .gainLife (.fixed 4)])]) }
    | .tapHumansDraw =>
      { resolution? := some (.sequence
          [.may (.tap .humans) (.sequence []), .draw .forEachTappedHuman]) }
    | .destroyOppArtifactsEnchantmentsGainLife =>
      { resolution? := some (.sequence
          [.destroy .oppArtifactsEnchantments (note := .countDestroyed),
           .gainLife .forEachDestroyedThisWay]) }
    | .damageEqualSubtypeToEachOpponent subtype =>
      { resolution? := some (.dealDamage (.subtypeCount subtype) (.player .eachOpponent)) }
    | .damageEqualTreasures =>
      { targeting := .of .anyTarget,
        resolution? := some (.dealDamage (.subtypeCount .treasure) .target) }
    | .dealDamageDestroyIfSubtype n subtype =>
      { targeting := .of .anyTarget,
        resolution? := some (.sequence
          [.dealDamage (.fixed n) .target .markedPermanent,
           .«if» (.dealtDamageToSubtype subtype) (.destroy .permanentDealtDamage)]) }
    | .attachEquipmentToCreature =>
      -- *Iron Hills Stalwart*: the Equipment target is mandatory (slot 0); only the creature
      -- slot is optional (`count := .upTo 1`), so the trigger is removed when you control
      -- no Equipment (CR 115.1c / 603.3d).
      { targeting := .of .equipmentYouControlThenCreatureYouControl,
        allowsZeroTargets := false, resolution? := some (.attach .target .optionalCreature) }
    | .defenderSacsLeastPower =>
      { resolution? := some (.sacrifice .leastPower) }
    | .returnOtherPlusOne =>
      { targeting := .of (.single {
          domain := .object .battlefield (.all #[.otherThan .this, .controlledBy .you])
          count := .upTo 1 })
        allowsZeroTargets := true
        resolution? := some (.sequence
          [.returnToHand .permanent .returnedPermanent,
           .«if» .returnedPermanent (.putCounters (.ofKind .plusOnePlusOne) .source)]) }
    | .lookAtTopRevealTypes n types =>
      { resolution? := some (.lookAtTopRevealTypes (.fixed n) types) }
    | .createTappedTreasuresEqualOppArtifacts =>
      { resolution? := some (.createTokens 0 .oppArtifacts true)
        legacyTokens := #[.treasure] }
    | .putNonlandMvAtMostFromGy mv =>
      { targeting := .of (.single {
          domain := .object .anyGraveyard (.all #[
            .not (.hasType .land), .isKind .permanentCard, .stat .manaValue .le (.const mv)])
          count := .upTo 1 })
        allowsZeroTargets := true, resolution? := some (.put (.nonlandMvAtMost mv)) }
    | .othersGetAndOppsGet subtypes p t oppP oppT =>
      { resolution? := some (.sequence
          [.pump (.fixed p) (.fixed t) (.intersection [.creaturesYouControl, .union (subtypes.toList.map .othersOfSubtype)]),
           .pump (.fixed oppP) (.fixed oppT) .opponentsCreatures]) }
    | .wolfPlusOneOrTreasure =>
      { resolution? := some (.or
          [.putCounters (.ofKind .plusOnePlusOne) .permanent,
           .createTokens 0 (.fixed 1) false])
        legacyTokens := #[.treasure] }
    | .trampleCounterBecomeBear =>
      { targeting := .of .creatureYouControl, allowsZeroTargets := true,
        resolution? := some (.sequence
          [.putCounters (.ofKind .trample) .permanent, .becomeBear, .«if» ((.atLeast (.count (.youControl (.subtype .bear))) (.fixed 3))) (.draw (.fixed 2))]) }
    | .millThenSubtypeToHand n subtype =>
      { resolution? := some (.sequence
          [.mill (.fixed n) (note := .milledCards), .returnToHand (.milledSubtype subtype)]) }
    | .exileOppNonlandEachUntilLeaves =>
      { targeting := .of (.forEachOpponentControlled (.not (.hasType .land)) (.upTo 1))
        allowsZeroTargets := true
        resolution? := some (.exile (.target .eachPermanent) .untilSourceLeaves) }
    | .plusOneEqualLastKnownMv =>
      { targeting := .of .creatureYouControl,
        resolution? := some (.putCounters .plusOneLastKnownMv .permanent) }
    | .mountainQuestDragon =>
      { resolution? := some (.sequence [.putCounters (.ofKind .quest) .source, .«if» ((.atLeast (.count .questCounters) (.fixed 6))) (.sequence [.sacrifice (.sacrificedSource .movedAsSacrificed), .searchLibrary (.put .dragon)])]) }
    | .treasuresPerChosenType =>
      { resolution? := some (.createTokens 0 .chosenCreatureType false)
        legacyTokens := #[.treasure] }
    | .revealUntilCreature =>
      { resolution? := some (.revealLibrary .untilCreature
          (.ifElse .revealedManaValueAtMostLands (.put .revealed) (.returnToHand .revealed))) }
    | .attackSacPlusOneEqualPower =>
      { resolution? := some (.may (.pay CostSpec.sacrificeAnotherCreature)
          (.putCounters .plusOneSacrificedPower .source) .ifYouDo) }
    | .lootLandEntersTapped =>
      { resolution? := some (.sequence
          [.draw (.fixed 1), .discard (.cards 1), .put .discardedLand (how := .tapped)]) }
    | .millThatManyLost =>
      { resolution? := some (.mill .thatManyLost .thatPlayer) }
    | .drawPerFatGraveyard =>
      { resolution? := some (.draw .perFatGraveyard) }
    | .maySacDrawTreasure =>
      { resolution? := some (.may (.pay CostSpec.sacrificeAnotherCreatureOrArtifactSpec)
          (.sequence [.draw (.fixed 1), .createTokens 0 (.fixed 1) false]) .ifYouDo)
        legacyTokens := #[.treasure] }
    | .castInstantSorceryFromHand =>
      { resolution? := some (.mayCast .hand .twiceLegendaryWizards .withoutPaying) }
    | .castInstantSorceryMvAtMost =>
      { resolution? := some (.mayCast .hand .lastKnown .withoutPaying) }
    | .millThenCopy =>
      { resolution? := some (.sequence
          [.mill (.fixed 2) .eachOpponent (note := .opponentsMilled),
           .«if» .opponentsMilled (.queueReflexive (.mayCast .milledSpell .causingSpell .withoutPaying))]) }
    | .pumpTargetBySourcePower =>
      { targeting := .of .anotherCreatureYouControl,
        resolution? := some (.pump .equalSourcePower (.fixed 0) .target) }
    | .createAlienPerInvasion =>
      { resolution? := some (.sequence
          [.createTokens 0 (.fixed 1) false (note := .invasion),
           .putCounters .plusOneNoted .createdToken,
           .putCounters (.ofKind .invasion) .source])
        legacyTokens := #[.alien] }
    | .mayPutArtifactAttachEquipment =>
      { resolution? := some (.sequence
          [.may (.put .artifactFromHand (note := .forAttach)) (.sequence []),
           .«if» (.atLeast (.count .putEquipment) (.fixed 1)) (.attach .putArtifact .notedHost)]) }
    | .cascade => { resolution? := some .cascade }
    | .belladonnaTokenReward =>
      { resolution? := some (.sequence [
          .noteResolveThisTurn 3,
          .«if» (.nthResolve 1) (.gainLife (.fixed 1)),
          .«if» (.nthResolve 2) (.draw (.fixed 1)),
          .«if» (.nthResolve 3) (.putCounters (.ofKind .plusOnePlusOne) .youControl)]) }
    | .bolgMaySacrifice => { resolution? := some (.may (.sacrifice .another) (.sequence [])) }
    | .bolgDealSacrificedPower =>
      { targeting := .of .anotherCreature,
        resolution? := some (.sequence
          [.dealDamage .lastKnownPower .permanent .excess,
           .amass .notedExcess]) }
    | .createSpiritsForEquipped =>
      { resolution? := some (.sequence
          [.createTokens 0 (.fixed 2) true, .«if» (.atLeast (.count (.intersection [.equipped, .legendaryCreaturesYouControl])) (.fixed 1)) .markRecentTokensAttacking])
        legacyTokens := #[.spirit] }
    | .createTreasuresEqualDamagedPlayerArtifacts =>
      { resolution? := some (.createTokens 0 .damagedPlayerArtifacts false)
        legacyTokens := #[.treasure] }
    | .deal1ThenAmassOrcs =>
      { targeting := .of .anyTarget,
        resolution? := some (.sequence
          [.dealDamage (.fixed 1) .target .markedPermanent, .amass (.fixed 1) .orc]) }
    | .untapAttackersExtraCombat _n =>
      { resolution? := some (.sequence [.untap .attackingCreatures, .additionalCombatPhase]) }
    | .eaglesCreateBirds =>
      { resolution? := some (.createTokens 0 .lastKnownPower false)
        legacyTokens := #[.birdSoldier] }
    | .allianceMode =>
      { resolution? := some (.chooseModes TriggeredAbility.TriggerResolution.allianceModes
          .oneUnusedThisTurn) }
    | .destroyOtherAmassControllerPower =>
      { targeting := .of .anotherCreature, allowsZeroTargets := true,
        resolution? := some (.sequence
          [.destroy .target (note := .forAmass),
           .amass .notedPower (who := .controller .target),
           .«if» .youControlledDestroyed (.draw (.fixed 1))]) }
    | .gollumMode =>
      { resolution? := some (.chooseModes TriggeredAbility.TriggerResolution.gollumModes
          .oneUnused) }
    | .discardHandDrawDamageIfStory =>
      { resolution? := some (.sequence
          [.may (.discard .hand) (.sequence []), .draw .discardedHand,
           .«if» .enduringStoryNoted (.dealDamage .discardedHand (.player .eachOpponent))]) }
    | .castFromGyArtifactInstantSorcery =>
      { resolution? := some (.mayCast .graveyard .unlimited .pay .exileInstead) }
    | .equippedAttackersGainDoubleStrike =>
      { resolution? := some (.grant .doubleStrike .equippedAttackers) }
    | .tapEnchantedRemoveCounters =>
      { resolution? := some (.sequence [.tap .enchanted, .removeCounters .all .enchanted]) }
    | .revealTopPutRandomCreature n =>
      { resolution? := some (.revealLibrary (.top n) (.put .randomCreature)) }
    | .beginCombatIfDrawnTwoPump =>
      { targeting := .of .anotherCreatureYouControl,
        resolution? := some (.«if» (.atLeast .cardsDrawnThisTurn (.fixed 2)) (.sequence [
          .pump (.fixed 3) (.fixed 0) .target,
          .grant (.keywords #[Keyword.firstStrike]) .target])) }
    | .honePerOppAttach =>
      { targeting := .of (.ofSlots #[.of .opponent, { domain := .creatureYouControl, count := .upTo 1 }])
        resolution? := some (.sequence
          [.putCounters .honePerOpponent .source, .attach .source (.target .laterCreature)]) }
    | .damageTargetOpponent n =>
      { targeting := .of .opponent, resolution? := some (.dealDamage (.fixed n) (.player (.target .opponent))) }
    | .copySelfNonlegendary => { resolution? := some .copySelfNonlegendary }
    | .attachEquipmentThenFight =>
      { targeting := .of .creatureYouControl,
        resolution? := some (.sequence [.attach .anyYouControl .target,
          .«if» .equipmentAttached (.fight .equipmentHost .reflexive)]) }
    | .returnAsArtifact => { resolution? := some (.put .source (how := .asArtifact)) }
    | .exileLandsThenReturnTapped =>
      { targeting := .of (.single {
          domain := .object .battlefield (.all #[.hasType .land, .controlledBy .you])
          count := .upTo 3 })
        allowsZeroTargets := true, maxTargets := 3
        resolution? := some (.sequence
          [.exile .landsYouControl .forLater .lands,
           .put .notedLands (how := .tapped)]) }
    | .grimaImpulse =>
      { resolution? := some (.sequence
          [.revealLibrary .untilInstantOrSorcery (.exile .top .forLater .impulse) .damagedPlayer,
           .mayCast .impulse .unlimited .withoutPaying]) }
    | .palantir =>
      { targeting := .of .opponent,
        resolution? := some (.sequence
          [.putCounters (.ofKind .influence) .source, .scry (.fixed 2),
           .may (.draw (.fixed 1) (who := .opponentHasYou)) (.sequence [])]) }
    | .treasuresEqualLastKnown =>
      { resolution? := some (.createTokens 0 .lastKnownPower false)
        legacyTokens := #[.treasure] }
    | .protectionEverything =>
      { resolution? := some (.grant .protectionEverything .youIfCast) }
    | .loseLifePerBurden => { resolution? := some (.loseLife .perBurden) }
    | .revealSaga =>
      { resolution? := some (.revealLibrary .untilSaga (.put .revealed)) }
    | .sacDamagersRingTempts =>
      { resolution? := some (.sequence [.sacrifice .combatDamager, .ringTempts]) }
    | .drawIfAttackedOrEnteredSubtype subtype =>
      { resolution? := some (.«if»
          (.or [.attackedWithSubtype subtype, .subtypeEntered subtype])
          (.draw (.fixed 1))) }
    | .othersOfSubtypeGetEqualSourceToughness subtype =>
      { resolution? := some (.pump .equalSourceToughness .equalSourceToughness
          (.othersOfSubtype subtype)) }
    | .scryAndPlan n =>
      { resolution? := some (.sequence [.putCounters (.ofKind .plan) .source, .scry (.fixed n)]) }
    | .lootAndPlan =>
      { resolution? := some (.sequence
          [.putCounters (.ofKind .plan) .source, .draw (.fixed 1), .discard (.cards 1)]) }
    | .createVillainAndPlan =>
      { resolution? := some (.sequence
          [.putCounters (.ofKind .plan) .source, .createTokens 0 (.fixed 1) false])
        legacyTokens := #[.villain21menace] }
    | .drainAndPlan n =>
      { resolution? := some (.sequence
          [.putCounters (.ofKind .plan) .source, .loseLife (.fixed n) .eachOpponent, .gainLife (.fixed n)]) }
    | .drawLoseLifeAndPlan =>
      { resolution? := some (.sequence
          [.putCounters (.ofKind .plan) .source, .draw (.fixed 1), .loseLife (.fixed 1)]) }
    | .treasureTappedAndPlan =>
      { resolution? := some (.sequence
          [.putCounters (.ofKind .plan) .source, .createTokens 0 (.fixed 1) true])
        legacyTokens := #[.treasure] }
    | .plusOneOnTargetAndPlan =>
      { targeting := .of .creatureYouControl,
        resolution? := some (.sequence
          [.putCounters (.ofKind .plan) .source,
           .putCounters (.ofKind .plusOnePlusOne) (.permanent true)]) }
    | .planFinishDrawPlusOneEach =>
      { resolution? := some (.sequence
          [.sacrifice .plan, .draw (.fixed 1), .putCounters (.ofKind .plusOnePlusOne) .youControl]) }
    | .planFinishReturnInstants =>
      { resolution? := some (.sequence
          [.sacrifice .plan .forReflexive,
           .«if» .planWasSacrificed (.queueReflexive (.returnToHand (.graveyardInstants 2)))]) }
    | .planFinishControlOpponent =>
      { resolution? := some (.sequence
          [.sacrifice .plan .forReflexive,
           .«if» .planWasSacrificed (.queueReflexive (.gainControl .duringNextTurn))]) }
    | .planFinishExileTopCast =>
      { resolution? := some (.sequence
          [.sacrifice .plan .forReflexive,
           .«if» .planWasSacrificed (.queueReflexive (.exile (.opponentTop 5) (.mayCastUpTo 2)))]) }
    | .planFinishCreateRobots n =>
      { resolution? := some (.sequence
          [.sacrifice .plan, .createTokens 0 (.fixed n) false])
        legacyTokens := #[.robotVillain22] }
    | .planFinishDividedDamage n =>
      { resolution? := some (.sequence
          [.sacrifice .plan .forReflexive,
           .«if» .planWasSacrificed (.queueReflexive (.dealDamage (.fixed n) .target .divided))]) }
    | .planFinishIndestructibleOnTarget =>
      { resolution? := some (.sequence
          [.sacrifice .plan .forReflexive,
           .«if» .planWasSacrificed (.queueReflexive (.putCounters (.ofKind .indestructible) .permanent))]) }
    | .surveil n => { resolution? := some (.surveil (.fixed n)) }
    | .empowerJace n => { resolution? := some (.empowerJace (.fixed n)) }
    | .prepareSource k => { resolution? := some (.prepareSource k) }
    | .drawIfRemovedTwoLoyalty =>
      { resolution? := some (.«if» (.atLeast .lastKnownPower (.fixed 2)) (.draw (.fixed 1))) }
    | .loyaltyOnSource =>
      { resolution? := some (.putCounters (.ofKind .loyalty) .source) }
    | .grantThenCounterByType k =>
      { targeting := .of .permanentYouControl,
        resolution? := some (.sequence
          [.grant (.keywords k) .target,
           .«if» (.atLeast (.count (.target .creature)) (.fixed 1)) (.putCounters (.ofKind .plusOnePlusOne) .permanent),
           .«if» (.atLeast (.count (.target .planeswalker)) (.fixed 1)) (.putCounters (.ofKind .loyalty) .permanent)]) }
    | .destroyOppPermanentIfSixLands =>
      { targeting := .of .oppPermanent,
        resolution? := some (.«if» ((.atLeast (.count .landsYouControl) (.fixed 6))) (.sequence [
          .destroy .target,
          .createTokens 0 (.fixed 1) false (who := .controller .target)]))
        legacyTokens := #[.treasure] }
    | .pumpOrCounterIfScried =>
      { targeting := .of .anotherCreatureYouControl,
        resolution? := some (.ifElse (.or [.scriedThisTurn, .surveilledThisTurn])
          (.putCounters (.ofKind .plusOnePlusOne) .permanent)
          (.pump (.fixed 1) (.fixed 1) .target)) }
    | .sacrificeSourceIfNoPlaneswalker =>
      { resolution? := some (.«if» (.not (.atLeast (.count .planeswalkersYouControl) (.fixed 1))) (.sacrifice (.sacrificedSource .controllerSacrifices))) }
    | .creaturesYouControlGet p t =>
      { resolution? := some (.pump (.fixed p) (.fixed t) .creaturesYouControl) }
    | .putSourceCountersOnTarget =>
      { targeting := .of .creatureYouControl, allowsZeroTargets := true,
        resolution? := some (.putCounters .sourceCounters .permanent) }
    | .chargeCounterOnSource =>
      { resolution? := some (.putCounters (.ofKind .charge) .source) }
    | .addGreenPerChargeCounter =>
      { resolution? := some (.addMana #[.colored .green] .perChargeCounter) }
    | .drawTwoWinIfEmptyShuffleSource =>
      { resolution? := some (.sequence
          [.draw (.fixed 2), .«if» (.not (.atLeast .libraryCards (.fixed 1))) .winTheGame, .«if» (.atLeast .libraryCards (.fixed 1)) .shuffleSource]) }
    | .surveilReturnIfGainedLife =>
      { resolution? := some (.sequence [.armSurveilReturnLifeGained, .surveil (.fixed 1)]) }
    | .pumpIfFiveOtherForests =>
      { targeting := .of .creatureYouControl,
        resolution? := some (.«if» ((.atLeast (.count .forestsExceptCause) (.fixed 5))) (.pump (.fixed 3) (.fixed 3) .target)) }
    | .exileOtherCopyEnchanted =>
      { targeting := .of .creature, allowsZeroTargets := true,
        resolution? := some (.sequence
          [.exile .target .untilSourceLeaves .copyAndHost, .becomeCopy .noted]) }
    | .exileUntilNextEndStep =>
      { targeting := .of .creatureYouControl, allowsZeroTargets := true,
        resolution? := some (.exile .target .nextEndStep) }
    | .tapOrUntapNonland =>
      { targeting := .of .nonland, allowsZeroTargets := true,
        resolution? := some (.or [.tap .target, .untap]) }
    | .createFoodOrTreasure =>
      { resolution? := some (.or
          [.createTokens 0 (.fixed 1) false, .createTokens 1 (.fixed 1) false])
        legacyTokens := #[.food, .treasure] }
    | .villainIfGyElseMill =>
      { resolution? := some (.ifElse ((.atLeast (.count .creatureCardsInGraveyard) (.fixed 2)))
          (.createTokens 0 (.fixed 1) true) (.mill (.fixed 2)))
        legacyTokens := #[.villain21menace] }
    | .drawMayPutLandTapped =>
      { resolution? := some (.sequence
          [.draw (.fixed 1), .may (.put .landFromHand (how := .tapped)) (.sequence [])]) }
    | .drawGainLifeIfAnotherHero =>
      { resolution? := some (.sequence [.draw (.fixed 1), .«if» (.atLeast (.count (.othersOfSubtype .hero)) (.fixed 1)) (.gainLife (.fixed 2))]) }
    | .plusOneOrTwoIfAnotherHero =>
      { targeting := .of .creature,
        resolution? := some (.ifElse ((.atLeast (.count (.target (.anotherSubtype .hero))) (.fixed 1)))
          (.putCounters (.ofKind .plusOnePlusOne 2) .permanent)
          (.putCounters (.ofKind .plusOnePlusOne) .permanent)) }
    | .maySacArtifactOrDiscardDraw =>
      { resolution? := some (.may (.pay CostSpec.sacrificeArtifactOrDiscardCard) (.draw (.fixed 1)) .ifYouDo) }
    | .enter (.destroy kind) =>
      { targeting := .of kind, resolution? := some (.destroy .target) }
    | .enter (.dealDamageUpToOne n) =>
      { targeting := .of .creature, allowsZeroTargets := true,
        resolution? := some (.dealDamage (.fixed n) .target) }
    | .enter .fightUpToOne =>
      { targeting := .of .anotherCreature, allowsZeroTargets := true,
        resolution? := some .fight }
    | .enter .returnNonlandNontoken =>
      { targeting := .of .nonlandNontoken, allowsZeroTargets := true,
        resolution? := some (.returnToHand .permanent .returnedPermanent) }
    | .enter .createZabu =>
      { resolution? := some (.createTokens 0 (.fixed 1) false)
        legacyTokens := #[.zabu] }
    | .enter .oppCreatesTheVoid =>
      { targeting := .of .opponent,
        resolution? := some (.createTokens 0 (.fixed 1) false (.target .opponent))
        legacyTokens := #[.theVoid] }
    | .enter .createSturdyShieldAttach =>
      { resolution? := some (.sequence
          [.createTokens 0 (.fixed 1) false (note := .remember),
           .attach .createdToken .source])
        legacyTokens := #[.sturdyShield] }
    | .enter .exileGyPlayUntilNextTurn =>
      { targeting := .of .equipmentInstantOrSorceryInYourGraveyard,
        resolution? := some (.sequence
          [.exile .graveyardCard .forLater .playCard, .grantPlayNotedUntilNextTurn]) }
    | .enter .returnGyPermanentThisTurn =>
      { targeting := .of .permanentCardInYourGraveyard,
        resolution? := some (.returnToHand .graveyardPermanent) }
    | .enter .tapOppCantUntapWhileControl =>
      { targeting := .of .oppCreature,
        resolution? := some (.sequence [.tap .target, .cant .untapWhileYouControl]) }
    | .enter .maySacAnotherThenDestroyOppNonland =>
      { resolution? := some (.may (.pay CostSpec.sacrificeAnotherCreature) (.queueReflexive (.destroy .target)) .ifYouDo) }
    | .enter .maySacOrDiscardNonlandThenDamage =>
      { resolution? := some (.may (.pay CostSpec.sacrificeArtifactOrDiscardNonland)
          (.queueReflexive (.dealDamage (.fixed 2) .target)) .ifYouDo) }
    | .enter .revealHandExileUntilLeaves =>
      { targeting := .of .opponent, allowsZeroTargets := true,
        resolution? := some (.revealFromHand .hand (.exile .target .untilSourceLeaves)) }
    | .enter .plusOnesOrReturnArtEnch =>
      { targeting := .of .creature, allowsZeroTargets := true,
        resolution? := some (.or
          [.putCounters (.ofKind .plusOnePlusOne) .permanent,
           .returnToHand .graveyardCard]) }
    | .enter .chooseUpToXModes =>
      { targeting := .of .opponent, allowsZeroTargets := true,
        resolution? := some (.chooseModes TriggeredAbility.TriggerResolution.upToXModes
          .alreadyChosen) }
    | .enter .mayTapThenGrantIndestructible =>
      { resolution? := some (.may (.tap .source) (.queueReflexive (.grant (.keywords #[Keyword.indestructible]) .target)) .ifYouDo) }
    | .enter .tapLoseAbilitiesWhileSource =>
      { targeting := .of .creature, allowsZeroTargets := true,
        resolution? := some (.sequence
          [.tap (.target .ifPresent), .lose .allAbilities (.target .ifPresent)]) }
    | .enter .revealDiscardFromHand =>
      { targeting := .of .player,
        resolution? := some (.revealFromHand .onePlusCreatureCards
          (.discard (.cards 1 (.target .opponent)))) }
    | .enter .createRedwing =>
      { resolution? := some (.createTokens 0 (.fixed 1) false)
        legacyTokens := #[.redwing] }
    | .step .enchantedControllerDraws =>
      { resolution? := some (.draw (.fixed 1) (who := .controller .enchanted)) }
    | .step .drawToTen =>
      { resolution? := some (.draw (.upToHandSize 10)) }
    | .step .copyAbsorbingMan =>
      { targeting := .of (.single {
          domain := .object .battlefield (.any #[
            .hasType .artifact,
            .all #[.not (.hasSubtype (.literal .aura)), .hasType .enchantment],
            .hasType .land])
          count := .upTo 1 })
        allowsZeroTargets := true, maxTargets := 1
        resolution? := some (.becomeCopy .artifactEnchantmentOrLand) }
    | .step .hydeChoose =>
      { resolution? := some (.chooseModes TriggeredAbility.TriggerResolution.hydeModes
          .plusOneOrRemoveCounter) }
    | .step .copyTaskmaster =>
      { targeting := .of .creatureOrGyCreatureCard,
        allowsZeroTargets := true, maxTargets := 1
        resolution? := some (.becomeCopy .creatureOrGraveyardCard) }
    | .step .harnessedFlicker =>
      { targeting := .of (.single {
          domain := .object .battlefield (.all #[.otherThan .this, .not (.hasType .land), .controlledBy .you])
          count := .upTo 1 })
        allowsZeroTargets := true, maxTargets := 1
        resolution? := some (.«if» (.atLeast (.count .harnessedSource) (.fixed 1)) (.exile .target .returnImmediately)) }
    | .death .hellcatReturn =>
      { resolution? := some (.put .source .underOwner (.entering [
          .loseAllAbilities, .keywords #[Keyword.haste],
          .counter .plusOnePlusOne (asEnters := true)])) }
    | .death .villainReturnAsHero =>
      { resolution? := some (.put (.cause (some .villain)) .underOwner (.entering [
          .additionalSubtype .hero, .counter .finality])) }
    | .death .attackingReturnHand =>
      { resolution? := some (.returnToHand .cause) }
    | .death .deathtouchOppSac =>
      { resolution? := some (.sacrifice .chosenNontokenCreature) }
    | .thisAttack .mayPayPlusOne =>
      { resolution? := some (.may (.pay (CostSpec.ofGeneric 1)) (.queueReflexive (.putCounters (.ofKind .plusOnePlusOne) .permanent)) .ifYouDo) }
    | .thisAttack .payReturnAttacking =>
      { resolution? := some (.may (.pay (CostSpec.ofMana { symbols := #[.generic 3, .colored .black] }))
          (.queueReflexive (.put .creatureCard .tapped (.entering [.attacking, .counter .finality]))) .ifYouDo) }
    | .thisAttack .ifArtifactEnteredDraw =>
      { resolution? := some (.«if» .artifactEnteredThisTurn (.draw (.fixed 1))) }
    | .thisAttack .blinkNontoken =>
      { targeting := .of (.single {
          domain := .object .battlefield (.all #[.isToken false, .any #[.hasType .artifact, .hasType .creature]])
          count := .upTo 1 })
        allowsZeroTargets := true, maxTargets := 1
        resolution? := some (.exile .target .returnTapped) }
    | .thisAttack .equippedDrain =>
      { resolution? := some (.«if» .attachedEquipment (.sequence [
          .loseLife .attachedEquipment .eachOpponent,
          .gainLife .attachedEquipment])) }
    | .thisAttack .drawIfPower4 =>
      { resolution? := some (.«if» (.atLeast .equalSourcePower (.fixed 4)) (.draw (.fixed 1))) }
    | .thisAttack .attacksAlonePlus2Indestructible =>
      { resolution? := some (.sequence [
          .pump (.fixed 2) (.fixed 0) .source,
          .grant (.keywords #[Keyword.indestructible]) .source]) }
    | .enterOrAttack .copyKeywords =>
      { targeting := .of .anotherCreature,
        resolution? := some (.putCounters .missingKeywordsFromTarget .source) }
    | .enterOrAttack .createSquirrel =>
      { resolution? := some (.createTokens 0 (.fixed 1) false)
        legacyTokens := #[.squirrel11green] }
    | .watch .combatDamageExileUntilNonland =>
      { resolution? := some (.revealLibrary .untilNonland
          (.may (.putCounters (.ofKind .plusOnePlusOne) .source)
            (.exile .top .forLater .anyManaThisTurn) .ifYouDont)
          .announced) }
    | .watch .attacksAloneDrain =>
      { targeting := .of .opponent,
        resolution? := some (.sequence [.loseLife (.fixed 1) (.target .opponent), .gainLife (.fixed 1)]) }
    | .watch .attacksAloneFirstStrikeMenace =>
      { resolution? := some (.grant
          (.keywords #[Keyword.firstStrike, Keyword.menace]) .attackingAlone) }
    | .watch .firstTapUntap =>
      { resolution? := some (.untap .firstThisTurn) }
    | .watch .sheHulkRedirectOnce =>
      { targeting := .of .anyTarget,
        resolution? := some (.may (.dealDamage .lastKnownPower .target) (.sequence []) .ifYouDo) }
    | .watch .speedballTargeted =>
      { resolution? := some (.sequence [
          .pump (.fixed 2) (.fixed 2) .source, .may .retargetCause (.sequence []) .ifYouDo]) }
    | .watch .anyPlayerSecondDraw =>
      { resolution? := some (.draw (.fixed 1)) }
    | .watch .youTargetDrawOnce =>
      { resolution? := some (.draw (.fixed 1)) }
    | .watch .villainOrArtifactDamage =>
      { targeting := .of .opponent,
        resolution? := some (.dealDamage (.fixed 1) (.player (.target .opponent))) }
    | .watch .villainConniveOnce =>
      { resolution? := some (.connive .enteringVillain) }
    | .watch .villainPlusOneDamageOnce =>
      { resolution? := some (.sequence [
          .putCounters (.ofKind .plusOnePlusOne) .sourceIfPresent,
          .dealDamage (.fixed 2) (.player .eachOpponent)]) }
    | .watch .villainAttachEquipment =>
      { targeting := .of .upToOneEquipmentThenCreatureYouControl
        resolution? := some (.attach .announcedEquipment .announcedCreature) }
    | .watch .villainPlusOneLifelink =>
      { resolution? := some (.sequence [
          .pump (.fixed 1) (.fixed 0) .source, .grant (.keywords #[Keyword.lifelink]) .source]) }
    | .watch .hulklingCompare =>
      { resolution? := some (.«if» (.or [.causeGreaterPower, .causeGreaterToughness])
          (.putCounters (.ofKind .plusOnePlusOne) .source)) }
    | .watch .justiceBounce =>
      { resolution? := some (.putCounters (.ofKind .plusOnePlusOne) .source) }
    | .watch .nontokenHeroModal =>
      { resolution? := some (.chooseModes
          [.createTokens 0 (.fixed 1) false,
           .pump (.fixed 1) (.fixed 1) .creaturesYouControl]
          .fromLastKnown)
        legacyTokens := #[.soldier11white] }
    | .watch .ultronCopy =>
      { resolution? := some (.may (.pay (CostSpec.ofGeneric 2)) (.becomeCopy .cause) .ifYouDo) }
    | .watch .enchantedAttachEquipment =>
      { targeting := .of .equipmentYouControl
        allowsZeroTargets := true, maxTargets := 1000,
        resolution? := some (.attach (.target .eachEquipment) .enchantedCreature) }
    | .watch .equippedAttacksAloneUntapScry =>
      { resolution? := some (.sequence [.untap .equipped, .scry (.fixed 1)]) }
    | .watch .equippedAttacksTap =>
      { targeting := .of .defendingPlayerCreature,
        resolution? := some (.tap .target) }
    | .watch .equippedTappedDamage =>
      { resolution? := some (.dealDamage (.fixed 1) (.player .eachOpponent) .fromEquipped) }
    | .watch .heroesDamagePlusTwo =>
      { resolution? := some (.putCounters (.ofKind .plusOnePlusOne 2) .source) }
    | .watch .merfolkAttackDraw =>
      { resolution? := some (.draw (.fixed 1)) }
    | .watch .tokensEnterMayDraw =>
      { resolution? := some (.may (.draw (.fixed 1)) (.sequence []) .ifYouDo) }
    | .watch .hawkeyeModes =>
      { allowsZeroTargets := true,
        resolution? := some (.may (.pay (CostSpec.ofGeneric 1)) (.queueReflexive (.chooseModes TriggeredAbility.TriggerResolution.trickArrowModes .alreadyChosen)) .ifYouDo) }
    | .watch .redHulk =>
      { resolution? := some (.sequence [
          .putCounters (.ofKind .plusOnePlusOne) .source,
          .queueReflexive (.dealDamage .plusOneCounters .target)]) }
    | .watch .hulk =>
      { resolution? := some (.sequence [
          .putCounters (.ofKind .plusOnePlusOne) .source,
          .«if» (.atLeast (.count (.intersection [.source, .attackingCreatures])) (.fixed 1)) (.untap .source),
          .«if» .enrageGrantsCombat .additionalCombatPhase]) }
    | .youAttacking .pay2LifeToughness =>
      { resolution? := some (.may (.loseLife (.fixed 2))
          (.grant .assignCombatDamageEqualToughness .creaturesYouControl) .ifYouDo) }
    | .youAttacking .exileTopHeroPump =>
      { resolution? := some (.may (.exile .top .playThisTurn .ifHero) (.sequence [])) }
    | .youAttacking .lookSixCast =>
      { resolution? := some (.revealLibrary (.top 6)
          (.mayCast .looked .greatestAttackingPower .withoutPaying)) }
    | .casting .villainToken =>
      { resolution? := some (.createTokens 0 (.fixed 1) false)
        legacyTokens := #[.villain21menace] }
    | .casting .merfolkFromBlue =>
      { resolution? := some (.createTokens 0 .blueManaSymbols false)
        legacyTokens := #[.merfolk] }
    | .casting .mayPayHasteUnblockable =>
      { resolution? := some (.may (.pay (CostSpec.ofGeneric 1)) (.queueReflexive (.cant (.beBlockedExceptByHaste .target))) .ifYouDo) }
    | .casting .plusOneEachOther =>
      { resolution? := some (.putCounters (.ofKind .plusOnePlusOne) .eachOther) }
    | .casting .exileFlicker =>
      { targeting := .of (.ofDomain (.object .battlefield (.all #[
          .otherThan .this, .not (.hasType .land), .isToken false])))
        resolution? := some (.exile .target .nextEndStep) }
    | .casting .visionModes =>
      { resolution? := some (.chooseModes TriggeredAbility.TriggerResolution.visionModes .vision) }
    | .casting .damageEqualMv =>
      { targeting := .of .anyTarget,
        resolution? := some (.dealDamage .spellManaValue .target) }
    | .casting .drawPowerEqualHand =>
      { resolution? := some (.sequence [.draw (.fixed 1), .grant .basePowerEqualHand .source]) }
    | .casting .plusOneThis =>
      { resolution? := some (.putCounters (.ofKind .plusOnePlusOne) .source) }
    | .casting .plusOneScry =>
      { resolution? := some (.sequence [.putCounters (.ofKind .plusOnePlusOne) .source, .scry (.fixed 1)]) }
    | .casting .ironFistTap =>
      { resolution? := some (.grant .ironFistTap .source) }
    | .casting .targetsGainFlying =>
      { resolution? := some (.grant (.keywords #[Keyword.flying]) .spellTargets) }
    | .casting .copyIfArtifactOrLand =>
      { resolution? := some (.sequence [
          .putCounters (.ofKind .plusOnePlusOne 2) .source, .copyCause]) }
    | .casting .tapCreatureOrLand =>
      { targeting := .of (.ofDomain (.object .battlefield (.any #[.hasType .creature, .hasType .land]))),
        resolution? := some (.tap .target) }
    | .resource .discardExilePlay =>
      { resolution? := some (.may (.exile .discarded .playUntilNextTurn) (.sequence []) .ifYouDo) }
    | .resource .drawIfAnotherHeroDamage =>
      { targeting := .of .opponent,
        resolution? := some (.«if» (.atLeast (.count (.othersOfSubtype .hero)) (.fixed 1)) (.dealDamage (.fixed 1) (.player (.target .opponent)))) }
    | .resource .secondDrawBecome66 =>
      { resolution? := some (.sequence [
          .setBasePT (.fixed 6) (.fixed 6) .source, .grant (.keywords #[Keyword.trample]) .source]) }
    | .resource .secondDrawPlusOneTarget =>
      { targeting := .of .creature,
        resolution? := some (.putCounters (.ofKind .plusOnePlusOne) .permanent) }
    | .resource .secondDrawDrain =>
      { resolution? := some (.sequence [.loseLife (.fixed 1) .eachOpponent, .gainLife (.fixed 1)]) }
    | .resource .gainLifePlusOnes =>
      { targeting := .of .creatureYouControl,
        allowsZeroTargets := true,
        resolution? := some (.putCounters (.ofKind .plusOnePlusOne) .eachUpToLastKnown) }
    | .resource .plusOneCreateInsectOnce =>
      { resolution? := some (.createTokens 0 (.fixed 1) false)
        legacyTokens := #[.insect11green] }
    | .resource .plusOneOnThisOnce =>
      { resolution? := some (.putCounters (.ofKind .plusOnePlusOne) .source) }
    | .resource .plusOneOnHeroesCreateWall =>
      { resolution? := some (.may (.createTokens 0 (.fixed 1) false) (.sequence []) .ifYouDo)
        legacyTokens := #[.wall04defender] }
  { base with sharedTrigger := some s }

/-- Default `TriggerPattern` for leftover `SharedTrigger` families that carry
their own printed event. -/
def defaultPattern : SharedTrigger → TriggerPattern
  | .prepareSource .ifNotPrepared => TriggerPattern.stepYourUpkeep
  | .prepareSource .ifThreeCreaturesDied => TriggerPattern.stepEachEndStep
  | .pumpOrCounterIfScried => TriggerPattern.stepYourBeginCombat
  | .sacrificeSourceIfNoPlaneswalker => TriggerPattern.stepEachEndStep
  | .addGreenPerChargeCounter => TriggerPattern.stepYourFirstMain
  | .surveilReturnIfGainedLife => TriggerPattern.stepYourEndStep
  | .drawIfRemovedTwoLoyalty => TriggerPattern.youActivateLoyaltyAbility 2
  | .returnAsArtifact => TriggerPattern.thisCreatureDies
  | .cascade => TriggerPattern.thisCast
  | .eaglesCreateBirds => TriggerPattern.stepEachUpkeep
  | .bolgDealSacrificedPower => TriggerPattern.youSacrificeOtherCreature
  | .enter _ => TriggerPattern.thisEnters
  | .step .enchantedControllerDraws => TriggerPattern.stepEnchantedControllerUpkeep
  | .step .drawToTen => TriggerPattern.stepYourEndStep
  | .step .copyAbsorbingMan => TriggerPattern.stepYourFirstMain
  | .step .hydeChoose => TriggerPattern.stepYourUpkeep
  | .step .copyTaskmaster => TriggerPattern.stepYourFirstMain
  | .step .harnessedFlicker =>
    .whenCond TriggerPattern.stepYourEndStep TriggeredAbility.condSourceHarnessed
  | .death .hellcatReturn => TriggerPattern.thisDies
  | .death .villainReturnAsHero => TriggerPattern.villainYouControlDies
  | .death .attackingReturnHand => TriggerPattern.attackingCreatureYouControlDies
  | .death .deathtouchOppSac =>
    TriggerPattern.permanentDies (.all #[
      .otherThan .this, .hasType .creature, .controlledBy .you, .hasKeyword .deathtouch])
  | .thisAttack .attacksAlonePlus2Indestructible => TriggerPattern.thisAttacksAlone
  | .thisAttack _ => TriggerPattern.thisAttacks
  | .enterOrAttack _ => TriggerPattern.enterOrAttack
  | .watch .combatDamageExileUntilNonland => TriggerPattern.thisDealsCombatDamageToPlayer
  | .watch .attacksAloneDrain | .watch .attacksAloneFirstStrikeMenace =>
    TriggerPattern.creatureYouControlAttacksAlone
  | .watch .firstTapUntap => TriggerPattern.creatureYouControlFirstTappedYourTurn
  | .watch .sheHulkRedirectOnce => TriggerPattern.creatureYouControlDealtDamage
  | .watch .speedballTargeted => TriggerPattern.spellTargetsThis
  | .watch .anyPlayerSecondDraw => .drawCard .any
  | .watch .youTargetDrawOnce => TriggerPattern.youTargetPlayerOrPermanentWithAbility
  | .watch .villainOrArtifactDamage => TriggerPattern.anotherVillainOrArtifactYouControlEnters
  | .watch .villainConniveOnce | .watch .villainPlusOneDamageOnce
  | .watch .villainAttachEquipment | .watch .villainPlusOneLifelink =>
    TriggerPattern.anotherSubtypeYouControlEnters .villain
  | .watch .hulklingCompare => TriggerPattern.anotherCreatureYouControlEnters
  | .watch .justiceBounce => TriggerPattern.anotherNonlandYouControlReturnedToHand
  | .watch .nontokenHeroModal => TriggerPattern.anotherNontokenSubtypeYouControlEnters .hero
  | .watch .ultronCopy => TriggerPattern.anotherNontokenArtifactYouControlEnters
  | .watch .enchantedAttachEquipment => TriggerPattern.enchantedAttacksOrBlocks
  | .watch .equippedAttacksAloneUntapScry => TriggerPattern.equippedAttacksAlone
  | .watch .equippedAttacksTap => TriggerPattern.equippedAttacks
  | .watch .equippedTappedDamage => TriggerPattern.equippedBecomesTapped
  | .watch .heroesDamagePlusTwo => TriggerPattern.heroesYouControlDealDamageToPlayer
  | .watch .merfolkAttackDraw => TriggerPattern.merfolkYouControlAttackPlayer
  | .watch .tokensEnterMayDraw => TriggerPattern.tokenYouControlEnters
  | .watch .hawkeyeModes => TriggerPattern.thisBecomesTapped
  | .watch .redHulk | .watch .hulk => TriggerPattern.thisDealtDamage
  | .youAttacking _ => TriggerPattern.youAttack
  | .casting .villainToken => TriggerPattern.youCastSubtype .villain
  | .casting .merfolkFromBlue | .casting .mayPayHasteUnblockable
  | .casting .plusOneEachOther | .casting .exileFlicker | .casting .visionModes
  | .casting .damageEqualMv | .casting .tapCreatureOrLand => TriggerPattern.youCastNoncreature
  | .casting .drawPowerEqualHand | .casting .plusOneThis
  | .casting .plusOneScry | .casting .ironFistTap => TriggerPattern.youCastTargetingCreatureYouControl
  | .casting .targetsGainFlying => TriggerPattern.youCastTargetingCreature
  | .casting .copyIfArtifactOrLand => TriggerPattern.youCastInstantSorceryTargetingArtifactOrLand
  | .resource .discardExilePlay => .discard .you
  | .resource .drawIfAnotherHeroDamage => .drawCard .you
  | .resource .secondDrawBecome66 | .resource .secondDrawPlusOneTarget
  | .resource .secondDrawDrain => .drawCard .you
  | .resource .gainLifePlusOnes => .gainLife .you
  | .resource .plusOneCreateInsectOnce => TriggerPattern.youPutPlusOneOnCreature
  | .resource .plusOneOnThisOnce => TriggerPattern.youPutPlusOneOnOtherCreature
  | .resource .plusOneOnHeroesCreateWall => TriggerPattern.youPutPlusOneOnOtherHeroYouControl
  | _ => TriggerPattern.thisEnters

/-- Default `BatchGrouping` for leftover `SharedTrigger` families. -/
def defaultGrouping : SharedTrigger → BatchGrouping
  | .watch .heroesDamagePlusTwo | .watch .tokensEnterMayDraw
  | .watch .redHulk | .watch .hulk
  | .youAttacking _
  | .resource .plusOneCreateInsectOnce | .resource .plusOneOnThisOnce
  | .resource .plusOneOnHeroesCreateWall => .oncePerBatch
  | .watch .merfolkAttackDraw => .perPlayerInBatch
  | .watch .sheHulkRedirectOnce => .perSourceInBatch
  | _ => .perOccurrence

/-- Default `TriggerLimit` for leftover `SharedTrigger` families. -/
def defaultLimit : SharedTrigger → TriggerLimit
  | .watch .youTargetDrawOnce | .watch .villainPlusOneDamageOnce
  | .resource .plusOneCreateInsectOnce | .resource .plusOneOnThisOnce => .onceEachTurn
  | .watch .villainConniveOnce | .watch .sheHulkRedirectOnce => .optionalOnceEachTurn
  | .watch .anyPlayerSecondDraw
  | .resource .secondDrawBecome66 | .resource .secondDrawPlusOneTarget
  | .resource .secondDrawDrain => .nthEachTurn 2
  | _ => .unlimited

/-- Default CR 603.4 intervening `"if"` condition carried by a `SharedTrigger` payload. -/
def defaultInterveningIf? : SharedTrigger → Option Condition
  | .pumpIfFiveOtherForests => some TriggeredAbility.condFiveOtherForests
  | .destroyOppPermanentIfSixLands => some (TriggeredAbility.condControlLandsAtLeast 6)
  | .prepareSource .ifNotPrepared => some TriggeredAbility.condSourceNotPrepared
  | .prepareSource .ifThreeCreaturesDied => some (TriggeredAbility.condCreaturesDiedThisTurn 3)
  | .sacrificeSourceIfNoPlaneswalker => some TriggeredAbility.condControlNoPlaneswalker
  | .surveilReturnIfGainedLife => some (TriggeredAbility.condGainedLifeAtLeast 1)
  | .beginCombatIfDrawnTwoPump => some (TriggeredAbility.condDrawnAtLeast 2)
  | .thisAttack .equippedDrain => some TriggeredAbility.condSourceIsEquipped
  | .thisAttack .ifArtifactEnteredDraw => some TriggeredAbility.condArtifactEnteredThisTurn
  | .resource .drawIfAnotherHeroDamage => some (TriggeredAbility.condControlAnotherSubtype .hero)
  | .step .drawToTen => some (TriggeredAbility.condHandSizeLessThan 10)
  | .protectionEverything => some TriggeredAbility.condSourceWasCast
  | .copySelfNonlegendary => some TriggeredAbility.condSourceNotToken
  | .drawIfAttackedOrEnteredSubtype st => some (TriggeredAbility.condAttackedOrEnteredSubtype st)
  | .watch .hulklingCompare => some TriggeredAbility.condTriggerSubjectGreaterPT
  | _ => none

/-- Default active zones (CR 113.6) for a `SharedTrigger` payload. -/
def defaultActiveZones : SharedTrigger → Array ZoneKind
  | .payReturnFromGy => #[.graveyard]
  | .cascade => #[.stack]
  | _ => #[.battlefield]

/-- Build a complete `TriggeredAbility` from a `SharedTrigger` payload with
optional pattern/grouping/condition/zone/limit overrides. -/
def toTriggeredAbility (s : SharedTrigger)
    (pattern? : Option TriggerPattern := none)
    (word? : Option TriggerWord := none)
    (grouping? : Option BatchGrouping := none)
    (interveningIf? : Option Condition := none)
    (activeZones? : Option (Array ZoneKind) := none)
    (limit? : Option TriggerLimit := none)
    (untargeted : Bool := false)
    (allowsZeroTargets : Bool := false) : TriggeredAbility :=
  let pat := pattern?.getD s.defaultPattern
  let eff0 := s.toEffect
  let eff : Effect :=
    { eff0 with
      targeting := if untargeted then {} else eff0.targeting
      dividedDamage := if untargeted then none else eff0.dividedDamage
      allowsZeroTargets := eff0.allowsZeroTargets || allowsZeroTargets }
  { word := word?.getD pat.defaultWord
    pattern := pat
    grouping := grouping?.getD s.defaultGrouping
    interveningIf? := Condition.andOpt s.defaultInterveningIf? interveningIf?
    activeZones := activeZones?.getD s.defaultActiveZones
    limit := limit?.getD s.defaultLimit
    effect := eff }

end SharedTrigger

#guard !(SharedTrigger.toTriggeredAbility (.watch .sheHulkRedirectOnce)).onceEachTurn
#guard (SharedTrigger.toTriggeredAbility (.watch .sheHulkRedirectOnce)).optionalOnceEachTurn
#guard (SharedTrigger.toEffect (.watch .sheHulkRedirectOnce)).targeting.spec == .anyTarget
#guard (SharedTrigger.toEffect (.thisAttack .blinkNontoken)).allowsZeroTargets &&
  (SharedTrigger.toEffect (.thisAttack .blinkNontoken)).maxTargets == 1
#guard (SharedTrigger.toEffect (.thisAttack .mayPayPlusOne)).resolution ==
  .may (.pay (CostSpec.ofGeneric 1)) (.queueReflexive (.putCounters (.ofKind .plusOnePlusOne) .permanent)) .ifYouDo
#guard (SharedTrigger.toEffect (.thisAttack .payReturnAttacking)).resolution ==
  .may (.pay (CostSpec.ofMana { symbols := #[.generic 3, .colored .black] })) (.queueReflexive (.put .creatureCard .tapped (.entering [.attacking, .counter .finality]))) .ifYouDo
#guard (SharedTrigger.toEffect (.thisAttack .ifArtifactEnteredDraw)).resolution ==
  .«if» .artifactEnteredThisTurn (.draw (.fixed 1))
#guard (SharedTrigger.toEffect (.thisAttack .blinkNontoken)).resolution ==
  .exile .target .returnTapped
#guard (SharedTrigger.toEffect (.thisAttack .equippedDrain)).resolution ==
  .«if» .attachedEquipment (.sequence [
    .loseLife .attachedEquipment .eachOpponent,
    .gainLife .attachedEquipment])
#guard (SharedTrigger.toEffect (.thisAttack .drawIfPower4)).resolution ==
  .«if» (.atLeast .equalSourcePower (.fixed 4)) (.draw (.fixed 1))
#guard (SharedTrigger.toEffect (.thisAttack .attacksAlonePlus2Indestructible)).resolution ==
  .sequence [.pump (.fixed 2) (.fixed 0) .source, .grant (.keywords #[Keyword.indestructible]) .source]
#guard (SharedTrigger.toEffect (.enterOrAttack .copyKeywords)).targeting.spec == .anotherCreature
#guard (SharedTrigger.toEffect (.enterOrAttack .copyKeywords)).resolution ==
  .putCounters .missingKeywordsFromTarget .source
#guard (SharedTrigger.toEffect (.enterOrAttack .createSquirrel)).resolution ==
  .createTokens 0 (.fixed 1) false &&
  (SharedTrigger.toEffect (.enterOrAttack .createSquirrel)).legacyToken 0 == .squirrel11green
#guard (SharedTrigger.toTriggeredAbility (.watch .villainConniveOnce)).optionalOnceEachTurn
#guard (SharedTrigger.toEffect (.watch .combatDamageExileUntilNonland)).resolution ==
  .revealLibrary .untilNonland
    (.may (.putCounters (.ofKind .plusOnePlusOne) .source)
      (.exile .top .forLater .anyManaThisTurn) .ifYouDont)
    .announced
#guard (SharedTrigger.toEffect (.watch .hawkeyeModes)).resolution ==
  .may (.pay (CostSpec.ofGeneric 1)) (.queueReflexive (.chooseModes TriggeredAbility.TriggerResolution.trickArrowModes .alreadyChosen)) .ifYouDo
#guard (SharedTrigger.toEffect (.watch .hulk)).resolution ==
  .sequence [
    .putCounters (.ofKind .plusOnePlusOne) .source,
    .«if» (.atLeast (.count (.intersection [.source, .attackingCreatures])) (.fixed 1)) (.untap .source),
    .«if» .enrageGrantsCombat .additionalCombatPhase]
#guard (SharedTrigger.toTriggeredAbility (.enterOrAttack .copyKeywords)).pattern ==
  TriggerPattern.enterOrAttack
#guard (SharedTrigger.toEffect (.death .hellcatReturn)).resolution ==
  .put .source .underOwner (.entering [
    .loseAllAbilities, .keywords #[Keyword.haste],
    .counter .plusOnePlusOne (asEnters := true)])
#guard (SharedTrigger.toEffect (.death .villainReturnAsHero)).resolution ==
  .put (.cause (some .villain)) .underOwner (.entering [
    .additionalSubtype .hero, .counter .finality])
#guard (SharedTrigger.toEffect (.death .attackingReturnHand)).resolution ==
  .returnToHand .cause
#guard (SharedTrigger.toEffect (.death .deathtouchOppSac)).resolution ==
  .sacrifice .chosenNontokenCreature
#guard (SharedTrigger.toEffect (.resource .discardExilePlay)).resolution ==
  .may (.exile .discarded .playUntilNextTurn) (.sequence []) .ifYouDo
#guard (SharedTrigger.toEffect (.resource .drawIfAnotherHeroDamage)).resolution ==
  .«if» (.atLeast (.count (.othersOfSubtype .hero)) (.fixed 1)) (.dealDamage (.fixed 1) (.player (.target .opponent)))
#guard (SharedTrigger.toEffect (.resource .secondDrawBecome66)).resolution ==
  .sequence [.setBasePT (.fixed 6) (.fixed 6) .source, .grant (.keywords #[Keyword.trample]) .source]
#guard (SharedTrigger.toEffect (.resource .secondDrawPlusOneTarget)).resolution ==
  .putCounters (.ofKind .plusOnePlusOne) .permanent
#guard (SharedTrigger.toEffect (.resource .secondDrawDrain)).resolution ==
  .sequence [.loseLife (.fixed 1) .eachOpponent, .gainLife (.fixed 1)]
#guard (SharedTrigger.toEffect (.resource .gainLifePlusOnes)).resolution ==
  .putCounters (.ofKind .plusOnePlusOne) .eachUpToLastKnown
#guard (SharedTrigger.toEffect (.resource .plusOneCreateInsectOnce)).resolution ==
  .createTokens 0 (.fixed 1) false &&
  (SharedTrigger.toEffect (.resource .plusOneCreateInsectOnce)).legacyToken 0 == .insect11green
#guard (SharedTrigger.toEffect (.resource .plusOneOnThisOnce)).resolution ==
  .putCounters (.ofKind .plusOnePlusOne) .source
#guard (SharedTrigger.toEffect (.resource .plusOneOnHeroesCreateWall)).resolution ==
  .may (.createTokens 0 (.fixed 1) false) (.sequence []) .ifYouDo &&
  (SharedTrigger.toEffect (.resource .plusOneOnHeroesCreateWall)).legacyToken 0 == .wall04defender

end Mtg.Engine
