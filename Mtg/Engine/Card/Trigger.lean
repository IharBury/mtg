import Mtg.Engine.Card.Counter
import Mtg.Engine.Card.Effect
import Mtg.Engine.Card.TriggerPattern

/-!
# Unified triggered abilities (CR 113.3c / 603 / 605.1b / 700.1 / 714.2b,d)

Defines the unified `TriggeredAbility` structure (`word`, `pattern`, `grouping`,
`interveningIf?`, `activeZones`, `limit`, `effect`, `modes`), structural
CR 605.1b `isManaAbility`, CR 714.2b/d Saga chapter helpers, functorial
`HasTextChange`, and the `SharedTrigger` / `ChapterResolution` effect builders.
-/

namespace Mtg.Engine

/-- A triggered ability (CR 113.3c / 603 / 605.1b / 700.1 / 714.2b,d). -/
structure TriggeredAbility where
  /-- Leading trigger word (`When`, `Whenever`, or `At`, CR 603.1). -/
  word : TriggerWord := .whenever
  /-- Declarative `RulesEvent` trigger condition (CR 603.2). -/
  pattern : TriggerPattern := TriggerPattern.thisEnters
  /-- Simultaneous-event batching semantics (CR 603.2c / 700.1 / 714.2b). -/
  grouping : BatchGrouping := .perOccurrence
  /-- Intervening `"if"` clause (CR 603.4): checked both when the trigger event
  occurs and again as the ability resolves (CR 608.2a). -/
  interveningIf? : Option Condition := none
  /-- Zones where this triggered ability functions (CR 113.6). Emblems
  additionally function in `.command` per CR 114.4. -/
  activeZones : Array ZoneKind := #[.battlefield]
  /-- Per-turn frequency cap (CR 603.2h). -/
  limit : TriggerLimit := .unlimited
  /-- Unified one-shot effect resolved by this triggered ability. -/
  effect : Effect := {}
  /-- Modes of a modal triggered ability (`"choose one/two —"`, CR 603.3c / 700.2). -/
  modes : Array Effect := #[]
deriving Repr, Inhabited, BEq

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

/-! ### Direct projections on `TriggeredAbility` -/

/-- Leftover shared trigger payload this ability resolves, when present. -/
def shared (ab : TriggeredAbility) : SharedTrigger :=
  ab.effect.asTrigger?.getD (.draw 0)

/-- How this triggered ability resolves. -/
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
  let effs : Array Effect := if ab.modes.isEmpty then #[ab.effect] else ab.modes
  !effs.any (fun e => !e.targetSpec.isEmpty) &&
    ab.pattern.triggersOnActivatedManaAbilityOrManaAdded &&
    effs.any (fun e => e.resolution.couldAddMana)

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

/-- Functorial Layer-3 text change across `pattern`, `interveningIf?`, `effect`, and `modes` (CR 612 / 613.1c). -/
instance : HasTextChange TriggeredAbility where
  applyTextChanges tcs ab :=
    if tcs.isEmpty then ab
    else
      { ab with
        pattern := HasTextChange.applyTextChanges tcs ab.pattern
        interveningIf? := ab.interveningIf?.map (HasTextChange.applyTextChanges tcs)
        effect := HasTextChange.applyTextChanges tcs ab.effect
        modes := ab.modes.map (HasTextChange.applyTextChanges tcs) }

/-- Targeting, zero-target allowance, and `TriggerResolution` for a printed Saga
chapter (CR 714.2). -/
def chapterResolutionSpec (e : ChapterResolution) : EffectTargeting × Bool × TriggerResolution :=
  match e with
  | .dealDamageToOppCreature n =>
    (.of .oppCreature, false, .dealDamage (.fixed n) .target)
  | .destroyOppArtifact =>
    (.of .oppArtifact, false, .destroy .target)
  | .addMana mana =>
    (.of .none, false, .addMana #[mana])
  | .searchBasicLandToHand =>
    (.of .none, false, .searchLibrary (.returnToHand .basicLand))
  | .gainLandfallCreateElf =>
    (.of .none, false, .grant .landfallCreateElf .source)
  | .elvesGetVigilance p =>
    (.of .none, false, .sequence [
      .pump (.fixed p) (.fixed 0) (.intersection [.creaturesYouControl, .youControl (.subtype .elf)]),
      .grant (.keywords #[Keyword.vigilance]) (.intersection [.creaturesYouControl, .youControl (.subtype .elf)])])
  | .opponentDiscardsNonland =>
    (.of .opponent, false, .discard .chosenNonland)
  | .amass n =>
    (.of .none, false, .amass (.fixed n))
  | .opponentLosesYouGain n =>
    (.of .opponent, false, .sequence [.loseLife (.fixed n) (.target .opponent), .gainLife (.fixed n)])
  | .grantHexproofWhileRemains =>
    (.of .creatureYouControl, false, .grant .hexproofWhileSource .target)
  | .preventDamageWhileRemains =>
    (.of .creature, true, .grant .preventDamageWhileSource .target)
  | .draw n =>
    (.of .none, false, .draw (.fixed n))
  | .searchBasicPlainsExileGainLife max life =>
    (.of .none, false, .sequence [
      .searchLibrary (.exile (.basicUpTo .plains max) .forLater .linked),
      .gainLife (.fixed life)])
  | .returnLinkedExileToHand =>
    (.of .none, false, .returnToHand .linkedExile)
  | .grantAttackPumpPerPlainsThisTurn =>
    (.of .none, false, .queueReflexive (.pump .perPlains .perPlains .target))
  | .blinkUntilEndStep =>
    (.of .creatureOrLandYouControl, true, .exile .target .nextEndStep)
  | .treasureThenDragonIfFour =>
    (.of .none, false, .sequence [
      .createTokens .treasure (.fixed 1) false,
      .«if» ((.atLeast (.count (.youControl (.subtype .treasure))) (.fixed 4)))
        (.sacrifice (.sacrificedSource .isSacrificed) .noted),
      .«if» .sourceWasSacrificed (.createTokens .dragon (.fixed 1) false)])
  | .recruit =>
    (.of .none, false, .recruit)
  | .returnCreatureFromGyMvAtMost n =>
    (.of (.creatureCardInYourGraveyardMvAtMost n), false, .put (.creatureMvAtMost n))
  | .plusOneUpToOne =>
    (.of .creature, true, .putCounters (.ofKind .plusOnePlusOne) .permanent)
  | .gainControlOfUpToTwoCreaturesTotalMvAtMost n =>
    (.of (.upToTwoCreaturesTotalMvAtMost n), true, .gainControl .whileSourceRemains)
  | .dealDamageToEachNonSubtypeAndOpponents n subtype =>
    (.of .none, false, .dealDamage (.fixed n) (.eachNonSubtypeAndOpponents subtype))
  | .dealXDamageToTargetOpponentGreatestArtifactMv =>
    (.of .opponent, false, .dealDamage .greatestArtifactMv (.player (.target .opponent)))
  | .spell s =>
    (s.targeting, s.allowsZeroTargets, TriggerResolution.ofSpell s.resolution)

/-- Construct a unified `Effect` for a printed `ChapterResolution`. -/
def chapterEffect (e : ChapterResolution) : Effect :=
  let (targeting, allowsZeroTargets, resolution) := chapterResolutionSpec e
  { targeting, allowsZeroTargets, resolution, sharedTrigger := some (.chapter 0 e) }

end TriggeredAbility

namespace SharedTrigger

/-- Build the unified `Effect` (targeting, zero-target/max-target/divided-damage
metadata, and `Resolution`) for a `SharedTrigger` payload. -/
def toEffect (s : SharedTrigger) : Effect :=
  let base : Effect :=
    match s with
    | .scry n => { resolution := .scry (.fixed n) }
    | .draw n => { resolution := .draw (.fixed n) }
    | .createTokens kind n tapped => { resolution := .createTokens kind (.fixed n) tapped }
    | .amass n subtype amount attachSource =>
      let resolved : TriggeredAbility.NumberSelector :=
        match amount with
        | .fixed => .fixed n
        | .sourcePower => .lastKnownPower
        | .notedExcess => .notedExcess
        | .notedPower => .notedPower
      { resolution := .amass resolved subtype attachSource }
    | .recruit who => { resolution := .recruit who }
    | .dividedDamage amount maxTargets =>
      { targeting := .of .anyTarget,
        dividedDamage := some (amount, maxTargets), resolution := .dividedDamage }
    | .gainLife n => { resolution := .gainLife (.fixed n) }
    | .connive who =>
      match who with
      | .source => { resolution := .connive .source }
      | .target kind => { targeting := .of kind, resolution := .connive .target }
      | .enteringVillain => { resolution := .connive .enteringVillain }
    | .exileUntilLeaves kind =>
      { targeting := .of kind, resolution := .exile .target .untilSourceLeaves }
    | .damageEachOpponent n =>
      { targeting := .of .opponent, resolution := .dealDamage (.fixed n) (.player .eachOpponent) }
    | .attachTo kind =>
      { targeting := .of kind, resolution := .attach .source .target }
    | .opponentSacrificesCreature =>
      { targeting := .of .opponent,
        resolution := .sacrifice .opponentChosenCreature }
    | .onPermanent kind action =>
      { targeting := .of kind
        resolution := TriggeredAbility.TriggerResolution.ofPermanent action }
    | .onSource action =>
      { resolution := TriggeredAbility.TriggerResolution.ofSource action }
    | .exileTop => { resolution := .exile .top .playUntilNextTurn }
    | .discard n => { resolution := .discard (.cards n) }
    | .mayTo can thenDo =>
      let left := toEffect can
      let right := toEffect thenDo
      { targeting :=
          if left.targeting.spec.isEmpty then right.targeting else left.targeting
        allowsZeroTargets := left.allowsZeroTargets || right.allowsZeroTargets
        maxTargets :=
          if left.targeting.spec.isEmpty then right.maxTargets else left.maxTargets
        dividedDamage :=
          match left.dividedDamage with
          | some d => some d
          | none => right.dividedDamage
        resolution := .may left.resolution right.resolution .ifYouDo }
    | .may action =>
      let inner := toEffect action
      { inner with resolution := .may inner.resolution (.sequence []) }
    | .opponentDiscards n who =>
      match who with
      | .each => { resolution := .discard (.cards n .eachOpponent) }
      | .target =>
        { targeting := .of .opponent, resolution := .discard (.cards n (.target .opponent)) }
    | .millPlayer n =>
      { targeting := .of .player, resolution := .mill (.fixed n) (.target .player) }
    | .investigate => { resolution := .investigate }
    | .pumpCause p t => { resolution := .pump (.fixed p) (.fixed t) .cause }
    | .searchLibrary => { resolution := .searchLibrary (.put .forest) }
    | .searchBasicLandToHand =>
      { resolution := .searchLibrary (.returnToHand .basicLand) }
    | .eachPlayerSacrificesCreature =>
      { resolution := .sacrifice .eachPlayersCreature }
    | .exileTarget kind =>
      { targeting := .of kind, resolution := .exile .target .leaveTrigger }
    | .returnCreatureFromGyToHand =>
      { targeting := .of .creatureCardInYourGraveyard,
        resolution := .returnToHand .graveyardCard }
    | .plusOneEachYouControl which =>
      { resolution := .putCounters (.ofKind .plusOnePlusOne) (.youControl which) }
    | .honeEachEquipment => { resolution := .honeEachEquipment }
    | .plusOneEachOtherGainLife =>
      { resolution := .sequence
          [.putCounters (.ofKind .plusOnePlusOne) .eachOther,
           .gainLife .perOtherCreature] }
    | .becomePT p t => { resolution := .becomePT (.fixed p) (.fixed t) }
    | .pumpTargetPerPlains =>
      { targeting := .of .creatureYouControl, resolution := .pump .perPlains .perPlains .target }
    | .mayDiscardHandDraw n =>
      { resolution := .may (.discard .hand) (.draw (.fixed n)) .ifYouDo }
    | .pumpByLookedAt => { resolution := .pump .perLookedAt .perLookedAt .source }
    | .pumpGreatestPower => { resolution := .pump .greatestPower (.fixed 0) .source }
    | .pumpForEachOtherCreature =>
      { resolution := .pump .perOtherCreature .perOtherCreature .source }
    | .damageBlockers n => { resolution := .dealDamage (.fixed n) .blockers }
    | .returnLinkedExile => { resolution := .put .linkedExile }
    | .createThenAttach kind =>
      { resolution := .sequence [.createTokens kind (.fixed 1) false, .attach .source .createdToken] }
    | .gainLifeSearchBasicOnTop n =>
      { resolution := .sequence [.gainLife (.fixed n), .searchLibrary (.put .basicLandOnTop)] }
    | .addMana types => { resolution := .addMana types }
    | .createAxe attach =>
      { resolution :=
          .createTokens .axe (.fixed 1) false
            (note := if attach then .attachReflexive else .none) }
    | .tapOppOrUntapYours =>
      { resolution := .or [.tap .target, .untap] }
    | .gainControlOppUntilEot =>
      { targeting := .of .oppCreature, resolution := .gainControl .untilEndOfTurn }
    | .payReturnFromGy =>
      { resolution := .may
          (.pay (CostSpec.ofMana { symbols := #[.generic 1, .colored .green, .colored .blue] }))
          (.returnToHand .source) .ifYouDo }
    | .targetOpponentLosesLife n =>
      { targeting := .of .opponent, resolution := .loseLife (.fixed n) (.target .opponent) }
    | .drawXDiscard n =>
      { resolution := .sequence
          [.draw .equalToManaSpent, .«if» .manaSpent (.discard (.cards n))] }
    | .ringTempts => { resolution := .ringTempts }
    | .setOtherBasePT =>
      { targeting := .of .anotherCreatureYouControl, allowsZeroTargets := true,
        resolution := .setBasePT .equalSourcePower .equalSourceToughness }
    | .returnElfGainLife =>
      { targeting := .of .elfInYourGraveyard
        resolution := .sequence
          [.returnToHand .graveyardCard, .gainLife .equalToTargetPower] }
    | .damageFromLastKnownPower =>
      { targeting := .of .oppCreature,
        resolution := .dealDamage .lastKnownPower .permanent }
    | .mayPayGenericDraw n plusOne =>
      { resolution :=
          if plusOne then
            .may (.pay (CostSpec.ofGeneric n))
              (.sequence [.putCounters (.ofKind .plusOnePlusOne) .source, .draw (.fixed 1)]) .ifYouDo
          else
            .may (.pay (CostSpec.ofGeneric n)) (.draw (.fixed 1)) .ifYouDo }
    | .drawThenBottomIfNoLegendary =>
      { resolution := .sequence
          [.draw (.fixed 1), .«if» (.not (.atLeast (.count .legendaryCreaturesYouControl) (.fixed 1))) (.putOnLibrary .bottom .cardFromHand)] }
    | .removeHopeDrawSac =>
      { resolution := .sequence
          [.removeCounters .hope .source, .«if» .removedHope (.draw (.fixed 1)), .«if» (.not .hopeOnSource) (.sequence [.sacrifice .source, .gainLife (.fixed 4)])] }
    | .tapHumansDraw =>
      { resolution := .sequence
          [.may (.tap .humans) (.sequence []), .draw .forEachTappedHuman] }
    | .destroyOppArtifactsEnchantmentsGainLife =>
      { resolution := .sequence
          [.destroy .oppArtifactsEnchantments (note := .countDestroyed),
           .gainLife .forEachDestroyedThisWay] }
    | .damageEqualSubtypeToEachOpponent subtype =>
      { resolution := .dealDamage (.subtypeCount subtype) (.player .eachOpponent) }
    | .damageEqualTreasures =>
      { targeting := .of .anyTarget,
        resolution := .dealDamage (.subtypeCount .treasure) .target }
    | .dealDamageDestroyIfSubtype n subtype =>
      { targeting := .of .anyTarget,
        resolution := .sequence
          [.dealDamage (.fixed n) .target .markedPermanent,
           .«if» (.dealtDamageToSubtype subtype) (.destroy .permanentDealtDamage)] }
    | .attachEquipmentToCreature =>
      -- *Iron Hills Stalwart*: the Equipment target is mandatory (slot 0); only the creature
      -- slot is optional (`count := .upTo 1`), so the trigger is removed when you control
      -- no Equipment (CR 115.1c / 603.3d).
      { targeting := .of .equipmentYouControlThenCreatureYouControl,
        allowsZeroTargets := false, resolution := .attach .target .optionalCreature }
    | .defenderSacsLeastPower =>
      { resolution := .sacrifice .leastPower }
    | .returnOtherPlusOne =>
      { targeting := .of (.single {
          domain := .object .battlefield (.all #[.otherThan .this, .controlledBy .you])
          count := .upTo 1 })
        allowsZeroTargets := true
        resolution := .sequence
          [.returnToHand .permanent .returnedPermanent,
           .«if» .returnedPermanent (.putCounters (.ofKind .plusOnePlusOne) .source)] }
    | .lookAtTopRevealTypes n types =>
      { resolution := .lookAtTopRevealTypes (.fixed n) types }
    | .createTappedTreasuresEqualOppArtifacts =>
      { resolution := .createTokens .treasure .oppArtifacts true }
    | .putNonlandMvAtMostFromGy mv =>
      { targeting := .of (.single {
          domain := .object .anyGraveyard (.all #[
            .not (.hasType .land), .isKind .permanentCard, .stat .manaValue .le (.const mv)])
          count := .upTo 1 })
        allowsZeroTargets := true, resolution := .put (.nonlandMvAtMost mv) }
    | .othersGetAndOppsGet subtypes p t oppP oppT =>
      { resolution := .sequence
          [.pump (.fixed p) (.fixed t) (.intersection [.creaturesYouControl, .union (subtypes.toList.map .othersOfSubtype)]),
           .pump (.fixed oppP) (.fixed oppT) .opponentsCreatures] }
    | .wolfPlusOneOrTreasure =>
      { resolution := .or
          [.putCounters (.ofKind .plusOnePlusOne) .permanent,
           .createTokens .treasure (.fixed 1) false] }
    | .trampleCounterBecomeBear =>
      { targeting := .of .creatureYouControl, allowsZeroTargets := true,
        resolution := .sequence
          [.putCounters (.ofKind .trample) .permanent, .becomeBear, .«if» ((.atLeast (.count (.youControl (.subtype .bear))) (.fixed 3))) (.draw (.fixed 2))] }
    | .millThenSubtypeToHand n subtype =>
      { resolution := .sequence
          [.mill (.fixed n) (note := .milledCards), .returnToHand (.milledSubtype subtype)] }
    | .exileOppNonlandEachUntilLeaves =>
      { targeting := .of (.forEachOpponentControlled (.not (.hasType .land)) (.upTo 1))
        allowsZeroTargets := true
        resolution := .exile (.target .eachPermanent) .untilSourceLeaves }
    | .plusOneEqualLastKnownMv =>
      { targeting := .of .creatureYouControl,
        resolution := .putCounters .plusOneLastKnownMv .permanent }
    | .mountainQuestDragon =>
      { resolution := .sequence [.putCounters (.ofKind .quest) .source, .«if» ((.atLeast (.count .questCounters) (.fixed 6))) (.sequence [.sacrifice (.sacrificedSource .movedAsSacrificed), .searchLibrary (.put .dragon)])] }
    | .treasuresPerChosenType =>
      { resolution := .createTokens .treasure .chosenCreatureType false }
    | .revealUntilCreature =>
      { resolution := .revealLibrary .untilCreature
          (.ifElse .revealedManaValueAtMostLands (.put .revealed) (.returnToHand .revealed)) }
    | .attackSacPlusOneEqualPower =>
      { resolution := .may (.pay CostSpec.sacrificeAnotherCreature)
          (.putCounters .plusOneSacrificedPower .source) .ifYouDo }
    | .lootLandEntersTapped =>
      { resolution := .sequence
          [.draw (.fixed 1), .discard (.cards 1), .put .discardedLand (how := .tapped)] }
    | .millThatManyLost =>
      { resolution := .mill .thatManyLost .thatPlayer }
    | .drawPerFatGraveyard =>
      { resolution := .draw .perFatGraveyard }
    | .maySacDrawTreasure =>
      { resolution := .may (.pay CostSpec.sacrificeAnotherCreatureOrArtifactSpec)
          (.sequence [.draw (.fixed 1), .createTokens .treasure (.fixed 1) false]) .ifYouDo }
    | .castInstantSorceryFromHand =>
      { resolution := .mayCast .hand .twiceLegendaryWizards .withoutPaying }
    | .castInstantSorceryMvAtMost =>
      { resolution := .mayCast .hand .lastKnown .withoutPaying }
    | .millThenCopy =>
      { resolution := .sequence
          [.mill (.fixed 2) .eachOpponent (note := .opponentsMilled),
           .«if» .opponentsMilled (.queueReflexive (.mayCast .milledSpell .causingSpell .withoutPaying))] }
    | .pumpTargetBySourcePower =>
      { targeting := .of .anotherCreatureYouControl,
        resolution := .pump .equalSourcePower (.fixed 0) .target }
    | .createAlienPerInvasion =>
      { resolution := .sequence
          [.createTokens .alien (.fixed 1) false (note := .invasion),
           .putCounters .plusOneNoted .createdToken,
           .putCounters (.ofKind .invasion) .source] }
    | .mayPutArtifactAttachEquipment =>
      { resolution := .sequence
          [.may (.put .artifactFromHand (note := .forAttach)) (.sequence []),
           .«if» (.atLeast (.count .putEquipment) (.fixed 1)) (.attach .putArtifact .notedHost)] }
    | .cascade => { resolution := .cascade }
    | .belladonnaTokenReward =>
      { resolution := .sequence [
          .noteResolveThisTurn 3,
          .«if» (.nthResolve 1) (.gainLife (.fixed 1)),
          .«if» (.nthResolve 2) (.draw (.fixed 1)),
          .«if» (.nthResolve 3) (.putCounters (.ofKind .plusOnePlusOne) .youControl)] }
    | .bolgMaySacrifice => { resolution := .may (.sacrifice .another) (.sequence []) }
    | .bolgDealSacrificedPower =>
      { targeting := .of .anotherCreature,
        resolution := .sequence
          [.dealDamage .lastKnownPower .permanent .excess,
           .amass .notedExcess] }
    | .createSpiritsForEquipped =>
      { resolution := .sequence
          [.createTokens .spirit (.fixed 2) true, .«if» (.atLeast (.count (.intersection [.equipped, .legendaryCreaturesYouControl])) (.fixed 1)) .markRecentTokensAttacking] }
    | .createTreasuresEqualDamagedPlayerArtifacts =>
      { resolution :=
          .createTokens .treasure .damagedPlayerArtifacts false }
    | .deal1ThenAmassOrcs =>
      { targeting := .of .anyTarget,
        resolution := .sequence
          [.dealDamage (.fixed 1) .target .markedPermanent, .amass (.fixed 1) .orc] }
    | .untapAttackersExtraCombat _n =>
      { resolution := .sequence [.untap .attackingCreatures, .additionalCombatPhase] }
    | .eaglesCreateBirds =>
      { resolution := .createTokens .birdSoldier .lastKnownPower false }
    | .allianceMode =>
      { resolution := .chooseModes TriggeredAbility.TriggerResolution.allianceModes
          .oneUnusedThisTurn }
    | .destroyOtherAmassControllerPower =>
      { targeting := .of .anotherCreature, allowsZeroTargets := true,
        resolution := .sequence
          [.destroy .target (note := .forAmass),
           .amass .notedPower (who := .controller .target),
           .«if» .youControlledDestroyed (.draw (.fixed 1))] }
    | .gollumMode =>
      { resolution := .chooseModes TriggeredAbility.TriggerResolution.gollumModes
          .oneUnused }
    | .discardHandDrawDamageIfStory =>
      { resolution := .sequence
          [.may (.discard .hand) (.sequence []), .draw .discardedHand,
           .«if» .enduringStoryNoted (.dealDamage .discardedHand (.player .eachOpponent))] }
    | .castFromGyArtifactInstantSorcery =>
      { resolution := .mayCast .graveyard .unlimited .pay .exileInstead }
    | .equippedAttackersGainDoubleStrike =>
      { resolution := .grant .doubleStrike .equippedAttackers }
    | .tapEnchantedRemoveCounters =>
      { resolution := .sequence [.tap .enchanted, .removeCounters .all .enchanted] }
    | .revealTopPutRandomCreature n =>
      { resolution := .revealLibrary (.top n) (.put .randomCreature) }
    | .beginCombatIfDrawnTwoPump =>
      { targeting := .of .anotherCreatureYouControl,
        resolution := .«if» (.atLeast .cardsDrawnThisTurn (.fixed 2)) (.sequence [
          .pump (.fixed 3) (.fixed 0) .target,
          .grant (.keywords #[Keyword.firstStrike]) .target]) }
    | .honePerOppAttach =>
      { targeting := .of (.ofSlots #[.of .opponent, { domain := .creatureYouControl, count := .upTo 1 }])
        resolution := .sequence
          [.putCounters .honePerOpponent .source, .attach .source (.target .laterCreature)] }
    | .damageTargetOpponent n =>
      { targeting := .of .opponent, resolution := .dealDamage (.fixed n) (.player (.target .opponent)) }
    | .copySelfNonlegendary => { resolution := .copySelfNonlegendary }
    | .attachEquipmentThenFight =>
      { targeting := .of .creatureYouControl,
        resolution := .sequence [.attach .anyYouControl .target,
          .«if» .equipmentAttached (.fight .equipmentHost .reflexive)] }
    | .returnAsArtifact => { resolution := .put .source (how := .asArtifact) }
    | .exileLandsThenReturnTapped =>
      { targeting := .of (.single {
          domain := .object .battlefield (.all #[.hasType .land, .controlledBy .you])
          count := .upTo 3 })
        allowsZeroTargets := true, maxTargets := 3
        resolution := .sequence
          [.exile .landsYouControl .forLater .lands,
           .put .notedLands (how := .tapped)] }
    | .grimaImpulse =>
      { resolution := .sequence
          [.revealLibrary .untilInstantOrSorcery (.exile .top .forLater .impulse) .damagedPlayer,
           .mayCast .impulse .unlimited .withoutPaying] }
    | .palantir =>
      { targeting := .of .opponent,
        resolution := .sequence
          [.putCounters (.ofKind .influence) .source, .scry (.fixed 2),
           .may (.draw (.fixed 1) (who := .opponentHasYou)) (.sequence [])] }
    | .treasuresEqualLastKnown =>
      { resolution := .createTokens .treasure .lastKnownPower false }
    | .protectionEverything =>
      { resolution := .grant .protectionEverything .youIfCast }
    | .loseLifePerBurden => { resolution := .loseLife .perBurden }
    | .revealSaga =>
      { resolution := .revealLibrary .untilSaga (.put .revealed) }
    | .sacDamagersRingTempts =>
      { resolution := .sequence [.sacrifice .combatDamager, .ringTempts] }
    | .chapter _n e =>
      TriggeredAbility.chapterEffect e
    | .drawIfAttackedOrEnteredSubtype subtype =>
      { resolution := .«if»
          (.or [.attackedWithSubtype subtype, .subtypeEntered subtype])
          (.draw (.fixed 1)) }
    | .othersOfSubtypeGetEqualSourceToughness subtype =>
      { resolution := .pump .equalSourceToughness .equalSourceToughness
          (.othersOfSubtype subtype) }
    | .scryAndPlan n =>
      { resolution := .sequence [.putCounters (.ofKind .plan) .source, .scry (.fixed n)] }
    | .lootAndPlan =>
      { resolution := .sequence
          [.putCounters (.ofKind .plan) .source, .draw (.fixed 1), .discard (.cards 1)] }
    | .createVillainAndPlan =>
      { resolution := .sequence
          [.putCounters (.ofKind .plan) .source, .createTokens .villain21menace (.fixed 1) false] }
    | .drainAndPlan n =>
      { resolution := .sequence
          [.putCounters (.ofKind .plan) .source, .loseLife (.fixed n) .eachOpponent, .gainLife (.fixed n)] }
    | .drawLoseLifeAndPlan =>
      { resolution := .sequence
          [.putCounters (.ofKind .plan) .source, .draw (.fixed 1), .loseLife (.fixed 1)] }
    | .treasureTappedAndPlan =>
      { resolution := .sequence
          [.putCounters (.ofKind .plan) .source, .createTokens .treasure (.fixed 1) true] }
    | .plusOneOnTargetAndPlan =>
      { targeting := .of .creatureYouControl,
        resolution := .sequence
          [.putCounters (.ofKind .plan) .source,
           .putCounters (.ofKind .plusOnePlusOne) (.permanent true)] }
    | .planFinishDrawPlusOneEach =>
      { resolution := .sequence
          [.sacrifice .plan, .draw (.fixed 1), .putCounters (.ofKind .plusOnePlusOne) .youControl] }
    | .planFinishReturnInstants =>
      { resolution := .sequence
          [.sacrifice .plan .forReflexive,
           .«if» .planWasSacrificed (.queueReflexive (.returnToHand (.graveyardInstants 2)))] }
    | .planFinishControlOpponent =>
      { resolution := .sequence
          [.sacrifice .plan .forReflexive,
           .«if» .planWasSacrificed (.queueReflexive (.gainControl .duringNextTurn))] }
    | .planFinishExileTopCast =>
      { resolution := .sequence
          [.sacrifice .plan .forReflexive,
           .«if» .planWasSacrificed (.queueReflexive (.exile (.opponentTop 5) (.mayCastUpTo 2)))] }
    | .planFinishCreateRobots n =>
      { resolution := .sequence
          [.sacrifice .plan, .createTokens .robotVillain22 (.fixed n) false] }
    | .planFinishDividedDamage n =>
      { resolution := .sequence
          [.sacrifice .plan .forReflexive,
           .«if» .planWasSacrificed (.queueReflexive (.dealDamage (.fixed n) .target .divided))] }
    | .planFinishIndestructibleOnTarget =>
      { resolution := .sequence
          [.sacrifice .plan .forReflexive,
           .«if» .planWasSacrificed (.queueReflexive (.putCounters (.ofKind .indestructible) .permanent))] }
    | .surveil n => { resolution := .surveil (.fixed n) }
    | .empowerJace n => { resolution := .empowerJace (.fixed n) }
    | .prepareSource k => { resolution := .prepareSource k }
    | .drawIfRemovedTwoLoyalty =>
      { resolution := .«if» (.atLeast .lastKnownPower (.fixed 2)) (.draw (.fixed 1)) }
    | .loyaltyOnSource =>
      { resolution := .putCounters (.ofKind .loyalty) .source }
    | .grantThenCounterByType k =>
      { targeting := .of .permanentYouControl,
        resolution := .sequence
          [.grant (.keywords k) .target,
           .«if» (.atLeast (.count (.target .creature)) (.fixed 1)) (.putCounters (.ofKind .plusOnePlusOne) .permanent),
           .«if» (.atLeast (.count (.target .planeswalker)) (.fixed 1)) (.putCounters (.ofKind .loyalty) .permanent)] }
    | .destroyOppPermanentIfSixLands =>
      { targeting := .of .oppPermanent,
        resolution := .«if» ((.atLeast (.count .landsYouControl) (.fixed 6))) (.sequence [
          .destroy .target,
          .createTokens .treasure (.fixed 1) false (who := .controller .target)]) }
    | .pumpOrCounterIfScried =>
      { targeting := .of .anotherCreatureYouControl,
        resolution := .ifElse (.or [.scriedThisTurn, .surveilledThisTurn])
          (.putCounters (.ofKind .plusOnePlusOne) .permanent)
          (.pump (.fixed 1) (.fixed 1) .target) }
    | .sacrificeSourceIfNoPlaneswalker =>
      { resolution := .«if» (.not (.atLeast (.count .planeswalkersYouControl) (.fixed 1))) (.sacrifice (.sacrificedSource .controllerSacrifices)) }
    | .creaturesYouControlGet p t =>
      { resolution := .pump (.fixed p) (.fixed t) .creaturesYouControl }
    | .putSourceCountersOnTarget =>
      { targeting := .of .creatureYouControl, allowsZeroTargets := true,
        resolution := .putCounters .sourceCounters .permanent }
    | .chargeCounterOnSource =>
      { resolution := .putCounters (.ofKind .charge) .source }
    | .addGreenPerChargeCounter =>
      { resolution := .addMana #[.colored .green] .perChargeCounter }
    | .drawTwoWinIfEmptyShuffleSource =>
      { resolution := .sequence
          [.draw (.fixed 2), .«if» (.not (.atLeast .libraryCards (.fixed 1))) .winTheGame, .«if» (.atLeast .libraryCards (.fixed 1)) .shuffleSource] }
    | .surveilReturnIfGainedLife =>
      { resolution := .sequence [.armSurveilReturnLifeGained, .surveil (.fixed 1)] }
    | .pumpIfFiveOtherForests =>
      { targeting := .of .creatureYouControl,
        resolution := .«if» ((.atLeast (.count .forestsExceptCause) (.fixed 5))) (.pump (.fixed 3) (.fixed 3) .target) }
    | .onEnchanted action =>
      { resolution := TriggeredAbility.TriggerResolution.ofEnchanted action }
    | .attachThen followup =>
      { targeting := .of .creatureYouControl,
        resolution := .sequence
          ([.attach .source .target] ++
            (TriggeredAbility.TriggerResolution.ofTargetWhileSource followup).flatten) }
    | .exileOtherCopyEnchanted =>
      { targeting := .of .creature, allowsZeroTargets := true,
        resolution := .sequence
          [.exile .target .untilSourceLeaves .copyAndHost, .becomeCopy .noted] }
    | .exileUntilNextEndStep =>
      { targeting := .of .creatureYouControl, allowsZeroTargets := true,
        resolution := .exile .target .nextEndStep }
    | .tapOrUntapNonland =>
      { targeting := .of .nonland, allowsZeroTargets := true,
        resolution := .or [.tap .target, .untap] }
    | .createFoodOrTreasure =>
      { resolution := .or
          [.createTokens .food (.fixed 1) false, .createTokens .treasure (.fixed 1) false] }
    | .villainIfGyElseMill =>
      { resolution := .ifElse ((.atLeast (.count .creatureCardsInGraveyard) (.fixed 2)))
          (.createTokens .villain21menace (.fixed 1) true) (.mill (.fixed 2)) }
    | .drawMayPutLandTapped =>
      { resolution := .sequence
          [.draw (.fixed 1), .may (.put .landFromHand (how := .tapped)) (.sequence [])] }
    | .drawGainLifeIfAnotherHero =>
      { resolution := .sequence [.draw (.fixed 1), .«if» (.atLeast (.count (.othersOfSubtype .hero)) (.fixed 1)) (.gainLife (.fixed 2))] }
    | .plusOneOrTwoIfAnotherHero =>
      { targeting := .of .creature,
        resolution := .ifElse ((.atLeast (.count (.target (.anotherSubtype .hero))) (.fixed 1)))
          (.putCounters (.ofKind .plusOnePlusOne 2) .permanent)
          (.putCounters (.ofKind .plusOnePlusOne) .permanent) }
    | .maySacArtifactOrDiscardDraw =>
      { resolution := .may (.pay CostSpec.sacrificeArtifactOrDiscardCard) (.draw (.fixed 1)) .ifYouDo }
    | .enter (.destroy kind) =>
      { targeting := .of kind, resolution := .destroy .target }
    | .enter (.dealDamageUpToOne n) =>
      { targeting := .of .creature, allowsZeroTargets := true,
        resolution := .dealDamage (.fixed n) .target }
    | .enter .fightUpToOne =>
      { targeting := .of .anotherCreature, allowsZeroTargets := true,
        resolution := .fight }
    | .enter .returnNonlandNontoken =>
      { targeting := .of .nonlandNontoken, allowsZeroTargets := true,
        resolution := .returnToHand .permanent .returnedPermanent }
    | .enter .createZabu =>
      { resolution := .createTokens .zabu (.fixed 1) false }
    | .enter .oppCreatesTheVoid =>
      { targeting := .of .opponent,
        resolution := .createTokens .theVoid (.fixed 1) false (.target .opponent) }
    | .enter .createSturdyShieldAttach =>
      { resolution := .sequence
          [.createTokens .sturdyShield (.fixed 1) false (note := .remember),
           .attach .createdToken .source] }
    | .enter .exileGyPlayUntilNextTurn =>
      { targeting := .of .equipmentInstantOrSorceryInYourGraveyard,
        resolution := .sequence
          [.exile .graveyardCard .forLater .playCard, .grantPlayNotedUntilNextTurn] }
    | .enter .returnGyPermanentThisTurn =>
      { targeting := .of .permanentCardInYourGraveyard,
        resolution := .returnToHand .graveyardPermanent }
    | .enter .tapOppCantUntapWhileControl =>
      { targeting := .of .oppCreature,
        resolution := .sequence [.tap .target, .cant .untapWhileYouControl] }
    | .enter .maySacAnotherThenDestroyOppNonland =>
      { resolution := .may (.pay CostSpec.sacrificeAnotherCreature) (.queueReflexive (.destroy .target)) .ifYouDo }
    | .enter .maySacOrDiscardNonlandThenDamage =>
      { resolution := .may (.pay CostSpec.sacrificeArtifactOrDiscardNonland)
          (.queueReflexive (.dealDamage (.fixed 2) .target)) .ifYouDo }
    | .enter .revealHandExileUntilLeaves =>
      { targeting := .of .opponent, allowsZeroTargets := true,
        resolution := .revealFromHand .hand (.exile .target .untilSourceLeaves) }
    | .enter .plusOnesOrReturnArtEnch =>
      { targeting := .of .creature, allowsZeroTargets := true,
        resolution := .or
          [.putCounters (.ofKind .plusOnePlusOne) .permanent,
           .returnToHand .graveyardCard] }
    | .enter .chooseUpToXModes =>
      { targeting := .of .opponent, allowsZeroTargets := true,
        resolution := .chooseModes TriggeredAbility.TriggerResolution.upToXModes
          .alreadyChosen }
    | .enter .mayTapThenGrantIndestructible =>
      { resolution := .may (.tap .source) (.queueReflexive (.grant (.keywords #[Keyword.indestructible]) .target)) .ifYouDo }
    | .enter .tapLoseAbilitiesWhileSource =>
      { targeting := .of .creature, allowsZeroTargets := true,
        resolution := .sequence
          [.tap (.target .ifPresent), .lose .allAbilities (.target .ifPresent)] }
    | .enter .revealDiscardFromHand =>
      { targeting := .of .player,
        resolution := .revealFromHand .onePlusCreatureCards
          (.discard (.cards 1 (.target .opponent))) }
    | .enter .createRedwing =>
      { resolution := .createTokens .redwing (.fixed 1) false }
    | .step .enchantedControllerDraws =>
      { resolution := .draw (.fixed 1) (who := .controller .enchanted) }
    | .step .drawToTen =>
      { resolution := .draw (.upToHandSize 10) }
    | .step .copyAbsorbingMan =>
      { targeting := .of (.single {
          domain := .object .battlefield (.any #[
            .hasType .artifact,
            .all #[.not (.hasSubtype (.literal .aura)), .hasType .enchantment],
            .hasType .land])
          count := .upTo 1 })
        allowsZeroTargets := true, maxTargets := 1
        resolution := .becomeCopy .artifactEnchantmentOrLand }
    | .step .hydeChoose =>
      { resolution := .chooseModes TriggeredAbility.TriggerResolution.hydeModes
          .plusOneOrRemoveCounter }
    | .step .copyTaskmaster =>
      { targeting := .of .creatureOrGyCreatureCard,
        allowsZeroTargets := true, maxTargets := 1
        resolution := .becomeCopy .creatureOrGraveyardCard }
    | .step .harnessedFlicker =>
      { targeting := .of (.single {
          domain := .object .battlefield (.all #[.otherThan .this, .not (.hasType .land), .controlledBy .you])
          count := .upTo 1 })
        allowsZeroTargets := true, maxTargets := 1
        resolution := .«if» (.atLeast (.count .harnessedSource) (.fixed 1)) (.exile .target .returnImmediately) }
    | .death .hellcatReturn =>
      { resolution := .put .source .underOwner (.entering [
          .loseAllAbilities, .keywords #[Keyword.haste],
          .counter .plusOnePlusOne (asEnters := true)]) }
    | .death .villainReturnAsHero =>
      { resolution := .put (.cause (some .villain)) .underOwner (.entering [
          .additionalSubtype .hero, .counter .finality]) }
    | .death .attackingReturnHand =>
      { resolution := .returnToHand .cause }
    | .death .deathtouchOppSac =>
      { resolution := .sacrifice .chosenNontokenCreature }
    | .thisAttack .mayPayPlusOne =>
      { resolution := .may (.pay (CostSpec.ofGeneric 1)) (.queueReflexive (.putCounters (.ofKind .plusOnePlusOne) .permanent)) .ifYouDo }
    | .thisAttack .payReturnAttacking =>
      { resolution := .may (.pay (CostSpec.ofMana { symbols := #[.generic 3, .colored .black] }))
          (.queueReflexive (.put .creatureCard .tapped (.entering [.attacking, .counter .finality]))) .ifYouDo }
    | .thisAttack .ifArtifactEnteredDraw =>
      { resolution := .«if» .artifactEnteredThisTurn (.draw (.fixed 1)) }
    | .thisAttack .blinkNontoken =>
      { targeting := .of (.single {
          domain := .object .battlefield (.all #[.isToken false, .any #[.hasType .artifact, .hasType .creature]])
          count := .upTo 1 })
        allowsZeroTargets := true, maxTargets := 1
        resolution := .exile .target .returnTapped }
    | .thisAttack .equippedDrain =>
      { resolution := .«if» .attachedEquipment (.sequence [
          .loseLife .attachedEquipment .eachOpponent,
          .gainLife .attachedEquipment]) }
    | .thisAttack .drawIfPower4 =>
      { resolution := .«if» (.atLeast .equalSourcePower (.fixed 4)) (.draw (.fixed 1)) }
    | .thisAttack .attacksAlonePlus2Indestructible =>
      { resolution := .sequence [
          .pump (.fixed 2) (.fixed 0) .source,
          .grant (.keywords #[Keyword.indestructible]) .source] }
    | .enterOrAttack .copyKeywords =>
      { targeting := .of .anotherCreature,
        resolution := .putCounters .missingKeywordsFromTarget .source }
    | .enterOrAttack .createSquirrel =>
      { resolution := .createTokens .squirrel11green (.fixed 1) false }
    | .watch .combatDamageExileUntilNonland =>
      { resolution := .revealLibrary .untilNonland
          (.may (.putCounters (.ofKind .plusOnePlusOne) .source)
            (.exile .top .forLater .anyManaThisTurn) .ifYouDont)
          .announced }
    | .watch .attacksAloneDrain =>
      { targeting := .of .opponent,
        resolution := .sequence [.loseLife (.fixed 1) (.target .opponent), .gainLife (.fixed 1)] }
    | .watch .attacksAloneFirstStrikeMenace =>
      { resolution := .grant
          (.keywords #[Keyword.firstStrike, Keyword.menace]) .attackingAlone }
    | .watch .firstTapUntap =>
      { resolution := .untap .firstThisTurn }
    | .watch .sheHulkRedirectOnce =>
      { targeting := .of .anyTarget,
        resolution := .may (.dealDamage .lastKnownPower .target) (.sequence []) .ifYouDo }
    | .watch .speedballTargeted =>
      { resolution := .sequence [
          .pump (.fixed 2) (.fixed 2) .source, .may .retargetCause (.sequence []) .ifYouDo] }
    | .watch .anyPlayerSecondDraw =>
      { resolution := .draw (.fixed 1) }
    | .watch .youTargetDrawOnce =>
      { resolution := .draw (.fixed 1) }
    | .watch .villainOrArtifactDamage =>
      { targeting := .of .opponent,
        resolution := .dealDamage (.fixed 1) (.player (.target .opponent)) }
    | .watch .villainConniveOnce =>
      { resolution := .connive .enteringVillain }
    | .watch .villainPlusOneDamageOnce =>
      { resolution := .sequence [
          .putCounters (.ofKind .plusOnePlusOne) .sourceIfPresent,
          .dealDamage (.fixed 2) (.player .eachOpponent)] }
    | .watch .villainAttachEquipment =>
      { targeting := .of .upToOneEquipmentThenCreatureYouControl
        resolution := .attach .announcedEquipment .announcedCreature }
    | .watch .villainPlusOneLifelink =>
      { resolution := .sequence [
          .pump (.fixed 1) (.fixed 0) .source, .grant (.keywords #[Keyword.lifelink]) .source] }
    | .watch .hulklingCompare =>
      { resolution := .«if» (.or [.causeGreaterPower, .causeGreaterToughness])
          (.putCounters (.ofKind .plusOnePlusOne) .source) }
    | .watch .justiceBounce =>
      { resolution := .putCounters (.ofKind .plusOnePlusOne) .source }
    | .watch .nontokenHeroModal =>
      { resolution := .chooseModes
          [.createTokens .soldier11white (.fixed 1) false,
           .pump (.fixed 1) (.fixed 1) .creaturesYouControl]
          .fromLastKnown }
    | .watch .ultronCopy =>
      { resolution := .may (.pay (CostSpec.ofGeneric 2)) (.becomeCopy .cause) .ifYouDo }
    | .watch .enchantedAttachEquipment =>
      { targeting := .of .equipmentYouControl
        allowsZeroTargets := true, maxTargets := 1000,
        resolution := .attach (.target .eachEquipment) .enchantedCreature }
    | .watch .equippedAttacksAloneUntapScry =>
      { resolution := .sequence [.untap .equipped, .scry (.fixed 1)] }
    | .watch .equippedAttacksTap =>
      { targeting := .of .defendingPlayerCreature,
        resolution := .tap .target }
    | .watch .equippedTappedDamage =>
      { resolution := .dealDamage (.fixed 1) (.player .eachOpponent) .fromEquipped }
    | .watch .heroesDamagePlusTwo =>
      { resolution := .putCounters (.ofKind .plusOnePlusOne 2) .source }
    | .watch .merfolkAttackDraw =>
      { resolution := .draw (.fixed 1) }
    | .watch .tokensEnterMayDraw =>
      { resolution := .may (.draw (.fixed 1)) (.sequence []) .ifYouDo }
    | .watch .hawkeyeModes =>
      { allowsZeroTargets := true,
        resolution := .may (.pay (CostSpec.ofGeneric 1)) (.queueReflexive (.chooseModes TriggeredAbility.TriggerResolution.trickArrowModes .alreadyChosen)) .ifYouDo }
    | .watch .redHulk =>
      { resolution := .sequence [
          .putCounters (.ofKind .plusOnePlusOne) .source,
          .queueReflexive (.dealDamage .plusOneCounters .target)] }
    | .watch .hulk =>
      { resolution := .sequence [
          .putCounters (.ofKind .plusOnePlusOne) .source,
          .«if» (.atLeast (.count (.intersection [.source, .attackingCreatures])) (.fixed 1)) (.untap .source),
          .«if» .enrageGrantsCombat .additionalCombatPhase] }
    | .youAttacking .pay2LifeToughness =>
      { resolution := .may (.loseLife (.fixed 2))
          (.grant .assignCombatDamageEqualToughness .creaturesYouControl) .ifYouDo }
    | .youAttacking .exileTopHeroPump =>
      { resolution := .may (.exile .top .playThisTurn .ifHero) (.sequence []) }
    | .youAttacking .lookSixCast =>
      { resolution := .revealLibrary (.top 6)
          (.mayCast .looked .greatestAttackingPower .withoutPaying) }
    | .casting .villainToken =>
      { resolution := .createTokens .villain21menace (.fixed 1) false }
    | .casting .merfolkFromBlue =>
      { resolution := .createTokens .merfolk .blueManaSymbols false }
    | .casting .mayPayHasteUnblockable =>
      { resolution := .may (.pay (CostSpec.ofGeneric 1)) (.queueReflexive (.cant (.beBlockedExceptByHaste .target))) .ifYouDo }
    | .casting .plusOneEachOther =>
      { resolution := .putCounters (.ofKind .plusOnePlusOne) .eachOther }
    | .casting .exileFlicker =>
      { targeting := .of (.ofDomain (.object .battlefield (.all #[
          .otherThan .this, .not (.hasType .land), .isToken false])))
        resolution := .exile .target .nextEndStep }
    | .casting .visionModes =>
      { resolution := .chooseModes TriggeredAbility.TriggerResolution.visionModes .vision }
    | .casting .damageEqualMv =>
      { targeting := .of .anyTarget,
        resolution := .dealDamage .spellManaValue .target }
    | .casting .drawPowerEqualHand =>
      { resolution := .sequence [.draw (.fixed 1), .grant .basePowerEqualHand .source] }
    | .casting .plusOneThis =>
      { resolution := .putCounters (.ofKind .plusOnePlusOne) .source }
    | .casting .plusOneScry =>
      { resolution := .sequence [.putCounters (.ofKind .plusOnePlusOne) .source, .scry (.fixed 1)] }
    | .casting .ironFistTap =>
      { resolution := .grant .ironFistTap .source }
    | .casting .targetsGainFlying =>
      { resolution := .grant (.keywords #[Keyword.flying]) .spellTargets }
    | .casting .copyIfArtifactOrLand =>
      { resolution := .sequence [
          .putCounters (.ofKind .plusOnePlusOne 2) .source, .copyCause] }
    | .casting .tapCreatureOrLand =>
      { targeting := .of (.ofDomain (.object .battlefield (.any #[.hasType .creature, .hasType .land]))),
        resolution := .tap .target }
    | .resource .discardExilePlay =>
      { resolution := .may (.exile .discarded .playUntilNextTurn) (.sequence []) .ifYouDo }
    | .resource .drawIfAnotherHeroDamage =>
      { targeting := .of .opponent,
        resolution := .«if» (.atLeast (.count (.othersOfSubtype .hero)) (.fixed 1)) (.dealDamage (.fixed 1) (.player (.target .opponent))) }
    | .resource .secondDrawBecome66 =>
      { resolution := .sequence [
          .setBasePT (.fixed 6) (.fixed 6) .source, .grant (.keywords #[Keyword.trample]) .source] }
    | .resource .secondDrawPlusOneTarget =>
      { targeting := .of .creature,
        resolution := .putCounters (.ofKind .plusOnePlusOne) .permanent }
    | .resource .secondDrawDrain =>
      { resolution := .sequence [.loseLife (.fixed 1) .eachOpponent, .gainLife (.fixed 1)] }
    | .resource .gainLifePlusOnes =>
      { targeting := .of .creatureYouControl,
        allowsZeroTargets := true,
        resolution := .putCounters (.ofKind .plusOnePlusOne) .eachUpToLastKnown }
    | .resource .plusOneCreateInsectOnce =>
      { resolution := .createTokens .insect11green (.fixed 1) false }
    | .resource .plusOneOnThisOnce =>
      { resolution := .putCounters (.ofKind .plusOnePlusOne) .source }
    | .resource .plusOneOnHeroesCreateWall =>
      { resolution := .may (.createTokens .wall04defender (.fixed 1) false) (.sequence []) .ifYouDo }
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
  | .chapter _ _ => TriggerPattern.putCountersOnSelf .lore
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
  | .chapter n _ => .counterThreshold .lore (if n == 0 then #[] else #[n])
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
  .createTokens .squirrel11green (.fixed 1) false
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
#guard TriggeredAbility.TriggerResolution.ofPermanent .loseIndestructible == .lose .indestructible
#guard TriggeredAbility.TriggerResolution.ofSource .loseIndestructible == .lose .indestructible .source
#guard TriggeredAbility.TriggerResolution.ofEnchanted .loseIndestructible == .lose .indestructible .enchanted
#guard TriggeredAbility.TriggerResolution.ofTargetWhileSource .loseIndestructible ==
  .lose .indestructible (.target .whileSource)
#guard TriggeredAbility.TriggerResolution.ofPermanent .cantBeBlocked == .cant .beBlocked
#guard TriggeredAbility.TriggerResolution.ofPermanent .indestructibleCounter ==
  .putCounters (.ofKind .indestructible) .permanent
#guard TriggeredAbility.TriggerResolution.ofPermanent .doubleStrikeCounter ==
  .putCounters (.ofKind .doubleStrike) .permanent
#guard TriggeredAbility.TriggerResolution.ofPermanent .burdenCounter ==
  .putCounters (.ofKind .burden) .permanent
#guard TriggeredAbility.TriggerResolution.ofPermanent .becomeArtifactIndestructible ==
  .sequence [.becomeArtifact, .grant (.keywords #[Keyword.indestructible]) .target]
#guard TriggeredAbility.TriggerResolution.ofPermanent .becomePrepared == .becomePrepared
#guard TriggeredAbility.TriggerResolution.ofPermanent (.setBasePT 2 2) ==
  .setBasePT (.fixed 2) (.fixed 2)
#guard TriggeredAbility.TriggerResolution.ofPermanent .tapAndStun ==
  .sequence [.tap .target, .putCounters (.ofKind .stun) .permanent]
#guard TriggeredAbility.TriggerResolution.ofPermanent .putOnTopOfLibrary == .putOnLibrary .top
#guard TriggeredAbility.TriggerResolution.ofPermanent .putOnBottomOfLibrary == .putOnLibrary .bottom
#guard TriggeredAbility.TriggerResolution.ofSource .putOnTopOfLibrary == .putOnLibrary .top .source
#guard TriggeredAbility.TriggerResolution.ofSource .putOnBottomOfLibrary == .putOnLibrary .bottom .source
#guard TriggeredAbility.TriggerResolution.ofEnchanted .putOnTopOfLibrary == .putOnLibrary .top .enchanted
#guard TriggeredAbility.TriggerResolution.ofEnchanted .putOnBottomOfLibrary == .putOnLibrary .bottom .enchanted
#guard TriggeredAbility.TriggerResolution.ofTargetWhileSource .putOnTopOfLibrary ==
  .putOnLibrary .top (.target .whileSource)
#guard TriggeredAbility.TriggerResolution.ofTargetWhileSource .putOnBottomOfLibrary ==
  .putOnLibrary .bottom (.target .whileSource)
#guard TriggeredAbility.TriggerResolution.ofPermanent .exile == .exile .target .forLater
#guard TriggeredAbility.TriggerResolution.ofSource .exile == .exile .source .forLater
#guard TriggeredAbility.TriggerResolution.ofEnchanted .exile == .exile .enchanted .forLater
#guard TriggeredAbility.TriggerResolution.ofTargetWhileSource .exile ==
  .exile (.target .whileSource) .forLater
#guard TriggeredAbility.TriggerResolution.ofPermanent .doublePowerAndToughness ==
  .pump .double .double .target
#guard TriggeredAbility.TriggerResolution.ofPermanent (.pumpAndTrample 2 0) ==
  .sequence [.pump (.fixed 2) (.fixed 0) .target, .grant (.keywords #[Keyword.trample]) .target]
#guard TriggeredAbility.TriggerResolution.ofSource (.plusOne 1) ==
  .putCounters (.ofKind .plusOnePlusOne) .source
#guard TriggeredAbility.TriggerResolution.ofSource (.pump 1 1) ==
  .pump (.fixed 1) (.fixed 1) .source
#guard TriggeredAbility.TriggerResolution.ofSource .tap == .tap .source
#guard TriggeredAbility.TriggerResolution.ofEnchanted .tap == .tap .enchantedWhileSource
#guard TriggeredAbility.TriggerResolution.ofEnchanted (.grantKeywords #[Keyword.firstStrike]) ==
  .grant (.keywords #[Keyword.firstStrike]) .enchanted
#guard TriggeredAbility.TriggerResolution.ofTargetWhileSource .untap ==
  .untap (.target .whileSource)
#guard TriggeredAbility.TriggerResolution.ofTargetWhileSource
    (.grantKeywords #[Keyword.indestructible]) ==
  .grant (.keywords #[Keyword.indestructible]) (.target .whileSource)
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
  .createTokens .insect11green (.fixed 1) false
#guard (SharedTrigger.toEffect (.resource .plusOneOnThisOnce)).resolution ==
  .putCounters (.ofKind .plusOnePlusOne) .source
#guard (SharedTrigger.toEffect (.resource .plusOneOnHeroesCreateWall)).resolution ==
  .may (.createTokens .wall04defender (.fixed 1) false) (.sequence []) .ifYouDo

end Mtg.Engine
