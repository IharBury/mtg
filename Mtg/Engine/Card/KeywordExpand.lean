import Mtg.Engine.Card.ActivatedAbility
import Mtg.Engine.Card.StaticAbility
import Mtg.Engine.Card.TriggeredAbility

/-!
# Keyword Expansion (CR 702.1)

Pure projection `KeywordAbility.expand : KeywordAbility → ExpandedKeyword`
translating every CR 702 keyword ability directly into the unified Phase-8
`ActivatedAbility`, `TriggeredAbility`, `StaticAbility`, `SpecialActionSpec`,
`AdditionalCostSpec`, `AlternativeCostSpec`, and `Instruction` AST anchored to
the 6 November 2026 Comprehensive Rules:

- Intrinsic `ActivatedAbility`s: Equip (CR 702.6a), Cycling / Typecycling
  (CR 702.29a,e), Crew (CR 702.122a).
- Special actions (`SpecialActionSpec`, CR 116.2b): Morph's turn-face-up
  special action (CR 702.37e — kept distinct from `ActivatedAbility` so
  Split second CR 702.61b does not forbid it).
- Intrinsic `TriggeredAbility`s: Prowess (CR 702.108a), Exalted (CR 702.83a),
  Decayed's attack trigger scheduling an end-of-combat delayed sacrifice
  (CR 702.147a / 603.7 / 511.2), Ward (CR 702.21a), Cascade (CR 702.85a),
  Myriad (CR 702.116a), Undying (CR 702.93a), Extort (CR 702.101a),
  Impending's intervening-if end-step trigger (CR 702.176a / 603.4), and
  Gift's intervening-if permanent ETB trigger (CR 702.174b / 603.4).
- Intrinsic `StaticAbility`s: Changeling CDA (CR 702.73a), Decayed `"can't
  block"` (CR 702.147a), Affinity (CR 702.41a), Ascend (CR 702.131b), Storied,
  Flashback's leave-the-stack exile replacement (CR 702.34a), Impending's ETB
  time counters and Layer-4 noncreature static (CR 702.176a), and Sneak's ETB
  tapped-and-attacking same-defender modification (CR 702.190b / 506.2 / 506.3a).
- Alternative and additional casting costs (`AlternativeCostSpec` /
  `AdditionalCostSpec`): Morph's `{3}` face-down alternative cast (CR 702.37a/c),
  Flashback (CR 702.34a), Impending (CR 702.176a), Sneak (CR 702.190a), Kicker
  (CR 702.33a), Teamwork (CR 702.194a), and Gift (CR 702.174a).
- Prepended instant/sorcery spell `Instruction`s: Gift (CR 702.174b/j),
  Ascend (CR 702.131a), and Storied.
-/

namespace Mtg.Engine

/-- A keyword-generated special action (CR 116.2b). Kept distinct from
`ActivatedAbility` so Split second (CR 702.61b) never forbids it. -/
inductive SpecialActionSpec where
  /-- Morph turn-face-up special action (CR 702.37e / 116.2b): reveal the
  printed morph cost, pay `cost`, and turn the face-down permanent face up. -/
  | turnFaceUp (cost : CostSpec)
deriving Repr, Inhabited, BEq

instance : HasTextChange SpecialActionSpec where
  applyTextChanges tcs
    | .turnFaceUp cost => .turnFaceUp (HasTextChange.applyTextChanges tcs cost)

/-- Result of expanding one or more `KeywordAbility` values directly into unified
Phase-8 CR 113.3 abilities, special actions, costs, and prepended spell
`Instruction`s. -/
structure ExpandedKeyword where
  activatedAbilities : Array ActivatedAbility := #[]
  triggeredAbilities : Array TriggeredAbility := #[]
  staticAbilities : Array StaticAbility := #[]
  specialActions : Array SpecialActionSpec := #[]
  additionalCosts : Array AdditionalCostSpec := #[]
  alternativeCosts : Array AlternativeCostSpec := #[]
  spellInstructions : Array Instruction := #[]
deriving Repr, Inhabited, BEq

namespace ExpandedKeyword

def empty : ExpandedKeyword := {}

def merge (a b : ExpandedKeyword) : ExpandedKeyword :=
  { activatedAbilities := a.activatedAbilities ++ b.activatedAbilities
    triggeredAbilities := a.triggeredAbilities ++ b.triggeredAbilities
    staticAbilities := a.staticAbilities ++ b.staticAbilities
    specialActions := a.specialActions ++ b.specialActions
    additionalCosts := a.additionalCosts ++ b.additionalCosts
    alternativeCosts := a.alternativeCosts ++ b.alternativeCosts
    spellInstructions := a.spellInstructions ++ b.spellInstructions }

def mergeAll (xs : Array ExpandedKeyword) : ExpandedKeyword :=
  xs.foldl merge empty

/-- True when this expansion introduces a `"can't block"` restriction (Decayed CR 702.147a). -/
def hasCantBlock (e : ExpandedKeyword) : Bool :=
  e.staticAbilities.any fun ab =>
    ab.anyRule fun _ r =>
      match r with
      | .combat (.cantBlock .self none) => true
      | _ => false

/-- True when this expansion introduces the Changeling Layer-4 CDA (CR 702.73a). -/
def hasChangelingCda (e : ExpandedKeyword) : Bool :=
  e.staticAbilities.any fun
    | .characteristicDefining .allCreatureTypes => true
    | _ => false

end ExpandedKeyword

namespace KeywordAbility

/-- CR 702.131a–b: You control ten or more permanents. -/
def condAscendTenPermanents : Condition :=
  .cmp .ge (.aggregate .count .one (.inZones .battlefield (.controlledBy .you))) (.const 10)

/-- HOB Storied: You control three or more storied (historic) permanents. -/
def condStoriedThreePermanents : Condition :=
  .cmp .ge
    (.aggregate .count .one (.inZones .battlefield (.all #[.controlledBy .you, ObjectPred.storied])))
    (.const 3)

/-- CR 702.176a: This permanent's impending cost was paid and it has a time counter on it. -/
def condImpendingActive : Condition :=
  .all #[.castPred (.impendingPaid .this), .cmp .ge (.counterCount (some .time) .this) (.const 1)]

/-- Pure Phase-8 `Instruction` granting the promised gift to the chosen opponent
(CR 702.174d–i). -/
def giftGrantInstruction (kind : GiftKind) : Instruction :=
  let opp : PlayerExpr := .triggerPlayer .giftOpponent
  match kind with
  | .food => .create (.tokens opp (.const 1) TokenSpec.food)
  | .card => .player (.drawCards opp (.const 1))
  | .tappedFish => .create (.tokens opp (.const 1) TokenSpec.fish11blue { tapped := true })
  | .extraTurn => .turn (.extraTurn opp none)
  | .treasure => .create (.tokens opp (.const 1) TokenSpec.treasure)
  | .octopus => .create (.tokens opp (.const 1) TokenSpec.octopus88blue)

/-- Construct the CR 702.6a sorcery-speed Equip activated ability. -/
def equipActivatedAbility (filter : ObjectPred) (cost : CostSpec) : ActivatedAbility :=
  let isDefault :=
    filter == .anyObject || filter == .hasType .creature ||
      filter == .all #[.hasType .creature, .controlledBy .you]
  let subtype? : Option CardSubtype :=
    match filter with
    | .hasSubtype (.literal sub) => some sub
    | .all #[.hasType .creature, .hasSubtype (.literal sub), .controlledBy .you] => some sub
    | _ => none
  let isWorthy :=
    filter == ObjectPred.worthy ||
      match filter with
      | .all ps => ps.contains ObjectPred.worthy
      | _ => false
  let (extraPred?, spec) : Option ObjectPred × TargetSpec :=
    if isDefault then
      (none, .creatureYouControl)
    else if isWorthy then
      (some ObjectPred.worthy, Effect.equipEffect none true |>.targets)
    else
      match subtype? with
      | some sub =>
        (some (.hasSubtype (.literal sub)), (Effect.equipEffect (some sub) false).targets)
      | none =>
        let basePred : ObjectPred :=
          match filter with
          | .all ps =>
            let hasC := ps.contains (.hasType .creature)
            let hasY := ps.contains (.controlledBy .you)
            let ps := if hasC then ps else #[.hasType .creature] ++ ps
            let ps := if hasY then ps else ps.push (.controlledBy .you)
            .all ps
          | other => .all #[.hasType .creature, other, .controlledBy .you]
        (some filter, .ofDomain (.object .battlefield basePred))
  { cost
    effect := { targets := spec
                body := .permanent (.attach .this (.target 0)) }
    timing := .sorcery
    tag? := some (.equip extraPred?) }

/-- Construct the CR 702.29a / 702.29e hand-zone Cycling / Typecycling activated ability. -/
def cyclingActivatedAbility (typeFilter? : Option ObjectPred) (cost : CostSpec) : ActivatedAbility :=
  let fullCost := cost.append (CostSpec.ofItem (.discard (.exact 1) .self))
  let (eff, subLabel?) : Effect × Option String :=
    match typeFilter? with
    | none =>
      ({ body := Instruction.drawFixed 1 }, none)
    | some (.hasSubtype (.literal sub)) =>
      ({ body := .player (.searchLibrary {
            zones := .libraryOf .you
            filter := .hasSubtype (.literal sub)
            count := .upTo (.const 1)
            dest := .hand .controller
            reveal := true
            shuffle := true }) },
       some sub.englishName)
    | some (.all #[.hasSupertype .basic, .hasType .land]) =>
      ({ body := .player (.searchLibrary {
            zones := .libraryOf .you
            filter := .all #[.hasSupertype .basic, .hasType .land]
            count := .upTo (.const 1)
            dest := .hand .controller
            reveal := true
            shuffle := true }) },
       some "Basic land")
    | some (.hasSupertype sup) =>
      ({ body := .player (.searchLibrary {
            zones := .libraryOf .you
            filter := .hasSupertype sup
            count := .upTo (.const 1)
            dest := .hand .controller
            reveal := true
            shuffle := true }) },
       some sup.englishName)
    | some (.hasType ty) =>
      ({ body := .player (.searchLibrary {
            zones := .libraryOf .you
            filter := .hasType ty
            count := .upTo (.const 1)
            dest := .hand .controller
            reveal := true
            shuffle := true }) },
       some ty.englishName)
    | some pred =>
      ({ body := .player (.searchLibrary {
            zones := .libraryOf .you
            filter := pred
            count := .upTo (.const 1)
            dest := .hand .controller
            reveal := true
            shuffle := true }) },
       none)
  { cost := fullCost
    effect := eff
    activeZones := #[.hand]
    tag? := some (.cycling subLabel?) }

/-- Pure CR 702.1 expansion of one `KeywordAbility` into its exact intrinsic
unified activated abilities, triggered abilities, static/replacement abilities,
special actions, additional/alternative casting costs, and prepended spell
`Instruction`s. -/
def expand : KeywordAbility → ExpandedKeyword
  -- CR 702.147a: Decayed = static "can't block" + attack trigger scheduling
  -- end-of-combat delayed sacrifice (CR 603.7 / 511.2).
  | .simple .decayed =>
    { staticAbilities := #[.ruleModifying none (.combat (.cantBlock .self none))]
      triggeredAbilities := #[{
        word := .when
        pattern := .attacks (.sameAs .this)
        effect := {
          body := .installEffect (.createDelayedTrigger {
            pattern := .stepBegins .endOfCombat (.player .any)
            duration := .untilEndOfCombat
            oneShot := true
            effect := { body := Instruction.sacrifice .this } }) } }] }
  -- CR 702.83a: Exalted
  | .simple .exalted =>
    { triggeredAbilities := #[{
        word := .whenever
        pattern := .attacks (.all #[.hasType .creature, .controlledBy .you]) .any true
        effect := {
          body := Instruction.pumpFixed .triggerSubject 1 1 } }] }
  -- CR 702.73a: Changeling Layer-4 CDA
  | .simple .changeling =>
    { staticAbilities := #[.characteristicDefining .allCreatureTypes] }
  -- CR 702.131a–b: Ascend (permanent static + instant/sorcery spell instruction)
  | .simple .ascend =>
    { staticAbilities := #[
        .ruleModifying (some condAscendTenPermanents) (.player (.gainDesignation .you .citysBlessing))]
      spellInstructions := #[
        .player (.setPlayerDesignation .you .citysBlessing (some condAscendTenPermanents))] }
  -- HOB Storied (permanent static + instant/sorcery spell instruction)
  | .simple .storied =>
    { staticAbilities := #[
        .ruleModifying (some condStoriedThreePermanents) (.player (.gainDesignation .you .enduringStory))]
      spellInstructions := #[
        .player (.setPlayerDesignation .you .enduringStory (some condStoriedThreePermanents))] }
  -- CR 702.108a: Prowess
  | .simple .prowess =>
    { triggeredAbilities := #[{
        word := .whenever
        pattern := .castSpell .you (.not (.hasType .creature))
        effect := {
          body := Instruction.pumpFixed .this 1 1 } }] }
  -- CR 702.85a: Cascade
  | .simple .cascade =>
    { triggeredAbilities := #[TriggeredAbility.onCastCascade] }
  -- CR 702.116a: Myriad
  | .simple .myriad =>
    { triggeredAbilities := #[{
        word := .whenever
        pattern := .attacks (.sameAs .this)
        effect := {
          body := .forEach (.eachPlayer { relation := .opponent, pred := .not .isDefendingPlayer }) ⟨0⟩
            (Instruction.may .you none
              (.create (.tokens .you (.const 1) (.copyOf .this #[])
                { tapped := true, attacking := true, delayedAction? := some .exileAtEndOfCombat }))) } }] }
  -- CR 702.93a: Undying (CR 603.4 intervening-if: no +1/+1 counters)
  | .simple .undying =>
    { triggeredAbilities := #[{
        word := .when
        pattern := .zoneChange (.sameAs .this) .battlefield .graveyard
        interveningIf? := some (.cmp .eq (.counterCount (some .plusOnePlusOne) .this) (.const 0))
        effect := {
          body := .moveZone .this (.battlefield .owner) .put
            { enterCounters := #[(.plusOnePlusOne, .const 1)] } } }] }
  -- CR 702.101a: Extort
  | .simple .extort =>
    { triggeredAbilities := #[{
        word := .whenever
        pattern := .castSpell .you .anyObject
        effect := {
          body := Instruction.may .you
            (some (CostSpec.ofMana { symbols := #[.hybrid .white .black] }))
            (.bind ⟨0⟩ (.life (.lose .opponents (.const 1)))
              (.life (.gain .you (.stepMetric .lifeChanged ⟨0⟩)))) } }] }
  -- CR 702.21a: Ward [cost]
  | .ward cost =>
    { triggeredAbilities := #[TriggeredAbility.onWard cost] }
  -- CR 702.41a: Affinity for [filter]
  | .affinity forWhat =>
    { staticAbilities := #[
        .costModifier none .thisSpell
          (.reduceGeneric (.aggregate .count .one (.inZones forWhat.zones forWhat.pred)))] }
  -- CR 702.6a: Equip [filter] [cost] (sorcery-speed activated ability)
  | .equip filter cost =>
    { activatedAbilities := #[equipActivatedAbility filter cost] }
  -- CR 702.29a / 702.29e: Cycling / Typecycling [cost] (hand-zone activated ability)
  | .cycling typeFilter? cost =>
    { activatedAbilities := #[cyclingActivatedAbility typeFilter? cost] }
  -- CR 702.33a: Kicker [cost] (optional additional cost)
  | .kicker cost =>
    { additionalCosts := #[AdditionalCostSpec.opt cost (some .kicker)] }
  -- CR 702.174a–b,j / 603.4: Gift [kind]
  | .gift kind =>
    { additionalCosts := #[AdditionalCostSpec.opt {} (some .gift)]
      triggeredAbilities := #[{
        word := .when
        pattern := TriggerPattern.thisEnters
        interveningIf? := some (.castPred (.giftPromised .this))
        effect := {
          body := giftGrantInstruction kind } }]
      spellInstructions := #[
        Instruction.ifThen (.castPred (.giftPromised .this)) (giftGrantInstruction kind)] }
  -- CR 702.34a: Flashback [cost] (graveyard alternative cost + leave-stack exile replacement)
  | .flashback cost =>
    { alternativeCosts := #[{
        cost
        fromZones := #[.graveyard]
        keywordTag? := some .flashback }]
      staticAbilities := #[
        .replacement (some (.castPred (.castFrom .graveyard .this))) .exileOnLeaveStack] }
  -- CR 702.37a/c/e / 116.2b: Morph [cost]
  | .morph cost =>
    { alternativeCosts := #[{
        cost := CostSpec.ofGeneric 3
        fromZones := #[.hand]
        keywordTag? := some .morph
        faceDown := true }]
      specialActions := #[.turnFaceUp cost] }
  -- CR 702.176a / 603.4: Impending N—[cost]
  | .impending counters cost =>
    { alternativeCosts := #[{
        cost
        fromZones := #[.hand]
        keywordTag? := some .impending }]
      staticAbilities := #[
        .replacement (some (.castPred (.impendingPaid .this)))
          (.entersWithCounters .self .time (.const counters) false),
        .continuous (some condImpendingActive) StaticAbility.scopeSelf
          (.modifyTypes { mode := .add, removeTypes := #[.creature] })]
      triggeredAbilities := #[TriggeredAbility.impendingEndStep] }
  -- CR 702.190a–b / 506.2 / 506.3a: Sneak [cost]
  | .sneak cost =>
    { alternativeCosts := #[{
        cost := CostSpec.sneakFullCost cost
        fromZones := #[.hand]
        condition? := some (.duringStep .declareBlockers)
        keywordTag? := some .sneak }]
      staticAbilities := #[
        .replacement (some (.castPred (.sneakPaid .this))) .entersTappedAndAttackingSameDefender] }
  -- CR 702.122a: Crew N (activated ability)
  | .crew power =>
    { activatedAbilities := #[ActivatedAbility.crewAbility power] }
  -- CR 702.194a: Teamwork N (optional additional cost)
  | .teamwork count =>
    { additionalCosts := #[AdditionalCostSpec.opt (CostSpec.teamworkCost count) (some .teamwork)] }
  -- Evergreen combat / evasion / targeting / cast-timing / mana-assist keywords
  -- are evaluated directly from `CardDef.keywords` / `effectiveKeywords`.
  | _ => {}

/-- Pure CR 702.1 expansion of an entire keyword array, preserving multiplicity. -/
def expandAll (ks : Array KeywordAbility) : ExpandedKeyword :=
  ExpandedKeyword.mergeAll (ks.map expand)

end KeywordAbility

-- Compile-time CR 702.1 expansion guards.
#guard (KeywordAbility.expand (.morph (CostSpec.ofMana { symbols := #[.generic 2, .colored .blue] }))).alternativeCosts[0]!.cost ==
  CostSpec.ofGeneric 3
#guard (KeywordAbility.expand (.morph (CostSpec.ofMana { symbols := #[.generic 2, .colored .blue] }))).alternativeCosts[0]!.faceDown == true
#guard (KeywordAbility.expand (.morph (CostSpec.ofMana { symbols := #[.generic 2, .colored .blue] }))).specialActions ==
  #[.turnFaceUp (CostSpec.ofMana { symbols := #[.generic 2, .colored .blue] })]
#guard (KeywordAbility.expand (.morph (CostSpec.ofGeneric 2))).activatedAbilities.isEmpty
#guard (KeywordAbility.expand Keyword.decayed).hasCantBlock == true
#guard (KeywordAbility.expand Keyword.decayed).triggeredAbilities.size == 1
#guard (KeywordAbility.expand Keyword.changeling).hasChangelingCda == true
#guard (KeywordAbility.expand (.impending 4 (CostSpec.ofGeneric 2))).triggeredAbilities[0]!.interveningIf?.isSome
#guard (KeywordAbility.expand (.impending 4 (CostSpec.ofGeneric 2))).staticAbilities.size == 2
#guard (KeywordAbility.expand (.gift .treasure)).triggeredAbilities[0]!.interveningIf? ==
  some (.castPred (.giftPromised .this))
#guard (KeywordAbility.expand (.gift .treasure)).spellInstructions.size == 1
#guard (KeywordAbility.expand (.crew 3)).activatedAbilities.size == 1
#guard (KeywordAbility.expand (.flashback (CostSpec.ofGeneric 2))).staticAbilities ==
  #[.replacement (some (.castPred (.castFrom .graveyard .this))) .exileOnLeaveStack]
#guard (KeywordAbility.expand (.sneak (CostSpec.ofGeneric 1))).alternativeCosts[0]!.condition? ==
  some (.duringStep .declareBlockers)
#guard (KeywordAbility.expandAll #[.ward (CostSpec.ofGeneric 2), .ward CostSpec.discardCard]).triggeredAbilities.size == 2

end Mtg.Engine
