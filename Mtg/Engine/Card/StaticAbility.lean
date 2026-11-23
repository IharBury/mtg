import Mtg.Engine.Card.ActivatedAbility
import Mtg.Engine.Card.TriggeredAbility
import Mtg.Engine.Card.Targeting
import Mtg.Engine.Card.Token

/-!
# Stratified Static Abilities (CR 113.3d / 303.4a / 601.2f / 602.2b / 604 / 611.3 / 613 / 614–616)

CR-stratified 6-constructor `StaticAbility` AST replacing the retired flat
static-ability and raw-printed representations:

1. `characteristicDefining (cda : CdaSpec)` — CR 604.3 (all zones: Layer 4/5/7a CDAs)
2. `continuous (cond? : Option Condition) (scope : ObjectFilter) (mod : ContinuousModification)`
   — CR 611.3 / 613 Layers 4–7d
3. `ruleModifying (cond? : Option Condition) (rule : RuleModification)`
   — CR 604 / 101.2 player, play, combat, trigger, and game rules
4. `costModifier (cond? : Option Condition) (appliesTo : CostTargetSpec) (mod : CostModification)`
   — CR 601.2f / 602.2b spell and ability cost modifiers
5. `replacement (cond? : Option Condition) (spec : StaticReplacementSpec)`
   — CR 614 / 615 replacement and prevention effects
6. `enchantRestriction (filter : TargetSlot)` — CR 303.4a Aura enchant restriction

Every `inductive` in this module stays at ≤ 18 constructors (`< 8%` of the
Lean 4 C runtime `LeanMaxCtorTag = 243` ceiling), carries zero card- or set-named
constructors, implements functorial Layer 3 `HasTextChange`, and renders
canonical Oracle text through `ToOracle` / `toNotation`.
-/

namespace Mtg.Engine

/-! ### 1. Continuous Modification Helpers -/

namespace ContinuousModification

/-- Flatten nested `.all` modifications in printed order. -/
partial def flatten : ContinuousModification → Array ContinuousModification
  | .all ms => ms.foldl (fun acc m => acc ++ flatten m) #[]
  | m => #[m]

/-- Combine an array of modifications into a canonical single `ContinuousModification`. -/
def ofArray (ms : Array ContinuousModification) : ContinuousModification :=
  let flat := ms.foldl (fun acc m => acc ++ flatten m) #[]
  match flat.toList with
  | [m] => m
  | _ => .all flat

end ContinuousModification

/-! ### 6. Canonical Scope & Condition Builders -/

namespace StaticAbility

/-- Canonical battlefield filter matching the source permanent itself. -/
def scopeSelf : ObjectFilter :=
  { zones := .battlefield, pred := .sameAs .this }

/-- Canonical battlefield filter matching the creature equipped by this Equipment. -/
def scopeEquippedCreature : ObjectFilter :=
  { zones := .battlefield
    pred := .all #[
      .hasType .creature,
      .hasAttachment { zones := .battlefield
                       pred := .all #[.sameAs .this, .hasSubtype (.literal .equipment)] }
    ] }

/-- Canonical battlefield filter matching the creature enchanted by this Aura. -/
def scopeEnchantedCreature : ObjectFilter :=
  { zones := .battlefield
    pred := .all #[
      .hasType .creature,
      .hasAttachment { zones := .battlefield
                       pred := .all #[.sameAs .this, .hasSubtype (.literal .aura)] }
    ] }

/-- Canonical battlefield filter matching the permanent enchanted by this Aura. -/
def scopeEnchantedPermanent : ObjectFilter :=
  { zones := .battlefield
    pred := .hasAttachment { zones := .battlefield
                             pred := .all #[.sameAs .this, .hasSubtype (.literal .aura)] } }

/-- Canonical battlefield filter for creatures you control. -/
def scopeCreaturesYouControl : ObjectFilter :=
  { zones := .battlefield, pred := .all #[.hasType .creature, .controlledBy .you] }

/-- Canonical battlefield filter for other creatures you control. -/
def scopeOtherCreaturesYouControl : ObjectFilter :=
  { zones := .battlefield
    pred := .all #[.otherThan .this, .hasType .creature, .controlledBy .you] }

/-- Canonical battlefield filter for creatures your opponents control. -/
def scopeOpponentsCreatures : ObjectFilter :=
  { zones := .battlefield, pred := .all #[.hasType .creature, .controlledBy .opponent] }

/-- Canonical battlefield filter for lands you control. -/
def scopeLandsYouControl : ObjectFilter :=
  { zones := .battlefield, pred := .all #[.hasType .land, .controlledBy .you] }

/-- Canonical battlefield filter for planeswalkers you control. -/
def scopePlaneswalkersYouControl : ObjectFilter :=
  { zones := .battlefield, pred := .all #[.hasType .planeswalker, .controlledBy .you] }

/-- Canonical battlefield filter for permanents you control. -/
def scopePermanentsYouControl : ObjectFilter :=
  { zones := .battlefield, pred := .controlledBy .you }

/-- Canonical battlefield filter for permanents an opponent controls. -/
def scopeOpponentsPermanents : ObjectFilter :=
  { zones := .battlefield, pred := .controlledBy .opponent }

/-- Canonical battlefield filter for creatures you control of subtype `sub`. -/
def scopeCreaturesOfSubtypeYouControl (sub : CardSubtype) : ObjectFilter :=
  { zones := .battlefield
    pred := .all #[.hasType .creature, .hasSubtype (.literal sub), .controlledBy .you] }

/-- Canonical battlefield filter for permanents you control of subtype `sub`. -/
def scopeSubtypeYouControl (sub : CardSubtype) : ObjectFilter :=
  { zones := .battlefield, pred := .all #[.hasSubtype (.literal sub), .controlledBy .you] }

/-- Canonical battlefield filter for other permanents you control of subtype `sub`. -/
def scopeOtherSubtypeYouControl (sub : CardSubtype) : ObjectFilter :=
  { zones := .battlefield
    pred := .all #[.otherThan .this, .hasSubtype (.literal sub), .controlledBy .you] }

/-- Canonical `ObjectPred` matching any subtype in `subs`. -/
def anySubtypePred (subs : Array CardSubtype) : ObjectPred :=
  match subs.toList with
  | [s] => .hasSubtype (.literal s)
  | _ => .any (subs.map fun s => .hasSubtype (.literal s))

/-- Canonical battlefield filter for other creatures you control of any subtype in `subs`.
Empty `subs` yields `scopeOtherCreaturesYouControl`. -/
def scopeOtherCreaturesOfSubtypesYouControl (subs : Array CardSubtype) : ObjectFilter :=
  if subs.isEmpty then scopeOtherCreaturesYouControl
  else
    { zones := .battlefield
      pred := .all #[.otherThan .this, .hasType .creature, anySubtypePred subs, .controlledBy .you] }

/-- Canonical battlefield filter for other permanents you control of any subtype in `subs`. -/
def scopeOtherSubtypesYouControl (subs : Array CardSubtype) : ObjectFilter :=
  { zones := .battlefield
    pred := .all #[.otherThan .this, anySubtypePred subs, .controlledBy .you] }

/-- Canonical stack filter for instant and sorcery spells you control. -/
def scopeInstantSorcerySpellsYouControl : ObjectFilter :=
  { zones := .stack
    pred := .all #[.any #[.hasType .instant, .hasType .sorcery], .isKind .spell, .controlledBy .you] }

/-- Canonical stack filter for noncreature spells you control. -/
def scopeNoncreatureSpellsYouControl : ObjectFilter :=
  { zones := .stack
    pred := .all #[.not (.hasType .creature), .isKind .spell, .controlledBy .you] }

/-- Canonical recipient filter for an opponent or a permanent an opponent controls. -/
def recipientOppOrOppPermanent : RecipientFilter :=
  .playerOrObject .opponent scopeOpponentsPermanents

/-- Scale `v` by integer factor `k` (`k = 1` keeps `v` bare). -/
def scaledValue (k : Int) (v : ValueExpr) : ValueExpr :=
  if k == 1 then v else .binary .mul (.const k) v

/-- Count of objects matching `pred` on the battlefield. -/
def countBf (pred : ObjectPred) : ValueExpr :=
  .aggregate .count .one (.inZones .battlefield pred)

/-- Condition: you have an enduring story. -/
def condEnduringStory : Condition :=
  .playerPred .you (.hasDesignation .enduringStory)

/-- Condition: there are `n` or more cards in your graveyard (e.g. Threshold with `n = 7`). -/
def condGraveyardAtLeast (n : Nat) : Condition :=
  .cmp .ge (.playerMetric .graveyardSize .you) (.const n)

/-- Condition: there are `n` or more other cards in your graveyard. -/
def condOtherCardsInGraveyardAtLeast (n : Nat) : Condition :=
  .cmp .ge (.aggregate .count .one (.inZones .yourGraveyard (.otherThan .this))) (.const n)

/-- Condition: there are `n` or more creature cards in your graveyard. -/
def condGyCreatureCardsAtLeast (n : Nat) : Condition :=
  .cmp .ge (.aggregate .count .one (.inZones .yourGraveyard (.all #[.isCard, .hasType .creature]))) (.const n)

/-- Condition: you control a permanent with subtype `sub`. -/
def condControlSubtype (sub : CardSubtype) : Condition :=
  .exists (.inZones .battlefield (.all #[.hasSubtype (.literal sub), .controlledBy .you]))

/-- Condition: you control another permanent with subtype `sub`. -/
def condControlOtherSubtype (sub : CardSubtype) : Condition :=
  .exists (.inZones .battlefield (.all #[.otherThan .this, .hasSubtype (.literal sub), .controlledBy .you]))

/-- Condition: you control `n` or more other permanents with subtype `sub`. -/
def condControlNOtherSubtype (n : Nat) (sub : CardSubtype) : Condition :=
  .cmp .ge (countBf (.all #[.otherThan .this, .hasSubtype (.literal sub), .controlledBy .you])) (.const n)

/-- Condition: you control a permanent with any subtype in `subs`. -/
def condControlAnySubtype (subs : Array CardSubtype) : Condition :=
  .exists (.inZones .battlefield (.all #[anySubtypePred subs, .controlledBy .you]))

/-- Condition: you control a land with any subtype in `subs`. -/
def condControlLandAnySubtype (subs : Array CardSubtype) : Condition :=
  .exists (.inZones .battlefield (.all #[.hasType .land, anySubtypePred subs, .controlledBy .you]))

/-- Condition: you control a legendary creature. -/
def condControlLegendaryCreature : Condition :=
  .exists (.inZones .battlefield (.all #[.hasSupertype .legendary, .hasType .creature, .controlledBy .you]))

/-- Condition: you control a planeswalker. -/
def condControlPlaneswalker : Condition :=
  .exists (.inZones .battlefield (.all #[.hasType .planeswalker, .controlledBy .you]))

/-- Condition: you control a commander. -/
def condControlCommander : Condition :=
  .exists (.inZones .battlefield (.all #[.isCommander, .controlledBy .you]))

/-- Condition: you control `n` or more other lands. -/
def condControlNOtherLands (n : Nat) : Condition :=
  .cmp .ge (countBf (.all #[.otherThan .this, .hasType .land, .controlledBy .you])) (.const n)

/-- Condition: you control `n` or more basic lands. -/
def condControlNBasicLands (n : Nat) : Condition :=
  .cmp .ge (countBf (.all #[.hasSupertype .basic, .hasType .land, .controlledBy .you])) (.const n)

/-- Condition: your opponents control `n` or more lands. -/
def condOpponentsControlNLands (n : Nat) : Condition :=
  .cmp .ge (countBf (.all #[.hasType .land, .controlledBy .opponent])) (.const n)

/-- Condition: an opponent has `n` or more poison counters (Corrupted: `n = 3`). -/
def condOpponentPoisonAtLeast (n : Nat) : Condition :=
  .playerPred (.matching .opponent (.metric .poisonCounters .ge (.const n))) .any

/-- Condition: you've scried or surveilled this turn. -/
def condScriedOrSurveilledThisTurn : Condition :=
  .any #[.turnHistory (.scriedThisTurn .you), .turnHistory (.surveilledThisTurn .you)]

/-- Condition: a creature died this turn. -/
def condCreatureDiedThisTurn : Condition :=
  .turnHistory (.eventOccurredThisTurn .any (.permanentDied (.hasType .creature)))

/-- Condition: you've cast a noncreature spell this turn. -/
def condCastNoncreatureThisTurn : Condition :=
  .turnHistory (.eventOccurredThisTurn .you (.castSpell (.not (.hasType .creature))))

/-- Condition: an opponent has cast a spell this turn. -/
def condOpponentCastSpellThisTurn : Condition :=
  .turnHistory (.eventOccurredThisTurn .opponent (.castSpell .anyObject))

/-- Condition: an opponent was dealt noncombat damage this turn. -/
def condOpponentDealtNoncombatDamageThisTurn : Condition :=
  .turnHistory (.eventOccurredThisTurn .opponent (.dealtDamage false true))

/-- Condition: this spell targets a creature matching `pred`. -/
def condTargetsCreature (pred : ObjectPred) : Condition :=
  .all #[.exists (.target 0), .forAll (.target 0) (.all #[.hasType .creature, pred])]

/-- Condition: there are `n` or more lore counters among Sagas you control. -/
def condSagaLoreCountersAtLeast (n : Nat) : Condition :=
  .cmp .ge
    (.aggregate .sum (.counterCount (some .lore))
      (.inZones .battlefield (.all #[.hasSubtype (.literal .saga), .controlledBy .you])))
    (.const n)

/-- Condition: this permanent has a counter of kind `k` on it. -/
def condSelfHasCounter (k : CounterKind) : Condition :=
  .forAll .this (.counterCount (some k) .ge (.const 1))

/-- Condition: you control a planeswalker with subtype `sub`. -/
def condControlPlaneswalkerSubtype (sub : CardSubtype) : Condition :=
  .exists (.inZones .battlefield (.all #[.hasType .planeswalker, .hasSubtype (.literal sub), .controlledBy .you]))

/-! ### 7. Canonical CR-Semantic Smart Constructors -/

/-- `This creature can't be blocked.` (CR 509.1b). -/
def cantBeBlocked : StaticAbility :=
  .ruleModifying none (.combat (.cantBeBlocked .self))

/-- `This creature can't block.` (CR 509.1b). -/
def cantBlock : StaticAbility :=
  .ruleModifying none (.combat (.cantBlock .self none))

/-- `This creature can't block unless you control a ...` (empty = can't block at all). -/
def cantBlockUnlessYouControl (subtypes : Array CardSubtype) : StaticAbility :=
  if subtypes.isEmpty then cantBlock
  else .ruleModifying none (.combat (.cantBlock .self (some (condControlAnySubtype subtypes))))

/-- `This creature can't be blocked except by N or more creatures.` -/
def cantBeBlockedExceptBy (n : Nat) : StaticAbility :=
  .ruleModifying none (.combat (.minBlockers .self n))

/-- `This creature can't be blocked by more than N creature(s).` -/
def cantBeBlockedByMoreThan (n : Nat) : StaticAbility :=
  .ruleModifying none (.combat (.maxBlockers .self n))

/-- `This creature can't be blocked by tokens.` -/
def cantBeBlockedByTokens : StaticAbility :=
  .ruleModifying none (.combat (.cantBeBlockedBy .self (.isToken true)))

/-- `This creature can't be blocked by creatures with power N or less.` -/
def cantBeBlockedByPowerAtMost (n : Int) : StaticAbility :=
  .ruleModifying none (.combat (.cantBeBlockedBy .self (.all #[.hasType .creature, .stat .power .le (.const n)])))

/-- `This creature can't be blocked by creatures with power N or greater.` -/
def cantBeBlockedByPowerAtLeast (n : Int) : StaticAbility :=
  .ruleModifying none (.combat (.cantBeBlockedBy .self (.all #[.hasType .creature, .stat .power .ge (.const n)])))

/-- `This creature can't be blocked if its power is N or less.` -/
def cantBeBlockedIfPowerAtMost (n : Int) : StaticAbility :=
  .ruleModifying (some (.forAll .this (.stat .power .le (.const n)))) (.combat (.cantBeBlocked .self))

/-- `Creatures you control with power or toughness 1 or less can't be blocked.` -/
def smallCreaturesYouControlUnblockable : StaticAbility :=
  .ruleModifying none (.combat (.cantBeBlocked (.matching {
    zones := .battlefield
    pred := .all #[
      .hasType .creature,
      .controlledBy .you,
      .any #[.stat .power .le (.const 1), .stat .toughness .le (.const 1)]
    ] })))

/-- `This creature attacks each combat if able.` -/
def attacksEachCombatIfAble : StaticAbility :=
  .ruleModifying none (.combat (.attacksEachCombatIfAble .self))

/-- `This creature can't attack unless you control N or more other <subtype>s.` -/
def cantAttackUnlessYouControlNOther (n : Nat) (subtype : CardSubtype) : StaticAbility :=
  .ruleModifying none (.combat (.cantAttackUnless .self (condControlNOtherSubtype n subtype)))

/-- `As long as you've scried or surveilled this turn, this creature can attack as though it didn't have defender.` -/
def attackDespiteDefenderIfScried : StaticAbility :=
  .ruleModifying (some condScriedOrSurveilledThisTurn) (.combat (.attackDespiteDefender .self))

/-- `Creatures you control can attack as though they didn't have defender.` -/
def creaturesAttackDespiteDefender : StaticAbility :=
  .ruleModifying none (.combat (.attackDespiteDefender (.matching scopeCreaturesYouControl)))

/-- `As long as you have an enduring story, creatures can't attack you unless their controller pays {N} for each.` -/
def creaturesCantAttackYouUnlessPayIfEnduringStory (n : Nat) : StaticAbility :=
  .ruleModifying (some condEnduringStory)
    (.combat (.attackTax (.hasType .creature) .you (CostSpec.ofGeneric n)))

/-- `Creatures with flying can't attack you or block creatures you control.` -/
def flyingCantAttackYouOrBlockYours : StaticAbility :=
  let flier : ObjectPred := .all #[.hasType .creature, .hasKeyword .flying]
  .ruleModifying none (.all #[
    .combat (.cantAttackPlayer flier .you),
    .combat (.cantBlockMatching flier (.all #[.hasType .creature, .controlledBy .you]))
  ])

/-- `Each creature you control with toughness greater than its power assigns combat damage equal to its toughness rather than its power.` -/
def toughnessAssignsCombatDamage : StaticAbility :=
  .ruleModifying none (.combat (.assignCombatDamageByToughness scopeCreaturesYouControl true))

/-- `If this creature's power is negative, it assigns combat damage as though its power were positive.` -/
def negativePowerAssignsAsPositive : StaticAbility :=
  .ruleModifying none (.combat (.assignNegativePowerAsPositive .self))

/-- `Other <subtypes> you control have trample.` (empty = `Other creatures you control have trample.`). -/
def otherCreaturesHaveTrample (subtypes : Array CardSubtype) : StaticAbility :=
  .continuous none (scopeOtherCreaturesOfSubtypesYouControl subtypes) (.grantKeywords #[Keyword.trample])

/-- `Other <subtypes> creatures you control get +P/+T.` -/
def otherCreaturesGet (subtypes : Array CardSubtype) (power toughness : Int) : StaticAbility :=
  .continuous none (scopeOtherCreaturesOfSubtypesYouControl subtypes)
    (.modifyPT (.const power) (.const toughness))

/-- `Creatures you control get +P/+T.` -/
def creaturesYouControlGet (power toughness : Int) : StaticAbility :=
  .continuous none scopeCreaturesYouControl (.modifyPT (.const power) (.const toughness))

/-- `Creatures you control get +2/+2 and have flying.` -/
def creaturesYouControlGetAndHave (power toughness : Int) (k : Array KeywordAbility) : StaticAbility :=
  .continuous none scopeCreaturesYouControl
    (.all #[.modifyPT (.const power) (.const toughness), .grantKeywords k])

/-- `Creatures your opponents control get +P/+T.` -/
def opponentsCreaturesGet (power toughness : Int) : StaticAbility :=
  .continuous none scopeOpponentsCreatures (.modifyPT (.const power) (.const toughness))

/-- `Creatures you control of <subtype> get +P/+T.` -/
def creaturesYouControlOfSubtypeGet (subtype : CardSubtype) (power toughness : Int) : StaticAbility :=
  .continuous none (scopeCreaturesOfSubtypeYouControl subtype)
    (.modifyPT (.const power) (.const toughness))

/-- `Creatures you control of the chosen type get +P/+T.` -/
def chosenTypeCreaturesGet (power toughness : Int) : StaticAbility :=
  .continuous none
    { zones := .battlefield
      pred := .all #[.hasType .creature, .hasSubtype .chosenOnSource, .controlledBy .you] }
    (.modifyPT (.const power) (.const toughness))

/-- `Legendary creatures you control get +P/+T and have ward {w}.` -/
def legendaryCreaturesGetAndWard (power toughness : Int) (ward : Nat) : StaticAbility :=
  .continuous none
    { zones := .battlefield
      pred := .all #[.hasSupertype .legendary, .hasType .creature, .controlledBy .you] }
    (.all #[.modifyPT (.const power) (.const toughness), .grantKeywords #[.ward (CostSpec.ofGeneric ward)]])

/-- `Nonlegendary creatures you control get +P/+T.` -/
def nonlegendaryCreaturesGet (power toughness : Int) : StaticAbility :=
  .continuous none
    { zones := .battlefield
      pred := .all #[.not (.hasSupertype .legendary), .hasType .creature, .controlledBy .you] }
    (.modifyPT (.const power) (.const toughness))

/-- `Armies you control have trample.` -/
def armiesYouControlHaveTrample : StaticAbility :=
  .continuous none (scopeCreaturesOfSubtypeYouControl .army) (.grantKeywords #[Keyword.trample])

/-- `Creatures you control have <keywords>.` -/
def creaturesYouControlHave (k : Array KeywordAbility) : StaticAbility :=
  .continuous none scopeCreaturesYouControl (.grantKeywords k)

/-- `Lands you control have hexproof.` -/
def landsHaveHexproof : StaticAbility :=
  .continuous none scopeLandsYouControl (.grantKeywords #[Keyword.hexproof])

/-- `Thopters you control have haste.` -/
def subtypeYouControlHave (sub : CardSubtype) (k : Array KeywordAbility) : StaticAbility :=
  .continuous none (scopeSubtypeYouControl sub) (.grantKeywords k)

/-- `Artifact creatures you control have vigilance.` -/
def artifactCreaturesHaveVigilance : StaticAbility :=
  .continuous none
    { zones := .battlefield
      pred := .all #[.hasType .artifact, .hasType .creature, .controlledBy .you] }
    (.grantKeywords #[Keyword.vigilance])

/-- `Creature tokens you control get +1/+0 and have vigilance.` -/
def creatureTokensGetAndHave (power toughness : Int) (k : Array KeywordAbility) : StaticAbility :=
  .continuous none
    { zones := .battlefield
      pred := .all #[.hasType .creature, .isToken true, .controlledBy .you] }
    (.all #[.modifyPT (.const power) (.const toughness), .grantKeywords k])

/-- `Attacking creature tokens you control have <keywords>.` -/
def attackingTokensHave (k : Array KeywordAbility) : StaticAbility :=
  .continuous none
    { zones := .battlefield
      pred := .all #[.combatRole .attacking, .hasType .creature, .isToken true, .controlledBy .you] }
    (.grantKeywords k)

/-- `Creatures you control with +1/+1 counters on them have <keywords>.` -/
def creaturesWithPlusOneHave (k : Array KeywordAbility) : StaticAbility :=
  .continuous none
    { zones := .battlefield
      pred := .all #[.hasType .creature, .controlledBy .you, .counterCount (some .plusOnePlusOne) .ge (.const 1)] }
    (.grantKeywords k)

/-- `Each other creature you control with a +1/+1 counter on it has <keywords>.` -/
def otherPlusOneCreaturesHave (k : Array KeywordAbility) : StaticAbility :=
  .continuous none
    { zones := .battlefield
      pred := .all #[.otherThan .this, .hasType .creature, .controlledBy .you,
                     .counterCount (some .plusOnePlusOne) .ge (.const 1)] }
    (.grantKeywords k)

/-- `Each creature you control that you've put one or more +1/+1 counters on this turn has hexproof.` -/
def hexproofIfPlusOneThisTurn : StaticAbility :=
  .continuous none
    { zones := .battlefield
      pred := .all #[.hasType .creature, .controlledBy .you,
                     .receivedCounterThisTurn (some .plusOnePlusOne) (some .you)] }
    (.grantKeywords #[Keyword.hexproof])

/-- `As long as you've put one or more +1/+1 counters on this creature this turn, it has flying.` -/
def flyingIfPlusOneThisTurn : StaticAbility :=
  .continuous
    (some (.forAll .this (.receivedCounterThisTurn (some .plusOnePlusOne) (some .you))))
    scopeSelf (.grantKeywords #[Keyword.flying])

/-- `This creature has hexproof as long as it hasn't dealt combat damage yet.` -/
def hexproofUntilCombatDamage : StaticAbility :=
  .continuous
    (some (.forAll .this (.not (.dealtDamageThisTurn true none false))))
    scopeSelf (.grantKeywords #[Keyword.hexproof])

/-- `During your turn, this creature has first strike.` -/
def firstStrikeDuringYourTurn : StaticAbility :=
  .continuous (some .isYourTurn) scopeSelf (.grantKeywords #[Keyword.firstStrike])

/-- `This creature has vigilance as long as you control a Jace planeswalker.` -/
def vigilanceIfPlaneswalkerSubtype (sub : CardSubtype) : StaticAbility :=
  .continuous (some (condControlPlaneswalkerSubtype sub)) scopeSelf
    (.grantKeywords #[Keyword.vigilance])

/-- `As long as an opponent was dealt noncombat damage this turn, this creature has flying and haste.` -/
def flyingHasteIfOpponentDealtNoncombat : StaticAbility :=
  .continuous (some condOpponentDealtNoncombatDamageThisTurn) scopeSelf
    (.grantKeywords #[Keyword.flying, Keyword.haste])

/-- `This creature gets +1/+0 and has flying as long as there are seven or more cards in your graveyard.` -/
def powerAndFlyingIfSevenInGraveyard : StaticAbility :=
  .continuous (some (condGraveyardAtLeast 7)) scopeSelf
    (.all #[.modifyPT (.const 1) (.const 0), .grantKeywords #[Keyword.flying]])

/-- `Threshold — this creature gets +P/+T as long as there are seven or more cards in your graveyard.` -/
def thresholdGets (power toughness : Int) : StaticAbility :=
  .continuous (some (condGraveyardAtLeast 7)) scopeSelf
    (.modifyPT (.const power) (.const toughness))

/-- `This creature has <kw> as long as you control another <subtype>.` -/
def keywordIfYouControlOtherSubtype (kw : KeywordAbility) (subtype : CardSubtype) : StaticAbility :=
  .continuous (some (condControlOtherSubtype subtype)) scopeSelf (.grantKeywords #[kw])

def hasteIfYouControlOtherSubtype (subtype : CardSubtype) : StaticAbility :=
  keywordIfYouControlOtherSubtype Keyword.haste subtype

def lifelinkIfYouControlOtherSubtype (subtype : CardSubtype) : StaticAbility :=
  keywordIfYouControlOtherSubtype Keyword.lifelink subtype

/-- `During your turn, creatures you control that are equipped have <keywords>.` -/
def equippedCreaturesHaveKeywordsDuringYourTurn (k : Array KeywordAbility) : StaticAbility :=
  .continuous (some .isYourTurn)
    { zones := .battlefield
      pred := .all #[
        .hasType .creature,
        .controlledBy .you,
        .hasAttachment { zones := .battlefield, pred := .hasSubtype (.literal .equipment) }
      ] }
    (.grantKeywords k)

/-- `As long as you have an enduring story, this gets +P/+T and has <keywords>.` -/
def getsAndHasIfEnduringStory (power toughness : Int) (k : Array KeywordAbility) : StaticAbility :=
  let mods : Array ContinuousModification :=
    (if power != 0 || toughness != 0 then #[.modifyPT (.const power) (.const toughness)] else #[]) ++
    (if k.isEmpty then #[] else #[.grantKeywords k])
  .continuous (some condEnduringStory) scopeSelf (ContinuousModification.ofArray mods)

/-- `As long as you have an enduring story, creatures you control get +P/+T.` -/
def creaturesYouControlGetIfEnduringStory (power toughness : Int) : StaticAbility :=
  .continuous (some condEnduringStory) scopeCreaturesYouControl
    (.modifyPT (.const power) (.const toughness))

/-- `As long as you have an enduring story, artifacts and creatures you control have ward {w}.` -/
def artifactsAndCreaturesHaveWardIfEnduringStory (ward : Nat) : StaticAbility :=
  .continuous (some condEnduringStory)
    { zones := .battlefield
      pred := .all #[.any #[.hasType .artifact, .hasType .creature], .controlledBy .you] }
    (.grantKeywords #[.ward (CostSpec.ofGeneric ward)])

/-- `As long as there are <min> or more creature cards in your graveyard, this creature gets +P/+T.` -/
def getsIfGyCreatureCards (min : Nat) (power toughness : Int) : StaticAbility :=
  .continuous (some (condGyCreatureCardsAtLeast min)) scopeSelf
    (.modifyPT (.const power) (.const toughness))

/-- `As long as there are <min> or more creature cards in your graveyard, this creature gets +P/+T and is all creature types.` -/
def getsAndAllTypesIfGyCreatureCards (min : Nat) (power toughness : Int) : StaticAbility :=
  .continuous (some (condGyCreatureCardsAtLeast min)) scopeSelf
    (.all #[.modifyPT (.const power) (.const toughness), .addAllCreatureTypes])

/-- `As long as you control an artifact creature or a Plan, this has indestructible.` -/
def indestructibleIfArtifactCreatureOrPlan : StaticAbility :=
  .continuous
    (some (.exists (.inZones .battlefield (.all #[
      .any #[.all #[.hasType .artifact, .hasType .creature], .hasSubtype (.literal .plan)],
      .controlledBy .you
    ]))))
    scopeSelf (.grantKeywords #[Keyword.indestructible])

/-- `As long as there are N or more lore counters among Sagas you control, this has hexproof and indestructible.` -/
def hexproofIndestructibleIfLore (n : Nat) : StaticAbility :=
  .continuous (some (condSagaLoreCountersAtLeast n)) scopeSelf
    (.grantKeywords #[Keyword.hexproof, Keyword.indestructible])

/-- `Corrupted — As long as an opponent has three or more poison counters, creatures you control with toxic have lifelink.` -/
def corruptedToxicLifelink : StaticAbility :=
  .continuous (some (condOpponentPoisonAtLeast 3))
    { zones := .battlefield
      pred := .all #[.hasType .creature, .controlledBy .you, .hasKeyword .toxic] }
    (.grantKeywords #[Keyword.lifelink])

/-- `As long as this has a shield counter on it, you and other <subtype>s you control have hexproof.` -/
def youAndOtherSubtypeHaveHexproofIfShield (subtype : CardSubtype) : StaticAbility :=
  .continuous (some (condSelfHasCounter .shield)) (scopeOtherSubtypeYouControl subtype)
    (.all #[.grantKeywords #[Keyword.hexproof], .applyRule (.player (.hexproof .you))])

/-- `You and creatures you control have protection from the chosen card type.` -/
def protectionFromChosenCardType : StaticAbility :=
  .continuous none scopeCreaturesYouControl
    (.all #[.grantKeywords #[.protection .chosenCardType],
            .applyRule (.player (.protectionFrom .you .chosenCardType))])

/-- `Enchanted creature gets +P/+T.` -/
def enchantedCreatureGets (power toughness : Int) : StaticAbility :=
  .continuous none scopeEnchantedCreature (.modifyPT (.const power) (.const toughness))

/-- `Equipped creature gets +P/+T.` -/
def equippedCreatureGets (power toughness : Int) : StaticAbility :=
  .continuous none scopeEquippedCreature (.modifyPT (.const power) (.const toughness))

/-- `Equipped creature has <keywords>.` -/
def equippedCreatureHasKeywords (k : Array KeywordAbility) : StaticAbility :=
  .continuous none scopeEquippedCreature (.grantKeywords k)

/-- `Enchanted creature gets +P/+T and has <keywords>.` -/
def enchantedCreatureGetsAndHas (power toughness : Int) (k : Array KeywordAbility) : StaticAbility :=
  .continuous none scopeEnchantedCreature
    (.all #[.modifyPT (.const power) (.const toughness), .grantKeywords k])

/-- `Equipped creature gets +P/+T and has <keywords>.` -/
def equippedCreatureGetsAndHas (power toughness : Int) (k : Array KeywordAbility) : StaticAbility :=
  .continuous none scopeEquippedCreature
    (.all #[.modifyPT (.const power) (.const toughness), .grantKeywords k])

/-- `Equipped creature gets +P/+T and has ward {w}.` -/
def equippedCreatureGetsAndWard (power toughness : Int) (ward : Nat) : StaticAbility :=
  .continuous none scopeEquippedCreature
    (.all #[.modifyPT (.const power) (.const toughness), .grantKeywords #[.ward (CostSpec.ofGeneric ward)]])

/-- `Enchanted creature has ward {w}.` -/
def enchantedCreatureHasWard (ward : Nat) : StaticAbility :=
  .continuous none scopeEnchantedCreature (.grantKeywords #[.ward (CostSpec.ofGeneric ward)])

/-- `Equipped creature gets +P/+T and has <keywords> and ward {w}.` -/
def equippedCreatureGetsHasAndWard (power toughness : Int) (k : Array KeywordAbility) (ward : Nat) : StaticAbility :=
  .continuous none scopeEquippedCreature
    (.all #[.modifyPT (.const power) (.const toughness),
            .grantKeywords (k.push (.ward (CostSpec.ofGeneric ward)))])

/-- `Enchanted creature gets +P/+T and has <keywords> and ward {w}.` -/
def enchantedCreatureGetsHasAndWard (power toughness : Int) (k : Array KeywordAbility) (ward : Nat) : StaticAbility :=
  .continuous none scopeEnchantedCreature
    (.all #[.modifyPT (.const power) (.const toughness),
            .grantKeywords (k.push (.ward (CostSpec.ofGeneric ward)))])

/-- `Enchanted creature gets +P/+T, has <keywords>, and is a legendary <subtypes> in addition to its other types.` -/
def enchantedCreatureGetsHasAndTypes (power toughness : Int) (k : Array KeywordAbility)
    (types : Array CardSubtype) : StaticAbility :=
  let mods : Array ContinuousModification :=
    #[.modifyPT (.const power) (.const toughness), .grantKeywords k] ++
    (if types.isEmpty then #[]
     else #[.modifyTypes { mode := .addDedup, subtypes := types, supertypes := #[.legendary] }])
  .continuous none scopeEnchantedCreature (ContinuousModification.ofArray mods)

/-- `Enchanted permanent is a Construct creature with base power and toughness 5/5 in addition to its other types.` -/
def enchantedIsConstruct55 : StaticAbility :=
  .continuous none scopeEnchantedPermanent
    (.all #[
      .modifyTypes { mode := .addDedup, types := #[.artifact, .creature], subtypes := #[.construct] },
      .setBasePT (some (.const 5)) (some (.const 5))
    ])

/-- `Enchanted creature is a <subtype> and can't attack or block.` -/
def enchantedIsOnlySubtypeCantAttackOrBlock (subtype : CardSubtype) : StaticAbility :=
  .continuous none scopeEnchantedCreature
    (.all #[
      .modifyTypes { mode := .setAndKeepNoncreatureSubtypes, subtypes := #[subtype] },
      .applyRule (.all #[.combat (.cantAttack .self), .combat (.cantBlock .self)])
    ])

/-- `Enchanted creature loses all abilities and doesn't untap during its controller's untap step.` -/
def enchantedLosesAbilitiesDoesntUntap : StaticAbility :=
  .continuous none scopeEnchantedCreature
    (.all #[.loseAllAbilities, .applyRule (.game (.doesntUntapDuringUntapStep .self none))])

/-- `Enchanted creature loses all abilities and can't become untapped.` -/
def enchantedLosesAbilitiesCantUntap : StaticAbility :=
  .continuous none scopeEnchantedCreature
    (.all #[.loseAllAbilities, .applyRule (.game (.cantBecomeUntapped .self))])

/-- `Equipped creature has <keywords> and can't be blocked.` -/
def equippedCreatureHasKeywordsAndCantBeBlocked (k : Array KeywordAbility) : StaticAbility :=
  .continuous none scopeEquippedCreature
    (.all #[.grantKeywords k, .grantStatic #[cantBeBlocked]])

/-- `During your turn, equipped creature has hexproof and can't be blocked.` -/
def equippedHexproofUnblockableDuringYourTurn : StaticAbility :=
  .continuous (some .isYourTurn) scopeEquippedCreature
    (.all #[.grantKeywords #[Keyword.hexproof], .grantStatic #[cantBeBlocked]])

/-- `Equipped creature gets +2/+0 and has "Whenever this creature attacks, it gains your choice of trample or deathtouch until end of turn."` -/
def equippedGetsAndAttackChooseKeyword : StaticAbility :=
  .continuous none scopeEquippedCreature
    (.all #[
      .modifyPT (.const 2) (.const 0),
      .grantTriggered #[TriggeredAbility.ofPattern .thisAttacks
        "Whenever this creature attacks, it gains your choice of trample or deathtouch until end of turn."
        (.player (.choose .you (.keyword #[Keyword.trample, Keyword.deathtouch])))]
    ])

/-- `Equipped creature gets +1/+0 and has flying and "Whenever this creature attacks, you gain 1 life."` -/
def equippedGetsFlyingAndAttackGainLife : StaticAbility :=
  .continuous none scopeEquippedCreature
    (.all #[
      .modifyPT (.const 1) (.const 0),
      .grantKeywords #[Keyword.flying],
      .grantTriggered #[TriggeredAbility.ofPattern .thisAttacks
        "Whenever this creature attacks, you gain 1 life." (Instruction.gainLifeFixed 1)]
    ])

/-- `Equipped creature gets +P/+T and has trample and "Whenever this creature deals combat damage to a player or planeswalker, create that many Treasure tokens."` -/
def equippedGetsTrampleAndCombatTreasures (power toughness : Int) : StaticAbility :=
  .continuous none scopeEquippedCreature
    (.all #[
      .modifyPT (.const power) (.const toughness),
      .grantKeywords #[Keyword.trample],
      .grantTriggered #[TriggeredAbility.ofPattern .thisDealsCombatDamageToPlayerOrPlaneswalker
        "Whenever this creature deals combat damage to a player or planeswalker, create that many Treasure tokens."
        (Instruction.createTokens .treasure .eventAmount)]
    ])

/-- `Equipped creature has first strike and gets +1/+0 for each instant and sorcery card in your graveyard.` -/
def equippedFirstStrikePlusPerInstantSorcery : StaticAbility :=
  let cnt : ValueExpr :=
    .aggregate .count .one
      (.inZones .yourGraveyard (.all #[.isCard, .any #[.hasType .instant, .hasType .sorcery]]))
  .continuous none scopeEquippedCreature
    (.all #[.grantKeywords #[Keyword.firstStrike], .modifyPT cnt (.const 0)])

/-- `Other <subtypes> you control have "{T}: Add <mana>."` -/
def otherSubtypeHaveTapAddOneOf (subtypes : Array CardSubtype) (mana : Array ManaType) : StaticAbility :=
  .continuous none (scopeOtherSubtypesYouControl subtypes)
    (.grantActivated #[ActivatedAbility.manaAbility (.oneOf (.explicit mana) (.const 1)) CostSpec.tapOnly])

/-- `Creatures you control have "{T}: Add one mana of any color."` -/
def grantCreaturesTapAddAnyColor : StaticAbility :=
  .continuous none scopeCreaturesYouControl
    (.grantActivated #[ActivatedAbility.manaAbility (.oneOf .anyColor (.const 1)) CostSpec.tapOnly])

/-- `Lands you control have "{T}: Add one mana of any color."` -/
def grantLandsTapAnyColor : StaticAbility :=
  .continuous none scopeLandsYouControl
    (.grantActivated #[ActivatedAbility.manaAbility (.oneOf .anyColor (.const 1)) CostSpec.tapOnly])

/-- `Planeswalkers you control have "<activated ability>."` -/
def planeswalkersYouControlHave (abilities : Array ActivatedAbility) : StaticAbility :=
  .continuous none scopePlaneswalkersYouControl (.grantActivated abilities)

/-- `Planeswalkers you control have "No more than one creature can attack this planeswalker each combat."` -/
def planeswalkersAttackedByOneAtMost : StaticAbility :=
  .continuous none scopePlaneswalkersYouControl
    (.grantStatic #[.ruleModifying none (.combat (.maxAttackersPerPermanent .self 1))])

/-- `This has all activated abilities of all <subtype> cards in your graveyard.` -/
def copyActivatedFromGySubtype (subtype : CardSubtype) : StaticAbility :=
  .continuous none scopeSelf
    (.copyActivatedFrom { zones := .yourGraveyard
                          pred := .all #[.isCard, .hasSubtype (.literal subtype)] })

/-- `Instant and sorcery spells you control have split second.` (CR 702.61). -/
def instantSorcerySplitSecond : StaticAbility :=
  .continuous none scopeInstantSorcerySpellsYouControl (.grantKeywords #[Keyword.splitSecond])

/-- `Noncreature spells you cast have improvise.` (CR 702.126). -/
def noncreatureSpellsHaveImprovise : StaticAbility :=
  .continuous none scopeNoncreatureSpellsYouControl (.grantKeywords #[Keyword.improvise])

/-- Dynamic Layer 7c: `This creature gets +N/+0 for each Mountain you control.` -/
def powerPerMountain (n : Nat) : StaticAbility :=
  let cnt := countBf (.all #[.hasSubtype (.literal .mountain), .controlledBy .you])
  .continuous none scopeSelf (.modifyPT (scaledValue n cnt) (.const 0))

/-- Dynamic Layer 7c: `This creature gets +1/+1 for each unspent mana you have.` -/
def powerPerUnspentMana : StaticAbility :=
  let v := ValueExpr.playerMetric .unspentMana .you
  .continuous none scopeSelf (.modifyPT v v)

/-- Dynamic Layer 7c: `This creature gets +2/+0 for every seven cards in your graveyard.` -/
def powerPerSevenInGraveyard : StaticAbility :=
  let v : ValueExpr :=
    .binary .mul (.const 2) (.binary .divFloor (.playerMetric .graveyardSize .you) (.const 7))
  .continuous none scopeSelf (.modifyPT v (.const 0))

/-- Dynamic Layer 7c: `This creature gets +P/+0 for each graveyard with seven or more cards in it.` -/
def powerPerFatGraveyard (power : Int) : StaticAbility :=
  let cnt : ValueExpr :=
    .playerMetric .one (.matching .anyPlayer (.metric .graveyardSize .ge (.const 7)))
  .continuous none scopeSelf (.modifyPT (scaledValue power cnt) (.const 0))

/-- Dynamic Layer 7c: `This creature gets +1/+0 for each creature and planeswalker card in your graveyard.` -/
def powerPerCreatureAndPlaneswalkerCard : StaticAbility :=
  let cnt : ValueExpr :=
    .aggregate .count .one
      (.inZones .yourGraveyard (.all #[.isCard, .any #[.hasType .creature, .hasType .planeswalker]]))
  .continuous none scopeSelf (.modifyPT cnt (.const 0))

/-- Dynamic Layer 7c: `This creature gets +P/+0 for each other artifact you control.` -/
def getsPowerPerOtherArtifact (power : Int) : StaticAbility :=
  let cnt := countBf (.all #[.otherThan .this, .hasType .artifact, .controlledBy .you])
  .continuous none scopeSelf (.modifyPT (scaledValue power cnt) (.const 0))

/-- Dynamic Layer 7c: `This creature gets +P/+0 for each Equipment attached to it.` -/
def getsPowerPerAttachedEquipment (power : Int) : StaticAbility :=
  let cnt := countBf (.all #[.hasSubtype (.literal .equipment), .attachedTo .this])
  .continuous none scopeSelf (.modifyPT (scaledValue power cnt) (.const 0))

/-- Dynamic Layer 7c: `Other <subtype>s you control get +1/+0 for each artifact token you control.` -/
def otherSubtypeGetPowerPerArtifactToken (subtype : CardSubtype) : StaticAbility :=
  let cnt := countBf (.all #[.hasType .artifact, .isToken true, .controlledBy .you])
  .continuous none (scopeOtherSubtypeYouControl subtype) (.modifyPT cnt (.const 0))

-- Characteristic-defining abilities (CR 604.3)

def powerToughnessEqualLandsYouControl : StaticAbility :=
  let n := countBf (.all #[.hasType .land, .controlledBy .you])
  .characteristicDefining (.setPT (some n) (some n))

def powerEqualCardsInHand : StaticAbility :=
  .characteristicDefining (.setPT (some (.playerMetric .handSize .you)) none)

def powerEqualCreaturesYouControl : StaticAbility :=
  .characteristicDefining (.setPT (some (countBf (.all #[.hasType .creature, .controlledBy .you]))) none)

def powerEqualSubtypeYouControl (subtype : CardSubtype) : StaticAbility :=
  .characteristicDefining
    (.setPT (some (countBf (.all #[.hasSubtype (.literal subtype), .controlledBy .you]))) none)

def powerEqualLegendaryCreaturesYouControl : StaticAbility :=
  .characteristicDefining
    (.setPT (some (countBf (.all #[.hasSupertype .legendary, .hasType .creature, .controlledBy .you]))) none)

def ptEqualGraveyardCardTypes : StaticAbility :=
  let n : ValueExpr := .cardTypeCount (.inZones .anyGraveyard .isCard)
  .characteristicDefining (.setPT (some n) (some (.binary .add n (.const 1))))

def powerEqualsBasicLandTypes : StaticAbility :=
  let n : ValueExpr :=
    .basicLandTypeCount (.inZones .battlefield (.all #[.hasType .land, .controlledBy .you]))
  .characteristicDefining (.setPT (some n) none)

-- Player, Play, Trigger, and Game rule-modifying statics

def noMaximumHandSize : StaticAbility :=
  .ruleModifying none (.player (.maxHandSize .you none))

def maximumHandSize (n : Nat) : StaticAbility :=
  .ruleModifying none (.player (.maxHandSize .you (some n)))

def extraLandIfOtherSubtype (sub : CardSubtype) : StaticAbility :=
  .ruleModifying (some (condControlOtherSubtype sub)) (.player (.additionalLands .you 1))

def opponentsCantGainLife : StaticAbility :=
  .ruleModifying none (.player (.cantGainLife .opponent))

def cantLoseAndOpponentsCantWin : StaticAbility :=
  .ruleModifying none (.all #[.player (.cantLoseGame .you), .player (.cantWinGame .opponent)])

def opponentsCantCastOnYourTurn : StaticAbility :=
  .ruleModifying (some .isYourTurn) (.player (.cantCastSpells .opponent .anyObject))

def chosenNameSpellsCantBeCast : StaticAbility :=
  .ruleModifying none (.player (.cantCastSpells .any (.named .chosenOnSource)))

def activateCreaturesAsThoughHaste : StaticAbility :=
  .ruleModifying none (.player (.activateAsThoughHaste .you scopeCreaturesYouControl))

def extraPowerUpActivation : StaticAbility :=
  .ruleModifying none (.player (.extraAbilityActivation .powerUp scopePermanentsYouControl 1))

def mayLookAtTopAnytime : StaticAbility :=
  .ruleModifying none (.play (.lookAtTopOfLibrary .you))

def mayCastCreaturesFromTop : StaticAbility :=
  .ruleModifying none (.play (.mayPlayFrom .you .library (.hasType .creature)))

def mayPlayLandsFromTop : StaticAbility :=
  .ruleModifying none (.play (.mayPlayFrom .you .library (.hasType .land) (landsAllowed := true)))

def mayPlayLandsFromGraveyard : StaticAbility :=
  .ruleModifying none (.play (.mayPlayFrom .you .graveyard (.hasType .land) (landsAllowed := true)))

def castExiledWithSevenInGraveyard : StaticAbility :=
  .ruleModifying (some (condGraveyardAtLeast 7))
    (.play (.mayPlayFrom .you .exile .anyObject (linkedExile := true) (castAnyColorMana := true)))

def castFromHandFreeUpToCreatures : StaticAbility :=
  let nCreatures := countBf (.all #[.hasType .creature, .controlledBy .you])
  .ruleModifying none
    (.play (.mayPlayFrom .you .hand (.stat .manaValue .le nCreatures) (freeCast := true)))

def flashIfYouControlSubtype (sub : CardSubtype) : StaticAbility :=
  .ruleModifying (some (condControlSubtype sub))
    (.play (.castAsThoughFlash .you .anyObject (thisSpell := true)))

def firstCreatureHasFlash : StaticAbility :=
  .ruleModifying none (.play (.castAsThoughFlash .you (.hasType .creature) (nthEachTurn? := some 1)))

def flashIfOpponentCastThisTurn : StaticAbility :=
  .ruleModifying (some condOpponentCastSpellThisTurn) (.play (.castAsThoughFlash .you .anyObject))

def spellCantBeCountered : StaticAbility :=
  .ruleModifying none (.play (.spellCantBeCountered none))

def castOnlyIfGraveyardAtLeast (n : Nat) : StaticAbility :=
  .ruleModifying none (.play (.castRestriction (condOtherCardsInGraveyardAtLeast n)))

def mayBeginOnBattlefield : StaticAbility :=
  .ruleModifying none (.play .mayBeginOnBattlefield)

def canBeCommander : StaticAbility :=
  .ruleModifying none (.play .canBeCommander)

def extraTriggerIfEnduringStorySubtype (subtype : CardSubtype) : StaticAbility :=
  .ruleModifying (some condEnduringStory)
    (.trigger (.extraTrigger (scopeSubtypeYouControl subtype) 1))

def extraTriggerAnotherYouControl (subtypes : Array CardSubtype) (types : Array CardType) : StaticAbility :=
  let predParts : Array ObjectPred :=
    subtypes.map (fun s => .hasSubtype (.literal s)) ++ types.map ObjectPred.hasType
  let kindPred : ObjectPred :=
    match predParts.toList with
    | [p] => p
    | _ => .any predParts
  .ruleModifying none
    (.trigger (.extraTrigger { zones := .battlefield
                               pred := .all #[.otherThan .this, kindPred, .controlledBy .you] } 1))

def equippedTriggersAgain : StaticAbility :=
  .ruleModifying none (.trigger (.extraTrigger scopeEquippedCreature 1))

def enteringArtifactsCreaturesDontTrigger : StaticAbility :=
  .ruleModifying none
    (.trigger (.suppressEnteringTriggers { zones := .battlefield
                                           pred := .any #[.hasType .artifact, .hasType .creature] }))

def doesntUntap : StaticAbility :=
  .ruleModifying none (.game (.doesntUntapDuringUntapStep .self none))

def doesntUntapUnlessEnduringStory : StaticAbility :=
  .ruleModifying none (.game (.doesntUntapDuringUntapStep .self (some condEnduringStory)))

def noSpellsOrAbilitiesDuringCombat : StaticAbility :=
  .ruleModifying none (.game (.lockNonManaDuringPhase .combat .any))

def planeswalkersSurviveZeroLoyalty : StaticAbility :=
  .ruleModifying none (.game (.planeswalkersSurviveZeroLoyalty scopePlaneswalkersYouControl))

def creaturesCantGetMinusCounters : StaticAbility :=
  .ruleModifying none (.game (.cantHaveCountersPutOn scopeCreaturesYouControl (some .minusOneMinusOne)))

-- Cost modifiers (CR 601.2f / 602.2b)

def costReductionIfCreatureDied (n : Nat) : StaticAbility :=
  .costModifier (some condCreatureDiedThisTurn) .thisSpell (.reduceGeneric (.const n))

def costReductionIfTargetDamaged (n : Nat) : StaticAbility :=
  .costModifier (some (condTargetsCreature .wasDealtDamageThisTurn)) .thisSpell (.reduceGeneric (.const n))

def costReductionIfTargetTapped (n : Nat) : StaticAbility :=
  .costModifier (some (condTargetsCreature (.tapped true))) .thisSpell (.reduceGeneric (.const n))

def costReductionIfTargetAttackingNontoken (n : Nat) : StaticAbility :=
  .costModifier (some (condTargetsCreature (.all #[.combatRole .attacking, .isToken false])))
    .thisSpell (.reduceGeneric (.const n))

def costReductionIfTargetAttacking (n : Nat) : StaticAbility :=
  .costModifier (some (condTargetsCreature (.combatRole .attacking))) .thisSpell (.reduceGeneric (.const n))

def costReductionIfYouControl (n : Nat) (sub : CardSubtype) : StaticAbility :=
  .costModifier (some (condControlSubtype sub)) .thisSpell (.reduceGeneric (.const n))

def costReductionIfYouControlLegendary (n : Nat) : StaticAbility :=
  .costModifier (some condControlLegendaryCreature) .thisSpell (.reduceGeneric (.const n))

def costReductionIfGyCreaturesAtLeast (min n : Nat) : StaticAbility :=
  .costModifier (some (condGyCreatureCardsAtLeast min)) .thisSpell (.reduceGeneric (.const n))

def costReductionEqualFlyingPower : StaticAbility :=
  let v : ValueExpr :=
    .aggregate .sum (.stat .power)
      (.inZones .battlefield (.all #[.hasType .creature, .controlledBy .you, .hasKeyword .flying]))
  .costModifier none .thisSpell (.reduceGeneric v)

def costReductionGreatestPower : StaticAbility :=
  let v : ValueExpr :=
    .aggregate .max (.stat .power)
      (.inZones .battlefield (.all #[.hasType .creature, .controlledBy .you]))
  .costModifier none .thisSpell (.reduceGeneric v)

def costReductionGreatestToughness : StaticAbility :=
  let v : ValueExpr :=
    .aggregate .max (.stat .toughness)
      (.inZones .battlefield (.all #[.hasType .creature, .controlledBy .you]))
  .costModifier none .thisSpell (.reduceGeneric v)

def costReductionEqualOppArtifacts : StaticAbility :=
  .costModifier none .thisSpell (.reduceGeneric (.maxControlled .opponent (.hasType .artifact)))

def costsLessIfCastNoncreature (n : Nat := 2) : StaticAbility :=
  .costModifier (some condCastNoncreatureThisTurn) .thisSpell (.reduceGeneric (.const n))

def freeCastIfControlCommander : StaticAbility :=
  .costModifier (some condControlCommander) .thisSpell .alternativeFree

def subtypeSpellsCostLess (subtype : CardSubtype) (n : Nat) : StaticAbility :=
  .costModifier none (.spells .you (.hasSubtype (.literal subtype))) (.reduceGeneric (.const n))

def typeSpellsCostLess (ty : CardType) (n : Nat) : StaticAbility :=
  .costModifier none (.spells .you (.hasType ty)) (.reduceGeneric (.const n))

def supertypeSpellsCostLess (s : Supertype) (n : Nat) : StaticAbility :=
  .costModifier none (.spells .you (.hasSupertype s)) (.reduceGeneric (.const n))

def noncreatureSpellsCostLess (n : Nat := 1) : StaticAbility :=
  .costModifier none (.spells .you (.not (.hasType .creature))) (.reduceGeneric (.const n))

def opponentsNoncreatureSpellsCostMore (n : Nat := 1) : StaticAbility :=
  .costModifier none (.spells .opponent (.not (.hasType .creature))) (.increaseGeneric (.const n))

def firstCreatureCostsLess (n : Nat) : StaticAbility :=
  .costModifier none (.spells .you (.hasType .creature) (nthEachTurn? := some 1)) (.reduceGeneric (.const n))

def costReductionNotFromHand (n : Nat) : StaticAbility :=
  .costModifier none (.spells .you .anyObject (notFromZone? := some .hand)) (.reduceGeneric (.const n))

def eminenceSubtypeSpellsCostLess (sub : CardSubtype) (n : Nat) : StaticAbility :=
  .costModifier none
    (.spells .you (.all #[.otherThan .this, .hasSubtype (.literal sub)])
      (activeZones := #[.battlefield, .command]))
    (.reduceGeneric (.const n))

def instantSorceryCostReductionEqualEquippedPower : StaticAbility :=
  .costModifier none
    (.spells .you (.any #[.hasType .instant, .hasType .sorcery]))
    (.reduceGeneric (.objectStat .power .attachedHost))

def instantSorceryCostLessEqualPower : StaticAbility :=
  .costModifier none
    (.spells .you (.all #[.any #[.hasType .instant, .hasType .sorcery], .stat .manaValue .ge (.const 4)]))
    (.reduceGeneric (.objectStat .power .this))

def equipAbilitiesTargetingThisCostLess (n : Nat) : StaticAbility :=
  .costModifier none
    (.abilities .you (some (.equip none)) { zones := .battlefield, pred := .anyObject }
      (targetPred? := some (.sameAs .this)))
    (.reduceGeneric (.const n))

def firstEquipFreeIfEnduringStory : StaticAbility :=
  .costModifier (some condEnduringStory)
    (.abilities .you (some (.equip none)) { zones := .battlefield, pred := .anyObject }
      (nthEachTurn? := some 1))
    .alternativeFree

def otherPowerUpCostsLess (n : Nat) : StaticAbility :=
  .costModifier none (.abilities .you (some .powerUp) scopeOtherCreaturesYouControl) (.reduceGeneric (.const n))

-- Replacement & prevention statics (CR 614 / 615)

def entersTapped : StaticAbility :=
  .replacement none (.entersTapped .self none)

def entersTappedUnless (cond : Condition) : StaticAbility :=
  .replacement none (.entersTapped .self (some cond))

def entersTappedUnlessLegendary : StaticAbility :=
  entersTappedUnless condControlLegendaryCreature

def entersTappedUnlessEquipment : StaticAbility :=
  entersTappedUnless (condControlSubtype .equipment)

def entersTappedUnlessPlaneswalker : StaticAbility :=
  entersTappedUnless condControlPlaneswalker

def entersTappedUnlessTwoOtherLands : StaticAbility :=
  entersTappedUnless (condControlNOtherLands 2)

def entersTappedUnlessAnySubtype (subs : Array CardSubtype) : StaticAbility :=
  entersTappedUnless (condControlLandAnySubtype subs)

def entersTappedUnlessNBasics (n : Nat) : StaticAbility :=
  entersTappedUnless (condControlNBasicLands n)

def entersTappedUnlessOppLands (n : Nat) : StaticAbility :=
  entersTappedUnless (condOpponentsControlNLands n)

def entersTappedUnlessPayLife (n : Nat) : StaticAbility :=
  .replacement none (.entersTappedUnlessPay (CostSpec.ofItems #[.payLife (.const n)]))

def entersTappedUnlessBehold (sub : CardSubtype) : StaticAbility :=
  .replacement none (.entersTappedUnlessPay (CostSpec.ofItems #[.behold sub]))

def entersTappedChooseColor : StaticAbility :=
  .replacement none (.all #[.entersTapped .self none, .asEntersChoose .color])

def entersWithCounters (kind : CounterKind) (count : ValueExpr) : StaticAbility :=
  .replacement none (.entersWithCounters .self kind count false)

def entersWithPlusOneCounters (n : Nat) : StaticAbility :=
  entersWithCounters .plusOnePlusOne (.const n)

def entersWithXPlusOne : StaticAbility :=
  entersWithCounters .plusOnePlusOne .chosenX

def entersWithIndestructibleCounter : StaticAbility :=
  entersWithCounters .indestructible (.const 1)

def entersWithShield (n : Nat) : StaticAbility :=
  entersWithCounters .shield (.const n)

def entersWithHopePerCreature : StaticAbility :=
  entersWithCounters .hope (countBf (.all #[.hasType .creature, .controlledBy .you]))

def othersEnterWithPlusOneEqualToughness : StaticAbility :=
  .replacement none
    (.entersWithCounters (.matching scopeOtherCreaturesYouControl) .plusOnePlusOne
      (.objectStat .toughness .this) true)

def entersPrepared : StaticAbility :=
  .replacement none (.entersWithDesignation .prepared)

def asEntersChooseCreatureType : StaticAbility :=
  .replacement none (.asEntersChoose .creatureType)

def asEntersChooseOddEven : StaticAbility :=
  .replacement none (.asEntersChoose .oddOrEven)

def asEntersChooseCardType : StaticAbility :=
  .replacement none (.asEntersChoose .cardType)

def asEntersChooseNonlandCardName : StaticAbility :=
  .replacement none (.asEntersChoose .nonlandCardName)

def asEntersChooseNamedAnchors (options : Array String) : StaticAbility :=
  .replacement none (.asEntersChoose (.namedAnchors options))

def asEntersMayCopyCreatureHasteUntilEot : StaticAbility :=
  .replacement none
    (.asEntersMayCopy { zones := .battlefield, pred := .hasType .creature }
      .untilEndOfTurn #[.addKeywords #[Keyword.haste]])

def exileOpponentsDyingCreatures : StaticAbility :=
  .replacement none (.exileInsteadOfDying scopeOpponentsCreatures none)

def exileOppDeathCreateWolf : StaticAbility :=
  .replacement none (.exileInsteadOfDying scopeOpponentsCreatures (some .wolf))

def tokenDoubling : StaticAbility :=
  .replacement none (.multiplyTokens .you 2)

def foodAlsoCreatesTreasure : StaticAbility :=
  .replacement none (.extraTokenWith .you (.hasSubtype (.literal .food)) .treasure 1)

def artifactTokensBecomeDragons : StaticAbility :=
  .replacement none (.replaceTokens .you (.hasType .artifact) .dragon55flying)

def drawTwoExceptFirstDrawStep : StaticAbility :=
  .replacement none (.extraDraw .you 2 true)

def extraDrawOnConnive : StaticAbility :=
  .replacement none (.extraDrawOnConnive .you scopeCreaturesYouControl 1)

def extraPlusOneCounter : StaticAbility :=
  .replacement none (.modifyCountersPut scopeCreaturesYouControl (some .plusOnePlusOne) none 1)

def extraCounterOnPermanents : StaticAbility :=
  .replacement none (.modifyCountersPut scopePermanentsYouControl none (some .you) 1)

def preventAllDamageToThis : StaticAbility :=
  .replacement none (.preventDamage .self none)

def noncombatDamagePlusOne : StaticAbility :=
  .replacement none
    (.modifyDamage scopePermanentsYouControl true recipientOppOrOppPermanent 1 (.const 1))

def noncombatDamagePlusSourcePower : StaticAbility :=
  .replacement none
    (.modifyDamage scopePermanentsYouControl true recipientOppOrOppPermanent 1 (.objectStat .power .this))

def equippedDealsDoubleDamage : StaticAbility :=
  .replacement none (.modifyDamage scopeEquippedCreature false .any 2 (.const 0))

def healOtherDamageWhenDealt : StaticAbility :=
  .replacement none (.healOtherDamageWhenDealt .self)

def unspentManaBecomesColorless : StaticAbility :=
  .replacement none (.unspentManaBecomesColorless .you)

-- Aura Enchant restrictions (CR 303.4a)

/-- `Enchant artifact or non-Aura enchantment` (CR 303.4a). -/
def enchantArtifactOrNonAuraEnchantment : StaticAbility :=
  .enchantRestriction {
    domain := .object .battlefield (.any #[
      .hasType .artifact,
      .all #[.not (.hasSubtype (.literal .aura)), .hasType .enchantment]
    ])
  }

/-- `Enchant creature you control` (CR 303.4a). -/
def enchantCreatureYouControl : StaticAbility :=
  .enchantRestriction {
    domain := .object .battlefield (.all #[.hasType .creature, .controlledBy .you])
  }

/-! ### 8. Structural Predicates & Projections -/

/-- True when `ab` is a power/toughness characteristic-defining ability (CR 604.3 / 707.9d). -/
def isPTDefiningCDA : StaticAbility → Bool
  | .characteristicDefining (.setPT _ _) => true
  | _ => false

/-- True when `ab` is unconditional self `"can't be blocked"` (CR 509.1b). -/
def isCantBeBlocked : StaticAbility → Bool
  | .ruleModifying none (.combat (.cantBeBlocked .self)) => true
  | _ => false

/-- Enchant target slot if `ab` is an Aura `enchantRestriction` (CR 303.4a). -/
def enchantRestriction? : StaticAbility → Option TargetSlot
  | .enchantRestriction slot => some slot
  | _ => none

/-- True when `ab` contains a `StaticReplacementSpec` matching `p`. -/
def anyReplacement (ab : StaticAbility) (p : Option Condition → StaticReplacementSpec → Bool) : Bool :=
  match ab with
  | .replacement cond? spec => spec.flatten.any (p cond?)
  | _ => false

/-- True when `ab` contains a `RuleModification` matching `p` (including inside
`ContinuousModification.applyRule`). -/
def anyRule (ab : StaticAbility) (p : Option Condition → RuleModification → Bool) : Bool :=
  match ab with
  | .ruleModifying cond? rule => rule.flatten.any (p cond?)
  | .continuous cond? _ mod =>
    mod.flatten.any fun
      | .applyRule r => r.flatten.any (p cond?)
      | _ => false
  | _ => false

/-- True when `scope` is the canonical self filter. -/
def isScopeSelf (sc : ObjectFilter) : Bool :=
  sc == scopeSelf

/-- True when `scope` is the canonical equipped-creature filter. -/
def isScopeEquippedCreature (sc : ObjectFilter) : Bool :=
  sc == scopeEquippedCreature

/-- True when `scope` is the canonical enchanted-creature filter. -/
def isScopeEnchantedCreature (sc : ObjectFilter) : Bool :=
  sc == scopeEnchantedCreature

/-- True when `scope` is the canonical enchanted-permanent filter. -/
def isScopeEnchantedPermanent (sc : ObjectFilter) : Bool :=
  sc == scopeEnchantedPermanent

/-- True when `scope` targets the attached host of an Aura or Equipment. -/
def isAttachedHostScope (sc : ObjectFilter) : Bool :=
  isScopeEquippedCreature sc || isScopeEnchantedCreature sc || isScopeEnchantedPermanent sc

/-! ### 9. Canonical `ToOracle` / `toNotation` Printer -/

private def unwrapScaled (v : ValueExpr) : Int × ValueExpr :=
  match v with
  | .binary .mul (.const k) inner => (k, inner)
  | other => (1, other)

private def renderConditionClause (ctx : PrintCtx) (c : Condition) : String :=
  if c == .isYourTurn then "during your turn"
  else if c == condEnduringStory then "you have an enduring story"
  else if c == condScriedOrSurveilledThisTurn then "you've scried or surveilled this turn"
  else if c == condCreatureDiedThisTurn then "a creature died this turn"
  else if c == condCastNoncreatureThisTurn then "you've cast a noncreature spell this turn"
  else if c == condOpponentCastSpellThisTurn then "an opponent has cast a spell this turn"
  else if c == condOpponentDealtNoncombatDamageThisTurn then
    "an opponent was dealt noncombat damage this turn"
  else if c == condControlLegendaryCreature then "you control a legendary creature"
  else if c == condControlPlaneswalker then "you control a planeswalker"
  else if c == condControlCommander then "you control a commander"
  else if c == condSelfHasCounter .shield then "this has a shield counter on it"
  else if c == (.forAll .this (.receivedCounterThisTurn (some .plusOnePlusOne) (some .you))) then
    "you've put one or more +1/+1 counters on this creature this turn"
  else if c == (.forAll .this (.not (.dealtDamageThisTurn true none false))) then
    "they haven't dealt combat damage yet"
  else if c == (.exists (.inZones .battlefield (.all #[
      .any #[.all #[.hasType .artifact, .hasType .creature], .hasSubtype (.literal .plan)],
      .controlledBy .you]))) then
    "you control an artifact creature or a Plan"
  else
    match c with
    | .cmp .ge (.playerMetric .graveyardSize .you) (.const n) =>
      s!"there are {englishNumber n.toNat} or more cards in your graveyard"
    | .cmp .ge (.aggregate .count .one (.inZones .yourGraveyard (.otherThan .this))) (.const n) =>
      s!"there are {englishNumber n.toNat} or more other cards in your graveyard"
    | .cmp .ge (.aggregate .count .one (.inZones .yourGraveyard (.all #[.isCard, .hasType .creature]))) (.const n) =>
      if n == 1 then "there is a creature card in your graveyard"
      else s!"there are {n.toNat} or more creature cards in your graveyard"
    | .exists (.inZones .battlefield (.all #[.otherThan .this, .hasSubtype (.literal sub), .controlledBy .you])) =>
      s!"you control another {sub}"
    | .exists (.inZones .battlefield (.all #[.hasSubtype (.literal sub), .controlledBy .you])) =>
      s!"you control {indefinite sub.englishName} {sub}"
    | .exists (.inZones .battlefield (.all #[.hasType .planeswalker, .hasSubtype (.literal sub), .controlledBy .you])) =>
      s!"you control {indefinite sub.englishName} {sub} planeswalker"
    | .exists (.inZones .battlefield (.all #[.hasType .land, .any ps, .controlledBy .you])) =>
      let subs := ps.toList.filterMap fun | .hasSubtype (.literal s) => some s | _ => none
      if subs.length == ps.size && !subs.isEmpty then
        let phr := String.intercalate " or " (subs.map fun s => s!"{indefinite s.englishName} {s}")
        s!"you control {phr}"
      else toOracleStr c { ctx with capitalize := false }
    | .exists (.inZones .battlefield (.all #[.any ps, .controlledBy .you])) =>
      let subs := ps.toList.filterMap fun | .hasSubtype (.literal s) => some s | _ => none
      if subs.length == ps.size && !subs.isEmpty then
        s!"you control a {String.intercalate " or " (subs.map CardSubtype.englishName)}"
      else toOracleStr c { ctx with capitalize := false }
    | .cmp .ge (.aggregate .count .one (.inZones .battlefield (.all #[.otherThan .this, .hasSubtype (.literal sub), .controlledBy .you]))) (.const n) =>
      s!"you control {englishNumber n.toNat} or more other {sub.pluralName}"
    | .cmp .ge (.aggregate .count .one (.inZones .battlefield (.all #[.otherThan .this, .hasType .land, .controlledBy .you]))) (.const n) =>
      s!"you control {englishNumber n.toNat} or more other lands"
    | .cmp .ge (.aggregate .count .one (.inZones .battlefield (.all #[.hasSupertype .basic, .hasType .land, .controlledBy .you]))) (.const n) =>
      s!"you control {englishNumber n.toNat} or more basic lands"
    | .cmp .ge (.aggregate .count .one (.inZones .battlefield (.all #[.hasType .land, .controlledBy .opponent]))) (.const n) =>
      s!"your opponents control {englishNumber n.toNat} or more lands"
    | .cmp .ge (.aggregate .sum (.counterCount (some .lore))
        (.inZones .battlefield (.all #[.hasSubtype (.literal .saga), .controlledBy .you]))) (.const n) =>
      s!"there are {englishNumber n.toNat} or more lore counters among Sagas you control"
    | .playerPred (.matching .opponent (.metric .poisonCounters .ge (.const n))) .any =>
      s!"an opponent has {englishNumber n.toNat} or more poison counters"
    | .forAll .this (.stat .power .le (.const n)) =>
      s!"its power is {n} or less"
    | .all #[.exists (.target 0), .forAll (.target 0) (.all #[.hasType .creature, pred])] =>
      match pred with
      | .wasDealtDamageThisTurn => "it targets a creature that was dealt damage this turn"
      | .tapped true => "it targets a tapped creature"
      | .all #[.combatRole .attacking, .isToken false] => "it targets an attacking nontoken creature"
      | .combatRole .attacking => "it targets an attacking creature"
      | _ =>
        let noun := toOracleStr pred { ctx with plural := false, capitalize := false }
        s!"it targets {indefinite noun} {noun}"
    | _ => toOracleStr c { ctx with capitalize := false }

private def renderCda (ctx : PrintCtx) : CdaSpec → String
  | .setPT (some p) (some t) =>
    if p == t then
      s!"This creature's power and toughness are each equal to {toOracleStr p { ctx with capitalize := false }}."
    else
      match p, t with
      | n, .binary .add n2 (.const 1) =>
        if n == n2 then
          s!"This creature's power is equal to {toOracleStr n { ctx with capitalize := false }} and its toughness is equal to that number plus 1."
        else
          s!"This creature's power is equal to {toOracleStr p { ctx with capitalize := false }} and its toughness is equal to {toOracleStr t { ctx with capitalize := false }}."
      | _, _ =>
        s!"This creature's power is equal to {toOracleStr p { ctx with capitalize := false }} and its toughness is equal to {toOracleStr t { ctx with capitalize := false }}."
  | .setPT (some p) none =>
    match p with
    | .playerMetric .handSize .you => "This power is equal to the number of cards in your hand."
    | .aggregate .count .one (.inZones .battlefield (.all #[.hasType .creature, .controlledBy .you])) =>
      "This power is equal to the number of creatures you control."
    | .aggregate .count .one (.inZones .battlefield (.all #[.hasSubtype (.literal sub), .controlledBy .you])) =>
      s!"This creature's power is equal to the number of {sub.pluralName} you control."
    | .aggregate .count .one (.inZones .battlefield (.all #[.hasSupertype .legendary, .hasType .creature, .controlledBy .you])) =>
      "This creature's power is equal to the number of legendary creatures you control."
    | .basicLandTypeCount (.inZones .battlefield (.all #[.hasType .land, .controlledBy .you])) =>
      "This creature's power is equal to the number of basic land types among lands you control."
    | _ =>
      s!"This creature's power is equal to {toOracleStr p { ctx with capitalize := false }}."
  | .setPT none (some t) =>
    s!"This creature's toughness is equal to {toOracleStr t { ctx with capitalize := false }}."
  | .setPT none none => ""
  | .setTypes m =>
    let subStr := String.intercalate " " (m.subtypes.toList.map CardSubtype.englishName)
    let typStr := String.intercalate " " (m.types.toList.map CardType.oracleWord)
    let combined := String.intercalate " " ([subStr, typStr].filter (!·.isEmpty))
    s!"This card is {indefinite combined} {combined}."
  | .allCreatureTypes => "This card is every creature type."
  | .setColors cs =>
    if cs.isColorless then "This card is colorless."
    else
      let names := Color.all.filter cs.contains |>.map Color.englishName
      s!"This card is {String.intercalate " and " names}."

private def renderSubjectPhrase (ctx : PrintCtx) (subj : StaticSubject) (pluralDefault : Bool := false) :
    String × Bool :=
  match subj with
  | .self => ("This creature", false)
  | .matching f =>
    if f == scopeEnchantedCreature then ("Enchanted creature", false)
    else if f == scopeEquippedCreature then ("Equipped creature", false)
    else if f == scopeEnchantedPermanent then ("Enchanted permanent", false)
    else
      (toOracleStr f { ctx with plural := pluralDefault, capitalize := true }, pluralDefault)

private def renderScopeSubject (ctx : PrintCtx) (sc : ObjectFilter) : String × Bool :=
  if sc == scopeSelf then ("this creature", false)
  else if sc == scopeEquippedCreature then ("equipped creature", false)
  else if sc == scopeEnchantedCreature then ("enchanted creature", false)
  else if sc == scopeEnchantedPermanent then ("enchanted permanent", false)
  else if sc == scopeCreaturesYouControl then ("creatures you control", true)
  else if sc == scopeOtherCreaturesYouControl then ("other creatures you control", true)
  else if sc == scopeOpponentsCreatures then ("creatures your opponents control", true)
  else if sc == scopeLandsYouControl then ("lands you control", true)
  else if sc == scopePlaneswalkersYouControl then ("planeswalkers you control", true)
  else if sc == scopePermanentsYouControl then ("permanents you control", true)
  else if sc == scopeInstantSorcerySpellsYouControl then ("instant and sorcery spells you control", true)
  else if sc == scopeNoncreatureSpellsYouControl then ("noncreature spells you cast", true)
  else
    match sc.zones.zones.toList, sc.pred with
    | [.battlefield], .all #[.otherThan .this, .hasType .creature, .hasSubtype (.literal s), .controlledBy .you] =>
      (s!"other {s} creatures you control", true)
    | [.battlefield], .all #[.otherThan .this, .hasType .creature, .any ps, .controlledBy .you] =>
      let subs := ps.toList.filterMap fun | .hasSubtype (.literal s) => some s | _ => none
      if subs.length == ps.size && !subs.isEmpty then
        (s!"other {joinedSubtypes subs.toArray} creatures you control", true)
      else (toOracleStr sc { ctx with plural := true, capitalize := false }, true)
    | [.battlefield], .all #[.otherThan .this, .hasSubtype (.literal s), .controlledBy .you] =>
      (s!"other {s.pluralName} you control", true)
    | [.battlefield], .all #[.otherThan .this, .any ps, .controlledBy .you] =>
      let subs := ps.toList.filterMap fun | .hasSubtype (.literal s) => some s | _ => none
      if subs.length == ps.size && !subs.isEmpty then
        (s!"other {joinedSubtypes subs.toArray CardSubtype.pluralName} you control", true)
      else (toOracleStr sc { ctx with plural := true, capitalize := false }, true)
    | [.battlefield], .all #[.hasType .creature, .hasSubtype (.literal s), .controlledBy .you] =>
      (s!"{s.pluralName} you control", true)
    | [.battlefield], .all #[.hasSubtype (.literal s), .controlledBy .you] =>
      (s!"{s.pluralName} you control", true)
    | [.battlefield], .all #[.hasType .creature, .hasSubtype .chosenOnSource, .controlledBy .you] =>
      ("creatures you control of the chosen type", true)
    | [.battlefield], .all #[.hasSupertype .legendary, .hasType .creature, .controlledBy .you] =>
      ("legendary creatures you control", true)
    | [.battlefield], .all #[.not (.hasSupertype .legendary), .hasType .creature, .controlledBy .you] =>
      ("nonlegendary creatures you control", true)
    | [.battlefield], .all #[.hasType .artifact, .hasType .creature, .controlledBy .you] =>
      ("artifact creatures you control", true)
    | [.battlefield], .all #[.any #[.hasType .artifact, .hasType .creature], .controlledBy .you] =>
      ("artifacts and creatures you control", true)
    | [.battlefield], .all #[.hasType .creature, .isToken true, .controlledBy .you] =>
      ("creature tokens you control", true)
    | [.battlefield], .all #[.combatRole .attacking, .hasType .creature, .isToken true, .controlledBy .you] =>
      ("attacking creature tokens you control", true)
    | [.battlefield], .all #[.hasType .creature, .controlledBy .you, .counterCount (some .plusOnePlusOne) .ge (.const 1)] =>
      ("each creature you control with a +1/+1 counter on it", false)
    | [.battlefield], .all #[.otherThan .this, .hasType .creature, .controlledBy .you, .counterCount (some .plusOnePlusOne) .ge (.const 1)] =>
      ("each other creature you control with a +1/+1 counter on it", false)
    | [.battlefield], .all #[.hasType .creature, .controlledBy .you, .receivedCounterThisTurn (some .plusOnePlusOne) (some .you)] =>
      ("each creature you control that you've put one or more +1/+1 counters on this turn", false)
    | [.battlefield], .all #[.hasType .creature, .controlledBy .you, .hasKeyword .toxic] =>
      ("creatures you control with toxic", true)
    | [.battlefield], .all #[.hasType .creature, .controlledBy .you, .hasAttachment { zones := { zones := #[.battlefield], owner := .any }, pred := .hasSubtype (.literal .equipment) }] =>
      ("creatures you control that are equipped", true)
    | _, _ => (toOracleStr sc { ctx with plural := true, capitalize := false }, true)

private def renderDynamicModifyPT (ctx : PrintCtx) (verb : String) (p t : ValueExpr) : String :=
  match p, t with
  | .const pv, .const tv => s!"{verb} {signedStat pv}/{signedStat tv}"
  | .playerMetric .unspentMana .you, .playerMetric .unspentMana .you =>
    s!"{verb} +1/+1 for each unspent mana you have"
  | .binary .mul (.const 2) (.binary .divFloor (.playerMetric .graveyardSize .you) (.const 7)), .const 0 =>
    s!"{verb} +2/+0 for every seven cards in your graveyard"
  | pExpr, .const 0 =>
    let (k, inner) := unwrapScaled pExpr
    let perPhrase :=
      match inner with
      | .aggregate .count .one (.inZones .battlefield (.all #[.hasSubtype (.literal .mountain), .controlledBy .you])) =>
        "each Mountain you control"
      | .aggregate .count .one (.inZones .battlefield (.all #[.otherThan .this, .hasType .artifact, .controlledBy .you])) =>
        "each other artifact you control"
      | .aggregate .count .one (.inZones .battlefield (.all #[.hasSubtype (.literal .equipment), .attachedTo .this])) =>
        "each Equipment attached to it"
      | .aggregate .count .one (.inZones .battlefield (.all #[.hasType .artifact, .isToken true, .controlledBy .you])) =>
        "each artifact token you control"
      | .aggregate .count .one (.inZones .yourGraveyard (.all #[.isCard, .any #[.hasType .instant, .hasType .sorcery]])) =>
        "each instant and sorcery card in your graveyard"
      | .aggregate .count .one (.inZones .yourGraveyard (.all #[.isCard, .any #[.hasType .creature, .hasType .planeswalker]])) =>
        "each creature and planeswalker card in your graveyard"
      | .playerMetric .one (.matching .anyPlayer (.metric .graveyardSize .ge (.const 7))) =>
        "each graveyard with seven or more cards in it"
      | other => toOracleStr other { ctx with capitalize := false }
    s!"{verb} {signedStat k}/+0 for {perPhrase}"
  | pExpr, tExpr =>
    if pExpr == tExpr then
      s!"{verb} +X/+X, where X is {toOracleStr pExpr { ctx with capitalize := false }}"
    else
      s!"{verb} +{toOracleStr pExpr { ctx with capitalize := false }}/+{toOracleStr tExpr { ctx with capitalize := false }}"

private def renderKeywordsAndWards (ks : Array KeywordAbility) : String :=
  if ks.size == 2 && KeywordAbility.hasFirstStrike ks && KeywordAbility.hasVigilance ks then
    "first strike and vigilance"
  else
    let nonWards := ks.filter fun | .ward _ => false | _ => true
    let wards := ks.filter fun | .ward _ => true | _ => false
    if wards.isEmpty then KeywordAbility.joinedAnd ks
    else if nonWards.isEmpty then KeywordAbility.joinedAnd wards
    else s!"{KeywordAbility.joinedAnd nonWards} and {KeywordAbility.joinedAnd wards}"

private def renderRuleMod (ctx : PrintCtx) (cond? : Option Condition) (rule : RuleModification) : String :=
  let flat := rule.flatten
  -- Special compound rules
  let special? : Option String :=
    if flat == #[.player (.cantLoseGame .you), .player (.cantWinGame .opponent)] then
      some "You can't lose the game and your opponents can't win the game."
    else if flat.size == 2 then
      match flat[0]!, flat[1]! with
      | .combat (.cantAttackPlayer (.all #[.hasType .creature, .hasKeyword .flying]) .you),
        .combat (.cantBlockMatching (.all #[.hasType .creature, .hasKeyword .flying])
          (.all #[.hasType .creature, .controlledBy .you])) =>
        some "Creatures with flying can't attack you or block creatures you control."
      | .combat (.cantAttack s1), .combat (.cantBlock s2 none) =>
        if s1 == s2 then
          let (subj, _) := renderSubjectPhrase ctx s1
          some s!"{subj} can't attack or block."
        else none
      | _, _ => none
    else none
  let body :=
    match special? with
    | some s => s
    | none =>
      let renderOne : RuleModification → String
        | .player (.maxHandSize _ none) => "You have no maximum hand size."
        | .player (.maxHandSize _ (some n)) => s!"Your maximum hand size is {n}."
        | .player (.additionalLands _ n) =>
          let cnt := if n == 1 then "an additional land" else s!"{englishNumber n} additional lands"
          s!"You may play {cnt} on each of your turns."
        | .player (.cantGainLife { relation := .opponent, pred := .any }) =>
          "Your opponents can't gain life."
        | .player (.cantGainLife pf) =>
          s!"{toOracleStr pf { ctx with plural := true, capitalize := true }} can't gain life."
        | .player (.cantLoseGame { relation := .you, pred := .any }) => "You can't lose the game."
        | .player (.cantLoseGame pf) =>
          s!"{toOracleStr pf { ctx with capitalize := true }} can't lose the game."
        | .player (.cantWinGame { relation := .opponent, pred := .any }) =>
          "Your opponents can't win the game."
        | .player (.cantWinGame pf) =>
          s!"{toOracleStr pf { ctx with plural := true, capitalize := true }} can't win the game."
        | .player (.hexproof { relation := .you, pred := .any } none) => "You have hexproof."
        | .player (.hexproof pf none) =>
          s!"{toOracleStr pf { ctx with capitalize := true }} have hexproof."
        | .player (.hexproof pf (some q)) =>
          s!"{toOracleStr pf { ctx with capitalize := true }} have hexproof from {toOracleStr q { ctx with capitalize := false }}."
        | .player (.protectionFrom { relation := .you, pred := .any } q) =>
          s!"You have protection from {toOracleStr q { ctx with capitalize := false }}."
        | .player (.protectionFrom pf q) =>
          s!"{toOracleStr pf { ctx with capitalize := true }} have protection from {toOracleStr q { ctx with capitalize := false }}."
        | .player (.cantCastSpells { relation := .opponent, pred := .any } (.all #[])) =>
          "Your opponents can't cast spells."
        | .player (.cantCastSpells { relation := .anyPlayer, pred := .any } (.named .chosenOnSource)) =>
          "Spells with the chosen name can't be cast."
        | .player (.cantCastSpells pf pred) =>
          let sp := if pred == .anyObject then "spells" else toOracleStr pred { ctx with plural := true, capitalize := false }
          s!"{toOracleStr pf { ctx with plural := true, capitalize := true }} can't cast {sp}."
        | .player (.activateAsThoughHaste _ sc) =>
          let (subj, _) := renderScopeSubject ctx sc
          s!"You may activate abilities of {subj} as though those creatures had haste."
        | .player (.extraAbilityActivation .powerUp sc 1) =>
          let (subj, _) := renderScopeSubject ctx sc
          s!"Each power-up ability of {subj} can be activated an additional time."
        | .player (.extraAbilityActivation _ sc n) =>
          let (subj, _) := renderScopeSubject ctx sc
          s!"Activated abilities of {subj} can be activated {englishNumber n} additional time(s)."
        | .player (.lifeTotalCantChange pf) =>
          s!"{toOracleStr pf { ctx with capitalize := true }}'s life total can't change."
        | .player (.forbidAbilityActivation _ .powerUp) =>
          "Power-up abilities can't be activated."
        | .player (.forbidAbilityActivation _ _) =>
          "Abilities can't be activated."
        | .player (.gainDesignation _ .citysBlessing) =>
          "You get the city's blessing for the rest of the game."
        | .player (.gainDesignation _ .enduringStory) =>
          "You get an enduring story for the rest of the game."
        | .player (.controlPlayer who) =>
          s!"You control {toOracleStr who { ctx with capitalize := false }}."
        | .play (.lookAtTopOfLibrary _) =>
          "You may look at the top card of your library any time."
        | .play (.mayPlayFrom _ .library (.hasType .creature) false false false false) =>
          "You may cast creature spells from the top of your library."
        | .play (.mayPlayFrom _ .library (.hasType .land) true false false false) =>
          "You may play lands from the top of your library."
        | .play (.mayPlayFrom _ .graveyard (.hasType .land) true false false false) =>
          "You may play lands from your graveyard."
        | .play (.mayPlayFrom _ .exile _ false true true false) =>
          "You may cast the exiled card, and mana of any type can be spent to cast that spell."
        | .play (.mayPlayFrom _ .hand (.stat .manaValue .le (.aggregate .count .one (.inZones .battlefield (.all #[.hasType .creature, .controlledBy .you])))) false false false true) =>
          "You may cast spells with mana value less than or equal to the number of creatures you control from your hand without paying their mana costs."
        | .play (.mayPlayFrom _ z pred lands _ anyC free) =>
          let verb := if lands then "play" else "cast"
          let what := if pred == .anyObject then (if lands then "lands" else "spells")
                      else toOracleStr pred { ctx with plural := true, capitalize := false }
          let fromS := match z with
            | .library => "the top of your library"
            | .graveyard => "your graveyard"
            | .hand => "your hand"
            | .exile => "exile"
            | _ => z.englishName
          let freeS := if free then " without paying their mana costs" else ""
          let anyS := if anyC then ", and mana of any type can be spent to cast them" else ""
          s!"You may {verb} {what} from {fromS}{freeS}{anyS}."
        | .play (.castAsThoughFlash _ _ true _) =>
          "You may cast this spell as though it had flash."
        | .play (.castAsThoughFlash _ (.hasType .creature) false (some 1)) =>
          "The first creature spell you cast each turn can be cast as though it had flash."
        | .play (.castAsThoughFlash _ (.all #[]) false none) =>
          "You may cast spells as though they had flash."
        | .play (.castAsThoughFlash _ pred false _) =>
          s!"You may cast {toOracleStr pred { ctx with plural := true, capitalize := false }} spells as though they had flash."
        | .play (.spellCantBeCountered none) => "This spell can't be countered."
        | .play (.spellCantBeCountered (some pred)) =>
          s!"{toOracleStr pred { ctx with plural := true, capitalize := true }} spells can't be countered."
        | .play (.nextSpellCantBeCountered _ _) =>
          "The next spell you cast can't be countered."
        | .play (.castRestriction c) =>
          s!"You can't cast this spell unless {renderConditionClause ctx c}."
        | .play .mayBeginOnBattlefield =>
          "If this card is in your opening hand, you may begin the game with it on the battlefield."
        | .play .canBeCommander =>
          "This planeswalker can be your commander."
        | .play (.activateLoyaltyAsInstant _ _) =>
          "You may activate loyalty abilities of planeswalkers you control on any player's turn any time you could cast an instant."
        | .combat (.cantAttack s) =>
          let (subj, _) := renderSubjectPhrase ctx s
          s!"{subj} can't attack."
        | .combat (.cantAttackUnless s c) =>
          let (subj, _) := renderSubjectPhrase ctx s
          s!"{subj} can't attack unless {renderConditionClause ctx c}."
        | .combat (.attackTax _ _ cost) =>
          s!"Creatures can't attack you unless their controller pays {cost.toNotation} for each of those creatures."
        | .combat (.attackPlaneswalkerTax _ _ cost) =>
          s!"Creatures can't attack planeswalkers you control unless their controller pays {cost.toNotation} for each of those creatures."
        | .combat (.cantAttackPlayer ap _ _) =>
          s!"{toOracleStr ap { ctx with plural := true, capitalize := true }} can't attack you."
        | .combat (.attacksEachCombatIfAble s) =>
          let (subj, pl) := renderSubjectPhrase ctx s
          s!"{subj} {if pl then "attack" else "attacks"} each combat if able."
        | .combat (.attackDespiteDefender .self) =>
          "This creature can attack as though it didn't have defender."
        | .combat (.attackDespiteDefender (.matching sc)) =>
          let (subj, _) := renderScopeSubject ctx sc
          s!"{capitalizeAscii subj} can attack as though they didn't have defender."
        | .combat (.maxAttackersPerPermanent .self n) =>
          let word := if n == 1 then "one creature" else s!"{englishNumber n} creatures"
          s!"No more than {word} can attack this planeswalker each combat."
        | .combat (.maxAttackersPerPermanent (.matching sc) n) =>
          let (subj, _) := renderScopeSubject ctx sc
          let word := if n == 1 then "one creature" else s!"{englishNumber n} creatures"
          s!"No more than {word} can attack {subj} each combat."
        | .combat (.cantBlock s none) =>
          let (subj, _) := renderSubjectPhrase ctx s
          s!"{subj} can't block."
        | .combat (.cantBlock s (some c)) =>
          let (subj, _) := renderSubjectPhrase ctx s
          s!"{subj} can't block unless {renderConditionClause ctx c}."
        | .combat (.cantBlockMatching bp ap) =>
          s!"{toOracleStr bp { ctx with plural := true, capitalize := true }} can't block {toOracleStr ap { ctx with plural := true, capitalize := false }}."
        | .combat (.cantBeBlocked .self) =>
          "This creature can't be blocked."
        | .combat (.cantBeBlocked (.matching sc)) =>
          s!"{toOracleStr sc { ctx with plural := true, capitalize := true }} can't be blocked."
        | .combat (.cantBeBlockedBy s (.isToken true)) =>
          let (subj, _) := renderSubjectPhrase ctx s
          s!"{subj} can't be blocked by tokens."
        | .combat (.cantBeBlockedBy s bp) =>
          let (subj, _) := renderSubjectPhrase ctx s
          s!"{subj} can't be blocked by {toOracleStr bp { ctx with plural := true, capitalize := false }}."
        | .combat (.minBlockers s n) =>
          let (subj, _) := renderSubjectPhrase ctx s
          s!"{subj} can't be blocked except by {englishNumber n} or more creatures."
        | .combat (.maxBlockers s n) =>
          let (subj, _) := renderSubjectPhrase ctx s
          s!"{subj} can't be blocked by more than {englishNumber n} creature(s)."
        | .combat (.assignCombatDamageByToughness sc true) =>
          let (subj, _) := renderScopeSubject ctx sc
          let head := if subj == "creatures you control" then "Each creature you control" else capitalizeAscii subj
          s!"{head} with toughness greater than its power assigns combat damage equal to its toughness rather than its power."
        | .combat (.assignCombatDamageByToughness sc false) =>
          let (subj, _) := renderScopeSubject ctx sc
          s!"{capitalizeAscii subj} assign combat damage equal to their toughness rather than their power."
        | .combat (.assignNegativePowerAsPositive _) =>
          "If this creature's power is negative, it assigns combat damage as though its power were positive."
        | .trigger (.extraTrigger sc _) =>
          if sc == scopeEquippedCreature then
            "If a triggered ability of equipped creature triggers, that ability triggers an additional time."
          else
            match sc.pred with
            | .all #[.hasSubtype (.literal sub), .controlledBy .you] =>
              s!"If a triggered ability of {indefinite sub.englishName} {sub} you control triggers, that ability triggers an additional time."
            | .all #[.otherThan .this, .any ps, .controlledBy .you] =>
              let parts := ps.toList.filterMap fun
                | .hasSubtype (.literal s) => some s.englishName
                | .hasType t => some t.oracleWord
                | _ => none
              let joined :=
                match parts with
                | [a] => a
                | [a, b] => s!"{a} or {b}"
                | xs => String.intercalate ", " xs
              s!"If a triggered ability of another {joined} you control triggers, that ability triggers an additional time."
            | _ =>
              let noun := toOracleStr sc { ctx with plural := false, capitalize := false }
              s!"If a triggered ability of {noun} triggers, that ability triggers an additional time."
        | .trigger (.suppressEnteringTriggers sc) =>
          let predStr :=
            if sc.pred == .any #[.hasType .artifact, .hasType .creature] then
              "Artifacts and creatures"
            else toOracleStr sc { ctx with plural := true, capitalize := true }
          s!"{predStr} entering the battlefield don't cause abilities to trigger."
        | .game (.doesntUntapDuringUntapStep s none) =>
          let (subj, pl) := renderSubjectPhrase ctx s
          let verb := if pl then "don't" else "doesn't"
          let poss := if s == .self then "your" else "its controller's"
          s!"{subj} {verb} untap during {poss} untap step."
        | .game (.doesntUntapDuringUntapStep s (some c)) =>
          let (subj, pl) := renderSubjectPhrase ctx s
          let verb := if pl then "don't" else "doesn't"
          s!"{subj} {verb} untap during your untap step unless {renderConditionClause ctx c}."
        | .game (.cantBecomeUntapped s) =>
          let (subj, _) := renderSubjectPhrase ctx s
          s!"{subj} can't become untapped."
        | .game (.lockNonManaDuringPhase ph _) =>
          s!"During {ph.englishName}, players can't cast spells or activate abilities that aren't mana abilities."
        | .game (.planeswalkersSurviveZeroLoyalty sc) =>
          let (subj, _) := renderScopeSubject ctx sc
          s!"{capitalizeAscii subj} aren't put into their owners' graveyards for having 0 loyalty."
        | .game (.cantHaveCountersPutOn sc (some k)) =>
          let (subj, _) := renderScopeSubject ctx sc
          s!"{capitalizeAscii subj} can't have {k.oracleName} counters put on them."
        | .game (.cantHaveCountersPutOn sc none) =>
          let (subj, _) := renderScopeSubject ctx sc
          s!"{capitalizeAscii subj} can't have counters put on them."
        | .game (.legendRuleDisabled _) =>
          "The \"legend rule\" doesn't apply to permanents you control."
        | .costMod _ _ _ =>
          "Spells and abilities cost different mana."
        | .all _ => ""
      String.intercalate " " (flat.toList.map renderOne)
  match cond? with
  | none => body
  | some .isYourTurn =>
    if body == "Your opponents can't cast spells." then
      "Your opponents can't cast spells during your turn."
    else
      let lowBody := match body.toList with
        | [] => ""
        | c :: cs => String.ofList (c.toLower :: cs)
      s!"During your turn, {lowBody}"
  | some c =>
    match rule with
    | .play (.castAsThoughFlash _ _ true _) =>
      s!"You may cast this spell as though it had flash if {renderConditionClause ctx c}."
    | .combat (.cantBeBlocked .self) =>
      match c with
      | .forAll .this (.stat .power .le (.const n)) =>
        s!"This creature can't be blocked if its power is {n} or less."
      | _ =>
        let lowBody := match body.toList with
          | [] => ""
          | ch :: cs => String.ofList (ch.toLower :: cs)
        s!"As long as {renderConditionClause ctx c}, {lowBody}"
    | _ =>
      let lowBody := match body.toList with
        | [] => ""
        | ch :: cs => String.ofList (ch.toLower :: cs)
      s!"As long as {renderConditionClause ctx c}, {lowBody}"

private def renderCostMod (ctx : PrintCtx) (cond? : Option Condition) (tgt : CostTargetSpec)
    (mod : CostModification) : String :=
  match tgt, mod with
  | .thisSpell, .alternativeFree =>
    match cond? with
    | some c => s!"If {renderConditionClause ctx c}, you may cast this spell without paying its mana cost."
    | none => "You may cast this spell without paying its mana cost."
  | .thisSpell, .reduceGeneric amt =>
    let (amtSym, whereClause) :=
      match amt with
      | .const n => (s!"\{{n.toNat}}", "")
      | _ => ("{X}", s!", where X is {toOracleStr amt { ctx with capitalize := false }}")
    let condClause :=
      match cond? with
      | none => ""
      | some c => s!" if {renderConditionClause ctx c}"
    s!"This spell costs {amtSym} less to cast{condClause}{whereClause}."
  | .thisSpell, .increaseGeneric amt =>
    let amtSym := match amt with | .const n => s!"\{{n.toNat}}" | _ => "{X}"
    s!"This spell costs {amtSym} more to cast."
  | .spells caster pred nth? notFrom? az, mod =>
    let dir := match mod with
      | .reduceGeneric _ => "less"
      | .increaseGeneric _ => "more"
      | .alternativeFree => "free"
    let (amtSym, whereClause) :=
      match mod with
      | .reduceGeneric (.const n) | .increaseGeneric (.const n) => (s!"\{{n.toNat}}", "")
      | .reduceGeneric (.objectStat .power .attachedHost) =>
        ("{X}", ", where X is equipped creature's power")
      | .reduceGeneric (.objectStat .power .this) =>
        ("{X}", ", where X is this creature's power")
      | .reduceGeneric v | .increaseGeneric v =>
        ("{X}", s!", where X is {toOracleStr v { ctx with capitalize := false }}")
      | .alternativeFree => ("{0}", "")
    let whoS :=
      match caster with
      | { relation := .you, pred := .any } => "you cast"
      | { relation := .opponent, pred := .any } => "your opponents cast"
      | pf => s!"{toOracleStr pf { ctx with capitalize := false }} casts"
    let isEminence := az.contains .command
    let (subj, isSing) :=
      match nth?, notFrom?, pred with
      | some 1, none, .hasType .creature => (s!"The first creature spell {whoS} each turn", true)
      | none, some .hand, .all #[] => (s!"Spells {whoS} from anywhere other than your hand", false)
      | none, none, .all #[.otherThan .this, .hasSubtype (.literal s)] =>
        (s!"Other {s} spells {whoS}", false)
      | none, none, .hasSubtype (.literal s) => (s!"{s} spells {whoS}", false)
      | none, none, .hasType t => (s!"{t} spells {whoS}", false)
      | none, none, .hasSupertype s => (s!"{s} spells {whoS}", false)
      | none, none, .not (.hasType .creature) => (s!"Noncreature spells {whoS}", false)
      | none, none, .any #[.hasType .instant, .hasType .sorcery] =>
        (s!"Instant and sorcery spells {whoS}", false)
      | none, none, .all #[.any #[.hasType .instant, .hasType .sorcery], .stat .manaValue .ge (.const n)] =>
        (s!"Instant and sorcery spells {whoS} with mana value {n} or greater", false)
      | _, _, _ =>
        let pS := toOracleStr pred { ctx with plural := false, capitalize := true }
        (s!"{pS} spells {whoS}", false)
    let verb := if isSing then "costs" else "cost"
    let eminPrefix := if isEminence then "Eminence — " else ""
    let eminSuffix :=
      if isEminence then " as long as this creature is in the command zone or on the battlefield"
      else ""
    s!"{eminPrefix}{subj} {verb} {amtSym} {dir} to cast{whereClause}{eminSuffix}."
  | .abilities _ tag? sc tgt? nth?, mod =>
    match tag?, tgt?, nth?, mod with
    | some (.equip _), some (.sameAs .this), none, .reduceGeneric (.const n) =>
      s!"Equip abilities you activate that target this creature cost \{{n.toNat}} less to activate."
    | some (.equip _), none, some 1, .alternativeFree =>
      let prefixS := match cond? with
        | some c => s!"As long as {renderConditionClause ctx c}, "
        | none => ""
      s!"{prefixS}you may pay \{0} rather than pay the equip cost of the first equip ability you activate each turn."
    | some .powerUp, none, none, .reduceGeneric (.const n) =>
      let (scS, _) := renderScopeSubject ctx sc
      s!"Power-up abilities of {scS} cost \{{n.toNat}} less to activate."
    | _, _, _, .reduceGeneric (.const n) =>
      let (scS, _) := renderScopeSubject ctx sc
      s!"Activated abilities of {scS} cost \{{n.toNat}} less to activate."
    | _, _, _, .increaseGeneric (.const n) =>
      let (scS, _) := renderScopeSubject ctx sc
      s!"Activated abilities of {scS} cost \{{n.toNat}} more to activate."
    | _, _, _, _ => "Activated abilities cost different mana to activate."

private def renderReplacementOne (ctx : PrintCtx) : StaticReplacementSpec → String
  | .entersTapped .self none => "This permanent enters tapped."
  | .entersTapped .self (some c) => s!"This permanent enters tapped unless {renderConditionClause ctx c}."
  | .entersTapped (.matching sc) none =>
    s!"{toOracleStr sc { ctx with plural := true, capitalize := true }} enter tapped."
  | .entersTapped (.matching sc) (some c) =>
    s!"{toOracleStr sc { ctx with plural := true, capitalize := true }} enter tapped unless {renderConditionClause ctx c}."
  | .entersTappedUnlessPay cost =>
    match cost.items.toList with
    | [.payLife (.const n)] =>
      s!"As this land enters, you may pay {n.toNat} life. If you don't, it enters tapped."
    | [.behold sub] =>
      s!"As this land enters, you may behold {indefinite sub.englishName} {sub}. If you don't, this land enters tapped."
    | _ =>
      s!"As this permanent enters, you may pay {cost.toNotation}. If you don't, it enters tapped."
  | .entersWithCounters .self .plusOnePlusOne .chosenX false =>
    "This enters with X +1/+1 counters on it."
  | .entersWithCounters .self .hope (.aggregate .count .one (.inZones .battlefield (.all #[.hasType .creature, .controlledBy .you]))) false =>
    "This enchantment enters with a hope counter on it for each creature you control."
  | .entersWithCounters .self k (.const n) false =>
    let kPhrase := k.countersPhrase n.toNat
    s!"This permanent enters with {kPhrase} on it."
  | .entersWithCounters .self k amt add =>
    let addS := if add then "additional " else ""
    s!"This permanent enters with {addS}{k.countersPhrase 1} on it for each {toOracleStr amt { ctx with capitalize := false }}."
  | .entersWithCounters (.matching sc) .plusOnePlusOne (.objectStat .toughness .this) true =>
    let (subj, _) := renderScopeSubject ctx sc
    s!"{capitalizeAscii subj} enter with a number of additional +1/+1 counters on them equal to this creature's toughness."
  | .entersWithCounters (.matching sc) k amt add =>
    let (subj, _) := renderScopeSubject ctx sc
    let addS := if add then "additional " else ""
    s!"{capitalizeAscii subj} enter with {toOracleStr amt { ctx with capitalize := false }} {addS}{k.oracleName} counters on them."
  | .entersWithDesignation .prepared => "This creature enters prepared."
  | .entersWithDesignation _ => "This permanent enters with a designation."
  | .asEntersChoose .color => "As this land enters, choose a color."
  | .asEntersChoose .creatureType => "As this enchantment enters, choose a creature type."
  | .asEntersChoose .cardType => "As this creature enters, choose a card type."
  | .asEntersChoose .nonlandCardName => "As this creature enters, choose a nonland card name."
  | .asEntersChoose .oddOrEven => "As this permanent enters, choose odd or even."
  | .asEntersChoose (.namedAnchors opts) =>
    s!"As this enchantment enters, choose {String.intercalate " or " opts.toList}."
  | .asEntersMayCopy _ .untilEndOfTurn mods =>
    let hasHaste := mods.any fun
      | .addKeywords ks => KeywordAbility.hasHaste ks
      | _ => false
    if hasHaste then
      "As this artifact enters, you may have it become a copy of any creature on the battlefield until end of turn, except it has haste."
    else
      "As this permanent enters, you may have it become a copy of any creature on the battlefield until end of turn."
  | .asEntersMayCopy f _ _ =>
    s!"As this permanent enters, you may have it become a copy of {toOracleStr f { ctx with plural := false, capitalize := false }}."
  | .exileInsteadOfDying sc none =>
    s!"If {indefinite (toOracleStr sc { ctx with plural := false, capitalize := false })} {toOracleStr sc { ctx with plural := false, capitalize := false }} would die, exile it instead."
  | .exileInsteadOfDying sc (some tok) =>
    let noun := toOracleStr sc { ctx with plural := false, capitalize := false }
    s!"If {indefinite noun} {noun} would die, exile it instead. When you do, {TokenSpec.createPhrase tok 1}."
  | .multiplyTokens _ 2 =>
    "If one or more tokens would be created under your control, twice that many of those tokens are created instead."
  | .multiplyTokens _ n =>
    s!"If one or more tokens would be created under your control, {timesPhrase n} that many of those tokens are created instead."
  | .extraTokenWith _ (.hasSubtype (.literal .food)) (.predefined .treasure) 1 =>
    "If you would create a Food token, create a Treasure token in addition."
  | .extraTokenWith _ pred tok n =>
    s!"If you would create a {toOracleStr pred { ctx with plural := false, capitalize := false }} token, also {TokenSpec.createPhrase tok n}."
  | .replaceTokens _ (.hasType .artifact) tok =>
    s!"If one or more artifact tokens would be created under your control, that many {tok.pluralNoun} are created instead."
  | .replaceTokens _ pred tok =>
    s!"If one or more {toOracleStr pred { ctx with plural := false, capitalize := false }} tokens would be created under your control, that many {tok.pluralNoun} are created instead."
  | .extraDraw _ 2 true =>
    "If you would draw a card except the first one you draw in each of your draw steps, draw two cards instead."
  | .extraDraw _ n _ =>
    s!"If you would draw a card, draw {englishNumber n} cards instead."
  | .extraDrawOnConnive _ _ _ =>
    "If a creature you control would connive, instead you draw a card, then that creature connives."
  | .modifyCountersPut _ (some .plusOnePlusOne) none 1 =>
    "If one or more +1/+1 counters would be put on a creature you control, that many plus one +1/+1 counters are put on it instead."
  | .modifyCountersPut _ none (some { relation := .you, pred := .any }) 1 =>
    "If you would put one or more counters on a permanent you control, put that many plus one of each of those kinds of counters on that permanent instead."
  | .modifyCountersPut sc k? _ n =>
    let kS := match k? with | some k => s!"{k.oracleName} " | none => ""
    s!"If one or more {kS}counters would be put on {toOracleStr sc { ctx with plural := false, capitalize := false }}, put that many plus {englishNumber n} instead."
  | .preventDamage .self none => "Prevent all damage that would be dealt to this."
  | .preventDamage .self (some v) =>
    s!"Prevent {toOracleStr v { ctx with capitalize := false }} of the damage that would be dealt to this."
  | .preventDamage (.matching sc) none =>
    s!"Prevent all damage that would be dealt to {toOracleStr sc { ctx with plural := true, capitalize := false }}."
  | .preventDamage (.matching sc) (some v) =>
    s!"Prevent {toOracleStr v { ctx with capitalize := false }} of the damage that would be dealt to {toOracleStr sc { ctx with plural := true, capitalize := false }}."
  | .modifyDamage sc false .any 2 (.const 0) =>
    if sc == scopeEquippedCreature then "Double all damage equipped creature would deal."
    else s!"Double all damage {toOracleStr sc { ctx with plural := false, capitalize := false }} would deal."
  | .modifyDamage _ true (.playerOrObject { relation := .opponent, pred := .any } _) 1 (.const 1) =>
    "If a source you control would deal noncombat damage to an opponent or a permanent an opponent controls, it deals that much damage plus 1 instead."
  | .modifyDamage _ true (.playerOrObject { relation := .opponent, pred := .any } _) 1 (.objectStat .power .this) =>
    "If a source you control would deal noncombat damage to an opponent or a permanent an opponent controls, instead it deals that much damage plus X, where X is this creature's power."
  | .modifyDamage _ nc _ mult add =>
    let dmg := if nc then "noncombat damage" else "damage"
    if mult > 1 then s!"If a source you control would deal {dmg}, it deals {timesPhrase mult} that much instead."
    else s!"If a source you control would deal {dmg}, it deals that much plus {toOracleStr add { ctx with capitalize := false }} instead."
  | .healOtherDamageWhenDealt _ =>
    "If damage would be dealt to this creature, instead that damage is dealt, but all other damage already dealt to it is healed."
  | .unspentManaBecomesColorless _ =>
    "If you would lose unspent mana, that mana becomes colorless instead."
  | .exileOnLeaveStack =>
    "If this spell would leave the stack, exile it instead of putting it anywhere else."
  | .entersTappedAndAttackingSameDefender =>
    "This creature enters tapped and attacking the same defender."
  | .all _ => ""

private def renderReplacement (ctx : PrintCtx) (cond? : Option Condition)
    (spec : StaticReplacementSpec) : String :=
  let flat := spec.flatten
  let body :=
    if flat == #[.entersTapped .self none, .asEntersChoose .color] then
      "This land enters tapped. As it enters, choose a color."
    else
      String.intercalate " " (flat.toList.map (renderReplacementOne ctx))
  match cond? with
  | none => body
  | some c =>
    let lowBody := match body.toList with
      | [] => ""
      | ch :: cs => String.ofList (ch.toLower :: cs)
    s!"As long as {renderConditionClause ctx c}, {lowBody}"

private def renderContinuous (ctx : PrintCtx) (cond? : Option Condition)
    (sc : ObjectFilter) (mod : ContinuousModification) : String :=
  let flat := mod.flatten
  let kwOnlyMod := !flat.isEmpty && flat.all fun | .grantKeywords _ => true | _ => false
  let (subj0, isPl) :=
    if kwOnlyMod then
      match sc.zones.zones.toList, sc.pred with
      | [.battlefield], .all #[.otherThan .this, .hasType .creature, .hasSubtype (.literal s), .controlledBy .you] =>
        (s!"other {s.pluralName} you control", true)
      | [.battlefield], .all #[.otherThan .this, .hasType .creature, .any ps, .controlledBy .you] =>
        let subs := ps.toList.filterMap fun | .hasSubtype (.literal s) => some s | _ => none
        if subs.length == ps.size && !subs.isEmpty then
          (s!"other {joinedSubtypes subs.toArray CardSubtype.pluralName} you control", true)
        else renderScopeSubject ctx sc
      | _, _ => renderScopeSubject ctx sc
    else renderScopeSubject ctx sc
  -- Special cases that combine player rule + object modification cleanly in one sentence
  let hasPlayerHexproof := flat.any fun
    | .applyRule (.player (.hexproof { relation := .you, pred := .any } none)) => true
    | _ => false
  let hasPlayerProtChosen := flat.any fun
    | .applyRule (.player (.protectionFrom { relation := .you, pred := .any } .chosenCardType)) => true
    | _ => false
  let (subj, isPl) :=
    if hasPlayerHexproof || hasPlayerProtChosen then (s!"you and {subj0}", true)
    else (subj0, isPl)
  let getVerb := if isPl then "get" else "gets"
  let haveVerb := if isPl then "have" else "has"
  let isVerb := if isPl then "are" else "is"
  let loseVerb := if isPl then "lose" else "loses"
  let clauses : List String := Id.run do
    let mut out : List String := []
    for m in flat do
      match m with
      | .modifyPT p t =>
        out := out ++ [renderDynamicModifyPT ctx getVerb p t]
      | .setBasePT (some (.const p)) (some (.const t)) =>
        -- Merged below with modifyTypes when paired (e.g. Construct 5/5)
        out := out ++ [s!"with base power and toughness {p}/{t}"]
      | .setBasePT (some p) (some t) =>
        out := out ++ [s!"{haveVerb} base power and toughness {toOracleStr p { ctx with capitalize := false }}/{toOracleStr t { ctx with capitalize := false }}"]
      | .setBasePT (some p) none =>
        out := out ++ [s!"{haveVerb} base power {toOracleStr p { ctx with capitalize := false }}"]
      | .setBasePT none (some t) =>
        out := out ++ [s!"{haveVerb} base toughness {toOracleStr t { ctx with capitalize := false }}"]
      | .setBasePT none none => pure ()
      | .grantKeywords ks =>
        if !ks.isEmpty then
          out := out ++ [s!"{haveVerb} {renderKeywordsAndWards ks}"]
      | .loseKeywords ks =>
        if !ks.isEmpty then
          out := out ++ [s!"{loseVerb} {KeywordAbility.joinedAnd ks}"]
      | .grantActivated abs =>
        for ab in abs do
          let q := ab.toOracle ctx
          let qDot := if q.endsWith "." then q else q ++ "."
          out := out ++ [s!"{haveVerb} \"{qDot}\""]
      | .grantTriggered trs =>
        for tr in trs do
          let q := tr.toNotation
          let qDot := if q.endsWith "." then q else q ++ "."
          out := out ++ [s!"{haveVerb} \"{qDot}\""]
      | .grantStatic sas =>
        for sa in sas do
          match sa with
          | .ruleModifying none (.combat (.cantBeBlocked .self)) =>
            out := out ++ ["can't be blocked"]
          | .ruleModifying none (.combat (.maxAttackersPerPermanent .self n)) =>
            let word := if n == 1 then "one creature" else s!"{englishNumber n} creatures"
            out := out ++ [s!"{haveVerb} \"No more than {word} can attack this planeswalker each combat.\""]
          | other =>
            -- Non-recursive rendering of granted statics (kept flat for C-code size)
            let _ := other
            out := out ++ [s!"{haveVerb} a static ability"]
      | .copyActivatedFrom src =>
        match src.pred with
        | .all #[.isCard, .hasSubtype (.literal sub)] =>
          out := out ++ [s!"{haveVerb} all activated abilities of all {sub} cards in your graveyard"]
        | _ =>
          out := out ++ [s!"{haveVerb} all activated abilities of {toOracleStr src { ctx with plural := true, capitalize := false }}"]
      | .loseAllAbilities =>
        out := out ++ [s!"{loseVerb} all abilities"]
      | .gainControl _ =>
        out := out ++ ["is controlled by you"]
      | .exchangeControl _ =>
        out := out ++ ["exchanges control"]
      | .becomeCopyOf _ _ =>
        out := out ++ ["is a copy"]
      | .addAllCreatureTypes =>
        out := out ++ [s!"{isVerb} all creature types"]
      | .modifyTypes tm =>
        let supStr := String.intercalate " " (tm.supertypes.toList.map Supertype.oracleWord)
        let subStr := String.intercalate " " (tm.subtypes.toList.map CardSubtype.englishName)
        let typStr := String.intercalate " " (tm.types.toList.map CardType.oracleWord)
        let desc := String.intercalate " " ([supStr, subStr, typStr].filter (!·.isEmpty))
        let inAdd := match tm.mode with
          | .add | .addDedup => " in addition to its other types"
          | .set | .setAndKeepNoncreatureSubtypes => ""
        out := out ++ [s!"{isVerb} {indefinite desc} {desc}{inAdd}"]
      | .modifyColors cm =>
        let names := Color.all.filter cm.colors.contains |>.map Color.englishName
        let desc := if names.isEmpty then "colorless" else String.intercalate " and " names
        out := out ++ [s!"{isVerb} {desc}"]
      | .applyRule (.all #[.combat (.cantAttack .self), .combat (.cantBlock .self)]) =>
        out := out ++ ["can't attack or block"]
      | .applyRule (.game (.doesntUntapDuringUntapStep .self none)) =>
        out := out ++ ["doesn't untap during its controller's untap step"]
      | .applyRule (.game (.cantBecomeUntapped .self)) =>
        out := out ++ ["can't become untapped"]
      | .applyRule (.player (.hexproof _ none)) => pure ()
      | .applyRule (.player (.protectionFrom _ _)) => pure ()
      | .applyRule r =>
        out := out ++ [renderRuleMod ctx none r]
      | .all _ => pure ()
    return out
  -- Canonical Oracle smoothing for paired clauses:
  let body :=
    -- Puppet Crafting: Construct creature + base P/T 5/5 in addition to its other types
    if sc == scopeEnchantedPermanent && flat.size == 2 &&
        (match flat[0]!, flat[1]! with
         | .modifyTypes tm, .setBasePT (some (.const p)) (some (.const t)) =>
           tm.subtypes == #[.construct] && p == 5 && t == 5
         | _, _ => false) then
      "Enchanted permanent is a Construct creature with base power and toughness 5/5 in addition to its other types."
    -- "has flying and \"Whenever...\"" (Medic's Kitesail / Reaver Cleaver)
    else if clauses.length == 3 && (clauses[1]!).startsWith "has " && (clauses[2]!).startsWith "has \"" then
      let c0 := clauses[0]!
      let c1 := clauses[1]!
      let c2 := (clauses[2]!.drop 4).copy
      s!"{capitalizeAscii subj} {c0} and {c1} and {c2}"
    -- "gets +2/+2, has first strike and vigilance, and is a legendary Soldier in addition to its other types."
    else if clauses.length == 3 && (clauses[2]!).startsWith "is a " then
      s!"{capitalizeAscii subj} {clauses[0]!}, {clauses[1]!}, and {clauses[2]!}."
    else
      let joined :=
        match clauses with
        | [] => ""
        | [a] => a
        | [a, b] => s!"{a} and {b}"
        | xs => s!"{String.intercalate ", " xs.dropLast}, and {xs.getLast!}"
      if joined.endsWith "\"" then s!"{capitalizeAscii subj} {joined}"
      else s!"{capitalizeAscii subj} {joined}."
  match cond? with
  | none => body
  | some .isYourTurn =>
    let lowBody := match body.toList with
      | [] => ""
      | ch :: cs => String.ofList (ch.toLower :: cs)
    s!"During your turn, {lowBody}"
  | some c =>
    -- Trailing "as long as ..." for threshold / other-subtype / Jace / hexproof-until-combat / power+flying
    let trailing :=
      sc == scopeSelf &&
      match c with
      | .cmp .ge (.playerMetric .graveyardSize .you) (.const _) => true
      | .exists (.inZones .battlefield (.all #[.otherThan .this, .hasSubtype (.literal _), .controlledBy .you])) => true
      | .exists (.inZones .battlefield (.all #[.hasType .planeswalker, .hasSubtype (.literal _), .controlledBy .you])) => true
      | .forAll .this (.not (.dealtDamageThisTurn true none false)) => true
      | _ => false
    if trailing then
      let bodyNoDot := if body.endsWith "." then (body.dropEnd 1).copy else body
      s!"{bodyNoDot} as long as {renderConditionClause ctx c}."
    else
      let lowBody := match body.toList with
        | [] => ""
        | ch :: cs => String.ofList (ch.toLower :: cs)
      s!"As long as {renderConditionClause ctx c}, {lowBody}"

private def renderEnchant (ctx : PrintCtx) (slot : TargetSlot) : String :=
  match slot.domain with
  | .object _ (.any #[.hasType .artifact, .all #[.not (.hasSubtype (.literal .aura)), .hasType .enchantment]])
  | .object _ (.any #[.hasType .artifact, .all #[.hasType .enchantment, .not (.hasSubtype (.literal .aura))]]) =>
    "Enchant artifact or non-Aura enchantment"
  | .object _ (.all #[.hasType .creature, .controlledBy { relation := .you, pred := .any }]) =>
    "Enchant creature you control"
  | .object zs pred =>
    s!"Enchant {toOracleStr ({ zones := zs, pred } : ObjectFilter) { ctx with plural := false, capitalize := false }}"
  | .player pf =>
    s!"Enchant {toOracleStr pf { ctx with plural := false, capitalize := false }}"
  | other => s!"Enchant {toOracleStr other { ctx with capitalize := false }}"

/-- Canonical Oracle rendering of a `StaticAbility` (CR 604). -/
def toOracle (ctx : PrintCtx) (ab : StaticAbility) : String :=
  match ab with
  | .characteristicDefining cda => renderCda ctx cda
  | .continuous cond? sc mod => renderContinuous ctx cond? sc mod
  | .ruleModifying cond? rule => renderRuleMod ctx cond? rule
  | .costModifier cond? tgt mod => renderCostMod ctx cond? tgt mod
  | .replacement cond? spec => renderReplacement ctx cond? spec
  | .enchantRestriction slot => renderEnchant ctx slot

/-- Oracle-style reminder string for `ab`. -/
def toNotation (ab : StaticAbility) : String :=
  toOracle {} ab

instance : ToOracle StaticAbility where
  toOracle := toOracle

instance : ToString StaticAbility where
  toString := toNotation

end StaticAbility

end Mtg.Engine
