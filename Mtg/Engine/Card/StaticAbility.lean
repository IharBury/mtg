import Mtg.Engine.Mana
import Mtg.Engine.TypeLine
import Mtg.Engine.Card.Keywords
import Mtg.Engine.Card.Text

/-!
# Static abilities (CR 604)

Unified static-ability representation aligned with the Comprehensive Rules:
- CR 613.1d Layer 4 type-changing effects (`TypeStatic`)
- CR 613.1f Layer 6 ability-adding and ability-removing effects (`AbilityStatic`)
- CR 604.3 / CR 613.4a Layer 7a characteristic-defining P/T abilities (`CdaStatic`)
- CR 613.4c Layer 7c power/toughness-modifying effects (`PtStatic`)
- CR 508 / CR 509 / CR 510 combat requirements, restrictions, and damage assignment (`CombatStatic`)
- CR 601.2f / CR 601.3 / CR 305.1 cost modifiers, casting permissions, and restrictions (`CostCastStatic`)
- CR 614 / CR 615 / CR 603.2d / CR 704 replacement, prevention, trigger, and rule-modifying effects (`RuleStatic`)
- CR 702 / CR 303.4 / CR 605 keyword, enchant, and intrinsic mana static abilities (`KeywordStatic`)
- Fallback printed text (`StaticAbility.printed`)

`FraStatic` and `StaticShape` are type aliases (`abbrev`) for `StaticAbility`.
-/

namespace Mtg.Engine

/-- Layer 4 type-changing static effects (CR 613.1d). -/
inductive TypeStatic where
  | enchantedOrConstructType (subtype : String := "") (construct55 : Bool := false)
  | ptAndTypesStatic (power toughness : Int) (k : Keywords := Keywords.none) (types : Array String := #[])
      (minGy : Nat := 0) (ifGyCards : Bool := false)
deriving Repr, Inhabited, BEq

namespace TypeStatic
@[match_pattern] abbrev enchantedIsOnlySubtypeCantAttackOrBlock (subtype : String) : TypeStatic := .enchantedOrConstructType subtype false
@[match_pattern] abbrev enchantedIsConstruct55 : TypeStatic := .enchantedOrConstructType "" true
@[match_pattern] abbrev enchantedCreatureGetsHasAndTypes (power toughness : Int) (k : Keywords) (types : Array String) : TypeStatic :=
  .ptAndTypesStatic power toughness k types 0 false
@[match_pattern] abbrev getsAndAllTypesIfGyCreatureCards (min : Nat) (power toughness : Int) : TypeStatic :=
  .ptAndTypesStatic power toughness Keywords.none #[] min true
end TypeStatic

/-- Layer 6 ability-adding and ability-removing static effects (CR 613.1f). -/
inductive AbilityStatic where
  | creaturesOrConditionalKeyword (k : Keywords) (subtypes : Array String := #[]) (subtype : String := "")
      (otherOnly : Bool := false) (ifControlOther : Bool := false)
  | stateOrCounterKeyword (k : Keywords) (alt1 : Bool := false) (alt2 : Bool := false)
      (equippedOrTokens : Bool := false) (plusOneThisTurn : Bool := false)
  | artifactsAndCreaturesHaveWardIfEnduringStory (ward : Nat)
  | otherSubtypeHaveTapAddOneOf (subtypes : Array String) (mana : Array ManaType)
  | subtypeAbilityRule (subtype : String) (hexproofShield : Bool := false)
  | permanentsYouControlHave (ty : CardType) (creature : Bool := false) (k : Keywords)
  | attachedOrGlobalAbilityRule (alt1 : Bool := false) (alt2 : Bool := false)
      (equippedOrSelf : Bool := false) (global : Bool := false)
deriving Repr, Inhabited, BEq

namespace AbilityStatic
@[match_pattern] abbrev creaturesYouControlHave (k : Keywords) (subtypes : Array String := #[]) (otherOnly : Bool := false) : AbilityStatic :=
  .creaturesOrConditionalKeyword k subtypes "" otherOnly false
@[match_pattern] abbrev keywordIfYouControlOtherSubtype (k : Keywords) (subtype : String) : AbilityStatic :=
  .creaturesOrConditionalKeyword k #[] subtype false true
@[match_pattern] abbrev creaturesWithPlusOneHave (k : Keywords) (each : Bool := false) (otherOnly : Bool := false) : AbilityStatic :=
  .stateOrCounterKeyword k each otherOnly false false
@[match_pattern] abbrev equippedOrAttackingTokensHave (k : Keywords) (attackingTokens : Bool := false) : AbilityStatic :=
  .stateOrCounterKeyword k attackingTokens false true false
@[match_pattern] abbrev keywordIfPlusOneThisTurn (k : Keywords) (team : Bool := false) : AbilityStatic :=
  .stateOrCounterKeyword k team false false true
@[match_pattern] abbrev enchantedLosesAbilitiesNoUntap (cantUntap : Bool := false) : AbilityStatic :=
  .attachedOrGlobalAbilityRule cantUntap false false false
@[match_pattern] abbrev equippedSpecialGrant (medicsKitesail : Bool := false) : AbilityStatic :=
  .attachedOrGlobalAbilityRule medicsKitesail false true false
@[match_pattern] abbrev selfConditionalKeyword (vigilanceOrHexproof : Bool := false) (noncombatOrHexproof : Bool := false) : AbilityStatic :=
  .attachedOrGlobalAbilityRule vigilanceOrHexproof noncombatOrHexproof true true
@[match_pattern] abbrev globalAbilityRule (splitOrPlan : Bool := false) (indestructibleOrPw : Bool := false) : AbilityStatic :=
  .attachedOrGlobalAbilityRule splitOrPlan indestructibleOrPw false true
@[match_pattern] abbrev equippedCreaturesHaveKeywordsDuringYourTurn (k : Keywords) : AbilityStatic := .equippedOrAttackingTokensHave k false
@[match_pattern] abbrev attackingTokensHave (k : Keywords) : AbilityStatic := .equippedOrAttackingTokensHave k true
@[match_pattern] abbrev copyActivatedFromGySubtype (subtype : String) : AbilityStatic := .subtypeAbilityRule subtype false
@[match_pattern] abbrev youAndOtherSubtypeHaveHexproofIfShield (subtype : String) : AbilityStatic := .subtypeAbilityRule subtype true
@[match_pattern] abbrev equippedHuntersAxe : AbilityStatic := .equippedSpecialGrant false
@[match_pattern] abbrev equippedMedicsKitesail : AbilityStatic := .equippedSpecialGrant true
@[match_pattern] abbrev firstStrikeDuringYourTurn : AbilityStatic := .selfConditionalKeyword false false
@[match_pattern] abbrev vigilanceIfJace : AbilityStatic := .selfConditionalKeyword true false
@[match_pattern] abbrev flyingHasteIfOpponentDealtNoncombat : AbilityStatic := .selfConditionalKeyword false true
@[match_pattern] abbrev hexproofUntilCombatDamage : AbilityStatic := .selfConditionalKeyword true true
@[match_pattern] abbrev noncreatureSpellsHaveImprovise : AbilityStatic := .globalAbilityRule false false
@[match_pattern] abbrev instantSorcerySplitSecond : AbilityStatic := .globalAbilityRule true false
@[match_pattern] abbrev indestructibleIfArtifactCreatureOrPlan : AbilityStatic := .globalAbilityRule false true
@[match_pattern] abbrev planeswalkersAttackedByOneAtMost : AbilityStatic := .globalAbilityRule true true
end AbilityStatic

/-- Layer 7a characteristic-defining P/T static abilities (CR 604.3 / CR 613.4a). -/
inductive CdaStatic where
  | countPtCda (alt1 : Bool := false) (alt2 : Bool := false) (bothPt : Bool := false)
  | powerEqualSubtypeYouControl (subtype : String)
deriving Repr, Inhabited, BEq

namespace CdaStatic
@[match_pattern] abbrev bothPtCda (graveyardCardTypes : Bool := false) : CdaStatic := .countPtCda graveyardCardTypes false true
@[match_pattern] abbrev powerCountCda (creaturesOrLegendaries : Bool := false) (legendariesOrBasicTypes : Bool := false) : CdaStatic :=
  .countPtCda creaturesOrLegendaries legendariesOrBasicTypes false
@[match_pattern] abbrev powerToughnessEqualLandsYouControl : CdaStatic := .bothPtCda false
@[match_pattern] abbrev ptEqualGraveyardCardTypes : CdaStatic := .bothPtCda true
@[match_pattern] abbrev powerEqualCardsInHand : CdaStatic := .powerCountCda false false
@[match_pattern] abbrev powerEqualCreaturesYouControl : CdaStatic := .powerCountCda true false
@[match_pattern] abbrev powerEqualLegendaryCreaturesYouControl : CdaStatic := .powerCountCda false true
@[match_pattern] abbrev powerEqualsBasicLandTypes : CdaStatic := .powerCountCda true true
end CdaStatic

/-- Layer 7c power/toughness-modifying static effects (CR 613.4c). -/
inductive PtStatic where
  | creaturesYouControlGet (power toughness : Int) (subtypes : Array String := #[]) (otherOnly : Bool := false)
  | attachedCreatureGetsAndHas (equipped : Bool) (power toughness : Int) (k : Keywords := Keywords.none) (ward : Nat := 0)
  | conditionalGetsAndHas (power toughness : Int) (k : Keywords := Keywords.none) (team : Bool := false) (enduringStory : Bool := false)
  | supertypeOrGyCountGets (power toughness : Int) (natParam : Nat := 0) (legendary : Bool := false) (gyCards : Bool := false)
  | stringOrCountPowerPt (s : String := "") (power toughness : Int := 0) (alt1 : Bool := false) (alt2 : Bool := false) (controlled : Bool := false)
  | groupOrSpecialPt (power toughness : Int := 0) (alt1 : Bool := false) (alt2 : Bool := false) (special : Bool := false)
deriving Repr, Inhabited, BEq

namespace PtStatic
@[match_pattern] abbrev thresholdGets (power toughness : Int) (k : Keywords := Keywords.none) : PtStatic :=
  .conditionalGetsAndHas power toughness k false false
@[match_pattern] abbrev getsIfEnduringStory (power toughness : Int) (k : Keywords := Keywords.none) (team : Bool := false) : PtStatic :=
  .conditionalGetsAndHas power toughness k team true
@[match_pattern] abbrev legendaryOrNonlegendaryCreaturesGet (power toughness : Int) (legendary : Bool) (ward : Nat := 0) : PtStatic :=
  .supertypeOrGyCountGets power toughness ward legendary false
@[match_pattern] abbrev getsIfGyCreatureCards (min : Nat) (power toughness : Int) : PtStatic :=
  .supertypeOrGyCountGets power toughness min false true
@[match_pattern] abbrev hostGets (host : String) (power toughness : Int) : PtStatic :=
  .stringOrCountPowerPt host power toughness false false false
@[match_pattern] abbrev otherSubtypeGetPowerPerArtifactToken (subtype : String) : PtStatic :=
  .stringOrCountPowerPt subtype 0 0 true false false
@[match_pattern] abbrev powerPerFatGraveyard (power : Int) : PtStatic :=
  .stringOrCountPowerPt "" power 0 false true false
@[match_pattern] abbrev getsPowerPerControlled (power : Int) (attachedEquipment : Bool := false) : PtStatic :=
  .stringOrCountPowerPt "" power 0 attachedEquipment false true
@[match_pattern] abbrev groupOrEquippedPt (power toughness : Int) (opponents : Bool := false) (equippedTreasures : Bool := false) : PtStatic :=
  .groupOrSpecialPt power toughness opponents equippedTreasures false
@[match_pattern] abbrev specialPtStatic (sevenInGyOrPw : Bool := false) (tokensOrPw : Bool := false) : PtStatic :=
  .groupOrSpecialPt 0 0 sevenInGyOrPw tokensOrPw true
@[match_pattern] abbrev chosenTypeCreaturesGet (power toughness : Int) : PtStatic := .groupOrEquippedPt power toughness false false
@[match_pattern] abbrev opponentsCreaturesGet (power toughness : Int) : PtStatic := .groupOrEquippedPt power toughness true false
@[match_pattern] abbrev equippedGetsTrampleAndCombatTreasures (power toughness : Int) : PtStatic := .groupOrEquippedPt power toughness false true
@[match_pattern] abbrev equippedFirstStrikePlusPerInstantSorcery : PtStatic := .specialPtStatic false false
@[match_pattern] abbrev powerPerSevenInGraveyard : PtStatic := .specialPtStatic true false
@[match_pattern] abbrev creatureTokensGetOneAndVigilance : PtStatic := .specialPtStatic false true
@[match_pattern] abbrev powerPerCreatureAndPlaneswalkerCard : PtStatic := .specialPtStatic true true
end PtStatic

/-- Combat requirements, restrictions, and damage-assignment static abilities (CR 508 / CR 509 / CR 510). -/
inductive CombatStatic where
  | cantBlockUnlessYouControl (subtypes : Array String)
  | natCombatRule (n : Nat) (subtype : String := "") (maxBlockers : Bool := false)
      (attackUnlessOther : Bool := false) (attackTax : Bool := false)
  | cantBeBlockedPowerRule (n : Int) (atLeast : Bool := false) (selfPower : Bool := false)
  | equippedCreatureHasKeywordsAndCantBeBlocked (k : Keywords)
  | booleanCombatRule (alt1 : Bool := false) (alt2 : Bool := false)
      (assignOrReq : Bool := false) (despiteDefender : Bool := false)
deriving Repr, Inhabited, BEq

namespace CombatStatic
@[match_pattern] abbrev cantBeBlockedCount (n : Nat) (maxBlockers : Bool := false) : CombatStatic :=
  .natCombatRule n "" maxBlockers false false
@[match_pattern] abbrev cantAttackUnlessYouControlNOther (n : Nat) (subtype : String) : CombatStatic :=
  .natCombatRule n subtype false true false
@[match_pattern] abbrev creaturesCantAttackYouUnlessPayIfEnduringStory (n : Nat) : CombatStatic :=
  .natCombatRule n "" false false true
@[match_pattern] abbrev cantBeBlockedByPower (n : Int) (atLeast : Bool := false) : CombatStatic :=
  .cantBeBlockedPowerRule n atLeast false
@[match_pattern] abbrev cantBeBlockedIfPowerAtMost (n : Int) : CombatStatic :=
  .cantBeBlockedPowerRule n false true
@[match_pattern] abbrev unblockableOrEvasionRule (equippedYourTurn : Bool := false) (smallOrFlying : Bool := false) : CombatStatic :=
  .booleanCombatRule equippedYourTurn smallOrFlying false false
@[match_pattern] abbrev combatAssignOrRequirement (toughnessAssigns : Bool := false) (negativePositive : Bool := false) : CombatStatic :=
  .booleanCombatRule toughnessAssigns negativePositive true false
@[match_pattern] abbrev attackDespiteDefender (team : Bool := false) : CombatStatic :=
  .booleanCombatRule team false false true
@[match_pattern] abbrev cantBeBlockedByTokens : CombatStatic := .unblockableOrEvasionRule false false
@[match_pattern] abbrev equippedHexproofUnblockableDuringYourTurn : CombatStatic := .unblockableOrEvasionRule true false
@[match_pattern] abbrev smallCreaturesYouControlUnblockable : CombatStatic := .unblockableOrEvasionRule false true
@[match_pattern] abbrev flyingCantAttackYouOrBlockYours : CombatStatic := .unblockableOrEvasionRule true true
@[match_pattern] abbrev attacksEachCombatIfAble : CombatStatic := .combatAssignOrRequirement false false
@[match_pattern] abbrev toughnessAssignsCombatDamage : CombatStatic := .combatAssignOrRequirement true false
@[match_pattern] abbrev negativePowerAssignsAsPositive : CombatStatic := .combatAssignOrRequirement false true
end CombatStatic

/-- Cost modifiers, casting permissions, and casting restrictions (CR 601.2f / CR 601.3 / CR 305.1). -/
inductive CostCastStatic where
  | abilityCostLess (n : Nat) (powerUp : Bool := false)
  | subtypeSpellsCostLess (subtype : String) (n : Nat)
  | typeSpellsCostLess (ty : CardType) (n : Nat)
  | supertypeSpellsCostLess (s : Supertype) (n : Nat)
  | costCastRuleKind (alt1 : Bool := false) (alt2 : Bool := false)
      (actOrPerm : Bool := false) (zoneOrFlash : Bool := false)
      (castRestr : Bool := false) (noncreatureCost : Bool := false)
deriving Repr, Inhabited, BEq

namespace CostCastStatic
@[match_pattern] abbrev instantSorceryCostLessEqualPower (equipped : Bool := false) : CostCastStatic :=
  .costCastRuleKind equipped false false false false false
@[match_pattern] abbrev activationOrPermissionStatic (extraPowerUp : Bool := false) (asThoughHaste : Bool := false) : CostCastStatic :=
  .costCastRuleKind extraPowerUp asThoughHaste true false false false
@[match_pattern] abbrev zoneOrFlashCastStatic (flashOppCast : Bool := false) (freeFromHand : Bool := false) : CostCastStatic :=
  .costCastRuleKind flashOppCast freeFromHand false true false false
@[match_pattern] abbrev castRestrictionStatic (duringCombat : Bool := false) (chosenName : Bool := false) : CostCastStatic :=
  .costCastRuleKind duringCombat chosenName false false true false
@[match_pattern] abbrev noncreatureCostStatic (lessYourSpells : Bool := false) (selfDiscount : Bool := false) : CostCastStatic :=
  .costCastRuleKind lessYourSpells selfDiscount false false false true
@[match_pattern] abbrev equipAbilitiesTargetingThisCostLess (n : Nat) : CostCastStatic := .abilityCostLess n false
@[match_pattern] abbrev otherPowerUpCostsLess (n : Nat) : CostCastStatic := .abilityCostLess n true
@[match_pattern] abbrev firstEquipFreeIfEnduringStory : CostCastStatic := .activationOrPermissionStatic false false
@[match_pattern] abbrev extraPowerUpActivation : CostCastStatic := .activationOrPermissionStatic true false
@[match_pattern] abbrev activateCreaturesAsThoughHaste : CostCastStatic := .activationOrPermissionStatic false true
@[match_pattern] abbrev mayPlayLandsFromGraveyard : CostCastStatic := .zoneOrFlashCastStatic false false
@[match_pattern] abbrev flashIfOpponentCastThisTurn : CostCastStatic := .zoneOrFlashCastStatic true false
@[match_pattern] abbrev castFromHandFreeUpToCreatures : CostCastStatic := .zoneOrFlashCastStatic false true
@[match_pattern] abbrev opponentsCantCastOnYourTurn : CostCastStatic := .castRestrictionStatic false false
@[match_pattern] abbrev noSpellsOrAbilitiesDuringCombat : CostCastStatic := .castRestrictionStatic true false
@[match_pattern] abbrev chosenNameSpellsCantBeCast : CostCastStatic := .castRestrictionStatic false true
@[match_pattern] abbrev opponentsNoncreatureSpellsCostMore : CostCastStatic := .noncreatureCostStatic false false
@[match_pattern] abbrev noncreatureSpellsCostLess : CostCastStatic := .noncreatureCostStatic true false
@[match_pattern] abbrev costsLessIfCastNoncreature : CostCastStatic := .noncreatureCostStatic false true
end CostCastStatic

/-- Replacement, prevention, trigger-modification, and rule-modifying static effects (CR 614 / CR 615 / CR 603.2d / CR 704). -/
inductive RuleStatic where
  | extraTriggerIfEnduringStorySubtype (subtype : String)
  | extraTriggerAnotherYouControl (subtypes : Array String) (includeBattles : Bool)
  | maximumHandSize (n : Nat := 0)
  | ruleStaticKind (alt1 : Bool := false) (alt2 : Bool := false) (alt3 : Bool := false)
      (exileDying : Bool := false) (extraCounterFlag : Bool := false) (noncombatBonus : Bool := false)
      (entersOrOpening : Bool := false) (damageOrState : Bool := false) (equippedOrAction : Bool := false)
deriving Repr, Inhabited, BEq

namespace RuleStatic
@[match_pattern] abbrev doesntUntap (unlessEnduringStory : Bool := false) : RuleStatic :=
  .ruleStaticKind unlessEnduringStory false false false false false false false false
@[match_pattern] abbrev exileOpponentsDyingCreatures (createWolf : Bool := false) : RuleStatic :=
  .ruleStaticKind createWolf false false true false false false false false
@[match_pattern] abbrev extraCounter (plusOneOnly : Bool := false) : RuleStatic :=
  .ruleStaticKind plusOneOnly false false false true false false false false
@[match_pattern] abbrev noncombatDamageBonus (sourcePower : Bool := false) : RuleStatic :=
  .ruleStaticKind sourcePower false false false false true false false false
@[match_pattern] abbrev entersOrOpeningRule (chooseColor : Bool := false) (chooseNameOrOpening : Bool := false) : RuleStatic :=
  .ruleStaticKind chooseColor chooseNameOrOpening false false false false true false false
@[match_pattern] abbrev damageOrStateRule (pwOrDragons : Bool := false) (suppressEntersOrDragons : Bool := false) : RuleStatic :=
  .ruleStaticKind pwOrDragons suppressEntersOrDragons false false false false false true false
@[match_pattern] abbrev equippedOrActionBonus (extraDrawConnive : Bool := false) (doubleDamageOrHeal : Bool := false) (healOther : Bool := false) : RuleStatic :=
  .ruleStaticKind extraDrawConnive doubleDamageOrHeal healOther false false false false false true
@[match_pattern] abbrev entersWithXPlusOne : RuleStatic := .entersOrOpeningRule false false
@[match_pattern] abbrev entersTappedChooseColor : RuleStatic := .entersOrOpeningRule true false
@[match_pattern] abbrev entersChooseNonlandCardName : RuleStatic := .entersOrOpeningRule false true
@[match_pattern] abbrev mayBeginOnBattlefield : RuleStatic := .entersOrOpeningRule true true
@[match_pattern] abbrev preventAllDamageToThis : RuleStatic := .damageOrStateRule false false
@[match_pattern] abbrev planeswalkersSurviveZeroLoyalty : RuleStatic := .damageOrStateRule true false
@[match_pattern] abbrev enteringArtifactsCreaturesDontTrigger : RuleStatic := .damageOrStateRule false true
@[match_pattern] abbrev artifactTokensBecomeDragons : RuleStatic := .damageOrStateRule true true
@[match_pattern] abbrev equippedTriggersAgain : RuleStatic := .equippedOrActionBonus false false false
@[match_pattern] abbrev extraDrawOnConnive : RuleStatic := .equippedOrActionBonus true false false
@[match_pattern] abbrev equippedDealsDoubleDamage : RuleStatic := .equippedOrActionBonus false true false
@[match_pattern] abbrev healOtherDamageWhenDealt : RuleStatic := .equippedOrActionBonus false true true
end RuleStatic

/-- Keyword, enchant, and intrinsic mana static abilities (CR 702 / CR 303.4 / CR 605). -/
inductive KeywordStatic where
  | wardOrKeywordStatic (alt1 : Bool := false) (alt2 : Bool := false)
      (keywordFlag : Bool := false) (intrinsicMana : Bool := false)
  | numericWardStatic (n : Nat) (poison : Bool := false)
  | sneak (cost : ManaCost)
deriving Repr, Inhabited, BEq

namespace KeywordStatic
@[match_pattern] abbrev nonManaWardStatic (sacrificeLegendary : Bool := false) (discardCardOrSacThree : Bool := false) : KeywordStatic :=
  .wardOrKeywordStatic sacrificeLegendary discardCardOrSacThree false false
@[match_pattern] abbrev keywordOrEnchantFlag (extortOrEnchant : Bool := false) (boastOrEnchant : Bool := false) : KeywordStatic :=
  .wardOrKeywordStatic extortOrEnchant boastOrEnchant true false
@[match_pattern] abbrev intrinsicManaStatic (notFromHandOrSacThree : Bool := false) (planeswalkerOrSacThree : Bool := false) : KeywordStatic :=
  .wardOrKeywordStatic notFromHandOrSacThree planeswalkerOrSacThree false true
@[match_pattern] abbrev wardDiscardEnchantmentInstantOrSorcery : KeywordStatic := .nonManaWardStatic false false
@[match_pattern] abbrev wardSacrificeLegendary : KeywordStatic := .nonManaWardStatic true false
@[match_pattern] abbrev wardDiscardCard : KeywordStatic := .nonManaWardStatic false true
@[match_pattern] abbrev wardSacrificeThreePermanents : KeywordStatic := .nonManaWardStatic true true
@[match_pattern] abbrev wardDiscardOrPay (n : Nat) : KeywordStatic := .numericWardStatic n false
@[match_pattern] abbrev wardPoisonCounters (n : Nat) : KeywordStatic := .numericWardStatic n true
@[match_pattern] abbrev improvise : KeywordStatic := .keywordOrEnchantFlag false false
@[match_pattern] abbrev extort : KeywordStatic := .keywordOrEnchantFlag true false
@[match_pattern] abbrev boast : KeywordStatic := .keywordOrEnchantFlag false true
@[match_pattern] abbrev enchantArtifactOrNonAuraEnchantment : KeywordStatic := .keywordOrEnchantFlag true true
@[match_pattern] abbrev tapAddChosenColor : KeywordStatic := .intrinsicManaStatic false false
@[match_pattern] abbrev tapAddColorlessNotFromHand : KeywordStatic := .intrinsicManaStatic true false
@[match_pattern] abbrev tapAddAnyColorPlaneswalkerOnly : KeywordStatic := .intrinsicManaStatic false true
@[match_pattern] abbrev tapSacrificeAddThreeOfOneColor : KeywordStatic := .intrinsicManaStatic true true
end KeywordStatic

/-- A static ability the engine understands (CR 604).
9 field-bearing constructors aligned with CR 604 / CR 613 / CR 614 categories. -/
inductive StaticAbility where
  /-- Layer 4 type-changing static effects (CR 613.1d). -/
  | typeChange (which : TypeStatic := .enchantedIsConstruct55)
  /-- Layer 6 ability-adding and ability-removing static effects (CR 613.1f). -/
  | ability (which : AbilityStatic := .creaturesYouControlHave Keyword.trample)
  /-- Layer 7a characteristic-defining P/T static abilities (CR 604.3 / CR 613.4a). -/
  | cda (which : CdaStatic := .powerToughnessEqualLandsYouControl)
  /-- Layer 7c power/toughness-modifying static effects (CR 613.4c). -/
  | pt (which : PtStatic := .creaturesYouControlGet 2 2)
  /-- Combat requirements, restrictions, and damage-assignment static abilities (CR 508 / CR 509 / CR 510). -/
  | combat (which : CombatStatic := .attacksEachCombatIfAble)
  /-- Cost modifiers, casting permissions, and casting restrictions (CR 601.2f / CR 601.3 / CR 305.1). -/
  | costCast (which : CostCastStatic := .noncreatureSpellsCostLess)
  /-- Replacement, prevention, trigger-modification, and rule-modifying static effects (CR 614 / CR 615 / CR 603.2d / CR 704). -/
  | rule (which : RuleStatic := .maximumHandSize 0)
  /-- Keyword, enchant, and intrinsic mana static abilities (CR 702 / CR 303.4 / CR 605). -/
  | keyword (which : KeywordStatic := .improvise)
  /-- Rules text kept when the line is not a modeled static ability. -/
  | printed (text : String)
deriving Repr, Inhabited, BEq

/-- Type alias unifying `FraStatic` with `StaticAbility`. -/
abbrev FraStatic := StaticAbility

namespace StaticAbility

/-- Identity wrapper for backward-compatible `.fra s` construction. -/
abbrev fra (s : StaticAbility) : StaticAbility := s

-- TypeStatic aliases
@[match_pattern] abbrev enchantedIsOnlySubtypeCantAttackOrBlock (subtype : String) : StaticAbility := .typeChange (.enchantedIsOnlySubtypeCantAttackOrBlock subtype)
@[match_pattern] abbrev enchantedCreatureGetsHasAndTypes (power toughness : Int) (k : Keywords) (types : Array String) : StaticAbility := .typeChange (.enchantedCreatureGetsHasAndTypes power toughness k types)
@[match_pattern] abbrev getsAndAllTypesIfGyCreatureCards (min : Nat) (power toughness : Int) : StaticAbility := .typeChange (.getsAndAllTypesIfGyCreatureCards min power toughness)
@[match_pattern] abbrev enchantedIsConstruct55 : StaticAbility := .typeChange .enchantedIsConstruct55

-- AbilityStatic aliases
@[match_pattern] abbrev otherCreaturesHaveTrample (subtypes : Array String := #[]) : StaticAbility := .ability (.creaturesYouControlHave Keyword.trample subtypes true)
@[match_pattern] abbrev equippedCreatureHasKeywords (k : Keywords) : StaticAbility := .pt (.attachedCreatureGetsAndHas true 0 0 k 0)
@[match_pattern] abbrev armiesYouControlHaveTrample : StaticAbility := .ability (.creaturesYouControlHave Keyword.trample #["Army"] false)
@[match_pattern] abbrev hasteIfYouControlOtherSubtype (subtype : String) : StaticAbility := .ability (.keywordIfYouControlOtherSubtype Keyword.haste subtype)
@[match_pattern] abbrev creaturesYouControlWithPlusOneHaveMenace : StaticAbility := .ability (.creaturesWithPlusOneHave Keyword.menace true false)
@[match_pattern] abbrev lifelinkIfYouControlOtherSubtype (subtype : String) : StaticAbility := .ability (.keywordIfYouControlOtherSubtype Keyword.lifelink subtype)
@[match_pattern] abbrev equippedCreaturesHaveKeywordsDuringYourTurn (k : Keywords) : StaticAbility := .ability (.equippedCreaturesHaveKeywordsDuringYourTurn k)
@[match_pattern] abbrev artifactsAndCreaturesHaveWardIfEnduringStory (ward : Nat) : StaticAbility := .ability (.artifactsAndCreaturesHaveWardIfEnduringStory ward)
@[match_pattern] abbrev otherSubtypeHaveTapAddOneOf (subtypes : Array String) (mana : Array ManaType) : StaticAbility := .ability (.otherSubtypeHaveTapAddOneOf subtypes mana)
@[match_pattern] abbrev enchantedLosesAbilitiesDoesntUntap : StaticAbility := .ability (.enchantedLosesAbilitiesNoUntap false)
@[match_pattern] abbrev copyActivatedFromGySubtype (subtype : String) : StaticAbility := .ability (.copyActivatedFromGySubtype subtype)
@[match_pattern] abbrev youAndOtherSubtypeHaveHexproofIfShield (subtype : String) : StaticAbility := .ability (.youAndOtherSubtypeHaveHexproofIfShield subtype)
@[match_pattern] abbrev noncreatureSpellsHaveImprovise : StaticAbility := .ability .noncreatureSpellsHaveImprovise
@[match_pattern] abbrev attackingTokensHave (k : Keywords) : StaticAbility := .ability (.attackingTokensHave k)
@[match_pattern] abbrev hexproofIfPlusOneThisTurn : StaticAbility := .ability (.keywordIfPlusOneThisTurn Keyword.hexproof true)
@[match_pattern] abbrev instantSorcerySplitSecond : StaticAbility := .ability .instantSorcerySplitSecond
@[match_pattern] abbrev enchantedCreatureHasWard (w : Nat) : StaticAbility := .pt (.attachedCreatureGetsAndHas false 0 0 Keywords.none w)
@[match_pattern] abbrev creaturesWithPlusOneHave (k : Keywords) : StaticAbility := .ability (.creaturesWithPlusOneHave k false false)
@[match_pattern] abbrev indestructibleIfArtifactCreatureOrPlan : StaticAbility := .ability .indestructibleIfArtifactCreatureOrPlan
@[match_pattern] abbrev flyingIfPlusOneThisTurn : StaticAbility := .ability (.keywordIfPlusOneThisTurn Keyword.flying false)
@[match_pattern] abbrev enchantedLosesAbilitiesCantUntap : StaticAbility := .ability (.enchantedLosesAbilitiesNoUntap true)
@[match_pattern] abbrev creaturesYouControlHaveTrample : StaticAbility := .ability (.creaturesYouControlHave Keyword.trample #[] false)
@[match_pattern] abbrev firstStrikeDuringYourTurn : StaticAbility := .ability .firstStrikeDuringYourTurn
@[match_pattern] abbrev equippedHuntersAxe : StaticAbility := .ability .equippedHuntersAxe
@[match_pattern] abbrev vigilanceIfJace : StaticAbility := .ability .vigilanceIfJace
@[match_pattern] abbrev plusOneCreaturesHaveVigilance : StaticAbility := .ability (.creaturesWithPlusOneHave Keyword.vigilance true false)
@[match_pattern] abbrev flyingHasteIfOpponentDealtNoncombat : StaticAbility := .ability .flyingHasteIfOpponentDealtNoncombat
@[match_pattern] abbrev equippedMedicsKitesail : StaticAbility := .ability .equippedMedicsKitesail
@[match_pattern] abbrev planeswalkersAttackedByOneAtMost : StaticAbility := .ability .planeswalkersAttackedByOneAtMost
@[match_pattern] abbrev otherPlusOneCreaturesHaveHaste : StaticAbility := .ability (.creaturesWithPlusOneHave Keyword.haste true true)
@[match_pattern] abbrev creaturesYouControlHaveHaste : StaticAbility := .ability (.creaturesYouControlHave Keyword.haste #[] false)
@[match_pattern] abbrev landsHaveHexproof : StaticAbility := .ability (.permanentsYouControlHave .land false Keyword.hexproof)
@[match_pattern] abbrev hexproofUntilCombatDamage : StaticAbility := .ability .hexproofUntilCombatDamage
@[match_pattern] abbrev thoptersHaveHaste : StaticAbility := .ability (.creaturesYouControlHave Keyword.haste #["Thopter"] false)
@[match_pattern] abbrev artifactCreaturesHaveVigilance : StaticAbility := .ability (.permanentsYouControlHave .artifact true Keyword.vigilance)

-- CdaStatic aliases
@[match_pattern] abbrev powerToughnessEqualLandsYouControl : StaticAbility := .cda .powerToughnessEqualLandsYouControl
@[match_pattern] abbrev powerEqualCardsInHand : StaticAbility := .cda .powerEqualCardsInHand
@[match_pattern] abbrev powerEqualCreaturesYouControl : StaticAbility := .cda .powerEqualCreaturesYouControl
@[match_pattern] abbrev powerEqualSubtypeYouControl (subtype : String) : StaticAbility := .cda (.powerEqualSubtypeYouControl subtype)
@[match_pattern] abbrev powerEqualLegendaryCreaturesYouControl : StaticAbility := .cda .powerEqualLegendaryCreaturesYouControl
@[match_pattern] abbrev ptEqualGraveyardCardTypes : StaticAbility := .cda .ptEqualGraveyardCardTypes
@[match_pattern] abbrev powerEqualsBasicLandTypes : StaticAbility := .cda .powerEqualsBasicLandTypes

-- PtStatic aliases
@[match_pattern] abbrev otherCreaturesGet (subtypes : Array String) (power toughness : Int) : StaticAbility := .pt (.creaturesYouControlGet power toughness subtypes true)
@[match_pattern] abbrev hostGets (host : String) (power toughness : Int) : StaticAbility := .pt (.hostGets host power toughness)
@[match_pattern] abbrev enchantedCreatureGets (power toughness : Int) : StaticAbility := .pt (.hostGets "Enchanted creature" power toughness)
@[match_pattern] abbrev equippedCreatureGets (power toughness : Int) : StaticAbility := .pt (.hostGets "Equipped creature" power toughness)
@[match_pattern] abbrev enchantedCreatureGetsAndHas (power toughness : Int) (k : Keywords) : StaticAbility := .pt (.attachedCreatureGetsAndHas false power toughness k 0)
@[match_pattern] abbrev creaturesYouControlGet (power toughness : Int) : StaticAbility := .pt (.creaturesYouControlGet power toughness #[] false)
@[match_pattern] abbrev legendaryCreaturesGetAndWard (power toughness : Int) (ward : Nat) : StaticAbility := .pt (.legendaryOrNonlegendaryCreaturesGet power toughness true ward)
@[match_pattern] abbrev nonlegendaryCreaturesGet (power toughness : Int) : StaticAbility := .pt (.legendaryOrNonlegendaryCreaturesGet power toughness false 0)
@[match_pattern] abbrev equippedCreatureGetsAndHas (power toughness : Int) (k : Keywords) : StaticAbility := .pt (.attachedCreatureGetsAndHas true power toughness k 0)
@[match_pattern] abbrev equippedCreatureGetsAndWard (power toughness : Int) (ward : Nat) : StaticAbility := .pt (.attachedCreatureGetsAndHas true power toughness Keywords.none ward)
@[match_pattern] abbrev thresholdGets (power toughness : Int) : StaticAbility := .pt (.thresholdGets power toughness Keywords.none)
@[match_pattern] abbrev getsAndHasIfEnduringStory (power toughness : Int) (k : Keywords) : StaticAbility := .pt (.getsIfEnduringStory power toughness k false)
@[match_pattern] abbrev creaturesYouControlGetIfEnduringStory (power toughness : Int) : StaticAbility := .pt (.getsIfEnduringStory power toughness Keywords.none true)
@[match_pattern] abbrev chosenTypeCreaturesGet (power toughness : Int) : StaticAbility := .pt (.chosenTypeCreaturesGet power toughness)
@[match_pattern] abbrev otherSubtypeGetPowerPerArtifactToken (subtype : String) : StaticAbility := .pt (.otherSubtypeGetPowerPerArtifactToken subtype)
@[match_pattern] abbrev equippedFirstStrikePlusPerInstantSorcery : StaticAbility := .pt .equippedFirstStrikePlusPerInstantSorcery
@[match_pattern] abbrev powerPerFatGraveyard (power : Int) : StaticAbility := .pt (.powerPerFatGraveyard power)
@[match_pattern] abbrev equippedGetsTrampleAndCombatTreasures (power toughness : Int) : StaticAbility := .pt (.equippedGetsTrampleAndCombatTreasures power toughness)
@[match_pattern] abbrev creaturesYouControlOfSubtypeGet (subtype : String) (power toughness : Int) : StaticAbility := .pt (.creaturesYouControlGet power toughness #[subtype] false)
@[match_pattern] abbrev equippedCreatureGetsHasAndWard (power toughness : Int) (k : Keywords) (w : Nat) : StaticAbility := .pt (.attachedCreatureGetsAndHas true power toughness k w)
@[match_pattern] abbrev opponentsCreaturesGet (power toughness : Int) : StaticAbility := .pt (.opponentsCreaturesGet power toughness)
@[match_pattern] abbrev getsPowerPerOtherArtifact (power : Int) : StaticAbility := .pt (.getsPowerPerControlled power false)
@[match_pattern] abbrev getsPowerPerAttachedEquipment (power : Int) : StaticAbility := .pt (.getsPowerPerControlled power true)
@[match_pattern] abbrev getsIfGyCreatureCards (min : Nat) (power toughness : Int) : StaticAbility := .pt (.getsIfGyCreatureCards min power toughness)
@[match_pattern] abbrev enchantedCreatureGetsHasAndWard (power toughness : Int) (k : Keywords) (w : Nat) : StaticAbility := .pt (.attachedCreatureGetsAndHas false power toughness k w)
@[match_pattern] abbrev powerPerSevenInGraveyard : StaticAbility := .pt .powerPerSevenInGraveyard
@[match_pattern] abbrev enchantedGetsOneAndDeathtouch : StaticAbility := .pt (.attachedCreatureGetsAndHas false 1 0 Keyword.deathtouch 0)
@[match_pattern] abbrev powerAndFlyingIfSevenInGraveyard : StaticAbility := .pt (.thresholdGets 1 0 Keyword.flying)
@[match_pattern] abbrev creatureTokensGetOneAndVigilance : StaticAbility := .pt .creatureTokensGetOneAndVigilance
@[match_pattern] abbrev powerPerCreatureAndPlaneswalkerCard : StaticAbility := .pt .powerPerCreatureAndPlaneswalkerCard
@[match_pattern] abbrev emblemCreaturesGetTwoTwo : StaticAbility := .pt (.creaturesYouControlGet 2 2 #[] false)

-- CombatStatic aliases
@[match_pattern] abbrev cantBlockUnlessYouControl (subtypes : Array String) : StaticAbility := .combat (.cantBlockUnlessYouControl subtypes)
@[match_pattern] abbrev cantBeBlockedExceptBy (n : Nat) : StaticAbility := .combat (.cantBeBlockedCount n false)
@[match_pattern] abbrev cantBeBlockedByMoreThan (n : Nat) : StaticAbility := .combat (.cantBeBlockedCount n true)
@[match_pattern] abbrev cantBeBlockedByTokens : StaticAbility := .combat .cantBeBlockedByTokens
@[match_pattern] abbrev cantAttackUnlessYouControlNOther (n : Nat) (subtype : String) : StaticAbility := .combat (.cantAttackUnlessYouControlNOther n subtype)
@[match_pattern] abbrev cantBeBlockedByPowerAtMost (n : Int) : StaticAbility := .combat (.cantBeBlockedByPower n false)
@[match_pattern] abbrev creaturesCantAttackYouUnlessPayIfEnduringStory (n : Nat) : StaticAbility := .combat (.creaturesCantAttackYouUnlessPayIfEnduringStory n)
@[match_pattern] abbrev cantBeBlockedByPowerAtLeast (n : Int) : StaticAbility := .combat (.cantBeBlockedByPower n true)
@[match_pattern] abbrev equippedCreatureHasKeywordsAndCantBeBlocked (k : Keywords) : StaticAbility := .combat (.equippedCreatureHasKeywordsAndCantBeBlocked k)
@[match_pattern] abbrev equippedHexproofUnblockableDuringYourTurn : StaticAbility := .combat .equippedHexproofUnblockableDuringYourTurn
@[match_pattern] abbrev cantBeBlockedIfPowerAtMost (n : Int) : StaticAbility := .combat (.cantBeBlockedIfPowerAtMost n)
@[match_pattern] abbrev attacksEachCombatIfAble : StaticAbility := .combat .attacksEachCombatIfAble
@[match_pattern] abbrev smallCreaturesYouControlUnblockable : StaticAbility := .combat .smallCreaturesYouControlUnblockable
@[match_pattern] abbrev toughnessAssignsCombatDamage : StaticAbility := .combat .toughnessAssignsCombatDamage
@[match_pattern] abbrev negativePowerAssignsAsPositive : StaticAbility := .combat .negativePowerAssignsAsPositive
@[match_pattern] abbrev flyingCantAttackYouOrBlockYours : StaticAbility := .combat .flyingCantAttackYouOrBlockYours
@[match_pattern] abbrev attackDespiteDefenderIfScried : StaticAbility := .combat (.attackDespiteDefender false)
@[match_pattern] abbrev creaturesAttackDespiteDefender : StaticAbility := .combat (.attackDespiteDefender true)

-- CostCastStatic aliases
@[match_pattern] abbrev equipAbilitiesTargetingThisCostLess (n : Nat) : StaticAbility := .costCast (.equipAbilitiesTargetingThisCostLess n)
@[match_pattern] abbrev firstEquipFreeIfEnduringStory : StaticAbility := .costCast .firstEquipFreeIfEnduringStory
@[match_pattern] abbrev instantSorceryCostReductionEqualEquippedPower : StaticAbility := .costCast (.instantSorceryCostLessEqualPower true)
@[match_pattern] abbrev opponentsCantCastOnYourTurn : StaticAbility := .costCast .opponentsCantCastOnYourTurn
@[match_pattern] abbrev subtypeSpellsCostLess (subtype : String) (n : Nat) : StaticAbility := .costCast (.subtypeSpellsCostLess subtype n)
@[match_pattern] abbrev typeSpellsCostLess (ty : CardType) (n : Nat) : StaticAbility := .costCast (.typeSpellsCostLess ty n)
@[match_pattern] abbrev supertypeSpellsCostLess (s : Supertype) (n : Nat) : StaticAbility := .costCast (.supertypeSpellsCostLess s n)
@[match_pattern] abbrev mayPlayLandsFromGraveyard : StaticAbility := .costCast .mayPlayLandsFromGraveyard
@[match_pattern] abbrev flashIfOpponentCastThisTurn : StaticAbility := .costCast .flashIfOpponentCastThisTurn
@[match_pattern] abbrev instantSorceryCostLessEqualPower : StaticAbility := .costCast (.instantSorceryCostLessEqualPower false)
@[match_pattern] abbrev extraPowerUpActivation : StaticAbility := .costCast .extraPowerUpActivation
@[match_pattern] abbrev otherPowerUpCostsLess (n : Nat) : StaticAbility := .costCast (.otherPowerUpCostsLess n)
@[match_pattern] abbrev activateCreaturesAsThoughHaste : StaticAbility := .costCast .activateCreaturesAsThoughHaste
@[match_pattern] abbrev castFromHandFreeUpToCreatures : StaticAbility := .costCast .castFromHandFreeUpToCreatures
@[match_pattern] abbrev opponentsNoncreatureSpellsCostMore : StaticAbility := .costCast .opponentsNoncreatureSpellsCostMore
@[match_pattern] abbrev noSpellsOrAbilitiesDuringCombat : StaticAbility := .costCast .noSpellsOrAbilitiesDuringCombat
@[match_pattern] abbrev noncreatureSpellsCostLess : StaticAbility := .costCast .noncreatureSpellsCostLess
@[match_pattern] abbrev costsLessIfCastNoncreature : StaticAbility := .costCast .costsLessIfCastNoncreature
@[match_pattern] abbrev chosenNameSpellsCantBeCast : StaticAbility := .costCast .chosenNameSpellsCantBeCast

-- RuleStatic aliases
@[match_pattern] abbrev doesntUntapUnlessEnduringStory : StaticAbility := .rule (.doesntUntap true)
@[match_pattern] abbrev extraTriggerIfEnduringStorySubtype (subtype : String) : StaticAbility := .rule (.extraTriggerIfEnduringStorySubtype subtype)
@[match_pattern] abbrev extraTriggerAnotherYouControl (subtypes : Array String) (includeBattles : Bool) : StaticAbility := .rule (.extraTriggerAnotherYouControl subtypes includeBattles)
@[match_pattern] abbrev equippedTriggersAgain : StaticAbility := .rule .equippedTriggersAgain
@[match_pattern] abbrev exileOppDeathCreateWolf : StaticAbility := .rule (.exileOpponentsDyingCreatures true)
@[match_pattern] abbrev preventAllDamageToThis : StaticAbility := .rule .preventAllDamageToThis
@[match_pattern] abbrev noMaximumHandSize : StaticAbility := .rule (.maximumHandSize 0)
@[match_pattern] abbrev maximumHandSize (n : Nat) : StaticAbility := .rule (.maximumHandSize n)
@[match_pattern] abbrev planeswalkersSurviveZeroLoyalty : StaticAbility := .rule .planeswalkersSurviveZeroLoyalty
@[match_pattern] abbrev enteringArtifactsCreaturesDontTrigger : StaticAbility := .rule .enteringArtifactsCreaturesDontTrigger
@[match_pattern] abbrev artifactTokensBecomeDragons : StaticAbility := .rule .artifactTokensBecomeDragons
@[match_pattern] abbrev extraCounterOnPermanents : StaticAbility := .rule (.extraCounter false)
@[match_pattern] abbrev mayBeginOnBattlefield : StaticAbility := .rule .mayBeginOnBattlefield
@[match_pattern] abbrev extraDrawOnConnive : StaticAbility := .rule .extraDrawOnConnive
@[match_pattern] abbrev noncombatDamagePlusSourcePower : StaticAbility := .rule (.noncombatDamageBonus true)
@[match_pattern] abbrev equippedDealsDoubleDamage : StaticAbility := .rule .equippedDealsDoubleDamage
@[match_pattern] abbrev healOtherDamageWhenDealt : StaticAbility := .rule .healOtherDamageWhenDealt
@[match_pattern] abbrev entersWithXPlusOne : StaticAbility := .rule .entersWithXPlusOne
@[match_pattern] abbrev entersTappedChooseColor : StaticAbility := .rule .entersTappedChooseColor
@[match_pattern] abbrev extraPlusOneCounter : StaticAbility := .rule (.extraCounter true)
@[match_pattern] abbrev exileOpponentsDyingCreatures : StaticAbility := .rule (.exileOpponentsDyingCreatures false)
@[match_pattern] abbrev noncombatDamagePlusOne : StaticAbility := .rule (.noncombatDamageBonus false)
@[match_pattern] abbrev doesntUntap : StaticAbility := .rule (.doesntUntap false)
@[match_pattern] abbrev entersChooseNonlandCardName : StaticAbility := .rule .entersChooseNonlandCardName

-- KeywordStatic aliases
@[match_pattern] abbrev wardDiscardEnchantmentInstantOrSorcery : StaticAbility := .keyword .wardDiscardEnchantmentInstantOrSorcery
@[match_pattern] abbrev wardSacrificeLegendary : StaticAbility := .keyword .wardSacrificeLegendary
@[match_pattern] abbrev improvise : StaticAbility := .keyword .improvise
@[match_pattern] abbrev extort : StaticAbility := .keyword .extort
@[match_pattern] abbrev wardDiscardOrPay (n : Nat) : StaticAbility := .keyword (.wardDiscardOrPay n)
@[match_pattern] abbrev wardPoisonCounters (n : Nat) : StaticAbility := .keyword (.wardPoisonCounters n)
@[match_pattern] abbrev sneak (cost : ManaCost) : StaticAbility := .keyword (.sneak cost)
@[match_pattern] abbrev boast : StaticAbility := .keyword .boast
@[match_pattern] abbrev enchantArtifactOrNonAuraEnchantment : StaticAbility := .keyword .enchantArtifactOrNonAuraEnchantment
@[match_pattern] abbrev tapAddChosenColor : StaticAbility := .keyword .tapAddChosenColor
@[match_pattern] abbrev tapAddColorlessNotFromHand : StaticAbility := .keyword .tapAddColorlessNotFromHand
@[match_pattern] abbrev tapAddAnyColorPlaneswalkerOnly : StaticAbility := .keyword .tapAddAnyColorPlaneswalkerOnly
@[match_pattern] abbrev wardDiscardCard : StaticAbility := .keyword .wardDiscardCard
@[match_pattern] abbrev wardSacrificeThreePermanents : StaticAbility := .keyword .wardSacrificeThreePermanents
@[match_pattern] abbrev tapSacrificeAddThreeOfOneColor : StaticAbility := .keyword .tapSacrificeAddThreeOfOneColor

/-- The restricted mana this ability adds, if it is a mana ability. -/
def manaUse? : StaticAbility → Option FraManaUse
  | .tapAddColorlessNotFromHand => some .notSpellsFromHand
  | .tapAddAnyColorPlaneswalkerOnly => some .planeswalkerSpell
  | _ => none

/-- English plural used in Oracle-style reminders (`Orc` → `Orcs`).
Known subtypes use the CR 205.3 spelling, including irregular plurals. -/
def pluralSubtype (s : String) : String :=
  pluralizeName s

#guard pluralSubtype "Orc" == "Orcs"
#guard pluralSubtype "Wolf" == "Wolves"
#guard pluralSubtype "Army" == "Armies"
#guard pluralSubtype "Hero" == "Heroes"
#guard pluralSubtype "Merfolk" == "Merfolk"

/-- Oracle-style “Enchanted/Equipped creature gets +P/+T.” -/
def hostGetsPhrase (host : String) (p t : Int) : String :=
  s!"{host} gets {signedStat p}/{signedStat t}."

/-- Join subtype names for Oracle-style lord reminders (`Orc` and `Goblin`). -/
def joinedSubtypes (subtypes : Array String) (each : String → String := fun s => s) : String :=
  String.intercalate " and " (subtypes.toList.map each)

/-- Layer 4, Layer 6, Layer 7a, and Layer 7c continuous-effect projections (CR 613.1d / 613.1f / 613.4). -/
structure StaticPtAndTypeMeta where
  lordPump : Option (Array String × Int × Int) := none
  trampleSubtypes : Option (Array String) := none
  hostBonus : Int × Int := (0, 0)
  landsYouControlPT : Bool := false
  enchantedOnlySubtype : Option String := none
  cardsInHandPower : Bool := false
  hostKeywords : Keywords := Keywords.none
  /-- Lord pump includes the source (not only other creatures). -/
  lordIncludesSelf : Bool := false
  /-- Lord pump applies only to legendary creatures. -/
  lordLegendaryOnly : Bool := false
  /-- Lord pump applies only to nonlegendary creatures. -/
  lordNonlegendaryOnly : Bool := false
  /-- Ward cost this ability grants matching creatures. -/
  grantedWard : Option Nat := none
  /-- Threshold +P/+T if seven or more cards in graveyard. -/
  thresholdGets : Option (Int × Int) := none
  /-- During your turn, equipped creatures you control have these keywords. -/
  equippedTeamKeywordsDuringYourTurn : Keywords := Keywords.none
deriving Repr, Inhabited, BEq

/-- Combat requirements and restrictions projections (CR 508 / CR 509). -/
structure StaticCombatMeta where
  cantBlockUnless : Option (Array String) := none
  cantBeBlockedExcept : Option Nat := none
  /-- Maximum number of creatures that may block this creature. -/
  cantBeBlockedByMoreThan : Option Nat := none
  cantBeBlockedByTokens : Bool := false
  /-- Can't attack unless you control this many other permanents of the subtype. -/
  cantAttackUnlessNOther : Option (Nat × String) := none
  /-- Can't be blocked by creatures with power at most this. -/
  cantBeBlockedByPowerAtMost : Option Int := none
  /-- This creature can't be blocked if its own power is at most this. -/
  cantBeBlockedIfPowerAtMost : Option Int := none
  /-- Can't be blocked by creatures with power at least this. -/
  cantBeBlockedByPowerAtLeast : Option Int := none
  /-- Equipped creature also can't be blocked. -/
  equippedCantBeBlocked : Bool := false
deriving Repr, Inhabited, BEq

/-- Conditional static modifiers gated on having an enduring story. -/
structure StaticEnduringStoryMeta where
  /-- Enduring-story self pump. -/
  selfIfEnduringStory : Option (Int × Int × Keywords) := none
  /-- Enduring-story team pump. -/
  teamIfEnduringStory : Option (Int × Int) := none
  /-- Doesn't untap unless enduring story. -/
  doesntUntapUnlessEnduringStory : Bool := false
  /-- Team ward if enduring story. -/
  teamWardIfEnduringStory : Option Nat := none
  /-- Attack tax `{n}` if enduring story. -/
  attackTaxIfEnduringStory : Option Nat := none
deriving Repr, Inhabited, BEq

/-- Projections Game reads from a static ability. -/
structure StaticMeta extends StaticPtAndTypeMeta, StaticCombatMeta, StaticEnduringStoryMeta where
deriving Repr, Inhabited, BEq

/-- Classification of a static ability for Game accessors. -/
def spec : StaticAbility → StaticMeta
  | .ability (.creaturesYouControlHave k subtypes _) =>
    if k == Keyword.trample && !subtypes.isEmpty then { trampleSubtypes := some subtypes }
    else {}
  | .pt (.creaturesYouControlGet p t subtypes otherOnly) =>
    { lordPump := some (subtypes, p, t), lordIncludesSelf := !otherOnly }
  | .hostGets _ p t => { hostBonus := (p, t) }
  | .powerToughnessEqualLandsYouControl => { landsYouControlPT := true }
  | .cantBlockUnlessYouControl subtypes => { cantBlockUnless := some subtypes }
  | .combat (.cantBeBlockedCount n maxBlockers) =>
    if maxBlockers then { cantBeBlockedByMoreThan := some n }
    else { cantBeBlockedExcept := some n }
  | .enchantedIsOnlySubtypeCantAttackOrBlock subtype =>
    { enchantedOnlySubtype := some subtype }
  | .powerEqualCardsInHand => { cardsInHandPower := true }
  | .pt (.attachedCreatureGetsAndHas _ p t k w) =>
    { hostBonus := (p, t), hostKeywords := k, grantedWard := if w == 0 then none else some w }
  | .cantBeBlockedByTokens => { cantBeBlockedByTokens := true }
  | .pt (.legendaryOrNonlegendaryCreaturesGet p t legendary w) =>
    { lordPump := some (#[], p, t), lordIncludesSelf := true,
      lordLegendaryOnly := legendary, lordNonlegendaryOnly := !legendary,
      grantedWard := if w == 0 then none else some w }
  | .cantAttackUnlessYouControlNOther n subtype => { cantAttackUnlessNOther := some (n, subtype) }
  | .pt (.thresholdGets p t _) =>
    { thresholdGets := some (p, t) }
  | .combat (.cantBeBlockedByPower n atLeast) =>
    if atLeast then { cantBeBlockedByPowerAtLeast := some n }
    else { cantBeBlockedByPowerAtMost := some n }
  | .equippedCreaturesHaveKeywordsDuringYourTurn k =>
    { equippedTeamKeywordsDuringYourTurn := k }
  | .pt (.getsIfEnduringStory p t k team) =>
    if team then { teamIfEnduringStory := some (p, t) }
    else { selfIfEnduringStory := some (p, t, k) }
  | .doesntUntapUnlessEnduringStory =>
    { doesntUntapUnlessEnduringStory := true }
  | .artifactsAndCreaturesHaveWardIfEnduringStory w =>
    { teamWardIfEnduringStory := some w }
  | .creaturesCantAttackYouUnlessPayIfEnduringStory n =>
    { attackTaxIfEnduringStory := some n }
  | .equippedCreatureHasKeywordsAndCantBeBlocked k =>
    { hostKeywords := k, equippedCantBeBlocked := true }
  | .equippedFirstStrikePlusPerInstantSorcery =>
    { hostKeywords := Keyword.firstStrike }
  | .equippedGetsTrampleAndCombatTreasures p t =>
    { hostBonus := (p, t), hostKeywords := Keyword.trample }
  | .equippedHuntersAxe => { hostBonus := (2, 0) }
  | .equippedMedicsKitesail => { hostBonus := (1, 0), hostKeywords := Keyword.flying }
  | .cantBeBlockedIfPowerAtMost n =>
    { cantBeBlockedIfPowerAtMost := some n }
  | .enchantedCreatureGetsHasAndTypes p t k _ =>
    { hostBonus := (p, t), hostKeywords := k }
  | _ => {}

@[match_pattern] abbrev lordPump (subtypes : Array String) (power toughness : Int) : StaticAbility := StaticAbility.otherCreaturesGet subtypes power toughness
@[match_pattern] abbrev lordTrample (subtypes : Array String) : StaticAbility := StaticAbility.otherCreaturesHaveTrample subtypes
@[match_pattern] abbrev landsYouControlPT : StaticAbility := StaticAbility.powerToughnessEqualLandsYouControl
@[match_pattern] abbrev cantBlockUnless (subtypes : Array String) : StaticAbility := StaticAbility.cantBlockUnlessYouControl subtypes

/-- Backward-compatible alias for `StaticShape`. -/
abbrev StaticShape := StaticAbility

namespace StaticShape
export StaticAbility (hostGets lordPump lordTrample landsYouControlPT cantBlockUnless)
abbrev spec := StaticAbility.spec
end StaticShape

/-- Identity projection kept for backward compatibility with `StaticAbility.shape`. -/
abbrev shape (ab : StaticAbility) : StaticShape := ab

/-- Oracle-style text for a static ability. -/
def toNotation (ab : StaticAbility) : String :=
  match ab with
  | .ability (.creaturesYouControlHave k subtypes otherOnly) =>
    if otherOnly then
      if subtypes.isEmpty then
        s!"Other creatures you control have {k.joinedAnd}."
      else
        s!"Other {joinedSubtypes subtypes pluralSubtype} you control have {k.joinedAnd}."
    else
      if subtypes.isEmpty then
        s!"Creatures you control have {k.joinedAnd}."
      else
        s!"{joinedSubtypes subtypes pluralSubtype} you control have {k.joinedAnd}."
  | .pt (.creaturesYouControlGet p t subtypes otherOnly) =>
    if otherOnly then
      if subtypes.isEmpty then
        s!"Other creatures you control get {signedStat p}/{signedStat t}."
      else
        s!"Other {joinedSubtypes subtypes} creatures you control get {signedStat p}/{signedStat t}."
    else
      if subtypes.isEmpty then
        s!"Creatures you control get {signedStat p}/{signedStat t}."
      else
        s!"{joinedSubtypes subtypes pluralSubtype} you control get {signedStat p}/{signedStat t}."
  | .hostGets host p t => hostGetsPhrase host p t
  | .powerToughnessEqualLandsYouControl =>
    "This creature's power and toughness are each equal to the number of lands you control."
  | .cantBlockUnlessYouControl subtypes =>
    match subtypes.toList with
    | [] => "This creature can't block."
    | xs =>
      s!"This creature can't block unless you control a {String.intercalate " or " xs}."
  | .combat (.cantBeBlockedCount n maxBlockers) =>
    if maxBlockers then
      s!"This creature can't be blocked by more than {englishNumber n} creature(s)."
    else
      s!"This creature can't be blocked except by {englishNumber n} or more creatures."
  | .enchantedIsOnlySubtypeCantAttackOrBlock subtype =>
    s!"Enchanted creature is a {subtype} and can't attack or block."
  | .powerEqualCardsInHand =>
    "This power is equal to the number of cards in your hand."
  | .pt (.attachedCreatureGetsAndHas equipped p t k w) =>
    let host := if equipped then "Equipped creature" else "Enchanted creature"
    let kw := k.joinedAnd
    if p == 0 && t == 0 then
      if w > 0 && k == Keywords.none then
        s!"{host} has ward \{{w}}."
      else
        s!"{host} has {kw}."
    else if w > 0 then
      if k == Keywords.none then
        s!"{host} gets {signedStat p}/{signedStat t} and has ward \{{w}}."
      else
        s!"{host} gets {signedStat p}/{signedStat t} and has {k} and ward \{{w}}."
    else
      s!"{host} gets {signedStat p}/{signedStat t} and has {kw}."
  | .cantBeBlockedByTokens =>
    "This creature can't be blocked by tokens."
  | .powerEqualCreaturesYouControl =>
    "This power is equal to the number of creatures you control."
  | .pt (.legendaryOrNonlegendaryCreaturesGet p t legendary w) =>
    if legendary then
      s!"Legendary creatures you control get {signedStat p}/{signedStat t} and have ward \{{w}}."
    else
      s!"Nonlegendary creatures you control get {signedStat p}/{signedStat t}."
  | .ability (.keywordIfYouControlOtherSubtype k subtype) =>
    s!"This creature has {k.joinedAnd} as long as you control another {subtype}."
  | .cantAttackUnlessYouControlNOther n subtype =>
    s!"This creature can't attack unless you control {englishNumber n} or more other {pluralSubtype subtype}."
  | .ability (.creaturesWithPlusOneHave k each otherOnly) =>
    if !each then
      s!"Creatures you control with +1/+1 counters on them have {k}."
    else if otherOnly then
      s!"Each other creature you control with a +1/+1 counter on it has {k.joinedAnd}."
    else
      s!"Each creature you control with a +1/+1 counter on it has {k.joinedAnd}."
  | .pt (.thresholdGets p t k) =>
    if k == Keywords.none then
      s!"This creature gets {signedStat p}/{signedStat t} as long as there are seven or more cards in your graveyard."
    else
      s!"This creature gets {signedStat p}/{signedStat t} and has {k.joinedAnd} as long as there are seven or more cards in your graveyard."
  | .combat (.cantBeBlockedByPower n atLeast) =>
    if atLeast then
      s!"This creature can't be blocked by creatures with power {n} or greater."
    else
      s!"This creature can't be blocked by creatures with power {n} or less."
  | .equippedCreaturesHaveKeywordsDuringYourTurn k =>
    let kw :=
      if k.firstStrike && k.vigilance then "first strike and vigilance"
      else k.joinedAnd
    s!"During your turn, creatures you control that are equipped have {kw}."
  | .pt (.getsIfEnduringStory p t k team) =>
    let kw := k.joinedAnd
    if team then
      s!"As long as you have an enduring story, creatures you control get {signedStat p}/{signedStat t}."
    else if p == 0 && t == 0 then
      s!"As long as you have an enduring story, this has {kw}."
    else if k.toList.isEmpty then
      s!"As long as you have an enduring story, this gets {signedStat p}/{signedStat t}."
    else
      s!"As long as you have an enduring story, this gets {signedStat p}/{signedStat t} and has {kw}."
  | .rule (.doesntUntap unlessEnduringStory) =>
    if unlessEnduringStory then
      "This doesn't untap during your untap step unless you have an enduring story."
    else
      "This creature doesn't untap during your untap step."
  | .artifactsAndCreaturesHaveWardIfEnduringStory w =>
    s!"As long as you have an enduring story, artifacts and creatures you control have ward \{{w}}."
  | .creaturesCantAttackYouUnlessPayIfEnduringStory n =>
    s!"As long as you have an enduring story, creatures can't attack you unless their controller pays \{{n}} for each of those creatures."
  | .otherSubtypeHaveTapAddOneOf subtypes mana =>
    let add := manaSymbolsText mana " or "
    s!"Other {joinedSubtypes subtypes pluralSubtype} you control have \"\{T}: Add {add}.\""
  | .equippedCreatureHasKeywordsAndCantBeBlocked k =>
    s!"Equipped creature has {k.joinedAnd} and can't be blocked."
  | .equipAbilitiesTargetingThisCostLess n =>
    s!"Equip abilities you activate that target this creature cost \{{n}} less to activate."
  | .firstEquipFreeIfEnduringStory =>
    "As long as you have an enduring story, you may pay {0} rather than pay the equip cost of the first equip ability you activate each turn."
  | .chosenTypeCreaturesGet p t =>
    s!"Creatures you control of the chosen type get {signedStat p}/{signedStat t}."
  | .costCast (.instantSorceryCostLessEqualPower equipped) =>
    if equipped then
      "Instant and sorcery spells you cast cost {X} less to cast, where X is equipped creature's power."
    else
      "Instant and sorcery spells you cast with mana value 4 or greater cost {X} less to cast, where X is this creature's power."
  | .otherSubtypeGetPowerPerArtifactToken subtype =>
    s!"Other {pluralSubtype subtype} you control get +1/+0 for each artifact token you control."
  | .extraTriggerIfEnduringStorySubtype subtype =>
    s!"As long as you have an enduring story, if a triggered ability of a {subtype} you control triggers, that ability triggers an additional time."
  | .extraTriggerAnotherYouControl subtypes includeBattles =>
    let parts :=
      subtypes.toList ++ (if includeBattles then ["battle"] else [])
    let joined :=
      match parts with
      | [a] => a
      | [a, b] => s!"{a} or {b}"
      | xs => String.intercalate ", " xs
    s!"If a triggered ability of another {joined} you control triggers, that ability triggers an additional time."
  | .ability (.enchantedLosesAbilitiesNoUntap cantUntap) =>
    if cantUntap then
      "Enchanted creature loses all abilities and can't become untapped."
    else
      "Enchanted creature loses all abilities and doesn't untap during its controller's untap step."
  | .equippedHexproofUnblockableDuringYourTurn =>
    "During your turn, equipped creature has hexproof and can't be blocked."
  | .equippedTriggersAgain =>
    "If a triggered ability of equipped creature triggers, that ability triggers an additional time."
  | .equippedFirstStrikePlusPerInstantSorcery =>
    "Equipped creature has first strike and gets +1/+0 for each instant and sorcery card in your graveyard."
  | .powerPerFatGraveyard n =>
    s!"This creature gets {signedStat n}/+0 for each graveyard with seven or more cards in it."
  | .rule (.exileOpponentsDyingCreatures createWolf) =>
    if createWolf then
      "If a creature an opponent controls would die, exile it instead. When you do, create a 2/2 green Wolf creature token."
    else
      "If a creature an opponent controls would die, exile it instead."
  | .copyActivatedFromGySubtype subtype =>
    s!"This has all activated abilities of all {subtype} cards in your graveyard."
  | .equippedGetsTrampleAndCombatTreasures p t =>
    s!"Equipped creature gets {signedStat p}/{signedStat t} and has trample and \"Whenever this creature deals combat damage to a player or planeswalker, create that many Treasure tokens.\""
  | .wardDiscardEnchantmentInstantOrSorcery =>
    "Ward—Discard an enchantment, instant, or sorcery card."
  | .wardSacrificeLegendary =>
    "Ward—Sacrifice a legendary artifact or legendary creature."
  | .youAndOtherSubtypeHaveHexproofIfShield subtype =>
    s!"As long as this has a shield counter on it, you and other {pluralSubtype subtype} you control have hexproof."
  | .opponentsCantCastOnYourTurn =>
    "Your opponents can't cast spells during your turn."
  | .subtypeSpellsCostLess subtype n =>
    s!"{subtype} spells you cast cost \{{n}} less to cast."
  | .cantBeBlockedIfPowerAtMost n =>
    s!"This creature can't be blocked if its power is {n} or less."
  | .preventAllDamageToThis =>
    "Prevent all damage that would be dealt to this."
  | .rule (.maximumHandSize n) =>
    if n == 0 then "You have no maximum hand size."
    else s!"Your maximum hand size is {n}."
  | .powerEqualSubtypeYouControl subtype =>
    s!"This creature's power is equal to the number of {pluralSubtype subtype} you control."
  | .powerEqualLegendaryCreaturesYouControl =>
    "This creature's power is equal to the number of legendary creatures you control."
  | .typeSpellsCostLess ty n =>
    s!"{ty} spells you cast cost \{{n}} less to cast."
  | .supertypeSpellsCostLess s n =>
    s!"{s} spells you cast cost \{{n}} less to cast."
  | .improvise =>
    "Improvise"
  | .noncreatureSpellsHaveImprovise =>
    "Noncreature spells you cast have improvise."
  | .extort =>
    "Extort"
  | .attackingTokensHave k =>
    s!"Attacking creature tokens you control have {k}."
  | .ability (.keywordIfPlusOneThisTurn k team) =>
    if team then
      s!"Each creature you control that you've put one or more +1/+1 counters on this turn has {k.joinedAnd}."
    else
      s!"As long as you've put one or more +1/+1 counters on this creature this turn, it has {k.joinedAnd}."
  | .mayPlayLandsFromGraveyard =>
    "You may play lands from your graveyard."
  | .flashIfOpponentCastThisTurn =>
    "As long as an opponent has cast a spell this turn, you may cast spells as though they had flash."
  | .wardDiscardOrPay n =>
    s!"Ward—Discard a card or pay \{{n}}."
  | .wardPoisonCounters n =>
    s!"Ward—Get {englishNumber n} poison counters."
  | .attacksEachCombatIfAble =>
    "This creature attacks each combat if able."
  | .extraPowerUpActivation =>
    "Each power-up ability of permanents you control can be activated an additional time."
  | .otherPowerUpCostsLess n =>
    s!"Power-up abilities of other creatures you control cost \{{n}} less to activate."
  | .activateCreaturesAsThoughHaste =>
    "You may activate abilities of creatures you control as though those creatures had haste."
  | .planeswalkersSurviveZeroLoyalty =>
    "Planeswalkers you control aren't put into their owners' graveyards for having 0 loyalty."
  | .enteringArtifactsCreaturesDontTrigger =>
    "Artifacts and creatures entering the battlefield don't cause abilities to trigger."
  | .instantSorcerySplitSecond =>
    "Instant and sorcery spells you control have split second."
  | .ptEqualGraveyardCardTypes =>
    "This creature's power is equal to the number of card types among cards in all graveyards and its toughness is equal to that number plus 1."
  | .artifactTokensBecomeDragons =>
    "If one or more artifact tokens would be created under your control, that many 5/5 red Dragon creature tokens with flying are created instead."
  | .smallCreaturesYouControlUnblockable =>
    "Creatures you control with power or toughness 1 or less can't be blocked."
  | .toughnessAssignsCombatDamage =>
    "Each creature you control with toughness greater than its power assigns combat damage equal to its toughness rather than its power."
  | .negativePowerAssignsAsPositive =>
    "If Loot's power is negative, he assigns combat damage as though his power were positive."
  | .castFromHandFreeUpToCreatures =>
    "You may cast spells with mana value less than or equal to the number of creatures you control from your hand without paying their mana costs."
  | .rule (.extraCounter plusOneOnly) =>
    if plusOneOnly then
      "If one or more +1/+1 counters would be put on a creature you control, that many plus one +1/+1 counters are put on it instead."
    else
      "If you would put one or more counters on a permanent you control, put that many plus one of each of those kinds of counters on that permanent instead."
  | .mayBeginOnBattlefield =>
    "If this card is in your opening hand, you may begin the game with it on the battlefield."
  | .opponentsCreaturesGet p t =>
    s!"Creatures your opponents control get {signedStat p}/{signedStat t}."
  | .pt (.getsPowerPerControlled p attachedEquipment) =>
    if attachedEquipment then
      s!"This creature gets {signedStat p}/+0 for each Equipment attached to it."
    else
      s!"This creature gets {signedStat p}/+0 for each other artifact you control."
  | .getsIfGyCreatureCards min p t =>
    s!"As long as there are {min} or more creature cards in your graveyard, this creature gets {signedStat p}/{signedStat t}."
  | .indestructibleIfArtifactCreatureOrPlan =>
    "As long as you control an artifact creature or a Plan, this has indestructible."
  | .flyingCantAttackYouOrBlockYours =>
    "Creatures with flying can't attack you or block creatures you control."
  | .extraDrawOnConnive =>
    "If a creature you control would connive, instead you draw a card, then that creature connives."
  | .rule (.noncombatDamageBonus sourcePower) =>
    if sourcePower then
      "If a source you control would deal noncombat damage to an opponent or a permanent an opponent controls, instead it deals that much damage plus X, where X is this creature's power."
    else
      "If a source you control would deal noncombat damage to an opponent or a permanent an opponent controls, it deals that much damage plus 1 instead."
  | .equippedDealsDoubleDamage =>
    "Double all damage equipped creature would deal."
  | .healOtherDamageWhenDealt =>
    "If damage would be dealt to this creature, instead that damage is dealt, but all other damage already dealt to it is healed."
  | .entersWithXPlusOne =>
    "This enters with X +1/+1 counters on it."
  | .enchantedCreatureGetsHasAndTypes p t k types =>
    let kw :=
      if k.firstStrike && k.vigilance then "first strike and vigilance"
      else k.joinedAnd
    let extra :=
      if types.isEmpty then ""
      else s!", and is a {String.intercalate " " types.toList} in addition to its other types"
    s!"Enchanted creature gets {signedStat p}/{signedStat t}, has {kw}{extra}."
  | .getsAndAllTypesIfGyCreatureCards min p t =>
    s!"As long as there are {min} or more creature cards in your graveyard, this creature gets {signedStat p}/{signedStat t} and is all creature types."
  | .sneak cost =>
    s!"Sneak {cost}"
  | .boast =>
    "Boast — Exile any number of black cards from your graveyard with fifteen or more black mana symbols among their mana costs: Copy those exiled cards. You may cast up to three of the copies without paying their mana costs."
  | .combat (.attackDespiteDefender team) =>
    if team then
      "Creatures you control can attack as though they didn't have defender."
    else
      "As long as you've scried or surveilled this turn, this creature can attack as though it didn't have defender."
  | .powerPerSevenInGraveyard =>
    "This creature gets +2/+0 for every seven cards in your graveyard."
  | .firstStrikeDuringYourTurn => "During your turn, this creature has first strike."
  | .equippedHuntersAxe =>
    "Equipped creature gets +2/+0 and has \"Whenever this creature attacks, it gains your choice of trample or deathtouch until end of turn.\""
  | .enchantArtifactOrNonAuraEnchantment => "Enchant artifact or non-Aura enchantment"
  | .enchantedIsConstruct55 =>
    "Enchanted permanent is a Construct creature with base power and toughness 5/5 in addition to its other types."
  | .vigilanceIfJace => "This creature has vigilance as long as you control a Jace planeswalker."
  | .flyingHasteIfOpponentDealtNoncombat =>
    "As long as an opponent was dealt noncombat damage this turn, this creature has flying and haste."
  | .equippedMedicsKitesail =>
    "Equipped creature gets +1/+0 and has flying and \"Whenever this creature attacks, you gain 1 life.\""
  | .entersTappedChooseColor => "This land enters tapped. As it enters, choose a color."
  | .tapAddChosenColor => "{T}: Add one mana of the chosen color."
  | .creatureTokensGetOneAndVigilance => "Creature tokens you control get +1/+0 and have vigilance."
  | .tapAddColorlessNotFromHand =>
    "{T}: Add {C}. This mana can't be spent to cast spells from your hand."
  | .tapAddAnyColorPlaneswalkerOnly =>
    "{T}: Add one mana of any color. Spend this mana only to cast a planeswalker spell."
  | .opponentsNoncreatureSpellsCostMore =>
    "Noncreature spells your opponents cast cost {1} more to cast."
  | .planeswalkersAttackedByOneAtMost =>
    "Planeswalkers you control have \"No more than one creature can attack this planeswalker each combat.\""
  | .noSpellsOrAbilitiesDuringCombat =>
    "During combat, players can't cast spells or activate abilities that aren't mana abilities."
  | .noncreatureSpellsCostLess => "Noncreature spells you cast cost {1} less to cast."
  | .costsLessIfCastNoncreature =>
    "This spell costs {2} less to cast if you've cast a noncreature spell this turn."
  | .wardDiscardCard => "Ward—Discard a card."
  | .wardSacrificeThreePermanents => "Ward—Sacrifice three permanents."
  | .powerPerCreatureAndPlaneswalkerCard =>
    "This creature gets +1/+0 for each creature and planeswalker card in your graveyard."
  | .powerEqualsBasicLandTypes =>
    "This creature's power is equal to the number of basic land types among lands you control."
  | .ability (.permanentsYouControlHave ty creature k) =>
    if creature then
      s!"{ty} creatures you control have {k.joinedAnd}."
    else
      s!"{pluralSubtype (toString ty)} you control have {k.joinedAnd}."
  | .hexproofUntilCombatDamage =>
    "This creature has hexproof as long as they haven't dealt combat damage yet."
  | .tapSacrificeAddThreeOfOneColor => "{T}, Sacrifice this token: Add three mana of any one color."
  | .entersChooseNonlandCardName => "As this creature enters, choose a nonland card name."
  | .chosenNameSpellsCantBeCast => "Spells with the chosen name can't be cast."
  | .printed text => text
  | _ => ""

instance : ToString StaticAbility where
  toString := toNotation

/-- Lord +P/+T this ability grants other matching creatures, if any. -/
def lordPump? (ab : StaticAbility) : Option (Array String × Int × Int) :=
  ab.spec.lordPump

/-- Subtypes this ability grants trample to, if any. -/
def trampleSubtypes? (ab : StaticAbility) : Option (Array String) :=
  ab.spec.trampleSubtypes

/-- Continuous +P/+T this ability grants its enchanted or equipped host
(CR 613.3c). Other static abilities contribute `(0, 0)` here. -/
def hostStatBonus (ab : StaticAbility) : Int × Int :=
  ab.spec.hostBonus

/-- True for the lands-you-control P/T characteristic-defining ability. -/
def isLandsYouControlPT (ab : StaticAbility) : Bool :=
  ab.spec.landsYouControlPT

/-- Subtypes required to declare a blocker, if this ability restricts blocking. -/
def cantBlockUnless? (ab : StaticAbility) : Option (Array String) :=
  ab.spec.cantBlockUnless

/-- Minimum number of blockers required, if this ability restricts blocking. -/
def cantBeBlockedExcept? (ab : StaticAbility) : Option Nat :=
  ab.spec.cantBeBlockedExcept

/-- Maximum number of blockers, if this ability caps how many may block. -/
def cantBeBlockedByMoreThan? (ab : StaticAbility) : Option Nat :=
  ab.spec.cantBeBlockedByMoreThan

/-- Enchanted-only subtype that also prevents attacking and blocking. -/
def enchantedOnlySubtype? (ab : StaticAbility) : Option String :=
  ab.spec.enchantedOnlySubtype

/-- True for the cards-in-hand power characteristic-defining ability. -/
def isCardsInHandPower (ab : StaticAbility) : Bool :=
  ab.spec.cardsInHandPower

/-- Keywords this ability grants its enchanted or equipped host. -/
def hostKeywords (ab : StaticAbility) : Keywords :=
  ab.spec.hostKeywords

/-- True when this creature can't be blocked by tokens. -/
def blocksTokens (ab : StaticAbility) : Bool :=
  ab.spec.cantBeBlockedByTokens

/-- True when this lord pump also applies to the source. -/
def lordIncludesSelf (ab : StaticAbility) : Bool :=
  ab.spec.lordIncludesSelf

/-- True when this lord pump applies only to legendary creatures. -/
def lordLegendaryOnly (ab : StaticAbility) : Bool :=
  ab.spec.lordLegendaryOnly

/-- True when this lord pump applies only to nonlegendary creatures. -/
def lordNonlegendaryOnly (ab : StaticAbility) : Bool :=
  ab.spec.lordNonlegendaryOnly

/-- Ward cost this ability grants matching creatures, if any. -/
def grantedWard? (ab : StaticAbility) : Option Nat :=
  ab.spec.grantedWard

/-- Attack restriction: need `n` other permanents of this subtype. -/
def cantAttackUnlessNOther? (ab : StaticAbility) : Option (Nat × String) :=
  ab.spec.cantAttackUnlessNOther

def thresholdGets? (ab : StaticAbility) : Option (Int × Int) :=
  ab.spec.thresholdGets

def cantBeBlockedByPowerAtMost? (ab : StaticAbility) : Option Int :=
  ab.spec.cantBeBlockedByPowerAtMost

/-- Can't be blocked by creatures with power at least this. -/
def cantBeBlockedByPowerAtLeast? (ab : StaticAbility) : Option Int :=
  ab.spec.cantBeBlockedByPowerAtLeast

/-- This creature can't be blocked if its power is at most this. -/
def cantBeBlockedIfPowerAtMost? (ab : StaticAbility) : Option Int :=
  ab.spec.cantBeBlockedIfPowerAtMost

/-- True when this Equipment also makes its host unblockable. -/
def equippedCantBeBlocked (ab : StaticAbility) : Bool :=
  ab.spec.equippedCantBeBlocked

def equippedTeamKeywordsDuringYourTurn (ab : StaticAbility) : Keywords :=
  ab.spec.equippedTeamKeywordsDuringYourTurn

def selfIfEnduringStory? (ab : StaticAbility) : Option (Int × Int × Keywords) :=
  ab.spec.selfIfEnduringStory

def teamIfEnduringStory? (ab : StaticAbility) : Option (Int × Int) :=
  ab.spec.teamIfEnduringStory

def doesntUntapUnlessEnduringStory? (ab : StaticAbility) : Bool :=
  ab.spec.doesntUntapUnlessEnduringStory

def teamWardIfEnduringStory? (ab : StaticAbility) : Option Nat :=
  ab.spec.teamWardIfEnduringStory

def attackTaxIfEnduringStory? (ab : StaticAbility) : Option Nat :=
  ab.spec.attackTaxIfEnduringStory

end StaticAbility

namespace FraStatic
export StaticAbility (
  attackDespiteDefenderIfScried powerPerSevenInGraveyard creaturesYouControlHaveTrample
  firstStrikeDuringYourTurn equippedHuntersAxe enchantArtifactOrNonAuraEnchantment
  enchantedIsConstruct55 enchantedGetsOneAndDeathtouch vigilanceIfJace
  powerAndFlyingIfSevenInGraveyard plusOneCreaturesHaveVigilance
  flyingHasteIfOpponentDealtNoncombat equippedMedicsKitesail entersTappedChooseColor
  tapAddChosenColor creaturesAttackDespiteDefender creatureTokensGetOneAndVigilance
  tapAddColorlessNotFromHand tapAddAnyColorPlaneswalkerOnly
  opponentsNoncreatureSpellsCostMore planeswalkersAttackedByOneAtMost
  extraPlusOneCounter noSpellsOrAbilitiesDuringCombat noncreatureSpellsCostLess
  costsLessIfCastNoncreature exileOpponentsDyingCreatures wardDiscardCard
  wardSacrificeThreePermanents powerPerCreatureAndPlaneswalkerCard
  otherPlusOneCreaturesHaveHaste creaturesYouControlHaveHaste noncombatDamagePlusOne
  powerEqualsBasicLandTypes otherCreaturesHaveTrample landsHaveHexproof
  hexproofUntilCombatDamage thoptersHaveHaste artifactCreaturesHaveVigilance
  doesntUntap emblemCreaturesGetTwoTwo tapSacrificeAddThreeOfOneColor
  entersChooseNonlandCardName chosenNameSpellsCantBeCast
)
abbrev text (s : FraStatic) : String := StaticAbility.toNotation s
abbrev manaUse? (s : FraStatic) : Option FraManaUse := StaticAbility.manaUse? s
end FraStatic

end Mtg.Engine
