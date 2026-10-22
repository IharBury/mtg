import Mtg.Engine.Card.ActivatedAbility
import Mtg.Engine.Card.Saga
import Mtg.Engine.Card.StaticAbility
import Mtg.Engine.Card.TriggeredAbility

/-!
# Card definitions (CR 108, 109.3, section 2)

Printed Oracle characteristics: `CardDef`, the `AdventureFace` of
adventurer cards, and per-card mana-ability storage.
-/

namespace Mtg.Engine

/-- A `{T}: Add {M} for each [subtype] you control` mana ability (CR 106.4 / 605). -/
abbrev TapAddForEach := SagaDef

namespace TapAddForEach

def toNotation (a : TapAddForEach) : String :=
  s!"\{T}: Add \{{a.mana.letter}} for each {a.subtype} you control"

instance : ToString TapAddForEach where
  toString := toNotation

end TapAddForEach

/-- Printed spell cost reduction (CR 601.2f), represented by the unified
`CostReduction`. -/
abbrev SpellCostReduction := CostReduction

/-- Printed additional cost to cast a spell (CR 601.2b / 118.8), represented by
the unified `CostSelector`. -/
abbrev SpellAdditionalCost := CostSelector

/-- Alternative characteristics of an adventurer card while it is a spell
cast as an Adventure (CR 715.2). -/
abbrev AdventureFace := SagaDef

namespace AdventureFace

def additionalCostSacrificeCreature (a : AdventureFace) : Bool :=
  a.additionalCost == .sacrificeCreature

end AdventureFace

/-- Continuous, replacement, top-of-library, enters-choice, enters-tapped, modal, casting-permission, tap-mana, or keyword static rule on a card (CR 601 / 604 / 605 / 613 / 614 / 700 / 702). -/
abbrev CardStaticRule :=
  Option Nat × Option String × Option (Array Color) × Option ManaCost ×
    Option Nat × Option ConditionSelector × Option (Array ManaType) ×
    Option (Array TapAddForEach) × Option ManaRestriction ×
    Bool × Bool × Bool × Bool × Bool × Bool × Bool

namespace CardStaticRule

@[match_pattern] abbrev cardStaticRuleKind (nOpt : Option Nat := Option.none) (subtypeOpt : Option String := Option.none)
    (colorsOpt : Option (Array Color) := Option.none) (costOpt : Option ManaCost := Option.none)
    (countersOpt : Option Nat := Option.none) (condOpt : Option ConditionSelector := Option.none)
    (typesOpt : Option (Array ManaType) := Option.none) (entriesOpt : Option (Array TapAddForEach) := Option.none)
    (restrictionOpt : Option ManaRestriction := Option.none)
    (alt1 : Bool := false) (alt2 : Bool := false) (alt3 : Bool := false) (alt4 : Bool := false)
    (unspentGroup : Bool := false) (numeric : Bool := false) (topOfLib : Bool := false) : CardStaticRule :=
  (nOpt, subtypeOpt, colorsOpt, costOpt, countersOpt, condOpt, typesOpt, entriesOpt, restrictionOpt,
    alt1, alt2, alt3, alt4, unspentGroup, numeric, topOfLib)

end CardStaticRule

/-- Replacement, modal, or casting-permission rule on a card (CR 601.2 / 601.3 / 614.1c / 700.2). -/
abbrev EntersTappedRule := CardStaticRule

namespace EntersTappedRule

@[match_pattern] abbrev entersTappedKind (condOpt : Option ConditionSelector := Option.none) (lifeOpt : Option Nat := Option.none)
    (tapped : Bool := false) (unlessFlag : Bool := false) (payLifeFlag : Bool := false)
    (conditional : Bool := false) : EntersTappedRule :=
  CardStaticRule.cardStaticRuleKind lifeOpt Option.none Option.none Option.none Option.none condOpt Option.none Option.none Option.none tapped unlessFlag payLifeFlag conditional

@[match_pattern] abbrev unconditional (tapped : Bool := false) : EntersTappedRule :=
  .entersTappedKind Option.none Option.none tapped false false false
@[match_pattern] abbrev «unless» (cond : ConditionSelector) : EntersTappedRule :=
  .entersTappedKind (some cond) Option.none false true false false
@[match_pattern] abbrev unlessPayLife (life : Nat) : EntersTappedRule :=
  .entersTappedKind Option.none (some life) false false true false
@[match_pattern] abbrev untapped : EntersTappedRule := .unconditional false
@[match_pattern] abbrev always : EntersTappedRule := .unconditional true
@[match_pattern] abbrev unlessLegendary : EntersTappedRule :=
  .«unless» .youControlLegendary
@[match_pattern] abbrev unlessEquipment : EntersTappedRule :=
  .«unless» (.atLeast (.count .equipmentYouControl) (.fixed 1))
@[match_pattern] abbrev unlessPlaneswalker : EntersTappedRule :=
  .«unless» (.atLeast (.count .planeswalkersYouControl) (.fixed 1))
@[match_pattern] abbrev unlessTwoOtherLands : EntersTappedRule :=
  .«unless» (.atLeast (.count .landsYouControl) (.fixed 2))
@[match_pattern] abbrev unlessAnySubtype (subtypes : Array String) : EntersTappedRule :=
  .«unless» (.youControlAnySubtype subtypes)
@[match_pattern] abbrev unlessNBasics (n : Nat) : EntersTappedRule :=
  .«unless» (.atLeast .basicLandsYouControl (.fixed (Int.ofNat n)))
@[match_pattern] abbrev unlessOppLands (n : Nat) : EntersTappedRule :=
  .«unless» (.atLeast .opponentLands (.fixed (Int.ofNat n)))

end EntersTappedRule

/-- Choice or state replacement as a permanent enters the battlefield (CR 614.1c / 614.12). -/
abbrev AsEntersChoice := CardStaticRule

namespace AsEntersChoice

@[match_pattern] abbrev asEntersKind (alt1 : Bool := false) (alt2 : Bool := false) (choose : Bool := false) : AsEntersChoice :=
  CardStaticRule.cardStaticRuleKind Option.none Option.none Option.none Option.none Option.none Option.none Option.none Option.none Option.none alt1 alt2 choose false false false false
@[match_pattern] abbrev none : AsEntersChoice := .asEntersKind false false false
@[match_pattern] abbrev prepared : AsEntersChoice := .asEntersKind true false false
@[match_pattern] abbrev chooseOption (oddEven : Bool := false) (cardType : Bool := false) : AsEntersChoice :=
  .asEntersKind oddEven cardType true
@[match_pattern] abbrev creatureType : AsEntersChoice := .chooseOption false false
@[match_pattern] abbrev oddEven : AsEntersChoice := .chooseOption true false
@[match_pattern] abbrev cardType : AsEntersChoice := .chooseOption false true
@[match_pattern] abbrev marduOrJeskai : AsEntersChoice := .chooseOption true true

end AsEntersChoice

/-- Printed `{T}: Add …` mana ability beyond simple single-symbol `tapAddMana`
(CR 605.1a). -/
abbrev TapManaAbility := CardStaticRule

namespace TapManaAbility

@[match_pattern] abbrev tapManaAbilityKind (typesOpt : Option (Array ManaType) := Option.none) (restrictionStr : Option String := Option.none)
    (costOpt : Option ManaCost := Option.none) (entriesOpt : Option (Array TapAddForEach) := Option.none)
    (restrictionOpt : Option ManaRestriction := Option.none) (damage : Nat := 0) (payLife : Nat := 0)
    (alt1 : Bool := false) (alt2 : Bool := false) (specialSource : Bool := false)
    (typesFlag : Bool := false) (filterOrEach : Bool := false) (anyColorFlag : Bool := false) : TapManaAbility :=
  CardStaticRule.cardStaticRuleKind (some damage) restrictionStr Option.none costOpt (some payLife) Option.none typesOpt entriesOpt restrictionOpt alt1 alt2 specialSource typesFlag filterOrEach anyColorFlag false

@[match_pattern] abbrev dynamicOrSpecialMana (alt1 : Bool := false) (alt2 : Bool := false) (specialSource : Bool := false) : TapManaAbility :=
  .tapManaAbilityKind Option.none Option.none Option.none Option.none Option.none 0 0 alt1 alt2 specialSource false false false
@[match_pattern] abbrev oneOf (types : Array ManaType) (ifEnteredOrBasic : Bool := false) (damage : Nat := 0) (payLife : Nat := 0) : TapManaAbility :=
  .tapManaAbilityKind (some types) Option.none Option.none Option.none Option.none damage payLife ifEnteredOrBasic false false true false false
@[match_pattern] abbrev multiTypes (types : Array ManaType) (restriction : String := "") (twoAmong : Bool := false) : TapManaAbility :=
  .tapManaAbilityKind (some types) (some restriction) Option.none Option.none Option.none 0 0 twoAmong true false true false false
@[match_pattern] abbrev filter (cost : ManaCost) (types : Array ManaType) : TapManaAbility :=
  .tapManaAbilityKind (some types) Option.none (some cost) Option.none Option.none 0 0 false false false false true false
@[match_pattern] abbrev forEach (entries : Array TapAddForEach) : TapManaAbility :=
  .tapManaAbilityKind Option.none Option.none Option.none (some entries) Option.none 0 0 true false false false true false
@[match_pattern] abbrev anyColor (restriction : ManaRestriction := .none) (sacrificeSelf : Bool := false) : TapManaAbility :=
  .tapManaAbilityKind Option.none Option.none Option.none Option.none (some restriction) 0 0 sacrificeSelf false false false false true
@[match_pattern] abbrev none : TapManaAbility := .dynamicOrSpecialMana false false false
@[match_pattern] abbrev anyColorEqualToPower : TapManaAbility := .dynamicOrSpecialMana true false false
@[match_pattern] abbrev anyColorAmongLegendaries : TapManaAbility := .dynamicOrSpecialMana false true false
@[match_pattern] abbrev chosenColorPerDifferentPower : TapManaAbility := .dynamicOrSpecialMana true true false
@[match_pattern] abbrev oneOfIfEnteredOrBasic (types : Array ManaType) : TapManaAbility :=
  .oneOf types (ifEnteredOrBasic := true)
@[match_pattern] abbrev oneOfDealsDamage (types : Array ManaType) (damage : Nat) : TapManaAbility :=
  .oneOf types (damage := damage)
@[match_pattern] abbrev payLifeOneOf (life : Nat) (types : Array ManaType) : TapManaAbility :=
  .oneOf types (payLife := life)
@[match_pattern] abbrev together (types : Array ManaType) (restriction : String := "") : TapManaAbility :=
  .multiTypes types restriction false
@[match_pattern] abbrev twoAmong (types : Array ManaType) : TapManaAbility :=
  .multiTypes types "" true
@[match_pattern] abbrev restricted (types : Array ManaType) (restriction : String) : TapManaAbility :=
  .together types restriction
@[match_pattern] abbrev sacrificeAnyColor : TapManaAbility :=
  .anyColor .none true
@[match_pattern] abbrev anyColorForInstantOrSorcery : TapManaAbility :=
  .anyColor .instantOrSorcery false
@[match_pattern] abbrev anyColorForLegendary : TapManaAbility :=
  .anyColor (.only .legendarySpell) false
@[match_pattern] abbrev commanderIdentity (scryCreature : Bool := false) : TapManaAbility :=
  .dynamicOrSpecialMana scryCreature false true
@[match_pattern] abbrev couldProduce (opp : Bool) : TapManaAbility :=
  .dynamicOrSpecialMana opp true true
@[match_pattern] abbrev oppCouldProduce : TapManaAbility :=
  .dynamicOrSpecialMana true true true
@[match_pattern] abbrev youCouldProduce : TapManaAbility :=
  .dynamicOrSpecialMana false true true

end TapManaAbility

/-- Mode-selection rule for a modal spell (CR 700.2). -/
abbrev ModalRule := EntersTappedRule

namespace ModalRule

@[match_pattern] abbrev modalRuleKind (condOpt : Option ConditionSelector := Option.none) (oneOrBoth : Bool := false) (twoIf : Bool := false) : ModalRule :=
  EntersTappedRule.entersTappedKind condOpt Option.none oneOrBoth twoIf false false
@[match_pattern] abbrev unconditionalModal (oneOrBoth : Bool := false) : ModalRule :=
  .modalRuleKind Option.none oneOrBoth false
@[match_pattern] abbrev chooseTwoIf (cond : ConditionSelector) : ModalRule :=
  .modalRuleKind (some cond) false true
@[match_pattern] abbrev chooseOne : ModalRule := .unconditionalModal false
@[match_pattern] abbrev chooseOneOrBoth : ModalRule := .unconditionalModal true
@[match_pattern] abbrev chooseTwoIfYouControl (subtype : String) : ModalRule :=
  .chooseTwoIf (.youControlSubtype subtype)
@[match_pattern] abbrev chooseBothIfTeamwork : ModalRule :=
  .chooseTwoIf .teamwork

end ModalRule

/-- Permission to look at or play/cast cards from the top of your library
(CR 401.5 / 601.3). -/
abbrev TopOfLibraryRule := CardStaticRule

namespace TopOfLibraryRule

@[match_pattern] abbrev topOfLibraryKind (alt1 : Bool := false) (alt2 : Bool := false) (access : Bool := false) : TopOfLibraryRule :=
  CardStaticRule.cardStaticRuleKind Option.none Option.none Option.none Option.none Option.none Option.none Option.none Option.none Option.none alt1 alt2 access false false false true
@[match_pattern] abbrev none : TopOfLibraryRule := .topOfLibraryKind false false false
@[match_pattern] abbrev grantCreaturesTapAnyColor : TopOfLibraryRule := .topOfLibraryKind true false false
@[match_pattern] abbrev libraryAccess (playLands : Bool := false) (castCreatures : Bool := false) : TopOfLibraryRule :=
  .topOfLibraryKind playLands castCreatures true
@[match_pattern] abbrev lookAnytime : TopOfLibraryRule := .libraryAccess false false
@[match_pattern] abbrev playLands : TopOfLibraryRule := .libraryAccess true false
@[match_pattern] abbrev castCreatures : TopOfLibraryRule := .libraryAccess false true
@[match_pattern] abbrev elvenChorus : TopOfLibraryRule := .libraryAccess true true

end TopOfLibraryRule

namespace CardStaticRule

@[match_pattern] abbrev topOfLibraryKind (alt1 : Bool := false) (alt2 : Bool := false) (access : Bool := false) : CardStaticRule :=
  TopOfLibraryRule.topOfLibraryKind alt1 alt2 access
@[match_pattern] abbrev staticRuleKind (alt1 : Bool := false) (alt2 : Bool := false)
    (alt3 : Bool := false) (alt4 : Bool := false) (unspentGroup : Bool := false) : CardStaticRule :=
  .cardStaticRuleKind Option.none Option.none Option.none Option.none Option.none Option.none Option.none Option.none Option.none alt1 alt2 alt3 alt4 unspentGroup false false
@[match_pattern] abbrev topOfLibrary (rule : TopOfLibraryRule) : CardStaticRule := rule
@[match_pattern] abbrev numericStaticRule (n : Nat) (alt1 : Bool := false) (alt2 : Bool := false) (firstCreature : Bool := false) : CardStaticRule :=
  .cardStaticRuleKind (some n) Option.none Option.none Option.none Option.none Option.none Option.none Option.none Option.none alt1 alt2 firstCreature false false true false
@[match_pattern] abbrev extraLandIfOtherSubtype (subtype : String) : CardStaticRule :=
  .cardStaticRuleKind Option.none (some subtype) Option.none Option.none Option.none Option.none Option.none Option.none Option.none false false false true false true false
@[match_pattern] abbrev noneOrUnspentMana (unspentMana : Bool := false) (andColorless : Bool := false) : CardStaticRule :=
  .staticRuleKind unspentMana andColorless false false true
@[match_pattern] abbrev replacementOrBooleanRule (alt1 : Bool := false) (alt2 : Bool := false)
    (cantLoseOrDoubling : Bool := false) : CardStaticRule :=
  .staticRuleKind alt1 alt2 cantLoseOrDoubling false false
@[match_pattern] abbrev manaOrCombatRule (alt1 : Bool := false) (alt2 : Bool := false)
    (combatOrKeep : Bool := false) : CardStaticRule :=
  .staticRuleKind alt1 alt2 combatOrKeep true false
@[match_pattern] abbrev none : CardStaticRule := .noneOrUnspentMana false false
@[match_pattern] abbrev powerPerUnspentMana (andColorless : Bool := false) : CardStaticRule :=
  .noneOrUnspentMana true andColorless
@[match_pattern] abbrev lookAnytime : CardStaticRule := .topOfLibrary .lookAnytime
@[match_pattern] abbrev playLands : CardStaticRule := .topOfLibrary .playLands
@[match_pattern] abbrev castCreatures : CardStaticRule := .topOfLibrary .castCreatures
@[match_pattern] abbrev elvenChorus : CardStaticRule := .topOfLibrary .elvenChorus
@[match_pattern] abbrev grantCreaturesTapAnyColor : CardStaticRule := .topOfLibrary .grantCreaturesTapAnyColor
@[match_pattern] abbrev foodAlsoCreatesTreasure : CardStaticRule := .replacementOrBooleanRule false false false
@[match_pattern] abbrev othersEnterWithPlusOneEqualToughness : CardStaticRule := .replacementOrBooleanRule true false false
@[match_pattern] abbrev drawTwoExceptFirstDrawStep : CardStaticRule := .replacementOrBooleanRule false true false
@[match_pattern] abbrev exileOppCreaturesInstead : CardStaticRule := .replacementOrBooleanRule true true false
@[match_pattern] abbrev tokenDoubling (andDrawTwo : Bool := false) : CardStaticRule :=
  .replacementOrBooleanRule andDrawTwo false true
@[match_pattern] abbrev cantLoseAndOpponentsCantWin (andNoMinusCounters : Bool := false) : CardStaticRule :=
  .replacementOrBooleanRule andNoMinusCounters true true
@[match_pattern] abbrev powerPerMountain (n : Nat) : CardStaticRule := .numericStaticRule n false false false
@[match_pattern] abbrev hexproofIndestructibleIfLore (minLore : Nat) : CardStaticRule := .numericStaticRule minLore true false false
@[match_pattern] abbrev costReductionNotFromHand (n : Nat) : CardStaticRule := .numericStaticRule n false true false
@[match_pattern] abbrev eminenceSphinxReduction (n : Nat) : CardStaticRule := .numericStaticRule n true true false
@[match_pattern] abbrev firstCreatureDiscount (costReduction : Nat) (hasFlash : Bool) : CardStaticRule :=
  .numericStaticRule costReduction hasFlash false true
@[match_pattern] abbrev grantLandsTapAnyColor : CardStaticRule := .manaOrCombatRule false false false
@[match_pattern] abbrev freeCastIfControlCommander : CardStaticRule := .manaOrCombatRule true false false
@[match_pattern] abbrev opponentsCantGainLife : CardStaticRule := .manaOrCombatRule false true false
@[match_pattern] abbrev creaturesCantGetMinusCounters : CardStaticRule := .manaOrCombatRule true true false
@[match_pattern] abbrev unspentManaBecomesColorless : CardStaticRule := .manaOrCombatRule false false true
@[match_pattern] abbrev protectionFromChosenCardType : CardStaticRule := .manaOrCombatRule true false true
@[match_pattern] abbrev corruptedToxicLifelink : CardStaticRule := .manaOrCombatRule false true true
@[match_pattern] abbrev grantTeamPlusTwoFlying : CardStaticRule := .manaOrCombatRule true true true

end CardStaticRule

/-- Parameterized keyword, casting option, or deck-building / blocking rule on a card
(CR 118.8 / 118.9 / 702 / 100.2a / 903.3a). -/
abbrev CardKeywordRule := CardStaticRule

namespace CardKeywordRule

@[match_pattern] abbrev cardKeywordRuleKind (nOpt : Option Nat := Option.none) (subtypeOpt : Option String := Option.none) (colorsOpt : Option (Array Color) := Option.none)
    (costOpt : Option ManaCost := Option.none) (countersOpt : Option Nat := Option.none)
    (alt1 : Bool := false) (alt2 : Bool := false) (alt3 : Bool := false)
    (numeric : Bool := false) (protection : Bool := false) (cyclingFlag : Bool := false) : CardKeywordRule :=
  CardStaticRule.cardStaticRuleKind nOpt subtypeOpt colorsOpt costOpt countersOpt Option.none Option.none Option.none Option.none alt1 alt2 alt3 false numeric protection cyclingFlag

end CardKeywordRule

/-- Optional or alternative casting option on a card (CR 118.8 / 118.9 / 702). -/
abbrev SpellCastOption := CardKeywordRule

namespace SpellCastOption

@[match_pattern] abbrev spellCastOptionKind (nOpt : Option Nat := Option.none) (subtypeOpt : Option String := Option.none) (costOpt : Option ManaCost := Option.none)
    (countersOpt : Option Nat := Option.none) (alt : Bool := false) (flashbackFlag : Bool := false)
    (impendingFlag : Bool := false) (numeric : Bool := false)
    (costFlag : Bool := false) (isAffinity : Bool := false) : SpellCastOption :=
  CardKeywordRule.cardKeywordRuleKind nOpt subtypeOpt Option.none costOpt countersOpt alt flashbackFlag impendingFlag numeric costFlag isAffinity
@[match_pattern] abbrev flagOrNumericCastOption (nOpt : Option Nat := Option.none) (alt : Bool := false) (numeric : Bool := false) : SpellCastOption :=
  .spellCastOptionKind nOpt Option.none Option.none Option.none alt false false numeric false false
@[match_pattern] abbrev costCastOption (cost : ManaCost) (countersOpt : Option Nat := Option.none) (alt : Bool := false)
    (flashback : Bool := false) (impending : Bool := false) : SpellCastOption :=
  .spellCastOptionKind Option.none Option.none (some cost) countersOpt alt flashback impending false true false
@[match_pattern] abbrev affinity (subtype : String) : SpellCastOption :=
  .spellCastOptionKind Option.none (some subtype) Option.none Option.none false false false false false true
@[match_pattern] abbrev noneOrGift (giftTreasure : Bool := false) : SpellCastOption :=
  .flagOrNumericCastOption Option.none giftTreasure false
@[match_pattern] abbrev numericCastOption (n : Nat) (cascade : Bool := false) : SpellCastOption :=
  .flagOrNumericCastOption (some n) cascade true
@[match_pattern] abbrev manaCastOption (cost : ManaCost) (alt : Bool := false)
    (flashback : Bool := false) : SpellCastOption :=
  .costCastOption cost Option.none alt flashback false
@[match_pattern] abbrev impending (counters : Nat) (cost : ManaCost) : SpellCastOption :=
  .costCastOption cost (some counters) false false true
@[match_pattern] abbrev none : SpellCastOption := .noneOrGift false
@[match_pattern] abbrev giftTreasure : SpellCastOption := .noneOrGift true
@[match_pattern] abbrev kicker (cost : ManaCost) : SpellCastOption := .manaCastOption cost false false
@[match_pattern] abbrev morph (cost : ManaCost) : SpellCastOption := .manaCastOption cost true false
@[match_pattern] abbrev flashback (cost : ManaCost) (discard : Bool := false) : SpellCastOption :=
  .manaCastOption cost discard true
@[match_pattern] abbrev teamwork (minPower : Nat) : SpellCastOption := .numericCastOption minPower false
@[match_pattern] abbrev cascade (n : Nat) : SpellCastOption := .numericCastOption n true

end SpellCastOption

/-- Casting permission, restriction, or counterability rule on a card
(CR 601.2 / 601.3 / 608.2a). -/
abbrev CastPermissionRule := EntersTappedRule

namespace CastPermissionRule

@[match_pattern] abbrev castPermissionKind (condOpt : Option ConditionSelector := Option.none) (cantBeCountered : Bool := false)
    (castOnly : Bool := false) (exiled : Bool := false) (conditional : Bool := false) : CastPermissionRule :=
  EntersTappedRule.entersTappedKind condOpt Option.none cantBeCountered castOnly exiled conditional
@[match_pattern] abbrev normalOrUncounterable (cantBeCountered : Bool := false) : CastPermissionRule :=
  .castPermissionKind Option.none cantBeCountered false false false
@[match_pattern] abbrev conditionalRule (cond : ConditionSelector) (castOnly : Bool := false) (exiled : Bool := false) : CastPermissionRule :=
  .castPermissionKind (some cond) false castOnly exiled true
@[match_pattern] abbrev conditionalPermission (cond : ConditionSelector) (castOnly : Bool := false) : CastPermissionRule :=
  .conditionalRule cond castOnly false
@[match_pattern] abbrev castExiledIf (cond : ConditionSelector) : CastPermissionRule :=
  .conditionalRule cond false true
@[match_pattern] abbrev normal : CastPermissionRule := .normalOrUncounterable false
@[match_pattern] abbrev cantBeCountered : CastPermissionRule := .normalOrUncounterable true
@[match_pattern] abbrev flashIf (cond : ConditionSelector) : CastPermissionRule := .conditionalPermission cond false
@[match_pattern] abbrev castOnlyIf (cond : ConditionSelector) : CastPermissionRule := .conditionalPermission cond true
@[match_pattern] abbrev flashIfYouControl (subtype : String) : CastPermissionRule :=
  .conditionalPermission (.youControlSubtype subtype) false
@[match_pattern] abbrev castExiledWithSevenInGraveyard : CastPermissionRule :=
  .castExiledIf (.graveyardAtLeast 7)
@[match_pattern] abbrev castOnlyIfGraveyardAtLeast (min : Nat) : CastPermissionRule :=
  .conditionalPermission (.graveyardAtLeast min) true

end CastPermissionRule

namespace CardKeywordRule

@[match_pattern] abbrev numericKeywordRule (nOpt : Option Nat := Option.none) (alt1 : Bool := false) (alt2 : Bool := false)
    (alt3 : Bool := false) (numeric : Bool := false) : CardKeywordRule :=
  .cardKeywordRuleKind nOpt Option.none Option.none Option.none Option.none alt1 alt2 alt3 numeric false false
@[match_pattern] abbrev protectionFromColors (colors : Array Color) : CardKeywordRule :=
  .cardKeywordRuleKind Option.none Option.none (some colors) Option.none Option.none false false false false true false
@[match_pattern] abbrev cycling (cost : ManaCost) : CardKeywordRule :=
  .cardKeywordRuleKind Option.none Option.none Option.none (some cost) Option.none false false false false false true
@[match_pattern] abbrev noneOrStaticFlag (cantBlock : Bool := false) (deckRule : Bool := false)
    (active : Bool := false) : CardKeywordRule :=
  .numericKeywordRule Option.none cantBlock deckRule active false
@[match_pattern] abbrev wardCrewOrProwess (n : Nat) (crew : Bool := false)
    (prowess : Bool := false) : CardKeywordRule :=
  .numericKeywordRule (some n) crew prowess false true
@[match_pattern] abbrev toxic (n : Nat) (cantBlock : Bool := false) : CardKeywordRule :=
  .numericKeywordRule (some n) cantBlock true true true
@[match_pattern] abbrev none : CardKeywordRule := .noneOrStaticFlag false false false
@[match_pattern] abbrev ward (n : Nat) : CardKeywordRule := .wardCrewOrProwess n false false
@[match_pattern] abbrev crew (n : Nat) : CardKeywordRule := .wardCrewOrProwess n true false
@[match_pattern] abbrev prowess (n : Nat) : CardKeywordRule := .wardCrewOrProwess n false true
@[match_pattern] abbrev daybound : CardKeywordRule := .noneOrStaticFlag false false true
@[match_pattern] abbrev cantBlock : CardKeywordRule := .noneOrStaticFlag true false true
@[match_pattern] abbrev anyNumberInDeck : CardKeywordRule := .noneOrStaticFlag false true true
@[match_pattern] abbrev canBeCommander : CardKeywordRule := .noneOrStaticFlag true true true

end CardKeywordRule

set_option maxRecDepth 1024 in
set_option maxHeartbeats 800000 in
/-- Printed (Oracle) characteristics of a card (CR 108 / 208–212 / 601–605 / 614 / 700 / 702 / 714 / 715). -/
structure CardDef where
  power : Option Int := none
  toughness : Option Int := none
  /-- Printed power includes a star added to `power` (CR 208.2).
  A bare `*` leaves `power` empty. `1+*` and `*+1` are `some 1`.
  When that star can't be determined it counts as 0, so the power is
  `power.getD 0`: `*` is 0 and `1+*` is 1 (CR 208.2a). -/
  powerStar : Bool := false
  /-- Printed toughness includes a star added to `toughness` (CR 208.2).
  See `powerStar`. -/
  toughnessStar : Bool := false
  /-- Printed loyalty number (CR 209.1). While this planeswalker is not on
  the battlefield, its loyalty is this number. It enters the battlefield
  with that many loyalty counters. -/
  loyalty : Option Int := none
  /-- Printed defense number (CR 210.1). While this battle is not on
  the battlefield, its defense is this number. It enters the battlefield
  with that many defense counters. -/
  defense : Option Nat := none
  /-- Printed hand modifier (CR 211.1). The lower-left corner of a vanguard:
  a number preceded by a plus sign, a number preceded by a minus sign, or
  zero. It modifies its owner's starting hand size and maximum hand size. -/
  handModifier : Option Int := none
  /-- Printed life modifier (CR 212.1). The lower-right corner of a vanguard:
  a number preceded by a plus sign, a number preceded by a minus sign, or
  zero. It modifies its owner's starting life total. -/
  lifeModifier : Option Int := none
  spellEffect : Option Effect := none
  /-- Additional cost to cast this spell (CR 601.2b / 118.8). -/
  additionalCost : SpellAdditionalCost := .none
  /-- Cost reduction on this spell (CR 601.2f). -/
  spellCostReduction : SpellCostReduction := .none
  /-- Optional or alternative casting option on this card (CR 118.8 / 118.9 / 702). -/
  castOption : SpellCastOption := .none
  /-- Casting permission, restriction, or counterability rule (CR 601.2 / 601.3 / 608.2a). -/
  castPermission : CastPermissionRule := .normal
  /-- Modes of a “Choose one” spell (CR 700.2). Nonempty means the spell is modal. -/
  spellModes : Array Effect := #[]
  /-- Mode-selection rule for a modal spell (CR 700.2). -/
  modalRule : ModalRule := .chooseOne
  /-- Alternative characteristics used when this card is cast as an Adventure
  (CR 715). -/
  adventure : Option AdventureFace := none
  /-- Empower Jace N on this spell (Reality Fracture). When the spell
  resolves, put N loyalty counters on a Jace planeswalker token you control,
  creating one first if you control none. -/
  empowerJace : Option Nat := none
  /-- Sorcery or instant copied while this permanent is prepared. -/
  prepareFace : Option AdventureFace := none
  /-- Modes of this card's modal triggered ability (“When this creature
  enters, choose one —”), chosen as it is put on the stack (CR 603.3c). -/
  fraTriggerModes : Array Effect := #[]
  /-- Additional `{T}: Add _` abilities that are not implied by basic land types. -/
  tapAddMana : Array ManaType := #[]
  /-- `{T}: Add …` mana ability beyond simple single-symbol `tapAddMana` (CR 605.1a). -/
  tapManaAbility : TapManaAbility := .none
  /-- Replacement rule for whether this permanent enters tapped (CR 614.1c). -/
  entersTappedRule : EntersTappedRule := .untapped
  /-- Counters this permanent enters the battlefield with (CR 614.1c). -/
  entersWithCounters : Option (CounterKind × NumberSelector) := none
  /-- Choice made as this permanent enters the battlefield (CR 614.12). -/
  asEntersChoose : AsEntersChoice := .none
  /-- Abilities planeswalkers you control have (“Planeswalkers you control
  have …”). -/
  planeswalkersYouControlHave : Array ActivatedAbility := #[]
  /-- Printed Saga chapters (CR 714). -/
  saga : Option SagaDef := none
  /-- Non-mana activated abilities (CR 602). `{T}: Add` mana abilities are
  `tapAddMana` / `tapManaAbility` / basic land types instead. -/
  activatedAbilities : Array ActivatedAbility := #[]
  /-- Static abilities other than printed keywords (CR 604). -/
  staticAbilities : Array StaticAbility := #[]
  /-- Triggered abilities (CR 603). -/
  triggeredAbilities : Array TriggeredAbility := #[]
  /-- Continuous or replacement static rule on this card (CR 604 / 613 / 614). -/
  staticRule : CardStaticRule := .none
  name : String
  manaCost : ManaCost := ManaCost.empty
  types : Array CardType
  subtypes : Array Subtype := #[]
  supertypes : Array Supertype := #[]
  /-- Explicit color indicator, if any (CR 107.13 / 202.2). -/
  colorIndicator : Option ColorSet := none
  keywords : Keywords := Keywords.none
  /-- Parameterized keyword or deck-building / blocking rule (CR 702 / 100.2a / 903.3a). -/
  keywordRule : CardKeywordRule := .none
  /-- This object is a token (CR 111). -/
  isToken : Bool := false
  /-- Back face of a modal double-faced card that can transform. -/
  otherFace : Option CardDef := none
deriving Repr, Inhabited

namespace CardDef

def cantBeCountered (c : CardDef) : Bool :=
  c.castPermission == .cantBeCountered

def flashIfYouControlSubtype (c : CardDef) : Option String :=
  match c.castPermission with
  | .flashIfYouControl s => some s
  | _ => none

def castExiledWithSevenInGraveyard (c : CardDef) : Bool :=
  c.castPermission == .castExiledWithSevenInGraveyard

def castOnlyIfGraveyardAtLeast (c : CardDef) : Option Nat :=
  match c.castPermission with
  | .castOnlyIfGraveyardAtLeast n => some n
  | _ => none

def flashback (c : CardDef) : Option ManaCost :=
  match c.castOption with
  | .flashback cost _ => some cost
  | _ => none

def flashbackDiscard (c : CardDef) : Bool :=
  match c.castOption with
  | .flashback _ d => d
  | _ => false

def affinityForSubtype (c : CardDef) : Option String :=
  match c.castOption with
  | .affinity s => some s
  | _ => none

def giftTreasure (c : CardDef) : Bool :=
  c.castOption == .giftTreasure

def cascade (c : CardDef) : Nat :=
  match c.castOption with
  | .cascade n => n
  | _ => 0

def kicker (c : CardDef) : Option ManaCost :=
  match c.castOption with
  | .kicker cost => some cost
  | _ => none

def teamwork (c : CardDef) : Option Nat :=
  match c.castOption with
  | .teamwork n => some n
  | _ => none

def morph (c : CardDef) : Option ManaCost :=
  match c.castOption with
  | .morph cost => some cost
  | _ => none

def impending (c : CardDef) : Option (Nat × ManaCost) :=
  match c.castOption with
  | .impending n cost => some (n, cost)
  | _ => none

def ward (c : CardDef) : Option Nat :=
  match c.keywordRule with
  | .ward n => some n
  | _ => none

def anyNumberInDeck (c : CardDef) : Bool :=
  c.keywordRule == .anyNumberInDeck

def crew (c : CardDef) : Option Nat :=
  match c.keywordRule with
  | .crew n => some n
  | _ => none

def prowessInstances (c : CardDef) : Nat :=
  match c.keywordRule with
  | .prowess n => n
  | _ => 0

def daybound (c : CardDef) : Bool :=
  c.keywordRule == .daybound

def protectionFromColors (c : CardDef) : Array Color :=
  match c.keywordRule with
  | .protectionFromColors cols => cols
  | _ => #[]

def cycling (c : CardDef) : Option ManaCost :=
  match c.keywordRule with
  | .cycling cost => some cost
  | _ => none

def canBeCommander (c : CardDef) : Bool :=
  c.keywordRule == .canBeCommander

def toxic (c : CardDef) : Nat :=
  match c.keywordRule with
  | .toxic n _ => n
  | _ => 0

def cantBlock (c : CardDef) : Bool :=
  match c.keywordRule with
  | .cantBlock | .toxic _ true => true
  | _ => false

def entersTapped (c : CardDef) : Bool :=
  c.entersTappedRule == .always

def entersTappedUnlessLegendary (c : CardDef) : Bool :=
  c.entersTappedRule == .unlessLegendary

def entersTappedUnlessEquipment (c : CardDef) : Bool :=
  c.entersTappedRule == .unlessEquipment

def entersTappedUnlessPlaneswalker (c : CardDef) : Bool :=
  c.entersTappedRule == .unlessPlaneswalker

def entersTappedUnlessTwoOtherLands (c : CardDef) : Bool :=
  c.entersTappedRule == .unlessTwoOtherLands

def entersTappedUnlessPayLife (c : CardDef) : Option Nat :=
  match c.entersTappedRule with
  | .unlessPayLife n => some n
  | _ => none

def entersTappedUnlessAnySubtype (c : CardDef) : Array String :=
  match c.entersTappedRule with
  | .unlessAnySubtype ts => ts
  | _ => #[]

def entersTappedUnlessNBasics (c : CardDef) : Option Nat :=
  match c.entersTappedRule with
  | .unlessNBasics n => some n
  | _ => none

def entersTappedUnlessOppLands (c : CardDef) : Option Nat :=
  match c.entersTappedRule with
  | .unlessOppLands n => some n
  | _ => none

def entersWithHopePerCreature (c : CardDef) : Bool :=
  c.entersWithCounters == some (.hope, .count .creature)

def entersWithPlusOneCounters (c : CardDef) : Nat :=
  match c.entersWithCounters with
  | some (.plusOnePlusOne, .fixed n) => n.toNat
  | _ => 0

def entersWithIndestructibleCounter (c : CardDef) : Bool :=
  c.entersWithCounters == some (.indestructible, .fixed 1)

def entersWithShield (c : CardDef) : Nat :=
  match c.entersWithCounters with
  | some (.shield, .fixed n) => n.toNat
  | _ => 0

def asEntersChooseCreatureType (c : CardDef) : Bool :=
  c.asEntersChoose == .creatureType

def asEntersChooseOddEven (c : CardDef) : Bool :=
  c.asEntersChoose == .oddEven

def asEntersChooseCardType (c : CardDef) : Bool :=
  c.asEntersChoose == .cardType

def asEntersChooseMarduOrJeskai (c : CardDef) : Bool :=
  c.asEntersChoose == .marduOrJeskai

def entersPrepared (c : CardDef) : Bool :=
  c.asEntersChoose == .prepared

def costReductionIfCreatureDied (c : CardDef) : Nat :=
  match c.spellCostReduction with
  | .ifCreatureDied n => n
  | _ => 0

def costReductionIfTargetDamaged (c : CardDef) : Nat :=
  match c.spellCostReduction with
  | .ifTargetDamaged n => n
  | _ => 0

def costReductionIfTargetTapped (c : CardDef) : Nat :=
  match c.spellCostReduction with
  | .ifTargetTapped n => n
  | _ => 0

def costReductionIfTargetAttackingNontoken (c : CardDef) : Nat :=
  match c.spellCostReduction with
  | .ifTargetAttackingNontoken n => n
  | _ => 0

def costReductionIfTargetAttacking (c : CardDef) : Nat :=
  match c.spellCostReduction with
  | .ifTargetAttacking n => n
  | _ => 0

def costReductionIfYouControl (c : CardDef) : Option (Nat × String) :=
  match c.spellCostReduction with
  | .ifYouControl n s => some (n, s)
  | _ => none

def costReductionIfGyCreaturesAtLeast (c : CardDef) : Option (Nat × Nat) :=
  match c.spellCostReduction with
  | .ifGyCreaturesAtLeast min n => some (min, n)
  | _ => none

def costReductionEqualFlyingPower (c : CardDef) : Bool :=
  c.spellCostReduction == .equalFlyingPower

def costReductionGreatestPower (c : CardDef) : Bool :=
  c.spellCostReduction == .greatestPower

def costReductionGreatestToughness (c : CardDef) : Bool :=
  c.spellCostReduction == .greatestToughness

def costReductionEqualOppArtifacts (c : CardDef) : Bool :=
  c.spellCostReduction == .equalOppArtifacts

def additionalCostSacrificeArtifactOrCreature (c : CardDef) : Bool :=
  match c.additionalCost with
  | .sacrificeArtifactOrCreatureOnly | .sacrificeArtifactOrCreatureOrPay _
  | .sacrificeCreatureOrPlaneswalkerOrPay _ => true
  | _ => false

def additionalCostSacrificeCreatureOrPlaneswalker (c : CardDef) : Bool :=
  match c.additionalCost with
  | .sacrificeCreatureOrPlaneswalkerOrPay _ => true
  | _ => false

def additionalCostOrPayGeneric (c : CardDef) : Option Nat :=
  match c.additionalCost with
  | .sacrificeArtifactOrCreatureOrPay n
  | .sacrificeCreatureOrPlaneswalkerOrPay n => some n
  | _ => none

def additionalCostDiscardOrPayGeneric (c : CardDef) : Option Nat :=
  match c.additionalCost with
  | .discardOrPay n => some n
  | _ => none

def additionalCostSacrificeCreature (c : CardDef) : Bool :=
  c.additionalCost == .sacrificeCreature

def additionalCostBeholdOrPay (c : CardDef) : Option (String × Nat) :=
  match c.additionalCost with
  | .beholdOrPay q n => some (q, n)
  | _ => none

def tapAddManaForEach (c : CardDef) : Array TapAddForEach :=
  match c.tapManaAbility with
  | .forEach es => es
  | _ => #[]

def tapAddAnyColorEqualToPower (c : CardDef) : Bool :=
  c.tapManaAbility == .anyColorEqualToPower

def tapAddAnyColorForInstantOrSorcery (c : CardDef) : Bool :=
  c.tapManaAbility == .anyColorForInstantOrSorcery

def tapAddOneOf (c : CardDef) : Array ManaType :=
  match c.tapManaAbility with
  | .oneOf ts false 0 0 => ts
  | _ => #[]

def tapAddOneOfIfEnteredOrBasic (c : CardDef) : Array ManaType :=
  match c.tapManaAbility with
  | .oneOfIfEnteredOrBasic ts => ts
  | _ => #[]

def tapAddAnyColor (c : CardDef) : Bool :=
  c.tapManaAbility == .anyColor

def tapSacrificeAddAnyColor (c : CardDef) : Bool :=
  c.tapManaAbility == .sacrificeAnyColor

def tapAddChosenColorPerDifferentPower (c : CardDef) : Bool :=
  c.tapManaAbility == .chosenColorPerDifferentPower

def tapAddAnyColorForLegendary (c : CardDef) : Bool :=
  c.tapManaAbility == .anyColorForLegendary

def tapAddTwoAmong (c : CardDef) : Array ManaType :=
  match c.tapManaAbility with
  | .twoAmong ts => ts
  | _ => #[]

def tapAddAnyColorAmongLegendaries (c : CardDef) : Bool :=
  c.tapManaAbility == .anyColorAmongLegendaries

def tapAddRestricted (c : CardDef) : Option (Array ManaType × String) :=
  match c.tapManaAbility with
  | .together ts r => if r.isEmpty then none else some (ts, r)
  | _ => none

def tapPayLifeAddOneOf (c : CardDef) : Option (Nat × Array ManaType) :=
  match c.tapManaAbility with
  | .oneOf ts false 0 n => if n > 0 then some (n, ts) else none
  | _ => none

def tapAddCommanderIdentity (c : CardDef) : Bool :=
  match c.tapManaAbility with
  | .commanderIdentity _ => true
  | _ => false

def commanderIdentityScryCreature (c : CardDef) : Bool :=
  c.tapManaAbility == .commanderIdentity true

def tapAddTogether (c : CardDef) : Array ManaType :=
  match c.tapManaAbility with
  | .together ts "" => ts
  | _ => #[]

def tapAddOneOfDealsDamage (c : CardDef) : Option (Array ManaType × Nat) :=
  match c.tapManaAbility with
  | .oneOf ts false n 0 => if n > 0 then some (ts, n) else none
  | _ => none

def tapAddOppCouldProduce (c : CardDef) : Bool :=
  c.tapManaAbility == .oppCouldProduce

def tapAddYouCouldProduce (c : CardDef) : Bool :=
  c.tapManaAbility == .youCouldProduce

def filterMana (c : CardDef) : Option (ManaCost × Array ManaType) :=
  match c.tapManaAbility with
  | .filter cost ts => some (cost, ts)
  | _ => none

def chooseOneOrBoth (c : CardDef) : Bool :=
  c.modalRule == .chooseOneOrBoth

def chooseTwoIfYouControlSubtype (c : CardDef) : Option String :=
  match c.modalRule with
  | .chooseTwoIfYouControl s => some s
  | _ => none

def chooseBothIfTeamwork (c : CardDef) : Bool :=
  c.modalRule == .chooseBothIfTeamwork

def topOfLibraryRule (c : CardDef) : TopOfLibraryRule :=
  match c.staticRule with
  | .topOfLibraryKind alt1 alt2 access => .topOfLibraryKind alt1 alt2 access
  | _ => .none

def mayLookAtTopAnytime (c : CardDef) : Bool :=
  match c.topOfLibraryRule with
  | .libraryAccess _ _ => true
  | _ => false

def mayCastCreaturesFromTop (c : CardDef) : Bool :=
  match c.topOfLibraryRule with
  | .libraryAccess _ true => true
  | _ => false

def mayPlayLandsFromTop (c : CardDef) : Bool :=
  c.topOfLibraryRule == .playLands

def grantCreaturesTapAddAnyColor (c : CardDef) : Bool :=
  match c.topOfLibraryRule with
  | .elvenChorus | .grantCreaturesTapAnyColor => true
  | _ => false

def foodAlsoCreatesTreasure (c : CardDef) : Bool :=
  c.staticRule == .foodAlsoCreatesTreasure

def othersEnterWithPlusOneEqualToughness (c : CardDef) : Bool :=
  c.staticRule == .othersEnterWithPlusOneEqualToughness

def powerPerMountain (c : CardDef) : Nat :=
  match c.staticRule with
  | .powerPerMountain n => n
  | _ => 0

def extraLandIfOtherSubtype (c : CardDef) : Option String :=
  match c.staticRule with
  | .extraLandIfOtherSubtype s => some s
  | _ => none

def tokenDoubling (c : CardDef) : Bool :=
  match c.staticRule with
  | .tokenDoubling _ => true
  | _ => false

def drawTwoExceptFirstDrawStep (c : CardDef) : Bool :=
  match c.staticRule with
  | .drawTwoExceptFirstDrawStep | .tokenDoubling true => true
  | _ => false

def exileOppCreaturesInstead (c : CardDef) : Bool :=
  c.staticRule == .exileOppCreaturesInstead

def firstCreatureCostsLess (c : CardDef) : Nat :=
  match c.staticRule with
  | .firstCreatureDiscount n _ => n
  | _ => 0

def firstCreatureHasFlash (c : CardDef) : Bool :=
  match c.staticRule with
  | .firstCreatureDiscount _ b => b
  | _ => false

def hexproofIndestructibleIfLore (c : CardDef) : Option Nat :=
  match c.staticRule with
  | .hexproofIndestructibleIfLore n => some n
  | _ => none

def costReductionNotFromHand (c : CardDef) : Nat :=
  match c.staticRule with
  | .costReductionNotFromHand n => n
  | _ => 0

def grantLandsTapAnyColor (c : CardDef) : Bool :=
  c.staticRule == .grantLandsTapAnyColor

def freeCastIfControlCommander (c : CardDef) : Bool :=
  c.staticRule == .freeCastIfControlCommander

def opponentsCantGainLife (c : CardDef) : Bool :=
  c.staticRule == .opponentsCantGainLife

def cantLoseGame (c : CardDef) : Bool :=
  match c.staticRule with
  | .cantLoseAndOpponentsCantWin _ => true
  | _ => false

def opponentsCantWin (c : CardDef) : Bool :=
  match c.staticRule with
  | .cantLoseAndOpponentsCantWin _ => true
  | _ => false

def creaturesCantGetMinusCounters (c : CardDef) : Bool :=
  match c.staticRule with
  | .creaturesCantGetMinusCounters | .cantLoseAndOpponentsCantWin true => true
  | _ => false

def powerPerUnspentMana (c : CardDef) : Bool :=
  match c.staticRule with
  | .powerPerUnspentMana _ => true
  | _ => false

def unspentManaBecomesColorless (c : CardDef) : Bool :=
  match c.staticRule with
  | .unspentManaBecomesColorless | .powerPerUnspentMana true => true
  | _ => false

def eminenceSphinxReduction (c : CardDef) : Nat :=
  match c.staticRule with
  | .eminenceSphinxReduction n => n
  | _ => 0

def protectionFromChosenCardType (c : CardDef) : Bool :=
  c.staticRule == .protectionFromChosenCardType

def corruptedToxicLifelink (c : CardDef) : Bool :=
  c.staticRule == .corruptedToxicLifelink

def grantTeamPlusTwoFlying (c : CardDef) : Bool :=
  c.staticRule == .grantTeamPlusTwoFlying

/-- Color from color indicator, otherwise from mana cost (CR 202.2). -/
def colors (c : CardDef) : ColorSet :=
  match c.colorIndicator with
  | some cs => cs
  | none => c.manaCost.colors

/-- Commander color identity of this face: mana cost, color indicator, and
basic land types (CR 903.4). Does not look at the other face. -/
def faceColorIdentity (c : CardDef) : ColorSet :=
  let fromCost :=
    match c.colorIndicator with
    | some cs => c.manaCost.colors.union cs
    | none => c.manaCost.colors
  c.subtypes.foldl (fun acc s =>
    match manaForBasicLandType s with
    | some col => acc.insert col
    | none => acc) fromCost

/-- Combined color identity of both faces of a DFC (CR 903.4 / MSH 18). -/
def colorIdentity (c : CardDef) : ColorSet :=
  match c.otherFace with
  | none => c.faceColorIdentity
  | some back => c.faceColorIdentity.union back.faceColorIdentity

/-- True when `t` is among this card's types. -/
def hasType (c : CardDef) (t : CardType) : Bool := c.types.any (· == t)

/-- True when `s` is among this card's subtypes. -/
def hasSubtype (c : CardDef) (s : Subtype) : Bool := c.subtypes.any (· == s)

/-- True when `s` is among this card's supertypes. -/
def hasSupertype (c : CardDef) (s : Supertype) : Bool := c.supertypes.any (· == s)

def isLand (c : CardDef) : Bool := c.hasType .land
def isCreature (c : CardDef) : Bool := c.hasType .creature
def isArtifact (c : CardDef) : Bool := c.hasType .artifact
def isInstant (c : CardDef) : Bool := c.hasType .instant
def isSorcery (c : CardDef) : Bool := c.hasType .sorcery
def isInstantOrSorcery (c : CardDef) : Bool := c.types.any CardType.isInstantOrSorcery
def isEnchantment (c : CardDef) : Bool := c.hasType .enchantment
def isPlaneswalker (c : CardDef) : Bool := c.hasType .planeswalker
def isBattle (c : CardDef) : Bool := c.hasType .battle
def isVanguard (c : CardDef) : Bool := c.hasType .vanguard
def isPermanentCard (c : CardDef) : Bool := c.types.any CardType.isPermanentType
/-- Aura subtype on an Enchantment (CR 303.4). -/
def isAura (c : CardDef) : Bool :=
  c.isEnchantment && c.hasSubtype "Aura"
/-- Equipment subtype on an Artifact (CR 301.5). -/
def isEquipment (c : CardDef) : Bool :=
  c.isArtifact && c.hasSubtype "Equipment"

/-- Names a player may choose for “choose a card name”, including an
Adventure face (Gatherer ruling on adventurer cards). -/
def choosableNames (c : CardDef) : Array String :=
  match c.adventure with
  | some adv => #[c.name, adv.name]
  | none => #[c.name]

/-- Timing of a sorcery: also the default for permanent spells without flash (CR 302.1, 307.1). -/
def hasSorcerySpeed (c : CardDef) : Bool :=
  !c.isInstant && !c.isLand && !c.keywords.flash

def hasInstantSpeed (c : CardDef) : Bool :=
  c.isInstant || c.keywords.flash

/-- Modal spell with “Choose one” (CR 700.2). -/
def isModal (c : CardDef) : Bool :=
  !c.spellModes.isEmpty

/-- Modes of a modal spell; empty when the card is not modal. -/
def modes (c : CardDef) : Array Effect :=
  c.spellModes

/-- Whether casting this card requires choosing a target (CR 115.1, 303.4). -/
def requiresTarget (c : CardDef) : Bool :=
  c.isAura ||
  match c.spellEffect with
  | some e => e.requiresTarget
  | none => !c.spellModes.isEmpty && c.spellModes.all (·.requiresTarget)

/-- True when the printed spell may be announced with zero targets. -/
def allowsZeroTargets (c : CardDef) : Bool :=
  match c.spellEffect with
  | some e => e.allowsZeroTargets
  | none => false

/-- True when the printed effect or a mode is classified as `k`. -/
def hasCastKind (c : CardDef) (k : SpellCastKind) : Bool :=
  c.spellEffect.any (fun e => e.castKind == k)

/-- True when a modal mode is classified as `k`. -/
def hasModeCastKind (c : CardDef) (k : SpellCastKind) : Bool :=
  c.spellModes.any (fun e => e.castKind == k)

/-- True when this card has an Adventure (CR 715). -/
def hasAdventure (c : CardDef) : Bool :=
  c.adventure.isSome

def manaValue (c : CardDef) : Nat := c.manaCost.manaValue

/-- Basic land types on this card produce the corresponding mana (CR 305.6). -/
def basicLandMana (c : CardDef) : Array Color :=
  c.subtypes.filterMap manaForBasicLandType

/-- `{T}: Add {M}` abilities that produce one mana, from basic land types or
an explicit `tapAddMana` list. -/
def simpleTapAddMana (c : CardDef) : Array ManaType :=
  c.basicLandMana.map ManaType.colored ++ c.tapAddMana

/-- `{T}: Add` types from modeled activated mana abilities. -/
def mshTapAddMana (c : CardDef) : Array ManaType :=
  c.activatedAbilities.foldl (fun acc ab =>
    match ab.effect.resolution with
    | .addMana types (.fixed 1) .none | .addMana types (.fixed 1) .cantNonartifact => acc ++ types
    | _ => acc) #[]

/-- `{T}: Add` types gated on this land entering this turn or a basic land. -/
def enteredOrBasicAddMana (c : CardDef) : Array ManaType :=
  c.tapAddOneOfIfEnteredOrBasic ++ c.mshTapAddMana

/-- True when a `{T}: Add` ability requires this land entered this turn or
a basic land you control. -/
def requiresEnteredOrBasicAdd (c : CardDef) : Bool :=
  !c.tapAddOneOfIfEnteredOrBasic.isEmpty

/-- True when an activated ability adds any color of mana. -/
def hasAnyColorActivatedAdd (c : CardDef) : Bool :=
  c.activatedAbilities.any (fun ab =>
    match ab.effect.resolution with
    | .addMana #[] _ note => note != .none
    | _ => false)

/-- All `{T}: Add` mana types this card can produce. -/
def manaAbilities (c : CardDef) : Array ManaType :=
  c.simpleTapAddMana ++ c.tapAddOneOf ++ c.tapAddManaForEach.map (·.mana) ++
    c.enteredOrBasicAddMana ++
    (if c.tapAddAnyColorEqualToPower || c.tapAddAnyColorForInstantOrSorcery ||
        c.tapAddAnyColor || c.tapSacrificeAddAnyColor ||
        c.tapAddAnyColorForLegendary || c.tapAddTwoAmong.size >= 2 ||
        c.tapAddAnyColorAmongLegendaries || c.tapAddCommanderIdentity ||
        c.hasAnyColorActivatedAdd || c.tapAddChosenColorPerDifferentPower then
      (Color.all.map ManaType.colored).toArray
     else #[])

/-- Lowercase ASCII for comparing Oracle keyword lines to `Keywords.toList`. -/
def lowerAscii (s : String) : String :=
  s.map Char.toLower

/-- Drop a trailing Oracle reminder parenthetical, e.g. `Menace (This creature...)`. -/
def stripReminderParenthetical (s : String) : String :=
  match s.splitOn "(" with
  | [] => s
  | head :: _ => head.trimAscii.copy

/-- True when `line` restates modeled keywords, e.g. `Haste` or `Reach, deathtouch`.
A line that is only a parenthetical (e.g. basic-land `{T}: Add` reminder text)
is not a keyword restatement. -/
def isKeywordRestatement (k : Keywords) (line : String) : Bool :=
  let kw := k.toList
  let cleaned := stripReminderParenthetical ((line.replace "." "").trimAscii.copy)
  if cleaned.isEmpty then false
  else
    let parts := cleaned.splitOn "," |>.map (fun s => s.trimAscii.copy) |>.filter (fun s => !s.isEmpty)
    !parts.isEmpty && parts.all (fun p => kw.any (fun w => w == lowerAscii p))

/-- Gatherer delimiter between an adventurer card's primary and Adventure faces. -/
def isAdventureDelimiter (line : String) : Bool :=
  line == "//ADV//" || line.startsWith "//ADV//"

/-- Drop a leading `//ADV//` marker. The remainder (Adventure name and mana
cost) is kept so leftover Oracle text does not lose printed mana symbols. -/
def stripAdventureDelimiter (line : String) : Option String :=
  if line == "//ADV//" then none
  else if line.startsWith "//ADV//" then
    let rest := (line.drop "//ADV//".length).trimAscii.copy
    if rest.isEmpty then none else some rest
  else some line

/-- `{T}: Add {C}` lines from an explicit `tapAddMana` list. Basic land types
print the parenthetical reminder instead. -/
def explicitTapAddLines (c : CardDef) : List String :=
  c.tapAddMana.toList.map (fun t => s!"\{T}: Add \{{t.letter}}")

/-- `({T}: Add {R}.)` for each basic land type, when no other tap-add list is set. -/
def basicLandReminderLines (c : CardDef) : List String :=
  if !c.tapAddMana.isEmpty then []
  else c.basicLandMana.toList.map fun col => s!"(\{T}: Add \{{col.letter}}.)"

/-- Adventure name, cost, and spell, without the Gatherer `//ADV//` marker. -/
def adventureLines (c : CardDef) : List String :=
  match c.adventure with
  | none => []
  | some a =>
    let header :=
      if a.manaCost.symbols.isEmpty then a.name else s!"{a.name} {a.manaCost}"
    let extra :=
      (if a.additionalCostSacrificeCreature then
        ["As an additional cost to cast this spell, sacrifice a creature."]
       else []) ++
      match a.spellEffect with
      | some e => [e.phrase]
      | none => []
    header :: extra ++ a.extraLines.toList

/-- Prepare-spell name, cost, and effect. -/
def prepareLines (c : CardDef) : List String :=
  match c.prepareFace with
  | none =>
    if c.entersPrepared then ["This creature enters prepared."] else []
  | some a =>
    let header :=
      if a.manaCost.symbols.isEmpty then a.name else s!"{a.name} {a.manaCost}"
    let effect :=
      match a.spellEffect with
      | some e => [e.phrase]
      | none => []
    (if c.entersPrepared then ["This creature enters prepared."] else []) ++
      [header] ++ effect ++ a.extraLines.toList

/-- Empower Jace printed on this spell. -/
def empowerLines (c : CardDef) : List String :=
  match c.empowerJace with
  | some n => [s!"Empower Jace {n}."]
  | none => []

/-- `{T}: Add {U} or {B}.` -/
def tapAddOneOfLines (c : CardDef) : List String :=
  if c.tapAddOneOf.isEmpty then []
  else [s!"\{T}: Add {manaSymbolsText c.tapAddOneOf " or "}."]

/-- `{T}: Add {U} or {B}` gated on entering this turn or a basic land. -/
def tapAddOneOfIfEnteredLines (c : CardDef) : List String :=
  if c.tapAddOneOfIfEnteredOrBasic.isEmpty then []
  else
    [s!"\{T}: Add {manaSymbolsText c.tapAddOneOfIfEnteredOrBasic " or "}. Activate only if this land entered this turn or if you control a basic land."]

/-- `{T}: Add` for each permanent of a listed type. -/
def tapAddForEachLines (c : CardDef) : List String :=
  c.tapAddManaForEach.toList.map TapAddForEach.toNotation

/-- Elf-restricted `{T}: Add` X mana of any color equal to power. -/
def tapAddAnyColorEqualToPowerLine (c : CardDef) : List String :=
  if c.tapAddAnyColorEqualToPower then
    ["{T}: Add X mana of any one color, where X is this creature's power. Spend this mana only to cast Elf spells and activate abilities of Elf sources."]
  else []

/-- Instant/sorcery-restricted `{T}: Add` one mana of any color. -/
def tapAddAnyColorForInstantOrSorceryLine (c : CardDef) : List String :=
  if c.tapAddAnyColorForInstantOrSorcery then
    ["{T}: Add one mana of any color. Spend this mana only to cast an instant or sorcery spell."]
  else []

/-- True when CR 601.2b must announce a sacrifice-or-pay or discard-or-pay
additional cost. -/
def announcesAdditionalCost (c : CardDef) : Bool :=
  c.additionalCostOrPayGeneric.isSome || c.additionalCostDiscardOrPayGeneric.isSome ||
    c.additionalCostBeholdOrPay.isSome

/-- Additional cost that sacrifices an artifact or creature (optionally or pay `{n}`). -/
def additionalCostSacrificeArtifactOrCreatureLine (c : CardDef) : List String :=
  if c.additionalCostSacrificeArtifactOrCreature then
    match c.additionalCostOrPayGeneric with
    | some n =>
      [s!"As an additional cost to cast this spell, sacrifice an artifact or creature or pay \{{n}}"]
    | none =>
      ["As an additional cost to cast this spell, sacrifice an artifact or creature"]
  else
    match c.additionalCostDiscardOrPayGeneric with
    | some n =>
      [s!"As an additional cost to cast this spell, discard a card or pay \{{n}}."]
    | none =>
      match c.additionalCostBeholdOrPay with
      | some (quality, n) =>
        [s!"As an additional cost to cast this spell, behold a {quality} or pay \{{n}}."]
      | none => []

/-- `{T}cycling` and other typecycling, printed as `Mountaincycling {1}`. -/
def activatedNotation (ab : ActivatedAbility) : String :=
  if ab.activateFromHand && ab.cost.discardSource then
    match ab.effect.resolution with
    | .searchLibrary (.returnToHand (.landSubtype t) _) =>
      if t == "Plan" then ab.toNotation else s!"{t}cycling {ab.cost.mana}"
    | _ => ab.toNotation
  else
    ab.toNotation

/-- Spell effect, or `Choose one —` when the spell is modal. -/
def spellLines (c : CardDef) : List String :=
  if !c.spellModes.isEmpty then
    [s!"Choose one — {String.intercalate "; " (c.spellModes.toList.map Effect.toNotation)}"]
  else
    match c.spellEffect with
    | some e => [Effect.toNotation e]
    | none => []

/-- `{T}: Add` mana abilities, additional costs, activated, static, triggered, and spell abilities. -/
def structuredAbilityLines (c : CardDef) : List String :=
  c.explicitTapAddLines ++
  c.basicLandReminderLines ++
  c.tapAddOneOfLines ++
  c.tapAddOneOfIfEnteredLines ++
  c.tapAddForEachLines ++
  c.tapAddAnyColorEqualToPowerLine ++
  c.tapAddAnyColorForInstantOrSorceryLine ++
  c.additionalCostSacrificeArtifactOrCreatureLine ++
  c.activatedAbilities.toList.map activatedNotation ++
  c.staticAbilities.toList.map StaticAbility.toNotation ++
  c.triggeredAbilities.toList.map TriggeredAbility.toNotation ++
  c.adventureLines ++
  c.prepareLines ++
  c.empowerLines ++
  c.spellLines

/-- Modeled ability lines. Keyword-only lines are omitted; those print with
`Keywords`. -/
def leftoverOracleLines (c : CardDef) : List String :=
  c.structuredAbilityLines.filter fun line => !isKeywordRestatement c.keywords line

/-- Abilities to print in the demo, taken from the modeled fields. -/
def abilitiesText (c : CardDef) : String :=
  String.intercalate "; " (structuredAbilityLines c)

/-- Keywords `k` plus leftover Oracle / structured abilities. -/
def keywordsAndAbilitiesOf (c : CardDef) (k : Keywords) : String :=
  String.intercalate " "
    ([toString k, c.abilitiesText].filter (fun s => !s.isEmpty))

/-- Keywords and abilities shown next to a card in the demo. -/
def keywordsAndAbilities (c : CardDef) : String :=
  c.keywordsAndAbilitiesOf c.keywords

def typeLine (c : CardDef) : String :=
  formatTypeLine c.supertypes c.types c.subtypes

/-- One side of a power/toughness box (CR 208.1 / 208.2).
A star plus constant `k` prints as `k+*` (CR 208.2a writes `1+*`). A bare
star, and `*+0`, print as `*`. -/
def renderPrintedStat (n : Option Int) (star : Bool) : String :=
  if star then
    match n with
    | some k => if k == 0 then "*" else s!"{k}+*"
    | none => "*"
  else
    match n with
    | some k => toString k
    | none => "*"

/-- Printed `power/toughness`, if this object has one.
A creature with neither a number nor a star prints `*/*`. Any other object
with neither prints nothing (CR 208.3). -/
def formatPowerToughness (power toughness : Option Int)
    (powerStar toughnessStar isCreature : Bool) : Option String :=
  if power.isNone && toughness.isNone && !powerStar && !toughnessStar then
    if isCreature then some "*/*" else none
  else
    some s!"{renderPrintedStat power powerStar}/{renderPrintedStat toughness toughnessStar}"

def ptString (c : CardDef) : String :=
  (formatPowerToughness c.power c.toughness c.powerStar c.toughnessStar c.isCreature).getD ""

/-- Name, printed mana cost if any, type line, P/T, then keywords and abilities.
Cards with no mana cost (lands, and other objects whose cost cannot be paid)
omit the cost rather than printing `{0}` (CR 202.1b / 118.6). -/
def summary (c : CardDef) : String :=
  String.intercalate " "
    ([c.name, toString c.manaCost, c.typeLine, c.ptString, c.keywordsAndAbilities].filter
      (fun s => !s.isEmpty))

instance : ToString CardDef where
  toString := summary

/-- True when this card itself has improvise (MSH). -/
def hasImprovise (c : CardDef) : Bool :=
  c.staticAbilities.any (fun
    | .improvise => true
    | _ => false)

/-- True when this permanent grants improvise to noncreature spells you cast. -/
def grantsImproviseToNoncreature (c : CardDef) : Bool :=
  c.staticAbilities.any (fun
    | .noncreatureSpellsHaveImprovise => true
    | _ => false)

/-- True when this permanent has a boast ability (MSH). -/
def hasBoast (c : CardDef) : Bool :=
  c.staticAbilities.any (fun
    | .boast => true
    | _ => false)

/-- Sneak alternative cost, if any (MSH). -/
def sneakCost (c : CardDef) : Option ManaCost :=
  c.staticAbilities.foldl (fun acc ab =>
    match acc, ab with
    | none, .sneak cost => some cost
    | acc, _ => acc) none

/-- Equip worthy: legendary non-Villain creature that's red or white. -/
def isWorthy (c : CardDef) : Bool :=
  c.hasSupertype .legendary &&
    !c.hasSubtype "Villain" &&
    (c.colors.contains .red || c.colors.contains .white)

/-- Equip worthy keyword on this Equipment (MSH). -/
def hasEquipWorthy (c : CardDef) : Bool :=
  c.activatedAbilities.any (·.equipWorthy)

/-- Spell, modal, adventure, prepare, and Saga-chapter effects on this face. -/
def spellLikeEffects (c : CardDef) : Array Effect :=
  let modes := if c.spellModes.isEmpty then
      match c.spellEffect with
      | some e => #[e]
      | none => #[]
    else c.spellModes
  let adv := match c.adventure with
    | some a => match a.spellEffect with
      | some e => #[e]
      | none => #[]
    | none => #[]
  let prep := match c.prepareFace with
    | some a => match a.spellEffect with
      | some e => #[e]
      | none => #[]
    | none => #[]
  let chapters := match c.saga with
    | some s => s.chapters.filterMap (·.chapterEffect)
    | none => #[]
  modes ++ adv ++ prep ++ chapters

/-- Why this face is not fully parsed or its effects are not fully modelled.
Does not look at `otherFace`. -/
def faceModellingError? (c : CardDef) : Option String :=
  let unparsed : Option String :=
    c.staticAbilities.foldl (fun acc ab =>
      match acc, ab with
      | some e, _ => some e
      | none, .printed line => some s!"unparsed rules line on {c.name}: {line}"
      | none, _ => none) none
      <|> (c.adventure.bind fun a =>
        a.extraLines[0]?.map fun line => s!"unparsed rules line on {a.name}: {line}")
      <|> (c.prepareFace.bind fun a =>
        a.extraLines[0]?.map fun line => s!"unparsed rules line on {a.name}: {line}")
  let spell : Option String :=
    c.spellLikeEffects.foldl (fun acc e =>
      match acc with
      | some err => some err
      | none =>
        if e.resolution.doesNothingAsSpell then
          some s!"{c.name} is not fully modelled: {e.toNotation}"
        else none) none
  let activated : Option String :=
    c.activatedAbilities.foldl (fun acc ab =>
      match acc with
      | some err => some err
      | none =>
        if ab.effect.resolution.doesNothingAsActivated then
          some s!"{c.name} activated ability is not fully modelled: {ab.effect.toNotation}"
        else none) none
  unparsed <|> spell <|> activated

/-- Why `c` or its back face is not fully parsed or fully modelled.
`none` when every rules line was recognized and every spell, mode,
adventure, prepare face, Saga chapter, and activated ability resolves. -/
def modellingError? (c : CardDef) : Option String :=
  c.faceModellingError? <|> (c.otherFace.bind faceModellingError?)

end CardDef

namespace AdventureFace

/-- Characteristics used while this card is on the stack as an Adventure (CR 715.3b). -/
def toCardDef (a : AdventureFace) : CardDef := {
  name := a.name
  manaCost := a.manaCost
  types := a.types
  subtypes := a.subtypes
  spellEffect := a.spellEffect
  staticAbilities := a.extraLines.map StaticAbility.printed
  empowerJace := a.empowerJace
  additionalCost := a.additionalCost
}

/-- True when this Adventure's effect is classified as `k`. -/
def hasCastKind (a : AdventureFace) (k : SpellCastKind) : Bool :=
  a.spellEffect.any (fun e => e.castKind == k)

end AdventureFace

/-- Constructed-play four-of rule applies to non-basic-land English names (CR 100.2a). -/
def isBasicLandCard (c : CardDef) : Bool :=
  c.isLand && c.hasSupertype .basic

/-- A land card with the given land type (CR 205.3i / 305.7). -/
def isLandTypeCard (c : CardDef) (landType : String) : Bool :=
  c.isLand && c.hasSubtype landType

/-- A card with the Forest land type (CR 205.3i / 305.7). -/
def isForestCard (c : CardDef) : Bool :=
  isLandTypeCard c "Forest"

end Mtg.Engine
