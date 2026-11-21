import Mtg.Engine.Card.ChapterEffects
import Mtg.Engine.Card.SpellEffects
import Mtg.Engine.Card.TriggerEffects

/-!
# Printed triggered abilities (CR 603)

Named constructors for the printed triggered-ability wordings and their
Oracle-text rendering.
-/

namespace Mtg.Engine

namespace TriggeredAbility

/-- Build a triggered ability from a `TriggerPattern` and a unified `Effect`. -/
def mkTrigger (pattern : TriggerPattern) (effect : Effect)
    (word : TriggerWord := pattern.defaultWord)
    (grouping : BatchGrouping := .perOccurrence)
    (interveningIf? : Option Condition := none)
    (activeZones : Array ZoneKind := #[.battlefield])
    (limit : TriggerLimit := .unlimited)
    (modes : Array Effect := #[]) : TriggeredAbility :=
  { word, pattern, grouping, interveningIf?, activeZones, limit, effect, modes }

/-- Build a triggered ability from a `SharedTrigger` payload and explicit pattern/overrides. -/
private def mkShared (pattern : TriggerPattern) (s : SharedTrigger)
    (word? : Option TriggerWord := none)
    (grouping? : Option BatchGrouping := none)
    (interveningIf? : Option Condition := none)
    (activeZones? : Option (Array ZoneKind) := none)
    (limit? : Option TriggerLimit := none)
    (untargeted : Bool := false)
    (allowsZeroTargets : Bool := false) : TriggeredAbility :=
  s.toTriggeredAbility (pattern? := some pattern) (word? := word?)
    (grouping? := grouping?) (interveningIf? := interveningIf?)
    (activeZones? := activeZones?) (limit? := limit?)
    (untargeted := untargeted) (allowsZeroTargets := allowsZeroTargets)

/-- Construct a triggered ability directly from a `TriggerPattern`, sentence
phrase, and `Resolution`. -/
def ofPattern (pattern : TriggerPattern) (phrase : String) (r : Resolution)
    (spec : TargetSpec := .none) (allowsZeroTargets := false) (maxTargets := 0)
    (grouping : BatchGrouping := .perOccurrence)
    (interveningIf? : Option Condition := none)
    (activeZones : Array ZoneKind := #[.battlefield])
    (limit : TriggerLimit := .unlimited)
    (modes : Array Effect := #[])
    (word : TriggerWord := pattern.defaultWord) : TriggeredAbility :=
  { word, pattern, grouping, interveningIf?, activeZones, limit, modes,
    effect := { targeting := .of spec, resolution := r, phrase, allowsZeroTargets, maxTargets } }

/-- Catalog aliases for reusable triggered abilities. -/
def onEnterScry (n : Nat) : TriggeredAbility := mkShared .thisEnters (.scry n)
def onAttackScry (n : Nat) : TriggeredAbility := mkShared .thisAttacks (.scry n)
def onAttackWithElvesScry (n : Nat) : TriggeredAbility :=
  mkShared (.youAttackWithSubtype .elf) (.scry n) (grouping? := some .oncePerBatch)
def onOneOrMoreOtherCreaturesDieScry (n : Nat) : TriggeredAbility :=
  mkShared .otherCreaturesDie (.scry n) (grouping? := some .oncePerBatch)
def onCastColorScry (c : Color) (n : Nat) : TriggeredAbility :=
  mkShared (.youCastColor c) (.scry n)
def onEnterDraw (n : Nat) : TriggeredAbility := mkShared .thisEnters (.draw n)
def onDiesDraw (n : Nat) : TriggeredAbility := mkShared .thisDies (.draw n)
def onYouAttackDraw : TriggeredAbility :=
  mkShared .youAttack (.draw 1) (grouping? := some .oncePerBatch)
def onYourEndStepDraw : TriggeredAbility := mkShared .stepYourEndStep (.draw 1)
def onBecomesTargetDraw : TriggeredAbility := mkShared .thisBecomesTargetByOpponent (.draw 1)
def onArtifactYouControlEntersDraw : TriggeredAbility :=
  mkShared .artifactYouControlEnters (.draw 1)
def onTheRingTemptsYouDraw (n : Nat) : TriggeredAbility :=
  mkShared .theRingTemptsYou (.draw n)
def onChooseRingBearerDraw : TriggeredAbility :=
  mkShared .youChooseRingBearer (.draw 1)
def onCombatDamageDraw (n : Nat) : TriggeredAbility :=
  mkShared .thisDealsCombatDamageToPlayer (.draw n)
def onEnterCreateTokens (kind : TokenSpec) (n : Nat) (tapped : Bool := false) :
    TriggeredAbility :=
  mkShared .thisEnters (.createTokens kind n tapped)
def onYourUpkeepCreateTokens (kind : TokenSpec) (n : Nat) : TriggeredAbility :=
  mkShared .stepYourUpkeep (.createTokens kind n)
def onLandYouControlEntersCreateTokens (kind : TokenSpec) (n : Nat) :
    TriggeredAbility :=
  mkShared .landYouControlEnters (.createTokens kind n)
def onDiesCreateTokens (kind : TokenSpec) (n : Nat) : TriggeredAbility :=
  mkShared .thisDies (.createTokens kind n)
def onYouDrawSecondCreateTokens (kind : TokenSpec) : TriggeredAbility :=
  mkShared (.drawCard .you) (.createTokens kind 1) (limit? := some (.nthEachTurn 2))
def onCastColorCreateTokens (c : Color) (kind : TokenSpec) (n : Nat) :
    TriggeredAbility :=
  mkShared (.youCastColor c) (.createTokens kind n)
def onEnterOrAttackCreateWall : TriggeredAbility :=
  mkShared .enterOrAttack (.createTokens .wall 1)
def onEnterAmassGoblins (n : Nat) : TriggeredAbility :=
  mkShared .thisEnters (.amass n)
def onDiesAmassGoblins (n : Nat) : TriggeredAbility :=
  mkShared .thisDies (.amass n)
def onYouAttackAmassGoblins (n : Nat) : TriggeredAbility :=
  mkShared .youAttack (.amass n) (grouping? := some .oncePerBatch)
def onCastNoncreatureAmassGoblins (n : Nat) : TriggeredAbility :=
  mkShared .youCastNoncreature (.amass n)
def onEnterOrAttackAmassGoblins (n : Nat) : TriggeredAbility :=
  mkShared .enterOrAttack (.amass n)
def onCreatureCardLeavesYourGyAmassGoblins (n : Nat) : TriggeredAbility :=
  mkShared .creatureCardLeavesYourGy (.amass n)
def onEnterRecruit : TriggeredAbility := mkShared .thisEnters .recruit
def onDiesRecruit : TriggeredAbility := mkShared .thisDies .recruit
def onEnterOrAttackRecruit : TriggeredAbility := mkShared .enterOrAttack .recruit
def onYouAttackRecruit : TriggeredAbility :=
  mkShared .youAttack .recruit (grouping? := some .oncePerBatch)
def onEnterDealDividedDamage (amount maxTargets : Nat) : TriggeredAbility :=
  mkShared .thisEnters (.dividedDamage amount maxTargets)
def onEnterOrAttackDealDividedDamage (amount maxTargets : Nat) : TriggeredAbility :=
  mkShared .enterOrAttack (.dividedDamage amount maxTargets)
def onEnterPlusOneOnCreature : TriggeredAbility :=
  mkShared .thisEnters (.onPermanent .creature (.plusOne 1))
def onEnterOrAttackPlusOneOnCreature : TriggeredAbility :=
  mkShared .enterOrAttack (.onPermanent .creature (.plusOne 1))
def onLandYouControlEntersPlusOnePlusOne : TriggeredAbility :=
  mkShared .landYouControlEnters (.onPermanent .creatureYouControl (.plusOne 1))
def onCombatPlusOneOnCreatureYouControl : TriggeredAbility :=
  mkShared .stepYourBeginCombat (.onPermanent .creatureYouControl (.plusOne 1))
def onEnterAttachToSubtype (subtype : String) : TriggeredAbility :=
  mkShared .thisEnters (.attachTo (.creatureYouControlSubtype (CardSubtype.ofOracleD subtype)))
def onEnterAttachToLegendary : TriggeredAbility :=
  mkShared .thisEnters (.attachTo .legendaryCreatureYouControl)
def onEnterAttachToCreatureYouControl : TriggeredAbility :=
  mkShared .thisEnters (.attachTo .creatureYouControl)
def onEnterTargetOpponentSacrificesCreature : TriggeredAbility :=
  mkShared .thisEnters .opponentSacrificesCreature
def onEnterTargetOpponentSacrifices : TriggeredAbility :=
  onEnterTargetOpponentSacrificesCreature
def onDrawSecondPlusOne : TriggeredAbility :=
  mkShared (.drawCard .you) (.onSource (.plusOne 1)) (limit? := some (.nthEachTurn 2))
def onDrawPlusOne : TriggeredAbility :=
  mkShared (.drawCard .you) (.onSource (.plusOne 1))
def onGainLifePlusOne : TriggeredAbility :=
  mkShared (.gainLife .you) (.onSource (.plusOne 1))
def onAnotherArtifactEntersPlusOne : TriggeredAbility :=
  mkShared .anotherArtifactYouControlEnters (.onSource (.plusOne 1))
/-- CR 603.4 intervening-if Ferocious trigger at beginning of combat (rechecked on resolution). -/
def onYourBeginCombatFerociousPlusOne : TriggeredAbility :=
  mkShared .stepYourBeginCombat (.onSource (.plusOne 1))
    (interveningIf? := some (condControlCreaturePowerAtLeast 4))
def onEquippedAttacksAloneDrawLoseLife : TriggeredAbility :=
  mkTrigger .equippedAttacksAlone Effect.seqDrawAndLoseLife
/-- CR 603.2 `"while you control..."` attack trigger (checked at trigger time, not on resolution). -/
def onYouAttackFerociousDrawLoseLife : TriggeredAbility :=
  mkTrigger (.whenCond .youAttack (condControlCreaturePowerAtLeast 4))
    Effect.seqDrawAndLoseLife (grouping := .oncePerBatch)
def onCastWithTreasureDrawLoseLife : TriggeredAbility :=
  mkTrigger .youCastWithTreasure Effect.seqDrawAndLoseLife
def onYourEndStepDrawLoseLife : TriggeredAbility :=
  mkTrigger .stepYourEndStep Effect.seqDrawAndLoseLife
def onEnterConnive : TriggeredAbility := mkShared .thisEnters .connive
def onAttackConnive : TriggeredAbility := mkShared .thisAttacks .connive
def onYouCastColorFromHandConnive (color : Color) : TriggeredAbility :=
  mkShared (.youCastColorFromHand color) .connive
def onEquippedCreatureYouControlAttacksConnive : TriggeredAbility :=
  mkShared .equippedCreatureYouControlAttacks .connive
def onCombatTargetYouControlConnives : TriggeredAbility :=
  mkShared .stepYourBeginCombat (.connive (.target .creatureYouControl))
def onEnterExileOppNonlandUntilLeaves : TriggeredAbility :=
  mkShared .thisEnters (.exileUntilLeaves .oppNonland)
def onEnterExileOppTappedUntilLeaves : TriggeredAbility :=
  mkShared .thisEnters (.exileUntilLeaves .oppTappedCreature)
def onAttackMayExileDefenderUntilLeaves : TriggeredAbility :=
  mkShared .thisAttacks (.exileUntilLeaves .defendingPlayerCreature) (allowsZeroTargets := true)
def onEnterGainLife (n : Nat) : TriggeredAbility := mkShared .thisEnters (.gainLife n)
/-- CR 603.2 `"while you control..."` attack trigger (checked at trigger time, not on resolution). -/
def onAttackFerociousGainLife (n : Nat) : TriggeredAbility :=
  mkShared (.whenCond .thisAttacks (condControlCreaturePowerAtLeast 4)) (.gainLife n)
def onEnterTargetGets (power toughness : Int) : TriggeredAbility :=
  mkShared .thisEnters (.onPermanent .creature (.pump power toughness))
def onDiesOppCreatureGets (power toughness : Int) : TriggeredAbility :=
  mkShared .thisDies (.onPermanent .oppCreature (.pump power toughness))
def onCastColorPump (color : Color) (power toughness : Int) : TriggeredAbility :=
  mkShared (.youCastColor color) (.onPermanent .creature (.pump power toughness))
def onLandYouControlEntersGets (power toughness : Int) : TriggeredAbility :=
  mkShared .landYouControlEnters (.onSource (.pump power toughness))
def onAttackFerociousSourceGets (power toughness : Int) : TriggeredAbility :=
  mkShared (.whenCond .thisAttacks (condControlCreaturePowerAtLeast 4))
    (.onSource (.pump power toughness))
def onAnotherElfYouControlEntersGets1 : TriggeredAbility :=
  mkShared (.anotherSubtypeYouControlEnters .elf) (.onSource (.pump 1 1))
def onArtifactYouControlEntersDrawOnce : TriggeredAbility :=
  mkShared .artifactYouControlEnters (.draw 1) (limit? := some .onceEachTurn)
def onActivateCreatureAbilityDrawOnce : TriggeredAbility :=
  mkShared .youActivateCreatureAbility (.draw 1) (limit? := some .onceEachTurn)
def onAnotherSubtypeOrEquipmentEntersDrawOnce (subtype : String) : TriggeredAbility :=
  mkShared (.anotherSubtypeOrEquipmentYouControlEnters (CardSubtype.ofOracleD subtype))
    (.draw 1) (limit? := some .onceEachTurn)
def onEachEndStepDrawIfGainedLife (n : Nat) : TriggeredAbility :=
  mkShared .stepEachEndStep (.draw 1) (interveningIf? := some (condGainedLifeAtLeast n))
def onThisOrNontokenSubtypeEntersCreateTokens (subtype : String) (kind : TokenSpec)
    (n : Nat) : TriggeredAbility :=
  mkShared (.thisOrNontokenSubtypeYouControlEnters (CardSubtype.ofOracleD subtype))
    (.createTokens kind n)
def onThisOrAnotherSubtypeEntersCreateTokens (subtype : String) (kind : TokenSpec)
    (n : Nat) : TriggeredAbility :=
  mkShared (.thisOrAnotherSubtypeYouControlEnters (CardSubtype.ofOracleD subtype))
    (.createTokens kind n)
def onSubtypeYouControlCombatDamageCreateTokens (subtype : String) (kind : TokenSpec)
    (n : Nat) : TriggeredAbility :=
  let sub := CardSubtype.ofOracleD subtype
  mkShared
    (.damageDealt
      (.all #[.hasSubtype (.literal sub), .controlledBy .you])
      (.playerOrObject .any { zones := .battlefield, pred := .hasType .battle })
      (combatOnly := true))
    (.createTokens kind n)
def onOpponentDrawsSecondCreateTreasure : TriggeredAbility :=
  mkShared (.drawCard .opponent) (.createTokens .treasure 1) (limit? := some (.nthEachTurn 2))
def onOpponentCastsFirstNoncreatureRecruit : TriggeredAbility :=
  mkShared .opponentCastsFirstNoncreature (.recruit .you)
def onCastColorDamageOpponent (color : Color) (n : Nat) : TriggeredAbility :=
  mkShared (.youCastColor color) (.damageEachOpponent n)
def onCastGreenOrForestEntersPlusOne : TriggeredAbility :=
  mkShared .castGreenOrForestEnters (.onPermanent .creatureYouControl (.plusOne 1))
def onAttackOtherGets2AndTrample : TriggeredAbility :=
  mkShared .thisAttacks (.onPermanent .anotherCreatureYouControl (.pumpAndTrample 2 0))
def onEnterMayDiscardDraw (n : Nat) : TriggeredAbility :=
  mkShared .thisEnters (.mayTo .discard (.draw n))
def onCastInstantOrSorceryDealDamageToEachOpponent (amount : Nat) : TriggeredAbility :=
  mkShared .youCastInstantOrSorcery (.damageEachOpponent amount) (untargeted := true)
def onEnterEachOpponentDiscards : TriggeredAbility :=
  mkShared .thisEnters .opponentDiscards
def onEnterExileTop : TriggeredAbility := mkShared .thisEnters .exileTop
def onAttackTargetGainsKeywords (k : Array KeywordAbility) : TriggeredAbility :=
  mkShared .thisAttacks (.onPermanent .attackingCreature (.grantKeywords k))
def onDrawSecondMillPlayer (n : Nat) : TriggeredAbility :=
  mkShared (.drawCard .you) (.millPlayer n) (limit? := some (.nthEachTurn 2))
def onAnotherGoblinOrcArmyDiesExileTop : TriggeredAbility :=
  mkShared .anotherGoblinOrcArmyYouControlDies .exileTop
def onAnotherSubtypeEntersPlusOneOnSource (subtype : String) (n : Nat) :
    TriggeredAbility :=
  mkShared (.anotherSubtypeYouControlEnters (CardSubtype.ofOracleD subtype))
    (.onSource (.plusOne n))
def onOpponentCastsAmassOrcs (n : Nat) : TriggeredAbility :=
  mkShared .opponentCastsSpell (.amass n .orc)
def onCreatureYouControlAttacksAloneInvestigate : TriggeredAbility :=
  mkShared .creatureYouControlAttacksAlone .investigate
def onCreatureYouControlAttacksAlonePump (power toughness : Int) : TriggeredAbility :=
  mkShared .creatureYouControlAttacksAlone (.pumpCause power toughness)
def onEnterTargetOpponentDiscards (n : Nat) : TriggeredAbility :=
  mkShared .thisEnters (.opponentDiscards n .target)
def onEquipmentYouControlEntersDraw : TriggeredAbility :=
  mkShared .equipmentYouControlEnters (.draw 1)
def onEnterSearchForest : TriggeredAbility := mkShared .thisEnters .searchLibrary
def onEnterSearchBasicToHand : TriggeredAbility := mkShared .thisEnters .searchBasicLandToHand
def onEnterEachPlayerSacrificesCreature : TriggeredAbility :=
  mkShared .thisEnters .eachPlayerSacrificesCreature
def onEnterMayExileAnotherCreature : TriggeredAbility :=
  mkShared .thisEnters (.exileTarget .anotherCreature) (allowsZeroTargets := true)
def onEnterReturnCreatureFromGyToHand : TriggeredAbility :=
  mkShared .thisEnters .returnCreatureFromGyToHand
def onCombatDamageToPlayerLoot : TriggeredAbility :=
  mkTrigger .thisDealsCombatDamageToPlayer (Effect.seqDrawThenDiscard 1)
def onAttackFerociousPlusOneEach : TriggeredAbility :=
  mkShared (.whenCond .thisAttacks (condControlCreaturePowerAtLeast 4)) .plusOneEachYouControl
def onAttackFerociousSourceGetsAndTeamTrample (power : Int) : TriggeredAbility :=
  mkTrigger (.whenCond .thisAttacks (condControlCreaturePowerAtLeast 4))
    (Effect.seqSourceGetsAndTeamTrample power)
def onEnterOrAttackHoneEachEquipment : TriggeredAbility :=
  mkShared .enterOrAttack .honeEachEquipment
def onEnterOrAttackPlusOneEachOtherGainLife : TriggeredAbility :=
  mkShared .enterOrAttack .plusOneEachOtherGainLife
def onLandYouControlEntersBecomePT (power toughness : Int) : TriggeredAbility :=
  mkShared .landYouControlEnters (.becomePT power toughness)
def onCastNoncreaturePumpAndDamageOpponents (n : Nat) : TriggeredAbility :=
  mkTrigger .youCastNoncreature (Effect.seqPumpAndDamageOpponents n)
def onDrawSecondPlusOneLifelink : TriggeredAbility :=
  mkTrigger (.drawCard .you) (Effect.seqPlusOneAndLifelink .creature) (limit := .nthEachTurn 2)
def onYouAttackPumpTargetPerPlains : TriggeredAbility :=
  mkShared .youAttack .pumpTargetPerPlains (grouping? := some .oncePerBatch)
def onAnotherLegendarySubtypeEntersLoot (subtype : String) : TriggeredAbility :=
  mkTrigger
    (.permanentEnters (.all #[
      .otherThan .this, .hasSupertype .legendary,
      .hasSubtype (.literal (CardSubtype.ofOracleD subtype)), .controlledBy .you]))
    (Effect.seqDrawThenDiscard 2)
def onRingTemptsMayDiscardDraw (n : Nat) : TriggeredAbility :=
  mkShared .theRingTemptsYou (.mayDiscardHandDraw n)
def onScryPumpSelfForEachLookedAt : TriggeredAbility :=
  mkShared .youScry .pumpByLookedAt
def onScryPumpAndUnblockableOnce : TriggeredAbility :=
  mkTrigger .youScry Effect.seqPumpAndUnblockable (limit := .onceEachTurn)
def onAttackPumpByGreatestPower : TriggeredAbility :=
  mkShared .thisAttacks .pumpGreatestPower
def onBecomesBlockedDeal1ToBlockers : TriggeredAbility :=
  mkShared .thisBecomesBlocked (.damageBlockers 1)
def onAttackPumpForEachOtherCreature : TriggeredAbility :=
  mkShared .thisAttacks .pumpForEachOtherCreature
def onAttackWithTwoOrMoreGrantFlying : TriggeredAbility :=
  mkShared .youAttackWithTwoOrMoreToPlayer
    (.onPermanent .attackingCreatureWithoutFlying (.grantKeywords #[Keyword.flying]))
    (grouping? := some .perPlayerInBatch)
def onLeaveReturnExiled : TriggeredAbility := mkShared .thisLeaves .returnLinkedExile
def onEnterCreateThenAttach (kind : TokenSpec) : TriggeredAbility :=
  mkShared .thisEnters (.createThenAttach kind)
def onEnterAmassThenAttach (n : Nat) : TriggeredAbility :=
  mkShared .thisEnters (.amass n (attachSource := true))
def onEnterGainLifeSearchBasicOnTop (n : Nat) : TriggeredAbility :=
  mkShared .thisEnters (.gainLifeSearchBasicOnTop n)
def onYourFirstMainAddMana (types : Array ManaType) : TriggeredAbility :=
  mkShared .stepYourFirstMain (.addMana types)
def onEnterCreateAxe : TriggeredAbility := mkShared .thisEnters .createAxe
def onLandYouControlEntersTapOrUntap : TriggeredAbility :=
  mkShared .landYouControlEnters .tapOppOrUntapYours
def onEnterGainControlOppUntilEot : TriggeredAbility :=
  mkShared .thisEnters .gainControlOppUntilEot
def onEnterCreateAxeAttach : TriggeredAbility :=
  mkShared .thisEnters (.createAxe (attach := true))
def onDiesAmassGoblinsEqualPower : TriggeredAbility :=
  mkShared .thisDies (.amass 0 (amount := .sourcePower))
def onLandYouControlEntersPayReturnFromGy : TriggeredAbility :=
  mkShared .landYouControlEnters .payReturnFromGy (activeZones? := some #[.graveyard])
def onYouSacrificeTokenOppLosesLife : TriggeredAbility :=
  mkShared .youSacrificeToken (.targetOpponentLosesLife 1)
def onLandYouControlEntersPlusOneVigilance : TriggeredAbility :=
  mkTrigger .landYouControlEnters (Effect.seqPlusOneVigilance 2)
def onCastNoncreatureMayDrawXDiscard2 : TriggeredAbility :=
  mkShared .youCastNoncreature (.may (.drawXDiscard 2))
def onLandYouControlEntersDrawPlusOneSource : TriggeredAbility :=
  mkTrigger .landYouControlEnters Effect.seqDrawPlusOneSource
def onArmyCombatDamageRingTempts : TriggeredAbility :=
  mkShared .armyYouControlCombatDamageToPlayer .ringTempts
def onAttackSetOtherBasePT : TriggeredAbility := mkShared .thisAttacks .setOtherBasePT
def onEnterOrAttackReturnElfGainLife : TriggeredAbility :=
  mkShared .enterOrAttack .returnElfGainLife
def onDiesDealDamageEqualToPowerToOppCreature : TriggeredAbility :=
  mkShared .thisDies .damageFromLastKnownPower
def onEnterExileOppGyCardOppsLoseLife (life : Nat) : TriggeredAbility :=
  mkTrigger .thisEnters (Effect.seqExileOppGyCardOppsLoseLife life)
def onEnterCreaturesYouControlGetAndFirstStrike (power : Int) : TriggeredAbility :=
  mkTrigger .thisEnters (Effect.seqCreaturesPumpAndFirstStrike power)
def onAnotherCreatureYouControlPowerAtMostEntersMayPayDraw (power : Int)
    (generic : Nat) : TriggeredAbility :=
  mkShared
    (.permanentEnters (.all #[
      .otherThan .this, .hasType .creature, .controlledBy .you, .stat .power .le (.const power)]))
    (.mayPayGenericDraw generic)
def onEnterDrawThenBottomIfNoLegendary : TriggeredAbility :=
  mkShared .thisEnters .drawThenBottomIfNoLegendary
def onYourEndStepRemoveHopeDrawSac : TriggeredAbility :=
  mkShared .stepYourEndStep .removeHopeDrawSac
def onAttackTapHumansDraw : TriggeredAbility := mkShared .thisAttacks .tapHumansDraw
def onEnterUntapOtherPlusOneIfSubtype (subtype : String) : TriggeredAbility :=
  mkTrigger .thisEnters (Effect.seqUntapPlusOneIfSubtype subtype)
def onEnterDestroyOppArtifactsEnchantmentsGainLife : TriggeredAbility :=
  mkShared .thisEnters .destroyOppArtifactsEnchantmentsGainLife
def onAttackDamageEqualSubtypeToEachOpponent (subtype : String) : TriggeredAbility :=
  mkShared .thisAttacks (.damageEqualSubtypeToEachOpponent (CardSubtype.ofOracleD subtype))
def onAttackDamageEqualTreasures : TriggeredAbility :=
  mkShared .thisAttacks .damageEqualTreasures
def onPlayerCastsSecondSpellLoseLifeCreateTreasure : TriggeredAbility :=
  mkTrigger .anyPlayerCastsSecondSpell Effect.seqLoseLifeCreateTreasure
def onEnterDealDamageDestroyIfSubtype (n : Nat) (subtype : String) : TriggeredAbility :=
  mkShared .thisEnters (.dealDamageDestroyIfSubtype n (CardSubtype.ofOracleD subtype))
def onEnterAttachTargetEquipment : TriggeredAbility :=
  mkShared .thisEnters .attachEquipmentToCreature
def onAttackDefenderSacsLeastPower : TriggeredAbility :=
  mkShared .thisAttacks .defenderSacsLeastPower
def onEnterReturnOtherPlusOne : TriggeredAbility :=
  mkShared .thisEnters .returnOtherPlusOne
def onEnterLookAtTopRevealTypes (n : Nat) (types : Array String) : TriggeredAbility :=
  mkShared .thisEnters (.lookAtTopRevealTypes n types)
def onEnterCreateTappedTreasuresEqualOppArtifacts : TriggeredAbility :=
  mkShared .thisEnters .createTappedTreasuresEqualOppArtifacts
def onCombatDamagePutNonlandMvAtMost (mv : Nat) : TriggeredAbility :=
  mkShared .thisDealsCombatDamageToPlayerOrBattle (.putNonlandMvAtMostFromGy mv)
def onEachCombatOthersGetAndOppsGet (subtypes : Array String)
    (power toughness oppP oppT : Int) : TriggeredAbility :=
  mkShared .stepEachBeginCombat
    (.othersGetAndOppsGet (CardSubtype.ofSubtypes subtypes) power toughness oppP oppT)
def onCombatDamageWolfPlusOneOrTreasure : TriggeredAbility :=
  mkShared .thisDealsCombatDamageToPlayer .wolfPlusOneOrTreasure
def onYourBeginCombatTrampleCounterBecomeBear : TriggeredAbility :=
  mkShared .stepYourBeginCombat .trampleCounterBecomeBear
def onEnterMillThenSubtypeToHand (n : Nat) (subtype : String) : TriggeredAbility :=
  mkShared .thisEnters (.millThenSubtypeToHand n (CardSubtype.ofOracleD subtype))
def onEnterExileOppNonlandEachUntilLeaves : TriggeredAbility :=
  mkShared .thisEnters .exileOppNonlandEachUntilLeaves
def onCastCreaturePlusOneEqualMv : TriggeredAbility :=
  mkShared .youCastCreature .plusOneEqualLastKnownMv
def onMountainEntersQuestThenDragon : TriggeredAbility :=
  mkShared .mountainYouControlEnters .mountainQuestDragon
def onEquippedCombatDamageTreasuresPerChosenType : TriggeredAbility :=
  mkShared .equippedDealsCombatDamageToPlayer .treasuresPerChosenType
def onNontokenYouControlDiesRevealCreature : TriggeredAbility :=
  mkShared .nontokenCreatureYouControlDies .revealUntilCreature (limit? := some .onceEachTurn)
def onAttackMaySacAnotherPlusOneEqualPower : TriggeredAbility :=
  mkShared .thisAttacks .attackSacPlusOneEqualPower
def onEnterLootLandEntersTapped : TriggeredAbility :=
  mkShared .thisEnters .lootLandEntersTapped
def onPlayerLosesLifeMillThatMany : TriggeredAbility :=
  mkShared (.loseLife .any) .millThatManyLost
def onDiesDrawPerFatGraveyard : TriggeredAbility :=
  mkShared .thisDies .drawPerFatGraveyard
def onEnterMaySacDrawTreasure : TriggeredAbility :=
  mkShared .thisEnters .maySacDrawTreasure
def onEquippedAttacksPlusOneEachIfCityBlessing : TriggeredAbility :=
  mkShared .equippedAttacks (.plusOneEachYouControl .citysBlessing)
def onYourBeginCombatCastInstantSorceryFromHand : TriggeredAbility :=
  mkShared .stepYourBeginCombat .castInstantSorceryFromHand
def onEquippedCombatDamageCastInstantSorcery : TriggeredAbility :=
  mkShared .equippedDealsCombatDamageToPlayer .castInstantSorceryMvAtMost
def onCastSecondSpellMillThenCopy : TriggeredAbility :=
  mkShared .youCastSecondSpell .millThenCopy
def onCombatAnotherGetsSourcePower : TriggeredAbility :=
  mkShared .stepYourBeginCombat .pumpTargetBySourcePower
def onCombatCreateAlienPerInvasion : TriggeredAbility :=
  mkShared .stepYourBeginCombat .createAlienPerInvasion
def onCombatMayPutArtifactAttachEquipment : TriggeredAbility :=
  mkShared .stepYourBeginCombat .mayPutArtifactAttachEquipment
def onCastCascade : TriggeredAbility :=
  mkShared .thisCast .cascade (activeZones? := some #[.stack])
def onWard (cost : CostSpec) : TriggeredAbility :=
  ofPattern .thisBecomesTargetByOpponent "Ward" (.frc (.ward cost))
/-- Path of Ancestry mana-spent commander creature-type scry trigger. -/
def onManaSpentCastCommanderTypeScry (n : Nat := 1) : TriggeredAbility :=
  { word := .when
    pattern := manaSpentCastCommanderCreaturePattern
    effect := Effect.scry n }
/-- CR 702.176a Impending end-step time-counter removal trigger. -/
def impendingEndStep : TriggeredAbility :=
  ofPattern .stepYourEndStep
    "At the beginning of your end step, if this permanent's impending cost was paid and it has a time counter on it, remove a time counter from it."
    (.removeCounters .time .source)
    (interveningIf? := some condImpendingPaidWithTimeCounter)
def onTokenYouControlEntersBelladonna : TriggeredAbility :=
  mkShared .tokenYouControlEnters .belladonnaTokenReward
def onEnterBolgMaySacrifice : TriggeredAbility :=
  mkShared .thisEnters .bolgMaySacrifice
def onBolgDealSacrificedPower : TriggeredAbility :=
  mkShared .youSacrificeOtherCreature .bolgDealSacrificedPower (word? := some .when)
def onEquippedAttacksCreateSpirits : TriggeredAbility :=
  mkShared .equippedAttacks .createSpiritsForEquipped
def onCombatDamageCreateTreasuresEqualPlayerArtifacts : TriggeredAbility :=
  mkShared .thisDealsCombatDamageToPlayer .createTreasuresEqualDamagedPlayerArtifacts
def onEnterOrOpponentDrawsDeal1AmassOrcs : TriggeredAbility :=
  mkShared .enterOrOpponentDrawsExceptFirst .deal1ThenAmassOrcs
def onAttackWithTotalPowerUntapExtraCombat (n : Int) : TriggeredAbility :=
  mkShared (.youAttackWithTotalPower n) (.untapAttackersExtraCombat n)
    (grouping? := some .oncePerBatch) (limit? := some .onceEachTurn)
def onAnotherCreatureYouControlEntersAlliance : TriggeredAbility :=
  mkShared .anotherCreatureYouControlEnters .allianceMode
def onEnterDestroyOtherAmassControllerPower : TriggeredAbility :=
  mkShared .thisEnters .destroyOtherAmassControllerPower
def onOpponentCastsChosenParityModes : TriggeredAbility :=
  mkShared .opponentCastsMatchingParity .gollumMode
def onThisOrAnotherSubtypeEntersDiscardHand (subtype : String) : TriggeredAbility :=
  mkShared (.thisOrAnotherSubtypeYouControlEnters (CardSubtype.ofOracleD subtype))
    .discardHandDrawDamageIfStory
def onAttackCastFromGyArtifactInstantSorcery : TriggeredAbility :=
  mkShared .thisAttacks .castFromGyArtifactInstantSorcery
def onAttackEquippedGainDoubleStrike : TriggeredAbility :=
  mkShared .thisAttacks .equippedAttackersGainDoubleStrike
def onEnterTapEnchantedRemoveCounters : TriggeredAbility :=
  mkShared .thisEnters .tapEnchantedRemoveCounters
def onDiesRevealTopPutRandomCreature (n : Nat) : TriggeredAbility :=
  mkShared .thisDies (.revealTopPutRandomCreature n)
def onYourBeginCombatIfDrawnTwoPumpFirstStrike : TriggeredAbility :=
  mkShared .stepYourBeginCombat .beginCombatIfDrawnTwoPump
def onEnterHonePerOppCreaturesAttach : TriggeredAbility :=
  mkShared .thisEnters .honePerOppAttach
def onPutCountersOnGoblinOrcArmyDamageOpp : TriggeredAbility :=
  mkShared .youPutCountersOnGoblinOrcArmy (.damageTargetOpponent 2)
    (grouping? := some .oncePerBatch)
def onEnterIfNotTokenCopySelf : TriggeredAbility :=
  mkShared .thisEnters .copySelfNonlegendary
def onEnterAttachEquipmentThenFight : TriggeredAbility :=
  mkShared .thisEnters .attachEquipmentThenFight
def onDiesReturnAsArtifact : TriggeredAbility :=
  mkShared .thisCreatureDies .returnAsArtifact
def onEnterExileLandsThenReturnTapped : TriggeredAbility :=
  mkShared .thisEnters .exileLandsThenReturnTapped
def onCombatDamageImpulseInstantSorcery : TriggeredAbility :=
  mkShared .thisDealsCombatDamageToPlayer .grimaImpulse
def onYourEndStepPalantir : TriggeredAbility :=
  mkShared .stepYourEndStep .palantir
def onDealtNoncombatDamageCreateTreasures : TriggeredAbility :=
  mkShared .thisDealtNoncombatDamage .treasuresEqualLastKnown (grouping? := some .oncePerBatch)
def onEnterIfCastProtectionEverything : TriggeredAbility :=
  mkShared .thisEnters .protectionEverything
def onYourUpkeepLoseLifePerBurden : TriggeredAbility :=
  mkShared .stepYourUpkeep .loseLifePerBurden
def onFinalSagaChapterRevealSaga : TriggeredAbility :=
  mkShared .finalSagaChapterResolves .revealSaga (limit? := some .onceEachTurn)
def onCombatDamageToYouSacRingTempts : TriggeredAbility :=
  mkShared .combatDamageToYou .sacDamagersRingTempts (grouping? := some .oncePerBatch)
/-- Construct a multi-chapter Saga triggered ability (CR 714.2b). -/
def sagaChapters (chapters : Array Nat) (e : Effect) : TriggeredAbility :=
  let eff :=
    match e.asChapter? with
    | some _ => e
    | none =>
      let wrapped := Effect.ofChapter (Effect.chapterSpell e)
      { wrapped with
        phrase := if e.phrase.isEmpty then wrapped.phrase else e.phrase }
  { word := .when
    pattern := TriggerPattern.putCountersOnSelf .lore
    grouping := .counterThreshold .lore chapters
    effect := eff }
/-- Construct a single-chapter Saga triggered ability (CR 714.2b). -/
def sagaChapter (n : Nat) (e : Effect) : TriggeredAbility :=
  sagaChapters #[n] e
def onTappedForTeamworkPlusOneAndDraw : TriggeredAbility :=
  mkTrigger .thisTappedForTeamwork Effect.seqPlusOneOnSourceAndDraw
def onEachEndStepDrawIfAttackedOrEnteredSubtype (subtype : String) : TriggeredAbility :=
  mkShared .stepEachEndStep (.drawIfAttackedOrEnteredSubtype (CardSubtype.ofOracleD subtype .hero))
def onAttackOthersOfSubtypeGetEqualToughness (subtype : String) : TriggeredAbility :=
  mkShared .thisAttacks (.othersOfSubtypeGetEqualSourceToughness (CardSubtype.ofOracleD subtype .hero))
def onCreatureYouControlEntersScryAndPlan (n : Nat) : TriggeredAbility :=
  mkShared .creatureYouControlEnters (.scryAndPlan n)
def onCreaturesYouControlBecomeTappedLootAndPlan : TriggeredAbility :=
  mkShared .creaturesYouControlBecomeTapped .lootAndPlan (grouping? := some .oncePerBatch)
def onYouDrawSecondCreateVillainAndPlan : TriggeredAbility :=
  mkShared (.drawCard .you) .createVillainAndPlan (limit? := some (.nthEachTurn 2))
def onVillainYouControlEntersDrainAndPlan (n : Nat) : TriggeredAbility :=
  mkShared (.subtypeYouControlEnters .villain) (.drainAndPlan n)
def onCreatureCardsToGyDrawLoseLifeAndPlan : TriggeredAbility :=
  mkShared .creatureCardPutIntoYourGy .drawLoseLifeAndPlan (grouping? := some .oncePerBatch)
def onCastNoncreatureTreasureAndPlan : TriggeredAbility :=
  mkShared .youCastNoncreature .treasureTappedAndPlan
def onLandYouControlEntersPlusOneAndPlan : TriggeredAbility :=
  mkShared .landYouControlEnters .plusOneOnTargetAndPlan
def onNthPlanCounter (n : Nat) (s : SharedTrigger) : TriggeredAbility :=
  mkShared (.putCountersOnSelf .plan) s (word? := some .when)
    (grouping? := some (.counterThreshold .plan #[n]))
def onFourthPlanDrawPlusOneEach : TriggeredAbility :=
  onNthPlanCounter 4 .planFinishDrawPlusOneEach
def onFourthPlanReturnInstants : TriggeredAbility :=
  onNthPlanCounter 4 .planFinishReturnInstants
def onSeventhPlanControlOpponent : TriggeredAbility :=
  onNthPlanCounter 7 .planFinishControlOpponent
def onFifthPlanExileTopCast : TriggeredAbility :=
  onNthPlanCounter 5 .planFinishExileTopCast
def onThirdPlanCreateRobots : TriggeredAbility :=
  onNthPlanCounter 3 (.planFinishCreateRobots 3)
def onFourthPlanDividedDamage : TriggeredAbility :=
  onNthPlanCounter 4 (.planFinishDividedDamage 7)
def onFourthPlanIndestructible : TriggeredAbility :=
  onNthPlanCounter 4 .planFinishIndestructibleOnTarget
def onEnterSurveil (n : Nat) : TriggeredAbility := mkShared .thisEnters (.surveil n)
def onEnterEnchanted (action : PermanentAction) : TriggeredAbility :=
  mkShared .thisEnters (.onEnchanted action)
def onEnterAttachThen (followup : PermanentAction) : TriggeredAbility :=
  mkShared .thisEnters (.attachThen followup)
def onEnterExileOtherCopyEnchanted : TriggeredAbility :=
  mkShared .thisEnters .exileOtherCopyEnchanted
def onEnterExileCreatureReturnEndStep : TriggeredAbility :=
  mkShared .thisEnters .exileUntilNextEndStep
def onEnterTapOrUntapNonland : TriggeredAbility :=
  mkShared .thisEnters .tapOrUntapNonland
def onEnterCreateFoodOrTreasure : TriggeredAbility :=
  mkShared .thisEnters .createFoodOrTreasure
def onEnterVillainIfGyElseMill : TriggeredAbility :=
  mkShared .thisEnters .villainIfGyElseMill
def onEnterDrawMayPutLandTapped : TriggeredAbility :=
  mkShared .thisEnters .drawMayPutLandTapped
def onEnterDrawGainLifeIfAnotherHero : TriggeredAbility :=
  mkShared .thisEnters .drawGainLifeIfAnotherHero
def onEnterPlusOneOrTwoIfAnotherHero : TriggeredAbility :=
  mkShared .thisEnters .plusOneOrTwoIfAnotherHero
def onEnterMaySacArtifactOrDiscardDraw : TriggeredAbility :=
  mkShared .thisEnters .maySacArtifactOrDiscardDraw
def onEnter (e : Effect) : TriggeredAbility :=
  match e.asTrigger? with
  | some s => s.toTriggeredAbility (pattern? := some .thisEnters)
  | none => mkTrigger .thisEnters e
def onStep (e : Effect) : TriggeredAbility :=
  match e.asTrigger? with
  | some s => s.toTriggeredAbility
  | none => mkTrigger .stepYourUpkeep e
def onDeath (e : Effect) : TriggeredAbility :=
  match e.asTrigger? with
  | some s => s.toTriggeredAbility
  | none => mkTrigger .thisDies e
def onThisAttack (e : Effect) : TriggeredAbility :=
  match e.asTrigger? with
  | some s => s.toTriggeredAbility
  | none => mkTrigger .thisAttacks e
def onEnterOrAttack (e : Effect) : TriggeredAbility :=
  match e.asTrigger? with
  | some s => s.toTriggeredAbility (pattern? := some .enterOrAttack)
  | none => mkTrigger .enterOrAttack e
def onWatch (e : Effect) : TriggeredAbility :=
  match e.asTrigger? with
  | some s => s.toTriggeredAbility
  | none => mkTrigger .thisEnters e
def onYouAttacking (e : Effect) : TriggeredAbility :=
  match e.asTrigger? with
  | some s => s.toTriggeredAbility (pattern? := some .youAttack) (grouping? := some .oncePerBatch)
  | none => mkTrigger .youAttack e (grouping := .oncePerBatch)
def onCasting (e : Effect) : TriggeredAbility :=
  match e.asTrigger? with
  | some s => s.toTriggeredAbility
  | none => mkTrigger .youCastSpell e
def onResource (e : Effect) : TriggeredAbility :=
  match e.asTrigger? with
  | some s => s.toTriggeredAbility
  | none => mkTrigger .thisEnters e

instance : HasTargeting TriggeredAbility where
  targeting ab := ab.effect.targeting

/-- Leading `"When / Whenever / At …"` prefix rendered from `word`, `pattern`,
`grouping`, and `limit`. -/
private def eventPrefixPattern (word : TriggerWord) (grouping : BatchGrouping)
    (limit : TriggerLimit) : TriggerPattern → String
  | .or (.zoneChange (.sameAs .this) (.notIn .battlefield) (.inZones { zones := #[.battlefield], .. }) none none)
        (.attacks (.sameAs .this) .any false 1 none false) =>
    "Whenever this creature enters or attacks"
  | .or (.castSpell { relation := .you, pred := .any } (.hasColor (.literal .green)) none none false none none)
        (.zoneChange (.all #[.hasSubtype (.literal .forest), .controlledBy { relation := .you, pred := .any }])
          (.notIn .battlefield) (.inZones { zones := #[.battlefield], .. }) none none) =>
    "Whenever you cast a green spell and whenever a Forest you control enters"
  | .zoneChange (.any #[.sameAs .this, .all #[.hasSubtype (.literal s), .controlledBy _]])
      (.notIn .battlefield) (.inZones { zones := #[.battlefield], .. }) none none =>
    s!"Whenever this or another {s} you control enters"
  | .zoneChange (.any #[.sameAs .this, .all #[.isToken false, .hasSubtype (.literal s), .controlledBy _]])
      (.notIn .battlefield) (.inZones { zones := #[.battlefield], .. }) none none =>
    s!"Whenever this or another nontoken {s} you control enters"
  | .zoneChange (.all #[.otherThan .this, .controlledBy _,
      .any #[.hasSubtype (.literal s), .all #[.hasType .artifact, .hasSubtype (.literal .equipment)]]])
      (.notIn .battlefield) (.inZones { zones := #[.battlefield], .. }) none none =>
    s!"Whenever another {s} or Equipment you control enters"
  | .zoneChange (.all #[.otherThan .this, .hasType .creature, .controlledBy _, .stat .power .le (.const n)])
      (.notIn .battlefield) (.inZones { zones := #[.battlefield], .. }) none none =>
    s!"Whenever another creature you control with power {n} or less enters"
  | .zoneChange (.all #[.otherThan .this, .hasSubtype (.literal s), .controlledBy _])
      (.notIn .battlefield) (.inZones { zones := #[.battlefield], .. }) none none =>
    s!"Whenever another {s} you control enters"
  | .whenCond inner (.exists (.inZones .battlefield (.all #[.hasType .creature, .controlledBy _, .stat .power .ge (.const n)]))) =>
    let base := eventPrefixPattern word grouping limit inner
    s!"{base} while you control a creature with power {n} or greater"
  | p =>
    let ctx : PrintCtx :=
      match p with
      | .attacks (.sameAs .this) .. | .blocks (.sameAs .this) | .becomesBlocked (.sameAs .this)
      | .zoneChange (.sameAs .this) (.inZones { zones := #[.battlefield], .. }) (.inZones { zones := #[.graveyard], .. }) _ _
      | .zoneChange (.sameAs .this) (.inZones { zones := #[.battlefield], .. }) (.notIn .battlefield) _ _ =>
        { selfRef := "this creature", capitalize := false }
      | .damageDealt (.sameAs .this) .. | .damageDealt _ (.object { pred := .sameAs .this, .. }) ..
      | .becomesTapped (.sameAs .this) .. =>
        { selfRef := "this", capitalize := false }
      | .becomesTarget (.object (.sameAs .this)) .. =>
        { selfRef := "this creature", capitalize := false }
      | _ => { selfRef := "this permanent", capitalize := false }
    let w := word.toOracleStr
    s!"{w} {p.renderClause ctx grouping limit}"

/-- Leading `"When / Whenever / At …"` prefix rendered from `ab.word`,
`ab.pattern`, `ab.grouping`, and `ab.limit`. -/
def eventPrefix (ab : TriggeredAbility) : String :=
  eventPrefixPattern ab.word ab.grouping ab.limit ab.pattern

/-- Intervening `"if …"` clause rendered from `ab.interveningIf?`, or empty. -/
def interveningClause (ab : TriggeredAbility) : String :=
  match ab.interveningIf? with
  | none => ""
  | some cond =>
    match cond with
    | .exists (.inZones .battlefield (.all #[.hasType .creature, .controlledBy _, .stat .power .ge (.const n)])) =>
      s!" while you control a creature with power {n} or greater"
    | .cmp .ge (.playerMetric .lifeGainedThisTurn .you) (.const n) =>
      s!", if you gained {n} or more life this turn"
    | _ =>
      s!", if {ToOracle.toOracle { selfRef := "this permanent", capitalize := false } cond}"

/-- Oracle clause for putting `n` counters of `kind` on `noun`. -/
def counterOn (noun : String) (kind : CounterKind) (n : Nat) : String :=
  match kind with
  | .plusOnePlusOne => s!"put {plusOnePlusOneCountersPhrase n} on {noun}"
  | .indestructible => s!"put {kind.countersPhrase n} on {noun}"
  | .doubleStrike => s!"put {kind.countersPhrase n} on {noun}"
  | .burden => s!"put {kind.countersPhrase n} on {noun}"
  | .stun => s!"put {kind.countersPhrase n} on {noun}"
  | _ => "put counters"

/-- Printed noun for the permanent `who` names. `targetNoun` is the announced target. -/
def affectedNoun (who : TriggerAffected) (targetNoun : String) : String :=
  match who with
  | .target => targetNoun
  | .source => "this creature"
  | .enchanted => "enchanted creature"
  | .targetWhileSource => "that creature"

/-- Oracle clause for the single step that follows attaching to the announced
creature. A compound action flattened into more than one step is `none`. -/
def attachedFollowupPhrase (r : TriggerResolution) : Option String :=
  match r with
  | .pump (.fixed p) (.fixed t) (.target .whileSource) =>
    some s!"that creature gets {signedStat p}/{signedStat t} until end of turn"
  | .pump .double .double (.target .whileSource) =>
    some "double that creature's power and toughness until end of turn"
  | .putCounters (.ofKind .plusOnePlusOne n) (.target .whileSource) =>
    some s!"put {plusOnePlusOneCountersPhrase n} on that creature"
  | .putCounters (.ofKind .indestructible n) (.target .whileSource) =>
    some s!"put {(.indestructible : CounterKind).countersPhrase n} on that creature"
  | .putCounters (.ofKind .doubleStrike n) (.target .whileSource) =>
    some s!"put {(.doubleStrike : CounterKind).countersPhrase n} on that creature"
  | .putCounters (.ofKind .burden n) (.target .whileSource) =>
    some s!"put {(.burden : CounterKind).countersPhrase n} on that creature"
  | .putCounters (.ofKind .stun n) (.target .whileSource) =>
    some s!"put {(.stun : CounterKind).countersPhrase n} on that creature"
  | .grant (.keywords k) (.target .whileSource) =>
    some s!"that creature gains {KeywordAbility.joinedAnd k} until end of turn"
  | .tap (.target .whileSource) => some "tap that creature"
  | .untap (.target .whileSource) => some "untap that creature"
  | .lose .indestructible (.target .whileSource) =>
    some "that creature loses indestructible until end of turn"
  | .cant (.beBlocked (.target .whileSource)) =>
    some "that creature can't be blocked this turn"
  | .becomeArtifact (.target .whileSource) =>
    some "until end of turn, that creature becomes an artifact in addition to its other types"
  | .becomePrepared (.target .whileSource) => some "that creature becomes prepared"
  | .setBasePT (.fixed p) (.fixed t) (.target .whileSource) =>
    some s!"that creature has base power and toughness {p}/{t} until end of turn"
  | .putOnLibrary .top (.target .whileSource) =>
    some "that creature's owner puts it on top of their library"
  | .putOnLibrary .bottom (.target .whileSource) =>
    some "that creature's owner puts it on the bottom of their library"
  | .destroy (.target .whileSource) _ => some "destroy that creature"
  | .dealDamage (.fixed n) (.target .whileSource) .none =>
    some s!"deals {n} damage to that creature"
  | .exile (.target .whileSource) .forLater .none => some "exile that creature"
  | _ => none

/-- Subtypes when `parts` is only `.othersOfSubtype`, in that order. -/
private def othersOfSubtypeParts (parts : List ObjectSelector) : Option (Array CardSubtype) :=
  parts.foldl (fun acc part =>
    match acc, part with
    | some ss, .othersOfSubtype subtype => some (ss.push subtype)
    | _, _ => none) (some #[])

/-- Effect clause from resolution, targeting, and divided-damage parameters. -/
def resolutionPhrase (t : Effect) : String :=
  let noun := t.targeting.spec.noun
  match t.resolution with
  | .pump power toughness who =>
    match power, toughness, who with
    | .greatestPower, .fixed 0, .source =>
      "it gets +X/+0 until end of turn, where X is the greatest power among creatures you control"
    | .perLookedAt, .perLookedAt, .source =>
      "this creature gets +1/+1 until end of turn for each card looked at while scrying this way"
    | .perOtherCreature, .perOtherCreature, .source =>
      "it gets +1/+1 until end of turn for each other creature you control"
    | .perPlains, .perPlains, .target =>
      "target creature you control gets +1/+1 until end of turn for each Plains you control"
    | .fixed power, .fixed toughness, .cause _ =>
      s!"that creature gets {signedStat power}/{signedStat toughness} until end of turn"
    | .equalSourceToughness, .equalSourceToughness, .othersOfSubtype subtype =>
      s!"each other {pluralSubtype subtype} you control get +X/+X until end of turn, where X is this toughness"
    | .equalSourcePower, .fixed 0, .target =>
      s!"{noun} gets +X/+0 until end of turn, where X is this creature's power"
    | .fixed power, .fixed toughness, .creaturesYouControl =>
      s!"creatures you control get {signedStat power}/{signedStat toughness} until end of turn"
    | .fixed power, .fixed toughness,
        .intersection [.creaturesYouControl, .union parts] =>
      match othersOfSubtypeParts parts with
      | some subtypes =>
        let recipients :=
          if subtypes == #[.goblin, .orc] then "other Goblins and Orcs you control"
          else s!"other {joinedSubtypes subtypes} you control"
        s!"{recipients} get {signedStat power}/{signedStat toughness} until end of turn"
      | none =>
        "those permanents get +P/+T until end of turn"
    | .fixed power, .fixed toughness, .opponentsCreatures =>
      s!"creatures your opponents control get {signedStat power}/{signedStat toughness} until end of turn"
    | .fixed power, .fixed toughness, .target =>
      s!"{noun} gets {signedStat power}/{signedStat toughness} until end of turn"
    | .double, .double, .target =>
      s!"double {noun}'s power and toughness until end of turn"
    | .fixed power, .fixed toughness, .source =>
      s!"this creature gets {signedStat power}/{signedStat toughness} until end of turn"
    | .double, .double, .source =>
      "double this creature's power and toughness until end of turn"
    | .fixed power, .fixed toughness, .enchanted =>
      s!"enchanted creature gets {signedStat power}/{signedStat toughness} until end of turn"
    | .double, .double, .enchanted =>
      "double enchanted creature's power and toughness until end of turn"
    | .fixed power, .fixed toughness, (.target .whileSource) =>
      s!"that creature gets {signedStat power}/{signedStat toughness} until end of turn"
    | .double, .double, (.target .whileSource) =>
      "double that creature's power and toughness until end of turn"
    | .fixed power, .fixed toughness,
        .intersection [.creaturesYouControl, .youControl (.subtype subtype)] =>
      s!"{subtype}s you control get {signedStat power}/{signedStat toughness} until end of turn"
    | _, _, _ =>
      "those permanents get +P/+T until end of turn"
  | .setBasePT .equalSourcePower .equalSourceToughness .target =>
    "choose up to one other target creature you control. Its base power and toughness become equal to this creature's power and toughness until end of turn"
  | .lose .indestructible .target =>
    s!"{noun} loses indestructible until end of turn"
  | .lose .indestructible .source =>
    "this creature loses indestructible until end of turn"
  | .lose .indestructible .enchanted =>
    "enchanted creature loses indestructible until end of turn"
  | .lose .indestructible (.target .whileSource) =>
    "that creature loses indestructible until end of turn"
  | .lose .allAbilities (.target .ifPresent) =>
    "it loses all abilities for as long as this remains on the battlefield"
  | .lose _ _ =>
    "lose"
  | .cant (.beBlocked .target) =>
    s!"{affectedNoun .target noun} can't be blocked this turn"
  | .cant (.beBlocked .source) =>
    s!"{affectedNoun .source noun} can't be blocked this turn"
  | .cant (.beBlocked .enchanted) =>
    s!"{affectedNoun .enchanted noun} can't be blocked this turn"
  | .cant (.beBlocked (.target .whileSource)) =>
    s!"{affectedNoun .targetWhileSource noun} can't be blocked this turn"
  | .cant (.beBlockedExceptByHaste .target) =>
    s!"{affectedNoun .target noun} can't be blocked this turn except by creatures with haste"
  | .cant (.beBlockedExceptByHaste .source) =>
    s!"{affectedNoun .source noun} can't be blocked this turn except by creatures with haste"
  | .cant (.beBlockedExceptByHaste .enchanted) =>
    s!"{affectedNoun .enchanted noun} can't be blocked this turn except by creatures with haste"
  | .cant (.beBlockedExceptByHaste (.target .whileSource)) =>
    s!"{affectedNoun .targetWhileSource noun} can't be blocked this turn except by creatures with haste"
  | .cant (.untapWhileYouControl .target) =>
    "that creature can't become untapped for as long as you control this creature"
  | .cant _ =>
    "can't"
  | .becomeArtifact .target =>
    s!"until end of turn, {noun} becomes an artifact in addition to its other types"
  | .becomeArtifact .source =>
    "until end of turn, this creature becomes an artifact in addition to its other types"
  | .becomeArtifact .enchanted =>
    "until end of turn, enchanted creature becomes an artifact in addition to its other types"
  | .becomeArtifact (.target .whileSource) =>
    "until end of turn, that creature becomes an artifact in addition to its other types"
  | .becomeArtifact _ =>
    "becomes an artifact"
  | .becomePrepared .target =>
    s!"{noun} becomes prepared"
  | .becomePrepared .source =>
    "this creature becomes prepared"
  | .becomePrepared .enchanted =>
    "enchanted creature becomes prepared"
  | .becomePrepared (.target .whileSource) =>
    "that creature becomes prepared"
  | .becomePrepared _ =>
    "becomes prepared"
  | .setBasePT (.fixed p) (.fixed t) .target =>
    s!"{noun} has base power and toughness {p}/{t} until end of turn"
  | .setBasePT (.fixed p) (.fixed t) .source =>
    s!"this creature has base power and toughness {p}/{t} until end of turn"
  | .setBasePT (.fixed p) (.fixed t) .enchanted =>
    s!"enchanted creature has base power and toughness {p}/{t} until end of turn"
  | .setBasePT (.fixed p) (.fixed t) (.target .whileSource) =>
    s!"that creature has base power and toughness {p}/{t} until end of turn"
  | .setBasePT _ _ _ =>
    "set base power and toughness"
  | .putOnLibrary .top .target =>
    s!"{noun}'s owner puts it on top of their library"
  | .putOnLibrary .bottom .target =>
    s!"{noun}'s owner puts it on the bottom of their library"
  | .putOnLibrary .top .source =>
    "this creature's owner puts it on top of their library"
  | .putOnLibrary .bottom .source =>
    "this creature's owner puts it on the bottom of their library"
  | .putOnLibrary .top .enchanted =>
    "enchanted creature's owner puts it on top of their library"
  | .putOnLibrary .bottom .enchanted =>
    "enchanted creature's owner puts it on the bottom of their library"
  | .putOnLibrary .top (.target .whileSource) =>
    "that creature's owner puts it on top of their library"
  | .putOnLibrary .bottom (.target .whileSource) =>
    "that creature's owner puts it on the bottom of their library"
  | .putOnLibrary .bottom .cardFromHand =>
    "put a card from your hand on the bottom of your library"
  | .putOnLibrary _ _ =>
    "put on library"
  | .surveil (.fixed n) => s!"surveil {n}"
  | .surveil _ => "surveil"
  | .empowerJace (.fixed n) => s!"empower Jace {n}"
  | .empowerJace _ => "empower Jace"
  | .prepareSource .ifNotPrepared =>
    "if this creature isn't prepared, it becomes prepared"
  | .prepareSource .ifThreeCreaturesDied =>
    "if three or more creatures died this turn, this creature becomes prepared"
  | .«if» (.atLeast .lastKnownPower (.fixed 2)) (.draw (.fixed 1)) =>
    "if you removed two or more loyalty counters to activate it, draw a card"
  | .putCounters what who =>
    match what, who with
    | .ofKind .plusOnePlusOne _, .youControl .eachCreature =>
      "put a +1/+1 counter on each creature you control"
    | .ofKind .plusOnePlusOne _, .youControl (.subtype s) =>
      s!"put a +1/+1 counter on each {s} you control"
    | .ofKind .plusOnePlusOne _, .youControl .citysBlessing =>
      "put a +1/+1 counter on each creature you control. If you have the city's blessing, put two +1/+1 counters on each creature you control instead"
    | .ofKind .plusOnePlusOne _, .eachOther =>
      "put a +1/+1 counter on each other creature you control"
    | .plusOneLastKnownMv, _ =>
      s!"put X +1/+1 counters on {noun}, where X is that spell's mana value"
    | .ofKind .loyalty _, .source => "put a loyalty counter on this"
    | .sourceCounters, _ =>
      "put its counters on up to one target creature you control"
    | .ofKind .charge _, _ => "put a charge counter on this enchantment"
    | .ofKind .quest _, _ => "put a quest counter on this enchantment"
    | .honePerOpponent, _ =>
      "put a hone counter on this for each creature target opponent controls"
    | .ofKind .plan _, _ => "put a plan counter on this enchantment"
    | .ofKind .plusOnePlusOne _, .permanent true =>
      s!"put a +1/+1 counter on {noun}"
    | .plusOneNoted, _ =>
      "put a +1/+1 counter on it for each invasion counter on this enchantment"
    | .ofKind .invasion _, _ => "put an invasion counter on this enchantment"
    | .ofKind .trample _, _ =>
      s!"put a trample counter on up to one {noun}"
    | .ofKind .influence _, _ => "put an influence counter on this"
    | .ofKind .loyalty _, .permanent _ => "put a loyalty counter on it"
    | .plusOneSacrificedPower, _ =>
      "put a number of +1/+1 counters on this creature equal to the sacrificed creature's power"
    | .ofKind .plusOnePlusOne n, .permanent false =>
      s!"put {plusOnePlusOneCountersPhrase n} on {noun}"
    | .ofKind .indestructible n, .permanent false =>
      s!"put {(.indestructible : CounterKind).countersPhrase n} on {noun}"
    | .ofKind .doubleStrike n, .permanent false =>
      s!"put {(.doubleStrike : CounterKind).countersPhrase n} on {noun}"
    | .ofKind .burden n, .permanent false =>
      s!"put {(.burden : CounterKind).countersPhrase n} on {noun}"
    | .ofKind .stun n, .permanent false =>
      s!"put {(.stun : CounterKind).countersPhrase n} on {noun}"
    | .ofKind kind n, .source =>
      counterOn "this creature" kind n
    | .ofKind kind n, .enchanted =>
      counterOn "enchanted creature" kind n
    | .ofKind kind n, (.target .whileSource) =>
      counterOn "that creature" kind n
    | .ofKind .plusOnePlusOne _, .eachUpToLastKnown =>
      "put a +1/+1 counter on each of up to that many target creatures you control"
    | .missingKeywordsFromTarget, .source =>
      "if that creature has haste and this doesn't, put a haste counter on this. Do the same for flying, first strike, double strike, deathtouch, indestructible, lifelink, menace, reach, trample, and vigilance"
    | _, _ => "put counters"
  | .«if» ((.atLeast (.count .landsYouControl) (.fixed 6))) (.sequence [.destroy .target,
      .createTokens _ (.fixed 1) false (.controller .target) _]) =>
    s!"if you control six or more lands, destroy {noun}. They create a Treasure token"
  | .ifElse (.or [.scriedThisTurn, .surveilledThisTurn])
      (.putCounters (.ofKind .plusOnePlusOne) .permanent) (.pump (.fixed 1) (.fixed 1) .target) =>
    s!"{noun} gets +1/+1 until end of turn. If you've scried or surveilled this turn, put a +1/+1 counter on that creature instead"
  | .«if» (.not (.atLeast (.count .planeswalkersYouControl) (.fixed 1))) (.sacrifice (.sacrificedSource .controllerSacrifices)) =>
    "if you don't control a planeswalker, sacrifice this creature"
  | .«if» ((.atLeast (.count .forestsExceptCause) (.fixed 5))) (.pump (.fixed 3) (.fixed 3) .target) =>
    s!"if you control at least five other Forests, {noun} gets +3/+3 until end of turn"
  | .may (.pay cost) (.sequence [.putCounters (.ofKind .plusOnePlusOne 1) .source, .draw (.fixed 1)]) .ifYouDo =>
    match cost.soleGenericMana? with
    | some n =>
      s!"you may pay \{{n}}. If you do, put a +1/+1 counter on this creature and draw a card"
    | none =>
      "you may pay. If you do, put a +1/+1 counter on this creature and draw a card"
  | .dealDamage amount who note =>
    match who, amount, note with
    | .blockers, .fixed n, _ =>
      s!"it deals {n} damage to each creature blocking it"
    | .permanent, .lastKnownPower, .excess =>
      s!"Bolg deals damage equal to the sacrificed creature's power to {noun}"
    | .permanent, .lastKnownPower, _ =>
      s!"it deals damage equal to its power to {noun}"
    | .player .eachOpponent, .subtypeCount subtype, _ =>
      s!"it deals damage equal to the number of {pluralSubtype subtype} you control to each opponent"
    | .player .eachOpponent, .discardedHand, _ =>
      "this deals X damage to each opponent"
    | .player .eachOpponent, .fixed n, _ =>
      s!"this creature deals {n} damage to each opponent"
    | .target, .subtypeCount subtype, _ =>
      s!"it deals damage equal to the number of {pluralSubtype subtype} you control to {noun}"
    | .target, .fixed n, .none =>
      s!"deals {n} damage to {noun}"
    | .target, .spellManaValue, _ =>
      s!"this deals damage equal to that spell's mana value to {noun}"
    | .target, .fixed n, _ =>
      s!"it deals {n} damage to {noun}"
    | .player (.target .opponent), .greatestArtifactMv, _ =>
      s!"this Saga deals X damage to {noun}, where X is the greatest mana value among artifacts you control"
    | .eachNonSubtypeAndOpponents subtype, .fixed n, _ =>
      s!"this Saga deals {n} damage to each non-{subtype} creature and each opponent"
    | .player (.target .opponent), .fixed n, _ =>
      s!"this deals {n} damage to {noun}"
    | .permanent, .fixed n, _ =>
      s!"it deals {n} damage to {noun}"
    | .source, .fixed n, .none =>
      s!"deals {n} damage to this creature"
    | .enchanted, .fixed n, .none =>
      s!"deals {n} damage to enchanted creature"
    | (.target .whileSource), .fixed n, .none =>
      s!"deals {n} damage to that creature"
    | _, _, _ =>
      "deal damage"
  | .scry (.fixed n) => s!"scry {n}"
  | .scry _ => "scry"
  | .draw amount who =>
    match who, amount with
    | .opponentHasYou, _ =>
      "target opponent may have you draw a card"
    | .you, .forEachTappedHuman =>
      "draw a card for each Human tapped this way"
    | .you, .perFatGraveyard =>
      "draw a card for each graveyard with seven or more cards in it"
    | .you, .discardedHand =>
      "draw X cards, where X is the number of cards discarded this way"
    | .you, .equalToManaSpent =>
      "draw X cards, where X is the amount of mana spent to cast that spell"
    | .you, .perControlled _ =>
      "draw a card for each permanent you control of that type"
    | .you, .upToHandSize _ =>
      "if you have fewer than that many cards in hand, draw cards equal to the difference"
    | .controller .enchanted, _ =>
      "that player draws a card"
    | .eachOpponent, .fixed n =>
      s!"each opponent draws {cardPhrase n.toNat}"
    | .you, .fixed n =>
      s!"draw {cardPhrase n.toNat}"
    | _, _ =>
      "draw cards"
  | .searchLibrary (.put .forest .asPrinted .none) =>
    "search your library for a Forest card, put that card onto the battlefield, then shuffle"
  | .searchLibrary (.returnToHand .basicLand .none) =>
    searchLibraryToHandPhrase "a basic land card"
  | .searchLibrary (.put .basicLandOnTop .asPrinted .none) =>
    "you may search your library for a basic land card, reveal it, then shuffle and put that card on top"
  | .searchLibrary (.put .dragon .asPrinted .none) =>
    "search your hand and/or library for a Dragon card and put it onto the battlefield"
  | .searchLibrary _ =>
    "search your library"
  | .discard what =>
    match what with
    | .cards n .you =>
      s!"discard {cardPhrase n}"
    | .hand =>
      "discard your hand"
    | .cards n .eachOpponent =>
      if n == 1 then "each opponent discards a card"
      else s!"each opponent discards {cardPhrase n}"
    | .cards n (.target .opponent) =>
      s!"{noun} discards {cardPhrase n}"
    | .chosenNonland =>
      s!"{noun} reveals their hand. You choose a nonland card from it. That player discards that card"
    | _ =>
      "discard cards"
  | .may (.discard (.cards 1)) (.draw (.fixed n)) .ifYouDo =>
    s!"you may discard a card. If you do, draw {cardPhrase n.toNat}"
  | .may (.dealDamage .lastKnownPower .target .none) (.sequence []) .ifYouDo =>
    "you may have this deal that much damage"
  | .may .retargetCause (.sequence []) .ifYouDo =>
    "you may choose new targets for that spell"
  | .may (.pay cost) (.queueReflexive follow) .ifYouDo =>
    if cost == CostSpec.sacrificeAnotherCreature && follow == .destroy .target then
      "you may sacrifice another creature. When you do, destroy target nonland permanent an opponent controls"
    else if cost == CostSpec.sacrificeArtifactOrDiscardNonland && follow == .dealDamage (.fixed 2) .target then
      "you may sacrifice an artifact or discard a nonland card. When you do, this deals 2 damage to any target"
    else if cost.isManaOnly && !cost.isEmpty then
      let times :=
        match TriggerResolution.queuedReflexive follow with
        | .modeled _ times => times
        | _ => 1
      match cost.soleGenericMana? with
      | some n =>
        if times > 1 then s!"you may pay \{{n}} up to {times} times"
        else s!"you may pay \{{n}}"
      | none => "you may pay that cost"
    else if cost.items.any (fun | .sacrifice _ _ => true | _ => false) then
      "you may sacrifice that. If you do, do that"
    else if cost.items.any (fun | .discard _ _ => true | _ => false) then
      "you may discard that. If you do, do that"
    else "you may pay that cost"
  | .may (.pay cost) (.becomeCopy (.cause none)) .ifYouDo =>
    match cost.soleGenericMana? with
    | some 2 => "you may pay {2} to copy it"
    | _ => "you may pay to copy it"
  | .may (.loseLife (.fixed 2) .you)
      (.grant .assignCombatDamageEqualToughness .creaturesYouControl) .ifYouDo =>
    "you may pay 2 life. If you do, until end of turn, creatures you control with toughness greater than their power assign combat damage equal to their toughness rather than their power"
  | .may (.exile .top .playThisTurn .ifHero) (.sequence []) _ =>
    "you may exile the top card of your library. If that card is a Hero card, this gets +2/+1 until end of turn. You may play that card this turn"
  | .may action _ =>
    match action with
    | .tap .humans =>
      "you may tap any number of untapped Humans you control"
    | .sacrifice .another _ =>
      "you may sacrifice another creature. When you do, Bolg deals damage equal to that creature's power to another target creature. If excess damage was dealt this way, amass Goblins X, where X is that excess damage"
    | .put .artifactFromHand _ .forAttach =>
      "you may put an artifact card from your hand onto the battlefield"
    | .discard .hand =>
      "you may discard your hand"
    | .draw _ .opponentHasYou =>
      "target opponent may have you draw a card"
    | .put .landFromHand .tapped _ =>
      "you may put a land card from your hand onto the battlefield tapped"
    | .put (.creatureFromHand subtype maxMv) _ _ =>
      s!"you may put a {subtype} creature card with mana value {maxMv} or less from your hand onto the battlefield. If you don't, draw a card"
    | .sequence [.draw .equalToManaSpent _, .«if» .manaSpent (.discard (.cards n))] =>
      let disc := if n == 2 then "two cards" else cardPhrase n
      s!"you may draw X cards, where X is the amount of mana spent to cast that spell. If you do, discard {disc}"
    | _ => "you may do it"
  | .sacrifice what _ =>
    match what with
    | .opponentChosenCreature =>
      s!"{noun} sacrifices a creature of their choice"
    | .eachPlayersCreature =>
      "each player sacrifices a creature of their choice"
    | .leastPower =>
      "defending player sacrifices a creature with the least power among creatures they control"
    | .combatDamager =>
      "each opponent sacrifices a creature of their choice that dealt combat damage to you this turn"
    | .chosenNontokenCreature =>
      "each opponent sacrifices a nontoken creature of their choice"
    | .sacrificedSource .controllerSacrifices =>
      "sacrifice this creature"
    | .another =>
      "sacrifice another creature. When you do, Bolg deals damage equal to that creature's power to another target creature. If excess damage was dealt this way, amass Goblins X, where X is that excess damage"
    | _ =>
      "sacrifice it"
  | .dividedDamage =>
    match t.dividedDamage with
    | some (amount, maxTargets) =>
      s!"it deals {amount} damage divided as you choose among {dividedAmong maxTargets}"
    | none => "it deals damage divided as you choose"
  | .sequence [.returnToHand .graveyardCard, .gainLife .equalToTargetPower] =>
    s!"return {noun} to your hand. You gain life equal to that card's power"
  | .sequence [.draw (.fixed 1), .«if» (.not (.atLeast (.count .legendaryCreaturesYouControl) (.fixed 1))) (.putOnLibrary .bottom .cardFromHand)] =>
    "draw a card. Then if you don't control a legendary creature, put a card from your hand on the bottom of your library"
  | .sequence [.removeCounters .hope .source, .«if» .removedHope (.draw (.fixed 1)),
      .«if» (.not .hopeOnSource) (.sequence [.sacrifice .source, .gainLife (.fixed 4)])] =>
    "remove a hope counter from this. If you do, draw a card. Then if this has no hope counters on it, sacrifice it and you gain 4 life"
  | .sequence [.may (.tap .humans) (.sequence []), .draw .forEachTappedHuman _] =>
    "you may tap any number of untapped Humans you control. Draw a card for each Human tapped this way"
  | .sequence [.createTokens kind (.fixed 1) false _ _, .attach .source .createdToken] =>
    s!"{TokenSpec.createPhrase kind 1}, then attach this Equipment to it"
  | .sequence [.gainLife (.fixed n), .searchLibrary (.put .basicLandOnTop .asPrinted .none)] =>
    s!"you gain {n} life. You may search your library for a basic land card, reveal it, then shuffle and put that card on top"
  | .sequence [.destroy .oppArtifactsEnchantments .countDestroyed, .gainLife .forEachDestroyedThisWay] =>
    "destroy all artifacts and enchantments your opponents control. You gain 1 life for each permanent destroyed this way"
  | .sequence [.putCounters (.ofKind .plusOnePlusOne) .eachOther, .gainLife .perOtherCreature] =>
    "put a +1/+1 counter on each other creature you control. You gain 1 life for each other creature you control"
  | .sequence [.dealDamage (.fixed n) .target .markedPermanent, .«if» (.dealtDamageToSubtype subtype) (.destroy .permanentDealtDamage .none)] =>
    s!"it deals {n} damage to {noun}. If a {subtype} is dealt damage this way, destroy it"
  | .sequence [.returnToHand .permanent .returnedPermanent, .«if» .returnedPermanent (.putCounters (.ofKind .plusOnePlusOne 1) .source)] =>
    s!"return {noun} to its owner's hand. If you do, put a +1/+1 counter on this creature"
  | .sequence [.pump (.fixed p) (.fixed t)
      (.intersection [.creaturesYouControl, .union parts]),
      .pump (.fixed oppP) (.fixed oppT) .opponentsCreatures] =>
    match othersOfSubtypeParts parts with
    | some subtypes =>
      let who :=
        if subtypes == #[.goblin, .orc] then "other Goblins and Orcs you control"
        else s!"other {joinedSubtypes subtypes} you control"
      s!"{who} get {signedStat p}/{signedStat t} until end of turn. Creatures your opponents control get {signedStat oppP}/{signedStat oppT} until end of turn"
    | none =>
      "resolve each step"
  | .sequence
      [.noteResolveThisTurn 3,
       .«if» (.nthResolve 1) (.gainLife (.fixed 1)),
       .«if» (.nthResolve 2) (.draw (.fixed 1)),
       .«if» (.nthResolve 3) (.putCounters (.ofKind .plusOnePlusOne) .youControl)] =>
    "you gain 1 life if this is the first time this ability has resolved this turn. If it's the second time, draw a card. If it's the third time, put a +1/+1 counter on each creature you control"
  | .sequence [.dealDamage .lastKnownPower .permanent .excess, .amass .notedExcess _ _ _] =>
    s!"Bolg deals damage equal to the sacrificed creature's power to {noun}. If excess damage was dealt this way, amass Goblins X, where X is that excess damage"
  | .sequence [.createTokens _ (.fixed 2) true _ _, .«if» (.atLeast (.count (.intersection [.equipped, .legendaryCreaturesYouControl])) (.fixed 1)) .markRecentTokensAttacking] =>
    "create two tapped 1/1 white Spirit creature tokens with flying. If that creature is legendary, instead create two of those tokens that are tapped and attacking"
  | .sequence [.dealDamage (.fixed 1) .target .markedPermanent, .amass (.fixed 1) .orc false _] =>
    s!"this creature deals 1 damage to {noun}. Then amass Orcs 1"
  | .sequence [.untap .attackingCreatures, .additionalCombatPhase] =>
    "untap all attacking creatures. After this phase, there is an additional combat phase"
  | .sequence [.destroy .target .forAmass, .amass .notedPower _ _ (.controller .target), .«if» .youControlledDestroyed (.draw (.fixed 1))] =>
    s!"destroy {noun}. Its controller amasses Goblins X, where X is that creature's power. If you controlled that creature, draw a card"
  | .sequence [.may (.discard .hand) (.sequence []), .draw .discardedHand _, .«if» .enduringStoryNoted (.dealDamage .discardedHand (.player .eachOpponent))] =>
    "you may discard your hand. Draw X cards, where X is the number of cards discarded this way. If you have an enduring story, this deals X damage to each opponent"
  | .sequence [.putCounters (.ofKind .trample) .permanent, .becomeBear, .«if» ((.atLeast (.count (.youControl (.subtype .bear))) (.fixed 3))) (.draw (.fixed 2))] =>
    s!"put a trample counter on up to one {noun}. It becomes a Bear in addition to its other types. Then if you control three or more Bears, draw two cards"
  | .sequence [.mill (.fixed n) .you .milledCards, .returnToHand (.milledSubtype subtype)] =>
    s!"mill {n} cards, then put all {subtype} cards from among them into your hand"
  | .sequence [.tap .enchanted, .removeCounters .all .enchanted] =>
    "tap enchanted creature and remove all counters from it"
  | .sequence [.putCounters (.ofKind .quest) .source,
      .«if» ((.atLeast (.count .questCounters) (.fixed 6)))
        (.sequence [.sacrifice (.sacrificedSource .movedAsSacrificed), .searchLibrary (.put .dragon .asPrinted .none)])] =>
    "put a quest counter on this enchantment. If it has six or more quest counters on it, sacrifice it. If you do, search your hand and/or library for a Dragon card and put it onto the battlefield. If you search your library this way, shuffle"
  | .sequence [.draw (.fixed 1), .discard (.cards 1), .put .discardedLand .tapped _] =>
    "draw a card, then discard a card. If you discard a land card this way, put it from your graveyard onto the battlefield tapped"
  | .sequence [.putCounters .honePerOpponent .source, .attach .source (.target .laterCreature)] =>
    "put a hone counter on this for each creature target opponent controls. Attach this to up to one target creature you control"
  | .sequence [.attach .anyYouControl .target, .«if» .equipmentAttached (.fight .equipmentHost .reflexive)] =>
    "attach any number of target Equipment you control to target creature you control. When one or more Equipment become attached to that creature this way, that creature deals damage equal to its power to up to one target creature"
  | .sequence [.draw .equalToManaSpent _, .«if» .manaSpent (.discard (.cards n))] =>
    let disc := if n == 2 then "two cards" else cardPhrase n
    s!"draw X cards, where X is the amount of mana spent to cast that spell, then discard {disc}"
  | .sequence [.exile .landsYouControl .forLater .lands, .put .notedLands .tapped _] =>
    "exile up to three target lands you control, then return them to the battlefield tapped under their owner's control"
  | .sequence [.revealLibrary .untilInstantOrSorcery (.exile .top .forLater .impulse) .damagedPlayer,
      .mayCast .impulse .unlimited .withoutPaying .none] =>
    "that player exiles cards from the top of their library until they exile an instant or sorcery card. You may cast that card without paying its mana cost. Then that player puts the exiled cards that weren't cast this way on the bottom of their library in a random order"
  | .sequence [.putCounters (.ofKind .influence) .source, .scry (.fixed 2), .may (.draw _ .opponentHasYou) _] =>
    "put an influence counter on this and scry 2. Then target opponent may have you draw a card. If that player doesn't, you mill X cards, where X is the number of influence counters on this, and that player loses life equal to the total mana value of those cards"
  | .sequence [.mill (.fixed 2) .eachOpponent .opponentsMilled,
      .«if» .opponentsMilled (.queueReflexive (.mayCast .milledSpell .causingSpell .withoutPaying))] =>
    "each opponent mills two cards. When one or more cards are milled this way, exile target enchantment, instant, or sorcery card with equal or lesser mana value than that spell from an opponent's graveyard. Copy the exiled card. You may cast the copy without paying its mana cost"
  | .sequence [.sacrifice .combatDamager, .ringTempts] =>
    "each opponent sacrifices a creature of their choice that dealt combat damage to you this turn. The Ring tempts you"
  | .sequence [.putCounters (.ofKind .plan) .source, .scry (.fixed n)] =>
    s!"scry {n} and put a plan counter on this enchantment"
  | .sequence [.putCounters (.ofKind .plan) .source, .draw (.fixed 1), .discard (.cards 1)] =>
    "draw a card, then discard a card and put a plan counter on this enchantment"
  | .sequence [.putCounters (.ofKind .plan) .source, .createTokens _ (.fixed 1) false _ _] =>
    "create a 2/1 black Villain creature token with menace and put a plan counter on this enchantment"
  | .sequence [.putCounters (.ofKind .plan) .source, .loseLife (.fixed n) .eachOpponent, .gainLife (.fixed m)] =>
    s!"each opponent loses {n} life and you gain {m} life. Put a plan counter on this enchantment"
  | .sequence [.putCounters (.ofKind .plan) .source, .draw (.fixed 1), .loseLife (.fixed 1)] =>
    "you draw a card, lose 1 life, and put a plan counter on this enchantment"
  | .sequence [.putCounters (.ofKind .plan) .source, .createTokens _ (.fixed 1) true _ _] =>
    "create a tapped Treasure token and put a plan counter on this enchantment"
  | .sequence [.putCounters (.ofKind .plan) .source,
      .putCounters (.ofKind .plusOnePlusOne) (.permanent true)] =>
    "put a +1/+1 counter on target creature you control and a plan counter on this enchantment"
  | .sequence [.sacrifice .plan, .draw (.fixed 1), .putCounters (.ofKind .plusOnePlusOne) .youControl] =>
    "sacrifice it, draw a card, and put a +1/+1 counter on each creature you control"
  | .sequence [.sacrifice .plan .forReflexive,
      .«if» .planWasSacrificed (.queueReflexive (.returnToHand (.graveyardInstants 2)))] =>
    "sacrifice it. When you do, return up to two target instant and/or sorcery cards from your graveyard to your hand"
  | .sequence [.sacrifice .plan .forReflexive,
      .«if» .planWasSacrificed (.queueReflexive (.gainControl .duringNextTurn))] =>
    "sacrifice it. When you do, you control target opponent during their next turn"
  | .sequence [.sacrifice .plan .forReflexive,
      .«if» .planWasSacrificed (.queueReflexive (.exile (.opponentTop 5) (.mayCastUpTo 2)))] =>
    "sacrifice it. When you do, target opponent exiles the top five cards of their library. You may cast up to two spells from among the exiled cards without paying their mana costs"
  | .sequence [.sacrifice .plan, .createTokens _ (.fixed n) false _ _] =>
    s!"sacrifice it and create {englishNumber n.toNat} 2/2 colorless Robot Villain artifact creature tokens"
  | .sequence [.sacrifice .plan .forReflexive,
      .«if» .planWasSacrificed (.queueReflexive (.dealDamage (.fixed n) .target .divided))] =>
    s!"sacrifice it. When you do, it deals {n} damage divided as you choose among one or two targets"
  | .sequence [.sacrifice .plan .forReflexive,
      .«if» .planWasSacrificed (.queueReflexive (.putCounters (.ofKind .indestructible) .permanent))] =>
    "sacrifice it. When you do, put an indestructible counter on target creature you control"
  | .sequence [.attach .source .target, followup] =>
    match attachedFollowupPhrase followup with
    | some phrase => s!"attach it to {noun}. {capitalizeAscii phrase}"
    | none => "resolve each step"
  | .sequence [.exile .target .untilSourceLeaves .copyAndHost, .becomeCopy .noted] =>
    "exile up to one target creature other than enchanted creature until this Aura leaves the battlefield. Enchanted creature becomes a copy of that creature until this Aura leaves the battlefield"
  | .sequence [.draw (.fixed 1), .may (.put .landFromHand .tapped _) _] =>
    "draw a card, then you may put a land card from your hand onto the battlefield tapped"
  | .sequence [.draw (.fixed 1), .«if» (.atLeast (.count (.othersOfSubtype .hero)) (.fixed 1)) (.gainLife (.fixed 2))] =>
    "draw a card. If you control another Hero, you gain 2 life"
  | .sequence [.createTokens _ (.fixed 1) false .you .invasion,
      .putCounters .plusOneNoted .createdToken,
      .putCounters (.ofKind .invasion) .source] =>
    "create a 1/1 red Alien creature token with haste and \"This token attacks each combat if able.\" Put a +1/+1 counter on it for each invasion counter on this enchantment, then put an invasion counter on this enchantment"
  | .sequence [.createTokens _ (.fixed 1) false .you .remember,
      .attach .createdToken .source] =>
    "create a colorless Equipment artifact token named Sturdy Shield with \"Equipped creature gets +1/+2\" and equip {2}. Attach it to this creature"
  | .sequence [.exile .graveyardCard .forLater .playCard, .grantPlayNotedUntilNextTurn] =>
    s!"exile {noun}. {playThatCardUntilNextTurnPhrase}"
  | .sequence [.tap .target, .cant (.untapWhileYouControl .target)] =>
    s!"tap {noun}. That creature can't become untapped for as long as you control this creature"
  | .sequence [.tap (.target .ifPresent), .lose .allAbilities (.target .ifPresent)] =>
    "tap up to one target creature. It loses all abilities for as long as this remains on the battlefield"
  | .sequence [.grant (.keywords k) .target,
      .«if» (.atLeast (.count (.target .creature)) (.fixed 1)) (.putCounters (.ofKind .plusOnePlusOne) .permanent),
      .«if» (.atLeast (.count (.target .planeswalker)) (.fixed 1)) (.putCounters (.ofKind .loyalty) .permanent)] =>
    s!"{noun} gains {KeywordAbility.joinedAnd k} until end of turn. Put a +1/+1 counter on it if it's a creature. Put a loyalty counter on it if it's a planeswalker"
  | .sequence [.draw (.fixed 2), .«if» (.not (.atLeast .libraryCards (.fixed 1))) .winTheGame, .«if» (.atLeast .libraryCards (.fixed 1)) .shuffleSource] =>
    "draw two cards. If your library has no cards in it, you win the game. Fblthp's owner shuffles him into their library"
  | .sequence [.armSurveilReturnLifeGained, .surveil (.fixed 1)] =>
    "if you gained life this turn, surveil 1. If you put a card with mana value less than or equal to the amount of life you gained this turn into your graveyard this way, put that card into your hand"
  | .sequence [.pump (.fixed 3) (.fixed 0) .target, .grant (.keywords k) .target] =>
    s!"{noun} gets +3/+0 and gains {KeywordAbility.joinedAnd k} until end of turn"
  | .sequence [.pump (.fixed p) (.fixed t) .target, .grant (.keywords k) .target] =>
    if k == #[Keyword.trample] then
      s!"{noun} gets {signedStat p}/{signedStat t} and gains trample until end of turn"
    else
      "resolve each step"
  | .sequence [.becomeArtifact .target, .grant (.keywords k) .target] =>
    if k == #[Keyword.indestructible] then
      s!"until end of turn, {noun} becomes an artifact in addition to its other types and gains indestructible"
    else
      "resolve each step"
  | .sequence [.tap .target, .putCounters (.ofKind .stun) .permanent] =>
    s!"tap {noun} and put a stun counter on it"
  | .sequence [.destroy .target,
      .createTokens _ (.fixed 1) false (.controller .target) _] =>
    s!"destroy {noun}. They create a Treasure token"
  | .sequence [.may (.put .artifactFromHand _ .forAttach) _, .«if» (.atLeast (.count .putEquipment) (.fixed 1)) (.attach .putArtifact .notedHost)] =>
    "you may put an artifact card from your hand onto the battlefield. If it's an Equipment, attach it to this creature"
  | .sequence [.loseLife (.fixed n) (.target .opponent), .gainLife (.fixed m)] =>
    s!"target opponent loses {n} life and you gain {m} life"
  | .sequence [.pump (.fixed p) (.fixed 0) (.intersection [.creaturesYouControl, .youControl (.subtype .elf)]),
      .grant (.keywords k) (.intersection [.creaturesYouControl, .youControl (.subtype .elf)])] =>
    if k == #[Keyword.vigilance] then
      s!"Elves you control get {signedStat p}/+0 and gain vigilance until end of turn"
    else
      "resolve each step"
  | .sequence [.searchLibrary (.exile (.basicUpTo .plains max) .forLater .linked),
      .gainLife (.fixed life)] =>
    s!"search your library for up to {max} basic Plains cards, exile them, then shuffle. You gain {life} life"
  | .sequence [.createTokens _ (.fixed 1) false _ _,
      .«if» ((.atLeast (.count (.youControl (.subtype .treasure))) (.fixed 4))) (.sacrifice (.sacrificedSource .isSacrificed) .noted),
      .«if» .sourceWasSacrificed (.createTokens _ (.fixed 1) false _ _)] =>
    "create a Treasure token. Then if you control four or more Treasures, sacrifice this Saga. If you do, create a 6/6 red Dragon creature token with flying"
  | .sequence [.draw (.fixed 1), .grant .basePowerEqualHand .source] =>
    "draw a card. Until end of turn, this creature's base power is equal to the number of cards in your hand"
  | .sequence [.putCounters (.ofKind .plusOnePlusOne) .source, .scry (.fixed 1)] =>
    "put a +1/+1 counter on this creature. Scry 1"
  | .sequence [.putCounters (.ofKind .plusOnePlusOne 2) .source, .copyCause] =>
    "copy that spell. You may choose new targets for the copy. Put two +1/+1 counters on this creature"
  | .sequence _ =>
    "resolve each step"
  | .gainLife amount =>
    match amount with
    | .fixed n => s!"you gain {n} life"
    | .equalToTargetPower =>
      "you gain life equal to that card's power"
    | .forEachDestroyedThisWay =>
      "you gain 1 life for each permanent destroyed this way"
    | .perOtherCreature =>
      "you gain 1 life for each other creature you control"
    | .attachedEquipment =>
      "you gain X life, where X is the number of Equipment attached to it"
    | _ =>
      "you gain life"
  | .may (.pay cost) (.draw (.fixed 1)) .ifYouDo =>
    if cost == CostSpec.sacrificeArtifactOrDiscardCard then
      "you may sacrifice an artifact or discard a card. If you do, draw a card"
    else
      match cost.soleGenericMana? with
      | some n => s!"you may pay \{{n}}. If you do, draw a card"
      | none =>
        if cost.items.any (fun | .sacrifice _ _ => true | _ => false) then
          "you may sacrifice that. If you do, do that"
        else if cost.items.any (fun | .discard _ _ => true | _ => false) then
          "you may discard that. If you do, do that"
        else "you may pay. If you do, draw a card"
  | .«if» (.not (.atLeast (.count .legendaryCreaturesYouControl) (.fixed 1))) (.putOnLibrary .bottom .cardFromHand) =>
    "if you don't control a legendary creature, put a card from your hand on the bottom of your library"
  | .exile what how note =>
    match what, how, note with
    | .target, .leaveTrigger, .none =>
      if t.allowsZeroTargets then s!"you may exile {noun}" else s!"exile {noun}"
    | .target, .untilSourceLeaves, .copyAndHost =>
      "exile up to one target creature other than enchanted creature until this Aura leaves the battlefield"
    | .target, .untilSourceLeaves, .none =>
      if t.allowsZeroTargets then
        if t.targeting.spec == TargetSpec.defendingPlayerCreature then
          s!"you may exile {noun} until this leaves the battlefield"
        else
          s!"you may exile {noun}"
      else
        s!"exile {noun} until this leaves the battlefield"
    | .top, .playUntilNextTurn, .none =>
      s!"exile the top card of your library. {playThatCardUntilNextTurnPhrase}"
    | .top, .playThisTurn, .ifHero =>
      "exile the top card of your library. If it is a Hero card, this gets +2/+1 until end of turn. You may play that card this turn"
    | (.target .eachPermanent), .untilSourceLeaves, .none =>
      "for each opponent, exile up to one target nonland permanent that player controls until this leaves the battlefield"
    | .target, .nextEndStep, .none =>
      s!"exile up to one {noun}. Return that card to the battlefield under its owner's control at the beginning of the next end step"
    | .landsYouControl, .forLater, .lands =>
      "exile up to three target lands you control"
    | .graveyardCard, .forLater, .playCard =>
      s!"exile {noun}"
    | .target, .forLater, .none =>
      if noun.isEmpty then "exile it" else s!"exile {noun}"
    | .source, .forLater, .none =>
      "exile this creature"
    | .enchanted, .forLater, .none =>
      "exile enchanted creature"
    | (.target .whileSource), .forLater, .none =>
      "exile that creature"
    | .top, .forLater, .impulse =>
      "exile cards from the top of their library until they exile an instant or sorcery card"
    | _, _, _ =>
      "exile it"
  | .put what how note =>
    match what, how, note with
    | .linkedExile, _, _ =>
      "return the exiled card to the battlefield under its owner's control"
    | .nonlandMvAtMost mv, _, _ =>
      s!"put up to one target nonland permanent card with mana value {mv} or less from a graveyard onto the battlefield under its owner's control"
    | .source, .asArtifact, _ =>
      "if they were a creature, return them to the battlefield. They're an artifact"
    | .source, .underOwner, .entering _ =>
      "return this from its owner's graveyard to the battlefield under its owner's control"
    | .cause _, .underOwner, _ =>
      "return it to the battlefield under its owner's control"
    | .notedLands, .tapped, _ =>
      "return those lands to the battlefield tapped"
    | .discardedLand, .tapped, _ =>
      "if you discard a land card this way, put it onto the battlefield tapped"
    | .landFromHand, .tapped, _ =>
      "put a land card from your hand onto the battlefield tapped"
    | .artifactFromHand, _, .forAttach =>
      "put an artifact card from your hand onto the battlefield"
    | .randomCreature, _, _ =>
      "put a random creature card from among them onto the battlefield"
    | .revealed, _, _ =>
      "put that card onto the battlefield"
    | .forest, _, _ =>
      "put that card onto the battlefield"
    | .basicLandOnTop, _, _ =>
      "put that card on top of your library"
    | .dragon, _, _ =>
      "put it onto the battlefield"
    | .creatureMvAtMost mv, _, _ =>
      s!"return target creature card with mana value {mv} or less from your graveyard to the battlefield"
    | _, _, _ =>
      "put it onto the battlefield"
  | .removeCounters what who =>
    match what, who with
    | .hope, .source =>
      "remove a hope counter from this"
    | .time, .source =>
      "remove a time counter from it"
    | .all, .enchanted =>
      "remove all counters from enchanted creature"
    | _, _ =>
      "remove counters"
  | .«if» .removedHope (.draw (.fixed 1)) =>
    "if a hope counter was removed this way, draw a card"
  | .«if» (.not .hopeOnSource) (.sequence [.sacrifice .source, .gainLife (.fixed 4)]) =>
    "if this has no hope counters on it, sacrifice it and you gain 4 life"
  | .tap .humans =>
    "tap any number of untapped Humans you control"
  | .destroy .oppArtifactsEnchantments .countDestroyed =>
    "destroy all artifacts and enchantments your opponents control"
  | .destroy .permanentDealtDamage .none =>
    "destroy the permanent dealt damage this way"
  | .destroy .target .forAmass | .destroy .target .none | .destroy .target .chosenToken =>
    if noun.isEmpty then "destroy it" else s!"destroy {noun}"
  | .destroy .source _ =>
    "destroy this creature"
  | .destroy .enchanted _ =>
    "destroy enchanted creature"
  | .destroy (.target .whileSource) _ =>
    "destroy that creature"
  | .destroy _ _ =>
    "destroy it"
  | .recruit .recruit =>
    "recruit"
  | .recruit .you =>
    "you recruit"
  | .amass .lastKnownPower subtype _ _ =>
    s!"amass {pluralizeName subtype} X, where X is this creature's power"
  | .amass .notedExcess subtype _ _ =>
    s!"amass {pluralizeName subtype} X, where X is the excess damage"
  | .amass .notedPower subtype _ (.controller .target) =>
    s!"its controller amasses {pluralizeName subtype} X, where X is that creature's power"
  | .amass (.fixed n) subtype true _ =>
    s!"amass {pluralizeName subtype} {n}, then attach this Equipment to the amassed Army"
  | .amass (.fixed n) subtype _ _ =>
    s!"amass {pluralizeName subtype} {n}"
  | .amass _ _ _ _ =>
    "amass"
  | .createTokens kind amount tapped who note =>
    if kind == .axe then
      match note with
      | .attachReflexive =>
        "create a colorless Equipment artifact token named Axe with \"Equipped creature gets +1/+0\" and equip {2}. When you do, attach it to target creature you control"
      | _ =>
        "create a colorless Equipment artifact token named Axe with \"Equipped creature gets +1/+0\" and equip {2}"
    else if kind == .zabu then
      "create Zabu, a legendary 2/2 green Cat creature token with \"Landfall — Whenever a land you control enters, put a +1/+1 counter on Zabu.\""
    else if kind == .theVoid then
      s!"{noun} creates The Void, a legendary 5/5 black Horror Villain creature token with flying, indestructible, and \"The Void attacks each combat if able.\""
    else if kind == .redwing then
      "create Redwing, a legendary 1/1 blue Bird Scout creature token with flying and \"Whenever Redwing attacks, surveil 1.\""
    else if kind == .alien then
      "create a 1/1 red Alien creature token with haste"
    else if kind == .galactus then
      "create Galactus, a legendary 16/16 black Elder Alien creature token with flying and trample"
    else if kind == .sturdyShield then
      "create a colorless Equipment artifact token named Sturdy Shield"
    else if kind == .merfolk && amount == .blueManaSymbols then
      "create a 1/1 blue Merfolk creature token for each blue mana symbol in that spell's mana cost"
    else
      match who, amount with
      | .you, .oppArtifacts =>
        "create X tapped Treasure tokens, where X is the number of artifacts your opponents control"
      | .you, .damagedPlayerArtifacts =>
        "you create a Treasure token for each artifact that player controls"
      | .you, .lastKnownPower =>
        if kind == .birdSoldier then
          "create a 4/4 white Bird Soldier creature token with flying for each creature returned to your hand this way"
        else
          "create that many Treasure tokens"
      | .you, .perSubtype subtype =>
        s!"create a {TokenSpec.oracleNoun kind} token for each {subtype} you control"
      | .you, .chosenCreatureType =>
        "choose a creature type. Create a Treasure token for each creature you control of that type"
      | .controller .target, _ =>
        "they create a Treasure token"
      | .you, .fixed n =>
        TokenSpec.createPhrase kind n.toNat (tapped := tapped)
      | _, _ =>
        "create a token"
  | .attach what host =>
    match what, host with
    | .source, .createdToken =>
      "attach this Equipment to it"
    | .source, .target =>
      s!"attach it to {noun}"
    | .target, .optionalCreature =>
      "attach target Equipment you control to up to one target creature you control"
    | .source, (.target .laterCreature) =>
      "attach this to up to one target creature you control"
    | .anyYouControl, .target =>
      "attach any number of Equipment you control to target creature you control"
    | .createdToken, .source | .putArtifact, .notedHost =>
      "attach it to this creature"
    | _, _ =>
      "attach it"
  | .«if» (.dealtDamageToSubtype subtype) (.destroy .permanentDealtDamage .none) =>
    s!"if a {subtype} is dealt damage this way, destroy it"
  | .addMana types amount =>
    match amount with
    | .perChargeCounter =>
      s!"add {manaSymbolsText types} for each charge counter on this enchantment"
    | .fixed 1 => s!"add {manaSymbolsText types}"
    | _ => "add mana"
  | .or [.tap .target, .untap .target] =>
    if t.targeting.spec == TargetSpec.nonland then
      "choose one — • Tap target nonland permanent. • Untap target nonland permanent"
    else
      "choose one — tap target creature an opponent controls; untap target creature you control"
  | .becomePT (.fixed p) (.fixed t) =>
    s!"you may have this creature's base power and toughness become {p}/{t} until end of turn"
  | .becomePT _ _ =>
    "you may have this creature's base power and toughness become those values until end of turn"
  | .«if» .returnedPermanent (.putCounters (.ofKind .plusOnePlusOne 1) .source) =>
    "if you do, put a +1/+1 counter on this creature"
  | .lookAtTopRevealTypes (.fixed n) types =>
    let joined :=
      match types.toList with
      | [a, b] => s!"a {a} or {b} card"
      | xs => s!"a {String.intercalate " or " xs} card"
    s!"look at the top {n} cards of your library. You may reveal {joined} from among them and put it into your hand. {restOnBottomRandomPhrase}"
  | .lookAtTopRevealTypes _ _ =>
    "look at the top cards of your library"
  | .gainControl .untilEndOfTurn =>
    s!"gain control of {noun} until end of turn. Untap it. It gains haste until end of turn"
  | .gainControl .whileSourceRemains =>
    s!"gain control of {noun} for as long as this Saga remains on the battlefield"
  | .gainControl .duringNextTurn =>
    "you control target opponent during their next turn"
  | .honeEachEquipment =>
    "put a hone counter on each Equipment you control"
  | .cascade =>
    "exile cards from the top of your library until you exile a nonland card that costs less. You may cast it without paying its mana cost"
  | .noteResolveThisTurn _ =>
    "count another resolution of this ability this turn"
  | .«if» (.nthResolve n) _ =>
    s!"if this is time {n} this ability has resolved this turn"
  | .chooseModes modes how =>
    if modes == TriggerResolution.allianceModes && how == .oneUnusedThisTurn then
      "choose one that hasn't been chosen this turn — • Add {G}{G}{G}. • Put a +1/+1 counter on each creature you control. • Scry 2, then draw a card"
    else if modes == TriggerResolution.gollumModes && how == .oneUnused then
      "choose one that hasn't been chosen — • Put a +1/+1 counter on Gollum. • Each opponent loses 2 life and you gain 2 life. • Draw a card"
    else if modes == TriggerResolution.upToXModes && how == .alreadyChosen then
      "choose up to X — • Discard a card, then draw a card. • Target opponent loses 2 life. • Destroy target token. • Each player sacrifices a creature of their choice"
    else if modes == TriggerResolution.hydeModes && how == .plusOneOrRemoveCounter then
      "choose one — put a +1/+1 counter on this, or remove a counter from a creature you control and draw a card"
    else if modes == TriggerResolution.visionModes && how == .vision then
      "choose one that hasn't been chosen this turn — • This gains double strike until end of turn. • This gains indestructible until end of turn. • Draw a card"
    else
      "choose a mode"
  | .returnToHand what note =>
    match what, note with
    | .graveyardCard, .none =>
      s!"return {noun} to your hand"
    | .permanent, .returnedPermanent =>
      s!"return up to one {noun} to its owner's hand"
    | .graveyardPermanent, .none =>
      s!"choose {noun.replace " from your graveyard" " in your graveyard"} that was put there from anywhere this turn. Return it to your hand"
    | .milledSubtype subtype, .none =>
      s!"put all {subtype} cards milled this way into your hand"
    | .source, .none =>
      "return this card from your graveyard to your hand"
    | .revealed, .none =>
      "put it into your hand"
    | .basicLand, .none =>
      "put it into your hand"
    | .linkedExile, .none =>
      "put a card exiled with this Saga into its owner's hand"
    | .cause _, .none =>
      "return that card to its owner's hand"
    | _, _ =>
      "return it to a hand"
  | .or [.putCounters (.ofKind .plusOnePlusOne) .permanent, .createTokens _ (.fixed 1) false _ _] =>
    "choose one — • Put a +1/+1 counter on target Wolf you control. • Create a Treasure token"
  | .mayCast origin maxMv cost note =>
    match origin, maxMv, cost, note with
    | .graveyard, .unlimited, .pay, .exileInstead =>
      "you may cast an artifact, instant, or sorcery spell from your graveyard. If an instant or sorcery spell cast this way would be put into your graveyard, exile it instead"
    | .hand, .twiceLegendaryWizards, .withoutPaying, .none =>
      "you may cast an instant or sorcery spell with mana value X or less from your hand without paying its mana cost, where X is twice the number of legendary Wizards you control"
    | .hand, .lastKnown, .withoutPaying, .none =>
      "you may cast an instant or sorcery spell from your hand with mana value less than or equal to that damage without paying its mana cost"
    | .impulse, .unlimited, .withoutPaying, .none =>
      "you may cast that card without paying its mana cost"
    | .nextRedOrGreenCreature, .unlimited, .withoutPaying, .none =>
      "the next red or green creature spell you cast this turn can be cast without paying its mana cost"
    | .looked, .greatestAttackingPower, .withoutPaying, .none =>
      "you may cast a spell from among them with mana value less than or equal to the greatest power among attacking creatures you control without paying its mana cost"
    | _, _, _, _ =>
      "you may cast a spell"
  | .grant what who =>
    match what, who with
    | .doubleStrike, .equippedAttackers =>
      "each equipped attacking creature gains double strike until end of turn"
    | .protectionEverything, .youIfCast =>
      "if you cast it, you gain protection from everything until your next turn"
    | .keywords k, .target =>
      s!"{noun} gains {KeywordAbility.joinedAnd k} until end of turn"
    | .keywords k, .source =>
      s!"this creature gains {KeywordAbility.joinedAnd k} until end of turn"
    | .keywords k, .enchanted =>
      s!"enchanted creature gains {KeywordAbility.joinedAnd k} until end of turn"
    | .keywords k, (.target .whileSource) =>
      s!"that creature gains {KeywordAbility.joinedAnd k} until end of turn"
    | .keywords k, .creaturesYouControl =>
      s!"creatures you control gain {KeywordAbility.joinedAnd k} until end of turn"
    | .keywords k, .intersection [.creaturesYouControl, .youControl (.subtype subtype)] =>
      s!"{subtype}s you control gain {KeywordAbility.joinedAnd k} until end of turn"
    | .hexproofWhileSource, .target =>
      s!"{noun} gains hexproof for as long as this Saga remains on the battlefield"
    | .preventDamageWhileSource, _ =>
      "prevent all damage that would be dealt by up to one target creature for as long as this Saga remains on the battlefield"
    | .landfallCreateElf, .source =>
      "this Saga gains \"Landfall — Whenever a land you control enters, create a 1/1 green Elf creature token.\""
    | .assignCombatDamageEqualToughness, .creaturesYouControl =>
      "until end of turn, creatures you control with toughness greater than their power assign combat damage equal to their toughness rather than their power"
    | .basePowerEqualHand, .source =>
      "until end of turn, this creature's base power is equal to the number of cards in your hand"
    | .ironFistTap, .source =>
      "this gains \"{T}: This deals damage equal to its power to any other target\" until end of turn"
    | .keywords _, .spellTargets =>
      "those creatures gain flying until end of turn"
    | _, _ =>
      "grant"
  | .revealLibrary how thenDo who =>
    match how, thenDo, who with
    | .top n, .put .randomCreature .asPrinted .none, .you =>
      s!"reveal the top {n} cards of your library. Put a random creature card from among them onto the battlefield. {restOnBottomRandomPhrase}"
    | .untilCreature,
      .ifElse .revealedManaValueAtMostLands
        (.put .revealed .asPrinted .none) (.returnToHand .revealed .none),
      .you =>
      s!"reveal cards from the top of your library until you reveal a creature card. If its mana value is less than or equal to the number of lands you control, put it onto the battlefield. Otherwise, put it into your hand. {restOnBottomRandomPhrase}"
    | .untilSaga, .put .revealed .asPrinted .none, .you =>
      "reveal cards from the top of your library until you reveal a Saga card. Put that card onto the battlefield and the rest on the bottom of your library in a random order"
    | .untilInstantOrSorcery, .exile .top .forLater .impulse, .damagedPlayer =>
      "that player exiles cards from the top of their library until they exile an instant or sorcery card"
    | .untilNonland,
      .may (.putCounters (.ofKind .plusOnePlusOne 1) .source)
        (.exile .top .forLater .anyManaThisTurn) .ifYouDont,
      .announced =>
      "that player exiles cards until a nonland card"
    | .top n, .mayCast .looked .greatestAttackingPower .withoutPaying .none, .you =>
      s!"look at the top {n} cards of your library. You may cast a spell from among them with mana value less than or equal to the greatest power among attacking creatures you control without paying its mana cost. {restOnBottomRandomPhrase}"
    | _, _, _ =>
      "reveal cards from a library"
  | .«if» (.atLeast .cardsDrawnThisTurn (.fixed 2)) (.sequence [.pump (.fixed 3) (.fixed 0) .target, .grant (.keywords k) .target]) =>
    s!"if you've drawn two or more cards this turn, {noun} gets +3/+0 and gains {KeywordAbility.joinedAnd k} until end of turn"
  | .mill amount who note =>
    match amount, who, note with
    | .fixed n, .you, .none | .fixed n, .you, .milledCards =>
      s!"mill {n} cards"
    | .fixed n, .target .player, .none =>
      s!"{noun} mills {n} cards"
    | .thatManyLost, .thatPlayer, .none =>
      "that player mills that many cards"
    | .fixed n, .eachOpponent, .opponentsMilled =>
      s!"each opponent mills {n} cards"
    | _, _, _ =>
      "mill"
  | .may (.pay cost) (.putCounters .plusOneSacrificedPower .source) .ifYouDo =>
    if cost == CostSpec.sacrificeAnotherCreature then
      "you may sacrifice another creature. If you do, put a number of +1/+1 counters on this creature equal to the sacrificed creature's power"
    else "you may pay that cost. If you do, put a number of +1/+1 counters on this creature equal to the sacrificed creature's power"
  | .may (.pay cost) (.returnToHand .source) .ifYouDo =>
    if cost.isManaOnly && !cost.isEmpty then
      s!"you may pay {cost.manaCost}. If you do, return this card from your graveyard to your hand"
    else
      s!"you may {cost.toInlinePhrase}. If you do, return this card from your graveyard to your hand"
  | .copySelfNonlegendary =>
    "if they're not a token, create two tokens that are copies of them, except the tokens aren't legendary"
  | .may (.pay cost)
      (.sequence [.draw (.fixed 1), .createTokens _ (.fixed 1) false _ _]) .ifYouDo =>
    if cost == CostSpec.sacrificeAnotherCreatureOrArtifactSpec then
      "you may sacrifice another creature or artifact. If you do, draw a card and create a Treasure token"
    else "you may pay that cost. If you do, draw a card and create a Treasure token"
  | .ringTempts =>
    "the Ring tempts you"
  | .may (.discard .hand) (.draw (.fixed n)) .ifYouDo =>
    s!"you may discard your hand. If you do, draw {cardPhrase n.toNat}"
  | .queueReflexive (.pump .perPlains .perPlains .target) =>
    "whenever you attack this turn, target creature you control gets +1/+1 until end of turn for each Plains you control"
  | .spellsCostLess _ (.fixed n) =>
    s!"spells you cast this turn cost \{{n}} less to cast"
  | .spellsCostLess _ _ =>
    "spells you cast this turn cost less to cast"
  | .may (.draw (.perControlled _) _) (.draw (.fixed 1) .eachOpponent) .ifYouDo =>
    "you may draw a card for each artifact you control. If you do, each opponent draws a card"
  | .investigate => "investigate"
  | .connive .source => "it connives"
  | .connive .target => s!"{noun} connives"
  | .connive .enteringVillain => "you may have it connive"
  | .connive _ => "connive"
  | .«if» (.or [.attackedWithSubtype attacked, .subtypeEntered entered]) (.draw (.fixed 1)) =>
    let attackedNoun := if attacked == .hero then "a Hero" else s!"a {attacked}"
    let enteredNoun := if entered == .hero then "a Hero" else s!"a {entered}"
    s!"if you attacked with {attackedNoun} this turn or {enteredNoun} entered the battlefield under your control this turn, draw a card"
  | .or [.createTokens _ (.fixed 1) false _ _, .createTokens _ (.fixed 1) false _ _] =>
    "create a Food token or a Treasure token"
  | .ifElse ((.atLeast (.count .creatureCardsInGraveyard) (.fixed 2)))
      (.createTokens _ (.fixed 1) true _ _) (.mill (.fixed 2)) =>
    "create a tapped 2/1 black Villain creature token with menace if there are two or more creature cards in your graveyard. Otherwise, mill two cards"
  | .ifElse ((.atLeast (.count (.target (.anotherSubtype .hero))) (.fixed 1)))
      (.putCounters (.ofKind .plusOnePlusOne 2) .permanent)
      (.putCounters (.ofKind .plusOnePlusOne) .permanent) =>
    "put a +1/+1 counter on target creature. If that creature is another Hero, put two +1/+1 counters on it instead"
  | .«if» (.atLeast (.count .putEquipment) (.fixed 1)) (.attach .putArtifact .notedHost) =>
    "if it's an Equipment, attach it to this creature"
  | .fight who how =>
    match who, how with
    | .source, .mutual =>
      "this fights up to one other target creature"
    | .announced, .upToOneOther =>
      "target creature you control fights up to one other target creature"
    | .announced, .mutual =>
      "target creature you control fights another target creature"
    | .equipmentHost, .reflexive =>
      "that creature deals damage equal to its power to up to one target creature"
    | _, _ =>
      "fight"
  | .revealFromHand count thenDo =>
    match count, thenDo with
    | .hand, .exile .target .untilSourceLeaves .none =>
      "choose target opponent and up to one target creature they control. They reveal their hand. You may exile a nonland card from their hand or the chosen creature until this leaves the battlefield"
    | .onePlusCreatureCards, .discard (.cards 1 (.target .opponent)) =>
      s!"{noun} reveals a number of cards from their hand equal to one plus the number of creature cards in your graveyard. You choose one of them. That player discards that card"
    | _, _ =>
      "reveal cards from their hand"
  | .or [.putCounters (.ofKind .plusOnePlusOne) .permanent, .returnToHand .graveyardCard] =>
    "choose one — • Put a +1/+1 counter on each of up to two target creatures. • Return target artifact or enchantment card from your graveyard to your hand"
  | .may (.tap .source) (.queueReflexive (.grant (.keywords k) .target)) .ifYouDo =>
    if k == #[Keyword.indestructible] then
      "you may tap this creature. When you do, another target nonattacking creature you control gains indestructible until end of turn"
    else
      "you may tap this creature. When you do, that ability triggers"
  | .markRecentTokensAttacking =>
    "those tokens enter tapped and attacking"
  | .«if» (.atLeast (.count (.intersection [.equipped, .legendaryCreaturesYouControl])) (.fixed 1)) .markRecentTokensAttacking =>
    "those tokens are tapped and attacking if that creature is legendary"
  | .additionalCombatPhase =>
    "after this phase, there is an additional combat phase"
  | .«if» .youControlledDestroyed (.draw (.fixed 1)) =>
    "if you controlled that creature, draw a card"
  | .«if» .enduringStoryNoted (.dealDamage .discardedHand (.player .eachOpponent)) =>
    "if you have an enduring story, this deals X damage to each opponent"
  | .becomeBear =>
    "it becomes a Bear in addition to its other types"
  | .«if» ((.atLeast (.count (.youControl (.subtype .bear))) (.fixed 3))) (.draw (.fixed 2)) =>
    "if you control three or more Bears, draw two cards"
  | .tap .enchanted | .tap .enchantedWhileSource => "tap enchanted creature"
  | .tap .source => "tap this creature"
  | .tap (.target .whileSource) => "tap that creature"
  | .«if» ((.atLeast (.count .questCounters) (.fixed 6))) (.sequence [.sacrifice (.sacrificedSource .movedAsSacrificed), .searchLibrary (.put .dragon .asPrinted .none)]) =>
    "if it has six or more quest counters on it, sacrifice it and search for a Dragon"
  | .«if» .equipmentAttached (.fight .equipmentHost .reflexive) =>
    "that creature deals damage equal to its power to up to one target creature"
  | .queueReflexive (.mayCast .milledSpell .causingSpell .withoutPaying) =>
    "exile and copy a card"
  | .«if» .opponentsMilled (.queueReflexive (.mayCast .milledSpell .causingSpell .withoutPaying)) =>
    "when one or more cards are milled this way, exile and copy a card"
  | .loseLife amount who =>
    match amount, who with
    | .fixed n, .you => s!"you lose {n} life"
    | .fixed n, .target .opponent => s!"{noun} loses {n} life"
    | .fixed n, .eachOpponent => s!"each opponent loses {n} life"
    | .perBurden, .you =>
      "you lose 1 life for each burden counter on this"
    | .attachedEquipment, .eachOpponent =>
      "each opponent loses X life, where X is the number of Equipment attached to it"
    | _, _ =>
      "lose life"
  | .«if» .planWasSacrificed (.queueReflexive (.dealDamage (.fixed n) .target .divided)) =>
    s!"when you do, it deals {n} damage divided as you choose among one or two targets"
  | .queueReflexive (.dealDamage (.fixed n) .target .divided) =>
    s!"when you do, it deals {n} damage divided as you choose among one or two targets"
  | .«if» .planWasSacrificed (.queueReflexive _) =>
    "when you do, the reflexive ability triggers"
  | .«if» (.atLeast (.count (.othersOfSubtype .hero)) (.fixed 1)) (.gainLife (.fixed n)) =>
    s!"if you control another Hero, you gain {n} life"
  | .grantPlayNotedUntilNextTurn =>
    playThatCardUntilNextTurnPhrase
  | .tap (.target .ifPresent) =>
    "tap up to one target creature"
  | .tap .target =>
    s!"tap {noun}"
  | .tap _ =>
    "tap it"
  | .untap who =>
    match who with
    | .attackingCreatures => "untap all attacking creatures"
    | .target => s!"untap {affectedNoun .target noun}"
    | .source => s!"untap {affectedNoun .source noun}"
    | .enchanted => s!"untap {affectedNoun .enchanted noun}"
    | .target .whileSource => s!"untap {affectedNoun .targetWhileSource noun}"
    | .equipped => "untap equipped creature"
    | .firstThisTurn => "untap it"
    | _ => "untap it"
  | .«if» (.atLeast (.count (.target .creature)) (.fixed 1)) (.putCounters (.ofKind .plusOnePlusOne) .permanent) =>
    "put a +1/+1 counter on it if it's a creature"
  | .«if» (.atLeast (.count (.target .planeswalker)) (.fixed 1)) (.putCounters (.ofKind .loyalty) .permanent) =>
    "put a loyalty counter on it if it's a planeswalker"
  | .winTheGame =>
    "you win the game"
  | .«if» (.not (.atLeast .libraryCards (.fixed 1))) .winTheGame =>
    "if your library has no cards in it, you win the game"
  | .shuffleSource =>
    "its owner shuffles it into their library"
  | .«if» (.atLeast .libraryCards (.fixed 1)) .shuffleSource =>
    "Fblthp's owner shuffles him into their library"
  | .armSurveilReturnLifeGained =>
    "if you gained life this turn"
  | .becomeCopy .artifactEnchantmentOrLand =>
    "until your next turn, this becomes a copy of up to one target artifact, non-Aura enchantment, or land, except its name, and it's a legendary 4/4 Human Villain creature with vigilance"
  | .becomeCopy .creatureOrGraveyardCard =>
    "until your next turn, this becomes a copy of up to one target creature or creature card in a graveyard, except its name, and it's a legendary Human Mercenary Villain creature"
  | .becomeCopy .noted =>
    "enchanted creature becomes a copy of that creature until this Aura leaves the battlefield"
  | .becomeCopy (.cause none) =>
    "create a token that's a copy of the artifact that caused this"
  | .becomeCopy _ =>
    "become a copy"
  | .«if» (.atLeast (.count .harnessedSource) (.fixed 1)) (.exile .target .returnImmediately) =>
    "exile up to one other target nonland permanent you control, then return that card to the battlefield under its owner's control"
  | .retargetCause =>
    "choose new targets for that spell"
  | .copyCause =>
    "copy that spell. You may choose new targets for the copy"
  | .may (.exile .discarded .playUntilNextTurn) (.sequence []) .ifYouDo =>
    "you may exile that card from your graveyard. If you do, until the end of your next turn, you may play that card"
  | .may (.mill (.fixed n) .you .none) (.sequence []) .ifYouDo =>
    if n == 1 then "you may mill a card" else s!"you may mill {n} cards"
  | .may (.createTokens _ (.fixed 1) false _ _) (.sequence []) .ifYouDo =>
    "you may create a 0/4 colorless Wall creature token with defender"
  | .may (.pay cost) _ .ifYouDo =>
    if cost.items.any (fun | .sacrifice _ _ => true | _ => false) then
      "you may sacrifice that. If you do, do that"
    else if cost.items.any (fun | .discard _ _ => true | _ => false) then
      "you may discard that. If you do, do that"
    else
      "you may do it. If you do, do that"
  | .may _ _ .ifYouDo =>
    "you may do it. If you do, do that"
  | .pay cost =>
    if cost.isManaOnly && !cost.isEmpty then
      s!"pay {cost.manaCost}"
    else
      "pay that cost"
  | .queueReflexive _ =>
    "when you do, that ability triggers"
  | .«if» .manaSpent (.discard (.cards n)) =>
    s!"discard {cardPhrase n}"
  | .«if» _ _ =>
    "if that is true"
  | .ifElse _ _ _ =>
    "if that is true"
  | .or _ =>
    "choose one"
  | r =>
    SpellResolution.toPhrase r noun

/-- Sentence whose printed “When/Whenever …” lead-in differs from the generic
`eventPrefix` (a card name, an ability word, or a more specific subject) but
whose effect clause is the shared `resolutionPhrase`. -/
def leadInSentence (ab : TriggeredAbility) (lead : String) : String :=
  s!"{lead}, {resolutionPhrase ab.effect}."

/-- Printed clause when the effect is a sequence of independent steps.
Numbers and the target noun come from the effect, so Oracle refill stays
in step with the printed line. -/
def sequenceClause (e : Effect) : Option String :=
  let noun := e.targetSpec.noun
  match e.resolution with
  | .sequence [.draw 1, .loseLife 1] =>
    some "you draw a card and lose 1 life"
  | .sequence [.draw (.fixed n), .discard (.cards 1)] =>
    some s!"draw {cardPhrase n.toNat}, then discard a card"
  | .sequence [.onSource (.pump p 0), .teamGain k] =>
    if k == #[Keyword.trample] then
      some s!"until end of turn, this creature gets {signedStat p}/+0 and creatures you control gain trample"
    else none
  | .sequence [.onPermanent (.plusOne n), .onPermanent (.grantKeywords k)] =>
    if k == #[Keyword.lifelink] && n == 1 then
      some s!"put a +1/+1 counter on {noun}. It gains lifelink until end of turn"
    else if k == #[Keyword.vigilance] then
      some s!"put {plusOnePlusOneCountersPhrase n} on {noun}. It gains vigilance until end of turn"
    else none
  | .sequence [.onSource (.pump 1 0), .onSource .cantBeBlocked] =>
    some "this gets +1/+0 until end of turn and can't be blocked this turn"
  | .sequence [.draw 1, .onSource (.plusOne 1)] =>
    some "draw a card and put a +1/+1 counter on this"
  | .sequence [.creaturesYouControlPump p 0, .teamGain k] =>
    if k == #[Keyword.firstStrike] then
      some s!"creatures you control get {signedStat p}/+0 and gain first strike until end of turn"
    else none
  | .sequence [.onSource (.plusOne 1), .draw 1] =>
    some "put a +1/+1 counter on this and draw a card"
  | .sequence [.onSource (.pump p t), .damageEachOpponent n] =>
    some s!"this gets {signedStat p}/{signedStat t} until end of turn and deals {n} damage to each opponent"
  | .sequence
      [.onPermanent .untap,
       .«if» (.subtype subtype) (.onPermanent (.plusOne n))] =>
    some s!"untap {noun}. If that creature is a {subtype}, put {plusOnePlusOneCountersPhrase n} on it"
  | .sequence [.loseLife (.fixed n) .you, .createTokens _ 1 false _ _] =>
    some s!"you lose {n} life and create a Treasure token"
  | .sequence [.exileCardFromGraveyard, .loseLife (.fixed n) .eachOpponent] =>
    some s!"exile up to one {noun}. Each opponent loses {n} life"
  | _ => none

/-- Printed sentence for a leftover dies trigger. Its resolution is a
`TriggerResolution` that does not carry `DeathLeftover`. -/
def deathSentence : DeathLeftover → String
  | .hellcatReturn =>
    "When Hellcat dies, return her to the battlefield under her owner's control with a +1/+1 counter on her. She loses all abilities and gains haste."
  | .villainReturnAsHero =>
    "Whenever a Villain you control dies, return it to the battlefield under its owner's control with a finality counter on it. That creature is a Hero in addition to its other types."
  | .attackingReturnHand =>
    "Whenever an attacking creature you control dies, return that card to its owner's hand."
  | .deathtouchOppSac =>
    "Whenever another creature you control with deathtouch dies, each opponent sacrifices a nontoken creature of their choice."

/-- Printed sentence for a leftover “enters or attacks” trigger.
Its resolution is a `TriggerResolution` that does not carry
`EnterOrAttackLeftover`. -/
def enterOrAttackSentence : EnterOrAttackLeftover → String
  | .copyKeywords =>
    "Whenever Super-Adaptoid enters or attacks, choose another target creature. If that creature has haste and Super-Adaptoid doesn't, put a haste counter on Super-Adaptoid. Do the same for flying, first strike, double strike, deathtouch, indestructible, lifelink, menace, reach, trample, and vigilance."
  | .createSquirrel =>
    "Do You Like Squirrels? — Whenever The Unbeatable Squirrel Girl enters or attacks, create a 1/1 green Squirrel creature token."

/-- Printed sentence for a leftover “whenever this attacks” trigger.
Its resolution is a `TriggerResolution` that does not carry
`ThisAttackLeftover`. -/
def thisAttackSentence : ThisAttackLeftover → String
  | .mayPayPlusOne =>
    "Whenever Ant-Man attacks, you may pay {1}. When you do, put a +1/+1 counter on target creature."
  | .payReturnAttacking =>
    "Whenever Grim Reaper attacks, you may pay {3}{B}. When you do, return target creature card from your graveyard to the battlefield tapped and attacking with a finality counter on it."
  | .ifArtifactEnteredDraw =>
    "Whenever Iron Man attacks, if an artifact entered the battlefield under your control this turn, draw a card."
  | .blinkNontoken =>
    "Whenever The Mighty Thor attacks, exile up to one target nontoken artifact or creature, then return that card to the battlefield tapped under its owner's control."
  | .equippedDrain =>
    "Whenever Whiplash attacks, if he's equipped, each opponent loses X life and you gain X life, where X is the number of Equipment attached to him."
  | .drawIfPower4 =>
    "Cybernetic Senses — Whenever Viv Vision attacks, draw a card if her power is 4 or greater."
  | .attacksAlonePlus2Indestructible =>
    "Unbreakable Skin — Whenever Luke Cage attacks alone, he gets +2/+0 and gains indestructible until end of turn."

/-- Printed sentence for a leftover “whenever you attack” trigger.
Its resolution is a `TriggerResolution` that does not carry
`YouAttackLeftover`. -/
def youAttackingSentence : YouAttackLeftover → String
  | .pay2LifeToughness =>
    "Whenever you attack, you may pay 2 life. If you do, until end of turn, creatures you control with toughness greater than their power assign combat damage equal to their toughness rather than their power."
  | .exileTopHeroPump =>
    "Whenever you attack, you may exile the top card of your library. If that card is a Hero card, Daredevil gets +2/+1 until end of turn. You may play that card this turn."
  | .lookSixCast =>
    s!"Whenever you attack, look at the top six cards of your library. You may cast a spell from among them with mana value less than or equal to the greatest power among attacking creatures you control without paying its mana cost. {restOnBottomRandomPhrase}."

/-- Printed sentence for a leftover draw, discard, life, or +1/+1-counter
trigger. Its resolution is a `TriggerResolution` that does not carry
`ResourceLeftover`. -/
def resourceSentence : ResourceLeftover → String
  | .discardExilePlay =>
    "Whenever you discard a card, you may exile that card from your graveyard. If you do, until the end of your next turn, you may play that card."
  | .drawIfAnotherHeroDamage =>
    "Whenever you draw a card, if you control another Hero, Human Torch deals 1 damage to target opponent."
  | .secondDrawBecome66 =>
    "Whenever you draw your second card each turn, until end of turn, Moon Girl and Devil Dinosaur's base power and toughness become 6/6 and they gain trample."
  | .secondDrawPlusOneTarget =>
    "Whenever you draw your second card each turn, put a +1/+1 counter on target creature."
  | .secondDrawDrain =>
    "Whenever you draw your second card each turn, each opponent loses 1 life and you gain 1 life."
  | .gainLifePlusOnes =>
    "Whenever you gain life, choose up to that many target creatures you control. Put a +1/+1 counter on each of them."
  | .plusOneCreateInsectOnce =>
    "Whenever you put a +1/+1 counter on a creature, create a 1/1 green Insect creature token. This ability triggers only once each turn."
  | .plusOneOnThisOnce =>
    "Whenever you put a +1/+1 counter on another creature, put a +1/+1 counter on this creature. This ability triggers only once each turn."
  | .plusOneOnHeroesCreateWall =>
    "Whenever you put one or more +1/+1 counters on one or more other Heroes you control, you may create a 0/4 colorless Wall creature token with defender."

/-- Printed sentence for a leftover “whenever you cast …” trigger.
Its resolution is a `TriggerResolution` that does not carry `CastLeftover`. -/
def castingSentence : CastLeftover → String
  | .villainToken =>
    "Whenever you cast a Villain spell, create a 2/1 black Villain creature token with menace."
  | .merfolkFromBlue =>
    "Whenever you cast a noncreature spell with one or more blue mana symbols in its mana cost, create that many 1/1 blue Merfolk creature tokens."
  | .mayPayHasteUnblockable =>
    "Whenever you cast a noncreature spell, you may pay {1}. When you do, target creature with haste can't be blocked this turn except by creatures with haste."
  | .plusOneEachOther =>
    "Whenever you cast a noncreature spell, put a +1/+1 counter on each other creature you control."
  | .exileFlicker =>
    "Whenever you cast a noncreature spell, exile another target nonland, nontoken permanent. Return that card to the battlefield under its owner's control at the beginning of the next end step."
  | .visionModes =>
    "Whenever you cast a noncreature spell, choose one that hasn't been chosen this turn — • Solar Beam — The Vision gains double strike until end of turn. • Density Control — The Vision gains indestructible until end of turn. • Technopathy — Draw a card."
  | .damageEqualMv =>
    "Whenever you cast a noncreature spell, Thor deals damage equal to that spell's mana value to any target."
  | .drawPowerEqualHand =>
    "Whenever you cast a spell that targets a creature you control, draw a card. Until end of turn, Ms. Marvel gains \"Ms. Marvel's base power is equal to the number of cards in your hand.\""
  | .plusOneThis =>
    "Whenever you cast a spell that targets a creature you control, put a +1/+1 counter on Mockingbird."
  | .plusOneScry =>
    "Whenever you cast a spell that targets a creature you control, put a +1/+1 counter on Colleen Wing. Scry 1."
  | .ironFistTap =>
    "Whenever you cast a spell that targets a creature you control, Iron Fist gains \"{T}: Iron Fist deals damage equal to his power to any other target\" until end of turn."
  | .targetsGainFlying =>
    "Whenever you cast a spell that targets one or more creatures, those creatures gain flying until end of turn."
  | .copyIfArtifactOrLand =>
    "Whenever you cast an instant or sorcery spell that targets an artifact or land, copy that spell. You may choose new targets for the copy. Put two +1/+1 counters on Fin Fang Foom."
  | .tapCreatureOrLand =>
    "Seismic Takedown — Whenever you cast a noncreature spell, tap target creature or land."

/-- Printed sentence for a leftover watch trigger. Its resolution is a
`TriggerResolution` that does not carry `WatchLeftover`. -/
def watchSentence : WatchLeftover → String
  | .combatDamageExileUntilNonland =>
    "Whenever Black Widow deals combat damage to a player, that player exiles cards from the top of their library until they exile a nonland card. You may put a +1/+1 counter on Black Widow. If you don't, you may cast the exiled nonland card until end of turn and mana of any type can be spent to cast that spell."
  | .attacksAloneDrain =>
    "Whenever a creature you control attacks alone, target opponent loses 1 life and you gain 1 life."
  | .attacksAloneFirstStrikeMenace =>
    "Whenever a creature you control attacks alone, it gains first strike and menace until end of turn."
  | .firstTapUntap =>
    "Whenever a creature you control becomes tapped during your turn, if it's the first time that creature has become tapped this turn, untap it."
  | .sheHulkRedirectOnce =>
    "Whenever a creature you control is dealt damage, you may have The Sensational She-Hulk deal that much damage to any target. Do this only once each turn."
  | .speedballTargeted =>
    "Whenever a player casts a spell that targets Speedball, he gets +2/+2 until end of turn. You may choose new targets for that spell."
  | .anyPlayerSecondDraw =>
    "Whenever a player draws their second card each turn, you draw a card."
  | .youTargetDrawOnce =>
    "Whenever a player or permanent becomes the target of an ability you control, draw a card. This ability triggers only once each turn."
  | .villainOrArtifactDamage =>
    "Whenever another Villain and/or artifact you control enters, this creature deals 1 damage to target opponent."
  | .villainConniveOnce =>
    "Whenever another Villain you control enters, you may have it connive. Do this only once each turn."
  | .villainPlusOneDamageOnce =>
    "Whenever another Villain you control enters, put a +1/+1 counter on Crossbones. He deals 2 damage to each opponent. This ability triggers only once each turn."
  | .villainAttachEquipment =>
    "Whenever another Villain you control enters, attach up to one target Equipment you control to target creature you control."
  | .villainPlusOneLifelink =>
    "Whenever another Villain you control enters, Yellowjacket gets +1/+0 and gains lifelink until end of turn."
  | .hulklingCompare =>
    "Whenever another creature you control enters, if it has greater power or toughness than Hulkling, put a +1/+1 counter on Hulkling."
  | .justiceBounce =>
    "Whenever another nonland permanent you control is returned to its owner's hand, put a +1/+1 counter on Justice."
  | .nontokenHeroModal =>
    "Whenever another nontoken Hero you control enters, choose one — • Create a 1/1 white Soldier creature token. • Creatures you control get +1/+1 until end of turn."
  | .ultronCopy =>
    "Whenever another nontoken artifact you control enters, you may pay {2}. If you do, create a token that's a copy of it. If the token isn't a creature, it becomes a 2/2 Robot Villain creature in addition to its other types."
  | .enchantedAttachEquipment =>
    "Whenever enchanted creature attacks or blocks, attach any number of target Equipment you control to it."
  | .equippedAttacksAloneUntapScry =>
    "Whenever equipped creature attacks alone, untap it and scry 1."
  | .equippedAttacksTap =>
    "Whenever equipped creature attacks, tap target creature defending player controls."
  | .equippedTappedDamage =>
    "Whenever equipped creature becomes tapped, it deals 1 damage to each opponent."
  | .heroesDamagePlusTwo =>
    "Whenever one or more Heroes you control deal damage to a player, put two +1/+1 counters on The Thing."
  | .merfolkAttackDraw =>
    "Whenever one or more Merfolk you control attack a player, draw a card."
  | .tokensEnterMayDraw =>
    "Whenever one or more tokens you control enter, you may draw a card."
  | .hawkeyeModes =>
    "Trick Arrows — Whenever Hawkeye becomes tapped, you may pay {1} up to three times. When you do, choose up to that many — • Net — Target creature can't block this turn. • Explosive — Hawkeye deals 2 damage to target player. • Boomerang — Discard a card, then draw a card."
  | .redHulk =>
    "Enrage — Whenever Red Hulk is dealt damage, put a +1/+1 counter on him. When you do, he deals damage equal to the number of +1/+1 counters on him to any other target."
  | .hulk =>
    "Enrage — Whenever The Incredible Hulk is dealt damage, put a +1/+1 counter on him. If he's attacking, untap him and there is an additional combat phase after this phase."

/-- Printed sentence for a leftover step trigger. Its resolution is a
`TriggerResolution` that does not carry `StepLeftover`. -/
def stepSentence : StepLeftover → String
  | .enchantedControllerDraws =>
    "At the beginning of the upkeep of enchanted creature's controller, that player draws a card."
  | .drawToTen =>
    "At the beginning of your end step, if you have fewer than ten cards in hand, draw cards equal to the difference."
  | .copyAbsorbingMan =>
    "At the beginning of your first main phase, until your next turn, Absorbing Man becomes a copy of up to one target artifact, non-Aura enchantment, or land, except his name is Absorbing Man, he's a legendary 4/4 Human Villain creature in addition to his other types, and he has vigilance."
  | .hydeChoose =>
    "At the beginning of your upkeep, choose one — • Put a +1/+1 counter on Mister Hyde. • Remove a counter from a creature you control. If you do, draw a card."
  | .copyTaskmaster =>
    "Photographic Reflexes — At the beginning of your first main phase, until your next turn, Taskmaster becomes a copy of up to one target creature on the battlefield or creature card in a graveyard, except his name is Taskmaster, Mercenary Mimic and he's a legendary Human Mercenary Villain creature."
  | .harnessedFlicker =>
    "∞ — At the beginning of your end step, exile up to one other target nonland permanent you control, then return that card to the battlefield under its owner's control."

def toNotation (ab : TriggeredAbility) : String :=
  if ab.isSagaChapter then
    s!"When a lore counter is put on this Saga, {ab.effect.phrase}."
  else if ab.isManaSpentCastScry then
    let n := match ab.effect.resolution with | .scry (.fixed k) => k.toNat | _ => 1
    s!"When that mana is spent to cast a creature spell that shares a creature type with your commander, scry {n}."
  else if !ab.modes.isEmpty then
    if !ab.effect.phrase.isEmpty && ab.effect.phrase.contains '•' then
      ab.effect.phrase
    else
      let modeTexts := ab.modes.toList.map fun m =>
        let txt := if !m.phrase.isEmpty then m.phrase else capitalizeAscii (resolutionPhrase m)
        let txt := if txt.endsWith "." then txt else s!"{txt}."
        s!"• {txt}"
      let hdr := if !ab.effect.phrase.isEmpty then ab.effect.phrase else "choose one"
      let once := if ab.onceEachTurn then " This ability triggers only once each turn." else ""
      s!"{eventPrefix ab}{interveningClause ab}, {hdr} — {" ".intercalate modeTexts}{once}"
  else if !ab.effect.phrase.isEmpty then
    ab.effect.phrase
  else
    let p := ab.pattern
    match ab.effect.asTrigger? with
    | some .bolgMaySacrifice =>
      leadInSentence ab "When Bolg enters"
    | some .createTreasuresEqualDamagedPlayerArtifacts =>
      leadInSentence ab "Whenever this creature deals combat damage to a player"
    | some .deal1ThenAmassOrcs =>
      "When this creature enters and whenever an opponent draws a card except the first one they draw in each of their draw steps, this creature deals 1 damage to any target. Then amass Orcs 1."
    | some (.createTokens k n) =>
      if p == .stepEachUpkeep then
        s!"At the beginning of each player's upkeep, you {TokenSpec.createPhrase k n}."
      else if p == .drawCard .opponent && ab.limit == .nthEachTurn 2 && n == 1 then
        "Whenever an opponent draws their second card each turn, you create a Treasure token."
      else if p == .damageDealt (.all #[.hasSubtype (.literal .dwarf), .controlledBy .you])
          (.playerOrObject .any { zones := .battlefield, pred := .hasType .battle }) (combatOnly := true) && n == 2 then
        leadInSentence ab "Whenever a Dwarf you control deals combat damage to a player or battle"
      else
        let once := if ab.onceEachTurn then " This ability triggers only once each turn." else ""
        let clause := (sequenceClause ab.effect).getD (resolutionPhrase ab.effect)
        s!"{eventPrefix ab}{interveningClause ab}, {clause}.{once}"
    | some (.draw 1) =>
      if p == .stepEachOpponentDrawStep then
        "At the beginning of each opponent's draw step, you draw a card."
      else
        let once := if ab.onceEachTurn then " This ability triggers only once each turn." else ""
        let clause := (sequenceClause ab.effect).getD (resolutionPhrase ab.effect)
        s!"{eventPrefix ab}{interveningClause ab}, {clause}.{once}"
    | some .loyaltyOnSource =>
      if p == .gainLife .you then
        "Whenever you gain life, put a loyalty counter on Ajani."
      else
        let once := if ab.onceEachTurn then " This ability triggers only once each turn." else ""
        s!"{eventPrefix ab}{interveningClause ab}, {resolutionPhrase ab.effect}.{once}"
    | some (.untapAttackersExtraCombat n) =>
      leadInSentence ab
        s!"Whenever you attack with creatures with total power {n} or greater for the first time each turn"
    | some .allianceMode =>
      leadInSentence ab "Alliance — Whenever another creature you control enters"
    | some .destroyOtherAmassControllerPower =>
      "When Azog enters, destroy up to one other target creature. Its controller amasses Goblins X, where X is that creature's power. If you controlled that creature, draw a card."
    | some (.damageEachOpponent 3) =>
      if p == .youCastColor .red then
        "Whenever you cast a red spell, Aragorn deals 3 damage to target opponent."
      else
        let once := if ab.onceEachTurn then " This ability triggers only once each turn." else ""
        s!"{eventPrefix ab}{interveningClause ab}, {resolutionPhrase ab.effect}.{once}"
    | some .returnCreatureFromGyToHand =>
      if p == .thisEnters then
        "When this enchantment enters, return target creature card from your graveyard to your hand."
      else
        s!"{eventPrefix ab}{interveningClause ab}, {resolutionPhrase ab.effect}."
    | some .discardHandDrawDamageIfStory =>
      "Whenever Balin or another Dwarf you control enters, you may discard your hand. Draw X cards, where X is the number of cards discarded this way. If you have an enduring story, Balin deals X damage to each opponent."
    | some .castFromGyArtifactInstantSorcery =>
      leadInSentence ab "Whenever Bilbo attacks"
    | some (.createAxe true) =>
      leadInSentence ab "When Dáin enters"
    | some .equippedAttackersGainDoubleStrike =>
      leadInSentence ab "Whenever Dáin attacks"
    | some .tapEnchantedRemoveCounters =>
      leadInSentence ab "When this Aura enters"
    | some (.revealTopPutRandomCreature _) =>
      leadInSentence ab "When this artifact is put into a graveyard from the battlefield"
    | some .beginCombatIfDrawnTwoPump =>
      "At the beginning of combat on your turn, if you've drawn two or more cards this turn, another target creature you control gets +3/+0 and gains first strike until end of turn."
    | some .honePerOppAttach =>
      "When Sting enters, put a hone counter on Sting for each creature target opponent controls. Attach Sting to up to one target creature you control."
    | some .copySelfNonlegendary =>
      leadInSentence ab "When The Notary Hobbits enter"
    | some .attachEquipmentThenFight =>
      leadInSentence ab "When Thorin enters"
    | some .returnAsArtifact =>
      leadInSentence ab "When Tom, Bert, and William die"
    | some .exileLandsThenReturnTapped =>
      leadInSentence ab "When Gandalf enters"
    | some .grimaImpulse =>
      leadInSentence ab "Whenever Gríma deals combat damage to a player"
    | some .palantir =>
      "At the beginning of your end step, put an influence counter on Palantír of Orthanc and scry 2. Then target opponent may have you draw a card. If that player doesn't, you mill X cards, where X is the number of influence counters on Palantír of Orthanc, and that player loses life equal to the total mana value of those cards."
    | some .treasuresEqualLastKnown =>
      if p == .thisDealtNoncombatDamage then
        leadInSentence ab "Whenever Smaug is dealt noncombat damage"
      else if p == .thisDealsCombatDamageToPlayerOrPlaneswalker then
        leadInSentence ab "Whenever this creature deals combat damage to a player or planeswalker"
      else
        s!"{eventPrefix ab}{interveningClause ab}, {resolutionPhrase ab.effect}."
    | some .protectionEverything =>
      leadInSentence ab "When The One Ring enters"
    | some .loseLifePerBurden =>
      "At the beginning of your upkeep, you lose 1 life for each burden counter on The One Ring."
    | some .payReturnFromGy =>
      if p == .landYouControlEnters then
        leadInSentence ab "Landfall — Whenever a land you control enters"
      else
        s!"{eventPrefix ab}{interveningClause ab}, {resolutionPhrase ab.effect}."
    | some (.damageTargetOpponent 2) =>
      if p == .youPutCountersOnGoblinOrcArmy then
        "Whenever you put one or more counters on a Goblin, Orc, or Army you control, The Great Goblin deals 2 damage to target opponent."
      else
        let once := if ab.onceEachTurn then " This ability triggers only once each turn." else ""
        s!"{eventPrefix ab}{interveningClause ab}, {resolutionPhrase ab.effect}.{once}"
    | some (.connive .source) =>
      if p == .thisEnters then
        leadInSentence ab "When this creature enters"
      else
        match p with
        | .castSpell { relation := .you, pred := .any } (.hasColor (.literal color))
            (some .hand) .. =>
          s!"Whenever you cast a {color} spell from your hand, this connives."
        | _ =>
          let once := if ab.onceEachTurn then " This ability triggers only once each turn." else ""
          s!"{eventPrefix ab}{interveningClause ab}, {resolutionPhrase ab.effect}.{once}"
    | some (.drawIfAttackedOrEnteredSubtype subtype) =>
      let a := if subtype == .hero then "a Hero" else s!"a {subtype}"
      s!"At the beginning of each end step, if you attacked with {a} this turn or {a} entered the battlefield under your control this turn, draw a card."
    | some (.othersOfSubtypeGetEqualSourceToughness subtype) =>
      s!"Whenever this attacks, each other {subtype} you control gets +X/+X until end of turn, where X is this toughness."
    | some (.onSource (.plusOne n)) =>
      if n == 2 && p == .anotherSubtypeYouControlEnters .wolf then
        "Whenever another Wolf you control enters, put two +1/+1 counters on Chief of the Wilds."
      else if n == 1 && p == .thisDealtDamage then
        "Whenever this is dealt damage, put a +1/+1 counter on it."
      else
        let once := if ab.onceEachTurn then " This ability triggers only once each turn." else ""
        s!"{eventPrefix ab}{interveningClause ab}, {resolutionPhrase ab.effect}.{once}"
    | some (.attachTo .creatureYouControl) =>
      if p == .thisEnters then leadInSentence ab "When this Equipment enters"
      else s!"{eventPrefix ab}{interveningClause ab}, {resolutionPhrase ab.effect}."
    | some (.surveil n) =>
      if p == .thisEnters then s!"When this permanent enters, surveil {n}."
      else s!"{eventPrefix ab}{interveningClause ab}, {resolutionPhrase ab.effect}."
    | some (.onEnchanted _) =>
      if p == .thisEnters then leadInSentence ab "When this Aura enters"
      else s!"{eventPrefix ab}{interveningClause ab}, {resolutionPhrase ab.effect}."
    | some (.attachThen _) =>
      if p == .thisEnters then leadInSentence ab "When this Equipment enters"
      else s!"{eventPrefix ab}{interveningClause ab}, {resolutionPhrase ab.effect}."
    | some .exileOtherCopyEnchanted =>
      if p == .thisEnters then leadInSentence ab "When this Aura enters"
      else s!"{eventPrefix ab}{interveningClause ab}, {resolutionPhrase ab.effect}."
    | some .exileUntilNextEndStep =>
      if p == .thisEnters then leadInSentence ab "When this Vehicle enters"
      else s!"{eventPrefix ab}{interveningClause ab}, {resolutionPhrase ab.effect}."
    | some .tapOrUntapNonland =>
      if p == .thisEnters then leadInSentence ab "When this creature enters"
      else s!"{eventPrefix ab}{interveningClause ab}, {resolutionPhrase ab.effect}."
    | some .createFoodOrTreasure =>
      if p == .thisEnters then leadInSentence ab "When this creature enters"
      else s!"{eventPrefix ab}{interveningClause ab}, {resolutionPhrase ab.effect}."
    | some .villainIfGyElseMill =>
      if p == .thisEnters then leadInSentence ab "When this creature enters"
      else s!"{eventPrefix ab}{interveningClause ab}, {resolutionPhrase ab.effect}."
    | some .drawMayPutLandTapped =>
      if p == .thisEnters then leadInSentence ab "When this creature enters"
      else s!"{eventPrefix ab}{interveningClause ab}, {resolutionPhrase ab.effect}."
    | some .drawGainLifeIfAnotherHero =>
      if p == .thisEnters then leadInSentence ab "When this creature enters"
      else s!"{eventPrefix ab}{interveningClause ab}, {resolutionPhrase ab.effect}."
    | some .plusOneOrTwoIfAnotherHero =>
      if p == .thisEnters then leadInSentence ab "When this creature enters"
      else s!"{eventPrefix ab}{interveningClause ab}, {resolutionPhrase ab.effect}."
    | some .maySacArtifactOrDiscardDraw =>
      if p == .thisEnters then leadInSentence ab "When this creature enters"
      else s!"{eventPrefix ab}{interveningClause ab}, {resolutionPhrase ab.effect}."
    | some (.exileUntilLeaves .oppTappedCreature) =>
      if p == .thisEnters then
        "When this enchantment enters, exile target tapped creature an opponent controls until this enchantment leaves the battlefield."
      else s!"{eventPrefix ab}{interveningClause ab}, {resolutionPhrase ab.effect}."
    | some (.opponentDiscards n .target) =>
      if p == .thisEnters then
        let cards := if n == 2 then "two cards" else cardPhrase n
        s!"When this enchantment enters, target opponent discards {cards}."
      else s!"{eventPrefix ab}{interveningClause ab}, {resolutionPhrase ab.effect}."
    | some (.enter (.dealDamageUpToOne n)) =>
      if p == .thisEnters then
        s!"When this permanent enters, it deals {n} damage to up to one target creature."
      else s!"{eventPrefix ab}{interveningClause ab}, {resolutionPhrase ab.effect}."
    | some (.step e) => stepSentence e
    | some (.death e) => deathSentence e
    | some (.thisAttack e) => thisAttackSentence e
    | some (.enterOrAttack e) => enterOrAttackSentence e
    | some (.watch e) => watchSentence e
    | some (.youAttacking e) => youAttackingSentence e
    | some (.casting e) => castingSentence e
    | some (.resource e) => resourceSentence e
    | _ =>
      if p == .equippedAttacksAlone then
        "Whenever equipped creature attacks alone, you draw a card and you lose 1 life."
      else if p == .landYouControlEnters &&
          ab.effect.resolution == .sequence [.draw 1, .onSource (.plusOne 1)] then
        "Landfall — Whenever a land you control enters, draw a card and put a +1/+1 counter on Gandalf."
      else if p == .permanentEnters (.all #[
            .otherThan .this, .hasSupertype .legendary,
            .hasSubtype (.literal .elf), .controlledBy .you]) &&
          ab.effect.resolution == .sequence [.draw (.fixed 2), .discard (.cards 1)] then
        "Whenever another legendary Elf you control enters, draw two cards, then discard a card."
      else
        let once :=
          if ab.onceEachTurn then " This ability triggers only once each turn."
          else if ab.optionalOnceEachTurn then " Do this only once each turn."
          else ""
        let clause := (sequenceClause ab.effect).getD (resolutionPhrase ab.effect)
        let inter :=
          if (clause.map Char.toLower).startsWith "if " then ""
          else interveningClause ab
        s!"{eventPrefix ab}{inter}, {clause}.{once}"

instance : ToString TriggeredAbility where
  toString := toNotation

instance : ToOracle TriggeredAbility where
  toOracle _ ab := toNotation ab

end TriggeredAbility

end Mtg.Engine
