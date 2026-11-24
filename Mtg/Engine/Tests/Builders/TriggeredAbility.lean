import Mtg.Engine.Card.TriggeredAbility
import Mtg.Engine.Tests.Builders.ChapterEffects
import Mtg.Engine.Tests.Builders.SpellEffects
import Mtg.Engine.Tests.Builders.TriggerEffects

/-!
# Test-only named `TriggeredAbility` builder table

Relocated out of the precompiled `Mtg.Engine.Card` library in Phase 12 so
`Card/` and `Game/` have zero dependency on named card/test builder tables.
-/

namespace Mtg.Engine

namespace TriggeredAbility

/-! ### Catalog constructors for reusable triggered abilities -/

def onEnterScry (n : Nat) : TriggeredAbility := mkTrigger .thisEnters (Effect.triggerScry n)
def onAttackScry (n : Nat) : TriggeredAbility := mkTrigger .thisAttacks (Effect.triggerScry n)
def onAttackWithElvesScry (n : Nat) : TriggeredAbility :=
  mkTrigger (.youAttackWithSubtype .elf) (Effect.triggerScry n) (grouping := .oncePerBatch)
def onOneOrMoreOtherCreaturesDieScry (n : Nat) : TriggeredAbility :=
  mkTrigger .otherCreaturesDie (Effect.triggerScry n) (grouping := .oncePerBatch)
def onCastColorScry (c : Color) (n : Nat) : TriggeredAbility :=
  mkTrigger (.youCastColor c) (Effect.triggerScry n)
def onEnterDraw (n : Nat) : TriggeredAbility := mkTrigger .thisEnters (Effect.triggerDraw n)
def onDiesDraw (n : Nat) : TriggeredAbility := mkTrigger .thisDies (Effect.triggerDraw n)
def onTheRingTemptsYouDraw (n : Nat) : TriggeredAbility :=
  mkTrigger .theRingTemptsYou (Effect.triggerDraw n)
def onChooseRingBearerDraw : TriggeredAbility :=
  mkTrigger .youChooseRingBearer (Effect.triggerDraw 1)
def onEnterCreateTokens (kind : TokenSpec) (n : Nat) (tapped : Bool := false) :
    TriggeredAbility :=
  mkTrigger .thisEnters (Effect.triggerCreateTokens kind n tapped)
def onCastColorCreateTokens (c : Color) (kind : TokenSpec) (n : Nat) :
    TriggeredAbility :=
  mkTrigger (.youCastColor c) (Effect.triggerCreateTokens kind n)
def onEnterOrAttackCreateWall : TriggeredAbility :=
  mkTrigger .enterOrAttack (Effect.triggerCreateTokens .wall 1)
def onEnterAmassGoblins (n : Nat) : TriggeredAbility :=
  mkTrigger .thisEnters (Effect.triggerAmass n .goblin)
def onEnterRecruit : TriggeredAbility := mkTrigger .thisEnters Effect.triggerRecruit
def onYouAttackRecruit : TriggeredAbility :=
  mkTrigger .youAttack Effect.triggerRecruit (grouping := .oncePerBatch)
def onEnterDealDividedDamage (amount maxTargets : Nat) : TriggeredAbility :=
  mkTrigger .thisEnters (Effect.triggerDividedDamage amount maxTargets)
def onEnterOrAttackDealDividedDamage (amount maxTargets : Nat) : TriggeredAbility :=
  mkTrigger .enterOrAttack (Effect.triggerDividedDamage amount maxTargets)
def onEnterOrAttackPlusOneOnCreature : TriggeredAbility :=
  mkTrigger .enterOrAttack { targets := .creature, body := Instruction.putPlusOne (.target 0) 1 }
def onLandYouControlEntersPlusOnePlusOne : TriggeredAbility :=
  mkTrigger .landYouControlEnters { targets := .creatureYouControl, body := Instruction.putPlusOne (.target 0) 1 }
def onCombatPlusOneOnCreatureYouControl : TriggeredAbility :=
  mkTrigger .stepYourBeginCombat { targets := .creatureYouControl, body := Instruction.putPlusOne (.target 0) 1 }
def onEnterAttachToLegendary : TriggeredAbility :=
  mkTrigger .thisEnters (Effect.triggerAttachTo .legendaryCreatureYouControl)
def onEnterAttachToCreatureYouControl : TriggeredAbility :=
  mkTrigger .thisEnters (Effect.triggerAttachTo .creatureYouControl)
def onEnterTargetOpponentSacrificesCreature : TriggeredAbility :=
  mkTrigger .thisEnters Effect.triggerOpponentSacrificesCreature
def onEnterTargetOpponentSacrifices : TriggeredAbility :=
  onEnterTargetOpponentSacrificesCreature
def onDrawSecondPlusOne : TriggeredAbility :=
  mkTrigger (.drawCard .you) { body := Instruction.putPlusOne .this 1 } (limit := .nthEachTurn 2)
/-- CR 603.4 intervening-if Ferocious trigger at beginning of combat (rechecked on resolution). -/
def onYourBeginCombatFerociousPlusOne : TriggeredAbility :=
  mkTrigger .stepYourBeginCombat { body := Instruction.putPlusOne .this 1 }
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
def onEnterConnive : TriggeredAbility := mkTrigger .thisEnters Effect.triggerConniveSource
def onCombatTargetYouControlConnives : TriggeredAbility :=
  mkTrigger .stepYourBeginCombat (Effect.triggerConniveTarget .creatureYouControl)
def onEnterExileOppNonlandUntilLeaves : TriggeredAbility :=
  mkTrigger .thisEnters (Effect.triggerExileUntilLeaves .oppNonland)
def onEnterExileOppTappedUntilLeaves : TriggeredAbility :=
  mkTrigger .thisEnters (Effect.triggerExileUntilLeaves .oppTappedCreature)
def onAttackMayExileDefenderUntilLeaves : TriggeredAbility :=
  mkTrigger .thisAttacks
    { targets := .defendingPlayerCreature
      body := Instruction.may .you none (Instruction.exile (.target 0) { exileUntilSourceLeaves := true }) }
/-- CR 603.2 `"while you control..."` attack trigger (checked at trigger time, not on resolution). -/
def onAttackFerociousGainLife (n : Nat) : TriggeredAbility :=
  mkTrigger (.whenCond .thisAttacks (condControlCreaturePowerAtLeast 4)) (Effect.triggerGainLife n)
def onDiesOppCreatureGets (power toughness : Int) : TriggeredAbility :=
  mkTrigger .thisDies { targets := .oppCreature, body := Instruction.pumpFixed (.target 0) power toughness }
def onCastColorPump (color : Color) (power toughness : Int) : TriggeredAbility :=
  mkTrigger (.youCastColor color) { targets := .creature, body := Instruction.pumpFixed (.target 0) power toughness }
def onLandYouControlEntersGets (power toughness : Int) : TriggeredAbility :=
  mkTrigger .landYouControlEnters { body := Instruction.pumpFixed .this power toughness }
def onAttackFerociousSourceGets (power toughness : Int) : TriggeredAbility :=
  mkTrigger (.whenCond .thisAttacks (condControlCreaturePowerAtLeast 4))
    { body := Instruction.pumpFixed .this power toughness }
def onAnotherElfYouControlEntersGets1 : TriggeredAbility :=
  mkTrigger (.anotherSubtypeYouControlEnters .elf) { body := Instruction.pumpFixed .this 1 1 }
def onArtifactYouControlEntersDrawOnce : TriggeredAbility :=
  mkTrigger .artifactYouControlEnters (Effect.triggerDraw 1) (limit := .onceEachTurn)
def onActivateCreatureAbilityDrawOnce : TriggeredAbility :=
  mkTrigger .youActivateCreatureAbility (Effect.triggerDraw 1) (limit := .onceEachTurn)
def onEachEndStepDrawIfGainedLife (n : Nat) : TriggeredAbility :=
  mkTrigger .stepEachEndStep (Effect.triggerDraw 1)
    (interveningIf? := some (.turnHistory (.eventOccurredThisTurn .you (.gainedLife n))))
def onThisOrAnotherSubtypeEntersCreateTokens (subtype : String) (kind : TokenSpec)
    (n : Nat) : TriggeredAbility :=
  mkTrigger (.thisOrAnotherSubtypeYouControlEnters (CardSubtype.ofOracleD subtype))
    (Effect.triggerCreateTokens kind n)
def onSubtypeYouControlCombatDamageCreateTokens (subtype : String) (kind : TokenSpec)
    (n : Nat) : TriggeredAbility :=
  let sub := CardSubtype.ofOracleD subtype
  mkTrigger
    (.damageDealt
      (.all #[.hasSubtype (.literal sub), .controlledBy .you])
      (.playerOrObject .any { zones := .battlefield, pred := .hasType .battle })
      (combatOnly := true))
    (Effect.triggerCreateTokens kind n)
def onOpponentCastsFirstNoncreatureRecruit : TriggeredAbility :=
  mkTrigger .opponentCastsFirstNoncreature Effect.triggerRecruit
def onCastColorDamageOpponent (color : Color) (n : Nat) : TriggeredAbility :=
  mkTrigger (.youCastColor color) (Effect.triggerDamageTargetOpponent n)
def onAttackOtherGets2AndTrample : TriggeredAbility :=
  mkTrigger .thisAttacks { targets := .anotherCreatureYouControl, body := Instruction.pumpAndTrample (.target 0) 2 0 }
def onEnterMayDiscardDraw (n : Nat) : TriggeredAbility :=
  mkTrigger .thisEnters (Effect.triggerMayDiscardDraw n)
def onCastInstantOrSorceryDealDamageToEachOpponent (amount : Nat) : TriggeredAbility :=
  mkTrigger .youCastInstantOrSorcery (Effect.triggerDamageEachOpponent amount)
def onEnterEachOpponentDiscards : TriggeredAbility :=
  mkTrigger .thisEnters (Effect.triggerEachOpponentDiscards 1)
def onEnterExileTop : TriggeredAbility := mkTrigger .thisEnters Effect.triggerExileTop
def onDrawSecondMillPlayer (n : Nat) : TriggeredAbility :=
  mkTrigger (.drawCard .you) (Effect.triggerMillPlayer n) (limit := .nthEachTurn 2)
def onOpponentCastsAmassOrcs (n : Nat) : TriggeredAbility :=
  mkTrigger .opponentCastsSpell (Effect.triggerAmass n .orc)
def onCreatureYouControlAttacksAloneInvestigate : TriggeredAbility :=
  mkTrigger .creatureYouControlAttacksAlone Effect.triggerInvestigate
def onEnterTargetOpponentDiscards (n : Nat) : TriggeredAbility :=
  mkTrigger .thisEnters (Effect.triggerTargetOpponentDiscards n)
def onEquipmentYouControlEntersDraw : TriggeredAbility :=
  mkTrigger .equipmentYouControlEnters (Effect.triggerDraw 1)
def onEnterSearchForest : TriggeredAbility := mkTrigger .thisEnters Effect.triggerSearchForest
def onEnterSearchBasicToHand : TriggeredAbility :=
  mkTrigger .thisEnters Effect.triggerSearchBasicLandToHand
def onEnterEachPlayerSacrificesCreature : TriggeredAbility :=
  mkTrigger .thisEnters Effect.triggerEachPlayerSacrificesCreature
def onEnterMayExileAnotherCreature : TriggeredAbility :=
  mkTrigger .thisEnters (Effect.triggerExileTarget .anotherCreature (allowsZeroTargets := true))
def onEnterReturnCreatureFromGyToHand : TriggeredAbility :=
  mkTrigger .thisEnters Effect.triggerReturnCreatureFromGyToHand
def onCombatDamageToPlayerLoot : TriggeredAbility :=
  mkTrigger .thisDealsCombatDamageToPlayer (Effect.seqDrawThenDiscard 1)
def onAttackFerociousPlusOneEach : TriggeredAbility :=
  mkTrigger (.whenCond .thisAttacks (condControlCreaturePowerAtLeast 4))
    Effect.triggerPlusOneEachYouControl
def onAttackFerociousSourceGetsAndTeamTrample (power : Int) : TriggeredAbility :=
  mkTrigger (.whenCond .thisAttacks (condControlCreaturePowerAtLeast 4))
    (Effect.seqSourceGetsAndTeamTrample power)
def onEnterOrAttackHoneEachEquipment : TriggeredAbility :=
  mkTrigger .enterOrAttack Effect.triggerHoneEachEquipment
def onEnterOrAttackPlusOneEachOtherGainLife : TriggeredAbility :=
  mkTrigger .enterOrAttack Effect.triggerPlusOneEachOtherGainLife
def onCastNoncreaturePumpAndDamageOpponents (n : Nat) : TriggeredAbility :=
  mkTrigger .youCastNoncreature (Effect.seqPumpAndDamageOpponents n)
def onDrawSecondPlusOneLifelink : TriggeredAbility :=
  mkTrigger (.drawCard .you) (Effect.seqPlusOneAndLifelink .creature) (limit := .nthEachTurn 2)
def onYouAttackPumpTargetPerPlains : TriggeredAbility :=
  mkTrigger .youAttack Effect.triggerPumpTargetPerPlains (grouping := .oncePerBatch)
def onAnotherLegendarySubtypeEntersLoot (subtype : String) : TriggeredAbility :=
  mkTrigger
    (.permanentEnters (.all #[
      .otherThan .this, .hasSupertype .legendary,
      .hasSubtype (.literal (CardSubtype.ofOracleD subtype)), .controlledBy .you]))
    (Effect.seqDrawThenDiscard 2)
def onRingTemptsMayDiscardDraw (n : Nat) : TriggeredAbility :=
  mkTrigger .theRingTemptsYou (Effect.triggerMayDiscardHandDraw n)
def onScryPumpSelfForEachLookedAt : TriggeredAbility :=
  mkTrigger .youScry Effect.triggerPumpByLookedAt
def onScryPumpAndUnblockableOnce : TriggeredAbility :=
  mkTrigger .youScry Effect.seqPumpAndUnblockable (limit := .onceEachTurn)
def onAttackPumpByGreatestPower : TriggeredAbility :=
  mkTrigger .thisAttacks Effect.triggerPumpGreatestPower
def onBecomesBlockedDeal1ToBlockers : TriggeredAbility :=
  mkTrigger .thisBecomesBlocked (Effect.triggerDamageBlockers 1)
def onAttackWithTwoOrMoreGrantFlying : TriggeredAbility :=
  mkTrigger .youAttackWithTwoOrMoreToPlayer
    { targets := .attackingCreatureWithoutFlying, body := Instruction.grantKeywords (.target 0) #[Keyword.flying] }
    (grouping := .perPlayerInBatch)
def onLeaveReturnExiled : TriggeredAbility := mkTrigger .thisLeaves Effect.triggerReturnLinkedExile
def onEnterCreateThenAttach (kind : TokenSpec) : TriggeredAbility :=
  mkTrigger .thisEnters (Effect.triggerCreateThenAttach kind)
def onEnterAmassThenAttach (n : Nat) : TriggeredAbility :=
  mkTrigger .thisEnters (Effect.triggerAmassThenAttach n .goblin)
def onEnterGainLifeSearchBasicOnTop (n : Nat) : TriggeredAbility :=
  mkTrigger .thisEnters (Effect.triggerGainLifeSearchBasicOnTop n)
def onYourFirstMainAddMana (types : Array ManaType) : TriggeredAbility :=
  mkTrigger .stepYourFirstMain (Effect.triggerAddMana types)
def onEnterCreateAxe : TriggeredAbility :=
  mkTrigger .thisEnters (Effect.triggerCreateAxe false)
def onLandYouControlEntersTapOrUntap : TriggeredAbility :=
  mkTrigger .landYouControlEnters Effect.triggerTapOppOrUntapYours
def onEnterCreateAxeAttach : TriggeredAbility :=
  mkTrigger .thisEnters (Effect.triggerCreateAxe true)
def onDiesAmassGoblinsEqualPower : TriggeredAbility :=
  mkTrigger .thisDies (Effect.triggerAmassSourcePower .goblin)
def onLandYouControlEntersPayReturnFromGy : TriggeredAbility :=
  mkTrigger .landYouControlEnters Effect.triggerPayReturnFromGy (activeZones := #[.graveyard])
def onYouSacrificeTokenOppLosesLife : TriggeredAbility :=
  mkTrigger .youSacrificeToken (Effect.triggerTargetOpponentLosesLife 1)
def onLandYouControlEntersPlusOneVigilance : TriggeredAbility :=
  mkTrigger .landYouControlEnters (Effect.seqPlusOneVigilance 2)
def onCastNoncreatureMayDrawXDiscard2 : TriggeredAbility :=
  mkTrigger .youCastNoncreature (Effect.triggerMayDrawXDiscard 2)
def onLandYouControlEntersDrawPlusOneSource : TriggeredAbility :=
  mkTrigger .landYouControlEnters Effect.seqDrawPlusOneSource
def onArmyCombatDamageRingTempts : TriggeredAbility :=
  mkTrigger .armyYouControlCombatDamageToPlayer Effect.triggerRingTempts
def onAttackSetOtherBasePT : TriggeredAbility :=
  mkTrigger .thisAttacks Effect.triggerSetOtherBasePT
def onEnterOrAttackReturnElfGainLife : TriggeredAbility :=
  mkTrigger .enterOrAttack Effect.triggerReturnElfGainLife
def onDiesDealDamageEqualToPowerToOppCreature : TriggeredAbility :=
  mkTrigger .thisDies Effect.triggerDamageFromLastKnownPower
def onEnterExileOppGyCardOppsLoseLife (life : Nat) : TriggeredAbility :=
  mkTrigger .thisEnters (Effect.seqExileOppGyCardOppsLoseLife life)
def onEnterCreaturesYouControlGetAndFirstStrike (power : Int) : TriggeredAbility :=
  mkTrigger .thisEnters (Effect.seqCreaturesPumpAndFirstStrike power)
def onAnotherCreatureYouControlPowerAtMostEntersMayPayDraw (power : Int)
    (generic : Nat) : TriggeredAbility :=
  mkTrigger
    (.permanentEnters (.all #[
      .otherThan .this, .hasType .creature, .controlledBy .you, .stat .power .le (.const power)]))
    (Effect.triggerMayPayGenericDraw generic)
def onEnterDrawThenBottomIfNoLegendary : TriggeredAbility :=
  mkTrigger .thisEnters Effect.triggerDrawThenBottomIfNoLegendary
def onYourEndStepRemoveHopeDrawSac : TriggeredAbility :=
  mkTrigger .stepYourEndStep Effect.triggerRemoveHopeDrawSac
def onAttackTapHumansDraw : TriggeredAbility := mkTrigger .thisAttacks Effect.triggerTapHumansDraw
def onEnterUntapOtherPlusOneIfSubtype (subtype : String) : TriggeredAbility :=
  mkTrigger .thisEnters (Effect.seqUntapPlusOneIfSubtype subtype)
def onEnterDestroyOppArtifactsEnchantmentsGainLife : TriggeredAbility :=
  mkTrigger .thisEnters Effect.triggerDestroyOppArtifactsEnchantmentsGainLife
def onAttackDamageEqualSubtypeToEachOpponent (subtype : String) : TriggeredAbility :=
  mkTrigger .thisAttacks (Effect.triggerDamageEqualSubtypeToEachOpponent (CardSubtype.ofOracleD subtype))
def onAttackDamageEqualTreasures : TriggeredAbility :=
  mkTrigger .thisAttacks Effect.triggerDamageEqualTreasures
def onPlayerCastsSecondSpellLoseLifeCreateTreasure : TriggeredAbility :=
  mkTrigger .anyPlayerCastsSecondSpell Effect.seqLoseLifeCreateTreasure
def onEnterDealDamageDestroyIfSubtype (n : Nat) (subtype : String) : TriggeredAbility :=
  mkTrigger .thisEnters (Effect.triggerDealDamageDestroyIfSubtype n (CardSubtype.ofOracleD subtype))
def onEnterAttachTargetEquipment : TriggeredAbility :=
  mkTrigger .thisEnters Effect.triggerAttachEquipmentToCreature
def onAttackDefenderSacsLeastPower : TriggeredAbility :=
  mkTrigger .thisAttacks Effect.triggerDefenderSacsLeastPower
def onEnterReturnOtherPlusOne : TriggeredAbility :=
  mkTrigger .thisEnters Effect.triggerReturnOtherPlusOne
def onEnterLookAtTopRevealTypes (n : Nat) (types : Array String) : TriggeredAbility :=
  mkTrigger .thisEnters (Effect.triggerLookAtTopRevealTypes n types)
def onEnterCreateTappedTreasuresEqualOppArtifacts : TriggeredAbility :=
  mkTrigger .thisEnters Effect.triggerCreateTappedTreasuresEqualOppArtifacts
def onCombatDamagePutNonlandMvAtMost (mv : Nat) : TriggeredAbility :=
  mkTrigger .thisDealsCombatDamageToPlayerOrBattle (Effect.triggerPutNonlandMvAtMostFromGy mv)
def onEachCombatOthersGetAndOppsGet (subtypes : Array String)
    (power toughness oppP oppT : Int) : TriggeredAbility :=
  mkTrigger .stepEachBeginCombat
    (Effect.triggerOthersGetAndOppsGet (CardSubtype.ofSubtypes subtypes) power toughness oppP oppT)
def onCombatDamageWolfPlusOneOrTreasure : TriggeredAbility :=
  mkTrigger .thisDealsCombatDamageToPlayer Effect.triggerWolfPlusOneOrTreasure
def onYourBeginCombatTrampleCounterBecomeBear : TriggeredAbility :=
  mkTrigger .stepYourBeginCombat Effect.triggerTrampleCounterBecomeBear
def onEnterMillThenSubtypeToHand (n : Nat) (subtype : String) : TriggeredAbility :=
  mkTrigger .thisEnters (Effect.triggerMillThenSubtypeToHand n (CardSubtype.ofOracleD subtype))
def onEnterExileOppNonlandEachUntilLeaves : TriggeredAbility :=
  mkTrigger .thisEnters Effect.triggerExileOppNonlandEachUntilLeaves
def onCastCreaturePlusOneEqualMv : TriggeredAbility :=
  mkTrigger .youCastCreature Effect.triggerPlusOneEqualLastKnownMv
def onMountainEntersQuestThenDragon : TriggeredAbility :=
  mkTrigger .mountainYouControlEnters Effect.triggerMountainQuestDragon
def onEquippedCombatDamageTreasuresPerChosenType : TriggeredAbility :=
  mkTrigger .equippedDealsCombatDamageToPlayer Effect.triggerTreasuresPerChosenType
def onNontokenYouControlDiesRevealCreature : TriggeredAbility :=
  mkTrigger .nontokenCreatureYouControlDies Effect.triggerRevealUntilCreature (limit := .onceEachTurn)
def onAttackMaySacAnotherPlusOneEqualPower : TriggeredAbility :=
  mkTrigger .thisAttacks Effect.triggerAttackSacPlusOneEqualPower
def onEnterLootLandEntersTapped : TriggeredAbility :=
  mkTrigger .thisEnters Effect.triggerLootLandEntersTapped
def onPlayerLosesLifeMillThatMany : TriggeredAbility :=
  mkTrigger (.loseLife .any) Effect.triggerMillThatManyLost
def onDiesDrawPerFatGraveyard : TriggeredAbility :=
  mkTrigger .thisDies Effect.triggerDrawPerFatGraveyard
def onEnterMaySacDrawTreasure : TriggeredAbility :=
  mkTrigger .thisEnters Effect.triggerMaySacDrawTreasure
def onEquippedAttacksPlusOneEachIfCityBlessing : TriggeredAbility :=
  mkTrigger .equippedAttacks Effect.triggerPlusOneEachCitysBlessing
def onYourBeginCombatCastInstantSorceryFromHand : TriggeredAbility :=
  mkTrigger .stepYourBeginCombat Effect.triggerCastInstantSorceryFromHand
def onEquippedCombatDamageCastInstantSorcery : TriggeredAbility :=
  mkTrigger .equippedDealsCombatDamageToPlayer Effect.triggerCastInstantSorceryMvAtMost
def onCastSecondSpellMillThenCopy : TriggeredAbility :=
  mkTrigger .youCastSecondSpell Effect.triggerMillThenCopy
def onCombatAnotherGetsSourcePower : TriggeredAbility :=
  mkTrigger .stepYourBeginCombat Effect.triggerPumpTargetBySourcePower
def onCombatCreateAlienPerInvasion : TriggeredAbility :=
  mkTrigger .stepYourBeginCombat Effect.triggerCreateAlienPerInvasion
def onCombatMayPutArtifactAttachEquipment : TriggeredAbility :=
  mkTrigger .stepYourBeginCombat Effect.triggerMayPutArtifactAttachEquipment
/-- Photon Blast Barrage cast trigger: copy this spell X times (CR 603.1 / 707.10c). -/
def onCastCopyThisSpellXTimes : TriggeredAbility :=
  mkTrigger .thisCast { body := .stack (.copyStackObject .this .chosenX true) }
    (word := .when) (activeZones := #[.stack])
/-- Path of Ancestry mana-spent commander creature-type scry trigger. -/
def onManaSpentCastCommanderTypeScry (n : Nat := 1) : TriggeredAbility :=
  { word := .when
    pattern := manaSpentCastCommanderCreaturePattern
    effect := Effect.scry n }
def onTokenYouControlEntersBelladonna : TriggeredAbility :=
  mkTrigger .tokenYouControlEnters Effect.triggerBelladonnaTokenReward
def onEnterBolgMaySacrifice : TriggeredAbility :=
  mkTrigger .thisEnters Effect.triggerBolgMaySacrifice
def onBolgDealSacrificedPower : TriggeredAbility :=
  mkTrigger .youSacrificeOtherCreature Effect.triggerBolgDealSacrificedPower (word := .when)
def onEquippedAttacksCreateSpirits : TriggeredAbility :=
  mkTrigger .equippedAttacks Effect.triggerCreateSpiritsForEquipped
def onCombatDamageCreateTreasuresEqualPlayerArtifacts : TriggeredAbility :=
  mkTrigger .thisDealsCombatDamageToPlayer Effect.triggerCreateTreasuresEqualDamagedPlayerArtifacts
def onEnterOrOpponentDrawsDeal1AmassOrcs : TriggeredAbility :=
  mkTrigger .enterOrOpponentDrawsExceptFirst Effect.triggerDeal1ThenAmassOrcs
def onAttackWithTotalPowerUntapExtraCombat (n : Int) : TriggeredAbility :=
  mkTrigger (.youAttackWithTotalPower n) Effect.triggerUntapAttackersExtraCombat
    (grouping := .oncePerBatch) (limit := .onceEachTurn)
def onAnotherCreatureYouControlEntersAlliance : TriggeredAbility :=
  mkTrigger .anotherCreatureYouControlEnters Effect.triggerAllianceMode
def onEnterDestroyOtherAmassControllerPower : TriggeredAbility :=
  mkTrigger .thisEnters Effect.triggerDestroyOtherAmassControllerPower
def onOpponentCastsChosenParityModes : TriggeredAbility :=
  mkTrigger .opponentCastsMatchingParity Effect.triggerGollumMode
def onThisOrAnotherSubtypeEntersDiscardHand (subtype : String) : TriggeredAbility :=
  mkTrigger (.thisOrAnotherSubtypeYouControlEnters (CardSubtype.ofOracleD subtype)) Effect.triggerDiscardHandDrawDamageIfStory
def onAttackCastFromGyArtifactInstantSorcery : TriggeredAbility :=
  mkTrigger .thisAttacks Effect.triggerCastFromGyArtifactInstantSorcery
def onAttackEquippedGainDoubleStrike : TriggeredAbility :=
  mkTrigger .thisAttacks Effect.triggerEquippedAttackersGainDoubleStrike
def onEnterTapEnchantedRemoveCounters : TriggeredAbility :=
  mkTrigger .thisEnters Effect.triggerTapEnchantedRemoveCounters
def onDiesRevealTopPutRandomCreature (n : Nat) : TriggeredAbility :=
  mkTrigger .thisDies (Effect.triggerRevealTopPutRandomCreature n)
def onYourBeginCombatIfDrawnTwoPumpFirstStrike : TriggeredAbility :=
  mkTrigger .stepYourBeginCombat Effect.triggerBeginCombatIfDrawnTwoPump
    (interveningIf? := some (condDrawnAtLeast 2))
def onEnterIfNotTokenCopySelf : TriggeredAbility :=
  mkTrigger .thisEnters Effect.triggerCopySelfNonlegendary (interveningIf? := some condSourceNotToken)
def onEnterAttachEquipmentThenFight : TriggeredAbility :=
  mkTrigger .thisEnters Effect.triggerAttachEquipmentThenFight
def onDiesReturnAsArtifact : TriggeredAbility :=
  mkTrigger .thisCreatureDies Effect.triggerReturnAsArtifact
def onEnterExileLandsThenReturnTapped : TriggeredAbility :=
  mkTrigger .thisEnters Effect.triggerExileLandsThenReturnTapped
def onCombatDamageImpulseInstantSorcery : TriggeredAbility :=
  mkTrigger .thisDealsCombatDamageToPlayer Effect.triggerGrimaImpulse
def onYourEndStepPalantir : TriggeredAbility :=
  mkTrigger .stepYourEndStep Effect.triggerPalantir
def onEnterIfCastProtectionEverything : TriggeredAbility :=
  mkTrigger .thisEnters Effect.triggerProtectionEverything (interveningIf? := some condSourceWasCast)
def onYourUpkeepLoseLifePerBurden : TriggeredAbility :=
  mkTrigger .stepYourUpkeep Effect.triggerLoseLifePerBurden
def onFinalSagaChapterRevealSaga : TriggeredAbility :=
  mkTrigger .finalSagaChapterResolves Effect.triggerRevealSaga (limit := .onceEachTurn)
def onCombatDamageToYouSacRingTempts : TriggeredAbility :=
  mkTrigger .combatDamageToYou Effect.triggerSacDamagersRingTempts (grouping := .oncePerBatch)
def onTappedForTeamworkPlusOneAndDraw : TriggeredAbility :=
  mkTrigger .thisTappedForTeamwork Effect.seqPlusOneOnSourceAndDraw
def onEachEndStepDrawIfAttackedOrEnteredSubtype (subtype : String) : TriggeredAbility :=
  let sub := CardSubtype.ofOracleD subtype .hero
  mkTrigger .stepEachEndStep (Effect.triggerDraw 1)
    (interveningIf? := some (condAttackedOrEnteredSubtype sub))
def onAttackOthersOfSubtypeGetEqualToughness (subtype : String) : TriggeredAbility :=
  mkTrigger .thisAttacks
    (Effect.triggerOthersOfSubtypeGetEqualSourceToughness (CardSubtype.ofOracleD subtype .hero))
def onCreatureYouControlEntersScryAndPlan (n : Nat) : TriggeredAbility :=
  mkTrigger .creatureYouControlEnters (Effect.triggerScryAndPlan n)
def onVillainYouControlEntersDrainAndPlan (n : Nat) : TriggeredAbility :=
  mkTrigger (.subtypeYouControlEnters .villain) (Effect.triggerDrainAndPlan n)
def onCreatureCardsToGyDrawLoseLifeAndPlan : TriggeredAbility :=
  mkTrigger .creatureCardPutIntoYourGy Effect.triggerDrawLoseLifeAndPlan (grouping := .oncePerBatch)
def onLandYouControlEntersPlusOneAndPlan : TriggeredAbility :=
  mkTrigger .landYouControlEnters Effect.triggerPlusOneOnTargetAndPlan
def onNthPlanCounter (n : Nat) (eff : Effect) : TriggeredAbility :=
  mkTrigger (.putCountersOnSelf .plan) eff (word := .when)
    (grouping := .counterThreshold .plan #[n])
def onFourthPlanDrawPlusOneEach : TriggeredAbility :=
  onNthPlanCounter 4 Effect.triggerPlanFinishDrawPlusOneEach
def onFourthPlanReturnInstants : TriggeredAbility :=
  onNthPlanCounter 4 Effect.triggerPlanFinishReturnInstants
def onSeventhPlanControlOpponent : TriggeredAbility :=
  onNthPlanCounter 7 Effect.triggerPlanFinishControlOpponent
def onFifthPlanExileTopCast : TriggeredAbility :=
  onNthPlanCounter 5 Effect.triggerPlanFinishExileTopCast
def onThirdPlanCreateRobots : TriggeredAbility :=
  onNthPlanCounter 3 (Effect.triggerPlanFinishCreateRobots 3)
def onFourthPlanDividedDamage : TriggeredAbility :=
  onNthPlanCounter 4 (Effect.triggerPlanFinishDividedDamage 7)
def onFourthPlanIndestructible : TriggeredAbility :=
  onNthPlanCounter 4 Effect.triggerPlanFinishIndestructibleOnTarget
def onEnterSurveil (n : Nat) : TriggeredAbility := mkTrigger .thisEnters (Effect.triggerSurveil n)
/-- Aura ETB trigger applying `action` to `ObjectExpr.attachedHost` (enchanted creature). -/
def onEnterEnchanted (action : ObjectExpr → Instruction) : TriggeredAbility :=
  mkTrigger .thisEnters { body := action .attachedHost }
/-- Equipment ETB trigger attaching this Equipment to target creature you control,
then applying `followup` to that creature if this Equipment is still on the battlefield. -/
def onEnterAttachThen (followup : ObjectExpr → Instruction) : TriggeredAbility :=
  mkTrigger .thisEnters {
    targets := .creatureYouControl
    body := .seq #[
      .permanent (.attach .this (.target 0)),
      Instruction.ifThen (.exists .this) (followup (.target 0))
    ]
  }
def onEnterExileOtherCopyEnchanted : TriggeredAbility :=
  mkTrigger .thisEnters Effect.triggerExileOtherCopyEnchanted
def onEnterExileCreatureReturnEndStep : TriggeredAbility :=
  mkTrigger .thisEnters Effect.triggerExileUntilNextEndStep
def onEnterTapOrUntapNonland : TriggeredAbility :=
  mkTrigger .thisEnters Effect.triggerTapOrUntapNonland
def onEnterCreateFoodOrTreasure : TriggeredAbility :=
  mkTrigger .thisEnters Effect.triggerCreateFoodOrTreasure
def onEnterVillainIfGyElseMill : TriggeredAbility :=
  mkTrigger .thisEnters Effect.triggerVillainIfGyElseMill
def onEnterDrawMayPutLandTapped : TriggeredAbility :=
  mkTrigger .thisEnters Effect.triggerDrawMayPutLandTapped
def onEnterDrawGainLifeIfAnotherHero : TriggeredAbility :=
  mkTrigger .thisEnters Effect.triggerDrawGainLifeIfAnotherHero
def onEnterPlusOneOrTwoIfAnotherHero : TriggeredAbility :=
  mkTrigger .thisEnters Effect.triggerPlusOneOrTwoIfAnotherHero
def onEnterMaySacArtifactOrDiscardDraw : TriggeredAbility :=
  mkTrigger .thisEnters Effect.triggerMaySacArtifactOrDiscardDraw

/-! ### Additional Reality Fracture & MSH named triggered-ability constructors -/

def onYourUpkeepPrepareSource : TriggeredAbility :=
  mkTrigger .stepYourUpkeep Effect.triggerPrepareSource (interveningIf? := some condSourceNotPrepared)
def onEachEndStepPrepareIfThreeDied : TriggeredAbility :=
  mkTrigger .stepEachEndStep Effect.triggerPrepareSource (interveningIf? := some (condCreaturesDiedThisTurn 3))
def onEnterGrantThenCounterByType (k : Array KeywordAbility) : TriggeredAbility :=
  mkTrigger .thisEnters (Effect.triggerGrantThenCounterByType k)
def onEnterDestroyOppPermanentIfSixLands : TriggeredAbility :=
  mkTrigger .thisEnters Effect.triggerDestroyOppPermanentIfSixLands
    (interveningIf? := some (condControlLandsAtLeast 6))
def onYourBeginCombatPumpOrCounterIfScried : TriggeredAbility :=
  mkTrigger .stepYourBeginCombat Effect.triggerPumpOrCounterIfScried
def onYourFirstMainAddGreenPerCharge : TriggeredAbility :=
  mkTrigger .stepYourFirstMain Effect.triggerAddGreenPerChargeCounter
def onScryOrSurveilMayPayDraw (n : Nat) : TriggeredAbility :=
  mkTrigger .youScryOrSurveil (Effect.triggerMayPayGenericDraw n (plusOneOnSource := true))
def onOpponentsDealtCombatDamageDrawTwoWin : TriggeredAbility :=
  mkTrigger .opponentsDealtCombatDamageYourTurn Effect.triggerDrawTwoWinIfEmptyShuffleSource (word := .when) (grouping := .oncePerBatch)
def onYourEndStepSurveilReturnIfGainedLife : TriggeredAbility :=
  mkTrigger .stepYourEndStep Effect.triggerSurveilReturnIfGainedLife (interveningIf? := some (condGainedLifeAtLeast 1))

/-! ### Unified triggered abilities -/

def onEnter (e : Effect) : TriggeredAbility := mkTrigger .thisEnters e

def stepEnchantedControllerDraws : TriggeredAbility :=
  mkTrigger .stepEnchantedControllerUpkeep Effect.stepEnchantedControllerDraws
def stepDrawToTen : TriggeredAbility :=
  mkTrigger .stepYourEndStep Effect.stepDrawToTen (interveningIf? := some (condHandSizeLessThan 10))
def stepCopyAbsorbingMan : TriggeredAbility :=
  mkTrigger .stepYourFirstMain Effect.stepCopyAbsorbingMan
def stepHydeChoose : TriggeredAbility :=
  mkTrigger .stepYourUpkeep Effect.stepHydeChoose
def stepCopyTaskmaster : TriggeredAbility :=
  mkTrigger .stepYourFirstMain Effect.stepCopyTaskmaster
def stepHarnessedFlicker : TriggeredAbility :=
  mkTrigger (.whenCond .stepYourEndStep condSourceHarnessed) Effect.stepHarnessedFlicker

def deathHellcatReturn : TriggeredAbility :=
  mkTrigger .thisDies Effect.deathHellcatReturn
def deathVillainReturnAsHero : TriggeredAbility :=
  mkTrigger .villainYouControlDies Effect.deathVillainReturnAsHero
def deathAttackingReturnHand : TriggeredAbility :=
  mkTrigger .attackingCreatureYouControlDies Effect.deathAttackingReturnHand
def deathDeathtouchOppSac : TriggeredAbility :=
  mkTrigger (TriggerPattern.permanentDies (.all #[
      .otherThan .this, .hasType .creature, .controlledBy .you, .hasKeyword .deathtouch])) Effect.deathDeathtouchOppSac

def thisAttackMayPayPlusOne : TriggeredAbility :=
  mkTrigger .thisAttacks Effect.thisAttackMayPayPlusOne
def thisAttackPayReturnAttacking : TriggeredAbility :=
  mkTrigger .thisAttacks Effect.thisAttackPayReturnAttacking
def thisAttackIfArtifactEnteredDraw : TriggeredAbility :=
  mkTrigger .thisAttacks Effect.thisAttackIfArtifactEnteredDraw (interveningIf? := some condArtifactEnteredThisTurn)
def thisAttackBlinkNontoken : TriggeredAbility :=
  mkTrigger .thisAttacks Effect.thisAttackBlinkNontoken
def thisAttackEquippedDrain : TriggeredAbility :=
  mkTrigger .thisAttacks Effect.thisAttackEquippedDrain (interveningIf? := some condSourceIsEquipped)
def thisAttackDrawIfPower4 : TriggeredAbility :=
  mkTrigger .thisAttacks Effect.thisAttackDrawIfPower4
def thisAttackAttacksAlonePlus2Indestructible : TriggeredAbility :=
  mkTrigger .thisAttacksAlone Effect.thisAttackAttacksAlonePlus2Indestructible

def enterOrAttackCopyKeywords : TriggeredAbility :=
  mkTrigger .enterOrAttack Effect.enterOrAttackCopyKeywords
def enterOrAttackCreateSquirrel : TriggeredAbility :=
  mkTrigger .enterOrAttack Effect.enterOrAttackCreateSquirrel

def watchCombatDamageExileUntilNonland : TriggeredAbility :=
  mkTrigger .thisDealsCombatDamageToPlayer Effect.watchCombatDamageExileUntilNonland
def watchAttacksAloneDrain : TriggeredAbility :=
  mkTrigger .creatureYouControlAttacksAlone Effect.watchAttacksAloneDrain
def watchAttacksAloneFirstStrikeMenace : TriggeredAbility :=
  mkTrigger .creatureYouControlAttacksAlone Effect.watchAttacksAloneFirstStrikeMenace
def watchFirstTapUntap : TriggeredAbility :=
  mkTrigger .creatureYouControlFirstTappedYourTurn Effect.watchFirstTapUntap
def watchSheHulkRedirectOnce : TriggeredAbility :=
  mkTrigger .creatureYouControlDealtDamage Effect.watchSheHulkRedirectOnce (grouping := .perSourceInBatch) (limit := .optionalOnceEachTurn)
def watchSpeedballTargeted : TriggeredAbility :=
  mkTrigger .spellTargetsThis Effect.watchSpeedballTargeted
def watchAnyPlayerSecondDraw : TriggeredAbility :=
  mkTrigger (.drawCard .any) Effect.watchAnyPlayerSecondDraw (limit := .nthEachTurn 2)
def watchYouTargetDrawOnce : TriggeredAbility :=
  mkTrigger .youTargetPlayerOrPermanentWithAbility Effect.watchYouTargetDrawOnce (limit := .onceEachTurn)
def watchVillainOrArtifactDamage : TriggeredAbility :=
  mkTrigger .anotherVillainOrArtifactYouControlEnters Effect.watchVillainOrArtifactDamage
def watchVillainConniveOnce : TriggeredAbility :=
  mkTrigger (.anotherSubtypeYouControlEnters .villain) Effect.watchVillainConniveOnce (limit := .optionalOnceEachTurn)
def watchVillainPlusOneDamageOnce : TriggeredAbility :=
  mkTrigger (.anotherSubtypeYouControlEnters .villain) Effect.watchVillainPlusOneDamageOnce (limit := .onceEachTurn)
def watchVillainAttachEquipment : TriggeredAbility :=
  mkTrigger (.anotherSubtypeYouControlEnters .villain) Effect.watchVillainAttachEquipment
def watchVillainPlusOneLifelink : TriggeredAbility :=
  mkTrigger (.anotherSubtypeYouControlEnters .villain) Effect.watchVillainPlusOneLifelink
def watchHulklingCompare : TriggeredAbility :=
  mkTrigger .anotherCreatureYouControlEnters Effect.watchHulklingCompare (interveningIf? := some condTriggerSubjectGreaterPT)
def watchJusticeBounce : TriggeredAbility :=
  mkTrigger .anotherNonlandYouControlReturnedToHand Effect.watchJusticeBounce
def watchNontokenHeroModal : TriggeredAbility :=
  mkTrigger (.anotherNontokenSubtypeYouControlEnters .hero) Effect.watchNontokenHeroModal
def watchUltronCopy : TriggeredAbility :=
  mkTrigger .anotherNontokenArtifactYouControlEnters Effect.watchUltronCopy
def watchEnchantedAttachEquipment : TriggeredAbility :=
  mkTrigger .enchantedAttacksOrBlocks Effect.watchEnchantedAttachEquipment
def watchEquippedAttacksAloneUntapScry : TriggeredAbility :=
  mkTrigger .equippedAttacksAlone Effect.watchEquippedAttacksAloneUntapScry
def watchEquippedAttacksTap : TriggeredAbility :=
  mkTrigger .equippedAttacks Effect.watchEquippedAttacksTap
def watchEquippedTappedDamage : TriggeredAbility :=
  mkTrigger .equippedBecomesTapped Effect.watchEquippedTappedDamage
def watchHeroesDamagePlusTwo : TriggeredAbility :=
  mkTrigger .heroesYouControlDealDamageToPlayer Effect.watchHeroesDamagePlusTwo (grouping := .oncePerBatch)
def watchMerfolkAttackDraw : TriggeredAbility :=
  mkTrigger .merfolkYouControlAttackPlayer Effect.watchMerfolkAttackDraw (grouping := .perPlayerInBatch)
def watchTokensEnterMayDraw : TriggeredAbility :=
  mkTrigger .tokenYouControlEnters Effect.watchTokensEnterMayDraw (grouping := .oncePerBatch)
def watchHawkeyeModes : TriggeredAbility :=
  mkTrigger .thisBecomesTapped Effect.watchHawkeyeModes
def watchRedHulk : TriggeredAbility :=
  mkTrigger .thisDealtDamage Effect.watchRedHulk (grouping := .oncePerBatch)
def watchHulk : TriggeredAbility :=
  mkTrigger .thisDealtDamage Effect.watchHulk (grouping := .oncePerBatch)

def youAttackingPay2LifeToughness : TriggeredAbility :=
  mkTrigger .youAttack Effect.youAttackingPay2LifeToughness (grouping := .oncePerBatch)
def youAttackingExileTopHeroPump : TriggeredAbility :=
  mkTrigger .youAttack Effect.youAttackingExileTopHeroPump (grouping := .oncePerBatch)
def youAttackingLookSixCast : TriggeredAbility :=
  mkTrigger .youAttack Effect.youAttackingLookSixCast (grouping := .oncePerBatch)

def castingVillainToken : TriggeredAbility :=
  mkTrigger (.youCastSubtype .villain) Effect.castingVillainToken
def castingMerfolkFromBlue : TriggeredAbility :=
  mkTrigger .youCastNoncreature Effect.castingMerfolkFromBlue
def castingMayPayHasteUnblockable : TriggeredAbility :=
  mkTrigger .youCastNoncreature Effect.castingMayPayHasteUnblockable
def castingPlusOneEachOther : TriggeredAbility :=
  mkTrigger .youCastNoncreature Effect.castingPlusOneEachOther
def castingExileFlicker : TriggeredAbility :=
  mkTrigger .youCastNoncreature Effect.castingExileFlicker
def castingVisionModes : TriggeredAbility :=
  mkTrigger .youCastNoncreature Effect.castingVisionModes
def castingDamageEqualMv : TriggeredAbility :=
  mkTrigger .youCastNoncreature Effect.castingDamageEqualMv
def castingDrawPowerEqualHand : TriggeredAbility :=
  mkTrigger .youCastTargetingCreatureYouControl Effect.castingDrawPowerEqualHand
def castingPlusOneThis : TriggeredAbility :=
  mkTrigger .youCastTargetingCreatureYouControl Effect.castingPlusOneThis
def castingPlusOneScry : TriggeredAbility :=
  mkTrigger .youCastTargetingCreatureYouControl Effect.castingPlusOneScry
def castingIronFistTap : TriggeredAbility :=
  mkTrigger .youCastTargetingCreatureYouControl Effect.castingIronFistTap
def castingTargetsGainFlying : TriggeredAbility :=
  mkTrigger .youCastTargetingCreature Effect.castingTargetsGainFlying
def castingCopyIfArtifactOrLand : TriggeredAbility :=
  mkTrigger .youCastInstantSorceryTargetingArtifactOrLand Effect.castingCopyIfArtifactOrLand
def castingTapCreatureOrLand : TriggeredAbility :=
  mkTrigger .youCastNoncreature Effect.castingTapCreatureOrLand

def resourceDiscardExilePlay : TriggeredAbility :=
  mkTrigger (.discard .you) Effect.resourceDiscardExilePlay
def resourceDrawIfAnotherHeroDamage : TriggeredAbility :=
  mkTrigger (.drawCard .you) Effect.resourceDrawIfAnotherHeroDamage (interveningIf? := some (condControlAnotherSubtype .hero))
def resourceSecondDrawBecome66 : TriggeredAbility :=
  mkTrigger (.drawCard .you) Effect.resourceSecondDrawBecome66 (limit := .nthEachTurn 2)
def resourceSecondDrawPlusOneTarget : TriggeredAbility :=
  mkTrigger (.drawCard .you) Effect.resourceSecondDrawPlusOneTarget (limit := .nthEachTurn 2)
def resourceSecondDrawDrain : TriggeredAbility :=
  mkTrigger (.drawCard .you) Effect.resourceSecondDrawDrain (limit := .nthEachTurn 2)
def resourceGainLifePlusOnes : TriggeredAbility :=
  mkTrigger (.gainLife .you) Effect.resourceGainLifePlusOnes
def resourcePlusOneCreateInsectOnce : TriggeredAbility :=
  mkTrigger .youPutPlusOneOnCreature Effect.resourcePlusOneCreateInsectOnce (grouping := .oncePerBatch) (limit := .onceEachTurn)
def resourcePlusOneOnThisOnce : TriggeredAbility :=
  mkTrigger .youPutPlusOneOnOtherCreature Effect.resourcePlusOneOnThisOnce (grouping := .oncePerBatch) (limit := .onceEachTurn)
def resourcePlusOneOnHeroesCreateWall : TriggeredAbility :=
  mkTrigger .youPutPlusOneOnOtherHeroYouControl Effect.resourcePlusOneOnHeroesCreateWall (grouping := .oncePerBatch)

private def lookupTriggerByEffect (cands : Array TriggeredAbility) (fallback : TriggerPattern)
    (e : Effect) (grouping : BatchGrouping := .perOccurrence) : TriggeredAbility :=
  (cands.find? fun ab => ab.effect == e).getD
    (mkTrigger fallback e (grouping := grouping))

def onStep (e : Effect) : TriggeredAbility :=
  lookupTriggerByEffect #[
    stepEnchantedControllerDraws, stepDrawToTen, stepCopyAbsorbingMan,
    stepHydeChoose, stepCopyTaskmaster, stepHarnessedFlicker
  ] .stepYourUpkeep e

def onDeath (e : Effect) : TriggeredAbility :=
  lookupTriggerByEffect #[
    deathHellcatReturn, deathVillainReturnAsHero,
    deathAttackingReturnHand, deathDeathtouchOppSac
  ] .thisDies e

def onThisAttack (e : Effect) : TriggeredAbility :=
  lookupTriggerByEffect #[
    thisAttackMayPayPlusOne, thisAttackPayReturnAttacking,
    thisAttackIfArtifactEnteredDraw, thisAttackBlinkNontoken,
    thisAttackEquippedDrain, thisAttackDrawIfPower4,
    thisAttackAttacksAlonePlus2Indestructible
  ] .thisAttacks e

def onEnterOrAttack (e : Effect) : TriggeredAbility :=
  lookupTriggerByEffect #[
    enterOrAttackCopyKeywords, enterOrAttackCreateSquirrel
  ] .enterOrAttack e

def onYouAttacking (e : Effect) : TriggeredAbility :=
  lookupTriggerByEffect #[
    youAttackingPay2LifeToughness, youAttackingExileTopHeroPump,
    youAttackingLookSixCast
  ] .youAttack e (grouping := .oncePerBatch)

def onWatch (e : Effect) : TriggeredAbility :=
  lookupTriggerByEffect #[
    watchCombatDamageExileUntilNonland, watchAttacksAloneDrain,
    watchAttacksAloneFirstStrikeMenace, watchFirstTapUntap,
    watchSheHulkRedirectOnce, watchSpeedballTargeted,
    watchAnyPlayerSecondDraw, watchYouTargetDrawOnce,
    watchVillainOrArtifactDamage, watchVillainConniveOnce,
    watchVillainPlusOneDamageOnce, watchVillainAttachEquipment,
    watchVillainPlusOneLifelink, watchHulklingCompare,
    watchJusticeBounce, watchNontokenHeroModal, watchUltronCopy,
    watchEnchantedAttachEquipment, watchEquippedAttacksAloneUntapScry,
    watchEquippedAttacksTap, watchEquippedTappedDamage,
    watchHeroesDamagePlusTwo, watchMerfolkAttackDraw,
    watchTokensEnterMayDraw, watchHawkeyeModes, watchRedHulk, watchHulk
  ] .thisBecomesTapped e

def onCasting (e : Effect) : TriggeredAbility :=
  lookupTriggerByEffect #[
    castingVillainToken, castingMerfolkFromBlue,
    castingMayPayHasteUnblockable, castingPlusOneEachOther,
    castingExileFlicker, castingVisionModes, castingDamageEqualMv,
    castingDrawPowerEqualHand, castingPlusOneThis, castingPlusOneScry,
    castingIronFistTap, castingTargetsGainFlying,
    castingCopyIfArtifactOrLand, castingTapCreatureOrLand
  ] .youCastNoncreature e

def onResource (e : Effect) : TriggeredAbility :=
  lookupTriggerByEffect #[
    resourceDiscardExilePlay, resourceDrawIfAnotherHeroDamage,
    resourceSecondDrawBecome66, resourceSecondDrawPlusOneTarget,
    resourceSecondDrawDrain, resourceGainLifePlusOnes,
    resourcePlusOneCreateInsectOnce, resourcePlusOneOnThisOnce,
    resourcePlusOneOnHeroesCreateWall
  ] (.drawCard .you) e


end TriggeredAbility

end Mtg.Engine
