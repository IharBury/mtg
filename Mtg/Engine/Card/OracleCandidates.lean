import Mtg.Engine.Card.OracleActivate
import Mtg.Engine.Card.SpellEffects

/-!
Modeled abilities the Oracle parser can recognize. Each entry is a shape.
`Nat`, `Int`, `String`, and target-kind arguments are read from the card's
own Oracle text, so a prototype such as `Effect.draw 1` also matches “Draw
seven cards,” and `Effect.destroyCreature` also matches “Destroy target
artifact.” Each list keeps one prototype per shape. Another entry that
differs only by those arguments is the same ability, so it is not listed again.
A spell whose text is several of these shapes in a row is parsed as a
`Resolution.sequence` of those shapes, so the sequence itself is not listed.
“Draw N cards, then discard a card” is `draw` followed by `discardCards`,
so that sentence is not listed either.
-/

namespace Mtg.Engine.OracleCandidates

open Mtg.Engine
open Mtg.Engine.OracleActivate

def spellEffects : Thunk (Array Effect) := Thunk.mk fun _ => #[
  Effect.searchBasicLandTapped,
  Effect.sourceGets 1 1,
  Effect.amassGoblins 1,
  Effect.searchLandTypeToHand "Mountain",
  Effect.tapScryDraw 1 1,
  Effect.exileAttackersSearchBasics,
  Effect.dealDamage 3,
  Effect.draw 1,
  Effect.discardCards 1,
  Effect.searchTwoBasicsSplit,
  Effect.targetCantBeBlockedPowerAtMost 2,
  Effect.playAdditionalLandThisTurn,
  Effect.becomeBearCreatureWithLandsPT,
  Effect.chooseTypeReturnOthers,
  Effect.returnFromGyAttachPowerAtMost 1,
  Effect.putOnTopOrBottom,
  Effect.transform,
  Effect.harnessInfinityStone,
  Effect.drawThreeDiscardUnlessArtifact,
  Effect.pump 3 3,
  Effect.addAnyColorSpendOnlyHero,
  Effect.returnFromGyFinalityAttach,
  Effect.watchEnchantedAttachEquipment,
  Effect.plusOneAndDraw 1 2,
  Effect.abilityDraw 1,
  Effect.addTwoAnyColorCreatureSources,
  Effect.watchVillainConniveOnce,
  Effect.grantVigilanceUnblockable,
  Effect.pumpThenExileTopPlay 3 1,
  Effect.dealDamageThenControllerIfTeamwork 5 2,
  Effect.exileCreatureMvAtMostOrAnyIfTeamwork 3 3,
  Effect.pumpAttackingAloneGainLife,
  Effect.stepCopyAbsorbingMan,
  Effect.stepCopyTaskmaster,
  Effect.becomeArtifactCreature44Flying,
  Effect.enterTapOppCantUntapWhileControl,
  Effect.watchHulklingCompare,
  Effect.plusOneAndCreateTigerGod,
  Effect.doublePowerAndToughness,
  Effect.addBlueCantNonartifact,
  Effect.watchFirstTapUntap,
  Effect.watchEquippedTappedDamage,
  Effect.enterRevealHandExileUntilLeaves,
  Effect.copyArtifactYouControlNotLegendary,
  Effect.watchSheHulkRedirectOnce,
  Effect.thisAttackDrawIfPower4,
  Effect.exileTopXPlayThisTurn,
  Effect.thisAttackEquippedDrain,
  Effect.enterMaySacOrDiscardNonlandThenDamage,
  Effect.enterMayTapThenGrantIndestructible,
  Effect.watchHawkeyeModes,
  Effect.thisAttackPayReturnAttacking,
  Effect.enterMaySacAnotherThenDestroyOppNonland,
  Effect.watchRedHulk,
  Effect.castingMayPayHasteUnblockable,
  Effect.watchSpeedballTargeted,
  Effect.youAttackingPay2LifeToughness,
  Effect.drawPerDiscardedThisTurn,
  Effect.deathAttackingReturnHand,
  Effect.enterDestroy .oppCreatureDealtDamageThisTurn,
  Effect.equipmentBecomesConstructHero,
  Effect.youAttackingExileTopHeroPump,
  Effect.watchVillainPlusOneDamageOnce,
  Effect.createTokensEqualSubtype .squirrel11green "Squirrel",
  Effect.enterTapLoseAbilitiesWhileSource,
  Effect.chapterGainControlOfUpToTwoCreaturesTotalMvAtMost 6,
  Effect.nextInstantSorceryCopyIfMvAtMostSourcePower,
  Effect.deathVillainReturnAsHero,
  Effect.castingIronFistTap,
  Effect.creatureYouControlDealsPowerToOppCreature,
  Effect.enterRevealDiscardFromHand,
  Effect.watchUltronCopy,
  Effect.castingVisionModes,
  Effect.watchVillainAttachEquipment,
  Effect.stepHydeChoose,
  Effect.resourceDrawIfAnotherHeroDamage,
  Effect.becomeDinosaurHero 3 5 #[Keyword.reach, Keyword.vigilance],
  Effect.becomeDinosaurHero 6 6 #[Keyword.trample],
  Effect.enterChooseUpToXModes,
  Effect.resourceSecondDrawBecome66,
  Effect.createTappedTokens .villain21menace 1,
  Effect.stepDrawToTen,
  Effect.nextFreeRGCreature,
  Effect.youAttackingLookSixCast,
  Effect.plusOneX,
  Effect.attachToTargetCreatureYouControl,
  Effect.targetCantBeBlockedThisTurn,
  Effect.gainLife 3,
  Effect.dealDamageToCreature 5,
  Effect.putPlusOnePlusOneOnSource 1,
  Effect.enterExileGyPlayUntilNextTurn,
  Effect.enterFightUpToOne,
  Effect.enterReturnNonlandNontoken,
  Effect.dealDamageLoseIndestructibleExile 3,
  Effect.destroyCreature,
  Effect.destroyArtifactOrLandNonflyersCantBlock,
  Effect.plusOnePlusOneTrampleHexproof,
  Effect.untapPumpMaybeAttach 2 2,
  Effect.castingPlusOneScry,
  Effect.stepEnchantedControllerDraws,
  Effect.thisAttackAttacksAlonePlus2Indestructible,
  Effect.castingPlusOneThis,
  Effect.watchNontokenHeroModal,
  Effect.resourceSecondDrawDrain,
  Effect.deathHellcatReturn,
  Effect.plusOneUpToOneAndPlayerGainsLife 2,
  Effect.drawAndLoseLife 2 2,
  Effect.drawLoseLifeThenAmass 2,
  Effect.ownerShuffleSourceDraw 3,
  Effect.creaturesYouControlGetOppsLoseLife 2 0 2,
  Effect.plusOneAndCreateTokens 2 .robotVillain22,
  Effect.subtypesGainMenace #["Goblin", "Orc"],
  Effect.subtypesGainMenace #["Elf"],
  Effect.teamGain #[Keyword.menace],
  Effect.amassGoblinsOrFromGy 1 3,
  Effect.exileTopPlayUntilEndOfNextTurn,
  Effect.tapOneOrTwoCreatures,
  Effect.grantHexproofIndestructible,
  Effect.abilityCreaturesYouControlGet 1 1,
  Effect.scry 2,
  Effect.abilitySurveil 1,
  Effect.counterUnlessPays 4,
  Effect.counterExilePermanentMayCast,
  Effect.exchangeControlSharingType,
  Effect.returnFromGraveyardToHand,
  Effect.pumpAndExileIfDies (-5) (-5),
  Effect.creaturesTargetPlayerGet (-1) (-1),
  Effect.targetPlayerDrawLoseLife 2 2,
  Effect.pumpAndLifelink 2 2,
  Effect.pumpAndGrantKeywords 3 0 #[Keyword.reach, Keyword.firstStrike],
  Effect.creaturesYouControlGet 2 1,
  Effect.destroyArtifactOrEnchantmentGainLife 2,
  Effect.becomeArtifactGainIndestructible,
  Effect.addAnyColor,
  Effect.returnCreatureFromGyThenAmass 3,
  Effect.counterThenRecruitIfMvAtMost 2,
  Effect.plusOneThenEachOtherIfFromGy,
  Effect.drawIfFromGy 1 2,
  Effect.plusOneThenFight 2,
  Effect.searchLegendaryCreatureToHand,
  Effect.addMana #[.colored .black, .colored .red],
  Effect.millThenPutInstantOrSorcery 4,
  Effect.exileThenReturnYouControl,
  Effect.dealDamageToCreatureExileIfDies 3,
  Effect.abilityCreateTokens .dwarf 1,
  Effect.millThenPutLands 4 2,
  Effect.dealDamageToEachOppCreature 1,
  Effect.dealDamageToEachNonDragonThenAddDragonMana 3,
  Effect.millThenPutAllInstantsOrSorceries 6,
  Effect.exileTopPlayIfYouControlSubtype 2 "Wizard",
  Effect.createTokensX .dwarf,
  Effect.returnSpellCantCastIfGift,
  Effect.chapterDealDamageToOppCreature 6,
  Effect.chapterDestroyOppArtifact,
  Effect.chapterAddMana (.colored .red),
  Effect.chapterSearchBasicLandToHand,
  Effect.chapterGainLandfallCreateElf,
  Effect.chapterElvesGetVigilance 1,
  Effect.chapterOpponentDiscardsNonland,
  Effect.chapterAmassGoblins 1,
  Effect.chapterOpponentLosesYouGain 1,
  Effect.exileThenReturnNextEnd,
  Effect.searchBasicBeholdSubtypeUntap "Elf",
  Effect.twoPlayersDraw,
  Effect.exileTopXOppPlayForLife,
  Effect.discardLegendarySameNameDraw,
  Effect.chapterGrantHexproofWhileRemains,
  Effect.chapterPreventDamageWhileRemains,
  Effect.chapterDraw 1,
  Effect.riddlesInTheDark,
  Effect.chapterSearchBasicPlainsExileGainLife 2 2,
  Effect.chapterReturnLinkedExileToHand,
  Effect.chapterGrantAttackPumpPerPlainsThisTurn,
  Effect.chapterBlinkUntilEndStep,
  Effect.supperForSpiders,
  Effect.eaglesAreComing,
  Effect.chapterTreasureThenDragonIfFour,
  Effect.chapterRecruit,
  Effect.chapterReturnCreatureFromGyMvAtMost 3,
  Effect.chapterPlusOneUpToOne,
  Effect.lookAtTopLandsGainLife 20 8,
  Effect.drawEqualSacrificedPowerThenDiscard,
  Effect.millPlayer 3,
  Effect.counterCreatureSpellPTAtMost 2,
  Effect.returnFromGraveyardTapped,
  Effect.allCreaturesGet (-4) (-4),
  Effect.exileGraveyardCreaturesGrantCast,
  Effect.destroyTargetCreatureControllerLosesLife 2,
  Effect.returnSpellDraw,
  Effect.abilityScry 2,
  Effect.targetPlayerDraw 2,
  Effect.drawEqualToughnessThenPutCreatures,
  Effect.addRedPerOppArtifacts,
  Effect.abilityCreateTokensX .treasure,
  Effect.abilityCreateTokens .food 1,
  Effect.arwenShare,
  Effect.gainControlOppArtifacts,
  Effect.damageOppCreaturesEqualOtherSpellsMv,
  Effect.grantCombatDamageCreateTreasure,
  Effect.phaseOutKicker,
  Effect.putShadowCounter,
  Effect.damageEachOpponent 1,
  Effect.chooseTwoDestroyRest,
  Effect.blackGateUnblockable,
  Effect.burdenThenDraw,
  Effect.teamGain #[Keyword.doubleStrike],
  Effect.sourceGainsIndestructibleTap,
  Effect.castingPlusOneEachOther,
  Effect.watchHulk,
  Effect.plusOneOnEachOtherSubtype "Hero" 1,
  Effect.createTokens .hero32vigilance 2,
  Effect.plusOneAndIndestructibleCounter,
  Effect.dealDamageToAttackerOrBlocker 2 4,
  Effect.resourcePlusOneOnHeroesCreateWall,
  Effect.stepHarnessedFlicker,
  Effect.exileCreatureToughnessAtLeast 4,
  Effect.exileEnchantmentMvAtLeast 4,
  Effect.lookAtTopPutTypes 7 #["Hero", "Equipment", "Vehicle"],
  Effect.enterReturnGyPermanentThisTurn,
  Effect.mayPutHeroMvOrDraw 3,
  Effect.plusOneOnEachYouControl,
  Effect.investigatePumpFlyingUntap,
  Effect.anotherYouControlGetsAndGrant 2 0 #[Keyword.hexproof],
  Effect.castingTapCreatureOrLand,
  Effect.tapTargetCreature,
  Effect.enterOppCreatesTheVoid,
  Effect.watchEquippedAttacksAloneUntapScry,
  Effect.plusOneLifelinkIndestructible,
  Effect.enterPlusOnesOrReturnArtEnch,
  Effect.targetPlayerCreatesTokens .leviathan65hexproof 1,
  Effect.returnOneOrTwoNonlands,
  Effect.watchMerfolkAttackDraw,
  Effect.drawX,
  Effect.copyControlledAbility .creature,
  Effect.enterCreateRedwing,
  Effect.revealTopDrawIfArtifact,
  Effect.watchJusticeBounce,
  Effect.plusOneAndExtraTurn,
  Effect.watchYouTargetDrawOnce,
  Effect.watchTokensEnterMayDraw,
  Effect.castingDrawPowerEqualHand,
  Effect.copyNontokenCreaturesYouControl,
  Effect.castingMerfolkFromBlue,
  Effect.lookAtTopRevealArtifact 4,
  Effect.ownerPutsLibraryThenConnive,
  Effect.counterUnlessPaysTeamwork 2 4,
  Effect.castingExileFlicker,
  Effect.watchCombatDamageExileUntilNonland,
  Effect.pump (-4) (-4),
  Effect.returnGySubtypeToHand "Villain",
  Effect.returnGySubtypeToHand "Hero",
  Effect.watchAttacksAloneDrain,
  Effect.connive,
  Effect.resourceDiscardExilePlay,
  Effect.eachOppDiscardThenPlusOne,
  Effect.addTwoAnyColorEquipment,
  Effect.targetGets (-4) (-4),
  Effect.resourceSecondDrawPlusOneTarget,
  Effect.abilityCreateTokens .wall04defender 1,
  Effect.abilityTargetPlayerDraw 4,
  Effect.returnGyCreatureMvAtMostOrAny 4,
  Effect.returnGyCreatureThenPlusOne 2,
  Effect.grantDeathtouch,
  Effect.watchVillainPlusOneLifelink,
  Effect.dealDamageToEachCreature 3,
  Effect.destroyLandSearchBasic,
  Effect.gainControlUntilEotOrNextIfVillain,
  Effect.castingCopyIfArtifactOrLand,
  Effect.exileHandDrawPlayUntilNext,
  Effect.createTokensThenTeamPump .villain21menace 1 1 0,
  Effect.watchVillainOrArtifactDamage,
  Effect.enterDealDamageUpToOne 4,
  Effect.copyThisSpellXTimesThenDamage 1,
  Effect.plusOneAndDoubleStrikeCounter,
  Effect.abilityCreateTokens .treasure 1,
  Effect.grantDoubleStrikeTeamworkTrample,
  Effect.castingDamageEqualMv,
  Effect.maySacArtifactOrDiscardDraw 2,
  Effect.returnUpToTwoGyModal,
  Effect.addAnyColorEqualToSourcePower,
  Effect.revealTopPutCreatures 8,
  Effect.fight,
  Effect.plusOneOnCreature,
  Effect.plusOneAndGrant #[Keyword.vigilance, Keyword.indestructible, Keyword.haste],
  Effect.resourceGainLifePlusOnes,
  Effect.enterCreateZabu,
  Effect.resourcePlusOneOnThisOnce,
  Effect.plusOneAndCreateTokens 1 .hero32vigilance,
  Effect.proliferateEachKind,
  Effect.creatureYouControlDealsTwicePower,
  Effect.millThenPutPermanentGainLife 2 2,
  Effect.gainLifeSearchBasicPlusOne 2,
  Effect.millThenPutSubtypeOrEnchantment 4 "Hero",
  Effect.watchHeroesDamagePlusTwo,
  Effect.enterOrAttackCreateSquirrel,
  Effect.plusOneOnCreatureN 3,
  Effect.chooseTargetDoubleAndTrample,
  Effect.plusOneThenFightUpToOne,
  Effect.thisAttackMayPayPlusOne,
  Effect.resourcePlusOneCreateInsectOnce,
  Effect.mayDrawPerArtifactOppsDraw,
  Effect.artifactSpellsCostLessThisTurn 1,
  Effect.supertypeSpellsCostLessThisTurn 1,
  Effect.chapterDealXDamageToTargetOpponentGreatestArtifactMv,
  Effect.createTokensEqualRemovedPlusOnes .insect11green,
  Effect.createTokens .villain21menace 2,
  Effect.chapterDealDamageToEachNonSubtypeAndOpponents 2 "Villain",
  Effect.createTokensPerSubtype .treasure "Villain",
  Effect.watchAttacksAloneFirstStrikeMenace,
  Effect.destroyUpToOneNonland,
  Effect.eachOpponentLosesLife 2,
  Effect.createGalactus,
  Effect.thisAttackIfArtifactEnteredDraw,
  Effect.watchAnyPlayerSecondDraw,
  Effect.castingVillainToken,
  Effect.thisAttackBlinkNontoken,
  Effect.copyControlledAbility .artifact,
  Effect.deathDeathtouchOppSac,
  Effect.castingTargetsGainFlying,
  Effect.creaturesYouControlGetAndGrant 1 1 #[Keyword.vigilance],
  Effect.fightUpToOne,
  Effect.plusTwoThenOddEvenDestroy,
  Effect.enterCreateSturdyShieldAttach,
  Effect.searchLibraryOrGyArtifactCreatureX,
  Effect.worldsWithinWorlds,
  Effect.addMana #[.colorless, .colorless, .colorless],
  Effect.watchEquippedAttacksTap,
  Effect.enterOrAttackCopyKeywords,
  Effect.lookAtTopRevealSubtype 3 "Hero",
  Effect.addFourAnyCombination,
  Effect.addAnyColorSpendOnlyArtifactSpell,
  Effect.abilityCreateTokens .doombot 1,
  Effect.targetSubtypeConnives "Villain",
  Effect.ofTrigger (.scry 2),
  Effect.drawAndLoseLife 1 0,
  Effect.becomeSubtypeWithLandsPT "Elf",
  Effect.plusOneOnTarget 2,
  Effect.ofTrigger (.draw 1),
  Effect.triggerCreateTokens .treasure 1 true,
  Effect.ofTrigger (.dividedDamage 3 3),
  Effect.ofTrigger .opponentSacrificesCreature,
  Effect.ofTrigger (.attachTo .legendaryCreatureYouControl),
  { targeting := .of .creatureYouControl
    body := Instruction.putPlusOne (.target 0) 1
    phrase := "put a +1/+1 counter on target creature you control" },
  Effect.triggerCreateTokens .wall 1,
  Effect.ofTrigger .connive,
  { body := Instruction.putPlusOne .this 1
    phrase := "put a +1/+1 counter on this creature" },
  Effect.ofTrigger (.gainLife 2),
  { targeting := .of .creature
    body := Instruction.pumpFixed (.target 0) 4 4
    phrase := "target creature gets +4/+4 until end of turn" },
  Effect.ofTrigger (.exileUntilLeaves .oppTappedCreature),
  Effect.ofTrigger (.recruit .you),
  Effect.ofTrigger (.damageEachOpponent 2),
  Effect.ofTrigger .exileTop,
  Effect.ofTrigger (.mayTo .discard (.draw 2)),
  Effect.ofTrigger .opponentDiscards,
  { targeting := .of .anotherCreatureYouControl
    body := Instruction.pumpAndTrample (.target 0) 2 0
    phrase := "another target creature you control gets +2/+0 and gains trample until end of turn" },
  Effect.ofTrigger .investigate,
  Effect.ofTrigger (.amass 1 .orc),
  Effect.ofTrigger .searchLibrary,
  Effect.ofTrigger .eachPlayerSacrificesCreature,
  Effect.ofTrigger .plusOneEachYouControl,
  Effect.ofTrigger .pumpByLookedAt,
  Effect.ofTrigger (.mayDiscardHandDraw 4),
  Effect.ofTrigger .pumpGreatestPower,
  Effect.ofTrigger (.damageBlockers 1),
  Effect.triggerCreateThenAttach .treasure,
  Effect.ofTrigger .ringTempts,
  Effect.ofTrigger .setOtherBasePT,
  Effect.ofTrigger .returnElfGainLife,
  Effect.ofTrigger .damageFromLastKnownPower,
  Effect.ofTrigger (.mayPayGenericDraw 1),
  Effect.ofTrigger .drawThenBottomIfNoLegendary,
  Effect.ofTrigger .removeHopeDrawSac,
  Effect.ofTrigger .tapHumansDraw,
  Effect.ofTrigger .destroyOppArtifactsEnchantmentsGainLife,
  Effect.ofTrigger (.damageEqualSubtypeToEachOpponent .dwarf),
  Effect.ofTrigger .damageEqualTreasures,
  Effect.ofTrigger (.dealDamageDestroyIfSubtype 1 .dragon),
  Effect.ofTrigger .attachEquipmentToCreature,
  Effect.ofTrigger .defenderSacsLeastPower,
  Effect.ofTrigger .returnOtherPlusOne,
  Effect.ofTrigger (.lookAtTopRevealTypes 4 #["Dwarf", "Equipment"]),
  Effect.ofTrigger .createTappedTreasuresEqualOppArtifacts,
  Effect.ofTrigger (.putNonlandMvAtMostFromGy 3),
  Effect.ofTrigger (.othersGetAndOppsGet #[.goblin, .orc] 2 2 (-1) (-1)),
  Effect.ofTrigger .wolfPlusOneOrTreasure,
  Effect.ofTrigger .trampleCounterBecomeBear,
  Effect.ofTrigger (.millThenSubtypeToHand 4 .elf),
  Effect.ofTrigger .exileOppNonlandEachUntilLeaves,
  Effect.ofTrigger .plusOneEqualLastKnownMv,
  Effect.ofTrigger .mountainQuestDragon,
  Effect.ofTrigger .treasuresPerChosenType,
  Effect.ofTrigger .revealUntilCreature,
  Effect.ofTrigger .attackSacPlusOneEqualPower,
  Effect.ofTrigger .lootLandEntersTapped,
  Effect.ofTrigger .millThatManyLost,
  Effect.ofTrigger .drawPerFatGraveyard,
  Effect.ofTrigger .maySacDrawTreasure,
  Effect.ofTrigger (.plusOneEachYouControl .citysBlessing),
  Effect.ofTrigger .castInstantSorceryFromHand,
  Effect.ofTrigger .castInstantSorceryMvAtMost,
  Effect.ofTrigger .millThenCopy,
  Effect.ofTrigger .pumpTargetBySourcePower,
  Effect.ofTrigger .createAlienPerInvasion,
  Effect.ofTrigger .mayPutArtifactAttachEquipment,
  Effect.ofTrigger .cascade,
  Effect.ofTrigger .bolgMaySacrifice,
  Effect.ofTrigger (.surveil 2),
  Effect.ofTrigger (.targetOpponentLosesLife 1),
  Effect.ofTrigger (.amass 0 (amount := .sourcePower)),
  Effect.ofTrigger .recruit,
  { targeting := .of .creature
    body := Instruction.putPlusOne (.target 0) 1
    phrase := "put a +1/+1 counter on target creature" },
  Effect.ofTrigger (.attachTo .creatureYouControl),
  Effect.ofTrigger (.connive (.target .creatureYouControl)),
  Effect.ofTrigger (.exileUntilLeaves .oppNonland),
  Effect.ofTrigger (.exileUntilLeaves .defendingPlayerCreature),
  { body := Instruction.pumpFixed .this 1 1
    phrase := "this creature gets +1/+1 until end of turn" },
  Effect.triggerCreateTokens .treasure 1,
  Effect.ofTrigger .searchBasicLandToHand,
  Effect.ofTrigger (.exileTarget .anotherCreature),
  Effect.ofTrigger .returnCreatureFromGyToHand,
  Effect.ofTrigger .honeEachEquipment,
  Effect.ofTrigger .plusOneEachOtherGainLife,
  Effect.ofTrigger .pumpTargetPerPlains,
  Effect.ofTrigger .pumpForEachOtherCreature,
  { targeting := .of .attackingCreatureWithoutFlying
    body := Instruction.grantKeywords (.target 0) #[Keyword.flying]
    phrase := "target attacking creature without flying gains flying until end of turn" },
  Effect.ofTrigger .returnLinkedExile,
  Effect.ofTrigger .createAxe,
  Effect.ofTrigger .tapOppOrUntapYours,
  Effect.ofTrigger .gainControlOppUntilEot,
  Effect.ofTrigger (.createAxe (attach := true)),
  Effect.ofTrigger .payReturnFromGy,
  Effect.ofTrigger (.may (.drawXDiscard 2)),
  Effect.ofTrigger .belladonnaTokenReward,
  Effect.ofTrigger .bolgDealSacrificedPower,
  Effect.ofTrigger .createSpiritsForEquipped,
  Effect.ofTrigger .createTreasuresEqualDamagedPlayerArtifacts,
  Effect.ofTrigger .deal1ThenAmassOrcs,
  Effect.ofTrigger .allianceMode,
  Effect.ofTrigger .destroyOtherAmassControllerPower,
  Effect.ofTrigger .gollumMode,
  Effect.ofTrigger .discardHandDrawDamageIfStory,
  Effect.ofTrigger .castFromGyArtifactInstantSorcery,
  Effect.ofTrigger .equippedAttackersGainDoubleStrike,
  Effect.ofTrigger .tapEnchantedRemoveCounters,
  Effect.ofTrigger .beginCombatIfDrawnTwoPump,
  Effect.ofTrigger .honePerOppAttach,
  Effect.ofTrigger (.damageTargetOpponent 2),
  Effect.ofTrigger .copySelfNonlegendary,
  Effect.ofTrigger .attachEquipmentThenFight,
  Effect.ofTrigger .returnAsArtifact,
  Effect.ofTrigger .exileLandsThenReturnTapped,
  Effect.ofTrigger .grimaImpulse,
  Effect.ofTrigger .palantir,
  Effect.ofTrigger .treasuresEqualLastKnown,
  Effect.ofTrigger .protectionEverything,
  Effect.ofTrigger .loseLifePerBurden,
  Effect.ofTrigger .revealSaga,
  Effect.ofTrigger .sacDamagersRingTempts,
  Effect.ofTrigger .lootAndPlan,
  Effect.ofTrigger .createVillainAndPlan,
  Effect.ofTrigger .drawLoseLifeAndPlan,
  Effect.ofTrigger .treasureTappedAndPlan,
  Effect.ofTrigger .plusOneOnTargetAndPlan,
  Effect.ofTrigger .planFinishDrawPlusOneEach,
  Effect.ofTrigger .planFinishReturnInstants,
  Effect.ofTrigger .planFinishControlOpponent,
  Effect.ofTrigger .planFinishExileTopCast,
  Effect.ofTrigger (.planFinishCreateRobots 3),
  Effect.ofTrigger (.planFinishDividedDamage 7),
  Effect.ofTrigger .planFinishIndestructibleOnTarget,
  Effect.ofTrigger .exileOtherCopyEnchanted,
  Effect.ofTrigger .exileUntilNextEndStep,
  Effect.ofTrigger .tapOrUntapNonland,
  Effect.ofTrigger .createFoodOrTreasure,
  Effect.ofTrigger .villainIfGyElseMill,
  Effect.ofTrigger .drawMayPutLandTapped,
  Effect.ofTrigger .drawGainLifeIfAnotherHero,
  Effect.ofTrigger .plusOneOrTwoIfAnotherHero,
  Effect.ofTrigger .maySacArtifactOrDiscardDraw,
  Effect.pumpAndGrantKeywords 2 2 #[Keyword.flying],
  Effect.plusOneThenGainLife 1 1,
  Effect.damageTargetOpponent 1,
  Effect.millSelf 3,
  Effect.mayDiscardDraw 1,
  Effect.createTokens .heartwood 1,
  Effect.createTokens .beast44trample 1,
  Effect.createTokensThenSurveil .cadet 1 1,
  Effect.createTokensLifeGained .cadet,
  Effect.setBasePT 0 0,
  Effect.oppSacrificesGreatestMvGainLife 2,
  Effect.damageThenEmpowerExcess 6,
  Effect.jaceLoyaltyAtInstantSpeed,
  Effect.creaturesYouControlGetAndGrant 1 0 #[Keyword.haste],
  Effect.createTokens .pridemate 1,
  Effect.copyEachCreatureOfTargetPlayer,
  Effect.copyNextInstantSorceryThisTurn,
  Effect.addMana #[.colored .red],
  Effect.exileTopMayCastElseDamageOpponents 2,
  Effect.emblemCastSpellDamage 5,
  Effect.addMana #[.colored .red, .colored .red],
  Effect.firstDealsStatDamageToSecond false,
  Effect.firstDealsStatDamageToSecond true,
  Effect.generousRevival,
  Effect.hexhavenBattalion,
  Effect.kindredJudgment,
  Effect.loyalTutor,
  Effect.predictivePreparations,
  Effect.prophesiedEnd,
  Effect.refuteDestiny,
  Effect.returnToTheLightRealms,
  Effect.surgicalPrecisionDestroy,
  Effect.drawAndGainLife 1 2,
  Effect.yourFateEndsHere,
  Effect.counterTargetSpell,
  Effect.cruelCalculations,
  Effect.icyReceptionCounter,
  Effect.targetCreatureGets (-5) 0,
  Effect.preciseRedaction,
  Effect.sphinxsApproach,
  Effect.unsummon,
  Effect.unwindHistory,
  Effect.arcOfFortune,
  Effect.castAwayDoubt,
  Effect.extendedAbsence,
  Effect.extrapolateTheImpossible,
  Effect.overwriteTheMultiverse,
  Effect.rewriteRegrets,
  Effect.riseDraw,
  Effect.allCreaturesGet (-3) (-3),
  Effect.destroyTargetCreatureOrPlaneswalker,
  Effect.solveForDisappointment,
  Effect.terminalCriticism,
  Effect.vraskasMercyDestroy,
  Effect.vraskasMercyEmpower,
  Effect.artifistAcumen,
  Effect.awakenTheInferno,
  Effect.commandTheStage,
  Effect.essenceBurn,
  Effect.fulminousForteSweep,
  Effect.damageToCreatureOrPlaneswalker 5,
  Effect.moltenTide,
  Effect.enroot,
  Effect.flourishingGrapple,
  Effect.restoreWithEmpathy,
  Effect.somethingWorthSaving,
  Effect.tethermagesAdvantage,
  Effect.creaturesYouControlGetUntilEot 2 0,
  Effect.chargeTheSanctumPump,
  Effect.clashOfElements,
  Effect.entrustTheSpark,
  Effect.drawThenEmpower 1 2,
  Effect.bounceSpellOrCreature,
  Effect.damageToCreatureWithFlying 6,
  Effect.plusOneThenGrant 2 #[Keyword.trample],
  Effect.addColorless 3,
  Effect.recursiveRecruitment,
  Effect.targetCreatureGains #[Keyword.firstStrike, Keyword.deathtouch]
    "first strike and deathtouch",
  Effect.cadetWithHaste,
  Effect.stingingVitriol,
  Effect.theorixCounter,
  Effect.millThenDraw 3 1,
  Effect.twinnedVision,
  Effect.twistedFates,
  Effect.permanentYouControlGains #[Keyword.hexproof, Keyword.indestructible],
  Effect.drawAndGainLife 1 3,
  Effect.vindictiveTriumph,
  Effect.tamsResistance,
  Effect.returnLegendaryCardToHand,
  Effect.plusOneVigilanceIndestructible,
  Effect.fraTapTargetCreature,
  Effect.untapTargetCreature,
  Effect.destroyNoncreatureNonland,
  Effect.gainLifeMode 4,
  Effect.minusPowerPerGraveyard,
  Effect.surveilMode 2,
  Effect.sourceDealsDamageToCreatureOrPlaneswalker 4,
  Effect.createCadetMode,
  Effect.drawMode,
  FraCandidates.ab (Instruction.createTokensFixed .illusion11blue 1)
    "Create a 1/1 blue Illusion creature token",
  FraCandidates.ab (Instruction.bounce .allTargets)
    "For each opponent, return up to one target artifact or creature that player controls to its owner's hand"
    (.forEachOpponentControlled (.any #[.hasType .artifact, .hasType .creature]) (.upTo 1))
    (allowsZeroTargets := true),
  FraCandidates.ab
    (.seq #[
      Instruction.drawFixed 3,
      Instruction.putCounters
        (.inZones .battlefield (.all #[.hasType .creature, .controlledBy .you]))
        .plusOnePlusOne (.playerMetric .handSize .you)])
    "Draw three cards. Then put X +1/+1 counters on each creature you control, where X is the number of cards in your hand",
  FraCandidates.ab
    (.bind ⟨0⟩ (Instruction.surveilFixed 1)
      (Instruction.bounce (.filter (.stepObjects ⟨0⟩) (.all #[.not (.hasType .creature), .not (.hasType .land)]))))
    "Surveil 1. If you put a noncreature, nonland card into your graveyard this way, put that card into your hand",
  FraCandidates.ab
    (Instruction.addMana {
      spec := .fixedOne (.colored .blue)
      restriction := some (.onlyForSpells (.not (.hasType .creature))) })
    "Add {U}. Spend this mana only to cast a noncreature spell",
  FraCandidates.ab (Instruction.tapAndStun (.target 0) .chosenX)
    "Tap target artifact or creature. Put X stun counters on it"
    (.ofDomain (.object .battlefield (.any #[.hasType .artifact, .hasType .creature]))),
  FraCandidates.ab
    (.create (.emblem .you {
      triggeredAbilities := #[TriggeredAbility.ofPattern .youCastSpell
        "Whenever you cast a spell, draw a card." (Instruction.drawFixed 1)] }))
    "You get an emblem with \"Whenever you cast a spell, draw a card.\"",
  FraCandidates.ab
    (Instruction.empower .jace
      (.aggregate .count .one (.inZones .battlefield (.all #[.hasSubtype (.literal .island), .controlledBy .you]))))
    "Empower Jace X, where X is the number of Islands you control",
  FraCandidates.ab
    (.installEffect (.createDelayedTrigger {
      pattern := .creatureAttacksYouOrYourPlaneswalker
      duration := .untilNextTurnOf .you
      oneShot := false
      effect := { body := Instruction.pumpFixed .triggerSubject (-5) 0, phrase := "It gets -5/-0 until end of turn" } }))
    "Until your next turn, whenever a creature attacks you or a planeswalker you control, it gets -5/-0 until end of turn",
  FraCandidates.ab
    (.player (.inspectLibrary {
      source := .allButBottom .opponents
      action := .moveAll .exile
      rest := .leaveInPlace }))
    "Exile all but the bottom card of each opponent's library",
  FraCandidates.ab (Instruction.pumpFixed (.target 0) (-4) (-1) (.untilNextTurnOf .you))
    "Up to one target creature gets -4/-1 until your next turn"
    (.single { domain := .creature, count := .upTo 1 }) (allowsZeroTargets := true),
  FraCandidates.ab
    (.bind ⟨0⟩
      (.forEach (.eachPlayer .any) ⟨1⟩
        (.moveZone
          (.inZones .battlefield (.all #[.hasType .creature, .controlledBy (PlayerFilter.ofExpr (.stepPlayers ⟨1⟩))]))
          .graveyard .sacrifice
          { choice? := some { chooser := .player (.stepPlayers ⟨1⟩), count := .exact (.const 1) } }))
      (Instruction.ifThen (.exists (.filter (.stepObjects ⟨0⟩) (.controlledBy .you)))
        (Instruction.createTokensFixed .beast44trample 1)))
    "Each player sacrifices a creature of their choice. If you sacrificed a creature this way, create a 4/4 green Beast creature token with trample",
  FraCandidates.ab
    (.forEach (.eachPlayer .opponent) ⟨0⟩
      (.bind ⟨1⟩ (Instruction.discardFixed 2 (.stepPlayers ⟨0⟩))
        (Instruction.ifThen
          (.cmp .lt (.aggregate .count .one (.filter (.stepObjects ⟨1⟩) (.not (.hasType .land)))) (.const 2))
          (Instruction.drawFixed 1))))
    "Each opponent discards two cards. For each opponent who didn't discard two nonland cards this way, you draw a card",
  FraCandidates.ab
    (.seq #[
      .moveZone (.inZones (.handOf .you) .anyObject) .graveyard .discard,
      .player (.drawCards .you
        (.aggregate .count .one (.inZones .battlefield (.all #[.hasType .creature, .controlledBy .you]))))])
    "Discard your hand, then draw a card for each creature you control",
  FraCandidates.ab
    (Instruction.dealDamageFixed
      (.objects (.inZones .battlefield (.all #[.hasType .creature, .not (.all #[.isToken true, .controlledBy .you])]))) 4)
    "This deals 4 damage to each creature except for tokens you control",
  FraCandidates.ab
    (.create (.emblem .you { staticAbilities := #[StaticAbility.creaturesYouControlGet 2 2] }))
    "You get an emblem with \"Creatures you control get +2/+2.\"",
  FraCandidates.ab (Instruction.untap .allTargets) "Untap up to two target lands"
    (.single { domain := .land, count := .upTo 2 }) (allowsZeroTargets := true) (maxTargets := 2),
  FraCandidates.ab
    (.installEffect (.createDelayedTrigger {
      pattern := .creaturesAttackYourOpponent
      grouping := .perPlayerInBatch
      duration := .untilNextTurnOf .you
      oneShot := false
      effect := { body := Instruction.pumpAndTrample .triggerSubject 2 2, phrase := "Those creatures get +2/+2 and gain trample until end of turn" } }))
    "Until your next turn, whenever one or more creatures attack one of your opponents, those creatures get +2/+2 and gain trample until end of turn",
  FraCandidates.ab (.seq #[Instruction.dealDamageFixed (.players .opponents) 1, Instruction.gainLifeFixed 1])
    "This planeswalker deals 1 damage to each opponent and you gain 1 life",
  FraCandidates.ab
    (Instruction.putCounters (.target 0) .plusOnePlusOne
      (.aggregate .count .one (.inZones .battlefield (.all #[.hasType .land, .controlledBy .you]))))
    "Put a +1/+1 counter on target creature for each land you control"
    .creature,
  FraCandidates.ab
    (Instruction.may .you
      (some (CostSpec.ofItem (.sacrifice (.exact 1) (.filter (.hasType .creature)))))
      (Instruction.createTokensFixed .beast44trample 1))
    "You may sacrifice a creature. If you do, create a 4/4 green Beast creature token with trample",
  FraCandidates.ab (Instruction.dealDamageFixed .allTargets 2)
    "This planeswalker deals 2 damage to up to one target creature or planeswalker and 2 damage to target player"
    (.ofSlots #[{ domain := .creatureOrPlaneswalker, count := .upTo 1 }, .of .anyPlayer]),
  FraCandidates.ab (Instruction.createTokensFixed .leviathan88hexproof 1)
    "Create an 8/8 blue Leviathan creature token with hexproof",
]

def staticAbilities : Thunk (Array StaticAbility) := Thunk.mk fun _ => #[
  .otherCreaturesHaveTrample #[.orc, .goblin],
  .enchantedCreatureGets 3 3,
  .otherCreaturesGet #[.elf] 1 1,
  .equippedCreatureGets 2 0,
  .powerToughnessEqualLandsYouControl,
  .cantBlockUnlessYouControl #[.goblin, .orc],
  .cantBlock,
  .cantBeBlockedByTokens,
  .powerEqualCreaturesYouControl,
  .otherCreaturesGet #[] 1 1,
  .cantAttackUnlessYouControlNOther 2 .wolf,
  .equippedCreatureGetsAndHas 1 0 #[Keyword.menace],
  .enchantedCreatureGetsAndHas 2 2 #[Keyword.flying],
  .equippedCreatureGetsAndWard 2 2 1,
  .creaturesWithPlusOneHave #[Keyword.menace],
  .creaturesYouControlGet 1 1,
  .hasteIfYouControlOtherSubtype .goblin,
  .equippedCreatureGetsAndHas 1 1 #[Keyword.reach],
  .getsAndHasIfEnduringStory 1 0 #[Keyword.vigilance],
  .getsAndHasIfEnduringStory 1 0 #[Keyword.haste],
  .doesntUntapUnlessEnduringStory,
  .creaturesYouControlGetIfEnduringStory 1 1,
  .artifactsAndCreaturesHaveWardIfEnduringStory 1,
  .creaturesCantAttackYouUnlessPayIfEnduringStory 1,
  .thresholdGets 1 1,
  .cantBeBlockedByPowerAtMost 2,
  .equipAbilitiesTargetingThisCostLess 2,
  .equippedCreatureHasKeywordsAndCantBeBlocked #[Keyword.hexproof],
  .firstEquipFreeIfEnduringStory,
  .lifelinkIfYouControlOtherSubtype .dwarf,
  .instantSorceryCostReductionEqualEquippedPower,
  .chosenTypeCreaturesGet 2 2,
  .extraTriggerIfEnduringStorySubtype .dwarf,
  .enchantedLosesAbilitiesDoesntUntap,
  .exileOppDeathCreateWolf,
  .powerPerFatGraveyard 2,
  .equippedCreatureGetsAndHas 2 2 #[Keyword.trample],
  .copyActivatedFromGySubtype .elf,
  .equippedTriggersAgain,
  .equippedCreatureHasKeywords #[Keyword.prowess],
  .enchantedIsOnlySubtypeCantAttackOrBlock .spirit,
  .powerEqualCardsInHand,
  .cantBeBlockedExceptBy 3,
  .armiesYouControlHaveTrample,
  .legendaryCreaturesGetAndWard 2 1 1,
  .nonlegendaryCreaturesGet 1 1,
  .equippedCreatureHasKeywords #[Keyword.indestructible],
  .equippedCreaturesHaveKeywordsDuringYourTurn #[Keyword.firstStrike, Keyword.vigilance],
  .otherSubtypeHaveTapAddOneOf #[.elf] #[.colored .green, .colored .blue],
  .otherSubtypeGetPowerPerArtifactToken .dwarf,
  .cantBeBlockedByPowerAtLeast 3,
  .equippedHexproofUnblockableDuringYourTurn,
  .extraTriggerAnotherYouControl #[.wolf] #[.battle],
  .equippedFirstStrikePlusPerInstantSorcery,
  .equippedGetsTrampleAndCombatTreasures 1 1,
  .opponentsCantCastOnYourTurn,
  .preventAllDamageToThis,
  .creaturesYouControlOfSubtypeGet .hero 2 2,
  .youAndOtherSubtypeHaveHexproofIfShield .hero,
  .flashIfOpponentCastThisTurn,
  .attackingTokensHave #[Keyword.firstStrike],
  .enchantedCreatureGetsHasAndTypes 2 2
    #[Keyword.firstStrike, Keyword.vigilance] #[.soldier],
  .otherCreaturesGet #[.merfolk] 1 1,
  .equippedCreatureGetsHasAndWard 1 1 #[Keyword.flying] 1,
  .enchantedLosesAbilitiesCantUntap,
  .noncreatureSpellsHaveImprovise,
  .hexproofIfPlusOneThisTurn,
  .extraDrawOnConnive,
  .noMaximumHandSize,
  .powerEqualSubtypeYouControl .merfolk,
  .enchantedCreatureHasWard 2,
  .typeSpellsCostLess .artifact 1,
  .supertypeSpellsCostLess .legendary 1,
  .cantBeBlockedIfPowerAtMost 1,
  .subtypeSpellsCostLess .villain 1,
  .indestructibleIfArtifactCreatureOrPlan,
  .opponentsCreaturesGet (-1) (-1),
  .noncombatDamagePlusSourcePower,
  .equippedDealsDoubleDamage,
  .mayBeginOnBattlefield,
  .instantSorceryCostLessEqualPower,
  .enchantedCreatureGetsAndHas 1 0 #[Keyword.haste],
  .extraPowerUpActivation,
  .extraCounterOnPermanents,
  .mayPlayLandsFromGraveyard,
  .activateCreaturesAsThoughHaste,
  .enchantedCreatureGetsHasAndWard 4 4 #[Keyword.trample] 1,
  .creaturesWithPlusOneHave #[Keyword.trample],
  .getsAndAllTypesIfGyCreatureCards 2 2 2,
  .attacksEachCombatIfAble,
  .flyingIfPlusOneThisTurn,
  .otherPowerUpCostsLess 3,
  .getsPowerPerOtherArtifact 1,
  .getsIfGyCreatureCards 2 2 1,
  .entersWithXPlusOne,
  .flyingCantAttackYouOrBlockYours,
  .getsPowerPerAttachedEquipment 2,
  .healOtherDamageWhenDealt,
  .equippedCreatureGetsAndHas 0 8 #[Keyword.vigilance],
  .equippedCreatureGetsAndHas 2 1 #[Keyword.flying],
  .powerEqualLegendaryCreaturesYouControl,
  .maximumHandSize 10,
  .planeswalkersSurviveZeroLoyalty,
  .enteringArtifactsCreaturesDontTrigger,
  .instantSorcerySplitSecond,
  .ptEqualGraveyardCardTypes,
  .artifactTokensBecomeDragons,
  .smallCreaturesYouControlUnblockable,
  .toughnessAssignsCombatDamage,
  .negativePowerAssignsAsPositive,
  .castFromHandFreeUpToCreatures,
  .attackDespiteDefenderIfScried,
  .powerPerSevenInGraveyard,
  .creaturesYouControlHave #[Keyword.trample],
  .firstStrikeDuringYourTurn,
  .equippedGetsAndAttackChooseKeyword,
  .enchantArtifactOrNonAuraEnchantment,
  .enchantCreatureYouControl,
  .enchantedIsConstruct55,
  .enchantedCreatureGetsAndHas 1 0 #[Keyword.deathtouch],
  .vigilanceIfPlaneswalkerSubtype .jace,
  .powerAndFlyingIfSevenInGraveyard,
  .creaturesWithPlusOneHave #[Keyword.vigilance],
  .flyingHasteIfOpponentDealtNoncombat,
  .equippedGetsFlyingAndAttackGainLife,
  .entersTappedChooseColor,
  .creaturesAttackDespiteDefender,
  .creatureTokensGetAndHave 1 0 #[Keyword.vigilance],
  .opponentsNoncreatureSpellsCostMore 1,
  .planeswalkersAttackedByOneAtMost,
  .extraPlusOneCounter,
  .noSpellsOrAbilitiesDuringCombat,
  .noncreatureSpellsCostLess 1,
  .costsLessIfCastNoncreature 2,
  .exileOpponentsDyingCreatures,
  .powerPerCreatureAndPlaneswalkerCard,
  .otherPlusOneCreaturesHave #[Keyword.haste],
  .creaturesYouControlHave #[Keyword.haste],
  .noncombatDamagePlusOne,
  .powerEqualsBasicLandTypes,
  .otherCreaturesHaveTrample #[],
  .landsHaveHexproof,
  .hexproofUntilCombatDamage,
  .subtypeYouControlHave .thopter #[Keyword.haste],
  .artifactCreaturesHaveVigilance,
  .doesntUntap,
  .asEntersChooseNonlandCardName,
  .chosenNameSpellsCantBeCast,
  .creaturesYouControlGetAndHave 2 2 #[Keyword.flying],
]

def triggeredAbilities : Thunk (Array TriggeredAbility) := Thunk.mk fun _ => #[
  .onAttackPumpByGreatestPower,
  .onTheRingTemptsYouDraw 1,
  .onChooseRingBearerDraw,
  .onEnterDraw 1,
  .onEnterGainLife 1,
  .onDiesDealDamageEqualToPowerToOppCreature,
  .onBecomesBlockedDeal1ToBlockers,
  .onEnterScry 2,
  .onEnterSearchForest,
  .onAnotherElfYouControlEntersGets1,
  .onEnterMayDiscardDraw 2,
  .onEnterTargetOpponentSacrificesCreature,
  .onLandYouControlEntersPlusOnePlusOne,
  (.onLandYouControlEntersGets 1 1),
  .onEnterDealDividedDamage 3 3,
  .onEnterOrAttackDealDividedDamage 3 3,
  .onEnterOrAttackReturnElfGainLife,
  .onAttackWithElvesScry 1,
  .onScryPumpSelfForEachLookedAt,
  .onCastInstantOrSorceryDealDamageToEachOpponent 2,
  .onAttackSetOtherBasePT,
  .onAttackScry 1,
  .onAttackFerociousGainLife 2,
  .onAttackOtherGets2AndTrample,
  .onAttackPumpForEachOtherCreature,
  .onDrawSecondPlusOne,
  .onDrawPlusOne,
  .onCombatDamageToPlayerLoot,
  .onDiesOppCreatureGets (-1) (-1),
  .onOneOrMoreOtherCreaturesDieScry 1,
  .onEnterExileOppGyCardOppsLoseLife 2,
  .onEnterEachOpponentDiscards,
  .onEnterUntapOtherPlusOneIfSubtype "Bear",
  .onAttackFerociousSourceGets 2 2,
  .onAttackFerociousSourceGetsAndTeamTrample 1,
  .onAttackFerociousPlusOneEach,
  .onYourBeginCombatFerociousPlusOne,
  .onYouAttackFerociousDrawLoseLife,
  .onEnterPlusOneOnCreature,
  .onEnterRecruit,
  .onDiesRecruit,
  .onEnterCreateTokens .treasure 1 true,
  .onEnterCreateTokens .treasure 1,
  .onEnterExileTop,
  .onCastNoncreatureAmassGoblins 1,
  .onDiesAmassGoblins 4,
  .onEnterAmassGoblins 1,
  .onYouAttackAmassGoblins 2,
  .onEnterOrAttackRecruit,
  .onArtifactYouControlEntersDraw,
  .onYourUpkeepCreateTokens .wolf 1,
  .onEnterCreateThenAttach .dwarf,
  .onEnterAmassThenAttach 1,
  .onEnterAttachToSubtype "Dwarf",
  .onYourEndStepDraw,
  .onAttackTargetGainsKeywords #[Keyword.firstStrike],
  .onEnterSearchBasicToHand,
  .onEnterDealDamageDestroyIfSubtype 1 "Dragon",
  .onAttackDamageEqualTreasures,
  .onYourUpkeepCreateTokens .treasure 1,
  .onOpponentCastsFirstNoncreatureRecruit,
  .onThisOrNontokenSubtypeEntersCreateTokens "Dwarf" .dwarf 1,
  .onEnterGainLifeSearchBasicOnTop 2,
  .onLandYouControlEntersCreateTokens .elf 1,
  .onYourFirstMainAddMana #[.colored .red, .colored .red],
  .onEnterAttachTargetEquipment,
  .onBecomesTargetDraw,
  .onYouAttackRecruit,
  .onLandYouControlEntersTapOrUntap,
  .onLandYouControlEntersBecomePT 4 2,
  .onEnterReturnOtherPlusOne,
  .onAnotherSubtypeOrEquipmentEntersDrawOnce "Dwarf",
  .onEnterLookAtTopRevealTypes 4 #["Dwarf", "Equipment"],
  .onEnterCreateTappedTreasuresEqualOppArtifacts,
  .onCastWithTreasureDrawLoseLife,
  .onEnterCreateAxe,
  .onCastNoncreaturePumpAndDamageOpponents 1,
  .onEnterReturnCreatureFromGyToHand,
  .onCreatureCardLeavesYourGyAmassGoblins 1,
  .onEnterDestroyOtherAmassControllerPower,
  .onThisOrAnotherSubtypeEntersDiscardHand "Dwarf",
  .onDrawSecondPlusOneLifelink,
  .onCombatDamageWolfPlusOneOrTreasure,
  .onTokenYouControlEntersBelladonna,
  .onYourBeginCombatTrampleCounterBecomeBear,
  .onEnterOrAttackPlusOneOnCreature,
  .onAttackCastFromGyArtifactInstantSorcery,
  .onEnterBolgMaySacrifice,
  .onEnterLookAtTopRevealTypes 4 #["permanent"],
  .onEnterMillThenSubtypeToHand 4 "Elf",
  .onEnterExileOppNonlandEachUntilLeaves,
  .onLandYouControlEntersCreateTokens .bear 1,
  .onCastCreaturePlusOneEqualMv,
  .onAttackWithTotalPowerUntapExtraCombat 12,
  .onEnterOrAttackHoneEachEquipment,
  .onEnterCreateAxeAttach,
  .onAttackEquippedGainDoubleStrike,
  .onActivateCreatureAbilityDrawOnce,
  .onEnterTapEnchantedRemoveCounters,
  .onDiesRevealTopPutRandomCreature 13,
  .onOpponentDrawsSecondCreateTreasure,
  .onOpponentCastsChosenParityModes,
  .onYourBeginCombatIfDrawnTwoPumpFirstStrike,
  .onMountainEntersQuestThenDragon,
  .onDrawSecondMillPlayer 3,
  .onEquippedCombatDamageTreasuresPerChosenType,
  .onNontokenYouControlDiesRevealCreature,
  .onAttackMaySacAnotherPlusOneEqualPower,
  .onDiesAmassGoblinsEqualPower,
  .onEnterLootLandEntersTapped,
  .onLandYouControlEntersPayReturnFromGy,
  .onEnterHonePerOppCreaturesAttach,
  .onEnterOrAttackCreateWall,
  .onPutCountersOnGoblinOrcArmyDamageOpp,
  .onAnotherGoblinOrcArmyDiesExileTop,
  .onPlayerLosesLifeMillThatMany,
  .onDiesDrawPerFatGraveyard,
  .onEnterIfNotTokenCopySelf,
  .onEnterMaySacDrawTreasure,
  .onYouSacrificeTokenOppLosesLife,
  .onEnterAttachEquipmentThenFight,
  .onLandYouControlEntersPlusOneVigilance,
  .onAnotherLegendarySubtypeEntersLoot "Elf",
  .onDiesReturnAsArtifact,
  .onCastNoncreatureMayDrawXDiscard2,
  .onAnotherCreatureYouControlPowerAtMostEntersMayPayDraw 2 1,
  .onEnterMayExileAnotherCreature,
  .onLeaveReturnExiled,
  .onEnterDrawThenBottomIfNoLegendary,
  .onAttackWithTwoOrMoreGrantFlying,
  .onEnterTargetGets 2 0,
  .onEnterCreaturesYouControlGetAndFirstStrike 1,
  .onEnterExileOppNonlandUntilLeaves,
  .onYourEndStepRemoveHopeDrawSac,
  .onDiesDraw 1,
  .onAttackTapHumansDraw,
  .onAttackMayExileDefenderUntilLeaves,
  .onScryPumpAndUnblockableOnce,
  .onEnterEachPlayerSacrificesCreature,
  .onYouAttackDraw,
  .onEnterOrAttackAmassGoblins 3,
  .onEnterCreateTokens .food 3,
  .onEnterAttachToLegendary,
  .onPlayerCastsSecondSpellLoseLifeCreateTreasure,
  .onEnterDestroyOppArtifactsEnchantmentsGainLife,
  .onAttackDamageEqualSubtypeToEachOpponent "Dwarf",
  .onEnterOrAttackPlusOneEachOtherGainLife,
  .onEachEndStepDrawIfGainedLife 3,
  .onAttackDefenderSacsLeastPower,
  .onCastGreenOrForestEntersPlusOne,
  .onEnterGainControlOppUntilEot,
  .onEachCombatOthersGetAndOppsGet #["Goblin", "Orc"] 2 2 (-1) (-1),
  .onThisOrAnotherSubtypeEntersCreateTokens "Dwarf" .treasure 1,
  .onCombatDamagePutNonlandMvAtMost 3,
  .onEquippedAttacksCreateSpirits,
  .onEquippedAttacksPlusOneEachIfCityBlessing,
  .onCastColorCreateTokens .white .humanSoldier 1,
  .onCastColorScry .blue 2,
  .onCastColorDamageOpponent .red 3,
  .onCastColorPump .green 4 4,
  .onEquippedAttacksAloneDrawLoseLife,
  .onCombatDamageCreateTreasuresEqualPlayerArtifacts,
  .onAnotherSubtypeEntersPlusOneOnSource "Wolf" 2,
  .onAnotherCreatureYouControlEntersAlliance,
  .onYourBeginCombatCastInstantSorceryFromHand,
  .onEnterExileLandsThenReturnTapped,
  .onLandYouControlEntersDrawPlusOneSource,
  .onEquippedCombatDamageCastInstantSorcery,
  .onCombatDamageImpulseInstantSorcery,
  .onEnterOrOpponentDrawsDeal1AmassOrcs,
  .onYourEndStepPalantir,
  .onCastSecondSpellMillThenCopy,
  .onOpponentCastsAmassOrcs 1,
  .onArmyCombatDamageRingTempts,
  .onRingTemptsMayDiscardDraw 4,
  .onDealtNoncombatDamageCreateTreasures,
  .onEnterIfCastProtectionEverything,
  .onYourUpkeepLoseLifePerBurden,
  .onSubtypeYouControlCombatDamageCreateTokens "Dwarf" .treasure 2,
  .onFinalSagaChapterRevealSaga,
  .onCombatDamageToYouSacRingTempts,
  .onWatch Effect.watchSheHulkRedirectOnce,
  .onCasting Effect.castingPlusOneEachOther,
  .onWatch Effect.watchHulk,
  .onCombatMayPutArtifactAttachEquipment,
  .onCombatDamageDraw 1,
  .onCreatureYouControlAttacksAloneInvestigate,
  .onTappedForTeamworkPlusOneAndDraw,
  .onCreatureYouControlAttacksAlonePump 1 1,
  .onEachEndStepDrawIfAttackedOrEnteredSubtype "Hero",
  .onAttackOthersOfSubtypeGetEqualToughness "Hero",
  .onCasting Effect.castingPlusOneScry,
  .onEnterDrawGainLifeIfAnotherHero,
  .onResource Effect.resourcePlusOneOnHeroesCreateWall,
  .onThisAttack Effect.thisAttackAttacksAlonePlus2Indestructible,
  .onStep Effect.stepHarnessedFlicker,
  .onCasting Effect.castingPlusOneThis,
  .onEnter Effect.enterReturnGyPermanentThisTurn,
  .onEnterCreateTokens .soldier11white 2,
  .onCreatureYouControlEntersScryAndPlan 1,
  .onFourthPlanDrawPlusOneEach,
  .onCasting Effect.castingTapCreatureOrLand,
  .onEnter (Effect.enterDestroy .oppCreatureDealtDamageThisTurn),
  .onEnter Effect.enterOppCreatesTheVoid,
  .onWatch Effect.watchEquippedAttacksAloneUntapScry,
  .onEnterExileOppTappedUntilLeaves,
  .onWatch Effect.watchEnchantedAttachEquipment,
  .onEnter Effect.enterPlusOnesOrReturnArtEnch,
  .onEnterConnive,
  .onWatch Effect.watchMerfolkAttackDraw,
  .onEnter Effect.enterCreateRedwing,
  .onEnterAttachToCreatureYouControl,
  .onEnterEnchanted Instruction.tap,
  .onEnterTapOrUntapNonland,
  .onEnter Effect.enterReturnNonlandNontoken,
  .onWatch Effect.watchJusticeBounce,
  .onCombatTargetYouControlConnives,
  .onWatch Effect.watchYouTargetDrawOnce,
  .onWatch Effect.watchTokensEnterMayDraw,
  .onCasting Effect.castingDrawPowerEqualHand,
  .onCasting Effect.castingMerfolkFromBlue,
  .onCreaturesYouControlBecomeTappedLootAndPlan,
  .onFourthPlanReturnInstants,
  .onEnterExileOtherCopyEnchanted,
  .onEnterCreateTokens .soldier11white 1,
  .onEnterExileCreatureReturnEndStep,
  .onStep Effect.stepEnchantedControllerDraws,
  .onEnterAttachThen Instruction.untap,
  .onCasting Effect.castingExileFlicker,
  .onEnter Effect.enterTapLoseAbilitiesWhileSource,
  .onDiesCreateTokens .villain21menace 1,
  .onYouCastColorFromHandConnive .black,
  .onWatch Effect.watchVillainConniveOnce,
  .onWatch Effect.watchCombatDamageExileUntilNonland,
  .onYouDrawSecondCreateVillainAndPlan,
  .onSeventhPlanControlOpponent,
  .onWatch Effect.watchVillainPlusOneDamageOnce,
  .onEnterCreateTokens .doombot 2,
  .onYourEndStepDrawLoseLife,
  .onVillainYouControlEntersDrainAndPlan 1,
  .onFifthPlanExileTopCast,
  .onThisAttack Effect.thisAttackPayReturnAttacking,
  .onEnterTargetOpponentDiscards 2,
  .onWatch Effect.watchAttacksAloneDrain,
  .onEnterVillainIfGyElseMill,
  .onEnter Effect.enterRevealDiscardFromHand,
  .onYouDrawSecondCreateTokens .villain21menace,
  .onResource Effect.resourceDiscardExilePlay,
  .onCreatureCardsToGyDrawLoseLifeAndPlan,
  .onThirdPlanCreateRobots,
  .onResource Effect.resourceSecondDrawPlusOneTarget,
  .onEnterAttachThen (fun o => Instruction.grantKeywords o #[Keyword.indestructible]),
  .onWatch Effect.watchVillainAttachEquipment,
  .onEquippedCreatureYouControlAttacksConnive,
  .onDeath Effect.deathVillainReturnAsHero,
  .onThisAttack Effect.thisAttackEquippedDrain,
  .onWatch Effect.watchVillainPlusOneLifelink,
  .onCastNoncreatureTreasureAndPlan,
  .onFourthPlanDividedDamage,
  .onCasting Effect.castingCopyIfArtifactOrLand,
  .onWatch Effect.watchHawkeyeModes,
  .onWatch Effect.watchEquippedTappedDamage,
  .onResource Effect.resourceDrawIfAnotherHeroDamage,
  .onWatch Effect.watchVillainOrArtifactDamage,
  .onCasting Effect.castingIronFistTap,
  .onEnterMaySacArtifactOrDiscardDraw,
  .onAnotherArtifactEntersPlusOne,
  .onEnter (Effect.enterDealDamageUpToOne 4),
  .onWatch Effect.watchRedHulk,
  .onCasting Effect.castingMayPayHasteUnblockable,
  .onEnterEnchanted (fun o => Instruction.grantKeywords o #[Keyword.firstStrike]),
  .onEnter Effect.enterExileGyPlayUntilNextTurn,
  .onCasting Effect.castingDamageEqualMv,
  .onEnterCreateFoodOrTreasure,
  .onLandYouControlEntersPlusOneAndPlan,
  .onFourthPlanIndestructible,
  .onDeath Effect.deathHellcatReturn,
  .onEnterCreateTokens .food 1,
  .onResource Effect.resourceGainLifePlusOnes,
  .onWatch Effect.watchHulklingCompare,
  .onEnter Effect.enterCreateZabu,
  .onResource Effect.resourcePlusOneOnThisOnce,
  .onStep Effect.stepHydeChoose,
  .onLandYouControlEntersCreateTokens .moloid 1,
  .onWatch Effect.watchHeroesDamagePlusTwo,
  .onGainLifePlusOne,
  .onCombatPlusOneOnCreatureYouControl,
  .onEnterOrAttack Effect.enterOrAttackCreateSquirrel,
  .onEnterPlusOneOrTwoIfAnotherHero,
  .onStep Effect.stepCopyAbsorbingMan,
  .onCombatCreateAlienPerInvasion,
  .onThisAttack Effect.thisAttackMayPayPlusOne,
  .onResource Effect.resourcePlusOneCreateInsectOnce,
  .onDeath Effect.deathAttackingReturnHand,
  .onWatch Effect.watchNontokenHeroModal,
  .onWatch Effect.watchAttacksAloneFirstStrikeMenace,
  .onEnter Effect.enterMaySacOrDiscardNonlandThenDamage,
  .onWatch Effect.watchFirstTapUntap,
  .onEnter Effect.enterRevealHandExileUntilLeaves,
  .onYouAttacking Effect.youAttackingExileTopHeroPump,
  .onThisAttack Effect.thisAttackIfArtifactEnteredDraw,
  .onAttackConnive,
  .onResource Effect.resourceSecondDrawDrain,
  .onEnter Effect.enterMaySacAnotherThenDestroyOppNonland,
  .onWatch Effect.watchAnyPlayerSecondDraw,
  .onYouAttacking Effect.youAttackingPay2LifeToughness,
  .onCasting Effect.castingVillainToken,
  .onThisAttack Effect.thisAttackBlinkNontoken,
  .onEquipmentYouControlEntersDraw,
  .onResource Effect.resourceSecondDrawBecome66,
  .onArtifactYouControlEntersDrawOnce,
  .onEnter Effect.enterChooseUpToXModes,
  .onDeath Effect.deathDeathtouchOppSac,
  .onWatch Effect.watchSpeedballTargeted,
  .onEnter Effect.enterMayTapThenGrantIndestructible,
  .onEnter Effect.enterTapOppCantUntapWhileControl,
  .onCasting Effect.castingTargetsGainFlying,
  .onStep Effect.stepCopyTaskmaster,
  .onEnter Effect.enterCreateSturdyShieldAttach,
  .onCombatAnotherGetsSourcePower,
  .onEnter Effect.enterFightUpToOne,
  .onEnterSurveil 2,
  .onWatch Effect.watchEquippedAttacksTap,
  .onYouAttacking Effect.youAttackingLookSixCast,
  .onEnterDrawMayPutLandTapped,
  .onEnterOrAttack Effect.enterOrAttackCopyKeywords,
  .onStep Effect.stepDrawToTen,
  .onWatch Effect.watchUltronCopy,
  .onCasting Effect.castingVisionModes,
  .onThisAttack Effect.thisAttackDrawIfPower4,
  SharedTrigger.toTriggeredAbility (.empowerJace 1) (pattern? := some .thisEnters),
  TriggeredAbility.mkTrigger (.gainLife .you) { body := Instruction.putPlusOne .this 2 },
  SharedTrigger.toTriggeredAbility (.empowerJace 2) (pattern? := some .landYouControlEnters),
  .onStep (Effect.ofTrigger .prepareSource),
  .onStep (Effect.ofTrigger (.prepareSource .ifThreeCreaturesDied)),
  SharedTrigger.toTriggeredAbility .drawIfRemovedTwoLoyalty (pattern? := some (.youActivateLoyaltyAbility 2)),
  TriggeredAbility.mkTrigger (.youActivateLoyaltyAbility 0) (Effect.triggerCreateTokens .cadet 1),
  SharedTrigger.toTriggeredAbility (.empowerJace 1) (pattern? := some .youCastFirstNoncreature),
  TriggeredAbility.mkTrigger .youCastNoncreature (Effect.triggerCreateTokens .sculpture 1),
  SharedTrigger.toTriggeredAbility (.plusOneEachYouControl (.subtype .angel)) (pattern? := some (.gainLife .you)),
  TriggeredAbility.mkTrigger .youCastTargetingOpponentOrTheirCreature { body := Instruction.putPlusOne .this 1 },
  SharedTrigger.toTriggeredAbility (.gainLife 1) (pattern? := some .landYouControlEnters),
  TriggeredAbility.mkTrigger (.subtypeYouControlEnters .plains)
    { targeting := .of .creature, body := Instruction.putPlusOne (.target 0) 1 },
  SharedTrigger.toTriggeredAbility .loyaltyOnSource (pattern? := some (.gainLife .you)),
  SharedTrigger.toTriggeredAbility (.grantThenCounterByType #[Keyword.hexproof]) (pattern? := some .thisEnters),
  SharedTrigger.toTriggeredAbility (.grantThenCounterByType #[Keyword.deathtouch]) (pattern? := some .thisEnters),
  SharedTrigger.toTriggeredAbility .destroyOppPermanentIfSixLands (pattern? := some .thisEnters),
  .onStep (Effect.ofTrigger .pumpOrCounterIfScried),
  TriggeredAbility.mkTrigger .stepEachUpkeep (Effect.triggerCreateTokens .forestTentacle 1),
  SharedTrigger.toTriggeredAbility (.draw 1) (pattern? := some .stepEachOpponentDrawStep),
  SharedTrigger.toTriggeredAbility (.creaturesYouControlGet 1 0) (pattern? := some .youCastNoncreature),
  SharedTrigger.toTriggeredAbility .putSourceCountersOnTarget (pattern? := some .thisDies),
  SharedTrigger.toTriggeredAbility .chargeCounterOnSource (pattern? := some .creatureYouControlDies),
  .onStep (Effect.ofTrigger .addGreenPerChargeCounter),
  SharedTrigger.toTriggeredAbility (.mayPayGenericDraw 2 (plusOneOnSource := true)) (pattern? := some .youScryOrSurveil),
  TriggeredAbility.mkTrigger .youScryOrSurveil { body := Instruction.pumpFixed .this 1 1 },
  SharedTrigger.toTriggeredAbility (.creaturesYouControlGet 1 0) (pattern? := some .youScryOrSurveil) (limit? := some .onceEachTurn),
  SharedTrigger.toTriggeredAbility .drawTwoWinIfEmptyShuffleSource (pattern? := some .opponentsDealtCombatDamageYourTurn)
    (word? := some .when) (grouping? := some .oncePerBatch),
  SharedTrigger.toTriggeredAbility .pumpIfFiveOtherForests (pattern? := some .forestYouControlEnters),
  .onStep (Effect.ofTrigger .surveilReturnIfGainedLife),
  TriggeredAbility.ofPattern .thisCast "When you cast this spell, untap all lands you control."
    (Instruction.untap (.inZones .battlefield (.all #[.hasType .land, .controlledBy .you])))
    (activeZones := #[.stack]),
  TriggeredAbility.ofPattern .youCastCreature
    "Whenever you cast a creature spell, exile up to one other target creature you control, then return that card to the battlefield under its owner's control."
    (Instruction.exile (.target 0) { delayedReturn? := some (.immediately false .owner) })
    (.single { domain := .anotherCreatureYouControl, count := .upTo 1 })
    (allowsZeroTargets := true),
  TriggeredAbility.ofPattern .stepYourBeginCombat
    "At the beginning of combat on your turn, you may remove a +1/+1 counter from this creature. If you do, put a +1/+1 counter on each other creature you control."
    (Instruction.may .you (some (CostSpec.ofItem (.removeCounters (.exact 1) (some .plusOnePlusOne) .self)))
      (Instruction.putPlusOne (.inZones .battlefield (.all #[.otherThan .this, .hasType .creature, .controlledBy .you])) 1)),
  TriggeredAbility.ofPattern .thisAttacks
    "Whenever this creature attacks, empower Jace X, where X is the number of creatures you control."
    (Instruction.empower .jace (.aggregate .count .one (.inZones .battlefield (.all #[.hasType .creature, .controlledBy .you])))),
  TriggeredAbility.ofPattern .thisEnters "When this Aura enters, tap enchanted creature. It becomes unprepared."
    (.seq #[Instruction.tap .attachedHost, .permanent (.setDesignation .attachedHost .prepared false)]),
  TriggeredAbility.ofPattern .thisEnters
    "When this enchantment enters, the owner of up to one other target nonland permanent puts it on their choice of the top or bottom of their library."
    (.moveZone (.target 0) (.library .owner .top true) .put)
    (.single {
      domain := .object .battlefield (.all #[.otherThan .this, .not (.hasType .land)])
      count := .upTo 1 })
    (allowsZeroTargets := true),
  TriggeredAbility.ofPattern .thisEnters
    "When this creature enters, draw two cards, then discard two cards. When you discard one or more nonland cards this way, tap up to that many target creatures and put a stun counter on each of them."
    (.seq #[
      Instruction.drawFixed 2,
      .bind ⟨0⟩ (Instruction.discardFixed 2)
        (Instruction.ifThen (.exists (.filter (.stepObjects ⟨0⟩) (.not (.hasType .land))))
          (.queueReflexiveTrigger {
            word := .when
            pattern := .discard .you (.not (.hasType .land))
            effect := {
              targeting := .of (.single { domain := .creature, count := .upTo 2 })
              allowsZeroTargets := true
              body := Instruction.tapAndStun .allTargets
              phrase := "Tap up to that many target creatures and put a stun counter on each of them" } }))]),
  TriggeredAbility.ofPattern .thisAttacks "Whenever this creature attacks, draw a card, then discard a card."
    (.seq #[Instruction.drawFixed 1, Instruction.discardFixed 1]),
  TriggeredAbility.ofPattern .thisDies "When this creature dies, if it isn't a token, create a token that's a copy of it."
    (.create (.tokens .you (.const 1) (.copyOf .this #[])))
    (interveningIf? := some TriggeredAbility.condSourceNotToken),
  TriggeredAbility.ofPattern (.or .thisEnters .thisDies) "When this creature enters or dies, you gain 2 life."
    (Instruction.gainLifeFixed 2),
  TriggeredAbility.ofPattern .thisEnters "When this creature enters, mill three cards."
    (Instruction.millFixed 3),
  TriggeredAbility.ofPattern .stepYourBeginCombat
    "At the beginning of combat on your turn, if two or more creatures died this turn, return this card from your graveyard to the battlefield."
    (.moveZone .this (.battlefield .controller) .put)
    (interveningIf? := some (TriggeredAbility.condCreaturesDiedThisTurn 2))
    (activeZones := #[.graveyard]),
  TriggeredAbility.ofPattern .thisEnters
    "When this Equipment enters, you may pay {2}. When you do, for each opponent, destroy up to one target creature or planeswalker that player controls."
    (Instruction.may .you (some (CostSpec.ofGeneric 2))
      (.queueReflexiveTrigger {
        word := .when
        pattern := .thisEnters
        effect := {
          targeting := .of (.forEachOpponentControlled (.any #[.hasType .creature, .hasType .planeswalker]) (.upTo 1))
          allowsZeroTargets := true
          body := Instruction.destroy .allTargets
          phrase := "For each opponent, destroy up to one target creature or planeswalker that player controls" } })),
  TriggeredAbility.ofPattern .thisEnters "When this creature enters, target creature gets +2/+2 and gains deathtouch until end of turn."
    (.seq #[Instruction.pumpFixed (.target 0) 2 2, Instruction.grantKeywords (.target 0) #[Keyword.deathtouch]])
    .creature,
  TriggeredAbility.ofPattern .thisAttacks "Whenever this creature attacks, it deals 1 damage to each opponent and you gain 1 life."
    (.seq #[Instruction.dealDamageFixed (.players .opponents) 1, Instruction.gainLifeFixed 1]),
  TriggeredAbility.ofPattern .thisEnters "When this enchantment enters, it deals X damage to any target."
    (Instruction.dealDamage (.targetSlot 0) .chosenX) .anyTarget,
  TriggeredAbility.ofPattern .youCastNoncreature "Whenever you cast a noncreature spell, put a +1/+1 counter on this creature."
    (Instruction.putPlusOne .this 1),
  TriggeredAbility.ofPattern .stepEachUpkeep
    "At the beginning of each upkeep, if an opponent was dealt noncombat damage last turn, return this card from your graveyard to your hand."
    (Instruction.bounce .this)
    (interveningIf? := some TriggeredAbility.condOpponentDealtNoncombatDamageLastTurn)
    (activeZones := #[.graveyard]),
  TriggeredAbility.ofPattern .thisEnters
    "When this creature enters, creatures you control gain trample and get +X/+0 until end of turn, where X is the number of artifacts you control."
    (.seq #[
      Instruction.pump (.inZones .battlefield (.all #[.hasType .creature, .controlledBy .you]))
        (.aggregate .count .one (.inZones .battlefield (.all #[.hasType .artifact, .controlledBy .you]))) (.const 0),
      Instruction.grantKeywords (.inZones .battlefield (.all #[.hasType .creature, .controlledBy .you])) #[Keyword.trample]]),
  TriggeredAbility.ofPattern .thisEnters
    "When this creature enters, search your library for a card, put it into your hand, shuffle, then discard a card at random."
    (.seq #[
      .player (.searchLibrary {
        zones := .libraryOf .you
        filter := .anyObject
        count := .upTo (.const 1)
        dest := .hand .controller
        reveal := false
        shuffle := true }),
      Instruction.discardFixed 1 .you true]),
  TriggeredAbility.ofPattern .thisEnters "When this creature enters, create a 2/2 colorless Wizard Soldier creature token named Cadet."
    (Instruction.createTokensFixed .cadet 1),
  TriggeredAbility.ofPattern .opponentsDealtNoncombatDamage
    "Whenever one or more opponents are dealt noncombat damage, creatures you control get +1/+0 until end of turn."
    (Instruction.pumpFixed (.inZones .battlefield (.all #[.hasType .creature, .controlledBy .you])) 1 0)
    (grouping := .oncePerBatch),
  TriggeredAbility.ofPattern .thisEnters
    "When this creature enters, target instant or sorcery card in your graveyard gains flashback until end of turn. The flashback cost is equal to its mana cost."
    (.stack (.mayCastOrPlay (.target 0) { duration := .untilEndOfTurn, landsAllowed := false, asFlashback := true }))
    (.ofDomain (.object .yourGraveyard (.all #[.any #[.hasType .instant, .hasType .sorcery], .isKind .card]))),
  TriggeredAbility.ofPattern .thisEnters "When this creature enters, you may discard a card. When you do, this creature deals 2 damage to any target."
    (Instruction.may .you (some CostSpec.discardCard)
      (.queueReflexiveTrigger {
        word := .when
        pattern := .discard .you .anyObject
        effect := {
          targeting := .of .anyTarget
          body := Instruction.dealDamageFixed (.targetSlot 0) 2
          phrase := "This creature deals 2 damage to any target" } })),
  TriggeredAbility.ofPattern .thisDealsCombatDamageToPlayer
    "Whenever this creature deals combat damage to a player, return target land card from your graveyard to your hand."
    (Instruction.bounce (.target 0))
    (.ofDomain (.object .yourGraveyard (.all #[.hasType .land, .isKind .card]))),
  TriggeredAbility.ofPattern .anotherCreatureYouControlEnters "Whenever another creature you control enters, you gain 1 life."
    (Instruction.gainLifeFixed 1),
  TriggeredAbility.ofPattern .thisDealtDamage
    "Whenever this creature is dealt damage, you may search your library for up to that many land cards, put them onto the battlefield tapped, then shuffle."
    (Instruction.may .you none
      (.player (.searchLibrary {
        zones := .libraryOf .you
        filter := .hasType .land
        count := .upTo .eventAmount
        dest := .battlefield .controller
        mods := { tapped := true }
        reveal := false
        shuffle := true })))
    (grouping := .oncePerBatch),
  TriggeredAbility.ofPattern .thisEnters "When this creature enters, create a Heartwood token."
    (Instruction.createTokensFixed .heartwood 1),
  TriggeredAbility.ofPattern .youPutLoyaltyCounters
    "Whenever you put one or more loyalty counters on a planeswalker, put a +1/+1 counter on this creature."
    (Instruction.putPlusOne .this 1) (grouping := .oncePerBatch),
  TriggeredAbility.ofPattern .thisEnters
    "When this creature enters, you may search your library for a basic land card, put that card onto the battlefield tapped, then shuffle."
    (Instruction.may .you none
      (.player (.searchLibrary {
        zones := .libraryOf .you
        filter := .all #[.hasSupertype .basic, .hasType .land]
        count := .upTo (.const 1)
        dest := .battlefield .controller
        mods := { tapped := true }
        reveal := false
        shuffle := true }))),
  TriggeredAbility.ofPattern .thisEnters "When this creature enters, put three +1/+1 counters on target creature."
    (Instruction.putPlusOne (.target 0) 3) .creature,
  TriggeredAbility.ofPattern (.or .thisEnters .thisDies) "When this creature enters or dies, create a Heartwood token."
    (Instruction.createTokensFixed .heartwood 1),
  TriggeredAbility.ofPattern (.gainLife .you) "Whenever you gain life, draw a card. This ability triggers only once each turn."
    (Instruction.drawFixed 1) (limit := .onceEachTurn),
  TriggeredAbility.ofPattern .youScryOrSurveil "Whenever you scry or surveil, put a +1/+1 counter on each creature you control."
    (Instruction.putPlusOne (.inZones .battlefield (.all #[.hasType .creature, .controlledBy .you])) 1),
  TriggeredAbility.ofPattern .enchantedDies
    "When enchanted creature dies, return that card to the battlefield tapped under its owner's control."
    (.moveZone .triggerSubject (.battlefield .owner) .put { tapped := true }),
  TriggeredAbility.ofPattern .stepEachEndStep "At the beginning of the end step, sacrifice this creature."
    (Instruction.sacrifice .this),
  TriggeredAbility.ofPattern .creatureYouControlAttacks
    "Whenever a creature you control attacks, that creature deals 1 damage to each opponent."
    (Instruction.dealDamageFixed (.players .opponents) 1 .triggerSubject),
  TriggeredAbility.ofPattern (.gainLife .you)
    "Whenever you gain life, create a colorless artifact token named Lotus with \"{T}, Sacrifice this token: Add three mana of any one color.\" This ability triggers only once each turn."
    (Instruction.createTokensFixed .lotus 1) (limit := .onceEachTurn),
  TriggeredAbility.ofPattern .thisEnters "When this creature enters, it fights up to one target creature an opponent controls."
    (.damage (.fight .this (.target 0) false))
    (.single { domain := .oppCreature, count := .upTo 1 })
    (allowsZeroTargets := true),
  TriggeredAbility.ofPattern .thisEnters
    "When this creature enters, if you cast it, target opponent reveals their hand. You choose a nonland card from it. Exile that card."
    (.seq #[
      .player (.reveal (.target 0) (.inZones (.handOf (.target 0)) .anyObject)),
      .moveZone (.inZones (.handOf (.target 0)) (.not (.hasType .land))) .exile .exile
        { exileUntilSourceLeaves := true
          choice? := some { chooser := .controller, count := .exact (.const 1), revealFirst := true } }])
    .opponent (interveningIf? := some TriggeredAbility.condSourceWasCast),
  TriggeredAbility.ofPattern .thisEnters
    "When this creature enters, mill four cards. When you do, return target land card from your graveyard to the battlefield tapped."
    (.seq #[
      Instruction.millFixed 4,
      .queueReflexiveTrigger {
        word := .when
        pattern := .thisEnters
        effect := {
          targeting := .of (.ofDomain (.object .yourGraveyard (.all #[.hasType .land, .isKind .card])))
          body := .moveZone (.target 0) (.battlefield .controller) .put { tapped := true }
          phrase := "Return target land card from your graveyard to the battlefield tapped" } }]),
  TriggeredAbility.ofPattern .thisOrAnotherCreatureYouControlEnters
    "Whenever this creature or another creature you control enters, surveil 1." (Instruction.surveilFixed 1),
  TriggeredAbility.ofPattern (.opponentCastsSpellMvAtMost 2)
    "Whenever an opponent casts a spell with mana value 2 or less, you gain 2 life." (Instruction.gainLifeFixed 2),
  TriggeredAbility.ofPattern .thisEnters
    "When this artifact enters, exile target nonland permanent an opponent controls with mana value 3 or less until this artifact leaves the battlefield."
    (Instruction.exile (.target 0) { exileUntilSourceLeaves := true })
    (.ofDomain (.object .battlefield (.all #[.not (.hasType .land), .controlledBy .opponent, .stat .manaValue .le (.const 3)]))),
  TriggeredAbility.ofPattern .thisEnters
    "When this creature enters, you may sacrifice a land. If you do, create two tapped Heartwood tokens."
    (Instruction.may .you (some (CostSpec.ofItem (.sacrifice (.exact 1) (.filter (.hasType .land)))))
      (Instruction.createTokensFixed .heartwood 2 .you true)),
  TriggeredAbility.ofPattern .thisEnters
    "When this creature enters, if you cast him, exile up to one target nonland card of each card type from your graveyard. Copy those cards. You may cast any number of spells with total mana value 6 or less from among the copies without paying their mana costs."
    (.moveZone .allTargets .exile .exile {
      grantPlayPerm? := some {
        duration := .untilEndOfTurn
        landsAllowed := false
        freeCast := true
        copyAndCast := true
        maxTotalManaValue? := some (.const 6) } })
    (.single {
      domain := .object .yourGraveyard (.all #[.not (.hasType .land), .isKind .card])
      count := .upTo 8
      groupConstraint? := some .distinctCardTypes })
    (allowsZeroTargets := true) (maxTargets := 8) (interveningIf? := some TriggeredAbility.condSourceWasCast),
  TriggeredAbility.ofPattern .thisEnters "When this Equipment enters, it deals 3 damage to any target and you gain 3 life."
    (.seq #[Instruction.dealDamageFixed (.targetSlot 0) 3, Instruction.gainLifeFixed 3]) .anyTarget,
  TriggeredAbility.ofPattern .thisAttacks "Whenever this creature attacks, exile up to one target card from a graveyard."
    (Instruction.exile (.target 0))
    (.single { domain := .object .anyGraveyard .isCard, count := .upTo 1 })
    (allowsZeroTargets := true),
  TriggeredAbility.ofPattern .youCastPreparedSpell
    "Whenever you cast a prepared spell, copy it. You may choose new targets for the copy."
    (.stack (.copyStackObject .triggerSubject (.const 1) true)),
  TriggeredAbility.ofPattern .thisEnters "When this artifact enters, draw a card, then discard a card."
    (.seq #[Instruction.drawFixed 1, Instruction.discardFixed 1]),
  TriggeredAbility.ofPattern .stepYourUpkeep
    "At the beginning of your upkeep, surveil 1. Then if there are seven or more cards in your graveyard, sacrifice this artifact, it deals 2 damage to each opponent, and you gain 2 life."
    (.seq #[
      Instruction.surveilFixed 1,
      Instruction.ifThen (.cmp .ge (.playerMetric .graveyardSize .you) (.const 7))
        (.seq #[
          Instruction.sacrifice .this,
          Instruction.dealDamageFixed (.players .opponents) 2,
          Instruction.gainLifeFixed 2])]),
  TriggeredAbility.ofPattern .youCastEquipmentOrTargetingCreatureYouControl
    "Whenever you cast an Equipment spell or a spell that targets a creature you control, draw a card. This ability triggers only once each turn."
    (Instruction.drawFixed 1) (limit := .onceEachTurn),
  TriggeredAbility.ofPattern .anotherCreatureOrPlaneswalkerYouControlEnters
    "Whenever another creature or planeswalker you control enters, you gain 1 life." (Instruction.gainLifeFixed 1),
  TriggeredAbility.ofPattern .youScryOrSurveil
    "Whenever you scry or surveil, create a 1/1 colorless Thopter artifact creature token with flying. This ability triggers only once each turn."
    (Instruction.createTokensFixed .thopter 1) (limit := .onceEachTurn),
  TriggeredAbility.ofPattern (.gainLife .you) "Whenever you gain life, put a loyalty counter on each planeswalker you control."
    (Instruction.putCounters (.inZones .battlefield (.all #[.hasType .planeswalker, .controlledBy .you])) .loyalty (.const 1)),
  TriggeredAbility.ofPattern .creatureYouControlAttacksPlayerAlone
    "Whenever a creature you control attacks a player alone, it gains double strike until end of turn."
    (Instruction.grantKeywords .triggerSubject #[Keyword.doubleStrike]),
  TriggeredAbility.ofPattern .anotherNontokenCreatureYouControlEnters
    "Whenever another nontoken creature you control enters, untap this creature." (Instruction.untap .this),
  TriggeredAbility.ofPattern .thisEnters
    "When this creature enters, for each opponent, tap up to one target creature that player controls. Put a stun counter on each of those creatures."
    (Instruction.tapAndStun .allTargets) (.forEachOpponentControlled (.hasType .creature) (.upTo 1))
    (allowsZeroTargets := true),
  TriggeredAbility.ofPattern .stepEachEndStep
    "At the beginning of each end step, if you've drawn three or more cards this turn, create a 3/3 blue Angel creature token with flying."
    (Instruction.createTokensFixed .angel33blue 1) (interveningIf? := some (TriggeredAbility.condDrawnAtLeast 3)),
  TriggeredAbility.ofPattern .creatureOpponentControlsEnters
    "Whenever a creature an opponent controls enters, this creature deals 1 damage to that player."
    (Instruction.dealDamageFixed (.players (.controllerOf .triggerSubject)) 1),
  TriggeredAbility.ofPattern .opponentActivatesLoyaltyAbility
    "Whenever an opponent activates a loyalty ability, this creature deals 1 damage to that player."
    (Instruction.dealDamageFixed (.players (.controllerOf .triggerSubject)) 1),
  TriggeredAbility.ofPattern .anotherCreatureOrPlaneswalkerYouControlEnters
    "Whenever another creature or planeswalker you control enters, mill two cards." (Instruction.millFixed 2),
  TriggeredAbility.ofPattern .thisEnters "When this creature enters, remove up to three counters from another target creature or planeswalker."
    (.permanent (.modifyCounters (.remove none (.upTo (.const 3))) (.target 0)))
    (.ofDomain (.object .battlefield (.all #[.otherThan .this, .any #[.hasType .creature, .hasType .planeswalker]]))),
  TriggeredAbility.ofPattern .anotherCreatureOrPlaneswalkerYouControlDies
    "Whenever another creature or planeswalker you control dies, this creature deals 1 damage to target opponent and you gain 1 life."
    (.seq #[Instruction.dealDamageFixed (.targetSlot 0) 1, Instruction.gainLifeFixed 1]) .opponent,
  TriggeredAbility.ofPattern (.damageDealt .anyObject (.player .opponent) (noncombatOnly := true))
    "Whenever an opponent is dealt noncombat damage, put a +1/+1 counter on this creature."
    (Instruction.putPlusOne .this 1) (grouping := .perPlayerInBatch),
  TriggeredAbility.ofPattern (.discard .any .anyObject)
    "Whenever a player discards one or more cards, this creature deals 1 damage to each opponent."
    (Instruction.dealDamageFixed (.players .opponents) 1) (grouping := .perPlayerInBatch),
  TriggeredAbility.ofPattern .creatureYouControlDies
    "Whenever a creature you control dies, put a loyalty counter on each planeswalker you control."
    (Instruction.putCounters (.inZones .battlefield (.all #[.hasType .planeswalker, .controlledBy .you])) .loyalty (.const 1)),
  TriggeredAbility.ofPattern .thisEnters
    "When this creature enters, you may sacrifice a creature or planeswalker. When you do, each opponent sacrifices a creature of their choice."
    (Instruction.may .you
      (some (CostSpec.ofItem (.sacrifice (.exact 1) (.filter (.any #[.hasType .creature, .hasType .planeswalker])))))
      (.forEach (.eachPlayer .opponent) ⟨0⟩
        (.moveZone
          (.inZones .battlefield (.all #[.hasType .creature, .controlledBy (PlayerFilter.ofExpr (.stepPlayers ⟨0⟩))]))
          .graveyard .sacrifice
          { choice? := some { chooser := .player (.stepPlayers ⟨0⟩), count := .exact (.const 1) } }))),
  TriggeredAbility.ofPattern .anotherCreatureYouControlEnters
    "Whenever another creature you control enters, this creature gets +X/+0 until end of turn, where X is that creature's power."
    (Instruction.pump .this (.objectStat .power .triggerSubject) (.const 0)),
  TriggeredAbility.ofPattern .creatureYouControlAttacksPlayerAlone
    "Whenever a creature you control attacks a player alone, discard a card, then draw a card. Then put a +1/+1 counter on that creature for each card you've discarded this turn."
    (.seq #[
      Instruction.discardFixed 1,
      Instruction.drawFixed 1,
      Instruction.putCounters .triggerSubject .plusOnePlusOne (.playerMetric .cardsDiscardedThisTurn .you)]),
  TriggeredAbility.ofPattern .thisEnters "When this creature enters, create a 5/5 red Dragon creature token with flying."
    (Instruction.createTokensFixed .dragon55flying 1),
  TriggeredAbility.ofPattern .landYouControlEnters
    "Whenever a land you control enters, this creature deals 1 damage to each opponent. If that land is a Mountain, add {R}."
    (.seq #[
      Instruction.dealDamageFixed (.players .opponents) 1,
      Instruction.ifThen (.exists (.filter .triggerSubject (.hasSubtype (.literal .mountain))))
        (Instruction.addSimpleMana #[.colored .red])]),
  TriggeredAbility.ofPattern .thisEnters "When this creature enters, create a 1/1 colorless Thopter artifact creature token with flying."
    (Instruction.createTokensFixed .thopter 1),
  TriggeredAbility.ofPattern .opponentSmallCreatureBlocks
    "Whenever a creature an opponent controls with power or toughness 1 or less blocks, this creature deals 1 damage to that creature's controller."
    (Instruction.dealDamageFixed (.players (.controllerOf .triggerSubject)) 1),
  TriggeredAbility.ofPattern .stepYourEndStep
    "At the beginning of your end step, if you didn't cast a spell this turn, put two +1/+1 counters on this creature."
    (Instruction.putPlusOne .this 2) (interveningIf? := some TriggeredAbility.condCastNoSpellThisTurn),
  TriggeredAbility.ofPattern .thisEnters
    "When this creature enters, search your library for up to X basic land cards with different names, reveal them, put them into your hand, then shuffle."
    (.player (.searchLibrary {
      zones := .libraryOf .you
      filter := .all #[.hasSupertype .basic, .hasType .land]
      count := .upTo .chosenX
      groupConstraint? := some .distinctNames
      dest := .hand .controller
      reveal := true
      shuffle := true })),
  TriggeredAbility.ofPattern (.creatureYouControlPowerAtLeastEnters 4)
    "Whenever a creature you control with power 4 or greater enters, draw a card." (Instruction.drawFixed 1),
  TriggeredAbility.ofPattern .thisEnters "When this creature enters, create Mowu, a legendary 3/3 green Dog creature token."
    (Instruction.createTokensFixed .mowu 1),
  TriggeredAbility.ofPattern .stepYourEndStep "At the beginning of your end step, untap all tokens you control."
    (Instruction.untap (.inZones .battlefield (.all #[.isToken true, .controlledBy .you]))),
  TriggeredAbility.ofPattern .thisEnters
    "When this creature enters, you may discard a card. If you do, search your library for an enchantment card, reveal it, put it into your hand, then shuffle."
    (Instruction.may .you (some CostSpec.discardCard)
      (.player (.searchLibrary {
        zones := .libraryOf .you
        filter := .hasType .enchantment
        count := .upTo (.const 1)
        dest := .hand .controller
        reveal := true
        shuffle := true }))),
  TriggeredAbility.ofPattern .thisDiscarded "When you discard this card, you gain 3 life." (Instruction.gainLifeFixed 3)
    (activeZones := #[.hand]),
  TriggeredAbility.ofPattern (.youActivateLoyaltyAbility 0)
    "Whenever you activate a loyalty ability, you gain 1 life. You may play an additional land this turn."
    (.seq #[Instruction.gainLifeFixed 1, Instruction.extraLand]),
  TriggeredAbility.ofPattern .thisEnters
    "When this creature enters, another target creature you control fights up to one target creature an opponent controls."
    (.damage (.fight (.target 0) (.target 1) false))
    (.ofSlots #[.of .anotherCreatureYouControl, { domain := .oppCreature, count := .upTo 1 }]),
  TriggeredAbility.ofPattern .anotherCreatureOrPlaneswalkerYouControlDies
    "Whenever another creature or planeswalker you control dies, you gain 1 life." (Instruction.gainLifeFixed 1),
  TriggeredAbility.ofPattern .thisEnters
    "When this creature enters, for each opponent, put X -1/-1 counters on up to one target creature that player controls, where X is the greatest mana value among cards in your graveyard."
    (Instruction.putCounters .allTargets .minusOneMinusOne
      (.aggregate .max (.stat .manaValue) (.inZones .yourGraveyard .isCard)))
    (.forEachOpponentControlled (.hasType .creature) (.upTo 1))
    (allowsZeroTargets := true),
  TriggeredAbility.ofPattern .thisEnters "When this creature enters, draw a card for each color among other artifacts you control."
    (.player (.drawCards .you
      (.colorCountAmong (.inZones .battlefield (.all #[.otherThan .this, .hasType .artifact, .controlledBy .you]))))),
  TriggeredAbility.ofPattern .youAttack
    "Whenever you attack, if you've activated a loyalty ability this turn, untap target attacking creature. It can't be blocked this turn."
    (.seq #[Instruction.untap (.target 0), Instruction.cantBeBlocked (.target 0)])
    .attackingCreature
    (grouping := .oncePerBatch)
    (interveningIf? := some TriggeredAbility.condActivatedLoyaltyThisTurn),
  TriggeredAbility.ofPattern .thisOrAnotherCreatureYouControlEnters
    "Whenever this creature or another creature you control enters, put a +1/+1 counter on target creature that entered this turn."
    (Instruction.putPlusOne (.target 0) 1)
    (.ofDomain (.object .battlefield (.all #[.hasType .creature, .enteredThisTurn]))),
  TriggeredAbility.ofPattern .youCastNoncreature
    "Whenever you cast a noncreature spell, create a 1/1 colorless Thopter artifact creature token with flying."
    (Instruction.createTokensFixed .thopter 1),
  TriggeredAbility.ofPattern .youCastArtifactOrCreature "Whenever you cast an artifact or creature spell, untap this creature."
    (Instruction.untap .this),
  TriggeredAbility.ofPattern (.permanentLeaves (.all #[.hasType .creature, .controlledBy .you]))
    "Whenever a creature you control leaves the battlefield, if it had counters on it, put those counters on this artifact."
    (.permanent (.modifyCounters (.copyFromLki .triggerSubject) .this))
    (interveningIf? := some TriggeredAbility.condTriggerSubjectHadCounters),
  TriggeredAbility.ofPattern .stepYourBeginCombat
    "At the beginning of combat on your turn, if this artifact has counters on it, you may move all counters from this artifact onto target creature."
    (Instruction.may .you none (.permanent (.modifyCounters (.moveAll .this none) (.target 0))))
    .creature (interveningIf? := some TriggeredAbility.condSourceHasCounters),
  TriggeredAbility.ofPattern .thisEnters "When this creature enters, you may pay {3}. If you do, proliferate twice."
    (Instruction.may .you (some (CostSpec.ofGeneric 3)) (.player (.proliferate .you (.const 2)))),
  TriggeredAbility.ofPattern .youProliferate "Whenever you proliferate, draw a card." (Instruction.drawFixed 1),
]

def activatedAbilities : Thunk (Array ActivatedAbility) := Thunk.mk fun _ => #[
  ActivatedAbility.zemoBoastAbility,
  activated (Effect.sourceGets 1 1) (ManaCost.ofGeneric 2)
          (costReductions := #[ActivationCostReduction.ifControlLegendary 2]),
  {
        cost := CostSpec.ofItems #[.mana (ManaCost.ofGeneric 2), .tapSelf, .sacrifice (.exact 1) .self],
        effect := Effect.gainLife 3
      },
  equipAbility (ManaCost.ofGeneric 3),
  activated (Effect.becomeBearCreatureWithLandsPT)
          (ManaCost.ofGenericAndColors 5 [.green, .green]),
  activated (Effect.sourceGets 1 0) (ManaCost.ofGenericAndColor 1 .red),
  activated (Effect.targetCantBeBlockedThisTurn) (ManaCost.ofGeneric 4) (tap := true),
  activated (Effect.sourceGets 1 0) (ManaCost.ofColor .red),
  activated (Effect.putPlusOnePlusOneOnSource 3)
          (ManaCost.ofGenericAndColors 5 [.green, .green]),
  activated (Effect.abilityCreaturesYouControlGet 1 1) (ManaCost.ofGenericAndColor 3 .white),
  activated (Effect.sourceGets 2 2) (payLife := 2) (turnLimit? := some 1),
  activated (Effect.returnFromGraveyardToHand) (ManaCost.ofGeneric 2)
          (sacrificeAnotherCreatureOrArtifact := true)
          (timing := .sorcery) (activeZones := #[.graveyard]),
  activated (Effect.exileTopPlayUntilEndOfNextTurn)
          (sacrificeAnotherCreatureOrArtifact := true)
          (condition? := some .isYourTurn) (turnLimit? := some 1),
  activated (Effect.targetCantBeBlockedThisTurn) (ManaCost.ofGenericAndColor 4 .blue),
  activated (Effect.searchBasicLandTapped) (tap := true) (sacrificeSource := true),
  typecyclingAbility "Halfling" (ManaCost.ofGeneric 4),
  activated (Effect.destroyTargetPermanent) (ManaCost.ofGeneric 7) (tap := true)
          (sacrificeSource := true),
  activated (Effect.returnFromGyAttachPowerAtMost 1)
          (ManaCost.ofGenericAndHybrids 2 .white .blue 2)
          (timing := .sorcery) (activeZones := #[.graveyard]),
  activated (Effect.ownerShuffleSourceDraw 3) (ManaCost.ofGeneric 6),
  activated (Effect.abilityDrawThenDiscard 1) (ManaCost.ofGeneric 2) (tap := true),
  activated (Effect.abilityDraw 1) (ManaCost.ofGeneric 1) (tap := true)
          (discardACard := true),
  activated (Effect.abilityCreateTokens .dwarf 1) (ManaCost.ofGenericAndColor 4 .red)
          (tap := true) (timing := .sorcery) (costReductions := #[ActivationCostReduction.perEquipment 1]),
  activated (Effect.attachToTargetCreatureYouControl) (ManaCost.ofGeneric 2)
          (timing := .sorcery) (tag? := some (.equip none)) (payLife := 2),
  activated (Effect.searchTwoBasicsSplit) (ManaCost.ofGeneric 2)
          (tap := true) (sacrificeSource := true),
  activated (Effect.subtypesGainMenace #["Goblin", "Orc"]) (ManaCost.ofGenericAndColor 1 .black),
  activated (Effect.exileThenReturnNextEnd) (ManaCost.ofGenericAndColors 5 [.blue, .blue]),
  activated (Effect.searchBasicBeholdSubtypeUntap "Elf") (tap := true) (payLife := 1)
          (sacrificeSource := true),
  activated (Effect.twoPlayersDraw) (ManaCost.ofGenericAndColor 2 .white),
  activated (Effect.discardLegendarySameNameDraw) (ManaCost.ofGeneric 1) (tap := true)
          (discardLegendarySameName := true),
  activated (Effect.dealDamageToAny 4) (ManaCost.ofGenericAndColor 2 .red)
          (sacrificeArtifact := true),
  activated (Effect.drawEqualSacrificedPowerThenDiscard) (ManaCost.ofGeneric 1)
          (sacrificeAnotherCreature := true),
  typecyclingAbility "Plains",
  equipAbility (ManaCost.ofGeneric 1) (some .human),
  activated (Effect.destroyTargetArtifactOrEnchantment) (sacrificeSource := true)
          (timing := .sorcery),
  activated (Effect.abilityCreaturesYouControlGet 1 1)
          (ManaCost.ofGenericAndColor 4 .white) (tap := true)
          (costReductions := #[ActivationCostReduction.ifControlLegendary 2]),
  activated (Effect.millPlayer 3) (ManaCost.ofGenericAndColor 5 .blue) (tap := true),
  activated (Effect.returnFromGraveyardTapped) (ManaCost.ofGenericAndColor 2 .black)
          (activeZones := #[.graveyard]) (condition? := some ActivatedAbility.condControlsLegendaryCreature),
  activated (Effect.searchBasicLandTapped) (ManaCost.ofGeneric 2)
          (tap := true) (sacrificeSource := true),
  activated (Effect.dealDamageToTargetCreature 2) (ManaCost.ofGeneric 1)
          (sacrificeSource := true)
          (extraModes := #[Effect.destroyTargetColorlessNonland]),
  activated (Effect.targetCantBeBlockedPowerAtMost 2) (tap := true),
  activated (Effect.abilityScry 2) (ManaCost.ofGenericAndColor 1 .blue) (tap := true)
          (condition? := some ActivatedAbility.condControlsLegendaryCreature),
  activated (Effect.abilityDrawThenDiscard 2) (ManaCost.ofGeneric 3) (tap := true),
  activated (Effect.abilityCreateTokensX .treasure) { symbols := #[.x, .x] }
          (tap := true) (sacrificeSource := true),
  activated (Effect.abilityDraw 1) (ManaCost.ofGenericAndColor 1 .white) (tap := true)
          (condition? := some (ActivatedAbility.condAttackedWithCreaturesAtLeast 2)),
  activated (Effect.abilityCreateTokens .food 1) (ManaCost.ofGenericAndColor 1 .green)
          (tap := true) (tapAnUntappedCreatureYouControl := true),
  activated (Effect.creaturesYouControlGetOppsLoseLife 2 0 2)
          (ManaCost.ofGenericAndColors 1 [.black, .red]),
  activated (Effect.arwenShare) (ManaCost.ofGeneric 1) (removeIndestructibleCounter := true),
  activated (Effect.grantCombatDamageCreateTreasure) (ManaCost.ofGeneric 1) (tap := true),
  activated (Effect.putShadowCounter) (ManaCost.ofGenericAndColor 3 .black) (tap := true),
  activated (Effect.damageEachOpponent 1) (ManaCost.ofGenericAndColors 1 [.black, .red]) (tap := true),
  activated (Effect.chooseTwoDestroyRest) (ManaCost.ofGenericAndColors 5 [.black, .red])
          (tap := true) (sacrificeSource := true) (sacrificeLegendaryArtifact := true)
          (timing := .sorcery),
  activated (Effect.blackGateUnblockable) (ManaCost.ofGenericAndColor 1 .black) (tap := true),
  activated (Effect.burdenThenDraw) (tap := true),
  activated (Effect.teamGain #[Keyword.doubleStrike]) (ManaCost.ofGeneric 10),
  activated (Effect.sourceGainsIndestructibleTap) (discardACard := true),
  activated (Effect.plusOneOnEachOtherSubtype "Hero" 1) (ManaCost.empty) (tap := true),
  typecyclingAbility "Basic land" (ManaCost.ofGeneric 2),
  powerUpAbility (Effect.putPlusOnePlusOneOnSource 2) (ManaCost.ofGenericAndColor 4 .white),
  activated (Effect.plusOneAndIndestructibleCounter) (ManaCost.ofGenericAndColors 5 [.white, .white]) (tag? := some .powerUp),
  activated (Effect.pumpAttackingAloneGainLife) (ManaCost.empty) (tap := true),
  activated (Effect.transform) (ManaCost.ofGenericAndColors 3 [.green, .white, .white]) (timing := .sorcery),
  activated (Effect.harnessInfinityStone) (ManaCost.ofGenericAndColor 5 .white) (tap := true),
  activated (Effect.transform) (ManaCost.ofGenericAndColors 2 [.red, .white, .white]) (timing := .sorcery),
  activated (Effect.lookAtTopPutTypes 7 #["Hero", "Equipment", "Vehicle"]) (ManaCost.ofColors [.white, .blue, .black, .red, .green]) (tag? := some .powerUp),
  activated (Effect.anotherYouControlGetsAndGrant 2 0 #[Keyword.hexproof]) (ManaCost.ofGeneric 2) (tap := true),
  activated (Effect.tapTargetCreature) (ManaCost.ofGeneric 2) (tap := true)
        (costReductions := #[ActivationCostReduction.ifTargetPowerAtMost 1 3]),
  powerUpAbility (Effect.putPlusOnePlusOneOnSource 3) (ManaCost.ofGenericAndColor 5 .blue),
  activated (Effect.plusOneAndDraw 1 2) (ManaCost.ofGenericAndColor 5 .blue) (tag? := some .powerUp),
  activated (Effect.drawX) ({ symbols := #[.x, .x] }) (tap := true) (timing := .sorcery),
  activated (Effect.transform) (ManaCost.ofGenericAndColors 2 [.red, .red, .green, .green]) (timing := .sorcery),
  activated (Effect.copyControlledAbility .creature) (ManaCost.ofGeneric 1) (tap := true),
  equipAbility (ManaCost.ofGenericAndColor 2 .blue),
  activated (Effect.abilityDraw 2) (ManaCost.ofGenericAndColor 3 .blue) (sacrificeSource := true),
  activated (Effect.revealTopDrawIfArtifact) (ManaCost.empty) (tap := true),
  activated (Effect.plusOneAndExtraTurn) (ManaCost.ofGenericAndColors 5 [.blue, .blue, .blue]) (tag? := some .powerUp),
  activated (Effect.copyArtifactYouControlNotLegendary) (ManaCost.ofGeneric 1) (tap := true) (timing := .sorcery),
  activated (Effect.plusOneX) ({ symbols := #[.x, .colored .blue, .colored .blue] }) (tag? := some .powerUp),
  activated (Effect.lookAtTopRevealArtifact 4) (ManaCost.ofGeneric 1) (tap := true),
  activated (Effect.transform) (ManaCost.ofGenericAndColors 4 [.blue, .red]) (timing := .sorcery),
  activated (Effect.createTappedTokens .villain21menace 1) (ManaCost.ofGeneric 3) (tap := true)
        (condition? := some (ActivatedAbility.condGraveyardCreatureCardsAtLeast 2)),
  activated (Effect.abilityDraw 1) (ManaCost.ofGenericAndColor 2 .black)
        (sacrificeArtifactOrCreature := true),
  activated (Effect.searchLandTypeToHand "Plan") (ManaCost.ofGenericAndColor 1 .black)
        (activeZones := #[.hand]) (discardSource := true),
  activated (Effect.connive) (condition? := some .isYourTurn) (payLife := 3),
  activated (Effect.eachOppDiscardThenPlusOne) (ManaCost.ofGenericAndColor 4 .black) (tag? := some .powerUp),
  activated (Effect.returnFromGraveyardToHand) (ManaCost.ofGenericAndColor 2 .black),
  activated (Effect.targetGets (-4) (-4)) (tap := true) (sacrificeEquipmentAttachedToSource := true)
          (timing := .sorcery),
  activated (Effect.abilityCreateTokens .wall04defender 1) (ManaCost.ofGenericAndColor 2 .white),
  activated (Effect.sourceGets 4 4) (ManaCost.ofGenericAndColor 3 .green),
  activated (Effect.dealDamageToTargetCreature 4) (ManaCost.ofGenericAndColor 4 .red),
  activated (Effect.abilityTargetPlayerDraw 4) (ManaCost.ofGenericAndColor 5 .blue),
  activated (Effect.returnGyCreatureThenPlusOne 2) (ManaCost.ofGenericAndColors 5 [.black, .black]) (tag? := some .powerUp),
  powerUpAbility (Effect.putPlusOnePlusOneOnSource 3) (ManaCost.ofGenericAndColor 6 .red),
  activated (Effect.exileTopXPlayThisTurn) (tap := true) (putStunCounterOnSource := true),
  activated (Effect.nextInstantSorceryCopyIfMvAtMostSourcePower) (ManaCost.ofGeneric 1) (tap := true),
  powerUpAbility (Effect.putPlusOnePlusOneOnSource 2) (ManaCost.ofGenericAndColor 4 .red),
  activated (Effect.drawPerDiscardedThisTurn)
        (ManaCost.ofGeneric 2) (tap := true) (discardACard := true),
  equipWorthyAbility (ManaCost.ofGeneric 1),
  activated (Effect.abilityDealDamageToEachCreature 2) (ManaCost.ofGenericAndColor 2 .red)
          (activeZones := #[.hand]) (discardSource := true),
  activated (Effect.plusOneAndDoubleStrikeCounter) (ManaCost.ofGenericAndColor 4 .red) (tag? := some .powerUp),
  activated (Effect.abilityCreateTokens .treasure 1) (ManaCost.ofGeneric 2) (tap := true),
  powerUpAbility (Effect.putPlusOnePlusOneOnSource 2) (ManaCost.ofGenericAndColor 5 .red),
  powerUpAbility (Effect.putPlusOnePlusOneOnSource 2) (ManaCost.ofGenericAndColors 5 [.red, .red]),
  activated (Effect.destroyTargetNoncreatureArtOrEnch)
        (sacrificeSource := true) (timing := .sorcery),
  activated (Effect.plusOneAndGrant #[Keyword.vigilance, Keyword.indestructible, Keyword.haste]) (ManaCost.ofGenericAndColor 4 .green) (tag? := some .powerUp),
  activated (Effect.plusOneAndCreateTokens 1 .hero32vigilance) (ManaCost.ofGenericAndColor 6 .green) (tag? := some .powerUp),
  activated (Effect.proliferateEachKind) (ManaCost.empty) (tap := true) (timing := .sorcery),
  activated (Effect.becomeTypes #["Dinosaur", "Hero"] 3 5 #[Keyword.reach, Keyword.vigilance]) (ManaCost.ofGeneric 3),
  activated (Effect.becomeTypes #["Dinosaur", "Hero"] 6 6 #[Keyword.trample]) (ManaCost.ofGeneric 6),
  activated (Effect.millThenPutSubtypeOrEnchantment 4 "Hero") (ManaCost.ofGeneric 3) (tap := true),
  powerUpAbility (Effect.putPlusOnePlusOneOnSource 2) (ManaCost.ofGenericAndColor 3 .green),
  activated (Effect.destroyUpToOneThenPlusOne) (ManaCost.ofGenericAndColors 4 [.green, .green]) (tag? := some .powerUp),
  activated (Effect.createTokensEqualSubtype .squirrel11green "Squirrel") (ManaCost.ofGenericAndColors 1 [.green, .green, .green]),
  activated (Effect.plusOneAndCreateTigerGod) (ManaCost.ofGenericAndColor 5 .green) (tag? := some .powerUp),
  activated (Effect.plusOneThenFightUpToOne) (ManaCost.ofGenericAndHybrids 5 .red .green 2) (tag? := some .powerUp),
  activated (Effect.createTokensEqualRemovedPlusOnes .insect11green)
        (ManaCost.ofGenericAndColor 2 .green) (tap := true) (removeAnyNumberPlusOne := true),
  activated (Effect.dealDamageToAny 2) (ManaCost.ofGeneric 3)
        (tap := true) (sacrificeArtifactOrDiscardNonland := true),
  powerUpAbility (Effect.putPlusOnePlusOneOnSource 5) (ManaCost.ofGenericAndColors 6 [.red, .green]),
  activated (Effect.transform) (ManaCost.ofGenericAndColors 4 [.white, .blue]) (timing := .sorcery),
  activated (Effect.copyControlledAbility .artifact)
        (turnLimit? := some 1) (condition? := some .isYourTurn) (payLife := 2),
  activated (Effect.plusTwoThenOddEvenDestroy) ({ symbols := #[.colorless, .colored .white, .colored .blue, .colored .black, .colored .red, .colored .green] }) (tag? := some .powerUp),
  activated (Effect.returnFromGyFinalityAttach) (ManaCost.ofGenericAndColors 3 [.white, .black])
        (activeZones := #[.graveyard]),
  activated (Effect.equipmentBecomesConstructHero) (ManaCost.ofGeneric 2),
  activated (Effect.plusOneAndCreateTokens 2 .robotVillain22) (ManaCost.ofGeneric 6) (tag? := some .powerUp),
  powerUpAbility (Effect.putPlusOnePlusOneOnSource 2) (ManaCost.ofGeneric 7),
  activated (Effect.lookAtTopRevealSubtype 3 "Hero") (ManaCost.ofGeneric 4) (tap := true),
  activated (Effect.abilityDraw 1) (ManaCost.ofGeneric 4) (tap := true)
          (condition? := some (ActivatedAbility.condControlsCreatureToughnessAtLeast 4)),
  activated (Effect.abilityCreateTokens .doombot 1) (ManaCost.ofGeneric 3) (tap := true)
          (sacrificeArtifact := true) (timing := .sorcery),
  activated (Effect.targetSubtypeConnives "Villain") (ManaCost.ofGeneric 3) (tap := true) (timing := .sorcery),
  {
      cost := CostSpec.ofItems #[.mana (ManaCost.ofGeneric 2), .sacrifice (.exact 1) .self],
      effect := Effect.abilityDraw 1
    },
  activated (Effect.abilityEmpowerJace 2) (ManaCost.ofGeneric 6),
  activated (Effect.abilityEmpowerJace 2) (ManaCost.ofGenericAndColor 2 .blue) (tap := true),
  activated (Effect.targetCreatureBecomesPrepared) (ManaCost.ofGeneric 4) (tap := true),
  activated (Effect.eachCreatureYouControlBecomesPrepared)
          (ManaCost.ofColors [.white, .blue, .black, .red, .green]) (tap := true),
  activated (Effect.becomeCopyLegendRuleOff) (ManaCost.ofGeneric 5),
  activated (Effect.cantBeBlockedAnotherPowerAtMost 2) (ManaCost.ofGeneric 1) (tap := true),
  activated (Effect.proliferatePlaneswalkerTypesTimes)
          (ManaCost.ofColors [.white, .blue, .black, .red, .green]) (tap := true),
  activated (Effect.returnFromGyWithFinality) (ManaCost.ofColors [.black, .red])
          (activeZones := #[.graveyard]) (condition? := some ActivatedAbility.condOpponentDealtNoncombatDamageThisTurn),
  activated (Effect.tapAndStunTargetCreature) (ManaCost.ofGenericAndColor 3 .blue)
          (timing := .sorcery) (activeZones := #[.graveyard]) (exileSourceFromGraveyard := true),
  activated (Effect.abilityEmpowerJace 2) (ManaCost.ofGeneric 1)
          (activeZones := #[.graveyard]) (exileSourceFromGraveyard := true),
  ActivatedAbility.fra
    "{3}, Exile this card from your hand: Target land gains \"{T}: Add {C}{C}\" until this card is cast from exile. You may cast this card for as long as it remains exiled."
    (FraCandidates.ab
      (.seq #[
        .stack (.mayCastOrPlay .this { duration := .whileInZone .this .exile, landsAllowed := false }),
        .installEffect (.applyContinuous (.whileInZone .this .exile) (.target 0)
          (.grantActivated #[ActivatedAbility.manaAbility (.sequence #[(.colorless, .const 2)]) CostSpec.tapOnly]))])
      "Target land gains \"{T}: Add {C}{C}\" until this card is cast from exile. You may cast this card for as long as it remains exiled"
      .land)
    (CostSpec.ofItems #[.mana (ManaCost.ofGeneric 3), .exile (.exact 1) .yourHand .self false])
    (activeZones := #[.hand]),
  ActivatedAbility.fra "{4}{W}: Creatures you control get +1/+1 until end of turn."
    (FraCandidates.ab
      (Instruction.pumpFixed (.inZones .battlefield (.all #[.hasType .creature, .controlledBy .you])) 1 1)
      "Creatures you control get +1/+1 until end of turn")
    (CostSpec.ofMana ⟨#[.generic 4, .colored .white]⟩),
  ActivatedAbility.fra "{3}{U}{U}, Exile this card from your graveyard: Draw two cards."
    (FraCandidates.ab (Instruction.drawFixed 2) "Draw two cards")
    (CostSpec.ofItems #[.mana ⟨#[.generic 3, .colored .blue, .colored .blue]⟩, .exile (.exact 1) .yourGraveyard .self false])
    (activeZones := #[.graveyard]),
  ActivatedAbility.fra "{3}{U}: Surveil 1." (FraCandidates.ab (Instruction.surveilFixed 1) "Surveil 1")
    (CostSpec.ofMana ⟨#[.generic 3, .colored .blue]⟩),
  ActivatedAbility.fra "{U}, Sacrifice this creature: The next spell you cast this turn can't be countered."
    (FraCandidates.ab
      (.installEffect (.applyRule .untilEndOfTurn (.play (.nextSpellCantBeCountered .you .anyObject))))
      "The next spell you cast this turn can't be countered")
    (CostSpec.ofItems #[.mana ⟨#[.colored .blue]⟩, .sacrifice (.exact 1) .self]),
  ActivatedAbility.fra "{2}: This creature gets +1/-1 until end of turn."
    (FraCandidates.ab (Instruction.pumpFixed .this 1 (-1)) "This creature gets +1/-1 until end of turn")
    (CostSpec.ofGeneric 2),
  ActivatedAbility.fra "{3}{B}, Exile this card from your graveyard: Return another target creature card from your graveyard to your hand."
    (FraCandidates.ab (Instruction.bounce (.target 0)) "Return another target creature card from your graveyard to your hand"
      (.ofDomain (.object .yourGraveyard (.all #[.otherThan .this, .hasType .creature, .isKind .card]))))
    (CostSpec.ofItems #[.mana ⟨#[.generic 3, .colored .black]⟩, .exile (.exact 1) .yourGraveyard .self false])
    (activeZones := #[.graveyard]),
  ActivatedAbility.fra "{T}, Discard a card: Draw a card." (FraCandidates.ab (Instruction.drawFixed 1) "Draw a card")
    (CostSpec.tapOnly.append CostSpec.discardCard),
  ActivatedAbility.fra
    "{3}{R}: Exile target creature or planeswalker you control. Reveal cards from the top of your library until you reveal a creature or planeswalker card. Put that card onto the battlefield and the rest on the bottom of your library in a random order. Activate only as a sorcery."
    (FraCandidates.ab
      (.bind ⟨0⟩
        (Instruction.exile (.target 0))
        (.player (.inspectLibrary {
          source := .revealUntil .you (.any #[.hasType .creature, .hasType .planeswalker]) (.const 1)
          action := .moveAll (.battlefield .controller)
          rest := .bottomRandom })))
      "Exile target creature or planeswalker you control"
      (.ofDomain (.object .battlefield (.all #[.any #[.hasType .creature, .hasType .planeswalker], .controlledBy .you]))))
    (CostSpec.ofMana ⟨#[.generic 3, .colored .red]⟩) (timing := .sorcery),
  ActivatedAbility.fra
    "Sacrifice this creature: Destroy target artifact or enchantment. If that permanent was a legendary enchantment, draw a card. Activate only as a sorcery."
    (FraCandidates.ab
      (.seq #[
        Instruction.destroy (.target 0),
        Instruction.ifThen (.exists (.filter (.target 0) (.all #[.hasSupertype .legendary, .hasType .enchantment])))
          (Instruction.drawFixed 1)])
      "Destroy target artifact or enchantment"
      .artifactOrEnchantment)
    CostSpec.sacSelf (timing := .sorcery),
  ActivatedAbility.fra
    "{1}, Sacrifice another artifact: Put a +1/+1 counter on this creature. It gains your choice of trample, hexproof, or haste until end of turn."
    (FraCandidates.ab
      (.seq #[
        Instruction.putPlusOne .this 1,
        .player (.choose .you (.keyword #[Keyword.trample, Keyword.hexproof, Keyword.haste]))])
      "Put a +1/+1 counter on this creature")
    ((CostSpec.ofGeneric 1).append CostSpec.sacrificeAnotherArtifact),
  ActivatedAbility.fra "{4}{G}: Return this card from your graveyard to your hand."
    (FraCandidates.ab (Instruction.bounce .this) "Return this card from your graveyard to your hand")
    (CostSpec.ofMana ⟨#[.generic 4, .colored .green]⟩) (activeZones := #[.graveyard]),
  ActivatedAbility.fra "{3}{G}, Discard this card: Destroy target creature with flying."
    (FraCandidates.ab (Instruction.destroy (.target 0)) "Destroy target creature with flying"
      .creatureWithFlying)
    (CostSpec.ofItems #[.mana ⟨#[.generic 3, .colored .green]⟩, .discard (.exact 1) .self])
    (activeZones := #[.hand]),
  ActivatedAbility.fra "{6}{G}{G}: This creature gets +4/+4 and gains trample until end of turn."
    (FraCandidates.ab (Instruction.pumpAndTrample .this 4 4) "This creature gets +4/+4 and gains trample until end of turn")
    (CostSpec.ofMana ⟨#[.generic 6, .colored .green, .colored .green]⟩),
  ActivatedAbility.fra
    "{6}: Create a Heartwood token. Then this creature gets +X/+0 until end of turn, where X is the number of artifacts you control."
    (FraCandidates.ab
      (.seq #[
        Instruction.createTokensFixed .heartwood 1,
        Instruction.pump .this
          (.aggregate .count .one (.inZones .battlefield (.all #[.hasType .artifact, .controlledBy .you]))) (.const 0)])
      "Create a Heartwood token")
    (CostSpec.ofGeneric 6),
  ActivatedAbility.fra "{2}{W/B}: Return this card from your graveyard to your hand."
    (FraCandidates.ab (Instruction.bounce .this) "Return this card from your graveyard to your hand")
    (CostSpec.ofMana ⟨#[.generic 2, .hybrid .white .black]⟩) (activeZones := #[.graveyard]),
  ActivatedAbility.fra "{4}{G}{W}: Target creature gains trample and lifelink until end of turn."
    (FraCandidates.ab (Instruction.grantKeywords (.target 0) #[Keyword.trample, Keyword.lifelink])
      "Target creature gains trample and lifelink until end of turn" .creature)
    (CostSpec.ofMana ⟨#[.generic 4, .colored .green, .colored .white]⟩),
  ActivatedAbility.fra
    "{4}: Create a 2/2 colorless Wizard Soldier creature token named Cadet. Then creatures you control gain haste until end of turn."
    (FraCandidates.ab
      (.seq #[
        Instruction.createTokensFixed .cadet 1,
        Instruction.grantKeywords (.inZones .battlefield (.all #[.hasType .creature, .controlledBy .you])) #[Keyword.haste]])
      "Create a Cadet")
    (CostSpec.ofGeneric 4),
  ActivatedAbility.fra "{2}: Put target card from your graveyard on the bottom of your library."
    (FraCandidates.ab (.moveZone (.target 0) (.library .owner .bottom false) .put)
      "Put target card from your graveyard on the bottom of your library"
      (.ofDomain (.object .yourGraveyard .isCard)))
    (CostSpec.ofGeneric 2),
  ActivatedAbility.fra
    "{W}{U}: Return this card from your graveyard to the battlefield with a finality counter on it. Activate only if you've scried or surveilled this turn."
    (FraCandidates.ab
      (.moveZone .this (.battlefield .controller) .put { enterCounters := #[(.finality, .const 1)] })
      "Return this card from your graveyard to the battlefield with a finality counter on it")
    (CostSpec.ofMana ⟨#[.colored .white, .colored .blue]⟩) (activeZones := #[.graveyard])
    (condition? := some ActivatedAbility.condScriedOrSurveilledThisTurn),
  ActivatedAbility.fra "{1}, {T}, Discard a legendary card: Draw a card." (FraCandidates.ab (Instruction.drawFixed 1) "Draw a card")
    ((CostSpec.ofItems #[.mana (ManaCost.ofGeneric 1), .tapSelf]).append CostSpec.discardLegendaryCard),
  ActivatedAbility.fra "Tap two untapped artifacts you control: Put two +1/+1 counters on this creature."
    (FraCandidates.ab (Instruction.putPlusOne .this 2) "Put two +1/+1 counters on this creature")
    CostSpec.tapTwoUntappedArtifacts,
  ActivatedAbility.fra
    "Equip {3}. This ability costs {1} less to activate for each +1/+1 counter on the creature it targets."
    Effect.attachToTargetCreatureYouControl (CostSpec.ofGeneric 3) (timing := .sorcery)
    (tag? := some (.equip none))
    (costReductions := #[ActivationCostReduction.perPlusOneOnTarget]),
  ActivatedAbility.fra "{2}: This creature gains flying until end of turn."
    (FraCandidates.ab (Instruction.grantKeywords .this #[Keyword.flying]) "This creature gains flying until end of turn")
    (CostSpec.ofGeneric 2),
  ActivatedAbility.fra "{5}, {T}, Exile this artifact: Destroy all creatures. Activate only as a sorcery."
    (FraCandidates.ab (Instruction.destroy (.inZones .battlefield (.hasType .creature))) "Destroy all creatures")
    (CostSpec.ofItems #[.mana (ManaCost.ofGeneric 5), .tapSelf, .exile (.exact 1) .battlefield .self false])
    (timing := .sorcery),
  ActivatedAbility.fra
    "{6}, Sacrifice this creature: Choose target creature or planeswalker an opponent controls. Its owner shuffles it into their library."
    (FraCandidates.ab
      (.moveZone (.target 0) (.library .owner .shuffledIn false) .shuffleIntoLibrary { shuffleAfter := true })
      "Its owner shuffles it into their library"
      .oppCreatureOrPlaneswalker)
    ((CostSpec.ofGeneric 6).append CostSpec.sacSelf),
  ActivatedAbility.fra "{2}, {T}, Discard a card: Draw a card." (FraCandidates.ab (Instruction.drawFixed 1) "Draw a card")
    ((CostSpec.ofItems #[.mana (ManaCost.ofGeneric 2), .tapSelf]).append CostSpec.discardCard),
  ActivatedAbility.fra
    "{2}, {T}: Target creature that attacked this turn becomes prepared. Activate only as a sorcery."
    (FraCandidates.ab (Instruction.becomePrepared (.target 0)) "Target creature that attacked this turn becomes prepared"
      (.ofDomain (.object .battlefield (.all #[.hasType .creature, .attackedThisTurn]))))
    (CostSpec.ofItems #[.mana (ManaCost.ofGeneric 2), .tapSelf]) (timing := .sorcery),
  ActivatedAbility.fra "{1}{W}, Discard this card: It deals 4 damage to target attacking or blocking creature."
    (FraCandidates.ab (Instruction.dealDamageFixed (.targetSlot 0) 4) "It deals 4 damage to target attacking or blocking creature"
      .attackingOrBlockingCreature)
    (CostSpec.ofItems #[.mana ⟨#[.generic 1, .colored .white]⟩, .discard (.exact 1) .self])
    (activeZones := #[.hand]),
  ActivatedAbility.fra
    "{1}, {T}, Discard a card: Another target creature or planeswalker you control gains hexproof until end of turn."
    (FraCandidates.ab (Instruction.grantKeywords (.target 0) #[Keyword.hexproof])
      "Another target creature or planeswalker you control gains hexproof until end of turn"
      (.ofDomain (.object .battlefield (.all #[
        .otherThan .this, .any #[.hasType .creature, .hasType .planeswalker], .controlledBy .you]))))
    ((CostSpec.ofItems #[.mana (ManaCost.ofGeneric 1), .tapSelf]).append CostSpec.discardCard),
  ActivatedAbility.fra "{T}: Return another target permanent you control to its owner's hand. Activate only during your turn."
    (FraCandidates.ab (Instruction.bounce (.target 0)) "Return another target permanent you control to its owner's hand"
      (.ofDomain (.object .battlefield (.all #[.otherThan .this, .controlledBy .you]))))
    CostSpec.tapOnly (condition? := some .isYourTurn),
  ActivatedAbility.fra "{T}: Target creature with a +1/+1 counter on it gains flying until end of turn."
    (FraCandidates.ab (Instruction.grantKeywords (.target 0) #[Keyword.flying])
      "Target creature with a +1/+1 counter on it gains flying until end of turn"
      (.ofDomain (.object .battlefield (.all #[.hasType .creature, .counterCount (some .plusOnePlusOne) .ge (.const 1)]))))
    CostSpec.tapOnly,
  ActivatedAbility.fra "{6}: Put a +1/+1 counter on target legendary creature."
    (FraCandidates.ab (Instruction.putPlusOne (.target 0) 1) "Put a +1/+1 counter on target legendary creature"
      (.ofDomain (.object .battlefield (.all #[.hasSupertype .legendary, .hasType .creature]))))
    (CostSpec.ofGeneric 6),
  ActivatedAbility.fra "{6}: Put a +1/+1 counter on target nonlegendary creature."
    (FraCandidates.ab (Instruction.putPlusOne (.target 0) 1) "Put a +1/+1 counter on target nonlegendary creature"
      (.ofDomain (.object .battlefield (.all #[.not (.hasSupertype .legendary), .hasType .creature]))))
    (CostSpec.ofGeneric 6),
  ActivatedAbility.fra "{T}: Draw a card, then discard a card."
    (FraCandidates.ab (.seq #[Instruction.drawFixed 1, Instruction.discardFixed 1]) "Draw a card, then discard a card")
    CostSpec.tapOnly,
  ActivatedAbility.fra "{2}{U}: Untap target creature."
    (FraCandidates.ab (Instruction.untap (.target 0)) "Untap target creature" .creature)
    (CostSpec.ofMana ⟨#[.generic 2, .colored .blue]⟩),
  ActivatedAbility.fra
    "{3}{U}{U}: Until end of turn, whenever this creature deals combat damage to a player, draw two cards."
    (FraCandidates.ab
      (.installEffect (.applyContinuous .untilEndOfTurn .this
        (.grantTriggered #[TriggeredAbility.ofPattern .thisDealsCombatDamageToPlayer
          "Whenever this creature deals combat damage to a player, draw two cards." (Instruction.drawFixed 2)])))
      "Until end of turn, whenever this creature deals combat damage to a player, draw two cards")
    (CostSpec.ofMana ⟨#[.generic 3, .colored .blue, .colored .blue]⟩),
  ActivatedAbility.fra
    "{4}{B}, Exile another creature card from your graveyard: Return this card from your graveyard to the battlefield tapped with a +1/+1 counter on her."
    (FraCandidates.ab
      (.moveZone .this (.battlefield .controller) .put { tapped := true, enterCounters := #[(.plusOnePlusOne, .const 1)] })
      "Return this card from your graveyard to the battlefield tapped")
    ((CostSpec.ofMana ⟨#[.generic 4, .colored .black]⟩).append CostSpec.exileAnotherCreatureCardFromGraveyard)
    (activeZones := #[.graveyard]),
  ActivatedAbility.fra
    "{5}{B}: Return target creature or planeswalker card from your graveyard to the battlefield. Put a +1/+1 counter on this creature. Activate only as a sorcery."
    (FraCandidates.ab
      (.seq #[.moveZone (.target 0) (.battlefield .controller) .put, Instruction.putPlusOne .this 1])
      "Return target creature or planeswalker card from your graveyard to the battlefield"
      (.ofDomain (.object .yourGraveyard (.all #[.any #[.hasType .creature, .hasType .planeswalker], .isKind .card]))))
    (CostSpec.ofMana ⟨#[.generic 5, .colored .black]⟩) (timing := .sorcery) (tag? := some .exhaust),
  ActivatedAbility.fra
    "Sacrifice another creature or planeswalker: This creature gets -2/-0 until end of turn. Activate only if there are seven or more cards in your graveyard."
    (FraCandidates.ab (Instruction.pumpFixed .this (-2) 0) "This creature gets -2/-0 until end of turn")
    CostSpec.sacrificeAnotherCreatureOrPlaneswalker
    (condition? := some (ActivatedAbility.condGraveyardCardsAtLeast 7)),
  ActivatedAbility.fra "{B}, Discard this card: Target creature gets -3/-1 until end of turn."
    (FraCandidates.ab (Instruction.pumpFixed (.target 0) (-3) (-1)) "Target creature gets -3/-1 until end of turn" .creature)
    (CostSpec.ofItems #[.mana ⟨#[.colored .black]⟩, .discard (.exact 1) .self])
    (activeZones := #[.hand]),
  ActivatedAbility.fra "{1}{R}, {T}: Put a +1/+1 counter on target creature that entered this turn."
    (FraCandidates.ab (Instruction.putPlusOne (.target 0) 1) "Put a +1/+1 counter on target creature that entered this turn"
      (.ofDomain (.object .battlefield (.all #[.hasType .creature, .enteredThisTurn]))))
    (CostSpec.ofItems #[.mana ⟨#[.generic 1, .colored .red]⟩, .tapSelf]),
  ActivatedAbility.fra "{8}: Create a 5/5 red Dragon creature token with flying."
    (FraCandidates.ab (Instruction.createTokensFixed .dragon55flying 1) "Create a 5/5 red Dragon creature token with flying")
    (CostSpec.ofGeneric 8),
  ActivatedAbility.fra "{2}, {T}, Sacrifice an artifact or land: Draw a card." (FraCandidates.ab (Instruction.drawFixed 1) "Draw a card")
    ((CostSpec.ofItems #[.mana (ManaCost.ofGeneric 2), .tapSelf]).append CostSpec.sacrificeArtifactOrLand),
  ActivatedAbility.fra
    "{5}{R}: Target creature gets +X/+0 until end of turn, where X is the number of artifacts you control."
    (FraCandidates.ab
      (Instruction.pump (.target 0)
        (.aggregate .count .one (.inZones .battlefield (.all #[.hasType .artifact, .controlledBy .you]))) (.const 0))
      "Target creature gets +X/+0 until end of turn" .creature)
    (CostSpec.ofMana ⟨#[.generic 5, .colored .red]⟩),
  ActivatedAbility.fra "{4}{G}: Put a +1/+1 counter on each creature you control with a +1/+1 counter on it."
    (FraCandidates.ab
      (Instruction.putPlusOne
        (.inZones .battlefield (.all #[.hasType .creature, .controlledBy .you, .counterCount (some .plusOnePlusOne) .ge (.const 1)])) 1)
      "Put a +1/+1 counter on each creature you control with a +1/+1 counter on it")
    (CostSpec.ofMana ⟨#[.generic 4, .colored .green]⟩),
  ActivatedAbility.fra "{2}: Return target land card from your graveyard to your hand."
    (FraCandidates.ab (Instruction.bounce (.target 0)) "Return target land card from your graveyard to your hand"
      (.ofDomain (.object .yourGraveyard (.all #[.hasType .land, .isKind .card]))))
    (CostSpec.ofGeneric 2),
  ActivatedAbility.fra
    "{2}, Sacrifice another creature or planeswalker: Put a +1/+1 counter on this creature. He gains menace until end of turn."
    (FraCandidates.ab (.seq #[Instruction.putPlusOne .this 1, Instruction.grantKeywords .this #[Keyword.menace]])
      "Put a +1/+1 counter on this creature")
    ((CostSpec.ofGeneric 2).append CostSpec.sacrificeAnotherCreatureOrPlaneswalker),
]

def chapterEffects : Thunk (Array (String × Effect)) := Thunk.mk fun _ => #[
  ("This Saga deals 6 damage to target creature an opponent controls.", Effect.chapterDealDamageToOppCreature 6),
  ("Destroy target artifact an opponent controls.", Effect.chapterDestroyOppArtifact),
  ("Add {R}.", Effect.chapterAddMana (.colored .red)),
  ("Search your library for a basic land card, reveal it, put it into your hand, then shuffle.", Effect.chapterSearchBasicLandToHand),
  ("This Saga gains \"Landfall — Whenever a land you control enters, create a 1/1 green Elf creature token.\"", Effect.chapterGainLandfallCreateElf),
  ("Elves you control get +1/+0 and gain vigilance until end of turn.", Effect.chapterElvesGetVigilance 1),
  ("Target opponent reveals their hand. You choose a nonland card from it. That player discards that card.", Effect.chapterOpponentDiscardsNonland),
  ("Amass Goblins 1. (Put a +1/+1 counter on an Army you control. It's also a Goblin. If you don't control an Army, create a 0/0 black Goblin Army creature token first.)", Effect.chapterAmassGoblins 1),
  ("Target opponent loses 1 life and you gain 1 life.", Effect.chapterOpponentLosesYouGain 1),
  ("Target creature you control gains hexproof for as long as this Saga remains on the battlefield.", Effect.chapterGrantHexproofWhileRemains),
  ("Prevent all damage that would be dealt by up to one target creature for as long as this Saga remains on the battlefield.", Effect.chapterPreventDamageWhileRemains),
  ("Draw a card.", Effect.chapterDraw 1),
  ("Search your library for up to two basic Plains cards, exile them, then shuffle. You gain 2 life.", Effect.chapterSearchBasicPlainsExileGainLife 2 2),
  ("Put a card exiled with this Saga into its owner's hand.", Effect.chapterReturnLinkedExileToHand),
  ("Whenever you attack this turn, target creature you control gets +1/+1 until end of turn for each Plains you control.", Effect.chapterGrantAttackPumpPerPlainsThisTurn),
  ("Exile up to one target creature or land you control. If you do, return it to the battlefield under its owner's control at the beginning of the next end step.", Effect.chapterBlinkUntilEndStep),
  ("Create a Treasure token. Then if you control four or more Treasures, sacrifice this Saga. If you do, create a 6/6 red Dragon creature token with flying. (A Treasure token is an artifact with \"{T}, Sacrifice this token: Add one mana of any color.\")", Effect.chapterTreasureThenDragonIfFour),
  ("Recruit. (Draw a card, then discard a card. If you discarded a nonland card, create a 1/1 white Human Soldier creature token.)", Effect.chapterRecruit),
  ("Return target creature card with mana value 3 or less from your graveyard to the battlefield.", Effect.chapterReturnCreatureFromGyMvAtMost 3),
  ("Put a +1/+1 counter on up to one target creature.", Effect.chapterPlusOneUpToOne),
  ("Scry 2.", Effect.scry 2),
  ("You may put a Hero creature card with mana value 3 or less from your hand onto the battlefield. If you don't, draw a card.", Effect.mayPutHeroMvOrDraw 3),
  ("Put a +1/+1 counter on each creature you control.", Effect.plusOneOnEachYouControl),
  ("The next red or green creature spell you cast this turn can be cast without paying its mana cost.", Effect.nextFreeRGCreature),
  ("Put three +1/+1 counters on target creature you control.", Effect.plusOneOnCreatureN 3),
  ("Choose target creature you control. Until end of turn, double its power and toughness and it gains trample.", Effect.chooseTargetDoubleAndTrample),
  ("You may draw a card for each artifact you control. If you do, each opponent draws a card.", Effect.mayDrawPerArtifactOppsDraw),
  ("Artifact spells you cast this turn cost {1} less to cast.", Effect.artifactSpellsCostLessThisTurn 1),
  ("This Saga deals X damage to target opponent, where X is the greatest mana value among artifacts you control.", Effect.chapterDealXDamageToTargetOpponentGreatestArtifactMv),
  ("Create two 2/1 black Villain creature tokens with menace.", Effect.createTokens .villain21menace 2),
  ("This Saga deals 2 damage to each non-Villain creature and each opponent.", Effect.chapterDealDamageToEachNonSubtypeAndOpponents 2 "Villain"),
  ("Create a Treasure token for each Villain you control.", Effect.createTokensPerSubtype .treasure "Villain"),
  ("Destroy up to one target nonland permanent.", Effect.destroyUpToOneNonland),
  ("Each opponent loses 2 life.", Effect.eachOpponentLosesLife 2),
  ("Create Galactus, a legendary 16/16 black Elder Alien creature token with flying, trample, and \"Whenever Galactus attacks, destroy target land.\".", Effect.createGalactus),
  ("Gain control of up to two target creatures with total mana value 6 or less for as long as this Saga remains on the battlefield.", Effect.chapterGainControlOfUpToTwoCreaturesTotalMvAtMost 6),
  ("Creatures you control get +1/+1 and gain vigilance until end of turn.", Effect.creaturesYouControlGetAndGrant 1 1 #[Keyword.vigilance]),
  ("Target creature you control fights up to one other target creature.", Effect.fightUpToOne),
]

end Mtg.Engine.OracleCandidates
