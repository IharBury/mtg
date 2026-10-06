import Mtg.Engine.Card.FraEffects

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
  Effect.dealDamageToTargetCreature 1,
  Effect.castingIronFistTap,
  Effect.creatureYouControlDealsPowerToOppCreature,
  Effect.enterRevealDiscardFromHand,
  Effect.watchUltronCopy,
  Effect.castingVisionModes,
  Effect.watchVillainAttachEquipment,
  Effect.stepHydeChoose,
  Effect.resourceDrawIfAnotherHeroDamage,
  Effect.becomeDinosaurHero 3 5 (Keyword.reach.merge Keyword.vigilance),
  Effect.becomeDinosaurHero 6 6 Keyword.trample,
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
  Effect.teamGain Keyword.menace,
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
  Effect.pumpAndGrantKeywords 3 0 (Keyword.reach.merge Keyword.firstStrike),
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
  Effect.dealDamageToAny 4,
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
  Effect.teamGain Keyword.doubleStrike,
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
  Effect.anotherYouControlGetsAndGrant 2 0 Keyword.hexproof,
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
  Effect.copyControlledAbility true,
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
  Effect.abilityDealDamageToEachCreature 2,
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
  Effect.plusOneAndGrant ((Keyword.vigilance.merge Keyword.indestructible).merge Keyword.haste),
  Effect.resourceGainLifePlusOnes,
  Effect.enterCreateZabu,
  Effect.resourcePlusOneOnThisOnce,
  Effect.plusOneAndCreateTokens 1 .hero32vigilance,
  Effect.proliferateEachKind,
  Effect.creatureYouControlDealsTwicePower,
  Effect.millThenPutPermanentGainLife 2 2,
  Effect.gainLifeSearchBasicPlusOne 2,
  Effect.millThenPutSubtypeOrEnchantment 4 "Hero",
  Effect.destroyUpToOneThenPlusOne,
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
  Effect.copyControlledAbility false,
  Effect.deathDeathtouchOppSac,
  Effect.castingTargetsGainFlying,
  Effect.creaturesYouControlGetAndGrant 1 1 Keyword.vigilance,
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
  Effect.ofTrigger (.createTokens .treasure 1 true),
  Effect.ofTrigger (.dividedDamage 3 3),
  Effect.ofTrigger .opponentSacrificesCreature,
  Effect.ofTrigger (.attachTo .legendaryCreatureYouControl),
  Effect.ofTrigger (.plusOneOn .creatureYouControl),
  Effect.ofTrigger (.createTokens .wall 1),
  Effect.ofTrigger .connive,
  Effect.ofTrigger .plusOneOnSource,
  Effect.ofTrigger .drawAndLoseLife,
  Effect.ofTrigger (.gainLife 2),
  Effect.ofTrigger (.pumpTarget .creature 4 4),
  Effect.ofTrigger (.exileUntilLeaves .oppTappedCreature),
  Effect.ofTrigger .youRecruit,
  Effect.ofTrigger (.damageEachOpponent 2),
  Effect.ofTrigger .exileTop,
  Effect.ofTrigger (.mayDiscardDraw 2),
  Effect.ofTrigger .eachOpponentDiscards,
  Effect.ofTrigger (.onPermanent .anotherCreatureYouControl (.pumpAndTrample 2 0)),
  Effect.ofTrigger .investigate,
  Effect.ofTrigger (.amassOrcs 1),
  Effect.ofTrigger .searchForest,
  Effect.ofTrigger .eachPlayerSacrificesCreature,
  Effect.ofTrigger .loot,
  Effect.ofTrigger .plusOneEachYouControl,
  Effect.ofTrigger .pumpByLookedAt,
  Effect.ofTrigger .pumpAndUnblockable,
  Effect.ofTrigger (.mayDiscardHandDraw 4),
  Effect.ofTrigger (.plusOneAndLifelink .creature),
  Effect.ofTrigger .pumpGreatestPower,
  Effect.ofTrigger (.damageBlockers 1),
  Effect.ofTrigger (.createThenAttach .treasure),
  Effect.ofTrigger .drawPlusOneSource,
  Effect.ofTrigger .ringTempts,
  Effect.ofTrigger .setOtherBasePT,
  Effect.ofTrigger .returnElfGainLife,
  Effect.ofTrigger .damageFromLastKnownPower,
  Effect.ofTrigger (.exileOppGyCardOppsLoseLife 2),
  Effect.ofTrigger (.creaturesYouControlPumpAndFirstStrike 1),
  Effect.ofTrigger (.mayPayGenericDraw 1),
  Effect.ofTrigger .drawThenBottomIfNoLegendary,
  Effect.ofTrigger .removeHopeDrawSac,
  Effect.ofTrigger .tapHumansDraw,
  Effect.ofTrigger (.untapPlusOneIfSubtype "Bear"),
  Effect.ofTrigger .destroyOppArtifactsEnchantmentsGainLife,
  Effect.ofTrigger (.damageEqualSubtypeToEachOpponent "Dwarf"),
  Effect.ofTrigger .damageEqualTreasures,
  Effect.ofTrigger .loseLifeCreateTreasure,
  Effect.ofTrigger (.dealDamageDestroyIfSubtype 1 "Dragon"),
  Effect.ofTrigger .attachEquipmentToCreature,
  Effect.ofTrigger .defenderSacsLeastPower,
  Effect.ofTrigger .returnOtherPlusOne,
  Effect.ofTrigger (.lookAtTopRevealTypes 4 #["Dwarf", "Equipment"]),
  Effect.ofTrigger .createTappedTreasuresEqualOppArtifacts,
  Effect.ofTrigger (.putNonlandMvAtMostFromGy 3),
  Effect.ofTrigger (.othersGetAndOppsGet #["Goblin", "Orc"] 2 2 (-1) (-1)),
  Effect.ofTrigger .wolfPlusOneOrTreasure,
  Effect.ofTrigger .trampleCounterBecomeBear,
  Effect.ofTrigger (.millThenSubtypeToHand 4 "Elf"),
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
  Effect.ofTrigger .plusOneEachIfCityBlessing,
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
  Effect.ofTrigger .amassGoblinsEqualPower,
  Effect.ofTrigger .recruit,
  Effect.ofTrigger (.plusOneOn .creature),
  Effect.ofTrigger (.attachTo .creatureYouControl),
  Effect.ofTrigger (.conniveTarget .creatureYouControl),
  Effect.ofTrigger (.exileUntilLeaves .oppNonland),
  Effect.ofTrigger (.exileUntilLeaves .defendingPlayerCreature),
  Effect.ofTrigger (.sourceGets 1 1),
  Effect.ofTrigger (.createTokens .treasure 1),
  Effect.ofTrigger .searchBasicToHand,
  Effect.ofTrigger (.exileTarget .anotherCreature),
  Effect.ofTrigger .returnCreatureFromGyToHand,
  Effect.ofTrigger .honeEachEquipment,
  Effect.ofTrigger .plusOneEachOtherGainLife,
  Effect.ofTrigger .pumpTargetPerPlains,
  Effect.ofTrigger (.drawThenDiscard 2),
  Effect.ofTrigger .pumpForEachOtherCreature,
  Effect.ofTrigger (.grantFlying .attackingCreatureWithoutFlying),
  Effect.ofTrigger .returnLinkedExile,
  Effect.ofTrigger .createAxe,
  Effect.ofTrigger .tapOppOrUntapYours,
  Effect.ofTrigger .gainControlOppUntilEot,
  Effect.ofTrigger .createAxeAttach,
  Effect.ofTrigger .payReturnFromGy,
  Effect.ofTrigger (.plusOneVigilance 2),
  Effect.ofTrigger .mayDrawXDiscard2,
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
  Effect.ofTrigger .plusOneOnSourceAndDraw,
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
  Effect.pumpAndGrantKeywords 2 2 Keyword.flying,
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
  Effect.creaturesYouControlGetAndGrant 1 0 Keyword.haste,
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
  Effect.plusOneThenGrant 2 Keyword.trample,
  Effect.addColorless 3,
  Effect.recursiveRecruitment,
  Effect.targetCreatureGains (Keyword.firstStrike.merge Keyword.deathtouch)
    "first strike and deathtouch",
  Effect.cadetWithHaste,
  Effect.stingingVitriol,
  Effect.theorixCounter,
  Effect.millThenDraw 3 1,
  Effect.twinnedVision,
  Effect.twistedFates,
  Effect.permanentYouControlGains (Keyword.hexproof.merge Keyword.indestructible),
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
  FraCandidates.ab (.createTokens .illusion11blue 1) "Create a 1/1 blue Illusion creature token",
  FraCandidates.ab (.fra .bounceEachTarget)
    "For each opponent, return up to one target artifact or creature that player controls to its owner's hand"
    (.filtered { noun := "up to one target artifact or creature that player controls",
                 types := #[.artifact, .creature], controller := .eachOpponent })
    (allowsZeroTargets := true),
  FraCandidates.ab (.fra .drawThreeThenCountersPerHand)
    "Draw three cards. Then put X +1/+1 counters on each creature you control, where X is the number of cards in your hand",
  FraCandidates.ab (.fra .surveilReturnNoncreatureNonland)
    "Surveil 1. If you put a noncreature, nonland card into your graveyard this way, put that card into your hand",
  FraCandidates.ab (.fra .addBlueNoncreatureOnly) "Add {U}. Spend this mana only to cast a noncreature spell",
  FraCandidates.ab (.fra .tapAndStunX) "Tap target artifact or creature. Put X stun counters on it"
    (.filtered { noun := "target artifact or creature", types := #[.artifact, .creature] }),
  FraCandidates.ab (.fra .emblemDrawOnCast) "You get an emblem with \"Whenever you cast a spell, draw a card.\"",
  FraCandidates.ab (.fra .empowerJacePerIsland) "Empower Jace X, where X is the number of Islands you control",
  FraCandidates.ab (.fra .attackersGetMinusFiveUntilYourTurn)
    "Until your next turn, whenever a creature attacks you or a planeswalker you control, it gets -5/-0 until end of turn",
  FraCandidates.ab (.fra .exileOpponentLibrariesButBottom) "Exile all but the bottom card of each opponent's library",
  FraCandidates.ab (.fra .minusFourMinusOneUntilYourTurn) "Up to one target creature gets -4/-1 until your next turn"
    (.filtered { TargetFilter.creature with noun := "up to one target creature" }) (allowsZeroTargets := true),
  FraCandidates.ab (.fra .eachPlayerSacrificesThenBeast)
    "Each player sacrifices a creature of their choice. If you sacrificed a creature this way, create a 4/4 green Beast creature token with trample",
  FraCandidates.ab (.fra .eachOpponentDiscardsTwoDrawPerShort)
    "Each opponent discards two cards. For each opponent who didn't discard two nonland cards this way, you draw a card",
  FraCandidates.ab (.fra .discardHandDrawPerCreature) "Discard your hand, then draw a card for each creature you control",
  FraCandidates.ab (.fra (.damageEachCreatureExceptYourTokens 4)) "This deals 4 damage to each creature except for tokens you control",
  FraCandidates.ab (.fra .emblemCreaturesGetTwoTwo) "You get an emblem with \"Creatures you control get +2/+2.\"",
  FraCandidates.ab (.fra .untapTargets) "Untap up to two target lands"
    (.filtered { noun := "up to two target lands", types := #[.land] }) (allowsZeroTargets := true) (maxTargets := 2),
  FraCandidates.ab (.fra .attackersGetTwoTwoTrampleUntilYourTurn)
    "Until your next turn, whenever one or more creatures attack one of your opponents, those creatures get +2/+2 and gain trample until end of turn",
  FraCandidates.ab (.sequence [.fra (.damageEachOpponent 1), .gainLife 1])
    "This planeswalker deals 1 damage to each opponent and you gain 1 life",
  FraCandidates.ab (.fra .plusOnePerLand) "Put a +1/+1 counter on target creature for each land you control"
    (.filtered TargetFilter.creature),
  FraCandidates.ab (.fra .maySacrificeCreatureForBeast)
    "You may sacrifice a creature. If you do, create a 4/4 green Beast creature token with trample",
  FraCandidates.ab (.fra (.damageUpToOneAndPlayer 2))
    "This planeswalker deals 2 damage to up to one target creature or planeswalker and 2 damage to target player"
    (.multi #[{ TargetFilter.creatureOrPlaneswalker with noun := "up to one target creature or planeswalker" },
      { noun := "target player", zone := .player }] #[0]),
  FraCandidates.ab (.createTokens .leviathan88hexproof 1) "Create an 8/8 blue Leviathan creature token with hexproof",
]

def staticAbilities : Thunk (Array StaticAbility) := Thunk.mk fun _ => #[
  .otherCreaturesHaveTrample #["Orc", "Goblin"],
  .enchantedCreatureGets 3 3,
  .otherCreaturesGet #["Elf"] 1 1,
  .equippedCreatureGets 2 0,
  .powerToughnessEqualLandsYouControl,
  .cantBlockUnlessYouControl #["Goblin", "Orc"],
  .cantBlockUnlessYouControl #[],
  .cantBeBlockedByTokens,
  .powerEqualCreaturesYouControl,
  .otherCreaturesGet #[] 1 1,
  .cantAttackUnlessYouControlNOther 2 "Wolf",
  .equippedCreatureGetsAndHas 1 0 Keyword.menace,
  .enchantedCreatureGetsAndHas 2 2 Keyword.flying,
  .equippedCreatureGetsAndWard 2 2 1,
  .creaturesYouControlWithPlusOneHaveMenace,
  .creaturesYouControlGet 1 1,
  .hasteIfYouControlOtherSubtype "Goblin",
  .equippedCreatureGetsAndHas 1 1 Keyword.reach,
  .getsAndHasIfEnduringStory 1 0 Keyword.vigilance,
  .getsAndHasIfEnduringStory 1 0 Keyword.haste,
  .doesntUntapUnlessEnduringStory,
  .creaturesYouControlGetIfEnduringStory 1 1,
  .artifactsAndCreaturesHaveWardIfEnduringStory 1,
  .creaturesCantAttackYouUnlessPayIfEnduringStory 1,
  .thresholdGets 1 1,
  .cantBeBlockedByPowerAtMost 2,
  .equipAbilitiesTargetingThisCostLess 2,
  .equippedCreatureHasKeywordsAndCantBeBlocked Keyword.hexproof,
  .firstEquipFreeIfEnduringStory,
  .lifelinkIfYouControlOtherSubtype "Dwarf",
  .instantSorceryCostReductionEqualEquippedPower,
  .chosenTypeCreaturesGet 2 2,
  .extraTriggerIfEnduringStorySubtype "Dwarf",
  .enchantedLosesAbilitiesDoesntUntap,
  .exileOppDeathCreateWolf,
  .powerPerFatGraveyard 2,
  .equippedCreatureGetsAndHas 2 2 Keyword.trample,
  .copyActivatedFromGySubtype "Elf",
  .equippedTriggersAgain,
  .equippedCreatureHasKeywords Keyword.prowess,
  .enchantedIsOnlySubtypeCantAttackOrBlock "Spirit",
  .powerEqualCardsInHand,
  .cantBeBlockedExceptBy 3,
  .armiesYouControlHaveTrample,
  .legendaryCreaturesGetAndWard 2 1 1,
  .nonlegendaryCreaturesGet 1 1,
  .equippedCreatureHasKeywords Keyword.indestructible,
  .equippedCreaturesHaveKeywordsDuringYourTurn (Keyword.firstStrike.merge Keyword.vigilance),
  .otherSubtypeHaveTapAddOneOf #["Elf"] #[.colored .green, .colored .blue],
  .otherSubtypeGetPowerPerArtifactToken "Dwarf",
  .cantBeBlockedByPowerAtLeast 3,
  .equippedHexproofUnblockableDuringYourTurn,
  .extraTriggerAnotherYouControl #["Wolf"] true,
  .equippedFirstStrikePlusPerInstantSorcery,
  .wardDiscardEnchantmentInstantOrSorcery,
  .wardSacrificeLegendary,
  .equippedGetsTrampleAndCombatTreasures 1 1,
  StaticAbility.opponentsCantCastOnYourTurn,
  StaticAbility.preventAllDamageToThis,
  StaticAbility.creaturesYouControlOfSubtypeGet "Hero" 2 2,
  StaticAbility.youAndOtherSubtypeHaveHexproofIfShield "Hero",
  StaticAbility.flashIfOpponentCastThisTurn,
  StaticAbility.attackingTokensHave Keyword.firstStrike,
  StaticAbility.enchantedCreatureGetsHasAndTypes 2 2
        (Keyword.firstStrike.merge Keyword.vigilance) #["legendary", "Soldier"],
  StaticAbility.otherCreaturesGet #["Merfolk"] 1 1,
  StaticAbility.equippedCreatureGetsHasAndWard 1 1 Keyword.flying 1,
  StaticAbility.enchantedLosesAbilitiesCantUntap,
  .improvise,
  .noncreatureSpellsHaveImprovise,
  StaticAbility.hexproofIfPlusOneThisTurn,
  StaticAbility.extraDrawOnConnive,
  .noMaximumHandSize,
  .powerEqualSubtypeYouControl "Merfolk",
  StaticAbility.enchantedCreatureHasWard 2,
  .typeSpellsCostLess .artifact 1,
  .supertypeSpellsCostLess .legendary 1,
  StaticAbility.cantBeBlockedIfPowerAtMost 1,
  StaticAbility.boast,
  StaticAbility.subtypeSpellsCostLess "Villain" 1,
  StaticAbility.indestructibleIfArtifactCreatureOrPlan,
  StaticAbility.sneak (ManaCost.ofGenericAndColors 1 [.black, .black]),
  StaticAbility.opponentsCreaturesGet (-1) (-1),
  StaticAbility.noncombatDamagePlusSourcePower,
  StaticAbility.equippedDealsDoubleDamage,
  StaticAbility.mayBeginOnBattlefield,
  StaticAbility.instantSorceryCostLessEqualPower,
  StaticAbility.enchantedCreatureGetsAndHas 1 0 Keyword.haste,
  StaticAbility.extraPowerUpActivation,
  StaticAbility.extraCounterOnPermanents,
  StaticAbility.mayPlayLandsFromGraveyard,
  StaticAbility.activateCreaturesAsThoughHaste,
  StaticAbility.enchantedCreatureGetsHasAndWard 4 4
        Keyword.trample 1,
  StaticAbility.creaturesWithPlusOneHave Keyword.trample,
  StaticAbility.getsAndAllTypesIfGyCreatureCards 2 2 2,
  StaticAbility.attacksEachCombatIfAble,
  StaticAbility.flyingIfPlusOneThisTurn,
  StaticAbility.otherPowerUpCostsLess 3,
  StaticAbility.getsPowerPerOtherArtifact 1,
  StaticAbility.getsIfGyCreatureCards 2 2 1,
  .extort,
  StaticAbility.entersWithXPlusOne,
  StaticAbility.wardPoisonCounters 5,
  StaticAbility.flyingCantAttackYouOrBlockYours,
  StaticAbility.wardDiscardOrPay 2,
  StaticAbility.getsPowerPerAttachedEquipment 2,
  StaticAbility.healOtherDamageWhenDealt,
  StaticAbility.equippedCreatureGetsAndHas 0 8 Keyword.vigilance,
  StaticAbility.equippedCreatureGetsAndHas 2 1 Keyword.flying,
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
  .fra .attackDespiteDefenderIfScried,
  .fra .powerPerSevenInGraveyard,
  .fra .creaturesYouControlHaveTrample,
  .fra .firstStrikeDuringYourTurn,
  .fra .equippedHuntersAxe,
  .fra .enchantArtifactOrNonAuraEnchantment,
  .fra .enchantedIsConstruct55,
  .fra .enchantedGetsOneAndDeathtouch,
  .fra .vigilanceIfJace,
  .fra .powerAndFlyingIfSevenInGraveyard,
  .fra .plusOneCreaturesHaveVigilance,
  .fra .flyingHasteIfOpponentDealtNoncombat,
  .fra .equippedMedicsKitesail,
  .fra .entersTappedChooseColor,
  .fra .tapAddChosenColor,
  .fra .creaturesAttackDespiteDefender,
  .fra .creatureTokensGetOneAndVigilance,
  .fra .tapAddColorlessNotFromHand,
  .fra .tapAddAnyColorPlaneswalkerOnly,
  .fra .opponentsNoncreatureSpellsCostMore,
  .fra .planeswalkersAttackedByOneAtMost,
  .fra .extraPlusOneCounter,
  .fra .noSpellsOrAbilitiesDuringCombat,
  .fra .noncreatureSpellsCostLess,
  .fra .costsLessIfCastNoncreature,
  .fra .exileOpponentsDyingCreatures,
  .fra .wardDiscardCard,
  .fra .wardSacrificeThreePermanents,
  .fra .powerPerCreatureAndPlaneswalkerCard,
  .fra .otherPlusOneCreaturesHaveHaste,
  .fra .creaturesYouControlHaveHaste,
  .fra .noncombatDamagePlusOne,
  .fra .powerEqualsBasicLandTypes,
  .fra .otherCreaturesHaveTrample,
  .fra .landsHaveHexproof,
  .fra .hexproofUntilCombatDamage,
  .fra .thoptersHaveHaste,
  .fra .artifactCreaturesHaveVigilance,
  .fra .doesntUntap,
  .fra .entersChooseNonlandCardName,
  .fra .chosenNameSpellsCantBeCast,
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
  .onAttackTargetGainsKeywords Keyword.firstStrike,
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
  .onEnterEnchanted .tap,
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
  .onEnterAttachThen .untap,
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
  .onEnterAttachThen (.grantKeywords Keyword.indestructible),
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
  .onEnterEnchanted (.grantKeywords Keyword.firstStrike),
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
  .triggered .enter (Effect.ofTrigger (.empowerJace 1)),
  .triggered .youGainLife (Effect.ofTrigger (.onSource (.plusOne 2))),
  .triggered .landYouControlEnters (Effect.ofTrigger (.empowerJace 2)),
  .onStep (Effect.ofTrigger .prepareSourceIfNot),
  .onStep (Effect.ofTrigger .prepareSourceIfThreeDied),
  .triggered .youActivateLoyaltyAbility (Effect.ofTrigger .drawIfRemovedTwoLoyalty),
  .triggered .youActivateLoyaltyAbility (Effect.ofTrigger (.createTokens .cadet 1)),
  .triggered .youCastFirstNoncreature (Effect.ofTrigger (.empowerJace 1)),
  .triggered .youCastNoncreature (Effect.ofTrigger (.createTokens .sculpture 1)),
  .triggered .youGainLife (Effect.ofTrigger (.plusOneOnEachSubtypeYouControl "Angel")),
  .triggered .youCastTargetingOpponentOrTheirCreature (Effect.ofTrigger .plusOneOnSource),
  .triggered .landYouControlEnters (Effect.ofTrigger (.gainLife 1)),
  .triggered (.subtypeYouControlEnters "Plains") (Effect.ofTrigger (.plusOneOn .creature)),
  .triggered .youGainLife (Effect.ofTrigger .loyaltyOnSource),
  .triggered .enter (Effect.ofTrigger (.grantThenCounterByType Keyword.hexproof)),
  .triggered .enter (Effect.ofTrigger (.grantThenCounterByType Keyword.deathtouch)),
  .triggered .enter (Effect.ofTrigger .destroyOppPermanentIfSixLands),
  .onStep (Effect.ofTrigger .pumpOrCounterIfScried),
  .triggered .eachUpkeep (Effect.ofTrigger (.createTokens .forestTentacle 1)),
  .triggered .eachOpponentDrawStep (Effect.ofTrigger (.draw 1)),
  .triggered .youCastNoncreature (Effect.ofTrigger (.creaturesYouControlGet 1 0)),
  .triggered .dies (Effect.ofTrigger .putSourceCountersOnTarget),
  .triggered .creatureYouControlDies (Effect.ofTrigger .chargeCounterOnSource),
  .onStep (Effect.ofTrigger .addGreenPerChargeCounter),
  .triggered .youScryOrSurveil (Effect.ofTrigger (.mayPayPlusOneAndDraw 2)),
  .triggered .youScryOrSurveil (Effect.ofTrigger (.sourceGets 1 1)),
  .triggered .youScryOrSurveil (Effect.ofTrigger (.creaturesYouControlGet 1 0)) .once,
  .triggered .opponentsDealtCombatDamageYourTurn (Effect.ofTrigger .drawTwoWinIfEmptyShuffleSource),
  .triggered .forestYouControlEnters (Effect.ofTrigger .pumpIfFiveOtherForests),
  .onStep (Effect.ofTrigger .surveilReturnIfGainedLife),
  TriggeredAbility.fra (.fra .castThis) "When you cast this spell, untap all lands you control."
    (.fra .untapAllLandsYouControl),
  TriggeredAbility.fra .youCastCreature
    "Whenever you cast a creature spell, exile up to one other target creature you control, then return that card to the battlefield under its owner's control."
    (.fra .blink)
    (.filtered { noun := "up to one other target creature you control", types := #[.creature], controller := .you, another := true })
    (allowsZeroTargets := true),
  TriggeredAbility.fra .yourBeginCombat
    "At the beginning of combat on your turn, you may remove a +1/+1 counter from this creature. If you do, put a +1/+1 counter on each other creature you control."
    (.fra .mayMovePlusOneToEachOther),
  TriggeredAbility.fra .attack
    "Whenever this creature attacks, empower Jace X, where X is the number of creatures you control."
    (.fra .empowerJacePerCreature),
  TriggeredAbility.fra .enter "When this Aura enters, tap enchanted creature. It becomes unprepared."
    (.fra .tapEnchantedUnprepare),
  TriggeredAbility.fra .enter
    "When this enchantment enters, the owner of up to one other target nonland permanent puts it on their choice of the top or bottom of their library."
    (.fra .ownerPutsOnTopOrBottom)
    (.filtered { noun := "up to one other target nonland permanent", nonland := true, another := true })
    (allowsZeroTargets := true),
  TriggeredAbility.fra .enter
    "When this creature enters, draw two cards, then discard two cards. When you discard one or more nonland cards this way, tap up to that many target creatures and put a stun counter on each of them."
    (.fra .drawTwoDiscardTwoStun),
  TriggeredAbility.fra .attack "Whenever this creature attacks, draw a card, then discard a card."
    (.sequence [.draw 1, .discard 1]),
  TriggeredAbility.fra .dies "When this creature dies, if it isn't a token, create a token that's a copy of it."
    (.fra .copyTokenOfSourceIfNotToken) (cond := .sourceNotToken),
  TriggeredAbility.fra (.or .enter .dies) "When this creature enters or dies, you gain 2 life." (.gainLife 2),
  TriggeredAbility.fra .enter "When this creature enters, mill three cards." (.millSelf 3),
  TriggeredAbility.fra (.fra .yourBeginCombatFromGraveyard)
    "At the beginning of combat on your turn, if two or more creatures died this turn, return this card from your graveyard to the battlefield."
    (.fra (.returnSourceFromGy false false 0)) (cond := .twoCreaturesDiedThisTurn),
  TriggeredAbility.fra .enter
    "When this Equipment enters, you may pay {2}. When you do, for each opponent, destroy up to one target creature or planeswalker that player controls."
    (.fra (.mayPayThenDestroyPerOpponent 2)),
  TriggeredAbility.fra .enter "When this creature enters, target creature gets +2/+2 and gains deathtouch until end of turn."
    (.sequence [.onPermanent (.pump 2 2), .onPermanent (.grantKeywords Keyword.deathtouch)])
    (.filtered TargetFilter.creature),
  TriggeredAbility.fra .attack "Whenever this creature attacks, it deals 1 damage to each opponent and you gain 1 life."
    (.sequence [.fra (.damageEachOpponent 1), .gainLife 1]),
  TriggeredAbility.fra .enter "When this enchantment enters, it deals X damage to any target." (.fra .damageX) .playerOrCreature,
  TriggeredAbility.fra .youCastNoncreature "Whenever you cast a noncreature spell, put a +1/+1 counter on this creature."
    (.fra (.plusOneOnSource 1)),
  TriggeredAbility.fra (.fra .eachUpkeepFromGraveyard)
    "At the beginning of each upkeep, if an opponent was dealt noncombat damage last turn, return this card from your graveyard to your hand."
    (.fra (.returnSourceFromGy true false 0)) (cond := .opponentDealtNoncombatDamageLastTurn),
  TriggeredAbility.fra .enter
    "When this creature enters, creatures you control gain trample and get +X/+0 until end of turn, where X is the number of artifacts you control."
    (.fra .trampleAndPowerPerArtifact),
  TriggeredAbility.fra .enter
    "When this creature enters, search your library for a card, put it into your hand, shuffle, then discard a card at random."
    (.fra .searchCardThenDiscardRandom),
  TriggeredAbility.fra .enter "When this creature enters, create a 2/2 colorless Wizard Soldier creature token named Cadet."
    (.createTokens .cadet 1),
  TriggeredAbility.fra (.fra .opponentsDealtNoncombatDamage)
    "Whenever one or more opponents are dealt noncombat damage, creatures you control get +1/+0 until end of turn."
    (.creaturesYouControlPump 1 0),
  TriggeredAbility.fra .enter
    "When this creature enters, target instant or sorcery card in your graveyard gains flashback until end of turn. The flashback cost is equal to its mana cost."
    (.fra .grantFlashbackUntilEot)
    (.filtered { noun := "target instant or sorcery card in your graveyard", zone := .yourGraveyard, types := #[.instant, .sorcery] }),
  TriggeredAbility.fra .enter "When this creature enters, you may discard a card. When you do, this creature deals 2 damage to any target."
    (.fra (.mayDiscardThenDamage 2)),
  TriggeredAbility.fra .combatDamageToPlayer
    "Whenever this creature deals combat damage to a player, return target land card from your graveyard to your hand."
    (.fra .returnFromGyToHand)
    (.filtered { noun := "target land card from your graveyard", zone := .yourGraveyard, types := #[.land] }),
  TriggeredAbility.fra .anotherCreatureYouControlEnters "Whenever another creature you control enters, you gain 1 life."
    (.gainLife 1),
  TriggeredAbility.fra .sourceDealtDamage
    "Whenever this creature is dealt damage, you may search your library for up to that many land cards, put them onto the battlefield tapped, then shuffle."
    (.fra .maySearchLandsEqualDamage),
  TriggeredAbility.fra .enter "When this creature enters, create a Heartwood token." (.createTokens .heartwood 1),
  TriggeredAbility.fra (.fra .youPutLoyaltyCounters)
    "Whenever you put one or more loyalty counters on a planeswalker, put a +1/+1 counter on this creature."
    (.fra (.plusOneOnSource 1)),
  TriggeredAbility.fra .enter
    "When this creature enters, you may search your library for a basic land card, put that card onto the battlefield tapped, then shuffle."
    (.fra .maySearchBasicLandTapped),
  TriggeredAbility.fra .enter "When this creature enters, put three +1/+1 counters on target creature."
    (.onPermanent (.plusOne 3)) (.filtered TargetFilter.creature),
  TriggeredAbility.fra (.or .enter .dies) "When this creature enters or dies, create a Heartwood token."
    (.createTokens .heartwood 1),
  TriggeredAbility.fra .youGainLife "Whenever you gain life, draw a card. This ability triggers only once each turn."
    (.draw 1) (once := true),
  TriggeredAbility.fra .youScryOrSurveil "Whenever you scry or surveil, put a +1/+1 counter on each creature you control."
    (.fra .plusOneOnEachCreatureYouControl),
  TriggeredAbility.fra (.fra .enchantedDies)
    "When enchanted creature dies, return that card to the battlefield tapped under its owner's control."
    (.fra .returnCauseTapped),
  TriggeredAbility.fra .eachEndStep "At the beginning of the end step, sacrifice this creature." (.fra .sacrificeSource),
  TriggeredAbility.fra (.fra .creatureYouControlAttacks)
    "Whenever a creature you control attacks, that creature deals 1 damage to each opponent."
    (.fra (.causeDealsDamageToEachOpponent 1)),
  TriggeredAbility.fra .youGainLife
    "Whenever you gain life, create a colorless artifact token named Lotus with \"{T}, Sacrifice this token: Add three mana of any one color.\" This ability triggers only once each turn."
    (.createTokens .lotus 1) (once := true),
  TriggeredAbility.fra .enter "When this creature enters, it fights up to one target creature an opponent controls."
    (.fra .sourceFightsTarget)
    (.filtered { noun := "up to one target creature an opponent controls", types := #[.creature], controller := .opponent })
    (allowsZeroTargets := true),
  TriggeredAbility.fra .enter
    "When this creature enters, if you cast it, target opponent reveals their hand. You choose a nonland card from it. Exile that card."
    (.fra .exileFromHandUntilLeaves) .opponent (cond := .sourceWasCast),
  TriggeredAbility.fra .enter
    "When this creature enters, mill four cards. When you do, return target land card from your graveyard to the battlefield tapped."
    (.fra (.millThenReturnLandTapped 4)),
  TriggeredAbility.fra (.fra .thisOrAnotherCreatureYouControlEnters)
    "Whenever this creature or another creature you control enters, surveil 1." (.surveil 1),
  TriggeredAbility.fra (.fra (.opponentCastsSpellMvAtMost 2))
    "Whenever an opponent casts a spell with mana value 2 or less, you gain 2 life." (.gainLife 2),
  TriggeredAbility.fra .enter
    "When this artifact enters, exile target nonland permanent an opponent controls with mana value 3 or less until this artifact leaves the battlefield."
    (.fra .exileUntilSourceLeaves)
    (.filtered { noun := "target nonland permanent an opponent controls with mana value 3 or less", nonland := true, controller := .opponent, mvAtMost := some 3 }),
  TriggeredAbility.fra .enter
    "When this creature enters, you may sacrifice a land. If you do, create two tapped Heartwood tokens."
    (.fra .maySacrificeLandForHeartwoods),
  TriggeredAbility.fra .enter
    "When this creature enters, if you cast him, exile up to one target nonland card of each card type from your graveyard. Copy those cards. You may cast any number of spells with total mana value 6 or less from among the copies without paying their mana costs."
    (.fra .uldarosCopies)
    (.filtered { noun := "up to one target nonland card of each card type from your graveyard"
                 zone := .yourGraveyard, nonland := true })
    (allowsZeroTargets := true) (maxTargets := 8) (cond := .sourceWasCast),
  TriggeredAbility.fra .enter "When this Equipment enters, it deals 3 damage to any target and you gain 3 life."
    (.sequence [.fra (.damageAny 3), .gainLife 3]) .playerOrCreature,
  TriggeredAbility.fra .attack "Whenever this creature attacks, exile up to one target card from a graveyard."
    (.fra .exileCardFromGraveyard)
    (.filtered { noun := "up to one target card from a graveyard", zone := .anyGraveyard })
    (allowsZeroTargets := true),
  TriggeredAbility.fra (.fra .youCastPreparedSpell)
    "Whenever you cast a prepared spell, copy it. You may choose new targets for the copy."
    (.fra .copyCauseSpell),
  TriggeredAbility.fra .enter "When this artifact enters, draw a card, then discard a card." (.sequence [.draw 1, .discard 1]),
  TriggeredAbility.fra .yourUpkeep
    "At the beginning of your upkeep, surveil 1. Then if there are seven or more cards in your graveyard, sacrifice this artifact, it deals 2 damage to each opponent, and you gain 2 life."
    (.fra .eyeOfJace),
  TriggeredAbility.fra (.fra .youCastEquipmentOrTargetingCreatureYouControl)
    "Whenever you cast an Equipment spell or a spell that targets a creature you control, draw a card. This ability triggers only once each turn."
    (.draw 1) (once := true),
  TriggeredAbility.fra (.fra .anotherCreatureOrPlaneswalkerYouControlEnters)
    "Whenever another creature or planeswalker you control enters, you gain 1 life." (.gainLife 1),
  TriggeredAbility.fra .youScryOrSurveil
    "Whenever you scry or surveil, create a 1/1 colorless Thopter artifact creature token with flying. This ability triggers only once each turn."
    (.createTokens .thopter 1) (once := true),
  TriggeredAbility.fra .youGainLife "Whenever you gain life, put a loyalty counter on each planeswalker you control."
    (.fra .loyaltyOnEachPlaneswalkerYouControl),
  TriggeredAbility.fra (.fra .creatureYouControlAttacksPlayerAlone)
    "Whenever a creature you control attacks a player alone, it gains double strike until end of turn."
    (.fra (.causeGains Keyword.doubleStrike)),
  TriggeredAbility.fra (.fra .anotherNontokenCreatureYouControlEnters)
    "Whenever another nontoken creature you control enters, untap this creature." (.fra .untapSource),
  TriggeredAbility.fra .enter
    "When this creature enters, for each opponent, tap up to one target creature that player controls. Put a stun counter on each of those creatures."
    (.fra .tapAndStunPerOpponent) (.filtered { noun := "up to one target creature that player controls", types := #[.creature], controller := .eachOpponent })
    (allowsZeroTargets := true),
  TriggeredAbility.fra .eachEndStep
    "At the beginning of each end step, if you've drawn three or more cards this turn, create a 3/3 blue Angel creature token with flying."
    (.createTokens .angel33blue 1) (cond := .drewThreeThisTurn),
  TriggeredAbility.fra (.fra .creatureOpponentControlsEnters)
    "Whenever a creature an opponent controls enters, this creature deals 1 damage to that player."
    (.fra (.damageCauseController 1)),
  TriggeredAbility.fra (.fra .opponentActivatesLoyaltyAbility)
    "Whenever an opponent activates a loyalty ability, this creature deals 1 damage to that player."
    (.fra (.damageCauseController 1)),
  TriggeredAbility.fra (.fra .anotherCreatureOrPlaneswalkerYouControlEnters)
    "Whenever another creature or planeswalker you control enters, mill two cards." (.millSelf 2),
  TriggeredAbility.fra .enter "When this creature enters, remove up to three counters from another target creature or planeswalker."
    (.fra (.removeUpToCounters 3))
    (.filtered { TargetFilter.creatureOrPlaneswalker with noun := "another target creature or planeswalker", another := true }),
  TriggeredAbility.fra (.fra .anotherCreatureOrPlaneswalkerYouControlDies)
    "Whenever another creature or planeswalker you control dies, this creature deals 1 damage to target opponent and you gain 1 life."
    (.sequence [.fra (.damageAny 1), .gainLife 1]) .opponent,
  TriggeredAbility.fra (.fra .opponentDealtNoncombatDamage)
    "Whenever an opponent is dealt noncombat damage, put a +1/+1 counter on this creature."
    (.fra (.plusOneOnSource 1)),
  TriggeredAbility.fra (.fra .playerDiscards)
    "Whenever a player discards one or more cards, this creature deals 1 damage to each opponent."
    (.fra (.damageEachOpponent 1)),
  TriggeredAbility.fra .creatureYouControlDies
    "Whenever a creature you control dies, put a loyalty counter on each planeswalker you control."
    (.fra .loyaltyOnEachPlaneswalkerYouControl),
  TriggeredAbility.fra .enter
    "When this creature enters, you may sacrifice a creature or planeswalker. When you do, each opponent sacrifices a creature of their choice."
    (.fra .maySacrificeThenEdict),
  TriggeredAbility.fra .anotherCreatureYouControlEnters
    "Whenever another creature you control enters, this creature gets +X/+0 until end of turn, where X is that creature's power."
    (.fra .sourceGetsCausePower),
  TriggeredAbility.fra (.fra .creatureYouControlAttacksPlayerAlone)
    "Whenever a creature you control attacks a player alone, discard a card, then draw a card. Then put a +1/+1 counter on that creature for each card you've discarded this turn."
    (.fra .jiangYangguAlone),
  TriggeredAbility.fra .enter "When this creature enters, create a 5/5 red Dragon creature token with flying."
    (.createTokens .dragon55flying 1),
  TriggeredAbility.fra .landYouControlEnters
    "Whenever a land you control enters, this creature deals 1 damage to each opponent. If that land is a Mountain, add {R}."
    (.fra .kothGeomancer),
  TriggeredAbility.fra .enter "When this creature enters, create a 1/1 colorless Thopter artifact creature token with flying."
    (.createTokens .thopter 1),
  TriggeredAbility.fra (.fra .opponentSmallCreatureBlocks)
    "Whenever a creature an opponent controls with power or toughness 1 or less blocks, this creature deals 1 damage to that creature's controller."
    (.fra (.damageCauseController 1)),
  TriggeredAbility.fra .yourEndStep
    "At the beginning of your end step, if you didn't cast a spell this turn, put two +1/+1 counters on this creature."
    (.fra (.plusOneOnSource 2)) (cond := .castNoSpellThisTurn),
  TriggeredAbility.fra .enter
    "When this creature enters, search your library for up to X basic land cards with different names, reveal them, put them into your hand, then shuffle."
    (.fra .fblthpSearch),
  TriggeredAbility.fra (.fra (.creatureYouControlPowerAtLeastEnters 4))
    "Whenever a creature you control with power 4 or greater enters, draw a card." (.draw 1),
  TriggeredAbility.fra .enter "When this creature enters, create Mowu, a legendary 3/3 green Dog creature token."
    (.createTokens .mowu 1),
  TriggeredAbility.fra .yourEndStep "At the beginning of your end step, untap all tokens you control."
    (.fra .untapAllTokensYouControl),
  TriggeredAbility.fra .enter
    "When this creature enters, you may discard a card. If you do, search your library for an enchantment card, reveal it, put it into your hand, then shuffle."
    (.fra .mayDiscardThenSearchEnchantment),
  TriggeredAbility.fra (.fra .youDiscardThis) "When you discard this card, you gain 3 life." (.gainLife 3),
  TriggeredAbility.fra .youActivateLoyaltyAbility
    "Whenever you activate a loyalty ability, you gain 1 life. You may play an additional land this turn."
    (.sequence [.gainLife 1, .spell .extraLand]),
  TriggeredAbility.fra .enter
    "When this creature enters, another target creature you control fights up to one target creature an opponent controls."
    (.fra .firstFightsSecond)
    (.multi #[{ noun := "another target creature you control", types := #[.creature], controller := .you, another := true },
      { noun := "up to one target creature an opponent controls", types := #[.creature], controller := .opponent }] #[1]),
  TriggeredAbility.fra (.fra .anotherCreatureOrPlaneswalkerYouControlDies)
    "Whenever another creature or planeswalker you control dies, you gain 1 life." (.gainLife 1),
  TriggeredAbility.fra .enter
    "When this creature enters, for each opponent, put X -1/-1 counters on up to one target creature that player controls, where X is the greatest mana value among cards in your graveyard."
    (.fra .minusOnesPerOpponent) (.filtered { noun := "up to one target creature that player controls", types := #[.creature], controller := .eachOpponent })
    (allowsZeroTargets := true),
  TriggeredAbility.fra .enter "When this creature enters, draw a card for each color among other artifacts you control."
    (.fra .drawPerColorAmongOtherArtifacts),
  TriggeredAbility.fra .youAttack
    "Whenever you attack, if you've activated a loyalty ability this turn, untap target attacking creature. It can't be blocked this turn."
    (.fra .untapUnblockable)
    (.filtered { noun := "target attacking creature", types := #[.creature], attacking := true })
    (cond := .activatedLoyaltyThisTurn),
  TriggeredAbility.fra (.fra .thisOrAnotherCreatureYouControlEnters)
    "Whenever this creature or another creature you control enters, put a +1/+1 counter on target creature that entered this turn."
    (.onPermanent (.plusOne 1))
    (.filtered { noun := "target creature that entered this turn", types := #[.creature], enteredThisTurn := true }),
  TriggeredAbility.fra .youCastNoncreature
    "Whenever you cast a noncreature spell, create a 1/1 colorless Thopter artifact creature token with flying."
    (.createTokens .thopter 1),
  TriggeredAbility.fra (.fra .youCastArtifactOrCreature) "Whenever you cast an artifact or creature spell, untap this creature."
    (.fra .untapSource),
  TriggeredAbility.fra (.fra .creatureYouControlLeaves)
    "Whenever a creature you control leaves the battlefield, if it had counters on it, put those counters on this artifact."
    (.fra .putCauseCountersOnSource) (cond := .causeHadCounters),
  TriggeredAbility.fra .yourBeginCombat
    "At the beginning of combat on your turn, if this artifact has counters on it, you may move all counters from this artifact onto target creature."
    (.fra .mayMoveSourceCountersToTarget) (.filtered TargetFilter.creature) (cond := .sourceHasCounters),
  TriggeredAbility.fra .enter "When this creature enters, you may pay {3}. If you do, proliferate twice."
    (.fra (.mayPayThenProliferate 3 2)),
  TriggeredAbility.fra (.fra .youProliferate) "Whenever you proliferate, draw a card." (.draw 1),
]

def activatedAbilities : Thunk (Array ActivatedAbility) := Thunk.mk fun _ => #[
  activated (Effect.sourceGets 1 1) (ManaCost.ofGeneric 2)
          (costReductionIfYouControlLegendary := 2),
  {
        cost := { mana := ManaCost.ofGeneric 2, tap := true, sacrificeSource := true },
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
  activated (Effect.sourceGets 2 2) (payLife := 2) (onceEachTurn := true),
  activated (Effect.returnFromGraveyardToHand) (ManaCost.ofGeneric 2)
          (sacrificeAnotherCreatureOrArtifact := true)
          (onlyAsSorcery := true) (activateFromGraveyard := true),
  activated (Effect.exileTopPlayUntilEndOfNextTurn)
          (sacrificeAnotherCreatureOrArtifact := true)
          (onlyDuringYourTurn := true) (onceEachTurn := true),
  activated (Effect.targetCantBeBlockedThisTurn) (ManaCost.ofGenericAndColor 4 .blue),
  activated (Effect.searchBasicLandTapped) (tap := true) (sacrificeSource := true),
  typecyclingAbility "Halfling" (ManaCost.ofGeneric 4),
  activated (Effect.addAnyColor) (ManaCost.ofGeneric 1) (tap := true),
  activated (Effect.destroyTargetPermanent) (ManaCost.ofGeneric 7) (tap := true)
          (sacrificeSource := true),
  activated (Effect.returnFromGyAttachPowerAtMost 1)
          (ManaCost.ofGenericAndHybrids 2 .white .blue 2)
          (activateFromGraveyard := true) (onlyAsSorcery := true),
  activated (Effect.ownerShuffleSourceDraw 3) (ManaCost.ofGeneric 6),
  activated (Effect.addMana #[.colored .black, .colored .red]) (tap := true)
          (sacrificeAnotherSubtype := some "Goblin"),
  activated (Effect.abilityDrawThenDiscard 1) (ManaCost.ofGeneric 2) (tap := true),
  activated (Effect.abilityDraw 1) (ManaCost.ofGeneric 1) (tap := true)
          (discardACard := true),
  activated (Effect.abilityCreateTokens .dwarf 1) (ManaCost.ofGenericAndColor 4 .red)
          (tap := true) (onlyAsSorcery := true) (costReductionPerEquipment := 1),
  activated (Effect.attachToTargetCreatureYouControl) (ManaCost.ofGeneric 2)
          (onlyAsSorcery := true) (payLife := 2),
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
          (sacrificeAnotherSubtype := some "creature"),
  typecyclingAbility "Plains",
  equipAbility (ManaCost.ofGeneric 1) (some "Human"),
  activated (Effect.destroyTargetArtifactOrEnchantment) (sacrificeSource := true)
          (onlyAsSorcery := true),
  activated (Effect.abilityCreaturesYouControlGet 1 1)
          (ManaCost.ofGenericAndColor 4 .white) (tap := true)
          (costReductionIfYouControlLegendary := 2),
  activated (Effect.millPlayer 3) (ManaCost.ofGenericAndColor 5 .blue) (tap := true),
  activated (Effect.returnFromGraveyardTapped) (ManaCost.ofGenericAndColor 2 .black)
          (activateFromGraveyard := true) (onlyIfYouControlLegendary := true),
  activated (Effect.searchBasicLandTapped) (ManaCost.ofGeneric 2)
          (tap := true) (sacrificeSource := true),
  activated (Effect.dealDamageToTargetCreature 2) (ManaCost.ofGeneric 1)
          (sacrificeSource := true)
          (otherModes := #[Effect.destroyTargetColorlessNonland]),
  activated (Effect.targetCantBeBlockedPowerAtMost 2) (tap := true),
  activated (Effect.abilityScry 2) (ManaCost.ofGenericAndColor 1 .blue) (tap := true)
          (onlyIfYouControlLegendary := true),
  activated (Effect.abilityDrawThenDiscard 2) (ManaCost.ofGeneric 3) (tap := true),
  activated (Effect.abilityCreateTokensX .treasure) { symbols := #[.x, .x] }
          (tap := true) (sacrificeSource := true),
  activated (Effect.abilityDraw 1) (ManaCost.ofGenericAndColor 1 .white) (tap := true)
          (onlyIfYouAttackedWithTwoOrMore := true),
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
          (onlyAsSorcery := true),
  activated (Effect.blackGateUnblockable) (ManaCost.ofGenericAndColor 1 .black) (tap := true),
  activated (Effect.burdenThenDraw) (tap := true),
  activated (Effect.teamGain Keyword.doubleStrike) (ManaCost.ofGeneric 10),
  activated (Effect.sourceGainsIndestructibleTap) (discardACard := true),
  activated (Effect.plusOneOnEachOtherSubtype "Hero" 1) (ManaCost.empty) (tap := true),
  typecyclingAbility "Basic land" (ManaCost.ofGeneric 2),
  powerUpAbility (Effect.putPlusOnePlusOneOnSource 2) (ManaCost.ofGenericAndColor 4 .white),
  activated (Effect.plusOneAndIndestructibleCounter) (ManaCost.ofGenericAndColors 5 [.white, .white]) (powerUp := true),
  activated (Effect.pumpAttackingAloneGainLife) (ManaCost.empty) (tap := true),
  activated (Effect.transform) (ManaCost.ofGenericAndColors 3 [.green, .white, .white]) (onlyAsSorcery := true),
  activated (Effect.harnessInfinityStone) (ManaCost.ofGenericAndColor 5 .white) (tap := true),
  activated (Effect.transform) (ManaCost.ofGenericAndColors 2 [.red, .white, .white]) (onlyAsSorcery := true),
  activated (Effect.lookAtTopPutTypes 7 #["Hero", "Equipment", "Vehicle"]) (ManaCost.ofColors [.white, .blue, .black, .red, .green]) (powerUp := true),
  activated (Effect.anotherYouControlGetsAndGrant 2 0 Keyword.hexproof) (ManaCost.ofGeneric 2) (tap := true),
  activated (Effect.tapTargetCreature) (ManaCost.ofGeneric 2) (tap := true)
        (costReductionIfTargetPowerAtMost := some (1, 3)),
  powerUpAbility (Effect.putPlusOnePlusOneOnSource 3) (ManaCost.ofGenericAndColor 5 .blue),
  activated (Effect.plusOneAndDraw 1 2) (ManaCost.ofGenericAndColor 5 .blue) (powerUp := true),
  activated (Effect.drawX) ({ symbols := #[.x, .x] }) (tap := true) (onlyAsSorcery := true),
  activated (Effect.transform) (ManaCost.ofGenericAndColors 2 [.red, .red, .green, .green]) (onlyAsSorcery := true),
  activated (Effect.copyControlledAbility true) (ManaCost.ofGeneric 1) (tap := true),
  equipAbility (ManaCost.ofGenericAndColor 2 .blue),
  activated (Effect.abilityDraw 2) (ManaCost.ofGenericAndColor 3 .blue) (sacrificeSource := true),
  activated (Effect.addBlueCantNonartifact) (ManaCost.empty) (tap := true),
  activated (Effect.revealTopDrawIfArtifact) (ManaCost.empty) (tap := true),
  activated (Effect.plusOneAndExtraTurn) (ManaCost.ofGenericAndColors 5 [.blue, .blue, .blue]) (powerUp := true),
  activated (Effect.copyArtifactYouControlNotLegendary) (ManaCost.ofGeneric 1) (tap := true) (onlyAsSorcery := true),
  activated (Effect.plusOneX) ({ symbols := #[.x, .colored .blue, .colored .blue] }) (powerUp := true),
  activated (Effect.lookAtTopRevealArtifact 4) (ManaCost.ofGeneric 1) (tap := true),
  activated (Effect.transform) (ManaCost.ofGenericAndColors 4 [.blue, .red]) (onlyAsSorcery := true),
  activated (Effect.createTappedTokens .villain21menace 1) (ManaCost.ofGeneric 3) (tap := true)
        (onlyIfGyCreaturesAtLeast := 2),
  activated (Effect.abilityDraw 1) (ManaCost.ofGenericAndColor 2 .black)
        (sacrificeArtifactOrCreature := true),
  activated (Effect.searchLandTypeToHand "Plan") (ManaCost.ofGenericAndColor 1 .black)
        (discardSource := true) (activateFromHand := true),
  activated (Effect.connive) (payLife := 3) (onlyDuringYourTurn := true),
  activated (Effect.eachOppDiscardThenPlusOne) (ManaCost.ofGenericAndColor 4 .black) (powerUp := true),
  activated (Effect.returnFromGraveyardToHand) (ManaCost.ofGenericAndColor 2 .black),
  activated (Effect.addTwoAnyColorEquipment) (payLife := 2) (onceEachTurn := true),
  activated (Effect.targetGets (-4) (-4)) (tap := true) (sacrificeEquipmentAttachedToSource := true)
          (onlyAsSorcery := true),
  activated (Effect.abilityCreateTokens .wall04defender 1) (ManaCost.ofGenericAndColor 2 .white),
  activated (Effect.sourceGets 4 4) (ManaCost.ofGenericAndColor 3 .green),
  activated (Effect.dealDamageToTargetCreature 4) (ManaCost.ofGenericAndColor 4 .red),
  activated (Effect.abilityTargetPlayerDraw 4) (ManaCost.ofGenericAndColor 5 .blue),
  activated (Effect.returnGyCreatureThenPlusOne 2) (ManaCost.ofGenericAndColors 5 [.black, .black]) (powerUp := true),
  powerUpAbility (Effect.putPlusOnePlusOneOnSource 3) (ManaCost.ofGenericAndColor 6 .red),
  activated (Effect.exileTopXPlayThisTurn) (tap := true) (putStunCounterOnSource := true),
  activated (Effect.nextInstantSorceryCopyIfMvAtMostSourcePower) (ManaCost.ofGeneric 1) (tap := true),
  powerUpAbility (Effect.putPlusOnePlusOneOnSource 2) (ManaCost.ofGenericAndColor 4 .red),
  activated (Effect.drawPerDiscardedThisTurn)
        (ManaCost.ofGeneric 2) (tap := true) (discardACard := true),
  equipWorthyAbility (ManaCost.ofGeneric 1),
  activated (Effect.abilityDealDamageToEachCreature 2) (ManaCost.ofGenericAndColor 2 .red)
          (discardSource := true) (activateFromHand := true),
  activated (Effect.plusOneAndDoubleStrikeCounter) (ManaCost.ofGenericAndColor 4 .red) (powerUp := true),
  activated (Effect.abilityCreateTokens .treasure 1) (ManaCost.ofGeneric 2) (tap := true),
  powerUpAbility (Effect.putPlusOnePlusOneOnSource 2) (ManaCost.ofGenericAndColor 5 .red),
  powerUpAbility (Effect.putPlusOnePlusOneOnSource 2) (ManaCost.ofGenericAndColors 5 [.red, .red]),
  activated (Effect.addAnyColorEqualToSourcePower) (ManaCost.empty) (tap := true),
  activated (Effect.destroyTargetNoncreatureArtOrEnch)
        (sacrificeSource := true) (onlyAsSorcery := true),
  activated (Effect.plusOneAndGrant ((Keyword.vigilance.merge Keyword.indestructible).merge Keyword.haste)) (ManaCost.ofGenericAndColor 4 .green) (powerUp := true),
  activated (Effect.plusOneAndCreateTokens 1 .hero32vigilance) (ManaCost.ofGenericAndColor 6 .green) (powerUp := true),
  activated (Effect.proliferateEachKind) (ManaCost.empty) (tap := true) (onlyAsSorcery := true),
  activated (Effect.becomeTypes #["Dinosaur", "Hero"] 3 5 (Keyword.reach.merge Keyword.vigilance)) (ManaCost.ofGeneric 3),
  activated (Effect.becomeTypes #["Dinosaur", "Hero"] 6 6 Keyword.trample) (ManaCost.ofGeneric 6),
  activated (Effect.millThenPutSubtypeOrEnchantment 4 "Hero") (ManaCost.ofGeneric 3) (tap := true),
  powerUpAbility (Effect.putPlusOnePlusOneOnSource 2) (ManaCost.ofGenericAndColor 3 .green),
  activated (Effect.addTwoAnyColorCreatureSources) (ManaCost.empty) (tap := true),
  activated (Effect.destroyUpToOneThenPlusOne) (ManaCost.ofGenericAndColors 4 [.green, .green]) (powerUp := true),
  activated (Effect.createTokensEqualSubtype .squirrel11green "Squirrel") (ManaCost.ofGenericAndColors 1 [.green, .green, .green]),
  activated (Effect.addAnyColor) (ManaCost.empty) (tap := true),
  activated (Effect.plusOneAndCreateTigerGod) (ManaCost.ofGenericAndColor 5 .green) (powerUp := true),
  activated (Effect.plusOneThenFightUpToOne) (ManaCost.ofGenericAndHybrids 5 .red .green 2) (powerUp := true),
  activated (Effect.createTokensEqualRemovedPlusOnes .insect11green)
        (ManaCost.ofGenericAndColor 2 .green) (tap := true) (removeAnyNumberPlusOne := true),
  activated (Effect.dealDamageToAny 2) (ManaCost.ofGeneric 3)
        (tap := true) (sacrificeArtifactOrDiscardNonland := true),
  powerUpAbility (Effect.putPlusOnePlusOneOnSource 5) (ManaCost.ofGenericAndColors 6 [.red, .green]),
  activated (Effect.transform) (ManaCost.ofGenericAndColors 4 [.white, .blue]) (onlyAsSorcery := true),
  activated (Effect.copyControlledAbility false)
        (payLife := 2) (onlyDuringYourTurn := true) (onceEachTurn := true),
  activated (Effect.plusTwoThenOddEvenDestroy) ({ symbols := #[.colorless, .colored .white, .colored .blue, .colored .black, .colored .red, .colored .green] }) (powerUp := true),
  activated (Effect.returnFromGyFinalityAttach) (ManaCost.ofGenericAndColors 3 [.white, .black])
        (activateFromGraveyard := true),
  activated (Effect.addMana #[.colorless, .colorless, .colorless]) (ManaCost.empty) (tap := true),
  activated (Effect.equipmentBecomesConstructHero) (ManaCost.ofGeneric 2),
  activated (Effect.plusOneAndCreateTokens 2 .robotVillain22) (ManaCost.ofGeneric 6) (powerUp := true),
  powerUpAbility (Effect.putPlusOnePlusOneOnSource 2) (ManaCost.ofGeneric 7),
  activated (Effect.addAnyColorSpendOnlySubtype "Hero") (ManaCost.empty) (tap := true),
  activated (Effect.lookAtTopRevealSubtype 3 "Hero") (ManaCost.ofGeneric 4) (tap := true),
  activated (Effect.addFourAnyCombination) (ManaCost.ofGeneric 4) (tap := true),
  activated (Effect.abilityDraw 1) (ManaCost.ofGeneric 4) (tap := true)
          (onlyIfYouControlCreatureToughnessAtLeast := 4),
  activated (Effect.addAnyColorSpendOnlyArtifactSpell) (ManaCost.empty) (tap := true),
  activated (Effect.abilityCreateTokens .doombot 1) (ManaCost.ofGeneric 3) (tap := true)
          (sacrificeArtifact := true) (onlyAsSorcery := true),
  activated (Effect.targetSubtypeConnives "Villain") (ManaCost.ofGeneric 3) (tap := true) (onlyAsSorcery := true),
  {
      cost := { mana := ManaCost.ofGeneric 2, sacrificeSource := true },
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
          (activateFromGraveyard := true) (onlyIfOpponentDealtNoncombatDamage := true),
  activated (Effect.tapAndStunTargetCreature) (ManaCost.ofGenericAndColor 3 .blue)
          (activateFromGraveyard := true) (exileSourceFromGraveyard := true)
          (onlyAsSorcery := true),
  activated (Effect.abilityEmpowerJace 2) (ManaCost.ofGeneric 1)
          (activateFromGraveyard := true) (exileSourceFromGraveyard := true),
  ActivatedAbility.fra
    "{3}, Exile this card from your hand: Target land gains \"{T}: Add {C}{C}\" until this card is cast from exile. You may cast this card for as long as it remains exiled."
    (FraCandidates.ab (.fra .emrakulGrantMana) "Target land gains \"{T}: Add {C}{C}\" until this card is cast from exile. You may cast this card for as long as it remains exiled"
      (.filtered { noun := "target land", types := #[.land] }))
    { mana := ManaCost.ofGeneric 3, fra := .exileSourceFromHand } (activateFromHand := true),
  ActivatedAbility.fra "{4}{W}: Creatures you control get +1/+1 until end of turn."
    (FraCandidates.ab (.creaturesYouControlPump 1 1) "Creatures you control get +1/+1 until end of turn")
    { mana := ⟨#[.generic 4, .colored .white]⟩ },
  ActivatedAbility.fra "{3}{U}{U}, Exile this card from your graveyard: Draw two cards."
    (FraCandidates.ab (.draw 2) "Draw two cards")
    { mana := ⟨#[.generic 3, .colored .blue, .colored .blue]⟩, exileSourceFromGraveyard := true }
    (activateFromGraveyard := true),
  ActivatedAbility.fra "{3}{U}: Surveil 1." (FraCandidates.ab (.surveil 1) "Surveil 1")
    { mana := ⟨#[.generic 3, .colored .blue]⟩ },
  ActivatedAbility.fra "{U}, Sacrifice this creature: The next spell you cast this turn can't be countered."
    (FraCandidates.ab (.fra .nextSpellCantBeCountered) "The next spell you cast this turn can't be countered")
    { mana := ⟨#[.colored .blue]⟩, sacrificeSource := true },
  ActivatedAbility.fra "{2}: This creature gets +1/-1 until end of turn."
    (FraCandidates.ab (.onSource (.pump 1 (-1))) "This creature gets +1/-1 until end of turn")
    { mana := ManaCost.ofGeneric 2 },
  ActivatedAbility.fra "{3}{B}, Exile this card from your graveyard: Return another target creature card from your graveyard to your hand."
    (FraCandidates.ab (.fra .returnFromGyToHand) "Return another target creature card from your graveyard to your hand"
      (.filtered { noun := "another target creature card from your graveyard", zone := .yourGraveyard
                   types := #[.creature], another := true }))
    { mana := ⟨#[.generic 3, .colored .black]⟩, exileSourceFromGraveyard := true }
    (activateFromGraveyard := true),
  ActivatedAbility.fra "{T}, Discard a card: Draw a card." (FraCandidates.ab (.draw 1) "Draw a card")
    { tap := true, discardACard := true },
  ActivatedAbility.fra
    "{3}{R}: Exile target creature or planeswalker you control. Reveal cards from the top of your library until you reveal a creature or planeswalker card. Put that card onto the battlefield and the rest on the bottom of your library in a random order. Activate only as a sorcery."
    (FraCandidates.ab (.fra .identityEcho) "Exile target creature or planeswalker you control"
      (.filtered { TargetFilter.creatureOrPlaneswalker with
        noun := "target creature or planeswalker you control", controller := .you }))
    { mana := ⟨#[.generic 3, .colored .red]⟩ } (onlyAsSorcery := true),
  ActivatedAbility.fra
    "Sacrifice this creature: Destroy target artifact or enchantment. If that permanent was a legendary enchantment, draw a card. Activate only as a sorcery."
    (FraCandidates.ab (.fra .destroyDrawIfLegendaryEnchantment) "Destroy target artifact or enchantment"
      (.filtered { noun := "target artifact or enchantment", types := #[.artifact, .enchantment] }))
    { sacrificeSource := true } (onlyAsSorcery := true),
  ActivatedAbility.fra
    "{1}, Sacrifice another artifact: Put a +1/+1 counter on this creature. It gains your choice of trample, hexproof, or haste until end of turn."
    (FraCandidates.ab (.fra (.plusOneThenChooseKeyword [0, 1, 2])) "Put a +1/+1 counter on this creature")
    { mana := ManaCost.ofGeneric 1, fra := .sacrificeAnotherArtifact },
  ActivatedAbility.fra "{4}{G}: Return this card from your graveyard to your hand."
    (FraCandidates.ab .returnFromGraveyardToHand "Return this card from your graveyard to your hand")
    { mana := ⟨#[.generic 4, .colored .green]⟩ } (activateFromGraveyard := true),
  ActivatedAbility.fra "{3}{G}, Discard this card: Destroy target creature with flying."
    (FraCandidates.ab (.fra .destroy) "Destroy target creature with flying"
      (.filtered { TargetFilter.creature with noun := "target creature with flying", withFlying := true }))
    { mana := ⟨#[.generic 3, .colored .green]⟩, discardSource := true } (activateFromHand := true),
  ActivatedAbility.fra "{6}{G}{G}: This creature gets +4/+4 and gains trample until end of turn."
    (FraCandidates.ab (.onSource (.pumpAndTrample 4 4)) "This creature gets +4/+4 and gains trample until end of turn")
    { mana := ⟨#[.generic 6, .colored .green, .colored .green]⟩ },
  ActivatedAbility.fra
    "{6}: Create a Heartwood token. Then this creature gets +X/+0 until end of turn, where X is the number of artifacts you control."
    (FraCandidates.ab (.sequence [.createTokens .heartwood 1, .fra .sourceGetsPowerPerArtifact])
      "Create a Heartwood token")
    { mana := ManaCost.ofGeneric 6 },
  ActivatedAbility.fra "{2}{W/B}: Return this card from your graveyard to your hand."
    (FraCandidates.ab .returnFromGraveyardToHand "Return this card from your graveyard to your hand")
    { mana := ⟨#[.generic 2, .hybrid .white .black]⟩ } (activateFromGraveyard := true),
  ActivatedAbility.fra "{4}{G}{W}: Target creature gains trample and lifelink until end of turn."
    (FraCandidates.ab (.onPermanent (.grantKeywords (Keyword.trample.merge Keyword.lifelink)))
      "Target creature gains trample and lifelink until end of turn" (.filtered TargetFilter.creature))
    { mana := ⟨#[.generic 4, .colored .green, .colored .white]⟩ },
  ActivatedAbility.fra
    "{4}: Create a 2/2 colorless Wizard Soldier creature token named Cadet. Then creatures you control gain haste until end of turn."
    (FraCandidates.ab (.sequence [.createTokens .cadet 1, .teamGain Keyword.haste]) "Create a Cadet")
    { mana := ManaCost.ofGeneric 4 },
  ActivatedAbility.fra "{2}: Put target card from your graveyard on the bottom of your library."
    (FraCandidates.ab (.fra .graveyardCardToLibraryBottom) "Put target card from your graveyard on the bottom of your library"
      (.filtered { noun := "target card from your graveyard", zone := .yourGraveyard }))
    { mana := ManaCost.ofGeneric 2 },
  ActivatedAbility.fra
    "{W}{U}: Return this card from your graveyard to the battlefield with a finality counter on it. Activate only if you've scried or surveilled this turn."
    (FraCandidates.ab .returnFromGyWithFinality "Return this card from your graveyard to the battlefield with a finality counter on it")
    { mana := ⟨#[.colored .white, .colored .blue]⟩ } (activateFromGraveyard := true)
    (cond := .scriedOrSurveilledThisTurn),
  ActivatedAbility.fra "{1}, {T}, Discard a legendary card: Draw a card." (FraCandidates.ab (.draw 1) "Draw a card")
    { mana := ManaCost.ofGeneric 1, tap := true, fra := .discardLegendaryCard },
  ActivatedAbility.fra "Tap two untapped artifacts you control: Put two +1/+1 counters on this creature."
    (FraCandidates.ab (.onSource (.plusOne 2)) "Put two +1/+1 counters on this creature")
    { fra := .tapTwoUntappedArtifacts },
  { ActivatedAbility.fra
      "Equip {3}. This ability costs {1} less to activate for each +1/+1 counter on the creature it targets."
      Effect.attachToTargetCreatureYouControl { mana := ManaCost.ofGeneric 3 } (onlyAsSorcery := true)
    with costLessPerPlusOneOnTarget := true },
  ActivatedAbility.fra "{2}: This creature gains flying until end of turn."
    (FraCandidates.ab (.onSource (.grantKeywords Keyword.flying)) "This creature gains flying until end of turn")
    { mana := ManaCost.ofGeneric 2 },
  ActivatedAbility.fra "{5}, {T}, Exile this artifact: Destroy all creatures. Activate only as a sorcery."
    (FraCandidates.ab (.fra .destroyAllCreatures) "Destroy all creatures")
    { mana := ManaCost.ofGeneric 5, tap := true, fra := .exileSource } (onlyAsSorcery := true),
  ActivatedAbility.fra
    "{6}, Sacrifice this creature: Choose target creature or planeswalker an opponent controls. Its owner shuffles it into their library."
    (FraCandidates.ab (.fra .ownerShufflesIntoLibrary) "Its owner shuffles it into their library"
      (.filtered TargetFilter.oppCreatureOrPlaneswalker))
    { mana := ManaCost.ofGeneric 6, sacrificeSource := true },
  ActivatedAbility.fra "{2}, {T}, Discard a card: Draw a card." (FraCandidates.ab (.draw 1) "Draw a card")
    { mana := ManaCost.ofGeneric 2, tap := true, discardACard := true },
  ActivatedAbility.fra
    "{2}, {T}: Target creature that attacked this turn becomes prepared. Activate only as a sorcery."
    (FraCandidates.ab (.onPermanent .becomePrepared) "Target creature that attacked this turn becomes prepared"
      (.filtered { TargetFilter.creature with noun := "target creature that attacked this turn", attackedThisTurn := true }))
    { mana := ManaCost.ofGeneric 2, tap := true } (onlyAsSorcery := true),
  ActivatedAbility.fra "{1}{W}, Discard this card: It deals 4 damage to target attacking or blocking creature."
    (FraCandidates.ab (.onPermanent (.dealDamage 4)) "It deals 4 damage to target attacking or blocking creature"
      (.filtered { TargetFilter.creature with noun := "target attacking or blocking creature", attackingOrBlocking := true }))
    { mana := ⟨#[.generic 1, .colored .white]⟩, discardSource := true } (activateFromHand := true),
  ActivatedAbility.fra
    "{1}, {T}, Discard a card: Another target creature or planeswalker you control gains hexproof until end of turn."
    (FraCandidates.ab (.onPermanent (.grantKeywords Keyword.hexproof)) "Another target creature or planeswalker you control gains hexproof until end of turn"
      (.filtered { TargetFilter.creatureOrPlaneswalker with
        noun := "another target creature or planeswalker you control", controller := .you, another := true }))
    { mana := ManaCost.ofGeneric 1, tap := true, discardACard := true },
  ActivatedAbility.fra "{T}: Return another target permanent you control to its owner's hand. Activate only during your turn."
    (FraCandidates.ab (.fra .bounce) "Return another target permanent you control to its owner's hand"
      (.filtered { noun := "another target permanent you control", controller := .you, another := true }))
    { tap := true } (onlyDuringYourTurn := true),
  ActivatedAbility.fra "{T}: Target creature with a +1/+1 counter on it gains flying until end of turn."
    (FraCandidates.ab (.onPermanent (.grantKeywords Keyword.flying)) "Target creature with a +1/+1 counter on it gains flying until end of turn"
      (.filtered { TargetFilter.creature with noun := "target creature with a +1/+1 counter on it", withPlusOneCounter := true }))
    { tap := true },
  ActivatedAbility.fra "{6}: Put a +1/+1 counter on target legendary creature."
    (FraCandidates.ab (.onPermanent (.plusOne 1)) "Put a +1/+1 counter on target legendary creature"
      (.filtered { TargetFilter.creature with noun := "target legendary creature", legendary := true }))
    { mana := ManaCost.ofGeneric 6 },
  ActivatedAbility.fra "{6}: Put a +1/+1 counter on target nonlegendary creature."
    (FraCandidates.ab (.onPermanent (.plusOne 1)) "Put a +1/+1 counter on target nonlegendary creature"
      (.filtered { TargetFilter.creature with noun := "target nonlegendary creature", nonlegendary := true }))
    { mana := ManaCost.ofGeneric 6 },
  ActivatedAbility.fra "{T}: Draw a card, then discard a card."
    (FraCandidates.ab (.sequence [.draw 1, .discard 1]) "Draw a card, then discard a card") { tap := true },
  ActivatedAbility.fra "{2}{U}: Untap target creature."
    (FraCandidates.ab (.onPermanent .untap) "Untap target creature" (.filtered TargetFilter.creature))
    { mana := ⟨#[.generic 2, .colored .blue]⟩ },
  ActivatedAbility.fra
    "{3}{U}{U}: Until end of turn, whenever this creature deals combat damage to a player, draw two cards."
    (FraCandidates.ab (.fra .grantCombatDamageDrawTwo) "Until end of turn, whenever this creature deals combat damage to a player, draw two cards")
    { mana := ⟨#[.generic 3, .colored .blue, .colored .blue]⟩ },
  ActivatedAbility.fra
    "{4}{B}, Exile another creature card from your graveyard: Return this card from your graveyard to the battlefield tapped with a +1/+1 counter on her."
    (FraCandidates.ab (.fra (.returnSourceFromGy false true 1)) "Return this card from your graveyard to the battlefield tapped")
    { mana := ⟨#[.generic 4, .colored .black]⟩, fra := .exileAnotherCreatureCardFromGraveyard }
    (activateFromGraveyard := true),
  ActivatedAbility.fra
    "{5}{B}: Return target creature or planeswalker card from your graveyard to the battlefield. Put a +1/+1 counter on this creature. Activate only as a sorcery."
    (FraCandidates.ab
      (.sequence [.fra (.returnFromGyToBattlefield 0), .onSource (.plusOne 1)])
      "Return target creature or planeswalker card from your graveyard to the battlefield"
      (.filtered { noun := "target creature or planeswalker card from your graveyard", zone := .yourGraveyard
                   types := #[.creature, .planeswalker] }))
    { mana := ⟨#[.generic 5, .colored .black]⟩ } (onlyAsSorcery := true) (exhaust := true),
  ActivatedAbility.fra
    "Sacrifice another creature or planeswalker: This creature gets -2/-0 until end of turn. Activate only if there are seven or more cards in your graveyard."
    (FraCandidates.ab (.onSource (.pump (-2) 0)) "This creature gets -2/-0 until end of turn")
    { fra := .sacrificeAnotherCreatureOrPlaneswalker } (cond := .graveyardAtLeast 7),
  ActivatedAbility.fra "{B}, Discard this card: Target creature gets -3/-1 until end of turn."
    (FraCandidates.ab (.onPermanent (.pump (-3) (-1))) "Target creature gets -3/-1 until end of turn" (.filtered TargetFilter.creature))
    { mana := ⟨#[.colored .black]⟩, discardSource := true } (activateFromHand := true),
  ActivatedAbility.fra "{1}{R}, {T}: Put a +1/+1 counter on target creature that entered this turn."
    (FraCandidates.ab (.onPermanent (.plusOne 1)) "Put a +1/+1 counter on target creature that entered this turn"
      (.filtered { TargetFilter.creature with noun := "target creature that entered this turn", enteredThisTurn := true }))
    { mana := ⟨#[.generic 1, .colored .red]⟩, tap := true },
  ActivatedAbility.fra "{8}: Create a 5/5 red Dragon creature token with flying."
    (FraCandidates.ab (.createTokens .dragon55flying 1) "Create a 5/5 red Dragon creature token with flying")
    { mana := ManaCost.ofGeneric 8 },
  ActivatedAbility.fra "{2}, {T}, Sacrifice an artifact or land: Draw a card." (FraCandidates.ab (.draw 1) "Draw a card")
    { mana := ManaCost.ofGeneric 2, tap := true, fra := .sacrificeArtifactOrLand },
  ActivatedAbility.fra
    "{5}{R}: Target creature gets +X/+0 until end of turn, where X is the number of artifacts you control."
    (FraCandidates.ab (.fra .pumpPerArtifact) "Target creature gets +X/+0 until end of turn" (.filtered TargetFilter.creature))
    { mana := ⟨#[.generic 5, .colored .red]⟩ },
  ActivatedAbility.fra "{4}{G}: Put a +1/+1 counter on each creature you control with a +1/+1 counter on it."
    (FraCandidates.ab (.fra .plusOneOnEachWithPlusOne) "Put a +1/+1 counter on each creature you control with a +1/+1 counter on it")
    { mana := ⟨#[.generic 4, .colored .green]⟩ },
  ActivatedAbility.fra "{2}: Return target land card from your graveyard to your hand."
    (FraCandidates.ab (.fra .returnFromGyToHand) "Return target land card from your graveyard to your hand"
      (.filtered { noun := "target land card from your graveyard", zone := .yourGraveyard, types := #[.land] }))
    { mana := ManaCost.ofGeneric 2 },
  ActivatedAbility.fra
    "{2}, Sacrifice another creature or planeswalker: Put a +1/+1 counter on this creature. He gains menace until end of turn."
    (FraCandidates.ab (.sequence [.onSource (.plusOne 1), .onSource (.grantKeywords Keyword.menace)]) "Put a +1/+1 counter on this creature")
    { mana := ManaCost.ofGeneric 2, fra := .sacrificeAnotherCreatureOrPlaneswalker },
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
  ("Creatures you control get +1/+1 and gain vigilance until end of turn.", Effect.creaturesYouControlGetAndGrant 1 1 Keyword.vigilance),
  ("Target creature you control fights up to one other target creature.", Effect.fightUpToOne),
]

end Mtg.Engine.OracleCandidates
