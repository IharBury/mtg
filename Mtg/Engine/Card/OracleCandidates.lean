import Mtg.Engine.Card.OracleActivate
import Mtg.Engine.Card.SpellEffects

/-!
Modeled abilities the Oracle parser can recognize. Each entry is a shape.
`Nat`, `Int`, `String`, and target-kind arguments are read from the card's
own Oracle text, so a prototype such as `Effect.draw 1` also matches “Draw
seven cards,” and `Effect.destroyCreature` also matches “Destroy target
artifact.” Each list keeps one prototype per shape. Another entry that
differs only by those arguments is the same ability, so it is not listed again.
A spell whose text is several of these shapes in a row is parsed as an
`Instruction.seq` of those shapes, so the sequence itself is not listed.
“Draw N cards, then discard a card” is `draw` followed by `discardCards`,
so that sentence is not listed either.
-/

namespace Mtg.Engine.OracleCandidates

open Mtg.Engine
open Mtg.Engine.OracleActivate

def spellEffectEntries : Thunk (Array (Option String × Effect)) := Thunk.mk fun _ => #[
  (none, Effect.searchBasicLandTapped),
  (none, Effect.sourceGets 1 1),
  (none, Effect.amassGoblins 1),
  (none, Effect.searchLandTypeToHand "Mountain"),
  (none, Effect.tapScryDraw 1 1),
  (some "Exile all attacking creatures target player controls. That player may search their library for that many basic land cards, put those cards onto the battlefield tapped, then shuffle.", Effect.exileAttackersSearchBasics),
  (none, Effect.dealDamage 3),
  (none, Effect.draw 1),
  (none, Effect.discardCards 1),
  (none, Effect.searchTwoBasicsSplit),
  (none, Effect.targetCantBeBlockedPowerAtMost 2),
  (none, Effect.playAdditionalLandThisTurn),
  (none, Effect.becomeBearCreatureWithLandsPT),
  (some "Choose a creature type. Return all creatures that aren't of the chosen type to their owners' hands.", Effect.chooseTypeReturnOthers),
  (none, Effect.returnFromGyAttachPowerAtMost 1),
  (none, Effect.putOnTopOrBottom),
  (none, Effect.transform),
  (none, Effect.harnessInfinityStone),
  (none, Effect.drawThreeDiscardUnlessArtifact),
  (none, Effect.pump 3 3),
  (none, Effect.addAnyColorSpendOnlyHero),
  (none, Effect.returnFromGyFinalityAttach),
  (none, Effect.watchEnchantedAttachEquipment),
  (none, Effect.plusOneAndDraw 1 2),
  (none, Effect.abilityDraw 1),
  (none, Effect.addTwoAnyColorCreatureSources),
  (none, Effect.watchVillainConniveOnce),
  (none, Effect.grantVigilanceUnblockable),
  (none, Effect.pumpThenExileTopPlay 3 1),
  (some "This spell deals 5 damage to target creature. If this spell was cast using teamwork, it also deals 2 damage to that creature's controller.", Effect.dealDamageThenControllerIfTeamwork 5 2),
  (some "Exile target creature with mana value 3 or less. If this spell was cast using teamwork, instead exile target creature and you gain 3 life.", Effect.exileCreatureMvAtMostOrAnyIfTeamwork 3 3),
  (none, Effect.pumpAttackingAloneGainLife),
  (none, Effect.stepCopyAbsorbingMan),
  (none, Effect.stepCopyTaskmaster),
  (none, Effect.becomeArtifactCreature44Flying),
  (none, Effect.enterTapOppCantUntapWhileControl),
  (none, Effect.watchHulklingCompare),
  (none, Effect.plusOneAndCreateTigerGod),
  (some "Double target creature's power and toughness until end of turn.", Effect.doublePowerAndToughness),
  (none, Effect.addBlueCantNonartifact),
  (none, Effect.watchFirstTapUntap),
  (none, Effect.watchEquippedTappedDamage),
  (none, Effect.enterRevealHandExileUntilLeaves),
  (none, Effect.copyArtifactYouControlNotLegendary),
  (none, Effect.watchSheHulkRedirectOnce),
  (none, Effect.thisAttackDrawIfPower4),
  (none, Effect.exileTopXPlayThisTurn),
  (none, Effect.thisAttackEquippedDrain),
  (none, Effect.enterMaySacOrDiscardNonlandThenDamage),
  (none, Effect.enterMayTapThenGrantIndestructible),
  (none, Effect.watchHawkeyeModes),
  (none, Effect.thisAttackPayReturnAttacking),
  (none, Effect.enterMaySacAnotherThenDestroyOppNonland),
  (none, Effect.watchRedHulk),
  (none, Effect.castingMayPayHasteUnblockable),
  (none, Effect.watchSpeedballTargeted),
  (none, Effect.youAttackingPay2LifeToughness),
  (none, Effect.drawPerDiscardedThisTurn),
  (none, Effect.deathAttackingReturnHand),
  (none, Effect.enterDestroy .oppCreatureDealtDamageThisTurn),
  (none, Effect.equipmentBecomesConstructHero),
  (none, Effect.youAttackingExileTopHeroPump),
  (none, Effect.watchVillainPlusOneDamageOnce),
  (none, Effect.createTokensEqualSubtype .squirrel11green "Squirrel"),
  (none, Effect.enterTapLoseAbilitiesWhileSource),
  (none, Effect.chapterGainControlOfUpToTwoCreaturesTotalMvAtMost 6),
  (none, Effect.nextInstantSorceryCopyIfMvAtMostSourcePower),
  (none, Effect.deathVillainReturnAsHero),
  (none, Effect.castingIronFistTap),
  (none, Effect.creatureYouControlDealsPowerToOppCreature),
  (none, Effect.enterRevealDiscardFromHand),
  (none, Effect.watchUltronCopy),
  (none, Effect.castingVisionModes),
  (none, Effect.watchVillainAttachEquipment),
  (none, Effect.stepHydeChoose),
  (none, Effect.resourceDrawIfAnotherHeroDamage),
  (none, Effect.becomeDinosaurHero 3 5 #[Keyword.reach, Keyword.vigilance]),
  (none, Effect.becomeDinosaurHero 6 6 #[Keyword.trample]),
  (none, Effect.enterChooseUpToXModes),
  (none, Effect.resourceSecondDrawBecome66),
  (none, Effect.createTappedTokens .villain21menace 1),
  (none, Effect.stepDrawToTen),
  (none, Effect.nextFreeRGCreature),
  (none, Effect.youAttackingLookSixCast),
  (none, Effect.plusOneX),
  (none, Effect.attachToTargetCreatureYouControl),
  (none, Effect.targetCantBeBlockedThisTurn),
  (none, Effect.gainLife 3),
  (none, Effect.dealDamageToCreature 5),
  (none, Effect.putPlusOnePlusOneOnSource 1),
  (none, Effect.enterExileGyPlayUntilNextTurn),
  (none, Effect.enterFightUpToOne),
  (none, Effect.enterReturnNonlandNontoken),
  (some "This spell deals 3 damage to target creature. That creature loses indestructible until end of turn. If that creature would die this turn, exile it instead.", Effect.dealDamageLoseIndestructibleExile 3),
  (none, Effect.destroyCreature),
  (some "Destroy target artifact or land. Creatures without flying can't block this turn.", Effect.destroyArtifactOrLandNonflyersCantBlock),
  (none, Effect.plusOnePlusOneTrampleHexproof),
  (some "Untap target creature you control. It gets +2/+2 until end of turn. If it's a Dwarf, you may attach an Equipment you control to it.", Effect.untapPumpMaybeAttach 2 2),
  (none, Effect.castingPlusOneScry),
  (none, Effect.stepEnchantedControllerDraws),
  (none, Effect.thisAttackAttacksAlonePlus2Indestructible),
  (none, Effect.castingPlusOneThis),
  (none, Effect.watchNontokenHeroModal),
  (none, Effect.resourceSecondDrawDrain),
  (none, Effect.deathHellcatReturn),
  (none, Effect.plusOneUpToOneAndPlayerGainsLife 2),
  (none, Effect.drawAndLoseLife 2 2),
  (none, Effect.drawLoseLifeThenAmass 2),
  (none, Effect.ownerShuffleSourceDraw 3),
  (none, Effect.creaturesYouControlGetOppsLoseLife 2 0 2),
  (none, Effect.plusOneAndCreateTokens 2 .robotVillain22),
  (none, Effect.subtypesGainMenace #["Goblin", "Orc"]),
  (none, Effect.subtypesGainMenace #["Elf"]),
  (none, Effect.teamGain #[Keyword.menace]),
  (none, Effect.amassGoblinsOrFromGy 1 3),
  (some "Exile the top card of your library. Until the end of your next turn, you may play that card.", Effect.exileTopPlayUntilEndOfNextTurn),
  (none, Effect.tapOneOrTwoCreatures),
  (none, Effect.grantHexproofIndestructible),
  (none, Effect.abilityCreaturesYouControlGet 1 1),
  (none, Effect.scry 2),
  (none, Effect.abilitySurveil 1),
  (none, Effect.counterUnlessPays 4),
  (some "Counter target spell. If a permanent spell is countered this way, exile it instead of putting it into its owner's graveyard. You may cast that card without paying its mana cost for as long as it remains exiled.", Effect.counterExilePermanentMayCast),
  (some "Exchange control of two target nonland permanents that share a card type.", Effect.exchangeControlSharingType),
  (none, Effect.returnFromGraveyardToHand),
  (none, Effect.pumpAndExileIfDies (-5) (-5)),
  (none, Effect.creaturesTargetPlayerGet (-1) (-1)),
  (none, Effect.targetPlayerDrawLoseLife 2 2),
  (none, Effect.pumpAndLifelink 2 2),
  (none, Effect.pumpAndGrantKeywords 3 0 #[Keyword.reach, Keyword.firstStrike]),
  (none, Effect.creaturesYouControlGet 2 1),
  (none, Effect.destroyArtifactOrEnchantmentGainLife 2),
  (some "Until end of turn, target creature becomes an artifact in addition to its other types and gains indestructible.", Effect.becomeArtifactGainIndestructible),
  (none, Effect.addAnyColor),
  (none, Effect.returnCreatureFromGyThenAmass 3),
  (some "Counter target spell. If that spell's mana value was 2 or less, recruit.", Effect.counterThenRecruitIfMvAtMost 2),
  (some "Put a +1/+1 counter on target creature you control. If this spell was cast from a graveyard, also put a +1/+1 counter on each other creature you control.", Effect.plusOneThenEachOtherIfFromGy),
  (none, Effect.drawIfFromGy 1 2),
  (some "Put two +1/+1 counters on target creature you control. Then it fights target creature an opponent controls.", Effect.plusOneThenFight 2),
  (none, Effect.searchLegendaryCreatureToHand),
  (none, Effect.addMana #[.colored .black, .colored .red]),
  (some "Mill four cards, then put an instant or sorcery card from among them into your hand.", Effect.millThenPutInstantOrSorcery 4),
  (some "Exile two target creatures and/or lands you control, then return them to the battlefield under their owner's control.", Effect.exileThenReturnYouControl),
  (some "This spell deals 3 damage to target creature. If that creature would die this turn, exile it instead.", Effect.dealDamageToCreatureExileIfDies 3),
  (none, Effect.abilityCreateTokens .dwarf 1),
  (some "Mill four cards, then put up to two land cards from among them into your hand.", Effect.millThenPutLands 4 2),
  (none, Effect.dealDamageToEachOppCreature 1),
  (none, Effect.dealDamageToEachNonDragonThenAddDragonMana 3),
  (some "Mill six cards, then put all instant and sorcery cards from among them into your hand.", Effect.millThenPutAllInstantsOrSorceries 6),
  (some "Look at the top two cards of your library and exile them face down. For as long as they remain exiled, you may play them if you control a Wizard.", Effect.exileTopPlayIfYouControlSubtype 2 "Wizard"),
  (none, Effect.createTokensX .dwarf),
  (some "Return target spell to its owner's hand. If the gift was promised, players can't cast spells this turn.", Effect.returnSpellCantCastIfGift),
  (none, Effect.chapterDealDamageToOppCreature 6),
  (none, Effect.chapterDestroyOppArtifact),
  (none, Effect.chapterAddMana (.colored .red)),
  (none, Effect.chapterSearchBasicLandToHand),
  (none, Effect.chapterGainLandfallCreateElf),
  (none, Effect.chapterElvesGetVigilance 1),
  (none, Effect.chapterOpponentDiscardsNonland),
  (none, Effect.chapterAmassGoblins 1),
  (none, Effect.chapterOpponentLosesYouGain 1),
  (none, Effect.exileThenReturnNextEnd),
  (none, Effect.searchBasicBeholdSubtypeUntap "Elf"),
  (none, Effect.twoPlayersDraw),
  (some "Exile the top X cards of target opponent's library. You may play those cards this turn. If you cast a spell this way, pay life equal to its mana value rather than pay its mana cost.", Effect.exileTopXOppPlayForLife),
  (none, Effect.discardLegendarySameNameDraw),
  (none, Effect.chapterGrantHexproofWhileRemains),
  (none, Effect.chapterPreventDamageWhileRemains),
  (none, Effect.chapterDraw 1),
  (none, Effect.riddlesInTheDark),
  (none, Effect.chapterSearchBasicPlainsExileGainLife 2 2),
  (none, Effect.chapterReturnLinkedExileToHand),
  (none, Effect.chapterGrantAttackPumpPerPlainsThisTurn),
  (none, Effect.chapterBlinkUntilEndStep),
  (some "Put onto the battlefield under your control all creature cards in your opponents' graveyards that were put there from the battlefield this turn. They are Food artifacts with \"{2}, {T}, Sacrifice this artifact: You gain 3 life.\"", Effect.supperForSpiders),
  (some "Choose target creature you own. If this spell was kicked, instead choose any number of target creatures you own. Return each chosen creature to your hand. At the beginning of the next upkeep, create a 4/4 white Bird Soldier creature token with flying for each creature returned to your hand this way.", Effect.eaglesAreComing),
  (none, Effect.chapterTreasureThenDragonIfFour),
  (none, Effect.chapterRecruit),
  (none, Effect.chapterReturnCreatureFromGyMvAtMost 3),
  (none, Effect.chapterPlusOneUpToOne),
  (some "Look at the top twenty cards of your library, put any number of land cards from among them onto the battlefield tapped, then shuffle. You gain 8 life.", Effect.lookAtTopLandsGainLife 20 8),
  (none, Effect.drawEqualSacrificedPowerThenDiscard),
  (none, Effect.millPlayer 3),
  (none, Effect.counterCreatureSpellPTAtMost 2),
  (none, Effect.returnFromGraveyardTapped),
  (none, Effect.allCreaturesGet (-4) (-4)),
  (some "Exile all creature cards from target player's graveyard. You may cast spells from among those cards for as long as they remain exiled, and mana of any type can be spent to cast them.", Effect.exileGraveyardCreaturesGrantCast),
  (none, Effect.destroyTargetCreatureControllerLosesLife 2),
  (none, Effect.returnSpellDraw),
  (none, Effect.abilityScry 2),
  (none, Effect.targetPlayerDraw 2),
  (some "Draw cards equal to the greatest toughness among creatures you control, then put any number of creature cards from your hand onto the battlefield.", Effect.drawEqualToughnessThenPutCreatures),
  (none, Effect.addRedPerOppArtifacts),
  (none, Effect.abilityCreateTokensX .treasure),
  (none, Effect.abilityCreateTokens .food 1),
  (none, Effect.arwenShare),
  (some "For each opponent, gain control of up to one target artifact that player controls.", Effect.gainControlOppArtifacts),
  (some "This spell deals damage to each creature your opponents control equal to the total mana value of other spells you've cast this turn.", Effect.damageOppCreaturesEqualOtherSpellsMv),
  (none, Effect.grantCombatDamageCreateTreasure),
  (some "Target creature phases out. If this spell was kicked, each creature target player controls phases out instead.", Effect.phaseOutKicker),
  (none, Effect.putShadowCounter),
  (none, Effect.damageEachOpponent 1),
  (none, Effect.chooseTwoDestroyRest),
  (none, Effect.blackGateUnblockable),
  (none, Effect.burdenThenDraw),
  (none, Effect.teamGain #[Keyword.doubleStrike]),
  (none, Effect.sourceGainsIndestructibleTap),
  (none, Effect.castingPlusOneEachOther),
  (none, Effect.watchHulk),
  (none, Effect.plusOneOnEachOtherSubtype "Hero" 1),
  (none, Effect.createTokens .hero32vigilance 2),
  (none, Effect.plusOneAndIndestructibleCounter),
  (some "This spell deals 2 damage to target attacking or blocking creature. If this spell was cast using teamwork, it deals 4 damage to that creature instead.", Effect.dealDamageToAttackerOrBlocker 2 4),
  (none, Effect.resourcePlusOneOnHeroesCreateWall),
  (none, Effect.stepHarnessedFlicker),
  (none, Effect.exileCreatureToughnessAtLeast 4),
  (none, Effect.exileEnchantmentMvAtLeast 4),
  (none, Effect.lookAtTopPutTypes 7 #["Hero", "Equipment", "Vehicle"]),
  (none, Effect.enterReturnGyPermanentThisTurn),
  (none, Effect.mayPutHeroMvOrDraw 3),
  (none, Effect.plusOneOnEachYouControl),
  (some "Target player investigates. Target creature gets +1/+0 and gains flying until end of turn. Untap it.", Effect.investigatePumpFlyingUntap),
  (none, Effect.anotherYouControlGetsAndGrant 2 0 #[Keyword.hexproof]),
  (none, Effect.castingTapCreatureOrLand),
  (none, Effect.tapTargetCreature),
  (none, Effect.enterOppCreatesTheVoid),
  (none, Effect.watchEquippedAttacksAloneUntapScry),
  (none, Effect.plusOneLifelinkIndestructible),
  (none, Effect.enterPlusOnesOrReturnArtEnch),
  (none, Effect.targetPlayerCreatesTokens .leviathan65hexproof 1),
  (some "Return one or two target nonland permanents to their owners' hands.", Effect.returnOneOrTwoNonlands),
  (none, Effect.watchMerfolkAttackDraw),
  (none, Effect.drawX),
  (none, Effect.copyControlledAbility .creature),
  (none, Effect.enterCreateRedwing),
  (none, Effect.revealTopDrawIfArtifact),
  (none, Effect.watchJusticeBounce),
  (none, Effect.plusOneAndExtraTurn),
  (none, Effect.watchYouTargetDrawOnce),
  (none, Effect.watchTokensEnterMayDraw),
  (none, Effect.castingDrawPowerEqualHand),
  (some "For each nontoken creature you control, create a token that's a copy of that creature, except it isn't legendary.", Effect.copyNontokenCreaturesYouControl),
  (none, Effect.castingMerfolkFromBlue),
  (none, Effect.lookAtTopRevealArtifact 4),
  (some "The owner of target creature an opponent controls puts it into their library second from the top or on the bottom. Then up to one target creature you control connives.", Effect.ownerPutsLibraryThenConnive),
  (some "Counter target spell unless its controller pays {2}. Counter that spell unless its controller pays {4} instead if this spell was cast using teamwork.", Effect.counterUnlessPaysTeamwork 2 4),
  (none, Effect.castingExileFlicker),
  (none, Effect.watchCombatDamageExileUntilNonland),
  (none, Effect.pump (-4) (-4)),
  (none, Effect.returnGySubtypeToHand "Villain"),
  (none, Effect.returnGySubtypeToHand "Hero"),
  (none, Effect.watchAttacksAloneDrain),
  (none, Effect.connive),
  (none, Effect.resourceDiscardExilePlay),
  (none, Effect.eachOppDiscardThenPlusOne),
  (none, Effect.addTwoAnyColorEquipment),
  (none, Effect.targetGets (-4) (-4)),
  (none, Effect.resourceSecondDrawPlusOneTarget),
  (none, Effect.abilityCreateTokens .wall04defender 1),
  (none, Effect.abilityTargetPlayerDraw 4),
  (some "Choose target creature card in your graveyard with mana value 4 or less. If this spell was cast using teamwork, instead choose target creature card in your graveyard. Return the chosen card to the battlefield.", Effect.returnGyCreatureMvAtMostOrAny 4),
  (none, Effect.returnGyCreatureThenPlusOne 2),
  (none, Effect.grantDeathtouch),
  (none, Effect.watchVillainPlusOneLifelink),
  (none, Effect.dealDamageToEachCreature 3),
  (some "Destroy target land. Its controller may search their library for a basic land card, put it onto the battlefield tapped, then shuffle.", Effect.destroyLandSearchBasic),
  (some "Gain control of target creature until end of turn. If you control a Villain with greater mana value than that creature, gain control of that creature until the end of your next turn instead. Untap that creature. It gains haste until end of turn.", Effect.gainControlUntilEotOrNextIfVillain),
  (none, Effect.castingCopyIfArtifactOrLand),
  (some "Exile all the cards from your hand, then draw that many cards. Until the end of your next turn, you may play cards exiled this way.", Effect.exileHandDrawPlayUntilNext),
  (some "Create a 2/1 black Villain creature token with menace, then creatures you control get +1/+0 until end of turn.", Effect.createTokensThenTeamPump .villain21menace 1 1 0),
  (none, Effect.watchVillainOrArtifactDamage),
  (none, Effect.enterDealDamageUpToOne 4),
  (none, Effect.plusOneAndDoubleStrikeCounter),
  (none, Effect.abilityCreateTokens .treasure 1),
  (some "Target creature gains double strike until end of turn. If this spell was cast using teamwork, that creature also gains trample until end of turn.", Effect.grantDoubleStrikeTeamworkTrample),
  (none, Effect.castingDamageEqualMv),
  (some "You may sacrifice an artifact or discard a card. If you do, draw two cards.", Effect.maySacArtifactOrDiscardDraw 2),
  (some "Choose up to two. Return those cards from your graveyard to your hand. • Target artifact card. • Target creature card. • Target enchantment card. • Target land card.", Effect.returnUpToTwoGyModal),
  (none, Effect.addAnyColorEqualToSourcePower),
  (some "Reveal the top eight cards of your library. You may put a creature card from among them onto the battlefield. If this spell was cast using teamwork, put any number of creature cards from among them onto the battlefield instead. Put the rest into your graveyard.", Effect.revealTopPutCreatures 8),
  (none, Effect.fight),
  (none, Effect.plusOneOnCreature),
  (none, Effect.plusOneAndGrant #[Keyword.vigilance, Keyword.indestructible, Keyword.haste]),
  (none, Effect.resourceGainLifePlusOnes),
  (none, Effect.enterCreateZabu),
  (none, Effect.resourcePlusOneOnThisOnce),
  (none, Effect.plusOneAndCreateTokens 1 .hero32vigilance),
  (none, Effect.proliferateEachKind),
  (none, Effect.creatureYouControlDealsTwicePower),
  (some "Mill two cards. You may put a permanent card from among the milled cards into your hand. You gain 2 life.", Effect.millThenPutPermanentGainLife 2 2),
  (some "Target player gains 2 life, then searches their library for a basic land card, puts it onto the battlefield tapped, then shuffles. Put a +1/+1 counter on up to one target creature.", Effect.gainLifeSearchBasicPlusOne 2),
  (none, Effect.millThenPutSubtypeOrEnchantment 4 "Hero"),
  (none, Effect.watchHeroesDamagePlusTwo),
  (none, Effect.enterOrAttackCreateSquirrel),
  (none, Effect.plusOneOnCreatureN 3),
  (none, Effect.chooseTargetDoubleAndTrample),
  (none, Effect.plusOneThenFightUpToOne),
  (none, Effect.thisAttackMayPayPlusOne),
  (none, Effect.resourcePlusOneCreateInsectOnce),
  (none, Effect.mayDrawPerArtifactOppsDraw),
  (none, Effect.artifactSpellsCostLessThisTurn 1),
  (none, Effect.supertypeSpellsCostLessThisTurn 1),
  (none, Effect.chapterDealXDamageToTargetOpponentGreatestArtifactMv),
  (none, Effect.createTokensEqualRemovedPlusOnes .insect11green),
  (none, Effect.createTokens .villain21menace 2),
  (none, Effect.chapterDealDamageToEachNonSubtypeAndOpponents 2 "Villain"),
  (none, Effect.createTokensPerSubtype .treasure "Villain"),
  (none, Effect.watchAttacksAloneFirstStrikeMenace),
  (none, Effect.destroyUpToOneNonland),
  (none, Effect.eachOpponentLosesLife 2),
  (none, Effect.createGalactus),
  (none, Effect.thisAttackIfArtifactEnteredDraw),
  (none, Effect.watchAnyPlayerSecondDraw),
  (none, Effect.castingVillainToken),
  (none, Effect.thisAttackBlinkNontoken),
  (none, Effect.copyControlledAbility .artifact),
  (none, Effect.deathDeathtouchOppSac),
  (none, Effect.castingTargetsGainFlying),
  (none, Effect.creaturesYouControlGetAndGrant 1 1 #[Keyword.vigilance]),
  (none, Effect.fightUpToOne),
  (none, Effect.plusTwoThenOddEvenDestroy),
  (none, Effect.enterCreateSturdyShieldAttach),
  (some "Search your library and/or graveyard for an artifact creature card with mana value X or less and put it onto the battlefield with X additional +1/+1 counters on it. If X is 4 or greater, it gains haste until end of turn. If you search your library this way, shuffle.", Effect.searchLibraryOrGyArtifactCreatureX),
  (some "Exile all creatures. Each player may put any number of creature cards from their hand onto the battlefield. Then put all cards exiled this way into their owners' hands. Exile this spell.", Effect.worldsWithinWorlds),
  (none, Effect.addMana #[.colorless, .colorless, .colorless]),
  (none, Effect.watchEquippedAttacksTap),
  (none, Effect.enterOrAttackCopyKeywords),
  (none, Effect.lookAtTopRevealSubtype 3 "Hero"),
  (none, Effect.addFourAnyCombination),
  (none, Effect.addAnyColorSpendOnlyArtifactSpell),
  (none, Effect.abilityCreateTokens .doombot 1),
  (none, Effect.targetSubtypeConnives "Villain"),
  (none, Effect.drawAndLoseLife 1 0),
  (none, Effect.becomeSubtypeWithLandsPT "Elf"),
  (none, Effect.plusOneOnTarget 2),
  (none, Effect.triggerCreateTokens .treasure 1 true),
  (some "put a +1/+1 counter on target creature you control",
    { targets := .creatureYouControl, body := Instruction.putPlusOne (.target 0) 1 }),
  (none, Effect.triggerCreateTokens .wall 1),
  (some "put a +1/+1 counter on this creature", { body := Instruction.putPlusOne .this 1 }),
  (some "target creature gets +4/+4 until end of turn",
    { targets := .creature, body := Instruction.pumpFixed (.target 0) 4 4 }),
  (some "another target creature you control gets +2/+0 and gains trample until end of turn",
    { targets := .anotherCreatureYouControl, body := Instruction.pumpAndTrample (.target 0) 2 0 }),
  (none, Effect.triggerCreateThenAttach .treasure),
  (some "put a +1/+1 counter on target creature",
    { targets := .creature, body := Instruction.putPlusOne (.target 0) 1 }),
  (some "this creature gets +1/+1 until end of turn", { body := Instruction.pumpFixed .this 1 1 }),
  (none, Effect.triggerCreateTokens .treasure 1),
  (some "target attacking creature without flying gains flying until end of turn",
    { targets := .attackingCreatureWithoutFlying, body := Instruction.grantKeywords (.target 0) #[Keyword.flying] }),
  (none, Effect.pumpAndGrantKeywords 2 2 #[Keyword.flying]),
  (none, Effect.plusOneThenGainLife 1 1),
  (none, Effect.damageTargetOpponent 1),
  (none, Effect.millSelf 3),
  (none, Effect.mayDiscardDraw 1),
  (none, Effect.createTokens .heartwood 1),
  (none, Effect.createTokens .beast44trample 1),
  (none, Effect.createTokensThenSurveil .cadet 1 1),
  (some "Create X 2/2 colorless Wizard Soldier creature tokens named Cadet, where X is the amount of life you gained this turn.", Effect.createTokensLifeGained .cadet),
  (none, Effect.setBasePT 0 0),
  (some "Target opponent sacrifices a creature or planeswalker with the greatest mana value among creatures and planeswalkers they control. You gain 2 life.", Effect.oppSacrificesGreatestMvGainLife 2),
  (some "This spell deals 6 damage to target creature or planeswalker. If excess damage was dealt to that permanent this way, empower Jace X, where X is that excess damage.", Effect.damageThenEmpowerExcess 6),
  (some "Until end of turn, you may activate loyalty abilities of Jace planeswalkers you control on any player's turn any time you could cast an instant.", Effect.jaceLoyaltyAtInstantSpeed),
  (none, Effect.creaturesYouControlGetAndGrant 1 0 #[Keyword.haste]),
  (none, Effect.createTokens .pridemate 1),
  (some "For each creature target player controls, create a token that's a copy of that creature, except it has haste and \"At the beginning of the end step, if you don't control a planeswalker, sacrifice this creature.\"", Effect.copyEachCreatureOfTargetPlayer),
  (none, Effect.copyNextInstantSorceryThisTurn),
  (none, Effect.addMana #[.colored .red]),
  (some "Exile the top card of your library. You may cast that card. If you don't, this deals 2 damage to each opponent.", Effect.exileTopMayCastElseDamageOpponents 2),
  (some "You get an emblem with \"Whenever you cast a spell, this emblem deals 5 damage to any target.\"", Effect.emblemCastSpellDamage 5),
  (none, Effect.addMana #[.colored .red, .colored .red]),
  (some "Target creature you control deals damage equal to its power to target creature or planeswalker an opponent controls.", Effect.firstDealsStatDamageToSecond false),
  (some "Target planeswalker you control deals damage equal to its loyalty to target creature or planeswalker an opponent controls.", Effect.firstDealsStatDamageToSecond true),
  (some "Return target creature card with mana value 3 or less from your graveyard to the battlefield with an additional +1/+1 counter on it.", Effect.generousRevival),
  (none, Effect.hexhavenBattalion),
  (some "Choose a creature type. Destroy all creatures that aren't of the chosen type.", Effect.kindredJudgment),
  (none, Effect.loyalTutor),
  (some "Put a +1/+1 counter on each of one or two target creatures.", Effect.predictivePreparations),
  (some "Destroy target creature. If it wasn't attacking, its controller draws a card.", Effect.prophesiedEnd),
  (none, Effect.refuteDestiny),
  (some "Return all nonland permanent cards from your graveyard to the battlefield.", Effect.returnToTheLightRealms),
  (none, Effect.surgicalPrecisionDestroy),
  (none, Effect.drawAndGainLife 1 2),
  (none, Effect.yourFateEndsHere),
  (none, Effect.counterTargetSpell),
  (some "Draw X cards, where X is the number of cards that were put into target player's graveyard from their library this turn.", Effect.cruelCalculations),
  (none, Effect.icyReceptionCounter),
  (none, Effect.targetCreatureGets (-5) 0),
  (none, Effect.preciseRedaction),
  (some "Draw two cards. Then you may exile this spell and four cards named this from your graveyard. If you do, search your library for a Sphinx creature card, put it onto the battlefield, then shuffle.", Effect.sphinxsApproach),
  (none, Effect.unsummon),
  (none, Effect.unwindHistory),
  (some "Each player may discard their hand and draw seven cards.", Effect.arcOfFortune),
  (none, Effect.castAwayDoubt),
  (some "Exile target creature or planeswalker. This spell deals 1 damage to each opponent and you gain 1 life.", Effect.extendedAbsence),
  (some "You may reveal exactly two cards you own with different names from outside the game. An opponent chooses one of them. You put that card into your hand.", Effect.extrapolateTheImpossible),
  (some "Exile all creatures. Empower Jace X, where X is the number of creatures exiled this way.", Effect.overwriteTheMultiverse),
  (some "Return target creature or planeswalker card with mana value 6 or less from your graveyard to the battlefield.", Effect.rewriteRegrets),
  (some "Draw cards equal to the greatest power among creatures you control. You lose life equal to the number of cards drawn this way.", Effect.riseDraw),
  (none, Effect.allCreaturesGet (-3) (-3)),
  (none, Effect.destroyTargetCreatureOrPlaneswalker),
  (some "Target opponent reveals their hand. You choose a nonland permanent card from it. That player discards that card.", Effect.solveForDisappointment),
  (none, Effect.terminalCriticism),
  (none, Effect.vraskasMercyDestroy),
  (none, Effect.vraskasMercyEmpower),
  (none, Effect.artifistAcumen),
  (none, Effect.awakenTheInferno),
  (some "Create a 2/2 colorless Wizard Soldier creature token named Cadet, then put a +1/+1 counter on each other Wizard token you control.", Effect.commandTheStage),
  (some "This spell deals 5 damage to target black or green creature or planeswalker. If that permanent would die this turn, exile it instead.", Effect.essenceBurn),
  (some "This spell deals 1 damage to each creature and planeswalker your opponents control.", Effect.fulminousForteSweep),
  (none, Effect.damageToCreatureOrPlaneswalker 5),
  (some "Until end of turn, whenever you tap a Mountain for mana, add an additional {R}.", Effect.moltenTide),
  (some "Search your library for a land card, put it into your graveyard, then shuffle.", Effect.enroot),
  (some "Target creature or planeswalker an opponent controls that's red or white loses all abilities until end of turn. Target creature you control deals damage equal to its power to that permanent.", Effect.flourishingGrapple),
  (none, Effect.restoreWithEmpathy),
  (some "Mill four cards. You may put a permanent card from among them into your hand. You gain 1 life.", Effect.somethingWorthSaving),
  (none, Effect.tethermagesAdvantage),
  (none, Effect.creaturesYouControlGetUntilEot 2 0),
  (none, Effect.chargeTheSanctumPump),
  (some "Choose target nonland permanent. Its owner may put it on top of their library. If they do, this spell deals 2 damage to them. If they didn't put the card on top of their library, they put it on the bottom.", Effect.clashOfElements),
  (some "You may sacrifice a planeswalker. If you do, search your library for a planeswalker card, put it onto the battlefield, then shuffle.", Effect.entrustTheSpark),
  (none, Effect.drawThenEmpower 1 2),
  (none, Effect.bounceSpellOrCreature),
  (none, Effect.damageToCreatureWithFlying 6),
  (none, Effect.plusOneThenGrant 2 #[Keyword.trample]),
  (none, Effect.addColorless 3),
  (some "Create two 2/2 colorless Wizard Soldier creature tokens named Cadet. If this spell was cast from a graveyard, put a +1/+1 counter on each of them for every three cards in your graveyard.", Effect.recursiveRecruitment),
  (none, Effect.targetCreatureGains #[Keyword.firstStrike, Keyword.deathtouch]),
  (some "Create a 2/2 colorless Wizard Soldier creature token named Cadet. It gains haste until end of turn.", Effect.cadetWithHaste),
  (some "This spell deals 2 damage to target opponent. That player reveals their hand. You choose a nonland card from it. They discard that card.", Effect.stingingVitriol),
  (none, Effect.theorixCounter),
  (some "Mill three cards, then draw a card.", Effect.millThenDraw 3 1),
  (some "Draw a card. If this spell wasn't cast from your hand, draw two cards instead.", Effect.twinnedVision),
  (none, Effect.twistedFates),
  (none, Effect.permanentYouControlGains #[Keyword.hexproof, Keyword.indestructible]),
  (none, Effect.drawAndGainLife 1 3),
  (some "Exile target creature or planeswalker. If that permanent's mana value was 3 or less, return it to the battlefield tapped under your control. Exile it at the beginning of the next end step.", Effect.vindictiveTriumph),
  (none, Effect.tamsResistance),
  (none, Effect.returnLegendaryCardToHand),
  (none, Effect.plusOneVigilanceIndestructible),
  (none, Effect.fraTapTargetCreature),
  (none, Effect.untapTargetCreature),
  (none, Effect.destroyNoncreatureNonland),
  (none, Effect.gainLifeMode 4),
  (some "Target creature gets -X/-0 until end of turn, where X is the number of cards in your graveyard.", Effect.minusPowerPerGraveyard),
  (none, Effect.surveilMode 2),
  (none, Effect.sourceDealsDamageToCreatureOrPlaneswalker 4),
  (none, Effect.createCadetMode),
  (none, Effect.drawMode),
  (some "Create a 1/1 blue Illusion creature token",
   FraCandidates.ab (Instruction.createTokensFixed .illusion11blue 1)),
  (some "For each opponent, return up to one target artifact or creature that player controls to its owner's hand",
   FraCandidates.ab (Instruction.bounce .allTargets) (.forEachOpponentControlled (.any #[.hasType .artifact, .hasType .creature]) (.upTo 1))
   ),
  (some "Draw three cards. Then put X +1/+1 counters on each creature you control, where X is the number of cards in your hand",
   FraCandidates.ab (.seq #[
      Instruction.drawFixed 3,
      Instruction.putCounters
        (.inZones .battlefield (.all #[.hasType .creature, .controlledBy .you]))
        .plusOnePlusOne (.playerMetric .handSize .you)])),
  (some "Surveil 1. If you put a noncreature, nonland card into your graveyard this way, put that card into your hand",
   FraCandidates.ab (.bind ⟨0⟩ (Instruction.surveilFixed 1)
      (Instruction.bounce (.filter (.stepObjects ⟨0⟩) (.all #[.not (.hasType .creature), .not (.hasType .land)]))))),
  (some "Add {U}. Spend this mana only to cast a noncreature spell",
   FraCandidates.ab (Instruction.addMana {
      spec := .fixedOne (.colored .blue)
      restriction := some (.onlyForSpells (.not (.hasType .creature))) })),
  (some "Tap target artifact or creature. Put X stun counters on it",
   FraCandidates.ab (Instruction.tapAndStun (.target 0) .chosenX) (.ofDomain (.object .battlefield (.any #[.hasType .artifact, .hasType .creature])))),
  (some "You get an emblem with \"Whenever you cast a spell, draw a card.\"",
   FraCandidates.ab (.create (.emblem .you {
      triggeredAbilities := #[TriggeredAbility.ofPattern .youCastSpell
        (Instruction.drawFixed 1)] }))),
  (some "Empower Jace X, where X is the number of Islands you control",
   FraCandidates.ab (Instruction.empower .jace
      (.aggregate .count .one (.inZones .battlefield (.all #[.hasSubtype (.literal .island), .controlledBy .you]))))),
  (some "Until your next turn, whenever a creature attacks you or a planeswalker you control, it gets -5/-0 until end of turn",
   FraCandidates.ab (.installEffect (.createDelayedTrigger {
      pattern := .creatureAttacksYouOrYourPlaneswalker
      duration := .untilNextTurnOf .you
      oneShot := false
      effect := { body := Instruction.pumpFixed .triggerSubject (-5) 0 } }))),
  (some "Exile all but the bottom card of each opponent's library",
   FraCandidates.ab (.player (.inspectLibrary {
      source := .allButBottom .opponents
      action := .moveAll .exile
      rest := .leaveInPlace }))),
  (some "Up to one target creature gets -4/-1 until your next turn",
   FraCandidates.ab (Instruction.pumpFixed (.target 0) (-4) (-1) (.untilNextTurnOf .you)) (.single { domain := .creature, count := .upTo 1 })),
  (some "Each player sacrifices a creature of their choice. If you sacrificed a creature this way, create a 4/4 green Beast creature token with trample",
   FraCandidates.ab (.bind ⟨0⟩
      (.forEach (.eachPlayer .any) ⟨1⟩
        (.moveZone
          (.inZones .battlefield (.all #[.hasType .creature, .controlledBy (PlayerFilter.ofExpr (.stepPlayers ⟨1⟩))]))
          .graveyard .sacrifice
          { choice? := some { chooser := .player (.stepPlayers ⟨1⟩), count := .exact (.const 1) } }))
      (Instruction.ifThen (.exists (.filter (.stepObjects ⟨0⟩) (.controlledBy .you)))
        (Instruction.createTokensFixed .beast44trample 1)))),
  (some "Each opponent discards two cards. For each opponent who didn't discard two nonland cards this way, you draw a card",
   FraCandidates.ab (.forEach (.eachPlayer .opponent) ⟨0⟩
      (.bind ⟨1⟩ (Instruction.discardFixed 2 (.stepPlayers ⟨0⟩))
        (Instruction.ifThen
          (.cmp .lt (.aggregate .count .one (.filter (.stepObjects ⟨1⟩) (.not (.hasType .land)))) (.const 2))
          (Instruction.drawFixed 1))))),
  (some "Discard your hand, then draw a card for each creature you control",
   FraCandidates.ab (.seq #[
      .moveZone (.inZones (.handOf .you) .anyObject) .graveyard .discard,
      .player (.drawCards .you
        (.aggregate .count .one (.inZones .battlefield (.all #[.hasType .creature, .controlledBy .you]))))])),
  (some "This deals 4 damage to each creature except for tokens you control",
   FraCandidates.ab (Instruction.dealDamageFixed
      (.objects (.inZones .battlefield (.all #[.hasType .creature, .not (.all #[.isToken true, .controlledBy .you])]))) 4)),
  (some "You get an emblem with \"Creatures you control get +2/+2.\"",
   FraCandidates.ab (.create (.emblem .you { staticAbilities := #[StaticAbility.creaturesYouControlGet 2 2] }))),
  (some "Untap up to two target lands",
   FraCandidates.ab (Instruction.untap .allTargets) (.single { domain := .land, count := .upTo 2 })),
  (some "Until your next turn, whenever one or more creatures attack one of your opponents, those creatures get +2/+2 and gain trample until end of turn",
   FraCandidates.ab (.installEffect (.createDelayedTrigger {
      pattern := .creaturesAttackYourOpponent
      grouping := .perPlayerInBatch
      duration := .untilNextTurnOf .you
      oneShot := false
      effect := { body := Instruction.pumpAndTrample .triggerSubject 2 2 } }))),
  (some "This planeswalker deals 1 damage to each opponent and you gain 1 life",
   FraCandidates.ab (.seq #[Instruction.dealDamageFixed (.players .opponents) 1, Instruction.gainLifeFixed 1])),
  (some "Put a +1/+1 counter on target creature for each land you control",
   FraCandidates.ab (Instruction.putCounters (.target 0) .plusOnePlusOne
      (.aggregate .count .one (.inZones .battlefield (.all #[.hasType .land, .controlledBy .you])))) .creature),
  (some "You may sacrifice a creature. If you do, create a 4/4 green Beast creature token with trample",
   FraCandidates.ab (Instruction.may .you
      (some (CostSpec.ofItem (.sacrifice (.exact 1) (.filter (.hasType .creature)))))
      (Instruction.createTokensFixed .beast44trample 1))),
  (some "This planeswalker deals 2 damage to up to one target creature or planeswalker and 2 damage to target player",
   FraCandidates.ab (Instruction.dealDamageFixed .allTargets 2) (.ofSlots #[{ domain := .creatureOrPlaneswalker, count := .upTo 1 }, .of .anyPlayer])),
  (some "Create an 8/8 blue Leviathan creature token with hexproof",
   FraCandidates.ab (Instruction.createTokensFixed .leviathan88hexproof 1))
]

def spellEffects : Thunk (Array Effect) := Thunk.mk fun _ => spellEffectEntries.get.map (·.2)

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

def triggeredAbilityEntries : Thunk (Array (Option String × TriggeredAbility)) := Thunk.mk fun _ => #[
  (some "When you cast this spell, copy it X times. You may choose new targets for the copies.", TriggeredAbility.onCastCopyThisSpellXTimes),
  (none, .onAttackPumpByGreatestPower),
  (none, .onTheRingTemptsYouDraw 1),
  (none, .onChooseRingBearerDraw),
  (none, .onEnterDraw 1),
  (none, .onEnterGainLife 1),
  (none, .onDiesDealDamageEqualToPowerToOppCreature),
  (none, .onBecomesBlockedDeal1ToBlockers),
  (none, .onEnterScry 2),
  (none, .onEnterSearchForest),
  (none, .onAnotherElfYouControlEntersGets1),
  (none, .onEnterMayDiscardDraw 2),
  (none, .onEnterTargetOpponentSacrificesCreature),
  (none, .onLandYouControlEntersPlusOnePlusOne),
  (none, (.onLandYouControlEntersGets 1 1)),
  (none, .onEnterDealDividedDamage 3 3),
  (none, .onEnterOrAttackDealDividedDamage 3 3),
  (none, .onEnterOrAttackReturnElfGainLife),
  (none, .onAttackWithElvesScry 1),
  (none, .onScryPumpSelfForEachLookedAt),
  (none, .onCastInstantOrSorceryDealDamageToEachOpponent 2),
  (none, .onAttackSetOtherBasePT),
  (none, .onAttackScry 1),
  (none, .onAttackFerociousGainLife 2),
  (none, .onAttackOtherGets2AndTrample),
  (none, .onAttackPumpForEachOtherCreature),
  (none, .onDrawSecondPlusOne),
  (none, .onDrawPlusOne),
  (none, .onCombatDamageToPlayerLoot),
  (none, .onDiesOppCreatureGets (-1) (-1)),
  (none, .onOneOrMoreOtherCreaturesDieScry 1),
  (none, .onEnterExileOppGyCardOppsLoseLife 2),
  (none, .onEnterEachOpponentDiscards),
  (none, .onEnterUntapOtherPlusOneIfSubtype "Bear"),
  (none, .onAttackFerociousSourceGets 2 2),
  (none, .onAttackFerociousSourceGetsAndTeamTrample 1),
  (none, .onAttackFerociousPlusOneEach),
  (none, .onYourBeginCombatFerociousPlusOne),
  (none, .onYouAttackFerociousDrawLoseLife),
  (none, .onEnterPlusOneOnCreature),
  (none, .onEnterRecruit),
  (none, .onDiesRecruit),
  (none, .onEnterCreateTokens .treasure 1 true),
  (none, .onEnterCreateTokens .treasure 1),
  (none, .onEnterExileTop),
  (none, .onCastNoncreatureAmassGoblins 1),
  (none, .onDiesAmassGoblins 4),
  (none, .onEnterAmassGoblins 1),
  (none, .onYouAttackAmassGoblins 2),
  (none, .onEnterOrAttackRecruit),
  (none, .onArtifactYouControlEntersDraw),
  (none, .onYourUpkeepCreateTokens .wolf 1),
  (none, .onEnterCreateThenAttach .dwarf),
  (none, .onEnterAmassThenAttach 1),
  (none, .onEnterAttachToSubtype "Dwarf"),
  (none, .onYourEndStepDraw),
  (none, .onAttackTargetGainsKeywords #[Keyword.firstStrike]),
  (none, .onEnterSearchBasicToHand),
  (none, .onEnterDealDamageDestroyIfSubtype 1 "Dragon"),
  (none, .onAttackDamageEqualTreasures),
  (none, .onYourUpkeepCreateTokens .treasure 1),
  (some "Whenever an opponent casts their first noncreature spell each turn, you recruit.", .onOpponentCastsFirstNoncreatureRecruit),
  (none, .onThisOrNontokenSubtypeEntersCreateTokens "Dwarf" .dwarf 1),
  (none, .onEnterGainLifeSearchBasicOnTop 2),
  (none, .onLandYouControlEntersCreateTokens .elf 1),
  (none, .onYourFirstMainAddMana #[.colored .red, .colored .red]),
  (none, .onEnterAttachTargetEquipment),
  (none, .onBecomesTargetDraw),
  (none, .onYouAttackRecruit),
  (none, .onLandYouControlEntersTapOrUntap),
  (none, .onLandYouControlEntersBecomePT 4 2),
  (none, .onEnterReturnOtherPlusOne),
  (none, .onAnotherSubtypeOrEquipmentEntersDrawOnce "Dwarf"),
  (none, .onEnterLookAtTopRevealTypes 4 #["Dwarf", "Equipment"]),
  (none, .onEnterCreateTappedTreasuresEqualOppArtifacts),
  (none, .onCastWithTreasureDrawLoseLife),
  (none, .onEnterCreateAxe),
  (none, .onCastNoncreaturePumpAndDamageOpponents 1),
  (some "When this enchantment enters, return target creature card from your graveyard to your hand.", .onEnterReturnCreatureFromGyToHand),
  (none, .onCreatureCardLeavesYourGyAmassGoblins 1),
  (some "When Azog enters, destroy up to one other target creature. Its controller amasses Goblins X, where X is that creature's power. If you controlled that creature, draw a card.", .onEnterDestroyOtherAmassControllerPower),
  (some "Whenever Balin or another Dwarf you control enters, you may discard your hand. Draw X cards, where X is the number of cards discarded this way. If you have an enduring story, Balin deals X damage to each opponent.", .onThisOrAnotherSubtypeEntersDiscardHand "Dwarf"),
  (none, .onDrawSecondPlusOneLifelink),
  (none, .onCombatDamageWolfPlusOneOrTreasure),
  (some "Whenever a token you control enters, you gain 1 life if this is the first time this ability has resolved this turn. If it's the second time, draw a card. If it's the third time, put a +1/+1 counter on each creature you control.", .onTokenYouControlEntersBelladonna),
  (none, .onYourBeginCombatTrampleCounterBecomeBear),
  (none, .onEnterOrAttackPlusOneOnCreature),
  (some "Whenever Bilbo attacks, you may cast an artifact, instant, or sorcery spell from your graveyard. If an instant or sorcery spell cast this way would be put into your graveyard, exile it instead.", .onAttackCastFromGyArtifactInstantSorcery),
  (some "When Bolg enters, you may sacrifice another creature. When you do, Bolg deals damage equal to that creature's power to another target creature. If excess damage was dealt this way, amass Goblins X, where X is that excess damage.", .onEnterBolgMaySacrifice),
  (none, .onEnterLookAtTopRevealTypes 4 #["permanent"]),
  (none, .onEnterMillThenSubtypeToHand 4 "Elf"),
  (none, .onEnterExileOppNonlandEachUntilLeaves),
  (none, .onLandYouControlEntersCreateTokens .bear 1),
  (none, .onCastCreaturePlusOneEqualMv),
  (none, .onAttackWithTotalPowerUntapExtraCombat 12),
  (none, .onEnterOrAttackHoneEachEquipment),
  (some "When Dáin enters, create a colorless Equipment artifact token named Axe with \"Equipped creature gets +1/+0\" and equip {2}. When you do, attach it to target creature you control.", .onEnterCreateAxeAttach),
  (some "Whenever Dáin attacks, each equipped attacking creature gains double strike until end of turn.", .onAttackEquippedGainDoubleStrike),
  (none, .onActivateCreatureAbilityDrawOnce),
  (some "When this Aura enters, tap enchanted creature and remove all counters from it.", .onEnterTapEnchantedRemoveCounters),
  (none, .onDiesRevealTopPutRandomCreature 13),
  (none, .onOpponentDrawsSecondCreateTreasure),
  (some "Whenever an opponent casts a spell with mana value of the chosen quality, choose one that hasn't been chosen — • Put a +1/+1 counter on Gollum. • Each opponent loses 2 life and you gain 2 life. • Draw a card.", .onOpponentCastsChosenParityModes),
  (some "At the beginning of combat on your turn, if you've drawn two or more cards this turn, another target creature you control gets +3/+0 and gains first strike until end of turn.", .onYourBeginCombatIfDrawnTwoPumpFirstStrike),
  (none, .onMountainEntersQuestThenDragon),
  (none, .onDrawSecondMillPlayer 3),
  (none, .onEquippedCombatDamageTreasuresPerChosenType),
  (none, .onNontokenYouControlDiesRevealCreature),
  (none, .onAttackMaySacAnotherPlusOneEqualPower),
  (none, .onDiesAmassGoblinsEqualPower),
  (none, .onEnterLootLandEntersTapped),
  (some "Landfall — Whenever a land you control enters, you may pay {1}{G}{U}. If you do, return this card from your graveyard to your hand.", .onLandYouControlEntersPayReturnFromGy),
  (some "When Sting enters, put a hone counter on Sting for each creature target opponent controls. Attach Sting to up to one target creature you control.", .onEnterHonePerOppCreaturesAttach),
  (none, .onEnterOrAttackCreateWall),
  (some "Whenever you put one or more counters on a Goblin, Orc, or Army you control, The Great Goblin deals 2 damage to target opponent.", .onPutCountersOnGoblinOrcArmyDamageOpp),
  (none, .onAnotherGoblinOrcArmyDiesExileTop),
  (none, .onPlayerLosesLifeMillThatMany),
  (none, .onDiesDrawPerFatGraveyard),
  (some "When The Notary Hobbits enter, if they're not a token, create two tokens that are copies of them, except the tokens aren't legendary.", .onEnterIfNotTokenCopySelf),
  (none, .onEnterMaySacDrawTreasure),
  (none, .onYouSacrificeTokenOppLosesLife),
  (some "When Thorin enters, attach any number of target Equipment you control to target creature you control. When one or more Equipment become attached to that creature this way, that creature deals damage equal to its power to up to one target creature.", .onEnterAttachEquipmentThenFight),
  (none, .onLandYouControlEntersPlusOneVigilance),
  (none, .onAnotherLegendarySubtypeEntersLoot "Elf"),
  (some "When Tom, Bert, and William die, if they were a creature, return them to the battlefield. They're an artifact.", .onDiesReturnAsArtifact),
  (none, .onCastNoncreatureMayDrawXDiscard2),
  (none, .onAnotherCreatureYouControlPowerAtMostEntersMayPayDraw 2 1),
  (none, .onEnterMayExileAnotherCreature),
  (none, .onLeaveReturnExiled),
  (none, .onEnterDrawThenBottomIfNoLegendary),
  (none, .onAttackWithTwoOrMoreGrantFlying),
  (none, .onEnterTargetGets 2 0),
  (none, .onEnterCreaturesYouControlGetAndFirstStrike 1),
  (none, .onEnterExileOppNonlandUntilLeaves),
  (none, .onYourEndStepRemoveHopeDrawSac),
  (none, .onDiesDraw 1),
  (none, .onAttackTapHumansDraw),
  (some "Whenever this creature attacks, you may exile target creature defending player controls until this creature leaves the battlefield.", .onAttackMayExileDefenderUntilLeaves),
  (none, .onScryPumpAndUnblockableOnce),
  (none, .onEnterEachPlayerSacrificesCreature),
  (none, .onYouAttackDraw),
  (none, .onEnterOrAttackAmassGoblins 3),
  (none, .onEnterCreateTokens .food 3),
  (none, .onEnterAttachToLegendary),
  (none, .onPlayerCastsSecondSpellLoseLifeCreateTreasure),
  (none, .onEnterDestroyOppArtifactsEnchantmentsGainLife),
  (none, .onAttackDamageEqualSubtypeToEachOpponent "Dwarf"),
  (none, .onEnterOrAttackPlusOneEachOtherGainLife),
  (none, .onEachEndStepDrawIfGainedLife 3),
  (none, .onAttackDefenderSacsLeastPower),
  (none, .onCastGreenOrForestEntersPlusOne),
  (none, .onEnterGainControlOppUntilEot),
  (none, .onEachCombatOthersGetAndOppsGet #["Goblin", "Orc"] 2 2 (-1) (-1)),
  (none, .onThisOrAnotherSubtypeEntersCreateTokens "Dwarf" .treasure 1),
  (none, .onCombatDamagePutNonlandMvAtMost 3),
  (some "Whenever equipped creature attacks, create two tapped 1/1 white Spirit creature tokens with flying. If that creature is legendary, instead create two of those tokens that are tapped and attacking.", .onEquippedAttacksCreateSpirits),
  (none, .onEquippedAttacksPlusOneEachIfCityBlessing),
  (none, .onCastColorCreateTokens .white .humanSoldier 1),
  (none, .onCastColorScry .blue 2),
  (none, .onCastColorDamageOpponent .red 3),
  (none, .onCastColorPump .green 4 4),
  (none, .onEquippedAttacksAloneDrawLoseLife),
  (some "Whenever this creature deals combat damage to a player, you create a Treasure token for each artifact that player controls.", .onCombatDamageCreateTreasuresEqualPlayerArtifacts),
  (none, .onAnotherSubtypeEntersPlusOneOnSource "Wolf" 2),
  (some "Alliance — Whenever another creature you control enters, choose one that hasn't been chosen this turn — • Add {G}{G}{G}. • Put a +1/+1 counter on each creature you control. • Scry 2, then draw a card.", .onAnotherCreatureYouControlEntersAlliance),
  (none, .onYourBeginCombatCastInstantSorceryFromHand),
  (some "When Gandalf enters, exile up to three target lands you control, then return them to the battlefield tapped under their owner's control.", .onEnterExileLandsThenReturnTapped),
  (none, .onLandYouControlEntersDrawPlusOneSource),
  (none, .onEquippedCombatDamageCastInstantSorcery),
  (some "Whenever Gríma deals combat damage to a player, that player exiles cards from the top of their library until they exile an instant or sorcery card. You may cast that card without paying its mana cost. Then that player puts the exiled cards that weren't cast this way on the bottom of their library in a random order.", .onCombatDamageImpulseInstantSorcery),
  (some "When this creature enters and whenever an opponent draws a card except the first one they draw in each of their draw steps, this creature deals 1 damage to any target. Then amass Orcs 1.", .onEnterOrOpponentDrawsDeal1AmassOrcs),
  (some "At the beginning of your end step, put an influence counter on Palantír of Orthanc and scry 2. Then target opponent may have you draw a card. If that player doesn't, you mill X cards, where X is the number of influence counters on Palantír of Orthanc, and that player loses life equal to the total mana value of those cards.", .onYourEndStepPalantir),
  (none, .onCastSecondSpellMillThenCopy),
  (none, .onOpponentCastsAmassOrcs 1),
  (none, .onArmyCombatDamageRingTempts),
  (none, .onRingTemptsMayDiscardDraw 4),
  (some "Whenever Smaug is dealt noncombat damage, create that many Treasure tokens.", .onDealtNoncombatDamageCreateTreasures),
  (some "When The One Ring enters, if you cast it, you gain protection from everything until your next turn.", .onEnterIfCastProtectionEverything),
  (some "At the beginning of your upkeep, you lose 1 life for each burden counter on The One Ring.", .onYourUpkeepLoseLifePerBurden),
  (none, .onSubtypeYouControlCombatDamageCreateTokens "Dwarf" .treasure 2),
  (some "Whenever the final chapter ability of a Saga you control resolves, reveal cards from the top of your library until you reveal a Saga card. Put that card onto the battlefield and the rest on the bottom of your library in a random order. This ability triggers only once each turn.", .onFinalSagaChapterRevealSaga),
  (some "Whenever one or more creatures deal combat damage to you, each opponent sacrifices a creature of their choice that dealt combat damage to you this turn. The Ring tempts you.", .onCombatDamageToYouSacRingTempts),
  (some "Whenever a creature you control is dealt damage, you may have The Sensational She-Hulk deal that much damage to any target. Do this only once each turn.", .watchSheHulkRedirectOnce),
  (some "Whenever you cast a noncreature spell, put a +1/+1 counter on each other creature you control.", .castingPlusOneEachOther),
  (some "Enrage — Whenever The Incredible Hulk is dealt damage, put a +1/+1 counter on him. If he's attacking, untap him and there is an additional combat phase after this phase.", .watchHulk),
  (none, .onCombatMayPutArtifactAttachEquipment),
  (none, .onCombatDamageDraw 1),
  (none, .onCreatureYouControlAttacksAloneInvestigate),
  (none, .onTappedForTeamworkPlusOneAndDraw),
  (none, .onCreatureYouControlAttacksAlonePump 1 1),
  (none, .onEachEndStepDrawIfAttackedOrEnteredSubtype "Hero"),
  (none, .onAttackOthersOfSubtypeGetEqualToughness "Hero"),
  (some "Whenever you cast a spell that targets a creature you control, put a +1/+1 counter on Colleen Wing. Scry 1.", .castingPlusOneScry),
  (some "When this creature enters, draw a card. If you control another Hero, you gain 2 life.", .onEnterDrawGainLifeIfAnotherHero),
  (some "Whenever you put one or more +1/+1 counters on one or more other Heroes you control, you may create a 0/4 colorless Wall creature token with defender.", .resourcePlusOneOnHeroesCreateWall),
  (some "Unbreakable Skin — Whenever Luke Cage attacks alone, he gets +2/+0 and gains indestructible until end of turn.", .thisAttackAttacksAlonePlus2Indestructible),
  (some "∞ — At the beginning of your end step, exile up to one other target nonland permanent you control, then return that card to the battlefield under its owner's control.", .stepHarnessedFlicker),
  (some "Whenever you cast a spell that targets a creature you control, put a +1/+1 counter on Mockingbird.", .castingPlusOneThis),
  (none, .onEnter Effect.enterReturnGyPermanentThisTurn),
  (none, .onEnterCreateTokens .soldier11white 2),
  (none, .onCreatureYouControlEntersScryAndPlan 1),
  (none, .onFourthPlanDrawPlusOneEach),
  (some "Seismic Takedown — Whenever you cast a noncreature spell, tap target creature or land.", .castingTapCreatureOrLand),
  (none, .onEnter (Effect.enterDestroy .oppCreatureDealtDamageThisTurn)),
  (none, .onEnter Effect.enterOppCreatesTheVoid),
  (some "Whenever equipped creature attacks alone, untap it and scry 1.", .watchEquippedAttacksAloneUntapScry),
  (some "When this enchantment enters, exile target tapped creature an opponent controls until this enchantment leaves the battlefield.", .onEnterExileOppTappedUntilLeaves),
  (some "Whenever enchanted creature attacks or blocks, attach any number of target Equipment you control to it.", .watchEnchantedAttachEquipment),
  (some "When this enters, choose one — • Put a +1/+1 counter on each of up to two target creatures. • Return target artifact or enchantment card from your graveyard to your hand.", .onEnter Effect.enterPlusOnesOrReturnArtEnch),
  (none, .onEnterConnive),
  (some "Whenever one or more Merfolk you control attack a player, draw a card.", .watchMerfolkAttackDraw),
  (none, .onEnter Effect.enterCreateRedwing),
  (none, .onEnterAttachToCreatureYouControl),
  (none, .onEnterEnchanted Instruction.tap),
  (some "When this creature enters, choose one — • Tap target nonland permanent. • Untap target nonland permanent.", .onEnterTapOrUntapNonland),
  (none, .onEnter Effect.enterReturnNonlandNontoken),
  (some "Whenever another nonland permanent you control is returned to its owner's hand, put a +1/+1 counter on Justice.", .watchJusticeBounce),
  (none, .onCombatTargetYouControlConnives),
  (some "Whenever a player or permanent becomes the target of an ability you control, draw a card. This ability triggers only once each turn.", .watchYouTargetDrawOnce),
  (some "Whenever one or more tokens you control enter, you may draw a card.", .watchTokensEnterMayDraw),
  (some "Whenever you cast a spell that targets a creature you control, draw a card. Until end of turn, Ms. Marvel gains \"Ms. Marvel's base power is equal to the number of cards in your hand.\"", .castingDrawPowerEqualHand),
  (some "Whenever you cast a noncreature spell with one or more blue mana symbols in its mana cost, create that many 1/1 blue Merfolk creature tokens.", .castingMerfolkFromBlue),
  (none, .onCreaturesYouControlBecomeTappedLootAndPlan),
  (some "When the fourth plan counter is put on this enchantment, sacrifice it. When you do, return up to two target instant and/or sorcery cards from your graveyard to your hand.", .onFourthPlanReturnInstants),
  (some "When this Aura enters, exile up to one target creature other than enchanted creature until this Aura leaves the battlefield. Enchanted creature becomes a copy of that creature until this Aura leaves the battlefield.", .onEnterExileOtherCopyEnchanted),
  (none, .onEnterCreateTokens .soldier11white 1),
  (some "When this Vehicle enters, exile up to one target creature you control. Return that card to the battlefield under its owner's control at the beginning of the next end step.", .onEnterExileCreatureReturnEndStep),
  (some "At the beginning of the upkeep of enchanted creature's controller, that player draws a card.", .stepEnchantedControllerDraws),
  (none, .onEnterAttachThen Instruction.untap),
  (some "Whenever you cast a noncreature spell, exile another target nonland, nontoken permanent. Return that card to the battlefield under its owner's control at the beginning of the next end step.", .castingExileFlicker),
  (none, .onEnter Effect.enterTapLoseAbilitiesWhileSource),
  (none, .onDiesCreateTokens .villain21menace 1),
  (none, .onYouCastColorFromHandConnive .black),
  (some "Whenever another Villain you control enters, you may have it connive. Do this only once each turn.", .watchVillainConniveOnce),
  (some "Whenever Black Widow deals combat damage to a player, that player exiles cards from the top of their library until they exile a nonland card. You may put a +1/+1 counter on Black Widow. If you don't, you may cast the exiled nonland card until end of turn and mana of any type can be spent to cast that spell.", .watchCombatDamageExileUntilNonland),
  (none, .onYouDrawSecondCreateVillainAndPlan),
  (some "When the seventh plan counter is put on this enchantment, sacrifice it. When you do, you control target opponent during their next turn.", .onSeventhPlanControlOpponent),
  (some "Whenever another Villain you control enters, put a +1/+1 counter on Crossbones. He deals 2 damage to each opponent. This ability triggers only once each turn.", .watchVillainPlusOneDamageOnce),
  (none, .onEnterCreateTokens .doombot 2),
  (none, .onYourEndStepDrawLoseLife),
  (none, .onVillainYouControlEntersDrainAndPlan 1),
  (some "When the fifth plan counter is put on this enchantment, sacrifice it. When you do, target opponent exiles the top five cards of their library. You may cast up to two spells from among the exiled cards without paying their mana costs.", .onFifthPlanExileTopCast),
  (some "Whenever Grim Reaper attacks, you may pay {3}{B}. When you do, return target creature card from your graveyard to the battlefield tapped and attacking with a finality counter on it.", .thisAttackPayReturnAttacking),
  (none, .onEnterTargetOpponentDiscards 2),
  (some "Whenever a creature you control attacks alone, target opponent loses 1 life and you gain 1 life.", .watchAttacksAloneDrain),
  (some "When this creature enters, create a tapped 2/1 black Villain creature token with menace if there are two or more creature cards in your graveyard. Otherwise, mill two cards.", .onEnterVillainIfGyElseMill),
  (none, .onEnter Effect.enterRevealDiscardFromHand),
  (none, .onYouDrawSecondCreateTokens .villain21menace),
  (some "Whenever you discard a card, you may exile that card from your graveyard. If you do, until the end of your next turn, you may play that card.", .resourceDiscardExilePlay),
  (none, .onCreatureCardsToGyDrawLoseLifeAndPlan),
  (none, .onThirdPlanCreateRobots),
  (some "Whenever you draw your second card each turn, put a +1/+1 counter on target creature.", .resourceSecondDrawPlusOneTarget),
  (none, .onEnterAttachThen (fun o => Instruction.grantKeywords o #[Keyword.indestructible])),
  (some "Whenever another Villain you control enters, attach up to one target Equipment you control to target creature you control.", .watchVillainAttachEquipment),
  (none, .onEquippedCreatureYouControlAttacksConnive),
  (some "Whenever a Villain you control dies, return it to the battlefield under its owner's control with a finality counter on it. That creature is a Hero in addition to its other types.", .deathVillainReturnAsHero),
  (some "Whenever Whiplash attacks, if he's equipped, each opponent loses X life and you gain X life, where X is the number of Equipment attached to him.", .thisAttackEquippedDrain),
  (some "Whenever another Villain you control enters, Yellowjacket gets +1/+0 and gains lifelink until end of turn.", .watchVillainPlusOneLifelink),
  (none, .onCastNoncreatureTreasureAndPlan),
  (some "When the fourth plan counter is put on this enchantment, sacrifice it. When you do, it deals 7 damage divided as you choose among one or two targets.", .onFourthPlanDividedDamage),
  (some "Whenever you cast an instant or sorcery spell that targets an artifact or land, copy that spell. You may choose new targets for the copy. Put two +1/+1 counters on Fin Fang Foom.", .castingCopyIfArtifactOrLand),
  (some "Trick Arrows — Whenever Hawkeye becomes tapped, you may pay {1} up to three times. When you do, choose up to that many — • Net — Target creature can't block this turn. • Explosive — Hawkeye deals 2 damage to target player. • Boomerang — Discard a card, then draw a card.", .watchHawkeyeModes),
  (some "Whenever equipped creature becomes tapped, it deals 1 damage to each opponent.", .watchEquippedTappedDamage),
  (some "Whenever you draw a card, if you control another Hero, Human Torch deals 1 damage to target opponent.", .resourceDrawIfAnotherHeroDamage),
  (some "Whenever another Villain and/or artifact you control enters, this creature deals 1 damage to target opponent.", .watchVillainOrArtifactDamage),
  (some "Whenever you cast a spell that targets a creature you control, Iron Fist gains \"{T}: Iron Fist deals damage equal to his power to any other target\" until end of turn.", .castingIronFistTap),
  (some "When this creature enters, you may sacrifice an artifact or discard a card. If you do, draw a card.", .onEnterMaySacArtifactOrDiscardDraw),
  (none, .onAnotherArtifactEntersPlusOne),
  (none, .onEnter (Effect.enterDealDamageUpToOne 4)),
  (some "Enrage — Whenever Red Hulk is dealt damage, put a +1/+1 counter on him. When you do, he deals damage equal to the number of +1/+1 counters on him to any other target.", .watchRedHulk),
  (some "Whenever you cast a noncreature spell, you may pay {1}. When you do, target creature with haste can't be blocked this turn except by creatures with haste.", .castingMayPayHasteUnblockable),
  (none, .onEnterEnchanted (fun o => Instruction.grantKeywords o #[Keyword.firstStrike])),
  (none, .onEnter Effect.enterExileGyPlayUntilNextTurn),
  (some "Whenever you cast a noncreature spell, Thor deals damage equal to that spell's mana value to any target.", .castingDamageEqualMv),
  (some "When this creature enters, create a Food token or a Treasure token.", .onEnterCreateFoodOrTreasure),
  (none, .onLandYouControlEntersPlusOneAndPlan),
  (none, .onFourthPlanIndestructible),
  (some "When Hellcat dies, return her to the battlefield under her owner's control with a +1/+1 counter on her. She loses all abilities and gains haste.", .deathHellcatReturn),
  (none, .onEnterCreateTokens .food 1),
  (some "Whenever you gain life, choose up to that many target creatures you control. Put a +1/+1 counter on each of them.", .resourceGainLifePlusOnes),
  (some "Whenever another creature you control enters, if it has greater power or toughness than Hulkling, put a +1/+1 counter on Hulkling.", .watchHulklingCompare),
  (none, .onEnter Effect.enterCreateZabu),
  (some "Whenever you put a +1/+1 counter on another creature, put a +1/+1 counter on this creature. This ability triggers only once each turn.", .resourcePlusOneOnThisOnce),
  (some "At the beginning of your upkeep, choose one — • Put a +1/+1 counter on Mister Hyde. • Remove a counter from a creature you control. If you do, draw a card.", .stepHydeChoose),
  (none, .onLandYouControlEntersCreateTokens .moloid 1),
  (some "Whenever one or more Heroes you control deal damage to a player, put two +1/+1 counters on The Thing.", .watchHeroesDamagePlusTwo),
  (none, .onGainLifePlusOne),
  (none, .onCombatPlusOneOnCreatureYouControl),
  (some "Do You Like Squirrels? — Whenever The Unbeatable Squirrel Girl enters or attacks, create a 1/1 green Squirrel creature token.", .enterOrAttackCreateSquirrel),
  (some "When this creature enters, put a +1/+1 counter on target creature. If that creature is another Hero, put two +1/+1 counters on it instead.", .onEnterPlusOneOrTwoIfAnotherHero),
  (some "At the beginning of your first main phase, until your next turn, Absorbing Man becomes a copy of up to one target artifact, non-Aura enchantment, or land, except his name is Absorbing Man, he's a legendary 4/4 Human Villain creature in addition to his other types, and he has vigilance.", .stepCopyAbsorbingMan),
  (none, .onCombatCreateAlienPerInvasion),
  (some "Whenever Ant-Man attacks, you may pay {1}. When you do, put a +1/+1 counter on target creature.", .thisAttackMayPayPlusOne),
  (some "Whenever you put a +1/+1 counter on a creature, create a 1/1 green Insect creature token. This ability triggers only once each turn.", .resourcePlusOneCreateInsectOnce),
  (some "Whenever an attacking creature you control dies, return that card to its owner's hand.", .deathAttackingReturnHand),
  (some "Whenever another nontoken Hero you control enters, choose one — • Create a 1/1 white Soldier creature token. • Creatures you control get +1/+1 until end of turn.", .watchNontokenHeroModal),
  (some "Whenever a creature you control attacks alone, it gains first strike and menace until end of turn.", .watchAttacksAloneFirstStrikeMenace),
  (none, .onEnter Effect.enterMaySacOrDiscardNonlandThenDamage),
  (some "Whenever a creature you control becomes tapped during your turn, if it's the first time that creature has become tapped this turn, untap it.", .watchFirstTapUntap),
  (none, .onEnter Effect.enterRevealHandExileUntilLeaves),
  (some "Whenever you attack, you may exile the top card of your library. If that card is a Hero card, Daredevil gets +2/+1 until end of turn. You may play that card this turn.", .youAttackingExileTopHeroPump),
  (some "Whenever Iron Man attacks, if an artifact entered the battlefield under your control this turn, draw a card.", .thisAttackIfArtifactEnteredDraw),
  (none, .onAttackConnive),
  (some "Whenever you draw your second card each turn, each opponent loses 1 life and you gain 1 life.", .resourceSecondDrawDrain),
  (none, .onEnter Effect.enterMaySacAnotherThenDestroyOppNonland),
  (some "Whenever a player draws their second card each turn, you draw a card.", .watchAnyPlayerSecondDraw),
  (some "Whenever you attack, you may pay 2 life. If you do, until end of turn, creatures you control with toughness greater than their power assign combat damage equal to their toughness rather than their power.", .youAttackingPay2LifeToughness),
  (some "Whenever you cast a Villain spell, create a 2/1 black Villain creature token with menace.", .castingVillainToken),
  (some "Whenever The Mighty Thor attacks, exile up to one target nontoken artifact or creature, then return that card to the battlefield tapped under its owner's control.", .thisAttackBlinkNontoken),
  (none, .onEquipmentYouControlEntersDraw),
  (some "Whenever you draw your second card each turn, until end of turn, Moon Girl and Devil Dinosaur's base power and toughness become 6/6 and they gain trample.", .resourceSecondDrawBecome66),
  (none, .onArtifactYouControlEntersDrawOnce),
  (some "When this enters, choose up to X — • Discard a card, then draw a card. • Target opponent loses 2 life. • Destroy target token. • Each player sacrifices a creature of their choice.", .onEnter Effect.enterChooseUpToXModes),
  (some "Whenever another creature you control with deathtouch dies, each opponent sacrifices a nontoken creature of their choice.", .deathDeathtouchOppSac),
  (some "Whenever a player casts a spell that targets Speedball, he gets +2/+2 until end of turn. You may choose new targets for that spell.", .watchSpeedballTargeted),
  (none, .onEnter Effect.enterMayTapThenGrantIndestructible),
  (none, .onEnter Effect.enterTapOppCantUntapWhileControl),
  (some "Whenever you cast a spell that targets one or more creatures, those creatures gain flying until end of turn.", .castingTargetsGainFlying),
  (some "Photographic Reflexes — At the beginning of your first main phase, until your next turn, Taskmaster becomes a copy of up to one target creature on the battlefield or creature card in a graveyard, except his name is Taskmaster, Mercenary Mimic and he's a legendary Human Mercenary Villain creature.", .stepCopyTaskmaster),
  (none, .onEnter Effect.enterCreateSturdyShieldAttach),
  (none, .onCombatAnotherGetsSourcePower),
  (none, .onEnter Effect.enterFightUpToOne),
  (none, .onEnterSurveil 2),
  (some "Whenever equipped creature attacks, tap target creature defending player controls.", .watchEquippedAttacksTap),
  (some s!"Whenever you attack, look at the top six cards of your library. You may cast a spell from among them with mana value less than or equal to the greatest power among attacking creatures you control without paying its mana cost. {restOnBottomRandomPhrase}.", .youAttackingLookSixCast),
  (some "When this creature enters, draw a card, then you may put a land card from your hand onto the battlefield tapped.", .onEnterDrawMayPutLandTapped),
  (some "Whenever Super-Adaptoid enters or attacks, choose another target creature. If that creature has haste and Super-Adaptoid doesn't, put a haste counter on Super-Adaptoid. Do the same for flying, first strike, double strike, deathtouch, indestructible, lifelink, menace, reach, trample, and vigilance.", .enterOrAttackCopyKeywords),
  (some "At the beginning of your end step, if you have fewer than ten cards in hand, draw cards equal to the difference.", .stepDrawToTen),
  (some "Whenever another nontoken artifact you control enters, you may pay {2}. If you do, create a token that's a copy of it. If the token isn't a creature, it becomes a 2/2 Robot Villain creature in addition to its other types.", .watchUltronCopy),
  (some "Whenever you cast a noncreature spell, choose one that hasn't been chosen this turn — • Solar Beam — The Vision gains double strike until end of turn. • Density Control — The Vision gains indestructible until end of turn. • Technopathy — Draw a card.", .castingVisionModes),
  (some "Cybernetic Senses — Whenever Viv Vision attacks, draw a card if her power is 4 or greater.", .thisAttackDrawIfPower4),
  (none, .onEnterEmpowerJace 1),
  (none, TriggeredAbility.mkTrigger (.gainLife .you) { body := Instruction.putPlusOne .this 2 }),
  (none, .onLandYouControlEntersEmpowerJace 2),
  (some "At the beginning of your upkeep, if this creature isn't prepared, it becomes prepared.", .onYourUpkeepPrepareSource),
  (some "At the beginning of each end step, if three or more creatures died this turn, this creature becomes prepared.", .onEachEndStepPrepareIfThreeDied),
  (some "Whenever you activate a loyalty ability, if you removed two or more loyalty counters to activate it, draw a card.", .onActivateLoyaltyDrawIfRemovedTwo),
  (none, TriggeredAbility.mkTrigger (.youActivateLoyaltyAbility 0) (Effect.triggerCreateTokens .cadet 1)),
  (none, .onCastFirstNoncreatureEmpowerJace 1),
  (none, TriggeredAbility.mkTrigger .youCastNoncreature (Effect.triggerCreateTokens .sculpture 1)),
  (none, .onGainLifePlusOneEachSubtype .angel),
  (none, TriggeredAbility.mkTrigger .youCastTargetingOpponentOrTheirCreature { body := Instruction.putPlusOne .this 1 }),
  (none, .onLandYouControlEntersGainLife 1),
  (none, TriggeredAbility.mkTrigger (.subtypeYouControlEnters .plains)
    { targets := .creature, body := Instruction.putPlusOne (.target 0) 1 }),
  (some "Whenever you gain life, put a loyalty counter on Ajani.", .onGainLifeLoyaltyOnSource),
  (none, .onEnterGrantThenCounterByType #[Keyword.hexproof]),
  (none, .onEnterGrantThenCounterByType #[Keyword.deathtouch]),
  (none, .onEnterDestroyOppPermanentIfSixLands),
  (some "At the beginning of combat on your turn, another target creature you control gets +1/+1 until end of turn. If you've scried or surveilled this turn, put a +1/+1 counter on that creature instead.", .onYourBeginCombatPumpOrCounterIfScried),
  (none, TriggeredAbility.mkTrigger .stepEachUpkeep (Effect.triggerCreateTokens .forestTentacle 1)),
  (some "At the beginning of each opponent's draw step, you draw a card.", .onEachOpponentDrawStepDraw),
  (none, .onCastNoncreatureCreaturesGet 1 0),
  (none, .onDiesPutSourceCountersOnTarget),
  (some "Whenever a creature you control dies, put a charge counter on this enchantment.", .onCreatureYouControlDiesChargeCounter),
  (some "At the beginning of your first main phase, add {G} for each charge counter on this enchantment.", .onYourFirstMainAddGreenPerCharge),
  (none, .onScryOrSurveilMayPayDraw 2),
  (none, TriggeredAbility.mkTrigger .youScryOrSurveil { body := Instruction.pumpFixed .this 1 1 }),
  (none, .onScryOrSurveilCreaturesGetOnce 1 0),
  (some "When one or more of your opponents are dealt combat damage during your turn, draw two cards. If your library has no cards in it, you win the game. Fblthp's owner shuffles him into their library.", .onOpponentsDealtCombatDamageDrawTwoWin),
  (none, .onForestYouControlEntersPumpIfFiveOther),
  (some "At the beginning of your end step, if you gained life this turn, surveil 1. If you put a card with mana value less than or equal to the amount of life you gained this turn into your graveyard this way, put that card into your hand.", .onYourEndStepSurveilReturnIfGainedLife),
  (some "When you cast this spell, untap all lands you control.",
   TriggeredAbility.ofPattern .thisCast
    (Instruction.untap (.inZones .battlefield (.all #[.hasType .land, .controlledBy .you])))
    (activeZones := #[.stack])),
  (some "Whenever you cast a creature spell, exile up to one other target creature you control, then return that card to the battlefield under its owner's control.",
   TriggeredAbility.ofPattern .youCastCreature
    (Instruction.exile (.target 0) { delayedReturn? := some (.immediately false .owner) })
    (.single { domain := .anotherCreatureYouControl, count := .upTo 1 })
   ),
  (some "At the beginning of combat on your turn, you may remove a +1/+1 counter from this creature. If you do, put a +1/+1 counter on each other creature you control.",
   TriggeredAbility.ofPattern .stepYourBeginCombat
    (Instruction.may .you (some (CostSpec.ofItem (.removeCounters (.exact 1) (some .plusOnePlusOne) .self)))
      (Instruction.putPlusOne (.inZones .battlefield (.all #[.otherThan .this, .hasType .creature, .controlledBy .you])) 1))),
  (some "Whenever this creature attacks, empower Jace X, where X is the number of creatures you control.",
   TriggeredAbility.ofPattern .thisAttacks
    (Instruction.empower .jace (.aggregate .count .one (.inZones .battlefield (.all #[.hasType .creature, .controlledBy .you]))))),
  (some "When this Aura enters, tap enchanted creature. It becomes unprepared.",
   TriggeredAbility.ofPattern .thisEnters
    (.seq #[Instruction.tap .attachedHost, .permanent (.setDesignation .attachedHost .prepared false)])),
  (some "When this enchantment enters, the owner of up to one other target nonland permanent puts it on their choice of the top or bottom of their library.",
   TriggeredAbility.ofPattern .thisEnters
    (.moveZone (.target 0) (.library .owner .top true) .put)
    (.single {
      domain := .object .battlefield (.all #[.otherThan .this, .not (.hasType .land)])
      count := .upTo 1 })
   ),
  (some "When this creature enters, draw two cards, then discard two cards. When you discard one or more nonland cards this way, tap up to that many target creatures and put a stun counter on each of them.",
   TriggeredAbility.ofPattern .thisEnters
    (.seq #[
      Instruction.drawFixed 2,
      .bind ⟨0⟩ (Instruction.discardFixed 2)
        (Instruction.ifThen (.exists (.filter (.stepObjects ⟨0⟩) (.not (.hasType .land))))
          (.queueReflexiveTrigger {
            word := .when
            pattern := .discard .you (.not (.hasType .land))
            effect := {
              targets := (.single { domain := .creature, count := .upTo 2 })
              body := Instruction.tapAndStun .allTargets } }))])),
  (some "Whenever this creature attacks, draw a card, then discard a card.",
   TriggeredAbility.ofPattern .thisAttacks
    (.seq #[Instruction.drawFixed 1, Instruction.discardFixed 1])),
  (some "When this creature dies, if it isn't a token, create a token that's a copy of it.",
   TriggeredAbility.ofPattern .thisDies
    (.create (.tokens .you (.const 1) (.copyOf .this #[])))
    (interveningIf? := some TriggeredAbility.condSourceNotToken)),
  (some "When this creature enters or dies, you gain 2 life.",
   TriggeredAbility.ofPattern (.or .thisEnters .thisDies)
    (Instruction.gainLifeFixed 2)),
  (some "When this creature enters, mill three cards.",
   TriggeredAbility.ofPattern .thisEnters
    (Instruction.millFixed 3)),
  (some "At the beginning of combat on your turn, if two or more creatures died this turn, return this card from your graveyard to the battlefield.",
   TriggeredAbility.ofPattern .stepYourBeginCombat
    (.moveZone .this (.battlefield .controller) .put)
    (interveningIf? := some (TriggeredAbility.condCreaturesDiedThisTurn 2))
    (activeZones := #[.graveyard])),
  (some "When this Equipment enters, you may pay {2}. When you do, for each opponent, destroy up to one target creature or planeswalker that player controls.",
   TriggeredAbility.ofPattern .thisEnters
    (Instruction.may .you (some (CostSpec.ofGeneric 2))
      (.queueReflexiveTrigger {
        word := .when
        pattern := .thisEnters
        effect := {
          targets := (.forEachOpponentControlled (.any #[.hasType .creature, .hasType .planeswalker]) (.upTo 1))
          body := Instruction.destroy .allTargets } }))),
  (some "When this creature enters, target creature gets +2/+2 and gains deathtouch until end of turn.",
   TriggeredAbility.ofPattern .thisEnters
    (.seq #[Instruction.pumpFixed (.target 0) 2 2, Instruction.grantKeywords (.target 0) #[Keyword.deathtouch]])
    .creature),
  (some "Whenever this creature attacks, it deals 1 damage to each opponent and you gain 1 life.",
   TriggeredAbility.ofPattern .thisAttacks
    (.seq #[Instruction.dealDamageFixed (.players .opponents) 1, Instruction.gainLifeFixed 1])),
  (some "When this enchantment enters, it deals X damage to any target.",
   TriggeredAbility.ofPattern .thisEnters
    (Instruction.dealDamage (.targetSlot 0) .chosenX) .anyTarget),
  (some "Whenever you cast a noncreature spell, put a +1/+1 counter on this creature.",
   TriggeredAbility.ofPattern .youCastNoncreature
    (Instruction.putPlusOne .this 1)),
  (some "At the beginning of each upkeep, if an opponent was dealt noncombat damage last turn, return this card from your graveyard to your hand.",
   TriggeredAbility.ofPattern .stepEachUpkeep
    (Instruction.bounce .this)
    (interveningIf? := some TriggeredAbility.condOpponentDealtNoncombatDamageLastTurn)
    (activeZones := #[.graveyard])),
  (some "When this creature enters, creatures you control gain trample and get +X/+0 until end of turn, where X is the number of artifacts you control.",
   TriggeredAbility.ofPattern .thisEnters
    (.seq #[
      Instruction.pump (.inZones .battlefield (.all #[.hasType .creature, .controlledBy .you]))
        (.aggregate .count .one (.inZones .battlefield (.all #[.hasType .artifact, .controlledBy .you]))) (.const 0),
      Instruction.grantKeywords (.inZones .battlefield (.all #[.hasType .creature, .controlledBy .you])) #[Keyword.trample]])),
  (some "When this creature enters, search your library for a card, put it into your hand, shuffle, then discard a card at random.",
   TriggeredAbility.ofPattern .thisEnters
    (.seq #[
      .player (.searchLibrary {
        zones := .libraryOf .you
        filter := .anyObject
        count := .upTo (.const 1)
        dest := .hand .controller
        reveal := false
        shuffle := true }),
      Instruction.discardFixed 1 .you true])),
  (some "When this creature enters, create a 2/2 colorless Wizard Soldier creature token named Cadet.",
   TriggeredAbility.ofPattern .thisEnters
    (Instruction.createTokensFixed .cadet 1)),
  (some "Whenever one or more opponents are dealt noncombat damage, creatures you control get +1/+0 until end of turn.",
   TriggeredAbility.ofPattern .opponentsDealtNoncombatDamage
    (Instruction.pumpFixed (.inZones .battlefield (.all #[.hasType .creature, .controlledBy .you])) 1 0)
    (grouping := .oncePerBatch)),
  (some "When this creature enters, target instant or sorcery card in your graveyard gains flashback until end of turn. The flashback cost is equal to its mana cost.",
   TriggeredAbility.ofPattern .thisEnters
    (.stack (.mayCastOrPlay (.target 0) { duration := .untilEndOfTurn, landsAllowed := false, asFlashback := true }))
    (.ofDomain (.object .yourGraveyard (.all #[.any #[.hasType .instant, .hasType .sorcery], .isKind .card])))),
  (some "When this creature enters, you may discard a card. When you do, this creature deals 2 damage to any target.",
   TriggeredAbility.ofPattern .thisEnters
    (Instruction.may .you (some CostSpec.discardCard)
      (.queueReflexiveTrigger {
        word := .when
        pattern := .discard .you .anyObject
        effect := {
          targets := .anyTarget
          body := Instruction.dealDamageFixed (.targetSlot 0) 2 } }))),
  (some "Whenever this creature deals combat damage to a player, return target land card from your graveyard to your hand.",
   TriggeredAbility.ofPattern .thisDealsCombatDamageToPlayer
    (Instruction.bounce (.target 0))
    (.ofDomain (.object .yourGraveyard (.all #[.hasType .land, .isKind .card])))),
  (some "Whenever another creature you control enters, you gain 1 life.",
   TriggeredAbility.ofPattern .anotherCreatureYouControlEnters
    (Instruction.gainLifeFixed 1)),
  (some "Whenever this creature is dealt damage, you may search your library for up to that many land cards, put them onto the battlefield tapped, then shuffle.",
   TriggeredAbility.ofPattern .thisDealtDamage
    (Instruction.may .you none
      (.player (.searchLibrary {
        zones := .libraryOf .you
        filter := .hasType .land
        count := .upTo .eventAmount
        dest := .battlefield .controller
        mods := { tapped := true }
        reveal := false
        shuffle := true })))
    (grouping := .oncePerBatch)),
  (some "When this creature enters, create a Heartwood token.",
   TriggeredAbility.ofPattern .thisEnters
    (Instruction.createTokensFixed .heartwood 1)),
  (some "Whenever you put one or more loyalty counters on a planeswalker, put a +1/+1 counter on this creature.",
   TriggeredAbility.ofPattern .youPutLoyaltyCounters
    (Instruction.putPlusOne .this 1) (grouping := .oncePerBatch)),
  (some "When this creature enters, you may search your library for a basic land card, put that card onto the battlefield tapped, then shuffle.",
   TriggeredAbility.ofPattern .thisEnters
    (Instruction.may .you none
      (.player (.searchLibrary {
        zones := .libraryOf .you
        filter := .all #[.hasSupertype .basic, .hasType .land]
        count := .upTo (.const 1)
        dest := .battlefield .controller
        mods := { tapped := true }
        reveal := false
        shuffle := true })))),
  (some "When this creature enters, put three +1/+1 counters on target creature.",
   TriggeredAbility.ofPattern .thisEnters
    (Instruction.putPlusOne (.target 0) 3) .creature),
  (some "When this creature enters or dies, create a Heartwood token.",
   TriggeredAbility.ofPattern (.or .thisEnters .thisDies)
    (Instruction.createTokensFixed .heartwood 1)),
  (some "Whenever you gain life, draw a card. This ability triggers only once each turn.",
   TriggeredAbility.ofPattern (.gainLife .you)
    (Instruction.drawFixed 1) (limit := .onceEachTurn)),
  (some "Whenever you scry or surveil, put a +1/+1 counter on each creature you control.",
   TriggeredAbility.ofPattern .youScryOrSurveil
    (Instruction.putPlusOne (.inZones .battlefield (.all #[.hasType .creature, .controlledBy .you])) 1)),
  (some "When enchanted creature dies, return that card to the battlefield tapped under its owner's control.",
   TriggeredAbility.ofPattern .enchantedDies
    (.moveZone .triggerSubject (.battlefield .owner) .put { tapped := true })),
  (some "At the beginning of the end step, sacrifice this creature.",
   TriggeredAbility.ofPattern .stepEachEndStep
    (Instruction.sacrifice .this)),
  (some "Whenever a creature you control attacks, that creature deals 1 damage to each opponent.",
   TriggeredAbility.ofPattern .creatureYouControlAttacks
    (Instruction.dealDamageFixed (.players .opponents) 1 .triggerSubject)),
  (some "Whenever you gain life, create a colorless artifact token named Lotus with \"{T}, Sacrifice this token: Add three mana of any one color.\" This ability triggers only once each turn.",
   TriggeredAbility.ofPattern (.gainLife .you)
    (Instruction.createTokensFixed .lotus 1) (limit := .onceEachTurn)),
  (some "When this creature enters, it fights up to one target creature an opponent controls.",
   TriggeredAbility.ofPattern .thisEnters
    (.damage (.fight .this (.target 0) false))
    (.single { domain := .oppCreature, count := .upTo 1 })
   ),
  (some "When this creature enters, if you cast it, target opponent reveals their hand. You choose a nonland card from it. Exile that card.",
   TriggeredAbility.ofPattern .thisEnters
    (.seq #[
      .player (.reveal (.target 0) (.inZones (.handOf (.target 0)) .anyObject)),
      .moveZone (.inZones (.handOf (.target 0)) (.not (.hasType .land))) .exile .exile
        { exileUntilSourceLeaves := true
          choice? := some { chooser := .controller, count := .exact (.const 1), revealFirst := true } }])
    .opponent (interveningIf? := some TriggeredAbility.condSourceWasCast)),
  (some "When this creature enters, mill four cards. When you do, return target land card from your graveyard to the battlefield tapped.",
   TriggeredAbility.ofPattern .thisEnters
    (.seq #[
      Instruction.millFixed 4,
      .queueReflexiveTrigger {
        word := .when
        pattern := .thisEnters
        effect := {
          targets := (.ofDomain (.object .yourGraveyard (.all #[.hasType .land, .isKind .card])))
          body := .moveZone (.target 0) (.battlefield .controller) .put { tapped := true } } }])),
  (some "Whenever this creature or another creature you control enters, surveil 1.",
   TriggeredAbility.ofPattern .thisOrAnotherCreatureYouControlEnters
    (Instruction.surveilFixed 1)),
  (some "Whenever an opponent casts a spell with mana value 2 or less, you gain 2 life.",
   TriggeredAbility.ofPattern (.opponentCastsSpellMvAtMost 2)
    (Instruction.gainLifeFixed 2)),
  (some "When this artifact enters, exile target nonland permanent an opponent controls with mana value 3 or less until this artifact leaves the battlefield.",
   TriggeredAbility.ofPattern .thisEnters
    (Instruction.exile (.target 0) { exileUntilSourceLeaves := true })
    (.ofDomain (.object .battlefield (.all #[.not (.hasType .land), .controlledBy .opponent, .stat .manaValue .le (.const 3)])))),
  (some "When this creature enters, you may sacrifice a land. If you do, create two tapped Heartwood tokens.",
   TriggeredAbility.ofPattern .thisEnters
    (Instruction.may .you (some (CostSpec.ofItem (.sacrifice (.exact 1) (.filter (.hasType .land)))))
      (Instruction.createTokensFixed .heartwood 2 .you true))),
  (some "When this creature enters, if you cast him, exile up to one target nonland card of each card type from your graveyard. Copy those cards. You may cast any number of spells with total mana value 6 or less from among the copies without paying their mana costs.",
   TriggeredAbility.ofPattern .thisEnters
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
    (interveningIf? := some TriggeredAbility.condSourceWasCast)),
  (some "When this Equipment enters, it deals 3 damage to any target and you gain 3 life.",
   TriggeredAbility.ofPattern .thisEnters
    (.seq #[Instruction.dealDamageFixed (.targetSlot 0) 3, Instruction.gainLifeFixed 3]) .anyTarget),
  (some "Whenever this creature attacks, exile up to one target card from a graveyard.",
   TriggeredAbility.ofPattern .thisAttacks
    (Instruction.exile (.target 0))
    (.single { domain := .object .anyGraveyard .isCard, count := .upTo 1 })
   ),
  (some "Whenever you cast a prepared spell, copy it. You may choose new targets for the copy.",
   TriggeredAbility.ofPattern .youCastPreparedSpell
    (.stack (.copyStackObject .triggerSubject (.const 1) true))),
  (some "When this artifact enters, draw a card, then discard a card.",
   TriggeredAbility.ofPattern .thisEnters
    (.seq #[Instruction.drawFixed 1, Instruction.discardFixed 1])),
  (some "At the beginning of your upkeep, surveil 1. Then if there are seven or more cards in your graveyard, sacrifice this artifact, it deals 2 damage to each opponent, and you gain 2 life.",
   TriggeredAbility.ofPattern .stepYourUpkeep
    (.seq #[
      Instruction.surveilFixed 1,
      Instruction.ifThen (.cmp .ge (.playerMetric .graveyardSize .you) (.const 7))
        (.seq #[
          Instruction.sacrifice .this,
          Instruction.dealDamageFixed (.players .opponents) 2,
          Instruction.gainLifeFixed 2])])),
  (some "Whenever you cast an Equipment spell or a spell that targets a creature you control, draw a card. This ability triggers only once each turn.",
   TriggeredAbility.ofPattern .youCastEquipmentOrTargetingCreatureYouControl
    (Instruction.drawFixed 1) (limit := .onceEachTurn)),
  (some "Whenever another creature or planeswalker you control enters, you gain 1 life.",
   TriggeredAbility.ofPattern .anotherCreatureOrPlaneswalkerYouControlEnters
    (Instruction.gainLifeFixed 1)),
  (some "Whenever you scry or surveil, create a 1/1 colorless Thopter artifact creature token with flying. This ability triggers only once each turn.",
   TriggeredAbility.ofPattern .youScryOrSurveil
    (Instruction.createTokensFixed .thopter 1) (limit := .onceEachTurn)),
  (some "Whenever you gain life, put a loyalty counter on each planeswalker you control.",
   TriggeredAbility.ofPattern (.gainLife .you)
    (Instruction.putCounters (.inZones .battlefield (.all #[.hasType .planeswalker, .controlledBy .you])) .loyalty (.const 1))),
  (some "Whenever a creature you control attacks a player alone, it gains double strike until end of turn.",
   TriggeredAbility.ofPattern .creatureYouControlAttacksPlayerAlone
    (Instruction.grantKeywords .triggerSubject #[Keyword.doubleStrike])),
  (some "Whenever another nontoken creature you control enters, untap this creature.",
   TriggeredAbility.ofPattern .anotherNontokenCreatureYouControlEnters
    (Instruction.untap .this)),
  (some "When this creature enters, for each opponent, tap up to one target creature that player controls. Put a stun counter on each of those creatures.",
   TriggeredAbility.ofPattern .thisEnters
    (Instruction.tapAndStun .allTargets) (.forEachOpponentControlled (.hasType .creature) (.upTo 1))
   ),
  (some "At the beginning of each end step, if you've drawn three or more cards this turn, create a 3/3 blue Angel creature token with flying.",
   TriggeredAbility.ofPattern .stepEachEndStep
    (Instruction.createTokensFixed .angel33blue 1) (interveningIf? := some (TriggeredAbility.condDrawnAtLeast 3))),
  (some "Whenever a creature an opponent controls enters, this creature deals 1 damage to that player.",
   TriggeredAbility.ofPattern .creatureOpponentControlsEnters
    (Instruction.dealDamageFixed (.players (.controllerOf .triggerSubject)) 1)),
  (some "Whenever an opponent activates a loyalty ability, this creature deals 1 damage to that player.",
   TriggeredAbility.ofPattern .opponentActivatesLoyaltyAbility
    (Instruction.dealDamageFixed (.players (.controllerOf .triggerSubject)) 1)),
  (some "Whenever another creature or planeswalker you control enters, mill two cards.",
   TriggeredAbility.ofPattern .anotherCreatureOrPlaneswalkerYouControlEnters
    (Instruction.millFixed 2)),
  (some "When this creature enters, remove up to three counters from another target creature or planeswalker.",
   TriggeredAbility.ofPattern .thisEnters
    (.permanent (.modifyCounters (.remove none (.upTo (.const 3))) (.target 0)))
    (.ofDomain (.object .battlefield (.all #[.otherThan .this, .any #[.hasType .creature, .hasType .planeswalker]])))),
  (some "Whenever another creature or planeswalker you control dies, this creature deals 1 damage to target opponent and you gain 1 life.",
   TriggeredAbility.ofPattern .anotherCreatureOrPlaneswalkerYouControlDies
    (.seq #[Instruction.dealDamageFixed (.targetSlot 0) 1, Instruction.gainLifeFixed 1]) .opponent),
  (some "Whenever an opponent is dealt noncombat damage, put a +1/+1 counter on this creature.",
   TriggeredAbility.ofPattern (.damageDealt .anyObject (.player .opponent) (noncombatOnly := true))
    (Instruction.putPlusOne .this 1) (grouping := .perPlayerInBatch)),
  (some "Whenever a player discards one or more cards, this creature deals 1 damage to each opponent.",
   TriggeredAbility.ofPattern (.discard .any .anyObject)
    (Instruction.dealDamageFixed (.players .opponents) 1) (grouping := .perPlayerInBatch)),
  (some "Whenever a creature you control dies, put a loyalty counter on each planeswalker you control.",
   TriggeredAbility.ofPattern .creatureYouControlDies
    (Instruction.putCounters (.inZones .battlefield (.all #[.hasType .planeswalker, .controlledBy .you])) .loyalty (.const 1))),
  (some "When this creature enters, you may sacrifice a creature or planeswalker. When you do, each opponent sacrifices a creature of their choice.",
   TriggeredAbility.ofPattern .thisEnters
    (Instruction.may .you
      (some (CostSpec.ofItem (.sacrifice (.exact 1) (.filter (.any #[.hasType .creature, .hasType .planeswalker])))))
      (.forEach (.eachPlayer .opponent) ⟨0⟩
        (.moveZone
          (.inZones .battlefield (.all #[.hasType .creature, .controlledBy (PlayerFilter.ofExpr (.stepPlayers ⟨0⟩))]))
          .graveyard .sacrifice
          { choice? := some { chooser := .player (.stepPlayers ⟨0⟩), count := .exact (.const 1) } })))),
  (some "Whenever another creature you control enters, this creature gets +X/+0 until end of turn, where X is that creature's power.",
   TriggeredAbility.ofPattern .anotherCreatureYouControlEnters
    (Instruction.pump .this (.objectStat .power .triggerSubject) (.const 0))),
  (some "Whenever a creature you control attacks a player alone, discard a card, then draw a card. Then put a +1/+1 counter on that creature for each card you've discarded this turn.",
   TriggeredAbility.ofPattern .creatureYouControlAttacksPlayerAlone
    (.seq #[
      Instruction.discardFixed 1,
      Instruction.drawFixed 1,
      Instruction.putCounters .triggerSubject .plusOnePlusOne (.playerMetric .cardsDiscardedThisTurn .you)])),
  (some "When this creature enters, create a 5/5 red Dragon creature token with flying.",
   TriggeredAbility.ofPattern .thisEnters
    (Instruction.createTokensFixed .dragon55flying 1)),
  (some "Whenever a land you control enters, this creature deals 1 damage to each opponent. If that land is a Mountain, add {R}.",
   TriggeredAbility.ofPattern .landYouControlEnters
    (.seq #[
      Instruction.dealDamageFixed (.players .opponents) 1,
      Instruction.ifThen (.exists (.filter .triggerSubject (.hasSubtype (.literal .mountain))))
        (Instruction.addSimpleMana #[.colored .red])])),
  (some "When this creature enters, create a 1/1 colorless Thopter artifact creature token with flying.",
   TriggeredAbility.ofPattern .thisEnters
    (Instruction.createTokensFixed .thopter 1)),
  (some "Whenever a creature an opponent controls with power or toughness 1 or less blocks, this creature deals 1 damage to that creature's controller.",
   TriggeredAbility.ofPattern .opponentSmallCreatureBlocks
    (Instruction.dealDamageFixed (.players (.controllerOf .triggerSubject)) 1)),
  (some "At the beginning of your end step, if you didn't cast a spell this turn, put two +1/+1 counters on this creature.",
   TriggeredAbility.ofPattern .stepYourEndStep
    (Instruction.putPlusOne .this 2) (interveningIf? := some TriggeredAbility.condCastNoSpellThisTurn)),
  (some "When this creature enters, search your library for up to X basic land cards with different names, reveal them, put them into your hand, then shuffle.",
   TriggeredAbility.ofPattern .thisEnters
    (.player (.searchLibrary {
      zones := .libraryOf .you
      filter := .all #[.hasSupertype .basic, .hasType .land]
      count := .upTo .chosenX
      groupConstraint? := some .distinctNames
      dest := .hand .controller
      reveal := true
      shuffle := true }))),
  (some "Whenever a creature you control with power 4 or greater enters, draw a card.",
   TriggeredAbility.ofPattern (.creatureYouControlPowerAtLeastEnters 4)
    (Instruction.drawFixed 1)),
  (some "When this creature enters, create Mowu, a legendary 3/3 green Dog creature token.",
   TriggeredAbility.ofPattern .thisEnters
    (Instruction.createTokensFixed .mowu 1)),
  (some "At the beginning of your end step, untap all tokens you control.",
   TriggeredAbility.ofPattern .stepYourEndStep
    (Instruction.untap (.inZones .battlefield (.all #[.isToken true, .controlledBy .you])))),
  (some "When this creature enters, you may discard a card. If you do, search your library for an enchantment card, reveal it, put it into your hand, then shuffle.",
   TriggeredAbility.ofPattern .thisEnters
    (Instruction.may .you (some CostSpec.discardCard)
      (.player (.searchLibrary {
        zones := .libraryOf .you
        filter := .hasType .enchantment
        count := .upTo (.const 1)
        dest := .hand .controller
        reveal := true
        shuffle := true })))),
  (some "When you discard this card, you gain 3 life.",
   TriggeredAbility.ofPattern .thisDiscarded
    (Instruction.gainLifeFixed 3)
    (activeZones := #[.hand])),
  (some "Whenever you activate a loyalty ability, you gain 1 life. You may play an additional land this turn.",
   TriggeredAbility.ofPattern (.youActivateLoyaltyAbility 0)
    (.seq #[Instruction.gainLifeFixed 1, Instruction.extraLand])),
  (some "When this creature enters, another target creature you control fights up to one target creature an opponent controls.",
   TriggeredAbility.ofPattern .thisEnters
    (.damage (.fight (.target 0) (.target 1) false))
    (.ofSlots #[.of .anotherCreatureYouControl, { domain := .oppCreature, count := .upTo 1 }])),
  (some "Whenever another creature or planeswalker you control dies, you gain 1 life.",
   TriggeredAbility.ofPattern .anotherCreatureOrPlaneswalkerYouControlDies
    (Instruction.gainLifeFixed 1)),
  (some "When this creature enters, for each opponent, put X -1/-1 counters on up to one target creature that player controls, where X is the greatest mana value among cards in your graveyard.",
   TriggeredAbility.ofPattern .thisEnters
    (Instruction.putCounters .allTargets .minusOneMinusOne
      (.aggregate .max (.stat .manaValue) (.inZones .yourGraveyard .isCard)))
    (.forEachOpponentControlled (.hasType .creature) (.upTo 1))
   ),
  (some "When this creature enters, draw a card for each color among other artifacts you control.",
   TriggeredAbility.ofPattern .thisEnters
    (.player (.drawCards .you
      (.colorCountAmong (.inZones .battlefield (.all #[.otherThan .this, .hasType .artifact, .controlledBy .you])))))),
  (some "Whenever you attack, if you've activated a loyalty ability this turn, untap target attacking creature. It can't be blocked this turn.",
   TriggeredAbility.ofPattern .youAttack
    (.seq #[Instruction.untap (.target 0), Instruction.cantBeBlocked (.target 0)])
    .attackingCreature
    (grouping := .oncePerBatch)
    (interveningIf? := some TriggeredAbility.condActivatedLoyaltyThisTurn)),
  (some "Whenever this creature or another creature you control enters, put a +1/+1 counter on target creature that entered this turn.",
   TriggeredAbility.ofPattern .thisOrAnotherCreatureYouControlEnters
    (Instruction.putPlusOne (.target 0) 1)
    (.ofDomain (.object .battlefield (.all #[.hasType .creature, .enteredThisTurn])))),
  (some "Whenever you cast a noncreature spell, create a 1/1 colorless Thopter artifact creature token with flying.",
   TriggeredAbility.ofPattern .youCastNoncreature
    (Instruction.createTokensFixed .thopter 1)),
  (some "Whenever you cast an artifact or creature spell, untap this creature.",
   TriggeredAbility.ofPattern .youCastArtifactOrCreature
    (Instruction.untap .this)),
  (some "Whenever a creature you control leaves the battlefield, if it had counters on it, put those counters on this artifact.",
   TriggeredAbility.ofPattern (.permanentLeaves (.all #[.hasType .creature, .controlledBy .you]))
    (.permanent (.modifyCounters (.copyFromLki .triggerSubject) .this))
    (interveningIf? := some TriggeredAbility.condTriggerSubjectHadCounters)),
  (some "At the beginning of combat on your turn, if this artifact has counters on it, you may move all counters from this artifact onto target creature.",
   TriggeredAbility.ofPattern .stepYourBeginCombat
    (Instruction.may .you none (.permanent (.modifyCounters (.moveAll .this none) (.target 0))))
    .creature (interveningIf? := some TriggeredAbility.condSourceHasCounters)),
  (some "When this creature enters, you may pay {3}. If you do, proliferate twice.",
   TriggeredAbility.ofPattern .thisEnters
    (Instruction.may .you (some (CostSpec.ofGeneric 3)) (.player (.proliferate .you (.const 2))))),
  (some "Whenever you proliferate, draw a card.",
   TriggeredAbility.ofPattern .youProliferate
    (Instruction.drawFixed 1))
]

def triggeredAbilities : Thunk (Array TriggeredAbility) := Thunk.mk fun _ => triggeredAbilityEntries.get.map (·.2)

def activatedAbilityEntries : Thunk (Array (Option String × ActivatedAbility)) := Thunk.mk fun _ => #[
  (some "Boast — Exile any number of black cards from your graveyard with fifteen or more black mana symbols among their mana costs: Copy those exiled cards. You may cast up to three of the copies without paying their mana costs.", ActivatedAbility.zemoBoastAbility),
  (none, activated (Effect.sourceGets 1 1) (ManaCost.ofGeneric 2)
          (costReductions := #[ActivationCostReduction.ifControlLegendary 2])),
  (none, {
        cost := CostSpec.ofItems #[.mana (ManaCost.ofGeneric 2), .tapSelf, .sacrifice (.exact 1) .self],
        effect := Effect.gainLife 3
      }),
  (none, equipAbility (ManaCost.ofGeneric 3)),
  (some "{5}{G}{G}: This enchantment becomes a Bear creature in addition to its other types and gains \"This creature's power and toughness are each equal to the number of lands you control.\"", activated (Effect.becomeBearCreatureWithLandsPT)
          (ManaCost.ofGenericAndColors 5 [.green, .green])),
  (none, activated (Effect.sourceGets 1 0) (ManaCost.ofGenericAndColor 1 .red)),
  (none, activated (Effect.targetCantBeBlockedThisTurn) (ManaCost.ofGeneric 4) (tap := true)),
  (none, activated (Effect.sourceGets 1 0) (ManaCost.ofColor .red)),
  (none, activated (Effect.putPlusOnePlusOneOnSource 3)
          (ManaCost.ofGenericAndColors 5 [.green, .green])),
  (none, activated (Effect.abilityCreaturesYouControlGet 1 1) (ManaCost.ofGenericAndColor 3 .white)),
  (none, activated (Effect.sourceGets 2 2) (payLife := 2) (turnLimit? := some 1)),
  (none, activated (Effect.returnFromGraveyardToHand) (ManaCost.ofGeneric 2)
          (sacrificeAnotherCreatureOrArtifact := true)
          (timing := .sorcery) (activeZones := #[.graveyard])),
  (some "Sacrifice another creature or artifact: Exile the top card of your library. You may play it until the end of your next turn. Activate only during your turn and only once each turn.", activated (Effect.exileTopPlayUntilEndOfNextTurn)
          (sacrificeAnotherCreatureOrArtifact := true)
          (condition? := some .isYourTurn) (turnLimit? := some 1)),
  (none, activated (Effect.targetCantBeBlockedThisTurn) (ManaCost.ofGenericAndColor 4 .blue)),
  (none, activated (Effect.searchBasicLandTapped) (tap := true) (sacrificeSource := true)),
  (none, typecyclingAbility "Halfling" (ManaCost.ofGeneric 4)),
  (none, activated (Effect.destroyTargetPermanent) (ManaCost.ofGeneric 7) (tap := true)
          (sacrificeSource := true)),
  (some "{2}{W/U}{W/U}: Return this card from your graveyard to the battlefield attached to target creature you control with power 1 or less. Activate only as a sorcery.", activated (Effect.returnFromGyAttachPowerAtMost 1)
          (ManaCost.ofGenericAndHybrids 2 .white .blue 2)
          (timing := .sorcery) (activeZones := #[.graveyard])),
  (some "{6}: This owner shuffles him into their library and draws three cards.", activated (Effect.ownerShuffleSourceDraw 3) (ManaCost.ofGeneric 6)),
  (none, activated (Effect.abilityDrawThenDiscard 1) (ManaCost.ofGeneric 2) (tap := true)),
  (none, activated (Effect.abilityDraw 1) (ManaCost.ofGeneric 1) (tap := true)
          (discardACard := true)),
  (none, activated (Effect.abilityCreateTokens .dwarf 1) (ManaCost.ofGenericAndColor 4 .red)
          (tap := true) (timing := .sorcery) (costReductions := #[ActivationCostReduction.perEquipment 1])),
  (none, activated (Effect.attachToTargetCreatureYouControl) (ManaCost.ofGeneric 2)
          (timing := .sorcery) (tag? := some (.equip none)) (payLife := 2)),
  (some "{2}, {T}, Sacrifice this creature: Search your library for up to two basic land cards, reveal them, put one onto the battlefield tapped and the other into your hand, then shuffle.", activated (Effect.searchTwoBasicsSplit) (ManaCost.ofGeneric 2)
          (tap := true) (sacrificeSource := true)),
  (some "{1}{B}: Goblins and Orcs you control gain menace until end of turn.", activated (Effect.subtypesGainMenace #["Goblin", "Orc"]) (ManaCost.ofGenericAndColor 1 .black)),
  (some "{5}{U}{U}: Exile up to two other target nonland permanents you control. Return those cards to the battlefield under their owner's control at the beginning of the next end step.", activated (Effect.exileThenReturnNextEnd) (ManaCost.ofGenericAndColors 5 [.blue, .blue])),
  (none, activated (Effect.searchBasicBeholdSubtypeUntap "Elf") (tap := true) (payLife := 1)
          (sacrificeSource := true)),
  (some "{2}{W}: Two target players each draw a card.", activated (Effect.twoPlayersDraw) (ManaCost.ofGenericAndColor 2 .white)),
  (none, activated (Effect.discardLegendarySameNameDraw) (ManaCost.ofGeneric 1) (tap := true)
          (discardLegendarySameName := true)),
  (none, activated (Effect.dealDamageToAny 4) (ManaCost.ofGenericAndColor 2 .red)
          (sacrificeArtifact := true)),
  (some "{1}, Sacrifice another creature: Draw cards equal to the sacrificed creature's power, then discard a card.", activated (Effect.drawEqualSacrificedPowerThenDiscard) (ManaCost.ofGeneric 1)
          (sacrificeAnotherCreature := true)),
  (none, typecyclingAbility "Plains"),
  (none, equipAbility (ManaCost.ofGeneric 1) (some .human)),
  (none, activated (Effect.destroyTargetArtifactOrEnchantment) (sacrificeSource := true)
          (timing := .sorcery)),
  (none, activated (Effect.abilityCreaturesYouControlGet 1 1)
          (ManaCost.ofGenericAndColor 4 .white) (tap := true)
          (costReductions := #[ActivationCostReduction.ifControlLegendary 2])),
  (none, activated (Effect.millPlayer 3) (ManaCost.ofGenericAndColor 5 .blue) (tap := true)),
  (some "{2}{B}: Return this card from your graveyard to the battlefield tapped. Activate only if you control a legendary creature.", activated (Effect.returnFromGraveyardTapped) (ManaCost.ofGenericAndColor 2 .black)
          (activeZones := #[.graveyard]) (condition? := some ActivatedAbility.condControlsLegendaryCreature)),
  (none, activated (Effect.searchBasicLandTapped) (ManaCost.ofGeneric 2)
          (tap := true) (sacrificeSource := true)),
  (none, activated (Effect.dealDamageToTargetCreature 2) (ManaCost.ofGeneric 1)
          (sacrificeSource := true)
          (extraModes := #[Effect.destroyTargetColorlessNonland])),
  (none, activated (Effect.targetCantBeBlockedPowerAtMost 2) (tap := true)),
  (none, activated (Effect.abilityScry 2) (ManaCost.ofGenericAndColor 1 .blue) (tap := true)
          (condition? := some ActivatedAbility.condControlsLegendaryCreature)),
  (none, activated (Effect.abilityDrawThenDiscard 2) (ManaCost.ofGeneric 3) (tap := true)),
  (none, activated (Effect.abilityCreateTokensX .treasure) { symbols := #[.x, .x] }
          (tap := true) (sacrificeSource := true)),
  (none, activated (Effect.abilityDraw 1) (ManaCost.ofGenericAndColor 1 .white) (tap := true)
          (condition? := some (ActivatedAbility.condAttackedWithCreaturesAtLeast 2))),
  (none, activated (Effect.abilityCreateTokens .food 1) (ManaCost.ofGenericAndColor 1 .green)
          (tap := true) (tapAnUntappedCreatureYouControl := true)),
  (none, activated (Effect.creaturesYouControlGetOppsLoseLife 2 0 2)
          (ManaCost.ofGenericAndColors 1 [.black, .red])),
  (some "{1}, Remove an indestructible counter from this: Another target creature gains indestructible until end of turn. Put a +1/+1 counter and a lifelink counter on that creature and a +1/+1 counter and a lifelink counter on this.", activated (Effect.arwenShare) (ManaCost.ofGeneric 1) (removeIndestructibleCounter := true)),
  (some "{1}, {T}: Until end of turn, target creature gains \"Whenever this creature deals combat damage to a player, create a Treasure token.\"", activated (Effect.grantCombatDamageCreateTreasure) (ManaCost.ofGeneric 1) (tap := true)),
  (some "{3}{B}, {T}: Put a shadow counter on target creature. For as long as that creature has a shadow counter on it, it's a Wraith in addition to its other types.", activated (Effect.putShadowCounter) (ManaCost.ofGenericAndColor 3 .black) (tap := true)),
  (none, activated (Effect.damageEachOpponent 1) (ManaCost.ofGenericAndColors 1 [.black, .red]) (tap := true)),
  (some "{5}{B}{R}, {T}, Sacrifice this and a legendary artifact: Choose up to two creatures, then destroy the rest. Activate only as a sorcery.", activated (Effect.chooseTwoDestroyRest) (ManaCost.ofGenericAndColors 5 [.black, .red])
          (tap := true) (sacrificeSource := true) (sacrificeLegendaryArtifact := true)
          (timing := .sorcery)),
  (some "{1}{B}, {T}: Choose a player with the most life or tied for most life. Target creature can't be blocked by creatures that player controls this turn.", activated (Effect.blackGateUnblockable) (ManaCost.ofGenericAndColor 1 .black) (tap := true)),
  (some "{T}: Put a burden counter on this, then draw a card for each burden counter on this.", activated (Effect.burdenThenDraw) (tap := true)),
  (none, activated (Effect.teamGain #[Keyword.doubleStrike]) (ManaCost.ofGeneric 10)),
  (none, activated (Effect.sourceGainsIndestructibleTap) (discardACard := true)),
  (none, activated (Effect.plusOneOnEachOtherSubtype "Hero" 1) (ManaCost.empty) (tap := true)),
  (none, typecyclingAbility "Basic land" (ManaCost.ofGeneric 2)),
  (none, powerUpAbility (Effect.putPlusOnePlusOneOnSource 2) (ManaCost.ofGenericAndColor 4 .white)),
  (some "Power-up — {5}{W}{W}: Put a +1/+1 counter and an indestructible counter on this.", activated (Effect.plusOneAndIndestructibleCounter) (ManaCost.ofGenericAndColors 5 [.white, .white]) (tag? := some .powerUp)),
  (none, activated (Effect.pumpAttackingAloneGainLife) (ManaCost.empty) (tap := true)),
  (none, activated (Effect.transform) (ManaCost.ofGenericAndColors 3 [.green, .white, .white]) (timing := .sorcery)),
  (none, activated (Effect.harnessInfinityStone) (ManaCost.ofGenericAndColor 5 .white) (tap := true)),
  (none, activated (Effect.transform) (ManaCost.ofGenericAndColors 2 [.red, .white, .white]) (timing := .sorcery)),
  (some "Power-up — {W}{U}{B}{R}{G}: Put two +1/+1 counters on this, then look at the top seven cards of your library. You may put a Hero, Equipment, or Vehicle card from among them onto the battlefield. If it's a double-faced card, you may transform it. Put the rest on the bottom of your library in a random order.", activated (Effect.lookAtTopPutTypes 7 #["Hero", "Equipment", "Vehicle"]) (ManaCost.ofColors [.white, .blue, .black, .red, .green]) (tag? := some .powerUp)),
  (none, activated (Effect.anotherYouControlGetsAndGrant 2 0 #[Keyword.hexproof]) (ManaCost.ofGeneric 2) (tap := true)),
  (none, activated (Effect.tapTargetCreature) (ManaCost.ofGeneric 2) (tap := true)
        (costReductions := #[ActivationCostReduction.ifTargetPowerAtMost 1 3])),
  (none, powerUpAbility (Effect.putPlusOnePlusOneOnSource 3) (ManaCost.ofGenericAndColor 5 .blue)),
  (some "Power-up — {5}{U}: Put a +1/+1 counter on this creature and draw two cards.", activated (Effect.plusOneAndDraw 1 2) (ManaCost.ofGenericAndColor 5 .blue) (tag? := some .powerUp)),
  (none, activated (Effect.drawX) ({ symbols := #[.x, .x] }) (tap := true) (timing := .sorcery)),
  (none, activated (Effect.transform) (ManaCost.ofGenericAndColors 2 [.red, .red, .green, .green]) (timing := .sorcery)),
  (none, activated (Effect.copyControlledAbility .creature) (ManaCost.ofGeneric 1) (tap := true)),
  (none, equipAbility (ManaCost.ofGenericAndColor 2 .blue)),
  (none, activated (Effect.abilityDraw 2) (ManaCost.ofGenericAndColor 3 .blue) (sacrificeSource := true)),
  (some "{T}: Reveal the top card of your library. If it's an artifact card, draw a card.", activated (Effect.revealTopDrawIfArtifact) (ManaCost.empty) (tap := true)),
  (some "Power-up — {5}{U}{U}{U}: Put a +1/+1 counter on this. Take an extra turn after this one. During that turn, power-up abilities can't be activated.", activated (Effect.plusOneAndExtraTurn) (ManaCost.ofGenericAndColors 5 [.blue, .blue, .blue]) (tag? := some .powerUp)),
  (some "{1}, {T}: Target artifact you control becomes a copy of a second target artifact you control until end of turn, except it isn't legendary. Activate only as a sorcery.", activated (Effect.copyArtifactYouControlNotLegendary) (ManaCost.ofGeneric 1) (tap := true) (timing := .sorcery)),
  (none, activated (Effect.plusOneX) ({ symbols := #[.x, .colored .blue, .colored .blue] }) (tag? := some .powerUp)),
  (some "{1}, {T}: Look at the top four cards of your library. You may reveal an artifact card from among them and put it into your hand. Put the rest on the bottom of your library in a random order.", activated (Effect.lookAtTopRevealArtifact 4) (ManaCost.ofGeneric 1) (tap := true)),
  (none, activated (Effect.transform) (ManaCost.ofGenericAndColors 4 [.blue, .red]) (timing := .sorcery)),
  (none, activated (Effect.createTappedTokens .villain21menace 1) (ManaCost.ofGeneric 3) (tap := true)
        (condition? := some (ActivatedAbility.condGraveyardCreatureCardsAtLeast 2))),
  (none, activated (Effect.abilityDraw 1) (ManaCost.ofGenericAndColor 2 .black)
        (sacrificeArtifactOrCreature := true)),
  (none, activated (Effect.searchLandTypeToHand "Plan") (ManaCost.ofGenericAndColor 1 .black)
        (activeZones := #[.hand]) (discardSource := true)),
  (none, activated (Effect.connive) (condition? := some .isYourTurn) (payLife := 3)),
  (some "Power-up — {4}{B}: Each opponent discards a card. Put a +1/+1 counter on this creature.", activated (Effect.eachOppDiscardThenPlusOne) (ManaCost.ofGenericAndColor 4 .black) (tag? := some .powerUp)),
  (some "{2}{B}: Return this card from your graveyard to your hand.", activated (Effect.returnFromGraveyardToHand) (ManaCost.ofGenericAndColor 2 .black)),
  (none, activated (Effect.targetGets (-4) (-4)) (tap := true) (sacrificeEquipmentAttachedToSource := true)
          (timing := .sorcery)),
  (none, activated (Effect.abilityCreateTokens .wall04defender 1) (ManaCost.ofGenericAndColor 2 .white)),
  (none, activated (Effect.sourceGets 4 4) (ManaCost.ofGenericAndColor 3 .green)),
  (none, activated (Effect.dealDamageToTargetCreature 4) (ManaCost.ofGenericAndColor 4 .red)),
  (none, activated (Effect.abilityTargetPlayerDraw 4) (ManaCost.ofGenericAndColor 5 .blue)),
  (none, activated (Effect.returnGyCreatureThenPlusOne 2) (ManaCost.ofGenericAndColors 5 [.black, .black]) (tag? := some .powerUp)),
  (none, powerUpAbility (Effect.putPlusOnePlusOneOnSource 3) (ManaCost.ofGenericAndColor 6 .red)),
  (some "{T}, Put a stun counter on this: Exile the top X cards of your library, where X is this creature's power. You may play those cards this turn.", activated (Effect.exileTopXPlayThisTurn) (tap := true) (putStunCounterOnSource := true)),
  (some "{1}, {T}: When you next cast an instant or sorcery spell with mana value less than or equal to this creature's power this turn, copy that spell. You may choose new targets for the copy.", activated (Effect.nextInstantSorceryCopyIfMvAtMostSourcePower) (ManaCost.ofGeneric 1) (tap := true)),
  (none, powerUpAbility (Effect.putPlusOnePlusOneOnSource 2) (ManaCost.ofGenericAndColor 4 .red)),
  (some "{2}, {T}, Discard a card: Draw a card for each card you've discarded this turn.", activated (Effect.drawPerDiscardedThisTurn)
        (ManaCost.ofGeneric 2) (tap := true) (discardACard := true)),
  (none, equipWorthyAbility (ManaCost.ofGeneric 1)),
  (none, activated (Effect.abilityDealDamageToEachCreature 2) (ManaCost.ofGenericAndColor 2 .red)
          (activeZones := #[.hand]) (discardSource := true)),
  (some "Power-up — {4}{R}: Put a +1/+1 counter and a double strike counter on this.", activated (Effect.plusOneAndDoubleStrikeCounter) (ManaCost.ofGenericAndColor 4 .red) (tag? := some .powerUp)),
  (none, activated (Effect.abilityCreateTokens .treasure 1) (ManaCost.ofGeneric 2) (tap := true)),
  (none, powerUpAbility (Effect.putPlusOnePlusOneOnSource 2) (ManaCost.ofGenericAndColor 5 .red)),
  (none, powerUpAbility (Effect.putPlusOnePlusOneOnSource 2) (ManaCost.ofGenericAndColors 5 [.red, .red])),
  (none, activated (Effect.destroyTargetNoncreatureArtOrEnch)
        (sacrificeSource := true) (timing := .sorcery)),
  (some "Power-up — {4}{G}: Put a +1/+1 counter on this. He gains vigilance, indestructible, and haste until end of turn.", activated (Effect.plusOneAndGrant #[Keyword.vigilance, Keyword.indestructible, Keyword.haste]) (ManaCost.ofGenericAndColor 4 .green) (tag? := some .powerUp)),
  (some "Power-up — {6}{G}: Put a +1/+1 counter on this creature and create a 3/2 white Hero creature token with vigilance.", activated (Effect.plusOneAndCreateTokens 1 .hero32vigilance) (ManaCost.ofGenericAndColor 6 .green) (tag? := some .powerUp)),
  (some "{T}: For each kind of counter on target permanent or player, give that permanent or player another counter of that kind. Activate only as a sorcery.", activated (Effect.proliferateEachKind) (ManaCost.empty) (tap := true) (timing := .sorcery)),
  (some "Brontosaurus — {3}: Until end of turn, this becomes a Dinosaur Hero with base power and toughness 3/5 and gains reach and vigilance.", activated (Effect.becomeTypes #["Dinosaur", "Hero"] 3 5 #[Keyword.reach, Keyword.vigilance]) (ManaCost.ofGeneric 3)),
  (some "Tyrannosaurus Rex — {6}: Until end of turn, this becomes a Dinosaur Hero with base power and toughness 6/6 and gains trample.", activated (Effect.becomeTypes #["Dinosaur", "Hero"] 6 6 #[Keyword.trample]) (ManaCost.ofGeneric 6)),
  (some "{3}, {T}: Mill four cards. You may put a Hero or enchantment card from among those cards into your hand.", activated (Effect.millThenPutSubtypeOrEnchantment 4 "Hero") (ManaCost.ofGeneric 3) (tap := true)),
  (none, powerUpAbility (Effect.putPlusOnePlusOneOnSource 2) (ManaCost.ofGenericAndColor 3 .green)),
  (none, activated (Effect.destroyUpToOneThenPlusOne) (ManaCost.ofGenericAndColors 4 [.green, .green]) (tag? := some .powerUp)),
  (some "I LOVE Squirrels! — {1}{G}{G}{G}: Create X 1/1 green Squirrel creature tokens, where X is the number of Squirrels you control.", activated (Effect.createTokensEqualSubtype .squirrel11green "Squirrel") (ManaCost.ofGenericAndColors 1 [.green, .green, .green])),
  (some "Power-up — {5}{G}: Put a +1/+1 counter on this and create The Tiger God, a legendary 4/4 green Cat God creature token with \"The Tiger God can't be blocked by more than one creature.\"", activated (Effect.plusOneAndCreateTigerGod) (ManaCost.ofGenericAndColor 5 .green) (tag? := some .powerUp)),
  (none, activated (Effect.plusOneThenFightUpToOne) (ManaCost.ofGenericAndHybrids 5 .red .green 2) (tag? := some .powerUp)),
  (some "{2}{G}, {T}, Remove any number of +1/+1 counters from this: Create that many 1/1 green Insect creature tokens.", activated (Effect.createTokensEqualRemovedPlusOnes .insect11green)
        (ManaCost.ofGenericAndColor 2 .green) (tap := true) (removeAnyNumberPlusOne := true)),
  (none, activated (Effect.dealDamageToAny 2) (ManaCost.ofGeneric 3)
        (tap := true) (sacrificeArtifactOrDiscardNonland := true)),
  (none, powerUpAbility (Effect.putPlusOnePlusOneOnSource 5) (ManaCost.ofGenericAndColors 6 [.red, .green])),
  (none, activated (Effect.transform) (ManaCost.ofGenericAndColors 4 [.white, .blue]) (timing := .sorcery)),
  (none, activated (Effect.copyControlledAbility .artifact)
        (turnLimit? := some 1) (condition? := some .isYourTurn) (payLife := 2)),
  (some "Power-up — {C}{W}{U}{B}{R}{G}: Put two +1/+1 counters on this. Choose odd or even. Destroy each other creature with mana value of the chosen quality.", activated (Effect.plusTwoThenOddEvenDestroy) ({ symbols := #[.colorless, .colored .white, .colored .blue, .colored .black, .colored .red, .colored .green] }) (tag? := some .powerUp)),
  (some "{3}{W}{B}: Return this card from your graveyard to the battlefield with a finality counter on him. Then you may attach an Equipment you control to him.", activated (Effect.returnFromGyFinalityAttach) (ManaCost.ofGenericAndColors 3 [.white, .black])
        (activeZones := #[.graveyard])),
  (some "{2}: If this Equipment isn't a creature, it becomes a 0/0 Construct Hero artifact creature with flying and \"This creature gets +1/+1 for each artifact you control\" until end of turn.", activated (Effect.equipmentBecomesConstructHero) (ManaCost.ofGeneric 2)),
  (some "Power-up — {6}: Put two +1/+1 counters on this creature and create a 2/2 colorless Robot Villain artifact creature token.", activated (Effect.plusOneAndCreateTokens 2 .robotVillain22) (ManaCost.ofGeneric 6) (tag? := some .powerUp)),
  (none, powerUpAbility (Effect.putPlusOnePlusOneOnSource 2) (ManaCost.ofGeneric 7)),
  (some "{4}, {T}: Look at the top three cards of your library. You may reveal a Hero card from among them and put it into your hand. Put the rest on the bottom of your library in any order.", activated (Effect.lookAtTopRevealSubtype 3 "Hero") (ManaCost.ofGeneric 4) (tap := true)),
  (none, activated (Effect.abilityDraw 1) (ManaCost.ofGeneric 4) (tap := true)
          (condition? := some (ActivatedAbility.condControlsCreatureToughnessAtLeast 4))),
  (none, activated (Effect.abilityCreateTokens .doombot 1) (ManaCost.ofGeneric 3) (tap := true)
          (sacrificeArtifact := true) (timing := .sorcery)),
  (none, activated (Effect.targetSubtypeConnives "Villain") (ManaCost.ofGeneric 3) (tap := true) (timing := .sorcery)),
  (none, {
      cost := CostSpec.ofItems #[.mana (ManaCost.ofGeneric 2), .sacrifice (.exact 1) .self],
      effect := Effect.abilityDraw 1
    }),
  (none, activated (Effect.abilityEmpowerJace 2) (ManaCost.ofGeneric 6)),
  (none, activated (Effect.abilityEmpowerJace 2) (ManaCost.ofGenericAndColor 2 .blue) (tap := true)),
  (none, activated (Effect.targetCreatureBecomesPrepared) (ManaCost.ofGeneric 4) (tap := true)),
  (some "{W}{U}{B}{R}{G}, {T}: Each creature you control becomes prepared.", activated (Effect.eachCreatureYouControlBecomesPrepared)
          (ManaCost.ofColors [.white, .blue, .black, .red, .green]) (tap := true)),
  (some "{5}: This land becomes a copy of target creature you control until end of turn. The \"legend rule\" doesn't apply to permanents you control this turn.", activated (Effect.becomeCopyLegendRuleOff) (ManaCost.ofGeneric 5)),
  (none, activated (Effect.cantBeBlockedAnotherPowerAtMost 2) (ManaCost.ofGeneric 1) (tap := true)),
  (some "{W}{U}{B}{R}{G}, {T}: Proliferate X times, where X is the number of planeswalker types among planeswalkers you control.", activated (Effect.proliferatePlaneswalkerTypesTimes)
          (ManaCost.ofColors [.white, .blue, .black, .red, .green]) (tap := true)),
  (some "{B}{R}: Return this card from your graveyard to the battlefield with a finality counter on it. Activate only if an opponent has been dealt noncombat damage this turn.", activated (Effect.returnFromGyWithFinality) (ManaCost.ofColors [.black, .red])
          (activeZones := #[.graveyard]) (condition? := some ActivatedAbility.condOpponentDealtNoncombatDamageThisTurn)),
  (some "{3}{U}, Exile this card from your graveyard: Tap target creature and put a stun counter on it. Activate only as a sorcery.", activated (Effect.tapAndStunTargetCreature) (ManaCost.ofGenericAndColor 3 .blue)
          (timing := .sorcery) (activeZones := #[.graveyard]) (exileSourceFromGraveyard := true)),
  (none, activated (Effect.abilityEmpowerJace 2) (ManaCost.ofGeneric 1)
          (activeZones := #[.graveyard]) (exileSourceFromGraveyard := true)),
  (some "{3}, Exile this card from your hand: Target land gains \"{T}: Add {C}{C}\" until this card is cast from exile. You may cast this card for as long as it remains exiled.",
   ActivatedAbility.fra (FraCandidates.ab
      (.seq #[
        .stack (.mayCastOrPlay .this { duration := .whileInZone .this .exile, landsAllowed := false }),
        .installEffect (.applyContinuous (.whileInZone .this .exile) (.target 0)
          (.grantActivated #[ActivatedAbility.manaAbility (.sequence #[(.colorless, .const 2)]) CostSpec.tapOnly]))])
      .land)
    (CostSpec.ofItems #[.mana (ManaCost.ofGeneric 3), .exile (.exact 1) .yourHand .self false])
    (activeZones := #[.hand])),
  (some "{4}{W}: Creatures you control get +1/+1 until end of turn.",
   ActivatedAbility.fra (FraCandidates.ab
      (Instruction.pumpFixed (.inZones .battlefield (.all #[.hasType .creature, .controlledBy .you])) 1 1))
    (CostSpec.ofMana ⟨#[.generic 4, .colored .white]⟩)),
  (some "{3}{U}{U}, Exile this card from your graveyard: Draw two cards.",
   ActivatedAbility.fra (FraCandidates.ab (Instruction.drawFixed 2))
    (CostSpec.ofItems #[.mana ⟨#[.generic 3, .colored .blue, .colored .blue]⟩, .exile (.exact 1) .yourGraveyard .self false])
    (activeZones := #[.graveyard])),
  (some "{3}{U}: Surveil 1.",
   ActivatedAbility.fra (FraCandidates.ab (Instruction.surveilFixed 1))
    (CostSpec.ofMana ⟨#[.generic 3, .colored .blue]⟩)),
  (some "{U}, Sacrifice this creature: The next spell you cast this turn can't be countered.",
   ActivatedAbility.fra (FraCandidates.ab
      (.installEffect (.applyRule .untilEndOfTurn (.play (.nextSpellCantBeCountered .you .anyObject)))))
    (CostSpec.ofItems #[.mana ⟨#[.colored .blue]⟩, .sacrifice (.exact 1) .self])),
  (some "{2}: This creature gets +1/-1 until end of turn.",
   ActivatedAbility.fra (FraCandidates.ab (Instruction.pumpFixed .this 1 (-1)))
    (CostSpec.ofGeneric 2)),
  (some "{3}{B}, Exile this card from your graveyard: Return another target creature card from your graveyard to your hand.",
   ActivatedAbility.fra (FraCandidates.ab (Instruction.bounce (.target 0))
      (.ofDomain (.object .yourGraveyard (.all #[.otherThan .this, .hasType .creature, .isKind .card]))))
    (CostSpec.ofItems #[.mana ⟨#[.generic 3, .colored .black]⟩, .exile (.exact 1) .yourGraveyard .self false])
    (activeZones := #[.graveyard])),
  (some "{T}, Discard a card: Draw a card.",
   ActivatedAbility.fra (FraCandidates.ab (Instruction.drawFixed 1))
    (CostSpec.tapOnly.append CostSpec.discardCard)),
  (some "{3}{R}: Exile target creature or planeswalker you control. Reveal cards from the top of your library until you reveal a creature or planeswalker card. Put that card onto the battlefield and the rest on the bottom of your library in a random order. Activate only as a sorcery.",
   ActivatedAbility.fra (FraCandidates.ab
      (.bind ⟨0⟩
        (Instruction.exile (.target 0))
        (.player (.inspectLibrary {
          source := .revealUntil .you (.any #[.hasType .creature, .hasType .planeswalker]) (.const 1)
          action := .moveAll (.battlefield .controller)
          rest := .bottomRandom })))
      (.ofDomain (.object .battlefield (.all #[.any #[.hasType .creature, .hasType .planeswalker], .controlledBy .you]))))
    (CostSpec.ofMana ⟨#[.generic 3, .colored .red]⟩) (timing := .sorcery)),
  (some "Sacrifice this creature: Destroy target artifact or enchantment. If that permanent was a legendary enchantment, draw a card. Activate only as a sorcery.",
   ActivatedAbility.fra (FraCandidates.ab
      (.seq #[
        Instruction.destroy (.target 0),
        Instruction.ifThen (.exists (.filter (.target 0) (.all #[.hasSupertype .legendary, .hasType .enchantment])))
          (Instruction.drawFixed 1)])
      .artifactOrEnchantment)
    CostSpec.sacSelf (timing := .sorcery)),
  (some "{1}, Sacrifice another artifact: Put a +1/+1 counter on this creature. It gains your choice of trample, hexproof, or haste until end of turn.",
   ActivatedAbility.fra (FraCandidates.ab
      (.seq #[
        Instruction.putPlusOne .this 1,
        .player (.choose .you (.keyword #[Keyword.trample, Keyword.hexproof, Keyword.haste]))]))
    ((CostSpec.ofGeneric 1).append CostSpec.sacrificeAnotherArtifact)),
  (some "{4}{G}: Return this card from your graveyard to your hand.",
   ActivatedAbility.fra (FraCandidates.ab (Instruction.bounce .this))
    (CostSpec.ofMana ⟨#[.generic 4, .colored .green]⟩) (activeZones := #[.graveyard])),
  (some "{3}{G}, Discard this card: Destroy target creature with flying.",
   ActivatedAbility.fra (FraCandidates.ab (Instruction.destroy (.target 0))
      .creatureWithFlying)
    (CostSpec.ofItems #[.mana ⟨#[.generic 3, .colored .green]⟩, .discard (.exact 1) .self])
    (activeZones := #[.hand])),
  (some "{6}{G}{G}: This creature gets +4/+4 and gains trample until end of turn.",
   ActivatedAbility.fra (FraCandidates.ab (Instruction.pumpAndTrample .this 4 4))
    (CostSpec.ofMana ⟨#[.generic 6, .colored .green, .colored .green]⟩)),
  (some "{6}: Create a Heartwood token. Then this creature gets +X/+0 until end of turn, where X is the number of artifacts you control.",
   ActivatedAbility.fra (FraCandidates.ab
      (.seq #[
        Instruction.createTokensFixed .heartwood 1,
        Instruction.pump .this
          (.aggregate .count .one (.inZones .battlefield (.all #[.hasType .artifact, .controlledBy .you]))) (.const 0)]))
    (CostSpec.ofGeneric 6)),
  (some "{2}{W/B}: Return this card from your graveyard to your hand.",
   ActivatedAbility.fra (FraCandidates.ab (Instruction.bounce .this))
    (CostSpec.ofMana ⟨#[.generic 2, .hybrid .white .black]⟩) (activeZones := #[.graveyard])),
  (some "{4}{G}{W}: Target creature gains trample and lifelink until end of turn.",
   ActivatedAbility.fra (FraCandidates.ab (Instruction.grantKeywords (.target 0) #[Keyword.trample, Keyword.lifelink]) .creature)
    (CostSpec.ofMana ⟨#[.generic 4, .colored .green, .colored .white]⟩)),
  (some "{4}: Create a 2/2 colorless Wizard Soldier creature token named Cadet. Then creatures you control gain haste until end of turn.",
   ActivatedAbility.fra (FraCandidates.ab
      (.seq #[
        Instruction.createTokensFixed .cadet 1,
        Instruction.grantKeywords (.inZones .battlefield (.all #[.hasType .creature, .controlledBy .you])) #[Keyword.haste]]))
    (CostSpec.ofGeneric 4)),
  (some "{2}: Put target card from your graveyard on the bottom of your library.",
   ActivatedAbility.fra (FraCandidates.ab (.moveZone (.target 0) (.library .owner .bottom false) .put)
      (.ofDomain (.object .yourGraveyard .isCard)))
    (CostSpec.ofGeneric 2)),
  (some "{W}{U}: Return this card from your graveyard to the battlefield with a finality counter on it. Activate only if you've scried or surveilled this turn.",
   ActivatedAbility.fra (FraCandidates.ab
      (.moveZone .this (.battlefield .controller) .put { enterCounters := #[(.finality, .const 1)] }))
    (CostSpec.ofMana ⟨#[.colored .white, .colored .blue]⟩) (activeZones := #[.graveyard])
    (condition? := some ActivatedAbility.condScriedOrSurveilledThisTurn)),
  (some "{1}, {T}, Discard a legendary card: Draw a card.",
   ActivatedAbility.fra (FraCandidates.ab (Instruction.drawFixed 1))
    ((CostSpec.ofItems #[.mana (ManaCost.ofGeneric 1), .tapSelf]).append CostSpec.discardLegendaryCard)),
  (some "Tap two untapped artifacts you control: Put two +1/+1 counters on this creature.",
   ActivatedAbility.fra (FraCandidates.ab (Instruction.putPlusOne .this 2))
    CostSpec.tapTwoUntappedArtifacts),
  (some "Equip {3}. This ability costs {1} less to activate for each +1/+1 counter on the creature it targets.",
   ActivatedAbility.fra Effect.attachToTargetCreatureYouControl (CostSpec.ofGeneric 3) (timing := .sorcery)
    (tag? := some (.equip none))
    (costReductions := #[ActivationCostReduction.perPlusOneOnTarget])),
  (some "{2}: This creature gains flying until end of turn.",
   ActivatedAbility.fra (FraCandidates.ab (Instruction.grantKeywords .this #[Keyword.flying]))
    (CostSpec.ofGeneric 2)),
  (some "{5}, {T}, Exile this artifact: Destroy all creatures. Activate only as a sorcery.",
   ActivatedAbility.fra (FraCandidates.ab (Instruction.destroy (.inZones .battlefield (.hasType .creature))))
    (CostSpec.ofItems #[.mana (ManaCost.ofGeneric 5), .tapSelf, .exile (.exact 1) .battlefield .self false])
    (timing := .sorcery)),
  (some "{6}, Sacrifice this creature: Choose target creature or planeswalker an opponent controls. Its owner shuffles it into their library.",
   ActivatedAbility.fra (FraCandidates.ab
      (.moveZone (.target 0) (.library .owner .shuffledIn false) .shuffleIntoLibrary { shuffleAfter := true })
      .oppCreatureOrPlaneswalker)
    ((CostSpec.ofGeneric 6).append CostSpec.sacSelf)),
  (some "{2}, {T}, Discard a card: Draw a card.",
   ActivatedAbility.fra (FraCandidates.ab (Instruction.drawFixed 1))
    ((CostSpec.ofItems #[.mana (ManaCost.ofGeneric 2), .tapSelf]).append CostSpec.discardCard)),
  (some "{2}, {T}: Target creature that attacked this turn becomes prepared. Activate only as a sorcery.",
   ActivatedAbility.fra (FraCandidates.ab (Instruction.becomePrepared (.target 0))
      (.ofDomain (.object .battlefield (.all #[.hasType .creature, .attackedThisTurn]))))
    (CostSpec.ofItems #[.mana (ManaCost.ofGeneric 2), .tapSelf]) (timing := .sorcery)),
  (some "{1}{W}, Discard this card: It deals 4 damage to target attacking or blocking creature.",
   ActivatedAbility.fra (FraCandidates.ab (Instruction.dealDamageFixed (.targetSlot 0) 4)
      .attackingOrBlockingCreature)
    (CostSpec.ofItems #[.mana ⟨#[.generic 1, .colored .white]⟩, .discard (.exact 1) .self])
    (activeZones := #[.hand])),
  (some "{1}, {T}, Discard a card: Another target creature or planeswalker you control gains hexproof until end of turn.",
   ActivatedAbility.fra (FraCandidates.ab (Instruction.grantKeywords (.target 0) #[Keyword.hexproof])
      (.ofDomain (.object .battlefield (.all #[
        .otherThan .this, .any #[.hasType .creature, .hasType .planeswalker], .controlledBy .you]))))
    ((CostSpec.ofItems #[.mana (ManaCost.ofGeneric 1), .tapSelf]).append CostSpec.discardCard)),
  (some "{T}: Return another target permanent you control to its owner's hand. Activate only during your turn.",
   ActivatedAbility.fra (FraCandidates.ab (Instruction.bounce (.target 0))
      (.ofDomain (.object .battlefield (.all #[.otherThan .this, .controlledBy .you]))))
    CostSpec.tapOnly (condition? := some .isYourTurn)),
  (some "{T}: Target creature with a +1/+1 counter on it gains flying until end of turn.",
   ActivatedAbility.fra (FraCandidates.ab (Instruction.grantKeywords (.target 0) #[Keyword.flying])
      (.ofDomain (.object .battlefield (.all #[.hasType .creature, .counterCount (some .plusOnePlusOne) .ge (.const 1)]))))
    CostSpec.tapOnly),
  (some "{6}: Put a +1/+1 counter on target legendary creature.",
   ActivatedAbility.fra (FraCandidates.ab (Instruction.putPlusOne (.target 0) 1)
      (.ofDomain (.object .battlefield (.all #[.hasSupertype .legendary, .hasType .creature]))))
    (CostSpec.ofGeneric 6)),
  (some "{6}: Put a +1/+1 counter on target nonlegendary creature.",
   ActivatedAbility.fra (FraCandidates.ab (Instruction.putPlusOne (.target 0) 1)
      (.ofDomain (.object .battlefield (.all #[.not (.hasSupertype .legendary), .hasType .creature]))))
    (CostSpec.ofGeneric 6)),
  (some "{T}: Draw a card, then discard a card.",
   ActivatedAbility.fra (FraCandidates.ab (.seq #[Instruction.drawFixed 1, Instruction.discardFixed 1]))
    CostSpec.tapOnly),
  (some "{2}{U}: Untap target creature.",
   ActivatedAbility.fra (FraCandidates.ab (Instruction.untap (.target 0)) .creature)
    (CostSpec.ofMana ⟨#[.generic 2, .colored .blue]⟩)),
  (some "{3}{U}{U}: Until end of turn, whenever this creature deals combat damage to a player, draw two cards.",
   ActivatedAbility.fra (FraCandidates.ab
      (.installEffect (.applyContinuous .untilEndOfTurn .this
        (.grantTriggered #[TriggeredAbility.ofPattern .thisDealsCombatDamageToPlayer
        (Instruction.drawFixed 2)]))))
    (CostSpec.ofMana ⟨#[.generic 3, .colored .blue, .colored .blue]⟩)),
  (some "{4}{B}, Exile another creature card from your graveyard: Return this card from your graveyard to the battlefield tapped with a +1/+1 counter on her.",
   ActivatedAbility.fra (FraCandidates.ab
      (.moveZone .this (.battlefield .controller) .put { tapped := true, enterCounters := #[(.plusOnePlusOne, .const 1)] }))
    ((CostSpec.ofMana ⟨#[.generic 4, .colored .black]⟩).append CostSpec.exileAnotherCreatureCardFromGraveyard)
    (activeZones := #[.graveyard])),
  (some "{5}{B}: Return target creature or planeswalker card from your graveyard to the battlefield. Put a +1/+1 counter on this creature. Activate only as a sorcery.",
   ActivatedAbility.fra (FraCandidates.ab
      (.seq #[.moveZone (.target 0) (.battlefield .controller) .put, Instruction.putPlusOne .this 1])
      (.ofDomain (.object .yourGraveyard (.all #[.any #[.hasType .creature, .hasType .planeswalker], .isKind .card]))))
    (CostSpec.ofMana ⟨#[.generic 5, .colored .black]⟩) (timing := .sorcery) (tag? := some .exhaust)),
  (some "Sacrifice another creature or planeswalker: This creature gets -2/-0 until end of turn. Activate only if there are seven or more cards in your graveyard.",
   ActivatedAbility.fra (FraCandidates.ab (Instruction.pumpFixed .this (-2) 0))
    CostSpec.sacrificeAnotherCreatureOrPlaneswalker
    (condition? := some (ActivatedAbility.condGraveyardCardsAtLeast 7))),
  (some "{B}, Discard this card: Target creature gets -3/-1 until end of turn.",
   ActivatedAbility.fra (FraCandidates.ab (Instruction.pumpFixed (.target 0) (-3) (-1)) .creature)
    (CostSpec.ofItems #[.mana ⟨#[.colored .black]⟩, .discard (.exact 1) .self])
    (activeZones := #[.hand])),
  (some "{1}{R}, {T}: Put a +1/+1 counter on target creature that entered this turn.",
   ActivatedAbility.fra (FraCandidates.ab (Instruction.putPlusOne (.target 0) 1)
      (.ofDomain (.object .battlefield (.all #[.hasType .creature, .enteredThisTurn]))))
    (CostSpec.ofItems #[.mana ⟨#[.generic 1, .colored .red]⟩, .tapSelf])),
  (some "{8}: Create a 5/5 red Dragon creature token with flying.",
   ActivatedAbility.fra (FraCandidates.ab (Instruction.createTokensFixed .dragon55flying 1))
    (CostSpec.ofGeneric 8)),
  (some "{2}, {T}, Sacrifice an artifact or land: Draw a card.",
   ActivatedAbility.fra (FraCandidates.ab (Instruction.drawFixed 1))
    ((CostSpec.ofItems #[.mana (ManaCost.ofGeneric 2), .tapSelf]).append CostSpec.sacrificeArtifactOrLand)),
  (some "{5}{R}: Target creature gets +X/+0 until end of turn, where X is the number of artifacts you control.",
   ActivatedAbility.fra (FraCandidates.ab
      (Instruction.pump (.target 0)
        (.aggregate .count .one (.inZones .battlefield (.all #[.hasType .artifact, .controlledBy .you]))) (.const 0)) .creature)
    (CostSpec.ofMana ⟨#[.generic 5, .colored .red]⟩)),
  (some "{4}{G}: Put a +1/+1 counter on each creature you control with a +1/+1 counter on it.",
   ActivatedAbility.fra (FraCandidates.ab
      (Instruction.putPlusOne
        (.inZones .battlefield (.all #[.hasType .creature, .controlledBy .you, .counterCount (some .plusOnePlusOne) .ge (.const 1)])) 1))
    (CostSpec.ofMana ⟨#[.generic 4, .colored .green]⟩)),
  (some "{2}: Return target land card from your graveyard to your hand.",
   ActivatedAbility.fra (FraCandidates.ab (Instruction.bounce (.target 0))
      (.ofDomain (.object .yourGraveyard (.all #[.hasType .land, .isKind .card]))))
    (CostSpec.ofGeneric 2)),
  (some "{2}, Sacrifice another creature or planeswalker: Put a +1/+1 counter on this creature. He gains menace until end of turn.",
   ActivatedAbility.fra (FraCandidates.ab (.seq #[Instruction.putPlusOne .this 1, Instruction.grantKeywords .this #[Keyword.menace]]))
    ((CostSpec.ofGeneric 2).append CostSpec.sacrificeAnotherCreatureOrPlaneswalker))
]

def activatedAbilities : Thunk (Array ActivatedAbility) := Thunk.mk fun _ => activatedAbilityEntries.get.map (·.2)

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
