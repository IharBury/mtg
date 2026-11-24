import Mtg.Engine.Catalog.Hobbit
import Mtg.Engine.Catalog.HobbitEternal
import Mtg.Engine.Tests.Builders

/-!
# Hobbit & Hobbit Eternal catalog parse guards

Relocated from `Catalog/Hobbit.lean` and `Catalog/HobbitEternal.lean` so
production catalog modules remain decoupled from `Mtg.Engine.Tests.Builders`.
-/

namespace Mtg.Engine.Tests.CatalogHobbitGuards

open Mtg.Engine
open Mtg.Engine.Catalog

/-! ### Hobbit (`HOB`) guards -/

#guard bofurReliableGuardian.colors.isMonocolored
#guard (attercop.summary.splitOn "a land you control enters").length > 1
#guard (attercop.summary.splitOn "reach").length > 1
#guard attercop.hasSimpleKeyword .reach
#guard attercop.hasSimpleKeyword .deathtouch
#guard attercop.triggeredAbilities == #[.onLandYouControlEntersGets 1 1]
#guard raggedShortSpear.isEquipment
#guard !raggedShortSpear.isAura
#guard !raggedShortSpear.requiresTarget
#guard raggedShortSpear.staticAbilities == #[.equippedCreatureGets 2 0]
#guard raggedShortSpear.triggeredAbilities == #[.onEnterMayDiscardDraw 2]
#guard raggedShortSpear.allActivatedAbilities.size == 1
#guard raggedShortSpear.allActivatedAbilities[0]!.isSorcerySpeed
#guard raggedShortSpear.allActivatedAbilities[0]!.effect == Effect.attachToTargetCreatureYouControl
#guard raggedShortSpear.allActivatedAbilities[0]!.cost.mana == (ManaCost.ofGeneric 3)
#guard (raggedShortSpear.summary.splitOn "Equipped creature").length > 1
#guard crudeBentBlade.isEquipment
#guard !crudeBentBlade.isAura
#guard !crudeBentBlade.requiresTarget
#guard crudeBentBlade.staticAbilities == #[.equippedCreatureGets 2 1]
#guard crudeBentBlade.triggeredAbilities == #[.onEnterTargetOpponentSacrificesCreature]
#guard crudeBentBlade.allActivatedAbilities.size == 1
#guard crudeBentBlade.allActivatedAbilities[0]!.isSorcerySpeed
#guard crudeBentBlade.allActivatedAbilities[0]!.effect == Effect.attachToTargetCreatureYouControl
#guard crudeBentBlade.allActivatedAbilities[0]!.cost.mana == (ManaCost.ofGeneric 2)
#guard (crudeBentBlade.summary.splitOn "Equipped creature").length > 1
#guard (crudeBentBlade.summary.splitOn "target opponent").length > 1
#guard woodElves.triggeredAbilities == #[.onEnterSearchForest]
#guard (woodElves.summary.splitOn "Forest card").length > 1
#guard galionElvenkingsButler.triggeredAbilities == #[.onAttackSetOtherBasePT]
#guard (galionElvenkingsButler.summary.splitOn "base power and toughness").length > 1
#guard galionElvenkingsButler.power == some (.fixed 4)
#guard galionElvenkingsButler.toughness == some (.fixed 4)
#guard woodlandWeavemaster.hasSimpleKeyword .vigilance
#guard woodlandWeavemaster.triggeredAbilities == #[.onAnotherElfYouControlEntersGets1]
#guard woodlandWeavemaster.activatedAbilities[0]?.bind (·.manaProduction?) ==
  some { spec := .oneOf .anyColor (.objectStat .power .this)
         restriction := some (.subtypeSpellOrSource .elf) }
#guard woodlandWeavemaster.manaAbilities == #[
  .colored .white, .colored .blue, .colored .black, .colored .red, .colored .green]
#guard woodlandWeavemaster.power == some (.fixed 1)
#guard woodlandWeavemaster.toughness == some (.fixed 2)
#guard (woodlandWeavemaster.summary.splitOn "vigilance").length > 1
#guard (woodlandWeavemaster.summary.splitOn "another Elf").length > 1
#guard (woodlandWeavemaster.summary.splitOn "any one color").length > 1
#guard quarrel.isInstant
#guard quarrel.spellEffect == some (Effect.creatureYouControlDealsPowerToOppCreature)
#guard soundTheTrumpets.isInstant
#guard soundTheTrumpets.spellEffect == some (Effect.counterThenRecruitIfMvAtMost 2)
#guard soundTheTrumpets.hasCastKind .counter
#guard quarrel.requiresTarget
#guard Effect.creatureYouControlDealsPowerToOppCreature.targetCount == 2
#guard (quarrel.summary.splitOn "deals damage equal to its power").length > 1
#guard wargTactics.isInstant
#guard wargTactics.isModal
#guard wargTactics.requiresTarget
#guard wargTactics.modes == #[
  Effect.destroyCreatureWithFlying,
  Effect.plusOnePlusOneTrampleHexproof]
#guard (wargTactics.summary.splitOn "Choose one").length > 1
#guard (wargTactics.summary.splitOn "hexproof").length > 1
#guard beornsHospitality.isEnchantment
#guard !beornsHospitality.isCreature
#guard beornsHospitality.triggeredAbilities == #[.onLandYouControlEntersPlusOnePlusOne]
#guard beornsHospitality.activatedAbilities.size == 1
#guard beornsHospitality.activatedAbilities[0]!.effect == Effect.becomeSubtypeWithLandsPT "Bear"
#guard beornsHospitality.activatedAbilities[0]!.cost.mana ==
  (ManaCost.ofGenericAndColors 5 [.green, .green])
#guard (beornsHospitality.summary.splitOn "a land you control enters").length > 1
#guard (beornsHospitality.summary.splitOn "Bear creature").length > 1
#guard mirkwoodPathmaker.staticAbilities == #[.powerToughnessEqualLandsYouControl]
#guard mirkwoodPathmaker.power == some (.star 0)
#guard mirkwoodPathmaker.toughness == some (.star 0)
#guard (mirkwoodPathmaker.summary.splitOn "*/*").length > 1
#guard (mirkwoodPathmaker.summary.splitOn "lands you control").length > 1
#guard gandalfSparkStarter.hasSimpleKeyword .reach
#guard gandalfSparkStarter.triggeredAbilities == #[.onEnterDealDividedDamage 3 3]
#guard (gandalfSparkStarter.summary.splitOn "divided as you choose").length > 1
#guard (gandalfSparkStarter.summary.splitOn "reach").length > 1
#guard guardianOfTheHalls.hasSimpleKeyword .trample
#guard guardianOfTheHalls.activatedAbilities.size == 1
#guard guardianOfTheHalls.activatedAbilities[0]!.effect == Effect.putPlusOnePlusOneOnSource 3
#guard guardianOfTheHalls.activatedAbilities[0]!.cost.mana ==
  (ManaCost.ofGenericAndColors 5 [.green, .green])
#guard guardianOfTheHalls.power == some (.fixed 2)
#guard guardianOfTheHalls.toughness == some (.fixed 2)
#guard (guardianOfTheHalls.summary.splitOn "trample").length > 1
#guard (guardianOfTheHalls.summary.splitOn "+1/+1").length > 1
#guard desolationProwler.activatedAbilities.size == 1
#guard desolationProwler.activatedAbilities[0]!.effect == Effect.sourceGets 2 2
#guard desolationProwler.activatedAbilities[0]!.cost.payLife == 2
#guard desolationProwler.activatedAbilities[0]!.isOnceEachTurn
#guard desolationProwler.power == some (.fixed 2)
#guard desolationProwler.toughness == some (.fixed 2)
#guard (desolationProwler.summary.splitOn "Pay 2 life").length > 1
#guard raveningWarg.hasSimpleKeyword .deathtouch
#guard raveningWarg.triggeredAbilities == #[.onAttackFerociousGainLife 2]
#guard raveningWarg.power == some (.fixed 2)
#guard raveningWarg.toughness == some (.fixed 2)
#guard (raveningWarg.summary.splitOn "deathtouch").length > 1
#guard (raveningWarg.summary.splitOn "while you control a creature with power 4 or greater").length > 1
#guard (raveningWarg.summary.splitOn "power 4 or greater").length > 1
#guard (raveningWarg.summary.splitOn "gain 2 life").length > 1
#guard frontPorchSentries.triggeredAbilities == #[.onDiesOppCreatureGets (-1) (-1)]
#guard (frontPorchSentries.summary.splitOn "-1/-1").length > 1
#guard greatFierceBee.hasSimpleKeyword .flying
#guard greatFierceBee.triggeredAbilities == #[.onOneOrMoreOtherCreaturesDieScry 1]
#guard (greatFierceBee.summary.splitOn "other creatures die").length > 1
#guard stirUpTrouble.spellEffect == some (Effect.destroyCreature)
#guard stirUpTrouble.additionalCosts == #[AdditionalCostSpec.mandatory (CostSpec.sacrificeArtifactOrCreatureOrPayGeneric 4)]
#guard gollumSilentSlinker.hasSimpleKeyword .menace
#guard (gollumSilentSlinker.summary.splitOn "menace").length > 1
#guard bilbosDeadlySlice.spellEffect == some (Effect.destroyCreature)
#guard bilbosDeadlySlice.requiresTarget
#guard dreadedBatCloud.staticAbilities.contains (.costReductionIfCreatureDied 3)
#guard dreadedBatCloud.hasSimpleKeyword .flying
#guard dreadedBatCloud.hasSimpleKeyword .deathtouch
#guard crudeBentBlade.isEquipment
#guard crudeBentBlade.staticAbilities == #[.equippedCreatureGets 2 1]
#guard crudeBentBlade.triggeredAbilities == #[.onEnterTargetOpponentSacrificesCreature]
#guard crudeBentBlade.allActivatedAbilities.size == 1
#guard gollumTheAbandoned.staticAbilities == #[.cantBlockUnlessYouControl #[]]
#guard gollumTheAbandoned.triggeredAbilities == #[.onEnterExileOppGyCardOppsLoseLife 2]
#guard littleBear.triggeredAbilities == #[.onEnterUntapOtherPlusOneIfSubtype "Bear"]
#guard gandalfGoblinsBane.triggeredAbilities == #[.onCastNoncreaturePumpAndDamageOpponents 1]
#guard gollumTheAbandoned.activatedAbilities[0]!.isFromGraveyard
#guard gollumTheAbandoned.activatedAbilities[0]!.isSorcerySpeed
#guard gollumTheAbandoned.activatedAbilities[0]!.effect == Effect.returnFromGraveyardToHand
#guard gnashingOfTeeth.isModal
#guard gnashingOfTeeth.modes ==
  #[Effect.pumpAndExileIfDies (-5) (-5),
    Effect.creaturesTargetPlayerGet (-1) (-1)]
#guard reverentHowl.isModal
#guard reverentHowl.modes ==
  #[Effect.targetPlayerDrawLoseLife 2 2,
    Effect.pumpAndLifelink 2 2]
#guard stonyVoicedGoblins.triggeredAbilities == #[.onEnterEachOpponentDiscards]
#guard gollumSilentSlinker.power == some (.fixed 4)
#guard gollumSilentSlinker.toughness == some (.fixed 3)
#guard gollumSilentSlinker.supertypes.any (· == .legendary)
#guard !(gollumSilentSlinker.summary.splitOn "can't be blocked except").length > 1
#guard bilbosDeadlySlice.isInstant
#guard bilbosDeadlySlice.hasCastKind .destroyCreature
#guard (bilbosDeadlySlice.summary.splitOn "destroy target creature").length > 1
#guard smaugTheGreatCalamity.hasSimpleKeyword .flying
#guard smaugTheGreatCalamity.hasAdventure
#guard smaugTheGreatCalamity.supertypes.any (· == .legendary)
#guard smaugTheGreatCalamity.power == some (.fixed 5)
#guard smaugTheGreatCalamity.toughness == some (.fixed 5)
#guard
  match smaugTheGreatCalamity.adventure with
  | some adv =>
    adv.name == "Spew Flame" &&
      adv.manaCost == (ManaCost.ofGenericAndColor 4 .red) &&
      adv.types == #[.sorcery] &&
      adv.subtypes.any (· == "Adventure") &&
      adv.spellEffect == some (Effect.dealDamageToCreature 5)
  | none => false
#guard (smaugTheGreatCalamity.summary.splitOn "//ADV//").length == 1
#guard !smaugTheGreatCalamity.leftoverOracleLines.any (· == "//ADV//")
#guard (smaugTheGreatCalamity.summary.splitOn "//ADV//").length == 1
#guard (smaugTheGreatCalamity.summary.splitOn "Spew Flame {4}{R}").length > 1
#guard (smaugTheGreatCalamity.summary.splitOn "flying").length > 1
#guard beornReluctantHost.hasSimpleKeyword .trample
#guard beornReluctantHost.hasAdventure
#guard beornReluctantHost.supertypes.any (· == .legendary)
#guard beornReluctantHost.power == some (.fixed 5)
#guard beornReluctantHost.toughness == some (.fixed 5)
#guard
  match beornReluctantHost.adventure with
  | some adv =>
    adv.name == "Till and Tend" &&
      adv.manaCost == (ManaCost.ofGenericAndColor 1 .green) &&
      adv.types == #[.sorcery] &&
      adv.subtypes.any (· == "Adventure") &&
      adv.spellEffect == some (Effect.playAdditionalLandThisTurn) &&
      !adv.toCardDef.requiresTarget
  | none => false
#guard (beornReluctantHost.summary.splitOn "//ADV//").length == 1
#guard !beornReluctantHost.leftoverOracleLines.any (· == "//ADV//")
#guard (beornReluctantHost.summary.splitOn "Till and Tend {1}{G}").length > 1
#guard (beornReluctantHost.summary.splitOn "trample").length > 1
#guard (beornReluctantHost.summary.splitOn "additional land").length > 1
#guard (bofurReliableGuardian.summary.splitOn "Concerted Care {1}{W}").length > 1
#guard (velvetwingButterflies.summary.splitOn "Gaze in Wonder {1}{W}").length > 1
#guard (bilboBagginsBurglar.summary.splitOn "Take a Glance {U}").length > 1
#guard (bilboLuckwearer.summary.splitOn "Burglar's Plot {4}{U}").length > 1
#guard (gollumSilentSlinker.summary.splitOn "Meager Meal {B}").length > 1


/-! ### Hobbit Eternal (`HOC`) guards -/

#guard roguesPassage.isLand
#guard roguesPassage.activatedAbilities.size == 2
#guard roguesPassage.activatedAbilities[0]!.manaProduction? == some { spec := .fixedOne .colorless }
#guard roguesPassage.activatedAbilities[1]!.effect == Effect.targetCantBeBlockedThisTurn
#guard roguesPassage.activatedAbilities[1]!.cost.tap
#guard roguesPassage.activatedAbilities[1]!.cost.mana == (ManaCost.ofGeneric 4)
#guard elvishMystic.activatedAbilities[0]?.bind (·.manaProduction?) == some { spec := .fixedOne (.colored .green) }
#guard (wayfarersBauble.summary.splitOn "Search your library").length > 1
#guard (roguesPassage.summary.splitOn "can't be blocked").length > 1
#guard orcishSiegemaster.hasSimpleKeyword .trample
#guard orcishSiegemaster.staticAbilities == #[.otherCreaturesHaveTrample #[.orc, .goblin]]
#guard orcishSiegemaster.triggeredAbilities == #[.onAttackPumpByGreatestPower]
#guard (orcishSiegemaster.summary.splitOn "Other Orcs and Goblins").length > 1
#guard battleScarredGoblin.triggeredAbilities == #[.onBecomesBlockedDeal1ToBlockers]
#guard (battleScarredGoblin.summary.splitOn "becomes blocked").length > 1
#guard giftOfStrands.isAura
#guard giftOfStrands.hasSimpleKeyword .flash
#guard !giftOfStrands.hasSorcerySpeed
#guard giftOfStrands.hasInstantSpeed
#guard giftOfStrands.requiresTarget
#guard giftOfStrands.staticAbilities == #[.enchantedCreatureGets 3 3]
#guard giftOfStrands.triggeredAbilities == #[.onEnterScry 2]
#guard dunedainBlade.allActivatedAbilities.size == 2
#guard dunedainBlade.allActivatedAbilities[0]!.equipSubtype? == some .human
#guard dunedainBlade.allActivatedAbilities[1]!.equipSubtype? == none
#guard dunedainBlade.allActivatedAbilities[0]!.cost.mana == (ManaCost.ofGeneric 1)
#guard dunedainBlade.allActivatedAbilities[1]!.cost.mana == (ManaCost.ofGeneric 3)
#guard (giftOfStrands.summary.splitOn "flash").length > 1
#guard (giftOfStrands.summary.splitOn "Enchanted creature").length > 1
#guard galadhrimGuide.triggeredAbilities == #[.onEnterScry 2]
#guard (galadhrimGuide.summary.splitOn "scry 2").length > 1
#guard elvishVisionary.triggeredAbilities == #[.onEnterDraw 1]
#guard (elvishVisionary.summary.splitOn "draw a card").length > 1
#guard elvishArchdruid.staticAbilities == #[.otherCreaturesGet #[.elf] 1 1]
#guard elvishArchdruid.activatedAbilities[0]?.bind (·.manaProduction?) ==
  some { spec := .sequence #[(ManaType.colored .green,
    ValueExpr.count (.inZones .battlefield (.all #[.hasSubtype (.literal .elf), .controlledBy .you])))] }
#guard elvishArchdruid.manaAbilities == #[.colored .green]
#guard (elvishArchdruid.summary.splitOn "Other Elf creatures").length > 1
#guard (elvishArchdruid.summary.splitOn "for each Elf").length > 1
#guard mirkwoodElk.hasSimpleKeyword .trample
#guard mirkwoodElk.triggeredAbilities == #[.onEnterOrAttackReturnElfGainLife]
#guard mirkwoodElk.power == some (.fixed 6)
#guard mirkwoodElk.toughness == some (.fixed 6)
#guard (mirkwoodElk.summary.splitOn "trample").length > 1
#guard (mirkwoodElk.summary.splitOn "Elf card").length > 1
#guard celebornTheWise.triggeredAbilities ==
  #[.onAttackWithElvesScry 1, .onScryPumpSelfForEachLookedAt]
#guard celebornTheWise.power == some (.fixed 3)
#guard celebornTheWise.toughness == some (.fixed 3)
#guard celebornTheWise.subtypes.any (· == "Elf")
#guard (celebornTheWise.summary.splitOn "one or more Elves").length > 1
#guard (celebornTheWise.summary.splitOn "looked at").length > 1
#guard lothlorienLookout.triggeredAbilities == #[.onAttackScry 1]
#guard (lothlorienLookout.summary.splitOn "scry 1").length > 1
#guard lothlorienLookout.power == some (.fixed 1)
#guard lothlorienLookout.toughness == some (.fixed 3)
#guard galadhrimGuide.power == some (.fixed 3)
#guard galadhrimGuide.toughness == some (.fixed 4)
#guard goblinCratermaker.activatedAbilities.size == 1
#guard goblinCratermaker.activatedAbilities[0]!.cost.sacrificeSource
#guard goblinCratermaker.activatedAbilities[0]!.cost.mana == (ManaCost.ofGeneric 1)
#guard goblinCratermaker.activatedAbilities[0]!.isModal
#guard goblinCratermaker.activatedAbilities[0]!.allModes ==
  #[Effect.dealDamageToTargetCreature 2, Effect.destroyTargetColorlessNonland]
#guard (goblinCratermaker.summary.splitOn "Choose one").length > 1
#guard (goblinCratermaker.summary.splitOn "colorless nonland").length > 1
#guard smiteTheDeathless.isInstant
#guard smiteTheDeathless.requiresTarget
#guard smiteTheDeathless.spellEffect == some (Effect.dealDamageLoseIndestructibleExile 3)
#guard (Effect.dealDamageLoseIndestructibleExile 3).targetCount == 1
#guard (smiteTheDeathless.summary.splitOn "loses indestructible").length > 1
#guard (smiteTheDeathless.summary.splitOn "exile it instead").length > 1
#guard ologHaiCrusher.hasSimpleKeyword .trample
#guard ologHaiCrusher.staticAbilities == #[.cantBlockUnlessYouControl #[.goblin, .orc]]
#guard (ologHaiCrusher.summary.splitOn "trample").length > 1
#guard (ologHaiCrusher.summary.splitOn "can't block unless").length > 1
#guard oliphaunt.hasSimpleKeyword .trample
#guard oliphaunt.triggeredAbilities == #[.onAttackOtherGets2AndTrample]
#guard oliphaunt.allActivatedAbilities.size == 1
#guard oliphaunt.allActivatedAbilities[0]!.isFromHand
#guard oliphaunt.allActivatedAbilities[0]!.cost.discardSource
#guard oliphaunt.allActivatedAbilities[0]!.effect == Effect.searchLandTypeToHand "Mountain"
#guard oliphaunt.allActivatedAbilities[0]!.cost.mana == (ManaCost.ofGeneric 1)
#guard oliphaunt.power == some (.fixed 6)
#guard oliphaunt.toughness == some (.fixed 4)
#guard (oliphaunt.summary.splitOn "trample").length > 1
#guard (oliphaunt.summary.splitOn "+2/+0").length > 1
#guard (oliphaunt.summary.splitOn "Mountaincycling").length > 1
#guard goblinFireleaper.activatedAbilities.size == 1
#guard goblinFireleaper.activatedAbilities[0]!.effect == Effect.sourceGets 1 0
#guard goblinFireleaper.activatedAbilities[0]!.cost.mana == (ManaCost.ofGenericAndColor 1 .red)
#guard goblinFireleaper.triggeredAbilities == #[.onDiesDealDamageEqualToPowerToOppCreature]
#guard (goblinFireleaper.summary.splitOn "+1/+0").length > 1
#guard (goblinFireleaper.summary.splitOn "dies").length > 1
#guard infernoTitan.activatedAbilities.size == 1
#guard infernoTitan.activatedAbilities[0]!.effect == Effect.sourceGets 1 0
#guard infernoTitan.activatedAbilities[0]!.cost.mana == (ManaCost.ofColor .red)
#guard infernoTitan.triggeredAbilities == #[.onEnterOrAttackDealDividedDamage 3 3]
#guard infernoTitan.power == some (.fixed 6)
#guard infernoTitan.toughness == some (.fixed 6)
#guard (infernoTitan.summary.splitOn "+1/+0").length > 1
#guard (infernoTitan.summary.splitOn "divided as you choose").length > 1
#guard guttersnipe.triggeredAbilities == #[.onCastInstantOrSorceryDealDamageToEachOpponent 2]
#guard guttersnipe.power == some (.fixed 2)
#guard guttersnipe.toughness == some (.fixed 2)
#guard (guttersnipe.summary.splitOn "instant or sorcery").length > 1
#guard hauntOfTheDeadMarshes.triggeredAbilities == #[.onEnterScry 1]
#guard hauntOfTheDeadMarshes.activatedAbilities.size == 1
#guard hauntOfTheDeadMarshes.activatedAbilities[0]!.isFromGraveyard
#guard hauntOfTheDeadMarshes.activatedAbilities[0]!.condition? == some ActivatedAbility.condControlsLegendaryCreature
#guard hauntOfTheDeadMarshes.activatedAbilities[0]!.effect == Effect.returnFromGraveyardTapped
#guard languish.spellEffect == some (Effect.allCreaturesGet (-4) (-4))
#guard !languish.requiresTarget
#guard shadowOfTheEnemy.spellEffect == some (Effect.exileGraveyardCreaturesGrantCast)
#guard shadowOfTheEnemy.requiresTarget
#guard trollOfKhazadDum.staticAbilities == #[.cantBeBlockedExceptBy 3]
#guard (trollOfKhazadDum.summary.splitOn "three or more").length > 1
#guard trollOfKhazadDum.allActivatedAbilities.size == 1
#guard trollOfKhazadDum.allActivatedAbilities[0]!.isFromHand
#guard trollOfKhazadDum.allActivatedAbilities[0]!.cost.discardSource
#guard trollOfKhazadDum.allActivatedAbilities[0]!.effect == Effect.searchLandTypeToHand "Swamp"
#guard trollOfKhazadDum.allActivatedAbilities[0]!.cost.mana == (ManaCost.ofGeneric 1)
#guard mercilessExecutioner.triggeredAbilities == #[.onEnterEachPlayerSacrificesCreature]
#guard bitterDownfall.spellEffect == some (Effect.destroyTargetCreatureControllerLosesLife 2)
#guard bitterDownfall.staticAbilities.contains (.costReductionIfTargetDamaged 3)
#guard improvisedClub.isInstant
#guard improvisedClub.spellEffect == some (Effect.dealDamage 4)
#guard improvisedClub.additionalCosts == #[AdditionalCostSpec.mandatory CostSpec.sacrificeArtifactOrCreature]
#guard improvisedClub.requiresTarget
#guard (improvisedClub.summary.splitOn "additional cost").length > 1
#guard (improvisedClub.summary.splitOn "4 damage").length > 1
#guard fireOfOrthanc.isSorcery
#guard fireOfOrthanc.spellEffect == some (Effect.destroyArtifactOrLandNonflyersCantBlock)
#guard fireOfOrthanc.requiresTarget
#guard (fireOfOrthanc.summary.splitOn "artifact or land").length > 1
#guard (fireOfOrthanc.summary.splitOn "can't block this turn").length > 1
#guard nightsWhisper.isSorcery
#guard nightsWhisper.spellEffect == some (Effect.drawAndLoseLife 2 2)
#guard !nightsWhisper.requiresTarget
#guard nightsWhisper.hasCastKind .draw
#guard (nightsWhisper.summary.splitOn "draw 2 cards").length > 1
#guard (nightsWhisper.summary.splitOn "lose 2 life").length > 1
#guard theOneRing.activatedAbilities[0]!.effect == Effect.burdenThenDraw
#guard theOneRing.triggeredAbilities ==
  #[.onEnterIfCastProtectionEverything, .onYourUpkeepLoseLifePerBurden]
#guard palantirOfOrthanc.triggeredAbilities == #[.onYourEndStepPalantir]
#guard grimaSarumanSFootman.staticAbilities.contains .cantBeBlocked
#guard grimaSarumanSFootman.triggeredAbilities == #[.onCombatDamageImpulseInstantSorcery]
#guard arwenMortalQueen.entersWithIndestructibleCounter
#guard arwenMortalQueen.activatedAbilities[0]!.effect == Effect.arwenShare
#guard callForthTheTempest.spellEffect == some (Effect.damageOppCreaturesEqualOtherSpellsMv)
#guard galadrielSDismissal.spellEffect == some (Effect.phaseOutKicker)
#guard theReaverCleaver.staticAbilities == #[.equippedGetsTrampleAndCombatTreasures 1 1]
#guard mountDoom.activatedAbilities.size == 3
#guard mountDoom.activatedAbilities[2]!.cost.sacrificeLegendaryArtifact
#guard lothoCorruptShirriff.triggeredAbilities ==
  #[.onPlayerCastsSecondSpellLoseLifeCreateTreasure]


end Mtg.Engine.Tests.CatalogHobbitGuards
