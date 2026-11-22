import Mtg.Engine.Card.CardDef
import Mtg.Engine.Card.ManaSpec
import Mtg.Engine.Card.Parser.SubGrammars

/-!
# Compile-time guards

Cross-abstraction `#guard` regression tests for Oracle wording and effect
wiring, kept together so each abstraction file stays focused.
-/

namespace Mtg.Engine

namespace CardDef

#guard toString Keyword.haste == "haste"
#guard toString Keyword.flash == "flash"
#guard toString Keyword.vigilance == "vigilance"
#guard toString Keyword.lifelink == "lifelink"
#guard toString Keyword.menace == "menace"
#guard CardDef.isKeywordRestatement #[Keyword.haste] "Haste"
#guard !CardDef.isKeywordRestatement #[] "({T}: Add {R}.)"
#guard CardDef.isKeywordRestatement #[Keyword.flash] "Flash"
#guard CardDef.isKeywordRestatement #[Keyword.vigilance] "Vigilance"
#guard CardDef.isKeywordRestatement #[Keyword.reach, Keyword.deathtouch]
  "Reach, deathtouch"
#guard !CardDef.isKeywordRestatement #[Keyword.flying] "Flash"
#guard toString Keyword.hexproof == "hexproof"
#guard CardDef.isKeywordRestatement #[Keyword.hexproof] "Hexproof"
#guard toString Keyword.indestructible == "indestructible"
#guard CardDef.isKeywordRestatement #[Keyword.indestructible] "Indestructible"
#guard CardDef.isAdventureDelimiter "//ADV//"
#guard CardDef.isAdventureDelimiter "//ADV// Spew Flame {4}{R}"
#guard !CardDef.isAdventureDelimiter "Spew Flame {4}{R}"
#guard CardDef.stripAdventureDelimiter "//ADV//" == none
#guard CardDef.stripAdventureDelimiter "//ADV// Spew Flame {4}{R}" ==
  some "Spew Flame {4}{R}"
#guard (Effect.dealDamage 3).targetSpec == .anyTarget
#guard (Effect.dealDamage 3).body == Instruction.dealDamageFixed (.targetSlot 0) 3
#guard (Effect.dealDamage 3).phrase == "deals 3 damage to any target"
#guard (Effect.draw 2).body == Instruction.drawFixed 2
#guard (Effect.scry 1).body == Instruction.scryFixed 1
#guard (Effect.gainLife 3).body == Instruction.gainLifeFixed 3
#guard (Effect.drawLoseLifeThenAmass 2).body ==
  .seq #[Instruction.drawFixed 1, Instruction.loseLifeFixed 1, Instruction.amassFixed 2 .goblin]
#guard (Effect.createTokensThenTeamPump .villain21menace 1 1 0).body ==
  .seq #[Instruction.createTokensFixed .villain21menace 1,
    Instruction.pumpFixed (.inZones .battlefield (.all #[.hasType .creature, .controlledBy .you])) 1 0]
#guard (Effect.createTokens .treasure 1).body == Instruction.createTokensFixed .treasure 1
#guard (Effect.targetPlayerCreatesTokens .leviathan65hexproof 1).body ==
  Instruction.createTokensFixed .leviathan65hexproof 1 (.target 0)
#guard (Effect.destroyArtifactOrEnchantmentGainLife 2).body ==
  .seq #[Instruction.destroy (.target 0), Instruction.gainLifeFixed 2]
#guard (Effect.tapScryDraw 1 1).body ==
  .seq #[Instruction.tap (.target 0), Instruction.scryFixed 1, Instruction.drawFixed 1]
#guard (Effect.tapScryDraw 1 1).phrase ==
  "tap target creature. Scry 1. Draw a card"
#guard (Effect.counterUnlessPays 4).body ==
  .unlessPays (.controllerOf (.target 0)) (CostSpec.ofGeneric 4) (Instruction.counter (.target 0))
#guard (Effect.counterUnlessPays 4).phrase ==
  "counter target spell unless its controller pays {4}"
#guard Effect.putOnTopOrBottom.body ==
  .moveZone (.target 0) (.library .owner .top true) .put {}
#guard Effect.putOnTopOrBottom.phrase ==
  "target creature's owner puts it on their choice of the top or bottom of their library"
#guard (Effect.untapPumpMaybeAttach 2 2).body ==
  .seq #[
    Instruction.untap (.target 0),
    Instruction.pumpFixed (.target 0) 2 2,
    Instruction.ifThen (.exists (.filter (.target 0) (.hasSubtype (.literal .dwarf))))
      (Instruction.may .you none
        (.permanent (.attach
          (.inZones .battlefield (.all #[.hasSubtype (.literal .equipment), .controlledBy .you]))
          (.target 0) true)))
  ]
#guard (Effect.untapPumpMaybeAttach 2 2).phrase ==
  "untap target creature you control. It gets +2/+2 until end of turn. If it's a Dwarf, you may attach an Equipment you control to it"
#guard Effect.destroyCreatureSurveil.body ==
  .seq #[Instruction.destroy (.target 0), Instruction.surveilFixed 1]
#guard (Effect.pumpThenDraw (-4) 0).body ==
  .seq #[Instruction.pumpFixed (.target 0) (-4) 0, Instruction.drawFixed 1]
#guard Effect.plusOneLifelinkIndestructible.body ==
  .seq #[Instruction.putPlusOne (.target 0) 1,
    Instruction.grantKeywords (.target 0) #[Keyword.lifelink, Keyword.indestructible]]
#guard Effect.grantVigilanceUnblockable.body ==
  .seq #[
    Instruction.grantKeywords (.target 0) #[Keyword.vigilance],
    Instruction.cantBeBlocked (.target 0),
    Instruction.drawFixed 1
  ]
#guard (Effect.creaturesYouControlGetAndGrant 1 1 #[Keyword.vigilance]).body ==
  .seq #[
    Instruction.pumpFixed (.inZones .battlefield (.all #[.hasType .creature, .controlledBy .you])) 1 1,
    Instruction.grantKeywords (.inZones .battlefield (.all #[.hasType .creature, .controlledBy .you])) #[Keyword.vigilance]
  ]
#guard Effect.sourceGainsIndestructibleTap.body ==
  .seq #[Instruction.grantKeywords .this #[Keyword.indestructible], Instruction.tap .this]
#guard Effect.sourceGainsIndestructibleTap.phrase ==
  "Witch-king of Angmar gains indestructible until end of turn. Tap him"
#guard (Effect.drawThenDiscard 2).body ==
  .seq #[Instruction.drawFixed 2, Instruction.discardFixed 1]
#guard (Effect.abilityDrawThenDiscard 2).body ==
  .seq #[Instruction.drawFixed 2, Instruction.discardFixed 1]
#guard (Effect.ownerShuffleSourceDraw 3).body ==
  .bind ⟨0⟩
    (.moveZone .this (.library .owner .bottom false) .shuffleIntoLibrary { shuffleAfter := true })
    (Instruction.ifThen (.stepSucceeded ⟨0⟩) (Instruction.drawFixed 3 (.ownerOf .this)))
#guard (Effect.ownerShuffleSourceDraw 3).phrase ==
  "This owner shuffles him into their library and draws 3 cards"
#guard (Effect.plusOneAndDraw 1 2).body ==
  .seq #[Instruction.putPlusOne .this 1, Instruction.drawFixed 2]
#guard (Effect.plusOneAndDraw 1 2).phrase ==
  "Put a +1/+1 counter on this and draw 2 cards"
#guard Effect.destroyUpToOneThenPlusOne.body ==
  .seq #[Instruction.destroy (.target 0), Instruction.putPlusOne .this 1]
#guard Effect.destroyUpToOneThenPlusOne.phrase ==
  "Destroy up to one target artifact or enchantment. Put a +1/+1 counter on this"
#guard (Effect.plusOneAndCreateTokens 2 .robotVillain22).body ==
  .seq #[Instruction.putPlusOne .this 2, Instruction.createTokensFixed .robotVillain22 1]
#guard (Effect.plusOneAndCreateTokens 2 .robotVillain22).phrase ==
  "Put 2 +1/+1 counters on this creature and create a 2/2 colorless Robot Villain artifact creature token"
#guard (Effect.plusOneAndGrant #[Keyword.vigilance, Keyword.indestructible, Keyword.haste]).body ==
  .seq #[
    Instruction.putPlusOne .this 1,
    Instruction.grantKeywords .this #[Keyword.vigilance, Keyword.indestructible, Keyword.haste]
  ]
#guard (Effect.plusOneAndGrant #[Keyword.vigilance, Keyword.indestructible, Keyword.haste]).phrase ==
  "Put a +1/+1 counter on this. He gains vigilance, indestructible, and haste until end of turn"
#guard (Effect.creaturesYouControlGetOppsLoseLife 1 0 1).body ==
  .seq #[
    Instruction.pumpFixed (.inZones .battlefield (.all #[.hasType .creature, .controlledBy .you])) 1 0,
    Instruction.loseLifeFixed 1 .opponents
  ]
#guard (Effect.creaturesYouControlGetOppsLoseLife 1 0 1).phrase ==
  "Creatures you control get +1/+0 until end of turn. Each opponent loses 1 life"
#guard (Effect.subtypesGainMenace #["Goblin", "Orc"]).phrase ==
  "Goblins and Orcs you control gain menace until end of turn"
#guard (Effect.subtypesGainMenace #["Elf"]).phrase ==
  "Elves you control gain menace until end of turn"
#guard (Effect.counterThenRecruitIfMvAtMost 2).body ==
  .seq #[
    Instruction.counter (.target 0),
    Instruction.ifThen (.cmp .le (.objectStat .manaValue (.target 0)) (.const 2)) (Instruction.recruit .you)
  ]
#guard (Effect.counterThenRecruitIfMvAtMost 2).phrase ==
  "counter target spell. If that spell's mana value was 2 or less, recruit"
#guard (Effect.counterThenRecruitIfMvAtMost 2).castKind == .counter
#guard (Effect.ofTrigger (.scry 2)).resolution == .scry (.fixed 2)
#guard (Effect.ofTrigger (.scry 2)).sharedTrigger == some (.scry 2)
#guard Effect.chapterRecruit.body == Instruction.recruit .you
#guard (Effect.chapterDraw 2).body == Instruction.drawFixed 2
#guard (Effect.enterDealDamageUpToOne 4).allowsZeroTargets
#guard Effect.watchHulk.resolution ==
  .sequence [
    .putCounters (.ofKind .plusOnePlusOne) .source,
    .«if» (.atLeast (.count (.intersection [.source, .attackingCreatures])) (.fixed 1)) (.untap .source),
    .«if» .enrageGrantsCombat .additionalCombatPhase]
#guard Effect.watchHulk.sharedTrigger == some (.watch .hulk)
#guard (TriggeredAbility.onEnterScry 2).effect.resolution == .scry (.fixed 2)
#guard (Effect.dealDamage 3).phrase == "deals 3 damage to any target"
#guard (Effect.pump 3 3).phrase == "target creature gets +3/+3 until end of turn"
#guard Effect.destroyCreatureWithFlying.phrase ==
  "destroy target creature with flying"
#guard Effect.destroyCreature.phrase ==
  "destroy target creature"
#guard Effect.plusOnePlusOneTrampleHexproof.phrase ==
  "put a +1/+1 counter on target creature you control. It gains trample and hexproof until end of turn"
#guard (Effect.dealDamageToCreature 5).phrase ==
  "deals 5 damage to target creature"
#guard (Effect.dealDamageLoseIndestructibleExile 3).phrase ==
  "deals 3 damage to target creature. That creature loses indestructible until end of turn. If that creature would die this turn, exile it instead"
#guard (Effect.dealDamageLoseIndestructibleExile 3).body ==
  .seq #[
    Instruction.dealDamageFixed (.targetSlot 0) 3,
    Instruction.loseKeywords (.target 0) #[Keyword.indestructible],
    Instruction.exileIfDiesThisTurn (.target 0)
  ]
#guard Effect.creatureYouControlDealsPowerToOppCreature.phrase ==
  "target creature you control deals damage equal to its power to target creature an opponent controls"
#guard Effect.playAdditionalLandThisTurn.phrase ==
  "you may play an additional land this turn"
#guard Effect.destroyArtifactOrLandNonflyersCantBlock.phrase ==
  "destroy target artifact or land. Creatures without flying can't block this turn"
#guard (Effect.destroyTargetCreatureControllerLosesLife 2).phrase ==
  "destroy target creature. Its controller loses 2 life"
#guard (Effect.allCreaturesGet (-4) (-4)).phrase ==
  "all creatures get -4/-4 until end of turn"
#guard (Effect.drawAndLoseLife 2 2).phrase ==
  "you draw 2 cards and lose 2 life"
#guard (Effect.drawAndLoseLife 1 0).phrase ==
  "you draw a card and lose 0 life"
#guard (Effect.targetPlayerDrawLoseLife 2 2).phrase ==
  "target player draws 2 cards and loses 2 life"
#guard (Effect.creaturesTargetPlayerGet (-1) (-1)).phrase ==
  "creatures target player controls get -1/-1 until end of turn"
#guard (Effect.pumpAndLifelink 2 2).phrase ==
  "target creature gets +2/+2 and gains lifelink until end of turn"
#guard (Effect.pumpAndExileIfDies (-5) (-5)).phrase ==
  "target creature gets -5/-5 until end of turn. If that creature would die this turn, exile it instead"
#guard (Effect.pumpAndExileIfDies (-5) (-5)).body ==
  .seq #[Instruction.pumpFixed (.target 0) (-5) (-5), Instruction.exileIfDiesThisTurn (.target 0)]
#guard (Effect.exileGraveyardCreaturesGrantCast.phrase).startsWith
  "exile all creature cards"
#guard TargetSpec.noun .anyTarget == "any target"
#guard TargetSpec.noun .creatureWithFlying == "target creature with flying"
#guard TargetSpec.noun .opponent == "target opponent"
#guard TargetSpec.noun .colorlessNonland ==
  "target colorless nonland permanent"
#guard TargetSpec.noun .player == "target player"
#guard TargetSpec.noun .opponent == "target opponent"
#guard TargetSpec.noun .oppGraveyardCard ==
  "target card from an opponent's graveyard"
#guard TargetSpec.none.isEmpty && TargetSpec.none.targetCount == 0 && TargetSpec.none.noun == "" &&
  TargetSpec.none.defaultPreference == .own
#guard TargetSpec.anyTarget.targetCount == 1 && TargetSpec.anyTarget.noun == "any target" &&
  TargetSpec.anyTarget.defaultPreference == .opponentPlayer
#guard TargetSpec.opponent.targetCount == 1 && TargetSpec.opponent.noun == "target opponent" &&
  TargetSpec.opponent.defaultPreference == .opponentPlayer
#guard TargetSpec.creatureYouControlThenOppCreature.targetCount == 2 &&
  TargetSpec.creatureYouControlThenOppCreature.noun ==
    "target creature you control and target creature an opponent controls" &&
  TargetSpec.creatureYouControlThenOppCreature.defaultPreference == .ownThenOpponent
#guard (TargetSpec.creatureYouControlThenOppCreature.slotAtPos 0).domain ==
  TargetDomain.creatureYouControl
#guard (TargetSpec.creatureYouControlThenOppCreature.slotAtPos 1).domain ==
  TargetDomain.oppCreature
#guard (TargetSpec.creature.slotAtPos 0).domain == TargetDomain.creature
#guard TargetSpec.upToOneCreatureThenPlayer.targetCount == 2 &&
  TargetSpec.upToOneCreatureThenPlayer.noun ==
    "up to one target creature and target player" &&
  TargetSpec.upToOneCreatureThenPlayer.defaultPreference == .own
#guard (TargetSpec.upToOneCreatureThenPlayer.slotAtPos 0).domain == TargetDomain.creature
#guard (TargetSpec.upToOneCreatureThenPlayer.slotAtPos 1).domain == TargetDomain.anyPlayer
#guard TargetSpec.isOptionalSlot .upToOneCreatureThenPlayer 0
#guard !TargetSpec.isOptionalSlot .upToOneCreatureThenPlayer 1
#guard TargetSpec.announcedSlotNoun .upToOneCreatureThenPlayer 0 ==
  "up to one target creature"
#guard TargetSpec.announcedSlotNoun .upToOneCreatureThenPlayer 1 ==
  "target player"
#guard TargetSpec.noun (.upToTwoCreaturesTotalMvAtMost 6) ==
  "up to two target creatures with total mana value 6 or less"
#guard (TargetSpec.upToTwoCreaturesTotalMvAtMost 6).targetCount == 2 &&
  (TargetSpec.upToTwoCreaturesTotalMvAtMost 6).totalMvCap? == some 6
#guard (Effect.chapterGainControlOfUpToTwoCreaturesTotalMvAtMost 6).allowsZeroTargets
#guard (Effect.chapterDealDamageToEachNonSubtypeAndOpponents 2 "Villain").phrase ==
  "This Saga deals 2 damage to each non-Villain creature and each opponent"
#guard Effect.chapterDealXDamageToTargetOpponentGreatestArtifactMv.targetSpec ==
  .opponent
#guard TriggerPattern.thisEnters.renderClause { selfRef := "this permanent", capitalize := false } ==
  "this permanent enters"
#guard TriggerPattern.thisEnters.defaultWord == .when
#guard TriggerPattern.thisEnters.label == "enters trigger"
#guard TriggerPattern.thisAttacks.renderClause { selfRef := "this creature", capitalize := false } ==
  "this creature attacks"
#guard TriggerPattern.thisAttacks.defaultWord == .whenever
#guard TriggerPattern.thisAttacks.label == "attack trigger"
#guard TriggerPattern.youScry.renderClause { selfRef := "this permanent", capitalize := false } == "you scry"
#guard TriggerPattern.thisDies.label == "dies trigger"
#guard TriggerPattern.youScry.label == "scry trigger"
#guard TriggerPattern.landYouControlEnters.label == "landfall trigger"
#guard TriggerPattern.thisBecomesBlocked.label == "becomes-blocked trigger"
#guard TriggerPattern.youCastInstantOrSorcery.label == "cast trigger"
#guard (TriggerPattern.anotherSubtypeYouControlEnters .elf).label == "Elf-enters trigger"
#guard (TriggerPattern.youAttackWithSubtype .elf).label == "attack trigger"
#guard TriggerPattern.thisDies.defaultWord == .when
#guard (TriggerPattern.youAttackWithSubtype .elf).defaultWord == .whenever
#guard (Effect.dealDamage 3).targetCount == 1
#guard Effect.tapOneOrTwoCreatures.targetCount == 1
#guard Effect.tapOneOrTwoCreatures.maxTargetCount == 2
#guard Effect.creatureYouControlDealsPowerToOppCreature.targetCount == 2
#guard Effect.playAdditionalLandThisTurn.targetCount == 0
#guard Effect.destroyArtifactOrLandNonflyersCantBlock.targetCount == 1
#guard Effect.destroyCreature.targetCount == 1
#guard (Effect.drawAndLoseLife 2 2).targetCount == 0
#guard (Effect.dealDamage 3).targetSpec == .anyTarget
#guard (Effect.pump 3 3).targetSpec == .creature
#guard (Effect.pump 3 3).targeting == EffectTargeting.of .creature .own
#guard TargetSpec.defaultPreference .anyTarget == .opponentPlayer
#guard TargetSpec.defaultPreference .opponent == .opponentPlayer
#guard TargetSpec.defaultPreference .creatureYouControl == .own
#guard TargetSpec.defaultPreference .creature == .opponent
#guard TargetSpec.targetsStackSpell .spell
#guard TargetSpec.targetsStackSpell .creatureSpell
#guard TargetSpec.targetsStackSpell (.creatureSpellPTAtMost 2)
#guard !TargetSpec.targetsStackSpell .creature
#guard Effect.destroyCreatureWithFlying.targetSpec == .creatureWithFlying
#guard Effect.destroyCreature.targetSpec == .creature
#guard Effect.plusOnePlusOneTrampleHexproof.targetSpec == .creatureYouControl
#guard (Effect.dealDamageToCreature 5).targetSpec == .creature
#guard (Effect.dealDamageLoseIndestructibleExile 3).targetSpec == .creature
#guard Effect.creatureYouControlDealsPowerToOppCreature.targetSpec ==
  .creatureYouControlThenOppCreature
#guard (Effect.plusOneUpToOneAndPlayerGainsLife 2).targetSpec ==
  .upToOneCreatureThenPlayer
#guard (Effect.plusOneUpToOneAndPlayerGainsLife 2).targetCount == 2
#guard !(Effect.plusOneUpToOneAndPlayerGainsLife 2).allowsZeroTargets
#guard (Effect.plusOneUpToOneAndPlayerGainsLife 2).body ==
  .seq #[Instruction.putPlusOne (.target 0) 1, Instruction.gainLifeFixed 2 (.target 1)]
#guard (Effect.plusOneUpToOneAndPlayerGainsLife 2).phrase ==
  "put a +1/+1 counter on up to one target creature. Target player gains 2 life"
#guard Effect.fight.body == .damage (.fight (.target 0) (.target 1) false)
#guard (Effect.plusOneThenFight 2).body ==
  .seq #[Instruction.putPlusOne (.target 0) 2, .damage (.fight (.target 0) (.target 1) false)]
#guard (Effect.plusOneThenFight 2).phrase ==
  "put 2 +1/+1 counters on target creature you control. Then it fights target creature an opponent controls"
#guard Effect.plusOneThenEachOtherIfFromGy.phrase ==
  "put a +1/+1 counter on target creature you control. If this spell was cast from a graveyard, also put a +1/+1 counter on each other creature you control"
#guard (Effect.drawIfFromGy 1 2).body ==
  .ifCond (.castPred (.castFrom .graveyard .this)) (Instruction.drawFixed 2) (Instruction.drawFixed 1)
#guard (Effect.drawIfFromGy 1 2).phrase ==
  "draw a card. If this spell was cast from a graveyard, draw 2 cards instead"
#guard (Effect.amassGoblinsOrFromGy 1 3).body ==
  .ifCond (.castPred (.castFrom .graveyard .this)) (Instruction.amassFixed 3 .goblin) (Instruction.amassFixed 1 .goblin)
#guard (Effect.amassGoblinsOrFromGy 1 3).phrase ==
  "amass Goblins 1. If this spell was cast from a graveyard, amass Goblins 3 instead"
#guard Effect.returnSpellDraw.body ==
  .seq #[Instruction.bounce (.target 0), Instruction.drawFixed 1]
#guard Effect.returnSpellDraw.phrase ==
  "return target spell to its owner's hand. Draw a card"
#guard (Effect.returnCreatureFromGyThenAmass 3).body ==
  .seq #[.moveZone (.target 0) (.hand .controller) .returnToHand {}, Instruction.amassFixed 3 .goblin]
#guard (Effect.returnCreatureFromGyThenAmass 3).phrase ==
  "return up to one target creature card from your graveyard to your hand. Amass Goblins 3"
#guard Effect.destroyArtifactOrLandNonflyersCantBlock.targetSpec == .artifactOrLand
#guard Effect.playAdditionalLandThisTurn.targetSpec == .none
#guard (Effect.destroyTargetCreatureControllerLosesLife 2).targetSpec == .creature
#guard (Effect.allCreaturesGet (-4) (-4)).targetSpec == .none
#guard (Effect.drawAndLoseLife 2 2).targetSpec == .none
#guard (Effect.targetPlayerDrawLoseLife 2 2).targetSpec == .player
#guard (Effect.creaturesTargetPlayerGet (-1) (-1)).targetSpec == .player
#guard Effect.exileGraveyardCreaturesGrantCast.targetSpec == .player
#guard !(Effect.allCreaturesGet (-4) (-4)).requiresTarget
#guard !(Effect.drawAndLoseLife 2 2).requiresTarget
#guard (Effect.destroyTargetCreatureControllerLosesLife 2).requiresTarget
#guard (Effect.targetPlayerDrawLoseLife 2 2).requiresTarget
#guard (Effect.allCreaturesGet (-4) (-4)).castKind == .massPump
#guard (Effect.drawAndLoseLife 2 2).castKind == .draw
#guard (Effect.targetPlayerDrawLoseLife 2 2).castKind == .draw
#guard (Effect.pumpAndExileIfDies (-5) (-5)).preferAsDefaultMode
#guard (Effect.dealDamage 3).requiresTarget
#guard (Effect.dealDamageToCreature 5).requiresTarget
#guard Effect.destroyCreature.requiresTarget
#guard Effect.destroyArtifactOrLandNonflyersCantBlock.requiresTarget
#guard (Effect.dealDamageLoseIndestructibleExile 3).requiresTarget
#guard (Effect.dealDamageLoseIndestructibleExile 3).targetCount == 1
#guard Effect.creatureYouControlDealsPowerToOppCreature.requiresTarget
#guard !Effect.playAdditionalLandThisTurn.requiresTarget
#guard !(Effect.drawAndLoseLife 2 2).requiresTarget
#guard (Effect.dealDamage 3).castKind == .burn
#guard (Effect.dealDamageToCreature 5).castKind == .creatureDamage
#guard (Effect.dealDamageLoseIndestructibleExile 3).castKind == .creatureDamage
#guard Effect.creatureYouControlDealsPowerToOppCreature.castKind == .fight
#guard Effect.destroyCreatureWithFlying.castKind == .destroyFlying
#guard Effect.destroyCreature.castKind == .destroyCreature
#guard Effect.destroyArtifactOrLandNonflyersCantBlock.castKind ==
  .destroyArtifactOrLand
#guard (Effect.pump 3 3).castKind == .pump
#guard Effect.plusOnePlusOneTrampleHexproof.castKind == .pump
#guard Effect.playAdditionalLandThisTurn.castKind == .extraLand
#guard (Effect.drawAndLoseLife 2 2).castKind == .draw
#guard Effect.destroyCreatureWithFlying.preferAsDefaultMode
#guard !Effect.destroyCreature.preferAsDefaultMode
#guard !(Effect.pump 3 3).preferAsDefaultMode
#guard !Effect.plusOnePlusOneTrampleHexproof.preferAsDefaultMode
#guard (Effect.pump 3 3).body == Instruction.pumpFixed (.target 0) 3 3
#guard Effect.destroyCreatureWithFlying.body == Instruction.destroy (.target 0)
#guard Effect.destroyCreature.body == Instruction.destroy (.target 0)
#guard Effect.playAdditionalLandThisTurn.body == Instruction.extraLand
#guard (Effect.drawAndLoseLife 2 2).body ==
  .seq #[Instruction.drawFixed 2, Instruction.loseLifeFixed 2]
#guard (Effect.targetPlayerDraw 2).body == Instruction.drawFixed 2 (.target 0)
#guard (Effect.targetPlayerDrawLoseLife 2 2).body ==
  .seq #[Instruction.drawFixed 2 (.target 0), Instruction.loseLifeFixed 2 (.target 0)]
#guard (Effect.destroyTargetCreatureControllerLosesLife 2).body ==
  .seq #[Instruction.destroy (.target 0), Instruction.loseLifeFixed 2 (.controllerOf (.target 0))]
#guard (Effect.eachOpponentLosesLife 2).body == Instruction.loseLifeFixed 2 .opponents
#guard (Effect.millThenPutInstantOrSorcery 4).phrase ==
  "mill 4 cards, then put an instant or sorcery card from among them into your hand"
#guard (Effect.millThenPutLands 4 2).phrase ==
  "mill 4 cards, then put up to two land cards from among them into your hand"
#guard (Effect.millThenPutAllInstantsOrSorceries 6).phrase ==
  "mill 6 cards, then put all instant and sorcery cards from among them into your hand"
#guard Effect.doublePowerAndToughness.body == Instruction.doublePT (.target 0)
#guard (Effect.exileCreatureToughnessAtLeast 4).body == Instruction.exile (.target 0)
#guard (Effect.dealDamageToCreature 5).body == Instruction.dealDamageFixed (.targetSlot 0) 5
#guard (Effect.dealDamageToCreatureExileIfDies 3).body ==
  .seq #[Instruction.exileIfDiesThisTurn (.target 0), Instruction.dealDamageFixed (.targetSlot 0) 3]
#guard (Effect.dealDamageToCreatureExileIfDies 3).phrase ==
  "deals 3 damage to target creature. If that creature would die this turn, exile it instead"
#guard
  let c : CardDef := {
    name := "Silent Club"
    types := #[.instant]
    spellEffect := some (Effect.dealDamage 4)
    additionalCosts := #[AdditionalCostSpec.mandatory CostSpec.sacrificeArtifactOrCreature]
  }
  (c.abilitiesText.splitOn "sacrifice an artifact or creature").length > 1 &&
    (c.abilitiesText.splitOn "deals 4 damage").length > 1
#guard (Effect.searchBasicLandTapped.phrase).startsWith "Search your library"
#guard (Effect.searchLandTypeToHand "Mountain").phrase ==
  "Search your library for a Mountain card, reveal it, put it into your hand, then shuffle"
#guard (Effect.searchLandTypeToHand "Swamp").phrase ==
  "Search your library for a Swamp card, reveal it, put it into your hand, then shuffle"
#guard !(Effect.searchLandTypeToHand "Mountain").requiresTarget
#guard Effect.addAnyColorSpendOnlyHero.phrase ==
  "Add one mana of any color. Spend this mana only to cast a Hero spell or to activate an ability of a Hero source"
#guard Effect.addAnyColorSpendOnlyVillain.phrase ==
  "Add one mana of any color. Spend this mana only to cast a Villain spell or to activate an ability of a Villain source"
#guard Effect.addAnyColorSpendOnlyArtifactSpell.phrase ==
  "Add one mana of any color. Spend this mana only to cast an artifact spell"
#guard (Effect.dealDamageToTargetCreature 2).phrase ==
  "This creature deals 2 damage to target creature"
#guard Effect.destroyTargetColorlessNonland.phrase ==
  "Destroy target colorless nonland permanent"
#guard Effect.attachToTargetCreatureYouControl.phrase ==
  "Attach this Equipment to target creature you control"
#guard (Effect.becomeBearCreatureWithLandsPT.phrase).startsWith
  "This enchantment becomes a Bear creature"
#guard (Effect.sourceGets 1 0).phrase ==
  "This creature gets +1/+0 until end of turn"
#guard (Effect.putPlusOnePlusOneOnSource 3).phrase ==
  "Put 3 +1/+1 counters on this creature"
#guard (Effect.putPlusOnePlusOneOnSource 1).phrase ==
  "Put a +1/+1 counter on this creature"
#guard Effect.targetCantBeBlockedThisTurn.phrase ==
  "Target creature can't be blocked this turn"
#guard Effect.returnFromGraveyardTapped.phrase ==
  "Return this card from your graveyard to the battlefield tapped"
#guard Effect.returnFromGraveyardToHand.phrase ==
  "Return this card from your graveyard to your hand"
#guard !Effect.returnFromGraveyardTapped.requiresTarget
#guard !Effect.returnFromGraveyardToHand.requiresTarget
#guard (Effect.dealDamageToTargetCreature 2).requiresTarget
#guard Effect.destroyTargetColorlessNonland.requiresTarget
#guard Effect.attachToTargetCreatureYouControl.requiresTarget
#guard Effect.targetCantBeBlockedThisTurn.requiresTarget
#guard (Effect.dealDamageToTargetCreature 2).targetSpec == .creature
#guard Effect.destroyTargetColorlessNonland.targetSpec == .colorlessNonland
#guard Effect.attachToTargetCreatureYouControl.targetSpec == .creatureYouControl
#guard Effect.targetCantBeBlockedThisTurn.targeting ==
  EffectTargeting.of .creature .own
#guard Effect.searchBasicLandTapped.targetSpec == .none
#guard (Effect.dealDamageToTargetCreature 2).targetCount == 1
#guard Effect.searchBasicLandTapped.targetCount == 0
#guard (Effect.dealDamageToTargetCreature 2).abilityKind == .creatureDamage
#guard Effect.destroyTargetColorlessNonland.abilityKind == .destroyColorless
#guard (Effect.sourceGets 1 0).abilityKind == .other
#guard (Effect.dealDamageToTargetCreature 2).body ==
  Instruction.dealDamageFixed (.targetSlot 0) 2
#guard Effect.destroyTargetColorlessNonland.body ==
  Instruction.destroy (.target 0)
#guard Effect.destroyTargetPermanent == Effect.destroyTarget .permanent (capitalize := true)
#guard Effect.destroyTargetArtifactOrEnchantment ==
  Effect.destroyTarget .artifactOrEnchantment (capitalize := true)
#guard Effect.destroyTargetNoncreatureArtOrEnch ==
  Effect.destroyTarget .noncreatureArtifactOrEnchantment (capitalize := true)
#guard Effect.destroyTargetNoncreatureArtOrEnch.phrase ==
  "Destroy target noncreature artifact or noncreature enchantment"
#guard Effect.destroyCreature.castKind == .destroyCreature
#guard Effect.destroyTargetArtifact.castKind == .destroyArtifactOrLand
#guard Effect.destroyTargetPermanent.body ==
  Effect.destroyTargetColorlessNonland.body
#guard Effect.destroyTargetPermanent.abilityKind ==
  Effect.destroyTargetColorlessNonland.abilityKind
#guard Effect.targetCantBeBlockedThisTurn.body ==
  Instruction.cantBeBlocked (.target 0)
#guard (Effect.sourceGets 1 0).body == Instruction.pumpFixed .this 1 0
#guard (Effect.putPlusOnePlusOneOnSource 3).body == Instruction.putPlusOne .this 3
#guard (Effect.becomeSubtypeWithLandsPT "Elf").phrase ==
  "This enchantment becomes an Elf creature in addition to its other types and gains \"This creature's power and toughness are each equal to the number of lands you control.\""
#guard (Effect.searchBasicBeholdSubtypeUntap "Orc").phrase.endsWith
  "You may behold an Orc. If you do, untap that land"
#guard Effect.addAnyColorSpendOnlyHero.manaProduction? ==
  some { spec := .oneOf .anyColor (.const 1), restriction := some (.subtypeSpellOrSource .hero) }
#guard Effect.addAnyColorSpendOnlyVillain.manaProduction? ==
  some { spec := .oneOf .anyColor (.const 1), restriction := some (.subtypeSpellOrSource .villain) }
#guard (Effect.teamGain #[Keyword.doubleStrike]).phrase ==
  "Creatures you control gain double strike until end of turn"
#guard (Effect.becomeTypes #["Dinosaur", "Hero"] 3 5
    #[Keyword.reach, Keyword.vigilance]).phrase ==
  "Until end of turn, this becomes a Dinosaur Hero with base power and toughness 3/5 and gains reach and vigilance"
#guard (Effect.millThenPutSubtypeOrEnchantment 4 "Hero").phrase ==
  "Mill 4 cards. You may put a Hero or enchantment card from among those cards into your hand"
#guard (Effect.lookAtTopPutTypes 7 #["Hero", "Equipment", "Vehicle"]).phrase.startsWith
  "Put two +1/+1 counters on this, then look at the top 7 cards"
#guard !Effect.searchBasicLandTapped.requiresTarget
#guard !Effect.becomeBearCreatureWithLandsPT.requiresTarget
#guard (Effect.abilityDrawThenDiscard 1).phrase ==
  "Draw a card, then discard a card"
#guard (Effect.abilityDrawThenDiscard 2).phrase ==
  "Draw 2 cards, then discard a card"
#guard (Effect.abilityCreateTokens .treasure 1).phrase ==
  "Create a Treasure token"
#guard (Effect.plusOneOnTarget 2).phrase ==
  "Put 2 +1/+1 counters on target creature you control"
#guard (Effect.plusOneOnTarget 2 #["Elf"]).phrase ==
  "Put 2 +1/+1 counters on target Elf you control"
#guard (Effect.plusOneOnTarget 2 #["Goblin", "Orc"]).phrase ==
  "Put 2 +1/+1 counters on target Goblin or Orc you control"
#guard (Effect.plusOneOnTarget 2).targetSpec == .creatureYouControl
#guard (Effect.plusOneOnTarget 2 #["Elf"]).targetSpec ==
  .creatureYouControlAnySubtype #[.elf]
#guard TriggeredAbility.toNotation (.onEnterCreateTokens .treasure 1) ==
  "When this permanent enters, create a Treasure token."
#guard TriggeredAbility.toNotation (.onEnterCreateTokens .treasure 1 true) ==
  "When this permanent enters, create a tapped Treasure token."
#guard (TriggeredAbility.onEnterCreateTokens .treasure 1).effect.body ==
  Instruction.createTokensFixed .treasure 1
#guard (TriggeredAbility.onEnterCreateTokens .treasure 1 true).effect.body ==
  Instruction.createTokensFixed .treasure 1 .you true
#guard TriggeredAbility.onEnterScry 2 == (SharedTrigger.scry 2).toTriggeredAbility (pattern? := some .thisEnters)
#guard TriggeredAbility.onAttackScry 1 == (SharedTrigger.scry 1).toTriggeredAbility (pattern? := some .thisAttacks)
#guard TriggeredAbility.onEnterDraw 1 == (SharedTrigger.draw 1).toTriggeredAbility (pattern? := some .thisEnters)
#guard TriggeredAbility.onDiesDraw 1 == (SharedTrigger.draw 1).toTriggeredAbility (pattern? := some .thisDies)
#guard TriggeredAbility.onEnterCreateTokens .treasure 1 true ==
  TriggeredAbility.mkTrigger .thisEnters (Effect.triggerCreateTokens .treasure 1 true)
#guard TriggeredAbility.onEnterOrAttackDealDividedDamage 3 3 ==
  (SharedTrigger.dividedDamage 3 3).toTriggeredAbility (pattern? := some .enterOrAttack)
#guard TriggeredAbility.onEnterTargetOpponentSacrifices ==
  SharedTrigger.opponentSacrificesCreature.toTriggeredAbility (pattern? := some .thisEnters)
#guard TriggeredAbility.onEnterAttachToLegendary ==
  (SharedTrigger.attachTo .legendaryCreatureYouControl).toTriggeredAbility (pattern? := some .thisEnters)
#guard TriggeredAbility.onCombatPlusOneOnCreatureYouControl.effect.body ==
  Instruction.putPlusOne (.target 0) 1
#guard TriggeredAbility.onEnterOrAttackCreateWall ==
  TriggeredAbility.mkTrigger .enterOrAttack (Effect.triggerCreateTokens .wall 1)
#guard TriggeredAbility.onEnterConnive ==
  SharedTrigger.connive.toTriggeredAbility (pattern? := some .thisEnters)
#guard TriggeredAbility.onDrawSecondPlusOne.effect.body == Instruction.putPlusOne .this 1
#guard TriggeredAbility.onYourEndStepDrawLoseLife ==
  TriggeredAbility.mkTrigger .stepYourEndStep Effect.seqDrawAndLoseLife
#guard TriggeredAbility.onAttackFerociousGainLife 2 ==
  (SharedTrigger.gainLife 2).toTriggeredAbility
    (pattern? := some (.whenCond .thisAttacks (TriggeredAbility.condControlCreaturePowerAtLeast 4)))
#guard TriggeredAbility.onArtifactYouControlEntersDrawOnce ==
  (SharedTrigger.draw 1).toTriggeredAbility (pattern? := some .artifactYouControlEnters) (limit? := some .onceEachTurn)
#guard (TriggeredAbility.onCastColorPump .green 4 4).effect.body ==
  Instruction.pumpFixed (.target 0) 4 4
#guard TriggeredAbility.onEnterExileOppTappedUntilLeaves ==
  (SharedTrigger.exileUntilLeaves .oppTappedCreature).toTriggeredAbility (pattern? := some .thisEnters)
#guard TriggeredAbility.onOpponentCastsFirstNoncreatureRecruit ==
  (SharedTrigger.recruit .you).toTriggeredAbility (pattern? := some .opponentCastsFirstNoncreature)
#guard TriggeredAbility.onCastInstantOrSorceryDealDamageToEachOpponent 2 ==
  (SharedTrigger.damageEachOpponent 2).toTriggeredAbility (pattern? := some .youCastInstantOrSorcery) (untargeted := true)
#guard TriggeredAbility.onEnterExileTop ==
  SharedTrigger.exileTop.toTriggeredAbility (pattern? := some .thisEnters)
#guard TriggeredAbility.onEnterMayDiscardDraw 2 ==
  (SharedTrigger.mayTo .discard (.draw 2)).toTriggeredAbility (pattern? := some .thisEnters)
#guard (TriggeredAbility.onEnterMayDiscardDraw 2).resolution ==
  .may (.discard (.cards 1)) (.draw (.fixed 2)) .ifYouDo
#guard ((SharedTrigger.mayTo (.scry 1) (.gainLife 2)).toTriggeredAbility (pattern? := some .thisEnters)).resolution ==
  .may (.scry (.fixed 1)) (.gainLife (.fixed 2)) .ifYouDo
#guard ((SharedTrigger.mayTo (.discard 1) (.millPlayer 3)).toTriggeredAbility (pattern? := some .thisEnters)).targetSpec ==
  .player
#guard TriggeredAbility.onCastNoncreatureMayDrawXDiscard2 ==
  (SharedTrigger.may (.drawXDiscard 2)).toTriggeredAbility (pattern? := some .youCastNoncreature)
#guard (TriggeredAbility.onCastNoncreatureMayDrawXDiscard2).resolution ==
  .may (.sequence [.draw .equalToManaSpent, .«if» .manaSpent (.discard (.cards 2))]) (.sequence [])
#guard TriggeredAbility.toNotation .onCastNoncreatureMayDrawXDiscard2 ==
  "Whenever you cast a noncreature spell, you may draw X cards, where X is the amount of mana spent to cast that spell. If you do, discard two cards."
#guard TriggeredAbility.onEnterEachOpponentDiscards ==
  SharedTrigger.opponentDiscards.toTriggeredAbility (pattern? := some .thisEnters)
#guard TriggeredAbility.onAttackOtherGets2AndTrample.effect.body ==
  Instruction.pumpAndTrample (.target 0) 2 0
#guard TriggeredAbility.onEquipmentYouControlEntersDraw ==
  (SharedTrigger.draw 1).toTriggeredAbility (pattern? := some .equipmentYouControlEnters)
#guard TriggeredAbility.onCreatureYouControlAttacksAloneInvestigate ==
  SharedTrigger.investigate.toTriggeredAbility (pattern? := some .creatureYouControlAttacksAlone)
#guard TriggeredAbility.onOpponentCastsAmassOrcs 1 ==
  (SharedTrigger.amass 1 .orc).toTriggeredAbility (pattern? := some .opponentCastsSpell)
#guard !TriggeredAbility.requiresTarget
  (.onCastInstantOrSorceryDealDamageToEachOpponent 2)
#guard TriggeredAbility.onEnterSearchForest ==
  SharedTrigger.searchLibrary.toTriggeredAbility (pattern? := some .thisEnters)
#guard TriggeredAbility.onEnterEachPlayerSacrificesCreature ==
  SharedTrigger.eachPlayerSacrificesCreature.toTriggeredAbility (pattern? := some .thisEnters)
#guard TriggeredAbility.onCombatDamageToPlayerLoot ==
  TriggeredAbility.mkTrigger .thisDealsCombatDamageToPlayer (Effect.seqDrawThenDiscard 1)
#guard TriggeredAbility.onAttackFerociousPlusOneEach ==
  SharedTrigger.plusOneEachYouControl.toTriggeredAbility
    (pattern? := some (.whenCond .thisAttacks (TriggeredAbility.condControlCreaturePowerAtLeast 4)))
#guard TriggeredAbility.onScryPumpSelfForEachLookedAt ==
  SharedTrigger.pumpByLookedAt.toTriggeredAbility (pattern? := some .youScry)
#guard TriggeredAbility.onScryPumpAndUnblockableOnce ==
  TriggeredAbility.mkTrigger .youScry Effect.seqPumpAndUnblockable (limit := .onceEachTurn)
#guard TriggeredAbility.onRingTemptsMayDiscardDraw 4 ==
  (SharedTrigger.mayDiscardHandDraw 4).toTriggeredAbility (pattern? := some .theRingTemptsYou)
#guard TriggeredAbility.onDrawSecondPlusOneLifelink ==
  TriggeredAbility.mkTrigger (.drawCard .you) (Effect.seqPlusOneAndLifelink .creature) (limit := .nthEachTurn 2)
#guard TriggeredAbility.onceEachTurn .onScryPumpAndUnblockableOnce
#guard TriggeredAbility.onAttackFerociousPlusOneEach.pattern ==
  .whenCond .thisAttacks (TriggeredAbility.condControlCreaturePowerAtLeast 4)
#guard TriggeredAbility.allowsZeroTargets .onEnterMayExileAnotherCreature
#guard TriggeredAbility.onAttackPumpByGreatestPower ==
  SharedTrigger.pumpGreatestPower.toTriggeredAbility (pattern? := some .thisAttacks)
#guard TriggeredAbility.onBecomesBlockedDeal1ToBlockers ==
  (SharedTrigger.damageBlockers 1).toTriggeredAbility (pattern? := some .thisBecomesBlocked)
#guard TriggeredAbility.onEnterCreateThenAttach .treasure ==
  TriggeredAbility.mkTrigger .thisEnters (Effect.triggerCreateThenAttach .treasure)
#guard (TriggeredAbility.onEnterCreateThenAttach .dwarf).effect.body ==
  .bind ⟨0⟩ (Instruction.createTokensFixed .dwarf 1) (.permanent (.attach .this (.stepObjects ⟨0⟩)))
#guard TriggeredAbility.toNotation (.onEnterCreateThenAttach .dwarf) ==
  "When this permanent enters, create a 2/2 red Dwarf creature token, then attach this Equipment to it."
#guard TriggeredAbility.resolution (.onEnterGainLifeSearchBasicOnTop 2) ==
  .sequence [.gainLife (.fixed 2), .searchLibrary (.put .basicLandOnTop)]
#guard TriggeredAbility.toNotation (.onEnterGainLifeSearchBasicOnTop 2) ==
  "When this permanent enters, you gain 2 life. You may search your library for a basic land card, reveal it, then shuffle and put that card on top."
#guard TriggeredAbility.onLandYouControlEntersDrawPlusOneSource ==
  TriggeredAbility.mkTrigger .landYouControlEnters Effect.seqDrawPlusOneSource
#guard TriggeredAbility.onArmyCombatDamageRingTempts ==
  SharedTrigger.ringTempts.toTriggeredAbility (pattern? := some .armyYouControlCombatDamageToPlayer)
#guard TriggeredAbility.onAttackSetOtherBasePT ==
  SharedTrigger.setOtherBasePT.toTriggeredAbility (pattern? := some .thisAttacks)
#guard TriggeredAbility.onEnterOrAttackReturnElfGainLife ==
  SharedTrigger.returnElfGainLife.toTriggeredAbility (pattern? := some .enterOrAttack)
#guard TriggeredAbility.resolution .onEnterOrAttackReturnElfGainLife ==
  .sequence [.returnToHand .graveyardCard, .gainLife .equalToTargetPower]
#guard TriggeredAbility.onDiesDealDamageEqualToPowerToOppCreature ==
  SharedTrigger.damageFromLastKnownPower.toTriggeredAbility (pattern? := some .thisDies)
#guard TriggeredAbility.onCastNoncreaturePumpAndDamageOpponents 1 ==
  TriggeredAbility.mkTrigger .youCastNoncreature (Effect.seqPumpAndDamageOpponents 1)
#guard TriggeredAbility.onEnterExileOppGyCardOppsLoseLife 2 ==
  TriggeredAbility.mkTrigger .thisEnters (Effect.seqExileOppGyCardOppsLoseLife 2)
#guard TriggeredAbility.onEnterCreaturesYouControlGetAndFirstStrike 1 ==
  TriggeredAbility.mkTrigger .thisEnters (Effect.seqCreaturesPumpAndFirstStrike 1)
#guard TriggeredAbility.onAnotherCreatureYouControlPowerAtMostEntersMayPayDraw 2 1 ==
  (SharedTrigger.mayPayGenericDraw 1).toTriggeredAbility (pattern? := some (.permanentEnters (.all #[
    .otherThan .this, .hasType .creature, .controlledBy .you, .stat .power .le (.const 2)])))
#guard (TriggeredAbility.onAnotherCreatureYouControlPowerAtMostEntersMayPayDraw 2 1).pattern ==
  .permanentEnters (.all #[
    .otherThan .this, .hasType .creature, .controlledBy .you, .stat .power .le (.const 2)])
#guard TriggeredAbility.onEnterDrawThenBottomIfNoLegendary ==
  SharedTrigger.drawThenBottomIfNoLegendary.toTriggeredAbility (pattern? := some .thisEnters)
#guard TriggeredAbility.resolution .onEnterDrawThenBottomIfNoLegendary ==
  .sequence [.draw (.fixed 1), .«if» (.not (.atLeast (.count .legendaryCreaturesYouControl) (.fixed 1))) (.putOnLibrary .bottom .cardFromHand)]
#guard TriggeredAbility.toNotation .onEnterDrawThenBottomIfNoLegendary ==
  "When this permanent enters, draw a card. Then if you don't control a legendary creature, put a card from your hand on the bottom of your library."
#guard TriggeredAbility.onYourEndStepRemoveHopeDrawSac ==
  SharedTrigger.removeHopeDrawSac.toTriggeredAbility (pattern? := some .stepYourEndStep)
#guard TriggeredAbility.resolution .onYourEndStepRemoveHopeDrawSac ==
  .sequence [.removeCounters .hope .source, .«if» .removedHope (.draw (.fixed 1)),
    .«if» (.not .hopeOnSource) (.sequence [.sacrifice .source, .gainLife (.fixed 4)])]
#guard TriggeredAbility.toNotation .onYourEndStepRemoveHopeDrawSac ==
  "At the beginning of your end step, remove a hope counter from this. If you do, draw a card. Then if this has no hope counters on it, sacrifice it and you gain 4 life."
#guard TriggeredAbility.onAttackTapHumansDraw ==
  SharedTrigger.tapHumansDraw.toTriggeredAbility (pattern? := some .thisAttacks)
#guard TriggeredAbility.resolution .onAttackTapHumansDraw ==
  .sequence [.may (.tap .humans) (.sequence []), .draw .forEachTappedHuman]
#guard TriggeredAbility.toNotation .onAttackTapHumansDraw ==
  "Whenever this creature attacks, you may tap any number of untapped Humans you control. Draw a card for each Human tapped this way."
#guard TriggeredAbility.onEnterUntapOtherPlusOneIfSubtype "Bear" ==
  TriggeredAbility.mkTrigger .thisEnters (Effect.seqUntapPlusOneIfSubtype "Bear")
#guard TriggeredAbility.onEnterDestroyOppArtifactsEnchantmentsGainLife ==
  SharedTrigger.destroyOppArtifactsEnchantmentsGainLife.toTriggeredAbility (pattern? := some .thisEnters)
#guard TriggeredAbility.resolution .onEnterDestroyOppArtifactsEnchantmentsGainLife ==
  .sequence [.destroy .oppArtifactsEnchantments (note := .countDestroyed),
    .gainLife .forEachDestroyedThisWay]
#guard TriggeredAbility.toNotation .onEnterDestroyOppArtifactsEnchantmentsGainLife ==
  "When this permanent enters, destroy all artifacts and enchantments your opponents control. You gain 1 life for each permanent destroyed this way."
#guard TriggeredAbility.onEnterOrAttackPlusOneEachOtherGainLife ==
  SharedTrigger.plusOneEachOtherGainLife.toTriggeredAbility (pattern? := some .enterOrAttack)
#guard TriggeredAbility.resolution .onEnterOrAttackPlusOneEachOtherGainLife ==
  .sequence [.putCounters (.ofKind .plusOnePlusOne) .eachOther, .gainLife .perOtherCreature]
#guard TriggeredAbility.toNotation .onEnterOrAttackPlusOneEachOtherGainLife ==
  "Whenever this creature enters or attacks, put a +1/+1 counter on each other creature you control. You gain 1 life for each other creature you control."
#guard TriggeredAbility.onAttackDamageEqualSubtypeToEachOpponent "Dwarf" ==
  (SharedTrigger.damageEqualSubtypeToEachOpponent .dwarf).toTriggeredAbility (pattern? := some .thisAttacks)
#guard TriggeredAbility.onAttackDamageEqualTreasures ==
  SharedTrigger.damageEqualTreasures.toTriggeredAbility (pattern? := some .thisAttacks)
#guard TriggeredAbility.onPlayerCastsSecondSpellLoseLifeCreateTreasure ==
  TriggeredAbility.mkTrigger .anyPlayerCastsSecondSpell Effect.seqLoseLifeCreateTreasure
#guard TriggeredAbility.onEnterDealDamageDestroyIfSubtype 1 "Dragon" ==
  (SharedTrigger.dealDamageDestroyIfSubtype 1 .dragon).toTriggeredAbility (pattern? := some .thisEnters)
#guard TriggeredAbility.resolution (.onEnterDealDamageDestroyIfSubtype 1 "Dragon") ==
  .sequence [.dealDamage (.fixed 1) .target .markedPermanent,
    .«if» (.dealtDamageToSubtype .dragon) (.destroy .permanentDealtDamage)]
#guard TriggeredAbility.toNotation (.onEnterDealDamageDestroyIfSubtype 1 "Dragon") ==
  "When this permanent enters, it deals 1 damage to any target. If a Dragon is dealt damage this way, destroy it."
#guard TriggeredAbility.onEnterAttachTargetEquipment ==
  SharedTrigger.attachEquipmentToCreature.toTriggeredAbility (pattern? := some .thisEnters)
#guard TriggeredAbility.onAttackDefenderSacsLeastPower ==
  SharedTrigger.defenderSacsLeastPower.toTriggeredAbility (pattern? := some .thisAttacks)
#guard TriggeredAbility.onEnterReturnOtherPlusOne ==
  SharedTrigger.returnOtherPlusOne.toTriggeredAbility (pattern? := some .thisEnters)
#guard TriggeredAbility.resolution .onEnterReturnOtherPlusOne ==
  .sequence [.returnToHand .permanent .returnedPermanent, .«if» .returnedPermanent (.putCounters (.ofKind .plusOnePlusOne) .source)]
#guard TriggeredAbility.toNotation .onEnterReturnOtherPlusOne ==
  "When this permanent enters, return up to one other target permanent you control to its owner's hand. If you do, put a +1/+1 counter on this creature."
#guard TriggeredAbility.onEnterLookAtTopRevealTypes 4 #["Dwarf", "Equipment"] ==
  (SharedTrigger.lookAtTopRevealTypes 4 #["Dwarf", "Equipment"]).toTriggeredAbility (pattern? := some .thisEnters)
#guard TriggeredAbility.onEnterCreateTappedTreasuresEqualOppArtifacts ==
  SharedTrigger.createTappedTreasuresEqualOppArtifacts.toTriggeredAbility (pattern? := some .thisEnters)
#guard TriggeredAbility.onCombatDamagePutNonlandMvAtMost 3 ==
  (SharedTrigger.putNonlandMvAtMostFromGy 3).toTriggeredAbility (pattern? := some .thisDealsCombatDamageToPlayerOrBattle)
#guard TriggerPattern.anyPlayerCastsSecondSpell.flattenOr ==
  #[.anyPlayerCastsSecondSpell]
#guard TriggerPattern.enterOrAttack == .or .thisEnters .thisAttacks
#guard TriggerPattern.enterOrAttack.flattenOr == #[.thisEnters, .thisAttacks]
#guard TriggerPattern.castGreenOrForestEnters ==
  .or (.youCastColor .green) .forestYouControlEnters
#guard TriggerPattern.enterOrOpponentDrawsExceptFirst ==
  .or .thisEnters (.drawCard .opponent (exceptFirstDrawStep := true))
#guard (TriggerPattern.or .thisEnters .thisAttacks).flattenOr == #[.thisEnters, .thisAttacks]
#guard TriggeredAbility.onEachCombatOthersGetAndOppsGet #["Goblin", "Orc"] 2 2 (-1) (-1) ==
  (SharedTrigger.othersGetAndOppsGet #[.goblin, .orc] 2 2 (-1) (-1)).toTriggeredAbility (pattern? := some .stepEachBeginCombat)
#guard TriggeredAbility.resolution
    (.onEachCombatOthersGetAndOppsGet #["Goblin", "Orc"] 2 2 (-1) (-1)) ==
  .sequence [.pump (.fixed 2) (.fixed 2) (.intersection [.creaturesYouControl, .union ([.goblin, .orc].map .othersOfSubtype)]),
    .pump (.fixed (-1)) (.fixed (-1)) .opponentsCreatures]
#guard TriggeredAbility.toNotation
    (.onEachCombatOthersGetAndOppsGet #["Goblin", "Orc"] 2 2 (-1) (-1)) ==
  "At the beginning of each combat, other Goblins and Orcs you control get +2/+2 until end of turn. Creatures your opponents control get -1/-1 until end of turn."
#guard TriggeredAbility.onCombatDamageWolfPlusOneOrTreasure ==
  SharedTrigger.wolfPlusOneOrTreasure.toTriggeredAbility (pattern? := some .thisDealsCombatDamageToPlayer)
#guard TriggeredAbility.resolution .onCombatDamageWolfPlusOneOrTreasure ==
  .or [.putCounters (.ofKind .plusOnePlusOne) .permanent, .createTokens 0 (.fixed 1) false]
#guard (SharedTrigger.toEffect .tapOppOrUntapYours).resolution ==
  .or [.tap .target, .untap]
#guard TriggeredAbility.resolution .onLandYouControlEntersTapOrUntap ==
  .or [.tap .target, .untap]
#guard TriggeredAbility.onYourBeginCombatTrampleCounterBecomeBear ==
  SharedTrigger.trampleCounterBecomeBear.toTriggeredAbility (pattern? := some .stepYourBeginCombat)
#guard TriggeredAbility.onEnterMillThenSubtypeToHand 4 "Elf" ==
  (SharedTrigger.millThenSubtypeToHand 4 .elf).toTriggeredAbility (pattern? := some .thisEnters)
#guard TriggeredAbility.onEnterExileOppNonlandEachUntilLeaves ==
  SharedTrigger.exileOppNonlandEachUntilLeaves.toTriggeredAbility (pattern? := some .thisEnters)
#guard TriggeredAbility.onCastCreaturePlusOneEqualMv ==
  SharedTrigger.plusOneEqualLastKnownMv.toTriggeredAbility (pattern? := some .youCastCreature)
#guard TriggeredAbility.onMountainEntersQuestThenDragon ==
  SharedTrigger.mountainQuestDragon.toTriggeredAbility (pattern? := some .mountainYouControlEnters)
#guard TriggeredAbility.onEquippedCombatDamageTreasuresPerChosenType ==
  SharedTrigger.treasuresPerChosenType.toTriggeredAbility (pattern? := some .equippedDealsCombatDamageToPlayer)
#guard TriggeredAbility.onNontokenYouControlDiesRevealCreature ==
  SharedTrigger.revealUntilCreature.toTriggeredAbility (pattern? := some .nontokenCreatureYouControlDies) (limit? := some .onceEachTurn)
#guard TriggeredAbility.onceEachTurn .onNontokenYouControlDiesRevealCreature
#guard TriggeredAbility.onAttackMaySacAnotherPlusOneEqualPower ==
  SharedTrigger.attackSacPlusOneEqualPower.toTriggeredAbility (pattern? := some .thisAttacks)
#guard TriggeredAbility.onEnterLootLandEntersTapped ==
  SharedTrigger.lootLandEntersTapped.toTriggeredAbility (pattern? := some .thisEnters)
#guard TriggeredAbility.onPlayerLosesLifeMillThatMany ==
  SharedTrigger.millThatManyLost.toTriggeredAbility (pattern? := some (.loseLife .any))
#guard TriggeredAbility.onDiesDrawPerFatGraveyard ==
  SharedTrigger.drawPerFatGraveyard.toTriggeredAbility (pattern? := some .thisDies)
#guard TriggeredAbility.onEnterMaySacDrawTreasure ==
  SharedTrigger.maySacDrawTreasure.toTriggeredAbility (pattern? := some .thisEnters)
#guard TriggeredAbility.onEquippedAttacksPlusOneEachIfCityBlessing ==
  (SharedTrigger.plusOneEachYouControl .citysBlessing).toTriggeredAbility (pattern? := some .equippedAttacks)
#guard TriggeredAbility.onYourBeginCombatCastInstantSorceryFromHand ==
  SharedTrigger.castInstantSorceryFromHand.toTriggeredAbility (pattern? := some .stepYourBeginCombat)
#guard TriggeredAbility.onEquippedCombatDamageCastInstantSorcery ==
  SharedTrigger.castInstantSorceryMvAtMost.toTriggeredAbility (pattern? := some .equippedDealsCombatDamageToPlayer)
#guard TriggeredAbility.onCastSecondSpellMillThenCopy ==
  SharedTrigger.millThenCopy.toTriggeredAbility (pattern? := some .youCastSecondSpell)
#guard TriggeredAbility.onCombatAnotherGetsSourcePower ==
  SharedTrigger.pumpTargetBySourcePower.toTriggeredAbility (pattern? := some .stepYourBeginCombat)
#guard TriggeredAbility.onCombatCreateAlienPerInvasion ==
  SharedTrigger.createAlienPerInvasion.toTriggeredAbility (pattern? := some .stepYourBeginCombat)
#guard TriggeredAbility.onCombatMayPutArtifactAttachEquipment ==
  SharedTrigger.mayPutArtifactAttachEquipment.toTriggeredAbility (pattern? := some .stepYourBeginCombat)
#guard TriggeredAbility.resolution .onCombatMayPutArtifactAttachEquipment ==
  .sequence [.may (.put .artifactFromHand (note := .forAttach)) (.sequence []),
    .«if» (.atLeast (.count .putEquipment) (.fixed 1)) (.attach .putArtifact .notedHost)]
#guard TriggeredAbility.onCastCascade ==
  SharedTrigger.cascade.toTriggeredAbility (pattern? := some .thisCast) (activeZones? := some #[.stack])
#guard TriggeredAbility.onEnterBolgMaySacrifice ==
  SharedTrigger.bolgMaySacrifice.toTriggeredAbility (pattern? := some .thisEnters)
#guard TriggeredAbility.onEnterSurveil 2 ==
  (SharedTrigger.surveil 2).toTriggeredAbility (pattern? := some .thisEnters)
#guard TriggeredAbility.onWatch Effect.watchHulk ==
  (SharedTrigger.watch .hulk).toTriggeredAbility
#guard TriggeredAbility.onStep Effect.stepDrawToTen ==
  (SharedTrigger.step .drawToTen).toTriggeredAbility
#guard TriggeredAbility.sagaChapter 1 Effect.chapterRecruit ==
  { word := .when
    pattern := TriggerPattern.putCountersOnSelf .lore
    grouping := .counterThreshold .lore #[1]
    effect := Effect.chapterRecruit }
#guard TriggeredAbility.onceEachTurn .onFinalSagaChapterRevealSaga
#guard TriggeredAbility.onYouSacrificeTokenOppLosesLife ==
  (SharedTrigger.targetOpponentLosesLife 1).toTriggeredAbility (pattern? := some .youSacrificeToken)
#guard TriggeredAbility.onDiesAmassGoblinsEqualPower ==
  (SharedTrigger.amass 0 (amount := .sourcePower)).toTriggeredAbility (pattern? := some .thisDies)
#guard (TriggeredAbility.onAttackFerociousGainLife 2).pattern ==
  .whenCond .thisAttacks (TriggeredAbility.condControlCreaturePowerAtLeast 4)
#guard TriggeredAbility.onceEachTurn .onArtifactYouControlEntersDrawOnce
#guard !(Effect.sourceGets 1 0).requiresTarget
#guard !(Effect.putPlusOnePlusOneOnSource 3).requiresTarget
#guard StaticAbility.toNotation .cantBeBlocked == "This creature can't be blocked."
#guard toString Keyword.menace == "menace"
#guard CardDef.isKeywordRestatement #[Keyword.menace] "Menace"
#guard CardDef.isKeywordRestatement #[Keyword.menace]
  "Menace (This creature can't be blocked except by two or more creatures.)"
#guard !CardDef.isKeywordRestatement #[Keyword.menace] "Flying"
#guard
  let ab : ActivatedAbility := {
    cost := CostSpec.ofItems #[.mana (ManaCost.ofGeneric 1), .discard (.exact 1) .self]
    effect := Effect.searchLandTypeToHand "Mountain"
    activeZones := #[.hand]
  }
  toString ab ==
    "{1}, Discard this card: Search your library for a Mountain card, reveal it, put it into your hand, then shuffle (activate only from your hand)"
#guard
  let ab : ActivatedAbility := {
    cost := CostSpec.ofItems #[.mana (ManaCost.ofGeneric 2), .tapSelf, .sacrifice (.exact 1) .self]
    effect := Effect.searchBasicLandTapped
  }
  (toString ab).startsWith "{2}, {T}, Sacrifice this:"
#guard
  let ab : ActivatedAbility := {
    cost := CostSpec.ofItem (.payLife (.const 2))
    effect := Effect.sourceGets 2 2
    turnLimit? := some 1
  }
  toString ab ==
    "Pay 2 life: This creature gets +2/+2 until end of turn (activate only once each turn)"
#guard
  let ab : ActivatedAbility := ActivatedAbility.mkModal
    (CostSpec.ofItems #[.mana (ManaCost.ofGeneric 1), .sacrifice (.exact 1) .self])
    #[Effect.dealDamageToTargetCreature 2, Effect.destroyTargetColorlessNonland]
  ab.isModal &&
    (toString ab).startsWith "{1}, Sacrifice this: Choose one —" &&
    ((toString ab).splitOn "target creature").length > 1 &&
    ((toString ab).splitOn "colorless nonland").length > 1
#guard StaticAbility.toNotation (.otherCreaturesHaveTrample #[.orc, .goblin]) ==
  "Other Orcs and Goblins you control have trample."
#guard StaticAbility.toNotation (.otherCreaturesGet #[.elf] 1 1) ==
  "Other Elf creatures you control get +1/+1."
#guard StaticAbility.toNotation (.extraTriggerAnotherYouControl #[.wolf] #[.battle]) ==
  "If a triggered ability of another Wolf or battle you control triggers, that ability triggers an additional time."
#guard StaticAbility.toNotation (.extraTriggerIfEnduringStorySubtype .dwarf) ==
  "As long as you have an enduring story, if a triggered ability of a Dwarf you control triggers, that ability triggers an additional time."
#guard
  let ab := ActivatedAbility.manaAbility
    (.sequence #[(.colored .green, ValueExpr.count (.controlledOfSubtype .elf))])
  toString ab == "{T}: Add {G} for each Elf you control."
#guard StaticAbility.toNotation (.enchantedCreatureGets 3 3) ==
  "Enchanted creature gets +3/+3."
#guard StaticAbility.toNotation (.equippedCreatureGets 2 0) ==
  "Equipped creature gets +2/+0."
#guard StaticAbility.toNotation .powerToughnessEqualLandsYouControl ==
  "This creature's power and toughness are each equal to the number of lands you control."
#guard
  let c : CardDef := { name := "Silent Path", types := #[.creature] }
  c.ptString == "*/*"
#guard
  let c : CardDef := { name := "Silent Aura", types := #[.enchantment] }
  c.ptString == ""
#guard
  let c : CardDef := { name := "Silent Star", types := #[.creature], power := some 2 }
  c.ptString == "2/*"
#guard
  let c : CardDef := { name := "Silent Star", types := #[.creature], toughness := some 3 }
  c.ptString == "*/3"
#guard
  let c : CardDef := {
    name := "Lost Order of Jarkeld", types := #[.creature]
    power := some 1, toughness := some 1, powerStar := true, toughnessStar := true
  }
  c.ptString == "1+*/1+*"
#guard
  let c : CardDef := {
    name := "Tarmogoyf", types := #[.creature]
    powerStar := true, toughness := some 1, toughnessStar := true
  }
  c.ptString == "*/1+*"
#guard StaticAbility.toNotation (.cantBlockUnlessYouControl #[.goblin, .orc]) ==
  "This creature can't block unless you control a Goblin or Orc."
#guard StaticAbility.toNotation (.cantBlockUnlessYouControl #[]) ==
  "This creature can't block."
#guard StaticAbility.toNotation (.cantBeBlockedExceptBy 3) ==
  "This creature can't be blocked except by three or more creatures."
#guard StaticAbility.toNotation (.cantBeBlockedExceptBy 2) ==
  "This creature can't be blocked except by two or more creatures."
#guard (match StaticAbility.cantBeBlockedExceptBy 3 with
  | .ruleModifying none (.combat (.minBlockers .self 3)) => true
  | _ => false)
#guard StaticAbility.toNotation (.cantBeBlockedIfPowerAtMost 1) ==
  "This creature can't be blocked if its power is 1 or less."
#guard (match StaticAbility.cantBeBlockedIfPowerAtMost 1 with
  | .ruleModifying (some (.forAll .this (.stat .power .le (.const 1)))) (.combat (.cantBeBlocked .self)) => true
  | _ => false)
#guard TriggeredAbility.toNotation .onAttackPumpByGreatestPower ==
  "Whenever this creature attacks, it gets +X/+0 until end of turn, where X is the greatest power among creatures you control."
#guard TriggeredAbility.toNotation .onAttackSetOtherBasePT ==
  "Whenever this creature attacks, choose up to one other target creature you control. Its base power and toughness become equal to this creature's power and toughness until end of turn."
#guard TriggeredAbility.toNotation .onAttackOtherGets2AndTrample ==
  "Whenever this creature attacks, another target creature you control gets +2/+0 and gains trample until end of turn."
#guard TriggeredAbility.toNotation (.onAttackScry 1) ==
  "Whenever this creature attacks, scry 1."
#guard TriggeredAbility.toNotation (.onAttackFerociousGainLife 2) ==
  "Whenever this creature attacks while you control a creature with power 4 or greater, you gain 2 life."
#guard TriggeredAbility.toNotation .onBecomesBlockedDeal1ToBlockers ==
  "Whenever this creature becomes blocked, it deals 1 damage to each creature blocking it."
#guard TriggeredAbility.toNotation (.onEnterScry 2) ==
  "When this permanent enters, scry 2."
#guard TriggeredAbility.toNotation (.onEnterDraw 1) ==
  "When this permanent enters, draw a card."
#guard TriggeredAbility.toNotation (.onEnterDraw 2) ==
  "When this permanent enters, draw 2 cards."
#guard TriggeredAbility.toNotation .onEnterSearchForest ==
  "When this permanent enters, search your library for a Forest card, put that card onto the battlefield, then shuffle."
#guard TriggeredAbility.toNotation (.onEnterMayDiscardDraw 2) ==
  "When this permanent enters, you may discard a card. If you do, draw 2 cards."
#guard TriggeredAbility.toNotation .onEnterTargetOpponentSacrificesCreature ==
  "When this permanent enters, target opponent sacrifices a creature of their choice."
#guard TriggeredAbility.toNotation .onLandYouControlEntersPlusOnePlusOne ==
  "Whenever a land you control enters, put a +1/+1 counter on target creature you control."
#guard TriggeredAbility.toNotation (.onLandYouControlEntersGets 1 1) ==
  "Whenever a land you control enters, this creature gets +1/+1 until end of turn."
#guard TriggeredAbility.toNotation .onCombatPlusOneOnCreatureYouControl ==
  "At the beginning of combat on your turn, put a +1/+1 counter on target creature you control."
#guard TriggeredAbility.toNotation .onCombatTargetYouControlConnives ==
  "At the beginning of combat on your turn, target creature you control connives."
#guard TriggeredAbility.toNotation .onCombatAnotherGetsSourcePower ==
  "At the beginning of combat on your turn, another target creature you control gets +X/+0 until end of turn, where X is this creature's power."
#guard TriggeredAbility.toNotation .onCombatCreateAlienPerInvasion ==
  "At the beginning of combat on your turn, create a 1/1 red Alien creature token with haste and \"This token attacks each combat if able.\" Put a +1/+1 counter on it for each invasion counter on this enchantment, then put an invasion counter on this enchantment."
#guard TriggeredAbility.toNotation .onCombatMayPutArtifactAttachEquipment ==
  "At the beginning of combat on your turn, you may put an artifact card from your hand onto the battlefield. If it's an Equipment, attach it to this creature."
#guard TriggeredAbility.resolution .onCombatTargetYouControlConnives ==
  .connive .target
#guard TriggeredAbility.targetSpec .onCombatTargetYouControlConnives ==
  .creatureYouControl
#guard TriggeredAbility.resolutionPhrase { resolution? := some (.connive .hand) } ==
  "connive"
#guard TriggeredAbility.targetSpec .onCombatAnotherGetsSourcePower ==
  .anotherCreatureYouControl
#guard TriggeredAbility.firesOn .onCombatCreateAlienPerInvasion .stepYourBeginCombat
#guard !TriggeredAbility.requiresTarget .onCombatMayPutArtifactAttachEquipment
#guard TriggeredAbility.toNotation (.onEnterDealDividedDamage 3 3) ==
  "When this permanent enters, it deals 3 damage divided as you choose among one, two, or three targets."
#guard TriggeredAbility.toNotation (.onEnterOrAttackDealDividedDamage 3 3) ==
  "Whenever this creature enters or attacks, it deals 3 damage divided as you choose among one, two, or three targets."
#guard TriggeredAbility.toNotation .onEnterOrAttackReturnElfGainLife ==
  "Whenever this creature enters or attacks, return target Elf card from your graveyard to your hand. You gain life equal to that card's power."
#guard TriggeredAbility.toNotation .onDiesDealDamageEqualToPowerToOppCreature ==
  "When this creature dies, it deals damage equal to its power to target creature an opponent controls."
#guard TriggeredAbility.toNotation (.onCastInstantOrSorceryDealDamageToEachOpponent 2) ==
  "Whenever you cast an instant or sorcery spell, this creature deals 2 damage to each opponent."
#guard TriggeredAbility.toNotation (.onAttackWithElvesScry 1) ==
  "Whenever you attack with one or more Elves, scry 1."
#guard TriggeredAbility.toNotation .onScryPumpSelfForEachLookedAt ==
  "Whenever you scry, this creature gets +1/+1 until end of turn for each card looked at while scrying this way."
#guard TriggeredAbility.toNotation .onAnotherElfYouControlEntersGets1 ==
  "Whenever another Elf you control enters, this creature gets +1/+1 until end of turn."
#guard TriggeredAbility.toNotation (.onDiesOppCreatureGets (-1) (-1)) ==
  "When this creature dies, target creature an opponent controls gets -1/-1 until end of turn."
#guard TriggeredAbility.toNotation (.onOneOrMoreOtherCreaturesDieScry 1) ==
  "Whenever one or more other creatures die, scry 1."
#guard TriggeredAbility.toNotation .onEnterTargetOpponentSacrifices ==
  "When this permanent enters, target opponent sacrifices a creature of their choice."
#guard TriggeredAbility.toNotation .onEnterEachPlayerSacrificesCreature ==
  "When this permanent enters, each player sacrifices a creature of their choice."
#guard TriggeredAbility.toNotation .onEnterEachOpponentDiscards ==
  "When this permanent enters, each opponent discards a card."
#guard TriggeredAbility.toNotation (.onEnterExileOppGyCardOppsLoseLife 2) ==
  "When this permanent enters, exile up to one target card from an opponent's graveyard. Each opponent loses 2 life."
#guard TriggeredAbility.toNotation (.onCastNoncreaturePumpAndDamageOpponents 1) ==
  "Whenever you cast a noncreature spell, this gets +1/+1 until end of turn and deals 1 damage to each opponent."
#guard TriggeredAbility.toNotation (.onEnterUntapOtherPlusOneIfSubtype "Bear") ==
  "When this permanent enters, untap another target creature you control. If that creature is a Bear, put a +1/+1 counter on it."
#guard TriggeredAbility.toNotation .onPlayerCastsSecondSpellLoseLifeCreateTreasure ==
  "Whenever a player casts their second spell each turn, you lose 1 life and create a Treasure token."
#guard TriggeredAbility.requiresTarget (.onEnterUntapOtherPlusOneIfSubtype "Bear")
#guard TriggeredAbility.targetSpec (.onEnterUntapOtherPlusOneIfSubtype "Bear") ==
  .anotherCreatureYouControl
#guard !TriggeredAbility.requiresTarget (.onCastNoncreaturePumpAndDamageOpponents 1)
#guard !TriggeredAbility.requiresTarget .onPlayerCastsSecondSpellLoseLifeCreateTreasure
#guard TriggeredAbility.firesOn (.onDiesOppCreatureGets (-1) (-1)) .thisDies
#guard TriggeredAbility.firesOn (.onOneOrMoreOtherCreaturesDieScry 1) .otherCreaturesDie
#guard !TriggeredAbility.firesOn (.onOneOrMoreOtherCreaturesDieScry 1) .thisDies
#guard TriggeredAbility.firesOn .onEnterEachPlayerSacrificesCreature .thisEnters
#guard TriggeredAbility.requiresTarget (.onDiesOppCreatureGets (-1) (-1))
#guard TriggeredAbility.requiresTarget .onEnterTargetOpponentSacrifices
#guard TriggeredAbility.requiresTarget (.onEnterExileOppGyCardOppsLoseLife 2)
#guard TriggeredAbility.allowsZeroTargets (.onEnterExileOppGyCardOppsLoseLife 2)
#guard !TriggeredAbility.requiresTarget .onEnterEachPlayerSacrificesCreature
#guard !TriggeredAbility.requiresTarget .onEnterEachOpponentDiscards
#guard TriggeredAbility.targetSpec (.onDiesOppCreatureGets (-1) (-1)) == .oppCreature
#guard TriggeredAbility.targetSpec .onEnterTargetOpponentSacrifices == .opponent
#guard TriggeredAbility.targetSpec (.onEnterExileOppGyCardOppsLoseLife 2) ==
  .oppGraveyardCard
#guard TriggerPattern.otherCreaturesDie.usesLookBack
#guard TriggerPattern.renderClause {} .oncePerBatch .unlimited .otherCreaturesDie ==
  "one or more other creatures die"
#guard TriggeredAbility.dividedDamage? (.onEnterDealDividedDamage 3 3) == some (3, 3)
#guard (TriggeredAbility.dividedDamage? (.onEnterOrAttackDealDividedDamage 3 3)) == some (3, 3)
#guard (TriggeredAbility.dividedDamage? .onEnterOrAttackReturnElfGainLife).isNone
#guard (TriggeredAbility.dividedDamage? .onLandYouControlEntersPlusOnePlusOne).isNone
#guard (TriggeredAbility.dividedDamage? (.onLandYouControlEntersGets 1 1)).isNone
#guard (TriggeredAbility.dividedDamage? (.onEnterDraw 1)).isNone
#guard (TriggeredAbility.dividedDamage? .onEnterSearchForest).isNone
#guard (TriggeredAbility.dividedDamage? .onEnterTargetOpponentSacrificesCreature).isNone
#guard (TriggeredAbility.dividedDamage? .onDiesDealDamageEqualToPowerToOppCreature).isNone
#guard (TriggeredAbility.dividedDamage? .onAttackSetOtherBasePT).isNone
#guard (TriggeredAbility.dividedDamage? .onAttackOtherGets2AndTrample).isNone
#guard (TriggeredAbility.dividedDamage? (.onAttackScry 1)).isNone
#guard (TriggeredAbility.dividedDamage? (.onAttackFerociousGainLife 2)).isNone
#guard (TriggeredAbility.dividedDamage? (.onCastInstantOrSorceryDealDamageToEachOpponent 2)).isNone
#guard TriggeredAbility.firesOn .onAttackPumpByGreatestPower .thisAttacks
#guard TriggeredAbility.firesOn .onAttackSetOtherBasePT .thisAttacks
#guard TriggeredAbility.firesOn .onAttackOtherGets2AndTrample .thisAttacks
#guard TriggeredAbility.firesOn (.onAttackScry 1) .thisAttacks
#guard TriggeredAbility.firesOn (.onAttackFerociousGainLife 2) .thisAttacks
#guard TriggeredAbility.firesOn (.onEnterOrAttackDealDividedDamage 3 3) .thisAttacks
#guard TriggeredAbility.firesOn .onEnterOrAttackReturnElfGainLife .thisAttacks
#guard !TriggeredAbility.firesOn (.onEnterDealDividedDamage 3 3) .thisAttacks
#guard !TriggeredAbility.firesOn (.onEnterScry 2) .thisAttacks
#guard !TriggeredAbility.firesOn (.onAttackWithElvesScry 1) .thisAttacks
#guard !TriggeredAbility.firesOn .onScryPumpSelfForEachLookedAt .thisAttacks
#guard TriggeredAbility.firesOn (.onAttackWithElvesScry 1) (.youAttackWithSubtype .elf)
#guard !TriggeredAbility.firesOn .onAttackPumpByGreatestPower (.youAttackWithSubtype .elf)
#guard !TriggeredAbility.firesOn (.onAttackScry 1) (.youAttackWithSubtype .elf)
#guard TriggeredAbility.firesOn .onScryPumpSelfForEachLookedAt .youScry
#guard !TriggeredAbility.firesOn (.onEnterScry 2) .youScry
#guard !TriggeredAbility.firesOn (.onAttackWithElvesScry 1) .youScry
#guard !TriggeredAbility.firesOn (.onAttackScry 1) .youScry
#guard TriggeredAbility.firesOn .onAnotherElfYouControlEntersGets1 (.anotherSubtypeYouControlEnters .elf)
#guard !TriggeredAbility.firesOn (.onEnterDraw 1) (.anotherSubtypeYouControlEnters .elf)
#guard !TriggeredAbility.firesOn .onAnotherElfYouControlEntersGets1 .thisEnters
#guard !TriggeredAbility.requiresTarget .onAnotherElfYouControlEntersGets1
#guard (TriggeredAbility.dividedDamage? .onAnotherElfYouControlEntersGets1).isNone
#guard TriggeredAbility.firesOn .onBecomesBlockedDeal1ToBlockers .thisBecomesBlocked
#guard TriggeredAbility.firesOn (.onEnterScry 2) .thisEnters
#guard TriggeredAbility.firesOn (.onEnterDraw 1) .thisEnters
#guard TriggeredAbility.firesOn .onEnterSearchForest .thisEnters
#guard TriggeredAbility.firesOn (.onEnterMayDiscardDraw 2) .thisEnters
#guard TriggeredAbility.firesOn .onEnterTargetOpponentSacrificesCreature .thisEnters
#guard TriggeredAbility.firesOn (.onEnterDealDividedDamage 3 3) .thisEnters
#guard TriggeredAbility.firesOn (.onEnterOrAttackDealDividedDamage 3 3) .thisEnters
#guard TriggeredAbility.firesOn .onEnterOrAttackReturnElfGainLife .thisEnters
#guard !TriggeredAbility.firesOn .onAttackPumpByGreatestPower .thisEnters
#guard !TriggeredAbility.firesOn (.onAttackScry 1) .thisEnters
#guard TriggeredAbility.firesOn
  (.onCastInstantOrSorceryDealDamageToEachOpponent 2) .youCastInstantOrSorcery
#guard !TriggeredAbility.firesOn (.onEnterScry 2) .youCastInstantOrSorcery
#guard
  let ab : ActivatedAbility := {
    cost := CostSpec.ofGeneric 3
    effect := Effect.attachToTargetCreatureYouControl
    timing := .sorcery
  }
  (toString ab).startsWith "{3}: Attach this Equipment" &&
    (toString ab).endsWith "(activate only as a sorcery)"
#guard TriggeredAbility.firesOn .onLandYouControlEntersPlusOnePlusOne .landYouControlEnters
#guard TriggeredAbility.firesOn (.onLandYouControlEntersGets 1 1) .landYouControlEnters
#guard !TriggeredAbility.firesOn (.onEnterScry 2) .landYouControlEnters
#guard TriggeredAbility.requiresTarget .onLandYouControlEntersPlusOnePlusOne
#guard !TriggeredAbility.requiresTarget (.onLandYouControlEntersGets 1 1)
#guard TriggeredAbility.targetSpec .onLandYouControlEntersPlusOnePlusOne ==
  .creatureYouControl
#guard TriggeredAbility.targetSpec .onAttackSetOtherBasePT ==
  .anotherCreatureYouControl
#guard TriggeredAbility.targetSpec (.onEnterDealDividedDamage 3 3) ==
  .anyTarget
#guard TriggeredAbility.targetSpec .onEnterOrAttackReturnElfGainLife ==
  .elfInYourGraveyard
#guard TriggeredAbility.targetSpec .onDiesDealDamageEqualToPowerToOppCreature ==
  .oppCreature
#guard TriggeredAbility.targetSpec .onEnterTargetOpponentSacrificesCreature ==
  .opponent
#guard TriggeredAbility.targetSpec (.onEnterDraw 1) == .none
#guard (match StaticAbility.enchantedCreatureGets 3 3 with
  | .continuous none sc (.modifyPT (.const 3) (.const 3)) => StaticAbility.isScopeEnchantedCreature sc
  | _ => false)
#guard (match StaticAbility.equippedCreatureGets 2 0 with
  | .continuous none sc (.modifyPT (.const 2) (.const 0)) => StaticAbility.isScopeEquippedCreature sc
  | _ => false)
#guard (match StaticAbility.otherCreaturesGet #[.elf] 1 1 with
  | .continuous none sc (.modifyPT (.const 1) (.const 1)) =>
    sc == StaticAbility.scopeOtherCreaturesOfSubtypesYouControl #[.elf]
  | _ => false)
#guard (match StaticAbility.otherCreaturesHaveTrample #[.orc] with
  | .continuous none sc (.grantKeywords ks) =>
    ks == #[Keyword.trample] && sc == StaticAbility.scopeOtherCreaturesOfSubtypesYouControl #[.orc]
  | _ => false)
#guard StaticAbility.isPTDefiningCDA .powerToughnessEqualLandsYouControl
#guard !StaticAbility.isPTDefiningCDA (.enchantedCreatureGets 1 1)
#guard StaticAbility.isCantBeBlocked .cantBeBlocked
#guard !StaticAbility.isCantBeBlocked (.cantBlockUnlessYouControl #[.goblin])
#guard (StaticAbility.cantBlockUnlessYouControl #[.goblin]).anyRule fun cond? r =>
  cond?.isNone && r == .combat (.cantBlock .self (some (StaticAbility.condControlAnySubtype #[.goblin])))
#guard TriggeredAbility.requiresTarget (.onEnterDealDividedDamage 3 3)
#guard TriggeredAbility.requiresTarget (.onEnterOrAttackDealDividedDamage 3 3)
#guard TriggeredAbility.requiresTarget .onEnterOrAttackReturnElfGainLife
#guard TriggeredAbility.requiresTarget .onDiesDealDamageEqualToPowerToOppCreature
#guard TriggeredAbility.requiresTarget .onEnterTargetOpponentSacrificesCreature
#guard TriggeredAbility.requiresTarget .onAttackSetOtherBasePT
#guard TriggeredAbility.requiresTarget .onAttackOtherGets2AndTrample
#guard TriggeredAbility.allowsZeroTargets .onAttackSetOtherBasePT
#guard !TriggeredAbility.allowsZeroTargets .onAttackOtherGets2AndTrample
#guard !TriggeredAbility.allowsZeroTargets .onEnterOrAttackReturnElfGainLife
#guard !TriggeredAbility.allowsZeroTargets .onEnterTargetOpponentSacrificesCreature
#guard !TriggeredAbility.allowsZeroTargets .onLandYouControlEntersPlusOnePlusOne
#guard !TriggeredAbility.allowsZeroTargets (.onLandYouControlEntersGets 1 1)
#guard TriggeredAbility.firesOn .onDiesDealDamageEqualToPowerToOppCreature .thisDies
#guard !TriggeredAbility.firesOn (.onEnterScry 2) .thisDies
#guard !TriggeredAbility.requiresTarget (.onEnterScry 2)
#guard !TriggeredAbility.requiresTarget (.onAttackScry 1)
#guard !TriggeredAbility.requiresTarget (.onAttackFerociousGainLife 2)
#guard !TriggeredAbility.requiresTarget (.onEnterDraw 1)
#guard !TriggeredAbility.requiresTarget .onEnterSearchForest
#guard !TriggeredAbility.requiresTarget .onAnotherElfYouControlEntersGets1
#guard !TriggeredAbility.requiresTarget (.onCastInstantOrSorceryDealDamageToEachOpponent 2)
#guard !TriggeredAbility.requiresTarget (.onAttackWithElvesScry 1)
#guard !TriggeredAbility.requiresTarget .onScryPumpSelfForEachLookedAt
#guard (TriggeredAbility.dividedDamage? (.onAttackWithElvesScry 1)).isNone
#guard (TriggeredAbility.dividedDamage? .onScryPumpSelfForEachLookedAt).isNone
#guard TriggeredAbility.resolution .onAttackPumpByGreatestPower ==
  .pump .greatestPower (.fixed 0) .source
#guard TriggeredAbility.resolution .onAttackSetOtherBasePT ==
  .setBasePT .equalSourcePower .equalSourceToughness
#guard TriggeredAbility.onAttackOtherGets2AndTrample.effect.body ==
  Instruction.pumpAndTrample (.target 0) 2 0
#guard TriggeredAbility.resolution (.onEnterScry 2) == .scry (.fixed 2)
#guard TriggeredAbility.resolution (.onEnterSurveil 2) == .surveil (.fixed 2)
#guard TriggeredAbility.resolutionPhrase { resolution? := some (.surveil .perOtherCreature) } ==
  "surveil"
#guard TriggeredAbility.resolutionPhrase { resolution? := some (.attach .source .source) } ==
  "attach it"
#guard TriggeredAbility.resolutionPhrase { body := Instruction.empowerJace 2 } ==
  "empower Jace 2"
#guard (TriggeredAbility.resolutionPhrase
    { body := Instruction.empower .jace (.aggregate .count .one (.inZones .battlefield (.all #[.otherThan .this, .hasType .creature, .controlledBy .you]))) }).startsWith
  "empower Jace"
#guard TriggeredAbility.resolutionPhrase
    { resolution? := some (.becomePT (.fixed 2) (.fixed 2)) } ==
  "you may have this creature's base power and toughness become 2/2 until end of turn"
#guard TriggeredAbility.resolutionPhrase
    { resolution? := some (.becomePT .perOtherCreature (.fixed 2)) } ==
  "you may have this creature's base power and toughness become those values until end of turn"
#guard TriggeredAbility.resolutionPhrase
    { resolution? := some (.lookAtTopRevealTypes .perOtherCreature #["Dwarf"]) } ==
  "look at the top cards of your library"
#guard TriggeredAbility.toNotation (.onEnterSurveil 1) ==
  "When this permanent enters, surveil 1."
#guard TriggeredAbility.toNotation (.onEnterEnchanted (fun o => Instruction.grantKeywords o #[Keyword.firstStrike])) ==
  "When this Aura enters, enchanted creature gains first strike until end of turn."
#guard TriggeredAbility.toNotation (.onEnterEnchanted Instruction.tap) ==
  "When this Aura enters, tap enchanted creature."
#guard (TriggeredAbility.onEnterEnchanted Instruction.tap).effect.body == Instruction.tap .attachedHost
#guard TriggeredAbility.toNotation (.onEnterAttachThen (fun o => Instruction.grantKeywords o #[Keyword.indestructible])) ==
  "When this Equipment enters, attach it to target creature you control. That creature gains indestructible until end of turn."
#guard TriggeredAbility.toNotation (.onEnterAttachThen Instruction.untap) ==
  "When this Equipment enters, attach it to target creature you control. Untap that creature."
#guard TriggeredAbility.targetSpec (.onEnterAttachThen Instruction.untap) == .creatureYouControl
#guard TriggeredAbility.toNotation .onEnterExileOtherCopyEnchanted ==
  "When this Aura enters, exile up to one target creature other than enchanted creature until this Aura leaves the battlefield. Enchanted creature becomes a copy of that creature until this Aura leaves the battlefield."
#guard TriggeredAbility.allowsZeroTargets .onEnterExileOtherCopyEnchanted
#guard TriggeredAbility.toNotation .onEnterExileCreatureReturnEndStep ==
  "When this Vehicle enters, exile up to one target creature you control. Return that card to the battlefield under its owner's control at the beginning of the next end step."
#guard TriggeredAbility.allowsZeroTargets .onEnterExileCreatureReturnEndStep
#guard TriggeredAbility.toNotation .onEnterTapOrUntapNonland ==
  "When this creature enters, choose one — • Tap target nonland permanent. • Untap target nonland permanent."
#guard TriggeredAbility.targetSpec .onEnterTapOrUntapNonland == .nonland
#guard TriggeredAbility.resolution .onEnterTapOrUntapNonland ==
  .or [.tap .target, .untap]
#guard TriggeredAbility.toNotation .onEnterCreateFoodOrTreasure ==
  "When this creature enters, create a Food token or a Treasure token."
#guard TriggeredAbility.resolution .onEnterCreateFoodOrTreasure ==
  .or [.createTokens 0 (.fixed 1) false, .createTokens 1 (.fixed 1) false]
#guard TriggeredAbility.resolution (.onEnter Effect.enterPlusOnesOrReturnArtEnch) ==
  .or [.putCounters (.ofKind .plusOnePlusOne) .permanent, .returnToHand .graveyardCard]
#guard TriggeredAbility.toNotation (.onEnter Effect.enterPlusOnesOrReturnArtEnch) ==
  "When this permanent enters, choose one — • Put a +1/+1 counter on each of up to two target creatures. • Return target artifact or enchantment card from your graveyard to your hand."
#guard TriggeredAbility.toNotation .onEnterVillainIfGyElseMill ==
  "When this creature enters, create a tapped 2/1 black Villain creature token with menace if there are two or more creature cards in your graveyard. Otherwise, mill two cards."
#guard TriggeredAbility.resolution .onEnterVillainIfGyElseMill ==
  .ifElse ((.atLeast (.count .creatureCardsInGraveyard) (.fixed 2)))
    (.createTokens 0 (.fixed 1) true) (.mill (.fixed 2))
#guard TriggeredAbility.toNotation .onEnterDrawMayPutLandTapped ==
  "When this creature enters, draw a card, then you may put a land card from your hand onto the battlefield tapped."
#guard TriggeredAbility.toNotation .onEnterDrawGainLifeIfAnotherHero ==
  "When this creature enters, draw a card. If you control another Hero, you gain 2 life."
#guard TriggeredAbility.toNotation .onEnterPlusOneOrTwoIfAnotherHero ==
  "When this creature enters, put a +1/+1 counter on target creature. If that creature is another Hero, put two +1/+1 counters on it instead."
#guard TriggeredAbility.resolution .onEnterPlusOneOrTwoIfAnotherHero ==
  .ifElse ((.atLeast (.count (.target (.anotherSubtype .hero))) (.fixed 1)))
    (.putCounters (.ofKind .plusOnePlusOne 2) .permanent)
    (.putCounters (.ofKind .plusOnePlusOne) .permanent)
#guard TriggeredAbility.targetSpec .onEnterPlusOneOrTwoIfAnotherHero == .creature
#guard TriggeredAbility.toNotation
    (SharedTrigger.pumpOrCounterIfScried.toTriggeredAbility (pattern? := some .stepYourBeginCombat)) ==
  "At the beginning of combat on your turn, another target creature you control gets +1/+1 until end of turn. If you've scried or surveilled this turn, put a +1/+1 counter on that creature instead."
#guard (SharedTrigger.toEffect .pumpOrCounterIfScried).resolution ==
  .ifElse (.or [.scriedThisTurn, .surveilledThisTurn])
    (.putCounters (.ofKind .plusOnePlusOne) .permanent) (.pump (.fixed 1) (.fixed 1) .target)
#guard TriggeredAbility.toNotation .onEnterMaySacArtifactOrDiscardDraw ==
  "When this creature enters, you may sacrifice an artifact or discard a card. If you do, draw a card."
#guard TriggeredAbility.toNotation .onEnterExileOppTappedUntilLeaves ==
  "When this enchantment enters, exile target tapped creature an opponent controls until this enchantment leaves the battlefield."
#guard TriggeredAbility.targetSpec .onEnterExileOppTappedUntilLeaves == .oppTappedCreature
#guard TriggeredAbility.resolution .onEnterExileOppTappedUntilLeaves ==
  .exile .target .untilSourceLeaves
#guard TriggeredAbility.toNotation (.onEnterTargetOpponentDiscards 2) ==
  "When this enchantment enters, target opponent discards two cards."
#guard TriggeredAbility.targetSpec (.onEnterTargetOpponentDiscards 2) == .opponent
#guard TriggeredAbility.toNotation (.onEnter (Effect.enterDestroy (.oppCreaturePowerAtMost 3))) ==
  "When this permanent enters, destroy target creature an opponent controls with power 3 or less."
#guard TriggeredAbility.targetSpec (.onEnter (Effect.enterDestroy (.oppCreaturePowerAtMost 3))) ==
  .oppCreaturePowerAtMost 3
#guard TriggeredAbility.toNotation (.onEnter (Effect.enterDealDamageUpToOne 4)) ==
  "When this permanent enters, it deals 4 damage to up to one target creature."
#guard TriggeredAbility.allowsZeroTargets (.onEnter (Effect.enterDealDamageUpToOne 4))
#guard TriggeredAbility.toNotation (.onEnter Effect.enterFightUpToOne) ==
  "When this permanent enters, this fights up to one other target creature."
#guard TriggeredAbility.targetSpec (.onEnter Effect.enterFightUpToOne) == .anotherCreature
#guard TriggeredAbility.toNotation (.onEnter Effect.enterCreateZabu) ==
  "When this permanent enters, create Zabu, a legendary 2/2 green Cat creature token with \"Landfall — Whenever a land you control enters, put a +1/+1 counter on Zabu.\"."
#guard TriggeredAbility.targetSpec (.onEnter Effect.enterOppCreatesTheVoid) == .opponent
#guard TriggeredAbility.resolution (.onEnter Effect.enterCreateSturdyShieldAttach) ==
  .sequence [.createTokens 0 (.fixed 1) false (note := .remember),
    .attach .createdToken .source]
#guard TriggeredAbility.targetSpec (.onEnter Effect.enterExileGyPlayUntilNextTurn) ==
  .equipmentInstantOrSorceryInYourGraveyard
#guard TriggeredAbility.targetSpec (.onEnter Effect.enterReturnGyPermanentThisTurn) ==
  .permanentCardInYourGraveyard
#guard TriggeredAbility.resolution (.onEnter Effect.enterTapOppCantUntapWhileControl) ==
  .sequence [.tap .target, .cant .untapWhileYouControl]
#guard TriggeredAbility.resolution (.onEnter Effect.enterMaySacAnotherThenDestroyOppNonland) ==
  .may (.pay CostSpec.sacrificeAnotherCreature) (.queueReflexive (.destroy .target)) .ifYouDo
#guard TriggeredAbility.resolution (.onEnterExileTop) == .exile .top .playUntilNextTurn
#guard StaticAbility.toNotation .noMaximumHandSize ==
  "You have no maximum hand size."
#guard StaticAbility.toNotation (.maximumHandSize 10) ==
  "Your maximum hand size is 10."
#guard StaticAbility.toNotation (.powerEqualSubtypeYouControl .merfolk) ==
  "This creature's power is equal to the number of Merfolk you control."
#guard KeywordAbility.toOracleStr { capitalize := true } (.simple .improvise) == "Improvise"
#guard StaticAbility.toNotation (.typeSpellsCostLess .artifact 1) ==
  "Artifact spells you cast cost {1} less to cast."
#guard StaticAbility.toNotation (.supertypeSpellsCostLess .legendary 1) ==
  "Legendary spells you cast cost {1} less to cast."
#guard StaticAbility.toNotation (.supertypeSpellsCostLess .snow 2) ==
  "Snow spells you cast cost {2} less to cast."
#guard StaticAbility.toNotation (.enchantedCreatureGetsHasAndTypes 2 2
    #[Keyword.firstStrike, Keyword.vigilance] #[.soldier]) ==
  "Enchanted creature gets +2/+2, has first strike and vigilance, and is a legendary Soldier in addition to its other types."
#guard StaticAbility.toNotation .enchantedLosesAbilitiesCantUntap ==
  "Enchanted creature loses all abilities and can't become untapped."
#guard StaticAbility.toNotation (.enchantedCreatureGetsHasAndWard 4 4 #[Keyword.trample] 1) ==
  "Enchanted creature gets +4/+4 and has trample and ward {1}."
#guard StaticAbility.toNotation (.getsAndAllTypesIfGyCreatureCards 2 2 2) ==
  "As long as there are 2 or more creature cards in your graveyard, this creature gets +2/+2 and is all creature types."
#guard KeywordAbility.toOracleStr { capitalize := true } (.sneak (CostSpec.ofMana (ManaCost.ofGenericAndColors 1 [.black, .black]))) ==
  "Sneak {1}{B}{B}"
#guard ActivatedAbility.zemoBoastAbility.printed ==
  "Boast — Exile any number of black cards from your graveyard with fifteen or more black mana symbols among their mana costs: Copy those exiled cards. You may cast up to three of the copies without paying their mana costs."
#guard TriggeredAbility.resolution (.onAttackScry 1) == .scry (.fixed 1)
#guard TriggeredAbility.resolution (.onAttackFerociousGainLife 2) == .gainLife (.fixed 2)
#guard (TriggeredAbility.onAttackFerociousGainLife 2).pattern ==
  .whenCond .thisAttacks (TriggeredAbility.condControlCreaturePowerAtLeast 4)
#guard (TriggeredAbility.onAttackScry 1).pattern == .thisAttacks
#guard TriggeredAbility.resolution (.onAttackWithElvesScry 1) == .scry (.fixed 1)
#guard TriggeredAbility.resolution (.onEnterDraw 1) == .draw (.fixed 1)
#guard TriggeredAbility.resolution .onEnterSearchForest ==
  .searchLibrary (.put .forest)
#guard TriggeredAbility.resolution .onEnterSearchBasicToHand ==
  .searchLibrary (.returnToHand .basicLand)
#guard TriggeredAbility.resolution (.onOpponentCastsAmassOrcs 1) == .amass (.fixed 1) .orc
#guard TriggeredAbility.resolution .onDiesAmassGoblinsEqualPower ==
  .amass .lastKnownPower
#guard TriggeredAbility.resolution (.onEnterAmassThenAttach 1) ==
  .amass (.fixed 1) (attachSource := true)
#guard TriggeredAbility.resolutionPhrase { resolution? := some (.amass .perOtherCreature) } ==
  "amass"
#guard TriggeredAbility.resolution .onOpponentCastsFirstNoncreatureRecruit == .recruit .you
#guard TriggeredAbility.resolution .onEnterRecruit == .recruit
#guard TriggeredAbility.onCombatDamageToPlayerLoot.effect.body ==
  .seq #[Instruction.drawFixed 1, Instruction.discardFixed 1]
#guard TriggeredAbility.resolution .onEnterEachOpponentDiscards ==
  .discard (.cards 1 .eachOpponent)
#guard TriggeredAbility.resolution (.onEnterTargetOpponentDiscards 2) ==
  .discard (.cards 2 (.target .opponent))
#guard TriggeredAbility.resolution .onAttackFerociousPlusOneEach ==
  .putCounters (.ofKind .plusOnePlusOne) .youControl
#guard TriggeredAbility.resolution .onEnterCreateAxe ==
  .createTokens 0 (.fixed 1) false
#guard TriggeredAbility.resolution .onEnterCreateAxeAttach ==
  .createTokens 0 (.fixed 1) false (note := .attachReflexive)
#guard TriggeredAbility.resolution .onEquippedAttacksPlusOneEachIfCityBlessing ==
  .putCounters (.ofKind .plusOnePlusOne) (.youControl .citysBlessing)
#guard TriggeredAbility.resolution
    (.onStep (Effect.ofTrigger .prepareSource)) == .prepareSource
#guard TriggeredAbility.resolution
    (.onStep (Effect.ofTrigger (.prepareSource .ifThreeCreaturesDied))) ==
  .prepareSource .ifThreeCreaturesDied
#guard ((SharedTrigger.mayPayGenericDraw 2 (plusOneOnSource := true)).toTriggeredAbility
    (pattern? := some .youScryOrSurveil)).resolution ==
  .may (.pay (CostSpec.ofGeneric 2)) (.sequence [.putCounters (.ofKind .plusOnePlusOne) .source, .draw (.fixed 1)]) .ifYouDo
#guard TriggeredAbility.toNotation .onEnterCreateAxe ==
  "When this permanent enters, create a colorless Equipment artifact token named Axe with \"Equipped creature gets +1/+0\" and equip {2}."
#guard TriggeredAbility.toNotation .onEnterCreateAxeAttach ==
  "When Dáin enters, create a colorless Equipment artifact token named Axe with \"Equipped creature gets +1/+0\" and equip {2}. When you do, attach it to target creature you control."
#guard TriggeredAbility.toNotation .onEquippedAttacksPlusOneEachIfCityBlessing ==
  "Whenever equipped creature attacks, put a +1/+1 counter on each creature you control. If you have the city's blessing, put two +1/+1 counters on each creature you control instead."
#guard TriggeredAbility.toNotation (.onStep (Effect.ofTrigger .prepareSource)) ==
  "At the beginning of your upkeep, if this creature isn't prepared, it becomes prepared."
#guard TriggeredAbility.toNotation
    (.onStep (Effect.ofTrigger (.prepareSource .ifThreeCreaturesDied))) ==
  "At the beginning of each end step, if three or more creatures died this turn, this creature becomes prepared."
#guard TriggeredAbility.toNotation
    ((SharedTrigger.mayPayGenericDraw 2 (plusOneOnSource := true)).toTriggeredAbility
      (pattern? := some .youScryOrSurveil)) ==
  "Whenever you scry or surveil, you may pay {2}. If you do, put a +1/+1 counter on this creature and draw a card."
#guard TriggeredAbility.toNotation
    (.onAnotherCreatureYouControlPowerAtMostEntersMayPayDraw 2 1) ==
  "Whenever another creature you control with power 2 or less enters, you may pay {1}. If you do, draw a card."
#guard TriggeredAbility.onAttackWithTwoOrMoreGrantFlying.effect.body ==
  Instruction.grantKeywords (.target 0) #[Keyword.flying]
#guard TriggeredAbility.toNotation (.onOpponentCastsAmassOrcs 1) ==
  "Whenever an opponent casts a spell, amass Orcs 1."
#guard TriggeredAbility.toNotation .onDiesAmassGoblinsEqualPower ==
  "When this creature dies, amass Goblins X, where X is this creature's power."
#guard TriggeredAbility.toNotation (.onEnterAmassThenAttach 1) ==
  "When this permanent enters, amass Goblins 1, then attach this Equipment to the amassed Army."
#guard TriggeredAbility.toNotation .onOpponentCastsFirstNoncreatureRecruit ==
  "Whenever an opponent casts their first noncreature spell each turn, you recruit."
#guard TriggeredAbility.toNotation .onCombatDamageToPlayerLoot ==
  "Whenever this deals combat damage to a player, draw a card, then discard a card."
#guard TriggeredAbility.toNotation .onYourEndStepDrawLoseLife ==
  "At the beginning of your end step, you draw a card and lose 1 life."
#guard TriggeredAbility.toNotation .onEquippedAttacksAloneDrawLoseLife ==
  "Whenever equipped creature attacks alone, you draw a card and you lose 1 life."
#guard TriggeredAbility.toNotation .onYouAttackFerociousDrawLoseLife ==
  "Whenever you attack while you control a creature with power 4 or greater, you draw a card and lose 1 life."
#guard TriggeredAbility.toNotation .onCastWithTreasureDrawLoseLife ==
  "Whenever you cast a spell, if mana from a Treasure was spent to cast it, you draw a card and lose 1 life."
#guard TriggeredAbility.toNotation (.onAttackFerociousSourceGetsAndTeamTrample 1) ==
  "Whenever this creature attacks while you control a creature with power 4 or greater, until end of turn, this creature gets +1/+0 and creatures you control gain trample."
#guard TriggeredAbility.toNotation .onDrawSecondPlusOneLifelink ==
  "Whenever you draw your second card each turn, put a +1/+1 counter on target creature. It gains lifelink until end of turn."
#guard TriggeredAbility.toNotation (.onAnotherLegendarySubtypeEntersLoot "Elf") ==
  "Whenever another legendary Elf you control enters, draw two cards, then discard a card."
#guard TriggeredAbility.toNotation .onScryPumpAndUnblockableOnce ==
  "Whenever you scry, this gets +1/+0 until end of turn and can't be blocked this turn. This ability triggers only once each turn."
#guard TriggeredAbility.toNotation .onLandYouControlEntersPlusOneVigilance ==
  "Whenever a land you control enters, put 2 +1/+1 counters on target creature you control. It gains vigilance until end of turn."
#guard TriggeredAbility.toNotation .onLandYouControlEntersDrawPlusOneSource ==
  "Landfall — Whenever a land you control enters, draw a card and put a +1/+1 counter on Gandalf."
#guard TriggeredAbility.toNotation (.onEnterCreaturesYouControlGetAndFirstStrike 1) ==
  "When this permanent enters, creatures you control get +1/+0 and gain first strike until end of turn."
#guard TriggeredAbility.toNotation .onTappedForTeamworkPlusOneAndDraw ==
  "Whenever this becomes tapped to pay a teamwork cost, put a +1/+1 counter on this and draw a card."
#guard TriggeredAbility.toNotation .onEnterSearchBasicToHand ==
  "When this permanent enters, search your library for a basic land card, reveal it, put it into your hand, then shuffle."
#guard TriggeredAbility.toNotation .onAttackWithTwoOrMoreGrantFlying ==
  "Whenever two or more creatures you control attack a player, target attacking creature without flying gains flying until end of turn."
#guard TriggeredAbility.resolution .onEnterTargetOpponentSacrificesCreature ==
  .sacrifice .opponentChosenCreature
#guard (TriggeredAbility.onLandYouControlEntersGets 1 1).effect.body ==
  Instruction.pumpFixed .this 1 1
#guard TriggeredAbility.onLandYouControlEntersPlusOnePlusOne.effect.body ==
  Instruction.putPlusOne (.target 0) 1
#guard TriggeredAbility.onAnotherElfYouControlEntersGets1.effect.body ==
  Instruction.pumpFixed .this 1 1
#guard TriggeredAbility.resolution (.onEnterDealDividedDamage 3 3) == .dividedDamage
#guard TriggeredAbility.resolution (.onEnterOrAttackDealDividedDamage 3 3) ==
  .dividedDamage
#guard TriggeredAbility.resolution .onDiesDealDamageEqualToPowerToOppCreature ==
  .dealDamage .lastKnownPower .permanent
#guard TriggeredAbility.resolution (.onCastInstantOrSorceryDealDamageToEachOpponent 2) ==
  .dealDamage (.fixed 2) (.player .eachOpponent)
#guard
  let instant : CardDef := { name := "Silent Bolt", types := #[.instant] }
  let sorcery : CardDef := { name := "Silent Flame", types := #[.sorcery] }
  let creature : CardDef := { name := "Silent Ogre", types := #[.creature] }
  instant.isInstantOrSorcery && sorcery.isInstantOrSorcery && !creature.isInstantOrSorcery

end CardDef

#guard
  let adv : AdventureFace := {
    name := "Spew Flame"
    manaCost := ManaCost.ofGenericAndColor 4 .red
    spellEffect := some (Effect.dealDamageToCreature 5)
  }
  let c := adv.toCardDef
  c.name == "Spew Flame" && c.isSorcery && c.requiresTarget &&
    c.hasSubtype .adventure

#guard
  let adv : AdventureFace := {
    name := "Till and Tend"
    manaCost := ManaCost.ofGenericAndColor 1 .green
    spellEffect := some (Effect.playAdditionalLandThisTurn)
  }
  let c := adv.toCardDef
  c.name == "Till and Tend" && c.isSorcery && !c.requiresTarget &&
    c.hasSubtype .adventure

#guard TriggeredAbility.resolution .onTokenYouControlEntersBelladonna ==
  .sequence [
    .noteResolveThisTurn 3,
    .«if» (.nthResolve 1) (.gainLife (.fixed 1)),
    .«if» (.nthResolve 2) (.draw (.fixed 1)),
    .«if» (.nthResolve 3) (.putCounters (.ofKind .plusOnePlusOne) .youControl)]
#guard TriggeredAbility.resolution .onBolgDealSacrificedPower ==
  .sequence [.dealDamage .lastKnownPower .permanent .excess,
    .amass .notedExcess]
#guard TriggeredAbility.resolution .onEquippedAttacksCreateSpirits ==
  .sequence [.createTokens 0 (.fixed 2) true, .«if» (.atLeast (.count (.intersection [.equipped, .legendaryCreaturesYouControl])) (.fixed 1)) .markRecentTokensAttacking]
#guard TriggeredAbility.resolution .onEnterOrOpponentDrawsDeal1AmassOrcs ==
  .sequence [.dealDamage (.fixed 1) .target .markedPermanent, .amass (.fixed 1) .orc]
#guard TriggeredAbility.resolution (.onAttackWithTotalPowerUntapExtraCombat 10) ==
  .sequence [.untap .attackingCreatures, .additionalCombatPhase]
#guard TriggeredAbility.resolution .onEnterDestroyOtherAmassControllerPower ==
  .sequence [.destroy .target (note := .forAmass),
    .amass .notedPower (who := .controller .target),
    .«if» .youControlledDestroyed (.draw (.fixed 1))]
#guard TriggeredAbility.resolution (.onThisOrAnotherSubtypeEntersDiscardHand "Dwarf") ==
  .sequence [.may (.discard .hand) (.sequence []), .draw .discardedHand,
    .«if» .enduringStoryNoted (.dealDamage .discardedHand (.player .eachOpponent))]
#guard TriggeredAbility.resolution .onYourBeginCombatTrampleCounterBecomeBear ==
  .sequence [.putCounters (.ofKind .trample) .permanent, .becomeBear,
    .«if» ((.atLeast (.count (.youControl (.subtype .bear))) (.fixed 3))) (.draw (.fixed 2))]
#guard TriggeredAbility.resolution .onEnterLootLandEntersTapped ==
  .sequence [.draw (.fixed 1), .discard (.cards 1), .put .discardedLand (how := .tapped)]
#guard TriggeredAbility.resolution (.onEnterMillThenSubtypeToHand 4 "Elf") ==
  .sequence [.mill (.fixed 4) (note := .milledCards), .returnToHand (.milledSubtype .elf)]
#guard TriggeredAbility.resolution .onEnterTapEnchantedRemoveCounters ==
  .sequence [.tap .enchanted, .removeCounters .all .enchanted]
#guard TriggeredAbility.resolution .onYourEndStepPalantir ==
  .sequence [.putCounters (.ofKind .influence) .source, .scry (.fixed 2),
    .may (.draw (.fixed 1) (who := .opponentHasYou)) (.sequence [])]
#guard TriggeredAbility.resolution .onCombatDamageToYouSacRingTempts ==
  .sequence [.sacrifice .combatDamager, .ringTempts]
#guard TriggeredAbility.resolution (.onCreatureYouControlEntersScryAndPlan 2) ==
  .sequence [.putCounters (.ofKind .plan) .source, .scry (.fixed 2)]
#guard TriggeredAbility.resolution .onLandYouControlEntersPlusOneAndPlan ==
  .sequence [.putCounters (.ofKind .plan) .source,
    .putCounters (.ofKind .plusOnePlusOne) (.permanent true)]
#guard TriggeredAbility.resolution .onFourthPlanDrawPlusOneEach ==
  .sequence [.sacrifice .plan, .draw (.fixed 1), .putCounters (.ofKind .plusOnePlusOne) .youControl]
#guard TriggeredAbility.resolution .onFourthPlanReturnInstants ==
  .sequence [.sacrifice .plan .forReflexive,
    .«if» .planWasSacrificed (.queueReflexive (.returnToHand (.graveyardInstants 2)))]
#guard TriggeredAbility.resolution .onFourthPlanDividedDamage ==
  .sequence [.sacrifice .plan .forReflexive,
    .«if» .planWasSacrificed (.queueReflexive (.dealDamage (.fixed 7) .target .divided))]
#guard TriggeredAbility.resolution .onEnterDrawMayPutLandTapped ==
  .sequence [.draw (.fixed 1), .may (.put .landFromHand (how := .tapped)) (.sequence [])]
#guard TriggeredAbility.resolution .onEnterDrawGainLifeIfAnotherHero ==
  .sequence [.draw (.fixed 1), .«if» (.atLeast (.count (.othersOfSubtype .hero)) (.fixed 1)) (.gainLife (.fixed 2))]
#guard TriggeredAbility.resolution .onCombatCreateAlienPerInvasion ==
  .sequence [.createTokens 0 (.fixed 1) false (note := .invasion),
    .putCounters .plusOneNoted .createdToken,
    .putCounters (.ofKind .invasion) .source]
#guard (SharedTrigger.toEffect .drawTwoWinIfEmptyShuffleSource).resolution ==
  .sequence [.draw (.fixed 2), .«if» (.not (.atLeast .libraryCards (.fixed 1))) .winTheGame, .«if» (.atLeast .libraryCards (.fixed 1)) .shuffleSource]
#guard (SharedTrigger.toEffect .surveilReturnIfGainedLife).resolution ==
  .sequence [.armSurveilReturnLifeGained, .surveil (.fixed 1)]
#guard (SharedTrigger.toEffect (.grantThenCounterByType #[Keyword.hexproof])).resolution ==
  .sequence [.grant (.keywords #[Keyword.hexproof]) .target,
    .«if» (.atLeast (.count (.target .creature)) (.fixed 1)) (.putCounters (.ofKind .plusOnePlusOne) .permanent),
    .«if» (.atLeast (.count (.target .planeswalker)) (.fixed 1)) (.putCounters (.ofKind .loyalty) .permanent)]
#guard (SharedTrigger.toEffect .beginCombatIfDrawnTwoPump).resolution ==
  .«if» (.atLeast .cardsDrawnThisTurn (.fixed 2)) (.sequence [
    .pump (.fixed 3) (.fixed 0) .target,
    .grant (.keywords #[Keyword.firstStrike]) .target])
#guard (SharedTrigger.toEffect .destroyOppPermanentIfSixLands).resolution ==
  .«if» ((.atLeast (.count .landsYouControl) (.fixed 6))) (.sequence [
    .destroy .target,
    .createTokens 0 (.fixed 1) false (who := .controller .target)])
#guard TriggeredAbility.toNotation
    (SharedTrigger.destroyOppPermanentIfSixLands.toTriggeredAbility (pattern? := some .thisEnters)) ==
  "When this permanent enters, if you control six or more lands, destroy target permanent an opponent controls. They create a Treasure token."
#guard TriggeredAbility.toNotation .onYourBeginCombatIfDrawnTwoPumpFirstStrike ==
  "At the beginning of combat on your turn, if you've drawn two or more cards this turn, another target creature you control gets +3/+0 and gains first strike until end of turn."
#guard (SharedTrigger.toEffect (.drawXDiscard 2)).resolution ==
  .sequence [.draw .equalToManaSpent, .«if» .manaSpent (.discard (.cards 2))]
#guard TriggeredAbility.resolution .onDiesDrawPerFatGraveyard ==
  .draw .perFatGraveyard
#guard (SharedTrigger.toEffect (.enter .createSturdyShieldAttach)).resolution ==
  .sequence [.createTokens 0 (.fixed 1) false (note := .remember),
    .attach .createdToken .source]
#guard (SharedTrigger.toEffect (.enter .tapLoseAbilitiesWhileSource)).resolution ==
  .sequence [.tap (.target .ifPresent), .lose .allAbilities (.target .ifPresent)]
#guard TriggeredAbility.toNotation .onTokenYouControlEntersBelladonna ==
  "Whenever a token you control enters, you gain 1 life if this is the first time this ability has resolved this turn. If it's the second time, draw a card. If it's the third time, put a +1/+1 counter on each creature you control."
#guard TriggeredAbility.toNotation .onActivateCreatureAbilityDrawOnce ==
  "Whenever you activate an ability of a creature, draw a card. This ability triggers only once each turn."
#guard TriggeredAbility.resolution .onYourBeginCombatCastInstantSorceryFromHand ==
  .mayCast .hand .twiceLegendaryWizards .withoutPaying
#guard TriggeredAbility.resolution .onEquippedCombatDamageCastInstantSorcery ==
  .mayCast .hand .lastKnown .withoutPaying
#guard TriggeredAbility.resolution .onAttackCastFromGyArtifactInstantSorcery ==
  .mayCast .graveyard .unlimited .pay .exileInstead
#guard TriggeredAbility.resolution .onCombatDamageImpulseInstantSorcery ==
  .sequence [.revealLibrary .untilInstantOrSorcery (.exile .top .forLater .impulse) .damagedPlayer,
    .mayCast .impulse .unlimited .withoutPaying]
#guard TriggeredAbility.toNotation .onYourBeginCombatCastInstantSorceryFromHand ==
  "At the beginning of combat on your turn, you may cast an instant or sorcery spell with mana value X or less from your hand without paying its mana cost, where X is twice the number of legendary Wizards you control."
#guard TriggeredAbility.toNotation .onEquippedCombatDamageCastInstantSorcery ==
  "Whenever equipped creature deals combat damage to a player, you may cast an instant or sorcery spell from your hand with mana value less than or equal to that damage without paying its mana cost."
#guard TriggeredAbility.toNotation .onAttackCastFromGyArtifactInstantSorcery ==
  "Whenever Bilbo attacks, you may cast an artifact, instant, or sorcery spell from your graveyard. If an instant or sorcery spell cast this way would be put into your graveyard, exile it instead."
#guard TriggeredAbility.toNotation .onCombatDamageImpulseInstantSorcery ==
  "Whenever Gríma deals combat damage to a player, that player exiles cards from the top of their library until they exile an instant or sorcery card. You may cast that card without paying its mana cost. Then that player puts the exiled cards that weren't cast this way on the bottom of their library in a random order."
#guard TriggeredAbility.firesOn .onTokenYouControlEntersBelladonna .tokenYouControlEnters
#guard TriggeredAbility.firesOn .onActivateCreatureAbilityDrawOnce .youActivateCreatureAbility
#guard TriggeredAbility.onceEachTurn .onActivateCreatureAbilityDrawOnce
#guard
  let c : CardDef := {
    name := "Smaug, the Great Calamity"
    types := #[.creature]
    adventure := some {
      name := "Spew Flame"
      manaCost := ManaCost.ofGenericAndColor 4 .red
      spellEffect := some (Effect.dealDamageToCreature 5)
    }
  }
  c.choosableNames == #["Smaug, the Great Calamity", "Spew Flame"]

-- Phase 1 foundation `#guard`s: Primitives, ManaSpec, TokenSpec, and HasTextChange.
#guard Zone.battlefield.kind == .battlefield
#guard (Zone.hand ⟨0⟩).kind == .hand
#guard (Zone.graveyard ⟨1⟩).kind == .graveyard
#guard (Zone.library ⟨0⟩).kind == .library
#guard Zone.stack.kind == .stack
#guard Zone.exile.kind == .exile
#guard Zone.command.kind == .command
#guard (Zone.outside ⟨0⟩).kind == .outside
#guard ZoneKind.hand.toZone ⟨2⟩ == .hand ⟨2⟩
#guard ZoneKind.battlefield.isPublic && !ZoneKind.hand.isPublic && ZoneKind.library.isHidden
#guard ZoneKind.graveyard.isOwned && !ZoneKind.exile.isOwned
#guard (PermanentDesignation.goaded ⟨0⟩).tag == .goaded
#guard PermanentDesignation.ringBearer.tag == .ringBearer
#guard ReplacementTier.self.rank < ReplacementTier.control.rank
#guard ReplacementTier.control.rank < ReplacementTier.copy.rank
#guard ReplacementTier.copy.rank < ReplacementTier.backFaceUp.rank
#guard ReplacementTier.backFaceUp.rank < ReplacementTier.auraHost.rank
#guard ReplacementTier.auraHost.rank < ReplacementTier.other.rank

-- Layer 4 `TypeSetMod.apply` and Layer 5 `ColorSetMod.apply` (CR 205.1a–b / 205.3d / 613.1d–e).
#guard
  let m : TypeSetMod := { mode := .add, types := #[.artifact], removeTypes := #[.creature] }
  m.apply #[.creature] #[.elf, .warrior] #[] == (#[.artifact], #[], #[])
#guard
  let m : TypeSetMod := { mode := .add, removeTypes := #[.creature] }
  m.apply #[.kindred, .creature] #[.elf] #[] == (#[.kindred], #[.elf], #[])
#guard
  let m : TypeSetMod := { mode := .add, types := #[.artifact], removeTypes := #[.creature] }
  m.apply #[.artifact, .creature] #[.construct, .food] #[] == (#[.artifact], #[.food], #[])
#guard
  let m : TypeSetMod := { mode := .set, types := #[.artifact], subtypes := #[.food] }
  m.apply #[.creature] #[.bear] #[.legendary] == (#[.artifact], #[.food], #[.legendary])
#guard
  let m : ColorSetMod := { mode := .add, colors := ColorSet.singleton .red, removeColors := ColorSet.singleton .green }
  m.apply (ColorSet.singleton .green) == ColorSet.singleton .red

-- `ManaSpec` / `ManaOutput` / `ManaSpendRestriction` (CR 106.1 / 106.6 / 106.12).
#guard (ManaSpec.ofOutput (.fixed #[.colored .red, .colored .red])).toConstantOutput? ==
  some (.fixed #[.colored .red, .colored .red])
#guard (ManaSpec.ofOutput (.oneOf anyColorMana 2)).toConstantOutput? ==
  some (.oneOf anyColorMana 2)
#guard (ManaSpec.ofOutput (.combination #[.colored .blue, .colored .red] 2)).toConstantOutput? ==
  some (.combination #[.colored .blue, .colored .red] 2)
#guard ManaSpendRestriction.parseOracle? "Dwarf, Equipment, and Saga spells" ==
  some .dwarfEquipmentSagaSpell
#guard ManaSpendRestriction.parseOracle? "Dragon spells" == some .dragonSpell
#guard ManaSpendRestriction.parseOracle? "a Goblin spell" == some (.subtypeSpell .goblin)
#guard ManaSpendRestriction.legendarySpell.grantsRider .cantBeCountered
#guard !ManaSpendRestriction.dragonSpell.grantsRider .cantBeCountered
#guard ManaSpendRestriction.elf.isNarrow && !ManaSpendRestriction.cantNonartifact.isNarrow
#guard !ManaSpendRestriction.notSpellsFromHand.isNarrow
#guard ManaSpendRestriction.legendarySpell.allows { spell := true, supertypes := #[.legendary] }
#guard !ManaSpendRestriction.legendarySpell.allows { spell := true, supertypes := #[] }
#guard ManaSpendRestriction.cantNonartifact.allows { spell := true, types := #[.artifact] }
#guard !ManaSpendRestriction.cantNonartifact.allows { spell := true, types := #[.creature] }
#guard ManaSpendRestriction.cantNonartifact.allows { spell := false }
#guard ManaSpendRestriction.creatureSource.allows { spell := false, abilitySourceTypes := #[.creature] }
#guard !ManaSpendRestriction.creatureSource.allows { spell := true, types := #[.creature] }
#guard ManaSpendRestriction.notSpellsFromHand.allows { spell := true, fromHand := false }
#guard !ManaSpendRestriction.notSpellsFromHand.allows { spell := true, fromHand := true }
#guard !ManaSpendRestriction.notSpellsFromHand.allows { spell := true, castFromZone := some .hand }
#guard ManaSpendRestriction.notSpellsFromHand.allows { spell := true, castFromZone := some .graveyard }
#guard !(ManaSpendRestriction.notFromZone .graveyard).allows { spell := true, castFromZone := some .graveyard }
#guard (ManaSpendRestriction.notFromZone .graveyard).allows { spell := true, castFromZone := some .exile }
#guard (ManaSpendRestriction.notFromZone .graveyard).allows { spell := true, fromHand := true, castFromZone := some .hand }
#guard (ManaSpendRestriction.notFromZone .graveyard).allows { spell := false, castFromZone := some .graveyard }
#guard !(ManaSpendRestriction.notFromZone .exile).allows { spell := true, castFromZone := some .exile }
#guard (ManaSpendRestriction.notFromZone .exile).allows { spell := true, castFromZone := some .graveyard }

-- `HasTextChange` identity, composition, and token/mana/ability traversal (CR 612.2 / 613.1c).
#guard
  let tcs : Array TextChange := #[.replaceCreatureType .dwarf .bear, .replaceColorWord .red .blue]
  HasTextChange.applyTextChanges #[] ManaSpendRestriction.dwarfEquipmentSagaSpell ==
    ManaSpendRestriction.dwarfEquipmentSagaSpell &&
  HasTextChange.applyTextChanges tcs ManaSpendRestriction.dwarfEquipmentSagaSpell ==
    .subtypeEquipmentSagaSpell .bear &&
  HasTextChange.applyTextChanges tcs TokenSpec.dwarf ==
    TokenSpec.creature #[.bear] 2 2 (ColorSet.singleton .blue) &&
  HasTextChange.applyTextChanges tcs (TokenSpec.copyOf .target #[.addSubtypes #[.dwarf], .addColors (ColorSet.singleton .red)]) ==
    TokenSpec.copyOf .target #[.addSubtypes #[.bear], .addColors (ColorSet.singleton .blue)] &&
  HasTextChange.applyTextChanges tcs (Instruction.createTokensFixed .dwarf 2) ==
    Instruction.createTokensFixed (TokenSpec.creature #[.bear] 2 2 (ColorSet.singleton .blue)) 2 &&
  HasTextChange.applyTextChanges #[] (StaticAbility.otherCreaturesGet #[.elf] 1 1) ==
    StaticAbility.otherCreaturesGet #[.elf] 1 1 &&
  HasTextChange.applyTextChanges #[.replaceCreatureType .elf .goblin]
    (StaticAbility.otherCreaturesGet #[.elf] 1 1) ==
    StaticAbility.otherCreaturesGet #[.goblin] 1 1

-- Phase 2: Pure Expression Algebra (`Expr`), generalized `ManaSpec` & `TokenSpec`,
-- `ToOracle`, and Stage-4 Sub-Grammar Parsers (CR 106, 107, 111, 611, 612).
#guard ValueExpr.evalConst? 5 (.binary .add (.const 2) .chosenX) == some 7
#guard ValueExpr.evalConst? 0 (.binary .max (.const (-3)) (.const 0)) == some 0
#guard ValueExpr.evalConst? 0 (.binary .divFloor (.const 7) (.const 2)) == some 3
#guard ValueExpr.evalConst? 0 (.binary .min (.const 7) (.const 2)) == some 2
#guard ValueExpr.evalConst? 0 (.playerMetric .life .you) == none
#guard CmpOp.ge.eval 4 4 && !CmpOp.gt.eval 4 4 && CmpOp.le.eval 3 4 && CmpOp.ne.eval 3 4
#guard
  let tcs : Array TextChange := #[.replaceCreatureType .elf .goblin, .replaceColorWord .green .red]
  let objs : ObjectExpr :=
    .inZones .battlefield
      (.all #[.hasSubtype (.literal .elf), .hasColor (.literal .green), .controlledBy .you])
  let spec : ManaSpec := .sequence #[(ManaType.colored .green, .count objs)]
  HasTextChange.applyTextChanges tcs spec ==
    .sequence #[(ManaType.colored .green,
      .count (.inZones .battlefield
        (.all #[.hasSubtype (.literal .goblin), .hasColor (.literal .red), .controlledBy .you])))]
#guard
  let tcs : Array TextChange := #[.replaceCreatureType .elf .goblin]
  let tok : TokenSpec := .custom {
    subtypes := #[.elf]
    power? := some (.count (.inZones .battlefield (.hasSubtype (.literal .elf))))
    toughness? := some (.const 1)
  }
  HasTextChange.applyTextChanges tcs tok == .custom {
    subtypes := #[.goblin]
    power? := some (.count (.inZones .battlefield (.hasSubtype (.literal .goblin))))
    toughness? := some (.const 1)
  }
#guard
  let s : ManaSpec := .oneOf (.commanderColorIdentity .you) (.const 1)
  toOracleStr s == "one mana of any color in your commander's color identity"
#guard
  let s : ManaSpec := .sequence #[(ManaType.colored .green,
    .count (.inZones .battlefield (.all #[.hasSubtype (.literal .elf), .controlledBy .you])))]
  toOracleStr s == "{G} for each Elf you control"
#guard
  (Parser.parseNounPhrase "target untapped red Elf creature you control").map (·.isTarget) ==
    some true
#guard
  Parser.parseValueExpr "the number of Elves you control" ==
    some (.aggregate .count .one
      (.inZones .battlefield (.all #[.hasSubtype (.literal .elf), .controlledBy .you])))
#guard
  Parser.parseCondition "you control three or more artifacts" ==
    some (.cmp .ge
      (.aggregate .count .one
        (.inZones .battlefield (.all #[.hasType .artifact, .controlledBy .you])))
      (.const 3))
#guard
  Parser.parseDuration "until end of turn" == some .untilEndOfTurn
#guard
  Parser.parseDuration "until this enchantment leaves the battlefield" ==
    some (.untilLeavesBattlefield .this)
#guard
  Parser.parseDuration "for as long as it remains exiled" ==
    some (.whileInZone .this .exile)

-- Phase 3: Unified `TargetSpec`, `ToOracle`, `HasTextChange`, and compositional `parseTargetSpec`.
#guard
  let specs : Array TargetSpec := #[
    .creature, .creatureYouControl, .anotherCreatureYouControl, .anotherCreature,
    .anyTarget, .anyOtherTarget, .player, .opponent, .oppCreature, .oppTappedCreature,
    .creatureWithFlying, .artifactOrLand, .colorlessNonland, .artifactOrEnchantment,
    .artifactOrCreatureYouControl, .nonland, .oppNonland, .attackingCreatureWithoutFlying,
    .creatureYouControlSubtype .elf, .creatureYouControlAnySubtype #[.goblin, .orc],
    .creatureYouControlAnySubtype #[.bear, .spider, .wolf],
    .spell, .creatureSpell, .creatureSpellPTAtMost 3, .defendingPlayerCreature,
    .creaturePowerAtLeast 4, .creaturePowerAtMost 2, .creatureYouControlPowerAtMost 3,
    .anotherCreatureYouControlPowerAtMost 2, .oppCreaturePowerAtMost 3,
    .permanent, .permanentYouControl, .oppPermanent, .legendaryCreatureYouControl,
    .artifact, .oppArtifact, .artifactYouControl, .artifactToken, .land,
    .attackingCreature, .attackingOrBlockingCreature, .attackingAloneCreatureYouControl,
    .equipmentYouControl, .creatureOrLandYouControl, .creatureMvAtMost 3,
    .creatureToughnessAtLeast 4, .enchantmentMvAtLeast 3, .noncreatureArtifact,
    .noncreatureArtifactOrEnchantment, .oppCreatureDealtDamageThisTurn,
    .nonlandNontoken, .creatureOrPlaneswalker, .planeswalkerYouControl,
    .oppCreatureOrPlaneswalker, .worthyCreatureYouControl, .elfInYourGraveyard,
    .oppGraveyardCard, .creatureCardInYourGraveyard, .creatureCardInYourGraveyardMvAtMost 3,
    .permanentCardInYourGraveyard, .equipmentInstantOrSorceryInYourGraveyard,
    .artEnchCardInYourGraveyard, .creatureOrGyCreatureCard, .spellOrCreature,
    .permanentOrPlayer, .stackAbilityFromSource .artifact,
    .twoNonlandsSharingType, .twoCreaturesOrLandsYouControl, .twoPlayers,
    .twoArtifactsYouControl, .upToTwoCreaturesTotalMvAtMost 4,
    .playerThenCreature, .creatureYouControlThenOppCreature,
    .oppCreatureThenUpToOneCreatureYouControl, .equipmentYouControlThenCreatureYouControl,
    .upToOneEquipmentThenCreatureYouControl, .upToOneCreatureThenPlayer,
    .creatureYouControlThenOppCreatureOrPlaneswalker,
    .planeswalkerYouControlThenOppCreatureOrPlaneswalker,
    .forEachOpponentControlled (.not (.hasType .land)) (.upTo 1),
    .forEachPlayerControlled (.hasType .creature) (.upTo 1)
  ]
  specs.all fun ts => Parser.parseTargetSpec ts.noun == some ts

-- Phase 3: Layer-3 `HasTextChange` transforms `TargetSpec` and updates rendered `ToOracle` wording.
#guard
  let ts := TargetSpec.creatureYouControlSubtype .elf
  let changed := HasTextChange.applyTextChanges #[.replaceCreatureType .elf .bear] ts
  changed == TargetSpec.creatureYouControlSubtype .bear &&
    changed.noun == "target Bear you control"
#guard
  let ts : TargetSpec := .single {
    domain := .object .battlefield (.all #[.hasColor (.literal .green), .hasSubtype (.literal .elf), .hasType .creature])
    count := .upTo 1 }
  let changed := HasTextChange.applyTextChanges
    #[.replaceColorWord .green .red, .replaceCreatureType .elf .goblin] ts
  changed.noun == "up to one target red Goblin creature"

-- Phase 3: Novel compositional target specs parsed without any new constructors.
#guard
  match Parser.parseTargetSpec "up to two target untapped multicolored creatures an opponent controls with different names" with
  | some ts =>
    ts.slots.size == 1 &&
      ts.slots[0]!.count == .upTo 2 &&
      ts.slots[0]!.groupConstraint? == some .distinctNames &&
      Parser.parseTargetSpec ts.noun == some ts
  | none => false
#guard
  match Parser.parseTargetSpec "two target creatures with different controllers" with
  | some ts =>
    ts.slots.size == 1 && ts.slots[0]!.groupConstraint? == some .distinctControllers
  | none => false
#guard
  match Parser.parseTargetSpec "one or two other targets" with
  | some ts =>
    ts.slots.size == 1 &&
      ts.slots[0]!.domain == .anyTarget (.otherThan .this) &&
      ts.slots[0]!.count == .between 1 2 &&
      ts.noun == "one or two other targets"
  | none => false
-- Phase 3: `"for each player"` uses `PlayerFilter.thatPlayer` (never concrete `.seat 0`) and round-trips cleanly.
#guard
  match Parser.parseTargetSpec "for each player, up to one target creature that player controls" with
  | some ts =>
    ts == TargetSpec.forEachPlayerControlled (.hasType .creature) (.upTo 1) &&
      ts.slots[0]!.forEach? == some .any &&
      ts.slots[0]!.domain == .object .battlefield (.all #[.hasType .creature, .controlledBy .thatPlayer]) &&
      ts.noun == "for each player, up to one target creature that player controls"
  | none => false
#guard
  match Parser.parseTargetSpec "for each player, target creature card from that player's graveyard" with
  | some ts =>
    ts.slots.size == 1 &&
      ts.slots[0]!.forEach? == some .any &&
      ts.slots[0]!.domain == .object { zones := #[.graveyard], owner := .matching .thatPlayer }
        (.all #[.hasType .creature, .isKind .card]) &&
      Parser.parseTargetSpec ts.noun == some ts
  | none => false
#guard
  match Parser.parseTargetSpec "for each player, target creature" with
  | some ts =>
    ts.slots.size == 1 &&
      ts.slots[0]!.forEach? == some .any &&
      ts.slots[0]!.domain == .creature &&
      ts.noun == "for each player, target creature"
  | none => false

-- Phase 4 Stage-4 Cost & Keyword Sub-Grammar guards (CR 118, 122.1b, 509.1b, 606.2–6, 702)
#guard Parser.parseCostSpec "{1}{B}, {T}, Sacrifice a creature" ==
  some (CostSpec.ofItems #[.mana (ManaCost.ofGenericAndColor 1 .black), .tapSelf, .sacrifice (.exact 1) (.filter (.hasType .creature))])
#guard Parser.parseCostSpec "Discard a card or pay {2}." ==
  some (CostSpec.discardCardOrPayGeneric 2)
#guard Parser.parseCostSpec "Sacrifice an artifact or creature or pay {4}." ==
  some (CostSpec.sacrificeArtifactOrCreatureOrPayGeneric 4)
#guard Parser.parseCostSpec "Sacrifice a creature or planeswalker or pay {3}." ==
  some (CostSpec.sacrificeCreatureOrPlaneswalkerOrPayGeneric 3)
#guard Parser.parseCostSpec "Behold a Jace or pay {1}." ==
  some (CostSpec.beholdOrPayGeneric .jace 1)
#guard Parser.parseCostSpec "Get five poison counters." ==
  some (CostSpec.getPoisonCounters 5)
#guard Parser.parseCostSpec "Sacrifice three permanents." ==
  some (CostSpec.sacrificePermanents 3)
#guard Parser.parseCostSpec "Discard an enchantment, instant, or sorcery card." ==
  some CostSpec.discardEnchantmentInstantOrSorcery
#guard Parser.parseCostSpec "Sacrifice a legendary artifact or legendary creature." ==
  some CostSpec.sacrificeLegendaryArtifactOrCreature
#guard Parser.parseAdditionalCostSpec "As an additional cost to cast this spell, sacrifice an artifact or creature or pay {4}." ==
  some (AdditionalCostSpec.mandatory (CostSpec.sacrificeArtifactOrCreatureOrPayGeneric 4))
#guard Parser.parseAdditionalCostSpec "As an additional cost to cast this spell, you may discard a card." ==
  some (AdditionalCostSpec.opt CostSpec.discardCard)
#guard Parser.parseKeywordAbility "Flying" == some Keyword.flying
#guard Parser.parseKeywordAbility "Decayed" == some Keyword.decayed
#guard Parser.parseKeywordAbility "Exalted" == some Keyword.exalted
#guard Parser.parseKeywordAbility "Storied" == some Keyword.storied
#guard Parser.parseKeywordAbility "Hexproof" == some Keyword.hexproof
#guard Parser.parseKeywordAbility "Hexproof from black" == some (.hexproof (some (.color (.literal .black))))
#guard Parser.parseKeywordAbility "Islandwalk" == some Keyword.islandwalk
#guard Parser.parseKeywordAbility "Swampwalk" == some (.landwalk (.hasSubtype (.literal .swamp)))
#guard Parser.parseKeywordAbility "Nonbasic landwalk" ==
  some (.landwalk (.all #[.hasType .land, .not (.hasSupertype .basic)]))
#guard Parser.parseKeywordAbility "Legendary landwalk" ==
  some (.landwalk (.all #[.hasType .land, .hasSupertype .legendary]))
#guard Parser.parseKeywordAbility "Snow landwalk" ==
  some (.landwalk (.all #[.hasType .land, .hasSupertype .snow]))
#guard Parser.parseKeywordAbility "Wizardwalk" == none
#guard ["Nonbasic landwalk", "Legendary landwalk", "Snow landwalk", "Islandwalk", "Swampwalk", "Wizardwalk"].all fun s =>
  Parser.parseKeywordAbility s == KeywordAbility.ofSimpleName? s
#guard [Keyword.islandwalk, KeywordAbility.subtypeLandwalk .swamp,
        KeywordAbility.nonbasicLandwalk, KeywordAbility.legendaryLandwalk,
        KeywordAbility.snowLandwalk].all fun kw =>
  Parser.parseKeywordAbility (ToOracle.toOracle {} kw) == some kw &&
  Parser.parseKeywordAbility (ToOracle.toOracle { capitalize := true } kw) == some kw
#guard ToOracle.toOracle { capitalize := true } KeywordAbility.nonbasicLandwalk == "Nonbasic landwalk"
#guard ToOracle.toOracle { capitalize := true } KeywordAbility.legendaryLandwalk == "Legendary landwalk"
#guard ToOracle.toOracle { capitalize := true } KeywordAbility.snowLandwalk == "Snow landwalk"
-- Qualified Equip parsing and ToOracle round-trip (CR 702.6a).
#guard Parser.parseKeywordAbility "Equip {2}" ==
  some (.equip (.all #[.hasType .creature, .controlledBy .you]) (CostSpec.ofGeneric 2))
#guard Parser.parseKeywordAbility "Equip Soldier {1}" ==
  some (.equip (.all #[.hasType .creature, .hasSubtype (.literal .soldier), .controlledBy .you]) (CostSpec.ofGeneric 1))
#guard Parser.parseKeywordAbility "Equip legendary creature {2}" ==
  some (.equip (.all #[.hasSupertype .legendary, .hasType .creature, .controlledBy .you]) (CostSpec.ofGeneric 2))
#guard (Parser.parseKeywordAbility "Equip {2}").map (ToOracle.toOracle { capitalize := true }) == some "Equip {2}"
#guard (Parser.parseKeywordAbility "Equip Soldier {1}").map (ToOracle.toOracle { capitalize := true }) == some "Equip Soldier {1}"
#guard (Parser.parseKeywordAbility "Equip Soldier—Pay 2 life.").map (ToOracle.toOracle { capitalize := true }) == some "Equip Soldier—Pay 2 life."
#guard (Parser.parseKeywordAbility "Equip legendary creature {2}").map (ToOracle.toOracle { capitalize := true }) ==
  some "Equip legendary creature {2}"
#guard (Parser.parseKeywordAbility "Equip worthy creature {2}").map (ToOracle.toOracle { capitalize := true }) ==
  some "Equip worthy creature {2}"
#guard (Parser.parseKeywordAbility "Equip legendary creature—{2}, Pay 2 life.").map (ToOracle.toOracle { capitalize := true }) ==
  some "Equip legendary creature—{2}, Pay 2 life."
#guard ["Equip {2}", "Equip—{2}, Pay 2 life.", "Equip Soldier {1}", "Equip Soldier—Pay 2 life.",
        "Equip legendary creature {2}", "Equip worthy creature {2}",
        "Equip legendary creature—{2}, Pay 2 life."].all fun s =>
  match Parser.parseKeywordAbility s with
  | some kw =>
    Parser.parseKeywordAbility (ToOracle.toOracle {} kw) == some kw &&
    Parser.parseKeywordAbility (ToOracle.toOracle { capitalize := true } kw) == some kw
  | none => false
#guard Parser.parseKeywordAbility "Ward {2}" == some (.ward (CostSpec.ofGeneric 2))
#guard Parser.parseKeywordAbility "Ward—Discard a card or pay {2}." ==
  some (.ward (CostSpec.discardCardOrPayGeneric 2))
#guard Parser.parseKeywordAbility "Ward—Get five poison counters." ==
  some (.ward (CostSpec.getPoisonCounters 5))
#guard Parser.parseKeywordAbility "Gift a Treasure" == some (.gift .treasure)
#guard Parser.parseKeywordAbility "Flashback—{1}{B}, Discard a card." ==
  some (.flashback (CostSpec.ofItems #[.mana (ManaCost.ofGenericAndColor 1 .black), .discard (.exact 1) .hand]))
#guard Parser.parseKeywordAbility "Impending 4—{1}{W}{W}" ==
  some (.impending 4 (CostSpec.ofMana (ManaCost.ofGenericAndColors 1 [.white, .white])))
#guard Parser.parseKeywordAbility "Morph {3}{U}" ==
  some (.morph (CostSpec.ofMana (ManaCost.ofGenericAndColor 3 .blue)))
#guard Parser.parseKeywordAbility "Toxic 2" == some (.toxic 2)
#guard Parser.parseKeywordAbility "Can't be blocked" == none
#guard Parser.parseKeywordLine "Prowess, prowess" == some #[Keyword.prowess, Keyword.prowess]
#guard Parser.parseKeywordLine "Flying, protection from white and from black" ==
  some #[Keyword.flying, .protection (.color (.literal .white)), .protection (.color (.literal .black))]
#guard HasTextChange.applyTextChanges #[TextChange.replaceCreatureType .island .swamp] Keyword.islandwalk ==
  KeywordAbility.subtypeLandwalk .swamp
#guard HasTextChange.applyTextChanges #[TextChange.replaceColorWord .red .blue]
    (KeywordAbility.protection (.color (.literal .red))) ==
  KeywordAbility.protection (.color (.literal .blue))
#guard CounterKind.grantedKeyword? .decayed == some Keyword.decayed
#guard CounterKind.grantedKeyword? .exalted == some Keyword.exalted
#guard CounterKind.grantedKeyword? .hexproof == some Keyword.hexproof

-- Phase 5: Compositional `parseManaSpec` / `parseManaProductionSpec` /
-- `parseManaAbilityLine`, CR 605.1a all 4 criteria, `HasTextChange`, and
-- `ToOracle` round-trips (anchored to 25 September 2026 CR).

-- All 4 `ManaSpec` ctors & all 6 `ManaPoolPalette` ctors, including novel combinations.
#guard Parser.parseManaSpec "{G}" == some (.fixed #[.colored .green])
#guard Parser.parseManaSpec "{C}{C}" == some (.fixed #[.colorless, .colorless])
#guard Parser.parseManaSpec "{W}{U}{B}" == some (.fixed #[.colored .white, .colored .blue, .colored .black])
#guard Parser.parseManaSpec "{G} for each Elf you control" ==
  some (.sequence #[(.colored .green, ValueExpr.count (.controlledOfSubtype .elf))])
#guard Parser.parseManaSpec "{R} for each Goblin you control" ==
  some (.sequence #[(.colored .red, ValueExpr.count (.controlledOfSubtype .goblin))])
#guard Parser.parseManaSpec "{U} or {B}" ==
  some (.oneOf (.explicit #[.colored .blue, .colored .black]) (.const 1))
#guard Parser.parseManaSpec "{W}, {U}, or {B}" ==
  some (.oneOf (.explicit #[.colored .white, .colored .blue, .colored .black]) (.const 1))
#guard Parser.parseManaSpec "one mana of any color" == some (.oneOf .anyColor (.const 1))
#guard Parser.parseManaSpec "three mana of any one color" == some (.oneOf .anyColor (.const 3))
#guard Parser.parseManaSpec "X mana of any one color, where X is this creature's power" ==
  some (.oneOf .anyColor (.objectStat .power .this))
-- CR 201.5c comma-shortened legendary self-reference normalization.
#guard Parser.parseManaSpec "X mana of any one color, where X is Doc Samson's power"
    "Doc Samson, Super Psychiatrist" ==
  some (.oneOf .anyColor (.objectStat .power .this))
#guard Parser.parseManaSpec "one mana of the chosen color" ==
  some (.oneOf .chosenColorOnSource (.const 1))
#guard Parser.parseManaSpec "two mana of the chosen color" ==
  some (.oneOf .chosenColorOnSource (.const 2))
#guard Parser.parseManaSpec "four mana in any combination of colors" ==
  some (.combination .anyColor (.const 4))
#guard Parser.parseManaSpec "two mana in any combination of {U}, {B}, and/or {R}" ==
  some (.combination (.explicit #[.colored .blue, .colored .black, .colored .red]) (.const 2))
#guard Parser.parseManaSpecWithFormat "{W}{W}, {W}{B}, or {B}{B}" ==
  some (.combination (.explicit #[.colored .white, .colored .black]) (.const 2), true)
#guard Parser.parseManaSpec "one mana of any color in your commander's color identity" ==
  some (.colorAmong (.commanderColorIdentity .you) false)
#guard Parser.parseManaSpec "one mana of any color among legendary creatures and planeswalkers you control" ==
  some (.colorAmong (.colorsAmong .legendaryCreaturesAndPlaneswalkersYouControl) false)
#guard Parser.parseManaSpec "one mana of any color that a land an opponent controls could produce" ==
  some (.colorAmong (.typesLandsCouldProduce .landsOpponentsControl) false)
#guard Parser.parseManaSpec "one mana of any type that a land you control could produce" ==
  some (.colorAmong (.typesLandsCouldProduce .otherLandsYouControl) true)

-- `parseManaProductionSpec`: self-damage, restrictions, riders, "Choose a color.", & rejection.
#guard Parser.parseManaProductionSpec #["Add {R} or {W}", "This land deals 1 damage to you"] ==
  some { spec := .oneOf (.explicit #[.colored .red, .colored .white]) (.const 1), damageYou := 1 }
#guard
  match Parser.parseManaProductionSpec #[
    "Add one mana of any color",
    "Spend this mana only to cast a legendary spell, and that spell can't be countered"
  ] with
  | some mp => mp.restriction == some .legendarySpell && mp.allRiders == #[.cantBeCountered]
  | none => false
#guard Parser.parseManaProductionSpec #[
    "Add {G}", "If that mana is spent on a creature spell, it gains haste"
  ] == some { spec := .fixedOne (.colored .green), riders := #[.gainsHaste] }
#guard Parser.parseManaProductionSpec #[
    "Add {C}", "If that mana is spent on a creature spell, that creature enters with a +1/+1 counter on it"
  ] == some { spec := .fixedOne .colorless, riders := #[.entersWithPlusOneCounters 1] }
#guard Parser.parseManaProductionSpec #[
    "Add {C}", "If that mana is spent on a creature spell, that creature enters with two additional +1/+1 counters on it"
  ] == some { spec := .fixedOne .colorless, riders := #[.entersWithPlusOneCounters 2] }
#guard
  match Parser.parseManaProductionSpec #[
    "Choose a color",
    "Add one mana of that color for each different power among creatures you control"
  ] with
  | some mp => mp.chooseColorPrefix &&
      mp.spec == .oneOf .anyColor (.aggregate .countDistinct (.stat .power) .creaturesYouControl)
  | none => false
#guard Parser.parseManaProductionSpec #["Add {G}", "Draw a card"] == none

-- `parseManaAbilityLine`: Exhaust, Boast, timing, turn limits, zones, conditions, & rejections.
#guard
  match Parser.parseManaAbilityLine "Exhaust — {T}: Add {G}{G}{G}." with
  | some ab => ab.isManaAbility && ab.isExhaust && ab.lifetimeLimit? == some 1 &&
      ab.cost == CostSpec.tapOnly &&
      (ab.manaProduction?.map (·.spec)) == some (.fixed #[.colored .green, .colored .green, .colored .green])
  | none => false
#guard
  match Parser.parseManaAbilityLine "Boast — {1}: Add {R}{R}." with
  | some ab => ab.isManaAbility && ab.isBoast && ab.turnLimit? == some 1 &&
      ab.condition? == some ActivatedAbility.condSourceAttackedThisTurn
  | none => false
#guard
  match Parser.parseManaAbilityLine "{T}: Add {U}. Activate only as a sorcery." with
  | some ab => ab.isManaAbility && ab.timing == .sorcery
  | none => false
#guard
  match Parser.parseManaAbilityLine "{T}: Add {B}. Activate no more than two times each turn." with
  | some ab => ab.isManaAbility && ab.turnLimit? == some 2
  | none => false
#guard
  match Parser.parseManaAbilityLine "{T}: Add {C}. Activate only from your graveyard." with
  | some ab => ab.isManaAbility && ab.activeZones == #[.graveyard]
  | none => false
#guard
  match Parser.parseManaAbilityLine
      "{T}: Add {U} or {R}. Activate only if this land entered this turn or if you control a basic land." with
  | some ab => ab.isManaAbility &&
      ab.condition? == some ActivatedAbility.condEnteredThisTurnOrControlBasicLand
  | none => false
-- Rejects loyalty abilities, triggered abilities, and library-moving / non-mana abilities.
#guard Parser.parseManaAbilityLine "[+1]: Add {R}." == none
#guard Parser.parseManaAbilityLine "Whenever a land enters, add {G}." == none
#guard Parser.parseManaAbilityLine "{T}: Add {G}. Draw a card." == none

-- CR 605.1a (25 September 2026) all 4 criteria on `ActivatedAbility.isManaAbility`:
#guard (ActivatedAbility.manaSimple (.colored .green)).isManaAbility
#guard (ActivatedAbility.intrinsicBasicLandMana .red).isManaAbility
-- Fails criterion 1 (requires target).
#guard !({ cost := CostSpec.tapOnly,
           effect := { targeting := .of TargetSpec.creature,
                       body := Instruction.addSimpleMana #[.colored .green] } } : ActivatedAbility).isManaAbility
-- Fails criterion 2 (does not add mana).
#guard !({ cost := CostSpec.tapOnly, effect := Effect.gainLife 1 } : ActivatedAbility).isManaAbility
-- Fails criterion 3 (loyalty ability, CR 606.2).
#guard !({ cost := CostSpec.ofLoyalty (.plus 1), timing := .loyalty,
           effect := { body := Instruction.addSimpleMana #[.colored .red] } } : ActivatedAbility).isManaAbility
-- Fails criterion 4 (effect moves cards from library).
#guard !({ cost := CostSpec.tapOnly,
           effect := { body := .seq #[Instruction.addSimpleMana #[.colored .green], Instruction.drawFixed 1] } } : ActivatedAbility).isManaAbility
-- Fails criterion 4 (cost exiles from library).
#guard !({ cost := CostSpec.ofItems #[.tapSelf, .exile (.exact 1) { zones := #[.library], owner := .ofPlayer .you } (.filter .isCard)],
           effect := { body := Instruction.addSimpleMana #[.colored .green] } } : ActivatedAbility).isManaAbility
-- Fails criterion 4 (library-moving `Instruction` steps: draw, mill, search, inspect-to-hand, explore),
-- while `.scry` only reorders cards inside a library and remains a mana ability.
#guard [
  Instruction.drawFixed 1,
  Instruction.millFixed 2,
  .player (.searchLibrary { filter := .hasType .land, dest := .hand .controller }),
  .player (.explore .this)
].all fun instr =>
  !({ cost := CostSpec.tapOnly,
      effect := { body := .seq #[Instruction.addSimpleMana #[.colored .green], instr] } } : ActivatedAbility).isManaAbility
#guard ({ cost := CostSpec.tapOnly,
          effect := { body := .seq #[Instruction.addSimpleMana #[.colored .green], Instruction.scryFixed 1] } } : ActivatedAbility).isManaAbility
-- Modal activated abilities follow the exact four CR 605.1a criteria across every mode:
-- untargeted non-library modal abilities that could add mana ARE mana abilities,
-- while a targeted or library-moving mode disqualifies them.
#guard (ActivatedAbility.mkModal CostSpec.tapOnly #[Effect.addMana #[.colored .green], Effect.gainLife 1]).isManaAbility
#guard (ActivatedAbility.mkModal CostSpec.tapOnly #[Effect.addMana #[.colored .red], Effect.addMana #[.colored .green]]).isManaAbility
#guard (ActivatedAbility.mkModal CostSpec.tapOnly #[Effect.gainLife 1, Effect.addMana #[.colored .red]]).isManaAbility
#guard !(ActivatedAbility.mkModal CostSpec.tapOnly
  #[Effect.addMana #[.colored .green], { targeting := .of TargetSpec.creature, body := Instruction.gainLifeFixed 1 }]).isManaAbility
#guard !(ActivatedAbility.mkModal CostSpec.tapOnly
  #[Effect.addMana #[.colored .green], Effect.draw 1]).isManaAbility

-- Functorial `HasTextChange` on `ManaSpec`, `ManaProductionSpec`, `ActivationCostReduction`,
-- `ActivationMechanicTag`, and `ActivatedAbility` (CR 612.2 / 613.1c).
#guard
  let tcs := #[TextChange.replaceCreatureType .elf .goblin]
  let ab := ActivatedAbility.manaAbility
    (.sequence #[(.colored .green, ValueExpr.count (.controlledOfSubtype .elf))])
    (restriction := some (.subtypeSpellOrSource .elf))
  let ab' := HasTextChange.applyTextChanges tcs ab
  ab'.manaProduction? == some {
    spec := .sequence #[(.colored .green, ValueExpr.count (.controlledOfSubtype .goblin))]
    restriction := some (.subtypeSpellOrSource .goblin)
  }
#guard
  let tcs := #[TextChange.replaceCreatureType .human .soldier]
  HasTextChange.applyTextChanges tcs (ActivationMechanicTag.equip (some (.hasSubtype (.literal .human)))) ==
    ActivationMechanicTag.equip (some (.hasSubtype (.literal .soldier)))
#guard
  let tcs := #[TextChange.replaceCreatureType .equipment .aura]
  let red' := HasTextChange.applyTextChanges tcs (ActivationCostReduction.perEquipment 1)
  red' == { amount := ValueExpr.count (.inZones .battlefield (.all #[.hasSubtype (.literal .aura), .controlledBy .you])) }

-- Canonical `ToOracle` round-trips through `Parser.parseManaAbilityLine`
-- (including `chooseColorPrefix` across both distinct-power and general `ValueExpr` counts).
#guard [
  ActivatedAbility.manaSimple (.colored .green),
  ActivatedAbility.manaTapSacrificeAnyColor,
  ActivatedAbility.manaTapSacrificeThreeOfOneColor,
  ActivatedAbility.manaTapChosenColor,
  ActivatedAbility.manaAbility (.fixedOne (.colored .green)) (riders := #[.gainsHaste]),
  ActivatedAbility.manaAbility (.fixedOne .colorless) (riders := #[.entersWithPlusOneCounters 2]),
  ActivatedAbility.manaAbility (.oneOf (.explicit #[.colored .red, .colored .white]) (.const 1)) (damageYou := 1),
  ActivatedAbility.manaAbility (.oneOf .anyColor (.const 1)) (restriction := some .legendarySpell) (riders := #[.cantBeCountered]),
  ActivatedAbility.manaAbility (.oneOf .anyColor (.aggregate .countDistinct (.stat .power) .creaturesYouControl)) (chooseColorPrefix := true),
  ActivatedAbility.manaAbility (.oneOf .anyColor (ValueExpr.count (.controlledOfSubtype .elf))) (chooseColorPrefix := true),
  ActivatedAbility.manaAbility (.oneOf .anyColor (.basicLandTypeCount .landsYouControl)) (chooseColorPrefix := true),
  ActivatedAbility.manaAbility (.oneOf .anyColor (.counterCount (some .charge) .this)) (chooseColorPrefix := true),
  ActivatedAbility.manaAbility (.colorAmong (.commanderColorIdentity .you) false),
  ActivatedAbility.manaAbility (.colorAmong (.colorsAmong .legendaryCreaturesAndPlaneswalkersYouControl) false),
  ActivatedAbility.manaAbility (.colorAmong (.typesLandsCouldProduce .otherLandsYouControl) true),
  ActivatedAbility.manaAbility (.colorAmong (.typesLandsCouldProduce .landsOpponentsControl) false),
  ActivatedAbility.manaAbility (.combination (.explicit #[.colored .white, .colored .black]) (.const 2))
    (cost := CostSpec.ofItems #[.mana (ManaCost.ofHybrid .white .black), .tapSelf]) (filterPairFormat := true),
  ActivatedAbility.manaAbility (.fixedOne (.colored .blue)) (turnLimit? := some 2),
  ActivatedAbility.manaAbility (.fixedOne (.colored .black)) (timing := .sorcery)
].all fun ab =>
  Parser.parseManaAbilityLine (ab.toOracle {}) == some ab

-- Phase 6: Functorial `HasTextChange` on stratified `StaticAbility` (CR 612.2 / 613.1c).
#guard
  let tcs := #[TextChange.replaceCreatureType .elf .goblin]
  HasTextChange.applyTextChanges tcs (StaticAbility.costReductionIfYouControl 2 .elf) ==
    StaticAbility.costReductionIfYouControl 2 .goblin
#guard
  let tcs := #[TextChange.replaceCreatureType .elf .goblin]
  HasTextChange.applyTextChanges tcs (StaticAbility.flashIfYouControlSubtype .elf) ==
    StaticAbility.flashIfYouControlSubtype .goblin
#guard
  let tcs := #[TextChange.replaceCreatureType .elf .goblin]
  HasTextChange.applyTextChanges tcs (StaticAbility.extraLandIfOtherSubtype .elf) ==
    StaticAbility.extraLandIfOtherSubtype .goblin
#guard
  let tcs := #[TextChange.replaceCreatureType .dragon .angel]
  HasTextChange.applyTextChanges tcs (StaticAbility.entersTappedUnlessBehold .dragon) ==
    StaticAbility.entersTappedUnlessBehold .angel
#guard
  let tcs := #[TextChange.replaceCreatureType .sphinx .wizard]
  HasTextChange.applyTextChanges tcs (StaticAbility.eminenceSubtypeSpellsCostLess .sphinx 1) ==
    StaticAbility.eminenceSubtypeSpellsCostLess .wizard 1
#guard
  let tcs := #[TextChange.replaceCreatureType .army .zombie]
  HasTextChange.applyTextChanges tcs StaticAbility.armiesYouControlHaveTrample ==
    StaticAbility.continuous none (StaticAbility.scopeCreaturesOfSubtypeYouControl .zombie) (.grantKeywords #[Keyword.trample])

-- Phase 6: Stage-4 `Parser.parseStaticAbilityLine` & `Parser.parseNovelStaticAbilityLine`.
#guard Parser.parseStaticAbilityLine "Enchant creature you control" ==
  some #[StaticAbility.enchantCreatureYouControl]
#guard Parser.parseStaticAbilityLine "Enchant artifact or non-Aura enchantment" ==
  some #[StaticAbility.enchantArtifactOrNonAuraEnchantment]
#guard (Parser.parseStaticAbilityLine "Enchant nonland permanent").isSome
#guard Parser.parseStaticAbilityLine "This spell can't be countered." ==
  some #[StaticAbility.spellCantBeCountered]
#guard Parser.parseStaticAbilityLine "Your opponents can't gain life." ==
  some #[StaticAbility.opponentsCantGainLife]
#guard Parser.parseStaticAbilityLine "You can't lose the game and your opponents can't win the game." ==
  some #[StaticAbility.cantLoseAndOpponentsCantWin]
#guard Parser.parseStaticAbilityLine "This land enters tapped unless you pay 2 life." ==
  some #[StaticAbility.entersTappedUnlessPayLife 2]
#guard Parser.parseStaticAbilityLine "As this creature enters, choose a creature type." ==
  some #[StaticAbility.asEntersChooseCreatureType]
#guard Parser.parseStaticAbilityLine
    "Eminence — As long as this creature is in the command zone or on the battlefield, Sphinx spells you cast cost {1} less to cast." ==
  some #[StaticAbility.eminenceSubtypeSpellsCostLess .sphinx 1]
#guard Parser.parseNovelStaticAbilityLine "During your turn, creatures you control get +3/+1." ==
  some #[.continuous (some .isYourTurn) StaticAbility.scopeCreaturesYouControl (.modifyPT (.const 3) (.const 1))]
#guard Parser.parseNovelStaticAbilityLine "Other Elves you control have vigilance and lifelink." ==
  some #[.continuous none (StaticAbility.scopeOtherSubtypeYouControl .elf) (.grantKeywords #[Keyword.vigilance, Keyword.lifelink])]

-- Phase 6: Canonical `ToOracle` round-trip through `Parser.parseStaticAbilityLine`.
#guard [
  StaticAbility.spellCantBeCountered,
  StaticAbility.canBeCommander,
  StaticAbility.opponentsCantGainLife,
  StaticAbility.cantLoseAndOpponentsCantWin,
  StaticAbility.creaturesCantGetMinusCounters,
  StaticAbility.unspentManaBecomesColorless,
  StaticAbility.tokenDoubling,
  StaticAbility.foodAlsoCreatesTreasure,
  StaticAbility.drawTwoExceptFirstDrawStep,
  StaticAbility.entersTapped,
  StaticAbility.entersPrepared,
  StaticAbility.entersWithShield 1,
  StaticAbility.entersWithIndestructibleCounter,
  StaticAbility.entersTappedUnlessPayLife 2,
  StaticAbility.entersTappedUnlessBehold .dragon,
  StaticAbility.entersTappedUnlessNBasics 2,
  StaticAbility.entersTappedUnlessAnySubtype #[.plains, .swamp],
  StaticAbility.asEntersChooseCreatureType,
  StaticAbility.asEntersChooseCardType,
  StaticAbility.asEntersChooseOddEven,
  StaticAbility.protectionFromChosenCardType,
  StaticAbility.corruptedToxicLifelink,
  StaticAbility.eminenceSubtypeSpellsCostLess .sphinx 1,
  StaticAbility.enchantCreatureYouControl,
  StaticAbility.enchantArtifactOrNonAuraEnchantment
].all fun ab =>
  Parser.parseStaticAbilityLine (ab.toOracle {}) == some #[ab]

-- Phase 7: CR 603.10a–f structural look-back (`TriggerPattern.usesLookBack`).
#guard TriggerPattern.thisDies.usesLookBack
#guard TriggerPattern.thisLeaves.usesLookBack
#guard TriggerPattern.otherCreaturesDie.usesLookBack
#guard TriggerPattern.creatureCardLeavesYourGy.usesLookBack
#guard (TriggerPattern.zoneChange (.sameAs .this) .battlefield .hand).usesLookBack
#guard (TriggerPattern.zoneChange .isCard .graveyard .library).usesLookBack
#guard (TriggerPattern.zoneChange .isCard .exile .hand).usesLookBack
#guard (TriggerPattern.sacrifice .you (.hasType .creature)).usesLookBack
#guard (TriggerPattern.phasesOut (.sameAs .this)).usesLookBack
#guard (TriggerPattern.becomesUnattached (.sameAs .this)).usesLookBack
#guard (TriggerPattern.controlLost (.sameAs .this)).usesLookBack
#guard (TriggerPattern.spellCountered .anyObject).usesLookBack
#guard (TriggerPattern.playerAction .any .losesGame).usesLookBack
#guard !TriggerPattern.thisEnters.usesLookBack
#guard !TriggerPattern.thisAttacks.usesLookBack
#guard !TriggerPattern.thisBecomesBlocked.usesLookBack
#guard !TriggerPattern.thisDealsCombatDamageToPlayer.usesLookBack
#guard !TriggerPattern.creaturesYouControlBecomeTapped.usesLookBack
#guard !(TriggerPattern.becomesTapped (.sameAs .this)).usesLookBack
#guard !TriggerPattern.youCastSpell.usesLookBack
#guard !(TriggerPattern.drawCard .you).usesLookBack
#guard !TriggerPattern.stepYourUpkeep.usesLookBack
#guard !TriggerPattern.youScry.usesLookBack
#guard !(TriggerPattern.zoneChange .isCard .hand .graveyard).usesLookBack
#guard !(TriggerPattern.zoneChange .isCard .library .graveyard).usesLookBack
-- `.or` propagates `usesLookBack` if any disjunct looks back, while `flattenOr`
-- lets `matchTriggers` inspect each disjunct independently.
#guard (TriggerPattern.or .thisEnters .thisDies).usesLookBack
#guard (TriggerPattern.or .thisEnters .thisDies).flattenOr.map TriggerPattern.usesLookBack ==
  #[false, true]

-- Phase 7: CR 605.1b triggered mana ability classification (`TriggeredAbility.isManaAbility`).
#guard ({
  pattern := .activateAbility .you .anyObject .manaAbility
  effect := Effect.addMana #[.colored .green]
} : TriggeredAbility).isManaAbility
#guard ({
  pattern := .playerAction .you .manaAdded
  effect := Effect.addMana #[.colored .red]
} : TriggeredAbility).isManaAbility
-- CR 605.1b has NO library-movement exclusion (unlike CR 605.1a).
#guard ({
  pattern := .activateAbility .you .anyObject .manaAbility
  effect := { body := .seq #[Instruction.addSimpleMana #[.colored .green], Instruction.drawFixed 1] }
} : TriggeredAbility).isManaAbility
-- Fails criterion 1 (requires target).
#guard !({
  pattern := .activateAbility .you .anyObject .manaAbility
  effect := { targeting := .of .creature, body := Instruction.addSimpleMana #[.colored .green] }
} : TriggeredAbility).isManaAbility
-- Fails criterion 2 (triggers on landfall, not activated mana ability / mana added).
#guard !({
  pattern := .landYouControlEnters
  effect := Effect.addMana #[.colored .green]
} : TriggeredAbility).isManaAbility
-- Fails criterion 2 (`.or` where one disjunct does not trigger on mana ability / mana added).
#guard !({
  pattern := .or (.activateAbility .you .anyObject .manaAbility) .landYouControlEnters
  effect := Effect.addMana #[.colored .green]
} : TriggeredAbility).isManaAbility
-- Fails criterion 3 (cannot add mana).
#guard !({
  pattern := .activateAbility .you .anyObject .manaAbility
  effect := Effect.gainLife 1
} : TriggeredAbility).isManaAbility

-- Phase 7: Functorial `HasTextChange` on `TriggerPattern` and `TriggeredAbility` (CR 612.2 / 613.1c).
#guard
  let tcs := #[TextChange.replaceCreatureType .elf .goblin]
  HasTextChange.applyTextChanges tcs (TriggerPattern.anotherSubtypeYouControlEnters .elf) ==
    TriggerPattern.anotherSubtypeYouControlEnters .goblin
#guard
  let tcs := #[TextChange.replaceColorWord .green .blue]
  HasTextChange.applyTextChanges tcs (TriggerPattern.youCastColor .green) ==
    TriggerPattern.youCastColor .blue
#guard
  let tcs := #[TextChange.replaceColorWord .green .blue]
  HasTextChange.applyTextChanges tcs TriggerPattern.castGreenOrForestEnters ==
    .or (.youCastColor .blue) .forestYouControlEnters
#guard
  let tcs := #[TextChange.replaceCreatureType .elf .goblin]
  let ab := TriggeredAbility.onAttackWithElvesScry 1
  (HasTextChange.applyTextChanges tcs ab).pattern == .youAttackWithSubtype .goblin

-- Phase 7: Unified Saga chapters as `TriggeredAbility` with `.counterThreshold .lore` (CR 714.2b/d).
#guard
  let sagaCard : CardDef := {
    name := "Test Saga"
    types := #[.enchantment]
    subtypes := #["Saga"]
    triggeredAbilities := #[
      TriggeredAbility.sagaChapter 1 (Effect.chapterDraw 1),
      TriggeredAbility.sagaChapters #[2, 3] (Effect.chapterAmassGoblins 2)
    ]
  }
  sagaCard.hasSagaChapters &&
    sagaCard.sagaChapters.size == 2 &&
    sagaCard.finalChapterNumber == 3 &&
    TriggeredAbility.finalChapterNumberOf #[] == 0

-- Phase 7 / 8: `CardDef.modellingError?` trigger validation.
#guard
  let badNoop : CardDef := {
    name := "Bad Trigger"
    types := #[.creature]
    triggeredAbilities := #[{ pattern := .thisEnters, effect := { body := .noop } }]
  }
  badNoop.modellingError?.isSome
#guard
  let badEmptySeq : CardDef := {
    name := "Empty Seq Trigger"
    types := #[.creature]
    triggeredAbilities := #[{ pattern := .thisEnters, effect := { body := .seq #[] } }]
  }
  badEmptySeq.modellingError?.isSome
#guard
  let badNoZones : CardDef := {
    name := "No Active Zones"
    types := #[.creature]
    triggeredAbilities := #[{ pattern := .thisEnters, activeZones := #[], effect := Effect.draw 1 }]
  }
  badNoZones.modellingError?.isSome
#guard
  let badModal : CardDef := {
    name := "Broken Modal Trigger"
    types := #[.creature]
    triggeredAbilities := #[TriggeredAbility.mkModal .thisEnters #[Effect.draw 1]
      (minModes := .const 2) (maxModes := .const 2)]
  }
  badModal.modellingError?.isSome
#guard
  let goodMayNoElse : CardDef := {
    name := "Valid May Trigger"
    types := #[.creature]
    triggeredAbilities := #[{
      pattern := .thisEnters
      effect := { body := Instruction.may .you none (Instruction.drawFixed 1) }
    }]
  }
  goodMayNoElse.modellingError?.isNone

-- Phase 7: Stage-4 compositional `Parser.parseTriggerClause`.
#guard
  match Parser.parseTriggerClause "When this creature enters, draw a card." with
  | some h => h.word == .when && h.pattern == .thisEnters && h.grouping == .perOccurrence &&
      h.interveningIf?.isNone && h.activeZones == #[.battlefield] && h.limit == .unlimited &&
      h.effectText == "draw a card"
  | none => false
#guard
  match Parser.parseTriggerClause "Whenever one or more other creatures die, scry 1." with
  | some h => h.word == .whenever && h.pattern == .otherCreaturesDie && h.grouping == .oncePerBatch &&
      h.effectText == "scry 1"
  | none => false
#guard
  match Parser.parseTriggerClause
      "Whenever this creature attacks while you control a creature with power 4 or greater, you gain 2 life." with
  | some h =>
      (match h.pattern with
      | .whenCond .thisAttacks (.exists (.inZones .battlefield _)) => true
      | _ => false) &&
      h.interveningIf?.isNone && h.effectText == "you gain 2 life"
  | none => false
#guard
  match Parser.parseTriggerClause
      "At the beginning of each end step, if you gained 3 or more life this turn, draw a card." with
  | some h => h.word == .at && h.pattern == .stepEachEndStep &&
      h.interveningIf? == some (.turnHistory (.eventOccurredThisTurn .you (.gainedLife 3))) &&
      h.effectText == "draw a card"
  | none => false
#guard
  match Parser.parseTriggerClause
      "Whenever an artifact you control enters, draw a card. This ability triggers only once each turn." with
  | some h => h.pattern == .artifactYouControlEnters && h.limit == .onceEachTurn &&
      h.effectText == "draw a card"
  | none => false
#guard
  match Parser.parseTriggerClause "When you cast this spell, draw a card." with
  | some h => h.pattern == .thisCast && h.activeZones == #[.stack]
  | none => false
#guard
  match Parser.parseTriggerClause
      "Whenever a land you control enters, you may pay {1}{B}. If you do, return this card from your graveyard to the battlefield." with
  | some h => h.pattern == .landYouControlEnters && h.activeZones == #[.graveyard]
  | none => false
#guard
  match Parser.parseTriggerClause "When you cycle this card, draw a card." with
  | some h => h.activeZones == #[.hand]
  | none => false

-- Phase 8: Unified `Instruction` AST, computed agent classification, `CardDef.modalSpec?` /
-- `empowerPlaneswalkerAmount?`, `HasTextChange` on `Instruction`/`Effect`, and Stage-4
-- compositional `Parser.parseInstructionSeq` / `Parser.parseInstructionEffect`.
#guard (Effect.dealDamage 3).classifyForAgent == .burn
#guard (Effect.dealDamageToCreature 5).classifyForAgent == .creatureDamage
#guard Effect.destroyCreatureWithFlying.classifyForAgent == .destroyFlying
#guard Effect.destroyCreature.classifyForAgent == .destroyCreature
#guard Effect.destroyArtifactOrLandNonflyersCantBlock.classifyForAgent == .destroyArtifactOrLand
#guard (Effect.pump 3 3).classifyForAgent == .pump
#guard (Effect.allCreaturesGet (-4) (-4)).classifyForAgent == .massPump
#guard Effect.playAdditionalLandThisTurn.classifyForAgent == .extraLand
#guard (Effect.drawAndLoseLife 2 2).classifyForAgent == .draw
#guard Effect.counterSpell.classifyForAgent == .counter
#guard Effect.creatureYouControlDealsPowerToOppCreature.classifyForAgent == .fight
#guard (Effect.dealDamageToTargetCreature 2).classifyAbilityForAgent == .creatureDamage
#guard Effect.destroyTargetColorlessNonland.classifyAbilityForAgent == .destroyColorless
#guard (Effect.sourceGets 1 0).classifyAbilityForAgent == .other
#guard
  let c : CardDef := {
    name := "Test Modal"
    types := #[.instant]
    spellEffect := some {
      body := .chooseModes {
        minModes := .const 1
        maxModes := .const 2
        modes := #[Effect.draw 1, Effect.gainLife 3]
      }
    }
  }
  c.isModal && c.modes.size == 2 &&
    (c.modalSpec?.map CardDef.modalHeader) == some "Choose one or both —"
#guard
  let c : CardDef := {
    name := "Test Empower"
    types := #[.sorcery]
    spellEffect := some {
      body := .seq #[Instruction.drawFixed 1, Instruction.empowerJace 3]
      phrase := "draw a card"
    }
  }
  c.empowerPlaneswalkerAmount? == some 3 &&
    c.empowerLines == ["Empower Jace 3."]
#guard
  let tcs := #[TextChange.replaceCreatureType .elf .goblin]
  let i : Instruction :=
    .ifCond (.forAll (.target 0) (.hasSubtype (.literal .elf)))
      (Instruction.createTokensFixed .elf 1) .noop
  HasTextChange.applyTextChanges tcs i ==
    .ifCond (.forAll (.target 0) (.hasSubtype (.literal .goblin)))
      (Instruction.createTokensFixed (HasTextChange.applyTextChanges tcs TokenSpec.elf) 1) .noop
#guard
  match Parser.parseInstructionSeq "Draw two cards. You gain 3 life." with
  | some (.seq #[.player (.drawCards .you (.const 2)), .life (.gain .you (.const 3))], _) => true
  | _ => false
#guard
  match Parser.parseInstructionEffect "Destroy target creature. Scry 2." with
  | some e =>
    e.targetSpec == .creature &&
      e.body == .seq #[Instruction.destroy (.target 0), Instruction.scryFixed 2]
  | none => false
#guard
  match Parser.parseInstructionEffect "Exile target artifact. Draw a card." with
  | some e =>
    e.targetSpec == .artifact &&
      e.body == .seq #[Instruction.exile (.target 0), Instruction.drawFixed 1]
  | none => false

end Mtg.Engine


