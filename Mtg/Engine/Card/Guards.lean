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
#guard (Effect.dealDamage 3).resolution == Resolution.onPermanent (.dealDamage 3)
#guard (Effect.dealDamage 3).phrase == "deals 3 damage to any target"
#guard (Effect.dealDamage 3).spellResolution == .onPermanent (.dealDamage 3)
#guard (Effect.draw 2).resolution == Resolution.draw 2
#guard (Effect.scry 1).resolution == Resolution.scry 1
#guard (Effect.gainLife 3).resolution == .gainLife 3
#guard Resolution.toPhrase (.gainLife 3) "target creature" == "You gain 3 life"
#guard Resolution.toPhrase (.draw 2) "target player" == "Draw 2 cards"
#guard Resolution.toPhrase (.sequence [.draw 1, .discard (.cards 1)]) "target creature" ==
  "Draw a card. Discard a card"
#guard Resolution.toPhrase (.createTokens .treasure 1 (tapped := true)) "" ==
  "Create a tapped Treasure token"
#guard (Effect.drawLoseLifeThenAmass 2).resolution ==
  Resolution.sequence [.draw 1, .loseLife 1, .amass 2]
#guard (Effect.createTokensThenTeamPump .villain21menace 1 1 0).resolution ==
  Resolution.sequence
    [.createTokens .villain21menace 1, .creaturesYouControlPump 1 0]
#guard (Effect.createTokens .treasure 1).spellResolution == .createTokens .treasure 1
#guard (Effect.targetPlayerCreatesTokens .leviathan65hexproof 1).spellResolution ==
  .createTokens .leviathan65hexproof 1 (who := .player)
#guard (Effect.targetPlayerCreatesTokens .leviathan65hexproof 1).resolution ==
  .createTokens .leviathan65hexproof 1 (who := .player)
#guard SpellResolution.toPhrase (.createTokens .treasure 1) "target player" ==
  "create a Treasure token"
#guard SpellResolution.toPhrase
    (.createTokens .leviathan65hexproof 1 (who := .player)) "target player" ==
  "target player creates a 6/5 blue Leviathan creature token with hexproof"
#guard (Effect.destroyArtifactOrEnchantmentGainLife 2).resolution ==
  Resolution.sequence [.onPermanent .destroy, .gainLife 2]
#guard (Effect.tapScryDraw 1 1).resolution ==
  Resolution.sequence [.onPermanent .tap, .scry 1, .draw 1]
#guard (Effect.tapScryDraw 1 1).spellResolution ==
  .sequence [.onPermanent .tap, .scry 1, .draw 1]
#guard (Effect.tapScryDraw 1 1).phrase ==
  "tap target creature. Scry 1. Draw a card"
#guard (Effect.counterUnlessPays 4).spellResolution == .unlessPays .counter 4
#guard (Effect.counterUnlessPays 4).phrase ==
  "counter target spell unless its controller pays {4}"
#guard Effect.putOnTopOrBottom.spellResolution ==
  .or [.onPermanent .putOnTopOfLibrary, .onPermanent .putOnBottomOfLibrary]
#guard Effect.putOnTopOrBottom.phrase ==
  "target creature's owner puts it on their choice of the top or bottom of their library"
#guard (Effect.untapPumpMaybeAttach 2 2).spellResolution ==
  .sequence [
    .onPermanent .untap,
    .onPermanent (.pump 2 2),
    .«if» (.subtype .dwarf) (.may .attachEquipment (.sequence []))]
#guard (Effect.untapPumpMaybeAttach 2 2).phrase ==
  "untap target creature you control. It gets +2/+2 until end of turn. If it's a Dwarf, you may attach an Equipment you control to it"
#guard SpellResolution.toPhrase (.«if» (.subtype .elf) (.draw 1)) "target creature" ==
  "if target creature is an Elf, draw a card"
#guard SpellResolution.toPhrase (.may (.gainLife 3) (.sequence [])) "target creature" ==
  "you may gain 3 life"
#guard SpellResolution.toPhrase (.may .attachEquipment (.sequence [])) "target creature" ==
  "you may attach an Equipment you control to it"
#guard SpellResolution.toPhrase (.«if» (.subtype .dwarf) (.may .attachEquipment (.sequence []))) "target creature" ==
  "if target creature is a Dwarf, you may attach an Equipment you control to it"
#guard SpellResolution.toPhrase (.«if» (.mvAtMost 2) .recruit) "target spell" ==
  "if that spell's mana value was 2 or less, recruit"
#guard SpellResolution.toPhrase (.or [.draw 1, .gainLife 3]) "target creature" ==
  "draw a card or you gain 3 life"
#guard Effect.destroyCreatureSurveil.resolution ==
  Resolution.sequence [.onPermanent .destroy, .surveil 1]
#guard Effect.destroyCreatureSurveil.spellResolution ==
  .sequence [.onPermanent .destroy, .surveil 1]
#guard (Effect.pumpThenDraw (-4) 0).resolution ==
  Resolution.sequence [.onPermanent (.pump (-4) 0), .draw 1]
#guard (Effect.pumpThenDraw (-4) 0).spellResolution ==
  .sequence [.onPermanent (.pump (-4) 0), .draw 1]
#guard Effect.plusOneLifelinkIndestructible.resolution ==
  Resolution.sequence [.onPermanent (.plusOne 1),
    .onPermanent (.grantKeywords #[Keyword.lifelink, Keyword.indestructible])]
#guard Effect.plusOneLifelinkIndestructible.spellResolution ==
  .sequence [.onPermanent (.plusOne 1),
    .onPermanent (.grantKeywords #[Keyword.lifelink, Keyword.indestructible])]
#guard Effect.grantVigilanceUnblockable.resolution ==
  Resolution.sequence
    [.onPermanent (.grantKeywords #[Keyword.vigilance]),
     .onPermanent .cantBeBlocked,
     .draw 1]
#guard Effect.grantVigilanceUnblockable.spellResolution ==
  .sequence
    [.onPermanent (.grantKeywords #[Keyword.vigilance]),
     .onPermanent .cantBeBlocked,
     .draw 1]
#guard (Effect.creaturesYouControlGetAndGrant 1 1 #[Keyword.vigilance]).resolution ==
  Resolution.sequence [.creaturesYouControlPump 1 1, .teamGain #[Keyword.vigilance]]
#guard (Effect.creaturesYouControlGetAndGrant 1 1 #[Keyword.vigilance]).spellResolution ==
  .sequence [.creaturesPump 1 1, .teamGain #[Keyword.vigilance]]
#guard Effect.sourceGainsIndestructibleTap.resolution ==
  Resolution.sequence
    [.onSource (.grantKeywords #[Keyword.indestructible]), .onSource .tap]
#guard Effect.sourceGainsIndestructibleTap.phrase ==
  "Witch-king of Angmar gains indestructible until end of turn. Tap him"
#guard (Effect.drawThenDiscard 2).resolution ==
  Resolution.sequence [.draw 2, .discard (.cards 1)]
#guard (Effect.drawThenDiscard 2).spellResolution ==
  .sequence [.draw 2, .discard (.cards 1)]
#guard (Effect.abilityDrawThenDiscard 2).resolution ==
  Resolution.sequence [.draw 2, .discard (.cards 1)]
#guard (Effect.ownerShuffleSourceDraw 3).resolution ==
  Resolution.sequence [.shuffleSource, .draw 3]
#guard (Effect.ownerShuffleSourceDraw 3).phrase ==
  "This owner shuffles him into their library and draws 3 cards"
#guard (Effect.plusOneAndDraw 1 2).resolution ==
  Resolution.sequence [.onSource (.plusOne 1), .draw 2]
#guard (Effect.plusOneAndDraw 1 2).phrase ==
  "Put a +1/+1 counter on this and draw 2 cards"
#guard Effect.destroyUpToOneThenPlusOne.resolution ==
  Resolution.sequence [.onPermanent .destroy, .onSource (.plusOne 1)]
#guard Effect.destroyUpToOneThenPlusOne.phrase ==
  "Destroy up to one target artifact or enchantment. Put a +1/+1 counter on this"
#guard (Effect.plusOneAndCreateTokens 2 .robotVillain22).resolution ==
  Resolution.sequence [.onSource (.plusOne 2), .createTokens .robotVillain22 1]
#guard (Effect.plusOneAndCreateTokens 2 .robotVillain22).phrase ==
  "Put 2 +1/+1 counters on this creature and create a 2/2 colorless Robot Villain artifact creature token"
#guard (Effect.plusOneAndGrant #[Keyword.vigilance, Keyword.indestructible, Keyword.haste]).resolution ==
  Resolution.sequence
    [.onSource (.plusOne 1),
     .onSource (.grantKeywords #[Keyword.vigilance, Keyword.indestructible, Keyword.haste])]
#guard (Effect.plusOneAndGrant #[Keyword.vigilance, Keyword.indestructible, Keyword.haste]).phrase ==
  "Put a +1/+1 counter on this. He gains vigilance, indestructible, and haste until end of turn"
#guard (Effect.creaturesYouControlGetOppsLoseLife 1 0 1).resolution ==
  Resolution.sequence
    [.creaturesYouControlPump 1 0, .loseLife 1 .eachOpponent]
#guard (Effect.creaturesYouControlGetOppsLoseLife 1 0 1).phrase ==
  "Creatures you control get +1/+0 until end of turn. Each opponent loses 1 life"
#guard (Effect.subtypesGainMenace #["Goblin", "Orc"]).resolution ==
  .subtypesGainMenace #[.goblin, .orc]
#guard (Effect.subtypesGainMenace #["Goblin", "Orc"]).phrase ==
  "Goblins and Orcs you control gain menace until end of turn"
#guard (Effect.subtypesGainMenace #["Elf"]).phrase ==
  "Elves you control gain menace until end of turn"
#guard (Effect.drawLoseLifeThenAmass 2).spellResolution ==
  .sequence [.draw 1, .loseLife 1, .amass 2]
#guard (Effect.counterThenRecruitIfMvAtMost 2).spellResolution ==
  .sequence [.counter, .«if» (.mvAtMost 2) .recruit]
#guard (Effect.counterThenRecruitIfMvAtMost 2).resolution ==
  .sequence [.counter, .«if» (.mvAtMost 2) .recruit]
#guard (Effect.counterThenRecruitIfMvAtMost 2).phrase ==
  "counter target spell. If that spell's mana value was 2 or less, recruit"
#guard (Effect.counterThenRecruitIfMvAtMost 2).castKind == .counter
#guard Resolution.flatten
    (.sequence [.sequence [.draw 1, .gainLife 1], .amass 2]) ==
  [.draw 1, .gainLife 1, .amass 2]
#guard (Effect.ofTrigger (.scry 2)).resolution == .scry (.fixed 2)
#guard (Effect.ofTrigger (.scry 2)).sharedTrigger == some (.scry 2)
#guard (Effect.chapterRecruit).asChapter? == some .recruit
#guard (Effect.chapterDraw 2).asChapter? == some (.draw 2)
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
#guard (Effect.dealDamageLoseIndestructibleExile 3).spellResolution ==
  .sequence [
    .onPermanent (.dealDamage 3),
    .onPermanent .loseIndestructible,
    .replace .diesThisTurn .exile]
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
#guard (Effect.pumpAndExileIfDies (-5) (-5)).spellResolution ==
  .sequence [.onPermanent (.pump (-5) (-5)), .replace .diesThisTurn .exile]
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
#guard TriggerEvent.spec .entering ==
  { clause := "this permanent enters", isWhenever := false, label := "enters trigger" }
#guard TriggerEvent.spec .attacking ==
  { clause := "this creature attacks", isWhenever := true, label := "attack trigger" }
#guard TriggerEvent.clause .youScry == "you scry"
#guard TriggerEvent.label .dying == "dies trigger"
#guard TriggerEvent.label .youScry == "scry trigger"
#guard TriggerEvent.label .landYouControlEnters == "landfall trigger"
#guard TriggerEvent.label .becomesBlocked == "becomes-blocked trigger"
#guard TriggerEvent.label .youCastInstantOrSorcery == "cast trigger"
#guard TriggerEvent.label .anotherElfYouControlEnters == "Elf-enters trigger"
#guard TriggerEvent.label .attacking == "attack trigger"
#guard TriggerEvent.label .youAttackWithElves == "attack trigger"
#guard !TriggerEvent.checkTargets .youCastInstantOrSorcery
#guard !TriggerEvent.checkTargets .youAttackWithElves
#guard !TriggerEvent.checkTargets .anotherElfYouControlEnters
#guard TriggerEvent.checkTargets .entering
#guard TriggerEvent.checkTargets .landYouControlEnters
#guard TriggerEvent.checkTargets .attacking
#guard !TriggerEvent.isWhenever .dying
#guard TriggerEvent.isWhenever .youAttackWithElves
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
#guard (Effect.plusOneUpToOneAndPlayerGainsLife 2).spellResolution ==
  .sequence [.countersOnCreatureTargets, .targetPlayersGainLife 2]
#guard (Effect.plusOneUpToOneAndPlayerGainsLife 2).phrase ==
  "put a +1/+1 counter on up to one target creature. Target player gains 2 life"
#guard SpellResolution.toPhrase (.countersOnCreatureTargets .stun 2) "target creature" ==
  "put 2 stun counters on up to one target creature"
#guard SpellResolution.toPhrase
    (.countersOnCreatureTargets .plusOnePlusOne 2 .firstYouControl) "target creature" ==
  "put 2 +1/+1 counters on target creature you control"
#guard Effect.fight.spellResolution == .mutualFight
#guard (Effect.plusOneThenFight 2).spellResolution ==
  .sequence [.countersOnCreatureTargets .plusOnePlusOne 2 .firstYouControl,
    .mutualFight]
#guard (Effect.plusOneThenFight 2).resolution ==
  .sequence [
    .countersOnCreatureTargets .plusOnePlusOne 2 .firstYouControl,
    .mutualFight]
#guard (Effect.plusOneThenFight 2).phrase ==
  "put 2 +1/+1 counters on target creature you control. Then it fights target creature an opponent controls"
#guard Effect.plusOneThenEachOtherIfFromGy.spellResolution ==
  .sequence [
    .countersOnCreatureTargets .plusOnePlusOne 1 .firstYouControl,
    .«if» .castFromGraveyard (.plusOneOnEachYouControl 1 .eachOther)]
#guard Effect.plusOneThenEachOtherIfFromGy.resolution ==
  .sequence [
    .countersOnCreatureTargets .plusOnePlusOne 1 .firstYouControl,
    .«if» .castFromGraveyard (.plusOneOnEachYouControl 1 .eachOther)]
#guard Effect.plusOneThenEachOtherIfFromGy.phrase ==
  "put a +1/+1 counter on target creature you control. If this spell was cast from a graveyard, also put a +1/+1 counter on each other creature you control"
#guard SpellResolution.toPhrase
    (.«if» .castFromGraveyard (.plusOneOnEachYouControl 1 .eachOther)) "target creature" ==
  "if this spell was cast from a graveyard, put a +1/+1 counter on each other creature you control"
#guard (Effect.drawIfFromGy 1 2).spellResolution ==
  .ifElse .castFromGraveyard (.draw 2) (.draw 1)
#guard (Effect.drawIfFromGy 1 2).resolution ==
  .ifElse .castFromGraveyard (.draw 2) (.draw 1)
#guard (Effect.drawIfFromGy 1 2).phrase ==
  "draw a card. If this spell was cast from a graveyard, draw 2 cards instead"
#guard (Effect.amassGoblinsOrFromGy 1 3).spellResolution ==
  .ifElse .castFromGraveyard (.amass 3) (.amass 1)
#guard (Effect.amassGoblinsOrFromGy 1 3).resolution ==
  .ifElse .castFromGraveyard (.amass 3) (.amass 1)
#guard (Effect.amassGoblinsOrFromGy 1 3).phrase ==
  "amass Goblins 1. If this spell was cast from a graveyard, amass Goblins 3 instead"
#guard SpellResolution.toPhrase
    (.ifElse (.subtype .elf) (.gainLife 3) (.draw 1)) "target creature" ==
  "draw a card. If target creature is an Elf, you gain 3 life instead"
#guard SpellResolution.toPhrase
    (.ifElse (.mvAtMost 2) .recruit (.draw 1)) "target spell" ==
  "draw a card. If that spell's mana value was 2 or less, recruit instead"
#guard SpellResolution.toPhrase (.plusOneOnEachYouControl 1 .eachOther) "target creature" ==
  "put a +1/+1 counter on each other creature you control"
#guard SpellResolution.toPhrase (.gainLife 3) "target creature" == "you gain 3 life"
#guard SpellResolution.toPhrase (.targetPlayersGainLife 2) "target player" ==
  "Target player gains 2 life"
#guard SpellResolution.toPhrase .returnTargetToHand "target spell" ==
  "return target spell to its owner's hand"
#guard SpellResolution.toPhrase (.returnTargetToHand .graveyard)
    "target creature card from your graveyard" ==
  "return up to one target creature card from your graveyard to your hand"
#guard Effect.returnSpellDraw.spellResolution ==
  .sequence [.returnTargetToHand, .draw 1]
#guard Effect.returnSpellDraw.resolution ==
  Resolution.sequence [.returnTargetSpell, .draw 1]
#guard Effect.returnSpellDraw.phrase ==
  "return target spell to its owner's hand. Draw a card"
#guard (Effect.returnCreatureFromGyThenAmass 3).spellResolution ==
  .sequence [.returnTargetToHand .graveyard, .amass 3]
#guard (Effect.returnCreatureFromGyThenAmass 3).resolution ==
  Resolution.sequence [.returnFromGyToHand, .amass 3]
#guard (Effect.returnCreatureFromGyThenAmass 3).phrase ==
  "return up to one target creature card from your graveyard to your hand. Amass Goblins 3"
#guard Effect.returnSpellCantCastIfGift.spellResolution ==
  .sequence [.returnTargetToHand, .«if» .giftPromised .playersCantCastThisTurn]
#guard SpellResolution.toPhrase (.creaturesPump 1 1) "target creature" ==
  "creatures you control get +1/+1 until end of turn"
#guard SpellResolution.toPhrase (.creaturesPump (-4) (-4) .all) "" ==
  "all creatures get -4/-4 until end of turn"
#guard SpellResolution.toPhrase (.creaturesPump (-1) (-1) .ofTargetPlayer) "target player" ==
  "creatures target player controls get -1/-1 until end of turn"
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
#guard (Effect.dealDamage 3).spellResolution == .onPermanent (.dealDamage 3)
#guard (Effect.pump 3 3).spellResolution == .onPermanent (.pump 3 3)
#guard Effect.destroyCreatureWithFlying.spellResolution == .onPermanent .destroy
#guard Effect.destroyCreature.spellResolution == .onPermanent .destroy
#guard Effect.playAdditionalLandThisTurn.spellResolution == .extraLand
#guard (Effect.drawAndLoseLife 2 2).spellResolution ==
  .sequence [.draw 2, .loseLife 2 .you]
#guard (Effect.draw 2).spellResolution == .draw 2
#guard (Effect.targetPlayerDraw 2).spellResolution == .draw 2 .player
#guard (Effect.targetPlayerDraw 2).resolution == .targetPlayerDraw 2
#guard SpellResolution.toPhrase (.draw 2 .you) "target player" == "draw 2 cards"
#guard SpellResolution.toPhrase (.draw 2 .player) "target player" ==
  "target player draws 2 cards"
#guard (Effect.targetPlayerDrawLoseLife 2 2).spellResolution ==
  .sequence [.draw 2 .player, .loseLife 2 .player]
#guard (Effect.destroyTargetCreatureControllerLosesLife 2).spellResolution ==
  .sequence [.onPermanent .destroy, .loseLife 2 (.controller .target)]
#guard (Effect.eachOpponentLosesLife 2).spellResolution == .loseLife 2 .eachOpponent
#guard SpellResolution.toPhrase (.loseLife 2 .you) "target player" == "lose 2 life"
#guard SpellResolution.toPhrase (.loseLife 2 .player) "target player" ==
  "target player loses 2 life"
#guard SpellResolution.toPhrase (.loseLife 2 (.controller .target)) "target creature" ==
  "its controller loses 2 life"
#guard SpellResolution.toPhrase (.loseLife 2 .eachOpponent) "target player" ==
  "each opponent loses 2 life"
#guard (Effect.millThenPutInstantOrSorcery 4).spellResolution ==
  .millThenPut 4 (.oneOf .instant .sorcery)
#guard (Effect.millThenPutLands 4 2).spellResolution ==
  .millThenPut 4 (.upTo 2 .land)
#guard (Effect.millThenPutAllInstantsOrSorceries 6).spellResolution ==
  .millThenPut 6 (.allOf .instant .sorcery)
#guard (Effect.millThenPutInstantOrSorcery 4).phrase ==
  "mill 4 cards, then put an instant or sorcery card from among them into your hand"
#guard (Effect.millThenPutLands 4 2).phrase ==
  "mill 4 cards, then put up to two land cards from among them into your hand"
#guard (Effect.millThenPutAllInstantsOrSorceries 6).phrase ==
  "mill 6 cards, then put all instant and sorcery cards from among them into your hand"
#guard (Effect.artifactSpellsCostLessThisTurn 1).spellResolution ==
  .spellsCostLessThisTurn (.cardType .artifact) 1
#guard (Effect.supertypeSpellsCostLessThisTurn 2).spellResolution ==
  .spellsCostLessThisTurn (.supertype .legendary) 2
#guard SpellResolution.toPhrase
    (.spellsCostLessThisTurn (.cardType .artifact) 1) "target player" ==
  "Artifact spells you cast this turn cost {1} less to cast"
#guard SpellResolution.toPhrase
    (.spellsCostLessThisTurn (.supertype .legendary) 2) "target player" ==
  "Legendary spells you cast this turn cost {2} less to cast"
#guard (Effect.dealDamageToEachCreature 3).spellResolution == .dealDamageToEachCreature 3
#guard (Effect.dealDamageToEachCreature 3).resolution == .dealDamageToEachCreature 3
#guard (Effect.dealDamageToEachOppCreature 1).spellResolution ==
  .dealDamageToEachCreature 1 .opponentsControl
#guard (Effect.dealDamageToEachNonDragon 2).spellResolution ==
  .dealDamageToEachCreature 2 (.nonSubtype .dragon)
#guard SpellResolution.toPhrase (.dealDamageToEachCreature 3 .each) "target creature" ==
  "deals 3 damage to each creature"
#guard SpellResolution.toPhrase (.dealDamageToEachCreature 1 .opponentsControl) "target creature" ==
  "deals 1 damage to each creature your opponents control"
#guard SpellResolution.toPhrase
    (.dealDamageToEachCreature 2 (.nonSubtype .elf)) "target creature" ==
  "deals 2 damage to each non-Elf creature"
#guard Effect.creatureYouControlDealsPowerToOppCreature.spellResolution ==
  .fight .announced (.timesPower 1)
#guard Effect.creatureYouControlDealsTwicePower.spellResolution == .fight .announced (.timesPower 2)
#guard Effect.fightUpToOne.spellResolution == .mutualFight .upToOne
#guard (Effect.createTokensX .dwarf).spellResolution ==
  .createTokens .dwarf .chosenX
#guard (Effect.createTokensPerSubtype .treasure "Villain").spellResolution ==
  .createTokens .treasure (.perSubtype .villain)
#guard Effect.damageOppCreaturesEqualOtherSpellsMv.spellResolution ==
  .dealDamageToEachCreature 0 .opponentsControl .otherSpellsManaValue
#guard (Effect.counterUnlessPaysTeamwork 2 4).spellResolution ==
  .ifElse .teamwork (.unlessPays .counter 4) (.unlessPays .counter 2)
#guard (Effect.dealDamageToAttackerOrBlocker 2 4).spellResolution ==
  .ifElse .teamwork (.onPermanent (.dealDamage 4)) (.onPermanent (.dealDamage 2))
#guard Effect.doublePowerAndToughness.spellResolution == .onPermanent .doublePowerAndToughness
#guard (Effect.exileCreatureToughnessAtLeast 4).spellResolution == .onPermanent .exile
#guard Effect.searchLegendaryCreatureToHand.spellResolution == .searchCard
#guard (Effect.destroyLandSearchBasic).spellResolution ==
  .sequence [.onPermanent .destroy, .searchCard .basic .land .ownerMayToBattlefield]
#guard SpellResolution.toPhrase (.fight .announced (.timesPower 2)) "target creature" ==
  "Target creature you control deals damage equal to twice its power to target creature an opponent controls."
#guard SpellResolution.toPhrase (.mutualFight .upToOne) "target creature" ==
  "target creature you control fights up to one other target creature"
#guard SpellResolution.toPhrase
    (.dealDamageToEachCreature 0 .opponentsControl .otherSpellsManaValue) "target creature" ==
  "deals damage to each creature your opponents control equal to the total mana value of other spells you've cast this turn"
#guard SpellResolution.toPhrase (.createTokens .dwarf .chosenX) "" ==
  "create X 2/2 red Dwarf creature tokens"
#guard SpellResolution.toPhrase
    (.createTokens .treasure (.perSubtype .villain)) "" ==
  "Create a Treasure token for each Villain you control"
#guard (Effect.dealDamageToCreature 5).spellResolution ==
  .onPermanent (.dealDamage 5)
#guard (Effect.dealDamageToCreatureExileIfDies 3).spellResolution ==
  .sequence [.replace .diesThisTurn .exile, .onPermanent (.dealDamage 3)]
#guard (Effect.dealDamageToCreatureExileIfDies 3).phrase ==
  "deals 3 damage to target creature. If that creature would die this turn, exile it instead"
#guard SpellResolution.toPhrase (.replace .diesThisTurn .exile) "target creature" ==
  "if target creature would die this turn, exile it instead"
#guard Effect.destroyArtifactOrLandNonflyersCantBlock.resolution ==
  .sequence [.onPermanent .destroy, .creaturesWithoutFlyingCantBlock]
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
#guard (Effect.searchLandTypeToHand "Swamp").resolution ==
  .searchLandTypeToHand "Swamp"
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
#guard Effect.returnFromGraveyardTapped.resolution ==
  .returnFromGraveyardTapped
#guard Effect.returnFromGraveyardToHand.resolution ==
  .returnFromGraveyardToHand
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
#guard (Effect.dealDamageToTargetCreature 2).resolution ==
  .onPermanent (.dealDamage 2)
#guard Effect.destroyTargetColorlessNonland.resolution ==
  .onPermanent .destroy
#guard Effect.destroyTargetPermanent == Effect.destroyTarget .permanent
#guard Effect.destroyTargetArtifactOrEnchantment ==
  Effect.destroyTarget .artifactOrEnchantment
#guard Effect.destroyTargetNoncreatureArtOrEnch ==
  Effect.destroyTarget .noncreatureArtifactOrEnchantment
#guard Effect.destroyTargetNoncreatureArtOrEnch.phrase ==
  "Destroy target noncreature artifact or noncreature enchantment"
#guard Effect.destroyCreature ==
  Effect.destroyTarget .creature (spellKind := some .destroyCreature)
#guard Effect.destroyTargetArtifact ==
  Effect.destroyTarget .artifact (spellKind := some .destroyArtifactOrLand)
#guard Effect.destroyTargetPermanent.resolution ==
  Effect.destroyTargetColorlessNonland.resolution
#guard Effect.destroyTargetPermanent.abilityKind ==
  Effect.destroyTargetColorlessNonland.abilityKind
#guard Effect.targetCantBeBlockedThisTurn.resolution ==
  .onPermanent .cantBeBlocked
#guard (Effect.sourceGets 1 0).resolution == .onSource (.pump 1 0)
#guard (Effect.putPlusOnePlusOneOnSource 3).resolution == .onSource (.plusOne 3)
#guard Effect.becomeBearCreatureWithLandsPT.resolution ==
  .becomeSubtypeWithLandsPT .bear
#guard (Effect.becomeSubtypeWithLandsPT "Elf").phrase ==
  "This enchantment becomes an Elf creature in addition to its other types and gains \"This creature's power and toughness are each equal to the number of lands you control.\""
#guard (Effect.searchBasicBeholdSubtypeUntap "Elf").resolution ==
  .searchBasicBeholdSubtypeUntap .elf
#guard (Effect.searchBasicBeholdSubtypeUntap "Orc").phrase.endsWith
  "You may behold an Orc. If you do, untap that land"
#guard Effect.addAnyColorSpendOnlyHero.resolution ==
  .addAnyColorSpendOnlySubtype .hero
#guard Effect.addAnyColorSpendOnlyVillain.resolution ==
  .addAnyColorSpendOnlySubtype .villain
#guard (Effect.teamGain #[Keyword.doubleStrike]).phrase ==
  "Creatures you control gain double strike until end of turn"
#guard (Effect.becomeTypes #["Dinosaur", "Hero"] 3 5
    #[Keyword.reach, Keyword.vigilance]).phrase ==
  "Until end of turn, this becomes a Dinosaur Hero with base power and toughness 3/5 and gains reach and vigilance"
#guard (Effect.millThenPutSubtypeOrEnchantment 4 "Hero").phrase ==
  "Mill 4 cards. You may put a Hero or enchantment card from among those cards into your hand"
#guard (Effect.lookAtTopPutTypes 7 #["Hero", "Equipment", "Vehicle"]).phrase.startsWith
  "Put two +1/+1 counters on this, then look at the top 7 cards"
#guard Effect.searchBasicLandTapped.resolution == .searchBasicLand
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
#guard TriggeredAbility.resolution (.onEnterCreateTokens .treasure 1) ==
  .createTokens .treasure (.fixed 1) false
#guard TriggeredAbility.resolution (.onEnterCreateTokens .treasure 1 true) ==
  .createTokens .treasure (.fixed 1) true
#guard TriggeredAbility.onEnterScry 2 == .triggered .enter (Effect.ofTrigger (.scry 2))
#guard TriggeredAbility.onAttackScry 1 == .triggered .attack (Effect.ofTrigger (.scry 1))
#guard TriggeredAbility.onEnterDraw 1 == .triggered .enter (Effect.ofTrigger (.draw 1))
#guard TriggeredAbility.onDiesDraw 1 == .triggered .dies (Effect.ofTrigger (.draw 1))
#guard TriggeredAbility.onEnterCreateTokens .treasure 1 true ==
  .triggered .enter (Effect.ofTrigger (.createTokens .treasure 1 true))
#guard TriggeredAbility.onEnterOrAttackDealDividedDamage 3 3 ==
  .triggered .enterOrAttack (Effect.ofTrigger (.dividedDamage 3 3))
#guard TriggeredAbility.onEnterTargetOpponentSacrifices ==
  .triggered .enter (Effect.ofTrigger .opponentSacrificesCreature)
#guard TriggeredAbility.onEnterAttachToLegendary ==
  .triggered .enter (Effect.ofTrigger (.attachTo .legendaryCreatureYouControl))
#guard TriggeredAbility.onCombatPlusOneOnCreatureYouControl ==
  .triggered .yourBeginCombat (Effect.ofTrigger (.onPermanent .creatureYouControl (.plusOne 1)))
#guard TriggeredAbility.onEnterOrAttackCreateWall ==
  .triggered .enterOrAttack (Effect.ofTrigger (.createTokens .wall 1))
#guard TriggeredAbility.onEnterConnive == .triggered .enter (Effect.ofTrigger .connive)
#guard TriggeredAbility.onDrawSecondPlusOne ==
  .triggered .youDrawSecond (Effect.ofTrigger (.onSource (.plusOne 1)))
#guard TriggeredAbility.onYourEndStepDrawLoseLife ==
  .triggered .yourEndStep Effect.seqDrawAndLoseLife
#guard TriggeredAbility.onAttackFerociousGainLife 2 ==
  .triggered .attack (Effect.ofTrigger (.gainLife 2)) .ferocious
#guard TriggeredAbility.onArtifactYouControlEntersDrawOnce ==
  .triggered .artifactYouControlEnters (Effect.ofTrigger (.draw 1)) .once
#guard TriggeredAbility.onCastColorPump .green 4 4 ==
  .triggered (.youCastColor .green) (Effect.ofTrigger (.onPermanent .creature (.pump 4 4)))
#guard TriggeredAbility.onEnterExileOppTappedUntilLeaves ==
  .triggered .enter (Effect.ofTrigger (.exileUntilLeaves .oppTappedCreature))
#guard TriggeredAbility.onOpponentCastsFirstNoncreatureRecruit ==
  .triggered .opponentCastsFirstNoncreature (Effect.ofTrigger (.recruit .you))
#guard TriggeredAbility.onCastInstantOrSorceryDealDamageToEachOpponent 2 ==
  .triggered .youCastInstantOrSorcery (Effect.ofTrigger (.damageEachOpponent 2)) .noTarget
#guard TriggeredAbility.onEnterExileTop == .triggered .enter (Effect.ofTrigger .exileTop)
#guard TriggeredAbility.onEnterMayDiscardDraw 2 ==
  .triggered .enter (Effect.ofTrigger (.mayTo .discard (.draw 2)))
#guard (TriggeredAbility.onEnterMayDiscardDraw 2).resolution ==
  .may (.discard (.cards 1)) (.draw (.fixed 2)) .ifYouDo
#guard (TriggeredAbility.triggered .enter
    (Effect.ofTrigger (.mayTo (.scry 1) (.gainLife 2)))).resolution ==
  .may (.scry (.fixed 1)) (.gainLife (.fixed 2)) .ifYouDo
#guard (TriggeredAbility.triggered .enter
    (Effect.ofTrigger (.mayTo (.onPermanent .creature .tap) (.draw 1)))).targetSpec ==
  .creature
#guard (TriggeredAbility.triggered .enter
    (Effect.ofTrigger (.mayTo (.discard 1) (.millPlayer 3)))).targetSpec ==
  .player
#guard TriggeredAbility.onCastNoncreatureMayDrawXDiscard2 ==
  .triggered .youCastNoncreature (Effect.ofTrigger (.may (.drawXDiscard 2)))
#guard (TriggeredAbility.onCastNoncreatureMayDrawXDiscard2).resolution ==
  .may (.sequence [.draw .equalToManaSpent, .«if» .manaSpent (.discard (.cards 2))]) (.sequence [])
#guard TriggeredAbility.toNotation .onCastNoncreatureMayDrawXDiscard2 ==
  "Whenever you cast a noncreature spell, you may draw X cards, where X is the amount of mana spent to cast that spell. If you do, discard two cards."
#guard TriggeredAbility.onEnterEachOpponentDiscards ==
  .triggered .enter (Effect.ofTrigger .opponentDiscards)
#guard TriggeredAbility.onAttackOtherGets2AndTrample ==
  .triggered .attack (Effect.ofTrigger (.onPermanent .anotherCreatureYouControl (.pumpAndTrample 2 0)))
#guard TriggeredAbility.onEquipmentYouControlEntersDraw ==
  .triggered .equipmentYouControlEnters (Effect.ofTrigger (.draw 1))
#guard TriggeredAbility.onCreatureYouControlAttacksAloneInvestigate ==
  .triggered .creatureYouControlAttacksAlone (Effect.ofTrigger .investigate)
#guard TriggeredAbility.onOpponentCastsAmassOrcs 1 ==
  .triggered .opponentCastsSpell (Effect.ofTrigger (.amass 1 .orc))
#guard !TriggeredAbility.requiresTarget
  (.onCastInstantOrSorceryDealDamageToEachOpponent 2)
#guard TriggeredAbility.onEnterSearchForest == .triggered .enter (Effect.ofTrigger .searchLibrary)
#guard TriggeredAbility.onEnterEachPlayerSacrificesCreature ==
  .triggered .enter (Effect.ofTrigger .eachPlayerSacrificesCreature)
#guard TriggeredAbility.onCombatDamageToPlayerLoot ==
  .triggered .combatDamageToPlayer (Effect.seqDrawThenDiscard 1)
#guard TriggeredAbility.onAttackFerociousPlusOneEach ==
  .triggered .attack (Effect.ofTrigger .plusOneEachYouControl) .ferocious
#guard TriggeredAbility.onScryPumpSelfForEachLookedAt ==
  .triggered .youScry (Effect.ofTrigger .pumpByLookedAt)
#guard TriggeredAbility.onScryPumpAndUnblockableOnce ==
  .triggered .youScry Effect.seqPumpAndUnblockable .once
#guard TriggeredAbility.onRingTemptsMayDiscardDraw 4 ==
  .triggered .theRingTemptsYou (Effect.ofTrigger (.mayDiscardHandDraw 4))
#guard TriggeredAbility.onDrawSecondPlusOneLifelink ==
  .triggered .youDrawSecond (Effect.seqPlusOneAndLifelink .creature)
#guard TriggeredAbility.onceEachTurn .onScryPumpAndUnblockableOnce
#guard TriggeredAbility.youControlCreatureWithPower? .onAttackFerociousPlusOneEach
  == some 4
#guard TriggeredAbility.allowsZeroTargets .onEnterMayExileAnotherCreature
#guard TriggeredAbility.onAttackPumpByGreatestPower ==
  .triggered .attack (Effect.ofTrigger .pumpGreatestPower)
#guard TriggeredAbility.onBecomesBlockedDeal1ToBlockers ==
  .triggered .becomesBlocked (Effect.ofTrigger (.damageBlockers 1))
#guard TriggeredAbility.onEnterCreateThenAttach .treasure ==
  .triggered .enter (Effect.ofTrigger (.createThenAttach .treasure))
#guard TriggeredAbility.resolution (.onEnterCreateThenAttach .dwarf) ==
  .sequence [.createTokens .dwarf (.fixed 1) false, .attach .source .createdToken]
#guard TriggeredAbility.toNotation (.onEnterCreateThenAttach .dwarf) ==
  "When this permanent enters, create a 2/2 red Dwarf creature token, then attach this Equipment to it."
#guard TriggeredAbility.resolution (.onEnterGainLifeSearchBasicOnTop 2) ==
  .sequence [.gainLife (.fixed 2), .searchLibrary (.put .basicLandOnTop)]
#guard TriggeredAbility.toNotation (.onEnterGainLifeSearchBasicOnTop 2) ==
  "When this permanent enters, you gain 2 life. You may search your library for a basic land card, reveal it, then shuffle and put that card on top."
#guard TriggeredAbility.onLandYouControlEntersDrawPlusOneSource ==
  .triggered .landYouControlEnters Effect.seqDrawPlusOneSource
#guard TriggeredAbility.onArmyCombatDamageRingTempts ==
  .triggered .armyYouControlCombatDamage (Effect.ofTrigger .ringTempts)
#guard TriggeredAbility.onAttackSetOtherBasePT ==
  .triggered .attack (Effect.ofTrigger .setOtherBasePT)
#guard TriggeredAbility.onEnterOrAttackReturnElfGainLife ==
  .triggered .enterOrAttack (Effect.ofTrigger .returnElfGainLife)
#guard TriggeredAbility.resolution .onEnterOrAttackReturnElfGainLife ==
  .sequence [.returnToHand .graveyardCard, .gainLife .equalToTargetPower]
#guard TriggeredAbility.onDiesDealDamageEqualToPowerToOppCreature ==
  .triggered .dies (Effect.ofTrigger .damageFromLastKnownPower)
#guard TriggeredAbility.onCastNoncreaturePumpAndDamageOpponents 1 ==
  .triggered .youCastNoncreature (Effect.seqPumpAndDamageOpponents 1)
#guard TriggeredAbility.onEnterExileOppGyCardOppsLoseLife 2 ==
  .triggered .enter (Effect.seqExileOppGyCardOppsLoseLife 2)
#guard TriggeredAbility.onEnterCreaturesYouControlGetAndFirstStrike 1 ==
  .triggered .enter (Effect.seqCreaturesPumpAndFirstStrike 1)
#guard TriggeredAbility.onAnotherCreatureYouControlPowerAtMostEntersMayPayDraw 2 1 ==
  .triggered .anotherCreatureYouControlEnters (Effect.ofTrigger (.mayPayGenericDraw 1))
    { anotherCreaturePowerAtMost := some 2 }
#guard TriggeredAbility.anotherCreaturePowerAtMost?
  (.onAnotherCreatureYouControlPowerAtMostEntersMayPayDraw 2 1) == some 2
#guard TriggeredAbility.onEnterDrawThenBottomIfNoLegendary ==
  .triggered .enter (Effect.ofTrigger .drawThenBottomIfNoLegendary)
#guard TriggeredAbility.resolution .onEnterDrawThenBottomIfNoLegendary ==
  .sequence [.draw (.fixed 1), .«if» (.not (.atLeast (.count .legendaryCreaturesYouControl) (.fixed 1))) (.putOnLibrary .bottom .cardFromHand)]
#guard TriggeredAbility.toNotation .onEnterDrawThenBottomIfNoLegendary ==
  "When this permanent enters, draw a card. Then if you don't control a legendary creature, put a card from your hand on the bottom of your library."
#guard TriggeredAbility.onYourEndStepRemoveHopeDrawSac ==
  .triggered .yourEndStep (Effect.ofTrigger .removeHopeDrawSac)
#guard TriggeredAbility.resolution .onYourEndStepRemoveHopeDrawSac ==
  .sequence [.removeCounters .hope .source, .«if» .removedHope (.draw (.fixed 1)),
    .«if» (.not .hopeOnSource) (.sequence [.sacrifice .source, .gainLife (.fixed 4)])]
#guard TriggeredAbility.toNotation .onYourEndStepRemoveHopeDrawSac ==
  "At the beginning of your end step, remove a hope counter from this. If you do, draw a card. Then if this has no hope counters on it, sacrifice it and you gain 4 life."
#guard TriggeredAbility.onAttackTapHumansDraw ==
  .triggered .attack (Effect.ofTrigger .tapHumansDraw)
#guard TriggeredAbility.resolution .onAttackTapHumansDraw ==
  .sequence [.may (.tap .humans) (.sequence []), .draw .forEachTappedHuman]
#guard TriggeredAbility.toNotation .onAttackTapHumansDraw ==
  "Whenever this creature attacks, you may tap any number of untapped Humans you control. Draw a card for each Human tapped this way."
#guard TriggeredAbility.onEnterUntapOtherPlusOneIfSubtype "Bear" ==
  .triggered .enter (Effect.seqUntapPlusOneIfSubtype "Bear")
#guard TriggeredAbility.onEnterDestroyOppArtifactsEnchantmentsGainLife ==
  .triggered .enter (Effect.ofTrigger .destroyOppArtifactsEnchantmentsGainLife)
#guard TriggeredAbility.resolution .onEnterDestroyOppArtifactsEnchantmentsGainLife ==
  .sequence [.destroy .oppArtifactsEnchantments (note := .countDestroyed),
    .gainLife .forEachDestroyedThisWay]
#guard TriggeredAbility.toNotation .onEnterDestroyOppArtifactsEnchantmentsGainLife ==
  "When this permanent enters, destroy all artifacts and enchantments your opponents control. You gain 1 life for each permanent destroyed this way."
#guard TriggeredAbility.onEnterOrAttackPlusOneEachOtherGainLife ==
  .triggered (.or .enter .attack) (Effect.ofTrigger .plusOneEachOtherGainLife)
#guard TriggeredAbility.resolution .onEnterOrAttackPlusOneEachOtherGainLife ==
  .sequence [.putCounters (.ofKind .plusOnePlusOne) .eachOther, .gainLife .perOtherCreature]
#guard TriggeredAbility.toNotation .onEnterOrAttackPlusOneEachOtherGainLife ==
  "Whenever this creature enters or attacks, put a +1/+1 counter on each other creature you control. You gain 1 life for each other creature you control."
#guard TriggeredAbility.onAttackDamageEqualSubtypeToEachOpponent "Dwarf" ==
  .triggered .attack (Effect.ofTrigger (.damageEqualSubtypeToEachOpponent .dwarf))
#guard TriggeredAbility.onAttackDamageEqualTreasures ==
  .triggered .attack (Effect.ofTrigger .damageEqualTreasures)
#guard TriggeredAbility.onPlayerCastsSecondSpellLoseLifeCreateTreasure ==
  .triggered .anyPlayerCastsSecondSpell Effect.seqLoseLifeCreateTreasure
#guard TriggeredAbility.onEnterDealDamageDestroyIfSubtype 1 "Dragon" ==
  .triggered .enter (Effect.ofTrigger (.dealDamageDestroyIfSubtype 1 .dragon))
#guard TriggeredAbility.resolution (.onEnterDealDamageDestroyIfSubtype 1 "Dragon") ==
  .sequence [.dealDamage (.fixed 1) .target .markedPermanent,
    .«if» (.dealtDamageToSubtype .dragon) (.destroy .permanentDealtDamage)]
#guard TriggeredAbility.toNotation (.onEnterDealDamageDestroyIfSubtype 1 "Dragon") ==
  "When this permanent enters, it deals 1 damage to any target. If a Dragon is dealt damage this way, destroy it."
#guard TriggeredAbility.onEnterAttachTargetEquipment ==
  .triggered .enter (Effect.ofTrigger .attachEquipmentToCreature)
#guard TriggeredAbility.onAttackDefenderSacsLeastPower ==
  .triggered .attack (Effect.ofTrigger .defenderSacsLeastPower)
#guard TriggeredAbility.onEnterReturnOtherPlusOne ==
  .triggered .enter (Effect.ofTrigger .returnOtherPlusOne)
#guard TriggeredAbility.resolution .onEnterReturnOtherPlusOne ==
  .sequence [.returnToHand .permanent .returnedPermanent, .«if» .returnedPermanent (.putCounters (.ofKind .plusOnePlusOne) .source)]
#guard TriggeredAbility.toNotation .onEnterReturnOtherPlusOne ==
  "When this permanent enters, return up to one other target permanent you control to its owner's hand. If you do, put a +1/+1 counter on this creature."
#guard TriggeredAbility.onEnterLookAtTopRevealTypes 4 #["Dwarf", "Equipment"] ==
  .triggered .enter (Effect.ofTrigger (.lookAtTopRevealTypes 4 #["Dwarf", "Equipment"]))
#guard TriggeredAbility.onEnterCreateTappedTreasuresEqualOppArtifacts ==
  .triggered .enter (Effect.ofTrigger .createTappedTreasuresEqualOppArtifacts)
#guard TriggeredAbility.onCombatDamagePutNonlandMvAtMost 3 ==
  .triggered .combatDamageToPlayerOrBattle (Effect.ofTrigger (.putNonlandMvAtMostFromGy 3))
#guard SharedTriggerWhen.anyPlayerCastsSecondSpell.events ==
  #[.anyPlayerCastsSecondSpell]
#guard SharedTriggerWhen.enterOrAttack == .or .enter .attack
#guard SharedTriggerWhen.enterOrAttack.events == #[.entering, .attacking]
#guard SharedTriggerWhen.castGreenOrForestEnters ==
  .or .youCastGreen .forestYouControlEnters
#guard SharedTriggerWhen.enterOrOpponentDrawsExceptFirst ==
  .or .enter .opponentDrawsExceptFirst
#guard (SharedTriggerWhen.or .enter .attack).events == #[.entering, .attacking]
#guard TriggeredAbility.onEachCombatOthersGetAndOppsGet #["Goblin", "Orc"] 2 2 (-1) (-1) ==
  .triggered .eachBeginCombat (Effect.ofTrigger (.othersGetAndOppsGet #[.goblin, .orc] 2 2 (-1) (-1)))
#guard TriggeredAbility.resolution
    (.onEachCombatOthersGetAndOppsGet #["Goblin", "Orc"] 2 2 (-1) (-1)) ==
  .sequence [.pump (.fixed 2) (.fixed 2) (.intersection [.creaturesYouControl, .union ([.goblin, .orc].map .othersOfSubtype)]),
    .pump (.fixed (-1)) (.fixed (-1)) .opponentsCreatures]
#guard TriggeredAbility.toNotation
    (.onEachCombatOthersGetAndOppsGet #["Goblin", "Orc"] 2 2 (-1) (-1)) ==
  "At the beginning of each combat, other Goblins and Orcs you control get +2/+2 until end of turn. Creatures your opponents control get -1/-1 until end of turn."
#guard TriggeredAbility.onCombatDamageWolfPlusOneOrTreasure ==
  .triggered .combatDamageToPlayer (Effect.ofTrigger .wolfPlusOneOrTreasure)
#guard TriggeredAbility.resolution .onCombatDamageWolfPlusOneOrTreasure ==
  .or [.putCounters (.ofKind .plusOnePlusOne) .permanent, .createTokens .treasure (.fixed 1) false]
#guard (SharedTrigger.timing .tapOppOrUntapYours).resolution ==
  .or [.tap .target, .untap]
#guard TriggeredAbility.resolution .onLandYouControlEntersTapOrUntap ==
  .or [.tap .target, .untap]
#guard TriggeredAbility.onYourBeginCombatTrampleCounterBecomeBear ==
  .triggered .yourBeginCombat (Effect.ofTrigger .trampleCounterBecomeBear)
#guard TriggeredAbility.onEnterMillThenSubtypeToHand 4 "Elf" ==
  .triggered .enter (Effect.ofTrigger (.millThenSubtypeToHand 4 .elf))
#guard TriggeredAbility.onEnterExileOppNonlandEachUntilLeaves ==
  .triggered .enter (Effect.ofTrigger .exileOppNonlandEachUntilLeaves)
#guard TriggeredAbility.onCastCreaturePlusOneEqualMv ==
  .triggered .youCastCreature (Effect.ofTrigger .plusOneEqualLastKnownMv)
#guard TriggeredAbility.onMountainEntersQuestThenDragon ==
  .triggered .mountainYouControlEnters (Effect.ofTrigger .mountainQuestDragon)
#guard TriggeredAbility.onEquippedCombatDamageTreasuresPerChosenType ==
  .triggered .equippedDealsCombatDamageToPlayer (Effect.ofTrigger .treasuresPerChosenType)
#guard TriggeredAbility.onNontokenYouControlDiesRevealCreature ==
  .triggered .nontokenYouControlDies (Effect.ofTrigger .revealUntilCreature) .once
#guard TriggeredAbility.onceEachTurn .onNontokenYouControlDiesRevealCreature
#guard TriggeredAbility.onAttackMaySacAnotherPlusOneEqualPower ==
  .triggered .attack (Effect.ofTrigger .attackSacPlusOneEqualPower)
#guard TriggeredAbility.onEnterLootLandEntersTapped ==
  .triggered .enter (Effect.ofTrigger .lootLandEntersTapped)
#guard TriggeredAbility.onPlayerLosesLifeMillThatMany ==
  .triggered .playerLosesLife (Effect.ofTrigger .millThatManyLost)
#guard TriggeredAbility.onDiesDrawPerFatGraveyard ==
  .triggered .dies (Effect.ofTrigger .drawPerFatGraveyard)
#guard TriggeredAbility.onEnterMaySacDrawTreasure ==
  .triggered .enter (Effect.ofTrigger .maySacDrawTreasure)
#guard TriggeredAbility.onEquippedAttacksPlusOneEachIfCityBlessing ==
  .triggered .equippedAttacks (Effect.ofTrigger (.plusOneEachYouControl .citysBlessing))
#guard TriggeredAbility.onYourBeginCombatCastInstantSorceryFromHand ==
  .triggered .yourBeginCombat (Effect.ofTrigger .castInstantSorceryFromHand)
#guard TriggeredAbility.onEquippedCombatDamageCastInstantSorcery ==
  .triggered .equippedDealsCombatDamageToPlayer (Effect.ofTrigger .castInstantSorceryMvAtMost)
#guard TriggeredAbility.onCastSecondSpellMillThenCopy ==
  .triggered .youCastSecondSpell (Effect.ofTrigger .millThenCopy)
#guard TriggeredAbility.onCombatAnotherGetsSourcePower ==
  .triggered .yourBeginCombat (Effect.ofTrigger .pumpTargetBySourcePower)
#guard TriggeredAbility.onCombatCreateAlienPerInvasion ==
  .triggered .yourBeginCombat (Effect.ofTrigger .createAlienPerInvasion)
#guard TriggeredAbility.onCombatMayPutArtifactAttachEquipment ==
  .triggered .yourBeginCombat (Effect.ofTrigger .mayPutArtifactAttachEquipment)
#guard TriggeredAbility.resolution .onCombatMayPutArtifactAttachEquipment ==
  .sequence [.may (.put .artifactFromHand (note := .forAttach)) (.sequence []),
    .«if» (.atLeast (.count .putEquipment) (.fixed 1)) (.attach .putArtifact .notedHost)]
#guard TriggeredAbility.onCastCascade == .triggered .cascade (Effect.ofTrigger .cascade)
#guard TriggeredAbility.onEnterBolgMaySacrifice ==
  .triggered .enter (Effect.ofTrigger .bolgMaySacrifice)
#guard TriggeredAbility.onEnterSurveil 2 == .triggered .enter (Effect.ofTrigger (.surveil 2))
#guard TriggeredAbility.onWatch Effect.watchHulk == .triggered .fromEffect Effect.watchHulk
#guard TriggeredAbility.onStep Effect.stepDrawToTen ==
  .triggered .fromEffect Effect.stepDrawToTen
#guard TriggeredAbility.sagaChapter 1 Effect.chapterRecruit ==
  .triggered .sagaChapter
    { Effect.chapterRecruit with
      sharedTrigger := some (SharedTrigger.chapter 1 .recruit) }
#guard TriggeredAbility.onceEachTurn .onFinalSagaChapterRevealSaga
#guard TriggeredAbility.onYouSacrificeTokenOppLosesLife ==
  .triggered .youSacrificeToken (Effect.ofTrigger (.targetOpponentLosesLife 1))
#guard TriggeredAbility.onDiesAmassGoblinsEqualPower ==
  .triggered .dies (Effect.ofTrigger (.amass 0 (amount := .sourcePower)))
#guard TriggeredAbility.youControlCreatureWithPower? (.onAttackFerociousGainLife 2)
  == some 4
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
  let ab : ActivatedAbility := {
    cost := CostSpec.ofItems #[.mana (ManaCost.ofGeneric 1), .sacrifice (.exact 1) .self]
    effect := Effect.dealDamageToTargetCreature 2
    otherModes := #[Effect.destroyTargetColorlessNonland]
  }
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
#guard (StaticAbility.cantBeBlockedExcept? (.cantBeBlockedExceptBy 3)) == some 3
#guard StaticAbility.toNotation (.cantBeBlockedIfPowerAtMost 1) ==
  "This creature can't be blocked if its power is 1 or less."
#guard (StaticAbility.cantBeBlockedIfPowerAtMost? (.cantBeBlockedIfPowerAtMost 1)) ==
  some 1
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
#guard TriggeredAbility.resolutionPhrase { resolution := .connive .hand } ==
  "connive"
#guard TriggeredAbility.targetSpec .onCombatAnotherGetsSourcePower ==
  .anotherCreatureYouControl
#guard TriggeredAbility.firesOn .onCombatCreateAlienPerInvasion .yourBeginCombat
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
#guard TriggeredAbility.firesOn (.onDiesOppCreatureGets (-1) (-1)) .dying
#guard TriggeredAbility.firesOn (.onOneOrMoreOtherCreaturesDieScry 1) .oneOrMoreOtherCreaturesDie
#guard !TriggeredAbility.firesOn (.onOneOrMoreOtherCreaturesDieScry 1) .dying
#guard TriggeredAbility.firesOn .onEnterEachPlayerSacrificesCreature .entering
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
#guard TriggerEvent.label .oneOrMoreOtherCreaturesDie == "other-creatures-die trigger"
#guard TriggerEvent.clause .oneOrMoreOtherCreaturesDie ==
  "one or more other creatures die"
#guard !TriggerEvent.checkTargets .oneOrMoreOtherCreaturesDie
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
#guard TriggeredAbility.firesOn .onAttackPumpByGreatestPower .attacking
#guard TriggeredAbility.firesOn .onAttackSetOtherBasePT .attacking
#guard TriggeredAbility.firesOn .onAttackOtherGets2AndTrample .attacking
#guard TriggeredAbility.firesOn (.onAttackScry 1) .attacking
#guard TriggeredAbility.firesOn (.onAttackFerociousGainLife 2) .attacking
#guard TriggeredAbility.firesOn (.onEnterOrAttackDealDividedDamage 3 3) .attacking
#guard TriggeredAbility.firesOn .onEnterOrAttackReturnElfGainLife .attacking
#guard !TriggeredAbility.firesOn (.onEnterDealDividedDamage 3 3) .attacking
#guard !TriggeredAbility.firesOn (.onEnterScry 2) .attacking
#guard !TriggeredAbility.firesOn (.onAttackWithElvesScry 1) .attacking
#guard !TriggeredAbility.firesOn .onScryPumpSelfForEachLookedAt .attacking
#guard TriggeredAbility.firesOn (.onAttackWithElvesScry 1) .youAttackWithElves
#guard !TriggeredAbility.firesOn .onAttackPumpByGreatestPower .youAttackWithElves
#guard !TriggeredAbility.firesOn (.onAttackScry 1) .youAttackWithElves
#guard TriggeredAbility.firesOn .onScryPumpSelfForEachLookedAt .youScry
#guard !TriggeredAbility.firesOn (.onEnterScry 2) .youScry
#guard !TriggeredAbility.firesOn (.onAttackWithElvesScry 1) .youScry
#guard !TriggeredAbility.firesOn (.onAttackScry 1) .youScry
#guard TriggeredAbility.firesOn .onAnotherElfYouControlEntersGets1 .anotherElfYouControlEnters
#guard !TriggeredAbility.firesOn (.onEnterDraw 1) .anotherElfYouControlEnters
#guard !TriggeredAbility.firesOn .onAnotherElfYouControlEntersGets1 .entering
#guard !TriggeredAbility.requiresTarget .onAnotherElfYouControlEntersGets1
#guard (TriggeredAbility.dividedDamage? .onAnotherElfYouControlEntersGets1).isNone
#guard TriggeredAbility.firesOn .onBecomesBlockedDeal1ToBlockers .becomesBlocked
#guard TriggeredAbility.firesOn (.onEnterScry 2) .entering
#guard TriggeredAbility.firesOn (.onEnterDraw 1) .entering
#guard TriggeredAbility.firesOn .onEnterSearchForest .entering
#guard TriggeredAbility.firesOn (.onEnterMayDiscardDraw 2) .entering
#guard TriggeredAbility.firesOn .onEnterTargetOpponentSacrificesCreature .entering
#guard TriggeredAbility.firesOn (.onEnterDealDividedDamage 3 3) .entering
#guard TriggeredAbility.firesOn (.onEnterOrAttackDealDividedDamage 3 3) .entering
#guard TriggeredAbility.firesOn .onEnterOrAttackReturnElfGainLife .entering
#guard !TriggeredAbility.firesOn .onAttackPumpByGreatestPower .entering
#guard !TriggeredAbility.firesOn (.onAttackScry 1) .entering
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
#guard StaticAbility.hostStatBonus (.enchantedCreatureGets 3 3) == (3, 3)
#guard StaticAbility.hostStatBonus (.equippedCreatureGets 2 0) == (2, 0)
#guard StaticAbility.shape (.enchantedCreatureGets 3 3) ==
  .hostGets "Enchanted creature" 3 3
#guard StaticAbility.shape (.equippedCreatureGets 2 0) ==
  .hostGets "Equipped creature" 2 0
#guard (StaticAbility.StaticShape.spec (.hostGets "Enchanted creature" 3 3)).hostBonus ==
  (3, 3)
#guard (StaticAbility.StaticShape.spec (.lordPump #[.elf] 1 1)).lordPump ==
  some (#[.elf], 1, 1)
#guard (StaticAbility.StaticShape.spec (.lordTrample #[.orc])).trampleSubtypes ==
  some #[.orc]
#guard (StaticAbility.StaticShape.spec .landsYouControlPT).landsYouControlPT
#guard (StaticAbility.StaticShape.spec (.cantBlockUnless #[.goblin])).cantBlockUnless ==
  some #[.goblin]
#guard (StaticAbility.lordPump? (.otherCreaturesGet #[.elf] 1 1)) == some (#[.elf], 1, 1)
#guard (StaticAbility.trampleSubtypes? (.otherCreaturesHaveTrample #[.orc])) == some #[.orc]
#guard StaticAbility.isLandsYouControlPT .powerToughnessEqualLandsYouControl
#guard !StaticAbility.isLandsYouControlPT (.enchantedCreatureGets 1 1)
#guard (StaticAbility.cantBlockUnless? (.cantBlockUnlessYouControl #[.goblin])) ==
  some #[.goblin]
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
#guard TriggeredAbility.firesOn .onDiesDealDamageEqualToPowerToOppCreature .dying
#guard !TriggeredAbility.firesOn (.onEnterScry 2) .dying
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
#guard (default : TriggeredAbility.TriggerResolution) ==
  .pump .greatestPower .greatestPower .source
#guard TriggeredAbility.resolution .onAttackSetOtherBasePT ==
  .setBasePT .equalSourcePower .equalSourceToughness
#guard TriggeredAbility.resolution .onAttackOtherGets2AndTrample ==
  .sequence [.pump (.fixed 2) (.fixed 0) .target, .grant (.keywords #[Keyword.trample]) .target]
#guard TriggeredAbility.resolution (.onEnterScry 2) == .scry (.fixed 2)
#guard TriggeredAbility.resolution (.onEnterSurveil 2) == .surveil (.fixed 2)
#guard TriggeredAbility.resolutionPhrase { resolution := .surveil .perOtherCreature } ==
  "surveil"
#guard TriggeredAbility.resolutionPhrase { resolution := .attach .source .source } ==
  "attach it"
#guard TriggeredAbility.resolutionPhrase { resolution := .empowerJace (.fixed 2) } ==
  "empower Jace 2"
#guard TriggeredAbility.resolutionPhrase { resolution := .empowerJace .perOtherCreature } ==
  "empower Jace"
#guard TriggeredAbility.resolutionPhrase
    { resolution := .spellsCostLess (.cardType .artifact) (.fixed 1) } ==
  "spells you cast this turn cost {1} less to cast"
#guard TriggeredAbility.resolutionPhrase
    { resolution := .spellsCostLess (.cardType .artifact) .perOtherCreature } ==
  "spells you cast this turn cost less to cast"
#guard TriggeredAbility.resolutionPhrase
    { resolution := .becomePT (.fixed 2) (.fixed 2) } ==
  "you may have this creature's base power and toughness become 2/2 until end of turn"
#guard TriggeredAbility.resolutionPhrase
    { resolution := .becomePT .perOtherCreature (.fixed 2) } ==
  "you may have this creature's base power and toughness become those values until end of turn"
#guard TriggeredAbility.resolutionPhrase
    { resolution := .lookAtTopRevealTypes .perOtherCreature #["Dwarf"] } ==
  "look at the top cards of your library"
#guard TriggeredAbility.toNotation (.onEnterSurveil 1) ==
  "When this permanent enters, surveil 1."
#guard TriggeredAbility.toNotation (.onEnterEnchanted (.grantKeywords #[Keyword.firstStrike])) ==
  "When this Aura enters, enchanted creature gains first strike until end of turn."
#guard TriggeredAbility.toNotation (.onEnterEnchanted .tap) ==
  "When this Aura enters, tap enchanted creature."
#guard TriggeredAbility.resolution (.onEnterEnchanted .tap) == .tap .enchantedWhileSource
#guard TriggeredAbility.toNotation (.onEnterAttachThen (.grantKeywords #[Keyword.indestructible])) ==
  "When this Equipment enters, attach it to target creature you control. That creature gains indestructible until end of turn."
#guard TriggeredAbility.toNotation (.onEnterAttachThen .untap) ==
  "When this Equipment enters, attach it to target creature you control. Untap that creature."
#guard TriggeredAbility.targetSpec (.onEnterAttachThen .untap) == .creatureYouControl
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
  .or [.createTokens .food (.fixed 1) false, .createTokens .treasure (.fixed 1) false]
#guard TriggeredAbility.resolution (.onEnter Effect.enterPlusOnesOrReturnArtEnch) ==
  .or [.putCounters (.ofKind .plusOnePlusOne) .permanent, .returnToHand .graveyardCard]
#guard TriggeredAbility.toNotation (.onEnter Effect.enterPlusOnesOrReturnArtEnch) ==
  "When this permanent enters, choose one — • Put a +1/+1 counter on each of up to two target creatures. • Return target artifact or enchantment card from your graveyard to your hand."
#guard TriggeredAbility.toNotation .onEnterVillainIfGyElseMill ==
  "When this creature enters, create a tapped 2/1 black Villain creature token with menace if there are two or more creature cards in your graveyard. Otherwise, mill two cards."
#guard TriggeredAbility.resolution .onEnterVillainIfGyElseMill ==
  .ifElse ((.atLeast (.count .creatureCardsInGraveyard) (.fixed 2)))
    (.createTokens .villain21menace (.fixed 1) true) (.mill (.fixed 2))
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
    (.triggered .yourBeginCombat (Effect.ofTrigger .pumpOrCounterIfScried)) ==
  "At the beginning of combat on your turn, another target creature you control gets +1/+1 until end of turn. If you've scried or surveilled this turn, put a +1/+1 counter on that creature instead."
#guard (SharedTrigger.timing .pumpOrCounterIfScried).resolution ==
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
  .sequence [.createTokens .sturdyShield (.fixed 1) false (note := .remember),
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
#guard StaticAbility.toNotation .improvise == "Improvise"
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
#guard StaticAbility.toNotation (.sneak (ManaCost.ofGenericAndColors 1 [.black, .black])) ==
  "Sneak {1}{B}{B}"
#guard StaticAbility.toNotation .boast ==
  "Boast — Exile any number of black cards from your graveyard with fifteen or more black mana symbols among their mana costs: Copy those exiled cards. You may cast up to three of the copies without paying their mana costs."
#guard TriggeredAbility.resolution (.onAttackScry 1) == .scry (.fixed 1)
#guard TriggeredAbility.resolution (.onAttackFerociousGainLife 2) == .gainLife (.fixed 2)
#guard TriggeredAbility.youControlCreatureWithPower? (.onAttackFerociousGainLife 2) == some 4
#guard (TriggeredAbility.youControlCreatureWithPower? (.onAttackScry 1)).isNone
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
#guard TriggeredAbility.resolutionPhrase { resolution := .amass .perOtherCreature } ==
  "amass"
#guard TriggeredAbility.resolution .onOpponentCastsFirstNoncreatureRecruit == .recruit .you
#guard TriggeredAbility.resolution .onEnterRecruit == .recruit
#guard TriggeredAbility.onCombatDamageToPlayerLoot.effect.resolution ==
  .sequence [.draw 1, .discard (.cards 1)]
#guard TriggeredAbility.resolution .onEnterEachOpponentDiscards ==
  .discard (.cards 1 .eachOpponent)
#guard TriggeredAbility.resolution (.onEnterTargetOpponentDiscards 2) ==
  .discard (.cards 2 (.target .opponent))
#guard TriggeredAbility.resolution .onAttackFerociousPlusOneEach ==
  .putCounters (.ofKind .plusOnePlusOne) .youControl
#guard TriggeredAbility.resolution .onEnterCreateAxe ==
  .createTokens .axe (.fixed 1) false
#guard TriggeredAbility.resolution .onEnterCreateAxeAttach ==
  .createTokens .axe (.fixed 1) false (note := .attachReflexive)
#guard TriggeredAbility.resolution .onEquippedAttacksPlusOneEachIfCityBlessing ==
  .putCounters (.ofKind .plusOnePlusOne) (.youControl .citysBlessing)
#guard TriggeredAbility.resolution
    (.onStep (Effect.ofTrigger .prepareSource)) == .prepareSource
#guard TriggeredAbility.resolution
    (.onStep (Effect.ofTrigger (.prepareSource .ifThreeCreaturesDied))) ==
  .prepareSource .ifThreeCreaturesDied
#guard (TriggeredAbility.triggered .youScryOrSurveil
    (Effect.ofTrigger (.mayPayGenericDraw 2 (plusOneOnSource := true)))).resolution ==
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
#guard TriggeredAbility.toNotation (TriggeredAbility.triggered .youScryOrSurveil
    (Effect.ofTrigger (.mayPayGenericDraw 2 (plusOneOnSource := true)))) ==
  "Whenever you scry or surveil, you may pay {2}. If you do, put a +1/+1 counter on this creature and draw a card."
#guard TriggeredAbility.toNotation
    (.onAnotherCreatureYouControlPowerAtMostEntersMayPayDraw 2 1) ==
  "Whenever another creature you control with power 2 or less enters, you may pay {1}. If you do, draw a card."
#guard TriggeredAbility.resolution .onAttackWithTwoOrMoreGrantFlying ==
  .grant (.keywords #[Keyword.flying]) .target
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
#guard TriggeredAbility.resolution (.onLandYouControlEntersGets 1 1) ==
  .pump (.fixed 1) (.fixed 1) .source
#guard TriggeredAbility.resolution .onLandYouControlEntersPlusOnePlusOne ==
  .putCounters (.ofKind .plusOnePlusOne) .permanent
#guard TriggeredAbility.resolution .onAnotherElfYouControlEntersGets1 ==
  .pump (.fixed 1) (.fixed 1) .source
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
  .sequence [.createTokens .spirit (.fixed 2) true, .«if» (.atLeast (.count (.intersection [.equipped, .legendaryCreaturesYouControl])) (.fixed 1)) .markRecentTokensAttacking]
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
  .sequence [.createTokens .alien (.fixed 1) false (note := .invasion),
    .putCounters .plusOneNoted .createdToken,
    .putCounters (.ofKind .invasion) .source]
#guard (SharedTrigger.timing .drawTwoWinIfEmptyShuffleSource).resolution ==
  .sequence [.draw (.fixed 2), .«if» (.not (.atLeast .libraryCards (.fixed 1))) .winTheGame, .«if» (.atLeast .libraryCards (.fixed 1)) .shuffleSource]
#guard (SharedTrigger.timing .surveilReturnIfGainedLife).resolution ==
  .sequence [.armSurveilReturnLifeGained, .surveil (.fixed 1)]
#guard (SharedTrigger.timing (.grantThenCounterByType #[Keyword.hexproof])).resolution ==
  .sequence [.grant (.keywords #[Keyword.hexproof]) .target,
    .«if» (.atLeast (.count (.target .creature)) (.fixed 1)) (.putCounters (.ofKind .plusOnePlusOne) .permanent),
    .«if» (.atLeast (.count (.target .planeswalker)) (.fixed 1)) (.putCounters (.ofKind .loyalty) .permanent)]
#guard (SharedTrigger.timing .beginCombatIfDrawnTwoPump).resolution ==
  .«if» (.atLeast .cardsDrawnThisTurn (.fixed 2)) (.sequence [
    .pump (.fixed 3) (.fixed 0) .target,
    .grant (.keywords #[Keyword.firstStrike]) .target])
#guard (SharedTrigger.timing .destroyOppPermanentIfSixLands).resolution ==
  .«if» ((.atLeast (.count .landsYouControl) (.fixed 6))) (.sequence [
    .destroy .target,
    .createTokens .treasure (.fixed 1) false (who := .controller .target)])
#guard TriggeredAbility.toNotation
    (.triggered .enter (Effect.ofTrigger .destroyOppPermanentIfSixLands)) ==
  "When this permanent enters, if you control six or more lands, destroy target permanent an opponent controls. They create a Treasure token."
#guard TriggeredAbility.toNotation .onYourBeginCombatIfDrawnTwoPumpFirstStrike ==
  "At the beginning of combat on your turn, if you've drawn two or more cards this turn, another target creature you control gets +3/+0 and gains first strike until end of turn."
#guard (SharedTrigger.timing (.drawXDiscard 2)).resolution ==
  .sequence [.draw .equalToManaSpent, .«if» .manaSpent (.discard (.cards 2))]
#guard TriggeredAbility.resolution .onDiesDrawPerFatGraveyard ==
  .draw .perFatGraveyard
#guard (SharedTrigger.timing (.enter .createSturdyShieldAttach)).resolution ==
  .sequence [.createTokens .sturdyShield (.fixed 1) false (note := .remember),
    .attach .createdToken .source]
#guard (SharedTrigger.timing (.enter .tapLoseAbilitiesWhileSource)).resolution ==
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
  HasTextChange.applyTextChanges tcs (Resolution.createTokens .dwarf (.fixed 2) false) ==
    Resolution.createTokens (TokenSpec.creature #[.bear] 2 2 (ColorSet.singleton .blue)) (.fixed 2) false &&
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
      (ab.mana?.map (·.spec)) == some (.fixed #[.colored .green, .colored .green, .colored .green])
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
-- default `Effect := {}` (resolution `.draw (.fixed 0) .you`) does NOT trip criterion 4.
#guard (ActivatedAbility.manaSimple (.colored .green)).isManaAbility
#guard (ActivatedAbility.intrinsicBasicLandMana .red).isManaAbility
-- Fails criterion 1 (requires target).
#guard !({ cost := CostSpec.tapOnly, mana? := some { spec := .fixedOne (.colored .green) },
           effect := { targeting := .of TargetSpec.creature } } : ActivatedAbility).isManaAbility
-- Fails criterion 2 (does not add mana).
#guard !({ cost := CostSpec.tapOnly, effect := Effect.gainLife 1 } : ActivatedAbility).isManaAbility
-- Fails criterion 3 (loyalty ability, CR 606.2).
#guard !({ cost := CostSpec.ofLoyalty (.plus 1), timing := .loyalty,
           mana? := some { spec := .fixedOne (.colored .red) } } : ActivatedAbility).isManaAbility
-- Fails criterion 4 (effect moves cards from library).
#guard !({ cost := CostSpec.tapOnly, mana? := some { spec := .fixedOne (.colored .green) },
           effect := Effect.draw 1 } : ActivatedAbility).isManaAbility
-- Fails criterion 4 (cost exiles from library).
#guard !({ cost := CostSpec.ofItems #[.tapSelf, .exile (.exact 1) { zones := #[.library], owner := .ofPlayer .you } (.filter .isCard)],
           mana? := some { spec := .fixedOne (.colored .green) } } : ActivatedAbility).isManaAbility
-- Fails criterion 4 (sibling library-moving `Resolution` and `FrcEffect` ctors),
-- while `.scry` only reorders cards inside a library and remains a mana ability.
#guard [Resolution.clashOfElements, .entrustTheSpark, .sphinxsApproach,
        .jiangYangguAlone, .exileOpponentLibrariesButBottom,
        .riddlesInTheDark 4, .identityEcho, .eyeOfJace, .frc .explore].all fun r =>
  !({ cost := CostSpec.tapOnly, mana? := some { spec := .fixedOne (.colored .green) },
      effect := { resolution := r } } : ActivatedAbility).isManaAbility
#guard ({ cost := CostSpec.tapOnly, mana? := some { spec := .fixedOne (.colored .green) },
          effect := { resolution := .scry (.fixed 1) } } : ActivatedAbility).isManaAbility
-- Modal activated abilities follow the exact four CR 605.1a criteria across every mode:
-- untargeted non-library modal abilities that could add mana ARE mana abilities,
-- while a targeted or library-moving mode in `otherModes` disqualifies them.
#guard ({ cost := CostSpec.tapOnly, mana? := some { spec := .fixedOne (.colored .green) },
          otherModes := #[Effect.gainLife 1] } : ActivatedAbility).isManaAbility
#guard ({ cost := CostSpec.tapOnly, effect := Effect.addMana #[.colored .red],
          otherModes := #[Effect.addMana #[.colored .green]] } : ActivatedAbility).isManaAbility
#guard ({ cost := CostSpec.tapOnly, effect := Effect.gainLife 1,
          otherModes := #[Effect.addMana #[.colored .red]] } : ActivatedAbility).isManaAbility
#guard !({ cost := CostSpec.tapOnly, mana? := some { spec := .fixedOne (.colored .green) },
           otherModes := #[{ targeting := .of TargetSpec.creature, resolution := .gainLife 1 }] } : ActivatedAbility).isManaAbility
#guard !({ cost := CostSpec.tapOnly, mana? := some { spec := .fixedOne (.colored .green) },
           otherModes := #[Effect.draw 1] } : ActivatedAbility).isManaAbility

-- Functorial `HasTextChange` on `ManaSpec`, `ManaProductionSpec`, `ActivationCostReduction`,
-- `ActivationMechanicTag`, and `ActivatedAbility` (CR 612.2 / 613.1c).
#guard
  let tcs := #[TextChange.replaceCreatureType .elf .goblin]
  let ab := ActivatedAbility.manaAbility
    (.sequence #[(.colored .green, ValueExpr.count (.controlledOfSubtype .elf))])
    (restriction := some (.subtypeSpellOrSource .elf))
  let ab' := HasTextChange.applyTextChanges tcs ab
  ab'.mana? == some {
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

end Mtg.Engine

