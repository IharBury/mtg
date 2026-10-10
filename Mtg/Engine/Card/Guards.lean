import Mtg.Engine.Card.CardDef

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
#guard CardDef.isKeywordRestatement Keyword.haste "Haste"
#guard !CardDef.isKeywordRestatement Keywords.none "({T}: Add {R}.)"
#guard CardDef.isKeywordRestatement Keyword.flash "Flash"
#guard CardDef.isKeywordRestatement Keyword.vigilance "Vigilance"
#guard CardDef.isKeywordRestatement (Keyword.reach.merge Keyword.deathtouch)
  "Reach, deathtouch"
#guard !CardDef.isKeywordRestatement Keyword.flying "Flash"
#guard toString Keyword.hexproof == "hexproof"
#guard CardDef.isKeywordRestatement Keyword.hexproof "Hexproof"
#guard toString Keyword.indestructible == "indestructible"
#guard CardDef.isKeywordRestatement Keyword.indestructible "Indestructible"
#guard CardDef.isAdventureDelimiter "//ADV//"
#guard CardDef.isAdventureDelimiter "//ADV// Spew Flame {4}{R}"
#guard !CardDef.isAdventureDelimiter "Spew Flame {4}{R}"
#guard CardDef.stripAdventureDelimiter "//ADV//" == none
#guard CardDef.stripAdventureDelimiter "//ADV// Spew Flame {4}{R}" ==
  some "Spew Flame {4}{R}"
#guard (Effect.dealDamage 3).targetKind == .playerOrCreature
#guard (Effect.dealDamage 3).resolution == Resolution.onPermanent (.dealDamage 3)
#guard (Effect.dealDamage 3).phrase == "deals 3 damage to any target"
#guard (Effect.dealDamage 3).spellResolution == .onPermanent (.dealDamage 3)
#guard (Effect.draw 2).resolution == Resolution.draw 2
#guard (Effect.scry 1).resolution == Resolution.scry 1
#guard (Effect.gainLife 3).resolution == .gainLife 3
#guard Resolution.toPhrase (.gainLife 3) "target creature" == "You gain 3 life"
#guard Resolution.toPhrase (.spell (.draw 2)) "target player" == "draw 2 cards"
#guard Resolution.toPhrase (.sequence [.draw 1, .discard 1]) "target creature" ==
  "Draw a card. Discard a card"
#guard Resolution.toPhrase (.createTokens .treasure 1 (tapped := true)) "" ==
  "Create a tapped Treasure token"
#guard (Effect.drawLoseLifeThenAmass 2).resolution ==
  Resolution.sequence [.draw 1, .fra (.loseLife 1), .spell (.amassGoblins 2)]
#guard (Effect.createTokensThenTeamPump .villain21menace 1 1 0).resolution ==
  Resolution.sequence
    [.createTokens .villain21menace 1, .creaturesYouControlPump 1 0]
#guard (Effect.createTokens .treasure 1).spellResolution == .createTokens .treasure 1
#guard (Effect.targetPlayerCreatesTokens .leviathan65hexproof 1).spellResolution ==
  .createTokens .leviathan65hexproof 1 .targetPlayer
#guard (Effect.targetPlayerCreatesTokens .leviathan65hexproof 1).resolution ==
  .spell (.createTokens .leviathan65hexproof 1 .targetPlayer)
#guard SpellResolution.toPhrase (.createTokens .treasure 1 .you) "target player" ==
  "create a Treasure token"
#guard SpellResolution.toPhrase
    (.createTokens .leviathan65hexproof 1 .targetPlayer) "target player" ==
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
    .«if» (.may .attachEquipment) (.subtype "Dwarf")]
#guard (Effect.untapPumpMaybeAttach 2 2).phrase ==
  "untap target creature you control. It gets +2/+2 until end of turn. If it's a Dwarf, you may attach an Equipment you control to it"
#guard SpellResolution.toPhrase (.«if» (.draw 1) (.subtype "Elf")) "target creature" ==
  "if target creature is an Elf, draw a card"
#guard SpellResolution.toPhrase (.may (.gainLife 3)) "target creature" ==
  "you may gain 3 life"
#guard SpellResolution.toPhrase (.may .attachEquipment) "target creature" ==
  "you may attach an Equipment you control to it"
#guard SpellResolution.toPhrase (.«if» (.may .attachEquipment) (.subtype "Dwarf")) "target creature" ==
  "if target creature is a Dwarf, you may attach an Equipment you control to it"
#guard SpellResolution.toPhrase (.«if» .recruit (.mvAtMost 2)) "target spell" ==
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
    .onPermanent (.grantKeywords (Keyword.lifelink.merge Keyword.indestructible))]
#guard Effect.plusOneLifelinkIndestructible.spellResolution ==
  .sequence [.onPermanent (.plusOne 1),
    .onPermanent (.grantKeywords (Keyword.lifelink.merge Keyword.indestructible))]
#guard Effect.grantVigilanceUnblockable.resolution ==
  Resolution.sequence
    [.onPermanent (.grantKeywords (Keyword.vigilance.merge Keyword.cantBeBlocked)),
     .draw 1]
#guard Effect.grantVigilanceUnblockable.spellResolution ==
  .sequence
    [.onPermanent (.grantKeywords (Keyword.vigilance.merge Keyword.cantBeBlocked)),
     .draw 1]
#guard (Effect.creaturesYouControlGetAndGrant 1 1 Keyword.vigilance).resolution ==
  Resolution.sequence [.creaturesYouControlPump 1 1, .teamGain Keyword.vigilance]
#guard (Effect.creaturesYouControlGetAndGrant 1 1 Keyword.vigilance).spellResolution ==
  .sequence [.creaturesPump 1 1, .teamGain Keyword.vigilance]
#guard Effect.sourceGainsIndestructibleTap.resolution ==
  Resolution.sequence
    [.onSource (.grantKeywords Keyword.indestructible), .onSource .tap]
#guard Effect.sourceGainsIndestructibleTap.phrase ==
  "Witch-king of Angmar gains indestructible until end of turn. Tap him"
#guard (Effect.drawThenDiscard 2).resolution ==
  Resolution.sequence [.draw 2, .discard 1]
#guard (Effect.drawThenDiscard 2).spellResolution ==
  .sequence [.draw 2, .discard 1]
#guard (Effect.abilityDrawThenDiscard 2).resolution ==
  Resolution.sequence [.draw 2, .discard 1]
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
#guard (Effect.plusOneAndGrant
    ((Keyword.vigilance.merge Keyword.indestructible).merge Keyword.haste)).resolution ==
  Resolution.sequence
    [.onSource (.plusOne 1),
     .onSource (.grantKeywords
       ((Keyword.vigilance.merge Keyword.indestructible).merge Keyword.haste))]
#guard (Effect.plusOneAndGrant
    ((Keyword.vigilance.merge Keyword.indestructible).merge Keyword.haste)).phrase ==
  "Put a +1/+1 counter on this. He gains vigilance, indestructible, and haste until end of turn"
#guard (Effect.creaturesYouControlGetOppsLoseLife 1 0 1).resolution ==
  Resolution.sequence
    [.creaturesYouControlPump 1 0, .spell (.loseLife 1 .eachOpponent)]
#guard (Effect.creaturesYouControlGetOppsLoseLife 1 0 1).phrase ==
  "Creatures you control get +1/+0 until end of turn. Each opponent loses 1 life"
#guard (Effect.subtypesGainMenace #["Goblin", "Orc"]).resolution ==
  .subtypesGainMenace #["Goblin", "Orc"]
#guard (Effect.subtypesGainMenace #["Goblin", "Orc"]).phrase ==
  "Goblins and Orcs you control gain menace until end of turn"
#guard (Effect.subtypesGainMenace #["Elf"]).phrase ==
  "Elves you control gain menace until end of turn"
#guard (Effect.drawLoseLifeThenAmass 2).spellResolution ==
  .sequence [.draw 1, .loseLife 1, .amassGoblins 2]
#guard (Effect.counterThenRecruitIfMvAtMost 2).spellResolution ==
  .sequence [.counter, .«if» .recruit (.mvAtMost 2)]
#guard (Effect.counterThenRecruitIfMvAtMost 2).resolution ==
  .sequence [.spell .counter, .spell (.«if» .recruit (.mvAtMost 2))]
#guard (Effect.counterThenRecruitIfMvAtMost 2).phrase ==
  "counter target spell. If that spell's mana value was 2 or less, recruit"
#guard (Effect.counterThenRecruitIfMvAtMost 2).castKind == .counter
#guard Resolution.flatten
    (.sequence [.sequence [.draw 1, .gainLife 1], .amassGoblins 2]) ==
  [.draw 1, .gainLife 1, .amassGoblins 2]
#guard (Effect.ofTrigger (.scry 2)).resolution == Resolution.trigger (.scry 2)
#guard (Effect.chapterRecruit).asChapter? == some .recruit
#guard (Effect.chapterDraw 2).asChapter? == some (.draw 2)
#guard (Effect.enterDealDamageUpToOne 4).allowsZeroTargets
#guard Effect.watchHulk.resolution == Resolution.trigger (.watch .hulk)
#guard (TriggeredAbility.onEnterScry 2).effect.resolution ==
  Resolution.trigger (.scry 2)
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
#guard EffectTargetKind.noun .playerOrCreature == "any target"
#guard EffectTargetKind.noun .creatureWithFlying == "target creature with flying"
#guard EffectTargetKind.noun .opponent == "target opponent"
#guard EffectTargetKind.noun .colorlessNonland ==
  "target colorless nonland permanent"
#guard EffectTargetKind.noun .player == "target player"
#guard EffectTargetKind.noun .opponent == "target opponent"
#guard EffectTargetKind.noun .oppGraveyardCard ==
  "target card from an opponent's graveyard"
#guard EffectTargetKind.spec .none == { count := 0, noun := "", prefer := .own }
#guard EffectTargetKind.spec .playerOrCreature ==
  { count := 1, noun := "any target", prefer := .opponentPlayer }
#guard EffectTargetKind.spec .opponent ==
  { count := 1, noun := "target opponent", prefer := .opponentPlayer }
#guard EffectTargetKind.spec .creatureYouControlThenOppCreature ==
  { count := 2
    noun := "target creature you control and a creature an opponent controls"
    prefer := .ownThenOpponent
    slots := #[.creatureYouControl, .oppCreature] }
#guard EffectTargetKind.slotKind .creatureYouControlThenOppCreature 0 ==
  .creatureYouControl
#guard EffectTargetKind.slotKind .creatureYouControlThenOppCreature 1 ==
  .oppCreature
#guard EffectTargetKind.slotKind .creature 0 == .creature
#guard EffectTargetKind.spec .upToOneCreatureThenPlayer ==
  { count := 2
    noun := "up to one target creature and target player"
    prefer := .own
    slots := #[.creature, .player]
    optionalSlots := #[0] }
#guard EffectTargetKind.slotKind .upToOneCreatureThenPlayer 0 == .creature
#guard EffectTargetKind.slotKind .upToOneCreatureThenPlayer 1 == .player
#guard EffectTargetKind.isOptionalSlot .upToOneCreatureThenPlayer 0
#guard !EffectTargetKind.isOptionalSlot .upToOneCreatureThenPlayer 1
#guard EffectTargetKind.announcedNoun .upToOneCreatureThenPlayer 0 ==
  "up to one target creature"
#guard EffectTargetKind.announcedNoun .upToOneCreatureThenPlayer 1 ==
  "target player"
#guard EffectTargetKind.noun (.upToTwoCreaturesTotalMvAtMost 6) ==
  "up to two target creatures with total mana value 6 or less"
#guard EffectTargetKind.spec (.upToTwoCreaturesTotalMvAtMost 6) ==
  { count := 2
    noun := "up to two target creatures with total mana value 6 or less" }
#guard (Effect.chapterGainControlOfUpToTwoCreaturesTotalMvAtMost 6).allowsZeroTargets
#guard (Effect.chapterDealDamageToEachNonSubtypeAndOpponents 2 "Villain").phrase ==
  "This Saga deals 2 damage to each non-Villain creature and each opponent"
#guard Effect.chapterDealXDamageToTargetOpponentGreatestArtifactMv.targetKind ==
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
#guard (Effect.dealDamage 3).targetKind == .playerOrCreature
#guard (Effect.pump 3 3).targetKind == .creature
#guard (Effect.pump 3 3).targeting == EffectTargeting.of .creature .own
#guard EffectTargetKind.defaultPreference .playerOrCreature == .opponentPlayer
#guard EffectTargetKind.defaultPreference .opponent == .opponentPlayer
#guard EffectTargetKind.defaultPreference .creatureYouControl == .own
#guard EffectTargetKind.defaultPreference .creature == .opponent
#guard EffectTargetKind.targetsStackSpell .spell
#guard EffectTargetKind.targetsStackSpell .creatureSpell
#guard EffectTargetKind.targetsStackSpell (.creatureSpellPTAtMost 2)
#guard !EffectTargetKind.targetsStackSpell .creature
#guard Effect.destroyCreatureWithFlying.targetKind == .creatureWithFlying
#guard Effect.destroyCreature.targetKind == .creature
#guard Effect.plusOnePlusOneTrampleHexproof.targetKind == .creatureYouControl
#guard (Effect.dealDamageToCreature 5).targetKind == .creature
#guard (Effect.dealDamageLoseIndestructibleExile 3).targetKind == .creature
#guard Effect.creatureYouControlDealsPowerToOppCreature.targetKind ==
  .creatureYouControlThenOppCreature
#guard (Effect.plusOneUpToOneAndPlayerGainsLife 2).targetKind ==
  .upToOneCreatureThenPlayer
#guard (Effect.plusOneUpToOneAndPlayerGainsLife 2).targetCount == 2
#guard !(Effect.plusOneUpToOneAndPlayerGainsLife 2).allowsZeroTargets
#guard (Effect.plusOneUpToOneAndPlayerGainsLife 2).spellResolution ==
  .sequence [.countersOnCreatureTargets, .gainLife 2 .targetPlayers]
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
    .spell (.countersOnCreatureTargets .plusOnePlusOne 2 .firstYouControl),
    .spell .mutualFight]
#guard (Effect.plusOneThenFight 2).phrase ==
  "put 2 +1/+1 counters on target creature you control. Then it fights target creature an opponent controls"
#guard Effect.plusOneThenEachOtherIfFromGy.spellResolution ==
  .sequence [
    .countersOnCreatureTargets .plusOnePlusOne 1 .firstYouControl,
    .«if» (.plusOneOnEachYouControl 1 .eachOther) .castFromGraveyard]
#guard Effect.plusOneThenEachOtherIfFromGy.resolution ==
  .sequence [
    .spell (.countersOnCreatureTargets .plusOnePlusOne 1 .firstYouControl),
    .spell (.«if» (.plusOneOnEachYouControl 1 .eachOther) .castFromGraveyard)]
#guard Effect.plusOneThenEachOtherIfFromGy.phrase ==
  "put a +1/+1 counter on target creature you control. If this spell was cast from a graveyard, also put a +1/+1 counter on each other creature you control"
#guard SpellResolution.toPhrase
    (.«if» (.plusOneOnEachYouControl 1 .eachOther) .castFromGraveyard) "target creature" ==
  "if this spell was cast from a graveyard, put a +1/+1 counter on each other creature you control"
#guard (Effect.drawIfFromGy 1 2).spellResolution ==
  .ifElse (.draw 2) (.draw 1) .castFromGraveyard
#guard (Effect.drawIfFromGy 1 2).resolution ==
  .spell (.ifElse (.draw 2) (.draw 1) .castFromGraveyard)
#guard (Effect.drawIfFromGy 1 2).phrase ==
  "draw a card. If this spell was cast from a graveyard, draw 2 cards instead"
#guard (Effect.amassGoblinsOrFromGy 1 3).spellResolution ==
  .ifElse (.amassGoblins 3) (.amassGoblins 1) .castFromGraveyard
#guard (Effect.amassGoblinsOrFromGy 1 3).resolution ==
  .spell (.ifElse (.amassGoblins 3) (.amassGoblins 1) .castFromGraveyard)
#guard (Effect.amassGoblinsOrFromGy 1 3).phrase ==
  "amass Goblins 1. If this spell was cast from a graveyard, amass Goblins 3 instead"
#guard SpellResolution.toPhrase
    (.ifElse (.gainLife 3) (.draw 1) (.subtype "Elf")) "target creature" ==
  "draw a card. If target creature is an Elf, you gain 3 life instead"
#guard SpellResolution.toPhrase
    (.ifElse .recruit (.draw 1) (.mvAtMost 2)) "target spell" ==
  "draw a card. If that spell's mana value was 2 or less, recruit instead"
#guard SpellResolution.toPhrase (.plusOneOnEachYouControl 1 .eachOther) "target creature" ==
  "put a +1/+1 counter on each other creature you control"
#guard SpellResolution.toPhrase (.gainLife 3) "target creature" == "you gain 3 life"
#guard SpellResolution.toPhrase (.gainLife 2 .targetPlayers) "target player" ==
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
  .sequence [.returnTargetToHand .graveyard, .amassGoblins 3]
#guard (Effect.returnCreatureFromGyThenAmass 3).resolution ==
  Resolution.sequence [.fra .returnFromGyToHand, .spell (.amassGoblins 3)]
#guard (Effect.returnCreatureFromGyThenAmass 3).phrase ==
  "return up to one target creature card from your graveyard to your hand. Amass Goblins 3"
#guard Effect.returnSpellCantCastIfGift.spellResolution ==
  .sequence [.returnTargetToHand, .«if» .playersCantCastThisTurn .giftPromised]
#guard SpellResolution.toPhrase (.creaturesPump 1 1) "target creature" ==
  "creatures you control get +1/+1 until end of turn"
#guard SpellResolution.toPhrase (.creaturesPump (-4) (-4) .all) "" ==
  "all creatures get -4/-4 until end of turn"
#guard SpellResolution.toPhrase (.creaturesPump (-1) (-1) .ofTargetPlayer) "target player" ==
  "creatures target player controls get -1/-1 until end of turn"
#guard Effect.destroyArtifactOrLandNonflyersCantBlock.targetKind == .artifactOrLand
#guard Effect.playAdditionalLandThisTurn.targetKind == .none
#guard (Effect.destroyTargetCreatureControllerLosesLife 2).targetKind == .creature
#guard (Effect.allCreaturesGet (-4) (-4)).targetKind == .none
#guard (Effect.drawAndLoseLife 2 2).targetKind == .none
#guard (Effect.targetPlayerDrawLoseLife 2 2).targetKind == .player
#guard (Effect.creaturesTargetPlayerGet (-1) (-1)).targetKind == .player
#guard Effect.exileGraveyardCreaturesGrantCast.targetKind == .player
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
#guard (Effect.targetPlayerDraw 2).spellResolution == .draw 2 .targetPlayer
#guard (Effect.targetPlayerDraw 2).resolution == .targetPlayerDraw 2
#guard SpellResolution.toPhrase (.draw 2 .you) "target player" == "draw 2 cards"
#guard SpellResolution.toPhrase (.draw 2 .targetPlayer) "target player" ==
  "target player draws 2 cards"
#guard (Effect.targetPlayerDrawLoseLife 2 2).spellResolution ==
  .sequence [.draw 2 .targetPlayer, .loseLife 2 .targetPlayer]
#guard (Effect.destroyTargetCreatureControllerLosesLife 2).spellResolution ==
  .sequence [.onPermanent .destroy, .loseLife 2 .controllerOfTarget]
#guard (Effect.eachOpponentLosesLife 2).spellResolution == .loseLife 2 .eachOpponent
#guard SpellResolution.toPhrase (.loseLife 2 .you) "target player" == "lose 2 life"
#guard SpellResolution.toPhrase (.loseLife 2 .targetPlayer) "target player" ==
  "target player loses 2 life"
#guard SpellResolution.toPhrase (.loseLife 2 .controllerOfTarget) "target creature" ==
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
  .dealDamageToEachCreature 2 (.nonSubtype "Dragon")
#guard SpellResolution.toPhrase (.dealDamageToEachCreature 3 .each) "target creature" ==
  "deals 3 damage to each creature"
#guard SpellResolution.toPhrase (.dealDamageToEachCreature 1 .opponentsControl) "target creature" ==
  "deals 1 damage to each creature your opponents control"
#guard SpellResolution.toPhrase
    (.dealDamageToEachCreature 2 (.nonSubtype "Elf")) "target creature" ==
  "deals 2 damage to each non-Elf creature"
#guard Effect.creatureYouControlDealsPowerToOppCreature.spellResolution == .fight
#guard Effect.creatureYouControlDealsTwicePower.spellResolution == .fight 2
#guard Effect.fightUpToOne.spellResolution == .mutualFight .upToOne
#guard (Effect.createTokensX .dwarf).spellResolution ==
  .createTokens .dwarf 0 (qty := .chosenX)
#guard (Effect.createTokensPerSubtype .treasure "Villain").spellResolution ==
  .createTokens .treasure 0 (qty := .perSubtype "Villain")
#guard Effect.damageOppCreaturesEqualOtherSpellsMv.spellResolution ==
  .dealDamageToEachCreature 0 .opponentsControl .otherSpellsManaValue
#guard (Effect.counterUnlessPaysTeamwork 2 4).spellResolution ==
  .ifElse (.unlessPays .counter 4) (.unlessPays .counter 2) .teamwork
#guard (Effect.dealDamageToAttackerOrBlocker 2 4).spellResolution ==
  .ifElse (.onPermanent (.dealDamage 4)) (.onPermanent (.dealDamage 2)) .teamwork
#guard Effect.doublePowerAndToughness.spellResolution == .onPermanent .doublePowerAndToughness
#guard (Effect.exileCreatureToughnessAtLeast 4).spellResolution == .onPermanent .exile
#guard Effect.searchLegendaryCreatureToHand.spellResolution == .searchLibrary
#guard (Effect.destroyLandSearchBasic).spellResolution ==
  .sequence [.onPermanent .destroy, .searchLibrary .basic .land .ownerMayToBattlefield]
#guard SpellResolution.toPhrase (.fight 2) "target creature" ==
  "Target creature you control deals damage equal to twice its power to target creature an opponent controls."
#guard SpellResolution.toPhrase (.mutualFight .upToOne) "target creature" ==
  "target creature you control fights up to one other target creature"
#guard SpellResolution.toPhrase
    (.dealDamageToEachCreature 0 .opponentsControl .otherSpellsManaValue) "target creature" ==
  "deals damage to each creature your opponents control equal to the total mana value of other spells you've cast this turn"
#guard SpellResolution.toPhrase (.createTokens .dwarf 0 (qty := .chosenX)) "" ==
  "create X 2/2 red Dwarf creature tokens"
#guard SpellResolution.toPhrase
    (.createTokens .treasure 0 (qty := .perSubtype "Villain")) "" ==
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
    additionalCostSacrificeArtifactOrCreature := true
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
#guard (Effect.dealDamageToTargetCreature 2).targetKind == .creature
#guard Effect.destroyTargetColorlessNonland.targetKind == .colorlessNonland
#guard Effect.attachToTargetCreatureYouControl.targetKind == .creatureYouControl
#guard Effect.targetCantBeBlockedThisTurn.targeting ==
  EffectTargeting.of .creature .own
#guard Effect.searchBasicLandTapped.targetKind == .none
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
  .becomeSubtypeWithLandsPT "Bear"
#guard (Effect.becomeSubtypeWithLandsPT "Elf").phrase ==
  "This enchantment becomes an Elf creature in addition to its other types and gains \"This creature's power and toughness are each equal to the number of lands you control.\""
#guard (Effect.searchBasicBeholdSubtypeUntap "Elf").resolution ==
  .searchBasicBeholdSubtypeUntap "Elf"
#guard (Effect.searchBasicBeholdSubtypeUntap "Orc").phrase.endsWith
  "You may behold an Orc. If you do, untap that land"
#guard Effect.addAnyColorSpendOnlyHero.resolution ==
  .addAnyColorSpendOnlySubtype "Hero"
#guard Effect.addAnyColorSpendOnlyVillain.resolution ==
  .addAnyColorSpendOnlySubtype "Villain"
#guard (Effect.teamGain Keyword.doubleStrike).phrase ==
  "Creatures you control gain double strike until end of turn"
#guard (Effect.becomeTypes #["Dinosaur", "Hero"] 3 5
    (Keyword.reach.merge Keyword.vigilance)).phrase ==
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
#guard (Effect.plusOneOnTarget 2).targetKind == .creatureYouControl
#guard (Effect.plusOneOnTarget 2 #["Elf"]).targetKind ==
  .creatureYouControlAnySubtype #["Elf"]
#guard TriggeredAbility.toNotation (.onEnterCreateTokens .treasure 1) ==
  "When this permanent enters, create a Treasure token."
#guard TriggeredAbility.toNotation (.onEnterCreateTokens .treasure 1 true) ==
  "When this permanent enters, create a tapped Treasure token."
#guard TriggeredAbility.resolution (.onEnterCreateTokens .treasure 1) ==
  .createTokens .treasure 1 false
#guard TriggeredAbility.resolution (.onEnterCreateTokens .treasure 1 true) ==
  .createTokens .treasure 1 true
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
#guard (TriggeredAbility.onEnterMayDiscardDraw 2).resolution == .mayDiscardDraw 2
#guard TriggeredAbility.onCastNoncreatureMayDrawXDiscard2 ==
  .triggered .youCastNoncreature (Effect.ofTrigger (.may (.drawXDiscard 2)))
#guard (TriggeredAbility.onCastNoncreatureMayDrawXDiscard2).resolution == .mayDrawXDiscard2
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
  .triggered .opponentCastsSpell (Effect.ofTrigger (.amassGoblins 1 "Orc"))
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
  .sequence [.createTokens .dwarf 1 false, .attachSourceToCreated]
#guard TriggeredAbility.toNotation (.onEnterCreateThenAttach .dwarf) ==
  "When this permanent enters, create a 2/2 red Dwarf creature token, then attach this Equipment to it."
#guard TriggeredAbility.onLandYouControlEntersDrawPlusOneSource ==
  .triggered .landYouControlEnters Effect.seqDrawPlusOneSource
#guard TriggeredAbility.onArmyCombatDamageRingTempts ==
  .triggered .armyYouControlCombatDamage (Effect.ofTrigger .ringTempts)
#guard TriggeredAbility.onAttackSetOtherBasePT ==
  .triggered .attack (Effect.ofTrigger .setOtherBasePT)
#guard TriggeredAbility.onEnterOrAttackReturnElfGainLife ==
  .triggered .enterOrAttack (Effect.ofTrigger .returnElfGainLife)
#guard TriggeredAbility.resolution .onEnterOrAttackReturnElfGainLife ==
  .sequence [.returnCreatureFromGyToHand, .gainLifeEqualToTargetPower]
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
  .sequence [.draw 1, .putOnBottomIfNoLegendary]
#guard TriggeredAbility.toNotation .onEnterDrawThenBottomIfNoLegendary ==
  "When this permanent enters, draw a card. Then if you don't control a legendary creature, put a card from your hand on the bottom of your library."
#guard TriggeredAbility.onYourEndStepRemoveHopeDrawSac ==
  .triggered .yourEndStep (Effect.ofTrigger .removeHopeDrawSac)
#guard TriggeredAbility.resolution .onYourEndStepRemoveHopeDrawSac ==
  .sequence [.removeHopeCounterDraw, .sacrificeGainLifeIfNoHope]
#guard TriggeredAbility.toNotation .onYourEndStepRemoveHopeDrawSac ==
  "At the beginning of your end step, remove a hope counter from this. If you do, draw a card. Then if this has no hope counters on it, sacrifice it and you gain 4 life."
#guard TriggeredAbility.onAttackTapHumansDraw ==
  .triggered .attack (Effect.ofTrigger .tapHumansDraw)
#guard TriggeredAbility.resolution .onAttackTapHumansDraw ==
  .sequence [.tapAnyHumans, .drawForEachTappedHuman]
#guard TriggeredAbility.toNotation .onAttackTapHumansDraw ==
  "Whenever this creature attacks, you may tap any number of untapped Humans you control. Draw a card for each Human tapped this way."
#guard TriggeredAbility.onEnterUntapOtherPlusOneIfSubtype "Bear" ==
  .triggered .enter (Effect.seqUntapPlusOneIfSubtype "Bear")
#guard TriggeredAbility.onEnterDestroyOppArtifactsEnchantmentsGainLife ==
  .triggered .enter (Effect.ofTrigger .destroyOppArtifactsEnchantmentsGainLife)
#guard TriggeredAbility.onAttackDamageEqualSubtypeToEachOpponent "Dwarf" ==
  .triggered .attack (Effect.ofTrigger (.damageEqualSubtypeToEachOpponent "Dwarf"))
#guard TriggeredAbility.onAttackDamageEqualTreasures ==
  .triggered .attack (Effect.ofTrigger .damageEqualTreasures)
#guard TriggeredAbility.onPlayerCastsSecondSpellLoseLifeCreateTreasure ==
  .triggered .anyPlayerCastsSecondSpell Effect.seqLoseLifeCreateTreasure
#guard TriggeredAbility.onEnterDealDamageDestroyIfSubtype 1 "Dragon" ==
  .triggered .enter (Effect.ofTrigger (.dealDamageDestroyIfSubtype 1 "Dragon"))
#guard TriggeredAbility.onEnterAttachTargetEquipment ==
  .triggered .enter (Effect.ofTrigger .attachEquipmentToCreature)
#guard TriggeredAbility.onAttackDefenderSacsLeastPower ==
  .triggered .attack (Effect.ofTrigger .defenderSacsLeastPower)
#guard TriggeredAbility.onEnterReturnOtherPlusOne ==
  .triggered .enter (Effect.ofTrigger .returnOtherPlusOne)
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
  .triggered .eachBeginCombat (Effect.ofTrigger (.othersGetAndOppsGet #["Goblin", "Orc"] 2 2 (-1) (-1)))
#guard TriggeredAbility.onCombatDamageWolfPlusOneOrTreasure ==
  .triggered .combatDamageToPlayer (Effect.ofTrigger .wolfPlusOneOrTreasure)
#guard TriggeredAbility.onYourBeginCombatTrampleCounterBecomeBear ==
  .triggered .yourBeginCombat (Effect.ofTrigger .trampleCounterBecomeBear)
#guard TriggeredAbility.onEnterMillThenSubtypeToHand 4 "Elf" ==
  .triggered .enter (Effect.ofTrigger (.millThenSubtypeToHand 4 "Elf"))
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
      resolution := Resolution.trigger (SharedTrigger.chapter 1 .recruit) }
#guard TriggeredAbility.onceEachTurn .onFinalSagaChapterRevealSaga
#guard TriggeredAbility.onYouSacrificeTokenOppLosesLife ==
  .triggered .youSacrificeToken (Effect.ofTrigger (.targetOpponentLosesLife 1))
#guard TriggeredAbility.onDiesAmassGoblinsEqualPower ==
  .triggered .dies (Effect.ofTrigger (.amassGoblins 0 (amount := .sourcePower)))
#guard TriggeredAbility.youControlCreatureWithPower? (.onAttackFerociousGainLife 2)
  == some 4
#guard TriggeredAbility.onceEachTurn .onArtifactYouControlEntersDrawOnce
#guard !(Effect.sourceGets 1 0).requiresTarget
#guard !(Effect.putPlusOnePlusOneOnSource 3).requiresTarget
#guard toString Keyword.cantBeBlocked == "can't be blocked"
#guard toString Keyword.menace == "menace"
#guard CardDef.isKeywordRestatement Keyword.menace "Menace"
#guard CardDef.isKeywordRestatement Keyword.menace
  "Menace (This creature can't be blocked except by two or more creatures.)"
#guard !CardDef.isKeywordRestatement Keyword.menace "Flying"
#guard
  let ab : ActivatedAbility := {
    cost := { mana := ManaCost.ofGeneric 1, discardSource := true }
    effect := Effect.searchLandTypeToHand "Mountain"
    activateFromHand := true
  }
  toString ab ==
    "{1}, Discard this card: Search your library for a Mountain card, reveal it, put it into your hand, then shuffle (activate only from your hand)"
#guard
  let ab : ActivatedAbility := {
    cost := { mana := ManaCost.ofGeneric 2, tap := true, sacrificeSource := true }
    effect := Effect.searchBasicLandTapped
  }
  (toString ab).startsWith "{2}, {T}, Sacrifice:"
#guard
  let ab : ActivatedAbility := {
    cost := { payLife := 2 }
    effect := Effect.sourceGets 2 2
    onceEachTurn := true
  }
  toString ab ==
    "Pay 2 life: This creature gets +2/+2 until end of turn (activate only once each turn)"
#guard
  let ab : ActivatedAbility := {
    cost := { mana := ManaCost.ofGeneric 1, sacrificeSource := true }
    effect := Effect.dealDamageToTargetCreature 2
    otherModes := #[Effect.destroyTargetColorlessNonland]
  }
  ab.isModal &&
    (toString ab).startsWith "{1}, Sacrifice: Choose one —" &&
    ((toString ab).splitOn "target creature").length > 1 &&
    ((toString ab).splitOn "colorless nonland").length > 1
#guard StaticAbility.toNotation (.otherCreaturesHaveTrample #["Orc", "Goblin"]) ==
  "Other Orcs and Goblins you control have trample."
#guard StaticAbility.toNotation (.otherCreaturesGet #["Elf"] 1 1) ==
  "Other Elf creatures you control get +1/+1."
#guard StaticAbility.toNotation (.extraTriggerAnotherYouControl #["Wolf"] true) ==
  "If a triggered ability of another Wolf or battle you control triggers, that ability triggers an additional time."
#guard StaticAbility.toNotation (.extraTriggerIfEnduringStorySubtype "Dwarf") ==
  "As long as you have an enduring story, if a triggered ability of a Dwarf you control triggers, that ability triggers an additional time."
#guard TapAddForEach.toNotation { mana := .colored .green, subtype := "Elf" } ==
  "{T}: Add {G} for each Elf you control"
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
#guard StaticAbility.toNotation (.cantBlockUnlessYouControl #["Goblin", "Orc"]) ==
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
  .connive (.target .creatureYouControl)
#guard TriggeredAbility.targetKind .onCombatAnotherGetsSourcePower ==
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
#guard TriggeredAbility.targetKind (.onEnterUntapOtherPlusOneIfSubtype "Bear") ==
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
#guard TriggeredAbility.targetKind (.onDiesOppCreatureGets (-1) (-1)) == .oppCreature
#guard TriggeredAbility.targetKind .onEnterTargetOpponentSacrifices == .opponent
#guard TriggeredAbility.targetKind (.onEnterExileOppGyCardOppsLoseLife 2) ==
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
    cost := { mana := ManaCost.ofGeneric 3 }
    effect := Effect.attachToTargetCreatureYouControl
    onlyAsSorcery := true
  }
  (toString ab).startsWith "{3}: Attach this Equipment" &&
    (toString ab).endsWith "(activate only as a sorcery)"
#guard TriggeredAbility.firesOn .onLandYouControlEntersPlusOnePlusOne .landYouControlEnters
#guard TriggeredAbility.firesOn (.onLandYouControlEntersGets 1 1) .landYouControlEnters
#guard !TriggeredAbility.firesOn (.onEnterScry 2) .landYouControlEnters
#guard TriggeredAbility.requiresTarget .onLandYouControlEntersPlusOnePlusOne
#guard !TriggeredAbility.requiresTarget (.onLandYouControlEntersGets 1 1)
#guard TriggeredAbility.targetKind .onLandYouControlEntersPlusOnePlusOne ==
  .creatureYouControl
#guard TriggeredAbility.targetKind .onAttackSetOtherBasePT ==
  .anotherCreatureYouControl
#guard TriggeredAbility.targetKind (.onEnterDealDividedDamage 3 3) ==
  .playerOrCreature
#guard TriggeredAbility.targetKind .onEnterOrAttackReturnElfGainLife ==
  .elfInYourGraveyard
#guard TriggeredAbility.targetKind .onDiesDealDamageEqualToPowerToOppCreature ==
  .oppCreature
#guard TriggeredAbility.targetKind .onEnterTargetOpponentSacrificesCreature ==
  .opponent
#guard TriggeredAbility.targetKind (.onEnterDraw 1) == .none
#guard StaticAbility.hostStatBonus (.enchantedCreatureGets 3 3) == (3, 3)
#guard StaticAbility.hostStatBonus (.equippedCreatureGets 2 0) == (2, 0)
#guard StaticAbility.shape (.enchantedCreatureGets 3 3) ==
  .hostGets "Enchanted creature" 3 3
#guard StaticAbility.shape (.equippedCreatureGets 2 0) ==
  .hostGets "Equipped creature" 2 0
#guard (StaticAbility.StaticShape.spec (.hostGets "Enchanted creature" 3 3)).hostBonus ==
  (3, 3)
#guard (StaticAbility.StaticShape.spec (.lordPump #["Elf"] 1 1)).lordPump ==
  some (#["Elf"], 1, 1)
#guard (StaticAbility.StaticShape.spec (.lordTrample #["Orc"])).trampleSubtypes ==
  some #["Orc"]
#guard (StaticAbility.StaticShape.spec .landsYouControlPT).landsYouControlPT
#guard (StaticAbility.StaticShape.spec (.cantBlockUnless #["Goblin"])).cantBlockUnless ==
  some #["Goblin"]
#guard (StaticAbility.lordPump? (.otherCreaturesGet #["Elf"] 1 1)) == some (#["Elf"], 1, 1)
#guard (StaticAbility.trampleSubtypes? (.otherCreaturesHaveTrample #["Orc"])) == some #["Orc"]
#guard StaticAbility.isLandsYouControlPT .powerToughnessEqualLandsYouControl
#guard !StaticAbility.isLandsYouControlPT (.enchantedCreatureGets 1 1)
#guard (StaticAbility.cantBlockUnless? (.cantBlockUnlessYouControl #["Goblin"])) ==
  some #["Goblin"]
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
#guard TriggeredAbility.resolution .onAttackPumpByGreatestPower == .pumpGreatestPower
#guard TriggeredAbility.resolution .onAttackSetOtherBasePT == .setOtherBasePT
#guard TriggeredAbility.resolution .onAttackOtherGets2AndTrample ==
  .onPermanent (.pumpAndTrample 2 0)
#guard TriggeredAbility.resolution (.onEnterScry 2) == .scry 2
#guard TriggeredAbility.resolution (.onEnterSurveil 2) == .surveil 2
#guard TriggeredAbility.toNotation (.onEnterSurveil 1) ==
  "When this permanent enters, surveil 1."
#guard TriggeredAbility.toNotation (.onEnterEnchanted (.grantKeywords Keyword.firstStrike)) ==
  "When this Aura enters, enchanted creature gains first strike until end of turn."
#guard TriggeredAbility.toNotation (.onEnterEnchanted .tap) ==
  "When this Aura enters, tap enchanted creature."
#guard TriggeredAbility.resolution (.onEnterEnchanted .tap) == .onEnchanted .tap
#guard TriggeredAbility.toNotation (.onEnterAttachThen (.grantKeywords Keyword.indestructible)) ==
  "When this Equipment enters, attach it to target creature you control. That creature gains indestructible until end of turn."
#guard TriggeredAbility.toNotation (.onEnterAttachThen .untap) ==
  "When this Equipment enters, attach it to target creature you control. Untap that creature."
#guard TriggeredAbility.targetKind (.onEnterAttachThen .untap) == .creatureYouControl
#guard TriggeredAbility.toNotation .onEnterExileOtherCopyEnchanted ==
  "When this Aura enters, exile up to one target creature other than enchanted creature until this Aura leaves the battlefield. Enchanted creature becomes a copy of that creature until this Aura leaves the battlefield."
#guard TriggeredAbility.allowsZeroTargets .onEnterExileOtherCopyEnchanted
#guard TriggeredAbility.toNotation .onEnterExileCreatureReturnEndStep ==
  "When this Vehicle enters, exile up to one target creature you control. Return that card to the battlefield under its owner's control at the beginning of the next end step."
#guard TriggeredAbility.allowsZeroTargets .onEnterExileCreatureReturnEndStep
#guard TriggeredAbility.toNotation .onEnterTapOrUntapNonland ==
  "When this creature enters, choose one — • Tap target nonland permanent. • Untap target nonland permanent."
#guard TriggeredAbility.targetKind .onEnterTapOrUntapNonland == .nonland
#guard TriggeredAbility.toNotation .onEnterCreateFoodOrTreasure ==
  "When this creature enters, create a Food token or a Treasure token."
#guard TriggeredAbility.toNotation .onEnterVillainIfGyElseMill ==
  "When this creature enters, create a tapped 2/1 black Villain creature token with menace if there are two or more creature cards in your graveyard. Otherwise, mill two cards."
#guard TriggeredAbility.toNotation .onEnterDrawMayPutLandTapped ==
  "When this creature enters, draw a card, then you may put a land card from your hand onto the battlefield tapped."
#guard TriggeredAbility.toNotation .onEnterDrawGainLifeIfAnotherHero ==
  "When this creature enters, draw a card. If you control another Hero, you gain 2 life."
#guard TriggeredAbility.toNotation .onEnterPlusOneOrTwoIfAnotherHero ==
  "When this creature enters, put a +1/+1 counter on target creature. If that creature is another Hero, put two +1/+1 counters on it instead."
#guard TriggeredAbility.targetKind .onEnterPlusOneOrTwoIfAnotherHero == .creature
#guard TriggeredAbility.toNotation .onEnterMaySacArtifactOrDiscardDraw ==
  "When this creature enters, you may sacrifice an artifact or discard a card. If you do, draw a card."
#guard TriggeredAbility.toNotation .onEnterExileOppTappedUntilLeaves ==
  "When this enchantment enters, exile target tapped creature an opponent controls until this enchantment leaves the battlefield."
#guard TriggeredAbility.targetKind .onEnterExileOppTappedUntilLeaves == .oppTappedCreature
#guard TriggeredAbility.resolution .onEnterExileOppTappedUntilLeaves == .exileUntilLeaves
#guard TriggeredAbility.toNotation (.onEnterTargetOpponentDiscards 2) ==
  "When this enchantment enters, target opponent discards two cards."
#guard TriggeredAbility.targetKind (.onEnterTargetOpponentDiscards 2) == .opponent
#guard TriggeredAbility.toNotation (.onEnter (Effect.enterDestroy (.oppCreaturePowerAtMost 3))) ==
  "When this permanent enters, destroy target creature an opponent controls with power 3 or less."
#guard TriggeredAbility.targetKind (.onEnter (Effect.enterDestroy (.oppCreaturePowerAtMost 3))) ==
  .oppCreaturePowerAtMost 3
#guard TriggeredAbility.toNotation (.onEnter (Effect.enterDealDamageUpToOne 4)) ==
  "When this permanent enters, it deals 4 damage to up to one target creature."
#guard TriggeredAbility.allowsZeroTargets (.onEnter (Effect.enterDealDamageUpToOne 4))
#guard TriggeredAbility.toNotation (.onEnter Effect.enterFightUpToOne) ==
  "When this permanent enters, this fights up to one other target creature."
#guard TriggeredAbility.targetKind (.onEnter Effect.enterFightUpToOne) == .anotherCreature
#guard TriggeredAbility.toNotation (.onEnter Effect.enterCreateZabu) ==
  "When this permanent enters, create Zabu, a legendary 2/2 green Cat creature token with \"Landfall — Whenever a land you control enters, put a +1/+1 counter on Zabu.\"."
#guard TriggeredAbility.targetKind (.onEnter Effect.enterOppCreatesTheVoid) == .opponent
#guard TriggeredAbility.resolution (.onEnter Effect.enterCreateSturdyShieldAttach) ==
  .createSturdyShieldAttach
#guard TriggeredAbility.targetKind (.onEnter Effect.enterExileGyPlayUntilNextTurn) ==
  .equipmentInstantOrSorceryInYourGraveyard
#guard TriggeredAbility.targetKind (.onEnter Effect.enterReturnGyPermanentThisTurn) ==
  .permanentCardInYourGraveyard
#guard TriggeredAbility.resolution (.onEnter Effect.enterTapOppCantUntapWhileControl) ==
  .tapCantUntapWhileControl
#guard TriggeredAbility.resolution (.onEnter Effect.enterMaySacAnotherThenDestroyOppNonland) ==
  .maySacAnotherThenDestroyOppNonland
#guard TriggeredAbility.resolution (.onEnterExileTop) == .exileTop
#guard StaticAbility.toNotation .noMaximumHandSize ==
  "You have no maximum hand size."
#guard StaticAbility.toNotation (.maximumHandSize 10) ==
  "Your maximum hand size is 10."
#guard StaticAbility.toNotation (.powerEqualSubtypeYouControl "Merfolk") ==
  "This creature's power is equal to the number of Merfolk you control."
#guard StaticAbility.toNotation .improvise == "Improvise"
#guard StaticAbility.toNotation (.typeSpellsCostLess .artifact 1) ==
  "Artifact spells you cast cost {1} less to cast."
#guard StaticAbility.toNotation (.supertypeSpellsCostLess .legendary 1) ==
  "Legendary spells you cast cost {1} less to cast."
#guard StaticAbility.toNotation (.supertypeSpellsCostLess .snow 2) ==
  "Snow spells you cast cost {2} less to cast."
#guard StaticAbility.toNotation (.enchantedCreatureGetsHasAndTypes 2 2
    (Keyword.firstStrike.merge Keyword.vigilance) #["legendary", "Soldier"]) ==
  "Enchanted creature gets +2/+2, has first strike and vigilance, and is a legendary Soldier in addition to its other types."
#guard StaticAbility.toNotation .enchantedLosesAbilitiesCantUntap ==
  "Enchanted creature loses all abilities and can't become untapped."
#guard StaticAbility.toNotation (.enchantedCreatureGetsHasAndWard 4 4 Keyword.trample 1) ==
  "Enchanted creature gets +4/+4 and has trample and ward {1}."
#guard StaticAbility.toNotation (.getsAndAllTypesIfGyCreatureCards 2 2 2) ==
  "As long as there are 2 or more creature cards in your graveyard, this creature gets +2/+2 and is all creature types."
#guard StaticAbility.toNotation (.sneak (ManaCost.ofGenericAndColors 1 [.black, .black])) ==
  "Sneak {1}{B}{B}"
#guard StaticAbility.toNotation .boast ==
  "Boast — Exile any number of black cards from your graveyard with fifteen or more black mana symbols among their mana costs: Copy those exiled cards. You may cast up to three of the copies without paying their mana costs."
#guard TriggeredAbility.resolution (.onAttackScry 1) == .scry 1
#guard TriggeredAbility.resolution (.onAttackFerociousGainLife 2) == .gainLife 2
#guard TriggeredAbility.youControlCreatureWithPower? (.onAttackFerociousGainLife 2) == some 4
#guard (TriggeredAbility.youControlCreatureWithPower? (.onAttackScry 1)).isNone
#guard TriggeredAbility.resolution (.onAttackWithElvesScry 1) == .scry 1
#guard TriggeredAbility.resolution (.onEnterDraw 1) == .draw 1
#guard TriggeredAbility.resolution .onEnterSearchForest == .searchLibrary
#guard TriggeredAbility.resolution .onEnterSearchBasicToHand == .searchLibrary .basicLandToHand
#guard TriggeredAbility.resolution (.onOpponentCastsAmassOrcs 1) == .amassGoblins 1 "Orc"
#guard TriggeredAbility.resolution .onDiesAmassGoblinsEqualPower ==
  .amassGoblins 0 "Goblin" .sourcePower
#guard TriggeredAbility.resolution (.onEnterAmassThenAttach 1) ==
  .amassGoblins 1 "Goblin" .fixed true
#guard TriggeredAbility.resolution .onOpponentCastsFirstNoncreatureRecruit == .recruit .you
#guard TriggeredAbility.resolution .onEnterRecruit == .recruit
#guard TriggeredAbility.onCombatDamageToPlayerLoot.effect.resolution ==
  .sequence [.draw 1, .discard 1]
#guard TriggeredAbility.resolution .onEnterEachOpponentDiscards == .opponentDiscards
#guard TriggeredAbility.resolution (.onEnterTargetOpponentDiscards 2) ==
  .opponentDiscards 2 .target
#guard TriggeredAbility.resolution .onAttackFerociousPlusOneEach == .plusOneEachYouControl
#guard TriggeredAbility.resolution .onEnterCreateAxe == .createAxe
#guard TriggeredAbility.resolution .onEnterCreateAxeAttach == .createAxe true
#guard TriggeredAbility.resolution .onEquippedAttacksPlusOneEachIfCityBlessing ==
  .plusOneEachYouControl .citysBlessing
#guard TriggeredAbility.resolution
    (.onStep (Effect.ofTrigger .prepareSource)) == .prepareSource
#guard TriggeredAbility.resolution
    (.onStep (Effect.ofTrigger (.prepareSource .ifThreeCreaturesDied))) ==
  .prepareSource .ifThreeCreaturesDied
#guard (TriggeredAbility.triggered .youScryOrSurveil
    (Effect.ofTrigger (.mayPayGenericDraw 2 (plusOneOnSource := true)))).resolution ==
  .mayPayGenericDraw 2 true
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
  .onPermanent (.grantKeywords Keyword.flying)
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
  .opponentSacrificesCreature
#guard TriggeredAbility.resolution (.onLandYouControlEntersGets 1 1) ==
  .onSource (.pump 1 1)
#guard TriggeredAbility.resolution .onLandYouControlEntersPlusOnePlusOne ==
  .onPermanent (.plusOne 1)
#guard TriggeredAbility.resolution .onAnotherElfYouControlEntersGets1 ==
  .onSource (.pump 1 1)
#guard TriggeredAbility.resolution (.onEnterDealDividedDamage 3 3) == .dividedDamage
#guard TriggeredAbility.resolution (.onEnterOrAttackDealDividedDamage 3 3) ==
  .dividedDamage
#guard TriggeredAbility.resolution .onDiesDealDamageEqualToPowerToOppCreature ==
  .damageFromLastKnownPower
#guard TriggeredAbility.resolution (.onCastInstantOrSorceryDealDamageToEachOpponent 2) ==
  .damageEachOpponent 2
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
    c.hasSubtype "Adventure"

#guard
  let adv : AdventureFace := {
    name := "Till and Tend"
    manaCost := ManaCost.ofGenericAndColor 1 .green
    spellEffect := some (Effect.playAdditionalLandThisTurn)
  }
  let c := adv.toCardDef
  c.name == "Till and Tend" && c.isSorcery && !c.requiresTarget &&
    c.hasSubtype "Adventure"

#guard TriggeredAbility.toNotation .onTokenYouControlEntersBelladonna ==
  "Whenever a token you control enters, you gain 1 life if this is the first time this ability has resolved this turn. If it's the second time, draw a card. If it's the third time, put a +1/+1 counter on each creature you control."
#guard TriggeredAbility.toNotation .onActivateCreatureAbilityDrawOnce ==
  "Whenever you activate an ability of a creature, draw a card. This ability triggers only once each turn."
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

end Mtg.Engine
