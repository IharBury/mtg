/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
Authors: MTG Engine Contributors
-/

import Mtg.Engine.Color
import Mtg.Engine.Mana

/-!
# Leftover modeled ability constructors

Reusable ability shapes live on `TriggeredAbility`, `StaticAbility`,
`SpellEffect`, `AbilityEffect`, and `CardDef` so any set can use them.
Reusable leftover *trigger* wordings now live on event-family effect
inductives (`StepEffect`, `DeathEffect`, `ThisAttackEffect`,
`EnterOrAttackEffect`, `WatchEffect`, `YouAttackEffect`, `CastEffect`,
`ResourceEffect`) with one `TriggeredAbility` constructor each.
Leftover statics, spells, and activations remain here.
-/

namespace Mtg.Engine

/-- A leftover modeled static that is not yet a shared shape. -/
inductive ModeledStatic where
  /-- Modeled MSH ability. -/
  | aresAttacksEachCombatIfAble
  /-- Modeled MSH ability. -/
  | artifactSpellsYouCastCost1LessToCast
  /-- Modeled MSH ability. -/
  | asAnAdditionalCostToCastThisSpell
  /-- Modeled MSH ability. -/
  | asLongAsThereAreTwoOrMoreCreatureCards
  /-- Modeled MSH ability. -/
  | asLongAsThereAreTwoOrMoreCreatureCards2
  /-- Modeled MSH ability. -/
  | asLongAsYouControlAnArtifactCreatureOrA
  /-- Modeled MSH ability. -/
  | asLongAsYouVePutOneOrMore11Counters
  /-- Modeled MSH ability. -/
  | attackingCreatureTokensYouControlHaveFirst
  /-- Modeled MSH ability. -/
  | boastExileAnyNumberOfBlackCardsFromYou
  /-- Modeled MSH ability. -/
  | cosmicAwarenessAsLongAsAnOpponentHasCa
  /-- Modeled MSH ability. -/
  | creaturesWithFlyingCanTAttackYouOrBlock
  /-- Modeled MSH ability. -/
  | creaturesYouControlWith11CountersOnThe
  /-- Modeled MSH ability. -/
  | designedOnlyForKillingCreaturesYourOppon
  /-- Modeled MSH ability. -/
  | doubleAllDamageEquippedCreatureWouldDeal
  /-- Modeled MSH ability. -/
  | eachCreatureYouControlThatYouVePutOneOr
  /-- Modeled MSH ability. -/
  | eachPowerUpAbilityOfPermanentsYouControl
  /-- Modeled MSH ability. -/
  | embiggenFistWheneverYouCastASpellThat
  /-- Modeled MSH ability. -/
  | enchantedCreatureGets22
  /-- Modeled MSH ability. -/
  | enchantedCreatureGets44AndHasTrampleAn
  /-- Modeled MSH ability. -/
  | enchantedCreatureHasWard2
  /-- Modeled MSH ability. -/
  | equipWorthy1
  /-- Modeled MSH ability. -/
  | equippedCreatureGets11AndHasFlyingAnd
  /-- Modeled MSH ability. -/
  | extort
  /-- Modeled MSH ability. -/
  | ifQuicksilver
  /-- Modeled MSH ability. -/
  | ifACreatureYouControlWouldConnive
  /-- Modeled MSH ability. -/
  | ifASourceYouControlWouldDealNoncombatDam
  /-- Modeled MSH ability. -/
  | ifDamageWouldBeDealtToWolverine
  /-- Modeled MSH ability. -/
  | ifYouWouldPutOneOrMoreCountersOnAPerma
  /-- Modeled MSH ability. -/
  | improvise
  /-- Modeled MSH ability. -/
  | instantAndSorcerySpellsYouCastWithManaVa
  /-- Modeled MSH ability. -/
  | intangibilityGhostCanTBeBlocked
  /-- Modeled MSH ability. -/
  | ironManGets10ForEachOtherArtifactYou
  /-- Modeled MSH ability. -/
  | landfallWheneverALandYouControlEnters
  /-- Modeled MSH ability. -/
  | namorSPowerIsEqualToTheNumberOfMerfolk
  /-- Modeled MSH ability. -/
  | noncreatureSpellsYouCastHaveImprovise
  /-- Modeled MSH ability. -/
  | pay2LifeAddTwoManaOfAnyOneColorSpend
  /-- Modeled MSH ability. -/
  | pay2LifeCopyTargetActivatedOrTriggeredA
  /-- Modeled MSH ability. -/
  | powerUpAbilitiesOfOtherCreaturesYouContro
  /-- Modeled MSH ability. -/
  | sacrificeThisCreatureDestroyTargetNoncreat
  /-- Modeled MSH ability. -/
  | sneak1BB
  /-- Modeled MSH ability. -/
  | superAdaptoidSPowerIsEqualToTheNumberOf
  /-- Modeled MSH ability. -/
  | theRuinousWreckingCrewEntersWithX11Co
  /-- Modeled MSH ability. -/
  | wardDiscardACardOrPay2
  /-- Modeled MSH ability. -/
  | wardGetFivePoisonCounters
  /-- Modeled MSH ability. -/
  | winterSoldierGets20ForEachEquipmentAtt
  /-- Modeled MSH ability. -/
  | youHaveNoMaximumHandSize
  /-- Modeled MSH ability. -/
  | youMayActivateAbilitiesOfCreaturesYouCont
  /-- Modeled MSH ability. -/
  | youMayPlayLandsFromTheTopOfYourLibrary
  /-- Modeled MSH ability. -/
  | youMayPlayLandsFromYourGraveyard
  /-- Modeled MSH ability. -/
  | yourMaximumHandSizeIsTen
  /-- Modeled MSH ability. -/
  | enchantedCreatureLosesAllAbilitiesAndCant
deriving Repr, Inhabited, BEq

namespace ModeledStatic

/-- Official Oracle wording for this ModeledStatic. -/
def toNotation : ModeledStatic → String
  | .aresAttacksEachCombatIfAble => "Ares attacks each combat if able."
  | .artifactSpellsYouCastCost1LessToCast => "Artifact spells you cast cost {1} less to cast."
  | .asAnAdditionalCostToCastThisSpell => "As an additional cost to cast this spell, discard a card or pay {2}."
  | .asLongAsThereAreTwoOrMoreCreatureCards => "As long as there are two or more creature cards in your graveyard, Killmonger gets +2/+1."
  | .asLongAsThereAreTwoOrMoreCreatureCards2 => "As long as there are two or more creature cards in your graveyard, this creature gets +2/+2 and is all creature types."
  | .asLongAsYouControlAnArtifactCreatureOrA => "As long as you control an artifact creature or a Plan, Doctor Doom has indestructible."
  | .asLongAsYouVePutOneOrMore11Counters => "As long as you've put one or more +1/+1 counters on Beast this turn, he has flying."
  | .attackingCreatureTokensYouControlHaveFirst => "Attacking creature tokens you control have first strike."
  | .boastExileAnyNumberOfBlackCardsFromYou => "Boast — Exile any number of black cards from your graveyard with fifteen or more black mana symbols among their mana costs: Copy those exiled cards. You may cast up to three of the copies without paying their mana costs."
  | .cosmicAwarenessAsLongAsAnOpponentHasCa => "Cosmic Awareness — As long as an opponent has cast a spell this turn, you may cast spells as though they had flash."
  | .creaturesWithFlyingCanTAttackYouOrBlock => "Creatures with flying can't attack you or block creatures you control."
  | .creaturesYouControlWith11CountersOnThe => "Creatures you control with +1/+1 counters on them have trample."
  | .designedOnlyForKillingCreaturesYourOppon => "Designed Only for Killing — Creatures your opponents control get -1/-1."
  | .doubleAllDamageEquippedCreatureWouldDeal => "Double all damage equipped creature would deal."
  | .eachCreatureYouControlThatYouVePutOneOr => "Each creature you control that you've put one or more +1/+1 counters on this turn has hexproof."
  | .eachPowerUpAbilityOfPermanentsYouControl => "Each power-up ability of permanents you control can be activated an additional time."
  | .embiggenFistWheneverYouCastASpellThat => "Embiggen Fist — Whenever you cast a spell that targets a creature you control, draw a card. Until end of turn, Ms. Marvel gains \"Ms. Marvel's base power is equal to the number of cards in your hand.\""
  | .enchantedCreatureGets22 => "Enchanted creature gets +2/+2, has first strike and vigilance, and is a legendary Soldier in addition to its other types."
  | .enchantedCreatureGets44AndHasTrampleAn => "Enchanted creature gets +4/+4 and has trample and ward {1}."
  | .enchantedCreatureHasWard2 => "Enchanted creature has ward {2}."
  | .equipWorthy1 => "Equip worthy {1}"
  | .equippedCreatureGets11AndHasFlyingAnd => "Equipped creature gets +1/+1 and has flying and ward {1}."
  | .extort => "Extort"
  | .ifQuicksilver => "If Quicksilver, Brash Blur is in your opening hand, you may begin the game with him on the battlefield."
  | .ifACreatureYouControlWouldConnive => "If a creature you control would connive, instead you draw a card, then that creature connives."
  | .ifASourceYouControlWouldDealNoncombatDam => "If a source you control would deal noncombat damage to an opponent or a permanent an opponent controls, instead it deals that much damage plus X, where X is Hawkeye's power."
  | .ifDamageWouldBeDealtToWolverine => "If damage would be dealt to Wolverine, instead that damage is dealt, but all other damage already dealt to him is healed."
  | .ifYouWouldPutOneOrMoreCountersOnAPerma => "If you would put one or more counters on a permanent you control, put that many plus one of each of those kinds of counters on that permanent instead."
  | .improvise => "Improvise"
  | .instantAndSorcerySpellsYouCastWithManaVa => "Instant and sorcery spells you cast with mana value 4 or greater cost {X} less to cast, where X is The Scarlet Witch's power."
  | .intangibilityGhostCanTBeBlocked => "Intangibility — Ghost can't be blocked."
  | .ironManGets10ForEachOtherArtifactYou => "Iron Man gets +1/+0 for each other artifact you control."
  | .landfallWheneverALandYouControlEnters => "Landfall — Whenever a land you control enters, create a 1/1 green Minion creature token named Moloid with \"Whenever this token attacks, you may mill a card.\""
  | .namorSPowerIsEqualToTheNumberOfMerfolk => "Namor's power is equal to the number of Merfolk you control."
  | .noncreatureSpellsYouCastHaveImprovise => "Noncreature spells you cast have improvise."
  | .pay2LifeAddTwoManaOfAnyOneColorSpend => "Pay 2 life: Add two mana of any one color. Spend this mana only to cast Equipment spells or activate equip abilities. Activate only once each turn."
  | .pay2LifeCopyTargetActivatedOrTriggeredA => "Pay 2 life: Copy target activated or triggered ability you control from an artifact source. You may choose new targets for the copy. Activate only during your turn and only once each turn."
  | .powerUpAbilitiesOfOtherCreaturesYouContro => "Power-up abilities of other creatures you control cost {3} less to activate."
  | .sacrificeThisCreatureDestroyTargetNoncreat => "Sacrifice this creature: Destroy target noncreature artifact or noncreature enchantment. Activate only as a sorcery."
  | .sneak1BB => "Sneak {1}{B}{B}"
  | .superAdaptoidSPowerIsEqualToTheNumberOf => "Super-Adaptoid's power is equal to the number of legendary creatures you control."
  | .theRuinousWreckingCrewEntersWithX11Co => "The Ruinous Wrecking Crew enters with X +1/+1 counters on it."
  | .wardDiscardACardOrPay2 => "Ward—Discard a card or pay {2}."
  | .wardGetFivePoisonCounters => "Ward—Get five poison counters."
  | .winterSoldierGets20ForEachEquipmentAtt => "Winter Soldier gets +2/+0 for each Equipment attached to him."
  | .youHaveNoMaximumHandSize => "You have no maximum hand size."
  | .youMayActivateAbilitiesOfCreaturesYouCont => "You may activate abilities of creatures you control as though those creatures had haste."
  | .youMayPlayLandsFromTheTopOfYourLibrary => "You may play lands from the top of your library."
  | .youMayPlayLandsFromYourGraveyard => "You may play lands from your graveyard."
  | .yourMaximumHandSizeIsTen => "Your maximum hand size is ten."
  | .enchantedCreatureLosesAllAbilitiesAndCant => "Enchanted creature loses all abilities and can't become untapped."

instance : ToString ModeledStatic where
  toString := toNotation

end ModeledStatic
/-- A leftover modeled spell effect that is not yet a shared shape. -/
inductive ModeledSpell where
  /-- Modeled MSH ability. -/
  | anotherTargetCreatureYouControlGets20A
  /-- Modeled MSH ability. -/
  | artifactSpellsYouCastThisTurnCost1Less
  /-- Modeled MSH ability. -/
  | chooseTargetCreatureCardInYourGraveyardWi
  /-- Modeled MSH ability. -/
  | chooseTargetCreatureYouControlUntilEndOf
  /-- Modeled MSH ability. -/
  | chooseUpToTwoReturnThoseCardsFromYourG
  /-- Modeled MSH ability. -/
  | copyTargetActivatedOrTriggeredAbilityYouC
  /-- Modeled MSH ability. -/
  | createGalactusALegendary1616BlackElderA
  /-- Modeled MSH ability. -/
  | createX11GreenSquirrelCreatureTokensWhe
  /-- Modeled MSH ability. -/
  | createA21BlackVillainCreatureTokenWithM
  /-- Modeled MSH ability. -/
  | createATreasureTokenForEachVillainYouCon
  /-- Modeled MSH ability. -/
  | createATapped21BlackVillainCreatureToken
  /-- Modeled MSH ability. -/
  | creaturesYouControlGet11AndGainVigilan
  /-- Modeled MSH ability. -/
  | destroyUpToOneTargetArtifactOrEnchantment
  /-- Modeled MSH ability. -/
  | destroyUpToOneTargetNonlandPermanent
  /-- Modeled MSH ability. -/
  | drawACardActivateOnlyIfYouControlACrea
  /-- Modeled MSH ability. -/
  | exileAllCreaturesEachPlayerMayPutAnyNum
  /-- Modeled MSH ability. -/
  | exileAllTheCardsFromYourHandThenDrawTh
  /-- Modeled MSH ability. -/
  | forEachKindOfCounterOnTargetPermanentOr
  /-- Modeled MSH ability. -/
  | forEachNontokenCreatureYouControlCreateA
  /-- Modeled MSH ability. -/
  | gainControlOfTargetCreatureUntilEndOfTur
  /-- Modeled MSH ability. -/
  | ifThisEquipmentIsnTACreatureItBecomesA
  /-- Modeled MSH ability. -/
  | lookAtTheTopThreeCardsOfYourLibraryYou
  /-- Modeled MSH ability. -/
  | millFourCardsYouMayPutAHeroOrEnchantme
  /-- Modeled MSH ability. -/
  | millTwoCardsYouMayPutAPermanentCardFro
  /-- Modeled MSH ability. -/
  | putA11CounterAndADoubleStrikeCounter
  /-- Modeled MSH ability. -/
  | putA11CounterOnAbominationHeFightsUp
  /-- Modeled MSH ability. -/
  | putA11CounterOnHerculesHeGainsVigila
  /-- Modeled MSH ability. -/
  | putA11CounterOnWhiteTigerAndCreateTh
  /-- Modeled MSH ability. -/
  | putA11CounterOnThisCreatureAndCreate
  /-- Modeled MSH ability. -/
  | putFive11CountersOnHulk
  /-- Modeled MSH ability. -/
  | putThree11CountersOnHumanTorch
  /-- Modeled MSH ability. -/
  | putTwo11CountersOnLoki
  /-- Modeled MSH ability. -/
  | putTwo11CountersOnThanosChooseOddOr
  /-- Modeled MSH ability. -/
  | putTwo11CountersOnVivVision
  /-- Modeled MSH ability. -/
  | putTwo11CountersOnWonderMan
  /-- Modeled MSH ability. -/
  | putTwo11CountersOnThisCreatureAndCrea
  /-- Modeled MSH ability. -/
  | returnThisCardFromYourGraveyardToTheBatt
  /-- Modeled MSH ability. -/
  | returnThisCardFromYourGraveyardToYourHan
  /-- Modeled MSH ability. -/
  | returnUpToOneTargetCreatureCardFromYour
  /-- Modeled MSH ability. -/
  | revealTheTopCardOfYourLibraryIfItSAn
  /-- Modeled MSH ability. -/
  | searchYourLibraryAndOrGraveyardForAnArti
  /-- Modeled MSH ability. -/
  | superSkrullDeals4DamageToTargetCreature
  /-- Modeled MSH ability. -/
  | superSkrullGets44UntilEndOfTurn
  /-- Modeled MSH ability. -/
  | tapTargetCreatureThisAbilityCosts1Less
  /-- Modeled MSH ability. -/
  | targetVillainYouControlConnives
  /-- Modeled MSH ability. -/
  | targetArtifactYouControlBecomesACopyOfA
  /-- Modeled MSH ability. -/
  | targetCreatureGets31UntilEndOfTurn
  /-- Modeled MSH ability. -/
  | targetCreatureYouControlThatSAttackingAlo
  /-- Modeled MSH ability. -/
  | targetPlayerGains2LifeThenSearchesTheir
  /-- Modeled MSH ability. -/
  | theNextRedOrGreenCreatureSpellYouCastTh
  /-- Modeled MSH ability. -/
  | theOwnerOfTargetCreatureAnOpponentControl
  /-- Modeled MSH ability. -/
  | thisSpellCosts1LessToCastIfYouControl
  /-- Modeled MSH ability. -/
  | thisSpellCosts2LessToCastIfItTargets
  /-- Modeled MSH ability. -/
  | thisSpellCosts2LessToCastIfThereAreT
  /-- Modeled MSH ability. -/
  | thisSpellCosts2LessToCastIfYouControl
  /-- Modeled MSH ability. -/
  | untilEndOfTurnReptilBecomesADinosaurHer
  /-- Modeled MSH ability. -/
  | whenYouCastThisSpellCopyItXTimesYouM
  /-- Modeled MSH ability. -/
  | whenYouNextCastAnInstantOrSorcerySpellW
  /-- Modeled MSH ability. -/
  | youMayDrawACardForEachArtifactYouContro
  /-- Modeled MSH ability. -/
  | youMayPutAHeroCreatureCardWithManaValue
  /-- Modeled MSH ability. -/
  | youMaySacrificeAnArtifactOrDiscardACard
deriving Repr, Inhabited, BEq

namespace ModeledSpell

/-- Official Oracle wording for this ModeledSpell. -/
def toNotation : ModeledSpell → String
  | .anotherTargetCreatureYouControlGets20A => "Another target creature you control gets +2/+0 and gains hexproof until end of turn"
  | .artifactSpellsYouCastThisTurnCost1Less => "Artifact spells you cast this turn cost {1} less to cast"
  | .chooseTargetCreatureCardInYourGraveyardWi => "Choose target creature card in your graveyard with mana value 4 or less. If this spell was cast using teamwork, instead choose target creature card in your graveyard. Return the chosen card to the battlefield."
  | .chooseTargetCreatureYouControlUntilEndOf => "Choose target creature you control. Until end of turn, double its power and toughness and it gains trample"
  | .chooseUpToTwoReturnThoseCardsFromYourG => "Choose up to two. Return those cards from your graveyard to your hand. • Target artifact card. • Target creature card. • Target enchantment card. • Target land card."
  | .copyTargetActivatedOrTriggeredAbilityYouC => "Copy target activated or triggered ability you control from a creature source. You may choose new targets for the copy"
  | .createGalactusALegendary1616BlackElderA => "Create Galactus, a legendary 16/16 black Elder Alien creature token with flying, trample, and \"Whenever Galactus attacks, destroy target land.\""
  | .createX11GreenSquirrelCreatureTokensWhe => "Create X 1/1 green Squirrel creature tokens, where X is the number of Squirrels you control"
  | .createA21BlackVillainCreatureTokenWithM => "Create a 2/1 black Villain creature token with menace, then creatures you control get +1/+0 until end of turn."
  | .createATreasureTokenForEachVillainYouCon => "Create a Treasure token for each Villain you control"
  | .createATapped21BlackVillainCreatureToken => "Create a tapped 2/1 black Villain creature token with menace. Activate only if there are two or more creature cards in your graveyard"
  | .creaturesYouControlGet11AndGainVigilan => "Creatures you control get +1/+1 and gain vigilance until end of turn"
  | .destroyUpToOneTargetArtifactOrEnchantment => "Destroy up to one target artifact or enchantment. Put a +1/+1 counter on She-Hulk"
  | .destroyUpToOneTargetNonlandPermanent => "Destroy up to one target nonland permanent"
  | .drawACardActivateOnlyIfYouControlACrea => "Draw a card. Activate only if you control a creature with toughness 4 or greater"
  | .exileAllCreaturesEachPlayerMayPutAnyNum => "Exile all creatures. Each player may put any number of creature cards from their hand onto the battlefield. Then put all cards exiled this way into their owners' hands. Exile Worlds Within Worlds."
  | .exileAllTheCardsFromYourHandThenDrawTh => "Exile all the cards from your hand, then draw that many cards. Until the end of your next turn, you may play cards exiled this way."
  | .forEachKindOfCounterOnTargetPermanentOr => "For each kind of counter on target permanent or player, give that permanent or player another counter of that kind"
  | .forEachNontokenCreatureYouControlCreateA => "For each nontoken creature you control, create a token that's a copy of that creature, except it isn't legendary."
  | .gainControlOfTargetCreatureUntilEndOfTur => "Gain control of target creature until end of turn. If you control a Villain with greater mana value than that creature, gain control of that creature until the end of your next turn instead. Untap that creature. It gains haste until end of turn."
  | .ifThisEquipmentIsnTACreatureItBecomesA => "If this Equipment isn't a creature, it becomes a 0/0 Construct Hero artifact creature with flying and \"This creature gets +1/+1 for each artifact you control\" until end of turn"
  | .lookAtTheTopThreeCardsOfYourLibraryYou => "Look at the top three cards of your library. You may reveal a Hero card from among them and put it into your hand. Put the rest on the bottom of your library in any order"
  | .millFourCardsYouMayPutAHeroOrEnchantme => "Mill four cards. You may put a Hero or enchantment card from among those cards into your hand"
  | .millTwoCardsYouMayPutAPermanentCardFro => "Mill two cards. You may put a permanent card from among the milled cards into your hand. You gain 2 life."
  | .putA11CounterAndADoubleStrikeCounter => "Put a +1/+1 counter and a double strike counter on Quicksilver"
  | .putA11CounterOnAbominationHeFightsUp => "Put a +1/+1 counter on Abomination. He fights up to one target creature an opponent controls"
  | .putA11CounterOnHerculesHeGainsVigila => "Put a +1/+1 counter on Hercules. He gains vigilance, indestructible, and haste until end of turn"
  | .putA11CounterOnWhiteTigerAndCreateTh => "Put a +1/+1 counter on White Tiger and create The Tiger God, a legendary 4/4 green Cat God creature token with \"The Tiger God can't be blocked by more than one creature.\""
  | .putA11CounterOnThisCreatureAndCreate => "Put a +1/+1 counter on this creature and create a 3/2 white Hero creature token with vigilance"
  | .putFive11CountersOnHulk => "Put five +1/+1 counters on Hulk"
  | .putThree11CountersOnHumanTorch => "Put three +1/+1 counters on Human Torch"
  | .putTwo11CountersOnLoki => "Put two +1/+1 counters on Loki"
  | .putTwo11CountersOnThanosChooseOddOr => "Put two +1/+1 counters on Thanos. Choose odd or even. Destroy each other creature with mana value of the chosen quality"
  | .putTwo11CountersOnVivVision => "Put two +1/+1 counters on Viv Vision"
  | .putTwo11CountersOnWonderMan => "Put two +1/+1 counters on Wonder Man"
  | .putTwo11CountersOnThisCreatureAndCrea => "Put two +1/+1 counters on this creature and create a 2/2 colorless Robot Villain artifact creature token"
  | .returnThisCardFromYourGraveyardToTheBatt => "Return this card from your graveyard to the battlefield with a finality counter on him. Then you may attach an Equipment you control to him"
  | .returnThisCardFromYourGraveyardToYourHan => "Return this card from your graveyard to your hand"
  | .returnUpToOneTargetCreatureCardFromYour => "Return up to one target creature card from your graveyard to your hand. Put two +1/+1 counters on this creature"
  | .revealTheTopCardOfYourLibraryIfItSAn => "Reveal the top card of your library. If it's an artifact card, draw a card"
  | .searchYourLibraryAndOrGraveyardForAnArti => "Search your library and/or graveyard for an artifact creature card with mana value X or less and put it onto the battlefield with X additional +1/+1 counters on it. If X is 4 or greater, it gains haste until end of turn. If you search your library this way, shuffle."
  | .superSkrullDeals4DamageToTargetCreature => "Super-Skrull deals 4 damage to target creature"
  | .superSkrullGets44UntilEndOfTurn => "Super-Skrull gets +4/+4 until end of turn"
  | .tapTargetCreatureThisAbilityCosts1Less => "Tap target creature. This ability costs {1} less to activate if it targets a creature with power 3 or less"
  | .targetVillainYouControlConnives => "Target Villain you control connives"
  | .targetArtifactYouControlBecomesACopyOfA => "Target artifact you control becomes a copy of a second target artifact you control until end of turn, except it isn't legendary"
  | .targetCreatureGets31UntilEndOfTurn => "Target creature gets +3/+1 until end of turn.\nExile the top card of your library. Until the end of your next turn, you may play that card."
  | .targetCreatureYouControlThatSAttackingAlo => "Target creature you control that's attacking alone gets +1/+0 until end of turn. You gain 1 life"
  | .targetPlayerGains2LifeThenSearchesTheir => "Target player gains 2 life, then searches their library for a basic land card, puts it onto the battlefield tapped, then shuffles. Put a +1/+1 counter on up to one target creature."
  | .theNextRedOrGreenCreatureSpellYouCastTh => "The next red or green creature spell you cast this turn can be cast without paying its mana cost"
  | .theOwnerOfTargetCreatureAnOpponentControl => "The owner of target creature an opponent controls puts it into their library second from the top or on the bottom. Then up to one target creature you control connives."
  | .thisSpellCosts1LessToCastIfYouControl => "This spell costs {1} less to cast if you control a Villain.\nYou draw two cards and lose 2 life."
  | .thisSpellCosts2LessToCastIfItTargets => "This spell costs {2} less to cast if it targets an attacking creature.\nTarget creature gets -4/-0 until end of turn.\nDraw a card."
  | .thisSpellCosts2LessToCastIfThereAreT => "This spell costs {2} less to cast if there are two or more creature cards in your graveyard.\nTarget creature you control deals damage equal to twice its power to target creature an opponent controls."
  | .thisSpellCosts2LessToCastIfYouControl => "This spell costs {2} less to cast if you control a Vehicle.\nTruck Toss deals 4 damage to any target."
  | .untilEndOfTurnReptilBecomesADinosaurHer => "Until end of turn, Reptil becomes a Dinosaur Hero with base power and toughness 3/5 and gains reach and vigilance"
  | .whenYouCastThisSpellCopyItXTimesYouM => "When you cast this spell, copy it X times. You may choose new targets for the copies.\nPhoton Blast Barrage deals 1 damage to target creature."
  | .whenYouNextCastAnInstantOrSorcerySpellW => "When you next cast an instant or sorcery spell with mana value less than or equal to Loki's power this turn, copy that spell. You may choose new targets for the copy"
  | .youMayDrawACardForEachArtifactYouContro => "You may draw a card for each artifact you control. If you do, each opponent draws a card"
  | .youMayPutAHeroCreatureCardWithManaValue => "You may put a Hero creature card with mana value 3 or less from your hand onto the battlefield. If you don't, draw a card"
  | .youMaySacrificeAnArtifactOrDiscardACard => "You may sacrifice an artifact or discard a card. If you do, draw two cards."

instance : ToString ModeledSpell where
  toString := toNotation

end ModeledSpell
/-- How leftover “add one mana of any color; spend only …” restricts the mana. -/
inductive RestrictedManaSpend where
  /-- Hero spells and Hero sources. -/
  | hero
  /-- Villain spells and Villain sources. -/
  | villain
  /-- Artifact spells. -/
  | artifactSpell
deriving Repr, Inhabited, BEq

namespace RestrictedManaSpend

/-- Official Oracle “Spend this mana only …” clause. -/
def spendClause : RestrictedManaSpend → String
  | .hero => "to cast a Hero spell or to activate an ability of a Hero source"
  | .villain => "to cast a Villain spell or to activate an ability of a Villain source"
  | .artifactSpell => "to cast an artifact spell"

end RestrictedManaSpend

/-- A leftover modeled activation that is not yet a shared shape. -/
inductive ModeledAbility where
  /-- Modeled MSH ability. -/
  | mentalOrganismPay3LifeMODOK
  /-- Modeled MSH ability. -/
  | tyrannosaurusRex6UntilEndOfTu
  /-- Modeled MSH ability. -/
  | addXManaOfAnyOneColorWhereXIsDocSams
  /-- Modeled MSH ability. -/
  | addFourManaInAnyCombinationOfColors
  /-- Add one mana of any color, spendable only as `kind` describes. -/
  | addOneManaOfAnyColorSpendOnly (kind : RestrictedManaSpend)
  /-- Modeled MSH ability. -/
  | addTwoManaOfAnyOneColorSpendThisManaO
  /-- `{T}: Add {A} or {B}`, optionally only if this land entered this turn
  or you control a basic land. -/
  | addOneOf (a b : Color) (enteredOrBasic : Bool := false)
  /-- Modeled MSH ability. -/
  | addCCC
  /-- Modeled MSH ability. -/
  | addUThisManaCanTBeSpentToCastANona
  /-- Modeled MSH ability. -/
  | addW
  /-- Modeled MSH ability. -/
  | n1BDiscardThisCard
  /-- Modeled MSH ability. -/
  | n2TDiscardACard
  /-- Modeled MSH ability. -/
  | n2BSacrificeAnArtifactOrCreatur
  /-- Modeled MSH ability. -/
  | n2GTRemoveAnyNumberOf11
  /-- Modeled MSH ability. -/
  | n2RDiscardThisCard
  /-- Modeled MSH ability. -/
  | n3TSacrificeAnArtifactOrDisca
  /-- Modeled MSH ability. -/
  | n3TSacrificeAnArtifact
  /-- Modeled MSH ability. -/
  | n3USacrificeThisArtifact
  /-- Modeled MSH ability. -/
  | tPutAStunCounterOnJessicaJones
  /-- Modeled MSH ability. -/
  | tSacrificeAnEquipmentAttachedTo
  /-- Modeled MSH ability. -/
  | harnessTheMindStone
  /-- Modeled MSH ability. -/
  | targetPlayerDrawsFourCards
deriving Repr, Inhabited, BEq

namespace ModeledAbility

/-- Official Oracle wording for this ModeledAbility. -/
def toNotation : ModeledAbility → String
  | .mentalOrganismPay3LifeMODOK => "Mental Organism — Pay 3 life: M.O.D.O.K. connives. Activate only during your turn."
  | .tyrannosaurusRex6UntilEndOfTu => "Tyrannosaurus Rex — {6}: Until end of turn, Reptil becomes a Dinosaur Hero with base power and toughness 6/6 and gains trample."
  | .addXManaOfAnyOneColorWhereXIsDocSams => "Add X mana of any one color, where X is Doc Samson's power"
  | .addFourManaInAnyCombinationOfColors => "Add four mana in any combination of colors"
  | .addOneManaOfAnyColorSpendOnly kind =>
    s!"Add one mana of any color. Spend this mana only {kind.spendClause}"
  | .addTwoManaOfAnyOneColorSpendThisManaO => "Add two mana of any one color. Spend this mana only to activate abilities of creature sources"
  | .addOneOf a b enteredOrBasic =>
    let base := s!"Add \{{a.letter}} or \{{b.letter}}"
    if enteredOrBasic then
      s!"{base}. Activate only if this land entered this turn or if you control a basic land"
    else base
  | .addCCC => "Add {C}{C}{C}"
  | .addUThisManaCanTBeSpentToCastANona => "Add {U}. This mana can't be spent to cast a nonartifact spell"
  | .addW => "Add {W}"
  | .n1BDiscardThisCard => "{1}{B}, Discard this card: Search your library for a Plan card, reveal it, put it into your hand, then shuffle."
  | .n2TDiscardACard => "{2}, {T}, Discard a card: Draw a card for each card you've discarded this turn."
  | .n2BSacrificeAnArtifactOrCreatur => "{2}{B}, Sacrifice an artifact or creature: Draw a card."
  | .n2GTRemoveAnyNumberOf11 => "{2}{G}, {T}, Remove any number of +1/+1 counters from The Astonishing Ant-Man: Create that many 1/1 green Insect creature tokens."
  | .n2RDiscardThisCard => "{2}{R}, Discard this card: It deals 2 damage to each creature."
  | .n3TSacrificeAnArtifactOrDisca => "{3}, {T}, Sacrifice an artifact or discard a nonland card: Bullseye deals 2 damage to any target."
  | .n3TSacrificeAnArtifact => "{3}, {T}, Sacrifice an artifact: Create a 3/3 colorless Robot Villain artifact creature token named Doombot. Activate only as a sorcery."
  | .n3USacrificeThisArtifact => "{3}{U}, Sacrifice this artifact: Draw two cards."
  | .tPutAStunCounterOnJessicaJones => "{T}, Put a stun counter on Jessica Jones: Exile the top X cards of your library, where X is Jessica Jones's power. You may play those cards this turn."
  | .tSacrificeAnEquipmentAttachedTo => "{T}, Sacrifice an Equipment attached to Ronin: Target creature gets -4/-4 until end of turn. Activate only as a sorcery."
  | .harnessTheMindStone => "Harness The Mind Stone"
  | .targetPlayerDrawsFourCards => "Target player draws four cards"

instance : ToString ModeledAbility where
  toString := toNotation

/-- `{T}: Add` types this modeled MSH ability produces for the demo `tap`
command and other mana-ability payment (CR 605.3a). -/
def addManaTypes : ModeledAbility → Array ManaType
  | .addW => #[.colored .white]
  | .addOneOf a b _ => #[.colored a, .colored b]
  | .addCCC => #[.colorless, .colorless, .colorless]
  | .addUThisManaCanTBeSpentToCastANona => #[.colored .blue]
  | _ => #[]

/-- True when the add ability may be activated only if this land entered this
turn or if you control a basic land. -/
def requiresEnteredOrBasic : ModeledAbility → Bool
  | .addOneOf _ _ true => true
  | _ => false

#guard addManaTypes (.addOneOf .blue .black true) ==
  #[.colored .blue, .colored .black]
#guard addManaTypes (.addOneOf .blue .black) == #[.colored .blue, .colored .black]
#guard requiresEnteredOrBasic (.addOneOf .blue .black true)
#guard !(requiresEnteredOrBasic (.addOneOf .blue .black))
#guard toNotation (.addOneOf .blue .black) == "Add {U} or {B}"
#guard toNotation (.addOneOf .blue .black true) ==
  "Add {U} or {B}. Activate only if this land entered this turn or if you control a basic land"
#guard toNotation (.addOneManaOfAnyColorSpendOnly .hero) ==
  "Add one mana of any color. Spend this mana only to cast a Hero spell or to activate an ability of a Hero source"
#guard toNotation (.addOneManaOfAnyColorSpendOnly .villain) ==
  "Add one mana of any color. Spend this mana only to cast a Villain spell or to activate an ability of a Villain source"
#guard toNotation (.addOneManaOfAnyColorSpendOnly .artifactSpell) ==
  "Add one mana of any color. Spend this mana only to cast an artifact spell"

end ModeledAbility
/-- A leftover modeled Saga chapter that is not yet a shared shape. -/
inductive ModeledChapter where
  /-- Modeled MSH ability. -/
  | gainControlOfUpToTwoTargetCreaturesWith
  /-- Modeled MSH ability. -/
  | harnessTheMindStone
  /-- Modeled MSH ability. -/
  | thisSagaDeals2DamageToEachNonVillainCre
  /-- Modeled MSH ability. -/
  | thisSagaDealsXDamageToTargetOpponentWhe
deriving Repr, Inhabited, BEq

namespace ModeledChapter

/-- Official Oracle wording for this ModeledChapter. -/
def toNotation : ModeledChapter → String
  | .gainControlOfUpToTwoTargetCreaturesWith => "Gain control of up to two target creatures with total mana value 6 or less for as long as this Saga remains on the battlefield"
  | .harnessTheMindStone => "Harness The Mind Stone"
  | .thisSagaDeals2DamageToEachNonVillainCre => "This Saga deals 2 damage to each non-Villain creature and each opponent"
  | .thisSagaDealsXDamageToTargetOpponentWhe => "This Saga deals X damage to target opponent, where X is the greatest mana value among artifacts you control"

instance : ToString ModeledChapter where
  toString := toNotation

end ModeledChapter
end Mtg.Engine
