import Mtg.Engine.Card.Trigger

/-!
# Shared-trigger effect constructors

`Effect.ofTrigger` plus the `Effect.enter*` / `step*` / `death*` /
`watch*` / `casting*` / `resource*` constructors that lift shared triggers
onto unified effects.
-/

namespace Mtg.Engine

namespace Effect

/-- Convert a shared trigger effect to the unified `Effect`. -/
def ofTrigger (e : SharedTrigger) : Effect :=
  let t := e.timing
  { events := t.events
    targeting := t.targeting
    allowsZeroTargets := t.allowsZeroTargets
    maxTargets := t.maxTargets
    dividedDamage := t.dividedDamage
    onceEachTurn := t.onceEachTurn
    optionalOnceEachTurn := t.optionalOnceEachTurn
    resolution := t.resolution
    sharedTrigger := some e
    phrase := "" }

/-- Direct triggered-ability `Effect` factories (CR 603 / 608). -/
def enterDestroy (kind : EffectTargetKind) : Effect :=
  { events := #[.entering], targeting := .of kind, resolution := .destroy .target }

def enterDealDamageUpToOne (n : Nat) : Effect :=
  { events := #[.entering], targeting := .of .creature, allowsZeroTargets := true
    resolution := .dealDamage (.fixed n) .target
    phrase := s!"When this permanent enters, it deals {n} damage to up to one target creature." }

def enterFightUpToOne : Effect :=
  { events := #[.entering], targeting := .of .anotherCreature, allowsZeroTargets := true
    resolution := .fight }

def enterReturnNonlandNontoken : Effect :=
  { events := #[.entering], targeting := .of .nonlandNontoken, allowsZeroTargets := true
    resolution := .returnToHand .permanent .returnedPermanent }

def enterCreateZabu : Effect :=
  { events := #[.entering], resolution := .createTokens .zabu (.fixed 1) false }

def enterOppCreatesTheVoid : Effect :=
  { events := #[.entering], targeting := .of .opponent
    resolution := .createTokens .theVoid (.fixed 1) false (.target .opponent) }

def enterCreateSturdyShieldAttach : Effect :=
  { events := #[.entering]
    resolution := .sequence
      [.createTokens .sturdyShield (.fixed 1) false (note := .remember),
       .attach .createdToken .source] }

def enterExileGyPlayUntilNextTurn : Effect :=
  { events := #[.entering], targeting := .of .equipmentInstantOrSorceryInYourGraveyard
    resolution := .sequence
      [.exile .graveyardCard .forLater .playCard, .grant .playNotedUntilNextTurn .target] }

def enterReturnGyPermanentThisTurn : Effect :=
  { events := #[.entering], targeting := .of .permanentCardInYourGraveyard
    resolution := .returnToHand .graveyardPermanent }

def enterTapOppCantUntapWhileControl : Effect :=
  { events := #[.entering], targeting := .of .oppCreature
    resolution := .sequence [.tap .target, .cant .untapWhileYouControl] }

def enterMaySacAnotherThenDestroyOppNonland : Effect :=
  { events := #[.entering]
    resolution := .may (.pay (.sacrifice (.fixed 1) .another)) (.queueReflexive (.destroy .target)) .ifYouDo }

def enterMaySacOrDiscardNonlandThenDamage : Effect :=
  { events := #[.entering]
    resolution := .may (.pay (.or [.sacrifice (.fixed 1) .artifact, .discard (.fixed 1) .nonland]))
      (.queueReflexive (.dealDamage (.fixed 2) .target)) .ifYouDo }

def enterRevealHandExileUntilLeaves : Effect :=
  { events := #[.entering], targeting := .of .opponent, allowsZeroTargets := true
    resolution := .revealFromHand .hand (.exile .target .untilSourceLeaves) }

def enterPlusOnesOrReturnArtEnch : Effect :=
  { events := #[.entering], targeting := .of .creature, allowsZeroTargets := true
    resolution := .or
      [.putCounters (.ofKind .plusOnePlusOne) .permanent,
       .returnToHand .graveyardCard] }

def enterChooseUpToXModes : Effect :=
  { events := #[.entering], targeting := .of .opponent, allowsZeroTargets := true
    resolution := .chooseModes TriggeredAbility.TriggerResolution.upToXModes .alreadyChosen }

def enterMayTapThenGrantIndestructible : Effect :=
  { events := #[.entering]
    resolution := .may (.tap .source) (.queueReflexive (.grant (.keywords Keyword.indestructible) .target)) .ifYouDo }

def enterTapLoseAbilitiesWhileSource : Effect :=
  { events := #[.entering], targeting := .of .creature, allowsZeroTargets := true
    resolution := .sequence
      [.tap (.target .ifPresent), .lose .allAbilities (.target .ifPresent)] }

def enterRevealDiscardFromHand : Effect :=
  { events := #[.entering], targeting := .of .player
    resolution := .revealFromHand .onePlusCreatureCards
      (.discard (.cards 1 (.target .opponent))) }

def enterCreateRedwing : Effect :=
  { events := #[.entering], resolution := .createTokens .redwing (.fixed 1) false }

def stepEnchantedControllerDraws : Effect :=
  { events := #[.enchantedControllerUpkeep]
    resolution := .draw (.fixed 1) (who := .controller .enchanted)
    phrase := "At the beginning of the upkeep of enchanted creature's controller, that player draws a card." }

def stepDrawToTen : Effect :=
  { events := #[.yourEndStep], resolution := .draw (.upToHandSize 10)
    phrase := "At the beginning of your end step, if you have fewer than ten cards in hand, draw cards equal to the difference." }

def stepCopyAbsorbingMan : Effect :=
  { events := #[.yourFirstMain]
    targeting := .of (.filtered {
      noun := "up to one target artifact, non-Aura enchantment, or land"
      types := #[.artifact, .enchantment, .land]
      nonAura := true })
    allowsZeroTargets := true, maxTargets := 1
    resolution := .becomeCopy .artifactEnchantmentOrLand
    phrase := "At the beginning of your first main phase, until your next turn, Absorbing Man becomes a copy of up to one target artifact, non-Aura enchantment, or land, except his name is Absorbing Man, he's a legendary 4/4 Human Villain creature in addition to his other types, and he has vigilance." }

def stepHydeChoose : Effect :=
  { events := #[.yourUpkeep]
    resolution := .chooseModes TriggeredAbility.TriggerResolution.hydeModes .plusOneOrRemoveCounter
    phrase := "At the beginning of your upkeep, choose one — • Put a +1/+1 counter on Mister Hyde. • Remove a counter from a creature you control. If you do, draw a card." }

def stepCopyTaskmaster : Effect :=
  { events := #[.yourFirstMain], targeting := .of .creatureOrGyCreatureCard
    allowsZeroTargets := true, maxTargets := 1
    resolution := .becomeCopy .creatureOrGraveyardCard
    phrase := "Photographic Reflexes — At the beginning of your first main phase, until your next turn, Taskmaster becomes a copy of up to one target creature on the battlefield or creature card in a graveyard, except his name is Taskmaster, Mercenary Mimic and he's a legendary Human Mercenary Villain creature." }

def stepHarnessedFlicker : Effect :=
  { events := #[.yourEndStep]
    targeting := .of (.filtered {
      noun := "up to one other target nonland permanent you control"
      nonland := true, controller := .you, another := true })
    allowsZeroTargets := true, maxTargets := 1
    resolution := .«if» (.atLeast (.count .harnessedSource) (.fixed 1)) (.exile .target .returnImmediately)
    phrase := "∞ — At the beginning of your end step, exile up to one other target nonland permanent you control, then return that card to the battlefield under its owner's control." }

def deathHellcatReturn : Effect :=
  { events := #[.dying]
    resolution := .put .source .underOwner (.entering [
      .loseAllAbilities, .keywords Keyword.haste,
      .counter .plusOnePlusOne (asEnters := true)])
    phrase := "When Hellcat dies, return her to the battlefield under her owner's control with a +1/+1 counter on her. She loses all abilities and gains haste." }

def deathVillainReturnAsHero : Effect :=
  { events := #[.villainYouControlDies]
    resolution := .put (.cause (some "Villain")) .underOwner (.entering [
      .additionalSubtype "Hero", .counter .finality])
    phrase := "Whenever a Villain you control dies, return it to the battlefield under its owner's control with a finality counter on it. That creature is a Hero in addition to its other types." }

def deathAttackingReturnHand : Effect :=
  { events := #[.attackingCreatureYouControlDies]
    resolution := .returnToHand .cause
    phrase := "Whenever an attacking creature you control dies, return that card to its owner's hand." }

def deathDeathtouchOppSac : Effect :=
  { events := #[.creatureYouControlDies]
    resolution := .sacrifice .chosenNontokenCreature
    phrase := "Whenever another creature you control with deathtouch dies, each opponent sacrifices a nontoken creature of their choice." }

def thisAttackMayPayPlusOne : Effect :=
  { events := #[.attacking]
    resolution := .may (.pay (.mana #[.generic 1])) (.queueReflexive (.putCounters (.ofKind .plusOnePlusOne) .permanent)) .ifYouDo
    phrase := "Whenever Ant-Man attacks, you may pay {1}. When you do, put a +1/+1 counter on target creature." }

def thisAttackPayReturnAttacking : Effect :=
  { events := #[.attacking]
    resolution := .may (.pay (.mana #[.generic 3, .colored .black]))
      (.queueReflexive (.put .creatureCard .tapped (.entering [.attacking, .counter .finality]))) .ifYouDo
    phrase := "Whenever Grim Reaper attacks, you may pay {3}{B}. When you do, return target creature card from your graveyard to the battlefield tapped and attacking with a finality counter on it." }

def thisAttackIfArtifactEnteredDraw : Effect :=
  { events := #[.attacking]
    resolution := .«if» .artifactEnteredThisTurn (.draw (.fixed 1))
    phrase := "Whenever Iron Man attacks, if an artifact entered the battlefield under your control this turn, draw a card." }

def thisAttackBlinkNontoken : Effect :=
  { events := #[.attacking]
    targeting := .of (.filtered {
      noun := "up to one target nontoken artifact or creature"
      types := #[.artifact, .creature], nontoken := true })
    allowsZeroTargets := true, maxTargets := 1
    resolution := .exile .target .returnTapped
    phrase := "Whenever The Mighty Thor attacks, exile up to one target nontoken artifact or creature, then return that card to the battlefield tapped under its owner's control." }

def thisAttackEquippedDrain : Effect :=
  { events := #[.attacking]
    resolution := .«if» .attachedEquipment (.sequence [
      .loseLife .attachedEquipment .eachOpponent,
      .gainLife .attachedEquipment])
    phrase := "Whenever Whiplash attacks, if he's equipped, each opponent loses X life and you gain X life, where X is the number of Equipment attached to him." }

def thisAttackDrawIfPower4 : Effect :=
  { events := #[.attacking]
    resolution := .«if» (.atLeast .equalSourcePower (.fixed 4)) (.draw (.fixed 1))
    phrase := "Cybernetic Senses — Whenever Viv Vision attacks, draw a card if her power is 4 or greater." }

def thisAttackAttacksAlonePlus2Indestructible : Effect :=
  { events := #[.attacking]
    resolution := .sequence [
      .pump (.fixed 2) (.fixed 0) .source,
      .grant (.keywords Keyword.indestructible) .source]
    phrase := "Unbreakable Skin — Whenever Luke Cage attacks alone, he gets +2/+0 and gains indestructible until end of turn." }

def enterOrAttackCopyKeywords : Effect :=
  { events := #[.entering, .attacking], targeting := .of .anotherCreature
    resolution := .putCounters .missingKeywordsFromTarget .source
    phrase := "Whenever Super-Adaptoid enters or attacks, choose another target creature. If that creature has haste and Super-Adaptoid doesn't, put a haste counter on Super-Adaptoid. Do the same for flying, first strike, double strike, deathtouch, indestructible, lifelink, menace, reach, trample, and vigilance." }

def enterOrAttackCreateSquirrel : Effect :=
  { events := #[.entering, .attacking]
    resolution := .createTokens .squirrel11green (.fixed 1) false
    phrase := "Do You Like Squirrels? — Whenever The Unbeatable Squirrel Girl enters or attacks, create a 1/1 green Squirrel creature token." }

def watchCombatDamageExileUntilNonland : Effect :=
  { events := #[.dealsCombatDamageToPlayer]
    resolution := .revealLibrary .untilNonland
      (.may (.putCounters (.ofKind .plusOnePlusOne) .source)
        (.exile .top .forLater .anyManaThisTurn) .ifYouDont)
      .announced
    phrase := "Whenever Black Widow deals combat damage to a player, that player exiles cards from the top of their library until they exile a nonland card. You may put a +1/+1 counter on Black Widow. If you don't, you may cast the exiled nonland card until end of turn and mana of any type can be spent to cast that spell." }

def watchAttacksAloneDrain : Effect :=
  { events := #[.creatureYouControlAttacksAlone], targeting := .of .opponent
    resolution := .sequence [.loseLife (.fixed 1) (.target .opponent), .gainLife (.fixed 1)]
    phrase := "Whenever a creature you control attacks alone, target opponent loses 1 life and you gain 1 life." }

def watchAttacksAloneFirstStrikeMenace : Effect :=
  { events := #[.creatureYouControlAttacksAlone]
    resolution := .grant (.keywords (Keywords.merge Keyword.firstStrike Keyword.menace)) .attackingAlone
    phrase := "Whenever a creature you control attacks alone, it gains first strike and menace until end of turn." }

def watchFirstTapUntap : Effect :=
  { events := #[.creatureYouControlTapped], resolution := .untap .firstThisTurn
    phrase := "Whenever a creature you control becomes tapped during your turn, if it's the first time that creature has become tapped this turn, untap it." }

def watchSheHulkRedirectOnce : Effect :=
  { events := #[.creatureYouControlDealtDamage], targeting := .of .playerOrCreature
    resolution := .may (.dealDamage .lastKnownPower .target) (.sequence []) .ifYouDo
    phrase := "Whenever a creature you control is dealt damage, you may have The Sensational She-Hulk deal that much damage to any target. Do this only once each turn." }

def watchSpeedballTargeted : Effect :=
  { events := #[.spellTargetsSource]
    resolution := .sequence [
      .pump (.fixed 2) (.fixed 2) .source, .may (.grant .newTargets .causingSpell) (.sequence []) .ifYouDo]
    phrase := "Whenever a player casts a spell that targets Speedball, he gets +2/+2 until end of turn. You may choose new targets for that spell." }

def watchAnyPlayerSecondDraw : Effect :=
  { events := #[.anyPlayerDrawsSecond], resolution := .draw (.fixed 1)
    phrase := "Whenever a player draws their second card each turn, you draw a card." }

def watchYouTargetDrawOnce : Effect :=
  { events := #[.youTargetSomething], onceEachTurn := true, resolution := .draw (.fixed 1)
    phrase := "Whenever a player or permanent becomes the target of an ability you control, draw a card. This ability triggers only once each turn." }

def watchVillainOrArtifactDamage : Effect :=
  { events := #[.anotherVillainOrArtifactEnters], targeting := .of .opponent
    resolution := .dealDamage (.fixed 1) (.player (.target .opponent))
    phrase := "Whenever another Villain and/or artifact you control enters, this creature deals 1 damage to target opponent." }

def watchVillainConniveOnce : Effect :=
  { events := #[.anotherVillainEnters], optionalOnceEachTurn := true
    resolution := .connive .enteringVillain
    phrase := "Whenever another Villain you control enters, you may have it connive. Do this only once each turn." }

def watchVillainPlusOneDamageOnce : Effect :=
  { events := #[.anotherVillainEnters], onceEachTurn := true
    resolution := .sequence [
      .putCounters (.ofKind .plusOnePlusOne) .sourceIfPresent,
      .dealDamage (.fixed 2) (.player .eachOpponent)]
    phrase := "Whenever another Villain you control enters, put a +1/+1 counter on Crossbones. He deals 2 damage to each opponent. This ability triggers only once each turn." }

def watchVillainAttachEquipment : Effect :=
  { events := #[.anotherVillainEnters]
    targeting := .of .upToOneEquipmentThenCreatureYouControl
    resolution := .attach .announcedEquipment .announcedCreature
    phrase := "Whenever another Villain you control enters, attach up to one target Equipment you control to target creature you control." }

def watchVillainPlusOneLifelink : Effect :=
  { events := #[.anotherVillainEnters]
    resolution := .sequence [
      .pump (.fixed 1) (.fixed 0) .source, .grant (.keywords Keyword.lifelink) .source]
    phrase := "Whenever another Villain you control enters, Yellowjacket gets +1/+0 and gains lifelink until end of turn." }

def watchHulklingCompare : Effect :=
  { events := #[.anotherCreatureYouControlEnters]
    resolution := .«if» (.or [.causeGreaterPower, .causeGreaterToughness])
      (.putCounters (.ofKind .plusOnePlusOne) .source)
    phrase := "Whenever another creature you control enters, if it has greater power or toughness than Hulkling, put a +1/+1 counter on Hulkling." }

def watchJusticeBounce : Effect :=
  { events := #[.anotherNonlandReturned]
    resolution := .putCounters (.ofKind .plusOnePlusOne) .source
    phrase := "Whenever another nonland permanent you control is returned to its owner's hand, put a +1/+1 counter on Justice." }

def watchNontokenHeroModal : Effect :=
  { events := #[.anotherNontokenHeroEnters]
    resolution := .chooseModes
      [.createTokens .soldier11white (.fixed 1) false,
       .pump (.fixed 1) (.fixed 1) .creaturesYouControl]
      .fromLastKnown
    phrase := "Whenever another nontoken Hero you control enters, choose one — • Create a 1/1 white Soldier creature token. • Creatures you control get +1/+1 until end of turn." }

def watchUltronCopy : Effect :=
  { events := #[.anotherNontokenArtifactEnters]
    resolution := .may (.pay (.mana #[.generic 2])) (.becomeCopy .cause) .ifYouDo
    phrase := "Whenever another nontoken artifact you control enters, you may pay {2}. If you do, create a token that's a copy of it. If the token isn't a creature, it becomes a 2/2 Robot Villain creature in addition to its other types." }

def watchEnchantedAttachEquipment : Effect :=
  { events := #[.enchantedAttacksOrBlocks], targeting := .of .equipmentYouControl
    allowsZeroTargets := true, maxTargets := 1000
    resolution := .attach (.target .eachEquipment) .enchantedCreature
    phrase := "Whenever enchanted creature attacks or blocks, attach any number of target Equipment you control to it." }

def watchEquippedAttacksAloneUntapScry : Effect :=
  { events := #[.equippedAttacksAlone]
    resolution := .sequence [.untap .equipped, .scry (.fixed 1)]
    phrase := "Whenever equipped creature attacks alone, untap it and scry 1." }

def watchEquippedAttacksTap : Effect :=
  { events := #[.equippedAttacks], targeting := .of .defendingPlayerCreature
    resolution := .tap .target
    phrase := "Whenever equipped creature attacks, tap target creature defending player controls." }

def watchEquippedTappedDamage : Effect :=
  { events := #[.equippedBecomesTapped]
    resolution := .dealDamage (.fixed 1) (.player .eachOpponent) .fromEquipped
    phrase := "Whenever equipped creature becomes tapped, it deals 1 damage to each opponent." }

def watchHeroesDamagePlusTwo : Effect :=
  { events := #[.heroesDealDamageToPlayer]
    resolution := .putCounters (.ofKind .plusOnePlusOne 2) .source
    phrase := "Whenever one or more Heroes you control deal damage to a player, put two +1/+1 counters on The Thing." }

def watchMerfolkAttackDraw : Effect :=
  { events := #[.merfolkAttackPlayer], resolution := .draw (.fixed 1)
    phrase := "Whenever one or more Merfolk you control attack a player, draw a card." }

def watchTokensEnterMayDraw : Effect :=
  { events := #[.tokenYouControlEnters]
    resolution := .may (.draw (.fixed 1)) (.sequence []) .ifYouDo
    phrase := "Whenever one or more tokens you control enter, you may draw a card." }

def watchHawkeyeModes : Effect :=
  { events := #[.sourceBecomesTapped], allowsZeroTargets := true
    resolution := .may (.pay (.mana #[.generic 1])) (.queueReflexive (.chooseModes TriggeredAbility.TriggerResolution.trickArrowModes .alreadyChosen)) .ifYouDo
    phrase := "Trick Arrows — Whenever Hawkeye becomes tapped, you may pay {1} up to three times. When you do, choose up to that many — • Net — Target creature can't block this turn. • Explosive — Hawkeye deals 2 damage to target player. • Boomerang — Discard a card, then draw a card." }

def watchRedHulk : Effect :=
  { events := #[.sourceDealtDamage]
    resolution := .sequence [
      .putCounters (.ofKind .plusOnePlusOne) .source,
      .queueReflexive (.dealDamage .plusOneCounters .target)]
    phrase := "Enrage — Whenever Red Hulk is dealt damage, put a +1/+1 counter on him. When you do, he deals damage equal to the number of +1/+1 counters on him to any other target." }

def watchHulk : Effect :=
  { events := #[.sourceDealtDamage]
    resolution := .sequence [
      .putCounters (.ofKind .plusOnePlusOne) .source,
      .«if» (.atLeast (.count (.intersection [.source, .attackingCreatures])) (.fixed 1)) (.untap .source),
      .«if» .enrageGrantsCombat .additionalCombatPhase]
    phrase := "Enrage — Whenever The Incredible Hulk is dealt damage, put a +1/+1 counter on him. If he's attacking, untap him and there is an additional combat phase after this phase." }

def youAttackingPay2LifeToughness : Effect :=
  { events := #[.youAttack]
    resolution := .may (.loseLife (.fixed 2))
      (.grant .assignCombatDamageEqualToughness .creaturesYouControl) .ifYouDo
    phrase := "Whenever you attack, you may pay 2 life. If you do, until end of turn, creatures you control with toughness greater than their power assign combat damage equal to their toughness rather than their power." }

def youAttackingExileTopHeroPump : Effect :=
  { events := #[.youAttack]
    resolution := .may (.exile .top .playThisTurn .ifHero) (.sequence [])
    phrase := "Whenever you attack, you may exile the top card of your library. If that card is a Hero card, Daredevil gets +2/+1 until end of turn. You may play that card this turn." }

def youAttackingLookSixCast : Effect :=
  { events := #[.youAttack]
    resolution := .revealLibrary (.top 6)
      (.mayCast .looked .greatestAttackingPower .withoutPaying)
    phrase := s!"Whenever you attack, look at the top six cards of your library. You may cast a spell from among them with mana value less than or equal to the greatest power among attacking creatures you control without paying its mana cost. {restOnBottomRandomPhrase}." }

def castingVillainToken : Effect :=
  { events := #[.youCastVillain]
    resolution := .createTokens .villain21menace (.fixed 1) false
    phrase := "Whenever you cast a Villain spell, create a 2/1 black Villain creature token with menace." }

def castingMerfolkFromBlue : Effect :=
  { events := #[.youCastNoncreature]
    resolution := .createTokens .merfolk .blueManaSymbols false
    phrase := "Whenever you cast a noncreature spell with one or more blue mana symbols in its mana cost, create that many 1/1 blue Merfolk creature tokens." }

def castingMayPayHasteUnblockable : Effect :=
  { events := #[.youCastNoncreature]
    resolution := .may (.pay (.mana #[.generic 1])) (.queueReflexive (.cant (.beBlockedExceptByHaste .target))) .ifYouDo
    phrase := "Whenever you cast a noncreature spell, you may pay {1}. When you do, target creature with haste can't be blocked this turn except by creatures with haste." }

def castingPlusOneEachOther : Effect :=
  { events := #[.youCastNoncreature]
    resolution := .putCounters (.ofKind .plusOnePlusOne) .eachOther
    phrase := "Whenever you cast a noncreature spell, put a +1/+1 counter on each other creature you control." }

def castingExileFlicker : Effect :=
  { events := #[.youCastNoncreature]
    targeting := .of (.filtered {
      noun := "another target nonland, nontoken permanent"
      nonland := true, nontoken := true, another := true })
    resolution := .exile .target .nextEndStep
    phrase := "Whenever you cast a noncreature spell, exile another target nonland, nontoken permanent. Return that card to the battlefield under its owner's control at the beginning of the next end step." }

def castingVisionModes : Effect :=
  { events := #[.youCastNoncreature]
    resolution := .chooseModes TriggeredAbility.TriggerResolution.visionModes .vision
    phrase := "Whenever you cast a noncreature spell, choose one that hasn't been chosen this turn — • Solar Beam — The Vision gains double strike until end of turn. • Density Control — The Vision gains indestructible until end of turn. • Technopathy — Draw a card." }

def castingDamageEqualMv : Effect :=
  { events := #[.youCastNoncreature], targeting := .of .playerOrCreature
    resolution := .dealDamage .spellManaValue .target
    phrase := "Whenever you cast a noncreature spell, Thor deals damage equal to that spell's mana value to any target." }

def castingDrawPowerEqualHand : Effect :=
  { events := #[.youCastTargetingCreatureYouControl]
    resolution := .sequence [.draw (.fixed 1), .grant .basePowerEqualHand .source]
    phrase := "Whenever you cast a spell that targets a creature you control, draw a card. Until end of turn, Ms. Marvel gains \"Ms. Marvel's base power is equal to the number of cards in your hand.\"" }

def castingPlusOneThis : Effect :=
  { events := #[.youCastTargetingCreatureYouControl]
    resolution := .putCounters (.ofKind .plusOnePlusOne) .source
    phrase := "Whenever you cast a spell that targets a creature you control, put a +1/+1 counter on Mockingbird." }

def castingPlusOneScry : Effect :=
  { events := #[.youCastTargetingCreatureYouControl]
    resolution := .sequence [.putCounters (.ofKind .plusOnePlusOne) .source, .scry (.fixed 1)]
    phrase := "Whenever you cast a spell that targets a creature you control, put a +1/+1 counter on Colleen Wing. Scry 1." }

def castingIronFistTap : Effect :=
  { events := #[.youCastTargetingCreatureYouControl]
    resolution := .grant .ironFistTap .source
    phrase := "Whenever you cast a spell that targets a creature you control, Iron Fist gains \"{T}: Iron Fist deals damage equal to his power to any other target\" until end of turn." }

def castingTargetsGainFlying : Effect :=
  { events := #[.youCastTargetingCreature]
    resolution := .grant (.keywords Keyword.flying) .spellTargets
    phrase := "Whenever you cast a spell that targets one or more creatures, those creatures gain flying until end of turn." }

def castingCopyIfArtifactOrLand : Effect :=
  { events := #[.youCastInstantSorceryTargetingArtifactOrLand]
    resolution := .sequence [
      .putCounters (.ofKind .plusOnePlusOne 2) .source, .becomeCopy .causingSpell]
    phrase := "Whenever you cast an instant or sorcery spell that targets an artifact or land, copy that spell. You may choose new targets for the copy. Put two +1/+1 counters on Fin Fang Foom." }

def castingTapCreatureOrLand : Effect :=
  { events := #[.youCastNoncreature]
    targeting := .of (.filtered {
      noun := "target creature or land",
      types := #[.creature, .land] })
    resolution := .tap .target
    phrase := "Seismic Takedown — Whenever you cast a noncreature spell, tap target creature or land." }

def resourceDiscardExilePlay : Effect :=
  { events := #[.youDiscard]
    resolution := .may (.exile .discarded .playUntilNextTurn) (.sequence []) .ifYouDo
    phrase := "Whenever you discard a card, you may exile that card from your graveyard. If you do, until the end of your next turn, you may play that card." }

def resourceDrawIfAnotherHeroDamage : Effect :=
  { events := #[.youDraw], targeting := .of .opponent
    resolution := .«if» (.atLeast (.count (.othersOfSubtype "Hero")) (.fixed 1)) (.dealDamage (.fixed 1) (.player (.target .opponent)))
    phrase := "Whenever you draw a card, if you control another Hero, Human Torch deals 1 damage to target opponent." }

def resourceSecondDrawBecome66 : Effect :=
  { events := #[.youDrawSecondCard]
    resolution := .sequence [
      .setBasePT (.fixed 6) (.fixed 6) .source, .grant (.keywords Keyword.trample) .source]
    phrase := "Whenever you draw your second card each turn, until end of turn, Moon Girl and Devil Dinosaur's base power and toughness become 6/6 and they gain trample." }

def resourceSecondDrawPlusOneTarget : Effect :=
  { events := #[.youDrawSecondCard], targeting := .of .creature
    resolution := .putCounters (.ofKind .plusOnePlusOne) .permanent
    phrase := "Whenever you draw your second card each turn, put a +1/+1 counter on target creature." }

def resourceSecondDrawDrain : Effect :=
  { events := #[.youDrawSecondCard]
    resolution := .sequence [.loseLife (.fixed 1) .eachOpponent, .gainLife (.fixed 1)]
    phrase := "Whenever you draw your second card each turn, each opponent loses 1 life and you gain 1 life." }

def resourceGainLifePlusOnes : Effect :=
  { events := #[.youGainLife], targeting := .of .creatureYouControl
    allowsZeroTargets := true
    resolution := .putCounters (.ofKind .plusOnePlusOne) .eachUpToLastKnown
    phrase := "Whenever you gain life, choose up to that many target creatures you control. Put a +1/+1 counter on each of them." }

def resourcePlusOneCreateInsectOnce : Effect :=
  { events := #[.youPutPlusOne], onceEachTurn := true
    resolution := .createTokens .insect11green (.fixed 1) false
    phrase := "Whenever you put a +1/+1 counter on a creature, create a 1/1 green Insect creature token. This ability triggers only once each turn." }

def resourcePlusOneOnThisOnce : Effect :=
  { events := #[.youPutPlusOne], onceEachTurn := true
    resolution := .putCounters (.ofKind .plusOnePlusOne) .source
    phrase := "Whenever you put a +1/+1 counter on another creature, put a +1/+1 counter on this creature. This ability triggers only once each turn." }

def resourcePlusOneOnHeroesCreateWall : Effect :=
  { events := #[.youPutPlusOne]
    resolution := .may (.createTokens .wall04defender (.fixed 1) false) (.sequence []) .ifYouDo
    phrase := "Whenever you put one or more +1/+1 counters on one or more other Heroes you control, you may create a 0/4 colorless Wall creature token with defender." }

/-!
Triggers whose effect is a list of independent steps. `Resolution.sequence`
already resolves them, so they are not `SharedTrigger` constructors.
`TriggeredAbility.toNotation` prints the clause from the sequence shape.
-/

/-- Draw a card and lose 1 life. -/
def seqDrawAndLoseLife : Effect :=
  { resolution := .sequence [.draw 1, .loseLife 1] }

/-- Draw `n` cards, then discard a card. -/
def seqDrawThenDiscard (n : Nat) : Effect :=
  { resolution := .sequence [.draw n, .discard (.cards 1)] }

/-- The source gets +P/+0 and creatures you control gain trample. -/
def seqSourceGetsAndTeamTrample (power : Int) : Effect :=
  { resolution := .sequence [.onSource (.pump power 0), .grant (.keywords Keyword.trample) .creaturesYouControl] }

/-- Put a +1/+1 counter on a target of this kind. It gains lifelink until end of turn. -/
def seqPlusOneAndLifelink (kind : EffectTargetKind) : Effect :=
  { targeting := .of kind
    resolution := .sequence
      [.onPermanent (.plusOne 1), .onPermanent (.grantKeywords Keyword.lifelink)] }

/-- The source gets +1/+0 and can't be blocked this turn. -/
def seqPumpAndUnblockable : Effect :=
  { resolution := .sequence [.onSource (.pump 1 0), .onSource .cantBeBlocked] }

/-- Put `n` +1/+1 counters on a creature you control. It gains vigilance until end of turn. -/
def seqPlusOneVigilance (n : Nat) : Effect :=
  { targeting := .of .creatureYouControl
    resolution := .sequence
      [.onPermanent (.plusOne n), .onPermanent (.grantKeywords Keyword.vigilance)] }

/-- Draw a card and put a +1/+1 counter on the source. -/
def seqDrawPlusOneSource : Effect :=
  { resolution := .sequence [.draw 1, .onSource (.plusOne 1)] }

/-- Creatures you control get +P/+0 and gain first strike until end of turn. -/
def seqCreaturesPumpAndFirstStrike (power : Int) : Effect :=
  { resolution := .sequence
      [.pump (.fixed power) (.fixed 0) .creaturesYouControl, .grant (.keywords Keyword.firstStrike) .creaturesYouControl] }

/-- Put a +1/+1 counter on the source and draw a card. -/
def seqPlusOneOnSourceAndDraw : Effect :=
  { resolution := .sequence [.onSource (.plusOne 1), .draw 1] }

/-- The source gets +1/+1 until end of turn and deals `n` damage to each opponent. -/
def seqPumpAndDamageOpponents (n : Nat) : Effect :=
  { resolution := .sequence [.onSource (.pump 1 1), .dealDamage n (.player .eachOpponent)] }

/-- Untap another creature you control. If it has `subtype`, put a +1/+1 counter on it. -/
def seqUntapPlusOneIfSubtype (subtype : String) : Effect :=
  { targeting := .of .anotherCreatureYouControl
    resolution := .sequence
      [.onPermanent .untap,
       .«if» (.subtype subtype) (.onPermanent (.plusOne 1))] }

/-- You lose 1 life and create a Treasure token. -/
def seqLoseLifeCreateTreasure : Effect :=
  { resolution := .sequence [.loseLife 1, .createTokens .treasure 1] }

/-- Exile up to one card from an opponent's graveyard. Each opponent loses `life`. -/
def seqExileOppGyCardOppsLoseLife (life : Nat) : Effect :=
  { targeting := .of .oppGraveyardCard
    allowsZeroTargets := true
    resolution := .sequence
      [.exile .graveyardCard .forLater, .loseLife life .eachOpponent] }

instance : Coe SharedTrigger Effect where
  coe := ofTrigger

end Effect

end Mtg.Engine
