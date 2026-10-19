import Mtg.Engine.Card.PermanentAction
import Mtg.Engine.Card.TriggerEvent
import Mtg.Engine.Card.Chapter

/-!
# Shared triggers (CR 603)

Reusable trigger payloads (`SharedTriggerWhen` x `SharedTrigger`) used by
triggered abilities and Saga chapters, including the leftover printed
wordings grouped per trigger family.
-/

namespace Mtg.Engine

/-- Leftover “When ⟨this⟩ enters” wordings that do not already match a more
specific `TriggeredAbility` constructor. One `onEnter` constructor keeps the
C runtime tag under the limit. -/
inductive EnterLeftover where
  /-- Destroy the targeted permanent. -/
  | destroy (kind : EffectTargetKind)
  /-- Deal `n` damage to up to one target creature. -/
  | dealDamageUpToOne (n : Nat)
  /-- This fights up to one other target creature. Resolves as `.fight`. -/
  | fightUpToOne
  /-- Return up to one nonland nontoken to its owner's hand. -/
  | returnNonlandNontoken
  /-- Create Zabu. -/
  | createZabu
  /-- Target opponent creates The Void. -/
  | oppCreatesTheVoid
  /-- Create Sturdy Shield and attach it to this. -/
  | createSturdyShieldAttach
  /-- Exile an Equipment, instant, or sorcery from your GY; play until next turn. -/
  | exileGyPlayUntilNextTurn
  /-- Return a GY permanent card put there this turn to your hand. -/
  | returnGyPermanentThisTurn
  /-- Tap an opposing creature; it can't untap while you control this. -/
  | tapOppCantUntapWhileControl
  /-- You may sacrifice another creature. When you do, destroy an opposing nonland. -/
  | maySacAnotherThenDestroyOppNonland
  /-- You may sac an artifact or discard a nonland. When you do, 2 damage.
  Resolves as
  `.may (.pay (.or [.sacrifice (.fixed 1) .artifact, .discard (.fixed 1) .nonland])) (.queueReflexive (.dealDamage (.fixed 2) .target)) .ifYouDo`. -/
  | maySacOrDiscardNonlandThenDamage
  /-- Reveal the opponent's hand; exile a card or creature until this leaves. -/
  | revealHandExileUntilLeaves
  /-- +1/+1 on up to two creatures, or return an artifact/enchantment from GY.
  Resolves as `.or [.putCounters (.ofKind .plusOnePlusOne) .permanent, .returnToHand .graveyardCard]`. -/
  | plusOnesOrReturnArtEnch
  /-- Choose up to X modes. Resolves as
  `.chooseModes TriggerResolution.upToXModes .alreadyChosen`. -/
  | chooseUpToXModes
  /-- You may tap this. When you do, grant indestructible. -/
  | mayTapThenGrantIndestructible
  /-- Tap up to one creature; it loses abilities while this remains. -/
  | tapLoseAbilitiesWhileSource
  /-- Target player reveals; you choose a card to discard. -/
  | revealDiscardFromHand
  /-- Create Redwing. -/
  | createRedwing
deriving Repr, Inhabited, BEq

/-- Leftover step, upkeep, end-step, and first-main triggers. -/
inductive StepLeftover where
  /-- At the beginning of the upkeep of enchanted creature's controller, that player draws a car… -/
  | enchantedControllerDraws
  /-- At the beginning of your end step, if you have fewer than ten cards in hand, draw cards eq… -/
  | drawToTen
  /-- At the beginning of your first main phase, until your next turn, Absorbing Man becomes a c… -/
  | copyAbsorbingMan
  /-- At the beginning of your upkeep, choose one — • Put a +1/+1 counter on Mister Hyde. • Remo… -/
  | hydeChoose
  /-- Photographic Reflexes — At the beginning of your first main phase, until your next turn, T… -/
  | copyTaskmaster
  /-- ∞ — At the beginning of your end step, exile up to one other target nonland permanent you … -/
  | harnessedFlicker
deriving Repr, Inhabited, BEq

/-- Leftover dies triggers that do not already match a more specific constructor.
Each one resolves through `put`, `returnToHand`, or `sacrifice`. -/
inductive DeathLeftover where
  /-- When Hellcat dies, return her under her owner's control with a +1/+1
  counter. She loses all abilities and gains haste. Resolves as
  `.put .source .underOwner (.entering [.loseAllAbilities, .keywords Keyword.haste, .counter .plusOnePlusOne (asEnters := true)])`. -/
  | hellcatReturn
  /-- Whenever a Villain you control dies, return it under its owner's control
  with a finality counter. It is a Hero in addition to its other types.
  Resolves as
  `.put (.cause (some "Villain")) .underOwner (.entering [.additionalSubtype "Hero", .counter .finality])`. -/
  | villainReturnAsHero
  /-- Whenever an attacking creature you control dies, return that card to its
  owner's hand. Resolves as `.returnToHand .cause`. -/
  | attackingReturnHand
  /-- Whenever another creature you control with deathtouch dies, each opponent
  sacrifices a nontoken creature of their choice. Resolves as
  `.sacrifice .chosenNontokenCreature`. -/
  | deathtouchOppSac
deriving Repr, Inhabited, BEq

/-- Leftover “whenever this attacks” (or attacks-alone) triggers.
Each one resolves through `may`, `if`, `exile`, `loseLife`, `gainLife`,
`pump`, or `grant`. -/
inductive ThisAttackLeftover where
  /-- Whenever Ant-Man attacks, you may pay {1}. When you do, put a +1/+1
  counter on target creature. Resolves as
  `.may (.pay (.mana #[.generic 1])) (.queueReflexive (.putCounters (.ofKind .plusOnePlusOne) .permanent)) .ifYouDo`. -/
  | mayPayPlusOne
  /-- Whenever Grim Reaper attacks, you may pay {3}{B}. When you do, return
  target creature card from your graveyard tapped and attacking with a
  finality counter. Resolves as
  `.may (.pay (.mana #[.generic 3, .colored .black])) (.queueReflexive (.put .creatureCard .tapped (.entering [.attacking, .counter .finality]))) .ifYouDo`. -/
  | payReturnAttacking
  /-- Whenever Iron Man attacks, if an artifact entered under your control
  this turn, draw a card. Resolves as
  `.«if» .artifactEnteredThisTurn (.draw (.fixed 1))`. -/
  | ifArtifactEnteredDraw
  /-- Whenever The Mighty Thor attacks, exile up to one target nontoken
  artifact or creature, then return it tapped. Resolves as
  `.exile .target .returnTapped`. -/
  | blinkNontoken
  /-- Whenever Whiplash attacks, if he's equipped, each opponent loses X
  life and you gain X life, where X is the number of Equipment attached
  to him. Resolves as
  `.«if» .attachedEquipment (.sequence [.loseLife .attachedEquipment .eachOpponent, .gainLife .attachedEquipment])`. -/
  | equippedDrain
  /-- Cybernetic Senses — Whenever Viv Vision attacks, draw a card if her
  power is 4 or greater. Resolves as
  `.«if» (.atLeast .equalSourcePower (.fixed 4)) (.draw (.fixed 1))`. -/
  | drawIfPower4
  /-- Unbreakable Skin — Whenever Luke Cage attacks alone, he gets +2/+0
  and gains indestructible until end of turn. Resolves as
  `.sequence [.pump (.fixed 2) (.fixed 0) .source, .grant (.keywords Keyword.indestructible) .source]`. -/
  | attacksAlonePlus2Indestructible
deriving Repr, Inhabited, BEq

/-- Leftover “enters or attacks” triggers.
Each one resolves through `createTokens` or `putCounters`. -/
inductive EnterOrAttackLeftover where
  /-- Whenever Super-Adaptoid enters or attacks, choose another target creature.
  If that creature has a keyword Super-Adaptoid lacks, put that counter on
  Super-Adaptoid. Resolves as
  `.putCounters .missingKeywordsFromTarget .source`. -/
  | copyKeywords
  /-- Do You Like Squirrels? — Whenever The Unbeatable Squirrel Girl enters or
  attacks, create a 1/1 green Squirrel creature token. Resolves as
  `.createTokens .squirrel11green (.fixed 1) false`. -/
  | createSquirrel
deriving Repr, Inhabited, BEq

/-- Leftover triggers that watch another event (another permanent, combat, tap, damage).
Each one resolves through `draw`, `putCounters`, `pump`, `grant`, `tap`,
`dealDamage`, `loseLife`, `gainLife`, `untap`, `scry`, `if`, `may`, `connive`,
`attach`, `chooseModes`, `queueReflexive`, or a step that does not carry
`WatchLeftover`. -/
inductive WatchLeftover where
  /-- Whenever Black Widow deals combat damage to a player, that player exiles cards from the to… -/
  | combatDamageExileUntilNonland
  /-- Whenever a creature you control attacks alone, target opponent loses 1 life and you gain 1… -/
  | attacksAloneDrain
  /-- Whenever a creature you control attacks alone, it gains first strike and menace until end … -/
  | attacksAloneFirstStrikeMenace
  /-- Whenever a creature you control becomes tapped during your turn, if it's the first time th… -/
  | firstTapUntap
  /-- Whenever a creature you control is dealt damage, you may have The Sensational She-Hulk dea… -/
  | sheHulkRedirectOnce
  /-- Whenever a player casts a spell that targets Speedball, he gets +2/+2 until end of turn. Y… -/
  | speedballTargeted
  /-- Whenever a player draws their second card each turn, you draw a card. -/
  | anyPlayerSecondDraw
  /-- Whenever a player or permanent becomes the target of an ability you control, draw a card. … -/
  | youTargetDrawOnce
  /-- Whenever another Villain and/or artifact you control enters, this creature deals 1 damage … -/
  | villainOrArtifactDamage
  /-- Whenever another Villain you control enters, you may have it connive. Do this only once ea… -/
  | villainConniveOnce
  /-- Whenever another Villain you control enters, put a +1/+1 counter on Crossbones. He deals 2… -/
  | villainPlusOneDamageOnce
  /-- Whenever another Villain you control enters, attach up to one target Equipment you control… -/
  | villainAttachEquipment
  /-- Whenever another Villain you control enters, Yellowjacket gets +1/+0 and gains lifelink un… -/
  | villainPlusOneLifelink
  /-- Whenever another creature you control enters, if it has greater power or toughness than Hu… -/
  | hulklingCompare
  /-- Whenever another nonland permanent you control is returned to its owner's hand, put a +1/+… -/
  | justiceBounce
  /-- Whenever another nontoken Hero you control enters, choose one — • Create a 1/1 white Soldi… -/
  | nontokenHeroModal
  /-- Whenever another nontoken artifact you control enters, you may pay {2}. If you do, create … -/
  | ultronCopy
  /-- Whenever enchanted creature attacks or blocks, attach any number of target Equipment you c… -/
  | enchantedAttachEquipment
  /-- Whenever equipped creature attacks alone, untap it and scry 1. -/
  | equippedAttacksAloneUntapScry
  /-- Whenever equipped creature attacks, tap target creature defending player controls. -/
  | equippedAttacksTap
  /-- Whenever equipped creature becomes tapped, it deals 1 damage to each opponent. -/
  | equippedTappedDamage
  /-- Whenever one or more Heroes you control deal damage to a player, put two +1/+1 counters on… -/
  | heroesDamagePlusTwo
  /-- Whenever one or more Merfolk you control attack a player, draw a card. -/
  | merfolkAttackDraw
  /-- Whenever one or more tokens you control enter, you may draw a card. -/
  | tokensEnterMayDraw
  /-- Trick Arrows — Whenever Hawkeye becomes tapped, you may pay {1} up to three times. When yo… -/
  | hawkeyeModes
  /-- Enrage — Whenever Red Hulk is dealt damage, put a +1/+1 counter on him. When you do, he de… -/
  | redHulk
  /-- Enrage — Whenever The Incredible Hulk is dealt damage, put a +1/+1 counter on him. If he's… -/
  | hulk
deriving Repr, Inhabited, BEq

/-- Leftover “whenever you attack” triggers. -/
inductive YouAttackLeftover where
  /-- Whenever you attack, you may pay 2 life. If you do, until end of turn, creatures you contr… -/
  | pay2LifeToughness
  /-- Whenever you attack, you may exile the top card of your library. If that card is a Hero ca… -/
  | exileTopHeroPump
  /-- Whenever you attack, look at the top six cards of your library. You may cast a spell from … -/
  | lookSixCast
deriving Repr, Inhabited, BEq

/-- Leftover “whenever you cast …” triggers. -/
inductive CastLeftover where
  /-- Whenever you cast a Villain spell, create a 2/1 black Villain creature token with menace. -/
  | villainToken
  /-- Whenever you cast a noncreature spell with one or more blue mana symbols in its mana cost,… -/
  | merfolkFromBlue
  /-- Whenever you cast a noncreature spell, you may pay {1}. When you do, target creature with … -/
  | mayPayHasteUnblockable
  /-- Whenever you cast a noncreature spell, put a +1/+1 counter on each other creature you cont… -/
  | plusOneEachOther
  /-- Whenever you cast a noncreature spell, exile another target nonland, nontoken permanent. R… -/
  | exileFlicker
  /-- Whenever you cast a noncreature spell, choose one that hasn't been chosen this turn — • So… -/
  | visionModes
  /-- Whenever you cast a noncreature spell, Thor deals damage equal to that spell's mana value … -/
  | damageEqualMv
  /-- Whenever you cast a spell that targets a creature you control, draw a card. Until end of t… -/
  | drawPowerEqualHand
  /-- Whenever you cast a spell that targets a creature you control, put a +1/+1 counter on Mock… -/
  | plusOneThis
  /-- Whenever you cast a spell that targets a creature you control, put a +1/+1 counter on Coll… -/
  | plusOneScry
  /-- Whenever you cast a spell that targets a creature you control, Iron Fist gains "{T}: Iron … -/
  | ironFistTap
  /-- Whenever you cast a spell that targets one or more creatures, those creatures gain flying … -/
  | targetsGainFlying
  /-- Whenever you cast an instant or sorcery spell that targets an artifact or land, copy that … -/
  | copyIfArtifactOrLand
  /-- Seismic Takedown — Whenever you cast a noncreature spell, tap target creature or land. -/
  | tapCreatureOrLand
deriving Repr, Inhabited, BEq

/-- Printed draw, discard, life, and +1/+1-counter triggers.
Each one resolves as the constructors named on `SharedTrigger.resource`. -/
inductive ResourceLeftover where
  /-- Whenever you discard a card, you may exile that card from your graveyard. If you do, until… -/
  | discardExilePlay
  /-- Whenever you draw a card, if you control another Hero, Human Torch deals 1 damage to targe… -/
  | drawIfAnotherHeroDamage
  /-- Whenever you draw your second card each turn, until end of turn, Moon Girl and Devil Dinos… -/
  | secondDrawBecome66
  /-- Whenever you draw your second card each turn, put a +1/+1 counter on target creature. -/
  | secondDrawPlusOneTarget
  /-- Whenever you draw your second card each turn, each opponent loses 1 life and you gain 1 li… -/
  | secondDrawDrain
  /-- Whenever you gain life, choose up to that many target creatures you control. Put a +1/+1 c… -/
  | gainLifePlusOnes
  /-- Whenever you put a +1/+1 counter on a creature, create a 1/1 green Insect creature token. … -/
  | plusOneCreateInsectOnce
  /-- Whenever you put a +1/+1 counter on another creature, put a +1/+1 counter on this creature… -/
  | plusOneOnThisOnce
  /-- Whenever you put one or more +1/+1 counters on one or more other Heroes you control, you m… -/
  | plusOneOnHeroesCreateWall
deriving Repr, Inhabited, BEq

/-- How many counters `amass` puts on the Army. `.fixed` uses `n`. -/
inductive AmassAmount where
  /-- The `n` argument. -/
  | fixed
  /-- This creature's power, as it last existed. -/
  | sourcePower
  /-- Excess damage an earlier step recorded. Zero excess amasses nothing. -/
  | notedExcess
  /-- The power an earlier step recorded when it destroyed a creature.
  No destruction amasses nothing. -/
  | notedPower
deriving Repr, Inhabited, BEq, DecidableEq

/-- Who `SharedTrigger.connive` makes connive. -/
inductive ConniveSubject where
  /-- The trigger's source. -/
  | source
  /-- The announced target of this kind. -/
  | target (kind : EffectTargetKind)
  /-- The Villain that caused this trigger. You may have it connive.
  Already chosen this turn does nothing. A Villain that will not connive
  is reported. -/
  | enteringVillain
deriving Repr, Inhabited, BEq

/-- Who discards for `SharedTrigger.opponentDiscards`. -/
inductive OpponentDiscard where
  /-- Each opponent. -/
  | each
  /-- The announced opponent. -/
  | target
deriving Repr, Inhabited, BEq, DecidableEq

/-- Shared triggered-ability effects that draw, scry, surveil, mill, search,
reveal from a library, connive, or cascade (CR 121 / CR 701.13 / CR 701.18 /
CR 701.20 / CR 701.25 / CR 701.48). -/
inductive LibraryTrigger where
  /-- Scry `n`. -/
  | scry (n : Nat)
  /-- Draw `n` cards. -/
  | draw (n : Nat)
  /-- Connive. The source is `.connive`. A target of `kind` is
  `.connive (.target kind)`. That target resolves as `.connive .target`. -/
  | connive (who : ConniveSubject := .source)
  /-- Target player mills `n` cards. Resolves as `.mill (.fixed n) (.target .player)`. -/
  | millPlayer (n : Nat)
  /-- Search your library for a Forest card and put it onto the battlefield.
  Resolves as `.searchLibrary (.put .forest)`. -/
  | searchLibrary
  /-- Search your library for a basic land card and put it into your hand.
  Resolves as `.searchLibrary (.returnToHand .basicLand)`. -/
  | searchBasicLandToHand
  /-- You may discard your hand. If you do, draw `n`. -/
  | mayDiscardHandDraw (n : Nat)
  /-- Draw X cards, where X is the mana spent to cast the triggering spell,
  then discard `n`. Resolves as
  `.sequence [.draw .equalToManaSpent, .«if» .manaSpent (.discard (.cards n))]`.
  Two cards is `.drawXDiscard 2`. Making that optional is
  `.may (.drawXDiscard 2)`. -/
  | drawXDiscard (n : Nat)
  /-- You may pay `{n}`. If you do, draw a card.
  Also putting a +1/+1 counter on this creature is
  `.mayPayGenericDraw n (plusOneOnSource := true)`. -/
  | mayPayGenericDraw (n : Nat) (plusOneOnSource : Bool := false)
  /-- Draw a card, then put a card from your hand on the bottom if you don't
  control a legendary creature.
  Resolves as `.sequence [.draw (.fixed 1), .«if» (.not (.atLeast (.count .legendaryCreaturesYouControl) (.fixed 1))) (.putOnLibrary .bottom .cardFromHand)]`. -/
  | drawThenBottomIfNoLegendary
  /-- Tap any number of untapped Humans you control. Draw a card for each
  Human tapped this way.
  Resolves as `.sequence [.may (.tap .humans) (.sequence []), .draw .forEachTappedHuman]`. -/
  | tapHumansDraw
  /-- Look at the top `n` cards; you may reveal one of these types. -/
  | lookAtTopRevealTypes (n : Nat) (types : Array String)
  /-- Mill `n`, then put matching subtype cards into hand. Resolves as
  `.sequence [.mill (.fixed n) (note := .milledCards), .returnToHand (.milledSubtype subtype)]`. -/
  | millThenSubtypeToHand (n : Nat) (subtype : String)
  /-- Reveal until a creature and put it in if cheap enough. -/
  | revealUntilCreature
  /-- Loot; a discarded land enters tapped. Resolves as
  `.sequence [.draw (.fixed 1), .discard (.cards 1), .put .discardedLand (how := .tapped)]`. -/
  | lootLandEntersTapped
  /-- That player mills that many cards. Resolves as
  `.mill .thatManyLost .thatPlayer`. -/
  | millThatManyLost
  /-- Draw a card for each fat graveyard. -/
  | drawPerFatGraveyard
  /-- Mill, then maybe copy a milled spell. Resolves as
  `.sequence [.mill (.fixed 2) .eachOpponent (note := .opponentsMilled), .«if» .opponentsMilled (.queueReflexive (.mayCast .milledSpell .causingSpell .withoutPaying))]`. -/
  | millThenCopy
  /-- Cascade. -/
  | cascade
  /-- Discard hand, draw that many; damage if enduring story. Resolves as
  `.sequence [.may (.discard .hand) (.sequence []), .draw .discardedHand, .«if» .enduringStoryNoted (.dealDamage .discardedHand (.player .eachOpponent))]`. -/
  | discardHandDrawDamageIfStory
  /-- Reveal the top `n` and put a random creature in. -/
  | revealTopPutRandomCreature (n : Nat)
  /-- Gríma impulse. Resolves as
  `.sequence [.revealLibrary .untilInstantOrSorcery (.exile .top .forLater .impulse) .damagedPlayer, .mayCast .impulse .unlimited .withoutPaying]`. -/
  | grimaImpulse
  /-- Palantír end-step. Resolves as
  `.sequence [.putCounters (.ofKind .influence) .source, .scry (.fixed 2), .may (.draw (.fixed 1) (who := .opponentHasYou)) (.sequence [])]`. -/
  | palantir
  /-- Reveal until a Saga. -/
  | revealSaga
  /-- Draw if you attacked with this subtype or one entered under your control.
  Resolves as
  `.«if» (.or [.attackedWithSubtype subtype, .subtypeEntered subtype]) (.draw (.fixed 1))`. -/
  | drawIfAttackedOrEnteredSubtype (subtype : String)
  /-- Surveil `n` (CR 701.25). -/
  | surveil (n : Nat)
  /-- If two or more loyalty counters were removed to activate the ability, draw a card. -/
  | drawIfRemovedTwoLoyalty
  /-- Draw two cards; if your library is then empty, you win; the owner
  shuffles the source into their library (Fblthp, Impossibly Lost). Resolves as
  `.sequence [.draw (.fixed 2), .«if» (.not (.atLeast .libraryCards (.fixed 1))) .winTheGame, .«if» (.atLeast .libraryCards (.fixed 1)) .shuffleSource]`. -/
  | drawTwoWinIfEmptyShuffleSource
  /-- If you gained life this turn, surveil 1; a card with mana value at most
  the life gained put into the graveyard this way goes to your hand. Resolves as
  `.sequence [.armSurveilReturnLifeGained, .surveil (.fixed 1)]`. -/
  | surveilReturnIfGainedLife
  /-- Draw, then you may put a land from hand tapped.
  Resolves as `.sequence [.draw (.fixed 1), .may (.put .landFromHand (how := .tapped)) (.sequence [])]`. -/
  | drawMayPutLandTapped
  /-- Draw; if you control another Hero, gain 2 life. -/
  | drawGainLifeIfAnotherHero
  /-- You may sac an artifact or discard; if you do, draw.
  Resolves as `.may (.pay (.or [.sacrifice (.fixed 1) .artifact, .discard (.fixed 1) .card])) (.draw (.fixed 1)) .ifYouDo`. -/
  | maySacArtifactOrDiscardDraw
deriving Repr, Inhabited, BEq

/-- Shared triggered-ability effects that create tokens, amass, recruit,
investigate, put or remove counters, tempt with the Ring, or advance Plan
counters (CR 111 / CR 122 / CR 701.36 / CR 701.47). -/
inductive TokenCounterTrigger where
  /-- Create `n` tokens of this kind. `tapped` is Treasure-style “create a tapped …”. -/
  | createTokens (kind : TokenKind) (n : Nat) (tapped : Bool := false)
  /-- Amass `subtype` `n`. Goblins `n` is `.amass n`.
  Orcs `n` is `.amass n "Orc"`.
  Amass equal to this creature's power is `.amass 0 (amount := .sourcePower)`.
  Amass, then attach this Equipment to the Army, is
  `.amass n (attachSource := true)`. -/
  | amass (n : Nat) (subtype : String := "Goblin")
      (amount : AmassAmount := .fixed) (attachSource : Bool := false)
  /-- Recruit. “recruit” is `.recruit`. “you recruit” is `.recruit .you`. -/
  | recruit (who : RecruitSubject := .recruit)
  /-- Investigate (create a Clue). -/
  | investigate
  /-- Put a +1/+1 counter on permanents you control.
  Each creature is `.plusOneEachYouControl`.
  Each permanent of a subtype is `.plusOneEachYouControl (.subtype s)`.
  One counter, or two with the city's blessing, is
  `.plusOneEachYouControl .citysBlessing`. -/
  | plusOneEachYouControl (which : YouControlPlusOne := .eachCreature)
  /-- Put a hone counter on each Equipment you control. -/
  | honeEachEquipment
  /-- +1/+1 on each other creature you control, then gain 1 life for each.
  Resolves as `.sequence [.putCounters (.ofKind .plusOnePlusOne) .eachOther, .gainLife .perOtherCreature]`. -/
  | plusOneEachOtherGainLife
  /-- Create one token, then attach the source to it.
  Resolves as `.sequence [.createTokens kind (.fixed 1) false, .attach .source .createdToken]`. -/
  | createThenAttach (kind : TokenKind)
  /-- Create an Axe Equipment token.
  Attaching it to a creature you control is `.createAxe (attach := true)`. -/
  | createAxe (attach : Bool := false)
  /-- The Ring tempts you. -/
  | ringTempts
  /-- Remove a hope counter from this. If you do, draw a card. Then if it has
  no hope counters, sacrifice it and you gain 4 life.
  Resolves as
  `.sequence [.removeCounters .hope .source, .«if» .removedHope (.draw (.fixed 1)), .«if» (.not .hopeOnSource) (.sequence [.sacrifice .source, .gainLife (.fixed 4)])]`. -/
  | removeHopeDrawSac
  /-- Create tapped Treasures equal to artifacts opponents control. -/
  | createTappedTreasuresEqualOppArtifacts
  /-- +1/+1 on a Wolf or create a Treasure.
  Resolves as `.or [.putCounters (.ofKind .plusOnePlusOne) .permanent, .createTokens .treasure (.fixed 1) false]`. -/
  | wolfPlusOneOrTreasure
  /-- Trample counter, become a Bear, maybe draw. Resolves as
  `.sequence [.putCounters (.ofKind .trample) .permanent, .becomeBear, .«if» ((.atLeast (.count (.youControl (.subtype "Bear"))) (.fixed 3))) (.draw (.fixed 2))]`. -/
  | trampleCounterBecomeBear
  /-- +X/+X counters equal to the last-known mana value. -/
  | plusOneEqualLastKnownMv
  /-- Quest, then maybe find a Dragon. -/
  | mountainQuestDragon
  /-- Treasures per chosen creature type. -/
  | treasuresPerChosenType
  /-- You may sacrifice another creature for +1/+1s equal to its power. -/
  | attackSacPlusOneEqualPower
  /-- You may sacrifice another for a card and a Treasure. -/
  | maySacDrawTreasure
  /-- Create an Alien and grow it from invasion counters. -/
  | createAlienPerInvasion
  /-- First resolve this turn: gain 1 life. Second: draw a card. Third:
  +1/+1 on each creature you control. Later resolves do nothing
  (Belladonna Took). Resolves as
  `.sequence [.noteResolveThisTurn 3, .«if» (.nthResolve 1) (.gainLife (.fixed 1)), .«if» (.nthResolve 2) (.draw (.fixed 1)), .«if» (.nthResolve 3) (.putCounters (.ofKind .plusOnePlusOne) .youControl)]`. -/
  | belladonnaTokenReward
  /-- Create Spirits for the equipped creature. Resolves as
  `.sequence [.createTokens .spirit (.fixed 2) true, .«if» (.atLeast (.count (.intersection [.equipped, .legendaryCreaturesYouControl])) (.fixed 1)) .markRecentTokensAttacking]`. -/
  | createSpiritsForEquipped
  /-- Treasures equal to the damaged player's artifacts. -/
  | createTreasuresEqualDamagedPlayerArtifacts
  /-- Delayed Eagles Bird Soldiers. -/
  | eaglesCreateBirds
  /-- Hone per opposing creatures and attach. -/
  | honePerOppAttach
  /-- Create Treasures equal to last-known noncombat damage. -/
  | treasuresEqualLastKnown
  /-- Scry `n` and put a plan counter. Resolves as
  `.sequence [.putCounters (.ofKind .plan) .source, .scry (.fixed n)]`. -/
  | scryAndPlan (n : Nat)
  /-- Loot and put a plan counter. Resolves as
  `.sequence [.putCounters (.ofKind .plan) .source, .draw (.fixed 1), .discard (.cards 1)]`. -/
  | lootAndPlan
  /-- Create a Villain and a plan counter. -/
  | createVillainAndPlan
  /-- Drain `n` and put a plan counter. Resolves as
  `.sequence [.putCounters (.ofKind .plan) .source, .loseLife (.fixed n) .eachOpponent, .gainLife (.fixed n)]`. -/
  | drainAndPlan (n : Nat)
  /-- Draw, lose life, and put a plan counter. Resolves as
  `.sequence [.putCounters (.ofKind .plan) .source, .draw (.fixed 1), .loseLife (.fixed 1)]`. -/
  | drawLoseLifeAndPlan
  /-- Create a tapped Treasure and put a plan counter. -/
  | treasureTappedAndPlan
  /-- +1/+1 on a target and a plan counter. -/
  | plusOneOnTargetAndPlan
  /-- Fourth-plan: sacrifice, draw, +1 each. -/
  | planFinishDrawPlusOneEach
  /-- Fourth-plan: sacrifice and return instants. -/
  | planFinishReturnInstants
  /-- Seventh-plan: sacrifice and control an opponent. -/
  | planFinishControlOpponent
  /-- Fifth-plan: sacrifice and exile-cast. -/
  | planFinishExileTopCast
  /-- Third-plan: sacrifice and create Robots. -/
  | planFinishCreateRobots (n : Nat)
  /-- Fourth-plan: sacrifice and divide damage. -/
  | planFinishDividedDamage (n : Nat)
  /-- Fourth-plan: sacrifice and grant indestructible. -/
  | planFinishIndestructibleOnTarget
  /-- Empower Jace `n` (Reality Fracture). -/
  | empowerJace (n : Nat)
  /-- Put a loyalty counter on the source (Ajani Resolute). -/
  | loyaltyOnSource
  /-- Target permanent you control gains these keywords until end of turn; a
  +1/+1 counter if it's a creature, a loyalty counter if it's a planeswalker.
  Resolves as
  `.sequence [.grant (.keywords k) .target, .«if» (.atLeast (.count (.target .creature)) (.fixed 1)) (.putCounters (.ofKind .plusOnePlusOne) .permanent), .«if» (.atLeast (.count (.target .planeswalker)) (.fixed 1)) (.putCounters (.ofKind .loyalty) .permanent)]`. -/
  | grantThenCounterByType (k : Keywords)
  /-- Another target creature you control gets +1/+1 until end of turn, or a
  +1/+1 counter instead if you've scried or surveilled this turn. Resolves as
  `.ifElse (.or [.scriedThisTurn, .surveilledThisTurn]) (.putCounters (.ofKind .plusOnePlusOne) .permanent) (.pump (.fixed 1) (.fixed 1) .target)`. -/
  | pumpOrCounterIfScried
  /-- Put the source's last-known counters on up to one target creature you
  control (Graft Surgeon). -/
  | putSourceCountersOnTarget
  /-- Put a charge counter on the source. -/
  | chargeCounterOnSource
  /-- Create a Food or a Treasure.
  Resolves as `.or [.createTokens .food (.fixed 1) false, .createTokens .treasure (.fixed 1) false]`. -/
  | createFoodOrTreasure
  /-- Villain if two creature cards in gy; otherwise mill two. Resolves as
  `.ifElse ((.atLeast (.count .creatureCardsInGraveyard) (.fixed 2))) (.createTokens .villain21menace (.fixed 1) true) (.mill (.fixed 2))`. -/
  | villainIfGyElseMill
  /-- +1/+1, or two if that creature is another Hero. Resolves as
  `.ifElse ((.atLeast (.count (.target (.anotherSubtype "Hero"))) (.fixed 1))) (.putCounters (.ofKind .plusOnePlusOne 2) .permanent) (.putCounters (.ofKind .plusOnePlusOne) .permanent)`. -/
  | plusOneOrTwoIfAnotherHero
deriving Repr, Inhabited, BEq

/-- Shared triggered-ability effects that deal damage, gain or lose life,
modify power/toughness, attach Equipment, fight, or grant extra combat
phases (CR 119 / CR 120 / CR 506 / CR 701.3 / CR 701.12). -/
inductive CombatDamageTrigger where
  /-- Deal `amount` damage divided as you choose among one to `maxTargets` targets. -/
  | dividedDamage (amount maxTargets : Nat)
  /-- You gain `n` life. -/
  | gainLife (n : Nat)
  /-- Deal `n` damage to each opponent (optionally after targeting one). -/
  | damageEachOpponent (n : Nat)
  /-- Attach this Equipment to a target of this kind. -/
  | attachTo (kind : EffectTargetKind)
  /-- The attacking creature that caused this trigger gets +P/+T. -/
  | pumpCause (power toughness : Int)
  /-- Set the source's base P/T. -/
  | becomePT (power toughness : Int)
  /-- Pump a target creature you control +1/+1 per Plains. -/
  | pumpTargetPerPlains
  /-- Pump the source +1/+1 per card looked at while scrying. -/
  | pumpByLookedAt
  /-- Pump the source by the greatest power among creatures you control. -/
  | pumpGreatestPower
  /-- Pump the source +1/+1 for each other creature you control. -/
  | pumpForEachOtherCreature
  /-- Deal `n` damage to each creature blocking the source. -/
  | damageBlockers (n : Nat)
  /-- Gain `n` life, then you may search a basic land to the top.
  Resolves as `.sequence [.gainLife (.fixed n), .searchLibrary (.put .basicLandOnTop)]`. -/
  | gainLifeSearchBasicOnTop (n : Nat)
  /-- Target opponent loses `n` life.
  Resolves as `.loseLife (.fixed n) (.target .opponent)`. -/
  | targetOpponentLosesLife (n : Nat)
  /-- Set another creature's base P/T to this creature's.
  Resolves as `.setBasePT .equalSourcePower .equalSourceToughness`. -/
  | setOtherBasePT
  /-- Deal damage equal to last-known power to a target. -/
  | damageFromLastKnownPower
  /-- Damage each opponent equal to permanents of this subtype you control. -/
  | damageEqualSubtypeToEachOpponent (subtype : String)
  /-- Damage any target equal to Treasures you control. -/
  | damageEqualTreasures
  /-- Deal `n` to any target; destroy it if it has this subtype and was dealt
  damage this way.
  Resolves as `.sequence [.dealDamage (.fixed n) .target .markedPermanent, .«if» (.dealtDamageToSubtype subtype) (.destroy .permanentDealtDamage)]`. -/
  | dealDamageDestroyIfSubtype (n : Nat) (subtype : String)
  /-- Attach target Equipment to up to one target creature you control. -/
  | attachEquipmentToCreature
  /-- Other matching creatures get +P/+T; opposing creatures get +oppP/+oppT.
  Resolves as
  `.sequence [.pump (.fixed p) (.fixed t) (.intersection [.creaturesYouControl, .union (subtypes.toList.map .othersOfSubtype)]), .pump (.fixed oppP) (.fixed oppT) .opponentsCreatures]`. -/
  | othersGetAndOppsGet (subtypes : Array String) (power toughness oppP oppT : Int)
  /-- Another creature gets +X/+0 equal to this creature's power. -/
  | pumpTargetBySourcePower
  /-- Bolg reflexive damage. Resolves as
  `.sequence [.dealDamage .lastKnownPower .permanent .excess, .amass .notedExcess]`. -/
  | bolgDealSacrificedPower
  /-- Deal 1 then amass Orcs 1. Resolves as
  `.sequence [.dealDamage (.fixed 1) .target .markedPermanent, .amass (.fixed 1) "Orc"]`. -/
  | deal1ThenAmassOrcs
  /-- Untap attackers and take an extra combat. `n` is Oracle total power.
  Resolves as `.sequence [.untap .attackingCreatures, .additionalCombatPhase]`. -/
  | untapAttackersExtraCombat (n : Int)
  /-- If you drew two or more, another creature you control gets +3/+0 and
  gains first strike. Resolves as
  `.«if» (.atLeast .cardsDrawnThisTurn (.fixed 2)) (.sequence [.pump (.fixed 3) (.fixed 0) .target, .grant (.keywords Keyword.firstStrike) .target])`. -/
  | beginCombatIfDrawnTwoPump
  /-- Deal `n` to target opponent. -/
  | damageTargetOpponent (n : Nat)
  /-- Attach Equipment, then the host deals damage equal to its power.
  Resolves as
  `.sequence [.attach .anyYouControl .target, .«if» .equipmentAttached (.fight .equipmentHost .reflexive)]`. -/
  | attachEquipmentThenFight
  /-- Lose 1 life per burden counter.
  Resolves as `.loseLife .perBurden`. -/
  | loseLifePerBurden
  /-- Other permanents of this subtype get +X/+X equal to this toughness. -/
  | othersOfSubtypeGetEqualSourceToughness (subtype : String)
  /-- Creatures you control get +P/+T until end of turn. -/
  | creaturesYouControlGet (power toughness : Int)
  /-- If you control at least five other Forests, target creature you
  control gets +3/+3 until end of turn (Roiling Canopy). -/
  | pumpIfFiveOtherForests
deriving Repr, Inhabited, BEq

/-- Shared triggered-ability effects that exile, return cards from a graveyard
or exile, put cards onto the battlefield, sacrifice, destroy, or discard
(CR 400 / CR 701.8 / CR 701.9 / CR 701.17). -/
inductive ZoneChangeTrigger where
  /-- Exile a target of this kind until the source leaves. -/
  | exileUntilLeaves (kind : EffectTargetKind)
  /-- Target opponent sacrifices a creature of their choice. -/
  | opponentSacrificesCreature
  /-- Exile the top card; you may play it until the end of your next turn. -/
  | exileTop
  /-- Discard `n` cards. One card is `.discard`. -/
  | discard (n : Nat := 1)
  /-- An opponent discards `n` cards. Each opponent discards one is
  `.opponentDiscards`. The announced opponent discards `n` is
  `.opponentDiscards n .target`. -/
  | opponentDiscards (n : Nat := 1) (who : OpponentDiscard := .each)
  /-- Each player sacrifices a creature of their choice. -/
  | eachPlayerSacrificesCreature
  /-- Exile a target of this kind. -/
  | exileTarget (kind : EffectTargetKind)
  /-- Return a creature card from your graveyard to your hand. -/
  | returnCreatureFromGyToHand
  /-- Return cards exiled by the source. -/
  | returnLinkedExile
  /-- Landfall from the graveyard: pay to return this to hand. -/
  | payReturnFromGy
  /-- Return a target Elf from the graveyard, then gain life equal to its power.
  Resolves as `.sequence [.returnToHand .graveyardCard, .gainLife .equalToTargetPower]`. -/
  | returnElfGainLife
  /-- Destroy opponents' artifacts and enchantments; gain life for each.
  Resolves as
  `.sequence [.destroy .oppArtifactsEnchantments (note := .countDestroyed), .gainLife .forEachDestroyedThisWay]`. -/
  | destroyOppArtifactsEnchantmentsGainLife
  /-- Defending player sacrifices a least-power creature. -/
  | defenderSacsLeastPower
  /-- Return up to one other permanent you control to its owner's hand.
  If you do, put a +1/+1 counter on this creature.
  Resolves as `.sequence [.returnToHand .permanent .returnedPermanent, .«if» .returnedPermanent (.putCounters (.ofKind .plusOnePlusOne) .source)]`. -/
  | returnOtherPlusOne
  /-- Put a nonland with mana value `mv` or less from a graveyard onto the battlefield. -/
  | putNonlandMvAtMostFromGy (mv : Nat)
  /-- Exile up to one opposing nonland per opponent until this leaves. -/
  | exileOppNonlandEachUntilLeaves
  /-- You may put an artifact from hand; attach if Equipment. Resolves as
  `.sequence [.may (.put .artifactFromHand (note := .forAttach)) (.sequence []), .«if» (.atLeast (.count .putEquipment) (.fixed 1)) (.attach .putArtifact .notedHost)]`. -/
  | mayPutArtifactAttachEquipment
  /-- Bolg may-sacrifice. Resolves as `.may (.sacrifice .another) (.sequence [])`. -/
  | bolgMaySacrifice
  /-- Destroy another; its controller amasses equal to its power. Resolves as
  `.sequence [.destroy .target (note := .forAmass), .amass .notedPower (who := .controller .target), .«if» .youControlledDestroyed (.draw (.fixed 1))]`. -/
  | destroyOtherAmassControllerPower
  /-- Return as an artifact. -/
  | returnAsArtifact
  /-- Exile lands, then return them tapped. -/
  | exileLandsThenReturnTapped
  /-- Opponents sac damagers; the Ring tempts you. Resolves as
  `.sequence [.sacrifice .combatDamager, .ringTempts]`. -/
  | sacDamagersRingTempts
  /-- If you control six or more lands, destroy target permanent an opponent
  controls; its controller creates a Treasure. Resolves as
  `.«if» ((.atLeast (.count .landsYouControl) (.fixed 6))) (.sequence [.destroy .target, .createTokens .treasure (.fixed 1) false (who := .controller .target)])`. -/
  | destroyOppPermanentIfSixLands
  /-- If you don't control a planeswalker, sacrifice the source.
  Resolves as `.«if» (.not (.atLeast (.count .planeswalkersYouControl) (.fixed 1))) (.sacrifice (.sacrificedSource .controllerSacrifices))`. -/
  | sacrificeSourceIfNoPlaneswalker
  /-- Exile another creature; enchanted becomes a copy. Resolves as
  `.sequence [.exile .target .untilSourceLeaves .copyAndHost, .becomeCopy .noted]`. -/
  | exileOtherCopyEnchanted
  /-- Exile a creature you control until the next end step. -/
  | exileUntilNextEndStep
deriving Repr, Inhabited, BEq

/-- Shared triggered-ability effects that grant continuous effects, tap or
untap permanents, gain control, add mana, cast or copy spells, choose
modes, or prepare permanents (CR 611 / CR 700.2 / CR 701.21 / CR 706). -/
inductive ContinuousTrigger where
  /-- Add these mana types. -/
  | addMana (types : Array ManaType)
  /-- Tap an opposing creature or untap yours.
  Resolves as `.or [.tap .target, .untap]`. -/
  | tapOppOrUntapYours
  /-- Gain control of the target until end of turn; untap; haste. -/
  | gainControlOppUntilEot
  /-- You may cast an instant or sorcery from hand. -/
  | castInstantSorceryFromHand
  /-- You may cast an instant or sorcery with mana value at most that damage. -/
  | castInstantSorceryMvAtMost
  /-- Alliance modes. Resolves as
  `.chooseModes TriggerResolution.allianceModes .oneUnusedThisTurn`. -/
  | allianceMode
  /-- Gollum parity modes. Resolves as
  `.chooseModes TriggerResolution.gollumModes .oneUnused`. -/
  | gollumMode
  /-- Cast artifact, instant, or sorcery from the graveyard. -/
  | castFromGyArtifactInstantSorcery
  /-- Equipped attackers gain double strike. Resolves as
  `.grant .doubleStrike .equippedAttackers`. -/
  | equippedAttackersGainDoubleStrike
  /-- Tap enchanted creature and remove counters. Resolves as
  `.sequence [.tap .enchanted, .removeCounters .all .enchanted]`. -/
  | tapEnchantedRemoveCounters
  /-- If not a token, create nonlegendary copies. -/
  | copySelfNonlegendary
  /-- If you cast it, protection from everything. Resolves as
  `.grant .protectionEverything .youIfCast`. -/
  | protectionEverything
  /-- This creature becomes prepared.
  If it isn't prepared is `.prepareSource`.
  If three or more creatures died this turn is
  `.prepareSource .ifThreeCreaturesDied`. -/
  | prepareSource (when : PrepareWhen := .ifNotPrepared)
  /-- Add {G} for each charge counter on the source.
  Resolves as `.addMana #[.colored .green] .perChargeCounter`. -/
  | addGreenPerChargeCounter
  /-- Tap or untap target nonland.
  Resolves as `.or [.tap .target, .untap]`. -/
  | tapOrUntapNonland
deriving Repr, Inhabited, BEq

/-- Shared triggered-ability effects that apply a `PermanentAction` to a
target, the source, the enchanted permanent, or an attached creature
(CR 603 / CR 608). -/
inductive PermanentTrigger where
  /-- Affect a still-legal permanent target. -/
  | onPermanent (kind : EffectTargetKind) (action : PermanentAction)
  /-- Affect the trigger's source if it is still on the battlefield.
  Resolves as `TriggerResolution.ofSource`. -/
  | onSource (action : PermanentAction)
  /-- Apply `action` to the enchanted creature.
  Resolves as `TriggerResolution.ofEnchanted`. -/
  | onEnchanted (action : PermanentAction)
  /-- Attach to target, then apply `followup`. Resolves as `.attach .source .target`
  followed by `TriggerResolution.ofTargetWhileSource`. -/
  | attachThen (followup : PermanentAction)
deriving Repr, Inhabited, BEq

/-- Event-specific leftover triggered-ability families (CR 603). -/
inductive EventLeftover where
  /-- Leftover “when this enters” effect. -/
  | enter (e : EnterLeftover)
  /-- Leftover step / upkeep / end-step / first-main effect.
  The enchanted creature's controller draws a card, as
  `.draw (.fixed 1) (who := .controller .enchanted)`.
  Drawing until you have ten cards is `.draw (.upToHandSize 10)`.
  Becoming a copy of an artifact, non-Aura enchantment, or land is
  `.becomeCopy .artifactEnchantmentOrLand`.
  Choosing a +1/+1 counter or removing a counter to draw is
  `.chooseModes TriggerResolution.hydeModes .plusOneOrRemoveCounter`.
  Becoming a copy of a creature or a graveyard creature card is
  `.becomeCopy .creatureOrGraveyardCard`.
  Exiling and returning another nonland while harnessed is
  `.«if» (.atLeast (.count .harnessedSource) (.fixed 1)) (.exile .target .returnImmediately)`. -/
  | step (e : StepLeftover)
  /-- Leftover dies effect.
  Hellcat returns under her owner's control, losing all abilities, gaining
  haste, and entering with a +1/+1 counter, as
  `.put .source .underOwner (.entering [.loseAllAbilities, .keywords Keyword.haste, .counter .plusOnePlusOne (asEnters := true)])`.
  A Villain returns under its owner's control as a Hero with a finality
  counter, as
  `.put (.cause (some "Villain")) .underOwner (.entering [.additionalSubtype "Hero", .counter .finality])`.
  The attacking creature that died returns to its owner's hand, as
  `.returnToHand .cause`.
  Each opponent sacrifices a nontoken creature, as
  `.sacrifice .chosenNontokenCreature`. -/
  | death (e : DeathLeftover)
  /-- Leftover “whenever this attacks” effect.
  Paying {1} to put a +1/+1 counter on target creature is
  `.may (.pay (.mana #[.generic 1])) (.queueReflexive (.putCounters (.ofKind .plusOnePlusOne) .permanent)) .ifYouDo`.
  Paying {3}{B} to return a graveyard creature tapped and attacking is
  `.may (.pay (.mana #[.generic 3, .colored .black])) (.queueReflexive (.put .creatureCard .tapped (.entering [.attacking, .counter .finality]))) .ifYouDo`.
  Drawing when an artifact entered under your control this turn is
  `.«if» .artifactEnteredThisTurn (.draw (.fixed 1))`.
  Exiling a nontoken artifact or creature and returning it tapped is
  `.exile .target .returnTapped`.
  Each opponent losing X life and you gaining X life, X the Equipment
  attached to the source, is
  `.«if» .attachedEquipment (.sequence [.loseLife .attachedEquipment .eachOpponent, .gainLife .attachedEquipment])`.
  Drawing when the source's power is 4 or greater is
  `.«if» (.atLeast .equalSourcePower (.fixed 4)) (.draw (.fixed 1))`.
  The source getting +2/+0 and indestructible until end of turn is
  `.sequence [.pump (.fixed 2) (.fixed 0) .source, .grant (.keywords Keyword.indestructible) .source]`. -/
  | thisAttack (e : ThisAttackLeftover)
  /-- Leftover “enters or attacks” effect.
  Copying the keyword counters the source lacks is
  `.putCounters .missingKeywordsFromTarget .source`.
  A 1/1 green Squirrel is `.createTokens .squirrel11green (.fixed 1) false`. -/
  | enterOrAttack (e : EnterOrAttackLeftover)
  /-- Leftover watch effect.
  Drawing a card is `.draw (.fixed 1)`. You may draw a card is
  `.may (.draw (.fixed 1)) (.sequence []) .ifYouDo`.
  A +1/+1 counter on the source is `.putCounters (.ofKind .plusOnePlusOne) .source`.
  Two +1/+1 counters are `.putCounters (.ofKind .plusOnePlusOne 2) .source`.
  A counter that is not put after the source has left, then 2 damage to
  each opponent, is
  `.sequence [.putCounters (.ofKind .plusOnePlusOne) .sourceIfPresent, .dealDamage (.fixed 2) (.player .eachOpponent)]`.
  +1/+0 and lifelink until end of turn is
  `.sequence [.pump (.fixed 1) (.fixed 0) .source, .grant (.keywords Keyword.lifelink) .source]`.
  First strike and menace on the creature attacking alone is
  `.grant (.keywords (Keywords.merge Keyword.firstStrike Keyword.menace)) .attackingAlone`.
  The opponent loses 1 life and you gain 1 life is
  `.sequence [.loseLife (.fixed 1) (.target .opponent), .gainLife (.fixed 1)]`.
  1 damage to the announced opponent is `.dealDamage (.fixed 1) (.player (.target .opponent))`.
  1 damage from the equipped creature to each opponent is
  `.dealDamage (.fixed 1) (.player .eachOpponent) .fromEquipped`.
  Tapping the announced creature is `.tap .target`.
  Untapping the creature that became tapped is `.untap .firstThisTurn`.
  Untapping the equipped creature, then scrying 1, is
  `.sequence [.untap .equipped, .scry (.fixed 1)]`.
  A +1/+1 counter when the entering creature is greater is
  `.«if» (.or [.causeGreaterPower, .causeGreaterToughness]) (.putCounters (.ofKind .plusOnePlusOne) .source)`.
  Putting a counter, untapping when attacking, and an Enrage combat is
  `.sequence [.putCounters (.ofKind .plusOnePlusOne) .source, .«if» (.atLeast (.count (.intersection [.source, .attackingCreatures])) (.fixed 1)) (.untap .source), .«if» .enrageGrantsCombat .additionalCombatPhase]`.
  Putting a counter, then damage equal to those counters, is
  `.sequence [.putCounters (.ofKind .plusOnePlusOne) .source, .queueReflexive (.dealDamage .plusOneCounters .target)]`.
  +2/+2, then you may retarget the spell, is
  `.sequence [.pump (.fixed 2) (.fixed 2) .source, .may .retargetCause (.sequence []) .ifYouDo]`.
  You may have the entering Villain connive is `.connive .enteringVillain`.
  Attaching the announced Equipment to the announced creature is
  `.attach .announcedEquipment .announcedCreature`.
  Attaching each announced Equipment to the enchanted creature is
  `.attach (.target .eachEquipment) .enchantedCreature`.
  Choosing a Soldier or a team pump from the last-known mode is
  `.chooseModes [.createTokens .soldier11white (.fixed 1) false, .pump (.fixed 1) (.fixed 1) .creaturesYouControl] .fromLastKnown`.
  Paying {1} up to three times is
  `.may (.pay (.mana #[.generic 1])) (.queueReflexive (.chooseModes TriggeredAbility.TriggerResolution.trickArrowModes .alreadyChosen)) .ifYouDo`.
  Exiling until a nonland, then a counter or a cast, is
  `.revealLibrary .untilNonland (.may (.putCounters (.ofKind .plusOnePlusOne) .source) (.exile .top .forLater .anyManaThisTurn) .ifYouDont) .announced`.
  You may deal the damage that caused this is
  `.may (.dealDamage .lastKnownPower .target) (.sequence []) .ifYouDo`.
  You may pay {2} to copy the artifact that caused this is
  `.may (.pay (.mana #[.generic 2])) (.becomeCopy .cause) .ifYouDo`. -/
  | watch (e : WatchLeftover)
  /-- Leftover “whenever you attack” effect.
  Paying 2 life so creatures you control assign combat damage equal to their
  toughness is
  `.may (.loseLife (.fixed 2)) (.grant .assignCombatDamageEqualToughness .creaturesYouControl) .ifYouDo`.
  Exiling the top card, pumping +2/+1 when it is a Hero, and playing it this
  turn is `.may (.exile .top .playThisTurn .ifHero) (.sequence [])`.
  Looking at the top six and casting one with mana value at most the greatest
  attacking power, without paying, is
  `.revealLibrary (.top 6) (.mayCast .looked .greatestAttackingPower .withoutPaying)`. -/
  | youAttacking (e : YouAttackLeftover)
  /-- Leftover “whenever you cast …” effect.
  A 2/1 black Villain with menace is `.createTokens .villain21menace (.fixed 1) false`.
  One 1/1 blue Merfolk for each blue mana symbol in the spell is
  `.createTokens .treasure .blueManaSymbols false .merfolk`.
  Paying {1} so a creature with haste can't be blocked except by creatures
  with haste is
  `.may (.pay (.mana #[.generic 1])) (.queueReflexive (.cant (.beBlockedExceptByHaste .target))) .ifYouDo`.
  A +1/+1 counter on each other creature you control is
  `.putCounters (.ofKind .plusOnePlusOne) .eachOther`.
  Exiling another nonland nontoken until the next end step is
  `.exile .target .nextEndStep`.
  One unused Vision mode this turn is
  `.chooseModes TriggerResolution.visionModes .vision`.
  Damage equal to that spell's mana value is
  `.dealDamage .spellManaValue .target`.
  Drawing a card, then base power equal to the cards in hand, is
  `.sequence [.draw (.fixed 1), .grant .basePowerEqualHand .source]`.
  A +1/+1 counter on the source is
  `.putCounters (.ofKind .plusOnePlusOne) .source`.
  That counter, then scry 1, is
  `.sequence [.putCounters (.ofKind .plusOnePlusOne) .source, .scry (.fixed 1)]`.
  Iron Fist's tap ability until end of turn is `.grant .ironFistTap .source`.
  Flying on the spell's creature targets is
  `.grant (.keywords Keyword.flying) .spellTargets`.
  Two +1/+1 counters on the source, then a copy of the spell, is
  `.sequence [.putCounters (.ofKind .plusOnePlusOne 2) .source, .copyCause]`.
  Tapping the announced creature or land is `.tap .target`. -/
  | casting (e : CastLeftover)
  /-- Leftover draw, discard, life, and +1/+1-counter effect.
  `ResourceLeftover` stays the printed sentence.
  You may exile the discarded card and play it until the end of your next
  turn with
  `.may (.exile .discarded .playUntilNextTurn) (.sequence []) .ifYouDo`.
  If you control another Hero, 1 damage to the announced opponent is
  `.«if» (.atLeast (.count (.othersOfSubtype "Hero")) (.fixed 1)) (.dealDamage (.fixed 1) (.player (.target .opponent)))`.
  Base power and toughness 6/6 and trample until end of turn is
  `.sequence [.setBasePT (.fixed 6) (.fixed 6) .source, .grant (.keywords Keyword.trample) .source]`.
  A +1/+1 counter on the announced creature is
  `.putCounters (.ofKind .plusOnePlusOne) .permanent`.
  Each opponent loses 1 life and you gain 1 life is
  `.sequence [.loseLife (.fixed 1) .eachOpponent, .gainLife (.fixed 1)]`.
  A +1/+1 counter on each announced creature you control, up to the life
  gained, is `.putCounters (.ofKind .plusOnePlusOne) .eachUpToLastKnown`.
  A 1/1 green Insect is `.createTokens .insect11green (.fixed 1) false`.
  A +1/+1 counter on the source is
  `.putCounters (.ofKind .plusOnePlusOne) .source`.
  You may create a 0/4 Wall with defender is
  `.may (.createTokens .wall04defender (.fixed 1) false) (.sequence []) .ifYouDo`. -/
  | resource (e : ResourceLeftover)
deriving Repr, Inhabited, BEq

/-- Shared resolution for reusable triggered abilities that only differ by
when they fire (CR 603 / CR 608). Grouped by effect category so the inductive
stays compact while `SharedTrigger.*` pattern aliases preserve existing names. -/
inductive SharedTrigger where
  /-- Library, card-draw, scry, surveil, mill, search, or reveal trigger effect. -/
  | library (t : LibraryTrigger)
  /-- Token, amass, recruit, investigate, counter, Ring, or Plan trigger effect. -/
  | tokenCounter (t : TokenCounterTrigger)
  /-- Damage, life, power/toughness, attach, fight, or combat trigger effect. -/
  | combatDamage (t : CombatDamageTrigger)
  /-- Exile, return, put onto battlefield, sacrifice, destroy, or discard trigger effect. -/
  | zoneChange (t : ZoneChangeTrigger)
  /-- Continuous, tap/untap, control, mana, cast/copy, modal, or prepare trigger effect. -/
  | continuous (t : ContinuousTrigger)
  /-- `PermanentAction` applied to a target, source, enchanted, or attached permanent. -/
  | permanent (t : PermanentTrigger)
  /-- Event-specific leftover trigger effect family. -/
  | leftover (t : EventLeftover)
  /-- You may do `can`. If you do, `thenDo`.
  You may discard a card. If you do, draw `n` is `.mayTo .discard (.draw n)`.
  Resolves as `.may` of each step's resolution, `.ifYouDo`. -/
  | mayTo (can thenDo : SharedTrigger)
  /-- You may do `action`. Declining skips it.
  Resolves as `TriggerResolution.may` of `action`'s resolution.
  You may draw X cards, where X is the mana spent to cast that spell, then
  discard two, is `.may (.drawXDiscard 2)`. -/
  | may (action : SharedTrigger)
  /-- A Saga chapter. Resolves as `TriggeredAbility.chapterTiming`. -/
  | chapter (n : Nat) (e : ChapterResolution)
deriving Repr, Inhabited, BEq

namespace SharedTrigger

-- LibraryTrigger aliases
@[match_pattern] abbrev scry (n : Nat) : SharedTrigger := .library (.scry n)
@[match_pattern] abbrev draw (n : Nat) : SharedTrigger := .library (.draw n)
@[match_pattern] abbrev connive (who : ConniveSubject := .source) : SharedTrigger := .library (.connive who)
@[match_pattern] abbrev millPlayer (n : Nat) : SharedTrigger := .library (.millPlayer n)
@[match_pattern] abbrev searchLibrary : SharedTrigger := .library .searchLibrary
@[match_pattern] abbrev searchBasicLandToHand : SharedTrigger := .library .searchBasicLandToHand
@[match_pattern] abbrev mayDiscardHandDraw (n : Nat) : SharedTrigger := .library (.mayDiscardHandDraw n)
@[match_pattern] abbrev drawXDiscard (n : Nat) : SharedTrigger := .library (.drawXDiscard n)
@[match_pattern] abbrev mayPayGenericDraw (n : Nat) (plusOneOnSource : Bool := false) : SharedTrigger := .library (.mayPayGenericDraw n plusOneOnSource)
@[match_pattern] abbrev drawThenBottomIfNoLegendary : SharedTrigger := .library .drawThenBottomIfNoLegendary
@[match_pattern] abbrev tapHumansDraw : SharedTrigger := .library .tapHumansDraw
@[match_pattern] abbrev lookAtTopRevealTypes (n : Nat) (types : Array String) : SharedTrigger := .library (.lookAtTopRevealTypes n types)
@[match_pattern] abbrev millThenSubtypeToHand (n : Nat) (subtype : String) : SharedTrigger := .library (.millThenSubtypeToHand n subtype)
@[match_pattern] abbrev revealUntilCreature : SharedTrigger := .library .revealUntilCreature
@[match_pattern] abbrev lootLandEntersTapped : SharedTrigger := .library .lootLandEntersTapped
@[match_pattern] abbrev millThatManyLost : SharedTrigger := .library .millThatManyLost
@[match_pattern] abbrev drawPerFatGraveyard : SharedTrigger := .library .drawPerFatGraveyard
@[match_pattern] abbrev millThenCopy : SharedTrigger := .library .millThenCopy
@[match_pattern] abbrev cascade : SharedTrigger := .library .cascade
@[match_pattern] abbrev discardHandDrawDamageIfStory : SharedTrigger := .library .discardHandDrawDamageIfStory
@[match_pattern] abbrev revealTopPutRandomCreature (n : Nat) : SharedTrigger := .library (.revealTopPutRandomCreature n)
@[match_pattern] abbrev grimaImpulse : SharedTrigger := .library .grimaImpulse
@[match_pattern] abbrev palantir : SharedTrigger := .library .palantir
@[match_pattern] abbrev revealSaga : SharedTrigger := .library .revealSaga
@[match_pattern] abbrev drawIfAttackedOrEnteredSubtype (subtype : String) : SharedTrigger := .library (.drawIfAttackedOrEnteredSubtype subtype)
@[match_pattern] abbrev surveil (n : Nat) : SharedTrigger := .library (.surveil n)
@[match_pattern] abbrev drawIfRemovedTwoLoyalty : SharedTrigger := .library .drawIfRemovedTwoLoyalty
@[match_pattern] abbrev drawTwoWinIfEmptyShuffleSource : SharedTrigger := .library .drawTwoWinIfEmptyShuffleSource
@[match_pattern] abbrev surveilReturnIfGainedLife : SharedTrigger := .library .surveilReturnIfGainedLife
@[match_pattern] abbrev drawMayPutLandTapped : SharedTrigger := .library .drawMayPutLandTapped
@[match_pattern] abbrev drawGainLifeIfAnotherHero : SharedTrigger := .library .drawGainLifeIfAnotherHero
@[match_pattern] abbrev maySacArtifactOrDiscardDraw : SharedTrigger := .library .maySacArtifactOrDiscardDraw

-- TokenCounterTrigger aliases
@[match_pattern] abbrev createTokens (kind : TokenKind) (n : Nat) (tapped : Bool := false) : SharedTrigger := .tokenCounter (.createTokens kind n tapped)
@[match_pattern] abbrev amass (n : Nat) (subtype : String := "Goblin") (amount : AmassAmount := .fixed) (attachSource : Bool := false) : SharedTrigger := .tokenCounter (.amass n subtype amount attachSource)
@[match_pattern] abbrev recruit (who : RecruitSubject := .recruit) : SharedTrigger := .tokenCounter (.recruit who)
@[match_pattern] abbrev investigate : SharedTrigger := .tokenCounter .investigate
@[match_pattern] abbrev plusOneEachYouControl (which : YouControlPlusOne := .eachCreature) : SharedTrigger := .tokenCounter (.plusOneEachYouControl which)
@[match_pattern] abbrev honeEachEquipment : SharedTrigger := .tokenCounter .honeEachEquipment
@[match_pattern] abbrev plusOneEachOtherGainLife : SharedTrigger := .tokenCounter .plusOneEachOtherGainLife
@[match_pattern] abbrev createThenAttach (kind : TokenKind) : SharedTrigger := .tokenCounter (.createThenAttach kind)
@[match_pattern] abbrev createAxe (attach : Bool := false) : SharedTrigger := .tokenCounter (.createAxe attach)
@[match_pattern] abbrev ringTempts : SharedTrigger := .tokenCounter .ringTempts
@[match_pattern] abbrev removeHopeDrawSac : SharedTrigger := .tokenCounter .removeHopeDrawSac
@[match_pattern] abbrev createTappedTreasuresEqualOppArtifacts : SharedTrigger := .tokenCounter .createTappedTreasuresEqualOppArtifacts
@[match_pattern] abbrev wolfPlusOneOrTreasure : SharedTrigger := .tokenCounter .wolfPlusOneOrTreasure
@[match_pattern] abbrev trampleCounterBecomeBear : SharedTrigger := .tokenCounter .trampleCounterBecomeBear
@[match_pattern] abbrev plusOneEqualLastKnownMv : SharedTrigger := .tokenCounter .plusOneEqualLastKnownMv
@[match_pattern] abbrev mountainQuestDragon : SharedTrigger := .tokenCounter .mountainQuestDragon
@[match_pattern] abbrev treasuresPerChosenType : SharedTrigger := .tokenCounter .treasuresPerChosenType
@[match_pattern] abbrev attackSacPlusOneEqualPower : SharedTrigger := .tokenCounter .attackSacPlusOneEqualPower
@[match_pattern] abbrev maySacDrawTreasure : SharedTrigger := .tokenCounter .maySacDrawTreasure
@[match_pattern] abbrev createAlienPerInvasion : SharedTrigger := .tokenCounter .createAlienPerInvasion
@[match_pattern] abbrev belladonnaTokenReward : SharedTrigger := .tokenCounter .belladonnaTokenReward
@[match_pattern] abbrev createSpiritsForEquipped : SharedTrigger := .tokenCounter .createSpiritsForEquipped
@[match_pattern] abbrev createTreasuresEqualDamagedPlayerArtifacts : SharedTrigger := .tokenCounter .createTreasuresEqualDamagedPlayerArtifacts
@[match_pattern] abbrev eaglesCreateBirds : SharedTrigger := .tokenCounter .eaglesCreateBirds
@[match_pattern] abbrev honePerOppAttach : SharedTrigger := .tokenCounter .honePerOppAttach
@[match_pattern] abbrev treasuresEqualLastKnown : SharedTrigger := .tokenCounter .treasuresEqualLastKnown
@[match_pattern] abbrev scryAndPlan (n : Nat) : SharedTrigger := .tokenCounter (.scryAndPlan n)
@[match_pattern] abbrev lootAndPlan : SharedTrigger := .tokenCounter .lootAndPlan
@[match_pattern] abbrev createVillainAndPlan : SharedTrigger := .tokenCounter .createVillainAndPlan
@[match_pattern] abbrev drainAndPlan (n : Nat) : SharedTrigger := .tokenCounter (.drainAndPlan n)
@[match_pattern] abbrev drawLoseLifeAndPlan : SharedTrigger := .tokenCounter .drawLoseLifeAndPlan
@[match_pattern] abbrev treasureTappedAndPlan : SharedTrigger := .tokenCounter .treasureTappedAndPlan
@[match_pattern] abbrev plusOneOnTargetAndPlan : SharedTrigger := .tokenCounter .plusOneOnTargetAndPlan
@[match_pattern] abbrev planFinishDrawPlusOneEach : SharedTrigger := .tokenCounter .planFinishDrawPlusOneEach
@[match_pattern] abbrev planFinishReturnInstants : SharedTrigger := .tokenCounter .planFinishReturnInstants
@[match_pattern] abbrev planFinishControlOpponent : SharedTrigger := .tokenCounter .planFinishControlOpponent
@[match_pattern] abbrev planFinishExileTopCast : SharedTrigger := .tokenCounter .planFinishExileTopCast
@[match_pattern] abbrev planFinishCreateRobots (n : Nat) : SharedTrigger := .tokenCounter (.planFinishCreateRobots n)
@[match_pattern] abbrev planFinishDividedDamage (n : Nat) : SharedTrigger := .tokenCounter (.planFinishDividedDamage n)
@[match_pattern] abbrev planFinishIndestructibleOnTarget : SharedTrigger := .tokenCounter .planFinishIndestructibleOnTarget
@[match_pattern] abbrev empowerJace (n : Nat) : SharedTrigger := .tokenCounter (.empowerJace n)
@[match_pattern] abbrev loyaltyOnSource : SharedTrigger := .tokenCounter .loyaltyOnSource
@[match_pattern] abbrev grantThenCounterByType (k : Keywords) : SharedTrigger := .tokenCounter (.grantThenCounterByType k)
@[match_pattern] abbrev pumpOrCounterIfScried : SharedTrigger := .tokenCounter .pumpOrCounterIfScried
@[match_pattern] abbrev putSourceCountersOnTarget : SharedTrigger := .tokenCounter .putSourceCountersOnTarget
@[match_pattern] abbrev chargeCounterOnSource : SharedTrigger := .tokenCounter .chargeCounterOnSource
@[match_pattern] abbrev createFoodOrTreasure : SharedTrigger := .tokenCounter .createFoodOrTreasure
@[match_pattern] abbrev villainIfGyElseMill : SharedTrigger := .tokenCounter .villainIfGyElseMill
@[match_pattern] abbrev plusOneOrTwoIfAnotherHero : SharedTrigger := .tokenCounter .plusOneOrTwoIfAnotherHero

-- CombatDamageTrigger aliases
@[match_pattern] abbrev dividedDamage (amount maxTargets : Nat) : SharedTrigger := .combatDamage (.dividedDamage amount maxTargets)
@[match_pattern] abbrev gainLife (n : Nat) : SharedTrigger := .combatDamage (.gainLife n)
@[match_pattern] abbrev damageEachOpponent (n : Nat) : SharedTrigger := .combatDamage (.damageEachOpponent n)
@[match_pattern] abbrev attachTo (kind : EffectTargetKind) : SharedTrigger := .combatDamage (.attachTo kind)
@[match_pattern] abbrev pumpCause (power toughness : Int) : SharedTrigger := .combatDamage (.pumpCause power toughness)
@[match_pattern] abbrev becomePT (power toughness : Int) : SharedTrigger := .combatDamage (.becomePT power toughness)
@[match_pattern] abbrev pumpTargetPerPlains : SharedTrigger := .combatDamage .pumpTargetPerPlains
@[match_pattern] abbrev pumpByLookedAt : SharedTrigger := .combatDamage .pumpByLookedAt
@[match_pattern] abbrev pumpGreatestPower : SharedTrigger := .combatDamage .pumpGreatestPower
@[match_pattern] abbrev pumpForEachOtherCreature : SharedTrigger := .combatDamage .pumpForEachOtherCreature
@[match_pattern] abbrev damageBlockers (n : Nat) : SharedTrigger := .combatDamage (.damageBlockers n)
@[match_pattern] abbrev gainLifeSearchBasicOnTop (n : Nat) : SharedTrigger := .combatDamage (.gainLifeSearchBasicOnTop n)
@[match_pattern] abbrev targetOpponentLosesLife (n : Nat) : SharedTrigger := .combatDamage (.targetOpponentLosesLife n)
@[match_pattern] abbrev setOtherBasePT : SharedTrigger := .combatDamage .setOtherBasePT
@[match_pattern] abbrev damageFromLastKnownPower : SharedTrigger := .combatDamage .damageFromLastKnownPower
@[match_pattern] abbrev damageEqualSubtypeToEachOpponent (subtype : String) : SharedTrigger := .combatDamage (.damageEqualSubtypeToEachOpponent subtype)
@[match_pattern] abbrev damageEqualTreasures : SharedTrigger := .combatDamage .damageEqualTreasures
@[match_pattern] abbrev dealDamageDestroyIfSubtype (n : Nat) (subtype : String) : SharedTrigger := .combatDamage (.dealDamageDestroyIfSubtype n subtype)
@[match_pattern] abbrev attachEquipmentToCreature : SharedTrigger := .combatDamage .attachEquipmentToCreature
@[match_pattern] abbrev othersGetAndOppsGet (subtypes : Array String) (power toughness oppP oppT : Int) : SharedTrigger := .combatDamage (.othersGetAndOppsGet subtypes power toughness oppP oppT)
@[match_pattern] abbrev pumpTargetBySourcePower : SharedTrigger := .combatDamage .pumpTargetBySourcePower
@[match_pattern] abbrev bolgDealSacrificedPower : SharedTrigger := .combatDamage .bolgDealSacrificedPower
@[match_pattern] abbrev deal1ThenAmassOrcs : SharedTrigger := .combatDamage .deal1ThenAmassOrcs
@[match_pattern] abbrev untapAttackersExtraCombat (n : Int) : SharedTrigger := .combatDamage (.untapAttackersExtraCombat n)
@[match_pattern] abbrev beginCombatIfDrawnTwoPump : SharedTrigger := .combatDamage .beginCombatIfDrawnTwoPump
@[match_pattern] abbrev damageTargetOpponent (n : Nat) : SharedTrigger := .combatDamage (.damageTargetOpponent n)
@[match_pattern] abbrev attachEquipmentThenFight : SharedTrigger := .combatDamage .attachEquipmentThenFight
@[match_pattern] abbrev loseLifePerBurden : SharedTrigger := .combatDamage .loseLifePerBurden
@[match_pattern] abbrev othersOfSubtypeGetEqualSourceToughness (subtype : String) : SharedTrigger := .combatDamage (.othersOfSubtypeGetEqualSourceToughness subtype)
@[match_pattern] abbrev creaturesYouControlGet (power toughness : Int) : SharedTrigger := .combatDamage (.creaturesYouControlGet power toughness)
@[match_pattern] abbrev pumpIfFiveOtherForests : SharedTrigger := .combatDamage .pumpIfFiveOtherForests

-- ZoneChangeTrigger aliases
@[match_pattern] abbrev exileUntilLeaves (kind : EffectTargetKind) : SharedTrigger := .zoneChange (.exileUntilLeaves kind)
@[match_pattern] abbrev opponentSacrificesCreature : SharedTrigger := .zoneChange .opponentSacrificesCreature
@[match_pattern] abbrev exileTop : SharedTrigger := .zoneChange .exileTop
@[match_pattern] abbrev discard (n : Nat := 1) : SharedTrigger := .zoneChange (.discard n)
@[match_pattern] abbrev opponentDiscards (n : Nat := 1) (who : OpponentDiscard := .each) : SharedTrigger := .zoneChange (.opponentDiscards n who)
@[match_pattern] abbrev eachPlayerSacrificesCreature : SharedTrigger := .zoneChange .eachPlayerSacrificesCreature
@[match_pattern] abbrev exileTarget (kind : EffectTargetKind) : SharedTrigger := .zoneChange (.exileTarget kind)
@[match_pattern] abbrev returnCreatureFromGyToHand : SharedTrigger := .zoneChange .returnCreatureFromGyToHand
@[match_pattern] abbrev returnLinkedExile : SharedTrigger := .zoneChange .returnLinkedExile
@[match_pattern] abbrev payReturnFromGy : SharedTrigger := .zoneChange .payReturnFromGy
@[match_pattern] abbrev returnElfGainLife : SharedTrigger := .zoneChange .returnElfGainLife
@[match_pattern] abbrev destroyOppArtifactsEnchantmentsGainLife : SharedTrigger := .zoneChange .destroyOppArtifactsEnchantmentsGainLife
@[match_pattern] abbrev defenderSacsLeastPower : SharedTrigger := .zoneChange .defenderSacsLeastPower
@[match_pattern] abbrev returnOtherPlusOne : SharedTrigger := .zoneChange .returnOtherPlusOne
@[match_pattern] abbrev putNonlandMvAtMostFromGy (mv : Nat) : SharedTrigger := .zoneChange (.putNonlandMvAtMostFromGy mv)
@[match_pattern] abbrev exileOppNonlandEachUntilLeaves : SharedTrigger := .zoneChange .exileOppNonlandEachUntilLeaves
@[match_pattern] abbrev mayPutArtifactAttachEquipment : SharedTrigger := .zoneChange .mayPutArtifactAttachEquipment
@[match_pattern] abbrev bolgMaySacrifice : SharedTrigger := .zoneChange .bolgMaySacrifice
@[match_pattern] abbrev destroyOtherAmassControllerPower : SharedTrigger := .zoneChange .destroyOtherAmassControllerPower
@[match_pattern] abbrev returnAsArtifact : SharedTrigger := .zoneChange .returnAsArtifact
@[match_pattern] abbrev exileLandsThenReturnTapped : SharedTrigger := .zoneChange .exileLandsThenReturnTapped
@[match_pattern] abbrev sacDamagersRingTempts : SharedTrigger := .zoneChange .sacDamagersRingTempts
@[match_pattern] abbrev destroyOppPermanentIfSixLands : SharedTrigger := .zoneChange .destroyOppPermanentIfSixLands
@[match_pattern] abbrev sacrificeSourceIfNoPlaneswalker : SharedTrigger := .zoneChange .sacrificeSourceIfNoPlaneswalker
@[match_pattern] abbrev exileOtherCopyEnchanted : SharedTrigger := .zoneChange .exileOtherCopyEnchanted
@[match_pattern] abbrev exileUntilNextEndStep : SharedTrigger := .zoneChange .exileUntilNextEndStep

-- ContinuousTrigger aliases
@[match_pattern] abbrev addMana (types : Array ManaType) : SharedTrigger := .continuous (.addMana types)
@[match_pattern] abbrev tapOppOrUntapYours : SharedTrigger := .continuous .tapOppOrUntapYours
@[match_pattern] abbrev gainControlOppUntilEot : SharedTrigger := .continuous .gainControlOppUntilEot
@[match_pattern] abbrev castInstantSorceryFromHand : SharedTrigger := .continuous .castInstantSorceryFromHand
@[match_pattern] abbrev castInstantSorceryMvAtMost : SharedTrigger := .continuous .castInstantSorceryMvAtMost
@[match_pattern] abbrev allianceMode : SharedTrigger := .continuous .allianceMode
@[match_pattern] abbrev gollumMode : SharedTrigger := .continuous .gollumMode
@[match_pattern] abbrev castFromGyArtifactInstantSorcery : SharedTrigger := .continuous .castFromGyArtifactInstantSorcery
@[match_pattern] abbrev equippedAttackersGainDoubleStrike : SharedTrigger := .continuous .equippedAttackersGainDoubleStrike
@[match_pattern] abbrev tapEnchantedRemoveCounters : SharedTrigger := .continuous .tapEnchantedRemoveCounters
@[match_pattern] abbrev copySelfNonlegendary : SharedTrigger := .continuous .copySelfNonlegendary
@[match_pattern] abbrev protectionEverything : SharedTrigger := .continuous .protectionEverything
@[match_pattern] abbrev prepareSource (when : PrepareWhen := .ifNotPrepared) : SharedTrigger := .continuous (.prepareSource when)
@[match_pattern] abbrev addGreenPerChargeCounter : SharedTrigger := .continuous .addGreenPerChargeCounter
@[match_pattern] abbrev tapOrUntapNonland : SharedTrigger := .continuous .tapOrUntapNonland

-- PermanentTrigger aliases
@[match_pattern] abbrev onPermanent (kind : EffectTargetKind) (action : PermanentAction) : SharedTrigger := .permanent (.onPermanent kind action)
@[match_pattern] abbrev onSource (action : PermanentAction) : SharedTrigger := .permanent (.onSource action)
@[match_pattern] abbrev onEnchanted (action : PermanentAction) : SharedTrigger := .permanent (.onEnchanted action)
@[match_pattern] abbrev attachThen (followup : PermanentAction) : SharedTrigger := .permanent (.attachThen followup)

-- EventLeftover aliases
@[match_pattern] abbrev enter (e : EnterLeftover) : SharedTrigger := .leftover (.enter e)
@[match_pattern] abbrev step (e : StepLeftover) : SharedTrigger := .leftover (.step e)
@[match_pattern] abbrev death (e : DeathLeftover) : SharedTrigger := .leftover (.death e)
@[match_pattern] abbrev thisAttack (e : ThisAttackLeftover) : SharedTrigger := .leftover (.thisAttack e)
@[match_pattern] abbrev enterOrAttack (e : EnterOrAttackLeftover) : SharedTrigger := .leftover (.enterOrAttack e)
@[match_pattern] abbrev watch (e : WatchLeftover) : SharedTrigger := .leftover (.watch e)
@[match_pattern] abbrev youAttacking (e : YouAttackLeftover) : SharedTrigger := .leftover (.youAttacking e)
@[match_pattern] abbrev casting (e : CastLeftover) : SharedTrigger := .leftover (.casting e)
@[match_pattern] abbrev resource (e : ResourceLeftover) : SharedTrigger := .leftover (.resource e)

end SharedTrigger

/-- An intervening “if” clause (CR 603.4), checked when the
ability triggers and again as it resolves. -/
inductive InterveningCondition where
  | none
  /-- “if it isn't a token” (the source, as it last existed). -/
  | sourceNotToken
  /-- “if two or more creatures died this turn”. -/
  | twoCreaturesDiedThisTurn
  /-- “if an opponent was dealt noncombat damage last turn”. -/
  | opponentDealtNoncombatDamageLastTurn
  /-- “if you've drawn three or more cards this turn”. -/
  | drewThreeThisTurn
  /-- “if you didn't cast a spell this turn”. -/
  | castNoSpellThisTurn
  /-- “if you've activated a loyalty ability this turn”. -/
  | activatedLoyaltyThisTurn
  /-- “if you cast it”. -/
  | sourceWasCast
  /-- “if it had counters on it” (the object that caused the trigger). -/
  | causeHadCounters
  /-- “if this has counters on it”. -/
  | sourceHasCounters
deriving Repr, Inhabited, BEq, DecidableEq

/-- Backward-compatible alias for `InterveningCondition` (CR 603.4). -/
abbrev FraCondition := InterveningCondition


/-- Optional intervening conditions and wording filters for `triggered`. -/
structure SharedTriggerOpts where
  onceEachTurn : Bool := false
  youControlCreatureWithPower : Option Int := none
  thisOrNontokenSubtype : Option String := none
  thisOrAnotherSubtype : Option String := none
  anotherSubtypeOrEquipment : Option String := none
  gainedLifeAtLeast : Option Nat := none
  /-- Intervening “another creature you control with power ≤ n”. -/
  anotherCreaturePowerAtMost : Option Int := none
  allowsZeroTargets : Bool := false
  /-- Subtype watched by “whenever a {subtype} you control deals combat damage”. -/
  watchedSubtype : Option String := none
  /-- Drop targeting from the shared effect (e.g. Guttersnipe). -/
  untargeted : Bool := false
  /-- The ability's printed sentence, when its wording isn't built from the
  event and resolution (Reality Fracture). -/
  printed : String := ""
  /-- Reality Fracture intervening “if” clause. -/
  fraCondition : FraCondition := .none
  /-- The other permanent must be legendary (“another legendary Elf”). -/
  anotherLegendary : Bool := false
deriving Repr, Inhabited, BEq

/-- Ferocious intervening condition (power 4 or greater). -/
def SharedTriggerOpts.ferocious : SharedTriggerOpts :=
  { youControlCreatureWithPower := some 4 }

/-- “This ability triggers only once each turn.” -/
def SharedTriggerOpts.once : SharedTriggerOpts :=
  { onceEachTurn := true }

/-- Shared effect has targeting; this printed ability does not. -/
def SharedTriggerOpts.noTarget : SharedTriggerOpts :=
  { untargeted := true }

end Mtg.Engine
