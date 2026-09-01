import Mtg.Engine.Card.PermanentAction
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
  /-- This fights up to one other target creature. -/
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
  /-- You may sac an artifact or discard a nonland. When you do, 2 damage. -/
  | maySacOrDiscardNonlandThenDamage
  /-- Reveal the opponent's hand; exile a card or creature until this leaves. -/
  | revealHandExileUntilLeaves
  /-- +1/+1 on up to two creatures, or return an artifact/enchantment from GY. -/
  | plusOnesOrReturnArtEnch
  /-- Choose up to X modes. -/
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

/-- Leftover dies triggers that do not already match a more specific constructor. -/
inductive DeathLeftover where
  /-- When Hellcat dies, return her to the battlefield under her owner's control with a +1/+1 co… -/
  | hellcatReturn
  /-- Whenever a Villain you control dies, return it to the battlefield under its owner's contro… -/
  | villainReturnAsHero
  /-- Whenever an attacking creature you control dies, return that card to its owner's hand. -/
  | attackingReturnHand
  /-- Whenever another creature you control with deathtouch dies, each opponent sacrifices a non… -/
  | deathtouchOppSac
deriving Repr, Inhabited, BEq

/-- Leftover “whenever this attacks” (or attacks-alone) triggers. -/
inductive ThisAttackLeftover where
  /-- Whenever Ant-Man attacks, you may pay {1}. When you do, put a +1/+1 counter on target crea… -/
  | mayPayPlusOne
  /-- Whenever Grim Reaper attacks, you may pay {3}{B}. When you do, return target creature card… -/
  | payReturnAttacking
  /-- Whenever Iron Man attacks, if an artifact entered the battlefield under your control this … -/
  | ifArtifactEnteredDraw
  /-- Whenever The Mighty Thor attacks, exile up to one target nontoken artifact or creature, th… -/
  | blinkNontoken
  /-- Whenever Whiplash attacks, if he's equipped, each opponent loses X life and you gain X lif… -/
  | equippedDrain
  /-- Cybernetic Senses — Whenever Viv Vision attacks, draw a card if her power is 4 or greater. -/
  | drawIfPower4
  /-- Unbreakable Skin — Whenever Luke Cage attacks alone, he gets +2/+0 and gains indestructibl… -/
  | attacksAlonePlus2Indestructible
deriving Repr, Inhabited, BEq

/-- Leftover “enters or attacks” triggers. -/
inductive EnterOrAttackLeftover where
  /-- Whenever Super-Adaptoid enters or attacks, choose another target creature. If that creatur… -/
  | copyKeywords
  /-- Do You Like Squirrels? — Whenever The Unbeatable Squirrel Girl enters or attacks, create a… -/
  | createSquirrel
deriving Repr, Inhabited, BEq

/-- Leftover triggers that watch another event (another permanent, combat, tap, damage). -/
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

/-- Leftover draw, discard, life, and +1/+1-counter triggers. -/
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

/-- When a reusable triggered ability fires. Constructors that only differ by
this event (scry on enter vs attack, draw on die vs enter, …) share one
`TriggeredAbility.triggered` constructor. -/
inductive SharedTriggerWhen where
  /-- When this permanent enters. -/
  | enter
  /-- Whenever this creature attacks. -/
  | attack
  /-- When this creature dies. -/
  | dies
  /-- Whenever you attack. -/
  | youAttack
  /-- Whenever you attack with one or more Elves. -/
  | youAttackWithElves
  /-- Whenever you cast a spell of this color. -/
  | youCastColor (c : Color)
  /-- Whenever you cast a noncreature spell. -/
  | youCastNoncreature
  /-- Landfall — whenever a land you control enters. -/
  | landYouControlEnters
  /-- At the beginning of your upkeep. -/
  | yourUpkeep
  /-- At the beginning of your end step. -/
  | yourEndStep
  /-- At the beginning of combat on your turn. -/
  | yourBeginCombat
  /-- Whenever you draw your second card each turn. -/
  | youDrawSecond
  /-- Whenever the Ring tempts you. -/
  | theRingTemptsYou
  /-- Whenever you choose a creature as your Ring-bearer. -/
  | youChooseRingBearer
  /-- Whenever this becomes the target of a spell or ability an opponent controls. -/
  | becomesTarget
  /-- Whenever an artifact you control enters. -/
  | artifactYouControlEnters
  /-- Whenever this deals combat damage to a player. -/
  | combatDamageToPlayer
  /-- Whenever one or more other creatures die. -/
  | oneOrMoreOtherCreaturesDie
  /-- Whenever a creature card leaves your graveyard. -/
  | creatureCardLeavesYourGy
  /-- Whenever you draw a card. -/
  | youDraw
  /-- Whenever you gain life. -/
  | youGainLife
  /-- Whenever another artifact you control enters. -/
  | anotherArtifactEnters
  /-- Whenever this is dealt damage. -/
  | sourceDealtDamage
  /-- Whenever equipped creature attacks alone. -/
  | equippedAttacksAlone
  /-- Whenever you cast a spell that had Treasure mana spent. -/
  | youCastWithTreasure
  /-- Whenever you cast a spell of this color from your hand. -/
  | youCastColorFromHand (c : Color)
  /-- Whenever an equipped creature you control attacks. -/
  | equippedCreatureYouControlAttacks
  /-- Whenever another Elf you control enters. -/
  | anotherElfYouControlEnters
  /-- Whenever you activate an ability of a creature. -/
  | youActivateCreatureAbility
  /-- Whenever an opponent draws their second card each turn. -/
  | opponentDrawsSecond
  /-- Whenever an opponent casts their first noncreature spell each turn. -/
  | opponentCastsFirstNoncreature
  /-- At the beginning of each end step. -/
  | eachEndStep
  /-- Whenever this or another nontoken permanent of a listed subtype enters. -/
  | thisOrNontokenSubtypeEnters
  /-- Whenever this or another permanent of a listed subtype enters. -/
  | thisOrAnotherSubtypeEnters
  /-- Whenever another permanent of a listed subtype or an Equipment enters. -/
  | anotherSubtypeOrEquipmentEnters
  /-- Whenever this deals combat damage to a player or battle. -/
  | combatDamageToPlayerOrBattle
  /-- Whenever you cast a green spell. -/
  | youCastGreen
  /-- Whenever a Forest you control enters. -/
  | forestYouControlEnters
  /-- Whenever you cast an instant or sorcery spell. -/
  | youCastInstantOrSorcery
  /-- Whenever an Equipment you control enters. -/
  | equipmentYouControlEnters
  /-- Whenever another creature you control enters. -/
  | anotherCreatureYouControlEnters
  /-- Whenever another Goblin, Orc, or Army you control dies. -/
  | anotherGoblinOrcArmyDies
  /-- Whenever a creature you control attacks alone. -/
  | creatureYouControlAttacksAlone
  /-- Whenever an opponent casts a spell. -/
  | opponentCastsSpell
  /-- Whenever you scry. -/
  | youScry
  /-- Whenever this creature becomes blocked. -/
  | becomesBlocked
  /-- When this permanent leaves the battlefield. -/
  | leaving
  /-- Whenever two or more creatures you control attack a player. -/
  | youAttackWithTwoOrMore
  /-- Whenever you sacrifice a token. -/
  | youSacrificeToken
  /-- Whenever an Army you control deals combat damage to a player. -/
  | armyYouControlCombatDamage
  /-- At the beginning of your first main phase. -/
  | yourFirstMain
  /-- Whenever a player casts their second spell each turn. -/
  | anyPlayerCastsSecondSpell
  /-- At the beginning of each combat. -/
  | eachBeginCombat
  /-- Whenever you cast a creature spell. -/
  | youCastCreature
  /-- Whenever a Mountain you control enters. -/
  | mountainYouControlEnters
  /-- Whenever equipped creature deals combat damage to a player. -/
  | equippedDealsCombatDamageToPlayer
  /-- Whenever a nontoken creature you control dies. -/
  | nontokenYouControlDies
  /-- Whenever a player loses life. -/
  | playerLosesLife
  /-- Whenever you cast your second spell each turn. -/
  | youCastSecondSpell
  /-- Whenever equipped creature attacks. -/
  | equippedAttacks
  /-- Cascade on the spell being cast (no `TriggerEvent`; queued from cast). -/
  | cascade
  /-- Whenever a token you control enters. -/
  | tokenYouControlEnters
  /-- Reflexive trigger after Bolg's sacrifice. -/
  | bolgSacrificedForReflexive
  /-- Whenever an opponent draws except their first draw-step card. -/
  | opponentDrawsExceptFirst
  /-- Whenever you attack with creatures with total power at least a listed amount. -/
  | youAttackWithTotalPower
  /-- Delayed Eagles Bird Soldier trigger. -/
  | eaglesCreateBirds
  /-- Whenever an opponent casts a spell of the chosen parity. -/
  | opponentCastsMatchingParity
  /-- Whenever you put counters on a Goblin, Orc, or Army. -/
  | youPutCountersOnGoblinOrcArmy
  /-- Whenever this is dealt noncombat damage. -/
  | sourceDealtNoncombatDamage
  /-- Whenever the final chapter of a Saga you control resolves. -/
  | finalSagaChapterResolves
  /-- Whenever one or more creatures deal combat damage to you. -/
  | combatDamageToYou
  /-- A Saga chapter ability. -/
  | sagaChapter
  /-- Whenever this becomes tapped to pay a teamwork cost. -/
  | tappedForTeamwork
  /-- Whenever a creature you control enters. -/
  | creatureYouControlEnters
  /-- Whenever one or more creatures you control become tapped. -/
  | creaturesYouControlBecomeTapped
  /-- Whenever a permanent of this subtype you control enters. -/
  | subtypeYouControlEnters (subtype : String)
  /-- Whenever one or more creature cards are put into your graveyard. -/
  | creatureCardsPutIntoYourGy
  /-- When the `n`th plan counter is put on this. -/
  | nthPlanCounter (n : Nat)
  /-- Triggers when at least one of the two given conditions triggers. -/
  | or (a b : SharedTriggerWhen)
  /-- Use the events stored on the shared effect (leftover family wrappers). -/
  | fromEffect
deriving Repr, Inhabited, BEq

/-- Shared resolution for reusable triggered abilities that only differ by
when they fire. `TriggeredAbility.triggered` pairs this with `SharedTriggerWhen`. -/
inductive SharedTrigger where
  /-- Scry `n`. -/
  | scry (n : Nat)
  /-- Draw `n` cards. -/
  | draw (n : Nat)
  /-- Create `n` tokens of this kind. `tapped` is Treasure-style “create a tapped …”. -/
  | createTokens (kind : TokenKind) (n : Nat) (tapped : Bool := false)
  /-- Amass Goblins `n`. -/
  | amassGoblins (n : Nat)
  /-- Recruit. -/
  | recruit
  /-- You recruit. -/
  | youRecruit
  /-- Deal `amount` damage divided as you choose among one to `maxTargets` targets. -/
  | dividedDamage (amount maxTargets : Nat)
  /-- Put a +1/+1 counter on a target of this kind. -/
  | plusOneOn (kind : EffectTargetKind)
  /-- Put a +1/+1 counter on the source. -/
  | plusOneOnSource
  /-- The source gets +P/+T until end of turn. -/
  | sourceGets (power toughness : Int)
  /-- Target of this kind gets +P/+T until end of turn. -/
  | pumpTarget (kind : EffectTargetKind) (power toughness : Int)
  /-- You gain `n` life. -/
  | gainLife (n : Nat)
  /-- Draw a card and lose 1 life. -/
  | drawAndLoseLife
  /-- The source connives. -/
  | connive
  /-- A target of this kind connives. -/
  | conniveTarget (kind : EffectTargetKind)
  /-- Exile a target of this kind until the source leaves. -/
  | exileUntilLeaves (kind : EffectTargetKind)
  /-- Deal `n` damage to each opponent (optionally after targeting one). -/
  | damageEachOpponent (n : Nat)
  /-- Attach this Equipment to a target of this kind. -/
  | attachTo (kind : EffectTargetKind)
  /-- Target opponent sacrifices a creature of their choice. -/
  | opponentSacrificesCreature
  /-- Affect a still-legal permanent target. -/
  | onPermanent (kind : EffectTargetKind) (action : PermanentAction)
  /-- Affect the trigger's source if it is still on the battlefield. -/
  | onSource (action : PermanentAction)
  /-- Exile the top card; you may play it until the end of your next turn. -/
  | exileTop
  /-- You may discard a card. If you do, draw `n`. -/
  | mayDiscardDraw (n : Nat)
  /-- Each opponent discards a card. -/
  | eachOpponentDiscards
  /-- Target opponent discards `n` cards. -/
  | targetOpponentDiscards (n : Nat)
  /-- Target player mills `n` cards. -/
  | millPlayer (n : Nat)
  /-- Amass Orcs `n`. -/
  | amassOrcs (n : Nat)
  /-- Investigate (create a Clue). -/
  | investigate
  /-- The attacking creature that caused this trigger gets +P/+T. -/
  | pumpCause (power toughness : Int)
  /-- Search the library for a Forest card. -/
  | searchForest
  /-- Search for a basic land and put it into hand. -/
  | searchBasicToHand
  /-- Each player sacrifices a creature of their choice. -/
  | eachPlayerSacrificesCreature
  /-- Exile a target of this kind. -/
  | exileTarget (kind : EffectTargetKind)
  /-- Return a creature card from your graveyard to your hand. -/
  | returnCreatureFromGyToHand
  /-- Draw a card, then discard a card. -/
  | loot
  /-- Put a +1/+1 counter on each creature you control. -/
  | plusOneEachYouControl
  /-- The source gets +P/+0 and creatures you control gain trample. -/
  | sourceGetsAndTeamTrample (power : Int)
  /-- Put a hone counter on each Equipment you control. -/
  | honeEachEquipment
  /-- +1/+1 on each other creature you control; gain that much life. -/
  | plusOneEachOtherGainLife
  /-- Set the source's base P/T. -/
  | becomePT (power toughness : Int)
  /-- Pump the source +1/+1 and deal `n` to each opponent. -/
  | pumpAndDamageOpponents (n : Nat)
  /-- +1/+1 and lifelink on a target of this kind. -/
  | plusOneAndLifelink (kind : EffectTargetKind)
  /-- Pump a target creature you control +1/+1 per Plains. -/
  | pumpTargetPerPlains
  /-- Draw `n` cards, then discard a card. -/
  | drawThenDiscard (n : Nat)
  /-- You may discard your hand. If you do, draw `n`. -/
  | mayDiscardHandDraw (n : Nat)
  /-- Pump the source +1/+1 per card looked at while scrying. -/
  | pumpByLookedAt
  /-- Pump the source +1/+0 and grant can't be blocked this turn. -/
  | pumpAndUnblockable
  /-- Pump the source by the greatest power among creatures you control. -/
  | pumpGreatestPower
  /-- Pump the source +1/+1 for each other creature you control. -/
  | pumpForEachOtherCreature
  /-- Deal `n` damage to each creature blocking the source. -/
  | damageBlockers (n : Nat)
  /-- Grant flying to a target of this kind. -/
  | grantFlying (kind : EffectTargetKind)
  /-- Return cards exiled by the source. -/
  | returnLinkedExile
  /-- Create a token, then attach the source to it. -/
  | createThenAttach (kind : TokenKind)
  /-- Amass Goblins `n`, then attach the source to the Army. -/
  | amassThenAttach (n : Nat)
  /-- Gain `n` life, then search a basic land to the top. -/
  | gainLifeSearchBasicOnTop (n : Nat)
  /-- Add these mana types. -/
  | addMana (types : Array ManaType)
  /-- Create an Axe Equipment token. -/
  | createAxe
  /-- Create an Axe and attach it to a creature you control. -/
  | createAxeAttach
  /-- Tap an opposing creature or untap yours. -/
  | tapOppOrUntapYours
  /-- Gain control of the target until end of turn; untap; haste. -/
  | gainControlOppUntilEot
  /-- Amass Goblins X, where X is this creature's power. -/
  | amassGoblinsEqualPower
  /-- Landfall from the graveyard: pay to return this to hand. -/
  | payReturnFromGy
  /-- Target opponent loses `n` life. -/
  | targetOpponentLosesLife (n : Nat)
  /-- Put `n` +1/+1 counters on a target and grant vigilance. -/
  | plusOneVigilance (n : Nat)
  /-- You may draw X cards, then discard two. -/
  | mayDrawXDiscard2
  /-- Draw a card and put a +1/+1 counter on the source. -/
  | drawPlusOneSource
  /-- The Ring tempts you. -/
  | ringTempts
  /-- Set another creature's base P/T to this creature's. -/
  | setOtherBasePT
  /-- Return a target Elf from the graveyard; gain life equal to its power. -/
  | returnElfGainLife
  /-- Deal damage equal to last-known power to a target. -/
  | damageFromLastKnownPower
  /-- Exile a card from an opponent's graveyard; each opponent loses `life`. -/
  | exileOppGyCardOppsLoseLife (life : Nat)
  /-- Creatures you control get +P/+0 and first strike. -/
  | creaturesYouControlPumpAndFirstStrike (power : Int)
  /-- You may pay `{generic}`. If you do, draw a card. -/
  | mayPayGenericDraw (generic : Nat)
  /-- Draw, then bottom a card if you don't control a legendary creature. -/
  | drawThenBottomIfNoLegendary
  /-- Remove a hope counter to draw; sacrifice if none remain. -/
  | removeHopeDrawSac
  /-- Tap any number of Humans; draw that many cards. -/
  | tapHumansDraw
  /-- Untap another creature; +1/+1 if it has this subtype. -/
  | untapPlusOneIfSubtype (subtype : String)
  /-- Destroy opponents' artifacts and enchantments; gain life for each. -/
  | destroyOppArtifactsEnchantmentsGainLife
  /-- Damage each opponent equal to permanents of this subtype you control. -/
  | damageEqualSubtypeToEachOpponent (subtype : String)
  /-- Damage any target equal to Treasures you control. -/
  | damageEqualTreasures
  /-- Lose 1 life and create a Treasure. -/
  | loseLifeCreateTreasure
  /-- Deal `n` to any target; destroy it if it has this subtype. -/
  | dealDamageDestroyIfSubtype (n : Nat) (subtype : String)
  /-- Attach target Equipment to up to one target creature you control. -/
  | attachEquipmentToCreature
  /-- Defending player sacrifices a least-power creature. -/
  | defenderSacsLeastPower
  /-- Return another permanent; put a +1/+1 counter on this. -/
  | returnOtherPlusOne
  /-- Look at the top `n` cards; you may reveal one of these types. -/
  | lookAtTopRevealTypes (n : Nat) (types : Array String)
  /-- Create tapped Treasures equal to artifacts opponents control. -/
  | createTappedTreasuresEqualOppArtifacts
  /-- Put a nonland with mana value `mv` or less from a graveyard onto the battlefield. -/
  | putNonlandMvAtMostFromGy (mv : Nat)
  /-- Other matching creatures get +P/+T; opposing creatures get +oppP/+oppT. -/
  | othersGetAndOppsGet (subtypes : Array String) (power toughness oppP oppT : Int)
  /-- +1/+1 on a Wolf or create a Treasure. -/
  | wolfPlusOneOrTreasure
  /-- Trample counter, become a Bear, maybe draw. -/
  | trampleCounterBecomeBear
  /-- Mill `n`, then put matching subtype cards into hand. -/
  | millThenSubtypeToHand (n : Nat) (subtype : String)
  /-- Exile up to one opposing nonland per opponent until this leaves. -/
  | exileOppNonlandEachUntilLeaves
  /-- +X/+X counters equal to the last-known mana value. -/
  | plusOneEqualLastKnownMv
  /-- Quest, then maybe find a Dragon. -/
  | mountainQuestDragon
  /-- Treasures per chosen creature type. -/
  | treasuresPerChosenType
  /-- Reveal until a creature and put it in if cheap enough. -/
  | revealUntilCreature
  /-- You may sacrifice another creature for +1/+1s equal to its power. -/
  | attackSacPlusOneEqualPower
  /-- Loot; a discarded land enters tapped. -/
  | lootLandEntersTapped
  /-- That player mills that many cards. -/
  | millThatManyLost
  /-- Draw a card for each fat graveyard. -/
  | drawPerFatGraveyard
  /-- You may sacrifice another for a card and a Treasure. -/
  | maySacDrawTreasure
  /-- +1/+1 each, or two with the city's blessing. -/
  | plusOneEachIfCityBlessing
  /-- You may cast an instant or sorcery from hand. -/
  | castInstantSorceryFromHand
  /-- You may cast an instant or sorcery with mana value at most that damage. -/
  | castInstantSorceryMvAtMost
  /-- Mill, then maybe copy a milled spell. -/
  | millThenCopy
  /-- Another creature gets +X/+0 equal to this creature's power. -/
  | pumpTargetBySourcePower
  /-- Create an Alien and grow it from invasion counters. -/
  | createAlienPerInvasion
  /-- You may put an artifact from hand; attach if Equipment. -/
  | mayPutArtifactAttachEquipment
  /-- Cascade. -/
  | cascade
  /-- Belladonna token-enter reward. -/
  | belladonnaTokenReward
  /-- Bolg may-sacrifice. -/
  | bolgMaySacrifice
  /-- Bolg reflexive damage. -/
  | bolgDealSacrificedPower
  /-- Create Spirits for equipped creature. -/
  | createSpiritsForEquipped
  /-- Treasures equal to the damaged player's artifacts. -/
  | createTreasuresEqualDamagedPlayerArtifacts
  /-- Deal 1 then amass Orcs 1. -/
  | deal1ThenAmassOrcs
  /-- Untap attackers and take an extra combat. `n` is Oracle total power. -/
  | untapAttackersExtraCombat (n : Int)
  /-- Delayed Eagles Bird Soldiers. -/
  | eaglesCreateBirds
  /-- Alliance modes. -/
  | allianceMode
  /-- Destroy another; its controller amasses equal to its power. -/
  | destroyOtherAmassControllerPower
  /-- Gollum parity modes. -/
  | gollumMode
  /-- Discard hand, draw that many; damage if enduring story. -/
  | discardHandDrawDamageIfStory
  /-- Cast artifact, instant, or sorcery from the graveyard. -/
  | castFromGyArtifactInstantSorcery
  /-- Equipped attackers gain double strike. -/
  | equippedAttackersGainDoubleStrike
  /-- Tap enchanted creature and remove counters. -/
  | tapEnchantedRemoveCounters
  /-- Reveal the top `n` and put a random creature in. -/
  | revealTopPutRandomCreature (n : Nat)
  /-- If you drew two or more, pump and first strike. -/
  | beginCombatIfDrawnTwoPump
  /-- Hone per opposing creatures and attach. -/
  | honePerOppAttach
  /-- Deal `n` to target opponent. -/
  | damageTargetOpponent (n : Nat)
  /-- If not a token, create nonlegendary copies. -/
  | copySelfNonlegendary
  /-- Attach Equipment, then the host fights. -/
  | attachEquipmentThenFight
  /-- Return as an artifact. -/
  | returnAsArtifact
  /-- Exile lands, then return them tapped. -/
  | exileLandsThenReturnTapped
  /-- Gríma impulse. -/
  | grimaImpulse
  /-- Palantír end-step. -/
  | palantir
  /-- Create Treasures equal to last-known noncombat damage. -/
  | treasuresEqualLastKnown
  /-- If you cast it, protection from everything. -/
  | protectionEverything
  /-- Lose 1 life per burden counter. -/
  | loseLifePerBurden
  /-- Reveal until a Saga. -/
  | revealSaga
  /-- Opponents sac damagers; the Ring tempts you. -/
  | sacDamagersRingTempts
  /-- A Saga chapter. -/
  | chapter (n : Nat) (e : ChapterResolution)
  /-- +1/+1 on this and draw. -/
  | plusOneOnSourceAndDraw
  /-- Draw if you attacked with or a subtype entered. -/
  | drawIfAttackedOrEnteredSubtype (subtype : String)
  /-- Other permanents of this subtype get +X/+X equal to this toughness. -/
  | othersOfSubtypeGetEqualSourceToughness (subtype : String)
  /-- Scry `n` and put a plan counter. -/
  | scryAndPlan (n : Nat)
  /-- Loot and put a plan counter. -/
  | lootAndPlan
  /-- Create a Villain and a plan counter. -/
  | createVillainAndPlan
  /-- Drain `n` and put a plan counter. -/
  | drainAndPlan (n : Nat)
  /-- Draw, lose life, and put a plan counter. -/
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
  /-- Surveil `n` (resolves as a scry-shaped look). -/
  | surveil (n : Nat)
  /-- Apply `action` to the enchanted creature. -/
  | onEnchanted (action : PermanentAction)
  /-- Attach to target, then apply `followup`. -/
  | attachThen (followup : PermanentAction)
  /-- Exile another creature; enchanted becomes a copy. -/
  | exileOtherCopyEnchanted
  /-- Exile a creature you control until the next end step. -/
  | exileUntilNextEndStep
  /-- Tap or untap target nonland. -/
  | tapOrUntapNonland
  /-- Create a Food or a Treasure. -/
  | createFoodOrTreasure
  /-- Villain if two creature cards in gy; otherwise mill two. -/
  | villainIfGyElseMill
  /-- Draw, then you may put a land from hand tapped. -/
  | drawMayPutLandTapped
  /-- Draw; if you control another Hero, gain 2 life. -/
  | drawGainLifeIfAnotherHero
  /-- +1/+1, or two if that creature is another Hero. -/
  | plusOneOrTwoIfAnotherHero
  /-- You may sac an artifact or discard; if you do, draw. -/
  | maySacArtifactOrDiscardDraw
  /-- Leftover “when this enters” effect. -/
  | enter (e : EnterLeftover)
  /-- Leftover step / upkeep / end-step / first-main effect. -/
  | step (e : StepLeftover)
  /-- Leftover dies effect. -/
  | death (e : DeathLeftover)
  /-- Leftover “whenever this attacks” effect. -/
  | thisAttack (e : ThisAttackLeftover)
  /-- Leftover “enters or attacks” effect. -/
  | enterOrAttack (e : EnterOrAttackLeftover)
  /-- Leftover watch effect. -/
  | watch (e : WatchLeftover)
  /-- Leftover “whenever you attack” effect. -/
  | youAttacking (e : YouAttackLeftover)
  /-- Leftover “whenever you cast …” effect. -/
  | casting (e : CastLeftover)
  /-- Leftover draw / discard / life / +1/+1-counter effect. -/
  | resource (e : ResourceLeftover)
deriving Repr, Inhabited, BEq

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
