import Mtg.Engine.Card.Effect
import Mtg.Engine.Card.TriggerEvent

/-!
# Triggered-ability core (CR 603)

The unified `TriggeredAbility` carrier plus its stack/resolution metadata:
`TriggerResolution`, `TriggerTiming`, the events each shared trigger
watches, and the timing of each shared trigger.
-/

namespace Mtg.Engine

/-- A triggered ability the engine currently understands (CR 603).
One constructor keeps the C runtime tag under the limit; leftover printed
names are aliases of `triggered`. -/
inductive TriggeredAbility where
  /-- Reusable trigger: when it fires, a unified `Effect`, and optional
  intervening conditions / wording filters. -/
  | triggered (when : SharedTriggerWhen) (effect : Effect)
      (opts : SharedTriggerOpts := {})
deriving Repr, Inhabited, BEq

namespace TriggeredAbility

/-- English for “divided as you choose among …” (CR 601.2d). -/
def dividedAmong (maxTargets : Nat) : String :=
  if maxTargets == 3 then "one, two, or three targets"
  else if maxTargets == 1 then "one target"
  else s!"up to {maxTargets} targets"

/-- How a triggered ability selects targets when it is put on the stack
(CR 603.3d / 601.2c). Spell and activated-ability targeting use the same
`EffectTargetKind` constructors. -/
abbrev TriggerTargetKind := EffectTargetKind

/-- What a triggered ability does when it resolves (CR 608). Grouped so
`Game.applyTriggeredAbility` matches resolution shapes instead of every
constructor: scry, +1/+1 on the source, and divided damage each cover
multiple printed abilities. Permanent-target counters and pumps, and source
pumps, share `PermanentAction` with spells and activated abilities. -/
inductive TriggerResolution where
  /-- Pump the source by the greatest power among creatures you control. -/
  | pumpGreatestPower
  /-- Set another creature's base P/T to this creature's. -/
  | setOtherBasePT
  /-- Deal `amount` damage to each creature blocking the source. -/
  | damageBlockers (amount : Nat)
  /-- Scry `n`. -/
  | scry (n : Nat)
  /-- Draw `n` cards. -/
  | draw (n : Nat)
  /-- Search the library for a Forest card. -/
  | searchForest
  /-- You may discard a card. If you do, draw `n`. -/
  | mayDiscardDraw (n : Nat)
  /-- Target opponent sacrifices a creature of their choice. -/
  | opponentSacrificesCreature
  /-- Affect a still-legal permanent target. -/
  | onPermanent (action : PermanentAction)
  /-- Deal previously divided damage to the announced targets. -/
  | dividedDamage
  /-- Deal last-known power as damage to the announced creature. -/
  | damageFromLastKnownPower
  /-- Return an Elf card from the graveyard and gain life equal to its power. -/
  | returnElfGainLife
  /-- Deal `amount` damage to each opponent. -/
  | damageEachOpponent (amount : Nat)
  /-- Pump the source +1/+1 per card looked at while scrying. -/
  | pumpByLookedAt
  /-- Affect the trigger's source if it is still on the battlefield. -/
  | onSource (action : PermanentAction)
  /-- You gain `n` life (CR 118.2). -/
  | gainLife (n : Nat)
  /-- Each player sacrifices a creature of their choice. -/
  | eachPlayerSacrificesCreature
  /-- Each opponent discards a card. -/
  | eachOpponentDiscards
  /-- Exile up to one targeted card from an opponent's graveyard, then each
  opponent loses `life` life. -/
  | exileOppGyCardOppsLoseLife (life : Nat)
  /-- Creatures you control get +P/+0 and first strike until end of turn. -/
  | creaturesYouControlPumpAndFirstStrike (power : Int)
  /-- Pump the source +1/+1 for each other creature you control. -/
  | pumpForEachOtherCreature
  /-- Grant flying until end of turn to the targeted creature. -/
  | grantFlying
  /-- You may pay `{generic}`. If you do, draw a card. -/
  | mayPayGenericDraw (generic : Nat)
  /-- Draw a card, then put a card on the bottom if you control no legendary. -/
  | drawThenBottomIfNoLegendary
  /-- Exile the targeted permanent. Link it if the source is still in play. -/
  | exileTarget
  /-- Exile the targeted permanent until the source leaves the battlefield. -/
  | exileUntilLeaves
  /-- Return cards exiled by the source. -/
  | returnLinkedExile
  /-- Remove a hope counter, draw, then maybe sacrifice and gain life. -/
  | removeHopeDrawSac
  /-- Draw a card, then discard a card. -/
  | loot
  /-- Tap any number of Humans you control; draw that many cards. -/
  | tapHumansDraw
  /-- Pump the source +1/+0 and grant can't be blocked this turn. -/
  | pumpAndUnblockable
  /-- Recruit. -/
  | recruit
  /-- You recruit. -/
  | youRecruit
  /-- Exile the top card; you may play it until the end of your next turn. -/
  | exileTop
  /-- Untap the target; if it has this subtype, put a +1/+1 counter on it. -/
  | untapPlusOneIfSubtype (subtype : String)
  /-- Put a +1/+1 counter on each creature you control. -/
  | plusOneEachYouControl
  /-- Pump the source +P/+0 and grant trample to creatures you control. -/
  | sourceGetsAndTeamTrample (power : Int)
  /-- Draw a card and lose 1 life. -/
  | drawAndLoseLife
  /-- Amass Goblins `n`. -/
  | amassGoblins (n : Nat)
  /-- Create `n` tokens of this kind. -/
  | createTokens (kind : TokenKind) (n : Nat) (tapped : Bool)
  /-- Create a token, then attach the source to it. -/
  | createThenAttach (kind : TokenKind)
  /-- Amass Goblins `n`, then attach the source to the Army. -/
  | amassThenAttach (n : Nat)
  /-- Attach the source to the targeted permanent. -/
  | attachSourceToTarget
  /-- Search for a basic land and put it into hand. -/
  | searchBasicToHand
  /-- Gain `n` life, then search a basic land to the top. -/
  | gainLifeSearchBasicOnTop (n : Nat)
  /-- +1/+1 on each other creature you control; gain that much life. -/
  | plusOneEachOtherGainLife
  /-- Destroy opponents' artifacts and enchantments; gain 1 per destroyed. -/
  | destroyOppArtifactsEnchantmentsGainLife
  /-- Deal damage equal to the count of this subtype you control to each
  opponent. -/
  | damageEqualSubtypeToEachOpponent (subtype : String)
  /-- Deal damage equal to Treasures you control to the target. -/
  | damageEqualTreasures
  /-- Lose 1 life and create a Treasure. -/
  | loseLifeCreateTreasure
  /-- Deal `n` damage to the target; destroy it if it has this subtype. -/
  | dealDamageDestroyIfSubtype (n : Nat) (subtype : String)
  /-- Attach the first target (Equipment) to the second (creature). -/
  | attachEquipmentToCreature
  /-- Add these mana types. -/
  | addMana (types : Array ManaType)
  /-- Defending player sacrifices a least-power creature. -/
  | defenderSacsLeastPower
  /-- Create an Axe Equipment token. -/
  | createAxe
  /-- Tap an opposing creature or untap yours. -/
  | tapOppOrUntapYours
  /-- Set the source's base P/T. -/
  | becomePT (power toughness : Int)
  /-- Return another permanent you control; if you do, +1 on the source. -/
  | returnOtherPlusOne
  /-- Look at the top `n` and reveal a listed type. -/
  | lookAtTopRevealTypes (n : Nat) (types : Array String)
  /-- Pump the source +1/+1 and deal `n` to each opponent. -/
  | pumpAndDamageOpponents (n : Nat)
  /-- Create tapped Treasures equal to opposing artifacts. -/
  | createTappedTreasuresEqualOppArtifacts
  /-- Gain control of the target until end of turn; untap; haste. -/
  | gainControlOppUntilEot
  /-- Other matching creatures get +P/+T; opposing creatures get +oppP/+oppT. -/
  | othersGetAndOppsGet (subtypes : Array String) (power toughness oppP oppT : Int)
  /-- Put a nonland permanent card with mana value at most `mv` from a
  graveyard onto the battlefield. -/
  | putNonlandMvAtMostFromGy (mv : Nat)
  /-- Put a hone counter on each Equipment you control. -/
  | honeEachEquipment
  /-- Cascade: exile until a cheaper nonland, then you may cast it. -/
  | cascade
  /-- First resolve: gain 1 life. Second: draw. Third: +1/+1 each creature.
  Later resolves this turn do nothing (Belladonna Took). -/
  | belladonnaTokenReward
  /-- You may sacrifice another creature you control (Bolg). -/
  | bolgMaySacrifice
  /-- Deal last-known sacrificed power to the target; amass Goblins equal to
  excess damage. -/
  | bolgDealSacrificedPower
  /-- Create two tapped Spirits; they enter attacking if the equipped
  creature is legendary and you control it. -/
  | createSpiritsForEquipped
  /-- Create a Treasure for each artifact the damaged player controls. -/
  | createTreasuresEqualDamagedPlayerArtifacts
  /-- Deal 1 damage to any target, then amass Orcs 1. -/
  | deal1ThenAmassOrcs
  /-- Untap attacking creatures; an additional combat phase follows. -/
  | untapAttackersExtraCombat
  /-- Create Bird Soldier tokens equal to last-known count. -/
  | eaglesCreateBirds
  /-- Apply an unused Alliance mode, or do nothing if all were chosen. -/
  | allianceMode
  /-- Destroy the targeted creature if any; that controller amasses equal
  to last-known power. No target means no player amasses. -/
  | destroyOtherAmassControllerPower
  /-- Apply an unused Gollum mode, or do nothing if all were chosen. -/
  | gollumMode
  /-- Return a creature card from your graveyard to your hand. -/
  | returnCreatureFromGyToHand
  /-- Discard your hand, draw that many, and maybe damage opponents. -/
  | discardHandDrawDamageIfStory
  /-- +1/+1 and lifelink on the targeted creature. -/
  | plusOneAndLifelink
  /-- +1/+1 on a Wolf you control, or create a Treasure. -/
  | wolfPlusOneOrTreasure
  /-- Trample counter, become a Bear, maybe draw two. -/
  | trampleCounterBecomeBear
  /-- You may cast an artifact, instant, or sorcery from your graveyard. -/
  | castFromGyArtifactInstantSorcery
  /-- Mill `n`, then put cards of this subtype into hand. -/
  | millThenSubtypeToHand (n : Nat) (subtype : String)
  /-- Exile up to one opposing nonland per opponent until this leaves. -/
  | exileOppNonlandEachUntilLeaves
  /-- +1/+1 counters equal to the last-known mana value. -/
  | plusOneEqualLastKnownMv
  /-- Create an Axe and attach it to a creature you control. -/
  | createAxeAttach
  /-- Equipped attacking creatures gain double strike. -/
  | equippedAttackersGainDoubleStrike
  /-- Tap the enchanted creature and remove its counters. -/
  | tapEnchantedRemoveCounters
  /-- Reveal the top `n`; put a random creature onto the battlefield. -/
  | revealTopPutRandomCreature (n : Nat)
  /-- If you drew two or more, pump and first strike. -/
  | beginCombatIfDrawnTwoPump
  /-- Quest counter; at six, sacrifice and find a Dragon. -/
  | mountainQuestDragon
  /-- Target player mills `n`. -/
  | millPlayer (n : Nat)
  /-- Treasures equal to permanents of a chosen type. -/
  | treasuresPerChosenType
  /-- Reveal until a creature; put it onto the battlefield or into hand. -/
  | revealUntilCreature
  /-- You may sacrifice another creature for +1/+1s equal to its power. -/
  | attackSacPlusOneEqualPower
  /-- Amass Goblins equal to last-known power. -/
  | amassGoblinsEqualPower
  /-- You may pay to return this from the graveyard to your hand. -/
  | payReturnFromGy
  /-- Draw, discard; a discarded land enters tapped. -/
  | lootLandEntersTapped
  /-- Hone per opposing creatures, then attach. -/
  | honePerOppAttach
  /-- Deal 2 to target opponent. -/
  | damageTargetOpponent (n : Nat)
  /-- Each player who lost life mills that much. -/
  | millThatManyLost
  /-- Draw per graveyard with seven or more cards. -/
  | drawPerFatGraveyard
  /-- Create two nonlegendary token copies of the source. -/
  | copySelfNonlegendary
  /-- You may sacrifice another for a card and a Treasure. -/
  | maySacDrawTreasure
  /-- Target opponent loses 1 life. -/
  | targetOpponentLosesLife (n : Nat)
  /-- Attach any number of Equipment, then the host fights. -/
  | attachEquipmentThenFight
  /-- Two +1/+1 counters and vigilance. -/
  | plusOneVigilance (n : Nat)
  /-- Draw two, then discard a card. -/
  | drawThenDiscardN (n : Nat)
  /-- Return the source as an artifact. -/
  | returnAsArtifact
  /-- You may draw X (mana spent), then discard two. -/
  | mayDrawXDiscard2
  /-- +1/+1 each, or two with the city's blessing. -/
  | plusOneEachIfCityBlessing
  /-- You may cast an instant or sorcery from hand without paying. -/
  | castInstantSorceryFromHand
  /-- Draw a card and put a +1/+1 counter on the source. -/
  | drawPlusOneSource
  /-- Exile up to three lands you control, then return them tapped. -/
  | exileLandsThenReturnTapped
  /-- You may cast an instant or sorcery of MV at most last-known power. -/
  | castInstantSorceryMvAtMost
  /-- Exile until an instant or sorcery; you may cast it. -/
  | grimaImpulse
  /-- Palantír of Orthanc. -/
  | palantir
  /-- Each opponent mills two; then maybe copy a card. -/
  | millThenCopy
  /-- Amass Orcs `n`. -/
  | amassOrcs (n : Nat)
  /-- The Ring tempts you. -/
  | ringTempts
  /-- You may discard your hand and draw `n`. -/
  | mayDiscardHandDraw (n : Nat)
  /-- Create Treasures equal to last-known damage. -/
  | treasuresEqualLastKnown
  /-- You gain protection from everything until your next turn. -/
  | protectionEverything
  /-- Lose 1 life per burden counter. -/
  | loseLifePerBurden
  /-- Reveal until a Saga and put it onto the battlefield. -/
  | revealSaga
  /-- Each opponent sacrifices a creature that damaged you; the Ring tempts you. -/
  | sacDamagersRingTempts
  /-- Resolve a printed Saga chapter. -/
  | chapter (effect : ChapterResolution)
  /-- Target creature you control gets +1/+1 per Plains you control. -/
  | pumpTargetPerPlains
  /-- Investigate (create a Clue). -/
  | investigate
  /-- Put a +1/+1 counter on the source and draw a card. -/
  | plusOneOnSourceAndDraw
  /-- The source connives (CR 701.48). -/
  | connive
  /-- The targeted creature connives. -/
  | targetConnive
  /-- Pump the creature that caused the trigger. -/
  | pumpCause (power toughness : Int)
  /-- Other permanents you control of this subtype get +X/+X, X = source toughness. -/
  | othersOfSubtypeGetEqualSourceToughness (subtype : String)
  /-- Draw a card if you attacked with this subtype or one entered this turn. -/
  | drawIfAttackedOrEnteredSubtype (subtype : String)
  /-- Scry `n` and put a plan counter on the source. -/
  | scryAndPlan (n : Nat)
  /-- Draw, discard, and put a plan counter on the source. -/
  | lootAndPlan
  /-- Create a Villain token and put a plan counter on the source. -/
  | createVillainAndPlan
  /-- Each opponent loses `n` life, you gain `n`, and put a plan counter. -/
  | drainAndPlan (n : Nat)
  /-- Draw a card, lose 1 life, and put a plan counter. -/
  | drawLoseLifeAndPlan
  /-- Create a tapped Treasure and put a plan counter. -/
  | treasureTappedAndPlan
  /-- Put a +1/+1 counter on the target and a plan counter on the source. -/
  | plusOneOnTargetAndPlan
  /-- Sacrifice this, draw a card, and put a +1/+1 counter on each creature. -/
  | planFinishDrawPlusOneEach
  /-- Sacrifice this. Return up to two instant/sorcery cards from your graveyard. -/
  | planFinishReturnInstants
  /-- Sacrifice this. You control target opponent during their next turn. -/
  | planFinishControlOpponent
  /-- Sacrifice this. Exile the top five; you may cast up to two without paying. -/
  | planFinishExileTopCast
  /-- Sacrifice this and create `n` Robot Villain tokens. -/
  | planFinishCreateRobots (n : Nat)
  /-- Sacrifice this. Deal `amount` divided among one or two targets. -/
  | planFinishDividedDamage (amount : Nat)
  /-- Sacrifice this. Put an indestructible counter on target creature you control. -/
  | planFinishIndestructibleOnTarget
  /-- Draw a card and lose 1 life. -/
  | drawAndLoseLife1
  /-- Apply `action` to the creature this Aura enchants. -/
  | onEnchanted (action : PermanentAction)
  /-- Attach the source to the target, then apply `action` to that host. -/
  | attachThen (action : PermanentAction)
  /-- Exile the targeted creature until this leaves; enchanted becomes a copy. -/
  | exileOtherCopyEnchanted
  /-- Exile the targeted creature; return it at the next end step. -/
  | exileUntilNextEndStep
  /-- Choose tap or untap for the targeted nonland. -/
  | tapOrUntapNonland
  /-- Create a Food token or a Treasure token. -/
  | createFoodOrTreasure
  /-- Tapped 2/1 menace Villain if ≥2 creature cards in GY; otherwise mill 2. -/
  | villainIfGyElseMill
  /-- Draw, then you may put a land from hand onto the battlefield tapped. -/
  | drawMayPutLandTapped
  /-- Draw. If you control another Hero, gain 2 life. -/
  | drawGainLifeIfAnotherHero
  /-- +1/+1 on the target; two if that creature is another Hero. -/
  | plusOneOrTwoIfAnotherHero
  /-- You may sacrifice an artifact or discard a card. If you do, draw. -/
  | maySacArtifactOrDiscardDraw
  /-- Target opponent discards `n` cards. -/
  | targetOpponentDiscards (n : Nat)
  /-- Another target creature gets +X/+0, X = source power. -/
  | pumpTargetBySourcePower
  /-- Create an Alien token, put +1/+1s for each invasion counter, then
  put an invasion counter on the source. -/
  | createAlienPerInvasion
  /-- You may put an artifact from your hand onto the battlefield; attach
  it if it is Equipment. -/
  | mayPutArtifactAttachEquipment
  /-- This fights the targeted creature. -/
  | fightUpToOne
  /-- Return the targeted permanent to its owner's hand. -/
  | returnToOwnerHand
  /-- Create Zabu. -/
  | createZabu
  /-- Target opponent creates The Void. -/
  | oppCreatesTheVoid
  /-- Create Sturdy Shield and attach it to the source. -/
  | createSturdyShieldAttach
  /-- Exile the targeted GY card; you may play it until the end of your next turn. -/
  | exileGyPlayUntilNextTurn
  /-- Return the targeted GY permanent card to your hand. -/
  | returnGyPermanentThisTurn
  /-- Tap the target; it can't become untapped while you control the source. -/
  | tapCantUntapWhileControl
  /-- You may sacrifice another creature. When you do, destroy an opposing nonland. -/
  | maySacAnotherThenDestroyOppNonland
  /-- You may sac an artifact or discard a nonland. When you do, 2 damage. -/
  | maySacOrDiscardNonlandThenDamage
  /-- Reveal the opponent's hand; exile a card or creature until this leaves. -/
  | revealHandExileUntilLeaves
  /-- +1/+1 on creature targets, or return an artifact/enchantment from GY. -/
  | plusOnesOrReturnArtEnch
  /-- Resolve chosen “up to X” modes in printed order. -/
  | chooseUpToXModes
  /-- You may tap this. When you do, grant indestructible to another creature. -/
  | mayTapThenGrantIndestructible
  /-- Tap the target; it loses abilities while the source remains. -/
  | tapLoseAbilitiesWhileSource
  /-- Target player reveals cards from hand; you choose one to discard. -/
  | revealDiscardFromHand
  /-- Create Redwing. -/
  | createRedwing
  /-- Resolve a leftover StepLeftover. -/
  | step (e : StepLeftover)
  /-- Resolve a leftover DeathLeftover. -/
  | death (e : DeathLeftover)
  /-- Resolve a leftover ThisAttackLeftover. -/
  | thisAttack (e : ThisAttackLeftover)
  /-- Resolve a leftover EnterOrAttackLeftover. -/
  | enterOrAttack (e : EnterOrAttackLeftover)
  /-- Resolve a leftover WatchLeftover. -/
  | watch (e : WatchLeftover)
  /-- Resolve a leftover YouAttackLeftover. -/
  | youAttacking (e : YouAttackLeftover)
  /-- Resolve a leftover CastLeftover. -/
  | casting (e : CastLeftover)
  /-- Resolve a leftover ResourceLeftover. -/
  | resource (e : ResourceLeftover)
deriving Repr, Inhabited, BEq

/-- When a triggered ability fires, how it targets, optional divided-damage
parameters, and how it resolves (CR 603 / 601.2d / 608). Adding a constructor
only requires updating `timing` instead of parallel match trees. -/
structure TriggerTiming where
  events : Array TriggerEvent := #[]
  targeting : EffectTargeting := .of .none
  /-- Zero targets is a legal announcement (CR 115.1c / 601.2c), e.g. “up to one”. -/
  allowsZeroTargets : Bool := false
  /-- Damage amount and maximum number of targets when this ability divides
  damage as the controller chooses (CR 601.2d). -/
  dividedDamage : Option (Nat × Nat) := none
  /-- What happens when this ability resolves. -/
  resolution : TriggerResolution := .pumpGreatestPower
  /-- Intervening “while you control a creature with power ≥ n” (e.g. Ferocious).
  Checked when the trigger event occurs (CR 603.2 / 603.4); not rechecked on
  resolution. -/
  youControlCreatureWithPower : Option Int := none
  /-- This trigger fires only once each turn. -/
  onceEachTurn : Bool := false
  /-- “Do this only once each turn”: the ability keeps triggering until the
  controller chooses to do the optional action (MSH 69). -/
  optionalOnceEachTurn : Bool := false
  /-- Intervening “another creature you control with power ≤ n”. -/
  anotherCreaturePowerAtMost : Option Int := none
  /-- “This or another nontoken {subtype} you control enters”. -/
  thisOrNontokenSubtype : Option String := none
  /-- Intervening “if you gained `n` or more life this turn”. -/
  gainedLifeAtLeast : Option Nat := none
  /-- “Another {subtype} or Equipment you control enters”. -/
  anotherSubtypeOrEquipment : Option String := none
  /-- “This or another {subtype} you control enters”. -/
  thisOrAnotherSubtype : Option String := none
deriving Repr, Inhabited, BEq

end TriggeredAbility

namespace SharedTriggerWhen

/-- Whenever this creature enters or attacks. -/
def enterOrAttack : SharedTriggerWhen := .or .enter .attack

/-- Whenever you cast a green spell and whenever a Forest you control enters. -/
def castGreenOrForestEnters : SharedTriggerWhen :=
  .or .youCastGreen .forestYouControlEnters

/-- When this enters and whenever an opponent draws except their first draw-step card. -/
def enterOrOpponentDrawsExceptFirst : SharedTriggerWhen :=
  .or .enter .opponentDrawsExceptFirst

/-- Events this reusable trigger watches. -/
def events : SharedTriggerWhen → Array TriggerEvent
  | .enter => #[.entering]
  | .attack => #[.attacking]
  | .dies => #[.dying]
  | .youAttack => #[.youAttack]
  | .youAttackWithElves => #[.youAttackWithElves]
  | .youCastColor c => #[.youCastColor c]
  | .youCastNoncreature => #[.youCastNoncreature]
  | .landYouControlEnters => #[.landYouControlEnters]
  | .yourUpkeep => #[.yourUpkeep]
  | .yourEndStep => #[.yourEndStep]
  | .yourBeginCombat => #[.yourBeginCombat]
  | .youDrawSecond => #[.youDrawSecondCard]
  | .theRingTemptsYou => #[.theRingTemptsYou]
  | .youChooseRingBearer => #[.youChooseRingBearer]
  | .becomesTarget => #[.becomesTarget]
  | .artifactYouControlEnters => #[.artifactYouControlEnters]
  | .combatDamageToPlayer => #[.dealsCombatDamageToPlayer]
  | .oneOrMoreOtherCreaturesDie => #[.oneOrMoreOtherCreaturesDie]
  | .creatureCardLeavesYourGy => #[.creatureCardLeavesYourGy]
  | .youDraw => #[.youDraw]
  | .youGainLife => #[.youGainLife]
  | .anotherArtifactEnters => #[.anotherArtifactEnters]
  | .sourceDealtDamage => #[.sourceDealtDamage]
  | .equippedAttacksAlone => #[.equippedAttacksAlone]
  | .youCastWithTreasure => #[.youCastWithTreasure]
  | .youCastColorFromHand c => #[.youCastColorFromHand c]
  | .equippedCreatureYouControlAttacks => #[.equippedCreatureYouControlAttacks]
  | .anotherElfYouControlEnters => #[.anotherElfYouControlEnters]
  | .youActivateCreatureAbility => #[.youActivateCreatureAbility]
  | .opponentDrawsSecond => #[.opponentDrawsSecondCard]
  | .opponentCastsFirstNoncreature => #[.opponentCastsFirstNoncreature]
  | .eachEndStep => #[.eachEndStep]
  | .thisOrNontokenSubtypeEnters => #[.thisOrNontokenSubtypeYouControlEnters]
  | .thisOrAnotherSubtypeEnters => #[.thisOrAnotherSubtypeYouControlEnters]
  | .anotherSubtypeOrEquipmentEnters => #[.anotherSubtypeOrEquipmentYouControlEnters]
  | .combatDamageToPlayerOrBattle => #[.dealsCombatDamageToPlayerOrBattle]
  | .youCastGreen => #[.youCastGreen]
  | .forestYouControlEnters => #[.forestYouControlEnters]
  | .youCastInstantOrSorcery => #[.youCastInstantOrSorcery]
  | .equipmentYouControlEnters => #[.equipmentYouControlEnters]
  | .anotherCreatureYouControlEnters => #[.anotherCreatureYouControlEnters]
  | .anotherGoblinOrcArmyDies => #[.anotherGoblinOrcArmyDies]
  | .creatureYouControlAttacksAlone => #[.creatureYouControlAttacksAlone]
  | .opponentCastsSpell => #[.opponentCastsSpell]
  | .youScry => #[.youScry]
  | .becomesBlocked => #[.becomesBlocked]
  | .leaving => #[.leaving]
  | .youAttackWithTwoOrMore => #[.youAttackWithTwoOrMore]
  | .youSacrificeToken => #[.youSacrificeToken]
  | .armyYouControlCombatDamage => #[.armyYouControlCombatDamage]
  | .yourFirstMain => #[.yourFirstMain]
  | .anyPlayerCastsSecondSpell => #[.anyPlayerCastsSecondSpell]
  | .eachBeginCombat => #[.eachBeginCombat]
  | .youCastCreature => #[.youCastCreature]
  | .mountainYouControlEnters => #[.mountainYouControlEnters]
  | .equippedDealsCombatDamageToPlayer => #[.equippedDealsCombatDamageToPlayer]
  | .nontokenYouControlDies => #[.nontokenYouControlDies]
  | .playerLosesLife => #[.playerLosesLife]
  | .youCastSecondSpell => #[.youCastSecondSpell]
  | .equippedAttacks => #[.equippedAttacks]
  | .cascade => #[]
  | .tokenYouControlEnters => #[.tokenYouControlEnters]
  | .bolgSacrificedForReflexive => #[.bolgSacrificedForReflexive]
  | .opponentDrawsExceptFirst => #[.opponentDrawsExceptFirstDrawStep]
  | .youAttackWithTotalPower => #[.youAttackWithTotalPower]
  | .eaglesCreateBirds => #[.eaglesCreateBirds]
  | .opponentCastsMatchingParity => #[.opponentCastsMatchingParity]
  | .youPutCountersOnGoblinOrcArmy => #[.youPutCountersOnGoblinOrcArmy]
  | .sourceDealtNoncombatDamage => #[.sourceDealtNoncombatDamage]
  | .finalSagaChapterResolves => #[.finalSagaChapterResolves]
  | .combatDamageToYou => #[.combatDamageToYou]
  | .sagaChapter => #[.sagaChapter]
  | .tappedForTeamwork => #[.tappedForTeamwork]
  | .creatureYouControlEnters => #[.creatureYouControlEnters]
  | .creaturesYouControlBecomeTapped => #[.creaturesYouControlBecomeTapped]
  | .subtypeYouControlEnters subtype => #[.subtypeYouControlEnters subtype]
  | .creatureCardsPutIntoYourGy => #[.creatureCardsPutIntoYourGy]
  | .nthPlanCounter n => #[.nthPlanCounter n]
  | .or a b => a.events ++ b.events
  | .fromEffect => #[]

end SharedTriggerWhen

namespace SharedTrigger

/-- Targeting, divided-damage parameters, and resolution for this shared effect. -/
def timing : SharedTrigger → TriggeredAbility.TriggerTiming
  | .scry n => { resolution := .scry n }
  | .draw n => { resolution := .draw n }
  | .createTokens kind n tapped => { resolution := .createTokens kind n tapped }
  | .amassGoblins n => { resolution := .amassGoblins n }
  | .recruit => { resolution := .recruit }
  | .youRecruit => { resolution := .youRecruit }
  | .dividedDamage amount maxTargets =>
    { targeting := .of .playerOrCreature,
      dividedDamage := some (amount, maxTargets), resolution := .dividedDamage }
  | .plusOneOn kind =>
    { targeting := .of kind, resolution := .onPermanent (.plusOne 1) }
  | .plusOneOnSource => { resolution := .onSource (.plusOne 1) }
  | .sourceGets p t => { resolution := .onSource (.pump p t) }
  | .pumpTarget kind p t =>
    { targeting := .of kind, resolution := .onPermanent (.pump p t) }
  | .gainLife n => { resolution := .gainLife n }
  | .drawAndLoseLife => { resolution := .drawAndLoseLife }
  | .connive => { resolution := .connive }
  | .conniveTarget kind =>
    { targeting := .of kind, resolution := .targetConnive }
  | .exileUntilLeaves kind =>
    { targeting := .of kind, resolution := .exileUntilLeaves }
  | .damageEachOpponent n =>
    { targeting := .of .opponent, resolution := .damageEachOpponent n }
  | .attachTo kind =>
    { targeting := .of kind, resolution := .attachSourceToTarget }
  | .opponentSacrificesCreature =>
    { targeting := .of .opponent, resolution := .opponentSacrificesCreature }
  | .onPermanent kind action =>
    { targeting := .of kind, resolution := .onPermanent action }
  | .onSource action =>
    { resolution := .onSource action }
  | .exileTop => { resolution := .exileTop }
  | .mayDiscardDraw n => { resolution := .mayDiscardDraw n }
  | .eachOpponentDiscards => { resolution := .eachOpponentDiscards }
  | .targetOpponentDiscards n =>
    { targeting := .of .opponent, resolution := .targetOpponentDiscards n }
  | .millPlayer n =>
    { targeting := .of .player, resolution := .millPlayer n }
  | .amassOrcs n => { resolution := .amassOrcs n }
  | .investigate => { resolution := .investigate }
  | .pumpCause p t => { resolution := .pumpCause p t }
  | .searchForest => { resolution := .searchForest }
  | .searchBasicToHand => { resolution := .searchBasicToHand }
  | .eachPlayerSacrificesCreature => { resolution := .eachPlayerSacrificesCreature }
  | .exileTarget kind =>
    { targeting := .of kind, resolution := .exileTarget }
  | .returnCreatureFromGyToHand =>
    { targeting := .of .creatureCardInYourGraveyard,
      resolution := .returnCreatureFromGyToHand }
  | .loot => { resolution := .loot }
  | .plusOneEachYouControl => { resolution := .plusOneEachYouControl }
  | .sourceGetsAndTeamTrample p => { resolution := .sourceGetsAndTeamTrample p }
  | .honeEachEquipment => { resolution := .honeEachEquipment }
  | .plusOneEachOtherGainLife => { resolution := .plusOneEachOtherGainLife }
  | .becomePT p t => { resolution := .becomePT p t }
  | .pumpAndDamageOpponents n => { resolution := .pumpAndDamageOpponents n }
  | .plusOneAndLifelink kind =>
    { targeting := .of kind, resolution := .plusOneAndLifelink }
  | .pumpTargetPerPlains =>
    { targeting := .of .creatureYouControl, resolution := .pumpTargetPerPlains }
  | .drawThenDiscard n => { resolution := .drawThenDiscardN n }
  | .mayDiscardHandDraw n => { resolution := .mayDiscardHandDraw n }
  | .pumpByLookedAt => { resolution := .pumpByLookedAt }
  | .pumpAndUnblockable => { resolution := .pumpAndUnblockable }
  | .pumpGreatestPower => { resolution := .pumpGreatestPower }
  | .pumpForEachOtherCreature => { resolution := .pumpForEachOtherCreature }
  | .damageBlockers n => { resolution := .damageBlockers n }
  | .grantFlying kind =>
    { targeting := .of kind, resolution := .grantFlying }
  | .returnLinkedExile => { resolution := .returnLinkedExile }
  | .createThenAttach kind => { resolution := .createThenAttach kind }
  | .amassThenAttach n => { resolution := .amassThenAttach n }
  | .gainLifeSearchBasicOnTop n => { resolution := .gainLifeSearchBasicOnTop n }
  | .addMana types => { resolution := .addMana types }
  | .createAxe => { resolution := .createAxe }
  | .createAxeAttach =>
    { targeting := .of .creatureYouControl, resolution := .createAxeAttach }
  | .tapOppOrUntapYours => { resolution := .tapOppOrUntapYours }
  | .gainControlOppUntilEot =>
    { targeting := .of .oppCreature, resolution := .gainControlOppUntilEot }
  | .amassGoblinsEqualPower => { resolution := .amassGoblinsEqualPower }
  | .payReturnFromGy => { resolution := .payReturnFromGy }
  | .targetOpponentLosesLife n =>
    { targeting := .of .opponent, resolution := .targetOpponentLosesLife n }
  | .plusOneVigilance n =>
    { targeting := .of .creatureYouControl, resolution := .plusOneVigilance n }
  | .mayDrawXDiscard2 => { resolution := .mayDrawXDiscard2 }
  | .drawPlusOneSource => { resolution := .drawPlusOneSource }
  | .ringTempts => { resolution := .ringTempts }
  | .setOtherBasePT =>
    { targeting := .of .anotherCreatureYouControl, allowsZeroTargets := true,
      resolution := .setOtherBasePT }
  | .returnElfGainLife =>
    { targeting := .of .elfInYourGraveyard, resolution := .returnElfGainLife }
  | .damageFromLastKnownPower =>
    { targeting := .of .oppCreature, resolution := .damageFromLastKnownPower }
  | .exileOppGyCardOppsLoseLife n =>
    { targeting := .of .oppGraveyardCard, allowsZeroTargets := true,
      resolution := .exileOppGyCardOppsLoseLife n }
  | .creaturesYouControlPumpAndFirstStrike p =>
    { resolution := .creaturesYouControlPumpAndFirstStrike p }
  | .mayPayGenericDraw generic =>
    { resolution := .mayPayGenericDraw generic }
  | .drawThenBottomIfNoLegendary =>
    { resolution := .drawThenBottomIfNoLegendary }
  | .removeHopeDrawSac => { resolution := .removeHopeDrawSac }
  | .tapHumansDraw => { resolution := .tapHumansDraw }
  | .untapPlusOneIfSubtype subtype =>
    { targeting := .of .anotherCreatureYouControl,
      resolution := .untapPlusOneIfSubtype subtype }
  | .destroyOppArtifactsEnchantmentsGainLife =>
    { resolution := .destroyOppArtifactsEnchantmentsGainLife }
  | .damageEqualSubtypeToEachOpponent subtype =>
    { resolution := .damageEqualSubtypeToEachOpponent subtype }
  | .damageEqualTreasures =>
    { targeting := .of .playerOrCreature, resolution := .damageEqualTreasures }
  | .loseLifeCreateTreasure => { resolution := .loseLifeCreateTreasure }
  | .dealDamageDestroyIfSubtype n subtype =>
    { targeting := .of .playerOrCreature,
      resolution := .dealDamageDestroyIfSubtype n subtype }
  | .attachEquipmentToCreature =>
    { targeting := .of .equipmentYouControlThenCreatureYouControl,
      allowsZeroTargets := true, resolution := .attachEquipmentToCreature }
  | .defenderSacsLeastPower => { resolution := .defenderSacsLeastPower }
  | .returnOtherPlusOne =>
    { targeting := .of .anotherCreatureYouControl, allowsZeroTargets := true,
      resolution := .returnOtherPlusOne }
  | .lookAtTopRevealTypes n types =>
    { resolution := .lookAtTopRevealTypes n types }
  | .createTappedTreasuresEqualOppArtifacts =>
    { resolution := .createTappedTreasuresEqualOppArtifacts }
  | .putNonlandMvAtMostFromGy mv =>
    { targeting := .of .nonland, allowsZeroTargets := true,
      resolution := .putNonlandMvAtMostFromGy mv }
  | .othersGetAndOppsGet subtypes p t oppP oppT =>
    { resolution := .othersGetAndOppsGet subtypes p t oppP oppT }
  | .wolfPlusOneOrTreasure => { resolution := .wolfPlusOneOrTreasure }
  | .trampleCounterBecomeBear =>
    { targeting := .of .creatureYouControl, allowsZeroTargets := true,
      resolution := .trampleCounterBecomeBear }
  | .millThenSubtypeToHand n subtype =>
    { resolution := .millThenSubtypeToHand n subtype }
  | .exileOppNonlandEachUntilLeaves =>
    { targeting := .of .oppNonland, allowsZeroTargets := true,
      resolution := .exileOppNonlandEachUntilLeaves }
  | .plusOneEqualLastKnownMv =>
    { targeting := .of .creatureYouControl, resolution := .plusOneEqualLastKnownMv }
  | .mountainQuestDragon => { resolution := .mountainQuestDragon }
  | .treasuresPerChosenType => { resolution := .treasuresPerChosenType }
  | .revealUntilCreature => { resolution := .revealUntilCreature }
  | .attackSacPlusOneEqualPower => { resolution := .attackSacPlusOneEqualPower }
  | .lootLandEntersTapped => { resolution := .lootLandEntersTapped }
  | .millThatManyLost => { resolution := .millThatManyLost }
  | .drawPerFatGraveyard => { resolution := .drawPerFatGraveyard }
  | .maySacDrawTreasure => { resolution := .maySacDrawTreasure }
  | .plusOneEachIfCityBlessing => { resolution := .plusOneEachIfCityBlessing }
  | .castInstantSorceryFromHand => { resolution := .castInstantSorceryFromHand }
  | .castInstantSorceryMvAtMost => { resolution := .castInstantSorceryMvAtMost }
  | .millThenCopy => { resolution := .millThenCopy }
  | .pumpTargetBySourcePower =>
    { targeting := .of .anotherCreatureYouControl,
      resolution := .pumpTargetBySourcePower }
  | .createAlienPerInvasion => { resolution := .createAlienPerInvasion }
  | .mayPutArtifactAttachEquipment => { resolution := .mayPutArtifactAttachEquipment }
  | .cascade => { resolution := .cascade }
  | .belladonnaTokenReward => { resolution := .belladonnaTokenReward }
  | .bolgMaySacrifice => { resolution := .bolgMaySacrifice }
  | .bolgDealSacrificedPower =>
    { targeting := .of .anotherCreature, resolution := .bolgDealSacrificedPower }
  | .createSpiritsForEquipped => { resolution := .createSpiritsForEquipped }
  | .createTreasuresEqualDamagedPlayerArtifacts =>
    { resolution := .createTreasuresEqualDamagedPlayerArtifacts }
  | .deal1ThenAmassOrcs =>
    { targeting := .of .playerOrCreature, resolution := .deal1ThenAmassOrcs }
  | .untapAttackersExtraCombat _n => { resolution := .untapAttackersExtraCombat }
  | .eaglesCreateBirds => { resolution := .eaglesCreateBirds }
  | .allianceMode => { resolution := .allianceMode }
  | .destroyOtherAmassControllerPower =>
    { targeting := .of .anotherCreature, allowsZeroTargets := true,
      resolution := .destroyOtherAmassControllerPower }
  | .gollumMode => { resolution := .gollumMode }
  | .discardHandDrawDamageIfStory => { resolution := .discardHandDrawDamageIfStory }
  | .castFromGyArtifactInstantSorcery =>
    { resolution := .castFromGyArtifactInstantSorcery }
  | .equippedAttackersGainDoubleStrike =>
    { resolution := .equippedAttackersGainDoubleStrike }
  | .tapEnchantedRemoveCounters => { resolution := .tapEnchantedRemoveCounters }
  | .revealTopPutRandomCreature n =>
    { resolution := .revealTopPutRandomCreature n }
  | .beginCombatIfDrawnTwoPump =>
    { targeting := .of .anotherCreatureYouControl,
      resolution := .beginCombatIfDrawnTwoPump }
  | .honePerOppAttach =>
    { targeting := .of .creatureYouControl, allowsZeroTargets := true,
      resolution := .honePerOppAttach }
  | .damageTargetOpponent n =>
    { targeting := .of .opponent, resolution := .damageTargetOpponent n }
  | .copySelfNonlegendary => { resolution := .copySelfNonlegendary }
  | .attachEquipmentThenFight =>
    { targeting := .of .creatureYouControl, resolution := .attachEquipmentThenFight }
  | .returnAsArtifact => { resolution := .returnAsArtifact }
  | .exileLandsThenReturnTapped =>
    { targeting := .of .creatureOrLandYouControl, allowsZeroTargets := true,
      resolution := .exileLandsThenReturnTapped }
  | .grimaImpulse => { resolution := .grimaImpulse }
  | .palantir =>
    { targeting := .of .opponent, resolution := .palantir }
  | .treasuresEqualLastKnown => { resolution := .treasuresEqualLastKnown }
  | .protectionEverything => { resolution := .protectionEverything }
  | .loseLifePerBurden => { resolution := .loseLifePerBurden }
  | .revealSaga => { resolution := .revealSaga }
  | .sacDamagersRingTempts => { resolution := .sacDamagersRingTempts }
  | .chapter _n e =>
    { resolution := .chapter e }
  | .plusOneOnSourceAndDraw => { resolution := .plusOneOnSourceAndDraw }
  | .drawIfAttackedOrEnteredSubtype subtype =>
    { resolution := .drawIfAttackedOrEnteredSubtype subtype }
  | .othersOfSubtypeGetEqualSourceToughness subtype =>
    { resolution := .othersOfSubtypeGetEqualSourceToughness subtype }
  | .scryAndPlan n => { resolution := .scryAndPlan n }
  | .lootAndPlan => { resolution := .lootAndPlan }
  | .createVillainAndPlan => { resolution := .createVillainAndPlan }
  | .drainAndPlan n => { resolution := .drainAndPlan n }
  | .drawLoseLifeAndPlan => { resolution := .drawLoseLifeAndPlan }
  | .treasureTappedAndPlan => { resolution := .treasureTappedAndPlan }
  | .plusOneOnTargetAndPlan =>
    { targeting := .of .creatureYouControl, resolution := .plusOneOnTargetAndPlan }
  | .planFinishDrawPlusOneEach => { resolution := .planFinishDrawPlusOneEach }
  | .planFinishReturnInstants => { resolution := .planFinishReturnInstants }
  | .planFinishControlOpponent => { resolution := .planFinishControlOpponent }
  | .planFinishExileTopCast => { resolution := .planFinishExileTopCast }
  | .planFinishCreateRobots n => { resolution := .planFinishCreateRobots n }
  | .planFinishDividedDamage n => { resolution := .planFinishDividedDamage n }
  | .planFinishIndestructibleOnTarget =>
    { resolution := .planFinishIndestructibleOnTarget }
  | .surveil n => { resolution := .scry n }
  | .onEnchanted action => { resolution := .onEnchanted action }
  | .attachThen followup =>
    { targeting := .of .creatureYouControl, resolution := .attachThen followup }
  | .exileOtherCopyEnchanted =>
    { targeting := .of .creature, allowsZeroTargets := true,
      resolution := .exileOtherCopyEnchanted }
  | .exileUntilNextEndStep =>
    { targeting := .of .creatureYouControl, allowsZeroTargets := true,
      resolution := .exileUntilNextEndStep }
  | .tapOrUntapNonland =>
    { targeting := .of .nonland, resolution := .tapOrUntapNonland }
  | .createFoodOrTreasure => { resolution := .createFoodOrTreasure }
  | .villainIfGyElseMill => { resolution := .villainIfGyElseMill }
  | .drawMayPutLandTapped => { resolution := .drawMayPutLandTapped }
  | .drawGainLifeIfAnotherHero => { resolution := .drawGainLifeIfAnotherHero }
  | .plusOneOrTwoIfAnotherHero =>
    { targeting := .of .creature, resolution := .plusOneOrTwoIfAnotherHero }
  | .maySacArtifactOrDiscardDraw => { resolution := .maySacArtifactOrDiscardDraw }
  | .enter (.destroy kind) =>
    { events := #[.entering], targeting := .of kind, resolution := .onPermanent .destroy }
  | .enter (.dealDamageUpToOne n) =>
    { events := #[.entering], targeting := .of .creature, allowsZeroTargets := true,
      resolution := .onPermanent (.dealDamage n) }
  | .enter .fightUpToOne =>
    { events := #[.entering], targeting := .of .anotherCreature, allowsZeroTargets := true,
      resolution := .fightUpToOne }
  | .enter .returnNonlandNontoken =>
    { events := #[.entering], targeting := .of .nonlandNontoken, allowsZeroTargets := true,
      resolution := .returnToOwnerHand }
  | .enter .createZabu =>
    { events := #[.entering], resolution := .createZabu }
  | .enter .oppCreatesTheVoid =>
    { events := #[.entering], targeting := .of .opponent, resolution := .oppCreatesTheVoid }
  | .enter .createSturdyShieldAttach =>
    { events := #[.entering], resolution := .createSturdyShieldAttach }
  | .enter .exileGyPlayUntilNextTurn =>
    { events := #[.entering], targeting := .of .equipmentInstantOrSorceryInYourGraveyard,
      resolution := .exileGyPlayUntilNextTurn }
  | .enter .returnGyPermanentThisTurn =>
    { events := #[.entering], targeting := .of .permanentCardInYourGraveyard,
      resolution := .returnGyPermanentThisTurn }
  | .enter .tapOppCantUntapWhileControl =>
    { events := #[.entering], targeting := .of .oppCreature,
      resolution := .tapCantUntapWhileControl }
  | .enter .maySacAnotherThenDestroyOppNonland =>
    { events := #[.entering], resolution := .maySacAnotherThenDestroyOppNonland }
  | .enter .maySacOrDiscardNonlandThenDamage =>
    { events := #[.entering], resolution := .maySacOrDiscardNonlandThenDamage }
  | .enter .revealHandExileUntilLeaves =>
    { events := #[.entering], targeting := .of .opponent, allowsZeroTargets := true,
      resolution := .revealHandExileUntilLeaves }
  | .enter .plusOnesOrReturnArtEnch =>
    { events := #[.entering], targeting := .of .creature, allowsZeroTargets := true,
      resolution := .plusOnesOrReturnArtEnch }
  | .enter .chooseUpToXModes =>
    { events := #[.entering], targeting := .of .opponent, allowsZeroTargets := true,
      resolution := .chooseUpToXModes }
  | .enter .mayTapThenGrantIndestructible =>
    { events := #[.entering], resolution := .mayTapThenGrantIndestructible }
  | .enter .tapLoseAbilitiesWhileSource =>
    { events := #[.entering], targeting := .of .creature, allowsZeroTargets := true,
      resolution := .tapLoseAbilitiesWhileSource }
  | .enter .revealDiscardFromHand =>
    { events := #[.entering], targeting := .of .player, resolution := .revealDiscardFromHand }
  | .enter .createRedwing =>
    { events := #[.entering], resolution := .createRedwing }
  | .step .enchantedControllerDraws =>
    { events := #[.enchantedControllerUpkeep], resolution := .step .enchantedControllerDraws }
  | .step .drawToTen =>
    { events := #[.yourEndStep], resolution := .step .drawToTen }
  | .step .copyAbsorbingMan =>
    { events := #[.yourFirstMain], resolution := .step .copyAbsorbingMan }
  | .step .hydeChoose =>
    { events := #[.yourUpkeep], resolution := .step .hydeChoose }
  | .step .copyTaskmaster =>
    { events := #[.yourFirstMain], targeting := .of .creature, allowsZeroTargets := true,
      resolution := .step .copyTaskmaster }
  | .step .harnessedFlicker =>
    { events := #[.yourEndStep], targeting := .of .nonland, allowsZeroTargets := true,
      resolution := .step .harnessedFlicker }
  | .death .hellcatReturn =>
    { events := #[.dying], resolution := .death .hellcatReturn }
  | .death .villainReturnAsHero =>
    { events := #[.villainYouControlDies], resolution := .death .villainReturnAsHero }
  | .death .attackingReturnHand =>
    { events := #[.attackingCreatureYouControlDies], resolution := .death .attackingReturnHand }
  | .death .deathtouchOppSac =>
    { events := #[.anotherCreatureYouControlEnters], resolution := .death .deathtouchOppSac }
  | .thisAttack .mayPayPlusOne =>
    { events := #[.attacking], targeting := .of .creature, resolution := .thisAttack .mayPayPlusOne }
  | .thisAttack .payReturnAttacking =>
    { events := #[.attacking], resolution := .thisAttack .payReturnAttacking }
  | .thisAttack .ifArtifactEnteredDraw =>
    { events := #[.attacking], resolution := .thisAttack .ifArtifactEnteredDraw }
  | .thisAttack .blinkNontoken =>
    { events := #[.attacking], resolution := .thisAttack .blinkNontoken }
  | .thisAttack .equippedDrain =>
    { events := #[.attacking], resolution := .thisAttack .equippedDrain }
  | .thisAttack .drawIfPower4 =>
    { events := #[.attacking], resolution := .thisAttack .drawIfPower4 }
  | .thisAttack .attacksAlonePlus2Indestructible =>
    { events := #[.attacking], resolution := .thisAttack .attacksAlonePlus2Indestructible }
  | .enterOrAttack .copyKeywords =>
    { events := #[.entering, .attacking], targeting := .of .creature,
      resolution := .enterOrAttack .copyKeywords }
  | .enterOrAttack .createSquirrel =>
    { events := #[.entering, .attacking], resolution := .enterOrAttack .createSquirrel }
  | .watch .combatDamageExileUntilNonland =>
    { events := #[.dealsCombatDamageToPlayer], resolution := .watch .combatDamageExileUntilNonland }
  | .watch .attacksAloneDrain =>
    { events := #[.creatureYouControlAttacksAlone], targeting := .of .opponent,
      resolution := .watch .attacksAloneDrain }
  | .watch .attacksAloneFirstStrikeMenace =>
    { events := #[.creatureYouControlAttacksAlone], resolution := .watch .attacksAloneFirstStrikeMenace }
  | .watch .firstTapUntap =>
    { events := #[.creatureYouControlTapped], resolution := .watch .firstTapUntap }
  | .watch .sheHulkRedirectOnce =>
    { events := #[.creatureYouControlDealtDamage], targeting := .of .playerOrCreature,
      onceEachTurn := true, resolution := .watch .sheHulkRedirectOnce }
  | .watch .speedballTargeted =>
    { events := #[.spellTargetsSource], resolution := .watch .speedballTargeted }
  | .watch .anyPlayerSecondDraw =>
    { events := #[.anyPlayerDrawsSecond], resolution := .watch .anyPlayerSecondDraw }
  | .watch .youTargetDrawOnce =>
    { events := #[.youTargetSomething], onceEachTurn := true, resolution := .watch .youTargetDrawOnce }
  | .watch .villainOrArtifactDamage =>
    { events := #[.anotherVillainOrArtifactEnters], targeting := .of .opponent,
      resolution := .watch .villainOrArtifactDamage }
  | .watch .villainConniveOnce =>
    { events := #[.anotherVillainEnters], optionalOnceEachTurn := true,
      resolution := .watch .villainConniveOnce }
  | .watch .villainPlusOneDamageOnce =>
    { events := #[.anotherVillainEnters], onceEachTurn := true,
      resolution := .watch .villainPlusOneDamageOnce }
  | .watch .villainAttachEquipment =>
    { events := #[.anotherVillainEnters], targeting := .of .creatureYouControl,
      allowsZeroTargets := true, resolution := .watch .villainAttachEquipment }
  | .watch .villainPlusOneLifelink =>
    { events := #[.anotherVillainEnters], resolution := .watch .villainPlusOneLifelink }
  | .watch .hulklingCompare =>
    { events := #[.anotherCreatureYouControlEnters], resolution := .watch .hulklingCompare }
  | .watch .justiceBounce =>
    { events := #[.anotherNonlandReturned], resolution := .watch .justiceBounce }
  | .watch .nontokenHeroModal =>
    { events := #[.anotherNontokenHeroEnters], resolution := .watch .nontokenHeroModal }
  | .watch .ultronCopy =>
    { events := #[.anotherNontokenArtifactEnters], resolution := .watch .ultronCopy }
  | .watch .enchantedAttachEquipment =>
    { events := #[.enchantedAttacksOrBlocks], resolution := .watch .enchantedAttachEquipment }
  | .watch .equippedAttacksAloneUntapScry =>
    { events := #[.equippedAttacksAlone], resolution := .watch .equippedAttacksAloneUntapScry }
  | .watch .equippedAttacksTap =>
    { events := #[.equippedAttacks], targeting := .of .creature,
      resolution := .watch .equippedAttacksTap }
  | .watch .equippedTappedDamage =>
    { events := #[.equippedBecomesTapped], resolution := .watch .equippedTappedDamage }
  | .watch .heroesDamagePlusTwo =>
    { events := #[.heroesDealDamageToPlayer], resolution := .watch .heroesDamagePlusTwo }
  | .watch .merfolkAttackDraw =>
    { events := #[.merfolkAttackPlayer], resolution := .watch .merfolkAttackDraw }
  | .watch .tokensEnterMayDraw =>
    { events := #[.tokenYouControlEnters], resolution := .watch .tokensEnterMayDraw }
  | .watch .hawkeyeModes =>
    { events := #[.sourceBecomesTapped], allowsZeroTargets := true,
      resolution := .watch .hawkeyeModes }
  | .watch .redHulk =>
    { events := #[.sourceDealtDamage], resolution := .watch .redHulk }
  | .watch .hulk =>
    { events := #[.sourceDealtDamage], resolution := .watch .hulk }
  | .youAttacking .pay2LifeToughness =>
    { events := #[.youAttack], resolution := .youAttacking .pay2LifeToughness }
  | .youAttacking .exileTopHeroPump =>
    { events := #[.youAttack], resolution := .youAttacking .exileTopHeroPump }
  | .youAttacking .lookSixCast =>
    { events := #[.youAttack], resolution := .youAttacking .lookSixCast }
  | .casting .villainToken =>
    { events := #[.youCastVillain], resolution := .casting .villainToken }
  | .casting .merfolkFromBlue =>
    { events := #[.youCastNoncreature], resolution := .casting .merfolkFromBlue }
  | .casting .mayPayHasteUnblockable =>
    { events := #[.youCastNoncreature], resolution := .casting .mayPayHasteUnblockable }
  | .casting .plusOneEachOther =>
    { events := #[.youCastNoncreature], resolution := .casting .plusOneEachOther }
  | .casting .exileFlicker =>
    { events := #[.youCastNoncreature], targeting := .of .nonland,
      resolution := .casting .exileFlicker }
  | .casting .visionModes =>
    { events := #[.youCastNoncreature], resolution := .casting .visionModes }
  | .casting .damageEqualMv =>
    { events := #[.youCastNoncreature], targeting := .of .playerOrCreature,
      resolution := .casting .damageEqualMv }
  | .casting .drawPowerEqualHand =>
    { events := #[.youCastTargetingCreatureYouControl], resolution := .casting .drawPowerEqualHand }
  | .casting .plusOneThis =>
    { events := #[.youCastTargetingCreatureYouControl], resolution := .casting .plusOneThis }
  | .casting .plusOneScry =>
    { events := #[.youCastTargetingCreatureYouControl], resolution := .casting .plusOneScry }
  | .casting .ironFistTap =>
    { events := #[.youCastTargetingCreatureYouControl], resolution := .casting .ironFistTap }
  | .casting .targetsGainFlying =>
    { events := #[.youCastTargetingCreatureYouControl], resolution := .casting .targetsGainFlying }
  | .casting .copyIfArtifactOrLand =>
    { events := #[.youCastInstantOrSorcery], resolution := .casting .copyIfArtifactOrLand }
  | .casting .tapCreatureOrLand =>
    { events := #[.youCastNoncreature], targeting := .of .creature,
      resolution := .casting .tapCreatureOrLand }
  | .resource .discardExilePlay =>
    { events := #[.youDiscard], resolution := .resource .discardExilePlay }
  | .resource .drawIfAnotherHeroDamage =>
    { events := #[.youDraw], targeting := .of .opponent,
      resolution := .resource .drawIfAnotherHeroDamage }
  | .resource .secondDrawBecome66 =>
    { events := #[.youDrawSecondCard], resolution := .resource .secondDrawBecome66 }
  | .resource .secondDrawPlusOneTarget =>
    { events := #[.youDrawSecondCard], targeting := .of .creature,
      resolution := .resource .secondDrawPlusOneTarget }
  | .resource .secondDrawDrain =>
    { events := #[.youDrawSecondCard], resolution := .resource .secondDrawDrain }
  | .resource .gainLifePlusOnes =>
    { events := #[.youGainLife], targeting := .of .playerOrCreature, allowsZeroTargets := true,
      resolution := .resource .gainLifePlusOnes }
  | .resource .plusOneCreateInsectOnce =>
    { events := #[.youPutPlusOne], onceEachTurn := true,
      resolution := .resource .plusOneCreateInsectOnce }
  | .resource .plusOneOnThisOnce =>
    { events := #[.youPutPlusOne], onceEachTurn := true,
      resolution := .resource .plusOneOnThisOnce }
  | .resource .plusOneOnHeroesCreateWall =>
    { events := #[.youPutPlusOne], resolution := .resource .plusOneOnHeroesCreateWall }

end SharedTrigger

#guard (SharedTrigger.timing (.watch .sheHulkRedirectOnce)).onceEachTurn
#guard (SharedTrigger.timing (.watch .villainConniveOnce)).optionalOnceEachTurn
#guard (SharedTrigger.timing (.enterOrAttack .copyKeywords)).events ==
  #[TriggerEvent.entering, TriggerEvent.attacking]
#guard (SharedTrigger.timing (.death .hellcatReturn)).resolution ==
  TriggeredAbility.TriggerResolution.death .hellcatReturn

end Mtg.Engine
