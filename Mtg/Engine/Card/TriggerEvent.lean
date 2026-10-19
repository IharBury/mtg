import Mtg.Engine.Color
import Mtg.Engine.Card.Text

/-!
# Trigger events (CR 603)

When a triggered ability fires, structured around the event categories of
CR 603 (`enters`, `leaves`, `step`, `casts`, `combat`, `damage`, `draws`,
`discards`, `taps`, `counters`, `action`, `or`), with per-event clause wording
and metadata.
-/

namespace Mtg.Engine

namespace TriggerEvent

/-- Which permanent entering the battlefield causes `TriggerEvent.enters` to fire (CR 603.6a). -/
inductive EntersEvent where
  | source
  | landYouControl
  | forestYouControl
  | mountainYouControl
  | artifactYouControl
  | anotherArtifact
  | anotherNontokenArtifact
  | equipmentYouControl
  | tokenYouControl
  | creatureYouControl
  | anotherCreatureYouControl
  | anotherNontokenCreatureYouControl
  | thisOrAnotherCreatureYouControl
  | anotherCreatureOrPlaneswalkerYouControl
  | creatureOpponentControls
  | creatureYouControlPowerAtLeast (n : Int)
  | anotherElfYouControl
  | anotherVillain
  | anotherVillainOrArtifact
  | anotherNontokenHero
  | subtypeYouControl (subtype : String)
  | thisOrAnotherSubtypeYouControl
  | thisOrNontokenSubtypeYouControl
  | anotherSubtypeOrEquipmentYouControl
deriving Repr, Inhabited, BEq, DecidableEq

/-- Which zone-leaving or graveyard-entering event causes `TriggerEvent.leaves` to fire (CR 603.6c / 700.4). -/
inductive LeavesEvent where
  | sourceDies
  | sourceLeaves
  | enchantedDies
  | creatureYouControlDies
  | nontokenYouControlDies
  | nontokenCreatureYouControlDies
  | attackingCreatureYouControlDies
  | villainYouControlDies
  | anotherGoblinOrcArmyDies
  | anotherCreatureOrPlaneswalkerYouControlDies
  | oneOrMoreOtherCreaturesDie
  | creatureYouControlLeaves
  | anotherNonlandReturned
  | creatureCardLeavesYourGy
  | creatureCardsPutIntoYourGy
deriving Repr, Inhabited, BEq, DecidableEq

/-- Which phase or step beginning causes `TriggerEvent.step` to fire (CR 603.2b). -/
inductive StepEvent where
  | yourUpkeep
  | eachUpkeep
  | eachUpkeepFromGraveyard
  | enchantedControllerUpkeep
  | eaglesCreateBirds
  | eachOpponentDrawStep
  | yourFirstMain
  | yourBeginCombat
  | yourBeginCombatFromGraveyard
  | opponentBeginCombat
  | eachBeginCombat
  | yourEndStep
  | eachEndStep
deriving Repr, Inhabited, BEq, DecidableEq

/-- Which spell being cast causes `TriggerEvent.casts` to fire (CR 601.2i). -/
inductive CastEvent where
  | castThis
  | youSpell
  | youInstantOrSorcery
  | youNoncreature
  | youFirstNoncreature
  | youSecondSpell
  | youCreature
  | youArtifactOrCreature
  | youGreen
  | youColor (color : Color)
  | youColorFromHand (color : Color)
  | youVillain
  | youWithTreasure
  | youPreparedSpell
  | youTargetingCreatureYouControl
  | youEquipmentOrTargetingCreatureYouControl
  | youTargetingCreature
  | youInstantSorceryTargetingArtifactOrLand
  | youTargetingOpponentOrTheirCreature
  | opponentSpell
  | opponentFirstNoncreature
  | opponentSpellMvAtMost (n : Nat)
  | opponentMatchingParity
  | anyPlayerSecondSpell
  | spellTargetsSource
deriving Repr, Inhabited, BEq, DecidableEq

/-- Which attacker or blocker declaration causes `TriggerEvent.combat` to fire (CR 508.2 / 509.5c). -/
inductive CombatEvent where
  | sourceAttacks
  | youAttack
  | youAttackWithElves
  | youAttackWithTwoOrMore
  | youAttackWithTotalPower
  | equippedAttacks
  | equippedAttacksAlone
  | equippedCreatureYouControlAttacks
  | creatureYouControlAttacks
  | creatureYouControlAttacksAlone
  | creatureYouControlAttacksPlayerAlone
  | creatureAttacksYouOrYourPlaneswalker
  | creaturesAttackYourOpponent
  | merfolkAttackPlayer
  | zombieTokenAttacks
  | sphinxesAttack
  | enchantedAttacksOrBlocks
  | becomesBlocked
  | opponentSmallCreatureBlocks
deriving Repr, Inhabited, BEq, DecidableEq

/-- Which damage event causes `TriggerEvent.damage` to fire (CR 510.2 / 120). -/
inductive DamageEvent where
  | sourceCombatToPlayer
  | sourceCombatToPlayerOrBattle
  | equippedCombatToPlayer
  | armyYouControlCombat
  | combatToYou
  | opponentsDealtCombatYourTurn
  | heroesDealToPlayer
  | sourceDealt
  | sourceDealtNoncombat
  | creatureYouControlDealt
  | opponentsDealtNoncombat
  | opponentDealtNoncombat
deriving Repr, Inhabited, BEq, DecidableEq

/-- Which card draw causes `TriggerEvent.draws` to fire (CR 121). -/
inductive DrawEvent where
  | youCard
  | youSecondCard
  | opponentExceptFirstDrawStep
  | opponentSecondCard
  | anyPlayerSecond
deriving Repr, Inhabited, BEq, DecidableEq

/-- Which discard or cycling action causes `TriggerEvent.discards` to fire (CR 701.8 / 702.29). -/
inductive DiscardEvent where
  | youCard
  | youOne
  | youThis
  | playerCards
  | youCycle
deriving Repr, Inhabited, BEq, DecidableEq

/-- Which permanent becoming tapped causes `TriggerEvent.taps` to fire (CR 701.26). -/
inductive TapEvent where
  | source
  | equipped
  | forTeamwork
  | creatureYouControl
  | creaturesYouControl
deriving Repr, Inhabited, BEq, DecidableEq

/-- Which counter placement, proliferation, or Saga chapter causes `TriggerEvent.counters` to fire (CR 122 / 701.34 / 714). -/
inductive CounterEvent where
  | youPutPlusOne
  | youPutOnGoblinOrcArmy
  | youPutLoyalty
  | nthPlan (n : Nat)
  | sagaChapter
  | finalSagaChapterResolves
  | youProliferate
deriving Repr, Inhabited, BEq, DecidableEq

/-- Which player or object game action causes `TriggerEvent.action` to fire (CR 603.2). -/
inductive ActionEvent where
  | youActivateCreatureAbility
  | youActivateLoyaltyAbility
  | opponentActivatesLoyaltyAbility
  | becomesTarget
  | youTargetSomething
  | youSacrificeToken
  | bolgSacrificedForReflexive
  | youCreateCreatureTokens
  | youGainLife
  | playerLosesLife
  | youScry
  | youScryOrSurveil
  | theRingTemptsYou
  | youChooseRingBearer
deriving Repr, Inhabited, BEq, DecidableEq

end TriggerEvent

/-- When a triggered ability fires (CR 603). -/
inductive TriggerEvent where
  /-- A permanent enters the battlefield (CR 603.6a). -/
  | enters (what : TriggerEvent.EntersEvent := .source)
  /-- A permanent dies, leaves the battlefield, or changes zone (CR 603.6c / 700.4). -/
  | leaves (what : TriggerEvent.LeavesEvent := .sourceDies)
  /-- At the beginning of a phase or step (CR 603.2b). -/
  | step (which : TriggerEvent.StepEvent)
  /-- A player casts a spell (CR 601.2i). -/
  | casts (what : TriggerEvent.CastEvent := .youSpell)
  /-- Attackers or blockers are declared (CR 508.2 / 509.5c). -/
  | combat (what : TriggerEvent.CombatEvent := .sourceAttacks)
  /-- Damage is dealt (CR 510.2 / 120). -/
  | damage (what : TriggerEvent.DamageEvent := .sourceCombatToPlayer)
  /-- A player draws a card (CR 121). -/
  | draws (what : TriggerEvent.DrawEvent := .youCard)
  /-- A player discards or cycles a card (CR 701.8 / 702.29). -/
  | discards (what : TriggerEvent.DiscardEvent := .youCard)
  /-- One or more permanents become tapped (CR 701.26). -/
  | taps (what : TriggerEvent.TapEvent := .source)
  /-- Counters are put on a permanent, a player proliferates, or a Saga chapter triggers (CR 122 / 701.34 / 714). -/
  | counters (what : TriggerEvent.CounterEvent)
  /-- A player or object performs a game action (CR 603.2). -/
  | action (what : TriggerEvent.ActionEvent)
  /-- Triggers when at least one of the two given conditions triggers. -/
  | or (a b : TriggerEvent)
  /-- Cascade on the spell being cast (no `TriggerEvent`; queued from cast). -/
  | cascade
  /-- Use the events stored on the shared effect (leftover family wrappers). -/
  | fromEffect
deriving Repr, Inhabited, BEq, DecidableEq

/-- Unified alias for `TriggerEvent`. -/
abbrev FraEvent := TriggerEvent

/-- Unified alias for `TriggerEvent`. -/
abbrev SharedTriggerWhen := TriggerEvent

namespace TriggerEvent

/-- Identity wrapper kept for `TriggerEvent.fra` call sites. -/
abbrev fra (e : TriggerEvent) : TriggerEvent := e

-- Enters-the-battlefield aliases (CR 603.6a)
@[match_pattern] abbrev entering : TriggerEvent := .enters .source
@[match_pattern] abbrev enter : TriggerEvent := .enters .source
@[match_pattern] abbrev landYouControlEnters : TriggerEvent := .enters .landYouControl
@[match_pattern] abbrev forestYouControlEnters : TriggerEvent := .enters .forestYouControl
@[match_pattern] abbrev mountainYouControlEnters : TriggerEvent := .enters .mountainYouControl
@[match_pattern] abbrev artifactYouControlEnters : TriggerEvent := .enters .artifactYouControl
@[match_pattern] abbrev anotherArtifactEnters : TriggerEvent := .enters .anotherArtifact
@[match_pattern] abbrev anotherNontokenArtifactEnters : TriggerEvent := .enters .anotherNontokenArtifact
@[match_pattern] abbrev equipmentYouControlEnters : TriggerEvent := .enters .equipmentYouControl
@[match_pattern] abbrev tokenYouControlEnters : TriggerEvent := .enters .tokenYouControl
@[match_pattern] abbrev creatureYouControlEnters : TriggerEvent := .enters .creatureYouControl
@[match_pattern] abbrev anotherCreatureYouControlEnters : TriggerEvent := .enters .anotherCreatureYouControl
@[match_pattern] abbrev anotherNontokenCreatureYouControlEnters : TriggerEvent := .enters .anotherNontokenCreatureYouControl
@[match_pattern] abbrev thisOrAnotherCreatureYouControlEnters : TriggerEvent := .enters .thisOrAnotherCreatureYouControl
@[match_pattern] abbrev anotherCreatureOrPlaneswalkerYouControlEnters : TriggerEvent := .enters .anotherCreatureOrPlaneswalkerYouControl
@[match_pattern] abbrev creatureOpponentControlsEnters : TriggerEvent := .enters .creatureOpponentControls
@[match_pattern] abbrev creatureYouControlPowerAtLeastEnters (n : Int) : TriggerEvent := .enters (.creatureYouControlPowerAtLeast n)
@[match_pattern] abbrev anotherElfYouControlEnters : TriggerEvent := .enters .anotherElfYouControl
@[match_pattern] abbrev anotherVillainEnters : TriggerEvent := .enters .anotherVillain
@[match_pattern] abbrev anotherVillainOrArtifactEnters : TriggerEvent := .enters .anotherVillainOrArtifact
@[match_pattern] abbrev anotherNontokenHeroEnters : TriggerEvent := .enters .anotherNontokenHero
@[match_pattern] abbrev subtypeYouControlEnters (subtype : String) : TriggerEvent := .enters (.subtypeYouControl subtype)
@[match_pattern] abbrev thisOrAnotherSubtypeYouControlEnters : TriggerEvent := .enters .thisOrAnotherSubtypeYouControl
@[match_pattern] abbrev thisOrAnotherSubtypeEnters : TriggerEvent := .enters .thisOrAnotherSubtypeYouControl
@[match_pattern] abbrev thisOrNontokenSubtypeYouControlEnters : TriggerEvent := .enters .thisOrNontokenSubtypeYouControl
@[match_pattern] abbrev thisOrNontokenSubtypeEnters : TriggerEvent := .enters .thisOrNontokenSubtypeYouControl
@[match_pattern] abbrev anotherSubtypeOrEquipmentYouControlEnters : TriggerEvent := .enters .anotherSubtypeOrEquipmentYouControl
@[match_pattern] abbrev anotherSubtypeOrEquipmentEnters : TriggerEvent := .enters .anotherSubtypeOrEquipmentYouControl

-- Zone-leaving / dies / graveyard aliases (CR 603.6c / 700.4)
@[match_pattern] abbrev dying : TriggerEvent := .leaves .sourceDies
@[match_pattern] abbrev dies : TriggerEvent := .leaves .sourceDies
@[match_pattern] abbrev leaving : TriggerEvent := .leaves .sourceLeaves
@[match_pattern] abbrev enchantedDies : TriggerEvent := .leaves .enchantedDies
@[match_pattern] abbrev creatureYouControlDies : TriggerEvent := .leaves .creatureYouControlDies
@[match_pattern] abbrev nontokenYouControlDies : TriggerEvent := .leaves .nontokenYouControlDies
@[match_pattern] abbrev nontokenCreatureYouControlDies : TriggerEvent := .leaves .nontokenCreatureYouControlDies
@[match_pattern] abbrev attackingCreatureYouControlDies : TriggerEvent := .leaves .attackingCreatureYouControlDies
@[match_pattern] abbrev villainYouControlDies : TriggerEvent := .leaves .villainYouControlDies
@[match_pattern] abbrev anotherGoblinOrcArmyDies : TriggerEvent := .leaves .anotherGoblinOrcArmyDies
@[match_pattern] abbrev anotherCreatureOrPlaneswalkerYouControlDies : TriggerEvent := .leaves .anotherCreatureOrPlaneswalkerYouControlDies
@[match_pattern] abbrev oneOrMoreOtherCreaturesDie : TriggerEvent := .leaves .oneOrMoreOtherCreaturesDie
@[match_pattern] abbrev creatureYouControlLeaves : TriggerEvent := .leaves .creatureYouControlLeaves
@[match_pattern] abbrev anotherNonlandReturned : TriggerEvent := .leaves .anotherNonlandReturned
@[match_pattern] abbrev creatureCardLeavesYourGy : TriggerEvent := .leaves .creatureCardLeavesYourGy
@[match_pattern] abbrev creatureCardsPutIntoYourGy : TriggerEvent := .leaves .creatureCardsPutIntoYourGy

-- Phase and step aliases (CR 603.2b)
@[match_pattern] abbrev yourUpkeep : TriggerEvent := .step .yourUpkeep
@[match_pattern] abbrev eachUpkeep : TriggerEvent := .step .eachUpkeep
@[match_pattern] abbrev eachUpkeepFromGraveyard : TriggerEvent := .step .eachUpkeepFromGraveyard
@[match_pattern] abbrev enchantedControllerUpkeep : TriggerEvent := .step .enchantedControllerUpkeep
@[match_pattern] abbrev eaglesCreateBirds : TriggerEvent := .step .eaglesCreateBirds
@[match_pattern] abbrev eachOpponentDrawStep : TriggerEvent := .step .eachOpponentDrawStep
@[match_pattern] abbrev yourFirstMain : TriggerEvent := .step .yourFirstMain
@[match_pattern] abbrev yourBeginCombat : TriggerEvent := .step .yourBeginCombat
@[match_pattern] abbrev yourBeginCombatFromGraveyard : TriggerEvent := .step .yourBeginCombatFromGraveyard
@[match_pattern] abbrev opponentBeginCombat : TriggerEvent := .step .opponentBeginCombat
@[match_pattern] abbrev eachBeginCombat : TriggerEvent := .step .eachBeginCombat
@[match_pattern] abbrev yourEndStep : TriggerEvent := .step .yourEndStep
@[match_pattern] abbrev eachEndStep : TriggerEvent := .step .eachEndStep

-- Spell-cast aliases (CR 601.2i)
@[match_pattern] abbrev castThis : TriggerEvent := .casts .castThis
@[match_pattern] abbrev youCastSpell : TriggerEvent := .casts .youSpell
@[match_pattern] abbrev youCastInstantOrSorcery : TriggerEvent := .casts .youInstantOrSorcery
@[match_pattern] abbrev youCastNoncreature : TriggerEvent := .casts .youNoncreature
@[match_pattern] abbrev youCastFirstNoncreature : TriggerEvent := .casts .youFirstNoncreature
@[match_pattern] abbrev youCastSecondSpell : TriggerEvent := .casts .youSecondSpell
@[match_pattern] abbrev youCastCreature : TriggerEvent := .casts .youCreature
@[match_pattern] abbrev youCastArtifactOrCreature : TriggerEvent := .casts .youArtifactOrCreature
@[match_pattern] abbrev youCastGreen : TriggerEvent := .casts .youGreen
@[match_pattern] abbrev youCastColor (color : Color) : TriggerEvent := .casts (.youColor color)
@[match_pattern] abbrev youCastColorFromHand (color : Color) : TriggerEvent := .casts (.youColorFromHand color)
@[match_pattern] abbrev youCastVillain : TriggerEvent := .casts .youVillain
@[match_pattern] abbrev youCastWithTreasure : TriggerEvent := .casts .youWithTreasure
@[match_pattern] abbrev youCastPreparedSpell : TriggerEvent := .casts .youPreparedSpell
@[match_pattern] abbrev youCastTargetingCreatureYouControl : TriggerEvent := .casts .youTargetingCreatureYouControl
@[match_pattern] abbrev youCastEquipmentOrTargetingCreatureYouControl : TriggerEvent := .casts .youEquipmentOrTargetingCreatureYouControl
@[match_pattern] abbrev youCastTargetingCreature : TriggerEvent := .casts .youTargetingCreature
@[match_pattern] abbrev youCastInstantSorceryTargetingArtifactOrLand : TriggerEvent := .casts .youInstantSorceryTargetingArtifactOrLand
@[match_pattern] abbrev youCastTargetingOpponentOrTheirCreature : TriggerEvent := .casts .youTargetingOpponentOrTheirCreature
@[match_pattern] abbrev opponentCastsSpell : TriggerEvent := .casts .opponentSpell
@[match_pattern] abbrev opponentCastsFirstNoncreature : TriggerEvent := .casts .opponentFirstNoncreature
@[match_pattern] abbrev opponentCastsSpellMvAtMost (n : Nat) : TriggerEvent := .casts (.opponentSpellMvAtMost n)
@[match_pattern] abbrev opponentCastsMatchingParity : TriggerEvent := .casts .opponentMatchingParity
@[match_pattern] abbrev anyPlayerCastsSecondSpell : TriggerEvent := .casts .anyPlayerSecondSpell
@[match_pattern] abbrev spellTargetsSource : TriggerEvent := .casts .spellTargetsSource

-- Combat declaration aliases (CR 508.2 / 509.5c)
@[match_pattern] abbrev attacking : TriggerEvent := .combat .sourceAttacks
@[match_pattern] abbrev attack : TriggerEvent := .combat .sourceAttacks
@[match_pattern] abbrev youAttack : TriggerEvent := .combat .youAttack
@[match_pattern] abbrev youAttackWithElves : TriggerEvent := .combat .youAttackWithElves
@[match_pattern] abbrev youAttackWithTwoOrMore : TriggerEvent := .combat .youAttackWithTwoOrMore
@[match_pattern] abbrev youAttackWithTotalPower : TriggerEvent := .combat .youAttackWithTotalPower
@[match_pattern] abbrev equippedAttacks : TriggerEvent := .combat .equippedAttacks
@[match_pattern] abbrev equippedAttacksAlone : TriggerEvent := .combat .equippedAttacksAlone
@[match_pattern] abbrev equippedCreatureYouControlAttacks : TriggerEvent := .combat .equippedCreatureYouControlAttacks
@[match_pattern] abbrev creatureYouControlAttacks : TriggerEvent := .combat .creatureYouControlAttacks
@[match_pattern] abbrev creatureYouControlAttacksAlone : TriggerEvent := .combat .creatureYouControlAttacksAlone
@[match_pattern] abbrev creatureYouControlAttacksPlayerAlone : TriggerEvent := .combat .creatureYouControlAttacksPlayerAlone
@[match_pattern] abbrev creatureAttacksYouOrYourPlaneswalker : TriggerEvent := .combat .creatureAttacksYouOrYourPlaneswalker
@[match_pattern] abbrev creaturesAttackYourOpponent : TriggerEvent := .combat .creaturesAttackYourOpponent
@[match_pattern] abbrev merfolkAttackPlayer : TriggerEvent := .combat .merfolkAttackPlayer
@[match_pattern] abbrev zombieTokenAttacks : TriggerEvent := .combat .zombieTokenAttacks
@[match_pattern] abbrev sphinxesAttack : TriggerEvent := .combat .sphinxesAttack
@[match_pattern] abbrev enchantedAttacksOrBlocks : TriggerEvent := .combat .enchantedAttacksOrBlocks
@[match_pattern] abbrev becomesBlocked : TriggerEvent := .combat .becomesBlocked
@[match_pattern] abbrev opponentSmallCreatureBlocks : TriggerEvent := .combat .opponentSmallCreatureBlocks

-- Damage aliases (CR 510.2 / 120)
@[match_pattern] abbrev dealsCombatDamageToPlayer : TriggerEvent := .damage .sourceCombatToPlayer
@[match_pattern] abbrev combatDamageToPlayer : TriggerEvent := .damage .sourceCombatToPlayer
@[match_pattern] abbrev dealsCombatDamageToPlayerOrBattle : TriggerEvent := .damage .sourceCombatToPlayerOrBattle
@[match_pattern] abbrev combatDamageToPlayerOrBattle : TriggerEvent := .damage .sourceCombatToPlayerOrBattle
@[match_pattern] abbrev equippedDealsCombatDamageToPlayer : TriggerEvent := .damage .equippedCombatToPlayer
@[match_pattern] abbrev armyYouControlCombatDamage : TriggerEvent := .damage .armyYouControlCombat
@[match_pattern] abbrev combatDamageToYou : TriggerEvent := .damage .combatToYou
@[match_pattern] abbrev opponentsDealtCombatDamageYourTurn : TriggerEvent := .damage .opponentsDealtCombatYourTurn
@[match_pattern] abbrev heroesDealDamageToPlayer : TriggerEvent := .damage .heroesDealToPlayer
@[match_pattern] abbrev sourceDealtDamage : TriggerEvent := .damage .sourceDealt
@[match_pattern] abbrev sourceDealtNoncombatDamage : TriggerEvent := .damage .sourceDealtNoncombat
@[match_pattern] abbrev creatureYouControlDealtDamage : TriggerEvent := .damage .creatureYouControlDealt
@[match_pattern] abbrev opponentsDealtNoncombatDamage : TriggerEvent := .damage .opponentsDealtNoncombat
@[match_pattern] abbrev opponentDealtNoncombatDamage : TriggerEvent := .damage .opponentDealtNoncombat

-- Draw aliases (CR 121)
@[match_pattern] abbrev youDraw : TriggerEvent := .draws .youCard
@[match_pattern] abbrev youDrawSecondCard : TriggerEvent := .draws .youSecondCard
@[match_pattern] abbrev youDrawSecond : TriggerEvent := .draws .youSecondCard
@[match_pattern] abbrev opponentDrawsExceptFirstDrawStep : TriggerEvent := .draws .opponentExceptFirstDrawStep
@[match_pattern] abbrev opponentDrawsExceptFirst : TriggerEvent := .draws .opponentExceptFirstDrawStep
@[match_pattern] abbrev opponentDrawsSecondCard : TriggerEvent := .draws .opponentSecondCard
@[match_pattern] abbrev opponentDrawsSecond : TriggerEvent := .draws .opponentSecondCard
@[match_pattern] abbrev anyPlayerDrawsSecond : TriggerEvent := .draws .anyPlayerSecond

-- Discard & cycle aliases (CR 701.8 / 702.29)
@[match_pattern] abbrev youDiscard : TriggerEvent := .discards .youCard
@[match_pattern] abbrev youDiscardOne : TriggerEvent := .discards .youOne
@[match_pattern] abbrev youDiscardThis : TriggerEvent := .discards .youThis
@[match_pattern] abbrev playerDiscards : TriggerEvent := .discards .playerCards
@[match_pattern] abbrev youCycle : TriggerEvent := .discards .youCycle

-- Tap aliases (CR 701.26)
@[match_pattern] abbrev sourceBecomesTapped : TriggerEvent := .taps .source
@[match_pattern] abbrev equippedBecomesTapped : TriggerEvent := .taps .equipped
@[match_pattern] abbrev tappedForTeamwork : TriggerEvent := .taps .forTeamwork
@[match_pattern] abbrev creatureYouControlTapped : TriggerEvent := .taps .creatureYouControl
@[match_pattern] abbrev creaturesYouControlBecomeTapped : TriggerEvent := .taps .creaturesYouControl

-- Counter, proliferate & Saga aliases (CR 122 / 701.34 / 714)
@[match_pattern] abbrev youPutPlusOne : TriggerEvent := .counters .youPutPlusOne
@[match_pattern] abbrev youPutCountersOnGoblinOrcArmy : TriggerEvent := .counters .youPutOnGoblinOrcArmy
@[match_pattern] abbrev youPutLoyaltyCounters : TriggerEvent := .counters .youPutLoyalty
@[match_pattern] abbrev nthPlanCounter (n : Nat) : TriggerEvent := .counters (.nthPlan n)
@[match_pattern] abbrev sagaChapter : TriggerEvent := .counters .sagaChapter
@[match_pattern] abbrev finalSagaChapterResolves : TriggerEvent := .counters .finalSagaChapterResolves
@[match_pattern] abbrev youProliferate : TriggerEvent := .counters .youProliferate

-- Player/object action aliases (CR 603.2)
@[match_pattern] abbrev youActivateCreatureAbility : TriggerEvent := .action .youActivateCreatureAbility
@[match_pattern] abbrev youActivateLoyaltyAbility : TriggerEvent := .action .youActivateLoyaltyAbility
@[match_pattern] abbrev opponentActivatesLoyaltyAbility : TriggerEvent := .action .opponentActivatesLoyaltyAbility
@[match_pattern] abbrev becomesTarget : TriggerEvent := .action .becomesTarget
@[match_pattern] abbrev youTargetSomething : TriggerEvent := .action .youTargetSomething
@[match_pattern] abbrev youSacrificeToken : TriggerEvent := .action .youSacrificeToken
@[match_pattern] abbrev bolgSacrificedForReflexive : TriggerEvent := .action .bolgSacrificedForReflexive
@[match_pattern] abbrev youCreateCreatureTokens : TriggerEvent := .action .youCreateCreatureTokens
@[match_pattern] abbrev youGainLife : TriggerEvent := .action .youGainLife
@[match_pattern] abbrev playerLosesLife : TriggerEvent := .action .playerLosesLife
@[match_pattern] abbrev youScry : TriggerEvent := .action .youScry
@[match_pattern] abbrev youScryOrSurveil : TriggerEvent := .action .youScryOrSurveil
@[match_pattern] abbrev theRingTemptsYou : TriggerEvent := .action .theRingTemptsYou
@[match_pattern] abbrev youChooseRingBearer : TriggerEvent := .action .youChooseRingBearer

-- Disjunctive composite events
/-- Whenever this creature enters or attacks. -/
def enterOrAttack : TriggerEvent := .or .enter .attack

/-- Whenever you cast a green spell and whenever a Forest you control enters. -/
def castGreenOrForestEnters : TriggerEvent :=
  .or .youCastGreen .forestYouControlEnters

/-- When this enters and whenever an opponent draws except their first draw-step card. -/
def enterOrOpponentDrawsExceptFirst : TriggerEvent :=
  .or .enter .opponentDrawsExceptFirst

/-- Events this trigger watches. -/
def events : TriggerEvent → Array TriggerEvent
  | .or a b => a.events ++ b.events
  | .cascade | .fromEffect => #[]
  | e => #[e]

/-- Oracle wording plus how Game queues this event. Exhaustive so a new event
is a compile error here rather than silently matching `When this occurs` with
`Whenever`, or restating the stack label and CR 603.3d check at every queue
site. -/
structure Spec where
  clause : String
  isWhenever : Bool := true
  /-- Log label when this event is put on the stack. -/
  label : String
  /-- Remove the ability when it requires a target and has none (CR 603.3d). -/
  checkTargets : Bool := true
  /-- Trigger condition is another ability triggering (CR 603.3b part 2). -/
  isAnotherAbilityTriggering : Bool := false
deriving Repr, Inhabited, BEq

/-- Classification of this event. `clause`, `isWhenever`, `label`, and
`checkTargets` read this table. -/
def spec : TriggerEvent → Spec
  | .attacking =>
    { clause := "this creature attacks", label := "attack trigger" }
  | .becomesBlocked =>
    { clause := "this creature becomes blocked", label := "becomes-blocked trigger",
      checkTargets := false }
  | .entering =>
    { clause := "this permanent enters", isWhenever := false, label := "enters trigger" }
  | .landYouControlEnters =>
    { clause := "a land you control enters", label := "landfall trigger" }
  | .dying =>
    { clause := "this creature dies", isWhenever := false, label := "dies trigger" }
  | .youCastInstantOrSorcery =>
    { clause := "you cast an instant or sorcery spell", label := "cast trigger",
      checkTargets := false }
  | .youAttackWithElves =>
    { clause := "you attack with one or more Elves", label := "attack trigger",
      checkTargets := false }
  | .youScry =>
    { clause := "you scry", label := "scry trigger", checkTargets := false }
  | .anotherElfYouControlEnters =>
    { clause := "another Elf you control enters", label := "Elf-enters trigger",
      checkTargets := false }
  | .oneOrMoreOtherCreaturesDie =>
    { clause := "one or more other creatures die", label := "other-creatures-die trigger",
      checkTargets := false }
  | .leaving =>
    { clause := "this creature leaves the battlefield", isWhenever := false,
      label := "leaves trigger", checkTargets := false }
  | .youDraw =>
    { clause := "you draw a card", label := "draw trigger", checkTargets := false }
  | .youDrawSecondCard =>
    { clause := "you draw your second card each turn", label := "second-card trigger",
      checkTargets := false }
  | .youAttackWithTwoOrMore =>
    { clause := "two or more creatures you control attack a player",
      label := "attack trigger" }
  | .dealsCombatDamageToPlayer =>
    { clause := "this deals combat damage to a player", label := "combat-damage trigger",
      checkTargets := false }
  | .yourEndStep =>
    { clause := "the beginning of your end step", isWhenever := false,
      label := "end-step trigger", checkTargets := false }
  | .anotherCreatureYouControlEnters =>
    { clause := "another creature you control enters", label := "creature-enters trigger",
      checkTargets := false }
  | .yourBeginCombat =>
    { clause := "the beginning of combat on your turn", isWhenever := false,
      label := "begin-combat trigger", checkTargets := false }
  | .youAttack =>
    { clause := "you attack", label := "attack trigger", checkTargets := false }
  | .youCastNoncreature =>
    { clause := "you cast a noncreature spell", label := "cast trigger",
      checkTargets := false }
  | .yourUpkeep =>
    { clause := "the beginning of your upkeep", isWhenever := false,
      label := "upkeep trigger", checkTargets := false }
  | .artifactYouControlEnters =>
    { clause := "an artifact you control enters", label := "artifact-enters trigger",
      checkTargets := false }
  | .opponentCastsFirstNoncreature =>
    { clause := "an opponent casts their first noncreature spell each turn",
      label := "opponent-cast trigger", checkTargets := false }
  | .anyPlayerCastsSecondSpell =>
    { clause := "a player casts their second spell each turn",
      label := "second-spell trigger", checkTargets := false }
  | .yourFirstMain =>
    { clause := "the beginning of your first main phase", isWhenever := false,
      label := "main-phase trigger", checkTargets := false }
  | .thisOrNontokenSubtypeYouControlEnters =>
    { clause := "this or another nontoken creature you control enters",
      label := "subtype-enters trigger", checkTargets := false }
  | .becomesTarget =>
    { clause := "this creature becomes the target of a spell or ability an opponent controls",
      label := "becomes-target trigger", checkTargets := false }
  | .eachEndStep =>
    { clause := "the beginning of each end step", isWhenever := false,
      label := "end-step trigger", checkTargets := false }
  | .eachBeginCombat =>
    { clause := "the beginning of each combat", isWhenever := false,
      label := "begin-combat trigger", checkTargets := false }
  | .youCastGreen =>
    { clause := "you cast a green spell", label := "cast trigger" }
  | .forestYouControlEnters =>
    { clause := "a Forest you control enters", label := "forest-enters trigger" }
  | .anotherSubtypeOrEquipmentYouControlEnters =>
    { clause := "another Dwarf or Equipment you control enters",
      label := "dwarf-or-equipment trigger", checkTargets := false }
  | .youCastWithTreasure =>
    { clause := "you cast a spell, if mana from a Treasure was spent to cast it",
      label := "treasure-cast trigger", checkTargets := false }
  | .thisOrAnotherSubtypeYouControlEnters =>
    { clause := "this or another creature you control enters",
      label := "subtype-enters trigger", checkTargets := false }
  | .dealsCombatDamageToPlayerOrBattle =>
    { clause := "this deals combat damage to a player or battle",
      label := "combat-damage trigger" }
  | .theRingTemptsYou =>
    { clause := "the Ring tempts you", label := "Ring-tempts trigger",
      checkTargets := false }
  | .youChooseRingBearer =>
    { clause := "you choose a creature as your Ring-bearer",
      label := "Ring-bearer trigger", checkTargets := false }
  | .equippedAttacksAlone =>
    { clause := "equipped creature attacks alone",
      label := "attacks-alone trigger", checkTargets := false }
  | .tokenYouControlEnters =>
    { clause := "a token you control enters", label := "token-enters trigger",
      checkTargets := false }
  | .youActivateCreatureAbility =>
    { clause := "you activate an ability of a creature",
      label := "activate-creature trigger", checkTargets := false }
  | .equippedAttacks =>
    { clause := "equipped creature attacks",
      label := "equipped-attacks trigger", checkTargets := false }
  | .opponentDrawsExceptFirstDrawStep =>
    { clause := "an opponent draws a card except the first one they draw in each of their draw steps",
      label := "opponent-draw trigger" }
  | .opponentDrawsSecondCard =>
    { clause := "an opponent draws their second card each turn",
      label := "opponent-second-card trigger", checkTargets := false }
  | .youAttackWithTotalPower =>
    { clause := "you attack with creatures with total power 12 or greater",
      label := "total-power-attack trigger", checkTargets := false }
  | .eaglesCreateBirds =>
    { clause := "the beginning of the next upkeep", isWhenever := false,
      label := "delayed Bird Soldier trigger", checkTargets := false }
  | .bolgSacrificedForReflexive =>
    { clause := "you sacrifice a creature this way", isWhenever := false,
      label := "reflexive trigger" }
  | .youCastColor c =>
    { clause := s!"you cast a {c} spell", label := "cast-color trigger",
      checkTargets := false }
  | .opponentCastsMatchingParity =>
    { clause := "an opponent casts a spell with mana value of the chosen quality",
      label := "parity-cast trigger", checkTargets := false }
  | .creatureCardLeavesYourGy =>
    { clause := "a creature card leaves your graveyard",
      label := "leaves-graveyard trigger", checkTargets := false }
  | .youCastCreature =>
    { clause := "you cast a creature spell", label := "cast-creature trigger" }
  | .mountainYouControlEnters =>
    { clause := "a Mountain you control enters", label := "mountain-enters trigger" }
  | .sourceDealtNoncombatDamage =>
    { clause := "this is dealt noncombat damage",
      label := "noncombat-damage trigger", checkTargets := false }
  | .opponentCastsSpell =>
    { clause := "an opponent casts a spell", label := "opponent-cast trigger",
      checkTargets := false }
  | .armyYouControlCombatDamage =>
    { clause := "an Army you control deals combat damage to a player",
      label := "army-combat-damage trigger", checkTargets := false }
  | .sagaChapter =>
    { clause := "a lore counter is put on this Saga", isWhenever := false,
      label := "saga chapter", checkTargets := true }
  | .finalSagaChapterResolves =>
    { clause := "the final chapter ability of a Saga you control resolves",
      label := "saga-chapter trigger", checkTargets := false }
  | .combatDamageToYou =>
    { clause := "one or more creatures deal combat damage to you",
      label := "combat-damage-to-you trigger", checkTargets := false }
  | .youCastSecondSpell =>
    { clause := "you cast your second spell each turn",
      label := "second-spell trigger", checkTargets := false }
  | .youSacrificeToken =>
    { clause := "you sacrifice a token", label := "sacrifice-token trigger" }
  | .playerLosesLife =>
    { clause := "a player loses life", label := "lose-life trigger",
      checkTargets := false }
  | .youPutCountersOnGoblinOrcArmy =>
    { clause := "you put one or more counters on a Goblin, Orc, or Army you control",
      label := "put-counters trigger" }
  | .anotherGoblinOrcArmyDies =>
    { clause := "another Goblin, Orc, or Army you control dies",
      label := "army-dies trigger", checkTargets := false }
  | .nontokenYouControlDies =>
    { clause := "a nontoken creature you control dies",
      label := "nontoken-dies trigger", checkTargets := false }
  | .equippedDealsCombatDamageToPlayer =>
    { clause := "equipped creature deals combat damage to a player",
      label := "equipped-combat-damage trigger", checkTargets := false }
  | .creatureYouControlAttacksAlone =>
    { clause := "a creature you control attacks alone",
      label := "attacks-alone trigger" }
  | .tappedForTeamwork =>
    { clause := "this becomes tapped to pay a teamwork cost",
      label := "teamwork-tap trigger", checkTargets := false }
  | .creatureYouControlEnters =>
    { clause := "a creature you control enters",
      label := "creature-enters trigger", checkTargets := false }
  | .subtypeYouControlEnters subtype =>
    { clause := s!"a {subtype} you control enters",
      label := "subtype-enters trigger", checkTargets := false }
  | .creaturesYouControlBecomeTapped =>
    { clause := "one or more creatures you control become tapped",
      label := "tap trigger", checkTargets := false }
  | .creatureCardsPutIntoYourGy =>
    { clause := "one or more creature cards are put into your graveyard from anywhere",
      label := "graveyard trigger", checkTargets := false }
  | .youCastColorFromHand color =>
    { clause := s!"you cast a {color.englishName} spell from your hand",
      label := "cast trigger", checkTargets := false }
  | .sourceDealtDamage =>
    { clause := "this is dealt damage",
      label := "dealt-damage trigger", checkTargets := false }
  | .nthPlanCounter n =>
    let ord :=
      match n with
      | 1 => "first" | 2 => "second" | 3 => "third" | 4 => "fourth"
      | 5 => "fifth" | 6 => "sixth" | 7 => "seventh" | 8 => "eighth"
      | _ => s!"{n}th"
    { clause := s!"the {ord} plan counter is put on this enchantment",
      isWhenever := false, label := "plan trigger" }
  | .youCastVillain =>
    { clause := "you cast a Villain spell", label := "cast trigger",
      checkTargets := false }
  | .youCastTargetingCreatureYouControl =>
    { clause := "you cast a spell that targets a creature you control",
      label := "cast trigger", checkTargets := false }
  | .youCastTargetingCreature =>
    { clause := "you cast a spell that targets one or more creatures",
      label := "cast trigger", checkTargets := false }
  | .youCastInstantSorceryTargetingArtifactOrLand =>
    { clause := "you cast an instant or sorcery spell that targets an artifact or land",
      label := "cast trigger", checkTargets := false }
  | .youCastTargetingOpponentOrTheirCreature =>
    { clause := "you cast a spell that targets an opponent or a creature an opponent controls",
      label := "cast trigger", checkTargets := false }
  | .youCastFirstNoncreature =>
    { clause := "you cast your first noncreature spell each turn",
      label := "cast trigger", checkTargets := false }
  | .youActivateLoyaltyAbility =>
    { clause := "you activate a loyalty ability",
      label := "loyalty trigger", checkTargets := false }
  | .eachUpkeep =>
    { clause := "the beginning of each player's upkeep", isWhenever := false,
      label := "upkeep trigger", checkTargets := false }
  | .youScryOrSurveil =>
    { clause := "you scry or surveil", label := "scry trigger", checkTargets := false }
  | .opponentsDealtCombatDamageYourTurn =>
    { clause := "one or more of your opponents are dealt combat damage during your turn",
      isWhenever := false, label := "combat-damage trigger", checkTargets := false }
  | .creatureYouControlDies =>
    { clause := "a creature you control dies", label := "dies trigger", checkTargets := false }
  | .eachOpponentDrawStep =>
    { clause := "the beginning of each opponent's draw step", isWhenever := false,
      label := "draw-step trigger", checkTargets := false }
  | .youCastSpell =>
    { clause := "you cast a spell", label := "cast trigger", checkTargets := false }
  | .youDiscard =>
    { clause := "you discard a card", label := "discard trigger", checkTargets := false }
  | .youPutPlusOne =>
    { clause := "you put a +1/+1 counter on a creature",
      label := "counter trigger", checkTargets := false }
  | .youGainLife =>
    { clause := "you gain life", label := "gain-life trigger", checkTargets := false }
  | .anyPlayerDrawsSecond =>
    { clause := "a player draws their second card each turn",
      label := "second-card trigger", checkTargets := false }
  | .spellTargetsSource =>
    { clause := "a player casts a spell that targets this",
      label := "becomes-target trigger", checkTargets := false }
  | .youTargetSomething =>
    { clause := "a player or permanent becomes the target of an ability you control",
      label := "you-target trigger", checkTargets := false }
  | .equipmentYouControlEnters =>
    { clause := "an Equipment you control enters",
      label := "equipment-enters trigger", checkTargets := false }
  | .anotherVillainOrArtifactEnters =>
    { clause := "another Villain and/or artifact you control enters",
      label := "villain-or-artifact trigger", checkTargets := false }
  | .anotherVillainEnters =>
    { clause := "another Villain you control enters",
      label := "villain-enters trigger", checkTargets := false }
  | .anotherArtifactEnters =>
    { clause := "another artifact you control enters",
      label := "artifact-enters trigger", checkTargets := false }
  | .anotherNontokenHeroEnters =>
    { clause := "another nontoken Hero you control enters",
      label := "hero-enters trigger", checkTargets := false }
  | .anotherNontokenArtifactEnters =>
    { clause := "another nontoken artifact you control enters",
      label := "artifact-enters trigger", checkTargets := false }
  | .anotherNonlandReturned =>
    { clause := "another nonland permanent you control is returned to its owner's hand",
      label := "return trigger", checkTargets := false }
  | .villainYouControlDies =>
    { clause := "a Villain you control dies",
      label := "villain-dies trigger", checkTargets := false }
  | .attackingCreatureYouControlDies =>
    { clause := "an attacking creature you control dies",
      label := "attacker-dies trigger", checkTargets := false }
  | .equippedCreatureYouControlAttacks =>
    { clause := "an equipped creature you control attacks",
      label := "equipped-attacks trigger", checkTargets := false }
  | .enchantedAttacksOrBlocks =>
    { clause := "enchanted creature attacks or blocks",
      label := "enchanted-combat trigger", checkTargets := false }
  | .creatureYouControlTapped =>
    { clause := "a creature you control becomes tapped during your turn",
      label := "tap trigger", checkTargets := false }
  | .creatureYouControlDealtDamage =>
    { clause := "a creature you control is dealt damage",
      label := "dealt-damage trigger", checkTargets := false }
  | .heroesDealDamageToPlayer =>
    { clause := "one or more Heroes you control deal damage to a player",
      label := "hero-damage trigger", checkTargets := false }
  | .merfolkAttackPlayer =>
    { clause := "one or more Merfolk you control attack a player",
      label := "merfolk-attack trigger", checkTargets := false }
  | .enchantedControllerUpkeep =>
    { clause := "the beginning of the upkeep of enchanted creature's controller",
      isWhenever := false, label := "enchanted-upkeep trigger", checkTargets := false }
  | .sourceBecomesTapped =>
    { clause := "this becomes tapped", label := "becomes-tapped trigger",
      checkTargets := false }
  | .equippedBecomesTapped =>
    { clause := "equipped creature becomes tapped", label := "equipped-tapped trigger",
      checkTargets := false }
  | .castThis =>
    { clause := "you cast this spell", isWhenever := false, label := "cast trigger" }
  | .enchantedDies =>
    { clause := "enchanted creature dies", isWhenever := false, label := "dies trigger" }
  | .youDiscardThis =>
    { clause := "you discard this card", isWhenever := false, label := "discard trigger" }
  | .yourBeginCombatFromGraveyard =>
    { clause := "the beginning of combat on your turn", isWhenever := false,
      label := "beginning-of-combat trigger" }
  | .eachUpkeepFromGraveyard =>
    { clause := "the beginning of each upkeep", isWhenever := false,
      label := "upkeep trigger" }
  | _ => { clause := "this occurs", label := "triggered ability" }

/-- Oracle “when/whenever” clause after the leading word. -/
def clause (e : TriggerEvent) : String :=
  e.spec.clause

/-- `Whenever` rather than one-shot `When` (enters / dies). -/
def isWhenever (e : TriggerEvent) : Bool :=
  e.spec.isWhenever

/-- Log label when this event is put on the stack. -/
def label (e : TriggerEvent) : String :=
  e.spec.label

/-- True when Game removes this trigger for lack of a legal target (CR 603.3d). -/
def checkTargets (e : TriggerEvent) : Bool :=
  e.spec.checkTargets

/-- True when this event is “another ability triggering” (CR 603.3b part 2). -/
def isAnotherAbilityTriggering (e : TriggerEvent) : Bool :=
  e.spec.isAnotherAbilityTriggering

end TriggerEvent

namespace SharedTriggerWhen
export TriggerEvent (
  enters leaves step casts combat damage draws discards taps counters action «or» cascade fromEffect fra
  entering enter landYouControlEnters forestYouControlEnters mountainYouControlEnters
  artifactYouControlEnters anotherArtifactEnters anotherNontokenArtifactEnters
  equipmentYouControlEnters tokenYouControlEnters creatureYouControlEnters
  anotherCreatureYouControlEnters anotherNontokenCreatureYouControlEnters
  thisOrAnotherCreatureYouControlEnters anotherCreatureOrPlaneswalkerYouControlEnters
  creatureOpponentControlsEnters creatureYouControlPowerAtLeastEnters
  anotherElfYouControlEnters anotherVillainEnters anotherVillainOrArtifactEnters
  anotherNontokenHeroEnters subtypeYouControlEnters
  thisOrAnotherSubtypeYouControlEnters thisOrAnotherSubtypeEnters
  thisOrNontokenSubtypeYouControlEnters thisOrNontokenSubtypeEnters
  anotherSubtypeOrEquipmentYouControlEnters anotherSubtypeOrEquipmentEnters
  dying dies leaving enchantedDies creatureYouControlDies nontokenYouControlDies
  nontokenCreatureYouControlDies attackingCreatureYouControlDies villainYouControlDies
  anotherGoblinOrcArmyDies anotherCreatureOrPlaneswalkerYouControlDies
  oneOrMoreOtherCreaturesDie creatureYouControlLeaves anotherNonlandReturned
  creatureCardLeavesYourGy creatureCardsPutIntoYourGy
  yourUpkeep eachUpkeep eachUpkeepFromGraveyard enchantedControllerUpkeep eaglesCreateBirds
  eachOpponentDrawStep yourFirstMain yourBeginCombat yourBeginCombatFromGraveyard
  opponentBeginCombat eachBeginCombat yourEndStep eachEndStep
  castThis youCastSpell youCastInstantOrSorcery youCastNoncreature youCastFirstNoncreature
  youCastSecondSpell youCastCreature youCastArtifactOrCreature youCastGreen
  youCastColor youCastColorFromHand youCastVillain youCastWithTreasure youCastPreparedSpell
  youCastTargetingCreatureYouControl youCastEquipmentOrTargetingCreatureYouControl
  youCastTargetingCreature youCastInstantSorceryTargetingArtifactOrLand
  youCastTargetingOpponentOrTheirCreature opponentCastsSpell opponentCastsFirstNoncreature
  opponentCastsSpellMvAtMost opponentCastsMatchingParity anyPlayerCastsSecondSpell
  spellTargetsSource
  attacking attack youAttack youAttackWithElves youAttackWithTwoOrMore
  youAttackWithTotalPower equippedAttacks equippedAttacksAlone
  equippedCreatureYouControlAttacks creatureYouControlAttacks
  creatureYouControlAttacksAlone creatureYouControlAttacksPlayerAlone
  creatureAttacksYouOrYourPlaneswalker creaturesAttackYourOpponent
  merfolkAttackPlayer zombieTokenAttacks sphinxesAttack
  enchantedAttacksOrBlocks becomesBlocked opponentSmallCreatureBlocks
  dealsCombatDamageToPlayer combatDamageToPlayer
  dealsCombatDamageToPlayerOrBattle combatDamageToPlayerOrBattle
  equippedDealsCombatDamageToPlayer armyYouControlCombatDamage combatDamageToYou
  opponentsDealtCombatDamageYourTurn heroesDealDamageToPlayer
  sourceDealtDamage sourceDealtNoncombatDamage creatureYouControlDealtDamage
  opponentsDealtNoncombatDamage opponentDealtNoncombatDamage
  youDraw youDrawSecondCard youDrawSecond
  opponentDrawsExceptFirstDrawStep opponentDrawsExceptFirst
  opponentDrawsSecondCard opponentDrawsSecond anyPlayerDrawsSecond
  youDiscard youDiscardOne youDiscardThis playerDiscards youCycle
  sourceBecomesTapped equippedBecomesTapped tappedForTeamwork
  creatureYouControlTapped creaturesYouControlBecomeTapped
  youPutPlusOne youPutCountersOnGoblinOrcArmy youPutLoyaltyCounters
  nthPlanCounter sagaChapter finalSagaChapterResolves youProliferate
  youActivateCreatureAbility youActivateLoyaltyAbility opponentActivatesLoyaltyAbility
  becomesTarget youTargetSomething youSacrificeToken bolgSacrificedForReflexive
  youCreateCreatureTokens youGainLife playerLosesLife youScry youScryOrSurveil
  theRingTemptsYou youChooseRingBearer
  enterOrAttack castGreenOrForestEnters enterOrOpponentDrawsExceptFirst
)
abbrev events (w : SharedTriggerWhen) : Array TriggerEvent := TriggerEvent.events w
end SharedTriggerWhen

namespace FraEvent
export TriggerEvent (
  castThis opponentsDealtNoncombatDamage opponentDealtNoncombatDamage
  youPutLoyaltyCounters enchantedDies creatureYouControlAttacks
  creatureYouControlAttacksPlayerAlone opponentCastsSpellMvAtMost
  youCastPreparedSpell anotherCreatureOrPlaneswalkerYouControlEnters
  thisOrAnotherCreatureYouControlEnters anotherNontokenCreatureYouControlEnters
  creatureOpponentControlsEnters opponentActivatesLoyaltyAbility
  anotherCreatureOrPlaneswalkerYouControlDies playerDiscards youDiscardThis
  creatureYouControlPowerAtLeastEnters youCastArtifactOrCreature
  youCastEquipmentOrTargetingCreatureYouControl opponentSmallCreatureBlocks
  yourBeginCombatFromGraveyard eachUpkeepFromGraveyard
  creatureAttacksYouOrYourPlaneswalker creaturesAttackYourOpponent
  creatureYouControlLeaves youProliferate youDiscardOne
  nontokenCreatureYouControlDies opponentBeginCombat youCreateCreatureTokens
  zombieTokenAttacks sphinxesAttack youCycle
)
end FraEvent

end Mtg.Engine
