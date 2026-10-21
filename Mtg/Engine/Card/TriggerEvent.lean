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
  | simpleEnters (landOrEquipment : Bool := false) (tokenOrEquipment : Bool := false)
  | landSubtypeYouControl (subtype : String)
  | artifactYouControl (another : Bool := false) (nontoken : Bool := false)
  | creatureYouControl (another : Bool := false) (nontoken : Bool := false) (thisOrAnother : Bool := false)
  | creatureYouControlPowerAtLeast (n : Int)
  | subtypeYouControl (subtype : String) (another : Bool := false) (nontoken : Bool := false)
  | thisOrAnotherSubtypeYouControl (nontoken : Bool := false)
  | otherPermanentEnters (oppCreatureOrVillain : Bool := false) (villainOrDwarfEquip : Bool := false)
deriving Repr, Inhabited, BEq, DecidableEq

namespace EntersEvent
@[match_pattern] abbrev source : EntersEvent := .simpleEnters false false
@[match_pattern] abbrev landYouControl : EntersEvent := .simpleEnters true false
@[match_pattern] abbrev tokenYouControl : EntersEvent := .simpleEnters false true
@[match_pattern] abbrev equipmentYouControl : EntersEvent := .simpleEnters true true
@[match_pattern] abbrev anotherCreatureOrPlaneswalkerYouControl : EntersEvent := .otherPermanentEnters false false
@[match_pattern] abbrev creatureOpponentControls : EntersEvent := .otherPermanentEnters true false
@[match_pattern] abbrev anotherVillainOrArtifact : EntersEvent := .otherPermanentEnters true true
@[match_pattern] abbrev anotherSubtypeOrEquipmentYouControl : EntersEvent := .otherPermanentEnters false true
end EntersEvent

/-- Which zone-leaving or graveyard-entering event causes `TriggerEvent.leaves` to fire (CR 603.6c / 700.4). -/
inductive LeavesEvent where
  | source (diesOnly : Bool := true)
  | creatureYouControlDies (nontoken : Bool := false) (attacking : Bool := false) (includeSelf : Bool := false)
  | subtypeYouControlDies (subtypes : Array String)
  | anotherNonlandReturned
  | creatureCardYourGy (leaves : Bool := true)
  | permanentDiesOrLeaves (otherDiesOrBatch : Bool := false) (batchOrLeaves : Bool := false)
deriving Repr, Inhabited, BEq, DecidableEq

namespace LeavesEvent
@[match_pattern] abbrev enchantedDies : LeavesEvent := .permanentDiesOrLeaves false false
@[match_pattern] abbrev anotherCreatureOrPlaneswalkerYouControlDies : LeavesEvent := .permanentDiesOrLeaves true false
@[match_pattern] abbrev oneOrMoreOtherCreaturesDie : LeavesEvent := .permanentDiesOrLeaves true true
@[match_pattern] abbrev creatureYouControlLeaves : LeavesEvent := .permanentDiesOrLeaves false true
end LeavesEvent

/-- Which phase or step beginning causes `TriggerEvent.step` to fire (CR 603.2b). -/
inductive StepEvent where
  | upkeep (enchantedController : Bool := false)
  | eachUpkeep (fromGraveyard : Bool := false)
  | fixedStep (oppDrawStep : Bool := false) (firstMain : Bool := false)
  | yourBeginCombat (fromGraveyard : Bool := false)
  | otherBeginCombat (each : Bool := false)
  | endStep (each : Bool := false)
deriving Repr, Inhabited, BEq, DecidableEq

namespace StepEvent
@[match_pattern] abbrev eaglesCreateBirds : StepEvent := .fixedStep false false
@[match_pattern] abbrev eachOpponentDrawStep : StepEvent := .fixedStep true false
@[match_pattern] abbrev yourFirstMain : StepEvent := .fixedStep false true
end StepEvent

/-- Which spell being cast causes `TriggerEvent.casts` to fire (CR 601.2i). -/
inductive CastEvent where
  | spell (opponent : Bool := false)
  | noncreature (firstOnly : Bool := false) (opponent : Bool := false)
  | secondSpell (anyPlayer : Bool := false)
  | youCreature (orArtifact : Bool := false)
  | youColor (color : Color) (fromHand : Bool := false)
  | opponentSpellMvAtMost (n : Nat)
  | youSpecialCast (greenOrPrepared : Bool := false) (treasureOrPrepared : Bool := false)
  | castThisOrVillainOrParity (villainOrTargetsSource : Bool := false) (parityOrTargetsSource : Bool := false)
  | youTargetingCast (orEquipment : Bool := false) (anyCreatureOrArtifactLand : Bool := false) (artifactLandOrOpponent : Bool := false)
deriving Repr, Inhabited, BEq, DecidableEq

namespace CastEvent
@[match_pattern] abbrev youInstantOrSorcery : CastEvent := .youSpecialCast false false
@[match_pattern] abbrev youGreen : CastEvent := .youSpecialCast true false
@[match_pattern] abbrev youWithTreasure : CastEvent := .youSpecialCast false true
@[match_pattern] abbrev youPreparedSpell : CastEvent := .youSpecialCast true true
@[match_pattern] abbrev castThis : CastEvent := .castThisOrVillainOrParity false false
@[match_pattern] abbrev youVillain : CastEvent := .castThisOrVillainOrParity true false
@[match_pattern] abbrev opponentMatchingParity : CastEvent := .castThisOrVillainOrParity false true
@[match_pattern] abbrev spellTargetsSource : CastEvent := .castThisOrVillainOrParity true true
@[match_pattern] abbrev youTargetingCreatureYouControl (orEquipment : Bool := false) : CastEvent :=
  .youTargetingCast orEquipment false false
@[match_pattern] abbrev youTargetingCreature : CastEvent := .youTargetingCast false true false
@[match_pattern] abbrev youInstantSorceryTargetingArtifactOrLand : CastEvent := .youTargetingCast false true true
@[match_pattern] abbrev youTargetingOpponentOrTheirCreature : CastEvent := .youTargetingCast false false true
end CastEvent

/-- Which attacker or blocker declaration causes `TriggerEvent.combat` to fire (CR 508.2 / 509.5c). -/
inductive CombatEvent where
  | youAttack (twoOrMore : Bool := false)
  | youAttackWithTotalPower (n : Int := 12)
  | equippedAttacks (alone : Bool := false) (anyEquippedYouControl : Bool := false)
  | creatureYouControlAttacks (alone : Bool := false) (playerOnly : Bool := false)
  | creaturesAttackPlayer (opponent : Bool := false)
  | subtypeAttacks (subtype : String) (tokenPowerAtLeast6 : Bool := false)
  | selfOrBlockCombat (enchantedOrSmallBlock : Bool := false) (blockedOrSmallBlock : Bool := false)
deriving Repr, Inhabited, BEq, DecidableEq

namespace CombatEvent
@[match_pattern] abbrev sourceAttacks : CombatEvent := .selfOrBlockCombat false false
@[match_pattern] abbrev enchantedAttacksOrBlocks : CombatEvent := .selfOrBlockCombat true false
@[match_pattern] abbrev becomesBlocked : CombatEvent := .selfOrBlockCombat false true
@[match_pattern] abbrev opponentSmallCreatureBlocks : CombatEvent := .selfOrBlockCombat true true
end CombatEvent

/-- Which damage event causes `TriggerEvent.damage` to fire (CR 510.2 / 120). -/
inductive DamageEvent where
  | sourceCombatToPlayer (orBattle : Bool := false)
  | subtypeToPlayer (subtype : String) (combatOnly : Bool := false)
  | sourceDealt (noncombatOnly : Bool := false)
  | opponentDealtNoncombat (batch : Bool := false)
  | fixedDamageEvent (combatToYouOrCreature : Bool := false) (oppCombatOrCreature : Bool := false)
deriving Repr, Inhabited, BEq, DecidableEq

namespace DamageEvent
@[match_pattern] abbrev equippedCombatToPlayer : DamageEvent := .fixedDamageEvent false false
@[match_pattern] abbrev combatToYou : DamageEvent := .fixedDamageEvent true false
@[match_pattern] abbrev opponentsDealtCombatYourTurn : DamageEvent := .fixedDamageEvent false true
@[match_pattern] abbrev creatureYouControlDealt : DamageEvent := .fixedDamageEvent true true
end DamageEvent

/-- Which card draw causes `TriggerEvent.draws` to fire (CR 121). -/
inductive DrawEvent where
  | youCard
  | secondCard (opponent : Bool := false) (anyPlayer : Bool := false)
  | opponentExceptFirstDrawStep
deriving Repr, Inhabited, BEq, DecidableEq

/-- Which discard or cycling action causes `TriggerEvent.discards` to fire (CR 701.8 / 702.29). -/
inductive DiscardEvent where
  | youCard (trackCause : Bool := false)
  | specialDiscard (playerCards : Bool := false) (cycle : Bool := false)
deriving Repr, Inhabited, BEq, DecidableEq

namespace DiscardEvent
@[match_pattern] abbrev youThis : DiscardEvent := .specialDiscard false false
@[match_pattern] abbrev playerCards : DiscardEvent := .specialDiscard true false
@[match_pattern] abbrev youCycle : DiscardEvent := .specialDiscard false true
end DiscardEvent

/-- Which permanent becoming tapped causes `TriggerEvent.taps` to fire (CR 701.26). -/
inductive TapEvent where
  | singleTap (equipped : Bool := false) (teamwork : Bool := false)
  | creatureYouControl (batch : Bool := false)
deriving Repr, Inhabited, BEq, DecidableEq

namespace TapEvent
@[match_pattern] abbrev source : TapEvent := .singleTap false false
@[match_pattern] abbrev equipped : TapEvent := .singleTap true false
@[match_pattern] abbrev forTeamwork : TapEvent := .singleTap false true
end TapEvent

/-- Which counter placement, proliferation, or Saga chapter causes `TriggerEvent.counters` to fire (CR 122 / 701.34 / 714). -/
inductive CounterEvent where
  | counterOrProliferateEvent (armyOrLoyalty : Bool := false) (loyaltyOrProliferate : Bool := false)
  | nthPlan (n : Nat)
  | sagaChapter (n : Nat := 0) (finalResolves : Bool := false)
deriving Repr, Inhabited, BEq, DecidableEq

namespace CounterEvent
@[match_pattern] abbrev youPutPlusOne : CounterEvent := .counterOrProliferateEvent false false
@[match_pattern] abbrev youPutOnGoblinOrcArmy : CounterEvent := .counterOrProliferateEvent true false
@[match_pattern] abbrev youPutLoyalty : CounterEvent := .counterOrProliferateEvent true true
@[match_pattern] abbrev youProliferate : CounterEvent := .counterOrProliferateEvent false true
end CounterEvent

/-- Which player or object game action causes `TriggerEvent.action` to fire (CR 603.2). -/
inductive ActionEvent where
  | activateLoyaltyAbility (opponent : Bool := false)
  | youScry (orSurveil : Bool := false)
  | ringTempts (chooseBearerOnly : Bool := false)
  | abilityOrTargetOrSacAction (becomesTargetOrSac : Bool := false) (youTargetOrSac : Bool := false)
  | tokenOrLifeAction (createTokensOrGainLife : Bool := false) (gainOrLoseLife : Bool := false)
deriving Repr, Inhabited, BEq, DecidableEq

namespace ActionEvent
@[match_pattern] abbrev youActivateCreatureAbility : ActionEvent := .abilityOrTargetOrSacAction false false
@[match_pattern] abbrev becomesTarget : ActionEvent := .abilityOrTargetOrSacAction true false
@[match_pattern] abbrev youTargetSomething : ActionEvent := .abilityOrTargetOrSacAction false true
@[match_pattern] abbrev youSacrificeToken : ActionEvent := .abilityOrTargetOrSacAction true true
@[match_pattern] abbrev bolgSacrificedForReflexive : ActionEvent := .tokenOrLifeAction false false
@[match_pattern] abbrev youCreateCreatureTokens : ActionEvent := .tokenOrLifeAction true false
@[match_pattern] abbrev youGainLife : ActionEvent := .tokenOrLifeAction true true
@[match_pattern] abbrev playerLosesLife : ActionEvent := .tokenOrLifeAction false true
end ActionEvent

end TriggerEvent

/-- When a triggered ability fires (CR 603). -/
inductive TriggerEvent where
  /-- A permanent enters the battlefield (CR 603.6a). -/
  | enters (what : TriggerEvent.EntersEvent := .source)
  /-- A permanent dies, leaves the battlefield, or changes zone (CR 603.6c / 700.4). -/
  | leaves (what : TriggerEvent.LeavesEvent := .source)
  /-- At the beginning of a phase or step (CR 603.2b). -/
  | step (which : TriggerEvent.StepEvent)
  /-- A player casts a spell (CR 601.2i). -/
  | casts (what : TriggerEvent.CastEvent := .spell)
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
@[match_pattern] abbrev forestYouControlEnters : TriggerEvent := .enters (.landSubtypeYouControl "Forest")
@[match_pattern] abbrev mountainYouControlEnters : TriggerEvent := .enters (.landSubtypeYouControl "Mountain")
@[match_pattern] abbrev artifactYouControlEnters : TriggerEvent := .enters (.artifactYouControl false false)
@[match_pattern] abbrev anotherArtifactEnters : TriggerEvent := .enters (.artifactYouControl true false)
@[match_pattern] abbrev anotherNontokenArtifactEnters : TriggerEvent := .enters (.artifactYouControl true true)
@[match_pattern] abbrev equipmentYouControlEnters : TriggerEvent := .enters .equipmentYouControl
@[match_pattern] abbrev tokenYouControlEnters : TriggerEvent := .enters .tokenYouControl
@[match_pattern] abbrev creatureYouControlEnters : TriggerEvent := .enters (.creatureYouControl false false false)
@[match_pattern] abbrev anotherCreatureYouControlEnters : TriggerEvent := .enters (.creatureYouControl true false false)
@[match_pattern] abbrev anotherNontokenCreatureYouControlEnters : TriggerEvent := .enters (.creatureYouControl true true false)
@[match_pattern] abbrev thisOrAnotherCreatureYouControlEnters : TriggerEvent := .enters (.creatureYouControl false false true)
@[match_pattern] abbrev anotherCreatureOrPlaneswalkerYouControlEnters : TriggerEvent := .enters .anotherCreatureOrPlaneswalkerYouControl
@[match_pattern] abbrev creatureOpponentControlsEnters : TriggerEvent := .enters .creatureOpponentControls
@[match_pattern] abbrev creatureYouControlPowerAtLeastEnters (n : Int) : TriggerEvent := .enters (.creatureYouControlPowerAtLeast n)
@[match_pattern] abbrev anotherElfYouControlEnters : TriggerEvent := .enters (.subtypeYouControl "Elf" true false)
@[match_pattern] abbrev anotherVillainEnters : TriggerEvent := .enters (.subtypeYouControl "Villain" true false)
@[match_pattern] abbrev anotherVillainOrArtifactEnters : TriggerEvent := .enters .anotherVillainOrArtifact
@[match_pattern] abbrev anotherNontokenHeroEnters : TriggerEvent := .enters (.subtypeYouControl "Hero" true true)
@[match_pattern] abbrev subtypeYouControlEnters (subtype : String) : TriggerEvent := .enters (.subtypeYouControl subtype false false)
@[match_pattern] abbrev thisOrAnotherSubtypeYouControlEnters : TriggerEvent := .enters (.thisOrAnotherSubtypeYouControl false)
@[match_pattern] abbrev thisOrAnotherSubtypeEnters : TriggerEvent := .enters (.thisOrAnotherSubtypeYouControl false)
@[match_pattern] abbrev thisOrNontokenSubtypeYouControlEnters : TriggerEvent := .enters (.thisOrAnotherSubtypeYouControl true)
@[match_pattern] abbrev thisOrNontokenSubtypeEnters : TriggerEvent := .enters (.thisOrAnotherSubtypeYouControl true)
@[match_pattern] abbrev anotherSubtypeOrEquipmentYouControlEnters : TriggerEvent := .enters .anotherSubtypeOrEquipmentYouControl
@[match_pattern] abbrev anotherSubtypeOrEquipmentEnters : TriggerEvent := .enters .anotherSubtypeOrEquipmentYouControl

-- Zone-leaving / dies / graveyard aliases (CR 603.6c / 700.4)
@[match_pattern] abbrev dying : TriggerEvent := .leaves (.source true)
@[match_pattern] abbrev dies : TriggerEvent := .leaves (.source true)
@[match_pattern] abbrev leaving : TriggerEvent := .leaves (.source false)
@[match_pattern] abbrev enchantedDies : TriggerEvent := .leaves .enchantedDies
@[match_pattern] abbrev creatureYouControlDies : TriggerEvent := .leaves (.creatureYouControlDies false false false)
@[match_pattern] abbrev nontokenYouControlDies : TriggerEvent := .leaves (.creatureYouControlDies true false false)
@[match_pattern] abbrev nontokenCreatureYouControlDies : TriggerEvent := .leaves (.creatureYouControlDies true false true)
@[match_pattern] abbrev attackingCreatureYouControlDies : TriggerEvent := .leaves (.creatureYouControlDies false true true)
@[match_pattern] abbrev villainYouControlDies : TriggerEvent := .leaves (.subtypeYouControlDies #["Villain"])
@[match_pattern] abbrev anotherGoblinOrcArmyDies : TriggerEvent := .leaves (.subtypeYouControlDies #["Goblin", "Orc", "Army"])
@[match_pattern] abbrev anotherCreatureOrPlaneswalkerYouControlDies : TriggerEvent := .leaves .anotherCreatureOrPlaneswalkerYouControlDies
@[match_pattern] abbrev oneOrMoreOtherCreaturesDie : TriggerEvent := .leaves .oneOrMoreOtherCreaturesDie
@[match_pattern] abbrev creatureYouControlLeaves : TriggerEvent := .leaves .creatureYouControlLeaves
@[match_pattern] abbrev anotherNonlandReturned : TriggerEvent := .leaves .anotherNonlandReturned
@[match_pattern] abbrev creatureCardLeavesYourGy : TriggerEvent := .leaves (.creatureCardYourGy true)
@[match_pattern] abbrev creatureCardsPutIntoYourGy : TriggerEvent := .leaves (.creatureCardYourGy false)

-- Phase and step aliases (CR 603.2b)
@[match_pattern] abbrev yourUpkeep : TriggerEvent := .step (.upkeep false)
@[match_pattern] abbrev eachUpkeep : TriggerEvent := .step (.eachUpkeep false)
@[match_pattern] abbrev eachUpkeepFromGraveyard : TriggerEvent := .step (.eachUpkeep true)
@[match_pattern] abbrev enchantedControllerUpkeep : TriggerEvent := .step (.upkeep true)
@[match_pattern] abbrev eaglesCreateBirds : TriggerEvent := .step .eaglesCreateBirds
@[match_pattern] abbrev eachOpponentDrawStep : TriggerEvent := .step .eachOpponentDrawStep
@[match_pattern] abbrev yourFirstMain : TriggerEvent := .step .yourFirstMain
@[match_pattern] abbrev yourBeginCombat : TriggerEvent := .step (.yourBeginCombat false)
@[match_pattern] abbrev yourBeginCombatFromGraveyard : TriggerEvent := .step (.yourBeginCombat true)
@[match_pattern] abbrev opponentBeginCombat : TriggerEvent := .step (.otherBeginCombat false)
@[match_pattern] abbrev eachBeginCombat : TriggerEvent := .step (.otherBeginCombat true)
@[match_pattern] abbrev yourEndStep : TriggerEvent := .step (.endStep false)
@[match_pattern] abbrev eachEndStep : TriggerEvent := .step (.endStep true)

-- Spell-cast aliases (CR 601.2i)
@[match_pattern] abbrev castThis : TriggerEvent := .casts .castThis
@[match_pattern] abbrev youCastSpell : TriggerEvent := .casts (.spell false)
@[match_pattern] abbrev youCastInstantOrSorcery : TriggerEvent := .casts .youInstantOrSorcery
@[match_pattern] abbrev youCastNoncreature : TriggerEvent := .casts (.noncreature false false)
@[match_pattern] abbrev youCastFirstNoncreature : TriggerEvent := .casts (.noncreature true false)
@[match_pattern] abbrev youCastSecondSpell : TriggerEvent := .casts (.secondSpell false)
@[match_pattern] abbrev youCastCreature : TriggerEvent := .casts (.youCreature false)
@[match_pattern] abbrev youCastArtifactOrCreature : TriggerEvent := .casts (.youCreature true)
@[match_pattern] abbrev youCastGreen : TriggerEvent := .casts .youGreen
@[match_pattern] abbrev youCastColor (color : Color) : TriggerEvent := .casts (.youColor color false)
@[match_pattern] abbrev youCastColorFromHand (color : Color) : TriggerEvent := .casts (.youColor color true)
@[match_pattern] abbrev youCastVillain : TriggerEvent := .casts .youVillain
@[match_pattern] abbrev youCastWithTreasure : TriggerEvent := .casts .youWithTreasure
@[match_pattern] abbrev youCastPreparedSpell : TriggerEvent := .casts .youPreparedSpell
@[match_pattern] abbrev youCastTargetingCreatureYouControl : TriggerEvent := .casts (.youTargetingCreatureYouControl false)
@[match_pattern] abbrev youCastEquipmentOrTargetingCreatureYouControl : TriggerEvent := .casts (.youTargetingCreatureYouControl true)
@[match_pattern] abbrev youCastTargetingCreature : TriggerEvent := .casts .youTargetingCreature
@[match_pattern] abbrev youCastInstantSorceryTargetingArtifactOrLand : TriggerEvent := .casts .youInstantSorceryTargetingArtifactOrLand
@[match_pattern] abbrev youCastTargetingOpponentOrTheirCreature : TriggerEvent := .casts .youTargetingOpponentOrTheirCreature
@[match_pattern] abbrev opponentCastsSpell : TriggerEvent := .casts (.spell true)
@[match_pattern] abbrev opponentCastsFirstNoncreature : TriggerEvent := .casts (.noncreature true true)
@[match_pattern] abbrev opponentCastsSpellMvAtMost (n : Nat) : TriggerEvent := .casts (.opponentSpellMvAtMost n)
@[match_pattern] abbrev opponentCastsMatchingParity : TriggerEvent := .casts .opponentMatchingParity
@[match_pattern] abbrev anyPlayerCastsSecondSpell : TriggerEvent := .casts (.secondSpell true)
@[match_pattern] abbrev spellTargetsSource : TriggerEvent := .casts .spellTargetsSource

-- Combat declaration aliases (CR 508.2 / 509.5c)
@[match_pattern] abbrev attacking : TriggerEvent := .combat .sourceAttacks
@[match_pattern] abbrev attack : TriggerEvent := .combat .sourceAttacks
@[match_pattern] abbrev youAttack : TriggerEvent := .combat (.youAttack false)
@[match_pattern] abbrev youAttackWithElves : TriggerEvent := .combat (.subtypeAttacks "Elf" false)
@[match_pattern] abbrev youAttackWithTwoOrMore : TriggerEvent := .combat (.youAttack true)
@[match_pattern] abbrev youAttackWithTotalPower (n : Int := 12) : TriggerEvent := .combat (.youAttackWithTotalPower n)
@[match_pattern] abbrev equippedAttacks : TriggerEvent := .combat (.equippedAttacks false false)
@[match_pattern] abbrev equippedAttacksAlone : TriggerEvent := .combat (.equippedAttacks true false)
@[match_pattern] abbrev equippedCreatureYouControlAttacks : TriggerEvent := .combat (.equippedAttacks false true)
@[match_pattern] abbrev creatureYouControlAttacks : TriggerEvent := .combat (.creatureYouControlAttacks false false)
@[match_pattern] abbrev creatureYouControlAttacksAlone : TriggerEvent := .combat (.creatureYouControlAttacks true false)
@[match_pattern] abbrev creatureYouControlAttacksPlayerAlone : TriggerEvent := .combat (.creatureYouControlAttacks true true)
@[match_pattern] abbrev creatureAttacksYouOrYourPlaneswalker : TriggerEvent := .combat (.creaturesAttackPlayer false)
@[match_pattern] abbrev creaturesAttackYourOpponent : TriggerEvent := .combat (.creaturesAttackPlayer true)
@[match_pattern] abbrev merfolkAttackPlayer : TriggerEvent := .combat (.subtypeAttacks "Merfolk" false)
@[match_pattern] abbrev zombieTokenAttacks : TriggerEvent := .combat (.subtypeAttacks "Zombie" true)
@[match_pattern] abbrev sphinxesAttack : TriggerEvent := .combat (.subtypeAttacks "Sphinx" false)
@[match_pattern] abbrev enchantedAttacksOrBlocks : TriggerEvent := .combat .enchantedAttacksOrBlocks
@[match_pattern] abbrev becomesBlocked : TriggerEvent := .combat .becomesBlocked
@[match_pattern] abbrev opponentSmallCreatureBlocks : TriggerEvent := .combat .opponentSmallCreatureBlocks

-- Damage aliases (CR 510.2 / 120)
@[match_pattern] abbrev dealsCombatDamageToPlayer : TriggerEvent := .damage (.sourceCombatToPlayer false)
@[match_pattern] abbrev combatDamageToPlayer : TriggerEvent := .damage (.sourceCombatToPlayer false)
@[match_pattern] abbrev dealsCombatDamageToPlayerOrBattle : TriggerEvent := .damage (.sourceCombatToPlayer true)
@[match_pattern] abbrev combatDamageToPlayerOrBattle : TriggerEvent := .damage (.sourceCombatToPlayer true)
@[match_pattern] abbrev equippedDealsCombatDamageToPlayer : TriggerEvent := .damage .equippedCombatToPlayer
@[match_pattern] abbrev armyYouControlCombatDamage : TriggerEvent := .damage (.subtypeToPlayer "Army" true)
@[match_pattern] abbrev combatDamageToYou : TriggerEvent := .damage .combatToYou
@[match_pattern] abbrev opponentsDealtCombatDamageYourTurn : TriggerEvent := .damage .opponentsDealtCombatYourTurn
@[match_pattern] abbrev heroesDealDamageToPlayer : TriggerEvent := .damage (.subtypeToPlayer "Hero" false)
@[match_pattern] abbrev sourceDealtDamage : TriggerEvent := .damage (.sourceDealt false)
@[match_pattern] abbrev sourceDealtNoncombatDamage : TriggerEvent := .damage (.sourceDealt true)
@[match_pattern] abbrev creatureYouControlDealtDamage : TriggerEvent := .damage .creatureYouControlDealt
@[match_pattern] abbrev opponentsDealtNoncombatDamage : TriggerEvent := .damage (.opponentDealtNoncombat true)
@[match_pattern] abbrev opponentDealtNoncombatDamage : TriggerEvent := .damage (.opponentDealtNoncombat false)

-- Draw aliases (CR 121)
@[match_pattern] abbrev youDraw : TriggerEvent := .draws .youCard
@[match_pattern] abbrev youDrawSecondCard : TriggerEvent := .draws (.secondCard false false)
@[match_pattern] abbrev youDrawSecond : TriggerEvent := .draws (.secondCard false false)
@[match_pattern] abbrev opponentDrawsExceptFirstDrawStep : TriggerEvent := .draws .opponentExceptFirstDrawStep
@[match_pattern] abbrev opponentDrawsExceptFirst : TriggerEvent := .draws .opponentExceptFirstDrawStep
@[match_pattern] abbrev opponentDrawsSecondCard : TriggerEvent := .draws (.secondCard true false)
@[match_pattern] abbrev opponentDrawsSecond : TriggerEvent := .draws (.secondCard true false)
@[match_pattern] abbrev anyPlayerDrawsSecond : TriggerEvent := .draws (.secondCard false true)

-- Discard & cycle aliases (CR 701.8 / 702.29)
@[match_pattern] abbrev youDiscard : TriggerEvent := .discards (.youCard false)
@[match_pattern] abbrev youDiscardOne : TriggerEvent := .discards (.youCard true)
@[match_pattern] abbrev youDiscardThis : TriggerEvent := .discards .youThis
@[match_pattern] abbrev playerDiscards : TriggerEvent := .discards .playerCards
@[match_pattern] abbrev youCycle : TriggerEvent := .discards .youCycle

-- Tap aliases (CR 701.26)
@[match_pattern] abbrev sourceBecomesTapped : TriggerEvent := .taps .source
@[match_pattern] abbrev equippedBecomesTapped : TriggerEvent := .taps .equipped
@[match_pattern] abbrev tappedForTeamwork : TriggerEvent := .taps .forTeamwork
@[match_pattern] abbrev creatureYouControlTapped : TriggerEvent := .taps (.creatureYouControl false)
@[match_pattern] abbrev creaturesYouControlBecomeTapped : TriggerEvent := .taps (.creatureYouControl true)

-- Counter, proliferate & Saga aliases (CR 122 / 701.34 / 714)
@[match_pattern] abbrev youPutPlusOne : TriggerEvent := .counters .youPutPlusOne
@[match_pattern] abbrev youPutCountersOnGoblinOrcArmy : TriggerEvent := .counters .youPutOnGoblinOrcArmy
@[match_pattern] abbrev youPutLoyaltyCounters : TriggerEvent := .counters .youPutLoyalty
@[match_pattern] abbrev nthPlanCounter (n : Nat) : TriggerEvent := .counters (.nthPlan n)
@[match_pattern] abbrev sagaChapter (n : Nat := 0) : TriggerEvent := .counters (.sagaChapter n false)
@[match_pattern] abbrev finalSagaChapterResolves : TriggerEvent := .counters (.sagaChapter 0 true)
@[match_pattern] abbrev youProliferate : TriggerEvent := .counters .youProliferate

-- Player/object action aliases (CR 603.2)
@[match_pattern] abbrev youActivateCreatureAbility : TriggerEvent := .action .youActivateCreatureAbility
@[match_pattern] abbrev youActivateLoyaltyAbility : TriggerEvent := .action (.activateLoyaltyAbility false)
@[match_pattern] abbrev opponentActivatesLoyaltyAbility : TriggerEvent := .action (.activateLoyaltyAbility true)
@[match_pattern] abbrev becomesTarget : TriggerEvent := .action .becomesTarget
@[match_pattern] abbrev youTargetSomething : TriggerEvent := .action .youTargetSomething
@[match_pattern] abbrev youSacrificeToken : TriggerEvent := .action .youSacrificeToken
@[match_pattern] abbrev bolgSacrificedForReflexive : TriggerEvent := .action .bolgSacrificedForReflexive
@[match_pattern] abbrev youCreateCreatureTokens : TriggerEvent := .action .youCreateCreatureTokens
@[match_pattern] abbrev youGainLife : TriggerEvent := .action .youGainLife
@[match_pattern] abbrev playerLosesLife : TriggerEvent := .action .playerLosesLife
@[match_pattern] abbrev youScry : TriggerEvent := .action (.youScry false)
@[match_pattern] abbrev youScryOrSurveil : TriggerEvent := .action (.youScry true)
@[match_pattern] abbrev theRingTemptsYou : TriggerEvent := .action (.ringTempts false)
@[match_pattern] abbrev youChooseRingBearer : TriggerEvent := .action (.ringTempts true)

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
  | .action (.youScry orSurveil) =>
    { clause := if orSurveil then "you scry or surveil" else "you scry",
      label := "scry trigger", checkTargets := false }
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
  | .draws (.secondCard opponent anyPlayer) =>
    if opponent then
      { clause := "an opponent draws their second card each turn",
        label := "opponent-second-card trigger", checkTargets := false }
    else
      { clause :=
          if anyPlayer then "a player draws their second card each turn"
          else "you draw your second card each turn",
        label := "second-card trigger", checkTargets := false }
  | .youAttackWithTwoOrMore =>
    { clause := "two or more creatures you control attack a player",
      label := "attack trigger" }
  | .damage (.sourceCombatToPlayer orBattle) =>
    { clause :=
        if orBattle then "this deals combat damage to a player or battle"
        else "this deals combat damage to a player",
      label := "combat-damage trigger", checkTargets := orBattle }
  | .step (.endStep each) =>
    let who := if each then "each" else "your"
    { clause := s!"the beginning of {who} end step", isWhenever := false,
      label := "end-step trigger", checkTargets := false }
  | .anotherCreatureYouControlEnters =>
    { clause := "another creature you control enters", label := "creature-enters trigger",
      checkTargets := false }
  | .step (.yourBeginCombat fromGraveyard) =>
    { clause := "the beginning of combat on your turn", isWhenever := false,
      label := if fromGraveyard then "beginning-of-combat trigger" else "begin-combat trigger",
      checkTargets := fromGraveyard }
  | .youAttack =>
    { clause := "you attack", label := "attack trigger", checkTargets := false }
  | .youCastNoncreature =>
    { clause := "you cast a noncreature spell", label := "cast trigger",
      checkTargets := false }
  | .yourUpkeep =>
    { clause := "the beginning of your upkeep", isWhenever := false,
      label := "upkeep trigger", checkTargets := false }
  | .enters (.artifactYouControl another nontoken) =>
    let lead :=
      if another && nontoken then "another nontoken"
      else if another then "another"
      else "an"
    { clause := s!"{lead} artifact you control enters", label := "artifact-enters trigger",
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
  | .enters (.thisOrAnotherSubtypeYouControl nontoken) =>
    let mid := if nontoken then "another nontoken" else "another"
    { clause := s!"this or {mid} creature you control enters",
      label := "subtype-enters trigger", checkTargets := false }
  | .becomesTarget =>
    { clause := "this creature becomes the target of a spell or ability an opponent controls",
      label := "becomes-target trigger", checkTargets := false }
  | .eachBeginCombat =>
    { clause := "the beginning of each combat", isWhenever := false,
      label := "begin-combat trigger", checkTargets := false }
  | .youCastGreen =>
    { clause := "you cast a green spell", label := "cast trigger" }
  | .enters (.landSubtypeYouControl s) =>
    { clause := s!"a {s} you control enters", label := s!"{s.toLower}-enters trigger" }
  | .anotherSubtypeOrEquipmentYouControlEnters =>
    { clause := "another Dwarf or Equipment you control enters",
      label := "dwarf-or-equipment trigger", checkTargets := false }
  | .youCastWithTreasure =>
    { clause := "you cast a spell, if mana from a Treasure was spent to cast it",
      label := "treasure-cast trigger", checkTargets := false }
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
  | .youAttackWithTotalPower n =>
    { clause := s!"you attack with creatures with total power {n} or greater",
      label := "total-power-attack trigger", checkTargets := false }
  | .eaglesCreateBirds =>
    { clause := "the beginning of the next upkeep", isWhenever := false,
      label := "delayed Bird Soldier trigger", checkTargets := false }
  | .bolgSacrificedForReflexive =>
    { clause := "you sacrifice a creature this way", isWhenever := false,
      label := "reflexive trigger" }
  | .casts (.youColor c fromHand) =>
    if fromHand then
      { clause := s!"you cast a {c.englishName} spell from your hand",
        label := "cast trigger", checkTargets := false }
    else
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
  | .damage (.sourceDealt noncombatOnly) =>
    if noncombatOnly then
      { clause := "this is dealt noncombat damage",
        label := "noncombat-damage trigger", checkTargets := false }
    else
      { clause := "this is dealt damage",
        label := "dealt-damage trigger", checkTargets := false }
  | .opponentCastsSpell =>
    { clause := "an opponent casts a spell", label := "opponent-cast trigger",
      checkTargets := false }
  | .armyYouControlCombatDamage =>
    { clause := "an Army you control deals combat damage to a player",
      label := "army-combat-damage trigger", checkTargets := false }
  | .counters (.sagaChapter _ finalResolves) =>
    if finalResolves then
      { clause := "the final chapter ability of a Saga you control resolves",
        label := "saga-chapter trigger", checkTargets := false }
    else
      { clause := "a lore counter is put on this Saga", isWhenever := false,
        label := "saga chapter", checkTargets := true }
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
  | .step (.eachUpkeep fromGraveyard) =>
    { clause :=
        if fromGraveyard then "the beginning of each upkeep"
        else "the beginning of each player's upkeep",
      isWhenever := false, label := "upkeep trigger", checkTargets := fromGraveyard }
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
  | .anotherNontokenHeroEnters =>
    { clause := "another nontoken Hero you control enters",
      label := "hero-enters trigger", checkTargets := false }
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
