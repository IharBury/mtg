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
  | entersEventKind (subtype : String := "") (n : Int := 0)
      (alt1 : Bool := false) (alt2 : Bool := false) (alt3 : Bool := false)
      (artifactOrSubtype : Bool := false) (creatureGroup : Bool := false)
      (powerAtLeast : Bool := false) (paramKind : Bool := false)
deriving Repr, Inhabited, BEq, DecidableEq

namespace EntersEvent
@[match_pattern] abbrev entersFilterKind (alt1 : Bool := false) (alt2 : Bool := false) (alt3 : Bool := false)
    (artifactOrSubtype : Bool := false) (creatureGroup : Bool := false) : EntersEvent :=
  .entersEventKind "" 0 alt1 alt2 alt3 artifactOrSubtype creatureGroup false false
@[match_pattern] abbrev paramEntersKind (subtype : String := "") (n : Int := 0) (another : Bool := false)
    (nontoken : Bool := false) (landSubtype : Bool := false) (powerAtLeast : Bool := false) : EntersEvent :=
  .entersEventKind subtype n another nontoken landSubtype false false powerAtLeast true
@[match_pattern] abbrev permanentEntersKind (alt1 : Bool := false) (alt2 : Bool := false) (other : Bool := false) : EntersEvent :=
  .entersFilterKind alt1 alt2 other false false
@[match_pattern] abbrev artifactOrThisSubtypeYouControl (another : Bool := false) (nontoken : Bool := false) (thisOrAnotherSubtype : Bool := false) : EntersEvent :=
  .entersFilterKind another nontoken thisOrAnotherSubtype true false
@[match_pattern] abbrev creatureYouControl (another : Bool := false) (nontoken : Bool := false) (thisOrAnother : Bool := false) : EntersEvent :=
  .entersFilterKind another nontoken thisOrAnother false true
@[match_pattern] abbrev subtypeEntersYouControl (subtype : String) (another : Bool := false) (nontoken : Bool := false) (landSubtype : Bool := false) : EntersEvent :=
  .paramEntersKind subtype 0 another nontoken landSubtype false
@[match_pattern] abbrev creatureYouControlPowerAtLeast (n : Int) : EntersEvent :=
  .paramEntersKind "" n false false false true
@[match_pattern] abbrev simpleEnters (landOrEquipment : Bool := false) (tokenOrEquipment : Bool := false) : EntersEvent :=
  .permanentEntersKind landOrEquipment tokenOrEquipment false
@[match_pattern] abbrev otherPermanentEnters (oppCreatureOrVillain : Bool := false) (villainOrDwarfEquip : Bool := false) : EntersEvent :=
  .permanentEntersKind oppCreatureOrVillain villainOrDwarfEquip true
@[match_pattern] abbrev landSubtypeYouControl (subtype : String) : EntersEvent :=
  .subtypeEntersYouControl subtype false false true
@[match_pattern] abbrev subtypeYouControl (subtype : String) (another : Bool := false) (nontoken : Bool := false) : EntersEvent :=
  .subtypeEntersYouControl subtype another nontoken false
@[match_pattern] abbrev artifactYouControl (another : Bool := false) (nontoken : Bool := false) : EntersEvent :=
  .artifactOrThisSubtypeYouControl another nontoken false
@[match_pattern] abbrev thisOrAnotherSubtypeYouControl (nontoken : Bool := false) : EntersEvent :=
  .artifactOrThisSubtypeYouControl false nontoken true
@[match_pattern] abbrev source : EntersEvent := .permanentEntersKind false false false
@[match_pattern] abbrev landYouControl : EntersEvent := .permanentEntersKind true false false
@[match_pattern] abbrev tokenYouControl : EntersEvent := .permanentEntersKind false true false
@[match_pattern] abbrev equipmentYouControl : EntersEvent := .permanentEntersKind true true false
@[match_pattern] abbrev anotherCreatureOrPlaneswalkerYouControl : EntersEvent := .permanentEntersKind false false true
@[match_pattern] abbrev creatureOpponentControls : EntersEvent := .permanentEntersKind true false true
@[match_pattern] abbrev anotherVillainOrArtifact : EntersEvent := .permanentEntersKind true true true
@[match_pattern] abbrev anotherSubtypeOrEquipmentYouControl : EntersEvent := .permanentEntersKind false true true
end EntersEvent

/-- Which zone-leaving or graveyard-entering event causes `TriggerEvent.leaves` to fire (CR 603.6c / 700.4). -/
inductive LeavesEvent where
  | leavesEventKind (subtypes : Array String := #[]) (alt1 : Bool := true) (alt2 : Bool := false)
      (alt3 : Bool := false) (alt4 : Bool := false) (diesGroup : Bool := false) (bySubtypes : Bool := false)
deriving Repr, Inhabited, BEq, DecidableEq

namespace LeavesEvent
@[match_pattern] abbrev leavesFilterKind (alt1 : Bool := true) (alt2 : Bool := false) (alt3 : Bool := false)
    (alt4 : Bool := false) (diesGroup : Bool := false) : LeavesEvent :=
  .leavesEventKind #[] alt1 alt2 alt3 alt4 diesGroup false
@[match_pattern] abbrev subtypeYouControlDies (subtypes : Array String) : LeavesEvent :=
  .leavesEventKind subtypes false false false false false true
@[match_pattern] abbrev sourceOrZoneLeave (diesOrLeaves : Bool := true) (gyOrReturned : Bool := false) (returned : Bool := false) : LeavesEvent :=
  .leavesFilterKind diesOrLeaves gyOrReturned returned false false
@[match_pattern] abbrev creatureOrPermanentDies (nontoken : Bool := false) (attacking : Bool := false) (includeSelf : Bool := false) (permanentDiesOrLeaves : Bool := false) : LeavesEvent :=
  .leavesFilterKind nontoken attacking includeSelf permanentDiesOrLeaves true
@[match_pattern] abbrev source (diesOnly : Bool := true) : LeavesEvent := .sourceOrZoneLeave diesOnly false false
@[match_pattern] abbrev creatureCardYourGy (leaves : Bool := true) : LeavesEvent := .sourceOrZoneLeave leaves true false
@[match_pattern] abbrev anotherNonlandReturned : LeavesEvent := .sourceOrZoneLeave false false true
@[match_pattern] abbrev creatureYouControlDies (nontoken : Bool := false) (attacking : Bool := false) (includeSelf : Bool := false) : LeavesEvent :=
  .creatureOrPermanentDies nontoken attacking includeSelf false
@[match_pattern] abbrev permanentDiesOrLeaves (otherDiesOrBatch : Bool := false) (batchOrLeaves : Bool := false) : LeavesEvent :=
  .creatureOrPermanentDies otherDiesOrBatch batchOrLeaves false true
@[match_pattern] abbrev enchantedDies : LeavesEvent := .creatureOrPermanentDies false false false true
@[match_pattern] abbrev anotherCreatureOrPlaneswalkerYouControlDies : LeavesEvent := .creatureOrPermanentDies true false false true
@[match_pattern] abbrev oneOrMoreOtherCreaturesDie : LeavesEvent := .creatureOrPermanentDies true true false true
@[match_pattern] abbrev creatureYouControlLeaves : LeavesEvent := .creatureOrPermanentDies false true false true
end LeavesEvent

/-- Which phase or step beginning causes `TriggerEvent.step` to fire (CR 603.2b). -/
inductive StepEvent where
  | stepEventKind (alt1 : Bool := false) (alt2 : Bool := false) (alt3 : Bool := false) (combatOrEnd : Bool := false)
deriving Repr, Inhabited, BEq, DecidableEq

namespace StepEvent
@[match_pattern] abbrev upkeepOrFixedStep (alt1 : Bool := false) (alt2 : Bool := false) (fixed : Bool := false) : StepEvent :=
  .stepEventKind alt1 alt2 fixed false
@[match_pattern] abbrev combatOrEndStep (alt : Bool := false) (otherCombat : Bool := false) (endStep : Bool := false) : StepEvent :=
  .stepEventKind alt otherCombat endStep true
@[match_pattern] abbrev upkeep (enchantedController : Bool := false) : StepEvent := .upkeepOrFixedStep enchantedController false false
@[match_pattern] abbrev eachUpkeep (fromGraveyard : Bool := false) : StepEvent := .upkeepOrFixedStep fromGraveyard true false
@[match_pattern] abbrev fixedStep (oppDrawStep : Bool := false) (firstMain : Bool := false) : StepEvent := .upkeepOrFixedStep oppDrawStep firstMain true
@[match_pattern] abbrev eaglesCreateBirds : StepEvent := .upkeepOrFixedStep false false true
@[match_pattern] abbrev eachOpponentDrawStep : StepEvent := .upkeepOrFixedStep true false true
@[match_pattern] abbrev yourFirstMain : StepEvent := .upkeepOrFixedStep false true true
@[match_pattern] abbrev yourBeginCombat (fromGraveyard : Bool := false) : StepEvent := .combatOrEndStep fromGraveyard false false
@[match_pattern] abbrev otherBeginCombat (each : Bool := false) : StepEvent := .combatOrEndStep each true false
@[match_pattern] abbrev endStep (each : Bool := false) : StepEvent := .combatOrEndStep each false true
end StepEvent

/-- Which spell being cast causes `TriggerEvent.casts` to fire (CR 601.2i). -/
inductive CastEvent where
  | castEventKind (color : Color := .white) (n : Nat := 0)
      (alt1 : Bool := false) (alt2 : Bool := false) (alt3 : Bool := false)
      (alt4 : Bool := false) (specialGroup : Bool := false)
      (targetingGroup : Bool := false) (paramKind : Bool := false)
deriving Repr, Inhabited, BEq, DecidableEq

namespace CastEvent
@[match_pattern] abbrev castFilterKind (alt1 : Bool := false) (alt2 : Bool := false) (alt3 : Bool := false)
    (alt4 : Bool := false) (specialGroup : Bool := false) (targetingGroup : Bool := false) : CastEvent :=
  .castEventKind .white 0 alt1 alt2 alt3 alt4 specialGroup targetingGroup false
@[match_pattern] abbrev paramCastKind (color : Color := .white) (n : Nat := 0) (fromHand : Bool := false) (mvAtMost : Bool := false) : CastEvent :=
  .castEventKind color n fromHand mvAtMost false false false false true
@[match_pattern] abbrev spellOrCreatureCast (alt1 : Bool := false) (alt2 : Bool := false) (secondOrCreature : Bool := false) (youCreature : Bool := false) : CastEvent :=
  .castFilterKind alt1 alt2 secondOrCreature youCreature false false
@[match_pattern] abbrev specialOrParityCast (alt1 : Bool := false) (alt2 : Bool := false) (villainOrParity : Bool := false) : CastEvent :=
  .castFilterKind alt1 alt2 villainOrParity false true false
@[match_pattern] abbrev youTargetingCast (orEquipment : Bool := false) (anyCreatureOrArtifactLand : Bool := false) (artifactLandOrOpponent : Bool := false) : CastEvent :=
  .castFilterKind orEquipment anyCreatureOrArtifactLand artifactLandOrOpponent false false true
@[match_pattern] abbrev youColor (color : Color) (fromHand : Bool := false) : CastEvent :=
  .paramCastKind color 0 fromHand false
@[match_pattern] abbrev opponentSpellMvAtMost (n : Nat) : CastEvent :=
  .paramCastKind .white n false true
@[match_pattern] abbrev spell (opponent : Bool := false) : CastEvent := .spellOrCreatureCast opponent false false false
@[match_pattern] abbrev noncreature (firstOnly : Bool := false) (opponent : Bool := false) : CastEvent :=
  .spellOrCreatureCast firstOnly opponent true false
@[match_pattern] abbrev secondSpell (anyPlayer : Bool := false) : CastEvent := .spellOrCreatureCast anyPlayer false false true
@[match_pattern] abbrev youCreature (orArtifact : Bool := false) : CastEvent := .spellOrCreatureCast orArtifact true false true
@[match_pattern] abbrev youSpecialCast (greenOrPrepared : Bool := false) (treasureOrPrepared : Bool := false) : CastEvent :=
  .specialOrParityCast greenOrPrepared treasureOrPrepared false
@[match_pattern] abbrev castThisOrVillainOrParity (villainOrTargetsSource : Bool := false) (parityOrTargetsSource : Bool := false) : CastEvent :=
  .specialOrParityCast villainOrTargetsSource parityOrTargetsSource true
@[match_pattern] abbrev youInstantOrSorcery : CastEvent := .specialOrParityCast false false false
@[match_pattern] abbrev youGreen : CastEvent := .specialOrParityCast true false false
@[match_pattern] abbrev youWithTreasure : CastEvent := .specialOrParityCast false true false
@[match_pattern] abbrev youPreparedSpell : CastEvent := .specialOrParityCast true true false
@[match_pattern] abbrev castThis : CastEvent := .specialOrParityCast false false true
@[match_pattern] abbrev youVillain : CastEvent := .specialOrParityCast true false true
@[match_pattern] abbrev opponentMatchingParity : CastEvent := .specialOrParityCast false true true
@[match_pattern] abbrev spellTargetsSource : CastEvent := .specialOrParityCast true true true
@[match_pattern] abbrev youTargetingCreatureYouControl (orEquipment : Bool := false) : CastEvent :=
  .youTargetingCast orEquipment false false
@[match_pattern] abbrev youTargetingCreature : CastEvent := .youTargetingCast false true false
@[match_pattern] abbrev youInstantSorceryTargetingArtifactOrLand : CastEvent := .youTargetingCast false true true
@[match_pattern] abbrev youTargetingOpponentOrTheirCreature : CastEvent := .youTargetingCast false false true
end CastEvent

/-- Which attacker or blocker declaration causes `TriggerEvent.combat` to fire (CR 508.2 / 509.5c). -/
inductive CombatEvent where
  | combatEventKind (n : Int := 12) (subtype : String := "")
      (alt1 : Bool := false) (alt2 : Bool := false) (alt3 : Bool := false)
      (creatureOrEquipped : Bool := false) (paramKind : Bool := false)
deriving Repr, Inhabited, BEq, DecidableEq

namespace CombatEvent
@[match_pattern] abbrev combatFilterKind (alt1 : Bool := false) (alt2 : Bool := false) (alt3 : Bool := false) (creatureOrEquipped : Bool := false) : CombatEvent :=
  .combatEventKind 12 "" alt1 alt2 alt3 creatureOrEquipped false
@[match_pattern] abbrev paramCombatKind (n : Int := 12) (subtype : String := "") (tokenPowerAtLeast6 : Bool := false) (bySubtype : Bool := false) : CombatEvent :=
  .combatEventKind n subtype tokenPowerAtLeast6 bySubtype false false true
@[match_pattern] abbrev youOrPlayerAttack (alt1 : Bool := false) (alt2 : Bool := false) (selfOrBlock : Bool := false) : CombatEvent :=
  .combatFilterKind alt1 alt2 selfOrBlock false
@[match_pattern] abbrev creatureOrEquippedAttacks (alone : Bool := false) (alt : Bool := false) (equipped : Bool := false) : CombatEvent :=
  .combatFilterKind alone alt equipped true
@[match_pattern] abbrev tokenOrTotalPowerAttack (n : Int := 12) (tokenPowerAtLeast6 : Bool := false) : CombatEvent :=
  .paramCombatKind n "" tokenPowerAtLeast6 false
@[match_pattern] abbrev subtypeAttacks (subtype : String) (tokenPowerAtLeast6 : Bool := false) : CombatEvent :=
  .paramCombatKind 12 subtype tokenPowerAtLeast6 true
@[match_pattern] abbrev youAttackWithTotalPower (n : Int := 12) : CombatEvent := .tokenOrTotalPowerAttack n false
@[match_pattern] abbrev youAttack (twoOrMore : Bool := false) : CombatEvent := .youOrPlayerAttack twoOrMore false false
@[match_pattern] abbrev creaturesAttackPlayer (opponent : Bool := false) : CombatEvent := .youOrPlayerAttack opponent true false
@[match_pattern] abbrev selfOrBlockCombat (enchantedOrSmallBlock : Bool := false) (blockedOrSmallBlock : Bool := false) : CombatEvent :=
  .youOrPlayerAttack enchantedOrSmallBlock blockedOrSmallBlock true
@[match_pattern] abbrev equippedAttacks (alone : Bool := false) (anyEquippedYouControl : Bool := false) : CombatEvent :=
  .creatureOrEquippedAttacks alone anyEquippedYouControl true
@[match_pattern] abbrev creatureYouControlAttacks (alone : Bool := false) (playerOnly : Bool := false) : CombatEvent :=
  .creatureOrEquippedAttacks alone playerOnly false
@[match_pattern] abbrev sourceAttacks : CombatEvent := .youOrPlayerAttack false false true
@[match_pattern] abbrev enchantedAttacksOrBlocks : CombatEvent := .youOrPlayerAttack true false true
@[match_pattern] abbrev becomesBlocked : CombatEvent := .youOrPlayerAttack false true true
@[match_pattern] abbrev opponentSmallCreatureBlocks : CombatEvent := .youOrPlayerAttack true true true
end CombatEvent

/-- Which damage event causes `TriggerEvent.damage` to fire (CR 510.2 / 120). -/
inductive DamageEvent where
  | damageFilterKind (subtype : String := "") (alt1 : Bool := false) (alt2 : Bool := false)
      (alt3 : Bool := false) (alt4 : Bool := false) (bySubtype : Bool := false)
deriving Repr, Inhabited, BEq, DecidableEq

namespace DamageEvent
@[match_pattern] abbrev damageEventKind (alt1 : Bool := false) (alt2 : Bool := false) (sourceDealtOrOppNoncombat : Bool := false) (fixed : Bool := false) : DamageEvent :=
  .damageFilterKind "" alt1 alt2 sourceDealtOrOppNoncombat fixed false
@[match_pattern] abbrev subtypeToPlayer (subtype : String) (combatOnly : Bool := false) : DamageEvent :=
  .damageFilterKind subtype combatOnly false false false true
@[match_pattern] abbrev sourceCombatToPlayer (orBattle : Bool := false) : DamageEvent := .damageEventKind orBattle false false false
@[match_pattern] abbrev sourceDealt (noncombatOnly : Bool := false) : DamageEvent := .damageEventKind noncombatOnly false true false
@[match_pattern] abbrev opponentDealtNoncombat (batch : Bool := false) : DamageEvent := .damageEventKind batch true true false
@[match_pattern] abbrev fixedDamageEvent (combatToYouOrCreature : Bool := false) (oppCombatOrCreature : Bool := false) : DamageEvent :=
  .damageEventKind combatToYouOrCreature oppCombatOrCreature false true
@[match_pattern] abbrev equippedCombatToPlayer : DamageEvent := .damageEventKind false false false true
@[match_pattern] abbrev combatToYou : DamageEvent := .damageEventKind true false false true
@[match_pattern] abbrev opponentsDealtCombatYourTurn : DamageEvent := .damageEventKind false true false true
@[match_pattern] abbrev creatureYouControlDealt : DamageEvent := .damageEventKind true true false true
end DamageEvent

/-- Which card draw causes `TriggerEvent.draws` to fire (CR 121). -/
inductive DrawEvent where
  | drawEventKind (opponent : Bool := false) (anyPlayer : Bool := false) (secondOrExceptFirst : Bool := false)
deriving Repr, Inhabited, BEq, DecidableEq

namespace DrawEvent
@[match_pattern] abbrev youCard : DrawEvent := .drawEventKind false false false
@[match_pattern] abbrev opponentExceptFirstDrawStep : DrawEvent := .drawEventKind true true false
@[match_pattern] abbrev secondCard (opponent : Bool := false) (anyPlayer : Bool := false) : DrawEvent :=
  .drawEventKind opponent anyPlayer true
end DrawEvent

/-- Which discard or cycling action causes `TriggerEvent.discards` to fire (CR 701.8 / 702.29). -/
inductive DiscardEvent where
  | discardEventKind (alt1 : Bool := false) (alt2 : Bool := false) (special : Bool := false)
deriving Repr, Inhabited, BEq, DecidableEq

namespace DiscardEvent
@[match_pattern] abbrev youCard (trackCause : Bool := false) : DiscardEvent := .discardEventKind trackCause false false
@[match_pattern] abbrev specialDiscard (playerCards : Bool := false) (cycle : Bool := false) : DiscardEvent :=
  .discardEventKind playerCards cycle true
@[match_pattern] abbrev youThis : DiscardEvent := .discardEventKind false false true
@[match_pattern] abbrev playerCards : DiscardEvent := .discardEventKind true false true
@[match_pattern] abbrev youCycle : DiscardEvent := .discardEventKind false true true
end DiscardEvent

/-- Which permanent becoming tapped causes `TriggerEvent.taps` to fire (CR 701.26). -/
inductive TapEvent where
  | tapEventKind (alt1 : Bool := false) (alt2 : Bool := false) (creatureYouControl : Bool := false)
deriving Repr, Inhabited, BEq, DecidableEq

namespace TapEvent
@[match_pattern] abbrev singleTap (equipped : Bool := false) (teamwork : Bool := false) : TapEvent :=
  .tapEventKind equipped teamwork false
@[match_pattern] abbrev creatureYouControl (batch : Bool := false) : TapEvent := .tapEventKind batch false true
@[match_pattern] abbrev source : TapEvent := .tapEventKind false false false
@[match_pattern] abbrev equipped : TapEvent := .tapEventKind true false false
@[match_pattern] abbrev forTeamwork : TapEvent := .tapEventKind false true false
end TapEvent

/-- Which counter placement, proliferation, or Saga chapter causes `TriggerEvent.counters` to fire (CR 122 / 701.34 / 714). -/
inductive CounterEvent where
  | counterEventKind (n : Nat := 0) (alt1 : Bool := false) (alt2 : Bool := false) (planOrSaga : Bool := false)
deriving Repr, Inhabited, BEq, DecidableEq

namespace CounterEvent
@[match_pattern] abbrev counterOrProliferateEvent (armyOrLoyalty : Bool := false) (loyaltyOrProliferate : Bool := false) : CounterEvent :=
  .counterEventKind 0 armyOrLoyalty loyaltyOrProliferate false
@[match_pattern] abbrev planOrSagaCounter (n : Nat := 0) (finalResolves : Bool := false) (saga : Bool := false) : CounterEvent :=
  .counterEventKind n finalResolves saga true
@[match_pattern] abbrev youPutPlusOne : CounterEvent := .counterOrProliferateEvent false false
@[match_pattern] abbrev youPutOnGoblinOrcArmy : CounterEvent := .counterOrProliferateEvent true false
@[match_pattern] abbrev youPutLoyalty : CounterEvent := .counterOrProliferateEvent true true
@[match_pattern] abbrev youProliferate : CounterEvent := .counterOrProliferateEvent false true
@[match_pattern] abbrev nthPlan (n : Nat) : CounterEvent := .planOrSagaCounter n false false
@[match_pattern] abbrev sagaChapter (n : Nat := 0) (finalResolves : Bool := false) : CounterEvent :=
  .planOrSagaCounter n finalResolves true
end CounterEvent

/-- Which player or object game action causes `TriggerEvent.action` to fire (CR 603.2). -/
inductive ActionEvent where
  | actionEventKind (alt1 : Bool := false) (alt2 : Bool := false) (alt3 : Bool := false) (gameAction : Bool := false)
deriving Repr, Inhabited, BEq, DecidableEq

namespace ActionEvent
@[match_pattern] abbrev loyaltyScryOrRingAction (alt : Bool := false) (scry : Bool := false) (ring : Bool := false) : ActionEvent :=
  .actionEventKind alt scry ring false
@[match_pattern] abbrev gameActionKind (alt1 : Bool := false) (alt2 : Bool := false) (tokenOrLife : Bool := false) : ActionEvent :=
  .actionEventKind alt1 alt2 tokenOrLife true
@[match_pattern] abbrev activateLoyaltyAbility (opponent : Bool := false) : ActionEvent :=
  .loyaltyScryOrRingAction opponent false false
@[match_pattern] abbrev youScry (orSurveil : Bool := false) : ActionEvent :=
  .loyaltyScryOrRingAction orSurveil true false
@[match_pattern] abbrev ringTempts (chooseBearerOnly : Bool := false) : ActionEvent :=
  .loyaltyScryOrRingAction chooseBearerOnly false true
@[match_pattern] abbrev abilityOrTargetOrSacAction (becomesTargetOrSac : Bool := false) (youTargetOrSac : Bool := false) : ActionEvent :=
  .gameActionKind becomesTargetOrSac youTargetOrSac false
@[match_pattern] abbrev tokenOrLifeAction (createTokensOrGainLife : Bool := false) (gainOrLoseLife : Bool := false) : ActionEvent :=
  .gameActionKind createTokensOrGainLife gainOrLoseLife true
@[match_pattern] abbrev youActivateCreatureAbility : ActionEvent := .gameActionKind false false false
@[match_pattern] abbrev becomesTarget : ActionEvent := .gameActionKind true false false
@[match_pattern] abbrev youTargetSomething : ActionEvent := .gameActionKind false true false
@[match_pattern] abbrev youSacrificeToken : ActionEvent := .gameActionKind true true false
@[match_pattern] abbrev bolgSacrificedForReflexive : ActionEvent := .gameActionKind false false true
@[match_pattern] abbrev youCreateCreatureTokens : ActionEvent := .gameActionKind true false true
@[match_pattern] abbrev youGainLife : ActionEvent := .gameActionKind true true true
@[match_pattern] abbrev playerLosesLife : ActionEvent := .gameActionKind false true true
end ActionEvent

end TriggerEvent

/-- When a triggered ability fires (CR 603). -/
inductive TriggerEvent where
  /-- Atomic trigger event (CR 603): enters (`entersOpt = some w`), leaves (`leavesOpt = some w`), step/taps (`isStepOrTaps = true`), casts (`castsOpt = some w`), combat (`combatOpt = some w`), damage (`damageOpt = some w`), draws/discards (`isDrawsOrDiscards = true`), or counters/action/special (`isCountersOrAction = true`). -/
  | atomicTriggerEvent (entersOpt : Option TriggerEvent.EntersEvent := none)
      (leavesOpt : Option TriggerEvent.LeavesEvent := none)
      (stepWhich : TriggerEvent.StepEvent := .upkeep false)
      (tapWhat : TriggerEvent.TapEvent := .source) (isTap : Bool := false)
      (isStepOrTaps : Bool := false)
      (castsOpt : Option TriggerEvent.CastEvent := none)
      (combatOpt : Option TriggerEvent.CombatEvent := none)
      (damageOpt : Option TriggerEvent.DamageEvent := none)
      (drawWhat : TriggerEvent.DrawEvent := .youCard)
      (discardWhat : TriggerEvent.DiscardEvent := .youCard) (isDiscard : Bool := false)
      (isDrawsOrDiscards : Bool := false)
      (counterWhat : TriggerEvent.CounterEvent := .youPutPlusOne)
      (actionWhat : TriggerEvent.ActionEvent := .youActivateCreatureAbility)
      (fromEffectFlag : Bool := false) (isAction : Bool := false) (isSpecial : Bool := false)
      (isCountersOrAction : Bool := false)
  /-- Triggers when at least one of the two given conditions triggers. -/
  | or (a b : TriggerEvent)
deriving Repr, Inhabited, BEq, DecidableEq

/-- Unified alias for `TriggerEvent`. -/
abbrev FraEvent := TriggerEvent

/-- Unified alias for `TriggerEvent`. -/
abbrev SharedTriggerWhen := TriggerEvent

namespace TriggerEvent

/-- Identity wrapper kept for `TriggerEvent.fra` call sites. -/
abbrev fra (e : TriggerEvent) : TriggerEvent := e

@[match_pattern] abbrev enters (what : TriggerEvent.EntersEvent := .source) : TriggerEvent :=
  .atomicTriggerEvent (some what) none (.upkeep false) .source false false none none none .youCard .youCard false false .youPutPlusOne .youActivateCreatureAbility false false false false
@[match_pattern] abbrev leaves (what : TriggerEvent.LeavesEvent := .source) : TriggerEvent :=
  .atomicTriggerEvent none (some what) (.upkeep false) .source false false none none none .youCard .youCard false false .youPutPlusOne .youActivateCreatureAbility false false false false
@[match_pattern] abbrev stepOrTaps (which : TriggerEvent.StepEvent := .upkeep false)
    (tapWhat : TriggerEvent.TapEvent := .source) (isTap : Bool := false) : TriggerEvent :=
  .atomicTriggerEvent none none which tapWhat isTap true none none none .youCard .youCard false false .youPutPlusOne .youActivateCreatureAbility false false false false
@[match_pattern] abbrev casts (what : TriggerEvent.CastEvent := .spell) : TriggerEvent :=
  .atomicTriggerEvent none none (.upkeep false) .source false false (some what) none none .youCard .youCard false false .youPutPlusOne .youActivateCreatureAbility false false false false
@[match_pattern] abbrev combat (what : TriggerEvent.CombatEvent := .sourceAttacks) : TriggerEvent :=
  .atomicTriggerEvent none none (.upkeep false) .source false false none (some what) none .youCard .youCard false false .youPutPlusOne .youActivateCreatureAbility false false false false
@[match_pattern] abbrev damage (what : TriggerEvent.DamageEvent := .sourceCombatToPlayer) : TriggerEvent :=
  .atomicTriggerEvent none none (.upkeep false) .source false false none none (some what) .youCard .youCard false false .youPutPlusOne .youActivateCreatureAbility false false false false
@[match_pattern] abbrev drawsOrDiscards (drawWhat : TriggerEvent.DrawEvent := .youCard)
    (discardWhat : TriggerEvent.DiscardEvent := .youCard) (isDiscard : Bool := false) : TriggerEvent :=
  .atomicTriggerEvent none none (.upkeep false) .source false false none none none drawWhat discardWhat isDiscard true .youPutPlusOne .youActivateCreatureAbility false false false false
@[match_pattern] abbrev countersOrAction (counterWhat : TriggerEvent.CounterEvent := .youPutPlusOne)
    (actionWhat : TriggerEvent.ActionEvent := .youActivateCreatureAbility)
    (fromEffectFlag : Bool := false) (isAction : Bool := false) (isSpecial : Bool := false) : TriggerEvent :=
  .atomicTriggerEvent none none (.upkeep false) .source false false none none none .youCard .youCard false false counterWhat actionWhat fromEffectFlag isAction isSpecial true
@[match_pattern] abbrev step (which : TriggerEvent.StepEvent) : TriggerEvent :=
  .stepOrTaps which .source false
@[match_pattern] abbrev taps (what : TriggerEvent.TapEvent := .source) : TriggerEvent :=
  .stepOrTaps (.upkeep false) what true
@[match_pattern] abbrev draws (what : TriggerEvent.DrawEvent := .youCard) : TriggerEvent :=
  .drawsOrDiscards what .youCard false
@[match_pattern] abbrev discards (what : TriggerEvent.DiscardEvent := .youCard) : TriggerEvent :=
  .drawsOrDiscards .youCard what true
@[match_pattern] abbrev counters (what : TriggerEvent.CounterEvent) : TriggerEvent :=
  .countersOrAction what .youActivateCreatureAbility false false false
@[match_pattern] abbrev action (what : TriggerEvent.ActionEvent) : TriggerEvent :=
  .countersOrAction .youPutPlusOne what false true false
@[match_pattern] abbrev specialTrigger (fromEffect : Bool := false) : TriggerEvent :=
  .countersOrAction .youPutPlusOne .youActivateCreatureAbility fromEffect false true
@[match_pattern] abbrev cascade : TriggerEvent := .specialTrigger false
@[match_pattern] abbrev fromEffect : TriggerEvent := .specialTrigger true

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
