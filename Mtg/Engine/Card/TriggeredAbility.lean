import Mtg.Engine.Card.ChapterEffects
import Mtg.Engine.Card.SpellEffects
import Mtg.Engine.Card.TriggerEffects

/-!
# Printed triggered abilities (CR 603)

Named constructors for the printed triggered-ability wordings and their
Oracle-text rendering, backed exclusively by unified `Instruction` bodies.
-/

namespace Mtg.Engine

namespace TriggeredAbility

/-- Build a triggered ability from a `TriggerPattern` and a unified `Effect`. -/
def mkTrigger (pattern : TriggerPattern) (effect : Effect)
    (word : TriggerWord := pattern.defaultWord)
    (grouping : BatchGrouping := .perOccurrence)
    (interveningIf? : Option Condition := none)
    (activeZones : Array ZoneKind := #[.battlefield])
    (limit : TriggerLimit := .unlimited) : TriggeredAbility :=
  { word, pattern, grouping, interveningIf?, activeZones, limit, effect }

/-- Construct a triggered ability directly from a `TriggerPattern` and unified `Instruction`. -/
def ofPattern (pattern : TriggerPattern) (body : Instruction)
    (spec : TargetSpec := .none)
    (grouping : BatchGrouping := .perOccurrence)
    (interveningIf? : Option Condition := none)
    (activeZones : Array ZoneKind := #[.battlefield])
    (limit : TriggerLimit := .unlimited)
    (word : TriggerWord := pattern.defaultWord) : TriggeredAbility :=
  { word, pattern, grouping, interveningIf?, activeZones, limit,
    effect := { targets := spec, body } }

/-! ### Catalog constructors for reusable triggered abilities -/

def onEnterScry (n : Nat) : TriggeredAbility := mkTrigger .thisEnters (Effect.triggerScry n)
def onAttackScry (n : Nat) : TriggeredAbility := mkTrigger .thisAttacks (Effect.triggerScry n)
def onAttackWithElvesScry (n : Nat) : TriggeredAbility :=
  mkTrigger (.youAttackWithSubtype .elf) (Effect.triggerScry n) (grouping := .oncePerBatch)
def onOneOrMoreOtherCreaturesDieScry (n : Nat) : TriggeredAbility :=
  mkTrigger .otherCreaturesDie (Effect.triggerScry n) (grouping := .oncePerBatch)
def onCastColorScry (c : Color) (n : Nat) : TriggeredAbility :=
  mkTrigger (.youCastColor c) (Effect.triggerScry n)
def onEnterDraw (n : Nat) : TriggeredAbility := mkTrigger .thisEnters (Effect.triggerDraw n)
def onDiesDraw (n : Nat) : TriggeredAbility := mkTrigger .thisDies (Effect.triggerDraw n)
def onYouAttackDraw : TriggeredAbility :=
  mkTrigger .youAttack (Effect.triggerDraw 1) (grouping := .oncePerBatch)
def onYourEndStepDraw : TriggeredAbility := mkTrigger .stepYourEndStep (Effect.triggerDraw 1)
def onBecomesTargetDraw : TriggeredAbility :=
  mkTrigger .thisBecomesTargetByOpponent (Effect.triggerDraw 1)
def onArtifactYouControlEntersDraw : TriggeredAbility :=
  mkTrigger .artifactYouControlEnters (Effect.triggerDraw 1)
def onTheRingTemptsYouDraw (n : Nat) : TriggeredAbility :=
  mkTrigger .theRingTemptsYou (Effect.triggerDraw n)
def onChooseRingBearerDraw : TriggeredAbility :=
  mkTrigger .youChooseRingBearer (Effect.triggerDraw 1)
def onCombatDamageDraw (n : Nat) : TriggeredAbility :=
  mkTrigger .thisDealsCombatDamageToPlayer (Effect.triggerDraw n)
def onEachOpponentDrawStepDraw : TriggeredAbility :=
  mkTrigger .stepEachOpponentDrawStep (Effect.triggerDraw 1)
def onEnterCreateTokens (kind : TokenSpec) (n : Nat) (tapped : Bool := false) :
    TriggeredAbility :=
  mkTrigger .thisEnters (Effect.triggerCreateTokens kind n tapped)
def onYourUpkeepCreateTokens (kind : TokenSpec) (n : Nat) : TriggeredAbility :=
  mkTrigger .stepYourUpkeep (Effect.triggerCreateTokens kind n)
def onLandYouControlEntersCreateTokens (kind : TokenSpec) (n : Nat) :
    TriggeredAbility :=
  mkTrigger .landYouControlEnters (Effect.triggerCreateTokens kind n)
def onDiesCreateTokens (kind : TokenSpec) (n : Nat) : TriggeredAbility :=
  mkTrigger .thisDies (Effect.triggerCreateTokens kind n)
def onYouDrawSecondCreateTokens (kind : TokenSpec) : TriggeredAbility :=
  mkTrigger (.drawCard .you) (Effect.triggerCreateTokens kind 1) (limit := .nthEachTurn 2)
def onCastColorCreateTokens (c : Color) (kind : TokenSpec) (n : Nat) :
    TriggeredAbility :=
  mkTrigger (.youCastColor c) (Effect.triggerCreateTokens kind n)
def onEnterOrAttackCreateWall : TriggeredAbility :=
  mkTrigger .enterOrAttack (Effect.triggerCreateTokens .wall 1)
def onEnterAmassGoblins (n : Nat) : TriggeredAbility :=
  mkTrigger .thisEnters (Effect.triggerAmass n .goblin)
def onDiesAmassGoblins (n : Nat) : TriggeredAbility :=
  mkTrigger .thisDies (Effect.triggerAmass n .goblin)
def onYouAttackAmassGoblins (n : Nat) : TriggeredAbility :=
  mkTrigger .youAttack (Effect.triggerAmass n .goblin) (grouping := .oncePerBatch)
def onCastNoncreatureAmassGoblins (n : Nat) : TriggeredAbility :=
  mkTrigger .youCastNoncreature (Effect.triggerAmass n .goblin)
def onEnterOrAttackAmassGoblins (n : Nat) : TriggeredAbility :=
  mkTrigger .enterOrAttack (Effect.triggerAmass n .goblin)
def onCreatureCardLeavesYourGyAmassGoblins (n : Nat) : TriggeredAbility :=
  mkTrigger .creatureCardLeavesYourGy (Effect.triggerAmass n .goblin)
def onEnterRecruit : TriggeredAbility := mkTrigger .thisEnters Effect.triggerRecruit
def onDiesRecruit : TriggeredAbility := mkTrigger .thisDies Effect.triggerRecruit
def onEnterOrAttackRecruit : TriggeredAbility := mkTrigger .enterOrAttack Effect.triggerRecruit
def onYouAttackRecruit : TriggeredAbility :=
  mkTrigger .youAttack Effect.triggerRecruit (grouping := .oncePerBatch)
def onEnterDealDividedDamage (amount maxTargets : Nat) : TriggeredAbility :=
  mkTrigger .thisEnters (Effect.triggerDividedDamage amount maxTargets)
def onEnterOrAttackDealDividedDamage (amount maxTargets : Nat) : TriggeredAbility :=
  mkTrigger .enterOrAttack (Effect.triggerDividedDamage amount maxTargets)
def onEnterPlusOneOnCreature : TriggeredAbility :=
  mkTrigger .thisEnters { targets := .creature, body := Instruction.putPlusOne (.target 0) 1 }
def onEnterOrAttackPlusOneOnCreature : TriggeredAbility :=
  mkTrigger .enterOrAttack { targets := .creature, body := Instruction.putPlusOne (.target 0) 1 }
def onLandYouControlEntersPlusOnePlusOne : TriggeredAbility :=
  mkTrigger .landYouControlEnters { targets := .creatureYouControl, body := Instruction.putPlusOne (.target 0) 1 }
def onCombatPlusOneOnCreatureYouControl : TriggeredAbility :=
  mkTrigger .stepYourBeginCombat { targets := .creatureYouControl, body := Instruction.putPlusOne (.target 0) 1 }
def onEnterAttachToSubtype (subtype : String) : TriggeredAbility :=
  mkTrigger .thisEnters (Effect.triggerAttachTo (.creatureYouControlSubtype (CardSubtype.ofOracleD subtype)))
def onEnterAttachToLegendary : TriggeredAbility :=
  mkTrigger .thisEnters (Effect.triggerAttachTo .legendaryCreatureYouControl)
def onEnterAttachToCreatureYouControl : TriggeredAbility :=
  mkTrigger .thisEnters (Effect.triggerAttachTo .creatureYouControl)
def onEnterTargetOpponentSacrificesCreature : TriggeredAbility :=
  mkTrigger .thisEnters Effect.triggerOpponentSacrificesCreature
def onEnterTargetOpponentSacrifices : TriggeredAbility :=
  onEnterTargetOpponentSacrificesCreature
def onDrawSecondPlusOne : TriggeredAbility :=
  mkTrigger (.drawCard .you) { body := Instruction.putPlusOne .this 1 } (limit := .nthEachTurn 2)
def onDrawPlusOne : TriggeredAbility :=
  mkTrigger (.drawCard .you) { body := Instruction.putPlusOne .this 1 }
def onGainLifePlusOne : TriggeredAbility :=
  mkTrigger (.gainLife .you) { body := Instruction.putPlusOne .this 1 }
def onAnotherArtifactEntersPlusOne : TriggeredAbility :=
  mkTrigger .anotherArtifactYouControlEnters { body := Instruction.putPlusOne .this 1 }
/-- CR 603.4 intervening-if Ferocious trigger at beginning of combat (rechecked on resolution). -/
def onYourBeginCombatFerociousPlusOne : TriggeredAbility :=
  mkTrigger .stepYourBeginCombat { body := Instruction.putPlusOne .this 1 }
    (interveningIf? := some (condControlCreaturePowerAtLeast 4))
def onEquippedAttacksAloneDrawLoseLife : TriggeredAbility :=
  mkTrigger .equippedAttacksAlone Effect.seqDrawAndLoseLife
/-- CR 603.2 `"while you control..."` attack trigger (checked at trigger time, not on resolution). -/
def onYouAttackFerociousDrawLoseLife : TriggeredAbility :=
  mkTrigger (.whenCond .youAttack (condControlCreaturePowerAtLeast 4))
    Effect.seqDrawAndLoseLife (grouping := .oncePerBatch)
def onCastWithTreasureDrawLoseLife : TriggeredAbility :=
  mkTrigger .youCastWithTreasure Effect.seqDrawAndLoseLife
def onYourEndStepDrawLoseLife : TriggeredAbility :=
  mkTrigger .stepYourEndStep Effect.seqDrawAndLoseLife
def onEnterConnive : TriggeredAbility := mkTrigger .thisEnters Effect.triggerConniveSource
def onAttackConnive : TriggeredAbility := mkTrigger .thisAttacks Effect.triggerConniveSource
def onYouCastColorFromHandConnive (color : Color) : TriggeredAbility :=
  mkTrigger (.youCastColorFromHand color) Effect.triggerConniveSource
def onEquippedCreatureYouControlAttacksConnive : TriggeredAbility :=
  mkTrigger .equippedCreatureYouControlAttacks Effect.triggerConniveSource
def onCombatTargetYouControlConnives : TriggeredAbility :=
  mkTrigger .stepYourBeginCombat (Effect.triggerConniveTarget .creatureYouControl)
def onEnterExileOppNonlandUntilLeaves : TriggeredAbility :=
  mkTrigger .thisEnters (Effect.triggerExileUntilLeaves .oppNonland)
def onEnterExileOppTappedUntilLeaves : TriggeredAbility :=
  mkTrigger .thisEnters (Effect.triggerExileUntilLeaves .oppTappedCreature)
def onAttackMayExileDefenderUntilLeaves : TriggeredAbility :=
  mkTrigger .thisAttacks (Effect.triggerExileUntilLeaves .defendingPlayerCreature (allowsZeroTargets := true))
def onEnterGainLife (n : Nat) : TriggeredAbility := mkTrigger .thisEnters (Effect.triggerGainLife n)
/-- CR 603.2 `"while you control..."` attack trigger (checked at trigger time, not on resolution). -/
def onAttackFerociousGainLife (n : Nat) : TriggeredAbility :=
  mkTrigger (.whenCond .thisAttacks (condControlCreaturePowerAtLeast 4)) (Effect.triggerGainLife n)
def onLandYouControlEntersGainLife (n : Nat) : TriggeredAbility :=
  mkTrigger .landYouControlEnters (Effect.triggerGainLife n)
def onEnterTargetGets (power toughness : Int) : TriggeredAbility :=
  mkTrigger .thisEnters { targets := .creature, body := Instruction.pumpFixed (.target 0) power toughness }
def onDiesOppCreatureGets (power toughness : Int) : TriggeredAbility :=
  mkTrigger .thisDies { targets := .oppCreature, body := Instruction.pumpFixed (.target 0) power toughness }
def onCastColorPump (color : Color) (power toughness : Int) : TriggeredAbility :=
  mkTrigger (.youCastColor color) { targets := .creature, body := Instruction.pumpFixed (.target 0) power toughness }
def onLandYouControlEntersGets (power toughness : Int) : TriggeredAbility :=
  mkTrigger .landYouControlEnters { body := Instruction.pumpFixed .this power toughness }
def onAttackFerociousSourceGets (power toughness : Int) : TriggeredAbility :=
  mkTrigger (.whenCond .thisAttacks (condControlCreaturePowerAtLeast 4))
    { body := Instruction.pumpFixed .this power toughness }
def onAnotherElfYouControlEntersGets1 : TriggeredAbility :=
  mkTrigger (.anotherSubtypeYouControlEnters .elf) { body := Instruction.pumpFixed .this 1 1 }
def onArtifactYouControlEntersDrawOnce : TriggeredAbility :=
  mkTrigger .artifactYouControlEnters (Effect.triggerDraw 1) (limit := .onceEachTurn)
def onActivateCreatureAbilityDrawOnce : TriggeredAbility :=
  mkTrigger .youActivateCreatureAbility (Effect.triggerDraw 1) (limit := .onceEachTurn)
def onAnotherSubtypeOrEquipmentEntersDrawOnce (subtype : String) : TriggeredAbility :=
  mkTrigger (.anotherSubtypeOrEquipmentYouControlEnters (CardSubtype.ofOracleD subtype))
    (Effect.triggerDraw 1) (limit := .onceEachTurn)
def onEachEndStepDrawIfGainedLife (n : Nat) : TriggeredAbility :=
  mkTrigger .stepEachEndStep (Effect.triggerDraw 1) (interveningIf? := some (condGainedLifeAtLeast n))
def onThisOrNontokenSubtypeEntersCreateTokens (subtype : String) (kind : TokenSpec)
    (n : Nat) : TriggeredAbility :=
  mkTrigger (.thisOrNontokenSubtypeYouControlEnters (CardSubtype.ofOracleD subtype))
    (Effect.triggerCreateTokens kind n)
def onThisOrAnotherSubtypeEntersCreateTokens (subtype : String) (kind : TokenSpec)
    (n : Nat) : TriggeredAbility :=
  mkTrigger (.thisOrAnotherSubtypeYouControlEnters (CardSubtype.ofOracleD subtype))
    (Effect.triggerCreateTokens kind n)
def onSubtypeYouControlCombatDamageCreateTokens (subtype : String) (kind : TokenSpec)
    (n : Nat) : TriggeredAbility :=
  let sub := CardSubtype.ofOracleD subtype
  mkTrigger
    (.damageDealt
      (.all #[.hasSubtype (.literal sub), .controlledBy .you])
      (.playerOrObject .any { zones := .battlefield, pred := .hasType .battle })
      (combatOnly := true))
    (Effect.triggerCreateTokens kind n)
def onOpponentDrawsSecondCreateTreasure : TriggeredAbility :=
  mkTrigger (.drawCard .opponent) (Effect.triggerCreateTokens .treasure 1) (limit := .nthEachTurn 2)
def onOpponentCastsFirstNoncreatureRecruit : TriggeredAbility :=
  mkTrigger .opponentCastsFirstNoncreature Effect.triggerRecruit
def onCastColorDamageOpponent (color : Color) (n : Nat) : TriggeredAbility :=
  mkTrigger (.youCastColor color) (Effect.triggerDamageTargetOpponent n)
def onCastGreenOrForestEntersPlusOne : TriggeredAbility :=
  mkTrigger .castGreenOrForestEnters { targets := .creatureYouControl, body := Instruction.putPlusOne (.target 0) 1 }
def onAttackOtherGets2AndTrample : TriggeredAbility :=
  mkTrigger .thisAttacks { targets := .anotherCreatureYouControl, body := Instruction.pumpAndTrample (.target 0) 2 0 }
def onEnterMayDiscardDraw (n : Nat) : TriggeredAbility :=
  mkTrigger .thisEnters (Effect.triggerMayDiscardDraw n)
def onCastInstantOrSorceryDealDamageToEachOpponent (amount : Nat) : TriggeredAbility :=
  mkTrigger .youCastInstantOrSorcery (Effect.triggerDamageEachOpponent amount)
def onEnterEachOpponentDiscards : TriggeredAbility :=
  mkTrigger .thisEnters (Effect.triggerEachOpponentDiscards 1)
def onEnterExileTop : TriggeredAbility := mkTrigger .thisEnters Effect.triggerExileTop
def onAttackTargetGainsKeywords (k : Array KeywordAbility) : TriggeredAbility :=
  mkTrigger .thisAttacks { targets := .attackingCreature, body := Instruction.grantKeywords (.target 0) k }
def onDrawSecondMillPlayer (n : Nat) : TriggeredAbility :=
  mkTrigger (.drawCard .you) (Effect.triggerMillPlayer n) (limit := .nthEachTurn 2)
def onAnotherGoblinOrcArmyDiesExileTop : TriggeredAbility :=
  mkTrigger .anotherGoblinOrcArmyYouControlDies Effect.triggerExileTop
def onAnotherSubtypeEntersPlusOneOnSource (subtype : String) (n : Nat) :
    TriggeredAbility :=
  mkTrigger (.anotherSubtypeYouControlEnters (CardSubtype.ofOracleD subtype))
    { body := Instruction.putPlusOne .this n }
def onOpponentCastsAmassOrcs (n : Nat) : TriggeredAbility :=
  mkTrigger .opponentCastsSpell (Effect.triggerAmass n .orc)
def onCreatureYouControlAttacksAloneInvestigate : TriggeredAbility :=
  mkTrigger .creatureYouControlAttacksAlone Effect.triggerInvestigate
def onCreatureYouControlAttacksAlonePump (power toughness : Int) : TriggeredAbility :=
  mkTrigger .creatureYouControlAttacksAlone (Effect.triggerPumpCause power toughness)
def onEnterTargetOpponentDiscards (n : Nat) : TriggeredAbility :=
  mkTrigger .thisEnters (Effect.triggerTargetOpponentDiscards n)
def onEquipmentYouControlEntersDraw : TriggeredAbility :=
  mkTrigger .equipmentYouControlEnters (Effect.triggerDraw 1)
def onEnterSearchForest : TriggeredAbility := mkTrigger .thisEnters Effect.triggerSearchForest
def onEnterSearchBasicToHand : TriggeredAbility :=
  mkTrigger .thisEnters Effect.triggerSearchBasicLandToHand
def onEnterEachPlayerSacrificesCreature : TriggeredAbility :=
  mkTrigger .thisEnters Effect.triggerEachPlayerSacrificesCreature
def onEnterMayExileAnotherCreature : TriggeredAbility :=
  mkTrigger .thisEnters (Effect.triggerExileTarget .anotherCreature (allowsZeroTargets := true))
def onEnterReturnCreatureFromGyToHand : TriggeredAbility :=
  mkTrigger .thisEnters Effect.triggerReturnCreatureFromGyToHand
def onCombatDamageToPlayerLoot : TriggeredAbility :=
  mkTrigger .thisDealsCombatDamageToPlayer (Effect.seqDrawThenDiscard 1)
def onAttackFerociousPlusOneEach : TriggeredAbility :=
  mkTrigger (.whenCond .thisAttacks (condControlCreaturePowerAtLeast 4))
    Effect.triggerPlusOneEachYouControl
def onAttackFerociousSourceGetsAndTeamTrample (power : Int) : TriggeredAbility :=
  mkTrigger (.whenCond .thisAttacks (condControlCreaturePowerAtLeast 4))
    (Effect.seqSourceGetsAndTeamTrample power)
def onEnterOrAttackHoneEachEquipment : TriggeredAbility :=
  mkTrigger .enterOrAttack Effect.triggerHoneEachEquipment
def onEnterOrAttackPlusOneEachOtherGainLife : TriggeredAbility :=
  mkTrigger .enterOrAttack Effect.triggerPlusOneEachOtherGainLife
def onLandYouControlEntersBecomePT (power toughness : Int) : TriggeredAbility :=
  mkTrigger .landYouControlEnters (Effect.triggerBecomePT power toughness)
def onCastNoncreaturePumpAndDamageOpponents (n : Nat) : TriggeredAbility :=
  mkTrigger .youCastNoncreature (Effect.seqPumpAndDamageOpponents n)
def onDrawSecondPlusOneLifelink : TriggeredAbility :=
  mkTrigger (.drawCard .you) (Effect.seqPlusOneAndLifelink .creature) (limit := .nthEachTurn 2)
def onYouAttackPumpTargetPerPlains : TriggeredAbility :=
  mkTrigger .youAttack Effect.triggerPumpTargetPerPlains (grouping := .oncePerBatch)
def onAnotherLegendarySubtypeEntersLoot (subtype : String) : TriggeredAbility :=
  mkTrigger
    (.permanentEnters (.all #[
      .otherThan .this, .hasSupertype .legendary,
      .hasSubtype (.literal (CardSubtype.ofOracleD subtype)), .controlledBy .you]))
    (Effect.seqDrawThenDiscard 2)
def onRingTemptsMayDiscardDraw (n : Nat) : TriggeredAbility :=
  mkTrigger .theRingTemptsYou (Effect.triggerMayDiscardHandDraw n)
def onScryPumpSelfForEachLookedAt : TriggeredAbility :=
  mkTrigger .youScry Effect.triggerPumpByLookedAt
def onScryPumpAndUnblockableOnce : TriggeredAbility :=
  mkTrigger .youScry Effect.seqPumpAndUnblockable (limit := .onceEachTurn)
def onAttackPumpByGreatestPower : TriggeredAbility :=
  mkTrigger .thisAttacks Effect.triggerPumpGreatestPower
def onBecomesBlockedDeal1ToBlockers : TriggeredAbility :=
  mkTrigger .thisBecomesBlocked (Effect.triggerDamageBlockers 1)
def onAttackPumpForEachOtherCreature : TriggeredAbility :=
  mkTrigger .thisAttacks Effect.triggerPumpForEachOtherCreature
def onAttackWithTwoOrMoreGrantFlying : TriggeredAbility :=
  mkTrigger .youAttackWithTwoOrMoreToPlayer
    { targets := .attackingCreatureWithoutFlying, body := Instruction.grantKeywords (.target 0) #[Keyword.flying] }
    (grouping := .perPlayerInBatch)
def onLeaveReturnExiled : TriggeredAbility := mkTrigger .thisLeaves Effect.triggerReturnLinkedExile
def onEnterCreateThenAttach (kind : TokenSpec) : TriggeredAbility :=
  mkTrigger .thisEnters (Effect.triggerCreateThenAttach kind)
def onEnterAmassThenAttach (n : Nat) : TriggeredAbility :=
  mkTrigger .thisEnters (Effect.triggerAmassThenAttach n .goblin)
def onEnterGainLifeSearchBasicOnTop (n : Nat) : TriggeredAbility :=
  mkTrigger .thisEnters (Effect.triggerGainLifeSearchBasicOnTop n)
def onYourFirstMainAddMana (types : Array ManaType) : TriggeredAbility :=
  mkTrigger .stepYourFirstMain (Effect.triggerAddMana types)
def onEnterCreateAxe : TriggeredAbility :=
  mkTrigger .thisEnters (Effect.triggerCreateAxe false)
def onLandYouControlEntersTapOrUntap : TriggeredAbility :=
  mkTrigger .landYouControlEnters Effect.triggerTapOppOrUntapYours
def onEnterGainControlOppUntilEot : TriggeredAbility :=
  mkTrigger .thisEnters Effect.triggerGainControlOppUntilEot
def onEnterCreateAxeAttach : TriggeredAbility :=
  mkTrigger .thisEnters (Effect.triggerCreateAxe true)
def onDiesAmassGoblinsEqualPower : TriggeredAbility :=
  mkTrigger .thisDies (Effect.triggerAmassSourcePower .goblin)
def onLandYouControlEntersPayReturnFromGy : TriggeredAbility :=
  mkTrigger .landYouControlEnters Effect.triggerPayReturnFromGy (activeZones := #[.graveyard])
def onYouSacrificeTokenOppLosesLife : TriggeredAbility :=
  mkTrigger .youSacrificeToken (Effect.triggerTargetOpponentLosesLife 1)
def onLandYouControlEntersPlusOneVigilance : TriggeredAbility :=
  mkTrigger .landYouControlEnters (Effect.seqPlusOneVigilance 2)
def onCastNoncreatureMayDrawXDiscard2 : TriggeredAbility :=
  mkTrigger .youCastNoncreature (Effect.triggerMayDrawXDiscard 2)
def onLandYouControlEntersDrawPlusOneSource : TriggeredAbility :=
  mkTrigger .landYouControlEnters Effect.seqDrawPlusOneSource
def onArmyCombatDamageRingTempts : TriggeredAbility :=
  mkTrigger .armyYouControlCombatDamageToPlayer Effect.triggerRingTempts
def onAttackSetOtherBasePT : TriggeredAbility :=
  mkTrigger .thisAttacks Effect.triggerSetOtherBasePT
def onEnterOrAttackReturnElfGainLife : TriggeredAbility :=
  mkTrigger .enterOrAttack Effect.triggerReturnElfGainLife
def onDiesDealDamageEqualToPowerToOppCreature : TriggeredAbility :=
  mkTrigger .thisDies Effect.triggerDamageFromLastKnownPower
def onEnterExileOppGyCardOppsLoseLife (life : Nat) : TriggeredAbility :=
  mkTrigger .thisEnters (Effect.seqExileOppGyCardOppsLoseLife life)
def onEnterCreaturesYouControlGetAndFirstStrike (power : Int) : TriggeredAbility :=
  mkTrigger .thisEnters (Effect.seqCreaturesPumpAndFirstStrike power)
def onAnotherCreatureYouControlPowerAtMostEntersMayPayDraw (power : Int)
    (generic : Nat) : TriggeredAbility :=
  mkTrigger
    (.permanentEnters (.all #[
      .otherThan .this, .hasType .creature, .controlledBy .you, .stat .power .le (.const power)]))
    (Effect.triggerMayPayGenericDraw generic)
def onEnterDrawThenBottomIfNoLegendary : TriggeredAbility :=
  mkTrigger .thisEnters Effect.triggerDrawThenBottomIfNoLegendary
def onYourEndStepRemoveHopeDrawSac : TriggeredAbility :=
  mkTrigger .stepYourEndStep Effect.triggerRemoveHopeDrawSac
def onAttackTapHumansDraw : TriggeredAbility := mkTrigger .thisAttacks Effect.triggerTapHumansDraw
def onEnterUntapOtherPlusOneIfSubtype (subtype : String) : TriggeredAbility :=
  mkTrigger .thisEnters (Effect.seqUntapPlusOneIfSubtype subtype)
def onEnterDestroyOppArtifactsEnchantmentsGainLife : TriggeredAbility :=
  mkTrigger .thisEnters Effect.triggerDestroyOppArtifactsEnchantmentsGainLife
def onAttackDamageEqualSubtypeToEachOpponent (subtype : String) : TriggeredAbility :=
  mkTrigger .thisAttacks (Effect.triggerDamageEqualSubtypeToEachOpponent (CardSubtype.ofOracleD subtype))
def onAttackDamageEqualTreasures : TriggeredAbility :=
  mkTrigger .thisAttacks Effect.triggerDamageEqualTreasures
def onPlayerCastsSecondSpellLoseLifeCreateTreasure : TriggeredAbility :=
  mkTrigger .anyPlayerCastsSecondSpell Effect.seqLoseLifeCreateTreasure
def onEnterDealDamageDestroyIfSubtype (n : Nat) (subtype : String) : TriggeredAbility :=
  mkTrigger .thisEnters (Effect.triggerDealDamageDestroyIfSubtype n (CardSubtype.ofOracleD subtype))
def onEnterAttachTargetEquipment : TriggeredAbility :=
  mkTrigger .thisEnters Effect.triggerAttachEquipmentToCreature
def onAttackDefenderSacsLeastPower : TriggeredAbility :=
  mkTrigger .thisAttacks Effect.triggerDefenderSacsLeastPower
def onEnterReturnOtherPlusOne : TriggeredAbility :=
  mkTrigger .thisEnters Effect.triggerReturnOtherPlusOne
def onEnterLookAtTopRevealTypes (n : Nat) (types : Array String) : TriggeredAbility :=
  mkTrigger .thisEnters (Effect.triggerLookAtTopRevealTypes n types)
def onEnterCreateTappedTreasuresEqualOppArtifacts : TriggeredAbility :=
  mkTrigger .thisEnters Effect.triggerCreateTappedTreasuresEqualOppArtifacts
def onCombatDamagePutNonlandMvAtMost (mv : Nat) : TriggeredAbility :=
  mkTrigger .thisDealsCombatDamageToPlayerOrBattle (Effect.triggerPutNonlandMvAtMostFromGy mv)
def onEachCombatOthersGetAndOppsGet (subtypes : Array String)
    (power toughness oppP oppT : Int) : TriggeredAbility :=
  mkTrigger .stepEachBeginCombat
    (Effect.triggerOthersGetAndOppsGet (CardSubtype.ofSubtypes subtypes) power toughness oppP oppT)
def onCombatDamageWolfPlusOneOrTreasure : TriggeredAbility :=
  mkTrigger .thisDealsCombatDamageToPlayer Effect.triggerWolfPlusOneOrTreasure
def onYourBeginCombatTrampleCounterBecomeBear : TriggeredAbility :=
  mkTrigger .stepYourBeginCombat Effect.triggerTrampleCounterBecomeBear
def onEnterMillThenSubtypeToHand (n : Nat) (subtype : String) : TriggeredAbility :=
  mkTrigger .thisEnters (Effect.triggerMillThenSubtypeToHand n (CardSubtype.ofOracleD subtype))
def onEnterExileOppNonlandEachUntilLeaves : TriggeredAbility :=
  mkTrigger .thisEnters Effect.triggerExileOppNonlandEachUntilLeaves
def onCastCreaturePlusOneEqualMv : TriggeredAbility :=
  mkTrigger .youCastCreature Effect.triggerPlusOneEqualLastKnownMv
def onMountainEntersQuestThenDragon : TriggeredAbility :=
  mkTrigger .mountainYouControlEnters Effect.triggerMountainQuestDragon
def onEquippedCombatDamageTreasuresPerChosenType : TriggeredAbility :=
  mkTrigger .equippedDealsCombatDamageToPlayer Effect.triggerTreasuresPerChosenType
def onNontokenYouControlDiesRevealCreature : TriggeredAbility :=
  mkTrigger .nontokenCreatureYouControlDies Effect.triggerRevealUntilCreature (limit := .onceEachTurn)
def onAttackMaySacAnotherPlusOneEqualPower : TriggeredAbility :=
  mkTrigger .thisAttacks Effect.triggerAttackSacPlusOneEqualPower
def onEnterLootLandEntersTapped : TriggeredAbility :=
  mkTrigger .thisEnters Effect.triggerLootLandEntersTapped
def onPlayerLosesLifeMillThatMany : TriggeredAbility :=
  mkTrigger (.loseLife .any) Effect.triggerMillThatManyLost
def onDiesDrawPerFatGraveyard : TriggeredAbility :=
  mkTrigger .thisDies Effect.triggerDrawPerFatGraveyard
def onEnterMaySacDrawTreasure : TriggeredAbility :=
  mkTrigger .thisEnters Effect.triggerMaySacDrawTreasure
def onEquippedAttacksPlusOneEachIfCityBlessing : TriggeredAbility :=
  mkTrigger .equippedAttacks Effect.triggerPlusOneEachCitysBlessing
def onYourBeginCombatCastInstantSorceryFromHand : TriggeredAbility :=
  mkTrigger .stepYourBeginCombat Effect.triggerCastInstantSorceryFromHand
def onEquippedCombatDamageCastInstantSorcery : TriggeredAbility :=
  mkTrigger .equippedDealsCombatDamageToPlayer Effect.triggerCastInstantSorceryMvAtMost
def onCastSecondSpellMillThenCopy : TriggeredAbility :=
  mkTrigger .youCastSecondSpell Effect.triggerMillThenCopy
def onCombatAnotherGetsSourcePower : TriggeredAbility :=
  mkTrigger .stepYourBeginCombat Effect.triggerPumpTargetBySourcePower
def onCombatCreateAlienPerInvasion : TriggeredAbility :=
  mkTrigger .stepYourBeginCombat Effect.triggerCreateAlienPerInvasion
def onCombatMayPutArtifactAttachEquipment : TriggeredAbility :=
  mkTrigger .stepYourBeginCombat Effect.triggerMayPutArtifactAttachEquipment
def onCastCascade : TriggeredAbility :=
  mkTrigger .thisCast Effect.triggerCascade (activeZones := #[.stack])
/-- Photon Blast Barrage cast trigger: copy this spell X times (CR 603.1 / 707.10c). -/
def onCastCopyThisSpellXTimes : TriggeredAbility :=
  mkTrigger .thisCast { body := .stack (.copyStackObject .this .chosenX true) }
    (word := .when) (activeZones := #[.stack])
def onWard (cost : CostSpec) : TriggeredAbility :=
  ofPattern .thisBecomesTargetByOpponent
    (.unlessPays (.controllerOf .triggerSubject) cost (Instruction.counter .triggerSubject))
/-- Path of Ancestry mana-spent commander creature-type scry trigger. -/
def onManaSpentCastCommanderTypeScry (n : Nat := 1) : TriggeredAbility :=
  { word := .when
    pattern := manaSpentCastCommanderCreaturePattern
    effect := Effect.scry n }
/-- CR 702.176a Impending end-step time-counter removal trigger. -/
def impendingEndStep : TriggeredAbility :=
  ofPattern .stepYourEndStep
    (.permanent (.modifyCounters (.remove (some .time) (.exact (.const 1))) .this))
    (interveningIf? := some condImpendingPaidWithTimeCounter)
def onTokenYouControlEntersBelladonna : TriggeredAbility :=
  mkTrigger .tokenYouControlEnters Effect.triggerBelladonnaTokenReward
def onEnterBolgMaySacrifice : TriggeredAbility :=
  mkTrigger .thisEnters Effect.triggerBolgMaySacrifice
def onBolgDealSacrificedPower : TriggeredAbility :=
  mkTrigger .youSacrificeOtherCreature Effect.triggerBolgDealSacrificedPower (word := .when)
def onEquippedAttacksCreateSpirits : TriggeredAbility :=
  mkTrigger .equippedAttacks Effect.triggerCreateSpiritsForEquipped
def onCombatDamageCreateTreasuresEqualPlayerArtifacts : TriggeredAbility :=
  mkTrigger .thisDealsCombatDamageToPlayer Effect.triggerCreateTreasuresEqualDamagedPlayerArtifacts
def onEnterOrOpponentDrawsDeal1AmassOrcs : TriggeredAbility :=
  mkTrigger .enterOrOpponentDrawsExceptFirst Effect.triggerDeal1ThenAmassOrcs
def onAttackWithTotalPowerUntapExtraCombat (n : Int) : TriggeredAbility :=
  mkTrigger (.youAttackWithTotalPower n) Effect.triggerUntapAttackersExtraCombat
    (grouping := .oncePerBatch) (limit := .onceEachTurn)
def onAnotherCreatureYouControlEntersAlliance : TriggeredAbility :=
  mkTrigger .anotherCreatureYouControlEnters Effect.triggerAllianceMode
def onEnterDestroyOtherAmassControllerPower : TriggeredAbility :=
  mkTrigger .thisEnters Effect.triggerDestroyOtherAmassControllerPower
def onOpponentCastsChosenParityModes : TriggeredAbility :=
  mkTrigger .opponentCastsMatchingParity Effect.triggerGollumMode
def onThisOrAnotherSubtypeEntersDiscardHand (subtype : String) : TriggeredAbility :=
  mkTrigger (.thisOrAnotherSubtypeYouControlEnters (CardSubtype.ofOracleD subtype)) Effect.triggerDiscardHandDrawDamageIfStory
def onAttackCastFromGyArtifactInstantSorcery : TriggeredAbility :=
  mkTrigger .thisAttacks Effect.triggerCastFromGyArtifactInstantSorcery
def onAttackEquippedGainDoubleStrike : TriggeredAbility :=
  mkTrigger .thisAttacks Effect.triggerEquippedAttackersGainDoubleStrike
def onEnterTapEnchantedRemoveCounters : TriggeredAbility :=
  mkTrigger .thisEnters Effect.triggerTapEnchantedRemoveCounters
def onDiesRevealTopPutRandomCreature (n : Nat) : TriggeredAbility :=
  mkTrigger .thisDies (Effect.triggerRevealTopPutRandomCreature n)
def onYourBeginCombatIfDrawnTwoPumpFirstStrike : TriggeredAbility :=
  mkTrigger .stepYourBeginCombat Effect.triggerBeginCombatIfDrawnTwoPump
    (interveningIf? := some (condDrawnAtLeast 2))
def onEnterHonePerOppCreaturesAttach : TriggeredAbility :=
  mkTrigger .thisEnters Effect.triggerHonePerOppAttach
def onPutCountersOnGoblinOrcArmyDamageOpp : TriggeredAbility :=
  mkTrigger .youPutCountersOnGoblinOrcArmy (Effect.triggerDamageTargetOpponent 2) (grouping := .oncePerBatch)
def onEnterIfNotTokenCopySelf : TriggeredAbility :=
  mkTrigger .thisEnters Effect.triggerCopySelfNonlegendary (interveningIf? := some condSourceNotToken)
def onEnterAttachEquipmentThenFight : TriggeredAbility :=
  mkTrigger .thisEnters Effect.triggerAttachEquipmentThenFight
def onDiesReturnAsArtifact : TriggeredAbility :=
  mkTrigger .thisCreatureDies Effect.triggerReturnAsArtifact
def onEnterExileLandsThenReturnTapped : TriggeredAbility :=
  mkTrigger .thisEnters Effect.triggerExileLandsThenReturnTapped
def onCombatDamageImpulseInstantSorcery : TriggeredAbility :=
  mkTrigger .thisDealsCombatDamageToPlayer Effect.triggerGrimaImpulse
def onYourEndStepPalantir : TriggeredAbility :=
  mkTrigger .stepYourEndStep Effect.triggerPalantir
def onDealtNoncombatDamageCreateTreasures : TriggeredAbility :=
  mkTrigger .thisDealtNoncombatDamage Effect.triggerTreasuresEqualLastKnown (grouping := .oncePerBatch)
def onEnterIfCastProtectionEverything : TriggeredAbility :=
  mkTrigger .thisEnters Effect.triggerProtectionEverything (interveningIf? := some condSourceWasCast)
def onYourUpkeepLoseLifePerBurden : TriggeredAbility :=
  mkTrigger .stepYourUpkeep Effect.triggerLoseLifePerBurden
def onFinalSagaChapterRevealSaga : TriggeredAbility :=
  mkTrigger .finalSagaChapterResolves Effect.triggerRevealSaga (limit := .onceEachTurn)
def onCombatDamageToYouSacRingTempts : TriggeredAbility :=
  mkTrigger .combatDamageToYou Effect.triggerSacDamagersRingTempts (grouping := .oncePerBatch)
/-- Construct a multi-chapter Saga triggered ability (CR 714.2b). -/
def sagaChapters (chapters : Array Nat) (e : Effect) : TriggeredAbility :=
  { word := .when
    pattern := TriggerPattern.putCountersOnSelf .lore
    grouping := .counterThreshold .lore chapters
    effect := e }
/-- Construct a single-chapter Saga triggered ability (CR 714.2b). -/
def sagaChapter (n : Nat) (e : Effect) : TriggeredAbility :=
  sagaChapters #[n] e
def onTappedForTeamworkPlusOneAndDraw : TriggeredAbility :=
  mkTrigger .thisTappedForTeamwork Effect.seqPlusOneOnSourceAndDraw
def onEachEndStepDrawIfAttackedOrEnteredSubtype (subtype : String) : TriggeredAbility :=
  let sub := CardSubtype.ofOracleD subtype .hero
  mkTrigger .stepEachEndStep (Effect.triggerDraw 1)
    (interveningIf? := some (condAttackedOrEnteredSubtype sub))
def onAttackOthersOfSubtypeGetEqualToughness (subtype : String) : TriggeredAbility :=
  mkTrigger .thisAttacks
    (Effect.triggerOthersOfSubtypeGetEqualSourceToughness (CardSubtype.ofOracleD subtype .hero))
def onCreatureYouControlEntersScryAndPlan (n : Nat) : TriggeredAbility :=
  mkTrigger .creatureYouControlEnters (Effect.triggerScryAndPlan n)
def onCreaturesYouControlBecomeTappedLootAndPlan : TriggeredAbility :=
  mkTrigger .creaturesYouControlBecomeTapped Effect.triggerLootAndPlan (grouping := .oncePerBatch)
def onYouDrawSecondCreateVillainAndPlan : TriggeredAbility :=
  mkTrigger (.drawCard .you) Effect.triggerCreateVillainAndPlan (limit := .nthEachTurn 2)
def onVillainYouControlEntersDrainAndPlan (n : Nat) : TriggeredAbility :=
  mkTrigger (.subtypeYouControlEnters .villain) (Effect.triggerDrainAndPlan n)
def onCreatureCardsToGyDrawLoseLifeAndPlan : TriggeredAbility :=
  mkTrigger .creatureCardPutIntoYourGy Effect.triggerDrawLoseLifeAndPlan (grouping := .oncePerBatch)
def onCastNoncreatureTreasureAndPlan : TriggeredAbility :=
  mkTrigger .youCastNoncreature Effect.triggerTreasureTappedAndPlan
def onLandYouControlEntersPlusOneAndPlan : TriggeredAbility :=
  mkTrigger .landYouControlEnters Effect.triggerPlusOneOnTargetAndPlan
def onNthPlanCounter (n : Nat) (eff : Effect) : TriggeredAbility :=
  mkTrigger (.putCountersOnSelf .plan) eff (word := .when)
    (grouping := .counterThreshold .plan #[n])
def onFourthPlanDrawPlusOneEach : TriggeredAbility :=
  onNthPlanCounter 4 Effect.triggerPlanFinishDrawPlusOneEach
def onFourthPlanReturnInstants : TriggeredAbility :=
  onNthPlanCounter 4 Effect.triggerPlanFinishReturnInstants
def onSeventhPlanControlOpponent : TriggeredAbility :=
  onNthPlanCounter 7 Effect.triggerPlanFinishControlOpponent
def onFifthPlanExileTopCast : TriggeredAbility :=
  onNthPlanCounter 5 Effect.triggerPlanFinishExileTopCast
def onThirdPlanCreateRobots : TriggeredAbility :=
  onNthPlanCounter 3 (Effect.triggerPlanFinishCreateRobots 3)
def onFourthPlanDividedDamage : TriggeredAbility :=
  onNthPlanCounter 4 (Effect.triggerPlanFinishDividedDamage 7)
def onFourthPlanIndestructible : TriggeredAbility :=
  onNthPlanCounter 4 Effect.triggerPlanFinishIndestructibleOnTarget
def onEnterSurveil (n : Nat) : TriggeredAbility := mkTrigger .thisEnters (Effect.triggerSurveil n)
/-- Aura ETB trigger applying `action` to `ObjectExpr.attachedHost` (enchanted creature). -/
def onEnterEnchanted (action : ObjectExpr → Instruction) : TriggeredAbility :=
  mkTrigger .thisEnters { body := action .attachedHost }
/-- Equipment ETB trigger attaching this Equipment to target creature you control,
then applying `followup` to that creature if this Equipment is still on the battlefield. -/
def onEnterAttachThen (followup : ObjectExpr → Instruction) : TriggeredAbility :=
  mkTrigger .thisEnters {
    targets := .creatureYouControl
    body := .seq #[
      .permanent (.attach .this (.target 0)),
      Instruction.ifThen (.exists .this) (followup (.target 0))
    ]
  }
def onEnterExileOtherCopyEnchanted : TriggeredAbility :=
  mkTrigger .thisEnters Effect.triggerExileOtherCopyEnchanted
def onEnterExileCreatureReturnEndStep : TriggeredAbility :=
  mkTrigger .thisEnters Effect.triggerExileUntilNextEndStep
def onEnterTapOrUntapNonland : TriggeredAbility :=
  mkTrigger .thisEnters Effect.triggerTapOrUntapNonland
def onEnterCreateFoodOrTreasure : TriggeredAbility :=
  mkTrigger .thisEnters Effect.triggerCreateFoodOrTreasure
def onEnterVillainIfGyElseMill : TriggeredAbility :=
  mkTrigger .thisEnters Effect.triggerVillainIfGyElseMill
def onEnterDrawMayPutLandTapped : TriggeredAbility :=
  mkTrigger .thisEnters Effect.triggerDrawMayPutLandTapped
def onEnterDrawGainLifeIfAnotherHero : TriggeredAbility :=
  mkTrigger .thisEnters Effect.triggerDrawGainLifeIfAnotherHero
def onEnterPlusOneOrTwoIfAnotherHero : TriggeredAbility :=
  mkTrigger .thisEnters Effect.triggerPlusOneOrTwoIfAnotherHero
def onEnterMaySacArtifactOrDiscardDraw : TriggeredAbility :=
  mkTrigger .thisEnters Effect.triggerMaySacArtifactOrDiscardDraw

/-! ### Additional Reality Fracture & MSH named triggered-ability constructors -/

def onEnterEmpowerJace (n : Nat) : TriggeredAbility :=
  mkTrigger .thisEnters (Effect.triggerEmpowerJace n)
def onLandYouControlEntersEmpowerJace (n : Nat) : TriggeredAbility :=
  mkTrigger .landYouControlEnters (Effect.triggerEmpowerJace n)
def onCastFirstNoncreatureEmpowerJace (n : Nat) : TriggeredAbility :=
  mkTrigger .youCastFirstNoncreature (Effect.triggerEmpowerJace n)
def onYourUpkeepPrepareSource : TriggeredAbility :=
  mkTrigger .stepYourUpkeep Effect.triggerPrepareSource (interveningIf? := some condSourceNotPrepared)
def onEachEndStepPrepareIfThreeDied : TriggeredAbility :=
  mkTrigger .stepEachEndStep Effect.triggerPrepareSource (interveningIf? := some (condCreaturesDiedThisTurn 3))
def onActivateLoyaltyDrawIfRemovedTwo : TriggeredAbility :=
  mkTrigger (.youActivateLoyaltyAbility 2) Effect.triggerDrawIfRemovedTwoLoyalty
def onGainLifePlusOneEachSubtype (sub : CardSubtype) : TriggeredAbility :=
  mkTrigger (.gainLife .you) (Effect.triggerPlusOneEachSubtypeYouControl sub)
def onGainLifeLoyaltyOnSource : TriggeredAbility :=
  mkTrigger (.gainLife .you) Effect.triggerLoyaltyOnSource
def onEnterGrantThenCounterByType (k : Array KeywordAbility) : TriggeredAbility :=
  mkTrigger .thisEnters (Effect.triggerGrantThenCounterByType k)
def onEnterDestroyOppPermanentIfSixLands : TriggeredAbility :=
  mkTrigger .thisEnters Effect.triggerDestroyOppPermanentIfSixLands
    (interveningIf? := some (condControlLandsAtLeast 6))
def onYourBeginCombatPumpOrCounterIfScried : TriggeredAbility :=
  mkTrigger .stepYourBeginCombat Effect.triggerPumpOrCounterIfScried
def onEachEndStepSacrificeIfNoPlaneswalker : TriggeredAbility :=
  mkTrigger .stepEachEndStep Effect.triggerSacrificeSource (interveningIf? := some condControlNoPlaneswalker)
def onCastNoncreatureCreaturesGet (power toughness : Int) : TriggeredAbility :=
  mkTrigger .youCastNoncreature (Effect.triggerCreaturesYouControlGet power toughness)
def onDiesPutSourceCountersOnTarget : TriggeredAbility :=
  mkTrigger .thisDies Effect.triggerPutSourceCountersOnTarget
def onCreatureYouControlDiesChargeCounter : TriggeredAbility :=
  mkTrigger .creatureYouControlDies Effect.triggerChargeCounterOnSource
def onYourFirstMainAddGreenPerCharge : TriggeredAbility :=
  mkTrigger .stepYourFirstMain Effect.triggerAddGreenPerChargeCounter
def onScryOrSurveilMayPayDraw (n : Nat) : TriggeredAbility :=
  mkTrigger .youScryOrSurveil (Effect.triggerMayPayGenericDraw n (plusOneOnSource := true))
def onScryOrSurveilCreaturesGetOnce (power toughness : Int) : TriggeredAbility :=
  mkTrigger .youScryOrSurveil (Effect.triggerCreaturesYouControlGet power toughness) (limit := .onceEachTurn)
def onOpponentsDealtCombatDamageDrawTwoWin : TriggeredAbility :=
  mkTrigger .opponentsDealtCombatDamageYourTurn Effect.triggerDrawTwoWinIfEmptyShuffleSource (word := .when) (grouping := .oncePerBatch)
def onForestYouControlEntersPumpIfFiveOther : TriggeredAbility :=
  mkTrigger .forestYouControlEnters Effect.triggerPumpIfFiveOtherForests
    (interveningIf? := some condFiveOtherForests)
def onYourEndStepSurveilReturnIfGainedLife : TriggeredAbility :=
  mkTrigger .stepYourEndStep Effect.triggerSurveilReturnIfGainedLife (interveningIf? := some (condGainedLifeAtLeast 1))

/-! ### Unified triggered abilities -/

def onEnter (e : Effect) : TriggeredAbility := mkTrigger .thisEnters e

def stepEnchantedControllerDraws : TriggeredAbility :=
  mkTrigger .stepEnchantedControllerUpkeep Effect.stepEnchantedControllerDraws
def stepDrawToTen : TriggeredAbility :=
  mkTrigger .stepYourEndStep Effect.stepDrawToTen (interveningIf? := some (condHandSizeLessThan 10))
def stepCopyAbsorbingMan : TriggeredAbility :=
  mkTrigger .stepYourFirstMain Effect.stepCopyAbsorbingMan
def stepHydeChoose : TriggeredAbility :=
  mkTrigger .stepYourUpkeep Effect.stepHydeChoose
def stepCopyTaskmaster : TriggeredAbility :=
  mkTrigger .stepYourFirstMain Effect.stepCopyTaskmaster
def stepHarnessedFlicker : TriggeredAbility :=
  mkTrigger (.whenCond .stepYourEndStep condSourceHarnessed) Effect.stepHarnessedFlicker

def deathHellcatReturn : TriggeredAbility :=
  mkTrigger .thisDies Effect.deathHellcatReturn
def deathVillainReturnAsHero : TriggeredAbility :=
  mkTrigger .villainYouControlDies Effect.deathVillainReturnAsHero
def deathAttackingReturnHand : TriggeredAbility :=
  mkTrigger .attackingCreatureYouControlDies Effect.deathAttackingReturnHand
def deathDeathtouchOppSac : TriggeredAbility :=
  mkTrigger (TriggerPattern.permanentDies (.all #[
      .otherThan .this, .hasType .creature, .controlledBy .you, .hasKeyword .deathtouch])) Effect.deathDeathtouchOppSac

def thisAttackMayPayPlusOne : TriggeredAbility :=
  mkTrigger .thisAttacks Effect.thisAttackMayPayPlusOne
def thisAttackPayReturnAttacking : TriggeredAbility :=
  mkTrigger .thisAttacks Effect.thisAttackPayReturnAttacking
def thisAttackIfArtifactEnteredDraw : TriggeredAbility :=
  mkTrigger .thisAttacks Effect.thisAttackIfArtifactEnteredDraw (interveningIf? := some condArtifactEnteredThisTurn)
def thisAttackBlinkNontoken : TriggeredAbility :=
  mkTrigger .thisAttacks Effect.thisAttackBlinkNontoken
def thisAttackEquippedDrain : TriggeredAbility :=
  mkTrigger .thisAttacks Effect.thisAttackEquippedDrain (interveningIf? := some condSourceIsEquipped)
def thisAttackDrawIfPower4 : TriggeredAbility :=
  mkTrigger .thisAttacks Effect.thisAttackDrawIfPower4
def thisAttackAttacksAlonePlus2Indestructible : TriggeredAbility :=
  mkTrigger .thisAttacksAlone Effect.thisAttackAttacksAlonePlus2Indestructible

def enterOrAttackCopyKeywords : TriggeredAbility :=
  mkTrigger .enterOrAttack Effect.enterOrAttackCopyKeywords
def enterOrAttackCreateSquirrel : TriggeredAbility :=
  mkTrigger .enterOrAttack Effect.enterOrAttackCreateSquirrel

def watchCombatDamageExileUntilNonland : TriggeredAbility :=
  mkTrigger .thisDealsCombatDamageToPlayer Effect.watchCombatDamageExileUntilNonland
def watchAttacksAloneDrain : TriggeredAbility :=
  mkTrigger .creatureYouControlAttacksAlone Effect.watchAttacksAloneDrain
def watchAttacksAloneFirstStrikeMenace : TriggeredAbility :=
  mkTrigger .creatureYouControlAttacksAlone Effect.watchAttacksAloneFirstStrikeMenace
def watchFirstTapUntap : TriggeredAbility :=
  mkTrigger .creatureYouControlFirstTappedYourTurn Effect.watchFirstTapUntap
def watchSheHulkRedirectOnce : TriggeredAbility :=
  mkTrigger .creatureYouControlDealtDamage Effect.watchSheHulkRedirectOnce (grouping := .perSourceInBatch) (limit := .optionalOnceEachTurn)
def watchSpeedballTargeted : TriggeredAbility :=
  mkTrigger .spellTargetsThis Effect.watchSpeedballTargeted
def watchAnyPlayerSecondDraw : TriggeredAbility :=
  mkTrigger (.drawCard .any) Effect.watchAnyPlayerSecondDraw (limit := .nthEachTurn 2)
def watchYouTargetDrawOnce : TriggeredAbility :=
  mkTrigger .youTargetPlayerOrPermanentWithAbility Effect.watchYouTargetDrawOnce (limit := .onceEachTurn)
def watchVillainOrArtifactDamage : TriggeredAbility :=
  mkTrigger .anotherVillainOrArtifactYouControlEnters Effect.watchVillainOrArtifactDamage
def watchVillainConniveOnce : TriggeredAbility :=
  mkTrigger (.anotherSubtypeYouControlEnters .villain) Effect.watchVillainConniveOnce (limit := .optionalOnceEachTurn)
def watchVillainPlusOneDamageOnce : TriggeredAbility :=
  mkTrigger (.anotherSubtypeYouControlEnters .villain) Effect.watchVillainPlusOneDamageOnce (limit := .onceEachTurn)
def watchVillainAttachEquipment : TriggeredAbility :=
  mkTrigger (.anotherSubtypeYouControlEnters .villain) Effect.watchVillainAttachEquipment
def watchVillainPlusOneLifelink : TriggeredAbility :=
  mkTrigger (.anotherSubtypeYouControlEnters .villain) Effect.watchVillainPlusOneLifelink
def watchHulklingCompare : TriggeredAbility :=
  mkTrigger .anotherCreatureYouControlEnters Effect.watchHulklingCompare (interveningIf? := some condTriggerSubjectGreaterPT)
def watchJusticeBounce : TriggeredAbility :=
  mkTrigger .anotherNonlandYouControlReturnedToHand Effect.watchJusticeBounce
def watchNontokenHeroModal : TriggeredAbility :=
  mkTrigger (.anotherNontokenSubtypeYouControlEnters .hero) Effect.watchNontokenHeroModal
def watchUltronCopy : TriggeredAbility :=
  mkTrigger .anotherNontokenArtifactYouControlEnters Effect.watchUltronCopy
def watchEnchantedAttachEquipment : TriggeredAbility :=
  mkTrigger .enchantedAttacksOrBlocks Effect.watchEnchantedAttachEquipment
def watchEquippedAttacksAloneUntapScry : TriggeredAbility :=
  mkTrigger .equippedAttacksAlone Effect.watchEquippedAttacksAloneUntapScry
def watchEquippedAttacksTap : TriggeredAbility :=
  mkTrigger .equippedAttacks Effect.watchEquippedAttacksTap
def watchEquippedTappedDamage : TriggeredAbility :=
  mkTrigger .equippedBecomesTapped Effect.watchEquippedTappedDamage
def watchHeroesDamagePlusTwo : TriggeredAbility :=
  mkTrigger .heroesYouControlDealDamageToPlayer Effect.watchHeroesDamagePlusTwo (grouping := .oncePerBatch)
def watchMerfolkAttackDraw : TriggeredAbility :=
  mkTrigger .merfolkYouControlAttackPlayer Effect.watchMerfolkAttackDraw (grouping := .perPlayerInBatch)
def watchTokensEnterMayDraw : TriggeredAbility :=
  mkTrigger .tokenYouControlEnters Effect.watchTokensEnterMayDraw (grouping := .oncePerBatch)
def watchHawkeyeModes : TriggeredAbility :=
  mkTrigger .thisBecomesTapped Effect.watchHawkeyeModes
def watchRedHulk : TriggeredAbility :=
  mkTrigger .thisDealtDamage Effect.watchRedHulk (grouping := .oncePerBatch)
def watchHulk : TriggeredAbility :=
  mkTrigger .thisDealtDamage Effect.watchHulk (grouping := .oncePerBatch)

def youAttackingPay2LifeToughness : TriggeredAbility :=
  mkTrigger .youAttack Effect.youAttackingPay2LifeToughness (grouping := .oncePerBatch)
def youAttackingExileTopHeroPump : TriggeredAbility :=
  mkTrigger .youAttack Effect.youAttackingExileTopHeroPump (grouping := .oncePerBatch)
def youAttackingLookSixCast : TriggeredAbility :=
  mkTrigger .youAttack Effect.youAttackingLookSixCast (grouping := .oncePerBatch)

def castingVillainToken : TriggeredAbility :=
  mkTrigger (.youCastSubtype .villain) Effect.castingVillainToken
def castingMerfolkFromBlue : TriggeredAbility :=
  mkTrigger .youCastNoncreature Effect.castingMerfolkFromBlue
def castingMayPayHasteUnblockable : TriggeredAbility :=
  mkTrigger .youCastNoncreature Effect.castingMayPayHasteUnblockable
def castingPlusOneEachOther : TriggeredAbility :=
  mkTrigger .youCastNoncreature Effect.castingPlusOneEachOther
def castingExileFlicker : TriggeredAbility :=
  mkTrigger .youCastNoncreature Effect.castingExileFlicker
def castingVisionModes : TriggeredAbility :=
  mkTrigger .youCastNoncreature Effect.castingVisionModes
def castingDamageEqualMv : TriggeredAbility :=
  mkTrigger .youCastNoncreature Effect.castingDamageEqualMv
def castingDrawPowerEqualHand : TriggeredAbility :=
  mkTrigger .youCastTargetingCreatureYouControl Effect.castingDrawPowerEqualHand
def castingPlusOneThis : TriggeredAbility :=
  mkTrigger .youCastTargetingCreatureYouControl Effect.castingPlusOneThis
def castingPlusOneScry : TriggeredAbility :=
  mkTrigger .youCastTargetingCreatureYouControl Effect.castingPlusOneScry
def castingIronFistTap : TriggeredAbility :=
  mkTrigger .youCastTargetingCreatureYouControl Effect.castingIronFistTap
def castingTargetsGainFlying : TriggeredAbility :=
  mkTrigger .youCastTargetingCreature Effect.castingTargetsGainFlying
def castingCopyIfArtifactOrLand : TriggeredAbility :=
  mkTrigger .youCastInstantSorceryTargetingArtifactOrLand Effect.castingCopyIfArtifactOrLand
def castingTapCreatureOrLand : TriggeredAbility :=
  mkTrigger .youCastNoncreature Effect.castingTapCreatureOrLand

def resourceDiscardExilePlay : TriggeredAbility :=
  mkTrigger (.discard .you) Effect.resourceDiscardExilePlay
def resourceDrawIfAnotherHeroDamage : TriggeredAbility :=
  mkTrigger (.drawCard .you) Effect.resourceDrawIfAnotherHeroDamage (interveningIf? := some (condControlAnotherSubtype .hero))
def resourceSecondDrawBecome66 : TriggeredAbility :=
  mkTrigger (.drawCard .you) Effect.resourceSecondDrawBecome66 (limit := .nthEachTurn 2)
def resourceSecondDrawPlusOneTarget : TriggeredAbility :=
  mkTrigger (.drawCard .you) Effect.resourceSecondDrawPlusOneTarget (limit := .nthEachTurn 2)
def resourceSecondDrawDrain : TriggeredAbility :=
  mkTrigger (.drawCard .you) Effect.resourceSecondDrawDrain (limit := .nthEachTurn 2)
def resourceGainLifePlusOnes : TriggeredAbility :=
  mkTrigger (.gainLife .you) Effect.resourceGainLifePlusOnes
def resourcePlusOneCreateInsectOnce : TriggeredAbility :=
  mkTrigger .youPutPlusOneOnCreature Effect.resourcePlusOneCreateInsectOnce (grouping := .oncePerBatch) (limit := .onceEachTurn)
def resourcePlusOneOnThisOnce : TriggeredAbility :=
  mkTrigger .youPutPlusOneOnOtherCreature Effect.resourcePlusOneOnThisOnce (grouping := .oncePerBatch) (limit := .onceEachTurn)
def resourcePlusOneOnHeroesCreateWall : TriggeredAbility :=
  mkTrigger .youPutPlusOneOnOtherHeroYouControl Effect.resourcePlusOneOnHeroesCreateWall (grouping := .oncePerBatch)

private def lookupTriggerByEffect (cands : Array TriggeredAbility) (fallback : TriggerPattern)
    (e : Effect) (grouping : BatchGrouping := .perOccurrence) : TriggeredAbility :=
  (cands.find? fun ab => ab.effect == e).getD
    (mkTrigger fallback e (grouping := grouping))

def onStep (e : Effect) : TriggeredAbility :=
  lookupTriggerByEffect #[
    stepEnchantedControllerDraws, stepDrawToTen, stepCopyAbsorbingMan,
    stepHydeChoose, stepCopyTaskmaster, stepHarnessedFlicker
  ] .stepYourUpkeep e

def onDeath (e : Effect) : TriggeredAbility :=
  lookupTriggerByEffect #[
    deathHellcatReturn, deathVillainReturnAsHero,
    deathAttackingReturnHand, deathDeathtouchOppSac
  ] .thisDies e

def onThisAttack (e : Effect) : TriggeredAbility :=
  lookupTriggerByEffect #[
    thisAttackMayPayPlusOne, thisAttackPayReturnAttacking,
    thisAttackIfArtifactEnteredDraw, thisAttackBlinkNontoken,
    thisAttackEquippedDrain, thisAttackDrawIfPower4,
    thisAttackAttacksAlonePlus2Indestructible
  ] .thisAttacks e

def onEnterOrAttack (e : Effect) : TriggeredAbility :=
  lookupTriggerByEffect #[
    enterOrAttackCopyKeywords, enterOrAttackCreateSquirrel
  ] .enterOrAttack e

def onYouAttacking (e : Effect) : TriggeredAbility :=
  lookupTriggerByEffect #[
    youAttackingPay2LifeToughness, youAttackingExileTopHeroPump,
    youAttackingLookSixCast
  ] .youAttack e (grouping := .oncePerBatch)

def onWatch (e : Effect) : TriggeredAbility :=
  lookupTriggerByEffect #[
    watchCombatDamageExileUntilNonland, watchAttacksAloneDrain,
    watchAttacksAloneFirstStrikeMenace, watchFirstTapUntap,
    watchSheHulkRedirectOnce, watchSpeedballTargeted,
    watchAnyPlayerSecondDraw, watchYouTargetDrawOnce,
    watchVillainOrArtifactDamage, watchVillainConniveOnce,
    watchVillainPlusOneDamageOnce, watchVillainAttachEquipment,
    watchVillainPlusOneLifelink, watchHulklingCompare,
    watchJusticeBounce, watchNontokenHeroModal, watchUltronCopy,
    watchEnchantedAttachEquipment, watchEquippedAttacksAloneUntapScry,
    watchEquippedAttacksTap, watchEquippedTappedDamage,
    watchHeroesDamagePlusTwo, watchMerfolkAttackDraw,
    watchTokensEnterMayDraw, watchHawkeyeModes, watchRedHulk, watchHulk
  ] .thisBecomesTapped e

def onCasting (e : Effect) : TriggeredAbility :=
  lookupTriggerByEffect #[
    castingVillainToken, castingMerfolkFromBlue,
    castingMayPayHasteUnblockable, castingPlusOneEachOther,
    castingExileFlicker, castingVisionModes, castingDamageEqualMv,
    castingDrawPowerEqualHand, castingPlusOneThis, castingPlusOneScry,
    castingIronFistTap, castingTargetsGainFlying,
    castingCopyIfArtifactOrLand, castingTapCreatureOrLand
  ] .youCastNoncreature e

def onResource (e : Effect) : TriggeredAbility :=
  lookupTriggerByEffect #[
    resourceDiscardExilePlay, resourceDrawIfAnotherHeroDamage,
    resourceSecondDrawBecome66, resourceSecondDrawPlusOneTarget,
    resourceSecondDrawDrain, resourceGainLifePlusOnes,
    resourcePlusOneCreateInsectOnce, resourcePlusOneOnThisOnce,
    resourcePlusOneOnHeroesCreateWall
  ] (.drawCard .you) e

instance : HasTargeting TriggeredAbility where
  targetSpec ab := ab.effect.targets

/-! ### Oracle Rendering -/

/-- Leading `"When / Whenever / At …"` prefix rendered from `word`, `pattern`,
`grouping`, and `limit`. -/
private def eventPrefixPattern (word : TriggerWord) (grouping : BatchGrouping)
    (limit : TriggerLimit) : TriggerPattern → String
  | .or (.zoneChange (.sameAs .this) (.notIn .battlefield) (.inZones { zones := #[.battlefield], .. }) none none)
        (.attacks (.sameAs .this) .any false 1 none false) =>
    "Whenever this creature enters or attacks"
  | .or (.castSpell { relation := .you, pred := .any } (.hasColor (.literal .green)) none none false none none)
        (.zoneChange (.all #[.hasSubtype (.literal .forest), .controlledBy { relation := .you, pred := .any }])
          (.notIn .battlefield) (.inZones { zones := #[.battlefield], .. }) none none) =>
    "Whenever you cast a green spell and whenever a Forest you control enters"
  | .zoneChange (.any #[.sameAs .this, .all #[.hasSubtype (.literal s), .controlledBy _]])
      (.notIn .battlefield) (.inZones { zones := #[.battlefield], .. }) none none =>
    s!"Whenever this or another {s} you control enters"
  | .zoneChange (.any #[.sameAs .this, .all #[.isToken false, .hasSubtype (.literal s), .controlledBy _]])
      (.notIn .battlefield) (.inZones { zones := #[.battlefield], .. }) none none =>
    s!"Whenever this or another nontoken {s} you control enters"
  | .zoneChange (.all #[.otherThan .this, .controlledBy _,
      .any #[.hasSubtype (.literal s), .all #[.hasType .artifact, .hasSubtype (.literal .equipment)]]])
      (.notIn .battlefield) (.inZones { zones := #[.battlefield], .. }) none none =>
    s!"Whenever another {s} or Equipment you control enters"
  | .zoneChange (.all #[.otherThan .this, .hasType .creature, .controlledBy _, .stat .power .le (.const n)])
      (.notIn .battlefield) (.inZones { zones := #[.battlefield], .. }) none none =>
    s!"Whenever another creature you control with power {n} or less enters"
  | .zoneChange (.all #[.otherThan .this, .hasSubtype (.literal s), .controlledBy _])
      (.notIn .battlefield) (.inZones { zones := #[.battlefield], .. }) none none =>
    s!"Whenever another {s} you control enters"
  | .whenCond inner (.exists (.inZones .battlefield (.all #[.hasType .creature, .controlledBy _, .stat .power .ge (.const n)]))) =>
    let base := eventPrefixPattern word grouping limit inner
    s!"{base} while you control a creature with power {n} or greater"
  | p =>
    let ctx : PrintCtx :=
      match p with
      | .attacks (.sameAs .this) .. | .blocks (.sameAs .this) | .becomesBlocked (.sameAs .this)
      | .zoneChange (.sameAs .this) (.inZones { zones := #[.battlefield], .. }) (.inZones { zones := #[.graveyard], .. }) _ _
      | .zoneChange (.sameAs .this) (.inZones { zones := #[.battlefield], .. }) (.notIn .battlefield) _ _ =>
        { selfRef := "this creature", capitalize := false }
      | .damageDealt (.sameAs .this) .. | .damageDealt _ (.object { pred := .sameAs .this, .. }) ..
      | .becomesTapped (.sameAs .this) .. =>
        { selfRef := "this", capitalize := false }
      | .becomesTarget (.object (.sameAs .this)) .. =>
        { selfRef := "this creature", capitalize := false }
      | _ => { selfRef := "this permanent", capitalize := false }
    let w := word.toOracleStr
    s!"{w} {p.renderClause ctx grouping limit}"

/-- Leading `"When / Whenever / At …"` prefix rendered from `ab.word`,
`ab.pattern`, `ab.grouping`, and `ab.limit`. -/
def eventPrefix (ab : TriggeredAbility) : String :=
  eventPrefixPattern ab.word ab.grouping ab.limit ab.pattern

/-- Intervening `"if …"` clause rendered from `ab.interveningIf?`, or empty. -/
def interveningClause (ab : TriggeredAbility) : String :=
  match ab.interveningIf? with
  | none => ""
  | some cond =>
    match cond with
    | .exists (.inZones .battlefield (.all #[.hasType .creature, .controlledBy _, .stat .power .ge (.const n)])) =>
      s!" while you control a creature with power {n} or greater"
    | .cmp .ge (.playerMetric .lifeGainedThisTurn .you) (.const n) =>
      s!", if you gained {n} or more life this turn"
    | .cmp .ge (.aggregate .count .one (.inZones .battlefield (.all #[
        .hasType .land, .controlledBy _]))) (.const 6) =>
      ", if you control six or more lands"
    | .cmp .ge (.aggregate .count .one (.inZones .battlefield (.all #[
        .otherThan .triggerSubject, .hasSubtype (.literal .forest), .controlledBy _]))) (.const 5) =>
      ", if you control at least five other Forests"
    | .any #[
        .turnHistory (.eventOccurredThisTurn _ (.attackedWith (.hasSubtype (.literal sub)) 1)),
        .turnHistory (.eventOccurredThisTurn _ (.permanentEntered (.hasSubtype (.literal _))))] =>
      let a := if sub == .hero then "a Hero" else s!"a {sub}"
      s!", if you attacked with {a} this turn or {a} entered the battlefield under your control this turn"
    | _ =>
      s!", if {ToOracle.toOracle { selfRef := "this permanent", capitalize := false } cond}"

/-- Oracle clause for putting `n` counters of `kind` on `noun`. -/
def counterOn (noun : String) (kind : CounterKind) (n : Nat) : String :=
  match kind with
  | .plusOnePlusOne => s!"put {plusOnePlusOneCountersPhrase n} on {noun}"
  | .indestructible | .doubleStrike | .burden | .stun | .trample
  | .hone | .plan | .loyalty | .charge | .quest | .influence | .invasion =>
    s!"put {kind.countersPhrase n} on {noun}"
  | _ => "put counters"

private def instrObjNoun (noun : String) : ObjectExpr → String
  | .this => "this creature"
  | .attachedHost => "enchanted creature"
  | .triggerSubject => "that creature"
  | .target 0 => if noun.isEmpty then "that creature" else noun
  | _ => if noun.isEmpty then "that creature" else noun

private def extractSubtypesFromPred : ObjectPred → Option (Array CardSubtype)
  | .hasSubtype (.literal s) => some #[s]
  | .any ps =>
    let ss := ps.filterMap fun | .hasSubtype (.literal s) => some s | _ => none
    if ss.size == ps.size && !ss.isEmpty then some ss else none
  | _ => none

private def extractTypesFromInspectPred : ObjectPred → Option (Array String)
  | .hasType ty => some #[capitalizeAscii ty.oracleWord]
  | .hasSubtype (.literal s) => some #[s.englishName]
  | .isKind .permanentCard => some #["permanent"]
  | .any ps =>
    let xs := ps.filterMap fun
      | .hasType ty => some (capitalizeAscii ty.oracleWord)
      | .hasSubtype (.literal s) => some s.englishName
      | .isKind .permanentCard => some "permanent"
      | _ => none
    if xs.size == ps.size && !xs.isEmpty then some xs else none
  | _ => none

/-- Printed clause for a unified `Instruction` triggered-ability effect. -/
private def withUpToOne (noun : String) : String :=
  if noun.startsWith "up to " then noun else s!"up to one {noun}"

private partial def instrTriggerPhrase (e : Effect) (body : Instruction) (noun : String) : String :=
  match body with
  | .seq #[.permanent (.attach .this (.target 0) _), .ifCond (.exists .this) inner .noop] =>
    s!"attach it to {noun}. {capitalizeAscii (instrTriggerPhrase e inner "that creature")}"
  | .bind ⟨0⟩ (.create (.tokens .you (.const 1) kind _)) (.permanent (.attach .this (.stepObjects ⟨0⟩) _)) =>
    s!"{TokenSpec.createPhrase kind 1}, then attach this Equipment to it"
  | .bind ⟨0⟩ (.create (.tokens .you (.const 1) kind _)) (.permanent (.attach (.stepObjects ⟨0⟩) .this _)) =>
    if kind == .sturdyShield then
      "create a colorless Equipment artifact token named Sturdy Shield with \"Equipped creature gets +1/+2\" and equip {2}. Attach it to this creature"
    else
      s!"{TokenSpec.createPhrase kind 1}. Attach it to this creature"
  | .bind ⟨0⟩ (.player (.amass .you subtype (.const n))) (.permanent (.attach .this (.stepObjects ⟨0⟩) _)) =>
    s!"amass {pluralizeName subtype} {n.toNat}, then attach this Equipment to the amassed Army"
  | .create (.tokens .you (.const n) kind mods) =>
    if kind == .clue && n == 1 && !mods.tapped then "investigate"
    else if kind == .axe && n == 1 && !mods.tapped then
      "create a colorless Equipment artifact token named Axe with \"Equipped creature gets +1/+0\" and equip {2}"
    else if kind == .zabu && n == 1 && !mods.tapped then
      "create Zabu, a legendary 2/2 green Cat creature token with \"Landfall — Whenever a land you control enters, put a +1/+1 counter on Zabu.\""
    else if kind == .redwing && n == 1 && !mods.tapped then
      "create Redwing, a legendary 1/1 blue Bird Scout creature token with flying and \"Whenever Redwing attacks, surveil 1.\""
    else TokenSpec.createPhrase kind n.toNat (tapped := mods.tapped)
  | .create (.tokens (.target 0) (.const 1) kind _) =>
    if kind == .theVoid then
      s!"{noun} creates The Void, a legendary 5/5 black Horror Villain creature token with flying, indestructible, and \"The Void attacks each combat if able.\""
    else s!"{noun} creates {kind.oracleNoun}"
  | .create (.tokens .you (.aggregate .count .one (.inZones .battlefield (.all #[.hasType .artifact, .controlledBy .opponent]))) .treasure mods) =>
    if mods.tapped then "create X tapped Treasure tokens, where X is the number of artifacts your opponents control"
    else "create a Treasure token for each artifact your opponents control"
  | .bind ⟨0⟩ (.player (.choose .you .creatureType))
      (.create (.tokens .you (.aggregate .count .one (.inZones .battlefield (.all #[.hasType .creature, .hasSubtype (.fromStep ⟨0⟩), .controlledBy .you]))) .treasure _)) =>
    "choose a creature type. Create a Treasure token for each creature you control of that type"
  | .create (.tokens .you (.aggregate .count .one (.inZones .battlefield (.all #[.hasType .creature, .hasSubtype .chosenOnSource, .controlledBy .you]))) .treasure _) =>
    "create a Treasure token for each creature you control of the chosen type"
  | .create (.tokens .you .eventAmount .birdSoldier _) =>
    "create X 1/1 white Bird Soldier creature tokens with flying"
  | .create (.tokens .you .eventAmount .treasure _) =>
    "create that many Treasure tokens"
  | .player (.scry .you (.const n)) => s!"scry {n.toNat}"
  | .player (.surveil .you (.const n)) => s!"surveil {n.toNat}"
  | .player (.empowerPlaneswalker .jace (.const n)) => s!"empower Jace {n.toNat}"
  | .player (.drawCards .you (.const n)) => s!"draw {cardPhrase n.toNat}"
  | .player (.drawCards .you (.playerMetric .one (.matching .anyPlayer (.metric .graveyardSize .ge (.const 7))))) =>
    "draw a card for each graveyard with seven or more cards in it"
  | .player (.amass .you subtype (.const n)) =>
    s!"amass {pluralizeName subtype} {n.toNat}"
  | .player (.amass .you subtype (.objectStat .power .this)) =>
    s!"amass {pluralizeName subtype} X, where X is this creature's power"
  | .player (.connive .this) => "it connives"
  | .player (.connive (.target 0)) => s!"{noun} connives"
  | .player (.temptWithRing .you) => "the Ring tempts you"
  | .player (.addMana .you mp) =>
    let manaSym : ManaType → String
      | .colored c => s!"\{{c.letter}}"
      | .colorless => "{C}"
    let syms :=
      match mp.spec with
      | .sequence pairs =>
        String.join (pairs.toList.map fun (p : ManaType × ValueExpr) =>
          String.join (List.replicate (p.2.evalConst?.getD 1).toNat (manaSym p.1)))
      | _ => ""
    if syms.isEmpty then mp.toOracleSentence {} else s!"add {syms}"
  | .player (.searchLibrary spec) =>
    if spec.filter == .hasSubtype (.literal .forest) then
      "search your library for a Forest card, put that card onto the battlefield, then shuffle"
    else if spec.filter == .all #[.hasSupertype .basic, .hasType .land] &&
        spec.dest == .hand .controller &&
        spec.count == .upTo (.const 1) &&
        spec.groupConstraint?.isNone then
      searchLibraryToHandPhrase "a basic land card"
    else
      Instruction.toOracleWith { capitalize := false } e.targets body
  | .player (.inspectLibrary spec) =>
    match spec.source, spec.action with
    | .topCards .you (.const n) false, .takeMatching pred (.upTo (.const 1)) (.hand .controller) _ true _ =>
      match extractTypesFromInspectPred pred with
      | some ts =>
        let joined :=
          match ts.toList with
          | [a, b] => s!"a {a} or {b} card"
          | xs => s!"a {String.intercalate " or " xs} card"
        s!"look at the top {n.toNat} cards of your library. You may reveal {joined} from among them and put it into your hand. {restOnBottomRandomPhrase}"
      | none => "look at the top cards of your library"
    | .topCards .you (.const n) true, .takeMatching (.hasType .creature) (.exact (.const 1)) (.battlefield .controller) _ false true =>
      s!"reveal the top {n.toNat} cards of your library. Put a random creature card from among them onto the battlefield. {restOnBottomRandomPhrase}"
    | .millCards .you (.const n), .takeMatching (.hasSubtype (.literal sub)) .anyNumber (.hand .controller) _ _ _ =>
      s!"mill {n.toNat} cards, then put all {sub} cards from among them into your hand"
    | _, _ => Instruction.toOracleWith { capitalize := false } e.targets body
  | .player (.reveal (.target 0) _ (some _)) =>
    s!"{noun} reveals a number of cards from their hand equal to one plus the number of creature cards in your graveyard. You choose one of them. That player discards that card"
  | .seq #[.player (.reveal (.target 0) _ none), .ifCond (.exists .this) (.moveZone (.target 1) .exile .exile _) .noop] =>
    "choose target opponent and up to one target creature they control. They reveal their hand. You may exile a nonland card from their hand or the chosen creature until this leaves the battlefield"
  | .seq #[.player (.drawCards .you (.const 1)),
           .bind ⟨0⟩ (.moveZone (.inZones _ .anyObject) .graveyard .discard _)
             (.ifCond (.exists (.filter (.stepObjects ⟨0⟩) (.not (.hasType .land))))
               (.create (.tokens .you (.const 1) .humanSoldier _)) .noop)] =>
    "recruit"
  | .damage (.deal .this .allTargets (.const _) fl) =>
    if fl.divided then
      match e.dividedDamage? with
      | some (amount, maxTargets) =>
        s!"it deals {amount} damage divided as you choose among {dividedAmong maxTargets}"
      | none => "it deals damage divided as you choose"
    else
      Instruction.toOracleWith { capitalize := false } e.targets body
  | .damage (.deal .this (.players (.target 0)) (.const n) _) =>
    s!"this creature deals {n.toNat} damage to {noun}"
  | .damage (.deal .this (.players _) (.const n) _) =>
    s!"this creature deals {n.toNat} damage to each opponent"
  | .damage (.deal .this (.players _) (.aggregate .count .one (.inZones .battlefield (.all #[.hasSubtype (.literal sub), .controlledBy _]))) _) =>
    s!"it deals damage equal to the number of {pluralSubtype sub} you control to each opponent"
  | .damage (.deal .this (.targetSlot 0) (.aggregate .count .one (.inZones .battlefield (.all #[.hasSubtype (.literal .treasure), .controlledBy _]))) _) =>
    s!"it deals damage equal to the number of Treasures you control to {noun}"
  | .damage (.deal .this (.objects (.inZones .battlefield (.all #[.hasType .creature, .combatRole (.blockingObject .this)]))) (.const n) _) =>
    s!"it deals {n.toNat} damage to each creature blocking it"
  | .damage (.deal .this (.targetSlot 0) (.objectStat .power .this) _) =>
    s!"it deals damage equal to its power to {noun}"
  | .damage (.deal _ (.objects obj) (.const n) _) =>
    s!"deals {n.toNat} damage to {instrObjNoun noun obj}"
  | .damage (.deal _ (.targetSlot 0) (.const n) _) =>
    if e.allowsZeroTargets then s!"it deals {n.toNat} damage to {withUpToOne noun}"
    else s!"deals {n.toNat} damage to {noun}"
  | .damage (.fight .this (.target 0) false) =>
    s!"this fights {noun}"
  | .life (.gain .you (.const n)) => s!"you gain {n.toNat} life"
  | .life (.lose (.target 0) (.const n)) => s!"{noun} loses {n.toNat} life"
  | .permanent (.attach .this (.target 0) false) =>
    s!"attach it to {noun}"
  | .permanent (.attach (.target 0) (.target 1) false) =>
    "attach target Equipment you control to up to one target creature you control"
  | .permanent (.modifyCounters (.put kind (.const n)) obj _) =>
    match obj with
    | .inZones .battlefield (.all #[.hasType .creature, .controlledBy _]) =>
      "put a +1/+1 counter on each creature you control"
    | .inZones .battlefield (.all #[.hasSubtype (.literal .equipment), .controlledBy _]) =>
      if kind == .hone then "put a hone counter on each Equipment you control"
      else s!"put a {kind.oracleName} counter on each Equipment you control"
    | .inZones .battlefield (.all #[.hasSubtype (.literal s), .controlledBy _]) =>
      s!"put a +1/+1 counter on each {s} you control"
    | _ =>
      counterOn (instrObjNoun noun obj) kind n.toNat
  | .permanent (.modifyCounters (.put .plusOnePlusOne (.objectStat .manaValue .triggerSubject)) (.target 0) _) =>
    s!"put X +1/+1 counters on {noun}, where X is that spell's mana value"
  | .permanent (.modifyCounters (.copyFromLki .this) (.target 0) _) =>
    "put its counters on up to one target creature you control"
  | .permanent (.setTapped obj true _) =>
    s!"tap {instrObjNoun noun obj}"
  | .permanent (.setTapped obj false _) =>
    s!"untap {instrObjNoun noun obj}"
  | .permanent (.setDesignation obj .prepared true) =>
    s!"{instrObjNoun noun obj} becomes prepared"
  | .ifCond (.playerPred .you (.hasDesignation .citysBlessing))
      (.permanent (.modifyCounters (.put .plusOnePlusOne (.const 2)) _ _))
      (.permanent (.modifyCounters (.put .plusOnePlusOne (.const 1)) _ _)) =>
    "put a +1/+1 counter on each creature you control. If you have the city's blessing, put two +1/+1 counters on each creature you control instead"
  | .installEffect (.applyContinuous .untilEndOfTurn obj (.modifyPT (.const p) (.const t))) =>
    match obj with
    | .inZones .battlefield (.all #[.hasType .creature, .controlledBy _]) =>
      s!"creatures you control get {signedStat p}/{signedStat t} until end of turn"
    | _ =>
      s!"{instrObjNoun noun obj} gets {signedStat p}/{signedStat t} until end of turn"
  | .installEffect (.applyContinuous .untilEndOfTurn obj (.modifyPT (.objectStat .power _) (.objectStat .toughness _))) =>
    s!"double {instrObjNoun noun obj}'s power and toughness until end of turn"
  | .installEffect (.applyContinuous .untilEndOfTurn (.target 0) (.modifyPT (.objectStat .power .this) (.const 0))) =>
    s!"{noun} gets +X/+0 until end of turn, where X is this creature's power"
  | .installEffect (.applyContinuous .untilEndOfTurn (.target 0) (.modifyPT (.aggregate .count .one (.inZones .battlefield (.all #[.hasSubtype (.literal .plains), .controlledBy _]))) _)) =>
    "target creature you control gets +1/+1 until end of turn for each Plains you control"
  | .installEffect (.applyContinuous .untilEndOfTurn .this (.modifyPT .eventAmount .eventAmount)) =>
    "this creature gets +1/+1 until end of turn for each card looked at while scrying this way"
  | .installEffect (.applyContinuous .untilEndOfTurn .this (.modifyPT (.aggregate .max (.stat .power) _) (.const 0))) =>
    "it gets +X/+0 until end of turn, where X is the greatest power among creatures you control"
  | .installEffect (.applyContinuous .untilEndOfTurn .this (.modifyPT (.aggregate .count .one (.inZones .battlefield (.all #[.otherThan .this, .hasType .creature, .controlledBy _]))) _)) =>
    "it gets +1/+1 until end of turn for each other creature you control"
  | .installEffect (.applyContinuous .untilEndOfTurn (.inZones .battlefield (.all #[.otherThan .this, .hasSubtype (.literal sub), .controlledBy _])) (.modifyPT (.objectStat .toughness .this) (.objectStat .toughness .this))) =>
    s!"each other {sub} you control gets +X/+X until end of turn, where X is this toughness"
  | .installEffect (.applyContinuous .untilEndOfTurn .this (.all #[.modifyTypes { types := #[.creature], .. }, .setBasePT (some (.const p)) (some (.const t))])) =>
    s!"it becomes a {p}/{t} creature until end of turn"
  | .installEffect (.applyContinuous .untilEndOfTurn (.target 0) (.setBasePT (some (.objectStat .power .this)) (some (.objectStat .toughness .this)))) =>
    "choose up to one other target creature you control. Its base power and toughness become equal to this creature's power and toughness until end of turn"
  | .installEffect (.applyContinuous .untilEndOfTurn obj (.grantKeywords k)) =>
    s!"{instrObjNoun noun obj} gains {KeywordAbility.joinedAnd k} until end of turn"
  | .installEffect (.applyContinuous .untilEndOfTurn obj (.loseKeywords k)) =>
    if k == #[Keyword.indestructible] then
      s!"{instrObjNoun noun obj} loses indestructible until end of turn"
    else
      s!"{instrObjNoun noun obj} loses {KeywordAbility.joinedAnd k} until end of turn"
  | .installEffect (.applyContinuous .untilEndOfTurn obj (.setBasePT (some (.const p)) (some (.const t)))) =>
    s!"{instrObjNoun noun obj} has base power and toughness {p}/{t} until end of turn"
  | .installEffect (.applyContinuous .untilEndOfTurn obj (.applyRule (.combat (.cantBeBlocked .self)))) =>
    s!"{instrObjNoun noun obj} can't be blocked this turn"
  | .installEffect (.applyContinuous .untilEndOfTurn obj (.modifyTypes { types := #[.artifact], .. }))
  | .installEffect (.applyContinuous .untilEndOfTurn obj (.all #[.modifyTypes { types := #[.artifact], .. }])) =>
    s!"until end of turn, {instrObjNoun noun obj} becomes an artifact in addition to its other types"
  | .installEffect (.applyContinuous .untilEndOfTurn obj (.all #[.modifyTypes { types := #[.artifact], .. }, .grantKeywords k])) =>
    if k == #[Keyword.indestructible] then
      s!"until end of turn, {instrObjNoun noun obj} becomes an artifact in addition to its other types and gains indestructible"
    else
      s!"until end of turn, {instrObjNoun noun obj} becomes an artifact in addition to its other types"
  | .moveZone (.topOfLibrary (.target 0) (.const n)) .graveyard .mill _ =>
    s!"{noun} mills {n.toNat} cards"
  | .moveZone (.topOfLibrary (.triggerPlayer .actor) .eventAmount) .graveyard .mill _ =>
    "that player mills that many cards"
  | .moveZone (.topOfLibrary .you (.const 1)) .exile .exile { grantPlayPerm? := some _, .. } =>
    s!"exile the top card of your library. {playThatCardUntilNextTurnPhrase}"
  | .moveZone (.target 0) .exile .exile { grantPlayPerm? := some _, .. } =>
    s!"exile {noun}. {playThatCardUntilNextTurnPhrase}"
  | .moveZone (.target 0) .exile .exile { exileUntilSourceLeaves := true, .. } =>
    if e.allowsZeroTargets then
      if e.targets == TargetSpec.defendingPlayerCreature then
        s!"you may exile {noun} until this leaves the battlefield"
      else s!"you may exile {noun}"
    else s!"exile {noun} until this leaves the battlefield"
  | .moveZone .allTargets .exile .exile { exileUntilSourceLeaves := true, .. } =>
    "for each opponent, exile up to one target nonland permanent that player controls until this leaves the battlefield"
  | .moveZone (.target 0) .exile .exile { linkToSource := true, .. } =>
    if e.allowsZeroTargets then s!"you may exile {noun}" else s!"exile {noun}"
  | .moveZone (.linkedExile .this) (.battlefield .owner) .put _ =>
    "return the exiled card to the battlefield under its owner's control"
  | .moveZone (.target 0) (.battlefield .owner) .put _ =>
    match (e.targets.slots[0]?.map (·.domain) : Option TargetDomain) with
    | some (.object .anyGraveyard (.all #[.not (.hasType .land), .isKind .permanentCard, .stat .manaValue .le (.const mv)])) =>
      s!"put up to one target nonland permanent card with mana value {mv.toNat} or less from a graveyard onto the battlefield under its owner's control"
    | _ => s!"return {noun} to the battlefield under its owner's control"
  | .moveZone (.target 0) (.hand .owner) .returnToHand _ =>
    if e.targets == .permanentCardInYourGraveyard then
      s!"choose {noun.replace " from your graveyard" " in your graveyard"} that was put there from anywhere this turn. Return it to your hand"
    else if e.allowsZeroTargets then
      s!"return {withUpToOne noun} to its owner's hand"
    else s!"return {noun} to its owner's hand"
  | .moveZone (.inZones (.handOf (.target 0)) .anyObject) .graveyard .discard _ =>
    match body with
    | .moveZone _ _ _ { choice? := some { count := .exact (.const n), .. }, .. } =>
      s!"{noun} discards {cardPhrase n.toNat}"
    | _ => s!"{noun} discards a card"
  | .moveZone (.inZones .battlefield (.all #[.hasType .creature, .controlledBy (.ofExpr (.target 0))])) .graveyard .sacrifice _ =>
    s!"{noun} sacrifices a creature of their choice"
  | .moveZone (.inZones .battlefield (.all #[.hasType .creature, .controlledBy .defendingPlayer])) .graveyard .sacrifice _ =>
    "defending player sacrifices a creature with the least power among creatures they control"
  | .forEach (.eachPlayer .opponent) ⟨0⟩ (.moveZone (.inZones (.handOf _) .anyObject) .graveyard .discard _) =>
    "each opponent discards a card"
  | .forEach (.eachPlayer .any) ⟨0⟩ (.moveZone (.inZones .battlefield (.all #[.hasType .creature, _])) .graveyard .sacrifice _) =>
    "each player sacrifices a creature of their choice"
  | .moveZone obj (.library .owner .top false) .put _ =>
    s!"{instrObjNoun noun obj}'s owner puts it on top of their library"
  | .moveZone obj (.library .owner .bottom false) .put _ =>
    s!"{instrObjNoun noun obj}'s owner puts it on the bottom of their library"
  | .moveZone obj .graveyard .destroy _ =>
    s!"destroy {instrObjNoun noun obj}"
  | .moveZone obj .exile .exile _ =>
    s!"exile {instrObjNoun noun obj}"
  | .optional .you (some cs) (.player (.drawCards .you (.const n))) .noop _ =>
    if cs == CostSpec.discardCard then
      s!"you may discard a card. If you do, draw {cardPhrase n.toNat}"
    else
      match cs.soleGenericMana? with
      | some k => s!"you may pay \{{k}}. If you do, draw {cardPhrase n.toNat}"
      | none => s!"you may pay {cs.toNotation}. If you do, draw {cardPhrase n.toNat}"
  | .optional .you (some cs) (.seq #[.permanent (.modifyCounters (.put .plusOnePlusOne (.const 1)) .this _), .player (.drawCards .you (.const 1))]) .noop _ =>
    match cs.soleGenericMana? with
    | some k => s!"you may pay \{{k}}. If you do, put a +1/+1 counter on this creature and draw a card"
    | none => s!"you may pay {cs.toNotation}. If you do, put a +1/+1 counter on this creature and draw a card"
  | .optional .you (some cs) (.permanent (.modifyCounters (.put .plusOnePlusOne (.stepMetric .sumPower ⟨0⟩)) .this _)) .noop _ =>
    let _ := cs
    "you may sacrifice another creature. If you do, put a number of +1/+1 counters on this creature equal to the sacrificed creature's power"
  | .optional .you (some _) (.seq #[.player (.drawCards .you (.const 1)), .create (.tokens .you (.const 1) .treasure _)]) .noop _ =>
    "you may sacrifice another creature or artifact. If you do, draw a card and create a Treasure token"
  | .optional .you (some cs) (.queueReflexiveTrigger ab) .noop _ =>
    if cs == CostSpec.sacrificeAnotherCreature then
      "you may sacrifice another creature. When you do, destroy target nonland permanent an opponent controls"
    else if cs == CostSpec.sacrificeArtifactOrDiscardNonland then
      "you may sacrifice an artifact or discard a nonland card. When you do, this deals 2 damage to any target"
    else if cs == CostSpec.tapOnly then
      "you may tap this creature. When you do, another target nonattacking creature you control gains indestructible until end of turn"
    else
      s!"you may {cs.toInlinePhrase}. When you do, {instrTriggerPhrase ab.effect ab.effect.body ab.effect.targets.noun}"
  | .optional .you none (.bind ⟨0⟩ (.moveZone (.inZones (.handOf .you) .anyObject) .graveyard .discard _) (.player (.drawCards .you (.const n)))) .noop _ =>
    s!"you may discard your hand. If you do, draw {cardPhrase n.toNat}"
  | .optional .you none (.seq #[.player (.drawCards .you (.manaSpent .triggerSubject)), .ifCond _ (.moveZone _ .graveyard .discard { choice? := some { count := .exact (.const n), .. }, .. }) .noop]) .noop _ =>
    let disc := if n == 2 then "two cards" else cardPhrase n.toNat
    s!"you may draw X cards, where X is the amount of mana spent to cast that spell. If you do, discard {disc}"
  | .optional .you none (.installEffect (.applyContinuous .untilEndOfTurn .this (.setBasePT (some (.const p)) (some (.const t))))) .noop _ =>
    s!"you may have this creature's base power and toughness become {p}/{t} until end of turn"
  | .optional .you none (.bind ⟨0⟩ (.moveZone (.inZones (.handOf .you) (.hasType .artifact)) (.battlefield .controller) .put _) _) .noop _ =>
    "you may put an artifact card from your hand onto the battlefield. If it's an Equipment, attach it to this creature"
  | .bind ⟨0⟩ (.moveZone (.target 0) (.hand .owner) .returnToHand _) (.life (.gain .you (.stepMetric .sumPower ⟨0⟩))) =>
    s!"return {noun} to your hand. You gain life equal to that card's power"
  | .bind ⟨0⟩ (.moveZone (.target 0) (.hand .owner) .returnToHand _) (.ifCond (.stepSucceeded ⟨0⟩) (.permanent (.modifyCounters (.put .plusOnePlusOne (.const 1)) .this _)) .noop) =>
    s!"return {noun} to its owner's hand. If you do, put a +1/+1 counter on this creature"
  | .bind ⟨0⟩ (.moveZone (.inZones .battlefield (.all #[.any #[.hasType .artifact, .hasType .enchantment], .controlledBy .opponent])) .graveyard .destroy _) (.life (.gain .you (.stepMetric .movedCount ⟨0⟩))) =>
    "destroy all artifacts and enchantments your opponents control. You gain 1 life for each permanent destroyed this way"
  | .bind ⟨0⟩ (.moveZone (.target 0) .graveyard .destroy _) (.create (.tokens (.controllerOf (.target 0)) (.const 1) .treasure _)) =>
    s!"destroy {noun}. They create a Treasure token"
  | .bind ⟨0⟩ (.permanent (.setTapped _ true (some _))) (.player (.drawCards .you (.stepMetric .movedCount ⟨0⟩))) =>
    "you may tap any number of untapped Humans you control. Draw a card for each Human tapped this way"
  | .bind ⟨0⟩ (.damage (.deal .this (.targetSlot 0) (.const n) _)) (.ifCond _ (.moveZone (.filter (.stepObjects ⟨0⟩) (.hasSubtype (.literal sub))) .graveyard .destroy _) .noop) =>
    s!"it deals {n.toNat} damage to {noun}. If a {sub} is dealt damage this way, destroy it"
  | .bind ⟨0⟩ (.player (.inspectLibrary { source := .revealUntil .you (.hasType .creature) _, .. })) _ =>
    s!"reveal cards from the top of your library until you reveal a creature card. If its mana value is less than or equal to the number of lands you control, put it onto the battlefield. Otherwise, put it into your hand. {restOnBottomRandomPhrase}"
  | .bind ⟨0⟩ (.moveZone (.topOfLibrary .opponents (.const 2)) .graveyard .mill _) _ =>
    "each opponent mills two cards. When one or more cards are milled this way, exile target enchantment, instant, or sorcery card with equal or lesser mana value than that spell from an opponent's graveyard. Copy the exiled card. You may cast the copy without paying its mana cost"
  | .bind ⟨0⟩ (.moveZone .this .graveyard .sacrifice _) (.ifCond (.stepSucceeded ⟨0⟩) (.queueReflexiveTrigger ab) .noop) =>
    s!"sacrifice it. When you do, {instrTriggerPhrase ab.effect ab.effect.body ab.effect.targets.noun}"
  | .bind ⟨0⟩ (.player (.inspectLibrary { source := .revealUntil .you (.all #[.not (.hasType .land), .stat .manaValue .lt (.objectStat .manaValue .this)]) _ true, .. })) _ =>
    "exile cards from the top of your library until you exile a nonland card that costs less. You may cast it without paying its mana cost"
  | .stack (.mayCastOrPlay (.inZones (.handOf .you) _) { maxTotalManaValue? := some (.binary .mul (.const 2) _), .. }) =>
    "you may cast an instant or sorcery spell with mana value X or less from your hand without paying its mana cost, where X is twice the number of legendary Wizards you control"
  | .stack (.mayCastOrPlay (.inZones (.handOf .you) _) { maxTotalManaValue? := some .eventAmount, .. }) =>
    "you may cast an instant or sorcery spell from your hand with mana value less than or equal to that damage without paying its mana cost"
  | .seq #[.permanent (.modifyCounters (.put .plusOnePlusOne (.const 1)) (.inZones .battlefield (.all #[.otherThan .this, .hasType .creature, .controlledBy _])) _),
           .life (.gain .you (.aggregate .count .one _))] =>
    "put a +1/+1 counter on each other creature you control. You gain 1 life for each other creature you control"
  | .seq #[.life (.gain .you (.const n)), .player (.searchLibrary _)] =>
    s!"you gain {n.toNat} life. You may search your library for a basic land card, reveal it, then shuffle and put that card on top"
  | .seq #[.installEffect (.applyContinuous .untilEndOfTurn (.target 0) (.gainControl .you)),
           .permanent (.setTapped (.target 0) false _),
           .installEffect (.applyContinuous .untilEndOfTurn (.target 0) (.grantKeywords _))] =>
    s!"gain control of {noun} until end of turn. Untap it. It gains haste until end of turn"
  | .seq #[.player (.drawCards .you (.const 1)), .ifCond (.not _) (.moveZone (.inZones (.handOf .you) .anyObject) (.library .owner .bottom false) .put _) .noop] =>
    "draw a card. Then if you don't control a legendary creature, put a card from your hand on the bottom of your library"
  | .seq #[.bind ⟨0⟩ (.permanent (.modifyCounters (.remove (some .hope) _) .this _)) _, .ifCond _ (.seq #[.moveZone .this .graveyard .sacrifice _, .life (.gain .you (.const 4))]) .noop] =>
    "remove a hope counter from this. If you do, draw a card. Then if this has no hope counters on it, sacrifice it and you gain 4 life"
  | .seq #[.installEffect (.applyContinuous .untilEndOfTurn (.inZones .battlefield (.all #[.otherThan .this, .hasType .creature, subPred, .controlledBy _])) (.modifyPT (.const p) (.const t))),
           .installEffect (.applyContinuous .untilEndOfTurn _ (.modifyPT (.const oppP) (.const oppT)))] =>
    match extractSubtypesFromPred subPred with
    | some subtypes =>
      let who :=
        if subtypes == #[.goblin, .orc] then "other Goblins and Orcs you control"
        else s!"other {joinedSubtypes subtypes} you control"
      s!"{who} get {signedStat p}/{signedStat t} until end of turn. Creatures your opponents control get {signedStat oppP}/{signedStat oppT} until end of turn"
    | none => "resolve each step"
  | .seq #[.permanent (.modifyCounters (.put .trample (.const 1)) (.target 0) _),
           .installEffect (.applyContinuous .indefinite (.target 0) (.modifyTypes { subtypes := #[.bear], .. })),
           .ifCond _ (.player (.drawCards .you (.const 2))) .noop] =>
    s!"put a trample counter on {withUpToOne noun}. It becomes a Bear in addition to its other types. Then if you control three or more Bears, draw two cards"
  | .seq #[.permanent (.modifyCounters (.put .quest (.const 1)) .this _), .ifCond _ (.bind ⟨0⟩ (.moveZone .this .graveyard .sacrifice _) _) .noop] =>
    "put a quest counter on this enchantment. If it has six or more quest counters on it, sacrifice it. If you do, search your hand and/or library for a Dragon card and put it onto the battlefield. If you search your library this way, shuffle"
  | .seq #[.player (.drawCards .you (.const 1)), .bind ⟨0⟩ (.moveZone (.inZones (.handOf .you) .anyObject) .graveyard .discard _) (.moveZone (.filter (.stepObjects ⟨0⟩) (.hasType .land)) (.battlefield .controller) .put { tapped := true, .. })] =>
    "draw a card, then discard a card. If you discard a land card this way, put it from your graveyard onto the battlefield tapped"
  | .seq #[.bind ⟨0⟩ (.create (.tokens .you (.const 1) .alien _)) _, .permanent (.modifyCounters (.put .invasion (.const 1)) .this _)] =>
    "create a 1/1 red Alien creature token with haste and \"This token attacks each combat if able.\" Put a +1/+1 counter on it for each invasion counter on this enchantment, then put an invasion counter on this enchantment"
  | .seq #[.permanent (.setTapped _ false _), .turn (.extraPhase .combat true)] =>
    "untap all attacking creatures. After this phase, there is an additional combat phase"
  | .seq #[.permanent (.modifyCounters (.put .plan (.const 1)) .this _), .player (.scry .you (.const n))] =>
    s!"scry {n.toNat} and put a plan counter on this enchantment"
  | .seq #[.permanent (.modifyCounters (.put .plan (.const 1)) .this _), .player (.drawCards .you (.const 1)), .moveZone _ .graveyard .discard _] =>
    "draw a card, then discard a card and put a plan counter on this enchantment"
  | .seq #[.permanent (.modifyCounters (.put .plan (.const 1)) .this _), .create (.tokens .you (.const 1) .villain21menace _)] =>
    "create a 2/1 black Villain creature token with menace and put a plan counter on this enchantment"
  | .seq #[.permanent (.modifyCounters (.put .plan (.const 1)) .this _), .life (.lose _ (.const n)), .life (.gain .you (.const m))] =>
    s!"each opponent loses {n.toNat} life and you gain {m.toNat} life. Put a plan counter on this enchantment"
  | .seq #[.permanent (.modifyCounters (.put .plan (.const 1)) .this _), .player (.drawCards .you (.const 1)), .life (.lose .you (.const 1))] =>
    "you draw a card, lose 1 life, and put a plan counter on this enchantment"
  | .seq #[.permanent (.modifyCounters (.put .plan (.const 1)) .this _), .create (.tokens .you (.const 1) .treasure { tapped := true, .. })] =>
    "create a tapped Treasure token and put a plan counter on this enchantment"
  | .seq #[.permanent (.modifyCounters (.put .plan (.const 1)) .this _), .permanent (.modifyCounters (.put .plusOnePlusOne (.const 1)) (.target 0) _)] =>
    "put a +1/+1 counter on target creature you control and a plan counter on this enchantment"
  | .seq #[.moveZone .this .graveyard .sacrifice _, .player (.drawCards .you (.const 1)), .permanent (.modifyCounters (.put .plusOnePlusOne (.const 1)) _ _)] =>
    "sacrifice it, draw a card, and put a +1/+1 counter on each creature you control"
  | .seq #[.moveZone .this .graveyard .sacrifice _, .create (.tokens .you (.const n) .robotVillain22 _)] =>
    s!"sacrifice it and create {englishNumber n.toNat} 2/2 colorless Robot Villain artifact creature tokens"
  | .seq #[.permanent (.setTapped (.target 0) true _), .installEffect (.applyContinuous (.whileOnBattlefield .this) (.target 0) (.applyRule (.game (.cantBecomeUntapped .self))))] =>
    s!"tap {noun}. That creature can't become untapped for as long as you control this creature"
  | .seq #[.permanent (.setTapped (.target 0) true _), .ifCond (.exists .this) (.installEffect (.applyContinuous (.whileOnBattlefield .this) (.target 0) .loseAllAbilities)) .noop] =>
    "tap up to one target creature. It loses all abilities for as long as this remains on the battlefield"
  | .seq #[.installEffect (.applyContinuous .untilEndOfTurn (.target 0) (.grantKeywords k)),
           .ifCond (.exists (.filter (.target 0) (.hasType .creature))) _ .noop,
           .ifCond (.exists (.filter (.target 0) (.hasType .planeswalker))) _ .noop] =>
    s!"{noun} gains {KeywordAbility.joinedAnd k} until end of turn. Put a +1/+1 counter on it if it's a creature. Put a loyalty counter on it if it's a planeswalker"
  | .seq #[.installEffect (.applyContinuous .untilEndOfTurn obj (.modifyPT (.const p) (.const t))),
           .installEffect (.applyContinuous .untilEndOfTurn _ (.grantKeywords k))] =>
    if k == #[Keyword.trample] then
      s!"{instrObjNoun noun obj} gets {signedStat p}/{signedStat t} and gains trample until end of turn"
    else
      s!"{instrObjNoun noun obj} gets {signedStat p}/{signedStat t} and gains {KeywordAbility.joinedAnd k} until end of turn"
  | .seq #[.permanent (.setTapped obj true _), .permanent (.modifyCounters (.put .stun (.const 1)) _ _)] =>
    s!"tap {instrObjNoun noun obj} and put a stun counter on it"
  | _ =>
    Instruction.toOracleWith { capitalize := false } e.targets body

/-- Effect clause rendered from unified `Instruction`, targeting, and divided-damage parameters. -/
def resolutionPhrase (t : Effect) : String :=
  instrTriggerPhrase t t.body t.targets.noun

/-- Sentence whose printed “When/Whenever …” lead-in differs from the generic
`eventPrefix` (a card name, an ability word, or a more specific subject) but
whose effect clause is the shared `resolutionPhrase`. -/
def leadInSentence (ab : TriggeredAbility) (lead : String) : String :=
  s!"{lead}, {resolutionPhrase ab.effect}."

/-- Printed clause when the effect is a pure `Instruction` sequence.
Numbers and the target noun come from the effect, so Oracle refill stays
in step with the printed line. -/
def sequenceClause (e : Effect) : Option String :=
  let noun := e.targetSpec.noun
  match e.body with
  | .seq #[.player (.drawCards .you (.const 1)), .life (.lose .you (.const 1))] =>
    some "you draw a card and lose 1 life"
  | .seq #[.player (.drawCards .you (.const n)),
           .moveZone (.inZones _ .anyObject) .graveyard .discard _] =>
    some s!"draw {cardPhrase n.toNat}, then discard a card"
  | .seq #[.installEffect (.applyContinuous .untilEndOfTurn .this (.modifyPT (.const p) (.const 0))),
           .installEffect (.applyContinuous .untilEndOfTurn (.inZones _ _) (.grantKeywords k))] =>
    if k == #[Keyword.trample] then
      some s!"until end of turn, this creature gets {signedStat p}/+0 and creatures you control gain trample"
    else none
  | .seq #[.permanent (.modifyCounters (.put .plusOnePlusOne (.const n)) (.target 0) _),
           .installEffect (.applyContinuous .untilEndOfTurn (.target 0) (.grantKeywords k))] =>
    if k == #[Keyword.lifelink] && n == 1 then
      some s!"put a +1/+1 counter on {noun}. It gains lifelink until end of turn"
    else if k == #[Keyword.vigilance] then
      some s!"put {plusOnePlusOneCountersPhrase n.toNat} on {noun}. It gains vigilance until end of turn"
    else none
  | .seq #[.installEffect (.applyContinuous .untilEndOfTurn .this (.modifyPT (.const 1) (.const 0))),
           .installEffect (.applyContinuous .untilEndOfTurn .this (.applyRule (.combat (.cantBeBlocked .self))))] =>
    some "this gets +1/+0 until end of turn and can't be blocked this turn"
  | .seq #[.player (.drawCards .you (.const 1)),
           .permanent (.modifyCounters (.put .plusOnePlusOne (.const 1)) .this _)] =>
    some "draw a card and put a +1/+1 counter on this"
  | .seq #[.installEffect (.applyContinuous .untilEndOfTurn (.inZones _ _) (.modifyPT (.const p) (.const 0))),
           .installEffect (.applyContinuous .untilEndOfTurn (.inZones _ _) (.grantKeywords k))] =>
    if k == #[Keyword.firstStrike] then
      some s!"creatures you control get {signedStat p}/+0 and gain first strike until end of turn"
    else none
  | .seq #[.permanent (.modifyCounters (.put .plusOnePlusOne (.const 1)) .this _),
           .player (.drawCards .you (.const 1))] =>
    some "put a +1/+1 counter on this and draw a card"
  | .seq #[.installEffect (.applyContinuous .untilEndOfTurn .this (.modifyPT (.const p) (.const t))),
           .damage (.deal .this (.players _) (.const n) _)] =>
    some s!"this gets {signedStat p}/{signedStat t} until end of turn and deals {n} damage to each opponent"
  | .seq #[.permanent (.setTapped (.target 0) false _),
           .ifCond (.exists (.filter (.target 0) (.hasSubtype (.literal subtype))))
             (.permanent (.modifyCounters (.put .plusOnePlusOne (.const n)) (.target 0) _)) .noop] =>
    some s!"untap {noun}. If that creature is a {subtype}, put {plusOnePlusOneCountersPhrase n.toNat} on it"
  | .seq #[.life (.lose .you (.const n)),
           .create (.tokens .you (.const 1) k _)] =>
    some s!"you lose {n} life and {TokenSpec.createPhrase k 1}"
  | .seq #[.moveZone (.target 0) .exile .exile _,
           .life (.lose _ (.const n))] =>
    some s!"exile {withUpToOne noun}. Each opponent loses {n} life"
  | _ => none

private partial def isEnchantedHostInstr : Instruction → Bool
  | .permanent (.setTapped .attachedHost _ _)
  | .permanent (.modifyCounters _ .attachedHost _)
  | .permanent (.setDesignation .attachedHost _ _)
  | .moveZone .attachedHost _ _ _
  | .damage (.deal _ (.objects .attachedHost) _ _)
  | .installEffect (.applyContinuous _ .attachedHost _) => true
  | .seq steps => steps.any isEnchantedHostInstr
  | _ => false

def toNotation (ab : TriggeredAbility) : String :=
  if ab.isSagaChapter then
    s!"When a lore counter is put on this Saga, {resolutionPhrase ab.effect}."
  else if ab.isManaSpentCastScry then
    let n :=
      match ab.effect.body with
      | .player (.scry _ (.const k)) => k.toNat
      | _ => 1
    s!"When that mana is spent to cast a creature spell that shares a creature type with your commander, scry {n}."
  else if ab.isModal then
    let once := if ab.onceEachTurn then " This ability triggers only once each turn." else ""
    match ab.effect.body with
    | .chooseModes spec =>
      if spec.chooseAtResolution && spec.modes.size == 2 && ab.effect.targets.isEmpty then
        s!"{eventPrefix ab}{interveningClause ab}, {resolutionPhrase spec.modes[0]!} or {resolutionPhrase spec.modes[1]!}.{once}"
      else
        let modeTexts := ab.modeEffects.toList.map fun m =>
          let txt := capitalizeAscii (resolutionPhrase m)
          let txt := if txt.endsWith "." then txt else s!"{txt}."
          s!"• {txt}"
        let hdr :=
          if spec.minModes == ValueExpr.const 0 && spec.maxModes == ValueExpr.chosenX then "choose up to X"
          else if spec.minModes == ValueExpr.const 2 && spec.maxModes == ValueExpr.const 2 then "choose two"
          else if spec.unusedThisTurn then "choose one that hasn't been chosen this turn"
          else if spec.unusedEver then "choose one that hasn't been chosen"
          else "choose one"
        s!"{eventPrefix ab}{interveningClause ab}, {hdr} — {" ".intercalate modeTexts}{once}"
    | _ =>
      let modeTexts := ab.modeEffects.toList.map fun m =>
        let txt := capitalizeAscii (resolutionPhrase m)
        let txt := if txt.endsWith "." then txt else s!"{txt}."
        s!"• {txt}"
      s!"{eventPrefix ab}{interveningClause ab}, choose one — {" ".intercalate modeTexts}{once}"
  else
    let p := ab.pattern
    match ab.effect.body with
    | .create (.tokens .you (.const n) k _) =>
      if p == .stepEachUpkeep then
        s!"At the beginning of each player's upkeep, you {TokenSpec.createPhrase k n.toNat}."
      else if p == .drawCard .opponent && ab.limit == .nthEachTurn 2 && n == 1 then
        "Whenever an opponent draws their second card each turn, you create a Treasure token."
      else if p == .damageDealt (.all #[.hasSubtype (.literal .dwarf), .controlledBy .you])
          (.playerOrObject .any { zones := .battlefield, pred := .hasType .battle }) (combatOnly := true) && n == 2 then
        leadInSentence ab "Whenever a Dwarf you control deals combat damage to a player or battle"
      else
        let once := if ab.onceEachTurn then " This ability triggers only once each turn." else ""
        let clause := (sequenceClause ab.effect).getD (resolutionPhrase ab.effect)
        s!"{eventPrefix ab}{interveningClause ab}, {clause}.{once}"
    | .permanent (.modifyCounters (.put .plusOnePlusOne (.const n)) .this _) =>
      if n == 2 && p == .anotherSubtypeYouControlEnters .wolf then
        "Whenever another Wolf you control enters, put two +1/+1 counters on Chief of the Wilds."
      else if n == 1 && p == .thisDealtDamage then
        "Whenever this is dealt damage, put a +1/+1 counter on it."
      else
        let once := if ab.onceEachTurn then " This ability triggers only once each turn." else ""
        s!"{eventPrefix ab}{interveningClause ab}, {resolutionPhrase ab.effect}.{once}"
    | .permanent (.attach .this (.target 0) false) =>
      if p == .thisEnters && ab.effect.targets == .creatureYouControl then
        leadInSentence ab "When this Equipment enters"
      else
        s!"{eventPrefix ab}{interveningClause ab}, {resolutionPhrase ab.effect}."
    | .player (.surveil .you (.const n)) =>
      if p == .thisEnters then s!"When this permanent enters, surveil {n.toNat}."
      else s!"{eventPrefix ab}{interveningClause ab}, {resolutionPhrase ab.effect}."
    | .player (.connive .this) =>
      if p == .thisEnters then
        leadInSentence ab "When this creature enters"
      else
        match p with
        | .castSpell { relation := .you, pred := .any } (.hasColor (.literal color))
            (some .hand) .. =>
          s!"Whenever you cast a {color} spell from your hand, this connives."
        | _ =>
          let once := if ab.onceEachTurn then " This ability triggers only once each turn." else ""
          s!"{eventPrefix ab}{interveningClause ab}, {resolutionPhrase ab.effect}.{once}"
    | .damage (.deal .this (.players (.target 0)) (.const 3) _) =>
      if p == .youCastColor .red then
        "Whenever you cast a red spell, Aragorn deals 3 damage to target opponent."
      else
        let once := if ab.onceEachTurn then " This ability triggers only once each turn." else ""
        s!"{eventPrefix ab}{interveningClause ab}, {resolutionPhrase ab.effect}.{once}"
    | .moveZone (.inZones (.handOf (.target 0)) .anyObject) .graveyard .discard { choice? := some { count := .exact (.const n), .. }, .. } =>
      if p == .thisEnters then
        let cards := if n == 2 then "two cards" else cardPhrase n.toNat
        s!"When this enchantment enters, target opponent discards {cards}."
      else s!"{eventPrefix ab}{interveningClause ab}, {resolutionPhrase ab.effect}."
    | .player (.inspectLibrary { source := .topCards .you (.const _) true, action := .takeMatching (.hasType .creature) (.exact (.const 1)) (.battlefield .controller) _ false true, .. }) =>
      if p == .thisDies then
        leadInSentence ab "When this artifact is put into a graveyard from the battlefield"
      else s!"{eventPrefix ab}{interveningClause ab}, {resolutionPhrase ab.effect}."
    | .seq #[.permanent (.setTapped _ false _), .turn (.extraPhase .combat true)] =>
      match p with
      | .attacks _ _ _ _ (some n) _ =>
        leadInSentence ab
          s!"Whenever you attack with creatures with total power {n} or greater for the first time each turn"
      | _ => s!"{eventPrefix ab}{interveningClause ab}, {resolutionPhrase ab.effect}."
    | .seq #[.permanent (.attach .this (.target 0) _), .ifCond (.exists .this) _ .noop] =>
      if p == .thisEnters then leadInSentence ab "When this Equipment enters"
      else s!"{eventPrefix ab}{interveningClause ab}, {resolutionPhrase ab.effect}."
    | body =>
      if p == .thisEnters && isEnchantedHostInstr body then
        leadInSentence ab "When this Aura enters"
      else if p == .equippedAttacksAlone && ab.effect.body == (Effect.drawAndLoseLife 1 1).body then
        "Whenever equipped creature attacks alone, you draw a card and you lose 1 life."
      else if p == .landYouControlEnters && ab.effect.body == Effect.seqDrawPlusOneSource.body then
        "Landfall — Whenever a land you control enters, draw a card and put a +1/+1 counter on Gandalf."
      else if p == .permanentEnters (.all #[
            .otherThan .this, .hasSupertype .legendary,
            .hasSubtype (.literal .elf), .controlledBy .you]) &&
          ab.effect.body == (Effect.seqDrawThenDiscard 2).body then
        "Whenever another legendary Elf you control enters, draw two cards, then discard a card."
      else
        let once :=
          if ab.onceEachTurn then " This ability triggers only once each turn."
          else if ab.optionalOnceEachTurn then " Do this only once each turn."
          else ""
        let clause := (sequenceClause ab.effect).getD (resolutionPhrase ab.effect)
        let inter :=
          if (clause.map Char.toLower).startsWith "if " then ""
          else interveningClause ab
        s!"{eventPrefix ab}{inter}, {clause}.{once}"

instance : ToString TriggeredAbility where
  toString := toNotation

instance : ToOracle TriggeredAbility where
  toOracle _ ab := toNotation ab

end TriggeredAbility

end Mtg.Engine
