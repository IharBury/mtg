import Mtg.Engine.Card.ChapterEffects
import Mtg.Engine.Card.SpellEffects
import Mtg.Engine.Card.StaticAbility
import Mtg.Engine.Card.TriggerEffects

/-!
# Printed triggered abilities (CR 603)

Named constructors for the printed triggered-ability wordings and their
Oracle-text rendering.
-/

namespace Mtg.Engine

namespace TriggeredAbility

/-- Classification of this triggered ability. Exhaustive so a new constructor
is a compile error here rather than silently matching `false` elsewhere. -/
def timing : TriggeredAbility → TriggerTiming
  | .triggered w e opts =>
    let t := (e.asTrigger?.getD (.draw 0)).timing
    { t with
      events :=
        match w with
        | .fromEffect => t.events
        | _ => w.events
      onceEachTurn := t.onceEachTurn || opts.onceEachTurn
      youControlCreatureWithPower := opts.youControlCreatureWithPower
      thisOrNontokenSubtype := opts.thisOrNontokenSubtype
      thisOrAnotherSubtype := opts.thisOrAnotherSubtype
      anotherSubtypeOrEquipment := opts.anotherSubtypeOrEquipment
      gainedLifeAtLeast := opts.gainedLifeAtLeast
      anotherCreaturePowerAtMost := opts.anotherCreaturePowerAtMost
      targeting := if opts.untargeted then {} else e.targeting
      allowsZeroTargets := e.allowsZeroTargets || opts.allowsZeroTargets }

/-- Unified effect this trigger resolves. -/
def effect (ab : TriggeredAbility) : Effect :=
  match ab with
  | .triggered _ e _ => e

/-- Leftover shared trigger this ability resolves. -/
def shared (ab : TriggeredAbility) : SharedTrigger :=
  match ab.effect.asTrigger? with
  | some te => te
  | none => .draw 0

/-- Catalog aliases for reusable triggers that now share `triggered`. -/
def onEnterScry (n : Nat) : TriggeredAbility := .triggered .enter (Effect.ofTrigger (.scry n))
def onAttackScry (n : Nat) : TriggeredAbility := .triggered .attack (Effect.ofTrigger (.scry n))
def onAttackWithElvesScry (n : Nat) : TriggeredAbility :=
  .triggered .youAttackWithElves (Effect.ofTrigger (.scry n))
def onOneOrMoreOtherCreaturesDieScry (n : Nat) : TriggeredAbility :=
  .triggered .oneOrMoreOtherCreaturesDie (Effect.ofTrigger (.scry n))
def onCastColorScry (c : Color) (n : Nat) : TriggeredAbility :=
  .triggered (.youCastColor c) (Effect.ofTrigger (.scry n))
def onEnterDraw (n : Nat) : TriggeredAbility := .triggered .enter (Effect.ofTrigger (.draw n))
def onDiesDraw (n : Nat) : TriggeredAbility := .triggered .dies (Effect.ofTrigger (.draw n))
def onYouAttackDraw : TriggeredAbility := .triggered .youAttack (Effect.ofTrigger (.draw 1))
def onYourEndStepDraw : TriggeredAbility := .triggered .yourEndStep (Effect.ofTrigger (.draw 1))
def onBecomesTargetDraw : TriggeredAbility := .triggered .becomesTarget (Effect.ofTrigger (.draw 1))
def onArtifactYouControlEntersDraw : TriggeredAbility :=
  .triggered .artifactYouControlEnters (Effect.ofTrigger (.draw 1))
def onTheRingTemptsYouDraw (n : Nat) : TriggeredAbility :=
  .triggered .theRingTemptsYou (Effect.ofTrigger (.draw n))
def onChooseRingBearerDraw : TriggeredAbility :=
  .triggered .youChooseRingBearer (Effect.ofTrigger (.draw 1))
def onCombatDamageDraw (n : Nat) : TriggeredAbility :=
  .triggered .combatDamageToPlayer (Effect.ofTrigger (.draw n))
def onEnterCreateTokens (kind : TokenKind) (n : Nat) (tapped : Bool := false) :
    TriggeredAbility :=
  .triggered .enter (Effect.ofTrigger (.createTokens kind n tapped))
def onYourUpkeepCreateTokens (kind : TokenKind) (n : Nat) : TriggeredAbility :=
  .triggered .yourUpkeep (Effect.ofTrigger (.createTokens kind n))
def onLandYouControlEntersCreateTokens (kind : TokenKind) (n : Nat) :
    TriggeredAbility :=
  .triggered .landYouControlEnters (Effect.ofTrigger (.createTokens kind n))
def onDiesCreateTokens (kind : TokenKind) (n : Nat) : TriggeredAbility :=
  .triggered .dies (Effect.ofTrigger (.createTokens kind n))
def onYouDrawSecondCreateTokens (kind : TokenKind) : TriggeredAbility :=
  .triggered .youDrawSecond (Effect.ofTrigger (.createTokens kind 1))
def onCastColorCreateTokens (c : Color) (kind : TokenKind) (n : Nat) :
    TriggeredAbility :=
  .triggered (.youCastColor c) (Effect.ofTrigger (.createTokens kind n))
def onEnterOrAttackCreateWall : TriggeredAbility :=
  .triggered (.or .enter .attack) (Effect.ofTrigger (.createTokens .wall 1))
def onEnterAmassGoblins (n : Nat) : TriggeredAbility :=
  .triggered .enter (Effect.ofTrigger (.amassGoblins n))
def onDiesAmassGoblins (n : Nat) : TriggeredAbility :=
  .triggered .dies (Effect.ofTrigger (.amassGoblins n))
def onYouAttackAmassGoblins (n : Nat) : TriggeredAbility :=
  .triggered .youAttack (Effect.ofTrigger (.amassGoblins n))
def onCastNoncreatureAmassGoblins (n : Nat) : TriggeredAbility :=
  .triggered .youCastNoncreature (Effect.ofTrigger (.amassGoblins n))
def onEnterOrAttackAmassGoblins (n : Nat) : TriggeredAbility :=
  .triggered (.or .enter .attack) (Effect.ofTrigger (.amassGoblins n))
def onCreatureCardLeavesYourGyAmassGoblins (n : Nat) : TriggeredAbility :=
  .triggered .creatureCardLeavesYourGy (Effect.ofTrigger (.amassGoblins n))
def onEnterRecruit : TriggeredAbility := .triggered .enter (Effect.ofTrigger .recruit)
def onDiesRecruit : TriggeredAbility := .triggered .dies (Effect.ofTrigger .recruit)
def onEnterOrAttackRecruit : TriggeredAbility :=
  .triggered (.or .enter .attack) (Effect.ofTrigger .recruit)
def onYouAttackRecruit : TriggeredAbility := .triggered .youAttack (Effect.ofTrigger .recruit)
def onEnterDealDividedDamage (amount maxTargets : Nat) : TriggeredAbility :=
  .triggered .enter (Effect.ofTrigger (.dividedDamage amount maxTargets))
def onEnterOrAttackDealDividedDamage (amount maxTargets : Nat) : TriggeredAbility :=
  .triggered (.or .enter .attack) (Effect.ofTrigger (.dividedDamage amount maxTargets))
def onEnterPlusOneOnCreature : TriggeredAbility :=
  .triggered .enter (Effect.ofTrigger (.plusOneOn .creature))
def onEnterOrAttackPlusOneOnCreature : TriggeredAbility :=
  .triggered (.or .enter .attack) (Effect.ofTrigger (.plusOneOn .creature))
def onLandYouControlEntersPlusOnePlusOne : TriggeredAbility :=
  .triggered .landYouControlEnters (Effect.ofTrigger (.plusOneOn .creatureYouControl))
def onCombatPlusOneOnCreatureYouControl : TriggeredAbility :=
  .triggered .yourBeginCombat (Effect.ofTrigger (.plusOneOn .creatureYouControl))
def onEnterAttachToSubtype (subtype : String) : TriggeredAbility :=
  .triggered .enter (Effect.ofTrigger (.attachTo (.creatureYouControlSubtype subtype)))
def onEnterAttachToLegendary : TriggeredAbility :=
  .triggered .enter (Effect.ofTrigger (.attachTo .legendaryCreatureYouControl))
def onEnterAttachToCreatureYouControl : TriggeredAbility :=
  .triggered .enter (Effect.ofTrigger (.attachTo .creatureYouControl))
def onEnterTargetOpponentSacrificesCreature : TriggeredAbility :=
  .triggered .enter (Effect.ofTrigger .opponentSacrificesCreature)
def onEnterTargetOpponentSacrifices : TriggeredAbility :=
  onEnterTargetOpponentSacrificesCreature
def onDrawSecondPlusOne : TriggeredAbility :=
  .triggered .youDrawSecond (Effect.ofTrigger .plusOneOnSource)
def onDrawPlusOne : TriggeredAbility :=
  .triggered .youDraw (Effect.ofTrigger .plusOneOnSource)
def onGainLifePlusOne : TriggeredAbility :=
  .triggered .youGainLife (Effect.ofTrigger .plusOneOnSource)
def onAnotherArtifactEntersPlusOne : TriggeredAbility :=
  .triggered .anotherArtifactEnters (Effect.ofTrigger .plusOneOnSource)
def onYourBeginCombatFerociousPlusOne : TriggeredAbility :=
  .triggered .yourBeginCombat (Effect.ofTrigger .plusOneOnSource) .ferocious
def onEquippedAttacksAloneDrawLoseLife : TriggeredAbility :=
  .triggered .equippedAttacksAlone (Effect.ofTrigger .drawAndLoseLife)
def onYouAttackFerociousDrawLoseLife : TriggeredAbility :=
  .triggered .youAttack (Effect.ofTrigger .drawAndLoseLife) .ferocious
def onCastWithTreasureDrawLoseLife : TriggeredAbility :=
  .triggered .youCastWithTreasure (Effect.ofTrigger .drawAndLoseLife)
def onYourEndStepDrawLoseLife : TriggeredAbility :=
  .triggered .yourEndStep (Effect.ofTrigger .drawAndLoseLife)
def onEnterConnive : TriggeredAbility :=
  .triggered .enter (Effect.ofTrigger .connive)
def onAttackConnive : TriggeredAbility :=
  .triggered .attack (Effect.ofTrigger .connive)
def onYouCastColorFromHandConnive (color : Color) : TriggeredAbility :=
  .triggered (.youCastColorFromHand color) (Effect.ofTrigger .connive)
def onEquippedCreatureYouControlAttacksConnive : TriggeredAbility :=
  .triggered .equippedCreatureYouControlAttacks (Effect.ofTrigger .connive)
def onCombatTargetYouControlConnives : TriggeredAbility :=
  .triggered .yourBeginCombat (Effect.ofTrigger (.conniveTarget .creatureYouControl))
def onEnterExileOppNonlandUntilLeaves : TriggeredAbility :=
  .triggered .enter (Effect.ofTrigger (.exileUntilLeaves .oppNonland))
def onEnterExileOppTappedUntilLeaves : TriggeredAbility :=
  .triggered .enter (Effect.ofTrigger (.exileUntilLeaves .oppTappedCreature))
def onAttackMayExileDefenderUntilLeaves : TriggeredAbility :=
  .triggered .attack (Effect.ofTrigger (.exileUntilLeaves .defendingPlayerCreature))
    { allowsZeroTargets := true }
def onEnterGainLife (n : Nat) : TriggeredAbility :=
  .triggered .enter (Effect.ofTrigger (.gainLife n))
def onAttackFerociousGainLife (n : Nat) : TriggeredAbility :=
  .triggered .attack (Effect.ofTrigger (.gainLife n)) .ferocious
def onEnterTargetGets (power toughness : Int) : TriggeredAbility :=
  .triggered .enter (Effect.ofTrigger (.pumpTarget .creature power toughness))
def onDiesOppCreatureGets (power toughness : Int) : TriggeredAbility :=
  .triggered .dies (Effect.ofTrigger (.pumpTarget .oppCreature power toughness))
def onCastColorPump (color : Color) (power toughness : Int) : TriggeredAbility :=
  .triggered (.youCastColor color) (Effect.ofTrigger (.pumpTarget .creature power toughness))
def onLandYouControlEntersGets (power toughness : Int) : TriggeredAbility :=
  .triggered .landYouControlEnters (Effect.ofTrigger (.sourceGets power toughness))
def onAttackFerociousSourceGets (power toughness : Int) : TriggeredAbility :=
  .triggered .attack (Effect.ofTrigger (.sourceGets power toughness)) .ferocious
def onAnotherElfYouControlEntersGets1 : TriggeredAbility :=
  .triggered .anotherElfYouControlEnters (Effect.ofTrigger (.sourceGets 1 1))
def onArtifactYouControlEntersDrawOnce : TriggeredAbility :=
  .triggered .artifactYouControlEnters (Effect.ofTrigger (.draw 1)) .once
def onActivateCreatureAbilityDrawOnce : TriggeredAbility :=
  .triggered .youActivateCreatureAbility (Effect.ofTrigger (.draw 1)) .once
def onAnotherSubtypeOrEquipmentEntersDrawOnce (subtype : String) : TriggeredAbility :=
  .triggered .anotherSubtypeOrEquipmentEnters (Effect.ofTrigger (.draw 1))
    { onceEachTurn := true, anotherSubtypeOrEquipment := some subtype }
def onEachEndStepDrawIfGainedLife (n : Nat) : TriggeredAbility :=
  .triggered .eachEndStep (Effect.ofTrigger (.draw 1)) { gainedLifeAtLeast := some n }
def onThisOrNontokenSubtypeEntersCreateTokens (subtype : String) (kind : TokenKind)
    (n : Nat) : TriggeredAbility :=
  .triggered .thisOrNontokenSubtypeEnters (Effect.ofTrigger (.createTokens kind n))
    { thisOrNontokenSubtype := some subtype }
def onThisOrAnotherSubtypeEntersCreateTokens (subtype : String) (kind : TokenKind)
    (n : Nat) : TriggeredAbility :=
  .triggered .thisOrAnotherSubtypeEnters (Effect.ofTrigger (.createTokens kind n))
    { thisOrAnotherSubtype := some subtype }
def onSubtypeYouControlCombatDamageCreateTokens (subtype : String) (kind : TokenKind)
    (n : Nat) : TriggeredAbility :=
  .triggered .combatDamageToPlayerOrBattle (Effect.ofTrigger (.createTokens kind n))
    { watchedSubtype := some subtype }
def onOpponentDrawsSecondCreateTreasure : TriggeredAbility :=
  .triggered .opponentDrawsSecond (Effect.ofTrigger (.createTokens .treasure 1))
def onOpponentCastsFirstNoncreatureRecruit : TriggeredAbility :=
  .triggered .opponentCastsFirstNoncreature (Effect.ofTrigger .youRecruit)
def onCastColorDamageOpponent (color : Color) (n : Nat) : TriggeredAbility :=
  .triggered (.youCastColor color) (Effect.ofTrigger (.damageEachOpponent n))
def onCastGreenOrForestEntersPlusOne : TriggeredAbility :=
  .triggered (.or .youCastGreen .forestYouControlEnters) (Effect.ofTrigger (.plusOneOn .creatureYouControl))
def onAttackOtherGets2AndTrample : TriggeredAbility :=
  .triggered .attack (Effect.ofTrigger (.onPermanent .anotherCreatureYouControl (.pumpAndTrample 2 0)))
def onEnterMayDiscardDraw (n : Nat) : TriggeredAbility :=
  .triggered .enter (Effect.ofTrigger (.mayDiscardDraw n))
def onCastInstantOrSorceryDealDamageToEachOpponent (amount : Nat) : TriggeredAbility :=
  .triggered .youCastInstantOrSorcery (Effect.ofTrigger (.damageEachOpponent amount)) .noTarget
def onEnterEachOpponentDiscards : TriggeredAbility :=
  .triggered .enter (Effect.ofTrigger .eachOpponentDiscards)
def onEnterExileTop : TriggeredAbility :=
  .triggered .enter (Effect.ofTrigger .exileTop)
def onAttackTargetGainsKeywords (k : Keywords) : TriggeredAbility :=
  .triggered .attack (Effect.ofTrigger (.onPermanent .attackingCreature (.grantKeywords k)))
def onDrawSecondMillPlayer (n : Nat) : TriggeredAbility :=
  .triggered .youDrawSecond (Effect.ofTrigger (.millPlayer n))
def onAnotherGoblinOrcArmyDiesExileTop : TriggeredAbility :=
  .triggered .anotherGoblinOrcArmyDies (Effect.ofTrigger .exileTop)
def onAnotherSubtypeEntersPlusOneOnSource (subtype : String) (n : Nat) :
    TriggeredAbility :=
  .triggered .anotherCreatureYouControlEnters (Effect.ofTrigger (.onSource (.plusOne n)))
    { thisOrAnotherSubtype := some subtype }
def onOpponentCastsAmassOrcs (n : Nat) : TriggeredAbility :=
  .triggered .opponentCastsSpell (Effect.ofTrigger (.amassOrcs n))
def onCreatureYouControlAttacksAloneInvestigate : TriggeredAbility :=
  .triggered .creatureYouControlAttacksAlone (Effect.ofTrigger .investigate)
def onCreatureYouControlAttacksAlonePump (power toughness : Int) : TriggeredAbility :=
  .triggered .creatureYouControlAttacksAlone (Effect.ofTrigger (.pumpCause power toughness))
def onEnterTargetOpponentDiscards (n : Nat) : TriggeredAbility :=
  .triggered .enter (Effect.ofTrigger (.targetOpponentDiscards n))
def onEquipmentYouControlEntersDraw : TriggeredAbility :=
  .triggered .equipmentYouControlEnters (Effect.ofTrigger (.draw 1))
def onEnterSearchForest : TriggeredAbility :=
  .triggered .enter (Effect.ofTrigger .searchForest)
def onEnterSearchBasicToHand : TriggeredAbility :=
  .triggered .enter (Effect.ofTrigger .searchBasicToHand)
def onEnterEachPlayerSacrificesCreature : TriggeredAbility :=
  .triggered .enter (Effect.ofTrigger .eachPlayerSacrificesCreature)
def onEnterMayExileAnotherCreature : TriggeredAbility :=
  .triggered .enter (Effect.ofTrigger (.exileTarget .anotherCreature)) { allowsZeroTargets := true }
def onEnterReturnCreatureFromGyToHand : TriggeredAbility :=
  .triggered .enter (Effect.ofTrigger .returnCreatureFromGyToHand)
def onCombatDamageToPlayerLoot : TriggeredAbility :=
  .triggered .combatDamageToPlayer (Effect.ofTrigger .loot)
def onAttackFerociousPlusOneEach : TriggeredAbility :=
  .triggered .attack (Effect.ofTrigger .plusOneEachYouControl) .ferocious
def onAttackFerociousSourceGetsAndTeamTrample (power : Int) : TriggeredAbility :=
  .triggered .attack (Effect.ofTrigger (.sourceGetsAndTeamTrample power)) .ferocious
def onEnterOrAttackHoneEachEquipment : TriggeredAbility :=
  .triggered (.or .enter .attack) (Effect.ofTrigger .honeEachEquipment)
def onEnterOrAttackPlusOneEachOtherGainLife : TriggeredAbility :=
  .triggered (.or .enter .attack) (Effect.ofTrigger .plusOneEachOtherGainLife)
def onLandYouControlEntersBecomePT (power toughness : Int) : TriggeredAbility :=
  .triggered .landYouControlEnters (Effect.ofTrigger (.becomePT power toughness))
def onCastNoncreaturePumpAndDamageOpponents (n : Nat) : TriggeredAbility :=
  .triggered .youCastNoncreature (Effect.ofTrigger (.pumpAndDamageOpponents n))
def onDrawSecondPlusOneLifelink : TriggeredAbility :=
  .triggered .youDrawSecond (Effect.ofTrigger (.plusOneAndLifelink .creature))
def onYouAttackPumpTargetPerPlains : TriggeredAbility :=
  .triggered .youAttack (Effect.ofTrigger .pumpTargetPerPlains)
def onAnotherLegendarySubtypeEntersLoot (subtype : String) : TriggeredAbility :=
  .triggered .anotherCreatureYouControlEnters (Effect.ofTrigger (.drawThenDiscard 2))
    { thisOrAnotherSubtype := some subtype }
def onRingTemptsMayDiscardDraw (n : Nat) : TriggeredAbility :=
  .triggered .theRingTemptsYou (Effect.ofTrigger (.mayDiscardHandDraw n))
def onScryPumpSelfForEachLookedAt : TriggeredAbility :=
  .triggered .youScry (Effect.ofTrigger .pumpByLookedAt)
def onScryPumpAndUnblockableOnce : TriggeredAbility :=
  .triggered .youScry (Effect.ofTrigger .pumpAndUnblockable) .once
def onAttackPumpByGreatestPower : TriggeredAbility :=
  .triggered .attack (Effect.ofTrigger .pumpGreatestPower)
def onBecomesBlockedDeal1ToBlockers : TriggeredAbility :=
  .triggered .becomesBlocked (Effect.ofTrigger (.damageBlockers 1))
def onAttackPumpForEachOtherCreature : TriggeredAbility :=
  .triggered .attack (Effect.ofTrigger .pumpForEachOtherCreature)
def onAttackWithTwoOrMoreGrantFlying : TriggeredAbility :=
  .triggered .youAttackWithTwoOrMore (Effect.ofTrigger (.grantFlying .attackingCreatureWithoutFlying))
def onLeaveReturnExiled : TriggeredAbility :=
  .triggered .leaving (Effect.ofTrigger .returnLinkedExile)
def onEnterCreateThenAttach (kind : TokenKind) : TriggeredAbility :=
  .triggered .enter (Effect.ofTrigger (.createThenAttach kind))
def onEnterAmassThenAttach (n : Nat) : TriggeredAbility :=
  .triggered .enter (Effect.ofTrigger (.amassThenAttach n))
def onEnterGainLifeSearchBasicOnTop (n : Nat) : TriggeredAbility :=
  .triggered .enter (Effect.ofTrigger (.gainLifeSearchBasicOnTop n))
def onYourFirstMainAddMana (types : Array ManaType) : TriggeredAbility :=
  .triggered .yourFirstMain (Effect.ofTrigger (.addMana types))
def onEnterCreateAxe : TriggeredAbility :=
  .triggered .enter (Effect.ofTrigger .createAxe)
def onLandYouControlEntersTapOrUntap : TriggeredAbility :=
  .triggered .landYouControlEnters (Effect.ofTrigger .tapOppOrUntapYours)
def onEnterGainControlOppUntilEot : TriggeredAbility :=
  .triggered .enter (Effect.ofTrigger .gainControlOppUntilEot)
def onEnterCreateAxeAttach : TriggeredAbility :=
  .triggered .enter (Effect.ofTrigger .createAxeAttach)
def onDiesAmassGoblinsEqualPower : TriggeredAbility :=
  .triggered .dies (Effect.ofTrigger .amassGoblinsEqualPower)
def onLandYouControlEntersPayReturnFromGy : TriggeredAbility :=
  .triggered .landYouControlEnters (Effect.ofTrigger .payReturnFromGy)
def onYouSacrificeTokenOppLosesLife : TriggeredAbility :=
  .triggered .youSacrificeToken (Effect.ofTrigger (.targetOpponentLosesLife 1))
def onLandYouControlEntersPlusOneVigilance : TriggeredAbility :=
  .triggered .landYouControlEnters (Effect.ofTrigger (.plusOneVigilance 2))
def onCastNoncreatureMayDrawXDiscard2 : TriggeredAbility :=
  .triggered .youCastNoncreature (Effect.ofTrigger .mayDrawXDiscard2)
def onLandYouControlEntersDrawPlusOneSource : TriggeredAbility :=
  .triggered .landYouControlEnters (Effect.ofTrigger .drawPlusOneSource)
def onArmyCombatDamageRingTempts : TriggeredAbility :=
  .triggered .armyYouControlCombatDamage (Effect.ofTrigger .ringTempts)
def onAttackSetOtherBasePT : TriggeredAbility :=
  .triggered .attack (Effect.ofTrigger .setOtherBasePT)
def onEnterOrAttackReturnElfGainLife : TriggeredAbility :=
  .triggered (.or .enter .attack) (Effect.ofTrigger .returnElfGainLife)
def onDiesDealDamageEqualToPowerToOppCreature : TriggeredAbility :=
  .triggered .dies (Effect.ofTrigger .damageFromLastKnownPower)
def onEnterExileOppGyCardOppsLoseLife (life : Nat) : TriggeredAbility :=
  .triggered .enter (Effect.ofTrigger (.exileOppGyCardOppsLoseLife life))
def onEnterCreaturesYouControlGetAndFirstStrike (power : Int) : TriggeredAbility :=
  .triggered .enter (Effect.ofTrigger (.creaturesYouControlPumpAndFirstStrike power))
def onAnotherCreatureYouControlPowerAtMostEntersMayPayDraw (power : Int)
    (generic : Nat) : TriggeredAbility :=
  .triggered .anotherCreatureYouControlEnters (Effect.ofTrigger (.mayPayGenericDraw generic))
    { anotherCreaturePowerAtMost := some power }
def onEnterDrawThenBottomIfNoLegendary : TriggeredAbility :=
  .triggered .enter (Effect.ofTrigger .drawThenBottomIfNoLegendary)
def onYourEndStepRemoveHopeDrawSac : TriggeredAbility :=
  .triggered .yourEndStep (Effect.ofTrigger .removeHopeDrawSac)
def onAttackTapHumansDraw : TriggeredAbility :=
  .triggered .attack (Effect.ofTrigger .tapHumansDraw)
def onEnterUntapOtherPlusOneIfSubtype (subtype : String) : TriggeredAbility :=
  .triggered .enter (Effect.ofTrigger (.untapPlusOneIfSubtype subtype))
def onEnterDestroyOppArtifactsEnchantmentsGainLife : TriggeredAbility :=
  .triggered .enter (Effect.ofTrigger .destroyOppArtifactsEnchantmentsGainLife)
def onAttackDamageEqualSubtypeToEachOpponent (subtype : String) : TriggeredAbility :=
  .triggered .attack (Effect.ofTrigger (.damageEqualSubtypeToEachOpponent subtype))
def onAttackDamageEqualTreasures : TriggeredAbility :=
  .triggered .attack (Effect.ofTrigger .damageEqualTreasures)
def onPlayerCastsSecondSpellLoseLifeCreateTreasure : TriggeredAbility :=
  .triggered .anyPlayerCastsSecondSpell (Effect.ofTrigger .loseLifeCreateTreasure)
def onEnterDealDamageDestroyIfSubtype (n : Nat) (subtype : String) : TriggeredAbility :=
  .triggered .enter (Effect.ofTrigger (.dealDamageDestroyIfSubtype n subtype))
def onEnterAttachTargetEquipment : TriggeredAbility :=
  .triggered .enter (Effect.ofTrigger .attachEquipmentToCreature)
def onAttackDefenderSacsLeastPower : TriggeredAbility :=
  .triggered .attack (Effect.ofTrigger .defenderSacsLeastPower)
def onEnterReturnOtherPlusOne : TriggeredAbility :=
  .triggered .enter (Effect.ofTrigger .returnOtherPlusOne)
def onEnterLookAtTopRevealTypes (n : Nat) (types : Array String) : TriggeredAbility :=
  .triggered .enter (Effect.ofTrigger (.lookAtTopRevealTypes n types))
def onEnterCreateTappedTreasuresEqualOppArtifacts : TriggeredAbility :=
  .triggered .enter (Effect.ofTrigger .createTappedTreasuresEqualOppArtifacts)
def onCombatDamagePutNonlandMvAtMost (mv : Nat) : TriggeredAbility :=
  .triggered .combatDamageToPlayerOrBattle (Effect.ofTrigger (.putNonlandMvAtMostFromGy mv))
def onEachCombatOthersGetAndOppsGet (subtypes : Array String)
    (power toughness oppP oppT : Int) : TriggeredAbility :=
  .triggered .eachBeginCombat (Effect.ofTrigger (.othersGetAndOppsGet subtypes power toughness oppP oppT))
def onCombatDamageWolfPlusOneOrTreasure : TriggeredAbility :=
  .triggered .combatDamageToPlayer (Effect.ofTrigger .wolfPlusOneOrTreasure)
def onYourBeginCombatTrampleCounterBecomeBear : TriggeredAbility :=
  .triggered .yourBeginCombat (Effect.ofTrigger .trampleCounterBecomeBear)
def onEnterMillThenSubtypeToHand (n : Nat) (subtype : String) : TriggeredAbility :=
  .triggered .enter (Effect.ofTrigger (.millThenSubtypeToHand n subtype))
def onEnterExileOppNonlandEachUntilLeaves : TriggeredAbility :=
  .triggered .enter (Effect.ofTrigger .exileOppNonlandEachUntilLeaves)
def onCastCreaturePlusOneEqualMv : TriggeredAbility :=
  .triggered .youCastCreature (Effect.ofTrigger .plusOneEqualLastKnownMv)
def onMountainEntersQuestThenDragon : TriggeredAbility :=
  .triggered .mountainYouControlEnters (Effect.ofTrigger .mountainQuestDragon)
def onEquippedCombatDamageTreasuresPerChosenType : TriggeredAbility :=
  .triggered .equippedDealsCombatDamageToPlayer (Effect.ofTrigger .treasuresPerChosenType)
def onNontokenYouControlDiesRevealCreature : TriggeredAbility :=
  .triggered .nontokenYouControlDies (Effect.ofTrigger .revealUntilCreature) .once
def onAttackMaySacAnotherPlusOneEqualPower : TriggeredAbility :=
  .triggered .attack (Effect.ofTrigger .attackSacPlusOneEqualPower)
def onEnterLootLandEntersTapped : TriggeredAbility :=
  .triggered .enter (Effect.ofTrigger .lootLandEntersTapped)
def onPlayerLosesLifeMillThatMany : TriggeredAbility :=
  .triggered .playerLosesLife (Effect.ofTrigger .millThatManyLost)
def onDiesDrawPerFatGraveyard : TriggeredAbility :=
  .triggered .dies (Effect.ofTrigger .drawPerFatGraveyard)
def onEnterMaySacDrawTreasure : TriggeredAbility :=
  .triggered .enter (Effect.ofTrigger .maySacDrawTreasure)
def onEquippedAttacksPlusOneEachIfCityBlessing : TriggeredAbility :=
  .triggered .equippedAttacks (Effect.ofTrigger .plusOneEachIfCityBlessing)
def onYourBeginCombatCastInstantSorceryFromHand : TriggeredAbility :=
  .triggered .yourBeginCombat (Effect.ofTrigger .castInstantSorceryFromHand)
def onEquippedCombatDamageCastInstantSorcery : TriggeredAbility :=
  .triggered .equippedDealsCombatDamageToPlayer (Effect.ofTrigger .castInstantSorceryMvAtMost)
def onCastSecondSpellMillThenCopy : TriggeredAbility :=
  .triggered .youCastSecondSpell (Effect.ofTrigger .millThenCopy)
def onCombatAnotherGetsSourcePower : TriggeredAbility :=
  .triggered .yourBeginCombat (Effect.ofTrigger .pumpTargetBySourcePower)
def onCombatCreateAlienPerInvasion : TriggeredAbility :=
  .triggered .yourBeginCombat (Effect.ofTrigger .createAlienPerInvasion)
def onCombatMayPutArtifactAttachEquipment : TriggeredAbility :=
  .triggered .yourBeginCombat (Effect.ofTrigger .mayPutArtifactAttachEquipment)
def onCastCascade : TriggeredAbility :=
  .triggered .cascade (Effect.ofTrigger .cascade)
def onTokenYouControlEntersBelladonna : TriggeredAbility :=
  .triggered .tokenYouControlEnters (Effect.ofTrigger .belladonnaTokenReward)
def onEnterBolgMaySacrifice : TriggeredAbility :=
  .triggered .enter (Effect.ofTrigger .bolgMaySacrifice)
def onBolgDealSacrificedPower : TriggeredAbility :=
  .triggered .bolgSacrificedForReflexive (Effect.ofTrigger .bolgDealSacrificedPower)
def onEquippedAttacksCreateSpirits : TriggeredAbility :=
  .triggered .equippedAttacks (Effect.ofTrigger .createSpiritsForEquipped)
def onCombatDamageCreateTreasuresEqualPlayerArtifacts : TriggeredAbility :=
  .triggered .combatDamageToPlayer (Effect.ofTrigger .createTreasuresEqualDamagedPlayerArtifacts)
def onEnterOrOpponentDrawsDeal1AmassOrcs : TriggeredAbility :=
  .triggered (.or .enter .opponentDrawsExceptFirst) (Effect.ofTrigger .deal1ThenAmassOrcs)
def onAttackWithTotalPowerUntapExtraCombat (n : Int) : TriggeredAbility :=
  .triggered .youAttackWithTotalPower (Effect.ofTrigger (.untapAttackersExtraCombat n)) .once
def onAnotherCreatureYouControlEntersAlliance : TriggeredAbility :=
  .triggered .anotherCreatureYouControlEnters (Effect.ofTrigger .allianceMode)
def onEnterDestroyOtherAmassControllerPower : TriggeredAbility :=
  .triggered .enter (Effect.ofTrigger .destroyOtherAmassControllerPower)
def onOpponentCastsChosenParityModes : TriggeredAbility :=
  .triggered .opponentCastsMatchingParity (Effect.ofTrigger .gollumMode)
def onThisOrAnotherSubtypeEntersDiscardHand (subtype : String) : TriggeredAbility :=
  .triggered .thisOrAnotherSubtypeEnters (Effect.ofTrigger .discardHandDrawDamageIfStory)
    { thisOrAnotherSubtype := some subtype }
def onAttackCastFromGyArtifactInstantSorcery : TriggeredAbility :=
  .triggered .attack (Effect.ofTrigger .castFromGyArtifactInstantSorcery)
def onAttackEquippedGainDoubleStrike : TriggeredAbility :=
  .triggered .attack (Effect.ofTrigger .equippedAttackersGainDoubleStrike)
def onEnterTapEnchantedRemoveCounters : TriggeredAbility :=
  .triggered .enter (Effect.ofTrigger .tapEnchantedRemoveCounters)
def onDiesRevealTopPutRandomCreature (n : Nat) : TriggeredAbility :=
  .triggered .dies (Effect.ofTrigger (.revealTopPutRandomCreature n))
def onYourBeginCombatIfDrawnTwoPumpFirstStrike : TriggeredAbility :=
  .triggered .yourBeginCombat (Effect.ofTrigger .beginCombatIfDrawnTwoPump)
def onEnterHonePerOppCreaturesAttach : TriggeredAbility :=
  .triggered .enter (Effect.ofTrigger .honePerOppAttach)
def onPutCountersOnGoblinOrcArmyDamageOpp : TriggeredAbility :=
  .triggered .youPutCountersOnGoblinOrcArmy (Effect.ofTrigger (.damageTargetOpponent 2))
def onEnterIfNotTokenCopySelf : TriggeredAbility :=
  .triggered .enter (Effect.ofTrigger .copySelfNonlegendary)
def onEnterAttachEquipmentThenFight : TriggeredAbility :=
  .triggered .enter (Effect.ofTrigger .attachEquipmentThenFight)
def onDiesReturnAsArtifact : TriggeredAbility :=
  .triggered .dies (Effect.ofTrigger .returnAsArtifact)
def onEnterExileLandsThenReturnTapped : TriggeredAbility :=
  .triggered .enter (Effect.ofTrigger .exileLandsThenReturnTapped)
def onCombatDamageImpulseInstantSorcery : TriggeredAbility :=
  .triggered .combatDamageToPlayer (Effect.ofTrigger .grimaImpulse)
def onYourEndStepPalantir : TriggeredAbility :=
  .triggered .yourEndStep (Effect.ofTrigger .palantir)
def onDealtNoncombatDamageCreateTreasures : TriggeredAbility :=
  .triggered .sourceDealtNoncombatDamage (Effect.ofTrigger .treasuresEqualLastKnown)
def onEnterIfCastProtectionEverything : TriggeredAbility :=
  .triggered .enter (Effect.ofTrigger .protectionEverything)
def onYourUpkeepLoseLifePerBurden : TriggeredAbility :=
  .triggered .yourUpkeep (Effect.ofTrigger .loseLifePerBurden)
def onFinalSagaChapterRevealSaga : TriggeredAbility :=
  .triggered .finalSagaChapterResolves (Effect.ofTrigger .revealSaga) .once
def onCombatDamageToYouSacRingTempts : TriggeredAbility :=
  .triggered .combatDamageToYou (Effect.ofTrigger .sacDamagersRingTempts)
def sagaChapter (n : Nat) (e : Effect) : TriggeredAbility :=
  match e.asChapter? with
  | some ch =>
    .triggered .sagaChapter
      { e with resolution := Resolution.trigger (SharedTrigger.chapter n ch) }
  | none => .triggered .sagaChapter e
def onTappedForTeamworkPlusOneAndDraw : TriggeredAbility :=
  .triggered .tappedForTeamwork (Effect.ofTrigger .plusOneOnSourceAndDraw)
def onEachEndStepDrawIfAttackedOrEnteredSubtype (subtype : String) : TriggeredAbility :=
  .triggered .eachEndStep (Effect.ofTrigger (.drawIfAttackedOrEnteredSubtype subtype))
def onAttackOthersOfSubtypeGetEqualToughness (subtype : String) : TriggeredAbility :=
  .triggered .attack (Effect.ofTrigger (.othersOfSubtypeGetEqualSourceToughness subtype))
def onCreatureYouControlEntersScryAndPlan (n : Nat) : TriggeredAbility :=
  .triggered .creatureYouControlEnters (Effect.ofTrigger (.scryAndPlan n))
def onCreaturesYouControlBecomeTappedLootAndPlan : TriggeredAbility :=
  .triggered .creaturesYouControlBecomeTapped (Effect.ofTrigger .lootAndPlan)
def onYouDrawSecondCreateVillainAndPlan : TriggeredAbility :=
  .triggered .youDrawSecond (Effect.ofTrigger .createVillainAndPlan)
def onVillainYouControlEntersDrainAndPlan (n : Nat) : TriggeredAbility :=
  .triggered (.subtypeYouControlEnters "Villain") (Effect.ofTrigger (.drainAndPlan n))
def onCreatureCardsToGyDrawLoseLifeAndPlan : TriggeredAbility :=
  .triggered .creatureCardsPutIntoYourGy (Effect.ofTrigger .drawLoseLifeAndPlan)
def onCastNoncreatureTreasureAndPlan : TriggeredAbility :=
  .triggered .youCastNoncreature (Effect.ofTrigger .treasureTappedAndPlan)
def onLandYouControlEntersPlusOneAndPlan : TriggeredAbility :=
  .triggered .landYouControlEnters (Effect.ofTrigger .plusOneOnTargetAndPlan)
def onFourthPlanDrawPlusOneEach : TriggeredAbility :=
  .triggered (.nthPlanCounter 4) (Effect.ofTrigger .planFinishDrawPlusOneEach)
def onFourthPlanReturnInstants : TriggeredAbility :=
  .triggered (.nthPlanCounter 4) (Effect.ofTrigger .planFinishReturnInstants)
def onSeventhPlanControlOpponent : TriggeredAbility :=
  .triggered (.nthPlanCounter 7) (Effect.ofTrigger .planFinishControlOpponent)
def onFifthPlanExileTopCast : TriggeredAbility :=
  .triggered (.nthPlanCounter 5) (Effect.ofTrigger .planFinishExileTopCast)
def onThirdPlanCreateRobots : TriggeredAbility :=
  .triggered (.nthPlanCounter 3) (Effect.ofTrigger (.planFinishCreateRobots 3))
def onFourthPlanDividedDamage : TriggeredAbility :=
  .triggered (.nthPlanCounter 4) (Effect.ofTrigger (.planFinishDividedDamage 7))
def onFourthPlanIndestructible : TriggeredAbility :=
  .triggered (.nthPlanCounter 4) (Effect.ofTrigger .planFinishIndestructibleOnTarget)
def onEnterSurveil (n : Nat) : TriggeredAbility :=
  .triggered .enter (Effect.ofTrigger (.surveil n))
def onEnterEnchanted (action : PermanentAction) : TriggeredAbility :=
  .triggered .enter (Effect.ofTrigger (.onEnchanted action))
def onEnterAttachThen (followup : PermanentAction) : TriggeredAbility :=
  .triggered .enter (Effect.ofTrigger (.attachThen followup))
def onEnterExileOtherCopyEnchanted : TriggeredAbility :=
  .triggered .enter (Effect.ofTrigger .exileOtherCopyEnchanted)
def onEnterExileCreatureReturnEndStep : TriggeredAbility :=
  .triggered .enter (Effect.ofTrigger .exileUntilNextEndStep)
def onEnterTapOrUntapNonland : TriggeredAbility :=
  .triggered .enter (Effect.ofTrigger .tapOrUntapNonland)
def onEnterCreateFoodOrTreasure : TriggeredAbility :=
  .triggered .enter (Effect.ofTrigger .createFoodOrTreasure)
def onEnterVillainIfGyElseMill : TriggeredAbility :=
  .triggered .enter (Effect.ofTrigger .villainIfGyElseMill)
def onEnterDrawMayPutLandTapped : TriggeredAbility :=
  .triggered .enter (Effect.ofTrigger .drawMayPutLandTapped)
def onEnterDrawGainLifeIfAnotherHero : TriggeredAbility :=
  .triggered .enter (Effect.ofTrigger .drawGainLifeIfAnotherHero)
def onEnterPlusOneOrTwoIfAnotherHero : TriggeredAbility :=
  .triggered .enter (Effect.ofTrigger .plusOneOrTwoIfAnotherHero)
def onEnterMaySacArtifactOrDiscardDraw : TriggeredAbility :=
  .triggered .enter (Effect.ofTrigger .maySacArtifactOrDiscardDraw)
def onEnter (e : Effect) : TriggeredAbility :=
  .triggered .enter e
def onStep (e : Effect) : TriggeredAbility :=
  .triggered .fromEffect e
def onDeath (e : Effect) : TriggeredAbility :=
  .triggered .fromEffect e
def onThisAttack (e : Effect) : TriggeredAbility :=
  .triggered .attack e
def onEnterOrAttack (e : Effect) : TriggeredAbility :=
  .triggered (.or .enter .attack) e
def onWatch (e : Effect) : TriggeredAbility :=
  .triggered .fromEffect e
def onYouAttacking (e : Effect) : TriggeredAbility :=
  .triggered .youAttack e
def onCasting (e : Effect) : TriggeredAbility :=
  .triggered .fromEffect e
def onResource (e : Effect) : TriggeredAbility :=
  .triggered .fromEffect e

/-- Damage amount and maximum number of targets when this ability divides
damage as the controller chooses (CR 601.2d). -/
def dividedDamage? (ab : TriggeredAbility) : Option (Nat × Nat) :=
  ab.timing.dividedDamage

/-- How this ability resolves (CR 608). -/
def resolution (ab : TriggeredAbility) : TriggerResolution :=
  ab.timing.resolution

instance : HasTargeting TriggeredAbility where
  targeting ab := ab.timing.targeting

/-- Targeting shape when this trigger is put on the stack (CR 603.3d). -/
def targeting (ab : TriggeredAbility) : EffectTargeting :=
  HasTargeting.targeting ab

/-- True when this ability fires on `e`. Game queues triggers by `TriggerEvent`. -/
def firesOn (ab : TriggeredAbility) (e : TriggerEvent) : Bool :=
  ab.timing.events.contains e

/-- Whom this trigger may target when announced (CR 603.3d / 601.2c). -/
def targetKind (ab : TriggeredAbility) : TriggerTargetKind :=
  HasTargeting.targetKind ab

/-- True when putting this trigger on the stack requires announcing a target
(CR 603.3d / 601.2c). “Up to one” still announces, including choosing zero. -/
def requiresTarget (ab : TriggeredAbility) : Bool :=
  HasTargeting.requiresTarget ab

/-- True when zero targets is a legal announcement (CR 115.1c / 601.2c), e.g.
“choose up to one”. Such a trigger is never removed for lack of targets. -/
def allowsZeroTargets (ab : TriggeredAbility) : Bool :=
  ab.timing.allowsZeroTargets

/-- Intervening power threshold, if this ability requires you to control a
creature with at least that power (e.g. Ferocious). -/
def youControlCreatureWithPower? (ab : TriggeredAbility) : Option Int :=
  ab.timing.youControlCreatureWithPower

/-- Leading “When/Whenever …” from the event list. -/
def eventPrefix (t : TriggerTiming) : String :=
  if t.events.contains .entering && t.events.contains .attacking then
    "Whenever this creature enters or attacks"
  else if t.events.contains .yourEndStep then
    "At the beginning of your end step"
  else if t.events.contains .yourBeginCombat then
    "At the beginning of combat on your turn"
  else if t.events.contains .yourUpkeep then
    "At the beginning of your upkeep"
  else if t.events.contains .yourFirstMain then
    "At the beginning of your first main phase"
  else if t.events.contains .eachEndStep then
    "At the beginning of each end step"
  else if t.events.contains .eachBeginCombat then
    "At the beginning of each combat"
  else if t.events.contains .youCastGreen && t.events.contains .forestYouControlEnters then
    "Whenever you cast a green spell and whenever a Forest you control enters"
  else if t.events.contains .thisOrAnotherSubtypeYouControlEnters then
    match t.thisOrAnotherSubtype with
    | some s => s!"Whenever this or another {s} you control enters"
    | none => "Whenever this or another creature you control enters"
  else if t.events.contains .anotherSubtypeOrEquipmentYouControlEnters then
    match t.anotherSubtypeOrEquipment with
    | some s => s!"Whenever another {s} or Equipment you control enters"
    | none => "Whenever another creature or Equipment you control enters"
  else if t.events.contains .thisOrNontokenSubtypeYouControlEnters then
    match t.thisOrNontokenSubtype with
    | some s => s!"Whenever this or another nontoken {s} you control enters"
    | none => "Whenever this or another nontoken creature you control enters"
  else if t.events.contains .anotherCreatureYouControlEnters then
    match t.anotherCreaturePowerAtMost, t.thisOrAnotherSubtype with
    | some n, _ =>
      s!"Whenever another creature you control with power {n} or less enters"
    | none, some s => s!"Whenever another {s} you control enters"
    | none, none => "Whenever another creature you control enters"
  else
    match t.events[0]? with
    | none => "When this occurs"
    | some e =>
      let word := if e.isWhenever then "Whenever" else "When"
      s!"{word} {e.clause}"

/-- Intervening “while you control a creature with power ≥ n”, or empty. -/
def interveningClause (t : TriggerTiming) : String :=
  match t.youControlCreatureWithPower, t.gainedLifeAtLeast with
  | some n, _ => s!" while you control a creature with power {n} or greater"
  | none, some n => s!", if you gained {n} or more life this turn"
  | none, none => ""

/-- Effect clause from resolution, targeting, and divided-damage parameters. -/
def resolutionPhrase (t : TriggerTiming) : String :=
  let noun := t.targeting.kind.noun
  match t.resolution with
  | .pumpGreatestPower =>
    "it gets +X/+0 until end of turn, where X is the greatest power among creatures you control"
  | .setOtherBasePT =>
    "choose up to one other target creature you control. Its base power and toughness become equal to this creature's power and toughness until end of turn"
  | .onPermanent action => PermanentAction.toNotation action noun
  | .damageBlockers n =>
    s!"it deals {n} damage to each creature blocking it"
  | .scry n => s!"scry {n}"
  | .draw n => s!"draw {cardPhrase n}"
  | .searchForest =>
    "search your library for a Forest card, put that card onto the battlefield, then shuffle"
  | .mayDiscardDraw n =>
    s!"you may discard a card. If you do, draw {cardPhrase n}"
  | .opponentSacrificesCreature =>
    s!"{noun} sacrifices a creature of their choice"
  | .dividedDamage =>
    match t.dividedDamage with
    | some (amount, maxTargets) =>
      s!"it deals {amount} damage divided as you choose among {dividedAmong maxTargets}"
    | none => "it deals damage divided as you choose"
  | .damageFromLastKnownPower =>
    s!"it deals damage equal to its power to {noun}"
  | .returnElfGainLife =>
    s!"return {noun} to your hand. You gain life equal to that card's power"
  | .damageEachOpponent n =>
    s!"this creature deals {n} damage to each opponent"
  | .pumpByLookedAt =>
    "this creature gets +1/+1 until end of turn for each card looked at while scrying this way"
  | .onSource action => PermanentAction.toNotation action "this creature"
  | .gainLife n => s!"you gain {n} life"
  | .eachPlayerSacrificesCreature =>
    "each player sacrifices a creature of their choice"
  | .eachOpponentDiscards =>
    "each opponent discards a card"
  | .exileOppGyCardOppsLoseLife n =>
    s!"exile up to one {noun}. Each opponent loses {n} life"
  | .creaturesYouControlPumpAndFirstStrike p =>
    s!"creatures you control get {signedStat p}/+0 and gain first strike until end of turn"
  | .pumpForEachOtherCreature =>
    "it gets +1/+1 until end of turn for each other creature you control"
  | .grantFlying =>
    s!"{noun} gains flying until end of turn"
  | .mayPayGenericDraw generic =>
    s!"you may pay \{{generic}}. If you do, draw a card"
  | .drawThenBottomIfNoLegendary =>
    "draw a card. Then if you don't control a legendary creature, put a card from your hand on the bottom of your library"
  | .exileTarget =>
    if t.allowsZeroTargets then s!"you may exile {noun}" else s!"exile {noun}"
  | .exileUntilLeaves =>
    if t.allowsZeroTargets then
      if t.targeting.kind == .defendingPlayerCreature then
        s!"you may exile {noun} until this leaves the battlefield"
      else
        s!"you may exile {noun}"
    else
      s!"exile {noun} until this leaves the battlefield"
  | .returnLinkedExile =>
    "return the exiled card to the battlefield under its owner's control"
  | .removeHopeDrawSac =>
    "remove a hope counter from this. If you do, draw a card. Then if this has no hope counters on it, sacrifice it and you gain 4 life"
  | .loot =>
    "draw a card, then discard a card"
  | .tapHumansDraw =>
    "you may tap any number of untapped Humans you control. Draw a card for each Human tapped this way"
  | .pumpAndUnblockable =>
    "this gets +1/+0 until end of turn and can't be blocked this turn"
  | .recruit =>
    "recruit"
  | .youRecruit =>
    "you recruit"
  | .exileTop =>
    s!"exile the top card of your library. {playThatCardUntilNextTurnPhrase}"
  | .sourceGetsAndTeamTrample p =>
    s!"until end of turn, this creature gets {signedStat p}/+0 and creatures you control gain trample"
  | .untapPlusOneIfSubtype subtype =>
    s!"untap {noun}. If that creature is a {subtype}, put a +1/+1 counter on it"
  | .plusOneEachYouControl =>
    "put a +1/+1 counter on each creature you control"
  | .drawAndLoseLife =>
    "you draw a card and lose 1 life"
  | .amassGoblins n =>
    s!"amass Goblins {n}"
  | .createTokens kind n tapped =>
    TokenKind.createPhrase kind n (tapped := tapped)
  | .createThenAttach kind =>
    s!"{TokenKind.createPhrase kind 1}, then attach this Equipment to it"
  | .amassThenAttach n =>
    s!"amass Goblins {n}, then attach this Equipment to the amassed Army"
  | .attachSourceToTarget =>
    s!"attach it to {noun}"
  | .searchBasicToHand =>
    searchLibraryToHandPhrase "a basic land card"
  | .gainLifeSearchBasicOnTop n =>
    s!"you gain {n} life. You may search your library for a basic land card, reveal it, then shuffle and put that card on top"
  | .plusOneEachOtherGainLife =>
    "put a +1/+1 counter on each other creature you control. You gain 1 life for each other creature you control"
  | .destroyOppArtifactsEnchantmentsGainLife =>
    "destroy all artifacts and enchantments your opponents control. You gain 1 life for each permanent destroyed this way"
  | .damageEqualSubtypeToEachOpponent subtype =>
    s!"it deals damage equal to the number of {StaticAbility.pluralSubtype subtype} you control to each opponent"
  | .damageEqualTreasures =>
    s!"it deals damage equal to the number of Treasures you control to {noun}"
  | .loseLifeCreateTreasure =>
    "you lose 1 life and create a Treasure token"
  | .dealDamageDestroyIfSubtype n subtype =>
    s!"it deals {n} damage to {noun}. If a {subtype} is dealt damage this way, destroy it"
  | .attachEquipmentToCreature =>
    "attach target Equipment you control to up to one target creature you control"
  | .addMana types =>
    s!"add {manaSymbolsText types}"
  | .defenderSacsLeastPower =>
    "defending player sacrifices a creature with the least power among creatures they control"
  | .createAxe =>
    "create a colorless Equipment artifact token named Axe with \"Equipped creature gets +1/+0\" and equip {2}"
  | .tapOppOrUntapYours =>
    "choose one — tap target creature an opponent controls; untap target creature you control"
  | .becomePT p t =>
    s!"you may have this creature's base power and toughness become {p}/{t} until end of turn"
  | .returnOtherPlusOne =>
    "return up to one other target permanent you control to its owner's hand. If you do, put a +1/+1 counter on this creature"
  | .lookAtTopRevealTypes n types =>
    let joined :=
      match types.toList with
      | [a, b] => s!"a {a} or {b} card"
      | xs => s!"a {String.intercalate " or " xs} card"
    s!"look at the top {n} cards of your library. You may reveal {joined} from among them and put it into your hand. {restOnBottomRandomPhrase}"
  | .pumpAndDamageOpponents n =>
    s!"this gets +1/+1 until end of turn and deals {n} damage to each opponent"
  | .createTappedTreasuresEqualOppArtifacts =>
    "create X tapped Treasure tokens, where X is the number of artifacts your opponents control"
  | .gainControlOppUntilEot =>
    s!"gain control of {noun} until end of turn. Untap it. It gains haste until end of turn"
  | .othersGetAndOppsGet subtypes p t oppP oppT =>
    let who :=
      if subtypes == #["Goblin", "Orc"] then "other Goblins and Orcs you control"
      else s!"other {StaticAbility.joinedSubtypes subtypes} you control"
    s!"{who} get {signedStat p}/{signedStat t} until end of turn. Creatures your opponents control get {signedStat oppP}/{signedStat oppT} until end of turn"
  | .putNonlandMvAtMostFromGy mv =>
    s!"put up to one target nonland permanent card with mana value {mv} or less from a graveyard onto the battlefield under its owner's control"
  | .honeEachEquipment =>
    "put a hone counter on each Equipment you control"
  | .cascade =>
    "exile cards from the top of your library until you exile a nonland card that costs less. You may cast it without paying its mana cost"
  | .belladonnaTokenReward =>
    "you gain 1 life if this is the first time this ability has resolved this turn. If it's the second time, draw a card. If it's the third time, put a +1/+1 counter on each creature you control"
  | .bolgMaySacrifice =>
    "you may sacrifice another creature. When you do, Bolg deals damage equal to that creature's power to another target creature. If excess damage was dealt this way, amass Goblins X, where X is that excess damage"
  | .bolgDealSacrificedPower =>
    s!"Bolg deals damage equal to the sacrificed creature's power to {noun}. If excess damage was dealt this way, amass Goblins X, where X is that excess damage"
  | .createSpiritsForEquipped =>
    "create two tapped 1/1 white Spirit creature tokens with flying. If that creature is legendary, instead create two of those tokens that are tapped and attacking"
  | .createTreasuresEqualDamagedPlayerArtifacts =>
    "you create a Treasure token for each artifact that player controls"
  | .deal1ThenAmassOrcs =>
    s!"this creature deals 1 damage to {noun}. Then amass Orcs 1"
  | .untapAttackersExtraCombat =>
    "untap all attacking creatures. After this phase, there is an additional combat phase"
  | .eaglesCreateBirds =>
    "create a 4/4 white Bird Soldier creature token with flying for each creature returned to your hand this way"
  | .allianceMode =>
    "choose one that hasn't been chosen this turn — • Add {G}{G}{G}. • Put a +1/+1 counter on each creature you control. • Scry 2, then draw a card"
  | .destroyOtherAmassControllerPower =>
    s!"destroy {noun}. Its controller amasses Goblins X, where X is that creature's power. If you controlled that creature, draw a card"
  | .gollumMode =>
    "choose one that hasn't been chosen — • Put a +1/+1 counter on Gollum. • Each opponent loses 2 life and you gain 2 life. • Draw a card"
  | .returnCreatureFromGyToHand =>
    s!"return {noun} to your hand"
  | .discardHandDrawDamageIfStory =>
    "you may discard your hand. Draw X cards, where X is the number of cards discarded this way. If you have an enduring story, this deals X damage to each opponent"
  | .plusOneAndLifelink =>
    s!"put a +1/+1 counter on {noun}. It gains lifelink until end of turn"
  | .wolfPlusOneOrTreasure =>
    "choose one — • Put a +1/+1 counter on target Wolf you control. • Create a Treasure token"
  | .trampleCounterBecomeBear =>
    s!"put a trample counter on up to one {noun}. It becomes a Bear in addition to its other types. Then if you control three or more Bears, draw two cards"
  | .castFromGyArtifactInstantSorcery =>
    "you may cast an artifact, instant, or sorcery spell from your graveyard. If an instant or sorcery spell cast this way would be put into your graveyard, exile it instead"
  | .millThenSubtypeToHand n subtype =>
    s!"mill {n} cards, then put all {subtype} cards from among them into your hand"
  | .exileOppNonlandEachUntilLeaves =>
    "for each opponent, exile up to one target nonland permanent that player controls until this leaves the battlefield"
  | .plusOneEqualLastKnownMv =>
    s!"put X +1/+1 counters on {noun}, where X is that spell's mana value"
  | .createAxeAttach =>
    "create a colorless Equipment artifact token named Axe with \"Equipped creature gets +1/+0\" and equip {2}. When you do, attach it to target creature you control"
  | .equippedAttackersGainDoubleStrike =>
    "each equipped attacking creature gains double strike until end of turn"
  | .tapEnchantedRemoveCounters =>
    "tap enchanted creature and remove all counters from it"
  | .revealTopPutRandomCreature n =>
    s!"reveal the top {n} cards of your library. Put a random creature card from among them onto the battlefield. {restOnBottomRandomPhrase}"
  | .beginCombatIfDrawnTwoPump =>
    s!"if you've drawn two or more cards this turn, {noun} gets +3/+0 and gains first strike until end of turn"
  | .mountainQuestDragon =>
    "put a quest counter on this enchantment. If it has six or more quest counters on it, sacrifice it. If you do, search your hand and/or library for a Dragon card and put it onto the battlefield. If you search your library this way, shuffle"
  | .millPlayer n =>
    s!"{noun} mills {n} cards"
  | .treasuresPerChosenType =>
    "choose a creature type. Create a Treasure token for each creature you control of that type"
  | .revealUntilCreature =>
    s!"reveal cards from the top of your library until you reveal a creature card. If its mana value is less than or equal to the number of lands you control, put it onto the battlefield. Otherwise, put it into your hand. {restOnBottomRandomPhrase}"
  | .attackSacPlusOneEqualPower =>
    "you may sacrifice another creature. If you do, put a number of +1/+1 counters on this creature equal to the sacrificed creature's power"
  | .amassGoblinsEqualPower =>
    "amass Goblins X, where X is this creature's power"
  | .payReturnFromGy =>
    "you may pay {1}{G}{U}. If you do, return this card from your graveyard to your hand"
  | .lootLandEntersTapped =>
    "draw a card, then discard a card. If you discard a land card this way, put it from your graveyard onto the battlefield tapped"
  | .honePerOppAttach =>
    "put a hone counter on this for each creature target opponent controls. Attach this to up to one target creature you control"
  | .damageTargetOpponent n =>
    s!"this deals {n} damage to {noun}"
  | .millThatManyLost =>
    "that player mills that many cards"
  | .drawPerFatGraveyard =>
    "draw a card for each graveyard with seven or more cards in it"
  | .copySelfNonlegendary =>
    "if they're not a token, create two tokens that are copies of them, except the tokens aren't legendary"
  | .maySacDrawTreasure =>
    "you may sacrifice another creature or artifact. If you do, draw a card and create a Treasure token"
  | .targetOpponentLosesLife n =>
    s!"{noun} loses {n} life"
  | .attachEquipmentThenFight =>
    "attach any number of target Equipment you control to target creature you control. When one or more Equipment become attached to that creature this way, that creature deals damage equal to its power to up to one target creature"
  | .plusOneVigilance n =>
    s!"put {plusOnePlusOneCountersPhrase n} on {noun}. It gains vigilance until end of turn"
  | .drawThenDiscardN n =>
    s!"draw {cardPhrase n}, then discard a card"
  | .returnAsArtifact =>
    "if they were a creature, return them to the battlefield. They're an artifact"
  | .mayDrawXDiscard2 =>
    "you may draw X cards, where X is the amount of mana spent to cast that spell. If you do, discard two cards"
  | .plusOneEachIfCityBlessing =>
    "put a +1/+1 counter on each creature you control. If you have the city's blessing, put two +1/+1 counters on each creature you control instead"
  | .castInstantSorceryFromHand =>
    "you may cast an instant or sorcery spell with mana value X or less from your hand without paying its mana cost, where X is twice the number of legendary Wizards you control"
  | .drawPlusOneSource =>
    "draw a card and put a +1/+1 counter on this"
  | .exileLandsThenReturnTapped =>
    "exile up to three target lands you control, then return them to the battlefield tapped under their owner's control"
  | .castInstantSorceryMvAtMost =>
    "you may cast an instant or sorcery spell from your hand with mana value less than or equal to that damage without paying its mana cost"
  | .grimaImpulse =>
    "that player exiles cards from the top of their library until they exile an instant or sorcery card. You may cast that card without paying its mana cost. Then that player puts the exiled cards that weren't cast this way on the bottom of their library in a random order"
  | .palantir =>
    "put an influence counter on this and scry 2. Then target opponent may have you draw a card. If that player doesn't, you mill X cards, where X is the number of influence counters on this, and that player loses life equal to the total mana value of those cards"
  | .millThenCopy =>
    "each opponent mills two cards. When one or more cards are milled this way, exile target enchantment, instant, or sorcery card with equal or lesser mana value than that spell from an opponent's graveyard. Copy the exiled card. You may cast the copy without paying its mana cost"
  | .amassOrcs n =>
    s!"amass Orcs {n}"
  | .ringTempts =>
    "the Ring tempts you"
  | .mayDiscardHandDraw n =>
    s!"you may discard your hand. If you do, draw {cardPhrase n}"
  | .treasuresEqualLastKnown =>
    "create that many Treasure tokens"
  | .protectionEverything =>
    "if you cast it, you gain protection from everything until your next turn"
  | .loseLifePerBurden =>
    "you lose 1 life for each burden counter on this"
  | .revealSaga =>
    "reveal cards from the top of your library until you reveal a Saga card. Put that card onto the battlefield and the rest on the bottom of your library in a random order"
  | .sacDamagersRingTempts =>
    "each opponent sacrifices a creature of their choice that dealt combat damage to you this turn. The Ring tempts you"
  | .chapter e => (Effect.ofChapter e).phrase
  | .pumpTargetPerPlains =>
    "target creature you control gets +1/+1 until end of turn for each Plains you control"
  | .investigate => "investigate"
  | .plusOneOnSourceAndDraw =>
    "put a +1/+1 counter on this and draw a card"
  | .connive => "it connives"
  | .targetConnive => "target creature you control connives"
  | .pumpCause p t =>
    s!"that creature gets {signedStat p}/{signedStat t} until end of turn"
  | .othersOfSubtypeGetEqualSourceToughness subtype =>
    s!"each other {StaticAbility.pluralSubtype subtype} you control get +X/+X until end of turn, where X is this toughness"
  | .drawIfAttackedOrEnteredSubtype subtype =>
    let a := if subtype == "Hero" then "a Hero" else s!"a {subtype}"
    s!"if you attacked with {a} this turn or {a} entered the battlefield under your control this turn, draw a card"
  | .scryAndPlan n =>
    s!"scry {n} and put a plan counter on this enchantment"
  | .lootAndPlan =>
    "draw a card, then discard a card and put a plan counter on this enchantment"
  | .createVillainAndPlan =>
    "create a 2/1 black Villain creature token with menace and put a plan counter on this enchantment"
  | .drainAndPlan n =>
    s!"each opponent loses {n} life and you gain {n} life. Put a plan counter on this enchantment"
  | .drawLoseLifeAndPlan =>
    "you draw a card, lose 1 life, and put a plan counter on this enchantment"
  | .treasureTappedAndPlan =>
    "create a tapped Treasure token and put a plan counter on this enchantment"
  | .plusOneOnTargetAndPlan =>
    "put a +1/+1 counter on target creature you control and a plan counter on this enchantment"
  | .planFinishDrawPlusOneEach =>
    "sacrifice it, draw a card, and put a +1/+1 counter on each creature you control"
  | .planFinishReturnInstants =>
    "sacrifice it. When you do, return up to two target instant and/or sorcery cards from your graveyard to your hand"
  | .planFinishControlOpponent =>
    "sacrifice it. When you do, you control target opponent during their next turn"
  | .planFinishExileTopCast =>
    "sacrifice it. When you do, target opponent exiles the top five cards of their library. You may cast up to two spells from among the exiled cards without paying their mana costs"
  | .planFinishCreateRobots n =>
    s!"sacrifice it and create {englishNumber n} 2/2 colorless Robot Villain artifact creature tokens"
  | .planFinishDividedDamage n =>
    s!"sacrifice it. When you do, it deals {n} damage divided as you choose among one or two targets"
  | .planFinishIndestructibleOnTarget =>
    "sacrifice it. When you do, put an indestructible counter on target creature you control"
  | .drawAndLoseLife1 =>
    "you draw a card and lose 1 life"
  | .onEnchanted action =>
    PermanentAction.toNotation action "enchanted creature"
  | .attachThen action =>
    s!"attach it to {noun}. {PermanentAction.toNotation action "that creature" (sentence := true)}"
  | .exileOtherCopyEnchanted =>
    "exile up to one target creature other than enchanted creature until this Aura leaves the battlefield. Enchanted creature becomes a copy of that creature until this Aura leaves the battlefield"
  | .exileUntilNextEndStep =>
    s!"exile up to one {noun}. Return that card to the battlefield under its owner's control at the beginning of the next end step"
  | .tapOrUntapNonland =>
    "choose one — • Tap target nonland permanent. • Untap target nonland permanent"
  | .createFoodOrTreasure =>
    "create a Food token or a Treasure token"
  | .villainIfGyElseMill =>
    "create a tapped 2/1 black Villain creature token with menace if there are two or more creature cards in your graveyard. Otherwise, mill two cards"
  | .drawMayPutLandTapped =>
    "draw a card, then you may put a land card from your hand onto the battlefield tapped"
  | .drawGainLifeIfAnotherHero =>
    "draw a card. If you control another Hero, you gain 2 life"
  | .plusOneOrTwoIfAnotherHero =>
    "put a +1/+1 counter on target creature. If that creature is another Hero, put two +1/+1 counters on it instead"
  | .maySacArtifactOrDiscardDraw =>
    "you may sacrifice an artifact or discard a card. If you do, draw a card"
  | .targetOpponentDiscards n =>
    s!"{noun} discards {cardPhrase n}"
  | .pumpTargetBySourcePower =>
    s!"{noun} gets +X/+0 until end of turn, where X is this creature's power"
  | .createAlienPerInvasion =>
    "create a 1/1 red Alien creature token with haste and \"This token attacks each combat if able.\" Put a +1/+1 counter on it for each invasion counter on this enchantment, then put an invasion counter on this enchantment"
  | .mayPutArtifactAttachEquipment =>
    "you may put an artifact card from your hand onto the battlefield. If it's an Equipment, attach it to this creature"
  | .fightUpToOne =>
    "this fights up to one other target creature"
  | .returnToOwnerHand =>
    s!"return up to one {noun} to its owner's hand"
  | .createZabu =>
    "create Zabu, a legendary 2/2 green Cat creature token with \"Landfall — Whenever a land you control enters, put a +1/+1 counter on Zabu.\""
  | .oppCreatesTheVoid =>
    s!"{noun} creates The Void, a legendary 5/5 black Horror Villain creature token with flying, indestructible, and \"The Void attacks each combat if able.\""
  | .createSturdyShieldAttach =>
    "create a colorless Equipment artifact token named Sturdy Shield with \"Equipped creature gets +1/+2\" and equip {2}. Attach it to this creature"
  | .exileGyPlayUntilNextTurn =>
    s!"exile {noun}. {playThatCardUntilNextTurnPhrase}"
  | .returnGyPermanentThisTurn =>
    s!"choose {noun} that was put there from anywhere this turn. Return it to your hand"
  | .tapCantUntapWhileControl =>
    s!"tap {noun}. That creature can't become untapped for as long as you control this creature"
  | .maySacAnotherThenDestroyOppNonland =>
    "you may sacrifice another creature. When you do, destroy target nonland permanent an opponent controls"
  | .maySacOrDiscardNonlandThenDamage =>
    "you may sacrifice an artifact or discard a nonland card. When you do, this deals 2 damage to any target"
  | .revealHandExileUntilLeaves =>
    "choose target opponent and up to one target creature they control. They reveal their hand. You may exile a nonland card from their hand or the chosen creature until this leaves the battlefield"
  | .plusOnesOrReturnArtEnch =>
    "choose one — • Put a +1/+1 counter on each of up to two target creatures. • Return target artifact or enchantment card from your graveyard to your hand"
  | .chooseUpToXModes =>
    "choose up to X — • Discard a card, then draw a card. • Target opponent loses 2 life. • Destroy target token. • Each player sacrifices a creature of their choice"
  | .mayTapThenGrantIndestructible =>
    "you may tap this creature. When you do, another target nonattacking creature you control gains indestructible until end of turn"
  | .tapLoseAbilitiesWhileSource =>
    "tap up to one target creature. It loses all abilities for as long as this remains on the battlefield"
  | .revealDiscardFromHand =>
    s!"{noun} reveals a number of cards from their hand equal to one plus the number of creature cards in your graveyard. You choose one of them. That player discards that card"
  | .createRedwing =>
    "create Redwing, a legendary 1/1 blue Bird Scout creature token with flying and \"Whenever Redwing attacks, surveil 1.\""
  | .step .enchantedControllerDraws =>
    "At the beginning of the upkeep of enchanted creature's controller, that player draws a card."
  | .step .drawToTen =>
    "At the beginning of your end step, if you have fewer than ten cards in hand, draw cards equal to the difference."
  | .step .copyAbsorbingMan =>
    "At the beginning of your first main phase, until your next turn, Absorbing Man becomes a copy of up to one target artifact, non-Aura enchantment, or land, except his name is Absorbing Man, he's a legendary 4/4 Human Villain creature in addition to his other types, and he has vigilance."
  | .step .hydeChoose =>
    "At the beginning of your upkeep, choose one — • Put a +1/+1 counter on Mister Hyde. • Remove a counter from a creature you control. If you do, draw a card."
  | .step .copyTaskmaster =>
    "Photographic Reflexes — At the beginning of your first main phase, until your next turn, Taskmaster becomes a copy of up to one target creature on the battlefield or creature card in a graveyard, except his name is Taskmaster, Mercenary Mimic and he's a legendary Human Mercenary Villain creature."
  | .step .harnessedFlicker =>
    "∞ — At the beginning of your end step, exile up to one other target nonland permanent you control, then return that card to the battlefield under its owner's control."
  | .death .hellcatReturn =>
    "When Hellcat dies, return her to the battlefield under her owner's control with a +1/+1 counter on her. She loses all abilities and gains haste."
  | .death .villainReturnAsHero =>
    "Whenever a Villain you control dies, return it to the battlefield under its owner's control with a finality counter on it. That creature is a Hero in addition to its other types."
  | .death .attackingReturnHand =>
    "Whenever an attacking creature you control dies, return that card to its owner's hand."
  | .death .deathtouchOppSac =>
    "Whenever another creature you control with deathtouch dies, each opponent sacrifices a nontoken creature of their choice."
  | .thisAttack .mayPayPlusOne =>
    "Whenever Ant-Man attacks, you may pay {1}. When you do, put a +1/+1 counter on target creature."
  | .thisAttack .payReturnAttacking =>
    "Whenever Grim Reaper attacks, you may pay {3}{B}. When you do, return target creature card from your graveyard to the battlefield tapped and attacking with a finality counter on it."
  | .thisAttack .ifArtifactEnteredDraw =>
    "Whenever Iron Man attacks, if an artifact entered the battlefield under your control this turn, draw a card."
  | .thisAttack .blinkNontoken =>
    "Whenever The Mighty Thor attacks, exile up to one target nontoken artifact or creature, then return that card to the battlefield tapped under its owner's control."
  | .thisAttack .equippedDrain =>
    "Whenever Whiplash attacks, if he's equipped, each opponent loses X life and you gain X life, where X is the number of Equipment attached to him."
  | .thisAttack .drawIfPower4 =>
    "Cybernetic Senses — Whenever Viv Vision attacks, draw a card if her power is 4 or greater."
  | .thisAttack .attacksAlonePlus2Indestructible =>
    "Unbreakable Skin — Whenever Luke Cage attacks alone, he gets +2/+0 and gains indestructible until end of turn."
  | .enterOrAttack .copyKeywords =>
    "Whenever Super-Adaptoid enters or attacks, choose another target creature. If that creature has haste and Super-Adaptoid doesn't, put a haste counter on Super-Adaptoid. Do the same for flying, first strike, double strike, deathtouch, indestructible, lifelink, menace, reach, trample, and vigilance."
  | .enterOrAttack .createSquirrel =>
    "Do You Like Squirrels? — Whenever The Unbeatable Squirrel Girl enters or attacks, create a 1/1 green Squirrel creature token."
  | .watch .combatDamageExileUntilNonland =>
    "Whenever Black Widow deals combat damage to a player, that player exiles cards from the top of their library until they exile a nonland card. You may put a +1/+1 counter on Black Widow. If you don't, you may cast the exiled nonland card until end of turn and mana of any type can be spent to cast that spell."
  | .watch .attacksAloneDrain =>
    "Whenever a creature you control attacks alone, target opponent loses 1 life and you gain 1 life."
  | .watch .attacksAloneFirstStrikeMenace =>
    "Whenever a creature you control attacks alone, it gains first strike and menace until end of turn."
  | .watch .firstTapUntap =>
    "Whenever a creature you control becomes tapped during your turn, if it's the first time that creature has become tapped this turn, untap it."
  | .watch .sheHulkRedirectOnce =>
    "Whenever a creature you control is dealt damage, you may have The Sensational She-Hulk deal that much damage to any target. Do this only once each turn."
  | .watch .speedballTargeted =>
    "Whenever a player casts a spell that targets Speedball, he gets +2/+2 until end of turn. You may choose new targets for that spell."
  | .watch .anyPlayerSecondDraw =>
    "Whenever a player draws their second card each turn, you draw a card."
  | .watch .youTargetDrawOnce =>
    "Whenever a player or permanent becomes the target of an ability you control, draw a card. This ability triggers only once each turn."
  | .watch .villainOrArtifactDamage =>
    "Whenever another Villain and/or artifact you control enters, this creature deals 1 damage to target opponent."
  | .watch .villainConniveOnce =>
    "Whenever another Villain you control enters, you may have it connive. Do this only once each turn."
  | .watch .villainPlusOneDamageOnce =>
    "Whenever another Villain you control enters, put a +1/+1 counter on Crossbones. He deals 2 damage to each opponent. This ability triggers only once each turn."
  | .watch .villainAttachEquipment =>
    "Whenever another Villain you control enters, attach up to one target Equipment you control to target creature you control."
  | .watch .villainPlusOneLifelink =>
    "Whenever another Villain you control enters, Yellowjacket gets +1/+0 and gains lifelink until end of turn."
  | .watch .hulklingCompare =>
    "Whenever another creature you control enters, if it has greater power or toughness than Hulkling, put a +1/+1 counter on Hulkling."
  | .watch .justiceBounce =>
    "Whenever another nonland permanent you control is returned to its owner's hand, put a +1/+1 counter on Justice."
  | .watch .nontokenHeroModal =>
    "Whenever another nontoken Hero you control enters, choose one — • Create a 1/1 white Soldier creature token. • Creatures you control get +1/+1 until end of turn."
  | .watch .ultronCopy =>
    "Whenever another nontoken artifact you control enters, you may pay {2}. If you do, create a token that's a copy of it. If the token isn't a creature, it becomes a 2/2 Robot Villain creature in addition to its other types."
  | .watch .enchantedAttachEquipment =>
    "Whenever enchanted creature attacks or blocks, attach any number of target Equipment you control to it."
  | .watch .equippedAttacksAloneUntapScry =>
    "Whenever equipped creature attacks alone, untap it and scry 1."
  | .watch .equippedAttacksTap =>
    "Whenever equipped creature attacks, tap target creature defending player controls."
  | .watch .equippedTappedDamage =>
    "Whenever equipped creature becomes tapped, it deals 1 damage to each opponent."
  | .watch .heroesDamagePlusTwo =>
    "Whenever one or more Heroes you control deal damage to a player, put two +1/+1 counters on The Thing."
  | .watch .merfolkAttackDraw =>
    "Whenever one or more Merfolk you control attack a player, draw a card."
  | .watch .tokensEnterMayDraw =>
    "Whenever one or more tokens you control enter, you may draw a card."
  | .watch .hawkeyeModes =>
    "Trick Arrows — Whenever Hawkeye becomes tapped, you may pay {1} up to three times. When you do, choose up to that many — • Net — Target creature can't block this turn. • Explosive — Hawkeye deals 2 damage to target player. • Boomerang — Discard a card, then draw a card."
  | .watch .redHulk =>
    "Enrage — Whenever Red Hulk is dealt damage, put a +1/+1 counter on him. When you do, he deals damage equal to the number of +1/+1 counters on him to any other target."
  | .watch .hulk =>
    "Enrage — Whenever The Incredible Hulk is dealt damage, put a +1/+1 counter on him. If he's attacking, untap him and there is an additional combat phase after this phase."
  | .youAttacking .pay2LifeToughness =>
    "Whenever you attack, you may pay 2 life. If you do, until end of turn, creatures you control with toughness greater than their power assign combat damage equal to their toughness rather than their power."
  | .youAttacking .exileTopHeroPump =>
    "Whenever you attack, you may exile the top card of your library. If that card is a Hero card, Daredevil gets +2/+1 until end of turn. You may play that card this turn."
  | .youAttacking .lookSixCast =>
    s!"Whenever you attack, look at the top six cards of your library. You may cast a spell from among them with mana value less than or equal to the greatest power among attacking creatures you control without paying its mana cost. {restOnBottomRandomPhrase}."
  | .casting .villainToken =>
    "Whenever you cast a Villain spell, create a 2/1 black Villain creature token with menace."
  | .casting .merfolkFromBlue =>
    "Whenever you cast a noncreature spell with one or more blue mana symbols in its mana cost, create that many 1/1 blue Merfolk creature tokens."
  | .casting .mayPayHasteUnblockable =>
    "Whenever you cast a noncreature spell, you may pay {1}. When you do, target creature with haste can't be blocked this turn except by creatures with haste."
  | .casting .plusOneEachOther =>
    "Whenever you cast a noncreature spell, put a +1/+1 counter on each other creature you control."
  | .casting .exileFlicker =>
    "Whenever you cast a noncreature spell, exile another target nonland, nontoken permanent. Return that card to the battlefield under its owner's control at the beginning of the next end step."
  | .casting .visionModes =>
    "Whenever you cast a noncreature spell, choose one that hasn't been chosen this turn — • Solar Beam — The Vision gains double strike until end of turn. • Density Control — The Vision gains indestructible until end of turn. • Technopathy — Draw a card."
  | .casting .damageEqualMv =>
    "Whenever you cast a noncreature spell, Thor deals damage equal to that spell's mana value to any target."
  | .casting .drawPowerEqualHand =>
    "Whenever you cast a spell that targets a creature you control, draw a card. Until end of turn, Ms. Marvel gains \"Ms. Marvel's base power is equal to the number of cards in your hand.\""
  | .casting .plusOneThis =>
    "Whenever you cast a spell that targets a creature you control, put a +1/+1 counter on Mockingbird."
  | .casting .plusOneScry =>
    "Whenever you cast a spell that targets a creature you control, put a +1/+1 counter on Colleen Wing. Scry 1."
  | .casting .ironFistTap =>
    "Whenever you cast a spell that targets a creature you control, Iron Fist gains \"{T}: Iron Fist deals damage equal to his power to any other target\" until end of turn."
  | .casting .targetsGainFlying =>
    "Whenever you cast a spell that targets one or more creatures, those creatures gain flying until end of turn."
  | .casting .copyIfArtifactOrLand =>
    "Whenever you cast an instant or sorcery spell that targets an artifact or land, copy that spell. You may choose new targets for the copy. Put two +1/+1 counters on Fin Fang Foom."
  | .casting .tapCreatureOrLand =>
    "Seismic Takedown — Whenever you cast a noncreature spell, tap target creature or land."
  | .resource .discardExilePlay =>
    "Whenever you discard a card, you may exile that card from your graveyard. If you do, until the end of your next turn, you may play that card."
  | .resource .drawIfAnotherHeroDamage =>
    "Whenever you draw a card, if you control another Hero, Human Torch deals 1 damage to target opponent."
  | .resource .secondDrawBecome66 =>
    "Whenever you draw your second card each turn, until end of turn, Moon Girl and Devil Dinosaur's base power and toughness become 6/6 and they gain trample."
  | .resource .secondDrawPlusOneTarget =>
    "Whenever you draw your second card each turn, put a +1/+1 counter on target creature."
  | .resource .secondDrawDrain =>
    "Whenever you draw your second card each turn, each opponent loses 1 life and you gain 1 life."
  | .resource .gainLifePlusOnes =>
    "Whenever you gain life, choose up to that many target creatures you control. Put a +1/+1 counter on each of them."
  | .resource .plusOneCreateInsectOnce =>
    "Whenever you put a +1/+1 counter on a creature, create a 1/1 green Insect creature token. This ability triggers only once each turn."
  | .resource .plusOneOnThisOnce =>
    "Whenever you put a +1/+1 counter on another creature, put a +1/+1 counter on this creature. This ability triggers only once each turn."
  | .resource .plusOneOnHeroesCreateWall =>
    "Whenever you put one or more +1/+1 counters on one or more other Heroes you control, you may create a 0/4 colorless Wall creature token with defender."

/-- True when this trigger fires only once each turn. -/
def onceEachTurn (ab : TriggeredAbility) : Bool :=
  ab.timing.onceEachTurn

/-- True when the optional action may be chosen only once each turn (MSH 69). -/
def optionalOnceEachTurn (ab : TriggeredAbility) : Bool :=
  ab.timing.optionalOnceEachTurn

/-- Intervening power-at-most threshold for another creature entering. -/
def anotherCreaturePowerAtMost? (ab : TriggeredAbility) : Option Int :=
  ab.timing.anotherCreaturePowerAtMost

/-- Sentence whose printed “When/Whenever …” lead-in differs from the generic
`eventPrefix` (a card name, an ability word, or a more specific subject) but
whose effect clause is the shared `resolutionPhrase`. -/
def leadInSentence (ab : TriggeredAbility) (lead : String) : String :=
  s!"{lead}, {resolutionPhrase ab.timing}."

def toNotation (ab : TriggeredAbility) : String :=
  match ab with
  | .triggered w e opts =>
    match w, e.asTrigger?, opts with
    | .enter, some .bolgMaySacrifice, _ =>
      leadInSentence ab "When Bolg enters"
    | .combatDamageToPlayer, some .createTreasuresEqualDamagedPlayerArtifacts, _ =>
      leadInSentence ab "Whenever this creature deals combat damage to a player"
    | .enterOrOpponentDrawsExceptFirst, some .deal1ThenAmassOrcs, _ =>
    "When this creature enters and whenever an opponent draws a card except the first one they draw in each of their draw steps, this creature deals 1 damage to any target. Then amass Orcs 1."
    | .opponentDrawsSecond, some (.createTokens .treasure 1), _ =>
    "Whenever an opponent draws their second card each turn, you create a Treasure token."
    | .youAttackWithTotalPower, some (.untapAttackersExtraCombat n), _ =>
      leadInSentence ab
        s!"Whenever you attack with creatures with total power {n} or greater for the first time each turn"
    | .anotherCreatureYouControlEnters, some .allianceMode, _ =>
      leadInSentence ab "Alliance — Whenever another creature you control enters"
    | .enter, some .destroyOtherAmassControllerPower, _ =>
    "When Azog enters, destroy up to one other target creature. Its controller amasses Goblins X, where X is that creature's power. If you controlled that creature, draw a card."
    | .combatDamageToPlayerOrBattle, some (.createTokens .treasure 2), { watchedSubtype := some "Dwarf", .. } =>
      leadInSentence ab "Whenever a Dwarf you control deals combat damage to a player or battle"
    | (.youCastColor .red), some (.damageEachOpponent 3), _ =>
    "Whenever you cast a red spell, Aragorn deals 3 damage to target opponent."
    | .enter, some .returnCreatureFromGyToHand, _ =>
    "When this enchantment enters, return target creature card from your graveyard to your hand."
    | .thisOrAnotherSubtypeEnters, some .discardHandDrawDamageIfStory, { thisOrAnotherSubtype := some "Dwarf", .. } =>
    "Whenever Balin or another Dwarf you control enters, you may discard your hand. Draw X cards, where X is the number of cards discarded this way. If you have an enduring story, Balin deals X damage to each opponent."
    | .attack, some .castFromGyArtifactInstantSorcery, _ =>
      leadInSentence ab "Whenever Bilbo attacks"
    | .enter, some .createAxeAttach, _ =>
      leadInSentence ab "When Dáin enters"
    | .attack, some .equippedAttackersGainDoubleStrike, _ =>
      leadInSentence ab "Whenever Dáin attacks"
    | .enter, some .tapEnchantedRemoveCounters, _ =>
      leadInSentence ab "When this Aura enters"
    | .dies, some (.revealTopPutRandomCreature _), _ =>
      leadInSentence ab "When this artifact is put into a graveyard from the battlefield"
    | .yourBeginCombat, some .beginCombatIfDrawnTwoPump, _ =>
    "At the beginning of combat on your turn, if you've drawn two or more cards this turn, another target creature you control gets +3/+0 and gains first strike until end of turn."
    | .enter, some .honePerOppAttach, _ =>
    "When Sting enters, put a hone counter on Sting for each creature target opponent controls. Attach Sting to up to one target creature you control."
    | .enter, some .copySelfNonlegendary, _ =>
      leadInSentence ab "When The Notary Hobbits enter"
    | .enter, some .attachEquipmentThenFight, _ =>
      leadInSentence ab "When Thorin enters"
    | .anotherCreatureYouControlEnters, some (.drawThenDiscard 2), { thisOrAnotherSubtype := some "Elf", .. } =>
    "Whenever another legendary Elf you control enters, draw two cards, then discard a card."
    | .dies, some .returnAsArtifact, _ =>
      leadInSentence ab "When Tom, Bert, and William die"
    | .anotherCreatureYouControlEnters, some (.onSource (.plusOne 2)), { thisOrAnotherSubtype := some "Wolf", .. } =>
    "Whenever another Wolf you control enters, put two +1/+1 counters on Chief of the Wilds."
    | .landYouControlEnters, some .drawPlusOneSource, _ =>
    "Landfall — Whenever a land you control enters, draw a card and put a +1/+1 counter on Gandalf."
    | .enter, some .exileLandsThenReturnTapped, _ =>
      leadInSentence ab "When Gandalf enters"
    | .combatDamageToPlayer, some .grimaImpulse, _ =>
      leadInSentence ab "Whenever Gríma deals combat damage to a player"
    | .yourEndStep, some .palantir, _ =>
    "At the beginning of your end step, put an influence counter on Palantír of Orthanc and scry 2. Then target opponent may have you draw a card. If that player doesn't, you mill X cards, where X is the number of influence counters on Palantír of Orthanc, and that player loses life equal to the total mana value of those cards."
    | .sourceDealtNoncombatDamage, some .treasuresEqualLastKnown, _ =>
      leadInSentence ab "Whenever Smaug is dealt noncombat damage"
    | .enter, some .protectionEverything, _ =>
      leadInSentence ab "When The One Ring enters"
    | .yourUpkeep, some .loseLifePerBurden, _ =>
    "At the beginning of your upkeep, you lose 1 life for each burden counter on The One Ring."
    | .landYouControlEnters, some .payReturnFromGy, _ =>
      leadInSentence ab "Landfall — Whenever a land you control enters"
    | .youPutCountersOnGoblinOrcArmy, some (.damageTargetOpponent 2), _ =>
    "Whenever you put one or more counters on a Goblin, Orc, or Army you control, The Great Goblin deals 2 damage to target opponent."
    | .enter, some .connive, _ =>
      leadInSentence ab "When this creature enters"
    | .eachEndStep, some (.drawIfAttackedOrEnteredSubtype subtype), _ =>
    let a := if subtype == "Hero" then "a Hero" else s!"a {subtype}"
    s!"At the beginning of each end step, if you attacked with {a} this turn or {a} entered the battlefield under your control this turn, draw a card."
    | .attack, some (.othersOfSubtypeGetEqualSourceToughness subtype), _ =>
    s!"Whenever this attacks, each other {subtype} you control gets +X/+X until end of turn, where X is this toughness."
    | (.youCastColorFromHand color), some .connive, _ =>
    s!"Whenever you cast a {color} spell from your hand, this connives."
    | .sourceDealtDamage, some .plusOneOnSource, _ =>
    "Whenever this is dealt damage, put a +1/+1 counter on it."
    | .enter, some (.attachTo .creatureYouControl), _ =>
      leadInSentence ab "When this Equipment enters"
    | .enter, some (.surveil n), _ =>
    s!"When this permanent enters, surveil {n}."
    | .enter, some (.onEnchanted _), _ =>
      leadInSentence ab "When this Aura enters"
    | .enter, some (.attachThen _), _ =>
      leadInSentence ab "When this Equipment enters"
    | .enter, some .exileOtherCopyEnchanted, _ =>
      leadInSentence ab "When this Aura enters"
    | .enter, some .exileUntilNextEndStep, _ =>
      leadInSentence ab "When this Vehicle enters"
    | .enter, some .tapOrUntapNonland, _ =>
      leadInSentence ab "When this creature enters"
    | .enter, some .createFoodOrTreasure, _ =>
      leadInSentence ab "When this creature enters"
    | .enter, some .villainIfGyElseMill, _ =>
      leadInSentence ab "When this creature enters"
    | .enter, some .drawMayPutLandTapped, _ =>
      leadInSentence ab "When this creature enters"
    | .enter, some .drawGainLifeIfAnotherHero, _ =>
      leadInSentence ab "When this creature enters"
    | .enter, some .plusOneOrTwoIfAnotherHero, _ =>
      leadInSentence ab "When this creature enters"
    | .enter, some .maySacArtifactOrDiscardDraw, _ =>
      leadInSentence ab "When this creature enters"
    | .enter, some (.exileUntilLeaves .oppTappedCreature), _ =>
    "When this enchantment enters, exile target tapped creature an opponent controls until this enchantment leaves the battlefield."
    | .enter, some (.targetOpponentDiscards n), _ =>
    let cards := if n == 2 then "two cards" else cardPhrase n
    s!"When this enchantment enters, target opponent discards {cards}."
    | .enter, some (.enter (.dealDamageUpToOne n)), _ =>
    s!"When this permanent enters, it deals {n} damage to up to one target creature."
    | _, some (.step e), _ => resolutionPhrase { resolution := .step e }
    | _, some (.death e), _ => resolutionPhrase { resolution := .death e }
    | _, some (.thisAttack e), _ => resolutionPhrase { resolution := .thisAttack e }
    | _, some (.enterOrAttack e), _ =>
      resolutionPhrase { resolution := .enterOrAttack e }
    | _, some (.watch e), _ => resolutionPhrase { resolution := .watch e }
    | _, some (.youAttacking e), _ =>
      resolutionPhrase { resolution := .youAttacking e }
    | _, some (.casting e), _ => resolutionPhrase { resolution := .casting e }
    | _, some (.resource e), _ => resolutionPhrase { resolution := .resource e }

    | _, _, _ =>
    let t := ab.timing
    if t.events.contains .equippedAttacksAlone then
      "Whenever equipped creature attacks alone, you draw a card and you lose 1 life."
    else
      let once :=
        if t.onceEachTurn then " This ability triggers only once each turn." else ""
      s!"{eventPrefix t}{interveningClause t}, {resolutionPhrase t}.{once}"

instance : ToString TriggeredAbility where
  toString := toNotation

end TriggeredAbility

end Mtg.Engine
