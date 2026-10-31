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

/-- The options of this triggered ability. -/
def opts : TriggeredAbility → SharedTriggerOpts
  | .triggered _ _ o => o

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
  .triggered .enter (Effect.ofTrigger (.amass n))
def onDiesAmassGoblins (n : Nat) : TriggeredAbility :=
  .triggered .dies (Effect.ofTrigger (.amass n))
def onYouAttackAmassGoblins (n : Nat) : TriggeredAbility :=
  .triggered .youAttack (Effect.ofTrigger (.amass n))
def onCastNoncreatureAmassGoblins (n : Nat) : TriggeredAbility :=
  .triggered .youCastNoncreature (Effect.ofTrigger (.amass n))
def onEnterOrAttackAmassGoblins (n : Nat) : TriggeredAbility :=
  .triggered (.or .enter .attack) (Effect.ofTrigger (.amass n))
def onCreatureCardLeavesYourGyAmassGoblins (n : Nat) : TriggeredAbility :=
  .triggered .creatureCardLeavesYourGy (Effect.ofTrigger (.amass n))
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
  .triggered .enter (Effect.ofTrigger (.onPermanent .creature (.plusOne 1)))
def onEnterOrAttackPlusOneOnCreature : TriggeredAbility :=
  .triggered (.or .enter .attack) (Effect.ofTrigger (.onPermanent .creature (.plusOne 1)))
def onLandYouControlEntersPlusOnePlusOne : TriggeredAbility :=
  .triggered .landYouControlEnters (Effect.ofTrigger (.onPermanent .creatureYouControl (.plusOne 1)))
def onCombatPlusOneOnCreatureYouControl : TriggeredAbility :=
  .triggered .yourBeginCombat (Effect.ofTrigger (.onPermanent .creatureYouControl (.plusOne 1)))
def onEnterAttachToSubtype (subtype : String) : TriggeredAbility :=
  .triggered .enter (Effect.ofTrigger (.attachTo (.creatureYouControlSubtype (CardSubtype.ofOracleD subtype))))
def onEnterAttachToLegendary : TriggeredAbility :=
  .triggered .enter (Effect.ofTrigger (.attachTo .legendaryCreatureYouControl))
def onEnterAttachToCreatureYouControl : TriggeredAbility :=
  .triggered .enter (Effect.ofTrigger (.attachTo .creatureYouControl))
def onEnterTargetOpponentSacrificesCreature : TriggeredAbility :=
  .triggered .enter (Effect.ofTrigger .opponentSacrificesCreature)
def onEnterTargetOpponentSacrifices : TriggeredAbility :=
  onEnterTargetOpponentSacrificesCreature
def onDrawSecondPlusOne : TriggeredAbility :=
  .triggered .youDrawSecond (Effect.ofTrigger (.onSource (.plusOne 1)))
def onDrawPlusOne : TriggeredAbility :=
  .triggered .youDraw (Effect.ofTrigger (.onSource (.plusOne 1)))
def onGainLifePlusOne : TriggeredAbility :=
  .triggered .youGainLife (Effect.ofTrigger (.onSource (.plusOne 1)))
def onAnotherArtifactEntersPlusOne : TriggeredAbility :=
  .triggered .anotherArtifactEnters (Effect.ofTrigger (.onSource (.plusOne 1)))
def onYourBeginCombatFerociousPlusOne : TriggeredAbility :=
  .triggered .yourBeginCombat (Effect.ofTrigger (.onSource (.plusOne 1))) .ferocious
def onEquippedAttacksAloneDrawLoseLife : TriggeredAbility :=
  .triggered .equippedAttacksAlone Effect.seqDrawAndLoseLife
def onYouAttackFerociousDrawLoseLife : TriggeredAbility :=
  .triggered .youAttack Effect.seqDrawAndLoseLife .ferocious
def onCastWithTreasureDrawLoseLife : TriggeredAbility :=
  .triggered .youCastWithTreasure Effect.seqDrawAndLoseLife
def onYourEndStepDrawLoseLife : TriggeredAbility :=
  .triggered .yourEndStep Effect.seqDrawAndLoseLife
def onEnterConnive : TriggeredAbility :=
  .triggered .enter (Effect.ofTrigger .connive)
def onAttackConnive : TriggeredAbility :=
  .triggered .attack (Effect.ofTrigger .connive)
def onYouCastColorFromHandConnive (color : Color) : TriggeredAbility :=
  .triggered (.youCastColorFromHand color) (Effect.ofTrigger .connive)
def onEquippedCreatureYouControlAttacksConnive : TriggeredAbility :=
  .triggered .equippedCreatureYouControlAttacks (Effect.ofTrigger .connive)
def onCombatTargetYouControlConnives : TriggeredAbility :=
  .triggered .yourBeginCombat (Effect.ofTrigger (.connive (.target .creatureYouControl)))
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
  .triggered .enter (Effect.ofTrigger (.onPermanent .creature (.pump power toughness)))
def onDiesOppCreatureGets (power toughness : Int) : TriggeredAbility :=
  .triggered .dies (Effect.ofTrigger (.onPermanent .oppCreature (.pump power toughness)))
def onCastColorPump (color : Color) (power toughness : Int) : TriggeredAbility :=
  .triggered (.youCastColor color) (Effect.ofTrigger (.onPermanent .creature (.pump power toughness)))
def onLandYouControlEntersGets (power toughness : Int) : TriggeredAbility :=
  .triggered .landYouControlEnters (Effect.ofTrigger (.onSource (.pump power toughness)))
def onAttackFerociousSourceGets (power toughness : Int) : TriggeredAbility :=
  .triggered .attack (Effect.ofTrigger (.onSource (.pump power toughness))) .ferocious
def onAnotherElfYouControlEntersGets1 : TriggeredAbility :=
  .triggered .anotherElfYouControlEnters (Effect.ofTrigger (.onSource (.pump 1 1)))
def onArtifactYouControlEntersDrawOnce : TriggeredAbility :=
  .triggered .artifactYouControlEnters (Effect.ofTrigger (.draw 1)) .once
def onActivateCreatureAbilityDrawOnce : TriggeredAbility :=
  .triggered .youActivateCreatureAbility (Effect.ofTrigger (.draw 1)) .once
def onAnotherSubtypeOrEquipmentEntersDrawOnce (subtype : String) : TriggeredAbility :=
  .triggered .anotherSubtypeOrEquipmentEnters (Effect.ofTrigger (.draw 1))
    { onceEachTurn := true, anotherSubtypeOrEquipment := CardSubtype.ofOracle? subtype }
def onEachEndStepDrawIfGainedLife (n : Nat) : TriggeredAbility :=
  .triggered .eachEndStep (Effect.ofTrigger (.draw 1)) { gainedLifeAtLeast := some n }
def onThisOrNontokenSubtypeEntersCreateTokens (subtype : String) (kind : TokenKind)
    (n : Nat) : TriggeredAbility :=
  .triggered .thisOrNontokenSubtypeEnters (Effect.ofTrigger (.createTokens kind n))
    { thisOrNontokenSubtype := CardSubtype.ofOracle? subtype }
def onThisOrAnotherSubtypeEntersCreateTokens (subtype : String) (kind : TokenKind)
    (n : Nat) : TriggeredAbility :=
  .triggered .thisOrAnotherSubtypeEnters (Effect.ofTrigger (.createTokens kind n))
    { thisOrAnotherSubtype := CardSubtype.ofOracle? subtype }
def onSubtypeYouControlCombatDamageCreateTokens (subtype : String) (kind : TokenKind)
    (n : Nat) : TriggeredAbility :=
  .triggered .combatDamageToPlayerOrBattle (Effect.ofTrigger (.createTokens kind n))
    { watchedSubtype := CardSubtype.ofOracle? subtype }
def onOpponentDrawsSecondCreateTreasure : TriggeredAbility :=
  .triggered .opponentDrawsSecond (Effect.ofTrigger (.createTokens .treasure 1))
def onOpponentCastsFirstNoncreatureRecruit : TriggeredAbility :=
  .triggered .opponentCastsFirstNoncreature (Effect.ofTrigger (.recruit .you))
def onCastColorDamageOpponent (color : Color) (n : Nat) : TriggeredAbility :=
  .triggered (.youCastColor color) (Effect.ofTrigger (.damageEachOpponent n))
def onCastGreenOrForestEntersPlusOne : TriggeredAbility :=
  .triggered (.or .youCastGreen .forestYouControlEnters)
    (Effect.ofTrigger (.onPermanent .creatureYouControl (.plusOne 1)))
def onAttackOtherGets2AndTrample : TriggeredAbility :=
  .triggered .attack (Effect.ofTrigger (.onPermanent .anotherCreatureYouControl (.pumpAndTrample 2 0)))
def onEnterMayDiscardDraw (n : Nat) : TriggeredAbility :=
  .triggered .enter (Effect.ofTrigger (.mayTo .discard (.draw n)))
def onCastInstantOrSorceryDealDamageToEachOpponent (amount : Nat) : TriggeredAbility :=
  .triggered .youCastInstantOrSorcery (Effect.ofTrigger (.damageEachOpponent amount)) .noTarget
def onEnterEachOpponentDiscards : TriggeredAbility :=
  .triggered .enter (Effect.ofTrigger .opponentDiscards)
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
    { thisOrAnotherSubtype := CardSubtype.ofOracle? subtype }
def onOpponentCastsAmassOrcs (n : Nat) : TriggeredAbility :=
  .triggered .opponentCastsSpell (Effect.ofTrigger (.amass n .orc))
def onCreatureYouControlAttacksAloneInvestigate : TriggeredAbility :=
  .triggered .creatureYouControlAttacksAlone (Effect.ofTrigger .investigate)
def onCreatureYouControlAttacksAlonePump (power toughness : Int) : TriggeredAbility :=
  .triggered .creatureYouControlAttacksAlone (Effect.ofTrigger (.pumpCause power toughness))
def onEnterTargetOpponentDiscards (n : Nat) : TriggeredAbility :=
  .triggered .enter (Effect.ofTrigger (.opponentDiscards n .target))
def onEquipmentYouControlEntersDraw : TriggeredAbility :=
  .triggered .equipmentYouControlEnters (Effect.ofTrigger (.draw 1))
def onEnterSearchForest : TriggeredAbility :=
  .triggered .enter (Effect.ofTrigger .searchLibrary)
def onEnterSearchBasicToHand : TriggeredAbility :=
  .triggered .enter (Effect.ofTrigger .searchBasicLandToHand)
def onEnterEachPlayerSacrificesCreature : TriggeredAbility :=
  .triggered .enter (Effect.ofTrigger .eachPlayerSacrificesCreature)
def onEnterMayExileAnotherCreature : TriggeredAbility :=
  .triggered .enter (Effect.ofTrigger (.exileTarget .anotherCreature)) { allowsZeroTargets := true }
def onEnterReturnCreatureFromGyToHand : TriggeredAbility :=
  .triggered .enter (Effect.ofTrigger .returnCreatureFromGyToHand)
def onCombatDamageToPlayerLoot : TriggeredAbility :=
  .triggered .combatDamageToPlayer (Effect.seqDrawThenDiscard 1)
def onAttackFerociousPlusOneEach : TriggeredAbility :=
  .triggered .attack (Effect.ofTrigger .plusOneEachYouControl) .ferocious
def onAttackFerociousSourceGetsAndTeamTrample (power : Int) : TriggeredAbility :=
  .triggered .attack (Effect.seqSourceGetsAndTeamTrample power) .ferocious
def onEnterOrAttackHoneEachEquipment : TriggeredAbility :=
  .triggered (.or .enter .attack) (Effect.ofTrigger .honeEachEquipment)
def onEnterOrAttackPlusOneEachOtherGainLife : TriggeredAbility :=
  .triggered (.or .enter .attack) (Effect.ofTrigger .plusOneEachOtherGainLife)
def onLandYouControlEntersBecomePT (power toughness : Int) : TriggeredAbility :=
  .triggered .landYouControlEnters (Effect.ofTrigger (.becomePT power toughness))
def onCastNoncreaturePumpAndDamageOpponents (n : Nat) : TriggeredAbility :=
  .triggered .youCastNoncreature (Effect.seqPumpAndDamageOpponents n)
def onDrawSecondPlusOneLifelink : TriggeredAbility :=
  .triggered .youDrawSecond (Effect.seqPlusOneAndLifelink .creature)
def onYouAttackPumpTargetPerPlains : TriggeredAbility :=
  .triggered .youAttack (Effect.ofTrigger .pumpTargetPerPlains)
def onAnotherLegendarySubtypeEntersLoot (subtype : String) : TriggeredAbility :=
  .triggered .anotherCreatureYouControlEnters (Effect.seqDrawThenDiscard 2)
    { thisOrAnotherSubtype := CardSubtype.ofOracle? subtype, anotherSupertype := some .legendary }
def onRingTemptsMayDiscardDraw (n : Nat) : TriggeredAbility :=
  .triggered .theRingTemptsYou (Effect.ofTrigger (.mayDiscardHandDraw n))
def onScryPumpSelfForEachLookedAt : TriggeredAbility :=
  .triggered .youScry (Effect.ofTrigger .pumpByLookedAt)
def onScryPumpAndUnblockableOnce : TriggeredAbility :=
  .triggered .youScry Effect.seqPumpAndUnblockable .once
def onAttackPumpByGreatestPower : TriggeredAbility :=
  .triggered .attack (Effect.ofTrigger .pumpGreatestPower)
def onBecomesBlockedDeal1ToBlockers : TriggeredAbility :=
  .triggered .becomesBlocked (Effect.ofTrigger (.damageBlockers 1))
def onAttackPumpForEachOtherCreature : TriggeredAbility :=
  .triggered .attack (Effect.ofTrigger .pumpForEachOtherCreature)
def onAttackWithTwoOrMoreGrantFlying : TriggeredAbility :=
  .triggered .youAttackWithTwoOrMore
    (Effect.ofTrigger (.onPermanent .attackingCreatureWithoutFlying (.grantKeywords Keyword.flying)))
def onLeaveReturnExiled : TriggeredAbility :=
  .triggered .leaving (Effect.ofTrigger .returnLinkedExile)
def onEnterCreateThenAttach (kind : TokenKind) : TriggeredAbility :=
  .triggered .enter (Effect.ofTrigger (.createThenAttach kind))
def onEnterAmassThenAttach (n : Nat) : TriggeredAbility :=
  .triggered .enter (Effect.ofTrigger (.amass n (attachSource := true)))
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
  .triggered .enter (Effect.ofTrigger (.createAxe (attach := true)))
def onDiesAmassGoblinsEqualPower : TriggeredAbility :=
  .triggered .dies (Effect.ofTrigger (.amass 0 (amount := .sourcePower)))
def onLandYouControlEntersPayReturnFromGy : TriggeredAbility :=
  .triggered .landYouControlEnters (Effect.ofTrigger .payReturnFromGy)
def onYouSacrificeTokenOppLosesLife : TriggeredAbility :=
  .triggered .youSacrificeToken (Effect.ofTrigger (.targetOpponentLosesLife 1))
def onLandYouControlEntersPlusOneVigilance : TriggeredAbility :=
  .triggered .landYouControlEnters (Effect.seqPlusOneVigilance 2)
def onCastNoncreatureMayDrawXDiscard2 : TriggeredAbility :=
  .triggered .youCastNoncreature (Effect.ofTrigger (.may (.drawXDiscard 2)))
def onLandYouControlEntersDrawPlusOneSource : TriggeredAbility :=
  .triggered .landYouControlEnters Effect.seqDrawPlusOneSource
def onArmyCombatDamageRingTempts : TriggeredAbility :=
  .triggered .armyYouControlCombatDamage (Effect.ofTrigger .ringTempts)
def onAttackSetOtherBasePT : TriggeredAbility :=
  .triggered .attack (Effect.ofTrigger .setOtherBasePT)
def onEnterOrAttackReturnElfGainLife : TriggeredAbility :=
  .triggered (.or .enter .attack) (Effect.ofTrigger .returnElfGainLife)
def onDiesDealDamageEqualToPowerToOppCreature : TriggeredAbility :=
  .triggered .dies (Effect.ofTrigger .damageFromLastKnownPower)
def onEnterExileOppGyCardOppsLoseLife (life : Nat) : TriggeredAbility :=
  .triggered .enter (Effect.seqExileOppGyCardOppsLoseLife life)
def onEnterCreaturesYouControlGetAndFirstStrike (power : Int) : TriggeredAbility :=
  .triggered .enter (Effect.seqCreaturesPumpAndFirstStrike power)
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
  .triggered .enter (Effect.seqUntapPlusOneIfSubtype subtype)
def onEnterDestroyOppArtifactsEnchantmentsGainLife : TriggeredAbility :=
  .triggered .enter (Effect.ofTrigger .destroyOppArtifactsEnchantmentsGainLife)
def onAttackDamageEqualSubtypeToEachOpponent (subtype : String) : TriggeredAbility :=
  .triggered .attack (Effect.ofTrigger (.damageEqualSubtypeToEachOpponent (CardSubtype.ofOracleD subtype)))
def onAttackDamageEqualTreasures : TriggeredAbility :=
  .triggered .attack (Effect.ofTrigger .damageEqualTreasures)
def onPlayerCastsSecondSpellLoseLifeCreateTreasure : TriggeredAbility :=
  .triggered .anyPlayerCastsSecondSpell Effect.seqLoseLifeCreateTreasure
def onEnterDealDamageDestroyIfSubtype (n : Nat) (subtype : String) : TriggeredAbility :=
  .triggered .enter (Effect.ofTrigger (.dealDamageDestroyIfSubtype n (CardSubtype.ofOracleD subtype)))
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
  .triggered .eachBeginCombat (Effect.ofTrigger (.othersGetAndOppsGet (CardSubtype.ofSubtypes subtypes) power toughness oppP oppT))
def onCombatDamageWolfPlusOneOrTreasure : TriggeredAbility :=
  .triggered .combatDamageToPlayer (Effect.ofTrigger .wolfPlusOneOrTreasure)
def onYourBeginCombatTrampleCounterBecomeBear : TriggeredAbility :=
  .triggered .yourBeginCombat (Effect.ofTrigger .trampleCounterBecomeBear)
def onEnterMillThenSubtypeToHand (n : Nat) (subtype : String) : TriggeredAbility :=
  .triggered .enter (Effect.ofTrigger (.millThenSubtypeToHand n (CardSubtype.ofOracleD subtype)))
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
  .triggered .equippedAttacks (Effect.ofTrigger (.plusOneEachYouControl .citysBlessing))
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
def onWard (cost : WardCost) : TriggeredAbility :=
  .triggered .becomesTarget { resolution := .frc (.ward cost), phrase := "Ward" } {}
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
    { thisOrAnotherSubtype := CardSubtype.ofOracle? subtype }
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
      { e with sharedTrigger := some (SharedTrigger.chapter n ch) }
  | none => .triggered .sagaChapter e
def onTappedForTeamworkPlusOneAndDraw : TriggeredAbility :=
  .triggered .tappedForTeamwork Effect.seqPlusOneOnSourceAndDraw
def onEachEndStepDrawIfAttackedOrEnteredSubtype (subtype : String) : TriggeredAbility :=
  .triggered .eachEndStep (Effect.ofTrigger (.drawIfAttackedOrEnteredSubtype (CardSubtype.ofOracleD subtype .hero)))
def onAttackOthersOfSubtypeGetEqualToughness (subtype : String) : TriggeredAbility :=
  .triggered .attack (Effect.ofTrigger (.othersOfSubtypeGetEqualSourceToughness (CardSubtype.ofOracleD subtype .hero)))
def onCreatureYouControlEntersScryAndPlan (n : Nat) : TriggeredAbility :=
  .triggered .creatureYouControlEnters (Effect.ofTrigger (.scryAndPlan n))
def onCreaturesYouControlBecomeTappedLootAndPlan : TriggeredAbility :=
  .triggered .creaturesYouControlBecomeTapped (Effect.ofTrigger .lootAndPlan)
def onYouDrawSecondCreateVillainAndPlan : TriggeredAbility :=
  .triggered .youDrawSecond (Effect.ofTrigger .createVillainAndPlan)
def onVillainYouControlEntersDrainAndPlan (n : Nat) : TriggeredAbility :=
  .triggered (.subtypeYouControlEnters .villain) (Effect.ofTrigger (.drainAndPlan n))
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

/-- Oracle clause for putting `n` counters of `kind` on `noun`. -/
def counterOn (noun : String) (kind : CounterKind) (n : Nat) : String :=
  match kind with
  | .plusOnePlusOne => s!"put {plusOnePlusOneCountersPhrase n} on {noun}"
  | .indestructible => s!"put {kind.countersPhrase n} on {noun}"
  | .doubleStrike => s!"put {kind.countersPhrase n} on {noun}"
  | .burden => s!"put {kind.countersPhrase n} on {noun}"
  | .stun => s!"put {kind.countersPhrase n} on {noun}"
  | _ => "put counters"

/-- Printed noun for the permanent `who` names. `targetNoun` is the announced target. -/
def affectedNoun (who : TriggerAffected) (targetNoun : String) : String :=
  match who with
  | .target => targetNoun
  | .source => "this creature"
  | .enchanted => "enchanted creature"
  | .targetWhileSource => "that creature"

/-- Oracle clause for the single step that follows attaching to the announced
creature. A compound action flattened into more than one step is `none`. -/
def attachedFollowupPhrase (r : TriggerResolution) : Option String :=
  match r with
  | .pump (.fixed p) (.fixed t) (.target .whileSource) =>
    some s!"that creature gets {signedStat p}/{signedStat t} until end of turn"
  | .pump .double .double (.target .whileSource) =>
    some "double that creature's power and toughness until end of turn"
  | .putCounters (.ofKind .plusOnePlusOne n) (.target .whileSource) =>
    some s!"put {plusOnePlusOneCountersPhrase n} on that creature"
  | .putCounters (.ofKind .indestructible n) (.target .whileSource) =>
    some s!"put {(.indestructible : CounterKind).countersPhrase n} on that creature"
  | .putCounters (.ofKind .doubleStrike n) (.target .whileSource) =>
    some s!"put {(.doubleStrike : CounterKind).countersPhrase n} on that creature"
  | .putCounters (.ofKind .burden n) (.target .whileSource) =>
    some s!"put {(.burden : CounterKind).countersPhrase n} on that creature"
  | .putCounters (.ofKind .stun n) (.target .whileSource) =>
    some s!"put {(.stun : CounterKind).countersPhrase n} on that creature"
  | .grant (.keywords k) (.target .whileSource) =>
    some s!"that creature gains {k.joinedAnd} until end of turn"
  | .tap (.target .whileSource) => some "tap that creature"
  | .untap (.target .whileSource) => some "untap that creature"
  | .lose .indestructible (.target .whileSource) =>
    some "that creature loses indestructible until end of turn"
  | .cant (.beBlocked (.target .whileSource)) =>
    some "that creature can't be blocked this turn"
  | .becomeArtifact (.target .whileSource) =>
    some "until end of turn, that creature becomes an artifact in addition to its other types"
  | .becomePrepared (.target .whileSource) => some "that creature becomes prepared"
  | .setBasePT (.fixed p) (.fixed t) (.target .whileSource) =>
    some s!"that creature has base power and toughness {p}/{t} until end of turn"
  | .putOnLibrary .top (.target .whileSource) =>
    some "that creature's owner puts it on top of their library"
  | .putOnLibrary .bottom (.target .whileSource) =>
    some "that creature's owner puts it on the bottom of their library"
  | .destroy (.target .whileSource) _ => some "destroy that creature"
  | .dealDamage (.fixed n) (.target .whileSource) .none =>
    some s!"deals {n} damage to that creature"
  | .exile (.target .whileSource) .forLater .none => some "exile that creature"
  | _ => none

/-- Subtypes when `parts` is only `.othersOfSubtype`, in that order. -/
private def othersOfSubtypeParts (parts : List ObjectSelector) : Option (Array CardSubtype) :=
  parts.foldl (fun acc part =>
    match acc, part with
    | some ss, .othersOfSubtype subtype => some (ss.push subtype)
    | _, _ => none) (some #[])

/-- Effect clause from resolution, targeting, and divided-damage parameters. -/
def resolutionPhrase (t : TriggerTiming) : String :=
  let noun := t.targeting.kind.noun
  match t.resolution with
  | .pump power toughness who =>
    match power, toughness, who with
    | .greatestPower, .fixed 0, .source =>
      "it gets +X/+0 until end of turn, where X is the greatest power among creatures you control"
    | .perLookedAt, .perLookedAt, .source =>
      "this creature gets +1/+1 until end of turn for each card looked at while scrying this way"
    | .perOtherCreature, .perOtherCreature, .source =>
      "it gets +1/+1 until end of turn for each other creature you control"
    | .perPlains, .perPlains, .target =>
      "target creature you control gets +1/+1 until end of turn for each Plains you control"
    | .fixed power, .fixed toughness, .cause _ =>
      s!"that creature gets {signedStat power}/{signedStat toughness} until end of turn"
    | .equalSourceToughness, .equalSourceToughness, .othersOfSubtype subtype =>
      s!"each other {StaticAbility.pluralSubtype subtype} you control get +X/+X until end of turn, where X is this toughness"
    | .equalSourcePower, .fixed 0, .target =>
      s!"{noun} gets +X/+0 until end of turn, where X is this creature's power"
    | .fixed power, .fixed toughness, .creaturesYouControl =>
      s!"creatures you control get {signedStat power}/{signedStat toughness} until end of turn"
    | .fixed power, .fixed toughness,
        .intersection [.creaturesYouControl, .union parts] =>
      match othersOfSubtypeParts parts with
      | some subtypes =>
        let recipients :=
          if subtypes == #[.goblin, .orc] then "other Goblins and Orcs you control"
          else s!"other {StaticAbility.joinedSubtypes subtypes} you control"
        s!"{recipients} get {signedStat power}/{signedStat toughness} until end of turn"
      | none =>
        "those permanents get +P/+T until end of turn"
    | .fixed power, .fixed toughness, .opponentsCreatures =>
      s!"creatures your opponents control get {signedStat power}/{signedStat toughness} until end of turn"
    | .fixed power, .fixed toughness, .target =>
      s!"{noun} gets {signedStat power}/{signedStat toughness} until end of turn"
    | .double, .double, .target =>
      s!"double {noun}'s power and toughness until end of turn"
    | .fixed power, .fixed toughness, .source =>
      s!"this creature gets {signedStat power}/{signedStat toughness} until end of turn"
    | .double, .double, .source =>
      "double this creature's power and toughness until end of turn"
    | .fixed power, .fixed toughness, .enchanted =>
      s!"enchanted creature gets {signedStat power}/{signedStat toughness} until end of turn"
    | .double, .double, .enchanted =>
      "double enchanted creature's power and toughness until end of turn"
    | .fixed power, .fixed toughness, (.target .whileSource) =>
      s!"that creature gets {signedStat power}/{signedStat toughness} until end of turn"
    | .double, .double, (.target .whileSource) =>
      "double that creature's power and toughness until end of turn"
    | .fixed power, .fixed toughness,
        .intersection [.creaturesYouControl, .youControl (.subtype subtype)] =>
      s!"{subtype}s you control get {signedStat power}/{signedStat toughness} until end of turn"
    | _, _, _ =>
      "those permanents get +P/+T until end of turn"
  | .setBasePT .equalSourcePower .equalSourceToughness .target =>
    "choose up to one other target creature you control. Its base power and toughness become equal to this creature's power and toughness until end of turn"
  | .lose .indestructible .target =>
    s!"{noun} loses indestructible until end of turn"
  | .lose .indestructible .source =>
    "this creature loses indestructible until end of turn"
  | .lose .indestructible .enchanted =>
    "enchanted creature loses indestructible until end of turn"
  | .lose .indestructible (.target .whileSource) =>
    "that creature loses indestructible until end of turn"
  | .lose .allAbilities (.target .ifPresent) =>
    "it loses all abilities for as long as this remains on the battlefield"
  | .lose _ _ =>
    "lose"
  | .cant (.beBlocked .target) =>
    s!"{affectedNoun .target noun} can't be blocked this turn"
  | .cant (.beBlocked .source) =>
    s!"{affectedNoun .source noun} can't be blocked this turn"
  | .cant (.beBlocked .enchanted) =>
    s!"{affectedNoun .enchanted noun} can't be blocked this turn"
  | .cant (.beBlocked (.target .whileSource)) =>
    s!"{affectedNoun .targetWhileSource noun} can't be blocked this turn"
  | .cant (.beBlockedExceptByHaste .target) =>
    s!"{affectedNoun .target noun} can't be blocked this turn except by creatures with haste"
  | .cant (.beBlockedExceptByHaste .source) =>
    s!"{affectedNoun .source noun} can't be blocked this turn except by creatures with haste"
  | .cant (.beBlockedExceptByHaste .enchanted) =>
    s!"{affectedNoun .enchanted noun} can't be blocked this turn except by creatures with haste"
  | .cant (.beBlockedExceptByHaste (.target .whileSource)) =>
    s!"{affectedNoun .targetWhileSource noun} can't be blocked this turn except by creatures with haste"
  | .cant (.untapWhileYouControl .target) =>
    "that creature can't become untapped for as long as you control this creature"
  | .cant _ =>
    "can't"
  | .becomeArtifact .target =>
    s!"until end of turn, {noun} becomes an artifact in addition to its other types"
  | .becomeArtifact .source =>
    "until end of turn, this creature becomes an artifact in addition to its other types"
  | .becomeArtifact .enchanted =>
    "until end of turn, enchanted creature becomes an artifact in addition to its other types"
  | .becomeArtifact (.target .whileSource) =>
    "until end of turn, that creature becomes an artifact in addition to its other types"
  | .becomeArtifact _ =>
    "becomes an artifact"
  | .becomePrepared .target =>
    s!"{noun} becomes prepared"
  | .becomePrepared .source =>
    "this creature becomes prepared"
  | .becomePrepared .enchanted =>
    "enchanted creature becomes prepared"
  | .becomePrepared (.target .whileSource) =>
    "that creature becomes prepared"
  | .becomePrepared _ =>
    "becomes prepared"
  | .setBasePT (.fixed p) (.fixed t) .target =>
    s!"{noun} has base power and toughness {p}/{t} until end of turn"
  | .setBasePT (.fixed p) (.fixed t) .source =>
    s!"this creature has base power and toughness {p}/{t} until end of turn"
  | .setBasePT (.fixed p) (.fixed t) .enchanted =>
    s!"enchanted creature has base power and toughness {p}/{t} until end of turn"
  | .setBasePT (.fixed p) (.fixed t) (.target .whileSource) =>
    s!"that creature has base power and toughness {p}/{t} until end of turn"
  | .setBasePT _ _ _ =>
    "set base power and toughness"
  | .putOnLibrary .top .target =>
    s!"{noun}'s owner puts it on top of their library"
  | .putOnLibrary .bottom .target =>
    s!"{noun}'s owner puts it on the bottom of their library"
  | .putOnLibrary .top .source =>
    "this creature's owner puts it on top of their library"
  | .putOnLibrary .bottom .source =>
    "this creature's owner puts it on the bottom of their library"
  | .putOnLibrary .top .enchanted =>
    "enchanted creature's owner puts it on top of their library"
  | .putOnLibrary .bottom .enchanted =>
    "enchanted creature's owner puts it on the bottom of their library"
  | .putOnLibrary .top (.target .whileSource) =>
    "that creature's owner puts it on top of their library"
  | .putOnLibrary .bottom (.target .whileSource) =>
    "that creature's owner puts it on the bottom of their library"
  | .putOnLibrary .bottom .cardFromHand =>
    "put a card from your hand on the bottom of your library"
  | .putOnLibrary _ _ =>
    "put on library"
  | .surveil (.fixed n) => s!"surveil {n}"
  | .surveil _ => "surveil"
  | .empowerJace (.fixed n) => s!"empower Jace {n}"
  | .empowerJace _ => "empower Jace"
  | .prepareSource .ifNotPrepared =>
    "if this creature isn't prepared, it becomes prepared"
  | .prepareSource .ifThreeCreaturesDied =>
    "if three or more creatures died this turn, this creature becomes prepared"
  | .«if» (.atLeast .lastKnownPower (.fixed 2)) (.draw (.fixed 1)) =>
    "if you removed two or more loyalty counters to activate it, draw a card"
  | .putCounters what who =>
    match what, who with
    | .ofKind .plusOnePlusOne _, .youControl .eachCreature =>
      "put a +1/+1 counter on each creature you control"
    | .ofKind .plusOnePlusOne _, .youControl (.subtype s) =>
      s!"put a +1/+1 counter on each {s} you control"
    | .ofKind .plusOnePlusOne _, .youControl .citysBlessing =>
      "put a +1/+1 counter on each creature you control. If you have the city's blessing, put two +1/+1 counters on each creature you control instead"
    | .ofKind .plusOnePlusOne _, .eachOther =>
      "put a +1/+1 counter on each other creature you control"
    | .plusOneLastKnownMv, _ =>
      s!"put X +1/+1 counters on {noun}, where X is that spell's mana value"
    | .ofKind .loyalty _, .source => "put a loyalty counter on this"
    | .sourceCounters, _ =>
      "put its counters on up to one target creature you control"
    | .ofKind .charge _, _ => "put a charge counter on this enchantment"
    | .ofKind .quest _, _ => "put a quest counter on this enchantment"
    | .honePerOpponent, _ =>
      "put a hone counter on this for each creature target opponent controls"
    | .ofKind .plan _, _ => "put a plan counter on this enchantment"
    | .ofKind .plusOnePlusOne _, .permanent true =>
      s!"put a +1/+1 counter on {noun}"
    | .plusOneNoted, _ =>
      "put a +1/+1 counter on it for each invasion counter on this enchantment"
    | .ofKind .invasion _, _ => "put an invasion counter on this enchantment"
    | .ofKind .trample _, _ =>
      s!"put a trample counter on up to one {noun}"
    | .ofKind .influence _, _ => "put an influence counter on this"
    | .ofKind .loyalty _, .permanent _ => "put a loyalty counter on it"
    | .plusOneSacrificedPower, _ =>
      "put a number of +1/+1 counters on this creature equal to the sacrificed creature's power"
    | .ofKind .plusOnePlusOne n, .permanent false =>
      s!"put {plusOnePlusOneCountersPhrase n} on {noun}"
    | .ofKind .indestructible n, .permanent false =>
      s!"put {(.indestructible : CounterKind).countersPhrase n} on {noun}"
    | .ofKind .doubleStrike n, .permanent false =>
      s!"put {(.doubleStrike : CounterKind).countersPhrase n} on {noun}"
    | .ofKind .burden n, .permanent false =>
      s!"put {(.burden : CounterKind).countersPhrase n} on {noun}"
    | .ofKind .stun n, .permanent false =>
      s!"put {(.stun : CounterKind).countersPhrase n} on {noun}"
    | .ofKind kind n, .source =>
      counterOn "this creature" kind n
    | .ofKind kind n, .enchanted =>
      counterOn "enchanted creature" kind n
    | .ofKind kind n, (.target .whileSource) =>
      counterOn "that creature" kind n
    | .ofKind .plusOnePlusOne _, .eachUpToLastKnown =>
      "put a +1/+1 counter on each of up to that many target creatures you control"
    | .missingKeywordsFromTarget, .source =>
      "if that creature has haste and this doesn't, put a haste counter on this. Do the same for flying, first strike, double strike, deathtouch, indestructible, lifelink, menace, reach, trample, and vigilance"
    | _, _ => "put counters"
  | .«if» ((.atLeast (.count .landsYouControl) (.fixed 6))) (.sequence [.destroy .target,
      .createTokens .treasure (.fixed 1) false .kind (.controller .target)]) =>
    s!"if you control six or more lands, destroy {noun}. They create a Treasure token"
  | .ifElse (.or [.scriedThisTurn, .surveilledThisTurn])
      (.putCounters (.ofKind .plusOnePlusOne) .permanent) (.pump (.fixed 1) (.fixed 1) .target) =>
    s!"{noun} gets +1/+1 until end of turn. If you've scried or surveilled this turn, put a +1/+1 counter on that creature instead"
  | .«if» (.not (.atLeast (.count .planeswalkersYouControl) (.fixed 1))) (.sacrifice (.sacrificedSource .controllerSacrifices)) =>
    "if you don't control a planeswalker, sacrifice this creature"
  | .«if» ((.atLeast (.count .forestsExceptCause) (.fixed 5))) (.pump (.fixed 3) (.fixed 3) .target) =>
    s!"if you control at least five other Forests, {noun} gets +3/+3 until end of turn"
  | .may (.pay (.mana symbols)) (.sequence [.putCounters (.ofKind .plusOnePlusOne 1) .source, .draw (.fixed 1)]) .ifYouDo =>
    match symbols.toList with
    | [.generic n] =>
      s!"you may pay \{{n}}. If you do, put a +1/+1 counter on this creature and draw a card"
    | _ =>
      "you may pay. If you do, put a +1/+1 counter on this creature and draw a card"
  | .dealDamage amount who note =>
    match who, amount, note with
    | .blockers, .fixed n, _ =>
      s!"it deals {n} damage to each creature blocking it"
    | .permanent, .lastKnownPower, .excess =>
      s!"Bolg deals damage equal to the sacrificed creature's power to {noun}"
    | .permanent, .lastKnownPower, _ =>
      s!"it deals damage equal to its power to {noun}"
    | .player .eachOpponent, .subtypeCount subtype, _ =>
      s!"it deals damage equal to the number of {StaticAbility.pluralSubtype subtype} you control to each opponent"
    | .player .eachOpponent, .discardedHand, _ =>
      "this deals X damage to each opponent"
    | .player .eachOpponent, .fixed n, _ =>
      s!"this creature deals {n} damage to each opponent"
    | .target, .subtypeCount subtype, _ =>
      s!"it deals damage equal to the number of {StaticAbility.pluralSubtype subtype} you control to {noun}"
    | .target, .fixed n, .none =>
      s!"deals {n} damage to {noun}"
    | .target, .spellManaValue, _ =>
      s!"this deals damage equal to that spell's mana value to {noun}"
    | .target, .fixed n, _ =>
      s!"it deals {n} damage to {noun}"
    | .player (.target .opponent), .greatestArtifactMv, _ =>
      s!"this Saga deals X damage to {noun}, where X is the greatest mana value among artifacts you control"
    | .eachNonSubtypeAndOpponents subtype, .fixed n, _ =>
      s!"this Saga deals {n} damage to each non-{subtype} creature and each opponent"
    | .player (.target .opponent), .fixed n, _ =>
      s!"this deals {n} damage to {noun}"
    | .permanent, .fixed n, _ =>
      s!"it deals {n} damage to {noun}"
    | .source, .fixed n, .none =>
      s!"deals {n} damage to this creature"
    | .enchanted, .fixed n, .none =>
      s!"deals {n} damage to enchanted creature"
    | (.target .whileSource), .fixed n, .none =>
      s!"deals {n} damage to that creature"
    | _, _, _ =>
      "deal damage"
  | .scry (.fixed n) => s!"scry {n}"
  | .scry _ => "scry"
  | .draw amount who =>
    match who, amount with
    | .opponentHasYou, _ =>
      "target opponent may have you draw a card"
    | .you, .forEachTappedHuman =>
      "draw a card for each Human tapped this way"
    | .you, .perFatGraveyard =>
      "draw a card for each graveyard with seven or more cards in it"
    | .you, .discardedHand =>
      "draw X cards, where X is the number of cards discarded this way"
    | .you, .equalToManaSpent =>
      "draw X cards, where X is the amount of mana spent to cast that spell"
    | .you, .perControlled _ =>
      "draw a card for each permanent you control of that type"
    | .you, .upToHandSize _ =>
      "if you have fewer than that many cards in hand, draw cards equal to the difference"
    | .controller .enchanted, _ =>
      "that player draws a card"
    | .eachOpponent, .fixed n =>
      s!"each opponent draws {cardPhrase n.toNat}"
    | .you, .fixed n =>
      s!"draw {cardPhrase n.toNat}"
    | _, _ =>
      "draw cards"
  | .searchLibrary (.put .forest .asPrinted .none) =>
    "search your library for a Forest card, put that card onto the battlefield, then shuffle"
  | .searchLibrary (.returnToHand .basicLand .none) =>
    searchLibraryToHandPhrase "a basic land card"
  | .searchLibrary (.put .basicLandOnTop .asPrinted .none) =>
    "you may search your library for a basic land card, reveal it, then shuffle and put that card on top"
  | .searchLibrary (.put .dragon .asPrinted .none) =>
    "search your hand and/or library for a Dragon card and put it onto the battlefield"
  | .searchLibrary _ =>
    "search your library"
  | .discard what =>
    match what with
    | .cards n .you =>
      s!"discard {cardPhrase n}"
    | .hand =>
      "discard your hand"
    | .cards n .eachOpponent =>
      if n == 1 then "each opponent discards a card"
      else s!"each opponent discards {cardPhrase n}"
    | .cards n (.target .opponent) =>
      s!"{noun} discards {cardPhrase n}"
    | .chosenNonland =>
      s!"{noun} reveals their hand. You choose a nonland card from it. That player discards that card"
    | _ =>
      "discard cards"
  | .may (.discard (.cards 1)) (.draw (.fixed n)) .ifYouDo =>
    s!"you may discard a card. If you do, draw {cardPhrase n.toNat}"
  | .may (.dealDamage .lastKnownPower .target .none) (.sequence []) .ifYouDo =>
    "you may have this deal that much damage"
  | .may .retargetCause (.sequence []) .ifYouDo =>
    "you may choose new targets for that spell"
  | .may (.pay (.mana symbols)) (.queueReflexive follow) .ifYouDo =>
    let times :=
      match TriggerResolution.queuedReflexive follow with
      | .modeled _ times => times
      | _ => 1
    match symbols.toList with
    | [.generic n] =>
      if times > 1 then s!"you may pay \{{n}} up to {times} times"
      else s!"you may pay \{{n}}"
    | _ => "you may pay that cost"
  | .may (.pay (.mana symbols)) (.becomeCopy (.cause none)) .ifYouDo =>
    match symbols.toList with
    | [.generic 2] => "you may pay {2} to copy it"
    | _ => "you may pay to copy it"
  | .may (.loseLife (.fixed 2) .you)
      (.grant .assignCombatDamageEqualToughness .creaturesYouControl) .ifYouDo =>
    "you may pay 2 life. If you do, until end of turn, creatures you control with toughness greater than their power assign combat damage equal to their toughness rather than their power"
  | .may (.exile .top .playThisTurn .ifHero) (.sequence []) _ =>
    "you may exile the top card of your library. If that card is a Hero card, this gets +2/+1 until end of turn. You may play that card this turn"
  | .may action _ =>
    match action with
    | .tap .humans =>
      "you may tap any number of untapped Humans you control"
    | .sacrifice .another _ =>
      "you may sacrifice another creature. When you do, Bolg deals damage equal to that creature's power to another target creature. If excess damage was dealt this way, amass Goblins X, where X is that excess damage"
    | .put .artifactFromHand _ .forAttach =>
      "you may put an artifact card from your hand onto the battlefield"
    | .discard .hand =>
      "you may discard your hand"
    | .draw _ .opponentHasYou =>
      "target opponent may have you draw a card"
    | .put .landFromHand .tapped _ =>
      "you may put a land card from your hand onto the battlefield tapped"
    | .put (.creatureFromHand subtype maxMv) _ _ =>
      s!"you may put a {subtype} creature card with mana value {maxMv} or less from your hand onto the battlefield. If you don't, draw a card"
    | .sequence [.draw .equalToManaSpent _, .«if» .manaSpent (.discard (.cards n))] =>
      let disc := if n == 2 then "two cards" else cardPhrase n
      s!"you may draw X cards, where X is the amount of mana spent to cast that spell. If you do, discard {disc}"
    | _ => "you may do it"
  | .sacrifice what _ =>
    match what with
    | .opponentChosenCreature =>
      s!"{noun} sacrifices a creature of their choice"
    | .eachPlayersCreature =>
      "each player sacrifices a creature of their choice"
    | .leastPower =>
      "defending player sacrifices a creature with the least power among creatures they control"
    | .combatDamager =>
      "each opponent sacrifices a creature of their choice that dealt combat damage to you this turn"
    | .chosenNontokenCreature =>
      "each opponent sacrifices a nontoken creature of their choice"
    | .sacrificedSource .controllerSacrifices =>
      "sacrifice this creature"
    | .another =>
      "sacrifice another creature. When you do, Bolg deals damage equal to that creature's power to another target creature. If excess damage was dealt this way, amass Goblins X, where X is that excess damage"
    | _ =>
      "sacrifice it"
  | .dividedDamage =>
    match t.dividedDamage with
    | some (amount, maxTargets) =>
      s!"it deals {amount} damage divided as you choose among {dividedAmong maxTargets}"
    | none => "it deals damage divided as you choose"
  | .sequence [.returnToHand .graveyardCard, .gainLife .equalToTargetPower] =>
    s!"return {noun} to your hand. You gain life equal to that card's power"
  | .sequence [.draw (.fixed 1), .«if» (.not (.atLeast (.count .legendaryCreaturesYouControl) (.fixed 1))) (.putOnLibrary .bottom .cardFromHand)] =>
    "draw a card. Then if you don't control a legendary creature, put a card from your hand on the bottom of your library"
  | .sequence [.removeCounters .hope .source, .«if» .removedHope (.draw (.fixed 1)),
      .«if» (.not .hopeOnSource) (.sequence [.sacrifice .source, .gainLife (.fixed 4)])] =>
    "remove a hope counter from this. If you do, draw a card. Then if this has no hope counters on it, sacrifice it and you gain 4 life"
  | .sequence [.may (.tap .humans) (.sequence []), .draw .forEachTappedHuman _] =>
    "you may tap any number of untapped Humans you control. Draw a card for each Human tapped this way"
  | .sequence [.createTokens kind (.fixed 1) false, .attach .source .createdToken] =>
    s!"{TokenKind.createPhrase kind 1}, then attach this Equipment to it"
  | .sequence [.gainLife (.fixed n), .searchLibrary (.put .basicLandOnTop .asPrinted .none)] =>
    s!"you gain {n} life. You may search your library for a basic land card, reveal it, then shuffle and put that card on top"
  | .sequence [.destroy .oppArtifactsEnchantments .countDestroyed, .gainLife .forEachDestroyedThisWay] =>
    "destroy all artifacts and enchantments your opponents control. You gain 1 life for each permanent destroyed this way"
  | .sequence [.putCounters (.ofKind .plusOnePlusOne) .eachOther, .gainLife .perOtherCreature] =>
    "put a +1/+1 counter on each other creature you control. You gain 1 life for each other creature you control"
  | .sequence [.dealDamage (.fixed n) .target .markedPermanent, .«if» (.dealtDamageToSubtype subtype) (.destroy .permanentDealtDamage .none)] =>
    s!"it deals {n} damage to {noun}. If a {subtype} is dealt damage this way, destroy it"
  | .sequence [.returnToHand .permanent .returnedPermanent, .«if» .returnedPermanent (.putCounters (.ofKind .plusOnePlusOne 1) .source)] =>
    s!"return {noun} to its owner's hand. If you do, put a +1/+1 counter on this creature"
  | .sequence [.pump (.fixed p) (.fixed t)
      (.intersection [.creaturesYouControl, .union parts]),
      .pump (.fixed oppP) (.fixed oppT) .opponentsCreatures] =>
    match othersOfSubtypeParts parts with
    | some subtypes =>
      let who :=
        if subtypes == #[.goblin, .orc] then "other Goblins and Orcs you control"
        else s!"other {StaticAbility.joinedSubtypes subtypes} you control"
      s!"{who} get {signedStat p}/{signedStat t} until end of turn. Creatures your opponents control get {signedStat oppP}/{signedStat oppT} until end of turn"
    | none =>
      "resolve each step"
  | .sequence
      [.noteResolveThisTurn 3,
       .«if» (.nthResolve 1) (.gainLife (.fixed 1)),
       .«if» (.nthResolve 2) (.draw (.fixed 1)),
       .«if» (.nthResolve 3) (.putCounters (.ofKind .plusOnePlusOne) .youControl)] =>
    "you gain 1 life if this is the first time this ability has resolved this turn. If it's the second time, draw a card. If it's the third time, put a +1/+1 counter on each creature you control"
  | .sequence [.dealDamage .lastKnownPower .permanent .excess, .amass .notedExcess _ _ _] =>
    s!"Bolg deals damage equal to the sacrificed creature's power to {noun}. If excess damage was dealt this way, amass Goblins X, where X is that excess damage"
  | .sequence [.createTokens .spirit (.fixed 2) true, .«if» (.atLeast (.count (.intersection [.equipped, .legendaryCreaturesYouControl])) (.fixed 1)) .markRecentTokensAttacking] =>
    "create two tapped 1/1 white Spirit creature tokens with flying. If that creature is legendary, instead create two of those tokens that are tapped and attacking"
  | .sequence [.dealDamage (.fixed 1) .target .markedPermanent, .amass (.fixed 1) .orc false _] =>
    s!"this creature deals 1 damage to {noun}. Then amass Orcs 1"
  | .sequence [.untap .attackingCreatures, .additionalCombatPhase] =>
    "untap all attacking creatures. After this phase, there is an additional combat phase"
  | .sequence [.destroy .target .forAmass, .amass .notedPower _ _ (.controller .target), .«if» .youControlledDestroyed (.draw (.fixed 1))] =>
    s!"destroy {noun}. Its controller amasses Goblins X, where X is that creature's power. If you controlled that creature, draw a card"
  | .sequence [.may (.discard .hand) (.sequence []), .draw .discardedHand _, .«if» .enduringStoryNoted (.dealDamage .discardedHand (.player .eachOpponent))] =>
    "you may discard your hand. Draw X cards, where X is the number of cards discarded this way. If you have an enduring story, this deals X damage to each opponent"
  | .sequence [.putCounters (.ofKind .trample) .permanent, .becomeBear, .«if» ((.atLeast (.count (.youControl (.subtype .bear))) (.fixed 3))) (.draw (.fixed 2))] =>
    s!"put a trample counter on up to one {noun}. It becomes a Bear in addition to its other types. Then if you control three or more Bears, draw two cards"
  | .sequence [.mill (.fixed n) .you .milledCards, .returnToHand (.milledSubtype subtype)] =>
    s!"mill {n} cards, then put all {subtype} cards from among them into your hand"
  | .sequence [.tap .enchanted, .removeCounters .all .enchanted] =>
    "tap enchanted creature and remove all counters from it"
  | .sequence [.putCounters (.ofKind .quest) .source,
      .«if» ((.atLeast (.count .questCounters) (.fixed 6)))
        (.sequence [.sacrifice (.sacrificedSource .movedAsSacrificed), .searchLibrary (.put .dragon .asPrinted .none)])] =>
    "put a quest counter on this enchantment. If it has six or more quest counters on it, sacrifice it. If you do, search your hand and/or library for a Dragon card and put it onto the battlefield. If you search your library this way, shuffle"
  | .sequence [.draw (.fixed 1), .discard (.cards 1), .put .discardedLand .tapped _] =>
    "draw a card, then discard a card. If you discard a land card this way, put it from your graveyard onto the battlefield tapped"
  | .sequence [.putCounters .honePerOpponent .source, .attach .source (.target .laterCreature)] =>
    "put a hone counter on this for each creature target opponent controls. Attach this to up to one target creature you control"
  | .sequence [.attach .anyYouControl .target, .«if» .equipmentAttached (.fight .equipmentHost .reflexive)] =>
    "attach any number of target Equipment you control to target creature you control. When one or more Equipment become attached to that creature this way, that creature deals damage equal to its power to up to one target creature"
  | .sequence [.draw .equalToManaSpent _, .«if» .manaSpent (.discard (.cards n))] =>
    let disc := if n == 2 then "two cards" else cardPhrase n
    s!"draw X cards, where X is the amount of mana spent to cast that spell, then discard {disc}"
  | .sequence [.exile .landsYouControl .forLater .lands, .put .notedLands .tapped _] =>
    "exile up to three target lands you control, then return them to the battlefield tapped under their owner's control"
  | .sequence [.revealLibrary .untilInstantOrSorcery (.exile .top .forLater .impulse) .damagedPlayer,
      .mayCast .impulse .unlimited .withoutPaying .none] =>
    "that player exiles cards from the top of their library until they exile an instant or sorcery card. You may cast that card without paying its mana cost. Then that player puts the exiled cards that weren't cast this way on the bottom of their library in a random order"
  | .sequence [.putCounters (.ofKind .influence) .source, .scry (.fixed 2), .may (.draw _ .opponentHasYou) _] =>
    "put an influence counter on this and scry 2. Then target opponent may have you draw a card. If that player doesn't, you mill X cards, where X is the number of influence counters on this, and that player loses life equal to the total mana value of those cards"
  | .sequence [.mill (.fixed 2) .eachOpponent .opponentsMilled,
      .«if» .opponentsMilled (.queueReflexive (.mayCast .milledSpell .causingSpell .withoutPaying))] =>
    "each opponent mills two cards. When one or more cards are milled this way, exile target enchantment, instant, or sorcery card with equal or lesser mana value than that spell from an opponent's graveyard. Copy the exiled card. You may cast the copy without paying its mana cost"
  | .sequence [.sacrifice .combatDamager, .ringTempts] =>
    "each opponent sacrifices a creature of their choice that dealt combat damage to you this turn. The Ring tempts you"
  | .sequence [.putCounters (.ofKind .plan) .source, .scry (.fixed n)] =>
    s!"scry {n} and put a plan counter on this enchantment"
  | .sequence [.putCounters (.ofKind .plan) .source, .draw (.fixed 1), .discard (.cards 1)] =>
    "draw a card, then discard a card and put a plan counter on this enchantment"
  | .sequence [.putCounters (.ofKind .plan) .source, .createTokens .villain21menace (.fixed 1) false] =>
    "create a 2/1 black Villain creature token with menace and put a plan counter on this enchantment"
  | .sequence [.putCounters (.ofKind .plan) .source, .loseLife (.fixed n) .eachOpponent, .gainLife (.fixed m)] =>
    s!"each opponent loses {n} life and you gain {m} life. Put a plan counter on this enchantment"
  | .sequence [.putCounters (.ofKind .plan) .source, .draw (.fixed 1), .loseLife (.fixed 1)] =>
    "you draw a card, lose 1 life, and put a plan counter on this enchantment"
  | .sequence [.putCounters (.ofKind .plan) .source, .createTokens .treasure (.fixed 1) true] =>
    "create a tapped Treasure token and put a plan counter on this enchantment"
  | .sequence [.putCounters (.ofKind .plan) .source,
      .putCounters (.ofKind .plusOnePlusOne) (.permanent true)] =>
    "put a +1/+1 counter on target creature you control and a plan counter on this enchantment"
  | .sequence [.sacrifice .plan, .draw (.fixed 1), .putCounters (.ofKind .plusOnePlusOne) .youControl] =>
    "sacrifice it, draw a card, and put a +1/+1 counter on each creature you control"
  | .sequence [.sacrifice .plan .forReflexive,
      .«if» .planWasSacrificed (.queueReflexive (.returnToHand (.graveyardInstants 2)))] =>
    "sacrifice it. When you do, return up to two target instant and/or sorcery cards from your graveyard to your hand"
  | .sequence [.sacrifice .plan .forReflexive,
      .«if» .planWasSacrificed (.queueReflexive (.gainControl .duringNextTurn))] =>
    "sacrifice it. When you do, you control target opponent during their next turn"
  | .sequence [.sacrifice .plan .forReflexive,
      .«if» .planWasSacrificed (.queueReflexive (.exile (.opponentTop 5) (.mayCastUpTo 2)))] =>
    "sacrifice it. When you do, target opponent exiles the top five cards of their library. You may cast up to two spells from among the exiled cards without paying their mana costs"
  | .sequence [.sacrifice .plan, .createTokens .robotVillain22 (.fixed n) false] =>
    s!"sacrifice it and create {englishNumber n.toNat} 2/2 colorless Robot Villain artifact creature tokens"
  | .sequence [.sacrifice .plan .forReflexive,
      .«if» .planWasSacrificed (.queueReflexive (.dealDamage (.fixed n) .target .divided))] =>
    s!"sacrifice it. When you do, it deals {n} damage divided as you choose among one or two targets"
  | .sequence [.sacrifice .plan .forReflexive,
      .«if» .planWasSacrificed (.queueReflexive (.putCounters (.ofKind .indestructible) .permanent))] =>
    "sacrifice it. When you do, put an indestructible counter on target creature you control"
  | .sequence [.attach .source .target, followup] =>
    match attachedFollowupPhrase followup with
    | some phrase => s!"attach it to {noun}. {capitalizeAscii phrase}"
    | none => "resolve each step"
  | .sequence [.exile .target .untilSourceLeaves .copyAndHost, .becomeCopy .noted] =>
    "exile up to one target creature other than enchanted creature until this Aura leaves the battlefield. Enchanted creature becomes a copy of that creature until this Aura leaves the battlefield"
  | .sequence [.draw (.fixed 1), .may (.put .landFromHand .tapped _) _] =>
    "draw a card, then you may put a land card from your hand onto the battlefield tapped"
  | .sequence [.draw (.fixed 1), .«if» (.atLeast (.count (.othersOfSubtype .hero)) (.fixed 1)) (.gainLife (.fixed 2))] =>
    "draw a card. If you control another Hero, you gain 2 life"
  | .sequence [.createTokens .treasure (.fixed 1) false .alien .you .invasion,
      .putCounters .plusOneNoted .createdToken,
      .putCounters (.ofKind .invasion) .source] =>
    "create a 1/1 red Alien creature token with haste and \"This token attacks each combat if able.\" Put a +1/+1 counter on it for each invasion counter on this enchantment, then put an invasion counter on this enchantment"
  | .sequence [.createTokens .treasure (.fixed 1) false .sturdyShield .you .remember,
      .attach .createdToken .source] =>
    "create a colorless Equipment artifact token named Sturdy Shield with \"Equipped creature gets +1/+2\" and equip {2}. Attach it to this creature"
  | .sequence [.exile .graveyardCard .forLater .playCard, .grantPlayNotedUntilNextTurn] =>
    s!"exile {noun}. {playThatCardUntilNextTurnPhrase}"
  | .sequence [.tap .target, .cant (.untapWhileYouControl .target)] =>
    s!"tap {noun}. That creature can't become untapped for as long as you control this creature"
  | .sequence [.tap (.target .ifPresent), .lose .allAbilities (.target .ifPresent)] =>
    "tap up to one target creature. It loses all abilities for as long as this remains on the battlefield"
  | .sequence [.grant (.keywords k) .target,
      .«if» (.atLeast (.count (.target .creature)) (.fixed 1)) (.putCounters (.ofKind .plusOnePlusOne) .permanent),
      .«if» (.atLeast (.count (.target .planeswalker)) (.fixed 1)) (.putCounters (.ofKind .loyalty) .permanent)] =>
    s!"{noun} gains {k.joinedAnd} until end of turn. Put a +1/+1 counter on it if it's a creature. Put a loyalty counter on it if it's a planeswalker"
  | .sequence [.draw (.fixed 2), .«if» (.not (.atLeast .libraryCards (.fixed 1))) .winTheGame, .«if» (.atLeast .libraryCards (.fixed 1)) .shuffleSource] =>
    "draw two cards. If your library has no cards in it, you win the game. Fblthp's owner shuffles him into their library"
  | .sequence [.armSurveilReturnLifeGained, .surveil (.fixed 1)] =>
    "if you gained life this turn, surveil 1. If you put a card with mana value less than or equal to the amount of life you gained this turn into your graveyard this way, put that card into your hand"
  | .sequence [.pump (.fixed 3) (.fixed 0) .target, .grant (.keywords k) .target] =>
    s!"{noun} gets +3/+0 and gains {k.joinedAnd} until end of turn"
  | .sequence [.pump (.fixed p) (.fixed t) .target, .grant (.keywords k) .target] =>
    if k == Keyword.trample then
      s!"{noun} gets {signedStat p}/{signedStat t} and gains trample until end of turn"
    else
      "resolve each step"
  | .sequence [.becomeArtifact .target, .grant (.keywords k) .target] =>
    if k == Keyword.indestructible then
      s!"until end of turn, {noun} becomes an artifact in addition to its other types and gains indestructible"
    else
      "resolve each step"
  | .sequence [.tap .target, .putCounters (.ofKind .stun) .permanent] =>
    s!"tap {noun} and put a stun counter on it"
  | .sequence [.destroy .target,
      .createTokens .treasure (.fixed 1) false .kind (.controller .target)] =>
    s!"destroy {noun}. They create a Treasure token"
  | .sequence [.may (.put .artifactFromHand _ .forAttach) _, .«if» (.atLeast (.count .putEquipment) (.fixed 1)) (.attach .putArtifact .notedHost)] =>
    "you may put an artifact card from your hand onto the battlefield. If it's an Equipment, attach it to this creature"
  | .sequence [.loseLife (.fixed n) (.target .opponent), .gainLife (.fixed m)] =>
    s!"target opponent loses {n} life and you gain {m} life"
  | .sequence [.pump (.fixed p) (.fixed 0) (.intersection [.creaturesYouControl, .youControl (.subtype .elf)]),
      .grant (.keywords k) (.intersection [.creaturesYouControl, .youControl (.subtype .elf)])] =>
    if k == Keyword.vigilance then
      s!"Elves you control get {signedStat p}/+0 and gain vigilance until end of turn"
    else
      "resolve each step"
  | .sequence [.searchLibrary (.exile (.basicUpTo .plains max) .forLater .linked),
      .gainLife (.fixed life)] =>
    s!"search your library for up to {max} basic Plains cards, exile them, then shuffle. You gain {life} life"
  | .sequence [.createTokens .treasure (.fixed 1) false,
      .«if» ((.atLeast (.count (.youControl (.subtype .treasure))) (.fixed 4))) (.sacrifice (.sacrificedSource .isSacrificed) .noted),
      .«if» .sourceWasSacrificed (.createTokens .dragon (.fixed 1) false)] =>
    "create a Treasure token. Then if you control four or more Treasures, sacrifice this Saga. If you do, create a 6/6 red Dragon creature token with flying"
  | .sequence [.draw (.fixed 1), .grant .basePowerEqualHand .source] =>
    "draw a card. Until end of turn, this creature's base power is equal to the number of cards in your hand"
  | .sequence [.putCounters (.ofKind .plusOnePlusOne) .source, .scry (.fixed 1)] =>
    "put a +1/+1 counter on this creature. Scry 1"
  | .sequence [.putCounters (.ofKind .plusOnePlusOne 2) .source, .copyCause] =>
    "copy that spell. You may choose new targets for the copy. Put two +1/+1 counters on this creature"
  | .sequence _ =>
    "resolve each step"
  | .gainLife amount =>
    match amount with
    | .fixed n => s!"you gain {n} life"
    | .equalToTargetPower =>
      "you gain life equal to that card's power"
    | .forEachDestroyedThisWay =>
      "you gain 1 life for each permanent destroyed this way"
    | .perOtherCreature =>
      "you gain 1 life for each other creature you control"
    | .attachedEquipment =>
      "you gain X life, where X is the number of Equipment attached to it"
    | _ =>
      "you gain life"
  | .may (.pay (.mana symbols)) (.draw (.fixed 1)) .ifYouDo =>
    match symbols.toList with
    | [.generic n] => s!"you may pay \{{n}}. If you do, draw a card"
    | _ => "you may pay. If you do, draw a card"
  | .«if» (.not (.atLeast (.count .legendaryCreaturesYouControl) (.fixed 1))) (.putOnLibrary .bottom .cardFromHand) =>
    "if you don't control a legendary creature, put a card from your hand on the bottom of your library"
  | .exile what how note =>
    match what, how, note with
    | .target, .leaveTrigger, .none =>
      if t.allowsZeroTargets then s!"you may exile {noun}" else s!"exile {noun}"
    | .target, .untilSourceLeaves, .copyAndHost =>
      "exile up to one target creature other than enchanted creature until this Aura leaves the battlefield"
    | .target, .untilSourceLeaves, .none =>
      if t.allowsZeroTargets then
        if t.targeting.kind == .defendingPlayerCreature then
          s!"you may exile {noun} until this leaves the battlefield"
        else
          s!"you may exile {noun}"
      else
        s!"exile {noun} until this leaves the battlefield"
    | .top, .playUntilNextTurn, .none =>
      s!"exile the top card of your library. {playThatCardUntilNextTurnPhrase}"
    | .top, .playThisTurn, .ifHero =>
      "exile the top card of your library. If it is a Hero card, this gets +2/+1 until end of turn. You may play that card this turn"
    | (.target .eachPermanent), .untilSourceLeaves, .none =>
      "for each opponent, exile up to one target nonland permanent that player controls until this leaves the battlefield"
    | .target, .nextEndStep, .none =>
      s!"exile up to one {noun}. Return that card to the battlefield under its owner's control at the beginning of the next end step"
    | .landsYouControl, .forLater, .lands =>
      "exile up to three target lands you control"
    | .graveyardCard, .forLater, .playCard =>
      s!"exile {noun}"
    | .target, .forLater, .none =>
      if noun.isEmpty then "exile it" else s!"exile {noun}"
    | .source, .forLater, .none =>
      "exile this creature"
    | .enchanted, .forLater, .none =>
      "exile enchanted creature"
    | (.target .whileSource), .forLater, .none =>
      "exile that creature"
    | .top, .forLater, .impulse =>
      "exile cards from the top of their library until they exile an instant or sorcery card"
    | _, _, _ =>
      "exile it"
  | .put what how note =>
    match what, how, note with
    | .linkedExile, _, _ =>
      "return the exiled card to the battlefield under its owner's control"
    | .nonlandMvAtMost mv, _, _ =>
      s!"put up to one target nonland permanent card with mana value {mv} or less from a graveyard onto the battlefield under its owner's control"
    | .source, .asArtifact, _ =>
      "if they were a creature, return them to the battlefield. They're an artifact"
    | .source, .underOwner, .entering _ =>
      "return this from its owner's graveyard to the battlefield under its owner's control"
    | .cause _, .underOwner, _ =>
      "return it to the battlefield under its owner's control"
    | .notedLands, .tapped, _ =>
      "return those lands to the battlefield tapped"
    | .discardedLand, .tapped, _ =>
      "if you discard a land card this way, put it onto the battlefield tapped"
    | .landFromHand, .tapped, _ =>
      "put a land card from your hand onto the battlefield tapped"
    | .artifactFromHand, _, .forAttach =>
      "put an artifact card from your hand onto the battlefield"
    | .randomCreature, _, _ =>
      "put a random creature card from among them onto the battlefield"
    | .revealed, _, _ =>
      "put that card onto the battlefield"
    | .forest, _, _ =>
      "put that card onto the battlefield"
    | .basicLandOnTop, _, _ =>
      "put that card on top of your library"
    | .dragon, _, _ =>
      "put it onto the battlefield"
    | .creatureMvAtMost mv, _, _ =>
      s!"return target creature card with mana value {mv} or less from your graveyard to the battlefield"
    | _, _, _ =>
      "put it onto the battlefield"
  | .removeCounters what who =>
    match what, who with
    | .hope, .source =>
      "remove a hope counter from this"
    | .all, .enchanted =>
      "remove all counters from enchanted creature"
    | _, _ =>
      "remove counters"
  | .«if» .removedHope (.draw (.fixed 1)) =>
    "if a hope counter was removed this way, draw a card"
  | .«if» (.not .hopeOnSource) (.sequence [.sacrifice .source, .gainLife (.fixed 4)]) =>
    "if this has no hope counters on it, sacrifice it and you gain 4 life"
  | .tap .humans =>
    "tap any number of untapped Humans you control"
  | .destroy .oppArtifactsEnchantments .countDestroyed =>
    "destroy all artifacts and enchantments your opponents control"
  | .destroy .permanentDealtDamage .none =>
    "destroy the permanent dealt damage this way"
  | .destroy .target .forAmass | .destroy .target .none | .destroy .target .chosenToken =>
    if noun.isEmpty then "destroy it" else s!"destroy {noun}"
  | .destroy .source _ =>
    "destroy this creature"
  | .destroy .enchanted _ =>
    "destroy enchanted creature"
  | .destroy (.target .whileSource) _ =>
    "destroy that creature"
  | .destroy _ _ =>
    "destroy it"
  | .recruit .recruit =>
    "recruit"
  | .recruit .you =>
    "you recruit"
  | .amass .lastKnownPower subtype _ _ =>
    s!"amass {pluralizeName subtype} X, where X is this creature's power"
  | .amass .notedExcess subtype _ _ =>
    s!"amass {pluralizeName subtype} X, where X is the excess damage"
  | .amass .notedPower subtype _ (.controller .target) =>
    s!"its controller amasses {pluralizeName subtype} X, where X is that creature's power"
  | .amass (.fixed n) subtype true _ =>
    s!"amass {pluralizeName subtype} {n}, then attach this Equipment to the amassed Army"
  | .amass (.fixed n) subtype _ _ =>
    s!"amass {pluralizeName subtype} {n}"
  | .amass _ _ _ _ =>
    "amass"
  | .createTokens kind amount tapped token who note =>
    match token, who, amount, note with
    | .axe, _, _, .attachReflexive =>
      "create a colorless Equipment artifact token named Axe with \"Equipped creature gets +1/+0\" and equip {2}. When you do, attach it to target creature you control"
    | .axe, _, _, _ =>
      "create a colorless Equipment artifact token named Axe with \"Equipped creature gets +1/+0\" and equip {2}"
    | .kind, .you, .oppArtifacts, _ =>
      "create X tapped Treasure tokens, where X is the number of artifacts your opponents control"
    | .kind, .you, .damagedPlayerArtifacts, _ =>
      "you create a Treasure token for each artifact that player controls"
    | .kind, .you, .lastKnownPower, _ =>
      if kind == .birdSoldier then
        "create a 4/4 white Bird Soldier creature token with flying for each creature returned to your hand this way"
      else
        "create that many Treasure tokens"
    | .kind, .you, .perSubtype subtype, _ =>
      s!"create a {TokenKind.oracleNoun kind} token for each {subtype} you control"
    | .kind, .you, .chosenCreatureType, _ =>
      "choose a creature type. Create a Treasure token for each creature you control of that type"
    | .zabu, _, _, _ =>
      "create Zabu, a legendary 2/2 green Cat creature token with \"Landfall — Whenever a land you control enters, put a +1/+1 counter on Zabu.\""
    | .theVoid, _, _, _ =>
      s!"{noun} creates The Void, a legendary 5/5 black Horror Villain creature token with flying, indestructible, and \"The Void attacks each combat if able.\""
    | .redwing, _, _, _ =>
      "create Redwing, a legendary 1/1 blue Bird Scout creature token with flying and \"Whenever Redwing attacks, surveil 1.\""
    | .alien, _, _, _ =>
      "create a 1/1 red Alien creature token with haste"
    | .galactus, _, _, _ =>
      "create Galactus, a legendary 16/16 black Elder Alien creature token with flying and trample"
    | .sturdyShield, _, _, _ =>
      "create a colorless Equipment artifact token named Sturdy Shield"
    | .merfolk, _, .blueManaSymbols, _ =>
      "create a 1/1 blue Merfolk creature token for each blue mana symbol in that spell's mana cost"
    | .kind, .controller .target, _, _ =>
      "they create a Treasure token"
    | .kind, .you, .fixed n, _ =>
      TokenKind.createPhrase kind n.toNat (tapped := tapped)
    | _, _, _, _ =>
      "create a token"
  | .attach what host =>
    match what, host with
    | .source, .createdToken =>
      "attach this Equipment to it"
    | .source, .target =>
      s!"attach it to {noun}"
    | .target, .optionalCreature =>
      "attach target Equipment you control to up to one target creature you control"
    | .source, (.target .laterCreature) =>
      "attach this to up to one target creature you control"
    | .anyYouControl, .target =>
      "attach any number of Equipment you control to target creature you control"
    | .createdToken, .source | .putArtifact, .notedHost =>
      "attach it to this creature"
    | _, _ =>
      "attach it"
  | .«if» (.dealtDamageToSubtype subtype) (.destroy .permanentDealtDamage .none) =>
    s!"if a {subtype} is dealt damage this way, destroy it"
  | .addMana types amount =>
    match amount with
    | .perChargeCounter =>
      s!"add {manaSymbolsText types} for each charge counter on this enchantment"
    | .fixed 1 => s!"add {manaSymbolsText types}"
    | _ => "add mana"
  | .or [.tap .target, .untap .target] =>
    if t.targeting.kind == .nonland then
      "choose one — • Tap target nonland permanent. • Untap target nonland permanent"
    else
      "choose one — tap target creature an opponent controls; untap target creature you control"
  | .becomePT (.fixed p) (.fixed t) =>
    s!"you may have this creature's base power and toughness become {p}/{t} until end of turn"
  | .becomePT _ _ =>
    "you may have this creature's base power and toughness become those values until end of turn"
  | .«if» .returnedPermanent (.putCounters (.ofKind .plusOnePlusOne 1) .source) =>
    "if you do, put a +1/+1 counter on this creature"
  | .lookAtTopRevealTypes (.fixed n) types =>
    let joined :=
      match types.toList with
      | [a, b] => s!"a {a} or {b} card"
      | xs => s!"a {String.intercalate " or " xs} card"
    s!"look at the top {n} cards of your library. You may reveal {joined} from among them and put it into your hand. {restOnBottomRandomPhrase}"
  | .lookAtTopRevealTypes _ _ =>
    "look at the top cards of your library"
  | .gainControl .untilEndOfTurn =>
    s!"gain control of {noun} until end of turn. Untap it. It gains haste until end of turn"
  | .gainControl .whileSourceRemains =>
    s!"gain control of {noun} for as long as this Saga remains on the battlefield"
  | .gainControl .duringNextTurn =>
    "you control target opponent during their next turn"
  | .honeEachEquipment =>
    "put a hone counter on each Equipment you control"
  | .cascade =>
    "exile cards from the top of your library until you exile a nonland card that costs less. You may cast it without paying its mana cost"
  | .noteResolveThisTurn _ =>
    "count another resolution of this ability this turn"
  | .«if» (.nthResolve n) _ =>
    s!"if this is time {n} this ability has resolved this turn"
  | .chooseModes modes how =>
    if modes == TriggerResolution.allianceModes && how == .oneUnusedThisTurn then
      "choose one that hasn't been chosen this turn — • Add {G}{G}{G}. • Put a +1/+1 counter on each creature you control. • Scry 2, then draw a card"
    else if modes == TriggerResolution.gollumModes && how == .oneUnused then
      "choose one that hasn't been chosen — • Put a +1/+1 counter on Gollum. • Each opponent loses 2 life and you gain 2 life. • Draw a card"
    else if modes == TriggerResolution.upToXModes && how == .alreadyChosen then
      "choose up to X — • Discard a card, then draw a card. • Target opponent loses 2 life. • Destroy target token. • Each player sacrifices a creature of their choice"
    else if modes == TriggerResolution.hydeModes && how == .plusOneOrRemoveCounter then
      "choose one — put a +1/+1 counter on this, or remove a counter from a creature you control and draw a card"
    else if modes == TriggerResolution.visionModes && how == .vision then
      "choose one that hasn't been chosen this turn — • This gains double strike until end of turn. • This gains indestructible until end of turn. • Draw a card"
    else
      "choose a mode"
  | .returnToHand what note =>
    match what, note with
    | .graveyardCard, .none =>
      s!"return {noun} to your hand"
    | .permanent, .returnedPermanent =>
      s!"return up to one {noun} to its owner's hand"
    | .graveyardPermanent, .none =>
      s!"choose {noun} that was put there from anywhere this turn. Return it to your hand"
    | .milledSubtype subtype, .none =>
      s!"put all {subtype} cards milled this way into your hand"
    | .source, .none =>
      "return this card from your graveyard to your hand"
    | .revealed, .none =>
      "put it into your hand"
    | .basicLand, .none =>
      "put it into your hand"
    | .linkedExile, .none =>
      "put a card exiled with this Saga into its owner's hand"
    | .cause _, .none =>
      "return that card to its owner's hand"
    | _, _ =>
      "return it to a hand"
  | .or [.putCounters (.ofKind .plusOnePlusOne) .permanent, .createTokens .treasure (.fixed 1) false] =>
    "choose one — • Put a +1/+1 counter on target Wolf you control. • Create a Treasure token"
  | .mayCast origin maxMv cost note =>
    match origin, maxMv, cost, note with
    | .graveyard, .unlimited, .pay, .exileInstead =>
      "you may cast an artifact, instant, or sorcery spell from your graveyard. If an instant or sorcery spell cast this way would be put into your graveyard, exile it instead"
    | .hand, .twiceLegendaryWizards, .withoutPaying, .none =>
      "you may cast an instant or sorcery spell with mana value X or less from your hand without paying its mana cost, where X is twice the number of legendary Wizards you control"
    | .hand, .lastKnown, .withoutPaying, .none =>
      "you may cast an instant or sorcery spell from your hand with mana value less than or equal to that damage without paying its mana cost"
    | .impulse, .unlimited, .withoutPaying, .none =>
      "you may cast that card without paying its mana cost"
    | .nextRedOrGreenCreature, .unlimited, .withoutPaying, .none =>
      "the next red or green creature spell you cast this turn can be cast without paying its mana cost"
    | .looked, .greatestAttackingPower, .withoutPaying, .none =>
      "you may cast a spell from among them with mana value less than or equal to the greatest power among attacking creatures you control without paying its mana cost"
    | _, _, _, _ =>
      "you may cast a spell"
  | .grant what who =>
    match what, who with
    | .doubleStrike, .equippedAttackers =>
      "each equipped attacking creature gains double strike until end of turn"
    | .protectionEverything, .youIfCast =>
      "if you cast it, you gain protection from everything until your next turn"
    | .keywords k, .target =>
      s!"{noun} gains {k.joinedAnd} until end of turn"
    | .keywords k, .source =>
      s!"this creature gains {k.joinedAnd} until end of turn"
    | .keywords k, .enchanted =>
      s!"enchanted creature gains {k.joinedAnd} until end of turn"
    | .keywords k, (.target .whileSource) =>
      s!"that creature gains {k.joinedAnd} until end of turn"
    | .keywords k, .creaturesYouControl =>
      s!"creatures you control gain {k.joinedAnd} until end of turn"
    | .keywords k, .intersection [.creaturesYouControl, .youControl (.subtype subtype)] =>
      s!"{subtype}s you control gain {k.joinedAnd} until end of turn"
    | .hexproofWhileSource, .target =>
      s!"{noun} gains hexproof for as long as this Saga remains on the battlefield"
    | .preventDamageWhileSource, _ =>
      "prevent all damage that would be dealt by up to one target creature for as long as this Saga remains on the battlefield"
    | .landfallCreateElf, .source =>
      "this Saga gains \"Landfall — Whenever a land you control enters, create a 1/1 green Elf creature token.\""
    | .assignCombatDamageEqualToughness, .creaturesYouControl =>
      "until end of turn, creatures you control with toughness greater than their power assign combat damage equal to their toughness rather than their power"
    | .basePowerEqualHand, .source =>
      "until end of turn, this creature's base power is equal to the number of cards in your hand"
    | .ironFistTap, .source =>
      "this gains \"{T}: This deals damage equal to its power to any other target\" until end of turn"
    | .keywords _, .spellTargets =>
      "those creatures gain flying until end of turn"
    | _, _ =>
      "grant"
  | .revealLibrary how thenDo who =>
    match how, thenDo, who with
    | .top n, .put .randomCreature .asPrinted .none, .you =>
      s!"reveal the top {n} cards of your library. Put a random creature card from among them onto the battlefield. {restOnBottomRandomPhrase}"
    | .untilCreature,
      .ifElse .revealedManaValueAtMostLands
        (.put .revealed .asPrinted .none) (.returnToHand .revealed .none),
      .you =>
      s!"reveal cards from the top of your library until you reveal a creature card. If its mana value is less than or equal to the number of lands you control, put it onto the battlefield. Otherwise, put it into your hand. {restOnBottomRandomPhrase}"
    | .untilSaga, .put .revealed .asPrinted .none, .you =>
      "reveal cards from the top of your library until you reveal a Saga card. Put that card onto the battlefield and the rest on the bottom of your library in a random order"
    | .untilInstantOrSorcery, .exile .top .forLater .impulse, .damagedPlayer =>
      "that player exiles cards from the top of their library until they exile an instant or sorcery card"
    | .untilNonland,
      .may (.putCounters (.ofKind .plusOnePlusOne 1) .source)
        (.exile .top .forLater .anyManaThisTurn) .ifYouDont,
      .announced =>
      "that player exiles cards until a nonland card"
    | .top n, .mayCast .looked .greatestAttackingPower .withoutPaying .none, .you =>
      s!"look at the top {n} cards of your library. You may cast a spell from among them with mana value less than or equal to the greatest power among attacking creatures you control without paying its mana cost. {restOnBottomRandomPhrase}"
    | _, _, _ =>
      "reveal cards from a library"
  | .«if» (.atLeast .cardsDrawnThisTurn (.fixed 2)) (.sequence [.pump (.fixed 3) (.fixed 0) .target, .grant (.keywords k) .target]) =>
    s!"if you've drawn two or more cards this turn, {noun} gets +3/+0 and gains {k.joinedAnd} until end of turn"
  | .mill amount who note =>
    match amount, who, note with
    | .fixed n, .you, .none | .fixed n, .you, .milledCards =>
      s!"mill {n} cards"
    | .fixed n, .target .player, .none =>
      s!"{noun} mills {n} cards"
    | .thatManyLost, .thatPlayer, .none =>
      "that player mills that many cards"
    | .fixed n, .eachOpponent, .opponentsMilled =>
      s!"each opponent mills {n} cards"
    | _, _, _ =>
      "mill"
  | .may (.pay (.sacrifice (.fixed 1) .another)) (.putCounters .plusOneSacrificedPower .source) .ifYouDo =>
    "you may sacrifice another creature. If you do, put a number of +1/+1 counters on this creature equal to the sacrificed creature's power"
  | .may (.pay (.mana symbols)) (.returnToHand .source) .ifYouDo =>
    s!"you may pay {String.join (symbols.toList.map ManaSymbol.toNotation)}. If you do, return this card from your graveyard to your hand"
  | .copySelfNonlegendary =>
    "if they're not a token, create two tokens that are copies of them, except the tokens aren't legendary"
  | .may (.pay (.sacrifice (.fixed 1) .anotherCreatureOrArtifact))
      (.sequence [.draw (.fixed 1), .createTokens .treasure (.fixed 1) false]) .ifYouDo =>
    "you may sacrifice another creature or artifact. If you do, draw a card and create a Treasure token"
  | .ringTempts =>
    "the Ring tempts you"
  | .may (.discard .hand) (.draw (.fixed n)) .ifYouDo =>
    s!"you may discard your hand. If you do, draw {cardPhrase n.toNat}"
  | .queueReflexive (.pump .perPlains .perPlains .target) =>
    "whenever you attack this turn, target creature you control gets +1/+1 until end of turn for each Plains you control"
  | .spellsCostLess _ (.fixed n) =>
    s!"spells you cast this turn cost \{{n}} less to cast"
  | .spellsCostLess _ _ =>
    "spells you cast this turn cost less to cast"
  | .may (.draw (.perControlled _) _) (.draw (.fixed 1) .eachOpponent) .ifYouDo =>
    "you may draw a card for each artifact you control. If you do, each opponent draws a card"
  | .investigate => "investigate"
  | .connive .source => "it connives"
  | .connive .target => s!"{noun} connives"
  | .connive .enteringVillain => "you may have it connive"
  | .connive _ => "connive"
  | .«if» (.or [.attackedWithSubtype attacked, .subtypeEntered entered]) (.draw (.fixed 1)) =>
    let attackedNoun := if attacked == .hero then "a Hero" else s!"a {attacked}"
    let enteredNoun := if entered == .hero then "a Hero" else s!"a {entered}"
    s!"if you attacked with {attackedNoun} this turn or {enteredNoun} entered the battlefield under your control this turn, draw a card"
  | .or [.createTokens .food (.fixed 1) false, .createTokens .treasure (.fixed 1) false] =>
    "create a Food token or a Treasure token"
  | .ifElse ((.atLeast (.count .creatureCardsInGraveyard) (.fixed 2)))
      (.createTokens .villain21menace (.fixed 1) true) (.mill (.fixed 2)) =>
    "create a tapped 2/1 black Villain creature token with menace if there are two or more creature cards in your graveyard. Otherwise, mill two cards"
  | .ifElse ((.atLeast (.count (.target (.anotherSubtype .hero))) (.fixed 1)))
      (.putCounters (.ofKind .plusOnePlusOne 2) .permanent)
      (.putCounters (.ofKind .plusOnePlusOne) .permanent) =>
    "put a +1/+1 counter on target creature. If that creature is another Hero, put two +1/+1 counters on it instead"
  | .may (.pay (.or [.sacrifice (.fixed 1) .artifact, .discard (.fixed 1) .card])) (.draw (.fixed 1)) .ifYouDo =>
    "you may sacrifice an artifact or discard a card. If you do, draw a card"
  | .«if» (.atLeast (.count .putEquipment) (.fixed 1)) (.attach .putArtifact .notedHost) =>
    "if it's an Equipment, attach it to this creature"
  | .fight who how =>
    match who, how with
    | .source, .mutual =>
      "this fights up to one other target creature"
    | .announced, .upToOneOther =>
      "target creature you control fights up to one other target creature"
    | .announced, .mutual =>
      "target creature you control fights another target creature"
    | .equipmentHost, .reflexive =>
      "that creature deals damage equal to its power to up to one target creature"
    | _, _ =>
      "fight"
  | .may (.pay (.sacrifice (.fixed 1) .another)) (.queueReflexive (.destroy .target)) .ifYouDo =>
    "you may sacrifice another creature. When you do, destroy target nonland permanent an opponent controls"
  | .may (.pay (.or [.sacrifice (.fixed 1) .artifact, .discard (.fixed 1) .nonland])) (.queueReflexive (.dealDamage (.fixed 2) .target)) .ifYouDo =>
    "you may sacrifice an artifact or discard a nonland card. When you do, this deals 2 damage to any target"
  | .revealFromHand count thenDo =>
    match count, thenDo with
    | .hand, .exile .target .untilSourceLeaves .none =>
      "choose target opponent and up to one target creature they control. They reveal their hand. You may exile a nonland card from their hand or the chosen creature until this leaves the battlefield"
    | .onePlusCreatureCards, .discard (.cards 1 (.target .opponent)) =>
      s!"{noun} reveals a number of cards from their hand equal to one plus the number of creature cards in your graveyard. You choose one of them. That player discards that card"
    | _, _ =>
      "reveal cards from their hand"
  | .or [.putCounters (.ofKind .plusOnePlusOne) .permanent, .returnToHand .graveyardCard] =>
    "choose one — • Put a +1/+1 counter on each of up to two target creatures. • Return target artifact or enchantment card from your graveyard to your hand"
  | .may (.tap .source) (.queueReflexive (.grant (.keywords k) .target)) .ifYouDo =>
    if k == Keyword.indestructible then
      "you may tap this creature. When you do, another target nonattacking creature you control gains indestructible until end of turn"
    else
      "you may tap this creature. When you do, that ability triggers"
  | .markRecentTokensAttacking =>
    "those tokens enter tapped and attacking"
  | .«if» (.atLeast (.count (.intersection [.equipped, .legendaryCreaturesYouControl])) (.fixed 1)) .markRecentTokensAttacking =>
    "those tokens are tapped and attacking if that creature is legendary"
  | .additionalCombatPhase =>
    "after this phase, there is an additional combat phase"
  | .«if» .youControlledDestroyed (.draw (.fixed 1)) =>
    "if you controlled that creature, draw a card"
  | .«if» .enduringStoryNoted (.dealDamage .discardedHand (.player .eachOpponent)) =>
    "if you have an enduring story, this deals X damage to each opponent"
  | .becomeBear =>
    "it becomes a Bear in addition to its other types"
  | .«if» ((.atLeast (.count (.youControl (.subtype .bear))) (.fixed 3))) (.draw (.fixed 2)) =>
    "if you control three or more Bears, draw two cards"
  | .tap .enchanted | .tap .enchantedWhileSource => "tap enchanted creature"
  | .tap .source => "tap this creature"
  | .tap (.target .whileSource) => "tap that creature"
  | .«if» ((.atLeast (.count .questCounters) (.fixed 6))) (.sequence [.sacrifice (.sacrificedSource .movedAsSacrificed), .searchLibrary (.put .dragon .asPrinted .none)]) =>
    "if it has six or more quest counters on it, sacrifice it and search for a Dragon"
  | .«if» .equipmentAttached (.fight .equipmentHost .reflexive) =>
    "that creature deals damage equal to its power to up to one target creature"
  | .queueReflexive (.mayCast .milledSpell .causingSpell .withoutPaying) =>
    "exile and copy a card"
  | .«if» .opponentsMilled (.queueReflexive (.mayCast .milledSpell .causingSpell .withoutPaying)) =>
    "when one or more cards are milled this way, exile and copy a card"
  | .loseLife amount who =>
    match amount, who with
    | .fixed n, .you => s!"you lose {n} life"
    | .fixed n, .target .opponent => s!"{noun} loses {n} life"
    | .fixed n, .eachOpponent => s!"each opponent loses {n} life"
    | .perBurden, .you =>
      "you lose 1 life for each burden counter on this"
    | .attachedEquipment, .eachOpponent =>
      "each opponent loses X life, where X is the number of Equipment attached to it"
    | _, _ =>
      "lose life"
  | .«if» .planWasSacrificed (.queueReflexive (.dealDamage (.fixed n) .target .divided)) =>
    s!"when you do, it deals {n} damage divided as you choose among one or two targets"
  | .queueReflexive (.dealDamage (.fixed n) .target .divided) =>
    s!"when you do, it deals {n} damage divided as you choose among one or two targets"
  | .«if» .planWasSacrificed (.queueReflexive _) =>
    "when you do, the reflexive ability triggers"
  | .«if» (.atLeast (.count (.othersOfSubtype .hero)) (.fixed 1)) (.gainLife (.fixed n)) =>
    s!"if you control another Hero, you gain {n} life"
  | .grantPlayNotedUntilNextTurn =>
    playThatCardUntilNextTurnPhrase
  | .tap (.target .ifPresent) =>
    "tap up to one target creature"
  | .tap .target =>
    s!"tap {noun}"
  | .tap _ =>
    "tap it"
  | .untap who =>
    match who with
    | .attackingCreatures => "untap all attacking creatures"
    | .target => s!"untap {affectedNoun .target noun}"
    | .source => s!"untap {affectedNoun .source noun}"
    | .enchanted => s!"untap {affectedNoun .enchanted noun}"
    | .target .whileSource => s!"untap {affectedNoun .targetWhileSource noun}"
    | .equipped => "untap equipped creature"
    | .firstThisTurn => "untap it"
    | _ => "untap it"
  | .«if» (.atLeast (.count (.target .creature)) (.fixed 1)) (.putCounters (.ofKind .plusOnePlusOne) .permanent) =>
    "put a +1/+1 counter on it if it's a creature"
  | .«if» (.atLeast (.count (.target .planeswalker)) (.fixed 1)) (.putCounters (.ofKind .loyalty) .permanent) =>
    "put a loyalty counter on it if it's a planeswalker"
  | .winTheGame =>
    "you win the game"
  | .«if» (.not (.atLeast .libraryCards (.fixed 1))) .winTheGame =>
    "if your library has no cards in it, you win the game"
  | .shuffleSource =>
    "its owner shuffles it into their library"
  | .«if» (.atLeast .libraryCards (.fixed 1)) .shuffleSource =>
    "Fblthp's owner shuffles him into their library"
  | .armSurveilReturnLifeGained =>
    "if you gained life this turn"
  | .becomeCopy .artifactEnchantmentOrLand =>
    "until your next turn, this becomes a copy of up to one target artifact, non-Aura enchantment, or land, except its name, and it's a legendary 4/4 Human Villain creature with vigilance"
  | .becomeCopy .creatureOrGraveyardCard =>
    "until your next turn, this becomes a copy of up to one target creature or creature card in a graveyard, except its name, and it's a legendary Human Mercenary Villain creature"
  | .becomeCopy .noted =>
    "enchanted creature becomes a copy of that creature until this Aura leaves the battlefield"
  | .becomeCopy (.cause none) =>
    "create a token that's a copy of the artifact that caused this"
  | .becomeCopy _ =>
    "become a copy"
  | .«if» (.atLeast (.count .harnessedSource) (.fixed 1)) (.exile .target .returnImmediately) =>
    "exile up to one other target nonland permanent you control, then return that card to the battlefield under its owner's control"
  | .retargetCause =>
    "choose new targets for that spell"
  | .copyCause =>
    "copy that spell. You may choose new targets for the copy"
  | .may (.exile .discarded .playUntilNextTurn) (.sequence []) .ifYouDo =>
    "you may exile that card from your graveyard. If you do, until the end of your next turn, you may play that card"
  | .may (.createTokens .wall04defender (.fixed 1) false) (.sequence []) .ifYouDo =>
    "you may create a 0/4 colorless Wall creature token with defender"
  | .may (.pay (.sacrifice _ _)) _ .ifYouDo =>
    "you may sacrifice that. If you do, do that"
  | .may (.pay (.discard _ _)) _ .ifYouDo =>
    "you may discard that. If you do, do that"
  | .may _ _ .ifYouDo =>
    "you may do it. If you do, do that"
  | .pay (.mana symbols) =>
    s!"pay {String.join (symbols.toList.map ManaSymbol.toNotation)}"
  | .pay _ =>
    "pay that cost"
  | .queueReflexive _ =>
    "when you do, that ability triggers"
  | .«if» .manaSpent (.discard (.cards n)) =>
    s!"discard {cardPhrase n}"
  | .«if» _ _ =>
    "if that is true"
  | .ifElse _ _ _ =>
    "if that is true"
  | .or _ =>
    "choose one"
  | r =>
    SpellResolution.toPhrase r noun

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

/-- Printed clause when the effect is a sequence of independent steps.
Numbers and the target noun come from the effect, so Oracle refill stays
in step with the printed line. -/
def sequenceClause (e : Effect) : Option String :=
  let noun := e.targetKind.noun
  match e.resolution with
  | .sequence [.draw 1, .loseLife 1] =>
    some "you draw a card and lose 1 life"
  | .sequence [.draw (.fixed n), .discard (.cards 1)] =>
    some s!"draw {cardPhrase n.toNat}, then discard a card"
  | .sequence [.onSource (.pump p 0), .teamGain k] =>
    if k == Keyword.trample then
      some s!"until end of turn, this creature gets {signedStat p}/+0 and creatures you control gain trample"
    else none
  | .sequence [.onPermanent (.plusOne n), .onPermanent (.grantKeywords k)] =>
    if k == Keyword.lifelink && n == 1 then
      some s!"put a +1/+1 counter on {noun}. It gains lifelink until end of turn"
    else if k == Keyword.vigilance then
      some s!"put {plusOnePlusOneCountersPhrase n} on {noun}. It gains vigilance until end of turn"
    else none
  | .sequence [.onSource (.pump 1 0), .onSource .cantBeBlocked] =>
    some "this gets +1/+0 until end of turn and can't be blocked this turn"
  | .sequence [.draw 1, .onSource (.plusOne 1)] =>
    some "draw a card and put a +1/+1 counter on this"
  | .sequence [.creaturesYouControlPump p 0, .teamGain k] =>
    if k == Keyword.firstStrike then
      some s!"creatures you control get {signedStat p}/+0 and gain first strike until end of turn"
    else none
  | .sequence [.onSource (.plusOne 1), .draw 1] =>
    some "put a +1/+1 counter on this and draw a card"
  | .sequence [.onSource (.pump p t), .damageEachOpponent n] =>
    some s!"this gets {signedStat p}/{signedStat t} until end of turn and deals {n} damage to each opponent"
  | .sequence
      [.onPermanent .untap,
       .«if» (.subtype subtype) (.onPermanent (.plusOne n))] =>
    some s!"untap {noun}. If that creature is a {subtype}, put {plusOnePlusOneCountersPhrase n} on it"
  | .sequence [.loseLife (.fixed n) .you, .createTokens .treasure 1 false] =>
    some s!"you lose {n} life and create a Treasure token"
  | .sequence [.exileCardFromGraveyard, .loseLife (.fixed n) .eachOpponent] =>
    some s!"exile up to one {noun}. Each opponent loses {n} life"
  | _ => none

/-- Printed sentence for a leftover dies trigger. Its resolution is a
`TriggerResolution` that does not carry `DeathLeftover`. -/
def deathSentence : DeathLeftover → String
  | .hellcatReturn =>
    "When Hellcat dies, return her to the battlefield under her owner's control with a +1/+1 counter on her. She loses all abilities and gains haste."
  | .villainReturnAsHero =>
    "Whenever a Villain you control dies, return it to the battlefield under its owner's control with a finality counter on it. That creature is a Hero in addition to its other types."
  | .attackingReturnHand =>
    "Whenever an attacking creature you control dies, return that card to its owner's hand."
  | .deathtouchOppSac =>
    "Whenever another creature you control with deathtouch dies, each opponent sacrifices a nontoken creature of their choice."

/-- Printed sentence for a leftover “enters or attacks” trigger.
Its resolution is a `TriggerResolution` that does not carry
`EnterOrAttackLeftover`. -/
def enterOrAttackSentence : EnterOrAttackLeftover → String
  | .copyKeywords =>
    "Whenever Super-Adaptoid enters or attacks, choose another target creature. If that creature has haste and Super-Adaptoid doesn't, put a haste counter on Super-Adaptoid. Do the same for flying, first strike, double strike, deathtouch, indestructible, lifelink, menace, reach, trample, and vigilance."
  | .createSquirrel =>
    "Do You Like Squirrels? — Whenever The Unbeatable Squirrel Girl enters or attacks, create a 1/1 green Squirrel creature token."

/-- Printed sentence for a leftover “whenever this attacks” trigger.
Its resolution is a `TriggerResolution` that does not carry
`ThisAttackLeftover`. -/
def thisAttackSentence : ThisAttackLeftover → String
  | .mayPayPlusOne =>
    "Whenever Ant-Man attacks, you may pay {1}. When you do, put a +1/+1 counter on target creature."
  | .payReturnAttacking =>
    "Whenever Grim Reaper attacks, you may pay {3}{B}. When you do, return target creature card from your graveyard to the battlefield tapped and attacking with a finality counter on it."
  | .ifArtifactEnteredDraw =>
    "Whenever Iron Man attacks, if an artifact entered the battlefield under your control this turn, draw a card."
  | .blinkNontoken =>
    "Whenever The Mighty Thor attacks, exile up to one target nontoken artifact or creature, then return that card to the battlefield tapped under its owner's control."
  | .equippedDrain =>
    "Whenever Whiplash attacks, if he's equipped, each opponent loses X life and you gain X life, where X is the number of Equipment attached to him."
  | .drawIfPower4 =>
    "Cybernetic Senses — Whenever Viv Vision attacks, draw a card if her power is 4 or greater."
  | .attacksAlonePlus2Indestructible =>
    "Unbreakable Skin — Whenever Luke Cage attacks alone, he gets +2/+0 and gains indestructible until end of turn."

/-- Printed sentence for a leftover “whenever you attack” trigger.
Its resolution is a `TriggerResolution` that does not carry
`YouAttackLeftover`. -/
def youAttackingSentence : YouAttackLeftover → String
  | .pay2LifeToughness =>
    "Whenever you attack, you may pay 2 life. If you do, until end of turn, creatures you control with toughness greater than their power assign combat damage equal to their toughness rather than their power."
  | .exileTopHeroPump =>
    "Whenever you attack, you may exile the top card of your library. If that card is a Hero card, Daredevil gets +2/+1 until end of turn. You may play that card this turn."
  | .lookSixCast =>
    s!"Whenever you attack, look at the top six cards of your library. You may cast a spell from among them with mana value less than or equal to the greatest power among attacking creatures you control without paying its mana cost. {restOnBottomRandomPhrase}."

/-- Printed sentence for a leftover draw, discard, life, or +1/+1-counter
trigger. Its resolution is a `TriggerResolution` that does not carry
`ResourceLeftover`. -/
def resourceSentence : ResourceLeftover → String
  | .discardExilePlay =>
    "Whenever you discard a card, you may exile that card from your graveyard. If you do, until the end of your next turn, you may play that card."
  | .drawIfAnotherHeroDamage =>
    "Whenever you draw a card, if you control another Hero, Human Torch deals 1 damage to target opponent."
  | .secondDrawBecome66 =>
    "Whenever you draw your second card each turn, until end of turn, Moon Girl and Devil Dinosaur's base power and toughness become 6/6 and they gain trample."
  | .secondDrawPlusOneTarget =>
    "Whenever you draw your second card each turn, put a +1/+1 counter on target creature."
  | .secondDrawDrain =>
    "Whenever you draw your second card each turn, each opponent loses 1 life and you gain 1 life."
  | .gainLifePlusOnes =>
    "Whenever you gain life, choose up to that many target creatures you control. Put a +1/+1 counter on each of them."
  | .plusOneCreateInsectOnce =>
    "Whenever you put a +1/+1 counter on a creature, create a 1/1 green Insect creature token. This ability triggers only once each turn."
  | .plusOneOnThisOnce =>
    "Whenever you put a +1/+1 counter on another creature, put a +1/+1 counter on this creature. This ability triggers only once each turn."
  | .plusOneOnHeroesCreateWall =>
    "Whenever you put one or more +1/+1 counters on one or more other Heroes you control, you may create a 0/4 colorless Wall creature token with defender."

/-- Printed sentence for a leftover “whenever you cast …” trigger.
Its resolution is a `TriggerResolution` that does not carry `CastLeftover`. -/
def castingSentence : CastLeftover → String
  | .villainToken =>
    "Whenever you cast a Villain spell, create a 2/1 black Villain creature token with menace."
  | .merfolkFromBlue =>
    "Whenever you cast a noncreature spell with one or more blue mana symbols in its mana cost, create that many 1/1 blue Merfolk creature tokens."
  | .mayPayHasteUnblockable =>
    "Whenever you cast a noncreature spell, you may pay {1}. When you do, target creature with haste can't be blocked this turn except by creatures with haste."
  | .plusOneEachOther =>
    "Whenever you cast a noncreature spell, put a +1/+1 counter on each other creature you control."
  | .exileFlicker =>
    "Whenever you cast a noncreature spell, exile another target nonland, nontoken permanent. Return that card to the battlefield under its owner's control at the beginning of the next end step."
  | .visionModes =>
    "Whenever you cast a noncreature spell, choose one that hasn't been chosen this turn — • Solar Beam — The Vision gains double strike until end of turn. • Density Control — The Vision gains indestructible until end of turn. • Technopathy — Draw a card."
  | .damageEqualMv =>
    "Whenever you cast a noncreature spell, Thor deals damage equal to that spell's mana value to any target."
  | .drawPowerEqualHand =>
    "Whenever you cast a spell that targets a creature you control, draw a card. Until end of turn, Ms. Marvel gains \"Ms. Marvel's base power is equal to the number of cards in your hand.\""
  | .plusOneThis =>
    "Whenever you cast a spell that targets a creature you control, put a +1/+1 counter on Mockingbird."
  | .plusOneScry =>
    "Whenever you cast a spell that targets a creature you control, put a +1/+1 counter on Colleen Wing. Scry 1."
  | .ironFistTap =>
    "Whenever you cast a spell that targets a creature you control, Iron Fist gains \"{T}: Iron Fist deals damage equal to his power to any other target\" until end of turn."
  | .targetsGainFlying =>
    "Whenever you cast a spell that targets one or more creatures, those creatures gain flying until end of turn."
  | .copyIfArtifactOrLand =>
    "Whenever you cast an instant or sorcery spell that targets an artifact or land, copy that spell. You may choose new targets for the copy. Put two +1/+1 counters on Fin Fang Foom."
  | .tapCreatureOrLand =>
    "Seismic Takedown — Whenever you cast a noncreature spell, tap target creature or land."

/-- Printed sentence for a leftover watch trigger. Its resolution is a
`TriggerResolution` that does not carry `WatchLeftover`. -/
def watchSentence : WatchLeftover → String
  | .combatDamageExileUntilNonland =>
    "Whenever Black Widow deals combat damage to a player, that player exiles cards from the top of their library until they exile a nonland card. You may put a +1/+1 counter on Black Widow. If you don't, you may cast the exiled nonland card until end of turn and mana of any type can be spent to cast that spell."
  | .attacksAloneDrain =>
    "Whenever a creature you control attacks alone, target opponent loses 1 life and you gain 1 life."
  | .attacksAloneFirstStrikeMenace =>
    "Whenever a creature you control attacks alone, it gains first strike and menace until end of turn."
  | .firstTapUntap =>
    "Whenever a creature you control becomes tapped during your turn, if it's the first time that creature has become tapped this turn, untap it."
  | .sheHulkRedirectOnce =>
    "Whenever a creature you control is dealt damage, you may have The Sensational She-Hulk deal that much damage to any target. Do this only once each turn."
  | .speedballTargeted =>
    "Whenever a player casts a spell that targets Speedball, he gets +2/+2 until end of turn. You may choose new targets for that spell."
  | .anyPlayerSecondDraw =>
    "Whenever a player draws their second card each turn, you draw a card."
  | .youTargetDrawOnce =>
    "Whenever a player or permanent becomes the target of an ability you control, draw a card. This ability triggers only once each turn."
  | .villainOrArtifactDamage =>
    "Whenever another Villain and/or artifact you control enters, this creature deals 1 damage to target opponent."
  | .villainConniveOnce =>
    "Whenever another Villain you control enters, you may have it connive. Do this only once each turn."
  | .villainPlusOneDamageOnce =>
    "Whenever another Villain you control enters, put a +1/+1 counter on Crossbones. He deals 2 damage to each opponent. This ability triggers only once each turn."
  | .villainAttachEquipment =>
    "Whenever another Villain you control enters, attach up to one target Equipment you control to target creature you control."
  | .villainPlusOneLifelink =>
    "Whenever another Villain you control enters, Yellowjacket gets +1/+0 and gains lifelink until end of turn."
  | .hulklingCompare =>
    "Whenever another creature you control enters, if it has greater power or toughness than Hulkling, put a +1/+1 counter on Hulkling."
  | .justiceBounce =>
    "Whenever another nonland permanent you control is returned to its owner's hand, put a +1/+1 counter on Justice."
  | .nontokenHeroModal =>
    "Whenever another nontoken Hero you control enters, choose one — • Create a 1/1 white Soldier creature token. • Creatures you control get +1/+1 until end of turn."
  | .ultronCopy =>
    "Whenever another nontoken artifact you control enters, you may pay {2}. If you do, create a token that's a copy of it. If the token isn't a creature, it becomes a 2/2 Robot Villain creature in addition to its other types."
  | .enchantedAttachEquipment =>
    "Whenever enchanted creature attacks or blocks, attach any number of target Equipment you control to it."
  | .equippedAttacksAloneUntapScry =>
    "Whenever equipped creature attacks alone, untap it and scry 1."
  | .equippedAttacksTap =>
    "Whenever equipped creature attacks, tap target creature defending player controls."
  | .equippedTappedDamage =>
    "Whenever equipped creature becomes tapped, it deals 1 damage to each opponent."
  | .heroesDamagePlusTwo =>
    "Whenever one or more Heroes you control deal damage to a player, put two +1/+1 counters on The Thing."
  | .merfolkAttackDraw =>
    "Whenever one or more Merfolk you control attack a player, draw a card."
  | .tokensEnterMayDraw =>
    "Whenever one or more tokens you control enter, you may draw a card."
  | .hawkeyeModes =>
    "Trick Arrows — Whenever Hawkeye becomes tapped, you may pay {1} up to three times. When you do, choose up to that many — • Net — Target creature can't block this turn. • Explosive — Hawkeye deals 2 damage to target player. • Boomerang — Discard a card, then draw a card."
  | .redHulk =>
    "Enrage — Whenever Red Hulk is dealt damage, put a +1/+1 counter on him. When you do, he deals damage equal to the number of +1/+1 counters on him to any other target."
  | .hulk =>
    "Enrage — Whenever The Incredible Hulk is dealt damage, put a +1/+1 counter on him. If he's attacking, untap him and there is an additional combat phase after this phase."

/-- Printed sentence for a leftover step trigger. Its resolution is a
`TriggerResolution` that does not carry `StepLeftover`. -/
def stepSentence : StepLeftover → String
  | .enchantedControllerDraws =>
    "At the beginning of the upkeep of enchanted creature's controller, that player draws a card."
  | .drawToTen =>
    "At the beginning of your end step, if you have fewer than ten cards in hand, draw cards equal to the difference."
  | .copyAbsorbingMan =>
    "At the beginning of your first main phase, until your next turn, Absorbing Man becomes a copy of up to one target artifact, non-Aura enchantment, or land, except his name is Absorbing Man, he's a legendary 4/4 Human Villain creature in addition to his other types, and he has vigilance."
  | .hydeChoose =>
    "At the beginning of your upkeep, choose one — • Put a +1/+1 counter on Mister Hyde. • Remove a counter from a creature you control. If you do, draw a card."
  | .copyTaskmaster =>
    "Photographic Reflexes — At the beginning of your first main phase, until your next turn, Taskmaster becomes a copy of up to one target creature on the battlefield or creature card in a graveyard, except his name is Taskmaster, Mercenary Mimic and he's a legendary Human Mercenary Villain creature."
  | .harnessedFlicker =>
    "∞ — At the beginning of your end step, exile up to one other target nonland permanent you control, then return that card to the battlefield under its owner's control."

def toNotation (ab : TriggeredAbility) : String :=
  match ab with
  | .triggered w e opts =>
    if !opts.printed.isEmpty then opts.printed else
    match w, e.asTrigger?, opts with
    | .sagaChapter, some (.chapter _ _), _ =>
      s!"When a lore counter is put on this Saga, {e.phrase}."
    | .enter, some .bolgMaySacrifice, _ =>
      leadInSentence ab "When Bolg enters"
    | .combatDamageToPlayer, some .createTreasuresEqualDamagedPlayerArtifacts, _ =>
      leadInSentence ab "Whenever this creature deals combat damage to a player"
    | .enterOrOpponentDrawsExceptFirst, some .deal1ThenAmassOrcs, _ =>
    "When this creature enters and whenever an opponent draws a card except the first one they draw in each of their draw steps, this creature deals 1 damage to any target. Then amass Orcs 1."
    | .eachUpkeep, some (.createTokens k n), _ =>
    s!"At the beginning of each player's upkeep, you {TokenKind.createPhrase k n}."
    | .eachOpponentDrawStep, some (.draw 1), _ =>
    "At the beginning of each opponent's draw step, you draw a card."
    | .youGainLife, some .loyaltyOnSource, _ =>
    "Whenever you gain life, put a loyalty counter on Ajani."
    | .opponentDrawsSecond, some (.createTokens .treasure 1), _ =>
    "Whenever an opponent draws their second card each turn, you create a Treasure token."
    | .youAttackWithTotalPower, some (.untapAttackersExtraCombat n), _ =>
      leadInSentence ab
        s!"Whenever you attack with creatures with total power {n} or greater for the first time each turn"
    | .anotherCreatureYouControlEnters, some .allianceMode, _ =>
      leadInSentence ab "Alliance — Whenever another creature you control enters"
    | .enter, some .destroyOtherAmassControllerPower, _ =>
    "When Azog enters, destroy up to one other target creature. Its controller amasses Goblins X, where X is that creature's power. If you controlled that creature, draw a card."
    | .combatDamageToPlayerOrBattle, some (.createTokens .treasure 2), { watchedSubtype := some .dwarf, .. } =>
      leadInSentence ab "Whenever a Dwarf you control deals combat damage to a player or battle"
    | (.youCastColor .red), some (.damageEachOpponent 3), _ =>
    "Whenever you cast a red spell, Aragorn deals 3 damage to target opponent."
    | .enter, some .returnCreatureFromGyToHand, _ =>
    "When this enchantment enters, return target creature card from your graveyard to your hand."
    | .thisOrAnotherSubtypeEnters, some .discardHandDrawDamageIfStory, { thisOrAnotherSubtype := some .dwarf, .. } =>
    "Whenever Balin or another Dwarf you control enters, you may discard your hand. Draw X cards, where X is the number of cards discarded this way. If you have an enduring story, Balin deals X damage to each opponent."
    | .attack, some .castFromGyArtifactInstantSorcery, _ =>
      leadInSentence ab "Whenever Bilbo attacks"
    | .enter, some (.createAxe true), _ =>
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
    | .anotherCreatureYouControlEnters, _, { thisOrAnotherSubtype := some .elf, anotherSupertype := some .legendary, .. } =>
    "Whenever another legendary Elf you control enters, draw two cards, then discard a card."
    | .dies, some .returnAsArtifact, _ =>
      leadInSentence ab "When Tom, Bert, and William die"
    | .anotherCreatureYouControlEnters, some (.onSource (.plusOne 2)), { thisOrAnotherSubtype := some .wolf, .. } =>
    "Whenever another Wolf you control enters, put two +1/+1 counters on Chief of the Wilds."
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
    | .enter, some (.connive .source), _ =>
      leadInSentence ab "When this creature enters"
    | .eachEndStep, some (.drawIfAttackedOrEnteredSubtype subtype), _ =>
    let a := if subtype == .hero then "a Hero" else s!"a {subtype}"
    s!"At the beginning of each end step, if you attacked with {a} this turn or {a} entered the battlefield under your control this turn, draw a card."
    | .attack, some (.othersOfSubtypeGetEqualSourceToughness subtype), _ =>
    s!"Whenever this attacks, each other {subtype} you control gets +X/+X until end of turn, where X is this toughness."
    | (.youCastColorFromHand color), some (.connive .source), _ =>
    s!"Whenever you cast a {color} spell from your hand, this connives."
    | .sourceDealtDamage, some (.onSource (.plusOne 1)), _ =>
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
    | .enter, some (.opponentDiscards n .target), _ =>
    let cards := if n == 2 then "two cards" else cardPhrase n
    s!"When this enchantment enters, target opponent discards {cards}."
    | .enter, some (.enter (.dealDamageUpToOne n)), _ =>
    s!"When this permanent enters, it deals {n} damage to up to one target creature."
    | _, some (.step e), _ => stepSentence e
    | _, some (.death e), _ => deathSentence e
    | _, some (.thisAttack e), _ => thisAttackSentence e
    | _, some (.enterOrAttack e), _ => enterOrAttackSentence e
    | _, some (.watch e), _ => watchSentence e
    | _, some (.youAttacking e), _ => youAttackingSentence e
    | _, some (.casting e), _ => castingSentence e
    | _, some (.resource e), _ => resourceSentence e

    | _, _, _ =>
    let t := ab.timing
    if t.events.contains .equippedAttacksAlone then
      "Whenever equipped creature attacks alone, you draw a card and you lose 1 life."
    else if t.events.contains .landYouControlEnters &&
        ab.effect.resolution == .sequence [.draw 1, .onSource (.plusOne 1)] then
      "Landfall — Whenever a land you control enters, draw a card and put a +1/+1 counter on Gandalf."
    else
      let once :=
        if t.onceEachTurn then " This ability triggers only once each turn." else ""
      let clause := (sequenceClause ab.effect).getD (resolutionPhrase t)
      s!"{eventPrefix t}{interveningClause t}, {clause}.{once}"

instance : ToString TriggeredAbility where
  toString := toNotation

end TriggeredAbility

namespace TriggeredAbility

/-- An FRA triggered ability with its printed sentence. -/
def fra (w : SharedTriggerWhen) (printed : String) (r : Resolution)
    (kind : EffectTargetKind := .none) (allowsZeroTargets := false) (maxTargets := 0)
    (once := false) (cond : FraCondition := .none) : TriggeredAbility :=
  .triggered w { targeting := .of kind, resolution := r, phrase := printed
                 allowsZeroTargets, maxTargets }
    { printed, onceEachTurn := once, fraCondition := cond, allowsZeroTargets }

end TriggeredAbility

end Mtg.Engine
