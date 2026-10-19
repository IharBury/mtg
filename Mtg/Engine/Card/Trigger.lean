import Mtg.Engine.Card.Counter
import Mtg.Engine.Card.Effect
import Mtg.Engine.Card.TriggerEvent

/-!
# Triggered-ability core (CR 603)

The unified `TriggeredAbility` carrier plus its stack/resolution metadata:
`TriggerTiming`, the events each shared trigger watches, and the timing of
each shared trigger. `TriggerResolution` names `Resolution`.
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



/-- When a triggered ability fires, how it targets, optional divided-damage
parameters, and how it resolves (CR 603 / 601.2d / 608). Adding a constructor
only requires updating `timing` instead of parallel match trees. -/
structure TriggerTiming where
  events : Array TriggerEvent := #[]
  targeting : EffectTargeting := .of .none
  /-- Zero targets is a legal announcement (CR 115.1c / 601.2c), e.g. “up to one”. -/
  allowsZeroTargets : Bool := false
  /-- Most targets one instance of “target” may take (“any number of target
  …”); 0 means the targeting's own count. -/
  maxTargets : Nat := 0
  /-- Damage amount and maximum number of targets when this ability divides
  damage as the controller chooses (CR 601.2d). -/
  dividedDamage : Option (Nat × Nat) := none
  /-- What happens when this ability resolves. -/
  resolution : TriggerResolution := .pump .greatestPower (.fixed 0) .source
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

/-- Targeting and resolution for a printed Saga chapter (CR 714.3).
The chapter is still stored as `ChapterResolution`. What resolves is one
of these `TriggerResolution` constructors. -/
def chapterTiming (e : ChapterResolution) : TriggerTiming :=
  match e with
  | .dealDamageToOppCreature n =>
    { targeting := .of .oppCreature, resolution := .dealDamage (.fixed n) .target }
  | .destroyOppArtifact =>
    { targeting := .of .oppArtifact, resolution := .destroy .target }
  | .addMana mana =>
    { resolution := .addMana #[mana] }
  | .searchBasicLandToHand =>
    { resolution := .searchLibrary (.returnToHand .basicLand) }
  | .gainLandfallCreateElf =>
    { resolution := .grant .landfallCreateElf .source }
  | .elvesGetVigilance p =>
    { resolution := .sequence [
        .pump (.fixed p) (.fixed 0) (.intersection [.creaturesYouControl, .youControl (.subtype "Elf")]),
        .grant (.keywords Keyword.vigilance) (.intersection [.creaturesYouControl, .youControl (.subtype "Elf")])] }
  | .opponentDiscardsNonland =>
    { targeting := .of .opponent
      resolution := .discard .chosenNonland }
  | .amass n =>
    { resolution := .amass (.fixed n) }
  | .opponentLosesYouGain n =>
    { targeting := .of .opponent
      resolution := .sequence [.loseLife (.fixed n) (.target .opponent), .gainLife (.fixed n)] }
  | .grantHexproofWhileRemains =>
    { targeting := .of .creatureYouControl
      resolution := .grant .hexproofWhileSource .target }
  | .preventDamageWhileRemains =>
    { targeting := .of .creature, allowsZeroTargets := true
      resolution := .grant .preventDamageWhileSource .target }
  | .draw n =>
    { resolution := .draw (.fixed n) }
  | .searchBasicPlainsExileGainLife max life =>
    { resolution := .sequence [
        .searchLibrary (.exile (.basicUpTo "Plains" max) .forLater .linked),
        .gainLife (.fixed life)] }
  | .returnLinkedExileToHand =>
    { resolution := .returnToHand .linkedExile }
  | .grantAttackPumpPerPlainsThisTurn =>
    { resolution := .queueReflexive (.pump .perPlains .perPlains .target) }
  | .blinkUntilEndStep =>
    { targeting := .of .creatureOrLandYouControl, allowsZeroTargets := true
      resolution := .exile .target .nextEndStep }
  | .treasureThenDragonIfFour =>
    { resolution := .sequence [
        .createTokens .treasure (.fixed 1) false,
        .«if» ((.atLeast (.count (.youControl (.subtype "Treasure"))) (.fixed 4)))
          (.sacrifice (.sacrificedSource .isSacrificed) .noted),
        .«if» .sourceWasSacrificed (.createTokens .dragon (.fixed 1) false)] }
  | .recruit =>
    { resolution := .recruit }
  | .returnCreatureFromGyMvAtMost n =>
    { targeting := .of (.creatureCardInYourGraveyardMvAtMost n)
      resolution := .put (.creatureMvAtMost n) }
  | .plusOneUpToOne =>
    { targeting := .of .creature, allowsZeroTargets := true
      resolution := .putCounters (.ofKind .plusOnePlusOne) .permanent }
  | .gainControlOfUpToTwoCreaturesTotalMvAtMost n =>
    { targeting := .of (.upToTwoCreaturesTotalMvAtMost n), allowsZeroTargets := true
      resolution := .gainControl .whileSourceRemains }
  | .dealDamageToEachNonSubtypeAndOpponents n subtype =>
    { resolution := .dealDamage (.fixed n) (.eachNonSubtypeAndOpponents subtype) }
  | .dealXDamageToTargetOpponentGreatestArtifactMv =>
    { targeting := .of .opponent
      resolution := .dealDamage .greatestArtifactMv (.player (.target .opponent)) }
  | .spell s =>
    { targeting := s.targeting, allowsZeroTargets := s.allowsZeroTargets
      resolution := TriggerResolution.ofSpell s.resolution }

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
  | .youCastFirstNoncreature => #[.youCastFirstNoncreature]
  | .youCastSpell => #[.youCastSpell]
  | .youCastTargetingOpponentOrTheirCreature => #[.youCastTargetingOpponentOrTheirCreature]
  | .youActivateLoyaltyAbility => #[.youActivateLoyaltyAbility]
  | .eachUpkeep => #[.eachUpkeep]
  | .youScryOrSurveil => #[.youScryOrSurveil]
  | .opponentsDealtCombatDamageYourTurn => #[.opponentsDealtCombatDamageYourTurn]
  | .creatureYouControlDies => #[.creatureYouControlDies]
  | .eachOpponentDrawStep => #[.eachOpponentDrawStep]
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
  | .fra e => #[.fra e]

end SharedTriggerWhen

namespace SharedTrigger

/-- Targeting, divided-damage parameters, and resolution for this shared effect. -/
def timing : SharedTrigger → TriggeredAbility.TriggerTiming
  | .scry n => { resolution := .scry (.fixed n) }
  | .draw n => { resolution := .draw (.fixed n) }
  | .createTokens kind n tapped => { resolution := .createTokens kind (.fixed n) tapped }
  | .amass n subtype amount attachSource =>
    let resolved : TriggeredAbility.NumberSelector :=
      match amount with
      | .fixed => .fixed n
      | .sourcePower => .lastKnownPower
      | .notedExcess => .notedExcess
      | .notedPower => .notedPower
    { resolution := .amass resolved subtype attachSource }
  | .recruit who => { resolution := .recruit who }
  | .dividedDamage amount maxTargets =>
    { targeting := .of .playerOrCreature,
      dividedDamage := some (amount, maxTargets), resolution := .dividedDamage }
  | .gainLife n => { resolution := .gainLife (.fixed n) }
  | .connive who =>
    match who with
    | .source => { resolution := .connive .source }
    | .target kind => { targeting := .of kind, resolution := .connive .target }
    | .enteringVillain => { resolution := .connive .enteringVillain }
  | .exileUntilLeaves kind =>
    { targeting := .of kind, resolution := .exile .target .untilSourceLeaves }
  | .damageEachOpponent n =>
    { targeting := .of .opponent, resolution := .dealDamage (.fixed n) (.player .eachOpponent) }
  | .attachTo kind =>
    { targeting := .of kind, resolution := .attach .source .target }
  | .opponentSacrificesCreature =>
    { targeting := .of .opponent,
      resolution := .sacrifice .opponentChosenCreature }
  | .onPermanent kind action =>
    { targeting := .of kind
      resolution := TriggeredAbility.TriggerResolution.ofPermanent action }
  | .onSource action =>
    { resolution := TriggeredAbility.TriggerResolution.ofSource action }
  | .exileTop => { resolution := .exile .top .playUntilNextTurn }
  | .discard n => { resolution := .discard (.cards n) }
  | .mayTo can thenDo =>
    let left := timing can
    let right := timing thenDo
    { targeting :=
        if left.targeting.kind == .none then right.targeting else left.targeting
      allowsZeroTargets := left.allowsZeroTargets || right.allowsZeroTargets
      maxTargets :=
        if left.targeting.kind == .none then right.maxTargets else left.maxTargets
      dividedDamage :=
        match left.dividedDamage with
        | some d => some d
        | none => right.dividedDamage
      resolution := .may left.resolution right.resolution .ifYouDo }
  | .may action =>
    let inner := timing action
    { inner with resolution := .may inner.resolution (.sequence []) }
  | .opponentDiscards n who =>
    match who with
    | .each => { resolution := .discard (.cards n .eachOpponent) }
    | .target =>
      { targeting := .of .opponent, resolution := .discard (.cards n (.target .opponent)) }
  | .millPlayer n =>
    { targeting := .of .player, resolution := .mill (.fixed n) (.target .player) }
  | .investigate => { resolution := .investigate }
  | .pumpCause p t => { resolution := .pump (.fixed p) (.fixed t) .cause }
  | .searchLibrary => { resolution := .searchLibrary (.put .forest) }
  | .searchBasicLandToHand =>
    { resolution := .searchLibrary (.returnToHand .basicLand) }
  | .eachPlayerSacrificesCreature =>
    { resolution := .sacrifice .eachPlayersCreature }
  | .exileTarget kind =>
    { targeting := .of kind, resolution := .exile .target .leaveTrigger }
  | .returnCreatureFromGyToHand =>
    { targeting := .of .creatureCardInYourGraveyard,
      resolution := .returnToHand .graveyardCard }
  | .plusOneEachYouControl which =>
    { resolution := .putCounters (.ofKind .plusOnePlusOne) (.youControl which) }
  | .honeEachEquipment => { resolution := .putCounters (.ofKind .hone 1) (.youControl (.subtype "Equipment")) }
  | .plusOneEachOtherGainLife =>
    { resolution := .sequence
        [.putCounters (.ofKind .plusOnePlusOne) .eachOther,
         .gainLife .perOtherCreature] }
  | .becomePT p t => { resolution := .becomePT (.fixed p) (.fixed t) }
  | .pumpTargetPerPlains =>
    { targeting := .of .creatureYouControl, resolution := .pump .perPlains .perPlains .target }
  | .mayDiscardHandDraw n =>
    { resolution := .may (.discard .hand) (.draw (.fixed n)) .ifYouDo }
  | .pumpByLookedAt => { resolution := .pump .perLookedAt .perLookedAt .source }
  | .pumpGreatestPower => { resolution := .pump .greatestPower (.fixed 0) .source }
  | .pumpForEachOtherCreature =>
    { resolution := .pump .perOtherCreature .perOtherCreature .source }
  | .damageBlockers n => { resolution := .dealDamage (.fixed n) .blockers }
  | .returnLinkedExile => { resolution := .put .linkedExile }
  | .createThenAttach kind =>
    { resolution := .sequence [.createTokens kind (.fixed 1) false, .attach .source .createdToken] }
  | .gainLifeSearchBasicOnTop n =>
    { resolution := .sequence [.gainLife (.fixed n), .searchLibrary (.put .basicLandOnTop)] }
  | .addMana types => { resolution := .addMana types }
  | .createAxe attach =>
    { resolution :=
        .createTokens .treasure (.fixed 1) false .axe
          (note := if attach then .attachReflexive else .none) }
  | .tapOppOrUntapYours =>
    { resolution := .or [.tap .target, .untap] }
  | .gainControlOppUntilEot =>
    { targeting := .of .oppCreature, resolution := .gainControl .untilEndOfTurn }
  | .payReturnFromGy =>
    { resolution := .may
        (.pay (.mana #[.generic 1, .colored .green, .colored .blue])) (.returnToHand .source) .ifYouDo }
  | .targetOpponentLosesLife n =>
    { targeting := .of .opponent, resolution := .loseLife (.fixed n) (.target .opponent) }
  | .drawXDiscard n =>
    { resolution := .sequence
        [.draw .equalToManaSpent, .«if» .manaSpent (.discard (.cards n))] }
  | .ringTempts => { resolution := .ringTempts }
  | .setOtherBasePT =>
    { targeting := .of .anotherCreatureYouControl, allowsZeroTargets := true,
      resolution := .setBasePT .equalSourcePower .equalSourceToughness }
  | .returnElfGainLife =>
    { targeting := .of .elfInYourGraveyard
      resolution := .sequence
        [.returnToHand .graveyardCard, .gainLife .equalToTargetPower] }
  | .damageFromLastKnownPower =>
    { targeting := .of .oppCreature,
      resolution := .dealDamage .lastKnownPower .permanent }
  | .mayPayGenericDraw n plusOne =>
    { resolution :=
        if plusOne then
          .may (.pay (.mana #[.generic n]))
            (.sequence [.putCounters (.ofKind .plusOnePlusOne) .source, .draw (.fixed 1)]) .ifYouDo
        else
          .may (.pay (.mana #[.generic n])) (.draw (.fixed 1)) .ifYouDo }
  | .drawThenBottomIfNoLegendary =>
    { resolution := .sequence
        [.draw (.fixed 1), .«if» (.not (.atLeast (.count .legendaryCreaturesYouControl) (.fixed 1))) (.putOnLibrary .bottom .cardFromHand)] }
  | .removeHopeDrawSac =>
    { resolution := .sequence
        [.removeCounters .hope .source, .«if» .removedHope (.draw (.fixed 1)), .«if» (.not .hopeOnSource) (.sequence [.sacrifice .source, .gainLife (.fixed 4)])] }
  | .tapHumansDraw =>
    { resolution := .sequence
        [.may (.tap .humans) (.sequence []), .draw .forEachTappedHuman] }
  | .destroyOppArtifactsEnchantmentsGainLife =>
    { resolution := .sequence
        [.destroy .oppArtifactsEnchantments (note := .countDestroyed),
         .gainLife .forEachDestroyedThisWay] }
  | .damageEqualSubtypeToEachOpponent subtype =>
    { resolution := .dealDamage (.subtypeCount subtype) (.player .eachOpponent) }
  | .damageEqualTreasures =>
    { targeting := .of .playerOrCreature,
      resolution := .dealDamage (.subtypeCount "Treasure") .target }
  | .dealDamageDestroyIfSubtype n subtype =>
    { targeting := .of .playerOrCreature,
      resolution := .sequence
        [.dealDamage (.fixed n) .target .markedPermanent,
         .«if» (.dealtDamageToSubtype subtype) (.destroy .permanentDealtDamage)] }
  | .attachEquipmentToCreature =>
    { targeting := .of .equipmentYouControlThenCreatureYouControl,
      allowsZeroTargets := true, resolution := .attach .target .optionalCreature }
  | .defenderSacsLeastPower =>
    { resolution := .sacrifice .leastPower }
  | .returnOtherPlusOne =>
    { targeting := .of (.filtered { noun := "up to one other target permanent you control"
                                    controller := .you, another := true })
      allowsZeroTargets := true
      resolution := .sequence
        [.returnToHand .permanent .returnedPermanent,
         .«if» .returnedPermanent (.putCounters (.ofKind .plusOnePlusOne) .source)] }
  | .lookAtTopRevealTypes n types =>
    { resolution := .lookAtTopRevealTypes (.fixed n) types }
  | .createTappedTreasuresEqualOppArtifacts =>
    { resolution := .createTokens .treasure .oppArtifacts true }
  | .putNonlandMvAtMostFromGy mv =>
    { targeting := .of (.filtered
        { noun := s!"up to one target nonland permanent card with mana value {mv} or less from a graveyard"
          zone := .anyGraveyard, permanentCard := true, nonland := true, mvAtMost := some mv })
      allowsZeroTargets := true, resolution := .put (.nonlandMvAtMost mv) }
  | .othersGetAndOppsGet subtypes p t oppP oppT =>
    { resolution := .sequence
        [.pump (.fixed p) (.fixed t) (.intersection [.creaturesYouControl, .union (subtypes.toList.map .othersOfSubtype)]),
         .pump (.fixed oppP) (.fixed oppT) .opponentsCreatures] }
  | .wolfPlusOneOrTreasure =>
    { resolution := .or
        [.putCounters (.ofKind .plusOnePlusOne) .permanent,
         .createTokens .treasure (.fixed 1) false] }
  | .trampleCounterBecomeBear =>
    { targeting := .of .creatureYouControl, allowsZeroTargets := true,
      resolution := .sequence
        [.putCounters (.ofKind .trample) .permanent, .grant .bearType .target, .«if» ((.atLeast (.count (.youControl (.subtype "Bear"))) (.fixed 3))) (.draw (.fixed 2))] }
  | .millThenSubtypeToHand n subtype =>
    { resolution := .sequence
        [.mill (.fixed n) (note := .milledCards), .returnToHand (.milledSubtype subtype)] }
  | .exileOppNonlandEachUntilLeaves =>
    { targeting := .of (.filtered
        { noun := "for each opponent, up to one target nonland permanent that player controls"
          nonland := true, controller := .eachOpponent })
      allowsZeroTargets := true
      resolution := .exile (.target .eachPermanent) .untilSourceLeaves }
  | .plusOneEqualLastKnownMv =>
    { targeting := .of .creatureYouControl,
      resolution := .putCounters .plusOneLastKnownMv .permanent }
  | .mountainQuestDragon =>
    { resolution := .sequence [.putCounters (.ofKind .quest) .source, .«if» ((.atLeast (.count .questCounters) (.fixed 6))) (.sequence [.sacrifice (.sacrificedSource .movedAsSacrificed), .searchLibrary (.put .dragon)])] }
  | .treasuresPerChosenType =>
    { resolution := .createTokens .treasure .chosenCreatureType false }
  | .revealUntilCreature =>
    { resolution := .revealLibrary .untilCreature
        (.ifElse .revealedManaValueAtMostLands (.put .revealed) (.returnToHand .revealed)) }
  | .attackSacPlusOneEqualPower =>
    { resolution := .may (.pay (.sacrifice (.fixed 1) .another))
        (.putCounters .plusOneSacrificedPower .source) .ifYouDo }
  | .lootLandEntersTapped =>
    { resolution := .sequence
        [.draw (.fixed 1), .discard (.cards 1), .put .discardedLand (how := .tapped)] }
  | .millThatManyLost =>
    { resolution := .mill .thatManyLost .thatPlayer }
  | .drawPerFatGraveyard =>
    { resolution := .draw .perFatGraveyard }
  | .maySacDrawTreasure =>
    { resolution := .may (.pay (.sacrifice (.fixed 1) .anotherCreatureOrArtifact))
        (.sequence [.draw (.fixed 1), .createTokens .treasure (.fixed 1) false]) .ifYouDo }
  | .castInstantSorceryFromHand =>
    { resolution := .mayCast .hand .twiceLegendaryWizards .withoutPaying }
  | .castInstantSorceryMvAtMost =>
    { resolution := .mayCast .hand .lastKnown .withoutPaying }
  | .millThenCopy =>
    { resolution := .sequence
        [.mill (.fixed 2) .eachOpponent (note := .opponentsMilled),
         .«if» .opponentsMilled (.queueReflexive (.mayCast .milledSpell .causingSpell .withoutPaying))] }
  | .pumpTargetBySourcePower =>
    { targeting := .of .anotherCreatureYouControl,
      resolution := .pump .equalSourcePower (.fixed 0) .target }
  | .createAlienPerInvasion =>
    { resolution := .sequence
        [.createTokens .treasure (.fixed 1) false .alien (note := .invasion),
         .putCounters .plusOneNoted .createdToken,
         .putCounters (.ofKind .invasion) .source] }
  | .mayPutArtifactAttachEquipment =>
    { resolution := .sequence
        [.may (.put .artifactFromHand (note := .forAttach)) (.sequence []),
         .«if» (.atLeast (.count .putEquipment) (.fixed 1)) (.attach .putArtifact .notedHost)] }
  | .cascade => { resolution := .cascade }
  | .belladonnaTokenReward =>
    { resolution := .sequence [
        .noteResolveThisTurn 3,
        .«if» (.nthResolve 1) (.gainLife (.fixed 1)),
        .«if» (.nthResolve 2) (.draw (.fixed 1)),
        .«if» (.nthResolve 3) (.putCounters (.ofKind .plusOnePlusOne) .youControl)] }
  | .bolgMaySacrifice => { resolution := .may (.sacrifice .another) (.sequence []) }
  | .bolgDealSacrificedPower =>
    { targeting := .of .anotherCreature,
      resolution := .sequence
        [.dealDamage .lastKnownPower .permanent .excess,
         .amass .notedExcess] }
  | .createSpiritsForEquipped =>
    { resolution := .sequence
        [.createTokens .spirit (.fixed 2) true, .«if» (.atLeast (.count (.intersection [.equipped, .legendaryCreaturesYouControl])) (.fixed 1)) .markRecentTokensAttacking] }
  | .createTreasuresEqualDamagedPlayerArtifacts =>
    { resolution :=
        .createTokens .treasure .damagedPlayerArtifacts false }
  | .deal1ThenAmassOrcs =>
    { targeting := .of .playerOrCreature,
      resolution := .sequence
        [.dealDamage (.fixed 1) .target .markedPermanent, .amass (.fixed 1) "Orc"] }
  | .untapAttackersExtraCombat _n =>
    { resolution := .sequence [.untap .attackingCreatures, .additionalCombatPhase] }
  | .eaglesCreateBirds =>
    { resolution := .createTokens .birdSoldier .lastKnownPower false }
  | .allianceMode =>
    { resolution := .chooseModes TriggeredAbility.TriggerResolution.allianceModes
        .oneUnusedThisTurn }
  | .destroyOtherAmassControllerPower =>
    { targeting := .of .anotherCreature, allowsZeroTargets := true,
      resolution := .sequence
        [.destroy .target (note := .forAmass),
         .amass .notedPower (who := .controller .target),
         .«if» .youControlledDestroyed (.draw (.fixed 1))] }
  | .gollumMode =>
    { resolution := .chooseModes TriggeredAbility.TriggerResolution.gollumModes
        .oneUnused }
  | .discardHandDrawDamageIfStory =>
    { resolution := .sequence
        [.may (.discard .hand) (.sequence []), .draw .discardedHand,
         .«if» .enduringStoryNoted (.dealDamage .discardedHand (.player .eachOpponent))] }
  | .castFromGyArtifactInstantSorcery =>
    { resolution := .mayCast .graveyard .unlimited .pay .exileInstead }
  | .equippedAttackersGainDoubleStrike =>
    { resolution := .grant .doubleStrike .equippedAttackers }
  | .tapEnchantedRemoveCounters =>
    { resolution := .sequence [.tap .enchanted, .removeCounters .all .enchanted] }
  | .revealTopPutRandomCreature n =>
    { resolution := .revealLibrary (.top n) (.put .randomCreature) }
  | .beginCombatIfDrawnTwoPump =>
    { targeting := .of .anotherCreatureYouControl,
      resolution := .«if» (.atLeast .cardsDrawnThisTurn (.fixed 2)) (.sequence [
        .pump (.fixed 3) (.fixed 0) .target,
        .grant (.keywords Keyword.firstStrike) .target]) }
  | .honePerOppAttach =>
    { targeting := .of (.multi #[
        { noun := "target opponent", zone := .player, controller := .opponent },
        { noun := "target creature you control", controller := .you, types := #[.creature] }
      ] #[1])
      resolution := .sequence
        [.putCounters .honePerOpponent .source, .attach .source (.target .laterCreature)] }
  | .damageTargetOpponent n =>
    { targeting := .of .opponent, resolution := .dealDamage (.fixed n) (.player (.target .opponent)) }
  | .copySelfNonlegendary => { resolution := .becomeCopy .sourceTwoNonlegendaryTokens }
  | .attachEquipmentThenFight =>
    { targeting := .of .creatureYouControl,
      resolution := .sequence [.attach .anyYouControl .target,
        .«if» .equipmentAttached (.fight .equipmentHost .reflexive)] }
  | .returnAsArtifact => { resolution := .put .source (how := .asArtifact) }
  | .exileLandsThenReturnTapped =>
    { targeting := .of (.filtered {
        noun := "up to three target lands you control"
        types := #[.land], controller := .you })
      allowsZeroTargets := true, maxTargets := 3
      resolution := .sequence
        [.exile .landsYouControl .forLater .lands,
         .put .notedLands (how := .tapped)] }
  | .grimaImpulse =>
    { resolution := .sequence
        [.revealLibrary .untilInstantOrSorcery (.exile .top .forLater .impulse) .damagedPlayer,
         .mayCast .impulse .unlimited .withoutPaying] }
  | .palantir =>
    { targeting := .of .opponent,
      resolution := .sequence
        [.putCounters (.ofKind .influence) .source, .scry (.fixed 2),
         .may (.draw (.fixed 1) (who := .opponentHasYou)) (.sequence [])] }
  | .treasuresEqualLastKnown =>
    { resolution := .createTokens .treasure .lastKnownPower false }
  | .protectionEverything =>
    { resolution := .grant .protectionEverything .youIfCast }
  | .loseLifePerBurden => { resolution := .loseLife .perBurden }
  | .revealSaga =>
    { resolution := .revealLibrary .untilSaga (.put .revealed) }
  | .sacDamagersRingTempts =>
    { resolution := .sequence [.sacrifice .combatDamager, .ringTempts] }
  | .chapter _n e =>
    TriggeredAbility.chapterTiming e
  | .drawIfAttackedOrEnteredSubtype subtype =>
    { resolution := .«if»
        (.or [.attackedWithSubtype subtype, .subtypeEntered subtype])
        (.draw (.fixed 1)) }
  | .othersOfSubtypeGetEqualSourceToughness subtype =>
    { resolution := .pump .equalSourceToughness .equalSourceToughness
        (.othersOfSubtype subtype) }
  | .scryAndPlan n =>
    { resolution := .sequence [.putCounters (.ofKind .plan) .source, .scry (.fixed n)] }
  | .lootAndPlan =>
    { resolution := .sequence
        [.putCounters (.ofKind .plan) .source, .draw (.fixed 1), .discard (.cards 1)] }
  | .createVillainAndPlan =>
    { resolution := .sequence
        [.putCounters (.ofKind .plan) .source, .createTokens .villain21menace (.fixed 1) false] }
  | .drainAndPlan n =>
    { resolution := .sequence
        [.putCounters (.ofKind .plan) .source, .loseLife (.fixed n) .eachOpponent, .gainLife (.fixed n)] }
  | .drawLoseLifeAndPlan =>
    { resolution := .sequence
        [.putCounters (.ofKind .plan) .source, .draw (.fixed 1), .loseLife (.fixed 1)] }
  | .treasureTappedAndPlan =>
    { resolution := .sequence
        [.putCounters (.ofKind .plan) .source, .createTokens .treasure (.fixed 1) true] }
  | .plusOneOnTargetAndPlan =>
    { targeting := .of .creatureYouControl,
      resolution := .sequence
        [.putCounters (.ofKind .plan) .source,
         .putCounters (.ofKind .plusOnePlusOne) (.permanent true)] }
  | .planFinishDrawPlusOneEach =>
    { resolution := .sequence
        [.sacrifice .plan, .draw (.fixed 1), .putCounters (.ofKind .plusOnePlusOne) .youControl] }
  | .planFinishReturnInstants =>
    { resolution := .sequence
        [.sacrifice .plan .forReflexive,
         .«if» .planWasSacrificed (.queueReflexive (.returnToHand (.graveyardInstants 2)))] }
  | .planFinishControlOpponent =>
    { resolution := .sequence
        [.sacrifice .plan .forReflexive,
         .«if» .planWasSacrificed (.queueReflexive (.gainControl .duringNextTurn))] }
  | .planFinishExileTopCast =>
    { resolution := .sequence
        [.sacrifice .plan .forReflexive,
         .«if» .planWasSacrificed (.queueReflexive (.exile (.opponentTop 5) (.mayCastUpTo 2)))] }
  | .planFinishCreateRobots n =>
    { resolution := .sequence
        [.sacrifice .plan, .createTokens .robotVillain22 (.fixed n) false] }
  | .planFinishDividedDamage n =>
    { resolution := .sequence
        [.sacrifice .plan .forReflexive,
         .«if» .planWasSacrificed (.queueReflexive (.dealDamage (.fixed n) .target .divided))] }
  | .planFinishIndestructibleOnTarget =>
    { resolution := .sequence
        [.sacrifice .plan .forReflexive,
         .«if» .planWasSacrificed (.queueReflexive (.putCounters (.ofKind .indestructible) .permanent))] }
  | .surveil n => { resolution := .surveil (.fixed n) }
  | .empowerJace n => { resolution := .empowerJace (.fixed n) }
  | .prepareSource .ifNotPrepared =>
    { events := #[.yourUpkeep], resolution := .«if» (.not .preparedSource) (.becomePrepared .source) }
  | .prepareSource .ifThreeCreaturesDied =>
    { events := #[.eachEndStep], resolution := .«if» (.atLeast .creaturesDiedThisTurn (.fixed 3)) (.becomePrepared .source) }
  | .drawIfRemovedTwoLoyalty =>
    { resolution := .«if» (.atLeast .lastKnownPower (.fixed 2)) (.draw (.fixed 1)) }
  | .loyaltyOnSource =>
    { resolution := .putCounters (.ofKind .loyalty) .source }
  | .grantThenCounterByType k =>
    { targeting := .of .permanentYouControl,
      resolution := .sequence
        [.grant (.keywords k) .target,
         .«if» (.atLeast (.count (.target .creature)) (.fixed 1)) (.putCounters (.ofKind .plusOnePlusOne) .permanent),
         .«if» (.atLeast (.count (.target .planeswalker)) (.fixed 1)) (.putCounters (.ofKind .loyalty) .permanent)] }
  | .destroyOppPermanentIfSixLands =>
    { targeting := .of .oppPermanent,
      resolution := .«if» ((.atLeast (.count .landsYouControl) (.fixed 6))) (.sequence [
        .destroy .target,
        .createTokens .treasure (.fixed 1) false (who := .controller .target)]) }
  | .pumpOrCounterIfScried =>
    { events := #[.yourBeginCombat], targeting := .of .anotherCreatureYouControl,
      resolution := .ifElse (.or [.scriedThisTurn, .surveilledThisTurn])
        (.putCounters (.ofKind .plusOnePlusOne) .permanent)
        (.pump (.fixed 1) (.fixed 1) .target) }
  | .sacrificeSourceIfNoPlaneswalker =>
    { events := #[.eachEndStep],
      resolution := .«if» (.not (.atLeast (.count .planeswalkersYouControl) (.fixed 1))) (.sacrifice (.sacrificedSource .controllerSacrifices)) }
  | .creaturesYouControlGet p t =>
    { resolution := .pump (.fixed p) (.fixed t) .creaturesYouControl }
  | .putSourceCountersOnTarget =>
    { targeting := .of .creatureYouControl, allowsZeroTargets := true,
      resolution := .putCounters .sourceCounters .permanent }
  | .chargeCounterOnSource =>
    { resolution := .putCounters (.ofKind .charge) .source }
  | .addGreenPerChargeCounter =>
    { events := #[.yourFirstMain],
      resolution := .addMana #[.colored .green] .perChargeCounter }
  | .drawTwoWinIfEmptyShuffleSource =>
    { resolution := .sequence
        [.draw (.fixed 2), .«if» (.not (.atLeast .libraryCards (.fixed 1))) .winTheGame, .«if» (.atLeast .libraryCards (.fixed 1)) (.putOnLibrary .shuffled .source)] }
  | .surveilReturnIfGainedLife =>
    { events := #[.yourEndStep],
      resolution := .sequence [.armSurveilReturnLifeGained, .surveil (.fixed 1)] }
  | .pumpIfFiveOtherForests =>
    { targeting := .of .creatureYouControl,
      resolution := .«if» ((.atLeast (.count .forestsExceptCause) (.fixed 5))) (.pump (.fixed 3) (.fixed 3) .target) }
  | .onEnchanted action =>
    { resolution := TriggeredAbility.TriggerResolution.ofEnchanted action }
  | .attachThen followup =>
    { targeting := .of .creatureYouControl,
      resolution := .sequence
        ([.attach .source .target] ++
          (TriggeredAbility.TriggerResolution.ofTargetWhileSource followup).flatten) }
  | .exileOtherCopyEnchanted =>
    { targeting := .of .creature, allowsZeroTargets := true,
      resolution := .sequence
        [.exile .target .untilSourceLeaves .copyAndHost, .becomeCopy .noted] }
  | .exileUntilNextEndStep =>
    { targeting := .of .creatureYouControl, allowsZeroTargets := true,
      resolution := .exile .target .nextEndStep }
  | .tapOrUntapNonland =>
    { targeting := .of .nonland,
      resolution := .or [.tap .target, .untap] }
  | .createFoodOrTreasure =>
    { resolution := .or
        [.createTokens .food (.fixed 1) false, .createTokens .treasure (.fixed 1) false] }
  | .villainIfGyElseMill =>
    { resolution := .ifElse ((.atLeast (.count .creatureCardsInGraveyard) (.fixed 2)))
        (.createTokens .villain21menace (.fixed 1) true) (.mill (.fixed 2)) }
  | .drawMayPutLandTapped =>
    { resolution := .sequence
        [.draw (.fixed 1), .may (.put .landFromHand (how := .tapped)) (.sequence [])] }
  | .drawGainLifeIfAnotherHero =>
    { resolution := .sequence [.draw (.fixed 1), .«if» (.atLeast (.count (.othersOfSubtype "Hero")) (.fixed 1)) (.gainLife (.fixed 2))] }
  | .plusOneOrTwoIfAnotherHero =>
    { targeting := .of .creature,
      resolution := .ifElse ((.atLeast (.count (.target (.anotherSubtype "Hero"))) (.fixed 1)))
        (.putCounters (.ofKind .plusOnePlusOne 2) .permanent)
        (.putCounters (.ofKind .plusOnePlusOne) .permanent) }
  | .maySacArtifactOrDiscardDraw =>
    { resolution := .may (.pay (.or [.sacrifice (.fixed 1) .artifact, .discard (.fixed 1) .card])) (.draw (.fixed 1)) .ifYouDo }
  | .enter (.destroy kind) =>
    { events := #[.entering], targeting := .of kind, resolution := .destroy .target }
  | .enter (.dealDamageUpToOne n) =>
    { events := #[.entering], targeting := .of .creature, allowsZeroTargets := true,
      resolution := .dealDamage (.fixed n) .target }
  | .enter .fightUpToOne =>
    { events := #[.entering], targeting := .of .anotherCreature, allowsZeroTargets := true,
      resolution := .fight }
  | .enter .returnNonlandNontoken =>
    { events := #[.entering], targeting := .of .nonlandNontoken, allowsZeroTargets := true,
      resolution := .returnToHand .permanent .returnedPermanent }
  | .enter .createZabu =>
    { events := #[.entering], resolution := .createTokens .treasure (.fixed 1) false .zabu }
  | .enter .oppCreatesTheVoid =>
    { events := #[.entering], targeting := .of .opponent,
      resolution := .createTokens .treasure (.fixed 1) false .theVoid (.target .opponent) }
  | .enter .createSturdyShieldAttach =>
    { events := #[.entering],
      resolution := .sequence
        [.createTokens .treasure (.fixed 1) false .sturdyShield (note := .remember),
         .attach .createdToken .source] }
  | .enter .exileGyPlayUntilNextTurn =>
    { events := #[.entering], targeting := .of .equipmentInstantOrSorceryInYourGraveyard,
      resolution := .sequence
        [.exile .graveyardCard .forLater .playCard, .grant .playNotedUntilNextTurn .target] }
  | .enter .returnGyPermanentThisTurn =>
    { events := #[.entering], targeting := .of .permanentCardInYourGraveyard,
      resolution := .returnToHand .graveyardPermanent }
  | .enter .tapOppCantUntapWhileControl =>
    { events := #[.entering], targeting := .of .oppCreature,
      resolution := .sequence [.tap .target, .cant .untapWhileYouControl] }
  | .enter .maySacAnotherThenDestroyOppNonland =>
    { events := #[.entering],
      resolution := .may (.pay (.sacrifice (.fixed 1) .another)) (.queueReflexive (.destroy .target)) .ifYouDo }
  | .enter .maySacOrDiscardNonlandThenDamage =>
    { events := #[.entering],
      resolution := .may (.pay (.or [.sacrifice (.fixed 1) .artifact, .discard (.fixed 1) .nonland]))
        (.queueReflexive (.dealDamage (.fixed 2) .target)) .ifYouDo }
  | .enter .revealHandExileUntilLeaves =>
    { events := #[.entering], targeting := .of .opponent, allowsZeroTargets := true,
      resolution := .revealFromHand .hand (.exile .target .untilSourceLeaves) }
  | .enter .plusOnesOrReturnArtEnch =>
    { events := #[.entering], targeting := .of .creature, allowsZeroTargets := true,
      resolution := .or
        [.putCounters (.ofKind .plusOnePlusOne) .permanent,
         .returnToHand .graveyardCard] }
  | .enter .chooseUpToXModes =>
    { events := #[.entering], targeting := .of .opponent, allowsZeroTargets := true,
      resolution := .chooseModes TriggeredAbility.TriggerResolution.upToXModes
        .alreadyChosen }
  | .enter .mayTapThenGrantIndestructible =>
    { events := #[.entering],
      resolution := .may (.tap .source) (.queueReflexive (.grant (.keywords Keyword.indestructible) .target)) .ifYouDo }
  | .enter .tapLoseAbilitiesWhileSource =>
    { events := #[.entering], targeting := .of .creature, allowsZeroTargets := true,
      resolution := .sequence
        [.tap (.target .ifPresent), .lose .allAbilities (.target .ifPresent)] }
  | .enter .revealDiscardFromHand =>
    { events := #[.entering], targeting := .of .player,
      resolution := .revealFromHand .onePlusCreatureCards
        (.discard (.cards 1 (.target .opponent))) }
  | .enter .createRedwing =>
    { events := #[.entering], resolution := .createTokens .treasure (.fixed 1) false .redwing }
  | .step .enchantedControllerDraws =>
    { events := #[.enchantedControllerUpkeep]
      resolution := .draw (.fixed 1) (who := .controller .enchanted) }
  | .step .drawToTen =>
    { events := #[.yourEndStep], resolution := .draw (.upToHandSize 10) }
  | .step .copyAbsorbingMan =>
    { events := #[.yourFirstMain]
      targeting := .of (.filtered {
        noun := "up to one target artifact, non-Aura enchantment, or land"
        types := #[.artifact, .enchantment, .land]
        nonAura := true })
      allowsZeroTargets := true, maxTargets := 1
      resolution := .becomeCopy .artifactEnchantmentOrLand }
  | .step .hydeChoose =>
    { events := #[.yourUpkeep],
      resolution := .chooseModes TriggeredAbility.TriggerResolution.hydeModes
        .plusOneOrRemoveCounter }
  | .step .copyTaskmaster =>
    { events := #[.yourFirstMain], targeting := .of .creatureOrGyCreatureCard,
      allowsZeroTargets := true, maxTargets := 1
      resolution := .becomeCopy .creatureOrGraveyardCard }
  | .step .harnessedFlicker =>
    { events := #[.yourEndStep]
      targeting := .of (.filtered {
        noun := "up to one other target nonland permanent you control"
        nonland := true, controller := .you, another := true })
      allowsZeroTargets := true, maxTargets := 1
      resolution := .«if» (.atLeast (.count .harnessedSource) (.fixed 1)) (.exile .target .returnImmediately) }
  | .death .hellcatReturn =>
    { events := #[.dying]
      resolution := .put .source .underOwner (.entering [
        .loseAllAbilities, .keywords Keyword.haste,
        .counter .plusOnePlusOne (asEnters := true)]) }
  | .death .villainReturnAsHero =>
    { events := #[.villainYouControlDies]
      resolution := .put (.cause (some "Villain")) .underOwner (.entering [
        .additionalSubtype "Hero", .counter .finality]) }
  | .death .attackingReturnHand =>
    { events := #[.attackingCreatureYouControlDies]
      resolution := .returnToHand .cause }
  | .death .deathtouchOppSac =>
    { events := #[.creatureYouControlDies]
      resolution := .sacrifice .chosenNontokenCreature }
  | .thisAttack .mayPayPlusOne =>
    { events := #[.attacking]
      resolution := .may (.pay (.mana #[.generic 1])) (.queueReflexive (.putCounters (.ofKind .plusOnePlusOne) .permanent)) .ifYouDo }
  | .thisAttack .payReturnAttacking =>
    { events := #[.attacking]
      resolution := .may (.pay (.mana #[.generic 3, .colored .black]))
        (.queueReflexive (.put .creatureCard .tapped (.entering [.attacking, .counter .finality]))) .ifYouDo }
  | .thisAttack .ifArtifactEnteredDraw =>
    { events := #[.attacking]
      resolution := .«if» .artifactEnteredThisTurn (.draw (.fixed 1)) }
  | .thisAttack .blinkNontoken =>
    { events := #[.attacking]
      targeting := .of (.filtered {
        noun := "up to one target nontoken artifact or creature"
        types := #[.artifact, .creature], nontoken := true })
      allowsZeroTargets := true, maxTargets := 1
      resolution := .exile .target .returnTapped }
  | .thisAttack .equippedDrain =>
    { events := #[.attacking]
      resolution := .«if» .attachedEquipment (.sequence [
        .loseLife .attachedEquipment .eachOpponent,
        .gainLife .attachedEquipment]) }
  | .thisAttack .drawIfPower4 =>
    { events := #[.attacking]
      resolution := .«if» (.atLeast .equalSourcePower (.fixed 4)) (.draw (.fixed 1)) }
  | .thisAttack .attacksAlonePlus2Indestructible =>
    { events := #[.attacking]
      resolution := .sequence [
        .pump (.fixed 2) (.fixed 0) .source,
        .grant (.keywords Keyword.indestructible) .source] }
  | .enterOrAttack .copyKeywords =>
    { events := #[.entering, .attacking], targeting := .of .anotherCreature,
      resolution := .putCounters .missingKeywordsFromTarget .source }
  | .enterOrAttack .createSquirrel =>
    { events := #[.entering, .attacking],
      resolution := .createTokens .squirrel11green (.fixed 1) false }
  | .watch .combatDamageExileUntilNonland =>
    { events := #[.dealsCombatDamageToPlayer],
      resolution := .revealLibrary .untilNonland
        (.may (.putCounters (.ofKind .plusOnePlusOne) .source)
          (.exile .top .forLater .anyManaThisTurn) .ifYouDont)
        .announced }
  | .watch .attacksAloneDrain =>
    { events := #[.creatureYouControlAttacksAlone], targeting := .of .opponent,
      resolution := .sequence [.loseLife (.fixed 1) (.target .opponent), .gainLife (.fixed 1)] }
  | .watch .attacksAloneFirstStrikeMenace =>
    { events := #[.creatureYouControlAttacksAlone],
      resolution := .grant
        (.keywords (Keywords.merge Keyword.firstStrike Keyword.menace)) .attackingAlone }
  | .watch .firstTapUntap =>
    { events := #[.creatureYouControlTapped], resolution := .untap .firstThisTurn }
  | .watch .sheHulkRedirectOnce =>
    { events := #[.creatureYouControlDealtDamage], targeting := .of .playerOrCreature,
      resolution := .may (.dealDamage .lastKnownPower .target) (.sequence []) .ifYouDo }
  | .watch .speedballTargeted =>
    { events := #[.spellTargetsSource],
      resolution := .sequence [
        .pump (.fixed 2) (.fixed 2) .source, .may .retargetCause (.sequence []) .ifYouDo] }
  | .watch .anyPlayerSecondDraw =>
    { events := #[.anyPlayerDrawsSecond], resolution := .draw (.fixed 1) }
  | .watch .youTargetDrawOnce =>
    { events := #[.youTargetSomething], onceEachTurn := true, resolution := .draw (.fixed 1) }
  | .watch .villainOrArtifactDamage =>
    { events := #[.anotherVillainOrArtifactEnters], targeting := .of .opponent,
      resolution := .dealDamage (.fixed 1) (.player (.target .opponent)) }
  | .watch .villainConniveOnce =>
    { events := #[.anotherVillainEnters], optionalOnceEachTurn := true,
      resolution := .connive .enteringVillain }
  | .watch .villainPlusOneDamageOnce =>
    { events := #[.anotherVillainEnters], onceEachTurn := true,
      resolution := .sequence [
        .putCounters (.ofKind .plusOnePlusOne) .sourceIfPresent,
        .dealDamage (.fixed 2) (.player .eachOpponent)] }
  | .watch .villainAttachEquipment =>
    { events := #[.anotherVillainEnters]
      targeting := .of .upToOneEquipmentThenCreatureYouControl
      resolution := .attach .announcedEquipment .announcedCreature }
  | .watch .villainPlusOneLifelink =>
    { events := #[.anotherVillainEnters],
      resolution := .sequence [
        .pump (.fixed 1) (.fixed 0) .source, .grant (.keywords Keyword.lifelink) .source] }
  | .watch .hulklingCompare =>
    { events := #[.anotherCreatureYouControlEnters],
      resolution := .«if» (.or [.causeGreaterPower, .causeGreaterToughness])
        (.putCounters (.ofKind .plusOnePlusOne) .source) }
  | .watch .justiceBounce =>
    { events := #[.anotherNonlandReturned],
      resolution := .putCounters (.ofKind .plusOnePlusOne) .source }
  | .watch .nontokenHeroModal =>
    { events := #[.anotherNontokenHeroEnters],
      resolution := .chooseModes
        [.createTokens .soldier11white (.fixed 1) false,
         .pump (.fixed 1) (.fixed 1) .creaturesYouControl]
        .fromLastKnown }
  | .watch .ultronCopy =>
    { events := #[.anotherNontokenArtifactEnters],
      resolution := .may (.pay (.mana #[.generic 2])) (.becomeCopy .cause) .ifYouDo }
  | .watch .enchantedAttachEquipment =>
    { events := #[.enchantedAttacksOrBlocks], targeting := .of .equipmentYouControl
      allowsZeroTargets := true, maxTargets := 1000,
      resolution := .attach (.target .eachEquipment) .enchantedCreature }
  | .watch .equippedAttacksAloneUntapScry =>
    { events := #[.equippedAttacksAlone],
      resolution := .sequence [.untap .equipped, .scry (.fixed 1)] }
  | .watch .equippedAttacksTap =>
    { events := #[.equippedAttacks], targeting := .of .defendingPlayerCreature,
      resolution := .tap .target }
  | .watch .equippedTappedDamage =>
    { events := #[.equippedBecomesTapped],
      resolution := .dealDamage (.fixed 1) (.player .eachOpponent) .fromEquipped }
  | .watch .heroesDamagePlusTwo =>
    { events := #[.heroesDealDamageToPlayer],
      resolution := .putCounters (.ofKind .plusOnePlusOne 2) .source }
  | .watch .merfolkAttackDraw =>
    { events := #[.merfolkAttackPlayer], resolution := .draw (.fixed 1) }
  | .watch .tokensEnterMayDraw =>
    { events := #[.tokenYouControlEnters],
      resolution := .may (.draw (.fixed 1)) (.sequence []) .ifYouDo }
  | .watch .hawkeyeModes =>
    { events := #[.sourceBecomesTapped], allowsZeroTargets := true,
      resolution := .may (.pay (.mana #[.generic 1])) (.queueReflexive (.chooseModes TriggeredAbility.TriggerResolution.trickArrowModes .alreadyChosen)) .ifYouDo }
  | .watch .redHulk =>
    { events := #[.sourceDealtDamage],
      resolution := .sequence [
        .putCounters (.ofKind .plusOnePlusOne) .source,
        .queueReflexive (.dealDamage .plusOneCounters .target)] }
  | .watch .hulk =>
    { events := #[.sourceDealtDamage],
      resolution := .sequence [
        .putCounters (.ofKind .plusOnePlusOne) .source,
        .«if» (.atLeast (.count (.intersection [.source, .attackingCreatures])) (.fixed 1)) (.untap .source),
        .«if» .enrageGrantsCombat .additionalCombatPhase] }
  | .youAttacking .pay2LifeToughness =>
    { events := #[.youAttack],
      resolution := .may (.loseLife (.fixed 2))
        (.grant .assignCombatDamageEqualToughness .creaturesYouControl) .ifYouDo }
  | .youAttacking .exileTopHeroPump =>
    { events := #[.youAttack],
      resolution := .may (.exile .top .playThisTurn .ifHero) (.sequence []) }
  | .youAttacking .lookSixCast =>
    { events := #[.youAttack],
      resolution := .revealLibrary (.top 6)
        (.mayCast .looked .greatestAttackingPower .withoutPaying) }
  | .casting .villainToken =>
    { events := #[.youCastVillain],
      resolution := .createTokens .villain21menace (.fixed 1) false }
  | .casting .merfolkFromBlue =>
    { events := #[.youCastNoncreature],
      resolution := .createTokens .treasure .blueManaSymbols false .merfolk }
  | .casting .mayPayHasteUnblockable =>
    { events := #[.youCastNoncreature],
      resolution := .may (.pay (.mana #[.generic 1])) (.queueReflexive (.cant (.beBlockedExceptByHaste .target))) .ifYouDo }
  | .casting .plusOneEachOther =>
    { events := #[.youCastNoncreature],
      resolution := .putCounters (.ofKind .plusOnePlusOne) .eachOther }
  | .casting .exileFlicker =>
    { events := #[.youCastNoncreature]
      targeting := .of (.filtered {
        noun := "another target nonland, nontoken permanent"
        nonland := true, nontoken := true, another := true })
      resolution := .exile .target .nextEndStep }
  | .casting .visionModes =>
    { events := #[.youCastNoncreature],
      resolution := .chooseModes TriggeredAbility.TriggerResolution.visionModes .vision }
  | .casting .damageEqualMv =>
    { events := #[.youCastNoncreature], targeting := .of .playerOrCreature,
      resolution := .dealDamage .spellManaValue .target }
  | .casting .drawPowerEqualHand =>
    { events := #[.youCastTargetingCreatureYouControl],
      resolution := .sequence [.draw (.fixed 1), .grant .basePowerEqualHand .source] }
  | .casting .plusOneThis =>
    { events := #[.youCastTargetingCreatureYouControl],
      resolution := .putCounters (.ofKind .plusOnePlusOne) .source }
  | .casting .plusOneScry =>
    { events := #[.youCastTargetingCreatureYouControl],
      resolution := .sequence [.putCounters (.ofKind .plusOnePlusOne) .source, .scry (.fixed 1)] }
  | .casting .ironFistTap =>
    { events := #[.youCastTargetingCreatureYouControl],
      resolution := .grant .ironFistTap .source }
  | .casting .targetsGainFlying =>
    { events := #[.youCastTargetingCreature],
      resolution := .grant (.keywords Keyword.flying) .spellTargets }
  | .casting .copyIfArtifactOrLand =>
    { events := #[.youCastInstantSorceryTargetingArtifactOrLand],
      resolution := .sequence [
        .putCounters (.ofKind .plusOnePlusOne 2) .source, .copyCause] }
  | .casting .tapCreatureOrLand =>
    { events := #[.youCastNoncreature],
      targeting := .of (.filtered {
        noun := "target creature or land",
        types := #[.creature, .land] }),
      resolution := .tap .target }
  | .resource .discardExilePlay =>
    { events := #[.youDiscard],
      resolution := .may (.exile .discarded .playUntilNextTurn) (.sequence []) .ifYouDo }
  | .resource .drawIfAnotherHeroDamage =>
    { events := #[.youDraw], targeting := .of .opponent,
      resolution := .«if» (.atLeast (.count (.othersOfSubtype "Hero")) (.fixed 1)) (.dealDamage (.fixed 1) (.player (.target .opponent))) }
  | .resource .secondDrawBecome66 =>
    { events := #[.youDrawSecondCard],
      resolution := .sequence [
        .setBasePT (.fixed 6) (.fixed 6) .source, .grant (.keywords Keyword.trample) .source] }
  | .resource .secondDrawPlusOneTarget =>
    { events := #[.youDrawSecondCard], targeting := .of .creature,
      resolution := .putCounters (.ofKind .plusOnePlusOne) .permanent }
  | .resource .secondDrawDrain =>
    { events := #[.youDrawSecondCard],
      resolution := .sequence [.loseLife (.fixed 1) .eachOpponent, .gainLife (.fixed 1)] }
  | .resource .gainLifePlusOnes =>
    { events := #[.youGainLife], targeting := .of .creatureYouControl,
      allowsZeroTargets := true,
      resolution := .putCounters (.ofKind .plusOnePlusOne) .eachUpToLastKnown }
  | .resource .plusOneCreateInsectOnce =>
    { events := #[.youPutPlusOne], onceEachTurn := true,
      resolution := .createTokens .insect11green (.fixed 1) false }
  | .resource .plusOneOnThisOnce =>
    { events := #[.youPutPlusOne], onceEachTurn := true,
      resolution := .putCounters (.ofKind .plusOnePlusOne) .source }
  | .resource .plusOneOnHeroesCreateWall =>
    { events := #[.youPutPlusOne],
      resolution := .may (.createTokens .wall04defender (.fixed 1) false) (.sequence []) .ifYouDo }

end SharedTrigger

#guard !(SharedTrigger.timing (.watch .sheHulkRedirectOnce)).onceEachTurn
#guard (SharedTrigger.timing (.watch .sheHulkRedirectOnce)).targeting.kind ==
  .playerOrCreature
#guard (SharedTrigger.timing (.thisAttack .blinkNontoken)).allowsZeroTargets &&
  (SharedTrigger.timing (.thisAttack .blinkNontoken)).maxTargets == 1
#guard (SharedTrigger.timing (.thisAttack .mayPayPlusOne)).resolution ==
  .may (.pay (.mana #[.generic 1])) (.queueReflexive (.putCounters (.ofKind .plusOnePlusOne) .permanent)) .ifYouDo
#guard (SharedTrigger.timing (.thisAttack .payReturnAttacking)).resolution ==
  .may (.pay (.mana #[.generic 3, .colored .black])) (.queueReflexive (.put .creatureCard .tapped (.entering [.attacking, .counter .finality]))) .ifYouDo
#guard (SharedTrigger.timing (.thisAttack .ifArtifactEnteredDraw)).resolution ==
  .«if» .artifactEnteredThisTurn (.draw (.fixed 1))
#guard (SharedTrigger.timing (.thisAttack .blinkNontoken)).resolution ==
  .exile .target .returnTapped
#guard (SharedTrigger.timing (.thisAttack .equippedDrain)).resolution ==
  .«if» .attachedEquipment (.sequence [
    .loseLife .attachedEquipment .eachOpponent,
    .gainLife .attachedEquipment])
#guard (SharedTrigger.timing (.thisAttack .drawIfPower4)).resolution ==
  .«if» (.atLeast .equalSourcePower (.fixed 4)) (.draw (.fixed 1))
#guard (SharedTrigger.timing (.thisAttack .attacksAlonePlus2Indestructible)).resolution ==
  .sequence [.pump (.fixed 2) (.fixed 0) .source, .grant (.keywords Keyword.indestructible) .source]
#guard (SharedTrigger.timing (.enterOrAttack .copyKeywords)).targeting.kind ==
  .anotherCreature
#guard (SharedTrigger.timing (.enterOrAttack .copyKeywords)).resolution ==
  .putCounters .missingKeywordsFromTarget .source
#guard (SharedTrigger.timing (.enterOrAttack .createSquirrel)).resolution ==
  .createTokens .squirrel11green (.fixed 1) false
#guard (SharedTrigger.timing (.watch .villainConniveOnce)).optionalOnceEachTurn
#guard (SharedTrigger.timing (.watch .combatDamageExileUntilNonland)).resolution ==
  .revealLibrary .untilNonland
    (.may (.putCounters (.ofKind .plusOnePlusOne) .source)
      (.exile .top .forLater .anyManaThisTurn) .ifYouDont)
    .announced
#guard (SharedTrigger.timing (.watch .hawkeyeModes)).resolution ==
  .may (.pay (.mana #[.generic 1])) (.queueReflexive (.chooseModes TriggeredAbility.TriggerResolution.trickArrowModes .alreadyChosen)) .ifYouDo
#guard (SharedTrigger.timing (.watch .hulk)).resolution ==
  .sequence [
    .putCounters (.ofKind .plusOnePlusOne) .source,
    .«if» (.atLeast (.count (.intersection [.source, .attackingCreatures])) (.fixed 1)) (.untap .source),
    .«if» .enrageGrantsCombat .additionalCombatPhase]
#guard (SharedTrigger.timing (.enterOrAttack .copyKeywords)).events ==
  #[TriggerEvent.entering, TriggerEvent.attacking]
#guard (SharedTrigger.timing (.death .hellcatReturn)).resolution ==
  .put .source .underOwner (.entering [
    .loseAllAbilities, .keywords Keyword.haste,
    .counter .plusOnePlusOne (asEnters := true)])
#guard (SharedTrigger.timing (.death .villainReturnAsHero)).resolution ==
  .put (.cause (some "Villain")) .underOwner (.entering [
    .additionalSubtype "Hero", .counter .finality])
#guard (SharedTrigger.timing (.death .attackingReturnHand)).resolution ==
  .returnToHand .cause
#guard (SharedTrigger.timing (.death .deathtouchOppSac)).resolution ==
  .sacrifice .chosenNontokenCreature
#guard TriggeredAbility.TriggerResolution.ofPermanent .loseIndestructible ==
  .lose .indestructible
#guard TriggeredAbility.TriggerResolution.ofSource .loseIndestructible ==
  .lose .indestructible .source
#guard TriggeredAbility.TriggerResolution.ofEnchanted .loseIndestructible ==
  .lose .indestructible .enchanted
#guard TriggeredAbility.TriggerResolution.ofTargetWhileSource .loseIndestructible ==
  .lose .indestructible (.target .whileSource)
#guard TriggeredAbility.TriggerResolution.ofPermanent .cantBeBlocked ==
  .cant .beBlocked
#guard TriggeredAbility.TriggerResolution.ofPermanent .indestructibleCounter ==
  .putCounters (.ofKind .indestructible) .permanent
#guard TriggeredAbility.TriggerResolution.ofPermanent .doubleStrikeCounter ==
  .putCounters (.ofKind .doubleStrike) .permanent
#guard TriggeredAbility.TriggerResolution.ofPermanent .burdenCounter ==
  .putCounters (.ofKind .burden) .permanent
#guard TriggeredAbility.TriggerResolution.ofPermanent .becomeArtifactIndestructible ==
  .sequence [.becomeArtifact, .grant (.keywords Keyword.indestructible) .target]
#guard TriggeredAbility.TriggerResolution.ofPermanent .becomePrepared == .becomePrepared
#guard TriggeredAbility.TriggerResolution.ofPermanent (.setBasePT 2 2) ==
  .setBasePT (.fixed 2) (.fixed 2)
#guard TriggeredAbility.TriggerResolution.ofPermanent .tapAndStun ==
  .sequence [.tap .target, .putCounters (.ofKind .stun) .permanent]
#guard TriggeredAbility.TriggerResolution.ofPermanent .putOnTopOfLibrary ==
  .putOnLibrary .top
#guard TriggeredAbility.TriggerResolution.ofPermanent .putOnBottomOfLibrary ==
  .putOnLibrary .bottom
#guard TriggeredAbility.TriggerResolution.ofSource .putOnTopOfLibrary ==
  .putOnLibrary .top .source
#guard TriggeredAbility.TriggerResolution.ofSource .putOnBottomOfLibrary ==
  .putOnLibrary .bottom .source
#guard TriggeredAbility.TriggerResolution.ofEnchanted .putOnTopOfLibrary ==
  .putOnLibrary .top .enchanted
#guard TriggeredAbility.TriggerResolution.ofEnchanted .putOnBottomOfLibrary ==
  .putOnLibrary .bottom .enchanted
#guard TriggeredAbility.TriggerResolution.ofTargetWhileSource .putOnTopOfLibrary ==
  .putOnLibrary .top (.target .whileSource)
#guard TriggeredAbility.TriggerResolution.ofTargetWhileSource .putOnBottomOfLibrary ==
  .putOnLibrary .bottom (.target .whileSource)
#guard TriggeredAbility.TriggerResolution.ofPermanent .exile == .exile .target .forLater
#guard TriggeredAbility.TriggerResolution.ofSource .exile == .exile .source .forLater
#guard TriggeredAbility.TriggerResolution.ofEnchanted .exile ==
  .exile .enchanted .forLater
#guard TriggeredAbility.TriggerResolution.ofTargetWhileSource .exile ==
  .exile (.target .whileSource) .forLater
#guard TriggeredAbility.TriggerResolution.ofPermanent .doublePowerAndToughness ==
  .pump .double .double .target
#guard TriggeredAbility.TriggerResolution.ofPermanent (.pumpAndTrample 2 0) ==
  .sequence [.pump (.fixed 2) (.fixed 0) .target, .grant (.keywords Keyword.trample) .target]
#guard TriggeredAbility.TriggerResolution.ofSource (.plusOne 1) ==
  .putCounters (.ofKind .plusOnePlusOne) .source
#guard TriggeredAbility.TriggerResolution.ofSource (.pump 1 1) ==
  .pump (.fixed 1) (.fixed 1) .source
#guard TriggeredAbility.TriggerResolution.ofSource .tap == .tap .source
#guard TriggeredAbility.TriggerResolution.ofEnchanted .tap == .tap .enchantedWhileSource
#guard TriggeredAbility.TriggerResolution.ofEnchanted (.grantKeywords Keyword.firstStrike) ==
  .grant (.keywords Keyword.firstStrike) .enchanted
#guard TriggeredAbility.TriggerResolution.ofTargetWhileSource .untap ==
  .untap (.target .whileSource)
#guard TriggeredAbility.TriggerResolution.ofTargetWhileSource
    (.grantKeywords Keyword.indestructible) ==
  .grant (.keywords Keyword.indestructible) (.target .whileSource)
#guard (SharedTrigger.timing (.resource .discardExilePlay)).resolution ==
  .may (.exile .discarded .playUntilNextTurn) (.sequence []) .ifYouDo
#guard (SharedTrigger.timing (.resource .drawIfAnotherHeroDamage)).resolution ==
  .«if» (.atLeast (.count (.othersOfSubtype "Hero")) (.fixed 1)) (.dealDamage (.fixed 1) (.player (.target .opponent)))
#guard (SharedTrigger.timing (.resource .secondDrawBecome66)).resolution ==
  .sequence [.setBasePT (.fixed 6) (.fixed 6) .source, .grant (.keywords Keyword.trample) .source]
#guard (SharedTrigger.timing (.resource .secondDrawPlusOneTarget)).resolution ==
  .putCounters (.ofKind .plusOnePlusOne) .permanent
#guard (SharedTrigger.timing (.resource .secondDrawDrain)).resolution ==
  .sequence [.loseLife (.fixed 1) .eachOpponent, .gainLife (.fixed 1)]
#guard (SharedTrigger.timing (.resource .gainLifePlusOnes)).resolution ==
  .putCounters (.ofKind .plusOnePlusOne) .eachUpToLastKnown
#guard (SharedTrigger.timing (.resource .plusOneCreateInsectOnce)).resolution ==
  .createTokens .insect11green (.fixed 1) false
#guard (SharedTrigger.timing (.resource .plusOneOnThisOnce)).resolution ==
  .putCounters (.ofKind .plusOnePlusOne) .source
#guard (SharedTrigger.timing (.resource .plusOneOnHeroesCreateWall)).resolution ==
  .may (.createTokens .wall04defender (.fixed 1) false) (.sequence []) .ifYouDo

end Mtg.Engine
