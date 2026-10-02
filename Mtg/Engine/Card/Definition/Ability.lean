import Mtg.Engine.Card.Definition.Compile

/-!
# Compiling an ability

Activated and triggered `Ability` values compiled to `ActivatedAbility`
and `TriggeredAbility`.
-/

namespace Mtg.Engine

namespace Ability

/-- Compile an `.activated` ability; `none` for a keyword. -/
def activatedAbility (costs : List Cost) (action : CardAction)
    (onceEachTurn : Bool := false) : ActivatedAbility :=
  let cyclingBasic :=
    Cost.discardsThis costs &&
      CardAction.leftoverSearchLibraryThenShuffle? action ==
        some Effect.searchBasicLandToHand
  { cost :=
      { mana := Cost.manaCost costs
        payLife := Cost.lifePaid costs
        tap := Cost.hasTapSymbol costs
        sacrificeSource := Cost.sacrificesThis costs
        sacrificeAnotherCreatureOrArtifact := Cost.sacrificesArtifactOrCreature costs
        sacrificeLegendaryArtifact := Cost.sacrificesLegendaryArtifact costs
        sacrificeArtifact := Cost.sacrificesArtifact costs
        discardSource := Cost.discardsThis costs
        sacrificeAnotherSubtype := Cost.sacrificeAnotherSubtype? costs
        discardACard := Cost.discardsACard costs
        sacrificeArtifactOrDiscardNonland :=
          CardAction.leftoverSacrificeArtifactOrDiscardNonlandCost? costs }
    effect :=
      if cyclingBasic then Effect.searchLandTypeToHand "Basic land"
      else if action == .tap (.target 1 (.intersection [.zone .battlefield, .cardType .creature])) then
        Effect.tapTargetCreature
      else action.toAbilityEffect
    onceEachTurn
    activateFromHand := Cost.discardsThis costs }

/-- Compile a conditional activated ability. `fromGraveyard` means it
functions while this card is in a graveyard (CR 113.6). -/
def compileConditional (cond : Condition) (costs : List Cost) (action : CardAction)
    (fromGraveyard : Bool) : Option ActivatedAbility :=
  match cond with
  | .greaterOrEqual (.count among) threshold =>
    if CardAction.leftoverYourGyCreatures? among && valToNat? threshold == some 2 then
      some { activatedAbility costs action with
        onlyIfGyCreaturesAtLeast := 2
        activateFromGraveyard := fromGraveyard }
    else none
  | .not (.happened (.abilityWithIdActivated _) .turnStart) =>
    some { activatedAbility costs action true with
      activateFromGraveyard := fromGraveyard }
  | .timeToCastSorcery _ =>
    some { activatedAbility costs action with
      onlyAsSorcery := true
      equipSubtype := CardAction.leftoverEquipSubtype? action
      activateFromGraveyard := fromGraveyard }
  | .and (.turn _) (.not (.happened (.abilityWithIdActivated _) .turnStart)) =>
    some { activatedAbility costs action true with
      onlyDuringYourTurn := true
      activateFromGraveyard := fromGraveyard }
  | .turn _ =>
    some { activatedAbility costs action with
      onlyDuringYourTurn := true
      activateFromGraveyard := fromGraveyard }
  | .any sel =>
    if sel == Selector.aLegendaryCreatureYouControl then
      some { activatedAbility costs action with
        onlyIfYouControlLegendary := true
        activateFromGraveyard := fromGraveyard }
    else none
  | .anySubtype _ _ | .happened _ _
  | .and _ _ | .not _ | .drawStep _ | .enduringStory _
  | .less _ _ | .lessOrEqual _ _ | .greater _ _ | .greaterOrEqual _ _
  | .equal _ _ => none

/-- `{k}` less for each Equipment this ability's controller controls.
`.this` is this ability. Zero is not a reduction. -/
def abilityEquipmentCostReduction? : ContinuousEffect → Option Nat
  | .reduceCostWithX .this [.mana [.generic k]] (.count among) =>
    if k != 0 &&
        among.includedSubtype? == some "Equipment" &&
        among.shape.sameController then
      some k
    else none
  | _ => none

/-- Apply a static effect that belongs to this activated ability. -/
def withAbilityStatic (ab : ActivatedAbility) (e : ContinuousEffect) : ActivatedAbility :=
  match abilityEquipmentCostReduction? e with
  | some k => { ab with costReductionPerEquipment := ab.costReductionPerEquipment + k }
  | none => ab

def toActivatedAbility? : Ability → Option ActivatedAbility
  | .keywordWithCost .equip costs =>
    some {
      cost := { mana := Cost.manaCost costs, payLife := Cost.lifePaid costs }
      effect := Effect.attachToTargetCreatureYouControl
      onlyAsSorcery := true }
  | .keywordWithSubtypeAndCost .equip st cost =>
    some {
      cost := { mana := Cost.manaCost [cost] }
      effect := Effect.attachToTargetCreatureYouControl
      onlyAsSorcery := true
      equipSubtype := some st.toString }
  | .keywordWithCost (.typecycling supertypes types subtypes) costs =>
    some {
      cost := { mana := Cost.manaCost costs, discardSource := true }
      effect := Effect.searchLandTypeToHand (Keyword.typecyclingPhrase supertypes types subtypes)
      activateFromHand := true }
  | .activated costs action => some (activatedAbility costs action)
  | .activatedIf cond costs action => compileConditional cond costs action false
  | .activatedWithStaticIf cond costs action e =>
    (compileConditional cond costs action false).map (withAbilityStatic · e)
  | .graveyardActivatedIf cond costs action =>
    compileConditional cond costs action true
  | .abilityId _ inner => toActivatedAbility? inner
  | _ => none

/-- Keyword actions on a trigger compile to a named `TriggeredAbility`. -/
def leftoverKeywordTriggered? (w : Trigger) (who : Selector) (k : Keyword) :
    Option TriggeredAbility :=
  match k with
  | .connive (.int 1) =>
    match w with
    | .enter .this =>
      if CardAction.leftoverSourceThis who then some TriggeredAbility.onEnterConnive
      else none
    | .attack .this .all =>
      if CardAction.leftoverSourceThis who then some TriggeredAbility.onAttackConnive
      else none
    | .combatStart p =>
      if CardAction.leftoverYou p &&
          CardAction.leftoverCreatureYouControlTarget? who then
        some TriggeredAbility.onCombatTargetYouControlConnives
      else none
    | .attack among .all =>
      if CardAction.leftoverEquippedCreatureYouControl among &&
          CardAction.leftoverEquippedCreatureYouControl who then
        some TriggeredAbility.onEquippedCreatureYouControlAttacksConnive
      else none
    | _ => none
  | _ =>
    if !CardAction.leftoverYou who then none
    else
      match w, k with
      | .enter .this, .recruit => some TriggeredAbility.onEnterRecruit
      | .die .this, .recruit => some TriggeredAbility.onDiesRecruit
      | .enter .this, .amass .goblin (.int (.ofNat n)) => some (TriggeredAbility.onEnterAmassGoblins n)
      | .die .this, .amass .goblin (.int (.ofNat n)) => some (TriggeredAbility.onDiesAmassGoblins n)
      | .die .this, .amass .goblin (.greatestPower (.source .this)) =>
        some TriggeredAbility.onDiesAmassGoblinsEqualPower
      | .or (.enter .this) (.attack .this .all), .recruit =>
        some TriggeredAbility.onEnterOrAttackRecruit
      | .or (.enter .this) (.attack .this .all), .amass .goblin (.int (.ofNat n)) =>
        some (TriggeredAbility.onEnterOrAttackAmassGoblins n)
      | .attackSimultaneously among dest _, .amass .goblin (.int (.ofNat n)) =>
        if dest == .all && among.shape.sameController then
          some (TriggeredAbility.onYouAttackAmassGoblins n)
        else none
      | .attackSimultaneously among dest _, .recruit =>
        if dest == .all && among.shape.sameController then
          some TriggeredAbility.onYouAttackRecruit
        else none
      | .castSpell among, .amass .goblin (.int (.ofNat n)) =>
        if Selector.youCastNoncreatureSpell among then
          some (TriggeredAbility.onCastNoncreatureAmassGoblins n)
        else none
      | .ordinal 1 .turnStart (.castSpell among), .recruit =>
        if Selector.opponentCastsNoncreatureSpell among then
          some TriggeredAbility.onOpponentCastsFirstNoncreatureRecruit
        else none
      | .leaveGraveyard among, .amass .goblin (.int (.ofNat n)) =>
        if CardAction.leftoverYourGyCreatures? among then
          some (TriggeredAbility.onCreatureCardLeavesYourGyAmassGoblins n)
        else none
      | _, _ => none

/-- Triggered abilities of cards read with `parseOracleParts` that compile to
one named `TriggeredAbility`. -/
def printedTriggeredAbility? : Ability → Option TriggeredAbility
  -- Beorn the Fierce: a trample counter, a Bear subtype, then a draw.
  | .triggered (.combatStart (.controller .this)) (.sequence [
      .putCounter (.targets _ (.range (.int 0) (.int 1)) who) .trample (.int 1),
      .continuous [.gainSubtype (.targetReference _) .bear] .endOfGame,
      .if (.greaterOrEqual (.count bears) (.int 3)) [.draw drawer (.int 2)]]) =>
    if who == .intersection [.zone .battlefield, .cardType .creature, .controlled (.controller .this)] &&
        bears == .intersection [.zone .battlefield, .subtype .bear, .controlled (.controller .this)] &&
        drawer == .controller .this then
      some TriggeredAbility.onYourBeginCombatTrampleCounterBecomeBear
    else none
  -- Bolg of the North: record the sacrificed creature's power, then a
  -- reflexive damage ability. Excess damage of that damage action is amassed.
  | .triggered (.enter .this) (.sequence [
      .optional who (.sequence [
        .defineSelectorVariable _ _,
        .defineValueVariable power (.greatestPower _),
        .actionId id (.sacrifice _)]),
      .reflexive id' [
        .actionId damageId (.dealDamage _ _ (.variable power')),
        .if (.happened (.actionWithIdDealtExcessDamage dealt) _) [
          .keyword amasser (.amass .goblin (.excessDamageOfActionWithId excess))]]]) =>
    if id == id' && power == power' && damageId == dealt && damageId == excess &&
        who == .controller .this && amasser == .controller .this then
      some TriggeredAbility.onEnterBolgMaySacrifice
    else none
  -- Desert Were-Worm: the first attack each turn whose creatures have
  -- total power 12 or greater untaps those attackers and adds a combat.
  -- “For the first time each turn” is `ordinal` 1 since turn start.
  -- The power predicate is part of the attack, so a lower total does not
  -- trigger the ability.
  | .triggered
      (.ordinal 1 .turnStart
        (.attackSimultaneously
          (.intersection [.zone .battlefield, .cardType .creature, ctl]) .all
          [.totalPowerAtLeast 12]))
      (.sequence [
        .untap attackers,
        .addPhaseAfterThisPhase .combat]) =>
    if ctl == .controlled (.controller .this) &&
        attackers == .intersection [
          .zone .battlefield, .cardType .creature, .attacking .all] then
      some (TriggeredAbility.onAttackWithTotalPowerUntapExtraCombat 12)
    else none
  -- Getaway Barrel: reveal the top thirteen cards, bind the random
  -- creature to a selector variable, put that card onto the battlefield,
  -- and put the rest on the bottom in a random order.
  | .triggered (.putToGraveyard .this) (.sequence [
      .actionId revealId (.reveal (.topOfLibrary who (.int 13))),
      .defineSelectorVariable varId
        (.chooseRandom
          (.intersection [.wasObjectOfAction revealed, .cardType .creature])),
      .putOntoBattlefield (.variable put),
      .putOnLibraryBottomInRandomOrder
        (.intersection [
          .wasObjectOfAction rest,
          .not (.variable excluded)])]) =>
    if who == .controller .this && revealId == revealed && revealId == rest &&
        varId == put && varId == excluded then
      some (TriggeredAbility.onDiesRevealTopPutRandomCreature 13)
    else none
  -- Dwalin, Weaponmaster: a hone counter on each Equipment you control.
  | .triggered (.or (.enter .this) (.attack .this .all))
      (.putCounter
        (.intersection [.zone .battlefield, .subtype .equipment, ctl]) .hone (.int 1)) =>
    if ctl == .controlled (.controller .this) then
      some TriggeredAbility.onEnterOrAttackHoneEachEquipment
    else none
  -- Dáin Ironfoot: create an Axe, then attach it when you do.
  | .triggered (.enter .this) (.sequence [
      .actionId id (.createTokens _ _ parts _),
      .reflexive id' [
        .attach (.wasCreatedByAction created)
          (.target _ (.intersection [
            .zone .battlefield, .cardType .creature, .controlled (.controller .this)]))]]) =>
    if id == id' && id == created && CardAction.leftoverAxeToken? parts then
      some TriggeredAbility.onEnterCreateAxeAttach
    else none
  -- Dáin Ironfoot: attacking hosts of Equipment gain double strike.
  | .triggered (.attack .this .all)
      (.continuous [
        .gainAbility
          (.intersection [
            .zone .battlefield, .cardType .creature, .attacking .all,
            .hostOf (.intersection [.zone .battlefield, .subtype .equipment])])
          (.keyword .doubleStrike)]
        .endOfTurn) =>
    some TriggeredAbility.onAttackEquippedGainDoubleStrike
  -- Elrond, Moon-Reader: the first time each turn this ability's controller
  -- activates an ability of a creature, draw a card. Another player's
  -- activation does not trigger it. “This ability triggers only once each
  -- turn” is `ordinal` 1 since turn start.
  | .triggered
      (.ordinal 1 .turnStart
        (.activateAbility activator
          (.intersection [.zone .battlefield, .cardType .creature])))
      (.draw who (.int 1)) =>
    if activator == .controller .this && who == .controller .this then
      some TriggeredAbility.onActivateCreatureAbilityDrawOnce
    else none
  | .triggered (.triggerId id (.castSpell among))
      (.sequence [
        .optional (.controller .this)
          (.actionId drawId
            (.draw drawer (.greatestManaSpent (.wasArgumentOfTrigger spellId 1)))),
        .if (.happened (.actionWithId ifId) .gameStart)
          [.discard discarder (.int 2)]]) =>
    if id == drawId && id == spellId && id == ifId &&
        Selector.youCastNoncreatureSpell among &&
        CardAction.leftoverYou drawer && CardAction.leftoverYou discarder then
      some TriggeredAbility.onCastNoncreatureMayDrawXDiscard2
    else none
  | .triggered (.triggerId id (.castSpell among))
      (.putCounter (.target id' who) .plusOnePlusOne
        (.greatestManaValue (.wasArgumentOfTrigger id'' 1))) =>
    let you := Selector.controlled (.controller .this)
    if id == id' && id == id'' &&
        among == .intersection [.spell, .cardType .creature, you] &&
        who == .intersection [.zone .battlefield, .cardType .creature, you] then
      some TriggeredAbility.onCastCreaturePlusOneEqualMv
    else none
  | .triggered (.attack .this .all)
      (.sequence [
        .optional chooser
          (.actionId id
            (.sacrifice
              (.selected picker (.range 1 1)
                (.intersection [
                  .not .this, .zone .battlefield, .cardType .creature, you])))),
        .if (.happened (.actionWithId id') .gameStart)
          [.putCounter (.source .this) .plusOnePlusOne
            (.greatestPower (.wasObjectOfAction id''))]
      ]) =>
    let youCtl := Selector.controlled (.controller .this)
    if CardAction.leftoverYou chooser && CardAction.leftoverYou picker &&
        you == youCtl && id == id' && id == id'' then
      some TriggeredAbility.onAttackMaySacAnotherPlusOneEqualPower
    else none
  | .triggered (.enter .this)
      (.sequence [
        .putCounter (.source .this) (.hone)
          (.count
            (.intersection [
              .zone .battlefield,
              .cardType .creature,
              .controlled (.target id (.opponent (.controller .this)))])),
        .attach .this
          (.targets id2 (.range 0 1)
            (.intersection [
              .zone .battlefield,
              .cardType .creature,
              .controlled (.controller .this)]))
      ]) =>
    if id2 == id + 1 then
      some TriggeredAbility.onEnterHonePerOppCreaturesAttach
    else none
  | .triggered (.endStep (.controller .this))
      (.sequence [
        .actionId id (.removeCounter (.source .this) (.hope) (.int 1)),
        .if (.happened (.actionWithId id') .gameStart) [
          .draw who (.int 1),
          .if (.not (.any (.intersection [.source .this, .hasCounter (.hope)]))) [
            .sacrifice (.source .this),
            .gainLife who' (.int 4)]]
      ]) =>
    if id == id' && CardAction.leftoverYou who && CardAction.leftoverYou who' then
      some TriggeredAbility.onYourEndStepRemoveHopeDrawSac
    else none
  | .triggered (.endStep .player)
      (.if (.not (.and
          (.not (.happened (.attack attackers .all) .turnStart))
          (.not (.happened (.enter entered) .turnStart))))
        [.draw who (.int 1)]) =>
    match Selector.subtypesYouControl? attackers with
    | some (#[st], false) =>
      if attackers == entered && who == .controller .this then
        some (TriggeredAbility.onEachEndStepDrawIfAttackedOrEnteredSubtype st)
      else none
    | _ => none
  | .triggered (.enter .this)
      (.sequence [
        .draw drawer (.int 1),
        .optional chooser (.putOntoBattlefieldInState
          (.selected picker (.range (.int 1) (.int 1))
            (.intersection [.zone .hand, .owner owner, .cardType .land])) [.tapped])]) =>
    let you := Selector.controller .this
    if drawer == you && chooser == you && picker == you && owner == you then
      some .onEnterDrawMayPutLandTapped
    else none
  | .triggered (.enter .this)
      (.ifElse (.greaterOrEqual (.count among) (.int 2))
        [.createTokens who (.int 1) parts [.tapped]]
        [.mill who' (.int 2)]) =>
    if CardAction.leftoverYourGyCreatures? among && who == .controller .this &&
        who' == .controller .this && CardAction.leftoverTokenKind? parts == some .villain21menace then
      some .onEnterVillainIfGyElseMill
    else none
  | .triggered (.triggerId 1
      (.enter (.intersection [.not .this, .zone .battlefield, .cardType .creature, .controlled (.controller .this)])))
      (.if (.not (.and
          (.not (.greater (.greatestPower (.wasArgumentOfTrigger 1 1)) (.greatestPower (.source .this))))
          (.not (.greater (.greatestToughness (.wasArgumentOfTrigger 1 1))
            (.greatestToughness (.source .this))))))
        [.putCounter (.source .this) .plusOnePlusOne 1]) =>
    some (.onWatch Effect.watchHulklingCompare)
  | .triggered (.castSpell (.intersection [.spell, .controlled (.controller .this)]))
      (.if (.any (.intersection [
          .zone .battlefield,
          .cardType .creature,
          .controlled (.controller .this),
          .isTargetOf .this]))
        [.continuous [.gainAbility (.source .this)
          (.activated [.tapSymbol]
            (.dealDamage (.source .this) (.target _ (.not .this)) (.greatestPower (.source .this))))]
          .endOfTurn]) =>
    some (.onCasting Effect.castingIronFistTap)
  | .triggered (.attack .this .all)
      (.if (.happened (.enter (.intersection [.zone .battlefield, .cardType .artifact, .controlled (.controller .this)]))
          .turnStart)
        [.draw who (.int 1)]) =>
    if who == .controller .this then some (.onThisAttack Effect.thisAttackIfArtifactEnteredDraw) else none
  | .triggered (.upkeep (.controller (.hostOf .this))) (.draw (.controller (.hostOf .this)) (.int 1)) =>
    some (.onStep Effect.stepEnchantedControllerDraws)
  | .triggered (.combatStart (.controller .this))
      (.optional chooser (.sequence [
        .actionId id (.putOntoBattlefield (.selected picker (.range (.int 1) (.int 1))
          (.intersection [.zone .hand, .owner owner, .cardType .artifact]))),
        .if (.anySubtype (.wasObjectOfAction id') .equipment)
          [.attach (.wasObjectOfAction id'') (.source .this)]])) =>
    let you := Selector.controller .this
    if chooser == you && picker == you && owner == you && id == id' && id == id'' then
      some .onCombatMayPutArtifactAttachEquipment
    else none
  | .triggered (.castSpell (.intersection [.spell, .not (.cardType .creature), .controlled (.controller .this)]))
      (.chooseModeRestricted who
        [(1, .not (.happened (.modeWithIdChosen .player 1) .turnStart),
            [.continuous [.gainAbility (.source .this) (.keyword .doubleStrike)] .endOfTurn]),
         (2, .not (.happened (.modeWithIdChosen .player 2) .turnStart),
            [.continuous [.gainAbility (.source .this) (.keyword .indestructible)] .endOfTurn]),
         (3, .not (.happened (.modeWithIdChosen .player 3) .turnStart), [.draw drawer (.int 1)])]) =>
    if who == .controller .this && drawer == .controller .this then
      some (.onCasting Effect.castingVisionModes)
    else none
  | .triggered (.enter .this)
      (.sequence [
        .actionId id (.createTokens who (.int 1) parts []),
        .attach (.wasCreatedByAction id') (.source .this)]) =>
    if id == id' && who == .controller .this &&
        parts.contains (.name "Sturdy Shield") && parts.contains (.subtype .equipment) then
      some (.onEnter Effect.enterCreateSturdyShieldAttach)
    else none
  | .triggered (.endStep (.controller .this))
      (.sequence [.draw drawer (.int 1), .loseLife loser (.int 1)]) =>
    if drawer == .controller .this && loser == .controller .this then
      some .onYourEndStepDrawLoseLife
    else none
  | .triggered (.or (.enter .this) (.attack .this .all)) (.createTokens who (.int 1) parts []) =>
    if who == .controller .this then
      match CardAction.leftoverTokenKind? parts with
      | some .squirrel11green => some (.onEnterOrAttack Effect.enterOrAttackCreateSquirrel)
      | some .wall => some .onEnterOrAttackCreateWall
      | _ => none
    else none
  | .triggered
      (.putCountersSimultaneously (.controller .this) heroes .plusOnePlusOne)
      (.optional (.controller .this) (.createTokens who (.int 1) parts [])) =>
    if heroes == .intersection
        [.not .this, .zone .battlefield, .subtype .hero, .controlled (.controller .this)] &&
        who == .controller .this &&
        CardAction.leftoverTokenKind? parts == some .wall04defender then
      some (.onResource Effect.resourcePlusOneOnHeroesCreateWall)
    else none
  | .triggered (.enterSimultaneously tokens [])
      (.optional (.controller .this) (.draw (.controller .this) (.int 1))) =>
    if tokens == .intersection
        [.zone .battlefield, .token, .controlled (.controller .this)] then
      some (.onWatch Effect.watchTokensEnterMayDraw)
    else none
  | .triggered (.combatStart (.controller .this))
      (.putCounter (.target _ sel) .plusOnePlusOne 1) =>
    if sel == .intersection [.zone .battlefield, .cardType .creature, .controlled (.controller .this)] then
      some .onCombatPlusOneOnCreatureYouControl
    else none
  | .triggered (.attack .this .all)
      (.continuous [.addPower others (.greatestToughness src), .addToughness others' (.greatestToughness src')]
        .endOfTurn) =>
    match Selector.subtypesYouControl? others with
    | some (#[st], true) =>
      if others == others' && CardAction.leftoverSourceThis src && src == src' then
        some (TriggeredAbility.onAttackOthersOfSubtypeGetEqualToughness st)
      else none
    | _ => none
  | .triggered (.combatStart (.controller .this))
      (.continuous [.addPower (.target _ sel) (.greatestPower src)] .endOfTurn) =>
    if CardAction.leftoverSourceThis src &&
        sel == .intersection [.not .this, .zone .battlefield, .cardType .creature, .controlled (.controller .this)] then
      some TriggeredAbility.onCombatAnotherGetsSourcePower
    else none
  | .triggered (.combatStart .player)
      (.sequence [
        .continuous [.addPower others (.int p), .addToughness others' (.int t)] .endOfTurn,
        .continuous [.addPower opps (.int op), .addToughness opps' (.int ot)] .endOfTurn]) =>
    let oppCreatures : Selector :=
      .intersection [.zone .battlefield, .cardType .creature, .controlled (.opponent (.controller .this))]
    match Selector.subtypesYouControl? others with
    | some (subtypes, true) =>
      if others == others' && opps == oppCreatures && opps' == oppCreatures then
        some (TriggeredAbility.onEachCombatOthersGetAndOppsGet subtypes p t op ot)
      else none
    | _ => none
  | .triggered (.attack .this .all) (.dealDamage src (.opponent who) (.count among)) =>
    match Selector.subtypesYouControl? among with
    | some (#[st], false) =>
      if (src == .this || src == .source .this) && who == .controller .this then
        some (TriggeredAbility.onAttackDamageEqualSubtypeToEachOpponent st)
      else none
    | _ => none
  | .triggered (.enter .this)
      (.sequence [
        .draw drawer (.int 1),
        .if (.not (.any among))
          [.putOnBottomOfLibrary (.selected chooser (.range (.int 1) (.int 1))
            (.intersection [.zone .hand, .owner owner]))]]) =>
    if drawer == .controller .this && chooser == .controller .this &&
        owner == .controller .this && among == Selector.aLegendaryCreatureYouControl then
      some TriggeredAbility.onEnterDrawThenBottomIfNoLegendary
    else none
  | .triggered
      (.enter (.intersection [
        .not .this, .zone .battlefield, .cardType .creature, .controlled (.controller .this),
        .powerAtMost (.int p)]))
      (.optionalPayFor payer [.mana [.generic g]] [.draw drawer (.int 1)]) =>
    if payer == .controller .this && drawer == .controller .this then
      some (TriggeredAbility.onAnotherCreatureYouControlPowerAtMostEntersMayPayDraw p g)
    else none
  | .triggered (.attack .this .all)
      (.sequence [
        .actionId id (.tap (.selected chooser .any
          (.intersection [.zone .battlefield, .subtype .human, .not .tapped, .controlled (.controller .this)]))),
        .draw drawer (.count (.wasObjectOfAction id'))]) =>
    if id == id' && chooser == .controller .this && drawer == .controller .this then
      some TriggeredAbility.onAttackTapHumansDraw
    else none
  | .triggered (.or (.enter .this) (.attack .this .all))
      (.sequence [
        .returnToHand (.target id
          (.intersection [.zone .graveyard, .subtype .elf, .owner owner])),
        .gainLife gainer (.greatestPower (.targetReference id'))]) =>
    if id == id' && owner == .controller .this && gainer == .controller .this then
      some TriggeredAbility.onEnterOrAttackReturnElfGainLife
    else none
  | .triggered (.attack .this .all)
      (.continuous [.addPower (.source .this) (.greatestPower among)] .endOfTurn) =>
    if among == .intersection [.zone .battlefield, .cardType .creature, .controlled (.controller .this)] then
      some TriggeredAbility.onAttackPumpByGreatestPower
    else none
  | .triggered (.enter .this)
      (.sequence [
        .actionId id (.destroy (.intersection [
          .zone .battlefield, .union [.cardType .artifact, .cardType .enchantment],
          .controlled (.opponent (.controller .this))])),
        .gainLife gainer (.count (.wasObjectOfAction id'))]) =>
    if id == id' && gainer == .controller .this then
      some TriggeredAbility.onEnterDestroyOppArtifactsEnchantmentsGainLife
    else none
  | .triggered (.enter .this)
      (.sequence [
        .tap (.hostOf .this),
        .removeAllCounters (.hostOf .this)]) =>
    some TriggeredAbility.onEnterTapEnchantedRemoveCounters
  | .triggered (.enter .this)
      (.sequence [
        .actionId id (.attach
          (.targets equipId .any
            (.intersection [.zone .battlefield, .subtype .equipment, .controlled (.controller .this)]))
          (.target creatureId
            (.intersection [.zone .battlefield, .cardType .creature, .controlled (.controller .this)]))),
        .if (.greaterOrEqual (.count (.wasObjectOfAction id')) (.int 1))
          [.dealDamage (.targetReference creatureId')
            (.targets damageId (.range (.int 0) (.int 1))
              (.intersection [.zone .battlefield, .cardType .creature]))
            (.greatestPower (.targetReference powerId))]]) =>
    if id == id' && creatureId == creatureId' && creatureId' == powerId &&
        equipId + 1 == creatureId && creatureId + 1 == damageId then
      some TriggeredAbility.onEnterAttachEquipmentThenFight
    else none
  | .triggered
      (.enter (.intersection [.zone .battlefield, .token, .controlled (.controller .this)]))
      (.sequence [
        .if (.not (.happened (.abilityWithIdResolved id1) .turnStart))
          [.gainLife who1 (.int 1)],
        .if (.and
            (.happened (.ordinal 1 .turnStart (.abilityWithIdResolved id2)) .turnStart)
            (.not (.happened (.ordinal 2 .turnStart (.abilityWithIdResolved id2b)) .turnStart)))
          [.draw who2 (.int 1)],
        .if (.and
            (.happened (.ordinal 2 .turnStart (.abilityWithIdResolved id3)) .turnStart)
            (.not (.happened (.ordinal 3 .turnStart (.abilityWithIdResolved id3b)) .turnStart)))
          [.putCounter
            (.intersection
              [.zone .battlefield, .cardType .creature, .controlled (.controller .this)])
            .plusOnePlusOne (.int 1)]]) =>
    if id1 == id2 && id2 == id2b && id2 == id3 && id3 == id3b &&
        who1 == .controller .this && who2 == .controller .this then
      some .onTokenYouControlEntersBelladonna
    else none
  | _ => none

/-- Compile a `.triggered` ability without the printed-card patterns. -/
def compileTriggeredAbility? : Ability → Option TriggeredAbility
  | .triggered (.attack .this .all) (.continuous effects _duration) =>
    if CardAction.leftoverSetOtherBasePT? effects then
      some TriggeredAbility.onAttackSetOtherBasePT
    else if CardAction.leftoverPumpForEachOtherCreature? effects then
      some TriggeredAbility.onAttackPumpForEachOtherCreature
    else
      match CardAction.leftoverPumpAndGrantKeywords? (.continuous effects .endOfTurn) with
      | some (2, 0, kws) =>
        match ContinuousEffect.targetingSelector? effects with
        | some sel =>
          if kws.trample && sel.targetingShape.anotherCreatureYouControl then
            some TriggeredAbility.onAttackOtherGets2AndTrample
          else none
        | none => none
      | _ =>
        let kws := CardAction.grantedKeywords effects
        match ContinuousEffect.targetingSelector? effects with
        | some sel =>
          if kws != Keywords.none && sel.targetingShape.attackingCreature then
            some (TriggeredAbility.onAttackTargetGainsKeywords kws)
          else none
        | none => none
  | .triggeredWhile (.attack .this .all) (.any among) (.gainLife _ (.int (.ofNat n))) =>
    if among.shape.ferocious then
      some (TriggeredAbility.onAttackFerociousGainLife n)
    else none
  | .triggeredWhile (.attack .this .all) (.any among) (.continuous effects _) =>
    if among.shape.ferocious then
      match CardAction.leftoverSourceGetsAndTeamTrample? effects with
      | some p => some (TriggeredAbility.onAttackFerociousSourceGetsAndTeamTrample p)
      | none =>
        match CardAction.leftoverSourcePump? effects with
        | some (p, t) => some (TriggeredAbility.onAttackFerociousSourceGets p t)
        | none => none
    else none
  | .triggeredWhile (.attack .this .all) (.any among) (.putCounter sel .plusOnePlusOne 1) =>
    if among.shape.ferocious &&
        sel.shape.sameController && sel.shape.types.eqTypes [.creature] then
      some TriggeredAbility.onAttackFerociousPlusOneEach
    else none
  | .triggered (.attack .this .all)
      (.if (.any (.intersection [.source .this, .powerAtLeast (.int 4)]))
        [.draw who (.int 1)]) =>
    if CardAction.leftoverYou who then
      some (TriggeredAbility.onThisAttack Effect.thisAttackDrawIfPower4)
    else none
  | .triggered (.draw who .all)
      (.if (.any (.intersection [.not .this, .zone .battlefield, .subtype .hero, ctl]))
        [.dealDamage .this (.target _ (.opponent (.controller .this))) (.int 1)]) =>
    if CardAction.leftoverYou who && ctl == .controlled (.controller .this) then
      some (TriggeredAbility.onResource Effect.resourceDrawIfAnotherHeroDamage)
    else none
  | .triggered (.attack .this .all) (.scry _ (.int (.ofNat n))) =>
    some (TriggeredAbility.onAttackScry n)
  | .triggered (.attack .this .all) (.surveil who (.int (.ofNat n))) =>
    if CardAction.leftoverYou who then
      some (TriggeredAbility.onAttackScry n)
    else none
  | .triggered (.block _ src) (.dealDamage dealer dest (.int 1)) =>
    if src == .this && dealer == .this && dest == .blocking .this then
      some TriggeredAbility.onBecomesBlockedDeal1ToBlockers
    else none
  | .triggered (.castSpell among) (.dealDamage _ (.opponent _) (.int (.ofNat n))) =>
    if among.shape.types.eqTypes [.instant, .sorcery] && among.shape.sameController then
      some (TriggeredAbility.onCastInstantOrSorceryDealDamageToEachOpponent n)
    else none
  | .triggered (.castSpell among) (.putCounter sel .plusOnePlusOne 1) =>
    if Selector.youCastNoncreatureSpell among &&
        sel.shape.other && sel.shape.sameController &&
        sel.shape.types.eqTypes [.creature] then
      some (TriggeredAbility.onCasting Effect.castingPlusOneEachOther)
    else none
  | .triggered (.castSpell among)
      (.if (.any creatureSel)
        [.putCounter (.source .this) .plusOnePlusOne 1]) =>
    if among.shape.sameController && Selector.includesSpell among &&
        Selector.includesIsTargetOf creatureSel &&
        creatureSel.shape.sameController &&
        creatureSel.shape.types.eqTypes [.creature] then
      some (TriggeredAbility.onCasting Effect.castingPlusOneThis)
    else none
  | .triggered (.castSpell among)
      (.if (.any creatureSel)
        [.putCounter (.source .this) .plusOnePlusOne 1, .scry who (.int 1)]) =>
    if among.shape.sameController && Selector.includesSpell among &&
        Selector.includesIsTargetOf creatureSel &&
        creatureSel.shape.sameController &&
        creatureSel.shape.types.eqTypes [.creature] &&
        CardAction.leftoverYou who then
      some (TriggeredAbility.onCasting Effect.castingPlusOneScry)
    else none
  | .triggered (.enter .this) (.draw (.controller .this) (.int (.ofNat n))) =>
    some (TriggeredAbility.onEnterDraw n)
  | .triggered (.enter .this) (.scry _ (.int (.ofNat n))) =>
    some (TriggeredAbility.onEnterScry n)
  | .triggered (.enter .this) (.surveil who (.int (.ofNat n))) =>
    if CardAction.leftoverYou who then
      some (TriggeredAbility.onEnterSurveil n)
    else none
  | .triggered (.enter .this) (.gainLife _ (.int (.ofNat n))) =>
    some (TriggeredAbility.onEnterGainLife n)
  | .triggered (.enter .this)
      (.sequence [
        .actionId id (.exile (.topOfLibrary who 1)),
        .continuous [.canPlay permit (.wasCreatedByAction created)] duration
      ]) =>
    if CardAction.leftoverExileTopPlayUntilEndOfNextTurn?
        (.sequence [
          .actionId id (.exile (.topOfLibrary who 1)),
          .continuous [.canPlay permit (.wasCreatedByAction created)] duration
        ]) then
      some TriggeredAbility.onEnterExileTop
    else none
  | .triggered (.enter .this) (.searchLibraryThenShuffle _ actions) =>
    CardAction.leftoverEnterSearch? actions
  | .triggered (.enter .this) (.continuous effects _duration) =>
    match ContinuousEffect.targetingSelector? effects, ContinuousEffect.addedPT? effects with
    | some sel, some (p, t) =>
      if sel.toTargetKind == .creature then
        some (TriggeredAbility.onEnterTargetGets p t)
      else none
    | _, _ =>
      match CardAction.leftoverPumpAndGrantKeywords? (.continuous effects .endOfTurn) with
      | some (p, 0, kws) =>
        if kws.firstStrike then
          match ContinuousEffect.massSelector? effects with
          | some among =>
            if among.shape.sameController && among.shape.types.eqTypes [.creature] then
              some (TriggeredAbility.onEnterCreaturesYouControlGetAndFirstStrike p)
            else none
          | none => none
        else none
      | _ =>
        let kws := CardAction.grantedKeywords effects
        if kws != Keywords.none &&
            effects.any (fun e => ContinuousEffect.selector e == .hostOf .this) then
          some (TriggeredAbility.onEnterEnchanted (.grantKeywords kws))
        else none
  | .triggered (.enter .this) (.putCounter sel .plusOnePlusOne 1) =>
    if sel.toTargetKind == .creature then
      some TriggeredAbility.onEnterPlusOneOnCreature
    else none
  | .triggered (.enter .this) (.attach .this sel) =>
    match sel.among? with
    | some among =>
      let s := among.shape
      if s.sameController && s.types.eqTypes [.creature] then
        if Selector.includesLegendary among then
          some TriggeredAbility.onEnterAttachToLegendary
        else
          match s.subtype with
          | some st => some (TriggeredAbility.onEnterAttachToSubtype st)
          | none => some TriggeredAbility.onEnterAttachToCreatureYouControl
      else none
    | none => none
  | .triggered (.enter .this) (.sequence [.attach .this sel, .untap _]) =>
    match sel.among? with
    | some among =>
      let s := among.shape
      if s.sameController && s.types.eqTypes [.creature] then
        some (TriggeredAbility.onEnterAttachThen PermanentAction.untap)
      else none
    | none => none
  | .triggered (.enter .this) (.sequence [.attach .this sel, .continuous effects _]) =>
    match sel.among? with
    | some among =>
      let s := among.shape
      let kws := CardAction.grantedKeywords effects
      if s.sameController && s.types.eqTypes [.creature] && kws != Keywords.none then
        some (TriggeredAbility.onEnterAttachThen (.grantKeywords kws))
      else none
    | none => none
  | .triggered
      (.ordinal 2 .turnStart (.draw (.controller .this) .all))
      (.putCounter (.source .this) .plusOnePlusOne 1) =>
    some TriggeredAbility.onDrawSecondPlusOne
  | .triggered
      (.ordinal 2 .turnStart (.draw (.opponent (.controller .this)) .all))
      action =>
    if CardAction.leftoverCreateTokensKindN? action == some (.treasure, 1) then
      some TriggeredAbility.onOpponentDrawsSecondCreateTreasure
    else none
  | .triggered
      (.ordinal 2 .turnStart (.draw (.controller .this) .all))
      action =>
    if CardAction.leftoverPlusOneAndLifelinkTarget? action then
      some TriggeredAbility.onDrawSecondPlusOneLifelink
    else
      match CardAction.leftoverCreateTokensKindN? action with
      | some (kind, 1) => some (TriggeredAbility.onYouDrawSecondCreateTokens kind)
      | _ =>
        match CardAction.leftoverEachOpponentLoseLifeYouGain? action with
        | some 1 => some (TriggeredAbility.onResource Effect.resourceSecondDrawDrain)
        | _ =>
          match action with
          | .mill who (.int (.ofNat n)) =>
            if CardAction.leftoverTargetPlayer? who then
              some (TriggeredAbility.onDrawSecondMillPlayer n)
            else none
          | .putCounter sel .plusOnePlusOne 1 =>
            if sel.toTargetKind == .creature then
              some (TriggeredAbility.onResource Effect.resourceSecondDrawPlusOneTarget)
            else none
          | _ => none
  | .triggered (.draw (.controller .this) .all)
      (.putCounter (.source .this) .plusOnePlusOne 1) =>
    some TriggeredAbility.onDrawPlusOne
  | .triggered (.combatDamage .this .player)
      (.sequence [.draw (.controller .this) 1, .discard (.controller .this) 1]) =>
    some TriggeredAbility.onCombatDamageToPlayerLoot
  | .triggered (.combatDamage .this .player) (.draw _ (.int (.ofNat n))) =>
    some (TriggeredAbility.onCombatDamageDraw n)
  | .triggered (.damageSimultaneously among .player preds)
      (.putCounter (.source .this) .plusOnePlusOne 2) =>
    -- One trigger when those Heroes deal damage at the same time
    -- (CR 603.2c), including combat damage and noncombat damage.
    if preds.isEmpty && among.shape.sameController &&
        among.shape.subtype == some "Hero" then
      some (TriggeredAbility.onWatch Effect.watchHeroesDamagePlusTwo)
    else none
  | .triggered (.die .this) (.continuous effects _duration) =>
    match ContinuousEffect.targetingSelector? effects, ContinuousEffect.addedPT? effects with
    | some sel, some (p, t) =>
      if sel.toTargetKind == .oppCreature then
        some (TriggeredAbility.onDiesOppCreatureGets p t)
      else none
    | _, _ => none
  | .triggered (.die .this) (.draw _ (.int (.ofNat n))) =>
    some (TriggeredAbility.onDiesDraw n)
  | .triggered (.die .this) (.dealDamage _ dest (.greatestPower _)) =>
    if dest.toTargetKind == .oppCreature then
      some TriggeredAbility.onDiesDealDamageEqualToPowerToOppCreature
    else none
  | .triggered (.dieSimultaneously among _) (.scry _ (.int (.ofNat n))) =>
    if among.shape.otherCreatures then
      some (TriggeredAbility.onOneOrMoreOtherCreaturesDieScry n)
    else none
  | .triggered (.enter .this)
      (.sacrifice
        (.selected (.target _ (.opponent _)) _
          (.intersection [
            .zone .battlefield,
            .cardType .creature,
            .controlled (.targetReference _)]))) =>
    some TriggeredAbility.onEnterTargetOpponentSacrificesCreature
  | .triggered (.enter .this)
      (.forEachVariable n among actions) =>
    if CardAction.leftoverEachPlayerSacrificesCreature? (.forEachVariable n among actions) then
      some TriggeredAbility.onEnterEachPlayerSacrificesCreature
    else if CardAction.leftoverExileOppNonlandEachUntilLeaves?
        (.forEachVariable n among actions) then
      some TriggeredAbility.onEnterExileOppNonlandEachUntilLeaves
    else none
  | .triggered (.enter .this)
      (.sequence [
        .exile
          (.targets _
            (.range 0 1)
            (.intersection [.zone .graveyard, .owner (.opponent _)])),
        .loseLife (.opponent _) (.int (.ofNat n))]) =>
    some (TriggeredAbility.onEnterExileOppGyCardOppsLoseLife n)
  | .triggered (.enter .this) (.discard (.opponent _) 1) =>
    some TriggeredAbility.onEnterEachOpponentDiscards
  | .triggered (.enter .this)
      (.divideDamage _ _ (.targets _ (.range 1 (.int (.ofNat maxTargets))) _) (.int (.ofNat amount))) =>
    some (TriggeredAbility.onEnterDealDividedDamage amount maxTargets)
  | .triggered
      (.or (.enter .this) (.attack .this .all))
      (.divideDamage _ _ (.targets _ (.range 1 (.int (.ofNat maxTargets))) _) (.int (.ofNat amount))) =>
    some (TriggeredAbility.onEnterOrAttackDealDividedDamage amount maxTargets)
  | .triggered (.enter .this)
      (.sequence [
        .optional (.controller .this) (.actionId id (.discard _ 1)),
        .if (.happened (.actionWithId id') _) [.draw _ (.int (.ofNat n))]]) =>
    if id == id' then some (TriggeredAbility.onEnterMayDiscardDraw n) else none
  | .triggered (.enter among) (.putCounter sel .plusOnePlusOne 1) =>
    if among.shape.landYouControl && sel.toTargetKind == .creatureYouControl then
      some TriggeredAbility.onLandYouControlEntersPlusOnePlusOne
    else if among == .this && sel.toTargetKind == .creature then
      some TriggeredAbility.onEnterPlusOneOnCreature
    else if among.shape.anotherArtifactYouControl &&
        (sel == .source .this || sel == .this) then
      some TriggeredAbility.onAnotherArtifactEntersPlusOne
    else none
  | .triggered (.enter among) (.draw (.controller .this) 1) =>
    match among.anotherSubtypeOrEquipment? with
    | some st =>
      some (TriggeredAbility.onAnotherSubtypeOrEquipmentEntersDrawOnce st)
    | none =>
      if among.includedSubtype? == some "Equipment" && among.shape.sameController then
        some TriggeredAbility.onEquipmentYouControlEntersDraw
      else if among.shape.artifactYouControl then
        some TriggeredAbility.onArtifactYouControlEntersDraw
      else none
  | .triggered (.enter among) (.continuous effects _duration) =>
    if among.shape.anotherElfYouControl then
      match CardAction.leftoverSourcePump? effects with
      | some (1, 1) => some TriggeredAbility.onAnotherElfYouControlEntersGets1
      | _ => none
    else if Selector.anotherVillainYouControl among then
      match CardAction.leftoverPumpAndGrantKeywords? (.continuous effects .endOfTurn) with
      | some (1, 0, kws) =>
        if kws.lifelink then
          some (TriggeredAbility.onWatch Effect.watchVillainPlusOneLifelink)
        else none
      | _ => none
    else if among.shape.landYouControl then
      match CardAction.leftoverSourcePump? effects with
      | some (p, t) => some (TriggeredAbility.onLandYouControlEntersGets p t)
      | none => none
    else none
  | .triggered (.enter .this) (.chooseUniqueModes r modes) =>
    if r == .range 0 .x && CardAction.wreckingCrewModes? modes then
      some (TriggeredAbility.onEnter Effect.enterChooseUpToXModes)
    else if CardAction.leftoverTapOrUntapNonland? modes then
      some TriggeredAbility.onEnterTapOrUntapNonland
    else if CardAction.leftoverPlusOnesOrReturnArtEnch? modes then
      some (TriggeredAbility.onEnter Effect.enterPlusOnesOrReturnArtEnch)
    else none
  | .triggered (.enter .this) action =>
    if CardAction.leftoverAttachTargetEquipment? action then
      some TriggeredAbility.onEnterAttachTargetEquipment
    else
      match CardAction.leftoverDealDamageDestroyIfSubtype? action with
      | some (n, st) => some (TriggeredAbility.onEnterDealDamageDestroyIfSubtype n st)
      | none =>
        match CardAction.leftoverUntapPlusOneIfSubtype? action with
        | some st => some (TriggeredAbility.onEnterUntapOtherPlusOneIfSubtype st)
        | none =>
          match CardAction.leftoverExileThenReturnTapped? action with
          | some sel =>
            match sel with
            | .targets _ (.range 0 3) among =>
              if among.shape.landYouControl then
                some TriggeredAbility.onEnterExileLandsThenReturnTapped
              else none
            | _ => none
          | none =>
            match CardAction.leftoverMaySacArtifactOrDiscardDraw? action with
            | some 1 => some TriggeredAbility.onEnterMaySacArtifactOrDiscardDraw
            | _ =>
              CardAction.leftoverEnterThisAction? action
  | .triggered (.enter among) (.chooseModeRestricted who modes) =>
    if among.shape.anotherCreatureYouControl &&
        CardAction.leftoverAllianceModes? who modes then
      some TriggeredAbility.onAnotherCreatureYouControlEntersAlliance
    else none
  | .triggered (.enter among) (.chooseUniqueModes _ modes) =>
    if among.shape.landYouControl && CardAction.leftoverTapOppOrUntapYours? modes then
      some TriggeredAbility.onLandYouControlEntersTapOrUntap
    else if CardAction.leftoverNontokenHeroModal? among modes then
      some (TriggeredAbility.onWatch Effect.watchNontokenHeroModal)
    else none
  | .triggered (.enter among) (.optional (.controller .this) (.continuous effects .endOfTurn)) =>
    if among.shape.landYouControl then
      match CardAction.leftoverSourceSetBasePT? effects with
      | some (p, t) => some (TriggeredAbility.onLandYouControlEntersBecomePT p t)
      | none => none
    else none
  | .triggered (.enter among) action =>
    match CardAction.leftoverPlusOneVigilance? action with
    | some 2 =>
      if among.shape.landYouControl then
        some TriggeredAbility.onLandYouControlEntersPlusOneVigilance
      else none
    | _ =>
      match action with
      | .dealDamage _ dest (.int 1) =>
        let opp :=
          dest == .opponent (.controller .this) ||
            match dest with
            | .target _ .player => true
            | .target _ (.opponent _) => true
            | _ => false
        if Selector.anotherVillainOrArtifactYouControl among && opp then
          some (TriggeredAbility.onWatch Effect.watchVillainOrArtifactDamage)
        else none
      | .draw (.controller .this) 1 =>
        if among.includedSubtype? == some "Equipment" && among.shape.sameController then
          some TriggeredAbility.onEquipmentYouControlEntersDraw
        else if among.shape.artifactYouControl then
          some TriggeredAbility.onArtifactYouControlEntersDraw
        else none
      | .sequence [.draw (.controller .this) 1, .putCounter sel .plusOnePlusOne 1] =>
        if among.shape.landYouControl &&
            (sel == .source .this || sel == .this) then
          some TriggeredAbility.onLandYouControlEntersDrawPlusOneSource
        else none
      | .createTokens who n parts [] =>
        if among.shape.landYouControl && CardAction.leftoverYou who then
          match valToNat? n with
          | some n =>
            CardAction.leftoverTokenKind? parts |>.map
              (fun k => TriggeredAbility.onLandYouControlEntersCreateTokens k n)
          | none => none
        else none
      | _ =>
        if Selector.anotherVillainYouControl among &&
            CardAction.leftoverAttachTargetEquipment? action then
          some (TriggeredAbility.onWatch Effect.watchVillainAttachEquipment)
        else none
  | .triggered (.attack .this .all)
      (.sequence [
        .actionId id (.mayCast who among),
        .continuous
          [.replace
            (.putToGraveyard
              (.intersection [
                .wasObjectOfAction id',
                .union [.cardType .instant, .cardType .sorcery]]))
            [.exile .replacingObject]]
          .endOfGame]) =>
    -- An instant or sorcery cast from the graveyard this way is exiled
    -- instead of being put into its owner's graveyard. The replacement
    -- lasts until the end of the game.
    if id == id' && who == .controller .this &&
        among == .selected (.controller .this) (.range 1 1) (.intersection [
          .zone .graveyard,
          .owner (.controller .this),
          .union [
            .cardType .artifact,
            .cardType .instant,
            .cardType .sorcery]]) then
      some TriggeredAbility.onAttackCastFromGyArtifactInstantSorcery
    else none
  | .triggered (.attack .this .all) action =>
    if CardAction.leftoverDamageEqualTreasures? action then
      some TriggeredAbility.onAttackDamageEqualTreasures
    else
    match CardAction.leftoverExileThenReturnTapped? action with
    | some sel =>
      match sel with
      | .targets _ (.range 0 1) among =>
        if among.shape.nontoken &&
            (among.shape.types.eqTypes [.artifact, .creature] ||
              among.shape.types.eqTypes [.creature] ||
              among.shape.types.eqTypes [.artifact]) then
          some (TriggeredAbility.onThisAttack Effect.thisAttackBlinkNontoken)
        else none
      | _ => none
    | none =>
      match action with
      | .keyword who k => leftoverKeywordTriggered? (.attack .this .all) who k
      | _ => none
  | .triggeredWhile (.attackSimultaneously among dest _) (.any ferociousSel) action =>
    if dest == .all && among.shape.sameController && ferociousSel.shape.ferocious then
      match CardAction.leftoverDrawLoseLifeSelf? action with
      | some (1, 1) => some TriggeredAbility.onYouAttackFerociousDrawLoseLife
      | _ => none
    else none
  | .triggered (.attackSimultaneously among dest _) (.draw (.controller .this) 1) =>
    if among.shape.sameController then
      if among.shape.subtype == some "Merfolk" then
        if dest == .player then
          some (TriggeredAbility.onWatch Effect.watchMerfolkAttackDraw)
        else none
      else if dest == .all then
        some TriggeredAbility.onYouAttackDraw
      else none
    else none
  | .triggered (.combatStart who) (.if (.any among) [.putCounter sel .plusOnePlusOne 1]) =>
    if who == .controller .this && among.shape.ferocious &&
        (sel == .source .this || sel == .this) then
      some TriggeredAbility.onYourBeginCombatFerociousPlusOne
    else none
  | .triggered w (.keyword who k) => leftoverKeywordTriggered? w who k
  | .triggered (.die .this) (.createTokens who n parts []) =>
    if CardAction.leftoverYou who then
      match valToNat? n with
      | some n =>
        CardAction.leftoverTokenKind? parts |>.map (fun k => TriggeredAbility.onDiesCreateTokens k n)
      | none => none
    else none
  | .triggered (.sacrifice among) (.loseLife sel 1) =>
    if among.shape.token && among.shape.sameController &&
        CardAction.leftoverTargetOpponent? sel then
      some TriggeredAbility.onYouSacrificeTokenOppLosesLife
    else none
  | .triggered (.combatDamage .this .player) (.chooseUniqueModes _ modes) =>
    if CardAction.leftoverWolfPlusOneOrTreasure? modes then
      some TriggeredAbility.onCombatDamageWolfPlusOneOrTreasure
    else none
  | .triggered (.combatDamage among dest) (.createTokens who n parts []) =>
    if CardAction.leftoverYou who && CardAction.leftoverPlayerOrBattle dest &&
        among.shape.sameController then
      match CardAction.leftoverTokenKind? parts, among.includedSubtype?, valToNat? n with
      | some kind, some st, some n =>
        some (TriggeredAbility.onSubtypeYouControlCombatDamageCreateTokens st kind n)
      | _, _, _ => none
    else none
  | .triggered (.attack (.hostOf .this) .all) action =>
    if CardAction.leftoverIfElseCreateSpiritsForEquipped? action then
      some TriggeredAbility.onEquippedAttacksCreateSpirits
    else none
  | .triggered (.ordinal 2 .turnStart (.castSpell among)) action =>
    if (among == .spell || among == .all) &&
        CardAction.leftoverLoseLifeCreateTreasure? action then
      some TriggeredAbility.onPlayerCastsSecondSpellLoseLifeCreateTreasure
    else none
  | .triggered (.castSpell among) (.createTokens who n parts []) =>
    if among.shape.sameController && among.shape.subtype == some "Villain" &&
        n == 1 && CardAction.leftoverYou who &&
        CardAction.leftoverTokenKind? parts == some .villain21menace then
      some (TriggeredAbility.onCasting Effect.castingVillainToken)
    else none
  | .triggered (.or (.enter .this) (.attack .this .all)) action =>
    if CardAction.leftoverPlusOneEachOtherGainLife? action then
      some TriggeredAbility.onEnterOrAttackPlusOneEachOtherGainLife
    else
      match action with
      | .putCounter sel .plusOnePlusOne 1 =>
        if sel.toTargetKind == .creature then
          some TriggeredAbility.onEnterOrAttackPlusOneOnCreature
        else none
      | _ => none
  | .triggered (.attackSimultaneously among dest preds) action =>
    if dest == .player && among.shape.sameController &&
        among.shape.types.eqTypes [.creature] &&
        preds == [.countAtLeast 2] &&
        CardAction.leftoverGrantFlyingToAttacking? action then
      some TriggeredAbility.onAttackWithTwoOrMoreGrantFlying
    else none
  | .triggered (.or (.enter .this) (.enter among)) (.createTokens who n parts []) =>
    if CardAction.leftoverYou who then
      match among.shape.anotherSubtypeYouControl, CardAction.leftoverTokenKind? parts,
          valToNat? n with
      | some st, some kind, some n =>
        if among.shape.nontoken then
          some (TriggeredAbility.onThisOrNontokenSubtypeEntersCreateTokens st kind n)
        else
          some (TriggeredAbility.onThisOrAnotherSubtypeEntersCreateTokens st kind n)
      | _, _, _ => none
    else none
  | .triggered (.or (.enter .this) (.enter among)) action =>
    match among.shape.anotherSubtypeYouControl with
    | some st =>
      if among.shape.types.eqTypes [.creature] && !among.shape.nontoken &&
          CardAction.leftoverMayDiscardHandDrawDamageIfStory? action then
        some (TriggeredAbility.onThisOrAnotherSubtypeEntersDiscardHand st)
      else none
    | none => none
  | .triggered (.castSpell among) (.tap sel) =>
    if Selector.youCastNoncreatureSpell among &&
        CardAction.leftoverCreatureOrLandTarget? sel then
      some (TriggeredAbility.onCasting Effect.castingTapCreatureOrLand)
    else none
  | .triggered (.castSpell among)
      (.sequence [
        copy,
        .putCounter (.source .this) .plusOnePlusOne 2])
  | .triggered (.triggerId _ (.castSpell among))
      (.sequence [
        copy,
        .putCounter (.source .this) .plusOnePlusOne 2]) =>
    if CardAction.leftoverCopyWithNewTargets? copy &&
        among.shape.types.eqTypes [.instant, .sorcery] &&
        among.shape.sameController &&
        match Selector.leftoverHasTarget? among with
        | some dest => dest.shape.types.eqTypes [.artifact, .land]
        | none => false then
      some (TriggeredAbility.onCasting Effect.castingCopyIfArtifactOrLand)
    else none
  | .triggered (.castSpell among) (.continuous effects _)
  | .triggered (.triggerId _ (.castSpell among)) (.continuous effects _) =>
    match Selector.leftoverHasTarget? among with
    | some dest =>
      if among.shape.sameController && Selector.includesSpell among &&
          dest.shape.mustBePermanent &&
          dest.shape.types.eqTypes [.creature] &&
          CardAction.leftoverGrantFlyingToThose? effects then
        some (TriggeredAbility.onCasting Effect.castingTargetsGainFlying)
      else none
    | none => none
  | .triggered
      (.sequence [
        .spendManaFrom (.subtype .treasure)
          (.triggerId id (.castSpell among)),
        .castSpell (.wasArgumentOfTrigger id' arg)]) action =>
    -- Mana from a Treasure is spent to cast this spell, then that spell is cast.
    if id == id' && arg == 1 && Selector.anySpellYouCast among then
      match CardAction.leftoverDrawLoseLifeSelf? action with
      | some (1, 1) => some TriggeredAbility.onCastWithTreasureDrawLoseLife
      | _ => none
    else none
  | .triggered (.castSpell among)
      (.sequence [
        .continuous effects .endOfTurn,
        .dealDamage src (.opponent who) (.int (.ofNat n))]) =>
    if Selector.youCastNoncreatureSpell among && n != 0 &&
        CardAction.leftoverSourcePump? effects == some (1, 1) &&
        (src == .source .this || src == .this) &&
        CardAction.leftoverYou who then
      some (TriggeredAbility.onCastNoncreaturePumpAndDamageOpponents n)
    else none
  | .triggered (.castSpell among) action =>
    if Selector.youCastNoncreatureSpell among &&
        CardAction.leftoverMayPayHasteUnblockable? action then
      some (TriggeredAbility.onCasting Effect.castingMayPayHasteUnblockable)
    else none
  | .triggered (.discard who) action
  | .triggered (.triggerId _ (.discard who)) action =>
    if CardAction.leftoverYou who &&
        CardAction.leftoverExileGyPlayUntilNextTurn? action then
      some (TriggeredAbility.onResource Effect.resourceDiscardExilePlay)
    else none
  | .triggered (.returnToHand among) action =>
    if among.shape.other && among.shape.sameController &&
        among.shape.nonland && !among.shape.nontoken &&
        match action with
        | .putCounter (.source .this) .plusOnePlusOne 1 => true
        | _ => false then
      some (TriggeredAbility.onWatch Effect.watchJusticeBounce)
    else none
  | .triggered (.upkeep who) (.createTokens controller n parts []) =>
    if who == .controller .this && CardAction.leftoverYou controller then
      match valToNat? n, CardAction.leftoverTokenKind? parts with
      | some n, some k => some (TriggeredAbility.onYourUpkeepCreateTokens k n)
      | _, _ => none
    else none
  | .triggered (.combatStart who)
      (.if (.happened (.ordinal 2 .turnStart (.draw drawer .all)) .turnStart)
        [.continuous
          [.addPower (.target id sel) (.int 3), .gainAbility (.targetReference id') (.keyword .firstStrike)]
          .endOfTurn]) =>
    if who == .controller .this && drawer == .controller .this && id == id' &&
        sel == .intersection [.not .this, .zone .battlefield, .cardType .creature, .controlled (.controller .this)] then
      some TriggeredAbility.onYourBeginCombatIfDrawnTwoPumpFirstStrike
    else none
  | .triggered (.combatDamage (.hostOf .this) .player)
      (.sequence [
        .actionId id (.chooseCreatureType chooser),
        .forEachVariable _ sel [token]]) =>
    if CardAction.leftoverYou chooser &&
        sel == .intersection [
          .zone .battlefield, .cardType .creature, .controlled (.controller .this),
          .hasCreatureTypeChosenByAction id] &&
        CardAction.leftoverCreateTokensKindN? token == some (.treasure, 1) then
      some TriggeredAbility.onEquippedCombatDamageTreasuresPerChosenType
    else none
  | .triggered (.endStep who) (.draw drawer (.int 1)) =>
    if who == .controller .this && drawer == .controller .this then
      some TriggeredAbility.onYourEndStepDraw
    else none
  | .triggered (.precombatMainPhase who) (.addMana gainer syms) =>
    if who == .controller .this && gainer == .controller .this then
      CardAction.addedManaTypes? syms |>.map TriggeredAbility.onYourFirstMainAddMana
    else none
  | .triggered (.target spellOrAbility object) (.draw drawer (.int 1)) =>
    if (object == .this || object == .source .this) &&
        spellOrAbility ==
          .intersection [
            .union [.spell, .ability],
            .controlled (.opponent (.controller .this))] &&
        drawer == .controller .this then
      some TriggeredAbility.onBecomesTargetDraw
    else none
  | _ => none

def toTriggeredAbility? (a : Ability) : Option TriggeredAbility :=
  a.printedTriggeredAbility?.orElse fun _ => a.compileTriggeredAbility?

end Ability

end Mtg.Engine
