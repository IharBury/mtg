import Mtg.Engine.Card.Definition.Guards

/-!
# Catalog definition guards

Regression tests continued from `Guards`. Static abilities, mana
abilities, enters triggers, and catalog spell leftovers.
-/

namespace Mtg.Engine

-- Woodland Weavemaster: another Elf enters +1/+1; tap for any color equal to power.
#guard Selector.shape
  (.intersection [
    .not .this,
    .zone .battlefield,
    .subtype .elf,
    .controlled (.controller .this)]) |>.anotherElfYouControl

#guard
  match
    (Ability.triggered
      (.enter
        (.intersection [
          .not .this,
          .zone .battlefield,
          .subtype .elf,
          .controlled (.controller .this)]))
      (.continuous [.addPower (.source .this) (Value.int 1),
                    .addToughness (.source .this) (Value.int 1)] .endOfTurn)).toTriggeredAbility? with
  | some ab => ab == TriggeredAbility.onAnotherElfYouControlEntersGets1
  | none => false

#guard
  (TraditionalCardDefinition.card [
    .ability (
      .activated
        [.tapSymbol]
        (.sequence [
          .actionId 1
          (.addManaOfOneColor
            (.controller .this)
            ManaSymbol.anyColor
            (.greatestPower .this)),
          .continuous
            [.forbid
              (.spendManaCreatedByAction 1
                (.not
                  (.or
                    (.castSpell (.subtype .elf))
                    (.activateAbility (.subtype .elf)))))]
            .endOfTurn]))
  ]).toCardDef.tapAddAnyColorEqualToPower

#guard
  let action : CardAction :=
    .continuous
      [.addPower
        (.target 1 (.intersection [.zone .battlefield, .cardType .creature])) (Value.int 3),
       .addToughness
        (.targetReference 1) (Value.int 3)]
      .endOfTurn
  action.toEffect == Effect.pump 3 3

#guard
  let action : CardAction :=
    .sequence [
      .draw (.controller .this) 2,
      .loseLife (.controller .this) 2]
  action.toEffect == Effect.drawAndLoseLife 2 2

#guard
  let action : CardAction :=
    .continuous
      [.addPower
        (.intersection [.zone .battlefield, .cardType .creature]) (Value.int (-4)),
       .addToughness
        (.intersection [.zone .battlefield, .cardType .creature]) (Value.int (-4))]
      .endOfTurn
  action.toEffect == Effect.allCreaturesGet (-4) (-4)

#guard
  match
    (Ability.triggered
      (.enter .this)
      (.scry (.controller .this) 2)).toTriggeredAbility? with
  | some ab => ab == TriggeredAbility.onEnterScry 2
  | none => false

#guard
  match
    (Ability.triggered
      (.die .this)
      (.draw (.controller .this) 1)).toTriggeredAbility? with
  | some ab => ab == TriggeredAbility.onDiesDraw 1
  | none => false

#guard
  (TraditionalCardDefinition.card [
    .ability
      (.static
        (.setPower
          .this
          (.count
            (.intersection [
              .zone .battlefield,
              .cardType .land,
              .controlled (.controller .this)])))),
    .ability
      (.static
        (.setToughness
          .this
          (.count
            (.intersection [
              .zone .battlefield,
              .cardType .land,
              .controlled (.controller .this)]))))
  ]).toCardDef.staticAbilities == #[.powerToughnessEqualLandsYouControl]

#guard
  (TraditionalCardDefinition.card [
    .ability
      (.static
        (.setPower
          .this
          (.count
            (.intersection [
              .zone .battlefield,
              .cardType .land,
              .controlled (.controller .this)]))))
  ]).toCardDef.staticAbilities == #[]

#guard
  (TraditionalCardDefinition.card [
    .ability
      (.static
        (.setPower
          .this
          (.count
            (.intersection [
              .zone .battlefield,
              .cardType .creature,
              .controlled (.controller .this)]))))
  ]).toCardDef.staticAbilities == #[.powerEqualCreaturesYouControl]

#guard
  (TraditionalCardDefinition.card [
    .ability (.stackStatic (.forbid (.counter .this)))
  ]).toCardDef.cantBeCountered

#guard
  !(TraditionalCardDefinition.card [
    .ability (.stackStatic (.forbid (.counter (.controller .this))))
  ]).toCardDef.cantBeCountered

#guard
  let action : CardAction :=
    .sequence [
      .continuous
        [.addPower
          (.target 1 (.intersection [.zone .battlefield, .cardType .creature])) (Value.int (-4))]
        .endOfTurn,
      .draw (.controller .this) 1]
  action.toEffect == Effect.pumpThenDraw (-4) 0

#guard
  (TraditionalCardDefinition.card [
    .ability (
      .static
        (.if
          (.any
            (.intersection [
              .zone .battlefield,
              .cardType .creature,
              .attacking .all,
              .isTargetOf .this]))
          [.reduceCost .this [.mana [.generic 2]]]))
  ]).toCardDef.costReductionIfTargetAttacking == 2

#guard
  (TraditionalCardDefinition.card [
    .ability (
      .static
        (.if
          (.anySubtype (.controlled (.controller .this)) .villain)
          [.reduceCost .this [.mana [.generic 1]]]))
  ]).toCardDef.costReductionIfYouControl == some (1, "Villain")

#guard
  let action : CardAction :=
    .continuous [.increaseLandPlayLimit (.controller .this) (Value.int 1)] .endOfTurn
  action.toEffect == Effect.playAdditionalLandThisTurn

#guard
  let s :=
    Selector.shape
      (.intersection [
        .not .this,
        .zone .battlefield,
        .subtype .elf,
        .controlled (.controller .this)])
  s.anotherSubtypeYouControl == some "Elf"

#guard
  (TraditionalCardDefinition.card [
    .ability (
      .static
        (.if
          (.any
            (.intersection [
              .not .this,
              .zone .battlefield,
              .subtype .elf,
              .controlled (.controller .this)]))
          [.increaseLandPlayLimit (.controller .this) (Value.int 1)]))
  ]).toCardDef.extraLandIfOtherSubtype == some "Elf"

#guard
  match
    (Ability.triggered
      (.enter
        (.intersection [
          .zone .battlefield,
          .cardType .land,
          .controlled (.controller .this)]))
      (.sequence [
        .putCounter
          (.target
            1
            (.intersection [
              .zone .battlefield,
              .cardType .creature,
              .controlled (.controller .this)]))
          .plusOnePlusOne
          2,
        .continuous
          [.gainAbility (.targetReference 1) (.keyword .vigilance)]
          .endOfTurn])).toTriggeredAbility? with
  | some ab => ab == TriggeredAbility.onLandYouControlEntersPlusOneVigilance
  | none => false

#guard
  match
    (Ability.triggered
      (.enter .this)
      (.continuous
        [.addPower
          (.target 1 (.intersection [.zone .battlefield, .cardType .creature])) (Value.int 2)]
        .endOfTurn)).toTriggeredAbility? with
  | some ab => ab == TriggeredAbility.onEnterTargetGets 2 0
  | none => false

#guard
  match
    (Ability.triggered
      (.enter .this)
      (.putCounter
        (.target 1 (.intersection [.zone .battlefield, .cardType .creature]))
        .plusOnePlusOne
        1)).toTriggeredAbility? with
  | some ab => ab == TriggeredAbility.onEnterPlusOneOnCreature
  | none => false

#guard
  match
    (Ability.triggered
      (.attack .this .all)
      (.continuous
        [.gainAbility
          (.target
            1
            (.intersection [
              .zone .battlefield,
              .cardType .creature,
              .attacking .all]))
          (.keyword .firstStrike)]
        .endOfTurn)).toTriggeredAbility? with
  | some ab => ab == TriggeredAbility.onAttackTargetGainsKeywords Keyword.firstStrike
  | none => false

#guard
  match
    (Ability.triggered
      (.or (.enter .this) (.attack .this .all))
      (.divideDamage
        (.controller .this)
        .this
        (.targets 1 (.range 1 3) .all)
        3)).toTriggeredAbility? with
  | some ab => ab == TriggeredAbility.onEnterOrAttackDealDividedDamage 3 3
  | none => false

#guard
  match
    (Ability.triggered
      (.die .this)
      (.dealDamage
        .this
        (.target
          1
          (.intersection [
            .zone .battlefield,
            .cardType .creature,
            .controlled (.opponent (.controller .this))]))
        (.greatestPower .this))).toTriggeredAbility? with
  | some ab => ab == TriggeredAbility.onDiesDealDamageEqualToPowerToOppCreature
  | none => false

#guard
  match
    (Ability.triggered
      (.enter .this)
      (.sequence [
        .attach
          .this
          (.target
            1
            (.intersection [
              .zone .battlefield,
              .cardType .creature,
              .controlled (.controller .this)])),
        .untap (.targetReference 1)])).toTriggeredAbility? with
  | some ab => ab == TriggeredAbility.onEnterAttachThen PermanentAction.untap
  | none => false

#guard
  (TraditionalCardDefinition.card [
    .ability (.static (.forbid (.block .token .this)))
  ]).toCardDef.staticAbilities == #[.cantBeBlockedByTokens]

#guard
  let action : CardAction :=
    .sequence [.draw (.controller .this) 1, .discard (.controller .this) 1]
  action.toAbilityEffect == Effect.abilityDrawThenDiscard 1

#guard
  let action : CardAction := .returnToHand .this
  action.toAbilityEffect == Effect.returnFromGraveyardToHand

#guard
  (TraditionalCardDefinition.card [
    .type .enchantment,
    .ability (.static (.addPower (.hostOf .this) (Value.int 3))),
    .ability (.static (.addToughness (.hostOf .this) (Value.int 3)))
  ]).toCardDef.staticAbilities == #[.enchantedCreatureGets 3 3]

#guard
  let action : CardAction := .draw (.controller .this) 2
  action.toAbilityEffect == Effect.abilityDraw 2

#guard
  (TraditionalCardDefinition.card [
    .ability (.activated [.sacrifice .this] (.draw (.controller .this) 2))
  ]).toCardDef.activatedAbilities[0]!.cost.sacrificeSource

#guard Selector.basicLandInLibrary
  (.intersection [.zone .library, .cardType .land, .supertype .basic])

#guard Selector.includesInLibrary (.zone .library)
#guard !Selector.includesInLibrary (.zone .hand)
#guard !Selector.includesInLibrary (.zone .exile)
#guard Selector.zone .hand != .zone .exile
#guard (Selector.shape (.zone .hand)) == {}
#guard (Selector.shape (.zone .exile)) == {}

#guard
  let action : CardAction :=
    .searchLibraryThenShuffle
      (.controller .this)
      [
        .defineSelectorVariable 1
          (.selected
            (.controller .this)
            (.range 1 1)
            (.intersection [
              .zone .library,
              .cardType .land,
              .supertype .basic])),
        .reveal (.variable 1),
        .returnToHand (.variable 1)]
  action.toAbilityEffect == Effect.searchBasicLandToHand

#guard
  let action : CardAction :=
    .searchLibraryThenShuffle
      (.controller .this)
      [
        .putOntoBattlefieldInState
          (.selected
            (.controller .this)
            (.range 1 1)
            (.intersection [.zone .library, .cardType .land, .supertype .basic]))
          [.tapped]]
  action.toAbilityEffect == Effect.searchBasicLandTapped

#guard
  let action : CardAction :=
    .sequence [
      .searchLibraryThenShuffle
        (.controller .this)
        [
          .defineSelectorVariable 1
            (.selected
              (.controller .this)
              (.range 1 1)
              (.intersection [.zone .library, .cardType .land, .supertype .basic])),
          .actionId 1
            (.putOntoBattlefieldInState (.variable 1) [.tapped])],
      .optional (.controller .this)
        (.actionId 2 (.keyword (.controller .this) (.behold .elf))),
      .if (.happened (.actionWithId 2) .gameStart)
        [.untap (.affectedByAction 1)]]
  action.toAbilityEffect == Effect.searchBasicBeholdSubtypeUntap "Elf"

#guard
  match
    (Ability.triggered
      (.enter .this)
      (.searchLibraryThenShuffle
        (.controller .this)
        [
          .putOntoBattlefield
            (.selected
              (.controller .this)
              (.range 1 1)
              (.intersection [.zone .library, .subtype .forest]))])).toTriggeredAbility? with
  | some ab => ab == TriggeredAbility.onEnterSearchForest
  | none => false

#guard
  match
    (Ability.triggered
      (.enter .this)
      (.searchLibraryThenShuffle
        (.controller .this)
        [
          .defineSelectorVariable 1
            (.selected
              (.controller .this)
              (.range 1 1)
              (.intersection [
                .zone .library,
                .cardType .land,
                .supertype .basic])),
          .reveal (.variable 1),
          .returnToHand (.variable 1)])).toTriggeredAbility? with
  | some ab => ab == TriggeredAbility.onEnterSearchBasicToHand
  | none => false

-- Threshold: +P/+T while seven or more cards are in your graveyard.
#guard
  (TraditionalCardDefinition.card [
    .ability (.static (.if
      (.greaterOrEqual
        (.count (.intersection [.zone .graveyard, .owner (.controller .this)]))
        7)
      [.addPower .this (Value.int 1), .addToughness .this (Value.int 1)]))
  ]).toCardDef.staticAbilities == #[.thresholdGets 1 1]

-- Speak Secrets: mill, then one instant or sorcery from among them.
#guard
  (CardAction.sequence [
    .actionId 1 (.mill (.controller .this) 4),
    .returnToHand
      (.selected (.controller .this) (.range 1 1)
        (.intersection [
          .wasObjectOfAction 1,
          .union [.cardType .instant, .cardType .sorcery]]))
  ]).toEffect == Effect.millThenPutInstantOrSorcery 4

-- Gone Fishing: exile two creatures and/or lands, then return them.
#guard
  (CardAction.sequence [
    .actionId 1 (.exile (.targets 1 (.range 2 2)
      (.intersection [
        .zone .battlefield,
        .union [.cardType .creature, .cardType .land],
        .controlled (.controller .this)]))),
    .putOntoBattlefieldInState (.wasCreatedByAction 1)
      [.controlled (.owner (.wasCreatedByAction 1))]
  ]).toEffect == Effect.exileThenReturnYouControl

-- Old Thrush: hold the found land out of the shuffle, then put it on top.
#guard
  match
    (Ability.triggered
      (.enter .this)
      (.sequence [
        .gainLife (.controller .this) 2,
        .optional (.controller .this)
          (.sequence [
            .searchLibraryThenShuffle
              (.controller .this)
              [
                .defineSelectorVariable 1
                  (.selected
                    (.controller .this)
                    (.range 1 1)
                    (.intersection [
                      .zone .library,
                      .cardType .land,
                      .supertype .basic])),
                .reveal (.variable 1),
                .holdOutInLibrary (.variable 1)],
            .putOnTopOfLibrary (.variable 1)])])).toTriggeredAbility? with
  | some ab => ab == TriggeredAbility.onEnterGainLifeSearchBasicOnTop 2
  | none => false

#guard
  (Ability.triggered
    (.enter .this)
    (.sequence [
      .gainLife (.controller .this) 2,
      .optional (.controller .this)
        (.searchLibraryThenShuffle
          (.controller .this)
          [
            .defineSelectorVariable 1
              (.selected
                (.controller .this)
                (.range 1 1)
                (.intersection [
                  .zone .library,
                  .cardType .land,
                  .supertype .basic])),
            .reveal (.variable 1),
            .putOnTopOfLibrary (.variable 1)])])).toTriggeredAbility?.isNone

#guard
  (Ability.triggered
    (.enter .this)
    (.sequence [
      .gainLife (.controller .this) 2,
      .optional (.controller .this)
        (.sequence [
          .searchLibraryThenShuffle
            (.controller .this)
            [
              .defineSelectorVariable 1
                (.selected
                  (.controller .this)
                  (.range 1 1)
                  (.intersection [
                    .zone .library,
                    .cardType .land,
                    .supertype .basic])),
              .reveal (.variable 1)],
          .putOnTopOfLibrary (.variable 1)])])).toTriggeredAbility?.isNone

-- Little Bear: flash; enter, untap another creature you control, +1/+1 if Bear.
#guard Selector.toTargetKind
  (.intersection [
    .not .this,
    .zone .battlefield,
    .cardType .creature,
    .controlled (.controller .this)])
  == .anotherCreatureYouControl

#guard
  match
    (Ability.triggered
      (.enter .this)
      (.sequence [
        .untap
          (.target
            1
            (.intersection [
              .not .this,
              .zone .battlefield,
              .cardType .creature,
              .controlled (.controller .this)])),
        .if
          (.anySubtype (.targetReference 1) .bear)
          [.putCounter (.targetReference 1) .plusOnePlusOne 1]])).toTriggeredAbility? with
  | some ab => ab == TriggeredAbility.onEnterUntapOtherPlusOneIfSubtype "Bear"
  | none => false

-- Wakandan Royal Guard: extra counters only if the target is another Hero,
-- not when the source targets itself.
#guard
  match
    (Ability.triggered
      (.enter .this)
      (.sequence [
        .putCounter
          (.target 1 (.intersection [.zone .battlefield, .cardType .creature]))
          .plusOnePlusOne
          1,
        .if
          (.anySubtype (.intersection [.targetReference 1, .not .this]) .hero)
          [.putCounter (.targetReference 1) .plusOnePlusOne 1]])).toTriggeredAbility? with
  | some ab => ab == TriggeredAbility.onEnterPlusOneOrTwoIfAnotherHero
  | none => false

#guard
  match
    (Ability.triggered
      (.enter .this)
      (.sequence [
        .putCounter
          (.target 1 (.intersection [.zone .battlefield, .cardType .creature]))
          .plusOnePlusOne
          1,
        .if
          (.anySubtype (.intersection [.not .this, .targetReference 1]) .hero)
          [.putCounter (.targetReference 1) .plusOnePlusOne 1]])).toTriggeredAbility? with
  | some ab => ab == TriggeredAbility.onEnterPlusOneOrTwoIfAnotherHero
  | none => false

#guard
  (Ability.triggered
    (.enter .this)
    (.sequence [
      .putCounter
        (.target 1 (.intersection [.zone .battlefield, .cardType .creature]))
        .plusOnePlusOne
        1,
      .if
        (.anySubtype (.targetReference 1) .hero)
        [.putCounter (.targetReference 1) .plusOnePlusOne 1]])).toTriggeredAbility?.isNone

#guard
  (Ability.triggered
    (.enter .this)
    (.sequence [
      .putCounter
        (.target 1 (.intersection [.zone .battlefield, .cardType .creature]))
        .plusOnePlusOne
        1,
      .if
        (.anySubtype (.not .this) .hero)
        [.putCounter (.targetReference 1) .plusOnePlusOne 1]])).toTriggeredAbility?.isNone

-- Dual land: enters tapped; tap-add one of two colors; counters on a typed creature.
#guard
  (TraditionalCardDefinition.card [
    .ability (
      .static
        (.replace
          (.enter .this)
          [.putOntoBattlefieldInState .this [.tapped]]))
  ]).toCardDef.entersTapped

#guard
  (TraditionalCardDefinition.card [
    .ability (
      .activated
        [.tapSymbol]
        (.playerSelectAction
          (.controller .this)
          (.range 1 1)
          [
            .addMana (.controller .this) [.mono .green],
            .addMana (.controller .this) [.mono .blue]]))
  ]).toCardDef.tapAddOneOf == #[.colored .green, .colored .blue]

#guard
  let action : CardAction :=
    .addMana (.controller .this) [.mono .black, .mono .red]
  action.toAbilityEffect == Effect.addMana #[.colored .black, .colored .red]

#guard Selector.includedSubtypes
  (.union [.subtype .goblin, .subtype .orc]) == ["Goblin", "Orc"]

#guard
  let action : CardAction :=
    .putCounter
      (.target
        1
        (.intersection [
          .zone .battlefield,
          .cardType .creature,
          .subtype .elf,
          .controlled (.controller .this)]))
      .plusOnePlusOne
      2
  action.toAbilityEffect == Effect.plusOneOnTarget 2 #["Elf"]

#guard
  let action : CardAction :=
    .putCounter
      (.target
        1
        (.intersection [
          .zone .battlefield,
          .cardType .creature,
          .union [.subtype .goblin, .subtype .orc],
          .controlled (.controller .this)]))
      .plusOnePlusOne
      2
  action.toAbilityEffect == Effect.plusOneOnTarget 2 #["Goblin", "Orc"]

#guard
  match
    (Ability.activatedIf
      (.timeToCastSorcery (.controller .this))
      [
        .mana [.generic 2, .mono .green, .mono .blue],
        .tapSymbol,
        .sacrifice .this]
      (.putCounter
        (.target
          1
          (.intersection [
            .zone .battlefield,
            .cardType .creature,
            .subtype .elf,
            .controlled (.controller .this)]))
        .plusOnePlusOne
        2)).toActivatedAbility? with
  | some ab =>
    ab.onlyAsSorcery &&
      ab.cost.tap &&
      ab.cost.sacrificeSource &&
      ab.cost.mana == ManaCost.ofGenericAndColors 2 [.green, .blue] &&
      ab.effect == Effect.plusOneOnTarget 2 #["Elf"]
  | none => false

#guard
  match
    (Ability.activated
      [.mana [.generic 4], .discard .this]
      (.searchLibraryThenShuffle
        (.controller .this)
        [
          .defineSelectorVariable 1
            (.selected
              (.controller .this)
              (.range 1 1)
              (.intersection [.zone .library, .subtype .halfling])),
          .reveal (.variable 1),
          .returnToHand (.variable 1)])).toActivatedAbility? with
  | some ab =>
    ab.cost.discardSource &&
      ab.activateFromHand &&
      ab.cost.mana == ManaCost.ofGeneric 4 &&
      ab.effect == Effect.searchLandTypeToHand "Halfling"
  | none => false

#guard
  (TraditionalCardDefinition.card [
    .ability (.activated [.tapSymbol] (.addMana (.controller .this) [.mono .green]))
  ]).toCardDef.tapAddMana == #[.colored .green]

#guard
  let action : CardAction := .dealDamage .this (.target 1 .all) (.int 3)
  action.toEffect == Effect.dealDamage 3

#guard
  Selector.toTargetKind
    (.union [.cardType .artifact, .cardType .enchantment])
  == .artifactOrEnchantment

#guard
  let action : CardAction :=
    .destroy
      (.target 1 (.union [.cardType .artifact, .cardType .enchantment]))
  action.toAbilityEffect == Effect.destroyTargetArtifactOrEnchantment

#guard
  let action : CardAction := .destroy (.target 1 (.zone .battlefield))
  action.toAbilityEffect == Effect.destroyTargetPermanent

#guard
  let action : CardAction :=
    .addManaOfOneColor
      (.controller .this)
      ManaSymbol.anyColor
      1
  action.toAbilityEffect == Effect.addAnyColor

#guard
  match
    (Ability.triggered
      (.enter .this)
      (.sequence [
        .actionId 1 (.exile (.topOfLibrary (.controller .this) 1)),
        .continuous
          [.canPlay (.controller .this) (.wasCreatedByAction 1)]
          (.sequence [.turnStart, .endOfPlayerTurn (.controller .this)])])).toTriggeredAbility? with
  | some ab => ab == TriggeredAbility.onEnterExileTop
  | none => false

#guard
  match
    (Ability.triggered
      (.enter
        (.intersection [
          .zone .battlefield,
          .cardType .artifact,
          .controlled (.controller .this)]))
      (.draw (.controller .this) 1)).toTriggeredAbility? with
  | some ab => ab == TriggeredAbility.onArtifactYouControlEntersDraw
  | none => false

#guard
  match
    (Ability.triggered
      (.enter
        (.intersection [
          .not .this,
          .zone .battlefield,
          .cardType .artifact,
          .controlled (.controller .this)]))
      (.putCounter (.source .this) .plusOnePlusOne 1)).toTriggeredAbility? with
  | some ab => ab == TriggeredAbility.onAnotherArtifactEntersPlusOne
  | none => false

#guard
  match
    (Ability.triggeredWhile
      (.attack .this .all)
      (.any
        (.intersection [
          .zone .battlefield,
          .cardType .creature,
          .controlled (.controller .this),
          .powerAtLeast (Value.int 4)]))
      (.continuous [.addPower (.source .this) (Value.int 2),
                    .addToughness (.source .this) (Value.int 2)] .endOfTurn)).toTriggeredAbility? with
  | some ab => ab == TriggeredAbility.onAttackFerociousSourceGets 2 2
  | none => false

#guard
  match
    (Ability.triggered
      (.combatStart (.controller .this))
      (.if
        (.any
          (.intersection [
            .zone .battlefield,
            .cardType .creature,
            .controlled (.controller .this),
            .powerAtLeast (Value.int 4)]))
        [.putCounter (.source .this) .plusOnePlusOne 1])).toTriggeredAbility? with
  | some ab => ab == TriggeredAbility.onYourBeginCombatFerociousPlusOne
  | none => false

#guard
  (Ability.triggered
    (.combatStart (.opponent (.controller .this)))
    (.if
      (.any
        (.intersection [
          .zone .battlefield,
          .cardType .creature,
          .controlled (.controller .this),
          .powerAtLeast (Value.int 4)]))
      [.putCounter (.source .this) .plusOnePlusOne 1])).toTriggeredAbility?.isNone

#guard
  (Ability.triggered
    (.combatStart (.controller .this))
    (.putCounter (.source .this) .plusOnePlusOne 1)).toTriggeredAbility?.isNone

#guard
  match
    (Ability.triggered
      (.attack .this .all)
      (.continuous
        [
          .addPower
            (.target
              1
              (.intersection [
                .not .this,
                .zone .battlefield,
                .cardType .creature,
                .controlled (.controller .this)])) (Value.int 2),
          .gainAbility (.targetReference 1) (.keyword .trample)]
        .endOfTurn)).toTriggeredAbility? with
  | some ab => ab == TriggeredAbility.onAttackOtherGets2AndTrample
  | none => false

#guard
  match
    (Ability.triggered
      (.enter .this)
      (.continuous
        [
          .addPower
            (.intersection [
              .zone .battlefield,
              .cardType .creature,
              .controlled (.controller .this)]) (Value.int 1),
          .gainAbility
            (.intersection [
              .zone .battlefield,
              .cardType .creature,
              .controlled (.controller .this)])
            (.keyword .firstStrike)]
        .endOfTurn)).toTriggeredAbility? with
  | some ab => ab == TriggeredAbility.onEnterCreaturesYouControlGetAndFirstStrike 1
  | none => false

#guard
  match
    (Ability.triggered
      (.enter .this)
      (.forEachVariable 1 .player [
        .sacrifice
          (.selected
            (.variable 1)
            (.range 1 1)
            (.intersection [
              .zone .battlefield,
              .cardType .creature,
              .controlled (.variable 1)]))])).toTriggeredAbility? with
  | some ab => ab == TriggeredAbility.onEnterEachPlayerSacrificesCreature
  | none => false

-- Sacrifice an artifact is `selected` 1, not every artifact you control.
#guard
  CardAction.leftoverMaySacArtifactOrDiscardDraw?
    (.sequence [
      .optional (.controller .this)
        (.actionId 1
          (.playerSelectAction
            (.controller .this)
            (.range 1 1)
            [
              .sacrifice
                (.selected
                  (.controller .this)
                  (.range 1 1)
                  (.intersection [
                    .zone .battlefield,
                    .cardType .artifact,
                    .controlled (.controller .this)])),
              .discard (.controller .this) 1])),
      .if (.happened (.actionWithId 1) .gameStart) [.draw (.controller .this) 1]]) == some 1

#guard
  CardAction.leftoverMaySacArtifactOrDiscardDraw?
    (.sequence [
      .optional (.controller .this)
        (.actionId 1
          (.playerSelectAction
            (.controller .this)
            (.range 1 1)
            [
              .sacrifice
                (.intersection [
                  .zone .battlefield,
                  .cardType .artifact,
                  .controlled (.controller .this)]),
              .discard (.controller .this) 1])),
      .if (.happened (.actionWithId 1) .gameStart) [.draw (.controller .this) 1]]) |>.isNone

#guard
  match
    (Ability.triggered
      (.block .all .this)
      (.dealDamage .this (.blocking .this) (.int 1))).toTriggeredAbility? with
  | some ab => ab == TriggeredAbility.onBecomesBlockedDeal1ToBlockers
  | none => false

#guard
  match
    (Ability.triggered
      (.castSpell
        (.intersection [
          .union [.cardType .instant, .cardType .sorcery],
          .controlled (.controller .this)]))
      (.dealDamage .this (.opponent (.controller .this)) (.int 2))).toTriggeredAbility? with
  | some ab => ab == TriggeredAbility.onCastInstantOrSorceryDealDamageToEachOpponent 2
  | none => false

#guard
  (Ability.triggered
    (.castSpell (.union [.cardType .instant, .cardType .sorcery]))
    (.dealDamage .this (.opponent (.controller .this)) (.int 2))).toTriggeredAbility?.isNone

#guard
  match
    (Ability.triggered
      (.enter .this)
      (.attach
        .this
        (.target
          1
          (.intersection [
            .zone .battlefield,
            .cardType .creature,
            .controlled (.controller .this),
            .supertype .legendary])))).toTriggeredAbility? with
  | some ab => ab == TriggeredAbility.onEnterAttachToLegendary
  | none => false

#guard
  (TraditionalCardDefinition.card [
    .type .artifact,
    .ability (.static (.gainAbility (.hostOf .this) (.keyword .indestructible)))
  ]).toCardDef.staticAbilities == #[.equippedCreatureHasKeywords Keyword.indestructible]

#guard
  (TraditionalCardDefinition.card [
    .type .enchantment,
    .ability (.static (.addPower (.hostOf .this) (Value.int 1))),
    .ability (.static (.gainAbility (.hostOf .this) (.keyword .haste)))
  ]).toCardDef.staticAbilities ==
    #[.enchantedCreatureGetsAndHas 1 0 Keyword.haste]

#guard
  match
    (Ability.keywordWithCost (.typecycling [] [] [.mountain]) [.mana [.generic 1]]).toActivatedAbility? with
  | some ab =>
    ab.activateFromHand &&
      ab.cost.discardSource &&
      ab.effect == Effect.searchLandTypeToHand "Mountain"
  | none => false

#guard Selector.toTargetKind
  (.intersection [
    .zone .battlefield,
    .union [.cardType .artifact, .cardType .land]])
  == .artifactOrLand

#guard Selector.toTargetKind
  (.intersection [
    .zone .battlefield,
    .cardType .creature,
    .powerAtLeast (Value.int 4)])
  == .creaturePowerAtLeast 4

#guard
  let action : CardAction :=
    .sequence [
      .tap
        (.target 1 (.intersection [.zone .battlefield, .cardType .creature])),
      .scry (.controller .this) 1,
      .draw (.controller .this) 1]
  action.toEffect == Effect.tapScryDraw 1 1

#guard
  let action : CardAction :=
    .sequence [
      .returnToHand (.target 1 .spell),
      .draw (.controller .this) 1]
  action.toEffect == Effect.returnSpellDraw

#guard
  let action : CardAction :=
    .sequence [
      .destroy
        (.target
          1
          (.intersection [
            .zone .battlefield,
            .union [.cardType .artifact, .cardType .enchantment]])),
      .gainLife (.controller .this) 2]
  action.toEffect == Effect.destroyArtifactOrEnchantmentGainLife 2

#guard
  let action : CardAction :=
    .sequence [
      .destroy
        (.target
          1
          (.intersection [
            .zone .battlefield,
            .union [.cardType .artifact, .cardType .land]])),
      .continuous
        [.forbid (.block (.not (.keyword .flying)) .all)]
        .endOfTurn]
  action.toEffect == Effect.destroyArtifactOrLandNonflyersCantBlock

#guard
  let action : CardAction :=
    .destroy
      (.target
        1
        (.intersection [
          .zone .battlefield,
          .cardType .creature,
          .powerAtLeast (Value.int 4)]))
  action.toEffect == Effect.destroyCreaturePowerAtLeast 4

#guard
  let action : CardAction :=
    .continuous
      [
        .gainType
          (.target 1 (.intersection [.zone .battlefield, .cardType .creature]))
          .artifact,
        .gainAbility (.targetReference 1) (.keyword .indestructible)]
      .endOfTurn
  action.toEffect == Effect.becomeArtifactGainIndestructible

#guard
  let action : CardAction :=
    .sequence [
      .putCounter
        (.target 1 (.intersection [.zone .battlefield, .cardType .creature]))
        .plusOnePlusOne
        1,
      .continuous
        [
          .gainAbility (.targetReference 1) (.keyword .lifelink),
          .gainAbility (.targetReference 1) (.keyword .indestructible)]
        .endOfTurn]
  action.toEffect == Effect.plusOneLifelinkIndestructible

#guard
  let action : CardAction :=
    .continuous
      [
        .addPower
          (.target
            1
            (.intersection [
              .not .this,
              .zone .battlefield,
              .cardType .creature,
              .controlled (.controller .this)])) (Value.int 2),
        .gainAbility (.targetReference 1) (.keyword .hexproof)]
      .endOfTurn
  action.toAbilityEffect == Effect.anotherYouControlGetsAndGrant 2 0 Keyword.hexproof

#guard
  match
    (Ability.triggered
      (.attackSimultaneously
        (.intersection [
          .zone .battlefield,
          .cardType .creature,
          .controlled (.controller .this)])
        .all
        [])
      (.draw (.controller .this) 1)).toTriggeredAbility? with
  | some ab => ab == TriggeredAbility.onYouAttackDraw
  | none => false

#guard
  match
    (Ability.triggered
      (.attackSimultaneously
        (.intersection [
          .zone .battlefield,
          .cardType .creature,
          .subtype .merfolk,
          .controlled (.controller .this)])
        .player
        [])
      (.draw (.controller .this) 1)).toTriggeredAbility? with
  | some ab => ab == TriggeredAbility.onWatch Effect.watchMerfolkAttackDraw
  | none => false

#guard
  (Ability.triggered
    (.attackSimultaneously
      (.intersection [
        .zone .battlefield,
        .cardType .creature,
        .subtype .merfolk,
        .controlled (.controller .this)])
      .all
      [])
    (.draw (.controller .this) 1)).toTriggeredAbility?.isNone

#guard
  (Ability.triggered
    (.attackSimultaneously
      (.intersection [
        .zone .battlefield,
        .cardType .creature,
        .controlled (.controller .this)])
      .player
      [])
    (.draw (.controller .this) 1)).toTriggeredAbility?.isNone

#guard
  match
    (Ability.triggered
      (.attackSimultaneously
        (.intersection [
          .zone .battlefield,
          .cardType .creature,
          .controlled (.controller .this)])
        .player
        [.countAtLeast 2])
      (.continuous
        [
          .gainAbility
            (.target
              1
              (.intersection [
                .zone .battlefield,
                .cardType .creature,
                .attacking .all,
                .not (.keyword .flying)]))
            (.keyword .flying)]
        .endOfTurn)).toTriggeredAbility? with
  | some ab => ab == TriggeredAbility.onAttackWithTwoOrMoreGrantFlying
  | none => false

#guard
  (Ability.triggered
    (.attackSimultaneously
      (.intersection [
        .zone .battlefield,
        .cardType .creature,
        .controlled (.controller .this)])
      .player
      [])
    (.continuous
      [
        .gainAbility
          (.target
            1
            (.intersection [
              .zone .battlefield,
              .cardType .creature,
              .attacking .all,
              .not (.keyword .flying)]))
          (.keyword .flying)]
      .endOfTurn)).toTriggeredAbility?.isNone

#guard
  match
    (Ability.triggered
      (.enter .this)
      (.continuous
        [.gainAbility (.hostOf .this) (.keyword .firstStrike)]
        .endOfTurn)).toTriggeredAbility? with
  | some ab => ab == TriggeredAbility.onEnterEnchanted (.grantKeywords Keyword.firstStrike)
  | none => false

#guard
  match
    (Ability.triggered
      (.enter .this)
      (.sequence [
        .attach
          .this
          (.target
            1
            (.intersection [
              .zone .battlefield,
              .cardType .creature,
              .controlled (.controller .this)])),
        .continuous
          [.gainAbility (.hostOf .this) (.keyword .indestructible)]
          .endOfTurn])).toTriggeredAbility? with
  | some ab =>
    ab == TriggeredAbility.onEnterAttachThen (.grantKeywords Keyword.indestructible)
  | none => false

#guard
  (TraditionalCardDefinition.card [
    .ability (.static (.addPower
          (.intersection [
            .not .this,
            .zone .battlefield,
            .cardType .creature,
            .controlled (.controller .this)]) (Value.int 1))),
    .ability (.static (.addToughness
          (.intersection [
            .not .this,
            .zone .battlefield,
            .cardType .creature,
            .controlled (.controller .this)]) (Value.int 1)))
  ]).toCardDef.staticAbilities == #[.otherCreaturesGet #[] 1 1]

#guard
  let card :=
    (TraditionalCardDefinition.card [
      .ability (.everywhereStatic (
        .canBeCastAsThoughWithFlashIf
          .this
          (.any (.intersection [
            .zone .battlefield, .subtype .human, .controlled .caster]))))
    ]).toCardDef
  card.flashIfYouControlSubtype == some "Human" && !card.keywords.flash

#guard
  match
    (Ability.activatedIf
      (.timeToCastSorcery (.controller .this))
      [.mana [.generic 1]]
      (.attach
        .this
        (.target
          1
          (.intersection [
            .zone .battlefield,
            .cardType .creature,
            .controlled (.controller .this),
            .subtype .human])))).toActivatedAbility? with
  | some ab =>
    ab.onlyAsSorcery &&
      ab.equipSubtype == some "Human" &&
      ab.effect == Effect.attachToTargetCreatureYouControl
  | none => false

#guard
  match
    (Ability.activated
      [.mana [.generic 2], .discard .this]
      (.searchLibraryThenShuffle
        (.controller .this)
        [
          .defineSelectorVariable 1
            (.selected
              (.controller .this)
              (.range 1 1)
              (.intersection [
                .zone .library,
                .cardType .land,
                .supertype .basic])),
          .reveal (.variable 1),
          .returnToHand (.variable 1)])).toActivatedAbility? with
  | some ab =>
    ab.activateFromHand &&
      ab.cost.discardSource &&
      ab.effect == Effect.searchLandTypeToHand "Basic land"
  | none => false

#guard
  match
    (Ability.triggeredWhile
      (.attack .this .all)
      (.any
        (.intersection [
          .zone .battlefield,
          .cardType .creature,
          .controlled (.controller .this),
          .powerAtLeast (Value.int 4)]))
      (.continuous
        [
          .addPower (.source .this) (Value.int 1),
          .gainAbility
            (.intersection [
              .zone .battlefield,
              .cardType .creature,
              .controlled (.controller .this)])
            (.keyword .trample)]
        .endOfTurn)).toTriggeredAbility? with
  | some ab => ab == TriggeredAbility.onAttackFerociousSourceGetsAndTeamTrample 1
  | none => false

#guard
  CardAction.leftoverGrantVigilanceUnblockable?
    (.sequence [
      .continuous
        [
          .gainAbility
            (.target 1 (.intersection [.zone .battlefield, .cardType .creature]))
            (.keyword .vigilance),
          .forbid
            (.block
              .any
              (.targetReference 1))]
        .endOfTurn,
      .draw (.controller .this) 1]) == true

#guard
  CardAction.leftoverPumpThenExileTopPlay?
    (.sequence [
      .continuous
        [
          .addPower
            (.target 1 (.intersection [.zone .battlefield, .cardType .creature])) (Value.int 3),
          .addToughness
            (.targetReference 1) (Value.int 1)]
        .endOfTurn,
      .actionId 1 (.exile (.topOfLibrary (.controller .this) 1)),
      .continuous
        [.canPlay (.controller .this) (.wasCreatedByAction 1)]
        (.sequence [.turnStart, .endOfPlayerTurn (.controller .this)])]) == some (3, 1)

end Mtg.Engine
