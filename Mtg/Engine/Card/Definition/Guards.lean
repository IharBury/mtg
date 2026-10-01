import Mtg.Engine.Card.Definition.CardFace

/-!
# Traditional definition guards

Regression tests for compiling `CardPart`s, in the order they were added.
`GuardsCatalog`, `GuardsTrigger`, and `GuardsSaga` continue this file.
Add a new guard at the end of `GuardsSaga`.
-/

namespace Mtg.Engine

-- Concerted Care: target artifact or creature you control gains hexproof
-- and indestructible until end of turn.
#guard
  let action : CardAction :=
    .continuous
      [
        .gainAbility
          (.target
            1
            (.intersection [
              .zone .battlefield,
              .union [.cardType .artifact, .cardType .creature],
              .controlled (.controller .this)]))
          (.keyword .hexproof),
        .gainAbility (.targetReference 1) (.keyword .indestructible)]
      .endOfTurn
  action.toEffect == Effect.grantHexproofIndestructible

#guard Selector.toTargetKind
  (.intersection [
    .zone .battlefield,
    .union [.cardType .artifact, .cardType .creature],
    .controlled (.controller .this)])
  == .artifactOrCreatureYouControl

#guard Selector.toTargetKind
  (.intersection [
    .controlled (.controller .this),
    .union [.cardType .creature, .cardType .artifact],
    .zone .battlefield])
  == .artifactOrCreatureYouControl

-- Dwarven Provisioner: {3}{W}: creatures you control get +1/+1 until end of turn.
#guard
  let action : CardAction :=
    .continuous
      [.addPower
        (.intersection [
          .zone .battlefield,
          .cardType .creature,
          .controlled (.controller .this)])
        (Value.int 1),
       .addToughness
        (.intersection [
          .zone .battlefield,
          .cardType .creature,
          .controlled (.controller .this)])
        (Value.int 1)]
      .endOfTurn
  action.toAbilityEffect == Effect.abilityCreaturesYouControlGet 1 1

#guard
  match
    (Ability.activated
      [.mana [.generic 3, .mono .white]]
      (.continuous
        [.addPower
          (.intersection [
            .zone .battlefield,
            .cardType .creature,
            .controlled (.controller .this)]) (Value.int 1),
         .addToughness
          (.intersection [
            .zone .battlefield,
            .cardType .creature,
            .controlled (.controller .this)]) (Value.int 1)]
        .endOfTurn)).toActivatedAbility? with
  | some ab =>
    ab.cost.mana == ManaCost.ofGenericAndColor 3 .white &&
      ab.effect == Effect.abilityCreaturesYouControlGet 1 1
  | none => false

-- Gaze in Wonder: tap one or two target creatures.
#guard
  let action : CardAction :=
    .tap (.targets 1 (.range 1 2) (.intersection [.zone .battlefield, .cardType .creature]))
  action.toEffect == Effect.tapOneOrTwoCreatures

-- Magnificent End: 5 damage to target creature; {3} less if that target is tapped.
#guard
  let action : CardAction :=
    .dealDamage
      .this
      (.target 1 (.intersection [.zone .battlefield, .cardType .creature]))
      (.int 5)
  action.toEffect == Effect.dealDamageToCreature 5

#guard Selector.shape
  (.intersection [.zone .battlefield, .cardType .creature, .tapped]) |>.tappedCreature

#guard
  (TraditionalCardDefinition.card [
    .name "Magnificent End",
    .manaCost [.generic 4, .mono .white],
    .type .instant,
    .ability (
      .stackStatic
        (.if
          (.any
            (.intersection [
              .zone .battlefield,
              .cardType .creature,
              .tapped,
              .isTargetOf .this]))
          [.reduceCost .this [.mana [.generic 3]]])),
    .actions [
      .dealDamage
        .this
        (.target 1 (.intersection [.zone .battlefield, .cardType .creature]))
        (.int 5)]
  ]).toCardDef.costReductionIfTargetTapped == 3

-- Eagle of the Great Shelf: whenever this attacks, +1/+1 for each other creature.
#guard
  let others : Selector :=
    .intersection [
      .not .this,
      .zone .battlefield,
      .cardType .creature,
      .controlled (.controller .this)]
  match
    (Ability.triggered
      (.attack .this .all)
      (.continuous
        [.addPower (.source .this) (Value.count others),
         .addToughness (.source .this) (Value.count others)]
        .endOfTurn)).toTriggeredAbility? with
  | some ab => ab == TriggeredAbility.onAttackPumpForEachOtherCreature
  | none => false

-- A flat +1/+1 is not +1/+1 for each other creature.
#guard
  (Ability.triggered
    (.attack .this .all)
    (.continuous [.addPower (.source .this) (Value.int 1),
                  .addToughness (.source .this) (Value.int 1)] .endOfTurn)).toTriggeredAbility?.isNone

-- Vow to Erebor: untap target creature you control, +2/+2, maybe attach if Dwarf.
#guard Selector.toTargetKind
  (.intersection [
    .zone .battlefield,
    .cardType .creature,
    .controlled (.controller .this)])
  == .creatureYouControl

#guard Selector.shape (.subtype .dwarf) |>.dwarf

#guard
  let action : CardAction :=
    .sequence [
      .untap
        (.target
          1
          (.intersection [
            .zone .battlefield,
            .cardType .creature,
            .controlled (.controller .this)])),
      .continuous [.addPower (.targetReference 1) (Value.int 2),
                   .addToughness (.targetReference 1) (Value.int 2)] .endOfTurn,
      .if
        (.anySubtype (.targetReference 1) .dwarf)
        [
          .optional (.controller .this)
            (.attach
              (.selected
                (.controller .this)
                (.range 1 1)
                (.intersection [
                  .zone .battlefield,
                  .subtype .equipment,
                  .controlled (.controller .this)]))
              (.targetReference 1))
        ]]
  action.toEffect == Effect.untapPumpMaybeAttach 2 2

-- Bilbo Baggins, Burglar: enters, draw a card; Adventure scry 2.
#guard
  match
    (Ability.triggered
      (.enter .this)
      (.draw (.controller .this) 1)).toTriggeredAbility? with
  | some ab => ab == TriggeredAbility.onEnterDraw 1
  | none => false

#guard CardAction.toEffect (.scry (.controller .this) 2) == Effect.scry 2

#guard valToNat? (3 : Value) == some 3
#guard (valToNat? Value.x).isNone
#guard (valToNat? (Value.greatestPower .this)).isNone
#guard (valToNat? (Value.greatestToughness .this)).isNone
#guard (valToNat? (Value.count .this)).isNone
#guard (valToNat? (Value.product (Value.count .this) (Value.int 2))).isNone
#guard (valToNat? (Value.variable 1)).isNone
#guard (valToNat? (Value.greatestManaSpent .this)).isNone
#guard Range.range Value.x 1 != Range.range 0 1
#guard Range.any != Range.range 0 0
#guard Range.from Value.x != Range.from 1
#guard Range.from 1 != Range.range 1 1
#guard
  let drawX : CardAction := .draw (.controller .this) .x
  let millPower : CardAction :=
    .mill (.controller .this)
      (.greatestPower
        (.intersection [
          .zone .battlefield,
          .cardType .creature,
          .controlled (.controller .this)]))
  let tokens : CardAction :=
    .createTokens (.controller .this) 1 PredefinedToken.treasureToken [.tapped]
  drawX != .draw (.controller .this) 1 &&
    millPower != .mill (.controller .this) 1 &&
    tokens ==
      .createTokens (.controller .this) 1 PredefinedToken.treasureToken [.tapped]

-- Lakeshore Apothecary: draw your second card, +1/+1 counter.
#guard
  match
    (Ability.triggered
      (.ordinal 2 .turnStart (.draw (.controller .this) .all))
      (.putCounter (.source .this) .plusOnePlusOne 1)).toTriggeredAbility? with
  | some ab => ab == TriggeredAbility.onDrawSecondPlusOne
  | none => false

-- Confusticate and Bebother: choose counter-unless or loot.
#guard
  let action : CardAction :=
    .chooseUniqueModes (.range 1 1) [
      .preventable (.controller (.targetReference 1)) [.mana [.generic 4]]
        (.counter (.target 1 .spell)),
      .sequence [
        .draw (.controller .this) 2,
        .discard (.controller .this) 1]]
  CardAction.leftoverModes? action ==
    some #[Effect.counterUnlessPays 4, Effect.drawThenDiscard 2]

-- Thirst for Knowledge: discard two unless you discard an artifact card.
#guard
  CardAction.leftoverDrawThreeDiscardUnlessArtifact?
    (.sequence [
      .draw (.controller .this) 3,
      .preventable
        (.controller .this)
        [.discard (.cardType .artifact)]
        (.discard (.controller .this) 2)]) == some true

#guard
  CardAction.leftoverDrawThreeDiscardUnlessArtifact?
    (.sequence [
      .draw (.controller .this) 3,
      .playerSelectAction
        (.controller .this)
        (.range 1 1)
        [
          .discard (.intersection [.cardType .artifact]) 1,
          .discard (.controller .this) 2]]) |>.isNone

#guard
  CardAction.leftoverDrawThreeDiscardUnlessArtifact?
    (.sequence [
      .draw (.controller .this) 3,
      .preventable
        (.controller .this)
        [.discard .this]
        (.discard (.controller .this) 2)]) |>.isNone

-- Ravenhill Flock: whenever you draw, +1/+1 counter.
#guard
  match
    (Ability.triggered
      (.draw (.controller .this) .all)
      (.putCounter (.source .this) .plusOnePlusOne 1)).toTriggeredAbility? with
  | some ab => ab == TriggeredAbility.onDrawPlusOne
  | none => false

-- Thranduil's Decree: counter; exile a permanent spell and maybe cast it.
#guard
  (TraditionalCardDefinition.card [
    .actions [
      .actionId 1 (.counter (.target 1 .spell)),
      .continuous
        [.replace
          (.putToGraveyard (.intersection [.wasObjectOfAction 1, .permanentSpell]))
          [.actionId 2 (.exile (.replacingObject)),
            .continuous
              [.canCastWithoutPayingManaCost (.controller .this) (.wasCreatedByAction 2)]
              .endOfGame]]
        .endOfGame]
  ]).toCardDef.spellEffect == some Effect.counterExilePermanentMayCast

-- Bilbo, Luckwearer: combat damage loot; Adventure exchanges control.
#guard
  match
    (Ability.triggered
      (.combatDamage .this .player)
      (.sequence [
        .draw (.controller .this) 1,
        .discard (.controller .this) 1])).toTriggeredAbility? with
  | some ab => ab == TriggeredAbility.onCombatDamageToPlayerLoot
  | none => false

#guard
  (TraditionalCardDefinition.card [
    .ability (.static (.forbid (.block .any .this)))
  ]).toCardDef.keywords.cantBeBlocked

#guard
  let action : CardAction :=
    .exchangeControl
      (.targetSet
        1
        (.range 2 2)
        (.intersection [.zone .battlefield, .not .land])
        [.shareCardType])
  action.toEffect == Effect.exchangeControlSharingType

#guard Selector.toTargetKind
  (.targetSet
    1
    (.range 2 2)
    (.intersection [.zone .battlefield, .not .land])
    [.shareCardType])
  == .twoNonlandsSharingType

-- Uneasy Partings: {1} less if the target is an attacking nontoken creature;
-- owner puts it on top or bottom.
#guard Selector.shape
  (.intersection [
    .zone .battlefield,
    .cardType .creature,
    .attacking .all,
    .not .token]) |>.attackingNontokenCreature

#guard
  (TraditionalCardDefinition.card [
    .ability (
      .stackStatic
        (.if
          (.any
            (.intersection [
              .zone .battlefield,
              .cardType .creature,
              .attacking .all,
              .not .token,
              .isTargetOf .this]))
          [.reduceCost .this [.mana [.generic 1]]])),
    .actions [
      .playerSelectAction (.owner (.targetReference 1)) (.range 1 1)
        [.putOnTopOfLibrary
          (.target 1 (.intersection [.zone .battlefield, .cardType .creature])),
          .putOnBottomOfLibrary (.targetReference 1)]]
  ]).toCardDef.costReductionIfTargetAttackingNontoken == 1

#guard
  let action : CardAction :=
    .playerSelectAction (.owner (.targetReference 1)) (.range 1 1)
      [.putOnTopOfLibrary
        (.target 1 (.intersection [.zone .battlefield, .cardType .creature])),
        .putOnBottomOfLibrary (.targetReference 1)]
  action.toEffect == Effect.putOnTopOrBottom

-- Front Porch Sentries: dies, -1/-1 to an opponent's creature.
#guard Selector.toTargetKind
  (.intersection [
    .zone .battlefield,
    .cardType .creature,
    .controlled (.opponent (.controller .this))])
  == .oppCreature

#guard Selector.toTargetKind
  (.intersection [
    .zone .battlefield,
    .cardType .creature,
    .controlled (.opponent (.controller .this)),
    .powerAtMost (.int 3)])
  == .oppCreaturePowerAtMost 3

#guard
  match
    (Ability.triggered
      (.die .this)
      (.continuous
        [.addPower
          (.target
            1
            (.intersection [
              .zone .battlefield,
              .cardType .creature,
              .controlled (.opponent (.controller .this))])) (Value.int (-1)),
         .addToughness
          (.targetReference 1) (Value.int (-1))]
        .endOfTurn)).toTriggeredAbility? with
  | some ab => ab == TriggeredAbility.onDiesOppCreatureGets (-1) (-1)
  | none => false

-- Great Fierce Bee: one or more other creatures die, scry 1.
#guard Selector.shape
  (.intersection [.not .this, .zone .battlefield, .cardType .creature]) |>.otherCreatures

#guard
  match
    (Ability.triggered
      (.dieSimultaneously (.intersection [.not .this, .zone .battlefield, .cardType .creature]) [])
      (.scry (.controller .this) 1)).toTriggeredAbility? with
  | some ab => ab == TriggeredAbility.onOneOrMoreOtherCreaturesDieScry 1
  | none => false

-- Stir Up Trouble: sacrifice an artifact or creature or pay {4}; destroy.
-- The additional cost functions while the spell is on the stack (CR 113.6 / 604.2).
#guard
  let action : CardAction :=
    .destroy (.target 1 (.intersection [.zone .battlefield, .cardType .creature]))
  action.toEffect == Effect.destroyCreature

#guard
  (TraditionalCardDefinition.card [
    .ability (.stackStatic (
      .additionalCost .this
        [.or [
          .sacrificeCount
            (.intersection [
              .zone .battlefield,
              .union [.cardType .artifact, .cardType .creature]])
            1,
          .mana [.generic 4]]])),
    .actions [
      .destroy (.target 1 (.intersection [.zone .battlefield, .cardType .creature]))]
  ]).toCardDef.additionalCostSacrificeArtifactOrCreature

#guard
  (TraditionalCardDefinition.card [
    .ability (.stackStatic (
      .additionalCost .this
        [.or [
          .sacrificeCount
            (.intersection [
              .zone .battlefield,
              .union [.cardType .artifact, .cardType .creature]])
            1,
          .mana [.generic 4]]]))
  ]).toCardDef.additionalCostOrPayGeneric == some 4

-- Improvised Club: sacrifice one artifact or creature as an additional cost.
#guard
  (TraditionalCardDefinition.card [
    .ability (.static (
      .additionalCost .this
        [.sacrificeCount
          (.intersection [
            .zone .battlefield,
            .union [.cardType .artifact, .cardType .creature]])
          1]))
  ]).toCardDef.additionalCostSacrificeArtifactOrCreature

-- Kingpin's Enforcers: {2}{B}, sacrifice an artifact or creature: draw a card.
#guard
  match
    (Ability.activated
      [.mana [.generic 2, .mono .black],
        .sacrificeCount
          (.intersection [
            .zone .battlefield,
            .union [.cardType .artifact, .cardType .creature]])
          1]
      (.draw (.controller .this) 1)).toActivatedAbility? with
  | some ab =>
    ab.cost.sacrificeAnotherCreatureOrArtifact &&
      ab.cost.mana == ManaCost.ofGenericAndColor 2 .black &&
      ab.effect == Effect.abilityDraw 1
  | none => false

-- Sacrifice another Goblin is `sacrificeCount` 1, not `sacrifice` (all of them).
#guard
  match
    (Ability.activated
      [.tapSymbol,
        .sacrificeCount
          (.intersection [
            .not .this,
            .zone .battlefield,
            .subtype .goblin,
            .controlled (.controller .this)])
          1]
      (.addMana (.controller .this) [.mono .black, .mono .red])).toActivatedAbility? with
  | some ab =>
      ab.cost.tap &&
      ab.cost.sacrificeAnotherSubtype == some "Goblin" &&
      ab.effect == Effect.addMana #[.colored .black, .colored .red]
  | none => false

#guard
  match
    (Ability.activated
      [.tapSymbol,
        .sacrifice
          (.intersection [
            .not .this,
            .zone .battlefield,
            .subtype .goblin,
            .controlled (.controller .this)])]
      (.addMana (.controller .this) [.mono .black, .mono .red])).toActivatedAbility? with
  | some ab => ab.cost.sacrificeAnotherSubtype.isNone
  | none => false

-- Desolation Prowler: pay 2 life, +2/+2, once each turn.
#guard
  match
    (Ability.abilityId 1
      (.activatedIf
        (.not (.happened (.abilityWithIdActivated 1) .turnStart))
        [.life 2]
        (.continuous [.addPower (.source .this) (Value.int 2),
                      .addToughness (.source .this) (Value.int 2)] .endOfTurn))).toActivatedAbility? with
  | some ab =>
    ab.effect == Effect.sourceGets 2 2 && ab.cost.payLife == 2 && ab.onceEachTurn
  | none => false

-- Ravening Warg: “while you control a creature with power 4 or greater”
-- is checked when the ability would trigger, not again on resolution.
#guard Selector.shape
  (.intersection [
    .zone .battlefield,
    .cardType .creature,
    .controlled (.controller .this),
    .powerAtLeast (Value.int 4)]) |>.ferocious

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
      (.gainLife (.controller .this) 2)).toTriggeredAbility? with
  | some ab => ab == TriggeredAbility.onAttackFerociousGainLife 2
  | none => false

#guard
  (Ability.triggered
    (.attack .this .all)
    (.if
      (.any
        (.intersection [
          .zone .battlefield,
          .cardType .creature,
          .controlled (.controller .this),
          .powerAtLeast (Value.int 4)]))
      [.gainLife (.controller .this) 2])).toTriggeredAbility?.isNone

-- Meager Meal: +1/+1 on up to one target creature; target player gains 2 life.
#guard
  let action : CardAction :=
    .sequence [
      .putCounter
        (.targets 1 (.range 0 1) (.intersection [.zone .battlefield, .cardType .creature]))
        .plusOnePlusOne
        1,
      .gainLife (.target 2 .player) 2]
  action.toEffect == Effect.plusOneUpToOneAndPlayerGainsLife 2

#guard
  CardAction.leftoverPlusOneAndGainLife?
    (.sequence [
      .putCounter
        (.targets 1 (.range 0 1) (.intersection [.zone .battlefield, .cardType .creature]))
        .plusOnePlusOne
        1,
      .gainLife (.target 1 .player) 2]) |>.isNone

#guard
  CardAction.leftoverPlusOnesOrReturnArtEnch?
    [
      .putCounter
        (.targets 1 (.range 0 2) (.intersection [.zone .battlefield, .cardType .creature]))
        .plusOnePlusOne
        1,
      .returnToHand
        (.target
          2
          (.intersection [
            .zone .graveyard,
            .union [.cardType .artifact, .cardType .enchantment],
            .owner (.controller .this)]))]

#guard
  !CardAction.leftoverPlusOnesOrReturnArtEnch?
    [
      .putCounter
        (.targets 1 (.range 0 2) (.intersection [.zone .battlefield, .cardType .creature]))
        .plusOnePlusOne
        1,
      .returnToHand
        (.target
          1
          (.intersection [
            .zone .graveyard,
            .union [.cardType .artifact, .cardType .enchantment],
            .owner (.controller .this)]))]

#guard
  CardAction.leftoverAttachTargetEquipment?
    (.attach
      (.target
        1
        (.intersection [
          .zone .battlefield,
          .subtype .equipment,
          .controlled (.controller .this)]))
      (.targets
        2
        (.range 0 1)
        (.intersection [
          .zone .battlefield,
          .cardType .creature,
          .controlled (.controller .this)])))

#guard
  !CardAction.leftoverAttachTargetEquipment?
    (.attach
      (.target
        1
        (.intersection [
          .zone .battlefield,
          .subtype .equipment,
          .controlled (.controller .this)]))
      (.targets
        1
        (.range 0 1)
        (.intersection [
          .zone .battlefield,
          .cardType .creature,
          .controlled (.controller .this)])))

-- Dreaded Bat-Cloud: {3} less if a creature died this turn.
-- The reduction functions while the spell is on the stack (CR 604.2).
#guard
  let s : Selector.Shape := { Selector.shape (.cardType .creature) with diedThisTurn := true }
  s.diedThisTurnCreature

#guard
  (TraditionalCardDefinition.card [
    .ability (
      .stackStatic
        (.if
          (.happened (.die (.cardType .creature)) .turnStart)
          [.reduceCost .this [.mana [.generic 3]]]))
  ]).toCardDef.costReductionIfCreatureDied == 3

-- Crude Bent Blade: ETB opponent sacrifices; equipped +2/+1; Equip {2}.
#guard
  match
    (Ability.triggered
      (.enter .this)
      (.sacrifice
        (.selected
          (.target 1 (.opponent (.controller .this)))
          (.range 1 1)
          (.intersection [
            .zone .battlefield,
            .cardType .creature,
            .controlled (.targetReference 1)])))).toTriggeredAbility? with
  | some ab => ab == TriggeredAbility.onEnterTargetOpponentSacrificesCreature
  | none => false

#guard
  (TraditionalCardDefinition.card [
    .ability (.static (.addPower (.hostOf .this) (Value.int 2))),
    .ability (.static (.addToughness (.hostOf .this) (Value.int 1)))
  ]).toCardDef.staticAbilities == #[.equippedCreatureGets 2 1]

#guard
  let action : CardAction :=
    .attach
      .this
      (.target
        1
        (.intersection [
          .zone .battlefield,
          .cardType .creature,
          .controlled (.controller .this)]))
  action.toAbilityEffect == Effect.attachToTargetCreatureYouControl

#guard Keyword.equip.toKeywords == Keywords.none
#guard Keyword.enchant.toKeywords == Keywords.none
#guard Keyword.recruit.toKeywords == Keywords.none
#guard (Keyword.amass .goblin (.int 1)).toKeywords == Keywords.none
#guard (Keyword.connive (.int 1)).toKeywords == Keywords.none
#guard (Keyword.chapter 1).toKeywords == Keywords.none
#guard toString Keyword.recruit == "recruit"
#guard toString (Keyword.amass .goblin (.int 1)) == "amass Goblins 1"
#guard toString (Keyword.amass .orc (.int 2)) == "amass Orcs 2"
#guard toString (Keyword.connive (.int 1)) == "connive 1"
#guard toString (Keyword.connive (.int 2)) == "connive 2"
#guard toString (Keyword.chapter 1) == "chapter I"
#guard toString (Keyword.chapter 3) == "chapter III"
#guard (Keyword.typecycling [] [] [.halfling]).toKeywords == Keywords.none
#guard toString (Keyword.typecycling [] [] [.halfling]) == "Halflingcycling"
#guard (Keyword.typecycling [.basic] [.land] []).toKeywords == Keywords.none
#guard toString (Keyword.typecycling [.basic] [.land] []) ==
  "Basic landcycling"
#guard toString (Keyword.typecycling [] [.land] []) == "landcycling"
#guard Keyword.typecyclingPhrase [] [] [.halfling] == "Halfling"
#guard Keyword.typecyclingPhrase [.basic] [.land] [] == "Basic land"

#guard
  let c :=
    (TraditionalCardDefinition.card [
      .type .enchantment,
      .subtype .aura,
      .ability (
        .keywordWithTarget
          .enchant
          1
          (.intersection [.zone .battlefield, .cardType .creature]))
    ]).toCardDef
  c.isAura && c.keywords == Keywords.none && c.activatedAbilities.isEmpty

#guard
  match
    (Ability.keywordWithCost .equip [.mana [.generic 2]]).toActivatedAbility? with
  | some ab =>
    ab.onlyAsSorcery &&
      ab.effect == Effect.attachToTargetCreatureYouControl &&
      ab.cost.mana == ManaCost.ofGeneric 2 &&
      ab.cost.payLife == 0
  | none => false

#guard
  match
    (Ability.keywordWithCost .equip [.mana [.generic 2], .life 2]).toActivatedAbility? with
  | some ab =>
    ab.onlyAsSorcery &&
      ab.effect == Effect.attachToTargetCreatureYouControl &&
      ab.cost.mana == ManaCost.ofGeneric 2 &&
      ab.cost.payLife == 2
  | none => false

#guard
  let c :=
    (TraditionalCardDefinition.card [
      .ability (.keywordWithCost .equip [.mana [.generic 2]])
    ]).toCardDef
  c.activatedAbilities.size == 1 &&
    c.activatedAbilities[0]!.onlyAsSorcery &&
    c.activatedAbilities[0]!.effect == Effect.attachToTargetCreatureYouControl &&
    c.activatedAbilities[0]!.cost.mana == ManaCost.ofGeneric 2

#guard
  match
    (Ability.keywordWithSubtypeAndCost
      .equip .human (.mana [.generic 1])).toActivatedAbility? with
  | some ab =>
    ab.onlyAsSorcery &&
      ab.equipSubtype == some "Human" &&
      ab.effect == Effect.attachToTargetCreatureYouControl &&
      ab.cost.mana == ManaCost.ofGeneric 1
  | none => false

#guard
  let c :=
    (TraditionalCardDefinition.card [
      .ability
        (.keywordWithSubtypeAndCost .equip .human (.mana [.generic 1]))
    ]).toCardDef
  c.activatedAbilities.size == 1 &&
    c.activatedAbilities[0]!.onlyAsSorcery &&
    c.activatedAbilities[0]!.equipSubtype == some "Human" &&
    c.activatedAbilities[0]!.effect == Effect.attachToTargetCreatureYouControl &&
    c.activatedAbilities[0]!.cost.mana == ManaCost.ofGeneric 1

#guard
  match
    (Ability.keywordWithCost
      (.typecycling [] [] [.halfling])
      [.mana [.generic 4]]).toActivatedAbility? with
  | some ab =>
    ab.activateFromHand &&
      ab.cost.discardSource &&
      ab.cost.mana == ManaCost.ofGeneric 4 &&
      ab.effect == Effect.searchLandTypeToHand "Halfling"
  | none => false

#guard
  let c :=
    (TraditionalCardDefinition.card [
      .ability
        (.keywordWithCost (.typecycling [] [] [.halfling]) [.mana [.generic 4]])
    ]).toCardDef
  c.activatedAbilities.size == 1 &&
    c.activatedAbilities[0]!.activateFromHand &&
    c.activatedAbilities[0]!.cost.discardSource &&
    c.activatedAbilities[0]!.effect == Effect.searchLandTypeToHand "Halfling"

#guard
  match
    (Ability.keywordWithCost
      (.typecycling [.basic] [.land] [])
      [.mana [.generic 2]]).toActivatedAbility? with
  | some ab =>
    ab.activateFromHand &&
      ab.cost.discardSource &&
      ab.cost.mana == ManaCost.ofGeneric 2 &&
      ab.effect == Effect.searchLandTypeToHand "Basic land"
  | none => false

#guard
  let c :=
    (TraditionalCardDefinition.card [
      .ability
        (.keywordWithCost
          (.typecycling [.basic] [.land] [])
          [.mana [.generic 2]])
    ]).toCardDef
  c.activatedAbilities.size == 1 &&
    c.activatedAbilities[0]!.activateFromHand &&
    c.activatedAbilities[0]!.cost.discardSource &&
    c.activatedAbilities[0]!.effect == Effect.searchLandTypeToHand "Basic land"

-- Gollum the Abandoned: can't block; ETB exile GY; return from GY.
#guard
  (TraditionalCardDefinition.card [
    .ability (.static (.forbid (.block .this .any)))
  ]).toCardDef.staticAbilities == #[.cantBlockUnlessYouControl #[]]

#guard
  match
    (Ability.triggered
      (.enter .this)
      (.sequence [
        .exile
          (.targets 1 (.range 0 1) (.intersection [.zone .graveyard, .owner (.opponent (.controller .this))])),
        .loseLife (.opponent (.controller .this)) 2])).toTriggeredAbility? with
  | some ab => ab == TriggeredAbility.onEnterExileOppGyCardOppsLoseLife 2
  | none => false

-- Returning this card from a graveyard functions there (CR 113.6).
-- `graveyardActivatedIf` records that zone.
#guard
  let costs : List Cost :=
    [.mana [.generic 2],
      .sacrificeCount
        (.intersection [
          .zone .battlefield,
          .union [.cardType .artifact, .cardType .creature]])
        1]
  let action : CardAction :=
    .returnToHand (.intersection [.zone .graveyard, .source .this])
  match
    (Ability.graveyardActivatedIf
      (.timeToCastSorcery (.controller .this)) costs action).toActivatedAbility?,
    (Ability.activatedIf
      (.timeToCastSorcery (.controller .this)) costs action).toActivatedAbility? with
  | some gy, some battlefield =>
    gy.onlyAsSorcery &&
      gy.activateFromGraveyard &&
      gy.effect == Effect.returnFromGraveyardToHand &&
      gy.cost.mana == ManaCost.ofGeneric 2 &&
      gy.cost.sacrificeAnotherCreatureOrArtifact &&
      battlefield.onlyAsSorcery &&
      !battlefield.activateFromGraveyard &&
      battlefield.effect == gy.effect
  | _, _ => false

-- Gnashing of Teeth / Reverent Howl modes.
#guard
  let action : CardAction :=
    .continuous
      [.addPower
        (.target 1 (.intersection [.zone .battlefield, .cardType .creature])) (Value.int (-5)),
       .addToughness
        (.targetReference 1) (Value.int (-5)),
        .replace
          (.putToGraveyard (.targetReference 1))
          [.exile (.replacingObject)]]
      .endOfTurn
  action.toEffect == Effect.pumpAndExileIfDies (-5) (-5)

#guard
  let action : CardAction :=
    .continuous
      [.addPower
        (.intersection [
          .zone .battlefield,
          .cardType .creature,
          .controlled (.target 1 .player)]) (Value.int (-1)),
       .addToughness
        (.intersection [
          .zone .battlefield,
          .cardType .creature,
          .controlled (.targetReference 1)]) (Value.int (-1))]
      .endOfTurn
  action.toEffect == Effect.creaturesTargetPlayerGet (-1) (-1)

#guard
  let action : CardAction :=
    .chooseUniqueModes (.range 1 1) [
      .continuous
        [.addPower
          (.target 1 (.intersection [.zone .battlefield, .cardType .creature])) (Value.int (-5)),
         .addToughness
          (.targetReference 1) (Value.int (-5)),
          .replace
            (.putToGraveyard (.targetReference 1))
            [.exile (.replacingObject)]]
        .endOfTurn,
      .continuous
        [.addPower
          (.intersection [
            .zone .battlefield,
            .cardType .creature,
            .controlled (.target 2 .player)]) (Value.int (-1)),
         .addToughness
          (.intersection [
            .zone .battlefield,
            .cardType .creature,
            .controlled (.targetReference 2)]) (Value.int (-1))]
        .endOfTurn]
  CardAction.leftoverModes? action ==
    some #[Effect.pumpAndExileIfDies (-5) (-5), Effect.creaturesTargetPlayerGet (-1) (-1)]

#guard
  let action : CardAction :=
    .sequence [.draw (.target 1 .player) 2, .loseLife (.targetReference 1) 2]
  action.toEffect == Effect.targetPlayerDrawLoseLife 2 2

#guard
  let action : CardAction :=
    .continuous
      [.addPower
        (.target 1 (.intersection [.zone .battlefield, .cardType .creature])) (Value.int 2),
       .addToughness
        (.targetReference 1) (Value.int 2),
        .gainAbility (.targetReference 1) (.keyword .lifelink)]
      .endOfTurn
  action.toEffect == Effect.pumpAndLifelink 2 2

-- Stony-Voiced Goblins: each opponent discards a card.
#guard
  match
    (Ability.triggered
      (.enter .this)
      (.discard (.opponent (.controller .this)) 1)).toTriggeredAbility? with
  | some ab => ab == TriggeredAbility.onEnterEachOpponentDiscards
  | none => false

-- Spew Flame: 5 damage to target creature.
#guard
  let action : CardAction :=
    .dealDamage
      .this
      (.target 1 (.intersection [.zone .battlefield, .cardType .creature]))
      (.int 5)
  action.toEffect == Effect.dealDamageToCreature 5

-- Gandalf, Spark Starter: enters, 3 damage divided among one to three targets.
#guard
  match
    (Ability.triggered
      (.enter .this)
      (.divideDamage
        (.controller .this)
        (.source .this)
        (.targets 1 (.range 1 3) .all)
        3)).toTriggeredAbility? with
  | some ab => ab == TriggeredAbility.onEnterDealDividedDamage 3 3
  | none => false

-- Ragged Short Spear: enters, you may discard a card. If you do, draw two.
#guard
  match
    (Ability.triggered
      (.enter .this)
      (.sequence [
        .optional (.controller .this)
          (.actionId 1 (.discard (.controller .this) 1)),
        .if (.happened (.actionWithId 1) .gameStart) [.draw (.controller .this) 2]])).toTriggeredAbility? with
  | some ab => ab == TriggeredAbility.onEnterMayDiscardDraw 2
  | none => false

#guard
  (TraditionalCardDefinition.card [
    .ability (.static (.addPower (.hostOf .this) (Value.int 2)))
  ]).toCardDef.staticAbilities == #[.equippedCreatureGets 2 0]

-- Snowslope Hunter: sacrifice another creature or artifact; exile top; your turn, once.
#guard
  let action : CardAction :=
    .sequence [
      .actionId 1 (.exile (.topOfLibrary (.controller .this) 1)),
      .continuous
        [.canPlay (.controller .this) (.wasCreatedByAction 1)]
        (.sequence [.turnStart, .endOfPlayerTurn (.controller .this)])]
  action.toAbilityEffect == Effect.exileTopPlayUntilEndOfNextTurn

#guard
  !(CardAction.leftoverExileTopPlayUntilEndOfNextTurn?
    (.sequence [
      .actionId 1 (.exile (.topOfLibrary (.controller .this) 1)),
      .continuous
        [.canPlay (.controller .this) (.wasCreatedByAction 1)]
        .endOfTurn]))

#guard
  match
    (Ability.abilityId 1
      (.activatedIf
        (.and
          (.turn (.controller .this))
          (.not (.happened (.abilityWithIdActivated 1) .turnStart)))
        [.sacrificeCount
          (.intersection [
            .not .this,
            .zone .battlefield,
            .union [.cardType .artifact, .cardType .creature]])
          1]
        (.sequence [
          .actionId 1 (.exile (.topOfLibrary (.controller .this) 1)),
          .continuous
            [.canPlay (.controller .this) (.wasCreatedByAction 1)]
            (.sequence [.turnStart, .endOfPlayerTurn (.controller .this)])]))).toActivatedAbility? with
  | some ab =>
    ab.onlyDuringYourTurn &&
      ab.onceEachTurn &&
      ab.cost.sacrificeAnotherCreatureOrArtifact &&
      ab.effect == Effect.exileTopPlayUntilEndOfNextTurn
  | none => false

#guard
  match
    (Ability.activatedIf
      (.turn (.controller .this))
      [.life 3]
      (.keyword (.source .this) (.connive (.int 1)))).toActivatedAbility? with
  | some ab =>
    ab.onlyDuringYourTurn &&
      !ab.onceEachTurn &&
      ab.cost.payLife == 3 &&
      ab.effect == Effect.connive
  | none => false

#guard
  match
    (Ability.activatedIf
      (.turn (.controller .this))
      [.life 3]
      (.keyword .this (.connive (.int 1)))).toActivatedAbility? with
  | some ab => ab.effect != Effect.connive
  | none => true

#guard
  (TraditionalCardDefinition.card [
    .ability (.static (.addPower
          (.intersection [
            .zone .battlefield,
            .cardType .creature,
            .controlled (.opponent (.controller .this))]) (Value.int (-1)))),
    .ability (.static (.addToughness
          (.intersection [
            .zone .battlefield,
            .cardType .creature,
            .controlled (.opponent (.controller .this))]) (Value.int (-1))))
  ]).toCardDef.staticAbilities == #[.opponentsCreaturesGet (-1) (-1)]

-- Guardian of the Halls: put three +1/+1 counters on this creature.
#guard
  let action : CardAction := .putCounter (.source .this) .plusOnePlusOne 3
  action.toAbilityEffect == Effect.putPlusOnePlusOneOnSource 3

-- Quarrel: a creature you control deals damage equal to its power.
#guard Selector.toTargetKind
  (.intersection [
    .zone .battlefield,
    .cardType .creature,
    .controlled (.controller .this)])
  == .creatureYouControl

#guard Selector.toTargetKind
  (.intersection [
    .zone .battlefield,
    .cardType .creature,
    .controlled (.opponent (.controller .this))])
  == .oppCreature

#guard
  let action : CardAction :=
    .dealDamage
      (.target
        1
        (.intersection [
          .zone .battlefield,
          .cardType .creature,
          .controlled (.controller .this)]))
      (.target
        2
        (.intersection [
          .zone .battlefield,
          .cardType .creature,
          .controlled (.opponent (.controller .this))]))
      (.greatestPower
        (.target
          1
          (.intersection [
            .zone .battlefield,
            .cardType .creature,
            .controlled (.controller .this)])))
  action.toEffect == Effect.creatureYouControlDealsPowerToOppCreature

-- Galion: attack, set another creature's base P/T.
#guard Selector.shape
  (.intersection [
    .not .this,
    .zone .battlefield,
    .cardType .creature,
    .controlled (.controller .this)]) |>.anotherCreatureYouControl

#guard
  match
    (Ability.triggered
      (.attack .this .all)
      (.continuous
        [.setBasePower
          (.targets
            1
            (.range 0 1)
            (.intersection [
              .not .this,
              .zone .battlefield,
              .cardType .creature,
              .controlled (.controller .this)]))
          (Value.greatestPower (.source .this)),
         .setBaseToughness
          (.targetReference 1)
          (Value.greatestToughness (.source .this))]
        .endOfTurn)).toTriggeredAbility? with
  | some ab => ab == TriggeredAbility.onAttackSetOtherBasePT
  | none => false

#guard
  let among : Selector :=
    .intersection [
      .not .this,
      .zone .battlefield,
      .cardType .creature,
      .controlled (.controller .this)]
  let who : Selector := .targets 1 (.range 0 1) among
  match
    (Ability.triggered
      (.attack .this .all)
      (.continuous
        [.setBasePower who (Value.greatestPower (.source .this)),
         .setBaseToughness who (Value.greatestToughness (.source .this))]
        .endOfTurn)).toTriggeredAbility? with
  | some _ => false
  | none => true

#guard
  match
    (Ability.triggered
      (.attack .this .all)
      (.continuous
        [.setBasePower
          (.targets
            1
            (.range 0 1)
            (.intersection [
              .not .this,
              .zone .battlefield,
              .cardType .creature,
              .controlled (.controller .this)]))
          (Value.greatestPower (.source .this))]
        .endOfTurn)).toTriggeredAbility? with
  | some _ => false
  | none => true

-- Warg Tactics: destroy a flyer, or +1/+1, trample, and hexproof.
#guard Selector.shape
  (.intersection [
    .zone .battlefield,
    .cardType .creature,
    .keyword .flying]) |>.flyingCreature

#guard Selector.toTargetKind
  (.intersection [
    .zone .battlefield,
    .cardType .creature,
    .keyword .flying])
  == .creatureWithFlying

#guard
  let action : CardAction :=
    .destroy
      (.target
        1
        (.intersection [
          .zone .battlefield,
          .cardType .creature,
          .keyword .flying]))
  action.toEffect == Effect.destroyCreatureWithFlying

#guard
  let action : CardAction :=
    .sequence [
      .putCounter
        (.target
          1
          (.intersection [
            .zone .battlefield,
            .cardType .creature,
            .controlled (.controller .this)]))
        .plusOnePlusOne
        1,
      .continuous
        [.gainAbility (.targetReference 1) (.keyword .trample),
          .gainAbility (.targetReference 1) (.keyword .hexproof)]
        .endOfTurn]
  action.toEffect == Effect.plusOnePlusOneTrampleHexproof

#guard
  let action : CardAction :=
    .chooseUniqueModes (.range 1 1) [
      .destroy
        (.target
          1
          (.intersection [
            .zone .battlefield,
            .cardType .creature,
            .keyword .flying])),
      .sequence [
        .putCounter
          (.target
            2
            (.intersection [
              .zone .battlefield,
              .cardType .creature,
              .controlled (.controller .this)]))
          .plusOnePlusOne
          1,
        .continuous
          [.gainAbility (.targetReference 2) (.keyword .trample),
            .gainAbility (.targetReference 2) (.keyword .hexproof)]
          .endOfTurn]]
  CardAction.leftoverModes? action ==
    some #[Effect.destroyCreatureWithFlying, Effect.plusOnePlusOneTrampleHexproof]

-- Beorn's Hospitality: landfall +1/+1; become a Bear and gain the lands P/T static ability.
#guard Selector.shape
  (.intersection [
    .zone .battlefield,
    .cardType .land,
    .controlled (.controller .this)]) |>.landYouControl

#guard
  match
    (Ability.triggered
      (.enter
        (.intersection [
          .zone .battlefield,
          .cardType .land,
          .controlled (.controller .this)]))
      (.putCounter
        (.target
          1
          (.intersection [
            .zone .battlefield,
            .cardType .creature,
            .controlled (.controller .this)]))
        .plusOnePlusOne
        1)).toTriggeredAbility? with
  | some ab => ab == TriggeredAbility.onLandYouControlEntersPlusOnePlusOne
  | none => false

#guard
  let action : CardAction :=
    .continuous
      [.gainType .this .creature,
        .gainSubtype .this .bear,
        .gainAbility
          .this
          (.static
            (.setPower
              .this
              (.count
                (.intersection [
                  .zone .battlefield,
                  .cardType .land,
                  .controlled (.controller .this)])))),
        .gainAbility
          .this
          (.static
            (.setToughness
              .this
              (.count
                (.intersection [
                  .zone .battlefield,
                  .cardType .land,
                  .controlled (.controller .this)]))))]
      .endOfGame
  action.toAbilityEffect == Effect.becomeSubtypeWithLandsPT "Bear"

end Mtg.Engine
