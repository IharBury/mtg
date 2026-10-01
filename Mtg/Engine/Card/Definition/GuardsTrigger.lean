import Mtg.Engine.Card.Definition.GuardsCatalog

/-!
# Trigger definition guards

Regression tests continued from `GuardsCatalog`. Exile-and-return,
graveyard triggers, and the cases that must not compile to a named
ability.
-/

namespace Mtg.Engine

-- Exile then return tapped under owner's control (Gandalf / Mighty Thor).
#guard
  CardAction.leftoverExileThenReturnTapped?
    (.sequence [
      .actionId 1
        (.exile
          (.targets
            1
            (.range 0 3)
            (.intersection [
              .zone .battlefield,
              .cardType .land,
              .controlled (.controller .this)]))),
      .putOntoBattlefieldInState
        (.wasCreatedByAction 1)
        [
          .tapped,
          .controlled (.owner (.wasCreatedByAction 1))]])
  |>.isSome

#guard
  CardAction.leftoverExileThenReturnTapped?
    (.sequence [
      .actionId 1
        (.exile
          (.targets
            1
            (.range 0 3)
            (.intersection [
              .zone .battlefield,
              .cardType .land,
              .controlled (.controller .this)]))),
      .putOntoBattlefieldInState (.wasCreatedByAction 1) [.tapped]])
  |>.isNone

#guard
  CardAction.leftoverExileThenReturnTapped?
    (.sequence [
      .actionId 1 (.exile (.targets 1 (.range 0 3) (.zone .battlefield))),
      .putOntoBattlefieldInState
        (.wasCreatedByAction 1)
        [
          .tapped,
          .controlled (.controller .this)]])
  |>.isNone

#guard
  match
    (Ability.triggered
      (.enter .this)
      (.sequence [
        .actionId 1
          (.exile
            (.targets
              1
              (.range 0 3)
              (.intersection [
                .zone .battlefield,
                .cardType .land,
                .controlled (.controller .this)]))),
        .putOntoBattlefieldInState
          (.wasCreatedByAction 1)
          [
            .tapped,
            .controlled (.owner (.wasCreatedByAction 1))]])).toTriggeredAbility? with
  | some ab => ab == TriggeredAbility.onEnterExileLandsThenReturnTapped
  | none => false

#guard
  match
    (Ability.triggered (.enter .this) (.keyword (.controller .this) .recruit)).toTriggeredAbility? with
  | some ab => ab == TriggeredAbility.onEnterRecruit
  | none => false

#guard
  (Ability.triggered (.enter .this) (.keyword .all .recruit)).toTriggeredAbility?.isNone

#guard
  match
    (Ability.triggered (.enter .this) (.keyword (.source .this) (.connive (.int 1)))).toTriggeredAbility? with
  | some ab => ab == TriggeredAbility.onEnterConnive
  | none => false

#guard
  (Ability.triggered (.enter .this) (.keyword .this (.connive (.int 1)))).toTriggeredAbility?.isNone

#guard
  (Ability.triggered (.enter .this) (.keyword (.controller .this) (.connive (.int 1)))).toTriggeredAbility?.isNone

#guard
  match
    (Ability.triggered (.attack .this .all) (.keyword (.source .this) (.connive (.int 1)))).toTriggeredAbility? with
  | some ab => ab == TriggeredAbility.onAttackConnive
  | none => false

#guard
  (Ability.triggered (.attack .this .all) (.keyword .this (.connive (.int 1)))).toTriggeredAbility?.isNone

#guard
  match
    (Ability.triggered
      (.combatStart (.controller .this))
      (.keyword
        (.target
          1
          (.intersection [
            .zone .battlefield,
            .cardType .creature,
            .controlled (.controller .this)]))
        (.connive (.int 1)))).toTriggeredAbility? with
  | some ab => ab == TriggeredAbility.onCombatTargetYouControlConnives
  | none => false

#guard
  (Ability.triggered
    (.combatStart (.opponent (.controller .this)))
    (.keyword
      (.target
        1
        (.intersection [
          .zone .battlefield,
          .cardType .creature,
          .controlled (.controller .this)]))
      (.connive (.int 1)))).toTriggeredAbility?.isNone

#guard
  match
    (Ability.triggered
      (.attack
        (.hostOf
          (.intersection [
            .zone .battlefield,
            .subtype .equipment,
            .controlled (.controller .this)]))
        .all)
      (.keyword
        (.hostOf
          (.intersection [
            .zone .battlefield,
            .subtype .equipment,
            .controlled (.controller .this)]))
        (.connive (.int 1)))).toTriggeredAbility? with
  | some ab => ab == TriggeredAbility.onEquippedCreatureYouControlAttacksConnive
  | none => false

#guard
  match
    (Ability.triggered
      (.ordinal 2 .turnStart (.draw (.controller .this) .all))
      (.createTokens (.controller .this) 1 [
        .type .creature, .subtype .villain, .colorIndicator [.black],
        .power 2, .toughness 1, .ability (.keyword .menace)])).toTriggeredAbility? with
  | some ab => ab == TriggeredAbility.onYouDrawSecondCreateTokens .villain21menace
  | none => false

#guard
  match
    (Ability.triggered
      (.ordinal 2 .turnStart (.draw (.controller .this) .all))
      (.sequence [
        .loseLife (.opponent (.controller .this)) 1,
        .gainLife (.controller .this) 1])).toTriggeredAbility? with
  | some ab => ab == TriggeredAbility.onResource Effect.resourceSecondDrawDrain
  | none => false

#guard
  match
    (Ability.triggered
      (.enter
        (.intersection [
          .not .this,
          .zone .battlefield,
          .subtype .villain,
          .controlled (.controller .this)]))
      (.attach
        (.targets
          1
          (.range 0 1)
          (.intersection [
            .zone .battlefield,
            .subtype .equipment,
            .controlled (.controller .this)]))
        (.target
          2
          (.intersection [
            .zone .battlefield,
            .cardType .creature,
            .controlled (.controller .this)])))).toTriggeredAbility? with
  | some ab => ab == TriggeredAbility.onWatch Effect.watchVillainAttachEquipment
  | none => false

#guard CardAction.toEffect (.putIntoLibraryFromTop .this 1) == Effect.putOnTopOrBottom

#guard
  !CardAction.leftoverOwnerPutsLibraryThenConnive?
    (.sequence [
      .playerSelectAction (.owner (.targetReference 1)) (.range 1 1)
        [.putOnTopOfLibrary
          (.target
            1
            (.intersection [
              .zone .battlefield,
              .cardType .creature,
              .controlled (.opponent (.controller .this))])),
          .putOnBottomOfLibrary (.targetReference 1)],
      .keyword
        (.targets
          2
          (.range 0 1)
          (.intersection [
            .zone .battlefield,
            .cardType .creature,
            .controlled (.controller .this)]))
        (.connive (.int 1))])

#guard
  CardAction.leftoverOwnerPutsLibraryThenConnive?
    (.sequence [
      .playerSelectAction (.owner (.targetReference 1)) (.range 1 1)
        [.putIntoLibraryFromTop
          (.target
            1
            (.intersection [
              .zone .battlefield,
              .cardType .creature,
              .controlled (.opponent (.controller .this))]))
          2,
          .putOnBottomOfLibrary (.targetReference 1)],
      .keyword
        (.targets
          2
          (.range 0 1)
          (.intersection [
            .zone .battlefield,
            .cardType .creature,
            .controlled (.controller .this)]))
        (.connive (.int 1))])

#guard
  CardAction.toEffect
    (.sequence [
      .playerSelectAction (.owner (.targetReference 1)) (.range 1 1)
        [.putIntoLibraryFromTop
          (.target
            1
            (.intersection [
              .zone .battlefield,
              .cardType .creature,
              .controlled (.opponent (.controller .this))]))
          2,
          .putOnBottomOfLibrary (.targetReference 1)],
      .keyword
        (.targets
          2
          (.range 0 1)
          (.intersection [
            .zone .battlefield,
            .cardType .creature,
            .controlled (.controller .this)]))
        (.connive (.int 1))]) == Effect.ownerPutsLibraryThenConnive

#guard
  match
    (Ability.triggered (.die .this) (.keyword (.controller .this) .recruit)).toTriggeredAbility? with
  | some ab => ab == TriggeredAbility.onDiesRecruit
  | none => false

#guard
  match
    (Ability.triggered
      (.enter .this)
      (.keyword (.controller .this) (.amass .goblin (.int 1)))).toTriggeredAbility? with
  | some ab => ab == TriggeredAbility.onEnterAmassGoblins 1
  | none => false

#guard
  match
    (Ability.triggered
      (.die .this)
      (.keyword (.controller .this) (.amass .goblin (.int 4)))).toTriggeredAbility? with
  | some ab => ab == TriggeredAbility.onDiesAmassGoblins 4
  | none => false

#guard
  match
    (Ability.triggered
      (.castSpell
        (.intersection [
          .spell,
          .not (.cardType .creature),
          .controlled (.controller .this)]))
      (.keyword (.controller .this) (.amass .goblin (.int 1)))).toTriggeredAbility? with
  | some ab => ab == TriggeredAbility.onCastNoncreatureAmassGoblins 1
  | none => false

#guard
  (Ability.triggered
    (.triggerId 1
      (.castSpell
        (.intersection [
          .spell,
          .not (.cardType .creature),
          .controlled (.controller .this)])))
    (.sequence [
      .optional (.controller .this)
        (.actionId 1
          (.draw (.controller .this) (.greatestManaSpent (.wasArgumentOfTrigger 1 1)))),
      .if (.happened (.actionWithId 1) .gameStart)
        [.discard (.controller .this) 2]])).toTriggeredAbility? ==
    some TriggeredAbility.onCastNoncreatureMayDrawXDiscard2

-- Mana value is not mana spent.
#guard
  (Ability.triggered
    (.triggerId 1
      (.castSpell
        (.intersection [
          .spell,
          .not (.cardType .creature),
          .controlled (.controller .this)])))
    (.sequence [
      .optional (.controller .this)
        (.actionId 1
          (.draw (.controller .this)
            (.greatestManaValue (.wasArgumentOfTrigger 1 1)))),
      .if (.happened (.actionWithId 1) .gameStart)
        [.discard (.controller .this) 2]])).toTriggeredAbility?.isNone

-- Discarding one card is not discarding two.
#guard
  (Ability.triggered
    (.triggerId 1
      (.castSpell
        (.intersection [
          .spell,
          .not (.cardType .creature),
          .controlled (.controller .this)])))
    (.sequence [
      .optional (.controller .this)
        (.actionId 1
          (.draw (.controller .this) (.greatestManaSpent (.wasArgumentOfTrigger 1 1)))),
      .if (.happened (.actionWithId 1) .gameStart)
        [.discard (.controller .this) 1]])).toTriggeredAbility?.isNone

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
      (.keyword (.controller .this) (.amass .goblin (.int 2)))).toTriggeredAbility? with
  | some ab => ab == TriggeredAbility.onYouAttackAmassGoblins 2
  | none => false

#guard
  match
    (Ability.triggered
      (.ordinal 1 .turnStart
        (.castSpell
          (.intersection [
            .spell,
            .not (.cardType .creature),
            .controlled (.opponent (.controller .this))])))
      (.keyword (.controller .this) .recruit)).toTriggeredAbility? with
  | some ab => ab == TriggeredAbility.onOpponentCastsFirstNoncreatureRecruit
  | none => false

#guard
  match
    (Ability.triggered
      (.enter .this)
      (.sequence [
        .actionId 1 (.keyword (.controller .this) (.amass .goblin (.int 1))),
        .attach .this (.wasObjectOfAction 1)])).toTriggeredAbility? with
  | some ab => ab == TriggeredAbility.onEnterAmassThenAttach 1
  | none => false

#guard
  match
    (Ability.triggered
      (.upkeep (.controller .this))
      (.createTokens (.controller .this) 1 [
        .type .creature, .subtype .wolf, .colorIndicator [.green],
        .power 2, .toughness 2])).toTriggeredAbility? with
  | some ab => ab == TriggeredAbility.onYourUpkeepCreateTokens .wolf 1
  | none => false

#guard
  (TraditionalCardDefinition.card [
    .ability (.static (.if
      (.less
        (.count
          (.intersection [
            .not .this,
            .zone .battlefield,
            .subtype .wolf,
            .controlled (.controller .this)]))
        (Value.int 2))
      [.forbid (.attack .this .all)]))
  ]).toCardDef.staticAbilities == #[.cantAttackUnlessYouControlNOther 2 "Wolf"]

#guard
  CardAction.toEffect
    (.sequence [
      .putCounter
        (.target 1
          (.intersection [
            .zone .battlefield,
            .cardType .creature,
            .controlled (.controller .this)]))
        .plusOnePlusOne 1,
      .if (.happened (.castSpellFromGraveyard .this) .gameStart)
        [.putCounter
          (.intersection [
            .not (.targetReference 1),
            .zone .battlefield,
            .cardType .creature,
            .controlled (.controller .this)])
          .plusOnePlusOne 1]]) ==
    Effect.plusOneThenEachOtherIfFromGy

#guard
  (TraditionalCardDefinition.card [
    .ability (.keywordWithCost .flashback [.mana [.generic 4, .mono .white]])
  ]).toCardDef.flashback == some (ManaCost.ofGenericAndColor 4 .white)

#guard
  (TraditionalCardDefinition.card [
    .ability (.keyword (.teamwork 2))
  ]).toCardDef.teamwork == some 2

#guard
  (TraditionalCardDefinition.card [
    .ability (.keyword (.teamwork 0))
  ]).toCardDef.teamwork.isNone

#guard
  (TraditionalCardDefinition.card [
    .ability (.keyword .improvise)
  ]).toCardDef.hasImprovise

#guard
  (TraditionalCardDefinition.card [
    .ability (.keywordWithCost .kicker [.mana [.generic 2, .mono .white]])
  ]).toCardDef.kicker == some (ManaCost.ofGenericAndColor 2 .white)

#guard
  (TraditionalCardDefinition.card [
    .ability (.keyword (.affinity [] [.elf]))
  ]).toCardDef.affinityForSubtype == some "Elf"

#guard
  (TraditionalCardDefinition.card [
    .ability (.keyword (.affinity [.artifact] []))
  ]).toCardDef.affinityForSubtype.isNone

#guard
  (TraditionalCardDefinition.card [
    .ability (.keyword .boast)
  ]).toCardDef.hasBoast

#guard
  (TraditionalCardDefinition.card [
    .ability (.keyword .cascade),
    .ability (.keyword .cascade)
  ]).toCardDef.cascade == 2

#guard
  (TraditionalCardDefinition.card [
    .ability (.keyword .extort)
  ]).toCardDef.staticAbilities == #[.extort]

#guard
  (TraditionalCardDefinition.card [
    .ability (.keywordWithCost .sneak [.mana [.generic 1, .mono .black, .mono .black]])
  ]).toCardDef.sneakCost ==
    some (ManaCost.ofGenericAndColors 1 [.black, .black])

#guard
  (TraditionalCardDefinition.card [
    .ability (.keyword (.gift .food))
  ]).toCardDef.gift == some .food

#guard
  (TraditionalCardDefinition.card [
    .ability (.keyword (.gift .card))
  ]).toCardDef.gift == some .card

#guard
  (TraditionalCardDefinition.card [
    .ability (.keyword (.gift .tappedFish))
  ]).toCardDef.gift == some .tappedFish

#guard
  (TraditionalCardDefinition.card [
    .ability (.keyword (.gift .extraTurn))
  ]).toCardDef.gift == some .extraTurn

#guard
  (TraditionalCardDefinition.card [
    .ability (.keyword (.gift .treasure))
  ]).toCardDef.giftTreasure

#guard
  (TraditionalCardDefinition.card [
    .ability (.keyword (.gift .octopus))
  ]).toCardDef.gift == some .octopus

#guard
  CardAction.toEffect
    (.sequence [
      .returnToHand (.target 1 .spell),
      .if (.happened (.giftPromised .this) .gameStart) [
        .continuous [.forbid (.castSpell .all)] .endOfTurn]]) ==
    Effect.returnSpellCantCastIfGift

#guard
  (Ability.triggered
    (.enter .this)
    (.sequence [
      .keyword (.controller .this) (.amass .goblin (.int 1)),
      .attach
        .this
        (.intersection [
          .zone .battlefield,
          .subtype .army,
          .controlled (.controller .this)])])).toTriggeredAbility?.isNone

#guard
  (Ability.triggered
    (.enter .this)
    (.sequence [
      .actionId 1 (.keyword (.controller .this) (.amass .goblin (.int 1))),
      .attach .this (.wasObjectOfAction 2)])).toTriggeredAbility?.isNone

#guard
  CardAction.leftoverDrawLoseLifeThenAmass?
    (.sequence [
      .draw (.controller .this) 1,
      .loseLife (.controller .this) 1,
      .keyword (.controller .this) (.amass .goblin (.int 2))]) == some 2

#guard
  CardAction.toEffect
    (.sequence [
      .draw (.controller .this) 1,
      .loseLife (.controller .this) 1,
      .keyword (.controller .this) (.amass .goblin (.int 2))]) == Effect.drawLoseLifeThenAmass 2

#guard
  CardAction.toEffect
    (.sequence [
      .returnToHand
        (.targets
          1
          (.range 0 1)
          (.intersection [
            .zone .graveyard,
            .cardType .creature,
            .owner (.controller .this)])),
      .keyword (.controller .this) (.amass .goblin (.int 3))]) == Effect.returnCreatureFromGyThenAmass 3

#guard
  CardAction.toEffect
    (.sequence [
      .defineValueVariable 1 (.greatestManaValue (.target 1 .spell)),
      .counter (.targetReference 1),
      .if (.lessOrEqual (.variable 1) 2)
        [.keyword (.controller .this) .recruit]]) ==
    Effect.counterThenRecruitIfMvAtMost 2

#guard
  CardAction.toEffect
    (.sequence [
      .counter (.target 1 .spell),
      .if (.lessOrEqual (.variable 1) 2)
        [.keyword (.controller .this) .recruit]]) !=
    Effect.counterThenRecruitIfMvAtMost 2

#guard
  CardAction.toEffect
    (.sequence [
      .defineValueVariable 1 (.greatestManaValue (.target 1 .spell)),
      .counter (.targetReference 2),
      .if (.lessOrEqual (.variable 1) 2)
        [.keyword (.controller .this) .recruit]]) !=
    Effect.counterThenRecruitIfMvAtMost 2

#guard
  CardAction.toEffect
    (.sequence [
      .defineValueVariable 1 (.greatestManaValue (.target 1 .spell)),
      .counter (.targetReference 1),
      .if (.less (.variable 1) 2)
        [.keyword (.controller .this) .recruit]]) !=
    Effect.counterThenRecruitIfMvAtMost 2

#guard CardAction.toEffect (.keyword (.controller .this) .recruit) == Effect.recruit
#guard CardAction.toEffect (.keyword (.controller .this) (.amass .goblin (.int 1))) == Effect.amassGoblins 1
#guard CardAction.toEffect (.keyword .this (.connive (.int 1))) == Effect.connive
#guard CardAction.toEffect (.keyword (.source .this) (.connive (.int 1))) == Effect.connive
#guard CardAction.toAbilityEffect (.keyword (.source .this) (.connive (.int 1))) == Effect.connive
#guard CardAction.toAbilityEffect (.keyword .this (.connive (.int 1))) != Effect.connive
#guard CardAction.leftoverSourceThis (.source .this)
#guard !CardAction.leftoverSourceThis .this

#guard CardAction.leftoverTokenKind? PredefinedToken.treasureToken == some TokenKind.treasure
#guard CardAction.leftoverTokenKind? PredefinedToken.foodToken == some TokenKind.food
#guard CardAction.leftoverTokenKind?
  [.type .creature, .subtype .dwarf, .colorIndicator [.red], .power 2, .toughness 2] ==
  some TokenKind.dwarf
#guard CardAction.leftoverTokenKind?
  [.type .creature, .subtype .spirit, .colorIndicator [.white], .power 1, .toughness 1,
    .ability (.keyword .flying)] ==
  some TokenKind.spirit
#guard CardAction.leftoverTokenKind?
  [.type .creature, .subtype .hero, .colorIndicator [.white], .power 3, .toughness 2,
    .ability (.keyword .vigilance)] ==
  some TokenKind.hero32vigilance
#guard CardAction.leftoverTokenKind?
  [.type .creature, .subtype .villain, .colorIndicator [.black], .power 2, .toughness 1,
    .ability (.keyword .menace)] ==
  some TokenKind.villain21menace
#guard CardAction.leftoverTokenKind?
  [.type .creature, .subtype .soldier, .colorIndicator [.white], .power 1, .toughness 1] ==
  some TokenKind.soldier11white

#guard
  CardAction.toEffect
    (.createTokens (.controller .this) 2 [
      .type .creature, .subtype .hero, .colorIndicator [.white], .power 3, .toughness 2,
      .ability (.keyword .vigilance)]) ==
    Effect.createTokens .hero32vigilance 2

#guard
  CardAction.toAbilityEffect
    (.createTokens (.controller .this) 1 PredefinedToken.treasureToken) ==
    Effect.abilityCreateTokens .treasure 1

#guard
  match
    (Ability.triggered
      (.enter .this)
      (.createTokens (.controller .this) 1 PredefinedToken.treasureToken)).toTriggeredAbility? with
  | some ab => ab == TriggeredAbility.onEnterCreateTokens .treasure 1
  | none => false

#guard
  CardAction.toAbilityEffect
    (.createTokens (.controller .this) 1 PredefinedToken.treasureToken [.tapped]) ==
    Effect.createTappedTokens .treasure 1

#guard
  match
    (Ability.triggered
      (.enter .this)
      (.createTokens (.controller .this) 1 PredefinedToken.treasureToken
        [.tapped])).toTriggeredAbility? with
  | some ab => ab == TriggeredAbility.onEnterCreateTokens .treasure 1 true
  | none => false

#guard
  match
    (Ability.triggered
      (.enter .this)
      (.playerSelectAction
        (.controller .this)
        (.range 1 1)
        [
          .createTokens (.controller .this) 1 PredefinedToken.foodToken,
          .createTokens (.controller .this) 1 PredefinedToken.treasureToken])).toTriggeredAbility? with
  | some ab => ab == TriggeredAbility.onEnterCreateFoodOrTreasure
  | none => false

#guard
  (Ability.triggered
    (.enter .this)
    (.chooseUniqueModes (.range 1 1) [
      .createTokens (.controller .this) 1 PredefinedToken.foodToken,
      .createTokens (.controller .this) 1 PredefinedToken.treasureToken])).toTriggeredAbility?
    |>.isNone

#guard
  match
    (Ability.triggered
      (.attack (.hostOf .this) .all)
      (.ifElse
        (.any (.intersection [.hostOf .this, .supertype .legendary]))
        [.createTokens (.controller .this) 2
          [.type .creature, .subtype .spirit, .colorIndicator [.white], .power 1, .toughness 1,
            .ability (.keyword .flying)]
          [.tapped, .attacking]]
        [.createTokens (.controller .this) 2
          [.type .creature, .subtype .spirit, .colorIndicator [.white], .power 1, .toughness 1,
            .ability (.keyword .flying)]
          [.tapped]])).toTriggeredAbility? with
  | some ab => ab == TriggeredAbility.onEquippedAttacksCreateSpirits
  | none => false

#guard
  match
    (Ability.triggered
      (.die .this)
      (.createTokens (.controller .this) 1 [
        .type .creature, .subtype .villain, .colorIndicator [.black], .power 2, .toughness 1,
        .ability (.keyword .menace)])).toTriggeredAbility? with
  | some ab => ab == TriggeredAbility.onDiesCreateTokens .villain21menace 1
  | none => false

#guard
  match
    (Ability.triggered
      (.enter .this)
      (.sequence [
        .actionId 1
          (.createTokens (.controller .this) 1 [
            .type .creature, .subtype .dwarf, .colorIndicator [.red], .power 2, .toughness 2]),
        .attach .this (.wasCreatedByAction 1)])).toTriggeredAbility? with
  | some ab => ab == TriggeredAbility.onEnterCreateThenAttach .dwarf
  | none => false

#guard
  CardAction.toEffect
    (.sequence [
      .createTokens (.controller .this) 1 [
        .type .creature, .subtype .villain, .colorIndicator [.black], .power 2, .toughness 1,
        .ability (.keyword .menace)],
      .continuous
        [.addPower
          (.intersection [
            .zone .battlefield,
            .cardType .creature,
            .controlled (.controller .this)]) (Value.int 1)]
        .endOfTurn]) ==
    Effect.createTokensThenTeamPump .villain21menace 1 1 0

#guard
  match
    (Ability.triggered
      (.or (.enter .this) (.attack .this .all))
      (.keyword (.controller .this) (.amass .goblin (.int 3)))).toTriggeredAbility? with
  | some ab => ab == TriggeredAbility.onEnterOrAttackAmassGoblins 3
  | none => false

#guard
  (TraditionalCardDefinition.card [
    .ability (
      .static
        (.gainAbility
          (.intersection [
            .zone .battlefield,
            .subtype .army,
            .controlled (.controller .this)])
          (.keyword .trample)))
  ]).toCardDef.staticAbilities == #[.armiesYouControlHaveTrample]

#guard CardAction.toAbilityEffect
  (.mill (.target 1 .player) 3) == Effect.millPlayer 3

#guard
  (TraditionalCardDefinition.card [
    .ability (
      .activated
        [.tapSymbol]
        (.sequence [
          .actionId 1
            (.addManaOfOneColor (.controller .this) ManaSymbol.anyColor 1),
          .continuous
            [.forbid
              (.spendManaCreatedByAction 1
                (.not
                  (.castSpell
                    (.union [.cardType .instant, .cardType .sorcery]))))]
            .endOfTurn]))
  ]).toCardDef.tapAddAnyColorForInstantOrSorcery

#guard
  CardAction.toEffect
    (.sequence [
      .actionId 1 (.mill (.controller .this) 2),
      .optional (.controller .this)
        (.returnToHand
          (.selected
            (.controller .this)
            (.range 0 1)
            (.intersection [.wasObjectOfAction 1, .zone .battlefield]))),
      .gainLife (.controller .this) 2]) ==
    Effect.millThenPutPermanentGainLife 2 2

#guard
  CardAction.toAbilityEffect
    (.sequence [
      .actionId 1 (.mill (.controller .this) 4),
      .optional (.controller .this)
        (.returnToHand
          (.selected
            (.controller .this)
            (.range 1 1)
            (.intersection [
              .wasObjectOfAction 1,
              .union [.subtype .hero, .cardType .enchantment]])))]) ==
    Effect.millThenPutSubtypeOrEnchantment 4 "Hero"

#guard
  CardAction.toEffect
    (.sequence [
      .actionId 1 (.mill (.controller .this) 4),
      .returnToHand
        (.selected
          (.controller .this)
          (.range 0 2)
          (.intersection [.wasObjectOfAction 1, .cardType .land]))]) ==
    Effect.millThenPutLands 4 2

#guard
  match
    (Ability.triggered
      (.ordinal 2 .turnStart (.draw (.controller .this) .all))
      (.mill (.target 1 .player) 3)).toTriggeredAbility? with
  | some ab => ab == TriggeredAbility.onDrawSecondMillPlayer 3
  | none => false

#guard
  match
    (Ability.triggered
      (.enter
        (.intersection [
          .zone .battlefield,
          .cardType .land,
          .controlled (.controller .this)]))
      (.createTokens (.controller .this) 1 [
        .type .creature, .subtype .elf, .colorIndicator [.green],
        .power 1, .toughness 1])).toTriggeredAbility? with
  | some ab => ab == TriggeredAbility.onLandYouControlEntersCreateTokens .elf 1
  | none => false

#guard
  match
    (Ability.triggered
      (.enter .this)
      (.sequence [
        .actionId 1 (.mill (.controller .this) 4),
        .returnToHand
          (.intersection [.wasObjectOfAction 1, .subtype .elf])])).toTriggeredAbility? with
  | some ab => ab == TriggeredAbility.onEnterMillThenSubtypeToHand 4 "Elf"
  | none => false

#guard
  match
    (Ability.triggered
      (.enter .this)
      (.destroy
        (.target 1
          (.intersection [
            .zone .battlefield,
            .cardType .creature,
            .controlled (.opponent (.controller .this)),
            .powerAtMost (.int 3)])))).toTriggeredAbility? with
  | some ab =>
    ab == TriggeredAbility.onEnter (Effect.enterDestroy (.oppCreaturePowerAtMost 3))
  | none => false

#guard CardAction.toEffect
  (.surveil (.controller .this) 2) == Effect.scry 2

#guard
  CardAction.toEffect
    (.sequence [
      .destroy
        (.target 1 (.intersection [.zone .battlefield, .cardType .creature])),
      .surveil (.controller .this) 1]) ==
    Effect.destroyCreatureSurveil

#guard
  match
    (Ability.triggered
      (.enter .this)
      (.surveil (.controller .this) 2)).toTriggeredAbility? with
  | some ab => ab == TriggeredAbility.onEnterSurveil 2
  | none => false

#guard
  match
    (Ability.triggered
      (.enter .this)
      (.createTokens (.controller .this) 1 [
        .name "Redwing",
        .type .creature,
        .supertype .legendary,
        .subtype .bird,
        .subtype .scout,
        .colorIndicator [.blue],
        .power 1,
        .toughness 1,
        .ability (.keyword .flying),
        .ability
          (.triggered
            (.attack .this .all)
            (.surveil (.controller .this) 1))])).toTriggeredAbility? with
  | some ab => ab == TriggeredAbility.onEnter Effect.enterCreateRedwing
  | none => false

#guard
  let action : CardAction :=
    .searchLibraryThenShuffle
      (.controller .this)
      [
        .defineSelectorVariable 1
          (.selected
            (.controller .this)
            (.range 0 2)
            (.intersection [
              .zone .library,
              .cardType .land,
              .supertype .basic])),
        .reveal (.variable 1),
        .putOntoBattlefieldInState
          (.selected (.controller .this) (.range 1 1) (.variable 1))
          [.tapped],
        .returnToHand (.variable 1)]
  action.toAbilityEffect == Effect.searchTwoBasicsSplit

#guard
  let action : CardAction :=
    .searchLibraryThenShuffle
      (.controller .this)
      [
        .defineSelectorVariable 1
          (.selected
            (.controller .this)
            (.range 0 2)
            (.intersection [
              .zone .library,
              .cardType .land,
              .supertype .basic])),
        .reveal (.variable 1),
        .putOntoBattlefieldInState
          (.selected (.controller .this) (.range 0 1) (.variable 1))
          [.tapped],
        .returnToHand (.variable 1)]
  action.toAbilityEffect != Effect.searchTwoBasicsSplit

#guard
  let action : CardAction :=
    .searchLibraryThenShuffle
      (.controller .this)
      [
        .defineSelectorVariable 1
          (.selected
            (.controller .this)
            (.range 1 1)
            (.intersection [.zone .library, .subtype .plan])),
        .reveal (.variable 1),
        .returnToHand (.variable 1)]
  action.toAbilityEffect == Effect.searchLandTypeToHand "Plan"

#guard
  let action : CardAction :=
    .destroy
      (.target
        1
        (.intersection [
          .zone .battlefield,
          .union [.cardType .artifact, .cardType .enchantment],
          .not (.cardType .creature)]))
  action.toAbilityEffect == Effect.destroyTargetNoncreatureArtOrEnch

#guard
  match
    (Ability.triggered
      (.enter .this)
      (.returnToHand
        (.target
          1
          (.intersection [
            .zone .graveyard,
            .zone .battlefield,
            .owner (.controller .this),
            .wasObjectSince (.putToGraveyard .all) .turnStart])))).toTriggeredAbility? with
  | some ab => ab == TriggeredAbility.onEnter Effect.enterReturnGyPermanentThisTurn
  | none => false

#guard
  (Ability.triggered
    (.enter .this)
    (.returnToHand
      (.target
        1
        (.intersection [
          .zone .graveyard,
          .zone .battlefield,
          .owner (.controller .this)])))).toTriggeredAbility?.isNone

-- Dying this turn is not “put into a graveyard from anywhere this turn”.
#guard
  (Ability.triggered
    (.enter .this)
    (.returnToHand
      (.target
        1
        (.intersection [
          .zone .graveyard,
          .zone .battlefield,
          .owner (.controller .this),
          .wasObjectSince (.die .all) .turnStart])))).toTriggeredAbility?.isNone

-- Since the start of the game is not this turn.
#guard
  (Ability.triggered
    (.enter .this)
    (.returnToHand
      (.target
        1
        (.intersection [
          .zone .graveyard,
          .zone .battlefield,
          .owner (.controller .this),
          .wasObjectSince (.putToGraveyard .all) .gameStart])))).toTriggeredAbility?.isNone

#guard
  match
    (Ability.triggered
      (.enter .this)
      (.fight
        .this
        (.targets
          1
          (.range 0 1)
          (.intersection [
            .not .this,
            .zone .battlefield,
            .cardType .creature])))).toTriggeredAbility? with
  | some ab => ab == TriggeredAbility.onEnter Effect.enterFightUpToOne
  | none => false

#guard
  (Ability.triggered
    (.enter .this)
    (.dealDamage
      .this
      (.targets
        1
        (.range 0 1)
        (.intersection [
          .not .this,
          .zone .battlefield,
          .cardType .creature]))
      (.greatestPower .this))).toTriggeredAbility?.isNone

#guard
  (Ability.triggered
    (.enter .this)
    (.dealDamage
      .this
      (.targets
        1
        (.range 0 1)
        (.intersection [
          .not .this,
          .zone .battlefield,
          .cardType .creature]))
      (.int 3))).toTriggeredAbility?.isNone

#guard
  let others : Selector :=
    .intersection [
      .not .this,
      .zone .battlefield,
      .cardType .creature,
      .controlled (.controller .this)]
  match
    (Ability.triggered
      (.or (.enter .this) (.attack .this .all))
      (.sequence [
        .putCounter others .plusOnePlusOne 1,
        .forEachVariable 1 others [.gainLife (.controller .this) 1]])).toTriggeredAbility? with
  | some ab => ab == TriggeredAbility.onEnterOrAttackPlusOneEachOtherGainLife
  | none => false

-- A flat 1 life is not 1 life for each other creature.
#guard
  (Ability.triggered
    (.or (.enter .this) (.attack .this .all))
    (.sequence [
      .putCounter
        (.intersection [
          .not .this,
          .zone .battlefield,
          .cardType .creature,
          .controlled (.controller .this)])
        .plusOnePlusOne
        1,
      .gainLife (.controller .this) 1])).toTriggeredAbility?.isNone

-- 2 life for each is not 1 life for each.
#guard
  let others : Selector :=
    .intersection [
      .not .this,
      .zone .battlefield,
      .cardType .creature,
      .controlled (.controller .this)]
  (Ability.triggered
    (.or (.enter .this) (.attack .this .all))
    (.sequence [
      .putCounter others .plusOnePlusOne 1,
      .forEachVariable 1 others [.gainLife (.controller .this) 2]])).toTriggeredAbility?.isNone

-- Including this creature is not each other creature.
#guard
  let yours : Selector :=
    .intersection [
      .zone .battlefield,
      .cardType .creature,
      .controlled (.controller .this)]
  (Ability.triggered
    (.or (.enter .this) (.attack .this .all))
    (.sequence [
      .putCounter yours .plusOnePlusOne 1,
      .forEachVariable 1 yours [.gainLife (.controller .this) 1]])).toTriggeredAbility?.isNone

#guard
  match
    (Ability.triggered
      (.ordinal 2 .turnStart (.draw (.controller .this) .all))
      (.putCounter
        (.target 1 (.intersection [.zone .battlefield, .cardType .creature]))
        .plusOnePlusOne
        1)).toTriggeredAbility? with
  | some ab => ab == TriggeredAbility.onResource Effect.resourceSecondDrawPlusOneTarget
  | none => false

#guard
  match
    (Ability.triggered
      (.castSpell
        (.intersection [
          .spell,
          .not (.cardType .creature),
          .controlled (.controller .this)]))
      (.tap
        (.target
          1
          (.union [.cardType .creature, .cardType .land])))).toTriggeredAbility? with
  | some ab => ab == TriggeredAbility.onCasting Effect.castingTapCreatureOrLand
  | none => false

#guard
  (TraditionalCardDefinition.card [
    .ability (.static (.addPower
          (.intersection [
            .not .this,
            .zone .battlefield,
            .cardType .creature,
            .subtype .villain,
            .controlled (.controller .this)]) (Value.int 2))),
    .ability (.static (.addToughness
          (.intersection [
            .not .this,
            .zone .battlefield,
            .cardType .creature,
            .subtype .villain,
            .controlled (.controller .this)]) (Value.int 1)))
  ]).toCardDef.staticAbilities == #[.otherCreaturesGet #["Villain"] 2 1]

#guard
  let dwarves : Selector :=
    .intersection [
      .not .this,
      .zone .battlefield,
      .cardType .creature,
      .subtype .dwarf,
      .controlled (.controller .this)]
  let tokens : Selector :=
    .intersection [
      .zone .battlefield,
      .token,
      .cardType .artifact,
      .controlled (.controller .this)]
  (TraditionalCardDefinition.card [
    .ability
      (.static
        (.addPower dwarves (Value.count tokens)))
  ]).toCardDef.staticAbilities == #[.otherSubtypeGetPowerPerArtifactToken "Dwarf"]

#guard
  let dwarves : Selector :=
    .intersection [
      .not .this,
      .zone .battlefield,
      .cardType .creature,
      .subtype .dwarf,
      .controlled (.controller .this)]
  let tokens : Selector :=
    .intersection [
      .zone .battlefield,
      .token,
      .cardType .artifact,
      .controlled (.controller .this)]
  (TraditionalCardDefinition.card [
    .ability (.static (.addPower dwarves (Value.count tokens))),
    .ability (.static (.addToughness dwarves (Value.count tokens)))
  ]).toCardDef.staticAbilities == #[]

#guard
  (TraditionalCardDefinition.card [
    .ability
      (.static
        (.if
          (.any
            (.intersection [
              .zone .battlefield,
              .token,
              .cardType .artifact,
              .controlled (.controller .this)]))
          [
            .addPower
              (.intersection [
                .not .this,
                .zone .battlefield,
                .cardType .creature,
                .subtype .dwarf,
                .controlled (.controller .this)]) (Value.int 1)]))
  ]).toCardDef.staticAbilities != #[.otherSubtypeGetPowerPerArtifactToken "Dwarf"]

#guard
  (TraditionalCardDefinition.card [
    .ability
      (.static
        (.if
          (.greaterOrEqual
            (.count
              (.intersection [
                .zone .graveyard,
                .cardType .creature,
                .owner (.controller .this)]))
            2)
          [.addPower .this (Value.int 2),
           .addToughness .this (Value.int 1)]))
  ]).toCardDef.staticAbilities == #[.getsIfGyCreatureCards 2 2 1]

#guard
  (TraditionalCardDefinition.card [
    .ability
      (.static
        (.if
          (.any
            (.intersection [
              .zone .graveyard,
              .cardType .creature,
              .owner (.controller .this)]))
          [.addPower .this (Value.int 2),
           .addToughness .this (Value.int 1)]))
  ]).toCardDef.staticAbilities == #[]

-- One creature card is not enough (Killmonger needs two or more).
#guard
  (TraditionalCardDefinition.card [
    .ability
      (.static
        (.if
          (.greaterOrEqual
            (.count
              (.intersection [
                .zone .graveyard,
                .cardType .creature,
                .owner (.controller .this)]))
            1)
          [.addPower .this (Value.int 2),
           .addToughness .this (Value.int 1)]))
  ]).toCardDef.staticAbilities == #[]

#guard
  (TraditionalCardDefinition.card [
    .ability
      (.static
        (.if
          (.greaterOrEqual
            (.count
              (.intersection [
                .zone .graveyard,
                .cardType .creature,
                .owner (.controller .this)]))
            2)
          [
            .addPower .this (Value.int 2),
            .addToughness .this (Value.int 2),
            .gainAllSubtypes .this .creature]))
  ]).toCardDef.staticAbilities == #[.getsAndAllTypesIfGyCreatureCards 2 2 2]

#guard
  (TraditionalCardDefinition.card [
    .ability
      (.static
        (.if
          (.greaterOrEqual
            (.count
              (.intersection [
                .zone .graveyard,
                .cardType .creature,
                .owner (.controller .this)]))
            2)
          [.addPower .this (Value.int 2),
           .addToughness .this (Value.int 2)]))
  ]).toCardDef.staticAbilities == #[.getsIfGyCreatureCards 2 2 2]

#guard
  (TraditionalCardDefinition.card [
    .ability
      (.static
        (.if
          (.greaterOrEqual
            (.count
              (.intersection [
                .zone .graveyard,
                .cardType .creature,
                .owner (.controller .this)]))
            2)
          [
            .addPower .this (Value.int 2),
            .addToughness .this (Value.int 2),
            .gainSubtype .this .elf]))
  ]).toCardDef.staticAbilities == #[]

#guard
  (TraditionalCardDefinition.card [
    .ability
      (.static
        (.if
          (.greaterOrEqual
            (.count
              (.intersection [
                .zone .graveyard,
                .cardType .creature,
                .owner (.controller .this)]))
            2)
          [
            .addPower .this (Value.int 2),
            .addToughness .this (Value.int 2),
            .gainAllSubtypes .this .artifact]))
  ]).toCardDef.staticAbilities == #[]

#guard
  (TraditionalCardDefinition.card [
    .ability
      (.static
        (.if
          (.any
            (.intersection [
              .zone .graveyard,
              .cardType .creature,
              .owner (.controller .this)]))
          [
            .addPower .this (Value.int 2),
            .addToughness .this (Value.int 2),
            .gainAllSubtypes .this .creature]))
  ]).toCardDef.staticAbilities == #[]

#guard
  (TraditionalCardDefinition.card [
    .ability
      (.static
        (.if
          (.any
            (.intersection [
              .zone .graveyard,
              .cardType .creature,
              .owner (.controller .this)]))
          [.addPower .this (Value.int 2),
           .addToughness .this (Value.int 2)]))
  ]).toCardDef.staticAbilities == #[]

-- One creature card is not enough (Undercover Skrull needs two or more).
#guard
  (TraditionalCardDefinition.card [
    .ability
      (.static
        (.if
          (.greaterOrEqual
            (.count
              (.intersection [
                .zone .graveyard,
                .cardType .creature,
                .owner (.controller .this)]))
            1)
          [
            .addPower .this (Value.int 2),
            .addToughness .this (Value.int 2),
            .gainAllSubtypes .this .creature]))
  ]).toCardDef.staticAbilities == #[]

#guard
  (TraditionalCardDefinition.card [
    .ability
      (.static
        (.if
          (.greaterOrEqual
            (.count
              (.intersection [
                .zone .graveyard,
                .cardType .creature,
                .owner (.controller .this)]))
            1)
          [.addPower .this (Value.int 2),
           .addToughness .this (Value.int 2)]))
  ]).toCardDef.staticAbilities == #[]

#guard
  (TraditionalCardDefinition.card [
    .ability
      (.static
        (.if
          (.happened
            (.putCountersSimultaneously (.controller .this) .this .plusOnePlusOne)
            .turnStart)
          [.gainAbility .this (.keyword .flying)]))
  ]).toCardDef.staticAbilities == #[.flyingIfPlusOneThisTurn]

-- Putting counters on any object is not enough (Beast is this creature).
#guard
  (TraditionalCardDefinition.card [
    .ability
      (.static
        (.if
          (.happened
            (.putCountersSimultaneously (.controller .this) .all .plusOnePlusOne)
            .turnStart)
          [.gainAbility .this (.keyword .flying)]))
  ]).toCardDef.staticAbilities == #[]

-- Since the start of the game is not this turn.
#guard
  (TraditionalCardDefinition.card [
    .ability
      (.static
        (.if
          (.happened
            (.putCountersSimultaneously (.controller .this) .this .plusOnePlusOne)
            .gameStart)
          [.gainAbility .this (.keyword .flying)]))
  ]).toCardDef.staticAbilities == #[]

#guard
  (TraditionalCardDefinition.card [
    .ability
      (.static
        (.if
          (.happened (.putToGraveyard .this) .turnStart)
          [.gainAbility .this (.keyword .flying)]))
  ]).toCardDef.staticAbilities == #[]

-- Dying (being put into a graveyard from the battlefield) is not enough.
#guard
  (TraditionalCardDefinition.card [
    .ability
      (.static
        (.if
          (.happened (.die .this) .turnStart)
          [.gainAbility .this (.keyword .flying)]))
  ]).toCardDef.staticAbilities == #[]

end Mtg.Engine
