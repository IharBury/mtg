import Mtg.Engine.Card.Definition.GuardsTrigger

/-!
# Saga and equipment guards

Regression tests continued from `GuardsTrigger`. Alliance, Saga chapters,
Equipment, and Adventure costs. Add a new guard at the end of this file.
-/

namespace Mtg.Engine

-- Galadriel, Light of Valinor: you choose modes unchosen this turn by
-- any player. Unrestricted `chooseUniqueModes` does not compile to Alliance.
#guard
  let you : Selector := .controller .this
  let among : Selector :=
    .intersection [
      .not .this,
      .permanent,
      .cardType .creature,
      .controlled you]
  let unchosen (id : Nat) : Condition :=
    .didNotHappen (.modeWithIdChosen .player id) .turnStart
  let modes : List (Nat × Condition × List CardAction) :=
    [
      (1, unchosen 1,
        [.addMana you [.mono .green, .mono .green, .mono .green]]),
      (2, unchosen 2,
        [.putCounter
          (.intersection [
            .permanent,
            .cardType .creature,
            .controlled you])
          .plusOnePlusOne
          1]),
      (3, unchosen 3,
        [.sequence [.scry you 2, .draw you 1]])]
  match
    (Ability.triggered (.enter among) (.chooseModeRestricted you modes)
      ).toTriggeredAbility? with
  | some ab => ab == TriggeredAbility.onAnotherCreatureYouControlEntersAlliance
  | none => false

#guard
  let you : Selector := .controller .this
  let among : Selector :=
    .intersection [
      .not .this,
      .permanent,
      .cardType .creature,
      .controlled you]
  let modes : List CardAction :=
    [
      .addMana you [.mono .green, .mono .green, .mono .green],
      .putCounter
        (.intersection [
          .permanent,
          .cardType .creature,
          .controlled you])
        .plusOnePlusOne
        1,
      .sequence [.scry you 2, .draw you 1]]
  (Ability.triggered (.enter among) (.chooseUniqueModes (.range 1 1) modes)).toTriggeredAbility?.isNone

-- An opponent choosing is not you.
#guard
  let you : Selector := .controller .this
  let among : Selector :=
    .intersection [
      .not .this,
      .permanent,
      .cardType .creature,
      .controlled you]
  let unchosen (id : Nat) : Condition :=
    .didNotHappen (.modeWithIdChosen .player id) .turnStart
  let modes : List (Nat × Condition × List CardAction) :=
    [
      (1, unchosen 1,
        [.addMana you [.mono .green, .mono .green, .mono .green]]),
      (2, unchosen 2,
        [.putCounter
          (.intersection [
            .permanent,
            .cardType .creature,
            .controlled you])
          .plusOnePlusOne
          1]),
      (3, unchosen 3,
        [.sequence [.scry you 2, .draw you 1]])]
  (Ability.triggered (.enter among)
    (.chooseModeRestricted (.opponent you) modes)).toTriggeredAbility?.isNone

-- Only you having chosen the mode is not any player.
#guard
  let you : Selector := .controller .this
  let among : Selector :=
    .intersection [
      .not .this,
      .permanent,
      .cardType .creature,
      .controlled you]
  let unchosenYou (id : Nat) : Condition :=
    .didNotHappen (.modeWithIdChosen you id) .turnStart
  let modes : List (Nat × Condition × List CardAction) :=
    [
      (1, unchosenYou 1,
        [.addMana you [.mono .green, .mono .green, .mono .green]]),
      (2, unchosenYou 2,
        [.putCounter
          (.intersection [
            .permanent,
            .cardType .creature,
            .controlled you])
          .plusOnePlusOne
          1]),
      (3, unchosenYou 3,
        [.sequence [.scry you 2, .draw you 1]])]
  (Ability.triggered (.enter among)
    (.chooseModeRestricted you modes)).toTriggeredAbility?.isNone

-- Since the start of the game is not this turn.
#guard
  let you : Selector := .controller .this
  let among : Selector :=
    .intersection [
      .not .this,
      .permanent,
      .cardType .creature,
      .controlled you]
  let unchosenGame (id : Nat) : Condition :=
    .didNotHappen (.modeWithIdChosen .player id) .gameStart
  let modes : List (Nat × Condition × List CardAction) :=
    [
      (1, unchosenGame 1,
        [.addMana you [.mono .green, .mono .green, .mono .green]]),
      (2, unchosenGame 2,
        [.putCounter
          (.intersection [
            .permanent,
            .cardType .creature,
            .controlled you])
          .plusOnePlusOne
          1]),
      (3, unchosenGame 3,
        [.sequence [.scry you 2, .draw you 1]])]
  (Ability.triggered (.enter among)
    (.chooseModeRestricted you modes)).toTriggeredAbility?.isNone

-- The same mode ID on every choice is not three Alliance modes.
#guard
  let you : Selector := .controller .this
  let among : Selector :=
    .intersection [
      .not .this,
      .permanent,
      .cardType .creature,
      .controlled you]
  let unchosen1 : Condition :=
    .didNotHappen (.modeWithIdChosen .player 1) .turnStart
  let modes : List (Nat × Condition × List CardAction) :=
    [
      (1, unchosen1,
        [.addMana you [.mono .green, .mono .green, .mono .green]]),
      (1, unchosen1,
        [.putCounter
          (.intersection [
            .permanent,
            .cardType .creature,
            .controlled you])
          .plusOnePlusOne
          1]),
      (1, unchosen1,
        [.sequence [.scry you 2, .draw you 1]])]
  (Ability.triggered (.enter among)
    (.chooseModeRestricted you modes)).toTriggeredAbility?.isNone

-- Night Nurse: only graveyard permanents put there this turn.
-- Justice: bounce-watch is return-to-hand, includes tokens.
-- Arnim Zola: activate only if two or more creature cards in the graveyard.
-- Moonstone: discard trigger, that discarded card, not any put-to-graveyard.
-- Fin Fang Foom: copy that spell with new targets if it targets an artifact or land.
#guard
  match
    (Ability.triggered
      (.returnToHand
        (.intersection [
          .not .this,
          .permanent,
          .not (.cardType .land),
          .controlled (.controller .this)]))
      (.putCounter (.source .this) .plusOnePlusOne 1)).toTriggeredAbility? with
  | some ab => ab == TriggeredAbility.onWatch Effect.watchJusticeBounce
  | none => false

#guard
  (Ability.triggered
    (.putToGraveyard
      (.intersection [
        .not .this,
        .permanent,
        .not (.cardType .land),
        .controlled (.controller .this)]))
    (.putCounter (.source .this) .plusOnePlusOne 1)).toTriggeredAbility?.isNone

#guard
  (Ability.triggered
    (.returnToHand
      (.intersection [
        .not .this,
        .permanent,
        .not (.cardType .land),
        .not .token,
        .controlled (.controller .this)]))
    (.putCounter (.source .this) .plusOnePlusOne 1)).toTriggeredAbility?.isNone

#guard
  match
    (Ability.activatedIf
      (.greaterOrEqual
        (.count
          (.intersection [
            .inGraveyard,
            .cardType .creature,
            .owner (.controller .this)]))
        2)
      [.mana [.generic 3], .tapSymbol]
      (.createTokens
        (.controller .this)
        1
        [
          .type .creature, .subtype .villain, .colorIndicator [.black],
          .power 2, .toughness 1, .ability (.keyword .menace)]
        [.tapped])).toActivatedAbility? with
  | some ab => ab.onlyIfGyCreaturesAtLeast == 2
  | none => false

#guard
  (Ability.activatedIf
    (.any
      (.intersection [
        .inGraveyard,
        .cardType .creature,
        .owner (.controller .this)]))
    [.mana [.generic 3], .tapSymbol]
    (.createTokens
      (.controller .this)
      1
      [
        .type .creature, .subtype .villain, .colorIndicator [.black],
        .power 2, .toughness 1, .ability (.keyword .menace)]
      [.tapped])).toActivatedAbility?.isNone

#guard
  (Ability.activatedIf
    (.greaterOrEqual
      (.count
        (.intersection [
          .inGraveyard,
          .cardType .creature,
          .owner (.controller .this)]))
      1)
    [.mana [.generic 3], .tapSymbol]
    (.createTokens
      (.controller .this)
      1
      [
        .type .creature, .subtype .villain, .colorIndicator [.black],
        .power 2, .toughness 1, .ability (.keyword .menace)]
      [.tapped])).toActivatedAbility?.isNone

#guard
  match
    (Ability.activated
      [.mana [.generic 3], .tapSymbol]
      (.createTokens
        (.controller .this)
        1
        [
          .type .creature, .subtype .villain, .colorIndicator [.black],
          .power 2, .toughness 1, .ability (.keyword .menace)]
        [.tapped])).toActivatedAbility? with
  | some ab => ab.onlyIfGyCreaturesAtLeast == 0
  | none => false

-- Naming the cast's argument before that cast is numbered does not compile.
#guard
  (Ability.triggered
    (.sequence [
      .spendManaFrom (.subtype .treasure)
        (.castSpell (.wasArgumentOfTrigger 1 1)),
      .triggerId 1
        (.castSpell (.intersection [.spell, .controlled (.controller .this)]))])
    (.sequence [
      .draw (.controller .this) 1,
      .loseLife (.controller .this) 1])).toTriggeredAbility?.isNone

-- The numbered cast comes after the payment only when the payment's event
-- is that cast. Numbering the cast first, then paying for its argument,
-- does not compile.
#guard
  (Ability.triggered
    (.sequence [
      .triggerId 1
        (.castSpell (.intersection [.spell, .controlled (.controller .this)])),
      .spendManaFrom (.subtype .treasure)
        (.castSpell (.wasArgumentOfTrigger 1 1))])
    (.sequence [
      .draw (.controller .this) 1,
      .loseLife (.controller .this) 1])).toTriggeredAbility?.isNone

-- A Treasure artifact permanent is a narrower source than the Treasure subtype.
#guard
  (Ability.triggered
    (.sequence [
      .spendManaFrom
        (.intersection [.permanent, .cardType .artifact, .subtype .treasure])
        (.triggerId 1
          (.castSpell (.intersection [.spell, .controlled (.controller .this)]))),
      .castSpell (.wasArgumentOfTrigger 1 1)])
    (.sequence [
      .draw (.controller .this) 1,
      .loseLife (.controller .this) 1])).toTriggeredAbility?.isNone

#guard
  let action : CardAction :=
    .optional (.controller .this)
      (.sequence [
        .actionId 1
          (.exile (.intersection [
            .inGraveyard,
            .wasArgumentOfTrigger 1 1,
            .owner (.controller .this)])),
        .continuous
          [.canPlay (.controller .this) (.wasCreatedByAction 1)]
          (.sequence [.turnStart, .endOfPlayerTurn (.controller .this)])])
  match (Ability.triggered (.triggerId 1 (.discard (.controller .this))) action).toTriggeredAbility? with
  | some ab => ab == TriggeredAbility.onResource Effect.resourceDiscardExilePlay
  | none => false

#guard
  let action : CardAction :=
    .optional (.controller .this)
      (.sequence [
        .actionId 1
          (.exile (.intersection [.inGraveyard, .owner (.controller .this)])),
        .continuous
          [.canPlay (.controller .this) (.wasCreatedByAction 1)]
          (.sequence [.turnStart, .endOfPlayerTurn (.controller .this)])])
  (Ability.triggered (.discard (.controller .this)) action).toTriggeredAbility?.isNone

#guard
  let action : CardAction :=
    .optional (.controller .this)
      (.sequence [
        .actionId 1
          (.exile (.intersection [
            .inGraveyard,
            .wasObjectSince (.discard (.controller .this)) .turnStart,
            .owner (.controller .this)])),
        .continuous
          [.canPlay (.controller .this) (.wasCreatedByAction 1)]
          (.sequence [.turnStart, .endOfPlayerTurn (.controller .this)])])
  (Ability.triggered (.discard (.controller .this)) action).toTriggeredAbility?.isNone

#guard
  let action : CardAction :=
    .optional (.controller .this)
      (.sequence [
        .actionId 1
          (.exile (.intersection [
            .inGraveyard,
            .wasArgumentOfTrigger 1 1,
            .owner (.controller .this)])),
        .continuous
          [.canPlay (.controller .this) (.wasCreatedByAction 1)]
          (.sequence [.turnStart, .endOfPlayerTurn (.controller .this)])])
  (Ability.triggered (.triggerId 1 (.putToGraveyard (.owner (.controller .this)))) action
    ).toTriggeredAbility?.isNone

#guard
  match
    (Ability.triggered
      (.triggerId 1
        (.castSpell
          (.intersection [
            .spell,
            .union [.cardType .instant, .cardType .sorcery],
            .controlled (.controller .this),
            .hasTarget (.union [.cardType .artifact, .cardType .land])])))
      (.sequence [
        .copyWithNewTargets (.controller .this) (.wasArgumentOfTrigger 1 1),
        .putCounter (.source .this) .plusOnePlusOne 2])).toTriggeredAbility? with
  | some ab => ab == TriggeredAbility.onCasting Effect.castingCopyIfArtifactOrLand
  | none => false

#guard
  (Ability.triggered
    (.castSpell
      (.intersection [
        .spell,
        .union [.cardType .instant, .cardType .sorcery],
        .controlled (.controller .this)]))
    (.if
      (.targetsIncludeAny
        (.intersection [
          .spell,
          .union [.cardType .instant, .cardType .sorcery],
          .controlled (.controller .this)])
        (.union [.cardType .artifact, .cardType .land]))
      [.putCounter (.source .this) .plusOnePlusOne 2])).toTriggeredAbility?.isNone

#guard
  (Ability.triggered
    (.triggerId 1
      (.castSpell
        (.intersection [
          .spell,
          .union [.cardType .instant, .cardType .sorcery],
          .controlled (.controller .this)])))
    (.sequence [
      .copyWithNewTargets (.controller .this) (.wasArgumentOfTrigger 1 1),
      .putCounter (.source .this) .plusOnePlusOne 2])).toTriggeredAbility?.isNone

#guard
  (Ability.triggered
    (.castSpell
      (.intersection [
        .spell,
        .union [.cardType .instant, .cardType .sorcery],
        .controlled (.controller .this),
        .hasTarget (.union [.cardType .artifact, .cardType .land])]))
    (.sequence [
      .copyWithNewTargets (.controller .this) .all,
      .putCounter (.source .this) .plusOnePlusOne 2])).toTriggeredAbility?.isNone

#guard
  (Ability.triggered
    (.triggerId 1
      (.castSpell
        (.intersection [
          .spell,
          .union [.cardType .instant, .cardType .sorcery],
          .controlled (.controller .this),
          .hasTarget (.cardType .creature)])))
    (.sequence [
      .copyWithNewTargets (.controller .this) (.wasArgumentOfTrigger 1 1),
      .putCounter (.source .this) .plusOnePlusOne 2])).toTriggeredAbility?.isNone

#guard
  (Ability.triggered
    (.castSpell
      (.intersection [
        .spell,
        .union [.cardType .instant, .cardType .sorcery],
        .controlled (.controller .this),
        .hasTarget (.union [.cardType .artifact, .cardType .land])]))
    (.putCounter (.source .this) .plusOnePlusOne 2)).toTriggeredAbility?.isNone

-- Speed: you may pay {1}; if you do, haste-except-haste.
#guard
  match
    (Ability.triggered
      (.castSpell
        (.intersection [
          .spell,
          .not (.cardType .creature),
          .controlled (.controller .this)]))
      (.optionalPayFor
        (.controller .this)
        [.mana [.generic 1]]
        [
          .continuous
            [
              .forbid
                (.block
                  (.not (.keyword .haste))
                  (.target
                    1
                    (.intersection [
                      .permanent,
                      .cardType .creature,
                      .keyword .haste])))]
            .endOfTurn])).toTriggeredAbility? with
  | some ab => ab == TriggeredAbility.onCasting Effect.castingMayPayHasteUnblockable
  | none => false

-- Paying is required (the restrict alone is not Speed).
#guard
  (Ability.triggered
    (.castSpell
      (.intersection [
        .spell,
        .not (.cardType .creature),
        .controlled (.controller .this)]))
    (.continuous
      [
        .forbid
          (.block
            (.not (.keyword .haste))
            (.target
              1
              (.intersection [
                .permanent,
                .cardType .creature,
                .keyword .haste])))]
      .endOfTurn)).toTriggeredAbility?.isNone

-- An opponent paying is not you.
#guard
  (Ability.triggered
    (.castSpell
      (.intersection [
        .spell,
        .not (.cardType .creature),
        .controlled (.controller .this)]))
    (.optionalPayFor
      (.opponent (.controller .this))
      [.mana [.generic 1]]
      [
        .continuous
          [
            .forbid
              (.block
                (.not (.keyword .haste))
                (.target
                  1
                  (.intersection [
                    .permanent,
                    .cardType .creature,
                    .keyword .haste])))]
          .endOfTurn])).toTriggeredAbility?.isNone

-- {2} is not {1}.
#guard
  (Ability.triggered
    (.castSpell
      (.intersection [
        .spell,
        .not (.cardType .creature),
        .controlled (.controller .this)]))
    (.optionalPayFor
      (.controller .this)
      [.mana [.generic 2]]
      [
        .continuous
          [
            .forbid
              (.block
                (.not (.keyword .haste))
                (.target
                  1
                  (.intersection [
                    .permanent,
                    .cardType .creature,
                    .keyword .haste])))]
          .endOfTurn])).toTriggeredAbility?.isNone

-- Drawing if paid is not the haste restrict.
#guard
  (Ability.triggered
    (.castSpell
      (.intersection [
        .spell,
        .not (.cardType .creature),
        .controlled (.controller .this)]))
    (.optionalPayFor
      (.controller .this)
      [.mana [.generic 1]]
      [.draw (.controller .this) 1])).toTriggeredAbility?.isNone

-- Bullseye: discard a nonland card, not any card.
#guard
  let sacArt : Cost :=
    .sacrificeCount
      (.intersection [
        .permanent,
        .cardType .artifact,
        .controlled (.controller .this)])
      1
  match
    (Ability.triggered
      (.enter .this)
      (.optionalPayFor
        (.controller .this)
        [.or [sacArt, .discard (.not (.cardType .land))]]
        [.dealDamage .this (.target 2 .all) (.nat 2)])).toTriggeredAbility? with
  | some ab => ab == TriggeredAbility.onEnter Effect.enterMaySacOrDiscardNonlandThenDamage
  | none => false

#guard
  let sacArt : Cost :=
    .sacrificeCount
      (.intersection [
        .permanent,
        .cardType .artifact,
        .controlled (.controller .this)])
      1
  (Ability.triggered
    (.enter .this)
    (.optionalPayFor
      (.controller .this)
      [.or [sacArt, .discard .all]]
      [.dealDamage .this (.target 2 .all) (.nat 2)])).toTriggeredAbility?.isNone

#guard
  let sacArt : Cost :=
    .sacrificeCount
      (.intersection [
        .permanent,
        .cardType .artifact,
        .controlled (.controller .this)])
      1
  match
    (Ability.activated
      [.mana [.generic 3], .tapSymbol, .or [sacArt, .discard (.not (.cardType .land))]]
      (.dealDamage .this (.target 1 .all) (.nat 2))).toActivatedAbility? with
  | some ab => ab.cost.sacrificeArtifactOrDiscardNonland
  | none => false

#guard
  let sacArt : Cost :=
    .sacrificeCount
      (.intersection [
        .permanent,
        .cardType .artifact,
        .controlled (.controller .this)])
      1
  match
    (Ability.activated
      [.mana [.generic 3], .tapSymbol, .or [sacArt, .discard .all]]
      (.dealDamage .this (.target 1 .all) (.nat 2))).toActivatedAbility? with
  | some ab => !ab.cost.sacrificeArtifactOrDiscardNonland
  | none => false

#guard
  (TraditionalCardDefinition.card [
    .ability
      (.static
        (.forbid
          (.or
            (.attack
              (.intersection [.permanent, .cardType .creature, .keyword .flying])
              (.controller .this))
            (.block
              (.intersection [.permanent, .cardType .creature, .keyword .flying])
              (.intersection [
                .permanent,
                .cardType .creature,
                .controlled (.controller .this)])))))
  ]).toCardDef.staticAbilities == #[.flyingCantAttackYouOrBlockYours]

-- Storm: a spell that hasTarget a creature; those creatures (targets of
-- this spell) gain flying.
#guard
  match
    (Ability.triggered
      (.triggerId 1
        (.castSpell
          (.intersection [
            .spell,
            .controlled (.controller .this),
            .hasTarget
              (.intersection [
                .permanent,
                .cardType .creature])])))
      (.continuous
        [
          .gainAbility
            (.intersection [
              .permanent,
              .cardType .creature,
              .isTargetOf (.wasArgumentOfTrigger 1 1)])
            (.keyword .flying)]
        .endOfTurn)).toTriggeredAbility? with
  | some ab => ab == TriggeredAbility.onCasting Effect.castingTargetsGainFlying
  | none => false

#guard
  (Ability.triggered
    (.castSpell (.intersection [.spell, .controlled (.controller .this)]))
    (.if
      (.targetsIncludeAny
        .this
        (.intersection [.permanent, .cardType .creature]))
      [
        .continuous
          [
            .gainAbility
              (.intersection [.permanent, .cardType .creature])
              (.keyword .flying)]
          .endOfTurn])).toTriggeredAbility?.isNone

#guard
  (Ability.triggered
    (.triggerId 1
      (.castSpell
        (.intersection [
          .spell,
          .controlled (.controller .this),
          .hasTarget
            (.intersection [
              .permanent,
              .cardType .creature])])))
    (.continuous
      [
        .gainAbility
          (.intersection [
            .permanent,
            .cardType .creature,
            (.wasArgumentOfTrigger 1 1)])
          (.keyword .flying)]
      .endOfTurn)).toTriggeredAbility?.isNone

#guard
  (Ability.triggered
    (.castSpell
      (.intersection [
        .spell,
        .controlled (.controller .this),
        .hasTarget
          (.intersection [
            .permanent,
            .cardType .creature])]))
    (.continuous
      [
        .gainAbility
          (.intersection [.permanent, .cardType .creature])
          (.keyword .flying)]
      .endOfTurn)).toTriggeredAbility?.isNone

#guard
  (Ability.triggered
    (.triggerId 1
      (.castSpell
        (.intersection [
          .spell,
          .controlled (.controller .this)])))
    (.continuous
      [
        .gainAbility
          (.intersection [
            .permanent,
            .cardType .creature,
            .isTargetOf (.wasArgumentOfTrigger 1 1)])
          (.keyword .flying)]
      .endOfTurn)).toTriggeredAbility?.isNone

#guard
  (Ability.triggered
    (.triggerId 1
      (.castSpell
        (.intersection [
          .spell,
          .controlled (.controller .this),
          .hasTarget
            (.intersection [
              .permanent,
              .cardType .artifact])])))
    (.continuous
      [
        .gainAbility
          (.intersection [
            .permanent,
            .cardType .creature,
            .isTargetOf (.wasArgumentOfTrigger 1 1)])
          (.keyword .flying)]
      .endOfTurn)).toTriggeredAbility?.isNone

-- Attack-only is not enough (Storm also forbids blocking).
#guard
  (TraditionalCardDefinition.card [
    .ability
      (.static
        (.forbid
          (.attack
            (.intersection [.permanent, .cardType .creature, .keyword .flying])
            (.controller .this))))
  ]).toCardDef.staticAbilities == #[]

-- Blocking-only is not enough (Storm also forbids attacking).
#guard
  (TraditionalCardDefinition.card [
    .ability
      (.static
        (.forbid
          (.block
            (.intersection [.permanent, .cardType .creature, .keyword .flying])
            (.intersection [
              .permanent,
              .cardType .creature,
              .controlled (.controller .this)]))))
  ]).toCardDef.staticAbilities == #[]

-- Wolverine: heal all damage on this, then keep the replaced damage event.
#guard
  (TraditionalCardDefinition.card [
    .ability
      (.static
        (.replace
          (.damage .all .this)
          [.healAllDamage .this, .keepReplacedAction]))
  ]).toCardDef.staticAbilities == #[.healOtherDamageWhenDealt]

-- An empty replacement prevents the damage instead of healing it.
#guard
  (TraditionalCardDefinition.card [
    .ability (.static (.replace (.damage .all .this) []))
  ]).toCardDef.staticAbilities == #[.preventAllDamageToThis]

#guard
  (TraditionalCardDefinition.card [
    .ability
      (.static
        (.replace
          (.damage .all .this)
          [.keepReplacedAction]))
  ]).toCardDef.staticAbilities == #[]

#guard
  (TraditionalCardDefinition.card [
    .ability
      (.static
        (.replace
          (.damage .all .this)
          [.healAllDamage .this]))
  ]).toCardDef.staticAbilities == #[]

#guard
  (TraditionalCardDefinition.card [
    .ability
      (.static
        (.replace
          (.damage .all .this)
          [.keepReplacedAction, .healAllDamage .this]))
  ]).toCardDef.staticAbilities == #[]

#guard
  (TraditionalCardDefinition.card [
    .ability
      (.static
        (.replace
          (.combatDamage .all .this)
          [.healAllDamage .this, .keepReplacedAction]))
  ]).toCardDef.staticAbilities == #[]

-- Dwarven Mauler: Equip abilities you activate that target this cost {2} less.
#guard Selector.leftoverKeywordAbility?
  (Selector.keywordAbility .equip) == some .equip

#guard Selector.leftoverKeywordAbility? (.keyword .equip) |>.isNone

#guard
  (TraditionalCardDefinition.card [
    .ability
      (.static
        (.reduceCost
          (.intersection [
            Selector.keywordAbility .equip,
            .hasTarget .this,
            .controlled (.controller .this)])
          [.mana [.generic 2]]))
  ]).toCardDef.staticAbilities == #[.equipAbilitiesTargetingThisCostLess 2]

-- Objects with Equip are not Equip abilities.
#guard
  (TraditionalCardDefinition.card [
    .ability
      (.static
        (.reduceCost
          (.intersection [
            .keyword .equip,
            .hasTarget .this,
            .controlled (.controller .this)])
          [.mana [.generic 2]]))
  ]).toCardDef.staticAbilities == #[]

-- Missing hasTarget is not enough (must target this).
#guard
  (TraditionalCardDefinition.card [
    .ability
      (.static
        (.reduceCost
          (.intersection [
            Selector.keywordAbility .equip,
            .controlled (.controller .this)])
          [.mana [.generic 2]]))
  ]).toCardDef.staticAbilities == #[]

#guard
  (TraditionalCardDefinition.card [
    .ability
      (.static
        (.reduceCost
          (.intersection [
            Selector.keywordAbility .equip,
            .hasTarget .player,
            .controlled (.controller .this)])
          [.mana [.generic 2]]))
  ]).toCardDef.staticAbilities == #[]

-- Missing you-activate is not enough.
#guard
  (TraditionalCardDefinition.card [
    .ability
      (.static
        (.reduceCost
          (.intersection [
            Selector.keywordAbility .equip,
            .hasTarget .this])
          [.mana [.generic 2]]))
  ]).toCardDef.staticAbilities == #[]

#guard
  (TraditionalCardDefinition.card [
    .ability
      (.static
        (.reduceCost
          (.intersection [
            Selector.keywordAbility .flying,
            .hasTarget .this,
            .controlled (.controller .this)])
          [.mana [.generic 2]]))
  ]).toCardDef.staticAbilities == #[]

-- Reducing this object's costs is not Equip-targeting-this.
#guard
  (TraditionalCardDefinition.card [
    .ability (.static (.reduceCost .this [.mana [.generic 2]]))
  ]).toCardDef.staticAbilities == #[]

-- Along the Crooked Way: creature card leaves your graveyard, amass Goblins.
#guard
  match
    (Ability.triggered
      (.leaveGraveyard
        (.intersection [
          .inGraveyard,
          .cardType .creature,
          .owner (.controller .this)]))
      (.keyword (.controller .this) (.amass .goblin (.nat 1)))).toTriggeredAbility? with
  | some ab => ab == TriggeredAbility.onCreatureCardLeavesYourGyAmassGoblins 1
  | none => false

-- Opponent's graveyard is not yours.
#guard
  (Ability.triggered
    (.leaveGraveyard
      (.intersection [
        .inGraveyard,
        .cardType .creature,
        .owner (.opponent (.controller .this))]))
    (.keyword (.controller .this) (.amass .goblin (.nat 1)))).toTriggeredAbility?.isNone

-- Instant cards leaving the graveyard are not creature cards.
#guard
  (Ability.triggered
    (.leaveGraveyard
      (.intersection [
        .inGraveyard,
        .cardType .instant,
        .owner (.controller .this)]))
    (.keyword (.controller .this) (.amass .goblin (.nat 1)))).toTriggeredAbility?.isNone

-- Enter: return target creature card from your graveyard.
#guard
  match
    (Ability.triggered
      (.enter .this)
      (.returnToHand
        (.target
          1
          (.intersection [
            .inGraveyard,
            .cardType .creature,
            .owner (.controller .this)])))).toTriggeredAbility? with
  | some ab => ab == TriggeredAbility.onEnterReturnCreatureFromGyToHand
  | none => false

-- Up-to-one is not a required target creature card.
#guard
  (Ability.triggered
    (.enter .this)
    (.returnToHand
      (.targets
        1
        (.range 0 1)
        (.intersection [
          .inGraveyard,
          .cardType .creature,
          .owner (.controller .this)])))).toTriggeredAbility?.isNone

-- Goblins and Orcs you control gain menace.
#guard
  CardAction.toAbilityEffect
    (.continuous
      [.gainAbility
        (.intersection [
          .permanent,
          .union [.subtype .goblin, .subtype .orc],
          .controlled (.controller .this)])
        (.keyword .menace)]
      .endOfTurn) ==
  Effect.subtypesGainMenace #["Goblin", "Orc"]

-- Flying instead of menace is not subtypesGainMenace.
#guard
  CardAction.toAbilityEffect
    (.continuous
      [.gainAbility
        (.intersection [
          .permanent,
          .union [.subtype .goblin, .subtype .orc],
          .controlled (.controller .this)])
        (.keyword .flying)]
      .endOfTurn) !=
  Effect.subtypesGainMenace #["Goblin", "Orc"]

-- Opponent's Goblins and Orcs are not yours.
#guard
  CardAction.toAbilityEffect
    (.continuous
      [.gainAbility
        (.intersection [
          .permanent,
          .union [.subtype .goblin, .subtype .orc],
          .controlled (.opponent (.controller .this))])
        (.keyword .menace)]
      .endOfTurn) !=
  Effect.subtypesGainMenace #["Goblin", "Orc"]

-- Creatures you control (no subtype) still leftover to teamGain.
#guard
  CardAction.toAbilityEffect
    (.continuous
      [.gainAbility
        (.intersection [
          .permanent,
          .cardType .creature,
          .controlled (.controller .this)])
        (.keyword .menace)]
      .endOfTurn) ==
  Effect.teamGain Keyword.menace.toKeywords

-- Armor Wars I: you may draw per artifact; if you do, each opponent draws.
#guard
  CardAction.leftoverMayDrawPerArtifactOppsDraw?
    (.optional (.controller .this)
      (.sequence [
        .forEachVariable 1
          (.intersection [
            .permanent,
            .cardType .artifact,
            .controlled (.controller .this)])
          [.draw (.controller .this) 1],
        .draw (.opponent (.controller .this)) 1
      ]))

-- Not optional is not enough.
#guard
  !CardAction.leftoverMayDrawPerArtifactOppsDraw?
    (.sequence [
      .forEachVariable 1
        (.intersection [
          .permanent,
          .cardType .artifact,
          .controlled (.controller .this)])
        [.draw (.controller .this) 1],
      .draw (.opponent (.controller .this)) 1
    ])

-- Creatures you control are not artifacts.
#guard
  !CardAction.leftoverMayDrawPerArtifactOppsDraw?
    (.optional (.controller .this)
      (.sequence [
        .forEachVariable 1
          (.intersection [
            .permanent,
            .cardType .creature,
            .controlled (.controller .this)])
          [.draw (.controller .this) 1],
        .draw (.opponent (.controller .this)) 1
      ]))

-- Missing opponent draw is not enough.
#guard
  !CardAction.leftoverMayDrawPerArtifactOppsDraw?
    (.optional (.controller .this)
      (.forEachVariable 1
        (.intersection [
          .permanent,
          .cardType .artifact,
          .controlled (.controller .this)])
        [.draw (.controller .this) 1]))

-- Each player drawing is not each opponent.
#guard
  !CardAction.leftoverMayDrawPerArtifactOppsDraw?
    (.optional (.controller .this)
      (.sequence [
        .forEachVariable 1
          (.intersection [
            .permanent,
            .cardType .artifact,
            .controlled (.controller .this)])
          [.draw (.controller .this) 1],
        .draw .player 1
      ]))

-- Armor Wars II: artifact spells you cast this turn cost {1} less.
#guard
  CardAction.leftoverArtifactSpellsCostLessThisTurn?
    (.continuous
      [
        .reduceCost
          (.intersection [
            .spell,
            .cardType .artifact,
            .controlled (.controller .this)])
          [.mana [.generic 1]]
      ]
      .endOfTurn) == some 1

-- Lasting cost reduction is not this turn.
#guard
  CardAction.leftoverArtifactSpellsCostLessThisTurn?
    (.continuous
      [
        .reduceCost
          (.intersection [
            .spell,
            .cardType .artifact,
            .controlled (.controller .this)])
          [.mana [.generic 1]]
      ]
      .endOfGame) |>.isNone

-- Creature spells are not artifact spells.
#guard
  CardAction.leftoverArtifactSpellsCostLessThisTurn?
    (.continuous
      [
        .reduceCost
          (.intersection [
            .spell,
            .cardType .creature,
            .controlled (.controller .this)])
          [.mana [.generic 1]]
      ]
      .endOfTurn) |>.isNone

-- Artifact permanents are not artifact spells.
#guard
  CardAction.leftoverArtifactSpellsCostLessThisTurn?
    (.continuous
      [
        .reduceCost
          (.intersection [
            .permanent,
            .cardType .artifact,
            .controlled (.controller .this)])
          [.mana [.generic 1]]
      ]
      .endOfTurn) |>.isNone

-- Armor Wars III: this deals X to target opponent, X = greatest artifact MV.
#guard
  CardAction.leftoverChapterDealXDamageToTargetOpponentGreatestArtifactMv?
    (.dealDamage
      .this
      (.target 1 (.opponent (.controller .this)))
      (.greatestManaValue
        (.intersection [
          .permanent,
          .cardType .artifact,
          .controlled (.controller .this)])))

-- Target player is not target opponent.
#guard
  !CardAction.leftoverChapterDealXDamageToTargetOpponentGreatestArtifactMv?
    (.dealDamage
      .this
      (.target 1 .player)
      (.greatestManaValue
        (.intersection [
          .permanent,
          .cardType .artifact,
          .controlled (.controller .this)])))

-- Greatest mana value among creatures is not artifacts.
#guard
  !CardAction.leftoverChapterDealXDamageToTargetOpponentGreatestArtifactMv?
    (.dealDamage
      .this
      (.target 1 (.opponent (.controller .this)))
      (.greatestManaValue
        (.intersection [
          .permanent,
          .cardType .creature,
          .controlled (.controller .this)])))

-- Literal damage is not computed greatest-mana-value damage.
#guard
  !CardAction.leftoverChapterDealXDamageToTargetOpponentGreatestArtifactMv?
    (.dealDamage .this (.target 1 (.opponent (.controller .this))) (.nat 3))

#guard
  CardAction.leftoverChapterEffect?
    [
      .optional (.controller .this)
        (.sequence [
          .forEachVariable 1
            (.intersection [
              .permanent,
              .cardType .artifact,
              .controlled (.controller .this)])
            [.draw (.controller .this) 1],
          .draw (.opponent (.controller .this)) 1
        ])
    ] == some Effect.mayDrawPerArtifactOppsDraw

#guard
  CardAction.leftoverChapterEffect?
    [
      .continuous
        [
          .reduceCost
            (.intersection [
              .spell,
              .cardType .artifact,
              .controlled (.controller .this)])
            [.mana [.generic 1]]
        ]
        .endOfTurn
    ] == some (Effect.artifactSpellsCostLessThisTurn 1)

#guard
  CardAction.leftoverChapterEffect?
    [
      .dealDamage
        .this
        (.target 1 (.opponent (.controller .this)))
        (.greatestManaValue
          (.intersection [
            .permanent,
            .cardType .artifact,
            .controlled (.controller .this)]))
    ] == some Effect.chapterDealXDamageToTargetOpponentGreatestArtifactMv

-- Armor Wars chapters compile to a three-chapter Saga sacrificed after III.
#guard
  match
    (TraditionalCardDefinition.card [
      .subtype .saga,
      .ability
        (.keywordWithEffect
          (.chapter 1)
          [
            .optional (.controller .this)
              (.sequence [
                .forEachVariable 1
                  (.intersection [
                    .permanent,
                    .cardType .artifact,
                    .controlled (.controller .this)])
                  [.draw (.controller .this) 1],
                .draw (.opponent (.controller .this)) 1
              ])
          ]),
      .ability
        (.keywordWithEffect
          (.chapter 2)
          [
            .continuous
              [
                .reduceCost
                  (.intersection [
                    .spell,
                    .cardType .artifact,
                    .controlled (.controller .this)])
                  [.mana [.generic 1]]
              ]
              .endOfTurn
          ]),
      .ability
        (.keywordWithEffect
          (.chapter 3)
          [
            .dealDamage
              .this
              (.target 1 (.opponent (.controller .this)))
              (.greatestManaValue
                (.intersection [
                  .permanent,
                  .cardType .artifact,
                  .controlled (.controller .this)]))
          ])
    ]).toCardDef.saga with
  | some s =>
    s.sacrificeAfter == "III" && s.chapters.size == 3 &&
      s.chapters[0]!.roman == "I" &&
      s.chapters[1]!.roman == "II" &&
      s.chapters[2]!.roman == "III" &&
      s.chapters[2]!.chapterEffect ==
        some Effect.chapterDealXDamageToTargetOpponentGreatestArtifactMv
  | none => false

-- Uncompiled chapter actions do not produce a Saga.
#guard
  (TraditionalCardDefinition.card [
    .subtype .saga,
    .ability (.keywordWithEffect (.chapter 1) [.draw (.controller .this) 1])
  ]).toCardDef.saga.isNone

-- The Mountain-king's Return: recruit, a graveyard creature of mana value
-- at most N, and one +1/+1 counter on up to one target creature.
#guard
  CardAction.leftoverChapterEffect?
    [.keyword (.controller .this) .recruit] == some Effect.chapterRecruit

#guard
  CardAction.leftoverChapterEffect?
    [.keyword .all .recruit] |>.isNone

#guard
  CardAction.leftoverChapterEffect?
    [.putOntoBattlefield
      (.target 1
        (.intersection [
          .inGraveyard,
          .cardType .creature,
          .owner (.controller .this),
          .manaValueAtMost (.nat 3)]))] ==
    some (Effect.chapterReturnCreatureFromGyMvAtMost 3)

#guard
  CardAction.leftoverChapterEffect?
    [.putOntoBattlefield
      (.target 1
        (.intersection [
          .inGraveyard,
          .cardType .creature,
          .owner (.controller .this),
          .manaValueAtMost (.nat 0)]))] |>.isNone

#guard
  CardAction.leftoverChapterEffect?
    [.putCounter
      (.targets 1 (.range 0 1)
        (.intersection [.permanent, .cardType .creature]))
      .plusOnePlusOne
      1] == some Effect.chapterPlusOneUpToOne

#guard
  CardAction.leftoverChapterEffect?
    [.putCounter
      (.targets 1 (.range 0 1)
        (.intersection [
          .permanent, .cardType .creature, .controlled (.controller .this)]))
      .plusOnePlusOne
      1] |>.isNone

-- Equipped creature has hexproof and can't be blocked.
#guard
  (TraditionalCardDefinition.card [
    .ability (.static (.gainAbility (.hostOf .this) (.keyword .hexproof))),
    .ability (.static (.forbid (.block .any (.hostOf .this))))
  ]).toCardDef.staticAbilities ==
    #[.equippedCreatureHasKeywordsAndCantBeBlocked Keyword.hexproof]

-- Hexproof without the restriction stays keywords only.
#guard
  (TraditionalCardDefinition.card [
    .ability (.static (.gainAbility (.hostOf .this) (.keyword .hexproof)))
  ]).toCardDef.staticAbilities == #[.equippedCreatureHasKeywords Keyword.hexproof]

-- Alternative cost of {0} for Equip abilities you control, only before
-- you have activated one this turn.
#guard
  (TraditionalCardDefinition.card [
    .ability (.static (.if
      (.and
        (.enduringStory (.controller .this))
        (.didNotHappen
          (.activateAbility
            (.intersection [
              Selector.keywordAbility .equip,
              .controlled (.controller .this)]))
          .turnStart))
      [.alternativeCost
        (.intersection [
          Selector.keywordAbility .equip,
          .controlled (.controller .this)])
        [.mana [.generic 0]]]))
  ]).toCardDef.staticAbilities == #[.firstEquipFreeIfEnduringStory]

-- Without the turn-start check, the alternative cost is not that ability.
#guard
  (TraditionalCardDefinition.card [
    .ability (.static (.if (.enduringStory (.controller .this))
      [.alternativeCost
        (.intersection [
          Selector.keywordAbility .equip,
          .controlled (.controller .this)])
        [.mana [.generic 0]]]))
  ]).toCardDef.staticAbilities == #[]

-- Reducing that cost, or an alternative cost other than {0}, is different.
#guard
  (TraditionalCardDefinition.card [
    .ability (.static (.if (.enduringStory (.controller .this))
      [.reduceCost
        (.intersection [
          Selector.keywordAbility .equip,
          .controlled (.controller .this)])
        [.mana [.generic 0]]]))
  ]).toCardDef.staticAbilities == #[]

#guard
  (TraditionalCardDefinition.card [
    .ability (.static (.if (.enduringStory (.controller .this))
      [.alternativeCost
        (.intersection [
          Selector.keywordAbility .equip,
          .controlled (.controller .this)])
        [.mana [.generic 1]]]))
  ]).toCardDef.staticAbilities == #[]

-- Landfall may set this creature's base power and toughness.
#guard
  (Ability.triggered
    (.enter
      (.intersection [
        .permanent, .cardType .land, .controlled (.controller .this)]))
    (.optional (.controller .this) (.continuous
      [.setBasePower (.source .this) (Value.int 4),
        .setBaseToughness (.source .this) (Value.int 2)]
      .endOfTurn))).toTriggeredAbility? ==
    some (TriggeredAbility.onLandYouControlEntersBecomePT 4 2)

-- Another Dwarf or Equipment you control entering draws once each turn.
#guard
  (Ability.triggered
    (.enter
      (.intersection [
        .not .this,
        .permanent,
        .union [.subtype .dwarf, .subtype .equipment],
        .controlled (.controller .this)]))
    (.draw (.controller .this) 1)).toTriggeredAbility? ==
    some (TriggeredAbility.onAnotherSubtypeOrEquipmentEntersDrawOnce "Dwarf")

-- Sacrifice a creature is its own additional cost.
#guard
  let c :=
    (TraditionalCardDefinition.card [
      .ability (.stackStatic (.additionalCost .this
        [.sacrificeCount
          (.intersection [.permanent, .cardType .creature]) 1])),
      .actions [.draw (.controller .this) 2]
    ]).toCardDef
  c.additionalCostSacrificeCreature &&
    !c.additionalCostSacrificeArtifactOrCreature &&
    c.spellEffect == some (Effect.draw 2)

-- That cost on an Adventure face stays on the Adventure.
#guard
  let c :=
    (TraditionalCardDefinition.card [
      .name "My Precious",
      .alternative [
        .name "Allure of Power",
        .type .instant,
        .ability (.stackStatic (.additionalCost .this
          [.sacrificeCount
            (.intersection [.permanent, .cardType .creature]) 1])),
        .actions [.draw (.controller .this) 2]]
    ]).toCardDef
  !c.additionalCostSacrificeCreature &&
    match c.adventure with
    | some a =>
      a.additionalCostSacrificeCreature &&
        a.spellEffect == some (Effect.draw 2) &&
        a.name == "Allure of Power"
    | none => false

-- Bard, King of Dale: a draw outside the first of your draw step becomes two,
-- and tokens you would create are doubled.
#guard
  let c :=
    (TraditionalCardDefinition.card [
      .ability (.static (.if
        (notFirstCardOfDrawStep (.controller .this))
        [.replace
          (.draw (.controller .this) .all)
          [.draw (.controller .this) 2]])),
      .ability (.static (.replace
        (.createTokens (.intersection [.token, .controlled (.controller .this)]))
        [.modifyReplacementCreatedTokenCount (fun n => .nat (n * 2))]))
    ]).toCardDef
  c.drawTwoExceptFirstDrawStep && c.tokenDoubling

#guard
  let c :=
    (TraditionalCardDefinition.card [
      .ability (.static (.replace
        (.createTokens (.intersection [.token, .controlled (.controller .this)]))
        [.modifyReplacementCreatedTokenCount (fun n => .nat (n * 3))]))
    ]).toCardDef
  !c.tokenDoubling

#guard
  let c :=
    (TraditionalCardDefinition.card [
      .ability (.static (.replace
        (.draw (.controller .this) .all)
        [.draw (.controller .this) 2]))
    ]).toCardDef
  !c.drawTwoExceptFirstDrawStep

#guard
  let c :=
    (TraditionalCardDefinition.card [
      .ability (.static (.replace
        (.draw (.controller .this) .all)
        [.draw (.controller .this) 3]))
    ]).toCardDef
  !c.drawTwoExceptFirstDrawStep && !c.tokenDoubling

-- Belladonna Took: the first three resolutions this turn are life, a card,
-- then a +1/+1 counter on each creature you control.
#guard
  let c :=
    (TraditionalCardDefinition.card [
      .ability (.abilityId 1 (.triggered
        (.enter (.intersection [.permanent, .token, .controlled (.controller .this)]))
        (.sequence [
          .if (.and
              (.happened (.ordinal 1 .turnStart (.abilityWithIdResolved 1)) .turnStart)
              (.didNotHappen (.ordinal 2 .turnStart (.abilityWithIdResolved 1)) .turnStart))
            [.gainLife (.controller .this) 1],
          .if (.and
              (.happened (.ordinal 2 .turnStart (.abilityWithIdResolved 1)) .turnStart)
              (.didNotHappen (.ordinal 3 .turnStart (.abilityWithIdResolved 1)) .turnStart))
            [.draw (.controller .this) 1],
          .if (.and
              (.happened (.ordinal 3 .turnStart (.abilityWithIdResolved 1)) .turnStart)
              (.didNotHappen (.ordinal 4 .turnStart (.abilityWithIdResolved 1)) .turnStart))
            [.putCounter
              (.intersection
                [.permanent, .cardType .creature, .controlled (.controller .this)])
              .plusOnePlusOne 1]])))
    ]).toCardDef
  c.triggeredAbilities == #[.onTokenYouControlEntersBelladonna]

#guard
  (Ability.triggered
    (.enter (.intersection [.permanent, .token, .controlled (.controller .this)]))
    (.if (.and
        (.happened (.ordinal 1 .turnStart (.abilityWithIdResolved 1)) .turnStart)
        (.didNotHappen (.ordinal 2 .turnStart (.abilityWithIdResolved 1)) .turnStart))
      [.gainLife (.controller .this) 1])).toTriggeredAbility?.isNone

end Mtg.Engine
