import Mtg.Engine.Card.OracleParse.Parse

/-!
# `parseOracleParts` guards

Regression tests for recognized Oracle text, in the order they were added.
`GuardsLines` and `GuardsCatalog` continue this file. Add a new guard at the
end of `GuardsCatalog`.
-/

namespace Mtg.Engine

open OracleParts

#guard parseOracleParts (name := "") "Lifelink" == some [.ability (.keyword .lifelink)]
#guard parseOracleParts (name := "") "Flying, deathtouch" ==
  some [.ability (.keyword .flying), .ability (.keyword .deathtouch)]
#guard parseOracleParts (name := "")
  "Reach (This creature can block creatures with flying.)" ==
  some [.ability (.keyword .reach)]
#guard parseOracleParts (name := "") "Whenever this creature attacks, draw a card." ==
  some [.ability
     (.triggered
       (.attack .this .all)
       (.draw (.controller .this) (.nat 1)))]
#guard parseOracleParts (name := "") "When another creature enters, draw a card." ==
  some [.ability
     (.triggered
       (.enter
         (.intersection
           [.not .this,
            .permanent,
            .cardType .creature]))
       (.draw (.controller .this) (.nat 1)))]
#guard parseOracleParts (name := "") "When Bilbo Baggins enters, draw a card." == none
#guard parseOracleParts (name := "Gandalf") "When Bilbo Baggins enters, draw a card." == none
#guard parseOracleParts (name := "Bilbo") "When Bilbo Baggins enters, draw a card." == none
#guard parseOracleParts (name := "Bilbo Baggins, Burglar")
    "When Bilbo Baggins enters, draw a card." ==
  some [.ability (.triggered (.enter .this) (.draw (.controller .this) 1))]
#guard parseOracleParts (name := "Bilbo Baggins, Burglar")
    "When Bilbo Baggins, Burglar enters, draw a card." ==
  some [.ability (.triggered (.enter .this) (.draw (.controller .this) 1))]
#guard parseOracleParts (name := "") "When this creature enters, draw two cards." ==
  some [.ability (.triggered (.enter .this) (.draw (.controller .this) 2))]
#guard parseOracleParts (name := "")
  "Whenever you draw your second card each turn, draw a card." ==
  some [.ability
     (.triggered
       (.ordinal
         2
         .turnStart
         (.draw (.controller .this) .all))
       (.draw (.controller .this) (.nat 1)))]
#guard parseOracleParts (name := "")
  "Whenever you draw your second card each turn, put a +1/+1 counter on target creature." ==
  some [.ability
     (.triggered
       (.ordinal
         2
         .turnStart
         (.draw (.controller .this) .all))
       (.putCounter
         (.target
           1
           (.intersection
             [.permanent, .cardType .creature]))
         .plusOnePlusOne
         1))]
#guard parseOracleParts (name := "Lakeshore Apothecary")
  "Whenever you draw your second card each turn, put a +1/+1 counter on this creature." ==
  some [.ability (
    .triggered
      (.ordinal 2 .turnStart (.draw (.controller .this) .all))
      (.putCounter (.source .this) .plusOnePlusOne 1))]
#guard parseOracleParts (name := "")
  "Whenever you draw a card, draw a card." ==
  some [.ability (
    .triggered (.draw (.controller .this) .all) (.draw (.controller .this) (.nat 1)))]
#guard parseOracleParts (name := "")
  "Whenever you draw a card, put a +1/+1 counter on target creature." ==
  some [.ability (
    .triggered (.draw (.controller .this) .all)
      (.putCounter (.target 1 (.intersection [.permanent, .cardType .creature])) .plusOnePlusOne 1))]
#guard parseOracleParts (name := "")
  "Whenever you draw a card, if you control another Hero, put a +1/+1 counter on this creature." == none
#guard parseOracleParts (name := "Ravenhill Flock")
  "Whenever you draw a card, put a +1/+1 counter on this creature." ==
  some [.ability (
    .triggered
      (.draw (.controller .this) .all)
      (.putCounter (.source .this) .plusOnePlusOne 1))]
#guard parseOracleParts (name := "Ravenhill Flock")
  "Flying\nWhenever you draw a card, put a +1/+1 counter on this creature." ==
  some [
    .ability (.keyword .flying),
    .ability (
      .triggered
        (.draw (.controller .this) .all)
        (.putCounter (.source .this) .plusOnePlusOne 1))]
#guard parseOracleParts (name := "Brave Brawler") (manaCost := [.generic 1, .mono .white])
  "Power-up — {4}{W}: Put two +1/+1 counters on this creature. (Activate each power-up ability only once. Reduce the cost by its mana cost if it entered this turn.)" ==
  some [.ability (
    .abilityId 1
      (.activatedWithStaticIf
        (.didNotHappen (.abilityWithIdActivated 1) .gameStart)
        [.mana [.generic 4, .mono .white]]
        (.putCounter (.source .this) .plusOnePlusOne 2)
        (.if (.happened (.enter (.source .this)) .turnStart)
          [.reduceCost .this [.mana [.generic 1, .mono .white]]])))]
#guard parseOracleParts (name := "Brave Brawler")
  "Power-up — {4}{W}: Put two +1/+1 counters on this creature. (Activate each power-up ability only once. Reduce the cost by its mana cost if it entered this turn.)" ==
  none
#guard parseOracleParts (name := "Hercules, Prince of Power") (manaCost := [.generic 2, .mono .green])
  "Power-up — {4}{G}: Put a +1/+1 counter on Hercules. He gains vigilance, indestructible, and haste until end of turn. (Activate each power-up ability only once. Reduce the cost by his mana cost if he entered this turn.)" ==
  some [.ability (
    .abilityId 1
      (.activatedWithStaticIf
        (.didNotHappen (.abilityWithIdActivated 1) .gameStart)
        [.mana [.generic 4, .mono .green]]
        (.sequence [
          .putCounter (.source .this) .plusOnePlusOne 1,
          .continuous [
            .gainAbility (.source .this) (.keyword .vigilance),
            .gainAbility (.source .this) (.keyword .indestructible),
            .gainAbility (.source .this) (.keyword .haste)]
            .endOfTurn])
        (.if (.happened (.enter (.source .this)) .turnStart)
          [.reduceCost .this [.mana [.generic 2, .mono .green]]])))]
#guard parseOracleParts (name := "Human Torch, Johnny Storm")
  "Whenever you draw a card, if you control another Hero, Human Torch deals 1 damage to target opponent." ==
  some [.ability (
    .triggered (.draw (.controller .this) .all)
      (.if (.any (.intersection [.not .this, .permanent, .subtype .hero, .controlled (.controller .this)]))
        [.dealDamage .this (.target 1 (.opponent (.controller .this))) (.nat 1)]))]
#guard parseOracleParts (name := "Viv Vision, Teen Synthezoid")
  "Cybernetic Senses — Whenever Viv Vision attacks, draw a card if her power is 4 or greater." ==
  some [.ability (
    .triggered (.attack .this .all)
      (.if (.any (.intersection [.source .this, .powerAtLeast (.int 4)]))
        [.draw (.controller .this) (.nat 1)]))]
#guard parseOracleParts (name := "")
  "{6}: Each opponent discards a card. Create a 2/2 colorless Robot Villain artifact creature token." ==
  some [.ability (
    .activated [.mana [.generic 6]]
      (.sequence [
        .discard (.opponent (.controller .this)) (.nat 1),
        .createTokens (.controller .this) (.nat 1)
          [.type .artifact, .type .creature, .subtype .robot, .subtype .villain,
            .colorIndicator [], .power 2, .toughness 2]
          []]))]
#guard parseOracleParts (name := "") "Scry 2." ==
  some [.actions [.scry (.controller .this) 2]]
#guard parseOracleParts (name := "")
  "Scry 2. (Then exile this card. You may cast the creature later from exile.)" ==
  some [.actions [.scry (.controller .this) 2]]
#guard parseOracleParts (name := "")
  "Target creature you control gains hexproof until end of turn." ==
  some [.actions [
    .continuous
      [.gainAbility
        (.target 1 (.intersection [
          .permanent,
          .cardType .creature,
          .controlled (.controller .this)]))
        (.keyword .hexproof)]
      .endOfTurn]]
#guard parseOracleParts (name := "")
  "{3}{W}: Creatures you control get +1/+1 until end of turn." ==
  some [.ability (
    .activated
      [.mana [.generic 3, .mono .white]]
      (.continuous
        [.addPower
          (.intersection [
            .permanent,
            .cardType .creature,
            .controlled (.controller .this)]) (Value.int 1),
         .addToughness
          (.intersection [
            .permanent,
            .cardType .creature,
            .controlled (.controller .this)]) (Value.int 1)]
        .endOfTurn))]
#guard parseOracleParts (name := "") "Tap one or two target creatures." ==
  some [.actions [
    .tap (.targets 1 (.range 1 2) (.intersection [.permanent, .cardType .creature]))]]
#guard parseOracleParts (name := "") "Tap two or one target creatures." == none
#guard parseOracleParts (name := "") "Tap 0 target creatures." == none
#guard parseOracleParts (name := "") "Tap 0 or 1 target creatures." == none
#guard parseOracleParts (name := "") "//ADV//\nSpew Flame {4}{R}\nSorcery — Adventure" ==
  some [.alternative [
    .name "Spew Flame",
    .manaCost [.generic 4, .mono .red],
    .type .sorcery,
    .subtype .adventure]]
#guard parseOracleParts (name := "")
  "This spell costs {3} less to cast if it targets a tapped creature." ==
  some [.ability (
    .stackStatic
      (.if
        (.targetsIncludeAny
          .this
          (.intersection [
            .permanent,
            .cardType .creature,
            .tapped]))
        [.reduceCost .this [.mana [.generic 3]]]))]
#guard parseOracleParts (name := "")
  "This spell costs {1} less to cast if it targets an attacking nontoken creature." ==
  some [.ability (
    .stackStatic
      (.if
        (.targetsIncludeAny
          .this
          (.intersection [
            .permanent,
            .cardType .creature,
            .attacking .all,
            .not .token]))
        [.reduceCost .this [.mana [.generic 1]]]))]
#guard parseOracleParts (name := "")
  "This spell costs {1} less to cast if it targets an attacking creature." ==
  some [.ability
     (.stackStatic
       (.if
         (.targetsIncludeAny
           .this
           (.intersection
             [.permanent,
              .cardType .creature,
              .attacking .all]))
         [.reduceCost
            .this
            [.mana [.generic 1]]]))]
#guard parseOracleParts (name := "") "Magnificent End deals 5 damage to target creature." == none
#guard parseOracleParts (name := "Shock") "Magnificent End deals 5 damage to target creature." == none
#guard parseOracleParts (name := "Magnificent End")
    "Magnificent End deals 5 damage to target creature." ==
  some [.actions [
    .dealDamage
      .this
      (.target 1 (.intersection [.permanent, .cardType .creature]))
      (.nat 5)]]
#guard parseOracleParts (name := "") "This spell deals 5 damage to target creature." ==
  some [.actions [
    .dealDamage
      .this
      (.target 1 (.intersection [.permanent, .cardType .creature]))
      (.nat 5)]]
#guard parseOracleParts (name := "") "This spell deals 0 damage to target creature." == none
#guard parseOracleParts (name := "Smaug, the Great Calamity")
    "//ADV//\nSpew Flame {4}{R}\nSorcery — Adventure\nSpew Flame deals 5 damage to target creature." ==
  some [.alternative [
    .name "Spew Flame",
    .manaCost [.generic 4, .mono .red],
    .type .sorcery,
    .subtype .adventure,
    .actions [
      .dealDamage
        .this
        (.target 1 (.intersection [.permanent, .cardType .creature]))
        (.nat 5)]]]
#guard
  let others : Selector :=
    .intersection [
      .not .this,
      .permanent,
      .cardType .creature,
      .controlled (.controller .this)]
  parseOracleParts (name := "")
    "Flying\nWhenever this creature attacks, it gets +1/+1 until end of turn for each other creature you control." ==
  some [
    .ability (.keyword .flying),
    .ability (
      .triggered
        (.attack .this .all)
        (.continuous
          [.addPower (.source .this) (Value.count others),
           .addToughness (.source .this) (Value.count others)]
          .endOfTurn))]
#guard parseOracleParts (name := "") "Untap target creature you control." ==
  some [.actions [
    .untap
      (.target
        1
        (.intersection [
          .permanent,
          .cardType .creature,
          .controlled (.controller .this)]))]]
#guard parseOracleParts (name := "")
  "Untap target creature you control. It gets +2/+2 until end of turn. If it's a Dwarf, you may attach an Equipment you control to it." ==
  some [.actions [
    .untap
      (.target
        1
        (.intersection [
          .permanent,
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
                  .permanent,
                  .subtype .equipment,
                  .controlled (.controller .this)]))
              (.targetReference 1))
        ]]]
#guard parseOracleParts (name := "Confusticate and Bebother")
  "Choose one —\n• Counter target spell unless its controller pays {4}.\n• Draw two cards, then discard a card." ==
  some [.actions [
    .chooseUniqueModes (.range 1 1) [
      .preventable (.controller (.targetReference 1)) [.mana [.generic 4]]
        (.counter (.target 1 .spell)),
      .sequence [
        .draw (.controller .this) 2,
        .discard (.controller .this) 1]]]]
#guard parseOracleParts (name := "")
  "Choose one —\n• Counter target spell unless its controller pays {4}.\n• Gain control of target creature." == none
#guard parseOracleParts (name := "")
  "Counter target spell unless its controller pays {4}." == none
#guard parseOracleParts (name := "") "" == some []
#guard parseOracleParts (name := "") "(This is reminder text.)" == some []
#guard parseOracleParts (name := "") "Lifelink\nDraw a card." ==
  some [.ability (.keyword .lifelink),
   .actions
     [.draw (.controller .this) (.nat 1)]]
#guard parseOracleParts (name := "") "Scry 2. Draw a card." ==
  some [.actions
     [.scry (.controller .this) (.nat 2),
      .draw (.controller .this) (.nat 1)]]
#guard parseOracleParts (name := "")
  "Untap target creature you control. Draw a card." ==
  some [.actions
     [.untap
        (.target
          1
          (.intersection
            [.permanent,
             .cardType .creature,
             .controlled (.controller .this)])),
      .draw (.controller .this) (.nat 1)]]
#guard parseOracleParts (name := "")
  "Flying\n//ADV//\nSpew Flame {4}{R}\nSorcery — Adventure\nDraw a card." == none
#guard parseOracleParts (name := "") "//ADV//\nSpew Flame {Z}\nSorcery — Adventure" == none
#guard parseOracleParts (name := "") "//ADV//\nSpew Flame {4}{R}\nNot a type" == none
#guard parseOracleParts (name := "")
  "Choose one —\n• Gain control of target creature.\n• Draw two cards, then discard a card." == none
#guard parseOracleParts (name := "Thranduil's Decree")
  "Counter target spell. If a permanent spell is countered this way, exile it instead of putting it into its owner's graveyard. You may cast that card without paying its mana cost for as long as it remains exiled." ==
  some [.actions [
    .actionId 1 (.counter (.target 1 .spell)),
    .continuous
      [.replace
        (.putToGraveyard (.intersection [.wasObjectOfAction 1, .permanentSpell]))
        [.actionId 2 (.exile (.replacingObject)),
          .continuous
            [.canCastWithoutPayingManaCost (.controller .this) (.wasCreatedByAction 2)]
            .endOfGame]]
      .endOfGame]]
#guard parseOracleParts (name := "") "Counter target spell." == none
#guard parseOracleParts (name := "Thranduil's Decree")
  "Counter target spell. If a permanent spell is countered this way, exile it instead of putting it into its owner's graveyard. Draw a card." == none
#guard parseOracleParts (name := "Bilbo, Luckwearer") "Bilbo can't be blocked." ==
  some [.ability (.static (.forbid (.block .any .this)))]
#guard parseOracleParts (name := "") "This creature can't be blocked." ==
  some [.ability (.static (.forbid (.block .any .this)))]
#guard parseOracleParts (name := "Gandalf") "Bilbo can't be blocked." == none
#guard parseOracleParts (name := "Bilbo, Luckwearer")
  "Bilbo can't be blocked by Goblins." == none
#guard parseOracleParts (name := "Bilbo, Luckwearer")
  "Whenever Bilbo deals combat damage to a player, draw a card, then discard a card." ==
  some [.ability (
    .triggered
      (.combatDamage .this .player)
      (.sequence [
        .draw (.controller .this) 1,
        .discard (.controller .this) 1]))]
#guard parseOracleParts (name := "Gandalf")
  "Whenever Bilbo deals combat damage to a player, draw a card, then discard a card." == none
#guard parseOracleParts (name := "Bilbo, Luckwearer")
  "Whenever Bilbo deals combat damage to a player, draw a card." ==
  some [.ability
     (.triggered
       (.combatDamage .this .player)
       (.draw (.controller .this) (.nat 1)))]
#guard parseOracleParts (name := "")
  "Exchange control of two target nonland permanents that share a card type." ==
  some [.actions [
    .exchangeControl
      (.targetSet
        1
        (.range 2 2)
        (.intersection [.permanent, .not .land])
        [.shareCardType])]]
#guard parseOracleParts (name := "")
  "Exchange control of one target nonland permanent that share a card type." == none
#guard parseOracleParts (name := "")
  "Exchange control of 0 target nonland permanents that share a card type." == none
#guard parseOracleParts (name := "")
  "Exchange control of two target creatures that share a card type." == none
#guard parseOracleParts (name := "Bilbo, Luckwearer")
  "Bilbo can't be blocked.\nWhenever Bilbo deals combat damage to a player, draw a card, then discard a card.\n//ADV//\nBurglar's Plot {4}{U}\nSorcery — Adventure\nExchange control of two target nonland permanents that share a card type. (Then exile this card. You may cast the creature later from exile.)" ==
  some [
    .ability (.static (.forbid (.block .any .this))),
    .ability (
      .triggered
        (.combatDamage .this .player)
        (.sequence [
          .draw (.controller .this) 1,
          .discard (.controller .this) 1])),
    .alternative [
      .name "Burglar's Plot",
      .manaCost [.generic 4, .mono .blue],
      .type .sorcery,
      .subtype .adventure,
      .actions [
        .exchangeControl
          (.targetSet
            1
            (.range 2 2)
            (.intersection [.permanent, .not .land])
            [.shareCardType])]]]
#guard parseOracleParts (name := "")
  "Target creature's owner puts it on their choice of the top or bottom of their library." ==
  some [.actions [
    .playerSelectAction (.owner (.targetReference 1)) (.range 1 1)
      [.putOnTopOfLibrary
        (.target 1 (.intersection [.permanent, .cardType .creature])),
        .putOnBottomOfLibrary (.targetReference 1)]]]
#guard parseOracleParts (name := "")
  "When this creature dies, target creature an opponent controls gets -1/-1 until end of turn." ==
  some [.ability (
    .triggered
      (.die .this)
      (.continuous
        [.addPower
          (.target
            1
            (.intersection [
              .permanent,
              .cardType .creature,
              .controlled (.opponent (.controller .this))])) (Value.int (-1)),
         .addToughness
          (.targetReference 1) (Value.int (-1))]
        .endOfTurn))]
#guard parseOracleParts (name := "Front Porch Sentries")
  "When Front Porch Sentries dies, target creature an opponent controls gets -1/-1 until end of turn." ==
  some [.ability (
    .triggered
      (.die .this)
      (.continuous
        [.addPower
          (.target
            1
            (.intersection [
              .permanent,
              .cardType .creature,
              .controlled (.opponent (.controller .this))])) (Value.int (-1)),
         .addToughness
          (.targetReference 1) (Value.int (-1))]
        .endOfTurn))]
#guard parseOracleParts (name := "")
  "When this creature dies, target creature an opponent controls gets +1/+1 until end of turn." ==
  some [.ability (
    .triggered
      (.die .this)
      (.continuous
        [.addPower
          (.target
            1
            (.intersection [
              .permanent,
              .cardType .creature,
              .controlled (.opponent (.controller .this))])) (Value.int 1),
         .addToughness
          (.targetReference 1) (Value.int 1)]
        .endOfTurn))]
#guard parseOracleParts (name := "Gandalf")
  "When Front Porch Sentries dies, target creature an opponent controls gets -1/-1 until end of turn." == none
#guard parseOracleParts (name := "")
  "When another creature dies, target creature an opponent controls gets -1/-1 until end of turn." == none
#guard parseOracleParts (name := "")
  "Whenever this creature dies, target creature an opponent controls gets -1/-1 until end of turn." ==
  some [.ability
     (.triggered
       (.die .this)
       (.continuous
         [.addPower
            (.target
              1
              (.intersection
                [.permanent,
                 .cardType .creature,
                 .controlled
                   (.opponent (.controller .this))]))
            (.int (-1)),
          .addToughness (.targetReference 1) (.int (-1))]
         .endOfTurn))]
#guard parseOracleParts (name := "")
  "When this creature dies, target creature you control gets -1/-1 until end of turn." ==
  some [.ability
     (.triggered
       (.die .this)
       (.continuous
         [.addPower
            (.target
              1
              (.intersection
                [.permanent,
                 .cardType .creature,
                 .controlled (.controller .this)]))
            (.int (-1)),
          .addToughness (.targetReference 1) (.int (-1))]
         .endOfTurn))]
#guard parseOracleParts (name := "")
  "When this creature dies, target creature an opponent controls gets -1/-1." == none
#guard parseOracleParts (name := "")
  "When this creature dies, draw a card." ==
  some [.ability
     (.triggered
       (.die .this)
       (.draw (.controller .this) (.nat 1)))]
#guard parseOracleParts (name := "")
  "Whenever one or more other creatures die, scry 1." ==
  some [.ability (
    .triggered
      (.dieSimultaneously (.intersection [.not .this, .permanent, .cardType .creature]) [])
      (.scry (.controller .this) 1))]
#guard parseOracleParts (name := "Great Fierce Bee")
  "Whenever one or more other creatures die, scry 1. (Look at the top card of your library. You may put that card on the bottom.)" ==
  some [.ability (
    .triggered
      (.dieSimultaneously (.intersection [.not .this, .permanent, .cardType .creature]) [])
      (.scry (.controller .this) 1))]
#guard parseOracleParts (name := "")
  "Whenever one or more other creatures die, scry 2." ==
  some [.ability (
    .triggered
      (.dieSimultaneously (.intersection [.not .this, .permanent, .cardType .creature]) [])
      (.scry (.controller .this) 2))]
#guard parseOracleParts (name := "Great Fierce Bee")
  "Flying\nWhenever one or more other creatures die, scry 1. (Look at the top card of your library. You may put that card on the bottom.)" ==
  some [
    .ability (.keyword .flying),
    .ability (
      .triggered
        (.dieSimultaneously (.intersection [.not .this, .permanent, .cardType .creature]) [])
        (.scry (.controller .this) 1))]
#guard parseOracleParts (name := "")
  "Whenever one or more creatures die, scry 1." == none
#guard parseOracleParts (name := "")
  "Whenever one or more other creatures you control die, scry 1." == none
#guard parseOracleParts (name := "")
  "When one or more other creatures die, scry 1." == none
#guard parseOracleParts (name := "")
  "Whenever another creature dies, scry 1." == none
#guard parseOracleParts (name := "")
  "Whenever one or more other creatures die, draw a card." == none
#guard parseOracleParts (name := "")
  "Whenever one or more other creatures die, scry 0." == none
#guard parseOracleParts (name := "")
  "Whenever one or more other creatures die." == none
#guard parseOracleParts (name := "")
  "Target spell's owner puts it on their choice of the top or bottom of their library." == none
#guard parseOracleParts (name := "")
  "Target creature's owner puts it on top of their library." == none
#guard parseOracleParts (name := "Uneasy Partings")
  "This spell costs {1} less to cast if it targets an attacking nontoken creature.\nTarget creature's owner puts it on their choice of the top or bottom of their library." ==
  some [
    .ability (
      .stackStatic
        (.if
          (.targetsIncludeAny
            .this
            (.intersection [
              .permanent,
              .cardType .creature,
              .attacking .all,
              .not .token]))
          [.reduceCost .this [.mana [.generic 1]]])),
    .actions [
      .playerSelectAction (.owner (.targetReference 1)) (.range 1 1)
        [.putOnTopOfLibrary
          (.target 1 (.intersection [.permanent, .cardType .creature])),
          .putOnBottomOfLibrary (.targetReference 1)]]]
#guard parseOracleParts (name := "") "Destroy target creature." ==
  some [.actions [
    .destroy (.target 1 (.intersection [.permanent, .cardType .creature]))]]
#guard parseOracleParts (name := "") "Destroy target spell." == none
#guard parseOracleParts (name := "") "Destroy target creature with flying." ==
  some [.actions [
    .destroy
      (.target 1
        (.intersection [
          .permanent,
          .cardType .creature,
          .keyword .flying]))]]
#guard parseOracleParts (name := "") "Destroy target creature with power 4 or greater." ==
  some [.actions [
    .destroy
      (.target 1
        (.intersection [
          .permanent,
          .cardType .creature,
          .powerAtLeast (Value.int 4)]))]]
#guard parseOracleParts (name := "") "Destroy target creature with power 0 or greater." == none
#guard parseOracleParts (name := "") "Destroy target creature with power 4 or less." ==
  some [.actions [
    .destroy
      (.target 1
        (.intersection [
          .permanent,
          .cardType .creature,
          .powerAtMost (Value.int 4)]))]]
#guard parseOracleParts (name := "") "Destroy target creature with power 4." == none
#guard parseOracleParts (name := "") "Destroy target creature with haste and flying." == none
#guard parseOracleParts (name := "")
  "As an additional cost to cast this spell, sacrifice an artifact or creature or pay {4}." ==
  some [.ability (.stackStatic (
    .additionalCost .this
      [.or [
        .sacrificeCount
          (.intersection [
            .permanent,
            .union [.cardType .artifact, .cardType .creature]])
          1,
        .mana [.generic 4]]]))]
#guard parseOracleParts (name := "")
  "As an additional cost to cast this spell, sacrifice an artifact or creature." ==
  some [.ability
     (.stackStatic
       (.additionalCost
         .this
         [.sacrificeCount
            (.intersection
              [.permanent,
               .union
                 [.cardType .artifact,
                  .cardType .creature]])
            1]))]
#guard parseOracleParts (name := "")
  "As an additional cost to cast this spell, sacrifice artifact or creature or pay {4}." == none
#guard parseOracleParts (name := "")
  "As an additional cost to cast this spell, discard a card or pay {4}." ==
  some [.ability (.stackStatic (.additionalCost .this [.or [
    .discard (.selected (.controller .this) (.range 1 1) (.intersection [.inHand, .owner (.controller .this)])),
    .mana [.generic 4]]]))]
#guard parseOracleParts (name := "")
  "As an additional cost to cast this spell, discard two cards or pay {4}." == none
#guard parseOracleParts (name := "")
  "As an additional cost to cast this spell, sacrifice an artifact or creature or pay {4}{B}." == none
#guard parseOracleParts (name := "Stir Up Trouble")
  "As an additional cost to cast this spell, sacrifice an artifact or creature or pay {4}.\nDestroy target creature." ==
  some [
    .ability (.stackStatic (
      .additionalCost .this
        [.or [
          .sacrificeCount
            (.intersection [
              .permanent,
              .union [.cardType .artifact, .cardType .creature]])
            1,
          .mana [.generic 4]]])),
    .actions [
      .destroy
        (.target 1 (.intersection [.permanent, .cardType .creature]))]]
#guard parseOracleParts (name := "Desolation Prowler")
  "Pay 2 life: This creature gets +2/+2 until end of turn. Activate only once each turn." ==
  some [.ability (
    .abilityId 1
      (.activatedIf
        (.didNotHappen (.abilityWithIdActivated 1) .turnStart)
        [.life 2]
        (.continuous
          [.addPower (.source .this) (Value.int 2),
           .addToughness (.source .this) (Value.int 2)]
          .endOfTurn)))]
#guard parseOracleParts (name := "")
  "Pay 2 life: This creature gets +2/+2 until end of turn." ==
  some [.ability (
    .activated
      [.life 2]
      (.continuous
        [.addPower (.source .this) (Value.int 2),
         .addToughness (.source .this) (Value.int 2)]
        .endOfTurn))]
#guard parseOracleParts (name := "")
  "Pay 2 life: This creature gets +2/+2 until end of turn. Activate only twice each turn." == none
#guard parseOracleParts (name := "")
  "Pay 0 life: This creature gets +2/+2 until end of turn." == none
#guard parseOracleParts (name := "") "Pay 2 life: Draw a card." ==
  some [.ability
     (.activated
       [.life 2]
       (.draw (.controller .this) (.nat 1)))]
#guard parseOracleParts (name := "Ravening Warg")
  "Ferocious — Whenever this creature attacks while you control a creature with power 4 or greater, you gain 2 life." ==
  some [.ability (
    .triggeredWhile
      (.attack .this .all)
      (.any
        (.intersection [
          .permanent,
          .cardType .creature,
          .controlled (.controller .this),
          .powerAtLeast (Value.int 4)]))
      (.gainLife (.controller .this) 2))]
#guard parseOracleParts (name := "Ravening Warg")
  "Whenever this creature attacks while you control a creature with power 4 or greater, you gain 2 life." ==
  parseOracleParts (name := "Ravening Warg")
    "Ferocious — Whenever this creature attacks while you control a creature with power 4 or greater, you gain 2 life."
#guard parseOracleParts (name := "")
  "Whenever this creature attacks while you control a creature with power 3 or greater, you gain 2 life." == none
#guard parseOracleParts (name := "")
  "Landfall — Whenever this creature attacks while you control a creature with power 4 or greater, you gain 2 life." == none
#guard parseOracleParts (name := "")
  "Ferocious — Whenever this creature attacks, you gain 2 life." == none
#guard parseOracleParts (name := "")
  "Put a +1/+1 counter on up to one target creature. Target player gains 2 life." ==
  some [.actions [
    .putCounter
      (.targets 1 (.range 0 1) (.intersection [.permanent, .cardType .creature]))
      .plusOnePlusOne
      1,
    .gainLife (.target 2 .player) 2]]
#guard parseOracleParts (name := "") "Put a +1/+1 counter on target creature." ==
  some [.actions
     [.putCounter
        (.target
          1
          (.intersection
            [.permanent, .cardType .creature]))
        .plusOnePlusOne
        1]]
#guard parseOracleParts (name := "")
  "Put two +1/+1 counters on up to one target creature." ==
  some [.actions
     [.putCounter
        (.targets
          1
          (.range (.nat 0) (.nat 1))
          (.intersection
            [.permanent, .cardType .creature]))
        .plusOnePlusOne
        2]]
#guard parseOracleParts (name := "") "Target opponent gains 2 life." == none
#guard parseOracleParts (name := "") "You gain 0 life." == none
#guard parseOracleParts (name := "") "You gain 2 life." ==
  some [.actions [.gainLife (.controller .this) 2]]
#guard parseOracleParts (name := "Gollum, Silent Slinker")
  "Menace (This creature can't be blocked except by two or more creatures.)\n//ADV//\nMeager Meal {B}\nSorcery — Adventure\nPut a +1/+1 counter on up to one target creature. Target player gains 2 life. (Then exile this card. You may cast the creature later from exile.)" ==
  some [
    .ability (.keyword .menace),
    .alternative [
      .name "Meager Meal",
      .manaCost [.mono .black],
      .type .sorcery,
      .subtype .adventure,
      .actions [
        .putCounter
          (.targets 1 (.range 0 1) (.intersection [.permanent, .cardType .creature]))
          .plusOnePlusOne
          1,
        .gainLife (.target 2 .player) 2]]]
#guard parseOracleParts (name := "Dreaded Bat-Cloud")
  "This spell costs {3} less to cast if a creature died this turn.\nFlying, deathtouch" ==
  some [
    .ability (
      .stackStatic
        (.if
          (.happened (.die (.cardType .creature)) .turnStart)
          [.reduceCost .this [.mana [.generic 3]]])),
    .ability (.keyword .flying),
    .ability (.keyword .deathtouch)]
#guard parseOracleParts (name := "")
  "This spell costs {3} less to cast if a creature you control died this turn." == none
#guard parseOracleParts (name := "")
  "This spell costs {3} less to cast if two creatures died this turn." == none
#guard parseOracleParts (name := "")
  "When this Equipment enters, target opponent sacrifices a creature of their choice." ==
  some [.ability (
    .triggered
      (.enter .this)
      (.sacrifice
        (.selected
          (.target 1 (.opponent (.controller .this)))
          (.range 1 1)
          (.intersection [
            .permanent,
            .cardType .creature,
            .controlled (.targetReference 1)]))))]
#guard parseOracleParts (name := "Crude Bent Blade")
  "When Crude Bent Blade enters, target opponent sacrifices a creature of their choice." ==
  some [.ability (
    .triggered
      (.enter .this)
      (.sacrifice
        (.selected
          (.target 1 (.opponent (.controller .this)))
          (.range 1 1)
          (.intersection [
            .permanent,
            .cardType .creature,
            .controlled (.targetReference 1)]))))]
#guard parseOracleParts (name := "Gandalf")
  "When Crude Bent Blade enters, target opponent sacrifices a creature of their choice." == none
#guard parseOracleParts (name := "")
  "When this Equipment enters, target opponent sacrifices a creature." == none
#guard parseOracleParts (name := "")
  "When another Equipment enters, target opponent sacrifices a creature of their choice." == none
#guard parseOracleParts (name := "")
  "When this Equipment enters, target opponent sacrifices an artifact of their choice." == none
#guard parseOracleParts (name := "") "Equipped creature gets +2/+1." ==
  some [.ability (.static (.addPower (.hostOf .this) (Value.int 2))),
.ability (.static (.addToughness (.hostOf .this) (Value.int 1)))]
#guard parseOracleParts (name := "") "Equipped creature gets +2/+1 until end of turn." == none
#guard parseOracleParts (name := "") "Equipped creature gets +2/+1 and has flying." ==
  some [
    .ability (.static (.addPower (.hostOf .this) (Value.int 2))),
    .ability (.static (.addToughness (.hostOf .this) (Value.int 1))),
    .ability (.static (.gainAbility (.hostOf .this) (.keyword .flying)))]
#guard parseOracleParts (name := "") "Equipped creature gets +1/+0 and has menace." ==
  some [
    .ability (.static (.addPower (.hostOf .this) (Value.int 1))),
    .ability (.static (.gainAbility (.hostOf .this) (.keyword .menace)))]
#guard parseOracleParts (name := "") "Equipped creature gets +0/+0 and has menace." == none
#guard parseOracleParts (name := "") "Equipped creature gets +1/+0 and gains menace." == none
#guard parseOracleParts (name := "")
  "Equipped creature gets +1/+0 and has menace until end of turn." == none
#guard parseOracleParts (name := "") "Equip {2}" ==
  some [.ability (.keywordWithCost .equip [.mana [.generic 2]])]
#guard parseOracleParts (name := "")
  "Equip {2} ({2}: Attach to target creature you control. Equip only as a sorcery.)" ==
  some [.ability (.keywordWithCost .equip [.mana [.generic 2]])]
#guard parseOracleParts (name := "") "Equip" == none
#guard parseOracleParts (name := "") "Equip {2}: Draw a card." == none
#guard parseOracleParts (name := "Crude Bent Blade")
  "When this Equipment enters, target opponent sacrifices a creature of their choice.\nEquipped creature gets +2/+1.\nEquip {2} ({2}: Attach to target creature you control. Equip only as a sorcery.)" ==
  some [
    .ability (
      .triggered
        (.enter .this)
        (.sacrifice
          (.selected
            (.target 1 (.opponent (.controller .this)))
            (.range 1 1)
            (.intersection [
              .permanent,
              .cardType .creature,
              .controlled (.targetReference 1)])))),
    .ability (.static (.addPower (.hostOf .this) (Value.int 2))),
    .ability (.static (.addToughness (.hostOf .this) (Value.int 1))),
    .ability (.keywordWithCost .equip [.mana [.generic 2]])]

#guard parseOracleParts (name := "Gollum the Abandoned") "Gollum can't block." ==
  some [.ability (.static (.forbid (.block .this .any)))]
#guard parseOracleParts (name := "Gollum the Abandoned") "When Gollum enters, draw a card." ==
  some [.ability (.triggered (.enter .this) (.draw (.controller .this) 1))]
#guard parseOracleParts (name := "Gandalf") "Gollum can't block." == none
#guard parseOracleParts (name := "Gandalf") "When Gollum enters, draw a card." == none
#guard parseOracleParts (name := "") "This creature can't block." ==
  some [.ability (.static (.forbid (.block .this .any)))]
#guard parseOracleParts (name := "") "This creature can't block unless you control a Goblin." ==
  some [.ability (.static (.if
    (.not (.any (.intersection [.permanent, .subtype .goblin, .controlled (.controller .this)])))
    [.forbid (.block .this .any)]))]
#guard parseOracleParts (name := "") "This creature can't block unless you control a Gandalf." ==
  none
#guard parseOracleParts (name := "Gollum the Abandoned")
  "When Gollum enters, exile up to one target card from an opponent's graveyard. Each opponent loses 2 life." ==
  some [.ability (
    .triggered
      (.enter .this)
      (.sequence [
        .exile
          (.targets 1 (.range 0 1)
            (.intersection [.inGraveyard, .owner (.opponent (.controller .this))])),
        .loseLife (.opponent (.controller .this)) 2]))]
#guard parseOracleParts (name := "")
  "When this creature enters, exile up to one target card from an opponent's graveyard. Each opponent loses 2 life." ==
  some [.ability (
    .triggered
      (.enter .this)
      (.sequence [
        .exile
          (.targets 1 (.range 0 1)
            (.intersection [.inGraveyard, .owner (.opponent (.controller .this))])),
        .loseLife (.opponent (.controller .this)) 2]))]
#guard parseOracleParts (name := "Gollum the Abandoned")
  "When Bilbo enters, exile up to one target card from an opponent's graveyard. Each opponent loses 2 life." ==
  none
#guard parseOracleParts (name := "")
  "When this creature enters, exile up to one target creature card from an opponent's graveyard. Each opponent loses 2 life." ==
  none
#guard parseOracleParts (name := "")
  "{2}, Sacrifice an artifact or creature: Return this card from your graveyard to your hand. Activate only as a sorcery." ==
  some [.ability (
    .graveyardActivatedIf
      (.timeToCastSorcery (.controller .this))
      [.mana [.generic 2],
        .sacrificeCount
          (.intersection [
            .permanent,
            .union [.cardType .artifact, .cardType .creature]])
          1]
      (.returnToHand (.intersection [.inGraveyard, .source .this])))]
#guard parseOracleParts (name := "")
  "{2}, Sacrifice an artifact or creature: Return this card from your graveyard to your hand." ==
  some [.ability
     (.activated
       [.mana [.generic 2],
        .sacrificeCount
          (.intersection
            [.permanent,
             .union
               [.cardType .artifact,
                .cardType .creature]])
          1]
       (.returnToHand
         (.intersection
           [.inGraveyard, .source .this])))]
#guard parseOracleParts (name := "")
  "{2}: Return this card from your graveyard to the battlefield." == none
#guard parseOracleParts (name := "Gollum the Abandoned")
  "Gollum can't block.\nWhen Gollum enters, exile up to one target card from an opponent's graveyard. Each opponent loses 2 life.\n{2}, Sacrifice an artifact or creature: Return this card from your graveyard to your hand. Activate only as a sorcery." ==
  some [
    .ability (.static (.forbid (.block .this .any))),
    .ability (
      .triggered
        (.enter .this)
        (.sequence [
          .exile
            (.targets 1 (.range 0 1)
              (.intersection [.inGraveyard, .owner (.opponent (.controller .this))])),
          .loseLife (.opponent (.controller .this)) 2])),
    .ability (
      .graveyardActivatedIf
        (.timeToCastSorcery (.controller .this))
        [.mana [.generic 2],
          .sacrificeCount
            (.intersection [
              .permanent,
              .union [.cardType .artifact, .cardType .creature]])
            1]
        (.returnToHand (.intersection [.inGraveyard, .source .this])))]

#guard parseOracleParts (name := "")
  "Target creature gets +2/+2 and gains lifelink until end of turn." ==
  some [.actions [
    .continuous
      [.addPower
        (.target 1 (.intersection [.permanent, .cardType .creature]))
        (Value.int 2),
       .addToughness
        (.targetReference 1)
        (Value.int 2),
       .gainAbility (.targetReference 1) (.keyword .lifelink)]
      .endOfTurn]]
#guard parseOracleParts (name := "")
  "Target creature gets +2/+2 and has lifelink until end of turn." == none
#guard parseOracleParts (name := "") "Target creature gets +0/+0 until end of turn." == none
#guard parseOracleParts (name := "") "Target creature gets +0/+1 until end of turn." ==
  some [.actions [
    .continuous
      [.addToughness
        (.target 1 (.intersection [.permanent, .cardType .creature]))
        (Value.int 1)]
      .endOfTurn]]
#guard parseOracleParts (name := "")
  "{W}: This creature gets +0/+0 until end of turn." == none
#guard parseOracleParts (name := "")
  "Target creature gets -5/-5 until end of turn. If that creature would die this turn, exile it instead." ==
  some [.actions [
    .continuous
      [.addPower
        (.target 1 (.intersection [.permanent, .cardType .creature]))
        (Value.int (-5)),
       .addToughness
        (.targetReference 1)
        (Value.int (-5)),
       .replace
         (.putToGraveyard (.targetReference 1))
         [.exile (.replacingObject)]]
      .endOfTurn]]
#guard parseOracleParts (name := "")
  "Target creature gets -5/-5 until end of turn. Exile it instead." == none
#guard parseOracleParts (name := "")
  "Creatures target player controls get -1/-1 until end of turn." ==
  some [.actions [
    .continuous
      [.addPower
        (.intersection [
          .permanent,
          .cardType .creature,
          .controlled (.target 1 .player)])
        (Value.int (-1)),
       .addToughness
        (.intersection [
          .permanent,
          .cardType .creature,
          .controlled (.targetReference 1)])
        (Value.int (-1))]
      .endOfTurn]]
#guard parseOracleParts (name := "")
  "Creatures target player controls get -1/-1." == none
#guard parseOracleParts (name := "")
  "Target player draws two cards and loses 2 life." ==
  some [.actions [
    .sequence [
      .draw (.target 1 .player) 2,
      .loseLife (.targetReference 1) 2]]]
#guard parseOracleParts (name := "")
  "Target player draws two cards and gains 2 life." == none
#guard parseOracleParts (name := "")
  "Choose one —\n• Target creature gets -5/-5 until end of turn. If that creature would die this turn, exile it instead.\n• Creatures target player controls get -1/-1 until end of turn." ==
  some [.actions [
    .chooseUniqueModes (.range 1 1) [
      .continuous
        [.addPower
          (.target 1 (.intersection [.permanent, .cardType .creature]))
          (Value.int (-5)),
         .addToughness
          (.targetReference 1)
          (Value.int (-5)),
         .replace
           (.putToGraveyard (.targetReference 1))
           [.exile (.replacingObject)]]
        .endOfTurn,
      .continuous
        [.addPower
          (.intersection [
            .permanent,
            .cardType .creature,
            .controlled (.target 2 .player)])
          (Value.int (-1)),
         .addToughness
          (.intersection [
            .permanent,
            .cardType .creature,
            .controlled (.targetReference 2)])
          (Value.int (-1))]
        .endOfTurn]]]
#guard parseOracleParts (name := "")
  "Choose one —\n• Target player draws two cards and loses 2 life.\n• Target creature gets +2/+2 and gains lifelink until end of turn." ==
  some [.actions [
    .chooseUniqueModes (.range 1 1) [
      .sequence [
        .draw (.target 1 .player) 2,
        .loseLife (.targetReference 1) 2],
      .continuous
        [.addPower
          (.target 2 (.intersection [.permanent, .cardType .creature]))
          (Value.int 2),
         .addToughness
          (.targetReference 2)
          (Value.int 2),
         .gainAbility (.targetReference 2) (.keyword .lifelink)]
        .endOfTurn]]]
#guard parseOracleParts (name := "")
  "Choose one —\n• Target creature gets -5/-5 until end of turn. If that creature would die this turn, exile it instead.\n• Gain control of target creature." ==
  none
#guard parseOracleParts (name := "")
  "When this creature enters, each opponent discards a card." ==
  some [.ability (
    .triggered
      (.enter .this)
      (.discard (.opponent (.controller .this)) 1))]
#guard parseOracleParts (name := "")
  "When another creature enters, each opponent discards a card." ==
  some [.ability (
    .triggered
      (.enter (.intersection [.not .this, .permanent, .cardType .creature]))
      (.discard (.opponent (.controller .this)) (.nat 1)))]
#guard parseOracleParts (name := "")
  "When this creature enters, each opponent discards a card of their choice." == none
#guard parseOracleParts (name := "Gandalf, Spark Starter")
  "When Gandalf enters, he deals 3 damage divided as you choose among one, two, or three targets." ==
  some [.ability (
    .triggered
      (.enter .this)
      (.divideDamage
        (.controller .this)
        (.source .this)
        (.targets 1 (.range 1 3) .all)
        3))]
#guard parseOracleParts (name := "Gandalf, Spark Starter")
  "Reach\nWhen Gandalf enters, he deals 3 damage divided as you choose among one, two, or three targets." ==
  some [
    .ability (.keyword .reach),
    .ability (
      .triggered
        (.enter .this)
        (.divideDamage
          (.controller .this)
          (.source .this)
          (.targets 1 (.range 1 3) .all)
          3))]
#guard parseOracleParts (name := "Gandalf")
  "When Bilbo enters, he deals 3 damage divided as you choose among one, two, or three targets." ==
  none
#guard parseOracleParts (name := "Gandalf, Spark Starter")
  "When Gandalf enters, Bilbo deals 3 damage divided as you choose among one, two, or three targets." ==
  none
#guard parseOracleParts (name := "Gandalf, Spark Starter")
  "When Gandalf enters, he deals 3 damage divided as you choose among one or four targets." == none
#guard parseOracleParts (name := "Gandalf, Spark Starter")
  "When Gandalf enters, he deals 0 damage divided as you choose among one, two, or three targets." ==
  none
#guard parseOracleParts (name := "Gandalf, Spark Starter")
  "When Gandalf enters, he deals 3 damage divided as you choose among one, two, or three target creatures." ==
  none
#guard parseOracleParts (name := "")
  "When this Equipment enters, you may discard a card. If you do, draw two cards." ==
  some [.ability (
    .triggered
      (.enter .this)
      (.sequence [
        .optional (.controller .this)
          (.actionId 1 (.discard (.controller .this) 1)),
        .if (.happened (.actionWithId 1) .gameStart) [.draw (.controller .this) 2]]))]
#guard parseOracleParts (name := "")
  "When this Equipment enters, you may discard a card. Draw two cards." == none
#guard parseOracleParts (name := "")
  "When this Equipment enters, discard a card. If you do, draw two cards." == none
#guard parseOracleParts (name := "")
  "When this Equipment enters, you may discard a card. If you do, draw two cards.\nEquipped creature gets +2/+0.\nEquip {3} ({3}: Attach to target creature you control. Equip only as a sorcery.)" ==
  some [
    .ability (
      .triggered
        (.enter .this)
        (.sequence [
          .optional (.controller .this)
            (.actionId 1 (.discard (.controller .this) 1)),
          .if (.happened (.actionWithId 1) .gameStart) [.draw (.controller .this) 2]])),
    .ability (.static (.addPower (.hostOf .this) (Value.int 2))),
    .ability (.keywordWithCost .equip [.mana [.generic 3]])]
#guard parseOracleParts (name := "Smaug, the Great Calamity")
  "Flying\n//ADV//\nSpew Flame {4}{R}\nSorcery — Adventure\nSpew Flame deals 5 damage to target creature. (Then exile this card. You may cast the creature later from exile.)" ==
  some [
    .ability (.keyword .flying),
    .alternative [
      .name "Spew Flame",
      .manaCost [.generic 4, .mono .red],
      .type .sorcery,
      .subtype .adventure,
      .actions [
        .dealDamage
          .this
          (.target 1 (.intersection [.permanent, .cardType .creature]))
          (.nat 5)]]]

#guard parseOracleParts (name := "")
  "{5}{G}{G}: Put three +1/+1 counters on this creature." ==
  some [.ability (
    .activated
      [.mana [.generic 5, .mono .green, .mono .green]]
      (.putCounter (.source .this) .plusOnePlusOne 3))]
#guard parseOracleParts (name := "")
  "{1}: Put a +1/+1 counter on this creature." ==
  some [.ability (
    .activated [.mana [.generic 1]] (.putCounter (.source .this) .plusOnePlusOne 1))]
#guard parseOracleParts (name := "")
  "{1}: Put three +1/+1 counter on this creature." == none
#guard parseOracleParts (name := "")
  "{1}: Put a +1/+1 counters on this creature." == none
#guard parseOracleParts (name := "")
  "{1}: Put three +1/+1 counters on target creature." ==
  some [.ability
     (.activated
       [.mana [.generic 1]]
       (.putCounter
         (.target
           1
           (.intersection
             [.permanent, .cardType .creature]))
         .plusOnePlusOne
         3))]
#guard parseOracleParts (name := "")
  "Sacrifice another creature or artifact: Exile the top card of your library. You may play it until the end of your next turn. Activate only during your turn and only once each turn." ==
  some [.ability (
    .abilityId 1
      (.activatedIf
        (.and
          (.turn (.controller .this))
          (.didNotHappen (.abilityWithIdActivated 1) .turnStart))
        [.sacrificeCount
          (.intersection [
            .not .this,
            .permanent,
            .union [.cardType .creature, .cardType .artifact]])
          1]
        (.sequence [
          .actionId 1 (.exile (.topOfLibrary (.controller .this) 1)),
          .continuous
            [.canPlay (.controller .this) (.wasCreatedByAction 1)]
            (.sequence [.turnStart, .endOfPlayerTurn (.controller .this)])])))]

end Mtg.Engine
