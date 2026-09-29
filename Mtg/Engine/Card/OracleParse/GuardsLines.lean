import Mtg.Engine.Card.OracleParse.Parse

/-!
# `parseOracleParts` guards, continued

The middle of the `parseOracleParts` regression tests. `Guards` holds the
first part and `GuardsCatalog` the last. Add a new guard at the end of
`GuardsCatalog`.
-/

namespace Mtg.Engine

open OracleParts

#guard parseOracleParts (name := "")
  "Sacrifice a creature or artifact: Exile the top card of your library. You may play it until the end of your next turn. Activate only during your turn and only once each turn." ==
  none
#guard parseOracleParts (name := "")
  "Sacrifice another creature or artifact: Exile the top card of your library. You may play it until end of turn. Activate only during your turn and only once each turn." ==
  none
#guard parseOracleParts (name := "")
  "Target creature you control deals damage equal to its power to target creature an opponent controls." ==
  some [.actions [
    .dealDamageEqualToPower
      (.target 1
        (.intersection [
          .permanent,
          .cardType .creature,
          .controlled (.controller .this)]))
      (.target 2
        (.intersection [
          .permanent,
          .cardType .creature,
          .controlled (.opponent (.controller .this))]))]]
#guard parseOracleParts (name := "")
  "Target creature deals damage equal to its power to target creature an opponent controls." ==
  none
#guard parseOracleParts (name := "Galion, Elvenking's Butler")
  "Whenever Galion attacks, choose up to one other target creature you control. Its base power and toughness become equal to Galion's power and toughness until end of turn." ==
  some [.ability (
    .triggered
      (.attack .this .all)
      (.continuous
        [.setBasePower
          (.targets 1 (.range 0 1)
            (.intersection [
              .not .this,
              .permanent,
              .cardType .creature,
              .controlled (.controller .this)]))
          (Value.greatestPower (.source .this)),
         .setBaseToughness
          (.targetReference 1)
          (Value.greatestToughness (.source .this))]
        .endOfTurn))]
#guard parseOracleParts (name := "Galion, Elvenking's Butler")
  "Whenever this creature attacks, choose up to one other target creature you control. Its base power and toughness become equal to this creature's power and toughness until end of turn." ==
  parseOracleParts (name := "Galion, Elvenking's Butler")
    "Whenever Galion attacks, choose up to one other target creature you control. Its base power and toughness become equal to Galion's power and toughness until end of turn."
#guard parseOracleParts (name := "Gandalf")
  "Whenever Galion attacks, choose up to one other target creature you control. Its base power and toughness become equal to Galion's power and toughness until end of turn." ==
  none
#guard parseOracleParts (name := "Galion, Elvenking's Butler")
  "Whenever Galion attacks, choose up to one target creature you control. Its base power and toughness become equal to Galion's power and toughness until end of turn." ==
  none
#guard parseOracleParts (name := "")
  "Choose one —\n• Destroy target creature with flying.\n• Put a +1/+1 counter on target creature you control. It gains trample and hexproof until end of turn. (It can't be the target of spells or abilities your opponents control.)" ==
  some [.actions [
    .chooseUniqueModes (.range 1 1) [
      .destroy
        (.target 1
          (.intersection [
            .permanent,
            .cardType .creature,
            .keyword .flying])),
      .sequence [
        .putCounter
          (.target 2
            (.intersection [
              .permanent,
              .cardType .creature,
              .controlled (.controller .this)]))
          .plusOnePlusOne
          1,
        .continuous
          [.gainAbility (.targetReference 2) (.keyword .trample),
            .gainAbility (.targetReference 2) (.keyword .hexproof)]
          .endOfTurn]]]]
#guard parseOracleParts (name := "")
  "Put a +1/+1 counter on target creature you control. It gets trample until end of turn." ==
  none
#guard parseOracleParts (name := "")
  "Choose one —\n• Put a +1/+1 counter on target creature you control." ==
  some [.actions
     [.chooseUniqueModes
        (.range (.nat 1) (.nat 1))
        [.putCounter
           (.target
             1
             (.intersection
               [.permanent,
                .cardType .creature,
                .controlled (.controller .this)]))
           .plusOnePlusOne
           1]]]
#guard parseOracleParts (name := "Beorn's Hospitality")
  "Landfall — Whenever a land you control enters, put a +1/+1 counter on target creature you control.\n{5}{G}{G}: This enchantment becomes a Bear creature in addition to its other types and gains \"This creature's power and toughness are each equal to the number of lands you control.\" (This effect doesn't end.)" ==
  some [
    .ability (
      .triggered
        (.enter
          (.intersection [
            .permanent,
            .cardType .land,
            .controlled (.controller .this)]))
        (.putCounter
          (.target
            1
            (.intersection [
              .permanent,
              .cardType .creature,
              .controlled (.controller .this)]))
          .plusOnePlusOne
          1)),
    .ability (
      .activated
        [.mana [.generic 5, .mono .green, .mono .green]]
        (.continuous
          [.gainType .this .creature,
            .gainSubtype .this .bear,
            .gainAbility
              .this
              (.static
                (.setPower
                  .this
                  (.count
                    (.intersection [
                      .permanent,
                      .cardType .land,
                      .controlled (.controller .this)])))),
            .gainAbility
              .this
              (.static
                (.setToughness
                  .this
                  (.count
                    (.intersection [
                      .permanent,
                      .cardType .land,
                      .controlled (.controller .this)]))))]
          .endOfGame))]
#guard parseOracleParts (name := "")
  "Whenever a land you control enters, put a +1/+1 counter on target creature you control." ==
  parseOracleParts (name := "")
    "Landfall — Whenever a land you control enters, put a +1/+1 counter on target creature you control."
#guard parseOracleParts (name := "")
  "{1}{G}: This enchantment becomes an Elf creature in addition to its other types and gains \"This creature's power and toughness are each equal to the number of lands you control.\"" ==
  some [.ability (
    .activated
      [.mana [.generic 1, .mono .green]]
      (.continuous
        [.gainType .this .creature,
          .gainSubtype .this .elf,
          .gainAbility
            .this
            (.static
              (.setPower
                .this
                (.count
                  (.intersection [
                    .permanent,
                    .cardType .land,
                    .controlled (.controller .this)])))),
          .gainAbility
            .this
            (.static
              (.setToughness
                .this
                (.count
                  (.intersection [
                    .permanent,
                    .cardType .land,
                    .controlled (.controller .this)]))))]
        .endOfGame))]
#guard parseOracleParts (name := "")
  "Landfall — Whenever a land enters, put a +1/+1 counter on target creature you control." == none
#guard parseOracleParts (name := "")
  "Whenever a land you control enters, put a +1/+1 counter on target creature." ==
  some [.ability
     (.triggered
       (.enter
         (.intersection
           [.permanent,
            .cardType .land,
            .controlled (.controller .this)]))
       (.putCounter
         (.target
           1
           (.intersection
             [.permanent, .cardType .creature]))
         .plusOnePlusOne
         1))]
#guard parseOracleParts (name := "Gandalf")
  "{5}{G}{G}: Beorn's Hospitality becomes a Bear creature in addition to its other types and gains \"This creature's power and toughness are each equal to the number of lands you control.\"" ==
  none
#guard parseOracleParts (name := "")
  "{5}{G}{G}: This enchantment becomes a Bear creature in addition to its other types and its power and toughness are each equal to the number of lands you control." ==
  none
#guard parseOracleParts (name := "")
  "{1}{G}: This enchantment becomes a Bear creature in addition to its other types and gains \"This creature's power and toughness are each equal to the number of lands you control.\" until end of turn." ==
  none
#guard englishSmall? " 2 " == some 2
#guard englishSmall? "Two" == some 2
#guard positiveCount "0" == none
#guard positiveCount " 3 " == some 3
#guard parseOracleParts (name := "") "When this creature enters, draw one card." ==
  parseOracleParts (name := "") "When this creature enters, draw a card."
#guard parseOracleParts (name := "") "When this creature enters, draw 1 card." ==
  parseOracleParts (name := "") "When this creature enters, draw a card."
#guard parseOracleParts (name := "") "When this creature enters, draw a cards." == none
#guard parseOracleParts (name := "") "When this creature enters, draw one cards." == none
#guard parseOracleParts (name := "")
  "Sacrifice a creature: This creature gets +1/+1 until end of turn." == none
#guard parseOracleParts (name := "") "Reach, trample, haste" ==
  some [
    .ability (.keyword .reach),
    .ability (.keyword .trample),
    .ability (.keyword .haste)]
#guard parseOracleParts (name := "") "Reach, deathtouch" ==
  some [.ability (.keyword .reach), .ability (.keyword .deathtouch)]
#guard parseOracleParts (name := "")
  "Whenever another Elf you control enters, this creature gets +1/+1 until end of turn." ==
  some [.ability (
    .triggered
      (.enter
        (.intersection [
          .not .this,
          .permanent,
          .subtype .elf,
          .controlled (.controller .this)]))
      (.continuous
        [.addPower (.source .this) (Value.int 1),
         .addToughness (.source .this) (Value.int 1)]
        .endOfTurn))]
#guard parseOracleParts (name := "")
  "Whenever another Bear you control enters, this creature gets +1/+1 until end of turn." ==
  some [.ability
     (.triggered
       (.enter
         (.intersection
           [.not .this,
            .permanent,
            .subtype .bear,
            .controlled (.controller .this)]))
       (.continuous
         [.addPower
            (.source .this)
            (.int 1),
          .addToughness
            (.source .this)
            (.int 1)]
         .endOfTurn))]
#guard parseOracleParts (name := "")
  "Whenever another Elf you control enters, this creature gets +2/+2 until end of turn." ==
  some [.ability
     (.triggered
       (.enter
         (.intersection
           [.not .this,
            .permanent,
            .subtype .elf,
            .controlled (.controller .this)]))
       (.continuous
         [.addPower
            (.source .this)
            (.int 2),
          .addToughness
            (.source .this)
            (.int 2)]
         .endOfTurn))]
#guard parseOracleParts (name := "")
  "Landfall — Whenever a land you control enters, this creature gets +1/+1 until end of turn." ==
  some [.ability (
    .triggered
      (.enter
        (.intersection [
          .permanent,
          .cardType .land,
          .controlled (.controller .this)]))
      (.continuous
        [.addPower (.source .this) (Value.int 1),
         .addToughness (.source .this) (Value.int 1)]
        .endOfTurn))]
#guard parseOracleParts (name := "")
  "Whenever a land you control enters, this creature gets +1/+1 until end of turn." ==
  parseOracleParts (name := "")
    "Landfall — Whenever a land you control enters, this creature gets +1/+1 until end of turn."
#guard parseOracleParts (name := "")
  "Landfall — Whenever a land you control enters, creatures you control get +1/+1 until end of turn." ==
  some [.ability
     (.triggered
       (.enter
         (.intersection
           [.permanent,
            .cardType .land,
            .controlled (.controller .this)]))
       (.continuous
         [.addPower
            (.intersection
              [.permanent,
               .cardType .creature,
               .controlled (.controller .this)])
            (.int 1),
          .addToughness
            (.intersection
              [.permanent,
               .cardType .creature,
               .controlled (.controller .this)])
            (.int 1)]
         .endOfTurn))]
#guard parseOracleParts (name := "Woodland Weavemaster")
  "{T}: Add X mana of any one color, where X is this creature's power. Spend this mana only to cast Elf spells and activate abilities of Elf sources." ==
  some [.ability (
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
          .endOfTurn]))]
#guard parseOracleParts (name := "Woodland Weavemaster")
  "{T}: Add X mana of any one color, where X is Woodland Weavemaster's power. Spend this mana only to cast Elf spells and activate abilities of Elf sources." ==
  parseOracleParts (name := "Woodland Weavemaster")
    "{T}: Add X mana of any one color, where X is this creature's power. Spend this mana only to cast Elf spells and activate abilities of Elf sources."
#guard parseOracleParts (name := "Gandalf")
  "{T}: Add X mana of any one color, where X is Woodland Weavemaster's power. Spend this mana only to cast Elf spells and activate abilities of Elf sources." ==
  none
#guard parseOracleParts (name := "Mirkwood Pathmaker")
  "Mirkwood Pathmaker's power and toughness are each equal to the number of lands you control." ==
  some [
    .ability (
      .static
        (.setPower
          .this
          (.count
            (.intersection [
              .permanent,
              .cardType .land,
              .controlled (.controller .this)])))),
    .ability (
      .static
        (.setToughness
          .this
          (.count
            (.intersection [
              .permanent,
              .cardType .land,
              .controlled (.controller .this)]))))]
#guard parseOracleParts (name := "")
  "This creature's power and toughness are each equal to the number of lands you control." ==
  parseOracleParts (name := "Mirkwood Pathmaker")
    "Mirkwood Pathmaker's power and toughness are each equal to the number of lands you control."
#guard parseOracleParts (name := "Gandalf")
  "Mirkwood Pathmaker's power and toughness are each equal to the number of lands you control." ==
  none
#guard parseOracleParts (name := "") "You may play an additional land this turn." ==
  some [.actions [
    .continuous
      [.increaseLandPlayLimit (.controller .this) (Value.nat 1)]
      .endOfTurn]]
#guard parseOracleParts (name := "") "You may play two additional lands this turn." == none
#guard parseOracleParts (name := "")
  "When this creature enters, search your library for a Forest card, put that card onto the battlefield, then shuffle." ==
  some [.ability (
    .triggered
      (.enter .this)
      (.searchLibraryThenShuffle
        (.controller .this)
        [.putOntoBattlefield
          (.selected
            (.controller .this)
            (.range 1 1)
            (.intersection [.inLibrary, .subtype .forest]))]))]
#guard parseOracleParts (name := "Wood Elves")
  "When Wood Elves enters, search your library for a Forest card, put that card onto the battlefield, then shuffle." ==
  parseOracleParts (name := "")
    "When this creature enters, search your library for a Forest card, put that card onto the battlefield, then shuffle."
#guard parseOracleParts (name := "")
  "When this creature enters, search your library for an Island card, put that card onto the battlefield, then shuffle." ==
  none
#guard parseOracleParts (name := "")
  "Trample\n//ADV//\nTill and Tend {1}{G}\nSorcery — Adventure\nYou may play an additional land this turn. (Then exile this card. You may cast the creature later from exile.)" ==
  some [
    .ability (.keyword .trample),
    .alternative [
      .name "Till and Tend",
      .manaCost [.generic 1, .mono .green],
      .type .sorcery,
      .subtype .adventure,
      .actions [
        .continuous
          [.increaseLandPlayLimit (.controller .this) (Value.nat 1)]
          .endOfTurn]]]
#guard parseOracleParts (name := "Elvenking's Halls") "This land enters tapped." ==
  some [.ability (.static (.replace (.enter .this)
    [.putOntoBattlefieldInState .this [.tapped]]))]
#guard parseOracleParts (name := "") "This spell enters tapped." == none
#guard parseOracleParts (name := "") "This land enters." == none
#guard parseOracleParts (name := "") "{T}: Add {G} or {U}." ==
  some [.ability (.activated [.tapSymbol]
    (.playerSelectAction (.controller .this) (.range 1 1)
      [.addMana (.controller .this) [.mono .green],
       .addMana (.controller .this) [.mono .blue]]))]
#guard parseOracleParts (name := "") "{T}: Add {G}." ==
  some [.ability
     (.activated
       [.tapSymbol]
       (.addMana
         (.controller .this)
         [.colored .green]))]
#guard parseOracleParts (name := "") "{T}: Add {2} or {G}." == none
#guard parseOracleParts (name := "")
  "{4}{U}: Target creature can't be blocked this turn." ==
  some [.ability (.activated [.mana [.generic 4, .mono .blue]]
    (.continuous
      [.forbid (.block .any
        (.target 1 (.intersection [.permanent, .cardType .creature])))]
      .endOfTurn))]
#guard parseOracleParts (name := "")
  "{2}{G}{U}, {T}, Sacrifice this land: Put two +1/+1 counters on target Elf you control. Activate only as a sorcery." ==
  some [.ability (.activatedIf (.timeToCastSorcery (.controller .this))
    [.mana [.generic 2, .mono .green, .mono .blue], .tapSymbol, .sacrifice .this]
    (.putCounter
      (.target 1 (.intersection
        [.permanent, .cardType .creature, .subtype .elf, .controlled (.controller .this)]))
      .plusOnePlusOne 2))]
#guard parseOracleParts (name := "")
  "{2}{B}{R}, {T}, Sacrifice this land: Put two +1/+1 counters on target Goblin or Orc you control. Activate only as a sorcery." ==
  some [.ability (.activatedIf (.timeToCastSorcery (.controller .this))
    [.mana [.generic 2, .mono .black, .mono .red], .tapSymbol, .sacrifice .this]
    (.putCounter
      (.target 1 (.intersection [
        .permanent, .cardType .creature,
        .union [.subtype .goblin, .subtype .orc],
        .controlled (.controller .this)]))
      .plusOnePlusOne 2))]
#guard parseOracleParts (name := "")
  "{2}{B}{G}, {T}, Sacrifice this land: Put two +1/+1 counter on target Bear, Spider, or Wolf you control. Activate only as a sorcery." ==
  none
#guard parseOracleParts (name := "")
  "{T}, Sacrifice this land: Search your library for a basic land card, put it onto the battlefield tapped, then shuffle." ==
  some [.ability (.activated [.tapSymbol, .sacrifice .this]
    (.searchLibraryThenShuffle (.controller .this)
      [.putOntoBattlefieldInState
        (.selected (.controller .this) (.range 1 1)
          (.intersection [.inLibrary, .cardType .land, .supertype .basic]))
        [.tapped]]))]
#guard parseOracleParts (name := "")
  "{T}, Pay 1 life, Sacrifice this land: Search your library for a basic land card, put it onto the battlefield tapped, then shuffle. You may behold an Elf. If you do, untap that land." ==
  some [.ability (.activated
    [.tapSymbol, .life 1, .sacrifice .this]
    (.sequence [
      .searchLibraryThenShuffle (.controller .this) [
        .defineSelectorVariable 1
          (.selected (.controller .this) (.range 1 1)
            (.intersection [.inLibrary, .cardType .land, .supertype .basic])),
        .actionId 2
          (.putOntoBattlefieldInState (.variable 1) [.tapped])],
      .optional (.controller .this)
        (.actionId 3 (.keyword (.controller .this) (.behold .elf))),
      .if (.happened (.actionWithId 3) .gameStart)
        [.untap (.affectedByAction 2)]]))]
#guard parseOracleParts (name := "")
  "{T}, Pay 1 life, Sacrifice this land: Search your library for a basic land card, put it onto the battlefield tapped, then shuffle. You may behold an Elf. If you do, untap that land. (To behold an Elf, choose an Elf you control or reveal an Elf card from your hand.)" ==
  parseOracleParts (name := "")
    "{T}, Pay 1 life, Sacrifice this land: Search your library for a basic land card, put it onto the battlefield tapped, then shuffle. You may behold an Elf. If you do, untap that land."
#guard parseOracleParts (name := "") "You may behold a Goblin." ==
  some [.actions [
    .optional (.controller .this) (.keyword (.controller .this) (.behold .goblin))]]
#guard parseOracleParts (name := "") "You may behold Elf." == none
#guard parseOracleParts (name := "")
  "Halflingcycling {4} ({4}, Discard this card: Search your library for a Halfling card, reveal it, put it into your hand, then shuffle.)" ==
  some [.ability (.keywordWithCost (.typecycling [] [] [.halfling]) [.mana [.generic 4]])]
#guard parseOracleParts (name := "") "Halflingcycling" == none
#guard parseOracleParts (name := "") "Cycling {2}" == none
#guard parseOracleParts (name := "") "Basic landcycling {2}" ==
  some [.ability (.keywordWithCost (.typecycling [.basic] [.land] []) [.mana [.generic 2]])]
#guard parseOracleParts (name := "")
  "When this Equipment enters, you gain 2 life." ==
  some [.ability (.triggered (.enter .this) (.gainLife (.controller .this) 2))]
#guard parseOracleParts (name := "")
  "When this Equipment enters, target player gains 2 life." ==
  some [.ability
     (.triggered
       (.enter .this)
       (.gainLife
         (.target 1 .player)
         (.nat 2)))]
#guard parseOracleParts (name := "")
  "When this creature enters, untap another target creature you control. If that creature is a Bear, put a +1/+1 counter on it." ==
  some [.ability (.triggered (.enter .this)
    (.sequence [
      .untap (.target 1 (.intersection [
        .not .this, .permanent, .cardType .creature, .controlled (.controller .this)])),
      .if (.anySubtype (.targetReference 1) .bear)
        [.putCounter (.targetReference 1) .plusOnePlusOne 1]]))]
#guard parseOracleParts (name := "")
  "When this creature enters, untap target creature you control. If that creature is a Bear, put a +1/+1 counter on it." ==
  none
#guard parseOracleParts (name := "")
  "Ferocious — Whenever this creature attacks while you control a creature with power 4 or greater, this creature gets +2/+2 until end of turn." ==
  some [.ability (.triggeredWhile (.attack .this .all)
    (.any (.intersection [
      .permanent, .cardType .creature, .controlled (.controller .this),
      .powerAtLeast (Value.int 4)]))
    (.continuous
      [.addPower (.source .this) (Value.int 2), .addToughness (.source .this) (Value.int 2)]
      .endOfTurn))]
#guard parseOracleParts (name := "")
  "Whenever this creature attacks while you control a creature with power 4 or greater, this creature gets +2/+2 until end of turn." ==
  parseOracleParts (name := "")
    "Ferocious — Whenever this creature attacks while you control a creature with power 4 or greater, this creature gets +2/+2 until end of turn."
#guard parseOracleParts (name := "")
  "Ferocious — Whenever this creature attacks while you control a creature with power 4 or greater, creatures you control get +2/+2 until end of turn." ==
  none
#guard parseOracleParts (name := "")
  "Ferocious — Whenever this creature attacks while you control a creature with power 4 or greater, until end of turn, this creature gets +1/+0 and creatures you control gain trample." ==
  some [.ability (.triggeredWhile (.attack .this .all)
    (.any (.intersection [
      .permanent, .cardType .creature, .controlled (.controller .this),
      .powerAtLeast (Value.int 4)]))
    (.continuous
      [.addPower (.source .this) (Value.int 1),
        .gainAbility
          (.intersection [
            .permanent, .cardType .creature, .controlled (.controller .this)])
          (.keyword .trample)]
      .endOfTurn))]
#guard parseOracleParts (name := "")
  "Whenever this creature attacks while you control a creature with power 4 or greater, until end of turn, this creature gets +1/+0 and creatures you control gain trample." ==
  parseOracleParts (name := "")
    "Ferocious — Whenever this creature attacks while you control a creature with power 4 or greater, until end of turn, this creature gets +1/+0 and creatures you control gain trample."
#guard parseOracleParts (name := "")
  "Ferocious — Whenever this creature attacks while you control a creature with power 4 or greater, until end of turn, this creature gets +0/+0 and creatures you control gain trample." ==
  none
#guard parseOracleParts (name := "")
  "Ferocious — Whenever this creature attacks while you control a creature with power 4 or greater, until end of turn, this creature gets +1/+1 and creatures you control gain trample." ==
  none
#guard parseOracleParts (name := "")
  "Ferocious — Whenever this creature attacks while you control a creature with power 4 or greater, until end of turn, this creature gets +1/+0 and creatures you control gain haste." ==
  none
#guard parseOracleParts (name := "")
  "Ferocious — Whenever this creature attacks while you control a creature with power 4 or greater, put a +1/+1 counter on each creature you control." ==
  some [.ability (.triggeredWhile (.attack .this .all)
    (.any (.intersection [
      .permanent, .cardType .creature, .controlled (.controller .this),
      .powerAtLeast (Value.int 4)]))
    (.putCounter
      (.intersection [
        .permanent, .cardType .creature, .controlled (.controller .this)])
      .plusOnePlusOne
      1))]
#guard parseOracleParts (name := "")
  "Ferocious — Whenever this creature attacks while you control a creature with power 4 or greater, put two +1/+1 counters on each creature you control." ==
  none
#guard parseOracleParts (name := "")
  "Ferocious — Whenever you attack while you control a creature with power 4 or greater, you draw a card and lose 1 life." ==
  some [.ability (.triggeredWhile
    (.attackSimultaneously
      (.intersection [
        .permanent, .cardType .creature, .controlled (.controller .this)])
      .all
      [])
    (.any (.intersection [
      .permanent, .cardType .creature, .controlled (.controller .this),
      .powerAtLeast (Value.int 4)]))
    (.sequence [
      .draw (.controller .this) 1,
      .loseLife (.controller .this) 1]))]
#guard parseOracleParts (name := "")
  "Whenever you attack while you control a creature with power 4 or greater, you draw a card and lose 1 life." ==
  parseOracleParts (name := "")
    "Ferocious — Whenever you attack while you control a creature with power 4 or greater, you draw a card and lose 1 life."
#guard parseOracleParts (name := "")
  "Ferocious — Whenever you attack while you control a creature with power 4 or greater, you draw two cards and lose 1 life." ==
  none
#guard parseOracleParts (name := "")
  "Ferocious — Whenever you attack while you control a creature with power 4 or greater, you gain 2 life." ==
  none
#guard parseOracleParts (name := "")
  "Ferocious — At the beginning of combat on your turn, if you control a creature with power 4 or greater, put a +1/+1 counter on this creature." ==
  some [.ability (.triggered
    (.combatStart (.controller .this))
    (.if
      (.any (.intersection [
        .permanent, .cardType .creature, .controlled (.controller .this),
        .powerAtLeast (Value.int 4)]))
      [.putCounter (.source .this) .plusOnePlusOne 1]))]
#guard parseOracleParts (name := "")
  "At the beginning of combat on your turn, if you control a creature with power 4 or greater, put a +1/+1 counter on this creature." ==
  parseOracleParts (name := "")
    "Ferocious — At the beginning of combat on your turn, if you control a creature with power 4 or greater, put a +1/+1 counter on this creature."
#guard parseOracleParts (name := "")
  "Ferocious — At the beginning of combat on your turn, put a +1/+1 counter on this creature." ==
  none
#guard parseOracleParts (name := "")
  "Choose one —\n• Creatures you control get +2/+1 until end of turn.\n• Destroy target artifact or enchantment. You gain 2 life." ==
  some [.actions [.chooseUniqueModes (.range 1 1) [
    .continuous
      [.addPower
        (.intersection [
          .permanent, .cardType .creature, .controlled (.controller .this)])
        (Value.int 2),
       .addToughness
        (.intersection [
          .permanent, .cardType .creature, .controlled (.controller .this)])
        (Value.int 1)]
      .endOfTurn,
    .sequence [
      .destroy
        (.target 1
          (.intersection [
            .permanent,
            .union [.cardType .artifact, .cardType .enchantment]])),
      .gainLife (.controller .this) 2]]]]
#guard parseOracleParts (name := "")
  "Choose one —\n• Destroy target creature with power 4 or greater.\n• Until end of turn, target creature becomes an artifact in addition to its other types and gains indestructible. (Damage and effects that say \"destroy\" don't destroy it.)" ==
  some [.actions [.chooseUniqueModes (.range 1 1) [
    .destroy
      (.target 1
        (.intersection [
          .permanent, .cardType .creature, .powerAtLeast (Value.int 4)])),
    .continuous
      [.gainType
        (.target 2 (.intersection [.permanent, .cardType .creature]))
        .artifact,
       .gainAbility (.targetReference 2) (.keyword .indestructible)]
      .endOfTurn]]]
#guard parseOracleParts (name := "")
  "Until end of turn, target artifact becomes an artifact in addition to its other types and gains indestructible." ==
  none
#guard parseOracleParts (name := "") "This creature can't be blocked by tokens." ==
  some [.ability (.static (.forbid (.block .token .this)))]
#guard parseOracleParts (name := "Duskwatch Hunter")
  "Duskwatch Hunter can't be blocked by tokens." ==
  parseOracleParts (name := "") "This creature can't be blocked by tokens."
#guard parseOracleParts (name := "") "This creature can't be blocked by Goblins." == none
#guard parseOracleParts (name := "")
  "When this creature enters, put a +1/+1 counter on target creature." ==
  some [.ability (.triggered (.enter .this)
    (.putCounter
      (.target 1 (.intersection [.permanent, .cardType .creature]))
      .plusOnePlusOne
      1))]
#guard parseOracleParts (name := "")
  "When this creature enters, put a +1/+1 counter on target Elf." ==
  some [.ability
     (.triggered
       (.enter .this)
       (.putCounter
         (.target
           1
           (.intersection
             [.permanent,
              .cardType .creature,
              .subtype .elf]))
         .plusOnePlusOne
         1))]
#guard parseOracleParts (name := "")
  "When this creature enters, recruit. (Draw a card, then discard a card. If you discarded a nonland card, create a 1/1 white Human Soldier creature token.)" ==
  some [.ability (.triggered (.enter .this) (.keyword (.controller .this) .recruit))]
#guard parseOracleParts (name := "Patient Instructor")
  "When Patient Instructor enters, recruit." ==
  parseOracleParts (name := "") "When this creature enters, recruit."
#guard parseOracleParts (name := "Gandalf") "When Patient Instructor enters, recruit." == none
#guard parseOracleParts (name := "")
  "Vigilance\nWhen this creature enters, recruit." ==
  some [
    .ability (.keyword .vigilance),
    .ability (.triggered (.enter .this) (.keyword (.controller .this) .recruit))]
#guard parseOracleParts (name := "")
  "Flying\nWhen this creature enters, recruit." ==
  some [
    .ability (.keyword .flying),
    .ability (.triggered (.enter .this) (.keyword (.controller .this) .recruit))]
#guard parseOracleParts (name := "")
  "When this creature dies, recruit. (Draw a card, then discard a card. If you discarded a nonland card, create a 1/1 white Human Soldier creature token.)" ==
  some [.ability (.triggered (.die .this) (.keyword (.controller .this) .recruit))]
#guard parseOracleParts (name := "Lake-town Lookout")
  "When Lake-town Lookout dies, recruit." ==
  parseOracleParts (name := "") "When this creature dies, recruit."
#guard parseOracleParts (name := "Gandalf") "When Lake-town Lookout dies, recruit." == none
#guard parseOracleParts (name := "") "When this creature dies, draw a card." ==
  some [.ability
     (.triggered
       (.die .this)
       (.draw (.controller .this) (.nat 1)))]
#guard parseOracleParts (name := "") "When another creature dies, recruit." == none
#guard parseOracleParts (name := "")
  "When this artifact enters, scry 2. (Look at the top two cards of your library, then put any number of them on the bottom and the rest on top in any order.)" ==
  some [.ability (.triggered (.enter .this) (.scry (.controller .this) 2))]
#guard parseOracleParts (name := "") "When this creature enters, scry 0." == none
#guard parseOracleParts (name := "") "When this artifact enters, scry two." ==
  some [.ability (.triggered (.enter .this) (.scry (.controller .this) 2))]
#guard parseOracleParts (name := "")
  "{1}, {T}: Add one mana of any color." ==
  some [.ability (
    .activated
      [.mana [.generic 1], .tapSymbol]
      (.addManaOfOneColor (.controller .this) ManaSymbol.anyColor 1))]
#guard parseOracleParts (name := "") "Add one mana of any color." ==
  some [.actions
     [.addManaOfOneColor
        (.controller .this)
        [.colored .white,
         .colored .blue,
         .colored .black,
         .colored .red,
         .colored .green]
        (.nat 1)]]
#guard parseOracleParts (name := "") "{T}: Add one mana of any color." ==
  some [.ability
     (.activated
       [.tapSymbol]
       (.addManaOfOneColor
         (.controller .this)
         [.colored .white,
          .colored .blue,
          .colored .black,
          .colored .red,
          .colored .green]
         (.nat 1)))]
#guard parseOracleParts (name := "Giant's Boulder")
  "{7}, {T}, Sacrifice this artifact: Destroy target permanent." ==
  some [.ability (
    .activated
      [.mana [.generic 7], .tapSymbol, .sacrifice .this]
      (.destroy (.target 1 .permanent)))]
#guard parseOracleParts (name := "Giant's Boulder")
  "{7}, {T}, Sacrifice Giant's Boulder: Destroy target permanent." ==
  parseOracleParts (name := "Giant's Boulder")
    "{7}, {T}, Sacrifice this artifact: Destroy target permanent."
#guard parseOracleParts (name := "") "Destroy target permanent." ==
  some [.actions
     [.destroy (.target 1 .permanent)]]
#guard parseOracleParts (name := "")
  "When this creature enters, create a tapped Treasure token. (It's an artifact with \"{T}, Sacrifice this token: Add one mana of any color.\")" ==
  some [.ability (
    .triggered
      (.enter .this)
      (.createTokens (.controller .this) 1 PredefinedToken.treasureToken [.tapped]))]
#guard parseOracleParts (name := "Dori, Bearer of Friends")
  "When Dori enters, create a Treasure token." ==
  some [.ability (
    .triggered
      (.enter .this)
      (.createTokens (.controller .this) 1 PredefinedToken.treasureToken))]
#guard parseOracleParts (name := "Gandalf")
  "When Dori enters, create a Treasure token." == none
#guard parseOracleParts (name := "")
  "When this creature enters, create two Treasure tokens." ==
  some [.ability
     (.triggered
       (.enter .this)
       (.createTokens
         (.controller .this)
         (.nat 2)
         [.type .artifact,
          .subtype .treasure,
          .ability
            (.activated
              [.tapSymbol, .sacrifice .this]
              (.addManaOfOneColor
                (.controller .this)
                [.colored .white,
                 .colored .blue,
                 .colored .black,
                 .colored .red,
                 .colored .green]
                (.nat 1)))]
         []))]
#guard parseOracleParts (name := "")
  "When this creature enters, create a tapped Food token." == none
#guard parseOracleParts (name := "Esgaroth Garrison")
  "Esgaroth Garrison's power is equal to the number of creatures you control." ==
  some [.ability (
    .static
      (.setPower
        .this
        (.count
          (.intersection [
            .permanent,
            .cardType .creature,
            .controlled (.controller .this)]))))]
#guard parseOracleParts (name := "")
  "This creature's power is equal to the number of creatures you control." ==
  parseOracleParts (name := "Esgaroth Garrison")
    "Esgaroth Garrison's power is equal to the number of creatures you control."
#guard parseOracleParts (name := "Gandalf")
  "Esgaroth Garrison's power is equal to the number of creatures you control." == none
#guard parseOracleParts (name := "")
  "This creature's toughness is equal to the number of creatures you control." == none
#guard parseOracleParts (name := "")
  "When this creature enters, exile the top card of your library. Until the end of your next turn, you may play that card." ==
  some [.ability (
    .triggered
      (.enter .this)
      (.sequence [
        .actionId 1 (.exile (.topOfLibrary (.controller .this) 1)),
        .continuous
          [.canPlay (.controller .this) (.wasCreatedByAction 1)]
          (.sequence [.turnStart, .endOfPlayerTurn (.controller .this)])]))]
#guard parseOracleParts (name := "")
  "When this creature enters, exile the top card of your library." == none
#guard parseOracleParts (name := "")
  "When this creature enters, exile the top card of your library. You may play it until the end of your next turn." == none
#guard parseOracleParts (name := "") "This spell can't be countered." ==
  some [.ability (.stackStatic (.forbid (.counter .this)))]
#guard parseOracleParts (name := "")
  "This spell can't be countered. (It can't be countered.)" ==
  parseOracleParts (name := "") "This spell can't be countered."
#guard parseOracleParts (name := "") "This creature can't be countered." == none
#guard parseOracleParts (name := "") "Hexproof, haste" ==
  some [.ability (.keyword .hexproof), .ability (.keyword .haste)]
#guard parseOracleParts (name := "")
  "Whenever you cast a noncreature spell, amass Goblins 1. (Put a +1/+1 counter on an Army you control. It's also a Goblin. If you don't control an Army, create a 0/0 black Goblin Army creature token first.)" ==
  some [.ability (
    .triggered
      (.castSpell
        (.intersection [
          .spell,
          .not (.cardType .creature),
          .controlled (.controller .this)]))
      (.keyword (.controller .this) (.amass .goblin (.nat 1))))]
#guard parseOracleParts (name := "")
  "Whenever you cast a creature spell, amass Goblins 1." ==
  some [.ability
     (.triggered
       (.castSpell
         (.intersection
           [.spell,
            .cardType .creature,
            .controlled (.controller .this)]))
       (.keyword
         (.controller .this)
         (.amass .goblin (.nat 1))))]
#guard parseOracleParts (name := "") "Whenever you cast a noncreature spell, amass Goblin 1." == none
#guard parseOracleParts (name := "") "Whenever you cast a noncreature spell, amass Goblins 0." == none
#guard parseOracleParts (name := "")
  "When this creature enters, amass Goblins 1." ==
  some [.ability (
    .triggered
      (.enter .this)
      (.keyword (.controller .this) (.amass .goblin (.nat 1))))]
#guard parseOracleParts (name := "Goblin-town Flunkies")
  "When Goblin-town Flunkies enters, amass Goblins 1." ==
  parseOracleParts (name := "") "When this creature enters, amass Goblins 1."
#guard parseOracleParts (name := "Gandalf")
  "When Goblin-town Flunkies enters, amass Goblins 1." == none
#guard parseOracleParts (name := "")
  "When this creature dies, amass Goblins 4." ==
  some [.ability (
    .triggered
      (.die .this)
      (.keyword (.controller .this) (.amass .goblin (.nat 4))))]
#guard parseOracleParts (name := "")
  "Whenever you attack, amass Goblins 2." ==
  some [.ability (
    .triggered
      (.attackSimultaneously
        (.intersection [
          .permanent,
          .cardType .creature,
          .controlled (.controller .this)])
        .all
        [])
      (.keyword (.controller .this) (.amass .goblin (.nat 2))))]
#guard parseOracleParts (name := "")
  "Whenever you attack while you control a Goblin, amass Goblins 2." == none
#guard parseOracleParts (name := "")
  "You may cast this spell as though it had flash if you control a Human." ==
  some [.ability (.everywhereStatic (
    .canBeCastAsThoughWithFlashIf
      .this
      (.any (.intersection [
        .permanent, .subtype .human, .controlled .caster]))))]
#guard parseOracleParts (name := "")
  "You may cast this spell as though it had flash if you control Human." == none
#guard parseOracleParts (name := "")
  "You may cast this spell as though it had flash if you control an Elf." ==
  some [.ability (.everywhereStatic (
    .canBeCastAsThoughWithFlashIf
      .this
      (.any (.intersection [
        .permanent, .subtype .elf, .controlled .caster]))))]
#guard parseOracleParts (name := "") "Other creatures you control get +1/+1." ==
  some [
    .ability (.static (.addPower
      (.intersection [
        .not .this,
        .permanent,
        .cardType .creature,
        .controlled (.controller .this)]) (Value.int 1))),
    .ability (.static (.addToughness
      (.intersection [
        .not .this,
        .permanent,
        .cardType .creature,
        .controlled (.controller .this)]) (Value.int 1)))]
#guard parseOracleParts (name := "") "Other creatures you control get +0/+0." == none
#guard parseOracleParts (name := "")
  "Other creatures you control get +1/+1 until end of turn." ==
  some [.actions
     [.continuous
        [.addPower
           (.intersection
             [.not .this,
              .permanent,
              .cardType .creature,
              .controlled (.controller .this)])
           (.int 1),
         .addToughness
           (.intersection
             [.not .this,
              .permanent,
              .cardType .creature,
              .controlled (.controller .this)])
           (.int 1)]
        .endOfTurn]]
#guard parseOracleParts (name := "")
  "Whenever this creature enters or attacks, recruit." ==
  some [.ability (
    .triggered
      (.or (.enter .this) (.attack .this .all))
      (.keyword (.controller .this) .recruit))]
#guard parseOracleParts (name := "Bard's Company")
  "Whenever Bard's Company enters or attacks, recruit." ==
  parseOracleParts (name := "") "Whenever this creature enters or attacks, recruit."
#guard parseOracleParts (name := "Gandalf")
  "Whenever Bard's Company enters or attacks, recruit." == none
#guard parseOracleParts (name := "")
  "Whenever this creature enters or attacks, draw a card." ==
  some [.ability
     (.triggered
       (.or
         (.enter .this)
         (.attack .this .all))
       (.draw (.controller .this) (.nat 1)))]
#guard parseOracleParts (name := "") "You draw a card and lose 1 life." ==
  some [.actions [
    .sequence [
      .draw (.controller .this) 1,
      .loseLife (.controller .this) 1]]]
#guard parseOracleParts (name := "") "You draw two cards and lose 1 life." ==
  some [.actions
     [.draw (.controller .this) (.nat 2),
      .loseLife
        (.controller .this)
        (.nat 1)]]
#guard parseOracleParts (name := "") "You draw a card and lose 2 life." ==
  some [.actions
     [.draw (.controller .this) (.nat 1),
      .loseLife
        (.controller .this)
        (.nat 2)]]
#guard parseOracleParts (name := "") "Amass Goblins 2." ==
  some [.actions [.keyword (.controller .this) (.amass .goblin (.nat 2))]]
#guard parseOracleParts (name := "")
  "Amass Goblins 2. (Put two +1/+1 counters on an Army you control. It's also a Goblin. If you don't control an Army, create a 0/0 black Goblin Army creature token first.)" ==
  parseOracleParts (name := "") "Amass Goblins 2."
#guard parseOracleParts (name := "") "Amass Goblin 2." == none
#guard parseOracleParts (name := "") "Amass Goblins 0." == none
#guard parseOracleParts (name := "")
  "You draw a card and lose 1 life.\nAmass Goblins 2." ==
  some [.actions [
    .draw (.controller .this) 1,
    .loseLife (.controller .this) 1,
    .keyword (.controller .this) (.amass .goblin (.nat 2))]]
#guard parseOracleParts (name := "")
  "Return up to one target creature card from your graveyard to your hand." ==
  some [.actions [
    .returnToHand
      (.targets 1 (.range 0 1)
        (.intersection [
          .inGraveyard,
          .cardType .creature,
          .owner (.controller .this)]))]]
#guard parseOracleParts (name := "")
  "Return up to one target creature from your graveyard to your hand." == none
#guard parseOracleParts (name := "")
  "Return target creature card from your graveyard to your hand." ==
  some [.actions
     [.returnToHand
        (.target
          1
          (.intersection
            [.inGraveyard,
             .cardType .creature,
             .owner (.controller .this)]))]]
#guard parseOracleParts (name := "")
  "Return up to one target creature card from your graveyard to your hand.\nAmass Goblins 3." ==
  some [.actions [
    .returnToHand
      (.targets 1 (.range 0 1)
        (.intersection [
          .inGraveyard,
          .cardType .creature,
          .owner (.controller .this)])),
    .keyword (.controller .this) (.amass .goblin (.nat 3))]]
#guard parseOracleParts (name := "")
  "Counter target spell. If that spell's mana value was 2 or less, recruit." ==
  some [.actions [
    .defineValueVariable 1 (.greatestManaValue (.target 1 .spell)),
    .counter (.targetReference 1),
    .if (.lessOrEqual (.variable 1) 2)
      [.keyword (.controller .this) .recruit]]]
#guard parseOracleParts (name := "")
  "Counter target spell. If that spell's mana value was 2 or less, recruit. (Draw a card, then discard a card. If you discarded a nonland card, create a 1/1 white Human Soldier creature token.)" ==
  parseOracleParts (name := "")
    "Counter target spell. If that spell's mana value was 2 or less, recruit."
#guard parseOracleParts (name := "")
  "Counter target spell. If that spell's mana value was 2 or less, draw a card." == none
#guard parseOracleParts (name := "")
  "Counter target spell. If that spell's mana value was 0 or less, recruit." == none
#guard parseOracleParts (name := "")
  "Counter target creature. If that spell's mana value was 2 or less, recruit." == none
#guard parseOracleParts (name := "")
  "Whenever an artifact you control enters, draw a card." ==
  some [.ability (.triggered
    (.enter (.intersection [
      .permanent, .cardType .artifact, .controlled (.controller .this)]))
    (.draw (.controller .this) 1))]
#guard parseOracleParts (name := "")
  "Whenever an artifact you control enters, draw two cards." ==
  some [.ability
     (.triggered
       (.enter
         (.intersection
           [.permanent,
            .cardType .artifact,
            .controlled (.controller .this)]))
       (.draw (.controller .this) (.nat 2)))]
#guard parseOracleParts (name := "")
  "Whenever a creature you control enters, draw a card." ==
  some [.ability
     (.triggered
       (.enter
         (.intersection
           [.permanent,
            .cardType .creature,
            .controlled (.controller .this)]))
       (.draw (.controller .this) (.nat 1)))]
#guard parseOracleParts (name := "Chief Warg's Company")
  "This creature can't attack unless you control two or more other Wolves." ==
  some [.ability (.static (.if
    (.less
      (.count (.intersection [
        .not .this, .permanent, .subtype .wolf, .controlled (.controller .this)]))
      (Value.nat 2))
    [.forbid (.attack .this .all)]))]
#guard parseOracleParts (name := "Chief Warg's Company")
  "Chief Warg's Company can't attack unless you control two or more other Wolves." ==
  parseOracleParts (name := "Chief Warg's Company")
    "This creature can't attack unless you control two or more other Wolves."
#guard parseOracleParts (name := "Gandalf")
  "Chief Warg's Company can't attack unless you control two or more other Wolves." == none
#guard parseOracleParts (name := "")
  "This creature can't attack unless you control two or more other Wolf." == none
#guard parseOracleParts (name := "")
  "This creature can't attack unless you control two other Wolves." == none
#guard parseOracleParts (name := "")
  "At the beginning of your upkeep, create a 2/2 green Wolf creature token." ==
  some [.ability (.triggered
    (.upkeep (.controller .this))
    (.createTokens (.controller .this) 1 [
      .type .creature, .subtype .wolf, .colorIndicator [.green],
      .power 2, .toughness 2]))]
#guard parseOracleParts (name := "")
  "At the beginning of your upkeep, create two 2/2 green Wolf creature tokens." ==
  some [.ability (.triggered
    (.upkeep (.controller .this))
    (.createTokens (.controller .this) 2 [
      .type .creature, .subtype .wolf, .colorIndicator [.green],
      .power 2, .toughness 2]))]
#guard parseOracleParts (name := "")
  "At the beginning of your upkeep, create a 2/2 green Wolf creature tokens." == none
#guard parseOracleParts (name := "")
  "When this Equipment enters, create a 2/2 red Dwarf creature token, then attach this Equipment to it." ==
  some [.ability (.triggered
    (.enter .this)
    (.sequence [
      .actionId 1
        (.createTokens (.controller .this) 1 [
          .type .creature, .subtype .dwarf, .colorIndicator [.red],
          .power 2, .toughness 2]),
      .attach .this (.wasCreatedByAction 1)]))]
#guard parseOracleParts (name := "")
  "When this Equipment enters, create two 2/2 red Dwarf creature tokens, then attach this Equipment to it." ==
  none
#guard parseOracleParts (name := "")
  "When this Equipment enters, amass Goblins 1, then attach this Equipment to the amassed Army." ==
  some [.ability (.triggered
    (.enter .this)
    (.sequence [
      .actionId 1 (.keyword (.controller .this) (.amass .goblin (.nat 1))),
      .attach .this (.wasObjectOfAction 1)]))]
#guard parseOracleParts (name := "")
  "When this Equipment enters, amass Goblins 1, then attach this Equipment to the amassed Army. (To amass Goblins 1, put a +1/+1 counter on an Army you control. It's also a Goblin. If you don't control an Army, create a 0/0 black Goblin Army creature token first.)" ==
  parseOracleParts (name := "")
    "When this Equipment enters, amass Goblins 1, then attach this Equipment to the amassed Army."
#guard parseOracleParts (name := "")
  "Put a +1/+1 counter on target creature you control. If this spell was cast from a graveyard, also put a +1/+1 counter on each other creature you control." ==
  some [.actions [
    .putCounter
      (.target 1 (.intersection [
        .permanent, .cardType .creature, .controlled (.controller .this)]))
      .plusOnePlusOne 1,
    .if (.happened (.castSpellFromGraveyard .this) .gameStart)
      [.putCounter
        (.intersection [
          .not (.targetReference 1),
          .permanent, .cardType .creature, .controlled (.controller .this)])
        .plusOnePlusOne 1]]]
#guard parseOracleParts (name := "") "Flashback {4}{W}" ==
  some [.ability (.keywordWithCost .flashback [.mana [.generic 4, .mono .white]])]
#guard parseOracleParts (name := "")
  "Flashback {4}{W} (You may cast this card from your graveyard for its flashback cost. Then exile it.)" ==
  parseOracleParts (name := "") "Flashback {4}{W}"
#guard parseOracleParts (name := "") "Flashback" == none
#guard parseOracleParts (name := "") "Teamwork 2" ==
  some [.ability (.keyword (.teamwork 2))]
#guard parseOracleParts (name := "")
  "Teamwork 2 (As an additional cost to cast this spell, you may tap any number of creatures you control with total power 2 or more.)" ==
  parseOracleParts (name := "") "Teamwork 2"
#guard parseOracleParts (name := "") "Teamwork" == none
#guard parseOracleParts (name := "") "Teamwork 0" == none
#guard parseOracleParts (name := "") "Improvise" ==
  some [.ability (.keyword .improvise)]
#guard parseOracleParts (name := "")
  "Improvise (Your artifacts can help cast this spell. Each artifact you tap after you're done activating mana abilities pays for {1}.)" ==
  parseOracleParts (name := "") "Improvise"
#guard parseOracleParts (name := "") "Kicker {2}{W}" ==
  some [.ability (.keywordWithCost .kicker [.mana [.generic 2, .mono .white]])]
#guard parseOracleParts (name := "")
  "Kicker {2}{W}{W} (You may pay an additional {2}{W}{W} as you cast this spell.)" ==
  some [.ability (.keywordWithCost .kicker [.mana [.generic 2, .mono .white, .mono .white]])]
#guard parseOracleParts (name := "") "Kicker" == none
#guard parseOracleParts (name := "") "Affinity for Elves" ==
  some [.ability (.keyword (.affinity [] [.elf]))]
#guard parseOracleParts (name := "")
  "Affinity for Elves (This spell costs {1} less to cast for each Elf you control.)" ==
  parseOracleParts (name := "") "Affinity for Elves"
#guard parseOracleParts (name := "") "Affinity for artifacts" ==
  some [.ability (.keyword (.affinity [.artifact] []))]
#guard parseOracleParts (name := "") "Affinity for Elf" == none
#guard parseOracleParts (name := "") "Affinity" == none
#guard parseOracleParts (name := "") "Boast" ==
  some [.ability (.keyword .boast)]
#guard parseOracleParts (name := "") "Cascade, cascade" ==
  some [.ability (.keyword .cascade), .ability (.keyword .cascade)]
#guard parseOracleParts (name := "")
  "Cascade, cascade (When you cast this spell, exile cards from the top of your library until you exile a nonland card that costs less. You may cast it without paying its mana cost. Put the exiled cards on the bottom of your library in a random order. Then do it again.)" ==
  parseOracleParts (name := "") "Cascade, cascade"
#guard parseOracleParts (name := "") "Extort" ==
  some [.ability (.keyword .extort)]
#guard parseOracleParts (name := "") "Sneak {1}{B}{B}" ==
  some [.ability (.keywordWithCost .sneak [.mana [.generic 1, .mono .black, .mono .black]])]
#guard parseOracleParts (name := "")
  "Sneak {1}{B}{B} (You may cast this spell for {1}{B}{B} if you also return an unblocked attacker you control to hand during the declare blockers step. She enters tapped and attacking.)" ==
  parseOracleParts (name := "") "Sneak {1}{B}{B}"
#guard parseOracleParts (name := "") "Sneak" == none
#guard parseOracleParts (name := "") "Gift a Food" ==
  some [.ability (.keyword (.gift .food))]
#guard parseOracleParts (name := "")
  "Gift a Food (You may promise an opponent a gift as you cast this spell. If you do, they create a Food token before its other effects.)" ==
  parseOracleParts (name := "") "Gift a Food"
#guard parseOracleParts (name := "") "Gift a card" ==
  some [.ability (.keyword (.gift .card))]
#guard parseOracleParts (name := "") "Gift a tapped Fish" ==
  some [.ability (.keyword (.gift .tappedFish))]
#guard parseOracleParts (name := "") "Gift an extra turn" ==
  some [.ability (.keyword (.gift .extraTurn))]
#guard parseOracleParts (name := "") "Gift a Treasure" ==
  some [.ability (.keyword (.gift .treasure))]
#guard parseOracleParts (name := "")
  "Gift a Treasure (You may promise an opponent a gift as you cast this spell. If you do, they create a Treasure token before its other effects. It's an artifact with \"{T}, Sacrifice this token: Add one mana of any color.\")" ==
  parseOracleParts (name := "") "Gift a Treasure"
#guard parseOracleParts (name := "") "Gift an Octopus" ==
  some [.ability (.keyword (.gift .octopus))]
#guard parseOracleParts (name := "") "Gift" == none
#guard parseOracleParts (name := "")
  "Return target spell to its owner's hand. If the gift was promised, players can't cast spells this turn." ==
  some [.actions [
    .returnToHand (.target 1 .spell),
    .if (.happened (.giftPromised .this) .gameStart) [
      .continuous [.forbid (.castSpell .all)] .endOfTurn]]]
#guard parseOracleParts (name := "")
  "Draw a card. If this spell was cast from a graveyard, draw two cards instead." ==
  some [.actions [
    .ifElse (.happened (.castSpellFromGraveyard .this) .gameStart)
      [.draw (.controller .this) 2]
      [.draw (.controller .this) 1]]]
#guard parseOracleParts (name := "")
  "Amass Goblins 1. If this spell was cast from a graveyard, amass Goblins 3 instead." ==
  some [.actions [
    .ifElse (.happened (.castSpellFromGraveyard .this) .gameStart)
      [.keyword (.controller .this) (.amass .goblin 3)]
      [.keyword (.controller .this) (.amass .goblin 1)]]]
#guard parseOracleParts (name := "") "Draw a card." ==
  some [.actions
     [.draw (.controller .this) (.nat 1)]]
#guard parseOracleParts (name := "")
  "Draw a card. If this spell was cast from a graveyard, amass Goblins 3 instead." == none
#guard parseOracleParts (name := "")
  "Put two +1/+1 counters on target creature you control. Then it fights target creature an opponent controls." ==
  some [.actions [
    .putCounter
      (.target 1 (.intersection [
        .permanent, .cardType .creature, .controlled (.controller .this)]))
      .plusOnePlusOne 2,
    .fight (.targetReference 1)
      (.target 2 (.intersection [
        .permanent, .cardType .creature,
        .controlled (.opponent (.controller .this))]))]]

end Mtg.Engine
