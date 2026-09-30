import Mtg.Engine.Card.OracleParse.Parse

/-!
# `parseOracleParts` guards, catalog cards

The last part of the `parseOracleParts` regression tests. Add a new guard
here.
-/

namespace Mtg.Engine

open OracleParts

#guard parseOracleParts (name := "") "Enchant creature" ==
  some [.ability (.keywordWithTarget .enchant 1
    (.intersection [.permanent, .cardType .creature]))]
#guard parseOracleParts (name := "") "Ward {3}" ==
  some [.ability (.keywordWithCost .ward [.mana [.generic 3]])]
#guard parseOracleParts (name := "") "Ward {U}" == none
#guard parseOracleParts (name := "")
  "Enchanted creature gets +2/+2 and has flying." ==
  some [
    .ability (.static (.addPower (.hostOf .this) (Value.int 2))),
    .ability (.static (.addToughness (.hostOf .this) (Value.int 2))),
    .ability (.static (.gainAbility (.hostOf .this) (.keyword .flying)))]
#guard parseOracleParts (name := "")
  "Equipped creature gets +2/+2 and has ward {1}." ==
  some [
    .ability (.static (.addPower (.hostOf .this) (Value.int 2))),
    .ability (.static (.addToughness (.hostOf .this) (Value.int 2))),
    .ability (.static (.gainAbility (.hostOf .this)
      (.keywordWithCost .ward [.mana [.generic 1]])))]
#guard parseOracleParts (name := "Gandalf, Wandering Wizard")
  "{6}: Gandalf's owner shuffles him into their library and draws three cards." ==
  some [.ability (.activated [.mana [.generic 6]]
    (.sequence [
      .defineSelectorVariable 1 (.owner (.source .this)),
      .shuffleIntoOwnersLibrary (.source .this),
      .draw (.variable 1) 3]))]
#guard parseOracleParts (name := "")
  "{2}{W/U}{W/U}: Return this card from your graveyard to the battlefield attached to target creature you control with power 1 or less. Activate only as a sorcery." ==
  some [.ability (.graveyardActivatedIf
    (.timeToCastSorcery (.controller .this))
    [.mana [.generic 2, .hybrid .white .blue, .hybrid .white .blue]]
    (.putOntoBattlefieldInState
      (.intersection [.inGraveyard, .source .this])
      [.attachedTo
        (.target 1 (.intersection [
          .permanent, .cardType .creature, .controlled (.controller .this),
          .powerAtMost (Value.int 1)]))]))]
#guard parseOracleParts (name := "")
  "When this Equipment enters, attach it to target Dwarf you control." ==
  some [.ability (.triggered (.enter .this)
    (.attach .this
      (.target 1 (.intersection [
        .permanent, .cardType .creature, .subtype .dwarf,
        .controlled (.controller .this)]))))]
#guard parseOracleParts (name := "")
  "Each creature you control with a +1/+1 counter on it has menace." ==
  some [.ability (.static (.gainAbility
    (.intersection [
      .permanent, .cardType .creature, .controlled (.controller .this),
      .hasCounter .plusOnePlusOne])
    (.keyword .menace)))]
#guard parseOracleParts (name := "")
  "At the beginning of your end step, draw a card." ==
  some [.ability (.triggered (.endStep (.controller .this))
    (.draw (.controller .this) 1))]
#guard parseOracleParts (name := "")
  "At the beginning of your end step, draw two cards." ==
  some [.ability (.triggered (.endStep (.controller .this))
    (.draw (.controller .this) 2))]
#guard parseOracleParts (name := "")
  "At the beginning of your end step, draw two." == none
#guard parseOracleParts (name := "")
  "Search your library for a legendary creature card, reveal it, put it into your hand, then shuffle." ==
  some [.actions [
    .searchLibraryThenShuffle (.controller .this) [
      .defineSelectorVariable 1
        (.selected (.controller .this) (.range 1 1)
          (.intersection [
            .inLibrary, .cardType .creature, .supertype .legendary])),
      .reveal (.variable 1),
      .returnToHand (.variable 1)]]]
#guard parseOracleParts (name := "") "Creatures you control get +1/+1." ==
  some [
    .ability (.static (.addPower
      (.intersection [
        .permanent, .cardType .creature, .controlled (.controller .this)])
      (Value.int 1))),
    .ability (.static (.addToughness
      (.intersection [
        .permanent, .cardType .creature, .controlled (.controller .this)])
      (Value.int 1)))]
#guard parseOracleParts (name := "")
  "This creature has haste as long as you control another Goblin." ==
  some [.ability (.static (.if
    (.any (.intersection [
      .not .this, .permanent, .subtype .goblin,
      .controlled (.controller .this)]))
    [.gainAbility .this (.keyword .haste)]))]
#guard parseOracleParts (name := "Bolg's Company")
  "{T}, Sacrifice another Goblin: Add {B}{R}." ==
  some [.ability (.activated
    [.tapSymbol,
      .sacrificeCount
        (.intersection [
          .not .this, .permanent, .subtype .goblin,
          .controlled (.controller .this)])
        1]
    (.addMana (.controller .this) [.colored .black, .colored .red]))]
#guard parseOracleParts (name := "") "{T}: Add {G}." ==
  some [.ability
     (.activated
       [.tapSymbol]
       (.addMana
         (.controller .this)
         [.colored .green]))]
#guard parseOracleParts (name := "") "{T}, Sacrifice another: Add {B}{R}." == none
#guard parseOracleParts (name := "Nori, Teller of Tales")
  "Whenever Nori attacks, target attacking creature gains first strike until end of turn." ==
  some [.ability (.triggered (.attack .this .all)
    (.continuous
      [.gainAbility
        (.target 1 (.intersection [
          .permanent, .cardType .creature, .attacking .all]))
        (.keyword .firstStrike)]
      .endOfTurn))]
#guard parseOracleParts (name := "Gandalf")
  "Whenever Nori attacks, target attacking creature gains first strike until end of turn." ==
  none
#guard parseOracleParts (name := "")
  "This spell costs {X} less to cast, where X is the total power of creatures you control with flying." ==
  some [.ability (.stackStatic
    (.reduceCostWithX .this [.mana [.x]]
      (.totalPower (.intersection [
        .permanent, .cardType .creature, .keyword .flying,
        .controlled (.controller .this)]))))]
#guard parseOracleParts (name := "")
  "This spell costs {2} less to cast, where X is the total power of creatures you control with flying." ==
  none
#guard parseOracleParts (name := "Thrór's Map")
  "When Thrór's Map enters, search your library for a basic land card, reveal it, put it into your hand, then shuffle." ==
  some [.ability (.triggered (.enter .this)
    (.searchLibraryThenShuffle (.controller .this) [
      .defineSelectorVariable 1
        (.selected (.controller .this) (.range 1 1)
          (.intersection [.inLibrary, .cardType .land, .supertype .basic])),
      .reveal (.variable 1),
      .returnToHand (.variable 1)]))]
#guard parseOracleParts (name := "")
  "{2}, {T}: Draw a card, then discard a card." ==
  some [.ability (.activated
    [.mana [.generic 2], .tapSymbol]
    (.sequence [
      .draw (.controller .this) 1,
      .discard (.controller .this) 1]))]
#guard parseOracleParts (name := "The Black Arrow")
  "When The Black Arrow enters, it deals 1 damage to any target. If a Dragon is dealt damage this way, destroy it." ==
  some [.ability (.triggered (.enter .this)
    (.sequence [
      .actionId 1
        (.dealDamage (.source .this) (.target 1 .all) 1),
      .if (.anySubtype (.wasObjectOfAction 1) .dragon)
        [.destroy (.wasObjectOfAction 1)]]))]
#guard parseOracleParts (name := "Gandalf")
  "When The Black Arrow enters, it deals 1 damage to any target. If a Dragon is dealt damage this way, destroy it." ==
  none
#guard parseOracleParts (name := "Smaug the Magnificent")
  "Whenever Smaug attacks, he deals damage equal to the number of Treasures you control to any target." ==
  some [.ability (.triggered (.attack .this .all)
    (.dealDamage (.source .this) (.target 1 .all)
      (.count (.intersection [
        .permanent, .cardType .artifact, .subtype .treasure,
        .controlled (.controller .this)]))))]
#guard parseOracleParts (name := "")
  "At the beginning of your upkeep, create a Treasure token." ==
  some [.ability (.triggered (.upkeep (.controller .this))
    (.createTokens (.controller .this) 1 PredefinedToken.treasureToken))]
#guard parseOracleParts (name := "")
  "Whenever an opponent casts their first noncreature spell each turn, you recruit." ==
  some [.ability (.triggered
    (.ordinal 1 .turnStart
      (.castSpell (.intersection [
        .spell, .not (.cardType .creature),
        .controlled (.opponent (.controller .this))])))
    (.keyword (.controller .this) .recruit))]
#guard parseOracleParts (name := "Ori, Keeper of Songs")
  "As long as you have an enduring story, Ori gets +1/+0 and has vigilance." ==
  some [.ability (.static (.if (.enduringStory (.controller .this))
    [.addPower .this (Value.int 1), .gainAbility .this (.keyword .vigilance)]))]
#guard parseOracleParts (name := "Gandalf")
  "As long as you have an enduring story, Ori gets +1/+0 and has vigilance." == none
#guard parseOracleParts (name := "Ori, Keeper of Songs")
  "As long as you have an enduring story, Ori gets +0/+0." == none
#guard parseOracleParts (name := "Óin the Brave")
  "As long as you have an enduring story, Óin gets +1/+0 and has haste." ==
  some [.ability (.static (.if (.enduringStory (.controller .this))
    [.addPower .this (Value.int 1), .gainAbility .this (.keyword .haste)]))]
#guard parseOracleParts (name := "Óin the Brave")
  "{1}, {T}, Discard a card: Draw a card." ==
  some [.ability (.activated
    [.mana [.generic 1], .tapSymbol,
      .discard
        (.selected
          (.controller .this)
          (.range 1 1)
          (.intersection [.inHand, .owner (.controller .this)]))]
    (.draw (.controller .this) 1))]
#guard parseOracleParts (name := "Óin the Brave")
  "{1}, {T}: Draw a card." ==
  some [.ability
     (.activated
       [.mana [.generic 1], .tapSymbol]
       (.draw (.controller .this) (.nat 1)))]
#guard parseOracleParts (name := "Fíli the Pathfinder")
  "As long as you have an enduring story, creatures you control get +1/+1." ==
  some [.ability (.static (.if (.enduringStory (.controller .this))
    [.addPower creaturesYouControl (Value.int 1),
      .addToughness creaturesYouControl (Value.int 1)]))]
#guard parseOracleParts (name := "Fíli the Pathfinder")
  "As long as you have an enduring story, creatures you control get +0/+0." == none
#guard parseOracleParts (name := "Thorin Oakenshield")
  "As long as you have an enduring story, artifacts and creatures you control have ward {1}." ==
  some [.ability (.static (.if (.enduringStory (.controller .this))
    [.gainAbility
      (permanentWith [.artifact, .creature] [youControl])
      (.keywordWithCost .ward [.mana [.generic 1]])]))]
#guard parseOracleParts (name := "Thorin Oakenshield")
  "As long as you have an enduring story, artifacts and creatures you control have ward {0}." ==
  none
#guard parseOracleParts (name := "Dáin, Lord of the Iron Hills")
  "As long as you have an enduring story, creatures can't attack you unless their controller pays {1} for each of those creatures." ==
  some [.ability (.static (.if (.enduringStory (.controller .this))
    [.cantAttackUnlessPays
      (permanentWith [.creature])
      (.controller .this)
      [.mana [.generic 1]]]))]
#guard parseOracleParts (name := "Bombur, Gentle Dreamer")
  "Bombur doesn't untap during your untap step unless you have an enduring story." ==
  some [.ability (.static
    (.if (.not (.enduringStory (.controller .this)))
      [.doesntUntap .this]))]
#guard parseOracleParts (name := "Gandalf")
  "Bombur doesn't untap during your untap step unless you have an enduring story." == none
#guard parseOracleParts (name := "Fíli the Pathfinder")
  "Whenever Fíli or another nontoken Dwarf you control enters, create a 2/2 red Dwarf creature token." ==
  some [.ability (.triggered
    (.or
      (.enter .this)
      (.enter
        (.intersection [
          .not .this,
          .not .token,
          .permanent,
          .cardType .creature,
          .subtype .dwarf,
          youControl])))
    (.createTokens (.controller .this) 1 [
      .type .creature,
      .subtype .dwarf,
      .colorIndicator [.red],
      .power 2,
      .toughness 2]))]
#guard parseOracleParts (name := "Gandalf")
  "Whenever Fíli or another nontoken Dwarf you control enters, create a 2/2 red Dwarf creature token." ==
  none
#guard parseOracleParts (name := "Old Thrush")
  "When this creature enters, you gain 2 life. You may search your library for a basic land card, reveal it, then shuffle and put that card on top." ==
  some [.ability (.triggered (.enter .this)
    (.sequence [
      .gainLife (.controller .this) 2,
      .optional (.controller .this)
        (.sequence [
          .searchLibraryThenShuffle (.controller .this) [
            .defineSelectorVariable 1
              (.selected (.controller .this) (.range 1 1)
                (.intersection [.inLibrary, .cardType .land, .supertype .basic])),
            .reveal (.variable 1),
            .holdOutInLibrary (.variable 1)],
          .putOnTopOfLibrary (.variable 1)])]))]
#guard parseOracleParts (name := "Old Thrush")
  "When this creature enters, you gain 2 life." ==
  some [.ability (.triggered (.enter .this) (.gainLife (.controller .this) 2))]
#guard parseOracleParts (name := "Old Thrush")
  "When this creature enters, you gain 2 life. Draw a card." ==
  some [.ability
     (.triggered
       (.enter .this)
       (.sequence
         [.gainLife
            (.controller .this)
            (.nat 2),
          .draw
            (.controller .this)
            (.nat 1)]))]
#guard parseOracleParts (name := "Gandalf")
  "When Old Thrush enters, you gain 2 life. You may search your library for a basic land card, reveal it, then shuffle and put that card on top." ==
  none
#guard parseOracleParts (name := "Most Decrepit Old Bird")
  "Threshold — This creature gets +1/+1 as long as there are seven or more cards in your graveyard." ==
  some [.ability (.static (.if
    (.greaterOrEqual
      (.count (.intersection [.inGraveyard, .owner (.controller .this)]))
      7)
    [.addPower .this (Value.int 1), .addToughness .this (Value.int 1)]))]
#guard parseOracleParts (name := "Most Decrepit Old Bird")
  "This creature gets +1/+1 as long as there are seven or more cards in your graveyard." ==
  parseOracleParts (name := "Most Decrepit Old Bird")
    "Threshold — This creature gets +1/+1 as long as there are seven or more cards in your graveyard."
#guard parseOracleParts (name := "Most Decrepit Old Bird")
  "Threshold — This creature gets +0/+0 as long as there are seven or more cards in your graveyard." ==
  none
#guard parseOracleParts (name := "Most Decrepit Old Bird")
  "Threshold — This creature gets +1/+1 as long as there are six or more cards in your graveyard." ==
  none
#guard parseOracleParts (name := "Gandalf")
  "Threshold — Most Decrepit Old Bird gets +1/+1 as long as there are seven or more cards in your graveyard." ==
  none
#guard parseOracleParts (name := "")
  "Mill four cards, then put an instant or sorcery card from among them into your hand." ==
  some [.actions [.sequence [
    .actionId 1 (.mill (.controller .this) 4),
    .returnToHand
      (.selected (.controller .this) (.range 1 1)
        (.intersection [
          .wasObjectOfAction 1,
          .union [.cardType .instant, .cardType .sorcery]]))]]]
#guard parseOracleParts (name := "")
  "Mill one cards, then put an instant or sorcery card from among them into your hand." == none
#guard parseOracleParts (name := "")
  "Mill four cards, then put a creature card from among them into your hand." == none
#guard parseOracleParts (name := "")
  "Exile two target creatures and/or lands you control, then return them to the battlefield under their owner's control." ==
  some [.actions [.sequence [
    .actionId 1 (.exile (.targets 1 (.range 2 2)
      (.intersection [
        .permanent,
        .union [.cardType .creature, .cardType .land],
        .controlled (.controller .this)]))),
    .putOntoBattlefieldInState (.wasCreatedByAction 1)
      [.controlled (.owner (.wasCreatedByAction 1))]]]]
#guard parseOracleParts (name := "")
  "Exile one target creatures and/or lands you control, then return them to the battlefield under their owner's control." ==
  none
#guard parseOracleParts (name := "Pinecone Strike")
  "Choose one or both —\n• Pinecone Strike deals 3 damage to target creature. If that creature would die this turn, exile it instead.\n• Destroy target artifact token." ==
  some [.actions [.chooseUniqueModes (.range 1 2) [
    .sequence [
      .dealDamage .this
        (.target 1 (.intersection [.permanent, .cardType .creature])) 3,
      .continuous
        [.replace (.putToGraveyard (.targetReference 1)) [.exile .replacingObject]]
        .endOfTurn],
    .destroy (.target 2 artifactTokenPermanent)]]]
#guard parseOracleParts (name := "Other")
  "Pinecone Strike deals 3 damage to target creature. If that creature would die this turn, exile it instead." ==
  none
#guard parseOracleParts (name := "")
  "Mill four cards, then put up to two land cards from among them into your hand." ==
  some [.actions [.sequence [
    .actionId 1 (.mill (.controller .this) 4),
    .returnToHand
      (.selected (.controller .this) (.range 0 2)
        (.intersection [.wasObjectOfAction 1, .cardType .land]))]]]
#guard parseOracleParts (name := "")
  "Mill one cards, then put up to two land cards from among them into your hand." == none
#guard parseOracleParts (name := "Easy Pickings")
  "Easy Pickings deals 1 damage to each creature your opponents control." ==
  some [.actions [.dealDamage .this eachOppCreature 1]]
#guard parseOracleParts (name := "Desolation of Smaug")
  "Desolation of Smaug deals 3 damage to each non-Dragon creature.\nAdd four mana in any combination of colors. Spend this mana only to cast Dragon spells." ==
  some [.actions [
    .dealDamage .this eachNonDragonCreature 3,
    .actionId 1 (.addManaInAnyCombination
      (.controller .this) ManaSymbol.anyColor 4),
    .continuous
      [.forbid (.spendManaCreatedByAction 1 (.not (.castSpell (.subtype .dragon))))]
      .endOfTurn]]
#guard parseOracleParts (name := "Thranduil, Sindarin Liege")
  "Other Elves you control get +1/+1." ==
  some [
    .ability (.static (.addPower
      (.intersection [
        .not .this, .permanent, .cardType .creature, .subtype .elf, youControl])
      (Value.int 1))),
    .ability (.static (.addToughness
      (.intersection [
        .not .this, .permanent, .cardType .creature, .subtype .elf, youControl])
      (Value.int 1)))]
#guard parseOracleParts (name := "The Lonely Mountain")
  "({T}: Add {R}.)\nThis land enters tapped unless you control an Equipment." ==
  some [.ability (.everywhereStatic (.if (.not (.any equipmentYouControl))
    [.replace (.enter .this) [.putOntoBattlefieldInState .this [.tapped]]]))]
#guard parseOracleParts (name := "Glóin the Mighty")
  "At the beginning of your first main phase, add {R}{R}." ==
  some [.ability (.triggered (.precombatMainPhase (.controller .this))
    (.addMana (.controller .this) [.colored .red, .colored .red]))]
#guard parseOracleParts (name := "Iron Hills Stalwart")
  "When this creature enters, attach target Equipment you control to up to one target creature you control." ==
  some [.ability (.triggered (.enter .this)
    (.attach
      (.target 1 equipmentYouControl)
      (.targets 2 (.range 0 1) creaturesYouControl)))]
#guard parseOracleParts (name := "Old Fat Spider")
  "This creature can't be blocked by creatures with power 2 or less.\nWhenever this creature becomes the target of a spell or ability an opponent controls, draw a card." ==
  some [
    .ability (.static (.forbid (.block
      (.intersection [.permanent, .cardType .creature, .powerAtMost (Value.int 2)])
      .this))),
    .ability (.triggered
      (.target spellOrAbilityOpponentControls .this)
      (.draw (.controller .this) 1))]
#guard parseOracleParts (name := "Great Gilded Boat")
  "Whenever you attack, recruit.\nCrew 2" ==
  some [
    .ability (.triggered
      (.attackSimultaneously creaturesYouControl .all [])
      (.keyword (.controller .this) .recruit)),
    .ability (.keyword (.crew 2))]
#guard parseOracleParts (name := "") "Crew 0" == none
#guard parseOracleParts (name := "Dwarven Mauler")
  "Equip abilities you activate that target this creature cost {2} less to activate." ==
  some [.ability (.static (.reduceCost
    (.intersection [
      Selector.keywordAbility .equip,
      .hasTarget .this,
      .controlled (.controller .this)])
    [.mana [.generic 2]]))]
#guard parseOracleParts (name := "")
  "Equip abilities you activate that target this creature cost {0} less to activate." ==
  none
#guard parseOracleParts (name := "My Precious")
  "Equipped creature has hexproof and can't be blocked.\nEquip—{2}, Pay 2 life." ==
  some [
    .ability (.static (.gainAbility (.hostOf .this) (.keyword .hexproof))),
    .ability (.static (.forbid (.block .any (.hostOf .this)))),
    .ability (.keywordWithCost .equip [.mana [.generic 2], .life 2])]
#guard parseOracleParts (name := "My Precious")
  "Equipped creature has hexproof and can't be blocked.\nEquip—{2}, Pay 2 life.\n//ADV//\nAllure of Power {1}{B}\nInstant — Adventure\nAs an additional cost to cast this spell, sacrifice a creature.\nDraw two cards. (Then exile this card. You may cast the artifact later from exile.)" ==
  some [
    .ability (.static (.gainAbility (.hostOf .this) (.keyword .hexproof))),
    .ability (.static (.forbid (.block .any (.hostOf .this)))),
    .ability (.keywordWithCost .equip [.mana [.generic 2], .life 2]),
    .alternative [
      .name "Allure of Power",
      .manaCost [.generic 1, .mono .black],
      .type .instant,
      .subtype .adventure,
      .ability (.stackStatic (.additionalCost .this
        [.sacrificeCount (permanentWith [.creature]) 1])),
      .actions [.draw (.controller .this) 2]]]
#guard parseOracleParts (name := "")
  "Flying\n//ADV//\nSpew Flame {4}{R}\nSorcery — Adventure\nDraw two cards." == none
#guard parseOracleParts (name := "Troop of Ponies")
  "{2}, {T}, Sacrifice this creature: Search your library for up to two basic land cards, reveal them, put one onto the battlefield tapped and the other into your hand, then shuffle." ==
  some [.ability (.activated
    [.mana [.generic 2], .tapSymbol, .sacrifice .this]
    (.searchLibraryThenShuffle
      (.controller .this)
      [
        .defineSelectorVariable 1
          (.selected
            (.controller .this)
            (.range 0 2)
            (.intersection [
              .inLibrary, .cardType .land, .supertype .basic])),
        .reveal (.variable 1),
        .putOntoBattlefieldInState
          (.selected (.controller .this) (.range 1 1) (.variable 1))
          [.tapped],
        .returnToHand (.variable 1)]))]
#guard parseOracleParts (name := "")
  "{2}, {T}, Sacrifice this creature: Search your library for up to one basic land card, reveal it, put it onto the battlefield tapped, then shuffle." ==
  none
#guard parseOracleParts (name := "Elven Raft-Steerer")
  "Landfall — Whenever a land you control enters, choose one —\n• Tap target creature an opponent controls.\n• Untap target creature you control." ==
  some [.ability (.triggered
    (.enter landsYouControl)
    (.chooseUniqueModes (.range 1 1) [
      .tap (.target 1 (permanentWith [.creature]
        [.controlled (.opponent (.controller .this))])),
      .untap (.target 2 (permanentWith [.creature] [youControl]))]))]
#guard parseOracleParts (name := "")
  "Landfall — Whenever a land you control enters, choose one —" == none
#guard parseOracleParts (name := "Mirkwood Meditator")
  "Landfall — Whenever a land you control enters, you may have this creature's base power and toughness become 4/2 until end of turn." ==
  some [.ability (.triggered
    (.enter landsYouControl)
    (.optional (.controller .this) (.continuous
      [.setBasePower (.source .this) (Value.int 4),
        .setBaseToughness (.source .this) (Value.int 2)]
      .endOfTurn)))]
#guard parseOracleParts (name := "Mirkwood Nurturer")
  "When this creature enters, return up to one other target permanent you control to its owner's hand. If you do, put a +1/+1 counter on this creature." ==
  some [.ability (.triggered
    (.enter .this)
    (.sequence [
      .actionId 1
        (.returnToHand
          (.targets 1 (.range 0 1)
            (.intersection [.not .this, .permanent, youControl]))),
      .if (.happened (.actionWithId 1) .gameStart)
        [.putCounter (.source .this) .plusOnePlusOne 1]]))]
#guard parseOracleParts (name := "Kíli the Resourceful")
  "As long as you have an enduring story, you may pay {0} rather than pay the equip cost of the first equip ability you activate each turn.\nWhenever another Dwarf or Equipment you control enters, draw a card. This ability triggers only once each turn." ==
  some [
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
        [.mana [.generic 0]]])),
    .ability (.triggered
      (.enter (.intersection [
        .not .this,
        .permanent,
        .union [.subtype .dwarf, .subtype .equipment],
        youControl]))
      (.draw (.controller .this) 1))]
#guard parseOracleParts (name := "")
  "As long as you have an enduring story, you may pay {1} rather than pay the equip cost of the first equip ability you activate each turn." ==
  none
#guard parseOracleParts (name := "")
  "Whenever another Dwarf or Equipment you control enters, draw a card." ==
  some [.ability
     (.triggered
       (.enter
         (.intersection
           [.not .this,
            .permanent,
            .union
              [.subtype .dwarf,
               .subtype .equipment],
            .controlled (.controller .this)]))
       (.draw (.controller .this) (.nat 1)))]
#guard parseOracleParts (name := "Dáin's Company")
  "This creature has lifelink as long as you control another Dwarf.\nWhen this creature enters, look at the top four cards of your library. You may reveal a Dwarf or Equipment card from among them and put it into your hand. Put the rest on the bottom of your library in a random order." ==
  some [
    .ability (.static (.if
      (.any (.intersection [.not .this, .permanent, .subtype .dwarf, youControl]))
      [.gainAbility .this (.keyword .lifelink)])),
    .ability (.triggered (.enter .this) (.sequence [
      .actionId 1
        (.lookAt (.topOfLibrary (.controller .this) 4)),
      .optional (.controller .this) (.sequence [
        .actionId 2
          (.reveal
            (.selected (.controller .this) (.range 1 1)
              (.intersection [
                .wasObjectOfAction 1,
                .union [.subtype .dwarf, .subtype .equipment]]))),
        .returnToHand (.wasObjectOfAction 2)]),
      .putOnLibraryBottomInRandomOrder
        (.intersection [
          .wasObjectOfAction 1,
          .not (.wasObjectOfAction 2)])]))]
#guard parseOracleParts (name := "")
  "This creature has lifelink as long as you control a Dwarf." == none
#guard parseOracleParts (name := "")
  "When this creature enters, look at the top one cards of your library. You may reveal a Dwarf or Equipment card from among them and put it into your hand. Put the rest on the bottom of your library in a random order." ==
  none
#guard parseOracleParts (name := "Smaug, Wicked Worm")
  "Flying\nWhen Smaug enters, create X tapped Treasure tokens, where X is the number of artifacts your opponents control.\nWhenever you cast a spell, if mana from a Treasure was spent to cast it, you draw a card and lose 1 life." ==
  some [
    .ability (.keyword .flying),
    .ability (.triggered (.enter .this)
      (.createTokens (.controller .this)
        (.count (.intersection [
          .permanent, .cardType .artifact,
          .controlled (.opponent (.controller .this))]))
        PredefinedToken.treasureToken
        [.tapped])),
    .ability (.triggered
      (.sequence [
        .spendManaFrom (.subtype .treasure)
          (.triggerId 1 (.castSpell (.intersection [.spell, youControl]))),
        .castSpell (.wasArgumentOfTrigger 1 1)])
      (.sequence [
        .draw (.controller .this) 1,
        .loseLife (.controller .this) 1]))]
#guard parseOracleParts (name := "Gandalf")
  "When Smaug enters, create X tapped Treasure tokens, where X is the number of artifacts your opponents control." ==
  none
#guard parseOracleParts (name := "")
  "When this creature enters, create X Treasure tokens, where X is the number of artifacts your opponents control." ==
  none
#guard parseOracleParts (name := "")
  "Whenever you cast a spell, you draw a card and lose 1 life." ==
  some [.ability
     (.triggered
       (.castSpell
         (.intersection
           [.spell,
            .controlled (.controller .this)]))
       (.sequence
         [.draw (.controller .this) (.nat 1),
          .loseLife
            (.controller .this)
            (.nat 1)]))]
#guard parseOracleParts (name := "Glamdring, Foe-hammer")
  "Instant and sorcery spells you cast cost {X} less to cast, where X is equipped creature's power.\nEquip {2}\n//ADV//\nGleam of Death {3}{U}\nSorcery — Adventure\nMill six cards, then put all instant and sorcery cards from among them into your hand. (Then exile this card. You may cast the artifact later from exile.)" ==
  some [
    .ability (.static (.reduceCostWithX
      (.intersection [
        .spell,
        .union [.cardType .instant, .cardType .sorcery],
        youControl])
      [.mana [.x]]
      (.greatestPower (.hostOf .this)))),
    .ability (.keywordWithCost .equip [.mana [.generic 2]]),
    .alternative [
      .name "Gleam of Death",
      .manaCost [.generic 3, .mono .blue],
      .type .sorcery,
      .subtype .adventure,
      .actions [
        .sequence [
          .actionId 1 (.mill (.controller .this) 6),
          .returnToHand (.intersection [
            .wasObjectOfAction 1,
            .union [.cardType .instant, .cardType .sorcery]])]]]]
#guard parseOracleParts (name := "")
  "Instant and sorcery spells you cast cost {1} less to cast, where X is equipped creature's power." ==
  none
#guard parseOracleParts (name := "")
  "Mill six cards, then put all instant and sorcery card from among them into your hand." ==
  none
#guard parseOracleParts (name := "")
  "Mill four cards, then put all Elf cards from among them into your hand." ==
  some [.actions [.sequence [
    .actionId 1 (.mill (.controller .this) 4),
    .returnToHand
      (.intersection [.wasObjectOfAction 1, .subtype .elf])]]]
#guard parseOracleParts (name := "Cantankerous Keepers")
  "When this creature enters, mill four cards, then put all Elf cards from among them into your hand." ==
  some [.ability (.triggered
    (.enter .this)
    (.sequence [
      .actionId 1 (.mill (.controller .this) 4),
      .returnToHand
        (.intersection [.wasObjectOfAction 1, .subtype .elf])]))]
#guard parseOracleParts (name := "")
  "Mill one cards, then put all Elf cards from among them into your hand." == none
#guard parseOracleParts (name := "")
  "Mill four cards, then put all Elves cards from among them into your hand." == none
#guard parseOracleParts (name := "")
  "Mill four cards, then put all instant cards from among them into your hand." == none
#guard parseOracleParts (name := "Elektra, Daughter of the Hand")
  "When Elektra enters, destroy target creature an opponent controls with power 3 or less." ==
  some [.ability (.triggered
    (.enter .this)
    (.destroy
      (.target 1
        (.intersection [
          .permanent,
          .cardType .creature,
          .controlled (.opponent (.controller .this)),
          .powerAtMost (Value.int 3)]))))]
#guard parseOracleParts (name := "Elektra, Daughter of the Hand")
  "When Gandalf enters, destroy target creature an opponent controls with power 3 or less." ==
  none
#guard parseOracleParts (name := "Settle the Wreckage")
  "Exile all attacking creatures target player controls. That player may search their library for that many basic land cards, put those cards onto the battlefield tapped, then shuffle." ==
  some [.actions [
    .actionId 1
      (.exile
        (.intersection [
          .permanent,
          .cardType .creature,
          .attacking .all,
          .controlled (.target 1 .player)])),
    .optional (.targetReference 1)
      (.searchLibraryThenShuffle
        (.targetReference 1)
        [
          .putOntoBattlefieldInState
            (.selected
              (.targetReference 1)
              (.range (.nat 0) (.count (.wasObjectOfAction 1)))
              (.intersection [
                .inLibrary,
                .cardType .land,
                .supertype .basic]))
            [.tapped]])]]
#guard parseOracleParts (name := "")
  "Exile all attacking creatures. That player may search their library for that many basic land cards, put those cards onto the battlefield tapped, then shuffle." ==
  none
#guard parseOracleParts (name := "Iron Hills Blacksmith")
  "When this creature enters, create a colorless Equipment artifact token named Axe with \"Equipped creature gets +1/+0\" and equip {2}." ==
  some [.ability (.triggered (.enter .this)
    (.createTokens (.controller .this) 1 [
      .name "Axe",
      .type .artifact,
      .subtype .equipment,
      .colorIndicator [],
      .ability (.static (.addPower (.hostOf .this) (Value.int 1))),
      .ability (.keywordWithCost .equip [.mana [.generic 2]])]))]
#guard parseOracleParts (name := "Iron Hills Blacksmith")
  "When Iron Hills Blacksmith enters, create a colorless Equipment artifact token named Axe with \"Equipped creature gets +1/+0\" and equip {2}." ==
  parseOracleParts (name := "Iron Hills Blacksmith")
    "When this creature enters, create a colorless Equipment artifact token named Axe with \"Equipped creature gets +1/+0\" and equip {2}."
#guard parseOracleParts (name := "")
  "When this creature enters, create a colorless Equipment artifact token named Axe with \"Equipped creature gets +0/+0\" and equip {2}." ==
  none
#guard parseOracleParts (name := "Gandalf, Goblins' Bane")
  "Whenever you cast a noncreature spell, Gandalf gets +1/+1 until end of turn and deals 1 damage to each opponent." ==
  some [.ability (.triggered
    (.castSpell (.intersection [
      .spell, .not (.cardType .creature), .controlled (.controller .this)]))
    (.sequence [
      .continuous [
        .addPower (.source .this) (Value.int 1),
        .addToughness (.source .this) (Value.int 1)]
        .endOfTurn,
      .dealDamage (.source .this) (.opponent (.controller .this)) 1]))]
#guard parseOracleParts (name := "Saruman")
  "Whenever you cast a noncreature spell, Gandalf gets +1/+1 until end of turn and deals 1 damage to each opponent." ==
  none
#guard parseOracleParts (name := "")
  "Look at the top two cards of your library and exile them face down. For as long as they remain exiled, you may play them if you control a Wizard." ==
  some [.actions [
    .actionId 1 (.lookAt (.topOfLibrary (.controller .this) 2)),
    .actionId 2 (.exileFaceDown (.wasObjectOfAction 1)),
    .continuous
      [.if
        (.any (.intersection [
          .permanent, .subtype .wizard, .controlled (.controller .this)]))
        [.canPlay
          (.controller .this)
          (.intersection [.inExile, .wasCreatedByAction 2])]]
      .endOfGame]]
#guard parseOracleParts (name := "")
  "Look at the top two cards of your library and exile them face down. For as long as they remain exiled, you may play them if you control a Wizard. (Then exile this card. You may cast the creature later from exile.)" ==
  parseOracleParts (name := "")
    "Look at the top two cards of your library and exile them face down. For as long as they remain exiled, you may play them if you control a Wizard."
#guard parseOracleParts (name := "")
  "Look at the top one cards of your library and exile them face down. For as long as they remain exiled, you may play them if you control a Wizard." ==
  none
#guard parseOracleParts (name := "")
  "Look at the top two cards of your library and exile them face up. For as long as they remain exiled, you may play them if you control a Wizard." ==
  none
#guard OracleParts.parseTargetDesc "up to one other target creature" 1 ==
  some (.targets 1 (.range 0 1) (.intersection [.not .this, .permanent, .cardType .creature]))
#guard parseOracleParts (name := "Azog, Moria's Ruin")
  "When Azog enters, destroy up to one other target creature. Its controller amasses Goblins X, where X is that creature's power. If you controlled that creature, draw a card. (To amass Goblins X, that player puts X +1/+1 counters on an Army they control. It's also a Goblin. If they don't control an Army, they create a 0/0 black Goblin Army creature token first.)" ==
  some [.ability (.triggered (.enter .this) (.sequence [
    .defineValueVariable 1
      (.greatestPower
        (.targets 1 (.range 0 1) (.intersection [.not .this, .permanent, .cardType .creature]))),
    .defineSelectorVariable 2 (.controller (.targetReference 1)),
    .destroy (.targetReference 1),
    .keyword (.variable 2) (.amass .goblin (.variable 1)),
    .if (.any (.intersection [.variable 2, .controller .this]))
      [.draw (.controller .this) 1]]))]
#guard parseOracleParts (name := "Azog, Moria's Ruin")
  "When this creature enters, destroy up to one other target creature. Its controller amasses Goblins X, where X is that creature's power. If you controlled that creature, draw a card." ==
  parseOracleParts (name := "Azog, Moria's Ruin")
    "When Azog enters, destroy up to one other target creature. Its controller amasses Goblins X, where X is that creature's power. If you controlled that creature, draw a card."
#guard parseOracleParts (name := "")
  "When this creature enters, destroy up to one other target creature. Its controller amasses Goblins X, where X is that creature's toughness. If you controlled that creature, draw a card." ==
  none
#guard parseOracleParts (name := "Balin, Loremaster")
  "Whenever Balin or another Dwarf you control enters, you may discard your hand. Draw X cards, where X is the number of cards discarded this way. If you have an enduring story, Balin deals X damage to each opponent." ==
  some [.ability (.triggered
    (.or
      (.enter .this)
      (.enter (.intersection [
        .not .this, .permanent, .cardType .creature, .subtype .dwarf,
        .controlled (.controller .this)])))
    (.sequence [
      .optional (.controller .this)
        (.actionId 1
          (.discard (.controller .this)
            (.count (.intersection [.inHand, .owner (.controller .this)])))),
      .draw (.controller .this) (.count (.wasObjectOfAction 1)),
      .if (.enduringStory (.controller .this))
        [.dealDamage (.source .this) (.opponent (.controller .this))
          (.count (.wasObjectOfAction 1))]]))]
#guard parseOracleParts (name := "Balin, Loremaster")
  "Whenever Balin or another Dwarf you control enters, you may discard your hand. Draw X cards, where X is the number of cards discarded this way. If you have an enduring story, Thorin deals X damage to each opponent." ==
  none
#guard parseOracleParts (name := "An Unexpected Party")
  "As this enchantment enters, choose a creature type.\nCreatures you control of the chosen type get +2/+2." ==
  some [
    .ability (.static (.replace (.enter .this)
      [.actionId 1 (.chooseCreatureType (.controller .this)), .keepReplacedAction])),
    .ability (.static (.addPower
      (.intersection [
        .permanent, .cardType .creature, .controlled (.controller .this),
        .hasCreatureTypeChosenByAction 1])
      (Value.int 2))),
    .ability (.static (.addToughness
      (.intersection [
        .permanent, .cardType .creature, .controlled (.controller .this),
        .hasCreatureTypeChosenByAction 1])
      (Value.int 2)))]
#guard parseOracleParts (name := "")
  "As this enchantment enters, choose a creature type." == none
#guard parseOracleParts (name := "")
  "Creatures you control of the chosen type get +2/+2." == none
#guard parseOracleParts (name := "")
  "As this enchantment enters, choose a creature type.\nCreatures you control of the chosen type get +0/+0." ==
  none
#guard parseOracleParts (name := "")
  "Create X 2/2 red Dwarf creature tokens." ==
  some [.actions [
    .createTokens (.controller .this) .x [
      .type .creature, .subtype .dwarf, .colorIndicator [.red], .power 2, .toughness 2]]]
#guard parseOracleParts (name := "")
  "Create X 2/2 red Dwarf creature token." == none
#guard parseOracleParts (name := "")
  "{X}{X}, {T}, Sacrifice this land: Create X Treasure tokens." ==
  some [.ability (.activated
    [.mana [.x, .x], .tapSymbol, .sacrifice .this]
    (.createTokens (.controller .this) .x PredefinedToken.treasureToken))]
#guard parseOracleParts (name := "")
  "{X}{X}, {T}, Sacrifice this land: Create X Treasure token." == none
#guard parseOracleParts (name := "")
  "III, IV — Add {R}." ==
  some [
    .ability (.keywordWithEffect (.chapter 3) [.addMana (.controller .this) [.mono .red]]),
    .ability (.keywordWithEffect (.chapter 4) [.addMana (.controller .this) [.mono .red]])]
#guard parseOracleParts (name := "")
  "II — This Saga gains \"Whenever a land you control enters, draw a card.\"" ==
  some [.ability (.keywordWithEffect (.chapter 2) [
    .continuous
      [.gainAbility .this (.triggered
        (.enter (.intersection [.permanent, .cardType .land, .controlled (.controller .this)]))
        (.draw (.controller .this) 1))]
      .endOfGame])]
#guard parseOracleParts (name := "")
  "II — This Saga gains \"Whenever a land you control enters, draw a card.\" Draw a card." ==
  none
#guard parseOracleParts (name := "")
  "{2}{W}: Two target players each draw a card." ==
  some [.ability (.activated [.mana [.generic 2, .mono .white]]
    (.draw (.targets 1 (.range 2 2) .player) 1))]
#guard parseOracleParts (name := "")
  "{2}{W}: Two target players each draw." == none
#guard parseOracleParts (name := "")
  "When this creature enters, you create a Treasure token." ==
  some [.ability (.triggered (.enter .this)
    (.createTokens (.controller .this) 1 PredefinedToken.treasureToken))]
#guard parseOracleParts (name := "")
  "Create a Treasure token for each Villain you control." ==
  some [.actions [.forEachVariable 1
    (.intersection [.permanent, .subtype .villain, .controlled (.controller .this)])
    [.createTokens (.controller .this) 1 PredefinedToken.treasureToken]]]
#guard parseOracleParts (name := "")
  "Create two Treasure tokens for each Villain you control." == none
#guard parseOracleParts (name := "")
  "Whenever equipped creature deals combat damage to a player, choose a creature type. Create a Treasure token for each creature you control of that type." ==
  some [.ability (.triggered (.combatDamage (.hostOf .this) .player) (.sequence [
    .actionId 1 (.chooseCreatureType (.controller .this)),
    .forEachVariable 1
      (.intersection [
        .permanent, .cardType .creature, .controlled (.controller .this),
        .hasCreatureTypeChosenByAction 1])
      [.createTokens (.controller .this) 1 PredefinedToken.treasureToken]]))]
#guard parseOracleParts (name := "")
  "Choose a creature type. Create a Treasure token for each creature you control." == none
#guard parseOracleParts (name := "")
  "Look at the top twenty cards of your library, put any number of land cards from among them onto the battlefield tapped, then shuffle." ==
  some [.actions [
    .actionId 1 (.lookAt (.topOfLibrary (.controller .this) 20)),
    .searchLibraryThenShuffle (.controller .this) [
      .putOntoBattlefieldInState
        (.selected (.controller .this) .any (.intersection [.wasObjectOfAction 1, .cardType .land]))
        [.tapped]]]]
#guard parseOracleParts (name := "")
  "Look at the top twenty cards of your library, put any number of land cards from among them onto the battlefield tapped." ==
  none
#guard parseOracleParts (name := "")
  "At the beginning of combat on your turn, if you've drawn two or more cards this turn, draw a card." ==
  some [.ability (.triggered (.combatStart (.controller .this))
    (.if (.happened (.ordinal 2 .turnStart (.draw (.controller .this) .all)) .turnStart)
      [.draw (.controller .this) 1]))]
#guard parseOracleParts (name := "")
  "At the beginning of combat on your turn, if you've drawn a card this turn, draw a card." == none
#guard parseOracleParts (name := "")
  "At the beginning of lunch, draw a card." == none
#guard parseOracleParts (name := "")
  "The first creature spell you cast each turn costs {1} less to cast and can be cast as though it had flash." ==
  let creatureSpell := Selector.intersection [.spell, .cardType .creature, .controlled (.controller .this)]
  let first := Condition.didNotHappen (.castSpell creatureSpell) .turnStart
  some [
    .ability (.static (.if first [.reduceCost creatureSpell [.mana [.generic 1]]])),
    .ability (.static (.canBeCastAsThoughWithFlashIf creatureSpell first))]
#guard parseOracleParts (name := "")
  "The first creature spell you cast each turn costs {1} less to cast." == none
#guard parseOracleParts (name := "")
  "{T}: Add {C} for each Food you control." ==
  some [.ability (.activated [.tapSymbol]
    (.forEachVariable 1 (.intersection [.permanent, .subtype .food, youControl])
      [.addMana (.controller .this) [.colorless]]))]
#guard parseOracleParts (name := "")
  "Add {R} for each artifact your opponents control." ==
  some [.actions [.forEachVariable 1
    (.intersection [.permanent, .cardType .artifact, .controlled (.opponent (.controller .this))])
    [.addMana (.controller .this) [.colored .red]]]]
#guard parseOracleParts (name := "")
  "{T}: Target creature with power 2 or less can't be blocked this turn." ==
  some [.ability (.activated [.tapSymbol]
    (.continuous [.forbid (.block .all (.target 1
      (.intersection [.permanent, .cardType .creature, .powerAtMost (Value.int 2)])))] .endOfTurn))]
#guard parseOracleParts (name := "")
  "Whenever this creature attacks, it deals damage equal to the number of Dwarves you control to each opponent." ==
  some [.ability (.triggered (.attack .this .all)
    (.dealDamage .this (.opponent (.controller .this))
      (.count (.intersection [.permanent, .subtype .dwarf, youControl]))))]
#guard parseOracleParts (name := "")
  "When this creature enters, draw a card. Then if you don't control a legendary creature, put a card from your hand on the bottom of your library." ==
  some [.ability (.triggered (.enter .this) (.sequence [
    .draw (.controller .this) 1,
    .if (.not (.any (.intersection
        [.permanent, .cardType .creature, .supertype .legendary, youControl])))
      [.putOnBottomOfLibrary (.selected (.controller .this) (.range 1 1)
        (.intersection [.inHand, .owner (.controller .this)]))]]))]
#guard parseOracleParts (name := "")
  "When this creature enters, draw a card. Then if you don't control a legendary creature, put two cards from your hand on the bottom of your library." ==
  none
#guard parseOracleParts (name := "")
  "Legendary creatures you control get +2/+1 and have ward {1}." ==
  let legendary := Selector.intersection
    [.permanent, .cardType .creature, youControl, .supertype .legendary]
  some [
    .ability (.static (.addPower legendary (Value.int 2))),
    .ability (.static (.addToughness legendary (Value.int 1))),
    .ability (.static (.gainAbility legendary (.keywordWithCost .ward [.mana [.generic 1]])))]
#guard parseOracleParts (name := "")
  "Nonlegendary creatures you control get +1/+1." ==
  let nonlegendary := Selector.intersection
    [.permanent, .cardType .creature, .not (.supertype .legendary), youControl]
  some [
    .ability (.static (.addPower nonlegendary (Value.int 1))),
    .ability (.static (.addToughness nonlegendary (Value.int 1)))]
#guard parseOracleParts (name := "")
  "{T}: Add {R}{R}. Spend this mana only to cast Dwarf, Equipment, and Saga spells." ==
  some [.ability (.activated [.tapSymbol] (.sequence [
    .actionId 1 (.addMana (.controller .this) [.colored .red, .colored .red]),
    .continuous [.forbid (.spendManaCreatedByAction 1 (.not (.castSpell
      (.intersection [.spell, .union [.subtype .dwarf, .subtype .equipment, .subtype .saga]]))))]
      .endOfTurn]))]
#guard parseOracleParts (name := "")
  "{2}{B}: Return this card from your graveyard to the battlefield tapped. Activate only if you control a legendary creature." ==
  some [.ability (.graveyardActivatedIf
    (.any (.intersection [.permanent, .cardType .creature, .supertype .legendary, youControl]))
    [.mana [.generic 2, .colored .black]]
    (.putOntoBattlefieldInState (.intersection [.inGraveyard, .source .this]) [.tapped]))]
#guard parseOracleParts (name := "")
  "{2}{B}: Return this card from your graveyard to the battlefield tapped." == none
#guard parseOracleParts (name := "")
  "Draw cards equal to the greatest toughness among creatures you control, then put any number of creature cards from your hand onto the battlefield." ==
  some [.actions [
    .draw (.controller .this) (.greatestToughness creaturesYouControl),
    .putOntoBattlefield (.selected (.controller .this) .any
      (.intersection [.inHand, .owner (.controller .this), .cardType .creature]))]]
#guard parseOracleParts (name := "")
  "Whenever another creature you control with power 2 or less enters, you may pay {1}. If you do, draw a card." ==
  some [.ability (.triggered
    (.enter (.intersection [
      .not .this, .permanent, .cardType .creature, youControl, .powerAtMost (Value.int 2)]))
    (.optionalPayFor (.controller .this) [.mana [.generic 1]] [.draw (.controller .this) 1]))]
#guard parseOracleParts (name := "")
  "Whenever another creature you control with power 2 or less enters, you may pay {1}. If you don't, draw a card." ==
  none
#guard parseOracleParts (name := "Minas Tirith Garrison")
  "Minas Tirith Garrison's power is equal to the number of cards in your hand." ==
  some [.ability (.static (.setPower .this
    (.count (.intersection [.inHand, .owner (.controller .this)]))))]
#guard parseOracleParts (name := "Minas Tirith Garrison")
  "Minas Tirith Garrison's power is equal to the number of cards in your graveyard." == none
#guard parseOracleParts (name := "")
  "Whenever this creature attacks, you may tap any number of untapped Humans you control. Draw a card for each Human tapped this way." ==
  some [.ability (.triggered (.attack .this .all) (.sequence [
    .actionId 1 (.tap (.selected (.controller .this) .any
      (.intersection [.permanent, .subtype .human, .not .tapped, youControl]))),
    .draw (.controller .this) (.count (.wasObjectOfAction 1))]))]
#guard parseOracleParts (name := "")
  "Whenever this creature enters or attacks, return target Elf card from your graveyard to your hand. You gain life equal to that card's power." ==
  some [.ability (.triggered (.or (.enter .this) (.attack .this .all)) (.sequence [
    .returnToHand (.target 1 (.intersection [.inGraveyard, .subtype .elf, .owner (.controller .this)])),
    .gainLife (.controller .this) (.greatestPower (.targetReference 1))]))]
#guard parseOracleParts (name := "")
  "{T}, Pay 1 life: Add {B} or {R}." ==
  some [.ability (.activated [.tapSymbol, .life 1]
    (.playerSelectAction (.controller .this) (.range 1 1)
      [.addMana (.controller .this) [.colored .black], .addMana (.controller .this) [.colored .red]]))]
#guard parseOracleParts (name := "Mount Doom")
  "{5}{B}{R}, {T}, Sacrifice Mount Doom and a legendary artifact: Choose up to two creatures, then destroy the rest. Activate only as a sorcery." ==
  some [.ability (.activatedIf (.timeToCastSorcery (.controller .this))
    [.mana [.generic 5, .colored .black, .colored .red], .tapSymbol, .sacrifice .this,
      .sacrificeCount (.intersection [.permanent, .cardType .artifact, .supertype .legendary]) 1]
    (.sequence [
      .defineSelectorVariable 1
        (.selected (.controller .this) (.range 0 2) (.intersection [.permanent, .cardType .creature])),
      .destroy (.intersection [.permanent, .cardType .creature, .not (.variable 1)])]))]
#guard parseOracleParts (name := "Mount Doom")
  "{5}{B}{R}, {T}, Sacrifice Rivendell and a legendary artifact: Choose up to two creatures, then destroy the rest. Activate only as a sorcery." ==
  none
#guard parseOracleParts (name := "")
  "This creature can't block unless you control a Goblin or Orc." ==
  some [.ability (.static (.if
    (.not (.any (.intersection [.permanent, .union [.subtype .goblin, .subtype .orc], youControl])))
    [.forbid (.block .this .any)]))]
#guard parseOracleParts (name := "")
  "Other Orcs and Goblins you control have trample." ==
  some [.ability (.static (.gainAbility
    (.intersection [.not .this, .permanent, .union [.subtype .orc, .subtype .goblin], youControl])
    (.keyword .trample)))]
#guard parseOracleParts (name := "")
  "Whenever this creature attacks, it gets +X/+0 until end of turn, where X is the greatest power among creatures you control." ==
  some [.ability (.triggered (.attack .this .all)
    (.continuous [.addPower (.source .this) (.greatestPower creaturesYouControl)] .endOfTurn))]
#guard parseOracleParts (name := "")
  "When this creature enters, destroy all artifacts and enchantments your opponents control. You gain 1 life for each permanent destroyed this way." ==
  some [.ability (.triggered (.enter .this) (.sequence [
    .actionId 1 (.destroy (.intersection [
      .permanent, .union [.cardType .artifact, .cardType .enchantment],
      .controlled (.opponent (.controller .this))])),
    .gainLife (.controller .this) (.count (.wasObjectOfAction 1))]))]
#guard parseOracleParts (name := "")
  "Choose a creature type. Return all creatures that aren't of the chosen type to their owners' hands." ==
  some [.actions [
    .actionId 1 (.chooseCreatureType (.controller .this)),
    .returnToHand (.intersection [.permanent, .cardType .creature, .not (.hasCreatureTypeChosenByAction 1)])]]
#guard parseOracleParts (name := "")
  "{T}: Add two mana in any combination of {U}, {B}, and/or {R}." ==
  some [.ability (.activated [.tapSymbol] (.addManaInAnyCombination (.controller .this)
    [.colored .blue, .colored .black, .colored .red] 2))]
#guard parseOracleParts (name := "Rivendell")
  "Rivendell enters tapped unless you control a legendary creature." ==
  some [.ability (.everywhereStatic (.if
    (.not (.any (.intersection [.permanent, .cardType .creature, .supertype .legendary, youControl])))
    [.replace (.enter .this) [.putOntoBattlefieldInState .this [.tapped]]]))]
#guard parseOracleParts (name := "")
  "{1}{U}, {T}: Scry 2. Activate only if you control a legendary creature." ==
  some [.ability (.activatedIf
    (.any (.intersection [.permanent, .cardType .creature, .supertype .legendary, youControl]))
    [.mana [.generic 1, .colored .blue], .tapSymbol]
    (.scry (.controller .this) 2))]
#guard parseOracleParts (name := "")
  "Other Elves you control have \"{T}: Add {G} or {U}.\"" ==
  some [.ability (.static (.gainAbility
    (.intersection [.not .this, .permanent, .subtype .elf, youControl])
    (.activated [.tapSymbol] (.playerSelectAction (.controller .this) (.range 1 1)
      [.addMana (.controller .this) [.colored .green], .addMana (.controller .this) [.colored .blue]]))))]
#guard parseOracleParts (name := "") "Other Elves you control have \"Flying.\"" == none
#guard parseOracleParts (name := "")
  "{T}: Add one mana of any color. Spend this mana only to cast a Hero spell or to activate an ability of a Hero source." ==
  some [.ability (.activated [.tapSymbol] (.sequence [
    .actionId 1 (.addManaOfOneColor (.controller .this) ManaSymbol.anyColor 1),
    .continuous [.forbid (.spendManaCreatedByAction 1 (.not (.or
      (.castSpell (.intersection [.spell, .subtype .hero])) (.activateAbility (.subtype .hero)))))]
      .endOfTurn]))]
#guard parseOracleParts (name := "")
  "{T}: Add one mana of any color. Spend this mana only to cast a Hero spell or to activate an ability of a Villain source." ==
  none
#guard parseOracleParts (name := "")
  "{T}: Add one mana of any color. Spend this mana only to cast an artifact spell." ==
  some [.ability (.activated [.tapSymbol] (.sequence [
    .actionId 1 (.addManaOfOneColor (.controller .this) ManaSymbol.anyColor 1),
    .continuous [.forbid (.spendManaCreatedByAction 1
      (.not (.castSpell (.intersection [.spell, .cardType .artifact]))))] .endOfTurn]))]
#guard parseOracleParts (name := "")
  "{T}: Add {U}. This mana can't be spent to cast a nonartifact spell." ==
  some [.ability (.activated [.tapSymbol] (.sequence [
    .actionId 1 (.addMana (.controller .this) [.colored .blue]),
    .continuous [.forbid (.spendManaCreatedByAction 1
      (.castSpell (.intersection [.spell, .not (.cardType .artifact)])))] .endOfTurn]))]
#guard parseOracleParts (name := "")
  "{T}: Add {B} or {R}. Activate only if this land entered this turn or if you control a basic land." ==
  some [.ability (.activatedIf
    (.not (.and (.not (.happened (.enter (.source .this)) .turnStart))
      (.not (.any (.intersection [.permanent, .cardType .land, .supertype .basic, youControl])))))
    [.tapSymbol]
    (.playerSelectAction (.controller .this) (.range 1 1)
      [.addMana (.controller .this) [.colored .black], .addMana (.controller .this) [.colored .red]]))]
#guard parseOracleParts (name := "")
  "{4}, {T}: Look at the top three cards of your library. You may reveal a Hero card from among them and put it into your hand. Put the rest on the bottom of your library in any order." ==
  some [.ability (.activated [.mana [.generic 4], .tapSymbol] (.sequence [
    .actionId 1 (.lookAt (.topOfLibrary (.controller .this) 3)),
    .optional (.controller .this) (.sequence [
      .actionId 2 (.reveal (.selected (.controller .this) (.range 1 1)
        (.intersection [.wasObjectOfAction 1, .subtype .hero]))),
      .returnToHand (.wasObjectOfAction 2)]),
    .putOnBottomOfLibrary (.intersection [.wasObjectOfAction 1, .not (.wasObjectOfAction 2)])]))]
#guard parseOracleParts (name := "")
  "{4}, {T}: Look at the top three cards of your library. You may reveal a Hero card from among them and put it into your hand. Put the rest on the bottom of your library in a random order." ==
  none

#guard parseOracleParts (name := "Quake") "Quake deals 3 damage to each creature." ==
  some [.actions [.dealDamage .this (.intersection [.permanent, .cardType .creature]) 3]]
#guard parseOracleParts (name := "")
  "Destroy target land. Its controller may search their library for a basic land card, put it onto the battlefield tapped, then shuffle." ==
  some [.actions [
    .destroy (.target 1 (.intersection [.permanent, .cardType .land])),
    .optional (.controller (.targetReference 1)) (.searchLibraryThenShuffle (.controller (.targetReference 1)) [
      .putOntoBattlefieldInState (.selected (.controller (.targetReference 1)) (.range 1 1)
        (.intersection [.inLibrary, .cardType .land, .supertype .basic])) [.tapped]])]]
#guard parseOracleParts (name := "")
  "Double target creature's power and toughness until end of turn." ==
  some [.actions [.continuous [
    .addPower (.target 1 (.intersection [.permanent, .cardType .creature])) (.greatestPower (.targetReference 1)),
    .addToughness (.targetReference 1) (.greatestToughness (.targetReference 1))] .endOfTurn]]
#guard parseOracleParts (name := "")
  "Target creature you control fights target creature an opponent controls." ==
  some [.actions [.fight
    (.target 1 (.intersection [.permanent, .cardType .creature, youControl]))
    (.target 2 (.intersection [.permanent, .cardType .creature, .controlled (.opponent (.controller .this))]))]]
#guard parseOracleParts (name := "")
  "Target creature you control deals damage equal to twice its power to target creature an opponent controls." ==
  some [.actions [.dealDamage
    (.target 1 (.intersection [.permanent, .cardType .creature, youControl]))
    (.target 2 (.intersection [.permanent, .cardType .creature, .controlled (.opponent (.controller .this))]))
    (.product (.totalPower (.targetReference 1)) (.int 2))]]
#guard parseOracleParts (name := "")
  "This spell costs {2} less to cast if there are two or more creature cards in your graveyard." ==
  some [.ability (.stackStatic (.if
    (.greaterOrEqual (.count (.intersection [.inGraveyard, .cardType .creature, .owner (.controller .this)])) 2)
    [.reduceCost .this [.mana [.generic 2]]]))]
#guard parseOracleParts (name := "Worlds")
  "Exile all creatures. Each player may put any number of creature cards from their hand onto the battlefield. Then put all cards exiled this way into their owners' hands. Exile Worlds." ==
  some [.actions [
    .actionId 1 (.exile (.intersection [.permanent, .cardType .creature])),
    .forEachVariable 1 .player [.optional (.variable 1) (.putOntoBattlefield
      (.selected (.variable 1) .any (.intersection [.inHand, .owner (.variable 1), .cardType .creature])))],
    .returnToHand (.wasCreatedByAction 1),
    .exile .this]]
#guard parseOracleParts (name := "Worlds")
  "Exile all creatures. Each player may put any number of creature cards from their hand onto the battlefield. Then put all cards exiled this way into their owners' hands. Exile Other Card." ==
  none
#guard parseOracleParts (name := "") "Mill two cards." ==
  some [.actions [.mill (.controller .this) 2]]
#guard parseOracleParts (name := "") "Mill a card." == none
#guard parseOracleParts (name := "HYDRA Troopers")
  "When this creature enters, create a tapped 2/1 black Villain creature token with menace if there are two or more creature cards in your graveyard. Otherwise, mill two cards. (Put the top two cards of your library into your graveyard.)" ==
  some [.ability (.triggered (.enter .this)
    (.ifElse (.greaterOrEqual (.count (.intersection [.inGraveyard, .cardType .creature, .owner (.controller .this)])) 2)
      [.createTokens (.controller .this) 1
        [.type .creature, .subtype .villain, .colorIndicator [.black], .power 2, .toughness 1,
          .ability (.keyword .menace)] [.tapped]]
      [.mill (.controller .this) 2]))]
#guard parseOracleParts (name := "Iron Man, Master of Machines")
  "Whenever Iron Man attacks, if an artifact entered the battlefield under your control this turn, draw a card." ==
  some [.ability (.triggered (.attack .this .all)
    (.if (.happened (.enter (.intersection [.permanent, .cardType .artifact, youControl])) .turnStart)
      [.draw (.controller .this) 1]))]
#guard parseOracleParts (name := "Super Intelligence")
  "At the beginning of the upkeep of enchanted creature's controller, that player draws a card." ==
  some [.ability (.triggered (.upkeep (.controller (.hostOf .this))) (.draw (.controller (.hostOf .this)) 1))]
#guard parseOracleParts (name := "Hulkling, Burgeoning Bruiser")
  "Whenever another creature you control enters, if it has greater power or toughness than Hulkling, put a +1/+1 counter on Hulkling." ==
  some [.ability (.triggered
    (.triggerId 1 (.enter (.intersection [.not .this, .permanent, .cardType .creature, youControl])))
    (.if (.not (.and
        (.not (.greater (.greatestPower (.wasArgumentOfTrigger 1 1)) (.greatestPower (.source .this))))
        (.not (.greater (.greatestToughness (.wasArgumentOfTrigger 1 1)) (.greatestToughness (.source .this))))))
      [.putCounter (.source .this) .plusOnePlusOne 1]))]
#guard parseOracleParts (name := "")
  "Flying, first strike, ward {1}" ==
  some [.ability (.keyword .flying), .ability (.keyword .firstStrike),
    .ability (.keywordWithCost .ward [.mana [.generic 1]])]
#guard parseOracleParts (name := "The Sackville-Bagginses")
  "Whenever you sacrifice a token, target opponent loses 1 life." ==
  some [.ability (.triggered
    (.sacrifice (.intersection [.permanent, .token, youControl]))
    (.loseLife (.target 1 (.opponent (.controller .this))) 1))]
#guard parseOracleParts (name := "The Sackville-Bagginses")
  "Whenever you sacrifice a creature, target opponent loses 1 life." == none
#guard parseOracleParts (name := "The Sackville-Bagginses")
  "Whenever a token you control dies, target opponent loses 1 life." == none
#guard parseOracleParts (name := "The Thing, Ben Grimm")
  "Whenever one or more Heroes you control deal damage to a player, put two +1/+1 counters on The Thing." ==
  some [.ability (.triggered
    (.damageSimultaneously
      (.intersection [
        .permanent, .cardType .creature, .subtype .hero, youControl])
      .player
      [])
    (.putCounter (.source .this) .plusOnePlusOne 2))]
#guard parseOracleParts (name := "The Thing, Ben Grimm")
  "Whenever one or more Heroes you control deal combat damage to a player, put two +1/+1 counters on The Thing." ==
  none
#guard parseOracleParts (name := "Other Card")
  "Whenever one or more Heroes you control deal damage to a player, put two +1/+1 counters on The Thing." ==
  none
#guard parseOracleParts (name := "Enchanted River's Grasp")
  "When this Aura enters, tap enchanted creature and remove all counters from it." ==
  some [.ability (.triggered (.enter .this)
    (.sequence [
      .tap (.hostOf .this),
      .removeAllCounters (.hostOf .this)]))]
#guard parseOracleParts (name := "Enchanted River's Grasp")
  "Enchanted creature loses all abilities and doesn't untap during its controller's untap step." ==
  some [
    .ability (.static (.removeAllAbilities (.hostOf .this))),
    .ability (.static (.doesntUntap (.hostOf .this)))]
#guard parseOracleParts (name := "Enchanted River's Grasp")
  "Enchanted creature loses all abilities." == none
#guard parseOracleParts (name := "Enchanted River's Grasp")
  "When this Aura enters, tap enchanted creature." == none
#guard parseOracleParts (name := "")
  "Attach any number of target Equipment you control to target creature you control." ==
  some [.actions [.attach
    (.targets 1 .any equipmentYouControl)
    (.target 2 creaturesYouControl)]]
#guard parseOracleParts (name := "Thorin, Mountain-king")
  "When Thorin enters, attach any number of target Equipment you control to target creature you control. When one or more Equipment become attached to that creature this way, that creature deals damage equal to its power to up to one target creature." ==
  some [.ability (.triggered (.enter .this)
    (.sequence [
      .actionId 1 (.attach
        (.targets 1 .any equipmentYouControl)
        (.target 2 creaturesYouControl)),
      .if (.greaterOrEqual (.count (.wasObjectOfAction 1)) 1)
        [.dealDamageEqualToPower (.targetReference 2)
          (.targets 3 (.range 0 1)
            (.intersection [.permanent, .cardType .creature]))]]))]
#guard parseOracleParts (name := "Thorin, Mountain-king")
  "When Thorin enters, attach any number of target Equipment you control to target creature you control. When one or more Equipment become attached to that creature this way, that creature deals damage equal to its toughness to up to one target creature." ==
  none
#guard parseOracleParts (name := "Other Card")
  "When Thorin enters, attach any number of target Equipment you control to target creature you control. When one or more Equipment become attached to that creature this way, that creature deals damage equal to its power to up to one target creature." ==
  none
#guard parseOracleParts (name := "Celebrate the Mountain-king")
  "When this enchantment enters, for each opponent, exile one target nonland permanent that player controls until this enchantment leaves the battlefield." ==
  none
#guard parseOracleParts (name := "Celebrate the Mountain-king")
  "When this enchantment enters, for each opponent, exile up to one target nonland permanent that player controls until Bilbo leaves the battlefield." ==
  none
#guard parseOracleParts (name := "Down, Down to Goblin-town")
  "I — Target player reveals their hand. You choose a nonland card from it. That player discards that card." ==
  none
#guard parseOracleParts (name := "The Mountain-king's Return")
  "I — Recruit. (Draw a card, then discard a card. If you discarded a nonland card, create a 1/1 white Human Soldier creature token.)" ==
  some [.ability (.keywordWithEffect (.chapter 1) [.keyword (.controller .this) .recruit])]
#guard parseOracleParts (name := "")
  "II — Return target creature card with mana value 3 or less from your graveyard to the battlefield." ==
  some [.ability (.keywordWithEffect (.chapter 2)
    [.putOntoBattlefield
      (.target 1
        (.intersection [
          .inGraveyard,
          .cardType .creature,
          .owner (.controller .this),
          .manaValueAtMost (.nat 3)]))])]
#guard parseOracleParts (name := "")
  "II — Return target creature card with mana value 0 or less from your graveyard to the battlefield." ==
  none
#guard parseOracleParts (name := "")
  "II — Return target creature card with mana value 3 or greater from your graveyard to the battlefield." ==
  none
#guard parseOracleParts (name := "")
  "III — Put a +1/+1 counter on up to one target creature." ==
  some [.ability (.keywordWithEffect (.chapter 3)
    [.putCounter
      (.targets 1 (.range 0 1) (.intersection [.permanent, .cardType .creature]))
      .plusOnePlusOne
      1])]
#guard parseOracleParts (name := "Uncover the Moon-Letters")
  "Whenever you cast a noncreature spell, you may draw X cards, where X is the amount of mana spent to cast that spell. If you do, discard two cards." ==
  some [.ability (.triggered
    (.triggerId 1
      (.castSpell
        (.intersection [
          .spell, .not (.cardType .creature), .controlled (.controller .this)])))
    (.sequence [
      .optional (.controller .this)
        (.actionId 1
          (.draw (.controller .this) (.manaSpent (.wasArgumentOfTrigger 1 1)))),
      .if (.happened (.actionWithId 1) .gameStart)
        [.discard (.controller .this) 2]]))]
#guard parseOracleParts (name := "Uncover the Moon-Letters")
  "Whenever you cast a creature spell, you may draw X cards, where X is the amount of mana spent to cast that spell. If you do, discard two cards." ==
  none
#guard parseOracleParts (name := "Uncover the Moon-Letters")
  "Whenever you cast a noncreature spell, you may draw X cards, where X is that spell's mana value. If you do, discard two cards." ==
  none
#guard parseOracleParts (name := "Uncover the Moon-Letters")
  "Whenever you cast a noncreature spell, you may draw X cards, where X is the amount of mana spent to cast that spell. If you do, discard a card." ==
  none

end Mtg.Engine
