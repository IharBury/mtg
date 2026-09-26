import Mtg.Engine.Card
import Mtg.Engine.Catalog

/-!
# The Hobbit catalog

Oracle characteristics for cards from Magic: The Gathering | The Hobbit
(HOB). Oracle text is stored verbatim from Scryfall.
`hobbitCards` lists every unique card in the set, including Journey basic
lands that are also in the core catalog.

New cards may be written as a `TraditionalCardDefinition` (a list of
`CardPart`s) and compiled with `toCardDef`. Bofur, Reliable Guardian,
Dwarven Provisioner, Velvetwing Butterflies, Magnificent End, Eagle
of the Great Shelf, Vow to Erebor, Bilbo Baggins, Burglar,
Lakeshore Apothecary, Confusticate and Bebother, Ravenhill Flock,
Thranduil's Decree, Bilbo, Luckwearer, Uneasy Partings, Front Porch
Sentries, Great Fierce Bee, Stir Up Trouble, Desolation Prowler,
Ravening Warg, Gollum, Silent Slinker, Bilbo's Deadly Slice,
Dreaded Bat-Cloud, Crude Bent Blade, Gollum the Abandoned, Gnashing of
Teeth, Reverent Howl, Stony-Voiced Goblins, Smaug, the Great Calamity,
Gandalf, Spark Starter, Ragged Short Spear, Snowslope Hunter,
Guardian of the Halls, Quarrel, Galion, Elvenking's Butler,
Warg Tactics, Beorn's Hospitality, Woodland Weavemaster,
Mirkwood Pathmaker, Beorn, Reluctant Host, Wood Elves, Attercop,
Large Bear, Little Bear, Elvenking's Harper, Smaug's Fury,
Well-Worn Spatula, Elvenking's Halls, Iron Hills, Lake-town,
Goblin-town, Mirkwood, Hobbit Hole, Nighthowl Pursuer, Wargling,
Wilderland Scrounger, Nasty Little Rabbit, The Chief Warg,
Thorin's Last Stand, Stone by Sunlight, Duskwatch Hunter,
Patient Instructor, Long Lake Nuisance, Lake-town Lookout,
Giant's Boulder, Long-Bodied Grey Dog, Dori, Bearer of Friends,
Esgaroth Garrison, Gundabad Opportunist, Gigantic Big Bear,
Bothersome Noisemaker, Fearsome Goblin Pair, Goblin-town Flunkies,
Misty Mountains Raider, Bard's Company, Rage into the Valley,
Gathering of Darkness, Sound the Trumpets, Fateful Discovery,
Chief Warg's Company, Dwarven Shortsword, Goblin Plate Mail,
Moment of Glory, Plunder the Trollshaws, Tidings of War,
Eagle's Rescue, Gandalf, Wandering Wizard, Troll Negotiations,
Dwarven Mattock, Great Ugly-Looking Goblin, The Arkenstone,
Bolg's Company, Nori, Teller of Tales, The Lord of the Eagles,
Thrór's Map, The Black Arrow, Smaug the Magnificent,
The Queen of Dale, Ori, Keeper of Songs, Óin the Brave,
Bombur, Gentle Dreamer, Fíli the Pathfinder, Thorin Oakenshield,
Dáin, Lord of the Iron Hills, Old Thrush, Most Decrepit Old Bird,
Lake-town Mariners, Pinecone Strike, The Lonely Mountain,
Thranduil, Sindarin Liege, Glóin the Mighty, Iron Hills Stalwart,
Old Fat Spider, Great Gilded Boat, and Desolation of Smaug
keep their printed characteristics as parts;
`parseOracleParts` reads the Oracle text into the rest, using the card
name for references to itself. These cards' text is fully recognized;
an unrecognized part fails the parse.

Source: https://magic.wizards.com/en/news/announcements/the-hobbit-welcome-decks
-/

namespace Mtg.Engine.Catalog

open Mtg.Engine

/-- Gatherer Oracle text for Bofur, Reliable Guardian // Concerted Care. -/
def bofurReliableGuardianOracle : String :=
  "Lifelink\n//ADV//\nConcerted Care {1}{W}\nInstant — Adventure\nTarget artifact or creature you control gains hexproof and indestructible until end of turn. (Then exile this card. You may cast the creature later from exile.)"

def bofurReliableGuardian : TraditionalCardDefinition := .card <|
  [
    .name "Bofur, Reliable Guardian",
    .manaCost [.mono .white],
    .type .creature,
    .supertype .legendary,
    .subtype .dwarf,
    .subtype .scout,
    .power 1,
    .toughness 1
  ] ++ (parseOracleParts (name := "Bofur, Reliable Guardian") bofurReliableGuardianOracle).get!

def bofurReliableGuardianCard : CardDef :=
  bofurReliableGuardian.toCardDef
    (oracleText := bofurReliableGuardianOracle)

#guard bofurReliableGuardian == .card [
  .name "Bofur, Reliable Guardian",
  .manaCost [.mono .white],
  .type .creature,
  .supertype .legendary,
  .subtype .dwarf,
  .subtype .scout,
  .power 1,
  .toughness 1,
  .ability (.keyword .lifelink),
  .alternative [
    .name "Concerted Care",
    .manaCost [.generic 1, .mono .white],
    .type .instant,
    .subtype .adventure,
    .actions [
      .continuous
        [
          .gainAbility
            (.target
              1
              (.intersection [
                .permanent,
                .union [.cardType .artifact, .cardType .creature],
                .controlled (.controller .this)]))
            (.keyword .hexproof),
          .gainAbility (.targetReference 1) (.keyword .indestructible)]
        .endOfTurn]]]

/-- Oracle text for Dwarven Provisioner. -/
def dwarvenProvisionerOracle : String :=
  "{3}{W}: Creatures you control get +1/+1 until end of turn."

def dwarvenProvisioner : TraditionalCardDefinition := .card <|
  [
    .name "Dwarven Provisioner",
    .manaCost [.generic 1, .mono .white],
    .type .creature,
    .subtype .dwarf,
    .subtype .citizen,
    .power 2,
    .toughness 2
  ] ++ (parseOracleParts (name := "Dwarven Provisioner") dwarvenProvisionerOracle).get!

def dwarvenProvisionerCard : CardDef :=
  dwarvenProvisioner.toCardDef
    (oracleText := dwarvenProvisionerOracle)

#guard dwarvenProvisioner == .card [
  .name "Dwarven Provisioner",
  .manaCost [.generic 1, .mono .white],
  .type .creature,
  .subtype .dwarf,
  .subtype .citizen,
  .power 2,
  .toughness 2,
  .ability (
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

/-- Gatherer Oracle text for Velvetwing Butterflies // Gaze in Wonder. -/
def velvetwingButterfliesOracle : String :=
  "Flying\n//ADV//\nGaze in Wonder {1}{W}\nInstant — Adventure\nTap one or two target creatures. (Then exile this card. You may cast the creature later from exile.)"

def velvetwingButterflies : TraditionalCardDefinition := .card <|
  [
    .name "Velvetwing Butterflies",
    .manaCost [.generic 2, .mono .white],
    .type .creature,
    .subtype .insect,
    .power 2,
    .toughness 2
  ] ++ (parseOracleParts (name := "Velvetwing Butterflies") velvetwingButterfliesOracle).get!

def velvetwingButterfliesCard : CardDef :=
  velvetwingButterflies.toCardDef
    (oracleText := velvetwingButterfliesOracle)

#guard velvetwingButterflies == .card [
  .name "Velvetwing Butterflies",
  .manaCost [.generic 2, .mono .white],
  .type .creature,
  .subtype .insect,
  .power 2,
  .toughness 2,
  .ability (.keyword .flying),
  .alternative [
    .name "Gaze in Wonder",
    .manaCost [.generic 1, .mono .white],
    .type .instant,
    .subtype .adventure,
    .actions [
      .tap (.targets 1 (.range 1 2) (.intersection [.permanent, .cardType .creature]))]]]

/-- Gatherer Oracle text for Magnificent End. -/
def magnificentEndOracle : String :=
  "This spell costs {3} less to cast if it targets a tapped creature.\nMagnificent End deals 5 damage to target creature."

def magnificentEnd : TraditionalCardDefinition := .card <|
  [
    .name "Magnificent End",
    .manaCost [.generic 4, .mono .white],
    .type .instant
  ] ++ (parseOracleParts (name := "Magnificent End") magnificentEndOracle).get!

def magnificentEndCard : CardDef :=
  magnificentEnd.toCardDef
    (oracleText := magnificentEndOracle)

#guard magnificentEnd == .card [
  .name "Magnificent End",
  .manaCost [.generic 4, .mono .white],
  .type .instant,
  .ability (
    .stackStatic
      (.if
        (.targetsIncludeAny
          .this
          (.intersection [
            .permanent,
            .cardType .creature,
            .tapped]))
        [.reduceCost .this [.mana [.generic 3]]])),
  .actions [
    .dealDamage
      .this
      (.target 1 (.intersection [.permanent, .cardType .creature]))
      (.nat 5)]]

/-- Gatherer Oracle text for Eagle of the Great Shelf. -/
def eagleOfTheGreatShelfOracle : String :=
  "Flying\nWhenever this creature attacks, it gets +1/+1 until end of turn for each other creature you control."

def eagleOfTheGreatShelf : TraditionalCardDefinition := .card <|
  [
    .name "Eagle of the Great Shelf",
    .manaCost [.generic 4, .mono .white],
    .type .creature,
    .subtype .bird,
    .subtype .soldier,
    .power 2,
    .toughness 5
  ] ++ (parseOracleParts (name := "Eagle of the Great Shelf") eagleOfTheGreatShelfOracle).get!

def eagleOfTheGreatShelfCard : CardDef :=
  eagleOfTheGreatShelf.toCardDef
    (oracleText := eagleOfTheGreatShelfOracle)

#guard
  let others : Selector :=
    .intersection [
      .not .this,
      .permanent,
      .cardType .creature,
      .controlled (.controller .this)]
  eagleOfTheGreatShelf == .card [
  .name "Eagle of the Great Shelf",
  .manaCost [.generic 4, .mono .white],
  .type .creature,
  .subtype .bird,
  .subtype .soldier,
  .power 2,
  .toughness 5,
  .ability (.keyword .flying),
  .ability (
    .triggered
      (.attack .this .all)
      (.continuous
        [.addPower (.source .this) (Value.count others),
         .addToughness (.source .this) (Value.count others)]
        .endOfTurn))]

/-- Gatherer Oracle text for Vow to Erebor. -/
def vowToEreborOracle : String :=
  "Untap target creature you control. It gets +2/+2 until end of turn. If it's a Dwarf, you may attach an Equipment you control to it."

def vowToErebor : TraditionalCardDefinition := .card <|
  [
    .name "Vow to Erebor",
    .manaCost [.generic 1, .mono .white],
    .type .instant
  ] ++ (parseOracleParts (name := "Vow to Erebor") vowToEreborOracle).get!

def vowToEreborCard : CardDef :=
  vowToErebor.toCardDef
    (oracleText := vowToEreborOracle)

#guard vowToErebor == .card [
  .name "Vow to Erebor",
  .manaCost [.generic 1, .mono .white],
  .type .instant,
  .actions [
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
          .optional
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

/-- Gatherer Oracle text for Bilbo Baggins, Burglar // Take a Glance. -/
def bilboBagginsBurglarOracle : String :=
  "When Bilbo Baggins enters, draw a card.\n//ADV//\nTake a Glance {U}\nSorcery — Adventure\nScry 2. (Then exile this card. You may cast the creature later from exile.)"

def bilboBagginsBurglar : TraditionalCardDefinition := .card <|
  [
    .name "Bilbo Baggins, Burglar",
    .manaCost [.generic 2, .mono .blue],
    .type .creature,
    .supertype .legendary,
    .subtype .halfling,
    .subtype .rogue,
    .power 2,
    .toughness 1
  ] ++ (parseOracleParts (name := "Bilbo Baggins, Burglar") bilboBagginsBurglarOracle).get!

def bilboBagginsBurglarCard : CardDef :=
  bilboBagginsBurglar.toCardDef
    (oracleText := bilboBagginsBurglarOracle)

#guard bilboBagginsBurglar == .card [
  .name "Bilbo Baggins, Burglar",
  .manaCost [.generic 2, .mono .blue],
  .type .creature,
  .supertype .legendary,
  .subtype .halfling,
  .subtype .rogue,
  .power 2,
  .toughness 1,
  .ability (.triggered (.enter .this) (.draw (.controller .this) 1)),
  .alternative [
    .name "Take a Glance",
    .manaCost [.mono .blue],
    .type .sorcery,
    .subtype .adventure,
    .actions [.scry (.controller .this) 2]]]

/-- Gatherer Oracle text for Lakeshore Apothecary. -/
def lakeshoreApothecaryOracle : String :=
  "Vigilance\nWhenever you draw your second card each turn, put a +1/+1 counter on this creature."

def lakeshoreApothecary : TraditionalCardDefinition := .card <|
  [
    .name "Lakeshore Apothecary",
    .manaCost [.generic 1, .mono .blue],
    .type .creature,
    .subtype .human,
    .subtype .cleric,
    .power 1,
    .toughness 2
  ] ++ (parseOracleParts (name := "Lakeshore Apothecary") lakeshoreApothecaryOracle).get!

def lakeshoreApothecaryCard : CardDef :=
  lakeshoreApothecary.toCardDef
    (oracleText := lakeshoreApothecaryOracle)

#guard lakeshoreApothecary == .card [
  .name "Lakeshore Apothecary",
  .manaCost [.generic 1, .mono .blue],
  .type .creature,
  .subtype .human,
  .subtype .cleric,
  .power 1,
  .toughness 2,
  .ability (.keyword .vigilance),
  .ability (
    .triggered
      (.ordinal 2 .turnStart (.draw (.controller .this) .all))
      (.putCounter (.source .this) .plusOnePlusOne 1))]

/-- Gatherer Oracle text for Confusticate and Bebother. -/
def confusticateAndBebotherOracle : String :=
  "Choose one —\n• Counter target spell unless its controller pays {4}.\n• Draw two cards, then discard a card."

def confusticateAndBebother : TraditionalCardDefinition := .card <|
  [
    .name "Confusticate and Bebother",
    .manaCost [.generic 2, .mono .blue],
    .type .instant
  ] ++ (parseOracleParts (name := "Confusticate and Bebother") confusticateAndBebotherOracle).get!

def confusticateAndBebotherCard : CardDef :=
  confusticateAndBebother.toCardDef
    (oracleText := confusticateAndBebotherOracle)

#guard confusticateAndBebother == .card [
  .name "Confusticate and Bebother",
  .manaCost [.generic 2, .mono .blue],
  .type .instant,
  .actions [
    .chooseUniqueModes (.range 1 1) [
      .preventable (.controller (.targetReference 1)) [.mana [.generic 4]]
        (.counter (.target 1 .spell)),
      .sequence [
        .draw (.controller .this) 2,
        .discard (.controller .this) 1]]]]

/-- Gatherer Oracle text for Ravenhill Flock. -/
def ravenhillFlockOracle : String :=
  "Flying\nWhenever you draw a card, put a +1/+1 counter on this creature."

def ravenhillFlock : TraditionalCardDefinition := .card <|
  [
    .name "Ravenhill Flock",
    .manaCost [.generic 3, .mono .blue],
    .type .creature,
    .subtype .bird,
    .power 1,
    .toughness 2
  ] ++ (parseOracleParts (name := "Ravenhill Flock") ravenhillFlockOracle).get!

def ravenhillFlockCard : CardDef :=
  ravenhillFlock.toCardDef
    (oracleText := ravenhillFlockOracle)

#guard ravenhillFlock == .card [
  .name "Ravenhill Flock",
  .manaCost [.generic 3, .mono .blue],
  .type .creature,
  .subtype .bird,
  .power 1,
  .toughness 2,
  .ability (.keyword .flying),
  .ability (
    .triggered
      (.draw (.controller .this) .all)
      (.putCounter (.source .this) .plusOnePlusOne 1))]

/-- Gatherer Oracle text for Thranduil's Decree. -/
def thranduilsDecreeOracle : String :=
  "Counter target spell. If a permanent spell is countered this way, exile it instead of putting it into its owner's graveyard. You may cast that card without paying its mana cost for as long as it remains exiled."

def thranduilsDecree : TraditionalCardDefinition := .card <|
  [
    .name "Thranduil's Decree",
    .manaCost [.generic 4, .mono .blue, .mono .blue],
    .type .instant
  ] ++ (parseOracleParts (name := "Thranduil's Decree") thranduilsDecreeOracle).get!

def thranduilsDecreeCard : CardDef :=
  thranduilsDecree.toCardDef
    (oracleText := thranduilsDecreeOracle)

#guard thranduilsDecree == .card [
  .name "Thranduil's Decree",
  .manaCost [.generic 4, .mono .blue, .mono .blue],
  .type .instant,
  .actions [
    .actionId 1 (.counter (.target 1 .spell)),
    .continuous
      [.replace
        (.putToGraveyard (.intersection [.wasObjectOfAction 1, .permanentSpell]))
        [.actionId 2 (.exile (.replacingObject)),
          .continuous
            [.canCastWithoutPayingManaCost (.controller .this) (.wasCreatedByAction 2)]
            .endOfGame]]
      .endOfGame]]

/-- Gatherer Oracle text for Bilbo, Luckwearer // Burglar's Plot. -/
def bilboLuckwearerOracle : String :=
  "Bilbo can't be blocked.\nWhenever Bilbo deals combat damage to a player, draw a card, then discard a card.\n//ADV//\nBurglar's Plot {4}{U}\nSorcery — Adventure\nExchange control of two target nonland permanents that share a card type. (Then exile this card. You may cast the creature later from exile.)"

def bilboLuckwearer : TraditionalCardDefinition := .card <|
  [
    .name "Bilbo, Luckwearer",
    .manaCost [.generic 1, .mono .blue],
    .type .creature,
    .supertype .legendary,
    .subtype .halfling,
    .subtype .rogue,
    .power 1,
    .toughness 1
  ] ++ (parseOracleParts (name := "Bilbo, Luckwearer") bilboLuckwearerOracle).get!

def bilboLuckwearerCard : CardDef :=
  bilboLuckwearer.toCardDef
    (oracleText := bilboLuckwearerOracle)

#guard bilboLuckwearer == .card [
  .name "Bilbo, Luckwearer",
  .manaCost [.generic 1, .mono .blue],
  .type .creature,
  .supertype .legendary,
  .subtype .halfling,
  .subtype .rogue,
  .power 1,
  .toughness 1,
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

/-- Gatherer Oracle text for Uneasy Partings. -/
def uneasyPartingsOracle : String :=
  "This spell costs {1} less to cast if it targets an attacking nontoken creature.\nTarget creature's owner puts it on their choice of the top or bottom of their library."

def uneasyPartings : TraditionalCardDefinition := .card <|
  [
    .name "Uneasy Partings",
    .manaCost [.generic 3, .mono .blue],
    .type .instant
  ] ++ (parseOracleParts (name := "Uneasy Partings") uneasyPartingsOracle).get!

def uneasyPartingsCard : CardDef :=
  uneasyPartings.toCardDef
    (oracleText := uneasyPartingsOracle)

#guard uneasyPartings == .card [
  .name "Uneasy Partings",
  .manaCost [.generic 3, .mono .blue],
  .type .instant,
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

/-- Gatherer Oracle text for Front Porch Sentries. -/
def frontPorchSentriesOracle : String :=
  "When this creature dies, target creature an opponent controls gets -1/-1 until end of turn."

def frontPorchSentries : TraditionalCardDefinition := .card <|
  [
    .name "Front Porch Sentries",
    .manaCost [.generic 1, .mono .black],
    .type .creature,
    .subtype .goblin,
    .subtype .soldier,
    .power 2,
    .toughness 2
  ] ++ (parseOracleParts (name := "Front Porch Sentries") frontPorchSentriesOracle).get!

def frontPorchSentriesCard : CardDef :=
  frontPorchSentries.toCardDef
    (oracleText := frontPorchSentriesOracle)

#guard frontPorchSentries == .card [
  .name "Front Porch Sentries",
  .manaCost [.generic 1, .mono .black],
  .type .creature,
  .subtype .goblin,
  .subtype .soldier,
  .power 2,
  .toughness 2,
  .ability (
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

/-- Gatherer Oracle text for Great Fierce Bee. -/
def greatFierceBeeOracle : String :=
  "Flying\nWhenever one or more other creatures die, scry 1. (Look at the top card of your library. You may put that card on the bottom.)"

def greatFierceBee : TraditionalCardDefinition := .card <|
  [
    .name "Great Fierce Bee",
    .manaCost [.generic 2, .mono .black],
    .type .creature,
    .subtype .insect,
    .power 2,
    .toughness 2
  ] ++ (parseOracleParts (name := "Great Fierce Bee") greatFierceBeeOracle).get!

def greatFierceBeeCard : CardDef :=
  greatFierceBee.toCardDef
    (oracleText := greatFierceBeeOracle)

#guard greatFierceBee == .card [
  .name "Great Fierce Bee",
  .manaCost [.generic 2, .mono .black],
  .type .creature,
  .subtype .insect,
  .power 2,
  .toughness 2,
  .ability (.keyword .flying),
  .ability (
    .triggered
      (.dieSimultaneously (.intersection [.not .this, .permanent, .cardType .creature]) [])
      (.scry (.controller .this) 1))]

/-- Gatherer Oracle text for Stir Up Trouble. -/
def stirUpTroubleOracle : String :=
  "As an additional cost to cast this spell, sacrifice an artifact or creature or pay {4}.\nDestroy target creature."

def stirUpTrouble : TraditionalCardDefinition := .card <|
  [
    .name "Stir Up Trouble",
    .manaCost [.mono .black],
    .type .sorcery
  ] ++ (parseOracleParts (name := "Stir Up Trouble") stirUpTroubleOracle).get!

def stirUpTroubleCard : CardDef :=
  stirUpTrouble.toCardDef
    (oracleText := stirUpTroubleOracle)

#guard stirUpTrouble == .card [
  .name "Stir Up Trouble",
  .manaCost [.mono .black],
  .type .sorcery,
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

/-- Gatherer Oracle text for Desolation Prowler. -/
def desolationProwlerOracle : String :=
  "Pay 2 life: This creature gets +2/+2 until end of turn. Activate only once each turn."

def desolationProwler : TraditionalCardDefinition := .card <|
  [
    .name "Desolation Prowler",
    .manaCost [.generic 1, .mono .black],
    .type .creature,
    .subtype .wolf,
    .power 2,
    .toughness 2
  ] ++ (parseOracleParts (name := "Desolation Prowler") desolationProwlerOracle).get!

def desolationProwlerCard : CardDef :=
  desolationProwler.toCardDef
    (oracleText := desolationProwlerOracle)

#guard desolationProwler == .card [
  .name "Desolation Prowler",
  .manaCost [.generic 1, .mono .black],
  .type .creature,
  .subtype .wolf,
  .power 2,
  .toughness 2,
  .ability (
    .abilityId 1
      (.activatedIf
        (.didNotHappen (.abilityWithIdActivated 1) .turnStart)
        [.life 2]
        (.continuous
          [.addPower (.source .this) (Value.int 2),
           .addToughness (.source .this) (Value.int 2)]
          .endOfTurn)))]

/-- Gatherer Oracle text for Ravening Warg. -/
def raveningWargOracle : String :=
  "Deathtouch\nFerocious — Whenever this creature attacks while you control a creature with power 4 or greater, you gain 2 life."

def raveningWarg : TraditionalCardDefinition := .card <|
  [
    .name "Ravening Warg",
    .manaCost [.generic 1, .mono .black],
    .type .creature,
    .subtype .wolf,
    .power 2,
    .toughness 2
  ] ++ (parseOracleParts (name := "Ravening Warg") raveningWargOracle).get!

def raveningWargCard : CardDef :=
  raveningWarg.toCardDef
    (oracleText := raveningWargOracle)

#guard raveningWarg == .card [
  .name "Ravening Warg",
  .manaCost [.generic 1, .mono .black],
  .type .creature,
  .subtype .wolf,
  .power 2,
  .toughness 2,
  .ability (.keyword .deathtouch),
  .ability (
    .triggeredWhile
      (.attack .this .all)
      (.any
        (.intersection [
          .permanent,
          .cardType .creature,
          .controlled (.controller .this),
          .powerAtLeast (Value.int 4)]))
      (.gainLife (.controller .this) 2))]

/-- Gatherer Oracle text for Gollum, Silent Slinker // Meager Meal. -/
def gollumSilentSlinkerOracle : String :=
  "Menace (This creature can't be blocked except by two or more creatures.)\n//ADV//\nMeager Meal {B}\nSorcery — Adventure\nPut a +1/+1 counter on up to one target creature. Target player gains 2 life. (Then exile this card. You may cast the creature later from exile.)"

def gollumSilentSlinker : TraditionalCardDefinition := .card <|
  [
    .name "Gollum, Silent Slinker",
    .manaCost [.generic 3, .mono .black],
    .type .creature,
    .supertype .legendary,
    .subtype .halfling,
    .subtype .horror,
    .power 4,
    .toughness 3
  ] ++ (parseOracleParts (name := "Gollum, Silent Slinker") gollumSilentSlinkerOracle).get!

def gollumSilentSlinkerCard : CardDef :=
  gollumSilentSlinker.toCardDef
    (oracleText := gollumSilentSlinkerOracle)

#guard gollumSilentSlinker == .card [
  .name "Gollum, Silent Slinker",
  .manaCost [.generic 3, .mono .black],
  .type .creature,
  .supertype .legendary,
  .subtype .halfling,
  .subtype .horror,
  .power 4,
  .toughness 3,
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

/-- Gatherer Oracle text for Bilbo's Deadly Slice. -/
def bilbosDeadlySliceOracle : String :=
  "Destroy target creature."

def bilbosDeadlySlice : TraditionalCardDefinition := .card <|
  [
    .name "Bilbo's Deadly Slice",
    .manaCost [.generic 1, .mono .black, .mono .black],
    .type .instant
  ] ++ (parseOracleParts (name := "Bilbo's Deadly Slice") bilbosDeadlySliceOracle).get!

def bilbosDeadlySliceCard : CardDef :=
  bilbosDeadlySlice.toCardDef
    (oracleText := bilbosDeadlySliceOracle)

#guard bilbosDeadlySlice == .card [
  .name "Bilbo's Deadly Slice",
  .manaCost [.generic 1, .mono .black, .mono .black],
  .type .instant,
  .actions [
    .destroy (.target 1 (.intersection [.permanent, .cardType .creature]))]]

/-- Gatherer Oracle text for Dreaded Bat-Cloud. -/
def dreadedBatCloudOracle : String :=
  "This spell costs {3} less to cast if a creature died this turn.\nFlying, deathtouch"

def dreadedBatCloud : TraditionalCardDefinition := .card <|
  [
    .name "Dreaded Bat-Cloud",
    .manaCost [.generic 4, .mono .black],
    .type .creature,
    .subtype .bat,
    .power 4,
    .toughness 2
  ] ++ (parseOracleParts (name := "Dreaded Bat-Cloud") dreadedBatCloudOracle).get!

def dreadedBatCloudCard : CardDef :=
  dreadedBatCloud.toCardDef
    (oracleText := dreadedBatCloudOracle)

#guard dreadedBatCloud == .card [
  .name "Dreaded Bat-Cloud",
  .manaCost [.generic 4, .mono .black],
  .type .creature,
  .subtype .bat,
  .power 4,
  .toughness 2,
  .ability (
    .stackStatic
      (.if
        (.happened (.die (.cardType .creature)) .turnStart)
        [.reduceCost .this [.mana [.generic 3]]])),
  .ability (.keyword .flying),
  .ability (.keyword .deathtouch)]

/-- Gatherer Oracle text for Crude Bent Blade. -/
def crudeBentBladeOracle : String :=
  "When this Equipment enters, target opponent sacrifices a creature of their choice.\nEquipped creature gets +2/+1.\nEquip {2} ({2}: Attach to target creature you control. Equip only as a sorcery.)"

def crudeBentBlade : TraditionalCardDefinition := .card <|
  [
    .name "Crude Bent Blade",
    .manaCost [.generic 2, .mono .black],
    .type .artifact,
    .subtype .equipment
  ] ++ (parseOracleParts (name := "Crude Bent Blade") crudeBentBladeOracle).get!

def crudeBentBladeCard : CardDef :=
  crudeBentBlade.toCardDef
    (oracleText := crudeBentBladeOracle)

#guard crudeBentBlade == .card [
  .name "Crude Bent Blade",
  .manaCost [.generic 2, .mono .black],
  .type .artifact,
  .subtype .equipment,
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
  .ability (.keywordWithCost .equip [.mana [.generic 2]])
]

/-- Gatherer Oracle text for Gollum the Abandoned. -/
def gollumTheAbandonedOracle : String :=
  "Gollum can't block.\nWhen Gollum enters, exile up to one target card from an opponent's graveyard. Each opponent loses 2 life.\n{2}, Sacrifice an artifact or creature: Return this card from your graveyard to your hand. Activate only as a sorcery."

def gollumTheAbandoned : TraditionalCardDefinition := .card <|
  [
    .name "Gollum the Abandoned",
    .manaCost [.generic 1, .mono .black],
    .type .creature,
    .supertype .legendary,
    .subtype .halfling,
    .subtype .horror,
    .power 2,
    .toughness 2
  ] ++ (parseOracleParts (name := "Gollum the Abandoned") gollumTheAbandonedOracle).get!

def gollumTheAbandonedCard : CardDef :=
  gollumTheAbandoned.toCardDef
    (oracleText := gollumTheAbandonedOracle)

#guard gollumTheAbandoned == .card [
  .name "Gollum the Abandoned",
  .manaCost [.generic 1, .mono .black],
  .type .creature,
  .supertype .legendary,
  .subtype .halfling,
  .subtype .horror,
  .power 2,
  .toughness 2,
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
      (.returnToHand (.intersection [.inGraveyard, .source .this])))
]

/-- Gatherer Oracle text for Gnashing of Teeth. -/
def gnashingOfTeethOracle : String :=
  "Choose one —\n• Target creature gets -5/-5 until end of turn. If that creature would die this turn, exile it instead.\n• Creatures target player controls get -1/-1 until end of turn."

def gnashingOfTeeth : TraditionalCardDefinition := .card <|
  [
    .name "Gnashing of Teeth",
    .manaCost [.generic 1, .mono .black, .mono .black],
    .type .sorcery
  ] ++ (parseOracleParts (name := "Gnashing of Teeth") gnashingOfTeethOracle).get!

def gnashingOfTeethCard : CardDef :=
  gnashingOfTeeth.toCardDef
    (oracleText := gnashingOfTeethOracle)

#guard gnashingOfTeeth == .card [
  .name "Gnashing of Teeth",
  .manaCost [.generic 1, .mono .black, .mono .black],
  .type .sorcery,
  .actions [
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
        .endOfTurn]]
]

/-- Gatherer Oracle text for Reverent Howl. -/
def reverentHowlOracle : String :=
  "Choose one —\n• Target player draws two cards and loses 2 life.\n• Target creature gets +2/+2 and gains lifelink until end of turn."

def reverentHowl : TraditionalCardDefinition := .card <|
  [
    .name "Reverent Howl",
    .manaCost [.generic 2, .mono .black],
    .type .instant
  ] ++ (parseOracleParts (name := "Reverent Howl") reverentHowlOracle).get!

def reverentHowlCard : CardDef :=
  reverentHowl.toCardDef
    (oracleText := reverentHowlOracle)

#guard reverentHowl == .card [
  .name "Reverent Howl",
  .manaCost [.generic 2, .mono .black],
  .type .instant,
  .actions [
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
        .endOfTurn]]
]

/-- Gatherer Oracle text for Stony-Voiced Goblins. -/
def stonyVoicedGoblinsOracle : String :=
  "When this creature enters, each opponent discards a card."

def stonyVoicedGoblins : TraditionalCardDefinition := .card <|
  [
    .name "Stony-Voiced Goblins",
    .manaCost [.generic 1, .mono .black],
    .type .creature,
    .subtype .goblin,
    .subtype .bard,
    .power 1,
    .toughness 1
  ] ++ (parseOracleParts (name := "Stony-Voiced Goblins") stonyVoicedGoblinsOracle).get!

def stonyVoicedGoblinsCard : CardDef :=
  stonyVoicedGoblins.toCardDef
    (oracleText := stonyVoicedGoblinsOracle)

#guard stonyVoicedGoblins == .card [
  .name "Stony-Voiced Goblins",
  .manaCost [.generic 1, .mono .black],
  .type .creature,
  .subtype .goblin,
  .subtype .bard,
  .power 1,
  .toughness 1,
  .ability (
    .triggered
      (.enter .this)
      (.discard (.opponent (.controller .this)) 1))
]

/-- Gatherer Oracle text for Smaug, the Great Calamity // Spew Flame. -/
def smaugTheGreatCalamityOracle : String :=
  "Flying\n//ADV//\nSpew Flame {4}{R}\nSorcery — Adventure\nSpew Flame deals 5 damage to target creature. (Then exile this card. You may cast the creature later from exile.)"

def smaugTheGreatCalamity : TraditionalCardDefinition := .card <|
  [
    .name "Smaug, the Great Calamity",
    .manaCost [.generic 5, .mono .red, .mono .red],
    .type .creature,
    .supertype .legendary,
    .subtype .dragon,
    .power 5,
    .toughness 5
  ] ++ (parseOracleParts (name := "Smaug, the Great Calamity") smaugTheGreatCalamityOracle).get!

def smaugTheGreatCalamityCard : CardDef :=
  smaugTheGreatCalamity.toCardDef
    (oracleText := smaugTheGreatCalamityOracle)

#guard smaugTheGreatCalamity == .card [
  .name "Smaug, the Great Calamity",
  .manaCost [.generic 5, .mono .red, .mono .red],
  .type .creature,
  .supertype .legendary,
  .subtype .dragon,
  .power 5,
  .toughness 5,
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
        (.nat 5)]]
]

/-- Gatherer Oracle text for Gandalf, Spark Starter. -/
def gandalfSparkStarterOracle : String :=
  "Reach\nWhen Gandalf enters, he deals 3 damage divided as you choose among one, two, or three targets."

def gandalfSparkStarter : TraditionalCardDefinition := .card <|
  [
    .name "Gandalf, Spark Starter",
    .manaCost [.generic 4, .mono .red, .mono .red],
    .type .creature,
    .supertype .legendary,
    .subtype .avatar,
    .subtype .wizard,
    .power 4,
    .toughness 3
  ] ++ (parseOracleParts (name := "Gandalf, Spark Starter") gandalfSparkStarterOracle).get!

def gandalfSparkStarterCard : CardDef :=
  gandalfSparkStarter.toCardDef
    (oracleText := gandalfSparkStarterOracle)

#guard gandalfSparkStarter == .card [
  .name "Gandalf, Spark Starter",
  .manaCost [.generic 4, .mono .red, .mono .red],
  .type .creature,
  .supertype .legendary,
  .subtype .avatar,
  .subtype .wizard,
  .power 4,
  .toughness 3,
  .ability (.keyword .reach),
  .ability (
    .triggered
      (.enter .this)
      (.divideDamage
        (.controller .this)
        (.source .this)
        (.targets 1 (.range 1 3) .all)
        3))
]

/-- Gatherer Oracle text for Ragged Short Spear. -/
def raggedShortSpearOracle : String :=
  "When this Equipment enters, you may discard a card. If you do, draw two cards.\nEquipped creature gets +2/+0.\nEquip {3} ({3}: Attach to target creature you control. Equip only as a sorcery.)"

def raggedShortSpear : TraditionalCardDefinition := .card <|
  [
    .name "Ragged Short Spear",
    .manaCost [.generic 1, .mono .red],
    .type .artifact,
    .subtype .equipment
  ] ++ (parseOracleParts (name := "Ragged Short Spear") raggedShortSpearOracle).get!

def raggedShortSpearCard : CardDef :=
  raggedShortSpear.toCardDef
    (oracleText := raggedShortSpearOracle)

#guard raggedShortSpear == .card [
  .name "Ragged Short Spear",
  .manaCost [.generic 1, .mono .red],
  .type .artifact,
  .subtype .equipment,
  .ability (
    .triggered
      (.enter .this)
      (.sequence [
        .optional
          (.actionId 1 (.discard (.controller .this) 1)),
        .if (.happened (.actionWithId 1) .gameStart) [.draw (.controller .this) 2]])),
  .ability (.static (.addPower (.hostOf .this) (Value.int 2))),
  .ability (.keywordWithCost .equip [.mana [.generic 3]])
]

/-- Gatherer Oracle text for Snowslope Hunter. -/
def snowslopeHunterOracle : String :=
  "Sacrifice another creature or artifact: Exile the top card of your library. You may play it until the end of your next turn. Activate only during your turn and only once each turn."

def snowslopeHunter : TraditionalCardDefinition := .card <|
  [
    .name "Snowslope Hunter",
    .manaCost [.generic 2, .mono .red],
    .type .creature,
    .subtype .goblin,
    .subtype .ranger,
    .power 2,
    .toughness 3
  ] ++ (parseOracleParts (name := "Snowslope Hunter") snowslopeHunterOracle).get!

def snowslopeHunterCard : CardDef :=
  snowslopeHunter.toCardDef
    (oracleText := snowslopeHunterOracle)

#guard snowslopeHunter == .card [
  .name "Snowslope Hunter",
  .manaCost [.generic 2, .mono .red],
  .type .creature,
  .subtype .goblin,
  .subtype .ranger,
  .power 2,
  .toughness 3,
  .ability (
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
          .actionId 1 (.exile (.topOfLibrary (.controller .this))),
          .continuous
            [.canPlay (.controller .this) (.wasCreatedByAction 1)]
            (.sequence [.turnStart, .endOfPlayerTurn (.controller .this)])])))
]

/-- Gatherer Oracle text for Guardian of the Halls. -/
def guardianOfTheHallsOracle : String :=
  "Trample\n{5}{G}{G}: Put three +1/+1 counters on this creature."

def guardianOfTheHalls : TraditionalCardDefinition := .card <|
  [
    .name "Guardian of the Halls",
    .manaCost [.generic 1, .mono .green],
    .type .creature,
    .subtype .elf,
    .subtype .soldier,
    .power 2,
    .toughness 2
  ] ++ (parseOracleParts (name := "Guardian of the Halls") guardianOfTheHallsOracle).get!

def guardianOfTheHallsCard : CardDef :=
  guardianOfTheHalls.toCardDef
    (oracleText := guardianOfTheHallsOracle)

#guard guardianOfTheHalls == .card [
  .name "Guardian of the Halls",
  .manaCost [.generic 1, .mono .green],
  .type .creature,
  .subtype .elf,
  .subtype .soldier,
  .power 2,
  .toughness 2,
  .ability (.keyword .trample),
  .ability (
    .activated
      [.mana [.generic 5, .mono .green, .mono .green]]
      (.putCounter (.source .this) .plusOnePlusOne 3))
]

/-- Gatherer Oracle text for Quarrel. -/
def quarrelOracle : String :=
  "Target creature you control deals damage equal to its power to target creature an opponent controls."

def quarrel : TraditionalCardDefinition := .card <|
  [
    .name "Quarrel",
    .manaCost [.generic 1, .mono .green],
    .type .instant
  ] ++ (parseOracleParts (name := "Quarrel") quarrelOracle).get!

def quarrelCard : CardDef :=
  quarrel.toCardDef
    (oracleText := quarrelOracle)

#guard quarrel == .card [
  .name "Quarrel",
  .manaCost [.generic 1, .mono .green],
  .type .instant,
  .actions [
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
          .controlled (.opponent (.controller .this))]))]
]

/-- Gatherer Oracle text for Galion, Elvenking's Butler. -/
def galionElvenkingsButlerOracle : String :=
  "Whenever Galion attacks, choose up to one other target creature you control. Its base power and toughness become equal to Galion's power and toughness until end of turn."

def galionElvenkingsButler : TraditionalCardDefinition := .card <|
  [
    .name "Galion, Elvenking's Butler",
    .manaCost [.generic 2, .mono .green, .mono .green],
    .type .creature,
    .supertype .legendary,
    .subtype .elf,
    .subtype .advisor,
    .power 4,
    .toughness 4
  ] ++ (parseOracleParts (name := "Galion, Elvenking's Butler") galionElvenkingsButlerOracle).get!

def galionElvenkingsButlerCard : CardDef :=
  galionElvenkingsButler.toCardDef
    (oracleText := galionElvenkingsButlerOracle)

#guard galionElvenkingsButler == .card [
  .name "Galion, Elvenking's Butler",
  .manaCost [.generic 2, .mono .green, .mono .green],
  .type .creature,
  .supertype .legendary,
  .subtype .elf,
  .subtype .advisor,
  .power 4,
  .toughness 4,
  .ability (
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
        .endOfTurn))
]

/-- Gatherer Oracle text for Warg Tactics. -/
def wargTacticsOracle : String :=
  "Choose one —\n• Destroy target creature with flying.\n• Put a +1/+1 counter on target creature you control. It gains trample and hexproof until end of turn. (It can't be the target of spells or abilities your opponents control.)"

def wargTactics : TraditionalCardDefinition := .card <|
  [
    .name "Warg Tactics",
    .manaCost [.generic 1, .mono .green],
    .type .instant
  ] ++ (parseOracleParts (name := "Warg Tactics") wargTacticsOracle).get!

def wargTacticsCard : CardDef :=
  wargTactics.toCardDef
    (oracleText := wargTacticsOracle)

#guard wargTactics == .card [
  .name "Warg Tactics",
  .manaCost [.generic 1, .mono .green],
  .type .instant,
  .actions [
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
          .endOfTurn]]]
]

/-- Gatherer Oracle text for Beorn's Hospitality. -/
def beornsHospitalityOracle : String :=
  "Landfall — Whenever a land you control enters, put a +1/+1 counter on target creature you control.\n{5}{G}{G}: This enchantment becomes a Bear creature in addition to its other types and gains \"This creature's power and toughness are each equal to the number of lands you control.\" (This effect doesn't end.)"

def beornsHospitality : TraditionalCardDefinition := .card <|
  [
    .name "Beorn's Hospitality",
    .manaCost [.generic 1, .mono .green],
    .type .enchantment
  ] ++ (parseOracleParts (name := "Beorn's Hospitality") beornsHospitalityOracle).get!

def beornsHospitalityCard : CardDef :=
  beornsHospitality.toCardDef
    (oracleText := beornsHospitalityOracle)

#guard beornsHospitality == .card [
  .name "Beorn's Hospitality",
  .manaCost [.generic 1, .mono .green],
  .type .enchantment,
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
        .endOfGame))
]

/-- Gatherer Oracle text for Woodland Weavemaster. -/
def woodlandWeavemasterOracle : String :=
  "Vigilance\nWhenever another Elf you control enters, this creature gets +1/+1 until end of turn.\n{T}: Add X mana of any one color, where X is this creature's power. Spend this mana only to cast Elf spells and activate abilities of Elf sources."

def woodlandWeavemaster : TraditionalCardDefinition := .card <|
  [
    .name "Woodland Weavemaster",
    .manaCost [.generic 1, .mono .green],
    .type .creature,
    .subtype .elf,
    .subtype .druid,
    .power 1,
    .toughness 2
  ] ++ (parseOracleParts (name := "Woodland Weavemaster") woodlandWeavemasterOracle).get!

def woodlandWeavemasterCard : CardDef :=
  woodlandWeavemaster.toCardDef
    (oracleText := woodlandWeavemasterOracle)

#guard woodlandWeavemaster == .card [
  .name "Woodland Weavemaster",
  .manaCost [.generic 1, .mono .green],
  .type .creature,
  .subtype .elf,
  .subtype .druid,
  .power 1,
  .toughness 2,
  .ability (.keyword .vigilance),
  .ability (
    .triggered
      (.enter
        (.intersection [
          .not .this,
          .permanent,
          .subtype .elf,
          .controlled (.controller .this)]))
      (.continuous [.addPower (.source .this) (Value.int 1),
                    .addToughness (.source .this) (Value.int 1)] .endOfTurn)),
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
]

/-- Gatherer Oracle text for Mirkwood Pathmaker. -/
def mirkwoodPathmakerOracle : String :=
  "Mirkwood Pathmaker's power and toughness are each equal to the number of lands you control."

def mirkwoodPathmakerDefinition : TraditionalCardDefinition := .card <|
  [
    .name "Mirkwood Pathmaker",
    .manaCost [.generic 2, .mono .green],
    .type .creature,
    .subtype .elf,
    .subtype .ranger
  ] ++ (parseOracleParts (name := "Mirkwood Pathmaker") mirkwoodPathmakerOracle).get!

def mirkwoodPathmaker : CardDef :=
  mirkwoodPathmakerDefinition.toCardDef
    (oracleText := mirkwoodPathmakerOracle)

#guard mirkwoodPathmakerDefinition == .card [
  .name "Mirkwood Pathmaker",
  .manaCost [.generic 2, .mono .green],
  .type .creature,
  .subtype .elf,
  .subtype .ranger,
  .ability
    (.static
      (.setPower
        .this
        (.count
          (.intersection [
            .permanent,
            .cardType .land,
            .controlled (.controller .this)])))),
  .ability
    (.static
      (.setToughness
        .this
        (.count
          (.intersection [
            .permanent,
            .cardType .land,
            .controlled (.controller .this)]))))
]

/-- Gatherer Oracle text for Beorn, Reluctant Host // Till and Tend. -/
def beornReluctantHostOracle : String :=
  "Trample\n//ADV//\nTill and Tend {1}{G}\nSorcery — Adventure\nYou may play an additional land this turn. (Then exile this card. You may cast the creature later from exile.)"

def beornReluctantHostDefinition : TraditionalCardDefinition := .card <|
  [
    .name "Beorn, Reluctant Host",
    .manaCost [.generic 4, .mono .green],
    .type .creature,
    .supertype .legendary,
    .subtype .human,
    .subtype .bear,
    .subtype .shapeshifter,
    .power 5,
    .toughness 5
  ] ++ (parseOracleParts (name := "Beorn, Reluctant Host") beornReluctantHostOracle).get!

def beornReluctantHost : CardDef :=
  beornReluctantHostDefinition.toCardDef
    (oracleText := beornReluctantHostOracle)

#guard beornReluctantHostDefinition == .card [
  .name "Beorn, Reluctant Host",
  .manaCost [.generic 4, .mono .green],
  .type .creature,
  .supertype .legendary,
  .subtype .human,
  .subtype .bear,
  .subtype .shapeshifter,
  .power 5,
  .toughness 5,
  .ability (.keyword .trample),
  .alternative [
    .name "Till and Tend",
    .manaCost [.generic 1, .mono .green],
    .type .sorcery,
    .subtype .adventure,
    .actions [
      .continuous
        [.increaseLandPlayLimit (.controller .this) (Value.nat 1)]
        .endOfTurn]]
]

/-- Gatherer Oracle text for Wood Elves. -/
def woodElvesOracle : String :=
  "When this creature enters, search your library for a Forest card, put that card onto the battlefield, then shuffle."

def woodElvesDefinition : TraditionalCardDefinition := .card <|
  [
    .name "Wood Elves",
    .manaCost [.generic 2, .mono .green],
    .type .creature,
    .subtype .elf,
    .subtype .scout,
    .power 1,
    .toughness 1
  ] ++ (parseOracleParts (name := "Wood Elves") woodElvesOracle).get!

def woodElves : CardDef :=
  woodElvesDefinition.toCardDef
    (oracleText := woodElvesOracle)

#guard woodElvesDefinition == .card [
  .name "Wood Elves",
  .manaCost [.generic 2, .mono .green],
  .type .creature,
  .subtype .elf,
  .subtype .scout,
  .power 1,
  .toughness 1,
  .ability (
    .triggered
      (.enter .this)
      (.searchLibraryThenShuffle
        (.controller .this)
        [
          .putOntoBattlefield
            (.selected
              (.controller .this)
              (.range 1 1)
              (.intersection [.inLibrary, .subtype .forest]))]))
]

/-- Gatherer Oracle text for Attercop. -/
def attercopOracle : String :=
  "Reach, deathtouch\nLandfall — Whenever a land you control enters, this creature gets +1/+1 until end of turn."

def attercopDefinition : TraditionalCardDefinition := .card <|
  [
    .name "Attercop",
    .manaCost [.generic 1, .mono .green],
    .type .creature,
    .subtype .spider,
    .power 2,
    .toughness 1
  ] ++ (parseOracleParts (name := "Attercop") attercopOracle).get!

def attercop : CardDef :=
  attercopDefinition.toCardDef
    (oracleText := attercopOracle)

#guard attercopDefinition == .card [
  .name "Attercop",
  .manaCost [.generic 1, .mono .green],
  .type .creature,
  .subtype .spider,
  .power 2,
  .toughness 1,
  .ability (.keyword .reach),
  .ability (.keyword .deathtouch),
  .ability (
    .triggered
      (.enter
        (.intersection [
          .permanent,
          .cardType .land,
          .controlled (.controller .this)]))
      (.continuous [.addPower (.source .this) (Value.int 1),
                    .addToughness (.source .this) (Value.int 1)] .endOfTurn))
]

def ordinaryBear : CardDef :=
  (TraditionalCardDefinition.card [
    .name "Ordinary Bear",
    .manaCost [.generic 3, .mono .green],
    .type .creature,
    .subtype .bear,
    .power 4,
    .toughness 5
  ]).toCardDef

/-- Gatherer Oracle text for Large Bear. -/
def largeBearOracle : String :=
  "Reach, trample, haste"

def largeBearDefinition : TraditionalCardDefinition := .card <|
  [
    .name "Large Bear",
    .manaCost [.generic 3, .hybrid .black .green, .hybrid .black .green],
    .type .creature,
    .subtype .bear,
    .power 5,
    .toughness 5
  ] ++ (parseOracleParts (name := "Large Bear") largeBearOracle).get!

def largeBear : CardDef :=
  largeBearDefinition.toCardDef
    (oracleText := largeBearOracle)

#guard largeBearDefinition == .card [
  .name "Large Bear",
  .manaCost [.generic 3, .hybrid .black .green, .hybrid .black .green],
  .type .creature,
  .subtype .bear,
  .power 5,
  .toughness 5,
  .ability (.keyword .reach),
  .ability (.keyword .trample),
  .ability (.keyword .haste)
]

/-- Gatherer Oracle text for Little Bear. -/
def littleBearOracle : String :=
  "Flash\nWhen this creature enters, untap another target creature you control. If that creature is a Bear, put a +1/+1 counter on it."

def littleBearDefinition : TraditionalCardDefinition := .card <|
  [
    .name "Little Bear",
    .manaCost [.generic 2, .mono .green],
    .type .creature,
    .subtype .bear,
    .power 3,
    .toughness 2
  ] ++ (parseOracleParts (name := "Little Bear") littleBearOracle).get!

def littleBear : CardDef :=
  littleBearDefinition.toCardDef
    (oracleText := littleBearOracle)

#guard littleBearDefinition == .card [
  .name "Little Bear",
  .manaCost [.generic 2, .mono .green],
  .type .creature,
  .subtype .bear,
  .power 3,
  .toughness 2,
  .ability (.keyword .flash),
  .ability (
    .triggered
      (.enter .this)
      (.sequence [
        .untap
          (.target
            1
            (.intersection [
              .not .this,
              .permanent,
              .cardType .creature,
              .controlled (.controller .this)])),
        .if
          (.anySubtype (.targetReference 1) .bear)
          [.putCounter (.targetReference 1) .plusOnePlusOne 1]]))
]

/-- Gatherer Oracle text for Elvenking's Harper. -/
def elvenkingsHarperOracle : String :=
  "{4}{U}: Target creature can't be blocked this turn."

def elvenkingsHarperDefinition : TraditionalCardDefinition := .card <|
  [
    .name "Elvenking's Harper",
    .manaCost [.generic 1, .mono .blue],
    .type .creature,
    .subtype .elf,
    .subtype .bard,
    .power 2,
    .toughness 2
  ] ++ (parseOracleParts (name := "Elvenking's Harper") elvenkingsHarperOracle).get!

def elvenkingsHarper : CardDef :=
  elvenkingsHarperDefinition.toCardDef
    (oracleText := elvenkingsHarperOracle)

#guard elvenkingsHarperDefinition == .card [
  .name "Elvenking's Harper",
  .manaCost [.generic 1, .mono .blue],
  .type .creature,
  .subtype .elf,
  .subtype .bard,
  .power 2,
  .toughness 2,
  .ability (
    .activated
      [.mana [.generic 4, .mono .blue]]
      (.continuous
        [.forbid
          (.block
            .any
            (.target 1 (.intersection [.permanent, .cardType .creature])))]
        .endOfTurn))
]

/-- Gatherer Oracle text for Smaug's Fury. -/
def smaugsFuryOracle : String :=
  "Target creature gets +3/+0 and gains reach and first strike until end of turn."

def smaugsFuryDefinition : TraditionalCardDefinition := .card <|
  [
    .name "Smaug's Fury",
    .manaCost [.generic 1, .mono .red],
    .type .instant
  ] ++ (parseOracleParts (name := "Smaug's Fury") smaugsFuryOracle).get!

def smaugsFury : CardDef :=
  smaugsFuryDefinition.toCardDef
    (oracleText := smaugsFuryOracle)

#guard smaugsFuryDefinition == .card [
  .name "Smaug's Fury",
  .manaCost [.generic 1, .mono .red],
  .type .instant,
  .actions [
    .continuous
      [
        .addPower
          (.target 1 (.intersection [.permanent, .cardType .creature])) (Value.int 3),
        .gainAbility (.targetReference 1) (.keyword .reach),
        .gainAbility (.targetReference 1) (.keyword .firstStrike)]
      .endOfTurn]
]

/-- Gatherer Oracle text for Well-Worn Spatula. -/
def wellWornSpatulaOracle : String :=
  "When this Equipment enters, you gain 2 life.\nEquipped creature gets +1/+1.\nEquip {1} ({1}: Attach to target creature you control. Equip only as a sorcery.)"

def wellWornSpatulaDefinition : TraditionalCardDefinition := .card <|
  [
    .name "Well-Worn Spatula",
    .manaCost [.generic 1],
    .type .artifact,
    .subtype .equipment
  ] ++ (parseOracleParts (name := "Well-Worn Spatula") wellWornSpatulaOracle).get!

def wellWornSpatula : CardDef :=
  wellWornSpatulaDefinition.toCardDef
    (oracleText := wellWornSpatulaOracle)

#guard wellWornSpatulaDefinition == .card [
  .name "Well-Worn Spatula",
  .manaCost [.generic 1],
  .type .artifact,
  .subtype .equipment,
  .ability (
    .triggered
      (.enter .this)
      (.gainLife (.controller .this) 2)),
  .ability (.static (.addPower (.hostOf .this) (Value.int 1))),
  .ability (.static (.addToughness (.hostOf .this) (Value.int 1))),
  .ability (.keywordWithCost .equip [.mana [.generic 1]])
]

/-- Gatherer Oracle text for Elvenking's Halls. -/
def elvenkingsHallsOracle : String :=
  "This land enters tapped.\n{T}: Add {G} or {U}.\n{2}{G}{U}, {T}, Sacrifice this land: Put two +1/+1 counters on target Elf you control. Activate only as a sorcery."

def elvenkingsHallsDefinition : TraditionalCardDefinition := .card <|
  [
    .name "Elvenking's Halls",
    .type .land
  ] ++ (parseOracleParts (name := "Elvenking's Halls") elvenkingsHallsOracle).get!

def elvenkingsHalls : CardDef :=
  elvenkingsHallsDefinition.toCardDef
    (oracleText := elvenkingsHallsOracle)

#guard elvenkingsHallsDefinition == .card [
    .name "Elvenking's Halls",
    .type .land,
    .ability (
      .static
        (.replace
          (.enter .this)
          [.putOntoBattlefieldInState .this [.tapped]])),
    .ability (
      .activated
        [.tapSymbol]
        (.playerSelectAction
          (.controller .this)
          (.range 1 1)
          [
            .addMana (.controller .this) [.mono .green],
            .addMana (.controller .this) [.mono .blue]])),
    .ability (
      .activatedIf
        (.timeToCastSorcery (.controller .this))
        [
          .mana [.generic 2, .mono .green, .mono .blue],
          .tapSymbol,
          .sacrifice .this]
        (.putCounter
          (.target
            1
            (.intersection [
              .permanent,
              .cardType .creature,
              .subtype .elf,
              .controlled (.controller .this)]))
          .plusOnePlusOne
          2))
]

/-- Gatherer Oracle text for Iron Hills. -/
def ironHillsOracle : String :=
  "This land enters tapped.\n{T}: Add {R} or {W}.\n{2}{R}{W}, {T}, Sacrifice this land: Put two +1/+1 counters on target Dwarf you control. Activate only as a sorcery."

def ironHillsDefinition : TraditionalCardDefinition := .card <|
  [
    .name "Iron Hills",
    .type .land
  ] ++ (parseOracleParts (name := "Iron Hills") ironHillsOracle).get!

def ironHills : CardDef :=
  ironHillsDefinition.toCardDef
    (oracleText := ironHillsOracle)

#guard ironHillsDefinition == .card [
    .name "Iron Hills",
    .type .land,
    .ability (
      .static
        (.replace
          (.enter .this)
          [.putOntoBattlefieldInState .this [.tapped]])),
    .ability (
      .activated
        [.tapSymbol]
        (.playerSelectAction
          (.controller .this)
          (.range 1 1)
          [
            .addMana (.controller .this) [.mono .red],
            .addMana (.controller .this) [.mono .white]])),
    .ability (
      .activatedIf
        (.timeToCastSorcery (.controller .this))
        [
          .mana [.generic 2, .mono .red, .mono .white],
          .tapSymbol,
          .sacrifice .this]
        (.putCounter
          (.target
            1
            (.intersection [
              .permanent,
              .cardType .creature,
              .subtype .dwarf,
              .controlled (.controller .this)]))
          .plusOnePlusOne
          2))
]

/-- Gatherer Oracle text for Lake-town. -/
def lakeTownOracle : String :=
  "This land enters tapped.\n{T}: Add {W} or {U}.\n{2}{W}{U}, {T}, Sacrifice this land: Put two +1/+1 counters on target Human you control. Activate only as a sorcery."

def lakeTownDefinition : TraditionalCardDefinition := .card <|
  [
    .name "Lake-town",
    .type .land
  ] ++ (parseOracleParts (name := "Lake-town") lakeTownOracle).get!

def lakeTown : CardDef :=
  lakeTownDefinition.toCardDef
    (oracleText := lakeTownOracle)

#guard lakeTownDefinition == .card [
    .name "Lake-town",
    .type .land,
    .ability (
      .static
        (.replace
          (.enter .this)
          [.putOntoBattlefieldInState .this [.tapped]])),
    .ability (
      .activated
        [.tapSymbol]
        (.playerSelectAction
          (.controller .this)
          (.range 1 1)
          [
            .addMana (.controller .this) [.mono .white],
            .addMana (.controller .this) [.mono .blue]])),
    .ability (
      .activatedIf
        (.timeToCastSorcery (.controller .this))
        [
          .mana [.generic 2, .mono .white, .mono .blue],
          .tapSymbol,
          .sacrifice .this]
        (.putCounter
          (.target
            1
            (.intersection [
              .permanent,
              .cardType .creature,
              .subtype .human,
              .controlled (.controller .this)]))
          .plusOnePlusOne
          2))
]

/-- Gatherer Oracle text for Goblin-town. -/
def goblinTownOracle : String :=
  "This land enters tapped.\n{T}: Add {B} or {R}.\n{2}{B}{R}, {T}, Sacrifice this land: Put two +1/+1 counters on target Goblin or Orc you control. Activate only as a sorcery."

def goblinTownDefinition : TraditionalCardDefinition := .card <|
  [
    .name "Goblin-town",
    .type .land
  ] ++ (parseOracleParts (name := "Goblin-town") goblinTownOracle).get!

def goblinTown : CardDef :=
  goblinTownDefinition.toCardDef
    (oracleText := goblinTownOracle)

#guard goblinTownDefinition == .card [
    .name "Goblin-town",
    .type .land,
    .ability (
      .static
        (.replace
          (.enter .this)
          [.putOntoBattlefieldInState .this [.tapped]])),
    .ability (
      .activated
        [.tapSymbol]
        (.playerSelectAction
          (.controller .this)
          (.range 1 1)
          [
            .addMana (.controller .this) [.mono .black],
            .addMana (.controller .this) [.mono .red]])),
    .ability (
      .activatedIf
        (.timeToCastSorcery (.controller .this))
        [
          .mana [.generic 2, .mono .black, .mono .red],
          .tapSymbol,
          .sacrifice .this]
        (.putCounter
          (.target
            1
            (.intersection [
              .permanent,
              .cardType .creature,
              .union [.subtype .goblin, .subtype .orc],
              .controlled (.controller .this)]))
          .plusOnePlusOne
          2))
]

/-- Gatherer Oracle text for Mirkwood. -/
def mirkwoodOracle : String :=
  "This land enters tapped.\n{T}: Add {B} or {G}.\n{2}{B}{G}, {T}, Sacrifice this land: Put two +1/+1 counters on target Bear, Spider, or Wolf you control. Activate only as a sorcery."

def mirkwoodDefinition : TraditionalCardDefinition := .card <|
  [
    .name "Mirkwood",
    .type .land
  ] ++ (parseOracleParts (name := "Mirkwood") mirkwoodOracle).get!

def mirkwood : CardDef :=
  mirkwoodDefinition.toCardDef
    (oracleText := mirkwoodOracle)

#guard mirkwoodDefinition == .card [
    .name "Mirkwood",
    .type .land,
    .ability (
      .static
        (.replace
          (.enter .this)
          [.putOntoBattlefieldInState .this [.tapped]])),
    .ability (
      .activated
        [.tapSymbol]
        (.playerSelectAction
          (.controller .this)
          (.range 1 1)
          [
            .addMana (.controller .this) [.mono .black],
            .addMana (.controller .this) [.mono .green]])),
    .ability (
      .activatedIf
        (.timeToCastSorcery (.controller .this))
        [
          .mana [.generic 2, .mono .black, .mono .green],
          .tapSymbol,
          .sacrifice .this]
        (.putCounter
          (.target
            1
            (.intersection [
              .permanent,
              .cardType .creature,
              .union [.subtype .bear, .subtype .spider, .subtype .wolf],
              .controlled (.controller .this)]))
          .plusOnePlusOne
          2))
]

/-- Gatherer Oracle text for Hobbit Hole. -/
def hobbitHoleOracle : String :=
  "{T}, Sacrifice this land: Search your library for a basic land card, put it onto the battlefield tapped, then shuffle.\nHalflingcycling {4} ({4}, Discard this card: Search your library for a Halfling card, reveal it, put it into your hand, then shuffle.)"

def hobbitHoleDefinition : TraditionalCardDefinition := .card <|
  [
    .name "Hobbit Hole",
    .type .land
  ] ++ (parseOracleParts (name := "Hobbit Hole") hobbitHoleOracle).get!

def hobbitHole : CardDef :=
  hobbitHoleDefinition.toCardDef
    (oracleText := hobbitHoleOracle)

#guard hobbitHoleDefinition == .card [
    .name "Hobbit Hole",
    .type .land,
    .ability (
      .activated
        [.tapSymbol, .sacrifice .this]
        (.searchLibraryThenShuffle
          (.controller .this)
          [
            .putOntoBattlefieldInState
              (.selected
                (.controller .this)
                (.range 1 1)
                (.intersection [
                  .inLibrary,
                  .cardType .land,
                  .supertype .basic]))
              [.tapped]])),
    .ability (.keywordWithCost (.typecycling [] [] [.halfling]) [.mana [.generic 4]])
]

/-- Gatherer Oracle text for Nighthowl Pursuer. -/
def nighthowlPursuerOracle : String :=
  "Menace (This creature can't be blocked except by two or more creatures.)\nFerocious — Whenever this creature attacks while you control a creature with power 4 or greater, this creature gets +2/+2 until end of turn."

def nighthowlPursuerDefinition : TraditionalCardDefinition := .card <|
  [
    .name "Nighthowl Pursuer",
    .manaCost [.mono .black],
    .type .creature,
    .subtype .wolf,
    .power 1,
    .toughness 1
  ] ++ (parseOracleParts (name := "Nighthowl Pursuer") nighthowlPursuerOracle).get!

def nighthowlPursuer : CardDef :=
  nighthowlPursuerDefinition.toCardDef
    (oracleText := nighthowlPursuerOracle)

#guard nighthowlPursuerDefinition == .card [
    .name "Nighthowl Pursuer",
    .manaCost [.mono .black],
    .type .creature,
    .subtype .wolf,
    .power 1,
    .toughness 1,
    .ability (.keyword .menace),
    .ability (
      .triggeredWhile
        (.attack .this .all)
        (.any
          (.intersection [
            .permanent,
            .cardType .creature,
            .controlled (.controller .this),
            .powerAtLeast (Value.int 4)]))
        (.continuous [.addPower (.source .this) (Value.int 2),
                      .addToughness (.source .this) (Value.int 2)] .endOfTurn))
]

/-- Gatherer Oracle text for Wargling. -/
def warglingOracle : String :=
  "Ferocious — Whenever this creature attacks while you control a creature with power 4 or greater, until end of turn, this creature gets +1/+0 and creatures you control gain trample."

def warglingDefinition : TraditionalCardDefinition := .card <|
  [
    .name "Wargling",
    .manaCost [.generic 1, .mono .green],
    .type .creature,
    .subtype .wolf,
    .power 2,
    .toughness 2
  ] ++ (parseOracleParts (name := "Wargling") warglingOracle).get!

def wargling : CardDef :=
  warglingDefinition.toCardDef
    (oracleText := warglingOracle)

#guard warglingDefinition == .card [
  .name "Wargling",
  .manaCost [.generic 1, .mono .green],
  .type .creature,
  .subtype .wolf,
  .power 2,
  .toughness 2,
  .ability (
    .triggeredWhile
      (.attack .this .all)
      (.any
        (.intersection [
          .permanent,
          .cardType .creature,
          .controlled (.controller .this),
          .powerAtLeast (Value.int 4)]))
      (.continuous
        [
          .addPower (.source .this) (Value.int 1),
          .gainAbility
            (.intersection [
              .permanent,
              .cardType .creature,
              .controlled (.controller .this)])
            (.keyword .trample)]
        .endOfTurn))
]

/-- Gatherer Oracle text for Wilderland Scrounger. -/
def wilderlandScroungerOracle : String :=
  "Ferocious — Whenever this creature attacks while you control a creature with power 4 or greater, put a +1/+1 counter on each creature you control."

def wilderlandScroungerDefinition : TraditionalCardDefinition := .card <|
  [
    .name "Wilderland Scrounger",
    .manaCost [.generic 4, .mono .green],
    .type .creature,
    .subtype .wolf,
    .power 3,
    .toughness 6
  ] ++ (parseOracleParts (name := "Wilderland Scrounger") wilderlandScroungerOracle).get!

def wilderlandScrounger : CardDef :=
  wilderlandScroungerDefinition.toCardDef
    (oracleText := wilderlandScroungerOracle)

#guard wilderlandScroungerDefinition == .card [
  .name "Wilderland Scrounger",
  .manaCost [.generic 4, .mono .green],
  .type .creature,
  .subtype .wolf,
  .power 3,
  .toughness 6,
  .ability (
    .triggeredWhile
      (.attack .this .all)
      (.any
        (.intersection [
          .permanent,
          .cardType .creature,
          .controlled (.controller .this),
          .powerAtLeast (Value.int 4)]))
      (.putCounter
        (.intersection [
          .permanent,
          .cardType .creature,
          .controlled (.controller .this)])
        .plusOnePlusOne
        1))
]

/-- Gatherer Oracle text for Nasty Little Rabbit. -/
def nastyLittleRabbitOracle : String :=
  "Ferocious — At the beginning of combat on your turn, if you control a creature with power 4 or greater, put a +1/+1 counter on this creature."

def nastyLittleRabbitDefinition : TraditionalCardDefinition := .card <|
  [
    .name "Nasty Little Rabbit",
    .manaCost [.mono .green],
    .type .creature,
    .subtype .rabbit,
    .power 1,
    .toughness 2
  ] ++ (parseOracleParts (name := "Nasty Little Rabbit") nastyLittleRabbitOracle).get!

def nastyLittleRabbit : CardDef :=
  nastyLittleRabbitDefinition.toCardDef
    (oracleText := nastyLittleRabbitOracle)

#guard nastyLittleRabbitDefinition == .card [
  .name "Nasty Little Rabbit",
  .manaCost [.mono .green],
  .type .creature,
  .subtype .rabbit,
  .power 1,
  .toughness 2,
  .ability (
    .triggered
      (.combatStart (.controller .this))
      (.if
        (.any
          (.intersection [
            .permanent,
            .cardType .creature,
            .controlled (.controller .this),
            .powerAtLeast (Value.int 4)]))
        [.putCounter (.source .this) .plusOnePlusOne 1]))
]

/-- Gatherer Oracle text for The Chief Warg. -/
def theChiefWargOracle : String :=
  "Menace (This creature can't be blocked except by two or more creatures.)\nFerocious — Whenever you attack while you control a creature with power 4 or greater, you draw a card and lose 1 life."

def theChiefWargDefinition : TraditionalCardDefinition := .card <|
  [
    .name "The Chief Warg",
    .manaCost [.generic 2, .mono .black, .mono .green],
    .type .creature,
    .supertype .legendary,
    .subtype .wolf,
    .power 3,
    .toughness 3
  ] ++ (parseOracleParts (name := "The Chief Warg") theChiefWargOracle).get!

def theChiefWarg : CardDef :=
  theChiefWargDefinition.toCardDef
    (oracleText := theChiefWargOracle)

#guard theChiefWargDefinition == .card [
  .name "The Chief Warg",
  .manaCost [.generic 2, .mono .black, .mono .green],
  .type .creature,
  .supertype .legendary,
  .subtype .wolf,
  .power 3,
  .toughness 3,
  .ability (.keyword .menace),
  .ability (
    .triggeredWhile
      (.attackSimultaneously
        (.intersection [
          .permanent,
          .cardType .creature,
          .controlled (.controller .this)])
        .all
        [])
      (.any
        (.intersection [
          .permanent,
          .cardType .creature,
          .controlled (.controller .this),
          .powerAtLeast (Value.int 4)]))
      (.sequence [
        .draw (.controller .this) 1,
        .loseLife (.controller .this) 1]))
]

/-- Gatherer Oracle text for Thorin's Last Stand. -/
def thorinsLastStandOracle : String :=
  "Choose one —\n• Creatures you control get +2/+1 until end of turn.\n• Destroy target artifact or enchantment. You gain 2 life."

def thorinsLastStandDefinition : TraditionalCardDefinition := .card <|
  [
    .name "Thorin's Last Stand",
    .manaCost [.generic 2, .mono .white, .mono .white],
    .type .instant
  ] ++ (parseOracleParts (name := "Thorin's Last Stand") thorinsLastStandOracle).get!

def thorinsLastStand : CardDef :=
  thorinsLastStandDefinition.toCardDef
    (oracleText := thorinsLastStandOracle)

#guard thorinsLastStandDefinition == .card [
  .name "Thorin's Last Stand",
  .manaCost [.generic 2, .mono .white, .mono .white],
  .type .instant,
  .actions [
    .chooseUniqueModes (.range 1 1) [
      .continuous
        [.addPower
          (.intersection [
            .permanent,
            .cardType .creature,
            .controlled (.controller .this)]) (Value.int 2),
         .addToughness
          (.intersection [
            .permanent,
            .cardType .creature,
            .controlled (.controller .this)]) (Value.int 1)]
        .endOfTurn,
      .sequence [
        .destroy
          (.target
            1
            (.intersection [
              .permanent,
              .union [.cardType .artifact, .cardType .enchantment]])),
        .gainLife (.controller .this) 2]]]
]

/-- Gatherer Oracle text for Stone by Sunlight. -/
def stoneBySunlightOracle : String :=
  "Choose one —\n• Destroy target creature with power 4 or greater.\n• Until end of turn, target creature becomes an artifact in addition to its other types and gains indestructible. (Damage and effects that say \"destroy\" don't destroy it.)"

def stoneBySunlightDefinition : TraditionalCardDefinition := .card <|
  [
    .name "Stone by Sunlight",
    .manaCost [.generic 1, .mono .white],
    .type .instant
  ] ++ (parseOracleParts (name := "Stone by Sunlight") stoneBySunlightOracle).get!

def stoneBySunlight : CardDef :=
  stoneBySunlightDefinition.toCardDef
    (oracleText := stoneBySunlightOracle)

#guard stoneBySunlightDefinition == .card [
  .name "Stone by Sunlight",
  .manaCost [.generic 1, .mono .white],
  .type .instant,
  .actions [
    .chooseUniqueModes (.range 1 1) [
      .destroy
        (.target
          1
          (.intersection [
            .permanent,
            .cardType .creature,
            .powerAtLeast (Value.int 4)])),
      .continuous
        [
          .gainType
            (.target 2 (.intersection [.permanent, .cardType .creature]))
            .artifact,
          .gainAbility (.targetReference 2) (.keyword .indestructible)]
        .endOfTurn]]
]

/-- Gatherer Oracle text for Duskwatch Hunter. -/
def duskwatchHunterOracle : String :=
  "This creature can't be blocked by tokens.\nWhen this creature enters, put a +1/+1 counter on target creature."

def duskwatchHunterDefinition : TraditionalCardDefinition := .card <|
  [
    .name "Duskwatch Hunter",
    .manaCost [.generic 2, .hybrid .black .green],
    .type .creature,
    .subtype .wolf,
    .power 3,
    .toughness 1
  ] ++ (parseOracleParts (name := "Duskwatch Hunter") duskwatchHunterOracle).get!

def duskwatchHunter : CardDef :=
  duskwatchHunterDefinition.toCardDef
    (oracleText := duskwatchHunterOracle)

#guard duskwatchHunterDefinition == .card [
  .name "Duskwatch Hunter",
  .manaCost [.generic 2, .hybrid .black .green],
  .type .creature,
  .subtype .wolf,
  .power 3,
  .toughness 1,
  .ability (.static (.forbid (.block .token .this))),
  .ability (
    .triggered
      (.enter .this)
      (.putCounter
        (.target 1 (.intersection [.permanent, .cardType .creature]))
        .plusOnePlusOne
        1))
]

/-- Gatherer Oracle text for Patient Instructor. -/
def patientInstructorOracle : String :=
  "Vigilance\nWhen this creature enters, recruit. (Draw a card, then discard a card. If you discarded a nonland card, create a 1/1 white Human Soldier creature token.)"

def patientInstructorDefinition : TraditionalCardDefinition := .card <|
  [
    .name "Patient Instructor",
    .manaCost [.generic 2, .hybrid .white .blue],
    .type .creature,
    .subtype .human,
    .subtype .citizen,
    .power 2,
    .toughness 2
  ] ++ (parseOracleParts (name := "Patient Instructor") patientInstructorOracle).get!

def patientInstructor : CardDef :=
  patientInstructorDefinition.toCardDef
    (oracleText := patientInstructorOracle)

#guard patientInstructorDefinition == .card [
  .name "Patient Instructor",
  .manaCost [.generic 2, .hybrid .white .blue],
  .type .creature,
  .subtype .human,
  .subtype .citizen,
  .power 2,
  .toughness 2,
  .ability (.keyword .vigilance),
  .ability (.triggered (.enter .this) (.keyword (.controller .this) .recruit))
]

/-- Gatherer Oracle text for Long Lake Nuisance. -/
def longLakeNuisanceOracle : String :=
  "Flying\nWhen this creature enters, recruit. (Draw a card, then discard a card. If you discarded a nonland card, create a 1/1 white Human Soldier creature token.)"

def longLakeNuisanceDefinition : TraditionalCardDefinition := .card <|
  [
    .name "Long Lake Nuisance",
    .manaCost [.generic 3, .mono .blue],
    .type .creature,
    .subtype .bird,
    .power 3,
    .toughness 1
  ] ++ (parseOracleParts (name := "Long Lake Nuisance") longLakeNuisanceOracle).get!

def longLakeNuisance : CardDef :=
  longLakeNuisanceDefinition.toCardDef
    (oracleText := longLakeNuisanceOracle)

#guard longLakeNuisanceDefinition == .card [
  .name "Long Lake Nuisance",
  .manaCost [.generic 3, .mono .blue],
  .type .creature,
  .subtype .bird,
  .power 3,
  .toughness 1,
  .ability (.keyword .flying),
  .ability (.triggered (.enter .this) (.keyword (.controller .this) .recruit))
]

/-- Gatherer Oracle text for Lake-town Lookout. -/
def laketownLookoutOracle : String :=
  "When this creature dies, recruit. (Draw a card, then discard a card. If you discarded a nonland card, create a 1/1 white Human Soldier creature token.)"

def laketownLookoutDefinition : TraditionalCardDefinition := .card <|
  [
    .name "Lake-town Lookout",
    .manaCost [.mono .white],
    .type .creature,
    .subtype .human,
    .subtype .scout,
    .power 1,
    .toughness 1
  ] ++ (parseOracleParts (name := "Lake-town Lookout") laketownLookoutOracle).get!

def laketownLookout : CardDef :=
  laketownLookoutDefinition.toCardDef
    (oracleText := laketownLookoutOracle)

#guard laketownLookoutDefinition == .card [
  .name "Lake-town Lookout",
  .manaCost [.mono .white],
  .type .creature,
  .subtype .human,
  .subtype .scout,
  .power 1,
  .toughness 1,
  .ability (.triggered (.die .this) (.keyword (.controller .this) .recruit))
]

#guard laketownLookout.triggeredAbilities == #[.onDiesRecruit]

/-- Gatherer Oracle text for Giant's Boulder. -/
def giantsBoulderOracle : String :=
  "When this artifact enters, scry 2. (Look at the top two cards of your library, then put any number of them on the bottom and the rest on top in any order.)\n{1}, {T}: Add one mana of any color.\n{7}, {T}, Sacrifice this artifact: Destroy target permanent."

def giantsBoulderDefinition : TraditionalCardDefinition := .card <|
  [
    .name "Giant's Boulder",
    .manaCost [.generic 1],
    .type .artifact
  ] ++ (parseOracleParts (name := "Giant's Boulder") giantsBoulderOracle).get!

def giantsBoulder : CardDef :=
  giantsBoulderDefinition.toCardDef
    (oracleText := giantsBoulderOracle)

#guard giantsBoulderDefinition == .card [
  .name "Giant's Boulder",
  .manaCost [.generic 1],
  .type .artifact,
  .ability (.triggered (.enter .this) (.scry (.controller .this) 2)),
  .ability (
    .activated
      [.mana [.generic 1], .tapSymbol]
      (.addManaOfOneColor
        (.controller .this)
        ManaSymbol.anyColor
        1)),
  .ability (
    .activated
      [.mana [.generic 7], .tapSymbol, .sacrifice .this]
      (.destroy (.target 1 .permanent)))
]

#guard giantsBoulder.triggeredAbilities == #[.onEnterScry 2]
#guard giantsBoulder.activatedAbilities.size == 2
#guard giantsBoulder.activatedAbilities[0]!.effect == Effect.addAnyColor
#guard giantsBoulder.activatedAbilities[0]!.cost.tap
#guard giantsBoulder.activatedAbilities[0]!.cost.mana == ManaCost.ofGeneric 1
#guard giantsBoulder.activatedAbilities[1]!.effect == Effect.destroyTargetPermanent
#guard giantsBoulder.activatedAbilities[1]!.cost.tap
#guard giantsBoulder.activatedAbilities[1]!.cost.sacrificeSource
#guard giantsBoulder.activatedAbilities[1]!.cost.mana == ManaCost.ofGeneric 7

/-- Gatherer Oracle text for Long-Bodied Grey Dog. -/
def longBodiedGreyDogOracle : String :=
  "Flash\nReach\nWhen this creature enters, create a tapped Treasure token. (It's an artifact with \"{T}, Sacrifice this token: Add one mana of any color.\")"

def longBodiedGreyDogDefinition : TraditionalCardDefinition := .card <|
  [
    .name "Long-Bodied Grey Dog",
    .manaCost [.generic 3],
    .type .creature,
    .subtype .dog,
    .power 2,
    .toughness 2
  ] ++ (parseOracleParts (name := "Long-Bodied Grey Dog") longBodiedGreyDogOracle).get!

def longBodiedGreyDog : CardDef :=
  longBodiedGreyDogDefinition.toCardDef
    (oracleText := longBodiedGreyDogOracle)

#guard longBodiedGreyDogDefinition == .card [
  .name "Long-Bodied Grey Dog",
  .manaCost [.generic 3],
  .type .creature,
  .subtype .dog,
  .power 2,
  .toughness 2,
  .ability (.keyword .flash),
  .ability (.keyword .reach),
  .ability (
    .triggered
      (.enter .this)
      (.createTokens (.controller .this) 1 PredefinedToken.treasureToken
        [.tapped]))
]

#guard longBodiedGreyDog.keywords.flash && longBodiedGreyDog.keywords.reach
#guard longBodiedGreyDog.triggeredAbilities ==
  #[.onEnterCreateTokens .treasure 1 true]

/-- Gatherer Oracle text for Dori, Bearer of Friends. -/
def doriBearerOfFriendsOracle : String :=
  "Trample\nWhen Dori enters, create a Treasure token. (It's an artifact with \"{T}, Sacrifice this token: Add one mana of any color.\")"

def doriBearerOfFriendsDefinition : TraditionalCardDefinition := .card <|
  [
    .name "Dori, Bearer of Friends",
    .manaCost [.generic 2, .mono .red],
    .type .creature,
    .supertype .legendary,
    .subtype .dwarf,
    .subtype .warrior,
    .power 3,
    .toughness 2
  ] ++ (parseOracleParts (name := "Dori, Bearer of Friends") doriBearerOfFriendsOracle).get!

def doriBearerOfFriends : CardDef :=
  doriBearerOfFriendsDefinition.toCardDef
    (oracleText := doriBearerOfFriendsOracle)

#guard doriBearerOfFriendsDefinition == .card [
  .name "Dori, Bearer of Friends",
  .manaCost [.generic 2, .mono .red],
  .type .creature,
  .supertype .legendary,
  .subtype .dwarf,
  .subtype .warrior,
  .power 3,
  .toughness 2,
  .ability (.keyword .trample),
  .ability (
    .triggered
      (.enter .this)
      (.createTokens (.controller .this) 1 PredefinedToken.treasureToken))
]

#guard doriBearerOfFriends.keywords.trample
#guard doriBearerOfFriends.triggeredAbilities == #[.onEnterCreateTokens .treasure 1]

/-- Gatherer Oracle text for Esgaroth Garrison. -/
def esgarothGarrisonOracle : String :=
  "Esgaroth Garrison's power is equal to the number of creatures you control.\nWhen this creature enters, recruit. (Draw a card, then discard a card. If you discarded a nonland card, create a 1/1 white Human Soldier creature token.)"

def esgarothGarrisonDefinition : TraditionalCardDefinition := .card <|
  [
    .name "Esgaroth Garrison",
    .manaCost [.generic 4, .mono .white],
    .type .creature,
    .subtype .human,
    .subtype .soldier,
    .toughness 5
  ] ++ (parseOracleParts (name := "Esgaroth Garrison") esgarothGarrisonOracle).get!

def esgarothGarrison : CardDef :=
  esgarothGarrisonDefinition.toCardDef
    (oracleText := esgarothGarrisonOracle)

#guard esgarothGarrisonDefinition == .card [
  .name "Esgaroth Garrison",
  .manaCost [.generic 4, .mono .white],
  .type .creature,
  .subtype .human,
  .subtype .soldier,
  .toughness 5,
  .ability (
    .static
      (.setPower
        .this
        (.count
          (.intersection [
            .permanent,
            .cardType .creature,
            .controlled (.controller .this)])))),
  .ability (.triggered (.enter .this) (.keyword (.controller .this) .recruit))
]

#guard esgarothGarrison.power == none
#guard esgarothGarrison.toughness == some 5
#guard esgarothGarrison.staticAbilities == #[.powerEqualCreaturesYouControl]
#guard esgarothGarrison.triggeredAbilities == #[.onEnterRecruit]

/-- Gatherer Oracle text for Gundabad Opportunist. -/
def gundabadOpportunistOracle : String :=
  "When this creature enters, exile the top card of your library. Until the end of your next turn, you may play that card."

def gundabadOpportunistDefinition : TraditionalCardDefinition := .card <|
  [
    .name "Gundabad Opportunist",
    .manaCost [.generic 3, .mono .red],
    .type .creature,
    .subtype .goblin,
    .subtype .rogue,
    .power 4,
    .toughness 2
  ] ++ (parseOracleParts (name := "Gundabad Opportunist") gundabadOpportunistOracle).get!

def gundabadOpportunist : CardDef :=
  gundabadOpportunistDefinition.toCardDef
    (oracleText := gundabadOpportunistOracle)

#guard gundabadOpportunistDefinition == .card [
  .name "Gundabad Opportunist",
  .manaCost [.generic 3, .mono .red],
  .type .creature,
  .subtype .goblin,
  .subtype .rogue,
  .power 4,
  .toughness 2,
  .ability (
    .triggered
      (.enter .this)
      (.sequence [
        .actionId 1 (.exile (.topOfLibrary (.controller .this))),
        .continuous
          [.canPlay (.controller .this) (.wasCreatedByAction 1)]
          (.sequence [.turnStart, .endOfPlayerTurn (.controller .this)])]))
]

/-- Gatherer Oracle text for Gigantic Big Bear. -/
def giganticBigBearOracle : String :=
  "This spell can't be countered.\nHexproof, haste"

def giganticBigBearDefinition : TraditionalCardDefinition := .card <|
  [
    .name "Gigantic Big Bear",
    .manaCost [.generic 5, .mono .green, .mono .green],
    .type .creature,
    .subtype .bear,
    .power 10,
    .toughness 7
  ] ++ (parseOracleParts (name := "Gigantic Big Bear") giganticBigBearOracle).get!

def giganticBigBear : CardDef :=
  giganticBigBearDefinition.toCardDef
    (oracleText := giganticBigBearOracle)

#guard giganticBigBearDefinition == .card [
  .name "Gigantic Big Bear",
  .manaCost [.generic 5, .mono .green, .mono .green],
  .type .creature,
  .subtype .bear,
  .power 10,
  .toughness 7,
  .ability (.stackStatic (.forbid (.counter .this))),
  .ability (.keyword .hexproof),
  .ability (.keyword .haste)
]

#guard giganticBigBear.cantBeCountered
#guard giganticBigBear.keywords.hexproof && giganticBigBear.keywords.haste
#guard giganticBigBear.power == some 10
#guard giganticBigBear.toughness == some 7

/-- Gatherer Oracle text for Bothersome Noisemaker. -/
def bothersomeNoisemakerOracle : String :=
  "Whenever you cast a noncreature spell, amass Goblins 1. (Put a +1/+1 counter on an Army you control. It's also a Goblin. If you don't control an Army, create a 0/0 black Goblin Army creature token first.)"

def bothersomeNoisemakerDefinition : TraditionalCardDefinition := .card <|
  [
    .name "Bothersome Noisemaker",
    .manaCost [.generic 1, .mono .red],
    .type .creature,
    .subtype .goblin,
    .subtype .bard,
    .power 2,
    .toughness 2
  ] ++ (parseOracleParts (name := "Bothersome Noisemaker") bothersomeNoisemakerOracle).get!

def bothersomeNoisemaker : CardDef :=
  bothersomeNoisemakerDefinition.toCardDef
    (oracleText := bothersomeNoisemakerOracle)

#guard bothersomeNoisemakerDefinition == .card [
  .name "Bothersome Noisemaker",
  .manaCost [.generic 1, .mono .red],
  .type .creature,
  .subtype .goblin,
  .subtype .bard,
  .power 2,
  .toughness 2,
  .ability (
    .triggered
      (.castSpell
        (.intersection [
          .spell,
          .not (.cardType .creature),
          .controlled (.controller .this)]))
      (.keyword (.controller .this) (.amass .goblin (.nat 1))))
]

#guard bothersomeNoisemaker.triggeredAbilities == #[.onCastNoncreatureAmassGoblins 1]

/-- Gatherer Oracle text for Fearsome Goblin Pair. -/
def fearsomeGoblinPairOracle : String :=
  "When this creature dies, amass Goblins 4. (Put four +1/+1 counters on an Army you control. It's also a Goblin. If you don't control an Army, create a 0/0 black Goblin Army creature token first.)"

def fearsomeGoblinPairDefinition : TraditionalCardDefinition := .card <|
  [
    .name "Fearsome Goblin Pair",
    .manaCost [.generic 2, .hybrid .black .red],
    .type .creature,
    .subtype .goblin,
    .subtype .soldier,
    .power 1,
    .toughness 1
  ] ++ (parseOracleParts (name := "Fearsome Goblin Pair") fearsomeGoblinPairOracle).get!

def fearsomeGoblinPair : CardDef :=
  fearsomeGoblinPairDefinition.toCardDef
    (oracleText := fearsomeGoblinPairOracle)

#guard fearsomeGoblinPairDefinition == .card [
  .name "Fearsome Goblin Pair",
  .manaCost [.generic 2, .hybrid .black .red],
  .type .creature,
  .subtype .goblin,
  .subtype .soldier,
  .power 1,
  .toughness 1,
  .ability (
    .triggered
      (.die .this)
      (.keyword (.controller .this) (.amass .goblin (.nat 4))))
]

#guard fearsomeGoblinPair.triggeredAbilities == #[.onDiesAmassGoblins 4]

/-- Gatherer Oracle text for Goblin-town Flunkies. -/
def goblinTownFlunkiesOracle : String :=
  "Haste\nWhen this creature enters, amass Goblins 1. (Put a +1/+1 counter on an Army you control. It's also a Goblin. If you don't control an Army, create a 0/0 black Goblin Army creature token first.)"

def goblinTownFlunkiesDefinition : TraditionalCardDefinition := .card <|
  [
    .name "Goblin-town Flunkies",
    .manaCost [.generic 1, .mono .red],
    .type .creature,
    .subtype .goblin,
    .subtype .soldier,
    .power 1,
    .toughness 1
  ] ++ (parseOracleParts (name := "Goblin-town Flunkies") goblinTownFlunkiesOracle).get!

def goblinTownFlunkies : CardDef :=
  goblinTownFlunkiesDefinition.toCardDef
    (oracleText := goblinTownFlunkiesOracle)

#guard goblinTownFlunkiesDefinition == .card [
  .name "Goblin-town Flunkies",
  .manaCost [.generic 1, .mono .red],
  .type .creature,
  .subtype .goblin,
  .subtype .soldier,
  .power 1,
  .toughness 1,
  .ability (.keyword .haste),
  .ability (
    .triggered
      (.enter .this)
      (.keyword (.controller .this) (.amass .goblin (.nat 1))))
]

#guard goblinTownFlunkies.keywords.haste
#guard goblinTownFlunkies.triggeredAbilities == #[.onEnterAmassGoblins 1]

/-- Gatherer Oracle text for Misty Mountains Raider. -/
def mistyMountainsRaiderOracle : String :=
  "Whenever you attack, amass Goblins 2. (Put two +1/+1 counters on an Army you control. It's also a Goblin. If you don't control an Army, create a 0/0 black Goblin Army creature token first.)"

def mistyMountainsRaiderDefinition : TraditionalCardDefinition := .card <|
  [
    .name "Misty Mountains Raider",
    .manaCost [.generic 4, .mono .red],
    .type .creature,
    .subtype .goblin,
    .subtype .soldier,
    .power 4,
    .toughness 4
  ] ++ (parseOracleParts (name := "Misty Mountains Raider") mistyMountainsRaiderOracle).get!

def mistyMountainsRaider : CardDef :=
  mistyMountainsRaiderDefinition.toCardDef
    (oracleText := mistyMountainsRaiderOracle)

#guard mistyMountainsRaiderDefinition == .card [
  .name "Misty Mountains Raider",
  .manaCost [.generic 4, .mono .red],
  .type .creature,
  .subtype .goblin,
  .subtype .soldier,
  .power 4,
  .toughness 4,
  .ability (
    .triggered
      (.attackSimultaneously
        (.intersection [
          .permanent,
          .cardType .creature,
          .controlled (.controller .this)])
        .all
        [])
      (.keyword (.controller .this) (.amass .goblin (.nat 2))))
]

#guard mistyMountainsRaider.triggeredAbilities == #[.onYouAttackAmassGoblins 2]

/-- Gatherer Oracle text for Bard's Company. -/
def bardsCompanyOracle : String :=
  "You may cast this spell as though it had flash if you control a Human.\nOther creatures you control get +1/+1.\nWhenever this creature enters or attacks, recruit. (Draw a card, then discard a card. If you discarded a nonland card, create a 1/1 white Human Soldier creature token.)"

def bardsCompanyDefinition : TraditionalCardDefinition := .card <|
  [
    .name "Bard's Company",
    .manaCost [.generic 2, .mono .white, .mono .blue],
    .type .creature,
    .subtype .human,
    .subtype .citizen,
    .power 2,
    .toughness 3
  ] ++ (parseOracleParts (name := "Bard's Company") bardsCompanyOracle).get!

def bardsCompany : CardDef :=
  bardsCompanyDefinition.toCardDef
    (oracleText := bardsCompanyOracle)

#guard bardsCompanyDefinition == .card [
  .name "Bard's Company",
  .manaCost [.generic 2, .mono .white, .mono .blue],
  .type .creature,
  .subtype .human,
  .subtype .citizen,
  .power 2,
  .toughness 3,
  .ability (.everywhereStatic (
    .canBeCastAsThoughWithFlashIf
      .this
      (.any (.intersection [
        .permanent, .subtype .human, .controlled .caster])))),
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
      .controlled (.controller .this)]) (Value.int 1))),
  .ability (
    .triggered
      (.or (.enter .this) (.attack .this .all))
      (.keyword (.controller .this) .recruit))
]

#guard bardsCompany.flashIfYouControlSubtype == some "Human"
#guard !bardsCompany.keywords.flash
#guard bardsCompany.staticAbilities == #[.otherCreaturesGet #[] 1 1]
#guard bardsCompany.triggeredAbilities == #[.onEnterOrAttackRecruit]

/-- Gatherer Oracle text for Rage into the Valley. -/
def rageIntoTheValleyOracle : String :=
  "You draw a card and lose 1 life.\nAmass Goblins 2. (Put two +1/+1 counters on an Army you control. It's also a Goblin. If you don't control an Army, create a 0/0 black Goblin Army creature token first.)"

def rageIntoTheValleyDefinition : TraditionalCardDefinition := .card <|
  [
    .name "Rage into the Valley",
    .manaCost [.generic 2, .mono .black],
    .type .sorcery
  ] ++ (parseOracleParts (name := "Rage into the Valley") rageIntoTheValleyOracle).get!

def rageIntoTheValley : CardDef :=
  rageIntoTheValleyDefinition.toCardDef
    (oracleText := rageIntoTheValleyOracle)

#guard rageIntoTheValleyDefinition == .card [
  .name "Rage into the Valley",
  .manaCost [.generic 2, .mono .black],
  .type .sorcery,
  .actions [
    .draw (.controller .this) 1,
    .loseLife (.controller .this) 1,
    .keyword (.controller .this) (.amass .goblin (.nat 2))]]

#guard rageIntoTheValley.spellEffect == some (Effect.drawLoseLifeThenAmass 2)
#guard rageIntoTheValley.oracleText == rageIntoTheValleyOracle

/-- Gatherer Oracle text for Gathering of Darkness. -/
def gatheringOfDarknessOracle : String :=
  "Return up to one target creature card from your graveyard to your hand.\nAmass Goblins 3. (Put three +1/+1 counters on an Army you control. It's also a Goblin. If you don't control an Army, create a 0/0 black Goblin Army creature token first.)"

def gatheringOfDarknessDefinition : TraditionalCardDefinition := .card <|
  [
    .name "Gathering of Darkness",
    .manaCost [.generic 3, .mono .black],
    .type .sorcery
  ] ++ (parseOracleParts (name := "Gathering of Darkness") gatheringOfDarknessOracle).get!

def gatheringOfDarkness : CardDef :=
  gatheringOfDarknessDefinition.toCardDef
    (oracleText := gatheringOfDarknessOracle)

#guard gatheringOfDarknessDefinition == .card [
  .name "Gathering of Darkness",
  .manaCost [.generic 3, .mono .black],
  .type .sorcery,
  .actions [
    .returnToHand
      (.targets
        1
        (.range 0 1)
        (.intersection [
          .inGraveyard,
          .cardType .creature,
          .owner (.controller .this)])),
    .keyword (.controller .this) (.amass .goblin (.nat 3))]]

#guard gatheringOfDarkness.spellEffect == some (Effect.returnCreatureFromGyThenAmass 3)
#guard gatheringOfDarkness.oracleText == gatheringOfDarknessOracle

/-- Gatherer Oracle text for Sound the Trumpets. -/
def soundTheTrumpetsOracle : String :=
  "Counter target spell. If that spell's mana value was 2 or less, recruit. (Draw a card, then discard a card. If you discarded a nonland card, create a 1/1 white Human Soldier creature token.)"

def soundTheTrumpetsDefinition : TraditionalCardDefinition := .card <|
  [
    .name "Sound the Trumpets",
    .manaCost [.generic 1, .mono .blue, .mono .blue],
    .type .instant
  ] ++ (parseOracleParts (name := "Sound the Trumpets") soundTheTrumpetsOracle).get!

def soundTheTrumpets : CardDef :=
  soundTheTrumpetsDefinition.toCardDef
    (oracleText := soundTheTrumpetsOracle)

#guard soundTheTrumpetsDefinition == .card [
  .name "Sound the Trumpets",
  .manaCost [.generic 1, .mono .blue, .mono .blue],
  .type .instant,
  .actions [
    .defineValueVariable 1 (.greatestManaValue (.target 1 .spell)),
    .counter (.targetReference 1),
    .if (.lessOrEqual (.variable 1) 2)
      [.keyword (.controller .this) .recruit]]]

#guard soundTheTrumpets.spellEffect == some (Effect.counterThenRecruitIfMvAtMost 2)
#guard soundTheTrumpets.oracleText == soundTheTrumpetsOracle

/-- Gatherer Oracle text for Fateful Discovery. -/
def fatefulDiscoveryOracle : String :=
  "Whenever an artifact you control enters, draw a card."

def fatefulDiscoveryDefinition : TraditionalCardDefinition := .card <|
  [
    .name "Fateful Discovery",
    .manaCost [.generic 3, .mono .blue, .mono .blue],
    .type .enchantment
  ] ++ (parseOracleParts (name := "Fateful Discovery") fatefulDiscoveryOracle).get!

def fatefulDiscovery : CardDef :=
  fatefulDiscoveryDefinition.toCardDef
    (oracleText := fatefulDiscoveryOracle)

#guard fatefulDiscoveryDefinition == .card [
  .name "Fateful Discovery",
  .manaCost [.generic 3, .mono .blue, .mono .blue],
  .type .enchantment,
  .ability (.triggered
    (.enter (.intersection [
      .permanent, .cardType .artifact, .controlled (.controller .this)]))
    (.draw (.controller .this) 1))]

#guard fatefulDiscovery.triggeredAbilities == #[.onArtifactYouControlEntersDraw]
#guard fatefulDiscovery.oracleText == fatefulDiscoveryOracle

/-- Gatherer Oracle text for Chief Warg's Company. -/
def chiefWargsCompanyOracle : String :=
  "Trample\nThis creature can't attack unless you control two or more other Wolves.\nAt the beginning of your upkeep, create a 2/2 green Wolf creature token."

def chiefWargsCompanyDefinition : TraditionalCardDefinition := .card <|
  [
    .name "Chief Warg's Company",
    .manaCost [.generic 1, .mono .black, .mono .green],
    .type .creature,
    .subtype .wolf,
    .power 5,
    .toughness 3
  ] ++ (parseOracleParts (name := "Chief Warg's Company") chiefWargsCompanyOracle).get!

def chiefWargsCompany : CardDef :=
  chiefWargsCompanyDefinition.toCardDef
    (oracleText := chiefWargsCompanyOracle)

#guard chiefWargsCompanyDefinition == .card [
  .name "Chief Warg's Company",
  .manaCost [.generic 1, .mono .black, .mono .green],
  .type .creature,
  .subtype .wolf,
  .power 5,
  .toughness 3,
  .ability (.keyword .trample),
  .ability (.static (.if
    (.less
      (.count (.intersection [
        .not .this, .permanent, .subtype .wolf, .controlled (.controller .this)]))
      (Value.nat 2))
    [.forbid (.attack .this .all)])),
  .ability (.triggered
    (.upkeep (.controller .this))
    (.createTokens (.controller .this) 1 [
      .type .creature, .subtype .wolf, .colorIndicator [.green],
      .power 2, .toughness 2]))]

#guard chiefWargsCompany.keywords.trample
#guard chiefWargsCompany.staticAbilities == #[.cantAttackUnlessYouControlNOther 2 "Wolf"]
#guard chiefWargsCompany.triggeredAbilities == #[.onYourUpkeepCreateTokens .wolf 1]
#guard chiefWargsCompany.oracleText == chiefWargsCompanyOracle

/-- Gatherer Oracle text for Dwarven Shortsword. -/
def dwarvenShortswordOracle : String :=
  "When this Equipment enters, create a 2/2 red Dwarf creature token, then attach this Equipment to it.\nEquipped creature gets +1/+2.\nEquip {2} ({2}: Attach to target creature you control. Equip only as a sorcery.)"

def dwarvenShortswordDefinition : TraditionalCardDefinition := .card <|
  [
    .name "Dwarven Shortsword",
    .manaCost [.generic 3, .mono .white],
    .type .artifact,
    .subtype .equipment
  ] ++ (parseOracleParts (name := "Dwarven Shortsword") dwarvenShortswordOracle).get!

def dwarvenShortsword : CardDef :=
  dwarvenShortswordDefinition.toCardDef
    (oracleText := dwarvenShortswordOracle)

#guard dwarvenShortswordDefinition == .card [
  .name "Dwarven Shortsword",
  .manaCost [.generic 3, .mono .white],
  .type .artifact,
  .subtype .equipment,
  .ability (.triggered
    (.enter .this)
    (.sequence [
      .actionId 1
        (.createTokens (.controller .this) 1 [
          .type .creature, .subtype .dwarf, .colorIndicator [.red], .power 2, .toughness 2]),
      .attach .this (.wasCreatedByAction 1)])),
  .ability (.static (.addPower (.hostOf .this) (Value.int 1))),
  .ability (.static (.addToughness (.hostOf .this) (Value.int 2))),
  .ability (.keywordWithCost .equip [.mana [.generic 2]])]

#guard dwarvenShortsword.triggeredAbilities == #[.onEnterCreateThenAttach .dwarf]
#guard dwarvenShortsword.staticAbilities == #[.equippedCreatureGets 1 2]
#guard dwarvenShortsword.oracleText == dwarvenShortswordOracle

/-- Gatherer Oracle text for Goblin Plate Mail. -/
def goblinPlateMailOracle : String :=
  "When this Equipment enters, amass Goblins 1, then attach this Equipment to the amassed Army. (To amass Goblins 1, put a +1/+1 counter on an Army you control. It's also a Goblin. If you don't control an Army, create a 0/0 black Goblin Army creature token first.)\nEquipped creature gets +1/+0 and has menace.\nEquip {4}"

def goblinPlateMailDefinition : TraditionalCardDefinition := .card <|
  [
    .name "Goblin Plate Mail",
    .manaCost [.generic 1, .hybrid .black .red],
    .type .artifact,
    .subtype .equipment
  ] ++ (parseOracleParts (name := "Goblin Plate Mail") goblinPlateMailOracle).get!

def goblinPlateMail : CardDef :=
  goblinPlateMailDefinition.toCardDef
    (oracleText := goblinPlateMailOracle)

#guard goblinPlateMailDefinition == .card [
  .name "Goblin Plate Mail",
  .manaCost [.generic 1, .hybrid .black .red],
  .type .artifact,
  .subtype .equipment,
  .ability (.triggered
    (.enter .this)
    (.sequence [
      .actionId 1 (.keyword (.controller .this) (.amass .goblin (.nat 1))),
      .attach .this (.wasObjectOfAction 1)])),
  .ability (.static (.addPower (.hostOf .this) (Value.int 1))),
  .ability (.static (.gainAbility (.hostOf .this) (.keyword .menace))),
  .ability (.keywordWithCost .equip [.mana [.generic 4]])]

#guard goblinPlateMail.triggeredAbilities == #[.onEnterAmassThenAttach 1]
#guard goblinPlateMail.staticAbilities == #[.equippedCreatureGetsAndHas 1 0 Keyword.menace]
#guard goblinPlateMail.oracleText == goblinPlateMailOracle

/-- Gatherer Oracle text for Moment of Glory. -/
def momentOfGloryOracle : String :=
  "Put a +1/+1 counter on target creature you control. If this spell was cast from a graveyard, also put a +1/+1 counter on each other creature you control.\nFlashback {4}{W} (You may cast this card from your graveyard for its flashback cost. Then exile it.)"

def momentOfGloryDefinition : TraditionalCardDefinition := .card <|
  [
    .name "Moment of Glory",
    .manaCost [.mono .white],
    .type .sorcery
  ] ++ (parseOracleParts (name := "Moment of Glory") momentOfGloryOracle).get!

def momentOfGlory : CardDef :=
  momentOfGloryDefinition.toCardDef
    (oracleText := momentOfGloryOracle)

#guard momentOfGloryDefinition == .card [
  .name "Moment of Glory",
  .manaCost [.mono .white],
  .type .sorcery,
  .actions [
    .putCounter
      (.target 1 (.intersection [
        .permanent, .cardType .creature, .controlled (.controller .this)]))
      .plusOnePlusOne 1,
    .if (.happened (.castSpellFromGraveyard .this) .gameStart)
      [.putCounter
        (.intersection [
          .not (.targetReference 1),
          .permanent, .cardType .creature, .controlled (.controller .this)])
        .plusOnePlusOne 1]],
  .ability (.keywordWithCost .flashback [.mana [.generic 4, .mono .white]])]

#guard momentOfGlory.spellEffect == some Effect.plusOneThenEachOtherIfFromGy
#guard momentOfGlory.flashback == some (ManaCost.ofGenericAndColor 4 .white)
#guard momentOfGlory.manaCost == ManaCost.ofColor .white
#guard momentOfGlory.oracleText == momentOfGloryOracle

/-- Gatherer Oracle text for Plunder the Trollshaws. -/
def plunderTheTrollshawsOracle : String :=
  "Draw a card. If this spell was cast from a graveyard, draw two cards instead.\nFlashback {3}{U} (You may cast this card from your graveyard for its flashback cost. Then exile it.)"

def plunderTheTrollshawsDefinition : TraditionalCardDefinition := .card <|
  [
    .name "Plunder the Trollshaws",
    .manaCost [.generic 1, .mono .blue],
    .type .instant
  ] ++ (parseOracleParts (name := "Plunder the Trollshaws") plunderTheTrollshawsOracle).get!

def plunderTheTrollshaws : CardDef :=
  plunderTheTrollshawsDefinition.toCardDef
    (oracleText := plunderTheTrollshawsOracle)

#guard plunderTheTrollshawsDefinition == .card [
  .name "Plunder the Trollshaws",
  .manaCost [.generic 1, .mono .blue],
  .type .instant,
  .actions [
    .ifElse (.happened (.castSpellFromGraveyard .this) .gameStart)
      [.draw (.controller .this) 2]
      [.draw (.controller .this) 1]],
  .ability (.keywordWithCost .flashback [.mana [.generic 3, .mono .blue]])]

#guard plunderTheTrollshaws.spellEffect == some (Effect.drawIfFromGy 1 2)
#guard plunderTheTrollshaws.flashback == some (ManaCost.ofGenericAndColor 3 .blue)
#guard plunderTheTrollshaws.manaCost == ManaCost.ofGenericAndColor 1 .blue
#guard plunderTheTrollshaws.oracleText == plunderTheTrollshawsOracle

/-- Gatherer Oracle text for Tidings of War. -/
def tidingsOfWarOracle : String :=
  "Amass Goblins 1. If this spell was cast from a graveyard, amass Goblins 3 instead. (To amass Goblins X, put X +1/+1 counters on an Army you control. It's also a Goblin. If you don't control an Army, create a 0/0 black Goblin Army creature token first.)\nFlashback {3}{R} (You may cast this card from your graveyard for its flashback cost. Then exile it.)"

def tidingsOfWarDefinition : TraditionalCardDefinition := .card <|
  [
    .name "Tidings of War",
    .manaCost [.mono .red],
    .type .sorcery
  ] ++ (parseOracleParts (name := "Tidings of War") tidingsOfWarOracle).get!

def tidingsOfWar : CardDef :=
  tidingsOfWarDefinition.toCardDef
    (oracleText := tidingsOfWarOracle)

#guard tidingsOfWarDefinition == .card [
  .name "Tidings of War",
  .manaCost [.mono .red],
  .type .sorcery,
  .actions [
    .ifElse (.happened (.castSpellFromGraveyard .this) .gameStart)
      [.keyword (.controller .this) (.amass .goblin 3)]
      [.keyword (.controller .this) (.amass .goblin 1)]],
  .ability (.keywordWithCost .flashback [.mana [.generic 3, .mono .red]])]

#guard tidingsOfWar.spellEffect == some (Effect.amassGoblinsOrFromGy 1 3)
#guard tidingsOfWar.flashback == some (ManaCost.ofGenericAndColor 3 .red)
#guard tidingsOfWar.manaCost == ManaCost.ofColor .red
#guard tidingsOfWar.oracleText == tidingsOfWarOracle

/-- Gatherer Oracle text for Eagle's Rescue. -/
def eaglesRescueOracle : String :=
  "Enchant creature\nEnchanted creature gets +2/+2 and has flying.\n{2}{W/U}{W/U}: Return this card from your graveyard to the battlefield attached to target creature you control with power 1 or less. Activate only as a sorcery."

def eaglesRescueDefinition : TraditionalCardDefinition := .card <|
  [
    .name "Eagle's Rescue",
    .manaCost [.generic 2, .hybrid .white .blue, .hybrid .white .blue],
    .type .enchantment,
    .subtype .aura
  ] ++ (parseOracleParts (name := "Eagle's Rescue") eaglesRescueOracle).get!

def eaglesRescue : CardDef :=
  eaglesRescueDefinition.toCardDef
    (oracleText := eaglesRescueOracle)

#guard eaglesRescueDefinition == .card [
  .name "Eagle's Rescue",
  .manaCost [.generic 2, .hybrid .white .blue, .hybrid .white .blue],
  .type .enchantment,
  .subtype .aura,
  .ability (.keywordWithTarget .enchant 1
    (.intersection [.permanent, .cardType .creature])),
  .ability (.static (.addPower (.hostOf .this) (Value.int 2))),
  .ability (.static (.addToughness (.hostOf .this) (Value.int 2))),
  .ability (.static (.gainAbility (.hostOf .this) (.keyword .flying))),
  .ability (.graveyardActivatedIf
    (.timeToCastSorcery (.controller .this))
    [.mana [.generic 2, .hybrid .white .blue, .hybrid .white .blue]]
    (.putOntoBattlefieldInState
      (.intersection [.inGraveyard, .source .this])
      [.attachedTo
        (.target 2 (.intersection [
          .permanent, .cardType .creature, .controlled (.controller .this),
          .powerAtMost (Value.int 1)]))]))]

#guard eaglesRescue.isAura
#guard eaglesRescue.staticAbilities == #[.enchantedCreatureGetsAndHas 2 2 Keyword.flying]
#guard eaglesRescue.activatedAbilities == #[
  activated (Effect.returnFromGyAttachPowerAtMost 1)
    (ManaCost.ofGenericAndHybrids 2 .white .blue 2)
    (activateFromGraveyard := true) (onlyAsSorcery := true)]
#guard eaglesRescue.oracleText == eaglesRescueOracle

/-- Gatherer Oracle text for Gandalf, Wandering Wizard. -/
def gandalfWanderingWizardOracle : String :=
  "Ward {3} (Whenever this creature becomes the target of a spell or ability an opponent controls, counter it unless that player pays {3}.)\n{6}: Gandalf's owner shuffles him into their library and draws three cards."

def gandalfWanderingWizardDefinition : TraditionalCardDefinition := .card <|
  [
    .name "Gandalf, Wandering Wizard",
    .manaCost [.generic 4, .mono .blue],
    .type .creature,
    .supertype .legendary,
    .subtype .avatar,
    .subtype .wizard,
    .power 4,
    .toughness 5
  ] ++ (parseOracleParts (name := "Gandalf, Wandering Wizard") gandalfWanderingWizardOracle).get!

def gandalfWanderingWizard : CardDef :=
  gandalfWanderingWizardDefinition.toCardDef
    (oracleText := gandalfWanderingWizardOracle)

#guard gandalfWanderingWizardDefinition == .card [
  .name "Gandalf, Wandering Wizard",
  .manaCost [.generic 4, .mono .blue],
  .type .creature,
  .supertype .legendary,
  .subtype .avatar,
  .subtype .wizard,
  .power 4,
  .toughness 5,
  .ability (.keywordWithCost .ward [.mana [.generic 3]]),
  .ability (.activated [.mana [.generic 6]]
    (.sequence [
      .defineSelectorVariable 1 (.owner (.source .this)),
      .shuffleIntoOwnersLibrary (.source .this),
      .draw (.variable 1) 3]))]

#guard gandalfWanderingWizard.ward == some 3
#guard gandalfWanderingWizard.activatedAbilities == #[
  activated (Effect.ownerShuffleSourceDraw 3) (ManaCost.ofGeneric 6)]
#guard gandalfWanderingWizard.oracleText == gandalfWanderingWizardOracle

/-- Gatherer Oracle text for Troll Negotiations. -/
def trollNegotiationsOracle : String :=
  "Put two +1/+1 counters on target creature you control. Then it fights target creature an opponent controls. (Each deals damage equal to its power to the other.)"

def trollNegotiationsDefinition : TraditionalCardDefinition := .card <|
  [
    .name "Troll Negotiations",
    .manaCost [.generic 2, .mono .green, .mono .green],
    .type .sorcery
  ] ++ (parseOracleParts (name := "Troll Negotiations") trollNegotiationsOracle).get!

def trollNegotiations : CardDef :=
  trollNegotiationsDefinition.toCardDef
    (oracleText := trollNegotiationsOracle)

#guard trollNegotiationsDefinition == .card [
  .name "Troll Negotiations",
  .manaCost [.generic 2, .mono .green, .mono .green],
  .type .sorcery,
  .actions [
    .putCounter
      (.target 1 (.intersection [
        .permanent, .cardType .creature, .controlled (.controller .this)]))
      .plusOnePlusOne 2,
    .fight (.targetReference 1)
      (.target 2 (.intersection [
        .permanent, .cardType .creature,
        .controlled (.opponent (.controller .this))]))]]

#guard trollNegotiations.spellEffect == some (Effect.plusOneThenFight 2)
#guard trollNegotiations.oracleText == trollNegotiationsOracle

/-- Gatherer Oracle text for Dwarven Mattock. -/
def dwarvenMattockOracle : String :=
  "When this Equipment enters, attach it to target Dwarf you control.\nEquipped creature gets +2/+2 and has ward {1}. (Whenever equipped creature becomes the target of a spell or ability an opponent controls, counter it unless that player pays {1}.)\nEquip {3} ({3}: Attach to target creature you control. Equip only as a sorcery.)"

def dwarvenMattockDefinition : TraditionalCardDefinition := .card <|
  [
    .name "Dwarven Mattock",
    .manaCost [.generic 2],
    .type .artifact,
    .subtype .equipment
  ] ++ (parseOracleParts (name := "Dwarven Mattock") dwarvenMattockOracle).get!

def dwarvenMattock : CardDef :=
  dwarvenMattockDefinition.toCardDef
    (oracleText := dwarvenMattockOracle)

#guard dwarvenMattockDefinition == .card [
  .name "Dwarven Mattock",
  .manaCost [.generic 2],
  .type .artifact,
  .subtype .equipment,
  .ability (.triggered (.enter .this)
    (.attach .this
      (.target 1 (.intersection [
        .permanent, .cardType .creature, .subtype .dwarf,
        .controlled (.controller .this)])))),
  .ability (.static (.addPower (.hostOf .this) (Value.int 2))),
  .ability (.static (.addToughness (.hostOf .this) (Value.int 2))),
  .ability (.static (.gainAbility (.hostOf .this)
    (.keywordWithCost .ward [.mana [.generic 1]]))),
  .ability (.keywordWithCost .equip [.mana [.generic 3]])]

#guard dwarvenMattock.triggeredAbilities == #[.onEnterAttachToSubtype "Dwarf"]
#guard dwarvenMattock.staticAbilities == #[.equippedCreatureGetsAndWard 2 2 1]
#guard dwarvenMattock.activatedAbilities == #[equipAbility (ManaCost.ofGeneric 3)]
#guard dwarvenMattock.oracleText == dwarvenMattockOracle

/-- Gatherer Oracle text for Great Ugly-Looking Goblin. -/
def greatUglyLookingGoblinOracle : String :=
  "Each creature you control with a +1/+1 counter on it has menace. (It can't be blocked except by two or more creatures.)\n//ADV//\nClap! Snap! {1}{B}\nSorcery — Adventure\nAmass Goblins 2. (Then exile this card. You may cast the creature later from exile.)"

def greatUglyLookingGoblinDefinition : TraditionalCardDefinition := .card <|
  [
    .name "Great Ugly-Looking Goblin",
    .manaCost [.generic 5, .mono .black],
    .type .creature,
    .subtype .goblin,
    .subtype .soldier,
    .power 4,
    .toughness 4
  ] ++ (parseOracleParts (name := "Great Ugly-Looking Goblin") greatUglyLookingGoblinOracle).get!

def greatUglyLookingGoblin : CardDef :=
  greatUglyLookingGoblinDefinition.toCardDef
    (oracleText := greatUglyLookingGoblinOracle)

#guard greatUglyLookingGoblinDefinition == .card [
  .name "Great Ugly-Looking Goblin",
  .manaCost [.generic 5, .mono .black],
  .type .creature,
  .subtype .goblin,
  .subtype .soldier,
  .power 4,
  .toughness 4,
  .ability (.static (.gainAbility
    (.intersection [
      .permanent, .cardType .creature, .controlled (.controller .this),
      .hasCounter .plusOnePlusOne])
    (.keyword .menace))),
  .alternative [
    .name "Clap! Snap!",
    .manaCost [.generic 1, .mono .black],
    .type .sorcery,
    .subtype .adventure,
    .actions [.keyword (.controller .this) (.amass .goblin 2)]]]

#guard greatUglyLookingGoblin.staticAbilities == #[.creaturesYouControlWithPlusOneHaveMenace]
#guard greatUglyLookingGoblin.adventure == some {
  name := "Clap! Snap!"
  manaCost := ManaCost.ofGenericAndColor 1 .black
  types := #[.sorcery]
  subtypes := #["Adventure"]
  oracleText := "amass Goblins 2"
  spellEffect := some (Effect.amassGoblins 2) }
#guard greatUglyLookingGoblin.oracleText == greatUglyLookingGoblinOracle

/-- Gatherer Oracle text for The Arkenstone. -/
def theArkenstoneOracle : String :=
  "Creatures you control get +1/+1.\nAt the beginning of your end step, draw a card.\n//ADV//\nSeek the Heart {2}{W}\nSorcery — Adventure\nSearch your library for a legendary creature card, reveal it, put it into your hand, then shuffle. (Then exile this card. You may cast the artifact later from exile.)"

def theArkenstoneDefinition : TraditionalCardDefinition := .card <|
  [
    .name "The Arkenstone",
    .manaCost [.generic 5],
    .type .artifact,
    .supertype .legendary
  ] ++ (parseOracleParts (name := "The Arkenstone") theArkenstoneOracle).get!

def theArkenstone : CardDef :=
  theArkenstoneDefinition.toCardDef
    (oracleText := theArkenstoneOracle)

#guard theArkenstoneDefinition == .card [
  .name "The Arkenstone",
  .manaCost [.generic 5],
  .type .artifact,
  .supertype .legendary,
  .ability (.static (.addPower
    (.intersection [
      .permanent, .cardType .creature, .controlled (.controller .this)])
    (Value.int 1))),
  .ability (.static (.addToughness
    (.intersection [
      .permanent, .cardType .creature, .controlled (.controller .this)])
    (Value.int 1))),
  .ability (.triggered (.endStep (.controller .this))
    (.draw (.controller .this) 1)),
  .alternative [
    .name "Seek the Heart",
    .manaCost [.generic 2, .mono .white],
    .type .sorcery,
    .subtype .adventure,
    .actions [
      .searchLibraryThenShuffle (.controller .this) [
        .defineSelectorVariable 1
          (.selected (.controller .this) (.range 1 1)
            (.intersection [
              .inLibrary, .cardType .creature, .supertype .legendary])),
        .reveal (.variable 1),
        .returnToHand (.variable 1)]]]]

#guard theArkenstone.staticAbilities == #[.creaturesYouControlGet 1 1]
#guard theArkenstone.triggeredAbilities == #[.onYourEndStepDraw]
#guard theArkenstone.adventure == some {
  name := "Seek the Heart"
  manaCost := ManaCost.ofGenericAndColor 2 .white
  types := #[.sorcery]
  subtypes := #["Adventure"]
  oracleText := "search your library for a legendary creature card, reveal it, put it into your hand, then shuffle"
  spellEffect := some Effect.searchLegendaryCreatureToHand }
#guard theArkenstone.oracleText == theArkenstoneOracle

/-- Gatherer Oracle text for Bolg's Company. -/
def bolgsCompanyOracle : String :=
  "This creature has haste as long as you control another Goblin.\n{T}, Sacrifice another Goblin: Add {B}{R}."

def bolgsCompanyDefinition : TraditionalCardDefinition := .card <|
  [
    .name "Bolg's Company",
    .manaCost [.mono .black, .mono .red],
    .type .creature,
    .subtype .goblin,
    .subtype .soldier,
    .power 2,
    .toughness 2
  ] ++ (parseOracleParts (name := "Bolg's Company") bolgsCompanyOracle).get!

def bolgsCompany : CardDef :=
  bolgsCompanyDefinition.toCardDef
    (oracleText := bolgsCompanyOracle)

#guard bolgsCompanyDefinition == .card [
  .name "Bolg's Company",
  .manaCost [.mono .black, .mono .red],
  .type .creature,
  .subtype .goblin,
  .subtype .soldier,
  .power 2,
  .toughness 2,
  .ability (.static (.if
    (.any (.intersection [
      .not .this, .permanent, .subtype .goblin, .controlled (.controller .this)]))
    [.gainAbility .this (.keyword .haste)])),
  .ability (.activated
    [.tapSymbol,
      .sacrificeCount
        (.intersection [
          .not .this, .permanent, .subtype .goblin, .controlled (.controller .this)])
        1]
    (.addMana (.controller .this) [.colored .black, .colored .red]))]

#guard bolgsCompany.staticAbilities == #[.hasteIfYouControlOtherSubtype "Goblin"]
#guard bolgsCompany.activatedAbilities.size == 1
#guard bolgsCompany.activatedAbilities[0]!.cost.tap
#guard bolgsCompany.activatedAbilities[0]!.cost.sacrificeAnotherSubtype == some "Goblin"
#guard bolgsCompany.activatedAbilities[0]!.effect ==
  Effect.addMana #[.colored .black, .colored .red]
#guard bolgsCompany.oracleText == bolgsCompanyOracle

/-- Gatherer Oracle text for Nori, Teller of Tales. -/
def noriTellerOfTalesOracle : String :=
  "Whenever Nori attacks, target attacking creature gains first strike until end of turn."

def noriTellerOfTalesDefinition : TraditionalCardDefinition := .card <|
  [
    .name "Nori, Teller of Tales",
    .manaCost [.generic 1, .hybrid .red .white],
    .type .creature,
    .supertype .legendary,
    .subtype .dwarf,
    .subtype .bard,
    .power 2,
    .toughness 2
  ] ++ (parseOracleParts (name := "Nori, Teller of Tales") noriTellerOfTalesOracle).get!

def noriTellerOfTales : CardDef :=
  noriTellerOfTalesDefinition.toCardDef
    (oracleText := noriTellerOfTalesOracle)

#guard noriTellerOfTalesDefinition == .card [
  .name "Nori, Teller of Tales",
  .manaCost [.generic 1, .hybrid .red .white],
  .type .creature,
  .supertype .legendary,
  .subtype .dwarf,
  .subtype .bard,
  .power 2,
  .toughness 2,
  .ability (.triggered (.attack .this .all)
    (.continuous
      [.gainAbility
        (.target 1 (.intersection [
          .permanent, .cardType .creature, .attacking .all]))
        (.keyword .firstStrike)]
      .endOfTurn))]

#guard noriTellerOfTales.triggeredAbilities ==
  #[.onAttackTargetGainsKeywords Keyword.firstStrike.toKeywords]
#guard noriTellerOfTales.supertypes.any (· == .legendary)
#guard noriTellerOfTales.oracleText == noriTellerOfTalesOracle

/-- Gatherer Oracle text for The Lord of the Eagles. -/
def theLordOfTheEaglesOracle : String :=
  "Flash\nThis spell costs {X} less to cast, where X is the total power of creatures you control with flying.\nFlying"

def theLordOfTheEaglesDefinition : TraditionalCardDefinition := .card <|
  [
    .name "The Lord of the Eagles",
    .manaCost [.generic 7, .mono .blue, .mono .blue],
    .type .creature,
    .supertype .legendary,
    .subtype .bird,
    .subtype .noble,
    .power 8,
    .toughness 8
  ] ++ (parseOracleParts (name := "The Lord of the Eagles") theLordOfTheEaglesOracle).get!

def theLordOfTheEagles : CardDef :=
  theLordOfTheEaglesDefinition.toCardDef
    (oracleText := theLordOfTheEaglesOracle)

#guard theLordOfTheEaglesDefinition == .card [
  .name "The Lord of the Eagles",
  .manaCost [.generic 7, .mono .blue, .mono .blue],
  .type .creature,
  .supertype .legendary,
  .subtype .bird,
  .subtype .noble,
  .power 8,
  .toughness 8,
  .ability (.keyword .flash),
  .ability (.stackStatic
    (.reduceCostWithX .this [.mana [.x]]
      (.totalPower (.intersection [
        .permanent, .cardType .creature, .keyword .flying,
        .controlled (.controller .this)])))),
  .ability (.keyword .flying)]

#guard theLordOfTheEagles.keywords.flash
#guard theLordOfTheEagles.keywords.flying
#guard theLordOfTheEagles.costReductionEqualFlyingPower
#guard theLordOfTheEagles.manaCost == ManaCost.ofGenericAndColors 7 [.blue, .blue]
#guard theLordOfTheEagles.oracleText == theLordOfTheEaglesOracle

/-- Gatherer Oracle text for Thrór's Map. -/
def throrsMapOracle : String :=
  "When Thrór's Map enters, search your library for a basic land card, reveal it, put it into your hand, then shuffle.\n{2}, {T}: Draw a card, then discard a card."

def throrsMapDefinition : TraditionalCardDefinition := .card <|
  [
    .name "Thrór's Map",
    .manaCost [.generic 2],
    .type .artifact,
    .supertype .legendary
  ] ++ (parseOracleParts (name := "Thrór's Map") throrsMapOracle).get!

def throrsMap : CardDef :=
  throrsMapDefinition.toCardDef
    (oracleText := throrsMapOracle)

#guard throrsMapDefinition == .card [
  .name "Thrór's Map",
  .manaCost [.generic 2],
  .type .artifact,
  .supertype .legendary,
  .ability (.triggered (.enter .this)
    (.searchLibraryThenShuffle (.controller .this) [
      .defineSelectorVariable 1
        (.selected (.controller .this) (.range 1 1)
          (.intersection [.inLibrary, .cardType .land, .supertype .basic])),
      .reveal (.variable 1),
      .returnToHand (.variable 1)])),
  .ability (.activated
    [.mana [.generic 2], .tapSymbol]
    (.sequence [
      .draw (.controller .this) 1,
      .discard (.controller .this) 1]))]

#guard throrsMap.triggeredAbilities == #[.onEnterSearchBasicToHand]
#guard throrsMap.activatedAbilities.size == 1
#guard throrsMap.activatedAbilities[0]!.effect == Effect.abilityDrawThenDiscard 1
#guard throrsMap.activatedAbilities[0]!.cost.tap
#guard throrsMap.activatedAbilities[0]!.cost.mana == ManaCost.ofGeneric 2
#guard throrsMap.supertypes.any (· == .legendary)
#guard throrsMap.oracleText == throrsMapOracle

/-- Gatherer Oracle text for The Black Arrow. -/
def theBlackArrowOracle : String :=
  "Flash\nWhen The Black Arrow enters, it deals 1 damage to any target. If a Dragon is dealt damage this way, destroy it.\nEquipped creature gets +1/+1 and has reach.\nEquip {1} ({1}: Attach to target creature you control. Equip only as a sorcery.)"

def theBlackArrowDefinition : TraditionalCardDefinition := .card <|
  [
    .name "The Black Arrow",
    .manaCost [.generic 3],
    .type .artifact,
    .supertype .legendary,
    .subtype .equipment
  ] ++ (parseOracleParts (name := "The Black Arrow") theBlackArrowOracle).get!

def theBlackArrow : CardDef :=
  theBlackArrowDefinition.toCardDef
    (oracleText := theBlackArrowOracle)

#guard theBlackArrowDefinition == .card [
  .name "The Black Arrow",
  .manaCost [.generic 3],
  .type .artifact,
  .supertype .legendary,
  .subtype .equipment,
  .ability (.keyword .flash),
  .ability (.triggered (.enter .this)
    (.sequence [
      .actionId 1
        (.dealDamage (.source .this) (.target 1 .all) 1),
      .if (.anySubtype (.wasObjectOfAction 1) .dragon)
        [.destroy (.wasObjectOfAction 1)]])),
  .ability (.static (.addPower (.hostOf .this) (Value.int 1))),
  .ability (.static (.addToughness (.hostOf .this) (Value.int 1))),
  .ability (.static (.gainAbility (.hostOf .this) (.keyword .reach))),
  .ability (.keywordWithCost .equip [.mana [.generic 1]])]

#guard theBlackArrow.keywords.flash
#guard theBlackArrow.triggeredAbilities == #[.onEnterDealDamageDestroyIfSubtype 1 "Dragon"]
#guard theBlackArrow.staticAbilities == #[.equippedCreatureGetsAndHas 1 1 Keyword.reach]
#guard theBlackArrow.supertypes.any (· == .legendary)
#guard theBlackArrow.isEquipment
#guard theBlackArrow.activatedAbilities.size == 1
#guard theBlackArrow.activatedAbilities[0]!.onlyAsSorcery
#guard theBlackArrow.activatedAbilities[0]!.effect == Effect.attachToTargetCreatureYouControl
#guard theBlackArrow.activatedAbilities[0]!.cost.mana == ManaCost.ofGeneric 1
#guard theBlackArrow.oracleText == theBlackArrowOracle

/-- Gatherer Oracle text for Smaug the Magnificent. -/
def smaugTheMagnificentOracle : String :=
  "Flying, haste\nWhenever Smaug attacks, he deals damage equal to the number of Treasures you control to any target.\nAt the beginning of your upkeep, create a Treasure token."

def smaugTheMagnificentDefinition : TraditionalCardDefinition := .card <|
  [
    .name "Smaug the Magnificent",
    .manaCost [.generic 2, .mono .red, .mono .red],
    .type .creature,
    .supertype .legendary,
    .subtype .dragon,
    .power 4,
    .toughness 3
  ] ++ (parseOracleParts (name := "Smaug the Magnificent") smaugTheMagnificentOracle).get!

def smaugTheMagnificent : CardDef :=
  smaugTheMagnificentDefinition.toCardDef
    (oracleText := smaugTheMagnificentOracle)

#guard smaugTheMagnificentDefinition == .card [
  .name "Smaug the Magnificent",
  .manaCost [.generic 2, .mono .red, .mono .red],
  .type .creature,
  .supertype .legendary,
  .subtype .dragon,
  .power 4,
  .toughness 3,
  .ability (.keyword .flying),
  .ability (.keyword .haste),
  .ability (.triggered (.attack .this .all)
    (.dealDamage (.source .this) (.target 1 .all)
      (.count (.intersection [
        .permanent, .cardType .artifact, .subtype .treasure,
        .controlled (.controller .this)])))),
  .ability (.triggered (.upkeep (.controller .this))
    (.createTokens (.controller .this) 1 PredefinedToken.treasureToken))]

#guard smaugTheMagnificent.keywords.flying
#guard smaugTheMagnificent.keywords.haste
#guard smaugTheMagnificent.triggeredAbilities ==
  #[.onAttackDamageEqualTreasures, .onYourUpkeepCreateTokens .treasure 1]
#guard smaugTheMagnificent.oracleText == smaugTheMagnificentOracle

/-- Gatherer Oracle text for The Queen of Dale. -/
def theQueenOfDaleOracle : String :=
  "Whenever an opponent casts their first noncreature spell each turn, you recruit. (Draw a card, then discard a card. If you discarded a nonland card, create a 1/1 white Human Soldier creature token.)"

def theQueenOfDaleDefinition : TraditionalCardDefinition := .card <|
  [
    .name "The Queen of Dale",
    .manaCost [.generic 1, .mono .white],
    .type .creature,
    .supertype .legendary,
    .subtype .human,
    .subtype .noble,
    .power 2,
    .toughness 1
  ] ++ (parseOracleParts (name := "The Queen of Dale") theQueenOfDaleOracle).get!

def theQueenOfDale : CardDef :=
  theQueenOfDaleDefinition.toCardDef
    (oracleText := theQueenOfDaleOracle)

#guard theQueenOfDaleDefinition == .card [
  .name "The Queen of Dale",
  .manaCost [.generic 1, .mono .white],
  .type .creature,
  .supertype .legendary,
  .subtype .human,
  .subtype .noble,
  .power 2,
  .toughness 1,
  .ability (.triggered
    (.ordinal 1 .turnStart
      (.castSpell (.intersection [
        .spell, .not (.cardType .creature),
        .controlled (.opponent (.controller .this))])))
    (.keyword (.controller .this) .recruit))]

#guard theQueenOfDale.triggeredAbilities == #[.onOpponentCastsFirstNoncreatureRecruit]
#guard theQueenOfDale.oracleText == theQueenOfDaleOracle

/-- Gatherer Oracle text for Ori, Keeper of Songs. -/
def oriKeeperOfSongsOracle : String :=
  "Storied (If you control three or more artifacts, legendaries, and/or Sagas, you have an enduring story for the rest of the game.)\nAs long as you have an enduring story, Ori gets +1/+0 and has vigilance."

def oriKeeperOfSongsDefinition : TraditionalCardDefinition := .card <|
  [
    .name "Ori, Keeper of Songs",
    .manaCost [.generic 2, .mono .white],
    .type .creature,
    .supertype .legendary,
    .subtype .dwarf,
    .subtype .bard,
    .power 3,
    .toughness 3
  ] ++ (parseOracleParts (name := "Ori, Keeper of Songs") oriKeeperOfSongsOracle).get!

def oriKeeperOfSongs : CardDef :=
  oriKeeperOfSongsDefinition.toCardDef
    (oracleText := oriKeeperOfSongsOracle)

#guard oriKeeperOfSongsDefinition == .card [
  .name "Ori, Keeper of Songs",
  .manaCost [.generic 2, .mono .white],
  .type .creature,
  .supertype .legendary,
  .subtype .dwarf,
  .subtype .bard,
  .power 3,
  .toughness 3,
  .ability (.keyword .storied),
  .ability (.static (.if (.enduringStory (.controller .this))
    [.addPower .this (Value.int 1), .gainAbility .this (.keyword .vigilance)]))]

#guard oriKeeperOfSongs.keywords.storied
#guard oriKeeperOfSongs.staticAbilities ==
  #[.getsAndHasIfEnduringStory 1 0 Keyword.vigilance]
#guard oriKeeperOfSongs.oracleText == oriKeeperOfSongsOracle

/-- Gatherer Oracle text for Óin the Brave. -/
def oinTheBraveOracle : String :=
  "Storied (If you control three or more artifacts, legendaries, and/or Sagas, you have an enduring story for the rest of the game.)\nAs long as you have an enduring story, Óin gets +1/+0 and has haste.\n{1}, {T}, Discard a card: Draw a card."

def oinTheBraveDefinition : TraditionalCardDefinition := .card <|
  [
    .name "Óin the Brave",
    .manaCost [.generic 1, .mono .red],
    .type .creature,
    .supertype .legendary,
    .subtype .dwarf,
    .subtype .warrior,
    .power 1,
    .toughness 3
  ] ++ (parseOracleParts (name := "Óin the Brave") oinTheBraveOracle).get!

def oinTheBrave : CardDef :=
  oinTheBraveDefinition.toCardDef
    (oracleText := oinTheBraveOracle)

#guard oinTheBraveDefinition == .card [
  .name "Óin the Brave",
  .manaCost [.generic 1, .mono .red],
  .type .creature,
  .supertype .legendary,
  .subtype .dwarf,
  .subtype .warrior,
  .power 1,
  .toughness 3,
  .ability (.keyword .storied),
  .ability (.static (.if (.enduringStory (.controller .this))
    [.addPower .this (Value.int 1), .gainAbility .this (.keyword .haste)])),
  .ability (.activated
    [.mana [.generic 1], .tapSymbol,
      .discard
        (.selected
          (.controller .this)
          (.range 1 1)
          (.intersection [.inHand, .owner (.controller .this)]))]
    (.draw (.controller .this) 1))]

#guard oinTheBrave.keywords.storied
#guard oinTheBrave.staticAbilities ==
  #[.getsAndHasIfEnduringStory 1 0 Keyword.haste]
#guard oinTheBrave.activatedAbilities ==
  #[activated (Effect.abilityDraw 1) (ManaCost.ofGeneric 1) (tap := true)
    (discardACard := true)]
#guard oinTheBrave.oracleText == oinTheBraveOracle

/-- Gatherer Oracle text for Bombur, Gentle Dreamer. -/
def bomburGentleDreamerOracle : String :=
  "Storied (If you control three or more artifacts, legendaries, and/or Sagas, you have an enduring story for the rest of the game.)\nBombur doesn't untap during your untap step unless you have an enduring story."

def bomburGentleDreamerDefinition : TraditionalCardDefinition := .card <|
  [
    .name "Bombur, Gentle Dreamer",
    .manaCost [.generic 2, .mono .red],
    .type .creature,
    .supertype .legendary,
    .subtype .dwarf,
    .subtype .bard,
    .power 5,
    .toughness 3
  ] ++ (parseOracleParts (name := "Bombur, Gentle Dreamer") bomburGentleDreamerOracle).get!

def bomburGentleDreamer : CardDef :=
  bomburGentleDreamerDefinition.toCardDef
    (oracleText := bomburGentleDreamerOracle)

#guard bomburGentleDreamerDefinition == .card [
  .name "Bombur, Gentle Dreamer",
  .manaCost [.generic 2, .mono .red],
  .type .creature,
  .supertype .legendary,
  .subtype .dwarf,
  .subtype .bard,
  .power 5,
  .toughness 3,
  .ability (.keyword .storied),
  .ability (.static
    (.if (.not (.enduringStory (.controller .this)))
      [.doesntUntap .this]))]

#guard bomburGentleDreamer.keywords.storied
#guard bomburGentleDreamer.staticAbilities == #[.doesntUntapUnlessEnduringStory]
#guard bomburGentleDreamer.oracleText == bomburGentleDreamerOracle

/-- Gatherer Oracle text for Fíli the Pathfinder. -/
def filiThePathfinderOracle : String :=
  "Storied (If you control three or more artifacts, legendaries, and/or Sagas, you have an enduring story for the rest of the game.)\nAs long as you have an enduring story, creatures you control get +1/+1.\nWhenever Fíli or another nontoken Dwarf you control enters, create a 2/2 red Dwarf creature token."

def filiThePathfinderDefinition : TraditionalCardDefinition := .card <|
  [
    .name "Fíli the Pathfinder",
    .manaCost [.generic 3, .mono .white],
    .type .creature,
    .supertype .legendary,
    .subtype .dwarf,
    .subtype .scout,
    .power 2,
    .toughness 2
  ] ++ (parseOracleParts (name := "Fíli the Pathfinder") filiThePathfinderOracle).get!

def filiThePathfinder : CardDef :=
  filiThePathfinderDefinition.toCardDef
    (oracleText := filiThePathfinderOracle)

#guard filiThePathfinderDefinition == .card [
  .name "Fíli the Pathfinder",
  .manaCost [.generic 3, .mono .white],
  .type .creature,
  .supertype .legendary,
  .subtype .dwarf,
  .subtype .scout,
  .power 2,
  .toughness 2,
  .ability (.keyword .storied),
  .ability (.static (.if (.enduringStory (.controller .this))
    [.addPower
      (.intersection [
        .permanent,
        .cardType .creature,
        .controlled (.controller .this)]) (Value.int 1),
     .addToughness
      (.intersection [
        .permanent,
        .cardType .creature,
        .controlled (.controller .this)]) (Value.int 1)])),
  .ability (.triggered
    (.or
      (.enter .this)
      (.enter
        (.intersection [
          .not .this,
          .not .token,
          .permanent,
          .cardType .creature,
          .subtype .dwarf,
          .controlled (.controller .this)])))
    (.createTokens (.controller .this) 1 [
      .type .creature,
      .subtype .dwarf,
      .colorIndicator [.red],
      .power 2,
      .toughness 2]))]

#guard filiThePathfinder.keywords.storied
#guard filiThePathfinder.staticAbilities ==
  #[.creaturesYouControlGetIfEnduringStory 1 1]
#guard filiThePathfinder.triggeredAbilities ==
  #[.onThisOrNontokenSubtypeEntersCreateTokens "Dwarf" .dwarf 1]
#guard filiThePathfinder.oracleText == filiThePathfinderOracle

/-- Gatherer Oracle text for Thorin Oakenshield. -/
def thorinOakenshieldOracle : String :=
  "Trample\nStoried (If you control three or more artifacts, legendaries, and/or Sagas, you have an enduring story for the rest of the game.)\nAs long as you have an enduring story, artifacts and creatures you control have ward {1}."

def thorinOakenshieldDefinition : TraditionalCardDefinition := .card <|
  [
    .name "Thorin Oakenshield",
    .manaCost [.mono .red, .mono .white],
    .type .creature,
    .supertype .legendary,
    .subtype .dwarf,
    .subtype .noble,
    .power 3,
    .toughness 2
  ] ++ (parseOracleParts (name := "Thorin Oakenshield") thorinOakenshieldOracle).get!

def thorinOakenshield : CardDef :=
  thorinOakenshieldDefinition.toCardDef
    (oracleText := thorinOakenshieldOracle)

#guard thorinOakenshieldDefinition == .card [
  .name "Thorin Oakenshield",
  .manaCost [.mono .red, .mono .white],
  .type .creature,
  .supertype .legendary,
  .subtype .dwarf,
  .subtype .noble,
  .power 3,
  .toughness 2,
  .ability (.keyword .trample),
  .ability (.keyword .storied),
  .ability (.static (.if (.enduringStory (.controller .this))
    [.gainAbility
      (.intersection [
        .permanent,
        .union [.cardType .artifact, .cardType .creature],
        .controlled (.controller .this)])
      (.keywordWithCost .ward [.mana [.generic 1]])]))]

#guard thorinOakenshield.keywords.trample
#guard thorinOakenshield.keywords.storied
#guard thorinOakenshield.staticAbilities ==
  #[.artifactsAndCreaturesHaveWardIfEnduringStory 1]
#guard thorinOakenshield.oracleText == thorinOakenshieldOracle

/-- Gatherer Oracle text for Dáin, Lord of the Iron Hills. -/
def dainLordOfTheIronHillsOracle : String :=
  "Vigilance\nStoried (If you control three or more artifacts, legendaries, and/or Sagas, you have an enduring story for the rest of the game.)\nAs long as you have an enduring story, creatures can't attack you unless their controller pays {1} for each of those creatures."

def dainLordOfTheIronHillsDefinition : TraditionalCardDefinition := .card <|
  [
    .name "Dáin, Lord of the Iron Hills",
    .manaCost [.generic 1, .mono .white],
    .type .creature,
    .supertype .legendary,
    .subtype .dwarf,
    .subtype .noble,
    .power 2,
    .toughness 2
  ] ++ (parseOracleParts (name := "Dáin, Lord of the Iron Hills") dainLordOfTheIronHillsOracle).get!

def dainLordOfTheIronHills : CardDef :=
  dainLordOfTheIronHillsDefinition.toCardDef
    (oracleText := dainLordOfTheIronHillsOracle)

#guard dainLordOfTheIronHillsDefinition == .card [
  .name "Dáin, Lord of the Iron Hills",
  .manaCost [.generic 1, .mono .white],
  .type .creature,
  .supertype .legendary,
  .subtype .dwarf,
  .subtype .noble,
  .power 2,
  .toughness 2,
  .ability (.keyword .vigilance),
  .ability (.keyword .storied),
  .ability (.static (.if (.enduringStory (.controller .this))
    [.cantAttackUnlessPays
      (.intersection [.permanent, .cardType .creature])
      (.controller .this)
      [.mana [.generic 1]]]))]

#guard dainLordOfTheIronHills.keywords.vigilance
#guard dainLordOfTheIronHills.keywords.storied
#guard dainLordOfTheIronHills.staticAbilities ==
  #[.creaturesCantAttackYouUnlessPayIfEnduringStory 1]
#guard dainLordOfTheIronHills.oracleText == dainLordOfTheIronHillsOracle

/-- Gatherer Oracle text for Old Thrush. -/
def oldThrushOracle : String :=
  "Flying\nWhen this creature enters, you gain 2 life. You may search your library for a basic land card, reveal it, then shuffle and put that card on top."

def oldThrushDefinition : TraditionalCardDefinition := .card <|
  [
    .name "Old Thrush",
    .manaCost [.generic 2],
    .type .creature,
    .subtype .bird,
    .power 1,
    .toughness 2
  ] ++ (parseOracleParts (name := "Old Thrush") oldThrushOracle).get!

def oldThrush : CardDef :=
  oldThrushDefinition.toCardDef
    (oracleText := oldThrushOracle)

#guard oldThrushDefinition == .card [
  .name "Old Thrush",
  .manaCost [.generic 2],
  .type .creature,
  .subtype .bird,
  .power 1,
  .toughness 2,
  .ability (.keyword .flying),
  .ability (.triggered (.enter .this)
    (.sequence [
      .gainLife (.controller .this) 2,
      .optional
        (.sequence [
          .searchLibraryThenShuffle (.controller .this) [
            .defineSelectorVariable 1
              (.selected (.controller .this) (.range 1 1)
                (.intersection [.inLibrary, .cardType .land, .supertype .basic])),
            .reveal (.variable 1),
            .holdOutInLibrary (.variable 1)],
          .putOnTopOfLibrary (.variable 1)])]))]

#guard oldThrush.keywords.flying
#guard oldThrush.triggeredAbilities == #[.onEnterGainLifeSearchBasicOnTop 2]
#guard oldThrush.oracleText == oldThrushOracle

/-- Gatherer Oracle text for Most Decrepit Old Bird. -/
def mostDecrepitOldBirdOracle : String :=
  "Flying\nThreshold — This creature gets +1/+1 as long as there are seven or more cards in your graveyard.\n//ADV//\nSpeak Secrets {1}{U}\nSorcery — Adventure\nMill four cards, then put an instant or sorcery card from among them into your hand."

def mostDecrepitOldBirdDefinition : TraditionalCardDefinition := .card <|
  [
    .name "Most Decrepit Old Bird",
    .manaCost [.mono .blue],
    .type .creature,
    .subtype .bird,
    .power 1,
    .toughness 1
  ] ++ (parseOracleParts (name := "Most Decrepit Old Bird") mostDecrepitOldBirdOracle).get!

def mostDecrepitOldBird : CardDef :=
  mostDecrepitOldBirdDefinition.toCardDef
    (oracleText := mostDecrepitOldBirdOracle)

#guard mostDecrepitOldBirdDefinition == .card [
  .name "Most Decrepit Old Bird",
  .manaCost [.mono .blue],
  .type .creature,
  .subtype .bird,
  .power 1,
  .toughness 1,
  .ability (.keyword .flying),
  .ability (.static (.if
    (.greaterOrEqual
      (.count (.intersection [.inGraveyard, .owner (.controller .this)]))
      7)
    [.addPower .this (Value.int 1), .addToughness .this (Value.int 1)])),
  .alternative [
    .name "Speak Secrets",
    .manaCost [.generic 1, .mono .blue],
    .type .sorcery,
    .subtype .adventure,
    .actions [.sequence [
      .actionId 1 (.mill (.controller .this) 4),
      .returnToHand
        (.selected (.controller .this) (.range 1 1)
          (.intersection [
            .wasObjectOfAction 1,
            .union [.cardType .instant, .cardType .sorcery]]))]]]]

#guard mostDecrepitOldBird.keywords.flying
#guard mostDecrepitOldBird.staticAbilities == #[.thresholdGets 1 1]
#guard mostDecrepitOldBird.oracleText == mostDecrepitOldBirdOracle
#guard
  match mostDecrepitOldBird.adventure with
  | some adv =>
    adv.name == "Speak Secrets" &&
      adv.manaCost == (ManaCost.ofGenericAndColor 1 .blue) &&
      adv.types == #[.sorcery] &&
      adv.spellEffect == some (Effect.millThenPutInstantOrSorcery 4)
  | none => false

/-- Gatherer Oracle text for Lake-town Mariners. -/
def lakeTownMarinersOracle : String :=
  "Vigilance\nWard {2} (Whenever this creature becomes the target of a spell or ability an opponent controls, counter it unless that player pays {2}.)\n//ADV//\nGone Fishing {3}{U}\nInstant — Adventure\nExile two target creatures and/or lands you control, then return them to the battlefield under their owner's control."

def lakeTownMarinersDefinition : TraditionalCardDefinition := .card <|
  [
    .name "Lake-town Mariners",
    .manaCost [.generic 4, .mono .blue, .mono .blue],
    .type .creature,
    .subtype .human,
    .subtype .citizen,
    .power 6,
    .toughness 5
  ] ++ (parseOracleParts (name := "Lake-town Mariners") lakeTownMarinersOracle).get!

def lakeTownMariners : CardDef :=
  lakeTownMarinersDefinition.toCardDef
    (oracleText := lakeTownMarinersOracle)

#guard lakeTownMarinersDefinition == .card [
  .name "Lake-town Mariners",
  .manaCost [.generic 4, .mono .blue, .mono .blue],
  .type .creature,
  .subtype .human,
  .subtype .citizen,
  .power 6,
  .toughness 5,
  .ability (.keyword .vigilance),
  .ability (.keywordWithCost .ward [.mana [.generic 2]]),
  .alternative [
    .name "Gone Fishing",
    .manaCost [.generic 3, .mono .blue],
    .type .instant,
    .subtype .adventure,
    .actions [.sequence [
      .actionId 1 (.exile (.targets 1 (.range 2 2)
        (.intersection [
          .permanent,
          .union [.cardType .creature, .cardType .land],
          .controlled (.controller .this)]))),
      .putOntoBattlefieldInState (.wasCreatedByAction 1)
        [.controlled (.owner (.wasCreatedByAction 1))]]]]]

#guard lakeTownMariners.keywords.vigilance
#guard lakeTownMariners.ward == some 2
#guard lakeTownMariners.oracleText == lakeTownMarinersOracle
#guard
  match lakeTownMariners.adventure with
  | some adv =>
    adv.name == "Gone Fishing" &&
      adv.manaCost == (ManaCost.ofGenericAndColor 3 .blue) &&
      adv.types == #[.instant] &&
      adv.spellEffect == some Effect.exileThenReturnYouControl
  | none => false

/-- Gatherer Oracle text for Pinecone Strike. -/
def pineconeStrikeOracle : String :=
  "Choose one or both —\n• Pinecone Strike deals 3 damage to target creature. If that creature would die this turn, exile it instead.\n• Destroy target artifact token."

def pineconeStrikeDefinition : TraditionalCardDefinition := .card <|
  [
    .name "Pinecone Strike",
    .manaCost [.generic 1, .mono .red],
    .type .instant
  ] ++ (parseOracleParts (name := "Pinecone Strike") pineconeStrikeOracle).get!

#guard pineconeStrikeDefinition == .card [
  .name "Pinecone Strike",
  .manaCost [.generic 1, .mono .red],
  .type .instant,
  .actions [.chooseUniqueModes (.range 1 2) [
    .sequence [
      .dealDamage .this
        (.target 1 (.intersection [.permanent, .cardType .creature])) 3,
      .continuous
        [.replace (.putToGraveyard (.targetReference 1)) [.exile .replacingObject]]
        .endOfTurn],
    .destroy (.target 2
      (.intersection [.permanent, .cardType .artifact, .token]))]]]

def pineconeStrike : CardDef :=
  pineconeStrikeDefinition.toCardDef (oracleText := pineconeStrikeOracle)

#guard pineconeStrike.chooseOneOrBoth
#guard pineconeStrike.spellEffect.isNone
#guard pineconeStrike.spellModes ==
  #[Effect.dealDamageToCreatureExileIfDies 3, Effect.destroyArtifactToken]

/-- Gatherer Oracle text for The Lonely Mountain. -/
def theLonelyMountainOracle : String :=
  "({T}: Add {R}.)\nThis land enters tapped unless you control an Equipment.\n{4}{R}, {T}: Create a 2/2 red Dwarf creature token. This ability costs {1} less to activate for each Equipment you control. Activate only as a sorcery."

def theLonelyMountainDefinition : TraditionalCardDefinition := .card <|
  [
    .name "The Lonely Mountain",
    .type .land,
    .subtype .mountain
  ] ++ (parseOracleParts (name := "The Lonely Mountain") theLonelyMountainOracle).get!

#guard theLonelyMountainDefinition == .card [
  .name "The Lonely Mountain",
  .type .land,
  .subtype .mountain,
  .ability (.everywhereStatic (.if
    (.not (.any (.intersection [
      .permanent, .subtype .equipment, .controlled (.controller .this)])))
    [.replace (.enter .this)
      [.putOntoBattlefieldInState .this [.tapped]]])),
  .ability (.activatedWithStaticIf
    (.timeToCastSorcery (.controller .this))
    [.mana [.generic 4, .mono .red], .tapSymbol]
    (.createTokens (.controller .this) 1 [
      .type .creature, .subtype .dwarf, .colorIndicator [.red],
      .power 2, .toughness 2])
    (.reduceCostWithX .this
      [.mana [.generic 1]]
      (.count (.intersection [
        .permanent, .subtype .equipment, .controlled (.controller .this)]))))]

def theLonelyMountain : CardDef :=
  theLonelyMountainDefinition.toCardDef (oracleText := theLonelyMountainOracle)

#guard theLonelyMountain.hasSubtype "Mountain"
#guard theLonelyMountain.basicLandMana == #[.red]
#guard theLonelyMountain.entersTappedUnlessEquipment
#guard theLonelyMountain.activatedAbilities.size == 1
#guard theLonelyMountain.activatedAbilities[0]!.onlyAsSorcery
#guard theLonelyMountain.activatedAbilities[0]!.cost.tap
#guard theLonelyMountain.activatedAbilities[0]!.costReductionPerEquipment == 1
#guard theLonelyMountain.activatedAbilities[0]!.effect ==
  Effect.abilityCreateTokens .dwarf 1

/-- Gatherer Oracle text for Thranduil, Sindarin Liege // Silvan Rally. -/
def thranduilSindarinLiegeOracle : String :=
  "Other Elves you control get +1/+1.\nLandfall — Whenever a land you control enters, create a 1/1 green Elf creature token.\n//ADV//\nSilvan Rally {1}{G/U}{G/U}\nSorcery — Adventure\nMill four cards, then put up to two land cards from among them into your hand. (Then exile this card. You may cast the creature later from exile.)"

def thranduilSindarinLiegeDefinition : TraditionalCardDefinition := .card <|
  [
    .name "Thranduil, Sindarin Liege",
    .manaCost [.generic 2, .hybrid .green .blue, .hybrid .green .blue],
    .type .creature,
    .supertype .legendary,
    .subtype .elf,
    .subtype .noble,
    .power 2,
    .toughness 3
  ] ++ (parseOracleParts (name := "Thranduil, Sindarin Liege") thranduilSindarinLiegeOracle).get!

#guard thranduilSindarinLiegeDefinition == .card [
  .name "Thranduil, Sindarin Liege",
  .manaCost [.generic 2, .hybrid .green .blue, .hybrid .green .blue],
  .type .creature,
  .supertype .legendary,
  .subtype .elf,
  .subtype .noble,
  .power 2,
  .toughness 3,
  .ability (.static (.addPower
    (.intersection [
      .not .this, .permanent, .cardType .creature, .subtype .elf,
      .controlled (.controller .this)])
    (Value.int 1))),
  .ability (.static (.addToughness
    (.intersection [
      .not .this, .permanent, .cardType .creature, .subtype .elf,
      .controlled (.controller .this)])
    (Value.int 1))),
  .ability (.triggered
    (.enter (.intersection [
      .permanent, .cardType .land, .controlled (.controller .this)]))
    (.createTokens (.controller .this) 1 [
      .type .creature, .subtype .elf, .colorIndicator [.green],
      .power 1, .toughness 1])),
  .alternative [
    .name "Silvan Rally",
    .manaCost [.generic 1, .hybrid .green .blue, .hybrid .green .blue],
    .type .sorcery,
    .subtype .adventure,
    .actions [.sequence [
      .actionId 1 (.mill (.controller .this) 4),
      .returnToHand
        (.selected (.controller .this) (.range 0 2)
          (.intersection [.wasObjectOfAction 1, .cardType .land]))]]]]

def thranduilSindarinLiege : CardDef :=
  thranduilSindarinLiegeDefinition.toCardDef
    (oracleText := thranduilSindarinLiegeOracle)

/-- Gatherer Oracle text for Glóin the Mighty // Easy Pickings. -/
def gloinTheMightyOracle : String :=
  "At the beginning of your first main phase, add {R}{R}.\n//ADV//\nEasy Pickings {2}{R}\nSorcery — Adventure\nEasy Pickings deals 1 damage to each creature your opponents control. (Then exile this card. You may cast the creature later from exile.)"

def gloinTheMightyDefinition : TraditionalCardDefinition := .card <|
  [
    .name "Glóin the Mighty",
    .manaCost [.generic 3, .mono .red],
    .type .creature,
    .supertype .legendary,
    .subtype .dwarf,
    .subtype .warrior,
    .power 4,
    .toughness 3
  ] ++ (parseOracleParts (name := "Glóin the Mighty") gloinTheMightyOracle).get!

#guard gloinTheMightyDefinition == .card [
  .name "Glóin the Mighty",
  .manaCost [.generic 3, .mono .red],
  .type .creature,
  .supertype .legendary,
  .subtype .dwarf,
  .subtype .warrior,
  .power 4,
  .toughness 3,
  .ability (.triggered
    (.precombatMainPhase (.controller .this))
    (.addMana (.controller .this) [.colored .red, .colored .red])),
  .alternative [
    .name "Easy Pickings",
    .manaCost [.generic 2, .mono .red],
    .type .sorcery,
    .subtype .adventure,
    .actions [.dealDamage .this
      (.intersection [
        .permanent, .cardType .creature,
        .controlled (.opponent (.controller .this))])
      1]]]

def gloinTheMighty : CardDef :=
  gloinTheMightyDefinition.toCardDef (oracleText := gloinTheMightyOracle)

#guard gloinTheMighty.triggeredAbilities ==
  #[.onYourFirstMainAddMana #[.colored .red, .colored .red]]
#guard
  match gloinTheMighty.adventure with
  | some adv =>
    adv.name == "Easy Pickings" &&
      adv.spellEffect == some (Effect.dealDamageToEachOppCreature 1)
  | none => false

/-- Gatherer Oracle text for Iron Hills Stalwart. -/
def ironHillsStalwartOracle : String :=
  "Reach, trample\nWhen this creature enters, attach target Equipment you control to up to one target creature you control."

def ironHillsStalwartDefinition : TraditionalCardDefinition := .card <|
  [
    .name "Iron Hills Stalwart",
    .manaCost [.generic 4, .mono .red],
    .type .creature,
    .subtype .dwarf,
    .subtype .warrior,
    .power 4,
    .toughness 5
  ] ++ (parseOracleParts (name := "Iron Hills Stalwart") ironHillsStalwartOracle).get!

#guard ironHillsStalwartDefinition == .card [
  .name "Iron Hills Stalwart",
  .manaCost [.generic 4, .mono .red],
  .type .creature,
  .subtype .dwarf,
  .subtype .warrior,
  .power 4,
  .toughness 5,
  .ability (.keyword .reach),
  .ability (.keyword .trample),
  .ability (.triggered
    (.enter .this)
    (.attach
      (.target 1 (.intersection [
        .permanent, .subtype .equipment, .controlled (.controller .this)]))
      (.targets 2 (.range 0 1)
        (.intersection [
          .permanent, .cardType .creature, .controlled (.controller .this)]))))]

def ironHillsStalwart : CardDef :=
  ironHillsStalwartDefinition.toCardDef (oracleText := ironHillsStalwartOracle)

/-- Gatherer Oracle text for Old Fat Spider. -/
def oldFatSpiderOracle : String :=
  "Reach\nThis creature can't be blocked by creatures with power 2 or less.\nWhenever this creature becomes the target of a spell or ability an opponent controls, draw a card."

def oldFatSpiderDefinition : TraditionalCardDefinition := .card <|
  [
    .name "Old Fat Spider",
    .manaCost [.generic 4, .mono .green, .mono .green],
    .type .creature,
    .subtype .spider,
    .power 6,
    .toughness 7
  ] ++ (parseOracleParts (name := "Old Fat Spider") oldFatSpiderOracle).get!

#guard oldFatSpiderDefinition == .card [
  .name "Old Fat Spider",
  .manaCost [.generic 4, .mono .green, .mono .green],
  .type .creature,
  .subtype .spider,
  .power 6,
  .toughness 7,
  .ability (.keyword .reach),
  .ability (.static (.forbid (.block
    (.intersection [
      .permanent, .cardType .creature, .powerAtMost (Value.int 2)])
    .this))),
  .ability (.triggered
    (.target
      (.intersection [
        .union [.spell, .ability],
        .controlled (.opponent (.controller .this))])
      .this)
    (.draw (.controller .this) 1))]

def oldFatSpider : CardDef :=
  oldFatSpiderDefinition.toCardDef (oracleText := oldFatSpiderOracle)

#guard oldFatSpider.keywords.reach
#guard oldFatSpider.staticAbilities == #[.cantBeBlockedByPowerAtMost 2]
#guard oldFatSpider.triggeredAbilities == #[.onBecomesTargetDraw]

/-- Gatherer Oracle text for Great Gilded Boat. -/
def greatGildedBoatOracle : String :=
  "Whenever you attack, recruit. (Draw a card, then discard a card. If you discarded a nonland card, create a 1/1 white Human Soldier creature token.)\nCrew 2 (Tap any number of creatures you control with total power 2 or more: This Vehicle becomes an artifact creature until end of turn.)"

def greatGildedBoatDefinition : TraditionalCardDefinition := .card <|
  [
    .name "Great Gilded Boat",
    .manaCost [.generic 2, .mono .blue],
    .type .artifact,
    .subtype .vehicle,
    .power 4,
    .toughness 4
  ] ++ (parseOracleParts (name := "Great Gilded Boat") greatGildedBoatOracle).get!

#guard greatGildedBoatDefinition == .card [
  .name "Great Gilded Boat",
  .manaCost [.generic 2, .mono .blue],
  .type .artifact,
  .subtype .vehicle,
  .power 4,
  .toughness 4,
  .ability (.triggered
    (.attackSimultaneously
      (.intersection [
        .permanent, .cardType .creature, .controlled (.controller .this)])
      .all
      [])
    (.keyword (.controller .this) .recruit)),
  .ability (.keyword (.crew 2))]

def greatGildedBoat : CardDef :=
  greatGildedBoatDefinition.toCardDef (oracleText := greatGildedBoatOracle)

#guard greatGildedBoat.triggeredAbilities == #[.onYouAttackRecruit]
#guard greatGildedBoat.crew == some 2

/-- Gatherer Oracle text for Desolation of Smaug. -/
def desolationOfSmaugOracle : String :=
  "Desolation of Smaug deals 3 damage to each non-Dragon creature.\nAdd four mana in any combination of colors. Spend this mana only to cast Dragon spells."

def desolationOfSmaugDefinition : TraditionalCardDefinition := .card <|
  [
    .name "Desolation of Smaug",
    .manaCost [.generic 2, .mono .red, .mono .red],
    .type .sorcery
  ] ++ (parseOracleParts (name := "Desolation of Smaug") desolationOfSmaugOracle).get!

#guard desolationOfSmaugDefinition == .card [
  .name "Desolation of Smaug",
  .manaCost [.generic 2, .mono .red, .mono .red],
  .type .sorcery,
  .actions [
    .dealDamage .this
      (.intersection [
        .permanent, .cardType .creature, .not (.subtype .dragon)])
      3,
    .actionId 1 (.addManaInAnyCombination
      (.controller .this) ManaSymbol.anyColor 4),
    .continuous
      [.forbid (.spendManaCreatedByAction 1 (.not (.castSpell (.subtype .dragon))))]
      .endOfTurn]]

def desolationOfSmaug : CardDef :=
  desolationOfSmaugDefinition.toCardDef (oracleText := desolationOfSmaugOracle)

#guard desolationOfSmaug.spellEffect ==
  some (Effect.dealDamageToEachNonDragonThenAddDragonMana 3)

def dwarvenMauler : CardDef :=
  (TraditionalCardDefinition.card [
    .name "Dwarven Mauler",
    .manaCost [.mono .red],
    .type .creature,
    .subtype .dwarf,
    .subtype .warrior,
    .power 2,
    .toughness 1,
    .ability
      (.static
        (.reduceCost
          (.intersection [
            Selector.keywordAbility .equip,
            .hasTarget .this,
            .controlled (.controller .this)])
          [.mana [.generic 2]]))
  ]).toCardDef
    (oracleText := "Equip abilities you activate that target this creature cost {2} less to activate.")

def myPrecious : CardDef :=
  artifact "My Precious" (ManaCost.ofGeneric 3)
    "Equipped creature has hexproof and can't be blocked.\nEquip—{2}, Pay 2 life.\n//ADV//\nAllure of Power {1}{B}\nInstant — Adventure\nAs an additional cost to cast this spell, sacrifice a creature.\nDraw two cards. (Then exile this card. You may cast the artifact later from exile.)"
    (subtypes := #["Equipment"])
    (supertypes := #[.legendary])
    (staticAbilities := #[.equippedCreatureHasKeywordsAndCantBeBlocked Keyword.hexproof])
    (activatedAbilities := #[
      activated (Effect.attachToTargetCreatureYouControl) (ManaCost.ofGeneric 2)
        (onlyAsSorcery := true) (payLife := 2)])
    (adventure := some (adventure "Allure of Power"
      (ManaCost.ofGenericAndColor 1 .black)
      "As an additional cost to cast this spell, sacrifice a creature.\nDraw two cards. (Then exile this card. You may cast the artifact later from exile.)"
      (Effect.draw 2) (cardType := .instant) (additionalCostSacrificeCreature := true)))

def troopOfPonies : CardDef :=
  (TraditionalCardDefinition.card [
    .name "Troop of Ponies",
    .manaCost [.generic 2],
    .type .creature,
    .subtype .horse,
    .power 2,
    .toughness 1,
    .ability
      (.activated
        [.mana [.generic 2], .tapSymbol, .sacrifice .this]
        (.searchLibraryThenShuffle
          (.controller .this)
          [
            .defineSelectorVariable 1
              (.selected
                (.controller .this)
                (.range 0 2)
                (.intersection [
                  .inLibrary,
                  .cardType .land,
                  .supertype .basic])),
            .reveal (.variable 1),
            .putOntoBattlefieldInState
              (.selected (.controller .this) (.range 1 1) (.variable 1))
              [.tapped],
            .returnToHand (.variable 1)]))
  ]).toCardDef
    (oracleText := "{2}, {T}, Sacrifice this creature: Search your library for up to two basic land cards, reveal them, put one onto the battlefield tapped and the other into your hand, then shuffle.")

def elvenRaftSteerer : CardDef :=
  (TraditionalCardDefinition.card [
    .name "Elven Raft-Steerer",
    .manaCost [.generic 2, .mono .blue],
    .type .creature,
    .subtype .elf,
    .subtype .pilot,
    .power 3,
    .toughness 2,
    .ability (
      .triggered
        (.enter
          (.intersection [
            .permanent,
            .cardType .land,
            .controlled (.controller .this)]))
        (.chooseUniqueModes (.range 1 1) [
          .tap
            (.target
              1
              (.intersection [
                .permanent,
                .cardType .creature,
                .controlled (.opponent (.controller .this))])),
          .untap
            (.target
              2
              (.intersection [
                .permanent,
                .cardType .creature,
                .controlled (.controller .this)]))]))
  ]).toCardDef
    (oracleText := "Landfall — Whenever a land you control enters, choose one —\n• Tap target creature an opponent controls.\n• Untap target creature you control.")

def mirkwoodMeditator : CardDef :=
  creature "Mirkwood Meditator" (ManaCost.ofGenericAndColor 2 .blue)
    #["Elf", "Druid"] 2 4
    (oracleText := "Landfall — Whenever a land you control enters, you may have this creature's base power and toughness become 4/2 until end of turn.")
    (triggeredAbilities := #[.onLandYouControlEntersBecomePT 4 2])

def mirkwoodNurturer : CardDef :=
  (TraditionalCardDefinition.card [
    .name "Mirkwood Nurturer",
    .manaCost [.generic 2, .hybrid .green .blue],
    .type .creature,
    .subtype .elf,
    .subtype .ranger,
    .power 3,
    .toughness 2,
    .ability (
      .triggered
        (.enter .this)
        (.sequence [
          .actionId 1
            (.returnToHand
              (.targets
                1
                (.range 0 1)
                (.intersection [
                  .not .this,
                  .permanent,
                  .controlled (.controller .this)]))),
          .if
            (.happened (.actionWithId 1) .gameStart)
            [.putCounter (.source .this) .plusOnePlusOne 1]]))
  ]).toCardDef
    (oracleText := "When this creature enters, return up to one other target permanent you control to its owner's hand. If you do, put a +1/+1 counter on this creature.")

def kiliTheResourceful : CardDef :=
  legendaryCreature "Kíli the Resourceful" (ManaCost.ofGenericAndColor 1 .white)
    #["Dwarf", "Scout"] 1 2
    (oracleText := "Storied (If you control three or more artifacts, legendaries, and/or Sagas, you have an enduring story for the rest of the game.)\nAs long as you have an enduring story, you may pay {0} rather than pay the equip cost of the first equip ability you activate each turn.\nWhenever another Dwarf or Equipment you control enters, draw a card. This ability triggers only once each turn.")
    (keywords := Keyword.storied)
    (staticAbilities := #[.firstEquipFreeIfEnduringStory])
    (triggeredAbilities := #[.onAnotherSubtypeOrEquipmentEntersDrawOnce "Dwarf"])

def dainsCompany : CardDef :=
  creature "Dáin's Company" (ManaCost.ofColors [.red, .white]) #["Dwarf", "Warrior"] 2 2
    (oracleText := "This creature has lifelink as long as you control another Dwarf.\nWhen this creature enters, look at the top four cards of your library. You may reveal a Dwarf or Equipment card from among them and put it into your hand. Put the rest on the bottom of your library in a random order.")
    (staticAbilities := #[.lifelinkIfYouControlOtherSubtype "Dwarf"])
    (triggeredAbilities := #[.onEnterLookAtTopRevealTypes 4 #["Dwarf", "Equipment"]])

def smaugWickedWorm : CardDef :=
  legendaryCreature "Smaug, Wicked Worm" (ManaCost.ofGenericAndColors 3 [.black, .red])
    #["Dragon"] 5 5
    (oracleText := "Flying\nWhen Smaug enters, create X tapped Treasure tokens, where X is the number of artifacts your opponents control.\nWhenever you cast a spell, if mana from a Treasure was spent to cast it, you draw a card and lose 1 life.")
    (keywords := Keyword.flying)
    (triggeredAbilities := #[
      .onEnterCreateTappedTreasuresEqualOppArtifacts,
      .onCastWithTreasureDrawLoseLife])

def glamdringFoeHammer : CardDef :=
  equipment "Glamdring, Foe-hammer" (ManaCost.ofGeneric 2)
    "Instant and sorcery spells you cast cost {X} less to cast, where X is equipped creature's power.\nEquip {2}\n//ADV//\nGleam of Death {3}{U}\nSorcery — Adventure\nMill six cards, then put all instant and sorcery cards from among them into your hand. (Then exile this card. You may cast the artifact later from exile.)"
    (ManaCost.ofGeneric 2)
    (legendary := true)
    (staticAbilities := #[.instantSorceryCostReductionEqualEquippedPower])
    (adventure := some (adventure "Gleam of Death" (ManaCost.ofGenericAndColor 3 .blue)
      "Mill six cards, then put all instant and sorcery cards from among them into your hand. (Then exile this card. You may cast the artifact later from exile.)"
      (Effect.millThenPutAllInstantsOrSorceries 6)))

def settleTheWreckage : CardDef :=
  instant "Settle the Wreckage" (ManaCost.ofGenericAndColors 2 [.white, .white])
    "Exile all attacking creatures target player controls. That player may search their library for that many basic land cards, put those cards onto the battlefield tapped, then shuffle."
    (some (Effect.exileAttackersSearchBasics))

def ironHillsBlacksmith : CardDef :=
  creature "Iron Hills Blacksmith" (ManaCost.ofGenericAndColor 1 .white)
    #["Dwarf", "Artificer"] 1 1
    (oracleText := "Double strike\nWhen this creature enters, create a colorless Equipment artifact token named Axe with \"Equipped creature gets +1/+0\" and equip {2}.")
    (keywords := Keyword.doubleStrike)
    (triggeredAbilities := #[.onEnterCreateAxe])

def gandalfGoblinsBane : CardDef :=
  legendaryCreature "Gandalf, Goblins' Bane" (ManaCost.ofGenericAndColor 2 .red)
    #["Avatar", "Wizard"] 2 3
    (oracleText := "Whenever you cast a noncreature spell, Gandalf gets +1/+1 until end of turn and deals 1 damage to each opponent.\n//ADV//\nFlameshape {1}{R}\nSorcery — Adventure\nLook at the top two cards of your library and exile them face down. For as long as they remain exiled, you may play them if you control a Wizard. (Then exile this card. You may cast the creature later from exile.)")
    (triggeredAbilities := #[.onCastNoncreaturePumpAndDamageOpponents 1])
    (adventure := some (adventure "Flameshape" (ManaCost.ofGenericAndColor 1 .red)
      "Look at the top two cards of your library and exile them face down. For as long as they remain exiled, you may play them if you control a Wizard. (Then exile this card. You may cast the creature later from exile.)"
      (Effect.exileTopPlayIfYouControlSubtype 2 "Wizard")))

def anUnexpectedParty : CardDef :=
  enchantment "An Unexpected Party" (ManaCost.ofGenericAndColors 2 [.white, .white])
    "As this enchantment enters, choose a creature type.\nCreatures you control of the chosen type get +2/+2.\n//ADV//\nAt the Door {X}{2}{W}\nSorcery — Adventure\nCreate X 2/2 red Dwarf creature tokens. (Then exile this card. You may cast the enchantment later from exile.)"
    (asEntersChooseCreatureType := true)
    (staticAbilities := #[.chosenTypeCreaturesGet 2 2])
    (adventure := some (adventure "At the Door"
      { symbols := #[.x, .generic 2, .colored .white] }
      "Create X 2/2 red Dwarf creature tokens. (Then exile this card. You may cast the enchantment later from exile.)"
      (Effect.createTokensX .dwarf)))

def alongTheCrookedWay : CardDef :=
  (TraditionalCardDefinition.card [
    .name "Along the Crooked Way",
    .manaCost [.generic 2, .mono .black],
    .type .enchantment,
    .ability (
      .triggered
        (.enter .this)
        (.returnToHand
          (.target
            1
            (.intersection [
              .inGraveyard,
              .cardType .creature,
              .owner (.controller .this)])))),
    .ability (
      .triggered
        (.leaveGraveyard
          (.intersection [
            .inGraveyard,
            .cardType .creature,
            .owner (.controller .this)]))
        (.keyword (.controller .this) (.amass .goblin (.nat 1)))),
    .ability (
      .activated
        [.mana [.generic 1, .mono .black]]
        (.continuous
          [.gainAbility
            (.intersection [
              .permanent,
              .union [.subtype .goblin, .subtype .orc],
              .controlled (.controller .this)])
            (.keyword .menace)]
          .endOfTurn))
  ]).toCardDef
    (oracleText := "When this enchantment enters, return target creature card from your graveyard to your hand.\nWhenever a creature card leaves your graveyard, amass Goblins 1.\n{1}{B}: Goblins and Orcs you control gain menace until end of turn.")

def azogMoriaSRuin : CardDef :=
  legendaryCreature "Azog, Moria's Ruin" (ManaCost.ofGenericAndColor 2 .black) #["Goblin", "Soldier"] 1 3 (oracleText := "When Azog enters, destroy up to one other target creature. Its controller amasses Goblins X, where X is that creature's power. If you controlled that creature, draw a card. (To amass Goblins X, that player puts X +1/+1 counters on an Army they control. It's also a Goblin. If they don't control an Army, they create a 0/0 black Goblin Army creature token first.)")
    (triggeredAbilities := #[.onEnterDestroyOtherAmassControllerPower])

def balinLoremaster : CardDef :=
  legendaryCreature "Balin, Loremaster" (ManaCost.ofGenericAndColors 3 [.red, .red]) #["Dwarf", "Bard"] 4 4 (oracleText := "Storied (If you control three or more artifacts, legendaries, and/or Sagas, you have an enduring story for the rest of the game.)\nWhenever Balin or another Dwarf you control enters, you may discard your hand. Draw X cards, where X is the number of cards discarded this way. If you have an enduring story, Balin deals X damage to each opponent.")
    (keywords := Keyword.storied)
    (triggeredAbilities := #[.onThisOrAnotherSubtypeEntersDiscardHand "Dwarf"])

def bardTheBowman : CardDef :=
  (TraditionalCardDefinition.card [
    .name "Bard the Bowman",
    .manaCost [.generic 1, .mono .white, .mono .blue],
    .type .creature,
    .supertype .legendary,
    .subtype .human,
    .subtype .archer,
    .power 1,
    .toughness 3,
    .ability (.keyword .reach),
    .ability (
      .triggered
        (.ordinal 2 .turnStart (.draw (.controller .this) .all))
        (.sequence [
          .putCounter
            (.target 1 (.intersection [.permanent, .cardType .creature]))
            .plusOnePlusOne
            1,
          .continuous
            [.gainAbility (.targetReference 1) (.keyword .lifelink)]
            .endOfTurn]))
  ]).toCardDef
    (oracleText := "Reach\nWhenever you draw your second card each turn, put a +1/+1 counter on target creature. It gains lifelink until end of turn.")

def bardKingOfDale : CardDef :=
  legendaryCreature "Bard, King of Dale" (ManaCost.ofGenericAndColors 4 [.white, .blue]) #["Human", "Noble", "Archer"] 3 5 (oracleText := "Reach, vigilance\nIf you would draw a card except the first one you draw in each of your draw steps, draw two cards instead.\nIf one or more tokens would be created under your control, twice that many of those tokens are created instead.")
    (keywords := Keyword.reach.merge Keyword.vigilance)
    (tokenDoubling := true)
    (drawTwoExceptFirstDrawStep := true)

def bejeweledWarg : CardDef :=
  (TraditionalCardDefinition.card [
    .name "Bejeweled Warg",
    .manaCost [.generic 1, .mono .green],
    .type .creature,
    .subtype .wolf,
    .power 3,
    .toughness 2,
    .ability (.keyword .trample),
    .ability (
      .triggered
        (.combatDamage .this .player)
        (.chooseUniqueModes (.range 1 1) [
          .putCounter
            (.target
              1
              (.intersection [
                .permanent,
                .cardType .creature,
                .subtype .wolf,
                .controlled (.controller .this)]))
            .plusOnePlusOne 1,
          .createTokens (.controller .this) 1 PredefinedToken.treasureToken]))
  ]).toCardDef
    (oracleText := "Trample\nWhenever this creature deals combat damage to a player, choose one —\n• Put a +1/+1 counter on target Wolf you control.\n• Create a Treasure token. (It's an artifact with \"{T}, Sacrifice this token: Add one mana of any color.\")")

def belladonnaTook : CardDef :=
  legendaryCreature "Belladonna Took" (ManaCost.ofGenericAndColor 1 .white) #["Halfling", "Citizen"] 2 2 (oracleText := "Whenever a token you control enters, you gain 1 life if this is the first time this ability has resolved this turn. If it's the second time, draw a card. If it's the third time, put a +1/+1 counter on each creature you control.")
    (triggeredAbilities := #[.onTokenYouControlEntersBelladonna])

def beornTheFierce : CardDef :=
  legendaryCreature "Beorn the Fierce" (ManaCost.ofGenericAndColors 3 [.green, .green]) #["Bear", "Shapeshifter", "Warrior"] 6 6 (oracleText := "Trample\nOther Bears you control get +2/+2.\nAt the beginning of combat on your turn, put a trample counter on up to one target creature you control. It becomes a Bear in addition to its other types. Then if you control three or more Bears, draw two cards.")
    (keywords := Keyword.trample)
    (staticAbilities := #[.otherCreaturesGet #["Bear"] 2 2])
    (triggeredAbilities := #[.onYourBeginCombatTrampleCounterBecomeBear])

def bifurMelodicRider : CardDef :=
  legendaryCreature "Bifur, Melodic Rider" (ManaCost.ofGenericAndHybrids 4 .red .white 2) #["Dwarf", "Bard"] 4 5 (oracleText := "Storied (If you control three or more artifacts, legendaries, and/or Sagas, you have an enduring story for the rest of the game.)\nWhenever Bifur enters or attacks, put a +1/+1 counter on target creature.\nAs long as you have an enduring story, if a triggered ability of a Dwarf you control triggers, that ability triggers an additional time.")
    (keywords := Keyword.storied)
    (staticAbilities := #[.extraTriggerIfEnduringStorySubtype "Dwarf"])
    (triggeredAbilities := #[.onEnterOrAttackPlusOneOnCreature])

def bilboSGambit : CardDef :=
  instant "Bilbo's Gambit" (ManaCost.ofGenericAndColor 1 .white) "Gift a Treasure (You may promise an opponent a gift as you cast this spell. If you do, they create a Treasure token before its other effects. It's an artifact with \"{T}, Sacrifice this token: Add one mana of any color.\")\nReturn target spell to its owner's hand. If the gift was promised, players can't cast spells this turn." (some (Effect.returnSpellCantCastIfGift))
    (giftTreasure := true)

def bilboThiefInTheNight : CardDef :=
  let c :=
    legendaryCreature "Bilbo, Thief in the Night" (ManaCost.ofGenericAndColor 1 .blue) #["Halfling", "Rogue"] 2 2 (oracleText := "Spells you cast from anywhere other than your hand cost {1} less to cast.\nWhenever Bilbo attacks, you may cast an artifact, instant, or sorcery spell from your graveyard. If an instant or sorcery spell cast this way would be put into your graveyard, exile it instead.")
      (triggeredAbilities := #[.onAttackCastFromGyArtifactInstantSorcery])
  { c with costReductionNotFromHand := 1 }

def bolgOfTheNorth : CardDef :=
  legendaryCreature "Bolg of the North" (ManaCost.ofGenericAndColors 3 [.black, .red]) #["Goblin", "Soldier"] 5 5 (oracleText := "When Bolg enters, you may sacrifice another creature. When you do, Bolg deals damage equal to that creature's power to another target creature. If excess damage was dealt this way, amass Goblins X, where X is that excess damage. (Put X +1/+1 counters on an Army you control. It's also a Goblin. If you don't control an Army, create a 0/0 black Goblin Army creature token first.)")
    (triggeredAbilities := #[.onEnterBolgMaySacrifice])

def boughsideWanderers : CardDef :=
  creature "Boughside Wanderers" (ManaCost.ofGenericAndColors 4 [.green, .green]) #["Elf", "Scout"] 4 4 (oracleText := "When this creature enters, look at the top four cards of your library. You may reveal a permanent card from among them and put it into your hand. Put the rest on the bottom of your library in a random order.\nLandfall — Whenever a land you control enters, this creature gets +2/+2 until end of turn.")
    (triggeredAbilities := #[.onLandYouControlEntersGets 2 2,
      .onEnterLookAtTopRevealTypes 4 #["permanent"]])

def burnBurnTreeAndFern : CardDef :=
  saga "Burn, Burn, Tree and Fern" (ManaCost.ofGenericAndColor 3 .red) "(As this Saga enters and after your draw step, add a lore counter. Sacrifice after IV.)\nI — This Saga deals 6 damage to target creature an opponent controls.\nII — Destroy target artifact an opponent controls.\nIII, IV — Add {R}." "IV" #[
    chapter "I" "This Saga deals 6 damage to target creature an opponent controls."
      (Effect.chapterDealDamageToOppCreature 6),
    chapter "II" "Destroy target artifact an opponent controls."
      (Effect.chapterDestroyOppArtifact),
    chapter "III, IV" "Add {R}." (Effect.chapterAddMana (.colored .red))]

def cantankerousKeepers : CardDef :=
  creature "Cantankerous Keepers" (ManaCost.ofGenericAndColor 5 .green) #["Elf", "Soldier"] 4 3 (oracleText := "Affinity for Elves (This spell costs {1} less to cast for each Elf you control.)\nWhen this creature enters, mill four cards, then put all Elf cards from among them into your hand.")
    (affinityForSubtype := some "Elves")
    (triggeredAbilities := #[.onEnterMillThenSubtypeToHand 4 "Elf"])

def celebrateTheMountainKing : CardDef :=
  enchantment "Celebrate the Mountain-king" (ManaCost.ofGenericAndColor 3 .white) "When this enchantment enters, for each opponent, exile up to one target nonland permanent that player controls until this enchantment leaves the battlefield.\nWhen this enchantment enters, recruit. (Draw a card, then discard a card. If you discarded a nonland card, create a 1/1 white Human Soldier creature token.)"
    (triggeredAbilities := #[.onEnterRecruit,
      .onEnterExileOppNonlandEachUntilLeaves])

def dancingFromDarkToDawn : CardDef :=
  enchantment "Dancing from Dark to Dawn" (ManaCost.ofGenericAndColors 3 [.green, .green]) "Whenever you cast a creature spell, put X +1/+1 counters on target creature you control, where X is that spell's mana value.\nLandfall — Whenever a land you control enters, create a 2/2 green Bear creature token."
    (triggeredAbilities := #[.onLandYouControlEntersCreateTokens .bear 1,
      .onCastCreaturePlusOneEqualMv])

def desertWereWorm : CardDef :=
  creature "Desert Were-Worm" (ManaCost.ofGenericAndColors 4 [.red, .red]) #["Dragon", "Wurm"] 0 5 (oracleText := "This creature gets +2/+0 for each Mountain you control.\nWhenever you attack with creatures with total power 12 or greater for the first time each turn, untap all attacking creatures. After this phase, there is an additional combat phase.")
    (powerPerMountain := 2)
    (triggeredAbilities := #[.onAttackWithTotalPowerUntapExtraCombat 12])

def downInTheValley : CardDef :=
  saga "Down in the Valley" (ManaCost.ofGenericAndColor 2 .green) "(As this Saga enters and after your draw step, add a lore counter. Sacrifice after IV.)\nI — Search your library for a basic land card, reveal it, put it into your hand, then shuffle.\nII — This Saga gains \"Landfall — Whenever a land you control enters, create a 1/1 green Elf creature token.\"\nIII, IV — Elves you control get +1/+0 and gain vigilance until end of turn." "IV" #[
    chapter "I" "Search your library for a basic land card, reveal it, put it into your hand, then shuffle."
      (Effect.chapterSearchBasicLandToHand),
    chapter "II" "This Saga gains \"Landfall — Whenever a land you control enters, create a 1/1 green Elf creature token.\""
      (Effect.chapterGainLandfallCreateElf),
    chapter "III, IV" "Elves you control get +1/+0 and gain vigilance until end of turn."
      (Effect.chapterElvesGetVigilance 1)]

def downDownToGoblinTown : CardDef :=
  saga "Down, Down to Goblin-town" (ManaCost.ofGenericAndColor 2 .black) "(As this Saga enters and after your draw step, add a lore counter. Sacrifice after IV.)\nI — Target opponent reveals their hand. You choose a nonland card from it. That player discards that card.\nII — Amass Goblins 1. (Put a +1/+1 counter on an Army you control. It's also a Goblin. If you don't control an Army, create a 0/0 black Goblin Army creature token first.)\nIII, IV — Target opponent loses 1 life and you gain 1 life." "IV" #[
    chapter "I" "Target opponent reveals their hand. You choose a nonland card from it. That player discards that card."
      (Effect.chapterOpponentDiscardsNonland),
    chapter "II" "Amass Goblins 1. (Put a +1/+1 counter on an Army you control. It's also a Goblin. If you don't control an Army, create a 0/0 black Goblin Army creature token first.)"
      (Effect.chapterAmassGoblins 1),
    chapter "III, IV" "Target opponent loses 1 life and you gain 1 life."
      (Effect.chapterOpponentLosesYouGain 1)]

def dwalinWeaponmaster : CardDef :=
  legendaryCreature "Dwalin, Weaponmaster" (ManaCost.ofGenericAndHybrids 1 .red .white 1) #["Dwarf", "Warrior"] 2 1 (oracleText := "First strike\nWhenever Dwalin enters or attacks, put a hone counter on each Equipment you control. (Each hone counter on an Equipment grants +1/+0 to equipped creature.)")
    (keywords := Keyword.firstStrike)
    (triggeredAbilities := #[.onEnterOrAttackHoneEachEquipment])

def dainIronfoot : CardDef :=
  legendaryCreature "Dáin Ironfoot" (ManaCost.ofGenericAndColor 2 .red) #["Dwarf", "Warrior"] 1 4 (oracleText := "When Dáin enters, create a colorless Equipment artifact token named Axe with \"Equipped creature gets +1/+0\" and equip {2}. When you do, attach it to target creature you control.\nWhenever Dáin attacks, each equipped attacking creature gains double strike until end of turn.")
    (triggeredAbilities := #[.onEnterCreateAxeAttach, .onAttackEquippedGainDoubleStrike])

def elrondMoonReader : CardDef :=
  legendaryCreature "Elrond, Moon-Reader" (ManaCost.ofGenericAndColor 2 .blue) #["Elf", "Noble"] 3 3 (oracleText := "Whenever you activate an ability of a creature, draw a card. This ability triggers only once each turn.\n{5}{U}{U}: Exile up to two other target nonland permanents you control. Return those cards to the battlefield under their owner's control at the beginning of the next end step.")
    (activatedAbilities := #[
      activated (Effect.exileThenReturnNextEnd) (ManaCost.ofGenericAndColors 5 [.blue, .blue])])
    (triggeredAbilities := #[.onActivateCreatureAbilityDrawOnce])

def elvenPassage : CardDef :=
  land "Elven Passage" "{T}, Pay 1 life, Sacrifice this land: Search your library for a basic land card, put it onto the battlefield tapped, then shuffle. You may behold an Elf. If you do, untap that land. (To behold an Elf, choose an Elf you control or reveal an Elf card from your hand.)"
    (activatedAbilities := #[
      activated (Effect.searchBasicBeholdSubtypeUntap "Elf") (tap := true) (payLife := 1)
        (sacrificeSource := true)])

def enchantedRiverSGrasp : CardDef :=
  aura "Enchanted River's Grasp" (ManaCost.ofGenericAndColor 2 .blue) "Enchant creature\nWhen this Aura enters, tap enchanted creature and remove all counters from it.\nEnchanted creature loses all abilities and doesn't untap during its controller's untap step."
    (staticAbilities := #[.enchantedLosesAbilitiesDoesntUntap])
    (triggeredAbilities := #[.onEnterTapEnchantedRemoveCounters])

def getawayBarrel : CardDef :=
  artifact "Getaway Barrel" (ManaCost.ofGenericAndColor 3 .red) "When this artifact is put into a graveyard from the battlefield, reveal the top thirteen cards of your library. Put a random creature card from among them onto the battlefield. Put the rest on the bottom of your library in a random order."
    (triggeredAbilities := #[.onDiesRevealTopPutRandomCreature 13])

def gleamingSplendor : CardDef :=
  enchantment "Gleaming Splendor" (ManaCost.ofGenericAndColor 1 .white) "Whenever an opponent draws their second card each turn, you create a Treasure token.\n{2}{W}: Two target players each draw a card."
    (activatedAbilities := #[
      activated (Effect.twoPlayersDraw) (ManaCost.ofGenericAndColor 2 .white)])
    (triggeredAbilities := #[.onOpponentDrawsSecondCreateTreasure])

def gollumRiddleMaster : CardDef :=
  let c :=
    legendaryCreature "Gollum, Riddle Master" (ManaCost.ofGenericAndColor 1 .black) #["Halfling", "Horror"] 3 1 (oracleText := "As Gollum enters, choose odd or even. (Zero is even.)\nWhenever an opponent casts a spell with mana value of the chosen quality, choose one that hasn't been chosen —\n• Put a +1/+1 counter on Gollum.\n• Each opponent loses 2 life and you gain 2 life.\n• Draw a card.")
      (triggeredAbilities := #[.onOpponentCastsChosenParityModes])
  { c with asEntersChooseOddEven := true }

def headOfTheHunt : CardDef :=
  let c :=
    creature "Head of the Hunt" (ManaCost.ofGenericAndColors 2 [.black, .black]) #["Wolf"] 4 3 (oracleText := "Flash\nIf a creature an opponent controls would die, exile it instead. When you do, create a 2/2 green Wolf creature token.")
      (keywords := Keyword.flash)
      (staticAbilities := #[.exileOppDeathCreateWolf])
  { c with exileOppCreaturesInstead := true }

def insideInformation : CardDef :=
  sorcery "Inside Information" ({ symbols := #[.x, .colored .black, .colored .black] }) "Exile the top X cards of target opponent's library. You may play those cards this turn. If you cast a spell this way, pay life equal to its mana value rather than pay its mana cost." (some (Effect.exileTopXOppPlayForLife))

def keyToTheSideDoor : CardDef :=
  artifact "Key to the Side-Door" (ManaCost.ofGeneric 1) "{2}, {T}: Target creature can't be blocked this turn.\n{1}, {T}, Discard a legendary card with the same name as a legendary permanent you control: Draw two cards."
    (activatedAbilities := #[
      activated (Effect.targetCantBeBlockedThisTurn) (ManaCost.ofGeneric 2) (tap := true),
      activated (Effect.discardLegendarySameNameDraw) (ManaCost.ofGeneric 1) (tap := true)
        (discardLegendarySameName := true)])

def lakeTownToymaker : CardDef :=
  creature "Lake-town Toymaker" (ManaCost.ofGenericAndColor 3 .white) #["Human", "Artificer"] 3 4 (oracleText := "At the beginning of combat on your turn, if you've drawn two or more cards this turn, another target creature you control gets +3/+0 and gains first strike until end of turn.")
    (triggeredAbilities := #[.onYourBeginCombatIfDrawnTwoPumpFirstStrike])

def lastLightOfDurinSDay : CardDef :=
  enchantment "Last Light of Durin's Day" (ManaCost.ofGenericAndColor 1 .red) "Whenever a Mountain you control enters, put a quest counter on this enchantment. If it has six or more quest counters on it, sacrifice it. If you do, search your hand and/or library for a Dragon card and put it onto the battlefield. If you search your library this way, shuffle.\nMountaincycling {2} ({2}, Discard this card: Search your library for a Mountain card, reveal it, put it into your hand, then shuffle.)"
    (triggeredAbilities := #[.onMountainEntersQuestThenDragon])
    (activatedAbilities := #[typecyclingAbility "Mountain" (ManaCost.ofGeneric 2)])

def masterSCouncillors : CardDef :=
  creature "Master's Councillors" (ManaCost.ofGenericAndColor 1 .blue) #["Human", "Advisor"] 1 3 (oracleText := "Vigilance\nThis creature gets +2/+0 for each graveyard with seven or more cards in it.\nWhenever you draw your second card each turn, target player mills three cards. (They put the top three cards of their library into their graveyard.)")
    (keywords := Keyword.vigilance)
    (staticAbilities := #[.powerPerFatGraveyard 2])
    (triggeredAbilities := #[.onDrawSecondMillPlayer 3])

def oldFatSpiderCanTSeeMe : CardDef :=
  saga "Old Fat Spider Can't See Me" (ManaCost.ofGenericAndColor 2 .blue) "(As this Saga enters and after your draw step, add a lore counter. Sacrifice after IV.)\nI — Target creature you control gains hexproof for as long as this Saga remains on the battlefield.\nII — Prevent all damage that would be dealt by up to one target creature for as long as this Saga remains on the battlefield.\nIII, IV — Draw a card." "IV" #[
    chapter "I" "Target creature you control gains hexproof for as long as this Saga remains on the battlefield."
      (Effect.chapterGrantHexproofWhileRemains),
    chapter "II" "Prevent all damage that would be dealt by up to one target creature for as long as this Saga remains on the battlefield."
      (Effect.chapterPreventDamageWhileRemains),
    chapter "III, IV" "Draw a card." (Effect.chapterDraw 1)]

def orcristGoblinCleaver : CardDef :=
  equipment "Orcrist, Goblin-cleaver" (ManaCost.ofGeneric 3) "Equipped creature gets +2/+2 and has trample.\nWhenever equipped creature deals combat damage to a player, choose a creature type. Create a Treasure token for each creature you control of that type.\nEquip {3}"
    (ManaCost.ofGeneric 3)
    (legendary := true)
    (staticAbilities := #[.equippedCreatureGetsAndHas 2 2 Keyword.trample])
    (triggeredAbilities := #[.onEquippedCombatDamageTreasuresPerChosenType])

def partInFriendship : CardDef :=
  enchantment "Part in Friendship" (ManaCost.ofGenericAndColor 4 .green) "Whenever a nontoken creature you control dies, reveal cards from the top of your library until you reveal a creature card. If its mana value is less than or equal to the number of lands you control, put it onto the battlefield. Otherwise, put it into your hand. Put the rest on the bottom of your library in a random order. This ability triggers only once each turn."
    (triggeredAbilities := #[.onNontokenYouControlDiesRevealCreature])

def radagastOfRhosgobel : CardDef :=
  let c :=
    legendaryCreature "Radagast of Rhosgobel" (ManaCost.ofGenericAndColors 2 [.green, .green]) #["Avatar", "Wizard"] 2 5 (oracleText := "The first creature spell you cast each turn costs {2} less to cast and can be cast as though it had flash.")
  { c with firstCreatureCostsLess := 2, firstCreatureHasFlash := true }

def rhovanionRampager : CardDef :=
  creature "Rhovanion Rampager" (ManaCost.ofGenericAndColor 2 .black) #["Wolf"] 3 2 (oracleText := "Whenever this creature attacks, you may sacrifice another creature. If you do, put a number of +1/+1 counters on this creature equal to the sacrificed creature's power.\nWhen this creature dies, amass Goblins X, where X is this creature's power. (Put X +1/+1 counters on an Army you control. It's also a Goblin. If you don't control an Army, create a 0/0 black Goblin Army creature token first.)")
    (triggeredAbilities := #[.onAttackMaySacAnotherPlusOneEqualPower,
      .onDiesAmassGoblinsEqualPower])

def riddlesInTheDark : CardDef :=
  instant "Riddles in the Dark" (ManaCost.ofGenericAndColor 2 .blue) "Look at the top four cards of your library and separate them into a face-down pile and a face-up pile. An opponent chooses one of the piles. Put that pile into your hand and the other into your graveyard." (some (Effect.riddlesInTheDark))

def roadsGoEverEverOn : CardDef :=
  saga "Roads Go Ever, Ever On" (ManaCost.ofGenericAndColor 1 .white) "(As this Saga enters and after your draw step, add a lore counter. Sacrifice after IV.)\nI — Search your library for up to two basic Plains cards, exile them, then shuffle. You gain 2 life.\nII, III — Put a card exiled with this Saga into its owner's hand.\nIV — Whenever you attack this turn, target creature you control gets +1/+1 until end of turn for each Plains you control." "IV" #[
    chapter "I" "Search your library for up to two basic Plains cards, exile them, then shuffle. You gain 2 life."
      (Effect.chapterSearchBasicPlainsExileGainLife 2 2),
    chapter "II, III" "Put a card exiled with this Saga into its owner's hand."
      (Effect.chapterReturnLinkedExileToHand),
    chapter "IV" "Whenever you attack this turn, target creature you control gets +1/+1 until end of turn for each Plains you control."
      (Effect.chapterGrantAttackPumpPerPlainsThisTurn)]

def rollRollRollRoll : CardDef :=
  saga "Roll-Roll-Roll-Roll" (ManaCost.ofGenericAndColor 2 .blue) "(As this Saga enters and after your draw step, add a lore counter. Sacrifice after IV.)\nI, II, III, IV — Exile up to one target creature or land you control. If you do, return it to the battlefield under its owner's control at the beginning of the next end step." "IV" #[
    chapter "I, II, III, IV" "Exile up to one target creature or land you control. If you do, return it to the battlefield under its owner's control at the beginning of the next end step."
      (Effect.chapterBlinkUntilEndStep)]

def silvanReveler : CardDef :=
  creature "Silvan Reveler" (ManaCost.ofGenericAndColors 2 [.green, .blue]) #["Elf", "Citizen"] 3 2 (oracleText := "When this creature enters, draw a card, then discard a card. If you discard a land card this way, put it from your graveyard onto the battlefield tapped.\nLandfall — Whenever a land you control enters, you may pay {1}{G}{U}. If you do, return this card from your graveyard to your hand.")
    (triggeredAbilities := #[.onEnterLootLandEntersTapped,
      .onLandYouControlEntersPayReturnFromGy])

def stingBilboSSword : CardDef :=
  equipment "Sting, Bilbo's Sword" (ManaCost.ofGeneric 2) "Flash\nWhen Sting enters, put a hone counter on Sting for each creature target opponent controls. Attach Sting to up to one target creature you control. (Each hone counter on an Equipment grants +1/+0 to equipped creature.)\nEquip {3}"
    (ManaCost.ofGeneric 3)
    (legendary := true)
    (keywords := Keyword.flash)
    (triggeredAbilities := #[.onEnterHonePerOppCreaturesAttach])

def stoneGiantOfHighPass : CardDef :=
  creature "Stone-Giant of High Pass" (ManaCost.ofGenericAndColors 5 [.red, .red]) #["Giant"] 7 7 (oracleText := "Whenever this creature enters or attacks, create a 3/1 colorless Wall artifact creature token with defender named Stone Boulder.\n{2}{R}, Sacrifice an artifact: This creature deals 4 damage to any target.")
    (activatedAbilities := #[
      activated (Effect.dealDamageToAny 4) (ManaCost.ofGenericAndColor 2 .red)
        (sacrificeArtifact := true)])
    (triggeredAbilities := #[.onEnterOrAttackCreateWall])

def supperForSpiders : CardDef :=
  instant "Supper for Spiders" (ManaCost.ofGenericAndColor 1 .black) "Put onto the battlefield under your control all creature cards in your opponents' graveyards that were put there from the battlefield this turn. They are Food artifacts with \"{2}, {T}, Sacrifice this artifact: You gain 3 life.\" (They lose all other types and subtypes.)" (some (Effect.supperForSpiders))

def theEaglesAreComing : CardDef :=
  instant "The Eagles Are Coming!" (ManaCost.ofGenericAndColor 1 .white) "Kicker {2}{W}{W} (You may pay an additional {2}{W}{W} as you cast this spell.)\nChoose target creature you own. If this spell was kicked, instead choose any number of target creatures you own. Return each chosen creature to your hand. At the beginning of the next upkeep, create a 4/4 white Bird Soldier creature token with flying for each creature returned to your hand this way." (some (Effect.eaglesAreComing))
    (kicker := some (ManaCost.ofGenericAndColors 2 [.white, .white]))

def theGreatGoblin : CardDef :=
  legendaryCreature "The Great Goblin" (ManaCost.ofGenericAndHybrids 1 .black .red 2) #["Goblin", "Noble"] 3 2 (oracleText := "Whenever you put one or more counters on a Goblin, Orc, or Army you control, The Great Goblin deals 2 damage to target opponent.\nWhenever another Goblin, Orc, or Army you control dies, exile the top card of your library. You may play it until the end of your next turn.")
    (triggeredAbilities := #[.onPutCountersOnGoblinOrcArmyDamageOpp,
      .onAnotherGoblinOrcArmyDiesExileTop])

def theMasterOfLakeTown : CardDef :=
  legendaryCreature "The Master of Lake-town" (ManaCost.ofGenericAndColors 1 [.black, .black]) #["Human", "Advisor"] 3 2 (oracleText := "Deathtouch\nWhenever a player loses life, that player mills that many cards. (Damage causes loss of life.)\nWhen The Master of Lake-town dies, draw a card for each graveyard with seven or more cards in it.")
    (keywords := Keyword.deathtouch)
    (triggeredAbilities := #[.onPlayerLosesLifeMillThatMany, .onDiesDrawPerFatGraveyard])

def theMistyMountainsCold : CardDef :=
  saga "The Misty Mountains Cold" (ManaCost.ofGenericAndColor 2 .red) "(As this Saga enters and after your draw step, add a lore counter. Sacrifice after IV.)\nI, II, III, IV — Create a Treasure token. Then if you control four or more Treasures, sacrifice this Saga. If you do, create a 6/6 red Dragon creature token with flying. (A Treasure token is an artifact with \"{T}, Sacrifice this token: Add one mana of any color.\")" "IV" #[
    chapter "I, II, III, IV" "Create a Treasure token. Then if you control four or more Treasures, sacrifice this Saga. If you do, create a 6/6 red Dragon creature token with flying. (A Treasure token is an artifact with \"{T}, Sacrifice this token: Add one mana of any color.\")"
      (Effect.chapterTreasureThenDragonIfFour)]

def theMountainKingSReturn : CardDef :=
  saga "The Mountain-king's Return" (ManaCost.ofGenericAndColor 2 .white) "(As this Saga enters and after your draw step, add a lore counter. Sacrifice after III.)\nI — Recruit. (Draw a card, then discard a card. If you discarded a nonland card, create a 1/1 white Human Soldier creature token.)\nII — Return target creature card with mana value 3 or less from your graveyard to the battlefield.\nIII — Put a +1/+1 counter on up to one target creature." "III" #[
    chapter "I" "Recruit. (Draw a card, then discard a card. If you discarded a nonland card, create a 1/1 white Human Soldier creature token.)"
      (Effect.chapterRecruit),
    chapter "II" "Return target creature card with mana value 3 or less from your graveyard to the battlefield."
      (Effect.chapterReturnCreatureFromGyMvAtMost 3),
    chapter "III" "Put a +1/+1 counter on up to one target creature."
      (Effect.chapterPlusOneUpToOne)]

def theNotaryHobbits : CardDef :=
  legendaryCreature "The Notary Hobbits" (ManaCost.ofGenericAndColors 3 [.green, .green]) #["Halfling", "Advisor"] 1 1 (oracleText := "When The Notary Hobbits enter, if they're not a token, create two tokens that are copies of them, except the tokens aren't legendary.\n{T}: Add {C} for each Halfling you control.")
    (tapAddColorlessPerSubtype := some "Halfling")
    (triggeredAbilities := #[.onEnterIfNotTokenCopySelf])

def theSackvilleBagginses : CardDef :=
  (TraditionalCardDefinition.card [
    .name "The Sackville-Bagginses",
    .manaCost [.generic 1, .mono .black],
    .type .creature,
    .supertype .legendary,
    .subtype .halfling,
    .subtype .citizen,
    .power 2,
    .toughness 2,
    .ability (
      .triggered
        (.enter .this)
        (.sequence [
          .optional
            (.actionId 1
              (.sacrifice
                (.selected
                  (.controller .this)
                  (.range 1 1)
                  (.intersection [
                    .not .this,
                    .permanent,
                    .union [.cardType .creature, .cardType .artifact],
                    .controlled (.controller .this)])))),
          .if (.happened (.actionWithId 1) .gameStart)
            [
              .draw (.controller .this) 1,
              .createTokens (.controller .this) 1 PredefinedToken.treasureToken]])),
    .ability (
      .triggered
        (.die
          (.intersection [
            .token,
            .controlled (.controller .this)]))
        (.loseLife (.target 1 (.opponent (.controller .this))) 1))
  ]).toCardDef
    (oracleText := "When The Sackville-Bagginses enter, you may sacrifice another creature or artifact. If you do, draw a card and create a Treasure token.\nWhenever you sacrifice a token, target opponent loses 1 life.")

def thorinMountainKing : CardDef :=
  legendaryCreature "Thorin, Mountain-king" (ManaCost.ofGenericAndColor 3 .red) #["Dwarf", "Noble"] 3 4 (oracleText := "Trample\nWhen Thorin enters, attach any number of target Equipment you control to target creature you control. When one or more Equipment become attached to that creature this way, that creature deals damage equal to its power to up to one target creature.")
    (keywords := Keyword.trample)
    (triggeredAbilities := #[.onEnterAttachEquipmentThenFight])

def thranduilSCompany : CardDef :=
  (TraditionalCardDefinition.card [
    .name "Thranduil's Company",
    .manaCost [.generic 2, .mono .green, .mono .blue],
    .type .creature,
    .subtype .elf,
    .subtype .soldier,
    .power 3,
    .toughness 4,
    .ability (
      .static
        (.if
          (.any
            (.intersection [
              .not .this,
              .permanent,
              .subtype .elf,
              .controlled (.controller .this)]))
          [.increaseLandPlayLimit (.controller .this) (Value.nat 1)])),
    .ability (
      .triggered
        (.enter
          (.intersection [
            .permanent,
            .cardType .land,
            .controlled (.controller .this)]))
        (.sequence [
          .putCounter
            (.target
              1
              (.intersection [
                .permanent,
                .cardType .creature,
                .controlled (.controller .this)]))
            .plusOnePlusOne
            2,
          .continuous
            [.gainAbility (.targetReference 1) (.keyword .vigilance)]
            .endOfTurn]))
  ]).toCardDef
    (oracleText := "As long as you control another Elf, you may play an additional land on each of your turns.\nLandfall — Whenever a land you control enters, put two +1/+1 counters on target creature you control. It gains vigilance until end of turn.")

def thranduilTheElvenking : CardDef :=
  legendaryCreature "Thranduil, the Elvenking" (ManaCost.ofGenericAndColors 2 [.black, .green, .blue]) #["Elf", "Noble"] 5 6 (oracleText := "Thranduil has all activated abilities of all Elf cards in your graveyard.\nWhenever another legendary Elf you control enters, draw two cards, then discard a card.")
    (staticAbilities := #[.copyActivatedFromGySubtype "Elf"])
    (triggeredAbilities := #[.onAnotherLegendarySubtypeEntersLoot "Elf"])

def throughTheForestGate : CardDef :=
  sorcery "Through the Forest Gate" (ManaCost.ofGenericAndColors 6 [.green, .green]) "Look at the top twenty cards of your library, put any number of land cards from among them onto the battlefield tapped, then shuffle. You gain 8 life." (some (Effect.lookAtTopLandsGainLife 20 8))

def tomBertAndWilliam : CardDef :=
  legendaryCreature "Tom, Bert, and William" (ManaCost.ofGenericAndColors 3 [.black, .green]) #["Troll"] 5 5 (oracleText := "{1}, Sacrifice another creature: Draw cards equal to the sacrificed creature's power, then discard a card.\nWhen Tom, Bert, and William die, if they were a creature, return them to the battlefield. They're an artifact. (They're no longer a creature.)")
    (activatedAbilities := #[
      activated (Effect.drawEqualSacrificedPowerThenDiscard) (ManaCost.ofGeneric 1)
        (sacrificeAnotherSubtype := some "creature")])
    (triggeredAbilities := #[.onDiesReturnAsArtifact])

def uncoverTheMoonLetters : CardDef :=
  enchantment "Uncover the Moon-Letters" (ManaCost.ofGenericAndColor 3 .blue) "Whenever you cast a noncreature spell, you may draw X cards, where X is the amount of mana spent to cast that spell. If you do, discard two cards."
    (triggeredAbilities := #[.onCastNoncreatureMayDrawXDiscard2])

def wizardSStaff : CardDef :=
  equipment "Wizard's Staff" (ManaCost.ofGenericAndColor 1 .blue) "Equipped creature has prowess. (Whenever its controller casts a noncreature spell, that creature gets +1/+1 until end of turn.)\nIf a triggered ability of equipped creature triggers, that ability triggers an additional time.\nEquip Wizard {1}\nEquip {3}"
    (ManaCost.ofGeneric 1)
    (equipSubtype := some "Wizard")
    (moreEquips := #[equipAbility (ManaCost.ofGeneric 3)])
    (staticAbilities := #[.equippedTriggersAgain,
      .equippedCreatureHasKeywords Keyword.prowess])

/-- Every unique card in The Hobbit (HOB), including Journey basic lands
that are also in the core catalog. -/
def hobbitCards : Array CardDef := #[
  plains,
  island,
  swamp,
  mountain,
  forest,
  bofurReliableGuardianCard,
  dwarvenProvisionerCard,
  velvetwingButterfliesCard,
  magnificentEndCard,
  eagleOfTheGreatShelfCard,
  vowToEreborCard,
  bilboBagginsBurglarCard,
  lakeshoreApothecaryCard,
  confusticateAndBebotherCard,
  ravenhillFlockCard,
  thranduilsDecreeCard,
  bilboLuckwearerCard,
  uneasyPartingsCard,
  frontPorchSentriesCard,
  greatFierceBeeCard,
  stirUpTroubleCard,
  desolationProwlerCard,
  raveningWargCard,
  gollumSilentSlinkerCard,
  bilbosDeadlySliceCard,
  dreadedBatCloudCard,
  crudeBentBladeCard,
  gollumTheAbandonedCard,
  gnashingOfTeethCard,
  reverentHowlCard,
  stonyVoicedGoblinsCard,
  smaugTheGreatCalamityCard,
  gandalfSparkStarterCard,
  raggedShortSpearCard,
  snowslopeHunterCard,
  guardianOfTheHallsCard,
  quarrelCard,
  galionElvenkingsButlerCard,
  wargTacticsCard,
  beornsHospitalityCard,
  woodlandWeavemasterCard,
  mirkwoodPathmaker,
  beornReluctantHost,
  woodElves,
  attercop,
  ordinaryBear,
  largeBear,
  littleBear,
  elvenkingsHarper,
  smaugsFury,
  wellWornSpatula,
  elvenkingsHalls,
  ironHills,
  lakeTown,
  goblinTown,
  mirkwood,
  hobbitHole,
  nighthowlPursuer,
  wargling,
  wilderlandScrounger,
  nastyLittleRabbit,
  theChiefWarg,
  thorinsLastStand,
  stoneBySunlight,
  duskwatchHunter,
  patientInstructor,
  longLakeNuisance,
  laketownLookout,
  giantsBoulder,
  longBodiedGreyDog,
  doriBearerOfFriends,
  esgarothGarrison,
  gundabadOpportunist,
  giganticBigBear,
  bothersomeNoisemaker,
  fearsomeGoblinPair,
  goblinTownFlunkies,
  mistyMountainsRaider,
  bardsCompany,
  rageIntoTheValley,
  gatheringOfDarkness,
  soundTheTrumpets,
  fatefulDiscovery,
  chiefWargsCompany,
  dwarvenShortsword,
  goblinPlateMail,
  momentOfGlory,
  plunderTheTrollshaws,
  tidingsOfWar,
  eaglesRescue,
  gandalfWanderingWizard,
  trollNegotiations,
  dwarvenMattock,
  greatUglyLookingGoblin,
  theArkenstone,
  bolgsCompany,
  noriTellerOfTales,
  theLordOfTheEagles,
  throrsMap,
  theBlackArrow,
  smaugTheMagnificent,
  theQueenOfDale,
  oriKeeperOfSongs,
  oinTheBrave,
  bomburGentleDreamer,
  filiThePathfinder,
  thorinOakenshield,
  dainLordOfTheIronHills,
  oldThrush,
  mostDecrepitOldBird,
  lakeTownMariners,
  pineconeStrike,
  theLonelyMountain,
  thranduilSindarinLiege,
  gloinTheMighty,
  ironHillsStalwart,
  oldFatSpider,
  greatGildedBoat,
  desolationOfSmaug,
  dwarvenMauler,
  myPrecious,
  troopOfPonies,
  elvenRaftSteerer,
  mirkwoodMeditator,
  mirkwoodNurturer,
  kiliTheResourceful,
  dainsCompany,
  smaugWickedWorm,
  glamdringFoeHammer,
  settleTheWreckage,
  ironHillsBlacksmith,
  gandalfGoblinsBane,
  anUnexpectedParty,
  alongTheCrookedWay,
  azogMoriaSRuin,
  balinLoremaster,
  bardTheBowman,
  bardKingOfDale,
  bejeweledWarg,
  belladonnaTook,
  beornTheFierce,
  bifurMelodicRider,
  bilboSGambit,
  bilboThiefInTheNight,
  bolgOfTheNorth,
  boughsideWanderers,
  burnBurnTreeAndFern,
  cantankerousKeepers,
  celebrateTheMountainKing,
  dancingFromDarkToDawn,
  desertWereWorm,
  downInTheValley,
  downDownToGoblinTown,
  dwalinWeaponmaster,
  dainIronfoot,
  elrondMoonReader,
  elvenPassage,
  enchantedRiverSGrasp,
  getawayBarrel,
  gleamingSplendor,
  gollumRiddleMaster,
  headOfTheHunt,
  insideInformation,
  keyToTheSideDoor,
  lakeTownToymaker,
  lastLightOfDurinSDay,
  masterSCouncillors,
  oldFatSpiderCanTSeeMe,
  orcristGoblinCleaver,
  partInFriendship,
  radagastOfRhosgobel,
  rhovanionRampager,
  riddlesInTheDark,
  roadsGoEverEverOn,
  rollRollRollRoll,
  silvanReveler,
  stingBilboSSword,
  stoneGiantOfHighPass,
  supperForSpiders,
  theEaglesAreComing,
  theGreatGoblin,
  theMasterOfLakeTown,
  theMistyMountainsCold,
  theMountainKingSReturn,
  theNotaryHobbits,
  theSackvilleBagginses,
  thorinMountainKing,
  thranduilSCompany,
  thranduilTheElvenking,
  throughTheForestGate,
  tomBertAndWilliam,
  uncoverTheMoonLetters,
  wizardSStaff
]

#guard bofurReliableGuardianCard.colors.isMonocolored
#guard bofurReliableGuardianCard.isCreature
#guard bofurReliableGuardianCard.hasSupertype .legendary
#guard bofurReliableGuardianCard.hasSubtype "Dwarf"
#guard bofurReliableGuardianCard.hasSubtype "Scout"
#guard bofurReliableGuardianCard.power == some 1
#guard bofurReliableGuardianCard.toughness == some 1
#guard bofurReliableGuardianCard.keywords.lifelink
#guard bofurReliableGuardianCard.hasAdventure
#guard
  match bofurReliableGuardianCard.adventure with
  | some adv =>
    adv.name == "Concerted Care" &&
      adv.manaCost == (ManaCost.ofGenericAndColor 1 .white) &&
      adv.types == #[.instant] &&
      adv.subtypes.any (· == "Adventure") &&
      adv.spellEffect == some Effect.grantHexproofIndestructible
  | none => false
#guard dwarvenProvisionerCard.isCreature
#guard dwarvenProvisionerCard.hasSubtype "Dwarf"
#guard dwarvenProvisionerCard.hasSubtype "Citizen"
#guard dwarvenProvisionerCard.power == some 2
#guard dwarvenProvisionerCard.toughness == some 2
#guard dwarvenProvisionerCard.manaCost == ManaCost.ofGenericAndColor 1 .white
#guard dwarvenProvisionerCard.activatedAbilities.size == 1
#guard
  let ab := dwarvenProvisionerCard.activatedAbilities[0]!
  ab.cost.mana == ManaCost.ofGenericAndColor 3 .white &&
    ab.effect == Effect.abilityCreaturesYouControlGet 1 1
#guard (attercop.summary.splitOn "Landfall").length > 1
#guard (attercop.summary.splitOn "reach").length > 1
#guard attercop.keywords.reach
#guard attercop.keywords.deathtouch
#guard attercop.triggeredAbilities == #[.onLandYouControlEntersGets 1 1]
#guard raggedShortSpearCard.isEquipment
#guard !raggedShortSpearCard.isAura
#guard !raggedShortSpearCard.requiresTarget
#guard raggedShortSpearCard.staticAbilities == #[.equippedCreatureGets 2 0]
#guard raggedShortSpearCard.triggeredAbilities == #[.onEnterMayDiscardDraw 2]
#guard raggedShortSpearCard.activatedAbilities.size == 1
#guard raggedShortSpearCard.activatedAbilities[0]!.onlyAsSorcery
#guard raggedShortSpearCard.activatedAbilities[0]!.effect == Effect.attachToTargetCreatureYouControl
#guard raggedShortSpearCard.activatedAbilities[0]!.cost.mana == (ManaCost.ofGeneric 3)
#guard (raggedShortSpearCard.summary.splitOn "Equipped creature").length > 1
#guard crudeBentBladeCard.isEquipment
#guard !crudeBentBladeCard.isAura
#guard !crudeBentBladeCard.requiresTarget
#guard crudeBentBladeCard.staticAbilities == #[.equippedCreatureGets 2 1]
#guard crudeBentBladeCard.triggeredAbilities == #[.onEnterTargetOpponentSacrificesCreature]
#guard crudeBentBladeCard.activatedAbilities.size == 1
#guard crudeBentBladeCard.activatedAbilities[0]!.onlyAsSorcery
#guard crudeBentBladeCard.activatedAbilities[0]!.effect == Effect.attachToTargetCreatureYouControl
#guard crudeBentBladeCard.activatedAbilities[0]!.cost.mana == (ManaCost.ofGeneric 2)
#guard (crudeBentBladeCard.summary.splitOn "Equipped creature").length > 1
#guard (crudeBentBladeCard.summary.splitOn "target opponent").length > 1
#guard woodElves.triggeredAbilities == #[.onEnterSearchForest]
#guard (woodElves.summary.splitOn "Forest card").length > 1
#guard elvenkingsHalls.entersTapped
#guard elvenkingsHalls.tapAddOneOf == #[.colored .green, .colored .blue]
#guard elvenkingsHalls.activatedAbilities.size == 1
#guard elvenkingsHalls.activatedAbilities[0]!.effect == Effect.plusOneOnTarget 2 #["Elf"]
#guard elvenkingsHalls.activatedAbilities[0]!.onlyAsSorcery
#guard elvenkingsHalls.activatedAbilities[0]!.cost.tap
#guard elvenkingsHalls.activatedAbilities[0]!.cost.sacrificeSource
#guard goblinTown.tapAddOneOf == #[.colored .black, .colored .red]
#guard goblinTown.activatedAbilities[0]!.effect ==
  Effect.plusOneOnTarget 2 #["Goblin", "Orc"]
#guard mirkwood.activatedAbilities[0]!.effect ==
  Effect.plusOneOnTarget 2 #["Bear", "Spider", "Wolf"]
#guard hobbitHole.activatedAbilities.size == 2
#guard hobbitHole.activatedAbilities[0]!.effect == Effect.searchBasicLandTapped
#guard hobbitHole.activatedAbilities[0]!.cost.tap
#guard hobbitHole.activatedAbilities[0]!.cost.sacrificeSource
#guard hobbitHole.activatedAbilities[1]!.effect == Effect.searchLandTypeToHand "Halfling"
#guard hobbitHole.activatedAbilities[1]!.cost.discardSource
#guard hobbitHole.activatedAbilities[1]!.activateFromHand
#guard hobbitHole.activatedAbilities[1]!.cost.mana == ManaCost.ofGeneric 4
#guard throrsMap.triggeredAbilities == #[.onEnterSearchBasicToHand]
#guard throrsMap.activatedAbilities.size == 1
#guard throrsMap.activatedAbilities[0]!.effect == Effect.abilityDrawThenDiscard 1
#guard throrsMap.activatedAbilities[0]!.cost.tap
#guard throrsMap.activatedAbilities[0]!.cost.mana == ManaCost.ofGeneric 2
#guard throrsMap.supertypes.any (· == .legendary)
#guard galionElvenkingsButlerCard.triggeredAbilities == #[.onAttackSetOtherBasePT]
#guard (galionElvenkingsButlerCard.summary.splitOn "base power and toughness").length > 1
#guard galionElvenkingsButlerCard.power == some 4
#guard galionElvenkingsButlerCard.toughness == some 4
#guard woodlandWeavemasterCard.keywords.vigilance
#guard woodlandWeavemasterCard.triggeredAbilities == #[.onAnotherElfYouControlEntersGets1]
#guard woodlandWeavemasterCard.tapAddAnyColorEqualToPower
#guard woodlandWeavemasterCard.manaAbilities == #[
  .colored .white, .colored .blue, .colored .black, .colored .red, .colored .green]
#guard woodlandWeavemasterCard.power == some 1
#guard woodlandWeavemasterCard.toughness == some 2
#guard (woodlandWeavemasterCard.summary.splitOn "vigilance").length > 1
#guard (woodlandWeavemasterCard.summary.splitOn "another Elf").length > 1
#guard (woodlandWeavemasterCard.summary.splitOn "any one color").length > 1
#guard quarrelCard.isInstant
#guard quarrelCard.spellEffect == some (Effect.creatureYouControlDealsPowerToOppCreature)
#guard quarrelCard.requiresTarget
#guard Effect.creatureYouControlDealsPowerToOppCreature.targetCount == 2
#guard (quarrelCard.summary.splitOn "deals damage equal to its power").length > 1
#guard wargTacticsCard.isInstant
#guard wargTacticsCard.isModal
#guard wargTacticsCard.requiresTarget
#guard wargTacticsCard.spellModes == #[
  Effect.destroyCreatureWithFlying,
  Effect.plusOnePlusOneTrampleHexproof]
#guard (wargTacticsCard.summary.splitOn "Choose one").length > 1
#guard (wargTacticsCard.summary.splitOn "hexproof").length > 1
#guard beornsHospitalityCard.isEnchantment
#guard !beornsHospitalityCard.isCreature
#guard beornsHospitalityCard.triggeredAbilities == #[.onLandYouControlEntersPlusOnePlusOne]
#guard beornsHospitalityCard.activatedAbilities.size == 1
#guard beornsHospitalityCard.activatedAbilities[0]!.effect == Effect.becomeSubtypeWithLandsPT "Bear"
#guard beornsHospitalityCard.activatedAbilities[0]!.cost.mana ==
  (ManaCost.ofGenericAndColors 5 [.green, .green])
#guard (beornsHospitalityCard.summary.splitOn "Landfall").length > 1
#guard (beornsHospitalityCard.summary.splitOn "Bear creature").length > 1
#guard mirkwoodPathmaker.staticAbilities == #[.powerToughnessEqualLandsYouControl]
#guard mirkwoodPathmaker.power.isNone
#guard mirkwoodPathmaker.toughness.isNone
#guard (mirkwoodPathmaker.summary.splitOn "*/*").length > 1
#guard (mirkwoodPathmaker.summary.splitOn "lands you control").length > 1
#guard gandalfSparkStarterCard.keywords.reach
#guard gandalfSparkStarterCard.triggeredAbilities == #[.onEnterDealDividedDamage 3 3]
#guard (gandalfSparkStarterCard.summary.splitOn "divided as you choose").length > 1
#guard (gandalfSparkStarterCard.summary.splitOn "reach").length > 1
#guard guardianOfTheHallsCard.keywords.trample
#guard guardianOfTheHallsCard.activatedAbilities.size == 1
#guard guardianOfTheHallsCard.activatedAbilities[0]!.effect == Effect.putPlusOnePlusOneOnSource 3
#guard guardianOfTheHallsCard.activatedAbilities[0]!.cost.mana ==
  (ManaCost.ofGenericAndColors 5 [.green, .green])
#guard guardianOfTheHallsCard.power == some 2
#guard guardianOfTheHallsCard.toughness == some 2
#guard (guardianOfTheHallsCard.summary.splitOn "trample").length > 1
#guard (guardianOfTheHallsCard.summary.splitOn "+1/+1").length > 1
#guard snowslopeHunterCard.activatedAbilities.size == 1
#guard snowslopeHunterCard.activatedAbilities[0]!.effect ==
  Effect.exileTopPlayUntilEndOfNextTurn
#guard snowslopeHunterCard.activatedAbilities[0]!.cost.sacrificeAnotherCreatureOrArtifact
#guard snowslopeHunterCard.activatedAbilities[0]!.onlyDuringYourTurn
#guard snowslopeHunterCard.activatedAbilities[0]!.onceEachTurn
#guard bolgsCompany.activatedAbilities[0]!.cost.tap
#guard bolgsCompany.activatedAbilities[0]!.cost.sacrificeAnotherSubtype == some "Goblin"
#guard oldThrush.triggeredAbilities == #[.onEnterGainLifeSearchBasicOnTop 2]
#guard snowslopeHunterCard.power == some 2
#guard snowslopeHunterCard.toughness == some 3
#guard (snowslopeHunterCard.summary.splitOn "Exile the top card").length > 1
#guard gundabadOpportunist.triggeredAbilities == #[.onEnterExileTop]
#guard desolationProwlerCard.activatedAbilities.size == 1
#guard desolationProwlerCard.activatedAbilities[0]!.effect == Effect.sourceGets 2 2
#guard desolationProwlerCard.activatedAbilities[0]!.cost.payLife == 2
#guard desolationProwlerCard.activatedAbilities[0]!.onceEachTurn
#guard desolationProwlerCard.power == some 2
#guard desolationProwlerCard.toughness == some 2
#guard (desolationProwlerCard.summary.splitOn "Pay 2 life").length > 1
#guard raveningWargCard.keywords.deathtouch
#guard raveningWargCard.triggeredAbilities == #[.onAttackFerociousGainLife 2]
#guard raveningWargCard.power == some 2
#guard raveningWargCard.toughness == some 2
#guard (raveningWargCard.summary.splitOn "deathtouch").length > 1
#guard (raveningWargCard.summary.splitOn "Ferocious").length > 1
#guard (raveningWargCard.summary.splitOn "power 4 or greater").length > 1
#guard (raveningWargCard.summary.splitOn "gain 2 life").length > 1
#guard frontPorchSentriesCard.triggeredAbilities == #[.onDiesOppCreatureGets (-1) (-1)]
#guard (frontPorchSentriesCard.summary.splitOn "-1/-1").length > 1
#guard greatFierceBeeCard.keywords.flying
#guard greatFierceBeeCard.triggeredAbilities == #[.onOneOrMoreOtherCreaturesDieScry 1]
#guard (greatFierceBeeCard.summary.splitOn "other creatures die").length > 1
#guard stirUpTroubleCard.spellEffect == some (Effect.destroyCreature)
#guard stirUpTroubleCard.additionalCostSacrificeArtifactOrCreature
#guard stirUpTroubleCard.additionalCostOrPayGeneric == some 4
#guard gollumSilentSlinkerCard.keywords.menace
#guard (gollumSilentSlinkerCard.summary.splitOn "menace").length > 1
#guard bilbosDeadlySliceCard.spellEffect == some (Effect.destroyCreature)
#guard bilbosDeadlySliceCard.requiresTarget
#guard dreadedBatCloudCard.costReductionIfCreatureDied == 3
#guard dreadedBatCloudCard.keywords.flying
#guard dreadedBatCloudCard.keywords.deathtouch
#guard crudeBentBladeCard.isEquipment
#guard crudeBentBladeCard.staticAbilities == #[.equippedCreatureGets 2 1]
#guard crudeBentBladeCard.triggeredAbilities == #[.onEnterTargetOpponentSacrificesCreature]
#guard crudeBentBladeCard.activatedAbilities.size == 1
#guard gollumTheAbandonedCard.staticAbilities == #[.cantBlockUnlessYouControl #[]]
#guard gollumTheAbandonedCard.triggeredAbilities == #[.onEnterExileOppGyCardOppsLoseLife 2]
#guard gollumTheAbandonedCard.activatedAbilities[0]!.activateFromGraveyard
#guard gollumTheAbandonedCard.activatedAbilities[0]!.onlyAsSorcery
#guard gollumTheAbandonedCard.activatedAbilities[0]!.effect == Effect.returnFromGraveyardToHand
#guard gnashingOfTeethCard.isModal
#guard gnashingOfTeethCard.spellModes ==
  #[Effect.pumpAndExileIfDies (-5) (-5),
    Effect.creaturesTargetPlayerGet (-1) (-1)]
#guard reverentHowlCard.isModal
#guard reverentHowlCard.spellModes ==
  #[Effect.targetPlayerDrawLoseLife 2 2,
    Effect.pumpAndLifelink 2 2]
#guard stonyVoicedGoblinsCard.triggeredAbilities == #[.onEnterEachOpponentDiscards]
#guard gollumSilentSlinkerCard.power == some 4
#guard gollumSilentSlinkerCard.toughness == some 3
#guard gollumSilentSlinkerCard.supertypes.any (· == .legendary)
#guard !(gollumSilentSlinkerCard.summary.splitOn "can't be blocked except").length > 1
#guard bilbosDeadlySliceCard.isInstant
#guard bilbosDeadlySliceCard.hasCastKind .destroyCreature
#guard (bilbosDeadlySliceCard.summary.splitOn "Destroy target creature").length > 1
#guard smaugTheGreatCalamityCard.keywords.flying
#guard smaugTheGreatCalamityCard.hasAdventure
#guard smaugTheGreatCalamityCard.supertypes.any (· == .legendary)
#guard smaugTheGreatCalamityCard.power == some 5
#guard smaugTheGreatCalamityCard.toughness == some 5
#guard
  match smaugTheGreatCalamityCard.adventure with
  | some adv =>
    adv.name == "Spew Flame" &&
      adv.manaCost == (ManaCost.ofGenericAndColor 4 .red) &&
      adv.types == #[.sorcery] &&
      adv.subtypes.any (· == "Adventure") &&
      adv.spellEffect == some (Effect.dealDamageToCreature 5)
  | none => false
#guard (smaugTheGreatCalamityCard.oracleText.splitOn "//ADV//").length > 1
#guard (smaugTheGreatCalamityCard.oracleText.splitOn "{4}{R}").length > 1
#guard !smaugTheGreatCalamityCard.leftoverOracleLines.any (· == "//ADV//")
#guard (smaugTheGreatCalamityCard.summary.splitOn "//ADV//").length == 1
#guard (smaugTheGreatCalamityCard.summary.splitOn "Spew Flame {4}{R}").length > 1
#guard (smaugTheGreatCalamityCard.summary.splitOn "flying").length > 1
#guard beornReluctantHost.keywords.trample
#guard beornReluctantHost.hasAdventure
#guard beornReluctantHost.supertypes.any (· == .legendary)
#guard beornReluctantHost.power == some 5
#guard beornReluctantHost.toughness == some 5
#guard beornReluctantHost.hasSubtype "Human"
#guard beornReluctantHost.hasSubtype "Bear"
#guard beornReluctantHost.hasSubtype "Shapeshifter"
#guard
  match beornReluctantHost.adventure with
  | some adv =>
    adv.name == "Till and Tend" &&
      adv.manaCost == (ManaCost.ofGenericAndColor 1 .green) &&
      adv.types == #[.sorcery] &&
      adv.subtypes.any (· == "Adventure") &&
      adv.spellEffect == some (Effect.playAdditionalLandThisTurn) &&
      !adv.toCardDef.requiresTarget
  | none => false
#guard (beornReluctantHost.oracleText.splitOn "//ADV//").length > 1
#guard (beornReluctantHost.oracleText.splitOn "{1}{G}").length > 1
#guard !beornReluctantHost.leftoverOracleLines.any (· == "//ADV//")
#guard (beornReluctantHost.summary.splitOn "Till and Tend {1}{G}").length > 1
#guard (beornReluctantHost.summary.splitOn "trample").length > 1
#guard (beornReluctantHost.summary.splitOn "additional land").length > 1
#guard thranduilSCompany.extraLandIfOtherSubtype == some "Elf"
#guard thranduilSCompany.triggeredAbilities ==
  #[TriggeredAbility.onLandYouControlEntersPlusOneVigilance]
#guard thranduilSCompany.power == some 3
#guard thranduilSCompany.toughness == some 4
#guard thranduilSCompany.hasSubtype "Elf"
#guard thranduilSCompany.hasSubtype "Soldier"
#guard (bofurReliableGuardianCard.oracleText.splitOn "//ADV//").length > 1
#guard (bofurReliableGuardianCard.oracleText.splitOn "Concerted Care {1}{W}").length > 1
#guard (velvetwingButterfliesCard.oracleText.splitOn "//ADV//").length > 1
#guard (velvetwingButterfliesCard.oracleText.splitOn "Gaze in Wonder {1}{W}").length > 1
#guard velvetwingButterfliesCard.hasAdventure
#guard
  match velvetwingButterfliesCard.adventure with
  | some adv =>
    adv.name == "Gaze in Wonder" &&
      adv.manaCost == (ManaCost.ofGenericAndColor 1 .white) &&
      adv.types == #[.instant] &&
      adv.subtypes.any (· == "Adventure") &&
      adv.spellEffect == some Effect.tapOneOrTwoCreatures
  | none => false
#guard magnificentEndCard.costReductionIfTargetTapped == 3
#guard magnificentEndCard.spellEffect == some (Effect.dealDamageToCreature 5)
#guard eagleOfTheGreatShelfCard.keywords.flying
#guard eagleOfTheGreatShelfCard.triggeredAbilities ==
  #[TriggeredAbility.onAttackPumpForEachOtherCreature]
#guard vowToEreborCard.spellEffect == some (Effect.untapPumpMaybeAttach 2 2)
#guard (bilboBagginsBurglarCard.oracleText.splitOn "//ADV//").length > 1
#guard (bilboBagginsBurglarCard.oracleText.splitOn "Take a Glance {U}").length > 1
#guard bilboBagginsBurglarCard.triggeredAbilities == #[TriggeredAbility.onEnterDraw 1]
#guard
  match bilboBagginsBurglarCard.adventure with
  | some adv => adv.spellEffect == some (Effect.scry 2)
  | none => false
#guard lakeshoreApothecaryCard.keywords.vigilance
#guard lakeshoreApothecaryCard.triggeredAbilities ==
  #[TriggeredAbility.onDrawSecondPlusOne]
#guard confusticateAndBebotherCard.spellModes ==
  #[Effect.counterUnlessPays 4, Effect.drawThenDiscard 2]
#guard ravenhillFlockCard.keywords.flying
#guard ravenhillFlockCard.triggeredAbilities ==
  #[TriggeredAbility.onDrawPlusOne]
#guard thranduilsDecreeCard.spellEffect ==
  some Effect.counterExilePermanentMayCast
#guard (bilboLuckwearerCard.oracleText.splitOn "//ADV//").length > 1
#guard (bilboLuckwearerCard.oracleText.splitOn "Burglar's Plot {4}{U}").length > 1
#guard bilboLuckwearerCard.keywords.cantBeBlocked
#guard bilboLuckwearerCard.triggeredAbilities ==
  #[TriggeredAbility.onCombatDamageToPlayerLoot]
#guard
  match bilboLuckwearerCard.adventure with
  | some adv => adv.spellEffect == some Effect.exchangeControlSharingType
  | none => false
#guard uneasyPartingsCard.costReductionIfTargetAttackingNontoken == 1
#guard uneasyPartingsCard.spellEffect == some Effect.putOnTopOrBottom
#guard frontPorchSentriesCard.triggeredAbilities ==
  #[TriggeredAbility.onDiesOppCreatureGets (-1) (-1)]
#guard greatFierceBeeCard.keywords.flying
#guard greatFierceBeeCard.triggeredAbilities ==
  #[TriggeredAbility.onOneOrMoreOtherCreaturesDieScry 1]
#guard stirUpTroubleCard.spellEffect == some Effect.destroyCreature
#guard stirUpTroubleCard.additionalCostSacrificeArtifactOrCreature
#guard stirUpTroubleCard.additionalCostOrPayGeneric == some 4
#guard desolationProwlerCard.activatedAbilities[0]!.effect == Effect.sourceGets 2 2
#guard desolationProwlerCard.activatedAbilities[0]!.cost.payLife == 2
#guard desolationProwlerCard.activatedAbilities[0]!.onceEachTurn
#guard raveningWargCard.triggeredAbilities ==
  #[TriggeredAbility.onAttackFerociousGainLife 2]
#guard (gollumSilentSlinkerCard.oracleText.splitOn "//ADV//").length > 1
#guard (gollumSilentSlinkerCard.oracleText.splitOn "Meager Meal {B}").length > 1
#guard
  match gollumSilentSlinkerCard.adventure with
  | some adv =>
    adv.name == "Meager Meal" &&
      adv.manaCost == (ManaCost.ofColor .black) &&
      adv.types == #[.sorcery] &&
      adv.subtypes.any (· == "Adventure") &&
      adv.spellEffect == some (Effect.plusOneUpToOneAndPlayerGainsLife 2)
  | none => false
#guard bilbosDeadlySliceCard.spellEffect == some Effect.destroyCreature
#guard dreadedBatCloudCard.costReductionIfCreatureDied == 3
#guard dreadedBatCloudCard.keywords.flying
#guard dreadedBatCloudCard.keywords.deathtouch
#guard crudeBentBladeCard.isEquipment
#guard crudeBentBladeCard.staticAbilities == #[.equippedCreatureGets 2 1]
#guard crudeBentBladeCard.triggeredAbilities ==
  #[TriggeredAbility.onEnterTargetOpponentSacrificesCreature]
#guard crudeBentBladeCard.activatedAbilities[0]!.onlyAsSorcery
#guard gollumTheAbandonedCard.staticAbilities == #[.cantBlockUnlessYouControl #[]]
#guard gollumTheAbandonedCard.triggeredAbilities ==
  #[TriggeredAbility.onEnterExileOppGyCardOppsLoseLife 2]
#guard gollumTheAbandonedCard.activatedAbilities[0]!.activateFromGraveyard
#guard gnashingOfTeethCard.spellModes ==
  #[Effect.pumpAndExileIfDies (-5) (-5), Effect.creaturesTargetPlayerGet (-1) (-1)]
#guard reverentHowlCard.spellModes ==
  #[Effect.targetPlayerDrawLoseLife 2 2, Effect.pumpAndLifelink 2 2]
#guard stonyVoicedGoblinsCard.triggeredAbilities ==
  #[TriggeredAbility.onEnterEachOpponentDiscards]
#guard smaugTheGreatCalamityCard.keywords.flying
#guard smaugTheGreatCalamityCard.hasAdventure
#guard
  match smaugTheGreatCalamityCard.adventure with
  | some adv => adv.spellEffect == some (Effect.dealDamageToCreature 5)
  | none => false
#guard gandalfSparkStarterCard.keywords.reach
#guard gandalfSparkStarterCard.triggeredAbilities ==
  #[TriggeredAbility.onEnterDealDividedDamage 3 3]
#guard raggedShortSpearCard.isEquipment
#guard raggedShortSpearCard.staticAbilities == #[.equippedCreatureGets 2 0]
#guard raggedShortSpearCard.triggeredAbilities ==
  #[TriggeredAbility.onEnterMayDiscardDraw 2]
#guard snowslopeHunterCard.activatedAbilities[0]!.onlyDuringYourTurn
#guard snowslopeHunterCard.activatedAbilities[0]!.onceEachTurn
#guard snowslopeHunterCard.activatedAbilities[0]!.effect ==
  Effect.exileTopPlayUntilEndOfNextTurn
#guard guardianOfTheHallsCard.keywords.trample
#guard guardianOfTheHallsCard.activatedAbilities[0]!.effect ==
  Effect.putPlusOnePlusOneOnSource 3
#guard ordinaryBear.isCreature
#guard ordinaryBear.hasSubtype "Bear"
#guard ordinaryBear.power == some 4
#guard ordinaryBear.toughness == some 5
#guard ordinaryBear.triggeredAbilities.isEmpty
#guard ordinaryBear.activatedAbilities.isEmpty
#guard largeBear.isCreature
#guard largeBear.hasSubtype "Bear"
#guard largeBear.keywords.reach
#guard largeBear.keywords.trample
#guard largeBear.keywords.haste
#guard largeBear.manaCost == ManaCost.ofGenericAndHybrids 3 .black .green 2
#guard littleBear.isCreature
#guard littleBear.hasSubtype "Bear"
#guard littleBear.power == some 3
#guard littleBear.toughness == some 2
#guard littleBear.keywords.flash
#guard littleBear.manaCost == ManaCost.ofGenericAndColor 2 .green
#guard littleBear.triggeredAbilities == #[.onEnterUntapOtherPlusOneIfSubtype "Bear"]
#guard ironHillsStalwart.triggeredAbilities == #[.onEnterAttachTargetEquipment]
#guard thranduilSindarinLiege.hasSupertype .legendary
#guard thranduilSindarinLiege.staticAbilities == #[.otherCreaturesGet #["Elf"] 1 1]
#guard thranduilSindarinLiege.triggeredAbilities ==
  #[.onLandYouControlEntersCreateTokens .elf 1]
#guard
  match thranduilSindarinLiege.adventure with
  | some adv =>
    adv.name == "Silvan Rally" &&
      adv.spellEffect == some (Effect.millThenPutLands 4 2)
  | none => false

end Mtg.Engine.Catalog
