import Mtg.Engine.Card
import Mtg.Engine.Catalog

/-!
# The Hobbit catalog

Oracle characteristics for cards from Magic: The Gathering | The Hobbit
(HOB). Oracle text is stored verbatim from Scryfall; modeled fields must
reconstruct it. `CardDef.matchesOracleText` checks that mechanically.
`hobbitCards` lists every unique card in the set, including Journey basic
lands that are also in the core catalog.

New cards may be written as a `TraditionalCardDefinition` (a list of
`CardPart`s) and compiled with `toCardDef`. Bofur, Reliable Guardian is
the first card in that style.

Source: https://magic.wizards.com/en/news/announcements/the-hobbit-welcome-decks
-/

namespace Mtg.Engine.Catalog

open Mtg.Engine

def bofurReliableGuardian : TraditionalCardDefinition := .card [
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
    .action (
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
        .endOfTurn)]
]

def bofurReliableGuardianCard : CardDef :=
  bofurReliableGuardian.toCardDef
    (oracleText := "Lifelink\n//ADV//\nConcerted Care {1}{W}\nInstant — Adventure\nTarget artifact or creature you control gains hexproof and indestructible until end of turn. (Then exile this card. You may cast the creature later from exile.)")

def dwarvenProvisioner : TraditionalCardDefinition := .card [
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
        [.addPowerToughness
          (.intersection [
            .permanent,
            .cardType .creature,
            .controlled (.controller .this)])
          1 1]
        .endOfTurn))
]

def dwarvenProvisionerCard : CardDef :=
  dwarvenProvisioner.toCardDef
    (oracleText := "{3}{W}: Creatures you control get +1/+1 until end of turn.")

def velvetwingButterflies : TraditionalCardDefinition := .card [
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
    .action (
      .tap (.targets 1 (.range 1 2) (.intersection [.permanent, .cardType .creature])))]]

def velvetwingButterfliesCard : CardDef :=
  velvetwingButterflies.toCardDef
    (oracleText := "Flying\n//ADV//\nGaze in Wonder {1}{W}\nInstant — Adventure\nTap one or two target creatures. (Then exile this card. You may cast the creature later from exile.)")

def magnificentEnd : TraditionalCardDefinition := .card [
  .name "Magnificent End",
  .manaCost [.generic 4, .mono .white],
  .type .instant,
  .ability (
    .static
      [.ifAny
        (.intersection [
          .allTargets .this,
          .permanent,
          .cardType .creature,
          .tapped])
        [.reduceCost .this [.mana [.generic 3]]]]),
  .action (
    .dealDamage
      .this
      (.target 1 (.intersection [.permanent, .cardType .creature]))
      5)]

def magnificentEndCard : CardDef :=
  magnificentEnd.toCardDef
    (oracleText := "This spell costs {3} less to cast if it targets a tapped creature.\nMagnificent End deals 5 damage to target creature.")

def eagleOfTheGreatShelf : TraditionalCardDefinition := .card [
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
      (.continuous [.addPowerToughness (.source .this) 1 1] .endOfTurn))
]

def eagleOfTheGreatShelfCard : CardDef :=
  eagleOfTheGreatShelf.toCardDef
    (oracleText := "Flying\nWhenever this creature attacks, it gets +1/+1 until end of turn for each other creature you control.")

def vowToErebor : TraditionalCardDefinition := .card [
  .name "Vow to Erebor",
  .manaCost [.generic 1, .mono .white],
  .type .instant,
  .action (
    .sequence [
      .untap
        (.target
          1
          (.intersection [
            .permanent,
            .cardType .creature,
            .controlled (.controller .this)])),
      .continuous [.addPowerToughness (.targetReference 1) 2 2] .endOfTurn,
      .forEach 1
        (.ifAny
          (.intersection [.var 1, .subtype .dwarf])
          [
            .optional
              (.attach
                (.selected
                  (.range 1 1)
                  (.intersection [
                    .permanent,
                    .subtype .equipment,
                    .controlled (.controller .this)]))
                (.var 1))
          ])])]

def vowToEreborCard : CardDef :=
  vowToErebor.toCardDef
    (oracleText := "Untap target creature you control. It gets +2/+2 until end of turn. If it's a Dwarf, you may attach an Equipment you control to it.")

def bilboBagginsBurglar : TraditionalCardDefinition := .card [
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
    .action (.scry (.controller .this) 2)]
]

def bilboBagginsBurglarCard : CardDef :=
  bilboBagginsBurglar.toCardDef
    (oracleText := "When Bilbo Baggins enters, draw a card.\n//ADV//\nTake a Glance {U}\nSorcery — Adventure\nScry 2. (Then exile this card. You may cast the creature later from exile.)")

def lakeshoreApothecary : TraditionalCardDefinition := .card [
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
      (.drawSecond (.controller .this))
      (.putCounter (.source .this) 1))
]

def lakeshoreApothecaryCard : CardDef :=
  lakeshoreApothecary.toCardDef
    (oracleText := "Vigilance\nWhenever you draw your second card each turn, put a +1/+1 counter on this creature.")

def confusticateAndBebother : TraditionalCardDefinition := .card [
  .name "Confusticate and Bebother",
  .manaCost [.generic 2, .mono .blue],
  .type .instant,
  .action (
    .choose [
      .counterUnless (.target 1 .spell) [.mana [.generic 4]],
      .sequence [
        .draw (.controller .this) 2,
        .discard (.controller .this) 1]])
]

def confusticateAndBebotherCard : CardDef :=
  confusticateAndBebother.toCardDef
    (oracleText := "Choose one —\n• Counter target spell unless its controller pays {4}.\n• Draw two cards, then discard a card.")

def ravenhillFlock : TraditionalCardDefinition := .card [
  .name "Ravenhill Flock",
  .manaCost [.generic 3, .mono .blue],
  .type .creature,
  .subtype .bird,
  .power 1,
  .toughness 2,
  .ability (.keyword .flying),
  .ability (
    .triggered
      (.draw (.controller .this))
      (.putCounter (.source .this) 1))
]

def ravenhillFlockCard : CardDef :=
  ravenhillFlock.toCardDef
    (oracleText := "Flying\nWhenever you draw a card, put a +1/+1 counter on this creature.")

def thranduilsDecree : TraditionalCardDefinition := .card [
  .name "Thranduil's Decree",
  .manaCost [.generic 4, .mono .blue, .mono .blue],
  .type .instant,
  .action (
    .sequence [
      .counter (.target 1 .spell),
      .ifAny
        (.intersection [.allTargets .this, .permanent])
        [
          .exile (.allTargets .this),
          .optional (.cast (.allTargets .this))
        ]])
]

def thranduilsDecreeCard : CardDef :=
  thranduilsDecree.toCardDef
    (oracleText := "Counter target spell. If a permanent spell is countered this way, exile it instead of putting it into its owner's graveyard. You may cast that card without paying its mana cost for as long as it remains exiled.")

def bilboLuckwearer : TraditionalCardDefinition := .card [
  .name "Bilbo, Luckwearer",
  .manaCost [.generic 1, .mono .blue],
  .type .creature,
  .supertype .legendary,
  .subtype .halfling,
  .subtype .rogue,
  .power 1,
  .toughness 1,
  .ability (.keyword .cantBeBlocked),
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
    .action (
      .exchangeControl
        (.targets
          1
          (.range 2 2)
          (.intersection [.permanent, .nonland, .shareCardType])))]
]

def bilboLuckwearerCard : CardDef :=
  bilboLuckwearer.toCardDef
    (oracleText := "Bilbo can't be blocked.\nWhenever Bilbo deals combat damage to a player, draw a card, then discard a card.\n//ADV//\nBurglar's Plot {4}{U}\nSorcery — Adventure\nExchange control of two target nonland permanents that share a card type. (Then exile this card. You may cast the creature later from exile.)")

def uneasyPartings : CardDef :=
  instant "Uneasy Partings" (ManaCost.ofGenericAndColor 3 .blue)
    "This spell costs {1} less to cast if it targets an attacking nontoken creature.\nTarget creature's owner puts it on their choice of the top or bottom of their library."
    (some (Effect.putOnTopOrBottom))
    (costReductionIfTargetAttackingNontoken := 1)

def frontPorchSentries : CardDef :=
  creature "Front Porch Sentries" (ManaCost.ofGenericAndColor 1 .black) #["Goblin", "Soldier"] 2 2
    (oracleText := "When this creature dies, target creature an opponent controls gets -1/-1 until end of turn.")
    (triggeredAbilities := #[.onDiesOppCreatureGets (-1) (-1)])

def greatFierceBee : CardDef :=
  creature "Great Fierce Bee" (ManaCost.ofGenericAndColor 2 .black) #["Insect"] 2 2
    (oracleText := "Flying\nWhenever one or more other creatures die, scry 1. (Look at the top card of your library. You may put that card on the bottom.)")
    (keywords := Keyword.flying)
    (triggeredAbilities := #[.onOneOrMoreOtherCreaturesDieScry 1])

def stirUpTrouble : CardDef :=
  sorcery "Stir Up Trouble" (ManaCost.ofColor .black)
    "As an additional cost to cast this spell, sacrifice an artifact or creature or pay {4}.\nDestroy target creature."
    (some (Effect.destroyCreature))
    (additionalCostSacrificeArtifactOrCreature := true)
    (additionalCostOrPayGeneric := some 4)

def desolationProwler : CardDef :=
  creature "Desolation Prowler" (ManaCost.ofGenericAndColor 1 .black) #["Wolf"] 2 2
    (oracleText := "Pay 2 life: This creature gets +2/+2 until end of turn. Activate only once each turn.")
    (activatedAbilities := #[
      activated (Effect.sourceGets 2 2) (payLife := 2) (onceEachTurn := true)])

def raveningWarg : CardDef :=
  creature "Ravening Warg" (ManaCost.ofGenericAndColor 1 .black) #["Wolf"] 2 2
    (oracleText := "Deathtouch\nFerocious — Whenever this creature attacks while you control a creature with power 4 or greater, you gain 2 life.")
    (keywords := Keyword.deathtouch)
    (triggeredAbilities := #[.onAttackFerociousGainLife 2])

def gollumSilentSlinker : CardDef :=
  legendaryCreature "Gollum, Silent Slinker" (ManaCost.ofGenericAndColor 3 .black) #["Halfling", "Horror"] 4 3
    (oracleText := "Menace (This creature can't be blocked except by two or more creatures.)\n//ADV//\nMeager Meal {B}\nSorcery — Adventure\nPut a +1/+1 counter on up to one target creature. Target player gains 2 life. (Then exile this card. You may cast the creature later from exile.)")
    (keywords := Keyword.menace)
    (adventure := some (adventure "Meager Meal" (ManaCost.ofColor .black)
      "Put a +1/+1 counter on up to one target creature. Target player gains 2 life. (Then exile this card. You may cast the creature later from exile.)"
      (Effect.plusOneUpToOneAndPlayerGainsLife 2)))

def bilbosDeadlySlice : CardDef :=
  instant "Bilbo's Deadly Slice" (ManaCost.ofGenericAndColors 1 [.black, .black])
    "Destroy target creature."
    (some (Effect.destroyCreature))

def dreadedBatCloud : CardDef :=
  creature "Dreaded Bat-Cloud" (ManaCost.ofGenericAndColor 4 .black) #["Bat"] 4 2
    (oracleText := "This spell costs {3} less to cast if a creature died this turn.\nFlying, deathtouch")
    (keywords := Keyword.deathtouch.merge Keyword.flying)
    (costReductionIfCreatureDied := 3)

def crudeBentBlade : CardDef :=
  equipment "Crude Bent Blade" (ManaCost.ofGenericAndColor 2 .black)
    "When this Equipment enters, target opponent sacrifices a creature of their choice.\nEquipped creature gets +2/+1.\nEquip {2} ({2}: Attach to target creature you control. Equip only as a sorcery.)"
    (ManaCost.ofGeneric 2)
    (staticAbilities := #[.equippedCreatureGets 2 1])
    (triggeredAbilities := #[.onEnterTargetOpponentSacrificesCreature])

def gollumTheAbandoned : CardDef :=
  legendaryCreature "Gollum the Abandoned" (ManaCost.ofGenericAndColor 1 .black) #["Halfling", "Horror"] 2 2
    (oracleText := "Gollum can't block.\nWhen Gollum enters, exile up to one target card from an opponent's graveyard. Each opponent loses 2 life.\n{2}, Sacrifice an artifact or creature: Return this card from your graveyard to your hand. Activate only as a sorcery.")
    (staticAbilities := #[.cantBlockUnlessYouControl #[]])
    (triggeredAbilities := #[.onEnterExileOppGyCardOppsLoseLife 2])
    (activatedAbilities := #[
      activated (Effect.returnFromGraveyardToHand) (ManaCost.ofGeneric 2)
        (sacrificeAnotherCreatureOrArtifact := true)
        (onlyAsSorcery := true) (activateFromGraveyard := true)])

def gnashingOfTeeth : CardDef :=
  sorcery "Gnashing of Teeth" (ManaCost.ofGenericAndColors 1 [.black, .black])
    "Choose one —\n• Target creature gets -5/-5 until end of turn. If that creature would die this turn, exile it instead.\n• Creatures target player controls get -1/-1 until end of turn."
    (spellModes := #[(Effect.pumpAndExileIfDies (-5) (-5)), (Effect.creaturesTargetPlayerGet (-1) (-1))])

def reverentHowl : CardDef :=
  instant "Reverent Howl" (ManaCost.ofGenericAndColor 2 .black)
    "Choose one —\n• Target player draws two cards and loses 2 life.\n• Target creature gets +2/+2 and gains lifelink until end of turn."
    (spellModes := #[(Effect.targetPlayerDrawLoseLife 2 2), (Effect.pumpAndLifelink 2 2)])

def stonyVoicedGoblins : CardDef :=
  creature "Stony-Voiced Goblins" (ManaCost.ofGenericAndColor 1 .black) #["Goblin", "Bard"] 1 1
    (oracleText := "When this creature enters, each opponent discards a card.")
    (triggeredAbilities := #[.onEnterEachOpponentDiscards])

def smaugTheGreatCalamity : CardDef :=
  legendaryCreature "Smaug, the Great Calamity" (ManaCost.ofGenericAndColors 5 [.red, .red])
    #["Dragon"] 5 5
    (oracleText := "Flying\n//ADV//\nSpew Flame {4}{R}\nSorcery — Adventure\nSpew Flame deals 5 damage to target creature. (Then exile this card. You may cast the creature later from exile.)")
    (keywords := Keyword.flying)
    (adventure := some (adventure "Spew Flame" (ManaCost.ofGenericAndColor 4 .red)
      "Spew Flame deals 5 damage to target creature. (Then exile this card. You may cast the creature later from exile.)"
      (Effect.dealDamageToCreature 5)))

def gandalfSparkStarter : CardDef :=
  legendaryCreature "Gandalf, Spark Starter" (ManaCost.ofGenericAndColors 4 [.red, .red])
    #["Avatar", "Wizard"] 4 3
    (oracleText := "Reach\nWhen Gandalf enters, he deals 3 damage divided as you choose among one, two, or three targets.")
    (keywords := Keyword.reach)
    (triggeredAbilities := #[.onEnterDealDividedDamage 3 3])

def raggedShortSpear : CardDef :=
  equipment "Ragged Short Sp