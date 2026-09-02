import Mtg.Engine.Card
import Mtg.Engine.Catalog

/-!
# The Hobbit catalog

Oracle characteristics for cards from Magic: The Gathering | The Hobbit
(HOB). Oracle text is stored verbatim from Scryfall; modeled fields must
reconstruct it. `CardDef.matchesOracleText` checks that mechanically.
`hobbitCards` lists every unique card in the set, including Journey basic
lands that are also in the core catalog.

Cards are written as a `TraditionalCardDefinition` (a list of `CardPart`s)
and compiled with `traditional` / `toCardDef`.

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
      .targeted
        ({filter := .and [
            .permanent,
            .or [.cardType .artifact, .cardType .creature],
            .sameController
          ]})
        (.continuous
          [
            .gainAbility (.keyword .hexproof),
            .gainAbility (.keyword .indestructible)]
          .endOfTurn))
  ]
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
      ([.mana [.generic 3, .mono .white]])
      (.filtered
        (.and [.permanent, .cardType .creature, .sameController])
        (.continuous [.addPowerToughness 1 1] .endOfTurn)))
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
    .action (.targeted
      ({maximumTargets := 2,
        filter := .and [
          .permanent,
          .cardType .creature
        ]})
      .tap)
  ]
]

def velvetwingButterfliesCard : CardDef :=
  velvetwingButterflies.toCardDef
    (oracleText := "Flying\n//ADV//\nGaze in Wonder {1}{W}\nInstant — Adventure\nTap one or two target creatures. (Then exile this card. You may cast the creature later from exile.)")

def magnificentEnd : TraditionalCardDefinition := .card [
  .name "Magnificent End",
  .manaCost [.generic 4, .mono .white],
  .type .instant,
  .ability (.conditional
    (.this (.hasAnyTarget (.and [.permanent, .cardType .creature, .tapped])))
    (.self (.static [.costReduction [.mana [.generic 3]]]))),
  .action (.targeted
    ({filter := .and [
        .permanent,
        .cardType .creature
      ]})
    (.dealDamage 5))
]

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
  .ability (.triggered (.attack (.hasThis)) (.self (.continuous [.addPowerToughness 1 1] .endOfTurn)))
]

def eagleOfTheGreatShelfCard : CardDef :=
  eagleOfTheGreatShelf.toCardDef
    (oracleText := "Flying\nWhenever this creature attacks, it gets +1/+1 until end of turn for each other creature you control.")

def vowToErebor : TraditionalCardDefinition := .card [
  .name "Vow to Erebor",
  .manaCost [.generic 1, .mono .white],
  .type .instant,
  .action (.targeted
    ({filter := .and [
        .permanent,
        .cardType .creature,
        .sameController
      ]})
    (.sequence [
      .untap,
      .continuous [.addPowerToughness 2 2] .endOfTurn,
      .conditional (.target (.subtype .dwarf))
        (.optional (.inGame
          (.and [.permanent, .cardType .enchantment, .sameController])
          (.select 1 (.attachTo .target))))
    ]))
]

def vowToEreborCard : CardDef :=
  vowToErebor.toCardDef
    (oracleText := "Untap target creature you control. It gets +2/+2 until end of turn. If it's a Dwarf, you may attach an Equipment you control to it.")

def bilboBagginsBurglar : CardDef :=
  traditional [
    .name "Bilbo Baggins, Burglar",
    .manaCost [.generic 2, .mono .blue],
    .type .creature,
    .supertype .legendary,
    .subtype .halfling,
    .subtype .rogue,
    .power 2,
    .toughness 1,
    .oracleText "When Bilbo Baggins enters, draw a card.\n//ADV//\nTake a Glance {U}\nSorcery — Adventure\nScry 2. (Then exile this card. You may cast the creature later from exile.)",
    .triggered (.onEnterDraw 1),
    .alternative [
      .name "Take a Glance",
      .manaCost [.mono .blue],
      .type .sorcery,
      .subtype .adventure,
      .action (.effect (Effect.scry 2)),
      .oracleText "Scry 2. (Then exile this card. You may cast the creature later from exile.)"
    ]
  ]

def lakeshoreApothecary : CardDef :=
  traditional [
    .name "Lakeshore Apothecary",
    .manaCost [.generic 1, .mono .blue],
    .type .creature,
    .subtype .human,
    .subtype .cleric,
    .power 1,
    .toughness 2,
    .oracleText "Vigilance\nWhenever you draw your second card each turn, put a +1/+1 counter on this creature.",
    .ability (.keyword .vigilance),
    .triggered (.onDrawSecondPlusOne)
  ]

def confusticateAndBebother : CardDef :=
  traditional [
    .name "Confusticate and Bebother",
    .manaCost [.generic 2, .mono .blue],
    .type .instant,
    .oracleText "Choose one —\n• Counter target spell unless its controller pays {4}.\n• Draw two cards, then discard a card.",
    .chooseOne [Effect.counterUnlessPays 4, Effect.drawThenDiscard 2]
  ]

def ravenhillFlock : CardDef :=
  traditional [
    .name "Ravenhill Flock",
    .manaCost [.generic 3, .mono .blue],
    .type .creature,
    .subtype .bird,
    .power 1,
    .toughness 2,
    .oracleText "Flying\nWhenever you draw a card, put a +1/+1 counter on this creature.",
    .ability (.keyword .flying),
    .triggered (.onDrawPlusOne)
  ]

def thranduilsDecree : CardDef :=
  traditional [
    .name "Thranduil's Decree",
    .manaCost [.generic 4, .mono .blue, .mono .blue],
    .type .instant,
    .action (.effect (Effect.counterExilePermanentMayCast)),
    .oracleText "Counter target spell. If a permanent spell is countered this way, exile it instead of putting it into its owner's graveyard. You may cast that card without paying its mana cost for as long as it remains exiled."
  ]

def bilboLuckwearer : CardDef :=
  traditional [
    .name "Bilbo, Luckwearer",
    .manaCost [.generic 1, .mono .blue],
    .type .creature,
    .supertype .legendary,
    .subtype .halfling,
    .subtype .rogue,
    .power 1,
    .toughness 1,
    .oracleText "Bilbo can't be blocked.\nWhenever Bilbo deals combat damage to a player, draw a card, then discard a card.\n//ADV//\nBurglar's Plot {4}{U}\nSorcery — Adventure\nExchange control of two target nonland permanents that share a card type. (Then exile this card. You may cast the creature later from exile.)",
    .ability (.keyword .cantBeBlocked),
    .triggered (.onCombatDamageToPlayerLoot),
    .alternative [
      .name "Burglar's Plot",
      .manaCost [.generic 4, .mono .blue],
      .type .sorcery,
      .subtype .adventure,
      .action (.effect (Effect.exchangeControlSharingType)),
      .oracleText "Exchange control of two target nonland permanents that share a card type. (Then exile this card. You may cast the creature later from exile.)"
    ]
  ]

def uneasyPartings : CardDef :=
  traditional [
    .name "Uneasy Partings",
    .manaCost [.generic 3, .mono .blue],
    .type .instant,
    .action (.effect (Effect.putOnTopOrBottom)),
    .oracleText "This spell costs {1} less to cast if it targets an attacking nontoken creature.\nTarget creature's owner puts it on their choice of the top or bottom of their library.",
    .costReductionIfTargetAttackingNontoken 1
  ]

def frontPorchSentries : CardDef :=
  traditional [
    .name "Front Porch Sentries",
    .manaCost [.generic 1, .mono .black],
    .type .creature,
    .subtype .goblin,
    .subtype .soldier,
    .power 2,
    .toughness 2,
    .oracleText "When this creature dies, target creature an opponent controls gets -1/-1 until end of turn.",
    .triggered (.onDiesOppCreatureGets (-1) (-1))
  ]

def greatFierceBee : CardDef :=
  traditional [
    .name "Great Fierce Bee",
    .manaCost [.generic 2, .mono .black],
    .type .creature,
    .subtype .insect,
    .power 2,
    .toughness 2,
    .oracleText "Flying\nWhenever one or more other creatures die, scry 1. (Look at the top card of your library. You may put that card on the bottom.)",
    .ability (.keyword .flying),
    .triggered (.onOneOrMoreOtherCreaturesDieScry 1)
  ]

def stirUpTrouble : CardDef :=
  traditional [
    .name "Stir Up Trouble",
    .manaCost [.mono .black],
    .type .sorcery,
    .action (.effect (Effect.destroyCreature)),
    .oracleText "As an additional cost to cast this spell, sacrifice an artifact or creature or pay {4}.\nDestroy target creature.",
    .additionalCostSacrificeArtifactOrCreature,
    .additionalCostOrPayGeneric 4
  ]

def desolationProwler : CardDef :=
  traditional [
    .name "Desolation Prowler",
    .manaCost [.generic 1, .mono .black],
    .type .creature,
    .subtype .wolf,
    .power 2,
    .toughness 2,
    .oracleText "Pay 2 life: This creature gets +2/+2 until end of turn. Activate only once each turn.",
    .ability (.activated ([.onceEachTurn, .payLife 2]) (.effect (Effect.sourceGets 2 2)))
  ]

def raveningWarg : CardDef :=
  traditional [
    .name "Ravening Warg",
    .manaCost [.generic 1, .mono .black],
    .type .creature,
    .subtype .wolf,
    .power 2,
    .toughness 2,
    .oracleText "Deathtouch\nFerocious — Whenever this creature attacks while you control a creature with power 4 or greater, you gain 2 life.",
    .ability (.keyword .deathtouch),
    .triggered (.onAttackFerociousGainLife 2)
  ]

def gollumSilentSlinker : CardDef :=
  traditional [
    .name "Gollum, Silent Slinker",
    .manaCost [.generic 3, .mono .black],
    .type .creature,
    .supertype .legendary,
    .subtype .halfling,
    .subtype .horror,
    .power 4,
    .toughness 3,
    .oracleText "Menace (This creature can't be blocked except by two or more creatures.)\n//ADV//\nMeager Meal {B}\nSorcery — Adventure\nPut a +1/+1 counter on up to one target creature. Target player gains 2 life. (Then exile this card. You may cast the creature later from exile.)",
    .ability (.keyword .menace),
    .alternative [
      .name "Meager Meal",
      .manaCost [.mono .black],
      .type .sorcery,
      .subtype .adventure,
      .action (.effect (Effect.plusOneUpToOneAndPlayerGainsLife 2)),
      .oracleText "Put a +1/+1 counter on up to one target creature. Target player gains 2 life. (Then exile this card. You may cast the creature later from exile.)"
    ]
  ]

def bilbosDeadlySlice : CardDef :=
  traditional [
    .name "Bilbo's Deadly Slice",
    .manaCost [.generic 1, .mono .black, .mono .black],
    .type .instant,
    .action (.effect (Effect.destroyCreature)),
    .oracleText "Destroy target creature."
  ]

def dreadedBatCloud : CardDef :=
  traditional [
    .name "Dreaded Bat-Cloud",
    .manaCost [.generic 4, .mono .black],
    .type .creature,
    .subtype .bat,
    .power 4,
    .toughness 2,
    .oracleText "This spell costs {3} less to cast if a creature died this turn.\nFlying, deathtouch",
    .ability (.keyword .deathtouch),
    .ability (.keyword .flying),
    .costReductionIfCreatureDied 3
  ]

def crudeBentBlade : CardDef :=
  traditional [
    .name "Crude Bent Blade",
    .manaCost [.generic 2, .mono .black],
    .type .artifact,
    .subtype .equipment,
    .oracleText "When this Equipment enters, target opponent sacrifices a creature of their choice.\nEquipped creature gets +2/+1.\nEquip {2} ({2}: Attach to target creature you control. Equip only as a sorcery.)",
    .equip [.generic 2],
    .triggered (.onEnterTargetOpponentSacrificesCreature),
    .static (.equippedCreatureGets 2 1)
  ]

def gollumTheAbandoned : CardDef :=
  traditional [
    .name "Gollum the Abandoned",
    .manaCost [.generic 1, .mono .black],
    .type .creature,
    .supertype .legendary,
    .subtype .halfling,
    .subtype .horror,
    .power 2,
    .toughness 2,
    .oracleText "Gollum can't block.\nWhen Gollum enters, exile up to one target card from an opponent's graveyard. Each opponent loses 2 life.\n{2}, Sacrifice an artifact or creature: Return this card from your graveyard to your hand. Activate only as a sorcery.",
    .triggered (.onEnterExileOppGyCardOppsLoseLife 2),
    .static (.cantBlockUnlessYouControl #[]),
    .ability (.activated ([.mana [.generic 2], .sacrificeAnotherCreatureOrArtifact, .onlyAsSorcery, .activateFromGraveyard]) (.effect (Effect.returnFromGraveyardToHand)))
  ]

def gnashingOfTeeth : CardDef :=
  traditional [
    .name "Gnashing of Teeth",
    .manaCost [.generic 1, .mono .black, .mono .black],
    .type .sorcery,
    .oracleText "Choose one —\n• Target creature gets -5/-5 until end of turn. If that creature would die this turn, exile it instead.\n• Creatures target player controls get -1/-1 until end of turn.",
    .chooseOne [Effect.pumpAndExileIfDies (-5) (-5), Effect.creaturesTargetPlayerGet (-1) (-1)]
  ]

def reverentHowl : CardDef :=
  traditional [
    .name "Reverent Howl",
    .manaCost [.generic 2, .mono .black],
    .type .instant,
    .oracleText "Choose one —\n• Target player draws two cards and loses 2 life.\n• Target creature gets +2/+2 and gains lifelink until end of turn.",
    .chooseOne [Effect.targetPlayerDrawLoseLife 2 2, Effect.pumpAndLifelink 2 2]
  ]

def stonyVoicedGoblins : CardDef :=
  traditional [
    .name "Stony-Voiced Goblins",
    .manaCost [.generic 1, .mono .black],
    .type .creature,
    .subtype .goblin,
    .subtype .bard,
    .power 1,
    .toughness 1,
    .oracleText "When this creature enters, each opponent discards a card.",
    .triggered (.onEnterEachOpponentDiscards)
  ]

def smaugTheGreatCalamity : CardDef :=
  traditional [
    .name "Smaug, the Great Calamity",
    .manaCost [.generic 5, .mono .red, .mono .red],
    .type .creature,
    .supertype .legendary,
    .subtype .dragon,
    .power 5,
    .toughness 5,
    .oracleText "Flying\n//ADV//\nSpew Flame {4}{R}\nSorcery — Adventure\nSpew Flame deals 5 damage to target creature. (Then exile this card. You may cast the creature later from exile.)",
    .ability (.keyword .flying),
    .alternative [
      .name "Spew Flame",
      .manaCost [.generic 4, .mono .red],
      .type .sorcery,
      .subtype .adventure,
      .action (.effect (Effect.dealDamageToCreature 5)),
      .oracleText "Spew Flame deals 5 damage to target creature. (Then exile this card. You may cast the creature later from exile.)"
    ]
  ]

def gandalfSparkStarter : CardDef :=
  traditional [
    .name "Gandalf, Spark Starter",
    .manaCost [.generic 4, .mono .red, .mono .red],
    .type .creature,
    .supertype .legendary,
    .subtype .avatar,
    .subtype .wizard,
    .power 4,
    .toughness 3,
    .oracleText "Reach\nWhen Gandalf enters, he deals 3 damage divided as you choose among one, two, or three targets.",
    .ability (.keyword .reach),
    .triggered (.onEnterDealDividedDamage 3 3)
  ]

def raggedShortSpear : CardDef :=
  traditional [
    .name "Ragged Short Spear",
    .manaCost [.generic 1, .mono .red],
    .type .artifact,
    .subtype .equipment,
    .oracleText "When this Equipment enters, you may discard a card. If you do, draw two cards.\nEquipped creature gets +2/+0.\nEquip {3} ({3}: Attach to target creature you control. Equip only as a sorcery.)",
    .equip [.generic 3],
    .triggered (.onEnterMayDiscardDraw 2),
    .static (.equippedCreatureGets 2 0)
  ]

def snowslopeHunter : CardDef :=
  traditional [
    .name "Snowslope Hunter",
    .manaCost [.generic 2, .mono .red],
    .type .creature,
    .subtype .goblin,
    .subtype .ranger,
    .power 2,
    .toughness 3,
    .oracleText "Sacrifice another creature or artifact: Exile the top card of your library. You may play it until the end of your next turn. Activate only during your turn and only once each turn.",
    .ability (.activated ([.sacrificeAnotherCreatureOrArtifact, .onlyDuringYourTurn, .onceEachTurn]) (.effect (Effect.exileTopPlayUntilEndOfNextTurn)))
  ]

def guardianOfTheHalls : CardDef :=
  traditional [
    .name "Guardian of the Halls",
    .manaCost [.generic 1, .mono .green],
    .type .creature,
    .subtype .elf,
    .subtype .soldier,
    .power 2,
    .toughness 2,
    .oracleText "Trample\n{5}{G}{G}: Put three +1/+1 counters on this creature.",
    .ability (.keyword .trample),
    .ability (.activated ([.mana [.generic 5, .mono .green, .mono .green]]) (.effect (Effect.putPlusOnePlusOneOnSource 3)))
  ]

def quarrel : CardDef :=
  traditional [
    .name "Quarrel",
    .manaCost [.generic 1, .mono .green],
    .type .instant,
    .action (.effect (Effect.creatureYouControlDealsPowerToOppCreature)),
    .oracleText "Target creature you control deals damage equal to its power to target creature an opponent controls."
  ]

def galionElvenkingsButler : CardDef :=
  traditional [
    .name "Galion, Elvenking's Butler",
    .manaCost [.generic 2, .mono .green, .mono .green],
    .type .creature,
    .supertype .legendary,
    .subtype .elf,
    .subtype .advisor,
    .power 4,
    .toughness 4,
    .oracleText "Whenever Galion attacks, choose up to one other target creature you control. Its base power and toughness become equal to Galion's power and toughness until end of turn.",
    .triggered (.onAttackSetOtherBasePT)
  ]

def wargTactics : CardDef :=
  traditional [
    .name "Warg Tactics",
    .manaCost [.generic 1, .mono .green],
    .type .instant,
    .oracleText "Choose one —\n• Destroy target creature with flying.\n• Put a +1/+1 counter on target creature you control. It gains trample and hexproof until end of turn. (It can't be the target of spells or abilities your opponents control.)",
    .chooseOne [Effect.destroyCreatureWithFlying, Effect.plusOnePlusOneTrampleHexproof]
  ]

def beornsHospitality : CardDef :=
  traditional [
    .name "Beorn's Hospitality",
    .manaCost [.generic 1, .mono .green],
    .type .enchantment,
    .oracleText "Landfall — Whenever a land you control enters, put a +1/+1 counter on target creature you control.\n{5}{G}{G}: This enchantment becomes a Bear creature in addition to its other types and gains \"This creature's power and toughness are each equal to the number of lands you control.\" (This effect doesn't end.)",
    .triggered (.onLandYouControlEntersPlusOnePlusOne),
    .ability (.activated ([.mana [.generic 5, .mono .green, .mono .green]]) (.effect (Effect.becomeSubtypeWithLandsPT "Bear")))
  ]

def woodlandWeavemaster : CardDef :=
  traditional [
    .name "Woodland Weavemaster",
    .manaCost [.generic 1, .mono .green],
    .type .creature,
    .subtype .elf,
    .subtype .druid,
    .power 1,
    .toughness 2,
    .oracleText "Vigilance\nWhenever another Elf you control enters, this creature gets +1/+1 until end of turn.\n{T}: Add X mana of any one color, where X is this creature's power. Spend this mana only to cast Elf spells and activate abilities of Elf sources.",
    .ability (.keyword .vigilance),
    .triggered (.onAnotherElfYouControlEntersGets1),
    .tapAddAnyColorEqualToPower
  ]

def mirkwoodPathmaker : CardDef :=
  traditional [
    .name "Mirkwood Pathmaker",
    .type .creature,
    .manaCost [.generic 2, .mono .green],
    .subtype .elf,
    .subtype .ranger,
    .oracleText "Mirkwood Pathmaker's power and toughness are each equal to the number of lands you control.",
    .static (.powerToughnessEqualLandsYouControl)
  ]

def beornReluctantHost : CardDef :=
  traditional [
    .name "Beorn, Reluctant Host",
    .manaCost [.generic 4, .mono .green],
    .type .creature,
    .supertype .legendary,
    .subtype .human,
    .subtype .bear,
    .subtype .shapeshifter,
    .power 5,
    .toughness 5,
    .oracleText "Trample\n//ADV//\nTill and Tend {1}{G}\nSorcery — Adventure\nYou may play an additional land this turn. (Then exile this card. You may cast the creature later from exile.)",
    .ability (.keyword .trample),
    .alternative [
      .name "Till and Tend",
      .manaCost [.generic 1, .mono .green],
      .type .sorcery,
      .subtype .adventure,
      .action (.effect (Effect.playAdditionalLandThisTurn)),
      .oracleText "You may play an additional land this turn. (Then exile this card. You may cast the creature later from exile.)"
    ]
  ]

def woodElves : CardDef :=
  traditional [
    .name "Wood Elves",
    .manaCost [.generic 2, .mono .green],
    .type .creature,
    .subtype .elf,
    .subtype .scout,
    .power 1,
    .toughness 1,
    .oracleText "When this creature enters, search your library for a Forest card, put that card onto the battlefield, then shuffle.",
    .triggered (.onEnterSearchForest)
  ]

def attercop : CardDef :=
  traditional [
    .name "Attercop",
    .manaCost [.generic 1, .mono .green],
    .type .creature,
    .subtype .spider,
    .power 2,
    .toughness 1,
    .oracleText "Reach, deathtouch\nLandfall — Whenever a land you control enters, this creature gets +1/+1 until end of turn.",
    .ability (.keyword .reach),
    .ability (.keyword .deathtouch),
    .triggered (.onLandYouControlEntersGets 1 1)
  ]

def ordinaryBear : CardDef :=
  traditional [
    .name "Ordinary Bear",
    .manaCost [.generic 3, .mono .green],
    .type .creature,
    .subtype .bear,
    .power 4,
    .toughness 5
  ]

def largeBear : CardDef :=
  traditional [
    .name "Large Bear",
    .manaCost [.generic 3, .hybrid .black .green, .hybrid .black .green],
    .type .creature,
    .subtype .bear,
    .power 5,
    .toughness 5,
    .oracleText "Reach, trample, haste",
    .ability (.keyword .reach),
    .ability (.keyword .trample),
    .ability (.keyword .haste)
  ]

def littleBear : CardDef :=
  traditional [
    .name "Little Bear",
    .manaCost [.generic 2, .mono .green],
    .type .creature,
    .subtype .bear,
    .power 3,
    .toughness 2,
    .oracleText "Flash\nWhen this creature enters, untap another target creature you control. If that creature is a Bear, put a +1/+1 counter on it.",
    .ability (.keyword .flash),
    .triggered (.onEnterUntapOtherPlusOneIfSubtype "Bear")
  ]

def elvenkingsHarper : CardDef :=
  traditional [
    .name "Elvenking's Harper",
    .manaCost [.generic 1, .mono .blue],
    .type .creature,
    .subtype .elf,
    .subtype .bard,
    .power 2,
    .toughness 2,
    .oracleText "{4}{U}: Target creature can't be blocked this turn.",
    .ability (.activated ([.mana [.generic 4, .mono .blue]]) (.effect (Effect.targetCantBeBlockedThisTurn)))
  ]

def smaugsFury : CardDef :=
  traditional [
    .name "Smaug's Fury",
    .manaCost [.generic 1, .mono .red],
    .type .instant,
    .action (.effect (Effect.pumpAndGrantKeywords 3 0 (Keyword.reach.merge Keyword.firstStrike))),
    .oracleText "Target creature gets +3/+0 and gains reach and first strike until end of turn."
  ]

def wellWornSpatula : CardDef :=
  traditional [
    .name "Well-Worn Spatula",
    .manaCost [.generic 1],
    .type .artifact,
    .subtype .equipment,
    .oracleText "When this Equipment enters, you gain 2 life.\nEquipped creature gets +1/+1.\nEquip {1} ({1}: Attach to target creature you control. Equip only as a sorcery.)",
    .equip [.generic 1],
    .triggered (.onEnterGainLife 2),
    .static (.equippedCreatureGets 1 1)
  ]

/-- Dual land: enters tapped; `{T}: Add {A} or {B}`; tap, pay, and sacrifice
for two +1/+1 counters on a typed creature you control. One type or several
types both use `plusOneOnTarget`. The Oracle text is reconstructed from the
colors and creature types. -/
def hobbitDualLand (name : String) (a b : Color) (creatureTypes : Array String) :
    CardDef :=
  traditional [
    .name name,
    .type .land,
    .entersTapped,
    .tapAddOneOf [.colored a, .colored b],
    .ability (.activated
      ([.mana [.generic 2, .mono a, .mono b], .tap, .sacrificeSource, .onlyAsSorcery])
      (.effect (Effect.plusOneOnTarget 2 creatureTypes))),
    .oracleText
      (s!"This land enters tapped.\n{dualAddClause a b}\n" ++
        s!"\{2}{manaSymbolsText #[.colored a, .colored b]}, \{T}, Sacrifice this land: " ++
        s!"Put two +1/+1 counters on target {orJoin creatureTypes.toList} you control. " ++
        "Activate only as a sorcery.")
  ]

def elvenkingsHalls : CardDef :=
  hobbitDualLand "Elvenking's Halls" .green .blue #["Elf"]

def ironHills : CardDef :=
  hobbitDualLand "Iron Hills" .red .white #["Dwarf"]

def lakeTown : CardDef :=
  hobbitDualLand "Lake-town" .white .blue #["Human"]

def goblinTown : CardDef :=
  hobbitDualLand "Goblin-town" .black .red #["Goblin", "Orc"]

def mirkwood : CardDef :=
  hobbitDualLand "Mirkwood" .black .green #["Bear", "Spider", "Wolf"]

def hobbitHole : CardDef :=
  traditional [
    .name "Hobbit Hole",
    .type .land,
    .oracleText "{T}, Sacrifice this land: Search your library for a basic land card, put it onto the battlefield tapped, then shuffle.\nHalflingcycling {4} ({4}, Discard this card: Search your library for a Halfling card, reveal it, put it into your hand, then shuffle.)",
    .ability (.activated ([.tap, .sacrificeSource]) (.effect (Effect.searchBasicLandTapped))),
    .ability (.activated ([.mana [.generic 4], .discardSource, .activateFromHand]) (.effect (Effect.searchLandTypeToHand "Halfling")))
  ]

def nighthowlPursuer : CardDef :=
  traditional [
    .name "Nighthowl Pursuer",
    .manaCost [.mono .black],
    .type .creature,
    .subtype .wolf,
    .power 1,
    .toughness 1,
    .oracleText "Menace (This creature can't be blocked except by two or more creatures.)\nFerocious — Whenever this creature attacks while you control a creature with power 4 or greater, this creature gets +2/+2 until end of turn.",
    .ability (.keyword .menace),
    .triggered (.onAttackFerociousSourceGets 2 2)
  ]

def wargling : CardDef :=
  traditional [
    .name "Wargling",
    .manaCost [.generic 1, .mono .green],
    .type .creature,
    .subtype .wolf,
    .power 2,
    .toughness 2,
    .oracleText "Ferocious — Whenever this creature attacks while you control a creature with power 4 or greater, until end of turn, this creature gets +1/+0 and creatures you control gain trample.",
    .triggered (.onAttackFerociousSourceGetsAndTeamTrample 1)
  ]

def wilderlandScrounger : CardDef :=
  traditional [
    .name "Wilderland Scrounger",
    .manaCost [.generic 4, .mono .green],
    .type .creature,
    .subtype .wolf,
    .power 3,
    .toughness 6,
    .oracleText "Ferocious — Whenever this creature attacks while you control a creature with power 4 or greater, put a +1/+1 counter on each creature you control.",
    .triggered (.onAttackFerociousPlusOneEach)
  ]

def nastyLittleRabbit : CardDef :=
  traditional [
    .name "Nasty Little Rabbit",
    .manaCost [.mono .green],
    .type .creature,
    .subtype .rabbit,
    .power 1,
    .toughness 2,
    .oracleText "Ferocious — At the beginning of combat on your turn, if you control a creature with power 4 or greater, put a +1/+1 counter on this creature.",
    .triggered (.onYourBeginCombatFerociousPlusOne)
  ]

def theChiefWarg : CardDef :=
  traditional [
    .name "The Chief Warg",
    .manaCost [.generic 2, .mono .black, .mono .green],
    .type .creature,
    .supertype .legendary,
    .subtype .wolf,
    .power 3,
    .toughness 3,
    .oracleText "Menace (This creature can't be blocked except by two or more creatures.)\nFerocious — Whenever you attack while you control a creature with power 4 or greater, you draw a card and lose 1 life.",
    .ability (.keyword .menace),
    .triggered (.onYouAttackFerociousDrawLoseLife)
  ]

def thorinsLastStand : CardDef :=
  traditional [
    .name "Thorin's Last Stand",
    .manaCost [.generic 2, .mono .white, .mono .white],
    .type .instant,
    .oracleText "Choose one —\n• Creatures you control get +2/+1 until end of turn.\n• Destroy target artifact or enchantment. You gain 2 life.",
    .chooseOne [Effect.creaturesYouControlGet 2 1, Effect.destroyArtifactOrEnchantmentGainLife 2]
  ]

def stoneBySunlight : CardDef :=
  traditional [
    .name "Stone by Sunlight",
    .manaCost [.generic 1, .mono .white],
    .type .instant,
    .oracleText "Choose one —\n• Destroy target creature with power 4 or greater.\n• Until end of turn, target creature becomes an artifact in addition to its other types and gains indestructible. (Damage and effects that say \"destroy\" don't destroy it.)",
    .chooseOne [Effect.destroyCreaturePowerAtLeast 4, Effect.becomeArtifactGainIndestructible]
  ]

def duskwatchHunter : CardDef :=
  traditional [
    .name "Duskwatch Hunter",
    .manaCost [.generic 2, .hybrid .black .green],
    .type .creature,
    .subtype .wolf,
    .power 3,
    .toughness 1,
    .oracleText "This creature can't be blocked by tokens.\nWhen this creature enters, put a +1/+1 counter on target creature.",
    .triggered (.onEnterPlusOneOnCreature),
    .static (.cantBeBlockedByTokens)
  ]

def patientInstructor : CardDef :=
  traditional [
    .name "Patient Instructor",
    .manaCost [.generic 2, .hybrid .white .blue],
    .type .creature,
    .subtype .human,
    .subtype .citizen,
    .power 2,
    .toughness 2,
    .oracleText "Vigilance\nWhen this creature enters, recruit. (Draw a card, then discard a card. If you discarded a nonland card, create a 1/1 white Human Soldier creature token.)",
    .ability (.keyword .vigilance),
    .triggered (.onEnterRecruit)
  ]

def longLakeNuisance : CardDef :=
  traditional [
    .name "Long Lake Nuisance",
    .manaCost [.generic 3, .mono .blue],
    .type .creature,
    .subtype .bird,
    .power 3,
    .toughness 1,
    .oracleText "Flying\nWhen this creature enters, recruit. (Draw a card, then discard a card. If you discarded a nonland card, create a 1/1 white Human Soldier creature token.)",
    .ability (.keyword .flying),
    .triggered (.onEnterRecruit)
  ]

def laketownLookout : CardDef :=
  traditional [
    .name "Lake-town Lookout",
    .manaCost [.mono .white],
    .type .creature,
    .subtype .human,
    .subtype .scout,
    .power 1,
    .toughness 1,
    .oracleText "When this creature dies, recruit. (Draw a card, then discard a card. If you discarded a nonland card, create a 1/1 white Human Soldier creature token.)",
    .triggered (.onDiesRecruit)
  ]

def giantsBoulder : CardDef :=
  traditional [
    .name "Giant's Boulder",
    .manaCost [.generic 1],
    .type .artifact,
    .oracleText "When this artifact enters, scry 2. (Look at the top two cards of your library, then put any number of them on the bottom and the rest on top in any order.)\n{1}, {T}: Add one mana of any color.\n{7}, {T}, Sacrifice this artifact: Destroy target permanent.",
    .triggered (.onEnterScry 2),
    .ability (.activated ([.mana [.generic 1], .tap]) (.effect (Effect.addAnyColor))),
    .ability (.activated ([.mana [.generic 7], .tap, .sacrificeSource]) (.effect (Effect.destroyTargetPermanent)))
  ]

def longBodiedGreyDog : CardDef :=
  traditional [
    .name "Long-Bodied Grey Dog",
    .manaCost [.generic 3],
    .type .creature,
    .subtype .dog,
    .power 2,
    .toughness 2,
    .oracleText "Flash\nReach\nWhen this creature enters, create a tapped Treasure token. (It's an artifact with \"{T}, Sacrifice this token: Add one mana of any color.\")",
    .ability (.keyword .flash),
    .ability (.keyword .reach),
    .triggered (.onEnterCreateTokens .treasure 1 true)
  ]

def doriBearerOfFriends : CardDef :=
  traditional [
    .name "Dori, Bearer of Friends",
    .manaCost [.generic 2, .mono .red],
    .type .creature,
    .supertype .legendary,
    .subtype .dwarf,
    .subtype .warrior,
    .power 3,
    .toughness 2,
    .oracleText "Trample\nWhen Dori enters, create a Treasure token. (It's an artifact with \"{T}, Sacrifice this token: Add one mana of any color.\")",
    .ability (.keyword .trample),
    .triggered (.onEnterCreateTokens .treasure 1)
  ]

def esgarothGarrison : CardDef :=
  traditional [
    .name "Esgaroth Garrison",
    .type .creature,
    .manaCost [.generic 4, .mono .white],
    .subtype .human,
    .subtype .soldier,
    .oracleText "Esgaroth Garrison's power is equal to the number of creatures you control.\nWhen this creature enters, recruit. (Draw a card, then discard a card. If you discarded a nonland card, create a 1/1 white Human Soldier creature token.)",
    .triggered (.onEnterRecruit),
    .static (.powerEqualCreaturesYouControl),
    .toughness 5
  ]

def gundabadOpportunist : CardDef :=
  traditional [
    .name "Gundabad Opportunist",
    .manaCost [.generic 3, .mono .red],
    .type .creature,
    .subtype .goblin,
    .subtype .rogue,
    .power 4,
    .toughness 2,
    .oracleText "When this creature enters, exile the top card of your library. Until the end of your next turn, you may play that card.",
    .triggered (.onEnterExileTop)
  ]

def giganticBigBear : CardDef :=
  traditional [
    .name "Gigantic Big Bear",
    .manaCost [.generic 5, .mono .green, .mono .green],
    .type .creature,
    .subtype .bear,
    .power 10,
    .toughness 7,
    .oracleText "This spell can't be countered.\nHexproof, haste",
    .ability (.keyword .hexproof),
    .ability (.keyword .haste),
    .cantBeCountered
  ]

def bothersomeNoisemaker : CardDef :=
  traditional [
    .name "Bothersome Noisemaker",
    .manaCost [.generic 1, .mono .red],
    .type .creature,
    .subtype .goblin,
    .subtype .bard,
    .power 2,
    .toughness 2,
    .oracleText "Whenever you cast a noncreature spell, amass Goblins 1. (Put a +1/+1 counter on an Army you control. It's also a Goblin. If you don't control an Army, create a 0/0 black Goblin Army creature token first.)",
    .triggered (.onCastNoncreatureAmassGoblins 1)
  ]

def fearsomeGoblinPair : CardDef :=
  traditional [
    .name "Fearsome Goblin Pair",
    .manaCost [.generic 2, .hybrid .black .red],
    .type .creature,
    .subtype .goblin,
    .subtype .soldier,
    .power 1,
    .toughness 1,
    .oracleText "When this creature dies, amass Goblins 4. (Put four +1/+1 counters on an Army you control. It's also a Goblin. If you don't control an Army, create a 0/0 black Goblin Army creature token first.)",
    .triggered (.onDiesAmassGoblins 4)
  ]

def goblinTownFlunkies : CardDef :=
  traditional [
    .name "Goblin-town Flunkies",
    .manaCost [.generic 1, .mono .red],
    .type .creature,
    .subtype .goblin,
    .subtype .soldier,
    .power 1,
    .toughness 1,
    .oracleText "Haste\nWhen this creature enters, amass Goblins 1. (Put a +1/+1 counter on an Army you control. It's also a Goblin. If you don't control an Army, create a 0/0 black Goblin Army creature token first.)",
    .ability (.keyword .haste),
    .triggered (.onEnterAmassGoblins 1)
  ]

def mistyMountainsRaider : CardDef :=
  traditional [
    .name "Misty Mountains Raider",
    .manaCost [.generic 4, .mono .red],
    .type .creature,
    .subtype .goblin,
    .subtype .soldier,
    .power 4,
    .toughness 4,
    .oracleText "Whenever you attack, amass Goblins 2. (Put two +1/+1 counters on an Army you control. It's also a Goblin. If you don't control an Army, create a 0/0 black Goblin Army creature token first.)",
    .triggered (.onYouAttackAmassGoblins 2)
  ]

def bardsCompany : CardDef :=
  traditional [
    .name "Bard's Company",
    .manaCost [.generic 2, .mono .white, .mono .blue],
    .type .creature,
    .subtype .human,
    .subtype .citizen,
    .power 2,
    .toughness 3,
    .oracleText "You may cast this spell as though it had flash if you control a Human.\nOther creatures you control get +1/+1.\nWhenever this creature enters or attacks, recruit. (Draw a card, then discard a card. If you discarded a nonland card, create a 1/1 white Human Soldier creature token.)",
    .triggered (.onEnterOrAttackRecruit),
    .static (.otherCreaturesGet #[] 1 1),
    .flashIfYouControlSubtype "Human"
  ]

def rageIntoTheValley : CardDef :=
  traditional [
    .name "Rage into the Valley",
    .manaCost [.generic 2, .mono .black],
    .type .sorcery,
    .action (.effect (Effect.drawLoseLifeThenAmass 2)),
    .oracleText "You draw a card and lose 1 life.\nAmass Goblins 2. (Put two +1/+1 counters on an Army you control. It's also a Goblin. If you don't control an Army, create a 0/0 black Goblin Army creature token first.)"
  ]

def gatheringOfDarkness : CardDef :=
  traditional [
    .name "Gathering of Darkness",
    .manaCost [.generic 3, .mono .black],
    .type .sorcery,
    .action (.effect (Effect.returnCreatureFromGyThenAmass 3)),
    .oracleText "Return up to one target creature card from your graveyard to your hand.\nAmass Goblins 3. (Put three +1/+1 counters on an Army you control. It's also a Goblin. If you don't control an Army, create a 0/0 black Goblin Army creature token first.)"
  ]

def soundTheTrumpets : CardDef :=
  traditional [
    .name "Sound the Trumpets",
    .manaCost [.generic 1, .mono .blue, .mono .blue],
    .type .instant,
    .action (.effect (Effect.counterThenRecruitIfMvAtMost 2)),
    .oracleText "Counter target spell. If that spell's mana value was 2 or less, recruit. (Draw a card, then discard a card. If you discarded a nonland card, create a 1/1 white Human Soldier creature token.)"
  ]

def fatefulDiscovery : CardDef :=
  traditional [
    .name "Fateful Discovery",
    .manaCost [.generic 3, .mono .blue, .mono .blue],
    .type .enchantment,
    .oracleText "Whenever an artifact you control enters, draw a card.",
    .triggered (.onArtifactYouControlEntersDraw)
  ]

def chiefWargsCompany : CardDef :=
  traditional [
    .name "Chief Warg's Company",
    .manaCost [.generic 1, .mono .black, .mono .green],
    .type .creature,
    .subtype .wolf,
    .power 5,
    .toughness 3,
    .oracleText "Trample\nThis creature can't attack unless you control two or more other Wolves.\nAt the beginning of your upkeep, create a 2/2 green Wolf creature token.",
    .ability (.keyword .trample),
    .triggered (.onYourUpkeepCreateTokens .wolf 1),
    .static (.cantAttackUnlessYouControlNOther 2 "Wolf")
  ]

def dwarvenShortsword : CardDef :=
  traditional [
    .name "Dwarven Shortsword",
    .manaCost [.generic 3, .mono .white],
    .type .artifact,
    .subtype .equipment,
    .oracleText "When this Equipment enters, create a 2/2 red Dwarf creature token, then attach this Equipment to it.\nEquipped creature gets +1/+2.\nEquip {2} ({2}: Attach to target creature you control. Equip only as a sorcery.)",
    .equip [.generic 2],
    .triggered (.onEnterCreateThenAttach .dwarf),
    .static (.equippedCreatureGets 1 2)
  ]

def goblinPlateMail : CardDef :=
  traditional [
    .name "Goblin Plate Mail",
    .manaCost [.generic 1, .hybrid .black .red],
    .type .artifact,
    .subtype .equipment,
    .oracleText "When this Equipment enters, amass Goblins 1, then attach this Equipment to the amassed Army. (To amass Goblins 1, put a +1/+1 counter on an Army you control. It's also a Goblin. If you don't control an Army, create a 0/0 black Goblin Army creature token first.)\nEquipped creature gets +1/+0 and has menace.\nEquip {4}",
    .equip [.generic 4],
    .triggered (.onEnterAmassThenAttach 1),
    .static (.equippedCreatureGetsAndHas 1 0 Keyword.menace)
  ]

def momentOfGlory : CardDef :=
  traditional [
    .name "Moment of Glory",
    .manaCost [.mono .white],
    .type .sorcery,
    .action (.effect (Effect.plusOneThenEachOtherIfFromGy)),
    .oracleText "Put a +1/+1 counter on target creature you control. If this spell was cast from a graveyard, also put a +1/+1 counter on each other creature you control.\nFlashback {4}{W} (You may cast this card from your graveyard for its flashback cost. Then exile it.)",
    .flashback [.generic 4, .mono .white]
  ]

def plunderTheTrollshaws : CardDef :=
  traditional [
    .name "Plunder the Trollshaws",
    .manaCost [.generic 1, .mono .blue],
    .type .instant,
    .action (.effect (Effect.drawIfFromGy 1 2)),
    .oracleText "Draw a card. If this spell was cast from a graveyard, draw two cards instead.\nFlashback {3}{U} (You may cast this card from your graveyard for its flashback cost. Then exile it.)",
    .flashback [.generic 3, .mono .blue]
  ]

def tidingsOfWar : CardDef :=
  traditional [
    .name "Tidings of War",
    .manaCost [.mono .red],
    .type .sorcery,
    .action (.effect (Effect.amassGoblinsOrFromGy 1 3)),
    .oracleText "Amass Goblins 1. If this spell was cast from a graveyard, amass Goblins 3 instead. (To amass Goblins X, put X +1/+1 counters on an Army you control. It's also a Goblin. If you don't control an Army, create a 0/0 black Goblin Army creature token first.)\nFlashback {3}{R} (You may cast this card from your graveyard for its flashback cost. Then exile it.)",
    .flashback [.generic 3, .mono .red]
  ]

def eaglesRescue : CardDef :=
  traditional [
    .name "Eagle's Rescue",
    .manaCost [.generic 2, .hybrid .white .blue, .hybrid .white .blue],
    .type .enchantment,
    .oracleText "Enchant creature\nEnchanted creature gets +2/+2 and has flying.\n{2}{W/U}{W/U}: Return this card from your graveyard to the battlefield attached to target creature you control with power 1 or less. Activate only as a sorcery.",
    .static (.enchantedCreatureGetsAndHas 2 2 Keyword.flying),
    .ability (.activated ([.mana [.generic 2, .hybrid .white .blue, .hybrid .white .blue], .onlyAsSorcery, .activateFromGraveyard]) (.effect (Effect.returnFromGyAttachPowerAtMost 1))),
    .subtype .aura
  ]

def gandalfWanderingWizard : CardDef :=
  traditional [
    .name "Gandalf, Wandering Wizard",
    .manaCost [.generic 4, .mono .blue],
    .type .creature,
    .supertype .legendary,
    .subtype .avatar,
    .subtype .wizard,
    .power 4,
    .toughness 5,
    .oracleText "Ward {3} (Whenever this creature becomes the target of a spell or ability an opponent controls, counter it unless that player pays {3}.)\n{6}: Gandalf's owner shuffles him into their library and draws three cards.",
    .ability (.activated ([.mana [.generic 6]]) (.effect (Effect.ownerShuffleSourceDraw 3))),
    .ward 3
  ]

def trollNegotiations : CardDef :=
  traditional [
    .name "Troll Negotiations",
    .manaCost [.generic 2, .mono .green, .mono .green],
    .type .sorcery,
    .action (.effect (Effect.plusOneThenFight 2)),
    .oracleText "Put two +1/+1 counters on target creature you control. Then it fights target creature an opponent controls. (Each deals damage equal to its power to the other.)"
  ]

def dwarvenMattock : CardDef :=
  traditional [
    .name "Dwarven Mattock",
    .manaCost [.generic 2],
    .type .artifact,
    .subtype .equipment,
    .oracleText "When this Equipment enters, attach it to target Dwarf you control.\nEquipped creature gets +2/+2 and has ward {1}. (Whenever equipped creature becomes the target of a spell or ability an opponent controls, counter it unless that player pays {1}.)\nEquip {3} ({3}: Attach to target creature you control. Equip only as a sorcery.)",
    .equip [.generic 3],
    .triggered (.onEnterAttachToSubtype "Dwarf"),
    .static (.equippedCreatureGetsAndWard 2 2 1)
  ]

def greatUglyLookingGoblin : CardDef :=
  traditional [
    .name "Great Ugly-Looking Goblin",
    .manaCost [.generic 5, .mono .black],
    .type .creature,
    .subtype .goblin,
    .subtype .soldier,
    .power 4,
    .toughness 4,
    .oracleText "Each creature you control with a +1/+1 counter on it has menace. (It can't be blocked except by two or more creatures.)\n//ADV//\nClap! Snap! {1}{B}\nSorcery — Adventure\nAmass Goblins 2. (Then exile this card. You may cast the creature later from exile.)",
    .static (.creaturesYouControlWithPlusOneHaveMenace),
    .alternative [
      .name "Clap! Snap!",
      .manaCost [.generic 1, .mono .black],
      .type .sorcery,
      .subtype .adventure,
      .action (.effect (Effect.amassGoblins 2)),
      .oracleText "Amass Goblins 2. (Then exile this card. You may cast the creature later from exile.)"
    ]
  ]

def theArkenstone : CardDef :=
  traditional [
    .name "The Arkenstone",
    .type .artifact,
    .manaCost [.generic 5],
    .oracleText "Creatures you control get +1/+1.\nAt the beginning of your end step, draw a card.\n//ADV//\nSeek the Heart {2}{W}\nSorcery — Adventure\nSearch your library for a legendary creature card, reveal it, put it into your hand, then shuffle. (Then exile this card. You may cast the artifact later from exile.)",
    .triggered (.onYourEndStepDraw),
    .static (.creaturesYouControlGet 1 1),
    .alternative [
      .name "Seek the Heart",
      .manaCost [.generic 2, .mono .white],
      .type .sorcery,
      .subtype .adventure,
      .action (.effect (Effect.searchLegendaryCreatureToHand)),
      .oracleText "Search your library for a legendary creature card, reveal it, put it into your hand, then shuffle. (Then exile this card. You may cast the artifact later from exile.)"
    ],
    .supertype .legendary
  ]

def bolgsCompany : CardDef :=
  traditional [
    .name "Bolg's Company",
    .manaCost [.mono .black, .mono .red],
    .type .creature,
    .subtype .goblin,
    .subtype .soldier,
    .power 2,
    .toughness 2,
    .oracleText "This creature has haste as long as you control another Goblin.\n{T}, Sacrifice another Goblin: Add {B}{R}.",
    .static (.hasteIfYouControlOtherSubtype "Goblin"),
    .ability (.activated ([.tap, .sacrificeAnotherSubtype "Goblin"]) (.effect (Effect.addMana #[.colored .black, .colored .red])))
  ]

def noriTellerOfTales : CardDef :=
  traditional [
    .name "Nori, Teller of Tales",
    .manaCost [.generic 1, .hybrid .red .white],
    .type .creature,
    .supertype .legendary,
    .subtype .dwarf,
    .subtype .bard,
    .power 2,
    .toughness 2,
    .oracleText "Whenever Nori attacks, target attacking creature gains first strike until end of turn.",
    .triggered (.onAttackTargetGainsKeywords Keyword.firstStrike)
  ]

def theLordOfTheEagles : CardDef :=
  traditional [
    .name "The Lord of the Eagles",
    .manaCost [.generic 7, .mono .blue, .mono .blue],
    .type .creature,
    .supertype .legendary,
    .subtype .bird,
    .subtype .noble,
    .power 8,
    .toughness 8,
    .oracleText "Flash\nThis spell costs {X} less to cast, where X is the total power of creatures you control with flying.\nFlying",
    .ability (.keyword .flash),
    .ability (.keyword .flying),
    .costReductionEqualFlyingPower
  ]

def throrsMap : CardDef :=
  traditional [
    .name "Thrór's Map",
    .manaCost [.generic 2],
    .type .artifact,
    .oracleText "When Thrór's Map enters, search your library for a basic land card, reveal it, put it into your hand, then shuffle.\n{2}, {T}: Draw a card, then discard a card.",
    .triggered (.onEnterSearchBasicToHand),
    .ability (.activated ([.mana [.generic 2], .tap]) (.effect (Effect.abilityDrawThenDiscard 1))),
    .supertype .legendary
  ]

def theBlackArrow : CardDef :=
  traditional [
    .name "The Black Arrow",
    .manaCost [.generic 3],
    .type .artifact,
    .subtype .equipment,
    .supertype .legendary,
    .oracleText "Flash\nWhen The Black Arrow enters, it deals 1 damage to any target. If a Dragon is dealt damage this way, destroy it.\nEquipped creature gets +1/+1 and has reach.\nEquip {1} ({1}: Attach to target creature you control. Equip only as a sorcery.)",
    .equip [.generic 1],
    .ability (.keyword .flash),
    .triggered (.onEnterDealDamageDestroyIfSubtype 1 "Dragon"),
    .static (.equippedCreatureGetsAndHas 1 1 Keyword.reach)
  ]

def smaugTheMagnificent : CardDef :=
  traditional [
    .name "Smaug the Magnificent",
    .manaCost [.generic 2, .mono .red, .mono .red],
    .type .creature,
    .supertype .legendary,
    .subtype .dragon,
    .power 4,
    .toughness 3,
    .oracleText "Flying, haste\nWhenever Smaug attacks, he deals damage equal to the number of Treasures you control to any target.\nAt the beginning of your upkeep, create a Treasure token.",
    .ability (.keyword .flying),
    .ability (.keyword .haste),
    .triggered (.onAttackDamageEqualTreasures),
    .triggered (.onYourUpkeepCreateTokens .treasure 1)
  ]

def theQueenOfDale : CardDef :=
  traditional [
    .name "The Queen of Dale",
    .manaCost [.generic 1, .mono .white],
    .type .creature,
    .supertype .legendary,
    .subtype .human,
    .subtype .noble,
    .power 2,
    .toughness 1,
    .oracleText "Whenever an opponent casts their first noncreature spell each turn, you recruit. (Draw a card, then discard a card. If you discarded a nonland card, create a 1/1 white Human Soldier creature token.)",
    .triggered (.onOpponentCastsFirstNoncreatureRecruit)
  ]

def oriKeeperOfSongs : CardDef :=
  traditional [
    .name "Ori, Keeper of Songs",
    .manaCost [.generic 2, .mono .white],
    .type .creature,
    .supertype .legendary,
    .subtype .dwarf,
    .subtype .bard,
    .power 3,
    .toughness 3,
    .oracleText "Storied (If you control three or more artifacts, legendaries, and/or Sagas, you have an enduring story for the rest of the game.)\nAs long as you have an enduring story, Ori gets +1/+0 and has vigilance.",
    .ability (.keyword .storied),
    .static (.getsAndHasIfEnduringStory 1 0 Keyword.vigilance)
  ]

def oinTheBrave : CardDef :=
  traditional [
    .name "Óin the Brave",
    .manaCost [.generic 1, .mono .red],
    .type .creature,
    .supertype .legendary,
    .subtype .dwarf,
    .subtype .warrior,
    .power 1,
    .toughness 3,
    .oracleText "Storied (If you control three or more artifacts, legendaries, and/or Sagas, you have an enduring story for the rest of the game.)\nAs long as you have an enduring story, Óin gets +1/+0 and has haste.\n{1}, {T}, Discard a card: Draw a card.",
    .ability (.keyword .storied),
    .static (.getsAndHasIfEnduringStory 1 0 Keyword.haste),
    .ability (.activated ([.mana [.generic 1], .tap, .discardACard]) (.effect (Effect.abilityDraw 1)))
  ]

def bomburGentleDreamer : CardDef :=
  traditional [
    .name "Bombur, Gentle Dreamer",
    .manaCost [.generic 2, .mono .red],
    .type .creature,
    .supertype .legendary,
    .subtype .dwarf,
    .subtype .bard,
    .power 5,
    .toughness 3,
    .oracleText "Storied (If you control three or more artifacts, legendaries, and/or Sagas, you have an enduring story for the rest of the game.)\nBombur doesn't untap during your untap step unless you have an enduring story.",
    .ability (.keyword .storied),
    .static (.doesntUntapUnlessEnduringStory)
  ]

def filiThePathfinder : CardDef :=
  traditional [
    .name "Fíli the Pathfinder",
    .manaCost [.generic 3, .mono .white],
    .type .creature,
    .supertype .legendary,
    .subtype .dwarf,
    .subtype .scout,
    .power 2,
    .toughness 2,
    .oracleText "Storied (If you control three or more artifacts, legendaries, and/or Sagas, you have an enduring story for the rest of the game.)\nAs long as you have an enduring story, creatures you control get +1/+1.\nWhenever Fíli or another nontoken Dwarf you control enters, create a 2/2 red Dwarf creature token.",
    .ability (.keyword .storied),
    .triggered (.onThisOrNontokenSubtypeEntersCreateTokens "Dwarf" .dwarf 1),
    .static (.creaturesYouControlGetIfEnduringStory 1 1)
  ]

def thorinOakenshield : CardDef :=
  traditional [
    .name "Thorin Oakenshield",
    .manaCost [.mono .red, .mono .white],
    .type .creature,
    .supertype .legendary,
    .subtype .dwarf,
    .subtype .noble,
    .power 3,
    .toughness 2,
    .oracleText "Trample\nStoried (If you control three or more artifacts, legendaries, and/or Sagas, you have an enduring story for the rest of the game.)\nAs long as you have an enduring story, artifacts and creatures you control have ward {1}.",
    .ability (.keyword .trample),
    .ability (.keyword .storied),
    .static (.artifactsAndCreaturesHaveWardIfEnduringStory 1)
  ]

def dainLordOfTheIronHills : CardDef :=
  traditional [
    .name "Dáin, Lord of the Iron Hills",
    .manaCost [.generic 1, .mono .white],
    .type .creature,
    .supertype .legendary,
    .subtype .dwarf,
    .subtype .noble,
    .power 2,
    .toughness 2,
    .oracleText "Vigilance\nStoried (If you control three or more artifacts, legendaries, and/or Sagas, you have an enduring story for the rest of the game.)\nAs long as you have an enduring story, creatures can't attack you unless their controller pays {1} for each of those creatures.",
    .ability (.keyword .vigilance),
    .ability (.keyword .storied),
    .static (.creaturesCantAttackYouUnlessPayIfEnduringStory 1)
  ]

def oldThrush : CardDef :=
  traditional [
    .name "Old Thrush",
    .manaCost [.generic 2],
    .type .creature,
    .subtype .bird,
    .power 1,
    .toughness 2,
    .oracleText "Flying\nWhen this creature enters, you gain 2 life. You may search your library for a basic land card, reveal it, then shuffle and put that card on top.",
    .ability (.keyword .flying),
    .triggered (.onEnterGainLifeSearchBasicOnTop 2)
  ]

def mostDecrepitOldBird : CardDef :=
  traditional [
    .name "Most Decrepit Old Bird",
    .manaCost [.mono .blue],
    .type .creature,
    .subtype .bird,
    .power 1,
    .toughness 1,
    .oracleText "Flying\nThreshold — This creature gets +1/+1 as long as there are seven or more cards in your graveyard.\n//ADV//\nSpeak Secrets {1}{U}\nSorcery — Adventure\nMill four cards, then put an instant or sorcery card from among them into your hand.",
    .ability (.keyword .flying),
    .static (.thresholdGets 1 1),
    .alternative [
      .name "Speak Secrets",
      .manaCost [.generic 1, .mono .blue],
      .type .sorcery,
      .subtype .adventure,
      .action (.effect (Effect.millThenPutInstantOrSorcery 4)),
      .oracleText "Mill four cards, then put an instant or sorcery card from among them into your hand."
    ]
  ]

def lakeTownMariners : CardDef :=
  traditional [
    .name "Lake-town Mariners",
    .manaCost [.generic 4, .mono .blue, .mono .blue],
    .type .creature,
    .subtype .human,
    .subtype .citizen,
    .power 6,
    .toughness 5,
    .oracleText "Vigilance\nWard {2} (Whenever this creature becomes the target of a spell or ability an opponent controls, counter it unless that player pays {2}.)\n//ADV//\nGone Fishing {3}{U}\nInstant — Adventure\nExile two target creatures and/or lands you control, then return them to the battlefield under their owner's control.",
    .ability (.keyword .vigilance),
    .alternative [
      .name "Gone Fishing",
      .manaCost [.generic 3, .mono .blue],
      .type .instant,
      .subtype .adventure,
      .action (.effect (Effect.exileThenReturnYouControl)),
      .oracleText "Exile two target creatures and/or lands you control, then return them to the battlefield under their owner's control."
    ],
    .ward 2
  ]

def pineconeStrike : CardDef :=
  traditional [
    .name "Pinecone Strike",
    .manaCost [.generic 1, .mono .red],
    .type .instant,
    .oracleText "Choose one or both —\n• Pinecone Strike deals 3 damage to target creature. If that creature would die this turn, exile it instead.\n• Destroy target artifact token.",
    .chooseOneOrBoth [Effect.dealDamageToCreatureExileIfDies 3, Effect.destroyArtifactToken]
  ]

def theLonelyMountain : CardDef :=
  traditional [
    .name "The Lonely Mountain",
    .type .land,
    .oracleText "({T}: Add {R}.)\nThis land enters tapped unless you control an Equipment.\n{4}{R}, {T}: Create a 2/2 red Dwarf creature token. This ability costs {1} less to activate for each Equipment you control. Activate only as a sorcery.",
    .ability (.activated ([.mana [.generic 4, .mono .red], .tap, .onlyAsSorcery, .costReductionPerEquipment 1]) (.effect (Effect.abilityCreateTokens .dwarf 1))),
    .subtype .mountain,
    .entersTappedUnlessEquipment
  ]

def thranduilSindarinLiege : CardDef :=
  traditional [
    .name "Thranduil, Sindarin Liege",
    .manaCost [.generic 2, .hybrid .green .blue, .hybrid .green .blue],
    .type .creature,
    .supertype .legendary,
    .subtype .elf,
    .subtype .noble,
    .power 2,
    .toughness 3,
    .oracleText "Other Elves you control get +1/+1.\nLandfall — Whenever a land you control enters, create a 1/1 green Elf creature token.\n//ADV//\nSilvan Rally {1}{G/U}{G/U}\nSorcery — Adventure\nMill four cards, then put up to two land cards from among them into your hand. (Then exile this card. You may cast the creature later from exile.)",
    .triggered (.onLandYouControlEntersCreateTokens .elf 1),
    .static (.otherCreaturesGet #["Elf"] 1 1),
    .alternative [
      .name "Silvan Rally",
      .manaCost [.generic 1, .hybrid .green .blue, .hybrid .green .blue],
      .type .sorcery,
      .subtype .adventure,
      .action (.effect (Effect.millThenPutLands 4 2)),
      .oracleText "Mill four cards, then put up to two land cards from among them into your hand. (Then exile this card. You may cast the creature later from exile.)"
    ]
  ]

def gloinTheMighty : CardDef :=
  traditional [
    .name "Glóin the Mighty",
    .manaCost [.generic 3, .mono .red],
    .type .creature,
    .supertype .legendary,
    .subtype .dwarf,
    .subtype .warrior,
    .power 4,
    .toughness 3,
    .oracleText "At the beginning of your first main phase, add {R}{R}.\n//ADV//\nEasy Pickings {2}{R}\nSorcery — Adventure\nEasy Pickings deals 1 damage to each creature your opponents control. (Then exile this card. You may cast the creature later from exile.)",
    .triggered (.onYourFirstMainAddMana #[.colored .red, .colored .red]),
    .alternative [
      .name "Easy Pickings",
      .manaCost [.generic 2, .mono .red],
      .type .sorcery,
      .subtype .adventure,
      .action (.effect (Effect.dealDamageToEachOppCreature 1)),
      .oracleText "Easy Pickings deals 1 damage to each creature your opponents control. (Then exile this card. You may cast the creature later from exile.)"
    ]
  ]

def ironHillsStalwart : CardDef :=
  traditional [
    .name "Iron Hills Stalwart",
    .manaCost [.generic 4, .mono .red],
    .type .creature,
    .subtype .dwarf,
    .subtype .warrior,
    .power 4,
    .toughness 5,
    .oracleText "Reach, trample\nWhen this creature enters, attach target Equipment you control to up to one target creature you control.",
    .ability (.keyword .reach),
    .ability (.keyword .trample),
    .triggered (.onEnterAttachTargetEquipment)
  ]

def oldFatSpider : CardDef :=
  traditional [
    .name "Old Fat Spider",
    .manaCost [.generic 4, .mono .green, .mono .green],
    .type .creature,
    .subtype .spider,
    .power 6,
    .toughness 7,
    .oracleText "Reach\nThis creature can't be blocked by creatures with power 2 or less.\nWhenever this creature becomes the target of a spell or ability an opponent controls, draw a card.",
    .ability (.keyword .reach),
    .triggered (.onBecomesTargetDraw),
    .static (.cantBeBlockedByPowerAtMost 2)
  ]

def greatGildedBoat : CardDef :=
  traditional [
    .name "Great Gilded Boat",
    .manaCost [.generic 2, .mono .blue],
    .type .artifact,
    .oracleText "Whenever you attack, recruit. (Draw a card, then discard a card. If you discarded a nonland card, create a 1/1 white Human Soldier creature token.)\nCrew 2 (Tap any number of creatures you control with total power 2 or more: This Vehicle becomes an artifact creature until end of turn.)",
    .triggered (.onYouAttackRecruit),
    .subtype .vehicle,
    .power 4,
    .toughness 4,
    .crew 2
  ]

def desolationOfSmaug : CardDef :=
  traditional [
    .name "Desolation of Smaug",
    .manaCost [.generic 2, .mono .red, .mono .red],
    .type .sorcery,
    .action (.effect (Effect.dealDamageToEachNonDragonThenAddDragonMana 3)),
    .oracleText "Desolation of Smaug deals 3 damage to each non-Dragon creature.\nAdd four mana in any combination of colors. Spend this mana only to cast Dragon spells."
  ]

def dwarvenMauler : CardDef :=
  traditional [
    .name "Dwarven Mauler",
    .manaCost [.mono .red],
    .type .creature,
    .subtype .dwarf,
    .subtype .warrior,
    .power 2,
    .toughness 1,
    .oracleText "Equip abilities you activate that target this creature cost {2} less to activate.",
    .static (.equipAbilitiesTargetingThisCostLess 2)
  ]

def myPrecious : CardDef :=
  traditional [
    .name "My Precious",
    .manaCost [.generic 3],
    .type .artifact,
    .oracleText "Equipped creature has hexproof and can't be blocked.\nEquip—{2}, Pay 2 life.\n//ADV//\nAllure of Power {1}{B}\nInstant — Adventure\nAs an additional cost to cast this spell, sacrifice a creature.\nDraw two cards. (Then exile this card. You may cast the artifact later from exile.)",
    .static (.equippedCreatureHasKeywordsAndCantBeBlocked Keyword.hexproof),
    .ability (.activated ([.mana [.generic 2], .onlyAsSorcery, .payLife 2]) (.effect (Effect.attachToTargetCreatureYouControl))),
    .alternative [
      .name "Allure of Power",
      .manaCost [.generic 1, .mono .black],
      .type .instant,
      .subtype .adventure,
      .action (.effect (Effect.draw 2)),
      .additionalCostSacrificeCreature,
      .oracleText "As an additional cost to cast this spell, sacrifice a creature.\nDraw two cards. (Then exile this card. You may cast the artifact later from exile.)"
    ],
    .supertype .legendary,
    .subtype .equipment
  ]

def troopOfPonies : CardDef :=
  traditional [
    .name "Troop of Ponies",
    .manaCost [.generic 2],
    .type .creature,
    .subtype .horse,
    .power 2,
    .toughness 1,
    .oracleText "{2}, {T}, Sacrifice this creature: Search your library for up to two basic land cards, reveal them, put one onto the battlefield tapped and the other into your hand, then shuffle.",
    .ability (.activated ([.mana [.generic 2], .tap, .sacrificeSource]) (.effect (Effect.searchTwoBasicsSplit)))
  ]

def elvenRaftSteerer : CardDef :=
  traditional [
    .name "Elven Raft-Steerer",
    .manaCost [.generic 2, .mono .blue],
    .type .creature,
    .subtype .elf,
    .subtype .pilot,
    .power 3,
    .toughness 2,
    .oracleText "Landfall — Whenever a land you control enters, choose one —\n• Tap target creature an opponent controls.\n• Untap target creature you control.",
    .triggered (.onLandYouControlEntersTapOrUntap)
  ]

def mirkwoodMeditator : CardDef :=
  traditional [
    .name "Mirkwood Meditator",
    .manaCost [.generic 2, .mono .blue],
    .type .creature,
    .subtype .elf,
    .subtype .druid,
    .power 2,
    .toughness 4,
    .oracleText "Landfall — Whenever a land you control enters, you may have this creature's base power and toughness become 4/2 until end of turn.",
    .triggered (.onLandYouControlEntersBecomePT 4 2)
  ]

def mirkwoodNurturer : CardDef :=
  traditional [
    .name "Mirkwood Nurturer",
    .manaCost [.generic 2, .hybrid .green .blue],
    .type .creature,
    .subtype .elf,
    .subtype .ranger,
    .power 3,
    .toughness 2,
    .oracleText "When this creature enters, return up to one other target permanent you control to its owner's hand. If you do, put a +1/+1 counter on this creature.",
    .triggered (.onEnterReturnOtherPlusOne)
  ]

def kiliTheResourceful : CardDef :=
  traditional [
    .name "Kíli the Resourceful",
    .manaCost [.generic 1, .mono .white],
    .type .creature,
    .supertype .legendary,
    .subtype .dwarf,
    .subtype .scout,
    .power 1,
    .toughness 2,
    .oracleText "Storied (If you control three or more artifacts, legendaries, and/or Sagas, you have an enduring story for the rest of the game.)\nAs long as you have an enduring story, you may pay {0} rather than pay the equip cost of the first equip ability you activate each turn.\nWhenever another Dwarf or Equipment you control enters, draw a card. This ability triggers only once each turn.",
    .ability (.keyword .storied),
    .triggered (.onAnotherSubtypeOrEquipmentEntersDrawOnce "Dwarf"),
    .static (.firstEquipFreeIfEnduringStory)
  ]

def dainsCompany : CardDef :=
  traditional [
    .name "Dáin's Company",
    .manaCost [.mono .red, .mono .white],
    .type .creature,
    .subtype .dwarf,
    .subtype .warrior,
    .power 2,
    .toughness 2,
    .oracleText "This creature has lifelink as long as you control another Dwarf.\nWhen this creature enters, look at the top four cards of your library. You may reveal a Dwarf or Equipment card from among them and put it into your hand. Put the rest on the bottom of your library in a random order.",
    .triggered (.onEnterLookAtTopRevealTypes 4 #["Dwarf", "Equipment"]),
    .static (.lifelinkIfYouControlOtherSubtype "Dwarf")
  ]

def smaugWickedWorm : CardDef :=
  traditional [
    .name "Smaug, Wicked Worm",
    .manaCost [.generic 3, .mono .black, .mono .red],
    .type .creature,
    .supertype .legendary,
    .subtype .dragon,
    .power 5,
    .toughness 5,
    .oracleText "Flying\nWhen Smaug enters, create X tapped Treasure tokens, where X is the number of artifacts your opponents control.\nWhenever you cast a spell, if mana from a Treasure was spent to cast it, you draw a card and lose 1 life.",
    .ability (.keyword .flying),
    .triggered (.onEnterCreateTappedTreasuresEqualOppArtifacts),
    .triggered (.onCastWithTreasureDrawLoseLife)
  ]

def glamdringFoeHammer : CardDef :=
  traditional [
    .name "Glamdring, Foe-hammer",
    .manaCost [.generic 2],
    .type .artifact,
    .subtype .equipment,
    .supertype .legendary,
    .oracleText "Instant and sorcery spells you cast cost {X} less to cast, where X is equipped creature's power.\nEquip {2}\n//ADV//\nGleam of Death {3}{U}\nSorcery — Adventure\nMill six cards, then put all instant and sorcery cards from among them into your hand. (Then exile this card. You may cast the artifact later from exile.)",
    .equip [.generic 2],
    .static (.instantSorceryCostReductionEqualEquippedPower),
    .alternative [
      .name "Gleam of Death",
      .manaCost [.generic 3, .mono .blue],
      .type .sorcery,
      .subtype .adventure,
      .action (.effect (Effect.millThenPutAllInstantsOrSorceries 6)),
      .oracleText "Mill six cards, then put all instant and sorcery cards from among them into your hand. (Then exile this card. You may cast the artifact later from exile.)"
    ]
  ]

def settleTheWreckage : CardDef :=
  traditional [
    .name "Settle the Wreckage",
    .manaCost [.generic 2, .mono .white, .mono .white],
    .type .instant,
    .action (.effect (Effect.exileAttackersSearchBasics)),
    .oracleText "Exile all attacking creatures target player controls. That player may search their library for that many basic land cards, put those cards onto the battlefield tapped, then shuffle."
  ]

def ironHillsBlacksmith : CardDef :=
  traditional [
    .name "Iron Hills Blacksmith",
    .manaCost [.generic 1, .mono .white],
    .type .creature,
    .subtype .dwarf,
    .subtype .artificer,
    .power 1,
    .toughness 1,
    .oracleText "Double strike\nWhen this creature enters, create a colorless Equipment artifact token named Axe with \"Equipped creature gets +1/+0\" and equip {2}.",
    .ability (.keyword .doubleStrike),
    .triggered (.onEnterCreateAxe)
  ]

def gandalfGoblinsBane : CardDef :=
  traditional [
    .name "Gandalf, Goblins' Bane",
    .manaCost [.generic 2, .mono .red],
    .type .creature,
    .supertype .legendary,
    .subtype .avatar,
    .subtype .wizard,
    .power 2,
    .toughness 3,
    .oracleText "Whenever you cast a noncreature spell, Gandalf gets +1/+1 until end of turn and deals 1 damage to each opponent.\n//ADV//\nFlameshape {1}{R}\nSorcery — Adventure\nLook at the top two cards of your library and exile them face down. For as long as they remain exiled, you may play them if you control a Wizard. (Then exile this card. You may cast the creature later from exile.)",
    .triggered (.onCastNoncreaturePumpAndDamageOpponents 1),
    .alternative [
      .name "Flameshape",
      .manaCost [.generic 1, .mono .red],
      .type .sorcery,
      .subtype .adventure,
      .action (.effect (Effect.exileTopPlayIfYouControlSubtype 2 "Wizard")),
      .oracleText "Look at the top two cards of your library and exile them face down. For as long as they remain exiled, you may play them if you control a Wizard. (Then exile this card. You may cast the creature later from exile.)"
    ]
  ]

def anUnexpectedParty : CardDef :=
  traditional [
    .name "An Unexpected Party",
    .manaCost [.generic 2, .mono .white, .mono .white],
    .type .enchantment,
    .oracleText "As this enchantment enters, choose a creature type.\nCreatures you control of the chosen type get +2/+2.\n//ADV//\nAt the Door {X}{2}{W}\nSorcery — Adventure\nCreate X 2/2 red Dwarf creature tokens. (Then exile this card. You may cast the enchantment later from exile.)",
    .static (.chosenTypeCreaturesGet 2 2),
    .alternative [
      .name "At the Door",
      .manaCost [.x, .generic 2, .mono .white],
      .type .sorcery,
      .subtype .adventure,
      .action (.effect (Effect.createTokensX .dwarf)),
      .oracleText "Create X 2/2 red Dwarf creature tokens. (Then exile this card. You may cast the enchantment later from exile.)"
    ],
    .asEntersChooseCreatureType
  ]

def alongTheCrookedWay : CardDef :=
  traditional [
    .name "Along the Crooked Way",
    .manaCost [.generic 2, .mono .black],
    .type .enchantment,
    .oracleText "When this enchantment enters, return target creature card from your graveyard to your hand.\nWhenever a creature card leaves your graveyard, amass Goblins 1.\n{1}{B}: Goblins and Orcs you control gain menace until end of turn.",
    .triggered (.onEnterReturnCreatureFromGyToHand),
    .triggered (.onCreatureCardLeavesYourGyAmassGoblins 1),
    .ability (.activated ([.mana [.generic 1, .mono .black]]) (.effect (Effect.subtypesGainMenace #["Goblin", "Orc"])))
  ]

def azogMoriaSRuin : CardDef :=
  traditional [
    .name "Azog, Moria's Ruin",
    .manaCost [.generic 2, .mono .black],
    .type .creature,
    .supertype .legendary,
    .subtype .goblin,
    .subtype .soldier,
    .power 1,
    .toughness 3,
    .oracleText "When Azog enters, destroy up to one other target creature. Its controller amasses Goblins X, where X is that creature's power. If you controlled that creature, draw a card. (To amass Goblins X, that player puts X +1/+1 counters on an Army they control. It's also a Goblin. If they don't control an Army, they create a 0/0 black Goblin Army creature token first.)",
    .triggered (.onEnterDestroyOtherAmassControllerPower)
  ]

def balinLoremaster : CardDef :=
  traditional [
    .name "Balin, Loremaster",
    .manaCost [.generic 3, .mono .red, .mono .red],
    .type .creature,
    .supertype .legendary,
    .subtype .dwarf,
    .subtype .bard,
    .power 4,
    .toughness 4,
    .oracleText "Storied (If you control three or more artifacts, legendaries, and/or Sagas, you have an enduring story for the rest of the game.)\nWhenever Balin or another Dwarf you control enters, you may discard your hand. Draw X cards, where X is the number of cards discarded this way. If you have an enduring story, Balin deals X damage to each opponent.",
    .ability (.keyword .storied),
    .triggered (.onThisOrAnotherSubtypeEntersDiscardHand "Dwarf")
  ]

def bardTheBowman : CardDef :=
  traditional [
    .name "Bard the Bowman",
    .manaCost [.generic 1, .mono .white, .mono .blue],
    .type .creature,
    .supertype .legendary,
    .subtype .human,
    .subtype .archer,
    .power 1,
    .toughness 3,
    .oracleText "Reach\nWhenever you draw your second card each turn, put a +1/+1 counter on target creature. It gains lifelink until end of turn.",
    .ability (.keyword .reach),
    .triggered (.onDrawSecondPlusOneLifelink)
  ]

def bardKingOfDale : CardDef :=
  traditional [
    .name "Bard, King of Dale",
    .manaCost [.generic 4, .mono .white, .mono .blue],
    .type .creature,
    .supertype .legendary,
    .subtype .human,
    .subtype .noble,
    .subtype .archer,
    .power 3,
    .toughness 5,
    .oracleText "Reach, vigilance\nIf you would draw a card except the first one you draw in each of your draw steps, draw two cards instead.\nIf one or more tokens would be created under your control, twice that many of those tokens are created instead.",
    .ability (.keyword .reach),
    .ability (.keyword .vigilance),
    .tokenDoubling,
    .drawTwoExceptFirstDrawStep
  ]

def bejeweledWarg : CardDef :=
  traditional [
    .name "Bejeweled Warg",
    .manaCost [.generic 1, .mono .green],
    .type .creature,
    .subtype .wolf,
    .power 3,
    .toughness 2,
    .oracleText "Trample\nWhenever this creature deals combat damage to a player, choose one —\n• Put a +1/+1 counter on target Wolf you control.\n• Create a Treasure token. (It's an artifact with \"{T}, Sacrifice this token: Add one mana of any color.\")",
    .ability (.keyword .trample),
    .triggered (.onCombatDamageWolfPlusOneOrTreasure)
  ]

def belladonnaTook : CardDef :=
  traditional [
    .name "Belladonna Took",
    .manaCost [.generic 1, .mono .white],
    .type .creature,
    .supertype .legendary,
    .subtype .halfling,
    .subtype .citizen,
    .power 2,
    .toughness 2,
    .oracleText "Whenever a token you control enters, you gain 1 life if this is the first time this ability has resolved this turn. If it's the second time, draw a card. If it's the third time, put a +1/+1 counter on each creature you control.",
    .triggered (.onTokenYouControlEntersBelladonna)
  ]

def beornTheFierce : CardDef :=
  traditional [
    .name "Beorn the Fierce",
    .manaCost [.generic 3, .mono .green, .mono .green],
    .type .creature,
    .supertype .legendary,
    .subtype .bear,
    .subtype .shapeshifter,
    .subtype .warrior,
    .power 6,
    .toughness 6,
    .oracleText "Trample\nOther Bears you control get +2/+2.\nAt the beginning of combat on your turn, put a trample counter on up to one target creature you control. It becomes a Bear in addition to its other types. Then if you control three or more Bears, draw two cards.",
    .ability (.keyword .trample),
    .triggered (.onYourBeginCombatTrampleCounterBecomeBear),
    .static (.otherCreaturesGet #["Bear"] 2 2)
  ]

def bifurMelodicRider : CardDef :=
  traditional [
    .name "Bifur, Melodic Rider",
    .manaCost [.generic 4, .hybrid .red .white, .hybrid .red .white],
    .type .creature,
    .supertype .legendary,
    .subtype .dwarf,
    .subtype .bard,
    .power 4,
    .toughness 5,
    .oracleText "Storied (If you control three or more artifacts, legendaries, and/or Sagas, you have an enduring story for the rest of the game.)\nWhenever Bifur enters or attacks, put a +1/+1 counter on target creature.\nAs long as you have an enduring story, if a triggered ability of a Dwarf you control triggers, that ability triggers an additional time.",
    .ability (.keyword .storied),
    .triggered (.onEnterOrAttackPlusOneOnCreature),
    .static (.extraTriggerIfEnduringStorySubtype "Dwarf")
  ]

def bilboSGambit : CardDef :=
  traditional [
    .name "Bilbo's Gambit",
    .manaCost [.generic 1, .mono .white],
    .type .instant,
    .action (.effect (Effect.returnSpellCantCastIfGift)),
    .oracleText "Gift a Treasure (You may promise an opponent a gift as you cast this spell. If you do, they create a Treasure token before its other effects. It's an artifact with \"{T}, Sacrifice this token: Add one mana of any color.\")\nReturn target spell to its owner's hand. If the gift was promised, players can't cast spells this turn.",
    .giftTreasure
  ]

def bilboThiefInTheNight : CardDef :=
  traditional [
    .name "Bilbo, Thief in the Night",
    .manaCost [.generic 1, .mono .blue],
    .type .creature,
    .supertype .legendary,
    .subtype .halfling,
    .subtype .rogue,
    .power 2,
    .toughness 2,
    .oracleText "Spells you cast from anywhere other than your hand cost {1} less to cast.\nWhenever Bilbo attacks, you may cast an artifact, instant, or sorcery spell from your graveyard. If an instant or sorcery spell cast this way would be put into your graveyard, exile it instead.",
    .triggered (.onAttackCastFromGyArtifactInstantSorcery),
    .costReductionNotFromHand 1
  ]

def bolgOfTheNorth : CardDef :=
  traditional [
    .name "Bolg of the North",
    .manaCost [.generic 3, .mono .black, .mono .red],
    .type .creature,
    .supertype .legendary,
    .subtype .goblin,
    .subtype .soldier,
    .power 5,
    .toughness 5,
    .oracleText "When Bolg enters, you may sacrifice another creature. When you do, Bolg deals damage equal to that creature's power to another target creature. If excess damage was dealt this way, amass Goblins X, where X is that excess damage. (Put X +1/+1 counters on an Army you control. It's also a Goblin. If you don't control an Army, create a 0/0 black Goblin Army creature token first.)",
    .triggered (.onEnterBolgMaySacrifice)
  ]

def boughsideWanderers : CardDef :=
  traditional [
    .name "Boughside Wanderers",
    .manaCost [.generic 4, .mono .green, .mono .green],
    .type .creature,
    .subtype .elf,
    .subtype .scout,
    .power 4,
    .toughness 4,
    .oracleText "When this creature enters, look at the top four cards of your library. You may reveal a permanent card from among them and put it into your hand. Put the rest on the bottom of your library in a random order.\nLandfall — Whenever a land you control enters, this creature gets +2/+2 until end of turn.",
    .triggered (.onLandYouControlEntersGets 2 2),
    .triggered (.onEnterLookAtTopRevealTypes 4 #["permanent"])
  ]

def burnBurnTreeAndFern : CardDef :=
  traditional [
    .name "Burn, Burn, Tree and Fern",
    .manaCost [.generic 3, .mono .red],
    .type .enchantment,
    .subtype .saga,
    .saga "IV" #[
    chapter "I" "This Saga deals 6 damage to target creature an opponent controls."
      (Effect.chapterDealDamageToOppCreature 6),
    chapter "II" "Destroy target artifact an opponent controls."
      (Effect.chapterDestroyOppArtifact),
    chapter "III, IV" "Add {R}." (Effect.chapterAddMana (.colored .red))],
    .oracleText "(As this Saga enters and after your draw step, add a lore counter. Sacrifice after IV.)\nI — This Saga deals 6 damage to target creature an opponent controls.\nII — Destroy target artifact an opponent controls.\nIII, IV — Add {R}."
  ]

def cantankerousKeepers : CardDef :=
  traditional [
    .name "Cantankerous Keepers",
    .manaCost [.generic 5, .mono .green],
    .type .creature,
    .subtype .elf,
    .subtype .soldier,
    .power 4,
    .toughness 3,
    .oracleText "Affinity for Elves (This spell costs {1} less to cast for each Elf you control.)\nWhen this creature enters, mill four cards, then put all Elf cards from among them into your hand.",
    .triggered (.onEnterMillThenSubtypeToHand 4 "Elf"),
    .affinityForSubtype "Elves"
  ]

def celebrateTheMountainKing : CardDef :=
  traditional [
    .name "Celebrate the Mountain-king",
    .manaCost [.generic 3, .mono .white],
    .type .enchantment,
    .oracleText "When this enchantment enters, for each opponent, exile up to one target nonland permanent that player controls until this enchantment leaves the battlefield.\nWhen this enchantment enters, recruit. (Draw a card, then discard a card. If you discarded a nonland card, create a 1/1 white Human Soldier creature token.)",
    .triggered (.onEnterRecruit),
    .triggered (.onEnterExileOppNonlandEachUntilLeaves)
  ]

def dancingFromDarkToDawn : CardDef :=
  traditional [
    .name "Dancing from Dark to Dawn",
    .manaCost [.generic 3, .mono .green, .mono .green],
    .type .enchantment,
    .oracleText "Whenever you cast a creature spell, put X +1/+1 counters on target creature you control, where X is that spell's mana value.\nLandfall — Whenever a land you control enters, create a 2/2 green Bear creature token.",
    .triggered (.onLandYouControlEntersCreateTokens .bear 1),
    .triggered (.onCastCreaturePlusOneEqualMv)
  ]

def desertWereWorm : CardDef :=
  traditional [
    .name "Desert Were-Worm",
    .manaCost [.generic 4, .mono .red, .mono .red],
    .type .creature,
    .subtype .dragon,
    .subtype .wurm,
    .power 0,
    .toughness 5,
    .oracleText "This creature gets +2/+0 for each Mountain you control.\nWhenever you attack with creatures with total power 12 or greater for the first time each turn, untap all attacking creatures. After this phase, there is an additional combat phase.",
    .triggered (.onAttackWithTotalPowerUntapExtraCombat 12),
    .powerPerMountain 2
  ]

def downInTheValley : CardDef :=
  traditional [
    .name "Down in the Valley",
    .manaCost [.generic 2, .mono .green],
    .type .enchantment,
    .subtype .saga,
    .saga "IV" #[
    chapter "I" "Search your library for a basic land card, reveal it, put it into your hand, then shuffle."
      (Effect.chapterSearchBasicLandToHand),
    chapter "II" "This Saga gains \"Landfall — Whenever a land you control enters, create a 1/1 green Elf creature token.\""
      (Effect.chapterGainLandfallCreateElf),
    chapter "III, IV" "Elves you control get +1/+0 and gain vigilance until end of turn."
      (Effect.chapterElvesGetVigilance 1)],
    .oracleText "(As this Saga enters and after your draw step, add a lore counter. Sacrifice after IV.)\nI — Search your library for a basic land card, reveal it, put it into your hand, then shuffle.\nII — This Saga gains \"Landfall — Whenever a land you control enters, create a 1/1 green Elf creature token.\"\nIII, IV — Elves you control get +1/+0 and gain vigilance until end of turn."
  ]

def downDownToGoblinTown : CardDef :=
  traditional [
    .name "Down, Down to Goblin-town",
    .manaCost [.generic 2, .mono .black],
    .type .enchantment,
    .subtype .saga,
    .saga "IV" #[
    chapter "I" "Target opponent reveals their hand. You choose a nonland card from it. That player discards that card."
      (Effect.chapterOpponentDiscardsNonland),
    chapter "II" "Amass Goblins 1. (Put a +1/+1 counter on an Army you control. It's also a Goblin. If you don't control an Army, create a 0/0 black Goblin Army creature token first.)"
      (Effect.chapterAmassGoblins 1),
    chapter "III, IV" "Target opponent loses 1 life and you gain 1 life."
      (Effect.chapterOpponentLosesYouGain 1)],
    .oracleText "(As this Saga enters and after your draw step, add a lore counter. Sacrifice after IV.)\nI — Target opponent reveals their hand. You choose a nonland card from it. That player discards that card.\nII — Amass Goblins 1. (Put a +1/+1 counter on an Army you control. It's also a Goblin. If you don't control an Army, create a 0/0 black Goblin Army creature token first.)\nIII, IV — Target opponent loses 1 life and you gain 1 life."
  ]

def dwalinWeaponmaster : CardDef :=
  traditional [
    .name "Dwalin, Weaponmaster",
    .manaCost [.generic 1, .hybrid .red .white],
    .type .creature,
    .supertype .legendary,
    .subtype .dwarf,
    .subtype .warrior,
    .power 2,
    .toughness 1,
    .oracleText "First strike\nWhenever Dwalin enters or attacks, put a hone counter on each Equipment you control. (Each hone counter on an Equipment grants +1/+0 to equipped creature.)",
    .ability (.keyword .firstStrike),
    .triggered (.onEnterOrAttackHoneEachEquipment)
  ]

def dainIronfoot : CardDef :=
  traditional [
    .name "Dáin Ironfoot",
    .manaCost [.generic 2, .mono .red],
    .type .creature,
    .supertype .legendary,
    .subtype .dwarf,
    .subtype .warrior,
    .power 1,
    .toughness 4,
    .oracleText "When Dáin enters, create a colorless Equipment artifact token named Axe with \"Equipped creature gets +1/+0\" and equip {2}. When you do, attach it to target creature you control.\nWhenever Dáin attacks, each equipped attacking creature gains double strike until end of turn.",
    .triggered (.onEnterCreateAxeAttach),
    .triggered (.onAttackEquippedGainDoubleStrike)
  ]

def elrondMoonReader : CardDef :=
  traditional [
    .name "Elrond, Moon-Reader",
    .manaCost [.generic 2, .mono .blue],
    .type .creature,
    .supertype .legendary,
    .subtype .elf,
    .subtype .noble,
    .power 3,
    .toughness 3,
    .oracleText "Whenever you activate an ability of a creature, draw a card. This ability triggers only once each turn.\n{5}{U}{U}: Exile up to two other target nonland permanents you control. Return those cards to the battlefield under their owner's control at the beginning of the next end step.",
    .triggered (.onActivateCreatureAbilityDrawOnce),
    .ability (.activated ([.mana [.generic 5, .mono .blue, .mono .blue]]) (.effect (Effect.exileThenReturnNextEnd)))
  ]

def elvenPassage : CardDef :=
  traditional [
    .name "Elven Passage",
    .type .land,
    .oracleText "{T}, Pay 1 life, Sacrifice this land: Search your library for a basic land card, put it onto the battlefield tapped, then shuffle. You may behold an Elf. If you do, untap that land. (To behold an Elf, choose an Elf you control or reveal an Elf card from your hand.)",
    .ability (.activated ([.tap, .sacrificeSource, .payLife 1]) (.effect (Effect.searchBasicBeholdSubtypeUntap "Elf")))
  ]

def enchantedRiverSGrasp : CardDef :=
  traditional [
    .name "Enchanted River's Grasp",
    .manaCost [.generic 2, .mono .blue],
    .type .enchantment,
    .subtype .aura,
    .oracleText "Enchant creature\nWhen this Aura enters, tap enchanted creature and remove all counters from it.\nEnchanted creature loses all abilities and doesn't untap during its controller's untap step.",
    .triggered (.onEnterTapEnchantedRemoveCounters),
    .static (.enchantedLosesAbilitiesDoesntUntap)
  ]

def getawayBarrel : CardDef :=
  traditional [
    .name "Getaway Barrel",
    .manaCost [.generic 3, .mono .red],
    .type .artifact,
    .oracleText "When this artifact is put into a graveyard from the battlefield, reveal the top thirteen cards of your library. Put a random creature card from among them onto the battlefield. Put the rest on the bottom of your library in a random order.",
    .triggered (.onDiesRevealTopPutRandomCreature 13)
  ]

def gleamingSplendor : CardDef :=
  traditional [
    .name "Gleaming Splendor",
    .manaCost [.generic 1, .mono .white],
    .type .enchantment,
    .oracleText "Whenever an opponent draws their second card each turn, you create a Treasure token.\n{2}{W}: Two target players each draw a card.",
    .triggered (.onOpponentDrawsSecondCreateTreasure),
    .ability (.activated ([.mana [.generic 2, .mono .white]]) (.effect (Effect.twoPlayersDraw)))
  ]

def gollumRiddleMaster : CardDef :=
  traditional [
    .name "Gollum, Riddle Master",
    .manaCost [.generic 1, .mono .black],
    .type .creature,
    .supertype .legendary,
    .subtype .halfling,
    .subtype .horror,
    .power 3,
    .toughness 1,
    .oracleText "As Gollum enters, choose odd or even. (Zero is even.)\nWhenever an opponent casts a spell with mana value of the chosen quality, choose one that hasn't been chosen —\n• Put a +1/+1 counter on Gollum.\n• Each opponent loses 2 life and you gain 2 life.\n• Draw a card.",
    .triggered (.onOpponentCastsChosenParityModes),
    .asEntersChooseOddEven
  ]

def headOfTheHunt : CardDef :=
  traditional [
    .name "Head of the Hunt",
    .manaCost [.generic 2, .mono .black, .mono .black],
    .type .creature,
    .subtype .wolf,
    .power 4,
    .toughness 3,
    .oracleText "Flash\nIf a creature an opponent controls would die, exile it instead. When you do, create a 2/2 green Wolf creature token.",
    .ability (.keyword .flash),
    .static (.exileOppDeathCreateWolf),
    .exileOppCreaturesInstead
  ]

def insideInformation : CardDef :=
  traditional [
    .name "Inside Information",
    .manaCost [.x, .mono .black, .mono .black],
    .type .sorcery,
    .action (.effect (Effect.exileTopXOppPlayForLife)),
    .oracleText "Exile the top X cards of target opponent's library. You may play those cards this turn. If you cast a spell this way, pay life equal to its mana value rather than pay its mana cost."
  ]

def keyToTheSideDoor : CardDef :=
  traditional [
    .name "Key to the Side-Door",
    .manaCost [.generic 1],
    .type .artifact,
    .oracleText "{2}, {T}: Target creature can't be blocked this turn.\n{1}, {T}, Discard a legendary card with the same name as a legendary permanent you control: Draw two cards.",
    .ability (.activated ([.mana [.generic 2], .tap]) (.effect (Effect.targetCantBeBlockedThisTurn))),
    .ability (.activated ([.mana [.generic 1], .tap, .discardLegendarySameName]) (.effect (Effect.discardLegendarySameNameDraw)))
  ]

def lakeTownToymaker : CardDef :=
  traditional [
    .name "Lake-town Toymaker",
    .manaCost [.generic 3, .mono .white],
    .type .creature,
    .subtype .human,
    .subtype .artificer,
    .power 3,
    .toughness 4,
    .oracleText "At the beginning of combat on your turn, if you've drawn two or more cards this turn, another target creature you control gets +3/+0 and gains first strike until end of turn.",
    .triggered (.onYourBeginCombatIfDrawnTwoPumpFirstStrike)
  ]

def lastLightOfDurinSDay : CardDef :=
  traditional [
    .name "Last Light of Durin's Day",
    .manaCost [.generic 1, .mono .red],
    .type .enchantment,
    .oracleText "Whenever a Mountain you control enters, put a quest counter on this enchantment. If it has six or more quest counters on it, sacrifice it. If you do, search your hand and/or library for a Dragon card and put it onto the battlefield. If you search your library this way, shuffle.\nMountaincycling {2} ({2}, Discard this card: Search your library for a Mountain card, reveal it, put it into your hand, then shuffle.)",
    .triggered (.onMountainEntersQuestThenDragon),
    .ability (.activated ([.mana [.generic 2], .discardSource, .activateFromHand]) (.effect (Effect.searchLandTypeToHand "Mountain")))
  ]

def masterSCouncillors : CardDef :=
  traditional [
    .name "Master's Councillors",
    .manaCost [.generic 1, .mono .blue],
    .type .creature,
    .subtype .human,
    .subtype .advisor,
    .power 1,
    .toughness 3,
    .oracleText "Vigilance\nThis creature gets +2/+0 for each graveyard with seven or more cards in it.\nWhenever you draw your second card each turn, target player mills three cards. (They put the top three cards of their library into their graveyard.)",
    .ability (.keyword .vigilance),
    .triggered (.onDrawSecondMillPlayer 3),
    .static (.powerPerFatGraveyard 2)
  ]

def oldFatSpiderCanTSeeMe : CardDef :=
  traditional [
    .name "Old Fat Spider Can't See Me",
    .manaCost [.generic 2, .mono .blue],
    .type .enchantment,
    .subtype .saga,
    .saga "IV" #[
    chapter "I" "Target creature you control gains hexproof for as long as this Saga remains on the battlefield."
      (Effect.chapterGrantHexproofWhileRemains),
    chapter "II" "Prevent all damage that would be dealt by up to one target creature for as long as this Saga remains on the battlefield."
      (Effect.chapterPreventDamageWhileRemains),
    chapter "III, IV" "Draw a card." (Effect.chapterDraw 1)],
    .oracleText "(As this Saga enters and after your draw step, add a lore counter. Sacrifice after IV.)\nI — Target creature you control gains hexproof for as long as this Saga remains on the battlefield.\nII — Prevent all damage that would be dealt by up to one target creature for as long as this Saga remains on the battlefield.\nIII, IV — Draw a card."
  ]

def orcristGoblinCleaver : CardDef :=
  traditional [
    .name "Orcrist, Goblin-cleaver",
    .manaCost [.generic 3],
    .type .artifact,
    .subtype .equipment,
    .supertype .legendary,
    .oracleText "Equipped creature gets +2/+2 and has trample.\nWhenever equipped creature deals combat damage to a player, choose a creature type. Create a Treasure token for each creature you control of that type.\nEquip {3}",
    .equip [.generic 3],
    .triggered (.onEquippedCombatDamageTreasuresPerChosenType),
    .static (.equippedCreatureGetsAndHas 2 2 Keyword.trample)
  ]

def partInFriendship : CardDef :=
  traditional [
    .name "Part in Friendship",
    .manaCost [.generic 4, .mono .green],
    .type .enchantment,
    .oracleText "Whenever a nontoken creature you control dies, reveal cards from the top of your library until you reveal a creature card. If its mana value is less than or equal to the number of lands you control, put it onto the battlefield. Otherwise, put it into your hand. Put the rest on the bottom of your library in a random order. This ability triggers only once each turn.",
    .triggered (.onNontokenYouControlDiesRevealCreature)
  ]

def radagastOfRhosgobel : CardDef :=
  traditional [
    .name "Radagast of Rhosgobel",
    .manaCost [.generic 2, .mono .green, .mono .green],
    .type .creature,
    .supertype .legendary,
    .subtype .avatar,
    .subtype .wizard,
    .power 2,
    .toughness 5,
    .oracleText "The first creature spell you cast each turn costs {2} less to cast and can be cast as though it had flash.",
    .firstCreatureHasFlash,
    .firstCreatureCostsLess 2
  ]

def rhovanionRampager : CardDef :=
  traditional [
    .name "Rhovanion Rampager",
    .manaCost [.generic 2, .mono .black],
    .type .creature,
    .subtype .wolf,
    .power 3,
    .toughness 2,
    .oracleText "Whenever this creature attacks, you may sacrifice another creature. If you do, put a number of +1/+1 counters on this creature equal to the sacrificed creature's power.\nWhen this creature dies, amass Goblins X, where X is this creature's power. (Put X +1/+1 counters on an Army you control. It's also a Goblin. If you don't control an Army, create a 0/0 black Goblin Army creature token first.)",
    .triggered (.onAttackMaySacAnotherPlusOneEqualPower),
    .triggered (.onDiesAmassGoblinsEqualPower)
  ]

def riddlesInTheDark : CardDef :=
  traditional [
    .name "Riddles in the Dark",
    .manaCost [.generic 2, .mono .blue],
    .type .instant,
    .action (.effect (Effect.riddlesInTheDark)),
    .oracleText "Look at the top four cards of your library and separate them into a face-down pile and a face-up pile. An opponent chooses one of the piles. Put that pile into your hand and the other into your graveyard."
  ]

def roadsGoEverEverOn : CardDef :=
  traditional [
    .name "Roads Go Ever, Ever On",
    .manaCost [.generic 1, .mono .white],
    .type .enchantment,
    .subtype .saga,
    .saga "IV" #[
    chapter "I" "Search your library for up to two basic Plains cards, exile them, then shuffle. You gain 2 life."
      (Effect.chapterSearchBasicPlainsExileGainLife 2 2),
    chapter "II, III" "Put a card exiled with this Saga into its owner's hand."
      (Effect.chapterReturnLinkedExileToHand),
    chapter "IV" "Whenever you attack this turn, target creature you control gets +1/+1 until end of turn for each Plains you control."
      (Effect.chapterGrantAttackPumpPerPlainsThisTurn)],
    .oracleText "(As this Saga enters and after your draw step, add a lore counter. Sacrifice after IV.)\nI — Search your library for up to two basic Plains cards, exile them, then shuffle. You gain 2 life.\nII, III — Put a card exiled with this Saga into its owner's hand.\nIV — Whenever you attack this turn, target creature you control gets +1/+1 until end of turn for each Plains you control."
  ]

def rollRollRollRoll : CardDef :=
  traditional [
    .name "Roll-Roll-Roll-Roll",
    .manaCost [.generic 2, .mono .blue],
    .type .enchantment,
    .subtype .saga,
    .saga "IV" #[
    chapter "I, II, III, IV" "Exile up to one target creature or land you control. If you do, return it to the battlefield under its owner's control at the beginning of the next end step."
      (Effect.chapterBlinkUntilEndStep)],
    .oracleText "(As this Saga enters and after your draw step, add a lore counter. Sacrifice after IV.)\nI, II, III, IV — Exile up to one target creature or land you control. If you do, return it to the battlefield under its owner's control at the beginning of the next end step."
  ]

def silvanReveler : CardDef :=
  traditional [
    .name "Silvan Reveler",
    .manaCost [.generic 2, .mono .green, .mono .blue],
    .type .creature,
    .subtype .elf,
    .subtype .citizen,
    .power 3,
    .toughness 2,
    .oracleText "When this creature enters, draw a card, then discard a card. If you discard a land card this way, put it from your graveyard onto the battlefield tapped.\nLandfall — Whenever a land you control enters, you may pay {1}{G}{U}. If you do, return this card from your graveyard to your hand.",
    .triggered (.onEnterLootLandEntersTapped),
    .triggered (.onLandYouControlEntersPayReturnFromGy)
  ]

def stingBilboSSword : CardDef :=
  traditional [
    .name "Sting, Bilbo's Sword",
    .manaCost [.generic 2],
    .type .artifact,
    .subtype .equipment,
    .supertype .legendary,
    .oracleText "Flash\nWhen Sting enters, put a hone counter on Sting for each creature target opponent controls. Attach Sting to up to one target creature you control. (Each hone counter on an Equipment grants +1/+0 to equipped creature.)\nEquip {3}",
    .equip [.generic 3],
    .ability (.keyword .flash),
    .triggered (.onEnterHonePerOppCreaturesAttach)
  ]

def stoneGiantOfHighPass : CardDef :=
  traditional [
    .name "Stone-Giant of High Pass",
    .manaCost [.generic 5, .mono .red, .mono .red],
    .type .creature,
    .subtype .giant,
    .power 7,
    .toughness 7,
    .oracleText "Whenever this creature enters or attacks, create a 3/1 colorless Wall artifact creature token with defender named Stone Boulder.\n{2}{R}, Sacrifice an artifact: This creature deals 4 damage to any target.",
    .triggered (.onEnterOrAttackCreateWall),
    .ability (.activated ([.mana [.generic 2, .mono .red], .sacrificeArtifact]) (.effect (Effect.dealDamageToAny 4)))
  ]

def supperForSpiders : CardDef :=
  traditional [
    .name "Supper for Spiders",
    .manaCost [.generic 1, .mono .black],
    .type .instant,
    .action (.effect (Effect.supperForSpiders)),
    .oracleText "Put onto the battlefield under your control all creature cards in your opponents' graveyards that were put there from the battlefield this turn. They are Food artifacts with \"{2}, {T}, Sacrifice this artifact: You gain 3 life.\" (They lose all other types and subtypes.)"
  ]

def theEaglesAreComing : CardDef :=
  traditional [
    .name "The Eagles Are Coming!",
    .manaCost [.generic 1, .mono .white],
    .type .instant,
    .action (.effect (Effect.eaglesAreComing)),
    .oracleText "Kicker {2}{W}{W} (You may pay an additional {2}{W}{W} as you cast this spell.)\nChoose target creature you own. If this spell was kicked, instead choose any number of target creatures you own. Return each chosen creature to your hand. At the beginning of the next upkeep, create a 4/4 white Bird Soldier creature token with flying for each creature returned to your hand this way.",
    .kicker [.generic 2, .mono .white, .mono .white]
  ]

def theGreatGoblin : CardDef :=
  traditional [
    .name "The Great Goblin",
    .manaCost [.generic 1, .hybrid .black .red, .hybrid .black .red],
    .type .creature,
    .supertype .legendary,
    .subtype .goblin,
    .subtype .noble,
    .power 3,
    .toughness 2,
    .oracleText "Whenever you put one or more counters on a Goblin, Orc, or Army you control, The Great Goblin deals 2 damage to target opponent.\nWhenever another Goblin, Orc, or Army you control dies, exile the top card of your library. You may play it until the end of your next turn.",
    .triggered (.onPutCountersOnGoblinOrcArmyDamageOpp),
    .triggered (.onAnotherGoblinOrcArmyDiesExileTop)
  ]

def theMasterOfLakeTown : CardDef :=
  traditional [
    .name "The Master of Lake-town",
    .manaCost [.generic 1, .mono .black, .mono .black],
    .type .creature,
    .supertype .legendary,
    .subtype .human,
    .subtype .advisor,
    .power 3,
    .toughness 2,
    .oracleText "Deathtouch\nWhenever a player loses life, that player mills that many cards. (Damage causes loss of life.)\nWhen The Master of Lake-town dies, draw a card for each graveyard with seven or more cards in it.",
    .ability (.keyword .deathtouch),
    .triggered (.onPlayerLosesLifeMillThatMany),
    .triggered (.onDiesDrawPerFatGraveyard)
  ]

def theMistyMountainsCold : CardDef :=
  traditional [
    .name "The Misty Mountains Cold",
    .manaCost [.generic 2, .mono .red],
    .type .enchantment,
    .subtype .saga,
    .saga "IV" #[
    chapter "I, II, III, IV" "Create a Treasure token. Then if you control four or more Treasures, sacrifice this Saga. If you do, create a 6/6 red Dragon creature token with flying. (A Treasure token is an artifact with \"{T}, Sacrifice this token: Add one mana of any color.\")"
      (Effect.chapterTreasureThenDragonIfFour)],
    .oracleText "(As this Saga enters and after your draw step, add a lore counter. Sacrifice after IV.)\nI, II, III, IV — Create a Treasure token. Then if you control four or more Treasures, sacrifice this Saga. If you do, create a 6/6 red Dragon creature token with flying. (A Treasure token is an artifact with \"{T}, Sacrifice this token: Add one mana of any color.\")"
  ]

def theMountainKingSReturn : CardDef :=
  traditional [
    .name "The Mountain-king's Return",
    .manaCost [.generic 2, .mono .white],
    .type .enchantment,
    .subtype .saga,
    .saga "III" #[
    chapter "I" "Recruit. (Draw a card, then discard a card. If you discarded a nonland card, create a 1/1 white Human Soldier creature token.)"
      (Effect.chapterRecruit),
    chapter "II" "Return target creature card with mana value 3 or less from your graveyard to the battlefield."
      (Effect.chapterReturnCreatureFromGyMvAtMost 3),
    chapter "III" "Put a +1/+1 counter on up to one target creature."
      (Effect.chapterPlusOneUpToOne)],
    .oracleText "(As this Saga enters and after your draw step, add a lore counter. Sacrifice after III.)\nI — Recruit. (Draw a card, then discard a card. If you discarded a nonland card, create a 1/1 white Human Soldier creature token.)\nII — Return target creature card with mana value 3 or less from your graveyard to the battlefield.\nIII — Put a +1/+1 counter on up to one target creature."
  ]

def theNotaryHobbits : CardDef :=
  traditional [
    .name "The Notary Hobbits",
    .manaCost [.generic 3, .mono .green, .mono .green],
    .type .creature,
    .supertype .legendary,
    .subtype .halfling,
    .subtype .advisor,
    .power 1,
    .toughness 1,
    .oracleText "When The Notary Hobbits enter, if they're not a token, create two tokens that are copies of them, except the tokens aren't legendary.\n{T}: Add {C} for each Halfling you control.",
    .triggered (.onEnterIfNotTokenCopySelf),
    .tapAddColorlessPerSubtype "Halfling"
  ]

def theSackvilleBagginses : CardDef :=
  traditional [
    .name "The Sackville-Bagginses",
    .manaCost [.generic 1, .mono .black],
    .type .creature,
    .supertype .legendary,
    .subtype .halfling,
    .subtype .citizen,
    .power 2,
    .toughness 2,
    .oracleText "When The Sackville-Bagginses enter, you may sacrifice another creature or artifact. If you do, draw a card and create a Treasure token.\nWhenever you sacrifice a token, target opponent loses 1 life.",
    .triggered (.onEnterMaySacDrawTreasure),
    .triggered (.onYouSacrificeTokenOppLosesLife)
  ]

def thorinMountainKing : CardDef :=
  traditional [
    .name "Thorin, Mountain-king",
    .manaCost [.generic 3, .mono .red],
    .type .creature,
    .supertype .legendary,
    .subtype .dwarf,
    .subtype .noble,
    .power 3,
    .toughness 4,
    .oracleText "Trample\nWhen Thorin enters, attach any number of target Equipment you control to target creature you control. When one or more Equipment become attached to that creature this way, that creature deals damage equal to its power to up to one target creature.",
    .ability (.keyword .trample),
    .triggered (.onEnterAttachEquipmentThenFight)
  ]

def thranduilSCompany : CardDef :=
  traditional [
    .name "Thranduil's Company",
    .manaCost [.generic 2, .mono .green, .mono .blue],
    .type .creature,
    .subtype .elf,
    .subtype .soldier,
    .power 3,
    .toughness 4,
    .oracleText "As long as you control another Elf, you may play an additional land on each of your turns.\nLandfall — Whenever a land you control enters, put two +1/+1 counters on target creature you control. It gains vigilance until end of turn.",
    .triggered (.onLandYouControlEntersPlusOneVigilance),
    .extraLandIfOtherSubtype "Elf"
  ]

def thranduilTheElvenking : CardDef :=
  traditional [
    .name "Thranduil, the Elvenking",
    .manaCost [.generic 2, .mono .black, .mono .green, .mono .blue],
    .type .creature,
    .supertype .legendary,
    .subtype .elf,
    .subtype .noble,
    .power 5,
    .toughness 6,
    .oracleText "Thranduil has all activated abilities of all Elf cards in your graveyard.\nWhenever another legendary Elf you control enters, draw two cards, then discard a card.",
    .triggered (.onAnotherLegendarySubtypeEntersLoot "Elf"),
    .static (.copyActivatedFromGySubtype "Elf")
  ]

def throughTheForestGate : CardDef :=
  traditional [
    .name "Through the Forest Gate",
    .manaCost [.generic 6, .mono .green, .mono .green],
    .type .sorcery,
    .action (.effect (Effect.lookAtTopLandsGainLife 20 8)),
    .oracleText "Look at the top twenty cards of your library, put any number of land cards from among them onto the battlefield tapped, then shuffle. You gain 8 life."
  ]

def tomBertAndWilliam : CardDef :=
  traditional [
    .name "Tom, Bert, and William",
    .manaCost [.generic 3, .mono .black, .mono .green],
    .type .creature,
    .supertype .legendary,
    .subtype .troll,
    .power 5,
    .toughness 5,
    .oracleText "{1}, Sacrifice another creature: Draw cards equal to the sacrificed creature's power, then discard a card.\nWhen Tom, Bert, and William die, if they were a creature, return them to the battlefield. They're an artifact. (They're no longer a creature.)",
    .triggered (.onDiesReturnAsArtifact),
    .ability (.activated ([.mana [.generic 1], .sacrificeAnotherSubtype "creature"]) (.effect (Effect.drawEqualSacrificedPowerThenDiscard)))
  ]

def uncoverTheMoonLetters : CardDef :=
  traditional [
    .name "Uncover the Moon-Letters",
    .manaCost [.generic 3, .mono .blue],
    .type .enchantment,
    .oracleText "Whenever you cast a noncreature spell, you may draw X cards, where X is the amount of mana spent to cast that spell. If you do, discard two cards.",
    .triggered (.onCastNoncreatureMayDrawXDiscard2)
  ]

def wizardSStaff : CardDef :=
  traditional [
    .name "Wizard's Staff",
    .manaCost [.generic 1, .mono .blue],
    .type .artifact,
    .subtype .equipment,
    .oracleText "Equipped creature has prowess. (Whenever its controller casts a noncreature spell, that creature gets +1/+1 until end of turn.)\nIf a triggered ability of equipped creature triggers, that ability triggers an additional time.\nEquip Wizard {1}\nEquip {3}",
    .equipFor "Wizard" [.generic 1],
    .equip [.generic 3],
    .static (.equippedTriggersAgain),
    .static (.equippedCreatureHasKeywords Keyword.prowess)
  ]

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
  bilboBagginsBurglar,
  lakeshoreApothecary,
  confusticateAndBebother,
  ravenhillFlock,
  thranduilsDecree,
  bilboLuckwearer,
  uneasyPartings,
  frontPorchSentries,
  greatFierceBee,
  stirUpTrouble,
  desolationProwler,
  raveningWarg,
  gollumSilentSlinker,
  bilbosDeadlySlice,
  dreadedBatCloud,
  crudeBentBlade,
  gollumTheAbandoned,
  gnashingOfTeeth,
  reverentHowl,
  stonyVoicedGoblins,
  smaugTheGreatCalamity,
  gandalfSparkStarter,
  raggedShortSpear,
  snowslopeHunter,
  guardianOfTheHalls,
  quarrel,
  galionElvenkingsButler,
  wargTactics,
  beornsHospitality,
  woodlandWeavemaster,
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
#guard raggedShortSpear.isEquipment
#guard !raggedShortSpear.isAura
#guard !raggedShortSpear.requiresTarget
#guard raggedShortSpear.staticAbilities == #[.equippedCreatureGets 2 0]
#guard raggedShortSpear.triggeredAbilities == #[.onEnterMayDiscardDraw 2]
#guard raggedShortSpear.activatedAbilities.size == 1
#guard raggedShortSpear.activatedAbilities[0]!.onlyAsSorcery
#guard raggedShortSpear.activatedAbilities[0]!.effect == Effect.attachToTargetCreatureYouControl
#guard raggedShortSpear.activatedAbilities[0]!.cost.mana == (ManaCost.ofGeneric 3)
#guard (raggedShortSpear.summary.splitOn "Equipped creature").length > 1
#guard crudeBentBlade.isEquipment
#guard !crudeBentBlade.isAura
#guard !crudeBentBlade.requiresTarget
#guard crudeBentBlade.staticAbilities == #[.equippedCreatureGets 2 1]
#guard crudeBentBlade.triggeredAbilities == #[.onEnterTargetOpponentSacrificesCreature]
#guard crudeBentBlade.activatedAbilities.size == 1
#guard crudeBentBlade.activatedAbilities[0]!.onlyAsSorcery
#guard crudeBentBlade.activatedAbilities[0]!.effect == Effect.attachToTargetCreatureYouControl
#guard crudeBentBlade.activatedAbilities[0]!.cost.mana == (ManaCost.ofGeneric 2)
#guard (crudeBentBlade.summary.splitOn "Equipped creature").length > 1
#guard (crudeBentBlade.summary.splitOn "target opponent").length > 1
#guard woodElves.triggeredAbilities == #[.onEnterSearchForest]
#guard (woodElves.summary.splitOn "Forest card").length > 1
#guard galionElvenkingsButler.triggeredAbilities == #[.onAttackSetOtherBasePT]
#guard (galionElvenkingsButler.summary.splitOn "base power and toughness").length > 1
#guard galionElvenkingsButler.power == some 4
#guard galionElvenkingsButler.toughness == some 4
#guard woodlandWeavemaster.keywords.vigilance
#guard woodlandWeavemaster.triggeredAbilities == #[.onAnotherElfYouControlEntersGets1]
#guard woodlandWeavemaster.tapAddAnyColorEqualToPower
#guard woodlandWeavemaster.manaAbilities == #[
  .colored .white, .colored .blue, .colored .black, .colored .red, .colored .green]
#guard woodlandWeavemaster.power == some 1
#guard woodlandWeavemaster.toughness == some 2
#guard (woodlandWeavemaster.summary.splitOn "vigilance").length > 1
#guard (woodlandWeavemaster.summary.splitOn "another Elf").length > 1
#guard (woodlandWeavemaster.summary.splitOn "any one color").length > 1
#guard quarrel.isInstant
#guard quarrel.spellEffect == some (Effect.creatureYouControlDealsPowerToOppCreature)
#guard quarrel.requiresTarget
#guard Effect.creatureYouControlDealsPowerToOppCreature.targetCount == 2
#guard (quarrel.summary.splitOn "deals damage equal to its power").length > 1
#guard wargTactics.isInstant
#guard wargTactics.isModal
#guard wargTactics.requiresTarget
#guard wargTactics.spellModes == #[
  Effect.destroyCreatureWithFlying,
  Effect.plusOnePlusOneTrampleHexproof]
#guard (wargTactics.summary.splitOn "Choose one").length > 1
#guard (wargTactics.summary.splitOn "hexproof").length > 1
#guard beornsHospitality.isEnchantment
#guard !beornsHospitality.isCreature
#guard beornsHospitality.triggeredAbilities == #[.onLandYouControlEntersPlusOnePlusOne]
#guard beornsHospitality.activatedAbilities.size == 1
#guard beornsHospitality.activatedAbilities[0]!.effect == Effect.becomeSubtypeWithLandsPT "Bear"
#guard beornsHospitality.activatedAbilities[0]!.cost.mana ==
  (ManaCost.ofGenericAndColors 5 [.green, .green])
#guard (beornsHospitality.summary.splitOn "Landfall").length > 1
#guard (beornsHospitality.summary.splitOn "Bear creature").length > 1
#guard mirkwoodPathmaker.staticAbilities == #[.powerToughnessEqualLandsYouControl]
#guard mirkwoodPathmaker.power.isNone
#guard mirkwoodPathmaker.toughness.isNone
#guard (mirkwoodPathmaker.summary.splitOn "*/*").length > 1
#guard (mirkwoodPathmaker.summary.splitOn "lands you control").length > 1
#guard gandalfSparkStarter.keywords.reach
#guard gandalfSparkStarter.triggeredAbilities == #[.onEnterDealDividedDamage 3 3]
#guard (gandalfSparkStarter.summary.splitOn "divided as you choose").length > 1
#guard (gandalfSparkStarter.summary.splitOn "reach").length > 1
#guard guardianOfTheHalls.keywords.trample
#guard guardianOfTheHalls.activatedAbilities.size == 1
#guard guardianOfTheHalls.activatedAbilities[0]!.effect == Effect.putPlusOnePlusOneOnSource 3
#guard guardianOfTheHalls.activatedAbilities[0]!.cost.mana ==
  (ManaCost.ofGenericAndColors 5 [.green, .green])
#guard guardianOfTheHalls.power == some 2
#guard guardianOfTheHalls.toughness == some 2
#guard (guardianOfTheHalls.summary.splitOn "trample").length > 1
#guard (guardianOfTheHalls.summary.splitOn "+1/+1").length > 1
#guard desolationProwler.activatedAbilities.size == 1
#guard desolationProwler.activatedAbilities[0]!.effect == Effect.sourceGets 2 2
#guard desolationProwler.activatedAbilities[0]!.cost.payLife == 2
#guard desolationProwler.activatedAbilities[0]!.onceEachTurn
#guard desolationProwler.power == some 2
#guard desolationProwler.toughness == some 2
#guard (desolationProwler.summary.splitOn "Pay 2 life").length > 1
#guard raveningWarg.keywords.deathtouch
#guard raveningWarg.triggeredAbilities == #[.onAttackFerociousGainLife 2]
#guard raveningWarg.power == some 2
#guard raveningWarg.toughness == some 2
#guard (raveningWarg.summary.splitOn "deathtouch").length > 1
#guard (raveningWarg.summary.splitOn "Ferocious").length > 1
#guard (raveningWarg.summary.splitOn "power 4 or greater").length > 1
#guard (raveningWarg.summary.splitOn "gain 2 life").length > 1
#guard frontPorchSentries.triggeredAbilities == #[.onDiesOppCreatureGets (-1) (-1)]
#guard (frontPorchSentries.summary.splitOn "-1/-1").length > 1
#guard greatFierceBee.keywords.flying
#guard greatFierceBee.triggeredAbilities == #[.onOneOrMoreOtherCreaturesDieScry 1]
#guard (greatFierceBee.summary.splitOn "other creatures die").length > 1
#guard stirUpTrouble.spellEffect == some (Effect.destroyCreature)
#guard stirUpTrouble.additionalCostSacrificeArtifactOrCreature
#guard stirUpTrouble.additionalCostOrPayGeneric == some 4
#guard gollumSilentSlinker.keywords.menace
#guard (gollumSilentSlinker.summary.splitOn "menace").length > 1
#guard bilbosDeadlySlice.spellEffect == some (Effect.destroyCreature)
#guard bilbosDeadlySlice.requiresTarget
#guard dreadedBatCloud.costReductionIfCreatureDied == 3
#guard dreadedBatCloud.keywords.flying
#guard dreadedBatCloud.keywords.deathtouch
#guard crudeBentBlade.isEquipment
#guard crudeBentBlade.staticAbilities == #[.equippedCreatureGets 2 1]
#guard crudeBentBlade.triggeredAbilities == #[.onEnterTargetOpponentSacrificesCreature]
#guard crudeBentBlade.activatedAbilities.size == 1
#guard gollumTheAbandoned.staticAbilities == #[.cantBlockUnlessYouControl #[]]
#guard gollumTheAbandoned.triggeredAbilities == #[.onEnterExileOppGyCardOppsLoseLife 2]
#guard gollumTheAbandoned.activatedAbilities[0]!.activateFromGraveyard
#guard gollumTheAbandoned.activatedAbilities[0]!.onlyAsSorcery
#guard gollumTheAbandoned.activatedAbilities[0]!.effect == Effect.returnFromGraveyardToHand
#guard gnashingOfTeeth.isModal
#guard gnashingOfTeeth.spellModes ==
  #[Effect.pumpAndExileIfDies (-5) (-5),
    Effect.creaturesTargetPlayerGet (-1) (-1)]
#guard reverentHowl.isModal
#guard reverentHowl.spellModes ==
  #[Effect.targetPlayerDrawLoseLife 2 2,
    Effect.pumpAndLifelink 2 2]
#guard stonyVoicedGoblins.triggeredAbilities == #[.onEnterEachOpponentDiscards]
#guard gollumSilentSlinker.power == some 4
#guard gollumSilentSlinker.toughness == some 3
#guard gollumSilentSlinker.supertypes.any (· == .legendary)
#guard !(gollumSilentSlinker.summary.splitOn "can't be blocked except").length > 1
#guard bilbosDeadlySlice.isInstant
#guard bilbosDeadlySlice.hasCastKind .destroyCreature
#guard (bilbosDeadlySlice.summary.splitOn "Destroy target creature").length > 1
#guard smaugTheGreatCalamity.keywords.flying
#guard smaugTheGreatCalamity.hasAdventure
#guard smaugTheGreatCalamity.supertypes.any (· == .legendary)
#guard smaugTheGreatCalamity.power == some 5
#guard smaugTheGreatCalamity.toughness == some 5
#guard
  match smaugTheGreatCalamity.adventure with
  | some adv =>
    adv.name == "Spew Flame" &&
      adv.manaCost == (ManaCost.ofGenericAndColor 4 .red) &&
      adv.types == #[.sorcery] &&
      adv.subtypes.any (· == "Adventure") &&
      adv.spellEffect == some (Effect.dealDamageToCreature 5)
  | none => false
#guard (smaugTheGreatCalamity.oracleText.splitOn "//ADV//").length > 1
#guard (smaugTheGreatCalamity.oracleText.splitOn "{4}{R}").length > 1
#guard !smaugTheGreatCalamity.leftoverOracleLines.any (· == "//ADV//")
#guard (smaugTheGreatCalamity.summary.splitOn "//ADV//").length == 1
#guard (smaugTheGreatCalamity.summary.splitOn "Spew Flame {4}{R}").length > 1
#guard (smaugTheGreatCalamity.summary.splitOn "flying").length > 1
#guard beornReluctantHost.keywords.trample
#guard beornReluctantHost.hasAdventure
#guard beornReluctantHost.supertypes.any (· == .legendary)
#guard beornReluctantHost.power == some 5
#guard beornReluctantHost.toughness == some 5
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
#guard (bilboBagginsBurglar.oracleText.splitOn "//ADV//").length > 1
#guard (bilboBagginsBurglar.oracleText.splitOn "Take a Glance {U}").length > 1
#guard (bilboLuckwearer.oracleText.splitOn "//ADV//").length > 1
#guard (bilboLuckwearer.oracleText.splitOn "Burglar's Plot {4}{U}").length > 1
#guard (gollumSilentSlinker.oracleText.splitOn "//ADV//").length > 1
#guard (gollumSilentSlinker.oracleText.splitOn "Meager Meal {B}").length > 1

end Mtg.Engine.Catalog
