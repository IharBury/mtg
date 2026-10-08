import Mtg.Engine.Card
import Mtg.Engine.Catalog
import Mtg.Engine.Catalog.HobbitEternal

/-!
# Reality Fracture Commander catalog

Oracle characteristics for every card in Magic: The Gathering | Reality Fracture
Commander (FRC). Each card is defined by its printed text. Arcane Signet is
the same card as the Hobbit Eternal printing.
-/

namespace Mtg.Engine.Catalog

open Mtg.Engine

def akromaAngelOfFury : CardDef :=
  fromOracleKeeping [
    "Akroma, Angel of Fury",
    "{5}{R}{R}{R}",
    "Legendary Creature — Angel",
    "6/6",
    "This spell can't be countered.",
    "Flying, trample, protection from white and from blue",
    "{R}: Akroma gets +1/+0 until end of turn.",
    "Morph {3}{R}{R}{R} (You may cast this card face down as a 2/2 creature for {3}. Turn her face up any time for her morph cost.)"
  ]

def archfiendOfDespair : CardDef :=
  fromOracleKeeping [
    "Archfiend of Despair",
    "{6}{B}{B}",
    "Creature — Demon",
    "6/6",
    "Flying",
    "Your opponents can't gain life.",
    "At the beginning of each end step, each opponent loses life equal to the life that player lost this turn. (Damage causes loss of life.)"
  ]

def archonOfCruelty : CardDef :=
  fromOracleKeeping [
    "Archon of Cruelty",
    "{6}{B}{B}",
    "Creature — Archon",
    "6/6",
    "Flying",
    "Whenever this creature enters or attacks, target opponent sacrifices a creature or planeswalker of their choice, discards a card, and loses 3 life. You draw a card and gain 3 life."
  ]

def avacynAngelOfHorror : CardDef :=
  fromOracleKeeping [
    "Avacyn, Angel of Horror",
    "{5}{B}{B}{B}",
    "Legendary Creature — Angel",
    "8/8",
    "Flying, deathtouch",
    "Whenever Avacyn or another nontoken creature you control dies, return that card to the battlefield under your control at the beginning of the next end step."
  ]

def azoriusSignet : CardDef :=
  fromOracleKeeping [
    "Azorius Signet",
    "{2}",
    "Artifact",
    "{1}, {T}: Add {W}{U}."
  ]

def battlefieldForge : CardDef :=
  fromOracleKeeping [
    "Battlefield Forge",
    "Land",
    "{T}: Add {C}.",
    "{T}: Add {R} or {W}. This land deals 1 damage to you."
  ]

def brainstorm : CardDef :=
  fromOracleKeeping [
    "Brainstorm",
    "{U}",
    "Instant",
    "Draw three cards, then put two cards from your hand on top of your library in any order."
  ]

def brainsurge : CardDef :=
  fromOracleKeeping [
    "Brainsurge",
    "{2}{U}",
    "Instant",
    "Draw four cards, then put two cards from your hand on top of your library in any order."
  ]

def cavesOfKoilos : CardDef :=
  fromOracleKeeping [
    "Caves of Koilos",
    "Land",
    "{T}: Add {C}.",
    "{T}: Add {W} or {B}. This land deals 1 damage to you."
  ]

def chromaticLantern : CardDef :=
  fromOracleKeeping [
    "Chromatic Lantern",
    "{3}",
    "Artifact",
    "Lands you control have \"{T}: Add one mana of any color.\"",
    "{T}: Add one mana of any color."
  ]

def clifftopRetreat : CardDef :=
  fromOracleKeeping [
    "Clifftop Retreat",
    "Land",
    "This land enters tapped unless you control a Mountain or a Plains.",
    "{T}: Add {R} or {W}."
  ]

def commandTower : CardDef :=
  fromOracleKeeping [
    "Command Tower",
    "Land",
    "{T}: Add one mana of any color in your commander's color identity."
  ]

def contaminatedLandscape : CardDef :=
  fromOracleKeeping [
    "Contaminated Landscape",
    "Land",
    "{T}: Add {C}.",
    "{T}, Sacrifice this land: Search your library for a basic Plains, Island, or Swamp card, put it onto the battlefield tapped, then shuffle.",
    "Cycling {W}{U}{B} ({W}{U}{B}, Discard this card: Draw a card.)"
  ]

def currencyConverter : CardDef :=
  fromOracleKeeping [
    "Currency Converter",
    "{1}",
    "Artifact",
    "Whenever you discard a card, you may exile that card from your graveyard.",
    "{2}, {T}: Draw a card, then discard a card.",
    "{T}: Put a card exiled with this artifact into its owner's graveyard. If it's a land card, create a Treasure token. If it's a nonland card, create a 2/2 black Rogue creature token."
  ]

def cursedMirror : CardDef :=
  fromOracleKeeping [
    "Cursed Mirror",
    "{2}{R}",
    "Artifact",
    "{T}: Add {R}.",
    "As this artifact enters, you may have it become a copy of any creature on the battlefield until end of turn, except it has haste."
  ]

def dackFaydenHelpingHand : CardDef :=
  fromOracleKeeping [
    "Dack Fayden, Helping Hand",
    "{4}{W}{W}",
    "Legendary Creature — Human Advisor",
    "4/6",
    "When Dack Fayden enters, reveal cards from the top of your library until you reveal X creature cards, where X is the number of opponents you have. Put those creature cards onto the battlefield, then shuffle. They're goaded for the rest of the game. For each of those permanents, choose a different opponent. Each opponent gains control of the permanent for which they were chosen."
  ]

def darksteelAngel : CardDef :=
  fromOracleKeeping [
    "Darksteel Angel",
    "{9}",
    "Artifact Creature — Angel",
    "4/4",
    "Flying, indestructible",
    "You can't lose the game and your opponents can't win the game.",
    "Creatures you control can't have -1/-1 counters put on them."
  ]

def despark : CardDef :=
  fromOracleKeeping [
    "Despark",
    "{W}{B}",
    "Instant",
    "Exile target permanent with mana value 4 or greater."
  ]

def dimirSignet : CardDef :=
  fromOracleKeeping [
    "Dimir Signet",
    "{2}",
    "Artifact",
    "{1}, {T}: Add {U}{B}."
  ]

def dreadhordeInvasion : CardDef :=
  fromOracleKeeping [
    "Dreadhorde Invasion",
    "{1}{B}",
    "Enchantment",
    "At the beginning of your upkeep, you lose 1 life and amass Zombies 1. (Put a +1/+1 counter on an Army you control. It's also a Zombie. If you don't control an Army, create a 0/0 black Zombie Army creature token first.)",
    "Whenever a Zombie token you control with power 6 or greater attacks, it gains lifelink until end of turn."
  ]

def drownedCatacomb : CardDef :=
  fromOracleKeeping [
    "Drowned Catacomb",
    "Land",
    "This land enters tapped unless you control an Island or a Swamp.",
    "{T}: Add {U} or {B}."
  ]

def elspethSunsChampion : CardDef :=
  fromOracleKeeping [
    "Elspeth, Sun's Champion",
    "{4}{W}{W}",
    "Legendary Planeswalker — Elspeth",
    "+1: Create three 1/1 white Soldier creature tokens.",
    "−3: Destroy all creatures with power 4 or greater.",
    "−7: You get an emblem with \"Creatures you control get +2/+2 and have flying.\"",
    "Loyalty: 4"
  ]

def exoticOrchard : CardDef :=
  fromOracleKeeping [
    "Exotic Orchard",
    "Land",
    "{T}: Add one mana of any color that a land an opponent controls could produce."
  ]

def fabledPassage : CardDef :=
  fromOracleKeeping [
    "Fabled Passage",
    "Land",
    "{T}, Sacrifice this land: Search your library for a basic land card, put it onto the battlefield tapped, then shuffle. Then if you control four or more lands, untap that land."
  ]

def factOrFiction : CardDef :=
  fromOracleKeeping [
    "Fact or Fiction",
    "{3}{U}",
    "Instant",
    "Reveal the top five cards of your library. An opponent separates those cards into two piles. Put one pile into your hand and the other into your graveyard."
  ]

def fellwarStone : CardDef :=
  fromOracleKeeping [
    "Fellwar Stone",
    "{2}",
    "Artifact",
    "{T}: Add one mana of any color that a land an opponent controls could produce."
  ]

def fetidHeath : CardDef :=
  fromOracleKeeping [
    "Fetid Heath",
    "Land",
    "{T}: Add {C}.",
    "{W/B}, {T}: Add {W}{W}, {W}{B}, or {B}{B}."
  ]

def flawlessManeuver : CardDef :=
  fromOracleKeeping [
    "Flawless Maneuver",
    "{2}{W}",
    "Instant",
    "If you control a commander, you may cast this spell without paying its mana cost.",
    "Creatures you control gain indestructible until end of turn."
  ]

def gingerQueenOfSweets : CardDef :=
  fromOracleKeeping [
    "Ginger, Queen of Sweets",
    "{6}",
    "Legendary Artifact Creature — Food Noble",
    "6/4",
    "When Ginger enters, you become the monarch.",
    "{2}, {T}, Sacrifice Ginger: You gain 6 life.",
    "At the beginning of each upkeep, if you're the monarch, create a Gingerbrute token. (It's a {1} 1/1 Food Golem artifact creature with haste, \"{1}: This token can't be blocked this turn except by creatures with haste,\" and \"{2}, {T}, Sacrifice this token: You gain 3 life.\")"
  ]

def glacialFortress : CardDef :=
  fromOracleKeeping [
    "Glacial Fortress",
    "Land",
    "This land enters tapped unless you control a Plains or an Island.",
    "{T}: Add {W} or {U}."
  ]

def grandCrescendo : CardDef :=
  fromOracleKeeping [
    "Grand Crescendo",
    "{X}{W}{W}",
    "Instant",
    "Create X 1/1 green and white Citizen creature tokens. Creatures you control gain indestructible until end of turn."
  ]

def isolatedChapel : CardDef :=
  fromOracleKeeping [
    "Isolated Chapel",
    "Land",
    "This land enters tapped unless you control a Plains or a Swamp.",
    "{T}: Add {W} or {B}."
  ]

def izzetSignet : CardDef :=
  fromOracleKeeping [
    "Izzet Signet",
    "{2}",
    "Artifact",
    "{1}, {T}: Add {U}{R}."
  ]

def jaceMultiverseArchitect : CardDef :=
  fromOracleKeeping [
    "Jace, Multiverse Architect",
    "{1}{W}{U}{B}{R}",
    "Legendary Planeswalker — Jace",
    "At the beginning of combat on each opponent's turn, they may pay {2}. If they don't, creatures they control can't attack Jaces you control this turn.",
    "+1: Draw two cards, then put a card from your hand on the bottom of your library.",
    "−3: Exile another target planeswalker or creature you control. Reveal cards from the top of your library until you reveal a creature or planeswalker card. Put that card onto the battlefield and the rest on the bottom of your library in a random order.",
    "Jace, Multiverse Architect can be your commander.",
    "Loyalty: 4"
  ]

def jhoiraWeatherlightCorsair : CardDef :=
  fromOracleKeeping [
    "Jhoira, Weatherlight Corsair",
    "{4}{B}{B}",
    "Legendary Creature — Human Pirate",
    "4/5",
    "Whenever Jhoira enters or attacks, target opponent reveals cards from the top of their library until they reveal a historic permanent card. You put that card onto the battlefield under your control and lose life equal to that permanent's mana value. That player puts the rest of the revealed cards on the bottom of their library in a random order. (Artifacts, legendaries, and Sagas are historic.)"
  ]

def kherKeep : CardDef :=
  fromOracleKeeping [
    "Kher Keep",
    "Legendary Land",
    "{T}: Add {C}.",
    "{1}{R}, {T}: Create a 0/1 red Kobold creature token named Kobolds of Kher Keep."
  ]

def lingeringSouls : CardDef :=
  fromOracleKeeping [
    "Lingering Souls",
    "{2}{W}",
    "Sorcery",
    "Create two 1/1 white Spirit creature tokens with flying.",
    "Flashback {1}{B} (You may cast this card from your graveyard for its flashback cost. Then exile it.)"
  ]

def martialCoup : CardDef :=
  fromOracleKeeping [
    "Martial Coup",
    "{X}{W}{W}",
    "Sorcery",
    "Create X 1/1 white Soldier creature tokens. If X is 5 or more, destroy all other creatures."
  ]

def massPolymorph : CardDef :=
  fromOracleKeeping [
    "Mass Polymorph",
    "{5}{U}",
    "Sorcery",
    "Exile all creatures you control, then reveal cards from the top of your library until you reveal that many creature cards. Put all creature cards revealed this way onto the battlefield, then shuffle the rest of the revealed cards into your library."
  ]

def memnarchTheWarden : CardDef :=
  fromOracleKeeping [
    "Memnarch, the Warden",
    "{10}",
    "Legendary Artifact Creature — Wizard",
    "8/9",
    "Indestructible",
    "When Memnarch enters, create two 1/1 colorless Myr artifact creature tokens.",
    "Whenever Memnarch attacks, draw a card for each artifact you control."
  ]

def mysticGate : CardDef :=
  fromOracleKeeping [
    "Mystic Gate",
    "Land",
    "{T}: Add {C}.",
    "{W/U}, {T}: Add {W}{W}, {W}{U}, or {U}{U}."
  ]

def nissaLeylineTamer : CardDef :=
  fromOracleKeeping [
    "Nissa, Leyline Tamer",
    "{3}{W}{U}{B}{R}",
    "Legendary Creature — Elf Wizard",
    "5/5",
    "Deathtouch, vigilance",
    "Landfall — Whenever a land you control enters, draw a card. Then if this is the first time this ability has resolved this turn, reveal cards from the top of your library until you reveal a creature card. Put that card onto the battlefield and the rest on the bottom of your library in a random order."
  ]

def nivMizzetGhostCounsel : CardDef :=
  fromOracleKeeping [
    "Niv-Mizzet, Ghost Counsel",
    "{2}{W}{W}{B}{B}",
    "Legendary Creature — Spirit Dragon",
    "4/4",
    "Flying",
    "Whenever you gain life, you may pay that much life. If you do, draw that many cards.",
    "{T}: Each opponent loses 1 life and you gain 1 life."
  ]

def obNixilisTheAscended : CardDef :=
  fromOracleKeeping [
    "Ob Nixilis, the Ascended",
    "{5}{W}{W}",
    "Legendary Creature — Angel",
    "4/4",
    "Flying",
    "When Ob Nixilis enters, destroy all tapped creatures your opponents control. You gain 1 life for each creature destroyed this way.",
    "At the beginning of each end step, if you gained life this turn, create a 4/4 white Angel creature token with flying."
  ]

def occultEpiphany : CardDef :=
  fromOracleKeeping [
    "Occult Epiphany",
    "{X}{U}",
    "Instant",
    "Draw X cards, then discard X cards. Create a 1/1 white Spirit creature token with flying for each card type among cards discarded this way."
  ]

def omnathLocusOfTheVoid : CardDef :=
  fromOracleKeeping [
    "Omnath, Locus of the Void",
    "{7}",
    "Legendary Creature — Elemental",
    "6/6",
    "Omnath gets +1/+1 for each unspent mana you have.",
    "If you would lose unspent mana, that mana becomes colorless instead.",
    "Landfall — Whenever a land you control enters, add {C}{C}."
  ]

def overlordOfTheMistmoors : CardDef :=
  fromOracleKeeping [
    "Overlord of the Mistmoors",
    "{5}{W}{W}",
    "Enchantment Creature — Avatar Horror",
    "6/6",
    "Impending 4—{2}{W}{W} (If you cast this spell for its impending cost, it enters with four time counters and isn't a creature until the last is removed. At the beginning of your end step, remove a time counter from it.)",
    "Whenever this permanent enters or attacks, create two 2/1 white Insect creature tokens with flying."
  ]

def pathOfAncestry : CardDef :=
  fromOracleKeeping [
    "Path of Ancestry",
    "Land",
    "This land enters tapped.",
    "{T}: Add one mana of any color in your commander's color identity. When that mana is spent to cast a creature spell that shares a creature type with your commander, scry 1. (Look at the top card of your library. You may put that card on the bottom.)"
  ]

def pathToExile : CardDef :=
  fromOracleKeeping [
    "Path to Exile",
    "{W}",
    "Instant",
    "Exile target creature. Its controller may search their library for a basic land card, put that card onto the battlefield tapped, then shuffle."
  ]

def perilousLandscape : CardDef :=
  fromOracleKeeping [
    "Perilous Landscape",
    "Land",
    "{T}: Add {C}.",
    "{T}, Sacrifice this land: Search your library for a basic Island, Mountain, or Plains card, put it onto the battlefield tapped, then shuffle.",
    "Cycling {U}{R}{W} ({U}{R}{W}, Discard this card: Draw a card.)"
  ]

def prairieStream : CardDef :=
  fromOracleKeeping [
    "Prairie Stream",
    "Land — Plains Island",
    "({T}: Add {W} or {U}.)",
    "This land enters tapped unless you control two or more basic lands."
  ]

def proteusStaff : CardDef :=
  fromOracleKeeping [
    "Proteus Staff",
    "{3}",
    "Artifact",
    "{2}{U}, {T}: Put target creature on the bottom of its owner's library. That creature's controller reveals cards from the top of their library until they reveal a creature card. The player puts that card onto the battlefield and the rest on the bottom of their library in any order. Activate only as a sorcery."
  ]

def radiantSummit : CardDef :=
  fromOracleKeeping [
    "Radiant Summit",
    "Land — Mountain Plains",
    "({T}: Add {R} or {W}.)",
    "This land enters tapped unless you control two or more basic lands."
  ]

def rakdosSignet : CardDef :=
  fromOracleKeeping [
    "Rakdos Signet",
    "{2}",
    "Artifact",
    "{1}, {T}: Add {B}{R}."
  ]

def reflectingPool : CardDef :=
  fromOracleKeeping [
    "Reflecting Pool",
    "Land",
    "{T}: Add one mana of any type that a land you control could produce."
  ]

def restlessAnchorage : CardDef :=
  fromOracleKeeping [
    "Restless Anchorage",
    "Land",
    "This land enters tapped.",
    "{T}: Add {W} or {U}.",
    "{1}{W}{U}: Until end of turn, this land becomes a 2/3 white and blue Bird creature with flying. It's still a land.",
    "Whenever this land attacks, create a Map token."
  ]

def restlessSpire : CardDef :=
  fromOracleKeeping [
    "Restless Spire",
    "Land",
    "This land enters tapped.",
    "{T}: Add {U} or {R}.",
    "{U}{R}: Until end of turn, this land becomes a 2/1 blue and red Elemental creature with \"During your turn, this creature has first strike.\" It's still a land.",
    "Whenever this land attacks, scry 1."
  ]

def secureTheWastes : CardDef :=
  fromOracleKeeping [
    "Secure the Wastes",
    "{X}{W}",
    "Instant",
    "Create X 1/1 white Warrior creature tokens."
  ]

def serrasEmissary : CardDef :=
  fromOracleKeeping [
    "Serra's Emissary",
    "{4}{W}{W}{W}",
    "Creature — Angel",
    "7/7",
    "Flying",
    "As this creature enters, choose a card type.",
    "You and creatures you control have protection from the chosen card type."
  ]

def sharkTyphoon : CardDef :=
  fromOracleKeeping [
    "Shark Typhoon",
    "{5}{U}",
    "Enchantment",
    "Whenever you cast a noncreature spell, create an X/X blue Shark creature token with flying, where X is that spell's mana value.",
    "Cycling {X}{1}{U} ({X}{1}{U}, Discard this card: Draw a card.)",
    "When you cycle this card, create an X/X blue Shark creature token with flying."
  ]

def shivanReef : CardDef :=
  fromOracleKeeping [
    "Shivan Reef",
    "Land",
    "{T}: Add {C}.",
    "{T}: Add {U} or {R}. This land deals 1 damage to you."
  ]

def skrelvsHive : CardDef :=
  fromOracleKeeping [
    "Skrelv's Hive",
    "{1}{W}",
    "Enchantment",
    "At the beginning of your upkeep, you lose 1 life and create a 1/1 colorless Phyrexian Mite artifact creature token with toxic 1 and \"This token can't block.\"",
    "Corrupted — As long as an opponent has three or more poison counters, creatures you control with toxic have lifelink."
  ]

def solRing : CardDef :=
  fromOracleKeeping [
    "Sol Ring",
    "{1}",
    "Artifact",
    "{T}: Add {C}{C}."
  ]

def staffOfTheStoryteller : CardDef :=
  fromOracleKeeping [
    "Staff of the Storyteller",
    "{1}{W}",
    "Artifact",
    "When this artifact enters, create a 1/1 white Spirit creature token with flying.",
    "Whenever you create one or more creature tokens, put a story counter on this artifact.",
    "{W}, {T}, Remove a story counter from this artifact: Draw a card."
  ]

def strokeOfMidnight : CardDef :=
  fromOracleKeeping [
    "Stroke of Midnight",
    "{2}{W}",
    "Instant",
    "Destroy target nonland permanent. Its controller creates a 1/1 white Human creature token."
  ]

def sulfurFalls : CardDef :=
  fromOracleKeeping [
    "Sulfur Falls",
    "Land",
    "This land enters tapped unless you control an Island or a Mountain.",
    "{T}: Add {U} or {R}."
  ]

def sulfurousSprings : CardDef :=
  fromOracleKeeping [
    "Sulfurous Springs",
    "Land",
    "{T}: Add {C}.",
    "{T}: Add {B} or {R}. This land deals 1 damage to you."
  ]

def sunfall : CardDef :=
  fromOracleKeeping [
    "Sunfall",
    "{3}{W}{W}",
    "Sorcery",
    "Exile all creatures. Incubate X, where X is the number of creatures exiled this way. (Create an Incubator token with X +1/+1 counters on it and \"{2}: Transform this token.\" It transforms into a 0/0 Phyrexian artifact creature.)"
  ]

def sunkenRuins : CardDef :=
  fromOracleKeeping [
    "Sunken Ruins",
    "Land",
    "{T}: Add {C}.",
    "{U/B}, {T}: Add {U}{U}, {U}{B}, or {B}{B}."
  ]

def swordsToPlowshares : CardDef :=
  fromOracleKeeping [
    "Swords to Plowshares",
    "{W}",
    "Instant",
    "Exile target creature. Its controller gains life equal to its power."
  ]

def syntheticDestiny : CardDef :=
  fromOracleKeeping [
    "Synthetic Destiny",
    "{4}{U}{U}",
    "Instant",
    "Exile all creatures you control. At the beginning of the next end step, reveal cards from the top of your library until you reveal that many creature cards, put all creature cards revealed this way onto the battlefield, then shuffle the rest of the revealed cards into your library."
  ]

def talismanOfCreativity : CardDef :=
  fromOracleKeeping [
    "Talisman of Creativity",
    "{2}",
    "Artifact",
    "{T}: Add {C}.",
    "{T}: Add {U} or {R}. This artifact deals 1 damage to you."
  ]

def talismanOfDominance : CardDef :=
  fromOracleKeeping [
    "Talisman of Dominance",
    "{2}",
    "Artifact",
    "{T}: Add {C}.",
    "{T}: Add {U} or {B}. This artifact deals 1 damage to you."
  ]

def talismanOfIndulgence : CardDef :=
  fromOracleKeeping [
    "Talisman of Indulgence",
    "{2}",
    "Artifact",
    "{T}: Add {C}.",
    "{T}: Add {B} or {R}. This artifact deals 1 damage to you."
  ]

def talismanOfProgress : CardDef :=
  fromOracleKeeping [
    "Talisman of Progress",
    "{2}",
    "Artifact",
    "{T}: Add {C}.",
    "{T}: Add {W} or {U}. This artifact deals 1 damage to you."
  ]

def tamiyoUpriserCrowned : CardDef :=
  fromOracleKeeping [
    "Tamiyo, Upriser Crowned",
    "{4}{R}{W}",
    "Legendary Creature — Moonfolk Warrior",
    "3/5",
    "Flying, double strike, haste",
    "When Tamiyo enters, you become the monarch.",
    "Whenever one or more creatures deal combat damage to you while you're the monarch, tap those creatures and put a stun counter on each of them."
  ]

def teferisReproach : CardDef :=
  fromOracleKeeping [
    "Teferi's Reproach",
    "{2}{W}",
    "Instant",
    "Choose target opponent. Until that player's next turn, they gain protection from everything and their life total can't change. All nonland permanents they control phase out. (While they're phased out, they're treated as though they don't exist. They phase in before that player untaps during their next untap step.)",
    "Exile Teferi's Reproach."
  ]

def theUrSphinx : CardDef :=
  fromOracleKeeping [
    "The Ur-Sphinx",
    "{6}{W}{U}{B}",
    "Legendary Creature — Sphinx Avatar",
    "10/10",
    "Eminence — As long as The Ur-Sphinx is in the command zone or on the battlefield, other Sphinx spells you cast cost {1} less to cast.",
    "Flying",
    "Whenever one or more Sphinxes you control attack, each player mills that many cards. For each player, you may cast a card that player milled this way without paying its mana cost."
  ]

def turbulentCrater : CardDef :=
  fromOracleKeeping [
    "Turbulent Crater",
    "Land — Swamp Mountain",
    "({T}: Add {B} or {R}.)",
    "This land enters tapped unless your opponents control eight or more lands."
  ]

def turbulentShore : CardDef :=
  fromOracleKeeping [
    "Turbulent Shore",
    "Land — Plains Island",
    "({T}: Add {W} or {U}.)",
    "This land enters tapped unless your opponents control eight or more lands."
  ]

def turbulentWetlands : CardDef :=
  fromOracleKeeping [
    "Turbulent Wetlands",
    "Land — Island Swamp",
    "({T}: Add {U} or {B}.)",
    "This land enters tapped unless your opponents control eight or more lands."
  ]

def undergroundRiver : CardDef :=
  fromOracleKeeping [
    "Underground River",
    "Land",
    "{T}: Add {C}.",
    "{T}: Add {U} or {B}. This land deals 1 damage to you."
  ]

def venserFerventForger : CardDef :=
  fromOracleKeeping [
    "Venser, Fervent Forger",
    "{4}{R}{R}",
    "Legendary Creature — Human Sorcerer",
    "5/3",
    "Flash",
    "When Venser enters, choose one —",
    "• Copy target instant or sorcery spell an opponent controls twice. You may choose new targets for the copies.",
    "• Create two tokens that are copies of target permanent an opponent controls. They gain haste. At the beginning of the next end step, sacrifice them."
  ]

def whirlwindOfThought : CardDef :=
  fromOracleKeeping [
    "Whirlwind of Thought",
    "{1}{U}{R}{W}",
    "Enchantment",
    "Whenever you cast a noncreature spell, draw a card."
  ]

def whiteSunsTwilight : CardDef :=
  fromOracleKeeping [
    "White Sun's Twilight",
    "{X}{W}{W}",
    "Sorcery",
    "You gain X life. Create X 1/1 colorless Phyrexian Mite artifact creature tokens with toxic 1 and \"This token can't block.\" If X is 5 or more, destroy all other creatures. (Players dealt combat damage by a creature with toxic 1 also get a poison counter.)"
  ]

def windcragSiege : CardDef :=
  fromOracleKeeping [
    "Windcrag Siege",
    "{1}{R}{W}",
    "Enchantment",
    "As this enchantment enters, choose Mardu or Jeskai.",
    "• Mardu — If a creature attacking causes a triggered ability of a permanent you control to trigger, that ability triggers an additional time.",
    "• Jeskai — At the beginning of your upkeep, create a 1/1 red Goblin creature token. It gains lifelink and haste until end of turn."
  ]

def realityFractureCommanderCards : Array CardDef := #[
    akromaAngelOfFury,
    arcaneSignet,
    archfiendOfDespair,
    archonOfCruelty,
    avacynAngelOfHorror,
    azoriusSignet,
    battlefieldForge,
    brainstorm,
    brainsurge,
    cavesOfKoilos,
    chromaticLantern,
    clifftopRetreat,
    commandTower,
    contaminatedLandscape,
    currencyConverter,
    cursedMirror,
    dackFaydenHelpingHand,
    darksteelAngel,
    despark,
    dimirSignet,
    dreadhordeInvasion,
    drownedCatacomb,
    elspethSunsChampion,
    exoticOrchard,
    fabledPassage,
    factOrFiction,
    fellwarStone,
    fetidHeath,
    flawlessManeuver,
    gingerQueenOfSweets,
    glacialFortress,
    grandCrescendo,
    isolatedChapel,
    izzetSignet,
    jaceMultiverseArchitect,
    jhoiraWeatherlightCorsair,
    kherKeep,
    lingeringSouls,
    martialCoup,
    massPolymorph,
    memnarchTheWarden,
    mysticGate,
    nissaLeylineTamer,
    nivMizzetGhostCounsel,
    obNixilisTheAscended,
    occultEpiphany,
    omnathLocusOfTheVoid,
    overlordOfTheMistmoors,
    pathOfAncestry,
    pathToExile,
    perilousLandscape,
    prairieStream,
    proteusStaff,
    radiantSummit,
    rakdosSignet,
    reflectingPool,
    restlessAnchorage,
    restlessSpire,
    secureTheWastes,
    serrasEmissary,
    sharkTyphoon,
    shivanReef,
    skrelvsHive,
    solRing,
    staffOfTheStoryteller,
    strokeOfMidnight,
    sulfurFalls,
    sulfurousSprings,
    sunfall,
    sunkenRuins,
    swordsToPlowshares,
    syntheticDestiny,
    talismanOfCreativity,
    talismanOfDominance,
    talismanOfIndulgence,
    talismanOfProgress,
    tamiyoUpriserCrowned,
    teferisReproach,
    theUrSphinx,
    turbulentCrater,
    turbulentShore,
    turbulentWetlands,
    undergroundRiver,
    venserFerventForger,
    whirlwindOfThought,
    whiteSunsTwilight,
    windcragSiege
  ]

end Mtg.Engine.Catalog
