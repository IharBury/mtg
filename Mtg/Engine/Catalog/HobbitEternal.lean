import Mtg.Engine.Card
import Mtg.Engine.Catalog

/-!
# The Hobbit Eternal catalog

Oracle characteristics for cards from Magic: The Gathering | The Hobbit
Eternal (HOC). Each card is defined by its full printed text.
`hobbitEternalCards` lists every unique card in the set,
including reprints that also appear in other sets.
-/

namespace Mtg.Engine.Catalog

open Mtg.Engine

def mentorOfTheMeek : CardDef :=
  fromOracle [
    "Mentor of the Meek",
    "{2}{W}",
    "Creature — Human Soldier",
    "2/2",
    "Whenever another creature you control with power 2 or less enters, you may pay {1}. If you do, draw a card.",
  ]

def fiendHunter : CardDef :=
  fromOracle [
    "Fiend Hunter",
    "{1}{W}{W}",
    "Creature — Human Cleric",
    "1/3",
    "When this creature enters, you may exile another target creature.",
    "When this creature leaves the battlefield, return the exiled card to the battlefield under its owner's control.",
  ]

def errandRiderOfGondor : CardDef :=
  fromOracle [
    "Errand-Rider of Gondor",
    "{2}{W}",
    "Creature — Human Soldier",
    "3/2",
    "When this creature enters, draw a card. Then if you don't control a legendary creature, put a card from your hand on the bottom of your library.",
  ]

def landrovalHorizonWitness : CardDef :=
  fromOracle [
    "Landroval, Horizon Witness",
    "{4}{W}",
    "Legendary Creature — Bird Noble",
    "3/4",
    "Flying",
    "Whenever two or more creatures you control attack a player, target attacking creature without flying gains flying until end of turn.",
  ]

def roguesPassage : CardDef :=
  fromOracle [
    "Rogue's Passage",
    "Land",
    "{T}: Add {C}.",
    "{4}, {T}: Target creature can't be blocked this turn.",
  ]

def soldierOfTheGreyHost : CardDef :=
  fromOracle [
    "Soldier of the Grey Host",
    "{3}{W}",
    "Creature — Spirit Soldier",
    "2/2",
    "Flash",
    "Flying",
    "When this creature enters, target creature gets +2/+0 until end of turn.",
  ]

def eaglesOfTheNorth : CardDef :=
  fromOracle [
    "Eagles of the North",
    "{5}{W}",
    "Creature — Bird Soldier",
    "3/3",
    "Flying",
    "When this creature enters, creatures you control get +1/+0 and gain first strike until end of turn.",
    "Plainscycling {1} ({1}, Discard this card: Search your library for a Plains card, reveal it, put it into your hand, then shuffle.)",
  ]

def dunedainBlade : CardDef :=
  fromOracle [
    "Dúnedain Blade",
    "{1}{W}",
    "Artifact — Equipment",
    "Equipped creature gets +2/+1.",
    "Equip Human {1}",
    "Equip {3} ({3}: Attach to target creature you control. Equip only as a sorcery.)",
  ]

def fogOnTheBarrowDowns : CardDef :=
  fromOracle [
    "Fog on the Barrow-Downs",
    "{2}{W}",
    "Enchantment — Aura",
    "Enchant creature",
    "Enchanted creature is a Spirit and can't attack or block. (It loses all other creature types.)",
  ]

def banishingLight : CardDef :=
  fromOracle [
    "Banishing Light",
    "{2}{W}",
    "Enchantment",
    "When this enchantment enters, exile target nonland permanent an opponent controls until this enchantment leaves the battlefield.",
  ]

def dawnOfANewAge : CardDef :=
  fromOracle [
    "Dawn of a New Age",
    "{1}{W}",
    "Enchantment",
    "This enchantment enters with a hope counter on it for each creature you control.",
    "At the beginning of your end step, remove a hope counter from this enchantment. If you do, draw a card. Then if this enchantment has no hope counters on it, sacrifice it and you gain 4 life.",
  ]

def westfoldRider : CardDef :=
  fromOracle [
    "Westfold Rider",
    "{1}{W}",
    "Creature — Human Knight",
    "3/1",
    "Sacrifice this creature: Destroy target artifact or enchantment. Activate only as a sorcery.",
  ]

def esquireOfTheKing : CardDef :=
  fromOracle [
    "Esquire of the King",
    "{W}",
    "Creature — Human Soldier",
    "1/1",
    "{4}{W}, {T}: Creatures you control get +1/+1 until end of turn. This ability costs {2} less to activate if you control a legendary creature.",
  ]

def pelargirSurvivor : CardDef :=
  fromOracle [
    "Pelargir Survivor",
    "{1}{U}",
    "Creature — Human Peasant",
    "1/3",
    "{T}: Add one mana of any color. Spend this mana only to cast an instant or sorcery spell.",
    "{5}{U}, {T}: Target player mills three cards. (They put the top three cards of their library into their graveyard.)",
  ]

def lorienRevealed : CardDef :=
  fromOracle [
    "Lórien Revealed",
    "{3}{U}{U}",
    "Sorcery",
    "Draw three cards.",
    "Islandcycling {1} ({1}, Discard this card: Search your library for an Island card, reveal it, put it into your hand, then shuffle.)",
  ]

def knightsOfDolAmroth : CardDef :=
  fromOracle [
    "Knights of Dol Amroth",
    "{3}{U}",
    "Creature — Human Knight",
    "3/3",
    "Whenever you draw your second card each turn, put a +1/+1 counter on this creature.",
  ]

def greyHavensNavigator : CardDef :=
  fromOracle [
    "Grey Havens Navigator",
    "{2}{U}",
    "Creature — Elf Pilot",
    "3/2",
    "Flash",
    "When this creature enters, scry 1.",
  ]

def ithilienKingfisher : CardDef :=
  fromOracle [
    "Ithilien Kingfisher",
    "{2}{U}",
    "Creature — Bird",
    "2/1",
    "Flying",
    "When this creature dies, draw a card.",
  ]

def hithlainKnots : CardDef :=
  fromOracle [
    "Hithlain Knots",
    "{1}{U}",
    "Instant",
    "Tap target creature. Scry 1.",
    "Draw a card.",
  ]

def captainOfUmbar : CardDef :=
  fromOracle [
    "Captain of Umbar",
    "{2}{U}",
    "Creature — Human Pirate",
    "2/3",
    "{1}, {T}: Draw a card, then discard a card.",
  ]

def minasTirithGarrison : CardDef :=
  fromOracle [
    "Minas Tirith Garrison",
    "{3}{U}",
    "Creature — Human Soldier",
    "*/5",
    "Minas Tirith Garrison's power is equal to the number of cards in your hand.",
    "Whenever this creature attacks, you may tap any number of untapped Humans you control. Draw a card for each Human tapped this way.",
  ]

def colossalWhale : CardDef :=
  fromOracle [
    "Colossal Whale",
    "{5}{U}{U}",
    "Creature — Whale",
    "5/5",
    "Islandwalk (This creature can't be blocked as long as defending player controls an Island.)",
    "Whenever this creature attacks, you may exile target creature defending player controls until this creature leaves the battlefield. (That creature returns under its owner's control.)",
  ]

def willowWind : CardDef :=
  fromOracle [
    "Willow-Wind",
    "{4}{U}",
    "Creature — Elemental",
    "3/4",
    "Flying",
    "When this creature enters, scry 2.",
  ]

def nimrodelWatcher : CardDef :=
  fromOracle [
    "Nimrodel Watcher",
    "{1}{U}",
    "Creature — Elf Scout",
    "2/1",
    "Whenever you scry, this creature gets +1/+0 until end of turn and can't be blocked this turn. This ability triggers only once each turn.",
  ]

def sternScolding : CardDef :=
  fromOracle [
    "Stern Scolding",
    "{U}",
    "Instant",
    "Counter target creature spell with power or toughness 2 or less.",
  ]

def hauntOfTheDeadMarshes : CardDef :=
  fromOracle [
    "Haunt of the Dead Marshes",
    "{B}",
    "Creature — Nightmare Elf",
    "1/1",
    "When this creature enters, scry 1.",
    "{2}{B}: Return this card from your graveyard to the battlefield tapped. Activate only if you control a legendary creature.",
  ]

def languish : CardDef :=
  fromOracle [
    "Languish",
    "{2}{B}{B}",
    "Sorcery",
    "All creatures get -4/-4 until end of turn.",
  ]

def shadowOfTheEnemy : CardDef :=
  fromOracle [
    "Shadow of the Enemy",
    "{3}{B}{B}{B}",
    "Sorcery",
    "Exile all creature cards from target player's graveyard. You may cast spells from among those cards for as long as they remain exiled, and mana of any type can be spent to cast them.",
  ]

def trollOfKhazadDum : CardDef :=
  fromOracle [
    "Troll of Khazad-dûm",
    "{5}{B}",
    "Creature — Troll",
    "6/5",
    "This creature can't be blocked except by three or more creatures.",
    "Swampcycling {1} ({1}, Discard this card: Search your library for a Swamp card, reveal it, put it into your hand, then shuffle.)",
  ]

def mercilessExecutioner : CardDef :=
  fromOracle [
    "Merciless Executioner",
    "{2}{B}",
    "Creature — Orc Warrior",
    "3/1",
    "When this creature enters, each player sacrifices a creature of their choice.",
  ]

def bitterDownfall : CardDef :=
  fromOracle [
    "Bitter Downfall",
    "{3}{B}",
    "Instant",
    "This spell costs {3} less to cast if it targets a creature that was dealt damage this turn.",
    "Destroy target creature. Its controller loses 2 life.",
  ]

def nightsWhisper : CardDef :=
  fromOracle [
    "Night's Whisper",
    "{1}{B}",
    "Sorcery",
    "You draw two cards and lose 2 life.",
  ]

def wayfarersBauble : CardDef :=
  fromOracle [
    "Wayfarer's Bauble",
    "{1}",
    "Artifact",
    "{2}, {T}, Sacrifice this artifact: Search your library for a basic land card, put that card onto the battlefield tapped, then shuffle.",
  ]

def battleScarredGoblin : CardDef :=
  fromOracle [
    "Battle-Scarred Goblin",
    "{1}{R}",
    "Creature — Goblin Warrior",
    "2/2",
    "Whenever this creature becomes blocked, it deals 1 damage to each creature blocking it.",
  ]

def improvisedClub : CardDef :=
  fromOracle [
    "Improvised Club",
    "{1}{R}",
    "Instant",
    "As an additional cost to cast this spell, sacrifice an artifact or creature.",
    "Improvised Club deals 4 damage to any target.",
  ]

def ologHaiCrusher : CardDef :=
  fromOracle [
    "Olog-hai Crusher",
    "{3}{R}",
    "Creature — Troll Soldier",
    "4/4",
    "Trample",
    "This creature can't block unless you control a Goblin or Orc.",
  ]

def smiteTheDeathless : CardDef :=
  fromOracle [
    "Smite the Deathless",
    "{1}{R}",
    "Instant",
    "Smite the Deathless deals 3 damage to target creature. That creature loses indestructible until end of turn. If that creature would die this turn, exile it instead.",
  ]

def goblinFireleaper : CardDef :=
  fromOracle [
    "Goblin Fireleaper",
    "{1}{R}",
    "Creature — Goblin Warrior",
    "1/1",
    "{1}{R}: This creature gets +1/+0 until end of turn.",
    "When this creature dies, it deals damage equal to its power to target creature an opponent controls.",
  ]

def oliphaunt : CardDef :=
  fromOracle [
    "Oliphaunt",
    "{5}{R}",
    "Creature — Elephant",
    "6/4",
    "Trample",
    "Whenever this creature attacks, another target creature you control gets +2/+0 and gains trample until end of turn.",
    "Mountaincycling {1} ({1}, Discard this card: Search your library for a Mountain card, reveal it, put it into your hand, then shuffle.)",
  ]

def goblinCratermaker : CardDef :=
  fromOracle [
    "Goblin Cratermaker",
    "{1}{R}",
    "Creature — Goblin Warrior",
    "2/2",
    "{1}, Sacrifice this creature: Choose one —",
    "• This creature deals 2 damage to target creature.",
    "• Destroy target colorless nonland permanent.",
  ]

def infernoTitan : CardDef :=
  fromOracle [
    "Inferno Titan",
    "{4}{R}{R}",
    "Creature — Giant",
    "6/6",
    "{R}: This creature gets +1/+0 until end of turn.",
    "Whenever this creature enters or attacks, it deals 3 damage divided as you choose among one, two, or three targets.",
  ]

def guttersnipe : CardDef :=
  fromOracle [
    "Guttersnipe",
    "{2}{R}",
    "Creature — Goblin Shaman",
    "2/2",
    "Whenever you cast an instant or sorcery spell, this creature deals 2 damage to each opponent.",
  ]

def orcishSiegemaster : CardDef :=
  fromOracle [
    "Orcish Siegemaster",
    "{2}{R}",
    "Creature — Orc Soldier",
    "0/5",
    "Trample",
    "Other Orcs and Goblins you control have trample.",
    "Whenever this creature attacks, it gets +X/+0 until end of turn, where X is the greatest power among creatures you control.",
  ]

def fireOfOrthanc : CardDef :=
  fromOracle [
    "Fire of Orthanc",
    "{3}{R}",
    "Sorcery",
    "Destroy target artifact or land. Creatures without flying can't block this turn.",
  ]

def galadhrimGuide : CardDef :=
  fromOracle [
    "Galadhrim Guide",
    "{3}{G}",
    "Creature — Elf Scout",
    "3/4",
    "When this creature enters, scry 2.",
  ]

def elvishVisionary : CardDef :=
  fromOracle [
    "Elvish Visionary",
    "{1}{G}",
    "Creature — Elf Shaman",
    "1/1",
    "When this creature enters, draw a card.",
  ]

def mirkwoodElk : CardDef :=
  fromOracle [
    "Mirkwood Elk",
    "{5}{G}",
    "Creature — Elk",
    "6/6",
    "Trample",
    "Whenever this creature enters or attacks, return target Elf card from your graveyard to your hand. You gain life equal to that card's power.",
  ]

def celebornTheWise : CardDef :=
  fromOracle [
    "Celeborn the Wise",
    "{3}{G}",
    "Legendary Creature — Elf Noble",
    "3/3",
    "Whenever you attack with one or more Elves, scry 1.",
    "Whenever you scry, Celeborn gets +1/+1 until end of turn for each card looked at while scrying this way.",
  ]

def giftOfStrands : CardDef :=
  fromOracle [
    "Gift of Strands",
    "{3}{G}",
    "Enchantment — Aura",
    "Flash",
    "Enchant creature",
    "When this Aura enters, scry 2.",
    "Enchanted creature gets +3/+3.",
  ]

def elvishArchdruid : CardDef :=
  fromOracle [
    "Elvish Archdruid",
    "{1}{G}{G}",
    "Creature — Elf Druid",
    "2/2",
    "Other Elf creatures you control get +1/+1.",
    "{T}: Add {G} for each Elf you control.",
  ]

def lothlorienLookout : CardDef :=
  fromOracle [
    "Lothlórien Lookout",
    "{1}{G}",
    "Creature — Elf Scout",
    "1/3",
    "Whenever this creature attacks, scry 1.",
  ]

def elvishMystic : CardDef :=
  fromOracle [
    "Elvish Mystic",
    "{G}",
    "Creature — Elf Druid",
    "1/1",
    "{T}: Add {G}.",
  ]

def bardHeirOfGirion : CardDef :=
  fromOracle [
    "Bard, Heir of Girion",
    "{2}{W}{U}",
    "Legendary Creature — Human Archer",
    "4/4",
    "Reach, vigilance",
    "Other creatures you control get +1/+1.",
    "Whenever you attack, draw a card.",
  ]

def reprieve : CardDef :=
  fromOracle [
    "Reprieve",
    "{1}{W}",
    "Instant",
    "Return target spell to its owner's hand.",
    "Draw a card.",
  ]

def greatGoblinFoulHearted : CardDef :=
  fromOracle [
    "Great Goblin, Foul-Hearted",
    "{3}{B}{R}",
    "Legendary Creature — Goblin Noble",
    "3/3",
    "Whenever Great Goblin enters or attacks, amass Goblins 3. (Put three +1/+1 counters on an Army you control. It's also a Goblin. If you don't control an Army, create a 0/0 black Goblin Army creature token first.)",
    "Armies you control have trample.",
  ]

def dwarvenWarriors : CardDef :=
  fromOracle [
    "Dwarven Warriors",
    "{2}{R}",
    "Creature — Dwarf Warrior",
    "1/1",
    "{T}: Target creature with power 2 or less can't be blocked this turn.",
  ]

def bagEndBanquet : CardDef :=
  fromOracle [
    "Bag End Banquet",
    "{6}",
    "Artifact",
    "When this artifact enters, create three Food tokens.",
    "{T}: Add {C} for each Food you control.",
  ]

def floweringOfTheWhiteTree : CardDef :=
  fromOracle [
    "Flowering of the White Tree",
    "{W}{W}",
    "Legendary Enchantment",
    "Legendary creatures you control get +2/+1 and have ward {1}.",
    "Nonlegendary creatures you control get +1/+1.",
  ]

def mithrilCoat : CardDef :=
  fromOracle [
    "Mithril Coat",
    "{3}",
    "Legendary Artifact — Equipment",
    "Flash",
    "Indestructible",
    "When Mithril Coat enters, attach it to target legendary creature you control.",
    "Equipped creature has indestructible.",
    "Equip {3}",
  ]

def rivendell : CardDef :=
  fromOracle [
    "Rivendell",
    "Legendary Land",
    "Rivendell enters tapped unless you control a legendary creature.",
    "{T}: Add {U}.",
    "{1}{U}, {T}: Scry 2. Activate only if you control a legendary creature.",
  ]

def delightedHalfling : CardDef :=
  fromOracle [
    "Delighted Halfling",
    "{G}",
    "Creature — Halfling Citizen",
    "1/2",
    "{T}: Add {C}.",
    "{T}: Add one mana of any color. Spend this mana only to cast a legendary spell, and that spell can't be countered.",
  ]

def relicOfSauron : CardDef :=
  fromOracle [
    "Relic of Sauron",
    "{4}",
    "Artifact",
    "{T}: Add two mana in any combination of {U}, {B}, and/or {R}.",
    "{3}, {T}: Draw two cards, then discard a card.",
  ]

def longLostLances : CardDef :=
  fromOracle [
    "Long-Lost Lances",
    "{2}",
    "Artifact — Equipment",
    "Equipped creature gets +2/+0.",
    "During your turn, creatures you control that are equipped have first strike and vigilance.",
    "Equip {2}",
  ]

def lothoCorruptShirriff : CardDef :=
  fromOracle [
    "Lotho, Corrupt Shirriff",
    "{W}{B}",
    "Legendary Creature — Halfling Rogue",
    "2/1",
    "Whenever a player casts their second spell each turn, you lose 1 life and create a Treasure token. (It's an artifact with \"{T}, Sacrifice this token: Add one mana of any color.\")",
  ]

def flameOfAnor : CardDef :=
  fromOracle [
    "Flame of Anor",
    "{1}{U}{R}",
    "Instant",
    "Choose one. If you control a Wizard as you cast this spell, you may choose two instead.",
    "• Target player draws two cards.",
    "• Destroy target artifact.",
    "• Flame of Anor deals 5 damage to target creature.",
  ]

def lastMarchOfTheEnts : CardDef :=
  fromOracle [
    "Last March of the Ents",
    "{6}{G}{G}",
    "Sorcery",
    "This spell can't be countered.",
    "Draw cards equal to the greatest toughness among creatures you control, then put any number of creature cards from your hand onto the battlefield.",
  ]

def raiseThePalisade : CardDef :=
  fromOracle [
    "Raise the Palisade",
    "{4}{U}",
    "Sorcery",
    "Choose a creature type. Return all creatures that aren't of the chosen type to their owners' hands.",
  ]

def dragonsDesire : CardDef :=
  fromOracle [
    "Dragon's Desire",
    "{2}{R}{R}",
    "Sorcery",
    "Add {R} for each artifact your opponents control.",
  ]

def oriPlateStacker : CardDef :=
  fromOracle [
    "Ori, Plate Stacker",
    "{5}{W}{W}",
    "Legendary Creature — Dwarf Bard",
    "3/3",
    "When Ori enters, destroy all artifacts and enchantments your opponents control. You gain 1 life for each permanent destroyed this way.",
  ]

def dainOfTheAncientHalls : CardDef :=
  fromOracle [
    "Dáin of the Ancient Halls",
    "{3}{R}{W}",
    "Legendary Creature — Dwarf Noble",
    "4/5",
    "Vigilance, haste",
    "Whenever Dáin attacks, he deals damage equal to the number of Dwarves you control to each opponent.",
  ]

def treasureVault : CardDef :=
  fromOracle [
    "Treasure Vault",
    "Artifact Land",
    "{T}: Add {C}.",
    "{X}{X}, {T}, Sacrifice this land: Create X Treasure tokens.",
  ]

def aragornAndArwenWed : CardDef :=
  fromOracle [
    "Aragorn and Arwen, Wed",
    "{4}{G}{W}",
    "Legendary Creature — Human Elf Noble",
    "3/6",
    "Vigilance",
    "Whenever Aragorn and Arwen enters or attacks, put a +1/+1 counter on each other creature you control. You gain 1 life for each other creature you control.",
  ]

def minasTirith : CardDef :=
  fromOracle [
    "Minas Tirith",
    "Legendary Land",
    "Minas Tirith enters tapped unless you control a legendary creature.",
    "{T}: Add {W}.",
    "{1}{W}, {T}: Draw a card. Activate only if you attacked with two or more creatures this turn.",
  ]

def theShire : CardDef :=
  fromOracle [
    "The Shire",
    "Legendary Land",
    "The Shire enters tapped unless you control a legendary creature.",
    "{T}: Add {G}.",
    "{1}{G}, {T}, Tap an untapped creature you control: Create a Food token.",
  ]

def thranduilTheStrategist : CardDef :=
  fromOracle [
    "Thranduil the Strategist",
    "{3}{G}{U}",
    "Legendary Creature — Elf Noble",
    "4/4",
    "Other Elves you control have \"{T}: Add {G} or {U}.\"",
    "Landfall — Whenever a land you control enters, create a 1/1 green Elf creature token.",
  ]

def moxAmber : CardDef :=
  fromOracle [
    "Mox Amber",
    "{0}",
    "Legendary Artifact",
    "{T}: Add one mana of any color among legendary creatures and planeswalkers you control.",
  ]

def filiAndKiliJoyous : CardDef :=
  fromOracle [
    "Fíli and Kíli, Joyous",
    "{2}{R}",
    "Legendary Creature — Dwarf Bard",
    "3/3",
    "Haste",
    "{T}: Add {R}{R}. Spend this mana only to cast Dwarf, Equipment, and Saga spells.",
  ]

def arcaneSignet : CardDef :=
  fromOracle [
    "Arcane Signet",
    "{2}",
    "Artifact",
    "{T}: Add one mana of any color in your commander's color identity.",
  ]

def theGaffer : CardDef :=
  fromOracle [
    "The Gaffer",
    "{2}{W}",
    "Legendary Creature — Halfling Peasant",
    "2/3",
    "At the beginning of each end step, if you gained 3 or more life this turn, draw a card.",
  ]

def witchKingBringerOfRuin : CardDef :=
  fromOracle [
    "Witch-king, Bringer of Ruin",
    "{4}{B}{B}",
    "Legendary Creature — Wraith Noble",
    "5/3",
    "Flying",
    "Whenever Witch-king attacks, defending player sacrifices a creature with the least power among creatures they control.",
  ]

def necklaceOfGirion : CardDef :=
  fromOracle [
    "Necklace of Girion",
    "{2}{G}",
    "Legendary Artifact",
    "Whenever you cast a green spell and whenever a Forest you control enters, put a +1/+1 counter on target creature you control.",
    "{T}: Add {G}.",
  ]

def sauronTheLidlessEye : CardDef :=
  fromOracle [
    "Sauron, the Lidless Eye",
    "{3}{B}{R}",
    "Legendary Creature — Avatar Horror",
    "4/4",
    "When Sauron enters, gain control of target creature an opponent controls until end of turn. Untap it. It gains haste until end of turn.",
    "{1}{B}{R}: Creatures you control get +2/+0 until end of turn. Each opponent loses 2 life.",
  ]

def bolgEreborsReckoning : CardDef :=
  fromOracle [
    "Bolg, Erebor's Reckoning",
    "{4}{B}{R}",
    "Legendary Creature — Goblin Soldier",
    "6/6",
    "Trample",
    "At the beginning of each combat, other Goblins and Orcs you control get +2/+2 until end of turn. Creatures your opponents control get -1/-1 until end of turn.",
  ]

def thorinKingOfDurinsFolk : CardDef :=
  fromOracle [
    "Thorin, King of Durin's Folk",
    "{3}{R}{W}",
    "Legendary Creature — Dwarf Noble",
    "4/4",
    "Whenever Thorin or another Dwarf you control enters, create a Treasure token.",
    "Other Dwarves you control get +1/+0 for each artifact token you control.",
  ]

def bilboUnexpectedAdventurer : CardDef :=
  fromOracle [
    "Bilbo, Unexpected Adventurer",
    "{3}{W}",
    "Legendary Creature — Halfling Rogue",
    "2/2",
    "Bilbo can't be blocked by creatures with power 3 or greater.",
    "Whenever Bilbo deals combat damage to a player or battle, put up to one target nonland permanent card with mana value 3 or less from a graveyard onto the battlefield under its owner's control.",
  ]

def andurilFlameOfTheWest : CardDef :=
  fromOracle [
    "Andúril, Flame of the West",
    "{3}",
    "Legendary Artifact — Equipment",
    "Equipped creature gets +3/+1.",
    "Whenever equipped creature attacks, create two tapped 1/1 white Spirit creature tokens with flying. If that creature is legendary, instead create two of those tokens that are tapped and attacking.",
    "Equip {2}",
  ]

def andurilNarsilReforged : CardDef :=
  fromOracle [
    "Andúril, Narsil Reforged",
    "{2}",
    "Legendary Artifact — Equipment",
    "Ascend (If you control ten or more permanents, you get the city's blessing for the rest of the game.)",
    "Whenever equipped creature attacks, put a +1/+1 counter on each creature you control. If you have the city's blessing, put two +1/+1 counters on each creature you control instead.",
    "Equip {3}",
  ]

def aragornTheUniter : CardDef :=
  fromOracle [
    "Aragorn, the Uniter",
    "{R}{G}{W}{U}",
    "Legendary Creature — Human Noble",
    "5/5",
    "Whenever you cast a white spell, create a 1/1 white Human Soldier creature token.",
    "Whenever you cast a blue spell, scry 2.",
    "Whenever you cast a red spell, Aragorn deals 3 damage to target opponent.",
    "Whenever you cast a green spell, target creature gets +4/+4 until end of turn.",
  ]

def arwenMortalQueen : CardDef :=
  fromOracle [
    "Arwen, Mortal Queen",
    "{1}{G}{W}",
    "Legendary Creature — Elf Noble",
    "2/2",
    "Arwen enters with an indestructible counter on her.",
    "{1}, Remove an indestructible counter from Arwen: Another target creature gains indestructible until end of turn. Put a +1/+1 counter and a lifelink counter on that creature and a +1/+1 counter and a lifelink counter on Arwen.",
  ]

def arwenWeaverOfHope : CardDef :=
  fromOracle [
    "Arwen, Weaver of Hope",
    "{1}{G}{G}",
    "Legendary Creature — Elf Noble",
    "2/1",
    "Each other creature you control enters with a number of additional +1/+1 counters on it equal to Arwen's toughness.",
  ]

def bilboSBurglaring : CardDef :=
  fromOracle [
    "Bilbo's Burglaring",
    "{4}{U}{U}",
    "Sorcery",
    "For each opponent, gain control of up to one target artifact that player controls.",
  ]

def bilboSRing : CardDef :=
  fromOracle [
    "Bilbo's Ring",
    "{3}",
    "Legendary Artifact — Equipment",
    "During your turn, equipped creature has hexproof and can't be blocked.",
    "Whenever equipped creature attacks alone, you draw a card and you lose 1 life.",
    "Equip Halfling {1} ({1}: Attach to target Halfling you control. Equip only as a sorcery.)",
    "Equip {4} ({4}: Attach to target creature you control. Equip only as a sorcery.)",
  ]

def bilboFellowConspirator : CardDef :=
  fromOracle [
    "Bilbo, Fellow Conspirator",
    "{2}{G}",
    "Legendary Creature — Halfling Citizen",
    "2/3",
    "If you would create a Food token, instead create a Food token and a Treasure token.",
  ]

def callForthTheTempest : CardDef :=
  fromOracle [
    "Call Forth the Tempest",
    "{5}{R}{R}{R}",
    "Sorcery",
    "Cascade, cascade (When you cast this spell, exile cards from the top of your library until you exile a nonland card that costs less. You may cast it without paying its mana cost. Put the exiled cards on the bottom of your library in a random order. Then do it again.)",
    "Call Forth the Tempest deals damage to each creature your opponents control equal to the total mana value of other spells you've cast this turn.",
  ]

def cavernHoardDragon : CardDef :=
  fromOracle [
    "Cavern-Hoard Dragon",
    "{7}{R}{R}",
    "Creature — Dragon",
    "6/6",
    "This spell costs {X} less to cast, where X is the greatest number of artifacts an opponent controls.",
    "Flying, trample, haste",
    "Whenever this creature deals combat damage to a player, you create a Treasure token for each artifact that player controls.",
  ]

def chiefOfTheWilds : CardDef :=
  fromOracle [
    "Chief of the Wilds",
    "{2}{B}{G}",
    "Legendary Creature — Wolf",
    "4/4",
    "Menace",
    "Whenever another Wolf you control enters, put two +1/+1 counters on Chief of the Wilds.",
    "If a triggered ability of another Wolf or battle you control triggers, that ability triggers an additional time.",
  ]

def dragonCursedHalls : CardDef :=
  fromOracle [
    "Dragon-Cursed Halls",
    "Land",
    "{T}: Add {C}.",
    "{1}, {T}: Until end of turn, target creature gains \"Whenever this creature deals combat damage to a player, create a Treasure token.\"",
  ]

def elvenChorus : CardDef :=
  fromOracle [
    "Elven Chorus",
    "{3}{G}",
    "Enchantment",
    "You may look at the top card of your library any time.",
    "You may cast creature spells from the top of your library.",
    "Creatures you control have \"{T}: Add one mana of any color.\"",
  ]

def galadrielSDismissal : CardDef :=
  fromOracle [
    "Galadriel's Dismissal",
    "{W}",
    "Instant",
    "Kicker {2}{W} (You may pay an additional {2}{W} as you cast this spell.)",
    "Target creature phases out. If this spell was kicked, each creature target player controls phases out instead. (Treat phased-out creatures and anything attached to them as though they don't exist until their controller's next turn.)",
  ]

def galadrielLightOfValinor : CardDef :=
  fromOracle [
    "Galadriel, Light of Valinor",
    "{2}{G}{W}{U}",
    "Legendary Creature — Elf Noble",
    "3/3",
    "Alliance — Whenever another creature you control enters, choose one that hasn't been chosen this turn —",
    "• Add {G}{G}{G}.",
    "• Put a +1/+1 counter on each creature you control.",
    "• Scry 2, then draw a card.",
  ]

def gandalfPartyGuest : CardDef :=
  fromOracle [
    "Gandalf, Party Guest",
    "{1}{U}{R}{W}",
    "Legendary Creature — Avatar Wizard",
    "3/4",
    "At the beginning of combat on your turn, you may cast an instant or sorcery spell with mana value X or less from your hand without paying its mana cost, where X is twice the number of legendary Wizards you control.",
  ]

def gandalfShadowSFoe : CardDef :=
  fromOracle [
    "Gandalf, Shadow's Foe",
    "{5}{U}{U}",
    "Legendary Creature — Avatar Wizard",
    "3/4",
    "Vigilance",
    "When Gandalf enters, exile up to three target lands you control, then return them to the battlefield tapped under their owner's control.",
    "Landfall — Whenever a land you control enters, draw a card and put a +1/+1 counter on Gandalf.",
  ]

def glamdring : CardDef :=
  fromOracle [
    "Glamdring",
    "{2}",
    "Legendary Artifact — Equipment",
    "Equipped creature has first strike and gets +1/+0 for each instant and sorcery card in your graveyard.",
    "Whenever equipped creature deals combat damage to a player, you may cast an instant or sorcery spell from your hand with mana value less than or equal to that damage without paying its mana cost.",
    "Equip {3}",
  ]

def grimaSarumanSFootman : CardDef :=
  fromOracle [
    "Gríma, Saruman's Footman",
    "{2}{U}{B}",
    "Legendary Creature — Human Advisor",
    "1/4",
    "Gríma can't be blocked.",
    "Whenever Gríma deals combat damage to a player, that player exiles cards from the top of their library until they exile an instant or sorcery card. You may cast that card without paying its mana cost. Then that player puts the exiled cards that weren't cast this way on the bottom of their library in a random order.",
  ]

def minasMorgulDarkFortress : CardDef :=
  fromOracle [
    "Minas Morgul, Dark Fortress",
    "Legendary Land",
    "Minas Morgul enters tapped.",
    "{T}: Add {B}.",
    "{3}{B}, {T}: Put a shadow counter on target creature. For as long as that creature has a shadow counter on it, it's a Wraith in addition to its other types. (A creature with shadow can block or be blocked by only creatures with shadow.)",
  ]

def mountDoom : CardDef :=
  fromOracle [
    "Mount Doom",
    "Legendary Land",
    "{T}, Pay 1 life: Add {B} or {R}.",
    "{1}{B}{R}, {T}: Mount Doom deals 1 damage to each opponent.",
    "{5}{B}{R}, {T}, Sacrifice Mount Doom and a legendary artifact: Choose up to two creatures, then destroy the rest. Activate only as a sorcery.",
  ]

def orcishBowmasters : CardDef :=
  fromOracle [
    "Orcish Bowmasters",
    "{1}{B}",
    "Creature — Orc Archer",
    "1/1",
    "Flash",
    "When this creature enters and whenever an opponent draws a card except the first one they draw in each of their draw steps, this creature deals 1 damage to any target. Then amass Orcs 1.",
  ]

def palantirOfOrthanc : CardDef :=
  fromOracle [
    "Palantír of Orthanc",
    "{3}",
    "Legendary Artifact",
    "At the beginning of your end step, put an influence counter on Palantír of Orthanc and scry 2. Then target opponent may have you draw a card. If that player doesn't, you mill X cards, where X is the number of influence counters on Palantír of Orthanc, and that player loses life equal to the total mana value of those cards.",
  ]

def sarumanOfManyColors : CardDef :=
  fromOracle [
    "Saruman of Many Colors",
    "{3}{W}{U}{B}",
    "Legendary Creature — Avatar Wizard",
    "5/4",
    "Ward—Discard an enchantment, instant, or sorcery card.",
    "Whenever you cast your second spell each turn, each opponent mills two cards. When one or more cards are milled this way, exile target enchantment, instant, or sorcery card with equal or lesser mana value than that spell from an opponent's graveyard. Copy the exiled card. You may cast the copy without paying its mana cost.",
  ]

def sauronTheDarkLord : CardDef :=
  fromOracle [
    "Sauron, the Dark Lord",
    "{3}{U}{B}{R}",
    "Legendary Creature — Avatar Horror",
    "7/6",
    "Ward—Sacrifice a legendary artifact or legendary creature.",
    "Whenever an opponent casts a spell, amass Orcs 1.",
    "Whenever an Army you control deals combat damage to a player, the Ring tempts you.",
    "Whenever the Ring tempts you, you may discard your hand. If you do, draw four cards.",
  ]

def smaugTheImpenetrable : CardDef :=
  fromOracle [
    "Smaug the Impenetrable",
    "{5}{B}{R}",
    "Legendary Creature — Dragon",
    "8/7",
    "Flying, indestructible, haste",
    "Whenever Smaug is dealt noncombat damage, create that many Treasure tokens.",
  ]

def theBlackGate : CardDef :=
  fromOracle [
    "The Black Gate",
    "Legendary Land — Gate",
    "As The Black Gate enters, you may pay 3 life. If you don't, it enters tapped.",
    "{T}: Add {B}.",
    "{1}{B}, {T}: Choose a player with the most life or tied for most life. Target creature can't be blocked by creatures that player controls this turn.",
  ]

def theOneRing : CardDef :=
  fromOracle [
    "The One Ring",
    "{4}",
    "Legendary Artifact",
    "Indestructible",
    "When The One Ring enters, if you cast it, you gain protection from everything until your next turn.",
    "At the beginning of your upkeep, you lose 1 life for each burden counter on The One Ring.",
    "{T}: Put a burden counter on The One Ring, then draw a card for each burden counter on The One Ring.",
  ]

def theReaverCleaver : CardDef :=
  fromOracle [
    "The Reaver Cleaver",
    "{2}{R}",
    "Legendary Artifact — Equipment",
    "Equipped creature gets +1/+1 and has trample and \"Whenever this creature deals combat damage to a player or planeswalker, create that many Treasure tokens.\"",
    "Equip {3}",
  ]

def thorinCompanySLeader : CardDef :=
  fromOracle [
    "Thorin, Company's Leader",
    "{4}{R}",
    "Legendary Creature — Dwarf Warrior",
    "4/5",
    "Whenever a Dwarf you control deals combat damage to a player or battle, create two Treasure tokens. (They're artifacts with \"{T}, Sacrifice this token: Add one mana of any color.\")",
    "{10}: Creatures you control gain double strike until end of turn.",
  ]

def tomBombadil : CardDef :=
  fromOracle [
    "Tom Bombadil",
    "{W}{U}{B}{R}{G}",
    "Legendary Creature — God Bard",
    "4/4",
    "As long as there are four or more lore counters among Sagas you control, Tom Bombadil has hexproof and indestructible.",
    "Whenever the final chapter ability of a Saga you control resolves, reveal cards from the top of your library until you reveal a Saga card. Put that card onto the battlefield and the rest on the bottom of your library in a random order. This ability triggers only once each turn.",
  ]

def witchKingOfAngmar : CardDef :=
  fromOracle [
    "Witch-king of Angmar",
    "{3}{B}{B}",
    "Legendary Creature — Wraith Noble",
    "5/3",
    "Flying",
    "Whenever one or more creatures deal combat damage to you, each opponent sacrifices a creature of their choice that dealt combat damage to you this turn. The Ring tempts you.",
    "Discard a card: Witch-king of Angmar gains indestructible until end of turn. Tap him.",
  ]

/-- Every unique card in The Hobbit Eternal (HOC), including reprints
that also appear in other sets. -/
@[irreducible, noinline] def hobbitEternalCards : Array CardDef := #[
  mentorOfTheMeek,
  fiendHunter,
  errandRiderOfGondor,
  landrovalHorizonWitness,
  roguesPassage,
  soldierOfTheGreyHost,
  eaglesOfTheNorth,
  dunedainBlade,
  fogOnTheBarrowDowns,
  banishingLight,
  dawnOfANewAge,
  westfoldRider,
  esquireOfTheKing,
  pelargirSurvivor,
  lorienRevealed,
  knightsOfDolAmroth,
  greyHavensNavigator,
  ithilienKingfisher,
  hithlainKnots,
  captainOfUmbar,
  minasTirithGarrison,
  colossalWhale,
  willowWind,
  nimrodelWatcher,
  sternScolding,
  hauntOfTheDeadMarshes,
  languish,
  shadowOfTheEnemy,
  trollOfKhazadDum,
  mercilessExecutioner,
  bitterDownfall,
  nightsWhisper,
  wayfarersBauble,
  battleScarredGoblin,
  improvisedClub,
  ologHaiCrusher,
  smiteTheDeathless,
  goblinFireleaper,
  oliphaunt,
  goblinCratermaker,
  infernoTitan,
  guttersnipe,
  orcishSiegemaster,
  fireOfOrthanc,
  galadhrimGuide,
  elvishVisionary,
  mirkwoodElk,
  celebornTheWise,
  giftOfStrands,
  elvishArchdruid,
  lothlorienLookout,
  elvishMystic,
  bardHeirOfGirion,
  reprieve,
  greatGoblinFoulHearted,
  dwarvenWarriors,
  bagEndBanquet,
  floweringOfTheWhiteTree,
  mithrilCoat,
  rivendell,
  delightedHalfling,
  relicOfSauron,
  longLostLances,
  lothoCorruptShirriff,
  flameOfAnor,
  lastMarchOfTheEnts,
  raiseThePalisade,
  dragonsDesire,
  oriPlateStacker,
  dainOfTheAncientHalls,
  treasureVault,
  aragornAndArwenWed,
  minasTirith,
  theShire,
  thranduilTheStrategist,
  moxAmber,
  filiAndKiliJoyous,
  arcaneSignet,
  theGaffer,
  witchKingBringerOfRuin,
  necklaceOfGirion,
  sauronTheLidlessEye,
  bolgEreborsReckoning,
  thorinKingOfDurinsFolk,
  bilboUnexpectedAdventurer,
  andurilFlameOfTheWest,
  andurilNarsilReforged,
  aragornTheUniter,
  arwenMortalQueen,
  arwenWeaverOfHope,
  bilboSBurglaring,
  bilboSRing,
  bilboFellowConspirator,
  callForthTheTempest,
  cavernHoardDragon,
  chiefOfTheWilds,
  dragonCursedHalls,
  elvenChorus,
  galadrielSDismissal,
  galadrielLightOfValinor,
  gandalfPartyGuest,
  gandalfShadowSFoe,
  glamdring,
  grimaSarumanSFootman,
  minasMorgulDarkFortress,
  mountDoom,
  orcishBowmasters,
  palantirOfOrthanc,
  sarumanOfManyColors,
  sauronTheDarkLord,
  smaugTheImpenetrable,
  theBlackGate,
  theOneRing,
  theReaverCleaver,
  thorinCompanySLeader,
  tomBombadil,
  witchKingOfAngmar
]

#guard roguesPassage.isLand
#guard roguesPassage.activatedAbilities.size == 1
#guard roguesPassage.activatedAbilities[0]!.effect == Effect.targetCantBeBlockedThisTurn
#guard roguesPassage.activatedAbilities[0]!.cost.tap
#guard roguesPassage.activatedAbilities[0]!.cost.mana == (ManaCost.ofGeneric 4)
#guard roguesPassage.tapAddMana == #[.colorless]
#guard elvishMystic.tapAddMana == #[.colored .green]
#guard (wayfarersBauble.summary.splitOn "Search your library").length > 1
#guard (roguesPassage.summary.splitOn "can't be blocked").length > 1
#guard orcishSiegemaster.keywords.trample
#guard orcishSiegemaster.staticAbilities == #[.otherCreaturesHaveTrample #["Orc", "Goblin"]]
#guard orcishSiegemaster.triggeredAbilities == #[.onAttackPumpByGreatestPower]
#guard (orcishSiegemaster.summary.splitOn "Other Orcs and Goblins").length > 1
#guard battleScarredGoblin.triggeredAbilities == #[.onBecomesBlockedDeal1ToBlockers]
#guard (battleScarredGoblin.summary.splitOn "becomes blocked").length > 1
#guard giftOfStrands.isAura
#guard giftOfStrands.keywords.flash
#guard !giftOfStrands.hasSorcerySpeed
#guard giftOfStrands.hasInstantSpeed
#guard giftOfStrands.requiresTarget
#guard giftOfStrands.staticAbilities == #[.enchantedCreatureGets 3 3]
#guard giftOfStrands.triggeredAbilities == #[.onEnterScry 2]
#guard dunedainBlade.activatedAbilities.size == 2
#guard dunedainBlade.activatedAbilities[0]!.equipSubtype == some "Human"
#guard dunedainBlade.activatedAbilities[1]!.equipSubtype == none
#guard dunedainBlade.activatedAbilities[0]!.cost.mana == (ManaCost.ofGeneric 1)
#guard dunedainBlade.activatedAbilities[1]!.cost.mana == (ManaCost.ofGeneric 3)
#guard (giftOfStrands.summary.splitOn "flash").length > 1
#guard (giftOfStrands.summary.splitOn "Enchanted creature").length > 1
#guard galadhrimGuide.triggeredAbilities == #[.onEnterScry 2]
#guard (galadhrimGuide.summary.splitOn "scry 2").length > 1
#guard elvishVisionary.triggeredAbilities == #[.onEnterDraw 1]
#guard (elvishVisionary.summary.splitOn "draw a card").length > 1
#guard elvishArchdruid.staticAbilities == #[.otherCreaturesGet #["Elf"] 1 1]
#guard elvishArchdruid.tapAddManaForEach == #[{ mana := .colored .green, subtype := "Elf" }]
#guard elvishArchdruid.manaAbilities == #[.colored .green]
#guard (elvishArchdruid.summary.splitOn "Other Elf creatures").length > 1
#guard (elvishArchdruid.summary.splitOn "for each Elf").length > 1
#guard mirkwoodElk.keywords.trample
#guard mirkwoodElk.triggeredAbilities == #[.onEnterOrAttackReturnElfGainLife]
#guard mirkwoodElk.power == some 6
#guard mirkwoodElk.toughness == some 6
#guard (mirkwoodElk.summary.splitOn "trample").length > 1
#guard (mirkwoodElk.summary.splitOn "Elf card").length > 1
#guard celebornTheWise.triggeredAbilities ==
  #[.onAttackWithElvesScry 1, .onScryPumpSelfForEachLookedAt]
#guard celebornTheWise.power == some 3
#guard celebornTheWise.toughness == some 3
#guard celebornTheWise.subtypes.any (· == "Elf")
#guard (celebornTheWise.summary.splitOn "one or more Elves").length > 1
#guard (celebornTheWise.summary.splitOn "looked at").length > 1
#guard lothlorienLookout.triggeredAbilities == #[.onAttackScry 1]
#guard (lothlorienLookout.summary.splitOn "scry 1").length > 1
#guard lothlorienLookout.power == some 1
#guard lothlorienLookout.toughness == some 3
#guard galadhrimGuide.power == some 3
#guard galadhrimGuide.toughness == some 4
#guard goblinCratermaker.activatedAbilities.size == 1
#guard goblinCratermaker.activatedAbilities[0]!.cost.sacrificeSource
#guard goblinCratermaker.activatedAbilities[0]!.cost.mana == (ManaCost.ofGeneric 1)
#guard goblinCratermaker.activatedAbilities[0]!.isModal
#guard goblinCratermaker.activatedAbilities[0]!.effect == Effect.dealDamageToTargetCreature 2
#guard goblinCratermaker.activatedAbilities[0]!.otherModes ==
  #[Effect.destroyTargetColorlessNonland]
#guard (goblinCratermaker.summary.splitOn "Choose one").length > 1
#guard (goblinCratermaker.summary.splitOn "colorless nonland").length > 1
#guard smiteTheDeathless.isInstant
#guard smiteTheDeathless.requiresTarget
#guard smiteTheDeathless.spellEffect == some (Effect.dealDamageLoseIndestructibleExile 3)
#guard (Effect.dealDamageLoseIndestructibleExile 3).targetCount == 1
#guard (smiteTheDeathless.summary.splitOn "loses indestructible").length > 1
#guard (smiteTheDeathless.summary.splitOn "exile it instead").length > 1
#guard ologHaiCrusher.keywords.trample
#guard ologHaiCrusher.staticAbilities == #[.cantBlockUnlessYouControl #["Goblin", "Orc"]]
#guard (ologHaiCrusher.summary.splitOn "trample").length > 1
#guard (ologHaiCrusher.summary.splitOn "can't block unless").length > 1
#guard oliphaunt.keywords.trample
#guard oliphaunt.triggeredAbilities == #[.onAttackOtherGets2AndTrample]
#guard oliphaunt.activatedAbilities.size == 1
#guard oliphaunt.activatedAbilities[0]!.activateFromHand
#guard oliphaunt.activatedAbilities[0]!.cost.discardSource
#guard oliphaunt.activatedAbilities[0]!.effect == Effect.searchLandTypeToHand "Mountain"
#guard oliphaunt.activatedAbilities[0]!.cost.mana == (ManaCost.ofGeneric 1)
#guard oliphaunt.power == some 6
#guard oliphaunt.toughness == some 4
#guard (oliphaunt.summary.splitOn "trample").length > 1
#guard (oliphaunt.summary.splitOn "+2/+0").length > 1
#guard (oliphaunt.summary.splitOn "Mountaincycling").length > 1
#guard goblinFireleaper.activatedAbilities.size == 1
#guard goblinFireleaper.activatedAbilities[0]!.effect == Effect.sourceGets 1 0
#guard goblinFireleaper.activatedAbilities[0]!.cost.mana == (ManaCost.ofGenericAndColor 1 .red)
#guard goblinFireleaper.triggeredAbilities == #[.onDiesDealDamageEqualToPowerToOppCreature]
#guard (goblinFireleaper.summary.splitOn "+1/+0").length > 1
#guard (goblinFireleaper.summary.splitOn "dies").length > 1
#guard infernoTitan.activatedAbilities.size == 1
#guard infernoTitan.activatedAbilities[0]!.effect == Effect.sourceGets 1 0
#guard infernoTitan.activatedAbilities[0]!.cost.mana == (ManaCost.ofColor .red)
#guard infernoTitan.triggeredAbilities == #[.onEnterOrAttackDealDividedDamage 3 3]
#guard infernoTitan.power == some 6
#guard infernoTitan.toughness == some 6
#guard (infernoTitan.summary.splitOn "+1/+0").length > 1
#guard (infernoTitan.summary.splitOn "divided as you choose").length > 1
#guard guttersnipe.triggeredAbilities == #[.onCastInstantOrSorceryDealDamageToEachOpponent 2]
#guard guttersnipe.power == some 2
#guard guttersnipe.toughness == some 2
#guard (guttersnipe.summary.splitOn "instant or sorcery").length > 1
#guard hauntOfTheDeadMarshes.triggeredAbilities == #[.onEnterScry 1]
#guard hauntOfTheDeadMarshes.activatedAbilities.size == 1
#guard hauntOfTheDeadMarshes.activatedAbilities[0]!.activateFromGraveyard
#guard hauntOfTheDeadMarshes.activatedAbilities[0]!.onlyIfYouControlLegendary
#guard hauntOfTheDeadMarshes.activatedAbilities[0]!.effect == Effect.returnFromGraveyardTapped
#guard languish.spellEffect == some (Effect.allCreaturesGet (-4) (-4))
#guard !languish.requiresTarget
#guard shadowOfTheEnemy.spellEffect == some (Effect.exileGraveyardCreaturesGrantCast)
#guard shadowOfTheEnemy.requiresTarget
#guard trollOfKhazadDum.staticAbilities == #[.cantBeBlockedExceptBy 3]
#guard (trollOfKhazadDum.summary.splitOn "three or more").length > 1
#guard trollOfKhazadDum.activatedAbilities.size == 1
#guard trollOfKhazadDum.activatedAbilities[0]!.activateFromHand
#guard trollOfKhazadDum.activatedAbilities[0]!.cost.discardSource
#guard trollOfKhazadDum.activatedAbilities[0]!.effect == Effect.searchLandTypeToHand "Swamp"
#guard trollOfKhazadDum.activatedAbilities[0]!.cost.mana == (ManaCost.ofGeneric 1)
#guard mercilessExecutioner.triggeredAbilities == #[.onEnterEachPlayerSacrificesCreature]
#guard bitterDownfall.spellEffect == some (Effect.destroyTargetCreatureControllerLosesLife 2)
#guard bitterDownfall.costReductionIfTargetDamaged == 3
#guard improvisedClub.isInstant
#guard improvisedClub.spellEffect == some (Effect.dealDamage 4)
#guard improvisedClub.additionalCostSacrificeArtifactOrCreature
#guard improvisedClub.requiresTarget
#guard (improvisedClub.summary.splitOn "additional cost").length > 1
#guard (improvisedClub.summary.splitOn "4 damage").length > 1
#guard fireOfOrthanc.isSorcery
#guard fireOfOrthanc.spellEffect == some (Effect.destroyArtifactOrLandNonflyersCantBlock)
#guard fireOfOrthanc.requiresTarget
#guard (fireOfOrthanc.summary.splitOn "artifact or land").length > 1
#guard (fireOfOrthanc.summary.splitOn "can't block this turn").length > 1
#guard nightsWhisper.isSorcery
#guard nightsWhisper.spellEffect == some (Effect.drawAndLoseLife 2 2)
#guard !nightsWhisper.requiresTarget
#guard nightsWhisper.hasCastKind .draw
#guard (nightsWhisper.summary.splitOn "draw 2 cards").length > 1
#guard (nightsWhisper.summary.splitOn "lose 2 life").length > 1
#guard theOneRing.activatedAbilities[0]!.effect == Effect.burdenThenDraw
#guard theOneRing.triggeredAbilities ==
  #[.onEnterIfCastProtectionEverything, .onYourUpkeepLoseLifePerBurden]
#guard palantirOfOrthanc.triggeredAbilities == #[.onYourEndStepPalantir]
#guard grimaSarumanSFootman.keywords.cantBeBlocked
#guard grimaSarumanSFootman.triggeredAbilities == #[.onCombatDamageImpulseInstantSorcery]
#guard arwenMortalQueen.entersWithIndestructibleCounter
#guard arwenMortalQueen.activatedAbilities[0]!.effect == Effect.arwenShare
#guard callForthTheTempest.spellEffect == some (Effect.damageOppCreaturesEqualOtherSpellsMv)
#guard galadrielSDismissal.spellEffect == some (Effect.phaseOutKicker)
#guard theReaverCleaver.staticAbilities == #[.equippedGetsTrampleAndCombatTreasures 1 1]
#guard mountDoom.activatedAbilities.size == 2
#guard mountDoom.activatedAbilities[1]!.cost.sacrificeLegendaryArtifact

end Mtg.Engine.Catalog
