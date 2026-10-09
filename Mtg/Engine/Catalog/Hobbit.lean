import Mtg.Engine.Card
import Mtg.Engine.Catalog

/-!
# The Hobbit catalog

Oracle characteristics for cards from Magic: The Gathering | The Hobbit
(HOB). Each card is defined by its full printed text.
`hobbitCards` lists every unique card in the set, including Journey basic
lands that are also in the core catalog.

Source: https://magic.wizards.com/en/news/announcements/the-hobbit-welcome-decks
-/

namespace Mtg.Engine.Catalog

open Mtg.Engine

def bofurReliableGuardian : CardDef :=
  fromOracle [
    "Bofur, Reliable Guardian",
    "{W}",
    "Legendary Creature — Dwarf Scout",
    "1/1",
    "Lifelink",
    "//ADV//",
    "Concerted Care",
    "{1}{W}",
    "Instant — Adventure",
    "Target artifact or creature you control gains hexproof and indestructible until end of turn. (Then exile this card. You may cast the creature later from exile.)",
  ]

def dwarvenProvisioner : CardDef :=
  fromOracle [
    "Dwarven Provisioner",
    "{1}{W}",
    "Creature — Dwarf Citizen",
    "2/2",
    "{3}{W}: Creatures you control get +1/+1 until end of turn.",
  ]

def velvetwingButterflies : CardDef :=
  fromOracle [
    "Velvetwing Butterflies",
    "{2}{W}",
    "Creature — Insect",
    "2/2",
    "Flying",
    "//ADV//",
    "Gaze in Wonder",
    "{1}{W}",
    "Instant — Adventure",
    "Tap one or two target creatures. (Then exile this card. You may cast the creature later from exile.)",
  ]

def magnificentEnd : CardDef :=
  fromOracle [
    "Magnificent End",
    "{4}{W}",
    "Instant",
    "This spell costs {3} less to cast if it targets a tapped creature.",
    "Magnificent End deals 5 damage to target creature.",
  ]

def eagleOfTheGreatShelf : CardDef :=
  fromOracle [
    "Eagle of the Great Shelf",
    "{4}{W}",
    "Creature — Bird Soldier",
    "2/5",
    "Flying",
    "Whenever this creature attacks, it gets +1/+1 until end of turn for each other creature you control.",
  ]

def vowToErebor : CardDef :=
  fromOracle [
    "Vow to Erebor",
    "{1}{W}",
    "Instant",
    "Untap target creature you control. It gets +2/+2 until end of turn. If it's a Dwarf, you may attach an Equipment you control to it.",
  ]

def bilboBagginsBurglar : CardDef :=
  fromOracle [
    "Bilbo Baggins, Burglar",
    "{2}{U}",
    "Legendary Creature — Halfling Rogue",
    "2/1",
    "When Bilbo Baggins enters, draw a card.",
    "//ADV//",
    "Take a Glance",
    "{U}",
    "Sorcery — Adventure",
    "Scry 2. (Then exile this card. You may cast the creature later from exile.)",
  ]

def lakeshoreApothecary : CardDef :=
  fromOracle [
    "Lakeshore Apothecary",
    "{1}{U}",
    "Creature — Human Cleric",
    "1/2",
    "Vigilance",
    "Whenever you draw your second card each turn, put a +1/+1 counter on this creature.",
  ]

def confusticateAndBebother : CardDef :=
  fromOracle [
    "Confusticate and Bebother",
    "{2}{U}",
    "Instant",
    "Choose one —",
    "• Counter target spell unless its controller pays {4}.",
    "• Draw two cards, then discard a card.",
  ]

def ravenhillFlock : CardDef :=
  fromOracle [
    "Ravenhill Flock",
    "{3}{U}",
    "Creature — Bird",
    "1/2",
    "Flying",
    "Whenever you draw a card, put a +1/+1 counter on this creature.",
  ]

def thranduilsDecree : CardDef :=
  fromOracle [
    "Thranduil's Decree",
    "{4}{U}{U}",
    "Instant",
    "Counter target spell. If a permanent spell is countered this way, exile it instead of putting it into its owner's graveyard. You may cast that card without paying its mana cost for as long as it remains exiled.",
  ]

def bilboLuckwearer : CardDef :=
  fromOracle [
    "Bilbo, Luckwearer",
    "{1}{U}",
    "Legendary Creature — Halfling Rogue",
    "1/1",
    "Bilbo can't be blocked.",
    "Whenever Bilbo deals combat damage to a player, draw a card, then discard a card.",
    "//ADV//",
    "Burglar's Plot",
    "{4}{U}",
    "Sorcery — Adventure",
    "Exchange control of two target nonland permanents that share a card type. (Then exile this card. You may cast the creature later from exile.)",
  ]

def uneasyPartings : CardDef :=
  fromOracle [
    "Uneasy Partings",
    "{3}{U}",
    "Instant",
    "This spell costs {1} less to cast if it targets an attacking nontoken creature.",
    "Target creature's owner puts it on their choice of the top or bottom of their library.",
  ]

def frontPorchSentries : CardDef :=
  fromOracle [
    "Front Porch Sentries",
    "{1}{B}",
    "Creature — Goblin Soldier",
    "2/2",
    "When this creature dies, target creature an opponent controls gets -1/-1 until end of turn.",
  ]

def greatFierceBee : CardDef :=
  fromOracle [
    "Great Fierce Bee",
    "{2}{B}",
    "Creature — Insect",
    "2/2",
    "Flying",
    "Whenever one or more other creatures die, scry 1. (Look at the top card of your library. You may put that card on the bottom.)",
  ]

def stirUpTrouble : CardDef :=
  fromOracle [
    "Stir Up Trouble",
    "{B}",
    "Sorcery",
    "As an additional cost to cast this spell, sacrifice an artifact or creature or pay {4}.",
    "Destroy target creature.",
  ]

def desolationProwler : CardDef :=
  fromOracle [
    "Desolation Prowler",
    "{1}{B}",
    "Creature — Wolf",
    "2/2",
    "Pay 2 life: This creature gets +2/+2 until end of turn. Activate only once each turn.",
  ]

def raveningWarg : CardDef :=
  fromOracle [
    "Ravening Warg",
    "{1}{B}",
    "Creature — Wolf",
    "2/2",
    "Deathtouch",
    "Ferocious — Whenever this creature attacks while you control a creature with power 4 or greater, you gain 2 life.",
  ]

def gollumSilentSlinker : CardDef :=
  fromOracle [
    "Gollum, Silent Slinker",
    "{3}{B}",
    "Legendary Creature — Halfling Horror",
    "4/3",
    "Menace (This creature can't be blocked except by two or more creatures.)",
    "//ADV//",
    "Meager Meal",
    "{B}",
    "Sorcery — Adventure",
    "Put a +1/+1 counter on up to one target creature. Target player gains 2 life. (Then exile this card. You may cast the creature later from exile.)",
  ]

def bilbosDeadlySlice : CardDef :=
  fromOracle [
    "Bilbo's Deadly Slice",
    "{1}{B}{B}",
    "Instant",
    "Destroy target creature.",
  ]

def dreadedBatCloud : CardDef :=
  fromOracle [
    "Dreaded Bat-Cloud",
    "{4}{B}",
    "Creature — Bat",
    "4/2",
    "This spell costs {3} less to cast if a creature died this turn.",
    "Flying, deathtouch",
  ]

def crudeBentBlade : CardDef :=
  fromOracle [
    "Crude Bent Blade",
    "{2}{B}",
    "Artifact — Equipment",
    "When this Equipment enters, target opponent sacrifices a creature of their choice.",
    "Equipped creature gets +2/+1.",
    "Equip {2} ({2}: Attach to target creature you control. Equip only as a sorcery.)",
  ]

def gollumTheAbandoned : CardDef :=
  fromOracle [
    "Gollum the Abandoned",
    "{1}{B}",
    "Legendary Creature — Halfling Horror",
    "2/2",
    "Gollum can't block.",
    "When Gollum enters, exile up to one target card from an opponent's graveyard. Each opponent loses 2 life.",
    "{2}, Sacrifice an artifact or creature: Return this card from your graveyard to your hand. Activate only as a sorcery.",
  ]

def gnashingOfTeeth : CardDef :=
  fromOracle [
    "Gnashing of Teeth",
    "{1}{B}{B}",
    "Sorcery",
    "Choose one —",
    "• Target creature gets -5/-5 until end of turn. If that creature would die this turn, exile it instead.",
    "• Creatures target player controls get -1/-1 until end of turn.",
  ]

def reverentHowl : CardDef :=
  fromOracle [
    "Reverent Howl",
    "{2}{B}",
    "Instant",
    "Choose one —",
    "• Target player draws two cards and loses 2 life.",
    "• Target creature gets +2/+2 and gains lifelink until end of turn.",
  ]

def stonyVoicedGoblins : CardDef :=
  fromOracle [
    "Stony-Voiced Goblins",
    "{1}{B}",
    "Creature — Goblin Bard",
    "1/1",
    "When this creature enters, each opponent discards a card.",
  ]

def smaugTheGreatCalamity : CardDef :=
  fromOracle [
    "Smaug, the Great Calamity",
    "{5}{R}{R}",
    "Legendary Creature — Dragon",
    "5/5",
    "Flying",
    "//ADV//",
    "Spew Flame",
    "{4}{R}",
    "Sorcery — Adventure",
    "Spew Flame deals 5 damage to target creature. (Then exile this card. You may cast the creature later from exile.)",
  ]

def gandalfSparkStarter : CardDef :=
  fromOracle [
    "Gandalf, Spark Starter",
    "{4}{R}{R}",
    "Legendary Creature — Avatar Wizard",
    "4/3",
    "Reach",
    "When Gandalf enters, he deals 3 damage divided as you choose among one, two, or three targets.",
  ]

def raggedShortSpear : CardDef :=
  fromOracle [
    "Ragged Short Spear",
    "{1}{R}",
    "Artifact — Equipment",
    "When this Equipment enters, you may discard a card. If you do, draw two cards.",
    "Equipped creature gets +2/+0.",
    "Equip {3} ({3}: Attach to target creature you control. Equip only as a sorcery.)",
  ]

def snowslopeHunter : CardDef :=
  fromOracle [
    "Snowslope Hunter",
    "{2}{R}",
    "Creature — Goblin Ranger",
    "2/3",
    "Sacrifice another creature or artifact: Exile the top card of your library. You may play it until the end of your next turn. Activate only during your turn and only once each turn.",
  ]

def guardianOfTheHalls : CardDef :=
  fromOracle [
    "Guardian of the Halls",
    "{1}{G}",
    "Creature — Elf Soldier",
    "2/2",
    "Trample",
    "{5}{G}{G}: Put three +1/+1 counters on this creature.",
  ]

def quarrel : CardDef :=
  fromOracle [
    "Quarrel",
    "{1}{G}",
    "Instant",
    "Target creature you control deals damage equal to its power to target creature an opponent controls.",
  ]

def galionElvenkingsButler : CardDef :=
  fromOracle [
    "Galion, Elvenking's Butler",
    "{2}{G}{G}",
    "Legendary Creature — Elf Advisor",
    "4/4",
    "Whenever Galion attacks, choose up to one other target creature you control. Its base power and toughness become equal to Galion's power and toughness until end of turn.",
  ]

def wargTactics : CardDef :=
  fromOracle [
    "Warg Tactics",
    "{1}{G}",
    "Instant",
    "Choose one —",
    "• Destroy target creature with flying.",
    "• Put a +1/+1 counter on target creature you control. It gains trample and hexproof until end of turn. (It can't be the target of spells or abilities your opponents control.)",
  ]

def beornsHospitality : CardDef :=
  fromOracle [
    "Beorn's Hospitality",
    "{1}{G}",
    "Enchantment",
    "Landfall — Whenever a land you control enters, put a +1/+1 counter on target creature you control.",
    "{5}{G}{G}: This enchantment becomes a Bear creature in addition to its other types and gains \"This creature's power and toughness are each equal to the number of lands you control.\" (This effect doesn't end.)",
  ]

def woodlandWeavemaster : CardDef :=
  fromOracle [
    "Woodland Weavemaster",
    "{1}{G}",
    "Creature — Elf Druid",
    "1/2",
    "Vigilance",
    "Whenever another Elf you control enters, this creature gets +1/+1 until end of turn.",
    "{T}: Add X mana of any one color, where X is this creature's power. Spend this mana only to cast Elf spells and activate abilities of Elf sources.",
  ]

def mirkwoodPathmaker : CardDef :=
  fromOracle [
    "Mirkwood Pathmaker",
    "{2}{G}",
    "Creature — Elf Ranger",
    "*/*",
    "Mirkwood Pathmaker's power and toughness are each equal to the number of lands you control.",
  ]

def beornReluctantHost : CardDef :=
  fromOracle [
    "Beorn, Reluctant Host",
    "{4}{G}",
    "Legendary Creature — Human Bear Shapeshifter",
    "5/5",
    "Trample",
    "//ADV//",
    "Till and Tend",
    "{1}{G}",
    "Sorcery — Adventure",
    "You may play an additional land this turn. (Then exile this card. You may cast the creature later from exile.)",
  ]

def woodElves : CardDef :=
  fromOracle [
    "Wood Elves",
    "{2}{G}",
    "Creature — Elf Scout",
    "1/1",
    "When this creature enters, search your library for a Forest card, put that card onto the battlefield, then shuffle.",
  ]

def attercop : CardDef :=
  fromOracle [
    "Attercop",
    "{1}{G}",
    "Creature — Spider",
    "2/1",
    "Reach, deathtouch",
    "Landfall — Whenever a land you control enters, this creature gets +1/+1 until end of turn.",
  ]

def ordinaryBear : CardDef :=
  fromOracle [
    "Ordinary Bear",
    "{3}{G}",
    "Creature — Bear",
    "4/5",
  ]

def largeBear : CardDef :=
  fromOracle [
    "Large Bear",
    "{3}{B/G}{B/G}",
    "Creature — Bear",
    "5/5",
    "Reach, trample, haste",
  ]

def littleBear : CardDef :=
  fromOracle [
    "Little Bear",
    "{2}{G}",
    "Creature — Bear",
    "3/2",
    "Flash",
    "When this creature enters, untap another target creature you control. If that creature is a Bear, put a +1/+1 counter on it.",
  ]

def elvenkingsHarper : CardDef :=
  fromOracle [
    "Elvenking's Harper",
    "{1}{U}",
    "Creature — Elf Bard",
    "2/2",
    "{4}{U}: Target creature can't be blocked this turn.",
  ]

def smaugsFury : CardDef :=
  fromOracle [
    "Smaug's Fury",
    "{1}{R}",
    "Instant",
    "Target creature gets +3/+0 and gains reach and first strike until end of turn.",
  ]

def wellWornSpatula : CardDef :=
  fromOracle [
    "Well-Worn Spatula",
    "{1}",
    "Artifact — Equipment",
    "When this Equipment enters, you gain 2 life.",
    "Equipped creature gets +1/+1.",
    "Equip {1} ({1}: Attach to target creature you control. Equip only as a sorcery.)",
  ]

/-- Dual land: enters tapped; `{T}: Add {A} or {B}`; tap, pay, and sacrifice
for two +1/+1 counters on a typed creature you control. One type or several
types both use `plusOneOnTarget`. The Oracle text is reconstructed from the
colors and creature types. -/
def hobbitDualLand (name : String) (a b : Color) (creatureTypes : Array String) :
    CardDef :=
  land name
    (s!"This land enters tapped.\n{dualAddClause a b}\n" ++
      s!"\{2}{manaSymbolsText #[.colored a, .colored b]}, \{T}, Sacrifice this land: " ++
      s!"Put two +1/+1 counters on target {orJoin creatureTypes.toList} you control. " ++
      "Activate only as a sorcery.")
    (entersTapped := true)
    (tapAddOneOf := #[.colored a, .colored b])
    (activatedAbilities := #[
      activated
        (Effect.plusOneOnTarget 2 creatureTypes)
        (ManaCost.ofGenericAndColors 2 [a, b])
        (tap := true) (sacrificeSource := true) (onlyAsSorcery := true)])

def elvenkingsHalls : CardDef :=
  fromOracle [
    "Elvenking's Halls",
    "Land",
    "This land enters tapped.",
    "{T}: Add {G} or {U}.",
    "{2}{G}{U}, {T}, Sacrifice this land: Put two +1/+1 counters on target Elf you control. Activate only as a sorcery.",
  ]

def ironHills : CardDef :=
  fromOracle [
    "Iron Hills",
    "Land",
    "This land enters tapped.",
    "{T}: Add {R} or {W}.",
    "{2}{R}{W}, {T}, Sacrifice this land: Put two +1/+1 counters on target Dwarf you control. Activate only as a sorcery.",
  ]

def lakeTown : CardDef :=
  fromOracle [
    "Lake-town",
    "Land",
    "This land enters tapped.",
    "{T}: Add {W} or {U}.",
    "{2}{W}{U}, {T}, Sacrifice this land: Put two +1/+1 counters on target Human you control. Activate only as a sorcery.",
  ]

def goblinTown : CardDef :=
  fromOracle [
    "Goblin-town",
    "Land",
    "This land enters tapped.",
    "{T}: Add {B} or {R}.",
    "{2}{B}{R}, {T}, Sacrifice this land: Put two +1/+1 counters on target Goblin or Orc you control. Activate only as a sorcery.",
  ]

def mirkwood : CardDef :=
  fromOracle [
    "Mirkwood",
    "Land",
    "This land enters tapped.",
    "{T}: Add {B} or {G}.",
    "{2}{B}{G}, {T}, Sacrifice this land: Put two +1/+1 counters on target Bear, Spider, or Wolf you control. Activate only as a sorcery.",
  ]

def hobbitHole : CardDef :=
  fromOracle [
    "Hobbit Hole",
    "Land",
    "{T}, Sacrifice this land: Search your library for a basic land card, put it onto the battlefield tapped, then shuffle.",
    "Halflingcycling {4} ({4}, Discard this card: Search your library for a Halfling card, reveal it, put it into your hand, then shuffle.)",
  ]

def nighthowlPursuer : CardDef :=
  fromOracle [
    "Nighthowl Pursuer",
    "{B}",
    "Creature — Wolf",
    "1/1",
    "Menace (This creature can't be blocked except by two or more creatures.)",
    "Ferocious — Whenever this creature attacks while you control a creature with power 4 or greater, this creature gets +2/+2 until end of turn.",
  ]

def wargling : CardDef :=
  fromOracle [
    "Wargling",
    "{1}{G}",
    "Creature — Wolf",
    "2/2",
    "Ferocious — Whenever this creature attacks while you control a creature with power 4 or greater, until end of turn, this creature gets +1/+0 and creatures you control gain trample.",
  ]

def wilderlandScrounger : CardDef :=
  fromOracle [
    "Wilderland Scrounger",
    "{4}{G}",
    "Creature — Wolf",
    "3/6",
    "Ferocious — Whenever this creature attacks while you control a creature with power 4 or greater, put a +1/+1 counter on each creature you control.",
  ]

def nastyLittleRabbit : CardDef :=
  fromOracle [
    "Nasty Little Rabbit",
    "{G}",
    "Creature — Rabbit",
    "1/2",
    "Ferocious — At the beginning of combat on your turn, if you control a creature with power 4 or greater, put a +1/+1 counter on this creature.",
  ]

def theChiefWarg : CardDef :=
  fromOracle [
    "The Chief Warg",
    "{2}{B}{G}",
    "Legendary Creature — Wolf",
    "3/3",
    "Menace (This creature can't be blocked except by two or more creatures.)",
    "Ferocious — Whenever you attack while you control a creature with power 4 or greater, you draw a card and lose 1 life.",
  ]

def thorinsLastStand : CardDef :=
  fromOracle [
    "Thorin's Last Stand",
    "{2}{W}{W}",
    "Instant",
    "Choose one —",
    "• Creatures you control get +2/+1 until end of turn.",
    "• Destroy target artifact or enchantment. You gain 2 life.",
  ]

def stoneBySunlight : CardDef :=
  fromOracle [
    "Stone by Sunlight",
    "{1}{W}",
    "Instant",
    "Choose one —",
    "• Destroy target creature with power 4 or greater.",
    "• Until end of turn, target creature becomes an artifact in addition to its other types and gains indestructible. (Damage and effects that say \"destroy\" don't destroy it.)",
  ]

def duskwatchHunter : CardDef :=
  fromOracle [
    "Duskwatch Hunter",
    "{2}{B/G}",
    "Creature — Wolf",
    "3/1",
    "This creature can't be blocked by tokens.",
    "When this creature enters, put a +1/+1 counter on target creature.",
  ]

def patientInstructor : CardDef :=
  fromOracle [
    "Patient Instructor",
    "{2}{W/U}",
    "Creature — Human Citizen",
    "2/2",
    "Vigilance",
    "When this creature enters, recruit. (Draw a card, then discard a card. If you discarded a nonland card, create a 1/1 white Human Soldier creature token.)",
  ]

def longLakeNuisance : CardDef :=
  fromOracle [
    "Long Lake Nuisance",
    "{3}{U}",
    "Creature — Bird",
    "3/1",
    "Flying",
    "When this creature enters, recruit. (Draw a card, then discard a card. If you discarded a nonland card, create a 1/1 white Human Soldier creature token.)",
  ]

def laketownLookout : CardDef :=
  fromOracle [
    "Lake-town Lookout",
    "{W}",
    "Creature — Human Scout",
    "1/1",
    "When this creature dies, recruit. (Draw a card, then discard a card. If you discarded a nonland card, create a 1/1 white Human Soldier creature token.)",
  ]

def giantsBoulder : CardDef :=
  fromOracle [
    "Giant's Boulder",
    "{1}",
    "Artifact",
    "When this artifact enters, scry 2. (Look at the top two cards of your library, then put any number of them on the bottom and the rest on top in any order.)",
    "{1}, {T}: Add one mana of any color.",
    "{7}, {T}, Sacrifice this artifact: Destroy target permanent.",
  ]

def longBodiedGreyDog : CardDef :=
  fromOracle [
    "Long-Bodied Grey Dog",
    "{3}",
    "Creature — Dog",
    "2/2",
    "Flash",
    "Reach",
    "When this creature enters, create a tapped Treasure token. (It's an artifact with \"{T}, Sacrifice this token: Add one mana of any color.\")",
  ]

def doriBearerOfFriends : CardDef :=
  fromOracle [
    "Dori, Bearer of Friends",
    "{2}{R}",
    "Legendary Creature — Dwarf Warrior",
    "3/2",
    "Trample",
    "When Dori enters, create a Treasure token. (It's an artifact with \"{T}, Sacrifice this token: Add one mana of any color.\")",
  ]

def esgarothGarrison : CardDef :=
  fromOracle [
    "Esgaroth Garrison",
    "{4}{W}",
    "Creature — Human Soldier",
    "*/5",
    "Esgaroth Garrison's power is equal to the number of creatures you control.",
    "When this creature enters, recruit. (Draw a card, then discard a card. If you discarded a nonland card, create a 1/1 white Human Soldier creature token.)",
  ]

def gundabadOpportunist : CardDef :=
  fromOracle [
    "Gundabad Opportunist",
    "{3}{R}",
    "Creature — Goblin Rogue",
    "4/2",
    "When this creature enters, exile the top card of your library. Until the end of your next turn, you may play that card.",
  ]

def giganticBigBear : CardDef :=
  fromOracle [
    "Gigantic Big Bear",
    "{5}{G}{G}",
    "Creature — Bear",
    "10/7",
    "This spell can't be countered.",
    "Hexproof, haste",
  ]

def bothersomeNoisemaker : CardDef :=
  fromOracle [
    "Bothersome Noisemaker",
    "{1}{R}",
    "Creature — Goblin Bard",
    "2/2",
    "Whenever you cast a noncreature spell, amass Goblins 1. (Put a +1/+1 counter on an Army you control. It's also a Goblin. If you don't control an Army, create a 0/0 black Goblin Army creature token first.)",
  ]

def fearsomeGoblinPair : CardDef :=
  fromOracle [
    "Fearsome Goblin Pair",
    "{2}{B/R}",
    "Creature — Goblin Soldier",
    "1/1",
    "When this creature dies, amass Goblins 4. (Put four +1/+1 counters on an Army you control. It's also a Goblin. If you don't control an Army, create a 0/0 black Goblin Army creature token first.)",
  ]

def goblinTownFlunkies : CardDef :=
  fromOracle [
    "Goblin-town Flunkies",
    "{1}{R}",
    "Creature — Goblin Soldier",
    "1/1",
    "Haste",
    "When this creature enters, amass Goblins 1. (Put a +1/+1 counter on an Army you control. It's also a Goblin. If you don't control an Army, create a 0/0 black Goblin Army creature token first.)",
  ]

def mistyMountainsRaider : CardDef :=
  fromOracle [
    "Misty Mountains Raider",
    "{4}{R}",
    "Creature — Goblin Soldier",
    "4/4",
    "Whenever you attack, amass Goblins 2. (Put two +1/+1 counters on an Army you control. It's also a Goblin. If you don't control an Army, create a 0/0 black Goblin Army creature token first.)",
  ]

def bardsCompany : CardDef :=
  fromOracle [
    "Bard's Company",
    "{2}{W}{U}",
    "Creature — Human Citizen",
    "2/3",
    "You may cast this spell as though it had flash if you control a Human.",
    "Other creatures you control get +1/+1.",
    "Whenever this creature enters or attacks, recruit. (Draw a card, then discard a card. If you discarded a nonland card, create a 1/1 white Human Soldier creature token.)",
  ]

def rageIntoTheValley : CardDef :=
  fromOracle [
    "Rage into the Valley",
    "{2}{B}",
    "Sorcery",
    "You draw a card and lose 1 life.",
    "Amass Goblins 2. (Put two +1/+1 counters on an Army you control. It's also a Goblin. If you don't control an Army, create a 0/0 black Goblin Army creature token first.)",
  ]

def gatheringOfDarkness : CardDef :=
  fromOracle [
    "Gathering of Darkness",
    "{3}{B}",
    "Sorcery",
    "Return up to one target creature card from your graveyard to your hand.",
    "Amass Goblins 3. (Put three +1/+1 counters on an Army you control. It's also a Goblin. If you don't control an Army, create a 0/0 black Goblin Army creature token first.)",
  ]

def soundTheTrumpets : CardDef :=
  fromOracle [
    "Sound the Trumpets",
    "{1}{U}{U}",
    "Instant",
    "Counter target spell. If that spell's mana value was 2 or less, recruit. (Draw a card, then discard a card. If you discarded a nonland card, create a 1/1 white Human Soldier creature token.)",
  ]

def fatefulDiscovery : CardDef :=
  fromOracle [
    "Fateful Discovery",
    "{3}{U}{U}",
    "Enchantment",
    "Whenever an artifact you control enters, draw a card.",
  ]

def chiefWargsCompany : CardDef :=
  fromOracle [
    "Chief Warg's Company",
    "{1}{B}{G}",
    "Creature — Wolf",
    "5/3",
    "Trample",
    "This creature can't attack unless you control two or more other Wolves.",
    "At the beginning of your upkeep, create a 2/2 green Wolf creature token.",
  ]

def dwarvenShortsword : CardDef :=
  fromOracle [
    "Dwarven Shortsword",
    "{3}{W}",
    "Artifact — Equipment",
    "When this Equipment enters, create a 2/2 red Dwarf creature token, then attach this Equipment to it.",
    "Equipped creature gets +1/+2.",
    "Equip {2} ({2}: Attach to target creature you control. Equip only as a sorcery.)",
  ]

def goblinPlateMail : CardDef :=
  fromOracle [
    "Goblin Plate Mail",
    "{1}{B/R}",
    "Artifact — Equipment",
    "When this Equipment enters, amass Goblins 1, then attach this Equipment to the amassed Army. (To amass Goblins 1, put a +1/+1 counter on an Army you control. It's also a Goblin. If you don't control an Army, create a 0/0 black Goblin Army creature token first.)",
    "Equipped creature gets +1/+0 and has menace.",
    "Equip {4}",
  ]

def momentOfGlory : CardDef :=
  fromOracle [
    "Moment of Glory",
    "{W}",
    "Sorcery",
    "Put a +1/+1 counter on target creature you control. If this spell was cast from a graveyard, also put a +1/+1 counter on each other creature you control.",
    "Flashback {4}{W} (You may cast this card from your graveyard for its flashback cost. Then exile it.)",
  ]

def plunderTheTrollshaws : CardDef :=
  fromOracle [
    "Plunder the Trollshaws",
    "{1}{U}",
    "Instant",
    "Draw a card. If this spell was cast from a graveyard, draw two cards instead.",
    "Flashback {3}{U} (You may cast this card from your graveyard for its flashback cost. Then exile it.)",
  ]

def tidingsOfWar : CardDef :=
  fromOracle [
    "Tidings of War",
    "{R}",
    "Sorcery",
    "Amass Goblins 1. If this spell was cast from a graveyard, amass Goblins 3 instead. (To amass Goblins X, put X +1/+1 counters on an Army you control. It's also a Goblin. If you don't control an Army, create a 0/0 black Goblin Army creature token first.)",
    "Flashback {3}{R} (You may cast this card from your graveyard for its flashback cost. Then exile it.)",
  ]

def eaglesRescue : CardDef :=
  fromOracle [
    "Eagle's Rescue",
    "{2}{W/U}{W/U}",
    "Enchantment — Aura",
    "Enchant creature",
    "Enchanted creature gets +2/+2 and has flying.",
    "{2}{W/U}{W/U}: Return this card from your graveyard to the battlefield attached to target creature you control with power 1 or less. Activate only as a sorcery.",
  ]

def gandalfWanderingWizard : CardDef :=
  fromOracle [
    "Gandalf, Wandering Wizard",
    "{4}{U}",
    "Legendary Creature — Avatar Wizard",
    "4/5",
    "Ward {3} (Whenever this creature becomes the target of a spell or ability an opponent controls, counter it unless that player pays {3}.)",
    "{6}: Gandalf's owner shuffles him into their library and draws three cards.",
  ]

def trollNegotiations : CardDef :=
  fromOracle [
    "Troll Negotiations",
    "{2}{G}{G}",
    "Sorcery",
    "Put two +1/+1 counters on target creature you control. Then it fights target creature an opponent controls. (Each deals damage equal to its power to the other.)",
  ]

def dwarvenMattock : CardDef :=
  fromOracle [
    "Dwarven Mattock",
    "{2}",
    "Artifact — Equipment",
    "When this Equipment enters, attach it to target Dwarf you control.",
    "Equipped creature gets +2/+2 and has ward {1}. (Whenever equipped creature becomes the target of a spell or ability an opponent controls, counter it unless that player pays {1}.)",
    "Equip {3} ({3}: Attach to target creature you control. Equip only as a sorcery.)",
  ]

def greatUglyLookingGoblin : CardDef :=
  fromOracle [
    "Great Ugly-Looking Goblin",
    "{5}{B}",
    "Creature — Goblin Soldier",
    "4/4",
    "Each creature you control with a +1/+1 counter on it has menace. (It can't be blocked except by two or more creatures.)",
    "//ADV//",
    "Clap! Snap!",
    "{1}{B}",
    "Sorcery — Adventure",
    "Amass Goblins 2. (Then exile this card. You may cast the creature later from exile.)",
  ]

def theArkenstone : CardDef :=
  fromOracle [
    "The Arkenstone",
    "{5}",
    "Legendary Artifact",
    "Creatures you control get +1/+1.",
    "At the beginning of your end step, draw a card.",
    "//ADV//",
    "Seek the Heart",
    "{2}{W}",
    "Sorcery — Adventure",
    "Search your library for a legendary creature card, reveal it, put it into your hand, then shuffle. (Then exile this card. You may cast the artifact later from exile.)",
  ]

def bolgsCompany : CardDef :=
  fromOracle [
    "Bolg's Company",
    "{B}{R}",
    "Creature — Goblin Soldier",
    "2/2",
    "This creature has haste as long as you control another Goblin.",
    "{T}, Sacrifice another Goblin: Add {B}{R}.",
  ]

def noriTellerOfTales : CardDef :=
  fromOracle [
    "Nori, Teller of Tales",
    "{1}{R/W}",
    "Legendary Creature — Dwarf Bard",
    "2/2",
    "Whenever Nori attacks, target attacking creature gains first strike until end of turn.",
  ]

def theLordOfTheEagles : CardDef :=
  fromOracle [
    "The Lord of the Eagles",
    "{7}{U}{U}",
    "Legendary Creature — Bird Noble",
    "8/8",
    "Flash",
    "This spell costs {X} less to cast, where X is the total power of creatures you control with flying.",
    "Flying",
  ]

def throrsMap : CardDef :=
  fromOracle [
    "Thrór's Map",
    "{2}",
    "Legendary Artifact",
    "When Thrór's Map enters, search your library for a basic land card, reveal it, put it into your hand, then shuffle.",
    "{2}, {T}: Draw a card, then discard a card.",
  ]

def theBlackArrow : CardDef :=
  fromOracle [
    "The Black Arrow",
    "{3}",
    "Legendary Artifact — Equipment",
    "Flash",
    "When The Black Arrow enters, it deals 1 damage to any target. If a Dragon is dealt damage this way, destroy it.",
    "Equipped creature gets +1/+1 and has reach.",
    "Equip {1} ({1}: Attach to target creature you control. Equip only as a sorcery.)",
  ]

def smaugTheMagnificent : CardDef :=
  fromOracle [
    "Smaug the Magnificent",
    "{2}{R}{R}",
    "Legendary Creature — Dragon",
    "4/3",
    "Flying, haste",
    "Whenever Smaug attacks, he deals damage equal to the number of Treasures you control to any target.",
    "At the beginning of your upkeep, create a Treasure token.",
  ]

def theQueenOfDale : CardDef :=
  fromOracle [
    "The Queen of Dale",
    "{1}{W}",
    "Legendary Creature — Human Noble",
    "2/1",
    "Whenever an opponent casts their first noncreature spell each turn, you recruit. (Draw a card, then discard a card. If you discarded a nonland card, create a 1/1 white Human Soldier creature token.)",
  ]

def oriKeeperOfSongs : CardDef :=
  fromOracle [
    "Ori, Keeper of Songs",
    "{2}{W}",
    "Legendary Creature — Dwarf Bard",
    "3/3",
    "Storied (If you control three or more artifacts, legendaries, and/or Sagas, you have an enduring story for the rest of the game.)",
    "As long as you have an enduring story, Ori gets +1/+0 and has vigilance.",
  ]

def oinTheBrave : CardDef :=
  fromOracle [
    "Óin the Brave",
    "{1}{R}",
    "Legendary Creature — Dwarf Warrior",
    "1/3",
    "Storied (If you control three or more artifacts, legendaries, and/or Sagas, you have an enduring story for the rest of the game.)",
    "As long as you have an enduring story, Óin gets +1/+0 and has haste.",
    "{1}, {T}, Discard a card: Draw a card.",
  ]

def bomburGentleDreamer : CardDef :=
  fromOracle [
    "Bombur, Gentle Dreamer",
    "{2}{R}",
    "Legendary Creature — Dwarf Bard",
    "5/3",
    "Storied (If you control three or more artifacts, legendaries, and/or Sagas, you have an enduring story for the rest of the game.)",
    "Bombur doesn't untap during your untap step unless you have an enduring story.",
  ]

def filiThePathfinder : CardDef :=
  fromOracle [
    "Fíli the Pathfinder",
    "{3}{W}",
    "Legendary Creature — Dwarf Scout",
    "2/2",
    "Storied (If you control three or more artifacts, legendaries, and/or Sagas, you have an enduring story for the rest of the game.)",
    "As long as you have an enduring story, creatures you control get +1/+1.",
    "Whenever Fíli or another nontoken Dwarf you control enters, create a 2/2 red Dwarf creature token.",
  ]

def thorinOakenshield : CardDef :=
  fromOracle [
    "Thorin Oakenshield",
    "{R}{W}",
    "Legendary Creature — Dwarf Noble",
    "3/2",
    "Trample",
    "Storied (If you control three or more artifacts, legendaries, and/or Sagas, you have an enduring story for the rest of the game.)",
    "As long as you have an enduring story, artifacts and creatures you control have ward {1}.",
  ]

def dainLordOfTheIronHills : CardDef :=
  fromOracle [
    "Dáin, Lord of the Iron Hills",
    "{1}{W}",
    "Legendary Creature — Dwarf Noble",
    "2/2",
    "Vigilance",
    "Storied (If you control three or more artifacts, legendaries, and/or Sagas, you have an enduring story for the rest of the game.)",
    "As long as you have an enduring story, creatures can't attack you unless their controller pays {1} for each of those creatures.",
  ]

def oldThrush : CardDef :=
  fromOracle [
    "Old Thrush",
    "{2}",
    "Creature — Bird",
    "1/2",
    "Flying",
    "When this creature enters, you gain 2 life. You may search your library for a basic land card, reveal it, then shuffle and put that card on top.",
  ]

def mostDecrepitOldBird : CardDef :=
  fromOracle [
    "Most Decrepit Old Bird",
    "{U}",
    "Creature — Bird",
    "1/1",
    "Flying",
    "Threshold — This creature gets +1/+1 as long as there are seven or more cards in your graveyard.",
    "//ADV//",
    "Speak Secrets",
    "{1}{U}",
    "Sorcery — Adventure",
    "Mill four cards, then put an instant or sorcery card from among them into your hand.",
  ]

def lakeTownMariners : CardDef :=
  fromOracle [
    "Lake-town Mariners",
    "{4}{U}{U}",
    "Creature — Human Citizen",
    "6/5",
    "Vigilance",
    "Ward {2} (Whenever this creature becomes the target of a spell or ability an opponent controls, counter it unless that player pays {2}.)",
    "//ADV//",
    "Gone Fishing",
    "{3}{U}",
    "Instant — Adventure",
    "Exile two target creatures and/or lands you control, then return them to the battlefield under their owner's control.",
  ]

def pineconeStrike : CardDef :=
  fromOracle [
    "Pinecone Strike",
    "{1}{R}",
    "Instant",
    "Choose one or both —",
    "• Pinecone Strike deals 3 damage to target creature. If that creature would die this turn, exile it instead.",
    "• Destroy target artifact token.",
  ]

def theLonelyMountain : CardDef :=
  fromOracle [
    "The Lonely Mountain",
    "Land — Mountain",
    "({T}: Add {R}.)",
    "This land enters tapped unless you control an Equipment.",
    "{4}{R}, {T}: Create a 2/2 red Dwarf creature token. This ability costs {1} less to activate for each Equipment you control. Activate only as a sorcery.",
  ]

def thranduilSindarinLiege : CardDef :=
  fromOracle [
    "Thranduil, Sindarin Liege",
    "{2}{G/U}{G/U}",
    "Legendary Creature — Elf Noble",
    "2/3",
    "Other Elves you control get +1/+1.",
    "Landfall — Whenever a land you control enters, create a 1/1 green Elf creature token.",
    "//ADV//",
    "Silvan Rally",
    "{1}{G/U}{G/U}",
    "Sorcery — Adventure",
    "Mill four cards, then put up to two land cards from among them into your hand. (Then exile this card. You may cast the creature later from exile.)",
  ]

def gloinTheMighty : CardDef :=
  fromOracle [
    "Glóin the Mighty",
    "{3}{R}",
    "Legendary Creature — Dwarf Warrior",
    "4/3",
    "At the beginning of your first main phase, add {R}{R}.",
    "//ADV//",
    "Easy Pickings",
    "{2}{R}",
    "Sorcery — Adventure",
    "Easy Pickings deals 1 damage to each creature your opponents control. (Then exile this card. You may cast the creature later from exile.)",
  ]

def ironHillsStalwart : CardDef :=
  fromOracle [
    "Iron Hills Stalwart",
    "{4}{R}",
    "Creature — Dwarf Warrior",
    "4/5",
    "Reach, trample",
    "When this creature enters, attach target Equipment you control to up to one target creature you control.",
  ]

def oldFatSpider : CardDef :=
  fromOracle [
    "Old Fat Spider",
    "{4}{G}{G}",
    "Creature — Spider",
    "6/7",
    "Reach",
    "This creature can't be blocked by creatures with power 2 or less.",
    "Whenever this creature becomes the target of a spell or ability an opponent controls, draw a card.",
  ]

def greatGildedBoat : CardDef :=
  fromOracle [
    "Great Gilded Boat",
    "{2}{U}",
    "Artifact — Vehicle",
    "4/4",
    "Whenever you attack, recruit. (Draw a card, then discard a card. If you discarded a nonland card, create a 1/1 white Human Soldier creature token.)",
    "Crew 2 (Tap any number of creatures you control with total power 2 or more: This Vehicle becomes an artifact creature until end of turn.)",
  ]

def desolationOfSmaug : CardDef :=
  fromOracle [
    "Desolation of Smaug",
    "{2}{R}{R}",
    "Sorcery",
    "Desolation of Smaug deals 3 damage to each non-Dragon creature.",
    "Add four mana in any combination of colors. Spend this mana only to cast Dragon spells.",
  ]

def dwarvenMauler : CardDef :=
  fromOracle [
    "Dwarven Mauler",
    "{R}",
    "Creature — Dwarf Warrior",
    "2/1",
    "Equip abilities you activate that target this creature cost {2} less to activate.",
  ]

def myPrecious : CardDef :=
  fromOracle [
    "My Precious",
    "{3}",
    "Legendary Artifact — Equipment",
    "Equipped creature has hexproof and can't be blocked.",
    "Equip—{2}, Pay 2 life.",
    "//ADV//",
    "Allure of Power",
    "{1}{B}",
    "Instant — Adventure",
    "As an additional cost to cast this spell, sacrifice a creature.",
    "Draw two cards.",
  ]

def troopOfPonies : CardDef :=
  fromOracle [
    "Troop of Ponies",
    "{2}",
    "Creature — Horse",
    "2/1",
    "{2}, {T}, Sacrifice this creature: Search your library for up to two basic land cards, reveal them, put one onto the battlefield tapped and the other into your hand, then shuffle.",
  ]

def elvenRaftSteerer : CardDef :=
  fromOracle [
    "Elven Raft-Steerer",
    "{2}{U}",
    "Creature — Elf Pilot",
    "3/2",
    "Landfall — Whenever a land you control enters, choose one —",
    "• Tap target creature an opponent controls.",
    "• Untap target creature you control.",
  ]

def mirkwoodMeditator : CardDef :=
  fromOracle [
    "Mirkwood Meditator",
    "{2}{U}",
    "Creature — Elf Druid",
    "2/4",
    "Landfall — Whenever a land you control enters, you may have this creature's base power and toughness become 4/2 until end of turn.",
  ]

def mirkwoodNurturer : CardDef :=
  fromOracle [
    "Mirkwood Nurturer",
    "{2}{G/U}",
    "Creature — Elf Ranger",
    "3/2",
    "When this creature enters, return up to one other target permanent you control to its owner's hand. If you do, put a +1/+1 counter on this creature.",
  ]

def kiliTheResourceful : CardDef :=
  fromOracle [
    "Kíli the Resourceful",
    "{1}{W}",
    "Legendary Creature — Dwarf Scout",
    "1/2",
    "Storied (If you control three or more artifacts, legendaries, and/or Sagas, you have an enduring story for the rest of the game.)",
    "As long as you have an enduring story, you may pay {0} rather than pay the equip cost of the first equip ability you activate each turn.",
    "Whenever another Dwarf or Equipment you control enters, draw a card. This ability triggers only once each turn.",
  ]

def dainsCompany : CardDef :=
  fromOracle [
    "Dáin's Company",
    "{R}{W}",
    "Creature — Dwarf Warrior",
    "2/2",
    "This creature has lifelink as long as you control another Dwarf.",
    "When this creature enters, look at the top four cards of your library. You may reveal a Dwarf or Equipment card from among them and put it into your hand. Put the rest on the bottom of your library in a random order.",
  ]

def smaugWickedWorm : CardDef :=
  fromOracle [
    "Smaug, Wicked Worm",
    "{3}{B}{R}",
    "Legendary Creature — Dragon",
    "5/5",
    "Flying",
    "When Smaug enters, create X tapped Treasure tokens, where X is the number of artifacts your opponents control.",
    "Whenever you cast a spell, if mana from a Treasure was spent to cast it, you draw a card and lose 1 life.",
  ]

def glamdringFoeHammer : CardDef :=
  fromOracle [
    "Glamdring, Foe-hammer",
    "{2}",
    "Legendary Artifact — Equipment",
    "Instant and sorcery spells you cast cost {X} less to cast, where X is equipped creature's power.",
    "Equip {2}",
    "//ADV//",
    "Gleam of Death",
    "{3}{U}",
    "Sorcery — Adventure",
    "Mill six cards, then put all instant and sorcery cards from among them into your hand. (Then exile this card. You may cast the artifact later from exile.)",
  ]

def settleTheWreckage : CardDef :=
  fromOracle [
    "Settle the Wreckage",
    "{2}{W}{W}",
    "Instant",
    "Exile all attacking creatures target player controls. That player may search their library for that many basic land cards, put those cards onto the battlefield tapped, then shuffle.",
  ]

def ironHillsBlacksmith : CardDef :=
  fromOracle [
    "Iron Hills Blacksmith",
    "{1}{W}",
    "Creature — Dwarf Artificer",
    "1/1",
    "Double strike",
    "When this creature enters, create a colorless Equipment artifact token named Axe with \"Equipped creature gets +1/+0\" and equip {2}.",
  ]

def gandalfGoblinsBane : CardDef :=
  fromOracle [
    "Gandalf, Goblins' Bane",
    "{2}{R}",
    "Legendary Creature — Avatar Wizard",
    "2/3",
    "Whenever you cast a noncreature spell, Gandalf gets +1/+1 until end of turn and deals 1 damage to each opponent.",
    "//ADV//",
    "Flameshape",
    "{1}{R}",
    "Sorcery — Adventure",
    "Look at the top two cards of your library and exile them face down. For as long as they remain exiled, you may play them if you control a Wizard.",
  ]

def anUnexpectedParty : CardDef :=
  fromOracle [
    "An Unexpected Party",
    "{2}{W}{W}",
    "Enchantment",
    "As this enchantment enters, choose a creature type.",
    "Creatures you control of the chosen type get +2/+2.",
    "//ADV//",
    "At the Door",
    "{X}{2}{W}",
    "Sorcery — Adventure",
    "Create X 2/2 red Dwarf creature tokens. (Then exile this card. You may cast the enchantment later from exile.)",
  ]

def alongTheCrookedWay : CardDef :=
  fromOracle [
    "Along the Crooked Way",
    "{2}{B}",
    "Enchantment",
    "When this enchantment enters, return target creature card from your graveyard to your hand.",
    "Whenever a creature card leaves your graveyard, amass Goblins 1.",
    "{1}{B}: Goblins and Orcs you control gain menace until end of turn.",
  ]

def azogMoriaSRuin : CardDef :=
  fromOracle [
    "Azog, Moria's Ruin",
    "{2}{B}",
    "Legendary Creature — Goblin Soldier",
    "1/3",
    "When Azog enters, destroy up to one other target creature. Its controller amasses Goblins X, where X is that creature's power. If you controlled that creature, draw a card. (To amass Goblins X, that player puts X +1/+1 counters on an Army they control. It's also a Goblin. If they don't control an Army, they create a 0/0 black Goblin Army creature token first.)",
  ]

def balinLoremaster : CardDef :=
  fromOracle [
    "Balin, Loremaster",
    "{3}{R}{R}",
    "Legendary Creature — Dwarf Bard",
    "4/4",
    "Storied (If you control three or more artifacts, legendaries, and/or Sagas, you have an enduring story for the rest of the game.)",
    "Whenever Balin or another Dwarf you control enters, you may discard your hand. Draw X cards, where X is the number of cards discarded this way. If you have an enduring story, Balin deals X damage to each opponent.",
  ]

def bardTheBowman : CardDef :=
  fromOracle [
    "Bard the Bowman",
    "{1}{W}{U}",
    "Legendary Creature — Human Archer",
    "1/3",
    "Reach",
    "Whenever you draw your second card each turn, put a +1/+1 counter on target creature. It gains lifelink until end of turn.",
  ]

def bardKingOfDale : CardDef :=
  fromOracle [
    "Bard, King of Dale",
    "{4}{W}{U}",
    "Legendary Creature — Human Noble Archer",
    "3/5",
    "Reach, vigilance",
    "If you would draw a card except the first one you draw in each of your draw steps, draw two cards instead.",
    "If one or more tokens would be created under your control, twice that many of those tokens are created instead.",
  ]

def bejeweledWarg : CardDef :=
  fromOracle [
    "Bejeweled Warg",
    "{1}{G}",
    "Creature — Wolf",
    "3/2",
    "Trample",
    "Whenever this creature deals combat damage to a player, choose one —",
    "• Put a +1/+1 counter on target Wolf you control.",
    "• Create a Treasure token. (It's an artifact with \"{T}, Sacrifice this token: Add one mana of any color.\")",
  ]

def belladonnaTook : CardDef :=
  fromOracle [
    "Belladonna Took",
    "{1}{W}",
    "Legendary Creature — Halfling Citizen",
    "2/2",
    "Whenever a token you control enters, you gain 1 life if this is the first time this ability has resolved this turn. If it's the second time, draw a card. If it's the third time, put a +1/+1 counter on each creature you control.",
  ]

def beornTheFierce : CardDef :=
  fromOracle [
    "Beorn the Fierce",
    "{3}{G}{G}",
    "Legendary Creature — Bear Shapeshifter Warrior",
    "6/6",
    "Trample",
    "Other Bears you control get +2/+2.",
    "At the beginning of combat on your turn, put a trample counter on up to one target creature you control. It becomes a Bear in addition to its other types. Then if you control three or more Bears, draw two cards.",
  ]

def bifurMelodicRider : CardDef :=
  fromOracle [
    "Bifur, Melodic Rider",
    "{4}{R/W}{R/W}",
    "Legendary Creature — Dwarf Bard",
    "4/5",
    "Storied (If you control three or more artifacts, legendaries, and/or Sagas, you have an enduring story for the rest of the game.)",
    "Whenever Bifur enters or attacks, put a +1/+1 counter on target creature.",
    "As long as you have an enduring story, if a triggered ability of a Dwarf you control triggers, that ability triggers an additional time.",
  ]

def bilboSGambit : CardDef :=
  fromOracle [
    "Bilbo's Gambit",
    "{1}{W}",
    "Instant",
    "Gift a Treasure (You may promise an opponent a gift as you cast this spell. If you do, they create a Treasure token before its other effects. It's an artifact with \"{T}, Sacrifice this token: Add one mana of any color.\")",
    "Return target spell to its owner's hand. If the gift was promised, players can't cast spells this turn.",
  ]

def bilboThiefInTheNight : CardDef :=
  fromOracle [
    "Bilbo, Thief in the Night",
    "{1}{U}",
    "Legendary Creature — Halfling Rogue",
    "2/2",
    "Spells you cast from anywhere other than your hand cost {1} less to cast.",
    "Whenever Bilbo attacks, you may cast an artifact, instant, or sorcery spell from your graveyard. If an instant or sorcery spell cast this way would be put into your graveyard, exile it instead.",
  ]

def bolgOfTheNorth : CardDef :=
  fromOracle [
    "Bolg of the North",
    "{3}{B}{R}",
    "Legendary Creature — Goblin Soldier",
    "5/5",
    "When Bolg enters, you may sacrifice another creature. When you do, Bolg deals damage equal to that creature's power to another target creature. If excess damage was dealt this way, amass Goblins X, where X is that excess damage. (Put X +1/+1 counters on an Army you control. It's also a Goblin. If you don't control an Army, create a 0/0 black Goblin Army creature token first.)",
  ]

def boughsideWanderers : CardDef :=
  fromOracle [
    "Boughside Wanderers",
    "{4}{G}{G}",
    "Creature — Elf Scout",
    "4/4",
    "When this creature enters, look at the top four cards of your library. You may reveal a permanent card from among them and put it into your hand. Put the rest on the bottom of your library in a random order.",
    "Landfall — Whenever a land you control enters, this creature gets +2/+2 until end of turn.",
  ]

def burnBurnTreeAndFern : CardDef :=
  fromOracle [
    "Burn, Burn, Tree and Fern",
    "{3}{R}",
    "Enchantment — Saga",
    "(As this Saga enters and after your draw step, add a lore counter. Sacrifice after IV.)",
    "I — This Saga deals 6 damage to target creature an opponent controls.",
    "II — Destroy target artifact an opponent controls.",
    "III, IV — Add {R}.",
  ]

def cantankerousKeepers : CardDef :=
  fromOracle [
    "Cantankerous Keepers",
    "{5}{G}",
    "Creature — Elf Soldier",
    "4/3",
    "Affinity for Elves (This spell costs {1} less to cast for each Elf you control.)",
    "When this creature enters, mill four cards, then put all Elf cards from among them into your hand.",
  ]

def celebrateTheMountainKing : CardDef :=
  fromOracle [
    "Celebrate the Mountain-king",
    "{3}{W}",
    "Enchantment",
    "When this enchantment enters, for each opponent, exile up to one target nonland permanent that player controls until this enchantment leaves the battlefield.",
    "When this enchantment enters, recruit. (Draw a card, then discard a card. If you discarded a nonland card, create a 1/1 white Human Soldier creature token.)",
  ]

def dancingFromDarkToDawn : CardDef :=
  fromOracle [
    "Dancing from Dark to Dawn",
    "{3}{G}{G}",
    "Enchantment",
    "Whenever you cast a creature spell, put X +1/+1 counters on target creature you control, where X is that spell's mana value.",
    "Landfall — Whenever a land you control enters, create a 2/2 green Bear creature token.",
  ]

def desertWereWorm : CardDef :=
  fromOracle [
    "Desert Were-Worm",
    "{4}{R}{R}",
    "Creature — Dragon Wurm",
    "0/5",
    "This creature gets +2/+0 for each Mountain you control.",
    "Whenever you attack with creatures with total power 12 or greater for the first time each turn, untap all attacking creatures. After this phase, there is an additional combat phase.",
  ]

def downInTheValley : CardDef :=
  fromOracle [
    "Down in the Valley",
    "{2}{G}",
    "Enchantment — Saga",
    "(As this Saga enters and after your draw step, add a lore counter. Sacrifice after IV.)",
    "I — Search your library for a basic land card, reveal it, put it into your hand, then shuffle.",
    "II — This Saga gains \"Landfall — Whenever a land you control enters, create a 1/1 green Elf creature token.\"",
    "III, IV — Elves you control get +1/+0 and gain vigilance until end of turn.",
  ]

def downDownToGoblinTown : CardDef :=
  fromOracle [
    "Down, Down to Goblin-town",
    "{2}{B}",
    "Enchantment — Saga",
    "(As this Saga enters and after your draw step, add a lore counter. Sacrifice after IV.)",
    "I — Target opponent reveals their hand. You choose a nonland card from it. That player discards that card.",
    "II — Amass Goblins 1. (Put a +1/+1 counter on an Army you control. It's also a Goblin. If you don't control an Army, create a 0/0 black Goblin Army creature token first.)",
    "III, IV — Target opponent loses 1 life and you gain 1 life.",
  ]

def dwalinWeaponmaster : CardDef :=
  fromOracle [
    "Dwalin, Weaponmaster",
    "{1}{R/W}",
    "Legendary Creature — Dwarf Warrior",
    "2/1",
    "First strike",
    "Whenever Dwalin enters or attacks, put a hone counter on each Equipment you control. (Each hone counter on an Equipment grants +1/+0 to equipped creature.)",
  ]

def dainIronfoot : CardDef :=
  fromOracle [
    "Dáin Ironfoot",
    "{2}{R}",
    "Legendary Creature — Dwarf Warrior",
    "1/4",
    "When Dáin enters, create a colorless Equipment artifact token named Axe with \"Equipped creature gets +1/+0\" and equip {2}. When you do, attach it to target creature you control.",
    "Whenever Dáin attacks, each equipped attacking creature gains double strike until end of turn.",
  ]

def elrondMoonReader : CardDef :=
  fromOracle [
    "Elrond, Moon-Reader",
    "{2}{U}",
    "Legendary Creature — Elf Noble",
    "3/3",
    "Whenever you activate an ability of a creature, draw a card. This ability triggers only once each turn.",
    "{5}{U}{U}: Exile up to two other target nonland permanents you control. Return those cards to the battlefield under their owner's control at the beginning of the next end step.",
  ]

def elvenPassage : CardDef :=
  fromOracle [
    "Elven Passage",
    "Land",
    "{T}, Pay 1 life, Sacrifice this land: Search your library for a basic land card, put it onto the battlefield tapped, then shuffle. You may behold an Elf. If you do, untap that land. (To behold an Elf, choose an Elf you control or reveal an Elf card from your hand.)",
  ]

def enchantedRiverSGrasp : CardDef :=
  fromOracle [
    "Enchanted River's Grasp",
    "{2}{U}",
    "Enchantment — Aura",
    "Enchant creature",
    "When this Aura enters, tap enchanted creature and remove all counters from it.",
    "Enchanted creature loses all abilities and doesn't untap during its controller's untap step.",
  ]

def getawayBarrel : CardDef :=
  fromOracle [
    "Getaway Barrel",
    "{3}{R}",
    "Artifact",
    "When this artifact is put into a graveyard from the battlefield, reveal the top thirteen cards of your library. Put a random creature card from among them onto the battlefield. Put the rest on the bottom of your library in a random order.",
  ]

def gleamingSplendor : CardDef :=
  fromOracle [
    "Gleaming Splendor",
    "{1}{W}",
    "Enchantment",
    "Whenever an opponent draws their second card each turn, you create a Treasure token.",
    "{2}{W}: Two target players each draw a card.",
  ]

def gollumRiddleMaster : CardDef :=
  fromOracle [
    "Gollum, Riddle Master",
    "{1}{B}",
    "Legendary Creature — Halfling Horror",
    "3/1",
    "As Gollum enters, choose odd or even. (Zero is even.)",
    "Whenever an opponent casts a spell with mana value of the chosen quality, choose one that hasn't been chosen —",
    "• Put a +1/+1 counter on Gollum.",
    "• Each opponent loses 2 life and you gain 2 life.",
    "• Draw a card.",
  ]

def headOfTheHunt : CardDef :=
  fromOracle [
    "Head of the Hunt",
    "{2}{B}{B}",
    "Creature — Wolf",
    "4/3",
    "Flash",
    "If a creature an opponent controls would die, exile it instead. When you do, create a 2/2 green Wolf creature token.",
  ]

def insideInformation : CardDef :=
  fromOracle [
    "Inside Information",
    "{X}{B}{B}",
    "Sorcery",
    "Exile the top X cards of target opponent's library. You may play those cards this turn. If you cast a spell this way, pay life equal to its mana value rather than pay its mana cost.",
  ]

def keyToTheSideDoor : CardDef :=
  fromOracle [
    "Key to the Side-Door",
    "{1}",
    "Artifact",
    "{2}, {T}: Target creature can't be blocked this turn.",
    "{1}, {T}, Discard a legendary card with the same name as a legendary permanent you control: Draw two cards.",
  ]

def lakeTownToymaker : CardDef :=
  fromOracle [
    "Lake-town Toymaker",
    "{3}{W}",
    "Creature — Human Artificer",
    "3/4",
    "At the beginning of combat on your turn, if you've drawn two or more cards this turn, another target creature you control gets +3/+0 and gains first strike until end of turn.",
  ]

def lastLightOfDurinSDay : CardDef :=
  fromOracle [
    "Last Light of Durin's Day",
    "{1}{R}",
    "Enchantment",
    "Whenever a Mountain you control enters, put a quest counter on this enchantment. If it has six or more quest counters on it, sacrifice it. If you do, search your hand and/or library for a Dragon card and put it onto the battlefield. If you search your library this way, shuffle.",
    "Mountaincycling {2} ({2}, Discard this card: Search your library for a Mountain card, reveal it, put it into your hand, then shuffle.)",
  ]

def masterSCouncillors : CardDef :=
  fromOracle [
    "Master's Councillors",
    "{1}{U}",
    "Creature — Human Advisor",
    "1/3",
    "Vigilance",
    "This creature gets +2/+0 for each graveyard with seven or more cards in it.",
    "Whenever you draw your second card each turn, target player mills three cards. (They put the top three cards of their library into their graveyard.)",
  ]

def oldFatSpiderCanTSeeMe : CardDef :=
  fromOracle [
    "Old Fat Spider Can't See Me",
    "{2}{U}",
    "Enchantment — Saga",
    "(As this Saga enters and after your draw step, add a lore counter. Sacrifice after IV.)",
    "I — Target creature you control gains hexproof for as long as this Saga remains on the battlefield.",
    "II — Prevent all damage that would be dealt by up to one target creature for as long as this Saga remains on the battlefield.",
    "III, IV — Draw a card.",
  ]

def orcristGoblinCleaver : CardDef :=
  fromOracle [
    "Orcrist, Goblin-cleaver",
    "{3}",
    "Legendary Artifact — Equipment",
    "Equipped creature gets +2/+2 and has trample.",
    "Whenever equipped creature deals combat damage to a player, choose a creature type. Create a Treasure token for each creature you control of that type.",
    "Equip {3}",
  ]

def partInFriendship : CardDef :=
  fromOracle [
    "Part in Friendship",
    "{4}{G}",
    "Enchantment",
    "Whenever a nontoken creature you control dies, reveal cards from the top of your library until you reveal a creature card. If its mana value is less than or equal to the number of lands you control, put it onto the battlefield. Otherwise, put it into your hand. Put the rest on the bottom of your library in a random order. This ability triggers only once each turn.",
  ]

def radagastOfRhosgobel : CardDef :=
  fromOracle [
    "Radagast of Rhosgobel",
    "{2}{G}{G}",
    "Legendary Creature — Avatar Wizard",
    "2/5",
    "The first creature spell you cast each turn costs {2} less to cast and can be cast as though it had flash.",
  ]

def rhovanionRampager : CardDef :=
  fromOracle [
    "Rhovanion Rampager",
    "{2}{B}",
    "Creature — Wolf",
    "3/2",
    "Whenever this creature attacks, you may sacrifice another creature. If you do, put a number of +1/+1 counters on this creature equal to the sacrificed creature's power.",
    "When this creature dies, amass Goblins X, where X is this creature's power. (Put X +1/+1 counters on an Army you control. It's also a Goblin. If you don't control an Army, create a 0/0 black Goblin Army creature token first.)",
  ]

def riddlesInTheDark : CardDef :=
  fromOracle [
    "Riddles in the Dark",
    "{2}{U}",
    "Instant",
    "Look at the top four cards of your library and separate them into a face-down pile and a face-up pile. An opponent chooses one of the piles. Put that pile into your hand and the other into your graveyard.",
  ]

def roadsGoEverEverOn : CardDef :=
  fromOracle [
    "Roads Go Ever, Ever On",
    "{1}{W}",
    "Enchantment — Saga",
    "(As this Saga enters and after your draw step, add a lore counter. Sacrifice after IV.)",
    "I — Search your library for up to two basic Plains cards, exile them, then shuffle. You gain 2 life.",
    "II, III — Put a card exiled with this Saga into its owner's hand.",
    "IV — Whenever you attack this turn, target creature you control gets +1/+1 until end of turn for each Plains you control.",
  ]

def rollRollRollRoll : CardDef :=
  fromOracle [
    "Roll-Roll-Roll-Roll",
    "{2}{U}",
    "Enchantment — Saga",
    "(As this Saga enters and after your draw step, add a lore counter. Sacrifice after IV.)",
    "I, II, III, IV — Exile up to one target creature or land you control. If you do, return it to the battlefield under its owner's control at the beginning of the next end step.",
  ]

def silvanReveler : CardDef :=
  fromOracle [
    "Silvan Reveler",
    "{2}{G}{U}",
    "Creature — Elf Citizen",
    "3/2",
    "When this creature enters, draw a card, then discard a card. If you discard a land card this way, put it from your graveyard onto the battlefield tapped.",
    "Landfall — Whenever a land you control enters, you may pay {1}{G}{U}. If you do, return this card from your graveyard to your hand.",
  ]

def stingBilboSSword : CardDef :=
  fromOracle [
    "Sting, Bilbo's Sword",
    "{2}",
    "Legendary Artifact — Equipment",
    "Flash",
    "When Sting enters, put a hone counter on Sting for each creature target opponent controls. Attach Sting to up to one target creature you control. (Each hone counter on an Equipment grants +1/+0 to equipped creature.)",
    "Equip {3}",
  ]

def stoneGiantOfHighPass : CardDef :=
  fromOracle [
    "Stone-Giant of High Pass",
    "{5}{R}{R}",
    "Creature — Giant",
    "7/7",
    "Whenever this creature enters or attacks, create a 3/1 colorless Wall artifact creature token with defender named Stone Boulder.",
    "{2}{R}, Sacrifice an artifact: This creature deals 4 damage to any target.",
  ]

def supperForSpiders : CardDef :=
  fromOracle [
    "Supper for Spiders",
    "{1}{B}",
    "Instant",
    "Put onto the battlefield under your control all creature cards in your opponents' graveyards that were put there from the battlefield this turn. They are Food artifacts with \"{2}, {T}, Sacrifice this artifact: You gain 3 life.\" (They lose all other types and subtypes.)",
  ]

def theEaglesAreComing : CardDef :=
  fromOracle [
    "The Eagles Are Coming!",
    "{1}{W}",
    "Instant",
    "Kicker {2}{W}{W} (You may pay an additional {2}{W}{W} as you cast this spell.)",
    "Choose target creature you own. If this spell was kicked, instead choose any number of target creatures you own. Return each chosen creature to your hand. At the beginning of the next upkeep, create a 4/4 white Bird Soldier creature token with flying for each creature returned to your hand this way.",
  ]

def theGreatGoblin : CardDef :=
  fromOracle [
    "The Great Goblin",
    "{1}{B/R}{B/R}",
    "Legendary Creature — Goblin Noble",
    "3/2",
    "Whenever you put one or more counters on a Goblin, Orc, or Army you control, The Great Goblin deals 2 damage to target opponent.",
    "Whenever another Goblin, Orc, or Army you control dies, exile the top card of your library. You may play it until the end of your next turn.",
  ]

def theMasterOfLakeTown : CardDef :=
  fromOracle [
    "The Master of Lake-town",
    "{1}{B}{B}",
    "Legendary Creature — Human Advisor",
    "3/2",
    "Deathtouch",
    "Whenever a player loses life, that player mills that many cards. (Damage causes loss of life.)",
    "When The Master of Lake-town dies, draw a card for each graveyard with seven or more cards in it.",
  ]

def theMistyMountainsCold : CardDef :=
  fromOracle [
    "The Misty Mountains Cold",
    "{2}{R}",
    "Enchantment — Saga",
    "(As this Saga enters and after your draw step, add a lore counter. Sacrifice after IV.)",
    "I, II, III, IV — Create a Treasure token. Then if you control four or more Treasures, sacrifice this Saga. If you do, create a 6/6 red Dragon creature token with flying. (A Treasure token is an artifact with \"{T}, Sacrifice this token: Add one mana of any color.\")",
  ]

def theMountainKingSReturn : CardDef :=
  fromOracle [
    "The Mountain-king's Return",
    "{2}{W}",
    "Enchantment — Saga",
    "(As this Saga enters and after your draw step, add a lore counter. Sacrifice after III.)",
    "I — Recruit. (Draw a card, then discard a card. If you discarded a nonland card, create a 1/1 white Human Soldier creature token.)",
    "II — Return target creature card with mana value 3 or less from your graveyard to the battlefield.",
    "III — Put a +1/+1 counter on up to one target creature.",
  ]

def theNotaryHobbits : CardDef :=
  fromOracle [
    "The Notary Hobbits",
    "{3}{G}{G}",
    "Legendary Creature — Halfling Advisor",
    "1/1",
    "When The Notary Hobbits enter, if they're not a token, create two tokens that are copies of them, except the tokens aren't legendary.",
    "{T}: Add {C} for each Halfling you control.",
  ]

def theSackvilleBagginses : CardDef :=
  fromOracle [
    "The Sackville-Bagginses",
    "{1}{B}",
    "Legendary Creature — Halfling Citizen",
    "2/2",
    "When The Sackville-Bagginses enter, you may sacrifice another creature or artifact. If you do, draw a card and create a Treasure token.",
    "Whenever you sacrifice a token, target opponent loses 1 life.",
  ]

def thorinMountainKing : CardDef :=
  fromOracle [
    "Thorin, Mountain-king",
    "{3}{R}",
    "Legendary Creature — Dwarf Noble",
    "3/4",
    "Trample",
    "When Thorin enters, attach any number of target Equipment you control to target creature you control. When one or more Equipment become attached to that creature this way, that creature deals damage equal to its power to up to one target creature.",
  ]

def thranduilSCompany : CardDef :=
  fromOracle [
    "Thranduil's Company",
    "{2}{G}{U}",
    "Creature — Elf Soldier",
    "3/4",
    "As long as you control another Elf, you may play an additional land on each of your turns.",
    "Landfall — Whenever a land you control enters, put two +1/+1 counters on target creature you control. It gains vigilance until end of turn.",
  ]

def thranduilTheElvenking : CardDef :=
  fromOracle [
    "Thranduil, the Elvenking",
    "{2}{B}{G}{U}",
    "Legendary Creature — Elf Noble",
    "5/6",
    "Thranduil has all activated abilities of all Elf cards in your graveyard.",
    "Whenever another legendary Elf you control enters, draw two cards, then discard a card.",
  ]

def throughTheForestGate : CardDef :=
  fromOracle [
    "Through the Forest Gate",
    "{6}{G}{G}",
    "Sorcery",
    "Look at the top twenty cards of your library, put any number of land cards from among them onto the battlefield tapped, then shuffle. You gain 8 life.",
  ]

def tomBertAndWilliam : CardDef :=
  fromOracle [
    "Tom, Bert, and William",
    "{3}{B}{G}",
    "Legendary Creature — Troll",
    "5/5",
    "{1}, Sacrifice another creature: Draw cards equal to the sacrificed creature's power, then discard a card.",
    "When Tom, Bert, and William die, if they were a creature, return them to the battlefield. They're an artifact. (They're no longer a creature.)",
  ]

def uncoverTheMoonLetters : CardDef :=
  fromOracle [
    "Uncover the Moon-Letters",
    "{3}{U}",
    "Enchantment",
    "Whenever you cast a noncreature spell, you may draw X cards, where X is the amount of mana spent to cast that spell. If you do, discard two cards.",
  ]

def wizardSStaff : CardDef :=
  fromOracle [
    "Wizard's Staff",
    "{1}{U}",
    "Artifact — Equipment",
    "Equipped creature has prowess. (Whenever its controller casts a noncreature spell, that creature gets +1/+1 until end of turn.)",
    "If a triggered ability of equipped creature triggers, that ability triggers an additional time.",
    "Equip Wizard {1}",
    "Equip {3}",
  ]

/-- Every unique card in The Hobbit (HOB), including Journey basic lands
that are also in the core catalog. -/
@[irreducible, noinline] def hobbitCards : Array CardDef := #[
  plains,
  island,
  swamp,
  mountain,
  forest,
  bofurReliableGuardian,
  dwarvenProvisioner,
  velvetwingButterflies,
  magnificentEnd,
  eagleOfTheGreatShelf,
  vowToErebor,
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

#guard bofurReliableGuardian.colors.isMonocolored
#guard (attercop.summary.splitOn "a land you control enters").length > 1
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
#guard soundTheTrumpets.isInstant
#guard soundTheTrumpets.spellEffect == some (Effect.counterThenRecruitIfMvAtMost 2)
#guard soundTheTrumpets.hasCastKind .counter
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
#guard (beornsHospitality.summary.splitOn "a land you control enters").length > 1
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
#guard (raveningWarg.summary.splitOn "while you control a creature with power 4 or greater").length > 1
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
#guard littleBear.triggeredAbilities == #[.onEnterUntapOtherPlusOneIfSubtype "Bear"]
#guard gandalfGoblinsBane.triggeredAbilities == #[.onCastNoncreaturePumpAndDamageOpponents 1]
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
#guard (bilbosDeadlySlice.summary.splitOn "destroy target creature").length > 1
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
#guard (smaugTheGreatCalamity.summary.splitOn "//ADV//").length == 1
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
#guard (beornReluctantHost.summary.splitOn "//ADV//").length == 1
#guard !beornReluctantHost.leftoverOracleLines.any (· == "//ADV//")
#guard (beornReluctantHost.summary.splitOn "Till and Tend {1}{G}").length > 1
#guard (beornReluctantHost.summary.splitOn "trample").length > 1
#guard (beornReluctantHost.summary.splitOn "additional land").length > 1
#guard (bofurReliableGuardian.summary.splitOn "Concerted Care {1}{W}").length > 1
#guard (velvetwingButterflies.summary.splitOn "Gaze in Wonder {1}{W}").length > 1
#guard (bilboBagginsBurglar.summary.splitOn "Take a Glance {U}").length > 1
#guard (bilboLuckwearer.summary.splitOn "Burglar's Plot {4}{U}").length > 1
#guard (gollumSilentSlinker.summary.splitOn "Meager Meal {B}").length > 1

end Mtg.Engine.Catalog
