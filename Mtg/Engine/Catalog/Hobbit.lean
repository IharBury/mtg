import Mtg.Engine.Card

/-!
# The Hobbit catalog

Oracle characteristics for cards that appear in the Magic: The Gathering |
The Hobbit Welcome Decks. The engine models a subset of rules text
(keywords including flash and hexproof, simple `{T}: Add` mana abilities, non-mana
activated abilities such as Wayfarer's Bauble, Snowslope Hunter, Goblin
Cratermaker, Goblin Fireleaper, and Equip, static abilities that grant trample or pump an enchanted
or equipped creature, attack triggers that pump or set another creature's base
power and toughness, becomes-blocked triggers that
damage blockers, dies triggers that deal last-known power, enters triggers that scry, may discard to draw, or deal damage
divided among targets, Aura and Equipment attachment, adventurer cards
(casting an Adventure, then the creature from exile), modal spells, destroy, +1/+1
counters, until-end-of-turn keyword grants, and a few one-shot spell effects);
remaining abilities are stored as Oracle text only.

Source: https://magic.wizards.com/en/news/announcements/the-hobbit-welcome-decks
-/

namespace Mtg.Engine.Catalog

open Mtg.Engine

def bofurReliableGuardian : CardDef := {
  name := "Bofur, Reliable Guardian"
  manaCost := ManaCost.ofColor .white
  types := #[.creature]
  subtypes := #["Dwarf", "Scout"]
  supertypes := #[.legendary]
  oracleText := "Lifelink"
  power := some 1
  toughness := some 1
}

def dwarvenProvisioner : CardDef := {
  name := "Dwarven Provisioner"
  manaCost := ManaCost.ofGenericAndColor 1 .white
  types := #[.creature]
  subtypes := #["Dwarf", "Citizen"]
  oracleText := "{3}{W}: Creatures you control get +1/+1 until end of turn."
  power := some 2
  toughness := some 2
}

def velvetwingButterflies : CardDef := {
  name := "Velvetwing Butterflies"
  manaCost := ManaCost.ofGenericAndColor 2 .white
  types := #[.creature]
  subtypes := #["Insect"]
  oracleText := "Flying"
  power := some 2
  toughness := some 2
  keywords := { Keywords.none with flying := true }
}

def magnificentEnd : CardDef := {
  name := "Magnificent End"
  manaCost := ManaCost.ofGenericAndColor 4 .white
  types := #[.instant]
  oracleText := "This spell costs {3} less to cast if it targets a tapped creature.\nMagnificent End deals 5 damage to target creature."
  spellEffect := some (.dealDamage 5)
}

def mentorOfTheMeek : CardDef := {
  name := "Mentor of the Meek"
  manaCost := ManaCost.ofGenericAndColor 2 .white
  types := #[.creature]
  subtypes := #["Human", "Soldier"]
  oracleText := "Whenever another creature you control with power 2 or less enters, you may pay {1}. If you do, draw a card."
  power := some 2
  toughness := some 2
}

def fiendHunter : CardDef := {
  name := "Fiend Hunter"
  manaCost := ManaCost.ofGenericAndColors 1 [.white, .white]
  types := #[.creature]
  subtypes := #["Human", "Cleric"]
  oracleText := "When this creature enters, you may exile another target creature.\nWhen this creature leaves the battlefield, return the exiled card to the battlefield under its owner's control."
  power := some 1
  toughness := some 3
}

def errandRiderOfGondor : CardDef := {
  name := "Errand-Rider of Gondor"
  manaCost := ManaCost.ofGenericAndColor 2 .white
  types := #[.creature]
  subtypes := #["Human", "Soldier"]
  oracleText := "When this creature enters, draw a card. Then if you don't control a legendary creature, put a card from your hand on the bottom of your library."
  power := some 3
  toughness := some 2
}

def landrovalHorizonWitness : CardDef := {
  name := "Landroval, Horizon Witness"
  manaCost := ManaCost.ofGenericAndColor 4 .white
  types := #[.creature]
  subtypes := #["Bird", "Noble"]
  supertypes := #[.legendary]
  oracleText := "Flying\nWhenever two or more creatures you control attack a player, target attacking creature without flying gains flying until end of turn."
  power := some 3
  toughness := some 4
  keywords := { Keywords.none with flying := true }
}

def roguesPassage : CardDef := {
  name := "Rogue's Passage"
  types := #[.land]
  oracleText := "{T}: Add {C}.\n{4}, {T}: Target creature can't be blocked this turn."
  tapAddMana := #[.colorless]
}

def soldierOfTheGreyHost : CardDef := {
  name := "Soldier of the Grey Host"
  manaCost := ManaCost.ofGenericAndColor 3 .white
  types := #[.creature]
  subtypes := #["Spirit", "Soldier"]
  oracleText := "Flash\nFlying\nWhen this creature enters, target creature gets +2/+0 until end of turn."
  power := some 2
  toughness := some 2
  keywords := { Keywords.none with flying := true }
}

def eaglesOfTheNorth : CardDef := {
  name := "Eagles of the North"
  manaCost := ManaCost.ofGenericAndColor 5 .white
  types := #[.creature]
  subtypes := #["Bird", "Soldier"]
  oracleText := "Flying\nWhen this creature enters, creatures you control get +1/+0 and gain first strike until end of turn.\nPlainscycling {1} ({1}, Discard this card: Search your library for a Plains card, reveal it, put it into your hand, then shuffle.)"
  power := some 3
  toughness := some 3
  keywords := { Keywords.none with flying := true }
}

def dunedainBlade : CardDef := {
  name := "Dúnedain Blade"
  manaCost := ManaCost.ofGenericAndColor 1 .white
  types := #[.artifact]
  subtypes := #["Equipment"]
  oracleText := "Equipped creature gets +2/+1.\nEquip Human {1}\nEquip {3} ({3}: Attach to target creature you control. Equip only as a sorcery.)"
}

def fogOnTheBarrowDowns : CardDef := {
  name := "Fog on the Barrow-Downs"
  manaCost := ManaCost.ofGenericAndColor 2 .white
  types := #[.enchantment]
  subtypes := #["Aura"]
  oracleText := "Enchant creature\nEnchanted creature is a Spirit and can't attack or block. (It loses all other creature types.)"
}

def eagleOfTheGreatShelf : CardDef := {
  name := "Eagle of the Great Shelf"
  manaCost := ManaCost.ofGenericAndColor 4 .white
  types := #[.creature]
  subtypes := #["Bird", "Soldier"]
  oracleText := "Flying\nWhenever this creature attacks, it gets +1/+1 until end of turn for each other creature you control."
  power := some 2
  toughness := some 5
  keywords := { Keywords.none with flying := true }
}

def banishingLight : CardDef := {
  name := "Banishing Light"
  manaCost := ManaCost.ofGenericAndColor 2 .white
  types := #[.enchantment]
  oracleText := "When this enchantment enters, exile target nonland permanent an opponent controls until this enchantment leaves the battlefield."
}

def dawnOfANewAge : CardDef := {
  name := "Dawn of a New Age"
  manaCost := ManaCost.ofGenericAndColor 1 .white
  types := #[.enchantment]
  oracleText := "This enchantment enters with a hope counter on it for each creature you control.\nAt the beginning of your end step, remove a hope counter from this enchantment. If you do, draw a card. Then if this enchantment has no hope counters on it, sacrifice it and you gain 4 life."
}

def vowToErebor : CardDef := {
  name := "Vow to Erebor"
  manaCost := ManaCost.ofGenericAndColor 1 .white
  types := #[.instant]
  oracleText := "Untap target creature you control. It gets +2/+2 until end of turn. If it's a Dwarf, you may attach an Equipment you control to it."
  spellEffect := some (.pump 2 2)
}

def westfoldRider : CardDef := {
  name := "Westfold Rider"
  manaCost := ManaCost.ofGenericAndColor 1 .white
  types := #[.creature]
  subtypes := #["Human", "Knight"]
  oracleText := "Sacrifice this creature: Destroy target artifact or enchantment. Activate only as a sorcery."
  power := some 3
  toughness := some 1
}

def esquireOfTheKing : CardDef := {
  name := "Esquire of the King"
  manaCost := ManaCost.ofColor .white
  types := #[.creature]
  subtypes := #["Human", "Soldier"]
  oracleText := "{4}{W}, {T}: Creatures you control get +1/+1 until end of turn. This ability costs {2} less to activate if you control a legendary creature."
  power := some 1
  toughness := some 1
}

def bilboBagginsBurglar : CardDef := {
  name := "Bilbo Baggins, Burglar"
  manaCost := ManaCost.ofGenericAndColor 2 .blue
  types := #[.creature]
  subtypes := #["Halfling", "Rogue"]
  supertypes := #[.legendary]
  oracleText := "When Bilbo Baggins enters, draw a card."
  power := some 2
  toughness := some 1
}

def pelargirSurvivor : CardDef := {
  name := "Pelargir Survivor"
  manaCost := ManaCost.ofGenericAndColor 1 .blue
  types := #[.creature]
  subtypes := #["Human", "Peasant"]
  oracleText := "{T}: Add one mana of any color. Spend this mana only to cast an instant or sorcery spell.\n{5}{U}, {T}: Target player mills three cards. (They put the top three cards of their library into their graveyard.)"
  power := some 1
  toughness := some 3
}

def lakeshoreApothecary : CardDef := {
  name := "Lakeshore Apothecary"
  manaCost := ManaCost.ofGenericAndColor 1 .blue
  types := #[.creature]
  subtypes := #["Human", "Cleric"]
  oracleText := "Vigilance\nWhenever you draw your second card each turn, put a +1/+1 counter on this creature."
  power := some 1
  toughness := some 2
}

def confusticateAndBebother : CardDef := {
  name := "Confusticate and Bebother"
  manaCost := ManaCost.ofGenericAndColor 2 .blue
  types := #[.instant]
  oracleText := "Choose one —\n• Counter target spell unless its controller pays {4}.\n• Draw two cards, then discard a card."
}

def ravenhillFlock : CardDef := {
  name := "Ravenhill Flock"
  manaCost := ManaCost.ofGenericAndColor 3 .blue
  types := #[.creature]
  subtypes := #["Bird"]
  oracleText := "Flying\nWhenever you draw a card, put a +1/+1 counter on this creature."
  power := some 1
  toughness := some 2
  keywords := { Keywords.none with flying := true }
}

def lorienRevealed : CardDef := {
  name := "Lórien Revealed"
  manaCost := ManaCost.ofGenericAndColors 3 [.blue, .blue]
  types := #[.sorcery]
  oracleText := "Draw three cards.\nIslandcycling {1} ({1}, Discard this card: Search your library for an Island card, reveal it, put it into your hand, then shuffle.)"
}

def thranduilsDecree : CardDef := {
  name := "Thranduil's Decree"
  manaCost := ManaCost.ofGenericAndColors 4 [.blue, .blue]
  types := #[.instant]
  oracleText := "Counter target spell. If a permanent spell is countered this way, exile it instead of putting it into its owner's graveyard. You may cast that card without paying its mana cost for as long as it remains exiled."
}

def knightsOfDolAmroth : CardDef := {
  name := "Knights of Dol Amroth"
  manaCost := ManaCost.ofGenericAndColor 3 .blue
  types := #[.creature]
  subtypes := #["Human", "Knight"]
  oracleText := "Whenever you draw your second card each turn, put a +1/+1 counter on this creature."
  power := some 3
  toughness := some 3
}

def greyHavensNavigator : CardDef := {
  name := "Grey Havens Navigator"
  manaCost := ManaCost.ofGenericAndColor 2 .blue
  types := #[.creature]
  subtypes := #["Elf", "Pilot"]
  oracleText := "Flash\nWhen this creature enters, scry 1."
  power := some 3
  toughness := some 2
}

def ithilienKingfisher : CardDef := {
  name := "Ithilien Kingfisher"
  manaCost := ManaCost.ofGenericAndColor 2 .blue
  types := #[.creature]
  subtypes := #["Bird"]
  oracleText := "Flying\nWhen this creature dies, draw a card."
  power := some 2
  toughness := some 1
  keywords := { Keywords.none with flying := true }
}

def hithlainKnots : CardDef := {
  name := "Hithlain Knots"
  manaCost := ManaCost.ofGenericAndColor 1 .blue
  types := #[.instant]
  oracleText := "Tap target creature. Scry 1.\nDraw a card."
}

def captainOfUmbar : CardDef := {
  name := "Captain of Umbar"
  manaCost := ManaCost.ofGenericAndColor 2 .blue
  types := #[.creature]
  subtypes := #["Human", "Pirate"]
  oracleText := "{1}, {T}: Draw a card, then discard a card."
  power := some 2
  toughness := some 3
}

def minasTirithGarrison : CardDef := {
  name := "Minas Tirith Garrison"
  manaCost := ManaCost.ofGenericAndColor 3 .blue
  types := #[.creature]
  subtypes := #["Human", "Soldier"]
  oracleText := "Minas Tirith Garrison's power is equal to the number of cards in your hand.\nWhenever this creature attacks, you may tap any number of untapped Humans you control. Draw a card for each Human tapped this way."
  toughness := some 5
}

def colossalWhale : CardDef := {
  name := "Colossal Whale"
  manaCost := ManaCost.ofGenericAndColors 5 [.blue, .blue]
  types := #[.creature]
  subtypes := #["Whale"]
  oracleText := "Islandwalk (This creature can't be blocked as long as defending player controls an Island.)\nWhenever this creature attacks, you may exile target creature defending player controls until this creature leaves the battlefield. (That creature returns under its owner's control.)"
  power := some 5
  toughness := some 5
}

def willowWind : CardDef := {
  name := "Willow-Wind"
  manaCost := ManaCost.ofGenericAndColor 4 .blue
  types := #[.creature]
  subtypes := #["Elemental"]
  oracleText := "Flying\nWhen this creature enters, scry 2."
  power := some 3
  toughness := some 4
  keywords := { Keywords.none with flying := true }
}

def bilboLuckwearer : CardDef := {
  name := "Bilbo, Luckwearer"
  manaCost := ManaCost.ofGenericAndColor 1 .blue
  types := #[.creature]
  subtypes := #["Halfling", "Rogue"]
  supertypes := #[.legendary]
  oracleText := "Bilbo can't be blocked.\nWhenever Bilbo deals combat damage to a player, draw a card, then discard a card."
  power := some 1
  toughness := some 1
}

def uneasyPartings : CardDef := {
  name := "Uneasy Partings"
  manaCost := ManaCost.ofGenericAndColor 3 .blue
  types := #[.instant]
  oracleText := "This spell costs {1} less to cast if it targets an attacking nontoken creature.\nTarget creature's owner puts it on their choice of the top or bottom of their library."
}

def nimrodelWatcher : CardDef := {
  name := "Nimrodel Watcher"
  manaCost := ManaCost.ofGenericAndColor 1 .blue
  types := #[.creature]
  subtypes := #["Elf", "Scout"]
  oracleText := "Whenever you scry, this creature gets +1/+0 until end of turn and can't be blocked this turn. This ability triggers only once each turn."
  power := some 2
  toughness := some 1
}

def sternScolding : CardDef := {
  name := "Stern Scolding"
  manaCost := ManaCost.ofColor .blue
  types := #[.instant]
  oracleText := "Counter target creature spell with power or toughness 2 or less."
}

def frontPorchSentries : CardDef := {
  name := "Front Porch Sentries"
  manaCost := ManaCost.ofGenericAndColor 1 .black
  types := #[.creature]
  subtypes := #["Goblin", "Soldier"]
  oracleText := "When this creature dies, target creature an opponent controls gets -1/-1 until end of turn."
  power := some 2
  toughness := some 2
}

def greatFierceBee : CardDef := {
  name := "Great Fierce Bee"
  manaCost := ManaCost.ofGenericAndColor 2 .black
  types := #[.creature]
  subtypes := #["Insect"]
  oracleText := "Flying\nWhenever one or more other creatures die, scry 1. (Look at the top card of your library. You may put that card on the bottom.)"
  power := some 2
  toughness := some 2
  keywords := { Keywords.none with flying := true }
}

def stirUpTrouble : CardDef := {
  name := "Stir Up Trouble"
  manaCost := ManaCost.ofColor .black
  types := #[.sorcery]
  oracleText := "As an additional cost to cast this spell, sacrifice an artifact or creature or pay {4}.\nDestroy target creature."
}

def hauntOfTheDeadMarshes : CardDef := {
  name := "Haunt of the Dead Marshes"
  manaCost := ManaCost.ofColor .black
  types := #[.creature]
  subtypes := #["Nightmare", "Elf"]
  oracleText := "When this creature enters, scry 1.\n{2}{B}: Return this card from your graveyard to the battlefield tapped. Activate only if you control a legendary creature."
  power := some 1
  toughness := some 1
}

def desolationProwler : CardDef := {
  name := "Desolation Prowler"
  manaCost := ManaCost.ofGenericAndColor 1 .black
  types := #[.creature]
  subtypes := #["Wolf"]
  oracleText := "Pay 2 life: This creature gets +2/+2 until end of turn. Activate only once each turn."
  power := some 2
  toughness := some 2
}

def raveningWarg : CardDef := {
  name := "Ravening Warg"
  manaCost := ManaCost.ofGenericAndColor 1 .black
  types := #[.creature]
  subtypes := #["Wolf"]
  oracleText := "Deathtouch\nFerocious — Whenever this creature attacks while you control a creature with power 4 or greater, you gain 2 life."
  power := some 2
  toughness := some 2
  keywords := { Keywords.none with deathtouch := true }
}

def gollumSilentSlinker : CardDef := {
  name := "Gollum, Silent Slinker"
  manaCost := ManaCost.ofGenericAndColor 3 .black
  types := #[.creature]
  subtypes := #["Halfling", "Horror"]
  supertypes := #[.legendary]
  oracleText := "Menace (This creature can't be blocked except by two or more creatures.)"
  power := some 4
  toughness := some 3
}

def bilbosDeadlySlice : CardDef := {
  name := "Bilbo's Deadly Slice"
  manaCost := ManaCost.ofGenericAndColors 1 [.black, .black]
  types := #[.instant]
  oracleText := "Destroy target creature."
}

def dreadedBatCloud : CardDef := {
  name := "Dreaded Bat-Cloud"
  manaCost := ManaCost.ofGenericAndColor 4 .black
  types := #[.creature]
  subtypes := #["Bat"]
  oracleText := "This spell costs {3} less to cast if a creature died this turn.\nFlying, deathtouch"
  power := some 4
  toughness := some 2
  keywords := { Keywords.none with deathtouch := true, flying := true }
}

def crudeBentBlade : CardDef := {
  name := "Crude Bent Blade"
  manaCost := ManaCost.ofGenericAndColor 2 .black
  types := #[.artifact]
  subtypes := #["Equipment"]
  oracleText := "When this Equipment enters, target opponent sacrifices a creature of their choice.\nEquipped creature gets +2/+1.\nEquip {2} ({2}: Attach to target creature you control. Equip only as a sorcery.)"
}

def languish : CardDef := {
  name := "Languish"
  manaCost := ManaCost.ofGenericAndColors 2 [.black, .black]
  types := #[.sorcery]
  oracleText := "All creatures get -4/-4 until end of turn."
}

def shadowOfTheEnemy : CardDef := {
  name := "Shadow of the Enemy"
  manaCost := ManaCost.ofGenericAndColors 3 [.black, .black, .black]
  types := #[.sorcery]
  oracleText := "Exile all creature cards from target player's graveyard. You may cast spells from among those cards for as long as they remain exiled, and mana of any type can be spent to cast them."
}

def gollumTheAbandoned : CardDef := {
  name := "Gollum the Abandoned"
  manaCost := ManaCost.ofGenericAndColor 1 .black
  types := #[.creature]
  subtypes := #["Halfling", "Horror"]
  supertypes := #[.legendary]
  oracleText := "Gollum can't block.\nWhen Gollum enters, exile up to one target card from an opponent's graveyard. Each opponent loses 2 life.\n{2}, Sacrifice an artifact or creature: Return this card from your graveyard to your hand. Activate only as a sorcery."
  power := some 2
  toughness := some 2
}

def gnashingOfTeeth : CardDef := {
  name := "Gnashing of Teeth"
  manaCost := ManaCost.ofGenericAndColors 1 [.black, .black]
  types := #[.sorcery]
  oracleText := "Choose one —\n• Target creature gets -5/-5 until end of turn. If that creature would die this turn, exile it instead.\n• Creatures target player controls get -1/-1 until end of turn."
}

def trollOfKhazadDum : CardDef := {
  name := "Troll of Khazad-dûm"
  manaCost := ManaCost.ofGenericAndColor 5 .black
  types := #[.creature]
  subtypes := #["Troll"]
  oracleText := "This creature can't be blocked except by three or more creatures.\nSwampcycling {1} ({1}, Discard this card: Search your library for a Swamp card, reveal it, put it into your hand, then shuffle.)"
  power := some 6
  toughness := some 5
}

def mercilessExecutioner : CardDef := {
  name := "Merciless Executioner"
  manaCost := ManaCost.ofGenericAndColor 2 .black
  types := #[.creature]
  subtypes := #["Orc", "Warrior"]
  oracleText := "When this creature enters, each player sacrifices a creature of their choice."
  power := some 3
  toughness := some 1
}

def bitterDownfall : CardDef := {
  name := "Bitter Downfall"
  manaCost := ManaCost.ofGenericAndColor 3 .black
  types := #[.instant]
  oracleText := "This spell costs {3} less to cast if it targets a creature that was dealt damage this turn.\nDestroy target creature. Its controller loses 2 life."
}

def reverentHowl : CardDef := {
  name := "Reverent Howl"
  manaCost := ManaCost.ofGenericAndColor 2 .black
  types := #[.instant]
  oracleText := "Choose one —\n• Target player draws two cards and loses 2 life.\n• Target creature gets +2/+2 and gains lifelink until end of turn."
}

def nightsWhisper : CardDef := {
  name := "Night's Whisper"
  manaCost := ManaCost.ofGenericAndColor 1 .black
  types := #[.sorcery]
  oracleText := "You draw two cards and lose 2 life."
}

def stonyVoicedGoblins : CardDef := {
  name := "Stony-Voiced Goblins"
  manaCost := ManaCost.ofGenericAndColor 1 .black
  types := #[.creature]
  subtypes := #["Goblin", "Bard"]
  oracleText := "When this creature enters, each opponent discards a card."
  power := some 1
  toughness := some 1
}

def wayfarersBauble : CardDef := {
  name := "Wayfarer's Bauble"
  manaCost := ManaCost.ofGeneric 1
  types := #[.artifact]
  oracleText := "{2}, {T}, Sacrifice this artifact: Search your library for a basic land card, put that card onto the battlefield tapped, then shuffle."
  activatedAbilities := #[{
    cost := {
      mana := ManaCost.ofGeneric 2
      tap := true
      sacrificeSource := true
    }
    effect := .searchBasicLandTapped
  }]
}

def battleScarredGoblin : CardDef := {
  name := "Battle-Scarred Goblin"
  manaCost := ManaCost.ofGenericAndColor 1 .red
  types := #[.creature]
  subtypes := #["Goblin", "Warrior"]
  oracleText := "Whenever this creature becomes blocked, it deals 1 damage to each creature blocking it."
  power := some 2
  toughness := some 2
  triggeredAbilities := #[.onBecomesBlockedDeal1ToBlockers]
}

def improvisedClub : CardDef := {
  name := "Improvised Club"
  manaCost := ManaCost.ofGenericAndColor 1 .red
  types := #[.instant]
  oracleText := "As an additional cost to cast this spell, sacrifice an artifact or creature.\nImprovised Club deals 4 damage to any target."
}

def smaugTheGreatCalamity : CardDef := {
  name := "Smaug, the Great Calamity"
  manaCost := ManaCost.ofGenericAndColors 5 [.red, .red]
  types := #[.creature]
  subtypes := #["Dragon"]
  supertypes := #[.legendary]
  oracleText := "Flying\nSpew Flame {4}{R}\nSorcery — Adventure\nSpew Flame deals 5 damage to target creature. (Then exile this card. You may cast the creature later from exile.)"
  power := some 5
  toughness := some 5
  keywords := { Keywords.none with flying := true }
  adventure := some {
    name := "Spew Flame"
    manaCost := ManaCost.ofGenericAndColor 4 .red
    types := #[.sorcery]
    subtypes := #["Adventure"]
    oracleText := "Spew Flame deals 5 damage to target creature. (Then exile this card. You may cast the creature later from exile.)"
    spellEffect := some (.dealDamageToCreature 5)
  }
}

def ologHaiCrusher : CardDef := {
  name := "Olog-hai Crusher"
  manaCost := ManaCost.ofGenericAndColor 3 .red
  types := #[.creature]
  subtypes := #["Troll", "Soldier"]
  oracleText := "Trample\nThis creature can't block unless you control a Goblin or Orc."
  power := some 4
  toughness := some 4
  keywords := { Keywords.none with trample := true }
}

def gandalfSparkStarter : CardDef := {
  name := "Gandalf, Spark Starter"
  manaCost := ManaCost.ofGenericAndColors 4 [.red, .red]
  types := #[.creature]
  subtypes := #["Avatar", "Wizard"]
  supertypes := #[.legendary]
  oracleText := "Reach\nWhen Gandalf enters, he deals 3 damage divided as you choose among one, two, or three targets."
  power := some 4
  toughness := some 3
  keywords := { Keywords.none with reach := true }
  triggeredAbilities := #[.onEnterDealDividedDamage 3 3]
}

def raggedShortSpear : CardDef := {
  name := "Ragged Short Spear"
  manaCost := ManaCost.ofGenericAndColor 1 .red
  types := #[.artifact]
  subtypes := #["Equipment"]
  oracleText := "When this Equipment enters, you may discard a card. If you do, draw two cards.\nEquipped creature gets +2/+0.\nEquip {3} ({3}: Attach to target creature you control. Equip only as a sorcery.)"
  staticAbilities := #[.equippedCreatureGets 2 0]
  triggeredAbilities := #[.onEnterMayDiscardDraw 2]
  activatedAbilities := #[{
    cost := { mana := ManaCost.ofGeneric 3 }
    effect := .attachToTargetCreatureYouControl
    onlyAsSorcery := true
  }]
}

def smiteTheDeathless : CardDef := {
  name := "Smite the Deathless"
  manaCost := ManaCost.ofGenericAndColor 1 .red
  types := #[.instant]
  oracleText := "Smite the Deathless deals 3 damage to target creature. That creature loses indestructible until end of turn. If that creature would die this turn, exile it instead."
  spellEffect := some (.dealDamage 3)
}

def goblinFireleaper : CardDef := {
  name := "Goblin Fireleaper"
  manaCost := ManaCost.ofGenericAndColor 1 .red
  types := #[.creature]
  subtypes := #["Goblin", "Warrior"]
  oracleText := "{1}{R}: This creature gets +1/+0 until end of turn.\nWhen this creature dies, it deals damage equal to its power to target creature an opponent controls."
  power := some 1
  toughness := some 1
  activatedAbilities := #[{
    cost := { mana := ManaCost.ofGenericAndColor 1 .red }
    effect := .sourceGets 1 0
  }]
  triggeredAbilities := #[.onDiesDealDamageEqualToPowerToOppCreature]
}

def oliphaunt : CardDef := {
  name := "Oliphaunt"
  manaCost := ManaCost.ofGenericAndColor 5 .red
  types := #[.creature]
  subtypes := #["Elephant"]
  oracleText := "Trample\nWhenever this creature attacks, another target creature you control gets +2/+0 and gains trample until end of turn.\nMountaincycling {1} ({1}, Discard this card: Search your library for a Mountain card, reveal it, put it into your hand, then shuffle.)"
  power := some 6
  toughness := some 4
  keywords := { Keywords.none with trample := true }
}

def goblinCratermaker : CardDef := {
  name := "Goblin Cratermaker"
  manaCost := ManaCost.ofGenericAndColor 1 .red
  types := #[.creature]
  subtypes := #["Goblin", "Warrior"]
  oracleText := "{1}, Sacrifice this creature: Choose one —\n• This creature deals 2 damage to target creature.\n• Destroy target colorless nonland permanent."
  power := some 2
  toughness := some 2
  activatedAbilities := #[{
    cost := { mana := ManaCost.ofGeneric 1, sacrificeSource := true }
    effect := .dealDamageToTargetCreature 2
    otherModes := #[.destroyTargetColorlessNonland]
  }]
}

def infernoTitan : CardDef := {
  name := "Inferno Titan"
  manaCost := ManaCost.ofGenericAndColors 4 [.red, .red]
  types := #[.creature]
  subtypes := #["Giant"]
  oracleText := "{R}: This creature gets +1/+0 until end of turn.\nWhenever this creature enters or attacks, it deals 3 damage divided as you choose among one, two, or three targets."
  power := some 6
  toughness := some 6
}

def guttersnipe : CardDef := {
  name := "Guttersnipe"
  manaCost := ManaCost.ofGenericAndColor 2 .red
  types := #[.creature]
  subtypes := #["Goblin", "Shaman"]
  oracleText := "Whenever you cast an instant or sorcery spell, this creature deals 2 damage to each opponent."
  power := some 2
  toughness := some 2
}

def orcishSiegemaster : CardDef := {
  name := "Orcish Siegemaster"
  manaCost := ManaCost.ofGenericAndColor 2 .red
  types := #[.creature]
  subtypes := #["Orc", "Soldier"]
  oracleText := "Trample\nOther Orcs and Goblins you control have trample.\nWhenever this creature attacks, it gets +X/+0 until end of turn, where X is the greatest power among creatures you control."
  power := some 0
  toughness := some 5
  keywords := { Keywords.none with trample := true }
  staticAbilities := #[.otherCreaturesHaveTrample #["Orc", "Goblin"]]
  triggeredAbilities := #[.onAttackPumpByGreatestPower]
}

def snowslopeHunter : CardDef := {
  name := "Snowslope Hunter"
  manaCost := ManaCost.ofGenericAndColor 2 .red
  types := #[.creature]
  subtypes := #["Goblin", "Ranger"]
  oracleText := "Sacrifice another creature or artifact: Exile the top card of your library. You may play it until the end of your next turn. Activate only during your turn and only once each turn."
  power := some 2
  toughness := some 3
  activatedAbilities := #[{
    cost := { sacrificeAnotherCreatureOrArtifact := true }
    effect := .exileTopPlayUntilEndOfNextTurn
    onlyDuringYourTurn := true
    onceEachTurn := true
  }]
}

def fireOfOrthanc : CardDef := {
  name := "Fire of Orthanc"
  manaCost := ManaCost.ofGenericAndColor 3 .red
  types := #[.sorcery]
  oracleText := "Destroy target artifact or land. Creatures without flying can't block this turn."
}

def guardianOfTheHalls : CardDef := {
  name := "Guardian of the Halls"
  manaCost := ManaCost.ofGenericAndColor 1 .green
  types := #[.creature]
  subtypes := #["Elf", "Soldier"]
  oracleText := "Trample\n{5}{G}{G}: Put three +1/+1 counters on this creature."
  power := some 2
  toughness := some 2
  keywords := { Keywords.none with trample := true }
}

def quarrel : CardDef := {
  name := "Quarrel"
  manaCost := ManaCost.ofGenericAndColor 1 .green
  types := #[.instant]
  oracleText := "Target creature you control deals damage equal to its power to target creature an opponent controls."
}

def galadhrimGuide : CardDef := {
  name := "Galadhrim Guide"
  manaCost := ManaCost.ofGenericAndColor 3 .green
  types := #[.creature]
  subtypes := #["Elf", "Scout"]
  oracleText := "When this creature enters, scry 2."
  power := some 3
  toughness := some 4
  triggeredAbilities := #[.onEnterScry 2]
}

def galionElvenkingsButler : CardDef := {
  name := "Galion, Elvenking's Butler"
  manaCost := ManaCost.ofGenericAndColors 2 [.green, .green]
  types := #[.creature]
  subtypes := #["Elf", "Advisor"]
  supertypes := #[.legendary]
  oracleText := "Whenever Galion attacks, choose up to one other target creature you control. Its base power and toughness become equal to Galion's power and toughness until end of turn."
  power := some 4
  toughness := some 4
  triggeredAbilities := #[.onAttackSetOtherBasePT]
}

def elvishVisionary : CardDef := {
  name := "Elvish Visionary"
  manaCost := ManaCost.ofGenericAndColor 1 .green
  types := #[.creature]
  subtypes := #["Elf", "Shaman"]
  oracleText := "When this creature enters, draw a card."
  power := some 1
  toughness := some 1
}

def wargTactics : CardDef := {
  name := "Warg Tactics"
  manaCost := ManaCost.ofGenericAndColor 1 .green
  types := #[.instant]
  oracleText := "Choose one —\n• Destroy target creature with flying.\n• Put a +1/+1 counter on target creature you control. It gains trample and hexproof until end of turn. (It can't be the target of spells or abilities your opponents control.)"
  spellModes := #[.destroyCreatureWithFlying, .plusOnePlusOneTrampleHexproof]
}

def beornsHospitality : CardDef := {
  name := "Beorn's Hospitality"
  manaCost := ManaCost.ofGenericAndColor 1 .green
  types := #[.enchantment]
  oracleText := "Landfall — Whenever a land you control enters, put a +1/+1 counter on target creature you control.\n{5}{G}{G}: This enchantment becomes a Bear creature in addition to its other types and gains \"This creature's power and toughness are each equal to the number of lands you control.\" (This effect doesn't end.)"
  triggeredAbilities := #[.onLandYouControlEntersPlusOnePlusOne]
  activatedAbilities := #[{
    cost := { mana := ManaCost.ofGenericAndColors 5 [.green, .green] }
    effect := .becomeBearCreatureWithLandsPT
  }]
}

def mirkwoodElk : CardDef := {
  name := "Mirkwood Elk"
  manaCost := ManaCost.ofGenericAndColor 5 .green
  types := #[.creature]
  subtypes := #["Elk"]
  oracleText := "Trample\nWhenever this creature enters or attacks, return target Elf card from your graveyard to your hand. You gain life equal to that card's power."
  power := some 6
  toughness := some 6
  keywords := { Keywords.none with trample := true }
}

def celebornTheWise : CardDef := {
  name := "Celeborn the Wise"
  manaCost := ManaCost.ofGenericAndColor 3 .green
  types := #[.creature]
  subtypes := #["Elf", "Noble"]
  supertypes := #[.legendary]
  oracleText := "Whenever you attack with one or more Elves, scry 1.\nWhenever you scry, Celeborn gets +1/+1 until end of turn for each card looked at while scrying this way."
  power := some 3
  toughness := some 3
}

def giftOfStrands : CardDef := {
  name := "Gift of Strands"
  manaCost := ManaCost.ofGenericAndColor 3 .green
  types := #[.enchantment]
  subtypes := #["Aura"]
  oracleText := "Flash\nEnchant creature\nWhen this Aura enters, scry 2.\nEnchanted creature gets +3/+3."
  keywords := { Keywords.none with flash := true }
  staticAbilities := #[.enchantedCreatureGets 3 3]
  triggeredAbilities := #[.onEnterScry 2]
}

def elvishArchdruid : CardDef := {
  name := "Elvish Archdruid"
  manaCost := ManaCost.ofGenericAndColors 1 [.green, .green]
  types := #[.creature]
  subtypes := #["Elf", "Druid"]
  oracleText := "Other Elf creatures you control get +1/+1.\n{T}: Add {G} for each Elf you control."
  power := some 2
  toughness := some 2
}

def lothlorienLookout : CardDef := {
  name := "Lothlórien Lookout"
  manaCost := ManaCost.ofGenericAndColor 1 .green
  types := #[.creature]
  subtypes := #["Elf", "Scout"]
  oracleText := "Whenever this creature attacks, scry 1."
  power := some 1
  toughness := some 3
}

def woodlandWeavemaster : CardDef := {
  name := "Woodland Weavemaster"
  manaCost := ManaCost.ofGenericAndColor 1 .green
  types := #[.creature]
  subtypes := #["Elf", "Druid"]
  oracleText := "Vigilance\nWhenever another Elf you control enters, this creature gets +1/+1 until end of turn.\n{T}: Add X mana of any one color, where X is this creature's power. Spend this mana only to cast Elf spells and activate abilities of Elf sources."
  power := some 1
  toughness := some 2
}

def mirkwoodPathmaker : CardDef := {
  name := "Mirkwood Pathmaker"
  manaCost := ManaCost.ofGenericAndColor 2 .green
  types := #[.creature]
  subtypes := #["Elf", "Ranger"]
  oracleText := "Mirkwood Pathmaker's power and toughness are each equal to the number of lands you control."
  staticAbilities := #[.powerToughnessEqualLandsYouControl]
}

def beornReluctantHost : CardDef := {
  name := "Beorn, Reluctant Host"
  manaCost := ManaCost.ofGenericAndColor 4 .green
  types := #[.creature]
  subtypes := #["Human", "Bear", "Shapeshifter"]
  supertypes := #[.legendary]
  oracleText := "Trample"
  power := some 5
  toughness := some 5
  keywords := { Keywords.none with trample := true }
}

def woodElves : CardDef := {
  name := "Wood Elves"
  manaCost := ManaCost.ofGenericAndColor 2 .green
  types := #[.creature]
  subtypes := #["Elf", "Scout"]
  oracleText := "When this creature enters, search your library for a Forest card, put that card onto the battlefield, then shuffle."
  power := some 1
  toughness := some 1
}

def elvishMystic : CardDef := {
  name := "Elvish Mystic"
  manaCost := ManaCost.ofColor .green
  types := #[.creature]
  subtypes := #["Elf", "Druid"]
  oracleText := "{T}: Add {G}."
  power := some 1
  toughness := some 1
  tapAddMana := #[.colored .green]
}

def attercop : CardDef := {
  name := "Attercop"
  manaCost := ManaCost.ofGenericAndColor 1 .green
  types := #[.creature]
  subtypes := #["Spider"]
  oracleText := "Reach, deathtouch\nLandfall — Whenever a land you control enters, this creature gets +1/+1 until end of turn."
  power := some 2
  toughness := some 1
  keywords := { Keywords.none with reach := true, deathtouch := true }
}

#guard bofurReliableGuardian.colors.isMonocolored
#guard roguesPassage.isLand
#guard elvishMystic.tapAddMana == #[.colored .green]
#guard (attercop.summary.splitOn "Landfall").length > 1
#guard (attercop.summary.splitOn "reach").length > 1
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
#guard raggedShortSpear.isEquipment
#guard !raggedShortSpear.isAura
#guard !raggedShortSpear.requiresTarget
#guard raggedShortSpear.staticAbilities == #[.equippedCreatureGets 2 0]
#guard raggedShortSpear.triggeredAbilities == #[.onEnterMayDiscardDraw 2]
#guard raggedShortSpear.activatedAbilities.size == 1
#guard raggedShortSpear.activatedAbilities[0]!.onlyAsSorcery
#guard raggedShortSpear.activatedAbilities[0]!.effect == .attachToTargetCreatureYouControl
#guard raggedShortSpear.activatedAbilities[0]!.cost.mana == ManaCost.ofGeneric 3
#guard (raggedShortSpear.summary.splitOn "Equipped creature").length > 1
#guard (giftOfStrands.summary.splitOn "flash").length > 1
#guard (giftOfStrands.summary.splitOn "Enchanted creature").length > 1
#guard galadhrimGuide.triggeredAbilities == #[.onEnterScry 2]
#guard (galadhrimGuide.summary.splitOn "scry 2").length > 1
#guard galionElvenkingsButler.triggeredAbilities == #[.onAttackSetOtherBasePT]
#guard (galionElvenkingsButler.summary.splitOn "base power and toughness").length > 1
#guard galionElvenkingsButler.power == some 4
#guard galionElvenkingsButler.toughness == some 4
#guard galadhrimGuide.power == some 3
#guard galadhrimGuide.toughness == some 4
#guard goblinCratermaker.activatedAbilities.size == 1
#guard goblinCratermaker.activatedAbilities[0]!.cost.sacrificeSource
#guard goblinCratermaker.activatedAbilities[0]!.cost.mana == ManaCost.ofGeneric 1
#guard goblinCratermaker.activatedAbilities[0]!.isModal
#guard goblinCratermaker.activatedAbilities[0]!.effect == .dealDamageToTargetCreature 2
#guard goblinCratermaker.activatedAbilities[0]!.otherModes ==
  #[.destroyTargetColorlessNonland]
#guard (goblinCratermaker.summary.splitOn "Choose one").length > 1
#guard (goblinCratermaker.summary.splitOn "colorless nonland").length > 1
#guard wargTactics.isInstant
#guard wargTactics.isModal
#guard wargTactics.requiresTarget
#guard wargTactics.spellModes == #[
  .destroyCreatureWithFlying,
  .plusOnePlusOneTrampleHexproof]
#guard (wargTactics.summary.splitOn "Choose one").length > 1
#guard (wargTactics.summary.splitOn "hexproof").length > 1
#guard beornsHospitality.isEnchantment
#guard !beornsHospitality.isCreature
#guard beornsHospitality.triggeredAbilities == #[.onLandYouControlEntersPlusOnePlusOne]
#guard beornsHospitality.activatedAbilities.size == 1
#guard beornsHospitality.activatedAbilities[0]!.effect == .becomeBearCreatureWithLandsPT
#guard beornsHospitality.activatedAbilities[0]!.cost.mana ==
  ManaCost.ofGenericAndColors 5 [.green, .green]
#guard (beornsHospitality.summary.splitOn "Landfall").length > 1
#guard (beornsHospitality.summary.splitOn "Bear creature").length > 1
#guard mirkwoodPathmaker.staticAbilities == #[.powerToughnessEqualLandsYouControl]
#guard (mirkwoodPathmaker.summary.splitOn "lands you control").length > 1
#guard gandalfSparkStarter.keywords.reach
#guard gandalfSparkStarter.triggeredAbilities == #[.onEnterDealDividedDamage 3 3]
#guard (gandalfSparkStarter.summary.splitOn "divided as you choose").length > 1
#guard (gandalfSparkStarter.summary.splitOn "reach").length > 1
#guard goblinFireleaper.activatedAbilities.size == 1
#guard goblinFireleaper.activatedAbilities[0]!.effect == .sourceGets 1 0
#guard goblinFireleaper.activatedAbilities[0]!.cost.mana == ManaCost.ofGenericAndColor 1 .red
#guard goblinFireleaper.triggeredAbilities == #[.onDiesDealDamageEqualToPowerToOppCreature]
#guard (goblinFireleaper.summary.splitOn "+1/+0").length > 1
#guard (goblinFireleaper.summary.splitOn "dies").length > 1
#guard smaugTheGreatCalamity.keywords.flying
#guard smaugTheGreatCalamity.hasAdventure
#guard smaugTheGreatCalamity.supertypes.any (· == .legendary)
#guard smaugTheGreatCalamity.power == some 5
#guard smaugTheGreatCalamity.toughness == some 5
#guard
  match smaugTheGreatCalamity.adventure with
  | some adv =>
    adv.name == "Spew Flame" &&
      adv.manaCost == ManaCost.ofGenericAndColor 4 .red &&
      adv.types == #[.sorcery] &&
      adv.subtypes.any (· == "Adventure") &&
      adv.spellEffect == some (.dealDamageToCreature 5)
  | none => false
#guard (smaugTheGreatCalamity.summary.splitOn "Spew Flame").length > 1
#guard (smaugTheGreatCalamity.summary.splitOn "flying").length > 1

end Mtg.Engine.Catalog
