import Mtg.Engine.Card
import Mtg.Engine.Catalog

/-!
# The Hobbit catalog

Oracle characteristics for cards that appear in the Magic: The Gathering |
The Hobbit Welcome Decks. The engine models a subset of rules text
(keywords including flash, hexproof, vigilance, and deathtouch, simple `{T}: Add` mana abilities, `{T}: Add`
for each permanent of a listed type, `{T}: Add` X mana of any color equal to power
with an Elf-only spending restriction, non-mana
activated abilities such as Wayfarer's Bauble, Snowslope Hunter, Goblin
Cratermaker, Goblin Fireleaper, Inferno Titan, Guardian of the Halls, Rogue's Passage, Equip, and paying life for an until-end-of-turn pump (Desolation Prowler), static abilities that grant trample, pump other creatures of listed types, pump an enchanted
or equipped creature, or restrict blocking unless you control certain creature
types, attack triggers that pump, set another creature's base
power and toughness, give another creature +2/+0 and trample, scry, deal damage
divided among targets, scry when you attack with Elves, or gain life while you
control a creature with power 4 or greater (Ferocious), scry triggers that
pump for each card looked at, becomes-blocked triggers that
damage blockers, dies triggers that deal last-known power, enters triggers that scry, draw a card, search for a Forest card, may discard to draw, or deal damage
divided among targets (including whenever the creature enters or attacks),
returning an Elf from the graveyard and gaining life equal to its power,
another Elf you control entering that pumps this creature,
landfall that pumps this creature until end of turn,
Aura and Equipment attachment, adventurer cards
(casting an Adventure, then the creature from exile, including additional land
plays this turn), modal spells, destroy (including target artifact or land,
after which creatures without flying can't block this turn), +1/+1
counters, until-end-of-turn keyword grants, additional costs that sacrifice an
artifact or creature, a creature you control dealing damage equal to its power
to a creature an opponent controls, dealing damage that also makes a creature
lose indestructible and exile it if it would die this turn, drawing cards and
losing life, and a few one-shot spell effects);
remaining abilities are stored as Oracle text only.

Source: https://magic.wizards.com/en/news/announcements/the-hobbit-welcome-decks
-/

namespace Mtg.Engine.Catalog

open Mtg.Engine

def bofurReliableGuardian : CardDef :=
  creature "Bofur, Reliable Guardian" (ManaCost.ofColor .white) #["Dwarf", "Scout"] 1 1
    (oracleText := "Lifelink")
    (supertypes := #[.legendary])

def dwarvenProvisioner : CardDef :=
  creature "Dwarven Provisioner" (ManaCost.ofGenericAndColor 1 .white) #["Dwarf", "Citizen"] 2 2
    (oracleText := "{3}{W}: Creatures you control get +1/+1 until end of turn.")

def velvetwingButterflies : CardDef :=
  creature "Velvetwing Butterflies" (ManaCost.ofGenericAndColor 2 .white) #["Insect"] 2 2
    (oracleText := "Flying")
    (keywords := Keyword.flying)

def magnificentEnd : CardDef :=
  instant "Magnificent End" (ManaCost.ofGenericAndColor 4 .white)
    "This spell costs {3} less to cast if it targets a tapped creature.\nMagnificent End deals 5 damage to target creature."
    (some (.dealDamage 5))

def mentorOfTheMeek : CardDef :=
  creature "Mentor of the Meek" (ManaCost.ofGenericAndColor 2 .white) #["Human", "Soldier"] 2 2
    (oracleText := "Whenever another creature you control with power 2 or less enters, you may pay {1}. If you do, draw a card.")

def fiendHunter : CardDef :=
  creature "Fiend Hunter" (ManaCost.ofGenericAndColors 1 [.white, .white]) #["Human", "Cleric"] 1 3
    (oracleText := "When this creature enters, you may exile another target creature.\nWhen this creature leaves the battlefield, return the exiled card to the battlefield under its owner's control.")

def errandRiderOfGondor : CardDef :=
  creature "Errand-Rider of Gondor" (ManaCost.ofGenericAndColor 2 .white) #["Human", "Soldier"] 3 2
    (oracleText := "When this creature enters, draw a card. Then if you don't control a legendary creature, put a card from your hand on the bottom of your library.")

def landrovalHorizonWitness : CardDef :=
  creature "Landroval, Horizon Witness" (ManaCost.ofGenericAndColor 4 .white) #["Bird", "Noble"] 3 4
    (oracleText := "Flying\nWhenever two or more creatures you control attack a player, target attacking creature without flying gains flying until end of turn.")
    (supertypes := #[.legendary])
    (keywords := Keyword.flying)

def roguesPassage : CardDef :=
  land "Rogue's Passage"
    "{T}: Add {C}.\n{4}, {T}: Target creature can't be blocked this turn."
    (tapAddMana := #[.colorless])
    (activatedAbilities := #[
      activated .targetCantBeBlockedThisTurn (ManaCost.ofGeneric 4) (tap := true)])

def soldierOfTheGreyHost : CardDef :=
  creature "Soldier of the Grey Host" (ManaCost.ofGenericAndColor 3 .white) #["Spirit", "Soldier"] 2 2
    (oracleText := "Flash\nFlying\nWhen this creature enters, target creature gets +2/+0 until end of turn.")
    (keywords := Keyword.flying)

def eaglesOfTheNorth : CardDef :=
  creature "Eagles of the North" (ManaCost.ofGenericAndColor 5 .white) #["Bird", "Soldier"] 3 3
    (oracleText := "Flying\nWhen this creature enters, creatures you control get +1/+0 and gain first strike until end of turn.\nPlainscycling {1} ({1}, Discard this card: Search your library for a Plains card, reveal it, put it into your hand, then shuffle.)")
    (keywords := Keyword.flying)

def dunedainBlade : CardDef :=
  artifact "Dúnedain Blade" (ManaCost.ofGenericAndColor 1 .white)
    "Equipped creature gets +2/+1.\nEquip Human {1}\nEquip {3} ({3}: Attach to target creature you control. Equip only as a sorcery.)"
    (subtypes := #["Equipment"])

def fogOnTheBarrowDowns : CardDef :=
  aura "Fog on the Barrow-Downs" (ManaCost.ofGenericAndColor 2 .white)
    "Enchant creature\nEnchanted creature is a Spirit and can't attack or block. (It loses all other creature types.)"

def eagleOfTheGreatShelf : CardDef :=
  creature "Eagle of the Great Shelf" (ManaCost.ofGenericAndColor 4 .white) #["Bird", "Soldier"] 2 5
    (oracleText := "Flying\nWhenever this creature attacks, it gets +1/+1 until end of turn for each other creature you control.")
    (keywords := Keyword.flying)

def banishingLight : CardDef :=
  enchantment "Banishing Light" (ManaCost.ofGenericAndColor 2 .white)
    "When this enchantment enters, exile target nonland permanent an opponent controls until this enchantment leaves the battlefield."

def dawnOfANewAge : CardDef :=
  enchantment "Dawn of a New Age" (ManaCost.ofGenericAndColor 1 .white)
    "This enchantment enters with a hope counter on it for each creature you control.\nAt the beginning of your end step, remove a hope counter from this enchantment. If you do, draw a card. Then if this enchantment has no hope counters on it, sacrifice it and you gain 4 life."

def vowToErebor : CardDef :=
  instant "Vow to Erebor" (ManaCost.ofGenericAndColor 1 .white)
    "Untap target creature you control. It gets +2/+2 until end of turn. If it's a Dwarf, you may attach an Equipment you control to it."
    (some (.pump 2 2))

def westfoldRider : CardDef :=
  creature "Westfold Rider" (ManaCost.ofGenericAndColor 1 .white) #["Human", "Knight"] 3 1
    (oracleText := "Sacrifice this creature: Destroy target artifact or enchantment. Activate only as a sorcery.")

def esquireOfTheKing : CardDef :=
  creature "Esquire of the King" (ManaCost.ofColor .white) #["Human", "Soldier"] 1 1
    (oracleText := "{4}{W}, {T}: Creatures you control get +1/+1 until end of turn. This ability costs {2} less to activate if you control a legendary creature.")

def bilboBagginsBurglar : CardDef :=
  creature "Bilbo Baggins, Burglar" (ManaCost.ofGenericAndColor 2 .blue) #["Halfling", "Rogue"] 2 1
    (oracleText := "When Bilbo Baggins enters, draw a card.")
    (supertypes := #[.legendary])

def pelargirSurvivor : CardDef :=
  creature "Pelargir Survivor" (ManaCost.ofGenericAndColor 1 .blue) #["Human", "Peasant"] 1 3
    (oracleText := "{T}: Add one mana of any color. Spend this mana only to cast an instant or sorcery spell.\n{5}{U}, {T}: Target player mills three cards. (They put the top three cards of their library into their graveyard.)")

def lakeshoreApothecary : CardDef :=
  creature "Lakeshore Apothecary" (ManaCost.ofGenericAndColor 1 .blue) #["Human", "Cleric"] 1 2
    (oracleText := "Vigilance\nWhenever you draw your second card each turn, put a +1/+1 counter on this creature.")

def confusticateAndBebother : CardDef :=
  instant "Confusticate and Bebother" (ManaCost.ofGenericAndColor 2 .blue)
    "Choose one —\n• Counter target spell unless its controller pays {4}.\n• Draw two cards, then discard a card."

def ravenhillFlock : CardDef :=
  creature "Ravenhill Flock" (ManaCost.ofGenericAndColor 3 .blue) #["Bird"] 1 2
    (oracleText := "Flying\nWhenever you draw a card, put a +1/+1 counter on this creature.")
    (keywords := Keyword.flying)

def lorienRevealed : CardDef :=
  sorcery "Lórien Revealed" (ManaCost.ofGenericAndColors 3 [.blue, .blue])
    "Draw three cards.\nIslandcycling {1} ({1}, Discard this card: Search your library for an Island card, reveal it, put it into your hand, then shuffle.)"

def thranduilsDecree : CardDef :=
  instant "Thranduil's Decree" (ManaCost.ofGenericAndColors 4 [.blue, .blue])
    "Counter target spell. If a permanent spell is countered this way, exile it instead of putting it into its owner's graveyard. You may cast that card without paying its mana cost for as long as it remains exiled."

def knightsOfDolAmroth : CardDef :=
  creature "Knights of Dol Amroth" (ManaCost.ofGenericAndColor 3 .blue) #["Human", "Knight"] 3 3
    (oracleText := "Whenever you draw your second card each turn, put a +1/+1 counter on this creature.")

def greyHavensNavigator : CardDef :=
  creature "Grey Havens Navigator" (ManaCost.ofGenericAndColor 2 .blue) #["Elf", "Pilot"] 3 2
    (oracleText := "Flash\nWhen this creature enters, scry 1.")

def ithilienKingfisher : CardDef :=
  creature "Ithilien Kingfisher" (ManaCost.ofGenericAndColor 2 .blue) #["Bird"] 2 1
    (oracleText := "Flying\nWhen this creature dies, draw a card.")
    (keywords := Keyword.flying)

def hithlainKnots : CardDef :=
  instant "Hithlain Knots" (ManaCost.ofGenericAndColor 1 .blue)
    "Tap target creature. Scry 1.\nDraw a card."

def captainOfUmbar : CardDef :=
  creature "Captain of Umbar" (ManaCost.ofGenericAndColor 2 .blue) #["Human", "Pirate"] 2 3
    (oracleText := "{1}, {T}: Draw a card, then discard a card.")

def minasTirithGarrison : CardDef :=
  card "Minas Tirith Garrison" #[.creature] (ManaCost.ofGenericAndColor 3 .blue) #["Human", "Soldier"]
    "Minas Tirith Garrison's power is equal to the number of cards in your hand.\nWhenever this creature attacks, you may tap any number of untapped Humans you control. Draw a card for each Human tapped this way."
    (toughness := some 5)

def colossalWhale : CardDef :=
  creature "Colossal Whale" (ManaCost.ofGenericAndColors 5 [.blue, .blue]) #["Whale"] 5 5
    (oracleText := "Islandwalk (This creature can't be blocked as long as defending player controls an Island.)\nWhenever this creature attacks, you may exile target creature defending player controls until this creature leaves the battlefield. (That creature returns under its owner's control.)")

def willowWind : CardDef :=
  creature "Willow-Wind" (ManaCost.ofGenericAndColor 4 .blue) #["Elemental"] 3 4
    (oracleText := "Flying\nWhen this creature enters, scry 2.")
    (keywords := Keyword.flying)

def bilboLuckwearer : CardDef :=
  creature "Bilbo, Luckwearer" (ManaCost.ofGenericAndColor 1 .blue) #["Halfling", "Rogue"] 1 1
    (oracleText := "Bilbo can't be blocked.\nWhenever Bilbo deals combat damage to a player, draw a card, then discard a card.")
    (supertypes := #[.legendary])

def uneasyPartings : CardDef :=
  instant "Uneasy Partings" (ManaCost.ofGenericAndColor 3 .blue)
    "This spell costs {1} less to cast if it targets an attacking nontoken creature.\nTarget creature's owner puts it on their choice of the top or bottom of their library."

def nimrodelWatcher : CardDef :=
  creature "Nimrodel Watcher" (ManaCost.ofGenericAndColor 1 .blue) #["Elf", "Scout"] 2 1
    (oracleText := "Whenever you scry, this creature gets +1/+0 until end of turn and can't be blocked this turn. This ability triggers only once each turn.")

def sternScolding : CardDef :=
  instant "Stern Scolding" (ManaCost.ofColor .blue)
    "Counter target creature spell with power or toughness 2 or less."

def frontPorchSentries : CardDef :=
  creature "Front Porch Sentries" (ManaCost.ofGenericAndColor 1 .black) #["Goblin", "Soldier"] 2 2
    (oracleText := "When this creature dies, target creature an opponent controls gets -1/-1 until end of turn.")

def greatFierceBee : CardDef :=
  creature "Great Fierce Bee" (ManaCost.ofGenericAndColor 2 .black) #["Insect"] 2 2
    (oracleText := "Flying\nWhenever one or more other creatures die, scry 1. (Look at the top card of your library. You may put that card on the bottom.)")
    (keywords := Keyword.flying)

def stirUpTrouble : CardDef :=
  sorcery "Stir Up Trouble" (ManaCost.ofColor .black)
    "As an additional cost to cast this spell, sacrifice an artifact or creature or pay {4}.\nDestroy target creature."

def hauntOfTheDeadMarshes : CardDef :=
  creature "Haunt of the Dead Marshes" (ManaCost.ofColor .black) #["Nightmare", "Elf"] 1 1
    (oracleText := "When this creature enters, scry 1.\n{2}{B}: Return this card from your graveyard to the battlefield tapped. Activate only if you control a legendary creature.")

def desolationProwler : CardDef :=
  creature "Desolation Prowler" (ManaCost.ofGenericAndColor 1 .black) #["Wolf"] 2 2
    (oracleText := "Pay 2 life: This creature gets +2/+2 until end of turn. Activate only once each turn.")
    (activatedAbilities := #[
      activated (.sourceGets 2 2) (payLife := 2) (onceEachTurn := true)])

def raveningWarg : CardDef :=
  creature "Ravening Warg" (ManaCost.ofGenericAndColor 1 .black) #["Wolf"] 2 2
    (oracleText := "Deathtouch\nFerocious — Whenever this creature attacks while you control a creature with power 4 or greater, you gain 2 life.")
    (keywords := Keyword.deathtouch)
    (triggeredAbilities := #[.onAttackFerociousGainLife 2])

def gollumSilentSlinker : CardDef :=
  creature "Gollum, Silent Slinker" (ManaCost.ofGenericAndColor 3 .black) #["Halfling", "Horror"] 4 3
    (oracleText := "Menace (This creature can't be blocked except by two or more creatures.)")
    (supertypes := #[.legendary])

def bilbosDeadlySlice : CardDef :=
  instant "Bilbo's Deadly Slice" (ManaCost.ofGenericAndColors 1 [.black, .black])
    "Destroy target creature."

def dreadedBatCloud : CardDef :=
  creature "Dreaded Bat-Cloud" (ManaCost.ofGenericAndColor 4 .black) #["Bat"] 4 2
    (oracleText := "This spell costs {3} less to cast if a creature died this turn.\nFlying, deathtouch")
    (keywords := Keyword.deathtouch.merge Keyword.flying)

def crudeBentBlade : CardDef :=
  artifact "Crude Bent Blade" (ManaCost.ofGenericAndColor 2 .black)
    "When this Equipment enters, target opponent sacrifices a creature of their choice.\nEquipped creature gets +2/+1.\nEquip {2} ({2}: Attach to target creature you control. Equip only as a sorcery.)"
    (subtypes := #["Equipment"])

def languish : CardDef :=
  sorcery "Languish" (ManaCost.ofGenericAndColors 2 [.black, .black])
    "All creatures get -4/-4 until end of turn."

def shadowOfTheEnemy : CardDef :=
  sorcery "Shadow of the Enemy" (ManaCost.ofGenericAndColors 3 [.black, .black, .black])
    "Exile all creature cards from target player's graveyard. You may cast spells from among those cards for as long as they remain exiled, and mana of any type can be spent to cast them."

def gollumTheAbandoned : CardDef :=
  creature "Gollum the Abandoned" (ManaCost.ofGenericAndColor 1 .black) #["Halfling", "Horror"] 2 2
    (oracleText := "Gollum can't block.\nWhen Gollum enters, exile up to one target card from an opponent's graveyard. Each opponent loses 2 life.\n{2}, Sacrifice an artifact or creature: Return this card from your graveyard to your hand. Activate only as a sorcery.")
    (supertypes := #[.legendary])

def gnashingOfTeeth : CardDef :=
  sorcery "Gnashing of Teeth" (ManaCost.ofGenericAndColors 1 [.black, .black])
    "Choose one —\n• Target creature gets -5/-5 until end of turn. If that creature would die this turn, exile it instead.\n• Creatures target player controls get -1/-1 until end of turn."

def trollOfKhazadDum : CardDef :=
  creature "Troll of Khazad-dûm" (ManaCost.ofGenericAndColor 5 .black) #["Troll"] 6 5
    (oracleText := "This creature can't be blocked except by three or more creatures.\nSwampcycling {1} ({1}, Discard this card: Search your library for a Swamp card, reveal it, put it into your hand, then shuffle.)")

def mercilessExecutioner : CardDef :=
  creature "Merciless Executioner" (ManaCost.ofGenericAndColor 2 .black) #["Orc", "Warrior"] 3 1
    (oracleText := "When this creature enters, each player sacrifices a creature of their choice.")

def bitterDownfall : CardDef :=
  instant "Bitter Downfall" (ManaCost.ofGenericAndColor 3 .black)
    "This spell costs {3} less to cast if it targets a creature that was dealt damage this turn.\nDestroy target creature. Its controller loses 2 life."

def reverentHowl : CardDef :=
  instant "Reverent Howl" (ManaCost.ofGenericAndColor 2 .black)
    "Choose one —\n• Target player draws two cards and loses 2 life.\n• Target creature gets +2/+2 and gains lifelink until end of turn."

def nightsWhisper : CardDef :=
  sorcery "Night's Whisper" (ManaCost.ofGenericAndColor 1 .black)
    "You draw two cards and lose 2 life."
    (some (.drawAndLoseLife 2 2))

def stonyVoicedGoblins : CardDef :=
  creature "Stony-Voiced Goblins" (ManaCost.ofGenericAndColor 1 .black) #["Goblin", "Bard"] 1 1
    (oracleText := "When this creature enters, each opponent discards a card.")

def wayfarersBauble : CardDef :=
  artifact "Wayfarer's Bauble" (ManaCost.ofGeneric 1)
    "{2}, {T}, Sacrifice this artifact: Search your library for a basic land card, put that card onto the battlefield tapped, then shuffle."
    (activatedAbilities := #[
      activated .searchBasicLandTapped (ManaCost.ofGeneric 2)
        (tap := true) (sacrificeSource := true)])

def battleScarredGoblin : CardDef :=
  creature "Battle-Scarred Goblin" (ManaCost.ofGenericAndColor 1 .red) #["Goblin", "Warrior"] 2 2
    (oracleText := "Whenever this creature becomes blocked, it deals 1 damage to each creature blocking it.")
    (triggeredAbilities := #[.onBecomesBlockedDeal1ToBlockers])

def improvisedClub : CardDef :=
  instant "Improvised Club" (ManaCost.ofGenericAndColor 1 .red)
    "As an additional cost to cast this spell, sacrifice an artifact or creature.\nImprovised Club deals 4 damage to any target."
    (some (.dealDamage 4))
    (additionalCostSacrificeArtifactOrCreature := true)

def smaugTheGreatCalamity : CardDef :=
  creature "Smaug, the Great Calamity" (ManaCost.ofGenericAndColors 5 [.red, .red])
    #["Dragon"] 5 5
    (oracleText := "Flying\nSpew Flame {4}{R}\nSorcery — Adventure\nSpew Flame deals 5 damage to target creature. (Then exile this card. You may cast the creature later from exile.)")
    (supertypes := #[.legendary])
    (keywords := Keyword.flying)
    (adventure := some (adventure "Spew Flame" (ManaCost.ofGenericAndColor 4 .red)
      "Spew Flame deals 5 damage to target creature. (Then exile this card. You may cast the creature later from exile.)"
      (.dealDamageToCreature 5)))

def ologHaiCrusher : CardDef :=
  creature "Olog-hai Crusher" (ManaCost.ofGenericAndColor 3 .red) #["Troll", "Soldier"] 4 4
    (oracleText := "Trample\nThis creature can't block unless you control a Goblin or Orc.")
    (keywords := Keyword.trample)
    (staticAbilities := #[.cantBlockUnlessYouControl #["Goblin", "Orc"]])

def gandalfSparkStarter : CardDef :=
  creature "Gandalf, Spark Starter" (ManaCost.ofGenericAndColors 4 [.red, .red])
    #["Avatar", "Wizard"] 4 3
    (oracleText := "Reach\nWhen Gandalf enters, he deals 3 damage divided as you choose among one, two, or three targets.")
    (supertypes := #[.legendary])
    (keywords := Keyword.reach)
    (triggeredAbilities := #[.onEnterDealDividedDamage 3 3])

def raggedShortSpear : CardDef :=
  artifact "Ragged Short Spear" (ManaCost.ofGenericAndColor 1 .red)
    "When this Equipment enters, you may discard a card. If you do, draw two cards.\nEquipped creature gets +2/+0.\nEquip {3} ({3}: Attach to target creature you control. Equip only as a sorcery.)"
    (subtypes := #["Equipment"])
    (staticAbilities := #[.equippedCreatureGets 2 0])
    (triggeredAbilities := #[.onEnterMayDiscardDraw 2])
    (activatedAbilities := #[equipAbility (ManaCost.ofGeneric 3)])

def smiteTheDeathless : CardDef :=
  instant "Smite the Deathless" (ManaCost.ofGenericAndColor 1 .red)
    "Smite the Deathless deals 3 damage to target creature. That creature loses indestructible until end of turn. If that creature would die this turn, exile it instead."
    (some (.dealDamageLoseIndestructibleExile 3))

def goblinFireleaper : CardDef :=
  creature "Goblin Fireleaper" (ManaCost.ofGenericAndColor 1 .red) #["Goblin", "Warrior"] 1 1
    (oracleText := "{1}{R}: This creature gets +1/+0 until end of turn.\nWhen this creature dies, it deals damage equal to its power to target creature an opponent controls.")
    (activatedAbilities := #[
      activated (.sourceGets 1 0) (ManaCost.ofGenericAndColor 1 .red)])
    (triggeredAbilities := #[.onDiesDealDamageEqualToPowerToOppCreature])

def oliphaunt : CardDef :=
  creature "Oliphaunt" (ManaCost.ofGenericAndColor 5 .red) #["Elephant"] 6 4
    (oracleText := "Trample\nWhenever this creature attacks, another target creature you control gets +2/+0 and gains trample until end of turn.\nMountaincycling {1} ({1}, Discard this card: Search your library for a Mountain card, reveal it, put it into your hand, then shuffle.)")
    (keywords := Keyword.trample)
    (triggeredAbilities := #[.onAttackOtherGets2AndTrample])

def goblinCratermaker : CardDef :=
  creature "Goblin Cratermaker" (ManaCost.ofGenericAndColor 1 .red) #["Goblin", "Warrior"] 2 2
    (oracleText := "{1}, Sacrifice this creature: Choose one —\n• This creature deals 2 damage to target creature.\n• Destroy target colorless nonland permanent.")
    (activatedAbilities := #[
      activated (.dealDamageToTargetCreature 2) (ManaCost.ofGeneric 1)
        (sacrificeSource := true)
        (otherModes := #[.destroyTargetColorlessNonland])])

def infernoTitan : CardDef :=
  creature "Inferno Titan" (ManaCost.ofGenericAndColors 4 [.red, .red]) #["Giant"] 6 6
    (oracleText := "{R}: This creature gets +1/+0 until end of turn.\nWhenever this creature enters or attacks, it deals 3 damage divided as you choose among one, two, or three targets.")
    (activatedAbilities := #[activated (.sourceGets 1 0) (ManaCost.ofColor .red)])
    (triggeredAbilities := #[.onEnterOrAttackDealDividedDamage 3 3])

def guttersnipe : CardDef :=
  creature "Guttersnipe" (ManaCost.ofGenericAndColor 2 .red) #["Goblin", "Shaman"] 2 2
    (oracleText := "Whenever you cast an instant or sorcery spell, this creature deals 2 damage to each opponent.")
    (triggeredAbilities := #[.onCastInstantOrSorceryDealDamageToEachOpponent 2])

def orcishSiegemaster : CardDef :=
  creature "Orcish Siegemaster" (ManaCost.ofGenericAndColor 2 .red) #["Orc", "Soldier"] 0 5
    (oracleText := "Trample\nOther Orcs and Goblins you control have trample.\nWhenever this creature attacks, it gets +X/+0 until end of turn, where X is the greatest power among creatures you control.")
    (keywords := Keyword.trample)
    (staticAbilities := #[.otherCreaturesHaveTrample #["Orc", "Goblin"]])
    (triggeredAbilities := #[.onAttackPumpByGreatestPower])

def snowslopeHunter : CardDef :=
  creature "Snowslope Hunter" (ManaCost.ofGenericAndColor 2 .red) #["Goblin", "Ranger"] 2 3
    (oracleText := "Sacrifice another creature or artifact: Exile the top card of your library. You may play it until the end of your next turn. Activate only during your turn and only once each turn.")
    (activatedAbilities := #[
      activated .exileTopPlayUntilEndOfNextTurn
        (sacrificeAnotherCreatureOrArtifact := true)
        (onlyDuringYourTurn := true) (onceEachTurn := true)])

def fireOfOrthanc : CardDef :=
  sorcery "Fire of Orthanc" (ManaCost.ofGenericAndColor 3 .red)
    "Destroy target artifact or land. Creatures without flying can't block this turn."
    (some .destroyArtifactOrLandNonflyersCantBlock)

def guardianOfTheHalls : CardDef :=
  creature "Guardian of the Halls" (ManaCost.ofGenericAndColor 1 .green) #["Elf", "Soldier"] 2 2
    (oracleText := "Trample\n{5}{G}{G}: Put three +1/+1 counters on this creature.")
    (keywords := Keyword.trample)
    (activatedAbilities := #[
      activated (.putPlusOnePlusOneOnSource 3)
        (ManaCost.ofGenericAndColors 5 [.green, .green])])

def quarrel : CardDef :=
  instant "Quarrel" (ManaCost.ofGenericAndColor 1 .green)
    "Target creature you control deals damage equal to its power to target creature an opponent controls."
    (some .creatureYouControlDealsPowerToOppCreature)

def galadhrimGuide : CardDef :=
  creature "Galadhrim Guide" (ManaCost.ofGenericAndColor 3 .green) #["Elf", "Scout"] 3 4
    (oracleText := "When this creature enters, scry 2.")
    (triggeredAbilities := #[.onEnterScry 2])

def galionElvenkingsButler : CardDef :=
  creature "Galion, Elvenking's Butler" (ManaCost.ofGenericAndColors 2 [.green, .green])
    #["Elf", "Advisor"] 4 4
    (oracleText := "Whenever Galion attacks, choose up to one other target creature you control. Its base power and toughness become equal to Galion's power and toughness until end of turn.")
    (supertypes := #[.legendary])
    (triggeredAbilities := #[.onAttackSetOtherBasePT])

def elvishVisionary : CardDef :=
  creature "Elvish Visionary" (ManaCost.ofGenericAndColor 1 .green) #["Elf", "Shaman"] 1 1
    (oracleText := "When this creature enters, draw a card.")
    (triggeredAbilities := #[.onEnterDraw 1])

def wargTactics : CardDef :=
  instant "Warg Tactics" (ManaCost.ofGenericAndColor 1 .green)
    "Choose one —\n• Destroy target creature with flying.\n• Put a +1/+1 counter on target creature you control. It gains trample and hexproof until end of turn. (It can't be the target of spells or abilities your opponents control.)"
    (spellModes := #[.destroyCreatureWithFlying, .plusOnePlusOneTrampleHexproof])

def beornsHospitality : CardDef :=
  enchantment "Beorn's Hospitality" (ManaCost.ofGenericAndColor 1 .green)
    "Landfall — Whenever a land you control enters, put a +1/+1 counter on target creature you control.\n{5}{G}{G}: This enchantment becomes a Bear creature in addition to its other types and gains \"This creature's power and toughness are each equal to the number of lands you control.\" (This effect doesn't end.)"
    (triggeredAbilities := #[.onLandYouControlEntersPlusOnePlusOne])
    (activatedAbilities := #[
      activated .becomeBearCreatureWithLandsPT
        (ManaCost.ofGenericAndColors 5 [.green, .green])])

def mirkwoodElk : CardDef :=
  creature "Mirkwood Elk" (ManaCost.ofGenericAndColor 5 .green) #["Elk"] 6 6
    (oracleText := "Trample\nWhenever this creature enters or attacks, return target Elf card from your graveyard to your hand. You gain life equal to that card's power.")
    (keywords := Keyword.trample)
    (triggeredAbilities := #[.onEnterOrAttackReturnElfGainLife])

def celebornTheWise : CardDef :=
  creature "Celeborn the Wise" (ManaCost.ofGenericAndColor 3 .green) #["Elf", "Noble"] 3 3
    (oracleText := "Whenever you attack with one or more Elves, scry 1.\nWhenever you scry, Celeborn gets +1/+1 until end of turn for each card looked at while scrying this way.")
    (supertypes := #[.legendary])
    (triggeredAbilities := #[.onAttackWithElvesScry 1, .onScryPumpSelfForEachLookedAt])

def giftOfStrands : CardDef :=
  aura "Gift of Strands" (ManaCost.ofGenericAndColor 3 .green)
    "Flash\nEnchant creature\nWhen this Aura enters, scry 2.\nEnchanted creature gets +3/+3."
    (keywords := Keyword.flash)
    (staticAbilities := #[.enchantedCreatureGets 3 3])
    (triggeredAbilities := #[.onEnterScry 2])

def elvishArchdruid : CardDef :=
  creature "Elvish Archdruid" (ManaCost.ofGenericAndColors 1 [.green, .green])
    #["Elf", "Druid"] 2 2
    (oracleText := "Other Elf creatures you control get +1/+1.\n{T}: Add {G} for each Elf you control.")
    (staticAbilities := #[.otherCreaturesGet #["Elf"] 1 1])
    (tapAddManaForEach := #[{ mana := .colored .green, subtype := "Elf" }])

def lothlorienLookout : CardDef :=
  creature "Lothlórien Lookout" (ManaCost.ofGenericAndColor 1 .green) #["Elf", "Scout"] 1 3
    (oracleText := "Whenever this creature attacks, scry 1.")
    (triggeredAbilities := #[.onAttackScry 1])

def woodlandWeavemaster : CardDef :=
  creature "Woodland Weavemaster" (ManaCost.ofGenericAndColor 1 .green) #["Elf", "Druid"] 1 2
    (oracleText := "Vigilance\nWhenever another Elf you control enters, this creature gets +1/+1 until end of turn.\n{T}: Add X mana of any one color, where X is this creature's power. Spend this mana only to cast Elf spells and activate abilities of Elf sources.")
    (keywords := Keyword.vigilance)
    (triggeredAbilities := #[.onAnotherElfYouControlEntersGets1])
    (tapAddAnyColorEqualToPower := true)

def mirkwoodPathmaker : CardDef :=
  card "Mirkwood Pathmaker" #[.creature]
    (ManaCost.ofGenericAndColor 2 .green) #["Elf", "Ranger"]
    "Mirkwood Pathmaker's power and toughness are each equal to the number of lands you control."
    (staticAbilities := #[.powerToughnessEqualLandsYouControl])

def beornReluctantHost : CardDef :=
  creature "Beorn, Reluctant Host" (ManaCost.ofGenericAndColor 4 .green)
    #["Human", "Bear", "Shapeshifter"] 5 5
    (oracleText := "Trample\nTill and Tend {1}{G}\nSorcery — Adventure\nYou may play an additional land this turn. (Then exile this card. You may cast the creature later from exile.)")
    (supertypes := #[.legendary])
    (keywords := Keyword.trample)
    (adventure := some (adventure "Till and Tend" (ManaCost.ofGenericAndColor 1 .green)
      "You may play an additional land this turn. (Then exile this card. You may cast the creature later from exile.)"
      .playAdditionalLandThisTurn))

def woodElves : CardDef :=
  creature "Wood Elves" (ManaCost.ofGenericAndColor 2 .green) #["Elf", "Scout"] 1 1
    (oracleText := "When this creature enters, search your library for a Forest card, put that card onto the battlefield, then shuffle.")
    (triggeredAbilities := #[.onEnterSearchForest])

def elvishMystic : CardDef :=
  creature "Elvish Mystic" (ManaCost.ofColor .green) #["Elf", "Druid"] 1 1
    (oracleText := "{T}: Add {G}.")
    (tapAddMana := #[.colored .green])

def attercop : CardDef :=
  creature "Attercop" (ManaCost.ofGenericAndColor 1 .green) #["Spider"] 2 1
    (oracleText := "Reach, deathtouch\nLandfall — Whenever a land you control enters, this creature gets +1/+1 until end of turn.")
    (keywords := Keyword.reach.merge Keyword.deathtouch)
    (triggeredAbilities := #[.onLandYouControlEntersGets1])

#guard bofurReliableGuardian.colors.isMonocolored
#guard roguesPassage.isLand
#guard roguesPassage.activatedAbilities.size == 1
#guard roguesPassage.activatedAbilities[0]!.effect == .targetCantBeBlockedThisTurn
#guard roguesPassage.activatedAbilities[0]!.cost.tap
#guard roguesPassage.activatedAbilities[0]!.cost.mana == (ManaCost.ofGeneric 4)
#guard roguesPassage.tapAddMana == #[.colorless]
#guard elvishMystic.tapAddMana == #[.colored .green]
#guard (attercop.summary.splitOn "Landfall").length > 1
#guard (attercop.summary.splitOn "reach").length > 1
#guard attercop.keywords.reach
#guard attercop.keywords.deathtouch
#guard attercop.triggeredAbilities == #[.onLandYouControlEntersGets1]
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
#guard raggedShortSpear.activatedAbilities[0]!.cost.mana == (ManaCost.ofGeneric 3)
#guard (raggedShortSpear.summary.splitOn "Equipped creature").length > 1
#guard (giftOfStrands.summary.splitOn "flash").length > 1
#guard (giftOfStrands.summary.splitOn "Enchanted creature").length > 1
#guard galadhrimGuide.triggeredAbilities == #[.onEnterScry 2]
#guard (galadhrimGuide.summary.splitOn "scry 2").length > 1
#guard elvishVisionary.triggeredAbilities == #[.onEnterDraw 1]
#guard (elvishVisionary.summary.splitOn "draw a card").length > 1
#guard woodElves.triggeredAbilities == #[.onEnterSearchForest]
#guard (woodElves.summary.splitOn "Forest card").length > 1
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
#guard galionElvenkingsButler.triggeredAbilities == #[.onAttackSetOtherBasePT]
#guard (galionElvenkingsButler.summary.splitOn "base power and toughness").length > 1
#guard galionElvenkingsButler.power == some 4
#guard galionElvenkingsButler.toughness == some 4
#guard lothlorienLookout.triggeredAbilities == #[.onAttackScry 1]
#guard (lothlorienLookout.summary.splitOn "scry 1").length > 1
#guard lothlorienLookout.power == some 1
#guard lothlorienLookout.toughness == some 3
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
#guard galadhrimGuide.power == some 3
#guard galadhrimGuide.toughness == some 4
#guard goblinCratermaker.activatedAbilities.size == 1
#guard goblinCratermaker.activatedAbilities[0]!.cost.sacrificeSource
#guard goblinCratermaker.activatedAbilities[0]!.cost.mana == (ManaCost.ofGeneric 1)
#guard goblinCratermaker.activatedAbilities[0]!.isModal
#guard goblinCratermaker.activatedAbilities[0]!.effect == .dealDamageToTargetCreature 2
#guard goblinCratermaker.activatedAbilities[0]!.otherModes ==
  #[.destroyTargetColorlessNonland]
#guard (goblinCratermaker.summary.splitOn "Choose one").length > 1
#guard (goblinCratermaker.summary.splitOn "colorless nonland").length > 1
#guard quarrel.isInstant
#guard quarrel.spellEffect == some .creatureYouControlDealsPowerToOppCreature
#guard quarrel.requiresTarget
#guard SpellEffect.targetCount .creatureYouControlDealsPowerToOppCreature == 2
#guard (quarrel.summary.splitOn "deals damage equal to its power").length > 1
#guard smiteTheDeathless.isInstant
#guard smiteTheDeathless.requiresTarget
#guard smiteTheDeathless.spellEffect == some (.dealDamageLoseIndestructibleExile 3)
#guard SpellEffect.targetCount (.dealDamageLoseIndestructibleExile 3) == 1
#guard (smiteTheDeathless.summary.splitOn "loses indestructible").length > 1
#guard (smiteTheDeathless.summary.splitOn "exile it instead").length > 1
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
  (ManaCost.ofGenericAndColors 5 [.green, .green])
#guard (beornsHospitality.summary.splitOn "Landfall").length > 1
#guard (beornsHospitality.summary.splitOn "Bear creature").length > 1
#guard mirkwoodPathmaker.staticAbilities == #[.powerToughnessEqualLandsYouControl]
#guard mirkwoodPathmaker.power.isNone
#guard mirkwoodPathmaker.toughness.isNone
#guard (mirkwoodPathmaker.summary.splitOn "*/*").length > 1
#guard (mirkwoodPathmaker.summary.splitOn "lands you control").length > 1
#guard ologHaiCrusher.keywords.trample
#guard ologHaiCrusher.staticAbilities == #[.cantBlockUnlessYouControl #["Goblin", "Orc"]]
#guard (ologHaiCrusher.summary.splitOn "trample").length > 1
#guard (ologHaiCrusher.summary.splitOn "can't block unless").length > 1
#guard oliphaunt.keywords.trample
#guard oliphaunt.triggeredAbilities == #[.onAttackOtherGets2AndTrample]
#guard oliphaunt.power == some 6
#guard oliphaunt.toughness == some 4
#guard (oliphaunt.summary.splitOn "trample").length > 1
#guard (oliphaunt.summary.splitOn "+2/+0").length > 1
#guard (oliphaunt.summary.splitOn "Mountaincycling").length > 1
#guard gandalfSparkStarter.keywords.reach
#guard gandalfSparkStarter.triggeredAbilities == #[.onEnterDealDividedDamage 3 3]
#guard (gandalfSparkStarter.summary.splitOn "divided as you choose").length > 1
#guard (gandalfSparkStarter.summary.splitOn "reach").length > 1
#guard goblinFireleaper.activatedAbilities.size == 1
#guard goblinFireleaper.activatedAbilities[0]!.effect == .sourceGets 1 0
#guard goblinFireleaper.activatedAbilities[0]!.cost.mana == (ManaCost.ofGenericAndColor 1 .red)
#guard goblinFireleaper.triggeredAbilities == #[.onDiesDealDamageEqualToPowerToOppCreature]
#guard (goblinFireleaper.summary.splitOn "+1/+0").length > 1
#guard (goblinFireleaper.summary.splitOn "dies").length > 1
#guard infernoTitan.activatedAbilities.size == 1
#guard infernoTitan.activatedAbilities[0]!.effect == .sourceGets 1 0
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
#guard guardianOfTheHalls.keywords.trample
#guard guardianOfTheHalls.activatedAbilities.size == 1
#guard guardianOfTheHalls.activatedAbilities[0]!.effect == .putPlusOnePlusOneOnSource 3
#guard guardianOfTheHalls.activatedAbilities[0]!.cost.mana ==
  (ManaCost.ofGenericAndColors 5 [.green, .green])
#guard guardianOfTheHalls.power == some 2
#guard guardianOfTheHalls.toughness == some 2
#guard (guardianOfTheHalls.summary.splitOn "trample").length > 1
#guard (guardianOfTheHalls.summary.splitOn "+1/+1").length > 1
#guard desolationProwler.activatedAbilities.size == 1
#guard desolationProwler.activatedAbilities[0]!.effect == .sourceGets 2 2
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
#guard improvisedClub.isInstant
#guard improvisedClub.spellEffect == some (.dealDamage 4)
#guard improvisedClub.additionalCostSacrificeArtifactOrCreature
#guard improvisedClub.requiresTarget
#guard (improvisedClub.summary.splitOn "additional cost").length > 1
#guard (improvisedClub.summary.splitOn "4 damage").length > 1
#guard fireOfOrthanc.isSorcery
#guard fireOfOrthanc.spellEffect == some .destroyArtifactOrLandNonflyersCantBlock
#guard fireOfOrthanc.requiresTarget
#guard (fireOfOrthanc.summary.splitOn "artifact or land").length > 1
#guard (fireOfOrthanc.summary.splitOn "can't block this turn").length > 1
#guard nightsWhisper.isSorcery
#guard nightsWhisper.spellEffect == some (.drawAndLoseLife 2 2)
#guard !nightsWhisper.requiresTarget
#guard nightsWhisper.hasCastKind .draw
#guard (nightsWhisper.summary.splitOn "draw two cards").length > 1
#guard (nightsWhisper.summary.splitOn "lose 2 life").length > 1
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
      adv.spellEffect == some (.dealDamageToCreature 5)
  | none => false
#guard (smaugTheGreatCalamity.summary.splitOn "Spew Flame").length > 1
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
      adv.spellEffect == some .playAdditionalLandThisTurn &&
      !adv.toCardDef.requiresTarget
  | none => false
#guard (beornReluctantHost.summary.splitOn "Till and Tend").length > 1
#guard (beornReluctantHost.summary.splitOn "trample").length > 1
#guard (beornReluctantHost.summary.splitOn "additional land").length > 1

end Mtg.Engine.Catalog
