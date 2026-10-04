/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
Authors: MTG Engine Contributors
-/
import Mtg.Engine.Catalog

/-!
# Marvel Super Heroes catalog (MSH, 2026)

Official *Magic: The Gathering | Marvel Super Heroes* set: 276 draft-legal
cards (collector numbers 1–276) plus the five basic lands printed in the set.
Each card is its full printed text from Scryfall (`set:msh unique:cards`).
-/

namespace Mtg.Engine.Catalog
open Mtg.Engine

def theSensationalSheHulk : CardDef :=
  fromOracle [
    "The Sensational She-Hulk",
    "{3}{G}{W}{W}",
    "Legendary Creature — Gamma Hero",
    "6/6",
    "Reach, trample",
    "Your opponents can't cast spells during your turn.",
    "Whenever a creature you control is dealt damage, you may have The Sensational She-Hulk deal that much damage to any target. Do this only once each turn.",
  ]

def photonLivingLight : CardDef :=
  fromOracle [
    "Photon, Living Light",
    "{2}{R}{W}{W}",
    "Legendary Creature — Elemental Hero",
    "4/4",
    "Flying, hexproof, prowess",
    "Whenever you cast a noncreature spell, put a +1/+1 counter on each other creature you control.",
  ]

def theIncredibleHulk : CardDef :=
  fromOracle [
    "The Incredible Hulk",
    "{2}{R}{R}{G}{G}",
    "Legendary Creature — Gamma Berserker Hero",
    "8/8",
    "Reach, trample",
    "Enrage — Whenever The Incredible Hulk is dealt damage, put a +1/+1 counter on him. If he's attacking, untap him and there is an additional combat phase after this phase.",
  ]

def theInvincibleIronMan : CardDef :=
  fromOracle [
    "The Invincible Iron Man",
    "{4}{U}{R}",
    "Legendary Artifact Creature — Human Hero",
    "5/5",
    "Flying, haste",
    "At the beginning of combat on your turn, you may put an artifact card from your hand onto the battlefield. If it's an Equipment, attach it to The Invincible Iron Man.",
  ]

def blackPantherHopeEnduring : CardDef :=
  fromOracle [
    "Black Panther, Hope Enduring",
    "{4}{W}{U}",
    "Legendary Creature — Human Warrior Hero",
    "3/3",
    "Flash",
    "Double strike",
    "Prevent all damage that would be dealt to Black Panther.",
    "Whenever Black Panther deals combat damage to a player, draw a card.",
  ]

def agent13SharonCarter : CardDef :=
  fromOracle [
    "Agent 13, Sharon Carter",
    "{2}{W}",
    "Legendary Creature — Human Spy Hero",
    "3/2",
    "Whenever a creature you control attacks alone, investigate. (Create a Clue token. It's an artifact with \"{2}, Sacrifice this token: Draw a card.\")",
  ]

def agentMariaHill : CardDef :=
  fromOracle [
    "Agent Maria Hill",
    "{W}",
    "Legendary Creature — Human Spy Hero",
    "2/1",
    "Whenever Agent Maria Hill becomes tapped to pay a teamwork cost, put a +1/+1 counter on her and draw a card.",
  ]

def agentOfAtlas : CardDef :=
  fromOracle [
    "Agent of Atlas",
    "{1}{W}",
    "Creature — Human Spy Hero",
    "2/2",
    "Prowess (Whenever you cast a noncreature spell, this creature gets +1/+1 until end of turn.)",
  ]

def agentPhilCoulson : CardDef :=
  fromOracle [
    "Agent Phil Coulson",
    "{1}{W}",
    "Legendary Creature — Human Spy Hero",
    "2/2",
    "Vigilance",
    "{T}: Put a +1/+1 counter on each other Hero you control.",
  ]

def agentsOfSHIELD : CardDef :=
  fromOracle [
    "Agents of S.H.I.E.L.D.",
    "{2}{W}",
    "Creature — Human Spy Hero",
    "2/4",
    "Whenever a creature you control attacks alone, that creature gets +1/+1 until end of turn.",
  ]

def avengersAssemble : CardDef :=
  fromOracle [
    "Avengers Assemble!",
    "{4}{W}",
    "Enchantment",
    "Flash",
    "Heroes you control get +2/+2.",
    "At the beginning of each end step, if you attacked with a Hero this turn or a Hero entered the battlefield under your control this turn, draw a card.",
  ]

def boroughBackup : CardDef :=
  fromOracle [
    "Borough Backup",
    "{4}{W}",
    "Sorcery",
    "Create two 3/2 white Hero creature tokens with vigilance.",
    "Basic landcycling {2} ({2}, Discard this card: Search your library for a basic land card, reveal it, put it into your hand, then shuffle.)",
  ]

def braveBrawler : CardDef :=
  fromOracle [
    "Brave Brawler",
    "{1}{W}",
    "Creature — Human Warrior Hero",
    "2/1",
    "Lifelink",
    "Power-up — {4}{W}: Put two +1/+1 counters on this creature. (Activate each power-up ability only once. Reduce the cost by its mana cost if it entered this turn.)",
  ]

def captainAmericaSuperSoldier : CardDef :=
  fromOracle [
    "Captain America, Super-Soldier",
    "{1}{W}{W}",
    "Legendary Creature — Human Soldier Hero",
    "3/2",
    "First strike",
    "Captain America enters with a shield counter on him. (If he would be dealt damage or destroyed, remove a shield counter from him instead.)",
    "As long as Captain America has a shield counter on him, you and other Heroes you control have hexproof.",
  ]

def captainAmericaWingsOfFreedom : CardDef :=
  fromOracle [
    "Captain America, Wings of Freedom",
    "{2}{W}",
    "Legendary Creature — Human Soldier Hero",
    "3/1",
    "Flying, first strike, ward {1}",
    "Whenever Captain America attacks, each other Hero you control gets +X/+X until end of turn, where X is Captain America's toughness.",
  ]

def captainMarvelEarthSProtector : CardDef :=
  fromOracle [
    "Captain Marvel, Earth's Protector",
    "{3}{W}{W}",
    "Legendary Creature — Human Kree Hero",
    "5/4",
    "Flash",
    "Flying, lifelink",
    "Power-up — {5}{W}{W}: Put a +1/+1 counter and an indestructible counter on Captain Marvel. (Activate each power-up ability only once. Reduce the cost by her mana cost if she entered this turn.)",
  ]

def captainMarVellSpaceBorn : CardDef :=
  fromOracle [
    "Captain Mar-Vell, Space-Born",
    "{4}{W}",
    "Legendary Creature — Kree Soldier Hero",
    "4/4",
    "Flying, vigilance",
    "Cosmic Awareness — As long as an opponent has cast a spell this turn, you may cast spells as though they had flash.",
  ]

def colleenWingStreetSamurai : CardDef :=
  fromOracle [
    "Colleen Wing, Street Samurai",
    "{1}{W}",
    "Legendary Creature — Human Samurai Hero",
    "2/2",
    "Whenever you cast a spell that targets a creature you control, put a +1/+1 counter on Colleen Wing. Scry 1. (Look at the top card of your library. You may put that card on the bottom.)",
  ]

def crowdOfTrueBelievers : CardDef :=
  fromOracle [
    "Crowd of True Believers",
    "{W}",
    "Creature — Human Citizen",
    "1/2",
    "{T}: Target creature you control that's attacking alone gets +1/+0 until end of turn. You gain 1 life.",
  ]

def helicarrierStrike : CardDef :=
  fromOracle [
    "Helicarrier Strike",
    "{W}",
    "Instant",
    "Teamwork 2 (As an additional cost to cast this spell, you may tap any number of creatures you control with total power 2 or more.)",
    "Helicarrier Strike deals 2 damage to target attacking or blocking creature. If this spell was cast using teamwork, it deals 4 damage to that creature instead.",
  ]

def heroInTraining : CardDef :=
  fromOracle [
    "Hero in Training",
    "{2}{W}",
    "Creature — Human Hero",
    "2/2",
    "When this creature enters, draw a card. If you control another Hero, you gain 2 life.",
  ]

def invisibleWomanSueStorm : CardDef :=
  fromOracle [
    "Invisible Woman, Sue Storm",
    "{4}{W}",
    "Legendary Creature — Human Hero",
    "2/5",
    "Lifelink",
    "Whenever you put one or more +1/+1 counters on one or more other Heroes you control, you may create a 0/4 colorless Wall creature token with defender.",
  ]

def jenniferWalters : CardDef :=
  fromOracle [
    "Jennifer Walters",
    "{1}{W}",
    "Legendary Creature — Human Advisor Hero",
    "2/3",
    "Your opponents can't cast spells during your turn.",
    "{3}{G}{W}{W}: Transform Jennifer Walters. Activate only as a sorcery.",
    "//",
    "The Sensational She-Hulk",
    "{3}{G}{W}{W}",
    "Legendary Creature — Gamma Hero",
    "6/6",
    "Reach, trample",
    "Your opponents can't cast spells during your turn.",
    "Whenever a creature you control is dealt damage, you may have The Sensational She-Hulk deal that much damage to any target. Do this only once each turn.",
  ]

def kreeCommandos : CardDef :=
  fromOracle [
    "Kree Commandos",
    "{2}{W}",
    "Creature — Kree Soldier Villain",
    "2/1",
    "Flying, vigilance",
    "Prowess (Whenever you cast a noncreature spell, this creature gets +1/+1 until end of turn.)",
  ]

def lukeCagePowerMan : CardDef :=
  fromOracle [
    "Luke Cage, Power Man",
    "{3}{W}",
    "Legendary Creature — Human Hero",
    "2/5",
    "Unbreakable Skin — Whenever Luke Cage attacks alone, he gets +2/+0 and gains indestructible until end of turn. (Damage and effects that say \"destroy\" don't destroy him.)",
  ]

def theMindStone : CardDef :=
  fromOracle [
    "The Mind Stone",
    "{1}{W}",
    "Legendary Artifact — Infinity Stone",
    "Indestructible",
    "{T}: Add {W}.",
    "{5}{W}, {T}: Harness The Mind Stone. (Once harnessed, its ∞ ability is active.)",
    "∞ — At the beginning of your end step, exile up to one other target nonland permanent you control, then return that card to the battlefield under its owner's control.",
  ]

def mockingbirdAceAgent : CardDef :=
  fromOracle [
    "Mockingbird, Ace Agent",
    "{3}{W}",
    "Legendary Creature — Human Spy Hero",
    "2/2",
    "Double strike",
    "Whenever you cast a spell that targets a creature you control, put a +1/+1 counter on Mockingbird.",
  ]

def monicaRambeau : CardDef :=
  fromOracle [
    "Monica Rambeau",
    "{2}{W}",
    "Legendary Creature — Human Hero",
    "3/3",
    "Flying, prowess (Whenever you cast a noncreature spell, this creature gets +1/+1 until end of turn.)",
    "{2}{R}{W}{W}: Transform Monica Rambeau. Activate only as a sorcery.",
    "//",
    "Photon, Living Light",
    "{2}{R}{W}{W}",
    "Legendary Creature — Elemental Hero",
    "4/4",
    "Flying, hexproof, prowess",
    "Whenever you cast a noncreature spell, put a +1/+1 counter on each other creature you control.",
  ]

def murdockSCrusade : CardDef :=
  fromOracle [
    "Murdock's Crusade",
    "{1}{W}",
    "Sorcery",
    "Teamwork 4 (As an additional cost to cast this spell, you may tap any number of creatures you control with total power 4 or more.)",
    "Choose one. If this spell was cast using teamwork, choose both instead.",
    "• Street Justice — Exile target creature with toughness 4 or greater.",
    "• Legal Justice — Exile target enchantment with mana value 4 or greater.",
  ]

def nickFuryAgentOfSHIELD : CardDef :=
  fromOracle [
    "Nick Fury, Agent of S.H.I.E.L.D.",
    "{W}",
    "Legendary Creature — Human Spy Hero",
    "2/1",
    "Power-up — {W}{U}{B}{R}{G}: Put two +1/+1 counters on Nick Fury, then look at the top seven cards of your library. You may put a Hero, Equipment, or Vehicle card from among them onto the battlefield. If it's a double-faced card, you may transform it. Put the rest on the bottom of your library in a random order. (Activate each power-up ability only once. Reduce the cost by his mana cost if he entered this turn.)",
  ]

def nightNurseHealerOfHeroes : CardDef :=
  fromOracle [
    "Night Nurse, Healer of Heroes",
    "{1}{W}",
    "Legendary Creature — Human Doctor Hero",
    "2/1",
    "Flash",
    "Lifelink",
    "When Night Nurse enters, choose target permanent card in your graveyard that was put there from anywhere this turn. Return it to your hand.",
  ]

def okoyeDoraMilajeLeader : CardDef :=
  fromOracle [
    "Okoye, Dora Milaje Leader",
    "{3}{W}",
    "Legendary Creature — Human Warrior Hero",
    "3/2",
    "When Okoye enters, create two 1/1 white Soldier creature tokens.",
    "Attacking creature tokens you control have first strike.",
  ]

def originOfTheAvengers : CardDef :=
  fromOracle [
    "Origin of the Avengers",
    "{1}{W}",
    "Enchantment — Saga",
    "(As this Saga enters and after your draw step, add a lore counter. Sacrifice after III.)",
    "I — Scry 2.",
    "II — You may put a Hero creature card with mana value 3 or less from your hand onto the battlefield. If you don't, draw a card.",
    "III — Put a +1/+1 counter on each creature you control.",
  ]

def pantherPounce : CardDef :=
  fromOracle [
    "Panther Pounce",
    "{W}",
    "Instant",
    "Target player investigates. Target creature gets +1/+0 and gains flying until end of turn. Untap it. (To investigate, create a Clue token. It's an artifact with \"{2}, Sacrifice this token: Draw a card.\")",
  ]

def patriotShieldWielder : CardDef :=
  fromOracle [
    "Patriot, Shield Wielder",
    "{1}{W}",
    "Legendary Creature — Human Hero",
    "2/2",
    "{2}, {T}: Another target creature you control gets +2/+0 and gains hexproof until end of turn. (It can't be the target of spells or abilities your opponents control.)",
  ]

def politicalTriumph : CardDef :=
  fromOracle [
    "Political Triumph",
    "{W}",
    "Enchantment — Plan",
    "Whenever a creature you control enters, scry 1 and put a plan counter on this enchantment.",
    "When the fourth plan counter is put on this enchantment, sacrifice it, draw a card, and put a +1/+1 counter on each creature you control.",
  ]

def quakeAgentOfSHIELD : CardDef :=
  fromOracle [
    "Quake, Agent of S.H.I.E.L.D.",
    "{2}{W}",
    "Legendary Creature — Inhuman Spy Hero",
    "3/3",
    "Seismic Takedown — Whenever you cast a noncreature spell, tap target creature or land.",
  ]

def raftSecurityOfficer : CardDef :=
  fromOracle [
    "Raft Security Officer",
    "{1}{W}",
    "Creature — Human Soldier",
    "1/3",
    "{2}, {T}: Tap target creature. This ability costs {1} less to activate if it targets a creature with power 3 or less.",
  ]

def redGuardianSuperSoldier : CardDef :=
  fromOracle [
    "Red Guardian, Super-Soldier",
    "{2}{W}",
    "Legendary Creature — Human Soldier Villain",
    "2/2",
    "Flash",
    "When Red Guardian enters, destroy target creature an opponent controls that dealt damage this turn.",
  ]

def theSentryGoldenGuardian : CardDef :=
  fromOracle [
    "The Sentry, Golden Guardian",
    "{3}{W}",
    "Legendary Creature — Human Hero",
    "5/5",
    "Flying, vigilance, indestructible",
    "When The Sentry enters, target opponent creates The Void, a legendary 5/5 black Horror Villain creature token with flying, indestructible, and \"The Void attacks each combat if able.\"",
  ]

def sHIELDSpyKit : CardDef :=
  fromOracle [
    "S.H.I.E.L.D. Spy Kit",
    "{W}",
    "Artifact — Equipment",
    "Equipped creature gets +1/+1.",
    "Whenever equipped creature attacks alone, untap it and scry 1. (Look at the top card of your library. You may put that card on the bottom.)",
    "Equip {1} ({1}: Attach to target creature you control. Equip only as a sorcery.)",
  ]

def superVillainLockup : CardDef :=
  fromOracle [
    "Super Villain Lockup",
    "{1}{W}",
    "Enchantment",
    "Flash",
    "When this enchantment enters, exile target tapped creature an opponent controls until this enchantment leaves the battlefield.",
  ]

def superSoldierSerum : CardDef :=
  fromOracle [
    "Super-Soldier Serum",
    "{1}{W}",
    "Enchantment — Aura",
    "Enchant creature",
    "Enchanted creature gets +2/+2, has first strike and vigilance, and is a legendary Soldier in addition to its other types.",
    "Whenever enchanted creature attacks or blocks, attach any number of target Equipment you control to it.",
  ]

def takeUpTheShield : CardDef :=
  fromOracle [
    "Take Up the Shield",
    "{1}{W}",
    "Instant",
    "Put a +1/+1 counter on target creature. It gains lifelink and indestructible until end of turn. (Damage and effects that say \"destroy\" don't destroy it.)",
  ]

def wakandanDroneFlock : CardDef :=
  fromOracle [
    "Wakandan Drone Flock",
    "{3}{W}",
    "Artifact Creature — Robot",
    "3/3",
    "Flying",
    "When this creature enters, scry 2. (Look at the top two cards of your library, then put any number of them on the bottom and the rest on top in any order.)",
  ]

def webUp : CardDef :=
  fromOracle [
    "Web Up",
    "{2}{W}",
    "Enchantment",
    "When this enchantment enters, exile target nonland permanent an opponent controls until this enchantment leaves the battlefield.",
  ]

def whiteWidowFreeAgent : CardDef :=
  fromOracle [
    "White Widow, Free Agent",
    "{3}{W}",
    "Legendary Creature — Human Hero Villain",
    "2/3",
    "When White Widow enters, choose one —",
    "• Put a +1/+1 counter on each of up to two target creatures.",
    "• Return target artifact or enchantment card from your graveyard to your hand.",
  ]

def aerialDoombot : CardDef :=
  fromOracle [
    "Aerial Doombot",
    "{U}",
    "Artifact Creature — Robot Villain",
    "1/1",
    "Flying",
    "Power-up — {5}{U}: Put three +1/+1 counters on this creature. (Activate each power-up ability only once. Reduce the cost by its mana cost if it entered this turn.)",
  ]

def aIMScientists : CardDef :=
  fromOracle [
    "A.I.M. Scientists",
    "{3}{U}",
    "Creature — Human Scientist Villain",
    "3/3",
    "When this creature enters, it connives. (Draw a card, then discard a card. If you discarded a nonland card, put a +1/+1 counter on this creature.)",
    "Basic landcycling {2} ({2}, Discard this card: Search your library for a basic land card, reveal it, put it into your hand, then shuffle.)",
  ]

def atlanteanCavalry : CardDef :=
  fromOracle [
    "Atlantean Cavalry",
    "{2}{U}",
    "Creature — Merfolk Soldier",
    "3/2",
    "Vigilance",
    "Whenever you draw your second card each turn, put a +1/+1 counter on this creature.",
  ]

def atlantisAttacks : CardDef :=
  fromOracle [
    "Atlantis Attacks",
    "{5}{U}{U}",
    "Sorcery",
    "Teamwork 4 (As an additional cost to cast this spell, you may tap any number of creatures you control with total power 4 or more.)",
    "Choose one. If this spell was cast using teamwork, choose both instead.",
    "• Target player creates a 6/5 blue Leviathan creature token with hexproof.",
    "• Return one or two target nonland permanents to their owners' hands.",
  ]

def attumaAtlanteanWarlord : CardDef :=
  fromOracle [
    "Attuma, Atlantean Warlord",
    "{2}{U}{U}",
    "Legendary Creature — Merfolk Warrior Villain",
    "3/4",
    "Other Merfolk you control get +1/+1.",
    "Whenever one or more Merfolk you control attack a player, draw a card.",
  ]

def boldBiochemist : CardDef :=
  fromOracle [
    "Bold Biochemist",
    "{1}{U}",
    "Creature — Human Scientist",
    "1/3",
    "Power-up — {5}{U}: Put a +1/+1 counter on this creature and draw two cards. (Activate each power-up ability only once. Reduce the cost by its mana cost if it entered this turn.)",
  ]

def bruceBanner : CardDef :=
  fromOracle [
    "Bruce Banner",
    "{U}",
    "Legendary Creature — Human Scientist Hero",
    "1/1",
    "{X}{X}, {T}: Draw X cards. Activate only as a sorcery.",
    "{2}{R}{R}{G}{G}: Transform Bruce Banner. Activate only as a sorcery.",
    "//",
    "The Incredible Hulk",
    "{2}{R}{R}{G}{G}",
    "Legendary Creature — Gamma Berserker Hero",
    "8/8",
    "Reach, trample",
    "Enrage — Whenever The Incredible Hulk is dealt damage, put a +1/+1 counter on him. If he's attacking, untap him and there is an additional combat phase after this phase.",
  ]

def depower : CardDef :=
  fromOracle [
    "Depower",
    "{2}{U}",
    "Instant",
    "This spell costs {2} less to cast if it targets an attacking creature.",
    "Target creature gets -4/-0 until end of turn.",
    "Draw a card.",
  ]

def echoPerceptiveProdigy : CardDef :=
  fromOracle [
    "Echo, Perceptive Prodigy",
    "{2}{U}",
    "Legendary Creature — Human Hero",
    "1/4",
    "Vigilance",
    "{1}, {T}: Copy target activated or triggered ability you control from a creature source. You may choose new targets for the copy. (Mana abilities can't be targeted.)",
  ]

def falconWingedWonder : CardDef :=
  fromOracle [
    "Falcon, Winged Wonder",
    "{4}{U}",
    "Legendary Creature — Human Hero",
    "3/4",
    "Flying",
    "Avian Telepathy — When Falcon enters, create Redwing, a legendary 1/1 blue Bird Scout creature token with flying and \"Whenever Redwing attacks, surveil 1.\" (Look at the top card of your library. You may put it into your graveyard.)",
  ]

def falconSWingHarness : CardDef :=
  fromOracle [
    "Falcon's Wing Harness",
    "{1}{U}",
    "Artifact — Equipment",
    "When this Equipment enters, attach it to target creature you control.",
    "Equipped creature gets +1/+1 and has flying and ward {1}. (Whenever equipped creature becomes the target of a spell or ability an opponent controls, counter it unless that player pays {1}.)",
    "Equip {2}{U} ({2}{U}: Attach to target creature you control. Equip only as a sorcery.)",
  ]

def frozenInIce : CardDef :=
  fromOracle [
    "Frozen in Ice",
    "{2}{U}",
    "Enchantment — Aura",
    "Enchant creature",
    "When this Aura enters, tap enchanted creature.",
    "Enchanted creature loses all abilities and can't become untapped.",
  ]

def futuristForge : CardDef :=
  fromOracle [
    "Futurist Forge",
    "{1}{U}",
    "Artifact",
    "When this artifact enters, draw a card.",
    "{3}{U}, Sacrifice this artifact: Draw two cards.",
  ]

def giantSizedFlyingAnt : CardDef :=
  fromOracle [
    "Giant-Sized Flying Ant",
    "{3}{U}",
    "Creature — Insect",
    "3/2",
    "Flash",
    "Flying",
    "When this creature enters, choose one —",
    "• Tap target nonland permanent.",
    "• Untap target nonland permanent.",
  ]

def hydraulicHelper : CardDef :=
  fromOracle [
    "Hydraulic Helper",
    "{1}{U}",
    "Artifact Creature — Robot",
    "2/3",
    "Defender",
    "{T}: Add {U}. This mana can't be spent to cast a nonartifact spell.",
  ]

def iAmIronMan : CardDef :=
  fromOracle [
    "I Am Iron Man",
    "{2}{U}",
    "Instant",
    "Until end of turn, target artifact or creature becomes an artifact creature with base power and toughness 4/4 and gains flying.",
    "Draw a card.",
  ]

def ironLadDivergingDestiny : CardDef :=
  fromOracle [
    "Iron Lad, Diverging Destiny",
    "{2}{U}",
    "Legendary Artifact Creature — Human Hero",
    "2/2",
    "Flying, vigilance",
    "You may look at the top card of your library any time.",
    "{T}: Reveal the top card of your library. If it's an artifact card, draw a card.",
  ]

def ironheartCleverChampion : CardDef :=
  fromOracle [
    "Ironheart, Clever Champion",
    "{4}{U}",
    "Legendary Artifact Creature — Human Hero",
    "3/4",
    "Improvise (Your artifacts can help cast this spell. Each artifact you tap after you're done activating mana abilities pays for {1}.)",
    "Flying",
    "Noncreature spells you cast have improvise.",
  ]

def justiceVanceAstrovik : CardDef :=
  fromOracle [
    "Justice, Vance Astrovik",
    "{2}{U}",
    "Legendary Creature — Mutant Hero",
    "2/2",
    "Flying",
    "When Justice enters, return up to one target nonland, nontoken permanent to its owner's hand.",
    "Whenever another nonland permanent you control is returned to its owner's hand, put a +1/+1 counter on Justice.",
  ]

def kangTheConqueror : CardDef :=
  fromOracle [
    "Kang the Conqueror",
    "{2}{U}{U}",
    "Legendary Creature — Human Villain",
    "4/5",
    "Flying",
    "Power-up — {5}{U}{U}{U}: Put a +1/+1 counter on Kang. Take an extra turn after this one. During that turn, power-up abilities can't be activated. (Activate each power-up ability only once. Reduce the cost by his mana cost if he entered this turn.)",
  ]

def kidLoki : CardDef :=
  fromOracle [
    "Kid Loki",
    "{U}",
    "Legendary Creature — God Hero Villain",
    "1/1",
    "Each creature you control that you've put one or more +1/+1 counters on this turn has hexproof.",
    "Whenever you draw your second card each turn, put a +1/+1 counter on Kid Loki.",
  ]

def leaderSuperGenius : CardDef :=
  fromOracle [
    "Leader, Super-Genius",
    "{2}{U}{U}",
    "Legendary Creature — Gamma Scientist Villain",
    "1/3",
    "If a creature you control would connive, instead you draw a card, then that creature connives.",
    "At the beginning of combat on your turn, target creature you control connives. (Draw a card, then discard a card. If you discarded a nonland card, put a +1/+1 counter on that creature.)",
  ]

def lokiGodOfMischief : CardDef :=
  fromOracle [
    "Loki, God of Mischief",
    "{1}{U}",
    "Legendary Creature — God Sorcerer Villain",
    "2/1",
    "Whenever a player or permanent becomes the target of an ability you control, draw a card. This ability triggers only once each turn.",
  ]

def misterFantasticReedRichards : CardDef :=
  fromOracle [
    "Mister Fantastic, Reed Richards",
    "{3}{U}",
    "Legendary Creature — Human Scientist Hero",
    "2/4",
    "Reach",
    "Whenever one or more tokens you control enter, you may draw a card.",
  ]

def msMarvelKamalaKhan : CardDef :=
  fromOracle [
    "Ms. Marvel, Kamala Khan",
    "{2}{U}",
    "Legendary Creature — Mutant Inhuman Hero",
    "1/4",
    "Reach, vigilance",
    "You have no maximum hand size.",
    "Embiggen Fist — Whenever you cast a spell that targets a creature you control, draw a card. Until end of turn, Ms. Marvel gains \"Ms. Marvel's base power is equal to the number of cards in your hand.\"",
  ]

def multiversalIncursion : CardDef :=
  fromOracle [
    "Multiversal Incursion",
    "{5}{U}{U}",
    "Sorcery",
    "For each nontoken creature you control, create a token that's a copy of that creature, except it isn't legendary.",
  ]

def namorTheSubMariner : CardDef :=
  fromOracle [
    "Namor the Sub-Mariner",
    "{1}{U}{U}",
    "Legendary Creature — Mutant Merfolk Villain",
    "*/4",
    "Flying",
    "Namor's power is equal to the number of Merfolk you control.",
    "Whenever you cast a noncreature spell with one or more blue mana symbols in its mana cost, create that many 1/1 blue Merfolk creature tokens.",
  ]

def pymParticles : CardDef :=
  fromOracle [
    "Pym Particles",
    "{U}",
    "Sorcery",
    "Target creature gains vigilance until end of turn and can't be blocked this turn.",
    "Draw a card.",
  ]

def rewriteHistory : CardDef :=
  fromOracle [
    "Rewrite History",
    "{2}{U}",
    "Enchantment — Plan",
    "Whenever one or more creatures you control become tapped, draw a card, then discard a card and put a plan counter on this enchantment.",
    "When the fourth plan counter is put on this enchantment, sacrifice it. When you do, return up to two target instant and/or sorcery cards from your graveyard to your hand.",
  ]

def secretInvasion : CardDef :=
  fromOracle [
    "Secret Invasion",
    "{1}{U}{U}",
    "Enchantment — Aura",
    "Enchant creature you control",
    "When this Aura enters, exile up to one target creature other than enchanted creature until this Aura leaves the battlefield. Enchanted creature becomes a copy of that creature until this Aura leaves the battlefield.",
    "Enchanted creature has ward {2}.",
  ]

def sHIELDDeploymentDrone : CardDef :=
  fromOracle [
    "S.H.I.E.L.D. Deployment Drone",
    "{2}{U}",
    "Artifact Creature — Robot",
    "2/2",
    "Flying",
    "When this creature enters, create a 1/1 white Soldier creature token.",
  ]

def sHIELDFlyingCar : CardDef :=
  fromOracle [
    "S.H.I.E.L.D. Flying Car",
    "{2}{U}",
    "Artifact — Vehicle",
    "3/3",
    "Flash",
    "Flying",
    "When this Vehicle enters, exile up to one target creature you control. Return that card to the battlefield under its owner's control at the beginning of the next end step.",
    "Crew 1",
  ]

def shuriWakandanInventor : CardDef :=
  fromOracle [
    "Shuri, Wakandan Inventor",
    "{1}{U}",
    "Legendary Creature — Human Artificer Hero",
    "2/1",
    "Artifact spells you cast cost {1} less to cast.",
    "{1}, {T}: Target artifact you control becomes a copy of a second target artifact you control until end of turn, except it isn't legendary. Activate only as a sorcery.",
  ]

def statureSizeShifter : CardDef :=
  fromOracle [
    "Stature, Size Shifter",
    "{U}",
    "Legendary Creature — Human Hero",
    "1/1",
    "Stature can't be blocked if her power is 1 or less.",
    "Power-up — {X}{U}{U}: Put X +1/+1 counters on Stature. (Activate each power-up ability only once. Reduce the cost by her mana cost if she entered this turn.)",
  ]

def superIntelligence : CardDef :=
  fromOracle [
    "Super Intelligence",
    "{U}",
    "Enchantment — Aura",
    "Enchant creature",
    "At the beginning of the upkeep of enchanted creature's controller, that player draws a card.",
  ]

def superSuit : CardDef :=
  fromOracle [
    "Super Suit",
    "{1}{U}",
    "Artifact — Equipment",
    "Flash",
    "When this Equipment enters, attach it to target creature you control. Untap that creature.",
    "Equipped creature gets +1/+2.",
    "Equip {2} ({2}: Attach to target creature you control. Equip only as a sorcery.)",
  ]

def thirstForKnowledge : CardDef :=
  fromOracle [
    "Thirst for Knowledge",
    "{2}{U}",
    "Instant",
    "Draw three cards. Then discard two cards unless you discard an artifact card.",
  ]

def tonyStark : CardDef :=
  fromOracle [
    "Tony Stark",
    "{1}{U}",
    "Legendary Creature — Human Artificer Hero",
    "1/3",
    "{1}, {T}: Look at the top four cards of your library. You may reveal an artifact card from among them and put it into your hand. Put the rest on the bottom of your library in a random order.",
    "{4}{U}{R}: Transform Tony Stark. Activate only as a sorcery.",
    "//",
    "The Invincible Iron Man",
    "{4}{U}{R}",
    "Legendary Artifact Creature — Human Hero",
    "5/5",
    "Flying, haste",
    "At the beginning of combat on your turn, you may put an artifact card from your hand onto the battlefield. If it's an Equipment, attach it to The Invincible Iron Man.",
  ]

def tricksterSStratagem : CardDef :=
  fromOracle [
    "Trickster's Stratagem",
    "{3}{U}",
    "Sorcery",
    "The owner of target creature an opponent controls puts it into their library second from the top or on the bottom. Then up to one target creature you control connives. (Draw a card, then discard a card. If you discarded a nonland card, put a +1/+1 counter on that creature.)",
  ]

def weSayTheeNay : CardDef :=
  fromOracle [
    "We Say Thee Nay!",
    "{1}{U}",
    "Instant — Arcane",
    "Teamwork 2 (As an additional cost to cast this spell, you may tap any number of creatures you control with total power 2 or more.)",
    "Counter target spell unless its controller pays {2}. Counter that spell unless its controller pays {4} instead if this spell was cast using teamwork.",
  ]

def wiccanRisingMagician : CardDef :=
  fromOracle [
    "Wiccan, Rising Magician",
    "{4}{U}",
    "Legendary Creature — Mutant Warlock Hero",
    "4/4",
    "Flying",
    "Whenever you cast a noncreature spell, exile another target nonland, nontoken permanent. Return that card to the battlefield under its owner's control at the beginning of the next end step.",
  ]

def theWondrousWasp : CardDef :=
  fromOracle [
    "The Wondrous Wasp",
    "{1}{U}",
    "Legendary Creature — Human Hero",
    "2/1",
    "Flash",
    "Flying",
    "Wasp's Sting — When The Wondrous Wasp enters, tap up to one target creature. It loses all abilities for as long as The Wondrous Wasp remains on the battlefield.",
  ]

def agentsOfHYDRA : CardDef :=
  fromOracle [
    "Agents of HYDRA",
    "{1}{B}",
    "Creature — Human Spy Villain",
    "1/1",
    "When this creature dies, create a 2/1 black Villain creature token with menace. (It can't be blocked except by two or more creatures.)",
  ]

def arnimZolaBioFanatic : CardDef :=
  fromOracle [
    "Arnim Zola, Bio-Fanatic",
    "{2}{B}",
    "Legendary Artifact Creature — Scientist Villain",
    "2/3",
    "{3}, {T}: Create a tapped 2/1 black Villain creature token with menace. Activate only if there are two or more creature cards in your graveyard. (It can't be blocked except by two or more creatures.)",
  ]

def baronHelmutZemo : CardDef :=
  fromOracle [
    "Baron Helmut Zemo",
    "{B}{B}{B}",
    "Legendary Creature — Human Noble Villain",
    "3/3",
    "Whenever you cast a black spell from your hand, Baron Helmut Zemo connives.",
    "Boast — Exile any number of black cards from your graveyard with fifteen or more black mana symbols among their mana costs: Copy those exiled cards. You may cast up to three of the copies without paying their mana costs. (Activate only if this creature attacked this turn and only once each turn.)",
  ]

def baronStruckerHYDRAOverlord : CardDef :=
  fromOracle [
    "Baron Strucker, HYDRA Overlord",
    "{2}{B}",
    "Legendary Creature — Human Villain",
    "2/2",
    "Villain spells you cast cost {1} less to cast.",
    "Whenever another Villain you control enters, you may have it connive. Do this only once each turn. (Draw a card, then discard a card. If you discarded a nonland card, put a +1/+1 counter on that creature.)",
  ]

def blackWidowSuperSpy : CardDef :=
  fromOracle [
    "Black Widow, Super Spy",
    "{1}{B}",
    "Legendary Creature — Human Spy Hero",
    "2/1",
    "Menace",
    "Whenever Black Widow deals combat damage to a player, that player exiles cards from the top of their library until they exile a nonland card. You may put a +1/+1 counter on Black Widow. If you don't, you may cast the exiled nonland card until end of turn and mana of any type can be spent to cast that spell.",
  ]

def constructACosmicCube : CardDef :=
  fromOracle [
    "Construct a Cosmic Cube",
    "{2}{B}",
    "Enchantment — Plan",
    "Whenever you draw your second card each turn, create a 2/1 black Villain creature token with menace and put a plan counter on this enchantment.",
    "When the seventh plan counter is put on this enchantment, sacrifice it. When you do, you control target opponent during their next turn. (You see all cards that player could see and make all decisions for them.)",
  ]

def crossbonesMaliciousMercenary : CardDef :=
  fromOracle [
    "Crossbones, Malicious Mercenary",
    "{3}{B}",
    "Legendary Creature — Human Mercenary Villain",
    "3/3",
    "Deathtouch",
    "Whenever another Villain you control enters, put a +1/+1 counter on Crossbones. He deals 2 damage to each opponent. This ability triggers only once each turn.",
  ]

def cruelAlliance : CardDef :=
  fromOracle [
    "Cruel Alliance",
    "{2}{B}",
    "Sorcery",
    "Teamwork 2 (As an additional cost to cast this spell, you may tap any number of creatures you control with total power 2 or more.)",
    "Exile target creature with mana value 3 or less. If this spell was cast using teamwork, instead exile target creature and you gain 3 life.",
  ]

def darkDeed : CardDef :=
  fromOracle [
    "Dark Deed",
    "{1}{B}",
    "Instant",
    "Target creature gets -4/-4 until end of turn.",
  ]

def decoyPloy : CardDef :=
  fromOracle [
    "Decoy Ploy",
    "{1}{B}",
    "Instant",
    "Choose one or both —",
    "• Return target Villain card from your graveyard to your hand.",
    "• Return target Hero card from your graveyard to your hand.",
  ]

def doctorDoom : CardDef :=
  fromOracle [
    "Doctor Doom",
    "{4}{B}{B}",
    "Legendary Creature — Human Scientist Villain",
    "3/3",
    "When Doctor Doom enters, create two 3/3 colorless Robot Villain artifact creature tokens named Doombot.",
    "As long as you control an artifact creature or a Plan, Doctor Doom has indestructible.",
    "At the beginning of your end step, you draw a card and lose 1 life.",
  ]

def doomReignsSupreme : CardDef :=
  fromOracle [
    "Doom Reigns Supreme",
    "{1}{B}",
    "Enchantment — Plan",
    "Whenever a Villain you control enters, each opponent loses 1 life and you gain 1 life. Put a plan counter on this enchantment.",
    "When the fifth plan counter is put on this enchantment, sacrifice it. When you do, target opponent exiles the top five cards of their library. You may cast up to two spells from among the exiled cards without paying their mana costs.",
  ]

def elektraDaughterOfTheHand : CardDef :=
  fromOracle [
    "Elektra, Daughter of the Hand",
    "{2}{B}{B}",
    "Legendary Creature — Human Ninja Villain",
    "3/3",
    "Sneak {1}{B}{B} (You may cast this spell for {1}{B}{B} if you also return an unblocked attacker you control to hand during the declare blockers step. She enters tapped and attacking.)",
    "When Elektra enters, destroy target creature an opponent controls with power 3 or less.",
  ]

def grimReaperLethalLegionnaire : CardDef :=
  fromOracle [
    "Grim Reaper, Lethal Legionnaire",
    "{3}{B}",
    "Legendary Creature — Human Villain",
    "3/4",
    "Whenever Grim Reaper attacks, you may pay {3}{B}. When you do, return target creature card from your graveyard to the battlefield tapped and attacking with a finality counter on it. (If a creature with a finality counter on it would die, exile it instead.)",
  ]

def hourOfDefeat : CardDef :=
  fromOracle [
    "Hour of Defeat",
    "{3}{B}",
    "Instant",
    "Destroy target creature. Surveil 1. (Look at the top card of your library. You may put it into your graveyard.)",
  ]

def hYDRAInfiltration : CardDef :=
  fromOracle [
    "HYDRA Infiltration",
    "{3}{B}",
    "Enchantment",
    "When this enchantment enters, target opponent discards two cards.",
    "Whenever a creature you control attacks alone, target opponent loses 1 life and you gain 1 life.",
  ]

def hYDRATroopers : CardDef :=
  fromOracle [
    "HYDRA Troopers",
    "{2}{B}",
    "Creature — Human Soldier Villain",
    "3/2",
    "When this creature enters, create a tapped 2/1 black Villain creature token with menace if there are two or more creature cards in your graveyard. Otherwise, mill two cards. (Put the top two cards of your library into your graveyard.)",
  ]

def kingpinSEnforcers : CardDef :=
  fromOracle [
    "Kingpin's Enforcers",
    "{2}{B}",
    "Creature — Human Villain",
    "2/3",
    "Lifelink",
    "{2}{B}, Sacrifice an artifact or creature: Draw a card.",
  ]

def klawSonicSubjugator : CardDef :=
  fromOracle [
    "Klaw, Sonic Subjugator",
    "{2}{B}",
    "Legendary Creature — Human Rogue Villain",
    "2/2",
    "Sonic Attack — When Klaw enters, target player reveals a number of cards from their hand equal to one plus the number of creature cards in your graveyard. You choose one of them. That player discards that card.",
  ]

def madameMasque : CardDef :=
  fromOracle [
    "Madame Masque",
    "{4}{B}",
    "Legendary Creature — Human Villain",
    "3/2",
    "When Madame Masque enters, she connives. (Draw a card, then discard a card. If you discarded a nonland card, put a +1/+1 counter on this creature.)",
    "Whenever you draw your second card each turn, create a 2/1 black Villain creature token with menace. (It can't be blocked except by two or more creatures.)",
  ]

def theMastersOfEvil : CardDef :=
  fromOracle [
    "The Masters of Evil",
    "{5}{B}",
    "Legendary Creature — Human Villain",
    "5/6",
    "Other Villains you control get +2/+1.",
    "{1}{B}, Discard this card: Search your library for a Plan card, reveal it, put it into your hand, then shuffle.",
  ]

def mODOK : CardDef :=
  fromOracle [
    "M.O.D.O.K.",
    "{3}{B}{B}",
    "Legendary Artifact Creature — Villain",
    "2/2",
    "Flying, lifelink",
    "Mental Organism — Pay 3 life: M.O.D.O.K. connives. Activate only during your turn. (Draw a card, then discard a card. If you discarded a nonland card, put a +1/+1 counter on this creature.)",
    "Designed Only for Killing — Creatures your opponents control get -1/-1.",
  ]

def moonstoneHarshMistress : CardDef :=
  fromOracle [
    "Moonstone, Harsh Mistress",
    "{3}{B}",
    "Legendary Creature — Human Doctor Villain",
    "2/4",
    "Flying",
    "Whenever you discard a card, you may exile that card from your graveyard. If you do, until the end of your next turn, you may play that card.",
  ]

def ninjaOfTheHand : CardDef :=
  fromOracle [
    "Ninja of the Hand",
    "{2}{B}",
    "Creature — Human Ninja Villain",
    "2/2",
    "Deathtouch",
    "Power-up — {4}{B}: Each opponent discards a card. Put a +1/+1 counter on this creature. (Activate each power-up ability only once. Reduce the cost by its mana cost if it entered this turn.)",
  ]

def projectDeathlokSoldier : CardDef :=
  fromOracle [
    "Project Deathlok Soldier",
    "{B}",
    "Artifact Creature — Zombie Soldier",
    "1/2",
    "{2}{B}: Return this card from your graveyard to your hand.",
  ]

def redRoomRecruit : CardDef :=
  fromOracle [
    "Red Room Recruit",
    "{1}{B}",
    "Creature — Human Spy Villain",
    "1/2",
    "When this creature enters, it connives. (Draw a card, then discard a card. If you discarded a nonland card, put a +1/+1 counter on this creature.)",
  ]

def robotDomination : CardDef :=
  fromOracle [
    "Robot Domination",
    "{3}{B}",
    "Enchantment — Plan",
    "Whenever one or more creature cards are put into your graveyard from anywhere, you draw a card, lose 1 life, and put a plan counter on this enchantment.",
    "When the third plan counter is put on this enchantment, sacrifice it and create three 2/2 colorless Robot Villain artifact creature tokens.",
  ]

def roninShadowStalker : CardDef :=
  fromOracle [
    "Ronin, Shadow Stalker",
    "{2}{B}",
    "Legendary Creature — Human Rogue Hero",
    "3/3",
    "Pay 2 life: Add two mana of any one color. Spend this mana only to cast Equipment spells or activate equip abilities. Activate only once each turn.",
    "{T}, Sacrifice an Equipment attached to Ronin: Target creature gets -4/-4 until end of turn. Activate only as a sorcery.",
  ]

def roxxonBrutes : CardDef :=
  fromOracle [
    "Roxxon Brutes",
    "{4}{B}",
    "Creature — Human Berserker Villain",
    "4/4",
    "Menace (This creature can't be blocked except by two or more creatures.)",
    "Whenever you draw your second card each turn, put a +1/+1 counter on target creature.",
    "Basic landcycling {2} ({2}, Discard this card: Search your library for a basic land card, reveal it, put it into your hand, then shuffle.)",
  ]

def stolenStarkTech : CardDef :=
  fromOracle [
    "Stolen Stark Tech",
    "{1}{B}",
    "Artifact — Equipment",
    "Flash",
    "When this Equipment enters, attach it to target creature you control. That creature gains indestructible until end of turn. (Damage and effects that say \"destroy\" don't destroy it.)",
    "Equipped creature gets +1/+0.",
    "Equip {1} ({1}: Attach to target creature you control. Equip only as a sorcery.)",
  ]

def superSkrull : CardDef :=
  fromOracle [
    "Super-Skrull",
    "{1}{B}{B}{B}",
    "Legendary Creature — Skrull Shapeshifter Villain",
    "4/5",
    "Flying",
    "{2}{W}: Create a 0/4 colorless Wall creature token with defender.",
    "{3}{G}: Super-Skrull gets +4/+4 until end of turn.",
    "{4}{R}: Super-Skrull deals 4 damage to target creature.",
    "{5}{U}: Target player draws four cards.",
  ]

def swordsmanSharpScoundrel : CardDef :=
  fromOracle [
    "Swordsman, Sharp Scoundrel",
    "{1}{B}",
    "Legendary Creature — Human Hero Villain",
    "2/2",
    "Whenever another Villain you control enters, attach up to one target Equipment you control to target creature you control.",
    "Whenever an equipped creature you control attacks, it connives. (Draw a card, then discard a card. If you discarded a nonland card, put a +1/+1 counter on that creature.)",
  ]

def thunderboltsConspiracy : CardDef :=
  fromOracle [
    "Thunderbolts Conspiracy",
    "{3}{B}",
    "Enchantment",
    "Flash",
    "Whenever a Villain you control dies, return it to the battlefield under its owner's control with a finality counter on it. That creature is a Hero in addition to its other types. (If a creature with a finality counter on it would die, exile it instead.)",
  ]

def tooEvilToStayDead : CardDef :=
  fromOracle [
    "Too Evil to Stay Dead",
    "{2}{B}",
    "Sorcery",
    "Teamwork 4 (As an additional cost to cast this spell, you may tap any number of creatures you control with total power 4 or more.)",
    "Choose target creature card in your graveyard with mana value 4 or less. If this spell was cast using teamwork, instead choose target creature card in your graveyard. Return the chosen card to the battlefield.",
  ]

def unlivingLegionnaire : CardDef :=
  fromOracle [
    "Unliving Legionnaire",
    "{3}{B}",
    "Creature — Vampire Villain",
    "3/2",
    "Flying",
    "Power-up — {5}{B}{B}: Return up to one target creature card from your graveyard to your hand. Put two +1/+1 counters on this creature. (Activate each power-up ability only once. Reduce the cost by its mana cost if it entered this turn.)",
  ]

def visionsOfVillainy : CardDef :=
  fromOracle [
    "Visions of Villainy",
    "{2}{B}",
    "Instant",
    "This spell costs {1} less to cast if you control a Villain.",
    "You draw two cards and lose 2 life.",
  ]

def whiplashVengefulEngineer : CardDef :=
  fromOracle [
    "Whiplash, Vengeful Engineer",
    "{B}",
    "Legendary Creature — Human Artificer Villain",
    "2/2",
    "Whiplash enters tapped.",
    "Whenever Whiplash attacks, if he's equipped, each opponent loses X life and you gain X life, where X is the number of Equipment attached to him.",
  ]

def widowSBite : CardDef :=
  fromOracle [
    "Widow's Bite",
    "{1}{B}",
    "Instant",
    "Teamwork 3 (As an additional cost to cast this spell, you may tap any number of creatures you control with total power 3 or more.)",
    "Choose one. If this spell was cast using teamwork, choose both instead.",
    "• Target creature gains deathtouch until end of turn.",
    "• Target creature gets -2/-2 until end of turn.",
  ]

def yellowjacketHeartlessMarauder : CardDef :=
  fromOracle [
    "Yellowjacket, Heartless Marauder",
    "{1}{B}",
    "Legendary Creature — Human Rogue Villain",
    "1/2",
    "Flying",
    "Whenever another Villain you control enters, Yellowjacket gets +1/+0 and gains lifelink until end of turn.",
  ]

def avengersDisassembled : CardDef :=
  fromOracle [
    "Avengers Disassembled",
    "{1}{R}{R}",
    "Sorcery",
    "Choose one or both —",
    "• Avengers Disassembled deals 3 damage to each creature.",
    "• Destroy target land. Its controller may search their library for a basic land card, put it onto the battlefield tapped, then shuffle.",
  ]

def blazingCrescendo : CardDef :=
  fromOracle [
    "Blazing Crescendo",
    "{1}{R}",
    "Instant",
    "Target creature gets +3/+1 until end of turn.",
    "Exile the top card of your library. Until the end of your next turn, you may play that card.",
  ]

def crimsonOperative : CardDef :=
  fromOracle [
    "Crimson Operative",
    "{3}{R}",
    "Artifact Creature — Human Villain",
    "3/2",
    "Prowess (Whenever you cast a noncreature spell, this creature gets +1/+1 until end of turn.)",
    "When this creature enters, exile the top card of your library. Until the end of your next turn, you may play that card.",
  ]

def deathToOurEnemies : CardDef :=
  fromOracle [
    "Death to Our Enemies",
    "{2}{R}",
    "Enchantment — Plan",
    "Whenever you cast a noncreature spell, create a tapped Treasure token and put a plan counter on this enchantment.",
    "When the fourth plan counter is put on this enchantment, sacrifice it. When you do, it deals 7 damage divided as you choose among one or two targets.",
  ]

def evilSThrall : CardDef :=
  fromOracle [
    "Evil's Thrall",
    "{2}{R}",
    "Sorcery",
    "Gain control of target creature until end of turn. If you control a Villain with greater mana value than that creature, gain control of that creature until the end of your next turn instead. Untap that creature. It gains haste until end of turn.",
  ]

def finFangFoom : CardDef :=
  fromOracle [
    "Fin Fang Foom",
    "{2}{R}{R}",
    "Legendary Creature — Alien Dragon Villain",
    "3/5",
    "Flying",
    "Whenever you cast an instant or sorcery spell that targets an artifact or land, copy that spell. You may choose new targets for the copy. Put two +1/+1 counters on Fin Fang Foom.",
  ]

def hawkeyeMasterMarksman : CardDef :=
  fromOracle [
    "Hawkeye, Master Marksman",
    "{1}{R}",
    "Legendary Creature — Human Archer Hero",
    "2/2",
    "Reach, first strike",
    "Trick Arrows — Whenever Hawkeye becomes tapped, you may pay {1} up to three times. When you do, choose up to that many —",
    "• Net — Target creature can't block this turn.",
    "• Explosive — Hawkeye deals 2 damage to target player.",
    "• Boomerang — Discard a card, then draw a card.",
  ]

def hawkeyeYoungAvenger : CardDef :=
  fromOracle [
    "Hawkeye, Young Avenger",
    "{3}{R}",
    "Legendary Creature — Human Archer Hero",
    "2/4",
    "Reach",
    "If a source you control would deal noncombat damage to an opponent or a permanent an opponent controls, instead it deals that much damage plus X, where X is Hawkeye's power.",
  ]

def hawkeyeSBow : CardDef :=
  fromOracle [
    "Hawkeye's Bow",
    "{R}",
    "Artifact — Equipment",
    "Equipped creature gets +1/+0 and has reach.",
    "Whenever equipped creature becomes tapped, it deals 1 damage to each opponent.",
    "Equip {1}",
  ]

def hexMagic : CardDef :=
  fromOracle [
    "Hex Magic",
    "{2}{R}",
    "Sorcery — Arcane",
    "Exile all the cards from your hand, then draw that many cards. Until the end of your next turn, you may play cards exiled this way.",
  ]

def hireACrew : CardDef :=
  fromOracle [
    "Hire a Crew",
    "{2}{R}",
    "Instant",
    "Create a 2/1 black Villain creature token with menace, then creatures you control get +1/+0 until end of turn. (A creature with menace can't be blocked except by two or more creatures.)",
  ]

def hULKSMASH : CardDef :=
  fromOracle [
    "HULK SMASH!",
    "{1}{R}",
    "Instant",
    "Teamwork 4 (As an additional cost to cast this spell, you may tap any number of creatures you control with total power 4 or more.)",
    "Choose one. If this spell was cast using teamwork, choose both instead.",
    "• Destroy target noncreature artifact.",
    "• Target creature you control deals damage equal to its power to target creature an opponent controls.",
  ]

def humanTorchJohnnyStorm : CardDef :=
  fromOracle [
    "Human Torch, Johnny Storm",
    "{2}{R}",
    "Legendary Creature — Human Hero",
    "2/2",
    "Flying",
    "Whenever you draw a card, if you control another Hero, Human Torch deals 1 damage to target opponent.",
    "Power-up — {6}{R}: Put three +1/+1 counters on Human Torch. (Activate each power-up ability only once. Reduce the cost by his mana cost if he entered this turn.)",
  ]

def hYDRAAssaultRobot : CardDef :=
  fromOracle [
    "HYDRA Assault Robot",
    "{1}{R}",
    "Artifact Creature — Robot Villain",
    "1/3",
    "Whenever another Villain and/or artifact you control enters, this creature deals 1 damage to target opponent.",
  ]

def ironFistLivingWeapon : CardDef :=
  fromOracle [
    "Iron Fist, Living Weapon",
    "{2}{R}",
    "Legendary Creature — Human Warrior Hero",
    "2/3",
    "Whenever you cast a spell that targets a creature you control, Iron Fist gains \"{T}: Iron Fist deals damage equal to his power to any other target\" until end of turn.",
  ]

def jessicaJonesPrivateEye : CardDef :=
  fromOracle [
    "Jessica Jones, Private Eye",
    "{2}{R}",
    "Legendary Creature — Human Detective Hero",
    "2/3",
    "{T}, Put a stun counter on Jessica Jones: Exile the top X cards of your library, where X is Jessica Jones's power. You may play those cards this turn. (If a permanent with a stun counter would become untapped, remove one from it instead.)",
  ]

def kUnLunWarrior : CardDef :=
  fromOracle [
    "K'un-Lun Warrior",
    "{1}{R}",
    "Creature — Human Warrior Hero",
    "2/2",
    "When this creature enters, you may sacrifice an artifact or discard a card. If you do, draw a card.",
  ]

def kreeSentinel : CardDef :=
  fromOracle [
    "Kree Sentinel",
    "{4}{R}",
    "Artifact Creature — Kree Robot Villain",
    "5/5",
    "Reach",
    "Basic landcycling {2} ({2}, Discard this card: Search your library for a basic land card, reveal it, put it into your hand, then shuffle.)",
  ]

def lightningStrike : CardDef :=
  fromOracle [
    "Lightning Strike",
    "{1}{R}",
    "Instant",
    "Lightning Strike deals 3 damage to any target.",
  ]

def lokiLaufeyson : CardDef :=
  fromOracle [
    "Loki Laufeyson",
    "{1}{R}",
    "Legendary Creature — God Sorcerer Villain",
    "2/1",
    "{1}, {T}: When you next cast an instant or sorcery spell with mana value less than or equal to Loki's power this turn, copy that spell. You may choose new targets for the copy.",
    "Power-up — {4}{R}: Put two +1/+1 counters on Loki. (Activate each power-up ability only once. Reduce the cost by his mana cost if he entered this turn.)",
  ]

def machinesmithAutomaton : CardDef :=
  fromOracle [
    "Machinesmith Automaton",
    "{2}{R}",
    "Artifact Creature — Robot Villain",
    "2/2",
    "Trample",
    "Whenever another artifact you control enters, put a +1/+1 counter on this creature.",
  ]

def mistyKnightHeroForHire : CardDef :=
  fromOracle [
    "Misty Knight, Hero for Hire",
    "{1}{R}",
    "Legendary Creature — Human Detective Hero",
    "3/1",
    "{2}, {T}, Discard a card: Draw a card for each card you've discarded this turn.",
  ]

def mjLnirHammerOfThor : CardDef :=
  fromOracle [
    "Mjölnir, Hammer of Thor",
    "{3}{R}",
    "Legendary Artifact — Equipment",
    "When Mjölnir enters, it deals 4 damage to up to one target creature.",
    "Double all damage equipped creature would deal.",
    "Equip worthy {1} (A creature is worthy if it's a legendary non-Villain that's red and/or white.)",
    "{2}{R}, Discard this card: It deals 2 damage to each creature.",
  ]

def photonBlastBarrage : CardDef :=
  fromOracle [
    "Photon Blast Barrage",
    "{X}{R}{R}",
    "Sorcery",
    "When you cast this spell, copy it X times. You may choose new targets for the copies.",
    "Photon Blast Barrage deals 1 damage to target creature.",
  ]

def quicksilverBrashBlur : CardDef :=
  fromOracle [
    "Quicksilver, Brash Blur",
    "{R}",
    "Legendary Creature — Mutant Hero",
    "1/1",
    "If Quicksilver, Brash Blur is in your opening hand, you may begin the game with him on the battlefield.",
    "Haste",
    "Power-up — {4}{R}: Put a +1/+1 counter and a double strike counter on Quicksilver. (Activate each power-up ability only once. Reduce the cost by his mana cost if he entered this turn.)",
  ]

def redHulk : CardDef :=
  fromOracle [
    "Red Hulk",
    "{4}{R}{R}",
    "Legendary Creature — Gamma Berserker Villain",
    "6/7",
    "Reach, trample",
    "Enrage — Whenever Red Hulk is dealt damage, put a +1/+1 counter on him. When you do, he deals damage equal to the number of +1/+1 counters on him to any other target.",
  ]

def repulsorBlast : CardDef :=
  fromOracle [
    "Repulsor Blast",
    "{3}{R}",
    "Sorcery",
    "Teamwork 2 (As an additional cost to cast this spell, you may tap any number of creatures you control with total power 2 or more.)",
    "Repulsor Blast deals 5 damage to target creature. If this spell was cast using teamwork, it also deals 2 damage to that creature's controller.",
  ]

def theScarletWitch : CardDef :=
  fromOracle [
    "The Scarlet Witch",
    "{2}{R}",
    "Legendary Creature — Mutant Warlock Hero",
    "2/3",
    "Instant and sorcery spells you cast with mana value 4 or greater cost {X} less to cast, where X is The Scarlet Witch's power.",
  ]

def speedYoungAvenger : CardDef :=
  fromOracle [
    "Speed, Young Avenger",
    "{1}{R}",
    "Legendary Creature — Mutant Hero",
    "2/2",
    "Haste",
    "Whenever you cast a noncreature spell, you may pay {1}. When you do, target creature with haste can't be blocked this turn except by creatures with haste.",
  ]

def starkIndustriesExecutive : CardDef :=
  fromOracle [
    "Stark Industries Executive",
    "{R}",
    "Creature — Human Advisor",
    "1/2",
    "{2}, {T}: Create a Treasure token. (It's an artifact with \"{T}, Sacrifice this token: Add one mana of any color.\")",
  ]

def superSpeed : CardDef :=
  fromOracle [
    "Super Speed",
    "{R}",
    "Enchantment — Aura",
    "Flash",
    "Enchant creature",
    "When this Aura enters, enchanted creature gains first strike until end of turn.",
    "Enchanted creature gets +1/+0 and has haste.",
  ]

def teamTactics : CardDef :=
  fromOracle [
    "Team Tactics",
    "{1}{R}",
    "Instant",
    "Teamwork 1 (As an additional cost to cast this spell, you may tap any number of creatures you control with total power 1 or more.)",
    "Target creature gains double strike until end of turn. If this spell was cast using teamwork, that creature also gains trample until end of turn.",
  ]

def thorGodOfThunder : CardDef :=
  fromOracle [
    "Thor, God of Thunder",
    "{3}{R}{R}",
    "Legendary Creature — God Warrior Hero",
    "5/5",
    "Flying",
    "When Thor enters, exile target Equipment, instant, or sorcery card from your graveyard. Until the end of your next turn, you may play that card.",
    "Whenever you cast a noncreature spell, Thor deals damage equal to that spell's mana value to any target.",
  ]

def truckToss : CardDef :=
  fromOracle [
    "Truck Toss",
    "{2}{R}{R}",
    "Instant",
    "This spell costs {2} less to cast if you control a Vehicle.",
    "Truck Toss deals 4 damage to any target.",
  ]

def visionOfLove : CardDef :=
  fromOracle [
    "Vision of Love",
    "{1}{R}",
    "Instant",
    "You may sacrifice an artifact or discard a card. If you do, draw two cards.",
  ]

def volcanicVillain : CardDef :=
  fromOracle [
    "Volcanic Villain",
    "{2}{R}",
    "Creature — Elemental Villain",
    "3/2",
    "Haste",
    "Power-up — {5}{R}: Put two +1/+1 counters on this creature. (Activate each power-up ability only once. Reduce the cost by its mana cost if it entered this turn.)",
  ]

def wonderManHollywoodHero : CardDef :=
  fromOracle [
    "Wonder Man, Hollywood Hero",
    "{3}{R}{R}",
    "Legendary Creature — Human Performer Hero",
    "4/4",
    "Flying",
    "Each power-up ability of permanents you control can be activated an additional time.",
    "Power-up — {5}{R}{R}: Put two +1/+1 counters on Wonder Man. (Activate each power-up ability only . . . once? Reduce the cost by his mana cost if he entered this turn.)",
  ]

def antManSArmy : CardDef :=
  fromOracle [
    "Ant-Man's Army",
    "{2}{G}",
    "Creature — Insect",
    "3/2",
    "When this creature enters, create a Food token or a Treasure token. (A Food token is an artifact with \"{2}, {T}, Sacrifice this token: You gain 3 life.\" A Treasure token is an artifact with \"{T}, Sacrifice this token: Add one mana of any color.\")",
  ]

def callDamageControl : CardDef :=
  fromOracle [
    "Call Damage Control",
    "{1}{G}",
    "Sorcery",
    "Choose up to two. Return those cards from your graveyard to your hand.",
    "• Target artifact card.",
    "• Target creature card.",
    "• Target enchantment card.",
    "• Target land card.",
  ]

def claimTheKingdom : CardDef :=
  fromOracle [
    "Claim the Kingdom",
    "{1}{G}",
    "Enchantment — Plan",
    "Landfall — Whenever a land you control enters, put a +1/+1 counter on target creature you control and a plan counter on this enchantment.",
    "When the fourth plan counter is put on this enchantment, sacrifice it. When you do, put an indestructible counter on target creature you control.",
  ]

def docSamsonSuperPsychiatrist : CardDef :=
  fromOracle [
    "Doc Samson, Super Psychiatrist",
    "{4}{G}",
    "Legendary Creature — Gamma Doctor Hero",
    "3/6",
    "If you would put one or more counters on a permanent you control, put that many plus one of each of those kinds of counters on that permanent instead.",
    "{T}: Add X mana of any one color, where X is Doc Samson's power.",
  ]

def earthSMightiestHeroes : CardDef :=
  fromOracle [
    "Earth's Mightiest Heroes",
    "{4}{G}{G}",
    "Sorcery",
    "Teamwork 5 (As an additional cost to cast this spell, you may tap any number of creatures you control with total power 5 or more.)",
    "Reveal the top eight cards of your library. You may put a creature card from among them onto the battlefield. If this spell was cast using teamwork, put any number of creature cards from among them onto the battlefield instead. Put the rest into your graveyard.",
  ]

def epicFight : CardDef :=
  fromOracle [
    "Epic Fight",
    "{2}{G}",
    "Sorcery",
    "Choose one or both —",
    "• Double target creature's power and toughness until end of turn.",
    "• Target creature you control fights target creature an opponent controls.",
  ]

def goNuts : CardDef :=
  fromOracle [
    "Go Nuts!",
    "{G}",
    "Sorcery",
    "Teamwork 3 (As an additional cost to cast this spell, you may tap any number of creatures you control with total power 3 or more.)",
    "Choose one. If this spell was cast using teamwork, choose both instead.",
    "• Put a +1/+1 counter on target creature.",
    "• Target creature you control fights target creature an opponent controls.",
  ]

def guerrillaGorilla : CardDef :=
  fromOracle [
    "Guerrilla Gorilla",
    "{1}{G}",
    "Creature — Ape Soldier Hero",
    "2/2",
    "Reach",
    "Sacrifice this creature: Destroy target noncreature artifact or noncreature enchantment. Activate only as a sorcery.",
  ]

def hellcatUndyingVigilante : CardDef :=
  fromOracle [
    "Hellcat, Undying Vigilante",
    "{G}{G}",
    "Legendary Creature — Human Hero",
    "2/2",
    "Haste",
    "When Hellcat dies, return her to the battlefield under her owner's control with a +1/+1 counter on her. She loses all abilities and gains haste.",
  ]

def herculesPrinceOfPower : CardDef :=
  fromOracle [
    "Hercules, Prince of Power",
    "{2}{G}",
    "Legendary Creature — Demigod Warrior Hero",
    "3/3",
    "Power-up — {4}{G}: Put a +1/+1 counter on Hercules. He gains vigilance, indestructible, and haste until end of turn. (Activate each power-up ability only once. Reduce the cost by his mana cost if he entered this turn.)",
  ]

def heroicFeast : CardDef :=
  fromOracle [
    "Heroic Feast",
    "{2}{G}",
    "Enchantment",
    "When this enchantment enters, create a Food token. (It's an artifact with \"{2}, {T}, Sacrifice this token: You gain 3 life.\")",
    "Whenever you gain life, choose up to that many target creatures you control. Put a +1/+1 counter on each of them.",
  ]

def hulklingBurgeoningBruiser : CardDef :=
  fromOracle [
    "Hulkling, Burgeoning Bruiser",
    "{2}{G}",
    "Legendary Creature — Kree Skrull Hero",
    "2/3",
    "Vigilance",
    "Whenever another creature you control enters, if it has greater power or toughness than Hulkling, put a +1/+1 counter on Hulkling.",
  ]

def kaZarOfTheSavageLand : CardDef :=
  fromOracle [
    "Ka-Zar of the Savage Land",
    "{4}{G}",
    "Legendary Creature — Human Barbarian Hero",
    "3/2",
    "You may look at the top card of your library any time.",
    "You may play lands from the top of your library.",
    "When Ka-Zar enters, create Zabu, a legendary 2/2 green Cat creature token with \"Landfall — Whenever a land you control enters, put a +1/+1 counter on Zabu.\"",
  ]

def knightOfWundagore : CardDef :=
  fromOracle [
    "Knight of Wundagore",
    "{1}{G}",
    "Creature — Cat Knight Villain",
    "2/1",
    "Trample",
    "Whenever you put a +1/+1 counter on another creature, put a +1/+1 counter on this creature. This ability triggers only once each turn.",
  ]

def misterHydeMonsterWithin : CardDef :=
  fromOracle [
    "Mister Hyde, Monster Within",
    "{2}{G}",
    "Legendary Creature — Human Villain",
    "2/2",
    "At the beginning of your upkeep, choose one —",
    "• Put a +1/+1 counter on Mister Hyde.",
    "• Remove a counter from a creature you control. If you do, draw a card.",
  ]

def moleManMoloidMaster : CardDef :=
  fromOracle [
    "Mole Man, Moloid Master",
    "{2}{G}",
    "Legendary Creature — Human Villain",
    "1/1",
    "You may play lands from your graveyard.",
    "Landfall — Whenever a land you control enters, create a 1/1 green Minion creature token named Moloid with \"Whenever this token attacks, you may mill a card.\"",
  ]

def petAvengers : CardDef :=
  fromOracle [
    "Pet Avengers",
    "{3}{G}",
    "Creature — Dragon Cat Dog Bird Frog Hero",
    "4/4",
    "Reach",
    "Power-up — {6}{G}: Put a +1/+1 counter on this creature and create a 3/2 white Hero creature token with vigilance. (Activate each power-up ability only once. Reduce the cost by its mana cost if it entered this turn.)",
  ]

def powerfulBroker : CardDef :=
  fromOracle [
    "Powerful Broker",
    "{2}{G}",
    "Creature — Human Villain",
    "3/3",
    "{T}: For each kind of counter on target permanent or player, give that permanent or player another counter of that kind. Activate only as a sorcery.",
  ]

def punishingPunch : CardDef :=
  fromOracle [
    "Punishing Punch",
    "{2}{G}",
    "Instant",
    "This spell costs {2} less to cast if there are two or more creature cards in your graveyard.",
    "Target creature you control deals damage equal to twice its power to target creature an opponent controls.",
  ]

def rapidRescue : CardDef :=
  fromOracle [
    "Rapid Rescue",
    "{G}",
    "Instant",
    "Mill two cards. You may put a permanent card from among the milled cards into your hand. You gain 2 life. (To mill two cards, put the top two cards of your library into your graveyard.)",
  ]

def reptilDinomorpher : CardDef :=
  fromOracle [
    "Reptil, Dinomorpher",
    "{G}",
    "Legendary Creature — Human Hero",
    "1/2",
    "Brontosaurus — {3}: Until end of turn, Reptil becomes a Dinosaur Hero with base power and toughness 3/5 and gains reach and vigilance.",
    "Tyrannosaurus Rex — {6}: Until end of turn, Reptil becomes a Dinosaur Hero with base power and toughness 6/6 and gains trample.",
  ]

def restorativeTechnique : CardDef :=
  fromOracle [
    "Restorative Technique",
    "{2}{G}",
    "Sorcery",
    "Target player gains 2 life, then searches their library for a basic land card, puts it onto the battlefield tapped, then shuffles. Put a +1/+1 counter on up to one target creature.",
  ]

def rickJonesDestinedSidekick : CardDef :=
  fromOracle [
    "Rick Jones, Destined Sidekick",
    "{G}",
    "Legendary Creature — Human Advisor",
    "0/3",
    "{3}, {T}: Mill four cards. You may put a Hero or enchantment card from among those cards into your hand. (To mill four cards, put the top four cards of your library into your graveyard.)",
  ]

def savageLandDinosaur : CardDef :=
  fromOracle [
    "Savage Land Dinosaur",
    "{4}{G}{G}",
    "Creature — Dinosaur",
    "7/6",
    "Trample",
    "Basic landcycling {2} ({2}, Discard this card: Search your library for a basic land card, reveal it, put it into your hand, then shuffle.)",
  ]

def serpentSpecialist : CardDef :=
  fromOracle [
    "Serpent Specialist",
    "{G}",
    "Creature — Human Snake Villain",
    "1/1",
    "Deathtouch",
    "Power-up — {3}{G}: Put two +1/+1 counters on this creature. (Activate each power-up ability only once. Reduce the cost by its mana cost if it entered this turn.)",
  ]

def shangChiMasterOfKungFu : CardDef :=
  fromOracle [
    "Shang-Chi, Master of Kung Fu",
    "{1}{G}",
    "Legendary Creature — Human Warrior Hero",
    "2/2",
    "You may activate abilities of creatures you control as though those creatures had haste.",
    "{T}: Add two mana of any one color. Spend this mana only to activate abilities of creature sources.",
  ]

def sheHulkJadeDefender : CardDef :=
  fromOracle [
    "She-Hulk, Jade Defender",
    "{3}{G}",
    "Legendary Creature — Gamma Hero",
    "4/4",
    "Reach, trample",
    "Power-up — {4}{G}{G}: Destroy up to one target artifact or enchantment. Put a +1/+1 counter on She-Hulk. (Activate each power-up ability only once. Reduce the cost by her mana cost if she entered this turn.)",
  ]

def superStrength : CardDef :=
  fromOracle [
    "Super Strength",
    "{4}{G}",
    "Enchantment — Aura",
    "Enchant creature",
    "Enchanted creature gets +4/+4 and has trample and ward {1}. (Whenever enchanted creature becomes the target of a spell or ability an opponent controls, counter it unless that player pays {1}.)",
  ]

def theThingBenGrimm : CardDef :=
  fromOracle [
    "The Thing, Ben Grimm",
    "{5}{G}",
    "Legendary Creature — Human Hero",
    "7/7",
    "Trample",
    "Whenever one or more Heroes you control deal damage to a player, put two +1/+1 counters on The Thing.",
  ]

def tigraFelineFury : CardDef :=
  fromOracle [
    "Tigra, Feline Fury",
    "{1}{G}",
    "Legendary Creature — Cat Human Hero",
    "2/1",
    "Flash",
    "Trample",
    "Whenever you gain life, put a +1/+1 counter on Tigra.",
  ]

def trainingRegimen : CardDef :=
  fromOracle [
    "Training Regimen",
    "{3}{G}",
    "Enchantment",
    "Creatures you control with +1/+1 counters on them have trample.",
    "At the beginning of combat on your turn, put a +1/+1 counter on target creature you control.",
  ]

def theUnbeatableSquirrelGirl : CardDef :=
  fromOracle [
    "The Unbeatable Squirrel Girl",
    "{1}{G}{G}{G}",
    "Legendary Creature — Squirrel Human Hero",
    "4/4",
    "Do You Like Squirrels? — Whenever The Unbeatable Squirrel Girl enters or attacks, create a 1/1 green Squirrel creature token.",
    "I LOVE Squirrels! — {1}{G}{G}{G}: Create X 1/1 green Squirrel creature tokens, where X is the number of Squirrels you control.",
  ]

def undercoverSkrull : CardDef :=
  fromOracle [
    "Undercover Skrull",
    "{1}{G}",
    "Creature — Skrull Shapeshifter Villain",
    "1/1",
    "As long as there are two or more creature cards in your graveyard, this creature gets +2/+2 and is all creature types.",
    "{T}: Add one mana of any color.",
  ]

def wakandanRoyalGuard : CardDef :=
  fromOracle [
    "Wakandan Royal Guard",
    "{4}{G}",
    "Creature — Human Soldier Hero",
    "4/4",
    "Vigilance",
    "When this creature enters, put a +1/+1 counter on target creature. If that creature is another Hero, put two +1/+1 counters on it instead.",
  ]

def whiteTigerAvaAyala : CardDef :=
  fromOracle [
    "White Tiger, Ava Ayala",
    "{1}{G}",
    "Legendary Creature — Human Hero",
    "2/2",
    "Power-up — {5}{G}: Put a +1/+1 counter on White Tiger and create The Tiger God, a legendary 4/4 green Cat God creature token with \"The Tiger God can't be blocked by more than one creature.\" (Activate each power-up ability only once. Reduce the cost by her mana cost if she entered this turn.)",
  ]

def worldWarHulk : CardDef :=
  fromOracle [
    "World War Hulk",
    "{3}{G}{G}",
    "Enchantment — Saga",
    "(As this Saga enters and after your draw step, add a lore counter. Sacrifice after III.)",
    "I — The next red or green creature spell you cast this turn can be cast without paying its mana cost.",
    "II — Put three +1/+1 counters on target creature you control.",
    "III — Choose target creature you control. Until end of turn, double its power and toughness and it gains trample.",
  ]

def abominationTerrifyingTitan : CardDef :=
  fromOracle [
    "Abomination, Terrifying Titan",
    "{3}{R/G}",
    "Legendary Creature — Gamma Villain",
    "4/4",
    "Trample",
    "Power-up — {5}{R/G}{R/G}: Put a +1/+1 counter on Abomination. He fights up to one target creature an opponent controls. (Activate each power-up ability only once. Reduce the cost by his mana cost if he entered this turn.)",
  ]

def absorbingMan : CardDef :=
  fromOracle [
    "Absorbing Man",
    "{1}{G}{U}",
    "Legendary Creature — Human Villain",
    "4/4",
    "Vigilance",
    "At the beginning of your first main phase, until your next turn, Absorbing Man becomes a copy of up to one target artifact, non-Aura enchantment, or land, except his name is Absorbing Man, he's a legendary 4/4 Human Villain creature in addition to his other types, and he has vigilance.",
  ]

def alienInvasion : CardDef :=
  fromOracle [
    "Alien Invasion",
    "{1}{R}{R}{G}",
    "Enchantment",
    "At the beginning of combat on your turn, create a 1/1 red Alien creature token with haste and \"This token attacks each combat if able.\" Put a +1/+1 counter on it for each invasion counter on this enchantment, then put an invasion counter on this enchantment.",
  ]

def antManColonyCommander : CardDef :=
  fromOracle [
    "Ant-Man, Colony Commander",
    "{1}{G}{U}",
    "Legendary Creature — Human Rogue Hero",
    "2/2",
    "Whenever Ant-Man attacks, you may pay {1}. When you do, put a +1/+1 counter on target creature.",
    "Whenever you put a +1/+1 counter on a creature, create a 1/1 green Insect creature token. This ability triggers only once each turn.",
  ]

def aresGodOfWar : CardDef :=
  fromOracle [
    "Ares, God of War",
    "{1}{B}{R}",
    "Legendary Creature — God Warrior Villain",
    "4/3",
    "Ares attacks each combat if able.",
    "Whenever an attacking creature you control dies, return that card to its owner's hand.",
  ]

def armorWars : CardDef :=
  fromOracle [
    "Armor Wars",
    "{2}{U}{R}",
    "Enchantment — Saga",
    "(As this Saga enters and after your draw step, add a lore counter. Sacrifice after III.)",
    "I — You may draw a card for each artifact you control. If you do, each opponent draws a card.",
    "II — Artifact spells you cast this turn cost {1} less to cast.",
    "III — This Saga deals X damage to target opponent, where X is the greatest mana value among artifacts you control.",
  ]

def theAstonishingAntMan : CardDef :=
  fromOracle [
    "The Astonishing Ant-Man",
    "{G}{U}",
    "Legendary Creature — Human Scientist Hero",
    "1/1",
    "Whenever you draw a card, put a +1/+1 counter on The Astonishing Ant-Man.",
    "{2}{G}, {T}, Remove any number of +1/+1 counters from The Astonishing Ant-Man: Create that many 1/1 green Insect creature tokens.",
  ]

def avengersUnderSiege : CardDef :=
  fromOracle [
    "Avengers: Under Siege",
    "{2}{B}{R}",
    "Enchantment — Saga",
    "(As this Saga enters and after your draw step, add a lore counter. Sacrifice after III.)",
    "I — Create two 2/1 black Villain creature tokens with menace.",
    "II — This Saga deals 2 damage to each non-Villain creature and each opponent.",
    "III — Create a Treasure token for each Villain you control.",
  ]

def beastEruditeAerialist : CardDef :=
  fromOracle [
    "Beast, Erudite Aerialist",
    "{3}{G/U}",
    "Legendary Creature — Mutant Scientist Hero",
    "3/3",
    "As long as you've put one or more +1/+1 counters on Beast this turn, he has flying.",
    "Whenever Beast deals combat damage to a player, draw a card.",
  ]

def blackPantherVanguard : CardDef :=
  fromOracle [
    "Black Panther, Vanguard",
    "{2}{G}{W}",
    "Legendary Creature — Human Warrior Hero",
    "4/4",
    "Whenever another nontoken Hero you control enters, choose one —",
    "• Create a 1/1 white Soldier creature token.",
    "• Creatures you control get +1/+1 until end of turn.",
  ]

def blackWidowDoubleAgent : CardDef :=
  fromOracle [
    "Black Widow, Double Agent",
    "{1}{W}{B}",
    "Legendary Creature — Human Hero Villain",
    "3/2",
    "Deathtouch",
    "Whenever a creature you control attacks alone, it gains first strike and menace until end of turn. (It can't be blocked except by two or more creatures.)",
  ]

def bullseyeDeathDealer : CardDef :=
  fromOracle [
    "Bullseye, Death Dealer",
    "{2}{B/R}",
    "Legendary Creature — Human Assassin Villain",
    "2/3",
    "When Bullseye enters, you may sacrifice an artifact or discard a nonland card. When you do, Bullseye deals 2 damage to any target.",
    "{3}, {T}, Sacrifice an artifact or discard a nonland card: Bullseye deals 2 damage to any target.",
  ]

def captainAmericaLivingLegend : CardDef :=
  fromOracle [
    "Captain America, Living Legend",
    "{1}{W}{U}",
    "Legendary Creature — Human Soldier Hero",
    "3/4",
    "Vigilance",
    "Whenever a creature you control becomes tapped during your turn, if it's the first time that creature has become tapped this turn, untap it.",
  ]

def cloakAndDaggerEntwined : CardDef :=
  fromOracle [
    "Cloak and Dagger, Entwined",
    "{1}{W}{B}",
    "Legendary Creature — Human Hero",
    "2/2",
    "Deathtouch, lifelink",
    "When Cloak and Dagger enter, choose target opponent and up to one target creature they control. They reveal their hand. You may exile a nonland card from their hand or the chosen creature until Cloak and Dagger leave the battlefield.",
  ]

def theComingOfGalactus : CardDef :=
  fromOracle [
    "The Coming of Galactus",
    "{2}{B}{B}{G}",
    "Enchantment — Saga",
    "(As this Saga enters and after your draw step, add a lore counter. Sacrifice after IV.)",
    "I — Destroy up to one target nonland permanent.",
    "II, III — Each opponent loses 2 life.",
    "IV — Create Galactus, a legendary 16/16 black Elder Alien creature token with flying, trample, and \"Whenever Galactus attacks, destroy target land.\"",
  ]

def daredevilManWithoutFear : CardDef :=
  fromOracle [
    "Daredevil, Man Without Fear",
    "{2}{R}{W}",
    "Legendary Creature — Human Hero",
    "3/4",
    "Vigilance, haste",
    "Radar Sense — You may look at the top card of your library any time.",
    "Whenever you attack, you may exile the top card of your library. If that card is a Hero card, Daredevil gets +2/+1 until end of turn. You may play that card this turn.",
  ]

def ghostSpectralSaboteur : CardDef :=
  fromOracle [
    "Ghost, Spectral Saboteur",
    "{2}{U/B}",
    "Legendary Creature — Human Rogue Villain",
    "2/2",
    "Flash",
    "Intangibility — Ghost can't be blocked.",
  ]

def hulkGammaGoliath : CardDef :=
  fromOracle [
    "Hulk, Gamma Goliath",
    "{3}{R}{G}",
    "Legendary Creature — Gamma Berserker Hero",
    "6/5",
    "Reach, trample",
    "Power-up abilities of other creatures you control cost {3} less to activate.",
    "Power-up — {6}{R}{G}: Put five +1/+1 counters on Hulk. (Activate each power-up ability only once. Reduce the cost by his mana cost if he entered this turn.)",
  ]

def ironManMasterOfMachines : CardDef :=
  fromOracle [
    "Iron Man, Master of Machines",
    "{2}{U}{R}",
    "Legendary Artifact Creature — Human Hero",
    "1/4",
    "Flying, vigilance",
    "Iron Man gets +1/+0 for each other artifact you control.",
    "Whenever Iron Man attacks, if an artifact entered the battlefield under your control this turn, draw a card.",
  ]

def kangTemporalTyrant : CardDef :=
  fromOracle [
    "Kang, Temporal Tyrant",
    "{2}{U}{B}",
    "Legendary Creature — Human Villain",
    "3/4",
    "Whenever Kang attacks, he connives. (Draw a card, then discard a card. If you discarded a nonland card, put a +1/+1 counter on this creature.)",
    "Whenever you draw your second card each turn, each opponent loses 1 life and you gain 1 life.",
  ]

def killmongerScourgeOfWakanda : CardDef :=
  fromOracle [
    "Killmonger, Scourge of Wakanda",
    "{2}{B}{G}",
    "Legendary Creature — Human Mercenary Villain",
    "3/3",
    "When Killmonger enters, you may sacrifice another creature. When you do, destroy target nonland permanent an opponent controls.",
    "As long as there are two or more creature cards in your graveyard, Killmonger gets +2/+1.",
  ]

def kingTChalla : CardDef :=
  fromOracle [
    "King T'Challa",
    "{1}{W}{U}",
    "Legendary Creature — Human Noble Hero",
    "3/2",
    "Flash",
    "Whenever a player draws their second card each turn, you draw a card.",
    "{4}{W}{U}: Transform King T'Challa. Activate only as a sorcery.",
    "//",
    "Black Panther, Hope Enduring",
    "{4}{W}{U}",
    "Legendary Creature — Human Warrior Hero",
    "3/3",
    "Flash",
    "Double strike",
    "Prevent all damage that would be dealt to Black Panther.",
    "Whenever Black Panther deals combat damage to a player, draw a card.",
  ]

def theKingpinOfCrime : CardDef :=
  fromOracle [
    "The Kingpin of Crime",
    "{1}{W}{B}",
    "Legendary Creature — Human Villain",
    "1/5",
    "Extort (Whenever you cast a spell, you may pay {W/B}. If you do, each opponent loses 1 life and you gain that much life.)",
    "Whenever you attack, you may pay 2 life. If you do, until end of turn, creatures you control with toughness greater than their power assign combat damage equal to their toughness rather than their power.",
  ]

def madameHydra : CardDef :=
  fromOracle [
    "Madame Hydra",
    "{2}{B}{R}",
    "Legendary Creature — Human Villain",
    "2/3",
    "Whenever you cast a Villain spell, create a 2/1 black Villain creature token with menace. (It can't be blocked except by two or more creatures.)",
  ]

def theMightyThorJaneFoster : CardDef :=
  fromOracle [
    "The Mighty Thor, Jane Foster",
    "{1}{W}{U}",
    "Legendary Creature — Human God Hero",
    "3/3",
    "Flying",
    "Whenever The Mighty Thor attacks, exile up to one target nontoken artifact or creature, then return that card to the battlefield tapped under its owner's control.",
    "Whenever an Equipment you control enters, draw a card.",
  ]

def moonGirlAndDevilDinosaur : CardDef :=
  fromOracle [
    "Moon Girl and Devil Dinosaur",
    "{1}{G}{U}",
    "Legendary Creature — Human Dinosaur Hero",
    "2/2",
    "Whenever you draw your second card each turn, until end of turn, Moon Girl and Devil Dinosaur's base power and toughness become 6/6 and they gain trample.",
    "Whenever an artifact you control enters, draw a card. This ability triggers only once each turn.",
  ]

def theRuinousWreckingCrew : CardDef :=
  fromOracle [
    "The Ruinous Wrecking Crew",
    "{X}{B}{R}",
    "Legendary Creature — Human Villain",
    "2/2",
    "The Ruinous Wrecking Crew enters with X +1/+1 counters on it.",
    "When The Ruinous Wrecking Crew enters, choose up to X —",
    "• Discard a card, then draw a card.",
    "• Target opponent loses 2 life.",
    "• Destroy target token.",
    "• Each player sacrifices a creature of their choice.",
  ]

def scientistSupremeOfAIM : CardDef :=
  fromOracle [
    "Scientist Supreme of A.I.M.",
    "{U}{B}",
    "Legendary Creature — Human Scientist Villain",
    "2/2",
    "Pay 2 life: Copy target activated or triggered ability you control from an artifact source. You may choose new targets for the copy. Activate only during your turn and only once each turn. (Mana abilities can't be targeted.)",
  ]

def theSerpentSociety : CardDef :=
  fromOracle [
    "The Serpent Society",
    "{1}{B}{G}",
    "Legendary Creature — Human Snake Villain",
    "3/4",
    "Deathtouch",
    "Ward—Get five poison counters. (A player with ten or more poison counters loses the game.)",
    "Whenever another creature you control with deathtouch dies, each opponent sacrifices a nontoken creature of their choice.",
  ]

def speedballNewWarrior : CardDef :=
  fromOracle [
    "Speedball, New Warrior",
    "{2}{U/R}",
    "Legendary Creature — Human Hero",
    "2/2",
    "Whenever a player casts a spell that targets Speedball, he gets +2/+2 until end of turn. You may choose new targets for that spell.",
  ]

def spiderManToTheRescue : CardDef :=
  fromOracle [
    "Spider-Man, To the Rescue",
    "{2}{G/W}",
    "Legendary Creature — Spider Human Hero",
    "3/2",
    "Flash",
    "Reach, vigilance",
    "No One Dies! — When Spider-Man enters, you may tap him. When you do, another target nonattacking creature you control gains indestructible until end of turn. (Damage and effects that say \"destroy\" don't destroy it.)",
  ]

def spiderWomanSecretAgent : CardDef :=
  fromOracle [
    "Spider-Woman, Secret Agent",
    "{3}{W/U}",
    "Legendary Creature — Spider Human Spy Hero",
    "1/4",
    "Flash",
    "When Spider-Woman enters, tap target creature an opponent controls. That creature can't become untapped for as long as you control Spider-Woman.",
  ]

def stormWindrider : CardDef :=
  fromOracle [
    "Storm, Windrider",
    "{1}{G}{W}{W}",
    "Legendary Creature — Mutant Hero",
    "4/4",
    "Flying",
    "Creatures with flying can't attack you or block creatures you control.",
    "Whenever you cast a spell that targets one or more creatures, those creatures gain flying until end of turn.",
  ]

def theSuperHeroCivilWar : CardDef :=
  fromOracle [
    "The Super Hero Civil War",
    "{3}{R}{W}",
    "Enchantment — Saga",
    "(As this Saga enters and after your draw step, add a lore counter. Sacrifice after III.)",
    "I — Gain control of up to two target creatures with total mana value 6 or less for as long as this Saga remains on the battlefield.",
    "II — Creatures you control get +1/+1 and gain vigilance until end of turn.",
    "III — Target creature you control fights up to one other target creature.",
  ]

def taskmasterMercenaryMimic : CardDef :=
  fromOracle [
    "Taskmaster, Mercenary Mimic",
    "{2}{U}{B}",
    "Legendary Creature — Human Mercenary Villain",
    "3/5",
    "Photographic Reflexes — At the beginning of your first main phase, until your next turn, Taskmaster becomes a copy of up to one target creature on the battlefield or creature card in a graveyard, except his name is Taskmaster, Mercenary Mimic and he's a legendary Human Mercenary Villain creature.",
  ]

def thanosTheMadTitan : CardDef :=
  fromOracle [
    "Thanos, the Mad Titan",
    "{R}{W}{B}",
    "Legendary Creature — Eternal Villain",
    "4/4",
    "Deathtouch, lifelink",
    "Power-up — {C}{W}{U}{B}{R}{G}: Put two +1/+1 counters on Thanos. Choose odd or even. Destroy each other creature with mana value of the chosen quality. (Activate each power-up ability only once. Reduce the cost by his mana cost if he entered this turn. Zero is even.)",
  ]

def thorOdinson : CardDef :=
  fromOracle [
    "Thor Odinson",
    "{3}{R}{W}",
    "Legendary Creature — God Warrior Hero",
    "4/4",
    "Flying, vigilance, prowess, prowess (Whenever you cast a noncreature spell, this creature gets +1/+1 until end of turn twice.)",
  ]

def titaniaRuggedRumbler : CardDef :=
  fromOracle [
    "Titania, Rugged Rumbler",
    "{2}{B/G}",
    "Legendary Creature — Human Villain",
    "5/5",
    "As an additional cost to cast this spell, discard a card or pay {2}.",
    "Ward—Discard a card or pay {2}. (Whenever this creature becomes the target of a spell or ability an opponent controls, counter it unless that player discards a card or pays {2}.)",
  ]

#guard titaniaRuggedRumbler.additionalCostDiscardOrPayGeneric == some 2
#guard titaniaRuggedRumbler.announcesAdditionalCost

def uSAgentJohnWalker : CardDef :=
  fromOracle [
    "U.S.Agent, John Walker",
    "{3}{W/B}",
    "Legendary Creature — Human Soldier Hero",
    "3/2",
    "When U.S.Agent enters, create a colorless Equipment artifact token named Sturdy Shield with \"Equipped creature gets +1/+2\" and equip {2}. Attach it to U.S.Agent.",
  ]

def visionQuest : CardDef :=
  fromOracle [
    "Vision Quest",
    "{X}{U}{R}",
    "Sorcery",
    "Search your library and/or graveyard for an artifact creature card with mana value X or less and put it onto the battlefield with X additional +1/+1 counters on it. If X is 4 or greater, it gains haste until end of turn. If you search your library this way, shuffle.",
  ]

def warMachineLegacyOfIron : CardDef :=
  fromOracle [
    "War Machine, Legacy of Iron",
    "{2}{R/W}",
    "Legendary Artifact Creature — Human Hero",
    "1/3",
    "Flying",
    "At the beginning of combat on your turn, another target creature you control gets +X/+0 until end of turn, where X is War Machine's power.",
  ]

def winterSoldierIcyAssassin : CardDef :=
  fromOracle [
    "Winter Soldier, Icy Assassin",
    "{W}{B}",
    "Legendary Creature — Human Assassin Villain",
    "2/2",
    "Vigilance, menace",
    "Winter Soldier gets +2/+0 for each Equipment attached to him.",
    "{3}{W}{B}: Return this card from your graveyard to the battlefield with a finality counter on him. Then you may attach an Equipment you control to him. (If a creature with a finality counter on it would die, exile it instead.)",
  ]

def wolverineFierceFighter : CardDef :=
  fromOracle [
    "Wolverine, Fierce Fighter",
    "{2}{R}{G}",
    "Legendary Creature — Mutant Berserker Hero",
    "3/5",
    "Haste",
    "When Wolverine enters, he fights up to one other target creature.",
    "If damage would be dealt to Wolverine, instead that damage is dealt, but all other damage already dealt to him is healed.",
  ]

def worldsWithinWorlds : CardDef :=
  fromOracle [
    "Worlds Within Worlds",
    "{5}{G}{U}",
    "Sorcery",
    "Exile all creatures. Each player may put any number of creature cards from their hand onto the battlefield. Then put all cards exiled this way into their owners' hands. Exile Worlds Within Worlds.",
  ]

def aIMSynthoids : CardDef :=
  fromOracle [
    "A.I.M. Synthoids",
    "{2}",
    "Artifact Creature — Robot Villain",
    "1/3",
    "When this creature enters, surveil 2. (Look at the top two cards of your library, then put any number of them into your graveyard and the rest on top of your library in any order.)",
  ]

def arcReactor : CardDef :=
  fromOracle [
    "Arc Reactor",
    "{5}",
    "Artifact",
    "Improvise (Your artifacts can help cast this spell. Each artifact you tap after you're done activating mana abilities pays for {1}.)",
    "This artifact enters tapped.",
    "{T}: Add {C}{C}{C}.",
  ]

def captainAmericaSShield : CardDef :=
  fromOracle [
    "Captain America's Shield",
    "{2}",
    "Legendary Artifact — Equipment",
    "Indestructible",
    "Equipped creature gets +0/+8 and has vigilance.",
    "Whenever equipped creature attacks, tap target creature defending player controls.",
    "Equip {2}",
  ]

def cosmicCube : CardDef :=
  fromOracle [
    "Cosmic Cube",
    "{5}",
    "Artifact",
    "Ward {2}",
    "Whenever you attack, look at the top six cards of your library. You may cast a spell from among them with mana value less than or equal to the greatest power among attacking creatures you control without paying its mana cost. Put the rest on the bottom of your library in a random order.",
  ]

def dependableQuinjet : CardDef :=
  fromOracle [
    "Dependable Quinjet",
    "{3}",
    "Artifact — Vehicle",
    "3/3",
    "Flying",
    "{T}: Add one mana of any color.",
    "Crew 4 (Tap any number of creatures you control with total power 4 or more: This Vehicle becomes an artifact creature until end of turn.)",
  ]

def hERBIEScoutUnit : CardDef :=
  fromOracle [
    "H.E.R.B.I.E. Scout Unit",
    "{4}",
    "Artifact Creature — Robot Scout",
    "2/1",
    "Flying",
    "When this creature enters, draw a card, then you may put a land card from your hand onto the battlefield tapped.",
  ]

def ironManArmor : CardDef :=
  fromOracle [
    "Iron Man Armor",
    "{3}",
    "Artifact — Equipment",
    "When this Equipment enters, attach it to target creature you control.",
    "Equipped creature gets +2/+1 and has flying.",
    "{2}: If this Equipment isn't a creature, it becomes a 0/0 Construct Hero artifact creature with flying and \"This creature gets +1/+1 for each artifact you control\" until end of turn.",
    "Equip {2}",
  ]

def sHIELDHelicarrier : CardDef :=
  fromOracle [
    "S.H.I.E.L.D. Helicarrier",
    "{4}",
    "Artifact — Vehicle",
    "4/5",
    "Flying",
    "When this Vehicle enters, create two 1/1 white Soldier creature tokens.",
    "Crew 6 (Tap any number of creatures you control with total power 6 or more: This Vehicle becomes an artifact creature until end of turn.)",
  ]

def superAdaptoid : CardDef :=
  fromOracle [
    "Super-Adaptoid",
    "{2}",
    "Legendary Artifact Creature — Robot Villain",
    "*/2",
    "Super-Adaptoid's power is equal to the number of legendary creatures you control.",
    "Whenever Super-Adaptoid enters or attacks, choose another target creature. If that creature has haste and Super-Adaptoid doesn't, put a haste counter on Super-Adaptoid. Do the same for flying, first strike, double strike, deathtouch, indestructible, lifelink, menace, reach, trample, and vigilance.",
  ]

def theTenRings : CardDef :=
  fromOracle [
    "The Ten Rings",
    "{8}",
    "Legendary Artifact",
    "Your maximum hand size is ten.",
    "At the beginning of your end step, if you have fewer than ten cards in hand, draw cards equal to the difference.",
  ]

def ultronArtificialMalevolence : CardDef :=
  fromOracle [
    "Ultron, Artificial Malevolence",
    "{3}",
    "Legendary Artifact Creature — Robot Villain",
    "2/4",
    "Whenever another nontoken artifact you control enters, you may pay {2}. If you do, create a token that's a copy of it. If the token isn't a creature, it becomes a 2/2 Robot Villain creature in addition to its other types.",
  ]

def ultronDrone : CardDef :=
  fromOracle [
    "Ultron Drone",
    "{3}",
    "Artifact Creature — Robot Villain",
    "2/3",
    "Power-up — {6}: Put two +1/+1 counters on this creature and create a 2/2 colorless Robot Villain artifact creature token. (Activate each power-up ability only once. Reduce the cost by its mana cost if it entered this turn.)",
  ]

def vibraniumEnergyDaggers : CardDef :=
  fromOracle [
    "Vibranium Energy Daggers",
    "{1}",
    "Artifact — Equipment",
    "Indestructible (Effects that say \"destroy\" don't destroy this Equipment.)",
    "Equipped creature gets +2/+2.",
    "Equip {3} ({3}: Attach to target creature you control. Equip only as a sorcery.)",
  ]

def theVision : CardDef :=
  fromOracle [
    "The Vision",
    "{4}",
    "Legendary Artifact Creature — Robot Hero",
    "2/5",
    "Flying, vigilance",
    "Whenever you cast a noncreature spell, choose one that hasn't been chosen this turn —",
    "• Solar Beam — The Vision gains double strike until end of turn.",
    "• Density Control — The Vision gains indestructible until end of turn.",
    "• Technopathy — Draw a card.",
  ]

def vivVisionTeenSynthezoid : CardDef :=
  fromOracle [
    "Viv Vision, Teen Synthezoid",
    "{3}",
    "Legendary Artifact Creature — Robot Hero",
    "2/2",
    "Flying",
    "Cybernetic Senses — Whenever Viv Vision attacks, draw a card if her power is 4 or greater.",
    "Power-up — {7}: Put two +1/+1 counters on Viv Vision. (Activate each power-up ability only once. Reduce the cost by her mana cost if she entered this turn.)",
  ]

def aIMLabs : CardDef :=
  fromOracle [
    "A.I.M. Labs",
    "Land",
    "This land enters tapped.",
    "When this land enters, you gain 1 life.",
    "{T}: Add {U} or {B}.",
  ]

def asgardianCitadel : CardDef :=
  fromOracle [
    "Asgardian Citadel",
    "Land",
    "This land enters tapped.",
    "When this land enters, you gain 1 life.",
    "{T}: Add {R} or {W}.",
  ]

def avengersHangar : CardDef :=
  fromOracle [
    "Avengers Hangar",
    "Land",
    "This land enters tapped.",
    "When this land enters, you gain 1 life.",
    "{T}: Add {W} or {U}.",
  ]

def avengersTower : CardDef :=
  fromOracle [
    "Avengers Tower",
    "Land",
    "{T}: Add {C}.",
    "{T}: Add one mana of any color. Spend this mana only to cast a Hero spell or to activate an ability of a Hero source.",
    "{4}, {T}: Look at the top three cards of your library. You may reveal a Hero card from among them and put it into your hand. Put the rest on the bottom of your library in any order.",
  ]

def baxterBuilding : CardDef :=
  fromOracle [
    "Baxter Building",
    "Land",
    "{T}: Add {C}.",
    "{4}, {T}: Add four mana in any combination of colors.",
    "{4}, {T}: Draw a card. Activate only if you control a creature with toughness 4 or greater.",
  ]

def birninZanaPlaza : CardDef :=
  fromOracle [
    "Birnin Zana Plaza",
    "Land",
    "This land enters tapped.",
    "When this land enters, you gain 1 life.",
    "{T}: Add {G} or {W}.",
  ]

def castleDoom : CardDef :=
  fromOracle [
    "Castle Doom",
    "Land",
    "{T}: Add {C}.",
    "{T}: Add one mana of any color. Spend this mana only to cast an artifact spell.",
    "{3}, {T}, Sacrifice an artifact: Create a 3/3 colorless Robot Villain artifact creature token named Doombot. Activate only as a sorcery.",
  ]

def darkFortress : CardDef :=
  fromOracle [
    "Dark Fortress",
    "Land",
    "{T}: Add {C}.",
    "{T}: Add {B} or {R}. Activate only if this land entered this turn or if you control a basic land.",
  ]

def fiskTower : CardDef :=
  fromOracle [
    "Fisk Tower",
    "Land",
    "This land enters tapped.",
    "When this land enters, you gain 1 life.",
    "{T}: Add {W} or {B}.",
  ]

def gatheringPlace : CardDef :=
  fromOracle [
    "Gathering Place",
    "Land",
    "{T}: Add {C}.",
    "{T}: Add {G} or {W}. Activate only if this land entered this turn or if you control a basic land.",
  ]

def gleamingBastion : CardDef :=
  fromOracle [
    "Gleaming Bastion",
    "Land",
    "{T}: Add {C}.",
    "{T}: Add {W} or {U}. Activate only if this land entered this turn or if you control a basic land.",
  ]

def hellSKitchen : CardDef :=
  fromOracle [
    "Hell's Kitchen",
    "Land",
    "This land enters tapped.",
    "When this land enters, you gain 1 life.",
    "{T}: Add {B} or {R}.",
  ]

def hiddenLair : CardDef :=
  fromOracle [
    "Hidden Lair",
    "Land",
    "{T}: Add {C}.",
    "{T}: Add {U} or {B}. Activate only if this land entered this turn or if you control a basic land.",
  ]

def losDiablosMissileBase : CardDef :=
  fromOracle [
    "Los Diablos Missile Base",
    "Land",
    "This land enters tapped.",
    "When this land enters, you gain 1 life.",
    "{T}: Add {R} or {G}.",
  ]

def pymTechnologies : CardDef :=
  fromOracle [
    "Pym Technologies",
    "Land",
    "This land enters tapped.",
    "When this land enters, you gain 1 life.",
    "{T}: Add {G} or {U}.",
  ]

def starkIndustries : CardDef :=
  fromOracle [
    "Stark Industries",
    "Land",
    "This land enters tapped.",
    "When this land enters, you gain 1 life.",
    "{T}: Add {U} or {R}.",
  ]

def subterraneanCavern : CardDef :=
  fromOracle [
    "Subterranean Cavern",
    "Land",
    "This land enters tapped.",
    "When this land enters, you gain 1 life.",
    "{T}: Add {B} or {G}.",
  ]

def surveillanceRoom : CardDef :=
  fromOracle [
    "Surveillance Room",
    "Land",
    "When this land enters, surveil 1. (Look at the top card of your library. You may put it into your graveyard.)",
    "{T}: Add {C}.",
    "{1}, {T}: Add one mana of any color.",
  ]

def trainingCompound : CardDef :=
  fromOracle [
    "Training Compound",
    "Land",
    "{T}: Add {C}.",
    "{T}: Add {R} or {G}. Activate only if this land entered this turn or if you control a basic land.",
  ]

def villainousHideout : CardDef :=
  fromOracle [
    "Villainous Hideout",
    "Land",
    "{T}: Add {C}.",
    "{T}: Add one mana of any color. Spend this mana only to cast a Villain spell or to activate an ability of a Villain source.",
    "{3}, {T}: Target Villain you control connives. Activate only as a sorcery. (Draw a card, then discard a card. If you discarded a nonland card, put a +1/+1 counter on that creature.)",
  ]

/-- All unique MSH card names, including both faces of transforming cards
and the five basic lands printed in the set. -/
@[irreducible, noinline] def mshCards : Array CardDef :=
  #[
    theSensationalSheHulk,
    photonLivingLight,
    theIncredibleHulk,
    theInvincibleIronMan,
    blackPantherHopeEnduring,
    agent13SharonCarter,
    agentMariaHill,
    agentOfAtlas,
    agentPhilCoulson,
    agentsOfSHIELD,
    avengersAssemble,
    boroughBackup,
    braveBrawler,
    captainAmericaSuperSoldier,
    captainAmericaWingsOfFreedom,
    captainMarvelEarthSProtector,
    captainMarVellSpaceBorn,
    colleenWingStreetSamurai,
    crowdOfTrueBelievers,
    helicarrierStrike,
    heroInTraining,
    invisibleWomanSueStorm,
    jenniferWalters,
    kreeCommandos,
    lukeCagePowerMan,
    theMindStone,
    mockingbirdAceAgent,
    monicaRambeau,
    murdockSCrusade,
    nickFuryAgentOfSHIELD,
    nightNurseHealerOfHeroes,
    okoyeDoraMilajeLeader,
    originOfTheAvengers,
    pantherPounce,
    patriotShieldWielder,
    politicalTriumph,
    quakeAgentOfSHIELD,
    raftSecurityOfficer,
    redGuardianSuperSoldier,
    theSentryGoldenGuardian,
    sHIELDSpyKit,
    superVillainLockup,
    superSoldierSerum,
    takeUpTheShield,
    wakandanDroneFlock,
    webUp,
    whiteWidowFreeAgent,
    aerialDoombot,
    aIMScientists,
    atlanteanCavalry,
    atlantisAttacks,
    attumaAtlanteanWarlord,
    boldBiochemist,
    bruceBanner,
    depower,
    echoPerceptiveProdigy,
    falconWingedWonder,
    falconSWingHarness,
    frozenInIce,
    futuristForge,
    giantSizedFlyingAnt,
    hydraulicHelper,
    iAmIronMan,
    ironLadDivergingDestiny,
    ironheartCleverChampion,
    justiceVanceAstrovik,
    kangTheConqueror,
    kidLoki,
    leaderSuperGenius,
    lokiGodOfMischief,
    misterFantasticReedRichards,
    msMarvelKamalaKhan,
    multiversalIncursion,
    namorTheSubMariner,
    pymParticles,
    rewriteHistory,
    secretInvasion,
    sHIELDDeploymentDrone,
    sHIELDFlyingCar,
    shuriWakandanInventor,
    statureSizeShifter,
    superIntelligence,
    superSuit,
    thirstForKnowledge,
    tonyStark,
    tricksterSStratagem,
    weSayTheeNay,
    wiccanRisingMagician,
    theWondrousWasp,
    agentsOfHYDRA,
    arnimZolaBioFanatic,
    baronHelmutZemo,
    baronStruckerHYDRAOverlord,
    blackWidowSuperSpy,
    constructACosmicCube,
    crossbonesMaliciousMercenary,
    cruelAlliance,
    darkDeed,
    decoyPloy,
    doctorDoom,
    doomReignsSupreme,
    elektraDaughterOfTheHand,
    grimReaperLethalLegionnaire,
    hourOfDefeat,
    hYDRAInfiltration,
    hYDRATroopers,
    kingpinSEnforcers,
    klawSonicSubjugator,
    madameMasque,
    theMastersOfEvil,
    mODOK,
    moonstoneHarshMistress,
    ninjaOfTheHand,
    projectDeathlokSoldier,
    redRoomRecruit,
    robotDomination,
    roninShadowStalker,
    roxxonBrutes,
    stolenStarkTech,
    superSkrull,
    swordsmanSharpScoundrel,
    thunderboltsConspiracy,
    tooEvilToStayDead,
    unlivingLegionnaire,
    visionsOfVillainy,
    whiplashVengefulEngineer,
    widowSBite,
    yellowjacketHeartlessMarauder,
    avengersDisassembled,
    blazingCrescendo,
    crimsonOperative,
    deathToOurEnemies,
    evilSThrall,
    finFangFoom,
    hawkeyeMasterMarksman,
    hawkeyeYoungAvenger,
    hawkeyeSBow,
    hexMagic,
    hireACrew,
    hULKSMASH,
    humanTorchJohnnyStorm,
    hYDRAAssaultRobot,
    ironFistLivingWeapon,
    jessicaJonesPrivateEye,
    kUnLunWarrior,
    kreeSentinel,
    lightningStrike,
    lokiLaufeyson,
    machinesmithAutomaton,
    mistyKnightHeroForHire,
    mjLnirHammerOfThor,
    photonBlastBarrage,
    quicksilverBrashBlur,
    redHulk,
    repulsorBlast,
    theScarletWitch,
    speedYoungAvenger,
    starkIndustriesExecutive,
    superSpeed,
    teamTactics,
    thorGodOfThunder,
    truckToss,
    visionOfLove,
    volcanicVillain,
    wonderManHollywoodHero,
    antManSArmy,
    callDamageControl,
    claimTheKingdom,
    docSamsonSuperPsychiatrist,
    earthSMightiestHeroes,
    epicFight,
    giantGrowth,
    goNuts,
    guerrillaGorilla,
    hellcatUndyingVigilante,
    herculesPrinceOfPower,
    heroicFeast,
    hulklingBurgeoningBruiser,
    kaZarOfTheSavageLand,
    knightOfWundagore,
    misterHydeMonsterWithin,
    moleManMoloidMaster,
    petAvengers,
    powerfulBroker,
    punishingPunch,
    rapidRescue,
    reptilDinomorpher,
    restorativeTechnique,
    rickJonesDestinedSidekick,
    savageLandDinosaur,
    serpentSpecialist,
    shangChiMasterOfKungFu,
    sheHulkJadeDefender,
    superStrength,
    theThingBenGrimm,
    tigraFelineFury,
    trainingRegimen,
    theUnbeatableSquirrelGirl,
    undercoverSkrull,
    wakandanRoyalGuard,
    whiteTigerAvaAyala,
    worldWarHulk,
    abominationTerrifyingTitan,
    absorbingMan,
    alienInvasion,
    antManColonyCommander,
    aresGodOfWar,
    armorWars,
    theAstonishingAntMan,
    avengersUnderSiege,
    beastEruditeAerialist,
    blackPantherVanguard,
    blackWidowDoubleAgent,
    bullseyeDeathDealer,
    captainAmericaLivingLegend,
    cloakAndDaggerEntwined,
    theComingOfGalactus,
    daredevilManWithoutFear,
    ghostSpectralSaboteur,
    hulkGammaGoliath,
    ironManMasterOfMachines,
    kangTemporalTyrant,
    killmongerScourgeOfWakanda,
    kingTChalla,
    theKingpinOfCrime,
    madameHydra,
    theMightyThorJaneFoster,
    moonGirlAndDevilDinosaur,
    theRuinousWreckingCrew,
    scientistSupremeOfAIM,
    theSerpentSociety,
    speedballNewWarrior,
    spiderManToTheRescue,
    spiderWomanSecretAgent,
    stormWindrider,
    theSuperHeroCivilWar,
    taskmasterMercenaryMimic,
    thanosTheMadTitan,
    thorOdinson,
    titaniaRuggedRumbler,
    uSAgentJohnWalker,
    visionQuest,
    warMachineLegacyOfIron,
    winterSoldierIcyAssassin,
    wolverineFierceFighter,
    worldsWithinWorlds,
    aIMSynthoids,
    arcReactor,
    captainAmericaSShield,
    cosmicCube,
    dependableQuinjet,
    hERBIEScoutUnit,
    ironManArmor,
    sHIELDHelicarrier,
    superAdaptoid,
    theTenRings,
    ultronArtificialMalevolence,
    ultronDrone,
    vibraniumEnergyDaggers,
    theVision,
    vivVisionTeenSynthezoid,
    aIMLabs,
    asgardianCitadel,
    avengersHangar,
    avengersTower,
    baxterBuilding,
    birninZanaPlaza,
    castleDoom,
    darkFortress,
    fiskTower,
    gatheringPlace,
    gleamingBastion,
    hellSKitchen,
    hiddenLair,
    losDiablosMissileBase,
    pymTechnologies,
    starkIndustries,
    subterraneanCavern,
    surveillanceRoom,
    trainingCompound,
    villainousHideout,
    plains,
    island,
    swamp,
    mountain,
    forest
  ]

#guard mshCards.size >= 281 && mshCards.all (fun c => c.name != "")

end Mtg.Engine.Catalog
