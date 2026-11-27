import Mtg.Engine.Card
import Mtg.Engine.Catalog

/-!
# Star Trek catalog

Oracle characteristics for every unique card in Magic: The Gathering | Star Trek
(TRK). Each card is defined by its official Gatherer Oracle text, and every rules
line is modeled: no card keeps a line as printed text. Station / Spacecraft
thresholds (CR 702.184 / 722.2), Beam me up (CR 702.196), facing a dilemma
(CR 700.17), Assimilate (CR 701.72), Discover (CR 701.57), and Sunburst
(CR 702.44) are modeled.

Source: Gatherer set `TRK` (https://gatherer.wizards.com/sets/TRK; 497 English
printings deduplicating to 311 unique Oracle cards). When Scryfall does not match
Gatherer, Gatherer is authoritative.
-/

namespace Mtg.Engine.Catalog

open Mtg.Engine

def seventyThousandLightYearsFromHome : CardDef :=
  fromOracle [
    "70,000 Light-Years from Home",
    "{1}{W}",
    "Sorcery",
    "Exile target creature or Spacecraft. Its controller may search their library for a basic land card, reveal it, put it into their hand, then shuffle."
  ]

def andromedanAutomatons : CardDef :=
  fromOracle [
    "Andromedan Automatons",
    "{2}{W}",
    "Artifact Creature — Android",
    "3/1",
    "When this creature enters, you may search your library for any number of cards named Andromedan Automatons, reveal them, put them into your hand, then shuffle."
  ]

def antagonistIncorporator : CardDef :=
  fromOracle [
    "Antagonist Incorporator",
    "{1}{W}",
    "Artifact Creature — Borg",
    "2/3",
    "Artifact creatures you control have \"Whenever this creature deals combat damage to a player, you may pay {1}. If you do, create a 1/1 colorless Borg artifact creature token.\""
  ]

def assemblySpecialist : CardDef :=
  fromOracle [
    "Assembly Specialist",
    "{1}{W}",
    "Artifact Creature — Borg",
    "1/1",
    "When this creature enters, create a 1/1 colorless Borg artifact creature token."
  ]

def bradBoimlerEagerEnsign : CardDef :=
  fromOracle [
    "Brad Boimler, Eager Ensign",
    "{1}{W}",
    "Legendary Creature — Human Officer",
    "2/2",
    "Lifelink",
    "Whenever Brad Boimler becomes tapped, until end of turn, if one or more counters would be put on a permanent you control, that many plus one of each of those kinds of counters are put on that permanent instead."
  ]

def captainBenjaminSisko : CardDef :=
  fromOracle [
    "Captain Benjamin Sisko",
    "{1}{W}",
    "Legendary Creature — Human Officer",
    "2/2",
    "At the beginning of your end step, create a 1/1 red Officer creature token for each dilemma you've faced this turn.",
    "{2}{W}{U}{B}{R}{G}, {T}: Exile the top five cards of your library. You may cast any number of spells with mana value less than or equal to the number of Officers you control from among those cards without paying their mana costs."
  ]

def captainJeanLucPicard : CardDef :=
  fromOracle [
    "Captain Jean-Luc Picard",
    "{2}{W}",
    "Legendary Creature — Human Officer",
    "2/3",
    "Other creatures you control get +1/+1.",
    "Whenever you cast a creature or Spacecraft spell, create a 1/1 red Officer creature token.",
    "Tap seven untapped Officers you control: Search your library for a Spacecraft card, put it onto the battlefield with seven charge counters on it, then shuffle."
  ]

def commandDecision : CardDef :=
  fromOracle [
    "Command Decision",
    "{1}{W}",
    "Sorcery",
    "Choose one —",
    "• Destroy target creature with power 4 or greater.",
    "• Draw a card."
  ]

def commandSubadjunct : CardDef :=
  fromOracle [
    "Command Subadjunct",
    "{W}",
    "Artifact Creature — Borg",
    "2/1",
    "Artifact creatures you control have vigilance."
  ]

def conquestMission : CardDef :=
  fromOracle [
    "Conquest Mission",
    "{2}{W}",
    "Enchantment",
    "Whenever a nontoken artifact you control enters, put a quest counter on this enchantment. Create a 1/1 colorless Borg artifact creature token. If this enchantment has six or more quest counters on it, create two of those tokens instead."
  ]

def deannaTroiPsychicCounsel : CardDef :=
  fromOracle [
    "Deanna Troi, Psychic Counsel",
    "{1}{W}",
    "Legendary Creature — Betazoid Human Advisor",
    "2/2",
    "Other creatures you control enter with an additional +1/+1 counter on them."
  ]

def dot7RepairSquad : CardDef :=
  fromOracle [
    "DOT-7 Repair Squad",
    "{3}{W}",
    "Artifact Creature — Robot",
    "3/3",
    "Flying",
    "{1}{W}: Untap target creature. Activate only as a sorcery and only once each turn."
  ]

def drBeverlyCrusher : CardDef :=
  fromOracle [
    "Dr. Beverly Crusher",
    "{2}{W}",
    "Legendary Creature — Human Doctor",
    "2/2",
    "If you gaining life causes a triggered ability of a permanent you control to trigger, that ability triggers an additional time.",
    "Whenever you gain life, put a +1/+1 counter on Dr. Crusher."
  ]

def drMcCoySurlySurgeon : CardDef :=
  fromOracle [
    "Dr. McCoy, Surly Surgeon",
    "{2}{W}{W}",
    "Legendary Creature — Human Doctor",
    "2/2",
    "When Dr. McCoy enters, put a +1/+1 counter on another target creature you control.",
    "If another creature you control with a +1/+1 counter on it would be destroyed, instead remove all +1/+1 counters from it and all damage already dealt to it is healed."
  ]

def emergencyMedicalHologram : CardDef :=
  fromOracle [
    "Emergency Medical Hologram",
    "{W}",
    "Artifact Creature — Illusion Doctor",
    "0/1",
    "When this creature enters, put a +1/+1 counter on target creature. You gain 1 life."
  ]

def excalbianGamemaster : CardDef :=
  fromOracle [
    "Excalbian Gamemaster",
    "{5}{W}",
    "Creature — Excalbian",
    "6/6",
    "Strange new worlds — When this creature enters, create X 1/1 red Officer creature tokens, where X is the number of differently named lands you control.",
    "Whenever this creature or another creature you control dies, put a +1/+1 counter on target creature you control."
  ]

def federationFieldMedic : CardDef :=
  fromOracle [
    "Federation Field Medic",
    "{3}{W}",
    "Creature — Human Doctor",
    "3/2",
    "Vigilance",
    "When this creature enters, choose one —",
    "• Put a +1/+1 counter on target creature. It gains vigilance until end of turn.",
    "• Draw a card if you control a permanent with a counter on it."
  ]

def federationResupply : CardDef :=
  fromOracle [
    "Federation Resupply",
    "{1}{W}",
    "Sorcery",
    "Search your library for an Aura, Equipment, or Spacecraft card, reveal it, put it into your hand, then shuffle.",
    "Beam me up {3}{W} (You may cast this card from your graveyard for {3}{W} if you also return a creature you control to its owner's hand. Then exile this spell.)"
  ]

def freeBorgRevolutionaries : CardDef :=
  fromOracle [
    "Free Borg Revolutionaries",
    "{3}{W}{W}",
    "Artifact Creature — Borg Rebel",
    "4/5",
    "When this creature enters, creatures you control get +1/+1 until end of turn.",
    "Basic landcycling {2} ({2}, Discard this card: Search your library for a basic land card, reveal it, put it into your hand, then shuffle.)"
  ]

def ghostOfIllyria : CardDef :=
  fromOracle [
    "Ghost of Illyria",
    "{3}{W}",
    "Creature — Elemental Spirit",
    "3/3",
    "Flying",
    "When this creature enters, exile up to one other target nonland permanent you control. Return that card to the battlefield under its owner's control at the beginning of the next end step."
  ]

def hologramJaneway : CardDef :=
  fromOracle [
    "Hologram Janeway",
    "{2}{W}",
    "Legendary Artifact Creature — Illusion Officer",
    "3/3",
    "Whenever you attack while creatures you control have total power 8 or greater, put a +1/+1 counter on target creature."
  ]

def malfunctioningHolodeck : CardDef :=
  fromOracle [
    "Malfunctioning Holodeck",
    "{2}{W}",
    "Artifact",
    "Ward {2} (Whenever this artifact becomes the target of a spell or ability an opponent controls, counter it unless that player pays {2}.)",
    "When this artifact enters, exile target nonland permanent an opponent controls until this artifact leaves the battlefield."
  ]

def theMeasureOfAMan : CardDef :=
  fromOracle [
    "The Measure of a Man",
    "{2}{W}",
    "Enchantment — Saga",
    "(As this Saga enters and after your draw step, add a lore counter. Sacrifice after III.)",
    "I — Exile up to one target nontoken artifact or creature.",
    "II — Investigate. (Create a Clue token. It's an artifact with \"{2}, Sacrifice this token: Draw a card.\")",
    "III — Return the exiled card to the battlefield under its owner's control. You gain 2 life."
  ]

def milesOBrienTransporterOps : CardDef :=
  fromOracle [
    "Miles O'Brien, Transporter Ops",
    "{2}{W}",
    "Legendary Creature — Human Artificer",
    "3/3",
    "When Miles O'Brien enters, return up to one other target creature or artifact you control to its owner's hand.",
    "At the beginning of each end step, if a permanent was returned to your hand from the battlefield this turn, draw a card."
  ]

def theNeedsOfTheMany : CardDef :=
  fromOracle [
    "The Needs of the Many",
    "{1}{W}",
    "Instant",
    "As an additional cost to cast this spell, sacrifice a creature.",
    "Creatures you control gain hexproof and indestructible until end of turn. You gain hexproof until end of turn. Prevent all damage that would be dealt to you this turn. Exile The Needs of the Many."
  ]

def oberthClassStarship : CardDef :=
  fromOracle [
    "Oberth-Class Starship",
    "{1}{W}",
    "Artifact — Spacecraft",
    "When this Spacecraft enters, search your library for a basic Plains card, reveal it, put it into your hand, then shuffle.",
    "Station (Tap another creature you control: Put charge counters equal to its power on this Spacecraft. Station only as a sorcery. It's an artifact creature at 6+.)",
    "6+ | [2/2] Flying"
  ]

def peaceInOurTime : CardDef :=
  fromOracle [
    "Peace in Our Time",
    "{3}{W}",
    "Enchantment",
    "At the beginning of combat on each player's turn, that player may draw a card. If they do, they can't attack this turn and you put a peace counter on this enchantment.",
    "At the beginning of your upkeep, if this enchantment has twelve or more peace counters on it, you win the game."
  ]

def petSehlat : CardDef :=
  fromOracle [
    "Pet Sehlat",
    "{2}{W}",
    "Creature — Bear",
    "4/3",
    "This creature can't attack alone."
  ]

def picardLeadingByExample : CardDef :=
  fromOracle [
    "Picard, Leading by Example",
    "{1}{W}",
    "Legendary Creature — Human Officer",
    "2/2",
    "{1}, {T}: Another target creature gets +X/+X until end of turn, where X is Picard's power. Activate only as a sorcery."
  ]

def primaryUnimatrixAdjunct : CardDef :=
  fromOracle [
    "Primary Unimatrix Adjunct",
    "{3}{W}",
    "Artifact Creature — Borg",
    "2/3",
    "Artifact creatures you control have double strike."
  ]

def pureEnergy : CardDef :=
  fromOracle [
    "Pure Energy",
    "{1}{W}",
    "Sorcery",
    "Distribute two +1/+1 counters among one or two target creatures.",
    "Beam me up {2}{W} (You may cast this card from your graveyard for {2}{W} if you also return a creature you control to its owner's hand. Then exile this spell.)"
  ]

def rutherfordUpgradedEnsign : CardDef :=
  fromOracle [
    "Rutherford, Upgraded Ensign",
    "{2}{W}",
    "Legendary Creature — Human Artificer",
    "2/2",
    "When Rutherford enters, look at the top six cards of your library. You may reveal an artifact card from among them and put it into your hand. Put the rest on the bottom of your library in a random order.",
    "Whenever you cast a Spacecraft spell, put a +1/+1 counter on target creature."
  ]

def saavikStoicStudent : CardDef :=
  fromOracle [
    "Saavik, Stoic Student",
    "{4}{W}",
    "Legendary Creature — Vulcan Advisor",
    "2/2",
    "Flash",
    "Federation — When Saavik enters, she deals X damage to target attacking or blocking creature an opponent controls, where X is the number of creature types among non-Borg creatures you control."
  ]

def setPhasersTo : CardDef :=
  fromOracle [
    "Set Phasers to . . .",
    "{W}",
    "Instant",
    "Choose one —",
    "• Stun — Tap target creature and put a stun counter on it. (If a permanent with a stun counter would become untapped, remove one from it instead.)",
    "• Kill — This spell deals 3 damage to target attacking creature."
  ]

def shieldsUp : CardDef :=
  fromOracle [
    "Shields Up!",
    "{1}{W}",
    "Instant",
    "Target artifact or creature you control gains hexproof and indestructible until end of turn. If it's a creature, put a +1/+1 counter on it. (It can't be the target of spells or abilities your opponents control. Damage and effects that say \"destroy\" don't destroy it.)"
  ]

def shuttleAce : CardDef :=
  fromOracle [
    "Shuttle Ace",
    "{4}{W}",
    "Creature — Kelpien Pilot",
    "4/4",
    "During your turn, this creature has flying.",
    "Whenever this creature becomes tapped, you gain 2 life."
  ]

def suluSpaceSwashbuckler : CardDef :=
  fromOracle [
    "Sulu, Space Swashbuckler",
    "{1}{W}",
    "Legendary Creature — Human Pilot",
    "2/2",
    "First strike",
    "Whenever Sulu becomes tapped, if an Equipment or Spacecraft entered the battlefield under your control this turn, draw a card."
  ]

def tacticalOfficer : CardDef :=
  fromOracle [
    "Tactical Officer",
    "{1}{W}",
    "Creature — Human Officer",
    "2/1",
    "Whenever you attack while creatures you control have total power 8 or greater, put a +1/+1 counter on this creature. Untap it."
  ]

def testOfConviction : CardDef :=
  fromOracle [
    "Test of Conviction",
    "{1}{W}",
    "Sorcery",
    "Choose one —",
    "• Battle Stations — Put a +1/+1 counter on each creature you control.",
    "• Begin Negotiations — Target opponent draws a card. You draw two cards."
  ]

def theresCoffeeInThatNebula : CardDef :=
  fromOracle [
    "There's Coffee in that Nebula",
    "{1}{W}",
    "Sorcery",
    "Look at the top five cards of your library. You may reveal a Plains card or nonland permanent card with mana value 3 or less from among them and put it into your hand. Put the rest on the bottom in a random order.",
    "Beam me up {2}{W} (You may cast this card from your graveyard for {2}{W} if you also return a creature you control to its owner's hand. Then exile this spell.)"
  ]

def troublingTribbles : CardDef :=
  fromOracle [
    "Troubling Tribbles",
    "{2}{W}",
    "Creature — Tribble",
    "0/1",
    "This creature can't block.",
    "At the beginning of your upkeep, create a token that's a copy of this creature."
  ]

def unaChinRileyNumberOne : CardDef :=
  fromOracle [
    "Una Chin-Riley, Number One",
    "{4}{W}",
    "Legendary Creature — Illyrian Officer",
    "4/5",
    "Whenever you attack while creatures you control have total power 8 or greater, target attacking creature gets +2/+0 and gains first strike until end of turn."
  ]

def ussEnterpriseAFreeSpirit : CardDef :=
  fromOracle [
    "U.S.S. Enterprise-A, Free Spirit",
    "{3}{W}{W}",
    "Legendary Artifact — Spacecraft",
    "Ward {2}",
    "When U.S.S. Enterprise-A enters, create three 1/1 red Officer creature tokens.",
    "Station (Tap another creature you control: Put charge counters equal to its power on this Spacecraft. Station only as a sorcery. It's an artifact creature at 6+.)",
    "6+ | [5/5] Flying, lifelink"
  ]

def ussExcelsiorCuttingEdge : CardDef :=
  fromOracle [
    "U.S.S. Excelsior, Cutting Edge",
    "{3}{W}",
    "Legendary Artifact — Spacecraft",
    "When U.S.S. Excelsior enters, destroy target tapped creature an opponent controls.",
    "Station (Tap another creature you control: Put charge counters equal to its power on this Spacecraft. Station only as a sorcery. It's an artifact creature at 8+.)",
    "8+ | [4/4] Flying"
  ]

def vexingDrone : CardDef :=
  fromOracle [
    "Vexing Drone",
    "{1}{W}",
    "Artifact Creature — Borg",
    "2/2",
    "When this creature enters, tap target creature an opponent controls."
  ]

def anthropologicalMission : CardDef :=
  fromOracle [
    "Anthropological Mission",
    "{2}{U}",
    "Enchantment",
    "Whenever you cast a noncreature spell, put a quest counter on this enchantment. Draw a card. Then discard a card unless this enchantment has three or more quest counters on it."
  ]

def theCaretaker : CardDef :=
  fromOracle [
    "The Caretaker",
    "{5}{U}",
    "Legendary Creature — Elemental",
    "5/6",
    "Vigilance, ward {2}",
    "At the beginning of each end step, if you faced a dilemma this turn, target opponent exiles cards from the top of their library until they exile a nonland card. You may cast that card without paying its mana cost. (You face a dilemma as you choose one or more modes for a spell or ability.)"
  ]

def cetaceanOps : CardDef :=
  fromOracle [
    "Cetacean Ops",
    "{3}{U}",
    "Creature — Whale Officer",
    "3/3",
    "Ward {1} (Whenever this creature becomes the target of a spell or ability an opponent controls, counter it unless that player pays {1}.)",
    "Whenever you cast a noncreature spell, put a +1/+1 counter on this creature."
  ]

def cloakAndPhaser : CardDef :=
  fromOracle [
    "Cloak and Phaser",
    "{8}{U}",
    "Sorcery",
    "Strange new worlds — This spell costs {X} less to cast, where X is the number of differently named lands you control.",
    "Create two 2/2 black Romulan creature tokens. Draw two cards, then discard a card."
  ]

def cloisteredTelepath : CardDef :=
  fromOracle [
    "Cloistered Telepath",
    "{1}{U}",
    "Creature — Talosian Advisor",
    "2/1",
    "Flash",
    "When this creature enters, draw a card, then discard a card."
  ]

def considerThePrimeDirective : CardDef :=
  fromOracle [
    "Consider the Prime Directive",
    "{2}{U}",
    "Instant",
    "Choose one —",
    "• Interfere — Counter target spell unless its controller pays {3}.",
    "• Observe — Tap up to one target creature and put a stun counter on it. Draw a card. (If a permanent with a stun counter would become untapped, remove one from it instead.)"
  ]

def dataNewLife : CardDef :=
  fromOracle [
    "Data, New Life",
    "{1}{U}",
    "Legendary Artifact Creature — Android Scientist",
    "0/1",
    "Whenever you draw a card, put a +1/+1 counter on Data."
  ]

def deepSpaceScan : CardDef :=
  fromOracle [
    "Deep Space Scan",
    "{4}{U}{U}",
    "Sorcery",
    "Strange new worlds — Draw X cards, where X is the number of differently named lands you control. You have no maximum hand size until your next turn."
  ]

def dominionSaboteur : CardDef :=
  fromOracle [
    "Dominion Saboteur",
    "{4}{U}",
    "Creature — Shapeshifter",
    "3/3",
    "You may have this creature enter as a copy of any artifact or creature on the battlefield, except it isn't legendary. If you do, it enters with additional counters on it equal to the same number and kinds of counters the copied permanent has on it."
  ]

def emergencyHolographicCrew : CardDef :=
  fromOracle [
    "Emergency Holographic Crew",
    "{3}{U}",
    "Artifact Creature — Illusion Officer",
    "3/4",
    "When this creature enters, choose one —",
    "• Return target Spacecraft card from your graveyard to your hand.",
    "• Surveil 2. (Look at the top two cards of your library, then put any number of them into your graveyard and the rest on top of your library in any order.)"
  ]

def energize : CardDef :=
  fromOracle [
    "Energize",
    "{1}{U}",
    "Sorcery",
    "Return target creature an opponent controls to its owner's hand.",
    "Beam me up {3}{U} (You may cast this card from your graveyard for {3}{U} if you also return a creature you control to its owner's hand. Then exile this spell.)"
  ]

def ensignPavelChekov : CardDef :=
  fromOracle [
    "Ensign Pavel Chekov",
    "{3}{U}",
    "Legendary Creature — Human Pilot",
    "1/5",
    "Strange new worlds — When Ensign Chekov enters, each opponent exiles the top X cards of their library, where X is the number of differently named lands you control. For each opponent, choose a land card that player owns exiled this way. You may play the chosen cards for as long as they remain exiled."
  ]

def enterpriseNX01 : CardDef :=
  fromOracle [
    "Enterprise NX-01",
    "{3}{U}",
    "Legendary Artifact — Spacecraft",
    "When Enterprise NX-01 enters, tap target creature an opponent controls and put a stun counter on it. (If a permanent with a stun counter would become untapped, remove one from it instead.)",
    "Station (Tap another creature you control: Put charge counters equal to its power on this Spacecraft. Station only as a sorcery. It's an artifact creature at 6+.)",
    "6+ | [4/3] Flying, vigilance"
  ]

def federationProbe : CardDef :=
  fromOracle [
    "Federation Probe",
    "{U}",
    "Artifact Creature — Construct",
    "1/1",
    "Flying",
    "When this creature enters, choose one —",
    "• Target creature gets +1/+1 until end of turn.",
    "• Surveil 1. (Look at the top card of your library. You may put it into your graveyard.)"
  ]

def guidanceFailure : CardDef :=
  fromOracle [
    "Guidance Failure",
    "{3}{U}",
    "Instant",
    "This spell costs {1} less to cast if it targets an attacking creature.",
    "Target creature or Spacecraft's owner puts it on their choice of the top or bottom of their library."
  ]

def gwyndalaTheProgeny : CardDef :=
  fromOracle [
    "Gwyndala, the Progeny",
    "{1}{U}",
    "Legendary Creature — Vau-N'Akat Advisor",
    "1/1",
    "When Gwyndala enters, create a colorless Equipment artifact token named Neuroflux Heirloom with \"Equipped creature gets +1/+1\" and equip {2}. Attach it to Gwyndala.",
    "{2}: Each Equipment token you control becomes a copy of target Equipment you control until end of turn."
  ]

def highlyIllogical : CardDef :=
  fromOracle [
    "Highly Illogical",
    "{1}{U}",
    "Instant",
    "Kicker {1}{U} (You may pay an additional {1}{U} as you cast this spell.)",
    "Counter target spell with mana value 2 or less. If this spell was kicked, instead counter target spell."
  ]

def hmsBountyUnlikelyTimeship : CardDef :=
  fromOracle [
    "H.M.S. Bounty, Unlikely Timeship",
    "{4}{U}",
    "Legendary Artifact — Spacecraft",
    "When H.M.S. Bounty enters, you may search your library for a Whale card, reveal it, put it into your hand, then shuffle.",
    "Station",
    "8+ | [3/4] Flying",
    "Whenever H.M.S. Bounty deals combat damage to a player, draw a card. If you control a Whale and haven't begun an extra turn this game, take an extra turn after this one."
  ]

def hoshiSatoExolinguist : CardDef :=
  fromOracle [
    "Hoshi Sato, Exolinguist",
    "{4}{U}",
    "Legendary Creature — Human Scientist",
    "3/3",
    "Federation — When Hoshi Sato enters, look at the top X cards of your library, where X is the number of creature types among non-Borg creatures you control. Put one of them into your hand and the rest on the bottom of your library in a random order."
  ]

def humpbackWhales : CardDef :=
  fromOracle [
    "Humpback Whales",
    "{4}{U}{U}",
    "Creature — Whale",
    "5/6",
    "Vigilance, ward {2} (Whenever this creature becomes the target of a spell or ability an opponent controls, counter it unless that player pays {2}.)",
    "Basic landcycling {2} ({2}, Discard this card: Search your library for a basic land card, reveal it, put it into your hand, then shuffle.)"
  ]

def interstellarEffigy : CardDef :=
  fromOracle [
    "Interstellar Effigy",
    "{4}{U}",
    "Artifact Creature — Construct",
    "4/3",
    "When this creature enters, return target creature an opponent controls to its owner's hand."
  ]

def jettRenoProblemSolver : CardDef :=
  fromOracle [
    "Jett Reno, Problem Solver",
    "{1}{U}",
    "Legendary Creature — Human Artificer",
    "1/2",
    "Whenever Jett Reno becomes tapped, surveil 1. If her power is 4 or greater, instead draw a card.",
    "Whenever you face a dilemma, put a +1/+1 counter on Jett Reno. (You face a dilemma as you choose one or more modes for a spell or ability.)"
  ]

def kobayashiMaruScenario : CardDef :=
  fromOracle [
    "Kobayashi Maru Scenario",
    "{1}{U}{U}",
    "Enchantment",
    "At the beginning of your upkeep, choose one that hasn't been chosen —",
    "• Hail — Return up to one target creature an opponent controls with mana value 3 or less to its owner's hand.",
    "• Sensors — Draw two cards.",
    "• Transport — Create two 1/1 red Officer creature tokens.",
    "• Abandon Ship — You lose the game."
  ]

def lieutenantCommanderData : CardDef :=
  fromOracle [
    "Lieutenant Commander Data",
    "{2}{U}",
    "Legendary Artifact Creature — Android Scientist",
    "2/2",
    "Whenever a player casts a noncreature spell, put a +1/+1 counter on Lieutenant Commander Data.",
    "{1}, Remove three counters from among creatures you control: Draw a card."
  ]

def ltCmdrGeordiLaForge : CardDef :=
  fromOracle [
    "Lt. Cmdr. Geordi La Forge",
    "{2}{U}",
    "Legendary Creature — Human Artificer",
    "3/2",
    "If you would put one or more charge counters on an artifact you control, put twice that many charge counters on that artifact instead."
  ]

def makeItSo : CardDef :=
  fromOracle [
    "Make It So",
    "{3}{U}",
    "Sorcery",
    "Choose one —",
    "• Untap target permanent you control. Target player draws two cards.",
    "• Create a 1/1 red Officer creature token and draw two cards."
  ]

def marooned : CardDef :=
  fromOracle [
    "Marooned",
    "{U}",
    "Enchantment — Aura",
    "Enchant artifact or creature",
    "When this Aura enters, you may pay {3}. If you do, tap enchanted permanent.",
    "Enchanted permanent doesn't untap during its controller's untap step and can't be beamed up."
  ]

def melkotianAdjudicator : CardDef :=
  fromOracle [
    "Melkotian Adjudicator",
    "{2}{U}",
    "Creature — Melkotian Advisor",
    "2/1",
    "Flying, vigilance",
    "Whenever you face a dilemma, put a +1/+1 counter on this creature. (You face a dilemma as you choose one or more modes for a spell or ability.)"
  ]

def mrSpockScienceOfficer : CardDef :=
  fromOracle [
    "Mr. Spock, Science Officer",
    "{2}{U}{U}",
    "Legendary Creature — Vulcan Human Scientist",
    "2/4",
    "If you would draw a card, draw two cards instead."
  ]

def nyotaUhuraCommunications : CardDef :=
  fromOracle [
    "Nyota Uhura, Communications",
    "{2}{U}",
    "Legendary Creature — Human Officer",
    "2/4",
    "Hailing Frequencies — As Nyota Uhura enters, choose a number between 0 and 10.",
    "Open a Channel — Whenever an opponent casts a spell with mana value equal to the chosen number, you draw a card."
  ]

def openCommunications : CardDef :=
  fromOracle [
    "Open Communications",
    "{U}",
    "Sorcery",
    "Draw a card.",
    "Beam me up {2}{U} (You may cast this card from your graveyard for {2}{U} if you also return a creature you control to its owner's hand. Then exile this spell.)"
  ]

def romulanBirdOfPrey : CardDef :=
  fromOracle [
    "Romulan Bird-of-Prey",
    "{1}{U}",
    "Artifact — Spacecraft",
    "Cloaking Device — As long as this Spacecraft isn't a creature, it has hexproof.",
    "Whenever you cast a noncreature spell, if this Spacecraft isn't a creature, put two charge counters on it.",
    "Station",
    "8+ | [4/4] Flying"
  ]

def rulesOfAcquisition : CardDef :=
  fromOracle [
    "Rules of Acquisition",
    "{3}{U}{U}",
    "Sorcery",
    "Choose one —",
    "• Follow the 3rd Rule — Gain control of target nonland permanent an opponent controls. That opponent draws three cards.",
    "• Follow the 98th Rule — Target opponent gains control of target nonland permanent you control. If they do, you draw three cards."
  ]

def scottyMiracleWorker : CardDef :=
  fromOracle [
    "Scotty, Miracle Worker",
    "{1}{U}{U}",
    "Legendary Creature — Human Artificer",
    "2/3",
    "During your main phase, each card in your graveyard has beam me up. The beam me up cost is equal to that spell's mana cost. Scotty can't be beamed up to cast a spell this way. (Only instant and sorcery spells can be cast this way. You may cast a card from your graveyard for its beam me up cost if you also return another creature you control to its owner's hand. Then exile that spell.)"
  ]

def sevenOfNineUnassimilated : CardDef :=
  fromOracle [
    "Seven of Nine, Unassimilated",
    "{1}{U}",
    "Legendary Artifact Creature — Human Officer",
    "0/4",
    "At the beginning of your first main phase, draw a card. Then discard a card unless you control five or more differently named lands.",
    "{6}{U}: Seven of Nine's base power and toughness become 7/9. Activate only if you control seven or more differently named lands."
  ]

def starfleetSpannerJockey : CardDef :=
  fromOracle [
    "Starfleet Spanner Jockey",
    "{1}{U}",
    "Creature — Human Artificer",
    "3/3",
    "Defender",
    "As long as you've cast a noncreature spell this turn, this creature can attack as though it didn't have defender."
  ]

def subcommanderTPol : CardDef :=
  fromOracle [
    "Subcommander T'Pol",
    "{2}{U}",
    "Legendary Creature — Vulcan Scientist",
    "3/1",
    "Flash",
    "When Subcommander T'Pol enters, choose one —",
    "• Counter target activated or triggered ability.",
    "• Tap up to one target artifact or creature. Put a stun counter on it. (If a permanent with a stun counter would become untapped, remove one from it instead.)"
  ]

def suurokClassScienceVessel : CardDef :=
  fromOracle [
    "Suurok-Class Science Vessel",
    "{2}{U}",
    "Artifact — Spacecraft",
    "When this Spacecraft enters, draw a card.",
    "Station (Tap another creature you control: Put charge counters equal to its power on this Spacecraft. Station only as a sorcery. It's an artifact creature at 5+.)",
    "5+ | [3/2] Flying"
  ]

def suusMahnaPractitioner : CardDef :=
  fromOracle [
    "Suus Mahna Practitioner",
    "{2}{U}",
    "Creature — Vulcan Officer",
    "3/2",
    "Strange new worlds — {4}{U}, {T}: Tap target creature. This ability costs {X} less to activate, where X is the number of differently named lands you control."
  ]

def testOfPriorities : CardDef :=
  fromOracle [
    "Test of Priorities",
    "{1}{U}",
    "Instant",
    "Choose one —",
    "• Power to Engines — Surveil 2, then draw a card.",
    "• Power to Life Support — Exile target creature you control. Return that card to the battlefield under its owner's control at the beginning of the next end step."
  ]

def thoseOldScientists : CardDef :=
  fromOracle [
    "Those Old Scientists",
    "{2}{U}",
    "Enchantment — Saga",
    "(As this Saga enters and after your draw step, add a lore counter. Sacrifice after III.)",
    "I — Draw two cards, then discard two cards.",
    "II — Return up to one target artifact, instant, or sorcery card from your graveyard to your hand.",
    "III — Choose up to two target cards in graveyards. The owners of those cards shuffle them into their libraries."
  ]

def vgerTheIntruder : CardDef :=
  fromOracle [
    "V'Ger, the Intruder",
    "{6}{U}",
    "Legendary Artifact Creature — Construct",
    "5/7",
    "Flying",
    "Whenever V'Ger enters or attacks, choose one —",
    "• Look at target opponent's hand, then draw a card.",
    "• Creatures your opponents control get -1/-0 until your next turn."
  ]

def vulcanMindMeld : CardDef :=
  fromOracle [
    "Vulcan Mind-Meld",
    "{U}",
    "Sorcery",
    "Target opponent looks at the top card of your library, then exiles it face down. You look at the top two cards of their library, then exile them face down. For each card exiled this way, the player who exiled it may play it for as long as it remains exiled. Mana of any type can be spent to cast spells this way."
  ]

def wesleyCrusherStarfleetCadet : CardDef :=
  fromOracle [
    "Wesley Crusher, Starfleet Cadet",
    "{2}{U}{U}",
    "Legendary Creature — Human Officer",
    "2/2",
    "Flash",
    "When Wesley Crusher enters, choose two —",
    "• Counter target noncreature spell unless its controller pays {2}.",
    "• Return target creature with mana value 2 or less to its owner's hand.",
    "• Target creature can't be blocked this turn.",
    "• Target player draws two cards, then discards two cards."
  ]

def zeframCochraneWarpPioneer : CardDef :=
  fromOracle [
    "Zefram Cochrane, Warp Pioneer",
    "{2}{U}",
    "Legendary Creature — Human Pilot",
    "2/3",
    "You may look at the top card of your library any time.",
    "Once during each of your turns, you may cast an artifact spell from the top of your library.",
    "Spacecraft you control enter with two additional charge counters on them."
  ]

def armusSkinOfEvil : CardDef :=
  fromOracle [
    "Armus, Skin of Evil",
    "{5}{B}{B}",
    "Legendary Creature — Ooze Horror",
    "6/6",
    "Menace",
    "At the beginning of your end step, target opponent discards two cards.",
    "{2}{B}, Discard this card: Target creature gets -4/-4 until end of turn."
  ]

def assaultDrone : CardDef :=
  fromOracle [
    "Assault Drone",
    "{3}{B}",
    "Artifact Creature — Borg",
    "2/4",
    "Artifact creatures you control get +1/+0."
  ]

def automatedWarfareSystem : CardDef :=
  fromOracle [
    "Automated Warfare System",
    "{2}{B}",
    "Artifact Creature — Construct",
    "2/2",
    "Flying",
    "Whenever this creature attacks, you may sacrifice another creature or artifact. If you do, draw a card."
  ]

def batleth : CardDef :=
  fromOracle [
    "Bat'leth",
    "{2}{B}",
    "Artifact — Equipment",
    "When this Equipment enters, target creature an opponent controls gets -2/-2 until end of turn.",
    "Equipped creature gets +2/+0.",
    "Equip {2} ({2}: Attach to target creature you control. Equip only as a sorcery.)"
  ]

def battleScarredSurvivalist : CardDef :=
  fromOracle [
    "Battle-Scarred Survivalist",
    "{1}{B}",
    "Creature — Klingon Scout",
    "1/1",
    "Menace (This creature can't be blocked except by two or more creatures.)",
    "Whenever another creature dies, put a +1/+1 counter on this creature. This ability triggers only once each turn."
  ]

def blastoneuron : CardDef :=
  fromOracle [
    "Blastoneuron",
    "{3}{B}",
    "Creature — Jellyfish Leech",
    "2/2",
    "Flying",
    "When this creature enters, exile target creature card with mana value 3 or less from your graveyard. Create a token that's a copy of it. That token gains haste. Sacrifice it at the beginning of the next end step.",
    "Whenever one or more cards leave your graveyard, each opponent loses 1 life and you gain 1 life."
  ]

def chadichInvestigator : CardDef :=
  fromOracle [
    "Cha'DIch Investigator",
    "{4}{B}",
    "Creature — Klingon Warrior",
    "4/4",
    "When this creature enters, create a 2/1 red Klingon Warrior creature token with haste."
  ]

def collationTrimatrix : CardDef :=
  fromOracle [
    "Collation Trimatrix",
    "{B}",
    "Artifact Creature — Borg",
    "1/1",
    "Tap three untapped artifact creatures you control: You draw a card and lose 1 life."
  ]

def collectiveDrone : CardDef :=
  fromOracle [
    "Collective Drone",
    "{1}{B}",
    "Artifact Creature — Borg",
    "*/2",
    "Collective Drone's power is equal to the number of artifact creatures you control."
  ]

def commanderRaffiMusiker : CardDef :=
  fromOracle [
    "Commander Raffi Musiker",
    "{2}{B}",
    "Legendary Creature — Human Officer",
    "3/2",
    "When Commander Musiker enters, choose one —",
    "• Exile up to one target card from a graveyard. You gain 2 life.",
    "• Investigate. You lose 2 life. (Create a Clue token. It's an artifact with \"{2}, Sacrifice this token: Draw a card.\")"
  ]

def dghorBloodletter : CardDef :=
  fromOracle [
    "D'Ghor Bloodletter",
    "{2}{B}",
    "Creature — Klingon Assassin",
    "2/2",
    "When this creature enters, choose one —",
    "• All other creatures get -1/-1 until end of turn.",
    "• Each player sacrifices a creature of their choice."
  ]

def deathIsIrrelevant : CardDef :=
  fromOracle [
    "Death Is Irrelevant",
    "{6}{B}{B}",
    "Enchantment",
    "Artifact creatures you control have indestructible.",
    "At the beginning of your end step, assimilate target creature card from a graveyard. (Put it onto the battlefield under your control with a +1/+1 counter. It's a Borg artifact creature and loses all other creature types.)"
  ]

def theDestructionOfPraxis : CardDef :=
  fromOracle [
    "The Destruction of Praxis",
    "{3}{B}{B}",
    "Sorcery",
    "Strange new worlds — All creatures get -X/-X until end of turn, where X is the number of differently named lands you control. If X is 6 or more, create two 2/1 red Klingon Warrior creature tokens with haste."
  ]

def deEvolve : CardDef :=
  fromOracle [
    "De-evolve",
    "{1}{B}",
    "Enchantment — Aura",
    "Enchant creature",
    "Enchanted creature gets -4/-0, can't block, and is a Salamander. (It loses all other creature types.)",
    "Threshold — At the beginning of each upkeep, if there are seven or more cards in your graveyard, exile enchanted creature."
  ]

def ejectTheWarpCore : CardDef :=
  fromOracle [
    "Eject the Warp Core",
    "{1}{B}",
    "Instant",
    "Kicker—Sacrifice an artifact or creature. (You may sacrifice an artifact or creature in addition to any other costs as you cast this spell.)",
    "Target creature gets -2/-2 until end of turn. If this spell was kicked, that creature gets -6/-6 until end of turn instead."
  ]

def elimGarakSimpleTailor : CardDef :=
  fromOracle [
    "Elim Garak, Simple Tailor",
    "{2}{B}",
    "Legendary Creature — Cardassian Rogue",
    "3/3",
    "Menace",
    "Whenever you face a dilemma, each opponent loses 2 life and you gain 2 life. (You face a dilemma as you choose one or more modes for a spell or ability.)"
  ]

def fugitiveListener : CardDef :=
  fromOracle [
    "Fugitive Listener",
    "{2}{B}",
    "Creature — El-Aurian Scout",
    "3/1",
    "When this creature enters, each opponent discards a card."
  ]

def gabrielLorcaMirrorMenace : CardDef :=
  fromOracle [
    "Gabriel Lorca, Mirror Menace",
    "{4}{B}",
    "Legendary Creature — Human Rogue Officer",
    "5/4",
    "Menace",
    "Whenever you face a dilemma, you may pay {B}. If you do, return this card from your graveyard to your hand. (You face a dilemma as you choose one or more modes for a spell or ability.)"
  ]

def generalChangColdWarrior : CardDef :=
  fromOracle [
    "General Chang, Cold Warrior",
    "{B}",
    "Legendary Creature — Klingon Warrior Officer",
    "1/2",
    "{1}, Sacrifice a creature: Put a +1/+1 counter on each Klingon you control."
  ]

def georgiouTerranEmperor : CardDef :=
  fromOracle [
    "Georgiou, Terran Emperor",
    "{4}{B}{B}",
    "Legendary Creature — Human Rogue Noble",
    "4/6",
    "You don't lose the game for having 0 or less life.",
    "At the beginning of your end step, you lose 3 life and draw a card. Then if your life total is 0 or less, create ten 1/1 red Officer creature tokens."
  ]

def aGoodDayToDie : CardDef :=
  fromOracle [
    "A Good Day to Die",
    "{B}",
    "Instant",
    "Target creature gets +2/+0 until end of turn. When that creature dies this turn, you draw a card."
  ]

def grandNagusZek : CardDef :=
  fromOracle [
    "Grand Nagus Zek",
    "{2}{B}",
    "Legendary Creature — Ferengi Noble",
    "1/1",
    "Grand Nagus Zek gets +1/+1 for each Treasure you control.",
    "Whenever another creature dies, create a Treasure token. This ability triggers only once each turn. (It's an artifact with \"{T}, Sacrifice this token: Add one mana of any color.\")"
  ]

def gulDukatColonialPrefect : CardDef :=
  fromOracle [
    "Gul Dukat, Colonial Prefect",
    "{4}{B}{B}{B}",
    "Legendary Creature — Cardassian Rogue",
    "6/6",
    "Menace",
    "At the beginning of each end step, each opponent loses life equal to the life that player lost this turn. You gain life equal to the life lost this way. (Damage causes loss of life.)"
  ]

def hesDeadJim : CardDef :=
  fromOracle [
    "He's Dead, Jim",
    "{3}{B}",
    "Instant",
    "Destroy target creature. Surveil 1. (Look at the top card of your library. You may put it into your graveyard.)"
  ]

def hiveMindCoprocessor : CardDef :=
  fromOracle [
    "Hive Mind Coprocessor",
    "{4}{B}",
    "Artifact Creature — Borg",
    "4/4",
    "Artifact creatures you control have \"Whenever this creature deals combat damage to a player, you may pay 1 life. If you do, draw a card.\""
  ]

def impossibleChoice : CardDef :=
  fromOracle [
    "Impossible Choice",
    "{2}{B}",
    "Instant",
    "Choose one —",
    "• Surgical Separation — Destroy target creature. Its controller creates two 1/1 red Officer creature tokens.",
    "• Remain Fused — You draw two cards and each player loses 2 life."
  ]

def inThePaleMoonlight : CardDef :=
  fromOracle [
    "In the Pale Moonlight",
    "{3}{B}{B}",
    "Enchantment — Saga",
    "(As this Saga enters and after your draw step, add a lore counter. Sacrifice after III.)",
    "I — Each opponent sacrifices a nontoken creature of their choice.",
    "II — Investigate. (Create a Clue token. It's an artifact with \"{2}, Sacrifice this token: Draw a card.\")",
    "III — You may sacrifice an artifact or creature. If you do, create two 2/2 black Romulan creature tokens."
  ]

def kaiWinnFaithlessLeader : CardDef :=
  fromOracle [
    "Kai Winn, Faithless Leader",
    "{1}{B}",
    "Legendary Creature — Bajoran Cleric",
    "3/1",
    "As Kai Winn enters, choose a nonland card name.",
    "Whenever an opponent casts a spell with the chosen name or activates an ability of a source with the chosen name, that player loses 3 life."
  ]

def khanVengefulHeart : CardDef :=
  fromOracle [
    "Khan, Vengeful Heart",
    "{2}{B}{B}",
    "Legendary Creature — Human Warrior",
    "5/3",
    "When Khan enters, you may sacrifice another creature or artifact. If you do, draw two cards.",
    "You may cast this card from exile."
  ]

def obsidianOrderOperative : CardDef :=
  fromOracle [
    "Obsidian Order Operative",
    "{3}{B}",
    "Creature — Cardassian Officer Spy",
    "2/5",
    "Whenever you face a dilemma, each opponent loses 1 life and you gain 1 life. (You face a dilemma as you choose one or more modes for a spell or ability.)"
  ]

def organicAvulsionUnit : CardDef :=
  fromOracle [
    "Organic Avulsion Unit",
    "{2}{B}",
    "Artifact Creature — Borg",
    "2/3",
    "{2}: Artifact creatures you control gain menace until end of turn. (A creature with menace can't be blocked except by two or more creatures.)"
  ]

def overflowSubmatrix : CardDef :=
  fromOracle [
    "Overflow Submatrix",
    "{2}{B}",
    "Artifact Creature — Borg",
    "3/3",
    "Once during each of your turns, you may cast an artifact creature spell from your graveyard. If you cast a spell this way, that artifact creature enters with a finality counter on it. (If a creature with a finality counter on it would die, exile it instead.)"
  ]

def patternBufferPreservation : CardDef :=
  fromOracle [
    "Pattern Buffer Preservation",
    "{1}{B}",
    "Sorcery",
    "Look at the top two cards of your library. Put one of them into your hand and the other into your graveyard.",
    "Beam me up {1}{B} (You may cast this card from your graveyard for {1}{B} if you also return a creature you control to its owner's hand. Then exile this spell.)"
  ]

def relentlessDrednok : CardDef :=
  fromOracle [
    "Relentless Drednok",
    "{B}",
    "Artifact Creature — Robot",
    "1/1",
    "Lifelink",
    "{2}{B}, Exile this card from your graveyard: You draw a card and lose 1 life."
  ]

def resistanceIsFutile : CardDef :=
  fromOracle [
    "Resistance Is Futile",
    "{1}{B}",
    "Sorcery",
    "Choose one —",
    "• Destroy target nonartifact creature.",
    "• Return target artifact creature card with mana value 3 or less from your graveyard to the battlefield."
  ]

def rogueArtificialIntelligence : CardDef :=
  fromOracle [
    "Rogue Artificial Intelligence",
    "{4}{B}{B}",
    "Artifact Creature — Construct",
    "6/5",
    "When this creature enters, choose one —",
    "• You gain 3 life.",
    "• Surveil 2. (Look at the top two cards of your library, then put any number of them into your graveyard and the rest on top of your library in any order.)",
    "Basic landcycling {2} ({2}, Discard this card: Search your library for a basic land card, reveal it, put it into your hand, then shuffle.)"
  ]

def saltVampire : CardDef :=
  fromOracle [
    "Salt Vampire",
    "{1}{B}",
    "Creature — Vampire Shapeshifter",
    "2/2",
    "Lifelink",
    "When this creature enters, look at target opponent's hand. You may choose a nonland card from it. If you do, that player exiles that card, then draws a card."
  ]

def selaTalShiarParadox : CardDef :=
  fromOracle [
    "Sela, Tal Shiar Paradox",
    "{3}{B}",
    "Legendary Creature — Romulan Human Rogue",
    "3/3",
    "Whenever Sela attacks, exile up to one target card from a graveyard.",
    "Whenever one or more cards leave your graveyard, create a tapped 2/2 black Romulan creature token."
  ]

def storiedVeteran : CardDef :=
  fromOracle [
    "Storied Veteran",
    "{B}",
    "Creature — Klingon Advisor",
    "2/1",
    "This creature can't block.",
    "You may cast this card from your graveyard. If you do, it enters with a finality counter on it. (If a creature with a finality counter on it would die, exile it instead.)"
  ]

def strayFromHistory : CardDef :=
  fromOracle [
    "Stray from History",
    "{2}{B}",
    "Sorcery",
    "Choose one —",
    "• Rewrite the Past — Return one or two target creature and/or Spacecraft cards from your graveyard to your hand.",
    "• Repair the Timeline — Target opponent reveals their hand. You choose a nonland card from it. Exile that card."
  ]

def talShiarOperative : CardDef :=
  fromOracle [
    "Tal Shiar Operative",
    "{1}{B}",
    "Creature — Romulan Officer Spy",
    "2/2",
    "Whenever this creature attacks, choose one —",
    "• Target creature you control gains deathtouch until end of turn.",
    "• Surveil 1. (Look at the top card of your library. You may put it into your graveyard.)"
  ]

def tellMeWhatYouSee : CardDef :=
  fromOracle [
    "Tell Me What You See",
    "{1}{B}",
    "Enchantment",
    "When this enchantment enters, target opponent may have you draw a card. If they don't, they lose 4 life and you surveil 1.",
    "Whenever you face a dilemma, you may return this enchantment to its owner's hand. (You face a dilemma as you choose one or more modes for a spell or ability.)"
  ]

def tenaciousDrone : CardDef :=
  fromOracle [
    "Tenacious Drone",
    "{1}{B}",
    "Artifact Creature — Borg",
    "2/1",
    "When this creature dies, create a 1/1 colorless Borg artifact creature token."
  ]

def testOfLoyalty : CardDef :=
  fromOracle [
    "Test of Loyalty",
    "{B}",
    "Sorcery",
    "Choose one —",
    "• Plain, Simple Garak — Exile target card from a graveyard. Draw a card.",
    "• Of the Obsidian Order — Return target creature card from your graveyard to your hand."
  ]

def ussReliantFromHellsHeart : CardDef :=
  fromOracle [
    "U.S.S. Reliant, From Hell's Heart",
    "{2}{B}{B}",
    "Legendary Artifact — Spacecraft",
    "Whenever U.S.S. Reliant enters or deals combat damage to a player, return target creature card with mana value 4 or less from your graveyard to the battlefield with a finality counter on it.",
    "Station (Tap another creature you control: Put charge counters equal to its power on this Spacecraft. Station only as a sorcery. It's an artifact creature at 10+.)",
    "10+ | [4/3] Flying"
  ]

def vengeanceMission : CardDef :=
  fromOracle [
    "Vengeance Mission",
    "{2}{B}",
    "Enchantment",
    "Whenever a creature dies, put a quest counter on this enchantment. Target opponent loses 1 life. That player loses 2 life instead if there are seven or more quest counters on this enchantment."
  ]

def academyInstructor : CardDef :=
  fromOracle [
    "Academy Instructor",
    "{2}{R}",
    "Creature — Bolian Officer",
    "0/3",
    "This creature gets +1/+0 for each Officer token you control.",
    "Whenever you cast a noncreature spell, create a 1/1 red Officer creature token."
  ]

def beckettMarinerImpetuousEnsign : CardDef :=
  fromOracle [
    "Beckett Mariner, Impetuous Ensign",
    "{1}{R}",
    "Legendary Creature — Human Officer",
    "2/1",
    "First strike",
    "Reckless Behavior — Whenever Beckett Mariner becomes tapped, put a promotion counter on her. Then if there are three or more promotion counters on her, remove those counters and she deals 2 damage to each opponent."
  ]

def boardingAction : CardDef :=
  fromOracle [
    "Boarding Action",
    "{1}{R}",
    "Sorcery",
    "Create a 2/1 red Klingon Warrior creature token with haste.",
    "Beam me up {2}{R} (You may cast this card from your graveyard for {2}{R} if you also return a creature you control to its owner's hand. Then exile this spell.)"
  ]

def brazenBluff : CardDef :=
  fromOracle [
    "Brazen Bluff",
    "{R}{R}",
    "Instant",
    "Choose target noncreature spell an opponent controls. That player may exile it. If they don't, you may cast a noncreature spell from your hand without paying its mana cost."
  ]

def cantankerousCaptain : CardDef :=
  fromOracle [
    "Cantankerous Captain",
    "{2}{R}",
    "Creature — Tellarite Officer",
    "2/3",
    "At the beginning of combat on your turn, target creature you control gets +1/+0 until end of turn. Then that creature gains menace until end of turn if creatures you control have total power 8 or greater. (It can't be blocked except by two or more creatures.)"
  ]

def captainJamesTKirk : CardDef :=
  fromOracle [
    "Captain James T. Kirk",
    "{2}{R}",
    "Legendary Creature — Human Officer",
    "2/2",
    "Whenever Captain Kirk enters or attacks, choose one. If you have no cards in hand, choose one or more instead.",
    "• Discard a card, then draw a card.",
    "• Create a 1/1 red Officer creature token.",
    "• Creatures you control get +1/+0 until end of turn."
  ]

def captainMichaelBurnham : CardDef :=
  fromOracle [
    "Captain Michael Burnham",
    "{2}{R}",
    "Legendary Creature — Human Officer",
    "3/3",
    "Trample",
    "Landfall — Whenever a land you control enters, Captain Burnham deals 1 damage to each opponent. If this is the second time this ability has resolved this turn, put a +1/+1 counter on Captain Burnham."
  ]

def captainsTutelage : CardDef :=
  fromOracle [
    "Captain's Tutelage",
    "{1}{R}",
    "Enchantment — Aura",
    "Flash",
    "Enchant creature",
    "When this Aura enters, enchanted creature gains first strike until end of turn.",
    "Enchanted creature gets +2/+0."
  ]

def d7BattleCruiser : CardDef :=
  fromOracle [
    "D-7 Battle Cruiser",
    "{1}{R}",
    "Artifact — Spacecraft",
    "Station (Tap another creature you control: Put charge counters equal to its power on this Spacecraft. Station only as a sorcery. It's an artifact creature at 8+.)",
    "3+ | At the beginning of combat on your turn, create a 2/1 red Klingon Warrior creature token with haste. Sacrifice it at the beginning of the next end step.",
    "8+ | [3/3] Flying"
  ]

def daharMaster : CardDef :=
  fromOracle [
    "Dahar Master",
    "{3}{R}",
    "Creature — Klingon Warrior",
    "4/3",
    "When this creature enters, you may sacrifice another nonland permanent. When you do, this creature deals 2 damage to any target."
  ]

def dominionInfiltration : CardDef :=
  fromOracle [
    "Dominion Infiltration",
    "{X}{R}{R}{R}",
    "Sorcery",
    "Choose X target creatures your opponents control. For each of them, create a token that's a copy of that creature, except it has changeling. Those tokens gain haste. Exile those tokens at the beginning of the next end step. (They're every creature type.)"
  ]

def encounterTheUnknown : CardDef :=
  fromOracle [
    "Encounter the Unknown",
    "{1}{R}{R}",
    "Instant",
    "Choose one —",
    "• Come in Peace — Exile the top two cards of your library. Until the end of your next turn, you may play those cards.",
    "• Shoot to Kill — Encounter the Unknown deals 2 damage to each creature and each player."
  ]

def ericaOrtegasPluckyPilot : CardDef :=
  fromOracle [
    "Erica Ortegas, Plucky Pilot",
    "{3}{R}",
    "Legendary Creature — Human Pilot",
    "3/3",
    "Haste",
    "Whenever Erica Ortegas becomes tapped, you may put a land card from your hand onto the battlefield. If you do, return a land you control to its owner's hand at the beginning of the next end step."
  ]

def exploratoryMission : CardDef :=
  fromOracle [
    "Exploratory Mission",
    "{2}{R}{R}",
    "Enchantment",
    "Landfall — Whenever a land you control enters, put a quest counter on this enchantment. Then exile cards from the top of your library until you exile a nonland card. You may play that card this turn. If this enchantment has five or more quest counters on it, add {R}{R}."
  ]

def genesisEffect : CardDef :=
  fromOracle [
    "Genesis Effect",
    "{4}{R}",
    "Instant",
    "Genesis Effect deals 6 damage to target creature. Destroy target land you control. Create a tapped Planet land token named New Planet with \"{T}: Add one mana of any color.\""
  ]

def horta : CardDef :=
  fromOracle [
    "Horta",
    "{4}{R}{R}",
    "Creature — Elemental",
    "7/6",
    "Trample",
    "Basic landcycling {2} ({2}, Discard this card: Search your library for a basic land card, reveal it, put it into your hand, then shuffle.)"
  ]

def infiniteDiversity : CardDef :=
  fromOracle [
    "Infinite Diversity",
    "{7}{R}{R}",
    "Sorcery",
    "Federation — Exile target instant or sorcery card from your graveyard. Copy that card X times, where X is the number of creature types among non-Borg creatures you control. You may cast the copies without paying their mana costs. Exile Infinite Diversity."
  ]

def khaaaaaaaaaaaannn : CardDef :=
  fromOracle [
    "Khaaaaaaaaaaaannn!",
    "{X}{R}",
    "Instant",
    "Khaaaaaaaaaaaannn! deals twice X damage to target creature. If that creature would die this turn, exile it instead."
  ]

def khanDespotByDesign : CardDef :=
  fromOracle [
    "Khan, Despot by Design",
    "{4}{R}",
    "Legendary Creature — Human Rogue",
    "5/4",
    "Trample",
    "When Khan enters, he deals 1 damage to each opponent and each creature your opponents control."
  ]

def laanNoonienSinghSecurity : CardDef :=
  fromOracle [
    "La'An Noonien-Singh, Security",
    "{2}{R}{R}",
    "Legendary Creature — Human Soldier",
    "4/3",
    "Whenever you attack while creatures you control have total power 8 or greater, target creature can't block this turn."
  ]

def lwaxanaTroiCharmingGuest : CardDef :=
  fromOracle [
    "Lwaxana Troi, Charming Guest",
    "{1}{R}",
    "Legendary Creature — Betazoid Advisor",
    "2/2",
    "You may choose not to untap Lwaxana Troi during your untap step.",
    "{2}, {T}: Choose another target creature you control. For as long as Lwaxana Troi remains tapped, if a triggered ability of that creature triggers, that ability triggers an additional time."
  ]

def munitionsEnthusiast : CardDef :=
  fromOracle [
    "Munitions Enthusiast",
    "{1}{R}",
    "Creature — Klingon Warrior",
    "3/2",
    "Trample",
    "When this creature dies, it deals 1 damage to any target."
  ]

def theNakedTime : CardDef :=
  fromOracle [
    "The Naked Time",
    "{1}{R}",
    "Enchantment — Saga",
    "(As this Saga enters and after your draw step, add a lore counter. Sacrifice after III.)",
    "I — Search your library for a basic Mountain card, put it onto the battlefield tapped, then shuffle.",
    "II — Whenever a creature you control enters this turn, put a +1/+1 counter on it and it gains haste until end of turn.",
    "III — Sacrifice a land."
  ]

def pahWraith : CardDef :=
  fromOracle [
    "Pah-Wraith",
    "{5}{R}{R}",
    "Creature — Wraith",
    "4/4",
    "First strike, haste",
    "Strange new worlds — Whenever this creature attacks, creatures you control get +X/+0 until end of turn, where X is the number of differently named lands you control."
  ]

def perilsOfThePast : CardDef :=
  fromOracle [
    "Perils of the Past",
    "{1}{R}",
    "Instant",
    "Choose one —",
    "• Use the Relic — Target creature gets +3/+2 until end of turn.",
    "• Destroy the Relic — Destroy target artifact."
  ]

def planetaryBombardment : CardDef :=
  fromOracle [
    "Planetary Bombardment",
    "{R}",
    "Sorcery",
    "Planetary Bombardment deals 2 damage to target creature. Planetary Bombardment deals 4 damage to that creature instead if a creature died this turn."
  ]

def planetaryPatrol : CardDef :=
  fromOracle [
    "Planetary Patrol",
    "{1}{R}",
    "Creature — Scout",
    "2/2",
    "Landfall — Whenever a land you control enters, this creature gets +1/+1 until end of turn."
  ]

def plasmaCascade : CardDef :=
  fromOracle [
    "Plasma Cascade",
    "{2}{R}",
    "Instant",
    "Plasma Cascade deals 3 damage to any target. You may discard a card. If you do, draw a card."
  ]

def qStackingTheDeck : CardDef :=
  fromOracle [
    "Q, Stacking the Deck",
    "{2}{R}{R}",
    "Legendary Creature — Q",
    "4/4",
    "When Q enters, shuffle your library, then exile cards from the top of your library until you exile a nonland card. That nonland card gains \"Exile a card from your hand: Create a copy of this card. You may cast the copy. Activate only during your turn and only if this card is exiled.\""
  ]

def quarkHumbleProprietor : CardDef :=
  fromOracle [
    "Quark, Humble Proprietor",
    "{2}{R}",
    "Legendary Creature — Ferengi Rogue",
    "1/2",
    "You can't sacrifice Treasure tokens.",
    "At the beginning of each upkeep, create a Treasure token. (It's an artifact with \"{T}, Sacrifice this token: Add one mana of any color.\")"
  ]

def ravenousCosmozoan : CardDef :=
  fromOracle [
    "Ravenous Cosmozoan",
    "{5}{R}",
    "Creature — Fish",
    "3/3",
    "This spell costs {1} less to cast for each noncreature, nonland card in your graveyard.",
    "Flying, haste"
  ]

def recklessImpulse : CardDef :=
  fromOracle [
    "Reckless Impulse",
    "{1}{R}",
    "Sorcery",
    "Exile the top two cards of your library. Until the end of your next turn, you may play those cards."
  ]

def redAlert : CardDef :=
  fromOracle [
    "Red Alert!",
    "{2}{R}",
    "Instant",
    "This spell costs {2} less to cast if a creature is attacking you.",
    "Creatures you control get +2/+0 until end of turn."
  ]

def sarcophagusShipOfTheDead : CardDef :=
  fromOracle [
    "Sarcophagus, Ship of the Dead",
    "{2}{R}",
    "Legendary Artifact — Spacecraft",
    "Other creatures you control get +1/+0.",
    "Whenever a creature dies, if Sarcophagus isn't a creature, put a charge counter on it.",
    "Station (Tap another creature you control: Put charge counters equal to its power on this Spacecraft. Station only as a sorcery. It's an artifact creature at 10+.)",
    "10+ | [4/4] Flying"
  ]

def savvyProfiteer : CardDef :=
  fromOracle [
    "Savvy Profiteer",
    "{1}{R}",
    "Creature — Ferengi Rogue",
    "2/1",
    "{T}: Add {R}.",
    "{3}, {T}: Create a Treasure token. (It's an artifact with \"{T}, Sacrifice this token: Add one mana of any color.\")"
  ]

def silicateSurveyor : CardDef :=
  fromOracle [
    "Silicate Surveyor",
    "{4}{R}",
    "Creature — Tholian Scout",
    "4/4",
    "Reach",
    "When this creature enters, exile the top card of your library. Until the end of your next turn, you may play that card."
  ]

def starfleetSecurity : CardDef :=
  fromOracle [
    "Starfleet Security",
    "{R}",
    "Creature — Human Officer",
    "1/1",
    "Haste",
    "When this creature dies during your turn, investigate. (Create a Clue token. It's an artifact with \"{2}, Sacrifice this token: Draw a card.\")"
  ]

def talShiarAnalyst : CardDef :=
  fromOracle [
    "Tal Shiar Analyst",
    "{2}{R}",
    "Creature — Romulan Scientist",
    "3/2",
    "{T}: This creature deals 1 damage to each opponent.",
    "Whenever you cast a noncreature spell, untap this creature."
  ]

def targWrangler : CardDef :=
  fromOracle [
    "Targ Wrangler",
    "{2}{R}",
    "Creature — Klingon Warrior",
    "5/3",
    "Menace (This creature can't be blocked except by two or more creatures.)",
    "At the beginning of your end step, if this creature attacked this turn, sacrifice a nonland permanent."
  ]

def tashaYarOutOfTime : CardDef :=
  fromOracle [
    "Tasha Yar, Out of Time",
    "{1}{R}",
    "Legendary Creature — Human Officer",
    "2/1",
    "Haste",
    "When Tasha Yar dies, exile the top card of your library. Until the end of your next turn, you may play that card.",
    "{2}{R}, Exile this card from your graveyard: Create a token that's a copy of this card. Sacrifice it at the beginning of the next end step. Activate only as a sorcery."
  ]

def testOfIdentity : CardDef :=
  fromOracle [
    "Test of Identity",
    "{1}{R}",
    "Instant",
    "Choose one —",
    "• I Am Klingon — Target Klingon gets +1/+1 and gains double strike until end of turn.",
    "• I Am Starfleet — Discard a card. If you do, draw two cards."
  ]

def transporterMalfunction : CardDef :=
  fromOracle [
    "Transporter Malfunction",
    "{1}{R}",
    "Sorcery",
    "Transporter Malfunction deals 3 damage to any target.",
    "Beam me up {3}{R}{R}{R} (You may cast this card from your graveyard for {3}{R}{R}{R} if you also return a creature you control to its owner's hand. Then exile this spell.)"
  ]

def willRikerFirstInTheField : CardDef :=
  fromOracle [
    "Will Riker, First in the Field",
    "{3}{R}",
    "Legendary Creature — Human Officer",
    "4/3",
    "At the beginning of combat on your turn, reveal cards from the top of your library until you reveal two land cards. Put those land cards onto the battlefield and the rest on the bottom of your library in a random order. Sacrifice those lands at the beginning of your next end step."
  ]

def worfIntelligenceContractor : CardDef :=
  fromOracle [
    "Worf, Intelligence Contractor",
    "{2}{R}",
    "Legendary Creature — Klingon Warrior Spy",
    "3/2",
    "When Worf enters, for each opponent, gain control of up to one target creature that player controls with mana value 3 or less until end of turn. Untap those creatures. Until end of turn, they become Warriors in addition to their other types and gain haste."
  ]

def theWrathOfKhan : CardDef :=
  fromOracle [
    "The Wrath of Khan",
    "{2}{R}",
    "Enchantment — Saga",
    "(As this Saga enters and after your draw step, add a lore counter. Sacrifice after III.)",
    "I — This Saga deals 4 damage to target creature an opponent controls. At the beginning of the next combat this turn, gain control of that creature until end of turn. Untap it. It gains haste until end of turn.",
    "II — You may exile a card from your hand. If you do, draw a card.",
    "III — Each opponent sacrifices a nontoken permanent of their choice."
  ]

def adversaryByAlgorithm : CardDef :=
  fromOracle [
    "Adversary by Algorithm",
    "{2}{G}",
    "Sorcery",
    "Create a 3/3 colorless Illusion artifact creature token.",
    "Beam me up {3}{G} (You may cast this card from your graveyard for {3}{G} if you also return a creature you control to its owner's hand. Then exile this spell.)"
  ]

def amokTime : CardDef :=
  fromOracle [
    "Amok Time",
    "{2}{G}",
    "Enchantment — Saga",
    "(As this Saga enters and after your draw step, add a lore counter. Sacrifice after III.)",
    "I — Target creature you control fights up to one target creature an opponent controls.",
    "II — You gain 3 life.",
    "III — Return target creature card from your graveyard to your hand."
  ]

def astuteTerraformer : CardDef :=
  fromOracle [
    "Astute Terraformer",
    "{1}{G}",
    "Creature — Vulcan Scientist",
    "2/2",
    "Strange new worlds — {6}: This creature gets +2/+2 until end of turn. This ability costs {X} less to activate, where X is the number of differently named lands you control. Activate only once each turn."
  ]

def branchingTimeline : CardDef :=
  fromOracle [
    "Branching Timeline",
    "{6}{G}{G}",
    "Sorcery",
    "Strange new worlds — Reveal the top X cards of your library, where X is the number of differently named lands you control. Put all permanent cards revealed this way onto the battlefield tapped and the rest on the bottom of your library in a random order."
  ]

def captainJonathanArcher : CardDef :=
  fromOracle [
    "Captain Jonathan Archer",
    "{2}{G}",
    "Legendary Creature — Human Officer",
    "3/3",
    "When Captain Archer enters, create Porthos, a legendary 1/1 green Dog creature token.",
    "Federation — {G}, {T}: Target creature you control gets +X/+X until end of turn, where X is the number of creature types among non-Borg creatures you control. Activate only as a sorcery."
  ]

def captainKathrynJaneway : CardDef :=
  fromOracle [
    "Captain Kathryn Janeway",
    "{3}{G}",
    "Legendary Creature — Human Officer",
    "2/3",
    "You may play an additional land on each of your turns.",
    "Whenever Captain Janeway or another creature you control enters, that creature explores. (Reveal the top card of your library. Put that card into your hand if it's a land. Otherwise, put a +1/+1 counter on the creature, then put the card back or put it into your graveyard.)"
  ]

def captainPikeFullnessOfTime : CardDef :=
  fromOracle [
    "Captain Pike, Fullness of Time",
    "{1}{G}{G}",
    "Legendary Creature — Human Officer Scout",
    "*/*",
    "Strange new worlds — Captain Pike's power and toughness are each equal to the number of differently named lands you control.",
    "You may look at the top card of your library any time.",
    "You may play lands from the top of your library."
  ]

def coldBloodedCrew : CardDef :=
  fromOracle [
    "Cold-Blooded Crew",
    "{4}{G}{G}",
    "Creature — Gorn Warrior",
    "4/4",
    "When this creature enters, put two +1/+1 counters on target creature.",
    "This creature can't be blocked by creatures with power 2 or less.",
    "Basic landcycling {2} ({2}, Discard this card: Search your library for a basic land card, reveal it, put it into your hand, then shuffle.)"
  ]

def commonGoal : CardDef :=
  fromOracle [
    "Common Goal",
    "{1}{G}",
    "Sorcery",
    "One or two target creatures you control each deal damage equal to their power to target creature an opponent controls."
  ]

def culberAndStametsStarCrossed : CardDef :=
  fromOracle [
    "Culber and Stamets, Star-Crossed",
    "{3}{G}",
    "Legendary Creature — Human Doctor Artificer",
    "3/4",
    "When Culber and Stamets enter, choose one —",
    "• Put a +1/+1 counter on target creature.",
    "• Add two mana of any one color."
  ]

def dathonAndPicardAtElAdrel : CardDef :=
  fromOracle [
    "Dathon and Picard at El-Adrel",
    "{2}{G}",
    "Instant",
    "Choose one —",
    "• Temba, His Arms Wide — Target creature gets +3/+3 and gains trample until end of turn.",
    "• Shaka, When the Walls Fell — Each opponent sacrifices a nontoken artifact or enchantment of their choice."
  ]

def davidAndCarolMarcusCreators : CardDef :=
  fromOracle [
    "David and Carol Marcus, Creators",
    "{2}{G}",
    "Legendary Creature — Human Scientist",
    "1/3",
    "When David and Carol Marcus enter, create a tapped Planet land token named New Planet with \"{T}: Add one mana of any color.\""
  ]

def dominionAssaultForce : CardDef :=
  fromOracle [
    "Dominion Assault Force",
    "{3}{G}",
    "Creature — Jem'Hadar Warrior",
    "4/4",
    "Vigilance",
    "When this creature enters, choose one —",
    "• Exile target card from a graveyard.",
    "• Surveil 1. (Look at the top card of your library. You may put it into your graveyard.)"
  ]

def dominionSupervisor : CardDef :=
  fromOracle [
    "Dominion Supervisor",
    "{2}{G}",
    "Creature — Vorta Doctor",
    "3/1",
    "When this creature enters, put a +1/+1 counter on target creature.",
    "Creatures you control with counters on them have trample."
  ]

def drJosephMBenga : CardDef :=
  fromOracle [
    "Dr. Joseph M'Benga",
    "{2}{G}{G}",
    "Legendary Creature — Human Doctor",
    "3/3",
    "Other creatures you control with counters on them have hexproof.",
    "If you would put one or more counters on a creature you control, put twice that many of each of those kinds of counters on that creature instead."
  ]

def drLeonardBonesMcCoy : CardDef :=
  fromOracle [
    "Dr. Leonard \"Bones\" McCoy",
    "{1}{G}{G}",
    "Legendary Creature — Human Doctor",
    "3/2",
    "Flash",
    "When Dr. McCoy enters, choose one —",
    "• Return target non-Doctor permanent card from your graveyard to your hand.",
    "• Choose up to one other target creature. When it dies this turn, return that card to the battlefield under its owner's control with a +1/+1 counter on it at the beginning of the next end step."
  ]

def finalFrontier : CardDef :=
  fromOracle [
    "Final Frontier",
    "{2}{G}",
    "Sorcery",
    "Search your library for a basic land card or Planet card, put it onto the battlefield tapped, then shuffle.",
    "Beam me up {1}{G} (You may cast this card from your graveyard for {1}{G} if you also return a creature you control to its owner's hand. Then exile this spell.)"
  ]

def firstContact : CardDef :=
  fromOracle [
    "First Contact",
    "{1}{G}",
    "Instant",
    "Mill four cards. You may put a permanent card from among them into your hand. If this spell is the first spell you've cast this game, you gain 2 life. (To mill four cards, put the top four cards of your library into your graveyard.)"
  ]

def genesisDevice : CardDef :=
  fromOracle [
    "Genesis Device",
    "{2}{G}",
    "Legendary Artifact",
    "When Genesis Device enters, search your library for a basic land card or Planet card, put it onto the battlefield tapped, then shuffle.",
    "{3}{G}{G}, {T}, Sacrifice Genesis Device: Sacrifice any number of lands you control, then search your library for up to that many land cards, put them onto the battlefield tapped, then shuffle. Activate only as a sorcery."
  ]

def holoEngineer : CardDef :=
  fromOracle [
    "Holo-Engineer",
    "{2}{G}{G}",
    "Creature — Human Artificer",
    "3/3",
    "When this creature enters, create a 3/3 colorless Illusion artifact creature token.",
    "If one or more tokens would be created under your control, that many 3/3 colorless Illusion artifact creature tokens are created instead."
  ]

def hologramStalker : CardDef :=
  fromOracle [
    "Hologram Stalker",
    "{4}{G}{G}",
    "Creature — Hirogen Warrior",
    "2/2",
    "When this creature enters, return target permanent card from your graveyard to your hand.",
    "Whenever a card leaves your graveyard, create a 3/3 colorless Illusion artifact creature token. This ability triggers only once each turn."
  ]

def imADoctorNotA : CardDef :=
  fromOracle [
    "I'm a Doctor, Not a . . .",
    "{G}",
    "Instant",
    "Put a +1/+1 counter on target creature you control. Untap it. Until end of turn, it gets +1/+1 and becomes a Doctor. (It loses all other creature types.)"
  ]

def jadziaDaxLivingLegacy : CardDef :=
  fromOracle [
    "Jadzia Dax, Living Legacy",
    "{1}{G}",
    "Legendary Creature — Trill Scientist",
    "0/1",
    "At the beginning of your first main phase, put a +1/+1 counter on Jadzia Dax, then add an amount of {G} equal to the number of counters on her.",
    "Transfer Symbiont — {2}{G}, Discard this card: Put two +1/+1 counters on target creature."
  ]

def jakeSiskoWarCorrespondent : CardDef :=
  fromOracle [
    "Jake Sisko, War Correspondent",
    "{1}{G}",
    "Legendary Creature — Human Citizen",
    "2/2",
    "Landfall — Whenever a land you control enters, you gain 1 life. If this is the second time this ability has resolved this turn, investigate. (Create a Clue token. It's an artifact with \"{2}, Sacrifice this token: Draw a card.\")"
  ]

def macoStrikeTeam : CardDef :=
  fromOracle [
    "MACO Strike Team",
    "{G}",
    "Creature — Human Soldier",
    "2/1",
    "Whenever a creature you control becomes the target of a spell or ability an opponent controls, create a tapped 1/1 red Officer creature token."
  ]

def moopsy : CardDef :=
  fromOracle [
    "Moopsy",
    "{G}",
    "Creature — Beast",
    "1/1",
    "Deathtouch",
    "{2}: This creature gains reach until end of turn."
  ]

def mugato : CardDef :=
  fromOracle [
    "Mugato",
    "{3}{G}{G}",
    "Creature — Ape Beast",
    "6/6",
    "Reach, vigilance, deathtouch"
  ]

def neelixMoralSupport : CardDef :=
  fromOracle [
    "Neelix, Moral Support",
    "{1}{G}",
    "Legendary Creature — Talaxian Advisor",
    "1/1",
    "When Neelix enters, create a Food token. (It's an artifact with \"{2}, {T}, Sacrifice this token: You gain 3 life.\")",
    "Whenever you gain life, put a +1/+1 counter on Neelix."
  ]

def photosyntheticPhysician : CardDef :=
  fromOracle [
    "Photosynthetic Physician",
    "{4}{G}",
    "Creature — Plant Doctor",
    "5/5",
    "Reach",
    "{G}, Exile this card from your graveyard: Create a 1/1 red Officer creature token. Activate only as a sorcery."
  ]

def rokTahkBuddingScientist : CardDef :=
  fromOracle [
    "Rok-Tahk, Budding Scientist",
    "{4}{G}{G}",
    "Legendary Creature — Brikar Scientist",
    "5/5",
    "Creatures you control have \"{T}: Add {G}{G}.\"",
    "When Rok-Tahk enters, create Murf, a legendary 0/1 green Ooze Slug creature token with indestructible."
  ]

def saruUnthreatened : CardDef :=
  fromOracle [
    "Saru, Unthreatened",
    "{2}{G}",
    "Legendary Creature — Kelpien Officer",
    "3/2",
    "Flash",
    "When Saru enters, another target creature you control gains hexproof until end of turn. (It can't be the target of spells or abilities your opponents control.)"
  ]

def saurianExplorer : CardDef :=
  fromOracle [
    "Saurian Explorer",
    "{3}{G}",
    "Creature — Dinosaur Scout",
    "4/3",
    "Landfall — Whenever a land you control enters, this creature gets +2/+2 until end of turn.",
    "{6}: Create a tapped Planet land token named New Planet with \"{T}: Add one mana of any color.\" Activate only as a sorcery."
  ]

def species8472 : CardDef :=
  fromOracle [
    "Species 8472",
    "{4}{G}{G}",
    "Creature — Insect Beast",
    "7/5",
    "Strange new worlds — When this creature enters, you gain life equal to the number of differently named lands you control.",
    "This creature can't be blocked by artifact creatures.",
    "This creature can't be the target of abilities from artifact sources your opponents control."
  ]

def stableWormhole : CardDef :=
  fromOracle [
    "Stable Wormhole",
    "{2}{G}",
    "Enchantment",
    "Whenever you attack, create a tapped Planet land token named New Planet with \"{T}: Add one mana of any color.\""
  ]

def supportMission : CardDef :=
  fromOracle [
    "Support Mission",
    "{2}{G}",
    "Enchantment",
    "Whenever a creature you control enters, put a quest counter on this enchantment. Put a +1/+1 counter on that creature. If this enchantment has five or more quest counters on it, instead put two +1/+1 counters on that creature."
  ]

def sylviaTillyJoyOfDiscovery : CardDef :=
  fromOracle [
    "Sylvia Tilly, Joy of Discovery",
    "{2}{G}",
    "Legendary Creature — Human Scientist Artificer",
    "2/2",
    "When Sylvia Tilly enters, surveil 2. (Look at the top two cards of your library, then put any number of them into your graveyard and the rest on top of your library in any order.)",
    "At the beginning of combat on your turn, you may pay {1} and exile a card from your graveyard. When you do, put a +1/+1 counter on target creature."
  ]

def syndicateLiquidators : CardDef :=
  fromOracle [
    "Syndicate Liquidators",
    "{4}{G}",
    "Creature — Orion Pirate",
    "4/4",
    "Trample",
    "Landfall — Whenever a land you control enters, put two +1/+1 counters on target creature you control."
  ]

def temporalConqueror : CardDef :=
  fromOracle [
    "Temporal Conqueror",
    "{2}{G}",
    "Creature — Na'kuhl Warrior",
    "2/3",
    "When this creature enters, mill three cards. Then return a land card from your graveyard to your hand. If you can't, create a Treasure token. (To mill three cards, put the top three cards of your library into your graveyard.)"
  ]

def testOfCourage : CardDef :=
  fromOracle [
    "Test of Courage",
    "{G}",
    "Instant",
    "Choose one —",
    "• Alter the Past — Exile target card from a graveyard. You gain 2 life.",
    "• Obliterate the Transwarp Network — Destroy target artifact or enchantment with mana value 3 or less."
  ]

def ussDiscoveryAtBlackAlert : CardDef :=
  fromOracle [
    "U.S.S. Discovery, at Black Alert",
    "{3}{G}{G}",
    "Legendary Artifact — Spacecraft",
    "Whenever U.S.S. Discovery enters or attacks, discover 5. (Exile cards from the top of your library until you exile a nonland card with mana value 5 or less. Cast it without paying its mana cost or put it into your hand. Put the rest on the bottom in a random order.)",
    "Station",
    "6+ | [5/5] Flying"
  ]

def ussVoyagerLoneWanderer : CardDef :=
  fromOracle [
    "U.S.S. Voyager, Lone Wanderer",
    "{3}{G}",
    "Legendary Artifact — Spacecraft",
    "When U.S.S. Voyager enters, reveal cards from the top of your library until you reveal two land cards. Put those land cards onto the battlefield tapped and the rest on the bottom of your library in a random order.",
    "Station (Tap another creature you control: Put charge counters equal to its power on this Spacecraft. Station only as a sorcery. It's an artifact creature at 8+.)",
    "8+ | [3/3] Flying, vigilance"
  ]

def warpSpeed : CardDef :=
  fromOracle [
    "Warp Speed",
    "{2}{G}",
    "Enchantment",
    "Lands you control enter untapped.",
    "When this enchantment enters, search your library for a basic land card or Planet card, reveal it, put it into your hand, then shuffle.",
    "Strange new worlds — {7}{U}{U}, Sacrifice this enchantment: Draw two cards. This ability costs {X} less to activate, where X is the number of differently named lands you control."
  ]

def xenobotanist : CardDef :=
  fromOracle [
    "Xenobotanist",
    "{1}{G}",
    "Creature — Vulcan Scientist",
    "1/3",
    "{T}: Add one mana of any color."
  ]

def xindiSurveyors : CardDef :=
  fromOracle [
    "Xindi Surveyors",
    "{2}{G}",
    "Creature — Xindi Scientist",
    "3/2",
    "Landfall — Whenever a land you control enters, put a +1/+1 counter on this creature."
  ]

def allGoodThings : CardDef :=
  fromOracle [
    "All Good Things . . .",
    "{3}{G}{U}",
    "Enchantment — Saga",
    "(As this Saga enters and after your draw step, add a lore counter. Sacrifice after IV.)",
    "I, II, III — Draw two cards, then exile a card from your hand.",
    "IV — If all cards exiled with this Saga share a card type, you gain 10 life."
  ]

def borgCube : CardDef :=
  fromOracle [
    "Borg Cube",
    "{5}{W}{B}",
    "Artifact — Spacecraft",
    "Affinity for artifact creatures",
    "Whenever this Spacecraft enters or attacks, assimilate a creature card exiled with it. If you can't, exile up to one target creature. (To assimilate a card, put it onto the battlefield under your control with a +1/+1 counter. It's a Borg artifact creature and loses all other creature types.)",
    "Station",
    "12+ | [6/6] Artifact creatures you control have flying."
  ]

def theCityOnTheEdgeOfForever : CardDef :=
  fromOracle [
    "The City on the Edge of Forever",
    "{3}{W}{B}",
    "Enchantment — Saga",
    "(As this Saga enters and after your draw step, add a lore counter. Sacrifice after III.)",
    "I — All artifacts and creatures phase out. Create a 0/1 white Human creature token with \"Permanents can't phase in.\" (Treat phased-out permanents and anything attached to them as though they don't exist.)",
    "II — You draw two cards and each player loses 2 life.",
    "III — Sacrifice a creature token. If you do, you gain 5 life."
  ]

def clevelandBookerEmpath : CardDef :=
  fromOracle [
    "Cleveland Booker, Empath",
    "{2}{R/G}{R/G}",
    "Legendary Creature — Kwejian Rogue",
    "2/2",
    "Landfall — Whenever a land you control enters, create a 2/2 red and green Worm creature token with \"This token can't block.\"",
    "{8}: Creatures you control get +2/+0 until end of turn."
  ]

def constableOdo : CardDef :=
  fromOracle [
    "Constable Odo",
    "{3}{W/U}{W/U}",
    "Legendary Creature — Shapeshifter Detective",
    "4/3",
    "When Constable Odo enters, choose one —",
    "• Tap target creature an opponent controls. Put two stun counters on it. (If a permanent with a stun counter would become untapped, remove one from it instead.)",
    "• Investigate twice. (To investigate, create a Clue token. It's an artifact with \"{2}, Sacrifice this token: Draw a card.\")"
  ]

def dalRElAugmentOrphan : CardDef :=
  fromOracle [
    "Dal R'El, Augment Orphan",
    "{1}{R}{G}",
    "Legendary Creature — Human Mutant Rogue",
    "3/3",
    "Landfall — Whenever a land you control enters, add {R} or {G}.",
    "{3}, Sacrifice a land: Draw a card."
  ]

def danielsTemporalAgent : CardDef :=
  fromOracle [
    "Daniels, Temporal Agent",
    "{2}{B/G}{B/G}",
    "Legendary Creature — Human Advisor",
    "3/1",
    "When Daniels enters, return target creature card from your graveyard to your hand.",
    "{2}, Put this card from your graveyard on the bottom of your library: You gain 2 life."
  ]

def dathonHisHeartOpen : CardDef :=
  fromOracle [
    "Dathon, His Heart Open",
    "{G}{U}{R}",
    "Legendary Creature — Tamarian Officer",
    "3/3",
    "Whenever you cast an enchantment spell, draw a card. If it's a Saga spell, Dathon deals 2 damage to each opponent.",
    "{2}: Choose a counter on target enchantment you control. Put another counter of that kind on it. Activate only as a sorcery."
  ]

def theDoctorEMH : CardDef :=
  fromOracle [
    "The Doctor, EMH",
    "{3}{G/W}{G/W}",
    "Legendary Artifact Creature — Illusion Doctor",
    "3/3",
    "When The Doctor enters, put a +1/+1 counter on target creature. Then put a +1/+1 counter on each creature you control with a counter on it."
  ]

def theDurasSisters : CardDef :=
  fromOracle [
    "The Duras Sisters",
    "{B/R}{B/R}",
    "Legendary Creature — Klingon Warrior",
    "3/2",
    "When The Duras Sisters die, create a 2/1 red Klingon Warrior creature token with haste."
  ]

def dvanaTendiOptimisticEnsign : CardDef :=
  fromOracle [
    "D'Vana Tendi, Optimistic Ensign",
    "{1}{G/U}{G/U}",
    "Legendary Creature — Orion Scientist",
    "2/4",
    "{T}: Untap another target permanent.",
    "{3}: Surveil 1. (Look at the top card of your library. You may put it into your graveyard.)"
  ]

def gowronEagerForBattle : CardDef :=
  fromOracle [
    "Gowron, Eager for Battle",
    "{2}{B}{R}",
    "Legendary Creature — Klingon Warrior",
    "3/3",
    "Whenever another creature dies, put a +1/+1 counter on Gowron.",
    "Sacrifice another creature: Gowron gains trample until end of turn. If you sacrificed a Klingon this way, you draw a card and lose 1 life."
  ]

def grayAndAdiraForeverJoined : CardDef :=
  fromOracle [
    "Gray and Adira, Forever Joined",
    "{2}{U/R}{U/R}",
    "Legendary Creature — Trill Human Officer",
    "2/3",
    "At the beginning of combat on your turn, if you've cast a noncreature spell this turn, create a token that's a copy of target creature you control, except it isn't legendary. It gains haste until end of turn. Sacrifice it at the beginning of the next end step."
  ]

def hemmerFixingWhatIsBroken : CardDef :=
  fromOracle [
    "Hemmer, Fixing What Is Broken",
    "{W}{U}",
    "Legendary Creature — Aenar Artificer",
    "2/3",
    "During your turn, Spacecraft you control have hexproof. (They can't be the targets of spells or abilities your opponents control.)",
    "Whenever Hemmer becomes tapped, draw a card, then discard a card."
  ]

def hitIt : CardDef :=
  fromOracle [
    "Hit It!",
    "{1}{R}{G}",
    "Enchantment",
    "Creatures you control have haste.",
    "When this enchantment enters, look at the top five cards of your library. Put a land card from among them onto the battlefield tapped and the rest into your graveyard."
  ]

def theInnerLight : CardDef :=
  fromOracle [
    "The Inner Light",
    "{3}{G}{W}",
    "Enchantment — Saga",
    "(As this Saga enters and after your draw step, add a lore counter. Sacrifice after III.)",
    "I — Return target green or white creature card from your graveyard to the battlefield.",
    "II — Choose target creature. Whenever it deals combat damage to a player this turn, you draw that many cards.",
    "III — You gain life equal to the greatest power among creatures you control. Create a Treasure token."
  ]

def kiraNerysFirebrand : CardDef :=
  fromOracle [
    "Kira Nerys, Firebrand",
    "{1}{R}{W}",
    "Legendary Creature — Bajoran Soldier",
    "4/3",
    "Trample",
    "If a creature you control would enter while you control an attacking creature, instead it enters tapped and attacking.",
    "Whenever another creature you control enters, it gets +1/+1 until end of turn."
  ]

def kirkCommandingOfficer : CardDef :=
  fromOracle [
    "Kirk, Commanding Officer",
    "{1}{R}{W}",
    "Legendary Creature — Human Officer",
    "3/3",
    "Whenever you attack while creatures you control have total power 8 or greater, exile the top card of your library. You may play that card this turn.",
    "{2}, Sacrifice Kirk: Destroy target artifact or enchantment."
  ]

def liveLongAndProsper : CardDef :=
  fromOracle [
    "Live Long and Prosper",
    "{5}{W}{U}",
    "Sorcery",
    "This spell can't be countered.",
    "Double your life total. Draw cards equal to the number of cards in your hand. You have no maximum hand size until your next turn."
  ]

def locutusTheOneWhoSpeaks : CardDef :=
  fromOracle [
    "Locutus, the One Who Speaks",
    "{W}{B}",
    "Legendary Artifact Creature — Borg",
    "1/1",
    "Artifact creatures you control get +1/+1.",
    "{W}{B}, Discard this card: It deals 2 damage to target creature. You gain 2 life."
  ]

def lorePositronicProvocateur : CardDef :=
  fromOracle [
    "Lore, Positronic Provocateur",
    "{1}{U/B}{U/B}",
    "Legendary Artifact Creature — Android Rogue",
    "2/3",
    "When Lore enters, choose one —",
    "• Target creature gets +1/+0 until end of turn and can't be blocked this turn.",
    "• Surveil 2. (Look at the top two cards of your library, then put any number of them into your graveyard and the rest on top of your library in any order.)"
  ]

def lrellFierceVisionary : CardDef :=
  fromOracle [
    "L'Rell, Fierce Visionary",
    "{1}{B}{R}",
    "Legendary Creature — Klingon Warrior",
    "1/4",
    "At the beginning of combat on your turn, create a 2/1 red Klingon Warrior creature token with haste. Sacrifice it at the beginning of the next end step.",
    "{2}, Sacrifice another creature or artifact: Surveil 1. (Look at the top card of your library. You may put it into your graveyard.)"
  ]

def mirrorUniverseIntrusion : CardDef :=
  fromOracle [
    "Mirror Universe Intrusion",
    "{1}{U}{B}",
    "Sorcery",
    "Kicker {4}{U}{B} (You may pay an additional {4}{U}{B} as you cast this spell.)",
    "Create a token that's a copy of target creature an opponent controls, except it has menace. If this spell was kicked, instead for each creature target opponent controls, create a token that's a copy of that creature, except it has menace."
  ]

def nogAmbitiousCadet : CardDef :=
  fromOracle [
    "Nog, Ambitious Cadet",
    "{B}{G}",
    "Legendary Creature — Ferengi Rogue",
    "2/2",
    "Menace",
    "{1}: If Nog is a Rogue, he becomes a Ferengi Scout with base power and toughness 3/4 and gains \"Whenever Nog becomes tapped, surveil 2.\"",
    "{3}: If Nog is a Scout, he becomes a Ferengi Officer and gains \"You may play lands from your graveyard\" and \"You may play an additional land on each of your turns.\""
  ]

def phloxUnorthodoxDoctor : CardDef :=
  fromOracle [
    "Phlox, Unorthodox Doctor",
    "{2}{G}{W}",
    "Legendary Creature — Denobulan Doctor",
    "3/4",
    "Trample",
    "Whenever a creature you control with a counter on it deals combat damage to a player, draw a card."
  ]

def sarekFederationAmbassador : CardDef :=
  fromOracle [
    "Sarek, Federation Ambassador",
    "{1}{G}{W}{U}",
    "Legendary Creature — Vulcan Advisor",
    "0/5",
    "Federation — At the beginning of combat on your turn, draw a card for every five creature types among non-Borg creatures you control. If you draw three or more cards this way, put two +1/+1 counters on each creature you control."
  ]

def sevenOfNine : CardDef :=
  fromOracle [
    "Seven of Nine",
    "{2}{U}{B}",
    "Legendary Artifact Creature — Human Scientist",
    "2/4",
    "Whenever you face a dilemma, draw a card. (You face a dilemma as you choose one or more modes for a spell or ability.)"
  ]

def spockAlwaysYourFriend : CardDef :=
  fromOracle [
    "Spock, Always Your Friend",
    "{U}{R}",
    "Legendary Creature — Vulcan Human Scientist",
    "2/2",
    "When Spock enters, look at the top four cards of your library. You may reveal a noncreature, nonland card from among them and put it into your hand. Put the rest on the bottom of your library in any order."
  ]

def theTraveler : CardDef :=
  fromOracle [
    "The Traveler",
    "{G}{U}",
    "Legendary Creature — Scout",
    "*/3",
    "Reach, vigilance",
    "Strange new worlds — The Traveler's power is equal to the number of differently named lands you control."
  ]

def vashFreelanceArchaeologist : CardDef :=
  fromOracle [
    "Vash, Freelance Archaeologist",
    "{1}{B}{G}",
    "Legendary Creature — Human Rogue Scientist",
    "2/4",
    "At the beginning of your upkeep, surveil 1. (Look at the top card of your library. You may put it into your graveyard.)",
    "Whenever a card leaves your graveyard, draw a card. This ability triggers only once each turn."
  ]

def worfHonorBoundWarrior : CardDef :=
  fromOracle [
    "Worf, Honor-Bound Warrior",
    "{R/W}{R/W}",
    "Legendary Creature — Klingon Warrior Officer",
    "1/1",
    "Whenever you attack while creatures you control have total power 8 or greater, double Worf's power until end of turn.",
    "Tap two untapped artifacts and/or creatures you control: Put a +1/+1 counter on Worf. Activate only as a sorcery."
  ]

def yearOfHell : CardDef :=
  fromOracle [
    "Year of Hell",
    "{1}{U}{R}",
    "Enchantment — Saga",
    "(As this Saga enters and after your draw step, add a lore counter. Sacrifice after III.)",
    "I, II, III — Each player draws a card. This Saga deals 2 damage to each player."
  ]

def zeroIncorporealSensate : CardDef :=
  fromOracle [
    "Zero, Incorporeal Sensate",
    "{1}{W/B}{W/B}",
    "Legendary Artifact Creature — Medusan Scientist",
    "2/2",
    "Lifelink",
    "When Zero enters, look at target opponent's hand. You may exile a nonland card from it. For as long as that card remains exiled, its owner may play it. A spell cast this way costs {2} more to cast."
  ]

def classFShuttlecraft : CardDef :=
  fromOracle [
    "Class-F Shuttlecraft",
    "{3}",
    "Artifact — Spacecraft",
    "{T}: Add one mana of any color.",
    "Station (Tap another creature you control: Put charge counters equal to its power on this Spacecraft. Station only as a sorcery. It's an artifact creature at 6+.)",
    "6+ | [2/4] Flying, vigilance"
  ]

def combadge : CardDef :=
  fromOracle [
    "Combadge",
    "{3}",
    "Artifact — Communicator Equipment",
    "When you cast this spell, copy it. (The copy becomes a token.)",
    "Equipped creature has \"Whenever this creature attacks while you control another creature with a Communicator attached to it, this creature can't be blocked this turn.\"",
    "Equip {2} ({2}: Attach to target creature you control. Equip only as a sorcery.)"
  ]

def crystallineEntity : CardDef :=
  fromOracle [
    "Crystalline Entity",
    "{8}",
    "Artifact Creature — Elemental",
    "7/7",
    "Flying",
    "When this creature enters, if you cast it, destroy all nonartifact creatures."
  ]

def cyberneticSpecialist : CardDef :=
  fromOracle [
    "Cybernetic Specialist",
    "{2}",
    "Artifact Creature — Human Scientist",
    "2/1",
    "When this creature enters, surveil 1. (Look at the top card of your library. You may put it into your graveyard.)",
    "{1}, {T}: Put target card from your graveyard on the bottom of your library."
  ]

def deepSpace9 : CardDef :=
  fromOracle [
    "Deep Space 9",
    "{9}",
    "Legendary Artifact — Spacecraft",
    "When Deep Space 9 enters and at the beginning of your upkeep, exile the top four cards of your library. Put all permanent cards exiled this way onto the battlefield.",
    "Station (Tap another creature you control: Put charge counters equal to its power on this Spacecraft. Station only as a sorcery.)",
    "9+ | Creatures you control get +3/+3."
  ]

def engineeredExplosives : CardDef :=
  fromOracle [
    "Engineered Explosives",
    "{X}",
    "Artifact",
    "Sunburst (This artifact enters with a charge counter on it for each color of mana spent to cast it.)",
    "{2}, Sacrifice this artifact: Destroy each nonland permanent with mana value equal to the number of charge counters on this artifact."
  ]

def theHolodeck : CardDef :=
  fromOracle [
    "The Holodeck",
    "{7}",
    "Legendary Artifact",
    "Once during each of your turns, you may play a permanent card you own from outside the game or from your graveyard."
  ]

def isolinearProcessor : CardDef :=
  fromOracle [
    "Isolinear Processor",
    "{2}",
    "Artifact",
    "{T}: Add {C}. Spend this mana only to cast an artifact spell or activate an ability of an artifact source.",
    "{2}, {T}: Draw a card, then discard a card."
  ]

def replicator : CardDef :=
  fromOracle [
    "Replicator",
    "{2}",
    "Artifact",
    "When this artifact enters, create a Food token. (It's an artifact with \"{2}, {T}, Sacrifice this token: You gain 3 life.\")",
    "{2}, {T}: Create a tapped token that's a copy of target token you control."
  ]

def sickbay : CardDef :=
  fromOracle [
    "Sickbay",
    "{5}",
    "Artifact",
    "Whenever a creature you control enters, you gain 1 life.",
    "At the beginning of combat on your turn, put X +1/+1 counters on target creature you control, where X is one plus the amount of life you gained this turn."
  ]

def teaEarlGreyHot : CardDef :=
  fromOracle [
    "Tea, Earl Grey, Hot",
    "{2}",
    "Artifact — Food",
    "When this artifact enters, draw a card.",
    "{2}, {T}, Sacrifice this artifact: Choose one —",
    "• This artifact deals 2 damage to target opponent.",
    "• You gain 3 life."
  ]

def tricorder : CardDef :=
  fromOracle [
    "Tricorder",
    "{1}",
    "Artifact — Equipment",
    "Equipped creature gets +1/+1.",
    "Whenever equipped creature attacks, surveil 1. (Look at the top card of your library. You may put it into your graveyard.)",
    "Equip {1} ({1}: Attach to target creature you control. Equip only as a sorcery.)"
  ]

def type2Phaser : CardDef :=
  fromOracle [
    "Type-2 Phaser",
    "{2}",
    "Artifact — Equipment",
    "When this Equipment enters, tap target creature an opponent controls and put a stun counter on it. (If a permanent with a stun counter would become untapped, remove one from it instead.)",
    "Equipped creature gets +3/+0.",
    "Equip {3} ({3}: Attach to target creature you control. Equip only as a sorcery.)"
  ]

def ussCerritosFollowingUp : CardDef :=
  fromOracle [
    "U.S.S. Cerritos, Following Up",
    "{5}",
    "Legendary Artifact — Spacecraft",
    "When U.S.S. Cerritos enters, create two 1/1 red Officer creature tokens.",
    "Station (Tap another creature you control: Put charge counters equal to its power on this Spacecraft. Station only as a sorcery. It's an artifact creature at 6+.)",
    "6+ | [4/4] Flying"
  ]

def ussEnterpriseDGalaxyClass : CardDef :=
  fromOracle [
    "U.S.S. Enterprise-D, Galaxy-Class",
    "{3}",
    "Legendary Artifact — Spacecraft",
    "Whenever one or more charge counters are put on U.S.S. Enterprise-D for the first time each turn, exile the top card of your library. You may play that card this turn.",
    "Station (Tap another creature you control: Put charge counters equal to its power on this Spacecraft. Station only as a sorcery. It's an artifact creature at 7+.)",
    "7+ | [4/5] Flying, vigilance"
  ]

def warpCore : CardDef :=
  fromOracle [
    "Warp Core",
    "{2}",
    "Artifact",
    "When this artifact enters, you may search your library for a basic land card, reveal it, put it into your hand, then shuffle.",
    "{1}, {T}: Put two charge counters on target Spacecraft. Activate only as a sorcery."
  ]

def andoria : CardDef :=
  fromOracle [
    "Andoria",
    "Land — Planet",
    "This land enters tapped.",
    "When this land enters, you gain 1 life.",
    "{T}: Add {U} or {R}."
  ]

def artificialAnomaly : CardDef :=
  fromOracle [
    "Artificial Anomaly",
    "Land",
    "{T}: Add {C}.",
    "{3}{B}, {T}, Sacrifice this land: Each opponent loses 2 life and you gain 2 life. Create a tapped Planet land token named New Planet with \"{T}: Add one mana of any color.\""
  ]

def bajor : CardDef :=
  fromOracle [
    "Bajor",
    "Land — Planet",
    "This land enters tapped.",
    "When this land enters, you gain 1 life.",
    "{T}: Add {R} or {W}."
  ]

def bloodCrypt : CardDef :=
  fromOracle [
    "Blood Crypt",
    "Land — Swamp Mountain",
    "({T}: Add {B} or {R}.)",
    "As this land enters, you may pay 2 life. If you don't, it enters tapped."
  ]

def breedingPool : CardDef :=
  fromOracle [
    "Breeding Pool",
    "Land — Forest Island",
    "({T}: Add {G} or {U}.)",
    "As this land enters, you may pay 2 life. If you don't, it enters tapped."
  ]

def cardassiaPrime : CardDef :=
  fromOracle [
    "Cardassia Prime",
    "Land — Planet",
    "This land enters tapped.",
    "When this land enters, you gain 1 life.",
    "{T}: Add {W} or {B}."
  ]

def earthSector001 : CardDef :=
  fromOracle [
    "Earth, Sector 001",
    "Land — Planet",
    "This land enters tapped.",
    "When this land enters, you gain 1 life.",
    "{T}: Add {G} or {U}."
  ]

def federationOutpost : CardDef :=
  fromOracle [
    "Federation Outpost",
    "Land",
    "This land enters tapped unless you control two or more other lands.",
    "When this land enters untapped, choose one —",
    "• You gain 2 life.",
    "• Surveil 1.",
    "{T}: Add {W}."
  ]

def ferenginar : CardDef :=
  fromOracle [
    "Ferenginar",
    "Land — Planet",
    "This land enters tapped.",
    "When this land enters, you gain 1 life.",
    "{T}: Add {B} or {G}."
  ]

def gaseousAnomaly : CardDef :=
  fromOracle [
    "Gaseous Anomaly",
    "Land",
    "{T}: Add {C}.",
    "{5}{U}, {T}, Sacrifice this land: Draw two cards. Create a tapped Planet land token named New Planet with \"{T}: Add one mana of any color.\""
  ]

def godlessShrine : CardDef :=
  fromOracle [
    "Godless Shrine",
    "Land — Plains Swamp",
    "({T}: Add {W} or {B}.)",
    "As this land enters, you may pay 2 life. If you don't, it enters tapped."
  ]

def hallowedFountain : CardDef :=
  fromOracle [
    "Hallowed Fountain",
    "Land — Plains Island",
    "({T}: Add {W} or {U}.)",
    "As this land enters, you may pay 2 life. If you don't, it enters tapped."
  ]

def nivarScienceAcademy : CardDef :=
  fromOracle [
    "Ni'Var Science Academy",
    "Land",
    "This land enters tapped unless you control two or more other lands.",
    "When this land enters untapped, choose one —",
    "• Target creature gains flying until end of turn.",
    "• Surveil 1.",
    "{T}: Add {U}."
  ]

def orion : CardDef :=
  fromOracle [
    "Orion",
    "Land — Planet",
    "This land enters tapped.",
    "When this land enters, you gain 1 life.",
    "{T}: Add {R} or {G}."
  ]

def overgrownTomb : CardDef :=
  fromOracle [
    "Overgrown Tomb",
    "Land — Swamp Forest",
    "({T}: Add {B} or {G}.)",
    "As this land enters, you may pay 2 life. If you don't, it enters tapped."
  ]

def qContinuum : CardDef :=
  fromOracle [
    "Q Continuum",
    "Land",
    "This land enters tapped unless you control two or more other lands.",
    "When this land enters untapped, choose one —",
    "• Target creature gets +1/+1 and gains vigilance until end of turn.",
    "• Surveil 1.",
    "{T}: Add {G}."
  ]

def qonos : CardDef :=
  fromOracle [
    "Qo'noS",
    "Land — Planet",
    "This land enters tapped.",
    "When this land enters, you gain 1 life.",
    "{T}: Add {B} or {R}."
  ]

def quarksBar : CardDef :=
  fromOracle [
    "Quark's Bar",
    "Land",
    "This land enters tapped unless you control two or more other lands.",
    "When this land enters untapped, choose one —",
    "• This land deals 1 damage to each opponent.",
    "• Surveil 1.",
    "{T}: Add {R}."
  ]

def risa : CardDef :=
  fromOracle [
    "Risa",
    "Land — Planet",
    "This land enters tapped.",
    "When this land enters, you gain 1 life.",
    "{T}: Add {G} or {W}."
  ]

def romulus : CardDef :=
  fromOracle [
    "Romulus",
    "Land — Planet",
    "This land enters tapped.",
    "When this land enters, you gain 1 life.",
    "{T}: Add {U} or {B}."
  ]

def sacredFoundry : CardDef :=
  fromOracle [
    "Sacred Foundry",
    "Land — Mountain Plains",
    "({T}: Add {R} or {W}.)",
    "As this land enters, you may pay 2 life. If you don't, it enters tapped."
  ]

def spatialAnomaly : CardDef :=
  fromOracle [
    "Spatial Anomaly",
    "Land",
    "{T}: Add {C}.",
    "{4}{R}, {T}, Sacrifice this land: It deals 2 damage to target creature. Create a tapped Planet land token named New Planet with \"{T}: Add one mana of any color.\""
  ]

def starfleetAcademy : CardDef :=
  fromOracle [
    "Starfleet Academy",
    "Legendary Land",
    "{T}: Add {C}.",
    "Federation — {5}, {T}: Choose a color. Add an amount of mana of that color equal to the number of creature types among non-Borg creatures you control."
  ]

def steamVents : CardDef :=
  fromOracle [
    "Steam Vents",
    "Land — Island Mountain",
    "({T}: Add {U} or {R}.)",
    "As this land enters, you may pay 2 life. If you don't, it enters tapped."
  ]

def stompingGround : CardDef :=
  fromOracle [
    "Stomping Ground",
    "Land — Mountain Forest",
    "({T}: Add {R} or {G}.)",
    "As this land enters, you may pay 2 life. If you don't, it enters tapped."
  ]

def subspaceAnomaly : CardDef :=
  fromOracle [
    "Subspace Anomaly",
    "Land",
    "{T}: Add {C}.",
    "{4}{W}, {T}, Sacrifice this land: Create two 1/1 red Officer creature tokens. Create a tapped Planet land token named New Planet with \"{T}: Add one mana of any color.\""
  ]

def templeGarden : CardDef :=
  fromOracle [
    "Temple Garden",
    "Land — Forest Plains",
    "({T}: Add {G} or {W}.)",
    "As this land enters, you may pay 2 life. If you don't, it enters tapped."
  ]

def temporalAnomaly : CardDef :=
  fromOracle [
    "Temporal Anomaly",
    "Land",
    "{T}: Add {C}.",
    "{3}{G}, {T}, Sacrifice this land: Mill four cards. You may put a permanent card from among them into your hand. Create a tapped Planet land token named New Planet with \"{T}: Add one mana of any color.\""
  ]

def unexploredTerritory : CardDef :=
  fromOracle [
    "Unexplored Territory",
    "Land",
    "{T}: Add {C}.",
    "{1}, {T}, Sacrifice this land: Search your library for a basic land card, put it onto the battlefield tapped, then shuffle."
  ]

def theUnicomplex : CardDef :=
  fromOracle [
    "The Unicomplex",
    "Land",
    "This land enters tapped unless you control two or more other lands.",
    "When this land enters untapped, choose one —",
    "• Put target creature card from your graveyard on top of your library.",
    "• Surveil 1.",
    "{T}: Add {B}."
  ]

def vulcan : CardDef :=
  fromOracle [
    "Vulcan",
    "Land — Planet",
    "This land enters tapped.",
    "When this land enters, you gain 1 life.",
    "{T}: Add {W} or {U}."
  ]

def wateryGrave : CardDef :=
  fromOracle [
    "Watery Grave",
    "Land — Island Swamp",
    "({T}: Add {U} or {B}.)",
    "As this land enters, you may pay 2 life. If you don't, it enters tapped."
  ]

def starTrekPlains : CardDef :=
  fromOracle [
    "Plains",
    "Basic Land — Plains",
    "({T}: Add {W}.)"
  ]

def starTrekIsland : CardDef :=
  fromOracle [
    "Island",
    "Basic Land — Island",
    "({T}: Add {U}.)"
  ]

def starTrekSwamp : CardDef :=
  fromOracle [
    "Swamp",
    "Basic Land — Swamp",
    "({T}: Add {B}.)"
  ]

def starTrekMountain : CardDef :=
  fromOracle [
    "Mountain",
    "Basic Land — Mountain",
    "({T}: Add {R}.)"
  ]

def starTrekForest : CardDef :=
  fromOracle [
    "Forest",
    "Basic Land — Forest",
    "({T}: Add {G}.)"
  ]

/-- Every unique card in Magic: The Gathering | Star Trek (TRK). -/
def starTrekCards : Array CardDef := #[
  seventyThousandLightYearsFromHome,
  andromedanAutomatons,
  antagonistIncorporator,
  assemblySpecialist,
  bradBoimlerEagerEnsign,
  captainBenjaminSisko,
  captainJeanLucPicard,
  commandDecision,
  commandSubadjunct,
  conquestMission,
  deannaTroiPsychicCounsel,
  dot7RepairSquad,
  drBeverlyCrusher,
  drMcCoySurlySurgeon,
  emergencyMedicalHologram,
  excalbianGamemaster,
  federationFieldMedic,
  federationResupply,
  freeBorgRevolutionaries,
  ghostOfIllyria,
  hologramJaneway,
  malfunctioningHolodeck,
  theMeasureOfAMan,
  milesOBrienTransporterOps,
  theNeedsOfTheMany,
  oberthClassStarship,
  peaceInOurTime,
  petSehlat,
  picardLeadingByExample,
  primaryUnimatrixAdjunct,
  pureEnergy,
  rutherfordUpgradedEnsign,
  saavikStoicStudent,
  setPhasersTo,
  shieldsUp,
  shuttleAce,
  suluSpaceSwashbuckler,
  tacticalOfficer,
  testOfConviction,
  theresCoffeeInThatNebula,
  troublingTribbles,
  unaChinRileyNumberOne,
  ussEnterpriseAFreeSpirit,
  ussExcelsiorCuttingEdge,
  vexingDrone,
  anthropologicalMission,
  theCaretaker,
  cetaceanOps,
  cloakAndPhaser,
  cloisteredTelepath,
  considerThePrimeDirective,
  dataNewLife,
  deepSpaceScan,
  dominionSaboteur,
  emergencyHolographicCrew,
  energize,
  ensignPavelChekov,
  enterpriseNX01,
  federationProbe,
  guidanceFailure,
  gwyndalaTheProgeny,
  highlyIllogical,
  hmsBountyUnlikelyTimeship,
  hoshiSatoExolinguist,
  humpbackWhales,
  interstellarEffigy,
  jettRenoProblemSolver,
  kobayashiMaruScenario,
  lieutenantCommanderData,
  ltCmdrGeordiLaForge,
  makeItSo,
  marooned,
  melkotianAdjudicator,
  mrSpockScienceOfficer,
  nyotaUhuraCommunications,
  openCommunications,
  romulanBirdOfPrey,
  rulesOfAcquisition,
  scottyMiracleWorker,
  sevenOfNineUnassimilated,
  starfleetSpannerJockey,
  subcommanderTPol,
  suurokClassScienceVessel,
  suusMahnaPractitioner,
  testOfPriorities,
  thoseOldScientists,
  vgerTheIntruder,
  vulcanMindMeld,
  wesleyCrusherStarfleetCadet,
  zeframCochraneWarpPioneer,
  armusSkinOfEvil,
  assaultDrone,
  automatedWarfareSystem,
  batleth,
  battleScarredSurvivalist,
  blastoneuron,
  chadichInvestigator,
  collationTrimatrix,
  collectiveDrone,
  commanderRaffiMusiker,
  dghorBloodletter,
  deathIsIrrelevant,
  theDestructionOfPraxis,
  deEvolve,
  ejectTheWarpCore,
  elimGarakSimpleTailor,
  fugitiveListener,
  gabrielLorcaMirrorMenace,
  generalChangColdWarrior,
  georgiouTerranEmperor,
  aGoodDayToDie,
  grandNagusZek,
  gulDukatColonialPrefect,
  hesDeadJim,
  hiveMindCoprocessor,
  impossibleChoice,
  inThePaleMoonlight,
  kaiWinnFaithlessLeader,
  khanVengefulHeart,
  obsidianOrderOperative,
  organicAvulsionUnit,
  overflowSubmatrix,
  patternBufferPreservation,
  relentlessDrednok,
  resistanceIsFutile,
  rogueArtificialIntelligence,
  saltVampire,
  selaTalShiarParadox,
  storiedVeteran,
  strayFromHistory,
  talShiarOperative,
  tellMeWhatYouSee,
  tenaciousDrone,
  testOfLoyalty,
  ussReliantFromHellsHeart,
  vengeanceMission,
  academyInstructor,
  beckettMarinerImpetuousEnsign,
  boardingAction,
  brazenBluff,
  cantankerousCaptain,
  captainJamesTKirk,
  captainMichaelBurnham,
  captainsTutelage,
  d7BattleCruiser,
  daharMaster,
  dominionInfiltration,
  encounterTheUnknown,
  ericaOrtegasPluckyPilot,
  exploratoryMission,
  genesisEffect,
  horta,
  infiniteDiversity,
  khaaaaaaaaaaaannn,
  khanDespotByDesign,
  laanNoonienSinghSecurity,
  lwaxanaTroiCharmingGuest,
  munitionsEnthusiast,
  theNakedTime,
  pahWraith,
  perilsOfThePast,
  planetaryBombardment,
  planetaryPatrol,
  plasmaCascade,
  qStackingTheDeck,
  quarkHumbleProprietor,
  ravenousCosmozoan,
  recklessImpulse,
  redAlert,
  sarcophagusShipOfTheDead,
  savvyProfiteer,
  silicateSurveyor,
  starfleetSecurity,
  talShiarAnalyst,
  targWrangler,
  tashaYarOutOfTime,
  testOfIdentity,
  transporterMalfunction,
  willRikerFirstInTheField,
  worfIntelligenceContractor,
  theWrathOfKhan,
  adversaryByAlgorithm,
  amokTime,
  astuteTerraformer,
  branchingTimeline,
  captainJonathanArcher,
  captainKathrynJaneway,
  captainPikeFullnessOfTime,
  coldBloodedCrew,
  commonGoal,
  culberAndStametsStarCrossed,
  dathonAndPicardAtElAdrel,
  davidAndCarolMarcusCreators,
  dominionAssaultForce,
  dominionSupervisor,
  drJosephMBenga,
  drLeonardBonesMcCoy,
  finalFrontier,
  firstContact,
  genesisDevice,
  holoEngineer,
  hologramStalker,
  imADoctorNotA,
  jadziaDaxLivingLegacy,
  jakeSiskoWarCorrespondent,
  macoStrikeTeam,
  moopsy,
  mugato,
  neelixMoralSupport,
  photosyntheticPhysician,
  rokTahkBuddingScientist,
  saruUnthreatened,
  saurianExplorer,
  species8472,
  stableWormhole,
  supportMission,
  sylviaTillyJoyOfDiscovery,
  syndicateLiquidators,
  temporalConqueror,
  testOfCourage,
  ussDiscoveryAtBlackAlert,
  ussVoyagerLoneWanderer,
  warpSpeed,
  xenobotanist,
  xindiSurveyors,
  allGoodThings,
  borgCube,
  theCityOnTheEdgeOfForever,
  clevelandBookerEmpath,
  constableOdo,
  dalRElAugmentOrphan,
  danielsTemporalAgent,
  dathonHisHeartOpen,
  theDoctorEMH,
  theDurasSisters,
  dvanaTendiOptimisticEnsign,
  gowronEagerForBattle,
  grayAndAdiraForeverJoined,
  hemmerFixingWhatIsBroken,
  hitIt,
  theInnerLight,
  kiraNerysFirebrand,
  kirkCommandingOfficer,
  liveLongAndProsper,
  locutusTheOneWhoSpeaks,
  lorePositronicProvocateur,
  lrellFierceVisionary,
  mirrorUniverseIntrusion,
  nogAmbitiousCadet,
  phloxUnorthodoxDoctor,
  sarekFederationAmbassador,
  sevenOfNine,
  spockAlwaysYourFriend,
  theTraveler,
  vashFreelanceArchaeologist,
  worfHonorBoundWarrior,
  yearOfHell,
  zeroIncorporealSensate,
  classFShuttlecraft,
  combadge,
  crystallineEntity,
  cyberneticSpecialist,
  deepSpace9,
  engineeredExplosives,
  theHolodeck,
  isolinearProcessor,
  replicator,
  sickbay,
  teaEarlGreyHot,
  tricorder,
  type2Phaser,
  ussCerritosFollowingUp,
  ussEnterpriseDGalaxyClass,
  warpCore,
  andoria,
  artificialAnomaly,
  bajor,
  bloodCrypt,
  breedingPool,
  cardassiaPrime,
  earthSector001,
  federationOutpost,
  ferenginar,
  gaseousAnomaly,
  godlessShrine,
  hallowedFountain,
  nivarScienceAcademy,
  orion,
  overgrownTomb,
  qContinuum,
  qonos,
  quarksBar,
  risa,
  romulus,
  sacredFoundry,
  spatialAnomaly,
  starfleetAcademy,
  steamVents,
  stompingGround,
  subspaceAnomaly,
  templeGarden,
  temporalAnomaly,
  unexploredTerritory,
  theUnicomplex,
  vulcan,
  wateryGrave,
  starTrekPlains,
  starTrekIsland,
  starTrekSwamp,
  starTrekMountain,
  starTrekForest
]

#guard starTrekCards.size == 311
#guard starTrekCards.any (fun c =>
  c.name == "U.S.S. Enterprise-D, Galaxy-Class" && c.hasSimpleKeyword .station && c.hasSubtype .spacecraft)
#guard starTrekCards.any (fun c =>
  c.name == "Federation Resupply" && c.beamMeUpCost?.isSome)
#guard starTrekCards.any (fun c =>
  c.name == "Engineered Explosives" && c.hasSimpleKeyword .sunburst)
#guard starTrekCards.any (fun c =>
  c.name == "Hit It!" && c.modellingError?.isNone)
#guard starTrekCards.any (fun c =>
  c.name == "All Good Things . . ." && c.modellingError?.isNone)

end Mtg.Engine.Catalog
