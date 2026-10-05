import Mtg.Engine.Card
import Mtg.Engine.Catalog

/-!
# Reality Fracture catalog

Oracle characteristics for every card in Magic: The Gathering | Reality Fracture
(FRA). Each card is defined by its printed text, and every rules line is
modeled: no card keeps a line as printed text. Empower Jace, prepare spells,
convoke, and `{2/C}` hybrid mana are modeled.

Source: Scryfall set `fra`.
-/

namespace Mtg.Engine.Catalog

open Mtg.Engine

def emrakulTheExigentDoom : CardDef :=
  fromOracleKeeping [
    "Emrakul, the Exigent Doom",
    "{10}",
    "Legendary Creature — Eldrazi",
    "12/12",
    "When you cast this spell, untap all lands you control.",
    "Flying, trample",
    "Ward—Sacrifice three permanents.",
    "{3}, Exile this card from your hand: Target land gains \"{T}: Add {C}{C}\" until this card is cast from exile. You may cast this card for as long as it remains exiled."
  ]

def academicAscent : CardDef :=
  fromOracleKeeping [
    "Academic Ascent",
    "{1}{W}",
    "Instant",
    "Target creature gets +2/+2 and gains flying until end of turn.",
    "Empower Jace 2. (Put two loyalty counters on a Jace token you control. If you don't control one, first create a blue Jace planeswalker token with \"[−1]: Surveil 1\" and \"[−3]: Draw a card.\")"
  ]

def blossomBlessedAngel : CardDef :=
  fromOracleKeeping [
    "Blossom-Blessed Angel",
    "{3}{W}",
    "Creature — Angel Cleric",
    "2/4",
    "Flying, vigilance",
    "This creature enters prepared. (While it's prepared, you may cast a copy of its spell. Doing so unprepares it.)",
    "//PREP//",
    "Seed Suture",
    "{G/W}",
    "Sorcery",
    "Put a +1/+1 counter on target creature. You gain 1 life."
  ]

def campusCrier : CardDef :=
  fromOracleKeeping [
    "Campus Crier",
    "{1}{W}",
    "Creature — Human Advisor",
    "3/1",
    "{1}, Exile this card from your graveyard: Empower Jace 2. (Put two loyalty counters on a Jace token you control. If you don't control one, first create a blue Jace planeswalker token with \"[−1]: Surveil 1\" and \"[−3]: Draw a card.\")"
  ]

def enlightenedConfidant : CardDef :=
  fromOracleKeeping [
    "Enlightened Confidant",
    "{1}{W}",
    "Creature — Kor Cleric",
    "2/1",
    "Lifelink",
    "At the beginning of your end step, if you gained life this turn, surveil 1. If you put a card with mana value less than or equal to the amount of life you gained this turn into your graveyard this way, put that card into your hand."
  ]

def fateshaperAspirant : CardDef :=
  fromOracleKeeping [
    "Fateshaper Aspirant",
    "{4}{W}",
    "Creature — Rhino Cleric",
    "3/4",
    "When this creature enters, choose one —",
    "• Return target legendary card from your graveyard to your hand.",
    "• Put a +1/+1 counter on target creature. It gains vigilance and indestructible until end of turn. (Damage and effects that say \"destroy\" don't destroy it.)"
  ]

def flickeringHound : CardDef :=
  fromOracleKeeping [
    "Flickering Hound",
    "{3}{W}",
    "Creature — Dog",
    "2/2",
    "Whenever you cast a creature spell, exile up to one other target creature you control, then return that card to the battlefield under its owner's control."
  ]

def generousRevival : CardDef :=
  fromOracleKeeping [
    "Generous Revival",
    "{2}{W}",
    "Sorcery",
    "Return target creature card with mana value 3 or less from your graveyard to the battlefield with an additional +1/+1 counter on it.",
    "Flashback {4}{W} (You may cast this card from your graveyard for its flashback cost. Then exile it.)"
  ]

def germinateRecruits : CardDef :=
  fromOracleKeeping [
    "Germinate Recruits",
    "{2}{W}",
    "Instant",
    "Create X 2/2 colorless Wizard Soldier creature tokens named Cadet, where X is the amount of life you gained this turn."
  ]

def graftSurgeon : CardDef :=
  fromOracleKeeping [
    "Graft Surgeon",
    "{2}{W}",
    "Creature — Human Cleric",
    "2/2",
    "This creature enters with a +1/+1 counter on it.",
    "When this creature dies, put its counters on up to one target creature you control."
  ]

def guidingHydra : CardDef :=
  fromOracleKeeping [
    "Guiding Hydra",
    "{X}{W}",
    "Creature — Hydra Horror",
    "1/0",
    "This creature enters with X +1/+1 counters on it.",
    "At the beginning of combat on your turn, you may remove a +1/+1 counter from this creature. If you do, put a +1/+1 counter on each other creature you control."
  ]

def hexhavenBattalion : CardDef :=
  fromOracleKeeping [
    "Hexhaven Battalion",
    "{4}{W}{W}",
    "Sorcery",
    "Create three 2/2 colorless Wizard Soldier creature tokens named Cadet. Empower Jace 2. (Put two loyalty counters on a Jace token you control. If you don't control one, first create a blue Jace planeswalker token with \"[−1]: Surveil 1\" and \"[−3]: Draw a card.\")",
    "Basic landcycling {2} ({2}, Discard this card: Search your library for a basic land card, reveal it, put it into your hand, then shuffle.)"
  ]

def kindredJudgment : CardDef :=
  fromOracleKeeping [
    "Kindred Judgment",
    "{5}{W}{W}",
    "Sorcery",
    "Choose a creature type. Destroy all creatures that aren't of the chosen type."
  ]

def loyalTutor : CardDef :=
  fromOracleKeeping [
    "Loyal Tutor",
    "{W}",
    "Instant",
    "Search your library for a planeswalker card, reveal it, then shuffle and put that card on top."
  ]

def memoryTrap : CardDef :=
  fromOracleKeeping [
    "Memory Trap",
    "{2}{W}",
    "Enchantment",
    "When this enchantment enters, exile target nonland permanent an opponent controls until this enchantment leaves the battlefield."
  ]

def predictivePreparations : CardDef :=
  fromOracleKeeping [
    "Predictive Preparations",
    "{1}{W}",
    "Sorcery",
    "Put a +1/+1 counter on each of one or two target creatures.",
    "Flashback {3}{W} (You may cast this card from your graveyard for its flashback cost. Then exile it.)"
  ]

def prophesiedEnd : CardDef :=
  fromOracleKeeping [
    "Prophesied End",
    "{1}{W}",
    "Instant",
    "Destroy target creature. If it wasn't attacking, its controller draws a card."
  ]

def refuteDestiny : CardDef :=
  fromOracleKeeping [
    "Refute Destiny",
    "{1}{W}",
    "Sorcery",
    "Exile target creature or planeswalker that's green or blue. Surveil 1. (Look at the top card of your library. You may put it into your graveyard.)"
  ]

def repurposedEnforcer : CardDef :=
  fromOracleKeeping [
    "Repurposed Enforcer",
    "{1}{W}",
    "Creature — Human Soldier",
    "3/2",
    "Whenever this creature attacks, empower Jace X, where X is the number of creatures you control. (Put that many loyalty counters on a Jace token you control. If you don't control one, first create a blue Jace planeswalker token with \"[−1]: Surveil 1\" and \"[−3]: Draw a card.\")"
  ]

def returnToTheLightRealms : CardDef :=
  fromOracleKeeping [
    "Return to the Light Realms",
    "{7}{W}{W}",
    "Sorcery",
    "Return all nonland permanent cards from your graveyard to the battlefield."
  ]

def shatterwingPegasus : CardDef :=
  fromOracleKeeping [
    "Shatterwing Pegasus",
    "{2}{W}",
    "Creature — Pegasus",
    "2/3",
    "Flying",
    "{4}{W}: Creatures you control get +1/+1 until end of turn."
  ]

def surgicalPrecision : CardDef :=
  fromOracleKeeping [
    "Surgical Precision",
    "{1}{W}",
    "Sorcery",
    "Choose one —",
    "• Destroy target creature with toughness 4 or greater. You gain 1 life.",
    "• You draw a card and gain 2 life."
  ]

def unflinchingHortimancer : CardDef :=
  fromOracleKeeping [
    "Unflinching Hortimancer",
    "{1}{W}",
    "Creature — Human Cleric",
    "2/1",
    "Ward {1} (Whenever this creature becomes the target of a spell or ability an opponent controls, counter it unless that player pays {1}.)",
    "Whenever you gain life, put a +1/+1 counter on this creature."
  ]

def yourFateEndsHere : CardDef :=
  fromOracleKeeping [
    "Your Fate Ends Here",
    "{2}{W}",
    "Instant",
    "Destroy target creature or planeswalker with mana value 3 or greater. Surveil 1. (Look at the top card of your library. You may put it into your graveyard.)"
  ]

def countersculpt : CardDef :=
  fromOracleKeeping [
    "Countersculpt",
    "{U}{U}",
    "Instant",
    "As an additional cost to cast this spell, behold a Jace or pay {1}. (To behold a Jace, choose a Jace you control or reveal a Jace card from your hand.)",
    "Counter target spell. Empower Jace 1. (Put a loyalty counter on a Jace token you control. If you don't control one, first create a blue Jace planeswalker token with \"[−1]: Surveil 1\" and \"[−3]: Draw a card.\")"
  ]

def cruelCalculations : CardDef :=
  fromOracleKeeping [
    "Cruel Calculations",
    "{2}{U}",
    "Sorcery",
    "Draw X cards, where X is the number of cards that were put into target player's graveyard from their library this turn."
  ]

def cryotheoryAdept : CardDef :=
  fromOracleKeeping [
    "Cryotheory Adept",
    "{1}{U}",
    "Creature — Human Wizard",
    "2/1",
    "Prowess (Whenever you cast a noncreature spell, this creature gets +1/+1 until end of turn.)",
    "{3}{U}, Exile this card from your graveyard: Tap target creature and put a stun counter on it. Activate only as a sorcery. (If a permanent with a stun counter would become untapped, remove one from it instead.)"
  ]

def divinerOfVictory : CardDef :=
  fromOracleKeeping [
    "Diviner of Victory",
    "{U}",
    "Creature — Dwarf Wizard",
    "1/1",
    "This creature enters prepared. (While it's prepared, you may cast a copy of its spell. Doing so unprepares it.)",
    "Whenever you scry or surveil, this creature gets +1/+1 until end of turn.",
    "//PREP//",
    "Unwind History",
    "{1}{U}",
    "Sorcery",
    "Return target creature an opponent controls with mana value 3 or less to its owner's hand. Surveil 1."
  ]

def diviningDuelist : CardDef :=
  fromOracleKeeping [
    "Divining Duelist",
    "{2}{U}",
    "Creature — Merfolk Wizard",
    "3/2",
    "Flash",
    "When this creature enters, choose one —",
    "• Tap target creature.",
    "• Untap target creature.",
    "• Draw a card, then discard a card."
  ]

def icyReception : CardDef :=
  fromOracleKeeping [
    "Icy Reception",
    "{1}{U}",
    "Instant",
    "Choose one —",
    "• Counter target creature or legendary spell unless its controller pays {3}.",
    "• Target creature gets -5/-0 until end of turn."
  ]

def infiniteCoursework : CardDef :=
  fromOracleKeeping [
    "Infinite Coursework",
    "{2}{U}",
    "Enchantment — Aura",
    "Enchant creature",
    "When this Aura enters, tap enchanted creature. It becomes unprepared.",
    "Enchanted creature loses all abilities and doesn't untap during its controller's untap step."
  ]

def jacesMachinations : CardDef :=
  fromOracleKeeping [
    "Jace's Machinations",
    "{2}{U}",
    "Instant",
    "Until end of turn, you may activate loyalty abilities of Jace planeswalkers you control on any player's turn any time you could cast an instant.",
    "Empower Jace 8. (Put eight loyalty counters on a Jace token you control. If you don't control one, first create a blue Jace planeswalker token with \"[−1]: Surveil 1\" and \"[−3]: Draw a card.\")"
  ]

def mindseekerOculus : CardDef :=
  fromOracleKeeping [
    "Mindseeker Oculus",
    "{2}{U}",
    "Creature — Homunculus",
    "2/1",
    "When this creature enters, empower Jace 4. (Put four loyalty counters on a Jace token you control. If you don't control one, first create a blue Jace planeswalker token with \"[−1]: Surveil 1\" and \"[−3]: Draw a card.\")"
  ]

def perfectedTheory : CardDef :=
  fromOracleKeeping [
    "Perfected Theory",
    "{U}",
    "Instant",
    "Choose one —",
    "• Target creature has base power and toughness 1/1 until end of turn.",
    "• Target creature has base power and toughness 4/5 until end of turn."
  ]

def planForAllOutcomes : CardDef :=
  fromOracleKeeping [
    "Plan for All Outcomes",
    "{3}{U}",
    "Enchantment",
    "When this enchantment enters, the owner of up to one other target nonland permanent puts it on their choice of the top or bottom of their library.",
    "Whenever you cast your first noncreature spell each turn, empower Jace 1. (Put a loyalty counter on a Jace token you control. If you don't control one, first create a blue Jace planeswalker token with \"[−1]: Surveil 1\" and \"[−3]: Draw a card.\")"
  ]

def preciseRedaction : CardDef :=
  fromOracleKeeping [
    "Precise Redaction",
    "{1}{U}",
    "Instant",
    "Counter target white or black spell."
  ]

def protegesAwakening : CardDef :=
  fromOracleKeeping [
    "Protege's Awakening",
    "{3}{U}",
    "Sorcery",
    "Empower Jace 6. (Put six loyalty counters on a Jace token you control. If you don't control one, first create a blue Jace planeswalker token with \"[−1]: Surveil 1\" and \"[−3]: Draw a card.\")",
    "Draw a card."
  ]

def seasonedCryomancer : CardDef :=
  fromOracleKeeping [
    "Seasoned Cryomancer",
    "{1}{U}{U}",
    "Creature — Human Wizard",
    "2/2",
    "When this creature enters, draw two cards, then discard two cards. When you discard one or more nonland cards this way, tap up to that many target creatures and put a stun counter on each of them.",
    "{3}{U}{U}, Exile this card from your graveyard: Draw two cards."
  ]

def semesterForeseer : CardDef :=
  fromOracleKeeping [
    "Semester Foreseer",
    "{3}{U}",
    "Creature — Human Wizard",
    "3/4",
    "This creature enters prepared. (While it's prepared, you may cast a copy of its spell. Doing so unprepares it.)",
    "When this creature enters, surveil 1.",
    "//PREP//",
    "Peer Review",
    "{2}{W/U}",
    "Sorcery",
    "Create a 2/2 colorless Wizard Soldier creature token named Cadet. Surveil 1."
  ]

def sphinxOfFalseConclusions : CardDef :=
  fromOracleKeeping [
    "Sphinx of False Conclusions",
    "{2}{U}{U}",
    "Creature — Sphinx Illusion",
    "4/2",
    "Flash",
    "Flying",
    "Whenever this creature attacks, draw a card, then discard a card.",
    "When this creature dies, if it isn't a token, create a token that's a copy of it."
  ]

def sphinxsApproach : CardDef :=
  fromOracleKeeping [
    "Sphinx's Approach",
    "{1}{U}{U}",
    "Instant",
    "Draw two cards. Then you may exile this spell and four cards named Sphinx's Approach from your graveyard. If you do, search your library for a Sphinx creature card, put it onto the battlefield, then shuffle.",
    "A deck can have any number of cards named Sphinx's Approach."
  ]

def surveillancePhantasm : CardDef :=
  fromOracleKeeping [
    "Surveillance Phantasm",
    "{1}{U}",
    "Creature — Bird Illusion",
    "2/3",
    "Defender, flying, vigilance",
    "As long as you've scried or surveilled this turn, this creature can attack as though it didn't have defender.",
    "{3}{U}: Surveil 1. (Look at the top card of your library. You may put it into your graveyard.)"
  ]

def theTheoristJaceBeleren : CardDef :=
  fromOracleKeeping [
    "The Theorist, Jace Beleren",
    "{2}{U}{U}",
    "Legendary Planeswalker — Jace",
    "At the beginning of each opponent's draw step, you draw a card.",
    "+1: Create a 1/1 blue Illusion creature token.",
    "−2: For each opponent, return up to one target artifact or creature that player controls to its owner's hand.",
    "−6: Draw three cards. Then put X +1/+1 counters on each creature you control, where X is the number of cards in your hand.",
    "Loyalty: 3"
  ]

def theoristsProxy : CardDef :=
  fromOracleKeeping [
    "Theorist's Proxy",
    "{1}{U}",
    "Creature — Illusion",
    "0/3",
    "Flash",
    "When this creature enters, empower Jace 3. (Put three loyalty counters on a Jace token you control. If you don't control one, first create a blue Jace planeswalker token with \"[−1]: Surveil 1\" and \"[−3]: Draw a card.\")",
    "{U}, Sacrifice this creature: The next spell you cast this turn can't be countered."
  ]

def undulatingWitness : CardDef :=
  fromOracleKeeping [
    "Undulating Witness",
    "{4}{U}",
    "Creature — Serpent",
    "3/5",
    "Flying",
    "{2}: This creature gets +1/-1 until end of turn.",
    "Basic landcycling {2} ({2}, Discard this card: Search your library for a basic land card, reveal it, put it into your hand, then shuffle.)"
  ]

def unsummon : CardDef :=
  fromOracleKeeping [
    "Unsummon",
    "{U}",
    "Instant",
    "Return target creature to its owner's hand."
  ]

def variableChaser : CardDef :=
  fromOracleKeeping [
    "Variable Chaser",
    "{2}{U}",
    "Creature — Human Wizard",
    "2/3",
    "Flying, prowess",
    "This creature enters prepared. (While it's prepared, you may cast a copy of its spell. Doing so unprepares it.)",
    "//PREP//",
    "Arc of Fortune",
    "{2}{U}",
    "Sorcery",
    "Each player may discard their hand and draw seven cards."
  ]

def apexWitchstalker : CardDef :=
  fromOracleKeeping [
    "Apex Witchstalker",
    "{4}{B}{B}",
    "Creature — Wolf",
    "6/4",
    "Menace (This creature can't be blocked except by two or more creatures.)",
    "When this creature enters or dies, you gain 2 life.",
    "Basic landcycling {2} ({2}, Discard this card: Search your library for a basic land card, reveal it, put it into your hand, then shuffle.)"
  ]

def bloodlineRecollector : CardDef :=
  fromOracleKeeping [
    "Bloodline Recollector",
    "{1}{B}",
    "Creature — Vampire Warlock",
    "2/2",
    "At the beginning of each end step, if three or more creatures died this turn, this creature becomes prepared. (While it's prepared, you may cast a copy of its spell. Doing so unprepares it.)",
    "//PREP//",
    "Ancestral Craving",
    "{B}",
    "Instant",
    "Target player draws three cards and loses 3 life."
  ]

def breakUnderPressure : CardDef :=
  fromOracleKeeping [
    "Break Under Pressure",
    "{2}{B}",
    "Instant",
    "Target opponent sacrifices a creature or planeswalker with the greatest mana value among creatures and planeswalkers they control. You gain 2 life."
  ]

def castAwayDoubt : CardDef :=
  fromOracleKeeping [
    "Cast Away Doubt",
    "{2}{B}",
    "Sorcery",
    "Draw two cards. Cast Away Doubt deals 2 damage to each player."
  ]

def darkMatterManipulator : CardDef :=
  fromOracleKeeping [
    "Dark Matter Manipulator",
    "{B}",
    "Creature — Human Warlock",
    "1/2",
    "When this creature enters, mill three cards.",
    "This creature gets +2/+0 for every seven cards in your graveyard."
  ]

def darklightPhoenix : CardDef :=
  fromOracleKeeping [
    "Darklight Phoenix",
    "{3}{B}",
    "Creature — Phoenix",
    "3/2",
    "Flying, haste",
    "At the beginning of combat on your turn, if two or more creatures died this turn, return this card from your graveyard to the battlefield."
  ]

def extendedAbsence : CardDef :=
  fromOracleKeeping [
    "Extended Absence",
    "{3}{B}",
    "Instant",
    "Exile target creature or planeswalker. Extended Absence deals 1 damage to each opponent and you gain 1 life."
  ]

def extrapolateTheImpossible : CardDef :=
  fromOracleKeeping [
    "Extrapolate the Impossible",
    "{1}{B}",
    "Sorcery",
    "You may reveal exactly two cards you own with different names from outside the game. An opponent chooses one of them. You put that card into your hand."
  ]

def lastGasp : CardDef :=
  fromOracleKeeping [
    "Last Gasp",
    "{1}{B}",
    "Instant",
    "Target creature gets -3/-3 until end of turn."
  ]

def lichsRelic : CardDef :=
  fromOracleKeeping [
    "Lich's Relic",
    "{B}",
    "Artifact — Equipment",
    "When this Equipment enters, you may pay {2}. When you do, for each opponent, destroy up to one target creature or planeswalker that player controls.",
    "Equipped creature gets +2/+1.",
    "Equip {2}"
  ]

def multiplyByZero : CardDef :=
  fromOracleKeeping [
    "Multiply by Zero",
    "{1}{B}",
    "Instant",
    "Target creature has base power and toughness 0/0 until end of turn."
  ]

def overwriteTheMultiverse : CardDef :=
  fromOracleKeeping [
    "Overwrite the Multiverse",
    "{4}{B}{B}",
    "Sorcery",
    "Exile all creatures. Empower Jace X, where X is the number of creatures exiled this way. (Put that many loyalty counters on a Jace token you control. If you don't control one, first create a blue Jace planeswalker token with \"[−1]: Surveil 1\" and \"[−3]: Draw a card.\")"
  ]

def rampartHunter : CardDef :=
  fromOracleKeeping [
    "Rampart Hunter",
    "{3}{B}",
    "Creature — Horror",
    "3/3",
    "Deathtouch",
    "When this creature enters, target creature gets +2/+2 and gains deathtouch until end of turn."
  ]

def rankRat : CardDef :=
  fromOracleKeeping [
    "Rank Rat",
    "{1}{B}",
    "Creature — Zombie Rat",
    "1/1",
    "When this creature enters, each opponent discards a card."
  ]

def rewriteRegrets : CardDef :=
  fromOracleKeeping [
    "Rewrite Regrets",
    "{3}{B}",
    "Sorcery",
    "Return target creature or planeswalker card with mana value 6 or less from your graveyard to the battlefield.",
    "Empower Jace 2. (Put two loyalty counters on a Jace token you control. If you don't control one, first create a blue Jace planeswalker token with \"[−1]: Surveil 1\" and \"[−3]: Draw a card.\")"
  ]

def riseOfTheDeathbringer : CardDef :=
  fromOracleKeeping [
    "Rise of the Deathbringer",
    "{4}{B}",
    "Instant",
    "Choose one —",
    "• Draw cards equal to the greatest power among creatures you control. You lose life equal to the number of cards drawn this way.",
    "• All creatures get -3/-3 until end of turn."
  ]

def sanctumLurker : CardDef :=
  fromOracleKeeping [
    "Sanctum Lurker",
    "{2}{B}",
    "Creature — Horror",
    "3/2",
    "When this creature enters, empower Jace 1.",
    "Planeswalkers you control aren't put into their owners' graveyards for having 0 loyalty.",
    "Planeswalkers you control have \"[+2]: This planeswalker deals 1 damage to each opponent and you gain 1 life.\""
  ]

def screechingSoulbreaker : CardDef :=
  fromOracleKeeping [
    "Screeching Soulbreaker",
    "{2}{B}",
    "Creature — Siren Bard",
    "1/4",
    "Flying",
    "Whenever this creature attacks, it deals 1 damage to each opponent and you gain 1 life."
  ]

def silenceTheEcho : CardDef :=
  fromOracleKeeping [
    "Silence the Echo",
    "{1}{B}",
    "Sorcery",
    "As an additional cost to cast this spell, sacrifice a creature or planeswalker or pay {3}.",
    "Destroy target creature or planeswalker."
  ]

def solveForDisappointment : CardDef :=
  fromOracleKeeping [
    "Solve for Disappointment",
    "{1}{B}",
    "Sorcery",
    "Target opponent reveals their hand. You choose a nonland permanent card from it. That player discards that card.",
    "Empower Jace 1. (Put a loyalty counter on a Jace token you control. If you don't control one, first create a blue Jace planeswalker token with \"[−1]: Surveil 1\" and \"[−3]: Draw a card.\")"
  ]

def terminalCriticism : CardDef :=
  fromOracleKeeping [
    "Terminal Criticism",
    "{1}{B}",
    "Instant",
    "Destroy target creature or planeswalker that's blue or red. You gain 1 life."
  ]

def theoreticalNecromancer : CardDef :=
  fromOracleKeeping [
    "Theoretical Necromancer",
    "{2}{B}",
    "Creature — Vampire Warlock",
    "4/1",
    "{3}{B}, Exile this card from your graveyard: Return another target creature card from your graveyard to your hand."
  ]

def voidExtrapolator : CardDef :=
  fromOracleKeeping [
    "Void Extrapolator",
    "{1}{B}",
    "Creature — Aetherborn Warlock",
    "2/2",
    "This creature enters prepared. (While it's prepared, you may cast a copy of its spell. Doing so unprepares it.)",
    "Threshold — This creature gets +1/+1 as long as there are seven or more cards in your graveyard.",
    "//PREP//",
    "Omit Variables",
    "{U/B}",
    "Sorcery",
    "Mill three cards. (Put the top three cards of your library into your graveyard.)"
  ]

def vraskasFinalMercy : CardDef :=
  fromOracleKeeping [
    "Vraska's Final Mercy",
    "{B}{B}",
    "Sorcery",
    "Choose one —",
    "• You lose 2 life. Destroy target creature or planeswalker.",
    "• You lose 2 life. Empower Jace 6. (Put six loyalty counters on a Jace token you control. If you don't control one, first create a blue Jace planeswalker token with \"[−1]: Surveil 1\" and \"[−3]: Draw a card.\")"
  ]

def ajanisAnguish : CardDef :=
  fromOracleKeeping [
    "Ajani's Anguish",
    "{X}{R}",
    "Enchantment",
    "When this enchantment enters, it deals X damage to any target.",
    "Creatures you control have trample."
  ]

def artifistAcumen : CardDef :=
  fromOracleKeeping [
    "Artifist Acumen",
    "{R}",
    "Sorcery",
    "Creatures you control gain first strike until end of turn.",
    "Draw a card."
  ]

def awakenTheInferno : CardDef :=
  fromOracleKeeping [
    "Awaken the Inferno",
    "{4}{R}",
    "Sorcery",
    "Awaken the Inferno deals 6 damage to target creature or planeswalker an opponent controls. Put a +1/+1 counter on up to one target creature you control.",
    "Basic landcycling {2} ({2}, Discard this card: Search your library for a basic land card, reveal it, put it into your hand, then shuffle.)"
  ]

def realityFractureBlazingCrescendo : CardDef :=
  fromOracleKeeping [
    "Blazing Crescendo",
    "{1}{R}",
    "Instant",
    "Target creature gets +3/+1 until end of turn.",
    "Exile the top card of your library. Until the end of your next turn, you may play that card."
  ]

def chandrasEmberling : CardDef :=
  fromOracleKeeping [
    "Chandra's Emberling",
    "{2}{R}",
    "Creature — Gremlin Elemental",
    "2/2",
    "Haste",
    "Whenever you cast a noncreature spell, put a +1/+1 counter on this creature."
  ]

def commandTheStage : CardDef :=
  fromOracleKeeping [
    "Command the Stage",
    "{2}{R}",
    "Sorcery",
    "Create a 2/2 colorless Wizard Soldier creature token named Cadet, then put a +1/+1 counter on each other Wizard token you control.",
    "At the beginning of each upkeep, if an opponent was dealt noncombat damage last turn, return this card from your graveyard to your hand."
  ]

def craterclawColossus : CardDef :=
  fromOracleKeeping [
    "Craterclaw Colossus",
    "{4}{R}{R}{R}",
    "Artifact Creature — Beast Construct",
    "5/5",
    "Haste",
    "When this creature enters, creatures you control gain trample and get +X/+0 until end of turn, where X is the number of artifacts you control."
  ]

def curseMarredDemon : CardDef :=
  fromOracleKeeping [
    "Curse-Marred Demon",
    "{2}{R}{R}",
    "Creature — Demon",
    "4/4",
    "Flying, trample",
    "When this creature enters, search your library for a card, put it into your hand, shuffle, then discard a card at random."
  ]

def draconicVisitor : CardDef :=
  fromOracleKeeping [
    "Draconic Visitor",
    "{3}{R}{R}",
    "Creature — Dragon",
    "5/5",
    "Flying",
    "If one or more artifact tokens would be created under your control, that many 5/5 red Dragon creature tokens with flying are created instead."
  ]

def eardrumRattler : CardDef :=
  fromOracleKeeping [
    "Eardrum Rattler",
    "{1}{R}",
    "Creature — Human Bard",
    "2/2",
    "{1}, {T}: Another target creature you control with power 2 or less can't be blocked this turn."
  ]

def essenceBurn : CardDef :=
  fromOracleKeeping [
    "Essence Burn",
    "{1}{R}",
    "Instant",
    "Essence Burn deals 5 damage to target black or green creature or planeswalker. If that permanent would die this turn, exile it instead."
  ]

def faceYourself : CardDef :=
  fromOracleKeeping [
    "Face Yourself",
    "{5}{R}{R}",
    "Sorcery",
    "For each creature target player controls, create a token that's a copy of that creature, except it has haste and \"At the beginning of the end step, if you don't control a planeswalker, sacrifice this creature.\""
  ]

def fulminousForte : CardDef :=
  fromOracleKeeping [
    "Fulminous Forte",
    "{2}{R}",
    "Instant",
    "Choose one —",
    "• Fulminous Forte deals 1 damage to each creature and planeswalker your opponents control.",
    "• Fulminous Forte deals 5 damage to target creature or planeswalker."
  ]

def hallwayHeckler : CardDef :=
  fromOracleKeeping [
    "Hallway Heckler",
    "{2}{R}",
    "Creature — Elemental Sorcerer",
    "2/3",
    "This creature enters prepared. (While it's prepared, you may cast a copy of its spell. Doing so unprepares it.)",
    "{T}, Discard a card: Draw a card.",
    "//PREP//",
    "Vicious Verse",
    "{B/R}",
    "Sorcery",
    "Vicious Verse deals 1 damage to target opponent."
  ]

def heartstringPuller : CardDef :=
  fromOracleKeeping [
    "Heartstring Puller",
    "{3}{R}",
    "Creature — Elf Sorcerer",
    "3/1",
    "Trample",
    "When this creature enters, create a 2/2 colorless Wizard Soldier creature token named Cadet."
  ]

def identityEcho : CardDef :=
  fromOracleKeeping [
    "Identity Echo",
    "{2}{R}",
    "Enchantment",
    "{3}{R}: Exile target creature or planeswalker you control. Reveal cards from the top of your library until you reveal a creature or planeswalker card. Put that card onto the battlefield and the rest on the bottom of your library in a random order. Activate only as a sorcery."
  ]

def masterOfBarbs : CardDef :=
  fromOracleKeeping [
    "Master of Barbs",
    "{1}{R}",
    "Creature — Lizard Bard",
    "2/1",
    "Menace",
    "Whenever one or more opponents are dealt noncombat damage, creatures you control get +1/+0 until end of turn."
  ]

def noAdmittance : CardDef :=
  fromOracleKeeping [
    "No Admittance",
    "{1}{R}",
    "Sorcery",
    "No Admittance deals 3 damage to any target.",
    "Empower Jace 1. (Put a loyalty counter on a Jace token you control. If you don't control one, first create a blue Jace planeswalker token with \"[−1]: Surveil 1\" and \"[−3]: Draw a card.\")"
  ]

def pompousBattlemage : CardDef :=
  fromOracleKeeping [
    "Pompous Battlemage",
    "{R}",
    "Creature — Goblin Sorcerer",
    "1/1",
    "Prowess",
    "This creature enters prepared. (While it's prepared, you may cast a copy of its spell. Doing so unprepares it.)",
    "//PREP//",
    "Improvised Act",
    "{R}",
    "Sorcery",
    "You may discard a card. If you do, draw a card."
  ]

def pyreRhymer : CardDef :=
  fromOracleKeeping [
    "Pyre Rhymer",
    "{1}{R}{R}",
    "Creature — Elemental Sorcerer",
    "3/3",
    "Prowess",
    "This creature enters prepared. (While it's prepared, you may cast a copy of its spell. Doing so unprepares it.)",
    "//PREP//",
    "Molten Tide",
    "{R}",
    "Instant",
    "Until end of turn, whenever you tap a Mountain for mana, add an additional {R}."
  ]

def skilledBattlecarver : CardDef :=
  fromOracleKeeping [
    "Skilled Battlecarver",
    "{1}{R}",
    "Creature — Human Warrior",
    "2/1",
    "During your turn, this creature has first strike.",
    "{1}{R}: This creature gets +1/+0 until end of turn."
  ]

def stingcasterMage : CardDef :=
  fromOracleKeeping [
    "Stingcaster Mage",
    "{1}{R}",
    "Creature — Human Wizard",
    "2/1",
    "Haste",
    "When this creature enters, target instant or sorcery card in your graveyard gains flashback until end of turn. The flashback cost is equal to its mana cost. (You may cast that card from your graveyard for its flashback cost. Then exile it.)"
  ]

def tetherTechnician : CardDef :=
  fromOracleKeeping [
    "Tether Technician",
    "{4}{R}",
    "Creature — Minotaur Artificer",
    "4/5",
    "Reach",
    "When this creature enters, you may discard a card. When you do, this creature deals 2 damage to any target."
  ]

def violentEchoes : CardDef :=
  fromOracleKeeping [
    "Violent Echoes",
    "{2}{R}{R}",
    "Instant",
    "Violent Echoes deals 6 damage to target creature or planeswalker. If excess damage was dealt to that permanent this way, empower Jace X, where X is that excess damage. (Put that many loyalty counters on a Jace token you control. If you don't control one, first create a blue Jace planeswalker token with \"[−1]: Surveil 1\" and \"[−3]: Draw a card.\")"
  ]

def wrathOfTheBloodmane : CardDef :=
  fromOracleKeeping [
    "Wrath of the Bloodmane",
    "{2}{R}",
    "Instant",
    "This spell costs {1} less to cast if you control a legendary creature.",
    "Wrath of the Bloodmane deals 4 damage to target creature or planeswalker."
  ]

def arcaneAmphisbaena : CardDef :=
  fromOracleKeeping [
    "Arcane Amphisbaena",
    "{1}{G}",
    "Creature — Snake",
    "1/1",
    "Deathtouch",
    "When this creature enters, empower Jace 2. (Put two loyalty counters on a Jace token you control. If you don't control one, first create a blue Jace planeswalker token with \"[−1]: Surveil 1\" and \"[−3]: Draw a card.\")"
  ]

def bestialIncursion : CardDef :=
  fromOracleKeeping [
    "Bestial Incursion",
    "{3}{G}",
    "Sorcery",
    "Create a 4/4 green Beast creature token with trample.",
    "Flashback {5}{G} (You may cast this card from your graveyard for its flashback cost. Then exile it.)"
  ]

def buddingInsurgent : CardDef :=
  fromOracleKeeping [
    "Budding Insurgent",
    "{2}{G}",
    "Creature — Dryad Scout",
    "3/3",
    "Vigilance",
    "Sacrifice this creature: Destroy target artifact or enchantment. If that permanent was a legendary enchantment, draw a card. Activate only as a sorcery."
  ]

def carnivorousCultivator : CardDef :=
  fromOracleKeeping [
    "Carnivorous Cultivator",
    "{1}{G}",
    "Creature — Elf Warlock",
    "2/3",
    "Deathtouch",
    "This creature enters prepared.",
    "Whenever this creature deals combat damage to a player, return target land card from your graveyard to your hand.",
    "//PREP//",
    "Enroot",
    "{G}",
    "Sorcery",
    "Search your library for a land card, put it into your graveyard, then shuffle."
  ]

def compelBrutality : CardDef :=
  fromOracleKeeping [
    "Compel Brutality",
    "{1}{G}",
    "Instant",
    "Choose one —",
    "• Target creature you control deals damage equal to its power to target creature or planeswalker an opponent controls.",
    "• Target planeswalker you control deals damage equal to its loyalty to target creature or planeswalker an opponent controls."
  ]

def flourishingGrapple : CardDef :=
  fromOracleKeeping [
    "Flourishing Grapple",
    "{G}",
    "Instant",
    "Target creature or planeswalker an opponent controls that's red or white loses all abilities until end of turn. Target creature you control deals damage equal to its power to that permanent."
  ]

def gardenize : CardDef :=
  fromOracleKeeping [
    "Gardenize",
    "{1}{G}{G}",
    "Enchantment",
    "Whenever a creature you control dies, put a charge counter on this enchantment.",
    "At the beginning of your first main phase, add {G} for each charge counter on this enchantment."
  ]

def greenhousePropagator : CardDef :=
  fromOracleKeeping [
    "Greenhouse Propagator",
    "{2}{G}",
    "Creature — Cat Druid",
    "2/3",
    "Whenever another creature you control enters, you gain 1 life.",
    "{T}: Add {G}."
  ]

def heartwoodCrafter : CardDef :=
  fromOracleKeeping [
    "Heartwood Crafter",
    "{G}",
    "Creature — Elf Artificer",
    "1/1",
    "This creature enters prepared. (While it's prepared, you may cast a copy of its spell. Doing so unprepares it.)",
    "{T}: Add {C}. This mana can't be spent to cast spells from your hand.",
    "//PREP//",
    "Soul Tether",
    "{2}{R/G}",
    "Sorcery",
    "Create a Heartwood token. (It's a red and green artifact with \"{T}: Add {R} or {G}.\")"
  ]

def hexhavenInvigorator : CardDef :=
  fromOracleKeeping [
    "Hexhaven Invigorator",
    "{G}{G}{G}{G}",
    "Creature — Chimera Horror",
    "6/6",
    "Vigilance",
    "Whenever this creature is dealt damage, you may search your library for up to that many land cards, put them onto the battlefield tapped, then shuffle."
  ]

def hungeringPuppetbeast : CardDef :=
  fromOracleKeeping [
    "Hungering Puppetbeast",
    "{3}{G}{G}",
    "Artifact Creature — Beast Construct",
    "5/5",
    "When this creature enters, create a Heartwood token. (It's a red and green artifact with \"{T}: Add {R} or {G}.\")",
    "{1}, Sacrifice another artifact: Put a +1/+1 counter on this creature. It gains your choice of trample, hexproof, or haste until end of turn."
  ]

def huntersAxe : CardDef :=
  fromOracleKeeping [
    "Hunter's Axe",
    "{G}",
    "Artifact — Equipment",
    "Equipped creature gets +2/+0 and has \"Whenever this creature attacks, it gains your choice of trample or deathtouch until end of turn.\"",
    "Equip {2} ({2}: Attach to target creature you control. Equip only as a sorcery.)"
  ]

def inspiredTethermage : CardDef :=
  fromOracleKeeping [
    "Inspired Tethermage",
    "{2}{G}",
    "Creature — Elf Warrior",
    "3/2",
    "Whenever you put one or more loyalty counters on a planeswalker, put a +1/+1 counter on this creature.",
    "{6}: Empower Jace 2. (Put two loyalty counters on a Jace token you control. If you don't control one, first create a blue Jace planeswalker token with \"[−1]: Surveil 1\" and \"[−3]: Draw a card.\")"
  ]

def omnipresence : CardDef :=
  fromOracleKeeping [
    "Omnipresence",
    "{5}{G}{G}{G}",
    "Enchantment",
    "You may cast spells with mana value less than or equal to the number of creatures you control from your hand without paying their mana costs."
  ]

def puppetCrafting : CardDef :=
  fromOracleKeeping [
    "Puppet Crafting",
    "{1}{G}",
    "Enchantment — Aura",
    "Enchant artifact or non-Aura enchantment",
    "Enchanted permanent is a Construct creature with base power and toughness 5/5 in addition to its other types.",
    "{4}{G}: Return this card from your graveyard to your hand."
  ]

def restoreWithEmpathy : CardDef :=
  fromOracleKeeping [
    "Restore with Empathy",
    "{2}{G}",
    "Instant",
    "Return target permanent card from your graveyard to your hand. You gain 4 life."
  ]

def simulacrumShaper : CardDef :=
  fromOracleKeeping [
    "Simulacrum Shaper",
    "{1}{G}{G}",
    "Creature — Elf Druid",
    "2/2",
    "When this creature enters, you may search your library for a basic land card, put that card onto the battlefield tapped, then shuffle.",
    "When this creature dies, draw a card."
  ]

def somethingWorthSaving : CardDef :=
  fromOracleKeeping [
    "Something Worth Saving",
    "{1}{G}",
    "Instant",
    "Mill four cards. You may put a permanent card from among them into your hand. You gain 1 life. (To mill four cards, put the top four cards of your library into your graveyard.)"
  ]

def sureshotSower : CardDef :=
  fromOracleKeeping [
    "Sureshot Sower",
    "{1}{G}",
    "Creature — Human Archer",
    "3/1",
    "Reach",
    "{3}{G}, Discard this card: Destroy target creature with flying."
  ]

def tarmogoyf : CardDef :=
  fromOracleKeeping [
    "Tarmogoyf",
    "{1}{G}",
    "Creature — Lhurgoyf",
    "*/1+*",
    "Tarmogoyf's power is equal to the number of card types among cards in all graveyards and its toughness is equal to that number plus 1."
  ]

def tethermagesAdvantage : CardDef :=
  fromOracleKeeping [
    "Tethermage's Advantage",
    "{G}",
    "Instant",
    "Target creature gets +2/+2 and gains reach until end of turn. Untap it."
  ]

def verdantKraken : CardDef :=
  fromOracleKeeping [
    "Verdant Kraken",
    "{4}{G}{G}{G}",
    "Creature — Plant Kraken",
    "6/6",
    "At the beginning of each player's upkeep, you create a 3/3 green Forest Tentacle land creature token. (It has \"{T}: Add {G}.\" It's affected by summoning sickness until your next turn.)"
  ]

def vinelasherAdept : CardDef :=
  fromOracleKeeping [
    "Vinelasher Adept",
    "{4}{G}{G}",
    "Creature — Rhino Soldier",
    "2/4",
    "Reach",
    "When this creature enters, put three +1/+1 counters on target creature.",
    "Basic landcycling {2} ({2}, Discard this card: Search your library for a basic land card, reveal it, put it into your hand, then shuffle.)"
  ]

def wreckingGecko : CardDef :=
  fromOracleKeeping [
    "Wrecking Gecko",
    "{4}{G}",
    "Artifact Creature — Lizard Construct",
    "5/5",
    "Ward {2} (Whenever this creature becomes the target of a spell or ability an opponent controls, counter it unless that player pays {2}.)",
    "{6}{G}{G}: This creature gets +4/+4 and gains trample until end of turn."
  ]

def aeridKonstrari : CardDef :=
  fromOracleKeeping [
    "Aerid Konstrari",
    "{1}{R}{G}{G}",
    "Legendary Creature — Elder Sphinx",
    "5/4",
    "Flying",
    "When Aerid Konstrari enters or dies, create a Heartwood token. (It's a red and green artifact with \"{T}: Add {R} or {G}.\")",
    "{6}: Create a Heartwood token. Then Aerid Konstrari gets +X/+0 until end of turn, where X is the number of artifacts you control."
  ]

def avatarOfBurgeoningEchoes : CardDef :=
  fromOracleKeeping [
    "Avatar of Burgeoning Echoes",
    "{G}{U}",
    "Creature — Avatar",
    "2/3",
    "Landfall — Whenever a land you control enters, empower Jace 2. (Put two loyalty counters on a Jace token you control. If you don't control one, first create a blue Jace planeswalker token with \"[−1]: Surveil 1\" and \"[−3]: Draw a card.\")",
    "Planeswalkers you control have \"[−10]: Put a +1/+1 counter on target creature for each land you control.\""
  ]

def blessedGhoul : CardDef :=
  fromOracleKeeping [
    "Blessed Ghoul",
    "{W/B}",
    "Creature — Zombie Cleric",
    "1/1",
    "Lifelink",
    "{2}{W/B}: Return this card from your graveyard to your hand."
  ]

def bloombrute : CardDef :=
  fromOracleKeeping [
    "Bloombrute",
    "{2}{G}{W}",
    "Creature — Plant Elemental",
    "4/4",
    "Whenever you gain life, draw a card. This ability triggers only once each turn.",
    "{4}{G}{W}: Target creature gains trample and lifelink until end of turn."
  ]

def chargeTheSanctum : CardDef :=
  fromOracleKeeping [
    "Charge the Sanctum",
    "{2}{R/W}",
    "Instant",
    "Choose one —",
    "• Creatures you control get +2/+0 until end of turn.",
    "• Target creature gets +2/+0 and gains first strike until end of turn. Put a +1/+1 counter on it."
  ]

def clashOfElements : CardDef :=
  fromOracleKeeping [
    "Clash of Elements",
    "{1}{U}{R}",
    "Instant",
    "Choose target nonland permanent. Its owner may put it on top of their library. If they do, Clash of Elements deals 2 damage to them. If they didn't put the card on top of their library, they put it on the bottom."
  ]

def craftworkCrusher : CardDef :=
  fromOracleKeeping [
    "Craftwork Crusher",
    "{3}{R}{R}{G}{G}",
    "Artifact Creature — Boar Construct",
    "7/5",
    "Trample",
    "When this creature enters, choose two —",
    "• This creature deals 4 damage to target creature or planeswalker.",
    "• Create a 2/2 colorless Wizard Soldier creature token named Cadet.",
    "• Draw a card."
  ]

def denziloreFatehold : CardDef :=
  fromOracleKeeping [
    "Denzilore Fatehold",
    "{1}{W}{U}{U}",
    "Legendary Creature — Elder Sphinx",
    "3/4",
    "Flash",
    "Flying",
    "Whenever you scry or surveil, put a +1/+1 counter on each creature you control."
  ]

def desperateFuturescribe : CardDef :=
  fromOracleKeeping [
    "Desperate Futurescribe",
    "{2}{W}{U}",
    "Creature — Kor Scout",
    "3/4",
    "Flying",
    "At the beginning of combat on your turn, another target creature you control gets +1/+1 until end of turn. If you've scried or surveilled this turn, put a +1/+1 counter on that creature instead."
  ]

def emergencyPhytomedic : CardDef :=
  fromOracleKeeping [
    "Emergency Phytomedic",
    "{G/W}",
    "Creature — Dryad Cleric",
    "1/1",
    "This creature enters prepared. (While it's prepared, you may cast a copy of its spell. Doing so unprepares it.)",
    "//PREP//",
    "Seed Suture",
    "{G/W}",
    "Sorcery",
    "Put a +1/+1 counter on target creature. You gain 1 life."
  ]

def entrustTheSpark : CardDef :=
  fromOracleKeeping [
    "Entrust the Spark",
    "{3}{G}{U}",
    "Sorcery",
    "You may sacrifice a planeswalker. If you do, search your library for a planeswalker card, put it onto the battlefield, then shuffle."
  ]

def fateholdCharm : CardDef :=
  fromOracleKeeping [
    "Fatehold Charm",
    "{W}{U}",
    "Instant",
    "Choose one —",
    "• Draw a card. Empower Jace 2.",
    "• Return target spell or creature to its owner's hand.",
    "• Creatures you control get +1/+2 until end of turn."
  ]

def fateholdChronologist : CardDef :=
  fromOracleKeeping [
    "Fatehold Chronologist",
    "{1}{W/U}",
    "Creature — Bird Wizard",
    "1/2",
    "Flying",
    "This creature enters prepared. (While it's prepared, you may cast a copy of its spell. Doing so unprepares it.)",
    "//PREP//",
    "Peer Review",
    "{2}{W/U}",
    "Sorcery",
    "Create a 2/2 colorless Wizard Soldier creature token named Cadet. Surveil 1."
  ]

def ferocityOfTheHunt : CardDef :=
  fromOracleKeeping [
    "Ferocity of the Hunt",
    "{1}{B/G}",
    "Enchantment — Aura",
    "Flash",
    "Enchant creature",
    "Enchanted creature gets +1/+0 and has deathtouch.",
    "When enchanted creature dies, return that card to the battlefield tapped under its owner's control."
  ]

def frostbitePyromental : CardDef :=
  fromOracleKeeping [
    "Frostbite Pyromental",
    "{U}{R}{R}",
    "Creature — Elemental",
    "4/4",
    "Trample, haste",
    "Whenever this creature deals combat damage to a player, draw two cards.",
    "At the beginning of the end step, sacrifice this creature."
  ]

def grimRepriser : CardDef :=
  fromOracleKeeping [
    "Grim Repriser",
    "{B}{R}",
    "Creature — Zombie Bard",
    "2/2",
    "Prowess (Whenever you cast a noncreature spell, this creature gets +1/+1 until end of turn.)",
    "{B}{R}: Return this card from your graveyard to the battlefield with a finality counter on it. Activate only if an opponent has been dealt noncombat damage this turn. (If a creature with a finality counter on it would die, exile it instead.)"
  ]

def ingrisStingerquill : CardDef :=
  fromOracleKeeping [
    "Ingris Stingerquill",
    "{B}{R}{R}",
    "Legendary Creature — Elder Sphinx",
    "1/4",
    "Flying",
    "Whenever a creature you control attacks, that creature deals 1 damage to each opponent.",
    "{4}: Create a 2/2 colorless Wizard Soldier creature token named Cadet. Then creatures you control gain haste until end of turn."
  ]

def konstrariCharm : CardDef :=
  fromOracleKeeping [
    "Konstrari Charm",
    "{R}{G}",
    "Instant",
    "Choose one —",
    "• Konstrari Charm deals 6 damage to target creature with flying.",
    "• Put two +1/+1 counters on target creature. It gains trample until end of turn.",
    "• Add {C}{C}{C}."
  ]

def konstrariImproviser : CardDef :=
  fromOracleKeeping [
    "Konstrari Improviser",
    "{1}{R/G}",
    "Creature — Human Artificer",
    "2/2",
    "This creature enters prepared. (While it's prepared, you may cast a copy of its spell. Doing so unprepares it.)",
    "//PREP//",
    "Soul Tether",
    "{2}{R/G}",
    "Sorcery",
    "Create a Heartwood token. (It's a red and green artifact with \"{T}: Add {R} or {G}.\")"
  ]

def kwiaVigorbloom : CardDef :=
  fromOracleKeeping [
    "Kwia Vigorbloom",
    "{3}{G}{W}{W}",
    "Legendary Creature — Elder Sphinx",
    "6/6",
    "Flying, vigilance, lifelink, ward {2}",
    "Whenever you gain life, create a colorless artifact token named Lotus with \"{T}, Sacrifice this token: Add three mana of any one color.\" This ability triggers only once each turn."
  ]

def mindMeanderer : CardDef :=
  fromOracleKeeping [
    "Mind Meanderer",
    "{3}{G}{U}{U}",
    "Creature — Bird Fish Illusion",
    "4/4",
    "Flying",
    "This creature has vigilance as long as you control a Jace planeswalker.",
    "When this creature enters, it fights up to one target creature an opponent controls. (Each deals damage equal to its power to the other.)"
  ]

def nullSummoner : CardDef :=
  fromOracleKeeping [
    "Null Summoner",
    "{2}{U}{B}",
    "Creature — Human Warlock",
    "4/2",
    "When this creature enters, if you cast it, target opponent reveals their hand. You choose a nonland card from it. Exile that card.",
    "Threshold — As long as there are seven or more cards in your graveyard, you may cast the exiled card, and mana of any type can be spent to cast that spell."
  ]

def paradoxShaper : CardDef :=
  fromOracleKeeping [
    "Paradox Shaper",
    "{1}{U/B}",
    "Creature — Octopus Wizard",
    "1/3",
    "At the beginning of your upkeep, if this creature isn't prepared, it becomes prepared.",
    "{2}: Put target card from your graveyard on the bottom of your library.",
    "//PREP//",
    "Omit Variables",
    "{U/B}",
    "Sorcery",
    "Mill three cards. (Put the top three cards of your library into your graveyard.)"
  ]

def primalWitchstalker : CardDef :=
  fromOracleKeeping [
    "Primal Witchstalker",
    "{1}{B}{G}",
    "Creature — Wolf",
    "2/1",
    "Menace (This creature can't be blocked except by two or more creatures.)",
    "When this creature enters, mill four cards. When you do, return target land card from your graveyard to the battlefield tapped. (To mill four cards, put the top four cards of your library into your graveyard.)"
  ]

def proctorOfPotential : CardDef :=
  fromOracleKeeping [
    "Proctor of Potential",
    "{W}{U}",
    "Creature — Human Cleric",
    "3/1",
    "Whenever this creature or another creature you control enters, surveil 1. (Look at the top card of your library. You may put it into your graveyard.)",
    "{W}{U}: Return this card from your graveyard to the battlefield with a finality counter on it. Activate only if you've scried or surveilled this turn. (If a creature with a finality counter on it would die, exile it instead.)"
  ]

def prudentFateseer : CardDef :=
  fromOracleKeeping [
    "Prudent Fateseer",
    "{1}{W/U}{W/U}",
    "Creature — Dwarf Wizard",
    "1/4",
    "This creature enters prepared.",
    "Whenever you scry or surveil, creatures you control get +1/+0 until end of turn. This ability triggers only once each turn.",
    "//PREP//",
    "Peer Review",
    "{2}{W/U}",
    "Sorcery",
    "Create a 2/2 colorless Wizard Soldier creature token named Cadet. Surveil 1."
  ]

def recursiveRecruitment : CardDef :=
  fromOracleKeeping [
    "Recursive Recruitment",
    "{2}{U}{B}",
    "Sorcery",
    "Create two 2/2 colorless Wizard Soldier creature tokens named Cadet. If this spell was cast from a graveyard, put a +1/+1 counter on each of them for every three cards in your graveyard.",
    "Flashback {6}{U}{B} (You may cast this card from your graveyard for its flashback cost. Then exile it.)"
  ]

def solariumSentry : CardDef :=
  fromOracleKeeping [
    "Solarium Sentry",
    "{G}{W}",
    "Creature — Cat Soldier",
    "3/3",
    "Whenever an opponent casts a spell with mana value 2 or less, you gain 2 life."
  ]

def solitaryCell : CardDef :=
  fromOracleKeeping [
    "Solitary Cell",
    "{R}{W}",
    "Artifact",
    "When this artifact enters, exile target nonland permanent an opponent controls with mana value 3 or less until this artifact leaves the battlefield.",
    "{1}, {T}, Discard a legendary card: Draw a card."
  ]

def stingerquillCharm : CardDef :=
  fromOracleKeeping [
    "Stingerquill Charm",
    "{B}{R}",
    "Instant",
    "Choose one —",
    "• Stingerquill Charm deals 3 damage to any target.",
    "• Target creature gains first strike and deathtouch until end of turn.",
    "• Create a 2/2 colorless Wizard Soldier creature token named Cadet. It gains haste until end of turn."
  ]

def stingerquillVoxmancer : CardDef :=
  fromOracleKeeping [
    "Stingerquill Voxmancer",
    "{B/R}",
    "Creature — Goblin Sorcerer",
    "1/2",
    "At the beginning of your upkeep, if this creature isn't prepared, it becomes prepared. (While it's prepared, you may cast a copy of its spell. Doing so unprepares it.)",
    "//PREP//",
    "Vicious Verse",
    "{B/R}",
    "Sorcery",
    "Vicious Verse deals 1 damage to target opponent."
  ]

def stingingVitriol : CardDef :=
  fromOracleKeeping [
    "Stinging Vitriol",
    "{B}{R}",
    "Sorcery",
    "Stinging Vitriol deals 2 damage to target opponent. That player reveals their hand. You choose a nonland card from it. They discard that card."
  ]

def tamsResistance : CardDef :=
  fromOracleKeeping [
    "Tam's Resistance",
    "{1}{G/U}",
    "Sorcery",
    "Put a +1/+1 counter on up to one target creature. It gains vigilance until end of turn.",
    "Empower Jace 4. (Put four loyalty counters on a Jace token you control. If you don't control one, first create a blue Jace planeswalker token with \"[−1]: Surveil 1\" and \"[−3]: Draw a card.\")"
  ]

def tenuredTethermage : CardDef :=
  fromOracleKeeping [
    "Tenured Tethermage",
    "{1}{R}{G}",
    "Creature — Human Artificer",
    "1/1",
    "When this creature enters, you may sacrifice a land. If you do, create two tapped Heartwood tokens. (They're red and green artifacts with \"{T}: Add {R} or {G}.\")",
    "Tap two untapped artifacts you control: Put two +1/+1 counters on this creature."
  ]

def theorixCharm : CardDef :=
  fromOracleKeeping [
    "Theorix Charm",
    "{U}{B}",
    "Instant",
    "Choose one —",
    "• Counter target noncreature spell unless its controller pays {2}.",
    "• Target creature gets -2/-2 until end of turn.",
    "• Mill three cards, then draw a card. (To mill three cards, put the top three cards of your library into your graveyard.)"
  ]

def theorixMetamage : CardDef :=
  fromOracleKeeping [
    "Theorix Metamage",
    "{2}{U/B}",
    "Creature — Shade Wizard",
    "2/3",
    "This creature enters prepared. (While it's prepared, you may cast a copy of its spell. Doing so unprepares it.)",
    "Threshold — This creature gets +1/+0 and has flying as long as there are seven or more cards in your graveyard.",
    "//PREP//",
    "Omit Variables",
    "{U/B}",
    "Sorcery",
    "Mill three cards. (Put the top three cards of your library into your graveyard.)"
  ]

def twinnedVision : CardDef :=
  fromOracleKeeping [
    "Twinned Vision",
    "{1}{U/R}",
    "Instant",
    "Draw a card. If this spell wasn't cast from your hand, draw two cards instead.",
    "Flashback—{1}{U/R}{U/R}, Discard a card. (You may cast this card from your graveyard for its flashback cost. Then exile it.)"
  ]

def twistedFates : CardDef :=
  fromOracleKeeping [
    "Twisted Fates",
    "{2}{W}{W}{B}",
    "Sorcery",
    "Destroy target nonland permanent. Put a +1/+1 counter on each creature target player controls."
  ]

def uldarosTheorix : CardDef :=
  fromOracleKeeping [
    "Uldaros Theorix",
    "{3}{U}{B}{B}",
    "Legendary Creature — Elder Sphinx",
    "5/5",
    "Flying",
    "When Uldaros Theorix enters, if you cast him, exile up to one target nonland card of each card type from your graveyard. Copy those cards. You may cast any number of spells with total mana value 6 or less from among the copies without paying their mana costs. (Permanent spells cast this way become tokens.)"
  ]

def vigorbloomCharm : CardDef :=
  fromOracleKeeping [
    "Vigorbloom Charm",
    "{G}{W}",
    "Instant",
    "Choose one —",
    "• Target permanent you control gains hexproof and indestructible until end of turn.",
    "• You draw a card and gain 3 life.",
    "• Put a +1/+1 counter on target creature you control. Then it fights target creature an opponent controls. (Each deals damage equal to its power to the other.)"
  ]

def vigorbloomVanguard : CardDef :=
  fromOracleKeeping [
    "Vigorbloom Vanguard",
    "{1}{G/W}",
    "Creature — Troll Druid",
    "2/2",
    "This creature enters prepared. (While it's prepared, you may cast a copy of its spell. Doing so unprepares it.)",
    "Each creature you control with a +1/+1 counter on it has vigilance.",
    "//PREP//",
    "Seed Suture",
    "{G/W}",
    "Sorcery",
    "Put a +1/+1 counter on target creature. You gain 1 life."
  ]

def vindictiveTriumph : CardDef :=
  fromOracleKeeping [
    "Vindictive Triumph",
    "{W}{B}{B}",
    "Instant",
    "Exile target creature or planeswalker. If that permanent's mana value was 3 or less, return it to the battlefield tapped under your control. Exile it at the beginning of the next end step."
  ]

def warriorsBlades : CardDef :=
  fromOracleKeeping [
    "Warrior's Blades",
    "{2}{R}{W}",
    "Artifact — Equipment",
    "When this Equipment enters, it deals 3 damage to any target and you gain 3 life.",
    "Equipped creature gets +2/+1.",
    "Equip {3}. This ability costs {1} less to activate for each +1/+1 counter on the creature it targets."
  ]

def whiplashWordsmith : CardDef :=
  fromOracleKeeping [
    "Whiplash Wordsmith",
    "{3}{B/R}",
    "Creature — Vampire Sorcerer",
    "3/3",
    "This creature enters prepared. (While it's prepared, you may cast a copy of its spell. Doing so unprepares it.)",
    "As long as an opponent was dealt noncombat damage this turn, this creature has flying and haste.",
    "//PREP//",
    "Vicious Verse",
    "{B/R}",
    "Sorcery",
    "Vicious Verse deals 1 damage to target opponent."
  ]

def woodworkProdigy : CardDef :=
  fromOracleKeeping [
    "Woodwork Prodigy",
    "{2}{R/G}",
    "Creature — Cat Druid",
    "3/3",
    "At the beginning of your upkeep, if this creature isn't prepared, it becomes prepared. (While it's prepared, you may cast a copy of its spell. Doing so unprepares it.)",
    "//PREP//",
    "Soul Tether",
    "{2}{R/G}",
    "Sorcery",
    "Create a Heartwood token. (It's a red and green artifact with \"{T}: Add {R} or {G}.\")"
  ]

def afterthoughtSentry : CardDef :=
  fromOracleKeeping [
    "Afterthought Sentry",
    "{2}",
    "Artifact Creature — Gargoyle",
    "2/2",
    "{2}: This creature gains flying until end of turn.",
    "Whenever this creature attacks, exile up to one target card from a graveyard."
  ]

def archiveArbiter : CardDef :=
  fromOracleKeeping [
    "Archive Arbiter",
    "{6}",
    "Artifact Creature — Sphinx",
    "4/4",
    "Flying",
    "When this creature enters, choose one —",
    "• Destroy target noncreature, nonland permanent.",
    "• You gain 4 life."
  ]

def codieRavenousCodex : CardDef :=
  fromOracleKeeping [
    "Codie, Ravenous Codex",
    "{3}",
    "Legendary Artifact Creature — Book Construct",
    "1/4",
    "Whenever you cast a prepared spell, copy it. You may choose new targets for the copy.",
    "{W}{U}{B}{R}{G}, {T}: Each creature you control becomes prepared. (Only creatures with prepare spells can become prepared.)"
  ]

def theEchoverseFulcrum : CardDef :=
  fromOracleKeeping [
    "The Echoverse Fulcrum",
    "{2}",
    "Legendary Artifact",
    "When The Echoverse Fulcrum enters, draw a card, then discard a card.",
    "{5}, {T}, Exile The Echoverse Fulcrum: Destroy all creatures. Activate only as a sorcery."
  ]

def eyeOfJace : CardDef :=
  fromOracleKeeping [
    "Eye of Jace",
    "{1}",
    "Artifact",
    "At the beginning of your upkeep, surveil 1. Then if there are seven or more cards in your graveyard, sacrifice this artifact, it deals 2 damage to each opponent, and you gain 2 life. (To surveil 1, look at the top card of your library. You may put it into your graveyard.)"
  ]

def keeperOfTheQuietHour : CardDef :=
  fromOracleKeeping [
    "Keeper of the Quiet Hour",
    "{3}",
    "Artifact Creature — Chimera",
    "3/2",
    "When this creature enters, empower Jace 2. (Put two loyalty counters on a Jace token you control. If you don't control one, first create a blue Jace planeswalker token with \"[−1]: Surveil 1\" and \"[−3]: Draw a card.\")"
  ]

def livingLibrary : CardDef :=
  fromOracleKeeping [
    "Living Library",
    "{2}",
    "Artifact Creature — Book Illusion",
    "0/4",
    "{6}, Sacrifice this creature: Choose target creature or planeswalker an opponent controls. Its owner shuffles it into their library."
  ]

def medicsKitesail : CardDef :=
  fromOracleKeeping [
    "Medic's Kitesail",
    "{2}",
    "Artifact — Equipment",
    "Equipped creature gets +1/+0 and has flying and \"Whenever this creature attacks, you gain 1 life.\"",
    "Equip {2} ({2}: Attach to target creature you control. Equip only as a sorcery.)"
  ]

def murmuringVolume : CardDef :=
  fromOracleKeeping [
    "Murmuring Volume",
    "{3}",
    "Artifact — Book",
    "{T}: Add one mana of any color.",
    "{2}, {T}, Discard a card: Draw a card."
  ]

def dedicatedCommons : CardDef :=
  fromOracleKeeping [
    "Dedicated Commons",
    "Land",
    "This land enters tapped unless you control a planeswalker.",
    "{T}: Add {R} or {W}."
  ]

def desertedBeach : CardDef :=
  fromOracleKeeping [
    "Deserted Beach",
    "Land",
    "This land enters tapped unless you control two or more other lands.",
    "{T}: Add {W} or {U}."
  ]

def fateholdAnnex : CardDef :=
  fromOracleKeeping [
    "Fatehold Annex",
    "Land",
    "This land enters tapped unless you control a planeswalker.",
    "{T}: Add {W} or {U}."
  ]

def formidableCommons : CardDef :=
  fromOracleKeeping [
    "Formidable Commons",
    "Land",
    "This land enters tapped unless you control a planeswalker.",
    "{T}: Add {B} or {G}."
  ]

def hallOfEchoes : CardDef :=
  fromOracleKeeping [
    "Hall of Echoes",
    "Land",
    "{T}: Add {C}.",
    "{5}: This land becomes a copy of target creature you control until end of turn. The \"legend rule\" doesn't apply to permanents you control this turn."
  ]

def hauntedRidge : CardDef :=
  fromOracleKeeping [
    "Haunted Ridge",
    "Land",
    "This land enters tapped unless you control two or more other lands.",
    "{T}: Add {B} or {R}."
  ]

def hexhavenDuelingArena : CardDef :=
  fromOracleKeeping [
    "Hexhaven Dueling Arena",
    "Land",
    "{T}: Add {C}.",
    "{2}, {T}: Target creature that attacked this turn becomes prepared. Activate only as a sorcery. (Only creatures with prepare spells can become prepared.)",
    "{4}, {T}: Target creature becomes prepared."
  ]

def innovativeCommons : CardDef :=
  fromOracleKeeping [
    "Innovative Commons",
    "Land",
    "This land enters tapped unless you control a planeswalker.",
    "{T}: Add {U} or {R}."
  ]

def konstrariAnnex : CardDef :=
  fromOracleKeeping [
    "Konstrari Annex",
    "Land",
    "This land enters tapped unless you control a planeswalker.",
    "{T}: Add {R} or {G}."
  ]

def meticulousCommons : CardDef :=
  fromOracleKeeping [
    "Meticulous Commons",
    "Land",
    "This land enters tapped unless you control a planeswalker.",
    "{T}: Add {W} or {B}."
  ]

def overgrownFarmland : CardDef :=
  fromOracleKeeping [
    "Overgrown Farmland",
    "Land",
    "This land enters tapped unless you control two or more other lands.",
    "{T}: Add {G} or {W}."
  ]

def rockfallVale : CardDef :=
  fromOracleKeeping [
    "Rockfall Vale",
    "Land",
    "This land enters tapped unless you control two or more other lands.",
    "{T}: Add {R} or {G}."
  ]

def roilingCanopy : CardDef :=
  fromOracleKeeping [
    "Roiling Canopy",
    "Land",
    "This land enters tapped.",
    "Whenever a Forest you control enters, if you control at least five other Forests, target creature you control gets +3/+3 until end of turn.",
    "{T}: Add {G}."
  ]

def roomOfRefuge : CardDef :=
  fromOracleKeeping [
    "Room of Refuge",
    "Land",
    "This land enters tapped. As it enters, choose a color.",
    "{T}: Add one mana of the chosen color.",
    "{5}, {T}, Sacrifice this land: Put two +1/+1 counters on target creature. Activate only as a sorcery."
  ]

def shipwreckMarsh : CardDef :=
  fromOracleKeeping [
    "Shipwreck Marsh",
    "Land",
    "This land enters tapped unless you control two or more other lands.",
    "{T}: Add {U} or {B}."
  ]

def stingerquillAnnex : CardDef :=
  fromOracleKeeping [
    "Stingerquill Annex",
    "Land",
    "This land enters tapped unless you control a planeswalker.",
    "{T}: Add {B} or {R}."
  ]

def theoristsSanctum : CardDef :=
  fromOracleKeeping [
    "Theorist's Sanctum",
    "Land — Island",
    "({T}: Add {U}.)",
    "As this land enters, you may behold a Jace. If you don't, this land enters tapped. (To behold a Jace, choose a Jace you control or reveal a Jace card from your hand.)",
    "{2}{U}, {T}: Empower Jace 2."
  ]

def theorixAnnex : CardDef :=
  fromOracleKeeping [
    "Theorix Annex",
    "Land",
    "This land enters tapped unless you control a planeswalker.",
    "{T}: Add {U} or {B}."
  ]

def transformativeCommons : CardDef :=
  fromOracleKeeping [
    "Transformative Commons",
    "Land",
    "This land enters tapped unless you control a planeswalker.",
    "{T}: Add {G} or {U}."
  ]

def vigorbloomAnnex : CardDef :=
  fromOracleKeeping [
    "Vigorbloom Annex",
    "Land",
    "This land enters tapped unless you control a planeswalker.",
    "{T}: Add {G} or {W}."
  ]

def ajaniResolute : CardDef :=
  fromOracleKeeping [
    "Ajani Resolute",
    "{1}{W}",
    "Legendary Planeswalker — Ajani",
    "Whenever you gain life, put a loyalty counter on Ajani.",
    "0: You gain 1 life.",
    "−4: Create a 2/2 white Cat Soldier creature token named Ajani's Pridemate with \"Whenever you gain life, put a +1/+1 counter on this token.\"",
    "−10: You get an emblem with \"Creatures you control get +2/+2.\"",
    "Loyalty: 2"
  ]

def danithaSwordOfHope : CardDef :=
  fromOracleKeeping [
    "Danitha, Sword of Hope",
    "{2}{W}",
    "Legendary Creature — Human Knight",
    "2/2",
    "First strike",
    "Whenever you cast an Equipment spell or a spell that targets a creature you control, draw a card. This ability triggers only once each turn."
  ]

def ghaltaTheImmovable : CardDef :=
  fromOracleKeeping [
    "Ghalta the Immovable",
    "{8}{W}",
    "Legendary Creature — Elder Dinosaur",
    "0/7",
    "This spell costs {X} less to cast, where X is the greatest toughness among creatures you control.",
    "Creatures you control can attack as though they didn't have defender.",
    "Each creature you control with toughness greater than its power assigns combat damage equal to its toughness rather than its power."
  ]

def gideonsMemorial : CardDef :=
  fromOracleKeeping [
    "Gideon's Memorial",
    "{1}{W}",
    "Legendary Artifact",
    "Creature tokens you control get +1/+0 and have vigilance.",
    "{T}: Add one mana of any color. Spend this mana only to cast a planeswalker spell.",
    "{1}{W}, Discard this card: It deals 4 damage to target attacking or blocking creature."
  ]

def kothOfTheHomestead : CardDef :=
  fromOracleKeeping [
    "Koth of the Homestead",
    "{2}{W}",
    "Legendary Creature — Human Citizen",
    "2/3",
    "Landfall — Whenever a land you control enters, you gain 1 life.",
    "Whenever a Plains you control enters, put a +1/+1 counter on target creature."
  ]

def lilianaTheFaultless : CardDef :=
  fromOracleKeeping [
    "Liliana the Faultless",
    "{W}",
    "Legendary Creature — Human Cleric",
    "1/1",
    "Whenever another creature or planeswalker you control enters, you gain 1 life.",
    "{1}, {T}, Discard a card: Another target creature or planeswalker you control gains hexproof until end of turn."
  ]

def lyraArchangelOfDawn : CardDef :=
  fromOracleKeeping [
    "Lyra, Archangel of Dawn",
    "{2}{W}",
    "Legendary Creature — Angel Knight",
    "3/3",
    "Flying",
    "Whenever you gain life, put a +1/+1 counter on each Angel you control."
  ]

def rescueGirlFirstResponder : CardDef :=
  fromOracleKeeping [
    "Rescue Girl, First Responder",
    "{2}{W}",
    "Legendary Creature — Human Cleric",
    "1/3",
    "Flying",
    "{T}: Return another target permanent you control to its owner's hand. Activate only during your turn."
  ]

def saheeliConsulOfOversight : CardDef :=
  fromOracleKeeping [
    "Saheeli, Consul of Oversight",
    "{3}{W}{W}",
    "Legendary Creature — Human Advisor",
    "4/4",
    "Flying",
    "Whenever you scry or surveil, create a 1/1 colorless Thopter artifact creature token with flying. This ability triggers only once each turn."
  ]

def teyoLightshieldExpert : CardDef :=
  fromOracleKeeping [
    "Teyo, Lightshield Expert",
    "{1}{W}",
    "Legendary Creature — Human Cleric",
    "1/1",
    "Flash",
    "When Teyo enters, target permanent you control gains hexproof until end of turn. Put a +1/+1 counter on it if it's a creature. Put a loyalty counter on it if it's a planeswalker. (It can't be the target of spells or abilities your opponents control.)"
  ]

def thaliaTheSurvivor : CardDef :=
  fromOracleKeeping [
    "Thalia, the Survivor",
    "{3}{W}",
    "Legendary Creature — Human Soldier",
    "3/4",
    "Lifelink",
    "Noncreature spells your opponents cast cost {1} more to cast."
  ]

def tomikOrzhovLawmage : CardDef :=
  fromOracleKeeping [
    "Tomik, Orzhov Lawmage",
    "{1}{W}",
    "Legendary Creature — Human Advisor",
    "2/1",
    "Flying",
    "Planeswalkers you control have \"No more than one creature can attack this planeswalker each combat.\"",
    "{T}: Target creature with a +1/+1 counter on it gains flying until end of turn."
  ]

def wayOfTheHealer : CardDef :=
  fromOracleKeeping [
    "Way of the Healer",
    "{3}{W}",
    "Legendary Enchantment",
    "When Way of the Healer enters, empower Jace 5. (Put five loyalty counters on a Jace token you control. If you don't control one, first create a blue Jace planeswalker token with \"[−1]: Surveil 1\" and \"[−3]: Draw a card.\")",
    "Planeswalkers you control have \"[−2]: Create a 2/2 colorless Wizard Soldier creature token named Cadet. Surveil 1.\""
  ]

def wayOfTheMentor : CardDef :=
  fromOracleKeeping [
    "Way of the Mentor",
    "{2}{W}",
    "Legendary Enchantment",
    "When Way of the Mentor enters, empower Jace 5. (Put five loyalty counters on a Jace token you control. If you don't control one, first create a blue Jace planeswalker token with \"[−1]: Surveil 1\" and \"[−3]: Draw a card.\")",
    "Whenever you gain life, put a loyalty counter on each planeswalker you control."
  ]

def yoshimaruBelovedCompanion : CardDef :=
  fromOracleKeeping [
    "Yoshimaru, Beloved Companion",
    "{2}{W}",
    "Legendary Creature — Dog",
    "2/2",
    "If one or more +1/+1 counters would be put on a creature you control, that many plus one +1/+1 counters are put on it instead.",
    "{6}: Put a +1/+1 counter on target legendary creature."
  ]

def yurikoBladeOfTheMighty : CardDef :=
  fromOracleKeeping [
    "Yuriko, Blade of the Mighty",
    "{3}{W}",
    "Legendary Creature — Human Samurai",
    "2/3",
    "During combat, players can't cast spells or activate abilities that aren't mana abilities.",
    "Whenever a creature you control attacks a player alone, it gains double strike until end of turn."
  ]

def arniHumbleScribe : CardDef :=
  fromOracleKeeping [
    "Arni, Humble Scribe",
    "{2}{U}",
    "Legendary Creature — Human Wizard",
    "3/2",
    "Whenever another nontoken creature you control enters, untap Arni.",
    "{T}: Draw a card, then discard a card."
  ]

def chandraChillOfCompliance : CardDef :=
  fromOracleKeeping [
    "Chandra, Chill of Compliance",
    "{1}{U}{U}",
    "Legendary Planeswalker — Chandra",
    "+1: Surveil 1. If you put a noncreature, nonland card into your graveyard this way, put that card into your hand.",
    "+1: Add {U}. Spend this mana only to cast a noncreature spell.",
    "−X: Tap target artifact or creature. Put X stun counters on it.",
    "−6: You get an emblem with \"Whenever you cast a spell, draw a card.\"",
    "Loyalty: 3"
  ]

def fblthpImpossiblyLost : CardDef :=
  fromOracleKeeping [
    "Fblthp, Impossibly Lost",
    "{1}{U}",
    "Legendary Creature — Homunculus",
    "1/1",
    "When one or more of your opponents are dealt combat damage during your turn, draw two cards. If your library has no cards in it, you win the game. Fblthp's owner shuffles him into their library. (If you draw from an empty library this way, you still win the game.)"
  ]

def geistOfSaintThalia : CardDef :=
  fromOracleKeeping [
    "Geist of Saint Thalia",
    "{1}{U}",
    "Legendary Creature — Spirit Cleric",
    "1/2",
    "Flying",
    "Noncreature spells you cast cost {1} less to cast."
  ]

def hapatraTheDesertFrost : CardDef :=
  fromOracleKeeping [
    "Hapatra, the Desert Frost",
    "{3}{U}",
    "Legendary Creature — Human Wizard",
    "4/3",
    "When Hapatra enters, for each opponent, tap up to one target creature that player controls. Put a stun counter on each of those creatures. (If a permanent with a stun counter would become untapped, remove one from it instead.)",
    "{2}{U}: Untap target creature."
  ]

def jaceRealitySculptor : CardDef :=
  fromOracleKeeping [
    "Jace, Reality Sculptor",
    "{3}{U}{U}",
    "Legendary Planeswalker — Jace",
    "+1: Empower Jace X, where X is the number of Islands you control.",
    "−3: Until your next turn, whenever a creature attacks you or a planeswalker you control, it gets -5/-0 until end of turn.",
    "0: Exile all but the bottom card of each opponent's library. Activate only if there are twenty-five or more loyalty counters among Jaces you control.",
    "Loyalty: 5"
  ]

def lyraTolarianArchangel : CardDef :=
  fromOracleKeeping [
    "Lyra, Tolarian Archangel",
    "{1}{U}{U}",
    "Legendary Creature — Angel Wizard",
    "3/3",
    "Flying",
    "At the beginning of each end step, if you've drawn three or more cards this turn, create a 3/3 blue Angel creature token with flying.",
    "{3}{U}{U}: Until end of turn, whenever Lyra deals combat damage to a player, draw two cards."
  ]

def proftConsultingDetective : CardDef :=
  fromOracleKeeping [
    "Proft, Consulting Detective",
    "{1}{U}",
    "Legendary Creature — Human Detective",
    "2/2",
    "Whenever you scry or surveil, you may pay {2}. If you do, put a +1/+1 counter on Proft and draw a card. (Draw after you scry or surveil.)"
  ]

def ruricTharBiomagus : CardDef :=
  fromOracleKeeping [
    "Ruric Thar, Biomagus",
    "{4}{U}{U}",
    "Legendary Creature — Ogre Crab Wizard",
    "4/6",
    "Flying",
    "Prowess, prowess (Whenever you cast a noncreature spell, this creature gets +1/+1 until end of turn twice.)",
    "Whenever Ruric Thar becomes the target of a spell or ability an opponent controls, draw a card."
  ]

def samutTyrantOfNaktamun : CardDef :=
  fromOracleKeeping [
    "Samut, Tyrant of Naktamun",
    "{1}{U}",
    "Legendary Creature — Human Wizard",
    "2/1",
    "Instant and sorcery spells you control have split second. (As long as a spell with split second is on the stack, players can't cast spells or activate abilities that aren't mana abilities.)"
  ]

def tetsukoUmezawaFugitive : CardDef :=
  fromOracleKeeping [
    "Tetsuko Umezawa, Fugitive",
    "{1}{U}",
    "Legendary Creature — Human Rogue",
    "1/3",
    "Creatures you control with power or toughness 1 or less can't be blocked."
  ]

def traxosAcademyGuardian : CardDef :=
  fromOracleKeeping [
    "Traxos, Academy Guardian",
    "{3}{U}",
    "Legendary Artifact Creature — Dragon Construct",
    "1/5",
    "This spell costs {2} less to cast if you've cast a noncreature spell this turn.",
    "Flying, vigilance",
    "Prowess (Whenever you cast a noncreature spell, this creature gets +1/+1 until end of turn.)"
  ]

def wayOfTheCryomancer : CardDef :=
  fromOracleKeeping [
    "Way of the Cryomancer",
    "{2}{U}",
    "Legendary Enchantment",
    "When Way of the Cryomancer enters, empower Jace 5. (Put five loyalty counters on a Jace token you control. If you don't control one, first create a blue Jace planeswalker token with \"[−1]: Surveil 1\" and \"[−3]: Draw a card.\")",
    "Planeswalkers you control have \"[−3]: When you next cast an instant or sorcery spell this turn, copy that spell. You may choose new targets for the copy.\""
  ]

def wayOfTheMindSculptor : CardDef :=
  fromOracleKeeping [
    "Way of the Mind Sculptor",
    "{4}{U}",
    "Legendary Enchantment",
    "When Way of the Mind Sculptor enters, empower Jace 5. (Put five loyalty counters on a Jace token you control. If you don't control one, first create a blue Jace planeswalker token with \"[−1]: Surveil 1\" and \"[−3]: Draw a card.\")",
    "Whenever you activate a loyalty ability, if you removed two or more loyalty counters to activate it, draw a card."
  ]

def yargleGoliathOfOtaria : CardDef :=
  fromOracleKeeping [
    "Yargle, Goliath of Otaria",
    "{4}{U}",
    "Legendary Creature — Frog Spirit",
    "3/9"
  ]

def yurikoHopeFromTheShadows : CardDef :=
  fromOracleKeeping [
    "Yuriko, Hope from the Shadows",
    "{U}",
    "Legendary Creature — Human Ninja",
    "1/1",
    "Flash",
    "When Yuriko enters, choose one —",
    "• Target creature gets -X/-0 until end of turn, where X is the number of cards in your graveyard.",
    "• Surveil 2. (Look at the top two cards of your library, then put any number of them into your graveyard and the rest on top of your library in any order.)"
  ]

def danithaSpearOfAgony : CardDef :=
  fromOracleKeeping [
    "Danitha, Spear of Agony",
    "{2}{B}",
    "Legendary Creature — Human Knight",
    "2/2",
    "First strike",
    "Whenever you cast a spell that targets an opponent or a creature an opponent controls, put a +1/+1 counter on Danitha."
  ]

def galliaTragicHost : CardDef :=
  fromOracleKeeping [
    "Gallia, Tragic Host",
    "{1}{B}",
    "Legendary Creature — Zombie Satyr",
    "2/1",
    "Menace (This creature can't be blocked except by two or more creatures.)",
    "{4}{B}, Exile another creature card from your graveyard: Return this card from your graveyard to the battlefield tapped with a +1/+1 counter on her."
  ]

def garrukVeiledButcher : CardDef :=
  fromOracleKeeping [
    "Garruk, Veiled Butcher",
    "{3}{B}{B}",
    "Legendary Planeswalker — Garruk",
    "If a creature an opponent controls would die, exile it instead.",
    "+2: Up to one target creature gets -4/-1 until your next turn.",
    "−2: Each player sacrifices a creature of their choice. If you sacrificed a creature this way, create a 4/4 green Beast creature token with trample.",
    "−3: Each opponent discards two cards. For each opponent who didn't discard two nonland cards this way, you draw a card.",
    "Loyalty: 5"
  ]

def gideonTheOathless : CardDef :=
  fromOracleKeeping [
    "Gideon the Oathless",
    "{2}{B}",
    "Legendary Creature — Human Mercenary",
    "3/3",
    "Ward—Discard a card.",
    "Whenever a creature an opponent controls enters, Gideon deals 1 damage to that player.",
    "Whenever an opponent activates a loyalty ability, Gideon deals 1 damage to that player."
  ]

def lilianaTheRepentant : CardDef :=
  fromOracleKeeping [
    "Liliana the Repentant",
    "{1}{B}",
    "Legendary Creature — Human Warlock",
    "2/2",
    "Whenever another creature or planeswalker you control enters, mill two cards.",
    "Exhaust — {5}{B}: Return target creature or planeswalker card from your graveyard to the battlefield. Put a +1/+1 counter on Liliana. Activate only as a sorcery. (Activate each exhaust ability only once.)"
  ]

def lootTheAnomaly : CardDef :=
  fromOracleKeeping [
    "Loot, the Anomaly",
    "{2}{B}",
    "Legendary Creature — Beast Horror",
    "-2/4",
    "If Loot's power is negative, he assigns combat damage as though his power were positive.",
    "Threshold — Sacrifice another creature or planeswalker: Loot gets -2/-0 until end of turn. Activate only if there are seven or more cards in your graveyard."
  ]

def mabelBitterRecluse : CardDef :=
  fromOracleKeeping [
    "Mabel, Bitter Recluse",
    "{B}",
    "Legendary Creature — Mouse Warlock",
    "1/1",
    "Deathtouch",
    "When Mabel enters, remove up to three counters from another target creature or planeswalker."
  ]

def massacreGirlMostWanted : CardDef :=
  fromOracleKeeping [
    "Massacre Girl, Most Wanted",
    "{4}{B}",
    "Legendary Creature — Human Assassin",
    "4/4",
    "Whenever another creature or planeswalker you control dies, Massacre Girl deals 1 damage to target opponent and you gain 1 life.",
    "Whenever an opponent is dealt noncombat damage, put a +1/+1 counter on Massacre Girl."
  ]

def proftSinisterMastermind : CardDef :=
  fromOracleKeeping [
    "Proft, Sinister Mastermind",
    "{2}{B}",
    "Legendary Creature — Human Rogue",
    "5/5",
    "Threshold — You can't cast this spell unless there are seven or more cards in your graveyard.",
    "Menace",
    "{B}, Discard this card: Target creature gets -3/-1 until end of turn."
  ]

def teyoDiamondbladeMage : CardDef :=
  fromOracleKeeping [
    "Teyo, Diamondblade Mage",
    "{3}{B}",
    "Legendary Creature — Human Warlock",
    "3/1",
    "Flash",
    "When Teyo enters, target permanent you control gains deathtouch until end of turn. Put a +1/+1 counter on it if it's a creature. Put a loyalty counter on it if it's a planeswalker."
  ]

def tinybonesPocketNuisance : CardDef :=
  fromOracleKeeping [
    "Tinybones, Pocket Nuisance",
    "{2}{B}",
    "Legendary Creature — Skeleton Rogue",
    "2/1",
    "When Tinybones enters, each opponent discards a card.",
    "Whenever a player discards one or more cards, Tinybones deals 1 damage to each opponent."
  ]

def wayOfTheDeathbringer : CardDef :=
  fromOracleKeeping [
    "Way of the Deathbringer",
    "{2}{B}",
    "Legendary Enchantment",
    "When Way of the Deathbringer enters, empower Jace 5. (Put five loyalty counters on a Jace token you control. If you don't control one, first create a blue Jace planeswalker token with \"[−1]: Surveil 1\" and \"[−3]: Draw a card.\")",
    "Planeswalkers you control have \"[−2]: You may sacrifice a creature. If you do, create a 4/4 green Beast creature token with trample.\""
  ]

def wayOfTheNecromancer : CardDef :=
  fromOracleKeeping [
    "Way of the Necromancer",
    "{1}{B}",
    "Legendary Enchantment",
    "When Way of the Necromancer enters, empower Jace 2. (Put two loyalty counters on a Jace token you control. If you don't control one, first create a blue Jace planeswalker token with \"[−1]: Surveil 1\" and \"[−3]: Draw a card.\")",
    "Whenever a creature you control dies, put a loyalty counter on each planeswalker you control."
  ]

def winterTormentedLoner : CardDef :=
  fromOracleKeeping [
    "Winter, Tormented Loner",
    "{2}{B}",
    "Legendary Creature — Human Warlock",
    "0/3",
    "When Winter enters, you may sacrifice a creature or planeswalker. When you do, each opponent sacrifices a creature of their choice.",
    "Winter gets +1/+0 for each creature and planeswalker card in your graveyard."
  ]

def yargleGluttonOfUrborg : CardDef :=
  fromOracleKeeping [
    "Yargle, Glutton of Urborg",
    "{4}{B}",
    "Legendary Creature — Frog Spirit",
    "9/3"
  ]

def ajaniUnrelenting : CardDef :=
  fromOracleKeeping [
    "Ajani Unrelenting",
    "{4}{R}{R}",
    "Legendary Planeswalker — Ajani",
    "Whenever you activate a loyalty ability, create a 2/2 colorless Wizard Soldier creature token named Cadet.",
    "+1: Creatures you control get +1/+0 and gain haste until end of turn.",
    "−2: Discard your hand, then draw a card for each creature you control.",
    "−3: Ajani deals 4 damage to each creature except for tokens you control.",
    "Loyalty: 5"
  ]

def arniRenownedChampion : CardDef :=
  fromOracleKeeping [
    "Arni, Renowned Champion",
    "{3}{R}",
    "Legendary Creature — Human Berserker",
    "1/5",
    "Trample",
    "Whenever another creature you control enters, Arni gets +X/+0 until end of turn, where X is that creature's power."
  ]

def chandraTorchOfDefiance : CardDef :=
  fromOracleKeeping [
    "Chandra, Torch of Defiance",
    "{2}{R}{R}",
    "Legendary Planeswalker — Chandra",
    "+1: Exile the top card of your library. You may cast that card. If you don't, Chandra deals 2 damage to each opponent.",
    "+1: Add {R}{R}.",
    "−3: Chandra deals 4 damage to target creature.",
    "−7: You get an emblem with \"Whenever you cast a spell, this emblem deals 5 damage to any target.\"",
    "Loyalty: 4"
  ]

def galliaTheMerrymaker : CardDef :=
  fromOracleKeeping [
    "Gallia, the Merrymaker",
    "{1}{R}",
    "Legendary Creature — Satyr",
    "2/1",
    "Haste",
    "Each other creature you control with a +1/+1 counter on it has haste.",
    "{1}{R}, {T}: Put a +1/+1 counter on target creature that entered this turn."
  ]

def jiangYangguAlone : CardDef :=
  fromOracleKeeping [
    "Jiang Yanggu, Alone",
    "{4}{R}",
    "Legendary Creature — Human Berserker",
    "4/4",
    "Menace (This creature can't be blocked except by two or more creatures.)",
    "Whenever a creature you control attacks a player alone, discard a card, then draw a card. Then put a +1/+1 counter on that creature for each card you've discarded this turn."
  ]

def kioraOfFireAndAshes : CardDef :=
  fromOracleKeeping [
    "Kiora of Fire and Ashes",
    "{4}{R}{R}",
    "Legendary Creature — Merfolk Noble",
    "2/2",
    "When Kiora enters, create a 5/5 red Dragon creature token with flying.",
    "{8}: Create a 5/5 red Dragon creature token with flying."
  ]

def kothTheGeomancer : CardDef :=
  fromOracleKeeping [
    "Koth, the Geomancer",
    "{2}{R}",
    "Legendary Creature — Human Warrior",
    "3/2",
    "Reach",
    "Landfall — Whenever a land you control enters, Koth deals 1 damage to each opponent. If that land is a Mountain, add {R}."
  ]

def marwynTheClearcutter : CardDef :=
  fromOracleKeeping [
    "Marwyn, the Clearcutter",
    "{R}",
    "Legendary Creature — Elf Warrior",
    "2/1",
    "{2}, {T}, Sacrifice an artifact or land: Draw a card."
  ]

def piaDeterminedRebuilder : CardDef :=
  fromOracleKeeping [
    "Pia, Determined Rebuilder",
    "{2}{R}",
    "Legendary Creature — Human Artificer",
    "2/2",
    "When Pia enters, create a 1/1 colorless Thopter artifact creature token with flying.",
    "{5}{R}: Target creature gets +X/+0 until end of turn, where X is the number of artifacts you control."
  ]

def samutHazoretsChampion : CardDef :=
  fromOracleKeeping [
    "Samut, Hazoret's Champion",
    "{1}{R}",
    "Legendary Creature — Human Warrior Cleric",
    "2/2",
    "Creatures you control have haste."
  ]

def tetsukoUmezawaPursuer : CardDef :=
  fromOracleKeeping [
    "Tetsuko Umezawa, Pursuer",
    "{3}{R}",
    "Legendary Creature — Human Mercenary",
    "2/4",
    "Double strike",
    "Prowess (Whenever you cast a noncreature spell, this creature gets +1/+1 until end of turn.)",
    "Whenever a creature an opponent controls with power or toughness 1 or less blocks, Tetsuko Umezawa deals 1 damage to that creature's controller."
  ]

def tomikIzzetSparkmage : CardDef :=
  fromOracleKeeping [
    "Tomik, Izzet Sparkmage",
    "{1}{R}",
    "Legendary Creature — Human Wizard",
    "1/2",
    "Prowess (Whenever you cast a noncreature spell, this creature gets +1/+1 until end of turn.)",
    "If a source you control would deal noncombat damage to an opponent or a permanent an opponent controls, it deals that much damage plus 1 instead."
  ]

def wayOfThePyromancer : CardDef :=
  fromOracleKeeping [
    "Way of the Pyromancer",
    "{1}{R}",
    "Legendary Enchantment",
    "When Way of the Pyromancer enters, empower Jace 2. (Put two loyalty counters on a Jace token you control. If you don't control one, first create a blue Jace planeswalker token with \"[−1]: Surveil 1\" and \"[−3]: Draw a card.\")",
    "Planeswalkers you control have \"[+1]: Add {R}.\""
  ]

def wayOfTheWarlord : CardDef :=
  fromOracleKeeping [
    "Way of the Warlord",
    "{2}{R}",
    "Legendary Enchantment",
    "When Way of the Warlord enters, empower Jace 5. (Put five loyalty counters on a Jace token you control. If you don't control one, first create a blue Jace planeswalker token with \"[−1]: Surveil 1\" and \"[−3]: Draw a card.\")",
    "Planeswalkers you control have \"[−4]: This planeswalker deals 2 damage to up to one target creature or planeswalker and 2 damage to target player.\""
  ]

def winterTeamPlayer : CardDef :=
  fromOracleKeeping [
    "Winter, Team Player",
    "{4}{R}",
    "Legendary Creature — Human Warrior",
    "3/3",
    "Convoke (Your creatures can help cast this spell. Each creature you tap while casting this spell pays for {1} or one mana of that creature's color.)",
    "Whenever you cast a noncreature spell, creatures you control get +1/+0 until end of turn."
  ]

def edgarMoonlitSovereign : CardDef :=
  fromOracleKeeping [
    "Edgar, Moonlit Sovereign",
    "{3}{G}{G}",
    "Legendary Creature — Werewolf Noble",
    "4/4",
    "Flash",
    "At the beginning of your end step, if you didn't cast a spell this turn, put two +1/+1 counters on Edgar.",
    "{4}{G}: Put a +1/+1 counter on each creature you control with a +1/+1 counter on it."
  ]

def fblthpKnowsTheWay : CardDef :=
  fromOracleKeeping [
    "Fblthp, Knows the Way",
    "{X}{G}{G}",
    "Legendary Creature — Homunculus Scout",
    "*/2",
    "Domain — Fblthp's power is equal to the number of basic land types among lands you control.",
    "When Fblthp enters, search your library for up to X basic land cards with different names, reveal them, put them into your hand, then shuffle."
  ]

def garrukCurseBreaker : CardDef :=
  fromOracleKeeping [
    "Garruk, Curse Breaker",
    "{3}{G}{G}",
    "Legendary Planeswalker — Garruk",
    "Whenever a creature you control with power 4 or greater enters, draw a card.",
    "+2: Untap up to two target lands.",
    "−3: Create a 4/4 green Beast creature token with trample.",
    "−4: Until your next turn, whenever one or more creatures attack one of your opponents, those creatures get +2/+2 and gain trample until end of turn.",
    "Loyalty: 5"
  ]

def ghaltaTheUnstoppable : CardDef :=
  fromOracleKeeping [
    "Ghalta the Unstoppable",
    "{8}{G}",
    "Legendary Creature — Elder Dinosaur",
    "8/8",
    "This spell costs {X} less to cast, where X is the greatest power among creatures you control.",
    "Trample",
    "Other creatures you control have trample."
  ]

def jiangYangguNeverAlone : CardDef :=
  fromOracleKeeping [
    "Jiang Yanggu, Never Alone",
    "{3}{G}",
    "Legendary Creature — Human Druid",
    "2/2",
    "When Jiang Yanggu enters, create Mowu, a legendary 3/3 green Dog creature token.",
    "At the beginning of your end step, untap all tokens you control."
  ]

def lootTheNexus : CardDef :=
  fromOracleKeeping [
    "Loot, the Nexus",
    "{2}{G}",
    "Legendary Creature — Beast Noble",
    "2/1",
    "{T}: Choose a color. Add one mana of that color for each different power among creatures you control."
  ]

def marwynThePreserver : CardDef :=
  fromOracleKeeping [
    "Marwyn, the Preserver",
    "{1}{G}",
    "Legendary Creature — Elf Druid",
    "3/2",
    "Lands you control have hexproof. (They can't be the targets of spells or abilities your opponents control.)",
    "{2}: Return target land card from your graveyard to your hand."
  ]

def piaAetherAscetic : CardDef :=
  fromOracleKeeping [
    "Pia, Aether Ascetic",
    "{2}{G}",
    "Legendary Creature — Human Druid",
    "2/2",
    "When Pia enters, you may discard a card. If you do, search your library for an enchantment card, reveal it, put it into your hand, then shuffle."
  ]

def ruricTharMagecrusher : CardDef :=
  fromOracleKeeping [
    "Ruric Thar, Magecrusher",
    "{5}{G}{G}",
    "Legendary Creature — Ogre Warrior",
    "7/7",
    "This spell can't be countered.",
    "Reach, vigilance, trample",
    "Ruric Thar has hexproof as long as they haven't dealt combat damage yet. (They can't be the target of spells or abilities your opponents control.)"
  ]

def titanbonesToweringHeart : CardDef :=
  fromOracleKeeping [
    "Titanbones, Towering Heart",
    "{3}{G}",
    "Legendary Creature — Skeleton Druid",
    "4/3",
    "Reach",
    "Whenever you gain life, put two +1/+1 counters on Titanbones.",
    "When you discard this card, you gain 3 life."
  ]

def wayOfTheParadox : CardDef :=
  fromOracleKeeping [
    "Way of the Paradox",
    "{2}{G}",
    "Legendary Enchantment",
    "When Way of the Paradox enters, empower Jace 5. (Put five loyalty counters on a Jace token you control. If you don't control one, first create a blue Jace planeswalker token with \"[−1]: Surveil 1\" and \"[−3]: Draw a card.\")",
    "Whenever you activate a loyalty ability, you gain 1 life. You may play an additional land this turn."
  ]

def wayOfTheWildspeaker : CardDef :=
  fromOracleKeeping [
    "Way of the Wildspeaker",
    "{4}{G}",
    "Legendary Enchantment",
    "When Way of the Wildspeaker enters, empower Jace 7. (Put seven loyalty counters on a Jace token you control. If you don't control one, first create a blue Jace planeswalker token with \"[−1]: Surveil 1\" and \"[−3]: Draw a card.\")",
    "Planeswalkers you control have \"[−4]: Create a 4/4 green Beast creature token with trample.\""
  ]

def yoshimaruScrappyStray : CardDef :=
  fromOracleKeeping [
    "Yoshimaru, Scrappy Stray",
    "{1}{G}",
    "Legendary Creature — Dog",
    "1/1",
    "When Yoshimaru enters, another target creature you control fights up to one target creature an opponent controls. (Each deals damage equal to its power to the other.)",
    "{6}: Put a +1/+1 counter on target nonlegendary creature."
  ]

def edgarAncientBloodlord : CardDef :=
  fromOracleKeeping [
    "Edgar, Ancient Bloodlord",
    "{W}{B}",
    "Legendary Creature — Vampire Noble",
    "2/3",
    "Whenever another creature or planeswalker you control dies, you gain 1 life.",
    "{2}, Sacrifice another creature or planeswalker: Put a +1/+1 counter on Edgar. He gains menace until end of turn. (He can't be blocked except by two or more creatures.)"
  ]

def hapatraTheDesertFang : CardDef :=
  fromOracleKeeping [
    "Hapatra, the Desert Fang",
    "{2}{B}{B}{G}",
    "Legendary Creature — Human Cleric",
    "3/3",
    "When Hapatra enters, for each opponent, put X -1/-1 counters on up to one target creature that player controls, where X is the greatest mana value among cards in your graveyard."
  ]

def karnGildedGuardian : CardDef :=
  fromOracleKeeping [
    "Karn, Gilded Guardian",
    "{2/W}{2/U}{2/B}{2/R}{2/G}",
    "Legendary Artifact Creature — Golem",
    "5/5",
    "Vigilance, trample",
    "When Karn enters, draw a card for each color among other artifacts you control."
  ]

def kioraOfSaltAndSand : CardDef :=
  fromOracleKeeping [
    "Kiora of Salt and Sand",
    "{1}{G}{U}",
    "Legendary Creature — Merfolk Noble",
    "2/4",
    "Whenever you attack, if you've activated a loyalty ability this turn, untap target attacking creature. It can't be blocked this turn.",
    "Planeswalkers you control have \"[−8]: Create an 8/8 blue Leviathan creature token with hexproof.\""
  ]

def mabelValleyHero : CardDef :=
  fromOracleKeeping [
    "Mabel, Valley Hero",
    "{1}{R}{W}",
    "Legendary Creature — Mouse Soldier",
    "1/2",
    "Whenever Mabel or another creature you control enters, put a +1/+1 counter on target creature that entered this turn."
  ]

def saheeliJewelOfAvishkar : CardDef :=
  fromOracleKeeping [
    "Saheeli, Jewel of Avishkar",
    "{2}{U}{R}",
    "Legendary Creature — Human Artificer",
    "2/4",
    "Thopters you control have haste.",
    "Whenever you cast a noncreature spell, create a 1/1 colorless Thopter artifact creature token with flying."
  ]

def tamThePossibility : CardDef :=
  fromOracleKeeping [
    "Tam, the Possibility",
    "{1}{G}{U}",
    "Legendary Creature — Gorgon Wizard",
    "2/4",
    "Planeswalker spells you cast cost {1} less to cast.",
    "{W}{U}{B}{R}{G}, {T}: Proliferate X times, where X is the number of planeswalker types among planeswalkers you control. (To proliferate, choose any number of permanents and/or players, then give each another counter of each kind already there.)"
  ]

def vraskaSoulOfStone : CardDef :=
  fromOracleKeeping [
    "Vraska, Soul of Stone",
    "{U}{R}{W}",
    "Legendary Creature — Gorgon Wizard",
    "3/3",
    "Artifact creatures you control have vigilance.",
    "Whenever you cast a noncreature spell, create a 1/1 colorless Sculpture Treasure artifact creature token with \"{T}, Sacrifice this token: Add one mana of any color.\""
  ]

def vraskaTheCuttingGlare : CardDef :=
  fromOracleKeeping [
    "Vraska, the Cutting Glare",
    "{B}{B}{G}",
    "Legendary Creature — Gorgon Assassin",
    "4/4",
    "Deathtouch",
    "When Vraska enters, if you control six or more lands, destroy target permanent an opponent controls. They create a Treasure token. (It's an artifact with \"{T}, Sacrifice this token: Add one mana of any color.\")"
  ]

def karnArgentDefender : CardDef :=
  fromOracleKeeping [
    "Karn, Argent Defender",
    "{2}",
    "Legendary Artifact Creature — Golem",
    "1/3",
    "Artifacts and creatures entering the battlefield don't cause abilities to trigger."
  ]

def traxosScourgeEternal : CardDef :=
  fromOracleKeeping [
    "Traxos, Scourge Eternal",
    "{4}",
    "Legendary Artifact Creature — Dragon Construct",
    "5/4",
    "Trample",
    "Traxos doesn't untap during your untap step.",
    "Whenever you cast an artifact or creature spell, untap Traxos."
  ]

def realityFracturePlains : CardDef :=
  fromOracleKeeping [
    "Plains",
    "Basic Land — Plains",
    "({T}: Add {W}.)"
  ]

def realityFractureIsland : CardDef :=
  fromOracleKeeping [
    "Island",
    "Basic Land — Island",
    "({T}: Add {U}.)"
  ]

def realityFractureSwamp : CardDef :=
  fromOracleKeeping [
    "Swamp",
    "Basic Land — Swamp",
    "({T}: Add {B}.)"
  ]

def realityFractureMountain : CardDef :=
  fromOracleKeeping [
    "Mountain",
    "Basic Land — Mountain",
    "({T}: Add {R}.)"
  ]

def realityFractureForest : CardDef :=
  fromOracleKeeping [
    "Forest",
    "Basic Land — Forest",
    "({T}: Add {G}.)"
  ]

@[irreducible, noinline] def realityFractureCards : Array CardDef := #[
  emrakulTheExigentDoom,
  academicAscent,
  blossomBlessedAngel,
  campusCrier,
  enlightenedConfidant,
  fateshaperAspirant,
  flickeringHound,
  generousRevival,
  germinateRecruits,
  graftSurgeon,
  guidingHydra,
  hexhavenBattalion,
  kindredJudgment,
  loyalTutor,
  memoryTrap,
  predictivePreparations,
  prophesiedEnd,
  refuteDestiny,
  repurposedEnforcer,
  returnToTheLightRealms,
  shatterwingPegasus,
  surgicalPrecision,
  unflinchingHortimancer,
  yourFateEndsHere,
  countersculpt,
  cruelCalculations,
  cryotheoryAdept,
  divinerOfVictory,
  diviningDuelist,
  icyReception,
  infiniteCoursework,
  jacesMachinations,
  mindseekerOculus,
  perfectedTheory,
  planForAllOutcomes,
  preciseRedaction,
  protegesAwakening,
  seasonedCryomancer,
  semesterForeseer,
  sphinxOfFalseConclusions,
  sphinxsApproach,
  surveillancePhantasm,
  theTheoristJaceBeleren,
  theoristsProxy,
  undulatingWitness,
  unsummon,
  variableChaser,
  apexWitchstalker,
  bloodlineRecollector,
  breakUnderPressure,
  castAwayDoubt,
  darkMatterManipulator,
  darklightPhoenix,
  extendedAbsence,
  extrapolateTheImpossible,
  lastGasp,
  lichsRelic,
  multiplyByZero,
  overwriteTheMultiverse,
  rampartHunter,
  rankRat,
  rewriteRegrets,
  riseOfTheDeathbringer,
  sanctumLurker,
  screechingSoulbreaker,
  silenceTheEcho,
  solveForDisappointment,
  terminalCriticism,
  theoreticalNecromancer,
  voidExtrapolator,
  vraskasFinalMercy,
  ajanisAnguish,
  artifistAcumen,
  awakenTheInferno,
  realityFractureBlazingCrescendo,
  chandrasEmberling,
  commandTheStage,
  craterclawColossus,
  curseMarredDemon,
  draconicVisitor,
  eardrumRattler,
  essenceBurn,
  faceYourself,
  fulminousForte,
  hallwayHeckler,
  heartstringPuller,
  identityEcho,
  masterOfBarbs,
  noAdmittance,
  pompousBattlemage,
  pyreRhymer,
  skilledBattlecarver,
  stingcasterMage,
  tetherTechnician,
  violentEchoes,
  wrathOfTheBloodmane,
  arcaneAmphisbaena,
  bestialIncursion,
  buddingInsurgent,
  carnivorousCultivator,
  compelBrutality,
  flourishingGrapple,
  gardenize,
  greenhousePropagator,
  heartwoodCrafter,
  hexhavenInvigorator,
  hungeringPuppetbeast,
  huntersAxe,
  inspiredTethermage,
  omnipresence,
  puppetCrafting,
  restoreWithEmpathy,
  simulacrumShaper,
  somethingWorthSaving,
  sureshotSower,
  tarmogoyf,
  tethermagesAdvantage,
  verdantKraken,
  vinelasherAdept,
  wreckingGecko,
  aeridKonstrari,
  avatarOfBurgeoningEchoes,
  blessedGhoul,
  bloombrute,
  chargeTheSanctum,
  clashOfElements,
  craftworkCrusher,
  denziloreFatehold,
  desperateFuturescribe,
  emergencyPhytomedic,
  entrustTheSpark,
  fateholdCharm,
  fateholdChronologist,
  ferocityOfTheHunt,
  frostbitePyromental,
  grimRepriser,
  ingrisStingerquill,
  konstrariCharm,
  konstrariImproviser,
  kwiaVigorbloom,
  mindMeanderer,
  nullSummoner,
  paradoxShaper,
  primalWitchstalker,
  proctorOfPotential,
  prudentFateseer,
  recursiveRecruitment,
  solariumSentry,
  solitaryCell,
  stingerquillCharm,
  stingerquillVoxmancer,
  stingingVitriol,
  tamsResistance,
  tenuredTethermage,
  theorixCharm,
  theorixMetamage,
  twinnedVision,
  twistedFates,
  uldarosTheorix,
  vigorbloomCharm,
  vigorbloomVanguard,
  vindictiveTriumph,
  warriorsBlades,
  whiplashWordsmith,
  woodworkProdigy,
  afterthoughtSentry,
  archiveArbiter,
  codieRavenousCodex,
  theEchoverseFulcrum,
  eyeOfJace,
  keeperOfTheQuietHour,
  livingLibrary,
  medicsKitesail,
  murmuringVolume,
  dedicatedCommons,
  desertedBeach,
  fateholdAnnex,
  formidableCommons,
  hallOfEchoes,
  hauntedRidge,
  hexhavenDuelingArena,
  innovativeCommons,
  konstrariAnnex,
  meticulousCommons,
  overgrownFarmland,
  rockfallVale,
  roilingCanopy,
  roomOfRefuge,
  shipwreckMarsh,
  stingerquillAnnex,
  theoristsSanctum,
  theorixAnnex,
  transformativeCommons,
  vigorbloomAnnex,
  ajaniResolute,
  danithaSwordOfHope,
  ghaltaTheImmovable,
  gideonsMemorial,
  kothOfTheHomestead,
  lilianaTheFaultless,
  lyraArchangelOfDawn,
  rescueGirlFirstResponder,
  saheeliConsulOfOversight,
  teyoLightshieldExpert,
  thaliaTheSurvivor,
  tomikOrzhovLawmage,
  wayOfTheHealer,
  wayOfTheMentor,
  yoshimaruBelovedCompanion,
  yurikoBladeOfTheMighty,
  arniHumbleScribe,
  chandraChillOfCompliance,
  fblthpImpossiblyLost,
  geistOfSaintThalia,
  hapatraTheDesertFrost,
  jaceRealitySculptor,
  lyraTolarianArchangel,
  proftConsultingDetective,
  ruricTharBiomagus,
  samutTyrantOfNaktamun,
  tetsukoUmezawaFugitive,
  traxosAcademyGuardian,
  wayOfTheCryomancer,
  wayOfTheMindSculptor,
  yargleGoliathOfOtaria,
  yurikoHopeFromTheShadows,
  danithaSpearOfAgony,
  galliaTragicHost,
  garrukVeiledButcher,
  gideonTheOathless,
  lilianaTheRepentant,
  lootTheAnomaly,
  mabelBitterRecluse,
  massacreGirlMostWanted,
  proftSinisterMastermind,
  teyoDiamondbladeMage,
  tinybonesPocketNuisance,
  wayOfTheDeathbringer,
  wayOfTheNecromancer,
  winterTormentedLoner,
  yargleGluttonOfUrborg,
  ajaniUnrelenting,
  arniRenownedChampion,
  chandraTorchOfDefiance,
  galliaTheMerrymaker,
  jiangYangguAlone,
  kioraOfFireAndAshes,
  kothTheGeomancer,
  marwynTheClearcutter,
  piaDeterminedRebuilder,
  samutHazoretsChampion,
  tetsukoUmezawaPursuer,
  tomikIzzetSparkmage,
  wayOfThePyromancer,
  wayOfTheWarlord,
  winterTeamPlayer,
  edgarMoonlitSovereign,
  fblthpKnowsTheWay,
  garrukCurseBreaker,
  ghaltaTheUnstoppable,
  jiangYangguNeverAlone,
  lootTheNexus,
  marwynThePreserver,
  piaAetherAscetic,
  ruricTharMagecrusher,
  titanbonesToweringHeart,
  wayOfTheParadox,
  wayOfTheWildspeaker,
  yoshimaruScrappyStray,
  edgarAncientBloodlord,
  hapatraTheDesertFang,
  karnGildedGuardian,
  kioraOfSaltAndSand,
  mabelValleyHero,
  saheeliJewelOfAvishkar,
  tamThePossibility,
  vraskaSoulOfStone,
  vraskaTheCuttingGlare,
  karnArgentDefender,
  traxosScourgeEternal,
  realityFracturePlains,
  realityFractureIsland,
  realityFractureSwamp,
  realityFractureMountain,
  realityFractureForest
]

#guard realityFractureCards.size == 285
#guard realityFractureCards.any (fun c =>
  c.name == "Academic Ascent" && c.empowerJace == some 2)
#guard realityFractureCards.any (fun c =>
  c.name == "Blossom-Blessed Angel" && c.entersPrepared &&
    c.prepareFace.any (fun a => a.name == "Seed Suture"))
#guard realityFractureCards.any (fun c =>
  c.name == "Countersculpt" && c.additionalCostBeholdOrPay == some ("Jace", 1))

end Mtg.Engine.Catalog
