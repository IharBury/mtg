import Mtg.Engine.Catalog
import Mtg.Engine.Card
import Mtg.Engine.Mana

/-!
# The Hobbit (HOB / HOC) catalog beyond Welcome Decks

Cards from The Hobbit and The Hobbit Eternal that are not in the five
Welcome Decks. Oracle text is stored verbatim from Scryfall; modeled
fields must reconstruct it.
-/

namespace Mtg.Engine.Catalog.HobbitSet

open Mtg.Engine
open Mtg.Engine.Catalog

def ordinaryBear : CardDef :=
  creature "Ordinary Bear" (ManaCost.ofGenericAndColor 3 .green) #["Bear"] 4 5

def largeBear : CardDef :=
  creature "Large Bear" (ManaCost.ofGenericAndHybrids 3 .black .green 2) #["Bear"] 5 5
    (oracleText := "Reach, trample, haste")
    (keywords := Keyword.reach.merge Keyword.trample |>.merge Keyword.haste)

def littleBear : CardDef :=
  creature "Little Bear" (ManaCost.ofGenericAndColor 2 .green) #["Bear"] 3 2
    (oracleText := "Flash\nWhen this creature enters, untap another target creature you control. If that creature is a Bear, put a +1/+1 counter on it.")
    (keywords := Keyword.flash)
    (triggeredAbilities := #[.onEnterUntapOtherPlusOneIfSubtype "Bear"])

def elvenkingsHarper : CardDef :=
  creature "Elvenking's Harper" (ManaCost.ofGenericAndColor 1 .blue) #["Elf", "Bard"] 2 2
    (oracleText := "{4}{U}: Target creature can't be blocked this turn.")
    (activatedAbilities := #[
      activated .targetCantBeBlockedThisTurn (ManaCost.ofGenericAndColor 4 .blue)])

def smaugsFury : CardDef :=
  instant "Smaug's Fury" (ManaCost.ofGenericAndColor 1 .red)
    "Target creature gets +3/+0 and gains reach and first strike until end of turn."
    (some (.pumpAndGrantKeywords 3 0 (Keyword.reach.merge Keyword.firstStrike)))

def wellWornSpatula : CardDef :=
  artifact "Well-Worn Spatula" (ManaCost.ofGeneric 1)
    "When this Equipment enters, you gain 2 life.\nEquipped creature gets +1/+1.\nEquip {1} ({1}: Attach to target creature you control. Equip only as a sorcery.)"
    (subtypes := #["Equipment"])
    (triggeredAbilities := #[.onEnterGainLife 2])
    (staticAbilities := #[.equippedCreatureGets 1 1])
    (activatedAbilities := #[equipAbility (ManaCost.ofGeneric 1)])

/-- Dual land: enters tapped; `{T}: Add {A} or {B}`; tap, pay, and sacrifice
for two +1/+1 counters on a typed creature you control. -/
def hobbitDualLand (name : String) (a b : Color) (creatureType : String)
    (oracleText : String) : CardDef :=
  land name oracleText
    (entersTapped := true)
    (tapAddOneOf := #[.colored a, .colored b])
    (activatedAbilities := #[
      activated (.plusOneOnTargetSubtype 2 creatureType)
        (ManaCost.ofGenericAndColors 2 [a, b])
        (tap := true) (sacrificeSource := true) (onlyAsSorcery := true)])

def elvenkingsHalls : CardDef :=
  hobbitDualLand "Elvenking's Halls" .green .blue "Elf"
    "This land enters tapped.\n{T}: Add {G} or {U}.\n{2}{G}{U}, {T}, Sacrifice this land: Put two +1/+1 counters on target Elf you control. Activate only as a sorcery."

def ironHills : CardDef :=
  hobbitDualLand "Iron Hills" .red .white "Dwarf"
    "This land enters tapped.\n{T}: Add {R} or {W}.\n{2}{R}{W}, {T}, Sacrifice this land: Put two +1/+1 counters on target Dwarf you control. Activate only as a sorcery."

def lakeTown : CardDef :=
  hobbitDualLand "Lake-town" .white .blue "Human"
    "This land enters tapped.\n{T}: Add {W} or {U}.\n{2}{W}{U}, {T}, Sacrifice this land: Put two +1/+1 counters on target Human you control. Activate only as a sorcery."

def goblinTown : CardDef :=
  land "Goblin-town"
    "This land enters tapped.\n{T}: Add {B} or {R}.\n{2}{B}{R}, {T}, Sacrifice this land: Put two +1/+1 counters on target Goblin or Orc you control. Activate only as a sorcery."
    (entersTapped := true)
    (tapAddOneOf := #[.colored .black, .colored .red])
    (activatedAbilities := #[
      activated (.plusOneOnTargetAnySubtype 2 #["Goblin", "Orc"])
        (ManaCost.ofGenericAndColors 2 [.black, .red])
        (tap := true) (sacrificeSource := true) (onlyAsSorcery := true)])

def mirkwood : CardDef :=
  land "Mirkwood"
    "This land enters tapped.\n{T}: Add {B} or {G}.\n{2}{B}{G}, {T}, Sacrifice this land: Put two +1/+1 counters on target Bear, Spider, or Wolf you control. Activate only as a sorcery."
    (entersTapped := true)
    (tapAddOneOf := #[.colored .black, .colored .green])
    (activatedAbilities := #[
      activated (.plusOneOnTargetAnySubtype 2 #["Bear", "Spider", "Wolf"])
        (ManaCost.ofGenericAndColors 2 [.black, .green])
        (tap := true) (sacrificeSource := true) (onlyAsSorcery := true)])

def hobbitHole : CardDef :=
  land "Hobbit Hole"
    "{T}, Sacrifice this land: Search your library for a basic land card, put it onto the battlefield tapped, then shuffle.\nHalflingcycling {4} ({4}, Discard this card: Search your library for a Halfling card, reveal it, put it into your hand, then shuffle.)"
    (activatedAbilities := #[
      activated .searchBasicLandTapped (tap := true) (sacrificeSource := true),
      typecyclingAbility "Halfling" (ManaCost.ofGeneric 4)])

def nighthowlPursuer : CardDef :=
  creature "Nighthowl Pursuer" (ManaCost.ofColor .black) #["Wolf"] 1 1
    (oracleText := "Menace (This creature can't be blocked except by two or more creatures.)\nFerocious — Whenever this creature attacks while you control a creature with power 4 or greater, this creature gets +2/+2 until end of turn.")
    (keywords := Keyword.menace)
    (triggeredAbilities := #[.onAttackFerociousSourceGets 2 2])

def wargling : CardDef :=
  creature "Wargling" (ManaCost.ofGenericAndColor 1 .green) #["Wolf"] 2 2
    (oracleText := "Ferocious — Whenever this creature attacks while you control a creature with power 4 or greater, until end of turn, this creature gets +1/+0 and creatures you control gain trample.")
    (triggeredAbilities := #[.onAttackFerociousSourceGetsAndTeamTrample 1])

def wilderlandScrounger : CardDef :=
  creature "Wilderland Scrounger" (ManaCost.ofGenericAndColor 4 .green) #["Wolf"] 3 6
    (oracleText := "Ferocious — Whenever this creature attacks while you control a creature with power 4 or greater, put a +1/+1 counter on each creature you control.")
    (triggeredAbilities := #[.onAttackFerociousPlusOneEach])

def nastyLittleRabbit : CardDef :=
  creature "Nasty Little Rabbit" (ManaCost.ofColor .green) #["Rabbit"] 1 2
    (oracleText := "Ferocious — At the beginning of combat on your turn, if you control a creature with power 4 or greater, put a +1/+1 counter on this creature.")
    (triggeredAbilities := #[.onYourBeginCombatFerociousPlusOne])

def theChiefWarg : CardDef :=
  legendaryCreature "The Chief Warg" (ManaCost.ofGenericAndColors 2 [.black, .green])
    #["Wolf"] 3 3
    (oracleText := "Menace (This creature can't be blocked except by two or more creatures.)\nFerocious — Whenever you attack while you control a creature with power 4 or greater, you draw a card and lose 1 life.")
    (keywords := Keyword.menace)
    (triggeredAbilities := #[.onYouAttackFerociousDrawLoseLife])

def bardHeirOfGirion : CardDef :=
  legendaryCreature "Bard, Heir of Girion" (ManaCost.ofGenericAndColors 2 [.white, .blue])
    #["Human", "Archer"] 4 4
    (oracleText := "Reach, vigilance\nOther creatures you control get +1/+1.\nWhenever you attack, draw a card.")
    (keywords := Keyword.reach.merge Keyword.vigilance)
    (staticAbilities := #[.otherCreaturesGet #[] 1 1])
    (triggeredAbilities := #[.onYouAttackDraw])

def reprieve : CardDef :=
  instant "Reprieve" (ManaCost.ofGenericAndColor 1 .white)
    "Return target spell to its owner's hand.\nDraw a card."
    (some .returnSpellDraw)

def thorinsLastStand : CardDef :=
  instant "Thorin's Last Stand" (ManaCost.ofGenericAndColors 2 [.white, .white])
    "Choose one —\n• Creatures you control get +2/+1 until end of turn.\n• Destroy target artifact or enchantment. You gain 2 life."
    (spellModes := #[.creaturesYouControlGet 2 1, .destroyArtifactOrEnchantmentGainLife 2])

def stoneBySunlight : CardDef :=
  instant "Stone by Sunlight" (ManaCost.ofGenericAndColor 1 .white)
    "Choose one —\n• Destroy target creature with power 4 or greater.\n• Until end of turn, target creature becomes an artifact in addition to its other types and gains indestructible. (Damage and effects that say \"destroy\" don't destroy it.)"
    (spellModes := #[.destroyCreaturePowerAtLeast 4, .becomeArtifactGainIndestructible])

def duskwatchHunter : CardDef :=
  creature "Duskwatch Hunter" (ManaCost.ofGenericAndHybrids 2 .black .green 1)
    #["Wolf"] 3 1
    (oracleText := "This creature can't be blocked by tokens.\nWhen this creature enters, put a +1/+1 counter on target creature.")
    (staticAbilities := #[.cantBeBlockedByTokens])
    (triggeredAbilities := #[.onEnterPlusOneOnCreature])

def patientInstructor : CardDef :=
  creature "Patient Instructor" (ManaCost.ofGenericAndHybrids 2 .white .blue 1)
    #["Human", "Citizen"] 2 2
    (oracleText := "Vigilance\nWhen this creature enters, recruit. (Draw a card, then discard a card. If you discarded a nonland card, create a 1/1 white Human Soldier creature token.)")
    (keywords := Keyword.vigilance)
    (triggeredAbilities := #[.onEnterRecruit])

def longLakeNuisance : CardDef :=
  creature "Long Lake Nuisance" (ManaCost.ofGenericAndColor 3 .blue) #["Bird"] 3 1
    (oracleText := "Flying\nWhen this creature enters, recruit. (Draw a card, then discard a card. If you discarded a nonland card, create a 1/1 white Human Soldier creature token.)")
    (keywords := Keyword.flying)
    (triggeredAbilities := #[.onEnterRecruit])

def laketownLookout : CardDef :=
  creature "Lake-town Lookout" (ManaCost.ofColor .white) #["Human", "Scout"] 1 1
    (oracleText := "When this creature dies, recruit. (Draw a card, then discard a card. If you discarded a nonland card, create a 1/1 white Human Soldier creature token.)")
    (triggeredAbilities := #[.onDiesRecruit])

def giantsBoulder : CardDef :=
  artifact "Giant's Boulder" (ManaCost.ofGeneric 1)
    "When this artifact enters, scry 2. (Look at the top two cards of your library, then put any number of them on the bottom and the rest on top in any order.)\n{1}, {T}: Add one mana of any color.\n{7}, {T}, Sacrifice this artifact: Destroy target permanent."
    (triggeredAbilities := #[.onEnterScry 2])
    (activatedAbilities := #[
      activated .addAnyColor (ManaCost.ofGeneric 1) (tap := true),
      activated .destroyTargetPermanent (ManaCost.ofGeneric 7) (tap := true)
        (sacrificeSource := true)])

def longBodiedGreyDog : CardDef :=
  creature "Long-Bodied Grey Dog" (ManaCost.ofGeneric 3) #["Dog"] 2 2
    (oracleText := "Flash\nReach\nWhen this creature enters, create a tapped Treasure token. (It's an artifact with \"{T}, Sacrifice this token: Add one mana of any color.\")")
    (keywords := Keyword.flash.merge Keyword.reach)
    (triggeredAbilities := #[.onEnterCreateTreasureTapped])

def doriBearerOfFriends : CardDef :=
  legendaryCreature "Dori, Bearer of Friends" (ManaCost.ofGenericAndColor 2 .red)
    #["Dwarf", "Warrior"] 3 2
    (oracleText := "Trample\nWhen Dori enters, create a Treasure token. (It's an artifact with \"{T}, Sacrifice this token: Add one mana of any color.\")")
    (keywords := Keyword.trample)
    (triggeredAbilities := #[.onEnterCreateTreasure])

def esgarothGarrison : CardDef :=
  card "Esgaroth Garrison" #[.creature] (ManaCost.ofGenericAndColor 4 .white)
    #["Human", "Soldier"]
    "Esgaroth Garrison's power is equal to the number of creatures you control.\nWhen this creature enters, recruit. (Draw a card, then discard a card. If you discarded a nonland card, create a 1/1 white Human Soldier creature token.)"
    (toughness := some 5)
    (staticAbilities := #[.powerEqualCreaturesYouControl])
    (triggeredAbilities := #[.onEnterRecruit])

def gundabadOpportunist : CardDef :=
  creature "Gundabad Opportunist" (ManaCost.ofGenericAndColor 3 .red)
    #["Goblin", "Rogue"] 4 2
    (oracleText := "When this creature enters, exile the top card of your library. Until the end of your next turn, you may play that card.")
    (triggeredAbilities := #[.onEnterExileTop])

def giganticBigBear : CardDef :=
  creature "Gigantic Big Bear" (ManaCost.ofGenericAndColors 5 [.green, .green])
    #["Bear"] 10 7
    (oracleText := "This spell can't be countered.\nHexproof, haste")
    (keywords := Keyword.hexproof.merge Keyword.haste)
    (cantBeCountered := true)

def bothersomeNoisemaker : CardDef :=
  creature "Bothersome Noisemaker" (ManaCost.ofGenericAndColor 1 .red)
    #["Goblin", "Bard"] 2 2
    (oracleText := "Whenever you cast a noncreature spell, amass Goblins 1. (Put a +1/+1 counter on an Army you control. It's also a Goblin. If you don't control an Army, create a 0/0 black Goblin Army creature token first.)")
    (triggeredAbilities := #[.onCastNoncreatureAmassGoblins 1])

def fearsomeGoblinPair : CardDef :=
  creature "Fearsome Goblin Pair" (ManaCost.ofGenericAndHybrids 2 .black .red 1)
    #["Goblin", "Soldier"] 1 1
    (oracleText := "When this creature dies, amass Goblins 4. (Put four +1/+1 counters on an Army you control. It's also a Goblin. If you don't control an Army, create a 0/0 black Goblin Army creature token first.)")
    (triggeredAbilities := #[.onDiesAmassGoblins 4])

def goblinTownFlunkies : CardDef :=
  creature "Goblin-town Flunkies" (ManaCost.ofGenericAndColor 1 .red)
    #["Goblin", "Soldier"] 1 1
    (oracleText := "Haste\nWhen this creature enters, amass Goblins 1. (Put a +1/+1 counter on an Army you control. It's also a Goblin. If you don't control an Army, create a 0/0 black Goblin Army creature token first.)")
    (keywords := Keyword.haste)
    (triggeredAbilities := #[.onEnterAmassGoblins 1])

def mistyMountainsRaider : CardDef :=
  creature "Misty Mountains Raider" (ManaCost.ofGenericAndColor 4 .red)
    #["Goblin", "Soldier"] 4 4
    (oracleText := "Whenever you attack, amass Goblins 2. (Put two +1/+1 counters on an Army you control. It's also a Goblin. If you don't control an Army, create a 0/0 black Goblin Army creature token first.)")
    (triggeredAbilities := #[.onYouAttackAmassGoblins 2])

def greatGoblinFoulHearted : CardDef :=
  legendaryCreature "Great Goblin, Foul-Hearted"
    (ManaCost.ofGenericAndColors 3 [.black, .red]) #["Goblin", "Noble"] 3 3
    (oracleText := "Whenever Great Goblin enters or attacks, amass Goblins 3. (Put three +1/+1 counters on an Army you control. It's also a Goblin. If you don't control an Army, create a 0/0 black Goblin Army creature token first.)\nArmies you control have trample.")
    (staticAbilities := #[.armiesYouControlHaveTrample])
    (triggeredAbilities := #[.onEnterOrAttackAmassGoblins 3])

def bardsCompany : CardDef :=
  creature "Bard's Company" (ManaCost.ofGenericAndColors 2 [.white, .blue])
    #["Human", "Citizen"] 2 3
    (oracleText := "You may cast this spell as though it had flash if you control a Human.\nOther creatures you control get +1/+1.\nWhenever this creature enters or attacks, recruit. (Draw a card, then discard a card. If you discarded a nonland card, create a 1/1 white Human Soldier creature token.)")
    (flashIfYouControlSubtype := some "Human")
    (staticAbilities := #[.otherCreaturesGet #[] 1 1])
    (triggeredAbilities := #[.onEnterOrAttackRecruit])

def dwarvenWarriors : CardDef :=
  creature "Dwarven Warriors" (ManaCost.ofGenericAndColor 2 .red)
    #["Dwarf", "Warrior"] 1 1
    (oracleText := "{T}: Target creature with power 2 or less can't be blocked this turn.")
    (activatedAbilities := #[
      activated (.targetCantBeBlockedPowerAtMost 2) (tap := true)])

def rageIntoTheValley : CardDef :=
  sorcery "Rage into the Valley" (ManaCost.ofGenericAndColor 2 .black)
    "You draw a card and lose 1 life.\nAmass Goblins 2. (Put two +1/+1 counters on an Army you control. It's also a Goblin. If you don't control an Army, create a 0/0 black Goblin Army creature token first.)"
    (some (.drawLoseLifeThenAmass 2))

def gatheringOfDarkness : CardDef :=
  sorcery "Gathering of Darkness" (ManaCost.ofGenericAndColor 3 .black)
    "Return up to one target creature card from your graveyard to your hand.\nAmass Goblins 3. (Put three +1/+1 counters on an Army you control. It's also a Goblin. If you don't control an Army, create a 0/0 black Goblin Army creature token first.)"
    (some (.returnCreatureFromGyThenAmass 3))

def soundTheTrumpets : CardDef :=
  instant "Sound the Trumpets" (ManaCost.ofGenericAndColors 1 [.blue, .blue])
    "Counter target spell. If that spell's mana value was 2 or less, recruit. (Draw a card, then discard a card. If you discarded a nonland card, create a 1/1 white Human Soldier creature token.)"
    (some (.counterThenRecruitIfMvAtMost 2))

def fatefulDiscovery : CardDef :=
  enchantment "Fateful Discovery" (ManaCost.ofGenericAndColors 3 [.blue, .blue])
    "Whenever an artifact you control enters, draw a card."
    (triggeredAbilities := #[.onArtifactYouControlEntersDraw])

def chiefWargsCompany : CardDef :=
  creature "Chief Warg's Company" (ManaCost.ofGenericAndColors 1 [.black, .green])
    #["Wolf"] 5 3
    (oracleText := "Trample\nThis creature can't attack unless you control two or more other Wolves.\nAt the beginning of your upkeep, create a 2/2 green Wolf creature token.")
    (keywords := Keyword.trample)
    (staticAbilities := #[.cantAttackUnlessYouControlNOther 2 "Wolf"])
    (triggeredAbilities := #[.onYourUpkeepCreateTokens .wolf 1])

def dwarvenShortsword : CardDef :=
  artifact "Dwarven Shortsword" (ManaCost.ofGenericAndColor 3 .white)
    "When this Equipment enters, create a 2/2 red Dwarf creature token, then attach this Equipment to it.\nEquipped creature gets +1/+2.\nEquip {2} ({2}: Attach to target creature you control. Equip only as a sorcery.)"
    (subtypes := #["Equipment"])
    (triggeredAbilities := #[.onEnterCreateThenAttach .dwarf])
    (staticAbilities := #[.equippedCreatureGets 1 2])
    (activatedAbilities := #[equipAbility (ManaCost.ofGeneric 2)])

def goblinPlateMail : CardDef :=
  artifact "Goblin Plate Mail" (ManaCost.ofGenericAndHybrids 1 .black .red)
    "When this Equipment enters, amass Goblins 1, then attach this Equipment to the amassed Army. (To amass Goblins 1, put a +1/+1 counter on an Army you control. It's also a Goblin. If you don't control an Army, create a 0/0 black Goblin Army creature token first.)\nEquipped creature gets +1/+0 and has menace.\nEquip {4}"
    (subtypes := #["Equipment"])
    (triggeredAbilities := #[.onEnterAmassThenAttach 1])
    (staticAbilities := #[.equippedCreatureGetsAndHas 1 0 Keyword.menace])
    (activatedAbilities := #[equipAbility (ManaCost.ofGeneric 4)])

def bagEndBanquet : CardDef :=
  artifact "Bag End Banquet" (ManaCost.ofGeneric 6)
    "When this artifact enters, create three Food tokens.\n{T}: Add {C} for each Food you control."
    (triggeredAbilities := #[.onEnterCreateTokens .food 3])
    (tapAddManaForEach := #[⟨.colorless, "Food"⟩])

def floweringOfTheWhiteTree : CardDef :=
  enchantment "Flowering of the White Tree" (ManaCost.ofColors [.white, .white])
    "Legendary creatures you control get +2/+1 and have ward {1}.\nNonlegendary creatures you control get +1/+1."
    (supertypes := #[.legendary])
    (staticAbilities := #[
      .legendaryCreaturesGetAndWard 2 1 1,
      .nonlegendaryCreaturesGet 1 1])

def momentOfGlory : CardDef :=
  sorcery "Moment of Glory" (ManaCost.ofColor .white)
    "Put a +1/+1 counter on target creature you control. If this spell was cast from a graveyard, also put a +1/+1 counter on each other creature you control.\nFlashback {4}{W} (You may cast this card from your graveyard for its flashback cost. Then exile it.)"
    (some .plusOneThenEachOtherIfFromGy)
    (flashback := some (ManaCost.ofGenericAndColor 4 .white))

def plunderTheTrollshaws : CardDef :=
  instant "Plunder the Trollshaws" (ManaCost.ofGenericAndColor 1 .blue)
    "Draw a card. If this spell was cast from a graveyard, draw two cards instead.\nFlashback {3}{U} (You may cast this card from your graveyard for its flashback cost. Then exile it.)"
    (some (.drawIfFromGy 1 2))
    (flashback := some (ManaCost.ofGenericAndColor 3 .blue))

def tidingsOfWar : CardDef :=
  sorcery "Tidings of War" (ManaCost.ofColor .red)
    "Amass Goblins 1. If this spell was cast from a graveyard, amass Goblins 3 instead. (To amass Goblins X, put X +1/+1 counters on an Army you control. It's also a Goblin. If you don't control an Army, create a 0/0 black Goblin Army creature token first.)\nFlashback {3}{R} (You may cast this card from your graveyard for its flashback cost. Then exile it.)"
    (some (.amassGoblinsOrFromGy 1 3))
    (flashback := some (ManaCost.ofGenericAndColor 3 .red))

def eaglesRescue : CardDef :=
  enchantment "Eagle's Rescue" (ManaCost.ofGenericAndHybrids 2 .white .blue 2)
    "Enchant creature\nEnchanted creature gets +2/+2 and has flying.\n{2}{W/U}{W/U}: Return this card from your graveyard to the battlefield attached to target creature you control with power 1 or less. Activate only as a sorcery."
    (subtypes := #["Aura"])
    (staticAbilities := #[.enchantedCreatureGetsAndHas 2 2 Keyword.flying])
    (activatedAbilities := #[
      activated (.returnFromGyAttachPowerAtMost 1)
        (ManaCost.ofGenericAndHybrids 2 .white .blue 2)
        (activateFromGraveyard := true) (onlyAsSorcery := true)])

def gandalfWanderingWizard : CardDef :=
  legendaryCreature "Gandalf, Wandering Wizard" (ManaCost.ofGenericAndColor 4 .blue)
    #["Avatar", "Wizard"] 4 5
    (oracleText := "Ward {3} (Whenever this creature becomes the target of a spell or ability an opponent controls, counter it unless that player pays {3}.)\n{6}: Gandalf's owner shuffles him into their library and draws three cards.")
    (ward := some 3)
    (activatedAbilities := #[
      activated (.ownerShuffleSourceDraw 3) (ManaCost.ofGeneric 6)])

def trollNegotiations : CardDef :=
  sorcery "Troll Negotiations" (ManaCost.ofGenericAndColors 2 [.green, .green])
    "Put two +1/+1 counters on target creature you control. Then it fights target creature an opponent controls. (Each deals damage equal to its power to the other.)"
    (some (.plusOneThenFight 2))

def dwarvenMattock : CardDef :=
  artifact "Dwarven Mattock" (ManaCost.ofGeneric 2)
    "When this Equipment enters, attach it to target Dwarf you control.\nEquipped creature gets +2/+2 and has ward {1}. (Whenever equipped creature becomes the target of a spell or ability an opponent controls, counter it unless that player pays {1}.)\nEquip {3} ({3}: Attach to target creature you control. Equip only as a sorcery.)"
    (subtypes := #["Equipment"])
    (triggeredAbilities := #[.onEnterAttachToSubtype "Dwarf"])
    (staticAbilities := #[.equippedCreatureGetsAndWard 2 2 1])
    (activatedAbilities := #[equipAbility (ManaCost.ofGeneric 3)])

def mithrilCoat : CardDef :=
  artifact "Mithril Coat" (ManaCost.ofGeneric 3)
    "Flash\nIndestructible\nWhen Mithril Coat enters, attach it to target legendary creature you control.\nEquipped creature has indestructible.\nEquip {3}"
    (subtypes := #["Equipment"])
    (supertypes := #[.legendary])
    (keywords := Keyword.flash.merge Keyword.indestructible)
    (triggeredAbilities := #[.onEnterAttachToLegendary])
    (staticAbilities := #[.equippedCreatureHasKeywords Keyword.indestructible])
    (activatedAbilities := #[equipAbility (ManaCost.ofGeneric 3)])

def allCards : Array CardDef := #[
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
  bardHeirOfGirion,
  reprieve,
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
  greatGoblinFoulHearted,
  bardsCompany,
  dwarvenWarriors,
  rageIntoTheValley,
  gatheringOfDarkness,
  soundTheTrumpets,
  fatefulDiscovery,
  chiefWargsCompany,
  dwarvenShortsword,
  goblinPlateMail,
  bagEndBanquet,
  floweringOfTheWhiteTree,
  momentOfGlory,
  plunderTheTrollshaws,
  tidingsOfWar,
  eaglesRescue,
  gandalfWanderingWizard,
  trollNegotiations,
  dwarvenMattock,
  mithrilCoat
]

end Mtg.Engine.Catalog.HobbitSet
