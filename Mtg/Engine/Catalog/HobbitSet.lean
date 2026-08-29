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

def greatUglyLookingGoblin : CardDef :=
  creature "Great Ugly-Looking Goblin" (ManaCost.ofGenericAndColor 5 .black)
    #["Goblin", "Soldier"] 4 4
    (oracleText := "Each creature you control with a +1/+1 counter on it has menace. (It can't be blocked except by two or more creatures.)\n//ADV//\nClap! Snap! {1}{B}\nSorcery — Adventure\nAmass Goblins 2. (Then exile this card. You may cast the creature later from exile.)")
    (staticAbilities := #[.creaturesYouControlWithPlusOneHaveMenace])
    (adventure := some (adventure "Clap! Snap!" (ManaCost.ofGenericAndColor 1 .black)
      "Amass Goblins 2. (Then exile this card. You may cast the creature later from exile.)"
      (.amassGoblins 2)))

def theArkenstone : CardDef :=
  card "The Arkenstone" #[.artifact] (ManaCost.ofGeneric 5)
    (oracleText := "Creatures you control get +1/+1.\nAt the beginning of your end step, draw a card.\n//ADV//\nSeek the Heart {2}{W}\nSorcery — Adventure\nSearch your library for a legendary creature card, reveal it, put it into your hand, then shuffle. (Then exile this card. You may cast the artifact later from exile.)")
    (supertypes := #[.legendary])
    (staticAbilities := #[.creaturesYouControlGet 1 1])
    (triggeredAbilities := #[.onYourEndStepDraw])
    (adventure := some (adventure "Seek the Heart" (ManaCost.ofGenericAndColor 2 .white)
      "Search your library for a legendary creature card, reveal it, put it into your hand, then shuffle. (Then exile this card. You may cast the artifact later from exile.)"
      .searchLegendaryCreatureToHand))

def bolgsCompany : CardDef :=
  creature "Bolg's Company" (ManaCost.ofColors [.black, .red]) #["Goblin", "Soldier"] 2 2
    (oracleText := "This creature has haste as long as you control another Goblin.\n{T}, Sacrifice another Goblin: Add {B}{R}.")
    (staticAbilities := #[.hasteIfYouControlOtherSubtype "Goblin"])
    (activatedAbilities := #[
      activated (.addMana #[.colored .black, .colored .red]) (tap := true)
        (sacrificeAnotherSubtype := some "Goblin")])

def noriTellerOfTales : CardDef :=
  legendaryCreature "Nori, Teller of Tales" (ManaCost.ofGenericAndHybrids 1 .red .white)
    #["Dwarf", "Bard"] 2 2
    (oracleText := "Whenever Nori attacks, target attacking creature gains first strike until end of turn.")
    (triggeredAbilities := #[.onAttackTargetGainsKeywords Keyword.firstStrike])

def theLordOfTheEagles : CardDef :=
  legendaryCreature "The Lord of the Eagles" (ManaCost.ofGenericAndColors 7 [.blue, .blue])
    #["Bird", "Noble"] 8 8
    (oracleText := "Flash\nThis spell costs {X} less to cast, where X is the total power of creatures you control with flying.\nFlying")
    (keywords := Keyword.flash.merge Keyword.flying)
    (costReductionEqualFlyingPower := true)

def throrsMap : CardDef :=
  artifact "Thrór's Map" (ManaCost.ofGeneric 2)
    "When Thrór's Map enters, search your library for a basic land card, reveal it, put it into your hand, then shuffle.\n{2}, {T}: Draw a card, then discard a card."
    (supertypes := #[.legendary])
    (triggeredAbilities := #[.onEnterSearchBasicToHand])
    (activatedAbilities := #[
      activated (.drawThenDiscardN 1) (ManaCost.ofGeneric 2) (tap := true)])

def rivendell : CardDef :=
  legendaryLand "Rivendell"
    "Rivendell enters tapped unless you control a legendary creature.\n{T}: Add {U}.\n{1}{U}, {T}: Scry 2. Activate only if you control a legendary creature."
    (tapAddMana := #[.colored .blue])
    (entersTappedUnlessLegendary := true)
    (activatedAbilities := #[
      activated (.scry 2) (ManaCost.ofGenericAndColor 1 .blue) (tap := true)
        (onlyIfYouControlLegendary := true)])

def delightedHalfling : CardDef :=
  creature "Delighted Halfling" (ManaCost.ofColor .green) #["Halfling", "Citizen"] 1 2
    (oracleText := "{T}: Add {C}.\n{T}: Add one mana of any color. Spend this mana only to cast a legendary spell, and that spell can't be countered.")
    (tapAddMana := #[.colorless])
    (tapAddAnyColorForLegendary := true)

def relicOfSauron : CardDef :=
  artifact "Relic of Sauron" (ManaCost.ofGeneric 4)
    "{T}: Add two mana in any combination of {U}, {B}, and/or {R}.\n{3}, {T}: Draw two cards, then discard a card."
    (tapAddTwoAmong := #[.colored .blue, .colored .black, .colored .red])
    (activatedAbilities := #[
      activated (.drawThenDiscardN 2) (ManaCost.ofGeneric 3) (tap := true)])

def longLostLances : CardDef :=
  artifact "Long-Lost Lances" (ManaCost.ofGeneric 2)
    "Equipped creature gets +2/+0.\nDuring your turn, creatures you control that are equipped have first strike and vigilance.\nEquip {2}"
    (subtypes := #["Equipment"])
    (staticAbilities := #[
      .equippedCreatureGets 2 0,
      .equippedCreaturesHaveKeywordsDuringYourTurn (Keyword.firstStrike.merge Keyword.vigilance)])
    (activatedAbilities := #[equipAbility (ManaCost.ofGeneric 2)])

def theBlackArrow : CardDef :=
  artifact "The Black Arrow" (ManaCost.ofGeneric 3)
    "Flash\nWhen The Black Arrow enters, it deals 1 damage to any target. If a Dragon is dealt damage this way, destroy it.\nEquipped creature gets +1/+1 and has reach.\nEquip {1} ({1}: Attach to target creature you control. Equip only as a sorcery.)"
    (subtypes := #["Equipment"])
    (supertypes := #[.legendary])
    (keywords := Keyword.flash)
    (triggeredAbilities := #[.onEnterDealDamageDestroyIfSubtype 1 "Dragon"])
    (staticAbilities := #[.equippedCreatureGetsAndHas 1 1 Keyword.reach])
    (activatedAbilities := #[equipAbility (ManaCost.ofGeneric 1)])

def smaugTheMagnificent : CardDef :=
  legendaryCreature "Smaug the Magnificent" (ManaCost.ofGenericAndColors 2 [.red, .red])
    #["Dragon"] 4 3
    (oracleText := "Flying, haste\nWhenever Smaug attacks, he deals damage equal to the number of Treasures you control to any target.\nAt the beginning of your upkeep, create a Treasure token.")
    (keywords := Keyword.flying.merge Keyword.haste)
    (triggeredAbilities := #[.onAttackDamageEqualTreasures, .onYourUpkeepCreateTokens .treasure 1])

def theQueenOfDale : CardDef :=
  legendaryCreature "The Queen of Dale" (ManaCost.ofGenericAndColor 1 .white)
    #["Human", "Noble"] 2 1
    (oracleText := "Whenever an opponent casts their first noncreature spell each turn, you recruit. (Draw a card, then discard a card. If you discarded a nonland card, create a 1/1 white Human Soldier creature token.)")
    (triggeredAbilities := #[.onOpponentCastsFirstNoncreatureRecruit])

def lothoCorruptShirriff : CardDef :=
  legendaryCreature "Lotho, Corrupt Shirriff" (ManaCost.ofColors [.white, .black])
    #["Halfling", "Rogue"] 2 1
    (oracleText := "Whenever a player casts their second spell each turn, you lose 1 life and create a Treasure token. (It's an artifact with \"{T}, Sacrifice this token: Add one mana of any color.\")")
    (triggeredAbilities := #[.onPlayerCastsSecondSpellLoseLifeCreateTreasure])

def oriKeeperOfSongs : CardDef :=
  legendaryCreature "Ori, Keeper of Songs" (ManaCost.ofGenericAndColor 2 .white)
    #["Dwarf", "Bard"] 3 3
    (oracleText := "Storied (If you control three or more artifacts, legendaries, and/or Sagas, you have an enduring story for the rest of the game.)\nAs long as you have an enduring story, Ori gets +1/+0 and has vigilance.")
    (keywords := Keyword.storied)
    (staticAbilities := #[.getsAndHasIfEnduringStory 1 0 Keyword.vigilance])

def oinTheBrave : CardDef :=
  legendaryCreature "Óin the Brave" (ManaCost.ofGenericAndColor 1 .red)
    #["Dwarf", "Warrior"] 1 3
    (oracleText := "Storied (If you control three or more artifacts, legendaries, and/or Sagas, you have an enduring story for the rest of the game.)\nAs long as you have an enduring story, Óin gets +1/+0 and has haste.\n{1}, {T}, Discard a card: Draw a card.")
    (keywords := Keyword.storied)
    (staticAbilities := #[.getsAndHasIfEnduringStory 1 0 Keyword.haste])
    (activatedAbilities := #[
      activated (.draw 1) (ManaCost.ofGeneric 1) (tap := true)
        (discardACard := true)])

def bomburGentleDreamer : CardDef :=
  legendaryCreature "Bombur, Gentle Dreamer" (ManaCost.ofGenericAndColor 2 .red)
    #["Dwarf", "Bard"] 5 3
    (oracleText := "Storied (If you control three or more artifacts, legendaries, and/or Sagas, you have an enduring story for the rest of the game.)\nBombur doesn't untap during your untap step unless you have an enduring story.")
    (keywords := Keyword.storied)
    (staticAbilities := #[.doesntUntapUnlessEnduringStory])

def filiThePathfinder : CardDef :=
  legendaryCreature "Fíli the Pathfinder" (ManaCost.ofGenericAndColor 3 .white)
    #["Dwarf", "Scout"] 2 2
    (oracleText := "Storied (If you control three or more artifacts, legendaries, and/or Sagas, you have an enduring story for the rest of the game.)\nAs long as you have an enduring story, creatures you control get +1/+1.\nWhenever Fíli or another nontoken Dwarf you control enters, create a 2/2 red Dwarf creature token.")
    (keywords := Keyword.storied)
    (staticAbilities := #[.creaturesYouControlGetIfEnduringStory 1 1])
    (triggeredAbilities := #[.onThisOrNontokenSubtypeEntersCreateTokens "Dwarf" .dwarf 1])

def thorinOakenshield : CardDef :=
  legendaryCreature "Thorin Oakenshield" (ManaCost.ofColors [.red, .white])
    #["Dwarf", "Noble"] 3 2
    (oracleText := "Trample\nStoried (If you control three or more artifacts, legendaries, and/or Sagas, you have an enduring story for the rest of the game.)\nAs long as you have an enduring story, artifacts and creatures you control have ward {1}.")
    (keywords := Keyword.trample.merge Keyword.storied)
    (staticAbilities := #[.artifactsAndCreaturesHaveWardIfEnduringStory 1])

def dainLordOfTheIronHills : CardDef :=
  legendaryCreature "Dáin, Lord of the Iron Hills" (ManaCost.ofGenericAndColor 1 .white)
    #["Dwarf", "Noble"] 2 2
    (oracleText := "Vigilance\nStoried (If you control three or more artifacts, legendaries, and/or Sagas, you have an enduring story for the rest of the game.)\nAs long as you have an enduring story, creatures can't attack you unless their controller pays {1} for each of those creatures.")
    (keywords := Keyword.vigilance.merge Keyword.storied)
    (staticAbilities := #[.creaturesCantAttackYouUnlessPayIfEnduringStory 1])

def oldThrush : CardDef :=
  creature "Old Thrush" (ManaCost.ofGeneric 2) #["Bird"] 1 2
    (oracleText := "Flying\nWhen this creature enters, you gain 2 life. You may search your library for a basic land card, reveal it, then shuffle and put that card on top.")
    (keywords := Keyword.flying)
    (triggeredAbilities := #[.onEnterGainLifeSearchBasicOnTop 2])

def mostDecrepitOldBird : CardDef :=
  creature "Most Decrepit Old Bird" (ManaCost.ofColor .blue) #["Bird"] 1 1
    (oracleText := "Flying\nThreshold — This creature gets +1/+1 as long as there are seven or more cards in your graveyard.\n//ADV//\nSpeak Secrets {1}{U}\nSorcery — Adventure\nMill four cards, then put an instant or sorcery card from among them into your hand.")
    (keywords := Keyword.flying)
    (staticAbilities := #[.thresholdGets 1 1])
    (adventure := some (adventure "Speak Secrets" (ManaCost.ofGenericAndColor 1 .blue)
      "Mill four cards, then put an instant or sorcery card from among them into your hand."
      (.millThenPutInstantOrSorcery 4)))

def lakeTownMariners : CardDef :=
  creature "Lake-town Mariners" (ManaCost.ofGenericAndColors 4 [.blue, .blue])
    #["Human", "Citizen"] 6 5
    (oracleText := "Vigilance\nWard {2} (Whenever this creature becomes the target of a spell or ability an opponent controls, counter it unless that player pays {2}.)\n//ADV//\nGone Fishing {3}{U}\nInstant — Adventure\nExile two target creatures and/or lands you control, then return them to the battlefield under their owner's control.")
    (keywords := Keyword.vigilance)
    (ward := some 2)
    (adventure := some (adventure "Gone Fishing" (ManaCost.ofGenericAndColor 3 .blue)
      "Exile two target creatures and/or lands you control, then return them to the battlefield under their owner's control."
      .exileThenReturnYouControl .instant))

def flameOfAnor : CardDef :=
  instant "Flame of Anor" (ManaCost.ofGenericAndColors 1 [.blue, .red])
    "Choose one. If you control a Wizard as you cast this spell, you may choose two instead.\n• Target player draws two cards.\n• Destroy target artifact.\n• Flame of Anor deals 5 damage to target creature."
    (spellModes := #[.targetPlayerDraw 2, .destroyTargetArtifact, .dealDamageToCreature 5])
    (chooseTwoIfYouControlSubtype := some "Wizard")

def lastMarchOfTheEnts : CardDef :=
  sorcery "Last March of the Ents" (ManaCost.ofGenericAndColors 6 [.green, .green])
    "This spell can't be countered.\nDraw cards equal to the greatest toughness among creatures you control, then put any number of creature cards from your hand onto the battlefield."
    (some .drawEqualToughnessThenPutCreatures)
    (cantBeCountered := true)

def raiseThePalisade : CardDef :=
  sorcery "Raise the Palisade" (ManaCost.ofGenericAndColor 4 .blue)
    "Choose a creature type. Return all creatures that aren't of the chosen type to their owners' hands."
    (some .chooseTypeReturnOthers)

def dragonsDesire : CardDef :=
  sorcery "Dragon's Desire" (ManaCost.ofGenericAndColors 2 [.red, .red])
    "Add {R} for each artifact your opponents control."
    (some .addRedPerOppArtifacts)

def pineconeStrike : CardDef :=
  instant "Pinecone Strike" (ManaCost.ofGenericAndColor 1 .red)
    "Choose one or both —\n• Pinecone Strike deals 3 damage to target creature. If that creature would die this turn, exile it instead.\n• Destroy target artifact token."
    (spellModes := #[.dealDamageToCreatureExileIfDies 3, .destroyArtifactToken])
    (chooseOneOrBoth := true)

def oriPlateStacker : CardDef :=
  legendaryCreature "Ori, Plate Stacker" (ManaCost.ofGenericAndColors 5 [.white, .white])
    #["Dwarf", "Bard"] 3 3
    (oracleText := "When Ori enters, destroy all artifacts and enchantments your opponents control. You gain 1 life for each permanent destroyed this way.")
    (triggeredAbilities := #[.onEnterDestroyOppArtifactsEnchantmentsGainLife])

def dainOfTheAncientHalls : CardDef :=
  legendaryCreature "Dáin of the Ancient Halls" (ManaCost.ofGenericAndColors 3 [.red, .white])
    #["Dwarf", "Noble"] 4 5
    (oracleText := "Vigilance, haste\nWhenever Dáin attacks, he deals damage equal to the number of Dwarves you control to each opponent.")
    (keywords := Keyword.vigilance.merge Keyword.haste)
    (triggeredAbilities := #[.onAttackDamageEqualSubtypeToEachOpponent "Dwarf"])

def treasureVault : CardDef :=
  card "Treasure Vault" #[.artifact, .land] ManaCost.empty
    (oracleText := "{T}: Add {C}.\n{X}{X}, {T}, Sacrifice this land: Create X Treasure tokens.")
    (tapAddMana := #[.colorless])
    (activatedAbilities := #[
      activated (.createTokensX .treasure) { symbols := #[.x, .x] }
        (tap := true) (sacrificeSource := true)])

def theLonelyMountain : CardDef :=
  land "The Lonely Mountain"
    "({T}: Add {R}.)\nThis land enters tapped unless you control an Equipment.\n{4}{R}, {T}: Create a 2/2 red Dwarf creature token. This ability costs {1} less to activate for each Equipment you control. Activate only as a sorcery."
    (subtypes := #["Mountain"])
    (entersTappedUnlessEquipment := true)
    (activatedAbilities := #[
      activated (.createTokens .dwarf 1) (ManaCost.ofGenericAndColor 4 .red)
        (tap := true) (onlyAsSorcery := true) (costReductionPerEquipment := 1)])

def thranduilSindarinLiege : CardDef :=
  legendaryCreature "Thranduil, Sindarin Liege"
    (ManaCost.ofGenericAndHybrids 2 .green .blue 2) #["Elf", "Noble"] 2 3
    (oracleText := "Other Elves you control get +1/+1.\nLandfall — Whenever a land you control enters, create a 1/1 green Elf creature token.\n//ADV//\nSilvan Rally {1}{G/U}{G/U}\nSorcery — Adventure\nMill four cards, then put up to two land cards from among them into your hand. (Then exile this card. You may cast the creature later from exile.)")
    (staticAbilities := #[.otherCreaturesGet #["Elf"] 1 1])
    (triggeredAbilities := #[.onLandYouControlEntersCreateTokens .elf 1])
    (adventure := some (adventure "Silvan Rally"
      (ManaCost.ofGenericAndHybrids 1 .green .blue 2)
      "Mill four cards, then put up to two land cards from among them into your hand. (Then exile this card. You may cast the creature later from exile.)"
      (.millThenPutLands 4 2)))

def aragornAndArwenWed : CardDef :=
  legendaryCreature "Aragorn and Arwen, Wed" (ManaCost.ofGenericAndColors 4 [.green, .white])
    #["Human", "Elf", "Noble"] 3 6
    (oracleText := "Vigilance\nWhenever Aragorn and Arwen enters or attacks, put a +1/+1 counter on each other creature you control. You gain 1 life for each other creature you control.")
    (keywords := Keyword.vigilance)
    (triggeredAbilities := #[.onEnterOrAttackPlusOneEachOtherGainLife])

def gloinTheMighty : CardDef :=
  legendaryCreature "Glóin the Mighty" (ManaCost.ofGenericAndColor 3 .red)
    #["Dwarf", "Warrior"] 4 3
    (oracleText := "At the beginning of your first main phase, add {R}{R}.\n//ADV//\nEasy Pickings {2}{R}\nSorcery — Adventure\nEasy Pickings deals 1 damage to each creature your opponents control. (Then exile this card. You may cast the creature later from exile.)")
    (triggeredAbilities := #[.onYourFirstMainAddMana #[.colored .red, .colored .red]])
    (adventure := some (adventure "Easy Pickings" (ManaCost.ofGenericAndColor 2 .red)
      "Easy Pickings deals 1 damage to each creature your opponents control. (Then exile this card. You may cast the creature later from exile.)"
      (.dealDamageToEachOppCreature 1)))

def ironHillsStalwart : CardDef :=
  creature "Iron Hills Stalwart" (ManaCost.ofGenericAndColor 4 .red)
    #["Dwarf", "Warrior"] 4 5
    (oracleText := "Reach, trample\nWhen this creature enters, attach target Equipment you control to up to one target creature you control.")
    (keywords := Keyword.reach.merge Keyword.trample)
    (triggeredAbilities := #[.onEnterAttachTargetEquipment])

def oldFatSpider : CardDef :=
  creature "Old Fat Spider" (ManaCost.ofGenericAndColors 4 [.green, .green])
    #["Spider"] 6 7
    (oracleText := "Reach\nThis creature can't be blocked by creatures with power 2 or less.\nWhenever this creature becomes the target of a spell or ability an opponent controls, draw a card.")
    (keywords := Keyword.reach)
    (staticAbilities := #[.cantBeBlockedByPowerAtMost 2])
    (triggeredAbilities := #[.onBecomesTargetDraw])

def greatGildedBoat : CardDef :=
  artifact "Great Gilded Boat" (ManaCost.ofGenericAndColor 2 .blue)
    "Whenever you attack, recruit. (Draw a card, then discard a card. If you discarded a nonland card, create a 1/1 white Human Soldier creature token.)\nCrew 2 (Tap any number of creatures you control with total power 2 or more: This Vehicle becomes an artifact creature until end of turn.)"
    (subtypes := #["Vehicle"])
    (power := some 4) (toughness := some 4)
    (triggeredAbilities := #[.onYouAttackRecruit])
    (crew := some 2)

def minasTirith : CardDef :=
  legendaryLand "Minas Tirith"
    "Minas Tirith enters tapped unless you control a legendary creature.\n{T}: Add {W}.\n{1}{W}, {T}: Draw a card. Activate only if you attacked with two or more creatures this turn."
    (tapAddMana := #[.colored .white])
    (entersTappedUnlessLegendary := true)
    (activatedAbilities := #[
      activated (.draw 1) (ManaCost.ofGenericAndColor 1 .white) (tap := true)
        (onlyIfYouAttackedWithTwoOrMore := true)])

def theShire : CardDef :=
  legendaryLand "The Shire"
    "The Shire enters tapped unless you control a legendary creature.\n{T}: Add {G}.\n{1}{G}, {T}, Tap an untapped creature you control: Create a Food token."
    (tapAddMana := #[.colored .green])
    (entersTappedUnlessLegendary := true)
    (activatedAbilities := #[
      activated (.createTokens .food 1) (ManaCost.ofGenericAndColor 1 .green)
        (tap := true) (tapAnUntappedCreatureYouControl := true)])

def thranduilTheStrategist : CardDef :=
  legendaryCreature "Thranduil the Strategist" (ManaCost.ofGenericAndColors 3 [.green, .blue])
    #["Elf", "Noble"] 4 4
    (oracleText := "Other Elves you control have \"{T}: Add {G} or {U}.\"\nLandfall — Whenever a land you control enters, create a 1/1 green Elf creature token.")
    (staticAbilities := #[
      .otherSubtypeHaveTapAddOneOf #["Elf"] #[.colored .green, .colored .blue]])
    (triggeredAbilities := #[.onLandYouControlEntersCreateTokens .elf 1])

def desolationOfSmaug : CardDef :=
  sorcery "Desolation of Smaug" (ManaCost.ofGenericAndColors 2 [.red, .red])
    "Desolation of Smaug deals 3 damage to each non-Dragon creature.\nAdd four mana in any combination of colors. Spend this mana only to cast Dragon spells."
    (some (.dealDamageToEachNonDragonThenAddDragonMana 3))

def moxAmber : CardDef :=
  artifact "Mox Amber" ManaCost.empty
    "{T}: Add one mana of any color among legendary creatures and planeswalkers you control."
    (supertypes := #[.legendary])
    (tapAddAnyColorAmongLegendaries := true)

def filiAndKiliJoyous : CardDef :=
  legendaryCreature "Fíli and Kíli, Joyous" (ManaCost.ofGenericAndColor 2 .red)
    #["Dwarf", "Bard"] 3 3
    (oracleText := "Haste\n{T}: Add {R}{R}. Spend this mana only to cast Dwarf, Equipment, and Saga spells.")
    (keywords := Keyword.haste)
    (tapAddRestricted := some (#[.colored .red, .colored .red],
      "Dwarf, Equipment, and Saga spells"))

def dwarvenMauler : CardDef :=
  creature "Dwarven Mauler" (ManaCost.ofColor .red) #["Dwarf", "Warrior"] 2 1
    (oracleText := "Equip abilities you activate that target this creature cost {2} less to activate.")
    (staticAbilities := #[.equipAbilitiesTargetingThisCostLess 2])

def myPrecious : CardDef :=
  artifact "My Precious" (ManaCost.ofGeneric 3)
    "Equipped creature has hexproof and can't be blocked.\nEquip—{2}, Pay 2 life.\n//ADV//\nAllure of Power {1}{B}\nInstant — Adventure\nAs an additional cost to cast this spell, sacrifice a creature.\nDraw two cards. (Then exile this card. You may cast the artifact later from exile.)"
    (subtypes := #["Equipment"])
    (supertypes := #[.legendary])
    (staticAbilities := #[.equippedCreatureHasKeywordsAndCantBeBlocked Keyword.hexproof])
    (activatedAbilities := #[
      activated .attachToTargetCreatureYouControl (ManaCost.ofGeneric 2)
        (onlyAsSorcery := true) (payLife := 2)])
    (adventure := some (adventure "Allure of Power"
      (ManaCost.ofGenericAndColor 1 .black)
      "As an additional cost to cast this spell, sacrifice a creature.\nDraw two cards. (Then exile this card. You may cast the artifact later from exile.)"
      (.draw 2) (cardType := .instant) (additionalCostSacrificeCreature := true)))

def troopOfPonies : CardDef :=
  creature "Troop of Ponies" (ManaCost.ofGeneric 2) #["Horse"] 2 1
    (oracleText := "{2}, {T}, Sacrifice this creature: Search your library for up to two basic land cards, reveal them, put one onto the battlefield tapped and the other into your hand, then shuffle.")
    (activatedAbilities := #[
      activated .searchTwoBasicsSplit (ManaCost.ofGeneric 2)
        (tap := true) (sacrificeSource := true)])

def arcaneSignet : CardDef :=
  artifact "Arcane Signet" (ManaCost.ofGeneric 2)
    "{T}: Add one mana of any color in your commander's color identity."
    (tapAddCommanderIdentity := true)

def theGaffer : CardDef :=
  legendaryCreature "The Gaffer" (ManaCost.ofGenericAndColor 2 .white)
    #["Halfling", "Peasant"] 2 3
    (oracleText := "At the beginning of each end step, if you gained 3 or more life this turn, draw a card.")
    (triggeredAbilities := #[.onEachEndStepDrawIfGainedLife 3])

def witchKingBringerOfRuin : CardDef :=
  legendaryCreature "Witch-king, Bringer of Ruin" (ManaCost.ofGenericAndColors 4 [.black, .black])
    #["Wraith", "Noble"] 5 3
    (oracleText := "Flying\nWhenever Witch-king attacks, defending player sacrifices a creature with the least power among creatures they control.")
    (keywords := Keyword.flying)
    (triggeredAbilities := #[.onAttackDefenderSacsLeastPower])

def elvenRaftSteerer : CardDef :=
  creature "Elven Raft-Steerer" (ManaCost.ofGenericAndColor 2 .blue)
    #["Elf", "Pilot"] 3 2
    (oracleText := "Landfall — Whenever a land you control enters, choose one —\n• Tap target creature an opponent controls.\n• Untap target creature you control.")
    (triggeredAbilities := #[.onLandYouControlEntersTapOrUntap])

def mirkwoodMeditator : CardDef :=
  creature "Mirkwood Meditator" (ManaCost.ofGenericAndColor 2 .blue)
    #["Elf", "Druid"] 2 4
    (oracleText := "Landfall — Whenever a land you control enters, you may have this creature's base power and toughness become 4/2 until end of turn.")
    (triggeredAbilities := #[.onLandYouControlEntersBecomePT 4 2])

def mirkwoodNurturer : CardDef :=
  creature "Mirkwood Nurturer" (ManaCost.ofGenericAndHybrids 2 .green .blue)
    #["Elf", "Ranger"] 3 2
    (oracleText := "When this creature enters, return up to one other target permanent you control to its owner's hand. If you do, put a +1/+1 counter on this creature.")
    (triggeredAbilities := #[.onEnterReturnOtherPlusOne])

def necklaceOfGirion : CardDef :=
  artifact "Necklace of Girion" (ManaCost.ofGenericAndColor 2 .green)
    "Whenever you cast a green spell and whenever a Forest you control enters, put a +1/+1 counter on target creature you control.\n{T}: Add {G}."
    (supertypes := #[.legendary])
    (tapAddMana := #[.colored .green])
    (triggeredAbilities := #[.onCastGreenOrForestEntersPlusOne])

def kiliTheResourceful : CardDef :=
  legendaryCreature "Kíli the Resourceful" (ManaCost.ofGenericAndColor 1 .white)
    #["Dwarf", "Scout"] 1 2
    (oracleText := "Storied (If you control three or more artifacts, legendaries, and/or Sagas, you have an enduring story for the rest of the game.)\nAs long as you have an enduring story, you may pay {0} rather than pay the equip cost of the first equip ability you activate each turn.\nWhenever another Dwarf or Equipment you control enters, draw a card. This ability triggers only once each turn.")
    (keywords := Keyword.storied)
    (staticAbilities := #[.firstEquipFreeIfEnduringStory])
    (triggeredAbilities := #[.onAnotherSubtypeOrEquipmentEntersDrawOnce "Dwarf"])

def dainsCompany : CardDef :=
  creature "Dáin's Company" (ManaCost.ofColors [.red, .white]) #["Dwarf", "Warrior"] 2 2
    (oracleText := "This creature has lifelink as long as you control another Dwarf.\nWhen this creature enters, look at the top four cards of your library. You may reveal a Dwarf or Equipment card from among them and put it into your hand. Put the rest on the bottom of your library in a random order.")
    (staticAbilities := #[.lifelinkIfYouControlOtherSubtype "Dwarf"])
    (triggeredAbilities := #[.onEnterLookAtTopRevealTypes 4 #["Dwarf", "Equipment"]])

def sauronTheLidlessEye : CardDef :=
  legendaryCreature "Sauron, the Lidless Eye" (ManaCost.ofGenericAndColors 3 [.black, .red])
    #["Avatar", "Horror"] 4 4
    (oracleText := "When Sauron enters, gain control of target creature an opponent controls until end of turn. Untap it. It gains haste until end of turn.\n{1}{B}{R}: Creatures you control get +2/+0 until end of turn. Each opponent loses 2 life.")
    (triggeredAbilities := #[.onEnterGainControlOppUntilEot])
    (activatedAbilities := #[
      activated (.creaturesYouControlGetOppsLoseLife 2 0 2)
        (ManaCost.ofGenericAndColors 1 [.black, .red])])

def bolgEreborsReckoning : CardDef :=
  legendaryCreature "Bolg, Erebor's Reckoning" (ManaCost.ofGenericAndColors 4 [.black, .red])
    #["Goblin", "Soldier"] 6 6
    (oracleText := "Trample\nAt the beginning of each combat, other Goblins and Orcs you control get +2/+2 until end of turn. Creatures your opponents control get -1/-1 until end of turn.")
    (keywords := Keyword.trample)
    (triggeredAbilities := #[.onEachCombatOthersGetAndOppsGet #["Goblin", "Orc"] 2 2 (-1) (-1)])

def smaugWickedWorm : CardDef :=
  legendaryCreature "Smaug, Wicked Worm" (ManaCost.ofGenericAndColors 3 [.black, .red])
    #["Dragon"] 5 5
    (oracleText := "Flying\nWhen Smaug enters, create X tapped Treasure tokens, where X is the number of artifacts your opponents control.\nWhenever you cast a spell, if mana from a Treasure was spent to cast it, you draw a card and lose 1 life.")
    (keywords := Keyword.flying)
    (triggeredAbilities := #[
      .onEnterCreateTappedTreasuresEqualOppArtifacts,
      .onCastWithTreasureDrawLoseLife])

def glamdringFoeHammer : CardDef :=
  artifact "Glamdring, Foe-hammer" (ManaCost.ofGeneric 2)
    "Instant and sorcery spells you cast cost {X} less to cast, where X is equipped creature's power.\nEquip {2}\n//ADV//\nGleam of Death {3}{U}\nSorcery — Adventure\nMill six cards, then put all instant and sorcery cards from among them into your hand. (Then exile this card. You may cast the artifact later from exile.)"
    (subtypes := #["Equipment"])
    (supertypes := #[.legendary])
    (staticAbilities := #[.instantSorceryCostReductionEqualEquippedPower])
    (activatedAbilities := #[equipAbility (ManaCost.ofGeneric 2)])
    (adventure := some (adventure "Gleam of Death" (ManaCost.ofGenericAndColor 3 .blue)
      "Mill six cards, then put all instant and sorcery cards from among them into your hand. (Then exile this card. You may cast the artifact later from exile.)"
      (.millThenPutAllInstantsOrSorceries 6)))

def settleTheWreckage : CardDef :=
  instant "Settle the Wreckage" (ManaCost.ofGenericAndColors 2 [.white, .white])
    "Exile all attacking creatures target player controls. That player may search their library for that many basic land cards, put those cards onto the battlefield tapped, then shuffle."
    (some .exileAttackersSearchBasics)

def anUnexpectedParty : CardDef :=
  enchantment "An Unexpected Party" (ManaCost.ofGenericAndColors 2 [.white, .white])
    "As this enchantment enters, choose a creature type.\nCreatures you control of the chosen type get +2/+2.\n//ADV//\nAt the Door {X}{2}{W}\nSorcery — Adventure\nCreate X 2/2 red Dwarf creature tokens. (Then exile this card. You may cast the enchantment later from exile.)"
    (asEntersChooseCreatureType := true)
    (staticAbilities := #[.chosenTypeCreaturesGet 2 2])
    (adventure := some (adventure "At the Door"
      { symbols := #[.x, .generic 2, .colored .white] }
      "Create X 2/2 red Dwarf creature tokens. (Then exile this card. You may cast the enchantment later from exile.)"
      (.createTokensX .dwarf)))

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
  mithrilCoat,
  greatUglyLookingGoblin,
  theArkenstone,
  bolgsCompany,
  noriTellerOfTales,
  theLordOfTheEagles,
  throrsMap,
  rivendell,
  delightedHalfling,
  relicOfSauron,
  longLostLances,
  theBlackArrow,
  smaugTheMagnificent,
  theQueenOfDale,
  lothoCorruptShirriff,
  oriKeeperOfSongs,
  oinTheBrave,
  bomburGentleDreamer,
  filiThePathfinder,
  thorinOakenshield,
  dainLordOfTheIronHills,
  oldThrush,
  mostDecrepitOldBird,
  lakeTownMariners,
  flameOfAnor,
  lastMarchOfTheEnts,
  raiseThePalisade,
  dragonsDesire,
  pineconeStrike,
  oriPlateStacker,
  dainOfTheAncientHalls,
  treasureVault,
  theLonelyMountain,
  thranduilSindarinLiege,
  aragornAndArwenWed,
  gloinTheMighty,
  ironHillsStalwart,
  oldFatSpider,
  greatGildedBoat,
  minasTirith,
  theShire,
  thranduilTheStrategist,
  desolationOfSmaug,
  moxAmber,
  filiAndKiliJoyous,
  dwarvenMauler,
  myPrecious,
  troopOfPonies,
  arcaneSignet,
  theGaffer,
  witchKingBringerOfRuin,
  elvenRaftSteerer,
  mirkwoodMeditator,
  mirkwoodNurturer,
  necklaceOfGirion,
  kiliTheResourceful,
  dainsCompany,
  sauronTheLidlessEye,
  bolgEreborsReckoning,
  smaugWickedWorm,
  glamdringFoeHammer,
  settleTheWreckage,
  anUnexpectedParty
]

end Mtg.Engine.Catalog.HobbitSet
