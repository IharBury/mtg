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

def ironHillsBlacksmith : CardDef :=
  creature "Iron Hills Blacksmith" (ManaCost.ofGenericAndColor 1 .white)
    #["Dwarf", "Artificer"] 1 1
    (oracleText := "Double strike\nWhen this creature enters, create a colorless Equipment artifact token named Axe with \"Equipped creature gets +1/+0\" and equip {2}.")
    (keywords := Keyword.doubleStrike)
    (triggeredAbilities := #[.onEnterCreateAxe])

def thorinKingOfDurinsFolk : CardDef :=
  legendaryCreature "Thorin, King of Durin's Folk" (ManaCost.ofGenericAndColors 3 [.red, .white])
    #["Dwarf", "Noble"] 4 4
    (oracleText := "Whenever Thorin or another Dwarf you control enters, create a Treasure token.\nOther Dwarves you control get +1/+0 for each artifact token you control.")
    (staticAbilities := #[.otherSubtypeGetPowerPerArtifactToken "Dwarf"])
    (triggeredAbilities := #[.onThisOrAnotherSubtypeEntersCreateTokens "Dwarf" .treasure 1])

def gandalfGoblinsBane : CardDef :=
  legendaryCreature "Gandalf, Goblins' Bane" (ManaCost.ofGenericAndColor 2 .red)
    #["Avatar", "Wizard"] 2 3
    (oracleText := "Whenever you cast a noncreature spell, Gandalf gets +1/+1 until end of turn and deals 1 damage to each opponent.\n//ADV//\nFlameshape {1}{R}\nSorcery — Adventure\nLook at the top two cards of your library and exile them face down. For as long as they remain exiled, you may play them if you control a Wizard. (Then exile this card. You may cast the creature later from exile.)")
    (triggeredAbilities := #[.onCastNoncreaturePumpAndDamageOpponents 1])
    (adventure := some (adventure "Flameshape" (ManaCost.ofGenericAndColor 1 .red)
      "Look at the top two cards of your library and exile them face down. For as long as they remain exiled, you may play them if you control a Wizard. (Then exile this card. You may cast the creature later from exile.)"
      (.exileTopPlayIfYouControlSubtype 2 "Wizard")))

def bilboUnexpectedAdventurer : CardDef :=
  legendaryCreature "Bilbo, Unexpected Adventurer" (ManaCost.ofGenericAndColor 3 .white)
    #["Halfling", "Rogue"] 2 2
    (oracleText := "Bilbo can't be blocked by creatures with power 3 or greater.\nWhenever Bilbo deals combat damage to a player or battle, put up to one target nonland permanent card with mana value 3 or less from a graveyard onto the battlefield under its owner's control.")
    (staticAbilities := #[.cantBeBlockedByPowerAtLeast 3])
    (triggeredAbilities := #[.onCombatDamagePutNonlandMvAtMost 3])

def anUnexpectedParty : CardDef :=
  enchantment "An Unexpected Party" (ManaCost.ofGenericAndColors 2 [.white, .white])
    "As this enchantment enters, choose a creature type.\nCreatures you control of the chosen type get +2/+2.\n//ADV//\nAt the Door {X}{2}{W}\nSorcery — Adventure\nCreate X 2/2 red Dwarf creature tokens. (Then exile this card. You may cast the enchantment later from exile.)"
    (asEntersChooseCreatureType := true)
    (staticAbilities := #[.chosenTypeCreaturesGet 2 2])
    (adventure := some (adventure "At the Door"
      { symbols := #[.x, .generic 2, .colored .white] }
      "Create X 2/2 red Dwarf creature tokens. (Then exile this card. You may cast the enchantment later from exile.)"
      (.createTokensX .dwarf)))

def alongTheCrookedWay : CardDef :=
  enchantment "Along the Crooked Way" (ManaCost.ofGenericAndColor 2 .black) "When this enchantment enters, return target creature card from your graveyard to your hand.\nWhenever a creature card leaves your graveyard, amass Goblins 1.\n{1}{B}: Goblins and Orcs you control gain menace until end of turn."
    (staticAbilities := #[.printed "{1}{B}: Goblins and Orcs you control gain menace until end of turn."])
    (triggeredAbilities := #[.printed "When this enchantment enters, return target creature card from your graveyard to your hand.",
      .printed "Whenever a creature card leaves your graveyard, amass Goblins 1."])

def andurilFlameOfTheWest : CardDef :=
  artifact "Andúril, Flame of the West" (ManaCost.ofGeneric 3) "Equipped creature gets +3/+1.\nWhenever equipped creature attacks, create two tapped 1/1 white Spirit creature tokens with flying. If that creature is legendary, instead create two of those tokens that are tapped and attacking.\nEquip {2}"
    (subtypes := #["Equipment"])
    (supertypes := #[.legendary])
    (staticAbilities := #[.equippedCreatureGets 3 1])
    (triggeredAbilities := #[.printed "Whenever equipped creature attacks, create two tapped 1/1 white Spirit creature tokens with flying. If that creature is legendary, instead create two of those tokens that are tapped and attacking."])
    (activatedAbilities := #[equipAbility (ManaCost.ofGeneric 2)])

def andurilNarsilReforged : CardDef :=
  artifact "Andúril, Narsil Reforged" (ManaCost.ofGeneric 2) "Ascend (If you control ten or more permanents, you get the city's blessing for the rest of the game.)\nWhenever equipped creature attacks, put a +1/+1 counter on each creature you control. If you have the city's blessing, put two +1/+1 counters on each creature you control instead.\nEquip {3}"
    (subtypes := #["Equipment"])
    (supertypes := #[.legendary])
    (keywords := Keyword.ascend)
    (triggeredAbilities := #[.printed "Whenever equipped creature attacks, put a +1/+1 counter on each creature you control. If you have the city's blessing, put two +1/+1 counters on each creature you control instead."])
    (activatedAbilities := #[equipAbility (ManaCost.ofGeneric 3)])

def aragornTheUniter : CardDef :=
  legendaryCreature "Aragorn, the Uniter" (ManaCost.ofColors [.red, .green, .white, .blue]) #["Human", "Noble"] 5 5 (oracleText := "Whenever you cast a white spell, create a 1/1 white Human Soldier creature token.\nWhenever you cast a blue spell, scry 2.\nWhenever you cast a red spell, Aragorn deals 3 damage to target opponent.\nWhenever you cast a green spell, target creature gets +4/+4 until end of turn.")
    (triggeredAbilities := #[.printed "Whenever you cast a white spell, create a 1/1 white Human Soldier creature token.",
      .printed "Whenever you cast a blue spell, scry 2.",
      .printed "Whenever you cast a red spell, Aragorn deals 3 damage to target opponent.",
      .printed "Whenever you cast a green spell, target creature gets +4/+4 until end of turn."])

def arwenMortalQueen : CardDef :=
  legendaryCreature "Arwen, Mortal Queen" (ManaCost.ofGenericAndColors 1 [.green, .white]) #["Elf", "Noble"] 2 2 (oracleText := "Arwen enters with an indestructible counter on her.\n{1}, Remove an indestructible counter from Arwen: Another target creature gains indestructible until end of turn. Put a +1/+1 counter and a lifelink counter on that creature and a +1/+1 counter and a lifelink counter on Arwen.")
    (staticAbilities := #[.printed "Arwen enters with an indestructible counter on her.",
      .printed "{1}, Remove an indestructible counter from Arwen: Another target creature gains indestructible until end of turn. Put a +1/+1 counter and a lifelink counter on that creature and a +1/+1 counter and a lifelink counter on Arwen."])

def arwenWeaverOfHope : CardDef :=
  legendaryCreature "Arwen, Weaver of Hope" (ManaCost.ofGenericAndColors 1 [.green, .green]) #["Elf", "Noble"] 2 1 (oracleText := "Each other creature you control enters with a number of additional +1/+1 counters on it equal to Arwen's toughness.")
    (othersEnterWithPlusOneEqualToughness := true)

def azogMoriaSRuin : CardDef :=
  legendaryCreature "Azog, Moria's Ruin" (ManaCost.ofGenericAndColor 2 .black) #["Goblin", "Soldier"] 1 3 (oracleText := "When Azog enters, destroy up to one other target creature. Its controller amasses Goblins X, where X is that creature's power. If you controlled that creature, draw a card. (To amass Goblins X, that player puts X +1/+1 counters on an Army they control. It's also a Goblin. If they don't control an Army, they create a 0/0 black Goblin Army creature token first.)")
    (triggeredAbilities := #[.printed "When Azog enters, destroy up to one other target creature. Its controller amasses Goblins X, where X is that creature's power. If you controlled that creature, draw a card. (To amass Goblins X, that player puts X +1/+1 counters on an Army they control. It's also a Goblin. If they don't control an Army, they create a 0/0 black Goblin Army creature token first.)"])

def balinLoremaster : CardDef :=
  legendaryCreature "Balin, Loremaster" (ManaCost.ofGenericAndColors 3 [.red, .red]) #["Dwarf", "Bard"] 4 4 (oracleText := "Storied (If you control three or more artifacts, legendaries, and/or Sagas, you have an enduring story for the rest of the game.)\nWhenever Balin or another Dwarf you control enters, you may discard your hand. Draw X cards, where X is the number of cards discarded this way. If you have an enduring story, Balin deals X damage to each opponent.")
    (keywords := Keyword.storied)
    (triggeredAbilities := #[.printed "Whenever Balin or another Dwarf you control enters, you may discard your hand. Draw X cards, where X is the number of cards discarded this way. If you have an enduring story, Balin deals X damage to each opponent."])

def bardTheBowman : CardDef :=
  legendaryCreature "Bard the Bowman" (ManaCost.ofGenericAndColors 1 [.white, .blue]) #["Human", "Archer"] 1 3 (oracleText := "Reach\nWhenever you draw your second card each turn, put a +1/+1 counter on target creature. It gains lifelink until end of turn.")
    (keywords := Keyword.reach)
    (triggeredAbilities := #[.printed "Whenever you draw your second card each turn, put a +1/+1 counter on target creature. It gains lifelink until end of turn."])

def bardKingOfDale : CardDef :=
  legendaryCreature "Bard, King of Dale" (ManaCost.ofGenericAndColors 4 [.white, .blue]) #["Human", "Noble", "Archer"] 3 5 (oracleText := "Reach, vigilance\nIf you would draw a card except the first one you draw in each of your draw steps, draw two cards instead.\nIf one or more tokens would be created under your control, twice that many of those tokens are created instead.")
    (keywords := Keyword.reach.merge Keyword.vigilance)
    (staticAbilities := #[.printed "If you would draw a card except the first one you draw in each of your draw steps, draw two cards instead.",
      .printed "If one or more tokens would be created under your control, twice that many of those tokens are created instead."])

def bejeweledWarg : CardDef :=
  creature "Bejeweled Warg" (ManaCost.ofGenericAndColor 1 .green) #["Wolf"] 3 2 (oracleText := "Trample\nWhenever this creature deals combat damage to a player, choose one —\n• Put a +1/+1 counter on target Wolf you control.\n• Create a Treasure token. (It's an artifact with \"{T}, Sacrifice this token: Add one mana of any color.\")")
    (keywords := Keyword.trample)
    (triggeredAbilities := #[.printed "Whenever this creature deals combat damage to a player, choose one — • Put a +1/+1 counter on target Wolf you control. • Create a Treasure token. (It's an artifact with \"{T}, Sacrifice this token: Add one mana of any color.\")"])

def belladonnaTook : CardDef :=
  legendaryCreature "Belladonna Took" (ManaCost.ofGenericAndColor 1 .white) #["Halfling", "Citizen"] 2 2 (oracleText := "Whenever a token you control enters, you gain 1 life if this is the first time this ability has resolved this turn. If it's the second time, draw a card. If it's the third time, put a +1/+1 counter on each creature you control.")
    (triggeredAbilities := #[.printed "Whenever a token you control enters, you gain 1 life if this is the first time this ability has resolved this turn. If it's the second time, draw a card. If it's the third time, put a +1/+1 counter on each creature you control."])

def beornTheFierce : CardDef :=
  legendaryCreature "Beorn the Fierce" (ManaCost.ofGenericAndColors 3 [.green, .green]) #["Bear", "Shapeshifter", "Warrior"] 6 6 (oracleText := "Trample\nOther Bears you control get +2/+2.\nAt the beginning of combat on your turn, put a trample counter on up to one target creature you control. It becomes a Bear in addition to its other types. Then if you control three or more Bears, draw two cards.")
    (keywords := Keyword.trample)
    (staticAbilities := #[.otherCreaturesGet #["Bear"] 2 2])
    (triggeredAbilities := #[.printed "At the beginning of combat on your turn, put a trample counter on up to one target creature you control. It becomes a Bear in addition to its other types. Then if you control three or more Bears, draw two cards."])

def bifurMelodicRider : CardDef :=
  legendaryCreature "Bifur, Melodic Rider" (ManaCost.ofGenericAndHybrids 4 .red .white 2) #["Dwarf", "Bard"] 4 5 (oracleText := "Storied (If you control three or more artifacts, legendaries, and/or Sagas, you have an enduring story for the rest of the game.)\nWhenever Bifur enters or attacks, put a +1/+1 counter on target creature.\nAs long as you have an enduring story, if a triggered ability of a Dwarf you control triggers, that ability triggers an additional time.")
    (keywords := Keyword.storied)
    (staticAbilities := #[.extraTriggerIfEnduringStorySubtype "Dwarf"])
    (triggeredAbilities := #[.printed "Whenever Bifur enters or attacks, put a +1/+1 counter on target creature."])

def bilboSBurglaring : CardDef :=
  sorcery "Bilbo's Burglaring" (ManaCost.ofGenericAndColors 4 [.blue, .blue]) "For each opponent, gain control of up to one target artifact that player controls." (some (.printed "For each opponent, gain control of up to one target artifact that player controls."))

def bilboSGambit : CardDef :=
  instant "Bilbo's Gambit" (ManaCost.ofGenericAndColor 1 .white) "Gift a Treasure (You may promise an opponent a gift as you cast this spell. If you do, they create a Treasure token before its other effects. It's an artifact with \"{T}, Sacrifice this token: Add one mana of any color.\")\nReturn target spell to its owner's hand. If the gift was promised, players can't cast spells this turn." (some (.printed "Return target spell to its owner's hand. If the gift was promised, players can't cast spells this turn."))
    (giftTreasure := true)

def bilboSRing : CardDef :=
  artifact "Bilbo's Ring" (ManaCost.ofGeneric 3) "During your turn, equipped creature has hexproof and can't be blocked.\nWhenever equipped creature attacks alone, you draw a card and you lose 1 life.\nEquip Halfling {1} ({1}: Attach to target Halfling you control. Equip only as a sorcery.)\nEquip {4} ({4}: Attach to target creature you control. Equip only as a sorcery.)"
    (subtypes := #["Equipment"])
    (supertypes := #[.legendary])
    (staticAbilities := #[.equippedHexproofUnblockableDuringYourTurn])
    (triggeredAbilities := #[.printed "Whenever equipped creature attacks alone, you draw a card and you lose 1 life."])
    (activatedAbilities := #[equipAbility (ManaCost.ofGeneric 1) (subtype := some "Halfling"),
      equipAbility (ManaCost.ofGeneric 4)])

def bilboFellowConspirator : CardDef :=
  legendaryCreature "Bilbo, Fellow Conspirator" (ManaCost.ofGenericAndColor 2 .green) #["Halfling", "Citizen"] 2 3 (oracleText := "If you would create a Food token, instead create a Food token and a Treasure token.")
    (foodAlsoCreatesTreasure := true)

def bilboThiefInTheNight : CardDef :=
  legendaryCreature "Bilbo, Thief in the Night" (ManaCost.ofGenericAndColor 1 .blue) #["Halfling", "Rogue"] 2 2 (oracleText := "Spells you cast from anywhere other than your hand cost {1} less to cast.\nWhenever Bilbo attacks, you may cast an artifact, instant, or sorcery spell from your graveyard. If an instant or sorcery spell cast this way would be put into your graveyard, exile it instead.")
    (staticAbilities := #[.printed "Spells you cast from anywhere other than your hand cost {1} less to cast."])
    (triggeredAbilities := #[.printed "Whenever Bilbo attacks, you may cast an artifact, instant, or sorcery spell from your graveyard. If an instant or sorcery spell cast this way would be put into your graveyard, exile it instead."])

def bolgOfTheNorth : CardDef :=
  legendaryCreature "Bolg of the North" (ManaCost.ofGenericAndColors 3 [.black, .red]) #["Goblin", "Soldier"] 5 5 (oracleText := "When Bolg enters, you may sacrifice another creature. When you do, Bolg deals damage equal to that creature's power to another target creature. If excess damage was dealt this way, amass Goblins X, where X is that excess damage. (Put X +1/+1 counters on an Army you control. It's also a Goblin. If you don't control an Army, create a 0/0 black Goblin Army creature token first.)")
    (triggeredAbilities := #[.printed "When Bolg enters, you may sacrifice another creature. When you do, Bolg deals damage equal to that creature's power to another target creature. If excess damage was dealt this way, amass Goblins X, where X is that excess damage. (Put X +1/+1 counters on an Army you control. It's also a Goblin. If you don't control an Army, create a 0/0 black Goblin Army creature token first.)"])

def boughsideWanderers : CardDef :=
  creature "Boughside Wanderers" (ManaCost.ofGenericAndColors 4 [.green, .green]) #["Elf", "Scout"] 4 4 (oracleText := "When this creature enters, look at the top four cards of your library. You may reveal a permanent card from among them and put it into your hand. Put the rest on the bottom of your library in a random order.\nLandfall — Whenever a land you control enters, this creature gets +2/+2 until end of turn.")
    (triggeredAbilities := #[.onLandYouControlEntersGets 2 2,
      .printed "When this creature enters, look at the top four cards of your library. You may reveal a permanent card from among them and put it into your hand. Put the rest on the bottom of your library in a random order."])

def burnBurnTreeAndFern : CardDef :=
  saga "Burn, Burn, Tree and Fern" (ManaCost.ofGenericAndColor 3 .red) "(As this Saga enters and after your draw step, add a lore counter. Sacrifice after IV.)\nI — This Saga deals 6 damage to target creature an opponent controls.\nII — Destroy target artifact an opponent controls.\nIII, IV — Add {R}." "IV" #[{ roman := "I", effect := "This Saga deals 6 damage to target creature an opponent controls." }, { roman := "II", effect := "Destroy target artifact an opponent controls." }, { roman := "III, IV", effect := "Add {R}." }]

def callForthTheTempest : CardDef :=
  sorcery "Call Forth the Tempest" (ManaCost.ofGenericAndColors 5 [.red, .red, .red]) "Cascade, cascade (When you cast this spell, exile cards from the top of your library until you exile a nonland card that costs less. You may cast it without paying its mana cost. Put the exiled cards on the bottom of your library in a random order. Then do it again.)\nCall Forth the Tempest deals damage to each creature your opponents control equal to the total mana value of other spells you've cast this turn." (some (.printed "Call Forth the Tempest deals damage to each creature your opponents control equal to the total mana value of other spells you've cast this turn."))
    (cascade := 2)

def cantankerousKeepers : CardDef :=
  creature "Cantankerous Keepers" (ManaCost.ofGenericAndColor 5 .green) #["Elf", "Soldier"] 4 3 (oracleText := "Affinity for Elves (This spell costs {1} less to cast for each Elf you control.)\nWhen this creature enters, mill four cards, then put all Elf cards from among them into your hand.")
    (affinityForSubtype := some "Elves")
    (triggeredAbilities := #[.printed "When this creature enters, mill four cards, then put all Elf cards from among them into your hand."])

def cavernHoardDragon : CardDef :=
  creature "Cavern-Hoard Dragon" (ManaCost.ofGenericAndColors 7 [.red, .red]) #["Dragon"] 6 6 (oracleText := "This spell costs {X} less to cast, where X is the greatest number of artifacts an opponent controls.\nFlying, trample, haste\nWhenever this creature deals combat damage to a player, you create a Treasure token for each artifact that player controls.")
    (costReductionEqualOppArtifacts := true)
    (keywords := Keyword.flying.merge Keyword.trample |>.merge Keyword.haste)
    (triggeredAbilities := #[.printed "Whenever this creature deals combat damage to a player, you create a Treasure token for each artifact that player controls."])

def celebrateTheMountainKing : CardDef :=
  enchantment "Celebrate the Mountain-king" (ManaCost.ofGenericAndColor 3 .white) "When this enchantment enters, for each opponent, exile up to one target nonland permanent that player controls until this enchantment leaves the battlefield.\nWhen this enchantment enters, recruit. (Draw a card, then discard a card. If you discarded a nonland card, create a 1/1 white Human Soldier creature token.)"
    (triggeredAbilities := #[.onEnterRecruit,
      .printed "When this enchantment enters, for each opponent, exile up to one target nonland permanent that player controls until this enchantment leaves the battlefield."])

def chiefOfTheWilds : CardDef :=
  legendaryCreature "Chief of the Wilds" (ManaCost.ofGenericAndColors 2 [.black, .green]) #["Wolf"] 4 4 (oracleText := "Menace\nWhenever another Wolf you control enters, put two +1/+1 counters on Chief of the Wilds.\nIf a triggered ability of another Wolf or battle you control triggers, that ability triggers an additional time.")
    (keywords := Keyword.menace)
    (staticAbilities := #[.printed "If a triggered ability of another Wolf or battle you control triggers, that ability triggers an additional time."])
    (triggeredAbilities := #[.printed "Whenever another Wolf you control enters, put two +1/+1 counters on Chief of the Wilds."])

def dancingFromDarkToDawn : CardDef :=
  enchantment "Dancing from Dark to Dawn" (ManaCost.ofGenericAndColors 3 [.green, .green]) "Whenever you cast a creature spell, put X +1/+1 counters on target creature you control, where X is that spell's mana value.\nLandfall — Whenever a land you control enters, create a 2/2 green Bear creature token."
    (staticAbilities := #[.printed "Landfall — Whenever a land you control enters, create a 2/2 green Bear creature token."])
    (triggeredAbilities := #[.printed "Whenever you cast a creature spell, put X +1/+1 counters on target creature you control, where X is that spell's mana value."])

def desertWereWorm : CardDef :=
  creature "Desert Were-Worm" (ManaCost.ofGenericAndColors 4 [.red, .red]) #["Dragon", "Wurm"] 0 5 (oracleText := "This creature gets +2/+0 for each Mountain you control.\nWhenever you attack with creatures with total power 12 or greater for the first time each turn, untap all attacking creatures. After this phase, there is an additional combat phase.")
    (powerPerMountain := 2)
    (triggeredAbilities := #[.printed "Whenever you attack with creatures with total power 12 or greater for the first time each turn, untap all attacking creatures. After this phase, there is an additional combat phase."])

def downInTheValley : CardDef :=
  saga "Down in the Valley" (ManaCost.ofGenericAndColor 2 .green) "(As this Saga enters and after your draw step, add a lore counter. Sacrifice after IV.)\nI — Search your library for a basic land card, reveal it, put it into your hand, then shuffle.\nII — This Saga gains \"Landfall — Whenever a land you control enters, create a 1/1 green Elf creature token.\"\nIII, IV — Elves you control get +1/+0 and gain vigilance until end of turn." "IV" #[{ roman := "I", effect := "Search your library for a basic land card, reveal it, put it into your hand, then shuffle." }, { roman := "II", effect := "This Saga gains \"Landfall — Whenever a land you control enters, create a 1/1 green Elf creature token.\"" }, { roman := "III, IV", effect := "Elves you control get +1/+0 and gain vigilance until end of turn." }]

def downDownToGoblinTown : CardDef :=
  saga "Down, Down to Goblin-town" (ManaCost.ofGenericAndColor 2 .black) "(As this Saga enters and after your draw step, add a lore counter. Sacrifice after IV.)\nI — Target opponent reveals their hand. You choose a nonland card from it. That player discards that card.\nII — Amass Goblins 1. (Put a +1/+1 counter on an Army you control. It's also a Goblin. If you don't control an Army, create a 0/0 black Goblin Army creature token first.)\nIII, IV — Target opponent loses 1 life and you gain 1 life." "IV" #[{ roman := "I", effect := "Target opponent reveals their hand. You choose a nonland card from it. That player discards that card." }, { roman := "II", effect := "Amass Goblins 1. (Put a +1/+1 counter on an Army you control. It's also a Goblin. If you don't control an Army, create a 0/0 black Goblin Army creature token first.)" }, { roman := "III, IV", effect := "Target opponent loses 1 life and you gain 1 life." }]

def dragonCursedHalls : CardDef :=
  land "Dragon-Cursed Halls" "{T}: Add {C}.\n{1}, {T}: Until end of turn, target creature gains \"Whenever this creature deals combat damage to a player, create a Treasure token.\""
    (tapAddMana := #[.colorless])
    (staticAbilities := #[.printed "{1}, {T}: Until end of turn, target creature gains \"Whenever this creature deals combat damage to a player, create a Treasure token.\""])

def dwalinWeaponmaster : CardDef :=
  legendaryCreature "Dwalin, Weaponmaster" (ManaCost.ofGenericAndHybrids 1 .red .white 1) #["Dwarf", "Warrior"] 2 1 (oracleText := "First strike\nWhenever Dwalin enters or attacks, put a hone counter on each Equipment you control. (Each hone counter on an Equipment grants +1/+0 to equipped creature.)")
    (keywords := Keyword.firstStrike)
    (triggeredAbilities := #[.printed "Whenever Dwalin enters or attacks, put a hone counter on each Equipment you control. (Each hone counter on an Equipment grants +1/+0 to equipped creature.)"])

def dainIronfoot : CardDef :=
  legendaryCreature "Dáin Ironfoot" (ManaCost.ofGenericAndColor 2 .red) #["Dwarf", "Warrior"] 1 4 (oracleText := "When Dáin enters, create a colorless Equipment artifact token named Axe with \"Equipped creature gets +1/+0\" and equip {2}. When you do, attach it to target creature you control.\nWhenever Dáin attacks, each equipped attacking creature gains double strike until end of turn.")
    (triggeredAbilities := #[
      .printed "When Dáin enters, create a colorless Equipment artifact token named Axe with \"Equipped creature gets +1/+0\" and equip {2}. When you do, attach it to target creature you control.",
      .printed "Whenever Dáin attacks, each equipped attacking creature gains double strike until end of turn."])

def elrondMoonReader : CardDef :=
  legendaryCreature "Elrond, Moon-Reader" (ManaCost.ofGenericAndColor 2 .blue) #["Elf", "Noble"] 3 3 (oracleText := "Whenever you activate an ability of a creature, draw a card. This ability triggers only once each turn.\n{5}{U}{U}: Exile up to two other target nonland permanents you control. Return those cards to the battlefield under their owner's control at the beginning of the next end step.")
    (staticAbilities := #[.printed "{5}{U}{U}: Exile up to two other target nonland permanents you control. Return those cards to the battlefield under their owner's control at the beginning of the next end step."])
    (triggeredAbilities := #[.printed "Whenever you activate an ability of a creature, draw a card. This ability triggers only once each turn."])

def elvenChorus : CardDef :=
  enchantment "Elven Chorus" (ManaCost.ofGenericAndColor 3 .green) "You may look at the top card of your library any time.\nYou may cast creature spells from the top of your library.\nCreatures you control have \"{T}: Add one mana of any color.\""
    (staticAbilities := #[.printed "You may look at the top card of your library any time.",
      .printed "You may cast creature spells from the top of your library.",
      .printed "Creatures you control have \"{T}: Add one mana of any color.\""])

def elvenPassage : CardDef :=
  land "Elven Passage" "{T}, Pay 1 life, Sacrifice this land: Search your library for a basic land card, put it onto the battlefield tapped, then shuffle. You may behold an Elf. If you do, untap that land. (To behold an Elf, choose an Elf you control or reveal an Elf card from your hand.)"
    (staticAbilities := #[.printed "{T}, Pay 1 life, Sacrifice this land: Search your library for a basic land card, put it onto the battlefield tapped, then shuffle. You may behold an Elf. If you do, untap that land. (To behold an Elf, choose an Elf you control or reveal an Elf card from your hand.)"])

def enchantedRiverSGrasp : CardDef :=
  aura "Enchanted River's Grasp" (ManaCost.ofGenericAndColor 2 .blue) "Enchant creature\nWhen this Aura enters, tap enchanted creature and remove all counters from it.\nEnchanted creature loses all abilities and doesn't untap during its controller's untap step."
    (staticAbilities := #[.enchantedLosesAbilitiesDoesntUntap])
    (triggeredAbilities := #[.printed "When this Aura enters, tap enchanted creature and remove all counters from it."])

def galadrielSDismissal : CardDef :=
  instant "Galadriel's Dismissal" (ManaCost.ofColor .white) "Kicker {2}{W} (You may pay an additional {2}{W} as you cast this spell.)\nTarget creature phases out. If this spell was kicked, each creature target player controls phases out instead. (Treat phased-out creatures and anything attached to them as though they don't exist until their controller's next turn.)" (some (.printed "Kicker {2}{W} (You may pay an additional {2}{W} as you cast this spell.)"))
    (staticAbilities := #[.printed "Target creature phases out. If this spell was kicked, each creature target player controls phases out instead. (Treat phased-out creatures and anything attached to them as though they don't exist until their controller's next turn.)"])

def galadrielLightOfValinor : CardDef :=
  legendaryCreature "Galadriel, Light of Valinor" (ManaCost.ofGenericAndColors 2 [.green, .white, .blue]) #["Elf", "Noble"] 3 3 (oracleText := "Alliance — Whenever another creature you control enters, choose one that hasn't been chosen this turn —\n• Add {G}{G}{G}.\n• Put a +1/+1 counter on each creature you control.\n• Scry 2, then draw a card.")
    (staticAbilities := #[.printed "Alliance — Whenever another creature you control enters, choose one that hasn't been chosen this turn — • Add {G}{G}{G}. • Put a +1/+1 counter on each creature you control. • Scry 2, then draw a card."])

def gandalfPartyGuest : CardDef :=
  legendaryCreature "Gandalf, Party Guest" (ManaCost.ofGenericAndColors 1 [.blue, .red, .white]) #["Avatar", "Wizard"] 3 4 (oracleText := "At the beginning of combat on your turn, you may cast an instant or sorcery spell with mana value X or less from your hand without paying its mana cost, where X is twice the number of legendary Wizards you control.")
    (triggeredAbilities := #[.printed "At the beginning of combat on your turn, you may cast an instant or sorcery spell with mana value X or less from your hand without paying its mana cost, where X is twice the number of legendary Wizards you control."])

def gandalfShadowSFoe : CardDef :=
  legendaryCreature "Gandalf, Shadow's Foe" (ManaCost.ofGenericAndColors 5 [.blue, .blue]) #["Avatar", "Wizard"] 3 4 (oracleText := "Vigilance\nWhen Gandalf enters, exile up to three target lands you control, then return them to the battlefield tapped under their owner's control.\nLandfall — Whenever a land you control enters, draw a card and put a +1/+1 counter on Gandalf.")
    (keywords := Keyword.vigilance)
    (staticAbilities := #[.printed "Landfall — Whenever a land you control enters, draw a card and put a +1/+1 counter on Gandalf."])
    (triggeredAbilities := #[.printed "When Gandalf enters, exile up to three target lands you control, then return them to the battlefield tapped under their owner's control."])

def getawayBarrel : CardDef :=
  artifact "Getaway Barrel" (ManaCost.ofGenericAndColor 3 .red) "When this artifact is put into a graveyard from the battlefield, reveal the top thirteen cards of your library. Put a random creature card from among them onto the battlefield. Put the rest on the bottom of your library in a random order."
    (triggeredAbilities := #[.printed "When this artifact is put into a graveyard from the battlefield, reveal the top thirteen cards of your library. Put a random creature card from among them onto the battlefield. Put the rest on the bottom of your library in a random order."])

def glamdring : CardDef :=
  artifact "Glamdring" (ManaCost.ofGeneric 2) "Equipped creature has first strike and gets +1/+0 for each instant and sorcery card in your graveyard.\nWhenever equipped creature deals combat damage to a player, you may cast an instant or sorcery spell from your hand with mana value less than or equal to that damage without paying its mana cost.\nEquip {3}"
    (subtypes := #["Equipment"])
    (supertypes := #[.legendary])
    (staticAbilities := #[.equippedFirstStrikePlusPerInstantSorcery])
    (triggeredAbilities := #[.printed "Whenever equipped creature deals combat damage to a player, you may cast an instant or sorcery spell from your hand with mana value less than or equal to that damage without paying its mana cost."])
    (activatedAbilities := #[equipAbility (ManaCost.ofGeneric 3)])

def gleamingSplendor : CardDef :=
  enchantment "Gleaming Splendor" (ManaCost.ofGenericAndColor 1 .white) "Whenever an opponent draws their second card each turn, you create a Treasure token.\n{2}{W}: Two target players each draw a card."
    (staticAbilities := #[.printed "{2}{W}: Two target players each draw a card."])
    (triggeredAbilities := #[.printed "Whenever an opponent draws their second card each turn, you create a Treasure token."])

def gollumRiddleMaster : CardDef :=
  legendaryCreature "Gollum, Riddle Master" (ManaCost.ofGenericAndColor 1 .black) #["Halfling", "Horror"] 3 1 (oracleText := "As Gollum enters, choose odd or even. (Zero is even.)\nWhenever an opponent casts a spell with mana value of the chosen quality, choose one that hasn't been chosen —\n• Put a +1/+1 counter on Gollum.\n• Each opponent loses 2 life and you gain 2 life.\n• Draw a card.")
    (staticAbilities := #[.printed "As Gollum enters, choose odd or even. (Zero is even.)"])
    (triggeredAbilities := #[.printed "Whenever an opponent casts a spell with mana value of the chosen quality, choose one that hasn't been chosen — • Put a +1/+1 counter on Gollum. • Each opponent loses 2 life and you gain 2 life. • Draw a card."])

def grimaSarumanSFootman : CardDef :=
  legendaryCreature "Gríma, Saruman's Footman" (ManaCost.ofGenericAndColors 2 [.blue, .black]) #["Human", "Advisor"] 1 4 (oracleText := "Gríma can't be blocked.\nWhenever Gríma deals combat damage to a player, that player exiles cards from the top of their library until they exile an instant or sorcery card. You may cast that card without paying its mana cost. Then that player puts the exiled cards that weren't cast this way on the bottom of their library in a random order.")
    (staticAbilities := #[.printed "Gríma can't be blocked."])
    (triggeredAbilities := #[.printed "Whenever Gríma deals combat damage to a player, that player exiles cards from the top of their library until they exile an instant or sorcery card. You may cast that card without paying its mana cost. Then that player puts the exiled cards that weren't cast this way on the bottom of their library in a random order."])

def headOfTheHunt : CardDef :=
  creature "Head of the Hunt" (ManaCost.ofGenericAndColors 2 [.black, .black]) #["Wolf"] 4 3 (oracleText := "Flash\nIf a creature an opponent controls would die, exile it instead. When you do, create a 2/2 green Wolf creature token.")
    (keywords := Keyword.flash)
    (staticAbilities := #[.printed "If a creature an opponent controls would die, exile it instead. When you do, create a 2/2 green Wolf creature token."])

def insideInformation : CardDef :=
  sorcery "Inside Information" ({ symbols := #[.x, .colored .black, .colored .black] }) "Exile the top X cards of target opponent's library. You may play those cards this turn. If you cast a spell this way, pay life equal to its mana value rather than pay its mana cost." (some (.printed "Exile the top X cards of target opponent's library. You may play those cards this turn. If you cast a spell this way, pay life equal to its mana value rather than pay its mana cost."))

def keyToTheSideDoor : CardDef :=
  artifact "Key to the Side-Door" (ManaCost.ofGeneric 1) "{2}, {T}: Target creature can't be blocked this turn.\n{1}, {T}, Discard a legendary card with the same name as a legendary permanent you control: Draw two cards."
    (staticAbilities := #[.printed "{2}, {T}: Target creature can't be blocked this turn.",
      .printed "{1}, {T}, Discard a legendary card with the same name as a legendary permanent you control: Draw two cards."])

def lakeTownToymaker : CardDef :=
  creature "Lake-town Toymaker" (ManaCost.ofGenericAndColor 3 .white) #["Human", "Artificer"] 3 4 (oracleText := "At the beginning of combat on your turn, if you've drawn two or more cards this turn, another target creature you control gets +3/+0 and gains first strike until end of turn.")
    (triggeredAbilities := #[.printed "At the beginning of combat on your turn, if you've drawn two or more cards this turn, another target creature you control gets +3/+0 and gains first strike until end of turn."])

def lastLightOfDurinSDay : CardDef :=
  enchantment "Last Light of Durin's Day" (ManaCost.ofGenericAndColor 1 .red) "Whenever a Mountain you control enters, put a quest counter on this enchantment. If it has six or more quest counters on it, sacrifice it. If you do, search your hand and/or library for a Dragon card and put it onto the battlefield. If you search your library this way, shuffle.\nMountaincycling {2} ({2}, Discard this card: Search your library for a Mountain card, reveal it, put it into your hand, then shuffle.)"
    (triggeredAbilities := #[.printed "Whenever a Mountain you control enters, put a quest counter on this enchantment. If it has six or more quest counters on it, sacrifice it. If you do, search your hand and/or library for a Dragon card and put it onto the battlefield. If you search your library this way, shuffle."])
    (activatedAbilities := #[typecyclingAbility "Mountain" (ManaCost.ofGeneric 2)])

def masterSCouncillors : CardDef :=
  creature "Master's Councillors" (ManaCost.ofGenericAndColor 1 .blue) #["Human", "Advisor"] 1 3 (oracleText := "Vigilance\nThis creature gets +2/+0 for each graveyard with seven or more cards in it.\nWhenever you draw your second card each turn, target player mills three cards. (They put the top three cards of their library into their graveyard.)")
    (keywords := Keyword.vigilance)
    (staticAbilities := #[.printed "This creature gets +2/+0 for each graveyard with seven or more cards in it."])
    (triggeredAbilities := #[.printed "Whenever you draw your second card each turn, target player mills three cards. (They put the top three cards of their library into their graveyard.)"])

def minasMorgulDarkFortress : CardDef :=
  legendaryLand "Minas Morgul, Dark Fortress" "Minas Morgul enters tapped.\n{T}: Add {B}.\n{3}{B}, {T}: Put a shadow counter on target creature. For as long as that creature has a shadow counter on it, it's a Wraith in addition to its other types. (A creature with shadow can block or be blocked by only creatures with shadow.)"
    (entersTapped := true)
    (tapAddMana := #[.colored .black])
    (staticAbilities := #[.printed "{3}{B}, {T}: Put a shadow counter on target creature. For as long as that creature has a shadow counter on it, it's a Wraith in addition to its other types. (A creature with shadow can block or be blocked by only creatures with shadow.)"])

def mountDoom : CardDef :=
  legendaryLand "Mount Doom" "{T}, Pay 1 life: Add {B} or {R}.\n{1}{B}{R}, {T}: Mount Doom deals 1 damage to each opponent.\n{5}{B}{R}, {T}, Sacrifice Mount Doom and a legendary artifact: Choose up to two creatures, then destroy the rest. Activate only as a sorcery."
    (tapPayLifeAddOneOf := some (1, #[.colored .black, .colored .red]))
    (staticAbilities := #[.printed "{1}{B}{R}, {T}: Mount Doom deals 1 damage to each opponent.",
      .printed "{5}{B}{R}, {T}, Sacrifice Mount Doom and a legendary artifact: Choose up to two creatures, then destroy the rest. Activate only as a sorcery."])

def oldFatSpiderCanTSeeMe : CardDef :=
  saga "Old Fat Spider Can't See Me" (ManaCost.ofGenericAndColor 2 .blue) "(As this Saga enters and after your draw step, add a lore counter. Sacrifice after IV.)\nI — Target creature you control gains hexproof for as long as this Saga remains on the battlefield.\nII — Prevent all damage that would be dealt by up to one target creature for as long as this Saga remains on the battlefield.\nIII, IV — Draw a card." "IV" #[{ roman := "I", effect := "Target creature you control gains hexproof for as long as this Saga remains on the battlefield." }, { roman := "II", effect := "Prevent all damage that would be dealt by up to one target creature for as long as this Saga remains on the battlefield." }, { roman := "III, IV", effect := "Draw a card." }]

def orcishBowmasters : CardDef :=
  creature "Orcish Bowmasters" (ManaCost.ofGenericAndColor 1 .black) #["Orc", "Archer"] 1 1 (oracleText := "Flash\nWhen this creature enters and whenever an opponent draws a card except the first one they draw in each of their draw steps, this creature deals 1 damage to any target. Then amass Orcs 1.")
    (keywords := Keyword.flash)
    (triggeredAbilities := #[.printed "When this creature enters and whenever an opponent draws a card except the first one they draw in each of their draw steps, this creature deals 1 damage to any target. Then amass Orcs 1."])

def orcristGoblinCleaver : CardDef :=
  artifact "Orcrist, Goblin-cleaver" (ManaCost.ofGeneric 3) "Equipped creature gets +2/+2 and has trample.\nWhenever equipped creature deals combat damage to a player, choose a creature type. Create a Treasure token for each creature you control of that type.\nEquip {3}"
    (subtypes := #["Equipment"])
    (supertypes := #[.legendary])
    (staticAbilities := #[.printed "Equipped creature gets +2/+2 and has trample."])
    (triggeredAbilities := #[.printed "Whenever equipped creature deals combat damage to a player, choose a creature type. Create a Treasure token for each creature you control of that type."])
    (activatedAbilities := #[equipAbility (ManaCost.ofGeneric 3)])

def palantirOfOrthanc : CardDef :=
  artifact "Palantír of Orthanc" (ManaCost.ofGeneric 3) "At the beginning of your end step, put an influence counter on Palantír of Orthanc and scry 2. Then target opponent may have you draw a card. If that player doesn't, you mill X cards, where X is the number of influence counters on Palantír of Orthanc, and that player loses life equal to the total mana value of those cards."
    (supertypes := #[.legendary])
    (triggeredAbilities := #[.printed "At the beginning of your end step, put an influence counter on Palantír of Orthanc and scry 2. Then target opponent may have you draw a card. If that player doesn't, you mill X cards, where X is the number of influence counters on Palantír of Orthanc, and that player loses life equal to the total mana value of those cards."])

def partInFriendship : CardDef :=
  enchantment "Part in Friendship" (ManaCost.ofGenericAndColor 4 .green) "Whenever a nontoken creature you control dies, reveal cards from the top of your library until you reveal a creature card. If its mana value is less than or equal to the number of lands you control, put it onto the battlefield. Otherwise, put it into your hand. Put the rest on the bottom of your library in a random order. This ability triggers only once each turn."
    (triggeredAbilities := #[.printed "Whenever a nontoken creature you control dies, reveal cards from the top of your library until you reveal a creature card. If its mana value is less than or equal to the number of lands you control, put it onto the battlefield. Otherwise, put it into your hand. Put the rest on the bottom of your library in a random order. This ability triggers only once each turn."])

def radagastOfRhosgobel : CardDef :=
  legendaryCreature "Radagast of Rhosgobel" (ManaCost.ofGenericAndColors 2 [.green, .green]) #["Avatar", "Wizard"] 2 5 (oracleText := "The first creature spell you cast each turn costs {2} less to cast and can be cast as though it had flash.")
    (staticAbilities := #[.printed "The first creature spell you cast each turn costs {2} less to cast and can be cast as though it had flash."])

def rhovanionRampager : CardDef :=
  creature "Rhovanion Rampager" (ManaCost.ofGenericAndColor 2 .black) #["Wolf"] 3 2 (oracleText := "Whenever this creature attacks, you may sacrifice another creature. If you do, put a number of +1/+1 counters on this creature equal to the sacrificed creature's power.\nWhen this creature dies, amass Goblins X, where X is this creature's power. (Put X +1/+1 counters on an Army you control. It's also a Goblin. If you don't control an Army, create a 0/0 black Goblin Army creature token first.)")
    (triggeredAbilities := #[.printed "Whenever this creature attacks, you may sacrifice another creature. If you do, put a number of +1/+1 counters on this creature equal to the sacrificed creature's power.",
      .printed "When this creature dies, amass Goblins X, where X is this creature's power. (Put X +1/+1 counters on an Army you control. It's also a Goblin. If you don't control an Army, create a 0/0 black Goblin Army creature token first.)"])

def riddlesInTheDark : CardDef :=
  instant "Riddles in the Dark" (ManaCost.ofGenericAndColor 2 .blue) "Look at the top four cards of your library and separate them into a face-down pile and a face-up pile. An opponent chooses one of the piles. Put that pile into your hand and the other into your graveyard." (some (.printed "Look at the top four cards of your library and separate them into a face-down pile and a face-up pile. An opponent chooses one of the piles. Put that pile into your hand and the other into your graveyard."))

def roadsGoEverEverOn : CardDef :=
  saga "Roads Go Ever, Ever On" (ManaCost.ofGenericAndColor 1 .white) "(As this Saga enters and after your draw step, add a lore counter. Sacrifice after IV.)\nI — Search your library for up to two basic Plains cards, exile them, then shuffle. You gain 2 life.\nII, III — Put a card exiled with this Saga into its owner's hand.\nIV — Whenever you attack this turn, target creature you control gets +1/+1 until end of turn for each Plains you control." "IV" #[{ roman := "I", effect := "Search your library for up to two basic Plains cards, exile them, then shuffle. You gain 2 life." }, { roman := "II, III", effect := "Put a card exiled with this Saga into its owner's hand." }, { roman := "IV", effect := "Whenever you attack this turn, target creature you control gets +1/+1 until end of turn for each Plains you control." }]

def rollRollRollRoll : CardDef :=
  saga "Roll-Roll-Roll-Roll" (ManaCost.ofGenericAndColor 2 .blue) "(As this Saga enters and after your draw step, add a lore counter. Sacrifice after IV.)\nI, II, III, IV — Exile up to one target creature or land you control. If you do, return it to the battlefield under its owner's control at the beginning of the next end step." "IV" #[{ roman := "I, II, III, IV", effect := "Exile up to one target creature or land you control. If you do, return it to the battlefield under its owner's control at the beginning of the next end step." }]

def sarumanOfManyColors : CardDef :=
  legendaryCreature "Saruman of Many Colors" (ManaCost.ofGenericAndColors 3 [.white, .blue, .black]) #["Avatar", "Wizard"] 5 4 (oracleText := "Ward—Discard an enchantment, instant, or sorcery card.\nWhenever you cast your second spell each turn, each opponent mills two cards. When one or more cards are milled this way, exile target enchantment, instant, or sorcery card with equal or lesser mana value than that spell from an opponent's graveyard. Copy the exiled card. You may cast the copy without paying its mana cost.")
    (staticAbilities := #[.printed "Ward—Discard an enchantment, instant, or sorcery card."])
    (triggeredAbilities := #[.printed "Whenever you cast your second spell each turn, each opponent mills two cards. When one or more cards are milled this way, exile target enchantment, instant, or sorcery card with equal or lesser mana value than that spell from an opponent's graveyard. Copy the exiled card. You may cast the copy without paying its mana cost."])

def sauronTheDarkLord : CardDef :=
  legendaryCreature "Sauron, the Dark Lord" (ManaCost.ofGenericAndColors 3 [.blue, .black, .red]) #["Avatar", "Horror"] 7 6 (oracleText := "Ward—Sacrifice a legendary artifact or legendary creature.\nWhenever an opponent casts a spell, amass Orcs 1.\nWhenever an Army you control deals combat damage to a player, the Ring tempts you.\nWhenever the Ring tempts you, you may discard your hand. If you do, draw four cards.")
    (staticAbilities := #[.printed "Ward—Sacrifice a legendary artifact or legendary creature."])
    (triggeredAbilities := #[.printed "Whenever an opponent casts a spell, amass Orcs 1.",
      .printed "Whenever an Army you control deals combat damage to a player, the Ring tempts you.",
      .printed "Whenever the Ring tempts you, you may discard your hand. If you do, draw four cards."])

def silvanReveler : CardDef :=
  creature "Silvan Reveler" (ManaCost.ofGenericAndColors 2 [.green, .blue]) #["Elf", "Citizen"] 3 2 (oracleText := "When this creature enters, draw a card, then discard a card. If you discard a land card this way, put it from your graveyard onto the battlefield tapped.\nLandfall — Whenever a land you control enters, you may pay {1}{G}{U}. If you do, return this card from your graveyard to your hand.")
    (staticAbilities := #[.printed "Landfall — Whenever a land you control enters, you may pay {1}{G}{U}. If you do, return this card from your graveyard to your hand."])
    (triggeredAbilities := #[.printed "When this creature enters, draw a card, then discard a card. If you discard a land card this way, put it from your graveyard onto the battlefield tapped."])

def smaugTheImpenetrable : CardDef :=
  legendaryCreature "Smaug the Impenetrable" (ManaCost.ofGenericAndColors 5 [.black, .red]) #["Dragon"] 8 7 (oracleText := "Flying, indestructible, haste\nWhenever Smaug is dealt noncombat damage, create that many Treasure tokens.")
    (keywords := Keyword.flying.merge Keyword.indestructible |>.merge Keyword.haste)
    (triggeredAbilities := #[.printed "Whenever Smaug is dealt noncombat damage, create that many Treasure tokens."])

def stingBilboSSword : CardDef :=
  artifact "Sting, Bilbo's Sword" (ManaCost.ofGeneric 2) "Flash\nWhen Sting enters, put a hone counter on Sting for each creature target opponent controls. Attach Sting to up to one target creature you control. (Each hone counter on an Equipment grants +1/+0 to equipped creature.)\nEquip {3}"
    (subtypes := #["Equipment"])
    (supertypes := #[.legendary])
    (keywords := Keyword.flash)
    (triggeredAbilities := #[.printed "When Sting enters, put a hone counter on Sting for each creature target opponent controls. Attach Sting to up to one target creature you control. (Each hone counter on an Equipment grants +1/+0 to equipped creature.)"])
    (activatedAbilities := #[equipAbility (ManaCost.ofGeneric 3)])

def stoneGiantOfHighPass : CardDef :=
  creature "Stone-Giant of High Pass" (ManaCost.ofGenericAndColors 5 [.red, .red]) #["Giant"] 7 7 (oracleText := "Whenever this creature enters or attacks, create a 3/1 colorless Wall artifact creature token with defender named Stone Boulder.\n{2}{R}, Sacrifice an artifact: This creature deals 4 damage to any target.")
    (staticAbilities := #[.printed "{2}{R}, Sacrifice an artifact: This creature deals 4 damage to any target."])
    (triggeredAbilities := #[.printed "Whenever this creature enters or attacks, create a 3/1 colorless Wall artifact creature token with defender named Stone Boulder."])

def supperForSpiders : CardDef :=
  instant "Supper for Spiders" (ManaCost.ofGenericAndColor 1 .black) "Put onto the battlefield under your control all creature cards in your opponents' graveyards that were put there from the battlefield this turn. They are Food artifacts with \"{2}, {T}, Sacrifice this artifact: You gain 3 life.\" (They lose all other types and subtypes.)" (some (.printed "Put onto the battlefield under your control all creature cards in your opponents' graveyards that were put there from the battlefield this turn. They are Food artifacts with \"{2}, {T}, Sacrifice this artifact: You gain 3 life.\" (They lose all other types and subtypes.)"))

def theBlackGate : CardDef :=
  legendaryLand "The Black Gate" "As The Black Gate enters, you may pay 3 life. If you don't, it enters tapped.\n{T}: Add {B}.\n{1}{B}, {T}: Choose a player with the most life or tied for most life. Target creature can't be blocked by creatures that player controls this turn."
    (entersTappedUnlessPayLife := some 3)
    (tapAddMana := #[.colored .black])
    (subtypes := #["Gate"])
    (staticAbilities := #[.printed "{1}{B}, {T}: Choose a player with the most life or tied for most life. Target creature can't be blocked by creatures that player controls this turn."])

def theEaglesAreComing : CardDef :=
  instant "The Eagles Are Coming!" (ManaCost.ofGenericAndColor 1 .white) "Kicker {2}{W}{W} (You may pay an additional {2}{W}{W} as you cast this spell.)\nChoose target creature you own. If this spell was kicked, instead choose any number of target creatures you own. Return each chosen creature to your hand. At the beginning of the next upkeep, create a 4/4 white Bird Soldier creature token with flying for each creature returned to your hand this way." (some (.printed "Kicker {2}{W}{W} (You may pay an additional {2}{W}{W} as you cast this spell.)"))
    (staticAbilities := #[.printed "Choose target creature you own. If this spell was kicked, instead choose any number of target creatures you own. Return each chosen creature to your hand. At the beginning of the next upkeep, create a 4/4 white Bird Soldier creature token with flying for each creature returned to your hand this way."])

def theGreatGoblin : CardDef :=
  legendaryCreature "The Great Goblin" (ManaCost.ofGenericAndHybrids 1 .black .red 2) #["Goblin", "Noble"] 3 2 (oracleText := "Whenever you put one or more counters on a Goblin, Orc, or Army you control, The Great Goblin deals 2 damage to target opponent.\nWhenever another Goblin, Orc, or Army you control dies, exile the top card of your library. You may play it until the end of your next turn.")
    (triggeredAbilities := #[.printed "Whenever you put one or more counters on a Goblin, Orc, or Army you control, The Great Goblin deals 2 damage to target opponent.",
      .printed "Whenever another Goblin, Orc, or Army you control dies, exile the top card of your library. You may play it until the end of your next turn."])

def theMasterOfLakeTown : CardDef :=
  legendaryCreature "The Master of Lake-town" (ManaCost.ofGenericAndColors 1 [.black, .black]) #["Human", "Advisor"] 3 2 (oracleText := "Deathtouch\nWhenever a player loses life, that player mills that many cards. (Damage causes loss of life.)\nWhen The Master of Lake-town dies, draw a card for each graveyard with seven or more cards in it.")
    (keywords := Keyword.deathtouch)
    (triggeredAbilities := #[.printed "Whenever a player loses life, that player mills that many cards. (Damage causes loss of life.)",
      .printed "When The Master of Lake-town dies, draw a card for each graveyard with seven or more cards in it."])

def theMistyMountainsCold : CardDef :=
  saga "The Misty Mountains Cold" (ManaCost.ofGenericAndColor 2 .red) "(As this Saga enters and after your draw step, add a lore counter. Sacrifice after IV.)\nI, II, III, IV — Create a Treasure token. Then if you control four or more Treasures, sacrifice this Saga. If you do, create a 6/6 red Dragon creature token with flying. (A Treasure token is an artifact with \"{T}, Sacrifice this token: Add one mana of any color.\")" "IV" #[{ roman := "I, II, III, IV", effect := "Create a Treasure token. Then if you control four or more Treasures, sacrifice this Saga. If you do, create a 6/6 red Dragon creature token with flying. (A Treasure token is an artifact with \"{T}, Sacrifice this token: Add one mana of any color.\")" }]

def theMountainKingSReturn : CardDef :=
  saga "The Mountain-king's Return" (ManaCost.ofGenericAndColor 2 .white) "(As this Saga enters and after your draw step, add a lore counter. Sacrifice after III.)\nI — Recruit. (Draw a card, then discard a card. If you discarded a nonland card, create a 1/1 white Human Soldier creature token.)\nII — Return target creature card with mana value 3 or less from your graveyard to the battlefield.\nIII — Put a +1/+1 counter on up to one target creature." "III" #[{ roman := "I", effect := "Recruit. (Draw a card, then discard a card. If you discarded a nonland card, create a 1/1 white Human Soldier creature token.)" }, { roman := "II", effect := "Return target creature card with mana value 3 or less from your graveyard to the battlefield." }, { roman := "III", effect := "Put a +1/+1 counter on up to one target creature." }]

def theNotaryHobbits : CardDef :=
  legendaryCreature "The Notary Hobbits" (ManaCost.ofGenericAndColors 3 [.green, .green]) #["Halfling", "Advisor"] 1 1 (oracleText := "When The Notary Hobbits enter, if they're not a token, create two tokens that are copies of them, except the tokens aren't legendary.\n{T}: Add {C} for each Halfling you control.")
    (tapAddColorlessPerSubtype := some "Halfling")
    (triggeredAbilities := #[.printed "When The Notary Hobbits enter, if they're not a token, create two tokens that are copies of them, except the tokens aren't legendary."])

def theOneRing : CardDef :=
  artifact "The One Ring" (ManaCost.ofGeneric 4) "Indestructible\nWhen The One Ring enters, if you cast it, you gain protection from everything until your next turn.\nAt the beginning of your upkeep, you lose 1 life for each burden counter on The One Ring.\n{T}: Put a burden counter on The One Ring, then draw a card for each burden counter on The One Ring."
    (supertypes := #[.legendary])
    (keywords := Keyword.indestructible)
    (staticAbilities := #[.printed "{T}: Put a burden counter on The One Ring, then draw a card for each burden counter on The One Ring."])
    (triggeredAbilities := #[.printed "When The One Ring enters, if you cast it, you gain protection from everything until your next turn.",
      .printed "At the beginning of your upkeep, you lose 1 life for each burden counter on The One Ring."])

def theReaverCleaver : CardDef :=
  artifact "The Reaver Cleaver" (ManaCost.ofGenericAndColor 2 .red) "Equipped creature gets +1/+1 and has trample and \"Whenever this creature deals combat damage to a player or planeswalker, create that many Treasure tokens.\"\nEquip {3}"
    (subtypes := #["Equipment"])
    (supertypes := #[.legendary])
    (staticAbilities := #[.printed "Equipped creature gets +1/+1 and has trample and \"Whenever this creature deals combat damage to a player or planeswalker, create that many Treasure tokens.\""])
    (activatedAbilities := #[equipAbility (ManaCost.ofGeneric 3)])

def theSackvilleBagginses : CardDef :=
  legendaryCreature "The Sackville-Bagginses" (ManaCost.ofGenericAndColor 1 .black) #["Halfling", "Citizen"] 2 2 (oracleText := "When The Sackville-Bagginses enter, you may sacrifice another creature or artifact. If you do, draw a card and create a Treasure token.\nWhenever you sacrifice a token, target opponent loses 1 life.")
    (triggeredAbilities := #[.printed "When The Sackville-Bagginses enter, you may sacrifice another creature or artifact. If you do, draw a card and create a Treasure token.",
      .printed "Whenever you sacrifice a token, target opponent loses 1 life."])

def thorinCompanySLeader : CardDef :=
  legendaryCreature "Thorin, Company's Leader" (ManaCost.ofGenericAndColor 4 .red) #["Dwarf", "Warrior"] 4 5 (oracleText := "Whenever a Dwarf you control deals combat damage to a player or battle, create two Treasure tokens.\n{10}: Creatures you control gain double strike until end of turn.")
    (staticAbilities := #[.printed "{10}: Creatures you control gain double strike until end of turn."])
    (triggeredAbilities := #[.printed "Whenever a Dwarf you control deals combat damage to a player or battle, create two Treasure tokens."])

def thorinMountainKing : CardDef :=
  legendaryCreature "Thorin, Mountain-king" (ManaCost.ofGenericAndColor 3 .red) #["Dwarf", "Noble"] 3 4 (oracleText := "Trample\nWhen Thorin enters, attach any number of target Equipment you control to target creature you control. When one or more Equipment become attached to that creature this way, that creature deals damage equal to its power to up to one target creature.")
    (keywords := Keyword.trample)
    (triggeredAbilities := #[.printed "When Thorin enters, attach any number of target Equipment you control to target creature you control. When one or more Equipment become attached to that creature this way, that creature deals damage equal to its power to up to one target creature."])

def thranduilSCompany : CardDef :=
  creature "Thranduil's Company" (ManaCost.ofGenericAndColors 2 [.green, .blue]) #["Elf", "Soldier"] 3 4 (oracleText := "As long as you control another Elf, you may play an additional land on each of your turns.\nLandfall — Whenever a land you control enters, put two +1/+1 counters on target creature you control. It gains vigilance until end of turn.")
    (extraLandIfOtherSubtype := some "Elf")
    (staticAbilities := #[.printed "Landfall — Whenever a land you control enters, put two +1/+1 counters on target creature you control. It gains vigilance until end of turn."])

def thranduilTheElvenking : CardDef :=
  legendaryCreature "Thranduil, the Elvenking" (ManaCost.ofGenericAndColors 2 [.black, .green, .blue]) #["Elf", "Noble"] 5 6 (oracleText := "Thranduil has all activated abilities of all Elf cards in your graveyard.\nWhenever another legendary Elf you control enters, draw two cards, then discard a card.")
    (staticAbilities := #[.printed "Thranduil has all activated abilities of all Elf cards in your graveyard."])
    (triggeredAbilities := #[.printed "Whenever another legendary Elf you control enters, draw two cards, then discard a card."])

def throughTheForestGate : CardDef :=
  sorcery "Through the Forest Gate" (ManaCost.ofGenericAndColors 6 [.green, .green]) "Look at the top twenty cards of your library, put any number of land cards from among them onto the battlefield tapped, then shuffle. You gain 8 life." (some (.printed "Look at the top twenty cards of your library, put any number of land cards from among them onto the battlefield tapped, then shuffle. You gain 8 life."))

def tomBombadil : CardDef :=
  legendaryCreature "Tom Bombadil" (ManaCost.ofColors [.white, .blue, .black, .red, .green]) #["God", "Bard"] 4 4 (oracleText := "As long as there are four or more lore counters among Sagas you control, Tom Bombadil has hexproof and indestructible.\nWhenever the final chapter ability of a Saga you control resolves, reveal cards from the top of your library until you reveal a Saga card. Put that card onto the battlefield and the rest on the bottom of your library in a random order. This ability triggers only once each turn.")
    (staticAbilities := #[.printed "As long as there are four or more lore counters among Sagas you control, Tom Bombadil has hexproof and indestructible."])
    (triggeredAbilities := #[.printed "Whenever the final chapter ability of a Saga you control resolves, reveal cards from the top of your library until you reveal a Saga card. Put that card onto the battlefield and the rest on the bottom of your library in a random order. This ability triggers only once each turn."])

def tomBertAndWilliam : CardDef :=
  legendaryCreature "Tom, Bert, and William" (ManaCost.ofGenericAndColors 3 [.black, .green]) #["Troll"] 5 5 (oracleText := "{1}, Sacrifice another creature: Draw cards equal to the sacrificed creature's power, then discard a card.\nWhen Tom, Bert, and William die, if they were a creature, return them to the battlefield. They're an artifact. (They're no longer a creature.)")
    (staticAbilities := #[.printed "{1}, Sacrifice another creature: Draw cards equal to the sacrificed creature's power, then discard a card."])
    (triggeredAbilities := #[.printed "When Tom, Bert, and William die, if they were a creature, return them to the battlefield. They're an artifact. (They're no longer a creature.)"])

def uncoverTheMoonLetters : CardDef :=
  enchantment "Uncover the Moon-Letters" (ManaCost.ofGenericAndColor 3 .blue) "Whenever you cast a noncreature spell, you may draw X cards, where X is the amount of mana spent to cast that spell. If you do, discard two cards."
    (triggeredAbilities := #[.printed "Whenever you cast a noncreature spell, you may draw X cards, where X is the amount of mana spent to cast that spell. If you do, discard two cards."])

def witchKingOfAngmar : CardDef :=
  legendaryCreature "Witch-king of Angmar" (ManaCost.ofGenericAndColors 3 [.black, .black]) #["Wraith", "Noble"] 5 3 (oracleText := "Flying\nWhenever one or more creatures deal combat damage to you, each opponent sacrifices a creature of their choice that dealt combat damage to you this turn. The Ring tempts you.\nDiscard a card: Witch-king of Angmar gains indestructible until end of turn. Tap him.")
    (keywords := Keyword.flying)
    (staticAbilities := #[.printed "Discard a card: Witch-king of Angmar gains indestructible until end of turn. Tap him."])
    (triggeredAbilities := #[.printed "Whenever one or more creatures deal combat damage to you, each opponent sacrifices a creature of their choice that dealt combat damage to you this turn. The Ring tempts you."])

def wizardSStaff : CardDef :=
  artifact "Wizard's Staff" (ManaCost.ofGenericAndColor 1 .blue) "Equipped creature has prowess. (Whenever its controller casts a noncreature spell, that creature gets +1/+1 until end of turn.)\nIf a triggered ability of equipped creature triggers, that ability triggers an additional time.\nEquip Wizard {1}\nEquip {3}"
    (subtypes := #["Equipment"])
    (staticAbilities := #[.equippedTriggersAgain,
      .printed "Equipped creature has prowess. (Whenever its controller casts a noncreature spell, that creature gets +1/+1 until end of turn.)"])
    (activatedAbilities := #[equipAbility (ManaCost.ofGeneric 1) (subtype := some "Wizard"),
      equipAbility (ManaCost.ofGeneric 3)])

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
  anUnexpectedParty,
  ironHillsBlacksmith,
  thorinKingOfDurinsFolk,
  gandalfGoblinsBane,
  bilboUnexpectedAdventurer,
  alongTheCrookedWay,
  andurilFlameOfTheWest,
  andurilNarsilReforged,
  aragornTheUniter,
  arwenMortalQueen,
  arwenWeaverOfHope,
  azogMoriaSRuin,
  balinLoremaster,
  bardTheBowman,
  bardKingOfDale,
  bejeweledWarg,
  belladonnaTook,
  beornTheFierce,
  bifurMelodicRider,
  bilboSBurglaring,
  bilboSGambit,
  bilboSRing,
  bilboFellowConspirator,
  bilboThiefInTheNight,
  bolgOfTheNorth,
  boughsideWanderers,
  burnBurnTreeAndFern,
  callForthTheTempest,
  cantankerousKeepers,
  cavernHoardDragon,
  celebrateTheMountainKing,
  chiefOfTheWilds,
  dancingFromDarkToDawn,
  desertWereWorm,
  downInTheValley,
  downDownToGoblinTown,
  dragonCursedHalls,
  dwalinWeaponmaster,
  dainIronfoot,
  elrondMoonReader,
  elvenChorus,
  elvenPassage,
  enchantedRiverSGrasp,
  galadrielSDismissal,
  galadrielLightOfValinor,
  gandalfPartyGuest,
  gandalfShadowSFoe,
  getawayBarrel,
  glamdring,
  gleamingSplendor,
  gollumRiddleMaster,
  grimaSarumanSFootman,
  headOfTheHunt,
  insideInformation,
  keyToTheSideDoor,
  lakeTownToymaker,
  lastLightOfDurinSDay,
  masterSCouncillors,
  minasMorgulDarkFortress,
  mountDoom,
  oldFatSpiderCanTSeeMe,
  orcishBowmasters,
  orcristGoblinCleaver,
  palantirOfOrthanc,
  partInFriendship,
  radagastOfRhosgobel,
  rhovanionRampager,
  riddlesInTheDark,
  roadsGoEverEverOn,
  rollRollRollRoll,
  sarumanOfManyColors,
  sauronTheDarkLord,
  silvanReveler,
  smaugTheImpenetrable,
  stingBilboSSword,
  stoneGiantOfHighPass,
  supperForSpiders,
  theBlackGate,
  theEaglesAreComing,
  theGreatGoblin,
  theMasterOfLakeTown,
  theMistyMountainsCold,
  theMountainKingSReturn,
  theNotaryHobbits,
  theOneRing,
  theReaverCleaver,
  theSackvilleBagginses,
  thorinCompanySLeader,
  thorinMountainKing,
  thranduilSCompany,
  thranduilTheElvenking,
  throughTheForestGate,
  tomBombadil,
  tomBertAndWilliam,
  uncoverTheMoonLetters,
  witchKingOfAngmar,
  wizardSStaff
]

end Mtg.Engine.Catalog.HobbitSet
