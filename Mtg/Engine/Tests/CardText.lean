import Mtg.Engine.Agent
import Mtg.Engine.Catalog
import Mtg.Engine.Catalog.Hobbit
import Mtg.Engine.Catalog.HobbitEternal
import Mtg.Engine.Catalog.MarvelSuperHeroes
import Mtg.Engine.Game
import Mtg.Engine.Oracle
import Mtg.Engine.Tests.Helpers

/-!
# Catalog summary and printed-text smoke tests.
-/

namespace Mtg.Engine.Tests

open Mtg.Engine
open Mtg.Engine.Catalog


/- Hands, battlefield, and other zones print keywords and abilities. -/
#guard mentions ragingGoblin.summary "haste"
#guard mentions giantSpider.summary "reach"
#guard mentions llanowarElves.summary "{T}: Add {G}"
#guard mentions lightningBolt.summary "deals 3 damage"
#guard mentions lightningBolt.summary "{R}"
#guard mentions mountain.summary "{T}: Add {R}"
#guard !mentions mountain.summary "{0}"
#guard !mentions forest.summary "{0}"
#guard !mentions roguesPassage.summary "{0}"
#guard mentions wayfarersBauble.summary "Search your library"
#guard mentions attercop.summary "reach"
#guard mentions attercop.summary "deathtouch"
#guard mentions attercop.summary "Landfall"
#guard attercop.keywords.reach
#guard attercop.keywords.deathtouch
#guard attercop.triggeredAbilities.size == 1
#guard attercop.triggeredAbilities == #[(.onLandYouControlEntersGets 1 1)]
#guard mentions landrovalHorizonWitness.summary "flying"
#guard mentions landrovalHorizonWitness.summary "Whenever two or more creatures"
#guard mentions soldierOfTheGreyHost.summary "flash"
#guard mentions soldierOfTheGreyHost.summary "flying"
#guard mentions roguesPassage.summary "{T}: Add {C}"
#guard mentions roguesPassage.summary "can't be blocked"
#guard roguesPassage.activatedAbilities.size == 1
#guard roguesPassage.activatedAbilities[0]!.effect == Effect.targetCantBeBlockedThisTurn
#guard roguesPassage.activatedAbilities[0]!.cost.tap
#guard roguesPassage.activatedAbilities[0]!.cost.mana == ManaCost.ofGeneric 4
#guard mentions orcishSiegemaster.summary "trample"
#guard mentions orcishSiegemaster.summary "Other Orcs and Goblins"
#guard mentions orcishSiegemaster.summary "greatest power"
#guard orcishSiegemaster.staticAbilities.size == 1
#guard orcishSiegemaster.triggeredAbilities.size == 1
#guard mentions battleScarredGoblin.summary "becomes blocked"
#guard battleScarredGoblin.triggeredAbilities.size == 1
#guard mentions giftOfStrands.summary "flash"
#guard mentions giftOfStrands.summary "Enchanted creature"
#guard giftOfStrands.staticAbilities.size == 1
#guard giftOfStrands.triggeredAbilities.size == 1
#guard mentions raggedShortSpear.summary "Equipped creature"
#guard mentions raggedShortSpear.summary "Equip"
#guard raggedShortSpear.isEquipment
#guard hawkeyeSBow.isEquipment
#guard hawkeyeSBow.staticAbilities == #[.equippedCreatureGetsAndHas 1 0 Keyword.reach]
#guard hawkeyeSBow.triggeredAbilities == #[.onWatch Effect.watchEquippedTappedDamage]
#guard hawkeyeSBow.activatedAbilities.size == 1
#guard hawkeyeSBow.activatedAbilities[0]!.onlyAsSorcery
#guard hawkeyeSBow.activatedAbilities[0]!.effect == Effect.attachToTargetCreatureYouControl
#guard hawkeyeSBow.activatedAbilities[0]!.cost.mana == (ManaCost.ofGeneric 1)
#guard mentions hawkeyeSBow.summary "Equipped creature"
#guard mentions hawkeyeSBow.summary "becomes tapped"
#guard mentions hawkeyeSBow.summary "Equip"
#guard raggedShortSpear.staticAbilities.size == 1
#guard raggedShortSpear.triggeredAbilities.size == 1
#guard raggedShortSpear.activatedAbilities.size == 1
#guard mentions crudeBentBlade.summary "Equipped creature"
#guard mentions crudeBentBlade.summary "Equip"
#guard mentions crudeBentBlade.summary "target opponent"
#guard crudeBentBlade.isEquipment
#guard crudeBentBlade.staticAbilities.size == 1
#guard crudeBentBlade.triggeredAbilities.size == 1
#guard crudeBentBlade.activatedAbilities.size == 1
#guard crudeBentBlade.triggeredAbilities == #[.onEnterTargetOpponentSacrificesCreature]
#guard mentions galadhrimGuide.summary "scry 2"
#guard galadhrimGuide.triggeredAbilities.size == 1
#guard galadhrimGuide.triggeredAbilities == #[.onEnterScry 2]
#guard mentions elvishVisionary.summary "draw a card"
#guard elvishVisionary.triggeredAbilities.size == 1
#guard elvishVisionary.triggeredAbilities == #[.onEnterDraw 1]
#guard mentions quarrel.summary "deals damage equal to its power"
#guard quarrel.isInstant
#guard quarrel.requiresTarget
#guard quarrel.spellEffect == some (Effect.creatureYouControlDealsPowerToOppCreature)
#guard mentions smiteTheDeathless.summary "loses indestructible"
#guard mentions smiteTheDeathless.summary "exile it instead"
#guard smiteTheDeathless.isInstant
#guard smiteTheDeathless.requiresTarget
#guard smiteTheDeathless.spellEffect == some (Effect.dealDamageLoseIndestructibleExile 3)
#guard mentions woodElves.summary "Forest card"
#guard woodElves.triggeredAbilities.size == 1
#guard woodElves.triggeredAbilities == #[.onEnterSearchForest]
#guard mentions elvishArchdruid.summary "Other Elf creatures"
#guard mentions elvishArchdruid.summary "for each Elf"
#guard elvishArchdruid.staticAbilities.size == 1
#guard elvishArchdruid.staticAbilities == #[.otherCreaturesGet #["Elf"] 1 1]
#guard elvishArchdruid.tapAddManaForEach == #[{ mana := .colored .green, subtype := "Elf" }]
#guard mentions mirkwoodElk.summary "trample"
#guard mentions mirkwoodElk.summary "Elf card"
#guard mirkwoodElk.keywords.trample
#guard mirkwoodElk.triggeredAbilities.size == 1
#guard mirkwoodElk.triggeredAbilities == #[.onEnterOrAttackReturnElfGainLife]
#guard mentions celebornTheWise.summary "one or more Elves"
#guard mentions celebornTheWise.summary "looked at"
#guard celebornTheWise.triggeredAbilities.size == 2
#guard celebornTheWise.triggeredAbilities ==
  #[.onAttackWithElvesScry 1, .onScryPumpSelfForEachLookedAt]
#guard mentions galionElvenkingsButler.summary "base power and toughness"
#guard galionElvenkingsButler.triggeredAbilities.size == 1
#guard galionElvenkingsButler.triggeredAbilities == #[.onAttackSetOtherBasePT]
#guard mentions lothlorienLookout.summary "scry 1"
#guard lothlorienLookout.triggeredAbilities.size == 1
#guard lothlorienLookout.triggeredAbilities == #[.onAttackScry 1]
#guard mentions woodlandWeavemaster.summary "vigilance"
#guard mentions woodlandWeavemaster.summary "another Elf"
#guard mentions woodlandWeavemaster.summary "any one color"
#guard woodlandWeavemaster.keywords.vigilance
#guard woodlandWeavemaster.triggeredAbilities.size == 1
#guard woodlandWeavemaster.triggeredAbilities == #[.onAnotherElfYouControlEntersGets1]
#guard woodlandWeavemaster.tapAddAnyColorEqualToPower
#guard mentions oliphaunt.summary "trample"
#guard mentions oliphaunt.summary "+2/+0"
#guard mentions oliphaunt.summary "Mountaincycling"
#guard oliphaunt.keywords.trample
#guard oliphaunt.triggeredAbilities.size == 1
#guard oliphaunt.triggeredAbilities == #[.onAttackOtherGets2AndTrample]
#guard oliphaunt.activatedAbilities.size == 1
#guard oliphaunt.activatedAbilities[0]!.effect == Effect.searchLandTypeToHand "Mountain"
#guard mentions wargTactics.summary "Choose one"
#guard mentions wargTactics.summary "hexproof"
#guard wargTactics.isModal
#guard wargTactics.modes.size == 2
#guard mentions goblinCratermaker.summary "Choose one"
#guard mentions goblinCratermaker.summary "colorless nonland"
#guard goblinCratermaker.activatedAbilities.size == 1
#guard mentions beornsHospitality.summary "Landfall"
#guard mentions beornsHospitality.summary "Bear creature"
#guard beornsHospitality.triggeredAbilities.size == 1
#guard beornsHospitality.activatedAbilities.size == 1
#guard mentions mirkwoodPathmaker.summary "lands you control"
#guard mentions mirkwoodPathmaker.summary "*/*"
#guard mirkwoodPathmaker.staticAbilities.size == 1
#guard mirkwoodPathmaker.power.isNone
#guard mirkwoodPathmaker.toughness.isNone
#guard mentions ologHaiCrusher.summary "trample"
#guard mentions ologHaiCrusher.summary "can't block unless"
#guard ologHaiCrusher.keywords.trample
#guard ologHaiCrusher.staticAbilities.size == 1
#guard ologHaiCrusher.staticAbilities == #[.cantBlockUnlessYouControl #["Goblin", "Orc"]]
#guard mentions gandalfSparkStarter.summary "reach"
#guard mentions gandalfSparkStarter.summary "divided as you choose"
#guard gandalfSparkStarter.keywords.reach
#guard gandalfSparkStarter.triggeredAbilities.size == 1
#guard gandalfSparkStarter.triggeredAbilities == #[.onEnterDealDividedDamage 3 3]
#guard mentions goblinFireleaper.summary "+1/+0"
#guard mentions goblinFireleaper.summary "dies"
#guard goblinFireleaper.activatedAbilities.size == 1
#guard goblinFireleaper.triggeredAbilities.size == 1
#guard goblinFireleaper.triggeredAbilities == #[.onDiesDealDamageEqualToPowerToOppCreature]
#guard mentions desolationProwler.summary "Pay 2 life"
#guard mentions desolationProwler.summary "+2/+2"
#guard desolationProwler.activatedAbilities.size == 1
#guard desolationProwler.activatedAbilities[0]!.effect == Effect.sourceGets 2 2
#guard desolationProwler.activatedAbilities[0]!.cost.payLife == 2
#guard desolationProwler.activatedAbilities[0]!.onceEachTurn
#guard mentions raveningWarg.summary "deathtouch"
#guard mentions raveningWarg.summary "Ferocious"
#guard mentions raveningWarg.summary "power 4 or greater"
#guard raveningWarg.keywords.deathtouch
#guard raveningWarg.triggeredAbilities.size == 1
#guard raveningWarg.triggeredAbilities == #[.onAttackFerociousGainLife 2]
#guard mentions gollumSilentSlinker.summary "menace"
#guard !mentions gollumSilentSlinker.summary "can't be blocked except"
#guard gollumSilentSlinker.keywords.menace
#guard gollumSilentSlinker.power == some 4
#guard gollumSilentSlinker.toughness == some 3
#guard mentions bilbosDeadlySlice.summary "Destroy target creature"
#guard bilbosDeadlySlice.isInstant
#guard bilbosDeadlySlice.spellEffect == some (Effect.destroyCreature)
#guard bilbosDeadlySlice.requiresTarget
#guard bilbosDeadlySlice.hasCastKind .destroyCreature
#guard mentions infernoTitan.summary "+1/+0"
#guard mentions infernoTitan.summary "divided as you choose"
#guard infernoTitan.activatedAbilities.size == 1
#guard infernoTitan.triggeredAbilities.size == 1
#guard infernoTitan.triggeredAbilities == #[.onEnterOrAttackDealDividedDamage 3 3]
#guard mentions guttersnipe.summary "instant or sorcery"
#guard mentions guttersnipe.summary "each opponent"
#guard guttersnipe.triggeredAbilities.size == 1
#guard guttersnipe.triggeredAbilities == #[.onCastInstantOrSorceryDealDamageToEachOpponent 2]
#guard mentions guardianOfTheHalls.summary "trample"
#guard mentions guardianOfTheHalls.summary "+1/+1"
#guard guardianOfTheHalls.keywords.trample
#guard guardianOfTheHalls.activatedAbilities.size == 1
#guard guardianOfTheHalls.activatedAbilities[0]!.effect == Effect.putPlusOnePlusOneOnSource 3
#guard guardianOfTheHalls.activatedAbilities[0]!.cost.mana ==
  ManaCost.ofGenericAndColors 5 [.green, .green]
#guard mentions improvisedClub.summary "additional cost"
#guard mentions improvisedClub.summary "4 damage"
#guard improvisedClub.isInstant
#guard improvisedClub.spellEffect == some (Effect.dealDamage 4)
#guard improvisedClub.additionalCostSacrificeArtifactOrCreature
#guard improvisedClub.requiresTarget
#guard mentions fireOfOrthanc.summary "artifact or land"
#guard mentions fireOfOrthanc.summary "can't block this turn"
#guard fireOfOrthanc.isSorcery
#guard fireOfOrthanc.spellEffect == some (Effect.destroyArtifactOrLandNonflyersCantBlock)
#guard fireOfOrthanc.requiresTarget
#guard mentions smaugTheGreatCalamity.summary "flying"
#guard mentions smaugTheGreatCalamity.summary "Spew Flame"
#guard smaugTheGreatCalamity.keywords.flying
#guard smaugTheGreatCalamity.hasAdventure
#guard mentions beornReluctantHost.summary "trample"
#guard mentions beornReluctantHost.summary "Till and Tend"
#guard mentions beornReluctantHost.summary "additional land"
#guard beornReluctantHost.keywords.trample
#guard beornReluctantHost.hasAdventure

/- Structured abilities still print when Oracle text is absent. -/
#guard
  let c := creature "Silent Elves" ManaCost.empty #[] 1 1
    (tapAddMana := #[.colored .green])
  mentions c.abilitiesText "{T}: Add {G}" &&
    mentions c.summary "{T}: Add {G}" &&
    !mentions c.summary "{0}"

#guard
  let c := creature "Silent Ornithopter" { symbols := #[.generic 0] } #[] 0 2
  mentions c.summary "{0}"

#guard
  let c := creature "Silent Siege" ManaCost.empty #[] 0 5
    (keywords := Keyword.trample)
    (staticAbilities := #[.otherCreaturesHaveTrample #["Orc", "Goblin"]])
    (triggeredAbilities := #[.onAttackPumpByGreatestPower])
  mentions c.abilitiesText "Other Orcs and Goblins" &&
    mentions c.abilitiesText "greatest power" &&
    mentions c.summary "trample"

#guard
  let c := creature "Silent Scar" ManaCost.empty #[] 2 2
    (triggeredAbilities := #[.onBecomesBlockedDeal1ToBlockers])
  mentions c.abilitiesText "becomes blocked" &&
    mentions c.abilitiesText "each creature blocking it"

#guard
  let c := aura "Silent Strands" ManaCost.empty ""
    (keywords := Keyword.flash)
    (staticAbilities := #[.enchantedCreatureGets 3 3])
    (triggeredAbilities := #[.onEnterScry 2])
  mentions c.abilitiesText "Enchanted creature gets +3/+3" &&
    mentions c.abilitiesText "scry 2" &&
    mentions c.summary "flash"

#guard
  let c := creature "Silent Visionary" ManaCost.empty #[] 1 1
    (triggeredAbilities := #[.onEnterDraw 1])
  mentions c.abilitiesText "draw a card"

#guard
  let c := creature "Silent Wood Elves" ManaCost.empty #[] 1 1
    (triggeredAbilities := #[.onEnterSearchForest])
  mentions c.abilitiesText "Forest card" &&
    mentions c.abilitiesText "onto the battlefield"

#guard
  let c := creature "Silent Archdruid" ManaCost.empty #["Elf", "Druid"] 2 2
    (staticAbilities := #[.otherCreaturesGet #["Elf"] 1 1])
    (tapAddManaForEach := #[{ mana := .colored .green, subtype := "Elf" }])
  mentions c.abilitiesText "Other Elf creatures you control get +1/+1" &&
    mentions c.abilitiesText "{T}: Add {G} for each Elf you control" &&
    !mentions c.abilitiesText "{T}: Add {G};" &&
    c.manaAbilities == #[.colored .green]

#guard
  let c := creature "Silent Weavemaster" ManaCost.empty #["Elf", "Druid"] 1 2
    (keywords := Keyword.vigilance)
    (triggeredAbilities := #[.onAnotherElfYouControlEntersGets1])
    (tapAddAnyColorEqualToPower := true)
  mentions c.summary "vigilance" &&
    mentions c.abilitiesText "another Elf you control enters" &&
    mentions c.abilitiesText "any one color" &&
    mentions c.abilitiesText "Elf spells" &&
    c.tapAddAnyColorEqualToPower &&
    c.manaAbilities.size == 5

#guard
  let c := artifact "Silent Spear" ManaCost.empty ""
    (subtypes := #["Equipment"])
    (staticAbilities := #[.equippedCreatureGets 2 0])
    (triggeredAbilities := #[.onEnterMayDiscardDraw 2])
    (activatedAbilities := #[equipAbility (ManaCost.ofGeneric 3)])
  mentions c.abilitiesText "Equipped creature gets +2/+0" &&
    mentions c.abilitiesText "you may discard a card" &&
    mentions c.abilitiesText "Attach this Equipment" &&
    mentions c.abilitiesText "activate only as a sorcery"

#guard
  let c := artifact "Silent Blade" ManaCost.empty ""
    (subtypes := #["Equipment"])
    (staticAbilities := #[.equippedCreatureGets 2 1])
    (triggeredAbilities := #[.onEnterTargetOpponentSacrificesCreature])
    (activatedAbilities := #[equipAbility (ManaCost.ofGeneric 2)])
  mentions c.abilitiesText "Equipped creature gets +2/+1" &&
    mentions c.abilitiesText "target opponent sacrifices a creature" &&
    mentions c.abilitiesText "Attach this Equipment" &&
    mentions c.abilitiesText "activate only as a sorcery"

#guard
  let c := enchantment "Silent Hospitality" ManaCost.empty ""
    (triggeredAbilities := #[.onLandYouControlEntersPlusOnePlusOne])
    (activatedAbilities := #[
      activated (Effect.becomeBearCreatureWithLandsPT)
        (ManaCost.ofGenericAndColors 5 [.green, .green])])
  mentions c.abilitiesText "land you control enters" &&
    mentions c.abilitiesText "Bear creature" &&
    mentions c.abilitiesText "{5}{G}{G}"

#guard
  let c := creature "Silent Attercop" ManaCost.empty #["Spider"] 2 1
    (keywords := Keyword.reach.merge Keyword.deathtouch)
    (triggeredAbilities := #[(.onLandYouControlEntersGets 1 1)])
  mentions c.summary "reach" &&
    mentions c.summary "deathtouch" &&
    mentions c.abilitiesText "land you control enters" &&
    mentions c.abilitiesText "+1/+1 until end of turn"

#guard
  let c := card "Silent Pathmaker" #[.creature]
    (staticAbilities := #[.powerToughnessEqualLandsYouControl])
  mentions c.abilitiesText "lands you control" &&
    mentions c.summary "*/*"

#guard
  let c := card "Silent Crusher" #[.creature]
    (keywords := Keyword.trample)
    (staticAbilities := #[.cantBlockUnlessYouControl #["Goblin", "Orc"]])
  mentions c.abilitiesText "can't block unless you control a Goblin or Orc" &&
    mentions c.summary "trample"

#guard
  let c := card "Silent Spark" #[.creature]
    (keywords := Keyword.reach)
    (triggeredAbilities := #[.onEnterDealDividedDamage 3 3])
  mentions c.abilitiesText "divided as you choose" &&
    mentions c.abilitiesText "one, two, or three" &&
    mentions c.summary "reach"

#guard
  let c := card "Silent Fireleaper" #[.creature]
    (activatedAbilities := #[
      activated (Effect.sourceGets 1 0) (ManaCost.ofGenericAndColor 1 .red)])
    (triggeredAbilities := #[.onDiesDealDamageEqualToPowerToOppCreature])
  mentions c.abilitiesText "+1/+0" &&
    mentions c.abilitiesText "dies" &&
    mentions c.abilitiesText "{1}{R}"

#guard
  let c := land "Silent Passage" ""
    (tapAddMana := #[.colorless])
    (activatedAbilities := #[
      activated (Effect.targetCantBeBlockedThisTurn) (ManaCost.ofGeneric 4) (tap := true)])
  mentions c.abilitiesText "{T}: Add {C}" &&
    mentions c.abilitiesText "can't be blocked this turn" &&
    mentions c.abilitiesText "{4}" &&
    mentions c.abilitiesText "{T}"

#guard
  let c := card "Silent Titan" #[.creature]
    (activatedAbilities := #[activated (Effect.sourceGets 1 0) (ManaCost.ofColor .red)])
    (triggeredAbilities := #[.onEnterOrAttackDealDividedDamage 3 3])
  mentions c.abilitiesText "+1/+0" &&
    mentions c.abilitiesText "enters or attacks" &&
    mentions c.abilitiesText "divided as you choose" &&
    mentions c.abilitiesText "{R}"

#guard
  let c := creature "Silent Elk" ManaCost.empty #[] 6 6
    (keywords := Keyword.trample)
    (triggeredAbilities := #[.onEnterOrAttackReturnElfGainLife])
  mentions c.abilitiesText "Elf card" &&
    mentions c.abilitiesText "graveyard" &&
    mentions c.abilitiesText "gain life" &&
    mentions c.summary "trample"

#guard
  let c := creature "Silent Celeborn" ManaCost.empty #[] 3 3
    (triggeredAbilities := #[.onAttackWithElvesScry 1, .onScryPumpSelfForEachLookedAt])
  mentions c.abilitiesText "one or more Elves" &&
    mentions c.abilitiesText "scry 1" &&
    mentions c.abilitiesText "looked at"

#guard
  let c := creature "Silent Snipe" ManaCost.empty #[] 2 2
    (triggeredAbilities := #[.onCastInstantOrSorceryDealDamageToEachOpponent 2])
  mentions c.abilitiesText "instant or sorcery" &&
    mentions c.abilitiesText "each opponent"

#guard
  let c := creature "Silent Guardian" ManaCost.empty #[] 2 2
    (keywords := Keyword.trample)
    (activatedAbilities := #[
      activated (Effect.putPlusOnePlusOneOnSource 3)
        (ManaCost.ofGenericAndColors 5 [.green, .green])])
  mentions c.abilitiesText "Put 3 +1/+1 counters" &&
    mentions c.abilitiesText "{5}{G}{G}" &&
    mentions c.summary "trample"

#guard
  let c := creature "Silent Butler" ManaCost.empty #[] 4 4
    (triggeredAbilities := #[.onAttackSetOtherBasePT])
  mentions c.abilitiesText "up to one other target" &&
    mentions c.abilitiesText "base power and toughness"

#guard
  let c := creature "Silent Lookout" ManaCost.empty #[] 1 3
    (triggeredAbilities := #[.onAttackScry 1])
  mentions c.abilitiesText "Whenever this creature attacks" &&
    mentions c.abilitiesText "scry 1"

#guard
  let c := creature "Silent Warg" ManaCost.empty #["Wolf"] 2 2
    (keywords := Keyword.deathtouch)
    (triggeredAbilities := #[.onAttackFerociousGainLife 2])
  mentions c.summary "deathtouch" &&
    mentions c.abilitiesText "power 4 or greater" &&
    mentions c.abilitiesText "you gain 2 life"

#guard
  let c := creature "Silent Slinker" ManaCost.empty #[] 4 3
    (oracleText := "Menace (This creature can't be blocked except by two or more creatures.)")
    (keywords := Keyword.menace)
  mentions c.summary "menace" &&
    !mentions c.summary "can't be blocked except" &&
    CardDef.isKeywordRestatement c.keywords c.oracleText

#guard
  let c := creature "Silent Oliphaunt" ManaCost.empty #[] 6 4
    (keywords := Keyword.trample)
    (triggeredAbilities := #[.onAttackOtherGets2AndTrample])
  mentions c.abilitiesText "+2/+0" &&
    mentions c.abilitiesText "gains trample" &&
    mentions c.summary "trample"

end Mtg.Engine.Tests
