import Mtg.Engine.Agent
import Mtg.Engine.Catalog
import Mtg.Engine.Catalog.Hobbit
import Mtg.Engine.Catalog.HobbitEternal
import Mtg.Engine.Catalog.MarvelSuperHeroes
import Mtg.Engine.Game
import Mtg.Engine.Oracle
import Mtg.Engine.Tests.Helpers
import Mtg.Engine.Tests.Turns
import Mtg.Engine.Tests.Auras
import Mtg.Engine.Tests.Abilities

/-!
# Optional and sequential spell targets.
-/

namespace Mtg.Engine.Tests

open Mtg.Engine
open Mtg.Engine.Catalog

/- Meager Meal (Gollum adventure): up to one target creature, then target
player, in that card-text order (CR 601.2c / 115.1c). -/

#guard (Effect.plusOneUpToOneAndPlayerGainsLife 2).targetKind ==
  .upToOneCreatureThenPlayer
#guard (Effect.plusOneUpToOneAndPlayerGainsLife 2).targetCount == 2
#guard
  match gollumSilentSlinker.adventure with
  | some adv => adv.spellEffect == some (Effect.plusOneUpToOneAndPlayerGainsLife 2)
  | none => false

/-- Gollum in hand, a creature you control, an opposing creature, and {B}. -/
def meagerMealSetup : Game :=
  let g := addPermanent afterDraw grizzlyBears ⟨0⟩ ⟨0⟩
  let g := addPermanent g grayOgre ⟨1⟩ ⟨1⟩
  let g := readyMain (emptyHand g ⟨0⟩)
  withBlackMana (addToHand g gollumSilentSlinker ⟨0⟩) ⟨0⟩ 1

#guard meagerMealSetup.canCastAdventure ⟨0⟩
  (handCardNamed meagerMealSetup ⟨0⟩ "Gollum, Silent Slinker")
#guard meagerMealSetup.asSorcery? ⟨0⟩

/-- No creatures: the first “target” word is optional, so Meager Meal is still
legal (the player target remains). -/
def meagerMealNoCreature : Game :=
  let g := readyMain (emptyHand afterDraw ⟨0⟩)
  withBlackMana (addToHand g gollumSilentSlinker ⟨0⟩) ⟨0⟩ 1

#guard meagerMealNoCreature.canCastAdventure ⟨0⟩
  (handCardNamed meagerMealNoCreature ⟨0⟩ "Gollum, Silent Slinker")

def proposedMeagerMeal : Game :=
  mustApply meagerMealSetup ⟨0⟩
    (.castAdventure (handCardNamed meagerMealSetup ⟨0⟩ "Gollum, Silent Slinker").id)

#guard proposedMeagerMeal.pending == .chooseTargets ⟨0⟩
#guard (proposedMeagerMeal.object! proposedMeagerMeal.stack.back!.objectId).name ==
  "Meager Meal"
#guard (proposedMeagerMeal.object! proposedMeagerMeal.stack.back!.objectId).isAdventureSpell
#guard proposedMeagerMeal.stack.back!.targets.isEmpty
#guard proposedMeagerMeal.currentTargetSlot
  (proposedMeagerMeal.object! proposedMeagerMeal.stack.back!.objectId) == 0
#guard proposedMeagerMeal.canSkipCurrentOptionalSlot
  (proposedMeagerMeal.object! proposedMeagerMeal.stack.back!.objectId)
#guard proposedMeagerMeal.log.any (fun s => mentions s "begins casting Meager Meal")
#guard proposedMeagerMeal.log.any (fun s => mentions s "must choose a target (CR 601.2c)")

-- The first instance is the creature, not the player (card-text order).
#guard
  match proposedMeagerMeal.apply ⟨0⟩ (.target (Target.player ⟨0⟩)) with
  | .error msg => mentions msg "Illegal target"
  | .ok _ => false
#guard
  match proposedMeagerMeal.apply ⟨0⟩ (.target (Target.player ⟨1⟩)) with
  | .error msg => mentions msg "Illegal target"
  | .ok _ => false
#guard
  match proposedMeagerMeal.announceTargetChoices ⟨0⟩
      #[(Target.permanent (namedPermanent proposedMeagerMeal "Grizzly Bears").id, none),
        (Target.player ⟨0⟩, none)] with
  | .error msg => mentions msg "separately"
  | .ok _ => false

-- Distinct instances of “target” are announced sequentially (CR 601.2c).
#guard
  match Agent.choose proposedMeagerMeal ⟨0⟩ with
  | some (.target (Target.permanent tid)) =>
    (proposedMeagerMeal.object! tid).name == "Grizzly Bears"
  | _ => false

def meagerMealCreatureChosen : Game :=
  mustApply proposedMeagerMeal ⟨0⟩
    (.target (Target.permanent (namedPermanent proposedMeagerMeal "Grizzly Bears").id))

#guard meagerMealCreatureChosen.pending == .chooseTargets ⟨0⟩
#guard meagerMealCreatureChosen.proposedSpell.isSome
#guard meagerMealCreatureChosen.stack.back!.targets ==
  #[Target.permanent (namedPermanent meagerMealCreatureChosen "Grizzly Bears").id]
#guard meagerMealCreatureChosen.currentTargetSlot
  (meagerMealCreatureChosen.object! meagerMealCreatureChosen.stack.back!.objectId) == 1
#guard !meagerMealCreatureChosen.canSkipCurrentOptionalSlot
  (meagerMealCreatureChosen.object! meagerMealCreatureChosen.stack.back!.objectId)
#guard meagerMealCreatureChosen.log.any (fun s =>
  mentions s "chooses Grizzly Bears as a target (CR 601.2c)")

-- After the creature, only a player is legal.
#guard
  match meagerMealCreatureChosen.apply ⟨0⟩
      (.target (Target.permanent
        (namedPermanent meagerMealCreatureChosen "Gray Ogre").id)) with
  | .error msg => mentions msg "Illegal target"
  | .ok _ => false
#guard
  match meagerMealCreatureChosen.apply ⟨0⟩ .decline with
  | .error msg => mentions msg "requires a target"
  | .ok _ => false
#guard
  match Agent.choose meagerMealCreatureChosen ⟨0⟩ with
  | some (.target (Target.player q)) => q == ⟨0⟩
  | _ => false

def targetedMeagerMeal : Game :=
  mustApply meagerMealCreatureChosen ⟨0⟩ (.target (Target.player ⟨0⟩))

#guard targetedMeagerMeal.pending == .activateManaAbilities ⟨0⟩
#guard targetedMeagerMeal.stack.back!.targets ==
  #[Target.permanent (namedPermanent targetedMeagerMeal "Grizzly Bears").id,
    Target.player ⟨0⟩]

def paidMeagerMeal : Game := mustApply targetedMeagerMeal ⟨0⟩ .pay

#guard paidMeagerMeal.hasPriority ⟨0⟩
#guard paidMeagerMeal.log.any (fun s => mentions s "casts Meager Meal")

def resolvedMeagerMeal : Game := passBoth paidMeagerMeal

#guard resolvedMeagerMeal.stack.isEmpty
#guard (namedPermanent resolvedMeagerMeal "Grizzly Bears").status.plusOnePlusOne == 1
#guard (namedPermanent resolvedMeagerMeal "Gray Ogre").status.plusOnePlusOne == 0
#guard (resolvedMeagerMeal.player ⟨0⟩).life == 22
#guard (resolvedMeagerMeal.player ⟨1⟩).life == 20
#guard resolvedMeagerMeal.log.any (fun s =>
  mentions s "Grizzly Bears gets a +1/+1 counter")
#guard resolvedMeagerMeal.log.any (fun s => mentions s "Chandra gains 2 life")
#guard resolvedMeagerMeal.objects.any (fun o =>
  o.name == "Gollum, Silent Slinker" && o.zone == .exile)

/-- Decline the optional creature, then announce the player. -/
def meagerMealDeclinedCreature : Game :=
  mustApply proposedMeagerMeal ⟨0⟩ .decline

#guard meagerMealDeclinedCreature.pending == .chooseTargets ⟨0⟩
#guard meagerMealDeclinedCreature.stack.back!.targets.isEmpty
#guard meagerMealDeclinedCreature.stack.back!.skippedOptionalSlots == 1
#guard meagerMealDeclinedCreature.currentTargetSlot
  (meagerMealDeclinedCreature.object! meagerMealDeclinedCreature.stack.back!.objectId) == 1
#guard meagerMealDeclinedCreature.log.any (fun s =>
  mentions s "chooses no target (CR 603.3d / 601.2c)")
#guard
  match meagerMealDeclinedCreature.apply ⟨0⟩
      (.target (Target.permanent
        (namedPermanent meagerMealDeclinedCreature "Grizzly Bears").id)) with
  | .error msg => mentions msg "Illegal target"
  | .ok _ => false

def targetedMeagerMealNoCreature : Game :=
  mustApply meagerMealDeclinedCreature ⟨0⟩ (.target (Target.player ⟨1⟩))

#guard targetedMeagerMealNoCreature.pending == .activateManaAbilities ⟨0⟩
#guard targetedMeagerMealNoCreature.stack.back!.targets == #[Target.player ⟨1⟩]

def resolvedMeagerMealNoCreature : Game :=
  passBoth (mustApply targetedMeagerMealNoCreature ⟨0⟩ .pay)

#guard (namedPermanent resolvedMeagerMealNoCreature "Grizzly Bears").status.plusOnePlusOne == 0
#guard (resolvedMeagerMealNoCreature.player ⟨0⟩).life == 20
#guard (resolvedMeagerMealNoCreature.player ⟨1⟩).life == 22
#guard resolvedMeagerMealNoCreature.log.any (fun s => mentions s "Nissa gains 2 life")
#guard !resolvedMeagerMealNoCreature.log.any (fun s =>
  mentions s "gets a +1/+1 counter")

/-- With no creatures, the first slot is skipped automatically by the idle
path, then the player is announced. -/
def proposedMeagerMealNoCreature : Game :=
  mustApply meagerMealNoCreature ⟨0⟩
    (.castAdventure (handCardNamed meagerMealNoCreature ⟨0⟩ "Gollum, Silent Slinker").id)

#guard proposedMeagerMealNoCreature.pending == .chooseTargets ⟨0⟩
#guard proposedMeagerMealNoCreature.canSkipCurrentOptionalSlot
  (proposedMeagerMealNoCreature.object! proposedMeagerMealNoCreature.stack.back!.objectId)
#guard (proposedMeagerMealNoCreature.legalProposedTargets ⟨0⟩
  (proposedMeagerMealNoCreature.object! proposedMeagerMealNoCreature.stack.back!.objectId)).isEmpty
#guard
  match Agent.choose proposedMeagerMealNoCreature ⟨0⟩ with
  | some .decline => true
  | _ => false

def meagerMealNoCreatureAfterSkip : Game :=
  mustApply proposedMeagerMealNoCreature ⟨0⟩ .decline

#guard meagerMealNoCreatureAfterSkip.pending == .chooseTargets ⟨0⟩
#guard
  match Agent.choose meagerMealNoCreatureAfterSkip ⟨0⟩ with
  | some (.target (Target.player q)) => q == ⟨0⟩
  | _ => false

-- A creature that leaves before resolution does not stop the life gain (CR 608.2b).
#guard
  let dest := namedPermanent paidMeagerMeal "Grizzly Bears"
  let (g, _) := paidMeagerMeal.move dest.id (.graveyard dest.owner) none
  let g := passBoth g
  !g.battlefield.any (fun o => o.name == "Grizzly Bears") &&
    (g.player ⟨0⟩).life == 22 &&
    g.log.any (fun s => mentions s "Chandra gains 2 life")

#guard Keyword.firstStrike.firstStrike
#guard Keyword.islandwalk.islandwalk
#guard supportedCardsMatchOracle
#guard bofurReliableGuardian.matchesOracleText
#guard mentorOfTheMeek.matchesOracleText
#guard fiendHunter.matchesOracleText
#guard dawnOfANewAge.matchesOracleText
#guard colossalWhale.matchesOracleText
#guard lorienRevealed.matchesOracleText
#guard sternScolding.matchesOracleText
#guard dunedainBlade.matchesOracleText
#guard ordinaryBear.matchesOracleText
#guard largeBear.matchesOracleText
#guard littleBear.matchesOracleText
#guard elvenkingsHarper.matchesOracleText
#guard smaugsFury.matchesOracleText
#guard wellWornSpatula.matchesOracleText
#guard elvenkingsHalls.matchesOracleText
#guard ironHills.matchesOracleText
#guard lakeTown.matchesOracleText
#guard nighthowlPursuer.matchesOracleText
#guard wargling.matchesOracleText
#guard wilderlandScrounger.matchesOracleText
#guard nastyLittleRabbit.matchesOracleText
#guard theChiefWarg.matchesOracleText
#guard bardHeirOfGirion.matchesOracleText
#guard reprieve.matchesOracleText
#guard thorinsLastStand.matchesOracleText
#guard stoneBySunlight.matchesOracleText
#guard duskwatchHunter.matchesOracleText
#guard patientInstructor.matchesOracleText
#guard longLakeNuisance.matchesOracleText
#guard laketownLookout.matchesOracleText
#guard giantsBoulder.matchesOracleText
#guard longBodiedGreyDog.matchesOracleText
#guard doriBearerOfFriends.matchesOracleText
#guard esgarothGarrison.matchesOracleText
#guard gundabadOpportunist.matchesOracleText
#guard giganticBigBear.matchesOracleText
#guard bothersomeNoisemaker.matchesOracleText
#guard fearsomeGoblinPair.matchesOracleText
#guard goblinTownFlunkies.matchesOracleText
#guard mistyMountainsRaider.matchesOracleText
#guard greatGoblinFoulHearted.matchesOracleText
#guard bardsCompany.matchesOracleText
#guard dwarvenWarriors.matchesOracleText
#guard goblinTown.matchesOracleText
#guard mirkwood.matchesOracleText
#guard hobbitHole.matchesOracleText
#guard rageIntoTheValley.matchesOracleText
#guard gatheringOfDarkness.matchesOracleText
#guard soundTheTrumpets.matchesOracleText
#guard fatefulDiscovery.matchesOracleText
#guard chiefWargsCompany.matchesOracleText
#guard dwarvenShortsword.matchesOracleText
#guard goblinPlateMail.matchesOracleText
#guard bagEndBanquet.matchesOracleText
#guard floweringOfTheWhiteTree.matchesOracleText
#guard momentOfGlory.matchesOracleText
#guard plunderTheTrollshaws.matchesOracleText
#guard tidingsOfWar.matchesOracleText
#guard eaglesRescue.matchesOracleText
#guard gandalfWanderingWizard.matchesOracleText
#guard trollNegotiations.matchesOracleText
#guard dwarvenMattock.matchesOracleText
#guard mithrilCoat.matchesOracleText
#guard greatUglyLookingGoblin.matchesOracleText
#guard theArkenstone.matchesOracleText
#guard bolgsCompany.matchesOracleText
#guard noriTellerOfTales.matchesOracleText
#guard theLordOfTheEagles.matchesOracleText
#guard throrsMap.matchesOracleText
#guard rivendell.matchesOracleText
#guard delightedHalfling.matchesOracleText
#guard relicOfSauron.matchesOracleText
#guard longLostLances.matchesOracleText
#guard theBlackArrow.matchesOracleText
#guard smaugTheMagnificent.matchesOracleText
#guard theQueenOfDale.matchesOracleText
#guard lothoCorruptShirriff.matchesOracleText
#guard oriKeeperOfSongs.matchesOracleText
#guard oinTheBrave.matchesOracleText
#guard bomburGentleDreamer.matchesOracleText
#guard filiThePathfinder.matchesOracleText
#guard thorinOakenshield.matchesOracleText
#guard dainLordOfTheIronHills.matchesOracleText
#guard oldThrush.matchesOracleText
#guard mostDecrepitOldBird.matchesOracleText
#guard lakeTownMariners.matchesOracleText
#guard flameOfAnor.matchesOracleText
#guard lastMarchOfTheEnts.matchesOracleText
#guard raiseThePalisade.matchesOracleText
#guard dragonsDesire.matchesOracleText
#guard pineconeStrike.matchesOracleText
#guard oriPlateStacker.matchesOracleText
#guard dainOfTheAncientHalls.matchesOracleText
#guard treasureVault.matchesOracleText
#guard theLonelyMountain.matchesOracleText
#guard thranduilSindarinLiege.matchesOracleText
#guard aragornAndArwenWed.matchesOracleText
#guard gloinTheMighty.matchesOracleText
#guard ironHillsStalwart.matchesOracleText
#guard oldFatSpider.matchesOracleText
#guard greatGildedBoat.matchesOracleText
#guard minasTirith.matchesOracleText
#guard theShire.matchesOracleText
#guard thranduilTheStrategist.matchesOracleText
#guard desolationOfSmaug.matchesOracleText
#guard moxAmber.matchesOracleText
#guard filiAndKiliJoyous.matchesOracleText
#guard dwarvenMauler.matchesOracleText
#guard myPrecious.matchesOracleText
#guard troopOfPonies.matchesOracleText
#guard arcaneSignet.matchesOracleText
#guard theGaffer.matchesOracleText
#guard witchKingBringerOfRuin.matchesOracleText
#guard elvenRaftSteerer.matchesOracleText
#guard mirkwoodMeditator.matchesOracleText
#guard mirkwoodNurturer.matchesOracleText
#guard necklaceOfGirion.matchesOracleText
#guard kiliTheResourceful.matchesOracleText
#guard dainsCompany.matchesOracleText
#guard sauronTheLidlessEye.matchesOracleText
#guard bolgEreborsReckoning.matchesOracleText
#guard smaugWickedWorm.matchesOracleText
#guard glamdringFoeHammer.matchesOracleText
#guard settleTheWreckage.matchesOracleText
#guard anUnexpectedParty.matchesOracleText
#guard ironHillsBlacksmith.matchesOracleText
#guard thorinKingOfDurinsFolk.matchesOracleText
#guard gandalfGoblinsBane.matchesOracleText
#guard bilboUnexpectedAdventurer.matchesOracleText
#guard alongTheCrookedWay.matchesOracleText
#guard andurilFlameOfTheWest.matchesOracleText
#guard andurilNarsilReforged.matchesOracleText
#guard aragornTheUniter.matchesOracleText
#guard arwenMortalQueen.matchesOracleText
#guard arwenWeaverOfHope.matchesOracleText
#guard azogMoriaSRuin.matchesOracleText
#guard balinLoremaster.matchesOracleText
#guard bardTheBowman.matchesOracleText
#guard bardKingOfDale.matchesOracleText
#guard bejeweledWarg.matchesOracleText
#guard belladonnaTook.matchesOracleText
#guard beornTheFierce.matchesOracleText
#guard bifurMelodicRider.matchesOracleText
#guard bilboSBurglaring.matchesOracleText
#guard bilboSGambit.matchesOracleText
#guard bilboSRing.matchesOracleText
#guard bilboFellowConspirator.matchesOracleText
#guard bilboThiefInTheNight.matchesOracleText
#guard bolgOfTheNorth.matchesOracleText
#guard boughsideWanderers.matchesOracleText
#guard burnBurnTreeAndFern.matchesOracleText
#guard callForthTheTempest.matchesOracleText
#guard cantankerousKeepers.matchesOracleText
#guard cavernHoardDragon.matchesOracleText
#guard celebrateTheMountainKing.matchesOracleText
#guard chiefOfTheWilds.matchesOracleText
#guard dancingFromDarkToDawn.matchesOracleText
#guard desertWereWorm.matchesOracleText
#guard downInTheValley.matchesOracleText
#guard downDownToGoblinTown.matchesOracleText
#guard dragonCursedHalls.matchesOracleText
#guard dwalinWeaponmaster.matchesOracleText
#guard dainIronfoot.matchesOracleText
#guard elrondMoonReader.matchesOracleText
#guard elvenChorus.matchesOracleText
#guard elvenPassage.matchesOracleText
#guard enchantedRiverSGrasp.matchesOracleText
#guard galadrielSDismissal.matchesOracleText
#guard galadrielLightOfValinor.matchesOracleText
#guard gandalfPartyGuest.matchesOracleText
#guard gandalfShadowSFoe.matchesOracleText
#guard getawayBarrel.matchesOracleText
#guard glamdring.matchesOracleText
#guard gleamingSplendor.matchesOracleText
#guard gollumRiddleMaster.matchesOracleText
#guard grimaSarumanSFootman.matchesOracleText
#guard headOfTheHunt.matchesOracleText
#guard insideInformation.matchesOracleText
#guard keyToTheSideDoor.matchesOracleText
#guard lakeTownToymaker.matchesOracleText
#guard lastLightOfDurinSDay.matchesOracleText
#guard masterSCouncillors.matchesOracleText
#guard minasMorgulDarkFortress.matchesOracleText
#guard mountDoom.matchesOracleText
#guard oldFatSpiderCanTSeeMe.matchesOracleText
#guard orcishBowmasters.matchesOracleText
#guard orcristGoblinCleaver.matchesOracleText
#guard palantirOfOrthanc.matchesOracleText
#guard partInFriendship.matchesOracleText
#guard radagastOfRhosgobel.matchesOracleText
#guard rhovanionRampager.matchesOracleText
#guard riddlesInTheDark.matchesOracleText
#guard roadsGoEverEverOn.matchesOracleText
#guard rollRollRollRoll.matchesOracleText
#guard sarumanOfManyColors.matchesOracleText
#guard sauronTheDarkLord.matchesOracleText
#guard silvanReveler.matchesOracleText
#guard smaugTheImpenetrable.matchesOracleText
#guard stingBilboSSword.matchesOracleText
#guard stoneGiantOfHighPass.matchesOracleText
#guard supperForSpiders.matchesOracleText
#guard theBlackGate.matchesOracleText
#guard theEaglesAreComing.matchesOracleText
#guard theGreatGoblin.matchesOracleText
#guard theMasterOfLakeTown.matchesOracleText
#guard theMistyMountainsCold.matchesOracleText
#guard theMountainKingSReturn.matchesOracleText
#guard theNotaryHobbits.matchesOracleText
#guard theOneRing.matchesOracleText
#guard theReaverCleaver.matchesOracleText
#guard theSackvilleBagginses.matchesOracleText
#guard thorinCompanySLeader.matchesOracleText
#guard thorinMountainKing.matchesOracleText
#guard thranduilSCompany.matchesOracleText
#guard thranduilTheElvenking.matchesOracleText
#guard throughTheForestGate.matchesOracleText
#guard tomBombadil.matchesOracleText
#guard tomBertAndWilliam.matchesOracleText
#guard uncoverTheMoonLetters.matchesOracleText
#guard witchKingOfAngmar.matchesOracleText
#guard wizardSStaff.matchesOracleText
#guard largeBear.manaCost.manaValue == 5
#guard
  let p := ManaPool.empty.add (.colored .black) 2 |>.add .colorless 3
  (p.pay? largeBear.manaCost).isSome
#guard
  let p := ManaPool.empty.add (.colored .green) 2 |>.add .colorless 3
  (p.pay? largeBear.manaCost).isSome
#guard
  let p := ManaPool.empty.add (.colored .red) 2 |>.add .colorless 3
  (p.pay? largeBear.manaCost).isNone

end Mtg.Engine.Tests
