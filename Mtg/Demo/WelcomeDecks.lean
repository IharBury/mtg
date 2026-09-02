import Mtg.Engine.Deck
import Mtg.Engine.Color
import Mtg.Engine.Catalog
import Mtg.Engine.Catalog.Hobbit
import Mtg.Engine.Catalog.HobbitEternal

/-!
# The Hobbit Welcome Decks

40-card monocolor Welcome Decks from Magic: The Gathering | The Hobbit, as
published by Wizards of the Coast. These are limited-size decks (CR 100.2b).

Source: https://magic.wizards.com/en/news/announcements/the-hobbit-welcome-decks
-/

namespace Mtg.Demo

open Mtg.Engine
open Mtg.Engine.Catalog

/-- White Welcome Deck (40 cards). -/
def hobbitWhite : Array CardDef :=
  #[bofurReliableGuardianCard] ++
  copies 16 plains ++
  copies 2 dwarvenProvisionerCard ++
  #[velvetwingButterfliesCard] ++
  copies 2 magnificentEndCard ++
  #[mentorOfTheMeek, fiendHunter] ++
  copies 2 errandRiderOfGondor ++
  #[landrovalHorizonWitness, roguesPassage] ++
  copies 2 soldierOfTheGreyHost ++
  #[eaglesOfTheNorth, dunedainBlade, fogOnTheBarrowDowns, eagleOfTheGreatShelfCard,
    banishingLight, dawnOfANewAge, vowToEreborCard] ++
  copies 2 westfoldRider ++
  #[esquireOfTheKing]

/-- Blue Welcome Deck (40 cards). -/
def hobbitBlue : Array CardDef :=
  copies 2 bilboBagginsBurglarCard ++
  copies 16 island ++
  #[pelargirSurvivor] ++
  copies 2 lakeshoreApothecaryCard ++
  #[confusticateAndBebother, ravenhillFlock, lorienRevealed, thranduilsDecree,
    knightsOfDolAmroth, greyHavensNavigator, roguesPassage] ++
  copies 2 ithilienKingfisher ++
  #[hithlainKnots, captainOfUmbar, minasTirithGarrison, colossalWhale,
    willowWind, bilboLuckwearer] ++
  copies 2 uneasyPartings ++
  #[nimrodelWatcher, sternScolding]

/-- Black Welcome Deck (40 cards). -/
def hobbitBlack : Array CardDef :=
  copies 2 frontPorchSentries ++
  #[greatFierceBee, stirUpTrouble, hauntOfTheDeadMarshes, desolationProwler,
    raveningWarg] ++
  copies 2 gollumSilentSlinker ++
  copies 2 bilbosDeadlySlice ++
  #[dreadedBatCloud, roguesPassage, crudeBentBlade, languish, shadowOfTheEnemy,
    gollumTheAbandoned, gnashingOfTeeth, trollOfKhazadDum, mercilessExecutioner,
    bitterDownfall, reverentHowl, nightsWhisper, stonyVoicedGoblins] ++
  copies 16 swamp

/-- Red Welcome Deck (40 cards). -/
def hobbitRed : Array CardDef :=
  copies 16 mountain ++
  copies 2 wayfarersBauble ++
  copies 2 battleScarredGoblin ++
  #[improvisedClub] ++
  copies 2 smaugTheGreatCalamity ++
  copies 2 ologHaiCrusher ++
  #[gandalfSparkStarter] ++
  copies 2 raggedShortSpear ++
  copies 2 smiteTheDeathless ++
  copies 2 goblinFireleaper ++
  #[oliphaunt, roguesPassage, goblinCratermaker, infernoTitan, guttersnipe,
    orcishSiegemaster, snowslopeHunter, fireOfOrthanc]

/-- Green Welcome Deck (40 cards). -/
def hobbitGreen : Array CardDef :=
  copies 16 forest ++
  copies 2 guardianOfTheHalls ++
  copies 2 quarrel ++
  copies 2 galadhrimGuide ++
  #[galionElvenkingsButler, elvishVisionary, wargTactics, beornsHospitality,
    roguesPassage, mirkwoodElk, celebornTheWise, giftOfStrands, elvishArchdruid,
    lothlorienLookout, woodlandWeavemaster, mirkwoodPathmaker,
    beornReluctantHost] ++
  copies 2 woodElves ++
  copies 2 elvishMystic ++
  #[attercop]

/-- The Welcome Deck for a color, in WUBRG order (CR 105.1). -/
def hobbitDeck : Color → Array CardDef
  | .white => hobbitWhite
  | .blue => hobbitBlue
  | .black => hobbitBlack
  | .red => hobbitRed
  | .green => hobbitGreen

#guard hobbitWhite.size == 40
#guard hobbitBlue.size == 40
#guard hobbitBlack.size == 40
#guard hobbitRed.size == 40
#guard hobbitGreen.size == 40
#guard isLegalDeck .limited hobbitWhite
#guard isLegalDeck .limited hobbitBlue
#guard isLegalDeck .limited hobbitBlack
#guard isLegalDeck .limited hobbitRed
#guard isLegalDeck .limited hobbitGreen
#guard !isLegalDeck .constructed hobbitRed
#guard Color.all.all (fun c => (hobbitDeck c).size == 40 && isLegalDeck .limited (hobbitDeck c))
#guard (hobbitDeck .white).any (fun c => c.name == "Bofur, Reliable Guardian")
#guard (hobbitDeck .blue).any (fun c => c.name == "Bilbo Baggins, Burglar")
#guard (hobbitDeck .black).any (fun c => c.name == "Bilbo's Deadly Slice")
#guard (hobbitDeck .black).any (fun c => c.name == "Gollum, Silent Slinker")
#guard (hobbitDeck .red).any (fun c => c.name == "Smaug, the Great Calamity")
#guard (hobbitDeck .green).any (fun c => c.name == "Elvish Archdruid")

end Mtg.Demo
