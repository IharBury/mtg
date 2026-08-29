import Mtg.Engine.Card
import Mtg.Engine.Catalog
import Mtg.Engine.Catalog.Hobbit
import Mtg.Engine.Catalog.HobbitEternal
import Mtg.Engine.Game
import Mtg.Engine.OracleRulings
import Mtg.Engine.Tests

/-!
# Engine behavior for unique HOB / HOC judge rulings

These tests check Gatherer / Scryfall `wotc` comments — rulings issued by
judges — not the rules text printed on the cards and not
`CardDef.matchesOracleText`. Each `#guard` is tagged with the ruling id
from `uniqueHobHocOracleRulings`.
-/

namespace Mtg.Engine.RulingTests

open Mtg.Engine
open Mtg.Engine.Catalog
open Mtg.Engine.Tests

/-- Look up a unique HOB/HOC judge ruling by 1-based id. -/
def ruling (id : Nat) : OracleRuling :=
  uniqueHobHocOracleRulings[id - 1]!

#guard uniqueHobHocOracleRulingCount == 359
#guard (List.range 359).all (fun i => (ruling (i + 1)).id == i + 1)
#guard !(ruling 1).comment.contains "Whenever"
#guard (ruling 38).comment.contains "hone counter"
#guard (ruling 22).comment.contains "permanent"

/-- A 0/0 legendary Storied creature used only to test judge ruling 26. -/
def zeroStoried : CardDef :=
  legendaryCreature "Zero Story" ManaCost.empty #["Dwarf"] 0 0
    (keywords := Keyword.storied)

/-- Attach `equipName` to `hostName` and put `n` hone counters on the Equipment. -/
def honeOn (g : Game) (equipName hostName : String) (n : Nat) : Game :=
  let eq := namedPermanent g equipName
  let host := namedPermanent g hostName
  let g := g.attachSourceTo eq host
  g.mapObjectStatus (namedPermanent g equipName) (fun s => { s with hone := n })

/-!
## 1, 14–18, 40–41, 51–53, 61 — amass
-/

/-- Ruling 18 / 1: create a 0/0 Goblin Army, then put N counters on the
amassed Army. -/
def amassFresh : Game := started.amassGoblins ⟨0⟩ 2

def amassFreshOk : Bool :=
  let army := namedPermanent amassFresh "Goblin Army"
  army.printed.isToken && amassFresh.hasSubtype army "Goblin" &&
    amassFresh.hasSubtype army "Army" && army.status.plusOnePlusOne == 2 &&
    amassFresh.power army == 2 && amassFresh.toughness army == 2 &&
    amassFresh.log.any (fun s => mentions s "amassed Army") &&
    amassFresh.log.any (fun s => mentions s "entered as a 0/0 creature")

#guard amassFreshOk

/-- Ruling 1: later amass still names the same creature as the amassed Army. -/
def amassAgain : Game := amassFresh.amassGoblins ⟨0⟩ 1

#guard
  (amassAgain.battlefield.filter (fun o => o.name == "Goblin Army")).size == 1
#guard (namedPermanent amassAgain "Goblin Army").status.plusOnePlusOne == 3
#guard amassAgain.log.any (fun s => mentions s "Goblin Army is the amassed Army")

/-- Ruling 14 / 61: amass Orcs creates an Orc Army; combining with Goblins
makes a Goblin Orc Army. -/
def amassOrcThenGoblin : Game :=
  (started.amassOrcs ⟨0⟩ 1).amassGoblins ⟨0⟩ 1

def amassOrcThenGoblinOk : Bool :=
  let army := namedPermanent amassOrcThenGoblin "Orc Army"
  amassOrcThenGoblin.hasSubtype army "Orc" &&
    amassOrcThenGoblin.hasSubtype army "Goblin" &&
    amassOrcThenGoblin.hasSubtype army "Army" &&
    army.status.plusOnePlusOne == 2 &&
    (amassOrcThenGoblin.battlefield.filter (fun o =>
      amassOrcThenGoblin.hasSubtype o "Army")).size == 1

#guard amassOrcThenGoblinOk

/-- Ruling 40 / 41: amass Zombies is the same action with a Zombie Army. -/
def amassZombieThenOrc : Game :=
  (started.amassZombies ⟨0⟩ 1).amassOrcs ⟨0⟩ 1

def amassZombieThenOrcOk : Bool :=
  let army := namedPermanent amassZombieThenOrc "Zombie Army"
  amassZombieThenOrc.hasSubtype army "Zombie" &&
    amassZombieThenOrc.hasSubtype army "Orc" &&
    army.status.plusOnePlusOne == 2

#guard amassZombieThenOrcOk

/-- Ruling 15 / 51: Mentor of the Meek sees the token enter as 0/0, even
when later counters would put it above 2 power. -/
def amassMentorSeesZero : Game :=
  let g := addPermanent started mentorOfTheMeek ⟨0⟩ ⟨0⟩
  let g := g.amassGoblins ⟨0⟩ 3
  g.receivePriority ⟨0⟩

def amassMentorSeesZeroOk : Bool :=
  let army := namedPermanent amassMentorSeesZero "Goblin Army"
  army.status.plusOnePlusOne == 3 && amassMentorSeesZero.power army == 3 &&
    amassMentorSeesZero.stack.any (fun e =>
      (amassMentorSeesZero.object! e.objectId).triggeredAbility ==
        some (.onAnotherCreatureYouControlPowerAtMostEntersMayPayDraw 2 1))

#guard amassMentorSeesZeroOk

/-- A 3-power creature entering after counters would not trigger Mentor. -/
def mentorIgnoresGiant : Game :=
  let g := addPermanent started mentorOfTheMeek ⟨0⟩ ⟨0⟩
  let g := addPermanent g hillGiant ⟨0⟩ ⟨0⟩
  let mentor := namedPermanent g "Mentor of the Meek"
  let giant := namedPermanent g "Hill Giant"
  let g := g.putMatchingSourceTriggers ⟨0⟩ mentor .anotherCreatureYouControlEnters
    (cause := some giant)
  g.receivePriority ⟨0⟩

#guard mentorIgnoresGiant.stack.isEmpty

/-- Ruling 16 / 52: with several Armies, the newest is the amassed Army. -/
def twoArmiesThenAmass : Game :=
  let (g, _) := started.createToken ⟨0⟩ Game.goblinArmyToken
  let (g, _) := g.createToken ⟨0⟩ Game.orcArmyToken
  g.amassGoblins ⟨0⟩ 1

def twoArmiesThenAmassOk : Bool :=
  let orc := namedPermanent twoArmiesThenAmass "Orc Army"
  orc.status.plusOnePlusOne == 1 && twoArmiesThenAmass.hasSubtype orc "Goblin" &&
    (namedPermanent twoArmiesThenAmass "Goblin Army").status.plusOnePlusOne == 0

#guard twoArmiesThenAmassOk

/-- Ruling 18: untargeted amass still creates the Army. -/
def untargetedAmass : Game := started.applyEffect ⟨0⟩ (.amassGoblins 1) #[]

#guard untargetedAmass.battlefield.any (fun o => untargetedAmass.hasSubtype o "Army")

/-!
## 2–13 — Adventure
-/

/-- Ruling 2: in every zone except the stack-as-Adventure, ignore the
Adventure face. Bilbo in a graveyard is a blue creature of mana value 2. -/
def burglarPlot : AdventureFace := bilboLuckwearer.adventure.get!

#guard bilboLuckwearer.isCreature
#guard !bilboLuckwearer.isInstant
#guard !bilboLuckwearer.isSorcery
#guard bilboLuckwearer.manaValue == 2
#guard burglarPlot.name == "Burglar's Plot"
#guard burglarPlot.manaCost.manaValue == 5

/-- Ruling 3: “has an Adventure” looks at the adventurer card’s alternative
characteristics even when they are not in use. -/
def bilboInPlay : Game := addPermanent started bilboLuckwearer ⟨0⟩ ⟨0⟩

#guard (namedPermanent bilboInPlay "Bilbo, Luckwearer").printed.adventure.isSome
#guard !(namedPermanent bilboInPlay "Bilbo, Luckwearer").isAdventureSpell
#guard (namedPermanent bilboInPlay "Bilbo, Luckwearer").printed.isCreature

/-- Ruling 12 / 9: a spell cast as an Adventure uses only the alternative
characteristics. On the stack it is not a card that “has an Adventure”. -/
def spewOnStack : GameObject :=
  paidSpewFlame.object! paidSpewFlame.stack.back!.objectId

#guard spewOnStack.name == "Spew Flame"
#guard spewOnStack.printed.isSorcery
#guard spewOnStack.isAdventureSpell
#guard spewOnStack.printed.adventure.isNone
#guard spewOnStack.printed.manaCost.manaValue == 5

/-- Ruling 5 / 13: a resolving Adventure is exiled and may be cast as the
permanent later, only when timing allows. -/
def smaugExiledFromAdventure : Bool :=
  resolvedSpewFlame.objects.any (fun o =>
    o.zone == .exile && o.name == "Smaug, the Great Calamity")

def smaugAdventureExileOk : Bool :=
  smaugExiledFromAdventure &&
    resolvedSpewFlame.mayPlayFromExile ⟨0⟩ (exiledSmaug resolvedSpewFlame) &&
    !(resolvedSpewFlame.canCastAdventure ⟨0⟩ (exiledSmaug resolvedSpewFlame)) &&
    resolvedSpewFlame.adventureExileForbidsRecast (exiledSmaug resolvedSpewFlame)

#guard smaugAdventureExileOk

/-- Ruling 6: exile for any other reason does not grant the Adventure
cast-as-permanent permission. -/
def smaugExiledOtherwise : Game :=
  let g := addToHand started smaugTheGreatCalamity ⟨0⟩
  let id := (handCardNamed g ⟨0⟩ "Smaug, the Great Calamity").id
  (g.move id .exile none).1

def smaugExiledOtherwiseCard : GameObject :=
  match smaugExiledOtherwise.objects.find? (fun x =>
      x.zone == .exile && x.name == "Smaug, the Great Calamity") with
  | some x => x
  | none => panic! "expected Smaug in exile"

#guard !(smaugExiledOtherwise.mayPlayFromExile ⟨0⟩ smaugExiledOtherwiseCard)

/-- Ruling 4 / 11: legality uses the Adventure face. Spew Flame is a sorcery. -/
def spewFlameIsSorcery : Bool :=
  match smaugTheGreatCalamity.adventure with
  | some adv => adv.types.contains CardType.sorcery
  | none => false

#guard spewFlameIsSorcery

def canCastSpewFlame : Bool :=
  smaugSetup.canCastAdventure ⟨0⟩
    (handCardNamed smaugSetup ⟨0⟩ "Smaug, the Great Calamity")

#guard canCastSpewFlame
#guard (smaugSetup.asSorcery? ⟨0⟩)

/-!
## 19–21 — landfall
-/

/-- Ruling 19: a nonland entering does not trigger landfall. -/
def creatureEtbVsLandfall : Game :=
  let g := addPermanent afterDraw attercop ⟨0⟩ ⟨0⟩
  let g := addPermanent g grizzlyBears ⟨0⟩ ⟨0⟩
  g.afterPermanentEnters (namedPermanent g "Grizzly Bears")

#guard !(creatureEtbVsLandfall.log.any (fun s => mentions s "landfall"))

/-- Ruling 20: playing a land triggers landfall. -/
def hospitalityLandfallOk : Bool :=
  hospitalityLandPlayed.log.any (fun s => mentions s "landfall trigger is put on the stack") &&
    hospitalityLandPlayed.stack.size == 1

#guard hospitalityLandfallOk

/-- Ruling 20: a spell that puts a land onto the battlefield also triggers
landfall (Wood Elves + Attercop). -/
def woodElvesLandfallOk : Bool :=
  attercopWoodElvesResolved.log.any (fun s => mentions s "landfall trigger is put on the stack")

#guard woodElvesLandfallOk

/-- Ruling 21: each landfall ability of permanents you control triggers. -/
def twoLandfall : Game :=
  let g := addPermanent afterDraw attercop ⟨0⟩ ⟨0⟩
  let g := addPermanent g beornsHospitality ⟨0⟩ ⟨0⟩
  let g := addToHand g forest ⟨0⟩
  mustApply g ⟨0⟩ (.playLand (handCardNamed g ⟨0⟩ "Forest").id)

def twoLandfallTriggered : Bool :=
  let onStack := twoLandfall.stack.filterMap (fun e =>
    (twoLandfall.object! e.objectId).triggeredAbility)
  let waiting := twoLandfall.waitingTriggers.map (·.ability)
  let all := onStack ++ waiting
  all.any (· == .onLandYouControlEntersGets1) &&
    all.any (· == .onLandYouControlEntersPlusOnePlusOne)

#guard twoLandfallTriggered

/-- Ruling 19 / 20: an opponent's land does not trigger your landfall. -/
def nissaLandfallSilent : Bool :=
  !(nissaLandVsAttercop.log.any (fun s => mentions s "landfall"))

#guard nissaLandfallSilent

/-!
## 22, 24–28 — Storied / enduring story
-/

/-- Ruling 22: tokens and lands are permanents; a spell on the stack is not. -/
def permanentsVsSpell : Game :=
  let g := addUntappedLand started mountain
  (g.createToken ⟨0⟩ Game.treasureToken).1

#guard (namedPermanent permanentsVsSpell "Mountain").isOnBattlefield
#guard permanentsVsSpell.battlefield.any (fun o => o.name == "Treasure")
#guard !paidSpewFlame.stack.isEmpty
#guard !(paidSpewFlame.object! paidSpewFlame.stack.back!.objectId).isOnBattlefield

/-- Ruling 24: a legendary artifact counts once, not once per quality. -/
def stingAlone : Game := addPermanent started stingBilboSSword ⟨0⟩ ⟨0⟩

#guard (namedPermanent stingAlone "Sting, Bilbo's Sword").isLegendary
#guard (namedPermanent stingAlone "Sting, Bilbo's Sword").printed.isArtifact
#guard stingAlone.countsTowardStoried (namedPermanent stingAlone "Sting, Bilbo's Sword")
#guard stingAlone.storiedPermanentCount ⟨0⟩ == 1

/-- Ruling 24: legendary artifact + Saga is two permanents, not three. -/
def stingAndSaga : Game :=
  addPermanent (addPermanent started stingBilboSSword ⟨0⟩ ⟨0⟩)
    downInTheValley ⟨0⟩ ⟨0⟩

#guard stingAndSaga.storiedPermanentCount ⟨0⟩ == 2
#guard !(stingAndSaga.hasEnduringStory ⟨0⟩)

/-- Ruling 25: three artifacts without a storied permanent grant nothing. -/
def threeTreasures : Game := started.createTreasureTokens ⟨0⟩ 3

#guard threeTreasures.storiedPermanentCount ⟨0⟩ == 3
#guard !(threeTreasures.controlsStoried ⟨0⟩)
#guard !(threeTreasures.hasEnduringStory ⟨0⟩)

/-- Ruling 25: one artifact plus Thorin is only two counting permanents. -/
def thorinAndOneTreasure : Game :=
  let g := started.createTreasureTokens ⟨0⟩ 1
  let g := addPermanent g thorinOakenshield ⟨0⟩ ⟨0⟩
  g.refreshEnduringStory

#guard thorinAndOneTreasure.controlsStoried ⟨0⟩
#guard thorinAndOneTreasure.storiedPermanentCount ⟨0⟩ == 2
#guard !(thorinAndOneTreasure.hasEnduringStory ⟨0⟩)

/-- Ruling 26 / 28: the third counting permanent grants an enduring story
before SBA; a 0/0 that then dies still leaves the player with the story.
Storied does not use the stack. -/
def storyFromZero : Game :=
  let g := started.createTreasureTokens ⟨0⟩ 2
  let g := addPermanent g zeroStoried ⟨0⟩ ⟨0⟩
  g.afterPermanentEnters (namedPermanent g "Zero Story")

#guard storyFromZero.hasEnduringStory ⟨0⟩
#guard storyFromZero.log.any (fun s => mentions s "has an enduring story")
#guard storyFromZero.stack.isEmpty

def storyAfterSba : Game := storyFromZero.checkSBA

#guard storyAfterSba.hasEnduringStory ⟨0⟩
#guard !(storyAfterSba.battlefield.any (fun o => o.name == "Zero Story"))

/-- Ruling 27: the designation stays on the player after the permanents leave. -/
def storyGranted : Game :=
  let g := started.createTreasureTokens ⟨0⟩ 2
  let g := addPermanent g thorinOakenshield ⟨0⟩ ⟨0⟩
  g.refreshEnduringStory

def storyThenLostPermanents : Game :=
  storyGranted.battlefield.foldl (fun acc o =>
    if o.controlledBy ⟨0⟩ then (acc.move o.id (.graveyard o.owner) none).1 else acc)
    storyGranted

#guard storyGranted.hasEnduringStory ⟨0⟩
#guard storyThenLostPermanents.hasEnduringStory ⟨0⟩
#guard storyThenLostPermanents.storiedPermanentCount ⟨0⟩ == 0

/-- Ori's +1/+0 and vigilance apply only while you have an enduring story. -/
def oriAlone : Game := addPermanent started oriKeeperOfSongs ⟨0⟩ ⟨0⟩

#guard oriAlone.power (namedPermanent oriAlone "Ori, Keeper of Songs") == 3
#guard !(oriAlone.currentKeywords (namedPermanent oriAlone "Ori, Keeper of Songs")).vigilance

def oriWithStory : Game :=
  oriAlone.modifyPlayer ⟨0⟩ (fun pl => { pl with enduringStory := true })

#guard oriWithStory.power (namedPermanent oriWithStory "Ori, Keeper of Songs") == 4
#guard (oriWithStory.currentKeywords (namedPermanent oriWithStory "Ori, Keeper of Songs")).vigilance

/-- Fíli's team pump applies to other creatures while you have a story. -/
def filiAndBears : Game :=
  addPermanent (addPermanent started filiThePathfinder ⟨0⟩ ⟨0⟩)
    grizzlyBears ⟨0⟩ ⟨0⟩

#guard filiAndBears.power (namedPermanent filiAndBears "Grizzly Bears") == 2

def filiAndBearsStory : Game :=
  filiAndBears.modifyPlayer ⟨0⟩ (fun pl => { pl with enduringStory := true })

#guard filiAndBearsStory.power (namedPermanent filiAndBearsStory "Grizzly Bears") == 3
#guard filiAndBearsStory.toughness (namedPermanent filiAndBearsStory "Grizzly Bears") == 3

/-- Bombur does not untap unless you have an enduring story. -/
def bomburTapped : Game :=
  let g := addPermanent started bomburGentleDreamer ⟨0⟩ ⟨0⟩
  let o := namedPermanent g "Bombur, Gentle Dreamer"
  g.setObject { o with status := { o.status with tapped := true } }

def bomburStillTapped : Game := bomburTapped.beginStep .untap

#guard (namedPermanent bomburStillTapped "Bombur, Gentle Dreamer").status.tapped

def bomburUntapsWithStory : Game :=
  let g := bomburTapped.modifyPlayer ⟨0⟩ (fun pl => { pl with enduringStory := true })
  g.beginStep .untap

#guard !(namedPermanent bomburUntapsWithStory "Bombur, Gentle Dreamer").status.tapped

/-!
## 23 — recruit
-/

/-- Ruling 23: once recruit begins, the draw/discard/token sequence is a
pending action; other players cannot take actions in the middle. -/
def recruitPendingOk : Bool :=
  instructorEntered.pending == .recruitDiscard ⟨0⟩ &&
    instructorEntered.actor == some ⟨0⟩ &&
    !(instructorEntered.hasPriority ⟨0⟩) &&
    !(instructorEntered.hasPriority ⟨1⟩)

#guard recruitPendingOk
def recruitMadeSoldier : Bool :=
  instructorRecruited.battlefield.any (fun o =>
    o.name == "Human Soldier" && o.printed.isToken)

#guard recruitMadeSoldier

/-!
## 29–30 — typecycling
-/

/-- Ruling 30: typecycling searches; it does not draw a card. -/
def oliphauntCycledOk : Bool :=
  (oliphauntCycled.handObjects ⟨0⟩).any (fun o => o.name == "Mountain") &&
    (oliphauntCycled.player ⟨0⟩).graveyard.any (fun id =>
      (oliphauntCycled.object! id).name == "Oliphaunt") &&
    !(oliphauntCycled.handObjects ⟨0⟩).any (fun o => o.name == "Oliphaunt")

#guard oliphauntCycledOk

/-- Ruling 29: typecycling is an activated cycling-form ability (discard
this card from hand, search). The same activation is legal at instant speed
and illegal from the battlefield. -/
def oliphauntCycleShape : Bool :=
  oliphauntCycleAbility.cost.discardSource &&
    oliphauntCycleAbility.activateFromHand &&
    oliphauntCycleAbility.effect == .searchLandTypeToHand "Mountain"

#guard oliphauntCycleShape
def oliphauntCycleAtEndOk : Bool :=
  oliphauntCycleAtEnd.canActivate ⟨0⟩
    (handCardNamed oliphauntCycleAtEnd ⟨0⟩ "Oliphaunt") oliphauntCycleAbility

#guard oliphauntCycleAtEndOk

def oliphauntOnBattlefield : Game := addPermanent afterDraw oliphaunt ⟨0⟩ ⟨0⟩

def oliphauntCannotCycleInPlay : Bool :=
  !oliphauntOnBattlefield.canActivate ⟨0⟩
    (namedPermanent oliphauntOnBattlefield "Oliphaunt") oliphauntCycleAbility

#guard oliphauntCannotCycleInPlay

/-!
## 31–33, 37 — flashback
-/

/-- Ruling 31: flashback means you may cast the card from the graveyard
paying the flashback cost. Moment of Glory needs a creature target. -/
def momentReady : Game :=
  let g := addPermanent afterDraw grizzlyBears ⟨0⟩ ⟨0⟩
  addToGraveyard (skipTo g .precombatMain 40) momentOfGlory ⟨0⟩

#guard momentOfGlory.flashback == some (ManaCost.ofGenericAndColor 4 .white)

def momentReadyPlayable : Bool :=
  momentReady.mayPlayFromGraveyard ⟨0⟩
    (namedGraveyardCard momentReady ⟨0⟩ "Moment of Glory") &&
    momentReady.canCast ⟨0⟩
      (namedGraveyardCard momentReady ⟨0⟩ "Moment of Glory")

#guard momentReadyPlayable

/-- Ruling 37: flashback still obeys timing. A sorcery cannot be flashbacked
in the end step. -/
def momentAtEnd : Game :=
  let g := applyIdle (passBoth (skipTo afterDraw .end 80))
  addToGraveyard g momentOfGlory ⟨0⟩

def momentAtEndIllegal : Bool :=
  !momentAtEnd.asSorcery? ⟨0⟩ &&
    !momentAtEnd.canCast ⟨0⟩
      (namedGraveyardCard momentAtEnd ⟨0⟩ "Moment of Glory")

#guard momentAtEndIllegal

/-- Ruling 32: a flashback spell is exiled as it leaves the stack. -/
def momentFlashbacked : Game :=
  let g := withWhiteMana momentReady ⟨0⟩ 5
  let src := namedGraveyardCard g ⟨0⟩ "Moment of Glory"
  let g := mustApply g ⟨0⟩ (.cast src.id)
  let g := mustApply g ⟨0⟩ (.target (Target.permanent (namedPermanent g "Grizzly Bears").id))
  let g := mustApply g ⟨0⟩ .pay
  passBoth g

def momentFlashbackedOk : Bool :=
  momentFlashbacked.objects.any (fun o =>
    o.zone == .exile && o.name == "Moment of Glory") &&
    !((momentFlashbacked.player ⟨0⟩).graveyard.any (fun id =>
      (momentFlashbacked.object! id).name == "Moment of Glory")) &&
    momentFlashbacked.log.any (fun s => mentions s "exiled (flashback)") &&
    (namedPermanent momentFlashbacked "Grizzly Bears").status.plusOnePlusOne == 1

#guard momentFlashbackedOk

/-- Ruling 33: if the card is in your graveyard on your turn, you may cast
it before the opponent receives priority. -/
def momentReadyHasPriority : Bool :=
  momentReady.hasPriority ⟨0⟩ && !momentReady.hasPriority ⟨1⟩ &&
    momentReady.canCast ⟨0⟩
      (namedGraveyardCard momentReady ⟨0⟩ "Moment of Glory")

#guard momentReadyHasPriority

/-!
## 38, 45, 60 — hone
-/

/-- Ruling 38 / 45: hone counters on any Equipment grant +1/+0, including
Equipment that never mentions hone (Dwarven Shortsword). -/
def shortswordHone : Game :=
  let g := addPermanent (addPermanent started dwarvenShortsword ⟨0⟩ ⟨0⟩)
    grizzlyBears ⟨0⟩ ⟨0⟩
  honeOn g "Dwarven Shortsword" "Grizzly Bears" 2

#guard shortswordHone.power (namedPermanent shortswordHone "Grizzly Bears") == 5
#guard shortswordHone.toughness (namedPermanent shortswordHone "Grizzly Bears") == 4

/-- Ruling 60: unattaching removes the power immediately. -/
def shortswordUnattached : Game :=
  let eq := namedPermanent shortswordHone "Dwarven Shortsword"
  shortswordHone.setObject { eq with attachedTo := none }

#guard shortswordUnattached.power (namedPermanent shortswordUnattached "Grizzly Bears") == 2
#guard shortswordUnattached.toughness (namedPermanent shortswordUnattached "Grizzly Bears") == 2

/-- Ruling 60: leaving the battlefield removes the boost immediately. -/
def shortswordLeft : Game :=
  let eq := namedPermanent shortswordHone "Dwarven Shortsword"
  (shortswordHone.move eq.id (.graveyard eq.owner) none).1

#guard shortswordLeft.power (namedPermanent shortswordLeft "Grizzly Bears") == 2

/-- Ruling 60: removing hone counters changes power immediately. -/
def shortswordHoneCleared : Game :=
  let eq := namedPermanent shortswordHone "Dwarven Shortsword"
  shortswordHone.mapObjectStatus eq (fun s => { s with hone := 0 })

#guard shortswordHoneCleared.power (namedPermanent shortswordHoneCleared "Grizzly Bears") == 3

/-- Ruling 38: the boost is from the counter, not an Equipment ability. -/
def shortswordNoStatics : Game :=
  let eq := namedPermanent shortswordHone "Dwarven Shortsword"
  shortswordHone.setObject { eq with printed := { eq.printed with staticAbilities := #[] } }

#guard shortswordNoStatics.power (namedPermanent shortswordNoStatics "Grizzly Bears") == 4
#guard shortswordNoStatics.toughness (namedPermanent shortswordNoStatics "Grizzly Bears") == 2

/-- Dwalin puts a hone counter on each Equipment you control. -/
def dwalinHoneTrigger : Bool :=
  dwalinWeaponmaster.triggeredAbilities == #[.onEnterOrAttackHoneEachEquipment]

#guard dwalinHoneTrigger

def dwalinHones : Game :=
  let g := addPermanent (addPermanent started dwarvenShortsword ⟨0⟩ ⟨0⟩)
    dwalinWeaponmaster ⟨0⟩ ⟨0⟩
  g.applyTriggeredAbility ⟨0⟩ .onEnterOrAttackHoneEachEquipment none

#guard (namedPermanent dwalinHones "Dwarven Shortsword").status.hone == 1

/-!
## 63, 69 — triggered vs activated wording (judge reminders)
-/

def dwalinTriggerWording : Bool :=
  (ruling 63).comment.contains "when" &&
    (TriggeredAbility.eventPrefix
      dwalinWeaponmaster.triggeredAbilities[0]!.timing).startsWith "Whenever"

def oinActivatedWording : Bool :=
  (ruling 69).comment.contains "colon" &&
    (ActivatedAbility.toNotation oinTheBrave.activatedAbilities[0]!).contains ":"

#guard dwalinTriggerWording
#guard oinActivatedWording

/-!
## 122 — Food is an artifact type, never a creature type
-/

#guard Game.foodToken.isArtifact
#guard !Game.foodToken.isCreature
#guard Game.foodToken.hasSubtype "Food"

end Mtg.Engine.RulingTests
