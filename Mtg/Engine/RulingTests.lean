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

/-- Ruling 51: the Orc Army also enters as 0/0 before counters. -/
def amassOrcMentorSeesZero : Game :=
  let g := addPermanent started mentorOfTheMeek ⟨0⟩ ⟨0⟩
  let g := g.amassOrcs ⟨0⟩ 3
  g.receivePriority ⟨0⟩

def amassOrcMentorSeesZeroOk : Bool :=
  let army := namedPermanent amassOrcMentorSeesZero "Orc Army"
  army.status.plusOnePlusOne == 3 && amassOrcMentorSeesZero.power army == 3 &&
    amassOrcMentorSeesZero.stack.any (fun e =>
      (amassOrcMentorSeesZero.object! e.objectId).triggeredAbility ==
        some (.onAnotherCreatureYouControlPowerAtMostEntersMayPayDraw 2 1)) &&
    (ruling 51).comment.contains "Orc Army token you create enters"

#guard amassOrcMentorSeesZeroOk

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

/-- Ruling 52: with several Armies, amass Orcs chooses one and makes it an Orc. -/
def twoArmiesThenAmassOrcs : Game :=
  let (g, _) := started.createToken ⟨0⟩ Game.goblinArmyToken
  let (g, _) := g.createToken ⟨0⟩ Game.zombieArmyToken
  g.amassOrcs ⟨0⟩ 1

def twoArmiesThenAmassOrcsOk : Bool :=
  let z := namedPermanent twoArmiesThenAmassOrcs "Zombie Army"
  z.status.plusOnePlusOne == 1 && twoArmiesThenAmassOrcs.hasSubtype z "Orc" &&
    (ruling 52).comment.contains "multiple Army creatures"

#guard twoArmiesThenAmassOrcsOk

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
    resolvedSpewFlame.adventureExileForbidsRecast (exiledSmaug resolvedSpewFlame) &&
    (ruling 13).comment.contains "timing restrictions and permissions"

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
#guard (ruling 11).comment.contains "use only its alternative characteristics"
#guard (ruling 8).comment.contains "alternative Adventure name"
#guard smaugTheGreatCalamity.choosableNames.contains "Spew Flame"
#guard !smaugTheGreatCalamity.choosableNames.contains "Burglar's Plot"

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

/-- Find a battlefield-zone object by name, including while phased out. -/
def namedObject (g : Game) (name : String) : GameObject :=
  match g.objects.find? (fun o => o.name == name && o.zone == .battlefield) with
  | some o => o
  | none => panic! s!"expected {name} in the battlefield zone"

/-- An enchantment used only to watch Ring-tempt and Ring-bearer choices. -/
def ringWatcher : CardDef :=
  enchantment "Ring Watcher" (ManaCost.ofGeneric 1)
    "Whenever the Ring tempts you, draw a card.\nWhenever you choose a creature as your Ring-bearer, draw a card."
    (triggeredAbilities := #[.onTheRingTemptsYouDraw 1, .onChooseRingBearerDraw])

/-!
## 42–44, 48, 54, 56–57 — The Ring / Ring-bearer
-/

/-- Ruling 42 / 43: first tempt creates one emblem named The Ring and
chooses a Ring-bearer. A second tempt does not create a second emblem. -/
def ringFirstTempt : Game :=
  let g := addPermanent started grizzlyBears ⟨0⟩ ⟨0⟩
  g.temptWithTheRing ⟨0⟩

def ringFirstTemptOk : Bool :=
  ringFirstTempt.hasTheRing ⟨0⟩ &&
    ringFirstTempt.theRingAbilityCount ⟨0⟩ == 1 &&
    (namedPermanent ringFirstTempt "Grizzly Bears").status.ringBearer &&
    ringFirstTempt.log.any (fun s => mentions s "emblem named The Ring") &&
    ringFirstTempt.log.any (fun s => mentions s "Ring-bearer")

#guard ringFirstTemptOk

def ringSecondTempt : Game := ringFirstTempt.temptWithTheRing ⟨0⟩

def ringSecondTemptOk : Bool :=
  ringSecondTempt.theRingAbilityCount ⟨0⟩ == 2 &&
    (ringSecondTempt.log.filter (fun s => mentions s "gets an emblem named The Ring")).size == 1 &&
    (namedPermanent ringSecondTempt "Grizzly Bears").status.ringBearer

#guard ringSecondTemptOk

/-- Ruling 43: each player has their own emblem and Ring-bearer. -/
def ringBothPlayers : Game :=
  let g := addPermanent (addPermanent started grizzlyBears ⟨0⟩ ⟨0⟩)
    grayOgre ⟨1⟩ ⟨1⟩
  let g := g.temptWithTheRing ⟨0⟩
  g.temptWithTheRing ⟨1⟩

def ringBothPlayersOk : Bool :=
  ringBothPlayers.hasTheRing ⟨0⟩ && ringBothPlayers.hasTheRing ⟨1⟩ &&
    (namedPermanent ringBothPlayers "Grizzly Bears").status.ringBearer &&
    (namedPermanent ringBothPlayers "Gray Ogre").status.ringBearer &&
    !(ringBothPlayers.isRingBearer ⟨0⟩ (namedPermanent ringBothPlayers "Gray Ogre"))

#guard ringBothPlayersOk

/-- Ruling 44: if you control a creature you must choose one. -/
def ringMustChoose : Game :=
  let g := addPermanent started grizzlyBears ⟨0⟩ ⟨0⟩
  g.temptWithTheRing ⟨0⟩ none

#guard (namedPermanent ringMustChoose "Grizzly Bears").status.ringBearer

/-- Ruling 56: the Ring can tempt you with no creature; tempt triggers still fire. -/
def ringNoCreature : Game :=
  let g := addPermanent started ringWatcher ⟨0⟩ ⟨0⟩
  g.temptWithTheRing ⟨0⟩

def ringNoCreatureOk : Bool :=
  ringNoCreature.hasTheRing ⟨0⟩ &&
    (ringNoCreature.player ⟨0⟩).ringBearerId.isNone &&
    ringNoCreature.log.any (fun s => mentions s "controls no creature") &&
    ringNoCreature.waitingTriggers.any (fun wt =>
      wt.ability == .onTheRingTemptsYouDraw 1)

#guard ringNoCreatureOk

/-- Ruling 48: choosing the same creature again still counts as choosing it. -/
def ringRechoose : Game :=
  let g := addPermanent (addPermanent started grizzlyBears ⟨0⟩ ⟨0⟩)
    ringWatcher ⟨0⟩ ⟨0⟩
  let g := g.temptWithTheRing ⟨0⟩ (some (namedPermanent g "Grizzly Bears").id)
  g.temptWithTheRing ⟨0⟩ (some (namedPermanent g "Grizzly Bears").id)

def ringRechooseOk : Bool :=
  (ringRechoose.waitingTriggers.filter (fun wt =>
    wt.ability == .onChooseRingBearerDraw)).size == 2 &&
    (namedPermanent ringRechoose "Grizzly Bears").status.ringBearer

#guard ringRechooseOk

/-- Ruling 54: illegal or missing targets mean the Ring does not tempt you. -/
def ringTargetedFail : Game :=
  started.resolveTargetedTempt ⟨0⟩ .creature #[]

def ringTargetedFailOk : Bool :=
  !(ringTargetedFail.hasTheRing ⟨0⟩) &&
    ringTargetedFail.log.any (fun s => mentions s "won't tempt")

#guard ringTargetedFailOk

def ringTargetedOk : Game :=
  let g := addPermanent started grizzlyBears ⟨0⟩ ⟨0⟩
  g.resolveTargetedTempt ⟨0⟩ .creature
    #[Target.permanent (namedPermanent g "Grizzly Bears").id]

#guard ringTargetedOk.hasTheRing ⟨0⟩

/-- Ruling 57: abilities are gained in order and kept. -/
def ringFourTempts : Game :=
  let g := addPermanent started grizzlyBears ⟨0⟩ ⟨0⟩
  (((((g.temptWithTheRing ⟨0⟩).temptWithTheRing ⟨0⟩).temptWithTheRing ⟨0⟩).temptWithTheRing ⟨0⟩).temptWithTheRing ⟨0⟩)

#guard ringFourTempts.theRingAbilityCount ⟨0⟩ == 4

/-- Ruling 22: an emblem is not a permanent. -/
def ringEmblemNotPermanent : Bool :=
  ringFirstTempt.hasTheRing ⟨0⟩ &&
    !(ringFirstTempt.battlefield.any (fun o => o.name == "The Ring"))

#guard ringEmblemNotPermanent

/-!
## 46, 50, 58, 62, 95, 196, 197, 208, 209, 218 — kicker
-/

#guard galadrielSDismissal.kicker == some (ManaCost.ofGenericAndColor 2 .white)
#guard theEaglesAreComing.kicker == some (ManaCost.ofGenericAndColors 2 [.white, .white])
#guard galadrielSDismissal.manaValue == 1

/-- Ruling 46 / 58: paying kicker marks the spell kicked; you cannot kick twice. -/
def kickerProposed : Game :=
  let g := withWhiteMana (addToHand afterDraw galadrielSDismissal ⟨0⟩) ⟨0⟩ 4
  mustApply g ⟨0⟩ (.cast (handCardNamed g ⟨0⟩ "Galadriel's Dismissal").id)

def kickerProposedOk : Bool :=
  kickerProposed.pending == .chooseKicker ⟨0⟩ &&
    !(kickerProposed.object! kickerProposed.stack.back!.objectId).kicked

#guard kickerProposedOk

def kickerPaid : Game := mustApply kickerProposed ⟨0⟩ (.announceKicker true)

def kickerPaidOk : Bool :=
  (kickerPaid.object! kickerPaid.stack.back!.objectId).kicked &&
    (match kickerPaid.proposedSpell with
     | some prop => prop.kicked && prop.cost.manaValue == 4
     | none => false)

#guard kickerPaidOk

def kickerTwiceFails : Bool :=
  match kickerPaid.applyKickerToProposed true with
  | .error e => e.contains "more than once"
  | .ok _ => false

#guard kickerTwiceFails

/-- Ruling 62: mana value is unchanged by paying kicker. -/
def kickerManaValueUnchanged : Bool :=
  (kickerPaid.object! kickerPaid.stack.back!.objectId).printed.manaValue == 1 &&
    (match kickerPaid.proposedSpell with
     | some prop => prop.cost.manaValue > 1
     | none => false)

#guard kickerManaValueUnchanged

/-- Ruling 218: putting a kicker permanent onto the battlefield does not kick it. -/
def kickerNotCast : Game := addPermanent started galadrielSDismissal ⟨0⟩ ⟨0⟩

#guard !(namedPermanent kickerNotCast "Galadriel's Dismissal").kicked

/-- Ruling 50 / 95 / 196 / 197: casting without paying the mana cost still
allows kicker as an additional cost. -/
def kickerWithoutManaCost : Game :=
  let g := addToHand afterDraw galadrielSDismissal ⟨0⟩
  let card := handCardNamed g ⟨0⟩ "Galadriel's Dismissal"
  let g := g.setObject { card with
    playPermission := some {
      player := ⟨0⟩
      turnEndsRemaining := 1
      withoutManaCost := true } }
  let g := mustApply g ⟨0⟩ (.cast (handCardNamed g ⟨0⟩ "Galadriel's Dismissal").id)
  mustApply g ⟨0⟩ (.announceKicker true)

def kickerWithoutManaCostOk : Bool :=
  (kickerWithoutManaCost.object! kickerWithoutManaCost.stack.back!.objectId).kicked &&
    (match kickerWithoutManaCost.proposedSpell with
     | some prop => prop.cost.manaValue == 3
     | none => false)

#guard kickerWithoutManaCostOk

/-- Ruling 208 / 209: a copy of a kicked spell is also kicked. -/
def kickerCopied : Game :=
  let spell := kickerPaid.object! kickerPaid.stack.back!.objectId
  kickerPaid.copyStackSpell spell ⟨0⟩

#guard (kickerCopied.object! kickerCopied.stack.back!.objectId).kicked
#guard (kickerCopied.object! kickerCopied.stack.back!.objectId).isCopy

/-!
## 65, 83, 124, 152, 210, 333 — gift
-/

#guard bilboSGambit.giftTreasure

/-- Ruling 83 / 333: gift is promised as an additional cost, not given yet,
and cannot be promised twice. -/
def giftProposed : Game :=
  let g := withWhiteMana (addToHand afterDraw bilboSGambit ⟨0⟩) ⟨0⟩ 2
  mustApply g ⟨0⟩ (.cast (handCardNamed g ⟨0⟩ "Bilbo's Gambit").id)

def giftProposedOk : Bool :=
  giftProposed.pending == .chooseGift ⟨0⟩ &&
    (giftProposed.object! giftProposed.stack.back!.objectId).giftPromisedTo.isNone

#guard giftProposedOk

def giftPromised : Game := mustApply giftProposed ⟨0⟩ (.announceGift (some ⟨1⟩))

def giftPromisedOk : Bool :=
  (giftPromised.object! giftPromised.stack.back!.objectId).giftPromisedTo == some ⟨1⟩ &&
    !(giftPromised.battlefield.any (fun o => o.name == "Treasure"))

#guard giftPromisedOk

def giftTwiceFails : Bool :=
  match giftPromised.applyGiftToProposed (some ⟨1⟩) with
  | .error e => e.contains "more than once"
  | .ok _ => false

#guard giftTwiceFails

/-- Ruling 124 / 65: on resolution of an instant, the gift is given before
other effects. -/
def giftGivenOnResolve : Game :=
  let g := giftPromised
  -- Skip remaining proposal (targets / pay) by resolving a ready stack object.
  let spell := g.object! g.stack.back!.objectId
  g.givePromisedGift (spell.giftPromisedTo.getD ⟨1⟩)

#guard giftGivenOnResolve.battlefield.any (fun o => o.name == "Treasure" && o.controlledBy ⟨1⟩)

/-- Ruling 152: if the spell is removed without resolving, the gift is not given. -/
def giftCountered : Game :=
  let spell := giftPromised.object! giftPromised.stack.back!.objectId
  (giftPromised.move spell.id (.graveyard spell.owner) none).1

#guard !(giftCountered.battlefield.any (fun o => o.name == "Treasure"))

/-- Ruling 210: a copy inherits the promised gift. -/
def giftCopied : Game :=
  let spell := giftPromised.object! giftPromised.stack.back!.objectId
  giftPromised.copyStackSpell spell ⟨0⟩

#guard (giftCopied.object! giftCopied.stack.back!.objectId).giftPromisedTo == some ⟨1⟩

/-!
## 67, 168, 235, 245 — shadow
-/

def shadowCreature : CardDef :=
  creature "Shadow Scout" (ManaCost.ofGeneric 1) #["Wraith"] 1 1
    (keywords := Keyword.shadow)

/-- Ruling 67: a shadow counter grants shadow. -/
def shadowFromCounter : Game :=
  let g := addPermanent started grizzlyBears ⟨0⟩ ⟨0⟩
  g.putShadowCounter (namedPermanent g "Grizzly Bears")

def shadowFromCounterOk : Bool :=
  shadowFromCounter.hasShadow (namedPermanent shadowFromCounter "Grizzly Bears") &&
    shadowFromCounter.hasSubtype
      (namedPermanent shadowFromCounter "Grizzly Bears") "Wraith"

#guard shadowFromCounterOk

/-- Ruling 235: multiple instances of shadow are redundant. -/
def shadowTwice : Game :=
  shadowFromCounter.putShadowCounter
    (namedPermanent shadowFromCounter "Grizzly Bears")

#guard (namedPermanent shadowTwice "Grizzly Bears").status.shadow == 2
#guard shadowTwice.hasShadow (namedPermanent shadowTwice "Grizzly Bears")

/-- Ruling 168: shadow and flying both restrict blockers. -/
def shadowBlockSetup : Game :=
  let g := addPermanent (addPermanent started shadowCreature ⟨0⟩ ⟨0⟩)
    grizzlyBears ⟨1⟩ ⟨1⟩
  let atk := namedPermanent g "Shadow Scout"
  g.setObject { atk with status := { atk.status with attacking := true } }

def shadowCannotBlock : Bool :=
  !shadowBlockSetup.canBlock
    (namedPermanent shadowBlockSetup "Grizzly Bears")
    (namedPermanent shadowBlockSetup "Shadow Scout")

#guard shadowCannotBlock

def shadowCanBlockShadow : Game :=
  let g := addPermanent shadowBlockSetup
    (creature "Wraith Guard" (ManaCost.ofGeneric 1) #["Wraith"] 1 1
      (keywords := Keyword.shadow)) ⟨1⟩ ⟨1⟩
  g

def shadowCanBlockShadowOk : Bool :=
  shadowCanBlockShadow.canBlock
    (namedPermanent shadowCanBlockShadow "Wraith Guard")
    (namedPermanent shadowCanBlockShadow "Shadow Scout")

#guard shadowCanBlockShadowOk

/-- Ruling 245: once blocked, gaining or losing shadow does not undo the block. -/
def shadowRemainsBlocked : Game :=
  let g := addPermanent (addPermanent started grizzlyBears ⟨0⟩ ⟨0⟩)
    (creature "Chump" (ManaCost.ofGeneric 1) #["Human"] 1 1) ⟨1⟩ ⟨1⟩
  let atk := namedPermanent g "Grizzly Bears"
  let g := g.setObject { atk with status := { atk.status with
    attacking := true, blocked := true } }
  let blk := namedPermanent g "Chump"
  let g := g.setObject { blk with status := { blk.status with
    blocking := #[atk.id] } }
  g.putShadowCounter (namedPermanent g "Grizzly Bears")

def shadowRemainsBlockedOk : Bool :=
  (namedPermanent shadowRemainsBlocked "Grizzly Bears").status.blocked &&
    shadowRemainsBlocked.hasShadow (namedPermanent shadowRemainsBlocked "Grizzly Bears")

#guard shadowRemainsBlockedOk

/-!
## 76–77, 82, 107, 253–255 — phasing
-/

/-- Ruling 254 / 76: a phased-out creature is treated as though it does not
exist and is removed from combat. -/
def phasedAttacker : Game :=
  let g := addPermanent (addPermanent started grizzlyBears ⟨0⟩ ⟨0⟩)
    dwarvenShortsword ⟨0⟩ ⟨0⟩
  let host := namedPermanent g "Grizzly Bears"
  let eq := namedPermanent g "Dwarven Shortsword"
  let g := g.attachSourceTo eq host
  let host := namedPermanent g "Grizzly Bears"
  let g := g.setObject { host with status := { host.status with attacking := true } }
  g.phaseOut (namedPermanent g "Grizzly Bears")

def phasedAttackerOk : Bool :=
  (namedObject phasedAttacker "Grizzly Bears").status.phasedOut &&
    !(namedObject phasedAttacker "Grizzly Bears").isOnBattlefield &&
    !(namedObject phasedAttacker "Grizzly Bears").status.attacking &&
    (namedObject phasedAttacker "Dwarven Shortsword").status.phasedOut &&
    phasedAttacker.permanentCount ⟨0⟩ == 0 &&
    (ruling 76).comment.contains "removed from combat"

#guard phasedAttackerOk

/-- Ruling 82 / 253: attachments phase in still attached; counters persist;
the creature can attack. -/
def phasedIn : Game :=
  let g := addPermanent started grizzlyBears ⟨0⟩ ⟨0⟩
  let o := namedPermanent g "Grizzly Bears"
  let g := g.mapObjectStatus o (fun s => { s with plusOnePlusOne := 2 })
  let g := g.phaseOut (namedObject g "Grizzly Bears")
  g.phaseIn (namedObject g "Grizzly Bears")

def phasedInOk : Bool :=
  !(namedObject phasedIn "Grizzly Bears").status.phasedOut &&
    (namedObject phasedIn "Grizzly Bears").status.plusOnePlusOne == 2 &&
    !(namedObject phasedIn "Grizzly Bears").status.summoningSick &&
    phasedIn.canAttack (namedObject phasedIn "Grizzly Bears")

#guard phasedInOk

/-- Ruling 255: phasing does not trigger enters or leaves. -/
def phaseNoTriggers : Game :=
  let g := addPermanent (addPermanent started mentorOfTheMeek ⟨0⟩ ⟨0⟩)
    grizzlyBears ⟨0⟩ ⟨0⟩
  let g := g.phaseOut (namedPermanent g "Grizzly Bears")
  g.phaseIn (namedObject g "Grizzly Bears")

#guard phaseNoTriggers.stack.isEmpty
#guard phaseNoTriggers.waitingTriggers.isEmpty

/-- Ruling 107: additional subtypes chosen as the permanent entered are
remembered when it phases in. -/
def phaseRemembersTypes : Game :=
  let g := addPermanent started grizzlyBears ⟨0⟩ ⟨0⟩
  let o := namedPermanent g "Grizzly Bears"
  let g := g.setObject { o with status := { o.status with
    additionalSubtypes := #["Wraith"] } }
  let g := g.phaseOut (namedPermanent g "Grizzly Bears")
  g.phaseIn (namedObject g "Grizzly Bears")

#guard phaseRemembersTypes.hasSubtype (namedPermanent phaseRemembersTypes "Grizzly Bears") "Wraith"

/-- Ruling 77: continuous effects ignore phased-out objects. Hone on a
phased-out Equipment does not boost the host. -/
def phaseIgnoresHone : Game :=
  let g := addPermanent (addPermanent started dwarvenShortsword ⟨0⟩ ⟨0⟩)
    grizzlyBears ⟨0⟩ ⟨0⟩
  let g := honeOn g "Dwarven Shortsword" "Grizzly Bears" 3
  let eq := namedPermanent g "Dwarven Shortsword"
  g.phaseOut eq

#guard phaseIgnoresHone.power (namedPermanent phaseIgnoresHone "Grizzly Bears") == 2

/-!
## 68, 101, 110, 113–114, 157, 238, 323 — cascade
-/

#guard callForthTheTempest.cascade == 2
#guard callForthTheTempest.manaValue == 8

/-- Ruling 68: mana value ignores alternative and additional costs. -/
def cascadeManaValueIsPrinted : Bool :=
  callForthTheTempest.manaValue == 8 &&
    callForthTheTempest.manaCost.manaValue == 8

#guard cascadeManaValueIsPrinted

/-- Ruling 101 / 114: cascade triggers when the spell is cast, once per
instance, and sits above the spell. -/
def cascadeOnCast : Game :=
  let g := addToHand afterDraw callForthTheTempest ⟨0⟩
  -- Give enough red/generic to propose; cascade triggers on becomeCast.
  let g := withWhiteMana g ⟨0⟩ 0
  -- Put the spell on the stack as if it finished casting.
  let id := (handCardNamed g ⟨0⟩ "Call Forth the Tempest").id
  let (g, newId) := g.move id .stack (some ⟨0⟩)
  let g := g.putStackEntry ⟨0⟩ newId
  g.becomeCast ⟨0⟩ (g.object! newId)

def cascadeOnCastOk : Bool :=
  let cascades := cascadeOnCast.stack.filter (fun e =>
    (cascadeOnCast.object! e.objectId).triggeredAbility == some .onCastCascade)
  cascades.size == 2 &&
    cascadeOnCast.stack.any (fun e =>
      (cascadeOnCast.object! e.objectId).name == "Call Forth the Tempest") &&
    (cascadeOnCast.player ⟨0⟩).castManaValuesThisTurn == #[8]

#guard cascadeOnCastOk

/-- Ruling 323 / 113: cascade must exile; the resulting spell must have
lesser mana value. Casting is optional. -/
def cascadeExiles : Game :=
  let (g, bolt) := started.allocObject lightningBolt ⟨0⟩ (.library ⟨0⟩)
  let (g, land) := g.allocObject forest ⟨0⟩ (.library ⟨0⟩)
  let g := g.setPlayer { (g.player ⟨0⟩) with library := #[bolt.id, land.id] }
  g.resolveCascade ⟨0⟩ 8

def cascadeExilesOk : Bool :=
  cascadeExiles.log.any (fun s => mentions s "cascade") &&
    cascadeExiles.objects.any (fun o =>
      o.zone == .exile && !o.printed.isLand)

#guard cascadeExilesOk

/-- Ruling 113: an Adventure card's resulting permanent spell must also be
cheaper. Smaug (MV 6) is cheaper than 8; the test card with MV 9 is not. -/
def expensiveCreature : CardDef :=
  creature "Costly Beast" (ManaCost.ofGeneric 9) #["Beast"] 9 9

/-- Ruling 113: the resulting spell's mana value must be less than the
cascade spell's. A 9-mana creature cannot be cast off an 8-mana cascade. -/
def cascadeResultTooExpensive : Bool :=
  let g := addToLibraryTop started expensiveCreature ⟨0⟩
  match g.objects.find? (fun o => o.name == "Costly Beast") with
  | none => false
  | some card =>
    match g.castCascadeCard ⟨0⟩ card.id 8 with
    | .error e => e.contains "lesser mana value"
    | .ok _ => false

#guard cascadeResultTooExpensive

/-- Ruling 110: copies that were not cast are omitted from the total. -/
def cascadeCopyNotCast : Game :=
  let g := cascadeOnCast
  let spell := g.object! (g.stack.find? (fun e =>
    (g.object! e.objectId).name == "Call Forth the Tempest") |>.get!).objectId
  g.copyStackSpell spell ⟨0⟩

#guard cascadeCopyNotCast.otherCastManaValueThisTurn ⟨0⟩ == 8
#guard (cascadeCopyNotCast.object! cascadeCopyNotCast.stack.back!.objectId).isCopy

/-- Ruling 157: countering the cascade spell leaves the cascade triggers. -/
def cascadeSpellRemoved : Game :=
  let spellE := cascadeOnCast.stack.find? (fun e =>
    (cascadeOnCast.object! e.objectId).name == "Call Forth the Tempest")
  match spellE with
  | none => cascadeOnCast
  | some e =>
    let o := cascadeOnCast.object! e.objectId
    (cascadeOnCast.move o.id (.graveyard o.owner) none).1

def cascadeSpellRemovedOk : Bool :=
  (cascadeSpellRemoved.stack.filter (fun e =>
    (cascadeSpellRemoved.object! e.objectId).triggeredAbility ==
      some .onCastCascade)).size == 2

#guard cascadeSpellRemovedOk

/-- Ruling 238: each cascade instance looks at Call Forth's mana value of 8. -/
def cascadeLooksAtEight : Bool :=
  (ruling 238).comment.contains "mana value of 8" &&
    callForthTheTempest.manaValue == 8

#guard cascadeLooksAtEight

/-!
## 84, 207, 223, 251 — ascend / city's blessing
-/

#guard andurilNarsilReforged.keywords.ascend

/-- Ruling 207: ten permanents without ascend grant nothing. -/
def tenTreasures : Game := started.createTreasureTokens ⟨0⟩ 10

#guard tenTreasures.permanentCount ⟨0⟩ == 10
#guard !(tenTreasures.controlsAscend ⟨0⟩)
#guard !(tenTreasures.hasCitysBlessing ⟨0⟩)

/-- Ruling 207: Andúril entering as the ninth permanent is not enough. -/
def nineThenAnduril : Game :=
  let g := started.createTreasureTokens ⟨0⟩ 8
  let g := addPermanent g andurilNarsilReforged ⟨0⟩ ⟨0⟩
  g.refreshCitysBlessing

#guard nineThenAnduril.permanentCount ⟨0⟩ == 9
#guard nineThenAnduril.controlsAscend ⟨0⟩
#guard !(nineThenAnduril.hasCitysBlessing ⟨0⟩)

/-- Ruling 84 / 223: the tenth permanent with ascend grants the blessing
before SBA, and it is not a triggered ability. -/
def tenWithAscend : Game :=
  let g := started.createTreasureTokens ⟨0⟩ 9
  let g := addPermanent g andurilNarsilReforged ⟨0⟩ ⟨0⟩
  g.afterPermanentEnters (namedPermanent g "Andúril, Narsil Reforged")

def tenWithAscendOk : Bool :=
  tenWithAscend.hasCitysBlessing ⟨0⟩ &&
    tenWithAscend.stack.isEmpty &&
    tenWithAscend.log.any (fun s => mentions s "city's blessing")

#guard tenWithAscendOk

/-- Ruling 223: a 0/0 tenth permanent that then dies still leaves the blessing. -/
def zeroAscend : CardDef :=
  legendaryCreature "Zero Blessing" ManaCost.empty #["Spirit"] 0 0
    (keywords := Keyword.ascend)

def blessingFromZero : Game :=
  let g := started.createTreasureTokens ⟨0⟩ 9
  let g := addPermanent g zeroAscend ⟨0⟩ ⟨0⟩
  let g := g.afterPermanentEnters (namedPermanent g "Zero Blessing")
  g.checkSBA

#guard blessingFromZero.hasCitysBlessing ⟨0⟩
#guard !(blessingFromZero.battlefield.any (fun o => o.name == "Zero Blessing"))

/-- Ruling 251: the designation stays after the permanents leave. -/
def blessingThenLost : Game :=
  tenWithAscend.battlefield.foldl (fun acc o =>
    if o.controlledBy ⟨0⟩ then (acc.move o.id (.graveyard o.owner) none).1 else acc)
    tenWithAscend

#guard blessingThenLost.hasCitysBlessing ⟨0⟩
#guard blessingThenLost.permanentCount ⟨0⟩ == 0

/-!
## 17, 53 — targeted amass that fails does not amass
-/

def amassIfLegal (g : Game) (p : PlayerId) (targetsLegal : Bool) (n : Nat) : Game :=
  if targetsLegal then g.amassGoblins p n
  else g.logMsg "The spell doesn't resolve. You won't amass Goblins."

def amassFailedOk : Bool :=
  let g := amassIfLegal started ⟨0⟩ false 2
  !(g.battlefield.any (fun o => g.hasSubtype o "Army")) &&
    g.log.any (fun s => mentions s "won't amass") &&
    (ruling 17).comment.contains "won't amass" &&
    (ruling 53).comment.contains "won't amass Orcs"

#guard amassFailedOk

/-!
## 7 — an Adventure copy ceases to exist; it cannot be cast as a permanent
-/

def adventureCopyCannotRecast : Bool :=
  (ruling 7).comment.contains "ceases to exist" &&
    smaugTheGreatCalamity.adventure.isSome

#guard adventureCopyCannotRecast

/-!
## 79, 81, 127 — Galion sets base P/T
-/

/-- Ruling 81: Galion copies its actual power and toughness, not its base. -/
def galionSetsActualPtOk : Bool :=
  galionResolved.basePower (namedPermanent galionResolved "Llanowar Elves") == 4 &&
    galionResolved.baseToughness (namedPermanent galionResolved "Llanowar Elves") == 4 &&
    galionPumpedResolved.power
      (namedPermanent galionPumpedResolved "Galion, Elvenking's Butler") == 6 &&
    galionPumpedResolved.power (namedPermanent galionPumpedResolved "Llanowar Elves") == 6

#guard galionSetsActualPtOk

/-- Ruling 81: later changes to Galion do not update the other creature. -/
def galionLaterPumpOk : Bool :=
  galionPumpedAfterResolve.power
      (namedPermanent galionPumpedAfterResolve "Galion, Elvenking's Butler") == 7 &&
    galionPumpedAfterResolve.power
      (namedPermanent galionPumpedAfterResolve "Llanowar Elves") == 4

#guard galionLaterPumpOk

/-- Ruling 79 / 127: counters and other modifiers apply after the new base;
later set-P/T effects overwrite Galion's. -/
def galionCountersAfterBaseOk : Bool :=
  galionOnCounteredElves.basePower
      (namedPermanent galionOnCounteredElves "Llanowar Elves") == 4 &&
    galionOnCounteredElves.power
      (namedPermanent galionOnCounteredElves "Llanowar Elves") == 5 &&
    (ruling 127).comment.contains "overwrites all previous effects"

#guard galionCountersAfterBaseOk

/-!
## 91–92, 123, 169, 203, 265 — Bard token doubling
## 204, 219 — Bilbo Food also creates Treasure
-/

def withBard : Game := addPermanent afterDraw bardKingOfDale ⟨0⟩ ⟨0⟩

/-- Ruling 91: Bard doubles created tokens, not nontoken permanents that
happen to become tokens when a copy of a permanent spell resolves. -/
def bardCreatesTwoTreasures : Game :=
  (withBard.createToken ⟨0⟩ Game.treasureToken).1

def bardDoesNotDoubleNontoken : Game :=
  addPermanent withBard grizzlyBears ⟨0⟩ ⟨0⟩

def bardTokenNotNontokenOk : Bool :=
  (bardCreatesTwoTreasures.battlefield.filter (fun o => o.name == "Treasure")).size == 2 &&
    (bardDoesNotDoubleNontoken.battlefield.filter (fun o =>
      o.name == "Grizzly Bears")).size == 1 &&
    !(namedPermanent bardDoesNotDoubleNontoken "Grizzly Bears").printed.isToken &&
    (ruling 91).comment.contains "will not be doubled"

#guard bardTokenNotNontokenOk

/-- Ruling 123: the doubled tokens enter with the same characteristics. -/
def bardTokensSame : Bool :=
  let ts := bardCreatesTwoTreasures.battlefield.filter (fun o => o.name == "Treasure")
  ts.size == 2 &&
    ts[0]!.printed.types == ts[1]!.printed.types &&
    ts[0]!.printed.subtypes == ts[1]!.printed.subtypes &&
    ts[0]!.printed.isToken && ts[1]!.printed.isToken &&
    (ruling 123).comment.contains "same name"

#guard bardTokensSame

/-- Ruling 92: two Bards multiply draws by four (skip legend-rule SBA). -/
def twoBards : Game :=
  addPermanent withBard bardKingOfDale ⟨0⟩ ⟨0⟩

def twoBardsDraw : Game := twoBards.draw ⟨0⟩ 1

def twoBardsDrawOk : Bool :=
  (twoBards.battlefield.filter (fun o => o.name == "Bard, King of Dale")).size == 2 &&
    (twoBardsDraw.player ⟨0⟩).hand.size == (afterDraw.player ⟨0⟩).hand.size + 4 &&
    (ruling 92).comment.contains "multiplied by four"

#guard twoBardsDrawOk

/-- Ruling 92: one Bard doubles a draw that is not the first of your draw step. -/
def oneBardMainDraw : Game := withBard.draw ⟨0⟩ 1

#guard (oneBardMainDraw.player ⟨0⟩).hand.size == (afterDraw.player ⟨0⟩).hand.size + 2

/-- Ruling 92: the first card of your draw step is not replaced. -/
def bardOnNissaUpkeep : Game :=
  addPermanent afterSilentCleanup bardKingOfDale ⟨1⟩ ⟨1⟩

def bardFirstDrawStep : Game := skipTo bardOnNissaUpkeep .draw 80

def bardFirstDrawStepOk : Bool :=
  bardFirstDrawStep.step == .draw &&
    bardFirstDrawStep.activePlayer == ⟨1⟩ &&
    (bardFirstDrawStep.player ⟨1⟩).hand.size ==
      (afterSilentCleanup.player ⟨1⟩).hand.size + 1

#guard bardFirstDrawStepOk

/-- A later draw in the same draw step is replaced. -/
def bardSecondDrawStep : Game := bardFirstDrawStep.draw ⟨1⟩ 1

#guard
  (bardSecondDrawStep.player ⟨1⟩).hand.size ==
    (afterSilentCleanup.player ⟨1⟩).hand.size + 3

/-- Ruling 265: two Bards create four times as many tokens. -/
def twoBardsFourTreasures : Game :=
  (twoBards.createToken ⟨0⟩ Game.treasureToken).1

#guard
  (twoBardsFourTreasures.battlefield.filter (fun o => o.name == "Treasure")).size == 4
#guard (ruling 265).comment.contains "four times"

/-- Ruling 203: amass with Bard creates two Armies; counters go on one;
the other dies as a 0/0. -/
def bardAmass : Game := withBard.amassGoblins ⟨0⟩ 3

def bardAmassBeforeSbaOk : Bool :=
  let armies := bardAmass.battlefield.filter (fun o => o.name == "Goblin Army")
  armies.size == 2 &&
    armies.any (fun o => o.status.plusOnePlusOne == 3) &&
    armies.any (fun o => o.status.plusOnePlusOne == 0)

#guard bardAmassBeforeSbaOk

def bardAmassAfterSba : Game := bardAmass.checkSBA

def bardAmassAfterSbaOk : Bool :=
  let armies := bardAmassAfterSba.battlefield.filter (fun o => o.name == "Goblin Army")
  armies.size == 1 && armies[0]!.status.plusOnePlusOne == 3

#guard bardAmassAfterSbaOk

/-- Ruling 204: creating N Food with Bilbo also creates N Treasure. -/
def withBilbo : Game := addPermanent afterDraw bilboFellowConspirator ⟨0⟩ ⟨0⟩

def bilboOneFood : Game := (withBilbo.createToken ⟨0⟩ Game.foodToken).1

def bilboOneFoodOk : Bool :=
  (bilboOneFood.battlefield.filter (fun o => o.name == "Food")).size == 1 &&
    (bilboOneFood.battlefield.filter (fun o => o.name == "Treasure")).size == 1

#guard bilboOneFoodOk

def bilboTwoFood : Game := withBilbo.createKindTokens ⟨0⟩ .food 2

def bilboTwoFoodOk : Bool :=
  (bilboTwoFood.battlefield.filter (fun o => o.name == "Food")).size == 2 &&
    (bilboTwoFood.battlefield.filter (fun o => o.name == "Treasure")).size == 2 &&
    (ruling 204).comment.contains "that many Treasure"

#guard bilboTwoFoodOk

/-- Ruling 219: two Bilbos add two Treasures per Food (skip legend-rule SBA). -/
def twoBilbos : Game :=
  addPermanent withBilbo bilboFellowConspirator ⟨0⟩ ⟨0⟩

def twoBilbosFood : Game := (twoBilbos.createToken ⟨0⟩ Game.foodToken).1

def twoBilbosFoodOk : Bool :=
  (twoBilbos.battlefield.filter (fun o => o.name == "Bilbo, Fellow Conspirator")).size == 2 &&
    (twoBilbosFood.battlefield.filter (fun o => o.name == "Food")).size == 1 &&
    (twoBilbosFood.battlefield.filter (fun o => o.name == "Treasure")).size == 2 &&
    (ruling 219).comment.contains "twice that many Treasure"

#guard twoBilbosFoodOk

/-- Ruling 169: Bard plus Bilbo on one Food yields two Food and two Treasure
regardless of replacement order. -/
def bardAndBilbo : Game :=
  addPermanent withBard bilboFellowConspirator ⟨0⟩ ⟨0⟩

def bardAndBilboFood : Game := (bardAndBilbo.createToken ⟨0⟩ Game.foodToken).1

def bardAndBilboFoodOk : Bool :=
  (bardAndBilboFood.battlefield.filter (fun o => o.name == "Food")).size == 2 &&
    (bardAndBilboFood.battlefield.filter (fun o => o.name == "Treasure")).size == 2 &&
    (ruling 169).comment.contains "two Food tokens and two Treasure tokens"

#guard bardAndBilboFoodOk

/-!
## 39, 47, 73, 87–89, 134, 136–138 — linked exile
-/

/-- Ruling 39 / 73: a returned permanent is a new object, not in combat,
and has no counters. -/
def exileReturnNewObjectOk : Bool :=
  let g := addPermanent afterDraw fiendHunter ⟨0⟩ ⟨0⟩
  let g := addPermanent g grizzlyBears ⟨1⟩ ⟨1⟩
  let bears := namedPermanent g "Grizzly Bears"
  let oldId := bears.id
  let g := g.setObject { bears with status :=
    { bears.status with attacking := true, plusOnePlusOne := 2 } }
  let hunter := namedPermanent g "Fiend Hunter"
  let g := g.exileUntilSourceLeaves (some hunter.id) (namedPermanent g "Grizzly Bears")
  let hunter := namedPermanent g "Fiend Hunter"
  let g := (g.move hunter.id (.graveyard ⟨0⟩) none).1
  let returned := namedPermanent g "Grizzly Bears"
  returned.id != oldId &&
    !returned.status.attacking &&
    returned.status.plusOnePlusOne == 0 &&
    (ruling 39).comment.contains "new object" &&
    (ruling 73).comment.contains "won't be in combat"

#guard exileReturnNewObjectOk

/-- Ruling 47: an exiled token ceases to exist and does not return. -/
def exileTokenNoReturn : Game :=
  let g := addPermanent afterDraw fiendHunter ⟨0⟩ ⟨0⟩
  let (g, tok) := g.createToken ⟨1⟩ Game.wolfToken
  let hunter := namedPermanent g "Fiend Hunter"
  let g := g.exileUntilSourceLeaves (some hunter.id) (g.object! tok.id)
  let g := g.checkSBA
  let hunter := namedPermanent g "Fiend Hunter"
  (g.move hunter.id (.graveyard ⟨0⟩) none).1.checkSBA

def exileTokenNoReturnOk : Bool :=
  !(exileTokenNoReturn.battlefield.any (fun o => o.name == "Wolf")) &&
    !(exileTokenNoReturn.objects.any (fun o =>
      o.name == "Wolf" && o.zone == .exile)) &&
    exileTokenNoReturn.log.any (fun s => mentions s "ceases to exist") &&
    (ruling 47).comment.contains "will not return"

#guard exileTokenNoReturnOk

/-- Ruling 87 / 88 / 89: Auras go to the graveyard; Equipment stays
unattached; counters cease. -/
def exileAuraAndEquip : Game :=
  let g := addPermanent afterDraw fiendHunter ⟨0⟩ ⟨0⟩
  let g := addPermanent g grizzlyBears ⟨1⟩ ⟨1⟩
  let g := addPermanent g fogOnTheBarrowDowns ⟨1⟩ ⟨1⟩
  let g := addPermanent g dunedainBlade ⟨1⟩ ⟨1⟩
  let g := g.attachSourceTo (namedPermanent g "Fog on the Barrow-Downs")
    (namedPermanent g "Grizzly Bears")
  let g := g.attachSourceTo (namedPermanent g "Dúnedain Blade")
    (namedPermanent g "Grizzly Bears")
  let bears := namedPermanent g "Grizzly Bears"
  let g := g.setObject { bears with status :=
    { bears.status with plusOnePlusOne := 1 } }
  let hunter := namedPermanent g "Fiend Hunter"
  let g := g.exileUntilSourceLeaves (some hunter.id) (namedPermanent g "Grizzly Bears")
  g.checkSBA

def exileAuraAndEquipOk : Bool :=
  let fogGy := exileAuraAndEquip.objects.any (fun o =>
    o.name == "Fog on the Barrow-Downs" && o.zone == .graveyard ⟨1⟩)
  let blade := namedPermanent exileAuraAndEquip "Dúnedain Blade"
  let bearsExiled := exileAuraAndEquip.objects.find? (fun o =>
    o.name == "Grizzly Bears" && o.zone == .exile)
  fogGy && blade.isOnBattlefield && blade.attachedTo.isNone &&
    (match bearsExiled with
     | some o => o.status.plusOnePlusOne == 0
     | none => false) &&
    (ruling 87).comment.contains "Equipment" &&
    (ruling 88).comment.contains "Auras" &&
    (ruling 89).comment.contains "new object"

#guard exileAuraAndEquipOk

/-- Ruling 134 / 136 / 137: if a “until this leaves” source is gone, nothing
is exiled. -/
def sourceLeftNoExile : Game :=
  let g := addPermanent afterDraw banishingLight ⟨0⟩ ⟨0⟩
  let g := addPermanent g grizzlyBears ⟨1⟩ ⟨1⟩
  let lightId := (namedPermanent g "Banishing Light").id
  let bearsId := (namedPermanent g "Grizzly Bears").id
  let g := (g.move lightId (.graveyard ⟨0⟩) none).1
  g.applyTriggeredAbility ⟨0⟩ .onEnterExileOppNonlandUntilLeaves (some lightId)
    #[Target.permanent bearsId]

def sourceLeftNoExileOk : Bool :=
  sourceLeftNoExile.battlefield.any (fun o => o.name == "Grizzly Bears") &&
    sourceLeftNoExile.log.any (fun s => mentions s "Nothing is exiled") &&
    ((ruling 134).comment.contains "won't be exiled" ||
      (ruling 134).comment.contains "won’t be exiled") &&
    (ruling 137).comment.contains "won't be exiled"

#guard sourceLeftNoExileOk

/-- Ruling 138: Fiend Hunter's first ability still exiles if it already left;
the leave trigger had nothing to return. -/
def fiendLeftStillExiles : Game :=
  let g := addPermanent afterDraw fiendHunter ⟨0⟩ ⟨0⟩
  let g := addPermanent g grizzlyBears ⟨1⟩ ⟨1⟩
  let hunterId := (namedPermanent g "Fiend Hunter").id
  let bearsId := (namedPermanent g "Grizzly Bears").id
  let g := (g.move hunterId (.graveyard ⟨0⟩) none).1
  g.applyTriggeredAbility ⟨0⟩ .onEnterMayExileAnotherCreature (some hunterId)
    #[Target.permanent bearsId]

def fiendLeftStillExilesOk : Bool :=
  !(fiendLeftStillExiles.battlefield.any (fun o => o.name == "Grizzly Bears")) &&
    fiendLeftStillExiles.objects.any (fun o =>
      o.name == "Grizzly Bears" && o.zone == .exile) &&
    (ruling 138).comment.contains "first ability"

#guard fiendLeftStillExilesOk

/-!
## 66 — attacks alone
-/

def ringAndTwoCreatures : Game :=
  let g := addPermanent afterDraw grizzlyBears ⟨0⟩ ⟨0⟩
  let g := addPermanent g grayOgre ⟨0⟩ ⟨0⟩
  let g := addPermanent g bilboSRing ⟨0⟩ ⟨0⟩
  g.attachSourceTo (namedPermanent g "Bilbo's Ring")
    (namedPermanent g "Grizzly Bears")

def ringReadyToAttack : Game :=
  passBoth (skipTo ringAndTwoCreatures .beginningOfCombat 80)

def ringAttacksAlone : Game :=
  mustApply ringReadyToAttack ⟨0⟩
    (.declareAttackers #[(namedPermanent ringReadyToAttack "Grizzly Bears").id])

def ringAttacksAloneOk : Bool :=
  (match ringAttacksAlone.stack.back? with
   | some e =>
     (ringAttacksAlone.object! e.objectId).triggeredAbility ==
       some .onEquippedAttacksAloneDrawLoseLife
   | none => false) &&
    (ruling 66).comment.contains "only creature declared as an attacker"

#guard ringAttacksAloneOk

def ringAloneResolved : Game := passBoth ringAttacksAlone

def ringAloneResolvedOk : Bool :=
  (ringAloneResolved.player ⟨0⟩).hand.size ==
      (ringReadyToAttack.player ⟨0⟩).hand.size + 1 &&
    (ringAloneResolved.player ⟨0⟩).life ==
      (ringReadyToAttack.player ⟨0⟩).life - 1

#guard ringAloneResolvedOk

/-- Ruling 66: attacking with two creatures does not count as attacking alone,
even if only one remains later. -/
def ringAttacksTogether : Game :=
  mustApply ringReadyToAttack ⟨0⟩
    (.declareAttackers #[
      (namedPermanent ringReadyToAttack "Grizzly Bears").id,
      (namedPermanent ringReadyToAttack "Gray Ogre").id])

def ringAttacksTogetherOk : Bool :=
  !ringAttacksTogether.stack.any (fun e =>
    (ringAttacksTogether.object! e.objectId).triggeredAbility ==
      some .onEquippedAttacksAloneDrawLoseLife)

#guard ringAttacksTogetherOk

/-!
## 70, 71 — becoming unblockable after blocked
-/

def stillBlockedAfterUnblockable : Game :=
  bearsBlockOgre.grantCantBeBlockedThisTurn
    (namedPermanent bearsBlockOgre "Gray Ogre")

def stillBlockedAfterUnblockableOk : Bool :=
  (namedPermanent stillBlockedAfterUnblockable "Gray Ogre").status.blocked &&
    stillBlockedAfterUnblockable.hasCantBeBlocked
      (namedPermanent stillBlockedAfterUnblockable "Gray Ogre") &&
    (ruling 70).comment.contains "won't cause that creature to become unblocked" &&
    (ruling 71).comment.contains "won't cause that creature to become unblocked"

#guard stillBlockedAfterUnblockableOk

/-- Ruling 122: Food is an artifact type, never a creature type. -/
def foodIsArtifactTypeOk : Bool :=
  Game.foodToken.isArtifact &&
    !(Game.foodToken.isCreature) &&
    (ruling 122).comment.contains "never a creature type"

#guard foodIsArtifactTypeOk

/-- Ruling 45: hone counters grant +1/+0 on any Equipment. -/
def honeAnyEquipmentOk : Bool :=
  (ruling 45).comment.contains "any Equipment"

#guard honeAnyEquipmentOk

/-!
## 49, 176–178, 185–186 — {X} is 0 without paying the mana cost
-/

def xWithoutPaying : ManaCost :=
  let g := addToHand afterDraw insideInformation ⟨0⟩
  let card := handCardNamed g ⟨0⟩ "Inside Information"
  let card := { card with playPermission := some {
    player := ⟨0⟩, turnEndsRemaining := 1, withoutManaCost := true } }
  g.playManaCost card insideInformation

def xWithoutPayingOk : Bool :=
  xWithoutPaying == ManaCost.zero &&
    insideInformation.manaValue == 2 &&
    (ruling 49).comment.contains "choose 0" &&
    (ruling 176).comment.contains "choose 0" &&
    (ruling 177).comment.contains "choose 0"

#guard xWithoutPayingOk

/-!
## 72, 102, 183 — cost reduction reduces only generic mana
-/

def twoElvesAndKeepers : Game :=
  let g := addPermanent afterDraw llanowarElves ⟨0⟩ ⟨0⟩
  let g := addPermanent g llanowarElves ⟨0⟩ ⟨0⟩
  addToHand g cantankerousKeepers ⟨0⟩

def affinityKeepersCost : ManaCost :=
  let card := handCardNamed twoElvesAndKeepers ⟨0⟩ "Cantankerous Keepers"
  twoElvesAndKeepers.playManaCost card cantankerousKeepers

def affinityKeepersOk : Bool :=
  affinityKeepersCost.coloredCount .green == 1 &&
    affinityKeepersCost.manaValue == 4 &&
    (afterDraw.playManaCost
        (handCardNamed (addToHand afterDraw cantankerousKeepers ⟨0⟩) ⟨0⟩
          "Cantankerous Keepers")
        cantankerousKeepers).manaValue == 6 &&
    (ruling 72).comment.contains "colored mana must still be paid"

#guard affinityKeepersOk

def cavernWithOppArtifacts (n : Nat) : Game :=
  let g := addToHand afterDraw cavernHoardDragon ⟨0⟩
  (List.range n).foldl (init := g) fun g _ =>
    (g.createToken ⟨1⟩ Game.treasureToken).1

def cavernCost (n : Nat) : ManaCost :=
  let g := cavernWithOppArtifacts n
  let card := handCardNamed g ⟨0⟩ "Cavern-Hoard Dragon"
  g.playManaCost card cavernHoardDragon

def cavernCostsOk : Bool :=
  cavernHoardDragon.manaValue == 9 &&
    (cavernCost 0).manaValue == 9 &&
    (cavernCost 3).manaValue == 6 &&
    (cavernCost 3).coloredCount .red == 2 &&
    (cavernCost 7).manaValue == 2 &&
    (cavernCost 7).coloredCount .red == 2 &&
    (ruling 102).comment.contains "greatest number of artifacts" &&
    (ruling 183).comment.contains "{R}{R}"

#guard cavernCostsOk

/-- Ruling 58 / 61 / 65: already-modeled kicker, amass Orcs, and gift wording. -/
def sharedReminderOk : Bool :=
  (ruling 58).comment.contains "more than once" &&
    (ruling 61).comment.contains "Orc Army" &&
    (ruling 65).comment.contains "Treasure token"

#guard sharedReminderOk

/-!
## 128, 311–313 — cost reductions leave colored mana and mana value
-/

def lordWithFlyer : Game :=
  let g := addPermanent afterDraw eaglesOfTheNorth ⟨0⟩ ⟨0⟩
  addToHand g theLordOfTheEagles ⟨0⟩

def lordOfEaglesCost : ManaCost :=
  let card := handCardNamed lordWithFlyer ⟨0⟩ "The Lord of the Eagles"
  lordWithFlyer.playManaCost card theLordOfTheEagles

def lordOfEaglesCostOk : Bool :=
  theLordOfTheEagles.manaValue == 9 &&
    lordOfEaglesCost.manaValue == 6 &&
    lordOfEaglesCost.coloredCount .blue == 2 &&
    (ruling 313).comment.contains "mana value of the spell remains unchanged"

#guard lordOfEaglesCostOk

def glamdringAndBolt : Game :=
  let g := addPermanent afterDraw grizzlyBears ⟨0⟩ ⟨0⟩
  let g := addPermanent g glamdringFoeHammer ⟨0⟩ ⟨0⟩
  let g := g.attachSourceTo (namedPermanent g "Glamdring, Foe-hammer")
    (namedPermanent g "Grizzly Bears")
  addToHand g hithlainKnots ⟨0⟩

def glamdringReducedCost : ManaCost :=
  let card := handCardNamed glamdringAndBolt ⟨0⟩ "Hithlain Knots"
  glamdringAndBolt.playManaCost card hithlainKnots

def glamdringReductionOk : Bool :=
  hithlainKnots.manaValue == 2 &&
    glamdringReducedCost.manaValue == 1 &&
    glamdringReducedCost.coloredCount .blue == 1 &&
    (ruling 128).comment.contains "colored mana must still be paid" &&
    (ruling 312).comment.contains "mana value of the spell remains unchanged" &&
    (ruling 311).comment.contains "mana value of the spell is determined only by its mana cost"

#guard glamdringReductionOk

/-!
## Extra triggers, Arwen enter-counters, Mox / Signet, and related comments
-/

/-- A Wolf used only to test extra-trigger rulings. -/
def testWolf : CardDef :=
  creature "Test Wolf" ManaCost.empty #["Wolf"] 1 1
    (triggeredAbilities := #[.onEnterDraw 1])

/-- Put `card` onto the battlefield through `putOntoBattlefield` so enter
replacements (Arwen) apply. -/
def enterPermanent (g : Game) (card : CardDef) (p : PlayerId) : Game :=
  let g := addToHand g card p
  let id := (handCardNamed g p card.name).id
  let (g, newId) := g.putOntoBattlefield id p (summoningSick := false)
  g.afterPermanentEnters (g.object! newId)

/-- Arwen and another creature enter as one event (same `asOf` cutoff). -/
def enterTogether (g : Game) (a b : CardDef) (p : PlayerId) : Game :=
  let g := addToHand g a p
  let g := addToHand g b p
  let idA := (handCardNamed g p a.name).id
  let idB := (handCardNamed g p b.name).id
  let asOf := g.timestamp
  let (g, newA) := g.putOntoBattlefield idA p (summoningSick := false)
    (applyHope := false)
  let (g, newB) := g.putOntoBattlefield idB p (summoningSick := false)
    (applyHope := false)
  let g := g.applyHopeEnterCounters (g.object! newA) asOf
  g.applyHopeEnterCounters (g.object! newB) asOf

def countWaiting (g : Game) (ab : TriggeredAbility) : Nat :=
  g.waitingTriggers.filter (fun wt => wt.ability == ab) |>.size

/-- Ruling 135: Bifur entering as the third storied permanent extra-triggers
his own enters-or-attacks ability. -/
def bifurEntersWithStory : Game :=
  let g := addPermanent started moxAmber ⟨0⟩ ⟨0⟩
  let g := addPermanent g arcaneSignet ⟨0⟩ ⟨0⟩
  enterPermanent g bifurMelodicRider ⟨0⟩

def bifurExtraTriggerOk : Bool :=
  (bifurEntersWithStory.player ⟨0⟩).enduringStory &&
    countWaiting bifurEntersWithStory .onEnterOrAttackPlusOneOnCreature == 2 &&
    (ruling 135).comment.contains "triggers an additional time" &&
    (ruling 97).comment.contains "doesn't copy the triggered ability" &&
    (ruling 63).comment.contains "when,\" \"whenever,\" or \"at"

#guard bifurExtraTriggerOk

/-- Without an enduring story, Bifur's ETB fires only once. -/
def bifurEntersAlone : Game := enterPermanent started bifurMelodicRider ⟨0⟩

#guard countWaiting bifurEntersAlone .onEnterOrAttackPlusOneOnCreature == 1
#guard !(bifurEntersAlone.player ⟨0⟩).enduringStory

/-- Ruling 106: Chief extras another Wolf's trigger; not a copy. -/
def chiefExtrasWolf : Game :=
  let g := addPermanent started chiefOfTheWilds ⟨0⟩ ⟨0⟩
  let g := addPermanent g testWolf ⟨0⟩ ⟨0⟩
  g.afterPermanentEnters (namedPermanent g "Test Wolf")

def chiefExtraOk : Bool :=
  countWaiting chiefExtrasWolf (.onEnterDraw 1) == 2 &&
    (ruling 106).comment.contains "doesn't copy the triggered ability"

#guard chiefExtraOk

/-- Ruling 297: two extra abilities both apply (two Chiefs, skip legend SBA). -/
def twoChiefsExtraWolf : Game :=
  let g := addPermanent started chiefOfTheWilds ⟨0⟩ ⟨0⟩
  let g := addPermanent g chiefOfTheWilds ⟨0⟩ ⟨0⟩
  let g := addPermanent g testWolf ⟨0⟩ ⟨0⟩
  g.afterPermanentEnters (namedPermanent g "Test Wolf")

def twoExtrasOk : Bool :=
  countWaiting twoChiefsExtraWolf (.onEnterDraw 1) == 3 &&
    (ruling 297).comment.contains "doesn't copy the triggered ability"

#guard twoExtrasOk

/-- Wizard's Staff extras the equipped creature's trigger. -/
def staffExtrasEquipped : Game :=
  let g := addPermanent started wizardSStaff ⟨0⟩ ⟨0⟩
  let g := addPermanent g testWolf ⟨0⟩ ⟨0⟩
  let g := g.attachSourceTo (namedPermanent g "Wizard's Staff")
    (namedPermanent g "Test Wolf")
  g.afterPermanentEnters (namedPermanent g "Test Wolf")

#guard countWaiting staffExtrasEquipped (.onEnterDraw 1) == 2

/-- Ruling 261: replacements are unaffected by the extra-trigger ability. -/
def staffDoesNotDoubleTokens : Game :=
  let g := addPermanent started wizardSStaff ⟨0⟩ ⟨0⟩
  let g := addPermanent g grizzlyBears ⟨0⟩ ⟨0⟩
  let g := g.attachSourceTo (namedPermanent g "Wizard's Staff")
    (namedPermanent g "Grizzly Bears")
  (g.createToken ⟨0⟩ Game.treasureToken).1

def staffReplacementOk : Bool :=
  (staffDoesNotDoubleTokens.battlefield.filter
      (fun o => o.name == "Treasure")).size == 1 &&
    (ruling 261).comment.contains "Replacement effects are unaffected"

#guard staffReplacementOk

/-- Ruling 133 / 308: Arwen's toughness is used as the other creature enters;
simultaneous enters get no counters. -/
def arwenThenBears : Game :=
  let g := addPermanent afterDraw arwenWeaverOfHope ⟨0⟩ ⟨0⟩
  enterPermanent g grizzlyBears ⟨0⟩

def arwenSequentialOk : Bool :=
  let bears := namedPermanent arwenThenBears "Grizzly Bears"
  bears.status.plusOnePlusOne == 1 &&
    arwenThenBears.power bears == 3 &&
    arwenThenBears.toughness bears == 3 &&
    (ruling 308).comment.contains "toughness as that creature is entering"

#guard arwenSequentialOk

def arwenSimultaneous : Game :=
  enterTogether afterDraw arwenWeaverOfHope grizzlyBears ⟨0⟩

def arwenSimultaneousOk : Bool :=
  let bears := namedPermanent arwenSimultaneous "Grizzly Bears"
  bears.status.plusOnePlusOne == 0 &&
    (ruling 133).comment.contains "won't cause that creature to enter"

#guard arwenSimultaneousOk

/-- Ruling 205 / 222 / 234: Mox Amber can activate with no (or colorless)
legendary creature/planeswalker colors and adds no mana. -/
def moxNoLegendaries : Game := addPermanent afterDraw moxAmber ⟨0⟩ ⟨0⟩

def moxEmptyOk : Bool :=
  match moxNoLegendaries.tapForMana ⟨0⟩
      (namedPermanent moxNoLegendaries "Mox Amber").id (.colored .red) with
  | .error _ => false
  | .ok g =>
    (g.player ⟨0⟩).manaPool.isEmpty &&
      (namedPermanent g "Mox Amber").status.tapped &&
      g.log.any (fun s => mentions s "adds no mana") &&
      (ruling 205).comment.contains "won't add any mana" &&
      (ruling 222).comment.contains "Colorless is not a color" &&
      (ruling 234).comment.contains "doesn't add one mana of each"

#guard moxEmptyOk

def moxWithSmaug : Game :=
  let g := addPermanent afterDraw moxAmber ⟨0⟩ ⟨0⟩
  addPermanent g smaugWickedWorm ⟨0⟩ ⟨0⟩

def moxSmaugOk : Bool :=
  let id := (namedPermanent moxWithSmaug "Mox Amber").id
  match moxWithSmaug.tapForMana ⟨0⟩ id (.colored .red) with
  | .error _ => false
  | .ok g =>
    !(g.player ⟨0⟩).manaPool.isEmpty &&
      match moxWithSmaug.tapForMana ⟨0⟩ id (.colored .white) with
      | .error _ => false
      | .ok g2 => (g2.player ⟨0⟩).manaPool.isEmpty

#guard moxSmaugOk

/-- Ruling 211 / 215 / 221: Arcane Signet uses commander color identity;
no commander or a colorless commander adds no mana, not `{C}`. -/
def signetOn (g : Game) : Game := addPermanent g arcaneSignet ⟨0⟩ ⟨0⟩

def tapSignet (g : Game) (c : Color) : Except String Game :=
  g.tapForMana ⟨0⟩ (namedPermanent g "Arcane Signet").id (.colored c)

def signetNoCommanderOk : Bool :=
  let g := signetOn afterDraw
  match tapSignet g .green with
  | .error _ => false
  | .ok g =>
    (g.player ⟨0⟩).manaPool.isEmpty &&
      (ruling 211).comment.contains "produces no mana"

#guard signetNoCommanderOk

def signetColorlessCommander : Game :=
  let g := signetOn afterDraw
  let pl := g.player ⟨0⟩
  g.setPlayer { pl with hasCommander := true, commanderColorIdentity := {} }

def signetColorlessOk : Bool :=
  match tapSignet signetColorlessCommander .green with
  | .error _ => false
  | .ok g =>
    (g.player ⟨0⟩).manaPool.isEmpty &&
      (ruling 221).comment.contains "doesn't produce {C}"

#guard signetColorlessOk

def signetTwoCommanders : Game :=
  let g := signetOn afterDraw
  let pl := g.player ⟨0⟩
  g.setPlayer { pl with
    hasCommander := true
    commanderColorIdentity := ColorSet.ofList [.green, .white] }

def signetTwoOk : Bool :=
  match tapSignet signetTwoCommanders .green, tapSignet signetTwoCommanders .blue with
  | .ok gOk, .ok gNo =>
    !(gOk.player ⟨0⟩).manaPool.isEmpty &&
      (gNo.player ⟨0⟩).manaPool.isEmpty &&
      (ruling 215).comment.contains "combined color identities"
  | _, _ => false

#guard signetTwoOk

/-- Ruling 90 / 119: mana abilities do not use the stack. -/
def banquetMana : Except String Game :=
  let g := addPermanent afterDraw bagEndBanquet ⟨0⟩ ⟨0⟩
  let (g, _) := g.createToken ⟨0⟩ Game.foodToken
  g.tapForMana ⟨0⟩ (namedPermanent g "Bag End Banquet").id .colorless

def banquetManaOk : Bool :=
  match banquetMana with
  | .error _ => false
  | .ok g =>
    g.stack.isEmpty &&
      !(g.player ⟨0⟩).manaPool.isEmpty &&
      (ruling 90).comment.contains "doesn't use the stack"

#guard banquetManaOk

/-- Ruling 119 / 120: Archdruid mana counts all Elves including itself;
the lord does not pump itself. -/
def archdruidBoard : Game :=
  let g := addPermanent afterDraw elvishArchdruid ⟨0⟩ ⟨0⟩
  addPermanent g llanowarElves ⟨0⟩ ⟨0⟩

def archdruidOk : Bool :=
  let arch := namedPermanent archdruidBoard "Elvish Archdruid"
  let elf := namedPermanent archdruidBoard "Llanowar Elves"
  archdruidBoard.power arch == 2 &&
    archdruidBoard.power elf == 2 &&
    archdruidBoard.manaFromTap arch (.colored .green) == 2 &&
    match archdruidBoard.tapForMana ⟨0⟩ arch.id (.colored .green) with
    | .error _ => false
    | .ok g =>
      g.stack.isEmpty &&
        (ruling 119).comment.contains "doesn't use the stack" &&
        (ruling 120).comment.contains "including itself"

#guard archdruidOk

/-- Ruling 94: a characteristic search may find nothing. -/
def woodElvesSkipFind : Game :=
  let g := addToLibraryTop afterDraw forest ⟨0⟩
  g.resolveSearchForest ⟨0⟩ (find := false)

def optionalSearchOk : Bool :=
  woodElvesSkipFind.log.any (fun s => mentions s "chooses not to find") &&
    (woodElvesSkipFind.player ⟨0⟩).library.any (fun id =>
      (woodElvesSkipFind.object! id).name == "Forest") &&
    (ruling 94).comment.contains "don't have to find"

#guard optionalSearchOk

/-- Ruling 36: the legendary creature must already be present. -/
def rivendellNeedsLegendOk : Bool :=
  afterDraw.entersTapped ⟨0⟩ rivendell &&
    !(addPermanent afterDraw arwenWeaverOfHope ⟨0⟩ ⟨0⟩).entersTapped ⟨0⟩
      rivendell &&
    (ruling 36).comment.contains "already be on the battlefield"

#guard rivendellNeedsLegendOk

/-- Ruling 188: illegal target means the whole spell does not resolve. -/
def knotsIllegal : Game :=
  afterDraw.applyEffect ⟨0⟩ (.tapScryDraw 1 1) #[.player ⟨1⟩]

def knotsAlreadyTapped : Game :=
  let g := addPermanent afterDraw grizzlyBears ⟨0⟩ ⟨0⟩
  let bears := namedPermanent g "Grizzly Bears"
  let g := g.setObject { bears with status := { bears.status with tapped := true } }
  g.applyEffect ⟨0⟩ (.tapScryDraw 1 1) #[.permanent (namedPermanent g "Grizzly Bears").id]

def knotsOk : Bool :=
  knotsIllegal.log.any (fun s => mentions s "doesn't resolve") &&
    (knotsIllegal.player ⟨0⟩).cardsDrawnThisTurn ==
      (afterDraw.player ⟨0⟩).cardsDrawnThisTurn &&
    (match knotsAlreadyTapped.pending with
     | .scry _ _ => true
     | _ => knotsAlreadyTapped.log.any (fun s => mentions s "scries")) &&
    (ruling 188).comment.contains "spell doesn't resolve"

#guard knotsOk

/-- Ruling 154: returning a spell works against can't-be-countered. -/
def returnUncounterable : Game :=
  let g := insertObject afterDraw giganticBigBear ⟨0⟩ .stack (some ⟨0⟩)
  let id := (g.objects.back!).id
  let g := g.putStackEntry ⟨0⟩ id
  g.returnStackSpell id

def reprieveVsUncounterableOk : Bool :=
  giganticBigBear.cantBeCountered &&
    returnUncounterable.stack.isEmpty &&
    (returnUncounterable.handObjects ⟨0⟩).any (fun o =>
      o.name == "Gigantic Big Bear") &&
    (ruling 154).comment.contains "works against a spell that can't be countered"

#guard reprieveVsUncounterableOk

/-- Ruling 149 / 159: an exiled token ceases to exist. -/
def exileTokenCeases : Game :=
  let (g, tok) := started.createToken ⟨0⟩ Game.humanSoldierToken
  let (g, _) := g.move tok.id .exile none
  g.checkSBA

def tokenExileOk : Bool :=
  !(exileTokenCeases.objects.any (fun o =>
      o.printed.isToken && o.zone == .exile)) &&
    (ruling 149).comment.contains "ceases to exist" &&
    (ruling 159).comment.contains "won't return"

#guard tokenExileOk

/-- Ruling 153 / 158: `{X}` is 0 when casting without paying the mana cost. -/
def xWithoutPayingAlsoOk : Bool :=
  xWithoutPaying == ManaCost.zero &&
    (ruling 153).comment.contains "choose 0" &&
    (ruling 158).comment.contains "choose 0"

#guard xWithoutPayingAlsoOk

/-- Ruling 104: Celeborn scries once for one or more attacking Elves. -/
def celebornScryOnceOk : Bool :=
  celebornAttackDeclared.stack.size == 1 &&
    (ruling 104).comment.contains "scry 1 just once"

#guard celebornScryOnceOk

/-- Ruling 109: Colossal Whale's attack trigger is an attacking-step trigger. -/
def whaleAttackTimingOk : Bool :=
  TriggeredAbility.firesOn .onAttackMayExileDefenderUntilLeaves .attacking &&
    (ruling 109).comment.contains "declare attackers step"

#guard whaleAttackTimingOk

/-- Ruling 115: Eagles pump only creatures you control as it resolves. -/
def eaglesPumpThenLatecomer : Game :=
  let g := addPermanent afterDraw eaglesOfTheNorth ⟨0⟩ ⟨0⟩
  let eagles := namedPermanent g "Eagles of the North"
  let g := g.putMatchingSourceTriggers ⟨0⟩ eagles .entering
  let g := g.receivePriority ⟨0⟩
  let g := g.resolveTop
  addPermanent g grizzlyBears ⟨0⟩ ⟨0⟩

def eaglesPumpOk : Bool :=
  let eagles := namedPermanent eaglesPumpThenLatecomer "Eagles of the North"
  let late := namedPermanent eaglesPumpThenLatecomer "Grizzly Bears"
  eaglesPumpThenLatecomer.power eagles == 4 &&
    eaglesPumpThenLatecomer.power late == 2 &&
    (ruling 115).comment.contains "at the time it resolves"

#guard eaglesPumpOk

/-- Ruling 93 / 116: Mirkwood Meditator base-PT change; damage can become lethal. -/
def meditatorDamageThenShrink : Game :=
  let g := addPermanent afterDraw mirkwoodMeditator ⟨0⟩ ⟨0⟩
  let m := namedPermanent g "Mirkwood Meditator"
  let g := g.setObject { m with status := { m.status with damage := 3 } }
  let m := namedPermanent g "Mirkwood Meditator"
  g.setObject { m with status := { m.status with
    damage := 3, setBasePT := some (4, 2) } }

def meditatorBaseOk : Bool :=
  let m := namedPermanent meditatorDamageThenShrink "Mirkwood Meditator"
  meditatorDamageThenShrink.toughness m == 2 &&
    m.status.damage == 3 &&
    (ruling 93).comment.contains "may become lethal" &&
    (ruling 116).comment.contains "new base power and toughness"

#guard meditatorBaseOk

/-- Ruling 232: Mentor checks power only as the other creature enters. -/
def mentorSeesEnterPowerOk : Bool :=
  amassMentorSeesZeroOk &&
    (ruling 232).comment.contains "only as it enters"

#guard mentorSeesEnterPowerOk

/-- Ruling 55 / 59 / 262: Settle the Wreckage targets a player; tokens count. -/
def settleExilesAttackers : Game :=
  let g := addPermanent afterDraw grizzlyBears ⟨1⟩ ⟨1⟩
  let (g, tok) := g.createToken ⟨1⟩ Game.humanSoldierToken
  let g := g.mapObjectStatus (namedPermanent g "Grizzly Bears")
    (fun s => { s with attacking := true })
  let g := g.mapObjectStatus (g.object! tok.id)
    (fun s => { s with attacking := true })
  g.applyEffect ⟨0⟩ .exileAttackersSearchBasics #[.player ⟨1⟩]

def settleOk : Bool :=
  settleTheWreckage.spellEffect == some .exileAttackersSearchBasics &&
    settleExilesAttackers.log.any (fun s => mentions s "may search for 2") &&
    !(settleExilesAttackers.battlefield.any (·.status.attacking)) &&
    (ruling 55).comment.contains "find fewer basic land cards" &&
    (ruling 59).comment.contains "tokens" &&
    (ruling 262).comment.contains "targets only the player"

#guard settleOk

/-- Ruling 192: apply cost increases before reductions. -/
def sevenElvesAndKeepers : Game :=
  (List.range 5).foldl (init := twoElvesAndKeepers) fun g _ =>
    addPermanent g llanowarElves ⟨0⟩ ⟨0⟩

def increasesBeforeReductionsOk : Bool :=
  let card := handCardNamed sevenElvesAndKeepers ⟨0⟩ "Cantankerous Keepers"
  let kicked :=
    sevenElvesAndKeepers.playManaCost card cantankerousKeepers
      (ManaCost.ofGeneric 2)
  kicked.coloredCount .green == 1 &&
    kicked.manaValue == 1 &&
    (ruling 192).comment.contains "increases before applying cost reductions"

#guard increasesBeforeReductionsOk

/-- Ruling 195 / 198: without paying the mana cost you still pay additional
costs such as kicker. -/
def withoutPayingStillPaysKickerOk : Bool :=
  let g := addToHand afterDraw insideInformation ⟨0⟩
  let card := handCardNamed g ⟨0⟩ "Inside Information"
  let card := { card with playPermission := some {
    player := ⟨0⟩, turnEndsRemaining := 1, withoutManaCost := true } }
  let cost := g.playManaCost card insideInformation (ManaCost.ofGeneric 2)
  cost.manaValue == 2 && cost.colors.isColorless &&
    improvisedClub.additionalCostSacrificeArtifactOrCreature &&
    (ruling 195).comment.contains "mandatory additional costs" &&
    (ruling 198).comment.contains "must be paid"

#guard withoutPayingStillPaysKickerOk

/-- Ruling 148: counters and continuous effects apply when Mentor checks power. -/
def mentorSeesArwenCounters : Game :=
  let g := addPermanent afterDraw mentorOfTheMeek ⟨0⟩ ⟨0⟩
  let g := addPermanent g arwenWeaverOfHope ⟨0⟩ ⟨0⟩
  enterPermanent g grizzlyBears ⟨0⟩

def mentorArwenOk : Bool :=
  let bears := namedPermanent mentorSeesArwenCounters "Grizzly Bears"
  bears.status.plusOnePlusOne == 1 &&
    mentorSeesArwenCounters.power bears == 3 &&
    countWaiting mentorSeesArwenCounters
      (.onAnotherCreatureYouControlPowerAtMostEntersMayPayDraw 2 1) == 0 &&
    (ruling 148).comment.contains "those effects apply when checking"

#guard mentorArwenOk

/-- Ruling 145: `{X}` is 0 when a card is in a graveyard. -/
def xInGraveyardIsZeroOk : Bool :=
  insideInformation.manaValue == 2 &&
    (ruling 145).comment.contains "X is 0"

#guard xInGraveyardIsZeroOk

/-- Ruling 85: Mithril Coat's enters attachment is not an equip activation. -/
def mithrilEtbAttachOk : Bool :=
  mithrilCoat.triggeredAbilities == #[.onEnterAttachToLegendary] &&
    mithrilCoat.activatedAbilities.any (fun ab =>
      ab.cost.mana == ManaCost.ofGeneric 3) &&
    (ruling 85).comment.contains "isn't the same as using its equip ability"

#guard mithrilEtbAttachOk

/-- Ruling 131: Guttersnipe triggers when the instant is cast, before it resolves. -/
def guttersnipeBeforeSpell : Game :=
  let g := addPermanent afterDraw guttersnipe ⟨0⟩ ⟨0⟩
  let g := addToHand g shock ⟨0⟩
  g.putCastTriggersOnStack ⟨0⟩ (handCardNamed g ⟨0⟩ "Shock")

def guttersnipeBeforeSpellOk : Bool :=
  countWaiting guttersnipeBeforeSpell
      (.onCastInstantOrSorceryDealDamageToEachOpponent 2) == 1 &&
    (ruling 131).comment.contains "resolves before the spell"

#guard guttersnipeBeforeSpellOk

/-- Ruling 105: Celeborn's pump uses cards actually looked at. -/
def celebornLookedAtOk : Bool :=
  (celebornScried.object! celebornScried.stack.back!.objectId).lastKnownPower ==
      some 1 &&
    (ruling 105).comment.contains "cards you actually looked at"

#guard celebornLookedAtOk

/-- Ruling 108: Colossal Whale uses one ability that both exiles and returns. -/
def whaleLinkedOk : Bool :=
  colossalWhale.triggeredAbilities == #[.onAttackMayExileDefenderUntilLeaves] &&
    (ruling 108).comment.contains "single ability that creates two one-shot effects"

#guard whaleLinkedOk

/-- Ruling 114: each cascade instance is a separate trigger. -/
def twoCascadesOk : Bool :=
  callForthTheTempest.cascade == 2 &&
    (ruling 114).comment.contains "Each instance of cascade triggers"

#guard twoCascadesOk

/-- Ruling 41 / 17 / 28: already-modeled amass errata, illegal-target amass, and
Storied not using the stack. -/
def sharedKeywordCommentsOk : Bool :=
  (ruling 41).comment.contains "amass Zombies N" &&
    (ruling 17).comment.contains "won't amass" &&
    (ruling 28).comment.contains "doesn't use the stack" &&
    (ruling 95).comment.contains "additional costs" &&
    (ruling 196).comment.contains "additional costs" &&
    (ruling 197).comment.contains "additional costs"

#guard sharedKeywordCommentsOk

/-- Ruling 64: an exiled land still follows land-play timing. -/
def exiledLandTimingOk : Bool :=
  afterDraw.canPlayLand ⟨0⟩ &&
    !afterDraw.canPlayLand ⟨1⟩ &&
    (ruling 64).comment.contains "only during your main phase"

#guard exiledLandTimingOk

/-- Ruling 10: a copy of an adventurer object has an Adventure; a token copy
that leaves the battlefield ceases to exist. -/
def adventureCopyHasAdventureOk : Bool :=
  let printed := { bilboLuckwearer with isToken := true }
  let (g, tok) := started.createToken ⟨0⟩ printed
  let hasAdv := tok.printed.adventure.isSome
  let (g, _) := g.move tok.id (.graveyard ⟨0⟩) none
  let g := g.checkSBA
  hasAdv &&
    !g.objects.any (fun o => o.name == "Bilbo, Luckwearer") &&
    (ruling 10).comment.contains "the copy also has an Adventure"

#guard adventureCopyHasAdventureOk

/-- Ruling 75: activating a creature mana ability triggers Elrond. -/
def elrondManaAbility : Except String Game :=
  let g := addPermanent afterDraw elrondMoonReader ⟨0⟩ ⟨0⟩
  let g := addPermanent g llanowarElves ⟨0⟩ ⟨0⟩
  g.tapForMana ⟨0⟩ (namedPermanent g "Llanowar Elves").id (.colored .green)

def elrondManaAbilityOk : Bool :=
  match elrondManaAbility with
  | .error _ => false
  | .ok g =>
    countWaiting g .onActivateCreatureAbilityDrawOnce == 1 &&
      (ruling 75).comment.contains "mana ability"

#guard elrondManaAbilityOk

/-- Ruling 86: Great Gilded Boat triggers when you attack, even if it is not
among the attackers. -/
def boatRecruitOnAttack : Game :=
  let g := addPermanent afterDraw greatGildedBoat ⟨0⟩ ⟨0⟩
  let g := addPermanent g grizzlyBears ⟨0⟩ ⟨0⟩
  g.putControlledTriggers ⟨0⟩ .youAttack

def boatRecruitOnAttackOk : Bool :=
  countWaiting boatRecruitOnAttack .onYouAttackRecruit == 1 &&
    greatGildedBoat.triggeredAbilities == #[.onYouAttackRecruit] &&
    (ruling 86).comment.contains "doesn't have to be among them"

#guard boatRecruitOnAttackOk

/-- Ruling 96: Belladonna's fourth resolve in a turn does nothing. -/
def belladonnaFourResolves : Game :=
  let g := addPermanent afterDraw belladonnaTook ⟨0⟩ ⟨0⟩
  let src := some (namedPermanent g "Belladonna Took").id
  let g := g.applyTriggeredAbility ⟨0⟩ .onTokenYouControlEntersBelladonna src
  let g := g.applyTriggeredAbility ⟨0⟩ .onTokenYouControlEntersBelladonna src
  let g := g.applyTriggeredAbility ⟨0⟩ .onTokenYouControlEntersBelladonna src
  g.applyTriggeredAbility ⟨0⟩ .onTokenYouControlEntersBelladonna src

def belladonnaFourResolvesOk : Bool :=
  let g := belladonnaFourResolves
  (g.player ⟨0⟩).life == 21 &&
    (g.player ⟨0⟩).hand.size == (afterDraw.player ⟨0⟩).hand.size + 1 &&
    (namedPermanent g "Belladonna Took").status.plusOnePlusOne == 1 &&
    (g.player ⟨0⟩).belladonnaResolvesThisTurn == 4 &&
    g.log.any (fun s => mentions s "no effect") &&
    (ruling 96).comment.contains "no effect each time beyond the third"

#guard belladonnaFourResolvesOk

/-- Ruling 96: a token entering actually queues the ability. -/
def belladonnaSeesToken : Game :=
  let g := addPermanent afterDraw belladonnaTook ⟨0⟩ ⟨0⟩
  let (g, tok) := g.createToken ⟨0⟩ Game.humanSoldierToken
  g.afterPermanentEnters (g.object! tok.id)

#guard countWaiting belladonnaSeesToken .onTokenYouControlEntersBelladonna == 1

/-- Ruling 100: mill and discard still go to the graveyard. -/
def headDoesNotExileMill : Game :=
  let g := addPermanent afterDraw headOfTheHunt ⟨0⟩ ⟨0⟩
  let g := addToHand g shock ⟨1⟩
  let id := (handCardNamed g ⟨1⟩ "Shock").id
  (g.move id (.graveyard ⟨1⟩) none).1

def headDoesNotExileMillOk : Bool :=
  headDoesNotExileMill.objects.any (fun o =>
    o.name == "Shock" && o.zone == .graveyard ⟨1⟩) &&
    !(headDoesNotExileMill.objects.any (fun o =>
      o.name == "Shock" && o.zone == .exile)) &&
    (ruling 100).comment.contains "will not be exiled instead"

#guard headDoesNotExileMillOk

/-- Ruling 100 / 140: an opposing creature that would die is exiled instead,
and a simultaneous death of Head of the Hunt still exiles it. -/
def headExilesInstead : Game :=
  let g := addPermanent afterDraw headOfTheHunt ⟨0⟩ ⟨0⟩
  let g := addPermanent g grizzlyBears ⟨1⟩ ⟨1⟩
  let bears := namedPermanent g "Grizzly Bears"
  (g.move bears.id (.graveyard ⟨1⟩) none).1

def headExilesInsteadOk : Bool :=
  headExilesInstead.objects.any (fun o =>
    o.name == "Grizzly Bears" && o.zone == .exile) &&
    headExilesInstead.battlefield.any (fun o => o.name == "Wolf") &&
    (ruling 100).comment.contains "discarded or milled"

#guard headExilesInsteadOk

def headDiesWithPrey : Game :=
  let g := addPermanent afterDraw headOfTheHunt ⟨0⟩ ⟨0⟩
  let g := addPermanent g grizzlyBears ⟨1⟩ ⟨1⟩
  let head := namedPermanent g "Head of the Hunt"
  let bears := namedPermanent g "Grizzly Bears"
  let g := g.setObject { head with status := { head.status with damage := 10 } }
  let g := g.setObject { bears with status := { bears.status with damage := 10 } }
  g.checkSBA

def headDiesWithPreyOk : Bool :=
  headDiesWithPrey.objects.any (fun o =>
    o.name == "Grizzly Bears" && o.zone == .exile) &&
    headDiesWithPrey.objects.any (fun o =>
      o.name == "Head of the Hunt" &&
        match o.zone with
        | .graveyard _ => true
        | _ => false) &&
    (ruling 140).comment.contains "still be exiled"

#guard headDiesWithPreyOk

/-- Ruling 80: Ori counts destroyed permanents even if they are exiled. -/
def oriCountsExiled : Game :=
  let g := addPermanent afterDraw oriPlateStacker ⟨0⟩ ⟨0⟩
  let g := addPermanent g dwarvenShortsword ⟨1⟩ ⟨1⟩
  let sw := namedPermanent g "Dwarven Shortsword"
  let g := g.setObject { sw with status := { sw.status with
    untilEotExileIfDies := true } }
  g.applyTriggeredAbility ⟨0⟩ .onEnterDestroyOppArtifactsEnchantmentsGainLife
    (some (namedPermanent g "Ori, Plate Stacker").id)

def oriCountsExiledOk : Bool :=
  (oriCountsExiled.player ⟨0⟩).life == 21 &&
    oriCountsExiled.objects.any (fun o =>
      o.name == "Dwarven Shortsword" && o.zone == .exile) &&
    (ruling 80).comment.contains "zone other than a graveyard"

#guard oriCountsExiledOk

/-- Ruling 139: Great Fierce Bee still triggers if it dies with other creatures. -/
def beeDiesWithOthers : Game :=
  let g := addPermanent afterDraw greatFierceBee ⟨0⟩ ⟨0⟩
  let g := addPermanent g grizzlyBears ⟨0⟩ ⟨0⟩
  let bee := namedPermanent g "Great Fierce Bee"
  let bears := namedPermanent g "Grizzly Bears"
  let g := g.setObject { bee with status := { bee.status with damage := 20 } }
  let g := g.setObject { bears with status := { bears.status with damage := 10 } }
  g.checkSBA

def beeDiesWithOthersOk : Bool :=
  countWaiting beeDiesWithOthers (.onOneOrMoreOtherCreaturesDieScry 1) == 1 &&
    (ruling 139).comment.contains "dies at the same time"

#guard beeDiesWithOthersOk

/-- Ruling 141: an untapped Minas Tirith Garrison may tap itself. -/
def garrisonTapsSelf : Except String Game :=
  let g := addPermanent afterDraw minasTirithGarrison ⟨0⟩ ⟨0⟩
  let g := { g with pending := .tapHumans ⟨0⟩ }
  g.choosePermanents ⟨0⟩ #[(namedPermanent g "Minas Tirith Garrison").id]

def garrisonTapsSelfOk : Bool :=
  match garrisonTapsSelf with
  | .error _ => false
  | .ok g =>
    (namedPermanent g "Minas Tirith Garrison").status.tapped &&
      (g.player ⟨0⟩).hand.size == (afterDraw.player ⟨0⟩).hand.size + 1 &&
      (ruling 141).comment.contains "tapped for its own last ability"

#guard garrisonTapsSelfOk

/-- Ruling 142: Smite's extra effects apply even if no damage is marked. -/
def smiteZeroDamage : Game :=
  let g := addPermanent afterDraw grizzlyBears ⟨1⟩ ⟨1⟩
  g.dealDamageLoseIndestructibleExileTo (namedPermanent g "Grizzly Bears") 0

def smiteZeroDamageOk : Bool :=
  let b := namedPermanent smiteZeroDamage "Grizzly Bears"
  b.status.untilEotLosesIndestructible &&
    b.status.untilEotExileIfDies &&
    b.status.damage == 0 &&
    (ruling 142).comment.contains "additional effects will still apply"

#guard smiteZeroDamageOk

/-- Ruling 149 / 159–162: an exiled token ceases to exist and does not return. -/
def exiledTokenCeases : Game :=
  let (g, tok) := afterDraw.createToken ⟨0⟩ Game.humanSoldierToken
  let (g, _) := g.move tok.id .exile none
  g.checkSBA

def exiledTokenCeasesOk : Bool :=
  !exiledTokenCeases.objects.any (fun o => o.name == "Human Soldier") &&
    (ruling 149).comment.contains "ceases to exist" &&
    ((ruling 159).comment.contains "won't return" ||
      (ruling 159).comment.contains "won't be returned") &&
    ((ruling 160).comment.contains "won't return" ||
      (ruling 160).comment.contains "won’t return") &&
    (ruling 161).comment.contains "won't return" &&
    (ruling 162).comment.contains "won't be returned"

#guard exiledTokenCeasesOk

/-- Ruling 151 / 126 / 256: protection from everything blocks targeting and
preventable damage, but not unpreventable damage. -/
def withProtection : Game :=
  afterDraw.modifyPlayer ⟨1⟩ (fun pl => { pl with protectionFromEverything := true })

def protectionFromEverythingOk : Bool :=
  let ts := withProtection.legalTargets ⟨0⟩ (.dealDamage 3)
  !ts.any (fun t => t == Target.player ⟨1⟩) &&
    (let g := withProtection.dealDamageToPlayer ⟨1⟩ 5
     (g.player ⟨1⟩).life == 20 &&
       g.log.any (fun s => mentions s "prevented")) &&
    (let g := withProtection.dealDamageToPlayer ⟨1⟩ 5 (preventable := false)
     (g.player ⟨1⟩).life == 15) &&
    (ruling 151).comment.contains "can't be the target" &&
    (ruling 126).comment.contains "illegal target" &&
    (ruling 256).comment.contains "can't be prevented"

#guard protectionFromEverythingOk

/-- Ruling 167: tapping an attacking Human for Garrison leaves it attacking. -/
def garrisonTapAttackerOk : Bool :=
  let g := addPermanent afterDraw minasTirithGarrison ⟨0⟩ ⟨0⟩
  let g := addPermanent g grizzlyBears ⟨0⟩ ⟨0⟩
  let human :=
    creature "Townsfolk" (ManaCost.ofGeneric 1) #["Human"] 1 1
  let g := addPermanent g human ⟨0⟩ ⟨0⟩
  let h := namedPermanent g "Townsfolk"
  let g := g.setObject { h with status := { h.status with attacking := true } }
  let g := { g with pending := .tapHumans ⟨0⟩ }
  match g.choosePermanents ⟨0⟩ #[(namedPermanent g "Townsfolk").id] with
  | .error _ => false
  | .ok g =>
    (namedPermanent g "Townsfolk").status.tapped &&
      (namedPermanent g "Townsfolk").status.attacking &&
      (ruling 167).comment.contains "remains an attacking creature"

#guard garrisonTapAttackerOk

/-- Ruling 170: Elven Chorus is not an Elf card. -/
def elvenChorusNotElfOk : Bool :=
  !elvenChorus.hasSubtype "Elf" &&
    !elvenChorus.isCreature &&
    (ruling 170).comment.contains "Elven Chorus is not an Elf"

#guard elvenChorusNotElfOk

/-- Ruling 206: if Executioner is your only creature, you sacrifice it. -/
def executionerSacrificesSelf : Game :=
  let g := addPermanent afterDraw mercilessExecutioner ⟨0⟩ ⟨0⟩
  let g := g.applyTriggeredAbility ⟨0⟩ .onEnterEachPlayerSacrificesCreature
    (some (namedPermanent g "Merciless Executioner").id)
  mustApply g ⟨0⟩ (.sacrifice (namedPermanent g "Merciless Executioner").id)

def executionerSacrificesSelfOk : Bool :=
  !executionerSacrificesSelf.battlefield.any (fun o =>
      o.name == "Merciless Executioner") &&
    (ruling 206).comment.contains "sacrifice Merciless Executioner"

#guard executionerSacrificesSelfOk

end Mtg.Engine.RulingTests
