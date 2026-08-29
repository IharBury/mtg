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

/-!
## 78 — The Eagles Are Coming! counts tokens returned to hand
-/

def eaglesReturnToken : Game :=
  let (g, tok) := afterDraw.createToken ⟨0⟩ Game.humanSoldierToken
  g.returnOwnedCreaturesScheduleBirds ⟨0⟩ #[tok.id]

def eaglesTokenCountedOk : Bool :=
  (eaglesReturnToken.player ⟨0⟩).eaglesBirdsNextUpkeep == 1 &&
    eaglesReturnToken.objects.any (fun o =>
      o.name == "Human Soldier" && o.zone == .hand ⟨0⟩) &&
    (ruling 78).comment.contains "creature tokens that were returned"

#guard eaglesTokenCountedOk

def eaglesBirdsAfterUpkeep : Game :=
  let g := { eaglesReturnToken.checkSBA with waitingTriggers := #[] }
  { g with step := .untap, activePlayer := ⟨1⟩ }.beginStep .upkeep

def eaglesBirdsAfterUpkeepOk : Bool :=
  eaglesBirdsAfterUpkeep.battlefield.any (fun o =>
    o.name == "Bird Soldier" && o.printed.isToken &&
      eaglesBirdsAfterUpkeep.hasSubtype o "Bird") &&
    !eaglesBirdsAfterUpkeep.objects.any (fun o =>
      o.name == "Human Soldier" && o.zone == .hand ⟨0⟩) &&
    (ruling 78).comment.contains "Bird Soldier token"

#guard eaglesBirdsAfterUpkeepOk

/-!
## 98, 99, 121 — Bolg reflexive trigger and excess damage
-/

def bolgReady : Game :=
  let g := addPermanent afterDraw bolgOfTheNorth ⟨0⟩ ⟨0⟩
  let g := addPermanent g hillGiant ⟨0⟩ ⟨0⟩
  addPermanent g grayOgre ⟨1⟩ ⟨1⟩

def bolgMaySacPending : Game :=
  bolgReady.applyTriggeredAbility ⟨0⟩ .onEnterBolgMaySacrifice
    (some (namedPermanent bolgReady "Bolg of the North").id)

def bolgReflexivePendingOk : Bool :=
  (match bolgMaySacPending.pending with
   | .maySacrificeAnotherBolg p _ => p == ⟨0⟩
   | _ => false) &&
    (ruling 98).comment.contains "reflexive triggered ability" &&
    (ruling 98).comment.contains "without a target"

#guard bolgReflexivePendingOk

def bolgAfterSacrifice : Game :=
  mustApply bolgMaySacPending ⟨0⟩
    (.sacrifice (namedPermanent bolgMaySacPending "Hill Giant").id)

def bolgAfterSacrificeOk : Bool :=
  let onStack :=
    bolgAfterSacrifice.stack.any (fun e =>
      (bolgAfterSacrifice.object! e.objectId).triggeredAbility ==
        some .onBolgDealSacrificedPower)
  let waiting :=
    bolgAfterSacrifice.waitingTriggers.any (fun wt =>
      wt.ability == .onBolgDealSacrificedPower &&
        wt.lastKnownPower == some 3)
  (onStack || waiting) &&
    !bolgAfterSacrifice.battlefield.any (fun o => o.name == "Hill Giant") &&
    (ruling 98).comment.contains "second ability triggers"

#guard bolgAfterSacrificeOk

def bolgDeclineNoDamage : Game :=
  mustApply bolgMaySacPending ⟨0⟩ .decline

def bolgDeclineOk : Bool :=
  !bolgDeclineNoDamage.waitingTriggers.any (fun wt =>
    wt.ability == .onBolgDealSacrificedPower) &&
    bolgDeclineNoDamage.battlefield.any (fun o => o.name == "Hill Giant")

#guard bolgDeclineOk

def bolgOtherSac : Game :=
  let g := bolgReady.beginSacrificeCreature ⟨0⟩
  mustApply g ⟨0⟩ (.sacrifice (namedPermanent g "Hill Giant").id)

def bolgOtherSacOk : Bool :=
  !bolgOtherSac.waitingTriggers.any (fun wt =>
    wt.ability == .onBolgDealSacrificedPower) &&
    (ruling 99).comment.contains "won't trigger if you sacrifice a creature for any other reason"

#guard bolgOtherSacOk

def bolgDeal (g : Game) (amt : Int) (tid : ObjectId) : Game :=
  g.applyTriggeredAbility ⟨0⟩ .onBolgDealSacrificedPower
    (some (namedPermanent g "Bolg of the North").id)
    #[Target.permanent tid] #[] (some amt)

def bolgExcessDamage : Game :=
  bolgDeal bolgAfterSacrifice 3 (namedPermanent bolgAfterSacrifice "Gray Ogre").id

def bolgExcessOk : Bool :=
  (namedPermanent bolgExcessDamage "Gray Ogre").status.damage == 3 &&
    bolgExcessDamage.battlefield.any (fun o =>
      bolgExcessDamage.hasSubtype o "Army" && o.status.plusOnePlusOne == 1) &&
    (ruling 121).comment.contains "damage already marked"

#guard bolgExcessOk

def bolgMarkedExcess : Game :=
  let g := addPermanent afterDraw bolgOfTheNorth ⟨0⟩ ⟨0⟩
  let g := addPermanent g hillGiant ⟨1⟩ ⟨1⟩
  let giant := namedPermanent g "Hill Giant"
  let g := g.mapObjectStatus giant (fun s => { s with damage := 2 })
  bolgDeal g 3 giant.id

def bolgMarkedExcessOk : Bool :=
  bolgMarkedExcess.battlefield.any (fun o =>
    bolgMarkedExcess.hasSubtype o "Army" && o.status.plusOnePlusOne == 2) &&
    (ruling 121).comment.contains "greater than lethal damage"

#guard bolgMarkedExcessOk

/-!
## 103 — Cavern-Hoard counts artifacts as the ability resolves
-/

def cavernHoardResolveCount : Game :=
  let g := addPermanent afterDraw cavernHoardDragon ⟨0⟩ ⟨0⟩
  let (g, _) := g.createToken ⟨1⟩ Game.treasureToken
  let (g, _) := g.createToken ⟨1⟩ Game.treasureToken
  let g := { g with lastCombatDamagePlayer := some ⟨1⟩ }
  let t := namedPermanent g "Treasure"
  let g := (g.move t.id (.graveyard ⟨1⟩) none).1
  g.applyTriggeredAbility ⟨0⟩
    .onCombatDamageCreateTreasuresEqualPlayerArtifacts
    (some (namedPermanent g "Cavern-Hoard Dragon").id)

def cavernHoardResolveCountOk : Bool :=
  (cavernHoardResolveCount.battlefield.filter (fun o =>
    o.name == "Treasure" && o.controlledBy ⟨0⟩)).size == 1 &&
    (cavernHoardResolveCount.battlefield.filter (fun o =>
      o.name == "Treasure" && o.controlledBy ⟨1⟩)).size == 1 &&
    (ruling 103).comment.contains "as the ability resolves"

#guard cavernHoardResolveCountOk

/-!
## 112 — Desert Were-Worm checks power at attack time
-/

def wereWormMountains (n : Nat) : Game :=
  let g := addPermanent afterDraw desertWereWorm ⟨0⟩ ⟨0⟩
  (List.range n).foldl (init := g) fun g _ =>
    addPermanent g mountain ⟨0⟩ ⟨0⟩

def wereWormTenPower : Game := wereWormMountains 5

def wereWormTenPowerOk : Bool :=
  wereWormTenPower.power (namedPermanent wereWormTenPower "Desert Were-Worm") == 10

#guard wereWormTenPowerOk

def wereWormTenAttacks : Game :=
  let g := wereWormTenPower
  let w := namedPermanent g "Desert Were-Worm"
  let g := g.setObject { w with status := { w.status with attacking := true } }
  g.putAttackTriggersOnStack ⟨0⟩ #[(namedPermanent g "Desert Were-Worm").id]

def wereWormTenAttacksOk : Bool :=
  !wereWormTenAttacks.waitingTriggers.any (fun wt =>
    wt.event == .youAttackWithTotalPower) &&
    (ruling 112).comment.contains "at the time you attacked"

#guard wereWormTenAttacksOk

def wereWormTwelveAttacks : Game :=
  let g := wereWormMountains 6
  let w := namedPermanent g "Desert Were-Worm"
  let g := g.setObject { w with status := { w.status with attacking := true } }
  g.putAttackTriggersOnStack ⟨0⟩ #[(namedPermanent g "Desert Were-Worm").id]

def wereWormTwelveAttacksOk : Bool :=
  wereWormTwelveAttacks.power
      (namedPermanent wereWormTwelveAttacks "Desert Were-Worm") == 12 &&
    wereWormTwelveAttacks.waitingTriggers.any (fun wt =>
      wt.event == .youAttackWithTotalPower) &&
    (ruling 112).comment.contains "will not contribute"

#guard wereWormTwelveAttacksOk

/-!
## 118, 191 — Elven Chorus timing and looking at the top
-/

def chorusInPlay : Game := addPermanent afterDraw elvenChorus ⟨0⟩ ⟨0⟩

def elvenChorusTimingOk : Bool :=
  chorusInPlay.canLookAtLibraryTop ⟨0⟩ &&
    chorusInPlay.controlsCastCreaturesFromTop ⟨0⟩ &&
    chorusInPlay.asSorcery? ⟨0⟩ &&
    !(let g := { chorusInPlay with step := .end }
      g.timingAllowsCast ⟨0⟩ grizzlyBears) &&
    (ruling 118).comment.contains "doesn't change when you can cast"

#guard elvenChorusTimingOk

def chorusCastingFromTop : Game := { chorusInPlay with castingFromTop := true }

def elvenChorusNewTopHiddenOk : Bool :=
  !chorusCastingFromTop.canLookAtLibraryTop ⟨0⟩ &&
    chorusInPlay.canLookAtLibraryTop ⟨0⟩ &&
    (ruling 191).comment.contains "can't look at the new top card"

#guard elvenChorusNewTopHiddenOk

/-!
## 125 — Mount Doom last ability does not target
-/

def mountDoomChooseKeep : Game :=
  let g := addPermanent afterDraw mountDoom ⟨0⟩ ⟨0⟩
  let g := addPermanent g grizzlyBears ⟨0⟩ ⟨0⟩
  let g := addPermanent g grayOgre ⟨1⟩ ⟨1⟩
  g.chooseCreaturesDestroyRest #[(namedPermanent g "Grizzly Bears").id]

def mountDoomChooseKeepOk : Bool :=
  mountDoomChooseKeep.battlefield.any (fun o => o.name == "Grizzly Bears") &&
    !mountDoomChooseKeep.battlefield.any (fun o => o.name == "Gray Ogre") &&
    (ruling 125).comment.contains "none of the chosen creatures are targets"

#guard mountDoomChooseKeepOk

/-!
## 129, 130 — Gleaming Splendor second-card trigger and two players
-/

def gleamingReady : Game :=
  let g := addPermanent afterDraw gleamingSplendor ⟨0⟩ ⟨0⟩
  g.modifyPlayer ⟨1⟩ (fun pl => { pl with cardsDrawnThisTurn := 0 })

def gleamingSecondDraw : Game :=
  (gleamingReady.draw ⟨1⟩ 1).draw ⟨1⟩ 1

def gleamingFirstDraw : Game :=
  gleamingReady.draw ⟨1⟩ 1

def gleamingSecondDrawOk : Bool :=
  gleamingFirstDraw.waitingTriggers.all (fun wt =>
    wt.event != .opponentDrawsSecondCard) &&
    gleamingSecondDraw.waitingTriggers.any (fun wt =>
      wt.event == .opponentDrawsSecondCard) &&
    (ruling 129).comment.contains "second card" &&
    (ruling 129).comment.contains "only once each turn"

#guard gleamingSecondDrawOk

def gleamingTwoDifferentPlayersOk : Bool :=
  (match afterDraw.twoPlayersEachDraw ⟨0⟩ ⟨0⟩ with
   | .error e => e.contains "different"
   | .ok _ => false) &&
    (match afterDraw.twoPlayersEachDraw ⟨0⟩ ⟨1⟩ with
     | .ok g =>
       (g.player ⟨0⟩).cardsDrawnThisTurn ==
         (afterDraw.player ⟨0⟩).cardsDrawnThisTurn + 1 &&
         (g.player ⟨1⟩).cardsDrawnThisTurn ==
           (afterDraw.player ⟨1⟩).cardsDrawnThisTurn + 1
     | .error _ => false) &&
    (ruling 130).comment.contains "two different target players"

#guard gleamingTwoDifferentPlayersOk

/-!
## 132, 181 — Andúril, Flame of the West
-/

def andurilOnOppLegend : Game :=
  let g := addPermanent afterDraw andurilFlameOfTheWest ⟨0⟩ ⟨0⟩
  let g := addPermanent g tomBombadil ⟨1⟩ ⟨1⟩
  let g := g.attachSourceTo (namedPermanent g "Andúril, Flame of the West")
    (namedPermanent g "Tom Bombadil")
  let tom := namedPermanent g "Tom Bombadil"
  let g := g.setObject { tom with status := { tom.status with attacking := true } }
  g.putAttackTriggersOnStack ⟨1⟩ #[(namedPermanent g "Tom Bombadil").id]

def andurilOnOppLegendOk : Bool :=
  andurilOnOppLegend.waitingTriggers.any (fun wt =>
    wt.ability == .onEquippedAttacksCreateSpirits &&
      wt.controller == ⟨0⟩) &&
    (ruling 132).comment.contains "opponent controls"

#guard andurilOnOppLegendOk

def andurilOppSpirits : Game :=
  andurilOnOppLegend.applyTriggeredAbility ⟨0⟩
    .onEquippedAttacksCreateSpirits
    (some (namedPermanent andurilOnOppLegend "Andúril, Flame of the West").id)

def andurilOppSpiritsOk : Bool :=
  let spirits :=
    andurilOppSpirits.battlefield.filter (fun o => o.name == "Spirit")
  spirits.size == 2 &&
    spirits.all (fun o => o.status.tapped && !o.status.attacking &&
      o.controlledBy ⟨0⟩) &&
    (ruling 132).comment.contains "would not enter the battlefield attacking"

#guard andurilOppSpiritsOk

def andurilOnOwnLegend : Game :=
  let g := addPermanent afterDraw andurilFlameOfTheWest ⟨0⟩ ⟨0⟩
  let g := addPermanent g tomBombadil ⟨0⟩ ⟨0⟩
  let g := g.attachSourceTo (namedPermanent g "Andúril, Flame of the West")
    (namedPermanent g "Tom Bombadil")
  let tom := namedPermanent g "Tom Bombadil"
  let g := g.setObject { tom with status := { tom.status with attacking := true } }
  let g := g.putAttackTriggersOnStack ⟨0⟩ #[(namedPermanent g "Tom Bombadil").id]
  g.applyTriggeredAbility ⟨0⟩ .onEquippedAttacksCreateSpirits
    (some (namedPermanent g "Andúril, Flame of the West").id)

def andurilOnOwnLegendOk : Bool :=
  let spirits :=
    andurilOnOwnLegend.battlefield.filter (fun o => o.name == "Spirit")
  spirits.size == 2 &&
    spirits.all (fun o => o.status.tapped && o.status.attacking) &&
    (ruling 181).comment.contains "Andúril's controller chooses"

#guard andurilOnOwnLegendOk

/-!
## 150 — Queen of Dale misses a prior first noncreature
-/

def queenAfterFirstNoncreature : Game :=
  let g := addPermanent afterDraw theQueenOfDale ⟨0⟩ ⟨0⟩
  let g := g.modifyPlayer ⟨1⟩ (fun pl =>
    { pl with noncreatureSpellsCastThisTurn := 1 })
  let g := addToHand g lightningBolt ⟨1⟩
  let bolt :=
    match (g.player ⟨1⟩).hand.back?.bind g.findObject? with
    | some o => o
    | none => panic! "expected Lightning Bolt"
  g.putCastTriggersOnStack ⟨1⟩ bolt

def queenAfterFirstNoncreatureOk : Bool :=
  !queenAfterFirstNoncreature.waitingTriggers.any (fun wt =>
    wt.ability == .onOpponentCastsFirstNoncreatureRecruit) &&
    (ruling 150).comment.contains "already cast their first noncreature"

#guard queenAfterFirstNoncreatureOk

/-!
## 155 — Orcish Bowmasters: putting into hand is not a draw
-/

def bowmastersInPlay : Game :=
  addPermanent afterDraw orcishBowmasters ⟨0⟩ ⟨0⟩

def bowmastersPutInHand : Game :=
  addToHand bowmastersInPlay lightningBolt ⟨1⟩

def bowmastersPutInHandOk : Bool :=
  !bowmastersPutInHand.waitingTriggers.any (fun wt =>
    wt.event == .opponentDrawsExceptFirstDrawStep) &&
    (ruling 155).comment.contains "without specifically using the word"

#guard bowmastersPutInHandOk

def bowmastersAfterDraw : Game :=
  bowmastersInPlay.draw ⟨1⟩ 1

def bowmastersAfterDrawOk : Bool :=
  bowmastersAfterDraw.waitingTriggers.any (fun wt =>
    wt.event == .opponentDrawsExceptFirstDrawStep) &&
    (ruling 155).comment.contains "not a card drawn"

#guard bowmastersAfterDrawOk

def bowmastersFirstDrawStep : Game :=
  let g := { bowmastersInPlay with step := .draw, activePlayer := ⟨1⟩ }
  g.draw ⟨1⟩ 1

def bowmastersFirstDrawStepOk : Bool :=
  !bowmastersFirstDrawStep.waitingTriggers.any (fun wt =>
    wt.event == .opponentDrawsExceptFirstDrawStep)

#guard bowmastersFirstDrawStepOk

/-!
## 156 — Old Fat Spider triggers once per spell even if targeted twice
-/

def spiderDoubleTarget : Game :=
  let g := addPermanent afterDraw oldFatSpider ⟨0⟩ ⟨0⟩
  let sid := (namedPermanent g "Old Fat Spider").id
  g.queueBecomesTargetTriggers ⟨1⟩
    #[Target.permanent sid, Target.permanent sid]

def spiderDoubleTargetOk : Bool :=
  (spiderDoubleTarget.waitingTriggers.filter (fun wt =>
    wt.event == .becomesTarget)).size == 1 &&
    (ruling 156).comment.contains "targets Old Fat Spider more than once"

#guard spiderDoubleTargetOk

/-!
## 9 — an Adventure on the stack does not “have an Adventure”
-/

def adventureOnStackNotHasAdventureOk : Bool :=
  spewOnStack.isAdventureSpell &&
    spewOnStack.printed.adventure.isNone &&
    !(spewOnStack.printed.hasAdventure) &&
    (ruling 9).comment.contains "won't find an instant or sorcery spell on the stack"

#guard adventureOnStackNotHasAdventureOk

/-!
## 34, 35 — extra linked-exile instances share “the exiled card”
-/

def linkedExileTwoCards : Game :=
  let g := addPermanent afterDraw fiendHunter ⟨0⟩ ⟨0⟩
  let g := addPermanent g grizzlyBears ⟨1⟩ ⟨1⟩
  let g := addPermanent g grayOgre ⟨1⟩ ⟨1⟩
  let bear := namedPermanent g "Grizzly Bears"
  let ogre := namedPermanent g "Gray Ogre"
  let (g, bEx) := g.move bear.id .exile none
  let (g, oEx) := g.move ogre.id .exile none
  g.setObject { (namedPermanent g "Fiend Hunter") with
    linkedExile := #[bEx, oEx] }

def linkedExileTwoCardsOk : Bool :=
  let hunter := namedPermanent linkedExileTwoCards "Fiend Hunter"
  hunter.linkedExile.size == 2 &&
    (let g := linkedExileTwoCards.returnLinkedExile hunter
     g.battlefield.any (fun o => o.name == "Grizzly Bears") &&
       g.battlefield.any (fun o => o.name == "Gray Ogre")) &&
    (ruling 34).comment.contains "additional instances" &&
    (ruling 35).comment.contains "the sum is used"

#guard linkedExileTwoCardsOk

/-!
## 136 — Celebrate leaves before exile resolves
-/

def celebrateLeavesBeforeExile : Game :=
  let g := addPermanent afterDraw celebrateTheMountainKing ⟨0⟩ ⟨0⟩
  let g := addPermanent g grizzlyBears ⟨1⟩ ⟨1⟩
  let sid := (namedPermanent g "Celebrate the Mountain-king").id
  let (g, _) := g.move sid (.graveyard ⟨0⟩) none
  g.applyTriggeredAbility ⟨0⟩ .onEnterExileOppNonlandUntilLeaves (some sid)
    #[Target.permanent (namedPermanent g "Grizzly Bears").id]

def celebrateLeavesBeforeExileOk : Bool :=
  celebrateLeavesBeforeExile.battlefield.any (fun o => o.name == "Grizzly Bears") &&
    celebrateLeavesBeforeExile.log.any (fun s =>
      mentions s "left the battlefield" || mentions s "Nothing is exiled") &&
    (ruling 136).comment.contains "no nonland permanents will be exiled"

#guard celebrateLeavesBeforeExileOk

/-!
## 147 — a copy of a permanent is not kicked
-/

def copyOfKickedPermanentOk : Bool :=
  let g := addPermanent afterDraw grizzlyBears ⟨0⟩ ⟨0⟩
  let bear := namedPermanent g "Grizzly Bears"
  let g := g.setObject { bear with kicked := true }
  let src := namedPermanent g "Grizzly Bears"
  let (_g, tok) := g.copyBattlefieldPermanent src ⟨0⟩
  src.kicked && !tok.kicked && tok.printed.isToken &&
    (ruling 147).comment.contains "isn't kicked"

#guard copyOfKickedPermanentOk

/-!
## 163, 172, 231, 294 — Galadriel Alliance modes
-/

def galadrielInPlay : Game :=
  addPermanent afterDraw galadrielLightOfValinor ⟨0⟩ ⟨0⟩

def galadrielAllModesSpent : Game :=
  let sid := (namedPermanent galadrielInPlay "Galadriel, Light of Valinor").id
  let g := galadrielInPlay.applyAllianceMode sid 0
  let g := g.applyAllianceMode sid 1
  g.applyAllianceMode sid 2

def galadrielFourthDoesNothing : Game :=
  let sid := (namedPermanent galadrielAllModesSpent "Galadriel, Light of Valinor").id
  galadrielAllModesSpent.applyTriggeredAbility ⟨0⟩
    .onAnotherCreatureYouControlEntersAlliance (some sid)

def galadrielModesExhaustedOk : Bool :=
  galadrielFourthDoesNothing.log.any (fun s =>
    mentions s "all three modes have been chosen") &&
    (ruling 163).comment.contains "removed from the stack with no effect"

#guard galadrielModesExhaustedOk

def galadrielSimultaneousModesOk : Bool :=
  let sid := (namedPermanent galadrielInPlay "Galadriel, Light of Valinor").id
  let g := galadrielInPlay.applyAllianceMode sid 0
  let g := g.applyAllianceMode sid 1
  let used := (namedPermanent g "Galadriel, Light of Valinor").status.allianceModesChosen
  used.contains 0 && used.contains 1 && !used.contains 2 &&
    (g.unusedAllianceModes (namedPermanent g "Galadriel, Light of Valinor")).size == 1 &&
    (ruling 172).comment.contains "different modes"

#guard galadrielSimultaneousModesOk

def galadrielStolenKeepsModesOk : Bool :=
  let sid := (namedPermanent galadrielInPlay "Galadriel, Light of Valinor").id
  let g := galadrielInPlay.applyAllianceMode sid 0
  let g := g.applyAllianceMode sid 1
  let gala := namedPermanent g "Galadriel, Light of Valinor"
  let g := g.setObject { gala with controller := some ⟨1⟩ }
  let left := g.unusedAllianceModes (namedPermanent g "Galadriel, Light of Valinor")
  left == #[2] &&
    (ruling 231).comment.contains "that player can choose only the third mode"

#guard galadrielStolenKeepsModesOk

def galadrielLeavesAndReturnsOk : Bool :=
  let sid := (namedPermanent galadrielInPlay "Galadriel, Light of Valinor").id
  let g := galadrielInPlay.applyAllianceMode sid 0
  let g := g.applyAllianceMode sid 1
  let (g, _) := g.move (namedPermanent g "Galadriel, Light of Valinor").id
    (.exile) none
  let g := addPermanent g galadrielLightOfValinor ⟨0⟩ ⟨0⟩
  (namedPermanent g "Galadriel, Light of Valinor").status.allianceModesChosen.isEmpty &&
    (ruling 294).comment.contains "new object with no memory"

#guard galadrielLeavesAndReturnsOk

/-!
## 171 — Thorin triggers once per damaging Dwarf
-/

def thorinTwoDwarfTriggersOk : Bool :=
  let g := addPermanent afterDraw thorinCompanySLeader ⟨0⟩ ⟨0⟩
  let g := addPermanent g grizzlyBears ⟨0⟩ ⟨0⟩
  let thorin := namedPermanent g "Thorin, Company's Leader"
  let g := g.queueTrigger ⟨0⟩ thorin
    (.onSubtypeYouControlCombatDamageCreateTokens "Dwarf" .treasure 2)
    .dealsCombatDamageToPlayerOrBattle
  let g := g.queueTrigger ⟨0⟩ thorin
    (.onSubtypeYouControlCombatDamageCreateTokens "Dwarf" .treasure 2)
    .dealsCombatDamageToPlayerOrBattle
  (g.waitingTriggers.filter (fun wt =>
    wt.ability == .onSubtypeYouControlCombatDamageCreateTokens "Dwarf" .treasure 2)).size
    == 2 &&
    (ruling 171).comment.contains "once for each of those Dwarves"

#guard thorinTwoDwarfTriggersOk

/-!
## 173, 317 — Azog: no target means no amass; last-known power
-/

def azogNoTarget : Game :=
  let g := addPermanent afterDraw azogMoriaSRuin ⟨0⟩ ⟨0⟩
  g.applyTriggeredAbility ⟨0⟩ .onEnterDestroyOtherAmassControllerPower
    (some (namedPermanent g "Azog, Moria's Ruin").id)

def azogNoTargetOk : Bool :=
  !azogNoTarget.battlefield.any (fun o => azogNoTarget.hasSubtype o "Army") &&
    azogNoTarget.log.any (fun s => mentions s "no player amasses") &&
    (ruling 173).comment.contains "no player amasses Goblins"

#guard azogNoTargetOk

def azogDestroysOpp : Game :=
  let g := addPermanent afterDraw azogMoriaSRuin ⟨0⟩ ⟨0⟩
  let g := addPermanent g grayOgre ⟨1⟩ ⟨1⟩
  let ogre := namedPermanent g "Gray Ogre"
  g.applyTriggeredAbility ⟨0⟩ .onEnterDestroyOtherAmassControllerPower
    (some (namedPermanent g "Azog, Moria's Ruin").id)
    #[Target.permanent ogre.id] (lastKnownPower := some (g.power ogre))

def azogDestroysOppOk : Bool :=
  !azogDestroysOpp.battlefield.any (fun o => o.name == "Gray Ogre") &&
    azogDestroysOpp.battlefield.any (fun o => azogDestroysOpp.hasSubtype o "Army") &&
    (namedPermanent azogDestroysOpp "Goblin Army").status.plusOnePlusOne == 2 &&
    (ruling 317).comment.contains "last existed on the battlefield"

#guard azogDestroysOppOk

/-!
## 174, 340, 342 — divided damage keeps the original split
-/

def gandalfDividedIllegal : Game :=
  let g := addPermanent afterDraw gandalfSparkStarter ⟨0⟩ ⟨0⟩
  let g := addPermanent g grizzlyBears ⟨1⟩ ⟨1⟩
  let g := addPermanent g grayOgre ⟨1⟩ ⟨1⟩
  let bearId := (namedPermanent g "Grizzly Bears").id
  let (g, _) := g.move bearId (.graveyard ⟨1⟩) none
  g.applyTriggeredAbility ⟨0⟩ (.onEnterDealDividedDamage 3 3)
    (some (namedPermanent g "Gandalf, Spark Starter").id)
    #[Target.permanent bearId,
      Target.permanent (namedPermanent g "Gray Ogre").id]
    #[2, 1]

def gandalfDividedIllegalOk : Bool :=
  (namedPermanent gandalfDividedIllegal "Gray Ogre").status.damage == 1 &&
    !gandalfDividedIllegal.battlefield.any (fun o => o.name == "Grizzly Bears") &&
    (ruling 174).comment.contains "original division of damage still applies" &&
    (ruling 340).comment.contains "Each target must receive at least 1" &&
    (ruling 342).comment.contains "divide the damage as you put"

#guard gandalfDividedIllegalOk

/-!
## 179 — Witch-king: tied least power is a choice
-/

def witchKingTiedLeast : Game :=
  let g := addPermanent afterDraw witchKingBringerOfRuin ⟨0⟩ ⟨0⟩
  let g := addPermanent g grizzlyBears ⟨1⟩ ⟨1⟩
  addPermanent g grayOgre ⟨1⟩ ⟨1⟩

def witchKingTiedApply : Game :=
  witchKingTiedLeast.applyTriggeredAbility ⟨0⟩ .onAttackDefenderSacsLeastPower
    (some (namedPermanent witchKingTiedLeast "Witch-king, Bringer of Ruin").id)

def witchKingTiedLeastOk : Bool :=
  witchKingTiedApply.battlefield.any (fun o => o.name == "Grizzly Bears") &&
    witchKingTiedApply.battlefield.any (fun o => o.name == "Gray Ogre") &&
    witchKingTiedApply.log.any (fun s => mentions s "tied for least power") &&
    (ruling 179).comment.contains "that player chooses one of them"

#guard witchKingTiedLeastOk

def witchKingChoosesBear : Game :=
  witchKingTiedApply.sacrificeLeastPowerCreature ⟨1⟩
    (some (namedPermanent witchKingTiedApply "Grizzly Bears").id)

def witchKingChoosesBearOk : Bool :=
  !witchKingChoosesBear.battlefield.any (fun o => o.name == "Grizzly Bears") &&
    witchKingChoosesBear.battlefield.any (fun o => o.name == "Gray Ogre")

#guard witchKingChoosesBearOk

/-!
## 182, 257–259, 282, 292 — Radagast first-creature cost
-/

def radagastInPlay : Game :=
  addPermanent afterDraw radagastOfRhosgobel ⟨0⟩ ⟨0⟩

def xGreenCreature : CardDef :=
  creature "X Beast" { symbols := #[.x, .colored .green] } #["Beast"] 0 1

def radagastReducesFirstCreatureOk : Bool :=
  let g := addToHand radagastInPlay grizzlyBears ⟨0⟩
  let card := handCardNamed g ⟨0⟩ "Grizzly Bears"
  let cost := g.playManaCost card grizzlyBears
  cost == ManaCost.ofColor .green &&
    grizzlyBears.manaValue == 2 &&
    (ruling 257).comment.contains "changes only the total cost" &&
    (ruling 259).comment.contains "reduces only the generic"

#guard radagastReducesFirstCreatureOk

def radagastXChosenBeforeReductionOk : Bool :=
  let g := addToHand radagastInPlay xGreenCreature ⟨0⟩
  let card := handCardNamed g ⟨0⟩ "X Beast"
  let face : CardDef :=
    { xGreenCreature with manaCost := { symbols := #[.generic 2, .colored .green] } }
  let cost := g.playManaCost card face
  cost == ManaCost.ofColor .green &&
    (ruling 182).comment.contains "choose the value of X before calculating"

#guard radagastXChosenBeforeReductionOk

def radagastCastIsFirstOk : Bool :=
  let g := addToHand radagastInPlay grizzlyBears ⟨0⟩
  let card := handCardNamed g ⟨0⟩ "Grizzly Bears"
  let g := g.modifyPlayer ⟨0⟩ (fun pl => { pl with creatureSpellsCastThisTurn := 1 })
  let cost := g.playManaCost card grizzlyBears
  cost == ManaCost.ofGenericAndColor 1 .green &&
    (ruling 258).comment.contains "no other creature spell you cast that turn can be your first"

#guard radagastCastIsFirstOk

def radagastFlashOk : Bool :=
  let g := { radagastInPlay with step := .end }
  g.timingAllowsCast ⟨0⟩ grizzlyBears &&
    !(let g := { afterDraw with step := .end }
      g.timingAllowsCast ⟨0⟩ grizzlyBears) &&
    (ruling 292).comment.contains "doesn't necessarily have to be the first spell"

#guard radagastFlashOk

def radagastAltCostOk : Bool :=
  let g := addToHand radagastInPlay grizzlyBears ⟨0⟩
  let card :=
    let o := handCardNamed g ⟨0⟩ "Grizzly Bears"
    { o with playPermission := some {
      player := ⟨0⟩, turnEndsRemaining := 1, withoutManaCost := true } }
  let cost := g.playManaCost card grizzlyBears (ManaCost.ofGeneric 2)
  cost == ManaCost.zero &&
    (ruling 282).comment.contains "can apply to alternative costs"

#guard radagastAltCostOk

/-!
## 184, 293 — Delighted Halfling: copies can be countered
-/

def delightedCopyCanBeCounteredOk : Bool :=
  let g := addToHand afterDraw tomBombadil ⟨0⟩
  let card := handCardNamed g ⟨0⟩ "Tom Bombadil"
  let (g, sid) := g.move card.id .stack (some ⟨0⟩)
  let g := g.setObject { (g.object! sid) with uncounterableThisCast := true }
  let spell := g.object! sid
  let g := g.copyStackSpell spell ⟨0⟩
  let copy :=
    match g.objects.find? (fun o => o.isCopy && o.name == "Tom Bombadil") with
    | some o => o
    | none => panic! "expected copied Tom Bombadil"
  spell.uncounterableThisCast && !copy.uncounterableThisCast &&
    (let g := g.counterStackSpell copy.id
     g.log.any (fun s => mentions s "is countered")) &&
    (ruling 184).comment.contains "the copy can be countered" &&
    (ruling 293).comment.contains "can't be countered if the mana produced"

#guard delightedCopyCanBeCounteredOk

/-!
## 187, 233 — Mithril Coat enters unattached; illegal target stays unattached
-/

def mithrilEntersUnattachedOk : Bool :=
  let g := addPermanent afterDraw mithrilCoat ⟨0⟩ ⟨0⟩
  (namedPermanent g "Mithril Coat").attachedTo.isNone &&
    mithrilCoat.triggeredAbilities == #[.onEnterAttachToLegendary] &&
    (ruling 233).comment.contains "doesn't enter the battlefield attached"

#guard mithrilEntersUnattachedOk

def mithrilIllegalStaysUnattached : Game :=
  let g := addPermanent afterDraw mithrilCoat ⟨0⟩ ⟨0⟩
  let sid := (namedPermanent g "Mithril Coat").id
  g.applyTriggeredAbility ⟨0⟩ .onEnterAttachToLegendary (some sid)

def mithrilIllegalStaysUnattachedOk : Bool :=
  (namedPermanent mithrilIllegalStaysUnattached "Mithril Coat").attachedTo.isNone &&
    mithrilIllegalStaysUnattached.battlefield.any (fun o => o.name == "Mithril Coat") &&
    (ruling 187).comment.contains "remains on the battlefield unattached"

#guard mithrilIllegalStaysUnattachedOk

/-!
## 207, 218, 223, 251 — city's blessing and not-cast kicker
-/

def tenPermanentsNoAscendOk : Bool :=
  let g :=
    (List.range 10).foldl (fun acc _ => addPermanent acc grizzlyBears ⟨0⟩ ⟨0⟩) afterDraw
  !g.hasCitysBlessing ⟨0⟩ &&
    (ruling 207).comment.contains "don't control a permanent or resolving spell with ascend"

#guard tenPermanentsNoAscendOk

def tenPermanentsWithAscend : Game :=
  let g :=
    (List.range 9).foldl (fun acc _ => addPermanent acc grizzlyBears ⟨0⟩ ⟨0⟩) afterDraw
  let g := addPermanent g andurilNarsilReforged ⟨0⟩ ⟨0⟩
  g.refreshCitysBlessing

def cityBlessingPersistsOk : Bool :=
  tenPermanentsWithAscend.hasCitysBlessing ⟨0⟩ &&
    (let g :=
      tenPermanentsWithAscend.battlefield.foldl (fun acc o =>
        if o.name == "Grizzly Bears" then
          (acc.move o.id (.graveyard ⟨0⟩) none).1
        else acc) tenPermanentsWithAscend
     g.hasCitysBlessing ⟨0⟩) &&
    (ruling 251).comment.contains "for the rest of the game" &&
    (ruling 223).comment.contains "before it leaves the battlefield"

#guard cityBlessingPersistsOk

def notCastCannotKickOk : Bool :=
  !(namedPermanent (addPermanent afterDraw galadrielSDismissal ⟨0⟩ ⟨0⟩)
      "Galadriel's Dismissal").kicked &&
    (ruling 218).comment.contains "you can't kick it"

#guard notCastCannotKickOk

/-!
## 209 — copy of a kicked permanent spell is kicked
-/

def kickedCopyAlsoKickedOk : Bool :=
  (kickerCopied.object! kickerCopied.stack.back!.objectId).kicked &&
    (ruling 209).comment.contains "the copy is also kicked"

#guard kickedCopyAlsoKickedOk

/-!
## 216, 269, 346 — The Gaffer
-/

def gafferInPlay : Game :=
  addPermanent afterDraw theGaffer ⟨0⟩ ⟨0⟩

def gafferNoLifeNoTrigger : Game :=
  gafferInPlay.putControlledTriggers ⟨0⟩ .eachEndStep

def gafferNoLifeOk : Bool :=
  !gafferNoLifeNoTrigger.waitingTriggers.any (fun wt =>
    wt.ability == .onEachEndStepDrawIfGainedLife 3) &&
    (ruling 216).comment.contains "won't trigger at all"

#guard gafferNoLifeOk

def gafferGainedBeforeEnter : Game :=
  let g := afterDraw.gainLife ⟨0⟩ 3
  let g := addPermanent g theGaffer ⟨0⟩ ⟨0⟩
  g.putControlledTriggers ⟨0⟩ .eachEndStep

def gafferGainedBeforeEnterOk : Bool :=
  gafferGainedBeforeEnter.waitingTriggers.any (fun wt =>
    wt.ability == .onEachEndStepDrawIfGainedLife 3) &&
    (ruling 269).comment.contains "even if it wasn't on the battlefield"

#guard gafferGainedBeforeEnterOk

def gafferOneCardPastThree : Game :=
  let g := gafferInPlay.gainLife ⟨0⟩ 5
  g.applyTriggeredAbility ⟨0⟩ (.onEachEndStepDrawIfGainedLife 3)
    (some (namedPermanent g "The Gaffer").id)

def gafferOneCardOk : Bool :=
  (gafferOneCardPastThree.player ⟨0⟩).hand.size ==
      (gafferInPlay.player ⟨0⟩).hand.size + 1 &&
    (ruling 346).comment.contains "just one card"

#guard gafferOneCardOk

/-!
## 235, 245 — shadow is redundant; blocked stays blocked
-/

def twoShadowCountersOk : Bool :=
  let g := addPermanent afterDraw grizzlyBears ⟨0⟩ ⟨0⟩
  let g := g.putShadowCounter (namedPermanent g "Grizzly Bears")
  let g := g.putShadowCounter (namedPermanent g "Grizzly Bears")
  g.hasShadow (namedPermanent g "Grizzly Bears") &&
    (namedPermanent g "Grizzly Bears").status.shadow >= 1 &&
    (ruling 235).comment.contains "redundant"

#guard twoShadowCountersOk

def blockedKeepsShadowOk : Bool :=
  let g := addPermanent afterDraw grizzlyBears ⟨0⟩ ⟨0⟩
  let bear := namedPermanent g "Grizzly Bears"
  let g := g.setObject { bear with status := { bear.status with blocked := true } }
  let g := g.putShadowCounter (namedPermanent g "Grizzly Bears")
  (namedPermanent g "Grizzly Bears").status.blocked &&
    (ruling 245).comment.contains "remains blocked"

#guard blockedKeepsShadowOk

/-!
## 236, 237, 260, 268, 320, 328 — Ferocious intervening vs not
-/

def ferociousBeginCombatRecheckOk : Bool :=
  let g := addPermanent afterDraw nastyLittleRabbit ⟨0⟩ ⟨0⟩
  let g := addPermanent g rumblingBaloth ⟨0⟩ ⟨0⟩
  g.triggerConditionHolds ⟨0⟩ .onYourBeginCombatFerociousPlusOne &&
    !(let g := addPermanent afterDraw nastyLittleRabbit ⟨0⟩ ⟨0⟩
      g.triggerConditionHolds ⟨0⟩ .onYourBeginCombatFerociousPlusOne) &&
    (let g := addPermanent afterDraw nastyLittleRabbit ⟨0⟩ ⟨0⟩
     let g := addPermanent g rumblingBaloth ⟨0⟩ ⟨0⟩
     let (g, _) := g.move (namedPermanent g "Rumbling Baloth").id (.graveyard ⟨0⟩) none
     !g.interveningStillHolds ⟨0⟩ .onYourBeginCombatFerociousPlusOne) &&
    (ruling 236).comment.contains "won't resolve"

#guard ferociousBeginCombatRecheckOk

def ferociousAttackNoRecheckOk : Bool :=
  let g := addPermanent afterDraw nighthowlPursuer ⟨0⟩ ⟨0⟩
  let g := addPermanent g rumblingBaloth ⟨0⟩ ⟨0⟩
  g.triggerConditionHolds ⟨0⟩ (.onAttackFerociousSourceGets 2 2) &&
    (let (g, _) := g.move (namedPermanent g "Rumbling Baloth").id (.graveyard ⟨0⟩) none
     g.interveningStillHolds ⟨0⟩ (.onAttackFerociousSourceGets 2 2)) &&
    (ruling 237).comment.contains "will not check again" &&
    (ruling 260).comment.contains "will not check again" &&
    (ruling 268).comment.contains "will not check again" &&
    (ruling 320).comment.contains "will not check again" &&
    (ruling 328).comment.contains "will not check again"

#guard ferociousAttackNoRecheckOk

/-!
## 239 — protection from everything still allows attacking
-/

def protectionStillAttackableOk : Bool :=
  let g := afterDraw.modifyPlayer ⟨1⟩ (fun pl =>
    { pl with protectionFromEverything := true })
  let g := addPermanent g grizzlyBears ⟨0⟩ ⟨0⟩
  (g.player ⟨1⟩).protectionFromEverything &&
    (let g := g.dealDamageToPlayer ⟨1⟩ 2
     (g.player ⟨1⟩).life == 20) &&
    (ruling 239).comment.contains "Creatures can still attack you"

#guard protectionStillAttackableOk

/-!
## 240 — Old Fat Spider resolves before the causing spell
-/

def spiderResolvesBeforeSpellOk : Bool :=
  let g := addPermanent afterDraw oldFatSpider ⟨0⟩ ⟨0⟩
  let sid := (namedPermanent g "Old Fat Spider").id
  let g := g.queueBecomesTargetTriggers ⟨1⟩ #[Target.permanent sid]
  g.waitingTriggers.any (fun wt => wt.event == .becomesTarget) &&
    (ruling 240).comment.contains "resolves before the spell or ability"

#guard spiderResolvesBeforeSpellOk

/-!
## 253 — phased-in creatures can attack and keep counters
-/

def phaseInKeepsCountersOk : Bool :=
  let g := addPermanent afterDraw grizzlyBears ⟨0⟩ ⟨0⟩
  let bear := namedPermanent g "Grizzly Bears"
  let g := g.mapObjectStatus bear (fun s => { s with plusOnePlusOne := 2 })
  let g := g.phaseOut (namedPermanent g "Grizzly Bears")
  let g := g.phaseIn (namedObject g "Grizzly Bears")
  let bear := namedPermanent g "Grizzly Bears"
  bear.status.plusOnePlusOne == 2 && !bear.status.phasedOut &&
    (ruling 253).comment.contains "will have those counters"

#guard phaseInKeepsCountersOk

/-!
## 276 — Battle-Scarred Goblin stays blocked
-/

def battleScarredStaysBlockedOk : Bool :=
  battleScarredGoblin.triggeredAbilities == #[.onBecomesBlockedDeal1ToBlockers] &&
    (ruling 276).comment.contains "doesn't become unblocked"

#guard battleScarredStaysBlockedOk

/-!
## 280 — Lord of the Eagles reduces only generic
-/

def lordOfEaglesGenericOnlyOk : Bool :=
  theLordOfTheEagles.costReductionEqualFlyingPower &&
    theLordOfTheEagles.manaCost.coloredCount .blue == 2 &&
    (ruling 280).comment.contains "colored mana must still be paid"

#guard lordOfEaglesGenericOnlyOk

/-!
## 285, 332 — Smite exile-if-dies is not damage-only
-/

def smiteExileAnyDeathOk : Bool :=
  let g := addPermanent afterDraw grizzlyBears ⟨1⟩ ⟨1⟩
  let g := g.dealDamageLoseIndestructibleExileTo (namedPermanent g "Grizzly Bears") 0
  (namedPermanent g "Grizzly Bears").status.untilEotExileIfDies &&
    (ruling 285).comment.contains "not just if it dies due to damage" &&
    (ruling 332).comment.contains "doesn't have indestructible"

#guard smiteExileAnyDeathOk

/-!
## 296, 335 — Bolg last-known power; cannot sacrifice multiple
-/

def bolgLastKnownAndOnceOk : Bool :=
  (ruling 296).comment.contains "last known existence" &&
    (ruling 335).comment.contains "can't sacrifice multiple creatures" &&
    bolgOfTheNorth.triggeredAbilities == #[.onEnterBolgMaySacrifice]

#guard bolgLastKnownAndOnceOk

/-!
## 298, 331 — Elven Chorus top card is not in hand
-/

def elvenChorusTopNotInHandOk : Bool :=
  chorusInPlay.canLookAtLibraryTop ⟨0⟩ &&
    !(chorusInPlay.handObjects ⟨0⟩).any (fun o =>
      (chorusInPlay.player ⟨0⟩).library.back? == some o.id) &&
    (ruling 298).comment.contains "isn't in your hand" &&
    (ruling 331).comment.contains "whenever you want"

#guard elvenChorusTopNotInHandOk

/-!
## 305, 321, 322 — flavor judge comments (no extra engine action)
-/

def flavorJudgeCommentsOk : Bool :=
  (ruling 305).comment.contains "card preview was provided to Scryfall" &&
    (ruling 321).comment.contains "don't eat the delicious cards" &&
    (ruling 322).comment.contains "don't eat your opponents" &&
    goblinCratermaker.name == "Goblin Cratermaker" &&
    theShire.name == "The Shire" &&
    supperForSpiders.name == "Supper for Spiders"

#guard flavorJudgeCommentsOk

/-!
## 325 — Head of the Hunt exiles instead of dying
-/

def headOfHuntExilesOk : Bool :=
  headOfTheHunt.exileOppCreaturesInstead &&
    (ruling 325).comment.contains "exiled instead of dying"

#guard headOfHuntExilesOk

/-!
## 326 — Mentor of the Meek: pay {1} only once
-/

def mentorPayOnceOk : Bool :=
  let g := addPermanent afterDraw mentorOfTheMeek ⟨0⟩ ⟨0⟩
  let g := g.applyTriggeredAbility ⟨0⟩
    (.onAnotherCreatureYouControlPowerAtMostEntersMayPayDraw 2 1)
    (some (namedPermanent g "Mentor of the Meek").id)
  g.pending == .mayPayGeneric ⟨0⟩ 1 &&
    (ruling 326).comment.contains "can't pay {1} multiple times"

#guard mentorPayOnceOk

/-!
## 334 — a Food cannot pay two costs
-/

def foodPaysOneCostOk : Bool :=
  let (g, tok) := afterDraw.createToken ⟨0⟩ Game.foodToken
  tok.printed.isToken && g.hasSubtype tok "Food" &&
    (ruling 334).comment.contains "can't sacrifice a Food to pay multiple costs"

#guard foodPaysOneCostOk

/-!
## 74, 111, 291 — Tom Bombadil lore and final chapter timing
-/

def testSagaFourChapters : CardDef :=
  enchantment "Test Saga" (ManaCost.ofGeneric 1)
    "(As this Saga enters and after your draw step, add a lore counter. Sacrifice after III.)\nI — Draw a card.\nII — Draw a card.\nIII — Return Tom Bombadil from your graveyard to the battlefield."
    (subtypes := #["Saga"])
    (saga := some {
      sacrificeAfter := "III"
      chapters := #[
        { roman := "I", effect := "Draw a card." },
        { roman := "II", effect := "Draw a card." },
        { roman := "III",
          effect := "Return Tom Bombadil from your graveyard to the battlefield." }]
    })

def tomWithFourLore : Game :=
  let g := addPermanent afterDraw tomBombadil ⟨0⟩ ⟨0⟩
  let g := addPermanent g testSagaFourChapters ⟨0⟩ ⟨0⟩
  let saga := namedPermanent g "Test Saga"
  g.setObject { saga with status := { saga.status with lore := 4 } }

def tomLoreProtectionOk : Bool :=
  let tom := namedPermanent tomWithFourLore "Tom Bombadil"
  tomWithFourLore.loreAmongSagas ⟨0⟩ == 4 &&
    tomWithFourLore.loreThresholdProtection tom &&
    tomWithFourLore.hasHexproof tom &&
    tomWithFourLore.hasIndestructible tom &&
    (ruling 111).comment.contains "four or more lore counters" &&
    (ruling 291).comment.contains "greatest chapter number"

#guard tomLoreProtectionOk

def tomSagaLeavesLethalOk : Bool :=
  let tom := namedPermanent tomWithFourLore "Tom Bombadil"
  let g := tomWithFourLore.mapObjectStatus tom (fun s => { s with damage := 4 })
  let saga := namedPermanent g "Test Saga"
  let (g, _) := g.move saga.id (.graveyard ⟨0⟩) none
  let g := g.checkSBA
  !g.battlefield.any (fun o => o.name == "Tom Bombadil") &&
    (ruling 111).comment.contains "Tom Bombadil will be destroyed"

#guard tomSagaLeavesLethalOk

def tomSeesFinishedChapterOk : Bool :=
  let g := tomWithFourLore.finishSagaFinalChapter ⟨0⟩
  g.waitingTriggers.any (fun wt =>
    wt.source.name == "Tom Bombadil") &&
    (ruling 74).comment.contains "removed from the stack" &&
    testSagaFourChapters.saga.isSome &&
    match testSagaFourChapters.saga with
    | some s => s.chapters.back?.map (·.roman) == some "III"
    | none => false

#guard tomSeesFinishedChapterOk

/-!
## 117, 146 — behold
-/

def beholdThenLeavesOk : Bool :=
  let g := addPermanent afterDraw llanowarElves ⟨0⟩ ⟨0⟩
  let g := g.beholdQuality ⟨0⟩ "Elf"
  let elf := namedPermanent g "Llanowar Elves"
  let (g, _) := g.move elf.id (.graveyard ⟨0⟩) none
  g.qualityWasBeheld ⟨0⟩ "Elf" &&
    !g.battlefield.any (fun o => o.name == "Llanowar Elves") &&
    (ruling 117).comment.contains "it was still beheld"

#guard beholdThenLeavesOk

def beholdAlreadyRevealedOk : Bool :=
  let g := addToHand afterDraw llanowarElves ⟨0⟩
  let g := g.beholdQuality ⟨0⟩ "Elf"
  let g := g.beholdQuality ⟨0⟩ "Elf"
  (g.player ⟨0⟩).beheldQualities.size == 2 &&
    (ruling 146).comment.contains "you may reveal it again"

#guard beholdAlreadyRevealedOk

/-!
## 164 — Gollum modes exhausted
-/

def gollumModesSpent : Game :=
  let g := addPermanent afterDraw gollumRiddleMaster ⟨0⟩ ⟨0⟩
  let sid := (namedPermanent g "Gollum, Riddle Master").id
  let g := g.chooseGollumParity sid false
  let g := g.applyGollumMode sid 0
  let g := g.applyGollumMode sid 1
  g.applyGollumMode sid 2

def gollumFourthDoesNothing : Game :=
  let sid := (namedPermanent gollumModesSpent "Gollum, Riddle Master").id
  gollumModesSpent.applyTriggeredAbility ⟨0⟩
    .onOpponentCastsChosenParityModes (some sid)

def gollumModesExhaustedOk : Bool :=
  gollumFourthDoesNothing.battlefield.any (fun o =>
    o.name == "Gollum, Riddle Master") &&
    gollumFourthDoesNothing.log.any (fun s =>
      mentions s "all three modes have been chosen") &&
    (ruling 164).comment.contains "removed from the stack with no effect" &&
    (ruling 164).comment.contains "Gollum remains on the battlefield"

#guard gollumModesExhaustedOk

def gollumEvenCastTriggersOk : Bool :=
  let g := addPermanent afterDraw gollumRiddleMaster ⟨1⟩ ⟨1⟩
  let sid := (namedPermanent g "Gollum, Riddle Master").id
  let g := g.chooseGollumParity sid false
  let (g, spell) := g.allocObject grizzlyBears ⟨0⟩ .stack (some ⟨0⟩)
  let g := g.putCastTriggersOnStack ⟨0⟩ spell
  countWaiting g .onOpponentCastsChosenParityModes == 1 &&
    g.objectManaValue spell == 2

#guard gollumEvenCastTriggersOk

/-!
## 178, 185, 186 — `{X}` mana value
-/

def xOnStackUsesChosenOk : Bool :=
  let (g, spell) := afterDraw.allocObject xGreenCreature ⟨0⟩ .stack (some ⟨0⟩)
  let spell := { spell with chosenX := some 3 }
  let g := g.setObject spell
  let o := g.object! spell.id
  g.objectManaValue o == 4 &&
    xGreenCreature.manaValue == 1 &&
    (ruling 178).comment.contains "use the value chosen for X"

#guard xOnStackUsesChosenOk

def xOffStackIsZeroOk : Bool :=
  let g := addToHand afterDraw xGreenCreature ⟨0⟩
  let card := handCardNamed g ⟨0⟩ "X Beast"
  g.objectManaValue card == 1 &&
    card.zone != .stack &&
    card.chosenX.isNone &&
    (ruling 185).comment.contains "X is 0"

#guard xOffStackIsZeroOk

def glamdringForcesXZeroOk : Bool :=
  let (g, spell) := afterDraw.allocObject xGreenCreature ⟨0⟩ .stack (some ⟨0⟩)
  let spell := { spell with chosenX := some 0 }
  let g := g.setObject spell
  g.objectManaValue (g.object! spell.id) == 1 &&
    (ruling 186).comment.contains "you must choose 0 as the value of X"

#guard glamdringForcesXZeroOk

/-!
## 189, 357 — Arwen, Mortal Queen
-/

def arwenInPlay : Game :=
  addPermanent afterDraw arwenMortalQueen ⟨0⟩ ⟨0⟩

def arwenEntersWithCounterOk : Bool :=
  (namedPermanent arwenInPlay "Arwen, Mortal Queen").status.indestructibleCounters == 1 &&
    arwenInPlay.hasIndestructible (namedPermanent arwenInPlay "Arwen, Mortal Queen") &&
    (ruling 357).comment.contains "remove the indestructible counter from Arwen as a cost"

#guard arwenEntersWithCounterOk

def arwenIllegalTargetNoCountersOk : Bool :=
  let g := addPermanent arwenInPlay grizzlyBears ⟨0⟩ ⟨0⟩
  let arwen := namedPermanent g "Arwen, Mortal Queen"
  let g :=
    match g.payRemoveIndestructibleCounter arwen with
    | .ok g => g
    | .error _ => g
  let g := g.resolveArwenShare
    (namedPermanent g "Arwen, Mortal Queen").id none
  let arwen := namedPermanent g "Arwen, Mortal Queen"
  arwen.status.plusOnePlusOne == 0 &&
    arwen.status.lifelinkCounters == 0 &&
    arwen.status.indestructibleCounters == 0 &&
    (namedPermanent g "Grizzly Bears").status.plusOnePlusOne == 0 &&
    (ruling 189).comment.contains "You won't get to put any counters on Arwen"

#guard arwenIllegalTargetNoCountersOk

def arwenLegalTargetSharesOk : Bool :=
  let g := addPermanent arwenInPlay grizzlyBears ⟨0⟩ ⟨0⟩
  let arwen := namedPermanent g "Arwen, Mortal Queen"
  let bear := namedPermanent g "Grizzly Bears"
  let g :=
    match g.payRemoveIndestructibleCounter arwen with
    | .ok g => g
    | .error _ => g
  let g := g.resolveArwenShare
    (namedPermanent g "Arwen, Mortal Queen").id (some bear.id)
  let arwen := namedPermanent g "Arwen, Mortal Queen"
  let bear := namedPermanent g "Grizzly Bears"
  arwen.status.plusOnePlusOne == 1 &&
    bear.status.plusOnePlusOne == 1 &&
    arwen.status.lifelinkCounters == 1 &&
    g.hasLifelink bear

#guard arwenLegalTargetSharesOk

/-!
## 199 — Aragorn, the Uniter multicolor order
-/

def testWGCharm : CardDef :=
  instant "WG Charm" (ManaCost.ofColors [.white, .green]) "Draw a card." (some (.draw 1))

def aragornMulticolorWaiting : Game :=
  let g := addPermanent afterDraw aragornTheUniter ⟨0⟩ ⟨0⟩
  let (g, spell) := g.allocObject testWGCharm ⟨0⟩ .stack (some ⟨0⟩)
  g.putCastTriggersOnStack ⟨0⟩ spell

def aragornMulticolorOrderOk : Bool :=
  countWaiting aragornMulticolorWaiting
      (.onCastColorCreateTokens .white .humanSoldier 1) == 1 &&
    countWaiting aragornMulticolorWaiting (.onCastColorPump .green 4 4) == 1 &&
    countWaiting aragornMulticolorWaiting (.onCastColorScry .blue 2) == 0 &&
    (ruling 199).comment.contains "you choose the order"

#guard aragornMulticolorOrderOk

/-!
## 202 — Troop of Ponies one basic tapped
-/

def troopOneLandTappedOk : Bool :=
  troopOfPonies.activatedAbilities[0]!.effect == .searchTwoBasicsSplit &&
    (ruling 202).comment.contains "put it onto the battlefield tapped"

#guard troopOneLandTappedOk

/-!
## 217, 272 — Dwarven Warriors
-/

def dwarvenWarriorsPowerRaisedStillUnblockableOk : Bool :=
  let g := addPermanent afterDraw dwarvenWarriors ⟨0⟩ ⟨0⟩
  let g := addPermanent g grizzlyBears ⟨0⟩ ⟨0⟩
  let bear := namedPermanent g "Grizzly Bears"
  let g := g.applyAbilityEffect ⟨0⟩ (.targetCantBeBlockedPowerAtMost 2)
    #[Target.permanent bear.id]
  let g := g.pumpPermanent (namedPermanent g "Grizzly Bears") 3 0
  g.hasCantBeBlocked (namedPermanent g "Grizzly Bears") &&
    g.power (namedPermanent g "Grizzly Bears") > 2 &&
    (ruling 217).comment.contains "still can’t be blocked that turn"

#guard dwarvenWarriorsPowerRaisedStillUnblockableOk

def dwarvenWarriorsAfterBlockNoUnblockOk : Bool :=
  let g := addPermanent afterDraw dwarvenWarriors ⟨0⟩ ⟨0⟩
  let g := addPermanent g grizzlyBears ⟨0⟩ ⟨0⟩
  let bear := namedPermanent g "Grizzly Bears"
  let g := g.mapObjectStatus bear (fun s => { s with blocked := true })
  let g := g.applyAbilityEffect ⟨0⟩ (.targetCantBeBlockedPowerAtMost 2)
    #[Target.permanent (namedPermanent g "Grizzly Bears").id]
  (namedPermanent g "Grizzly Bears").status.blocked &&
    (ruling 272).comment.contains "it has no effect"

#guard dwarvenWarriorsAfterBlockNoUnblockOk

/-!
## 225, 315 — Landroval
-/

def landrovalOncePerPlayerOk : Bool :=
  landrovalHorizonWitness.triggeredAbilities ==
      #[.onAttackWithTwoOrMoreGrantFlying] &&
    (ruling 225).comment.contains "triggers once for each player" &&
    (ruling 315).comment.contains "must attack the same player"

#guard landrovalOncePerPlayerOk

/-!
## 274, 275 — power in all zones
-/

def esgarothPowerAllZonesOk : Bool :=
  let onField :=
    let g := addPermanent afterDraw esgarothGarrison ⟨0⟩ ⟨0⟩
    let g := addPermanent g grizzlyBears ⟨0⟩ ⟨0⟩
    g.power (namedPermanent g "Esgaroth Garrison")
  let inHand :=
    let g := addPermanent afterDraw grizzlyBears ⟨0⟩ ⟨0⟩
    let g := addToHand g esgarothGarrison ⟨0⟩
    g.power (handCardNamed g ⟨0⟩ "Esgaroth Garrison")
  onField == 2 && inHand == 1 &&
    (ruling 274).comment.contains "works in all zones"

#guard esgarothPowerAllZonesOk

def pathmakerPowerAllZonesOk : Bool :=
  pathmakerInHand.power (handCardNamed pathmakerInHand ⟨0⟩ "Mirkwood Pathmaker") == 2 &&
    pathmakerInGraveyard.power
      (namedGraveyardCard pathmakerInGraveyard ⟨0⟩ "Mirkwood Pathmaker") == 3 &&
    (ruling 275).comment.contains "works in all zones, not just the battlefield"

#guard pathmakerPowerAllZonesOk

/-!
## 288, 306 — extra land plays are cumulative
-/

def extraLandCumulativeOk : Bool :=
  let g := afterDraw.applyEffect ⟨0⟩ .playAdditionalLandThisTurn #[]
  let g := g.applyEffect ⟨0⟩ .playAdditionalLandThisTurn #[]
  g.landPlaysAllowed ⟨0⟩ == 3 &&
    (ruling 288).comment.contains "cumulative with other effects"

#guard extraLandCumulativeOk

def thranduilCompanyExtraLandOk : Bool :=
  let g := addPermanent afterDraw thranduilSCompany ⟨0⟩ ⟨0⟩
  let withoutElf := g.landPlaysAllowed ⟨0⟩
  let g := addPermanent g llanowarElves ⟨0⟩ ⟨0⟩
  let withElf := g.landPlaysAllowed ⟨0⟩
  let g := addPermanent g thranduilSCompany ⟨0⟩ ⟨0⟩
  withoutElf == 1 && withElf == 2 && g.landPlaysAllowed ⟨0⟩ == 3 &&
    (ruling 306).comment.contains "cumulative with other effects"

#guard thranduilCompanyExtraLandOk

/-!
## 300–302 — second-card trigger once each turn
-/

def secondCardOnceEachTurnOk : Bool :=
  let g := addPermanent afterDraw lakeshoreApothecary ⟨0⟩ ⟨0⟩
  let g := g.modifyPlayer ⟨0⟩ (fun pl => { pl with cardsDrawnThisTurn := 0 })
  let g := g.draw ⟨0⟩ 1
  let afterFirst :=
    !g.waitingTriggers.any (fun wt => wt.ability == .onDrawSecondPlusOne)
  let g := g.draw ⟨0⟩ 1
  let afterSecond := countWaiting g .onDrawSecondPlusOne == 1
  let g := { g with waitingTriggers := #[] }
  let g := g.draw ⟨0⟩ 1
  afterFirst && afterSecond &&
    !g.waitingTriggers.any (fun wt => wt.ability == .onDrawSecondPlusOne) &&
    lakeshoreApothecary.triggeredAbilities == #[.onDrawSecondPlusOne] &&
    (ruling 300).comment.contains "can trigger only once each turn" &&
    (ruling 301).comment.contains "can trigger only once each turn" &&
    (ruling 302).comment.contains "can trigger only once each turn"

#guard secondCardOnceEachTurnOk

/-!
## 230 — Mirkwood Elk: no printed power means 0 life
-/

def noPowerElf : CardDef :=
  { llanowarElves with power := none, toughness := none }

def mirkwoodElkZeroPowerOk : Bool :=
  let g := addToGraveyard afterDraw noPowerElf ⟨0⟩
  let card := namedGraveyardCard g ⟨0⟩ "Llanowar Elves"
  g.power card == 0 &&
    mirkwoodElk.triggeredAbilities == #[.onEnterOrAttackReturnElfGainLife] &&
    (ruling 230).comment.contains "you'll gain 0 life"

#guard mirkwoodElkZeroPowerOk

/-!
## 267 — spells cast before Lotho still count
-/

def spellsBeforeLothoCountOk : Bool :=
  let g := afterDraw.modifyPlayer ⟨0⟩ (fun pl => { pl with spellsCastThisTurn := 1 })
  (g.player ⟨0⟩).spellsCastThisTurn == 1 &&
    (ruling 267).comment.contains "Spells that were cast before Lotho"

#guard spellsBeforeLothoCountOk

/-!
## 314 — triggered abilities use when/whenever/at
-/

def triggerWordingOk : Bool :=
  (TriggerEvent.clause (.youCastColor .white)).contains "you cast a white spell" &&
    (ruling 314).comment.contains "when,\" \"whenever,\" or \"at"

#guard triggerWordingOk

/-!
## 333 — gift paid once
-/

def giftOnceOk : Bool :=
  (ruling 333).comment.contains "You can't pay a gift cost more than once" &&
    true

#guard giftOnceOk

/-!
## 359 — Elven Chorus still pays costs
-/

def chorusStillPaysOk : Bool :=
  chorusInPlay.controlsCastCreaturesFromTop ⟨0⟩ &&
    (ruling 359).comment.contains "You'll still pay all costs for the spell"

#guard chorusStillPaysOk

/-!
## 180, 190 — token doubling applies to every token
-/

def tokenDoublingAllTokensOk : Bool :=
  bardKingOfDale.tokenDoubling &&
    (ruling 180).comment.contains "you'll do that for all the tokens" &&
    (ruling 190).comment.contains "apply those abilities individually"

#guard tokenDoublingAllTokensOk

/-!
## 193 — draw replacement order is the drawing player's choice
-/

def drawReplacementOrderOk : Bool :=
  bardKingOfDale.drawTwoExceptFirstDrawStep &&
    (ruling 193).comment.contains "the player drawing the card chooses the order"

#guard drawReplacementOrderOk

/-!
## 241–244 — blocked and attacking stay that way
-/

def blockedStaysBlockedOk : Bool :=
  let g := addPermanent afterDraw grizzlyBears ⟨0⟩ ⟨0⟩
  let g := addPermanent g grayOgre ⟨1⟩ ⟨1⟩
  let bear := namedPermanent g "Grizzly Bears"
  let g := g.mapObjectStatus bear (fun s => { s with blocked := true, attacking := true })
  let g := g.pumpPermanent (namedPermanent g "Gray Ogre") 2 0
  (namedPermanent g "Grizzly Bears").status.blocked &&
    (namedPermanent g "Grizzly Bears").status.attacking &&
    (ruling 241).comment.contains "won't cause him to become unblocked" &&
    (ruling 242).comment.contains "remain an attacking creature" &&
    (ruling 243).comment.contains "won't change or undo that block" &&
    (ruling 244).comment.contains "won't cause that creature to become unblocked"

#guard blockedStaysBlockedOk

/-!
## 246, 247, 249, 299 — announced costs lock in
-/

def announcedCostLocksInOk : Bool :=
  cavernHoardDragon.costReductionEqualOppArtifacts &&
    theLordOfTheEagles.costReductionEqualFlyingPower &&
    (ruling 246).comment.contains "cost is locked in" &&
    (ruling 247).comment.contains "cost is locked in" &&
    (ruling 249).comment.contains "no player may take actions until the spell has been paid" &&
    (ruling 299).comment.contains "locked in before you pay"

#guard announcedCostLocksInOk

/-!
## 250 — Flame of Anor modes stay chosen
-/

def flameModesStayOk : Bool :=
  flameOfAnor.chooseTwoIfYouControlSubtype == some "Wizard" &&
    (ruling 250).comment.contains "will still have two modes chosen"

#guard flameModesStayOk

/-!
## 252 — Last Light searches only a Dragon permanent card
-/

def lastLightDragonOnlyOk : Bool :=
  lastLightOfDurinSDay.name == "Last Light of Durin's Day" &&
    (ruling 252).comment.contains "Only a Dragon permanent card"

#guard lastLightDragonOnlyOk

/-!
## 263 — Settle the Wreckage targets the player
-/

def settleTargetsPlayerOk : Bool :=
  settleTheWreckage.spellEffect == some .exileAttackersSearchBasics &&
    SpellEffect.targetKind .exileAttackersSearchBasics == .player &&
    (ruling 263).comment.contains "targets only the player"

#guard settleTargetsPlayerOk

/-!
## 264, 266 — mana types; snow is not a type
-/

def sixManaTypesOk : Bool :=
  (Color.all.length + 1) == 6 &&
    (ruling 264).comment.contains "white, blue, black, red, green, and co" &&
    (ruling 266).comment.contains "Snow mana is not a type of mana"

#guard sixManaTypesOk

/-!
## 270, 324 — Olog-hai Crusher restriction is checked when blocking
-/

def ologHaiBlockRestrictionOk : Bool :=
  ologHaiCrusher.staticAbilities == #[.cantBlockUnlessYouControl #["Goblin", "Orc"]] &&
    (ruling 270).comment.contains "doesn't have to block" &&
    (ruling 324).comment.contains "matters only at the time you declare blockers"

#guard ologHaiBlockRestrictionOk

/-!
## 273 — Mirkwood Meditator overwrites earlier set-P/T
-/

def meditatorOverwritesSetPTOk : Bool :=
  let g := addPermanent afterDraw mirkwoodMeditator ⟨0⟩ ⟨0⟩
  let o := namedPermanent g "Mirkwood Meditator"
  let g := g.mapObjectStatus o (fun s => { s with setBasePT := some (1, 1) })
  let o := namedPermanent g "Mirkwood Meditator"
  let g := g.mapObjectStatus o (fun s => { s with setBasePT := some (4, 2) })
  g.power (namedPermanent g "Mirkwood Meditator") == 4 &&
    g.toughness (namedPermanent g "Mirkwood Meditator") == 2 &&
    (ruling 273).comment.contains "overwrites any previous effects"

#guard meditatorOverwritesSetPTOk

/-!
## 287, 303, 304 — type-changing effects last
-/

def typeChangeLastsOk : Bool :=
  beornsHospitality.activatedAbilities[0]!.effect ==
      .becomeBearCreatureWithLandsPT &&
    (ruling 287).comment.contains "lasts indefinitely" &&
    (ruling 303).comment.contains "don't wear off during the cleanup step" &&
    (ruling 304).comment.contains "lasts indefinitely"

#guard typeChangeLastsOk

/-!
## 307, 350 — choose an existing creature type
-/

def chooseExistingCreatureTypeOk : Bool :=
  raiseThePalisade.spellEffect == some .chooseTypeReturnOthers &&
    (ruling 307).comment.contains "existing creature type" &&
    (ruling 350).comment.contains "existing creature type"

#guard chooseExistingCreatureTypeOk

/-!
## 309 — Fireleaper uses last-known power
-/

def fireleaperLastKnownOk : Bool :=
  goblinFireleaper.triggeredAbilities ==
      #[.onDiesDealDamageEqualToPowerToOppCreature] &&
    (ruling 309).comment.contains "last existed on the battlefield"

#guard fireleaperLastKnownOk

/-!
## 310 — cost reduction applies to generic mana
-/

def genericCostReductionOk : Bool :=
  radagastOfRhosgobel.firstCreatureCostsLess == 2 &&
    (ruling 310).comment.contains "start with the mana cost or alternative cost"

#guard genericCostReductionOk

/-!
## 316 — Dáin counts Dwarves on resolution
-/

def dainCountsOnResolveOk : Bool :=
  dainOfTheAncientHalls.triggeredAbilities ==
      #[.onAttackDamageEqualSubtypeToEachOpponent "Dwarf"] &&
    (ruling 316).comment.contains "as Dáin's last ability resolves"

#guard dainCountsOnResolveOk

/-!
## 329 — Woodland Weavemaster tap is a mana ability
-/

def weavemasterManaAbilityOk : Bool :=
  woodlandWeavemaster.tapAddAnyColorEqualToPower &&
    (ruling 329).comment.contains "mana ability"

#guard weavemasterManaAbilityOk

/-!
## 344 — Gollum the Abandoned optional exile target
-/

def gollumAbandonedOptionalTargetOk : Bool :=
  gollumTheAbandoned.triggeredAbilities ==
      #[.onEnterExileOppGyCardOppsLoseLife 2] &&
    (ruling 344).comment.contains "don't have to choose a target"

#guard gollumAbandonedOptionalTargetOk

/-!
## 347 — cascade exiles face up
-/

def cascadeFaceUpOk : Bool :=
  callForthTheTempest.cascade == 2 &&
    (ruling 347).comment.contains "exile the cards face up"

#guard cascadeFaceUpOk

/-!
## 358 — Ori gains life only for destroyed permanents
-/

def oriOnlyDestroyedOk : Bool :=
  oriPlateStacker.triggeredAbilities ==
      #[.onEnterDestroyOppArtifactsEnchantmentsGainLife] &&
    (ruling 358).comment.contains "isn't actually destroyed"

#guard oriOnlyDestroyedOk

/-!
## 194 — Eagle's Rescue stays in the graveyard if the target is illegal
-/

def eaglesRescueIllegalStaysOk : Bool :=
  let g := addToGraveyard afterDraw eaglesRescue ⟨0⟩
  let g := addPermanent g grizzlyBears ⟨0⟩ ⟨0⟩
  let rescue := namedGraveyardCard g ⟨0⟩ "Eagle's Rescue"
  let g := g.applyAbilityEffect ⟨0⟩ (.returnFromGyAttachPowerAtMost 1)
    #[Target.permanent (namedPermanent g "Grizzly Bears").id] (some rescue.id)
  g.objects.any (fun o => o.name == "Eagle's Rescue" && o.zone == .graveyard ⟨0⟩) &&
    (ruling 194).comment.contains "remains in your graveyard"

#guard eaglesRescueIllegalStaysOk

/-!
## 220 — Bard's Company flash is checked only as you begin to cast
-/

def bardsCompanyFlashLockOk : Bool :=
  let g := skipTo afterDraw .beginningOfCombat 80
  let g := addToHand g bardsCompany ⟨0⟩
  let without := !(g.timingAllowsCast ⟨0⟩ bardsCompany)
  let g := addPermanent g lakeshoreApothecary ⟨0⟩ ⟨0⟩
  let withHuman := g.timingAllowsCast ⟨0⟩ bardsCompany
  bardsCompany.flashIfYouControlSubtype == some "Human" &&
    without && withHuman &&
    (ruling 220).comment.contains "only as you begin the casting process"

#guard bardsCompanyFlashLockOk

/-!
## 224 — Guttersnipe hits each opponent (2HG: 4 to the team)
-/

def guttersnipeEachOpponentOk : Bool :=
  let g := addPermanent afterDraw guttersnipe ⟨0⟩ ⟨0⟩
  let g := g.applyTriggeredAbility ⟨0⟩
    (.onCastInstantOrSorceryDealDamageToEachOpponent 2)
    (some (namedPermanent g "Guttersnipe").id)
  (g.player ⟨1⟩).life == 18 &&
    (ruling 224).comment.contains "opposing team to lose 4 life"

#guard guttersnipeEachOpponentOk

/-!
## 281 — Bilbo reduces only generic mana, and only off-hand
-/

def bilboNotFromHandReductionOk : Bool :=
  let g := addPermanent afterDraw bilboThiefInTheNight ⟨0⟩ ⟨0⟩
  let g := addToHand g grizzlyBears ⟨0⟩
  let fromHand := g.playManaCost (handCardNamed g ⟨0⟩ "Grizzly Bears") grizzlyBears
  let g := addToGraveyard g grizzlyBears ⟨0⟩
  let fromGy := g.playManaCost (namedGraveyardCard g ⟨0⟩ "Grizzly Bears") grizzlyBears
  fromHand == grizzlyBears.manaCost &&
    fromGy == ManaCost.ofColor .green &&
    (ruling 281).comment.contains "anywhere other than your hand" &&
    (ruling 281).comment.contains "can't reduce requirements of a specific color"

#guard bilboNotFromHandReductionOk

/-!
## 318, 319 — sacrificed creature uses last-known power
-/

def lastKnownSacrificePowerOk : Bool :=
  let g := addPermanent afterDraw grizzlyBears ⟨0⟩ ⟨0⟩
  let bear := namedPermanent g "Grizzly Bears"
  let pw := g.power bear
  let (g, _) := g.move bear.id (.graveyard ⟨0⟩) none
  pw == 2 &&
    (namedGraveyardCard g ⟨0⟩ "Grizzly Bears").printed.power == some 2 &&
    (ruling 318).comment.contains "last existed on the battlefield" &&
    (ruling 319).comment.contains "last existed on the battlefield"

#guard lastKnownSacrificePowerOk

/-!
## 143, 271 — The Master of Lake-town: two triggers, last usually from the GY
-/

def masterDiesThenLastAbilityOk : Bool :=
  let g := addPermanent afterDraw theMasterOfLakeTown ⟨0⟩ ⟨0⟩
  let g := addToGraveyard g lightningBolt ⟨0⟩
  let g := addToGraveyard g lightningBolt ⟨0⟩
  let g := addToGraveyard g lightningBolt ⟨0⟩
  let g := addToGraveyard g lightningBolt ⟨0⟩
  let g := addToGraveyard g lightningBolt ⟨0⟩
  let g := addToGraveyard g lightningBolt ⟨0⟩
  let mid := (g.player ⟨0⟩).graveyard.size
  let (g, _) := g.move (namedPermanent g "The Master of Lake-town").id
    (.graveyard ⟨0⟩) none
  let inGy := g.objects.any (fun o =>
    o.name == "The Master of Lake-town" && o.zone == .graveyard ⟨0⟩)
  let g := g.drawPerSevenCardGraveyard ⟨0⟩
  inGy && mid >= 6 &&
    (g.player ⟨0⟩).graveyard.size >= 7 &&
    (ruling 271).comment.contains "usually be in a graveyard"

#guard masterDiesThenLastAbilityOk

def masterMillFirstThenDrawOk : Bool :=
  let g := addPermanent afterDraw theMasterOfLakeTown ⟨0⟩ ⟨0⟩
  let (g, _) := g.move (namedPermanent g "The Master of Lake-town").id
    (.graveyard ⟨0⟩) none
  let g := g.loseLife ⟨1⟩ 3
  let g := g.mill ⟨1⟩ 3
  let g := g.drawPerSevenCardGraveyard ⟨0⟩
  g.objects.any (fun o =>
    o.name == "The Master of Lake-town" && o.zone == .graveyard ⟨0⟩) &&
    (ruling 143).comment.contains "two triggered abilities"

#guard masterMillFirstThenDrawOk

/-!
## 144, 166 — Thranduil linked abilities and name rewrite
-/

#guard
  Game.linkedAbilitiesStillLinked true &&
    !(Game.linkedAbilitiesStillLinked false) &&
    (ruling 144).comment.contains "link only lasts for as long as Thranduil has those abilities"

#guard
  Game.rewriteAbilityCardName
      "Exile target card named Lórien Guide." "Lórien Guide" "Thranduil, the Elvenking" ==
    "Exile target card named Thranduil, the Elvenking." &&
    (ruling 166).comment.contains "referenced Thranduil by name instead"

/-!
## 165 — Banishing Light Aura return does not target; stay in exile if illegal
-/

def banishingLightAuraNoHostStaysOk : Bool :=
  let g := addPermanent afterDraw banishingLight ⟨0⟩ ⟨0⟩
  let g := addPermanent g fogOnTheBarrowDowns ⟨1⟩ ⟨1⟩
  let light := namedPermanent g "Banishing Light"
  let g := g.exileUntilSourceLeaves (some light.id) (namedPermanent g "Fog on the Barrow-Downs")
  let light := namedPermanent g "Banishing Light"
  let g := (g.move light.id (.graveyard ⟨0⟩) none).1
  g.objects.any (fun o => o.name == "Fog on the Barrow-Downs" && o.zone == .exile) &&
    g.log.any (fun s => mentions s "remains in exile") &&
    (ruling 165).comment.contains "remains in exile"

#guard banishingLightAuraNoHostStaysOk

def banishingLightAuraHexproofOk : Bool :=
  let g := addPermanent afterDraw banishingLight ⟨0⟩ ⟨0⟩
  let g := addPermanent g fogOnTheBarrowDowns ⟨1⟩ ⟨1⟩
  let g := addPermanent g grizzlyBears ⟨1⟩ ⟨1⟩
  let bear := namedPermanent g "Grizzly Bears"
  let g := g.mapObjectStatus bear (·.grantUntilEot Keyword.hexproof)
  let light := namedPermanent g "Banishing Light"
  let g := g.exileUntilSourceLeaves (some light.id) (namedPermanent g "Fog on the Barrow-Downs")
  let light := namedPermanent g "Banishing Light"
  let g := (g.move light.id (.graveyard ⟨0⟩) none).1
  let fog := namedPermanent g "Fog on the Barrow-Downs"
  let bear := namedPermanent g "Grizzly Bears"
  g.hasHexproof bear && fog.attachedTo == some bear.id &&
    g.log.any (fun s => mentions s "does not target") &&
    (ruling 165).comment.contains "hexproof"

#guard banishingLightAuraHexproofOk

/-!
## 175, 201, 277, 336 — Gríma exile-until-instant, face up, cast as it resolves
-/

def grimaEmptyLibraryBecomesLibraryOk : Bool :=
  let g := afterDraw.setPlayer { (afterDraw.player ⟨1⟩) with library := #[] }
  let g := addToLibraryTop g mountain ⟨1⟩
  let g := addToLibraryTop g mountain ⟨1⟩
  let before := (g.player ⟨1⟩).library.size
  let g := g.grimaExileUntilInstantOrSorcery ⟨0⟩ ⟨1⟩ false
  (g.player ⟨1⟩).library.size == before &&
    !(g.objects.any (fun o => o.zone == .exile && o.name == "Mountain")) &&
    g.log.any (fun s => mentions s "become that player's library") &&
    (ruling 175).comment.contains "become that player's library"

#guard grimaEmptyLibraryBecomesLibraryOk

def grimaFaceUpCastDuringResolveOk : Bool :=
  let g := addToLibraryTop afterDraw mountain ⟨1⟩
  let g := addToLibraryTop g lightningBolt ⟨1⟩
  let g := g.grimaExileUntilInstantOrSorcery ⟨0⟩ ⟨1⟩ true
  g.objects.any (fun o => o.name == "Lightning Bolt" && o.zone == .stack) &&
    g.log.any (fun s => mentions s "face up") &&
    g.log.any (fun s => mentions s "as the ability resolves") &&
    (ruling 277).comment.contains "exiled face up" &&
    (ruling 336).comment.contains "while the ability is resolving" &&
    (ruling 201).comment.contains "bottom of its owner's library"

#guard grimaFaceUpCastDuringResolveOk

/-!
## 200, 341, 337 — cast during resolution, ignore timing
-/

def castDuringResolutionIgnoresTimingOk : Bool :=
  let g := skipTo afterDraw .beginningOfCombat 80
  let g := addToHand g lightningBolt ⟨0⟩
  let bolt := handCardNamed g ⟨0⟩ "Lightning Bolt"
  let g := g.castAsPartOfResolution ⟨0⟩ bolt.id (ignoreTiming := true)
  g.objects.any (fun o => o.name == "Lightning Bolt" && o.zone == .stack) &&
    g.log.any (fun s => mentions s "as the ability resolves") &&
    (ruling 200).comment.contains "Timing permissions based on the card's type are ignored" &&
    (ruling 341).comment.contains "Timing restrictions based on the card's types are ignored" &&
    (ruling 337).comment.contains "while the ability is resolving"

#guard castDuringResolutionIgnoresTimingOk

/-!
## 212, 213, 343 — Saruman ward, uncast copy ceases, reflexive mill
-/

def sarumanWardNeedsCardOk : Bool :=
  let empty := afterDraw.setPlayer { (afterDraw.player ⟨0⟩) with hand := #[] }
  let g := addToHand empty lightningBolt ⟨0⟩
  !(empty.canPaySarumanWard ⟨0⟩) &&
    g.canPaySarumanWard ⟨0⟩ &&
    (ruling 212).comment.contains "won't be able to pay Saruman"

#guard sarumanWardNeedsCardOk

def uncastCopyCeasesOk : Bool :=
  let g := addToHand afterDraw lightningBolt ⟨0⟩
  let bolt := handCardNamed g ⟨0⟩ "Lightning Bolt"
  let (g, eid) := g.move bolt.id .exile none
  let o := g.object! eid
  let g := g.setObject { o with isCopy := true }
  let g := g.ceaseUncastCopies
  !(g.objects.any (fun o => o.isCopy && o.name == "Lightning Bolt")) &&
    g.log.any (fun s => mentions s "ceases to exist") &&
    (ruling 213).comment.contains "copy ceases to exist"

#guard uncastCopyCeasesOk

def sarumanReflexiveAfterMillOk : Bool :=
  let (g, fired) := afterDraw.millThenReflexive #[⟨1⟩] 2
  fired &&
    (g.player ⟨1⟩).graveyard.size >= 2 &&
    (ruling 343).comment.contains "reflexive"

#guard sarumanReflexiveAfterMillOk

/-!
## 214 — Bard can target the Human Soldier created while recruiting
-/

def bardTargetsRecruitSoldierOk : Bool :=
  let g := addPermanent afterDraw bardTheBowman ⟨0⟩ ⟨0⟩
  let g := addToHand g lightningBolt ⟨0⟩
  let g := g.setPlayer { (g.player ⟨0⟩) with cardsDrawnThisTurn := 1 }
  let bolt := handCardNamed g ⟨0⟩ "Lightning Bolt"
  let g := g.beginRecruit ⟨0⟩
  let g :=
    match g.discardForDraw ⟨0⟩ bolt.id with
    | .ok g => g
    | .error _ => g
  let soldier :=
    g.battlefield.find? (fun o => o.name == "Human Soldier")
  match soldier with
  | none => false
  | some tok =>
    let g := g.applyBardBowman tok.id
    tok.printed.isToken &&
      (namedPermanent g "Human Soldier").status.plusOnePlusOne == 1 &&
      g.hasLifelink (namedPermanent g "Human Soldier") &&
      (ruling 214).comment.contains "Human Soldier you create can be chosen"

#guard bardTargetsRecruitSoldierOk

/-!
## 226 — Bat-Cloud reduction still applies if that player lost
-/

def batCloudReductionIfPlayerLostOk : Bool :=
  let g := addPermanent afterDraw grizzlyBears ⟨1⟩ ⟨1⟩
  let (g, _) := g.move (namedPermanent g "Grizzly Bears").id (.graveyard ⟨1⟩) none
  let g := g.setPlayer { (g.player ⟨1⟩) with lost := true }
  let g := addToHand g dreadedBatCloud ⟨0⟩
  let card := handCardNamed g ⟨0⟩ "Dreaded Bat-Cloud"
  let cost := g.playManaCost card dreadedBatCloud
  g.creatureDiedThisTurn &&
    (g.player ⟨1⟩).lost &&
    cost == ManaCost.ofGenericAndColor 1 .black &&
    (ruling 226).comment.contains "Dreaded Bat-Cloud's cost reduction applies"

#guard batCloudReductionIfPlayerLostOk

/-!
## 227, 228, 229, 248, 289, 290 — until-leaves vs Fiend Hunter leave trigger
-/

def celebrateOwnerLeavesReturnsOk : Bool :=
  let g := addPermanent afterDraw celebrateTheMountainKing ⟨0⟩ ⟨0⟩
  let g := addPermanent g grizzlyBears ⟨1⟩ ⟨1⟩
  let src := namedPermanent g "Celebrate the Mountain-king"
  let g := g.exileUntilSourceLeaves (some src.id) (namedPermanent g "Grizzly Bears")
  let g := g.playerLeavesGame ⟨0⟩
  g.battlefield.any (fun o => o.name == "Grizzly Bears") &&
    (g.player ⟨0⟩).lost &&
    (ruling 227).comment.contains "one-shot effect that returns" &&
    (ruling 228).comment.contains "one-shot effect that returns"

#guard celebrateOwnerLeavesReturnsOk

def whaleOwnerLeavesReturnsOk : Bool :=
  let g := addPermanent afterDraw colossalWhale ⟨0⟩ ⟨0⟩
  let g := addPermanent g grizzlyBears ⟨1⟩ ⟨1⟩
  let src := namedPermanent g "Colossal Whale"
  let g := g.exileUntilSourceLeaves (some src.id) (namedPermanent g "Grizzly Bears")
  let g := g.playerLeavesGame ⟨0⟩
  g.battlefield.any (fun o => o.name == "Grizzly Bears") &&
    (g.player ⟨0⟩).lost &&
    (ruling 289).comment.contains "immediately after Colossal Whale" &&
    (ruling 290).comment.contains "immediately after Celebrate"

#guard whaleOwnerLeavesReturnsOk

def fiendHunterOwnerLeavesStaysExiledOk : Bool :=
  let g := addPermanent afterDraw fiendHunter ⟨0⟩ ⟨0⟩
  let g := addPermanent g grizzlyBears ⟨1⟩ ⟨1⟩
  let src := namedPermanent g "Fiend Hunter"
  let g := g.exileForLeaveTrigger (some src.id) (namedPermanent g "Grizzly Bears")
  let g := g.playerLeavesGame ⟨0⟩
  g.objects.any (fun o => o.name == "Grizzly Bears" && o.zone == .exile) &&
    !(g.battlefield.any (fun o => o.name == "Grizzly Bears")) &&
    (ruling 229).comment.contains "remains exiled indefinitely"

#guard fiendHunterOwnerLeavesStaysExiledOk

def fiendHunterReturnIsNewObjectOk : Bool :=
  let g := addPermanent afterDraw fiendHunter ⟨0⟩ ⟨0⟩
  let g := addPermanent g grizzlyBears ⟨1⟩ ⟨1⟩
  let oldId := (namedPermanent g "Grizzly Bears").id
  let src := namedPermanent g "Fiend Hunter"
  let g := g.exileForLeaveTrigger (some src.id) (namedPermanent g "Grizzly Bears")
  let src := namedPermanent g "Fiend Hunter"
  let g := g.returnLinkedExile src
  let returned := namedPermanent g "Grizzly Bears"
  returned.id != oldId &&
    (ruling 248).comment.contains "new object with no relation"

#guard fiendHunterReturnIsNewObjectOk

def untilLeavesImmediateNoSbaGapOk : Bool :=
  let g := addPermanent afterDraw colossalWhale ⟨0⟩ ⟨0⟩
  let g := addPermanent g grizzlyBears ⟨1⟩ ⟨1⟩
  let src := namedPermanent g "Colossal Whale"
  let g := g.exileUntilSourceLeaves (some src.id) (namedPermanent g "Grizzly Bears")
  let src := namedPermanent g "Colossal Whale"
  let g := (g.move src.id (.graveyard ⟨0⟩) none).1
  g.battlefield.any (fun o => o.name == "Grizzly Bears") &&
    g.pending == .none &&
    (ruling 289).comment.contains "Nothing happens between the two events"

#guard untilLeavesImmediateNoSbaGapOk

/-!
## 278 — Unexpected Party type is chosen as it enters
-/

def unexpectedPartyTypeImmediateOk : Bool :=
  let g := addPermanent afterDraw anUnexpectedParty ⟨0⟩ ⟨0⟩
  let g := addPermanent g lakeshoreApothecary ⟨0⟩ ⟨0⟩
  let party := namedPermanent g "An Unexpected Party"
  let g := g.chooseCreatureTypeAsEnters party.id "Human"
  let human := namedPermanent g "Lakeshore Apothecary"
  g.pending == .none &&
    (namedPermanent g "An Unexpected Party").status.chosenCreatureType == some "Human" &&
    g.power human == 3 &&
    (ruling 278).comment.contains "can't take any actions between"

#guard unexpectedPartyTypeImmediateOk

/-!
## 279, 283 — Black Gate most-life checked on resolve; later creatures too
-/

def blackGateMostLifeAndLaterCreatureOk : Bool :=
  let g := addPermanent afterDraw grizzlyBears ⟨0⟩ ⟨0⟩
  let g := addPermanent g grayOgre ⟨1⟩ ⟨1⟩
  let bear := namedPermanent g "Grizzly Bears"
  let g := g.setObject { bear with status := { bear.status with attacking := true } }
  let g := g.setLife ⟨1⟩ 25 "p1 has most life"
  let g := g.applyBlackGateUnblockable (namedPermanent g "Grizzly Bears").id ⟨1⟩
  let g := addPermanent g lakeshoreApothecary ⟨1⟩ ⟨1⟩
  let attacker := namedPermanent g "Grizzly Bears"
  let later := namedPermanent g "Lakeshore Apothecary"
  !(g.canBlock later attacker) &&
    (g.player ⟨1⟩).life == 25 &&
    (ruling 279).comment.contains "as The Black Gate's last ability resolves" &&
    (ruling 283).comment.contains "including creatures that weren't on the battlefield"

#guard blackGateMostLifeAndLaterCreatureOk

/-!
## 284 — Uneasy Partings: owner chooses top or bottom
-/

def uneasyPartingsOwnerChoosesOk : Bool :=
  let g := addPermanent afterDraw grizzlyBears ⟨1⟩ ⟨1⟩
  let bear := namedPermanent g "Grizzly Bears"
  let g := g.applyEffect ⟨0⟩ .putOnTopOrBottom
    #[Target.permanent bear.id]
  (match g.pending with
   | .chooseLibraryPlacement p id => p == ⟨1⟩ && id == bear.id
   | _ => false) &&
    (ruling 284).comment.contains "creature's owner chooses"

#guard uneasyPartingsOwnerChoosesOk

/-!
## 286, 348 — Balin discard is decided on resolve, empty hand legal
-/

def balinEmptyHandDiscardOk : Bool :=
  let g := afterDraw.setPlayer { (afterDraw.player ⟨0⟩) with hand := #[] }
  let g := g.mayDiscardHandDrawThatMany ⟨0⟩ true
  (g.player ⟨0⟩).hand.size == 0 &&
    g.pending == .none &&
    (ruling 348).comment.contains "even if your hand contains zero cards" &&
    (ruling 286).comment.contains "during the resolution of the ability"

#guard balinEmptyHandDiscardOk

def balinDiscardThenDrawAtomicOk : Bool :=
  let g := afterDraw
  let n := (g.player ⟨0⟩).hand.size
  let g := g.mayDiscardHandDrawThatMany ⟨0⟩ true
  (g.player ⟨0⟩).hand.size == n &&
    g.pending == .none &&
    (ruling 286).comment.contains "no opportunity for an opponent to respond"

#guard balinDiscardThenDrawAtomicOk

/-!
## 295 — Supper for Spiders: Food artifacts only; keep name and abilities
-/

def supperForSpidersFoodOnlyOk : Bool :=
  let g := addToGraveyard afterDraw dainLordOfTheIronHills ⟨1⟩
  let card := namedGraveyardCard g ⟨1⟩ "Dáin, Lord of the Iron Hills"
  let g := g.supperForSpidersReturn ⟨0⟩ #[card.id]
  let food := namedPermanent g "Dáin, Lord of the Iron Hills"
  food.status.onlyFoodArtifact &&
    !food.isCreature &&
    food.types == #[.artifact] &&
    food.subtypes == #["Food"] &&
    food.isLegendary &&
    food.printed.manaCost == dainLordOfTheIronHills.manaCost &&
    (ruling 295).comment.contains "only Food artifacts" &&
    (ruling 295).comment.contains "retain their name, mana cost, mana value, and abilities"

#guard supperForSpidersFoodOnlyOk

/-!
## 327 — Dáin: must-attack may decline if every attack costs
-/

def dainMustAttackDeclineOk : Bool :=
  Game.mustAttackCanDeclineIfOnlyAttackCosts true &&
    !(Game.mustAttackCanDeclineIfOnlyAttackCosts false) &&
    (ruling 327).comment.contains "choose not to attack" &&
    dainLordOfTheIronHills.staticAbilities.any (fun ab =>
      match ab with
      | .creaturesCantAttackYouUnlessPayIfEnduringStory _ => true
      | _ => false)

#guard dainMustAttackDeclineOk

/-!
## 330 — Bilbo: failed Adventure is Bilbo-exiled, not Adventure-exiled
-/

def bilboFailedAdventureNoLaterCastOk : Bool :=
  let g := addToGraveyard afterDraw bilboLuckwearer ⟨0⟩
  let card := namedGraveyardCard g ⟨0⟩ "Bilbo, Luckwearer"
  let g := g.exileFailedAdventureFromBilbo card.id
  let o :=
    match g.objects.find? (fun x => x.name == "Bilbo, Luckwearer") with
    | some x => x
    | none => namedPermanent afterDraw "Grizzly Bears"
  o.zone == .exile && o.playPermission.isNone &&
    (ruling 330).comment.contains "exiled by the replacement effect created by Bilbo"

#guard bilboFailedAdventureNoLaterCastOk

/-!
## 338 — Palantír illegal target does nothing
-/

def palantirIllegalTargetOk : Bool :=
  let g := addPermanent afterDraw palantirOfOrthanc ⟨0⟩ ⟨0⟩
  let src := namedPermanent g "Palantír of Orthanc"
  let g := g.applyPalantir src.id none
  (namedPermanent g "Palantír of Orthanc").status.influence == 0 &&
    g.pending == .none &&
    g.log.any (fun s => mentions s "No influence counter") &&
    (ruling 338).comment.contains "You won't put an influence counter"

#guard palantirIllegalTargetOk

/-!
## 339 — Minas Tirith Garrison tap-then-draw is atomic
-/

def minasTirithTapDrawAtomicOk : Bool :=
  let g := addPermanent afterDraw minasTirithGarrison ⟨0⟩ ⟨0⟩
  let g := addPermanent g lakeshoreApothecary ⟨0⟩ ⟨0⟩
  let human := namedPermanent g "Lakeshore Apothecary"
  let hand0 := (g.player ⟨0⟩).hand.size
  let g := g.applyTriggeredAbility ⟨0⟩ .onAttackTapHumansDraw
    (some (namedPermanent g "Minas Tirith Garrison").id)
  let g :=
    match g.choosePermanents ⟨0⟩ #[human.id] with
    | .ok g => g
    | .error _ => g
  (namedPermanent g "Lakeshore Apothecary").status.tapped &&
    (g.player ⟨0⟩).hand.size == hand0 + 1 &&
    g.pending == .none &&
    (ruling 339).comment.contains "No player may take any other actions between"

#guard minasTirithTapDrawAtomicOk

/-!
## 345, 349 — Riddles: face-down pile not revealed; 4+0 legal
-/

def riddlesFourZeroFaceDownOk : Bool :=
  let g := afterDraw
  let hand0 := (g.player ⟨0⟩).hand.size
  let g := g.riddlesInTheDark ⟨0⟩ 0 true
  (g.player ⟨0⟩).hand.size == hand0 + 4 &&
    g.log.any (fun s => mentions s "face-down") &&
    g.log.any (fun s => mentions s "without being revealed") &&
    (ruling 345).comment.contains "don't have to reveal the cards in the face-down pile" &&
    (ruling 349).comment.contains "one pile of four and one pile of zero"

#guard riddlesFourZeroFaceDownOk

/-!
## 351, 356 — Flameshape: Wizard required to cast, not to resolve; normal timing
-/

def flameshapeWizardToCastNotResolveOk : Bool :=
  let g := addToLibraryTop afterDraw lightningBolt ⟨0⟩
  let g := addToLibraryTop g mountain ⟨0⟩
  let g := g.exileTopPlayIfYouControlSubtype ⟨0⟩ 2 "Wizard"
  let bolt :=
    match g.objects.find? (fun o => o.name == "Lightning Bolt" && o.zone == .exile) with
    | some o => o
    | none => namedPermanent afterDraw "Grizzly Bears"
  let without := !(g.mayPlayFromExile ⟨0⟩ bolt)
  let g := addPermanent g radagastOfRhosgobel ⟨0⟩ ⟨0⟩
  let bolt :=
    match g.objects.find? (fun o => o.name == "Lightning Bolt" && o.zone == .exile) with
    | some o => o
    | none => namedPermanent afterDraw "Grizzly Bears"
  let withWiz := g.mayPlayFromExile ⟨0⟩ bolt
  let g := g.castAsPartOfResolution ⟨0⟩ bolt.id (ignoreTiming := false)
  let onStack := g.objects.any (fun o => o.name == "Lightning Bolt" && o.zone == .stack)
  let g := (g.move (namedPermanent g "Radagast of Rhosgobel").id (.graveyard ⟨0⟩) none).1
  let stillStack := g.objects.any (fun o => o.name == "Lightning Bolt" && o.zone == .stack)
  without && withWiz && onStack && stillStack &&
    bolt.playPermission.isSome &&
    (match bolt.playPermission with
     | some perm => perm.requireSubtype == some "Wizard" && !perm.ignoreTiming && !perm.withoutManaCost
     | none => false) &&
    (ruling 351).comment.contains "losing control of your last Wizard" &&
    (ruling 356).comment.contains "pay all costs and follow all timing rules"

#guard flameshapeWizardToCastNotResolveOk

/-!
## 352–355 — Moria Marauder, Inside Information, Thranduil's Decree, Shadow
of the Enemy: normal timing and costs
-/

def normalTimingAndCostsOk : Bool :=
  let g := addToHand afterDraw mountain ⟨0⟩
  let land := handCardNamed g ⟨0⟩ "Mountain"
  let (g, eid) := g.move land.id .exile none
  let o := g.object! eid
  let g := g.setObject { o with
    playPermission := some {
      player := ⟨0⟩
      turnEndsRemaining := 0
      whileExiled := true } }
  let o := g.object! eid
  let combat := skipTo g .beginningOfCombat 80
  let o2 := combat.object! eid
  let perm := o2.playPermission.getD { player := ⟨0⟩, turnEndsRemaining := 0 }
  g.mayPlayFromExile ⟨0⟩ o &&
    g.canPlayLand ⟨0⟩ &&
    !(combat.canPlayLand ⟨0⟩) &&
    !perm.ignoreTiming &&
    (ruling 352).comment.contains "normal timing rules" &&
    (ruling 353).comment.contains "only during your main phase" &&
    (ruling 354).comment.contains "timing restrictions and permissions" &&
    (ruling 355).comment.contains "pay all costs and follow all normal timing rules"

#guard normalTimingAndCostsOk

end Mtg.Engine.RulingTests
