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

#guard
  let army := namedPermanent amassFresh "Goblin Army"
  army.printed.isToken && amassFresh.hasSubtype army "Goblin" &&
    amassFresh.hasSubtype army "Army" && army.status.plusOnePlusOne == 2 &&
    amassFresh.power army == 2 && amassFresh.toughness army == 2 &&
    amassFresh.log.any (fun s => mentions s "amassed Army") &&
    amassFresh.log.any (fun s => mentions s "entered as a 0/0 creature")

/-- Ruling 1: later amass still names the same creature as the amassed Army. -/
def amassAgain : Game := amassFresh.amassGoblins ⟨0⟩ 1

#guard
  (amassAgain.battlefield.filter (fun o => o.name == "Goblin Army")).size == 1 &&
    (namedPermanent amassAgain "Goblin Army").status.plusOnePlusOne == 3 &&
    amassAgain.log.any (fun s => mentions s "Goblin Army is the amassed Army")

/-- Ruling 14 / 61: amass Orcs creates an Orc Army; combining with Goblins
makes a Goblin Orc Army. -/
def amassOrcThenGoblin : Game :=
  (started.amassOrcs ⟨0⟩ 1).amassGoblins ⟨0⟩ 1

#guard
  let army := namedPermanent amassOrcThenGoblin "Orc Army"
  amassOrcThenGoblin.hasSubtype army "Orc" &&
    amassOrcThenGoblin.hasSubtype army "Goblin" &&
    amassOrcThenGoblin.hasSubtype army "Army" &&
    army.status.plusOnePlusOne == 2 &&
    (amassOrcThenGoblin.battlefield.filter (fun o =>
      amassOrcThenGoblin.hasSubtype o "Army")).size == 1

/-- Ruling 40 / 41: amass Zombies is the same action with a Zombie Army. -/
def amassZombieThenOrc : Game :=
  (started.amassZombies ⟨0⟩ 1).amassOrcs ⟨0⟩ 1

#guard
  let army := namedPermanent amassZombieThenOrc "Zombie Army"
  amassZombieThenOrc.hasSubtype army "Zombie" &&
    amassZombieThenOrc.hasSubtype army "Orc" &&
    army.status.plusOnePlusOne == 2

/-- Ruling 15 / 51: Mentor of the Meek sees the token enter as 0/0, even
when later counters would put it above 2 power. -/
def amassMentorSeesZero : Game :=
  let g := addPermanent started mentorOfTheMeek ⟨0⟩ ⟨0⟩
  let g := g.amassGoblins ⟨0⟩ 3
  g.receivePriority ⟨0⟩

#guard
  let army := namedPermanent amassMentorSeesZero "Goblin Army"
  army.status.plusOnePlusOne == 3 && amassMentorSeesZero.power army == 3 &&
    amassMentorSeesZero.stack.any (fun e =>
      (amassMentorSeesZero.object! e.objectId).triggeredAbility ==
        some (.onAnotherCreatureYouControlPowerAtMostEntersMayPayDraw 2 1))

/-- A 3-power creature entering after counters would not trigger Mentor. -/
#guard
  let g := addPermanent started mentorOfTheMeek ⟨0⟩ ⟨0⟩
  let g := addPermanent g hillGiant ⟨0⟩ ⟨0⟩
  let mentor := namedPermanent g "Mentor of the Meek"
  let giant := namedPermanent g "Hill Giant"
  let g := g.putMatchingSourceTriggers ⟨0⟩ mentor .anotherCreatureYouControlEnters
    (cause := some giant)
  (g.receivePriority ⟨0⟩).stack.isEmpty

/-- Ruling 16 / 52: with several Armies, the newest is the amassed Army. -/
def twoArmiesThenAmass : Game :=
  let (g, _) := started.createToken ⟨0⟩ goblinArmyToken
  let (g, _) := g.createToken ⟨0⟩ orcArmyToken
  g.amassGoblins ⟨0⟩ 1

#guard
  let g := twoArmiesThenAmass
  let orc := namedPermanent g "Orc Army"
  orc.status.plusOnePlusOne == 1 && g.hasSubtype orc "Goblin" &&
    (namedPermanent g "Goblin Army").status.plusOnePlusOne == 0

/-- Ruling 18: untargeted amass still creates the Army. Targeting-fizzle
(rulings 17 / 53) is the same CR 608.2b path used by other targeted spells. -/
#guard
  let g := started.applyEffect ⟨0⟩ (.amassGoblins 1) #[]
  g.battlefield.any (fun o => g.hasSubtype o "Army")

/-!
## 2–13 — Adventure
-/

/-- Ruling 2: in every zone except the stack-as-Adventure, ignore the
Adventure face. Bilbo in a graveyard is a blue creature of mana value 2. -/
#guard
  let adv := bilboLuckwearer.adventure.get!
  bilboLuckwearer.isCreature && !bilboLuckwearer.isInstant &&
    !bilboLuckwearer.isSorcery && bilboLuckwearer.manaValue == 2 &&
    adv.name == "Burglar's Plot" && adv.manaCost.manaValue == 5

/-- Ruling 3: “has an Adventure” looks at the adventurer card’s alternative
characteristics even when they are not in use. -/
#guard
  let g := addPermanent started bilboLuckwearer ⟨0⟩ ⟨0⟩
  let o := namedPermanent g "Bilbo, Luckwearer"
  o.printed.adventure.isSome && !o.isAdventureSpell && o.printed.isCreature

/-- Ruling 12 / 9: a spell cast as an Adventure uses only the alternative
characteristics. On the stack it is not a card that “has an Adventure”. -/
#guard
  let spell := paidSpewFlame.object! paidSpewFlame.stack.back!.objectId
  spell.name == "Spew Flame" && spell.printed.isSorcery &&
    spell.isAdventureSpell && spell.printed.adventure.isNone &&
    spell.printed.manaCost.manaValue == 5

/-- Ruling 5 / 13: a resolving Adventure is exiled and may be cast as the
permanent later, only when timing allows. -/
#guard
  resolvedSpewFlame.objects.any (fun o =>
    o.zone == .exile && o.name == "Smaug, the Great Calamity") &&
    resolvedSpewFlame.mayPlayFromExile ⟨0⟩ (exiledSmaug resolvedSpewFlame) &&
    !resolvedSpewFlame.canCastAdventure ⟨0⟩ (exiledSmaug resolvedSpewFlame) &&
    resolvedSpewFlame.adventureExileForbidsRecast (exiledSmaug resolvedSpewFlame)

/-- Ruling 6: exile for any other reason does not grant the Adventure
cast-as-permanent permission. -/
#guard
  let g := addToHand started smaugTheGreatCalamity ⟨0⟩
  let id := (handCardNamed g ⟨0⟩ "Smaug, the Great Calamity").id
  let (g, _) := g.move id .exile none
  let o :=
    match g.objects.find? (fun x => x.zone == .exile &&
        x.name == "Smaug, the Great Calamity") with
    | some x => x
    | none => panic! "expected Smaug in exile"
  !g.mayPlayFromExile ⟨0⟩ o

/-- Ruling 4 / 11: casting as an Adventure is not an alternative cost on the
creature; legality uses the Adventure face. Spew Flame is a sorcery. -/
#guard
  let adv := smaugTheGreatCalamity.adventure.get!
  adv.types.contains .sorcery &&
    smaugSetup.canCastAdventure ⟨0⟩
      (handCardNamed smaugSetup ⟨0⟩ "Smaug, the Great Calamity") &&
    smaugSetup.asSorcery? ⟨0⟩

/-!
## 19–21 — landfall
-/

/-- Ruling 19: a nonland entering does not trigger landfall. -/
#guard
  let g := addPermanent afterDraw attercop ⟨0⟩ ⟨0⟩
  let g := addPermanent g grizzlyBears ⟨0⟩ ⟨0⟩
  let g := g.afterPermanentEnters (namedPermanent g "Grizzly Bears")
  !(g.log.any (fun s => mentions s "landfall"))

/-- Ruling 20: playing a land triggers landfall. -/
#guard
  hospitalityLandPlayed.log.any (fun s => mentions s "landfall trigger is put on the stack") &&
    hospitalityLandPlayed.stack.size == 1

/-- Ruling 20: a spell that puts a land onto the battlefield also triggers
landfall (Wood Elves + Attercop). -/
#guard
  attercopWoodElvesResolved.log.any (fun s => mentions s "landfall trigger is put on the stack")

/-- Ruling 21: each landfall ability of permanents you control triggers. -/
def twoLandfall : Game :=
  let g := addPermanent afterDraw attercop ⟨0⟩ ⟨0⟩
  let g := addPermanent g beornsHospitality ⟨0⟩ ⟨0⟩
  let g := addToHand g forest ⟨0⟩
  mustApply g ⟨0⟩ (.playLand (handCardNamed g ⟨0⟩ "Forest").id)

#guard
  twoLandfall.stack.size == 2 &&
    twoLandfall.stack.any (fun e =>
      (twoLandfall.object! e.objectId).triggeredAbility ==
        some .onLandYouControlEntersGets1) &&
    twoLandfall.stack.any (fun e =>
      (twoLandfall.object! e.objectId).triggeredAbility ==
        some .onLandYouControlEntersPlusOnePlusOne)

/-- Ruling 19 / 20: an opponent's land does not trigger your landfall. -/
#guard !(nissaLandVsAttercop.log.any (fun s => mentions s "landfall"))

/-!
## 22, 24–28 — Storied / enduring story
-/

/-- Ruling 22: tokens and lands are permanents; a spell on the stack is not. -/
#guard
  let g := addUntappedLand started mountain
  let (g, tok) := g.createToken ⟨0⟩ treasureToken
  let land := namedPermanent g "Mountain"
  land.isOnBattlefield && tok.isOnBattlefield &&
    !paidSpewFlame.stack.isEmpty &&
    !(paidSpewFlame.object! paidSpewFlame.stack.back!.objectId).isOnBattlefield

/-- Ruling 24: a legendary artifact counts once, not once per quality. -/
#guard
  let g := addPermanent started stingBilboSSword ⟨0⟩ ⟨0⟩
  let o := namedPermanent g "Sting, Bilbo's Sword"
  o.isLegendary && o.printed.isArtifact && g.countsTowardStoried o &&
    g.storiedPermanentCount ⟨0⟩ == 1

/-- Ruling 24: legendary artifact + Saga is two permanents, not three. -/
#guard
  let g := addPermanent (addPermanent started stingBilboSSword ⟨0⟩ ⟨0⟩)
    downInTheValley ⟨0⟩ ⟨0⟩
  g.storiedPermanentCount ⟨0⟩ == 2 && !g.hasEnduringStory ⟨0⟩

/-- Ruling 25: three artifacts without a storied permanent grant nothing. -/
#guard
  let g := started.createTreasureTokens ⟨0⟩ 3
  g.storiedPermanentCount ⟨0⟩ == 3 && !g.controlsStoried ⟨0⟩ &&
    !g.hasEnduringStory ⟨0⟩

/-- Ruling 25: losing two of those artifacts and then adding Thorin still
does not grant an enduring story (only two counting permanents). -/
#guard
  let g := started.createTreasureTokens ⟨0⟩ 1
  let g := addPermanent g thorinOakenshield ⟨0⟩ ⟨0⟩
  let g := g.refreshEnduringStory
  g.controlsStoried ⟨0⟩ && g.storiedPermanentCount ⟨0⟩ == 2 &&
    !g.hasEnduringStory ⟨0⟩

/-- Ruling 26 / 28: the third counting permanent grants an enduring story
before SBA; a 0/0 that then dies still leaves the player with the story.
Storied does not use the stack. -/
def storyFromZero : Game :=
  let g := started.createTreasureTokens ⟨0⟩ 2
  let g := addPermanent g zeroStoried ⟨0⟩ ⟨0⟩
  g.afterPermanentEnters (namedPermanent g "Zero Story")

#guard
  storyFromZero.hasEnduringStory ⟨0⟩ &&
    storyFromZero.log.any (fun s => mentions s "has an enduring story") &&
    storyFromZero.stack.isEmpty

def storyAfterSba : Game := storyFromZero.checkSBA

#guard
  storyAfterSba.hasEnduringStory ⟨0⟩ &&
    !storyAfterSba.battlefield.any (fun o => o.name == "Zero Story")

/-- Ruling 27: the designation stays on the player after the permanents leave. -/
def storyThenLostPermanents : Game :=
  let g := started.createTreasureTokens ⟨0⟩ 2
  let g := addPermanent g thorinOakenshield ⟨0⟩ ⟨0⟩
  let g := g.refreshEnduringStory
  let g :=
    g.battlefield.foldl (fun acc o =>
      if o.controlledBy ⟨0⟩ then (acc.move o.id (.graveyard o.owner) none).1 else acc) g
  g

#guard
  let g := started.createTreasureTokens ⟨0⟩ 2
  let g := addPermanent g thorinOakenshield ⟨0⟩ ⟨0⟩
  g.refreshEnduringStory |>.hasEnduringStory ⟨0⟩ &&
    storyThenLostPermanents.hasEnduringStory ⟨0⟩ &&
    storyThenLostPermanents.storiedPermanentCount ⟨0⟩ == 0

/-- Ori's +1/+0 and vigilance apply only while you have an enduring story. -/
#guard
  let g := addPermanent started oriKeeperOfSongs ⟨0⟩ ⟨0⟩
  let ori := namedPermanent g "Ori, Keeper of Songs"
  g.power ori == 3 && !(g.currentKeywords ori).vigilance &&
    let g := g.modifyPlayer ⟨0⟩ (fun pl => { pl with enduringStory := true })
    let ori := namedPermanent g "Ori, Keeper of Songs"
    g.power ori == 4 && (g.currentKeywords ori).vigilance

/-- Fíli's team pump applies to other creatures while you have a story. -/
#guard
  let g := addPermanent (addPermanent started filiThePathfinder ⟨0⟩ ⟨0⟩)
    grizzlyBears ⟨0⟩ ⟨0⟩
  let bears := namedPermanent g "Grizzly Bears"
  g.power bears == 2 &&
    let g := g.modifyPlayer ⟨0⟩ (fun pl => { pl with enduringStory := true })
    g.power (namedPermanent g "Grizzly Bears") == 3 &&
      g.toughness (namedPermanent g "Grizzly Bears") == 3

/-- Bombur does not untap unless you have an enduring story. -/
def bomburTapped : Game :=
  let g := addPermanent started bomburGentleDreamer ⟨0⟩ ⟨0⟩
  let o := namedPermanent g "Bombur, Gentle Dreamer"
  g.setObject { o with status := { o.status with tapped := true } }

#guard
  let g := bomburTapped.beginStep .untap
  (namedPermanent g "Bombur, Gentle Dreamer").status.tapped

#guard
  let g := bomburTapped.modifyPlayer ⟨0⟩ (fun pl => { pl with enduringStory := true })
  let g := g.beginStep .untap
  !(namedPermanent g "Bombur, Gentle Dreamer").status.tapped

/-!
## 23 — recruit
-/

/-- Ruling 23: once recruit begins, the draw/discard/token sequence is a
pending action; other players cannot take actions in the middle. -/
#guard
  instructorEntered.pending == .recruitDiscard ⟨0⟩ &&
    instructorEntered.actor == some ⟨0⟩ &&
    !instructorEntered.hasPriority ⟨0⟩ &&
    !instructorEntered.hasPriority ⟨1⟩ &&
    instructorRecruited.battlefield.any (fun o =>
      o.name == "Human Soldier" && o.printed.isToken)

/-!
## 29–30 — typecycling
-/

/-- Ruling 30: typecycling searches; it does not draw. -/
#guard
  (oliphauntCycled.handObjects ⟨0⟩).any (fun o => o.name == "Mountain") &&
    (oliphauntCycled.player ⟨0⟩).graveyard.any (fun id =>
      (oliphauntCycled.object! id).name == "Oliphaunt") &&
    (oliphauntCycled.player ⟨0⟩).hand.size ==
      (oliphauntCycleReady.player ⟨0⟩).hand.size &&
    !(oliphauntCycled.log.any (fun s => mentions s "draws"))

/-- Ruling 29: typecycling is an activated cycling-form ability (discard
this card from hand, search). The same activation is legal at instant speed
and illegal from the graveyard or battlefield. -/
#guard
  oliphauntCycleAbility.cost.discardSource &&
    oliphauntCycleAbility.activateFromHand &&
    oliphauntCycleAbility.effect == .searchLandTypeToHand "Mountain" &&
    oliphauntCycleAtEnd.canActivate ⟨0⟩
      (handCardNamed oliphauntCycleAtEnd ⟨0⟩ "Oliphaunt") oliphauntCycleAbility &&
    !((addPermanent afterDraw oliphaunt ⟨0⟩ ⟨0⟩).canActivate ⟨0⟩
      (namedPermanent (addPermanent afterDraw oliphaunt ⟨0⟩ ⟨0⟩) "Oliphaunt")
      oliphauntCycleAbility)

/-!
## 31–33, 37 — flashback
-/

/-- Ruling 31: flashback means you may cast the card from the graveyard
paying the flashback cost. -/
#guard
  momentOfGlory.flashback == some (ManaCost.ofGenericAndColor 4 .white) &&
    let g := addToGraveyard (skipTo afterDraw .precombatMain 40) momentOfGlory ⟨0⟩
    g.mayPlayFromGraveyard ⟨0⟩ (namedGraveyardCard g ⟨0⟩ "Moment of Glory") &&
    g.canCast ⟨0⟩ (namedGraveyardCard g ⟨0⟩ "Moment of Glory")

/-- Ruling 37: flashback still obeys timing. A sorcery cannot be flashbacked
in the end step. -/
#guard
  let g := applyIdle (passBoth (skipTo afterDraw .end 80))
  let g := addToGraveyard g momentOfGlory ⟨0⟩
  !g.asSorcery? ⟨0⟩ &&
    !g.canCast ⟨0⟩ (namedGraveyardCard g ⟨0⟩ "Moment of Glory")

/-- Ruling 32: a flashback spell is exiled as it leaves the stack. -/
#guard
  let g := addPermanent afterDraw grizzlyBears ⟨0⟩ ⟨0⟩
  let g := addToGraveyard (skipTo g .precombatMain 40) momentOfGlory ⟨0⟩
  let g := withWhiteMana g ⟨0⟩ 5
  let src := namedGraveyardCard g ⟨0⟩ "Moment of Glory"
  let g := mustApply g ⟨0⟩ (.cast src.id)
  let g := mustApply g ⟨0⟩ (.target (Target.permanent (namedPermanent g "Grizzly Bears").id))
  let g := mustApply g ⟨0⟩ .pay
  let g := passBoth g
  g.objects.any (fun o => o.zone == .exile && o.name == "Moment of Glory") &&
    !((g.player ⟨0⟩).graveyard.any (fun id => (g.object! id).name == "Moment of Glory")) &&
    g.log.any (fun s => mentions s "exiled (flashback)") &&
    (namedPermanent g "Grizzly Bears").status.plusOnePlusOne == 1

/-- Ruling 33: if the card is in your graveyard on your turn, you may cast
it before the opponent receives priority (you have priority after it
enters the graveyard at sorcery speed). -/
#guard
  let g := addToGraveyard (skipTo afterDraw .precombatMain 40) momentOfGlory ⟨0⟩
  g.hasPriority ⟨0⟩ && !g.hasPriority ⟨1⟩ &&
    g.canCast ⟨0⟩ (namedGraveyardCard g ⟨0⟩ "Moment of Glory")

/-!
## 38, 45, 60 — hone
-/

/-- Ruling 38 / 45: hone counters on any Equipment grant +1/+0, including
Equipment that never mentions hone (Dwarven Shortsword). -/
def shortswordHone : Game :=
  let g := addPermanent (addPermanent started dwarvenShortsword ⟨0⟩ ⟨0⟩)
    grizzlyBears ⟨0⟩ ⟨0⟩
  honeOn g "Dwarven Shortsword" "Grizzly Bears" 2

#guard
  -- 2/2 bear, +1/+2 from the sword, +2/+0 from two hone counters.
  shortswordHone.power (namedPermanent shortswordHone "Grizzly Bears") == 5 &&
    shortswordHone.toughness (namedPermanent shortswordHone "Grizzly Bears") == 4

/-- Ruling 60: unattaching removes the power immediately. -/
#guard
  let eq := namedPermanent shortswordHone "Dwarven Shortsword"
  let g := shortswordHone.setObject { eq with attachedTo := none }
  g.power (namedPermanent g "Grizzly Bears") == 2 &&
    g.toughness (namedPermanent g "Grizzly Bears") == 2

/-- Ruling 60: leaving the battlefield removes the boost immediately. -/
#guard
  let eq := namedPermanent shortswordHone "Dwarven Shortsword"
  let g := (shortswordHone.move eq.id (.graveyard eq.owner) none).1
  g.power (namedPermanent g "Grizzly Bears") == 2

/-- Ruling 60: removing hone counters changes power immediately. -/
#guard
  let eq := namedPermanent shortswordHone "Dwarven Shortsword"
  let g := shortswordHone.mapObjectStatus eq (fun s => { s with hone := 0 })
  g.power (namedPermanent g "Grizzly Bears") == 3

/-- Ruling 38: the boost is from the counter, not an Equipment ability, so
it still applies if the Equipment's static abilities are gone. -/
#guard
  let eq := namedPermanent shortswordHone "Dwarven Shortsword"
  let g := shortswordHone.setObject { eq with printed := { eq.printed with staticAbilities := #[] } }
  -- Sword no longer grants +1/+2; two hone counters still grant +2/+0.
  g.power (namedPermanent g "Grizzly Bears") == 4 &&
    g.toughness (namedPermanent g "Grizzly Bears") == 2

/-- Dwalin puts a hone counter on each Equipment you control. -/
#guard
  dwalinWeaponmaster.triggeredAbilities == #[.onEnterOrAttackHoneEachEquipment] &&
    let g := addPermanent (addPermanent started dwarvenShortsword ⟨0⟩ ⟨0⟩)
      dwalinWeaponmaster ⟨0⟩ ⟨0⟩
    let g := g.applyTriggeredAbility ⟨0⟩ .onEnterOrAttackHoneEachEquipment none
    (namedPermanent g "Dwarven Shortsword").status.hone == 1

/-!
## 63, 69 — triggered vs activated wording (judge reminders)
-/

#guard
  (ruling 63).comment.contains "when" &&
    dwalinWeaponmaster.triggeredAbilities.any (fun ab =>
      (TriggeredAbility.eventPrefix ab.timing).startsWith "Whenever")

#guard
  (ruling 69).comment.contains "colon" &&
    oinTheBrave.activatedAbilities.any (fun ab =>
      (ActivatedAbility.toNotation ab).contains ":")

/-!
## 122 — Food is an artifact type, never a creature type
-/

#guard
  foodToken.isArtifact && !foodToken.isCreature &&
    foodToken.hasSubtype "Food" && !foodToken.isCreature

end Mtg.Engine.RulingTests
