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

/-!
# Tokens, sequenced resolution effects, and Sagas.
-/

namespace Mtg.Engine.Tests

open Mtg.Engine
open Mtg.Engine.Catalog

/-- Dual lands enter tapped when played (CR 110.5b exception). -/
def hallsInHand : Game :=
  addToHand started elvenkingsHalls ⟨0⟩

def hallsReady : Game := skipTo hallsInHand .precombatMain 40

def hallsPlayed : Game :=
  mustApply hallsReady ⟨0⟩ (.playLand (handCardNamed hallsReady ⟨0⟩ "Elvenking's Halls").id)

#guard (namedPermanent hallsPlayed "Elvenking's Halls").status.tapped
#guard (namedPermanent hallsPlayed "Elvenking's Halls").printed.tapAddOneOf ==
  #[.colored .green, .colored .blue]

/-- Recruit draws, then a nonland discard creates a Human Soldier token. -/
def instructorEntered : Game :=
  (addToHand started lightningBolt ⟨0⟩).beginRecruit ⟨0⟩

#guard instructorEntered.pending == .recruitDiscard ⟨0⟩
#guard (instructorEntered.player ⟨0⟩).hand.size == (started.player ⟨0⟩).hand.size + 2

def instructorRecruited : Game :=
  mustApply instructorEntered ⟨0⟩
    (.discard (handCardNamed instructorEntered ⟨0⟩ "Lightning Bolt").id)

#guard instructorRecruited.pending == .none
#guard instructorRecruited.battlefield.any (fun o =>
  o.name == "Human Soldier" && o.printed.isToken)

/-- Ferocious on The Chief Warg fires when you attack with a 4-power creature. -/
def chiefAndBaloth : Game :=
  addPermanent (addPermanent started theChiefWarg ⟨0⟩ ⟨0⟩) rumblingBaloth ⟨0⟩ ⟨0⟩

#guard chiefAndBaloth.triggerConditionHolds ⟨0⟩ .onYouAttackFerociousDrawLoseLife

def chiefReady : Game :=
  passBoth (skipTo chiefAndBaloth .beginningOfCombat 80)

def chiefAttackDeclared : Game :=
  mustApply chiefReady ⟨0⟩ (.declareAttackers #[(namedPermanent chiefReady "Rumbling Baloth").id])

#guard chiefAttackDeclared.stack.any (fun e =>
  (chiefAttackDeclared.object! e.objectId).triggeredAbility ==
    some .onYouAttackFerociousDrawLoseLife)

def chiefAttackResolved : Game := passBoth chiefAttackDeclared

#guard (chiefAttackResolved.player ⟨0⟩).life == 19
#guard (chiefAttackResolved.player ⟨0⟩).hand.size ==
  (chiefAttackDeclared.player ⟨0⟩).hand.size + 1

/-- Dori creates an untapped Treasure; Long-Bodied Grey Dog creates a tapped one. -/
def doriTreasure : Game :=
  (addPermanent started doriBearerOfFriends ⟨0⟩ ⟨0⟩).applyTriggeredAbility
    ⟨0⟩ (.onEnterCreateTokens .treasure 1) none

#guard doriTreasure.battlefield.any (fun o =>
  o.name == "Treasure" && o.printed.isToken && !o.status.tapped)

def dogTreasure : Game :=
  (addPermanent started longBodiedGreyDog ⟨0⟩ ⟨0⟩).applyTriggeredAbility
    ⟨0⟩ (.onEnterCreateTokens .treasure 1 true) none

#guard dogTreasure.battlefield.any (fun o =>
  o.name == "Treasure" && o.printed.isToken && o.status.tapped)

/-- Tokens cannot block Duskwatch Hunter. -/
def hunterVsToken : Game :=
  let g := addPermanent started duskwatchHunter ⟨0⟩ ⟨0⟩
  let (g, _) := g.createToken ⟨1⟩ Catalog.humanSoldierToken
  let o := namedPermanent g "Duskwatch Hunter"
  g.setObject { o with status := { o.status with attacking := true } }

#guard
  !hunterVsToken.canBlock (namedPermanent hunterVsToken "Human Soldier")
    (namedPermanent hunterVsToken "Duskwatch Hunter")

/-- Amass Goblins creates a 0/0 Goblin Army and puts +1/+1 counters on it. -/
def flunkiesAmass : Game :=
  (addPermanent started goblinTownFlunkies ⟨0⟩ ⟨0⟩).applyTriggeredAbility
    ⟨0⟩ (.onEnterAmassGoblins 1) none

#guard
  let army := namedPermanent flunkiesAmass "Goblin Army"
  army.printed.isToken && flunkiesAmass.hasSubtype army "Goblin" &&
    flunkiesAmass.hasSubtype army "Army" &&
    army.status.plusOnePlusOne == 1

/-- A second amass puts counters on the existing Army. -/
def secondAmass : Game :=
  flunkiesAmass.applyTriggeredAbility ⟨0⟩ (.onEnterAmassGoblins 1) none

#guard
  (secondAmass.battlefield.filter (fun o => o.name == "Goblin Army")).size == 1 &&
    (namedPermanent secondAmass "Goblin Army").status.plusOnePlusOne == 2

/-- Gigantic Big Bear cannot be countered. -/
def giganticBigBearUncounterable : Game :=
  let g := addToHand (skipTo started .precombatMain 40) giganticBigBear ⟨0⟩
  let g := mustApply g ⟨0⟩ (.cast (handCardNamed g ⟨0⟩ "Gigantic Big Bear").id)
  g.counterStackSpell g.stack.back!.objectId

#guard
  (giganticBigBearUncounterable.object!
    giganticBigBearUncounterable.stack.back!.objectId).name ==
    "Gigantic Big Bear" &&
    giganticBigBearUncounterable.log.any (fun s => mentions s "can't be countered")

/-- Rage into the Valley draws, loses life, and amasses Goblins. -/
def rageAmass : Game :=
  started.applyEffect ⟨0⟩ (Effect.drawLoseLifeThenAmass 2) #[]

#guard
  (rageAmass.player ⟨0⟩).life == 19 &&
    (namedPermanent rageAmass "Goblin Army").status.plusOnePlusOne == 2

/-- `Resolution.sequence` applies each step in order. -/
def sequenceDrawThenGain : Game :=
  started.applyEffect ⟨0⟩ {
    resolution := .sequence [.draw 1, .gainLife 3]
    phrase := "draw a card. You gain 3 life" } #[]

#guard
  (sequenceDrawThenGain.player ⟨0⟩).hand.size ==
      (started.player ⟨0⟩).hand.size + 1 &&
    (sequenceDrawThenGain.player ⟨0⟩).life ==
      (started.player ⟨0⟩).life + 3

/-- Spell and ability loot both apply as draw, then a discard choice. -/
def spellDrawThenDiscardPending : Game :=
  afterDraw.applyEffect ⟨0⟩ (Effect.drawThenDiscard 2) #[]

#guard
  (spellDrawThenDiscardPending.player ⟨0⟩).hand.size ==
      (afterDraw.player ⟨0⟩).hand.size + 2 &&
    (match spellDrawThenDiscardPending.pending with
     | .chooseDiscardCard ⟨0⟩ _ => true
     | _ => false)

def abilityDrawThenDiscardPending : Game :=
  afterDraw.applyAbilityEffect ⟨0⟩ (Effect.abilityDrawThenDiscard 2) #[]

#guard
  (abilityDrawThenDiscardPending.player ⟨0⟩).hand.size ==
      (afterDraw.player ⟨0⟩).hand.size + 2 &&
    (match abilityDrawThenDiscardPending.pending with
     | .chooseDiscardCard ⟨0⟩ _ => true
     | _ => false)

def abilityDrawThenDiscardDone : Game :=
  mustApply abilityDrawThenDiscardPending ⟨0⟩
    (.discard (abilityDrawThenDiscardPending.player ⟨0⟩).hand.back!)

#guard
  abilityDrawThenDiscardDone.pending == .none &&
    (abilityDrawThenDiscardDone.player ⟨0⟩).hand.size ==
      (afterDraw.player ⟨0⟩).hand.size + 1 &&
    (abilityDrawThenDiscardDone.player ⟨0⟩).graveyard.size ==
      (afterDraw.player ⟨0⟩).graveyard.size + 1

/-- `ownerShuffleSourceDraw` applies as shuffle the source, then draw. -/
def ownerShuffleSourceSetup : Game :=
  addPermanent afterDraw gandalfWanderingWizard ⟨0⟩ ⟨0⟩

def ownerShuffleSourceResolved : Game :=
  ownerShuffleSourceSetup.applyAbilityEffect ⟨0⟩ (Effect.ownerShuffleSourceDraw 3) #[]
    (some (namedPermanent ownerShuffleSourceSetup "Gandalf, Wandering Wizard").id)

#guard
  !ownerShuffleSourceResolved.battlefield.any (fun o =>
      o.name == "Gandalf, Wandering Wizard") &&
    (ownerShuffleSourceResolved.player ⟨0⟩).hand.size ==
      (ownerShuffleSourceSetup.player ⟨0⟩).hand.size + 3 &&
    ownerShuffleSourceResolved.objects.any (fun o =>
      o.name == "Gandalf, Wandering Wizard" &&
        (o.zone == .library ⟨0⟩ || o.zone == .hand ⟨0⟩)) &&
    ownerShuffleSourceResolved.log.any (fun s => mentions s "shuffles their library")

/-- The printed owner draws even when another player controls the source. -/
def ownerShuffleSourceStolen : Game :=
  let g := addPermanent afterDraw gandalfWanderingWizard ⟨0⟩ ⟨1⟩
  g.applyAbilityEffect ⟨1⟩ (Effect.ownerShuffleSourceDraw 3) #[]
    (some (namedPermanent g "Gandalf, Wandering Wizard").id)

#guard
  (ownerShuffleSourceStolen.player ⟨0⟩).hand.size ==
      (afterDraw.player ⟨0⟩).hand.size + 3 &&
    (ownerShuffleSourceStolen.player ⟨1⟩).hand.size ==
      (afterDraw.player ⟨1⟩).hand.size &&
    ownerShuffleSourceStolen.objects.any (fun o =>
      o.name == "Gandalf, Wandering Wizard" &&
        (o.zone == .library ⟨0⟩ || o.zone == .hand ⟨0⟩))

/-- Missing source: no shuffle or draw. -/
def ownerShuffleSourceGone : Game :=
  afterDraw.applyAbilityEffect ⟨0⟩ (Effect.ownerShuffleSourceDraw 3) #[] none

#guard
  ownerShuffleSourceGone.log.any (fun s => mentions s "no longer in play") &&
    (ownerShuffleSourceGone.player ⟨0⟩).hand.size ==
      (afterDraw.player ⟨0⟩).hand.size

/-- `--norandom` shuffles first; the draw waits for the supplied order. -/
def ownerShuffleSourceNorandomPending : Game :=
  let g := addPermanent { afterDraw with norandom := true } gandalfWanderingWizard ⟨0⟩ ⟨0⟩
  g.applyAbilityEffect ⟨0⟩ (Effect.ownerShuffleSourceDraw 3) #[]
    (some (namedPermanent g "Gandalf, Wandering Wizard").id)

#guard
  (match ownerShuffleSourceNorandomPending.pendingRandom? with
     | some (.shuffleLibrary p) => p == ⟨0⟩
     | _ => false) &&
    (ownerShuffleSourceNorandomPending.player ⟨0⟩).hand.size ==
      (afterDraw.player ⟨0⟩).hand.size

def ownerShuffleSourceNorandomDone : Game :=
  mustApply ownerShuffleSourceNorandomPending ⟨0⟩ (.supplyOrder #[])

#guard
  ownerShuffleSourceNorandomDone.pendingRandom?.isNone &&
    (ownerShuffleSourceNorandomDone.player ⟨0⟩).hand.size ==
      (afterDraw.player ⟨0⟩).hand.size + 3

/-- `creaturesYouControlGetOppsLoseLife` applies as team pump, then opponents lose life. -/
def teamPumpThenOppsLoseSetup : Game :=
  addPermanent (addPermanent afterDraw grayOgre ⟨0⟩ ⟨0⟩) grizzlyBears ⟨1⟩ ⟨1⟩

def teamPumpThenOppsLoseResolved : Game :=
  teamPumpThenOppsLoseSetup.applyAbilityEffect ⟨0⟩
    (Effect.creaturesYouControlGetOppsLoseLife 2 0 2) #[]

#guard
  (namedPermanent teamPumpThenOppsLoseResolved "Gray Ogre").status.pumpPower == 2 &&
    (namedPermanent teamPumpThenOppsLoseResolved "Grizzly Bears").status.pumpPower == 0 &&
    (teamPumpThenOppsLoseResolved.player ⟨0⟩).life == (afterDraw.player ⟨0⟩).life &&
    (teamPumpThenOppsLoseResolved.player ⟨1⟩).life == (afterDraw.player ⟨1⟩).life - 2 &&
    teamPumpThenOppsLoseResolved.log.any (fun s =>
      mentions s "Gray Ogre gets +2/+0 until end of turn") &&
    teamPumpThenOppsLoseResolved.log.any (fun s => mentions s "Nissa loses 2 life")

/-- No creatures: opponents still lose life. -/
def teamPumpThenOppsLoseNoCreatures : Game :=
  afterDraw.applyAbilityEffect ⟨0⟩ (Effect.creaturesYouControlGetOppsLoseLife 2 0 2) #[]

#guard
  (teamPumpThenOppsLoseNoCreatures.player ⟨0⟩).life == (afterDraw.player ⟨0⟩).life &&
    (teamPumpThenOppsLoseNoCreatures.player ⟨1⟩).life ==
      (afterDraw.player ⟨1⟩).life - 2 &&
    !teamPumpThenOppsLoseNoCreatures.log.any (fun s =>
      mentions s "until end of turn") &&
    teamPumpThenOppsLoseNoCreatures.log.any (fun s => mentions s "Nissa loses 2 life")

/-- `plusOneAndDraw` applies as +1/+1 on the source, then draw. -/
def plusOneAndDrawResolved : Game :=
  let g := addPermanent afterDraw grayOgre ⟨0⟩ ⟨0⟩
  g.applyAbilityEffect ⟨0⟩ (Effect.plusOneAndDraw 1 2) #[]
    (some (namedPermanent g "Gray Ogre").id)

#guard
  (namedPermanent plusOneAndDrawResolved "Gray Ogre").status.plusOnePlusOne == 1 &&
    (plusOneAndDrawResolved.player ⟨0⟩).hand.size ==
      (afterDraw.player ⟨0⟩).hand.size + 2

/-- `plusOneAndGrant` applies as +1/+1, then grant keywords. -/
def plusOneAndGrantK : Keywords :=
  (Keyword.vigilance.merge Keyword.indestructible).merge Keyword.haste

def plusOneAndGrantResolved : Game :=
  let g := addPermanent afterDraw grayOgre ⟨0⟩ ⟨0⟩
  g.applyAbilityEffect ⟨0⟩ (Effect.plusOneAndGrant plusOneAndGrantK) #[]
    (some (namedPermanent g "Gray Ogre").id)

#guard
  (namedPermanent plusOneAndGrantResolved "Gray Ogre").status.plusOnePlusOne == 1 &&
    (namedPermanent plusOneAndGrantResolved "Gray Ogre").status.untilEotKeywords.vigilance &&
    (namedPermanent plusOneAndGrantResolved "Gray Ogre").status.untilEotKeywords.indestructible &&
    (namedPermanent plusOneAndGrantResolved "Gray Ogre").status.untilEotKeywords.haste

/-- `destroyUpToOneThenPlusOne` still plus-ones with no target. -/
def destroyUpToOneThenPlusOneNoTarget : Game :=
  let g := addPermanent afterDraw grayOgre ⟨0⟩ ⟨0⟩
  g.applyAbilityEffect ⟨0⟩ Effect.destroyUpToOneThenPlusOne #[]
    (some (namedPermanent g "Gray Ogre").id)

#guard
  (namedPermanent destroyUpToOneThenPlusOneNoTarget "Gray Ogre").status.plusOnePlusOne == 1

/-- `destroyUpToOneThenPlusOne` destroys a legal target, then plus-ones the source. -/
def destroyUpToOneThenPlusOneSetup : Game :=
  addPermanent (addPermanent afterDraw grayOgre ⟨0⟩ ⟨0⟩) foodToken ⟨1⟩ ⟨1⟩

def destroyUpToOneThenPlusOneResolved : Game :=
  destroyUpToOneThenPlusOneSetup.applyAbilityEffect ⟨0⟩
    Effect.destroyUpToOneThenPlusOne
    #[Target.permanent (namedPermanent destroyUpToOneThenPlusOneSetup "Food").id]
    (some (namedPermanent destroyUpToOneThenPlusOneSetup "Gray Ogre").id)

#guard
  (namedPermanent destroyUpToOneThenPlusOneResolved "Gray Ogre").status.plusOnePlusOne == 1 &&
    !destroyUpToOneThenPlusOneResolved.battlefield.any (fun o => o.name == "Food")

/-- `plusOneAndCreateTokens` applies as +1/+1 counters, then create. -/
def plusOneAndCreateTokensResolved : Game :=
  let g := addPermanent afterDraw grayOgre ⟨0⟩ ⟨0⟩
  g.applyAbilityEffect ⟨0⟩ (Effect.plusOneAndCreateTokens 2 .robotVillain22) #[]
    (some (namedPermanent g "Gray Ogre").id)

#guard
  (namedPermanent plusOneAndCreateTokensResolved "Gray Ogre").status.plusOnePlusOne == 2 &&
    plusOneAndCreateTokensResolved.battlefield.any (fun o =>
      o.name == "Robot Villain" && o.printed.isToken)

/-- `subtypesGainMenace` grants menace only to matching creatures you control. -/
def subtypesGainMenaceSetup : Game :=
  addPermanent
    (addPermanent
      (addPermanent afterDraw ragingGoblin ⟨0⟩ ⟨0⟩)
      orcishSiegemaster ⟨0⟩ ⟨0⟩)
    grayOgre ⟨0⟩ ⟨0⟩

def subtypesGainMenaceResolved : Game :=
  subtypesGainMenaceSetup.applyAbilityEffect ⟨0⟩
    (Effect.subtypesGainMenace #["Goblin", "Orc"]) #[]

#guard
  (namedPermanent subtypesGainMenaceResolved "Raging Goblin").status.untilEotKeywords.menace &&
    (namedPermanent subtypesGainMenaceResolved "Orcish Siegemaster").status.untilEotKeywords.menace &&
    !(namedPermanent subtypesGainMenaceResolved "Gray Ogre").status.untilEotKeywords.menace &&
    subtypesGainMenaceResolved.log.any (fun s => mentions s "Raging Goblin gains menace") &&
    subtypesGainMenaceResolved.log.any (fun s => mentions s "Orcish Siegemaster gains menace") &&
    !subtypesGainMenaceResolved.log.any (fun s => mentions s "Gray Ogre gains menace")

/-- The same constructor grants menace to Elves when that subtype is passed. -/
def elvesGainMenaceResolved : Game :=
  (addPermanent (addPermanent afterDraw llanowarElves ⟨0⟩ ⟨0⟩) ragingGoblin ⟨0⟩ ⟨0⟩)
    |>.applyAbilityEffect ⟨0⟩ (Effect.subtypesGainMenace #["Elf"]) #[]

#guard
  (namedPermanent elvesGainMenaceResolved "Llanowar Elves").status.untilEotKeywords.menace &&
    !(namedPermanent elvesGainMenaceResolved "Raging Goblin").status.untilEotKeywords.menace

/-- `teamGain` grants the given keyword to every creature you control. -/
def teamGainMenaceResolved : Game :=
  (addPermanent (addPermanent afterDraw ragingGoblin ⟨0⟩ ⟨0⟩) grayOgre ⟨0⟩ ⟨0⟩)
    |>.applyAbilityEffect ⟨0⟩ (Effect.teamGain Keyword.menace) #[]

#guard
  (namedPermanent teamGainMenaceResolved "Raging Goblin").status.untilEotKeywords.menace &&
    (namedPermanent teamGainMenaceResolved "Gray Ogre").status.untilEotKeywords.menace

/-- `becomeSubtypeWithLandsPT` grants the given type, not only Bear. -/
def becomeWolfWithLandsPT : Game :=
  let g := addPermanent afterDraw forest ⟨0⟩ ⟨0⟩
  let g := addPermanent g beornsHospitality ⟨0⟩ ⟨0⟩
  let src := namedPermanent g "Beorn's Hospitality"
  g.applyAbilityEffect ⟨0⟩ (Effect.becomeSubtypeWithLandsPT "Wolf") #[] (some src.id)

#guard
  (namedPermanent becomeWolfWithLandsPT "Beorn's Hospitality").hasSubtype "Wolf" &&
    !(namedPermanent becomeWolfWithLandsPT "Beorn's Hospitality").hasSubtype "Bear" &&
    (namedPermanent becomeWolfWithLandsPT "Beorn's Hospitality").isCreature

/-- Chief Warg's Company cannot attack without two other Wolves. -/
def loneWargCompany : Game :=
  addPermanent started chiefWargsCompany ⟨0⟩ ⟨0⟩

#guard !loneWargCompany.canAttack (namedPermanent loneWargCompany "Chief Warg's Company")

/-- Dwarven Shortsword enters, makes a Dwarf, and attaches. -/
def shortswordEntered : Game :=
  let g := addPermanent started dwarvenShortsword ⟨0⟩ ⟨0⟩
  let src := namedPermanent g "Dwarven Shortsword"
  g.applyTriggeredAbility ⟨0⟩ (.onEnterCreateThenAttach .dwarf) (some src.id)

#guard
  let dwarf := namedPermanent shortswordEntered "Dwarf"
  let sword := namedPermanent shortswordEntered "Dwarven Shortsword"
  dwarf.printed.isToken && sword.attachedTo == some dwarf.id

/-- Bag End Banquet creates three Foods. -/
def banquetFoods : Game :=
  (addPermanent started bagEndBanquet ⟨0⟩ ⟨0⟩).applyTriggeredAbility
    ⟨0⟩ (.onEnterCreateTokens .food 3) none

#guard
  (banquetFoods.battlefield.filter (fun o => o.name == "Food")).size == 3

/-- Tidings of War from hand amasses 1; from the graveyard it would amass 3. -/
def tidingsFromHandAmass1 : Bool :=
  (started.applyEffect ⟨0⟩ (Effect.amassGoblinsOrFromGy 1 3) #[]
    (castFromGraveyard := false)).battlefield.any (fun o =>
      o.name == "Goblin Army" && o.status.plusOnePlusOne == 1)

def tidingsFromGraveyardAmass3 : Bool :=
  (started.applyEffect ⟨0⟩ (Effect.amassGoblinsOrFromGy 1 3) #[]
    (castFromGraveyard := true)).battlefield.any (fun o =>
      o.name == "Goblin Army" && o.status.plusOnePlusOne == 3)

#guard tidingsFromHandAmass1
#guard tidingsFromGraveyardAmass3

/- The Sackville-Bagginses: sacrificing a token targets an opponent for 1 life. -/

def sackvilleWithTreasure : Game :=
  let g := addPermanent afterDraw theSackvilleBagginses ⟨0⟩ ⟨0⟩
  (g.createToken ⟨0⟩ Game.treasureToken).1

def sackvilleTreasure (g : Game) : GameObject :=
  match g.battlefield.find? (fun o => o.name == "Treasure" && o.printed.isToken) with
  | some o => o
  | none => panic! "expected a Treasure token"

#guard
  (sackvilleWithTreasure.battlefield.filter (fun o => o.name == "Treasure")).size == 1 &&
    (namedPermanent sackvilleWithTreasure "The Sackville-Bagginses").printed.triggeredAbilities.contains
      .onYouSacrificeTokenOppLosesLife

def sackvilleAfterTreasureTap : Game :=
  match sackvilleWithTreasure.tapForMana ⟨0⟩ (sackvilleTreasure sackvilleWithTreasure).id
      (.colored .black) with
  | .ok g => g.receivePriority ⟨0⟩
  | .error e => panic! e

#guard !(sackvilleAfterTreasureTap.battlefield.any (fun o => o.name == "Treasure"))

#guard
  match sackvilleAfterTreasureTap.pending with
  | .chooseTargets ⟨0⟩ => true
  | _ => false

def sackvilleTokenTriggerOnStack : Game :=
  sackvilleAfterTreasureTap

#guard
  (sackvilleTokenTriggerOnStack.legalTriggerTargets ⟨0⟩
    .onYouSacrificeTokenOppLosesLife).contains (Target.player ⟨1⟩)

def sackvilleTokenTriggerResolved : Game :=
  passBoth (mustApply sackvilleTokenTriggerOnStack ⟨0⟩ (.target (Target.player ⟨1⟩)))

#guard
  (sackvilleTokenTriggerResolved.player ⟨1⟩).life == 19 &&
    sackvilleTokenTriggerResolved.stack.isEmpty &&
    sackvilleTokenTriggerResolved.log.any (fun s => mentions s "loses 1 life")

/-- Sacrificing a nontoken does not fire the token-sacrifice trigger. -/
def sackvilleNontokenSac : Game :=
  let g := addPermanent afterDraw theSackvilleBagginses ⟨0⟩ ⟨0⟩
  let g := addPermanent g grizzlyBears ⟨0⟩ ⟨0⟩
  let bears := namedPermanent g "Grizzly Bears"
  (g.sacrificeToGraveyard bears "Chandra sacrifices Grizzly Bears").receivePriority ⟨0⟩

#guard
  !(sackvilleNontokenSac.stack.any (fun e =>
    (sackvilleNontokenSac.object! e.objectId).triggeredAbility ==
      some .onYouSacrificeTokenOppLosesLife)) &&
    !sackvilleNontokenSac.waitingTriggers.any (fun wt =>
      wt.ability == .onYouSacrificeTokenOppLosesLife)

/- Thranduil, the Elvenking copies activated abilities of Elves in the graveyard. -/

def thranduilWithGuardianGy : Game :=
  let g := addPermanent afterDraw thranduilTheElvenking ⟨0⟩ ⟨0⟩
  addToGraveyard g guardianOfTheHalls ⟨0⟩

def thranduilSource (g : Game) : GameObject :=
  namedPermanent g "Thranduil, the Elvenking"

#guard
  let o := thranduilSource thranduilWithGuardianGy
  let abs := thranduilWithGuardianGy.activatedAbilitiesOf o
  o.printed.activatedAbilities.isEmpty &&
    abs.size == 1 &&
    abs[0]!.effect == Effect.putPlusOnePlusOneOnSource 3 &&
    abs[0]!.cost.mana == ManaCost.ofGenericAndColors 5 [.green, .green]

#guard
  let g := addPermanent afterDraw thranduilTheElvenking ⟨0⟩ ⟨0⟩
  (g.activatedAbilitiesOf (namedPermanent g "Thranduil, the Elvenking")).isEmpty

def thranduilReady : Game :=
  withGreenMana
    (thranduilWithGuardianGy.modifyPlayer ⟨0⟩ (fun pl => { pl with landsPlayedThisTurn := 1 }))
    ⟨0⟩ 7

#guard thranduilReady.canActivate ⟨0⟩ (thranduilSource thranduilReady)
  (thranduilReady.activatedAbilitiesOf (thranduilSource thranduilReady))[0]!

#guard
  match Agent.choose thranduilReady ⟨0⟩ with
  | some (.activate id 0) => id == (thranduilSource thranduilReady).id
  | _ => false

def paidThranduilCopy : Game :=
  mustApply (mustApply thranduilReady ⟨0⟩ (.activate (thranduilSource thranduilReady).id 0))
    ⟨0⟩ .pay

def thranduilCopyResolved : Game := passBoth paidThranduilCopy

#guard
  (namedPermanent thranduilCopyResolved "Thranduil, the Elvenking").status.plusOnePlusOne == 3 &&
    thranduilCopyResolved.power (namedPermanent thranduilCopyResolved "Thranduil, the Elvenking") == 8 &&
    thranduilCopyResolved.toughness
      (namedPermanent thranduilCopyResolved "Thranduil, the Elvenking") == 9 &&
    thranduilCopyResolved.log.any (fun s =>
      mentions s "Thranduil, the Elvenking gets 3 +1/+1 counters")

/- A non-Elf in the graveyard is not copied. -/
#guard
  let g := addPermanent afterDraw thranduilTheElvenking ⟨0⟩ ⟨0⟩
  let g := addToGraveyard g ragingGoblin ⟨0⟩
  (g.activatedAbilitiesOf (namedPermanent g "Thranduil, the Elvenking")).isEmpty

/-- Thranduil copies `{T}: Add {G}` from Llanowar Elves in the graveyard. -/
def thranduilWithLlanowarGy : Game :=
  let g := addPermanent afterDraw thranduilTheElvenking ⟨0⟩ ⟨0⟩
  addToGraveyard g llanowarElves ⟨0⟩

#guard
  let o := namedPermanent thranduilWithLlanowarGy "Thranduil, the Elvenking"
  (thranduilWithLlanowarGy.manaAbilitiesOf o).contains (.colored .green) &&
    !o.printed.manaAbilities.contains (.colored .green)

def thranduilTappedForCopiedGreen : Game :=
  match thranduilWithLlanowarGy.tapForMana ⟨0⟩
      (namedPermanent thranduilWithLlanowarGy "Thranduil, the Elvenking").id
      (.colored .green) with
  | .ok g => g
  | .error e => panic! e

#guard
  (thranduilTappedForCopiedGreen.player ⟨0⟩).manaPool.get (.colored .green) == 1 &&
    (namedPermanent thranduilTappedForCopiedGreen "Thranduil, the Elvenking").status.tapped

/-!
# Supported Saga cards (CR 714)

Catalog Sagas store structured chapter `Effect`s. Entering a Saga puts a lore
counter on it and the matching chapter goes on the stack.
-/

def catalogSagasImplemented : Bool :=
  #[burnBurnTreeAndFern, downInTheValley, downDownToGoblinTown,
    oldFatSpiderCanTSeeMe, roadsGoEverEverOn, rollRollRollRoll,
    theMistyMountainsCold, theMountainKingSReturn].all (fun c =>
      match c.saga with
      | none => false
      | some s =>
        !s.chapters.isEmpty &&
          s.chapters.all (fun ch =>
            ch.chapterEffect.isSome && !ch.chapterNumbers.isEmpty))

#guard catalogSagasImplemented
#guard burnBurnTreeAndFern.saga.get!.finalChapterNumber == 4
#guard theMountainKingSReturn.saga.get!.finalChapterNumber == 3
#guard (burnBurnTreeAndFern.saga.get!.chaptersForLore 3).size == 1
#guard (burnBurnTreeAndFern.saga.get!.chaptersForLore 4).size == 1

/-- Put `card` onto the battlefield and run its enters/chapter triggers. -/
def enterSaga (g : Game) (card : CardDef) : Game :=
  let g := addPermanent g card ⟨0⟩ ⟨0⟩
  let o := namedPermanent g card.name
  g.afterPermanentEnters o |>.receivePriority ⟨0⟩

/-- Apply idle actions until the stack is empty and no choice is pending. -/
def settle (g : Game) : Nat → Game
  | 0 => panic! "settle fuel exhausted"
  | n + 1 =>
    if g.over then g
    else if g.stack.isEmpty && g.pending == .none && !g.hasWaitingTriggers then g
    else settle (applyIdle g) n

/-- Add one lore counter to the named Saga and resolve the resulting chapter. -/
def addSagaLore (g : Game) (name : String) : Game :=
  let g := g.addOneLoreCounter (namedPermanent g name)
  settle (g.receivePriority ⟨0⟩) 24

def burnChapterI : Game :=
  let g := addPermanent afterDraw grayOgre ⟨1⟩ ⟨1⟩
  settle (enterSaga g burnBurnTreeAndFern) 24

#guard
  (namedPermanent burnChapterI "Burn, Burn, Tree and Fern").status.lore == 1 &&
    !burnChapterI.battlefield.any (fun o => o.name == "Gray Ogre") &&
    (namedGraveyardCard burnChapterI ⟨1⟩ "Gray Ogre").zone == .graveyard ⟨1⟩ &&
    burnChapterI.log.any (fun s => mentions s "is dealt 6 damage") &&
    burnChapterI.log.any (fun s => mentions s "gets a lore counter") &&
    burnChapterI.log.any (fun s => mentions s "saga chapter")

def burnChapterII : Game :=
  let g := addPermanent burnChapterI wayfarersBauble ⟨1⟩ ⟨1⟩
  addSagaLore g "Burn, Burn, Tree and Fern"

#guard
  (namedPermanent burnChapterII "Burn, Burn, Tree and Fern").status.lore == 2 &&
    !burnChapterII.battlefield.any (fun o => o.name == "Wayfarer's Bauble") &&
    burnChapterII.log.any (fun s => mentions s "is destroyed")

def burnChapterIII : Game :=
  addSagaLore burnChapterII "Burn, Burn, Tree and Fern"

#guard
  (namedPermanent burnChapterIII "Burn, Burn, Tree and Fern").status.lore == 3 &&
    (burnChapterIII.player ⟨0⟩).manaPool.get (.colored .red) == 1

def burnChapterIV : Game :=
  addSagaLore burnChapterIII "Burn, Burn, Tree and Fern"

#guard
  !burnChapterIV.battlefield.any (fun o => o.name == "Burn, Burn, Tree and Fern") &&
    (burnChapterIV.player ⟨0⟩).manaPool.get (.colored .red) == 2 &&
    burnChapterIV.log.any (fun s => mentions s "CR 714.4")

def valleyChapterI : Game :=
  let g := addToLibraryTop afterDraw forest ⟨0⟩
  settle (enterSaga g downInTheValley) 24

#guard
  (valleyChapterI.player ⟨0⟩).hand.size == (afterDraw.player ⟨0⟩).hand.size + 1 &&
    (valleyChapterI.player ⟨0⟩).hand.any (fun id =>
      isBasicLandCard (valleyChapterI.object! id).printed) &&
    (namedPermanent valleyChapterI "Down in the Valley").status.lore == 1

def valleyLandfall : Game :=
  let g := addSagaLore valleyChapterI "Down in the Valley"
  let g := addUntappedLand g forest
  g.afterLandEnters (namedPermanent g "Forest") |>.receivePriority ⟨0⟩ |> (settle · 24)

#guard
  valleyLandfall.battlefield.any (fun o =>
    o.name == "Elf" && o.printed.isToken) &&
    (namedPermanent valleyLandfall "Down in the Valley").status.grantedTriggeredAbilities.size == 1

def valleyElvesPumped : Game :=
  let g := addPermanent valleyLandfall llanowarElves ⟨0⟩ ⟨0⟩
  addSagaLore g "Down in the Valley"

#guard
  let elf := namedPermanent valleyElvesPumped "Llanowar Elves"
  valleyElvesPumped.power elf == 2 && valleyElvesPumped.hasVigilance elf

def goblinTownChapterI : Game :=
  settle (enterSaga afterDraw downDownToGoblinTown) 24

#guard
  (goblinTownChapterI.player ⟨1⟩).hand.size ==
    (afterDraw.player ⟨1⟩).hand.size - 1 &&
    goblinTownChapterI.log.any (fun s => mentions s "reveals")

def goblinTownAmass : Game :=
  addSagaLore goblinTownChapterI "Down, Down to Goblin-town"

#guard
  goblinTownAmass.battlefield.any (fun o => o.name == "Goblin Army") &&
    (namedPermanent goblinTownAmass "Goblin Army").status.plusOnePlusOne == 1

def goblinTownDrain : Game :=
  addSagaLore goblinTownAmass "Down, Down to Goblin-town"

#guard
  (goblinTownDrain.player ⟨1⟩).life == (goblinTownAmass.player ⟨1⟩).life - 1 &&
    (goblinTownDrain.player ⟨0⟩).life == (goblinTownAmass.player ⟨0⟩).life + 1

def spiderHexproof : Game :=
  let g := addPermanent afterDraw llanowarElves ⟨0⟩ ⟨0⟩
  settle (enterSaga g oldFatSpiderCanTSeeMe) 24

#guard
  spiderHexproof.hasHexproof (namedPermanent spiderHexproof "Llanowar Elves") &&
    (namedPermanent spiderHexproof "Llanowar Elves").status.hexproofGrantedBy.size == 1

def spiderPrevent : Game :=
  let g := addPermanent spiderHexproof grayOgre ⟨1⟩ ⟨1⟩
  addSagaLore g "Old Fat Spider Can't See Me"

#guard
  (namedPermanent spiderPrevent "Gray Ogre").status.preventDamageGrantedBy.size == 1 &&
    spiderPrevent.sourceDamagePrevented (namedPermanent spiderPrevent "Gray Ogre")

def spiderPreventedDamage : Game :=
  spiderPrevent.dealDamageFrom "Gray Ogre"
    (namedPermanent spiderPrevent "Llanowar Elves") 1
    (source := some (namedPermanent spiderPrevent "Gray Ogre"))

#guard
  (namedPermanent spiderPreventedDamage "Llanowar Elves").status.damage == 0 &&
    spiderPreventedDamage.log.any (fun s => mentions s "is prevented")

def spiderDraw : Game :=
  addSagaLore spiderPrevent "Old Fat Spider Can't See Me"

#guard
  (spiderDraw.player ⟨0⟩).hand.size == (spiderPrevent.player ⟨0⟩).hand.size + 1

def spiderLeaves : Game :=
  addSagaLore spiderDraw "Old Fat Spider Can't See Me"

#guard
  !spiderLeaves.battlefield.any (fun o => o.name == "Old Fat Spider Can't See Me") &&
    !spiderLeaves.hasHexproof (namedPermanent spiderLeaves "Llanowar Elves") &&
    !spiderLeaves.sourceDamagePrevented (namedPermanent spiderLeaves "Gray Ogre")

def roadsChapterI : Game :=
  let g := addToLibraryTop (addToLibraryTop afterDraw plains ⟨0⟩) plains ⟨0⟩
  settle (enterSaga g roadsGoEverEverOn) 24

#guard
  (roadsChapterI.player ⟨0⟩).life == (afterDraw.player ⟨0⟩).life + 2 &&
    (namedPermanent roadsChapterI "Roads Go Ever, Ever On").linkedExile.size == 2

def roadsReturn : Game :=
  addSagaLore roadsChapterI "Roads Go Ever, Ever On"

#guard
  (roadsReturn.player ⟨0⟩).hand.any (fun id =>
    (roadsReturn.object! id).name == "Plains") &&
    (namedPermanent roadsReturn "Roads Go Ever, Ever On").linkedExile.size == 1

def roadsChapterIII : Game :=
  addSagaLore roadsReturn "Roads Go Ever, Ever On"

#guard
  ((roadsChapterIII.player ⟨0⟩).hand.filter (fun id =>
    (roadsChapterIII.object! id).name == "Plains")).size == 2 &&
    (namedPermanent roadsChapterIII "Roads Go Ever, Ever On").linkedExile.isEmpty

def roadsChapterIV : Game :=
  addSagaLore roadsChapterIII "Roads Go Ever, Ever On"

#guard
  !roadsChapterIV.battlefield.any (fun o => o.name == "Roads Go Ever, Ever On") &&
    (roadsChapterIV.player ⟨0⟩).attackPumpPerPlainsThisTurn == 1 &&
    roadsChapterIV.log.any (fun s => mentions s "CR 714.4")

def roadsAttackPump : Game :=
  let g := addPermanent roadsChapterIV llanowarElves ⟨0⟩ ⟨0⟩
  let g := addUntappedLand g plains
  let g := passBoth (skipTo g .beginningOfCombat 80)
  let g := mustApply g ⟨0⟩ (.declareAttackers #[(namedPermanent g "Llanowar Elves").id])
  settle g 24

#guard
  roadsAttackPump.power (namedPermanent roadsAttackPump "Llanowar Elves") == 2 &&
    roadsAttackPump.toughness (namedPermanent roadsAttackPump "Llanowar Elves") == 2

def rollBlink : Game :=
  let g := addPermanent afterDraw llanowarElves ⟨0⟩ ⟨0⟩
  let g := settle (enterSaga g rollRollRollRoll) 24
  g

#guard
  !rollBlink.battlefield.any (fun o => o.name == "Llanowar Elves") &&
    rollBlink.delayedEndStepReturns.size == 1

def rollReturned : Game :=
  settle (rollBlink.beginStep .end) 24

#guard
  rollReturned.battlefield.any (fun o => o.name == "Llanowar Elves") &&
    rollReturned.log.any (fun s => mentions s "beginning of end step")

def mistyTreasures : Game :=
  let g := settle (enterSaga afterDraw theMistyMountainsCold) 24
  let g := addSagaLore g "The Misty Mountains Cold"
  let g := addSagaLore g "The Misty Mountains Cold"
  addSagaLore g "The Misty Mountains Cold"

#guard
  !mistyTreasures.battlefield.any (fun o => o.name == "The Misty Mountains Cold") &&
    mistyTreasures.battlefield.any (fun o => o.name == "Dragon") &&
    (mistyTreasures.battlefield.filter (fun o => o.name == "Treasure")).size == 4 &&
    (namedPermanent mistyTreasures "Dragon").printed.power == some 6

def mountainKingRecruit : Game :=
  settle (enterSaga afterDraw theMountainKingSReturn) 24

#guard
  mountainKingRecruit.log.any (fun s => mentions s "discards") &&
    (namedPermanent mountainKingRecruit "The Mountain-king's Return").status.lore == 1

def mountainKingReturn : Game :=
  let g := addToGraveyard mountainKingRecruit llanowarElves ⟨0⟩
  addSagaLore g "The Mountain-king's Return"

#guard
  mountainKingReturn.battlefield.any (fun o => o.name == "Llanowar Elves")

def mountainKingPlusOne : Game :=
  addSagaLore mountainKingReturn "The Mountain-king's Return"

#guard
  !mountainKingPlusOne.battlefield.any (fun o =>
    o.name == "The Mountain-king's Return") &&
    (namedPermanent mountainKingPlusOne "Llanowar Elves").status.plusOnePlusOne == 1 &&
    mountainKingPlusOne.log.any (fun s => mentions s "CR 714.4")

/-- A later first-main lore counter advances a Saga that entered this turn. -/
def loreAfterFirstMain : Game :=
  let g := addPermanent afterDraw grayOgre ⟨1⟩ ⟨1⟩
  let g := settle (enterSaga g burnBurnTreeAndFern) 24
  let g := skipTo g .end 80
  let g := passBoth g
  let g := skipTo g .end 80
  let g := passBoth g
  skipTo g .precombatMain 80

#guard
  loreAfterFirstMain.battlefield.any (fun o =>
    o.name == "Burn, Burn, Tree and Fern" && o.status.lore ≥ 2)

end Mtg.Engine.Tests
