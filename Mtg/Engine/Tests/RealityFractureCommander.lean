import Mtg.Engine.Catalog.RealityFractureCommander
import Mtg.Engine.Fixture
import Mtg.Engine.Game

/-!
# Reality Fracture Commander

Parsed cards resolve: commander mana rocks, pain and check lands, removal,
morph, monarch tokens, and life that cannot change.
-/

namespace Mtg.Engine.Tests

open Mtg.Engine
open Mtg.Engine.Catalog

def findPerm (g : Game) (name : String) : GameObject :=
  match g.battlefield.find? (·.name == name) with
  | some o => o
  | none => panic! s!"missing {name}"

def must (e : Except String Game) : Game :=
  match e with
  | .ok g => g
  | .error msg => panic! msg

def spellEff (c : CardDef) : Effect :=
  match c.spellEffect with
  | some e => e
  | none => panic! s!"{c.name} has no spell"

def entered (card : CardDef) : Game × ObjectId :=
  let (g, obj) := afterDraw.allocObject card ⟨0⟩ .exile none
  g.putOntoBattlefield obj.id ⟨0⟩

#guard realityFractureCommanderCards.size == 87
#guard realityFractureCommanderCards.all (·.modellingError?.isNone)

#guard glacialFortress.entersTappedUnlessAnySubtype == #["Plains", "Island"]
#guard drownedCatacomb.entersTappedUnlessAnySubtype == #["Island", "Swamp"]
#guard sulfurFalls.entersTappedUnlessAnySubtype == #["Island", "Mountain"]
#guard fetidHeath.filterMana.isSome
#guard reflectingPool.tapAddYouCouldProduce
#guard fellwarStone.tapAddOppCouldProduce
#guard akromaAngelOfFury.morph.isSome
#guard overlordOfTheMistmoors.impending.isSome
#guard izzetSignet.activatedAbilities.size == 1

#guard
  match izzetSignet.activatedAbilities[0]!.effect.resolution with
  | .addMana ts => ts == #[.colored .blue, .colored .red]
  | _ => false

def solRingCast : Game :=
  let g := addPermanent afterDraw solRing ⟨0⟩ ⟨0⟩
  let o := findPerm g "Sol Ring"
  must (g.activateManaAbility ⟨0⟩ o.id 0 #[.colorless, .colorless])

#guard (solRingCast.manaAbilityDefs (findPerm solRingCast "Sol Ring")).size == 1
#guard (solRingCast.player ⟨0⟩).manaPool.total == 2

def forgePain : Game :=
  let g := addPermanent afterDraw battlefieldForge ⟨0⟩ ⟨0⟩
  let o := findPerm g "Battlefield Forge"
  must (g.activateManaAbility ⟨0⟩ o.id 1 #[.colored .red])

#guard (forgePain.player ⟨0⟩).life == 19

def brainstormed : Game :=
  afterDraw.applyEffect ⟨0⟩ (spellEff brainstorm) #[]

#guard (brainstormed.player ⟨0⟩).hand.size ==
  (afterDraw.player ⟨0⟩).hand.size + 1

def desparked : Game :=
  let g := addPermanent afterDraw darksteelAngel ⟨1⟩ ⟨1⟩
  let id := (findPerm g "Darksteel Angel").id
  g.applyEffect ⟨0⟩ (spellEff despark) #[Target.permanent id]

#guard desparked.objects.any (fun o => o.name == "Darksteel Angel" && o.zone == .exile)

def pathed : Game :=
  let g := addPermanent afterDraw grayOgre ⟨1⟩ ⟨1⟩
  let id := (findPerm g "Gray Ogre").id
  g.applyEffect ⟨0⟩ (spellEff pathToExile) #[Target.permanent id]

#guard pathed.objects.any (fun o => o.name == "Gray Ogre" && o.zone == .exile)
#guard
  match pathed.pending with
  | .fraChoice _ (.maySearchLibrary ..) => true
  | _ => false

def swordsLife : Game :=
  let g := addPermanent afterDraw grizzlyBears ⟨1⟩ ⟨1⟩
  let id := (findPerm g "Grizzly Bears").id
  g.applyEffect ⟨0⟩ (spellEff swordsToPlowshares) #[Target.permanent id]

#guard (swordsLife.player ⟨1⟩).life == 22
#guard swordsLife.objects.any (fun o => o.name == "Grizzly Bears" && o.zone == .exile)

def fiction : Game :=
  afterDraw.applyEffect ⟨0⟩ (spellEff factOrFiction) #[]

#guard (fiction.player ⟨0⟩).hand.size == (afterDraw.player ⟨0⟩).hand.size + 3
#guard (fiction.player ⟨0⟩).graveyard.size == 2

def faceDownAkroma : Game :=
  let g := addPermanent afterDraw akromaAngelOfFury ⟨0⟩ ⟨0⟩
  let o := findPerm g "Akroma, Angel of Fury"
  g.setObject { o with status := { o.status with faceDown := true } }

#guard faceDownAkroma.power (findPerm faceDownAkroma "Akroma, Angel of Fury") == 2
#guard faceDownAkroma.toughness (findPerm faceDownAkroma "Akroma, Angel of Fury") == 2
#guard (faceDownAkroma.activatedAbilitiesOf (findPerm faceDownAkroma "Akroma, Angel of Fury")).size == 1

def angelAtZero : Game :=
  let g := addPermanent afterDraw darksteelAngel ⟨0⟩ ⟨0⟩
  let g := g.setLife ⟨0⟩ 0 "life total becomes 0"
  g.checkSBA

#guard !(angelAtZero.player ⟨0⟩).lost
#guard (angelAtZero.player ⟨0⟩).life == 0

def reproach : Game :=
  let g := afterDraw.applyEffect ⟨0⟩ (spellEff teferisReproach) #[Target.player ⟨1⟩]
  let g := g.gainLife ⟨1⟩ 5
  g.loseLife ⟨1⟩ 3

#guard (reproach.player ⟨1⟩).lifeCantChange
#guard (reproach.player ⟨1⟩).protectionFromEverything
#guard (reproach.player ⟨1⟩).life == 20

#guard
  let (g, id) := entered serrasEmissary
  (g.object! id).status.chosenCardType == some "Creature"

def monarchGinger : Game :=
  let g := afterDraw.modifyPlayer ⟨0⟩ (fun pl => { pl with isMonarch := true })
  g.applyEffect ⟨0⟩ { resolution := .createTokens .gingerbrute (.fixed 1) false .you .ifMonarch } #[]

#guard monarchGinger.battlefield.any (fun o => o.name == "Gingerbrute" && o.printed.isToken)

def windcragEnters : Game :=
  entered windcragSiege |>.1

#guard (findPerm windcragEnters "Windcrag Siege").status.windcragMardu

end Mtg.Engine.Tests
