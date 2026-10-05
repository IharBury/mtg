import Mtg.Engine.Card
import Mtg.Engine.Catalog
import Mtg.Engine.Catalog.Hobbit
import Mtg.Engine.Catalog.HobbitEternal
import Mtg.Engine.Catalog.MarvelSuperHeroes
import Mtg.Engine.Game
import Mtg.Engine.OracleData
import Mtg.Engine.Tests.Abilities
import Mtg.Engine.Tests.Adventures
import Mtg.Engine.Tests.AttackTriggers
import Mtg.Engine.Tests.Auras
import Mtg.Engine.Tests.Effects
import Mtg.Engine.Tests.Elves
import Mtg.Engine.Tests.Equipment
import Mtg.Engine.Tests.Helpers
import Mtg.Engine.Tests.Pathmaker
import Mtg.Engine.Tests.Removal
import Mtg.Engine.Tests.RulingFixtures
import Mtg.Engine.Tests.Turns


/-!
# Engine behavior for unique Marvel Super Heroes (MSH) judge rulings (part 4)

Fourth slice of the MSH judge-ruling checks, from Mjölnir through Iron Man Armor.
-/

namespace Mtg.Engine.MshRulingTests

open Mtg.Engine
open Mtg.Engine.Catalog
open Mtg.Engine.Tests

/-- Rulings 177 / 179 / 237: Mjölnir doubles after assignment; two hammers
multiply by four; prevention of all damage skips Mjölnir. -/
def mjolnirDoubleOk : Bool :=
  let g := addPermanent afterDraw mjLnirHammerOfThor ⟨0⟩ ⟨0⟩
  let g := addPermanent g grayOgre ⟨0⟩ ⟨0⟩
  let g := addPermanent g grizzlyBears ⟨1⟩ ⟨1⟩
  let hammer := namedPermanent g "Mjölnir, Hammer of Thor"
  let ogre := namedPermanent g "Gray Ogre"
  let bears := namedPermanent g "Grizzly Bears"
  let g := g.attachSourceTo hammer ogre
  let gHit := g.dealDamageFrom ogre.name bears 2 (source := some (namedPermanent g "Gray Ogre"))
  (namedPermanent gHit "Grizzly Bears").status.damage == 4 &&
    (let g := addPermanent g mjLnirHammerOfThor ⟨0⟩ ⟨0⟩
     let hammers := g.battlefield.filter (fun o => o.name == "Mjölnir, Hammer of Thor")
     let ogre := namedPermanent g "Gray Ogre"
     let g :=
       hammers.foldl (fun acc h => acc.attachSourceTo (acc.object! h.id) ogre) g
     let bears := namedPermanent g "Grizzly Bears"
     let g := g.dealDamageFrom ogre.name bears 2 (source := some (namedPermanent g "Gray Ogre"))
     (namedPermanent g "Grizzly Bears").status.damage == 8) &&
    (let gPrev := g.mapObjectStatus ogre (fun s =>
        { s with preventDamageGrantedBy := #[ogre.id] })
     let gPrev := gPrev.dealDamageFrom ogre.name (namedPermanent gPrev "Grizzly Bears") 2
       (source := some (namedPermanent gPrev "Gray Ogre"))
     (namedPermanent gPrev "Grizzly Bears").status.damage == 0 &&
       gPrev.log.any (fun s => mentions s "prevented")) &&
    (mshRuling 529).comment.contains "chooses the order" &&
    (mshRuling 531).comment.contains "divided or assigned before doubling" &&
    (mshRuling 589).comment.contains "multiplied by four"

#guard mjolnirDoubleOk

/-- Ruling 531: combat assignment is doubled after the split. -/
def mjolnirCombatDivideOk : Bool :=
  let g := addPermanent afterDraw mjLnirHammerOfThor ⟨0⟩ ⟨0⟩
  let g := addPermanent g grayOgre ⟨0⟩ ⟨0⟩
  let g := addPermanent g hillGiant ⟨1⟩ ⟨1⟩
  let hammer := namedPermanent g "Mjölnir, Hammer of Thor"
  let ogre := namedPermanent g "Gray Ogre"
  let giant := namedPermanent g "Hill Giant"
  let g := g.attachSourceTo hammer ogre
  let g := g.setObject { ogre with status :=
    { ogre.status with attacking := true, blocked := true, attackingWhom := some ⟨1⟩ } }
  let g := { g with assignedCombatDamage :=
    #[{ source := ogre.id, toCreatures := #[(giant.id, 1)], toPlayer := 2 }] }
  let g := g.dealAssignedCombatDamage
  (namedPermanent g "Hill Giant").status.damage == 2 &&
    (g.player ⟨1⟩).life == 20 - 4

#guard mjolnirCombatDivideOk

/-- Ruling 556: a creature not controlled by the target opponent is illegal,
but the ability may still reveal. -/
def cloakIllegalCreatureStillResolvesOk : Bool :=
  let g := addToHand afterDraw lightningBolt ⟨1⟩
  let g := addPermanent g cloakAndDaggerEntwined ⟨0⟩ ⟨0⟩
  let g := addPermanent g grizzlyBears ⟨0⟩ ⟨0⟩
  let cloak := namedPermanent g "Cloak and Dagger, Entwined"
  let bears := namedPermanent g "Grizzly Bears"
  let g := g.applyTriggeredAbility ⟨0⟩ (.onEnter Effect.enterRevealHandExileUntilLeaves)
    (some cloak.id) #[Target.player ⟨1⟩, Target.permanent bears.id]
  logContains g "illegal target" &&
    onBattlefield g "Grizzly Bears" &&
    (mshRuling 556).comment.contains "illegal target"

#guard cloakIllegalCreatureStillResolvesOk

/-- Ruling 586: a card exiled from hand returns to hand when Cloak leaves. -/
def cloakReturnToHandOk : Bool :=
  let g := addToHand afterDraw lightningBolt ⟨1⟩
  let g := addPermanent g cloakAndDaggerEntwined ⟨0⟩ ⟨0⟩
  let bolt := handCardNamed g ⟨1⟩ "Lightning Bolt"
  let cloak := namedPermanent g "Cloak and Dagger, Entwined"
  let g := g.exileUntilSourceLeaves (some cloak.id) bolt
  let (g, _) := g.move cloak.id (.graveyard ⟨0⟩) none
  (g.handObjects ⟨1⟩).any (fun o => o.name == "Lightning Bolt") &&
    (mshRuling 586).comment.contains "returns to their hand"

#guard cloakReturnToHandOk

/-- Ruling 557: if the enchanted creature left, Serum does not move Equipment. -/
def serumHostLeftOk : Bool :=
  let g := addPermanent afterDraw superSoldierSerum ⟨0⟩ ⟨0⟩
  let g := addPermanent g vibraniumEnergyDaggers ⟨0⟩ ⟨0⟩
  let g := addPermanent g grayOgre ⟨0⟩ ⟨0⟩
  let eq := namedPermanent g "Vibranium Energy Daggers"
  let ogre := namedPermanent g "Gray Ogre"
  let g := g.attachSourceTo eq ogre
  let serum := namedPermanent g "Super-Soldier Serum"
  let g := g.applyModeledTrigger ⟨0⟩ (.onWatch Effect.watchEnchantedAttachEquipment)
    (some serum.id) #[Target.permanent eq.id]
  (namedPermanent g "Vibranium Energy Daggers").attachedTo == some ogre.id &&
    logContains g "Equipment stays" &&
    (mshRuling 557).comment.contains "remain attached"

#guard serumHostLeftOk

/-- Ruling 558: if either fight target is illegal, HULK SMASH deals no damage. -/
def hulkSmashIllegalFizzleOk : Bool :=
  let g := addPermanent afterDraw grayOgre ⟨0⟩ ⟨0⟩
  let g := addPermanent g grizzlyBears ⟨1⟩ ⟨1⟩
  let ogre := namedPermanent g "Gray Ogre"
  let bears := namedPermanent g "Grizzly Bears"
  let (g, _) := g.move bears.id (.graveyard ⟨1⟩) none
  let g := g.applyEffect ⟨0⟩ (Effect.creatureYouControlDealsPowerToOppCreature)
    #[Target.permanent ogre.id, Target.permanent bears.id]
  (namedPermanent g "Gray Ogre").status.damage == 0 &&
    (mshRuling 558).comment.contains "no damage will be dealt"

#guard hulkSmashIllegalFizzleOk

/-- Ruling 559: an illegal land target fizzles Avengers Disassembled entirely. -/
def avengersDisassembledFizzleOk : Bool :=
  let g := addPermanent afterDraw grizzlyBears ⟨1⟩ ⟨1⟩
  let g := addPermanent g forest ⟨1⟩ ⟨1⟩
  let land := namedPermanent g "Forest"
  let (gGone, _) := g.move land.id (.graveyard ⟨1⟩) none
  let fizzled := gGone.applyAvengersDisassembled ⟨0⟩ true true (some land.id)
  (namedPermanent fizzled "Grizzly Bears").status.damage == 0 &&
    logContains fizzled "doesn't resolve" &&
    (let gOk := g.applyAvengersDisassembled ⟨0⟩ true true (some land.id)
     (namedPermanent gOk "Grizzly Bears").status.damage == 3 &&
       logContains gOk "may search") &&
    (mshRuling 559).comment.contains "won't resolve"

#guard avengersDisassembledFizzleOk

/-- Ruling 572: Klaw reveals the whole hand if it is smaller than N. -/
def klawRevealAllOk : Bool :=
  let g :=
    (afterDraw.player ⟨1⟩).hand.foldl (fun acc id =>
      (acc.move id (.library ⟨1⟩) none).1) afterDraw
  let g := addToHand g lightningBolt ⟨1⟩
  let g := addPermanent g klawSonicSubjugator ⟨0⟩ ⟨0⟩
  let klaw := namedPermanent g "Klaw, Sonic Subjugator"
  let g := addToGraveyard g grizzlyBears ⟨0⟩
  let g := addToGraveyard g hillGiant ⟨0⟩
  let g := g.applyTriggeredAbility ⟨0⟩ (.onEnter Effect.enterRevealDiscardFromHand)
    (some klaw.id) #[Target.player ⟨1⟩]
  (g.handObjects ⟨1⟩).size == 1 &&
    logContains g "if fewer than" &&
    (mshRuling 572).comment.contains "reveal all the cards"

#guard klawRevealAllOk

/-- Ruling 574: Ultron's token becomes a creature only after it enters. -/
def ultronAfterEnterOk : Bool :=
  let g := addPermanent afterDraw ultronArtificialMalevolence ⟨0⟩ ⟨0⟩
  let g := addPermanent g theMindStone ⟨0⟩ ⟨0⟩
  let g := g.modifyPlayer ⟨0⟩ (fun pl =>
    { pl with manaPool := pl.manaPool.add .colorless 2 })
  let stone := namedPermanent g "The Mind Stone"
  let before :=
    (g.waitingTriggers.filter (fun (t : WaitingTrigger) =>
      t.event == TriggerEvent.creatureYouControlEnters)).size
  let g := g.applyModeledTrigger ⟨0⟩ (.onWatch Effect.watchUltronCopy)
    (some (namedPermanent g "Ultron, Artificial Malevolence").id)
    #[Target.permanent stone.id]
  let g := mustApply g ⟨0⟩ .accept
  let tok :=
    (g.battlefield.find? (fun o =>
      o.printed.isToken && o.name == "The Mind Stone")).getD stone
  tok.isCreature &&
    g.power tok == 2 &&
    (g.waitingTriggers.filter (fun (t : WaitingTrigger) =>
      t.event == TriggerEvent.creatureYouControlEnters)).size == before &&
    g.log.any (fun s => mentions s "after it enters") &&
    (mshRuling 574).comment.contains "doesn't become a 2/2"

#guard ultronAfterEnterOk

/-- Ruling 578: original division stands; an illegal target is skipped. -/
def deathToOurEnemiesDivisionOk : Bool :=
  let g := addPermanent afterDraw deathToOurEnemies ⟨0⟩ ⟨0⟩
  let g := addPermanent g grizzlyBears ⟨1⟩ ⟨1⟩
  let plan := namedPermanent g "Death to Our Enemies"
  let bears := namedPermanent g "Grizzly Bears"
  let g := g.queueModeledReflexive ⟨0⟩ (some plan.id) 10 7
  let (gGone, _) := g.move bears.id (.graveyard ⟨1⟩) none
  let gGone := gGone.applyModeledReflexive #[Target.player ⟨1⟩, Target.permanent bears.id]
  (gGone.player ⟨1⟩).life == 16 &&
    (mshRuling 578).comment.contains "no damage is dealt to the illegal target"

#guard deathToOurEnemiesDivisionOk

/-- Ruling 706: each target of Death to Our Enemies' reflexive must receive
at least 1 of the 7 damage; a 0-damage share is illegal and deals nothing. -/
def deathToOurEnemiesEachTargetAtLeastOneOk : Bool :=
  let g := addPermanent afterDraw deathToOurEnemies ⟨0⟩ ⟨0⟩
  let g := addPermanent g grizzlyBears ⟨1⟩ ⟨1⟩
  let plan := namedPermanent g "Death to Our Enemies"
  let bears := namedPermanent g "Grizzly Bears"
  let g := g.queueModeledReflexive ⟨0⟩ (some plan.id) 10
  let life0 := (g.player ⟨1⟩).life
  let gZero := g.applyModeledReflexive
    #[Target.player ⟨1⟩, Target.permanent bears.id] #[0, 7]
  let gOk := g.applyModeledReflexive
    #[Target.player ⟨1⟩, Target.permanent bears.id] #[1, 6]
  (gZero.player ⟨1⟩).life == life0 &&
    (namedPermanent gZero "Grizzly Bears").status.damage == 0 &&
    gZero.log.any (fun s => mentions s "at least 1 damage") &&
    (gOk.player ⟨1⟩).life == life0 - 1 &&
    (namedPermanent gOk "Grizzly Bears").status.damage == 6 &&
    (mshRuling 706).comment.contains "Each target must receive at least 1 damage"

#guard deathToOurEnemiesEachTargetAtLeastOneOk

/-- Rulings 227 / 353: Zemo copies only this activation's exiles and casts
them while resolving. -/
def heavyWhisper : CardDef :=
  { nightsWhisper with manaCost := { symbols := Array.replicate 8 (.colored .black) } }

def zemoBoastThisActivationOk : Bool :=
  let g := addPermanent afterDraw baronHelmutZemo ⟨0⟩ ⟨0⟩
  let g := addToGraveyard (addToGraveyard g heavyWhisper ⟨0⟩) heavyWhisper ⟨0⟩
  let g := addToGraveyard g nightsWhisper ⟨0⟩
  let zemo := namedPermanent g "Baron Helmut Zemo"
  let g := g.mapObjectStatus zemo (fun s => { s with declaredAsAttackerThisTurn := true })
  let gy := (g.player ⟨0⟩).graveyard.filter (fun id => (g.object! id).printed.manaCost.symbols.size == 8)
  let idx := (g.activatedAbilitiesOf zemo).size - 1
  let g := mustApply g ⟨0⟩ (.activate zemo.id idx)
  let g := mustApply g ⟨0⟩ (.choosePermanents gy)
  let g := passBoth g
  let copies := match g.pending with
    | .fraChoice _ (.castCopiesFree ids _ 3) => ids
    | _ => #[]
  let hand0 := (g.player ⟨0⟩).hand.size
  let g := mustApply g ⟨0⟩ (.cast copies[0]!)
  copies.size == 2 &&
    g.stack.any (fun e => (g.object! e.objectId).isCopy) &&
    (namedGraveyardCard g ⟨0⟩ "Night's Whisper").zone == .graveyard ⟨0⟩ &&
    (let g := passBoth (mustApply g ⟨0⟩ .decline)
     (g.player ⟨0⟩).hand.size == hand0 + 2) &&
    (mshRuling 579).comment.contains "copy only the cards exiled" &&
    (mshRuling 705).comment.contains "while Baron Helmut Zemo's boast ability is resolving"

#guard zemoBoastThisActivationOk

/-- Ruling 580: if every Vision mode was chosen, the ability does nothing. -/
def visionModesExhaustedOk : Bool :=
  let g := addPermanent afterDraw theVision ⟨0⟩ ⟨0⟩
  let vis := namedPermanent g "The Vision"
  let g := g.mapObjectStatus vis (fun s => { s with modesChosenThisTurn := #[0, 1, 2] })
  let hand0 := (g.player ⟨0⟩).hand.size
  let g := g.applyModeledTrigger ⟨0⟩ (.onCasting Effect.castingVisionModes)
    (some (namedPermanent g "The Vision").id)
  (g.player ⟨0⟩).hand.size == hand0 &&
    logContains g "removed from the stack" &&
    (mshRuling 580).comment.contains "removed from the stack"

#guard visionModesExhaustedOk

/-- Ruling 583: if either Swordsman target is illegal, the Equipment stays. -/
def swordsmanIllegalOk : Bool :=
  let g := addPermanent afterDraw swordsmanSharpScoundrel ⟨0⟩ ⟨0⟩
  let g := addPermanent g vibraniumEnergyDaggers ⟨0⟩ ⟨0⟩
  let g := addPermanent g grayOgre ⟨0⟩ ⟨0⟩
  let eq := namedPermanent g "Vibranium Energy Daggers"
  let ogre := namedPermanent g "Gray Ogre"
  let g := g.attachSourceTo eq ogre
  let (g, _) := g.move ogre.id (.graveyard ⟨0⟩) none
  let g := g.applyModeledTrigger ⟨0⟩ (.onWatch Effect.watchVillainAttachEquipment)
    (some (namedPermanent g "Swordsman, Sharp Scoundrel").id)
    #[Target.permanent eq.id, Target.permanent ogre.id]
  (namedPermanent g "Vibranium Energy Daggers").attachedTo.isNone &&
    logContains g "won't move" &&
    (mshRuling 583).comment.contains "Equipment won't move"

#guard swordsmanIllegalOk

/-- Ruling 584: Hyde's second mode must remove a counter if able. -/
def hydeMustRemoveOk : Bool :=
  let g := addPermanent afterDraw misterHydeMonsterWithin ⟨0⟩ ⟨0⟩
  let hyde := namedPermanent g "Mister Hyde, Monster Within"
  let g := g.addPlusOnePlusOneTo hyde 1
  let g := g.applyModeledTrigger ⟨0⟩ (.onStep Effect.stepHydeChoose)
    (some (namedPermanent g "Mister Hyde, Monster Within").id) #[]
    "Mister Hyde, Monster Within" (some (1 : Int))
  logContains g "must remove a counter" &&
    (let hyde := namedPermanent g "Mister Hyde, Monster Within"
     let g := g.applyModeledTrigger ⟨0⟩ (.onStep Effect.stepHydeChoose)
       (some hyde.id) #[Target.permanent hyde.id]
       "Mister Hyde, Monster Within" (some (1 : Int))
     (namedPermanent g "Mister Hyde, Monster Within").status.plusOnePlusOne == 0 &&
       (g.player ⟨0⟩).hand.size >= 1) &&
    (mshRuling 584).comment.contains "must remove a counter"

#guard hydeMustRemoveOk

/-- Ruling 585: Human Torch needs another Hero both to trigger and to resolve. -/
def humanTorchInterveningOk : Bool :=
  let g := addPermanent afterDraw humanTorchJohnnyStorm ⟨0⟩ ⟨0⟩
  let torch := namedPermanent g "Human Torch, Johnny Storm"
  let g := g.applyModeledTrigger ⟨0⟩ (.onResource Effect.resourceDrawIfAnotherHeroDamage) (some torch.id)
    #[Target.player ⟨1⟩]
  (g.player ⟨1⟩).life == 20 &&
    logContains g "has no effect" &&
    (let g := addPermanent afterDraw humanTorchJohnnyStorm ⟨0⟩ ⟨0⟩
     let g := addPermanent g colleenWingStreetSamurai ⟨0⟩ ⟨0⟩
     let torch := namedPermanent g "Human Torch, Johnny Storm"
     let g := g.applyModeledTrigger ⟨0⟩ (.onResource Effect.resourceDrawIfAnotherHeroDamage) (some torch.id)
       #[Target.player ⟨1⟩]
     (g.player ⟨1⟩).life == 19) &&
    (mshRuling 585).comment.contains "won't trigger"

#guard humanTorchInterveningOk

/-- Rulings 235 / 275: the last Reptil ability to resolve sets P/T and types. -/
def reptilLastResolvesOk : Bool :=
  let g := addPermanent afterDraw reptilDinomorpher ⟨0⟩ ⟨0⟩
  let r := namedPermanent g "Reptil, Dinomorpher"
  let g := g.applyAbilityEffect ⟨0⟩ (Effect.becomeDinosaurHero 3 5 (Keyword.reach.merge Keyword.vigilance)) #[] (some r.id)
  let r := namedPermanent g "Reptil, Dinomorpher"
  g.power r == 3 && g.toughness r == 5 &&
    r.hasSubtype "Dinosaur" && !r.hasSubtype "Human" &&
    (let g := g.applyAbilityEffect ⟨0⟩ (Effect.becomeDinosaurHero 6 6 Keyword.trample) #[] (some r.id)
     let r := namedPermanent g "Reptil, Dinomorpher"
     g.power r == 6 && g.toughness r == 6 &&
       r.hasSubtype "Dinosaur" && !r.hasSubtype "Human") &&
    (mshRuling 587).comment.contains "last one to resolve" &&
    (mshRuling 627).comment.contains "overwrite all previous effects"

#guard reptilLastResolvesOk

/-- Ruling 593: Iron Man Armor unattaches when it becomes a creature. -/
def ironManArmorUnattachOk : Bool :=
  let g := addPermanent afterDraw ironManArmor ⟨0⟩ ⟨0⟩
  let g := addPermanent g grayOgre ⟨0⟩ ⟨0⟩
  let armor := namedPermanent g "Iron Man Armor"
  let ogre := namedPermanent g "Gray Ogre"
  let g := g.attachSourceTo armor ogre
  let armor := namedPermanent g "Iron Man Armor"
  armor.attachedTo == some ogre.id &&
    (let g := g.applyAbilityEffect ⟨0⟩ (Effect.equipmentBecomesConstructHero) #[]
       (some armor.id)
     let armor := namedPermanent g "Iron Man Armor"
     armor.attachedTo.isNone &&
       armor.isCreature &&
       armor.hasSubtype "Equipment" &&
       (mshRuling 593).comment.contains "become unattached")

#guard ironManArmorUnattachOk

end Mtg.Engine.MshRulingTests
