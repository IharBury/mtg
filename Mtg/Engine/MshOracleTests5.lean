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
# Engine behavior for unique Marvel Super Heroes (MSH) judge rulings (part 5)

Fifth slice of the MSH judge-ruling checks: attack, lock, and Cosmic Cube behavior.
-/

namespace Mtg.Engine.MshRulingTests

open Mtg.Engine
open Mtg.Engine.Catalog
open Mtg.Engine.Tests


/-- Rulings 242 / 323: Iron Man's attack trigger looks for an artifact that
entered this turn, even if it already left. -/
def ironManArtifactEnteredOk : Bool :=
  let g := addPermanent afterDraw ironManMasterOfMachines ⟨0⟩ ⟨0⟩
  let iron := namedPermanent g "Iron Man, Master of Machines"
  let gNo := g.putAttackTriggersOnStack ⟨0⟩ #[iron.id]
  !(gNo.waitingTriggers.any (fun (t : WaitingTrigger) =>
      t.source.name == "Iron Man, Master of Machines")) &&
    (let g := addPermanent g theMindStone ⟨0⟩ ⟨0⟩
     let stone := namedPermanent g "The Mind Stone"
     let g := g.afterPermanentEnters stone
     let (g, _) := g.move stone.id (.graveyard ⟨0⟩) none
     (g.player ⟨0⟩).artifactEnteredThisTurn &&
       (let iron := namedPermanent g "Iron Man, Master of Machines"
        let g := g.putAttackTriggersOnStack ⟨0⟩ #[iron.id]
        g.waitingTriggers.any (fun (t : WaitingTrigger) =>
          t.source.name == "Iron Man, Master of Machines"))) &&
    (mshRuling 594).comment.contains "artifact entered" &&
    (mshRuling 675).comment.contains "won't trigger at all"

#guard ironManArtifactEnteredOk

/-- Ruling 604: Wrecking Crew modes run in printed order, so a destroyed
token is not sacrificed. -/
def wreckingCrewPrintedOrderOk : Bool :=
  let g := addPermanent afterDraw theRuinousWreckingCrew ⟨0⟩ ⟨0⟩
  let (g, tok) := g.createToken ⟨0⟩ Game.soldier11whiteToken
  let crew := namedPermanent g "The Ruinous Wrecking Crew"
  let g := g.mapObjectStatus crew (fun s => { s with chosenModes := #[2, 3] })
  let g := g.applyTriggeredAbility ⟨0⟩ (.onEnter Effect.enterChooseUpToXModes)
    (some crew.id) #[Target.permanent tok.id, Target.permanent tok.id]
  !g.battlefield.any (fun o => o.id == tok.id) &&
    g.log.any (fun s => mentions s "can't be sacrificed" || mentions s "destroyed") &&
    (mshRuling 604).comment.contains "printed order"

#guard wreckingCrewPrintedOrderOk

/-- Rulings 253 / 254: Mole Man lets you play lands from the graveyard at
normal land-play times, not cycle them. -/
def moleManPlayLandOk : Bool :=
  let g := addPermanent afterDraw moleManMoloidMaster ⟨0⟩ ⟨0⟩
  let g := addToGraveyard g forest ⟨0⟩
  let land := namedGraveyardCard g ⟨0⟩ "Forest"
  g.mayPlayFromGraveyard ⟨0⟩ land &&
    g.canPlayLand ⟨0⟩ &&
    (let gLate := { g with step := .beginningOfCombat }
     !gLate.canPlayLand ⟨0⟩) &&
    (let gCyc := addToGraveyard afterDraw kreeSentinel ⟨0⟩
     let cyc := namedGraveyardCard gCyc ⟨0⟩ "Kree Sentinel"
     let ab := cyc.printed.activatedAbilities[0]!
     !gCyc.canActivate ⟨0⟩ cyc ab) &&
    (mshRuling 605).comment.contains "doesn't allow you to activate" &&
    (mshRuling 606).comment.contains "only one land per turn"

#guard moleManPlayLandOk

/-- Ruling 608: Moon Girl's 6/6 overwrites a prior set-P/T; pumps and
counters still apply. -/
def moonGirlOverwriteOk : Bool :=
  let g := addPermanent afterDraw moonGirlAndDevilDinosaur ⟨0⟩ ⟨0⟩
  let mg := namedPermanent g "Moon Girl and Devil Dinosaur"
  let g := g.mapObjectStatus mg (fun s => { s with setBasePT := some (1, 1), pump := (1, 1) })
  let g := g.addPlusOnePlusOneTo (namedPermanent g "Moon Girl and Devil Dinosaur") 1
  let g := g.applyModeledTrigger ⟨0⟩ (.onResource Effect.resourceSecondDrawBecome66)
    (some (namedPermanent g "Moon Girl and Devil Dinosaur").id)
  let mg := namedPermanent g "Moon Girl and Devil Dinosaur"
  g.power mg == 8 && g.toughness mg == 8 &&
    (mshRuling 608).comment.contains "overwrite any previous effects"

#guard moonGirlOverwriteOk

/-- Rulings 265 / 267: Baxter Building checks toughness only as you activate. -/
def baxterActivationLockOk : Bool :=
  let g := addPermanent afterDraw baxterBuilding ⟨0⟩ ⟨0⟩
  let g := addPermanent g hillGiant ⟨0⟩ ⟨0⟩
  let g := g.addPlusOnePlusOneTo (namedPermanent g "Hill Giant") 1
  let bax := namedPermanent g "Baxter Building"
  let ab := bax.printed.activatedAbilities[1]!
  g.canActivate ⟨0⟩ bax ab &&
    (let (g, _) := g.move (namedPermanent g "Hill Giant").id (.graveyard ⟨0⟩) none
     let bax := namedPermanent g "Baxter Building"
     !g.canActivate ⟨0⟩ bax ab) &&
    (let g := g.applyAbilityEffect ⟨0⟩ (Effect.abilityDraw 1) #[]
       (some bax.id)
     (g.player ⟨0⟩).hand.size >= 1) &&
    (mshRuling 617).comment.contains "no player may take actions" &&
    (mshRuling 619).comment.contains "doesn't check again"

#guard baxterActivationLockOk

/-- Ruling 618: Arnim Zola checks the graveyard only as you activate. -/
def arnimActivationLockOk : Bool :=
  let g := addPermanent afterDraw arnimZolaBioFanatic ⟨0⟩ ⟨0⟩
  let g := addToGraveyard g grizzlyBears ⟨0⟩
  let g := addToGraveyard g hillGiant ⟨0⟩
  let arnim := namedPermanent g "Arnim Zola, Bio-Fanatic"
  let ab := arnim.printed.activatedAbilities[0]!
  g.canActivate ⟨0⟩ arnim ab &&
    (let g := g.applyAbilityEffect ⟨0⟩ (Effect.createTappedTokens .villain21menace 1) #[]
       (some arnim.id)
     g.battlefield.any (fun o =>
       o.printed.isToken && o.hasSubtype "Villain" && o.status.tapped)) &&
    (mshRuling 618).comment.contains "won't stop the ability from resolving"

#guard arnimActivationLockOk

/-- Ruling 650: Ten Rings draws through replacement effects. -/
def tenRingsReplacementOk : Bool :=
  let g := addPermanent afterDraw theTenRings ⟨0⟩ ⟨0⟩
  let g := addPermanent g aerialDoombot ⟨0⟩ ⟨0⟩
  let bot := namedPermanent g "Aerial Doombot"
  let g := g.setObject { bot with printed :=
    { bot.printed with drawTwoExceptFirstDrawStep := true } }
  let rings := namedPermanent g "The Ten Rings"
  let hand0 := (g.player ⟨0⟩).hand.size
  let g := { g with step := .end }
  let g := g.applyModeledTrigger ⟨0⟩ (.onStep Effect.stepDrawToTen) (some rings.id)
  (g.player ⟨0⟩).hand.size == hand0 + 2 * (10 - hand0) &&
    (mshRuling 650).comment.contains "replacement effects"

#guard tenRingsReplacementOk

/-- Ruling 651: the owner chooses second-from-top versus bottom. -/
def tricksterOwnerChoosesOk : Bool :=
  let g := addPermanent afterDraw grayOgre ⟨1⟩ ⟨1⟩
  let ogre := namedPermanent g "Gray Ogre"
  let gBot := g.applyOwnerPutsLibraryThenConnive ⟨0⟩
    #[Target.permanent ogre.id] (putOnBottom := true)
  (gBot.objects.any (fun o =>
      o.name == "Gray Ogre" && o.zone == .library ⟨1⟩)) &&
    (let gTop := g.applyOwnerPutsLibraryThenConnive ⟨0⟩
       #[Target.permanent ogre.id] (putOnBottom := false)
     let lib := (gTop.player ⟨1⟩).library
     lib.size ≥ 2 &&
       (gTop.object! lib[lib.size - 2]!).name == "Gray Ogre") &&
    (mshRuling 651).comment.contains "second from the top"

#guard tricksterOwnerChoosesOk

/-- Ruling 695: World War Hulk frees only the next red or green creature. -/
def worldWarHulkNextOnlyOk : Bool :=
  let g := addToHand afterDraw grayOgre ⟨0⟩
  let g := addToHand g grizzlyBears ⟨0⟩
  let g := g.applyEffect ⟨0⟩ (Effect.nextFreeRGCreature) #[]
  g.pendingFreeRGCreature == some ⟨0⟩ &&
    (let ogre := handCardNamed g ⟨0⟩ "Gray Ogre"
     !(g.playManaCost ogre ogre.printed).includesManaPayment &&
       (let (g, spell) := g.allocObject grayOgre ⟨0⟩ .stack (some ⟨0⟩)
        let g := g.putCastTriggersOnStack ⟨0⟩ (g.object! spell.id)
        g.pendingFreeRGCreature.isNone &&
          (let bears := handCardNamed g ⟨0⟩ "Grizzly Bears"
           (g.playManaCost bears bears.printed).includesManaPayment))) &&
    (mshRuling 695).comment.contains "only affects the next"

#guard worldWarHulkNextOnlyOk

/-- Ruling 707: Grim Reaper's return can attack a different player. -/
def grimReaperOtherDestinationOk : Bool :=
  let g := addPermanent afterDraw grimReaperLethalLegionnaire ⟨0⟩ ⟨0⟩
  let g := addToGraveyard g grizzlyBears ⟨0⟩
  let gy := namedGraveyardCard g ⟨0⟩ "Grizzly Bears"
  let g := g.returnFromGyTappedAttackingFinality ⟨0⟩ gy.id (attackingWhom := some ⟨1⟩)
  let bears := namedPermanent g "Grizzly Bears"
  bears.status.attacking &&
    bears.status.attackingWhom == some ⟨1⟩ &&
    (mshRuling 707).comment.contains "doesn't have to be the same player"

#guard grimReaperOtherDestinationOk

def cosmicCubeLookedNamed (g : Game) (name : String) : ObjectId :=
  match g.pending with
  | .mayCastFromLooked _ ids _ =>
    match ids.find? (fun id => (g.object! id).name == name) with
    | some id => id
    | none => panic! s!"expected {name} among looked-at cards"
  | _ => panic! "expected Cosmic Cube to wait for a cast choice"

/-- Rulings 356 / 357: Cosmic Cube is a controller choice; Doom Reigns casts
as it resolves. -/
def castAsResolvesOk : Bool :=
  let g := cosmicCubePending
  let bolt := cosmicCubeLookedNamed g "Lightning Bolt"
  let giant := cosmicCubeLookedNamed g "Hill Giant"
  let land := cosmicCubeLookedNamed g "Mountain"
  let (gEx, card) := afterDraw.allocObject nightsWhisper ⟨1⟩ .exile none
  let gEx := gEx.setObject { card with playPermission := some {
    player := ⟨0⟩, turnEndsRemaining := 1, withoutManaCost := true } }
  let gEx := gEx.castExiledAsResolves ⟨0⟩ 1
  match g.pending with
  | .mayCastFromLooked p ids maxMv =>
    p == ⟨0⟩ && maxMv == 2 && ids.size == 6 &&
      g.actor == some ⟨0⟩ &&
      !g.objects.any (fun o => o.name == "Lightning Bolt" && o.zone == .stack) &&
      g.log.any (fun s => mentions s "as this ability resolves") &&
      (match g.apply ⟨0⟩ (.cast land) with
       | .error msg => mentions msg "land cannot be cast"
       | .ok _ => false) &&
      (match g.apply ⟨0⟩ (.cast giant) with
       | .error msg => mentions msg "mana value is greater"
       | .ok _ => false) &&
      (let gCast := mustApply g ⟨0⟩ (.cast bolt)
       gCast.objects.any (fun o => o.name == "Lightning Bolt" && o.zone == .stack) &&
         gCast.log.any (fun s => mentions s "as the ability resolves") &&
         gCast.log.any (fun s => mentions s "on the bottom")) &&
      (let gDec := mustApply g ⟨0⟩ .decline
       !gDec.objects.any (fun o => o.name == "Lightning Bolt" && o.zone == .stack) &&
         gDec.log.any (fun s => mentions s "declines to cast") &&
         (gDec.player ⟨0⟩).library.any (fun id =>
           (gDec.findObject? id).any (·.name == "Lightning Bolt"))) &&
      gEx.objects.any (fun o => o.name == "Night's Whisper" && o.zone == .stack) &&
      gEx.log.any (fun s => mentions s "as the ability resolves") &&
      (mshRuling 708).comment.contains "can't wait to cast one later" &&
      (mshRuling 709).comment.contains "can't wait to cast them later"
  | _ => false

#guard castAsResolvesOk

/-- Cosmic Cube: Super Speed (Aura) on top, attacking Bears as the host. -/
def cosmicCubeAuraSetup : Game :=
  let g := addPermanent afterDraw cosmicCube ⟨0⟩ ⟨0⟩
  let g := addPermanent g grizzlyBears ⟨0⟩ ⟨0⟩
  let bears := namedPermanent g "Grizzly Bears"
  let g := g.setObject { bears with status := { bears.status with attacking := true } }
  let g := addToLibraryTop g mountain ⟨0⟩
  addToLibraryTop g superSpeed ⟨0⟩

def cosmicCubeAuraPending : Game :=
  let cube := namedPermanent cosmicCubeAuraSetup "Cosmic Cube"
  cosmicCubeAuraSetup.applyModeledTrigger ⟨0⟩ (.onYouAttacking Effect.youAttackingLookSixCast)
    (some cube.id)

/-- Casting an Aura as Cosmic Cube resolves still asks for a target to
enchant (CR 601.2c / 303.4). -/
def cosmicCubeCastAuraChoosesEnchantTargetOk : Bool :=
  let g := cosmicCubeAuraPending
  let speed := cosmicCubeLookedNamed g "Super Speed"
  superSpeed.isAura && superSpeed.requiresTarget &&
    (let gCast := mustApply g ⟨0⟩ (.cast speed)
     gCast.pending == .chooseTargets ⟨0⟩ &&
       gCast.actor == some ⟨0⟩ &&
       gCast.objects.any (fun o => o.name == "Super Speed" && o.zone == .stack) &&
       gCast.log.any (fun s => mentions s "must choose a target to enchant") &&
       gCast.log.any (fun s => mentions s "on the bottom") &&
       (let bears := namedPermanent gCast "Grizzly Bears"
        let gTgt := mustApply gCast ⟨0⟩ (.target (Target.permanent bears.id))
        (gTgt.stack.find? (fun e =>
          (gTgt.object! e.objectId).name == "Super Speed")).any (fun e =>
            e.targets == #[Target.permanent bears.id]) &&
          (let gRes := passBoth gTgt
           let aura := namedPermanent gRes "Super Speed"
           aura.attachedTo == some bears.id &&
             gRes.power (namedPermanent gRes "Grizzly Bears") == 3)))

#guard cosmicCubeCastAuraChoosesEnchantTargetOk

/-- A non-Aura enchantment cast this way does not ask for an enchant target. -/
def cosmicCubeCastNonAuraEnchantmentOk : Bool :=
  let g := addPermanent afterDraw cosmicCube ⟨0⟩ ⟨0⟩
  let g := addPermanent g grizzlyBears ⟨0⟩ ⟨0⟩
  let bears := namedPermanent g "Grizzly Bears"
  let g := g.setObject { bears with status := { bears.status with attacking := true } }
  let g := addToLibraryTop g mountain ⟨0⟩
  let g := addToLibraryTop g doomReignsSupreme ⟨0⟩
  let cube := namedPermanent g "Cosmic Cube"
  let g := g.applyModeledTrigger ⟨0⟩ (.onYouAttacking Effect.youAttackingLookSixCast)
    (some cube.id)
  let plan := cosmicCubeLookedNamed g "Doom Reigns Supreme"
  !doomReignsSupreme.isAura &&
    (let gCast := mustApply g ⟨0⟩ (.cast plan)
     gCast.objects.any (fun o => o.name == "Doom Reigns Supreme" && o.zone == .stack) &&
       gCast.pending != .chooseTargets ⟨0⟩)

#guard cosmicCubeCastNonAuraEnchantmentOk

end Mtg.Engine.MshRulingTests
