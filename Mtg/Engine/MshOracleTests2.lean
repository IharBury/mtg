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
# Engine behavior for unique Marvel Super Heroes (MSH) judge rulings (part 2)

Middle slice of the MSH judge-ruling checks. Shared helpers (`mshRuling`,
`mshEnter`, `onBattlefield`) live in `Mtg.Engine` and `Mtg.Engine.Tests`.
`Mtg.Engine.MshOracleTests3` continues from ruling 521, and later slices follow it.
-/

namespace Mtg.Engine.MshRulingTests

open Mtg.Engine
open Mtg.Engine.Catalog
open Mtg.Engine.Tests


/-- Ruling 712: Claim the Kingdom's first ability only sacrifices; the
indestructible counter is a reflexive second trigger. -/
def claimTheKingdomReflexiveOk : Bool :=
  let g := addPermanent afterDraw claimTheKingdom ⟨0⟩ ⟨0⟩
  let g := addPermanent g grizzlyBears ⟨0⟩ ⟨0⟩
  let plan := namedPermanent g "Claim the Kingdom"
  let bears := namedPermanent g "Grizzly Bears"
  let g := g.applyTriggeredAbility ⟨0⟩ .onFourthPlanIndestructible (some plan.id)
  !g.battlefield.any (fun o => o.name == "Claim the Kingdom") &&
    (namedPermanent g "Grizzly Bears").status.indestructibleCounters == 0 &&
    g.hasModeledReflexiveOnStack &&
    (let g := g.applyModeledReflexive #[Target.permanent bears.id]
     (namedPermanent g "Grizzly Bears").status.indestructibleCounters == 1) &&
    (let g := addPermanent afterDraw claimTheKingdom ⟨0⟩ ⟨0⟩
     let g := addPermanent g grizzlyBears ⟨0⟩ ⟨0⟩
     let plan := namedPermanent g "Claim the Kingdom"
     let (g, _) := g.move plan.id (.graveyard ⟨0⟩) none
     let g := g.applyTriggeredAbility ⟨0⟩ .onFourthPlanIndestructible (some plan.id)
     !g.hasModeledReflexiveOnStack &&
       (namedPermanent g "Grizzly Bears").status.indestructibleCounters == 0) &&
    (mshRuling 712).comment.contains "reflexive"

#guard claimTheKingdomReflexiveOk

/-- Ruling 713: Construct a Cosmic Cube queues control of an opponent. -/
def constructACosmicCubeReflexiveOk : Bool :=
  let g := addPermanent afterDraw constructACosmicCube ⟨0⟩ ⟨0⟩
  let plan := namedPermanent g "Construct a Cosmic Cube"
  let g := g.applyTriggeredAbility ⟨0⟩ .onSeventhPlanControlOpponent (some plan.id)
  !g.battlefield.any (fun o => o.name == "Construct a Cosmic Cube") &&
    g.hasModeledReflexiveOnStack &&
    (let g := g.applyModeledReflexive #[Target.player ⟨1⟩]
     g.controlsPlayer ⟨0⟩ ⟨1⟩ && g.controlOnNextTakenTurn) &&
    (mshRuling 713).comment.contains "reflexive"

#guard constructACosmicCubeReflexiveOk

/-- Ruling 714: Doom Reigns Supreme exiles the opponent's top cards only
after the Plan is sacrificed. -/
def doomReignsSupremeReflexiveOk : Bool :=
  let g := addPermanent afterDraw doomReignsSupreme ⟨0⟩ ⟨0⟩
  let plan := namedPermanent g "Doom Reigns Supreme"
  let lib0 := (g.player ⟨1⟩).library.size
  let g := g.applyTriggeredAbility ⟨0⟩ .onFifthPlanExileTopCast (some plan.id)
  (g.player ⟨1⟩).library.size == lib0 &&
    g.hasModeledReflexiveOnStack &&
    (let g := g.applyModeledReflexive #[Target.player ⟨1⟩]
     (g.player ⟨1⟩).library.size == lib0 - 5 &&
       (g.objects.filter (fun o => o.zone == .exile)).size >= 5 &&
       !(g.objects.any (fun o => o.zone == .exile && o.playPermission.isSome))) &&
    (mshRuling 714).comment.contains "reflexive"

#guard doomReignsSupremeReflexiveOk

/-- Ruling 715: Grim Reaper's pay is the first ability; the return is
reflexive. -/
def grimReaperReflexiveOk : Bool :=
  let g := addPermanent afterDraw grimReaperLethalLegionnaire ⟨0⟩ ⟨0⟩
  let g := addToGraveyard g grizzlyBears ⟨0⟩
  let grim := namedPermanent g "Grim Reaper, Lethal Legionnaire"
  let unpaid :=
    g.applyModeledTrigger ⟨0⟩ (.onThisAttack Effect.thisAttackPayReturnAttacking) (some grim.id)
  !unpaid.hasModeledReflexiveOnStack &&
    (let g := unpaid.modifyPlayer ⟨0⟩ (fun pl =>
       { pl with manaPool := (pl.manaPool.add (.colored .black) 4) })
     let g := mustApply g ⟨0⟩ .accept
     g.hasModeledReflexiveOnStack &&
       (let gy := namedGraveyardCard g ⟨0⟩ "Grizzly Bears"
        let g := g.applyModeledReflexive #[Target.card gy.id]
        let bears := namedPermanent g "Grizzly Bears"
        bears.status.tapped && bears.status.attacking &&
          bears.status.finality ≥ 1)) &&
    (mshRuling 715).comment.contains "reflexive"

#guard grimReaperReflexiveOk

/-- Ruling 716: Killmonger only destroys if another creature was
sacrificed. -/
def killmongerReflexiveOk : Bool :=
  let g := addPermanent afterDraw killmongerScourgeOfWakanda ⟨0⟩ ⟨0⟩
  let g := addPermanent g grizzlyBears ⟨0⟩ ⟨0⟩
  let g := addPermanent g grayOgre ⟨1⟩ ⟨1⟩
  let km := namedPermanent g "Killmonger, Scourge of Wakanda"
  let ogre := namedPermanent g "Gray Ogre"
  let g := g.applyTriggeredAbility ⟨0⟩ (.onEnter Effect.enterMaySacAnotherThenDestroyOppNonland) (some km.id)
  let g := mustApply g ⟨0⟩ (.choosePermanents #[(namedPermanent g "Grizzly Bears").id])
  !g.battlefield.any (fun o => o.name == "Grizzly Bears") &&
    g.hasModeledReflexiveOnStack &&
    g.battlefield.any (fun o => o.name == "Gray Ogre") &&
    (let g := g.applyModeledReflexive #[Target.permanent ogre.id]
     !g.battlefield.any (fun o => o.name == "Gray Ogre")) &&
    (let g := addPermanent afterDraw killmongerScourgeOfWakanda ⟨0⟩ ⟨0⟩
     let km := namedPermanent g "Killmonger, Scourge of Wakanda"
     let g := g.applyTriggeredAbility ⟨0⟩ (.onEnter Effect.enterMaySacAnotherThenDestroyOppNonland) (some km.id)
     !g.hasModeledReflexiveOnStack) &&
    (mshRuling 716).comment.contains "reflexive"

#guard killmongerReflexiveOk

/-- Rulings 273 / 365: Red Hulk's reflexive damage uses the counters only
if he survived to receive one. -/
def redHulkReflexiveOk : Bool :=
  let g := addPermanent afterDraw redHulk ⟨0⟩ ⟨0⟩
  let g := addPermanent g grizzlyBears ⟨1⟩ ⟨1⟩
  let hulk := namedPermanent g "Red Hulk"
  let g := g.applyModeledTrigger ⟨0⟩ (.onWatch Effect.watchRedHulk) (some hulk.id)
  (namedPermanent g "Red Hulk").status.plusOnePlusOne == 1 &&
    g.hasModeledReflexiveOnStack &&
    (let bears := namedPermanent g "Grizzly Bears"
     let g := g.applyModeledReflexive #[Target.permanent bears.id]
     (namedPermanent g "Grizzly Bears").status.damage == 1) &&
    (let g := addPermanent afterDraw redHulk ⟨0⟩ ⟨0⟩
     let hulk := namedPermanent g "Red Hulk"
     let (g, _) := g.move hulk.id (.graveyard ⟨0⟩) none
     let g := g.applyModeledTrigger ⟨0⟩ (.onWatch Effect.watchRedHulk) (some hulk.id)
     !g.hasModeledReflexiveOnStack) &&
    (mshRuling 625).comment.contains "must survive the damage" &&
    (mshRuling 717).comment.contains "reflexive"

#guard redHulkReflexiveOk

/-- Ruling 718: Speed's pay queues a haste-only blocker restriction. -/
def speedYoungAvengerReflexiveOk : Bool :=
  let g := addPermanent afterDraw speedYoungAvenger ⟨0⟩ ⟨0⟩
  let g := addPermanent g grizzlyBears ⟨1⟩ ⟨1⟩
  let speed := namedPermanent g "Speed, Young Avenger"
  let unpaid :=
    g.applyModeledTrigger ⟨0⟩ (.onCasting Effect.castingMayPayHasteUnblockable) (some speed.id)
  !unpaid.hasModeledReflexiveOnStack &&
    (let g := unpaid.modifyPlayer ⟨0⟩ (fun pl =>
       { pl with manaPool := (pl.manaPool.add (.colored .red) 1) })
     let g := mustApply g ⟨0⟩ .accept
     g.hasModeledReflexiveOnStack &&
       (let speed := namedPermanent g "Speed, Young Avenger"
        let g := g.applyModeledReflexive #[Target.permanent speed.id]
        let speed := namedPermanent g "Speed, Young Avenger"
        let g := g.setObject { speed with status := { speed.status with
          attacking := true, attackingWhom := some ⟨1⟩ } }
        let speed := namedPermanent g "Speed, Young Avenger"
        let bears := namedPermanent g "Grizzly Bears"
        speed.status.cantBeBlockedExceptByHasteUntilEot &&
          !g.canBlock bears speed &&
          (let g := g.mapObjectStatus bears (·.grantUntilEot Keyword.haste)
           g.canBlock (namedPermanent g "Grizzly Bears")
             (namedPermanent g "Speed, Young Avenger")))) &&
    (mshRuling 718).comment.contains "reflexive"

#guard speedYoungAvengerReflexiveOk

/-- Speed's reflexive ability can target only a creature that has haste. -/
def speedReflexiveHasteOnlyOk : Bool :=
  let g := addPermanent afterDraw speedYoungAvenger ⟨0⟩ ⟨0⟩
  let g := addPermanent g grizzlyBears ⟨1⟩ ⟨1⟩
  let g := g.modifyPlayer ⟨0⟩ (fun pl =>
    { pl with manaPool := pl.manaPool.add (.colored .red) 1 })
  let speed := namedPermanent g "Speed, Young Avenger"
  let g := g.applyModeledTrigger ⟨0⟩ (.onCasting Effect.castingMayPayHasteUnblockable)
    (some speed.id)
  let g := mustApply g ⟨0⟩ .accept
  let kind := (Game.modeledReflexiveEffect 9 1).targetKind
  let legal := g.legalTargetsForKind ⟨0⟩ kind (some speed.id)
  let bears := namedPermanent g "Grizzly Bears"
  legal.contains (Target.permanent speed.id) &&
    !legal.contains (Target.permanent bears.id) &&
    (let gMiss := g.applyModeledReflexive #[Target.permanent bears.id]
     !(namedPermanent gMiss "Grizzly Bears").status.cantBeBlockedExceptByHasteUntilEot)

#guard speedReflexiveHasteOnlyOk

/-- Ruling 720: Death to Our Enemies deals 7 only after the sacrifice. -/
def deathToOurEnemiesReflexiveOk : Bool :=
  let g := addPermanent afterDraw deathToOurEnemies ⟨0⟩ ⟨0⟩
  let plan := namedPermanent g "Death to Our Enemies"
  let life0 := (g.player ⟨1⟩).life
  let g := g.applyTriggeredAbility ⟨0⟩ .onFourthPlanDividedDamage (some plan.id)
  (g.player ⟨1⟩).life == life0 &&
    g.hasModeledReflexiveOnStack &&
    (let g := g.applyModeledReflexive #[Target.player ⟨1⟩]
     (g.player ⟨1⟩).life + 7 == life0) &&
    (mshRuling 720).comment.contains "reflexive"

#guard deathToOurEnemiesReflexiveOk

/-- Ruling 721: Rewrite History returns instants and sorceries only after
the Plan is sacrificed. -/
def rewriteHistoryReflexiveOk : Bool :=
  let g := addPermanent afterDraw rewriteHistory ⟨0⟩ ⟨0⟩
  let g := addToGraveyard g helicarrierStrike ⟨0⟩
  let g := addToGraveyard g hourOfDefeat ⟨0⟩
  let plan := namedPermanent g "Rewrite History"
  let inst := namedGraveyardCard g ⟨0⟩ "Helicarrier Strike"
  let sorc := namedGraveyardCard g ⟨0⟩ "Hour of Defeat"
  let hand0 := (g.player ⟨0⟩).hand.size
  let g := g.applyTriggeredAbility ⟨0⟩ .onFourthPlanReturnInstants (some plan.id)
  (g.player ⟨0⟩).hand.size == hand0 &&
    g.hasModeledReflexiveOnStack &&
    (let g := g.applyModeledReflexive #[Target.card inst.id, Target.card sorc.id]
     (g.player ⟨0⟩).hand.size == hand0 + 2 &&
       (g.handObjects ⟨0⟩).any (fun o => o.name == "Helicarrier Strike") &&
       (g.handObjects ⟨0⟩).any (fun o => o.name == "Hour of Defeat")) &&
    (mshRuling 721).comment.contains "reflexive"

#guard rewriteHistoryReflexiveOk

/-- Rulings 283 / 370: Speedball pumps even if the spell left, and may
change any number of that spell's targets (illegal replacements stay). -/
def speedballRetargetOk : Bool :=
  let g := addPermanent afterDraw speedballNewWarrior ⟨0⟩ ⟨0⟩
  let g := addPermanent g grizzlyBears ⟨1⟩ ⟨1⟩
  let g := addPermanent g mountain ⟨1⟩ ⟨1⟩
  let speed := namedPermanent g "Speedball, New Warrior"
  let (g, bolt) := g.allocObject lightningBolt ⟨1⟩ .stack (some ⟨1⟩)
  let g := g.putStackEntry ⟨1⟩ bolt.id
  let g := g.setStackEntryTargets bolt.id #[Target.permanent speed.id]
  let (gGone, _) := g.move bolt.id (.graveyard ⟨1⟩) none
  let gGone :=
    gGone.applyModeledTrigger ⟨0⟩ (.onWatch Effect.watchSpeedballTargeted) (some speed.id)
  gGone.power (namedPermanent gGone "Speedball, New Warrior") == 4 &&
    gGone.toughness (namedPermanent gGone "Speedball, New Warrior") == 4 &&
    (let g :=
       g.applyModeledTrigger ⟨0⟩ (.onWatch Effect.watchSpeedballTargeted) (some speed.id)
     let bears := namedPermanent g "Grizzly Bears"
     let g := g.retargetStackSpell bolt.id #[Target.permanent bears.id]
     (match g.stackEntry? bolt.id with
      | some e => e.targets[0]? == some (Target.permanent bears.id)
      | none => false) &&
       (let mt := namedPermanent g "Mountain"
        let g := g.retargetStackSpell bolt.id #[Target.permanent mt.id]
        match g.stackEntry? bolt.id with
        | some e => e.targets[0]? == some (Target.permanent bears.id)
        | none => false)) &&
    (mshRuling 635).comment.contains "resolves even if that spell" &&
    (mshRuling 722).comment.contains "You may change any number of the targets"

#guard speedballRetargetOk

/-- Rulings 287 / 292 / 296 / 371: Kingpin extort pays once; life gained
equals life actually lost; combat assignment uses toughness, not power. -/
def kingpinExtortAndToughnessOk : Bool :=
  let g := addPermanent afterDraw theKingpinOfCrime ⟨0⟩ ⟨0⟩
  (let life0 := (g.player ⟨0⟩).life
   let life1 := (g.player ⟨1⟩).life
   let g := g.extortDrain ⟨0⟩
   (g.player ⟨1⟩).life + 1 == life1 && (g.player ⟨0⟩).life == life0 + 1) &&
    (let g := g.modifyPlayer ⟨1⟩ (fun pl => { pl with lifeLocked := true })
     let life0 := (g.player ⟨0⟩).life
     let life1 := (g.player ⟨1⟩).life
     let g := g.extortDrain ⟨0⟩
     (g.player ⟨1⟩).life == life1 &&
       (g.player ⟨0⟩).life == life0) &&
    (let g := addPermanent afterDraw theKingpinOfCrime ⟨0⟩ ⟨0⟩
     let kp := namedPermanent g "The Kingpin of Crime"
     let g := g.setObject { kp with status := { kp.status with
       attacking := true, attackingWhom := some ⟨1⟩, summoningSick := false } }
     let kp := namedPermanent g "The Kingpin of Crime"
     let life0 := (g.player ⟨0⟩).life
     let g := g.applyModeledTrigger ⟨0⟩ (.onYouAttacking Effect.youAttackingPay2LifeToughness) (some kp.id)
       #[] "The Kingpin of Crime" (some (1 : Int))
     let g := mustApply g ⟨0⟩ .accept
     let kp := namedPermanent g "The Kingpin of Crime"
     g.power kp == 1 &&
       g.toughness kp == 5 &&
       (g.player ⟨0⟩).life == life0 - 2 &&
       g.combatDamageToAssign kp true == 5) &&
    (mshRuling 639).comment.contains "doesn't actually change any creature's power" &&
    (mshRuling 644).comment.contains "total amount of life lost" &&
    (mshRuling 648).comment.contains "doesn't target any player" &&
    (mshRuling 723).comment.contains "maximum of one time"

#guard kingpinExtortAndToughnessOk

/-- Ruling 727: Misty Knight draws for each discard this turn even if those
cards left the graveyard. -/
def mistyKnightDiscardCountOk : Bool :=
  let g := addPermanent afterDraw mistyKnightHeroForHire ⟨0⟩ ⟨0⟩
  let g := addToGraveyard g lightningBolt ⟨0⟩
  let g := addToGraveyard g giantGrowth ⟨0⟩
  let bolt := namedGraveyardCard g ⟨0⟩ "Lightning Bolt"
  let growth := namedGraveyardCard g ⟨0⟩ "Giant Growth"
  let (g, _) := g.move bolt.id .exile none
  let (g, _) := g.move growth.id .exile none
  let g := g.modifyPlayer ⟨0⟩ (fun pl => { pl with cardsDiscardedThisTurn := 2 })
  let misty := namedPermanent g "Misty Knight, Hero for Hire"
  let hand0 := (g.player ⟨0⟩).hand.size
  let g := g.applyAbilityEffect ⟨0⟩ (Effect.drawPerDiscardedThisTurn) #[] (some misty.id)
  (g.player ⟨0⟩).hand.size == hand0 + 2 &&
    !(g.objects.any (fun o =>
      o.zone == .graveyard ⟨0⟩ &&
        (o.name == "Lightning Bolt" || o.name == "Giant Growth"))) &&
    (mshRuling 727).comment.contains "even if those cards are no longer"

#guard mistyKnightDiscardCountOk

/-- Ruling 447: Ares returns himself if he dies while attacking. -/
def aresDiesAttackingOk : Bool :=
  let g := addPermanent afterDraw aresGodOfWar ⟨0⟩ ⟨0⟩
  let ares := namedPermanent g "Ares, God of War"
  let g := g.setObject { ares with status := { ares.status with
    attacking := true, attackingWhom := some ⟨1⟩ } }
  let ares := namedPermanent g "Ares, God of War"
  let (g, _) := g.move ares.id (.graveyard ⟨0⟩) none
  let g := g.applyModeledTrigger ⟨0⟩ (.onDeath Effect.deathAttackingReturnHand)
    (some ares.id)
  (g.handObjects ⟨0⟩).any (fun o => o.name == "Ares, God of War") &&
    !g.battlefield.any (fun o => o.name == "Ares, God of War") &&
    (mshRuling 447).comment.contains "Ares himself"

#guard aresDiesAttackingOk

/-- Ruling 452: Attuma triggers once per player attacked with Merfolk. -/
def attumaMerfolkOncePerPlayerOk : Bool :=
  let g := addPermanent afterDraw attumaAtlanteanWarlord ⟨0⟩ ⟨0⟩
  let g := addPermanent g grizzlyBears ⟨0⟩ ⟨0⟩
  let g :=
    g.mapObjectStatus (namedPermanent g "Grizzly Bears") (fun s =>
      { s with additionalSubtypes := #["Merfolk"] })
  let attuma := namedPermanent g "Attuma, Atlantean Warlord"
  let bears := namedPermanent g "Grizzly Bears"
  let g := g.setObject { attuma with status := { attuma.status with
    attacking := true, attackingWhom := some ⟨1⟩ } }
  let g := g.setObject { (namedPermanent g "Grizzly Bears") with status :=
    { bears.status with attacking := true, attackingWhom := some ⟨1⟩ } }
  let one :=
    g.putAttackTriggersOnStack ⟨0⟩
      #[(namedPermanent g "Attuma, Atlantean Warlord").id,
        (namedPermanent g "Grizzly Bears").id]
  let merfolkWaits (g : Game) : Nat :=
    (g.waitingTriggers.filter (fun (t : WaitingTrigger) =>
      t.event == TriggerEvent.merfolkAttackPlayer)).size
  merfolkWaits one == 1 &&
    (let g := { afterDraw with
      players := afterDraw.players.push
        { (afterDraw.player ⟨1⟩) with id := ⟨2⟩, name := "Gimli" } }
     let g := addPermanent g attumaAtlanteanWarlord ⟨0⟩ ⟨0⟩
     let g := addPermanent g grizzlyBears ⟨0⟩ ⟨0⟩
     let g :=
       g.mapObjectStatus (namedPermanent g "Grizzly Bears") (fun s =>
         { s with additionalSubtypes := #["Merfolk"] })
     let attuma := namedPermanent g "Attuma, Atlantean Warlord"
     let bears := namedPermanent g "Grizzly Bears"
     let g := g.setObject { attuma with status := { attuma.status with
       attacking := true, attackingWhom := some ⟨1⟩ } }
     let g := g.setObject { (namedPermanent g "Grizzly Bears") with status :=
       { bears.status with attacking := true, attackingWhom := some ⟨2⟩ } }
     let two :=
       g.putAttackTriggersOnStack ⟨0⟩
         #[(namedPermanent g "Attuma, Atlantean Warlord").id,
           (namedPermanent g "Grizzly Bears").id]
     merfolkWaits two == 2) &&
    (mshRuling 452).comment.contains "once for each player"

#guard attumaMerfolkOncePerPlayerOk

/-- Ruling 638: Avengers Assemble! still draws if the Hero left after
attacking. -/
def avengersAssembleHeroLeftOk : Bool :=
  let g := addPermanent afterDraw avengersAssemble ⟨0⟩ ⟨0⟩
  let g := addPermanent g mistyKnightHeroForHire ⟨0⟩ ⟨0⟩
  let g := g.modifyPlayer ⟨0⟩ (fun pl => { pl with attackedWithHeroThisTurn := true })
  let hero := namedPermanent g "Misty Knight, Hero for Hire"
  let (g, _) := g.move hero.id (.graveyard ⟨0⟩) none
  let assem := namedPermanent g "Avengers Assemble!"
  let hand0 := (g.player ⟨0⟩).hand.size
  let g := g.applyTriggeredAbility ⟨0⟩
    (.onEachEndStepDrawIfAttackedOrEnteredSubtype "Hero") (some assem.id)
  (g.player ⟨0⟩).hand.size == hand0 + 1 &&
    !g.battlefield.any (fun o => o.name == "Misty Knight, Hero for Hire") &&
    (mshRuling 638).comment.contains "doesn't need to still be on the battlefield"

#guard avengersAssembleHeroLeftOk

/-- Ruling 632: Shang-Chi lets you activate tap abilities immediately but
does not grant haste. -/
def shangChiActivateNotHasteOk : Bool :=
  -- `addPermanent` clears summoning sickness; insert Shang-Chi as sick.
  let g := insertObject afterDraw shangChiMasterOfKungFu ⟨0⟩ .battlefield
    (some ⟨0⟩) { summoningSick := true }
  let shang := namedPermanent g "Shang-Chi, Master of Kung Fu"
  shang.hasSummoningSickness &&
    !g.canAttack shang &&
    !g.hasHaste shang &&
    (g.tapForMana ⟨0⟩ shang.id (.colored .green)).isOk &&
    (mshRuling 632).comment.contains "doesn't grant haste"

#guard shangChiActivateNotHasteOk

/-- Ruling 624: Red Guardian can destroy a creature that dealt damage even
if the recipient has left. -/
def redGuardianDealtDamageOk : Bool :=
  let g := addPermanent afterDraw grizzlyBears ⟨1⟩ ⟨1⟩
  let g := addPermanent g grayOgre ⟨0⟩ ⟨0⟩
  let bears := namedPermanent g "Grizzly Bears"
  let ogre := namedPermanent g "Gray Ogre"
  let g := g.dealDamageFrom "Grizzly Bears" ogre 2 (source := some bears)
  let (g, _) := g.move (namedPermanent g "Gray Ogre").id (.graveyard ⟨0⟩) none
  let g := addPermanent g redGuardianSuperSoldier ⟨0⟩ ⟨0⟩
  let rg := namedPermanent g "Red Guardian, Super-Soldier"
  let bears := namedPermanent g "Grizzly Bears"
  bears.status.dealtDamageThisTurn &&
    (let g := g.applyTriggeredAbility ⟨0⟩ (.onEnter (Effect.enterDestroy .oppCreatureDealtDamageThisTurn))
       (some rg.id) #[Target.permanent bears.id]
     !g.battlefield.any (fun o => o.name == "Grizzly Bears")) &&
    (let g := addPermanent afterDraw grizzlyBears ⟨1⟩ ⟨1⟩
     let g := addPermanent g redGuardianSuperSoldier ⟨0⟩ ⟨0⟩
     let rg := namedPermanent g "Red Guardian, Super-Soldier"
     let bears := namedPermanent g "Grizzly Bears"
     let g := g.applyTriggeredAbility ⟨0⟩ (.onEnter (Effect.enterDestroy .oppCreatureDealtDamageThisTurn))
       (some rg.id) #[Target.permanent bears.id]
     g.battlefield.any (fun o => o.name == "Grizzly Bears")) &&
    (mshRuling 624).comment.contains "dealt damage this turn"

#guard redGuardianDealtDamageOk

/-- Rulings 221 / 259 / 300 / 346 / 358: control another player. -/
def controlAnotherPlayerOk : Bool :=
  let g := addPermanent afterDraw grizzlyBears ⟨1⟩ ⟨1⟩
  let g := g.setPlayerControl ⟨0⟩ ⟨1⟩
  g.controlsPlayer ⟨0⟩ ⟨1⟩ &&
    g.activePlayer == ⟨0⟩ &&
    (namedPermanent g "Grizzly Bears").controlledBy ⟨1⟩ &&
    g.resourcesFor ⟨1⟩ == ⟨1⟩ &&
    (let g := g.setPlayerControl ⟨0⟩ ⟨1⟩
     let g := { g with controlOnNextTakenTurn := true }
     g.controlsPlayer ⟨0⟩ ⟨1⟩ && g.controlOnNextTakenTurn) &&
    (mshRuling 573).comment.contains "next turn they actually take" &&
    (mshRuling 611).comment.contains "overwrite each other" &&
    (mshRuling 652).comment.contains "still the active player" &&
    (mshRuling 698).comment.contains "can't use your own" &&
    (mshRuling 710).comment.contains "don't control any of that player's permanents"

#guard controlAnotherPlayerOk

/-- Ruling 458: Captain Mar-Vell grants flash if an opponent has already
cast a spell this turn, even if he entered afterward. -/
def captainMarVellFlashOk : Bool :=
  let g := addPermanent afterDraw captainMarVellSpaceBorn ⟨0⟩ ⟨0⟩
  let g := addToHand g grizzlyBears ⟨0⟩
  let gCombat := { g with step := .beginningOfCombat }
  let bears := handCardNamed gCombat ⟨0⟩ "Grizzly Bears"
  !gCombat.asSorcery? ⟨0⟩ &&
    !gCombat.canCast ⟨0⟩ bears &&
    (let gOpp := gCombat.modifyPlayer ⟨1⟩ (fun pl =>
      { pl with spellsCastThisTurn := 1 })
     gOpp.canCast ⟨0⟩ (handCardNamed gOpp ⟨0⟩ "Grizzly Bears")) &&
    (let gLate := addToHand afterDraw grizzlyBears ⟨0⟩
     let gLate := { gLate with step := .beginningOfCombat }
     let gLate := gLate.modifyPlayer ⟨1⟩ (fun pl =>
       { pl with spellsCastThisTurn := 1 })
     !gLate.canCast ⟨0⟩ (handCardNamed gLate ⟨0⟩ "Grizzly Bears") &&
       (let gLate := addPermanent gLate captainMarVellSpaceBorn ⟨0⟩ ⟨0⟩
        gLate.canCast ⟨0⟩ (handCardNamed gLate ⟨0⟩ "Grizzly Bears"))) &&
    (mshRuling 458).comment.contains "as though they had flash"

#guard captainMarVellFlashOk

/-- Ruling 441: becoming a Construct Hero artifact creature replaces
creature types and keeps Equipment. -/
def ironManArmorTypesOk : Bool :=
  let g := addPermanent afterDraw ironManArmor ⟨0⟩ ⟨0⟩
  let armor := namedPermanent g "Iron Man Armor"
  let g := g.applyAbilityEffect ⟨0⟩ (Effect.equipmentBecomesConstructHero) #[]
    (some armor.id)
  let armor := namedPermanent g "Iron Man Armor"
  armor.isCreature &&
    armor.hasSubtype "Construct" &&
    armor.hasSubtype "Hero" &&
    armor.hasSubtype "Equipment" &&
    armor.types.any (· == .artifact) &&
    g.power armor == 1 &&
    g.toughness armor == 1 &&
    (let g := addPermanent afterDraw grayOgre ⟨0⟩ ⟨0⟩
     let ogre := namedPermanent g "Gray Ogre"
     let g := g.mapObjectStatus ogre (fun s => { s with
       additionalArtifactUntilEot := true
       additionalCreatureUntilEot := true
       replacedCreatureTypesUntilEot := some #["Construct", "Hero"] })
     let ogre := namedPermanent g "Gray Ogre"
     !ogre.hasSubtype "Ogre" &&
       ogre.hasSubtype "Construct" &&
       ogre.hasSubtype "Hero") &&
    (mshRuling 441).comment.contains "replaces any existing creature types"

#guard ironManArmorTypesOk

/-- Ruling 491: Robot Domination does not see creature cards that go to
the graveyard at the same time it leaves, and an animated copy is not a
creature card. -/
def robotDominationSimultaneousOk : Bool :=
  let gyWait (g : Game) : Bool :=
    g.waitingTriggers.any (fun (t : WaitingTrigger) =>
      t.event == TriggerEvent.creatureCardsPutIntoYourGy)
  let g := addPermanent afterDraw robotDomination ⟨0⟩ ⟨0⟩
  let g := addPermanent g grizzlyBears ⟨0⟩ ⟨0⟩
  let (g, _) := g.move (namedPermanent g "Grizzly Bears").id (.graveyard ⟨0⟩) none
  gyWait g &&
    (let g := addPermanent afterDraw robotDomination ⟨0⟩ ⟨0⟩
     let g := addPermanent g grizzlyBears ⟨0⟩ ⟨0⟩
     let g := g.moveSimultaneousToGraveyard
       #[(namedPermanent g "Robot Domination").id,
         (namedPermanent g "Grizzly Bears").id]
     !gyWait g) &&
    (let g := addPermanent afterDraw robotDomination ⟨0⟩ ⟨0⟩
     let rd := namedPermanent g "Robot Domination"
     let g := g.mapObjectStatus rd (fun s =>
       { s with additionalCreatureUntilEot := true })
     let (g, _) :=
       g.move (namedPermanent g "Robot Domination").id (.graveyard ⟨0⟩) none
     !gyWait g) &&
    (mshRuling 491).comment.contains "won't trigger at all" &&
    (mshRuling 628).comment.contains "creature cards are put into your graveyard"

#guard robotDominationSimultaneousOk

/-- Ruling 575: two attackers are never attacking alone, even at
different players. -/
def attacksAloneDestinationsOk : Bool :=
  let alone (g : Game) : Bool :=
    g.waitingTriggers.any (fun (t : WaitingTrigger) =>
      t.event == TriggerEvent.creatureYouControlAttacksAlone)
  let g := addPermanent afterDraw agent13SharonCarter ⟨0⟩ ⟨0⟩
  let g := addPermanent g grizzlyBears ⟨0⟩ ⟨0⟩
  let g := addPermanent g grayOgre ⟨0⟩ ⟨0⟩
  let bears := namedPermanent g "Grizzly Bears"
  let ogre := namedPermanent g "Gray Ogre"
  let g := g.setObject { bears with status := { bears.status with
    attacking := true, attackingWhom := some ⟨1⟩ } }
  let g := g.setObject { (namedPermanent g "Gray Ogre") with status :=
    { ogre.status with attacking := true, attackingWhom := some ⟨2⟩ } }
  let two :=
    g.putAttackTriggersOnStack ⟨0⟩
      #[(namedPermanent g "Grizzly Bears").id,
        (namedPermanent g "Gray Ogre").id]
  !alone two &&
    (let g := addPermanent afterDraw agent13SharonCarter ⟨0⟩ ⟨0⟩
     let g := addPermanent g grizzlyBears ⟨0⟩ ⟨0⟩
     let bears := namedPermanent g "Grizzly Bears"
     let g := g.setObject { bears with status := { bears.status with
       attacking := true, attackingWhom := some ⟨1⟩ } }
     let one :=
       g.putAttackTriggersOnStack ⟨0⟩ #[(namedPermanent g "Grizzly Bears").id]
     alone one) &&
    (mshRuling 430).comment.contains "attacks alone" &&
    (mshRuling 431).comment.contains "attacks alone" &&
    (mshRuling 432).comment.contains "declare attackers step" &&
    (mshRuling 433).comment.contains "declared as an attacker" &&
    (mshRuling 435).comment.contains "currently attacking" &&
    (mshRuling 575).comment.contains "neither attacking creature is attacking alone"

#guard attacksAloneDestinationsOk

/-- Ruling 685: Daredevil lets you play the exiled card whether or not
it is a Hero; Hero-ness only grants the pump. -/
def daredevilPlayExiledOk : Bool :=
  let g := addPermanent afterDraw daredevilManWithoutFear ⟨0⟩ ⟨0⟩
  let g := addToLibraryTop g lightningBolt ⟨0⟩
  let dd := namedPermanent g "Daredevil, Man Without Fear"
  let g := g.applyModeledTrigger ⟨0⟩ (.onYouAttacking Effect.youAttackingExileTopHeroPump) (some dd.id)
  let g := mustApply g ⟨0⟩ .accept
  let bolt? := g.objects.find? (fun o =>
    o.name == "Lightning Bolt" && o.zone == .exile)
  (match bolt? with
   | some o =>
     g.mayPlayFromExile ⟨0⟩ o &&
       (namedPermanent g "Daredevil, Man Without Fear").status.pump == (0, 0)
   | none => false) &&
    (let g := addPermanent afterDraw daredevilManWithoutFear ⟨0⟩ ⟨0⟩
     let g := addToLibraryTop g mistyKnightHeroForHire ⟨0⟩
     let dd := namedPermanent g "Daredevil, Man Without Fear"
     let g := g.applyModeledTrigger ⟨0⟩ (.onYouAttacking Effect.youAttackingExileTopHeroPump) (some dd.id)
     let g := mustApply g ⟨0⟩ .accept
     let hero? := g.objects.find? (fun o =>
       o.name == "Misty Knight, Hero for Hire" && o.zone == .exile)
     match hero? with
     | some o =>
       g.mayPlayFromExile ⟨0⟩ o &&
         (namedPermanent g "Daredevil, Man Without Fear").status.pump == (2, 1)
     | none => false) &&
    (mshRuling 685).comment.contains "You may play the exiled card"

#guard daredevilPlayExiledOk

/-- Ruling 437: opening-hand actions happen after mulligans, starting
player first, then the first turn begins. -/
def quicksilverOpeningHandOk : Bool :=
  let g := addToHand afterDraw quicksilverBrashBlur ⟨0⟩
  let g := addToHand g quicksilverBrashBlur ⟨1⟩
  let g := g.applyOpeningHandActions
  let p0 := g.battlefield.find? (fun o =>
    o.name == "Quicksilver, Brash Blur" && o.controlledBy ⟨0⟩)
  let p1 := g.battlefield.find? (fun o =>
    o.name == "Quicksilver, Brash Blur" && o.controlledBy ⟨1⟩)
  p0.isSome && p1.isSome &&
    (match p0, p1 with
     | some a, some b => a.timestamp < b.timestamp
     | _, _ => false) &&
    (mshRuling 437).comment.contains "opening hand"

#guard quicksilverOpeningHandOk

/-- Ruling 539: a copy cast without paying its mana cost has X = 0. -/
def freeCopyXIsZeroOk : Bool :=
  let g := addToHand afterDraw photonBlastBarrage ⟨0⟩
  let card := handCardNamed g ⟨0⟩ "Photon Blast Barrage"
  let card := { card with playPermission := some {
    player := ⟨0⟩, turnEndsRemaining := 1, withoutManaCost := true } }
  g.playManaCost card photonBlastBarrage == ManaCost.zero &&
    (mshRuling 539).comment.contains "choose 0 as the value of X" &&
    (mshRuling 197).comment.contains "can't choose to cast it for any alternative"

#guard freeCopyXIsZeroOk

/-- Ruling 483: Ares must attack if able, but not if he is sick, tapped,
or attacking would cost. -/
def aresAttacksIfAbleOk : Bool :=
  let g := addPermanent afterDraw aresGodOfWar ⟨0⟩ ⟨0⟩
  let ares := namedPermanent g "Ares, God of War"
  g.mustAttackIfAble ares &&
    (let g := insertObject afterDraw aresGodOfWar ⟨0⟩ .battlefield
       (some ⟨0⟩) { summoningSick := true }
     !g.mustAttackIfAble (namedPermanent g "Ares, God of War")) &&
    (let g := g.mapObjectStatus ares (fun s => { s with tapped := true })
     !g.mustAttackIfAble (namedPermanent g "Ares, God of War")) &&
    !g.mustAttackIfAble ares (attackRequiresCost := true) &&
    (mshRuling 483).comment.contains "doesn't have to attack"

#guard aresAttacksIfAbleOk

/-- Ruling 657: Hawkeye's plus-X is calculated when the noncombat damage
would be dealt. -/
def hawkeyeNoncombatXOk : Bool :=
  let g := addPermanent afterDraw hawkeyeYoungAvenger ⟨0⟩ ⟨0⟩
  let g := addPermanent g grayOgre ⟨0⟩ ⟨0⟩
  let g := addPermanent g grizzlyBears ⟨1⟩ ⟨1⟩
  let ogre := namedPermanent g "Gray Ogre"
  let bears := namedPermanent g "Grizzly Bears"
  let gHit := g.dealDamageFrom "Gray Ogre" bears 2 (source := some ogre)
  (namedPermanent gHit "Grizzly Bears").status.damage == 4 &&
    (let g := g.pumpPermanent (namedPermanent g "Hawkeye, Young Avenger") 3 0
     let ogre := namedPermanent g "Gray Ogre"
     let bears := namedPermanent g "Grizzly Bears"
     let g := g.dealDamageFrom "Gray Ogre" bears 2 (source := some ogre)
     (namedPermanent g "Grizzly Bears").status.damage == 7) &&
    (let (g, _) :=
       g.move (namedPermanent g "Hawkeye, Young Avenger").id (.graveyard ⟨0⟩) none
     let ogre := namedPermanent g "Gray Ogre"
     let bears := namedPermanent g "Grizzly Bears"
     let g := g.dealDamageFrom "Gray Ogre" bears 2 (source := some ogre)
     (namedPermanent g "Grizzly Bears").status.damage == 2) &&
    (mshRuling 657).comment.contains "calculated at the time"

#guard hawkeyeNoncombatXOk

/-- Rulings 372 / 373 / 374: play-from-exile permissions still follow
normal timing. -/
def exilePlayFollowsTimingOk : Bool :=
  let g := addToHand afterDraw grizzlyBears ⟨0⟩
  let card := handCardNamed g ⟨0⟩ "Grizzly Bears"
  let (g, exiled) := g.move card.id .exile none
  let o := g.object! exiled
  let g := g.setObject { o with playPermission := some {
    player := ⟨0⟩, turnEndsRemaining := 1 } }
  let o := g.object! exiled
  g.mayPlayFromExile ⟨0⟩ o &&
    g.canCast ⟨0⟩ o &&
    (let gCombat := { g with step := .beginningOfCombat }
     !gCombat.asSorcery? ⟨0⟩ &&
       !gCombat.canCast ⟨0⟩ (gCombat.object! exiled)) &&
    (mshRuling 388).comment.contains "normal timing rules" &&
    (mshRuling 421).comment.contains "normal timing rules" &&
    (mshRuling 724).comment.contains "normal timing rules" &&
    (mshRuling 725).comment.contains "normal timing rules" &&
    (mshRuling 726).comment.contains "timing rules"

#guard exilePlayFollowsTimingOk

/-- Rulings 133 / 189: Crossbones sees other Villains that enter with him,
but the ability triggers only once each turn. -/
def crossbonesVillainOnceOk : Bool :=
  let villainWait (g : Game) : Nat :=
    (g.waitingTriggers.filter (fun (t : WaitingTrigger) =>
      t.event == TriggerEvent.anotherVillainEnters)).size
  let g0 := addPermanent afterDraw crossbonesMaliciousMercenary ⟨0⟩ ⟨0⟩
  let gAlone := g0.afterPermanentEnters
    (namedPermanent g0 "Crossbones, Malicious Mercenary")
  villainWait gAlone == 0 &&
    (let g := addPermanent g0 redGuardianSuperSoldier ⟨0⟩ ⟨0⟩
     let g := g.afterPermanentEnters
       (namedPermanent g "Red Guardian, Super-Soldier")
     villainWait g == 1 &&
       (let xb := namedPermanent g "Crossbones, Malicious Mercenary"
        xb.status.firedOnceEachTurn &&
          (let g := addPermanent g baronStruckerHYDRAOverlord ⟨0⟩ ⟨0⟩
           let g := g.afterPermanentEnters
             (namedPermanent g "Baron Strucker, HYDRA Overlord")
           villainWait g == 1))) &&
    (let xb := namedPermanent g0 "Crossbones, Malicious Mercenary"
     let g := g0.applyModeledTrigger ⟨0⟩ (.onWatch Effect.watchVillainPlusOneDamageOnce)
       (some xb.id)
     (namedPermanent g "Crossbones, Malicious Mercenary").status.plusOnePlusOne == 1 &&
       (g.player ⟨1⟩).life == 18) &&
    (mshRuling 486).comment.contains "same time as other Villains" &&
    (mshRuling 541).comment.contains "trigger only once"

#guard crossbonesVillainOnceOk

/-- Ruling 659: Squirrel Girl's X is the squirrel count as the ability
resolves. -/
def squirrelGirlXOnceOk : Bool :=
  let g := addPermanent afterDraw theUnbeatableSquirrelGirl ⟨0⟩ ⟨0⟩
  let squirrels (g : Game) : Nat :=
    (g.battlefield.filter (fun o => o.hasSubtype "Squirrel")).size
  let n0 := squirrels g
  let g := g.applyAbilityEffect ⟨0⟩ (Effect.createTokensEqualSubtype .squirrel11green "Squirrel") #[] none
  let n1 := squirrels g
  n0 == 1 && n1 == 2 &&
    (let g := g.applyAbilityEffect ⟨0⟩ (Effect.createTokensEqualSubtype .squirrel11green "Squirrel") #[] none
     squirrels g == 4) &&
    (mshRuling 659).comment.contains "calculated only once"

#guard squirrelGirlXOnceOk

/-- Rulings 171 / 172: a copy of a linked exile ability adds to the same
exiled-card set; both return when the source leaves. -/
def linkedExileCopyOk : Bool :=
  let g := addPermanent afterDraw cloakAndDaggerEntwined ⟨0⟩ ⟨0⟩
  let g := addPermanent g grizzlyBears ⟨1⟩ ⟨1⟩
  let g := addPermanent g grayOgre ⟨1⟩ ⟨1⟩
  let cd := namedPermanent g "Cloak and Dagger, Entwined"
  let bears := namedPermanent g "Grizzly Bears"
  let g := g.applyTriggeredAbility ⟨0⟩ (.onEnter Effect.enterRevealHandExileUntilLeaves)
    (some cd.id) #[Target.player ⟨1⟩, Target.permanent bears.id]
  (namedPermanent g "Cloak and Dagger, Entwined").linkedExile.size == 1 &&
    (let cd := namedPermanent g "Cloak and Dagger, Entwined"
     let ogre := namedPermanent g "Gray Ogre"
     let g := g.applyTriggeredAbility ⟨0⟩ (.onEnter Effect.enterRevealHandExileUntilLeaves)
       (some cd.id) #[Target.player ⟨1⟩, Target.permanent ogre.id]
     let cd := namedPermanent g "Cloak and Dagger, Entwined"
     cd.linkedExile.size == 2 &&
       !g.battlefield.any (fun o => o.name == "Grizzly Bears") &&
       !g.battlefield.any (fun o => o.name == "Gray Ogre") &&
       (let (g, _) := g.move cd.id (.graveyard ⟨0⟩) none
        g.battlefield.any (fun o => o.name == "Grizzly Bears") &&
          g.battlefield.any (fun o => o.name == "Gray Ogre"))) &&
    (mshRuling 523).comment.contains "linked to a second ability" &&
    (mshRuling 524).comment.contains "linked to a second ability"

#guard linkedExileCopyOk

/-- Ruling 526: boast can be activated only once even if there is another
combat. -/
def boastOncePerTurnOk : Bool :=
  let g := addPermanent afterDraw baronHelmutZemo ⟨0⟩ ⟨0⟩
  let z := namedPermanent g "Baron Helmut Zemo"
  let g := g.mapObjectStatus z (fun s => { s with
    declaredAsAttackerThisTurn := true })
  let z := namedPermanent g "Baron Helmut Zemo"
  g.canActivateBoast z &&
    (let g := g.markBoastUsed z
     let z := namedPermanent g "Baron Helmut Zemo"
     !g.canActivateBoast z &&
       (let g := { g with additionalCombatPhases := 1 }
        !g.canActivateBoast (namedPermanent g "Baron Helmut Zemo"))) &&
    (mshRuling 526).comment.contains "only once"

#guard boastOncePerTurnOk

/-- Ruling 525: a token that dealt first-strike damage and then lost first
strike does not also deal regular combat damage. -/
def okoyeFirstStrikeLossOk : Bool :=
  let g := addPermanent afterDraw okoyeDoraMilajeLeader ⟨0⟩ ⟨0⟩
  let (g, tok) := g.createToken ⟨0⟩ Game.soldier11whiteToken
  let g := g.setObject { tok with status := { tok.status with
    attacking := true, attackingWhom := some ⟨1⟩ } }
  let tok := g.object! tok.id
  g.hasFirstStrike tok &&
    (let g := { g with
        firstStrikeDamageDone := true
        firstStrikeAssignedThisCombat := #[tok.id] }
     let (g, _) := g.move (namedPermanent g "Okoye, Dora Milaje Leader").id
       (.graveyard ⟨0⟩) none
     let tok := g.object! tok.id
     !g.hasFirstStrike tok &&
       !(g.creaturesAssigningCombatDamage true).any (fun o => o.id == tok.id)) &&
    (mshRuling 525).comment.contains "won't also deal normal combat damage"

#guard okoyeFirstStrikeLossOk

/-- Rulings 191 / 192: Nick Fury puts a DFC onto the battlefield front-face-up
unless it is night and the front has daybound. -/
def nickFuryDayDfc : CardDef := { bruceBanner with daybound := true }

def nickFuryDayEnter : Game :=
  let g := addToLibraryTop afterDraw nickFuryDayDfc ⟨0⟩
  g.enterFromNickFury ⟨0⟩ (g.player ⟨0⟩).library.back!

def nickFuryNightEnter : Game :=
  let g := addToLibraryTop { afterDraw with isNight := true } nickFuryDayDfc ⟨0⟩
  g.enterFromNickFury ⟨0⟩ (g.player ⟨0⟩).library.back!

#guard (namedPermanent nickFuryDayEnter "Bruce Banner").name == "Bruce Banner"
#guard !(namedPermanent nickFuryDayEnter "Bruce Banner").status.cantTransform
#guard
  let banner := namedPermanent nickFuryDayEnter "Bruce Banner"
  let g := nickFuryDayEnter.applyAbilityEffect ⟨0⟩ (Effect.transform) #[] (some banner.id)
  (namedPermanent g "The Incredible Hulk").name == "The Incredible Hulk"
#guard nickFuryNightEnter.isNight && nickFuryDayDfc.daybound &&
  nickFuryDayDfc.otherFace.isSome
#guard (namedPermanent nickFuryNightEnter "The Incredible Hulk").status.cantTransform
#guard
  let hulk := namedPermanent nickFuryNightEnter "The Incredible Hulk"
  let g := nickFuryNightEnter.applyAbilityEffect ⟨0⟩ (Effect.transform) #[] (some hulk.id)
  (namedPermanent g "The Incredible Hulk").name == "The Incredible Hulk" &&
    logContains g "can't transform"
#guard (mshRuling 543).comment.contains "daybound"
#guard (mshRuling 544).comment.contains "front face up"

def nickFuryDayboundOk : Bool :=
  let banner := namedPermanent nickFuryDayEnter "Bruce Banner"
  let gFlip := nickFuryDayEnter.applyAbilityEffect ⟨0⟩ (Effect.transform) #[] (some banner.id)
  let hulk := namedPermanent nickFuryNightEnter "The Incredible Hulk"
  let gBlocked := nickFuryNightEnter.applyAbilityEffect ⟨0⟩ (Effect.transform) #[] (some hulk.id)
  banner.name == "Bruce Banner" &&
    !banner.status.cantTransform &&
    (namedPermanent gFlip "The Incredible Hulk").name == "The Incredible Hulk" &&
    hulk.status.cantTransform &&
    (namedPermanent gBlocked "The Incredible Hulk").name == "The Incredible Hulk" &&
    logContains gBlocked "can't transform" &&
    (mshRuling 543).comment.contains "daybound" &&
    (mshRuling 544).comment.contains "front face up"

#guard nickFuryDayboundOk

/-- Rulings 334 / 335 / 336: you still decide for yourself, you see the
controlled player's hand, and you make their choices. -/
def controlPlayerChoicesOk : Bool :=
  let g := addToHand afterDraw lightningBolt ⟨1⟩
  let g := g.setPlayerControl ⟨0⟩ ⟨1⟩
  g.decidesFor ⟨0⟩ ⟨0⟩ &&
    g.decidesFor ⟨0⟩ ⟨1⟩ &&
    !g.decidesFor ⟨1⟩ ⟨1⟩ &&
    g.canSeeAs ⟨0⟩ ⟨1⟩ &&
    !g.canSeeAs ⟨1⟩ ⟨0⟩ &&
    (g.visibleHand ⟨0⟩ ⟨1⟩).any (fun o => o.name == "Lightning Bolt") &&
    (g.visibleHand ⟨1⟩ ⟨0⟩).isEmpty &&
    (mshRuling 686).comment.contains "continue to make your own choices" &&
    (mshRuling 687).comment.contains "you can see all cards" &&
    (mshRuling 688).comment.contains "you make all choices"

#guard controlPlayerChoicesOk

/-- Rulings 349 / 350 / 351 / 352: controlling a player does not reveal
their sideboard, grant outside-game or tournament choices, or let you
concede for them. They may still concede. -/
def controlPlayerLimitsOk : Bool :=
  let g := afterDraw.setPlayerControl ⟨0⟩ ⟨1⟩
  !g.canLookAtSideboard ⟨0⟩ ⟨1⟩ &&
    g.canLookAtSideboard ⟨1⟩ ⟨1⟩ &&
    !g.canChooseOutsideGame ⟨0⟩ ⟨1⟩ &&
    !g.canMakeTournamentDecision ⟨0⟩ ⟨1⟩ &&
    g.canMakeTournamentDecision ⟨1⟩ ⟨1⟩ &&
    !g.canMakeIllegalDecision ⟨0⟩ ⟨1⟩ &&
    !g.canConcedeAs ⟨0⟩ ⟨1⟩ &&
    g.canConcedeAs ⟨1⟩ ⟨1⟩ &&
    (let g := g.concede ⟨1⟩
     (g.player ⟨1⟩).lost) &&
    (mshRuling 701).comment.contains "sideboard" &&
    (mshRuling 702).comment.contains "tournament rules" &&
    (mshRuling 703).comment.contains "can't make any illegal decisions" &&
    (mshRuling 704).comment.contains "can't make the player"

#guard controlPlayerLimitsOk

/-- Rulings 193 / 196 / 197 / 200: copying a token uses its original
characteristics, not counters or tap. -/
def copyTokenOriginalOk : Bool :=
  let g := addPermanent afterDraw aerialDoombot ⟨0⟩ ⟨0⟩
  let (g, tok) := g.createToken ⟨0⟩ Game.soldier11whiteToken
  let g := g.mapObjectStatus tok (fun s =>
    { s with plusOnePlusOne := 3, tapped := true })
  let dest := namedPermanent g "Aerial Doombot"
  let tok := g.object! tok.id
  let g := g.becomeCopyOf dest tok
  let dest := g.object! dest.id
  dest.printed.name == "Soldier" &&
    dest.printed.power == some 1 &&
    dest.printed.toughness == some 1 &&
    dest.status.plusOnePlusOne == 0 &&
    !dest.status.tapped &&
    (mshRuling 545).comment.contains "original characteristics of that token" &&
    (mshRuling 548).comment.contains "original characteristics of that token" &&
    (mshRuling 549).comment.contains "original characteristics of that token" &&
    (mshRuling 552).comment.contains "original characteristics of that token"

#guard copyTokenOriginalOk

/-- Rulings 155 / 194 / 195 / 198 / 199 / 201: a copy of a copy uses the
copied characteristics. -/
def copyOfCopyOk : Bool :=
  let g := addPermanent afterDraw aerialDoombot ⟨0⟩ ⟨0⟩
  let g := addPermanent g sHIELDDeploymentDrone ⟨0⟩ ⟨0⟩
  let g := addPermanent g futuristForge ⟨0⟩ ⟨0⟩
  let drone := namedPermanent g "S.H.I.E.L.D. Deployment Drone"
  let dest := namedPermanent g "Aerial Doombot"
  let g := g.becomeCopyOf dest drone
  let dest := g.object! dest.id
  let forge := namedPermanent g "Futurist Forge"
  let g := g.becomeCopyOf forge dest
  let forge := g.object! forge.id
  dest.printed.name == "S.H.I.E.L.D. Deployment Drone" &&
    forge.printed.name == "S.H.I.E.L.D. Deployment Drone" &&
    (mshRuling 546).comment.contains "copy of whatever that permanent copied" &&
    (mshRuling 550).comment.contains "copy of whatever" &&
    (mshRuling 551).comment.contains "whatever that creature copied" &&
    (mshRuling 553).comment.contains "copy of whatever that permanent copied" &&
    (mshRuling 508).comment.contains "whatever that creature copied" &&
    (mshRuling 547).comment.contains "whatever that artifact copied"

#guard copyOfCopyOk

/-- Rulings 92 / 93 / 115 / 304: a token copy is not tapped or countered,
and the copied permanent's enters abilities trigger. -/
def copyTokenEntersAbilitiesOk : Bool :=
  let g := addPermanent afterDraw futuristForge ⟨0⟩ ⟨0⟩
  let src := namedPermanent g "Futurist Forge"
  let (g, tok) := g.copyBattlefieldPermanent src ⟨0⟩
  let before := g.waitingTriggers.size
  let g := g.afterPermanentEnters tok
  !tok.status.tapped &&
    tok.status.plusOnePlusOne == 0 &&
    tok.printed.isToken &&
    g.waitingTriggers.size > before &&
    (mshRuling 445).comment.contains "enters abilities of each copied" &&
    (mshRuling 446).comment.contains "enters abilities of the copied" &&
    (mshRuling 468).comment.contains "exactly what was printed" &&
    (mshRuling 656).comment.contains "exactly what was printed"

#guard copyTokenEntersAbilitiesOk

/-- Rulings 36 / 46 / 48 / 66 / 116 / 117 / 278 / 279 / 303: a stack-ability
copy keeps mode, divided damage, and the original source. -/
def copyStackAbilityDetailsOk : Bool :=
  let g := addPermanent afterDraw aerialDoombot ⟨0⟩ ⟨0⟩
  let src := namedPermanent g "Aerial Doombot"
  let (g, ab) := g.allocStackAbility src ⟨0⟩
    (triggeredAbility := some (.onEnterDraw 1))
  let g := g.putStackEntry ⟨0⟩ ab.id
  let g :=
    match g.stack.findIdx? (fun e => e.objectId == ab.id) with
    | none => g
    | some i =>
      { g with stack := g.stack.set! i { g.stack[i]! with
        targets := #[Target.player ⟨1⟩]
        dividedDamage := #[2, 1]
        chosenMode := some 1 } }
  let g := g.copyStackAbility (g.object! ab.id) ⟨0⟩
  let copies := g.objects.filter (fun o =>
    o.zone == .stack && o.isCopy && o.sourceId == some src.id)
  let last := g.stack.back!
  copies.size == 1 &&
    copies[0]!.sourceId == some src.id &&
    last.chosenMode == some 1 &&
    last.dividedDamage == #[2, 1] &&
    last.targets.size == 1 &&
    (mshRuling 391).comment.contains "choices will be made separately" &&
    (mshRuling 400).comment.contains "division can't be changed" &&
    (mshRuling 402).comment.contains "same mode" &&
    (mshRuling 419).comment.contains "can't choose to pay any activation" &&
    (mshRuling 469).comment.contains "not just one with targets" &&
    (mshRuling 470).comment.contains "doesn't cause any object to gain" &&
    (mshRuling 630).comment.contains "not just one with targets" &&
    (mshRuling 631).comment.contains "doesn't cause any object to gain" &&
    (mshRuling 655).comment.contains "same as the source of the original"

#guard copyStackAbilityDetailsOk

/-- Rulings 134 / 183 / 327: Hulkling re-checks on resolve, multiple
enters trigger separately, and a swapped greater stat still counts. -/
def hulklingRecheckOk : Bool :=
  let g := mshEnter afterDraw hulklingBurgeoningBruiser
  let g := addPermanent g hillGiant ⟨0⟩ ⟨0⟩
  let giant := namedPermanent g "Hill Giant"
  let hulkling := namedPermanent g "Hulkling, Burgeoning Bruiser"
  let gShrink := g.pumpPermanent giant (-2) (-2)
  let gShrink := gShrink.applyModeledTrigger ⟨0⟩ (.onWatch Effect.watchHulklingCompare)
    (some hulkling.id) #[Target.permanent giant.id]
  (namedPermanent gShrink "Hulkling, Burgeoning Bruiser").status.plusOnePlusOne == 0 &&
    (let g := addPermanent g hillGiant ⟨0⟩ ⟨0⟩
     let g := addPermanent g hillGiant ⟨0⟩ ⟨0⟩
     let hulkling := namedPermanent g "Hulkling, Burgeoning Bruiser"
     let giants := g.battlefield.filter (fun o => o.name == "Hill Giant")
     let g := g.applyModeledTrigger ⟨0⟩ (.onWatch Effect.watchHulklingCompare)
       (some hulkling.id) #[Target.permanent giants[0]!.id]
     let g := g.applyModeledTrigger ⟨0⟩ (.onWatch Effect.watchHulklingCompare)
       (some hulkling.id) #[Target.permanent giants[1]!.id]
     (namedPermanent g "Hulkling, Burgeoning Bruiser").status.plusOnePlusOne == 1) &&
    (let g := mshEnter afterDraw hulklingBurgeoningBruiser
     let g := addPermanent g aerialDoombot ⟨0⟩ ⟨0⟩
     let bot := namedPermanent g "Aerial Doombot"
     let g := g.mapObjectStatus bot (fun s => { s with setBasePT := some (1, 4) })
     let hulkling := namedPermanent g "Hulkling, Burgeoning Bruiser"
     let g := g.mapObjectStatus hulkling (fun s => { s with setBasePT := some (4, 3) })
     let hulkling := namedPermanent g "Hulkling, Burgeoning Bruiser"
     let g := g.applyModeledTrigger ⟨0⟩ (.onWatch Effect.watchHulklingCompare)
       (some hulkling.id) #[Target.permanent bot.id]
     (namedPermanent g "Hulkling, Burgeoning Bruiser").status.plusOnePlusOne == 1) &&
    (mshRuling 487).comment.contains "stat comparison will happen again" &&
    (mshRuling 535).comment.contains "trigger multiple times" &&
    (mshRuling 679).comment.contains "stat that's greater changes"

#guard hulklingRecheckOk

/-- Rulings 112 / 293: damage is tracked through indestructible; deathtouch
is checked only on the first SBA pass after the damage. -/
def doctorDoomDamageTrackedOk : Bool :=
  let g := addPermanent afterDraw doctorDoom ⟨0⟩ ⟨0⟩
  let doom := namedPermanent g "Doctor Doom"
  let g := g.mapObjectStatus doom (·.grantUntilEot Keyword.indestructible)
  let doom := namedPermanent g "Doctor Doom"
  let g := g.markDamageOn doom 3 "Doctor Doom is dealt 3"
  let g := g.checkSBA
  onBattlefield g "Doctor Doom" &&
    (namedPermanent g "Doctor Doom").status.damage == 3 &&
    (let doom := namedPermanent g "Doctor Doom"
     let g := g.mapObjectStatus doom (fun s =>
       { s with untilEotKeywords := Keywords.none })
     let g := g.checkSBA
     !onBattlefield g "Doctor Doom") &&
    (let g := addPermanent afterDraw doctorDoom ⟨0⟩ ⟨0⟩
     let doom := namedPermanent g "Doctor Doom"
     let g := g.mapObjectStatus doom (·.grantUntilEot Keyword.indestructible)
     let doom := namedPermanent g "Doctor Doom"
     let g := g.markDamageOn doom 1 "deathtouch" (deathtouch := true)
     let g := g.checkSBA
     onBattlefield g "Doctor Doom" &&
       !(namedPermanent g "Doctor Doom").status.dealtDeathtouch &&
       (let doom := namedPermanent g "Doctor Doom"
        let g := g.mapObjectStatus doom (fun s =>
          { s with untilEotKeywords := Keywords.none })
        let g := g.checkSBA
        onBattlefield g "Doctor Doom")) &&
    (mshRuling 465).comment.contains "tracked even if he has indestructible" &&
    (mshRuling 645).comment.contains "first time that state-based actions"

#guard doctorDoomDamageTrackedOk

/-- Rulings 145 / 190: Wasp leaving before resolve still taps; later granted
abilities are kept after printed abilities are lost. -/
def wondrousWaspLoseAbilitiesOk : Bool :=
  let g := addPermanent afterDraw theWondrousWasp ⟨0⟩ ⟨0⟩
  let g := addPermanent g stormWindrider ⟨0⟩ ⟨0⟩
  let wasp := namedPermanent g "The Wondrous Wasp"
  let storm := namedPermanent g "Storm, Windrider"
  let (g, _) := g.move wasp.id (.graveyard ⟨0⟩) none
  let g := g.applyTriggeredAbility ⟨0⟩ (.onEnter Effect.enterTapLoseAbilitiesWhileSource)
    (some wasp.id) #[Target.permanent storm.id]
  (namedPermanent g "Storm, Windrider").status.tapped &&
    g.hasFlying (namedPermanent g "Storm, Windrider") &&
    (let g := addPermanent afterDraw theWondrousWasp ⟨0⟩ ⟨0⟩
     let g := addPermanent g stormWindrider ⟨0⟩ ⟨0⟩
     let wasp := namedPermanent g "The Wondrous Wasp"
     let storm := namedPermanent g "Storm, Windrider"
     let g := g.applyTriggeredAbility ⟨0⟩ (.onEnter Effect.enterTapLoseAbilitiesWhileSource)
       (some wasp.id) #[Target.permanent storm.id]
     let storm := namedPermanent g "Storm, Windrider"
     storm.status.tapped &&
       !g.hasFlying storm &&
       (let g := g.mapObjectStatus storm (·.grantUntilEot Keyword.flying)
        g.hasFlying (namedPermanent g "Storm, Windrider"))) &&
    (mshRuling 498).comment.contains "won't lose its abilities" &&
    (mshRuling 542).comment.contains "will keep that ability"

#guard wondrousWaspLoseAbilitiesOk

/-- Ruling 496: Super Hero Civil War leaving skips the control change. -/
def superHeroCivilWarLeaveOk : Bool :=
  let g := addPermanent afterDraw theSuperHeroCivilWar ⟨0⟩ ⟨0⟩
  let g := addPermanent g grizzlyBears ⟨1⟩ ⟨1⟩
  let saga := namedPermanent g "The Super Hero Civil War"
  let bears := namedPermanent g "Grizzly Bears"
  let (g, _) := g.move saga.id (.graveyard ⟨0⟩) none
  let g := g.applyChapterEffect ⟨0⟩ (Effect.chapterGainControlOfUpToTwoCreaturesTotalMvAtMost 6)
    (some saga.id) #[Target.permanent bears.id]
  (namedPermanent g "Grizzly Bears").controlledBy ⟨1⟩ &&
    (let g := addPermanent afterDraw theSuperHeroCivilWar ⟨0⟩ ⟨0⟩
     let g := addPermanent g grizzlyBears ⟨1⟩ ⟨1⟩
     let saga := namedPermanent g "The Super Hero Civil War"
     let bears := namedPermanent g "Grizzly Bears"
     let g := g.applyChapterEffect ⟨0⟩ (Effect.chapterGainControlOfUpToTwoCreaturesTotalMvAtMost 6)
       (some saga.id) #[Target.permanent bears.id]
     (namedPermanent g "Grizzly Bears").controlledBy ⟨0⟩) &&
    (mshRuling 496).comment.contains "won't gain control"

#guard superHeroCivilWarLeaveOk

/-- Ruling 504: an artifact Villain entering fires HYDRA Assault Robot once. -/
def hydraAssaultOnceOk : Bool :=
  let g := addPermanent afterDraw hYDRAAssaultRobot ⟨0⟩ ⟨0⟩
  let g := addPermanent g ultronDrone ⟨0⟩ ⟨0⟩
  let drone := namedPermanent g "Ultron Drone"
  let g := g.afterPermanentEnters drone
  let n :=
    (g.waitingTriggers.filter (fun (t : WaitingTrigger) =>
      t.source.name == "HYDRA Assault Robot")).size
  n == 1 &&
    (mshRuling 504).comment.contains "trigger only once"

#guard hydraAssaultOnceOk

/-- Ruling 669: token creatures dying do not trigger Robot Domination. -/
def robotDominationTokenOk : Bool :=
  let g := addPermanent afterDraw robotDomination ⟨0⟩ ⟨0⟩
  let (g, tok) := g.createToken ⟨0⟩ Game.soldier11whiteToken
  let (g, _) := g.move tok.id (.graveyard ⟨0⟩) none
  !g.waitingTriggers.any (fun (t : WaitingTrigger) =>
    t.event == TriggerEvent.creatureCardsPutIntoYourGy) &&
    (mshRuling 669).comment.contains "Token creatures"

#guard robotDominationTokenOk

/-- Ruling 649: Avengers Assemble! does not trigger if neither condition
was met. -/
def avengersAssembleNoTriggerOk : Bool :=
  let g := addPermanent afterDraw avengersAssemble ⟨0⟩ ⟨0⟩
  let assem := namedPermanent g "Avengers Assemble!"
  let hand0 := (g.player ⟨0⟩).hand.size
  let g := g.applyTriggeredAbility ⟨0⟩
    (.onEachEndStepDrawIfAttackedOrEnteredSubtype "Hero") (some assem.id)
  (g.player ⟨0⟩).hand.size == hand0 &&
    (mshRuling 649).comment.contains "won't trigger at all"

#guard avengersAssembleNoTriggerOk

/-- Rulings 262 / 263 / 264: becoming a better blocker or shrinking after
the block does not make the attacker unblocked. -/
def blockedStaysBlockedOk : Bool :=
  let g := addPermanent afterDraw grizzlyBears ⟨0⟩ ⟨0⟩
  let g := addPermanent g grayOgre ⟨1⟩ ⟨1⟩
  let bears := namedPermanent g "Grizzly Bears"
  let ogre := namedPermanent g "Gray Ogre"
  let g := g.setObject { bears with status := { bears.status with
    attacking := true, attackingWhom := some ⟨1⟩, blocked := true } }
  let bears := namedPermanent g "Grizzly Bears"
  let g := g.setObject { ogre with status := { ogre.status with
    blocking := #[bears.id] } }
  let g := g.mapObjectStatus (namedPermanent g "Grizzly Bears")
    (·.grantUntilEot Keyword.flying)
  (namedPermanent g "Grizzly Bears").status.blocked &&
    g.hasFlying (namedPermanent g "Grizzly Bears") &&
    (mshRuling 614).comment.contains "won't cause him to become unblocked" &&
    (mshRuling 615).comment.contains "won't cause her to become unblocked" &&
    (mshRuling 616).comment.contains "won't be able to make that block illegal"

#guard blockedStaysBlockedOk

/-- Ruling 615: once Stature is blocked at high power, shrinking her to 1
does not make her unblocked. -/
def statureBlockedThenShrunkOk : Bool :=
  let g := addPermanent afterDraw statureSizeShifter ⟨0⟩ ⟨0⟩
  let g := addPermanent g grizzlyBears ⟨1⟩ ⟨1⟩
  let st := namedPermanent g "Stature, Size Shifter"
  let g := g.setObject { st with status := { st.status with
    plusOnePlusOne := 3, attacking := true, attackingWhom := some ⟨1⟩,
    blocked := true } }
  let st := namedPermanent g "Stature, Size Shifter"
  let bears := namedPermanent g "Grizzly Bears"
  let g := g.setObject { bears with status := { bears.status with
    blocking := #[st.id] } }
  let g := g.mapObjectStatus (namedPermanent g "Stature, Size Shifter")
    (fun s => { s with plusOnePlusOne := 0 })
  let st := namedPermanent g "Stature, Size Shifter"
  g.power st == 1 && g.hasCantBeBlocked st && st.status.blocked &&
    (namedPermanent g "Grizzly Bears").status.blocking == #[st.id]

#guard statureBlockedThenShrunkOk

/-- Ruling 610: multiple lifelink instances are redundant. -/
def yellowjacketLifelinkRedundantOk : Bool :=
  let g := addPermanent afterDraw yellowjacketHeartlessMarauder ⟨0⟩ ⟨0⟩
  let yj := namedPermanent g "Yellowjacket, Heartless Marauder"
  let g := g.mapObjectStatus yj (·.grantUntilEot Keyword.lifelink)
  g.hasLifelink (namedPermanent g "Yellowjacket, Heartless Marauder") &&
    (mshRuling 610).comment.contains "Multiple instances of lifelink"

#guard yellowjacketLifelinkRedundantOk

end Mtg.Engine.MshRulingTests
