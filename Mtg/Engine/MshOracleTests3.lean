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
# Engine behavior for unique Marvel Super Heroes (MSH) judge rulings (part 3)

Third slice of the MSH judge-ruling checks, through the Mind Stone aura return.
-/

namespace Mtg.Engine.MshRulingTests

open Mtg.Engine
open Mtg.Engine.Catalog
open Mtg.Engine.Tests


/-- Ruling 521: Scarlet Witch uses the chosen X when checking mana value. -/
def scarletWitchXManaValueOk : Bool :=
  let g := addPermanent afterDraw theScarletWitch ⟨0⟩ ⟨0⟩
  let (g, spell) := g.allocObject photonBlastBarrage ⟨0⟩ (.hand ⟨0⟩) (some ⟨0⟩)
  let cheap := g.object! spell.id
  let cheap := { cheap with chosenX := some 1 }
  let g := g.setObject cheap
  let costly := { cheap with chosenX := some 2 }
  let start := photonBlastBarrage.manaCost
  let reduced := g.applyCastCostReductions costly photonBlastBarrage start
  let unreduced := g.applyCastCostReductions cheap photonBlastBarrage start
  reduced.manaValue == 2 &&
    unreduced.manaValue == 3 &&
    (mshRuling 521).comment.contains "value chosen for X"

#guard scarletWitchXManaValueOk

/-- Ruling 462: Loki compares mana value to last-known power if he left. -/
def lokiLastKnownPowerOk : Bool :=
  let g := addPermanent afterDraw lokiLaufeyson ⟨0⟩ ⟨0⟩
  let loki := namedPermanent g "Loki Laufeyson"
  let g := g.applyAbilityEffect ⟨0⟩ (Effect.nextInstantSorceryCopyIfMvAtMostSourcePower) #[]
    (some loki.id)
  let (g, _) := g.move loki.id (.graveyard ⟨0⟩) none
  let (g, spell) := g.allocObject lightningBolt ⟨0⟩ .stack (some ⟨0⟩)
  let g := g.putStackEntry ⟨0⟩ spell.id
  let g := g.putCastTriggersOnStack ⟨0⟩ (g.object! spell.id)
  let copies := g.objects.filter (fun o =>
    o.zone == .stack && o.isCopy && o.printed.name == "Lightning Bolt")
  copies.size == 1 &&
    (mshRuling 462).comment.contains "last time he was on the battlefield"

#guard lokiLastKnownPowerOk

/-- Ruling 622: H.E.R.B.I.E. putting a land onto the battlefield is not
playing a land. -/
def herbieLandNotPlayOk : Bool :=
  let g := addToHand afterDraw forest ⟨0⟩
  let played0 := (g.player ⟨0⟩).landsPlayedThisTurn
  let g := addPermanent g hERBIEScoutUnit ⟨0⟩ ⟨0⟩
  let herbie := namedPermanent g "H.E.R.B.I.E. Scout Unit"
  let g := g.applyTriggeredAbility ⟨0⟩ .onEnterDrawMayPutLandTapped (some herbie.id)
  let landId := (g.player ⟨0⟩).hand.findSome? (fun id =>
    match g.findObject? id with
    | some o => if o.printed.isLand then some id else none
    | none => none)
  let g :=
    match landId with
    | some id => mustApply g ⟨0⟩ (.cast id)
    | none => g
  g.battlefield.any (fun o =>
      o.printed.isLand && o.status.tapped && o.status.enteredThisTurn) &&
    (g.player ⟨0⟩).landsPlayedThisTurn == played0 &&
    (mshRuling 622).comment.contains "doesn't count as playing a land"

#guard herbieLandNotPlayOk

/-- Ruling 499 / 312: Tigra does not get a counter in time to survive
simultaneous lethal damage, and life gain is one event. -/
def tigraLethalLifeOk : Bool :=
  let g := addPermanent afterDraw tigraFelineFury ⟨0⟩ ⟨0⟩
  let tigra := namedPermanent g "Tigra, Feline Fury"
  let g := g.markDamageOn tigra 1 "Tigra is dealt 1"
  let g := g.gainLife ⟨0⟩ 3
  let g := g.checkSBA
  !onBattlefield g "Tigra, Feline Fury" &&
    (mshRuling 499).comment.contains "won't receive a counter" &&
    (mshRuling 664).comment.contains "just once"

#guard tigraLethalLifeOk

/-- Ruling 647: Thunderbolts returns a Villain as a Hero from the moment
it enters. -/
def thunderboltsHeroTypeOk : Bool :=
  let g := addPermanent afterDraw thunderboltsConspiracy ⟨0⟩ ⟨0⟩
  let g := addPermanent g agentsOfHYDRA ⟨0⟩ ⟨0⟩
  let villain := namedPermanent g "Agents of HYDRA"
  let (g, _) := g.move villain.id (.graveyard ⟨0⟩) none
  let gy := namedGraveyardCard g ⟨0⟩ "Agents of HYDRA"
  let before := g.waitingTriggers.size
  let g := g.applyModeledTrigger ⟨0⟩ (.onDeath Effect.deathVillainReturnAsHero)
    (some (namedPermanent g "Thunderbolts Conspiracy").id) #[Target.card gy.id]
  let o := namedPermanent g "Agents of HYDRA"
  g.hasSubtype o "Hero" &&
    o.status.finality == 1 &&
    g.waitingTriggers.size >= before &&
    (mshRuling 647).comment.contains "Hero in addition to its other types"

#guard thunderboltsHeroTypeOk

/-- Ruling 497: The Void attacks if able, but not while sick, tapped, or
if attacking would require an unpaid cost. -/
def theVoidAttacksIfAbleOk : Bool :=
  let (g, tok) := afterDraw.createToken ⟨0⟩ Game.theVoidToken
  Game.hasAttacksIfAble tok &&
    !g.mustAttackIfAble tok &&
    (let g := g.mapObjectStatus tok (fun s => { s with summoningSick := false })
     let tok := g.object! tok.id
     g.mustAttackIfAble tok &&
       (let g := g.mapObjectStatus tok (fun s => { s with tapped := true })
        !g.mustAttackIfAble (g.object! tok.id) &&
          !g.mustAttackIfAble tok (attackRequiresCost := true))) &&
    (mshRuling 497).comment.contains "doesn't attack"

#guard theVoidAttacksIfAbleOk

/-- Rulings 107 / 108 / 123 / 239 / 248 / 250 / 251 / 260 / 269 / 271 / 282 /
285 / 311 / 339: a spell that targets a creature you control queues those
cast triggers once, above the spell. Madame Hydra queues on a Villain
spell. Loki (247) queues when an ability you control gets a target. -/
def castTriggerBeforeSpellOk : Bool :=
  let g := addPermanent afterDraw colleenWingStreetSamurai ⟨0⟩ ⟨0⟩
  let g := addPermanent g ironFistLivingWeapon ⟨0⟩ ⟨0⟩
  let g := addPermanent g mockingbirdAceAgent ⟨0⟩ ⟨0⟩
  let g := addPermanent g msMarvelKamalaKhan ⟨0⟩ ⟨0⟩
  let g := addPermanent g madameHydra ⟨0⟩ ⟨0⟩
  let g := addPermanent g lokiGodOfMischief ⟨0⟩ ⟨0⟩
  let g := addPermanent g grizzlyBears ⟨0⟩ ⟨0⟩
  let bears := namedPermanent g "Grizzly Bears"
  let (g, spell) := g.allocObject helicarrierStrike ⟨0⟩ .stack (some ⟨0⟩)
  let g := g.putStackEntry ⟨0⟩ spell.id
  let g :=
    match g.stack.findIdx? (fun e => e.objectId == spell.id) with
    | none => g
    | some i =>
      { g with stack := g.stack.set! i { g.stack[i]! with
          targets := #[Target.permanent bears.id] } }
  let g := g.putCastTriggersOnStack ⟨0⟩ (g.object! spell.id)
  let names :=
    (g.waitingTriggers.map (fun (t : WaitingTrigger) => t.source.name))
  names.any (· == "Colleen Wing, Street Samurai") &&
    names.any (· == "Iron Fist, Living Weapon") &&
    names.any (· == "Mockingbird, Ace Agent") &&
    names.any (· == "Ms. Marvel, Kamala Khan") &&
    !names.any (· == "Madame Hydra") &&
    g.objects.any (fun o => o.id == spell.id && o.zone == .stack) &&
    (let (gV, villain) := g.allocObject agentsOfHYDRA ⟨0⟩ .stack (some ⟨0⟩)
     let gV := gV.putStackEntry ⟨0⟩ villain.id
     let gV := gV.putCastTriggersOnStack ⟨0⟩ (gV.object! villain.id)
     (gV.waitingTriggers.map (fun (t : WaitingTrigger) => t.source.name)).any
       (· == "Madame Hydra") &&
       gV.objects.any (fun o => o.id == villain.id && o.zone == .stack)) &&
    (let (gAb, ab) := g.allocObject helicarrierStrike ⟨0⟩ .stack (some ⟨0⟩)
     let gAb := gAb.setObject { ab with
       abilityEffect := some (Effect.dealDamageToTargetCreature 1) }
     let gAb := gAb.putStackEntry ⟨0⟩ ab.id
     let gAb := gAb.queueYouTargetTriggers ⟨0⟩ (gAb.object! ab.id)
     gAb.waitingTriggers.any (fun (t : WaitingTrigger) =>
         t.source.name == "Loki, God of Mischief") &&
       gAb.objects.any (fun o => o.id == ab.id && o.zone == .stack)) &&
    (mshRuling 460).comment.contains "resolves before the spell" &&
    (mshRuling 461).comment.contains "doesn't trigger multiple times" &&
    (mshRuling 476).comment.contains "doesn't trigger multiple times" &&
    (mshRuling 612).comment.contains "resolves before the spell" &&
    (mshRuling 621).comment.contains "resolves before the spell" &&
    (mshRuling 623).comment.contains "resolves before the spell" &&
    (mshRuling 634).comment.contains "resolves before the spell" &&
    (mshRuling 637).comment.contains "resolves before the spell" &&
    (mshRuling 663).comment.contains "resolves before the spell" &&
    (mshRuling 691).comment.contains "resolves before the spell" &&
    (mshRuling 591).comment.contains "resolves before the spell" &&
    (mshRuling 599).comment.contains "resolves before the ability" &&
    (mshRuling 600).comment.contains "resolves before the spell" &&
    (mshRuling 602).comment.contains "resolves before the spell" &&
    (mshRuling 603).comment.contains "resolves before the spell"

#guard castTriggerBeforeSpellOk

/-- Rulings 41 / 53 / 126: one life-gaining event triggers Tigra once. -/
def lifeGainOnceOk : Bool :=
  let g := addPermanent afterDraw tigraFelineFury ⟨0⟩ ⟨0⟩
  let g := g.gainLife ⟨0⟩ 5
  let n :=
    (g.waitingTriggers.filter (fun (t : WaitingTrigger) =>
      t.source.name == "Tigra, Feline Fury")).size
  n == 1 &&
    (mshRuling 395).comment.contains "separate life-gaining event" &&
    (mshRuling 406).comment.contains "triggers only once" &&
    (mshRuling 479).comment.contains "just once"

#guard lifeGainOnceOk

/-- Ruling 643: Hawkeye's extra damage is dealt by the original source. -/
def hawkeyeSameSourceOk : Bool :=
  let g := addPermanent afterDraw hawkeyeYoungAvenger ⟨0⟩ ⟨0⟩
  let g := addPermanent g aerialDoombot ⟨0⟩ ⟨0⟩
  let g := addPermanent g grizzlyBears ⟨1⟩ ⟨1⟩
  let src := namedPermanent g "Aerial Doombot"
  let bears := namedPermanent g "Grizzly Bears"
  let hawk := namedPermanent g "Hawkeye, Young Avenger"
  let g := g.dealDamageFrom src.name bears 1 (source := some src)
  (namedPermanent g "Grizzly Bears").status.damage == 1 + g.power hawk &&
    logContains g "Aerial Doombot deals" &&
    (mshRuling 643).comment.contains "same source as the original"

#guard hawkeyeSameSourceOk

/-- Ruling 530: if all of a source's damage is prevented, Hawkeye's extra
damage no longer applies. -/
def hawkeyePreventionSkipsExtraOk : Bool :=
  let g := addPermanent afterDraw hawkeyeYoungAvenger ⟨0⟩ ⟨0⟩
  let g := addPermanent g aerialDoombot ⟨0⟩ ⟨0⟩
  let g := addPermanent g grizzlyBears ⟨1⟩ ⟨1⟩
  let src := namedPermanent g "Aerial Doombot"
  let hawk := namedPermanent g "Hawkeye, Young Avenger"
  let extra := g.power hawk
  let gHit := g.dealDamageFrom src.name (namedPermanent g "Grizzly Bears") 1
    (source := some src)
  (namedPermanent gHit "Grizzly Bears").status.damage == 1 + extra &&
    (let gPrev := g.mapObjectStatus src (fun s =>
        { s with preventDamageGrantedBy := #[src.id] })
     let src := namedPermanent gPrev "Aerial Doombot"
     let gPrev := gPrev.dealDamageFrom src.name (namedPermanent gPrev "Grizzly Bears") 1
       (source := some src)
     (namedPermanent gPrev "Grizzly Bears").status.damage == 0 &&
       gPrev.log.any (fun s => mentions s "prevented")) &&
    (mshRuling 530).comment.contains "chooses an order"

#guard hawkeyePreventionSkipsExtraOk

/-- Ruling 700: The Ruinous Wrecking Crew cannot choose the same mode twice. -/
def wreckingCrewModesOnceOk : Bool :=
  let g := addPermanent afterDraw theRuinousWreckingCrew ⟨0⟩ ⟨0⟩
  let o := namedPermanent g "The Ruinous Wrecking Crew"
  let g := g.mapObjectStatus o (fun s => { s with chosenModes := #[0, 2] })
  let o := namedPermanent g "The Ruinous Wrecking Crew"
  o.status.chosenModes.contains 0 &&
    !o.status.chosenModes.contains 1 &&
    (mshRuling 700).comment.contains "can't choose the same mode"

#guard wreckingCrewModesOnceOk

/-- Ruling 412: tapping an artifact does not turn off its static abilities. -/
def improviseStaticsWhileTappedOk : Bool :=
  let g := addPermanent afterDraw ironheartCleverChampion ⟨0⟩ ⟨0⟩
  let ih := namedPermanent g "Ironheart, Clever Champion"
  let g := g.mapObjectStatus ih (fun s => { s with tapped := true })
  g.spellHasImprovise helicarrierStrike ⟨0⟩ &&
    (namedPermanent g "Ironheart, Clever Champion").status.tapped &&
    (mshRuling 412).comment.contains "won't cause its abilities to stop"

#guard improviseStaticsWhileTappedOk

/-- Ruling 581: tap an artifact for improvise, then it can still be
sacrificed as an additional cost. -/
def improviseThenSacrificeOk : Bool :=
  let (g, tok) := afterDraw.createToken ⟨0⟩ treasureToken
  match g.tapArtifactsForImprovise ⟨0⟩ #[tok.id] with
  | .ok g =>
    (g.object! tok.id).status.tapped &&
      (g.object! tok.id).isOnBattlefield &&
      (mshRuling 581).comment.contains "tap that permanent"
  | .error _ => false

#guard improviseThenSacrificeOk

/-- Ruling 410: a Two-Headed Giant teammate's life gain is not "you gain life". -/
def twoHeadedGiantTeammateLifeOk : Bool :=
  let g := addPermanent afterDraw tigraFelineFury ⟨0⟩ ⟨0⟩
  let g := g.modifyPlayer ⟨0⟩ (fun pl => { pl with teammate := some ⟨1⟩ })
  let g := g.modifyPlayer ⟨1⟩ (fun pl => { pl with teammate := some ⟨0⟩ })
  let g := g.gainLife ⟨1⟩ 3
  !(g.waitingTriggers.any (fun (t : WaitingTrigger) =>
      t.source.name == "Tigra, Feline Fury")) &&
    (mshRuling 410).comment.contains "Two-Headed Giant"

#guard twoHeadedGiantTeammateLifeOk

/-- Ruling 588: controlling a player in Two-Headed Giant controls the team. -/
def twoHeadedGiantControlTeamOk : Bool :=
  let g := afterDraw.modifyPlayer ⟨1⟩ (fun pl => { pl with teammate := some ⟨0⟩ })
  let g := g.setPlayerControl ⟨0⟩ ⟨1⟩
  g.controlsPlayer ⟨0⟩ ⟨1⟩ &&
    g.controlsPlayer ⟨0⟩ ⟨0⟩ &&
    (mshRuling 588).comment.contains "gain control of each player"

#guard twoHeadedGiantControlTeamOk

/-- Ruling 459 / 239: each targeting spell grants Iron Fist another tap
ability; the trigger waits above the spell. -/
def ironFistMultipleGrantsOk : Bool :=
  let g := addPermanent afterDraw ironFistLivingWeapon ⟨0⟩ ⟨0⟩
  let g := addPermanent g grizzlyBears ⟨0⟩ ⟨0⟩
  let fist := namedPermanent g "Iron Fist, Living Weapon"
  let g := g.applyModeledTrigger ⟨0⟩ (.onCasting Effect.castingIronFistTap)
    (some fist.id)
  let g := g.applyModeledTrigger ⟨0⟩ (.onCasting Effect.castingIronFistTap)
    (some fist.id)
  (namedPermanent g "Iron Fist, Living Weapon").status.ironFistTapGrants == 2 &&
    (mshRuling 459).comment.contains "multiple instances"

#guard ironFistMultipleGrantsOk

/-- Ruling 522: an Aura returns without targeting and can attach through
hexproof. -/
def mindStoneAuraReturnOk : Bool :=
  let g := addPermanent afterDraw theMindStone ⟨0⟩ ⟨0⟩
  let g := addPermanent g superSoldierSerum ⟨0⟩ ⟨0⟩
  let g := addPermanent g grizzlyBears ⟨0⟩ ⟨0⟩
  let aura := namedPermanent g "Super-Soldier Serum"
  let bears := namedPermanent g "Grizzly Bears"
  let g := g.mapObjectStatus bears (·.grantUntilEot Keyword.hexproof)
  let (g, _) := g.move aura.id .exile none
  let ex :=
    (g.objects.find? (fun o => o.name == "Super-Soldier Serum" && o.zone == .exile)).getD aura
  let g := g.returnExiledId ex.id
  let aura := namedPermanent g "Super-Soldier Serum"
  aura.attachedTo == some (namedPermanent g "Grizzly Bears").id &&
    g.log.any (fun s => mentions s "does not target") &&
    (mshRuling 522).comment.contains "doesn't target anything"

#guard mindStoneAuraReturnOk

end Mtg.Engine.MshRulingTests
