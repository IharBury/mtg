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
import Mtg.Engine.Tests.Abilities
import Mtg.Engine.Tests.Effects

/-!
# MSH connive, teamwork, Power-up, wards, and remaining catalog interactions.
-/

namespace Mtg.Engine.Tests

open Mtg.Engine
open Mtg.Engine.Catalog

/-! ## Marvel Super Heroes (MSH) -/

#guard mshCards.size == 286
#guard mshCards.all (·.matchesOracleText)
#guard supportedCatalogCards.any (fun c => c.name == "Brave Brawler")
#guard supportedCatalogCards.any (fun c => c.name == "Jennifer Walters")
#guard supportedCatalogCards.any (fun c => c.name == "The Sensational She-Hulk")
#guard supportedCatalogCards.any (fun c => c.name == "Stature, Size Shifter")
#guard statureSizeShifter.staticAbilities == #[StaticAbility.cantBeBlockedIfPowerAtMost 1]
#guard statureSizeShifter.activatedAbilities[0]!.effect == Effect.plusOneX
#guard statureSizeShifter.activatedAbilities[0]!.powerUp
#guard statureSizeShifter.activatedAbilities[0]!.cost.mana ==
  ({ symbols := #[.x, .colored .blue, .colored .blue] } : ManaCost)

/-- Put `card` onto the battlefield and run enters replacements (shield, power-up). -/
def mshEnter (g : Game) (card : CardDef) : Game :=
  let g := addPermanent g card ⟨0⟩ ⟨0⟩
  let o := namedPermanent g card.name
  (g.afterPermanentEnters o).receivePriority ⟨0⟩

/-- Power-up costs are reduced by the creature's mana cost if it entered this turn
(CR 702.193b). `{4}{W}` minus Brave Brawler's `{1}{W}` is `{3}`. -/
def brawlerEntered : Game := mshEnter afterDraw braveBrawler

#guard (namedPermanent brawlerEntered "Brave Brawler").status.enteredThisTurn
#guard
  let o := namedPermanent brawlerEntered "Brave Brawler"
  let ab := o.printed.activatedAbilities[0]!
  ab.powerUp &&
    brawlerEntered.activationManaCost ⟨0⟩ ab (some o) ==
      ({ symbols := #[.generic 3] } : ManaCost)

/-- Without the enters-this-turn flag the power-up cost is printed. -/
def brawlerNoEnterFlag : Game := addPermanent afterDraw braveBrawler ⟨0⟩ ⟨0⟩

#guard !(namedPermanent brawlerNoEnterFlag "Brave Brawler").status.enteredThisTurn
#guard
  let o := namedPermanent brawlerNoEnterFlag "Brave Brawler"
  let ab := o.printed.activatedAbilities[0]!
  brawlerNoEnterFlag.activationManaCost ⟨0⟩ ab (some o) ==
    ({ symbols := #[.generic 4, .colored .white] } : ManaCost)

/-- Captain America enters with a shield counter (CR 122.1 / 702.193-adjacent). -/
def capEntered : Game := mshEnter afterDraw captainAmericaSuperSoldier

#guard (namedPermanent capEntered "Captain America, Super-Soldier").status.shield == 1
#guard capEntered.log.any (fun s => mentions s "shield counter")

/-- Advance by idle actions until Baron Strucker's optional connive is pending. -/
def skipToMayHaveVillainConnive (g : Game) : Nat → Game
  | 0 => panic! "skipToMayHaveVillainConnive fuel exhausted"
  | n + 1 =>
    match g.pending with
    | .mayHaveVillainConnive .. => g
    | _ =>
      if g.over then panic! "game over while waiting for Baron Strucker"
      else skipToMayHaveVillainConnive (applyIdle g) n

/-- Baron Strucker asks whether the entering Villain connives (MSH 422). -/
def struckerMayConnive : Game :=
  let g := addToHand afterDraw lightningBolt ⟨0⟩
  let g := addPermanent g baronStruckerHYDRAOverlord ⟨0⟩ ⟨0⟩
  let g := addPermanent g redGuardianSuperSoldier ⟨0⟩ ⟨0⟩
  let g := g.afterPermanentEnters (namedPermanent g "Red Guardian, Super-Soldier")
  skipToMayHaveVillainConnive (g.receivePriority ⟨0⟩) 24

#guard
  match struckerMayConnive.pending with
  | .mayHaveVillainConnive ⟨0⟩ src vid =>
    src == (namedPermanent struckerMayConnive "Baron Strucker, HYDRA Overlord").id &&
      vid == (namedPermanent struckerMayConnive "Red Guardian, Super-Soldier").id
  | _ => false
#guard struckerMayConnive.actor == some ⟨0⟩
#guard !struckerMayConnive.hasPriority ⟨0⟩
#guard struckerMayConnive.log.any (fun s => mentions s "may have Red Guardian")
#guard
  match Agent.choose struckerMayConnive ⟨0⟩ with
  | some .haveVillainConnive => true
  | _ => false

def struckerConnived : Game :=
  mustApply struckerMayConnive ⟨0⟩ .haveVillainConnive

#guard (namedPermanent struckerConnived "Baron Strucker, HYDRA Overlord").status.optionalOnceUsed
#guard (struckerConnived.player ⟨0⟩).hand.size ==
  (struckerMayConnive.player ⟨0⟩).hand.size + 1
#guard struckerConnived.log.any (fun s => mentions s "connives")

def struckerDeclinedConnive : Game :=
  mustApply struckerMayConnive ⟨0⟩ .decline

#guard !(namedPermanent struckerDeclinedConnive "Baron Strucker, HYDRA Overlord").status.optionalOnceUsed
#guard (struckerDeclinedConnive.player ⟨0⟩).hand.size ==
  (struckerMayConnive.player ⟨0⟩).hand.size
#guard struckerDeclinedConnive.log.any (fun s => mentions s "declines to have the Villain connive")

/-- A.I.M. Scientists connives on enter: draw, then discard. -/
def scientistsConnive : Game := settle (mshEnter afterDraw aIMScientists) 24

#guard scientistsConnive.log.any (fun s => mentions s "draws")
#guard (scientistsConnive.player ⟨0⟩).hand.size == 7

/-- Agent 13 investigates when a creature you control attacks alone. -/
def agentAttacksAlone : Game :=
  let g := mshEnter afterDraw agent13SharonCarter
  let g := addPermanent g grizzlyBears ⟨0⟩ ⟨0⟩
  let g := passBoth (skipTo g .beginningOfCombat 80)
  let g := mustApply g ⟨0⟩
    (.declareAttackers #[(namedPermanent g "Grizzly Bears").id])
  settle (passBoth g) 40

#guard agentAttacksAlone.battlefield.any (fun o => o.name == "Clue")
#guard agentAttacksAlone.log.any (fun s => mentions s "investigates")

/-- Claim the Kingdom puts a plan counter when a land enters. -/
def planFromLandfall : Game :=
  let g := mshEnter afterDraw claimTheKingdom
  let g := addPermanent g grizzlyBears ⟨0⟩ ⟨0⟩
  let g := addPermanent g forest ⟨0⟩ ⟨0⟩
  settle ((g.afterLandEnters (namedPermanent g "Forest")).receivePriority ⟨0⟩) 24

#guard (namedPermanent planFromLandfall "Claim the Kingdom").status.plan == 1
#guard (namedPermanent planFromLandfall "Grizzly Bears").status.plusOnePlusOne == 1

/-- Helicarrier Strike announces teamwork and taps a creature of enough power. -/
def teamworkPaidStrike : Game :=
  let g := addPermanent afterDraw grizzlyBears ⟨0⟩ ⟨0⟩
  let g := insertObject g grayOgre ⟨1⟩ .battlefield (some ⟨1⟩)
    { attacking := true, summoningSick := false }
  let g := addToHand g helicarrierStrike ⟨0⟩
  let g := withMana g ⟨0⟩ .white 1
  let g := mustApply g ⟨0⟩ (.cast (handCardNamed g ⟨0⟩ "Helicarrier Strike").id)
  let g := mustApply g ⟨0⟩ (.announceTeamwork true)
  mustApply g ⟨0⟩ (.choosePermanents #[(namedPermanent g "Grizzly Bears").id])

#guard (namedPermanent teamworkPaidStrike "Grizzly Bears").status.tapped
#guard teamworkPaidStrike.log.any (fun s => mentions s "pays a teamwork cost")
#guard
  let g := addPermanent afterDraw grizzlyBears ⟨0⟩ ⟨0⟩
  let g := addPermanent g treasureToken ⟨1⟩ ⟨1⟩
  g.countOpponentArtifacts ⟨0⟩ == 1 &&
    g.countArtifactsControlledBy ⟨1⟩ == 1 &&
    (g.pickTeamworkCreatures ⟨0⟩ 2) == #[(namedPermanent g "Grizzly Bears").id]

/-- Okoye creates two 1/1 white Soldier tokens on enter. -/
def okoyeSoldiers : Game := settle (mshEnter afterDraw okoyeDoraMilajeLeader) 24

#guard
  (okoyeSoldiers.battlefield.filter (fun o =>
    o.name == "Soldier" && o.printed.isToken)).size == 2

/-- Black Panther draws when he deals combat damage. -/
def pantherCombatDraw : Game :=
  let g := addPermanent afterDraw blackPantherHopeEnduring ⟨0⟩ ⟨0⟩
  let o := namedPermanent g "Black Panther, Hope Enduring"
  let g := g.setObject { o with status := { o.status with
    attacking := true, summoningSick := false } }
  settle g.combatDamage 24

#guard (pantherCombatDraw.player ⟨0⟩).hand.size ≥ 8
#guard pantherCombatDraw.log.any (fun s => mentions s "draws")

-- Daredevil looks at the library top; that is a field, not leftover text.
#guard daredevilManWithoutFear.mayLookAtTopAnytime

-- Hidden Lair's second ability is {T}: Add {U} or {B} when it entered
-- this turn or you control a basic land.
#guard hiddenLair.enteredOrBasicAddMana ==
  #[.colored .blue, .colored .black]
#guard hiddenLair.requiresEnteredOrBasicAdd
#guard hiddenLair.manaAbilities.contains (.colored .blue)

def hiddenLairEntered : Game := mshEnter afterDraw hiddenLair

#guard (namedPermanent hiddenLairEntered "Hidden Lair").status.enteredThisTurn
#guard
  hiddenLairEntered.manaAbilitiesOf (namedPermanent hiddenLairEntered "Hidden Lair") ==
    #[.colorless, .colored .blue, .colored .black]

def hiddenLairTappedBlue : Game :=
  mustApply hiddenLairEntered ⟨0⟩
    (.tapForMana (namedPermanent hiddenLairEntered "Hidden Lair").id (.colored .blue))

#guard (namedPermanent hiddenLairTappedBlue "Hidden Lair").status.tapped
#guard (hiddenLairTappedBlue.player ⟨0⟩).manaPool.blue == 1
#guard hiddenLairTappedBlue.log.any (fun s => mentions s "blue")

/-- Without entering this turn or a basic, Hidden Lair taps only for `{C}`. -/
def hiddenLairStuck : Game := addPermanent afterDraw hiddenLair ⟨0⟩ ⟨0⟩

#guard !(namedPermanent hiddenLairStuck "Hidden Lair").status.enteredThisTurn
#guard
  hiddenLairStuck.manaAbilitiesOf (namedPermanent hiddenLairStuck "Hidden Lair") ==
    #[.colorless]
#guard
  match hiddenLairStuck.tapForMana ⟨0⟩
      (namedPermanent hiddenLairStuck "Hidden Lair").id (.colored .blue) with
  | .error msg => mentions msg "entered this turn"
  | .ok _ => false

/-- A basic land you control unlocks Hidden Lair's colored mana. -/
def hiddenLairWithIsland : Game :=
  addUntappedLand (addPermanent afterDraw hiddenLair ⟨0⟩ ⟨0⟩) island

#guard hiddenLairWithIsland.controlsBasicLand ⟨0⟩
#guard
  match hiddenLairWithIsland.tapForMana ⟨0⟩
      (namedPermanent hiddenLairWithIsland "Hidden Lair").id (.colored .blue) with
  | .ok g =>
    (namedPermanent g "Hidden Lair").status.tapped &&
      (g.player ⟨0⟩).manaPool.blue == 1
  | .error _ => false

def hiddenLairWithSwamp : Game :=
  addUntappedLand (addPermanent afterDraw hiddenLair ⟨0⟩ ⟨0⟩) swamp

/-- Propose `card` from hand after putting it there. -/
def proposeFromHand (g : Game) (card : CardDef) : Game :=
  let g := addToHand g card ⟨0⟩
  mustApply g ⟨0⟩ (.cast (handCardNamed g ⟨0⟩ card.name).id)

/-- Hidden Lair entered this turn; `{U}` must come from its colored ability. -/
def hiddenLairPayingDoombot : Game :=
  proposeFromHand hiddenLairEntered aerialDoombot

#guard
  match hiddenLairPayingDoombot.pending with
  | .activateManaAbilities ⟨0⟩ => true
  | _ => false

#guard
  match Agent.chooseManaPayment hiddenLairPayingDoombot ⟨0⟩ with
  | some (.tapForMana id (.colored .blue)) =>
    (hiddenLairPayingDoombot.object! id).name == "Hidden Lair"
  | _ => false

/-- Hidden Lair entered this turn; `{B}` must come from its colored ability. -/
def hiddenLairPayingDeathlok : Game :=
  proposeFromHand hiddenLairEntered projectDeathlokSoldier

#guard
  match Agent.chooseManaPayment hiddenLairPayingDeathlok ⟨0⟩ with
  | some (.tapForMana id (.colored .black)) =>
    (hiddenLairPayingDeathlok.object! id).name == "Hidden Lair"
  | _ => false

/-- Without the colored ability, Hidden Lair cannot pay `{U}`. -/
def hiddenLairStuckPayingDoombot : Game :=
  proposeFromHand hiddenLairStuck aerialDoombot

#guard
  match Agent.chooseManaPayment hiddenLairStuckPayingDoombot ⟨0⟩ with
  | some .pay =>
    !(namedPermanent hiddenLairStuckPayingDoombot "Hidden Lair").status.tapped
  | _ => false

/-- Island already makes `{U}`; Hidden Lair must tap for `{B}` so `{U}{B}`
is still payable. -/
def hiddenLairScientistWithIsland : Game :=
  proposeFromHand hiddenLairWithIsland scientistSupremeOfAIM

#guard
  match hiddenLairScientistWithIsland.proposedSpell with
  | some prop =>
    let lair := namedPermanent hiddenLairScientistWithIsland "Hidden Lair"
    let isl := namedPermanent hiddenLairScientistWithIsland "Island"
    hiddenLairScientistWithIsland.preferredManaType ⟨0⟩ lair
      (hiddenLairScientistWithIsland.manaAbilitiesOf lair) prop.cost false false
      [(isl, hiddenLairScientistWithIsland.manaAbilitiesOf isl)] ==
        some (.colored .black)
  | none => false

#guard
  match Agent.chooseManaPayment hiddenLairScientistWithIsland ⟨0⟩ with
  | some (.tapForMana id (.colored .black)) =>
    (hiddenLairScientistWithIsland.object! id).name == "Hidden Lair"
  | _ => false

/-- Swamp already makes `{B}`; Hidden Lair must tap for `{U}`. -/
def hiddenLairScientistWithSwamp : Game :=
  proposeFromHand hiddenLairWithSwamp scientistSupremeOfAIM

#guard
  match Agent.chooseManaPayment hiddenLairScientistWithSwamp ⟨0⟩ with
  | some (.tapForMana id (.colored .blue)) =>
    (hiddenLairScientistWithSwamp.object! id).name == "Hidden Lair"
  | _ => false

/- Stature, Size Shifter: unblockable at power ≤ 1; power-up puts X +1/+1. -/

def statureInPlay : Game :=
  addPermanent afterDraw statureSizeShifter ⟨0⟩ ⟨0⟩

#guard (namedPermanent statureInPlay "Stature, Size Shifter").printed.power == some 1
#guard statureInPlay.power (namedPermanent statureInPlay "Stature, Size Shifter") == 1
#guard statureInPlay.hasCantBeBlocked (namedPermanent statureInPlay "Stature, Size Shifter")

/-- Stature attacks at 1 power; Bears cannot block. -/
def statureAttacking : Game :=
  let g := addPermanent afterDraw statureSizeShifter ⟨0⟩ ⟨0⟩
  let g := addPermanent g grizzlyBears ⟨1⟩ ⟨1⟩
  let g := passBoth (skipTo g .beginningOfCombat 80)
  mustApply g ⟨0⟩ (.declareAttackers #[(namedPermanent g "Stature, Size Shifter").id])

def statureReadyToBlock : Game := passBoth statureAttacking

#guard statureReadyToBlock.pending == .declareBlockers
#guard !statureReadyToBlock.canBlock
  (namedPermanent statureReadyToBlock "Grizzly Bears")
  (namedPermanent statureReadyToBlock "Stature, Size Shifter")
#guard
  match statureReadyToBlock.apply ⟨1⟩ (.declareBlockers #[(
    (namedPermanent statureReadyToBlock "Grizzly Bears").id,
    (namedPermanent statureReadyToBlock "Stature, Size Shifter").id)]) with
  | .error msg => mentions msg "cannot block"
  | .ok _ => false

/-- After power-up counters, Stature is 4/4 and can be blocked. -/
def staturePumpedInCombat : Game :=
  let g := addPermanent afterDraw statureSizeShifter ⟨0⟩ ⟨0⟩
  let g := addPermanent g grizzlyBears ⟨1⟩ ⟨1⟩
  let o := namedPermanent g "Stature, Size Shifter"
  let g := g.setObject { o with status := { o.status with plusOnePlusOne := 3 } }
  let g := passBoth (skipTo g .beginningOfCombat 80)
  let g := mustApply g ⟨0⟩
    (.declareAttackers #[(namedPermanent g "Stature, Size Shifter").id])
  passBoth g

#guard staturePumpedInCombat.power
  (namedPermanent staturePumpedInCombat "Stature, Size Shifter") == 4
#guard !staturePumpedInCombat.hasCantBeBlocked
  (namedPermanent staturePumpedInCombat "Stature, Size Shifter")
#guard staturePumpedInCombat.canBlock
  (namedPermanent staturePumpedInCombat "Grizzly Bears")
  (namedPermanent staturePumpedInCombat "Stature, Size Shifter")

/-- Stature in play with enough blue to activate `{X}{U}{U}` at X = 3. -/
def statureReady : Game :=
  let g := addPermanent afterDraw statureSizeShifter ⟨0⟩ ⟨0⟩
  withBlueMana (g.modifyPlayer ⟨0⟩ (fun pl => { pl with landsPlayedThisTurn := 1 })) ⟨0⟩ 5

def proposedStature : Game :=
  mustApply statureReady ⟨0⟩ (.activate (namedPermanent statureReady "Stature, Size Shifter").id 0)

#guard proposedStature.pending == .chooseX ⟨0⟩
#guard proposedStature.proposedSpell.isSome
#guard (proposedStature.object! proposedStature.stack.back!.objectId).abilityEffect ==
  some (Effect.plusOneX)
#guard proposedStature.log.any (fun s => mentions s "begins activating Stature")
#guard proposedStature.log.any (fun s => mentions s "must choose a value for X")

def statureXChosen : Game :=
  mustApply proposedStature ⟨0⟩ (.chooseX 3)

#guard statureXChosen.pending == .activateManaAbilities ⟨0⟩
#guard (statureXChosen.object! statureXChosen.stack.back!.objectId).chosenX == some 3
#guard
  match statureXChosen.proposedSpell with
  | some prop =>
    prop.cost == ({ symbols := #[.generic 3, .colored .blue, .colored .blue] } : ManaCost)
  | none => false
#guard statureXChosen.log.any (fun s => mentions s "chooses X = 3")

def paidStature : Game := mustApply statureXChosen ⟨0⟩ .pay

#guard paidStature.hasPriority ⟨0⟩
#guard paidStature.stack.size == 1
#guard (namedPermanent paidStature "Stature, Size Shifter").status.plusOnePlusOne == 0
#guard (namedPermanent paidStature "Stature, Size Shifter").status.powerUpUsed
#guard (namedPermanent paidStature "Stature, Size Shifter").status.powerUpActivations == 1

def staturePowerUpResolved : Game := passBoth paidStature

#guard staturePowerUpResolved.stack.isEmpty
#guard (namedPermanent staturePowerUpResolved "Stature, Size Shifter").status.plusOnePlusOne == 3
#guard staturePowerUpResolved.power
  (namedPermanent staturePowerUpResolved "Stature, Size Shifter") == 4
#guard staturePowerUpResolved.toughness
  (namedPermanent staturePowerUpResolved "Stature, Size Shifter") == 4
#guard !staturePowerUpResolved.hasCantBeBlocked
  (namedPermanent staturePowerUpResolved "Stature, Size Shifter")
#guard staturePowerUpResolved.log.any (fun s =>
  mentions s "Stature, Size Shifter gets 3 +1/+1 counters")

/-- Entered this turn, `{X}{U}{U}` minus `{U}` is `{X}{U}`. -/
def statureEntered : Game := mshEnter afterDraw statureSizeShifter

#guard (namedPermanent statureEntered "Stature, Size Shifter").status.enteredThisTurn
#guard
  let o := namedPermanent statureEntered "Stature, Size Shifter"
  let ab := o.printed.activatedAbilities[0]!
  statureEntered.activationManaCost ⟨0⟩ ab (some o) ==
    ({ symbols := #[.x, .colored .blue] } : ManaCost)
#guard
  let o := namedPermanent statureEntered "Stature, Size Shifter"
  let ab := o.printed.activatedAbilities[0]!
  let cost :=
    statureEntered.activationManaCost ⟨0⟩ ab (source := some o) (chosenX := some 2)
  cost == ({ symbols := #[.generic 2, .colored .blue] } : ManaCost)

/-- Power-up is used after activation even if X is 0. -/
def statureXZeroUsed : Game :=
  let g := mustApply proposedStature ⟨0⟩ (.chooseX 0)
  mustApply g ⟨0⟩ .pay

#guard (namedPermanent statureXZeroUsed "Stature, Size Shifter").status.powerUpUsed
#guard
  let o := namedPermanent statureXZeroUsed "Stature, Size Shifter"
  !statureXZeroUsed.canActivate ⟨0⟩ o o.printed.activatedAbilities[0]!

/- Empty-spec statics and unused `cantBeBlockedByPowerAtLeast` actually apply. -/

/-- Attach `eqName` to `hostName`. -/
def attachNamed (g : Game) (eqName hostName : String) : Game :=
  g.attachSourceTo (namedPermanent g eqName) (namedPermanent g hostName)

/-- Thranduil the Strategist: other Elves have `{T}: Add {G} or {U}`. -/
def thranduilGrantsElfMana : Game :=
  addPermanent (addPermanent afterDraw thranduilTheStrategist ⟨0⟩ ⟨0⟩)
    llanowarElves ⟨0⟩ ⟨0⟩

#guard
  let elf := namedPermanent thranduilGrantsElfMana "Llanowar Elves"
  (thranduilGrantsElfMana.manaAbilitiesOf elf).contains (.colored .green) &&
    (thranduilGrantsElfMana.manaAbilitiesOf elf).contains (.colored .blue)
#guard
  let th := namedPermanent thranduilGrantsElfMana "Thranduil the Strategist"
  !(thranduilGrantsElfMana.manaAbilitiesOf th).contains (.colored .blue)

def thranduilElfTappedBlue : Game :=
  mustApply thranduilGrantsElfMana ⟨0⟩
    (.tapForMana (namedPermanent thranduilGrantsElfMana "Llanowar Elves").id
      (.colored .blue))

#guard (namedPermanent thranduilElfTappedBlue "Llanowar Elves").status.tapped
#guard (thranduilElfTappedBlue.player ⟨0⟩).manaPool.blue == 1

/-- Thorin: other Dwarves get +1/+0 per artifact token. -/
def thorinWithMauler : Game :=
  let g := addPermanent afterDraw thorinKingOfDurinsFolk ⟨0⟩ ⟨0⟩
  let g := addPermanent g dwarvenMauler ⟨0⟩ ⟨0⟩
  g.createTreasureTokens ⟨0⟩ 2

#guard thorinWithMauler.power (namedPermanent thorinWithMauler "Dwarven Mauler") == 4
#guard thorinWithMauler.toughness (namedPermanent thorinWithMauler "Dwarven Mauler") == 1
#guard thorinWithMauler.power
  (namedPermanent thorinWithMauler "Thorin, King of Durin's Folk") == 4

/-- Bilbo can't be blocked by power 3 or greater. -/
def bilboReadyToBlock : Game :=
  let g := addPermanent afterDraw bilboUnexpectedAdventurer ⟨0⟩ ⟨0⟩
  let g := addPermanent g hillGiant ⟨1⟩ ⟨1⟩
  let g := addPermanent g grizzlyBears ⟨1⟩ ⟨1⟩
  let g := passBoth (skipTo g .beginningOfCombat 80)
  let g := mustApply g ⟨0⟩
    (.declareAttackers #[(namedPermanent g "Bilbo, Unexpected Adventurer").id])
  passBoth g

#guard !bilboReadyToBlock.canBlock
  (namedPermanent bilboReadyToBlock "Hill Giant")
  (namedPermanent bilboReadyToBlock "Bilbo, Unexpected Adventurer")
#guard bilboReadyToBlock.canBlock
  (namedPermanent bilboReadyToBlock "Grizzly Bears")
  (namedPermanent bilboReadyToBlock "Bilbo, Unexpected Adventurer")
#guard
  match bilboReadyToBlock.apply ⟨1⟩ (.declareBlockers #[(
    (namedPermanent bilboReadyToBlock "Hill Giant").id,
    (namedPermanent bilboReadyToBlock "Bilbo, Unexpected Adventurer").id)]) with
  | .error msg => mentions msg "cannot block"
  | .ok _ => false

/-- Enchanted River's Grasp: loses abilities and doesn't untap. -/
def riverGraspOnGoblin : Game :=
  let g := addPermanent afterDraw enchantedRiverSGrasp ⟨0⟩ ⟨0⟩
  let g := addPermanent g ragingGoblin ⟨1⟩ ⟨1⟩
  attachNamed g "Enchanted River's Grasp" "Raging Goblin"

#guard !riverGraspOnGoblin.hasKeyword
  (namedPermanent riverGraspOnGoblin "Raging Goblin") (·.haste)
#guard riverGraspOnGoblin.hostCantBecomeUntapped
  (namedPermanent riverGraspOnGoblin "Raging Goblin")

def riverGraspOnElf : Game :=
  let g := addPermanent afterDraw enchantedRiverSGrasp ⟨0⟩ ⟨0⟩
  let g := addPermanent g llanowarElves ⟨1⟩ ⟨1⟩
  attachNamed g "Enchanted River's Grasp" "Llanowar Elves"

#guard (riverGraspOnElf.manaAbilitiesOf
  (namedPermanent riverGraspOnElf "Llanowar Elves")).isEmpty

/-- Bilbo's Ring: hexproof and unblockable during your turn only. -/
def bilboRingEquipped : Game :=
  let g := addPermanent afterDraw bilboSRing ⟨0⟩ ⟨0⟩
  let g := addPermanent g grizzlyBears ⟨0⟩ ⟨0⟩
  attachNamed g "Bilbo's Ring" "Grizzly Bears"

#guard bilboRingEquipped.hasHexproof
  (namedPermanent bilboRingEquipped "Grizzly Bears")
#guard bilboRingEquipped.hasCantBeBlocked
  (namedPermanent bilboRingEquipped "Grizzly Bears")
#guard !bilboRingEquipped.canBeTargetedBy ⟨1⟩
  (namedPermanent bilboRingEquipped "Grizzly Bears")

def bilboRingOnNissaTurn : Game :=
  { bilboRingEquipped with activePlayer := ⟨1⟩ }

#guard !bilboRingOnNissaTurn.hasHexproof
  (namedPermanent bilboRingOnNissaTurn "Grizzly Bears")
#guard !bilboRingOnNissaTurn.hasCantBeBlocked
  (namedPermanent bilboRingOnNissaTurn "Grizzly Bears")
#guard bilboRingOnNissaTurn.canBeTargetedBy ⟨1⟩
  (namedPermanent bilboRingOnNissaTurn "Grizzly Bears")

/-- Glamdring: first strike and +1/+0 per instant/sorcery in your graveyard. -/
def glamdringEquipped : Game :=
  let g := addPermanent afterDraw glamdring ⟨0⟩ ⟨0⟩
  let g := addPermanent g grizzlyBears ⟨0⟩ ⟨0⟩
  let g := addToGraveyard g lightningBolt ⟨0⟩
  let g := addToGraveyard g shock ⟨0⟩
  attachNamed g "Glamdring" "Grizzly Bears"

#guard glamdringEquipped.hasFirstStrike
  (namedPermanent glamdringEquipped "Grizzly Bears")
#guard glamdringEquipped.power (namedPermanent glamdringEquipped "Grizzly Bears") == 4
#guard glamdringEquipped.toughness (namedPermanent glamdringEquipped "Grizzly Bears") == 2

/-- My Precious: equipped creature has hexproof and can't be blocked. -/
def myPreciousEquipped : Game :=
  let g := addPermanent afterDraw myPrecious ⟨0⟩ ⟨0⟩
  let g := addPermanent g grizzlyBears ⟨0⟩ ⟨0⟩
  attachNamed g "My Precious" "Grizzly Bears"

#guard myPreciousEquipped.hasHexproof
  (namedPermanent myPreciousEquipped "Grizzly Bears")
#guard myPreciousEquipped.hasCantBeBlocked
  (namedPermanent myPreciousEquipped "Grizzly Bears")

/-- Black Panther prevents all damage that would be dealt to him. -/
def pantherDamagePrevented : Game :=
  let g := addPermanent afterDraw blackPantherHopeEnduring ⟨0⟩ ⟨0⟩
  g.dealDamageToPermanent (namedPermanent g "Black Panther, Hope Enduring") 3

#guard (namedPermanent pantherDamagePrevented "Black Panther, Hope Enduring").status.damage == 0
#guard pantherDamagePrevented.log.any (fun s => mentions s "prevented")

/-- Cast Lightning Bolt at an opponent's permanent and lock in the cost. -/
def boltAt (g : Game) (name : String) : Game :=
  let g := addToHand g lightningBolt ⟨0⟩
  let g := withRedMana g ⟨0⟩ 1
  let g := proposeTargeted g ⟨0⟩ (handCardNamed g ⟨0⟩ "Lightning Bolt").id
    (Target.permanent (namedPermanent g name).id)
  mustApply g ⟨0⟩ .pay

/-- Saruman ward: discard an enchantment, instant, or sorcery or the spell
is countered. -/
def sarumanWardPending : Game :=
  boltAt (addPermanent afterDraw sarumanOfManyColors ⟨1⟩ ⟨1⟩)
    "Saruman of Many Colors"

#guard
  match sarumanWardPending.pending with
  | .payWard p _ .discardEnchantmentInstantOrSorcery => p == ⟨0⟩
  | _ => false

def sarumanWardDeclined : Game :=
  mustApply sarumanWardPending ⟨0⟩ .decline

#guard sarumanWardDeclined.stack.isEmpty
#guard sarumanWardDeclined.log.any (fun s => mentions s "countered")

def sarumanWardPaid : Game :=
  let g := addToHand sarumanWardPending shock ⟨0⟩
  mustApply g ⟨0⟩ (.discard (handCardNamed g ⟨0⟩ "Shock").id)

#guard sarumanWardPaid.stack.any (fun e =>
  (sarumanWardPaid.object! e.objectId).name == "Lightning Bolt")
#guard sarumanWardPaid.log.any (fun s => mentions s "discards Shock")

/-- Sauron ward: sacrifice a legendary artifact or creature. -/
def sauronWardPending : Game :=
  let g := addPermanent afterDraw sauronTheDarkLord ⟨1⟩ ⟨1⟩
  let g := addPermanent g gandalfWanderingWizard ⟨0⟩ ⟨0⟩
  boltAt g "Sauron, the Dark Lord"

#guard
  match sauronWardPending.pending with
  | .payWard p _ .sacrificeLegendary => p == ⟨0⟩
  | _ => false

def sauronWardPaid : Game :=
  mustApply sauronWardPending ⟨0⟩
    (.sacrifice (namedPermanent sauronWardPending "Gandalf, Wandering Wizard").id)

#guard !sauronWardPaid.battlefield.any (fun o => o.name == "Gandalf, Wandering Wizard")
#guard sauronWardPaid.stack.any (fun e =>
  (sauronWardPaid.object! e.objectId).name == "Lightning Bolt")

/-- Printed `ward {3}` on Gandalf. -/
def gandalfWardPending : Game :=
  boltAt (addPermanent afterDraw gandalfWanderingWizard ⟨1⟩ ⟨1⟩)
    "Gandalf, Wandering Wizard"

#guard
  match gandalfWardPending.pending with
  | .payWard p _ (.genericMana 3) => p == ⟨0⟩
  | _ => false

def gandalfWardPaid : Game :=
  let g := gandalfWardPending.modifyPlayer ⟨0⟩ (fun pl =>
    { pl with manaPool := { pl.manaPool with colorless := 3 } })
  mustApply g ⟨0⟩ .payGeneric

#guard gandalfWardPaid.stack.any (fun e =>
  (gandalfWardPaid.object! e.objectId).name == "Lightning Bolt")
#guard gandalfWardPaid.log.any (fun s => mentions s "pays {3}")

/-- Equipped creature has ward {1} (Dwarven Mattock). -/
def mattockWardPending : Game :=
  let g := addPermanent afterDraw dwarvenMattock ⟨1⟩ ⟨1⟩
  let g := addPermanent g dwarvenMauler ⟨1⟩ ⟨1⟩
  let g := attachNamed g "Dwarven Mattock" "Dwarven Mauler"
  boltAt g "Dwarven Mauler"

#guard
  match mattockWardPending.pending with
  | .payWard p _ (.genericMana 1) => p == ⟨0⟩
  | _ => false

/-- Titania: ward — discard a card or pay {2}. -/
def titaniaWardPending : Game :=
  boltAt (addPermanent afterDraw titaniaRuggedRumbler ⟨1⟩ ⟨1⟩)
    "Titania, Rugged Rumbler"

#guard
  match titaniaWardPending.pending with
  | .payWard p _ (.discardOrPay 2) => p == ⟨0⟩
  | _ => false

def titaniaWardDiscarded : Game :=
  let g := addToHand titaniaWardPending forest ⟨0⟩
  mustApply g ⟨0⟩ (.discard (handCardNamed g ⟨0⟩ "Forest").id)

#guard titaniaWardDiscarded.stack.any (fun e =>
  (titaniaWardDiscarded.object! e.objectId).name == "Lightning Bolt")

/-- Titania: additional cost is discard a card or pay {2} (CR 601.2b). -/
def titaniaReady : Game :=
  let g := readyMain (emptyHand afterDraw ⟨0⟩)
  withBlackMana (addToHand (addToHand g titaniaRuggedRumbler ⟨0⟩) forest ⟨0⟩) ⟨0⟩ 4

#guard titaniaReady.canCast ⟨0⟩ (handCardNamed titaniaReady ⟨0⟩ "Titania, Rugged Rumbler")
#guard titaniaRuggedRumbler.announcesAdditionalCost
#guard titaniaRuggedRumbler.additionalCostDiscardOrPayGeneric == some 2

def proposedTitania : Game :=
  mustApply titaniaReady ⟨0⟩
    (.cast (handCardNamed titaniaReady ⟨0⟩ "Titania, Rugged Rumbler").id)

#guard
  match proposedTitania.pending with
  | .chooseAdditionalCost ⟨0⟩ => true
  | _ => false
#guard proposedTitania.log.any (fun s =>
  mentions s "must choose an additional cost (CR 601.2b)")
#guard
  match proposedTitania.apply ⟨0⟩ .pay with
  | .error msg => mentions msg "Choose an additional cost first (CR 601.2b)"
  | .ok _ => false
#guard
  match Agent.choose proposedTitania ⟨0⟩ with
  | some (.chooseAdditionalCost false) => true
  | _ => false

def titaniaDiscardChosen : Game :=
  mustApply proposedTitania ⟨0⟩ (.chooseAdditionalCost false)

#guard
  match titaniaDiscardChosen.proposedSpell with
  | some prop => prop.needsDiscardCard && !prop.needsSacrificeOther &&
      prop.cost.manaValue == titaniaRuggedRumbler.manaValue
  | none => false
#guard titaniaDiscardChosen.pending == .activateManaAbilities ⟨0⟩
#guard titaniaDiscardChosen.log.any (fun s =>
  mentions s "chooses to discard a card as an additional cost (CR 601.2b)")

def titaniaPaidDiscard : Game := mustApply titaniaDiscardChosen ⟨0⟩ .pay

#guard
  match titaniaPaidDiscard.pending with
  | .discardForAdditionalCost ⟨0⟩ => true
  | _ => false
#guard titaniaPaidDiscard.proposedSpell.isSome
#guard !(titaniaPaidDiscard.log.any (fun s => mentions s "casts Titania"))
#guard titaniaPaidDiscard.log.any (fun s => mentions s "must discard a card")

def titaniaCastViaDiscard : Game :=
  mustApply titaniaPaidDiscard ⟨0⟩
    (.discard (handCardNamed titaniaPaidDiscard ⟨0⟩ "Forest").id)

#guard titaniaCastViaDiscard.log.any (fun s => mentions s "casts Titania")
#guard (titaniaCastViaDiscard.handObjects ⟨0⟩).isEmpty
#guard (namedGraveyardCard titaniaCastViaDiscard ⟨0⟩ "Forest").name == "Forest"
#guard titaniaCastViaDiscard.stack.any (fun e =>
  (titaniaCastViaDiscard.object! e.objectId).name == "Titania, Rugged Rumbler")

def titaniaResolvedViaDiscard : Game := passBoth titaniaCastViaDiscard

#guard titaniaResolvedViaDiscard.battlefield.any (fun o =>
  o.name == "Titania, Rugged Rumbler")

def titaniaPayGenericReady : Game :=
  let g := readyMain (emptyHand afterDraw ⟨0⟩)
  withBlackMana (addToHand g titaniaRuggedRumbler ⟨0⟩) ⟨0⟩ 6

#guard
  match titaniaPayGenericReady.apply ⟨0⟩
      (.cast (handCardNamed titaniaPayGenericReady ⟨0⟩ "Titania, Rugged Rumbler").id) with
  | .ok g =>
    (match Agent.choose g ⟨0⟩ with
     | some (.chooseAdditionalCost true) => true
     | _ => false) &&
      (match g.apply ⟨0⟩ (.chooseAdditionalCost false) with
       | .error msg => mentions msg "requires discarding a card"
       | .ok _ => false)
  | .error _ => false

def titaniaPayGenericChosen : Game :=
  let g := mustApply titaniaPayGenericReady ⟨0⟩
    (.cast (handCardNamed titaniaPayGenericReady ⟨0⟩ "Titania, Rugged Rumbler").id)
  mustApply g ⟨0⟩ (.chooseAdditionalCost true)

#guard
  match titaniaPayGenericChosen.proposedSpell with
  | some prop =>
    !prop.needsDiscardCard && !prop.needsSacrificeOther &&
      prop.cost.manaValue == titaniaRuggedRumbler.manaValue + 2
  | none => false
#guard titaniaPayGenericChosen.pending == .activateManaAbilities ⟨0⟩
#guard titaniaPayGenericChosen.log.any (fun s =>
  mentions s "chooses to pay {2} as an additional cost (CR 601.2b)")

def titaniaCastViaPay : Game := mustApply titaniaPayGenericChosen ⟨0⟩ .pay

#guard titaniaCastViaPay.log.any (fun s => mentions s "casts Titania")
#guard titaniaCastViaPay.pending == .none

/-- Ruling 582: casting Titania without paying its mana cost still requires
the mandatory additional cost. -/
def titaniaFreeCastReady : Game :=
  let g := readyMain (emptyHand afterDraw ⟨0⟩)
  let g := addToHand (addToHand g titaniaRuggedRumbler ⟨0⟩) forest ⟨0⟩
  let card := handCardNamed g ⟨0⟩ "Titania, Rugged Rumbler"
  g.setObject { card with playPermission := some {
    player := ⟨0⟩, turnEndsRemaining := 1, withoutManaCost := true } }

def titaniaFreeCastViaDiscard : Game :=
  let g := mustApply titaniaFreeCastReady ⟨0⟩
    (.cast (handCardNamed titaniaFreeCastReady ⟨0⟩ "Titania, Rugged Rumbler").id)
  let g := mustApply g ⟨0⟩ (.chooseAdditionalCost false)
  let g := mustApply g ⟨0⟩ .pay
  mustApply g ⟨0⟩ (.discard (handCardNamed g ⟨0⟩ "Forest").id)

#guard
  match (mustApply titaniaFreeCastReady ⟨0⟩
      (.cast (handCardNamed titaniaFreeCastReady ⟨0⟩
        "Titania, Rugged Rumbler").id)).pending with
  | .chooseAdditionalCost ⟨0⟩ => true
  | _ => false
#guard !(titaniaFreeCastReady.playManaCost
  (handCardNamed titaniaFreeCastReady ⟨0⟩ "Titania, Rugged Rumbler")
  titaniaRuggedRumbler).includesManaPayment
#guard titaniaFreeCastViaDiscard.log.any (fun s => mentions s "casts Titania")
#guard (namedGraveyardCard titaniaFreeCastViaDiscard ⟨0⟩ "Forest").name == "Forest"

/-- The Serpent Society: ward — get five poison counters. -/
def serpentWardPending : Game :=
  boltAt (addPermanent afterDraw theSerpentSociety ⟨1⟩ ⟨1⟩)
    "The Serpent Society"

#guard
  match serpentWardPending.pending with
  | .payWard p _ .fivePoison => p == ⟨0⟩
  | _ => false

def serpentWardPaid : Game :=
  mustApply serpentWardPending ⟨0⟩ .pay

#guard (serpentWardPaid.player ⟨0⟩).poison == 5
#guard serpentWardPaid.stack.any (fun e =>
  (serpentWardPaid.object! e.objectId).name == "Lightning Bolt")

/-- Elven Chorus grants `{T}: Add one mana of any color` to creatures. -/
def chorusGrantsAnyColor : Game :=
  addPermanent (addPermanent afterDraw elvenChorus ⟨0⟩ ⟨0⟩) grizzlyBears ⟨0⟩ ⟨0⟩

#guard
  (chorusGrantsAnyColor.manaAbilitiesOf
    (namedPermanent chorusGrantsAnyColor "Grizzly Bears")).contains (.colored .red)

/-- `applyModeledTrigger` resolves leftover constructors, not Oracle text.
A shared `.draw` trigger must not draw via a `toNotation` fallback. -/
def applyModeledTriggerIgnoresDrawText : Game :=
  afterDraw.applyModeledTrigger ⟨0⟩ (.onEnterDraw 1) none

#guard (applyModeledTriggerIgnoresDrawText.player ⟨0⟩).hand.size ==
  (afterDraw.player ⟨0⟩).hand.size

/-- Colleen Wing: +1/+1 and scry from the leftover constructor, not from
parsing “put a +1/+1 counter” ahead of “Scry”. -/
def colleenWingPlusOneScry : Game :=
  let g := addPermanent afterDraw colleenWingStreetSamurai ⟨0⟩ ⟨0⟩
  let src := namedPermanent g "Colleen Wing, Street Samurai"
  g.applyModeledTrigger ⟨0⟩ (.onCasting Effect.castingPlusOneScry) (some src.id)

#guard (namedPermanent colleenWingPlusOneScry "Colleen Wing, Street Samurai").status.plusOnePlusOne == 1
#guard
  match colleenWingPlusOneScry.pending with
  | .scry p 1 => p == ⟨0⟩
  | _ => false

/-- Super Intelligence draws for the enchanted creature's controller. -/
def enchantedControllerDrawsForHost : Game :=
  let g := addPermanent afterDraw grizzlyBears ⟨1⟩ ⟨1⟩
  let g := addPermanent g superIntelligence ⟨0⟩ ⟨0⟩
  let host := namedPermanent g "Grizzly Bears"
  let aura := namedPermanent g "Super Intelligence"
  let g := g.attachSourceTo aura host
  g.applyModeledTrigger ⟨0⟩ (.onStep Effect.stepEnchantedControllerDraws)
    (some (namedPermanent g "Super Intelligence").id)

#guard (enchantedControllerDrawsForHost.player ⟨1⟩).hand.size ==
  (afterDraw.player ⟨1⟩).hand.size + 1
#guard (enchantedControllerDrawsForHost.player ⟨0⟩).hand.size ==
  (afterDraw.player ⟨0⟩).hand.size

/-- Luke Cage's leftover attack trigger pumps and grants indestructible. -/
def lukeCageAttacksAlone : Game :=
  let g := addPermanent afterDraw lukeCagePowerMan ⟨0⟩ ⟨0⟩
  let src := namedPermanent g "Luke Cage, Power Man"
  g.applyModeledTrigger ⟨0⟩ (.onThisAttack Effect.thisAttackAttacksAlonePlus2Indestructible)
    (some src.id)

#guard (namedPermanent lukeCageAttacksAlone "Luke Cage, Power Man").status.pump == (2, 0)
#guard (namedPermanent lukeCageAttacksAlone "Luke Cage, Power Man").status.untilEotKeywords.indestructible

/-- Mockingbird's leftover constructor puts a +1/+1 on the source. -/
def mockingbirdPlusOneThis : Game :=
  let g := addPermanent afterDraw mockingbirdAceAgent ⟨0⟩ ⟨0⟩
  let src := namedPermanent g "Mockingbird, Ace Agent"
  g.applyModeledTrigger ⟨0⟩ (.onCasting Effect.castingPlusOneThis) (some src.id)

#guard (namedPermanent mockingbirdPlusOneThis "Mockingbird, Ace Agent").status.plusOnePlusOne == 1

/-- Nontoken-Hero modal leftover: soldier mode vs team pump, from the
constructor rather than matching “create a 1/1 white Soldier”. -/
def nontokenHeroModalSoldier : Game :=
  afterDraw.applyModeledTrigger ⟨0⟩ (.onWatch Effect.watchNontokenHeroModal) none

def nontokenHeroModalPump : Game :=
  let g := addPermanent afterDraw grizzlyBears ⟨0⟩ ⟨0⟩
  g.applyModeledTrigger ⟨0⟩ (.onWatch Effect.watchNontokenHeroModal) none #[]
    "This creature" (some 1)

#guard (nontokenHeroModalSoldier.battlefield.filter (fun o =>
  o.printed.isToken && o.printed.hasSubtype "Soldier")).size == 1
#guard (namedPermanent nontokenHeroModalPump "Grizzly Bears").status.pump == (1, 1)

/-- Second-draw drain leftover: each opponent loses 1 and you gain 1. -/
def secondDrawDrain : Game :=
  afterDraw.applyModeledTrigger ⟨0⟩ (.onResource Effect.resourceSecondDrawDrain) none

#guard (secondDrawDrain.player ⟨0⟩).life == (afterDraw.player ⟨0⟩).life + 1
#guard (secondDrawDrain.player ⟨1⟩).life == (afterDraw.player ⟨1⟩).life - 1

/-- Hellcat's leftover death trigger returns her with a +1/+1, no printed
abilities, and haste. -/
def hellcatReturns : Game :=
  let g := addPermanent afterDraw hellcatUndyingVigilante ⟨0⟩ ⟨0⟩
  let src := namedPermanent g "Hellcat, Undying Vigilante"
  let (g, gyId) := g.move src.id (.graveyard ⟨0⟩) none
  g.applyModeledTrigger ⟨0⟩ (.onDeath Effect.deathHellcatReturn) (some gyId)

#guard (namedPermanent hellcatReturns "Hellcat, Undying Vigilante").isOnBattlefield
#guard (namedPermanent hellcatReturns "Hellcat, Undying Vigilante").status.plusOnePlusOne == 1
#guard (namedPermanent hellcatReturns "Hellcat, Undying Vigilante").printed.triggeredAbilities.isEmpty
#guard (namedPermanent hellcatReturns "Hellcat, Undying Vigilante").printed.keywords.haste

/- Hawkeye's Bow: +1/+0 and reach, tap damage, Equip {1}. -/

/-- Attach Hawkeye's Bow to Grizzly Bears. -/
def hawkeyeBowEquipped : Game :=
  let g := addPermanent afterDraw grizzlyBears ⟨0⟩ ⟨0⟩
  addAttachedAura g hawkeyeSBow (namedPermanent g "Grizzly Bears") ⟨0⟩ ⟨0⟩

#guard hawkeyeBowEquipped.power (namedPermanent hawkeyeBowEquipped "Grizzly Bears") == 3
#guard hawkeyeBowEquipped.toughness (namedPermanent hawkeyeBowEquipped "Grizzly Bears") == 2
#guard hawkeyeBowEquipped.hasKeyword
  (namedPermanent hawkeyeBowEquipped "Grizzly Bears") (·.reach)
#guard (namedPermanent hawkeyeBowEquipped "Hawkeye's Bow").attachedTo ==
  some (namedPermanent hawkeyeBowEquipped "Grizzly Bears").id

/-- Reach from the Bow lets a ground creature block a flyer. -/
def flyerVsHawkeyeBow : Game :=
  let g := addPermanent started smaugTheGreatCalamityCard ⟨0⟩ ⟨0⟩
  let g := addPermanent g grizzlyBears ⟨1⟩ ⟨1⟩
  let g := addAttachedAura g hawkeyeSBow (namedPermanent g "Grizzly Bears") ⟨1⟩ ⟨1⟩
  let smaug := namedPermanent g "Smaug, the Great Calamity"
  g.setObject { smaug with status := { smaug.status with attacking := true } }

#guard flyerVsHawkeyeBow.canBlock
  (namedPermanent flyerVsHawkeyeBow "Grizzly Bears")
  (namedPermanent flyerVsHawkeyeBow "Smaug, the Great Calamity")
#guard
  let g := addPermanent started smaugTheGreatCalamityCard ⟨0⟩ ⟨0⟩
  let g := addPermanent g grizzlyBears ⟨1⟩ ⟨1⟩
  let smaug := namedPermanent g "Smaug, the Great Calamity"
  let g := g.setObject { smaug with status := { smaug.status with attacking := true } }
  !g.canBlock (namedPermanent g "Grizzly Bears")
    (namedPermanent g "Smaug, the Great Calamity")

/-- Tapping the equipped creature queues the Bow and deals 1 to each opponent. -/
def hawkeyeBowTapped : Game :=
  let host := namedPermanent hawkeyeBowEquipped "Grizzly Bears"
  hawkeyeBowEquipped.applyPermanentAction host PermanentAction.tap

#guard (namedPermanent hawkeyeBowTapped "Grizzly Bears").status.tapped
#guard hawkeyeBowTapped.waitingTriggers.any (fun t =>
  t.source.name == "Hawkeye's Bow")
#guard hawkeyeBowTapped.log.any (fun s => mentions s "Grizzly Bears becomes tapped")

def hawkeyeBowTapResolved : Game :=
  let bow := namedPermanent hawkeyeBowTapped "Hawkeye's Bow"
  let g := hawkeyeBowTapped.applyTriggeredAbility ⟨0⟩
    (.onWatch Effect.watchEquippedTappedDamage) (some bow.id)
  g

#guard (hawkeyeBowTapResolved.player ⟨1⟩).life ==
  (hawkeyeBowEquipped.player ⟨1⟩).life - 1
#guard hawkeyeBowTapResolved.log.any (fun s => mentions s "is dealt 1 damage")

-- An unattached Bow does not trigger when a creature becomes tapped.
#guard
  let g := addPermanent afterDraw grizzlyBears ⟨0⟩ ⟨0⟩
  let g := addPermanent g hawkeyeSBow ⟨0⟩ ⟨0⟩
  let host := namedPermanent g "Grizzly Bears"
  let g := g.applyPermanentAction host PermanentAction.tap
  !g.waitingTriggers.any (fun t => t.source.name == "Hawkeye's Bow")

-- Tapping an already-tapped equipped creature does not trigger the Bow.
#guard
  let host := namedPermanent hawkeyeBowTapped "Grizzly Bears"
  let g := hawkeyeBowTapped.applyPermanentAction host PermanentAction.tap
  g.waitingTriggers.size == hawkeyeBowTapped.waitingTriggers.size &&
    g.log.any (fun s => mentions s "already tapped")

/-- Attacking with the equipped creature taps it and the Bow deals 1. -/
def hawkeyeBowAttacked : Game :=
  let g := addPermanent afterDraw grizzlyBears ⟨0⟩ ⟨0⟩
  let g := addAttachedAura g hawkeyeSBow (namedPermanent g "Grizzly Bears") ⟨0⟩ ⟨0⟩
  let g := passBoth (skipTo g .beginningOfCombat 80)
  mustApply g ⟨0⟩ (.declareAttackers #[(namedPermanent g "Grizzly Bears").id])

#guard (namedPermanent hawkeyeBowAttacked "Grizzly Bears").status.tapped
#guard (namedPermanent hawkeyeBowAttacked "Grizzly Bears").status.attacking
#guard hawkeyeBowAttacked.log.any (fun s =>
  mentions s "Hawkeye's Bow's equipped-tapped trigger")
#guard
  hawkeyeBowAttacked.stack.any (fun e =>
    mentions (hawkeyeBowAttacked.object! e.objectId).name "Hawkeye's Bow") ||
    hawkeyeBowAttacked.waitingTriggers.any (fun t =>
      t.source.name == "Hawkeye's Bow")

def hawkeyeBowAttackResolved : Game :=
  let g :=
    if hawkeyeBowAttacked.waitingTriggers.any (fun t =>
        t.source.name == "Hawkeye's Bow") then
      hawkeyeBowAttacked.receivePriority ⟨0⟩
    else hawkeyeBowAttacked
  passBoth g

#guard (hawkeyeBowAttackResolved.player ⟨1⟩).life ==
  (afterDraw.player ⟨1⟩).life - 1

/-- Tapping an equipped mana creature for mana also fires the Bow. -/
def hawkeyeBowManaTap : Game :=
  let g := addPermanent afterDraw llanowarElves ⟨0⟩ ⟨0⟩
  let g := addAttachedAura g hawkeyeSBow (namedPermanent g "Llanowar Elves") ⟨0⟩ ⟨0⟩
  let elf := namedPermanent g "Llanowar Elves"
  match g.tapForMana ⟨0⟩ elf.id (.colored .green) with
  | .ok g => g
  | .error e => panic! e

#guard (namedPermanent hawkeyeBowManaTap "Llanowar Elves").status.tapped
#guard (hawkeyeBowManaTap.player ⟨0⟩).manaPool.green == 1
#guard hawkeyeBowManaTap.waitingTriggers.any (fun t =>
  t.source.name == "Hawkeye's Bow")

-- Vigilance means attacking does not tap, so the Bow does not trigger.
#guard
  let g := addPermanent afterDraw captainAmericaLivingLegend ⟨0⟩ ⟨0⟩
  let g := addAttachedAura g hawkeyeSBow
    (namedPermanent g "Captain America, Living Legend") ⟨0⟩ ⟨0⟩
  let g := passBoth (skipTo g .beginningOfCombat 80)
  let g := mustApply g ⟨0⟩
    (.declareAttackers #[(namedPermanent g "Captain America, Living Legend").id])
  !(namedPermanent g "Captain America, Living Legend").status.tapped &&
    !g.waitingTriggers.any (fun t => t.source.name == "Hawkeye's Bow") &&
    !g.stack.any (fun e => mentions (g.object! e.objectId).name "Hawkeye's Bow") &&
    !g.log.any (fun s => mentions s "Hawkeye's Bow's equipped-tapped trigger")

/-- Equip {1} attaches the Bow as a sorcery. -/
def hawkeyeBowReadyToEquip : Game :=
  let g := addPermanent afterDraw grizzlyBears ⟨0⟩ ⟨0⟩
  let g := addPermanent g hawkeyeSBow ⟨0⟩ ⟨0⟩
  let g := g.modifyPlayer ⟨0⟩ (fun pl => { pl with landsPlayedThisTurn := 1 })
  withRedMana g ⟨0⟩ 1

def hawkeyeBowEquippedViaEquip : Game :=
  let g := mustApply hawkeyeBowReadyToEquip ⟨0⟩
    (.activate (namedPermanent hawkeyeBowReadyToEquip "Hawkeye's Bow").id 0)
  let g := mustApply g ⟨0⟩
    (.target (Target.permanent (namedPermanent g "Grizzly Bears").id))
  let g := mustApply g ⟨0⟩ .pay
  passBoth g

#guard (namedPermanent hawkeyeBowEquippedViaEquip "Hawkeye's Bow").attachedTo ==
  some (namedPermanent hawkeyeBowEquippedViaEquip "Grizzly Bears").id
#guard hawkeyeBowEquippedViaEquip.power
  (namedPermanent hawkeyeBowEquippedViaEquip "Grizzly Bears") == 3
#guard hawkeyeBowEquippedViaEquip.hasKeyword
  (namedPermanent hawkeyeBowEquippedViaEquip "Grizzly Bears") (·.reach)
#guard hawkeyeBowReadyToEquip.canActivate ⟨0⟩
  (namedPermanent hawkeyeBowReadyToEquip "Hawkeye's Bow")
  hawkeyeSBow.activatedAbilities[0]!

-- Equip is sorcery-speed only (CR 702.6a).
#guard
  let g := applyIdle (passBoth (skipTo afterDraw .end 80))
  let g := addPermanent g grizzlyBears ⟨0⟩ ⟨0⟩
  let g := addPermanent g hawkeyeSBow ⟨0⟩ ⟨0⟩
  let g := withRedMana g ⟨0⟩ 1
  !g.asSorcery? ⟨0⟩ &&
    !g.canActivate ⟨0⟩ (namedPermanent g "Hawkeye's Bow")
      hawkeyeSBow.activatedAbilities[0]!

end Mtg.Engine.Tests
