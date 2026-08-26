import Mtg.Engine.Agent
import Mtg.Engine.Catalog
import Mtg.Engine.Catalog.Hobbit
import Mtg.Engine.Game

/-!
# Compile-time smoke tests for the engine.
-/

namespace Mtg.Engine.Tests

open Mtg.Engine
open Mtg.Engine.Catalog

/-- 60-card constructed red fixture used only by engine tests. -/
def testRedDeck : Array CardDef :=
  copies 32 mountain ++
  copies 4 lightningBolt ++
  copies 4 shock ++
  copies 4 ragingGoblin ++
  copies 4 grayOgre ++
  copies 4 hillGiant ++
  copies 4 canyonMinotaur ++
  copies 4 mountain

/-- 60-card constructed green fixture used only by engine tests. -/
def testGreenDeck : Array CardDef :=
  copies 32 forest ++
  copies 4 llanowarElves ++
  copies 4 giantGrowth ++
  copies 4 grizzlyBears ++
  copies 4 giantSpider ++
  copies 4 crawWurm ++
  copies 4 centaurCourser ++
  copies 4 rumblingBaloth

def testConfig (seed : UInt64 := 20260807) : StartConfig := {
  seats := #[
    { name := "Chandra", deck := testRedDeck },
    { name := "Nissa", deck := testGreenDeck }
  ]
  format := .constructed
  seed := seed
  startingPlayer := some 0
}

def drawnHands : Game :=
  match Start.start (testConfig 1) with
  | .ok g => g
  | .error e => panic! e

/-- Keep every remaining opening hand (CR 103.5) so tests can begin on turn 1. -/
def keepOpeningHands : Game → Nat → Game
  | _, 0 => panic! "keepOpeningHands fuel exhausted"
  | g, n + 1 =>
    match g.pending with
    | .declareMulligan p =>
      match g.apply p .keep with
      | .ok g' => keepOpeningHands g' n
      | .error e => panic! e
    | .putOnBottom _ _ => panic! "keepOpeningHands: unexpected putOnBottom"
    | _ => g

def started : Game := keepOpeningHands drawnHands 8

#guard testRedDeck.size == 60
#guard testGreenDeck.size == 60
#guard isLegalDeck .constructed testRedDeck
#guard isLegalDeck .constructed testGreenDeck
#guard !isLegalDeck .constructed (copies 5 lightningBolt)

#guard drawnHands.pending == .declareMulligan ⟨0⟩
#guard drawnHands.actor == some ⟨0⟩
#guard drawnHands.openingHandsPending
#guard !drawnHands.hasPriority ⟨0⟩
#guard (drawnHands.player ⟨0⟩).hand.size == 7
#guard (drawnHands.player ⟨1⟩).hand.size == 7
#guard !(drawnHands.player ⟨0⟩).keptOpeningHand

#guard started.players.size == 2
#guard (started.player ⟨0⟩).life == 20
#guard (started.player ⟨1⟩).life == 20
#guard (started.player ⟨0⟩).hand.size == 7
#guard (started.player ⟨1⟩).hand.size == 7
#guard (started.player ⟨0⟩).library.size == 53
#guard started.startingPlayer == ⟨0⟩
#guard started.isFirstTurn
#guard started.step == .upkeep

/-- CR 103.1: the starting player is chosen before opening hands; that player
declares keep-or-mulligan first (CR 103.5). -/
def nissaStarts : Game :=
  match Start.start { testConfig 1 with startingPlayer := some 1 } with
  | .ok g => g
  | .error e => panic! e

#guard nissaStarts.startingPlayer == ⟨1⟩
#guard nissaStarts.activePlayer == ⟨1⟩
#guard nissaStarts.pending == .declareMulligan ⟨1⟩
#guard nissaStarts.actor == some ⟨1⟩
#guard nissaStarts.log.any (· == "Starting player: Nissa")

def nissaStarted : Game := keepOpeningHands nissaStarts 8

#guard nissaStarted.startingPlayer == ⟨1⟩
#guard nissaStarted.activePlayer == ⟨1⟩
#guard nissaStarted.skipsFirstDraw
#guard nissaStarted.log.any (· == "Nissa takes the first turn")

def nissaAfterDraw : Game :=
  match Game.pass nissaStarted ⟨1⟩ with
  | .error e => panic! e
  | .ok g1 =>
    match Game.pass g1 ⟨0⟩ with
    | .error e => panic! e
    | .ok g2 => g2

#guard nissaAfterDraw.step == .precombatMain
#guard (nissaAfterDraw.player ⟨1⟩).hand.size == 7
#guard nissaAfterDraw.hasPriority ⟨1⟩
#guard nissaAfterDraw.log.any (· == "Nissa skips their first draw step (CR 103.8a)")

/-- First player skipped the draw step (CR 103.8a / 500.11), so after upkeep
the game proceeds to precombat main: no card is drawn and nobody received
priority during the skipped step. -/
def afterDraw : Game :=
  match Game.pass started ⟨0⟩ with
  | .error e => panic! e
  | .ok g1 =>
    match Game.pass g1 ⟨1⟩ with
    | .error e => panic! e
    | .ok g2 => g2

#guard started.skipsFirstDraw
#guard afterDraw.step == .precombatMain
#guard (afterDraw.player ⟨0⟩).hand.size == 7
#guard (afterDraw.player ⟨0⟩).library.size == 53
#guard afterDraw.hasPriority ⟨0⟩
#guard afterDraw.asSorcery? ⟨0⟩
#guard afterDraw.canPlayLand ⟨0⟩
#guard !afterDraw.hasPriority ⟨1⟩
#guard afterDraw.actor == some ⟨0⟩
#guard afterDraw.log.any (· == "Chandra skips their first draw step (CR 103.8a)")
#guard (started.beginStep .draw).step == .precombatMain
#guard ((started.beginStep .draw).player ⟨0⟩).hand.size == 7

def played : Game :=
  Agent.play started 80

#guard played.log.size > 10
#guard played.turnNumber ≥ 1
#guard started.stack.isEmpty

/-- `true` iff `needle` occurs in `haystack`. -/
def mentions (haystack needle : String) : Bool :=
  (haystack.splitOn needle).length > 1

/-- First card of `p`'s hand; tests assume opening hands are non-empty. -/
def firstHandCard (g : Game) (p : PlayerId) : GameObject :=
  match (g.handObjects p)[0]? with
  | some o => o
  | none => panic! "expected a card in hand"

def drawnOnce : Game := Game.draw started ⟨0⟩

#guard (drawnOnce.player ⟨0⟩).hand.size == 8
#guard (drawnOnce.player ⟨0⟩).library.size == 52
#guard (drawnOnce.player ⟨1⟩).hand.size == 7

/-- Put `card` onto the battlefield with explicit owner and controller. -/
def addPermanent (g : Game) (card : CardDef) (owner controller : PlayerId) : Game :=
  let (g, id) := g.allocId
  let (g, ts) := g.bumpTime
  let obj : GameObject := {
    id := id
    printed := card
    owner := owner
    controller := some controller
    zone := .battlefield
    status := { summoningSick := false }
    timestamp := ts
  }
  { g with objects := g.objects.push obj }

/-- Drop a basic land onto the battlefield without using the play-land action. -/
def addUntappedLand (g : Game) (card : CardDef) : Game :=
  addPermanent g card g.activePlayer g.activePlayer

def withMountain : Game := addUntappedLand started mountain

def tappedMountain : Game :=
  match (withMountain.permanentsOf ⟨0⟩).find? (·.printed.isLand) with
  | none => panic! "expected a land on the battlefield"
  | some o =>
    match o.printed.manaAbilities[0]? with
    | none => panic! s!"{o.name} has no mana ability"
    | some m =>
      match withMountain.tapForMana ⟨0⟩ o.id m with
      | .ok g => g
      | .error e => panic! e

-- Occupants are unchanged, but the land is now tapped (CR 110.5 / 605.3a).
#guard withMountain.battlefield.map (·.id) == tappedMountain.battlefield.map (·.id)
#guard tappedMountain.battlefield.any (·.status.tapped)
#guard !(withMountain.battlefield.any (·.status.tapped))
#guard (tappedMountain.player ⟨0⟩).manaPool != (withMountain.player ⟨0⟩).manaPool

/-- Last permanent on the battlefield; tests assume one is present. -/
def lastPermanent (g : Game) : GameObject :=
  match g.battlefield.back? with
  | some o => o
  | none => panic! "expected a permanent on the battlefield"

/-- Untap is a turn-based action (CR 502.2): occupants stay put, but the land
is no longer tapped. -/
def afterUntapStep : Game := tappedMountain.beginStep .untap

#guard tappedMountain.battlefield.map (·.id) == afterUntapStep.battlefield.map (·.id)
#guard afterUntapStep.step == .untap
#guard !(afterUntapStep.battlefield.any (·.status.tapped))
#guard afterUntapStep.log.any (fun s => mentions s "untaps Mountain")

/-- A permanent Chandra owns and Nissa controls is among Nissa's permanents. -/
def stolenMountain : Game := addPermanent started mountain ⟨0⟩ ⟨1⟩

#guard (stolenMountain.permanentsOf ⟨1⟩).any (·.id == (lastPermanent stolenMountain).id)
#guard !(stolenMountain.permanentsOf ⟨0⟩).any (·.id == (lastPermanent stolenMountain).id)
#guard (lastPermanent stolenMountain).owner == ⟨0⟩
#guard (lastPermanent stolenMountain).controller == some ⟨1⟩

/-- Changing control does not move the permanent off the battlefield. -/
def afterControlChange : Game :=
  let o := lastPermanent withMountain
  withMountain.setObject { o with controller := some ⟨1⟩ }

#guard withMountain.battlefield.map (·.id) == afterControlChange.battlefield.map (·.id)
#guard (lastPermanent afterControlChange).controller == some ⟨1⟩
#guard (lastPermanent afterControlChange).owner == ⟨0⟩

/-- Nissa's permanent entered first; Chandra still has a later Forest. -/
def mixedControllers : Game := addPermanent stolenMountain forest ⟨0⟩ ⟨0⟩

#guard (mixedControllers.permanentsOf ⟨0⟩)[0]!.name == "Forest"
#guard (mixedControllers.permanentsOf ⟨1⟩)[0]!.name == "Mountain"

def uncontrolledPermanent : Game :=
  let o := lastPermanent withMountain
  withMountain.setObject { o with controller := none }

#guard (lastPermanent uncontrolledPermanent).controller.isNone
#guard (lastPermanent uncontrolledPermanent).owner == ⟨0⟩

/- Hands, battlefield, and other zones print keywords and abilities. -/
#guard mentions ragingGoblin.summary "haste"
#guard mentions giantSpider.summary "reach"
#guard mentions llanowarElves.summary "{T}: Add {G}"
#guard mentions lightningBolt.summary "deals 3 damage"
#guard mentions mountain.summary "{T}: Add {R}"
#guard mentions wayfarersBauble.summary "Search your library"
#guard mentions attercop.summary "reach"
#guard mentions attercop.summary "deathtouch"
#guard mentions attercop.summary "Landfall"
#guard mentions landrovalHorizonWitness.summary "flying"
#guard mentions landrovalHorizonWitness.summary "Whenever two or more creatures"
#guard mentions soldierOfTheGreyHost.summary "Flash"
#guard mentions soldierOfTheGreyHost.summary "flying"
#guard mentions roguesPassage.summary "{T}: Add {C}"
#guard mentions roguesPassage.summary "can't be blocked"
#guard mentions orcishSiegemaster.summary "trample"
#guard mentions orcishSiegemaster.summary "Other Orcs and Goblins"
#guard mentions orcishSiegemaster.summary "greatest power"
#guard orcishSiegemaster.staticAbilities.size == 1
#guard orcishSiegemaster.triggeredAbilities.size == 1
#guard mentions battleScarredGoblin.summary "becomes blocked"
#guard battleScarredGoblin.triggeredAbilities.size == 1
#guard mentions giftOfStrands.summary "flash"
#guard mentions giftOfStrands.summary "Enchanted creature"
#guard giftOfStrands.staticAbilities.size == 1
#guard giftOfStrands.triggeredAbilities.size == 1
#guard mentions raggedShortSpear.summary "Equipped creature"
#guard mentions raggedShortSpear.summary "Equip"
#guard raggedShortSpear.isEquipment
#guard raggedShortSpear.staticAbilities.size == 1
#guard raggedShortSpear.triggeredAbilities.size == 1
#guard raggedShortSpear.activatedAbilities.size == 1
#guard mentions galadhrimGuide.summary "scry 2"
#guard galadhrimGuide.triggeredAbilities.size == 1
#guard galadhrimGuide.triggeredAbilities == #[.onEnterScry 2]
#guard mentions wargTactics.summary "Choose one"
#guard mentions wargTactics.summary "hexproof"
#guard wargTactics.isModal
#guard wargTactics.modes.size == 2
#guard mentions goblinCratermaker.summary "Choose one"
#guard mentions goblinCratermaker.summary "colorless nonland"
#guard goblinCratermaker.activatedAbilities.size == 1
#guard mentions beornsHospitality.summary "Landfall"
#guard mentions beornsHospitality.summary "Bear creature"
#guard beornsHospitality.triggeredAbilities.size == 1
#guard beornsHospitality.activatedAbilities.size == 1
#guard mentions mirkwoodPathmaker.summary "lands you control"
#guard mirkwoodPathmaker.staticAbilities.size == 1

/- Structured abilities still print when Oracle text is absent. -/
#guard
  let c : CardDef := {
    name := "Silent Elves"
    types := #[.creature]
    power := some 1
    toughness := some 1
    tapAddMana := #[.colored .green]
  }
  mentions c.abilitiesText "{T}: Add {G}" &&
    mentions c.summary "{T}: Add {G}"

#guard
  let c : CardDef := {
    name := "Silent Siege"
    types := #[.creature]
    power := some 0
    toughness := some 5
    keywords := { Keywords.none with trample := true }
    staticAbilities := #[.otherCreaturesHaveTrample #["Orc", "Goblin"]]
    triggeredAbilities := #[.onAttackPumpByGreatestPower]
  }
  mentions c.abilitiesText "Other Orcs and Goblins" &&
    mentions c.abilitiesText "greatest power" &&
    mentions c.summary "trample"

#guard
  let c : CardDef := {
    name := "Silent Scar"
    types := #[.creature]
    power := some 2
    toughness := some 2
    triggeredAbilities := #[.onBecomesBlockedDeal1ToBlockers]
  }
  mentions c.abilitiesText "becomes blocked" &&
    mentions c.abilitiesText "each creature blocking it"

#guard
  let c : CardDef := {
    name := "Silent Strands"
    types := #[.enchantment]
    subtypes := #["Aura"]
    keywords := { Keywords.none with flash := true }
    staticAbilities := #[.enchantedCreatureGets 3 3]
    triggeredAbilities := #[.onEnterScry 2]
  }
  mentions c.abilitiesText "Enchanted creature gets +3/+3" &&
    mentions c.abilitiesText "scry 2" &&
    mentions c.summary "flash"

#guard
  let c : CardDef := {
    name := "Silent Spear"
    types := #[.artifact]
    subtypes := #["Equipment"]
    staticAbilities := #[.equippedCreatureGets 2 0]
    triggeredAbilities := #[.onEnterMayDiscardDraw 2]
    activatedAbilities := #[{
      cost := { mana := ManaCost.ofGeneric 3 }
      effect := .attachToTargetCreatureYouControl
      onlyAsSorcery := true
    }]
  }
  mentions c.abilitiesText "Equipped creature gets +2/+0" &&
    mentions c.abilitiesText "you may discard a card" &&
    mentions c.abilitiesText "Attach this Equipment" &&
    mentions c.abilitiesText "activate only as a sorcery"

#guard
  let c : CardDef := {
    name := "Silent Hospitality"
    types := #[.enchantment]
    triggeredAbilities := #[.onLandYouControlEntersPlusOnePlusOne]
    activatedAbilities := #[{
      cost := { mana := ManaCost.ofGenericAndColors 5 [.green, .green] }
      effect := .becomeBearCreatureWithLandsPT
    }]
  }
  mentions c.abilitiesText "land you control enters" &&
    mentions c.abilitiesText "Bear creature" &&
    mentions c.abilitiesText "{5}{G}{G}"

#guard
  let c : CardDef := {
    name := "Silent Pathmaker"
    types := #[.creature]
    staticAbilities := #[.powerToughnessEqualLandsYouControl]
  }
  mentions c.abilitiesText "lands you control"

def withGoblin : Game := addPermanent started ragingGoblin ⟨0⟩ ⟨0⟩
def withElves : Game := addPermanent started llanowarElves ⟨0⟩ ⟨0⟩
def withSpider : Game := addPermanent started giantSpider ⟨0⟩ ⟨0⟩
def withAttercop : Game := addPermanent started attercop ⟨0⟩ ⟨0⟩

/-- Apply the idle action for whoever must act: empty combat declarations or pass. -/
def applyIdle (g : Game) : Game :=
  match g.pending, g.actor with
  | .declareAttackers, some p =>
    match g.apply p (.declareAttackers #[]) with
    | .ok g' => g'
    | .error e => panic! e
  | .declareBlockers, some p =>
    match g.apply p (.declareBlockers #[]) with
    | .ok g' => g'
    | .error e => panic! e
  | .declareMulligan _, some p =>
    match g.apply p .keep with
    | .ok g' => g'
    | .error e => panic! e
  | .putOnBottom _ n, some p =>
    match g.apply p (.putOnBottom ((g.player p).hand.extract 0 n)) with
    | .ok g' => g'
    | .error e => panic! e
  | .scry _ n, some p =>
    match g.apply p (.scry (g.scryLookedIds p n) #[]) with
    | .ok g' => g'
    | .error e => panic! e
  | .mayDiscardDraw _ _, some p =>
    match g.apply p .decline with
    | .ok g' => g'
    | .error e => panic! e
  | .chooseMode _, some p =>
    match g.proposedSpell with
    | none => panic! "expected a proposed spell or ability while choosing a mode"
    | some prop =>
      match prop.kind with
      | .activatedAbility =>
        match g.defaultAbilityMode p prop.abilityModes with
        | none => panic! "no legal mode (CR 601.2b)"
        | some idx =>
          match g.apply p (.chooseMode idx) with
          | .ok g' => g'
          | .error e => panic! e
      | .spell =>
        match g.findObject? prop.spellId with
        | none => panic! "expected a proposed spell while choosing a mode"
        | some spell =>
          match g.defaultMode p spell with
          | none => panic! "no legal mode (CR 601.2b)"
          | some i =>
            match g.apply p (.chooseMode i) with
            | .ok g' => g'
            | .error e => panic! e
  | .assignCombatDamage _ _, some p =>
    match g.apply p (.assignCombatDamage #[]) with
    | .ok g' => g'
    | .error e => panic! e
  | .chooseTargets _, some p =>
    match g.objectAwaitingTargets with
    | none => panic! "expected a proposed spell or trigger while choosing targets"
    | some spell =>
      match g.defaultTarget p spell with
      | none => panic! "no legal target (CR 601.2c)"
      | some t =>
        match g.apply p (.target t) with
        | .ok g' => g'
        | .error e => panic! e
  | _, some p =>
    match g.apply p .pass with
    | .ok g' => g'
    | .error e => panic! e
  | _, none => panic! s!"no actor at {g.step}"

/-- Advance by idle actions until `g` is in `st` with no pending choice. -/
def skipTo (g : Game) (st : Step) : Nat → Game
  | 0 => panic! s!"skipTo fuel exhausted at {g.step}"
  | n + 1 =>
    if g.over then panic! "game over while skipping"
    else if g.step == st && g.pending == .none then g
    else skipTo (applyIdle g) st n

def passBoth (g : Game) : Game :=
  applyIdle (applyIdle g)

def atEndStep : Game := skipTo started .end 80

/-- A 0/0 creature kept alive only by an until-end-of-turn pump. -/
def zeroZero : CardDef := {
  name := "Zero/Zero"
  types := #[.creature]
  power := some 0
  toughness := some 0
}

def addPumpedCreature (g : Game) (card : CardDef) (pumpP pumpT : Int) : Game :=
  let (g, id) := g.allocId
  let (g, ts) := g.bumpTime
  let obj : GameObject := {
    id := id
    printed := card
    owner := g.activePlayer
    controller := some g.activePlayer
    zone := .battlefield
    status := { pumpPower := pumpP, pumpToughness := pumpT, summoningSick := false }
    timestamp := ts
  }
  { g with objects := g.objects.push obj }

/-- CR 514.3: after both players pass in the end step, cleanup does not grant
priority, so the next player's upkeep begins immediately. -/
def afterSilentCleanup : Game := passBoth atEndStep

#guard atEndStep.step == .end
#guard atEndStep.turnNumber == 1
#guard atEndStep.activePlayer == ⟨0⟩
#guard afterSilentCleanup.turnNumber == 2
#guard afterSilentCleanup.step == .upkeep
#guard afterSilentCleanup.activePlayer == ⟨1⟩
#guard !afterSilentCleanup.cleanupGivesPriority
#guard !afterSilentCleanup.log.any (· == "Players receive priority during cleanup (CR 514.3a)")

/-- Opponent's untap (CR 502.2) does not untap Chandra's land. -/
def nissaTurn2 : Game := passBoth (skipTo tappedMountain .end 80)

#guard nissaTurn2.turnNumber == 2
#guard nissaTurn2.activePlayer == ⟨1⟩
#guard nissaTurn2.step == .upkeep
#guard nissaTurn2.battlefield.any (·.status.tapped)
#guard !nissaTurn2.skipsFirstDraw

/-- The second player does draw on their first turn and receives priority
during the draw step (CR 103.8a applies only to the starting player). -/
def nissaDraw : Game := passBoth nissaTurn2

#guard nissaDraw.step == .draw
#guard nissaDraw.playersReceivePriority
#guard nissaDraw.hasPriority ⟨1⟩
#guard nissaDraw.actor == some ⟨1⟩
#guard (nissaDraw.player ⟨1⟩).hand.size == 8
#guard (nissaDraw.player ⟨0⟩).hand.size == 7
#guard !nissaDraw.asSorcery? ⟨1⟩
#guard nissaDraw.log.any (fun s => mentions s "Nissa draws")

/-- The pass that ends Nissa's turn also runs Chandra's untap. Occupants are
unchanged, but the land is now untapped (CR 502.2). -/
def nissaEnd : Game := skipTo nissaTurn2 .end 80
def chandraTurn3 : Game := passBoth nissaEnd

#guard nissaEnd.turnNumber == 2
#guard nissaEnd.step == .end
#guard nissaEnd.battlefield.any (·.status.tapped)
#guard chandraTurn3.turnNumber == 3
#guard chandraTurn3.activePlayer == ⟨0⟩
#guard chandraTurn3.step == .upkeep
#guard !(chandraTurn3.battlefield.any (·.status.tapped))
#guard nissaEnd.battlefield.map (·.id) == chandraTurn3.battlefield.map (·.id)
#guard chandraTurn3.log.any (fun s => mentions s "untaps Mountain")

/-- CR 514.3a: ending a pump that was keeping a 0/0 alive causes a state-based
action, so the active player receives priority still in cleanup. -/
def cleanupWithSBA : Game :=
  passBoth (addPumpedCreature atEndStep zeroZero 1 1)

#guard cleanupWithSBA.step == .cleanup
#guard cleanupWithSBA.cleanupGivesPriority
#guard cleanupWithSBA.playersReceivePriority
#guard cleanupWithSBA.actor == some ⟨0⟩
#guard cleanupWithSBA.hasPriority ⟨0⟩
#guard (cleanupWithSBA.battlefield.filter (fun o => o.name == "Zero/Zero")).isEmpty
#guard cleanupWithSBA.log.any (· == "Players receive priority during cleanup (CR 514.3a)")

/-- After the 514.3a priority window, another cleanup begins; with no further
state-based actions it ends the turn (CR 514.3a last sentence). -/
def afterExceptionCleanup : Game := passBoth cleanupWithSBA

#guard afterExceptionCleanup.turnNumber == 2
#guard afterExceptionCleanup.step == .upkeep
#guard afterExceptionCleanup.activePlayer == ⟨1⟩
#guard !afterExceptionCleanup.cleanupGivesPriority

/-- Lightning Bolt to a player (CR 120.3a) changes that player's life total. -/
def afterBolt : Game :=
  started.applyEffect ⟨0⟩ (.dealDamage 3) #[Target.player ⟨1⟩]

#guard (started.player ⟨1⟩).life == 20
#guard (afterBolt.player ⟨1⟩).life == 17
#guard (afterBolt.player ⟨0⟩).life == 20
#guard afterBolt.log.any (fun s => mentions s "17 life")

/-- Unblocked combat damage (CR 510.1a / 120.3a) also changes life. -/
def attackingGoblin : Game :=
  let g := addPermanent started ragingGoblin ⟨0⟩ ⟨0⟩
  let o := lastPermanent g
  g.setObject { o with status := { o.status with attacking := true } }

def afterCombatDamage : Game := attackingGoblin.combatDamage

#guard ragingGoblin.power == some 1
#guard (attackingGoblin.player ⟨1⟩).life == 20
#guard (afterCombatDamage.player ⟨1⟩).life == 19
#guard afterCombatDamage.log.any (fun s => mentions s "19 life")

/-- Put `card` into `p`'s hand without drawing. -/
def addToHand (g : Game) (card : CardDef) (p : PlayerId) : Game :=
  let (g, id) := g.allocId
  let (g, ts) := g.bumpTime
  let obj : GameObject := {
    id := id
    printed := card
    owner := p
    zone := .hand p
    timestamp := ts
  }
  { g with objects := g.objects.push obj }.modifyPlayer p (fun pl =>
    { pl with hand := pl.hand.push id })

/-- Put `card` on top of `p`'s library (the back of the library array). -/
def addToLibraryTop (g : Game) (card : CardDef) (p : PlayerId) : Game :=
  let (g, id) := g.allocId
  let (g, ts) := g.bumpTime
  let obj : GameObject := {
    id := id
    printed := card
    owner := p
    zone := .library p
    timestamp := ts
  }
  { g with objects := g.objects.push obj }.modifyPlayer p (fun pl =>
    { pl with library := pl.library.push id })

def mustApply (g : Game) (p : PlayerId) (a : Action) : Game :=
  match g.apply p a with
  | .ok g' => g'
  | .error e => panic! e

/-- Propose a spell (CR 601.2a) and announce its target (CR 601.2c). -/
def proposeTargeted (g : Game) (p : PlayerId) (id : ObjectId) (t : Target) : Game :=
  mustApply (mustApply g p (.cast id)) p (.target t)

def handCardNamed (g : Game) (p : PlayerId) (name : String) : GameObject :=
  match (g.handObjects p).find? (fun o => o.name == name) with
  | some o => o
  | none => panic! s!"expected {name} in hand"

/-- CR 601.2: a player may begin casting without mana in their pool, then
announce a target (601.2c), activate mana abilities (601.2g), then pay. -/
def boltSetup : Game :=
  addToHand (addUntappedLand started mountain) lightningBolt ⟨0⟩

def boltInHand : GameObject :=
  handCardNamed boltSetup ⟨0⟩ "Lightning Bolt"

def boltMountain : GameObject :=
  lastPermanent boltSetup

#guard (boltSetup.player ⟨0⟩).manaPool.isEmpty
#guard !(boltSetup.player ⟨0⟩).manaPool.canPay lightningBolt.manaCost
#guard (boltSetup.availableMana ⟨0⟩).canPay lightningBolt.manaCost
#guard boltSetup.canCast ⟨0⟩ boltInHand
#guard boltSetup.hasPriority ⟨0⟩

/-- The agent proposes a spell instead of tapping first. -/
def agentBeginsCast : Bool :=
  match Agent.choose boltSetup ⟨0⟩ with
  | some (.cast _) => true
  | _ => false

#guard agentBeginsCast

def proposedBolt : Game :=
  mustApply boltSetup ⟨0⟩ (.cast boltInHand.id)

#guard
  match proposedBolt.pending with
  | .chooseTargets ⟨0⟩ => true
  | _ => false
#guard proposedBolt.proposedSpell.isSome
#guard !proposedBolt.stack.isEmpty
#guard proposedBolt.stack.back!.targets.isEmpty
#guard !(proposedBolt.player ⟨0⟩).hand.contains boltInHand.id
#guard (proposedBolt.player ⟨0⟩).manaPool.isEmpty
#guard !proposedBolt.hasPriority ⟨0⟩
#guard !proposedBolt.canActivateManaAbility ⟨0⟩
#guard proposedBolt.actor == some ⟨0⟩
#guard proposedBolt.log.any (fun s => mentions s "begins casting Lightning Bolt")
#guard proposedBolt.log.any (fun s => mentions s "must choose a target (CR 601.2c)")

-- CR 601.2c comes before mana abilities and payment.
#guard
  match proposedBolt.apply ⟨0⟩ .pay with
  | .error msg => mentions msg "Choose a target first"
  | .ok _ => false
#guard
  match proposedBolt.apply ⟨0⟩ (.target (Target.permanent ⟨99999⟩)) with
  | .error msg => mentions msg "Illegal target"
  | .ok _ => false
#guard
  match proposedBolt.apply ⟨1⟩ (.target (Target.player ⟨1⟩)) with
  | .error msg => mentions msg "may choose targets"
  | .ok _ => false

def agentChoosesTarget : Bool :=
  match Agent.choose proposedBolt ⟨0⟩ with
  | some (.target (Target.player q)) => q == ⟨1⟩
  | _ => false

#guard agentChoosesTarget

def targetedBolt : Game :=
  mustApply proposedBolt ⟨0⟩ (.target (Target.player ⟨1⟩))

#guard targetedBolt.pending == .activateManaAbilities ⟨0⟩
#guard targetedBolt.stack.back!.targets == #[Target.player ⟨1⟩]
#guard targetedBolt.canActivateManaAbility ⟨0⟩
#guard !targetedBolt.canActivateManaAbility ⟨1⟩
#guard targetedBolt.log.any (fun s => mentions s "chooses Nissa as a target (CR 601.2c)")
#guard targetedBolt.log.any (fun s => mentions s "may activate mana abilities (CR 601.2g)")

/-- Opponent cannot activate mana abilities during the caster's 601.2g window. -/
def nissaTapDenied : Bool :=
  match targetedBolt.tapForMana ⟨1⟩ boltMountain.id (.colored .red) with
  | .error _ => true
  | .ok _ => false

#guard nissaTapDenied

def agentTapsInWindow : Bool :=
  match Agent.choose targetedBolt ⟨0⟩ with
  | some (.tapForMana id _) => id == boltMountain.id
  | _ => false

#guard agentTapsInWindow

def tappedForBolt : Game :=
  mustApply targetedBolt ⟨0⟩ (.tapForMana boltMountain.id (.colored .red))

#guard (tappedForBolt.player ⟨0⟩).manaPool.canPay lightningBolt.manaCost
#guard tappedForBolt.pending == .activateManaAbilities ⟨0⟩
#guard tappedForBolt.battlefield.any (·.status.tapped)

def agentPaysInWindow : Bool :=
  match Agent.choose tappedForBolt ⟨0⟩ with
  | some .pay => true
  | _ => false

#guard agentPaysInWindow

/-- Passing priority is not how the 601.2h payment is made. -/
def passDuringWindowDenied : Bool :=
  match targetedBolt.apply ⟨0⟩ .pass with
  | .error _ => true
  | .ok _ => false

#guard passDuringWindowDenied

def paidBolt : Game :=
  mustApply tappedForBolt ⟨0⟩ .pay

#guard paidBolt.pending == .none
#guard paidBolt.proposedSpell.isNone
#guard paidBolt.hasPriority ⟨0⟩
#guard (paidBolt.player ⟨0⟩).manaPool.isEmpty
#guard !paidBolt.stack.isEmpty
#guard paidBolt.log.any (fun s => mentions s "casts Lightning Bolt")

/-- Paying without enough mana reverses the cast (CR 601.2 / 733.1). -/
def reversedBolt : Game :=
  mustApply targetedBolt ⟨0⟩ .pay

#guard reversedBolt.pending == .none
#guard reversedBolt.proposedSpell.isNone
#guard reversedBolt.stack.isEmpty
#guard reversedBolt.hasPriority ⟨0⟩
#guard (reversedBolt.handObjects ⟨0⟩).any (fun o => o.name == "Lightning Bolt")
#guard !(reversedBolt.battlefield.any (·.status.tapped))
#guard (reversedBolt.player ⟨0⟩).manaPool.isEmpty
#guard reversedBolt.log.any (fun s => mentions s "the casting is reversed")

/-- Mana abilities activated at 601.2g are reversed with the illegal cast. -/
def ogreSetup : Game :=
  addToHand (addUntappedLand (skipTo started .precombatMain 80) mountain) grayOgre ⟨0⟩

def proposedOgre : Game :=
  mustApply ogreSetup ⟨0⟩ (.cast (handCardNamed ogreSetup ⟨0⟩ "Gray Ogre").id)

def tappedForOgre : Game :=
  mustApply proposedOgre ⟨0⟩ (.tapForMana (lastPermanent ogreSetup).id (.colored .red))

#guard tappedForOgre.pending == .activateManaAbilities ⟨0⟩
#guard (tappedForOgre.player ⟨0⟩).manaPool.canPay (ManaCost.ofColor .red)
#guard !(tappedForOgre.player ⟨0⟩).manaPool.canPay grayOgre.manaCost
#guard tappedForOgre.battlefield.any (·.status.tapped)

def reversedOgre : Game :=
  mustApply tappedForOgre ⟨0⟩ .pay

#guard reversedOgre.stack.isEmpty
#guard reversedOgre.hasPriority ⟨0⟩
#guard !(reversedOgre.battlefield.any (·.status.tapped))
#guard (reversedOgre.player ⟨0⟩).manaPool.isEmpty
#guard (reversedOgre.handObjects ⟨0⟩).any (fun o => o.name == "Gray Ogre")
#guard reversedOgre.log.any (fun s => mentions s "the casting is reversed")

/-- A resolved Lightning Bolt still changes life after the 601.2g window. -/
def resolvedBolt : Game :=
  mustApply (mustApply paidBolt ⟨0⟩ .pass) ⟨1⟩ .pass

#guard resolvedBolt.stack.isEmpty
#guard (resolvedBolt.player ⟨1⟩).life == 17
#guard resolvedBolt.log.any (fun s => mentions s "casts Lightning Bolt")

-- The heuristic still plays, and it announces targets then activates mana abilities.
#guard played.log.any (fun s => mentions s "may activate mana abilities (CR 601.2g)")
#guard played.log.any (fun s => mentions s "must choose a target (CR 601.2c)")
#guard played.log.any (fun s => mentions s "begins casting")

/-- Two ready creatures: declaring a subset of attackers leaves the rest
untapped and not attacking. -/
def twoReadyAttackers : Game :=
  addPermanent (addPermanent started grizzlyBears ⟨0⟩ ⟨0⟩) grayOgre ⟨0⟩ ⟨0⟩

def readyToDeclareAttackers : Game :=
  passBoth (skipTo twoReadyAttackers .beginningOfCombat 80)

def namedPermanent (g : Game) (name : String) : GameObject :=
  match g.battlefield.find? (fun o => o.name == name) with
  | some o => o
  | none => panic! s!"expected {name} on the battlefield"

#guard readyToDeclareAttackers.step == .declareAttackers
#guard readyToDeclareAttackers.pending == .declareAttackers
#guard (readyToDeclareAttackers.battlefield.filter (readyToDeclareAttackers.canAttack)).size == 2

def onlyBearsAttack : Game :=
  match readyToDeclareAttackers.apply ⟨0⟩
      (.declareAttackers #[(namedPermanent readyToDeclareAttackers "Grizzly Bears").id]) with
  | .ok g => g
  | .error e => panic! e

#guard (namedPermanent onlyBearsAttack "Grizzly Bears").status.attacking
#guard (namedPermanent onlyBearsAttack "Grizzly Bears").status.tapped
#guard !(namedPermanent onlyBearsAttack "Gray Ogre").status.attacking
#guard !(namedPermanent onlyBearsAttack "Gray Ogre").status.tapped
#guard onlyBearsAttack.log.any (fun s => mentions s "attacks with Grizzly Bears")
#guard !onlyBearsAttack.log.any (fun s => mentions s "attacks with Gray Ogre")

/-- Declaring both creatures still works; the demo's bare `attack` uses this. -/
def bothAttack : Game :=
  let ids := readyToDeclareAttackers.battlefield.filter (readyToDeclareAttackers.canAttack) |>.map (·.id)
  match readyToDeclareAttackers.apply ⟨0⟩ (.declareAttackers ids) with
  | .ok g => g
  | .error e => panic! e

#guard (namedPermanent bothAttack "Grizzly Bears").status.attacking
#guard (namedPermanent bothAttack "Gray Ogre").status.attacking

/-- Chandra's Gray Ogre attacks; Nissa has Grizzly Bears to block. -/
def ogreVsBears : Game :=
  addPermanent (addPermanent started grayOgre ⟨0⟩ ⟨0⟩) grizzlyBears ⟨1⟩ ⟨1⟩

def ogreDeclaredAttacker : Game :=
  let g := passBoth (skipTo ogreVsBears .beginningOfCombat 80)
  mustApply g ⟨0⟩ (.declareAttackers #[(namedPermanent g "Gray Ogre").id])

def readyToDeclareBlockers : Game :=
  passBoth ogreDeclaredAttacker

#guard readyToDeclareBlockers.step == .declareBlockers
#guard readyToDeclareBlockers.pending == .declareBlockers
#guard readyToDeclareBlockers.actor == some ⟨1⟩
#guard (namedPermanent readyToDeclareBlockers "Gray Ogre").status.attacking
#guard (namedPermanent readyToDeclareBlockers "Grizzly Bears").status.blocking.isEmpty

def bearsBlockOgre : Game :=
  let g := readyToDeclareBlockers
  mustApply g ⟨1⟩ (.declareBlockers #[(
    (namedPermanent g "Grizzly Bears").id,
    (namedPermanent g "Gray Ogre").id)])

#guard (namedPermanent bearsBlockOgre "Grizzly Bears").status.blocking ==
  #[(namedPermanent bearsBlockOgre "Gray Ogre").id]
#guard (namedPermanent bearsBlockOgre "Gray Ogre").status.blocked
#guard bearsBlockOgre.log.any (fun s => mentions s "Grizzly Bears blocks Gray Ogre")
#guard bearsBlockOgre.pending == .none

/-- Blocking sends combat damage to the creature, not the defending player. -/
def afterBlockedDamage : Game := passBoth bearsBlockOgre

#guard (afterBlockedDamage.player ⟨1⟩).life == 20
#guard afterBlockedDamage.log.any (fun s =>
  mentions s "Gray Ogre deals 2 combat damage to Grizzly Bears")
#guard afterBlockedDamage.log.any (fun s =>
  mentions s "Grizzly Bears deals 2 combat damage to Gray Ogre")
#guard !afterBlockedDamage.log.any (fun s =>
  mentions s "deals 2 combat damage to Nissa")

def afterUnblockedDamage : Game :=
  passBoth (mustApply readyToDeclareBlockers ⟨1⟩ (.declareBlockers #[]))

#guard (afterUnblockedDamage.player ⟨1⟩).life == 18
#guard afterUnblockedDamage.log.any (fun s =>
  mentions s "Gray Ogre deals 2 combat damage to Nissa")

/-- Unused mana is emptied as a turn-based action (CR 500.4). -/
def emptiedPool : Game := tappedMountain.emptyManaPools

#guard (emptiedPool.player ⟨0⟩).manaPool.isEmpty
#guard emptiedPool.log.any (fun s => mentions s "empties mana pool")

/-- CR 103.5: the starting player declares first; the mulligan is taken only
after every remaining player has declared. -/
def afterChandraDeclaresMulligan : Game :=
  mustApply drawnHands ⟨0⟩ .takeMulligan

#guard afterChandraDeclaresMulligan.pending == .declareMulligan ⟨1⟩
#guard afterChandraDeclaresMulligan.actor == some ⟨1⟩
#guard (afterChandraDeclaresMulligan.player ⟨0⟩).hand == (drawnHands.player ⟨0⟩).hand
#guard (afterChandraDeclaresMulligan.player ⟨0⟩).mulligansTaken == 0
#guard afterChandraDeclaresMulligan.willMulligan == #[⟨0⟩]
#guard afterChandraDeclaresMulligan.log.any (fun s => mentions s "will take a mulligan")
#guard !afterChandraDeclaresMulligan.log.any (fun s => mentions s "takes a mulligan (")

/-- Nissa keeps; then Chandra's declared mulligan is taken (CR 103.5). -/
def afterChandraMulligan : Game :=
  mustApply afterChandraDeclaresMulligan ⟨1⟩ .keep

#guard afterChandraMulligan.pending == .putOnBottom ⟨0⟩ 1
#guard afterChandraMulligan.actor == some ⟨0⟩
#guard (afterChandraMulligan.player ⟨0⟩).hand.size == 7
#guard (afterChandraMulligan.player ⟨0⟩).mulligansTaken == 1
#guard (afterChandraMulligan.player ⟨0⟩).library.size == 53
#guard (afterChandraMulligan.player ⟨1⟩).keptOpeningHand
#guard (afterChandraMulligan.player ⟨1⟩).hand == (drawnHands.player ⟨1⟩).hand
#guard afterChandraMulligan.log.any (fun s => mentions s "takes a mulligan")
#guard afterChandraMulligan.log.any (fun s => mentions s "at the same time")

def chandraBottomCard : GameObject :=
  match (afterChandraMulligan.handObjects ⟨0⟩)[0]? with
  | some o => o
  | none => panic! "expected a card to put on the bottom"

def afterChandraBottoms : Game :=
  mustApply afterChandraMulligan ⟨0⟩ (.putOnBottom #[chandraBottomCard.id])

#guard (afterChandraBottoms.player ⟨0⟩).hand.size == 6
#guard (afterChandraBottoms.player ⟨0⟩).library.size == 54
#guard afterChandraBottoms.pending == .declareMulligan ⟨0⟩
#guard (afterChandraBottoms.player ⟨1⟩).keptOpeningHand
#guard !(afterChandraBottoms.player ⟨0⟩).keptOpeningHand
#guard (afterChandraBottoms.object! (afterChandraBottoms.player ⟨0⟩).library[0]!).name ==
  chandraBottomCard.name
#guard afterChandraBottoms.log.any (fun s => mentions s "on the bottom of their library")

def afterChandraKeepsSix : Game :=
  mustApply afterChandraBottoms ⟨0⟩ .keep

#guard afterChandraKeepsSix.pending == .none
#guard afterChandraKeepsSix.step == .upkeep
#guard afterChandraKeepsSix.isFirstTurn
#guard (afterChandraKeepsSix.player ⟨0⟩).hand.size == 6
#guard (afterChandraKeepsSix.player ⟨1⟩).hand.size == 7
#guard (afterChandraKeepsSix.player ⟨0⟩).keptOpeningHand
#guard afterChandraKeepsSix.log.any (fun s => mentions s "takes the first turn")

/-- Both players declare a mulligan before either hand is shuffled (CR 103.5). -/
def afterBothDeclareMulligan : Game :=
  mustApply afterChandraDeclaresMulligan ⟨1⟩ .takeMulligan

#guard afterBothDeclareMulligan.pending == .putOnBottom ⟨0⟩ 1
#guard afterBothDeclareMulligan.actor == some ⟨0⟩
#guard (afterBothDeclareMulligan.player ⟨0⟩).mulligansTaken == 1
#guard (afterBothDeclareMulligan.player ⟨1⟩).mulligansTaken == 1
#guard (afterBothDeclareMulligan.player ⟨0⟩).hand.size == 7
#guard (afterBothDeclareMulligan.player ⟨1⟩).hand.size == 7
#guard (afterBothDeclareMulligan.player ⟨1⟩).hand != (drawnHands.player ⟨1⟩).hand
#guard afterBothDeclareMulligan.mulliganToBottom == #[⟨0⟩, ⟨1⟩]
#guard afterBothDeclareMulligan.log.any (fun s => mentions s "will take a mulligan")

def afterChandraBottomsBothMulligan : Game :=
  let id := (afterBothDeclareMulligan.player ⟨0⟩).hand[0]!
  mustApply afterBothDeclareMulligan ⟨0⟩ (.putOnBottom #[id])

#guard afterChandraBottomsBothMulligan.pending == .putOnBottom ⟨1⟩ 1
#guard afterChandraBottomsBothMulligan.actor == some ⟨1⟩
#guard (afterChandraBottomsBothMulligan.player ⟨0⟩).hand.size == 6
#guard (afterChandraBottomsBothMulligan.player ⟨1⟩).hand.size == 7

#guard started.pending == .none
#guard (started.player ⟨0⟩).keptOpeningHand
#guard (started.player ⟨1⟩).keptOpeningHand

-- Lands cannot be played before opening hands are kept.
#guard
  match drawnHands.apply ⟨0⟩ (.playLand (drawnHands.player ⟨0⟩).hand[0]!) with
  | .error _ => true
  | .ok _ => false

-- Nissa cannot declare before Chandra in the first round.
#guard
  match drawnHands.apply ⟨1⟩ .takeMulligan with
  | .error msg => mentions msg "not your turn"
  | .ok _ => false

#guard
  match started.apply ⟨0⟩ .takeMulligan with
  | .error msg => mentions msg "Not time to take a mulligan"
  | .ok _ => false

#guard
  match afterChandraMulligan.apply ⟨0⟩ (.putOnBottom #[]) with
  | .error msg => mentions msg "exactly 1"
  | .ok _ => false

#guard
  match afterChandraMulligan.apply ⟨0⟩ (.putOnBottom #[⟨99999⟩]) with
  | .error msg => msg == "no such object"
  | .ok _ => false

/-- The seventh mulligan leaves a zero-card hand; further mulligans are illegal. -/
def seventhMulligan : Game :=
  let g := drawnHands.modifyPlayer ⟨0⟩ (fun pl => { pl with mulligansTaken := 6 })
  let g := mustApply g ⟨0⟩ .takeMulligan
  mustApply g ⟨1⟩ .keep

#guard seventhMulligan.pending == .putOnBottom ⟨0⟩ 7

def afterZeroHand : Game :=
  mustApply seventhMulligan ⟨0⟩ (.putOnBottom (seventhMulligan.player ⟨0⟩).hand)

#guard (afterZeroHand.player ⟨0⟩).hand.size == 0
#guard (afterZeroHand.player ⟨0⟩).keptOpeningHand
#guard afterZeroHand.pending == .none
#guard afterZeroHand.step == .upkeep

#guard
  let g := drawnHands.modifyPlayer ⟨0⟩ (fun pl => { pl with mulligansTaken := 7 })
  match g.apply ⟨0⟩ .takeMulligan with
  | .error msg => mentions msg "zero cards"
  | .ok _ => false

-- The heuristic keeps opening hands rather than mulliganing.
#guard
  match Agent.choose drawnHands ⟨0⟩ with
  | some .keep => true
  | _ => false

def agentKeepsHands : Game := Agent.play drawnHands 10

#guard (agentKeepsHands.player ⟨0⟩).keptOpeningHand
#guard (agentKeepsHands.player ⟨1⟩).keptOpeningHand
#guard !agentKeepsHands.openingHandsPending
#guard agentKeepsHands.log.any (fun s => mentions s "takes the first turn")

/-- Two untapped Mountains and a Wayfarer's Bauble; a land has already been
played this turn so the agent will activate rather than play another land. -/
def baubleReady : Game :=
  let g := skipTo started .precombatMain 80
  let g := addUntappedLand g mountain
  let g := addUntappedLand g mountain
  let g := addPermanent g wayfarersBauble ⟨0⟩ ⟨0⟩
  g.modifyPlayer ⟨0⟩ (fun pl => { pl with landsPlayedThisTurn := 1 })

def baubleSource (g : Game) : GameObject :=
  namedPermanent g "Wayfarer's Bauble"

#guard wayfarersBauble.activatedAbilities.size == 1
#guard wayfarersBauble.manaAbilities.isEmpty
#guard baubleReady.hasPriority ⟨0⟩
#guard baubleReady.canActivate ⟨0⟩ (baubleSource baubleReady)
  (wayfarersBauble.activatedAbilities[0]!)
#guard !(baubleReady.canActivate ⟨1⟩ (baubleSource baubleReady)
  (wayfarersBauble.activatedAbilities[0]!))

-- The heuristic activates the bauble when {2} is available.
#guard
  match Agent.choose baubleReady ⟨0⟩ with
  | some (.activate id 0) => id == (baubleSource baubleReady).id
  | _ => false

def proposedBauble : Game :=
  mustApply baubleReady ⟨0⟩ (.activate (baubleSource baubleReady).id 0)

#guard proposedBauble.pending == .activateManaAbilities ⟨0⟩
#guard proposedBauble.proposedSpell.isSome
#guard
  match proposedBauble.proposedSpell with
  | some prop => prop.kind == .activatedAbility
  | none => false
#guard proposedBauble.stack.size == 1
#guard (proposedBauble.object! proposedBauble.stack.back!.objectId).sourceId ==
  some (baubleSource proposedBauble).id
#guard (namedPermanent proposedBauble "Wayfarer's Bauble").isOnBattlefield
#guard proposedBauble.log.any (fun s => mentions s "begins activating Wayfarer's Bauble")
#guard proposedBauble.log.any (fun s => mentions s "may activate mana abilities (CR 601.2g)")

-- Opponent cannot activate Chandra's bauble.
#guard
  match baubleReady.activateAbility ⟨1⟩ (baubleSource baubleReady).id 0 with
  | .error _ => true
  | .ok _ => false

-- A land has no non-mana activated ability.
#guard
  match (baubleReady.permanentsOf ⟨0⟩).find? (·.printed.isLand) with
  | none => false
  | some land =>
    match baubleReady.activateAbility ⟨0⟩ land.id 0 with
    | .error msg => mentions msg "has no activated ability"
    | .ok _ => false

def tapNextMana (g : Game) (p : PlayerId) : Game :=
  match (g.manaSources p)[0]? with
  | none => panic! "expected a mana source"
  | some (src, types) =>
    match types[0]? with
    | none => panic! "expected a mana type"
    | some t => mustApply g p (.tapForMana src.id t)

/-- Paying without enough mana reverses the activation (CR 602.2 / 733.1). -/
def reversedBauble : Game :=
  mustApply proposedBauble ⟨0⟩ .pay

#guard reversedBauble.pending == .none
#guard reversedBauble.proposedSpell.isNone
#guard reversedBauble.stack.isEmpty
#guard reversedBauble.hasPriority ⟨0⟩
#guard (namedPermanent reversedBauble "Wayfarer's Bauble").isOnBattlefield
#guard reversedBauble.log.any (fun s => mentions s "the activation is reversed")

def tappedOnceForBauble : Game := tapNextMana proposedBauble ⟨0⟩
def tappedTwiceForBauble : Game := tapNextMana tappedOnceForBauble ⟨0⟩

#guard (tappedTwiceForBauble.player ⟨0⟩).manaPool.canPay (ManaCost.ofGeneric 2)
#guard tappedTwiceForBauble.pending == .activateManaAbilities ⟨0⟩

def paidBauble : Game :=
  mustApply tappedTwiceForBauble ⟨0⟩ .pay

#guard paidBauble.pending == .none
#guard paidBauble.proposedSpell.isNone
#guard paidBauble.hasPriority ⟨0⟩
#guard paidBauble.stack.size == 1
#guard (paidBauble.player ⟨0⟩).manaPool.isEmpty
#guard (paidBauble.player ⟨0⟩).graveyard.any (fun id =>
  (paidBauble.object! id).name == "Wayfarer's Bauble")
#guard !(paidBauble.battlefield.any (fun o => o.name == "Wayfarer's Bauble"))
#guard paidBauble.log.any (fun s => mentions s "sacrifices Wayfarer's Bauble")
#guard paidBauble.log.any (fun s => mentions s "activates Wayfarer's Bauble")

-- The agent pays once the pool covers {2}.
#guard
  match Agent.choose tappedTwiceForBauble ⟨0⟩ with
  | some .pay => true
  | _ => false

def resolvedBauble : Game := passBoth paidBauble

#guard resolvedBauble.stack.isEmpty
#guard (resolvedBauble.battlefield.filter (fun o => o.name == "Mountain")).size == 3
#guard (resolvedBauble.battlefield.filter (fun o =>
  o.name == "Mountain" && o.status.tapped)).size == 3
#guard resolvedBauble.log.any (fun s =>
  mentions s "puts Mountain onto the battlefield tapped")
#guard resolvedBauble.log.any (fun s => mentions s "shuffles their library")

-- Lands put onto the battlefield this way are not a land drop (CR 305.3).
#guard (resolvedBauble.player ⟨0⟩).landsPlayedThisTurn == 1

/-- Snowslope Hunter plus fodder and a known library top, in the precombat main. -/
def hunterReady : Game :=
  let g := skipTo started .precombatMain 80
  let g := addPermanent g snowslopeHunter ⟨0⟩ ⟨0⟩
  let g := addPermanent g ragingGoblin ⟨0⟩ ⟨0⟩
  let g := addPermanent g grayOgre ⟨0⟩ ⟨0⟩
  let g := addUntappedLand g mountain
  let g := addToLibraryTop g lightningBolt ⟨0⟩
  g.modifyPlayer ⟨0⟩ (fun pl => { pl with landsPlayedThisTurn := 1 })

def hunterSource (g : Game) : GameObject :=
  namedPermanent g "Snowslope Hunter"

def hunterFodder (g : Game) : GameObject :=
  namedPermanent g "Raging Goblin"

def hunterAbility : ActivatedAbility :=
  snowslopeHunter.activatedAbilities[0]!

#guard snowslopeHunter.activatedAbilities.size == 1
#guard hunterAbility.cost.sacrificeAnotherCreatureOrArtifact
#guard hunterAbility.effect == .exileTopPlayUntilEndOfNextTurn
#guard hunterAbility.onlyDuringYourTurn
#guard hunterAbility.onceEachTurn
#guard !hunterAbility.onlyAsSorcery
#guard hunterReady.canActivate ⟨0⟩ (hunterSource hunterReady) hunterAbility
#guard !(hunterReady.canActivate ⟨1⟩ (hunterSource hunterReady) hunterAbility)
#guard (hunterReady.sacrificeCreatureOrArtifactChoices ⟨0⟩
  (hunterSource hunterReady).id).any (fun o => o.name == "Raging Goblin")

-- The heuristic begins activating the hunter when another creature is available.
#guard
  match Agent.choose hunterReady ⟨0⟩ with
  | some (.activate id 0) => id == (hunterSource hunterReady).id
  | _ => false

def proposedHunter : Game :=
  mustApply hunterReady ⟨0⟩ (.activate (hunterSource hunterReady).id 0)

#guard proposedHunter.pending == .activateManaAbilities ⟨0⟩
#guard proposedHunter.proposedSpell.isSome
#guard proposedHunter.stack.size == 1
#guard (namedPermanent proposedHunter "Raging Goblin").isOnBattlefield
#guard proposedHunter.log.any (fun s => mentions s "begins activating Snowslope Hunter")
#guard proposedHunter.log.any (fun s => mentions s "may activate mana abilities (CR 601.2g)")

-- Sacrifice is not chosen at `activate`; it comes after `pay`.
#guard
  match proposedHunter.apply ⟨0⟩ (.sacrifice (hunterFodder proposedHunter).id) with
  | .error msg => mentions msg "Not time to sacrifice"
  | .ok _ => false

-- The heuristic pays the empty mana cost next.
#guard
  match Agent.choose proposedHunter ⟨0⟩ with
  | some .pay => true
  | _ => false

def paidHunter : Game :=
  mustApply proposedHunter ⟨0⟩ .pay

#guard
  match paidHunter.pending with
  | .sacrificePermanent p sid =>
    p == ⟨0⟩ && sid == (hunterSource paidHunter).id
  | _ => false
#guard paidHunter.proposedSpell.isSome
#guard (namedPermanent paidHunter "Raging Goblin").isOnBattlefield
#guard paidHunter.log.any (fun s =>
  mentions s "must sacrifice another creature or artifact")

-- Cannot sacrifice the hunter itself, a land, or skip the choice.
#guard
  match paidHunter.apply ⟨0⟩ (.sacrifice (hunterSource paidHunter).id) with
  | .error msg => mentions msg "Can't sacrifice"
  | .ok _ => false

#guard
  match (paidHunter.permanentsOf ⟨0⟩).find? (·.printed.isLand) with
  | none => false
  | some land =>
    match paidHunter.apply ⟨0⟩ (.sacrifice land.id) with
    | .error msg => mentions msg "Can't sacrifice"
    | .ok _ => false

#guard
  match Agent.choose paidHunter ⟨0⟩ with
  | some (.sacrifice id) => id == (hunterFodder paidHunter).id
  | _ => false

def activatedHunter : Game :=
  mustApply paidHunter ⟨0⟩ (.sacrifice (hunterFodder paidHunter).id)

#guard activatedHunter.pending == .none
#guard activatedHunter.proposedSpell.isNone
#guard activatedHunter.hasPriority ⟨0⟩
#guard activatedHunter.stack.size == 1
#guard (activatedHunter.object! activatedHunter.stack.back!.objectId).sourceId ==
  some (hunterSource activatedHunter).id
#guard (namedPermanent activatedHunter "Snowslope Hunter").isOnBattlefield
#guard !(activatedHunter.battlefield.any (fun o => o.name == "Raging Goblin"))
#guard (activatedHunter.player ⟨0⟩).graveyard.any (fun id =>
  (activatedHunter.object! id).name == "Raging Goblin")
#guard (namedPermanent activatedHunter "Snowslope Hunter").status.activationsThisTurn == 1
#guard activatedHunter.log.any (fun s => mentions s "sacrifices Raging Goblin")
#guard activatedHunter.log.any (fun s => mentions s "activates Snowslope Hunter")

/-- Finish activating Snowslope Hunter by paying, then sacrificing `sacName`. -/
def completeHunterActivation (g : Game) (sacName : String) : Game :=
  let g := mustApply g ⟨0⟩ (.activate (hunterSource g).id 0)
  let g := mustApply g ⟨0⟩ .pay
  mustApply g ⟨0⟩ (.sacrifice (namedPermanent g sacName).id)

-- Only once each turn: a second fodder still cannot be spent this turn.
def hunterActivatedOnce : Game :=
  completeHunterActivation hunterReady "Raging Goblin"

#guard
  match hunterActivatedOnce.activateAbility ⟨0⟩ (hunterSource hunterActivatedOnce).id 0 with
  | .error msg => mentions msg "only once each turn"
  | .ok _ => false
#guard !(hunterActivatedOnce.canActivate ⟨0⟩ (hunterSource hunterActivatedOnce) hunterAbility)

def resolvedHunter : Game := passBoth activatedHunter

#guard resolvedHunter.stack.isEmpty
#guard resolvedHunter.objects.any (fun o => o.zone == .exile && o.name == "Lightning Bolt")
#guard resolvedHunter.log.any (fun s =>
  mentions s "exiles Lightning Bolt and may play it until the end of their next turn")

def exiledBolt (g : Game) : GameObject :=
  match g.objects.find? (fun o => o.zone == .exile && o.name == "Lightning Bolt") with
  | some o => o
  | none => panic! "expected Lightning Bolt in exile"

#guard resolvedHunter.mayPlayFromExile ⟨0⟩ (exiledBolt resolvedHunter)
#guard !(resolvedHunter.mayPlayFromExile ⟨1⟩ (exiledBolt resolvedHunter))
#guard resolvedHunter.canCast ⟨0⟩ (exiledBolt resolvedHunter)
#guard !(resolvedHunter.canCast ⟨1⟩ (exiledBolt resolvedHunter))

-- Opponent cannot play the exiled card.
#guard
  match resolvedHunter.castSpell ⟨1⟩ (exiledBolt resolvedHunter).id with
  | .error _ => true
  | .ok _ => false

-- Cast the exiled Lightning Bolt the same turn (CR 701.14).
def proposedExiledBolt : Game :=
  proposeTargeted resolvedHunter ⟨0⟩
    (exiledBolt resolvedHunter).id (Target.player ⟨1⟩)

#guard proposedExiledBolt.pending == .activateManaAbilities ⟨0⟩
#guard !(proposedExiledBolt.objects.any (fun o => o.zone == .exile && o.name == "Lightning Bolt"))
#guard proposedExiledBolt.log.any (fun s => mentions s "begins casting Lightning Bolt")

def paidExiledBolt : Game :=
  mustApply (tapNextMana proposedExiledBolt ⟨0⟩) ⟨0⟩ .pay

def resolvedExiledBolt : Game := passBoth paidExiledBolt

#guard resolvedExiledBolt.stack.isEmpty
#guard (resolvedExiledBolt.player ⟨1⟩).life == 17
#guard resolvedExiledBolt.log.any (fun s => mentions s "is dealt 3 damage")
#guard !(resolvedExiledBolt.objects.any (fun o => o.zone == .exile && o.name == "Lightning Bolt"))

-- Playing an exiled land uses the land drop.
def hunterLandReady : Game :=
  let g := skipTo started .precombatMain 80
  let g := addPermanent g snowslopeHunter ⟨0⟩ ⟨0⟩
  let g := addPermanent g ragingGoblin ⟨0⟩ ⟨0⟩
  addToLibraryTop g mountain ⟨0⟩

def resolvedHunterLand : Game :=
  passBoth (completeHunterActivation hunterLandReady "Raging Goblin")

def exiledMountain (g : Game) : GameObject :=
  match g.objects.find? (fun o => o.zone == .exile && o.name == "Mountain") with
  | some o => o
  | none => panic! "expected Mountain in exile"

#guard resolvedHunterLand.mayPlayFromExile ⟨0⟩ (exiledMountain resolvedHunterLand)
#guard resolvedHunterLand.canPlayLand ⟨0⟩

def playedExiledLand : Game :=
  mustApply resolvedHunterLand ⟨0⟩ (.playLand (exiledMountain resolvedHunterLand).id)

#guard (playedExiledLand.player ⟨0⟩).landsPlayedThisTurn == 1
#guard playedExiledLand.battlefield.any (fun o => o.name == "Mountain")
#guard playedExiledLand.log.any (fun s => mentions s "plays Mountain")
#guard !(playedExiledLand.objects.any (fun o => o.zone == .exile && o.name == "Mountain"))

-- Activate only during your turn: Chandra has priority on Nissa's turn.
def hunterOnNissaTurn : Game :=
  let g := skipTo hunterReady .end 80
  let g := passBoth g
  let g := skipTo g .precombatMain 80
  mustApply g ⟨1⟩ .pass

#guard hunterOnNissaTurn.activePlayer == ⟨1⟩
#guard hunterOnNissaTurn.hasPriority ⟨0⟩
#guard
  match hunterOnNissaTurn.activateAbility ⟨0⟩ (hunterSource hunterOnNissaTurn).id 0 with
  | .error msg => mentions msg "only during your turn"
  | .ok _ => false

-- Instant-speed: the hunter can activate during the end step of your turn.
def hunterAtEndStep : Game := skipTo hunterReady .end 80

#guard hunterAtEndStep.step == .end
#guard hunterAtEndStep.canActivate ⟨0⟩ (hunterSource hunterAtEndStep) hunterAbility

-- Permission lasts through the next turn, then expires.
def hunterPermissionActive : Game :=
  let g := skipTo resolvedHunter .end 80
  let g := passBoth g
  skipTo g .precombatMain 80

#guard hunterPermissionActive.activePlayer == ⟨1⟩
#guard hunterPermissionActive.mayPlayFromExile ⟨0⟩ (exiledBolt hunterPermissionActive)

def hunterOnNextTurn : Game :=
  let g := skipTo hunterPermissionActive .end 80
  let g := passBoth g
  skipTo g .precombatMain 80

#guard hunterOnNextTurn.activePlayer == ⟨0⟩
#guard hunterOnNextTurn.mayPlayFromExile ⟨0⟩ (exiledBolt hunterOnNextTurn)
#guard hunterOnNextTurn.canActivate ⟨0⟩ (hunterSource hunterOnNextTurn) hunterAbility

def hunterActivatedNextTurn : Game :=
  completeHunterActivation hunterOnNextTurn "Gray Ogre"

#guard hunterActivatedNextTurn.log.any (fun s => mentions s "activates Snowslope Hunter")
#guard hunterActivatedNextTurn.log.any (fun s => mentions s "sacrifices Gray Ogre")

def hunterPermissionExpired : Game :=
  let g := skipTo hunterOnNextTurn .end 80
  let g := passBoth g
  let g := skipTo g .precombatMain 80
  mustApply g ⟨1⟩ .pass

#guard hunterPermissionExpired.activePlayer == ⟨1⟩
#guard hunterPermissionExpired.hasPriority ⟨0⟩
#guard hunterPermissionExpired.log.any (fun s =>
  mentions s "can no longer be played from exile")
#guard
  match hunterPermissionExpired.objects.find? (fun o =>
    o.zone == .exile && o.name == "Lightning Bolt") with
  | none => false
  | some o => !hunterPermissionExpired.mayPlayFromExile ⟨0⟩ o
#guard
  match hunterPermissionExpired.objects.find? (fun o =>
    o.zone == .exile && o.name == "Lightning Bolt") with
  | none => false
  | some o =>
    match hunterPermissionExpired.castSpell ⟨0⟩ o.id with
    | .error msg => mentions msg "may not play that card from exile"
    | .ok _ => false

-- Empty library: the ability still resolves.
def hunterEmptyLibrary : Game :=
  let g := skipTo started .precombatMain 80
  let g := addPermanent g snowslopeHunter ⟨0⟩ ⟨0⟩
  let g := addPermanent g ragingGoblin ⟨0⟩ ⟨0⟩
  g.modifyPlayer ⟨0⟩ (fun pl => { pl with library := #[] })

def resolvedHunterEmpty : Game :=
  passBoth (completeHunterActivation hunterEmptyLibrary "Raging Goblin")

#guard resolvedHunterEmpty.stack.isEmpty
#guard resolvedHunterEmpty.log.any (fun s => mentions s "no cards in their library to exile")
#guard !(resolvedHunterEmpty.objects.any (fun o => o.zone == .exile))

/-- Orcish Siegemaster grants trample to other Orcs and Goblins you control. -/
def siegeAndGoblin : Game :=
  addPermanent (addPermanent started orcishSiegemaster ⟨0⟩ ⟨0⟩) ragingGoblin ⟨0⟩ ⟨0⟩

def siegeAndOgre : Game :=
  addPermanent (addPermanent started orcishSiegemaster ⟨0⟩ ⟨0⟩) grayOgre ⟨0⟩ ⟨0⟩

def siegeAndOppGoblin : Game :=
  addPermanent (addPermanent started orcishSiegemaster ⟨0⟩ ⟨0⟩) ragingGoblin ⟨1⟩ ⟨1⟩

#guard siegeAndGoblin.hasTrample (namedPermanent siegeAndGoblin "Orcish Siegemaster")
#guard siegeAndGoblin.hasTrample (namedPermanent siegeAndGoblin "Raging Goblin")
#guard (siegeAndGoblin.effectiveKeywords (namedPermanent siegeAndGoblin "Raging Goblin")).trample
#guard (siegeAndGoblin.effectiveKeywords (namedPermanent siegeAndGoblin "Raging Goblin")).haste
#guard !withGoblin.hasTrample (lastPermanent withGoblin)
#guard !siegeAndOgre.hasTrample (namedPermanent siegeAndOgre "Gray Ogre")
#guard !siegeAndOppGoblin.hasTrample (namedPermanent siegeAndOppGoblin "Raging Goblin")

/-- Snowslope Hunter (a Goblin) trampling over Llanowar Elves. -/
def siegeHunterVsElves : Game :=
  let g := addPermanent started orcishSiegemaster ⟨0⟩ ⟨0⟩
  let g := addPermanent g snowslopeHunter ⟨0⟩ ⟨0⟩
  addPermanent g llanowarElves ⟨1⟩ ⟨1⟩

def hunterGrantedTrampleAttack : Game :=
  let g := passBoth (skipTo siegeHunterVsElves .beginningOfCombat 80)
  mustApply g ⟨0⟩ (.declareAttackers #[(namedPermanent g "Snowslope Hunter").id])

def hunterGrantedTrampleBlocked : Game :=
  let g := passBoth hunterGrantedTrampleAttack
  mustApply g ⟨1⟩ (.declareBlockers #[(
    (namedPermanent g "Llanowar Elves").id,
    (namedPermanent g "Snowslope Hunter").id)])

def afterGrantedTrample : Game := passBoth hunterGrantedTrampleBlocked

#guard afterGrantedTrample.log.any (fun s =>
  mentions s "Snowslope Hunter deals 1 combat damage to Llanowar Elves")
#guard afterGrantedTrample.log.any (fun s =>
  mentions s "Snowslope Hunter tramples for 1 to Nissa")
#guard (afterGrantedTrample.player ⟨1⟩).life == 19

/-- Without the Siegemaster, the same Goblin assigns all damage to the blocker. -/
def hunterOnlyVsElves : Game :=
  addPermanent (addPermanent started snowslopeHunter ⟨0⟩ ⟨0⟩) llanowarElves ⟨1⟩ ⟨1⟩

def afterHunterNoTrample : Game :=
  let g := passBoth (skipTo hunterOnlyVsElves .beginningOfCombat 80)
  let g := mustApply g ⟨0⟩ (.declareAttackers #[(namedPermanent g "Snowslope Hunter").id])
  let g := passBoth g
  let g := mustApply g ⟨1⟩ (.declareBlockers #[(
    (namedPermanent g "Llanowar Elves").id,
    (namedPermanent g "Snowslope Hunter").id)])
  passBoth g

#guard afterHunterNoTrample.log.any (fun s =>
  mentions s "Snowslope Hunter deals 2 combat damage to Llanowar Elves")
#guard !afterHunterNoTrample.log.any (fun s => mentions s "tramples")
#guard (afterHunterNoTrample.player ⟨1⟩).life == 20

/-- A non-Orc, non-Goblin does not receive the grant. -/
def siegeOgreVsElves : Game :=
  let g := addPermanent started orcishSiegemaster ⟨0⟩ ⟨0⟩
  let g := addPermanent g grayOgre ⟨0⟩ ⟨0⟩
  addPermanent g llanowarElves ⟨1⟩ ⟨1⟩

def afterOgreNoTrample : Game :=
  let g := passBoth (skipTo siegeOgreVsElves .beginningOfCombat 80)
  let g := mustApply g ⟨0⟩ (.declareAttackers #[(namedPermanent g "Gray Ogre").id])
  let g := passBoth g
  let g := mustApply g ⟨1⟩ (.declareBlockers #[(
    (namedPermanent g "Llanowar Elves").id,
    (namedPermanent g "Gray Ogre").id)])
  passBoth g

#guard afterOgreNoTrample.log.any (fun s =>
  mentions s "Gray Ogre deals 2 combat damage to Llanowar Elves")
#guard !afterOgreNoTrample.log.any (fun s => mentions s "tramples")

/-- Attack trigger: +X/+0 where X is the greatest power among creatures you control. -/
def siegeGiantVsBears : Game :=
  let g := addPermanent started orcishSiegemaster ⟨0⟩ ⟨0⟩
  let g := addPermanent g hillGiant ⟨0⟩ ⟨0⟩
  addPermanent g grizzlyBears ⟨1⟩ ⟨1⟩

def siegeAttackDeclared : Game :=
  let g := passBoth (skipTo siegeGiantVsBears .beginningOfCombat 80)
  mustApply g ⟨0⟩ (.declareAttackers #[(namedPermanent g "Orcish Siegemaster").id])

#guard siegeAttackDeclared.stack.size == 1
#guard (siegeAttackDeclared.object! siegeAttackDeclared.stack.back!.objectId).name ==
  "Orcish Siegemaster's ability"
#guard (siegeAttackDeclared.object! siegeAttackDeclared.stack.back!.objectId).sourceId ==
  some (namedPermanent siegeAttackDeclared "Orcish Siegemaster").id
#guard siegeAttackDeclared.log.any (fun s => mentions s "attack trigger is put on the stack")
#guard (namedPermanent siegeAttackDeclared "Orcish Siegemaster").power == 0
#guard siegeAttackDeclared.step == .declareAttackers
#guard siegeAttackDeclared.hasPriority ⟨0⟩

def siegePumpResolved : Game := passBoth siegeAttackDeclared

#guard siegePumpResolved.stack.isEmpty
#guard (namedPermanent siegePumpResolved "Orcish Siegemaster").power == 3
#guard siegePumpResolved.log.any (fun s => mentions s "gets +3/+0 until end of turn")
#guard siegePumpResolved.step == .declareAttackers

def siegeReadyToBlock : Game := passBoth siegePumpResolved

#guard siegeReadyToBlock.pending == .declareBlockers

def siegeBlocked : Game :=
  let g := siegeReadyToBlock
  mustApply g ⟨1⟩ (.declareBlockers #[(
    (namedPermanent g "Grizzly Bears").id,
    (namedPermanent g "Orcish Siegemaster").id)])

def afterSiegeCombat : Game := passBoth siegeBlocked

#guard afterSiegeCombat.log.any (fun s =>
  mentions s "Orcish Siegemaster deals 2 combat damage to Grizzly Bears")
#guard afterSiegeCombat.log.any (fun s =>
  mentions s "Orcish Siegemaster tramples for 1 to Nissa")
#guard (afterSiegeCombat.player ⟨1⟩).life == 19

/-- Alone, X is the Siegemaster's own power (0). -/
def siegeAloneResolved : Game :=
  let g := addPermanent started orcishSiegemaster ⟨0⟩ ⟨0⟩
  let g := passBoth (skipTo g .beginningOfCombat 80)
  let g := mustApply g ⟨0⟩ (.declareAttackers #[(namedPermanent g "Orcish Siegemaster").id])
  passBoth g

#guard (namedPermanent siegeAloneResolved "Orcish Siegemaster").power == 0
#guard siegeAloneResolved.log.any (fun s => mentions s "gets +0/+0 until end of turn")

/-- Opponent creatures do not count toward X. -/
def siegeVsWurmResolved : Game :=
  let g := addPermanent started orcishSiegemaster ⟨0⟩ ⟨0⟩
  let g := addPermanent g crawWurm ⟨1⟩ ⟨1⟩
  let g := passBoth (skipTo g .beginningOfCombat 80)
  let g := mustApply g ⟨0⟩ (.declareAttackers #[(namedPermanent g "Orcish Siegemaster").id])
  passBoth g

#guard (namedPermanent siegeVsWurmResolved "Orcish Siegemaster").power == 0

/-- X uses current power, including until-end-of-turn pumps. -/
def siegePumpedGiantResolved : Game :=
  let g := addPermanent started orcishSiegemaster ⟨0⟩ ⟨0⟩
  let g := addPermanent g hillGiant ⟨0⟩ ⟨0⟩
  let g := g.applyEffect ⟨0⟩ (.pump 2 0)
    #[Target.permanent (namedPermanent g "Hill Giant").id]
  let g := passBoth (skipTo g .beginningOfCombat 80)
  let g := mustApply g ⟨0⟩ (.declareAttackers #[(namedPermanent g "Orcish Siegemaster").id])
  passBoth g

#guard (namedPermanent siegePumpedGiantResolved "Hill Giant").power == 5
#guard (namedPermanent siegePumpedGiantResolved "Orcish Siegemaster").power == 5
#guard siegePumpedGiantResolved.log.any (fun s => mentions s "gets +5/+0 until end of turn")

/-- If the source leaves before the trigger resolves, the pump does not happen. -/
def siegeSourceGone : Game :=
  let g := siegeAttackDeclared
  let id := (namedPermanent g "Orcish Siegemaster").id
  let (g, _) := g.move id (.graveyard (g.object! id).owner) none
  passBoth g

#guard siegeSourceGone.stack.isEmpty
#guard !(siegeSourceGone.battlefield.any (fun o => o.name == "Orcish Siegemaster"))
#guard siegeSourceGone.log.any (fun s => mentions s "source is no longer in play")
#guard (namedPermanent siegeSourceGone "Hill Giant").status.pumpPower == 0

/-- The +X/+0 wears off in cleanup. -/
def afterSiegeCleanup : Game := passBoth (skipTo siegePumpResolved .end 80)

#guard (namedPermanent afterSiegeCleanup "Orcish Siegemaster").power == 0
#guard (namedPermanent afterSiegeCleanup "Orcish Siegemaster").status.pumpPower == 0

/-- Printed trample still assigns leftover damage (Beorn 5/5 vs Grizzly Bears 2/2). -/
def afterBeornTrample : Game :=
  let g := addPermanent (addPermanent started beornReluctantHost ⟨0⟩ ⟨0⟩)
    grizzlyBears ⟨1⟩ ⟨1⟩
  let g := passBoth (skipTo g .beginningOfCombat 80)
  let g := mustApply g ⟨0⟩ (.declareAttackers #[(namedPermanent g "Beorn, Reluctant Host").id])
  let g := passBoth g
  let g := mustApply g ⟨1⟩ (.declareBlockers #[(
    (namedPermanent g "Grizzly Bears").id,
    (namedPermanent g "Beorn, Reluctant Host").id)])
  passBoth g

#guard afterBeornTrample.log.any (fun s =>
  mentions s "Beorn, Reluctant Host deals 2 combat damage to Grizzly Bears")
#guard afterBeornTrample.log.any (fun s =>
  mentions s "Beorn, Reluctant Host tramples for 3 to Nissa")
#guard (afterBeornTrample.player ⟨1⟩).life == 17

/-- Battle-Scarred Goblin vs Grizzly Bears: becomes-blocked trigger, then combat. -/
def goblinVsBears : Game :=
  addPermanent (addPermanent started battleScarredGoblin ⟨0⟩ ⟨0⟩) grizzlyBears ⟨1⟩ ⟨1⟩

def goblinDeclaredAttacker : Game :=
  let g := passBoth (skipTo goblinVsBears .beginningOfCombat 80)
  mustApply g ⟨0⟩ (.declareAttackers #[(namedPermanent g "Battle-Scarred Goblin").id])

def goblinReadyToBlock : Game := passBoth goblinDeclaredAttacker

def goblinBlockedByBears : Game :=
  let g := goblinReadyToBlock
  mustApply g ⟨1⟩ (.declareBlockers #[(
    (namedPermanent g "Grizzly Bears").id,
    (namedPermanent g "Battle-Scarred Goblin").id)])

#guard goblinBlockedByBears.stack.size == 1
#guard (goblinBlockedByBears.object! goblinBlockedByBears.stack.back!.objectId).name ==
  "Battle-Scarred Goblin's ability"
#guard (goblinBlockedByBears.object! goblinBlockedByBears.stack.back!.objectId).sourceId ==
  some (namedPermanent goblinBlockedByBears "Battle-Scarred Goblin").id
#guard goblinBlockedByBears.log.any (fun s => mentions s "becomes-blocked trigger is put on the stack")
#guard (namedPermanent goblinBlockedByBears "Battle-Scarred Goblin").status.blocked
#guard goblinBlockedByBears.step == .declareBlockers
#guard goblinBlockedByBears.hasPriority ⟨0⟩
#guard (namedPermanent goblinBlockedByBears "Grizzly Bears").status.damage == 0

def goblinTriggerResolved : Game := passBoth goblinBlockedByBears

#guard goblinTriggerResolved.stack.isEmpty
#guard (namedPermanent goblinTriggerResolved "Grizzly Bears").status.damage == 1
#guard goblinTriggerResolved.log.any (fun s =>
  mentions s "Battle-Scarred Goblin deals 1 damage to Grizzly Bears")
#guard goblinTriggerResolved.step == .declareBlockers
#guard goblinTriggerResolved.battlefield.any (fun o => o.name == "Grizzly Bears")
#guard (goblinTriggerResolved.player ⟨1⟩).life == 20

def afterGoblinBearsCombat : Game := passBoth goblinTriggerResolved

#guard afterGoblinBearsCombat.log.any (fun s =>
  mentions s "Battle-Scarred Goblin deals 2 combat damage to Grizzly Bears")
#guard afterGoblinBearsCombat.log.any (fun s =>
  mentions s "Grizzly Bears deals 2 combat damage to Battle-Scarred Goblin")
#guard (afterGoblinBearsCombat.player ⟨1⟩).life == 20
#guard !(afterGoblinBearsCombat.battlefield.any (fun o => o.name == "Battle-Scarred Goblin"))
#guard !(afterGoblinBearsCombat.battlefield.any (fun o => o.name == "Grizzly Bears"))

/-- A 1/1 blocker dies to the trigger; the Goblin stays blocked and assigns no
combat damage (CR 509.1h / 510.1c). -/
def goblinVsElves : Game :=
  addPermanent (addPermanent started battleScarredGoblin ⟨0⟩ ⟨0⟩) llanowarElves ⟨1⟩ ⟨1⟩

def goblinBlockedByElves : Game :=
  let g := passBoth (skipTo goblinVsElves .beginningOfCombat 80)
  let g := mustApply g ⟨0⟩ (.declareAttackers #[(namedPermanent g "Battle-Scarred Goblin").id])
  let g := passBoth g
  mustApply g ⟨1⟩ (.declareBlockers #[(
    (namedPermanent g "Llanowar Elves").id,
    (namedPermanent g "Battle-Scarred Goblin").id)])

def goblinElvesAfterTrigger : Game := passBoth goblinBlockedByElves

#guard goblinElvesAfterTrigger.stack.isEmpty
#guard goblinElvesAfterTrigger.log.any (fun s =>
  mentions s "Battle-Scarred Goblin deals 1 damage to Llanowar Elves")
#guard goblinElvesAfterTrigger.log.any (fun s => mentions s "Llanowar Elves dies from lethal damage")
#guard !(goblinElvesAfterTrigger.battlefield.any (fun o => o.name == "Llanowar Elves"))
#guard goblinElvesAfterTrigger.objects.any (fun o =>
  o.name == "Llanowar Elves" && o.zone == .graveyard ⟨1⟩)
#guard (namedPermanent goblinElvesAfterTrigger "Battle-Scarred Goblin").status.blocked
#guard goblinElvesAfterTrigger.step == .declareBlockers
#guard (goblinElvesAfterTrigger.player ⟨1⟩).life == 20

def afterGoblinElvesCombat : Game := passBoth goblinElvesAfterTrigger

#guard afterGoblinElvesCombat.log.any (fun s =>
  mentions s "blocked with no remaining blockers and assigns no combat damage")
#guard !afterGoblinElvesCombat.log.any (fun s => mentions s "combat damage to Nissa")
#guard (afterGoblinElvesCombat.player ⟨1⟩).life == 20
#guard afterGoblinElvesCombat.battlefield.any (fun o => o.name == "Battle-Scarred Goblin")
#guard (namedPermanent afterGoblinElvesCombat "Battle-Scarred Goblin").status.damage == 0

/-- Unblocked: the trigger does not fire, and combat damage hits the player. -/
def afterGoblinUnblocked : Game :=
  passBoth (mustApply goblinReadyToBlock ⟨1⟩ (.declareBlockers #[]))

#guard afterGoblinUnblocked.stack.isEmpty
#guard !afterGoblinUnblocked.log.any (fun s => mentions s "becomes-blocked trigger")
#guard (afterGoblinUnblocked.player ⟨1⟩).life == 18
#guard afterGoblinUnblocked.log.any (fun s =>
  mentions s "Battle-Scarred Goblin deals 2 combat damage to Nissa")

/-- CR 509.5c: two blockers still produce one trigger; each takes 1 damage. -/
def goblinVsTwoElves : Game :=
  let g := addPermanent started battleScarredGoblin ⟨0⟩ ⟨0⟩
  let g := addPermanent g llanowarElves ⟨1⟩ ⟨1⟩
  addPermanent g llanowarElves ⟨1⟩ ⟨1⟩

def goblinBlockedByTwoElves : Game :=
  let g := passBoth (skipTo goblinVsTwoElves .beginningOfCombat 80)
  let goblin := namedPermanent g "Battle-Scarred Goblin"
  let elves := g.battlefield.filter (fun o => o.name == "Llanowar Elves")
  let g := mustApply g ⟨0⟩ (.declareAttackers #[goblin.id])
  let g := passBoth g
  mustApply g ⟨1⟩ (.declareBlockers #[(elves[0]!.id, goblin.id), (elves[1]!.id, goblin.id)])

#guard goblinBlockedByTwoElves.stack.size == 1
#guard (goblinBlockedByTwoElves.battlefield.filter (fun o =>
  !o.status.blocking.isEmpty)).size == 2

def goblinTwoElvesAfterTrigger : Game := passBoth goblinBlockedByTwoElves

#guard (goblinTwoElvesAfterTrigger.log.filter (fun s =>
  mentions s "Battle-Scarred Goblin deals 1 damage to Llanowar Elves")).size == 2
#guard (goblinTwoElvesAfterTrigger.battlefield.filter (fun o =>
  o.name == "Llanowar Elves")).isEmpty
#guard (goblinTwoElvesAfterTrigger.objects.filter (fun o =>
  o.name == "Llanowar Elves" && o.zone == .graveyard ⟨1⟩)).size == 2

/-- Two Goblins, one blocked: only the blocked one triggers. -/
def twoGoblinsOneBlocked : Game :=
  let g := addPermanent started battleScarredGoblin ⟨0⟩ ⟨0⟩
  let g := addPermanent g battleScarredGoblin ⟨0⟩ ⟨0⟩
  let g := addPermanent g grizzlyBears ⟨1⟩ ⟨1⟩
  let g := passBoth (skipTo g .beginningOfCombat 80)
  let goblins := g.battlefield.filter (fun o => o.name == "Battle-Scarred Goblin")
  let g := mustApply g ⟨0⟩ (.declareAttackers (goblins.map (·.id)))
  let g := passBoth g
  mustApply g ⟨1⟩ (.declareBlockers #[(
    (namedPermanent g "Grizzly Bears").id,
    goblins[0]!.id)])

#guard twoGoblinsOneBlocked.stack.size == 1
#guard (twoGoblinsOneBlocked.battlefield.filter (fun o =>
  o.name == "Battle-Scarred Goblin" && o.status.blocked)).size == 1
#guard (twoGoblinsOneBlocked.battlefield.filter (fun o =>
  o.name == "Battle-Scarred Goblin" && o.status.attacking && !o.status.blocked)).size == 1

/-- If the source leaves before the trigger resolves, blockers are unharmed. -/
def goblinSourceGone : Game :=
  let g := goblinBlockedByBears
  let id := (namedPermanent g "Battle-Scarred Goblin").id
  let (g, _) := g.move id (.graveyard (g.object! id).owner) none
  passBoth g

#guard goblinSourceGone.stack.isEmpty
#guard goblinSourceGone.log.any (fun s => mentions s "source is no longer in play")
#guard (namedPermanent goblinSourceGone "Grizzly Bears").status.damage == 0

/-- Granted trample plus a killed 1/1 blocker: leftover damage goes to the player
(CR 702.19d). -/
def siegeGoblinVsElves : Game :=
  let g := addPermanent started orcishSiegemaster ⟨0⟩ ⟨0⟩
  let g := addPermanent g battleScarredGoblin ⟨0⟩ ⟨0⟩
  addPermanent g llanowarElves ⟨1⟩ ⟨1⟩

def afterSiegeGoblinElves : Game :=
  let g := passBoth (skipTo siegeGoblinVsElves .beginningOfCombat 80)
  let g := mustApply g ⟨0⟩ (.declareAttackers #[(namedPermanent g "Battle-Scarred Goblin").id])
  let g := passBoth g
  let g := mustApply g ⟨1⟩ (.declareBlockers #[(
    (namedPermanent g "Llanowar Elves").id,
    (namedPermanent g "Battle-Scarred Goblin").id)])
  let g := passBoth g
  passBoth g

#guard afterSiegeGoblinElves.log.any (fun s =>
  mentions s "Battle-Scarred Goblin deals 1 damage to Llanowar Elves")
#guard afterSiegeGoblinElves.log.any (fun s => mentions s "Llanowar Elves dies from lethal damage")
#guard afterSiegeGoblinElves.log.any (fun s =>
  mentions s "Battle-Scarred Goblin tramples for 2 to Nissa")
#guard (afterSiegeGoblinElves.player ⟨1⟩).life == 18
#guard afterSiegeGoblinElves.battlefield.any (fun o => o.name == "Battle-Scarred Goblin")

/-- Fill `p`'s mana pool with `n` green mana. -/
def withGreenMana (g : Game) (p : PlayerId) (n : Nat := 4) : Game :=
  g.modifyPlayer p (fun pl => { pl with manaPool := pl.manaPool.add (.colored .green) n })

/-- Fill `p`'s mana pool with `n` red mana. -/
def withRedMana (g : Game) (p : PlayerId) (n : Nat := 4) : Game :=
  g.modifyPlayer p (fun pl => { pl with manaPool := pl.manaPool.add (.colored .red) n })

/-- Put `aura` onto the battlefield already attached to `host`. -/
def addAttachedAura (g : Game) (aura : CardDef) (host : GameObject)
    (owner controller : PlayerId) : Game :=
  let (g, id) := g.allocId
  let (g, ts) := g.bumpTime
  let obj : GameObject := {
    id := id
    printed := aura
    owner := owner
    controller := some controller
    zone := .battlefield
    timestamp := ts
    attachedTo := some host.id
  }
  { g with objects := g.objects.push obj }

/-- Keep the looked-at cards on top in their current order (CR 701.20). -/
def keepScry (g : Game) : Game :=
  match g.pending with
  | .scry p n => mustApply g p (.scry (g.scryLookedIds p n) #[])
  | _ => panic! "expected a pending scry"

/-- Gift of Strands in hand, Grizzly Bears on the battlefield, enough mana. -/
def giftSetup : Game :=
  let g := addPermanent afterDraw grizzlyBears ⟨0⟩ ⟨0⟩
  withGreenMana (addToHand g giftOfStrands ⟨0⟩) ⟨0⟩

#guard giftSetup.canCast ⟨0⟩ (handCardNamed giftSetup ⟨0⟩ "Gift of Strands")
#guard giftSetup.asSorcery? ⟨0⟩
#guard giftOfStrands.keywords.flash
#guard !giftOfStrands.hasSorcerySpeed

-- An Aura cannot be cast with no creature on the battlefield.
#guard
  let g := withGreenMana (addToHand afterDraw giftOfStrands ⟨0⟩) ⟨0⟩
  !g.canCast ⟨0⟩ (handCardNamed g ⟨0⟩ "Gift of Strands")
#guard
  let g := withGreenMana (addToHand afterDraw giftOfStrands ⟨0⟩) ⟨0⟩
  match g.apply ⟨0⟩ (.cast (handCardNamed g ⟨0⟩ "Gift of Strands").id) with
  | .error msg => mentions msg "requires a target"
  | .ok _ => false

-- Cast proposes the Aura; the target is announced as a later action (CR 601.2c).
#guard
  match giftSetup.apply ⟨0⟩ (.cast (handCardNamed giftSetup ⟨0⟩ "Gift of Strands").id) with
  | .ok g' =>
    match g'.pending with
    | .chooseTargets ⟨0⟩ => g'.stack.back!.targets.isEmpty
    | _ => false
  | .error _ => false

def proposedGift : Game :=
  proposeTargeted giftSetup ⟨0⟩
    (handCardNamed giftSetup ⟨0⟩ "Gift of Strands").id
    (Target.permanent (namedPermanent giftSetup "Grizzly Bears").id)

#guard proposedGift.pending == .activateManaAbilities ⟨0⟩
#guard proposedGift.stack.back!.targets ==
  #[Target.permanent (namedPermanent giftSetup "Grizzly Bears").id]
#guard proposedGift.log.any (fun s => mentions s "chooses Grizzly Bears as a target (CR 601.2c)")

def paidGift : Game := mustApply proposedGift ⟨0⟩ .pay

#guard paidGift.stack.size == 1
#guard paidGift.hasPriority ⟨0⟩

/-- The Aura enters attached and the creature is immediately +3/+3; scry waits on the stack. -/
def giftEntered : Game := passBoth paidGift

#guard (namedPermanent giftEntered "Gift of Strands").attachedTo ==
  some (namedPermanent giftEntered "Grizzly Bears").id
#guard giftEntered.power (namedPermanent giftEntered "Grizzly Bears") == 5
#guard giftEntered.toughness (namedPermanent giftEntered "Grizzly Bears") == 5
#guard (namedPermanent giftEntered "Grizzly Bears").power == 2
#guard giftEntered.stack.size == 1
#guard giftEntered.log.any (fun s => mentions s "attached to Grizzly Bears")
#guard giftEntered.log.any (fun s => mentions s "enters trigger is put on the stack")

def giftScrying : Game := passBoth giftEntered

#guard
  match giftScrying.pending with
  | .scry ⟨0⟩ 2 => true
  | _ => false
#guard giftScrying.actor == some ⟨0⟩
#guard !giftScrying.hasPriority ⟨0⟩
#guard giftScrying.log.any (fun s => mentions s "scries 2")
#guard giftScrying.stack.isEmpty

def giftScried : Game := keepScry giftScrying

#guard giftScried.pending == .none
#guard giftScried.hasPriority ⟨0⟩
#guard giftScried.power (namedPermanent giftScried "Grizzly Bears") == 5

-- The agent keeps scried cards on top.
#guard
  match Agent.choose giftScrying ⟨0⟩ with
  | some (.scry top bottom) =>
    bottom.isEmpty && top == giftScrying.scryLookedIds ⟨0⟩ 2
  | _ => false

/-- Put the current top card on the bottom; the next stays on top. -/
def giftKnownLib : Game :=
  addToLibraryTop (addToLibraryTop giftEntered forest ⟨0⟩) llanowarElves ⟨0⟩

def giftKnownScrying : Game := passBoth giftKnownLib

def giftBottomedElves : Game :=
  let looked := giftKnownScrying.scryLookedIds ⟨0⟩ 2
  -- looked is [Forest, Llanowar Elves] with Elves on top.
  mustApply giftKnownScrying ⟨0⟩ (.scry looked.pop #[looked.back!])

#guard (giftBottomedElves.object! (giftBottomedElves.player ⟨0⟩).library.back!).name == "Forest"
#guard (giftBottomedElves.object! (giftBottomedElves.player ⟨0⟩).library[0]!).name ==
  "Llanowar Elves"
#guard giftBottomedElves.log.any (fun s =>
  mentions s "puts Llanowar Elves on the bottom of their library")

/-- The rest may be put on top in any order (CR 701.20). -/
def giftReorderedTop : Game :=
  let looked := giftKnownScrying.scryLookedIds ⟨0⟩ 2
  -- Reverse the two looked-at cards: Forest becomes the new top.
  mustApply giftKnownScrying ⟨0⟩ (.scry looked.reverse #[])

#guard (giftReorderedTop.object! (giftReorderedTop.player ⟨0⟩).library.back!).name == "Forest"
#guard
  let lib := (giftReorderedTop.player ⟨0⟩).library
  (giftReorderedTop.object! lib[lib.size - 2]!).name == "Llanowar Elves"
#guard giftReorderedTop.log.any (fun s => mentions s "puts Forest on top of their library")
#guard giftReorderedTop.log.any (fun s =>
  mentions s "puts Llanowar Elves on top of their library")
#guard !(giftReorderedTop.log.any (fun s => mentions s "on the bottom of their library"))

/-- The +3/+3 is a continuous effect, so it does not wear off in cleanup. -/
def afterGiftCleanup : Game := passBoth (skipTo giftScried .end 80)

#guard afterGiftCleanup.power (namedPermanent afterGiftCleanup "Grizzly Bears") == 5
#guard (namedPermanent afterGiftCleanup "Grizzly Bears").status.pumpPower == 0

/-- If the target leaves before the Aura resolves, the Aura goes to the graveyard (CR 608.3a). -/
def giftTargetGone : Game :=
  let id := (namedPermanent paidGift "Grizzly Bears").id
  let (g, _) := paidGift.move id (.graveyard ⟨0⟩) none
  passBoth g

#guard !(giftTargetGone.battlefield.any (fun o => o.name == "Gift of Strands"))
#guard giftTargetGone.log.any (fun s => mentions s "illegal Aura target")
#guard (giftTargetGone.player ⟨0⟩).graveyard.any (fun id =>
  (giftTargetGone.object! id).name == "Gift of Strands")

/-- If the enchanted creature leaves, the Aura becomes unattached and SBA 704.5n puts it
in the graveyard. -/
def afterHostLeaves : Game :=
  let id := (namedPermanent giftScried "Grizzly Bears").id
  let (g, _) := giftScried.move id (.graveyard ⟨0⟩) none
  g.checkSBA

#guard afterHostLeaves.log.any (fun s => mentions s "becomes unattached")
#guard afterHostLeaves.log.any (fun s => mentions s "704.5n")
#guard !(afterHostLeaves.battlefield.any (fun o => o.name == "Gift of Strands"))
#guard !(afterHostLeaves.battlefield.any (fun o => o.name == "Grizzly Bears"))

/-- A 0/0 creature survives while Gift of Strands is attached. -/
def zeroEnchanted : Game :=
  let g := addPermanent started zeroZero ⟨0⟩ ⟨0⟩
  addAttachedAura g giftOfStrands (namedPermanent g "Zero/Zero") ⟨0⟩ ⟨0⟩

#guard zeroEnchanted.power (namedPermanent zeroEnchanted "Zero/Zero") == 3
#guard zeroEnchanted.toughness (namedPermanent zeroEnchanted "Zero/Zero") == 3
#guard (zeroEnchanted.checkSBA).battlefield.any (fun o => o.name == "Zero/Zero")

/-- Combat uses the enchanted power. -/
def afterEnchantedCombat : Game :=
  let g := addPermanent started grizzlyBears ⟨0⟩ ⟨0⟩
  let g := addAttachedAura g giftOfStrands (namedPermanent g "Grizzly Bears") ⟨0⟩ ⟨0⟩
  let g := passBoth (skipTo g .beginningOfCombat 80)
  let g := mustApply g ⟨0⟩ (.declareAttackers #[(namedPermanent g "Grizzly Bears").id])
  let g := passBoth g
  let g := mustApply g ⟨1⟩ (.declareBlockers #[])
  passBoth g

#guard afterEnchantedCombat.log.any (fun s =>
  mentions s "Grizzly Bears deals 5 combat damage to Nissa")
#guard (afterEnchantedCombat.player ⟨1⟩).life == 15

/-- Flash lets Gift of Strands be cast when it is not a main phase. -/
def flashWindow : Game :=
  let g := applyIdle (passBoth (skipTo afterDraw .end 80))
  let g := addPermanent g grizzlyBears ⟨0⟩ ⟨0⟩
  withGreenMana (addToHand g giftOfStrands ⟨0⟩) ⟨0⟩

#guard flashWindow.hasPriority ⟨0⟩
#guard !flashWindow.asSorcery? ⟨0⟩
#guard flashWindow.canCast ⟨0⟩ (handCardNamed flashWindow ⟨0⟩ "Gift of Strands")
#guard
  let g := addToHand flashWindow grayOgre ⟨0⟩
  !g.canCast ⟨0⟩ (handCardNamed g ⟨0⟩ "Gray Ogre")

def paidFlashGift : Game :=
  let g := proposeTargeted flashWindow ⟨0⟩
    (handCardNamed flashWindow ⟨0⟩ "Gift of Strands").id
    (Target.permanent (namedPermanent flashWindow "Grizzly Bears").id)
  mustApply g ⟨0⟩ .pay

def flashGiftEntered : Game := passBoth paidFlashGift

#guard flashGiftEntered.step == .upkeep
#guard flashGiftEntered.activePlayer == ⟨1⟩
#guard flashGiftEntered.power (namedPermanent flashGiftEntered "Grizzly Bears") == 5

/-- You may enchant an opponent's creature. -/
def giftOnNissa : Game :=
  let g := addPermanent afterDraw grizzlyBears ⟨1⟩ ⟨1⟩
  let g := withGreenMana (addToHand g giftOfStrands ⟨0⟩) ⟨0⟩
  let g := proposeTargeted g ⟨0⟩
    (handCardNamed g ⟨0⟩ "Gift of Strands").id
    (Target.permanent (namedPermanent g "Grizzly Bears").id)
  let g := mustApply g ⟨0⟩ .pay
  keepScry (passBoth (passBoth g))

#guard giftOnNissa.power (namedPermanent giftOnNissa "Grizzly Bears") == 5
#guard (namedPermanent giftOnNissa "Grizzly Bears").controller == some ⟨1⟩
#guard (namedPermanent giftOnNissa "Gift of Strands").controller == some ⟨0⟩

/-- The agent casts Gift of Strands on its own creature when that is the
playable spell. -/
def agentGiftOnly : Game :=
  let g := addPermanent afterDraw grizzlyBears ⟨0⟩ ⟨0⟩
  let g := g.modifyPlayer ⟨0⟩ (fun pl => { pl with hand := #[], landsPlayedThisTurn := 1 })
  withGreenMana (addToHand g giftOfStrands ⟨0⟩) ⟨0⟩

#guard
  match Agent.choose agentGiftOnly ⟨0⟩ with
  | some (.cast id) => (agentGiftOnly.object! id).name == "Gift of Strands"
  | _ => false

#guard
  let g := mustApply agentGiftOnly ⟨0⟩
    (.cast (handCardNamed agentGiftOnly ⟨0⟩ "Gift of Strands").id)
  match Agent.choose g ⟨0⟩ with
  | some (.target (Target.permanent tid)) => (g.object! tid).name == "Grizzly Bears"
  | _ => false

/-- Scrying 2 with one card looks at that card; an empty library still scries. -/
def scryOneCard : Game :=
  let g := { giftEntered with pending := .none, stack := #[] }
  let g := g.modifyPlayer ⟨0⟩ (fun pl => { pl with library := pl.library.extract (pl.library.size - 1) pl.library.size })
  g.beginScry ⟨0⟩ 2

#guard
  match scryOneCard.pending with
  | .scry ⟨0⟩ 1 => true
  | _ => false

def scryEmpty : Game :=
  let g := { giftEntered with pending := .none, stack := #[] }
  let g := g.modifyPlayer ⟨0⟩ (fun pl => { pl with library := #[] })
  g.beginScry ⟨0⟩ 2

#guard scryEmpty.pending == .none
#guard scryEmpty.log.any (fun s => mentions s "no cards to look at")

/-- Galadhrim Guide in hand with enough mana to cast it (CR 601.2). -/
def guideSetup : Game :=
  withGreenMana (addToHand afterDraw galadhrimGuide ⟨0⟩) ⟨0⟩

#guard guideSetup.canCast ⟨0⟩ (handCardNamed guideSetup ⟨0⟩ "Galadhrim Guide")
#guard guideSetup.asSorcery? ⟨0⟩
#guard !galadhrimGuide.keywords.flash
#guard galadhrimGuide.hasSorcerySpeed

-- A creature without flash cannot be cast when it is not a main phase.
#guard
  let g := applyIdle (passBoth (skipTo afterDraw .end 80))
  let g := withGreenMana (addToHand g galadhrimGuide ⟨0⟩) ⟨0⟩
  !g.asSorcery? ⟨0⟩ && !g.canCast ⟨0⟩ (handCardNamed g ⟨0⟩ "Galadhrim Guide")

def proposedGuide : Game :=
  mustApply guideSetup ⟨0⟩ (.cast (handCardNamed guideSetup ⟨0⟩ "Galadhrim Guide").id)

#guard proposedGuide.pending == .activateManaAbilities ⟨0⟩
#guard proposedGuide.log.any (fun s => mentions s "begins casting Galadhrim Guide")

def paidGuide : Game := mustApply proposedGuide ⟨0⟩ .pay

#guard paidGuide.stack.size == 1
#guard paidGuide.hasPriority ⟨0⟩
#guard paidGuide.log.any (fun s => mentions s "casts Galadhrim Guide")

/-- The creature enters; scry waits on the stack (CR 603.6a). -/
def guideEntered : Game := passBoth paidGuide

#guard (namedPermanent guideEntered "Galadhrim Guide").printed.power == some 3
#guard guideEntered.power (namedPermanent guideEntered "Galadhrim Guide") == 3
#guard guideEntered.toughness (namedPermanent guideEntered "Galadhrim Guide") == 4
#guard guideEntered.stack.size == 1
#guard (guideEntered.object! guideEntered.stack.back!.objectId).triggeredAbility ==
  some (.onEnterScry 2)
#guard (guideEntered.object! guideEntered.stack.back!.objectId).sourceId ==
  some (namedPermanent guideEntered "Galadhrim Guide").id
#guard guideEntered.log.any (fun s => mentions s "enters the battlefield")
#guard guideEntered.log.any (fun s => mentions s "enters trigger is put on the stack")

def guideScrying : Game := passBoth guideEntered

#guard
  match guideScrying.pending with
  | .scry ⟨0⟩ 2 => true
  | _ => false
#guard guideScrying.actor == some ⟨0⟩
#guard !guideScrying.hasPriority ⟨0⟩
#guard guideScrying.log.any (fun s => mentions s "scries 2")
#guard guideScrying.stack.isEmpty
#guard guideScrying.battlefield.any (fun o => o.name == "Galadhrim Guide")

def guideScried : Game := keepScry guideScrying

#guard guideScried.pending == .none
#guard guideScried.hasPriority ⟨0⟩
#guard guideScried.battlefield.any (fun o => o.name == "Galadhrim Guide")

-- The agent keeps scried cards on top.
#guard
  match Agent.choose guideScrying ⟨0⟩ with
  | some (.scry top bottom) =>
    bottom.isEmpty && top == guideScrying.scryLookedIds ⟨0⟩ 2
  | _ => false

/-- Known library: Forest then Elves on top; scry 2 looks at both. -/
def guideKnownLib : Game :=
  addToLibraryTop (addToLibraryTop guideEntered forest ⟨0⟩) llanowarElves ⟨0⟩

def guideKnownScrying : Game := passBoth guideKnownLib

#guard
  let looked := guideKnownScrying.scryLookedIds ⟨0⟩ 2
  looked.size == 2 &&
    (guideKnownScrying.object! looked[0]!).name == "Forest" &&
    (guideKnownScrying.object! looked.back!).name == "Llanowar Elves"

/-- The trigger still scries if Galadhrim Guide has left the battlefield (CR 113.7a). -/
def guideLeftBeforeTrigger : Game :=
  let id := (namedPermanent guideEntered "Galadhrim Guide").id
  let (g, _) := guideEntered.move id (.graveyard ⟨0⟩) none
  passBoth g

#guard
  match guideLeftBeforeTrigger.pending with
  | .scry ⟨0⟩ 2 => true
  | _ => false
#guard !(guideLeftBeforeTrigger.battlefield.any (fun o => o.name == "Galadhrim Guide"))
#guard (guideLeftBeforeTrigger.player ⟨0⟩).graveyard.any (fun id =>
  (guideLeftBeforeTrigger.object! id).name == "Galadhrim Guide")

/-- The agent casts Galadhrim Guide when that is the playable spell. -/
def agentGuideOnly : Game :=
  let g := afterDraw.modifyPlayer ⟨0⟩ (fun pl => { pl with hand := #[], landsPlayedThisTurn := 1 })
  withGreenMana (addToHand g galadhrimGuide ⟨0⟩) ⟨0⟩

#guard
  match Agent.choose agentGuideOnly ⟨0⟩ with
  | some (.cast id) => (agentGuideOnly.object! id).name == "Galadhrim Guide"
  | _ => false

/-- Goblin Cratermaker plus an opposing 2/2 and a Mountain; a land drop is already
used so the agent will activate rather than play another land. -/
def cratermakerReady : Game :=
  let g := skipTo started .precombatMain 80
  let g := addUntappedLand g mountain
  let g := addPermanent g goblinCratermaker ⟨0⟩ ⟨0⟩
  let g := addPermanent g grizzlyBears ⟨1⟩ ⟨1⟩
  g.modifyPlayer ⟨0⟩ (fun pl => { pl with landsPlayedThisTurn := 1 })

def cratermakerSource (g : Game) : GameObject :=
  namedPermanent g "Goblin Cratermaker"

def cratermakerAbility : ActivatedAbility :=
  goblinCratermaker.activatedAbilities[0]!

#guard cratermakerAbility.isModal
#guard cratermakerAbility.cost.sacrificeSource
#guard cratermakerAbility.effect == .dealDamageToTargetCreature 2
#guard cratermakerAbility.otherModes == #[.destroyTargetColorlessNonland]
#guard cratermakerReady.canActivate ⟨0⟩ (cratermakerSource cratermakerReady) cratermakerAbility
#guard !(cratermakerReady.canActivate ⟨1⟩ (cratermakerSource cratermakerReady)
  cratermakerAbility)
#guard (namedPermanent cratermakerReady "Grizzly Bears").isColorlessNonland == false
#guard (cratermakerSource cratermakerReady).printed.colors.contains .red

-- The heuristic begins activating Cratermaker when {1} is available.
#guard
  match Agent.choose cratermakerReady ⟨0⟩ with
  | some (.activate id 0) => id == (cratermakerSource cratermakerReady).id
  | _ => false

def proposedCratermaker : Game :=
  mustApply cratermakerReady ⟨0⟩ (.activate (cratermakerSource cratermakerReady).id 0)

#guard
  match proposedCratermaker.pending with
  | .chooseMode ⟨0⟩ => true
  | _ => false
#guard proposedCratermaker.proposedSpell.isSome
#guard proposedCratermaker.stack.size == 1
#guard (proposedCratermaker.object! proposedCratermaker.stack.back!.objectId).abilityEffect.isNone
#guard (namedPermanent proposedCratermaker "Goblin Cratermaker").isOnBattlefield
#guard proposedCratermaker.log.any (fun s => mentions s "begins activating Goblin Cratermaker")
#guard proposedCratermaker.log.any (fun s => mentions s "must choose a mode (CR 601.2b)")

-- Opponent cannot choose Chandra's mode.
#guard
  match proposedCratermaker.apply ⟨1⟩ (.chooseMode 0) with
  | .error msg => mentions msg "Only Chandra"
  | .ok _ => false

-- Mode index out of range.
#guard
  match proposedCratermaker.apply ⟨0⟩ (.chooseMode 2) with
  | .error msg => mentions msg "No such mode"
  | .ok _ => false

-- Targeting is not chosen at `activate`; it comes after the mode.
#guard
  match proposedCratermaker.apply ⟨0⟩
      (.target (Target.permanent (namedPermanent proposedCratermaker "Grizzly Bears").id)) with
  | .error msg => mentions msg "Not time to choose targets"
  | .ok _ => false

-- The heuristic picks the damage mode when the opponent has a creature.
#guard
  match Agent.choose proposedCratermaker ⟨0⟩ with
  | some (.chooseMode 0) => true
  | _ => false

def cratermakerModeChosen : Game :=
  mustApply proposedCratermaker ⟨0⟩ (.chooseMode 0)

#guard cratermakerModeChosen.pending == .chooseTargets ⟨0⟩
#guard (cratermakerModeChosen.object! cratermakerModeChosen.stack.back!.objectId).abilityEffect ==
  some (.dealDamageToTargetCreature 2)
#guard cratermakerModeChosen.log.any (fun s =>
  mentions s "chooses a mode: This creature deals 2 damage")
#guard cratermakerModeChosen.log.any (fun s => mentions s "must choose a target (CR 601.2c)")

-- A player is not a legal target for the damage mode.
#guard
  match cratermakerModeChosen.apply ⟨0⟩ (.target (Target.player ⟨1⟩)) with
  | .error msg => mentions msg "Illegal target"
  | .ok _ => false

-- The heuristic targets Nissa's creature.
#guard
  match Agent.choose cratermakerModeChosen ⟨0⟩ with
  | some (.target (Target.permanent id)) =>
    (cratermakerModeChosen.object! id).name == "Grizzly Bears"
  | _ => false

def cratermakerTargeted : Game :=
  mustApply cratermakerModeChosen ⟨0⟩
    (.target (Target.permanent (namedPermanent cratermakerModeChosen "Grizzly Bears").id))

#guard cratermakerTargeted.pending == .activateManaAbilities ⟨0⟩
#guard cratermakerTargeted.stack.back!.targets ==
  #[Target.permanent (namedPermanent cratermakerTargeted "Grizzly Bears").id]
#guard cratermakerTargeted.log.any (fun s =>
  mentions s "chooses Grizzly Bears as a target (CR 601.2c)")
#guard cratermakerTargeted.log.any (fun s => mentions s "may activate mana abilities (CR 601.2g)")

-- Paying without mana reverses the activation (CR 602.2 / 733.1).
def reversedCratermaker : Game :=
  mustApply cratermakerTargeted ⟨0⟩ .pay

#guard reversedCratermaker.pending == .none
#guard reversedCratermaker.stack.isEmpty
#guard (namedPermanent reversedCratermaker "Goblin Cratermaker").isOnBattlefield
#guard reversedCratermaker.log.any (fun s => mentions s "the activation is reversed")

def paidCratermaker : Game :=
  mustApply (tapNextMana cratermakerTargeted ⟨0⟩) ⟨0⟩ .pay

#guard paidCratermaker.pending == .none
#guard paidCratermaker.proposedSpell.isNone
#guard paidCratermaker.hasPriority ⟨0⟩
#guard paidCratermaker.stack.size == 1
#guard (paidCratermaker.player ⟨0⟩).graveyard.any (fun id =>
  (paidCratermaker.object! id).name == "Goblin Cratermaker")
#guard !(paidCratermaker.battlefield.any (fun o => o.name == "Goblin Cratermaker"))
#guard paidCratermaker.log.any (fun s => mentions s "sacrifices Goblin Cratermaker")
#guard paidCratermaker.log.any (fun s => mentions s "activates Goblin Cratermaker")

def resolvedCratermaker : Game := passBoth paidCratermaker

#guard resolvedCratermaker.stack.isEmpty
#guard resolvedCratermaker.log.any (fun s => mentions s "Grizzly Bears is dealt 2 damage")
#guard resolvedCratermaker.log.any (fun s => mentions s "Grizzly Bears dies from lethal damage")
#guard !(resolvedCratermaker.battlefield.any (fun o => o.name == "Grizzly Bears"))
#guard resolvedCratermaker.objects.any (fun o =>
  o.name == "Grizzly Bears" && o.zone == .graveyard ⟨1⟩)

/-- 2 damage is not lethal to a 3-toughness creature. -/
def cratermakerVsGiant : Game :=
  let g := skipTo started .precombatMain 80
  let g := addUntappedLand g mountain
  let g := addPermanent g goblinCratermaker ⟨0⟩ ⟨0⟩
  addPermanent g hillGiant ⟨1⟩ ⟨1⟩

def resolvedCratermakerVsGiant : Game :=
  let g := mustApply cratermakerVsGiant ⟨0⟩
    (.activate (cratermakerSource cratermakerVsGiant).id 0)
  let g := mustApply g ⟨0⟩ (.chooseMode 0)
  let g := mustApply g ⟨0⟩
    (.target (Target.permanent (namedPermanent g "Hill Giant").id))
  let g := mustApply (tapNextMana g ⟨0⟩) ⟨0⟩ .pay
  passBoth g

#guard (namedPermanent resolvedCratermakerVsGiant "Hill Giant").status.damage == 2
#guard resolvedCratermakerVsGiant.battlefield.any (fun o => o.name == "Hill Giant")
#guard resolvedCratermakerVsGiant.log.any (fun s => mentions s "Hill Giant is dealt 2 damage")
#guard !resolvedCratermakerVsGiant.log.any (fun s => mentions s "Hill Giant dies")

/-- Targeting the Cratermaker itself: it is sacrificed as a cost, so the ability
does nothing on resolution. -/
def cratermakerSelfTarget : Game :=
  let g := skipTo started .precombatMain 80
  let g := addUntappedLand g mountain
  addPermanent g goblinCratermaker ⟨0⟩ ⟨0⟩

def resolvedCratermakerSelf : Game :=
  let g := mustApply cratermakerSelfTarget ⟨0⟩
    (.activate (cratermakerSource cratermakerSelfTarget).id 0)
  let g := mustApply g ⟨0⟩ (.chooseMode 0)
  let g := mustApply g ⟨0⟩
    (.target (Target.permanent (cratermakerSource g).id))
  let g := mustApply (tapNextMana g ⟨0⟩) ⟨0⟩ .pay
  passBoth g

#guard resolvedCratermakerSelf.stack.isEmpty
#guard !(resolvedCratermakerSelf.battlefield.any (fun o => o.name == "Goblin Cratermaker"))
#guard resolvedCratermakerSelf.log.any (fun s => mentions s "The target is no longer in play")

/-- Destroy mode: Wayfarer's Bauble is a colorless nonland permanent. -/
def cratermakerDestroyReady : Game :=
  let g := skipTo started .precombatMain 80
  let g := addUntappedLand g mountain
  let g := addPermanent g goblinCratermaker ⟨0⟩ ⟨0⟩
  let g := addPermanent g wayfarersBauble ⟨1⟩ ⟨1⟩
  g.modifyPlayer ⟨0⟩ (fun pl => { pl with landsPlayedThisTurn := 1 })

#guard (namedPermanent cratermakerDestroyReady "Wayfarer's Bauble").isColorlessNonland
#guard !(namedPermanent cratermakerDestroyReady "Goblin Cratermaker").isColorlessNonland

-- No opposing creature: the heuristic prefers the destroy mode.
#guard
  let g := mustApply cratermakerDestroyReady ⟨0⟩
    (.activate (cratermakerSource cratermakerDestroyReady).id 0)
  match Agent.choose g ⟨0⟩ with
  | some (.chooseMode 1) => true
  | _ => false

-- A Mountain is a land, so it is not a legal destroy target.
#guard
  let g := mustApply cratermakerDestroyReady ⟨0⟩
    (.activate (cratermakerSource cratermakerDestroyReady).id 0)
  let g := mustApply g ⟨0⟩ (.chooseMode 1)
  match (g.permanentsOf ⟨0⟩).find? (·.printed.isLand) with
  | none => false
  | some land =>
    match g.apply ⟨0⟩ (.target (Target.permanent land.id)) with
    | .error msg => mentions msg "Illegal target"
    | .ok _ => false

-- A colored creature is not a legal destroy target.
#guard
  let g := addPermanent cratermakerDestroyReady grizzlyBears ⟨1⟩ ⟨1⟩
  let g := mustApply g ⟨0⟩ (.activate (cratermakerSource g).id 0)
  let g := mustApply g ⟨0⟩ (.chooseMode 1)
  match g.apply ⟨0⟩ (.target (Target.permanent (namedPermanent g "Grizzly Bears").id)) with
  | .error msg => mentions msg "Illegal target"
  | .ok _ => false

def resolvedCratermakerDestroy : Game :=
  let g := mustApply cratermakerDestroyReady ⟨0⟩
    (.activate (cratermakerSource cratermakerDestroyReady).id 0)
  let g := mustApply g ⟨0⟩ (.chooseMode 1)
  let g := mustApply g ⟨0⟩
    (.target (Target.permanent (namedPermanent g "Wayfarer's Bauble").id))
  let g := mustApply (tapNextMana g ⟨0⟩) ⟨0⟩ .pay
  passBoth g

#guard resolvedCratermakerDestroy.stack.isEmpty
#guard resolvedCratermakerDestroy.log.any (fun s => mentions s "Wayfarer's Bauble is destroyed")
#guard !(resolvedCratermakerDestroy.battlefield.any (fun o => o.name == "Wayfarer's Bauble"))
#guard resolvedCratermakerDestroy.objects.any (fun o =>
  o.name == "Wayfarer's Bauble" && o.zone == .graveyard ⟨1⟩)
#guard !(resolvedCratermakerDestroy.battlefield.any (fun o => o.name == "Goblin Cratermaker"))

-- Destroy mode cannot be chosen when there is no colorless nonland.
#guard
  match proposedCratermaker.apply ⟨0⟩ (.chooseMode 1) with
  | .error msg => mentions msg "requires a target"
  | .ok _ => false

-- Instant-speed: Cratermaker can activate during the end step.
def cratermakerAtEndStep : Game := skipTo cratermakerReady .end 80

#guard cratermakerAtEndStep.step == .end
#guard cratermakerAtEndStep.canActivate ⟨0⟩ (cratermakerSource cratermakerAtEndStep)
  cratermakerAbility

/-- Hill Giant (3/3) blocked by two Llanowar Elves (1/1): CR 510.1c lets the
attacker assign all 3 damage to one blocker. -/
def giantVsTwoElves : Game :=
  let g := addPermanent started hillGiant ⟨0⟩ ⟨0⟩
  let g := addPermanent g llanowarElves ⟨1⟩ ⟨1⟩
  addPermanent g llanowarElves ⟨1⟩ ⟨1⟩

def giantBlockedByTwoElves : Game :=
  let g := passBoth (skipTo giantVsTwoElves .beginningOfCombat 80)
  let giant := namedPermanent g "Hill Giant"
  let elves := g.battlefield.filter (fun o => o.name == "Llanowar Elves")
  let g := mustApply g ⟨0⟩ (.declareAttackers #[giant.id])
  let g := passBoth g
  mustApply g ⟨1⟩ (.declareBlockers #[(elves[0]!.id, giant.id), (elves[1]!.id, giant.id)])

def giantReadyToAssign : Game := passBoth giantBlockedByTwoElves

#guard giantReadyToAssign.step == .combatDamage
#guard giantReadyToAssign.pending == .assignCombatDamage ⟨0⟩ true
#guard giantReadyToAssign.actor == some ⟨0⟩
#guard giantReadyToAssign.needsCombatDamageChoice true
#guard !giantReadyToAssign.needsCombatDamageChoice false

def giantAllDamageOnFirst : Game :=
  let g := giantReadyToAssign
  let giant := namedPermanent g "Hill Giant"
  let elves := g.battlefield.filter (fun o => o.name == "Llanowar Elves")
  mustApply g ⟨0⟩ (.assignCombatDamage #[{
    source := giant.id
    toCreatures := #[(elves[0]!.id, 3), (elves[1]!.id, 0)]
  }])

#guard giantAllDamageOnFirst.log.any (fun s =>
  mentions s "Hill Giant deals 3 combat damage to Llanowar Elves")
#guard (giantAllDamageOnFirst.log.filter (fun s =>
  mentions s "Hill Giant deals" && mentions s "combat damage to Llanowar Elves")).size == 1
#guard (giantAllDamageOnFirst.player ⟨1⟩).life == 20
#guard (giantAllDamageOnFirst.battlefield.filter (fun o =>
  o.name == "Llanowar Elves")).size == 1
#guard giantAllDamageOnFirst.battlefield.any (fun o => o.name == "Hill Giant")
#guard (namedPermanent giantAllDamageOnFirst "Hill Giant").status.damage == 2

/-- The same total can be split 1 and 2; both Elves then take lethal damage. -/
def giantSplitDamage : Game :=
  let g := giantReadyToAssign
  let giant := namedPermanent g "Hill Giant"
  let elves := g.battlefield.filter (fun o => o.name == "Llanowar Elves")
  mustApply g ⟨0⟩ (.assignCombatDamage #[{
    source := giant.id
    toCreatures := #[(elves[0]!.id, 1), (elves[1]!.id, 2)]
  }])

#guard giantSplitDamage.log.any (fun s =>
  mentions s "Hill Giant deals 1 combat damage to Llanowar Elves")
#guard giantSplitDamage.log.any (fun s =>
  mentions s "Hill Giant deals 2 combat damage to Llanowar Elves")
#guard (giantSplitDamage.battlefield.filter (fun o =>
  o.name == "Llanowar Elves")).isEmpty
#guard giantSplitDamage.battlefield.any (fun o => o.name == "Hill Giant")

/-- Assigning less than power, or to a creature that is not blocking, is illegal. -/
def giantTooLittleDamage : Bool :=
  let g := giantReadyToAssign
  let giant := namedPermanent g "Hill Giant"
  let elves := g.battlefield.filter (fun o => o.name == "Llanowar Elves")
  match g.apply ⟨0⟩ (.assignCombatDamage #[{
    source := giant.id
    toCreatures := #[(elves[0]!.id, 2)]
  }]) with
  | .error msg => mentions msg "equal to its power"
  | .ok _ => false

#guard giantTooLittleDamage

def giantAssignsToItself : Bool :=
  let g := giantReadyToAssign
  let giant := namedPermanent g "Hill Giant"
  match g.apply ⟨0⟩ (.assignCombatDamage #[{
    source := giant.id
    toCreatures := #[(giant.id, 3)]
  }]) with
  | .error msg => mentions msg "creatures blocking it"
  | .ok _ => false

#guard giantAssignsToItself

/-- An empty assignment uses the default (all damage to the first blocker). -/
def giantDefaultAssign : Game :=
  mustApply giantReadyToAssign ⟨0⟩ (.assignCombatDamage #[])

#guard giantDefaultAssign.log.any (fun s =>
  mentions s "Hill Giant deals 3 combat damage to Llanowar Elves")
#guard (giantDefaultAssign.battlefield.filter (fun o =>
  o.name == "Llanowar Elves")).size == 1

/-- CR 510.1d: a blocker whose attacker has left combat assigns no damage. -/
def twoOgresOneBears : Game :=
  let g := addPermanent started grayOgre ⟨0⟩ ⟨0⟩
  let g := addPermanent g grayOgre ⟨0⟩ ⟨0⟩
  addPermanent g grizzlyBears ⟨1⟩ ⟨1⟩

def blockerWhoseAttackerLeft : Game :=
  let g := passBoth (skipTo twoOgresOneBears .beginningOfCombat 80)
  let ogres := g.battlefield.filter (fun o => o.name == "Gray Ogre")
  let bears := namedPermanent g "Grizzly Bears"
  let g := mustApply g ⟨0⟩ (.declareAttackers (ogres.map (·.id)))
  let g := passBoth g
  let g := mustApply g ⟨1⟩ (.declareBlockers #[(bears.id, ogres[0]!.id)])
  let (g, _) := g.move ogres[0]!.id (.graveyard ⟨0⟩) none
  passBoth g

#guard blockerWhoseAttackerLeft.log.any (fun s =>
  mentions s "not blocking any creatures and assigns no combat damage")
#guard blockerWhoseAttackerLeft.log.any (fun s =>
  mentions s "Gray Ogre deals 2 combat damage to Nissa")
#guard (namedPermanent blockerWhoseAttackerLeft "Grizzly Bears").status.damage == 0
#guard (blockerWhoseAttackerLeft.player ⟨1⟩).life == 18

/-- CR 510.1d: a creature blocking two attackers divides its damage as chosen. -/
def bearsBlockingTwoOgresReady : Game :=
  let g := passBoth (skipTo twoOgresOneBears .beginningOfCombat 80)
  let ogres := g.battlefield.filter (fun o => o.name == "Gray Ogre")
  let g := mustApply g ⟨0⟩ (.declareAttackers (ogres.map (·.id)))
  let g := passBoth g
  let g := mustApply g ⟨1⟩ (.declareBlockers #[])
  let bears := namedPermanent g "Grizzly Bears"
  let g := g.setObject { bears with
    status := { bears.status with blocking := ogres.map (·.id) } }
  let g := Id.run do
    let mut g := g
    for o in ogres do
      let a := g.object! o.id
      g := g.setObject { a with status := { a.status with blocked := true } }
    return g
  passBoth g

#guard bearsBlockingTwoOgresReady.step == .combatDamage
#guard bearsBlockingTwoOgresReady.pending == .assignCombatDamage ⟨1⟩ false
#guard bearsBlockingTwoOgresReady.actor == some ⟨1⟩
#guard bearsBlockingTwoOgresReady.needsCombatDamageChoice false
#guard bearsBlockingTwoOgresReady.needsCombatDamageChoice true == false

def bearsAssignAllToFirstOgre : Game :=
  let g := bearsBlockingTwoOgresReady
  let bears := namedPermanent g "Grizzly Bears"
  let ogres := g.battlefield.filter (fun o => o.name == "Gray Ogre")
  mustApply g ⟨1⟩ (.assignCombatDamage #[{
    source := bears.id
    toCreatures := #[(ogres[0]!.id, 2), (ogres[1]!.id, 0)]
  }])

#guard bearsAssignAllToFirstOgre.log.any (fun s =>
  mentions s "Grizzly Bears deals 2 combat damage to Gray Ogre")
#guard (bearsAssignAllToFirstOgre.log.filter (fun s =>
  mentions s "Grizzly Bears deals" && mentions s "combat damage to Gray Ogre")).size == 1
#guard (bearsAssignAllToFirstOgre.battlefield.filter (fun o =>
  o.name == "Gray Ogre")).size == 1
#guard !(bearsAssignAllToFirstOgre.battlefield.any (fun o => o.name == "Grizzly Bears"))

def bearsAssignsToItself : Bool :=
  let g := bearsBlockingTwoOgresReady
  let bears := namedPermanent g "Grizzly Bears"
  match g.apply ⟨1⟩ (.assignCombatDamage #[{
    source := bears.id
    toCreatures := #[(bears.id, 2)]
  }]) with
  | .error msg => mentions msg "creatures it's blocking"
  | .ok _ => false

#guard bearsAssignsToItself

/-- Propose a modal spell, choose a 0-based mode, then announce its target. -/
def proposeModal (g : Game) (p : PlayerId) (id : ObjectId) (mode : Nat) (t : Target) : Game :=
  mustApply (mustApply (mustApply g p (.cast id)) p (.chooseMode mode)) p (.target t)

def hexproofFlyer : CardDef := {
  name := "Hexproof Flyer"
  types := #[.creature]
  power := some 1
  toughness := some 1
  keywords := { Keywords.none with flying := true, hexproof := true }
}

/-- Warg Tactics in hand, Grizzly Bears you control, an opposing flyer, enough mana. -/
def wargSetup : Game :=
  let g := addPermanent afterDraw grizzlyBears ⟨0⟩ ⟨0⟩
  let g := addPermanent g velvetwingButterflies ⟨1⟩ ⟨1⟩
  withGreenMana (addToHand g wargTactics ⟨0⟩) ⟨0⟩ 2

#guard wargSetup.canCast ⟨0⟩ (handCardNamed wargSetup ⟨0⟩ "Warg Tactics")
#guard wargTactics.isModal
#guard wargTactics.requiresTarget
#guard (wargSetup.legalModes ⟨0⟩ (handCardNamed wargSetup ⟨0⟩ "Warg Tactics")).size == 2

-- Cannot cast with no legal mode (no flyer and no creature you control).
#guard
  let g := withGreenMana (addToHand afterDraw wargTactics ⟨0⟩) ⟨0⟩ 2
  !g.canCast ⟨0⟩ (handCardNamed g ⟨0⟩ "Warg Tactics")
#guard
  let g := addPermanent afterDraw grizzlyBears ⟨1⟩ ⟨1⟩
  let g := withGreenMana (addToHand g wargTactics ⟨0⟩) ⟨0⟩ 2
  !g.canCast ⟨0⟩ (handCardNamed g ⟨0⟩ "Warg Tactics")
#guard
  let g := withGreenMana (addToHand afterDraw wargTactics ⟨0⟩) ⟨0⟩ 2
  match g.apply ⟨0⟩ (.cast (handCardNamed g ⟨0⟩ "Warg Tactics").id) with
  | .error msg => mentions msg "requires a target"
  | .ok _ => false

-- Own creature alone enables only the +1/+1 mode; an opposing flyer alone enables destroy.
#guard
  let g := addPermanent afterDraw grizzlyBears ⟨0⟩ ⟨0⟩
  let g := withGreenMana (addToHand g wargTactics ⟨0⟩) ⟨0⟩ 2
  g.canCast ⟨0⟩ (handCardNamed g ⟨0⟩ "Warg Tactics") &&
    g.legalModes ⟨0⟩ (handCardNamed g ⟨0⟩ "Warg Tactics") == #[1]
#guard
  let g := addPermanent afterDraw velvetwingButterflies ⟨1⟩ ⟨1⟩
  let g := withGreenMana (addToHand g wargTactics ⟨0⟩) ⟨0⟩ 2
  g.canCast ⟨0⟩ (handCardNamed g ⟨0⟩ "Warg Tactics") &&
    g.legalModes ⟨0⟩ (handCardNamed g ⟨0⟩ "Warg Tactics") == #[0]

-- An opposing hexproof flyer cannot be chosen for destroy (CR 702.11b).
#guard
  let g := addPermanent afterDraw hexproofFlyer ⟨1⟩ ⟨1⟩
  let g := withGreenMana (addToHand g wargTactics ⟨0⟩) ⟨0⟩ 2
  !g.canCast ⟨0⟩ (handCardNamed g ⟨0⟩ "Warg Tactics")
#guard
  let g := addPermanent afterDraw hexproofFlyer ⟨1⟩ ⟨1⟩
  let g := addPermanent g grizzlyBears ⟨0⟩ ⟨0⟩
  let g := withGreenMana (addToHand g wargTactics ⟨0⟩) ⟨0⟩ 2
  g.legalModes ⟨0⟩ (handCardNamed g ⟨0⟩ "Warg Tactics") == #[1]

-- Casting a modal spell asks for a mode before a target (CR 601.2b).
def proposedWarg : Game :=
  mustApply wargSetup ⟨0⟩ (.cast (handCardNamed wargSetup ⟨0⟩ "Warg Tactics").id)

#guard
  match proposedWarg.pending with
  | .chooseMode ⟨0⟩ => true
  | _ => false
#guard proposedWarg.proposedSpell.isSome
#guard !proposedWarg.stack.isEmpty
#guard proposedWarg.stack.back!.chosenMode.isNone
#guard proposedWarg.stack.back!.targets.isEmpty
#guard proposedWarg.actor == some ⟨0⟩
#guard proposedWarg.log.any (fun s => mentions s "begins casting Warg Tactics")
#guard proposedWarg.log.any (fun s => mentions s "must choose a mode (CR 601.2b")

#guard
  match proposedWarg.apply ⟨0⟩ .pay with
  | .error msg => mentions msg "Choose a mode first"
  | .ok _ => false
#guard
  match proposedWarg.apply ⟨0⟩ (.target (Target.permanent
    (namedPermanent proposedWarg "Velvetwing Butterflies").id)) with
  | .error msg => mentions msg "Not time to choose targets"
  | .ok _ => false
#guard
  match proposedWarg.apply ⟨0⟩ (.chooseMode 2) with
  | .error msg => mentions msg "No such mode"
  | .ok _ => false
#guard
  match proposedWarg.apply ⟨1⟩ (.chooseMode 0) with
  | .error msg => mentions msg "may choose a mode"
  | .ok _ => false

-- The agent prefers destroying an opponent's flyer when that mode is legal.
#guard
  match Agent.choose proposedWarg ⟨0⟩ with
  | some (.chooseMode 0) => true
  | _ => false
#guard
  let g := addPermanent afterDraw grizzlyBears ⟨0⟩ ⟨0⟩
  let g := withGreenMana (addToHand g wargTactics ⟨0⟩) ⟨0⟩ 2
  let g := mustApply g ⟨0⟩ (.cast (handCardNamed g ⟨0⟩ "Warg Tactics").id)
  match Agent.choose g ⟨0⟩ with
  | some (.chooseMode 1) => true
  | _ => false

def wargModeDestroy : Game :=
  mustApply proposedWarg ⟨0⟩ (.chooseMode 0)

#guard wargModeDestroy.pending == .chooseTargets ⟨0⟩
#guard wargModeDestroy.stack.back!.chosenMode == some 0
#guard wargModeDestroy.log.any (fun s => mentions s "chooses mode 1")
#guard wargModeDestroy.log.any (fun s => mentions s "destroy target creature with flying")
#guard wargModeDestroy.log.any (fun s => mentions s "must choose a target (CR 601.2c)")

-- Mode 1 cannot target a creature without flying or a player.
#guard
  match wargModeDestroy.apply ⟨0⟩ (.target (Target.permanent
    (namedPermanent wargModeDestroy "Grizzly Bears").id)) with
  | .error msg => mentions msg "Illegal target"
  | .ok _ => false
#guard
  match wargModeDestroy.apply ⟨0⟩ (.target (Target.player ⟨1⟩)) with
  | .error msg => mentions msg "Illegal target"
  | .ok _ => false

#guard
  match Agent.choose wargModeDestroy ⟨0⟩ with
  | some (.target (Target.permanent tid)) =>
    (wargModeDestroy.object! tid).name == "Velvetwing Butterflies"
  | _ => false

def targetedWargDestroy : Game :=
  mustApply wargModeDestroy ⟨0⟩
    (.target (Target.permanent (namedPermanent wargModeDestroy "Velvetwing Butterflies").id))

#guard targetedWargDestroy.pending == .activateManaAbilities ⟨0⟩
#guard targetedWargDestroy.stack.back!.targets ==
  #[Target.permanent (namedPermanent targetedWargDestroy "Velvetwing Butterflies").id]

def paidWargDestroy : Game :=
  mustApply targetedWargDestroy ⟨0⟩ .pay

#guard paidWargDestroy.hasPriority ⟨0⟩
#guard paidWargDestroy.stack.size == 1
#guard paidWargDestroy.log.any (fun s => mentions s "casts Warg Tactics")

def resolvedWargDestroy : Game := passBoth paidWargDestroy

#guard resolvedWargDestroy.stack.isEmpty
#guard !(resolvedWargDestroy.battlefield.any (fun o => o.name == "Velvetwing Butterflies"))
#guard resolvedWargDestroy.objects.any (fun o =>
  o.name == "Velvetwing Butterflies" && o.zone == .graveyard ⟨1⟩)
#guard resolvedWargDestroy.log.any (fun s => mentions s "Velvetwing Butterflies is destroyed")
#guard (resolvedWargDestroy.player ⟨0⟩).graveyard.any (fun id =>
  (resolvedWargDestroy.object! id).name == "Warg Tactics")

-- If the flyer leaves before resolution, the spell does nothing (CR 608.2b).
def wargDestroyTargetGone : Game :=
  let id := (namedPermanent paidWargDestroy "Velvetwing Butterflies").id
  let (g, _) := paidWargDestroy.move id (.graveyard ⟨1⟩) none
  passBoth g

#guard wargDestroyTargetGone.log.any (fun s => mentions s "no longer in play")
#guard !(wargDestroyTargetGone.battlefield.any (fun o => o.name == "Velvetwing Butterflies"))

def wargModePump : Game :=
  mustApply proposedWarg ⟨0⟩ (.chooseMode 1)

#guard wargModePump.pending == .chooseTargets ⟨0⟩
#guard wargModePump.stack.back!.chosenMode == some 1
#guard wargModePump.log.any (fun s => mentions s "chooses mode 2")

-- Mode 2 cannot target an opponent's creature.
#guard
  match wargModePump.apply ⟨0⟩ (.target (Target.permanent
    (namedPermanent wargModePump "Velvetwing Butterflies").id)) with
  | .error msg => mentions msg "Illegal target"
  | .ok _ => false

def paidWargPump : Game :=
  let g := mustApply wargModePump ⟨0⟩
    (.target (Target.permanent (namedPermanent wargModePump "Grizzly Bears").id))
  mustApply g ⟨0⟩ .pay

def resolvedWargPump : Game := passBoth paidWargPump

#guard resolvedWargPump.stack.isEmpty
#guard (namedPermanent resolvedWargPump "Grizzly Bears").status.plusOnePlusOne == 1
#guard resolvedWargPump.power (namedPermanent resolvedWargPump "Grizzly Bears") == 3
#guard resolvedWargPump.toughness (namedPermanent resolvedWargPump "Grizzly Bears") == 3
#guard resolvedWargPump.hasTrample (namedPermanent resolvedWargPump "Grizzly Bears")
#guard resolvedWargPump.hasHexproof (namedPermanent resolvedWargPump "Grizzly Bears")
#guard (resolvedWargPump.effectiveKeywords
  (namedPermanent resolvedWargPump "Grizzly Bears")).hexproof
#guard resolvedWargPump.log.any (fun s =>
  mentions s "gets a +1/+1 counter and gains trample and hexproof")

/-- A 0/0 survives after receiving a +1/+1 counter. -/
def zeroWithCounter : Game :=
  let g := addPermanent started zeroZero ⟨0⟩ ⟨0⟩
  let id := (namedPermanent g "Zero/Zero").id
  g.applyEffect ⟨0⟩ .plusOnePlusOneTrampleHexproof #[Target.permanent id]

#guard zeroWithCounter.power (namedPermanent zeroWithCounter "Zero/Zero") == 1
#guard zeroWithCounter.toughness (namedPermanent zeroWithCounter "Zero/Zero") == 1
#guard (zeroWithCounter.checkSBA).battlefield.any (fun o => o.name == "Zero/Zero")

/-- Hexproof wears off in cleanup; the counter does not. -/
def afterWargPumpCleanup : Game := passBoth (skipTo resolvedWargPump .end 80)

#guard (namedPermanent afterWargPumpCleanup "Grizzly Bears").status.plusOnePlusOne == 1
#guard afterWargPumpCleanup.power (namedPermanent afterWargPumpCleanup "Grizzly Bears") == 3
#guard !afterWargPumpCleanup.hasHexproof (namedPermanent afterWargPumpCleanup "Grizzly Bears")
#guard !afterWargPumpCleanup.hasTrample (namedPermanent afterWargPumpCleanup "Grizzly Bears")
#guard afterWargPumpCleanup.turnNumber == 2

/-- Granted trample assigns leftover combat damage. -/
def afterWargTrampleCombat : Game :=
  let g := addPermanent started grizzlyBears ⟨0⟩ ⟨0⟩
  let g := addPermanent g llanowarElves ⟨1⟩ ⟨1⟩
  let g := g.applyEffect ⟨0⟩ .plusOnePlusOneTrampleHexproof
    #[Target.permanent (namedPermanent g "Grizzly Bears").id]
  let g := passBoth (skipTo g .beginningOfCombat 80)
  let g := mustApply g ⟨0⟩ (.declareAttackers #[(namedPermanent g "Grizzly Bears").id])
  let g := passBoth g
  let g := mustApply g ⟨1⟩ (.declareBlockers #[(
    (namedPermanent g "Llanowar Elves").id,
    (namedPermanent g "Grizzly Bears").id)])
  passBoth g

#guard afterWargTrampleCombat.log.any (fun s =>
  mentions s "Grizzly Bears deals 1 combat damage to Llanowar Elves")
#guard afterWargTrampleCombat.log.any (fun s =>
  mentions s "Grizzly Bears tramples for 2 to Nissa")
#guard (afterWargTrampleCombat.player ⟨1⟩).life == 18

/-- Nissa has Lightning Bolt while Chandra's pumped Grizzly Bears has hexproof. -/
def nissaBoltVsHexproof : Game :=
  let g := addPermanent resolvedWargPump mountain ⟨1⟩ ⟨1⟩
  let g := addToHand g lightningBolt ⟨1⟩
  mustApply g ⟨0⟩ .pass

#guard nissaBoltVsHexproof.hasPriority ⟨1⟩
#guard nissaBoltVsHexproof.canCast ⟨1⟩ (handCardNamed nissaBoltVsHexproof ⟨1⟩ "Lightning Bolt")

def proposedNissaBolt : Game :=
  mustApply nissaBoltVsHexproof ⟨1⟩
    (.cast (handCardNamed nissaBoltVsHexproof ⟨1⟩ "Lightning Bolt").id)

#guard
  match proposedNissaBolt.apply ⟨1⟩ (.target (Target.permanent
    (namedPermanent proposedNissaBolt "Grizzly Bears").id)) with
  | .error msg => mentions msg "Illegal target"
  | .ok _ => false

def paidNissaBoltPlayer : Game :=
  let g := mustApply proposedNissaBolt ⟨1⟩ (.target (Target.player ⟨0⟩))
  let g := tapNextMana g ⟨1⟩
  mustApply g ⟨1⟩ .pay

def resolvedNissaBoltPlayer : Game := passBoth paidNissaBoltPlayer

#guard (resolvedNissaBoltPlayer.player ⟨0⟩).life == 17
#guard resolvedNissaBoltPlayer.battlefield.any (fun o => o.name == "Grizzly Bears")

-- After hexproof wears off, the same creature is a legal Lightning Bolt target.
#guard
  (afterWargPumpCleanup.legalTargets ⟨1⟩ (.dealDamage 3)).contains
    (Target.permanent (namedPermanent afterWargPumpCleanup "Grizzly Bears").id)

/-- The agent casts Warg Tactics to destroy a flyer when that is the playable spell. -/
def agentWargDestroyOnly : Game :=
  let g := addPermanent afterDraw velvetwingButterflies ⟨1⟩ ⟨1⟩
  let g := g.modifyPlayer ⟨0⟩ (fun pl => { pl with hand := #[], landsPlayedThisTurn := 1 })
  withGreenMana (addToHand g wargTactics ⟨0⟩) ⟨0⟩ 2

#guard
  match Agent.choose agentWargDestroyOnly ⟨0⟩ with
  | some (.cast id) => (agentWargDestroyOnly.object! id).name == "Warg Tactics"
  | _ => false

/-- The agent casts Warg Tactics as a pump when no flyer is available. -/
def agentWargPumpOnly : Game :=
  let g := addPermanent afterDraw grizzlyBears ⟨0⟩ ⟨0⟩
  let g := g.modifyPlayer ⟨0⟩ (fun pl => { pl with hand := #[], landsPlayedThisTurn := 1 })
  withGreenMana (addToHand g wargTactics ⟨0⟩) ⟨0⟩ 2

#guard
  match Agent.choose agentWargPumpOnly ⟨0⟩ with
  | some (.cast id) => (agentWargPumpOnly.object! id).name == "Warg Tactics"
  | _ => false

/-- Ragged Short Spear in hand, Grizzly Bears on the battlefield, enough mana. -/
def spearSetup : Game :=
  let g := addPermanent afterDraw grizzlyBears ⟨0⟩ ⟨0⟩
  withRedMana (addToHand g raggedShortSpear ⟨0⟩) ⟨0⟩ 2

#guard spearSetup.canCast ⟨0⟩ (handCardNamed spearSetup ⟨0⟩ "Ragged Short Spear")
#guard spearSetup.asSorcery? ⟨0⟩
#guard !raggedShortSpear.requiresTarget
#guard raggedShortSpear.isEquipment

/-- Equipment is cast without announcing a creature (CR 301.5b). -/
def proposedSpear : Game :=
  mustApply spearSetup ⟨0⟩ (.cast (handCardNamed spearSetup ⟨0⟩ "Ragged Short Spear").id)

#guard proposedSpear.pending == .activateManaAbilities ⟨0⟩
#guard proposedSpear.stack.back!.targets.isEmpty
#guard proposedSpear.log.any (fun s => mentions s "begins casting Ragged Short Spear")

def paidSpear : Game := mustApply proposedSpear ⟨0⟩ .pay

#guard paidSpear.stack.size == 1
#guard paidSpear.hasPriority ⟨0⟩

/-- The Equipment enters unattached; the discard trigger waits on the stack. -/
def spearEntered : Game := passBoth paidSpear

#guard (namedPermanent spearEntered "Ragged Short Spear").attachedTo.isNone
#guard spearEntered.power (namedPermanent spearEntered "Grizzly Bears") == 2
#guard spearEntered.stack.size == 1
#guard spearEntered.log.any (fun s => mentions s "enters the battlefield")
#guard spearEntered.log.any (fun s => mentions s "enters trigger is put on the stack")

def spearMayDiscard : Game := passBoth spearEntered

#guard
  match spearMayDiscard.pending with
  | .mayDiscardDraw ⟨0⟩ 2 => true
  | _ => false
#guard spearMayDiscard.actor == some ⟨0⟩
#guard !spearMayDiscard.hasPriority ⟨0⟩
#guard spearMayDiscard.log.any (fun s => mentions s "may discard a card")
#guard spearMayDiscard.stack.isEmpty

/-- Declining the optional discard draws nothing. -/
def spearDeclined : Game := mustApply spearMayDiscard ⟨0⟩ .decline

#guard spearDeclined.pending == .none
#guard spearDeclined.hasPriority ⟨0⟩
#guard spearDeclined.log.any (fun s => mentions s "declines to discard")
#guard (spearDeclined.player ⟨0⟩).hand.size == (spearMayDiscard.player ⟨0⟩).hand.size
#guard (spearDeclined.player ⟨0⟩).library.size == (spearMayDiscard.player ⟨0⟩).library.size

-- The opponent cannot discard or decline for Chandra.
#guard
  match spearMayDiscard.apply ⟨1⟩ .decline with
  | .error msg => mentions msg "Only Chandra"
  | .ok _ => false
#guard
  match spearMayDiscard.apply ⟨1⟩
      (.discard (spearMayDiscard.player ⟨0⟩).hand.back!) with
  | .error msg => mentions msg "Only Chandra"
  | .ok _ => false

-- Discarding a card that is not in hand is illegal.
#guard
  match spearMayDiscard.apply ⟨0⟩
      (.discard (namedPermanent spearMayDiscard "Grizzly Bears").id) with
  | .error msg => mentions msg "not in your hand"
  | .ok _ => false

/-- Discard a known extra card, then draw the two known library tops. -/
def spearKnownLib : Game :=
  let g := addToHand spearEntered forest ⟨0⟩
  addToLibraryTop (addToLibraryTop g forest ⟨0⟩) llanowarElves ⟨0⟩

def spearKnownMayDiscard : Game := passBoth spearKnownLib

def spearDiscardedForest : Game :=
  mustApply spearKnownMayDiscard ⟨0⟩
    (.discard (handCardNamed spearKnownMayDiscard ⟨0⟩ "Forest").id)

#guard spearDiscardedForest.pending == .none
#guard spearDiscardedForest.hasPriority ⟨0⟩
#guard spearDiscardedForest.log.any (fun s => mentions s "discards Forest")
#guard spearDiscardedForest.log.any (fun s => mentions s "draws Llanowar Elves")
#guard spearDiscardedForest.log.any (fun s => mentions s "draws Forest")
#guard (spearDiscardedForest.handObjects ⟨0⟩).any (fun o => o.name == "Llanowar Elves")
#guard (spearDiscardedForest.handObjects ⟨0⟩).any (fun o => o.name == "Forest")
#guard (spearDiscardedForest.player ⟨0⟩).graveyard.any (fun id =>
  (spearDiscardedForest.object! id).name == "Forest")
#guard (spearDiscardedForest.player ⟨0⟩).hand.size ==
  (spearKnownMayDiscard.player ⟨0⟩).hand.size + 1

-- The heuristic discards the last card in hand.
#guard
  match Agent.choose spearKnownMayDiscard ⟨0⟩ with
  | some (.discard id) => id == (spearKnownMayDiscard.player ⟨0⟩).hand.back!
  | _ => false

/-- An empty hand skips the optional discard; no draw. -/
def spearEmptyHand : Game :=
  let g := { spearEntered with pending := .none, stack := #[] }
  let g := g.modifyPlayer ⟨0⟩ (fun pl => { pl with hand := #[] })
  g.beginMayDiscardDraw ⟨0⟩ 2

#guard spearEmptyHand.pending == .none
#guard spearEmptyHand.log.any (fun s => mentions s "has no card to discard")

/-- Equip {3} with a creature you control and enough mana. -/
def spearReadyToEquip : Game :=
  let g := addPermanent afterDraw grizzlyBears ⟨0⟩ ⟨0⟩
  let g := addPermanent g raggedShortSpear ⟨0⟩ ⟨0⟩
  let g := g.modifyPlayer ⟨0⟩ (fun pl => { pl with landsPlayedThisTurn := 1 })
  withRedMana g ⟨0⟩ 3

def spearEquipAbility : ActivatedAbility :=
  raggedShortSpear.activatedAbilities[0]!

#guard spearReadyToEquip.canActivate ⟨0⟩
  (namedPermanent spearReadyToEquip "Ragged Short Spear") spearEquipAbility
#guard !(spearReadyToEquip.canActivate ⟨1⟩
  (namedPermanent spearReadyToEquip "Ragged Short Spear") spearEquipAbility)
#guard spearEquipAbility.onlyAsSorcery
#guard spearEquipAbility.effect.requiresTarget

-- Cannot Equip with no creature you control.
#guard
  let g := addPermanent afterDraw raggedShortSpear ⟨0⟩ ⟨0⟩
  let g := withRedMana g ⟨0⟩ 3
  !g.canActivate ⟨0⟩ (namedPermanent g "Ragged Short Spear") spearEquipAbility

-- Cannot Equip an opponent's creature: Equip needs a creature you control.
#guard
  let g := addPermanent afterDraw grizzlyBears ⟨1⟩ ⟨1⟩
  let g := addPermanent g raggedShortSpear ⟨0⟩ ⟨0⟩
  let g := withRedMana g ⟨0⟩ 3
  !g.canActivate ⟨0⟩ (namedPermanent g "Ragged Short Spear") spearEquipAbility
#guard
  let g := addPermanent afterDraw grizzlyBears ⟨0⟩ ⟨0⟩
  let g := addPermanent g grayOgre ⟨1⟩ ⟨1⟩
  let g := addPermanent g raggedShortSpear ⟨0⟩ ⟨0⟩
  let g := withRedMana g ⟨0⟩ 3
  let g := mustApply g ⟨0⟩ (.activate (namedPermanent g "Ragged Short Spear").id 0)
  match g.apply ⟨0⟩ (.target (Target.permanent (namedPermanent g "Gray Ogre").id)) with
  | .error msg => mentions msg "Illegal target"
  | .ok _ => false

-- Equip is sorcery-speed only (CR 702.6a).
#guard
  let g := applyIdle (passBoth (skipTo afterDraw .end 80))
  let g := addPermanent g grizzlyBears ⟨0⟩ ⟨0⟩
  let g := addPermanent g raggedShortSpear ⟨0⟩ ⟨0⟩
  let g := withRedMana g ⟨0⟩ 3
  !g.asSorcery? ⟨0⟩ &&
    !g.canActivate ⟨0⟩ (namedPermanent g "Ragged Short Spear") spearEquipAbility

-- The heuristic Equips when {3} is available and a creature is controlled.
#guard
  match Agent.choose spearReadyToEquip ⟨0⟩ with
  | some (.activate id 0) =>
    (spearReadyToEquip.object! id).name == "Ragged Short Spear"
  | _ => false

def proposedEquip : Game :=
  mustApply spearReadyToEquip ⟨0⟩
    (.activate (namedPermanent spearReadyToEquip "Ragged Short Spear").id 0)

#guard
  match proposedEquip.pending with
  | .chooseTargets ⟨0⟩ => true
  | _ => false
#guard proposedEquip.log.any (fun s => mentions s "begins activating Ragged Short Spear")
#guard proposedEquip.log.any (fun s => mentions s "must choose a target (CR 601.2c)")

-- The heuristic targets Chandra's creature.
#guard
  match Agent.choose proposedEquip ⟨0⟩ with
  | some (.target (Target.permanent tid)) =>
    (proposedEquip.object! tid).name == "Grizzly Bears"
  | _ => false

def targetedEquip : Game :=
  mustApply proposedEquip ⟨0⟩
    (.target (Target.permanent (namedPermanent proposedEquip "Grizzly Bears").id))

#guard targetedEquip.pending == .activateManaAbilities ⟨0⟩
#guard targetedEquip.stack.back!.targets ==
  #[Target.permanent (namedPermanent targetedEquip "Grizzly Bears").id]

def paidEquip : Game := mustApply targetedEquip ⟨0⟩ .pay

#guard paidEquip.pending == .none
#guard paidEquip.hasPriority ⟨0⟩
#guard (namedPermanent paidEquip "Ragged Short Spear").attachedTo.isNone
#guard paidEquip.log.any (fun s => mentions s "activates Ragged Short Spear")

def spearEquipped : Game := passBoth paidEquip

#guard (namedPermanent spearEquipped "Ragged Short Spear").attachedTo ==
  some (namedPermanent spearEquipped "Grizzly Bears").id
#guard spearEquipped.power (namedPermanent spearEquipped "Grizzly Bears") == 4
#guard spearEquipped.toughness (namedPermanent spearEquipped "Grizzly Bears") == 2
#guard (namedPermanent spearEquipped "Grizzly Bears").power == 2
#guard spearEquipped.log.any (fun s => mentions s "attaches to Grizzly Bears")

-- The heuristic does not re-equip a creature that is already equipped.
#guard
  let g := withRedMana spearEquipped ⟨0⟩ 3
  match Agent.choose g ⟨0⟩ with
  | some (.activate id 0) => (g.object! id).name != "Ragged Short Spear"
  | some .pass => true
  | some (.cast _) => true
  | _ => true

/-- The +2/+0 is a continuous effect, so it does not wear off in cleanup. -/
def afterSpearCleanup : Game := passBoth (skipTo spearEquipped .end 80)

#guard afterSpearCleanup.power (namedPermanent afterSpearCleanup "Grizzly Bears") == 4
#guard (namedPermanent afterSpearCleanup "Grizzly Bears").status.pumpPower == 0

/-- If the target leaves before Equip resolves, the ability does nothing. -/
def equipTargetGone : Game :=
  let id := (namedPermanent paidEquip "Grizzly Bears").id
  let (g, _) := paidEquip.move id (.graveyard ⟨0⟩) none
  passBoth g

#guard (namedPermanent equipTargetGone "Ragged Short Spear").attachedTo.isNone
#guard equipTargetGone.log.any (fun s => mentions s "no longer in play")

/-- If the equipped creature leaves, the Equipment becomes unattached and stays
on the battlefield (CR 301.5c / 704.5n). -/
def afterEquippedHostLeaves : Game :=
  let id := (namedPermanent spearEquipped "Grizzly Bears").id
  let (g, _) := spearEquipped.move id (.graveyard ⟨0⟩) none
  g.checkSBA

#guard afterEquippedHostLeaves.log.any (fun s => mentions s "becomes unattached")
#guard afterEquippedHostLeaves.battlefield.any (fun o => o.name == "Ragged Short Spear")
#guard (namedPermanent afterEquippedHostLeaves "Ragged Short Spear").attachedTo.isNone
#guard !(afterEquippedHostLeaves.battlefield.any (fun o => o.name == "Grizzly Bears"))
#guard !(afterEquippedHostLeaves.log.any (fun s =>
  mentions s "Ragged Short Spear is put into its owner's graveyard"))

/-- Combat uses the equipped power. -/
def afterEquippedCombat : Game :=
  let g := addPermanent started grizzlyBears ⟨0⟩ ⟨0⟩
  let g := addAttachedAura g raggedShortSpear (namedPermanent g "Grizzly Bears") ⟨0⟩ ⟨0⟩
  let g := passBoth (skipTo g .beginningOfCombat 80)
  let g := mustApply g ⟨0⟩ (.declareAttackers #[(namedPermanent g "Grizzly Bears").id])
  let g := passBoth g
  let g := mustApply g ⟨1⟩ (.declareBlockers #[])
  passBoth g

#guard afterEquippedCombat.log.any (fun s =>
  mentions s "Grizzly Bears deals 4 combat damage to Nissa")
#guard (afterEquippedCombat.player ⟨1⟩).life == 16

/-- Move Equip from one creature to another. -/
def spearTwoCreatures : Game :=
  let g := addPermanent afterDraw grizzlyBears ⟨0⟩ ⟨0⟩
  let g := addPermanent g grayOgre ⟨0⟩ ⟨0⟩
  let g := addPermanent g raggedShortSpear ⟨0⟩ ⟨0⟩
  withRedMana g ⟨0⟩ 3

def spearMovedToOgre : Game :=
  let g := mustApply spearTwoCreatures ⟨0⟩
    (.activate (namedPermanent spearTwoCreatures "Ragged Short Spear").id 0)
  let g := mustApply g ⟨0⟩
    (.target (Target.permanent (namedPermanent g "Grizzly Bears").id))
  let g := mustApply g ⟨0⟩ .pay
  let g := passBoth g
  let g := withRedMana g ⟨0⟩ 3
  let g := mustApply g ⟨0⟩
    (.activate (namedPermanent g "Ragged Short Spear").id 0)
  let g := mustApply g ⟨0⟩
    (.target (Target.permanent (namedPermanent g "Gray Ogre").id))
  let g := mustApply g ⟨0⟩ .pay
  passBoth g

#guard spearMovedToOgre.power (namedPermanent spearMovedToOgre "Grizzly Bears") == 2
#guard spearMovedToOgre.power (namedPermanent spearMovedToOgre "Gray Ogre") == 4
#guard (namedPermanent spearMovedToOgre "Ragged Short Spear").attachedTo ==
  some (namedPermanent spearMovedToOgre "Gray Ogre").id

/-- Illegally attached Equipment becomes unattached and stays (CR 704.5n). -/
def spearOnMountain : Game :=
  let g := addPermanent started mountain ⟨0⟩ ⟨0⟩
  addAttachedAura g raggedShortSpear (namedPermanent g "Mountain") ⟨0⟩ ⟨0⟩

def spearUnattachedFromLand : Game := spearOnMountain.checkSBA

#guard spearUnattachedFromLand.log.any (fun s => mentions s "704.5n")
#guard (namedPermanent spearUnattachedFromLand "Ragged Short Spear").attachedTo.isNone
#guard spearUnattachedFromLand.battlefield.any (fun o => o.name == "Ragged Short Spear")

/-- The agent casts Ragged Short Spear when that is the playable spell. -/
def agentSpearOnly : Game :=
  let g := addPermanent afterDraw grizzlyBears ⟨0⟩ ⟨0⟩
  let g := g.modifyPlayer ⟨0⟩ (fun pl => { pl with hand := #[], landsPlayedThisTurn := 1 })
  withRedMana (addToHand g raggedShortSpear ⟨0⟩) ⟨0⟩ 2

#guard
  match Agent.choose agentSpearOnly ⟨0⟩ with
  | some (.cast id) => (agentSpearOnly.object! id).name == "Ragged Short Spear"
  | _ => false

/- Beorn's Hospitality: landfall +1/+1 and lasting Bear animation. -/

def addForests (g : Game) (p : PlayerId) : Nat → Game
  | 0 => g
  | n + 1 => addPermanent (addForests g p n) forest p p

/-- Hospitality and Grizzly Bears in play; a Forest in hand. -/
def hospitalityLandfallSetup : Game :=
  let g := addPermanent afterDraw beornsHospitality ⟨0⟩ ⟨0⟩
  let g := addPermanent g grizzlyBears ⟨0⟩ ⟨0⟩
  addToHand g forest ⟨0⟩

#guard hospitalityLandfallSetup.canPlayLand ⟨0⟩
#guard beornsHospitality.triggeredAbilities == #[.onLandYouControlEntersPlusOnePlusOne]
#guard beornsHospitality.activatedAbilities[0]!.effect == .becomeBearCreatureWithLandsPT

def hospitalityLandPlayed : Game :=
  mustApply hospitalityLandfallSetup ⟨0⟩
    (.playLand (handCardNamed hospitalityLandfallSetup ⟨0⟩ "Forest").id)

#guard hospitalityLandPlayed.pending == .chooseTargets ⟨0⟩
#guard hospitalityLandPlayed.stack.size == 1
#guard (hospitalityLandPlayed.object! hospitalityLandPlayed.stack.back!.objectId).triggeredAbility ==
  some .onLandYouControlEntersPlusOnePlusOne
#guard hospitalityLandPlayed.stack.back!.targets.isEmpty
#guard hospitalityLandPlayed.log.any (fun s => mentions s "landfall trigger is put on the stack")
#guard hospitalityLandPlayed.log.any (fun s => mentions s "must choose a target (CR 603.3d")
#guard !hospitalityLandPlayed.hasPriority ⟨0⟩
#guard hospitalityLandPlayed.actor == some ⟨0⟩

-- The landfall trigger cannot target an opponent's creature or a player.
#guard
  let g := addPermanent hospitalityLandPlayed velvetwingButterflies ⟨1⟩ ⟨1⟩
  match g.apply ⟨0⟩ (.target (Target.permanent (namedPermanent g "Velvetwing Butterflies").id)) with
  | .error msg => mentions msg "Illegal target"
  | .ok _ => false
#guard
  match hospitalityLandPlayed.apply ⟨0⟩ (.target (Target.player ⟨1⟩)) with
  | .error msg => mentions msg "Illegal target"
  | .ok _ => false

-- The heuristic targets a creature you control.
#guard
  match Agent.choose hospitalityLandPlayed ⟨0⟩ with
  | some (.target (Target.permanent tid)) =>
    (hospitalityLandPlayed.object! tid).name == "Grizzly Bears"
  | _ => false

def hospitalityLandfallTargeted : Game :=
  mustApply hospitalityLandPlayed ⟨0⟩
    (.target (Target.permanent (namedPermanent hospitalityLandPlayed "Grizzly Bears").id))

#guard hospitalityLandfallTargeted.pending == .none
#guard hospitalityLandfallTargeted.hasPriority ⟨0⟩
#guard hospitalityLandfallTargeted.stack.back!.targets ==
  #[Target.permanent (namedPermanent hospitalityLandfallTargeted "Grizzly Bears").id]
#guard hospitalityLandfallTargeted.log.any (fun s =>
  mentions s "chooses Grizzly Bears as a target")

def hospitalityLandfallResolved : Game := passBoth hospitalityLandfallTargeted

#guard hospitalityLandfallResolved.stack.isEmpty
#guard (namedPermanent hospitalityLandfallResolved "Grizzly Bears").status.plusOnePlusOne == 1
#guard hospitalityLandfallResolved.power
  (namedPermanent hospitalityLandfallResolved "Grizzly Bears") == 3
#guard hospitalityLandfallResolved.log.any (fun s => mentions s "gets a +1/+1 counter")

/-- No creature you control: the landfall trigger is removed (CR 603.3d). -/
def hospitalityNoTarget : Game :=
  let g := addPermanent afterDraw beornsHospitality ⟨0⟩ ⟨0⟩
  let g := addPermanent g velvetwingButterflies ⟨1⟩ ⟨1⟩
  let g := addToHand g forest ⟨0⟩
  mustApply g ⟨0⟩ (.playLand (handCardNamed g ⟨0⟩ "Forest").id)

#guard hospitalityNoTarget.stack.isEmpty
#guard hospitalityNoTarget.hasPriority ⟨0⟩
#guard hospitalityNoTarget.log.any (fun s => mentions s "no legal target")

/-- An opponent's land does not trigger your landfall. -/
def nissaLandVsHospitality : Game :=
  let g := addPermanent afterDraw beornsHospitality ⟨0⟩ ⟨0⟩
  let g := addPermanent g grizzlyBears ⟨0⟩ ⟨0⟩
  let g := passBoth (skipTo g .end 80)
  let g := skipTo g .precombatMain 80
  let g := addToHand g forest ⟨1⟩
  mustApply g ⟨1⟩ (.playLand (handCardNamed g ⟨1⟩ "Forest").id)

#guard nissaLandVsHospitality.stack.isEmpty
#guard !(nissaLandVsHospitality.log.any (fun s => mentions s "landfall"))
#guard (namedPermanent nissaLandVsHospitality "Grizzly Bears").status.plusOnePlusOne == 0

/-- If the targeted creature leaves before resolution, the trigger does nothing. -/
def hospitalityTargetGone : Game :=
  let id := (namedPermanent hospitalityLandfallTargeted "Grizzly Bears").id
  let (g, _) := hospitalityLandfallTargeted.move id (.graveyard ⟨0⟩) none
  passBoth g

#guard hospitalityTargetGone.log.any (fun s => mentions s "no longer in play")
#guard !(hospitalityTargetGone.battlefield.any (fun o => o.name == "Grizzly Bears"))

/-- Animate Beorn's Hospitality with three lands in play. -/
def hospitalityAnimateSetup : Game :=
  let g := addPermanent afterDraw beornsHospitality ⟨0⟩ ⟨0⟩
  let g := addForests g ⟨0⟩ 3
  g.modifyPlayer ⟨0⟩ (fun pl =>
    { pl with
      manaPool := pl.manaPool.add (.colored .green) 7
      landsPlayedThisTurn := 1 })

#guard hospitalityAnimateSetup.canActivate ⟨0⟩
  (namedPermanent hospitalityAnimateSetup "Beorn's Hospitality")
  (beornsHospitality.activatedAbilities[0]!)
#guard !(namedPermanent hospitalityAnimateSetup "Beorn's Hospitality").isCreature
#guard hospitalityAnimateSetup.landsYouControl ⟨0⟩ == 3

def proposedHospitalityAnimate : Game :=
  mustApply hospitalityAnimateSetup ⟨0⟩
    (.activate (namedPermanent hospitalityAnimateSetup "Beorn's Hospitality").id 0)

#guard proposedHospitalityAnimate.pending == .activateManaAbilities ⟨0⟩
#guard proposedHospitalityAnimate.log.any (fun s => mentions s "begins activating Beorn's Hospitality")

def paidHospitalityAnimate : Game :=
  mustApply proposedHospitalityAnimate ⟨0⟩ .pay

#guard paidHospitalityAnimate.hasPriority ⟨0⟩
#guard paidHospitalityAnimate.stack.size == 1
#guard paidHospitalityAnimate.log.any (fun s => mentions s "activates Beorn's Hospitality")

def animatedHospitality : Game := passBoth paidHospitalityAnimate

#guard animatedHospitality.stack.isEmpty
#guard (namedPermanent animatedHospitality "Beorn's Hospitality").isCreature
#guard (namedPermanent animatedHospitality "Beorn's Hospitality").hasSubtype "Bear"
#guard (namedPermanent animatedHospitality "Beorn's Hospitality").printed.isEnchantment
#guard (namedPermanent animatedHospitality "Beorn's Hospitality").types.any (· == .creature)
#guard (namedPermanent animatedHospitality "Beorn's Hospitality").types.any (· == .enchantment)
#guard (namedPermanent animatedHospitality "Beorn's Hospitality").status.additionalCreature
#guard animatedHospitality.power
  (namedPermanent animatedHospitality "Beorn's Hospitality") == 3
#guard animatedHospitality.toughness
  (namedPermanent animatedHospitality "Beorn's Hospitality") == 3
#guard animatedHospitality.log.any (fun s => mentions s "becomes a Bear creature")

/-- The animation does not wear off in cleanup. -/
def afterHospitalityCleanup : Game := passBoth (skipTo animatedHospitality .end 80)

#guard (namedPermanent afterHospitalityCleanup "Beorn's Hospitality").isCreature
#guard afterHospitalityCleanup.power
  (namedPermanent afterHospitalityCleanup "Beorn's Hospitality") == 3

/-- 0/0 animated Hospitality dies (CR 704.5f). -/
def hospitalityZeroLands : Game :=
  let g := addPermanent afterDraw beornsHospitality ⟨0⟩ ⟨0⟩
  let g := withGreenMana g ⟨0⟩ 7
  let g := mustApply g ⟨0⟩
    (.activate (namedPermanent g "Beorn's Hospitality").id 0)
  let g := mustApply g ⟨0⟩ .pay
  passBoth g

#guard !(hospitalityZeroLands.battlefield.any (fun o => o.name == "Beorn's Hospitality"))
#guard hospitalityZeroLands.log.any (fun s => mentions s "dies (toughness 0)")

/-- Pathmaker's printed setting ability uses lands you control. -/
def pathmakerWithLands : Game :=
  let g := addForests afterDraw ⟨0⟩ 2
  addPermanent g mirkwoodPathmaker ⟨0⟩ ⟨0⟩

#guard pathmakerWithLands.power (namedPermanent pathmakerWithLands "Mirkwood Pathmaker") == 2
#guard pathmakerWithLands.toughness
  (namedPermanent pathmakerWithLands "Mirkwood Pathmaker") == 2

/-- Landfall can target the animated Hospitality; P/T is lands plus counters. -/
def hospitalitySelfLandfall : Game :=
  let g := addPermanent afterDraw beornsHospitality ⟨0⟩ ⟨0⟩
  let g := addForests g ⟨0⟩ 3
  let o := namedPermanent g "Beorn's Hospitality"
  let g := g.setObject { o with
    status := { o.status with
      additionalCreature := true
      additionalSubtypes := #["Bear"]
      grantedStaticAbilities := #[.powerToughnessEqualLandsYouControl] } }
  let g := addToHand g forest ⟨0⟩
  let g := mustApply g ⟨0⟩ (.playLand (handCardNamed g ⟨0⟩ "Forest").id)
  let g := mustApply g ⟨0⟩
    (.target (Target.permanent (namedPermanent g "Beorn's Hospitality").id))
  passBoth g

#guard (namedPermanent hospitalitySelfLandfall "Beorn's Hospitality").status.plusOnePlusOne == 1
#guard hospitalitySelfLandfall.power
  (namedPermanent hospitalitySelfLandfall "Beorn's Hospitality") ==
    Int.ofNat (hospitalitySelfLandfall.landsYouControl ⟨0⟩) + 1

/-- Summoning sickness: a Hospitality that entered this turn cannot attack
after it becomes a creature (CR 302.6). -/
def hospitalityEnteredThisTurn : Game :=
  let g := withGreenMana (addToHand afterDraw beornsHospitality ⟨0⟩) ⟨0⟩ 2
  let g := mustApply g ⟨0⟩ (.cast (handCardNamed g ⟨0⟩ "Beorn's Hospitality").id)
  let g := mustApply g ⟨0⟩ .pay
  let g := passBoth g
  let g := addForests g ⟨0⟩ 2
  let g := withGreenMana g ⟨0⟩ 7
  let g := mustApply g ⟨0⟩
    (.activate (namedPermanent g "Beorn's Hospitality").id 0)
  let g := mustApply g ⟨0⟩ .pay
  passBoth g

#guard (namedPermanent hospitalityEnteredThisTurn "Beorn's Hospitality").isCreature
#guard !(hospitalityEnteredThisTurn.canAttack
  (namedPermanent hospitalityEnteredThisTurn "Beorn's Hospitality"))
#guard (namedPermanent hospitalityEnteredThisTurn "Beorn's Hospitality").status.summoningSick

/- The agent begins activating Hospitality when {5}{G}{G} is available. -/
#guard
  match Agent.choose hospitalityAnimateSetup ⟨0⟩ with
  | some (.activate id 0) =>
    (hospitalityAnimateSetup.object! id).name == "Beorn's Hospitality"
  | _ => false

end Mtg.Engine.Tests
