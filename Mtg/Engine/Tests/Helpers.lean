import Mtg.Engine.Agent
import Mtg.Engine.Catalog
import Mtg.Engine.Catalog.Hobbit
import Mtg.Engine.Catalog.HobbitEternal
import Mtg.Engine.Catalog.MarvelSuperHeroes
import Mtg.Engine.Game
import Mtg.Engine.Oracle

/-!
# Shared fixtures, start-of-game setup, and idle-action helpers.
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

/-- `--norandom` pauses before opening shuffles so the host supplies the order. -/
def norandomOpening : Game :=
  match Start.start { testConfig 1 with norandom := true } with
  | .ok g => g
  | .error e => panic! e

#guard norandomOpening.norandom
#guard (norandomOpening.player ⟨0⟩).hand.isEmpty
#guard (norandomOpening.player ⟨1⟩).hand.isEmpty
#guard
  match norandomOpening.pendingRandom? with
  | some (.shuffleLibrary p) => p == ⟨0⟩
  | _ => false

#guard
  match norandomOpening.apply ⟨0⟩ (.supplyOrder #[⟨99⟩]) with
  | .error msg =>
    msg == "Shuffle must list each library card once (bottom first), or omit the ids to keep the current order"
  | .ok _ => false

def norandomAfterFirstShuffle : Game :=
  match norandomOpening.apply ⟨0⟩ (.supplyOrder #[]) with
  | .ok g => g
  | .error e => panic! e

#guard
  match norandomAfterFirstShuffle.pendingRandom? with
  | some (.shuffleLibrary p) => p == ⟨1⟩
  | _ => false
#guard (norandomAfterFirstShuffle.player ⟨0⟩).hand.isEmpty

def norandomDrawnHands : Game :=
  match norandomAfterFirstShuffle.apply ⟨1⟩ (.supplyOrder #[]) with
  | .ok g => g
  | .error e => panic! e

#guard norandomDrawnHands.pending == .declareMulligan ⟨0⟩
#guard (norandomDrawnHands.player ⟨0⟩).hand.size == 7
#guard (norandomDrawnHands.player ⟨1⟩).hand.size == 7
#guard (norandomDrawnHands.player ⟨0⟩).library.size == 53

/- Without `--norandom`, `Start.start` still shuffles from the seed. -/
#guard !drawnHands.norandom
#guard drawnHands.pendingRandom?.isNone

#guard
  match Start.start { testConfig 1 with norandom := true, startingPlayer := none } with
  | .ok g =>
    match g.pendingRandom? with
    | some (.chooseIndex n) => n == 2 && g.startingPlayer == ⟨0⟩
    | _ => false
  | .error _ => false

#guard
  match Start.start { testConfig 1 with norandom := true, startingPlayer := none } with
  | .ok g =>
    match g.apply ⟨0⟩ (.supplyIndex 1) with
    | .ok g' =>
      g'.startingPlayer == ⟨1⟩ &&
        (match g'.pendingRandom? with
         | some (.shuffleLibrary p) => p == ⟨0⟩
         | _ => false) &&
        g'.log.any (· == "Starting player: Nissa")
    | .error _ => false
  | .error _ => false

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

/-- `true` iff some log line contains `needle`. -/
def logContains (g : Game) (needle : String) : Bool :=
  g.log.any (fun s => mentions s needle)

/-- First card of `p`'s hand; tests assume opening hands are non-empty. -/
def firstHandCard (g : Game) (p : PlayerId) : GameObject :=
  match (g.handObjects p)[0]? with
  | some o => o
  | none => panic! "expected a card in hand"

def drawnOnce : Game := Game.draw started ⟨0⟩

#guard (drawnOnce.player ⟨0⟩).hand.size == 8
#guard (drawnOnce.player ⟨0⟩).library.size == 52
#guard (drawnOnce.player ⟨1⟩).hand.size == 7

/-- Put `card` into the game as a new object and optionally update its owner. -/
def insertObject (g : Game) (card : CardDef) (owner : PlayerId) (zone : Zone)
    (controller : Option PlayerId := none) (status : Status := {})
    (updateOwner : ObjectId → Player → Player := fun _ pl => pl) : Game :=
  let (g, obj) := g.allocObject card owner zone controller status
  g.modifyPlayer owner (updateOwner obj.id)

/-- Put `card` onto the battlefield with explicit owner and controller. -/
def addPermanent (g : Game) (card : CardDef) (owner controller : PlayerId) : Game :=
  let status : Status :=
    { summoningSick := false
      indestructibleCounters := if card.entersWithIndestructibleCounter then 1 else 0 }
  insertObject g card owner .battlefield (some controller) status

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

def withGoblin : Game := addPermanent started ragingGoblin ⟨0⟩ ⟨0⟩
def withElves : Game := addPermanent started llanowarElves ⟨0⟩ ⟨0⟩
def withSpider : Game := addPermanent started giantSpider ⟨0⟩ ⟨0⟩
def withAttercop : Game := addPermanent started attercop ⟨0⟩ ⟨0⟩
def withWarg : Game := addPermanent started raveningWarg ⟨0⟩ ⟨0⟩
def withGollum : Game := addPermanent started gollumSilentSlinker ⟨0⟩ ⟨0⟩
def withCrusher : Game := addPermanent started ologHaiCrusher ⟨0⟩ ⟨0⟩

def mustApply (g : Game) (p : PlayerId) (a : Action) : Game :=
  match g.apply p a with
  | .ok g' => g'
  | .error e => panic! e

/-- Apply the idle action for whoever must act: empty combat declarations or pass. -/
def applyIdle (g : Game) : Game :=
  match g.pending, g.actor with
  | .declareAttackers, some p =>
    mustApply g p (.declareAttackers #[])
  | .declareBlockers, some p =>
    mustApply g p (.declareBlockers #[])
  | .declareMulligan _, some p =>
    mustApply g p .keep
  | .putOnBottom _ n, some p =>
    mustApply g p (.putOnBottom ((g.player p).hand.extract 0 n))
  | .scry _ n, some p =>
    mustApply g p (.scry (g.scryLookedIds p n) #[])
  | .mayDiscardDraw _ _, some p =>
    mustApply g p .decline
  | .chooseTeamwork _, some p =>
    mustApply g p (.announceTeamwork false)
  | .chooseTeamworkCreatures _ need, some p =>
    mustApply g p (.choosePermanents (g.pickTeamworkCreatures p need))
  | .chooseAdditionalCost _, some p =>
    match g.proposedSpell with
    | none => panic! "expected a proposed spell while choosing an additional cost"
    | some prop =>
      mustApply g p (.chooseAdditionalCost (g.additionalCostChoosesGeneric p prop))
  | .discardForAdditionalCost p, some _ =>
    match (g.player p).hand.back? with
    | none => panic! "no card to discard as an additional cost"
    | some id => mustApply g p (.discard id)
  | .chooseSacrificeCreature p _ _, some _ =>
    match (g.creaturesControlledBy p)[0]? with
    | none => panic! "no creature to sacrifice"
    | some o => mustApply g p (.sacrifice o.id)
  | .chooseDiscardCard p _, some _ =>
    match (g.player p).hand.back? with
    | none => panic! "no card to discard"
    | some id => mustApply g p (.discard id)
  | .sacrificeCreature _, some p =>
    match (g.sacrificeCreatureChoices p)[0]? with
    | some sac => mustApply g p (.sacrifice sac.id)
    | none => panic! "expected a creature to sacrifice"
  | .chooseMode _, some p =>
    match g.proposedSpell with
    | none => panic! "expected a proposed spell or ability while choosing a mode"
    | some prop =>
      match prop.kind with
      | .activatedAbility =>
        match g.defaultAbilityMode p prop.abilityModes with
        | none => panic! "no legal mode (CR 601.2b)"
        | some idx => mustApply g p (.chooseMode idx)
      | .spell =>
        match g.findObject? prop.spellId with
        | none => panic! "expected a proposed spell while choosing a mode"
        | some spell =>
          match g.defaultMode p spell with
          | none => panic! "no legal mode (CR 601.2b)"
          | some i => mustApply g p (.chooseMode i)
  | .chooseX _, some p =>
    mustApply g p (.chooseX 0)
  | .assignCombatDamage _ _, some p =>
    mustApply g p (.assignCombatDamage #[])
  | .chooseLegend _ _ ids, some p =>
    mustApply g p (.keepLegend (g.defaultLegendToKeep ids))
  | .chooseTriggerToStack p, some _ =>
    mustApply g p (.stackTriggers (g.defaultTriggerSourceIds p))
  | .mayPayGeneric _ _, some p =>
    mustApply g p .decline
  | .chooseLibraryPlacement _ _, some p =>
    mustApply g p .chooseBottom
  | .mayAttachEquipment _ _, some p =>
    mustApply g p .decline
  | .tapHumans _, some p =>
    mustApply g p .decline
  | .payOrLetCounter _ _ _, some p =>
    mustApply g p .decline
  | .payWard _ _ _, some p =>
    mustApply g p .decline
  | .recruitDiscard _, some p =>
    match (g.player p).hand.back? with
    | none => panic! "no card to discard for recruit"
    | some id => mustApply g p (.discard id)
  | .maySacrificeAnotherBolg _ _, some p =>
    mustApply g p .decline
  | .mayCastFromLooked _ _ _, some p =>
    mustApply g p .decline
  | .mayPutLandFromHand _, some p =>
    mustApply g p .decline
  | .chooseFoodOrTreasure _, some p =>
    mustApply g p (.chooseMode 0)
  | .chooseTapOrUntap _ _, some p =>
    mustApply g p (.chooseMode 0)
  | .maySacArtifactOrDiscard _, some p =>
    mustApply g p .decline
  | .mayPutArtifactFromHand _ _, some p =>
    mustApply g p .decline
  | .mayHaveVillainConnive _ _ _, some p =>
    mustApply g p .decline
  | .chooseTargets _, some p =>
    match g.objectAwaitingTargets with
    | none => panic! "expected a proposed spell or trigger while choosing targets"
    | some spell =>
      match g.defaultTarget p spell with
      | some t => mustApply g p (.target t)
      | none =>
        if g.canSkipCurrentOptionalSlot spell then mustApply g p .decline
        else if g.canFinishOptionalTargets spell then mustApply g p .decline
        else
          match spell.triggeredAbility with
          | some ab =>
            if ab.allowsZeroTargets then mustApply g p .decline
            else panic! "no legal target (CR 601.2c)"
          | none => panic! "no legal target (CR 601.2c)"
  | _, some p =>
    mustApply g p .pass
  | _, none => panic! s!"no actor at {g.step}"

/-- Advance by idle actions until `g` is in `st` with no pending choice. -/
def skipTo (g : Game) (st : Step) : Nat → Game
  | 0 => panic! s!"skipTo fuel exhausted at {g.step}"
  | n + 1 =>
    if g.over then panic! "game over while skipping"
    else if g.step == st && g.pending == .none then g
    else skipTo (applyIdle g) st n

/-- Advance by idle actions until `g.pending` is `pend`. -/
def skipToPending (g : Game) (pend : Pending) : Nat → Game
  | 0 => panic! s!"skipToPending fuel exhausted at {g.step}"
  | n + 1 =>
    if g.over then panic! "game over while skipping"
    else if g.pending == pend then g
    else skipToPending (applyIdle g) pend n

def passBoth (g : Game) : Game :=
  applyIdle (applyIdle g)

end Mtg.Engine.Tests
