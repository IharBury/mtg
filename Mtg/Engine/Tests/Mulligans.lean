import Mtg.Engine.Agent
import Mtg.Engine.Catalog
import Mtg.Engine.Catalog.Hobbit
import Mtg.Engine.Catalog.HobbitEternal
import Mtg.Engine.Catalog.MarvelSuperHeroes
import Mtg.Engine.Game
import Mtg.Engine.Oracle
import Mtg.Engine.Tests.Helpers
import Mtg.Engine.Tests.Turns

/-!
# London mulligans, multiplayer combat, and Brawl.
-/

namespace Mtg.Engine.Tests

open Mtg.Engine
open Mtg.Engine.Catalog

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

#guard !drawnHands.isMultiplayer
#guard !drawnHands.freeFirstMulligan
#guard !drawnHands.brawl
#guard drawnHands.countedMulligans ⟨0⟩ == 0

/-- Three constructed seats so CR 100.1b treats the game as multiplayer. -/
def testThreeConfig : StartConfig := {
  seats := #[
    { name := "Chandra", deck := testRedDeck },
    { name := "Nissa", deck := testGreenDeck },
    { name := "Liliana", deck := testRedDeck }
  ]
  format := .constructed
  seed := 1
  startingPlayer := some 0
}

def threeDrawnHands : Game :=
  match Start.start testThreeConfig with
  | .ok g => g
  | .error e => panic! e

#guard threeDrawnHands.isMultiplayer
#guard threeDrawnHands.freeFirstMulligan
#guard !threeDrawnHands.skipsFirstDraw
#guard threeDrawnHands.pending == .declareMulligan ⟨0⟩
#guard threeDrawnHands.players.size == 3

/-- CR 103.5c: the first multiplayer mulligan puts no cards on the bottom. -/
def afterThreeChandraDeclares : Game :=
  mustApply threeDrawnHands ⟨0⟩ .takeMulligan

#guard afterThreeChandraDeclares.pending == .declareMulligan ⟨1⟩
#guard (afterThreeChandraDeclares.player ⟨0⟩).mulligansTaken == 0

def afterThreeFirstMulligan : Game :=
  let g := mustApply afterThreeChandraDeclares ⟨1⟩ .keep
  mustApply g ⟨2⟩ .keep

#guard afterThreeFirstMulligan.pending == .declareMulligan ⟨0⟩
#guard afterThreeFirstMulligan.actor == some ⟨0⟩
#guard (afterThreeFirstMulligan.player ⟨0⟩).hand.size == 7
#guard (afterThreeFirstMulligan.player ⟨0⟩).mulligansTaken == 1
#guard afterThreeFirstMulligan.countedMulligans ⟨0⟩ == 0
#guard !(afterThreeFirstMulligan.player ⟨0⟩).keptOpeningHand
#guard (afterThreeFirstMulligan.player ⟨1⟩).keptOpeningHand
#guard (afterThreeFirstMulligan.player ⟨2⟩).keptOpeningHand
#guard afterThreeFirstMulligan.log.any (fun s => mentions s "CR 103.5c")
#guard afterThreeFirstMulligan.log.any (fun s =>
  mentions s "puts no cards on the bottom")
#guard afterThreeFirstMulligan.canTakeMulligan ⟨0⟩

/-- The second multiplayer mulligan counts as the first toward bottoming. -/
def afterThreeSecondMulligan : Game :=
  mustApply afterThreeFirstMulligan ⟨0⟩ .takeMulligan

#guard afterThreeSecondMulligan.pending == .putOnBottom ⟨0⟩ 1
#guard (afterThreeSecondMulligan.player ⟨0⟩).mulligansTaken == 2
#guard afterThreeSecondMulligan.countedMulligans ⟨0⟩ == 1
#guard (afterThreeSecondMulligan.player ⟨0⟩).hand.size == 7

/-- In multiplayer, one extra mulligan is legal before the zero-card limit. -/
def eighthMultiplayerMulligan : Game :=
  let g := threeDrawnHands.modifyPlayer ⟨0⟩ (fun pl => { pl with mulligansTaken := 7 })
  let g := mustApply g ⟨0⟩ .takeMulligan
  let g := mustApply g ⟨1⟩ .keep
  mustApply g ⟨2⟩ .keep

#guard eighthMultiplayerMulligan.pending == .putOnBottom ⟨0⟩ 7
#guard (eighthMultiplayerMulligan.player ⟨0⟩).mulligansTaken == 8
#guard eighthMultiplayerMulligan.countedMulligans ⟨0⟩ == 7

/-- Three-player game after opening hands, ready for Chandra's first turn. -/
def threeStarted : Game := keepOpeningHands threeDrawnHands 16

#guard threeStarted.players.size == 3
#guard threeStarted.activePlayer == ⟨0⟩

/-- Chandra has a Gray Ogre and must declare attackers. -/
def threeReadyToAttack : Game :=
  skipToPending (addPermanent threeStarted grayOgre ⟨0⟩ ⟨0⟩) .declareAttackers 200

#guard threeReadyToAttack.pending == .declareAttackers
#guard threeReadyToAttack.activePlayer == ⟨0⟩
#guard threeReadyToAttack.opponent ⟨0⟩ == ⟨1⟩

/-- Default declaration attacks the next opponent (Nissa). -/
def threeOgreAttacksNissa : Game :=
  mustApply threeReadyToAttack ⟨0⟩
    (.declareAttackers #[(namedPermanent threeReadyToAttack "Gray Ogre").id])

#guard (namedPermanent threeOgreAttacksNissa "Gray Ogre").status.attackingWhom == some ⟨1⟩
#guard threeOgreAttacksNissa.defendingPlayer == ⟨1⟩

/-- Chandra can choose to attack Liliana instead of Nissa (CR 508.1). -/
def threeOgreAttacksLiliana : Game :=
  mustApply threeReadyToAttack ⟨0⟩
    (.declareAttackers #[(namedPermanent threeReadyToAttack "Gray Ogre").id] (some ⟨2⟩))

#guard (namedPermanent threeOgreAttacksLiliana "Gray Ogre").status.attackingWhom == some ⟨2⟩
#guard threeOgreAttacksLiliana.defendingPlayer == ⟨2⟩
#guard threeOgreAttacksLiliana.log.any (fun s => mentions s "attacks Liliana with Gray Ogre")

#guard
  match threeReadyToAttack.declareAttackers ⟨0⟩
      #[(namedPermanent threeReadyToAttack "Gray Ogre").id] (some ⟨0⟩) with
  | .error msg => mentions msg "cannot attack yourself"
  | .ok _ => false

/-- Liliana, not Nissa, declares blockers when she is being attacked. -/
def threeLilianaToBlock : Game :=
  skipToPending threeOgreAttacksLiliana .declareBlockers 80

#guard threeLilianaToBlock.pending == .declareBlockers
#guard threeLilianaToBlock.actor == some ⟨2⟩
#guard threeLilianaToBlock.defendingPlayer == ⟨2⟩

/-- Unblocked combat damage goes to the chosen defending player. -/
def threeLilianaTookCombat : Game :=
  skipTo threeOgreAttacksLiliana .postcombatMain 80

#guard (threeLilianaTookCombat.player ⟨2⟩).life == 18
#guard (threeLilianaTookCombat.player ⟨1⟩).life == 20
#guard (threeLilianaTookCombat.player ⟨0⟩).life == 20

/-- Two Gray Ogres so each can attack a different opponent (CR 508.1). -/
def threeTwoOgresReady : Game :=
  skipToPending
    (addPermanent (addPermanent threeStarted grayOgre ⟨0⟩ ⟨0⟩) grayOgre ⟨0⟩ ⟨0⟩)
    .declareAttackers 200

#guard threeTwoOgresReady.pending == .declareAttackers
#guard (threeTwoOgresReady.battlefield.filter (·.name == "Gray Ogre")).size == 2

def threeSplitAttack : Game :=
  let ogres := threeTwoOgresReady.battlefield.filter (·.name == "Gray Ogre")
  mustApply threeTwoOgresReady ⟨0⟩
    (.declareAttackers #[ogres[0]!.id, ogres[1]!.id] none #[some ⟨1⟩, some ⟨2⟩])

#guard
  let ogres := threeSplitAttack.battlefield.filter (·.name == "Gray Ogre")
  ogres[0]!.status.attackingWhom == some ⟨1⟩ &&
    ogres[1]!.status.attackingWhom == some ⟨2⟩
#guard threeSplitAttack.log.any (fun s => mentions s "attacks Nissa with Gray Ogre")
#guard threeSplitAttack.log.any (fun s => mentions s "attacks Liliana with Gray Ogre")

/-- Nissa declares blockers first (APNAP), then Liliana. -/
def threeSplitNissaToBlock : Game :=
  skipToPending threeSplitAttack .declareBlockers 80

#guard threeSplitNissaToBlock.pending == .declareBlockers
#guard threeSplitNissaToBlock.actor == some ⟨1⟩
#guard threeSplitNissaToBlock.defendingPlayers == #[⟨1⟩, ⟨2⟩]

def threeSplitLilianaToBlock : Game :=
  mustApply threeSplitNissaToBlock ⟨1⟩ (.declareBlockers #[])

#guard threeSplitLilianaToBlock.pending == .declareBlockers
#guard threeSplitLilianaToBlock.actor == some ⟨2⟩

/-- Each unblocked ogre deals 2 to its own defending player. -/
def threeSplitCombatDone : Game :=
  skipTo threeSplitAttack .postcombatMain 80

#guard (threeSplitCombatDone.player ⟨1⟩).life == 18
#guard (threeSplitCombatDone.player ⟨2⟩).life == 18
#guard (threeSplitCombatDone.player ⟨0⟩).life == 20

#guard
  let g := threeDrawnHands.modifyPlayer ⟨0⟩ (fun pl => { pl with mulligansTaken := 8 })
  match g.apply ⟨0⟩ .takeMulligan with
  | .error msg => mentions msg "zero cards"
  | .ok _ => false

/-- CR 103.5c / 903.12g: any Brawl game, including two-player, has a free first
mulligan. -/
def brawlDrawnHands : Game :=
  match Start.start { testConfig 1 with brawl := true } with
  | .ok g => g
  | .error e => panic! e

#guard !brawlDrawnHands.isMultiplayer
#guard brawlDrawnHands.brawl
#guard brawlDrawnHands.freeFirstMulligan
#guard brawlDrawnHands.skipsFirstDraw

def afterBrawlFirstMulligan : Game :=
  let g := mustApply brawlDrawnHands ⟨0⟩ .takeMulligan
  mustApply g ⟨1⟩ .keep

#guard afterBrawlFirstMulligan.pending == .declareMulligan ⟨0⟩
#guard (afterBrawlFirstMulligan.player ⟨0⟩).hand.size == 7
#guard (afterBrawlFirstMulligan.player ⟨0⟩).mulligansTaken == 1
#guard afterBrawlFirstMulligan.countedMulligans ⟨0⟩ == 0
#guard afterBrawlFirstMulligan.log.any (fun s => mentions s "CR 103.5c")

def afterBrawlSecondMulligan : Game :=
  mustApply afterBrawlFirstMulligan ⟨0⟩ .takeMulligan

#guard afterBrawlSecondMulligan.pending == .putOnBottom ⟨0⟩ 1
#guard (afterBrawlSecondMulligan.player ⟨0⟩).mulligansTaken == 2

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

end Mtg.Engine.Tests
