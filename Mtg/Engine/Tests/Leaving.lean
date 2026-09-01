import Mtg.Engine.Agent
import Mtg.Engine.Catalog
import Mtg.Engine.Catalog.Hobbit
import Mtg.Engine.Catalog.HobbitEternal
import Mtg.Engine.Catalog.MarvelSuperHeroes
import Mtg.Engine.Game
import Mtg.Engine.Oracle
import Mtg.Engine.Tests.Helpers
import Mtg.Engine.Tests.Turns
import Mtg.Engine.Tests.Mulligans

/-!
# A player leaving a multiplayer game (CR 800.4).
-/

namespace Mtg.Engine.Tests

open Mtg.Engine
open Mtg.Engine.Catalog

/-- Chandra concedes; Nissa and Liliana remain (CR 800.4). -/
def threeChandraConcedes : Game :=
  mustApply threeStarted ⟨0⟩ .concede

#guard (threeChandraConcedes.player ⟨0⟩).lost
#guard (threeChandraConcedes.player ⟨0⟩).leftTheGame
#guard !threeChandraConcedes.over
#guard threeChandraConcedes.livingPlayers.size == 2
#guard threeChandraConcedes.priority == ⟨1⟩
#guard threeChandraConcedes.activePlayer == ⟨0⟩
#guard threeChandraConcedes.log.any (fun s => mentions s "leaves the game")
#guard threeChandraConcedes.log.any (fun s => mentions s "concedes (CR 104.3a)")
#guard (threeChandraConcedes.player ⟨0⟩).hand.isEmpty
#guard (threeChandraConcedes.player ⟨0⟩).library.isEmpty
#guard (threeChandraConcedes.player ⟨1⟩).hand.size == 7
#guard threeChandraConcedes.actor == some ⟨1⟩

/-- Owned permanents leave; a teammate's permanent stays (CR 800.4a). -/
def threeOwnerLeavesPermanents : Game :=
  let g := addPermanent threeStarted grayOgre ⟨0⟩ ⟨0⟩
  let g := addPermanent g grizzlyBears ⟨1⟩ ⟨1⟩
  g.playerLeavesGame ⟨0⟩

#guard !threeOwnerLeavesPermanents.battlefield.any (fun o => o.name == "Gray Ogre")
#guard threeOwnerLeavesPermanents.battlefield.any (fun o => o.name == "Grizzly Bears")
#guard (threeOwnerLeavesPermanents.player ⟨0⟩).leftTheGame

/-- A permanent that entered under the leaving player is exiled (CR 800.4a,
Bribery). -/
def threeBriberyExile : Game :=
  let g := addPermanent threeStarted grizzlyBears ⟨1⟩ ⟨0⟩
  g.playerLeavesGame ⟨0⟩

#guard threeBriberyExile.objects.any (fun o =>
  o.name == "Grizzly Bears" && o.zone == .exile)
#guard !threeBriberyExile.battlefield.any (fun o => o.name == "Grizzly Bears")
#guard threeBriberyExile.log.any (fun s => mentions s "exiled (CR 800.4a)")

/-- An until-EOT control effect ends and the creature reverts (CR 800.4a,
Act of Treason). -/
def threeTreasonReverts : Game :=
  let g := addPermanent threeStarted grizzlyBears ⟨1⟩ ⟨1⟩
  let g := g.giveControlUntilEot (namedPermanent g "Grizzly Bears") ⟨0⟩
  g.playerLeavesGame ⟨0⟩

#guard (namedPermanent threeTreasonReverts "Grizzly Bears").controlledBy ⟨1⟩
#guard threeTreasonReverts.log.any (fun s => mentions s "reverts to Nissa's control")

/-- When a control effect ends and the default controller has left, exile
(CR 800.4c). -/
def threeControlEndsDefaultLeft : Game :=
  let g := addPermanent threeStarted grizzlyBears ⟨1⟩ ⟨0⟩
  let g := g.changeControl (namedPermanent g "Grizzly Bears") ⟨2⟩
  let g := g.playerLeavesGame ⟨0⟩
  g.endControlChangingEffect (namedPermanent g "Grizzly Bears")

#guard threeControlEndsDefaultLeft.objects.any (fun o =>
  o.name == "Grizzly Bears" && o.zone == .exile)
#guard threeControlEndsDefaultLeft.log.any (fun s => mentions s "exiled (CR 800.4c)")

/-- Tokens are not created under a player who has left (CR 800.4b). -/
def threeNoTokenForLeftPlayer : Game :=
  let g := threeStarted.playerLeavesGame ⟨0⟩
  (g.createToken ⟨0⟩ treasureToken).1

#guard !threeNoTokenForLeftPlayer.battlefield.any (fun o => o.name == "Treasure")
#guard threeNoTokenForLeftPlayer.log.any (fun s => mentions s "CR 800.4b")

/-- An object does not change control to a player who has left (CR 800.4b). -/
def threeNoControlToLeftPlayer : Game :=
  let g := addPermanent threeStarted grizzlyBears ⟨1⟩ ⟨1⟩
  let g := g.playerLeavesGame ⟨0⟩
  g.changeControl (namedPermanent g "Grizzly Bears") ⟨0⟩

#guard (namedPermanent threeNoControlToLeftPlayer "Grizzly Bears").controlledBy ⟨1⟩
#guard threeNoControlToLeftPlayer.log.any (fun s => mentions s "CR 800.4b")

/-- Ante objects owned by the leaving player stay (CR 800.4n). -/
def threeAnteStays : Game :=
  let g := insertObject threeStarted mountain ⟨0⟩ .ante
  g.playerLeavesGame ⟨0⟩

#guard threeAnteStays.objects.any (fun o => o.name == "Mountain" && o.zone == .ante)

/-- A trigger controlled by a player who has left is not put on the stack
(CR 800.4d). -/
def threeLeftPlayerTriggerSkipped : Game :=
  let g := addPermanent threeStarted elvishVisionary ⟨1⟩ ⟨1⟩
  let g := g.playerLeavesGame ⟨0⟩
  let vis := namedPermanent g "Elvish Visionary"
  g.putTriggeredAbilityOnStack ⟨0⟩ vis (.onEnterDraw 1) "enters"

#guard threeLeftPlayerTriggerSkipped.stack.isEmpty

/-- Combat damage is not assigned to a player who has left (CR 800.4e). -/
def threeNoCombatToLeftPlayer : Bool :=
  let g := addPermanent threeStarted grayOgre ⟨0⟩ ⟨0⟩
  let ogre := namedPermanent g "Gray Ogre"
  let g := g.setObject { ogre with status := { ogre.status with
    attacking := true, attackingWhom := some ⟨1⟩ } }
  let g := g.setPlayer { (g.player ⟨1⟩) with lost := true, leftTheGame := true }
  let asgn := g.defaultCombatAssignment (namedPermanent g "Gray Ogre") true #[]
  asgn.toPlayer == 0

#guard threeNoCombatToLeftPlayer

/-- A cost the leaving player would pay is not paid (CR 800.4f). -/
def threeUnpaidCostCounters : Game :=
  let g := addToHand threeStarted lightningBolt ⟨1⟩
  let bolt := handCardNamed g ⟨1⟩ "Lightning Bolt"
  let (g, newId) := g.move bolt.id .stack (some ⟨1⟩)
  let g := { g with pending := .payOrLetCounter ⟨0⟩ 3 newId }
  g.playerLeavesGame ⟨0⟩

#guard !threeUnpaidCostCounters.stack.any (fun e =>
  (threeUnpaidCostCounters.findObject? e.objectId).any (fun o =>
    o.name == "Lightning Bolt"))
#guard threeUnpaidCostCounters.log.any (fun s => mentions s "CR 800.4f")

/-- After Chandra leaves during her turn, Nissa takes the next turn and the
until-next-turn effect still lasts (CR 800.4j / 800.4m). -/
def threeAfterLeftPlayerCurrentTurn : Game :=
  let g := threeStarted.modifyPlayer ⟨0⟩ (fun pl =>
    { pl with protectionFromEverything := true })
  let g := mustApply g ⟨0⟩ .concede
  passBoth (skipTo g .end 200)

#guard threeAfterLeftPlayerCurrentTurn.activePlayer == ⟨1⟩
#guard threeAfterLeftPlayerCurrentTurn.step == .upkeep
#guard (threeAfterLeftPlayerCurrentTurn.player ⟨0⟩).protectionFromEverything

/-- Chandra's next turn does not begin (CR 800.4k). Effects that last until
that turn expire when it would have begun (CR 800.4m). -/
def threeSkipLeftPlayerTurn : Game :=
  let g := passBoth (skipTo threeAfterLeftPlayerCurrentTurn .end 200)
  passBoth (skipTo g .end 200)

#guard threeSkipLeftPlayerTurn.activePlayer == ⟨1⟩
#guard threeSkipLeftPlayerTurn.step == .upkeep
#guard !(threeSkipLeftPlayerTurn.player ⟨0⟩).protectionFromEverything
#guard threeSkipLeftPlayerTurn.log.any (fun s => mentions s "CR 800.4m")
#guard threeSkipLeftPlayerTurn.log.any (fun s => mentions s "Liliana's turn")

end Mtg.Engine.Tests
