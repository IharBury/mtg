import Mtg.Engine.Tests
import Mtg.Demo.Render

/-!
# Compile-time tests for console rendering.
-/

namespace Mtg.Demo.RenderTests

open Mtg.Engine
open Mtg.Engine.Game
open Mtg.Engine.Tests
open Mtg.Demo.Render

#guard (changedZones started started).isEmpty
#guard (zoneObjectIds started (.hand ⟨0⟩)).size == 7
#guard (zoneObjectIds started (.library ⟨0⟩)).size == 53
#guard (zoneObjectIds started .stack).isEmpty
#guard zoneBlock started .stack == "zone stack (0): (empty)"
#guard zoneBlock started (.library ⟨0⟩) == "zone Chandra's library (53)"

#guard canSeeZoneFaces none (.hand ⟨1⟩)
#guard canSeeZoneFaces (some ⟨0⟩) (.hand ⟨0⟩)
#guard !canSeeZoneFaces (some ⟨0⟩) (.hand ⟨1⟩)
#guard !canSeeZoneFaces none (.library ⟨0⟩)
#guard !canSeeZoneFaces (some ⟨0⟩) (.library ⟨0⟩)
#guard canSeeZoneFaces (some ⟨0⟩) .battlefield
#guard canSeeZoneFaces (some ⟨0⟩) (.graveyard ⟨1⟩)

#guard zoneBlock started (.library ⟨0⟩) (some ⟨0⟩) == "zone Chandra's library (53)"
#guard zoneBlock started (.hand ⟨1⟩) (some ⟨0⟩) == "zone Nissa's hand (7)"
#guard mentions (zoneBlock started (.hand ⟨0⟩) (some ⟨0⟩)) (firstHandCard started ⟨0⟩).name
#guard !mentions (zoneBlock started (.hand ⟨1⟩) (some ⟨0⟩)) (firstHandCard started ⟨1⟩).name
#guard mentions (zoneBlock started (.hand ⟨1⟩)) (firstHandCard started ⟨1⟩).name

#guard mentions (playerBlock started (started.player ⟨1⟩) (some ⟨0⟩)) "Hand (7):"
#guard mentions (playerBlock started (started.player ⟨1⟩) (some ⟨0⟩)) "(hidden)"
#guard !mentions (playerBlock started (started.player ⟨1⟩) (some ⟨0⟩))
  (firstHandCard started ⟨1⟩).name
#guard mentions (playerBlock started (started.player ⟨0⟩) (some ⟨0⟩))
  (firstHandCard started ⟨0⟩).name

#guard mentions (snapshot started (some ⟨0⟩)) "Chandra's view"
#guard !mentions (snapshot started) "view"
#guard mentions (snapshot started (some ⟨0⟩)) (firstHandCard started ⟨0⟩).name
#guard !mentions (snapshot started (some ⟨0⟩)) (firstHandCard started ⟨1⟩).name
#guard mentions (snapshot started) (firstHandCard started ⟨1⟩).name

#guard redactLogLine started ⟨0⟩ "Nissa draws Forest" == "Nissa draws a card"
#guard redactLogLine started ⟨0⟩ "Chandra draws Mountain" == "Chandra draws Mountain"
#guard redactLogLine started ⟨0⟩ "Nissa puts Forest on the bottom of their library" ==
  "Nissa puts a card on the bottom of their library"
#guard redactLogLine started ⟨0⟩ "Nissa puts Forest on top of their library" ==
  "Nissa puts a card on top of their library"
#guard redactLogLine started ⟨0⟩ "Chandra puts Forest on top of their library" ==
  "Chandra puts Forest on top of their library"
#guard redactLogLine started ⟨0⟩ "Nissa puts Forest onto the battlefield tapped" ==
  "Nissa puts Forest onto the battlefield tapped"
#guard (newLog started 0 (some ⟨0⟩)).any (· == "Nissa draws a card")
#guard !(newLog started 0 (some ⟨0⟩)).any (fun s =>
  s.startsWith "Nissa draws " && s != "Nissa draws a card")
#guard (newLog started 0).any (fun s =>
  s.startsWith "Nissa draws " && s != "Nissa draws a card")

#guard (zoneObjectIds drawnOnce (.hand ⟨0⟩)).size == 8
#guard (zoneObjectIds drawnOnce (.library ⟨0⟩)).size == 52
#guard (changedZones started drawnOnce).contains (.hand ⟨0⟩)
#guard (changedZones started drawnOnce).contains (.library ⟨0⟩)
#guard !(changedZones started drawnOnce).contains .battlefield
#guard !(changedZones started drawnOnce).contains .stack
#guard zoneBlock drawnOnce (.hand ⟨1⟩) (some ⟨0⟩) == "zone Nissa's hand (7)"
#guard mentions (zoneBlock drawnOnce (.hand ⟨0⟩) (some ⟨0⟩)) (firstHandCard drawnOnce ⟨0⟩).name
#guard (zoneBlock drawnOnce (.hand ⟨0⟩) (some ⟨0⟩)).startsWith "zone Chandra's hand (8):"

-- Occupants are unchanged, but the land is now tapped, so the battlefield
-- must reprint (the demo shows the land as tapped).
#guard (zoneObjectIds withMountain .battlefield) == (zoneObjectIds tappedMountain .battlefield)
#guard battlefieldView withMountain != battlefieldView tappedMountain
#guard (zoneBlock withMountain .battlefield) != (zoneBlock tappedMountain .battlefield)
#guard (changedZones withMountain tappedMountain).contains .battlefield
#guard (changedZones withMountain withMountain).isEmpty
#guard (changedManaPools withMountain tappedMountain).size == 1
#guard (changedManaPools withMountain tappedMountain).any (fun pl =>
  pl.id == ⟨0⟩ && !pl.manaPool.isEmpty)
#guard manaLine (tappedMountain.player ⟨0⟩) == "Chandra — mana {R}×1"

def mountainLine (g : Game) : String :=
  objectLine g (lastPermanent g)

#guard mountainLine withMountain ==
  s!"{(lastPermanent withMountain).id} Mountain \{T}: Add \{R}. (owned by Chandra, controlled by Chandra)"
#guard mentions (mountainLine withMountain) "{T}: Add {R}"
-- Ungrouped lines still name owner and controller. Grouped battlefield
-- listings omit them when they match the controller heading.
#guard !mentions (zoneBlock withMountain .battlefield) "owned by"
#guard !mentions (zoneBlock withMountain .battlefield) "controlled by"
#guard !mentions (snapshot withMountain) "owned by"
#guard !mentions (snapshot withMountain) "controlled by"
#guard mentions (mountainLine tappedMountain) "(tapped)"
#guard mentions (mountainLine tappedMountain)
  "(owned by Chandra, controlled by Chandra)"

#guard (zoneObjectIds tappedMountain .battlefield) == (zoneObjectIds afterUntapStep .battlefield)
#guard battlefieldView tappedMountain != battlefieldView afterUntapStep
#guard (zoneBlock tappedMountain .battlefield) != (zoneBlock afterUntapStep .battlefield)
#guard (changedZones tappedMountain afterUntapStep).contains .battlefield
#guard !mentions (mountainLine afterUntapStep) "(tapped)"

#guard mountainLine stolenMountain ==
  s!"{(lastPermanent stolenMountain).id} Mountain \{T}: Add \{R}. (owned by Chandra, controlled by Nissa)"
-- Grouped under Nissa: owner differs, so it is printed; controller matches.
#guard mentions (playerBlock stolenMountain (stolenMountain.player ⟨1⟩))
  "(owned by Chandra)"
#guard !mentions (playerBlock stolenMountain (stolenMountain.player ⟨1⟩))
  "controlled by"
#guard mentions (playerBlock stolenMountain (stolenMountain.player ⟨0⟩)) "  (none)"
#guard mentions (zoneBlock stolenMountain .battlefield)
  "(owned by Chandra)"
#guard !mentions (zoneBlock stolenMountain .battlefield) "controlled by"
#guard mentions (snapshot stolenMountain)
  "(owned by Chandra)"
#guard !mentions (snapshot stolenMountain) "controlled by"

#guard (zoneObjectIds withMountain .battlefield) == (zoneObjectIds afterControlChange .battlefield)
#guard battlefieldView withMountain != battlefieldView afterControlChange
#guard (changedZones withMountain afterControlChange).contains .battlefield
#guard mentions (objectLine afterControlChange (lastPermanent afterControlChange))
  "(owned by Chandra, controlled by Nissa)"
#guard mentions (objectLine afterControlChange (lastPermanent afterControlChange)
  (some (some ⟨1⟩))) "(owned by Chandra)"
#guard !mentions (objectLine afterControlChange (lastPermanent afterControlChange)
  (some (some ⟨1⟩))) "controlled by"

/- The shared battlefield listing is grouped by controller (CR 110.2). -/
#guard zoneBlock started .battlefield == "zone battlefield (0): (empty)"

#guard
  let m := lastPermanent withMountain
  zoneBlock withMountain .battlefield ==
    s!"zone battlefield (1):\n  Chandra:\n    {objectLine withMountain m (some (some ⟨0⟩))}"

#guard
  let m := lastPermanent stolenMountain
  zoneBlock stolenMountain .battlefield ==
    s!"zone battlefield (1):\n  Nissa:\n    {objectLine stolenMountain m (some (some ⟨1⟩))}"

#guard
  let forestP := (mixedControllers.permanentsOf ⟨0⟩)[0]!
  let mountainP := (mixedControllers.permanentsOf ⟨1⟩)[0]!
  forestP.name == "Forest" && mountainP.name == "Mountain" &&
    zoneBlock mixedControllers .battlefield ==
      s!"zone battlefield (2):\n  Chandra:\n    {objectLine mixedControllers forestP (some (some ⟨0⟩))}\n  Nissa:\n    {objectLine mixedControllers mountainP (some (some ⟨1⟩))}"

#guard
  let m := lastPermanent uncontrolledPermanent
  zoneBlock uncontrolledPermanent .battlefield ==
    s!"zone battlefield (1):\n  (no controller):\n    {objectLine uncontrolledPermanent m (some none)}"

-- Owner still prints under the no-controller heading; "no controller" does not
-- repeat on the permanent line.
#guard mentions (zoneBlock uncontrolledPermanent .battlefield) "(owned by Chandra)"
#guard !mentions (objectLine uncontrolledPermanent (lastPermanent uncontrolledPermanent)
  (some none)) "no controller"
#guard !mentions (objectLine withMountain (lastPermanent withMountain) (some (some ⟨0⟩)))
  "owned by"
#guard !mentions (objectLine mixedControllers
  ((mixedControllers.permanentsOf ⟨0⟩)[0]!) (some (some ⟨0⟩))) "owned by"
#guard mentions (objectLine mixedControllers
  ((mixedControllers.permanentsOf ⟨1⟩)[0]!) (some (some ⟨1⟩))) "(owned by Chandra)"

#guard mentions (objectLine withGoblin (lastPermanent withGoblin)) "haste"
#guard mentions (playerBlock withGoblin (withGoblin.player ⟨0⟩)) "haste"
#guard mentions (objectLine withElves (lastPermanent withElves)) "{T}: Add {G}"
#guard mentions (objectLine withSpider (lastPermanent withSpider)) "reach"
#guard mentions (objectLine withAttercop (lastPermanent withAttercop)) "deathtouch"
#guard mentions (objectLine withAttercop (lastPermanent withAttercop)) "Landfall"
#guard mentions (zoneLine withAttercop .battlefield (lastPermanent withAttercop).id)
  "Landfall"

#guard (zoneObjectIds nissaEnd .battlefield) == (zoneObjectIds chandraTurn3 .battlefield)
#guard battlefieldView nissaEnd != battlefieldView chandraTurn3
#guard (changedZones nissaEnd chandraTurn3).contains .battlefield
#guard mentions (zoneBlock nissaEnd .battlefield) "(tapped)"
#guard !mentions (zoneBlock chandraTurn3 .battlefield) "(tapped)"

#guard (changedLifeTotals started started).isEmpty
#guard (changedLifeTotals started afterDraw).isEmpty
#guard lifeLine (started.player ⟨0⟩) == "Chandra — life 20"
#guard lifeLine (started.player ⟨1⟩) == "Nissa — life 20"
#guard (changedLifeTotals started afterBolt).size == 1
#guard (changedLifeTotals started afterBolt).any (fun pl => pl.id == ⟨1⟩ && pl.life == 17)
#guard lifeLine (afterBolt.player ⟨1⟩) == "Nissa — life 17"
#guard mentions (playerBlock afterBolt (afterBolt.player ⟨1⟩)) "life 17"

#guard (changedLifeTotals attackingGoblin afterCombatDamage).size == 1
#guard (changedLifeTotals attackingGoblin afterCombatDamage).any (fun pl =>
  pl.id == ⟨1⟩ && pl.life == 19)
#guard lifeLine (afterCombatDamage.player ⟨1⟩) == "Nissa — life 19"
#guard (changedZones attackingGoblin afterCombatDamage).isEmpty

#guard mentions (header proposedBolt) "choose targets (CR 601.2c"
#guard mentions (header targetedBolt) "activate mana abilities (CR 601.2g)"
#guard (changedZones boltSetup proposedBolt).contains (.hand ⟨0⟩)
#guard (changedZones boltSetup proposedBolt).contains .stack
#guard !mentions (header paidBolt) "activate mana abilities"

-- The demo names the attacker a blocker is assigned to (CR 509.1a).
#guard
  let g := bearsBlockOgre
  let bears := namedPermanent g "Grizzly Bears"
  let ogre := namedPermanent g "Gray Ogre"
  objectLine g bears ==
    s!"{bears.id} Grizzly Bears {bears.power}/{bears.toughness} (owned by Nissa, controlled by Nissa) *blocking {ogre.id} Gray Ogre*" &&
  mentions (playerBlock g (g.player ⟨1⟩)) s!"*blocking {ogre.id} Gray Ogre*" &&
  mentions (zoneBlock g .battlefield) s!"*blocking {ogre.id} Gray Ogre*" &&
  mentions (objectLine g ogre) "*attacking, blocked*"
#guard !mentions
  (objectLine readyToDeclareBlockers (namedPermanent readyToDeclareBlockers "Grizzly Bears"))
  "*blocking"

#guard
  let g := goblinBlockedByBears
  let goblin := namedPermanent g "Battle-Scarred Goblin"
  mentions (objectLine g goblin) "*attacking, blocked*" &&
    !mentions (objectLine goblinDeclaredAttacker (namedPermanent goblinDeclaredAttacker
      "Battle-Scarred Goblin")) "*blocked"

#guard (changedManaPools started started).isEmpty
#guard (changedManaPools started afterDraw).isEmpty
#guard manaLine (started.player ⟨0⟩) == "Chandra — mana {}"
#guard manaLine (started.player ⟨1⟩) == "Nissa — mana {}"
#guard mentions (playerBlock tappedMountain (tappedMountain.player ⟨0⟩)) "mana {R}×1"

-- Paying a mana cost (CR 601.2h) spends the pool; the demo reprints the new
-- contents.
#guard (changedManaPools proposedBolt tappedForBolt).size == 1
#guard manaLine (tappedForBolt.player ⟨0⟩) == "Chandra — mana {R}×1"
#guard (changedManaPools tappedForBolt paidBolt).size == 1
#guard (changedManaPools tappedForBolt paidBolt).any (fun pl =>
  pl.id == ⟨0⟩ && pl.manaPool.isEmpty)
#guard manaLine (paidBolt.player ⟨0⟩) == "Chandra — mana {}"

#guard (changedManaPools tappedMountain emptiedPool).size == 1
#guard (changedManaPools tappedMountain emptiedPool).any (fun pl =>
  pl.id == ⟨0⟩ && pl.manaPool.isEmpty)
#guard manaLine (emptiedPool.player ⟨0⟩) == "Chandra — mana {}"

#guard mentions (header afterChandraMulligan) "on the bottom"
#guard (changedZones afterChandraMulligan afterChandraBottoms).contains (.hand ⟨0⟩)
#guard (changedZones afterChandraMulligan afterChandraBottoms).contains (.library ⟨0⟩)
#guard mentions (header drawnHands) "CR 103.5"

#guard (changedZones baubleReady proposedBauble).contains .stack
#guard mentions (stackBlock proposedBauble) "Search your library"
#guard mentions (zoneBlock proposedBauble .stack) "Search your library"

#guard (changedZones tappedTwiceForBauble paidBauble).contains .battlefield
#guard (changedZones tappedTwiceForBauble paidBauble).contains (.graveyard ⟨0⟩)
#guard (paidBauble.player ⟨0⟩).graveyard.any (fun id =>
  mentions (zoneLine paidBauble (.graveyard ⟨0⟩) id) "Search your library")

#guard (changedZones paidBauble resolvedBauble).contains .battlefield
#guard (changedZones paidBauble resolvedBauble).contains (.library ⟨0⟩)

#guard mentions (header paidHunter) "sacrifice a creature or artifact"
#guard (changedZones hunterReady activatedHunter).contains .stack
#guard (changedZones hunterReady activatedHunter).contains .battlefield
#guard (changedZones hunterReady activatedHunter).contains (.graveyard ⟨0⟩)

#guard (changedZones activatedHunter resolvedHunter).contains .exile
#guard (changedZones activatedHunter resolvedHunter).contains (.library ⟨0⟩)
#guard mentions (snapshot resolvedHunter) "may be played by Chandra"
#guard mentions (zoneBlock resolvedHunter .exile) "may be played by Chandra"

-- Granted trample shows on other Orcs and Goblins you control, not on others.
#guard mentions
  (objectLine siegeAndGoblin (namedPermanent siegeAndGoblin "Raging Goblin")) "trample"
#guard !mentions (objectLine withGoblin (lastPermanent withGoblin)) "trample"
#guard !mentions
  (objectLine siegeAndOgre (namedPermanent siegeAndOgre "Gray Ogre")) "trample"
#guard !mentions
  (objectLine siegeAndOppGoblin (namedPermanent siegeAndOppGoblin "Raging Goblin"))
  "trample"
#guard mentions (stackBlock siegeAttackDeclared) "Orcish Siegemaster's ability"
#guard
  let g := siegeAttackDeclared
  let siege := namedPermanent g "Orcish Siegemaster"
  mentions (stackBlock g) s!"*source {siege.id} Orcish Siegemaster*" &&
    mentions (zoneBlock g .stack) s!"*source {siege.id} Orcish Siegemaster*" &&
    mentions (snapshot g) s!"*source {siege.id} Orcish Siegemaster*"
#guard mentions (objectLine siegePumpResolved
  (namedPermanent siegePumpResolved "Orcish Siegemaster")) "3/5"

#guard
  let g := proposedBauble
  let bauble := baubleSource g
  mentions (stackBlock g) s!"*source {bauble.id} Wayfarer's Bauble*" &&
    mentions (zoneBlock g .stack) s!"*source {bauble.id} Wayfarer's Bauble*"
#guard
  let g := activatedHunter
  let hunter := hunterSource g
  mentions (stackBlock g) s!"*source {hunter.id} Snowslope Hunter*" &&
    mentions (zoneBlock g .stack) s!"*source {hunter.id} Snowslope Hunter*"
#guard
  let g := goblinBlockedByBears
  let goblin := namedPermanent g "Battle-Scarred Goblin"
  mentions (stackBlock g) s!"*source {goblin.id} Battle-Scarred Goblin*"
#guard
  let g := twoGoblinsOneBlocked
  let blocked :=
    (g.battlefield.filter (fun o => o.name == "Battle-Scarred Goblin" && o.status.blocked))[0]!
  let unblocked :=
    (g.battlefield.filter (fun o =>
      o.name == "Battle-Scarred Goblin" && o.status.attacking && !o.status.blocked))[0]!
  mentions (stackBlock g) s!"*source {blocked.id} Battle-Scarred Goblin*" &&
    !mentions (stackBlock g) s!"*source {unblocked.id} Battle-Scarred Goblin*"
-- Spells on the stack have no ability source.
#guard !mentions (stackBlock proposedBolt) "*source"
#guard !mentions (stackBlock targetedBolt) "*source"
#guard !mentions (zoneBlock targetedBolt .stack) "*source"
-- If the source has left play, print the last-known id (CR 113.7a / 400.7).
#guard
  let g0 := siegeAttackDeclared
  let id := (namedPermanent g0 "Orcish Siegemaster").id
  let (g, _) := g0.move id (.graveyard (g0.object! id).owner) none
  mentions (stackBlock g) s!"*source {id}*" &&
    !mentions (stackBlock g) s!"*source {id} Orcish Siegemaster*"

#guard
  let g := giftEntered
  let bears := namedPermanent g "Grizzly Bears"
  let aura := namedPermanent g "Gift of Strands"
  objectLine g bears ==
    s!"{bears.id} Grizzly Bears 5/5 (owned by Chandra, controlled by Chandra)" &&
  mentions (objectLine g aura) s!"*enchanting {bears.id} Grizzly Bears*" &&
  mentions (header giftScrying) "scry 2" &&
  mentions (snapshot giftScrying) "Scry (top last):"

#guard mentions (header proposedCratermaker) "choose a mode (CR 601.2b"
#guard mentions (header cratermakerModeChosen) "choose targets (CR 601.2c"
#guard (changedZones cratermakerTargeted paidCratermaker).contains .battlefield
#guard (changedZones cratermakerTargeted paidCratermaker).contains (.graveyard ⟨0⟩)
#guard (changedZones paidCratermaker resolvedCratermaker).contains (.graveyard ⟨1⟩)
#guard
  let g := paidCratermaker
  let srcId := (g.object! g.stack.back!.objectId).sourceId
  match srcId with
  | some id => mentions (stackBlock g) s!"*source {id}*"
  | none => false

end Mtg.Demo.RenderTests
