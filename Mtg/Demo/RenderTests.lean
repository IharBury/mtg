import Mtg.Engine.Tests
import Mtg.Demo.Render

/-!
# Compile-time tests for console rendering.
-/

namespace Mtg.Demo.RenderTests

open Mtg.Engine
open Mtg.Engine.Catalog
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
#guard mentions (objectLine withCrusher (lastPermanent withCrusher)) "trample"
#guard mentions (objectLine withCrusher (lastPermanent withCrusher)) "can't block unless"

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
#guard pendingCostLine proposedBolt == none
#guard pendingCostNotation targetedBolt == some "{R}"
#guard pendingCostLine targetedBolt == some "Cost: {R}"
#guard mentions (header targetedBolt) "cost {R}"
#guard mentions (snapshot targetedBolt) "Cost: {R}"
#guard pendingCostLine tappedForBolt == some "Cost: {R}"
#guard (changedZones boltSetup proposedBolt).contains (.hand ⟨0⟩)
#guard (changedZones boltSetup proposedBolt).contains .stack
#guard mentions (stackBlock proposedBolt) "deals 3 damage"
#guard !mentions (header paidBolt) "activate mana abilities"
#guard pendingCostLine paidBolt == none
#guard !mentions (snapshot paidBolt) "Cost: {R}"

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

#guard mentions (header giantReadyToAssign) "assign combat damage (CR 510.1c"
#guard mentions (header bearsBlockingTwoOgresReady) "assign combat damage (CR 510.1d"

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
#guard pendingCostNotation proposedBauble == some "{2}, {T}, Sacrifice"
#guard pendingCostLine proposedBauble == some "Cost: {2}, {T}, Sacrifice"
#guard mentions (header proposedBauble) "cost {2}, {T}, Sacrifice"
#guard mentions (snapshot proposedBauble) "Cost: {2}, {T}, Sacrifice"
#guard pendingCostLine tappedTwiceForBauble == some "Cost: {2}, {T}, Sacrifice"
#guard pendingCostLine paidBauble == none

/- Stacked abilities from a multi-ability card omit sibling Oracle lines. -/
#guard
  let c : CardDef := {
    name := "Silent Siege"
    types := #[.creature]
    oracleText := "Trample\nOther Orcs and Goblins you control have trample.\nWhenever this creature attacks, it gets +X/+0 until end of turn, where X is the greatest power among creatures you control."
    keywords := { Keywords.none with trample := true }
    staticAbilities := #[.otherCreaturesHaveTrample #["Orc", "Goblin"]]
    triggeredAbilities := #[.onAttackPumpByGreatestPower]
  }
  let t := TriggeredAbility.toNotation .onAttackPumpByGreatestPower
  textForStackedAbility c t == t &&
    !mentions (textForStackedAbility c t) "Other Orcs and Goblins"

/- A card with a single leftover Oracle ability keeps that printed wording. -/
#guard
  let c : CardDef := {
    name := "Silent Bauble"
    types := #[.artifact]
    oracleText := "{2}, {T}, Sacrifice this artifact: Search your library for a basic land card, put that card onto the battlefield tapped, then shuffle."
  }
  textForStackedAbility c (AbilityEffect.toNotation .searchBasicLandTapped) ==
    c.oracleText

#guard (changedZones tappedTwiceForBauble paidBauble).contains .battlefield
#guard (changedZones tappedTwiceForBauble paidBauble).contains (.graveyard ⟨0⟩)
#guard (paidBauble.player ⟨0⟩).graveyard.any (fun id =>
  mentions (zoneLine paidBauble (.graveyard ⟨0⟩) id) "Search your library")

#guard (changedZones paidBauble resolvedBauble).contains .battlefield
#guard (changedZones paidBauble resolvedBauble).contains (.library ⟨0⟩)

#guard mentions (header paidHunter) "sacrifice a creature or artifact"
#guard pendingCostNotation proposedHunter == some "Sacrifice another creature or artifact"
#guard pendingCostLine proposedHunter == some "Cost: Sacrifice another creature or artifact"
#guard mentions (header proposedHunter) "cost Sacrifice another creature or artifact"
#guard pendingCostLine paidHunter == none
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
#guard mentions (stackBlock siegeAttackDeclared) "Whenever this creature attacks"
#guard mentions (zoneBlock siegeAttackDeclared .stack) "Whenever this creature attacks"
#guard !mentions (stackBlock siegeAttackDeclared) "Other Orcs and Goblins"
#guard !mentions (zoneBlock siegeAttackDeclared .stack) "Other Orcs and Goblins"
#guard !mentions (stackBlock siegeAttackDeclared) "trample"
#guard !mentions (stackBlock siegeAttackDeclared) "Trample"
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
  mentions (snapshot giftScrying) "Looking at (scry 2, top last):"

#guard
  let g := spearEquipped
  let bears := namedPermanent g "Grizzly Bears"
  let spear := namedPermanent g "Ragged Short Spear"
  objectLine g bears ==
    s!"{bears.id} Grizzly Bears 4/2 (owned by Chandra, controlled by Chandra)" &&
  mentions (objectLine g spear) s!"*equipping {bears.id} Grizzly Bears*" &&
  mentions (header spearMayDiscard) "may discard a card, then draw 2"

#guard
  let g := spearEquipped
  let bears := namedPermanent g "Grizzly Bears"
  let spear := namedPermanent g "Ragged Short Spear"
  let hostLine := objectLine g bears (some (some ⟨0⟩))
  let spearLine := objectLine g spear (some (some ⟨0⟩))
  mentions spearLine "*equipping" &&
    mentions (playerBlock g (g.player ⟨0⟩)) s!"  {hostLine}\n    {spearLine}"

-- Attached permanents print next to their host, with two extra spaces.
#guard
  let g := giftEntered
  let bears := namedPermanent g "Grizzly Bears"
  let aura := namedPermanent g "Gift of Strands"
  let hostLine := objectLine g bears (some (some ⟨0⟩))
  let auraLine := objectLine g aura (some (some ⟨0⟩))
  zoneBlock g .battlefield ==
    s!"zone battlefield (2):\n  Chandra:\n    {hostLine}\n      {auraLine}" &&
  mentions (playerBlock g (g.player ⟨0⟩)) s!"  {hostLine}\n    {auraLine}"

-- A later unattached permanent does not sit between a host and its Aura.
#guard
  let g := addPermanent started grizzlyBears ⟨0⟩ ⟨0⟩
  let g := addPermanent g mountain ⟨0⟩ ⟨0⟩
  let g := addAttachedAura g giftOfStrands (namedPermanent g "Grizzly Bears") ⟨0⟩ ⟨0⟩
  let bears := namedPermanent g "Grizzly Bears"
  let land := namedPermanent g "Mountain"
  let aura := namedPermanent g "Gift of Strands"
  let hostLine := objectLine g bears (some (some ⟨0⟩))
  let landLine := objectLine g land (some (some ⟨0⟩))
  let auraLine := objectLine g aura (some (some ⟨0⟩))
  zoneBlock g .battlefield ==
    s!"zone battlefield (3):\n  Chandra:\n    {hostLine}\n      {auraLine}\n    {landLine}" &&
  mentions (playerBlock g (g.player ⟨0⟩)) s!"  {hostLine}\n    {auraLine}\n  {landLine}"

-- An Aura you control on an opponent's creature lists with that host.
#guard
  let g := giftOnNissa
  let bears := namedPermanent g "Grizzly Bears"
  let aura := namedPermanent g "Gift of Strands"
  let hostLine := objectLine g bears (some (some ⟨1⟩))
  let auraLine := objectLine g aura (some (some ⟨1⟩))
  bears.controller == some ⟨1⟩ && aura.controller == some ⟨0⟩ &&
    mentions auraLine "(owned by Chandra, controlled by Chandra)" &&
    zoneBlock g .battlefield ==
      s!"zone battlefield (2):\n  Nissa:\n    {hostLine}\n      {auraLine}" &&
    mentions (playerBlock g (g.player ⟨0⟩)) "  (none)" &&
    mentions (playerBlock g (g.player ⟨1⟩)) s!"  {hostLine}\n    {auraLine}"

-- Other permanents stay in their controller's group when an Aura is elsewhere.
#guard
  let g := addPermanent started mountain ⟨0⟩ ⟨0⟩
  let g := addPermanent g grizzlyBears ⟨1⟩ ⟨1⟩
  let g := addAttachedAura g giftOfStrands (namedPermanent g "Grizzly Bears") ⟨0⟩ ⟨0⟩
  let land := namedPermanent g "Mountain"
  let bears := namedPermanent g "Grizzly Bears"
  let aura := namedPermanent g "Gift of Strands"
  zoneBlock g .battlefield ==
    s!"zone battlefield (3):\n  Chandra:\n    {objectLine g land (some (some ⟨0⟩))}\n  Nissa:\n    {objectLine g bears (some (some ⟨1⟩))}\n      {objectLine g aura (some (some ⟨1⟩))}"

-- Several permanents attached to the same host all indent under it.
#guard
  let g := addPermanent started grizzlyBears ⟨0⟩ ⟨0⟩
  let g := addAttachedAura g giftOfStrands (namedPermanent g "Grizzly Bears") ⟨0⟩ ⟨0⟩
  let g := addAttachedAura g giftOfStrands (namedPermanent g "Grizzly Bears") ⟨0⟩ ⟨0⟩
  let bears := namedPermanent g "Grizzly Bears"
  let auras := g.battlefield.filter (fun o => o.name == "Gift of Strands")
  auras.size == 2 &&
    zoneBlock g .battlefield ==
      s!"zone battlefield (3):\n  Chandra:\n    {objectLine g bears (some (some ⟨0⟩))}\n      {objectLine g auras[0]! (some (some ⟨0⟩))}\n      {objectLine g auras[1]! (some (some ⟨0⟩))}"

-- Unattached permanents under a controller are creatures, then other non-lands,
-- then non-creature lands, regardless of the order they entered.
#guard
  let g := addPermanent started mountain ⟨0⟩ ⟨0⟩
  let g := addPermanent g wayfarersBauble ⟨0⟩ ⟨0⟩
  let g := addPermanent g grizzlyBears ⟨0⟩ ⟨0⟩
  let land := namedPermanent g "Mountain"
  let bauble := namedPermanent g "Wayfarer's Bauble"
  let bears := namedPermanent g "Grizzly Bears"
  let landLine := objectLine g land (some (some ⟨0⟩))
  let baubleLine := objectLine g bauble (some (some ⟨0⟩))
  let hostLine := objectLine g bears (some (some ⟨0⟩))
  zoneBlock g .battlefield ==
    s!"zone battlefield (3):\n  Chandra:\n    {hostLine}\n    {baubleLine}\n    {landLine}" &&
  mentions (playerBlock g (g.player ⟨0⟩)) s!"  {hostLine}\n  {baubleLine}\n  {landLine}"

-- An Aura stays with its creature host; unattached Equipment sits with other
-- non-lands, even if it entered before the creature.
#guard
  let g := addPermanent started mountain ⟨0⟩ ⟨0⟩
  let g := addPermanent g raggedShortSpear ⟨0⟩ ⟨0⟩
  let g := addPermanent g grizzlyBears ⟨0⟩ ⟨0⟩
  let g := addAttachedAura g giftOfStrands (namedPermanent g "Grizzly Bears") ⟨0⟩ ⟨0⟩
  let land := namedPermanent g "Mountain"
  let spear := namedPermanent g "Ragged Short Spear"
  let bears := namedPermanent g "Grizzly Bears"
  let aura := namedPermanent g "Gift of Strands"
  spear.attachedTo.isNone &&
    zoneBlock g .battlefield ==
      s!"zone battlefield (4):\n  Chandra:\n    {objectLine g bears (some (some ⟨0⟩))}\n      {objectLine g aura (some (some ⟨0⟩))}\n    {objectLine g spear (some (some ⟨0⟩))}\n    {objectLine g land (some (some ⟨0⟩))}"

-- A non-creature enchantment sits with other non-lands. After it becomes a
-- creature, it joins the creature subgroup (ahead of a later creature).
#guard
  let g := addPermanent started mountain ⟨0⟩ ⟨0⟩
  let g := addPermanent g beornsHospitality ⟨0⟩ ⟨0⟩
  let g := addPermanent g grizzlyBears ⟨0⟩ ⟨0⟩
  let hosp := namedPermanent g "Beorn's Hospitality"
  let bears := namedPermanent g "Grizzly Bears"
  let land := namedPermanent g "Mountain"
  let g' := g.setObject { hosp with
    status := { hosp.status with
      additionalCreature := true
      additionalSubtypes := #["Bear"] } }
  let hosp' := namedPermanent g' "Beorn's Hospitality"
  !hosp.isCreature && hosp'.isCreature &&
    zoneBlock g .battlefield ==
      s!"zone battlefield (3):\n  Chandra:\n    {objectLine g bears (some (some ⟨0⟩))}\n    {objectLine g hosp (some (some ⟨0⟩))}\n    {objectLine g land (some (some ⟨0⟩))}" &&
    zoneBlock g' .battlefield ==
      s!"zone battlefield (3):\n  Chandra:\n    {objectLine g' hosp' (some (some ⟨0⟩))}\n    {objectLine g' bears (some (some ⟨0⟩))}\n    {objectLine g' land (some (some ⟨0⟩))}"

-- Each controller's subgroups are independent.
#guard
  let g := addPermanent started mountain ⟨0⟩ ⟨0⟩
  let g := addPermanent g grizzlyBears ⟨0⟩ ⟨0⟩
  let g := addPermanent g forest ⟨1⟩ ⟨1⟩
  let g := addPermanent g grayOgre ⟨1⟩ ⟨1⟩
  let land0 := namedPermanent g "Mountain"
  let bears := namedPermanent g "Grizzly Bears"
  let land1 := namedPermanent g "Forest"
  let ogre := namedPermanent g "Gray Ogre"
  zoneBlock g .battlefield ==
    s!"zone battlefield (4):\n  Chandra:\n    {objectLine g bears (some (some ⟨0⟩))}\n    {objectLine g land0 (some (some ⟨0⟩))}\n  Nissa:\n    {objectLine g ogre (some (some ⟨1⟩))}\n    {objectLine g land1 (some (some ⟨1⟩))}"

-- Starting a scry does not move library cards, but the demo reprints that
-- library so the scrying player sees the looked-at faces (CR 701.20).
#guard (zoneObjectIds giftKnownLib (.library ⟨0⟩)) ==
  (zoneObjectIds giftKnownScrying (.library ⟨0⟩))
#guard (changedZones giftKnownLib giftKnownScrying).contains (.library ⟨0⟩)
#guard !(changedZones giftKnownScrying giftKnownScrying).contains (.library ⟨0⟩)
#guard
  let g := giftKnownScrying
  let looked := g.scryLookedIds ⟨0⟩ 2
  match looked[0]?, looked[1]? with
  | some forestId, some elvesId =>
    let forest := (g.object! forestId).name
    let elves := (g.object! elvesId).name
    forest == "Forest" && elves == "Llanowar Elves" &&
      mentions (zoneBlock g (.library ⟨0⟩)) "looking at (top last)" &&
      mentions (zoneBlock g (.library ⟨0⟩)) forest &&
      mentions (zoneBlock g (.library ⟨0⟩)) elves &&
      mentions (zoneBlock g (.library ⟨0⟩)) (toString forestId) &&
      mentions (zoneBlock g (.library ⟨0⟩)) (toString elvesId) &&
      mentions (playerBlock g (g.player ⟨0⟩)) s!"Looking at (scry 2, top last)" &&
      mentions (playerBlock g (g.player ⟨0⟩)) forest &&
      mentions (playerBlock g (g.player ⟨0⟩)) elves &&
      mentions (snapshot g) forest &&
      mentions (snapshot g) elves &&
      match scryLookBlock g with
      | some s => mentions s forest && mentions s elves
      | none => false
  | _, _ => false

-- Other players do not see the scried faces.
#guard
  let g := giftKnownScrying
  let looked := g.scryLookedIds ⟨0⟩ 2
  match looked[0]?, looked[1]? with
  | some forestId, some elvesId =>
    let forest := (g.object! forestId).name
    let elves := (g.object! elvesId).name
    !mentions (zoneBlock g (.library ⟨0⟩) (some ⟨1⟩)) forest &&
      !mentions (zoneBlock g (.library ⟨0⟩) (some ⟨1⟩)) elves &&
      zoneBlock g (.library ⟨0⟩) (some ⟨1⟩) ==
        s!"zone Chandra's library ({(g.player ⟨0⟩).library.size})" &&
      mentions (playerBlock g (g.player ⟨0⟩) (some ⟨1⟩)) "Looking at (scry 2): (hidden)" &&
      !mentions (playerBlock g (g.player ⟨0⟩) (some ⟨1⟩)) forest &&
      mentions (snapshot g (some ⟨1⟩)) "(hidden)" &&
      match scryLookBlock g (some ⟨1⟩) with
      | some s => s == "Chandra is scrying 2"
      | none => false
  | _, _ => false

-- The scrying player in hidden-information view still sees their own look.
#guard
  let g := giftKnownScrying
  let looked := g.scryLookedIds ⟨0⟩ 2
  match looked[0]? with
  | some forestId =>
    mentions (zoneBlock g (.library ⟨0⟩) (some ⟨0⟩)) (g.object! forestId).name &&
      mentions (snapshot g (some ⟨0⟩)) (g.object! forestId).name &&
      mentions (playerBlock g (g.player ⟨0⟩) (some ⟨0⟩)) (g.object! forestId).name
  | none => false

-- Finishing a scry that leaves library order unchanged still reprints the
-- library so the look is no longer shown.
#guard
  let before := giftScrying
  let after := giftScried
  scryLook before ⟨0⟩ != scryLook after ⟨0⟩ &&
    (changedZones before after).contains (.library ⟨0⟩) &&
    !mentions (zoneBlock after (.library ⟨0⟩)) "looking at"

#guard mentions (stackBlock guideEntered) "Galadhrim Guide's ability"
#guard mentions (stackBlock guideEntered) "When this creature enters, scry 2"
#guard !mentions (stackBlock guideEntered) "When this permanent enters"
#guard
  let g := guideEntered
  let guide := namedPermanent g "Galadhrim Guide"
  mentions (stackBlock g) s!"*source {guide.id} Galadhrim Guide*" &&
    mentions (zoneBlock g .stack) s!"*source {guide.id} Galadhrim Guide*" &&
    mentions (objectLine g guide) "3/4"
#guard mentions (header guideScrying) "scry 2"
#guard mentions (snapshot guideScrying) "Looking at (scry 2, top last):"
#guard
  let g := guideKnownScrying
  let looked := g.scryLookedIds ⟨0⟩ 2
  match looked[0]?, looked[1]? with
  | some forestId, some elvesId =>
    mentions (zoneBlock g (.library ⟨0⟩)) "looking at (top last)" &&
      mentions (zoneBlock g (.library ⟨0⟩)) "Forest" &&
      mentions (zoneBlock g (.library ⟨0⟩)) "Llanowar Elves" &&
      mentions (zoneBlock g (.library ⟨0⟩)) (toString forestId) &&
      mentions (zoneBlock g (.library ⟨0⟩)) (toString elvesId)
  | _, _ => false

#guard mentions (header proposedCratermaker) "choose a mode (CR 601.2b"
#guard mentions (header cratermakerModeChosen) "choose targets (CR 601.2c"
#guard pendingCostNotation cratermakerTargeted == some "{1}, Sacrifice"
#guard pendingCostLine cratermakerTargeted == some "Cost: {1}, Sacrifice"
#guard mentions (header cratermakerTargeted) "cost {1}, Sacrifice"
#guard (changedZones cratermakerTargeted paidCratermaker).contains .battlefield
#guard (changedZones cratermakerTargeted paidCratermaker).contains (.graveyard ⟨0⟩)
#guard (changedZones paidCratermaker resolvedCratermaker).contains (.graveyard ⟨1⟩)
#guard
  let g := paidCratermaker
  let srcId := (g.object! g.stack.back!.objectId).sourceId
  match srcId with
  | some id => mentions (stackBlock g) s!"*source {id}*"
  | none => false

#guard mentions (header proposedWarg) "choose a mode (CR 601.2b"
#guard mentions (header wargModeDestroy) "choose targets (CR 601.2c"
#guard
  let g := resolvedWargPump
  let bears := namedPermanent g "Grizzly Bears"
  mentions (objectLine g bears) "3/3" &&
    mentions (objectLine g bears) "+1/+1×1" &&
    mentions (objectLine g bears) "trample" &&
    mentions (objectLine g bears) "hexproof"
#guard
  let g := afterWargPumpCleanup
  let bears := namedPermanent g "Grizzly Bears"
  mentions (objectLine g bears) "3/3" &&
    mentions (objectLine g bears) "+1/+1×1" &&
    !mentions (objectLine g bears) "hexproof" &&
    !mentions (objectLine g bears) "trample"

#guard pendingCostNotation proposedHospitalityAnimate == some "{5}{G}{G}"
#guard pendingCostLine proposedHospitalityAnimate == some "Cost: {5}{G}{G}"
#guard mentions (header proposedHospitalityAnimate) "cost {5}{G}{G}"
#guard pendingCostNotation targetedEquip == some "{3}"
#guard pendingCostLine targetedEquip == some "Cost: {3}"

#guard mentions (header hospitalityLandPlayed) "choose targets (CR 601.2c"
#guard mentions (stackBlock hospitalityLandPlayed) "Beorn's Hospitality's ability"
#guard mentions (stackBlock hospitalityLandPlayed) "Whenever a land you control enters"
#guard !mentions (stackBlock hospitalityLandPlayed) "{5}{G}{G}"
#guard
  let g := hospitalityLandPlayed
  let src := namedPermanent g "Beorn's Hospitality"
  mentions (stackBlock g) s!"*source {src.id} Beorn's Hospitality*"
#guard
  let g := animatedHospitality
  let o := namedPermanent g "Beorn's Hospitality"
  mentions (objectLine g o) "Enchantment Creature" &&
    mentions (objectLine g o) "Bear" &&
    mentions (objectLine g o) "3/3"
#guard
  let g := hospitalityLandfallResolved
  let bears := namedPermanent g "Grizzly Bears"
  mentions (objectLine g bears) "3/3" &&
    mentions (objectLine g bears) "+1/+1×1"
#guard
  let g := pathmakerWithLands
  let o := namedPermanent g "Mirkwood Pathmaker"
  mentions (objectLine g o) "2/2"

#guard mentions (header gandalfEntered) "choose targets (CR 601.2c"
#guard mentions (stackBlock gandalfEntered) "Gandalf, Spark Starter's ability"
#guard mentions (stackBlock gandalfEntered) "divided as you choose"
#guard mentions (stackBlock gandalfEntered) "When Gandalf enters"
#guard !mentions (stackBlock gandalfEntered) "When this permanent enters"
#guard
  let g := gandalfEntered
  let src := namedPermanent g "Gandalf, Spark Starter"
  mentions (stackBlock g) s!"*source {src.id} Gandalf, Spark Starter*" &&
    mentions (objectLine g src) "reach" &&
    mentions (objectLine g src) "4/3"
#guard mentions (objectLine flyerVsGandalf
  (namedPermanent flyerVsGandalf "Gandalf, Spark Starter")) "reach"

#guard mentions (header galionAttackDeclared) "choose targets (CR 601.2c"
#guard mentions (stackBlock galionAttackDeclared) "Galion, Elvenking's Butler's ability"
#guard mentions (stackBlock galionAttackDeclared) "base power and toughness"
#guard
  let g := galionAttackDeclared
  let src := namedPermanent g "Galion, Elvenking's Butler"
  mentions (stackBlock g) s!"*source {src.id} Galion, Elvenking's Butler*" &&
    mentions (objectLine g src) "4/4"
#guard
  let g := galionResolved
  let elves := namedPermanent g "Llanowar Elves"
  mentions (objectLine g elves) "4/4"

end Mtg.Demo.RenderTests
