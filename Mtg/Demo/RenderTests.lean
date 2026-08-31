import Mtg.Engine.OracleRulings
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
#guard mentions (playerBlock started (started.player ⟨0⟩)) "Graveyard (0):"
#guard mentions (playerBlock started (started.player ⟨0⟩)) "  (empty)"
#guard !mentions (playerBlock started (started.player ⟨0⟩)) "Battlefield"
#guard !mentions (playerBlock started (started.player ⟨1⟩)) "Battlefield"
#guard battlefieldBlock started == "Battlefield (0): (empty)"
#guard mentions (snapshot started) (battlefieldBlock started)
#guard ((snapshot started).splitOn "Battlefield").length == 2

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
  s!"{(lastPermanent withMountain).id} Mountain {(lastPermanent withMountain).typeLine} (\{T}: Add \{R}.) (owned by Chandra, controlled by Chandra)"
#guard mentions (mountainLine withMountain) "Land"
#guard mentions (mountainLine withMountain) "{T}: Add {R}"
-- Hands print the card summary; lands have no mana cost, so not `{0}`.
#guard
  match (started.handObjects ⟨0⟩).find? (·.printed.isLand) with
  | some o =>
    let line := handLine started o.id
    mentions line o.name &&
      mentions line "Basic Land" &&
      !mentions line "{0}"
  | none => false
#guard mentions (handLine boltSetup boltInHand.id) "{R}"
#guard mentions (handLine boltSetup boltInHand.id) "Lightning Bolt"
-- Graveyard and exile print the same Oracle face as hand: mana cost, type
-- line, and creature P/T (not only name and abilities).
#guard
  let g := addToGraveyard started llanowarElves ⟨0⟩
  let elf := namedGraveyardCard g ⟨0⟩ "Llanowar Elves"
  let line := printedCardLine elf
  mentions line "{G}" &&
    mentions line "Creature — Elf Druid" &&
    mentions line "1/1" &&
    zoneLine g (.graveyard ⟨0⟩) elf.id == line &&
    mentions (playerBlock g (g.player ⟨0⟩)) line &&
    mentions (zoneBlock g (.graveyard ⟨0⟩)) line
#guard
  let g := addToGraveyard started lightningBolt ⟨0⟩
  let bolt := namedGraveyardCard g ⟨0⟩ "Lightning Bolt"
  let line := zoneLine g (.graveyard ⟨0⟩) bolt.id
  mentions line "{R}" && mentions line "Instant" &&
    mentions (playerBlock g (g.player ⟨0⟩)) line
#guard
  let g := addToGraveyard started mountain ⟨0⟩
  let land := namedGraveyardCard g ⟨0⟩ "Mountain"
  let line := zoneLine g (.graveyard ⟨0⟩) land.id
  mentions line "Basic Land — Mountain" && !mentions line "{0}"
#guard
  let g := insertObject started grizzlyBears ⟨0⟩ .exile
  match g.objects.find? (fun o => o.zone == .exile && o.name == "Grizzly Bears") with
  | none => false
  | some bears =>
    let line := exileLine g bears
    mentions line "{1}{G}" &&
      mentions line "Creature — Bear" &&
      mentions line "2/2" &&
      zoneLine g .exile bears.id == line &&
      mentions (zoneBlock g .exile) line &&
      mentions (snapshot g) line
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

/- Summoning sickness (CR 302.6) prints on battlefield creatures, like tapped. -/
#guard
  let g := insertObject started llanowarElves ⟨0⟩ .battlefield (some ⟨0⟩)
  let o := lastPermanent g
  o.hasSummoningSickness &&
    mentions (objectLine g o) "(summoning sickness)" &&
    mentions (zoneBlock g .battlefield) "(summoning sickness)" &&
    mentions (battlefieldBlock g) "(summoning sickness)" &&
    mentions (snapshot g) "(summoning sickness)"

-- A creature that has been under control since the turn began does not print it.
#guard !mentions (objectLine withElves (lastPermanent withElves)) "(summoning sickness)"
#guard !mentions (playerBlock withElves (withElves.player ⟨0⟩)) "(summoning sickness)"

-- Haste overrides the restriction, so a newly entered Goblin does not print it.
#guard
  let g := insertObject started ragingGoblin ⟨0⟩ .battlefield (some ⟨0⟩)
  let o := lastPermanent g
  o.status.summoningSick &&
    !o.hasSummoningSickness &&
    mentions (objectLine g o) "haste" &&
    !mentions (objectLine g o) "(summoning sickness)"

-- Non-creatures never print it, even if the status flag is set.
#guard
  let g := insertObject started mountain ⟨0⟩ .battlefield (some ⟨0⟩)
  let o := lastPermanent g
  o.status.summoningSick &&
    !o.isCreature &&
    !mentions (objectLine g o) "(summoning sickness)"

-- Tapped and summoning-sick print as adjacent status markers.
#guard
  let g := insertObject started llanowarElves ⟨0⟩ .battlefield (some ⟨0⟩)
    { tapped := true, summoningSick := true }
  let line := objectLine g (lastPermanent g)
  mentions line "(tapped)" && mentions line "(summoning sickness)" &&
    mentions line "(tapped) (summoning sickness)"

-- Untap clears sickness; occupants stay put, but the battlefield reprints.
#guard
  let before := insertObject started llanowarElves ⟨0⟩ .battlefield (some ⟨0⟩)
  let after := before.beginStep .untap
  let o := lastPermanent after
  (zoneObjectIds before .battlefield) == (zoneObjectIds after .battlefield) &&
    battlefieldView before != battlefieldView after &&
    (changedZones before after).contains .battlefield &&
    !o.hasSummoningSickness &&
    !mentions (objectLine after o) "(summoning sickness)"

-- A creature that entered this turn via the stack prints the marker.
#guard
  let g := pathmakerEntered
  let o := namedPermanent g "Mirkwood Pathmaker"
  o.hasSummoningSickness &&
    mentions (objectLine g o) "(summoning sickness)" &&
    mentions (zoneBlock g .battlefield) "(summoning sickness)"

-- An enchantment that became a creature the turn it entered is also sick.
#guard
  let g := hospitalityEnteredThisTurn
  let o := namedPermanent g "Beorn's Hospitality"
  o.isCreature && o.hasSummoningSickness &&
    mentions (objectLine g o) "(summoning sickness)"

-- The same animation after the permanent has already been in play is not sick.
#guard
  let g := animatedHospitality
  let o := namedPermanent g "Beorn's Hospitality"
  o.isCreature && !o.hasSummoningSickness &&
    !mentions (objectLine g o) "(summoning sickness)"

-- Stack objects are not battlefield creatures; they do not print the marker.
#guard mentions
  (objectLine guideEntered (namedPermanent guideEntered "Galadhrim Guide"))
  "(summoning sickness)"
#guard !mentions (stackBlock guideEntered) "(summoning sickness)"

#guard mountainLine stolenMountain ==
  s!"{(lastPermanent stolenMountain).id} Mountain {(lastPermanent stolenMountain).typeLine} (\{T}: Add \{R}.) (owned by Chandra, controlled by Nissa)"
-- Grouped under Nissa: owner differs, so it is printed; controller matches.
-- The shared battlefield is not listed under either player block.
#guard !mentions (playerBlock stolenMountain (stolenMountain.player ⟨0⟩)) "Battlefield"
#guard !mentions (playerBlock stolenMountain (stolenMountain.player ⟨1⟩)) "Battlefield"
#guard mentions (zoneBlock stolenMountain .battlefield)
  "(owned by Chandra)"
#guard !mentions (zoneBlock stolenMountain .battlefield) "controlled by"
#guard mentions (battlefieldBlock stolenMountain) "(owned by Chandra)"
#guard !mentions (battlefieldBlock stolenMountain) "controlled by"
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
#guard battlefieldBlock started == "Battlefield (0): (empty)"

#guard
  let m := lastPermanent withMountain
  let grouped :=
    s!"Chandra:\n    {objectLine withMountain m (some (some ⟨0⟩))}"
  zoneBlock withMountain .battlefield == s!"zone battlefield (1):\n  {grouped}" &&
    battlefieldBlock withMountain == s!"Battlefield (1):\n  {grouped}" &&
    mentions (snapshot withMountain) (battlefieldBlock withMountain) &&
    ((snapshot withMountain).splitOn "Battlefield").length == 2 &&
    !mentions (playerBlock withMountain (withMountain.player ⟨0⟩)) "Battlefield"

#guard
  let m := lastPermanent stolenMountain
  let grouped :=
    s!"Nissa:\n    {objectLine stolenMountain m (some (some ⟨1⟩))}"
  zoneBlock stolenMountain .battlefield == s!"zone battlefield (1):\n  {grouped}" &&
    battlefieldBlock stolenMountain == s!"Battlefield (1):\n  {grouped}"

#guard
  let forestP := (mixedControllers.permanentsOf ⟨0⟩)[0]!
  let mountainP := (mixedControllers.permanentsOf ⟨1⟩)[0]!
  let grouped :=
    s!"Chandra:\n    {objectLine mixedControllers forestP (some (some ⟨0⟩))}\n  Nissa:\n    {objectLine mixedControllers mountainP (some (some ⟨1⟩))}"
  forestP.name == "Forest" && mountainP.name == "Mountain" &&
    zoneBlock mixedControllers .battlefield == s!"zone battlefield (2):\n  {grouped}" &&
    battlefieldBlock mixedControllers == s!"Battlefield (2):\n  {grouped}" &&
    mentions (snapshot mixedControllers) (battlefieldBlock mixedControllers) &&
    ((snapshot mixedControllers).splitOn "Battlefield").length == 2

#guard
  let m := lastPermanent uncontrolledPermanent
  let grouped :=
    s!"(no controller):\n    {objectLine uncontrolledPermanent m (some none)}"
  zoneBlock uncontrolledPermanent .battlefield == s!"zone battlefield (1):\n  {grouped}" &&
    battlefieldBlock uncontrolledPermanent == s!"Battlefield (1):\n  {grouped}"

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
#guard mentions (battlefieldBlock withGoblin) "haste"
#guard mentions (snapshot withGoblin) "haste"
#guard mentions (objectLine withElves (lastPermanent withElves)) "{T}: Add {G}"
#guard mentions (objectLine withSpider (lastPermanent withSpider)) "reach"
#guard mentions (objectLine withAttercop (lastPermanent withAttercop)) "deathtouch"
#guard mentions (objectLine withAttercop (lastPermanent withAttercop)) "Landfall"
#guard mentions (zoneLine withAttercop .battlefield (lastPermanent withAttercop).id)
  "Landfall"
#guard mentions (objectLine withWarg (lastPermanent withWarg)) "deathtouch"
#guard mentions (objectLine withWarg (lastPermanent withWarg)) "Ferocious"
#guard mentions (objectLine withWarg (lastPermanent withWarg)) "gain 2 life"
#guard mentions (objectLine withGollum (lastPermanent withGollum)) "menace"
#guard !mentions (objectLine withGollum (lastPermanent withGollum)) "can't be blocked except"
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
#guard mentions (stackBlock proposedBolt) (toString proposedBolt.stack.back!.objectId)
#guard mentions (snapshot proposedBolt) (toString proposedBolt.stack.back!.objectId)
#guard !mentions (stackBlock proposedBolt) "*targeting"
#guard !mentions (stackBlock proposedBolt) "*no target"
#guard mentions (stackBlock targetedBolt) "*targeting Nissa*"
#guard mentions (zoneBlock targetedBolt .stack) "*targeting Nissa*"
#guard mentions (snapshot targetedBolt) "*targeting Nissa*"
#guard mentions (stackBlock paidBolt) "*targeting Nissa*"
#guard (zoneObjectIds proposedBolt .stack) == (zoneObjectIds targetedBolt .stack)
#guard stackView proposedBolt != stackView targetedBolt
#guard (changedZones proposedBolt targetedBolt).contains .stack
#guard !(changedZones targetedBolt targetedBolt).contains .stack
#guard !mentions (header paidBolt) "activate mana abilities"
#guard pendingCostLine paidBolt == none
#guard !mentions (snapshot paidBolt) "Cost: {R}"

-- The demo names the attacker a blocker is assigned to (CR 509.1a).
#guard
  let g := bearsBlockOgre
  let bears := namedPermanent g "Grizzly Bears"
  let ogre := namedPermanent g "Gray Ogre"
  objectLine g bears ==
    s!"{bears.id} Grizzly Bears {bears.typeLine} {bears.power}/{bears.toughness} (owned by Nissa, controlled by Nissa) *blocking {ogre.id} Gray Ogre*" &&
  mentions (zoneBlock g .battlefield) s!"*blocking {ogre.id} Gray Ogre*" &&
  mentions (battlefieldBlock g) s!"*blocking {ogre.id} Gray Ogre*" &&
  mentions (snapshot g) s!"*blocking {ogre.id} Gray Ogre*" &&
  mentions (objectLine g ogre) "*attacking Nissa, blocked*"
#guard !mentions
  (objectLine readyToDeclareBlockers (namedPermanent readyToDeclareBlockers "Grizzly Bears"))
  "*blocking"

#guard mentions (header giantReadyToAssign) "assign combat damage (CR 510.1c"
#guard mentions (header bearsBlockingTwoOgresReady) "assign combat damage (CR 510.1d"
#guard mentions (header twoBofursSBA) "legend rule"
#guard mentions (header twoBofursSBA) "704.5j"
#guard mentions (header twoBofursSBA) "Bofur, Reliable Guardian"
#guard
  match legendRuleBlock twoBofursSBA with
  | some s => mentions s "Bofur, Reliable Guardian" && mentions s "704.5j"
  | none => false
#guard mentions (snapshot twoBofursSBA) "chooses which Bofur, Reliable Guardian to keep"
#guard mentions (header twoAttercopsLandPending) "choose trigger order (CR 603.3b"
#guard mentions (header twoAttercopsLandPending) "Chandra"
#guard
  let wts := twoAttercopsLandPending.waitingTriggersOf ⟨0⟩
  wts.size == 2 &&
    waitingTriggerLine wts[0]! ==
      s!"{wts[0]!.source.id} Attercop Landfall — Whenever a land you control enters, this creature gets +1/+1 until end of turn."
#guard
  match triggerOrderBlock twoAttercopsLandPending with
  | some s =>
    let ids := twoAttercopsLandPending.defaultTriggerSourceIds ⟨0⟩
    mentions s "Attercop" && mentions s "CR 603.3b" && mentions s "Landfall" &&
      mentions s "Whenever a land you control enters" &&
      mentions s "+1/+1 until end of turn" &&
      mentions s (toString ids[0]!) && mentions s (toString ids[1]!)
  | none => false
#guard mentions (snapshot twoAttercopsLandPending)
  "chooses the order of triggered abilities (CR 603.3b)"
#guard
  let ids := twoAttercopsLandPending.defaultTriggerSourceIds ⟨0⟩
  mentions (snapshot twoAttercopsLandPending) (toString ids[0]!) &&
    mentions (snapshot twoAttercopsLandPending) "Whenever a land you control enters"
#guard (triggerOrderBlock attercopLandPlayed).isNone
#guard
  let g := addPermanent afterDraw attercop ⟨0⟩ ⟨0⟩
  let g := addPermanent g beornsHospitality ⟨0⟩ ⟨0⟩
  let g := addToHand g forest ⟨0⟩
  let g := mustApply g ⟨0⟩ (.playLand (handCardNamed g ⟨0⟩ "Forest").id)
  match triggerOrderBlock g with
  | some s =>
    mentions s "Attercop" && mentions s "Beorn's Hospitality" &&
      mentions s "this creature gets +1/+1 until end of turn" &&
      mentions s "put a +1/+1 counter on target creature you control"
  | none => false
#guard
  let g := giantReadyToAssign
  let giant := namedPermanent g "Hill Giant"
  let elves := g.battlefield.filter (fun o => o.name == "Llanowar Elves")
  let line := combatDamageSourceLine g giant true
  let block := combatDamageAssignmentBlock g
  line ==
    s!"{giant.id} Hill Giant assigns 3; legal: {elves[0]!.id} Llanowar Elves, {elves[1]!.id} Llanowar Elves" &&
    block == some (s!"Assign combat damage:\n  {line}") &&
    mentions (snapshot g) "Assign combat damage:" &&
    mentions (snapshot g) "Hill Giant assigns 3" &&
    mentions (snapshot g) (toString elves[0]!.id) &&
    mentions (snapshot g) (toString elves[1]!.id)
#guard
  let g := giantReadyToAssign
  let giant := namedPermanent g "Hill Giant"
  let g := g.setObject { giant with status := giant.status.grantUntilEot Keyword.trample }
  let giant := namedPermanent g "Hill Giant"
  let elves := g.battlefield.filter (fun o => o.name == "Llanowar Elves")
  combatDamageSourceLine g giant true ==
    s!"{giant.id} Hill Giant assigns 3; legal: {elves[0]!.id} Llanowar Elves, {elves[1]!.id} Llanowar Elves, Nissa"
#guard
  let g := bearsBlockingTwoOgresReady
  let bears := namedPermanent g "Grizzly Bears"
  let ogres := g.battlefield.filter (fun o => o.name == "Gray Ogre")
  let line := combatDamageSourceLine g bears false
  line ==
    s!"{bears.id} Grizzly Bears assigns 2; legal: {ogres[0]!.id} Gray Ogre, {ogres[1]!.id} Gray Ogre" &&
    combatDamageAssignmentBlock g == some (s!"Assign combat damage:\n  {line}") &&
    mentions (snapshot g) "Grizzly Bears assigns 2"
#guard (combatDamageAssignmentBlock readyToDeclareBlockers).isNone
#guard !mentions (snapshot readyToDeclareBlockers) "Assign combat damage:"
#guard
  let g := giantReadyToAssign
  let elves := g.battlefield.filter (fun o => o.name == "Llanowar Elves")
  let (g, _) := g.move elves[0]!.id (.graveyard ⟨1⟩) none
  let (g, _) := g.move elves[1]!.id (.graveyard ⟨1⟩) none
  let giant := namedPermanent g "Hill Giant"
  combatDamageToAssign g giant true == 0 &&
    combatDamageSourceLine g giant true ==
      s!"{giant.id} Hill Giant assigns no combat damage (no remaining blockers)"
#guard
  let g := bearsBlockingTwoOgresReady
  let ogres := g.battlefield.filter (fun o => o.name == "Gray Ogre")
  let (g, _) := g.move ogres[0]!.id (.graveyard ⟨0⟩) none
  let (g, _) := g.move ogres[1]!.id (.graveyard ⟨0⟩) none
  let bears := namedPermanent g "Grizzly Bears"
  combatDamageSourceLine g bears false ==
    s!"{bears.id} Grizzly Bears assigns no combat damage (not blocking any creatures)"

#guard
  let g := goblinBlockedByBears
  let goblin := namedPermanent g "Battle-Scarred Goblin"
  mentions (objectLine g goblin) "*attacking Nissa, blocked*" &&
    !mentions (objectLine goblinDeclaredAttacker (namedPermanent goblinDeclaredAttacker
      "Battle-Scarred Goblin")) "*blocked"

-- The demo names who an attacker is attacking (CR 508.1).
#guard
  mentions (objectLine onlyBearsAttack (namedPermanent onlyBearsAttack "Grizzly Bears"))
    "*attacking Nissa*" &&
    !mentions (objectLine onlyBearsAttack (namedPermanent onlyBearsAttack "Grizzly Bears"))
      "blocked"
#guard
  mentions (objectLine threeOgreAttacksLiliana
      (namedPermanent threeOgreAttacksLiliana "Gray Ogre"))
    "*attacking Liliana*"
#guard
  let ogres := threeSplitAttack.battlefield.filter (·.name == "Gray Ogre")
  mentions (objectLine threeSplitAttack ogres[0]!) "*attacking Nissa*" &&
    mentions (objectLine threeSplitAttack ogres[1]!) "*attacking Liliana*"

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
  let c := card "Silent Siege" #[.creature]
    (oracleText := "Trample\nOther Orcs and Goblins you control have trample.\nWhenever this creature attacks, it gets +X/+0 until end of turn, where X is the greatest power among creatures you control.")
    (keywords := Keyword.trample)
    (staticAbilities := #[.otherCreaturesHaveTrample #["Orc", "Goblin"]])
    (triggeredAbilities := #[.onAttackPumpByGreatestPower])
  let t := TriggeredAbility.toNotation .onAttackPumpByGreatestPower
  textForStackedAbility c t == t &&
    !mentions (textForStackedAbility c t) "Other Orcs and Goblins"

/- A card with a single leftover Oracle ability keeps that printed wording. -/
#guard
  let c := artifact "Silent Bauble" ManaCost.empty
    "{2}, {T}, Sacrifice this artifact: Search your library for a basic land card, put that card onto the battlefield tapped, then shuffle."
  textForStackedAbility c (Effect.toNotation (Effect.searchBasicLandTapped)) ==
    c.oracleText

#guard (changedZones tappedTwiceForBauble paidBauble).contains .battlefield
#guard (changedZones tappedTwiceForBauble paidBauble).contains (.graveyard ⟨0⟩)
#guard (paidBauble.player ⟨0⟩).graveyard.any (fun id =>
  let line := zoneLine paidBauble (.graveyard ⟨0⟩) id
  mentions line "Search your library" &&
    mentions line "{1}" &&
    mentions line "Artifact")

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

#guard mentions (header paidClub) "sacrifice a creature or artifact"
#guard mentions (header bladeMustSac) "sacrifice a creature (Nissa)"
#guard !mentions (header bladeMustSac) "artifact"
#guard pendingCostNotation targetedClub == some "{1}{R}, Sacrifice an artifact or creature"
#guard pendingCostLine targetedClub == some "Cost: {1}{R}, Sacrifice an artifact or creature"
#guard mentions (header targetedClub) "cost {1}{R}, Sacrifice an artifact or creature"
#guard pendingCostLine paidClub == none
#guard (changedZones clubReady castClub).contains .stack
#guard (changedZones clubReady castClub).contains .battlefield
#guard (changedZones clubReady castClub).contains (.graveyard ⟨0⟩)

#guard (changedZones activatedHunter resolvedHunter).contains .exile
#guard (changedZones activatedHunter resolvedHunter).contains (.library ⟨0⟩)
#guard mentions (snapshot resolvedHunter) "may be played by Chandra"
#guard mentions (zoneBlock resolvedHunter .exile) "may be played by Chandra"
#guard mentions (zoneBlock resolvedHunter .exile) "{R}"
#guard mentions (zoneBlock resolvedHunter .exile) "Instant"
-- Exile listings print the Oracle face (mana cost, type line, P/T) whether or
-- not someone may play the card. `exilePlayManaCost` is still empty without a
-- play permission.
#guard exilePlayManaCost (exiledBolt resolvedHunter) == "{R}"
#guard exilePlayManaCost (exiledMountain resolvedHunterLand) == ""
#guard exilePlayManaCost (exiledSmaug resolvedSpewFlame) == "{5}{R}{R}"
#guard exilePlayManaCost (exiledBeorn resolvedTillAndTend) == "{4}{G}"
#guard
  let o := exiledBolt resolvedHunter
  zoneLine resolvedHunter .exile o.id ==
    s!"{o.id} Lightning Bolt \{R} Instant Lightning Bolt deals 3 damage to any target. (may be played by Chandra)"
#guard !mentions (zoneLine resolvedHunter .exile (exiledBolt resolvedHunter).id)
  "without paying its mana cost"
#guard
  let o := exiledMountain resolvedHunterLand
  let line := zoneLine resolvedHunterLand .exile o.id
  mentions line "may be played by Chandra" &&
    mentions line "Basic Land — Mountain" &&
    !mentions line "{0}"
#guard
  let line := zoneLine resolvedSpewFlame .exile (exiledSmaug resolvedSpewFlame).id
  mentions line "{5}{R}{R}" &&
    mentions line "Legendary Creature — Dragon" &&
    mentions line "5/5"
#guard
  let line := zoneLine resolvedTillAndTend .exile (exiledBeorn resolvedTillAndTend).id
  mentions line "{4}{G}" &&
    mentions line "Legendary Creature — Human Bear Shapeshifter" &&
    mentions line "5/5"
#guard
  match resolvedSmiteOnBears.objects.find? (fun o =>
    o.zone == .exile && o.name == "Grizzly Bears") with
  | some o =>
    exilePlayManaCost o == "" &&
      mentions (zoneLine resolvedSmiteOnBears .exile o.id) "Grizzly Bears" &&
      mentions (zoneLine resolvedSmiteOnBears .exile o.id) "{1}{G}" &&
      mentions (zoneLine resolvedSmiteOnBears .exile o.id) "Creature — Bear" &&
      mentions (zoneLine resolvedSmiteOnBears .exile o.id) "2/2" &&
      !mentions (zoneLine resolvedSmiteOnBears .exile o.id) "may be played" &&
      !mentions (zoneLine resolvedSmiteOnBears .exile o.id) "exiled until"
  | none => false

-- Linked exile until a source leaves (CR 610.3) prints on the exiled card and
-- on the source permanent. Ordinary exile (above) does not.
#guard
  let g := fiendHunterLinked
  let hunter := namedPermanent g "Fiend Hunter"
  match g.objects.find? (fun o => o.zone == .exile && o.name == "Grizzly Bears") with
  | none => false
  | some bears =>
    let untilClause :=
      s!"*exiled until {hunter.id} Fiend Hunter leaves the battlefield*"
    let exilingClause := s!"*exiling {bears.id} Grizzly Bears*"
    (match linkedExileSource? g bears with
      | some src => src.id == hunter.id
      | none => false) &&
      (linkedExiledCards g hunter).size == 1 &&
      exileUntilLeavesClause g bears == s!" {untilClause}" &&
      linkedExileClause g hunter == s!" {exilingClause}" &&
      mentions (exileLine g bears) untilClause &&
      mentions (zoneLine g .exile bears.id) untilClause &&
      mentions (zoneBlock g .exile) untilClause &&
      mentions (snapshot g) untilClause &&
      mentions (objectLine g hunter) exilingClause &&
      mentions (zoneBlock g .battlefield) exilingClause &&
      mentions (battlefieldBlock g) exilingClause &&
      mentions (snapshot g) exilingClause

-- After the source leaves, the card is back and neither marker remains.
#guard
  let g := fiendHunterReturned
  let bears := namedPermanent g "Grizzly Bears"
  !mentions (objectLine g bears) "exiled until" &&
    !mentions (objectLine g bears) "*exiling" &&
    !mentions (snapshot g) "exiled until" &&
    !mentions (snapshot g) "*exiling" &&
    !(g.objects.any (fun o => o.zone == .exile && o.name == "Grizzly Bears"))

-- Several cards linked to one source are listed together.
#guard
  let g := addPermanent afterDraw fiendHunter ⟨0⟩ ⟨0⟩
  let g := addPermanent g grizzlyBears ⟨1⟩ ⟨1⟩
  let g := addPermanent g llanowarElves ⟨1⟩ ⟨1⟩
  let hunter := namedPermanent g "Fiend Hunter"
  let g := g.exileUntilSourceLeaves (some hunter.id) (namedPermanent g "Grizzly Bears")
  let g := g.exileUntilSourceLeaves (some hunter.id) (namedPermanent g "Llanowar Elves")
  let hunter := namedPermanent g "Fiend Hunter"
  match g.objects.find? (fun o => o.zone == .exile && o.name == "Grizzly Bears"),
        g.objects.find? (fun o => o.zone == .exile && o.name == "Llanowar Elves") with
  | some bears, some elves =>
    let clause :=
      s!"*exiling {bears.id} Grizzly Bears, {elves.id} Llanowar Elves*"
    mentions (objectLine g hunter) clause &&
      mentions (exileLine g bears)
        s!"*exiled until {hunter.id} Fiend Hunter leaves the battlefield*" &&
      mentions (exileLine g elves)
        s!"*exiled until {hunter.id} Fiend Hunter leaves the battlefield*"
  | _, _ => false

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
#guard mentions (stackBlock targetedBolt) "*targeting Nissa*"
#guard mentions (zoneBlock targetedBolt .stack) "*targeting Nissa*"
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
    s!"{bears.id} Grizzly Bears {bears.typeLine} 5/5 (owned by Chandra, controlled by Chandra)" &&
  mentions (objectLine g aura) s!"*enchanting {bears.id} Grizzly Bears*" &&
  mentions (header giftScrying) "scry 2" &&
  mentions (snapshot giftScrying) "Looking at (scry 2, top last):"

#guard
  let g := spearEquipped
  let bears := namedPermanent g "Grizzly Bears"
  let spear := namedPermanent g "Ragged Short Spear"
  objectLine g bears ==
    s!"{bears.id} Grizzly Bears {bears.typeLine} 4/2 (owned by Chandra, controlled by Chandra)" &&
  mentions (objectLine g spear) s!"*equipping {bears.id} Grizzly Bears*" &&
  mentions (header spearMayDiscard) "may discard a card, then draw 2"

#guard mentions (header struckerMayConnive) "may have Red Guardian, Super-Soldier connive"

#guard
  let g := spearEquipped
  let bears := namedPermanent g "Grizzly Bears"
  let spear := namedPermanent g "Ragged Short Spear"
  let hostLine := objectLine g bears (some (some ⟨0⟩))
  let spearLine := objectLine g spear (some (some ⟨0⟩))
  mentions spearLine "*equipping" &&
    mentions (battlefieldBlock g) s!"    {hostLine}\n      {spearLine}" &&
    mentions (snapshot g) (battlefieldBlock g)

-- Attached permanents print next to their host, with two extra spaces.
#guard
  let g := giftEntered
  let bears := namedPermanent g "Grizzly Bears"
  let aura := namedPermanent g "Gift of Strands"
  let hostLine := objectLine g bears (some (some ⟨0⟩))
  let auraLine := objectLine g aura (some (some ⟨0⟩))
  zoneBlock g .battlefield ==
    s!"zone battlefield (2):\n  Chandra:\n    {hostLine}\n      {auraLine}" &&
  battlefieldBlock g ==
    s!"Battlefield (2):\n  Chandra:\n    {hostLine}\n      {auraLine}" &&
  mentions (snapshot g) (battlefieldBlock g)

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
  battlefieldBlock g ==
    s!"Battlefield (3):\n  Chandra:\n    {hostLine}\n      {auraLine}\n    {landLine}"

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
    battlefieldBlock g ==
      s!"Battlefield (2):\n  Nissa:\n    {hostLine}\n      {auraLine}" &&
    !mentions (playerBlock g (g.player ⟨0⟩)) "Battlefield" &&
    !mentions (playerBlock g (g.player ⟨1⟩)) "Battlefield"

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
  battlefieldBlock g ==
    s!"Battlefield (3):\n  Chandra:\n    {hostLine}\n    {baubleLine}\n    {landLine}"

-- Each battlefield permanent prints its current types (CR 205.1a).
#guard
  let g := addPermanent started mountain ⟨0⟩ ⟨0⟩
  let g := addPermanent g wayfarersBauble ⟨0⟩ ⟨0⟩
  let g := addPermanent g grizzlyBears ⟨0⟩ ⟨0⟩
  let g := addPermanent g beornsHospitality ⟨0⟩ ⟨0⟩
  let land := namedPermanent g "Mountain"
  let bauble := namedPermanent g "Wayfarer's Bauble"
  let bears := namedPermanent g "Grizzly Bears"
  let hosp := namedPermanent g "Beorn's Hospitality"
  land.typeLine == "Basic Land — Mountain" &&
    bauble.typeLine == "Artifact" &&
    bears.typeLine == "Creature — Bear" &&
    hosp.typeLine == "Enchantment" &&
    mentions (objectLine g land) land.typeLine &&
    mentions (objectLine g bauble) bauble.typeLine &&
    mentions (objectLine g bears) bears.typeLine &&
    mentions (objectLine g hosp) hosp.typeLine &&
    mentions (zoneBlock g .battlefield) "Creature — Bear" &&
    mentions (zoneBlock g .battlefield) "Artifact" &&
    mentions (zoneBlock g .battlefield) "Enchantment" &&
    mentions (zoneBlock g .battlefield) "Basic Land — Mountain" &&
    mentions (battlefieldBlock g) "Creature — Bear"

#guard
  let g := giftEntered
  let aura := namedPermanent g "Gift of Strands"
  mentions (objectLine g aura) "Enchantment — Aura"

#guard
  let g := spearEquipped
  let spear := namedPermanent g "Ragged Short Spear"
  mentions (objectLine g spear) "Artifact — Equipment"

#guard
  let g := bladeEquipped
  let blade := namedPermanent g "Crude Bent Blade"
  mentions (objectLine g blade) "Artifact — Equipment"

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

-- Creature spells on the stack print types and P/T (CR 205.1a / 208.2).
#guard
  let g := paidGuide
  let o := g.object! g.stack.back!.objectId
  o.isCreature &&
    o.typeLine == "Creature — Elf Scout" &&
    g.power o == 3 && g.toughness o == 4 &&
    mentions (stackBlock g) "Creature — Elf Scout" &&
    mentions (stackBlock g) "3/4" &&
    mentions (zoneBlock g .stack) "Creature — Elf Scout" &&
    mentions (zoneBlock g .stack) "3/4" &&
    mentions (snapshot g) "Creature — Elf Scout" &&
    mentions (stackObjectLine g g.stack.back!) "Creature — Elf Scout 3/4"
#guard
  let g := proposedOgre
  let o := g.object! g.stack.back!.objectId
  o.typeLine == "Creature — Ogre" &&
    g.power o == 2 && g.toughness o == 2 &&
    mentions (stackBlock g) "Creature — Ogre" &&
    mentions (stackBlock g) "2/2"
#guard
  let g := paidGandalf
  let o := g.object! g.stack.back!.objectId
  o.typeLine == "Legendary Creature — Avatar Wizard" &&
    g.power o == 4 && g.toughness o == 3 &&
    mentions (stackBlock g) "Legendary Creature — Avatar Wizard" &&
    mentions (stackBlock g) "4/3" &&
    mentions (stackBlock g) "reach"
-- CDA power/toughness still apply on the stack (CR 604.3).
#guard
  let g := paidPathmaker
  let o := g.object! g.stack.back!.objectId
  o.typeLine == "Creature — Elf Ranger" &&
    g.power o == 2 && g.toughness o == 2 &&
    mentions (stackBlock g) "Creature — Elf Ranger" &&
    mentions (stackBlock g) "2/2"
-- Noncreature spells and stacked abilities omit creature types and P/T.
#guard !mentions (stackBlock proposedBolt) "Creature"
#guard !mentions (stackBlock proposedBauble) "Creature"
#guard
  let g := guideEntered
  !mentions (stackBlock g) "Creature — Elf Scout" &&
    !mentions (stackBlock g) "3/4"

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

#guard mentions (stackBlock lookoutAttackDeclared) "Lothlórien Lookout's ability"
#guard mentions (stackBlock lookoutAttackDeclared) "Whenever this creature attacks, scry 1"
#guard !mentions (stackBlock lookoutAttackDeclared) "When this permanent enters"
#guard
  let g := lookoutAttackDeclared
  let src := namedPermanent g "Lothlórien Lookout"
  mentions (stackBlock g) s!"*source {src.id} Lothlórien Lookout*" &&
    mentions (objectLine g src) "1/3"
#guard mentions (header lookoutScrying) "scry 1"
#guard mentions (snapshot lookoutScrying) "Looking at (scry 1, top last):"
#guard
  let g := lookoutKnownScrying
  let looked := g.scryLookedIds ⟨0⟩ 1
  match looked[0]? with
  | some forestId =>
    mentions (zoneBlock g (.library ⟨0⟩)) "looking at (top last)" &&
      mentions (zoneBlock g (.library ⟨0⟩)) "Forest" &&
      mentions (zoneBlock g (.library ⟨0⟩)) (toString forestId)
  | none => false

#guard mentions (stackBlock visionaryEntered) "Elvish Visionary's ability"
#guard mentions (stackBlock visionaryEntered) "When this creature enters, draw a card"
#guard !mentions (stackBlock visionaryEntered) "When this permanent enters"
#guard
  let g := visionaryEntered
  let visionary := namedPermanent g "Elvish Visionary"
  mentions (stackBlock g) s!"*source {visionary.id} Elvish Visionary*" &&
    mentions (zoneBlock g .stack) s!"*source {visionary.id} Elvish Visionary*" &&
    mentions (objectLine g visionary) "1/1"
#guard
  let g := visionaryDrew
  mentions (zoneBlock g (.hand ⟨0⟩)) "Forest" &&
    (changedZones visionaryKnownLib g).contains (.hand ⟨0⟩) &&
    (changedZones visionaryKnownLib g).contains (.library ⟨0⟩)

#guard mentions (stackBlock woodElvesEntered) "Wood Elves's ability"
#guard mentions (stackBlock woodElvesEntered) "When this creature enters, search your library for a Forest card"
#guard !mentions (stackBlock woodElvesEntered) "When this permanent enters"
#guard
  let g := woodElvesEntered
  let elves := namedPermanent g "Wood Elves"
  mentions (stackBlock g) s!"*source {elves.id} Wood Elves*" &&
    mentions (zoneBlock g .stack) s!"*source {elves.id} Wood Elves*" &&
    mentions (objectLine g elves) "1/1"
#guard
  let g := woodElvesResolved
  mentions (zoneBlock g .battlefield) "Forest" &&
    (changedZones woodElvesKnownLib g).contains .battlefield &&
    (changedZones woodElvesKnownLib g).contains (.library ⟨0⟩)

#guard
  let g := archAndElves
  mentions (objectLine g (namedPermanent g "Llanowar Elves")) "2/2" &&
    mentions (objectLine g (namedPermanent g "Elvish Archdruid")) "2/2" &&
    mentions (objectFaceExtras g (namedPermanent g "Elvish Archdruid"))
      "Other Elf creatures you control get +1/+1" &&
    mentions (objectFaceExtras g (namedPermanent g "Elvish Archdruid"))
      "{T}: Add {G} for each Elf you control"
#guard
  let g := tappedArchAndElves
  mentions (objectLine g (namedPermanent g "Elvish Archdruid")) "(tapped)" &&
    mentions (playerBlock g (g.player ⟨0⟩)) "{G}×2"

#guard mentions (header proposedCratermaker) "choose a mode (CR 601.2b"
#guard mentions (header proposedStature) "choose a value for X (CR 107.3a / 601.2b"
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
  mentions (stackBlock g) s!"*source {src.id} Beorn's Hospitality*" &&
    !mentions (stackBlock g) "*targeting"
#guard
  let g := hospitalityLandfallTargeted
  let bears := namedPermanent g "Grizzly Bears"
  mentions (stackBlock g) s!"*targeting {bears.id} Grizzly Bears*" &&
    mentions (zoneBlock g .stack) s!"*targeting {bears.id} Grizzly Bears*" &&
    (changedZones hospitalityLandPlayed g).contains .stack
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
#guard
  let g := pathmakerGrowsWithLand
  let o := namedPermanent g "Mirkwood Pathmaker"
  mentions (objectLine g o) "3/3"
#guard
  let g := pathmakerEntered
  let o := namedPermanent g "Mirkwood Pathmaker"
  mentions (objectLine g o) "2/2" &&
    mentions (objectLine g o) "(summoning sickness)"
#guard mentions (handLine pathmakerInHand
  (handCardNamed pathmakerInHand ⟨0⟩ "Mirkwood Pathmaker").id) "*/*"
#guard mentions mirkwoodPathmaker.summary "*/*"

#guard mentions (header gandalfEntered) "choose targets of this \"target\" word together (CR 601.2c"
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
#guard !mentions (stackBlock gandalfEntered) "*targeting"
#guard mentions (stackBlock gandalfTargetedOpponent) "*targeting Nissa for 3*"
#guard mentions (zoneBlock gandalfTargetedOpponent .stack) "*targeting Nissa for 3*"
#guard (changedZones gandalfEntered gandalfTargetedOpponent).contains .stack
#guard
  let g := gandalfSplitAnnounced
  let bears := namedPermanent g "Grizzly Bears"
  mentions (stackBlock g) s!"*targeting Nissa for 2 and {bears.id} Grizzly Bears for 1*" &&
    !mentions (stackBlock g) "; then" &&
    (changedZones gandalfSplitSetup g).contains .stack

#guard mentions (header galionAttackDeclared) "choose targets (CR 601.2c"
#guard mentions (stackBlock galionAttackDeclared) "Galion, Elvenking's Butler's ability"
#guard mentions (stackBlock galionAttackDeclared) "base power and toughness"
#guard
  let g := galionAttackDeclared
  let src := namedPermanent g "Galion, Elvenking's Butler"
  mentions (stackBlock g) s!"*source {src.id} Galion, Elvenking's Butler*" &&
    mentions (objectLine g src) "4/4" &&
    !mentions (stackBlock g) "*targeting" &&
    !mentions (stackBlock g) "*no target"
#guard
  let g := galionTargeted
  let elves := namedPermanent g "Llanowar Elves"
  mentions (stackBlock g) s!"*targeting {elves.id} Llanowar Elves*" &&
    (changedZones galionAttackDeclared g).contains .stack
#guard
  let g := mustApply galionAttackDeclared ⟨0⟩ .decline
  mentions (stackBlock g) "*no target*" &&
    mentions (zoneBlock g .stack) "*no target*" &&
    (changedZones galionAttackDeclared g).contains .stack
#guard
  let g := galionResolved
  let elves := namedPermanent g "Llanowar Elves"
  mentions (objectLine g elves) "4/4"

#guard mentions (header oliphauntAttackDeclared) "choose targets (CR 601.2c"
#guard mentions (stackBlock oliphauntAttackDeclared) "Oliphaunt's ability"
#guard mentions (stackBlock oliphauntAttackDeclared) "+2/+0"
#guard mentions (stackBlock oliphauntAttackDeclared) "trample"
#guard !mentions (stackBlock oliphauntAttackDeclared) "Mountaincycling"
#guard
  let g := oliphauntAttackDeclared
  let src := namedPermanent g "Oliphaunt"
  mentions (stackBlock g) s!"*source {src.id} Oliphaunt*" &&
    mentions (objectLine g src) "6/4" &&
    mentions (objectLine g src) "trample"
#guard
  let g := oliphauntResolved
  let ogre := namedPermanent g "Gray Ogre"
  mentions (objectLine g ogre) "4/2" &&
    mentions (objectLine g ogre) "trample"
#guard
  let g := afterOliphauntCleanup
  let ogre := namedPermanent g "Gray Ogre"
  mentions (objectLine g ogre) "2/2" &&
    !mentions (objectLine g ogre) "trample"

#guard mentions (header titanEntered) "choose targets of this \"target\" word together (CR 601.2c"
#guard mentions (stackBlock titanEntered) "Inferno Titan's ability"
#guard mentions (stackBlock titanEntered) "divided as you choose"
#guard mentions (stackBlock titanEntered) "Whenever this creature enters or attacks"
#guard !mentions (stackBlock titanEntered) "When this permanent enters"
#guard !mentions (stackBlock titanEntered) "+1/+0"
#guard
  let g := titanEntered
  let src := namedPermanent g "Inferno Titan"
  mentions (stackBlock g) s!"*source {src.id} Inferno Titan*" &&
    mentions (objectLine g src) "6/6"
#guard mentions (header titanAttackDeclared) "choose targets of this \"target\" word together (CR 601.2c"
#guard mentions (stackBlock titanAttackDeclared) "Inferno Titan's ability"
#guard mentions (stackBlock titanAttackDeclared) "divided as you choose"
#guard mentions (stackBlock titanAttackDeclared) "Whenever this creature enters or attacks"
#guard
  let g := pumpedTitan
  let o := namedPermanent g "Inferno Titan"
  mentions (objectLine g o) "7/6"

#guard mentions (stackBlock paidGuttersnipeBolt) "Guttersnipe's ability"
#guard mentions (stackBlock paidGuttersnipeBolt) "instant or sorcery"
#guard mentions (stackBlock paidGuttersnipeBolt) "Lightning Bolt"
#guard
  let g := paidGuttersnipeBolt
  let src := namedPermanent g "Guttersnipe"
  mentions (stackBlock g) s!"*source {src.id} Guttersnipe*" &&
    mentions (objectLine g src) "2/2"
#guard
  let g := guttersnipeTriggerResolved
  mentions (playerBlock g (g.player ⟨1⟩)) "life 18"

#guard mentions (header elkEntered) "choose targets (CR 601.2c"
#guard mentions (stackBlock elkEntered) "Mirkwood Elk's ability"
#guard mentions (stackBlock elkEntered) "Elf card"
#guard mentions (stackBlock elkEntered) "Whenever this creature enters or attacks"
#guard !mentions (stackBlock elkEntered) "When this permanent enters"
#guard
  let g := elkEntered
  let src := namedPermanent g "Mirkwood Elk"
  let elf := namedGraveyardCard g ⟨0⟩ "Llanowar Elves"
  mentions (stackBlock g) s!"*source {src.id} Mirkwood Elk*" &&
    mentions (objectLine g src) "6/6" &&
    mentions (playerBlock g (g.player ⟨0⟩)) "Graveyard (1):" &&
    mentions (playerBlock g (g.player ⟨0⟩)) elf.name &&
    mentions (playerBlock g (g.player ⟨0⟩)) "{G}" &&
    mentions (playerBlock g (g.player ⟨0⟩)) "Creature — Elf Druid" &&
    mentions (playerBlock g (g.player ⟨0⟩)) "1/1" &&
    !mentions (stackBlock g) "*targeting"
#guard
  let g := elkTargeted
  let elf := namedGraveyardCard g ⟨0⟩ "Llanowar Elves"
  mentions (stackBlock g) s!"*targeting {elf.id} Llanowar Elves*" &&
    (changedZones elkEntered g).contains .stack
#guard mentions (header elkAttackDeclared) "choose targets (CR 601.2c"
#guard mentions (stackBlock elkAttackDeclared) "Mirkwood Elk's ability"
#guard mentions (stackBlock elkAttackDeclared) "Whenever this creature enters or attacks"
#guard
  let g := elkResolved
  mentions (playerBlock g (g.player ⟨0⟩)) "life 21" &&
    mentions (playerBlock g (g.player ⟨0⟩)) "Graveyard (0):"

#guard mentions (stackBlock paidTillAndTend) "Till and Tend"
#guard mentions (stackBlock paidTillAndTend) "additional land"
#guard mentions (zoneBlock resolvedTillAndTend .exile) "Beorn, Reluctant Host"
#guard mentions (zoneBlock resolvedTillAndTend .exile) "{4}{G}"
#guard mentions (zoneBlock resolvedTillAndTend .exile) "Legendary Creature"
#guard mentions (zoneBlock resolvedTillAndTend .exile) "5/5"
#guard resolvedTillAndTend.log.any (fun s => mentions s "may play an additional land this turn")
#guard mentions (objectLine resolvedExiledBeorn
  (namedPermanent resolvedExiledBeorn "Beorn, Reluctant Host")) "trample"

#guard mentions (stackBlock paidFireOfOrthanc) "Fire of Orthanc"
#guard mentions (stackBlock paidFireOfOrthanc) "artifact or land"
#guard mentions (stackBlock paidFireOfOrthanc) "can't block this turn"
#guard resolvedFireOfOrthanc.log.any (fun s => mentions s "Forest is destroyed")
#guard resolvedFireOfOrthanc.log.any (fun s =>
  mentions s "Creatures without flying can't block this turn")
#guard mentions (stackBlock attercopLandPlayed) "Attercop's ability"
#guard mentions (stackBlock attercopLandPlayed) "Whenever a land you control enters"
#guard mentions (stackBlock attercopLandPlayed) "+1/+1 until end of turn"
#guard
  let g := attercopLandPlayed
  let src := namedPermanent g "Attercop"
  mentions (stackBlock g) s!"*source {src.id} Attercop*" &&
    mentions (objectLine g src) "2/1" &&
    mentions (objectLine g src) "reach" &&
    mentions (objectLine g src) "deathtouch"
#guard
  let g := attercopLandfallResolved
  let o := namedPermanent g "Attercop"
  mentions (objectLine g o) "3/2"
#guard
  let g := afterAttercopCleanup
  let o := namedPermanent g "Attercop"
  mentions (objectLine g o) "2/1"
#guard mentions (objectLine flyerVsAttercop
  (namedPermanent flyerVsAttercop "Attercop")) "reach"

#guard pendingCostNotation targetedPassage == some "{4}, {T}"
#guard pendingCostLine targetedPassage == some "Cost: {4}, {T}"
#guard mentions (header proposedPassage) "choose targets (CR 601.2c"
#guard mentions (stackBlock paidPassage) "can't be blocked"
#guard mentions (stackBlock paidPassage) "Rogue's Passage's ability"
#guard
  let g := paidPassage
  let ogre := namedPermanent g "Gray Ogre"
  mentions (stackBlock g) s!"*targeting {ogre.id} Gray Ogre*" &&
    mentions (zoneBlock g .stack) s!"*targeting {ogre.id} Gray Ogre*"
#guard !mentions (stackBlock proposedQuarrel) "*targeting"
#guard mentions (header proposedQuarrel) "first \"target\" word"
#guard
  let g := quarrelSourceChosen
  let elves := namedPermanent g "Llanowar Elves"
  mentions (stackBlock g) s!"*targeting {elves.id} Llanowar Elves*" &&
    mentions (header g) "next \"target\" word" &&
    (changedZones proposedQuarrel g).contains .stack
#guard
  let g := targetedQuarrel
  let elves := namedPermanent g "Llanowar Elves"
  let bears := namedPermanent g "Grizzly Bears"
  mentions (stackBlock g) s!"*targeting {elves.id} Llanowar Elves; then {bears.id} Grizzly Bears*" &&
    mentions (zoneBlock g .stack) s!"*targeting {elves.id} Llanowar Elves; then {bears.id} Grizzly Bears*" &&
    !mentions (stackBlock g)
      s!"*targeting {elves.id} Llanowar Elves and {bears.id} Grizzly Bears*" &&
    (changedZones quarrelSourceChosen g).contains .stack
#guard mentions (header gazeProposed) "choose targets of this \"target\" word together (CR 601.2c"
#guard mentions (header proposedMeagerMeal) "first \"target\" word"
#guard mentions (header proposedMeagerMeal) "up to one target creature"
#guard mentions (header meagerMealCreatureChosen) "next \"target\" word"
#guard mentions (header meagerMealCreatureChosen) "target player"
#guard mentions (header meagerMealDeclinedCreature) "next \"target\" word"
#guard mentions (header meagerMealDeclinedCreature) "target player"
#guard
  let g := gazeOneTarget
  let bears := namedPermanent g "Grizzly Bears"
  mentions (stackBlock g) s!"*targeting {bears.id} Grizzly Bears*" &&
    !mentions (stackBlock g) "; then"
#guard
  let g := gazeTwoTargets
  let bears := namedPermanent g "Grizzly Bears"
  let ogre := namedPermanent g "Gray Ogre"
  mentions (stackBlock g) s!"*targeting {bears.id} Grizzly Bears and {ogre.id} Gray Ogre*" &&
    !mentions (stackBlock g) "; then"
#guard
  let g := passageResolved
  mentions (objectLine g (namedPermanent g "Gray Ogre")) "can't be blocked"
#guard
  let g := afterPassageCleanup
  !mentions (objectLine g (namedPermanent g "Gray Ogre")) "can't be blocked"

#guard mentions smiteTheDeathless.summary "loses indestructible"
#guard mentions smiteTheDeathless.summary "exile it instead"
#guard
  let g := addPermanent started indestructibleBeast ⟨0⟩ ⟨0⟩
  mentions (objectLine g (lastPermanent g)) "indestructible"
#guard mentions (zoneBlock resolvedSmiteOnBears .exile) "Grizzly Bears"
#guard mentions (zoneBlock resolvedSmiteOnBears .exile) "{1}{G}"
#guard mentions (zoneBlock resolvedSmiteOnBears .exile) "Creature — Bear"
#guard mentions (zoneBlock resolvedSmiteOnBears .exile) "2/2"
#guard
  let g := resolvedSmiteOnWurm
  let w := namedPermanent g "Craw Wurm"
  mentions (objectLine g w) "dmg:3" &&
    mentions (objectLine g w) "exile if dies"
#guard
  let g := resolvedSmiteOnIndestructibleFlyer
  let o := namedPermanent g "Indestructible Flyer"
  mentions (objectLine g o) "flying" &&
    !mentions (objectLine g o) "indestructible" &&
    mentions (objectLine g o) "exile if dies" &&
    mentions (objectLine g o) "dmg:3"

#guard mentions (stackBlock wargFerociousDeclared) "Ravening Warg's ability"
#guard mentions (stackBlock wargFerociousDeclared) "power 4 or greater"
#guard mentions (stackBlock wargFerociousDeclared) "you gain 2 life"
#guard
  let g := wargFerociousDeclared
  let src := namedPermanent g "Ravening Warg"
  mentions (stackBlock g) s!"*source {src.id} Ravening Warg*" &&
    mentions (objectLine g src) "deathtouch" &&
    mentions (objectLine g src) "2/2"
#guard mentions (lifeLine (wargFerociousResolved.player ⟨0⟩)) "life 22"
#guard mentions (objectLine twoBearsBlockGollum
  (namedPermanent twoBearsBlockGollum "Gollum, Silent Slinker")) "menace"
#guard mentions (objectLine twoBearsBlockGollum
  (namedPermanent twoBearsBlockGollum "Gollum, Silent Slinker")) "blocked"

#guard mentions (stackBlock paidBilbosDeadlySlice) "Bilbo's Deadly Slice"
#guard mentions (stackBlock paidBilbosDeadlySlice) "Destroy target creature"
#guard
  let g := paidBilbosDeadlySlice
  let bears := namedPermanent g "Grizzly Bears"
  mentions (stackBlock g) s!"*targeting {bears.id} Grizzly Bears*"
#guard resolvedBilbosDeadlySlice.log.any (fun s =>
  mentions s "Grizzly Bears is destroyed")
#guard mentions (zoneBlock resolvedBilbosDeadlySlice (.graveyard ⟨1⟩)) "Grizzly Bears"

#guard mentions (stackBlock paidNightsWhisper) "Night's Whisper"
#guard mentions (stackBlock paidNightsWhisper) "draw two cards"
#guard mentions (stackBlock paidNightsWhisper) "lose 2 life"
#guard mentions (zoneBlock resolvedNightsWhisper (.hand ⟨0⟩)) "Swamp"
#guard mentions (zoneBlock resolvedNightsWhisper (.hand ⟨0⟩)) "Forest"
#guard mentions (lifeLine (resolvedNightsWhisper.player ⟨0⟩)) "life 18"
#guard resolvedNightsWhisper.log.any (fun s => mentions s "draws Swamp")
#guard resolvedNightsWhisper.log.any (fun s => mentions s "draws Forest")
#guard resolvedNightsWhisper.log.any (fun s => mentions s "loses 2 life (18 life)")

#guard mentions (header stirChooseAdditional) "choose an additional cost (CR 601.2b"
#guard mentions (header bladeMustSac) "sacrifice a creature"
#guard mentions (header stonyDiscarding) "discard a card"
#guard mentions (header gollumDeclareBlockers) "declare blockers"
#guard mentions (objectLine howlLifelink (namedPermanent howlLifelink "Raging Goblin"))
  "lifelink"

/-- Grant a “cast without paying its mana cost” exile permission (Thranduil's Decree). -/
def withFreeExileCast (g : Game) (name : String) (p : PlayerId) : Game :=
  match g.objects.find? (fun o => o.zone == .exile && o.name == name) with
  | none => g
  | some o =>
    g.setObject { o with playPermission := some {
      player := p
      turnEndsRemaining := 0
      whileExiled := true
      withoutManaCost := true } }

def freeExileOgre : Game :=
  withFreeExileCast (insertObject started grayOgre ⟨1⟩ .exile) "Gray Ogre" ⟨0⟩

#guard
  match freeExileOgre.objects.find? (fun o => o.zone == .exile && o.name == "Gray Ogre") with
  | none => false
  | some o =>
    let line := exileLine freeExileOgre o
    mentions line "may be played by Chandra without paying its mana cost" &&
      mentions line "{2}{R}" &&
      exilePlayManaCost o == "{0}" &&
      zoneLine freeExileOgre .exile o.id == line &&
      mentions (zoneBlock freeExileOgre .exile) "without paying its mana cost" &&
      mentions (snapshot freeExileOgre) "without paying its mana cost" &&
      freeExileOgre.playsWithoutPayingManaCost o

/-- A creature whose only ability costs `{2}` less (to `{0}`) if you control a
legendary creature. -/
def freeKnight : CardDef :=
  creature "Free Knight" (ManaCost.ofColor .white) #["Human", "Knight"] 1 1
    (oracleText :=
      "{2}: This creature gets +1/+1 until end of turn. This ability costs {2} less to activate if you control a legendary creature.")
    (activatedAbilities := #[
      activated (Effect.sourceGets 1 1) (ManaCost.ofGeneric 2)
        (costReductionIfYouControlLegendary := 2)])

def testLegend : CardDef :=
  legendaryCreature "Test Legend" (ManaCost.ofColor .white) #["Human"] 1 1

def freeKnightAlone : Game :=
  addPermanent afterDraw freeKnight ⟨0⟩ ⟨0⟩

def freeKnightWithLegend : Game :=
  addPermanent freeKnightAlone testLegend ⟨0⟩ ⟨0⟩

#guard
  let o := namedPermanent freeKnightAlone "Free Knight"
  !freeKnightAlone.activatesWithoutPayingManaCost ⟨0⟩ o.printed.activatedAbilities[0]! &&
    !mentions (objectLine freeKnightAlone o) "without paying its mana cost"

#guard
  let o := namedPermanent freeKnightWithLegend "Free Knight"
  freeKnightWithLegend.activatesWithoutPayingManaCost ⟨0⟩ o.printed.activatedAbilities[0]! &&
    mentions (objectLine freeKnightWithLegend o) "may be activated without paying its mana cost" &&
    mentions (battlefieldBlock freeKnightWithLegend) "without paying its mana cost" &&
    mentions (snapshot freeKnightWithLegend) "without paying its mana cost"

#guard !mentions (objectLine prowlerReady (namedPermanent prowlerReady "Desolation Prowler"))
  "without paying its mana cost"

def freeKnightActivating : Game :=
  mustApply (readyMain freeKnightWithLegend) ⟨0⟩
    (.activate (namedPermanent freeKnightWithLegend "Free Knight").id 0)

#guard pendingCostNotation freeKnightActivating == some "{0}"
#guard pendingCostLine freeKnightActivating == some "Cost: {0}"
#guard mentions (header freeKnightActivating) "cost {0}"
#guard mentions (snapshot freeKnightActivating) "Cost: {0}"

/-- A spell whose entire generic mana cost is waived if a creature died. -/
def freeCloud : CardDef :=
  creature "Free Cloud" (ManaCost.ofGeneric 3) #["Bat"] 1 1
    (costReductionIfCreatureDied := 3)

def freeCloudInHand : Game :=
  addToHand (readyMain (emptyHand afterDraw ⟨0⟩)) freeCloud ⟨0⟩

def freeCloudAfterDeath : Game :=
  { freeCloudInHand with creatureDiedThisTurn := true }

#guard
  let o := handCardNamed freeCloudInHand ⟨0⟩ "Free Cloud"
  !freeCloudInHand.playsWithoutPayingManaCost o &&
    !mentions (handLine freeCloudInHand o.id) "without paying its mana cost"

#guard
  let o := handCardNamed freeCloudAfterDeath ⟨0⟩ "Free Cloud"
  freeCloudAfterDeath.playsWithoutPayingManaCost o &&
    mentions (handLine freeCloudAfterDeath o.id) "may be cast without paying its mana cost" &&
    mentions (playerBlock freeCloudAfterDeath (freeCloudAfterDeath.player ⟨0⟩))
      "without paying its mana cost" &&
    mentions (snapshot freeCloudAfterDeath) "without paying its mana cost"

-- Cosmic Cube's look is a controller choice: the header and looked-at
-- faces are shown to that player, not auto-cast.
#guard
  let g := Mtg.Engine.MshRulingTests.cosmicCubePending
  mentions (header g) "may cast a looked-at spell" &&
    mentions (header g) "mana value ≤ 2" &&
    mentions (snapshot g) "Looking at (may cast, mana value ≤ 2, top last):" &&
    mentions (snapshot g) "Lightning Bolt" &&
    mentions (snapshot g (some ⟨1⟩)) "Looking at (may cast): (hidden)" &&
    !mentions (snapshot g (some ⟨1⟩)) "Lightning Bolt" &&
    (match scryLookBlock g (some ⟨1⟩) with
     | some s => mentions s "looking at cards"
     | none => false) &&
    !g.objects.any (fun o => o.name == "Lightning Bolt" && o.zone == .stack)

end Mtg.Demo.RenderTests
