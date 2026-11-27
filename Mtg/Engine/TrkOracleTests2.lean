import Mtg.Engine.Catalog
import Mtg.Engine.Catalog.StarTrek
import Mtg.Engine.Game
import Mtg.Engine.OracleData
import Mtg.Engine.Tests.Auras
import Mtg.Engine.Tests.Helpers
import Mtg.Engine.Tests.StarTrek
import Mtg.Engine.Tests.Turns
import Mtg.Engine.TrkOracleTests

/-!
# Engine behavior for Star Trek (TRK) judge rulings

These tests verify official Gatherer Oracle rulings on TRK cards against live
`Game` states. Each section tags its checks with the ruling id in
`uniqueOracleRulings`.
-/

namespace Mtg.Engine.TrkRulingTests

open Mtg.Engine
open Mtg.Engine.Catalog
open Mtg.Engine.Tests

private def trkRulingMain : Game :=
  skipTo started .precombatMain 40

private def rejects (g : Game) (p : PlayerId) (a : Action) (needle : String := "") : Bool :=
  match g.apply p a with
  | .error e => needle.isEmpty || mentions e needle
  | .ok _ => false

/-- Advance to the start of the next turn's upkeep (stopping even if a trigger
opened a `Pending` choice at upkeep). -/
private def toNextUpkeep (g : Game) : Game :=
  passBoth (skipTo g .end 40)

/-- Put `card` onto the battlefield via `putOntoBattlefield` (running ETB
replacements) and fire `afterPermanentEnters` if no choice paused it. -/
private def enterCard (g : Game) (card : CardDef) (p : PlayerId)
    (tapped : Bool := false) (preBattlefield : Option (Array GameObject) := none) : Game :=
  let (g, obj) := g.allocObject card p (.outside p) none
  let (g, newId) := g.putOntoBattlefield obj.id p (tapped := tapped)
    (summoningSick := false) (preBattlefield := preBattlefield)
  if let .chooseReplacement .. := g.pending then
    g.chainPendingReplacement (.afterLastPermanentEnters (some obj.id) false)
  else
    g.afterPermanentEnters (g.object! newId)

/-!
## 1058, 1059, 576 — Brad Boimler, Eager Ensign
-/

/-- Rulings 1058 & 1059: tapping *Brad Boimler* once increases counters put on
permanents you control this turn by +1 (including ETB counters), without
affecting opponents' permanents. Resolving his trigger a second time this turn
increases counters put by +2. -/
def boimlerOnce : Game :=
  let g := addPermanent trkRulingMain bradBoimlerEagerEnsign ⟨0⟩ ⟨0⟩
  let g := addPermanent g oberthClassStarship ⟨0⟩ ⟨0⟩
  let g := addPermanent g grayOgre ⟨0⟩ ⟨0⟩
  let g := addPermanent g grizzlyBears ⟨1⟩ ⟨1⟩
  let brad := namedPermanent g "Brad Boimler, Eager Ensign"
  let ship := namedPermanent g "Oberth-Class Starship"
  -- Tap Brad Boimler to pay Station: Boimler's trigger resolves BEFORE Station,
  -- so Oberth-Class Starship gets 2 + 1 = 3 charge counters!
  let g := mustApply g ⟨0⟩ (.activate ship.id 0)
  let g := if g.pending == .activateManaAbilities ⟨0⟩ then mustApply g ⟨0⟩ .pay else g
  let g := mustApply g ⟨0⟩ (.choosePermanents #[brad.id])
  passBoth (passBoth g)

#guard (trkRuling 1058).comment.contains "enters with that many counters plus one"
#guard (trkRuling 1059).comment.contains "increased by two"
#guard (trkRuling 576).comment.contains "choose the order to apply those effects"
#guard
  -- Station got 2 + 1 = 3 charge counters; normal +1/+1 counter adds +1 on your creature,
  -- unchanged on opponent's creature.
  let ogre := namedPermanent boimlerOnce "Gray Ogre"
  let bear := namedPermanent boimlerOnce "Grizzly Bears"
  let g1 := boimlerOnce.addCounters ogre .plusOnePlusOne 1
  let g2 := g1.addCounters bear .plusOnePlusOne 1
  (namedPermanent boimlerOnce "Oberth-Class Starship").status.charge == 3 &&
  (namedPermanent g2 "Gray Ogre").status.plusOnePlusOne == 2 &&
  (namedPermanent g2 "Grizzly Bears").status.plusOnePlusOne == 1
#guard
  -- Ruling 1058: ETB counters (Sunburst with 1 color -> 1 + 1 = 2 charge counters).
  let g := insertObject boimlerOnce engineeredExplosives ⟨0⟩ (.hand ⟨0⟩) none
  let g := g.addMana ⟨0⟩ (.colored .red) 1
  let ee := (g.objects.find? (fun o => o.name == "Engineered Explosives" && o.zone == .hand ⟨0⟩)).get!
  let g := mustApply g ⟨0⟩ (.cast ee.id)
  let g := mustApply g ⟨0⟩ (.chooseX 1)
  let g := mustApply g ⟨0⟩ .pay
  let g := passBoth g
  (namedPermanent g "Engineered Explosives").status.charge == 2
#guard
  -- Ruling 1059: resolving Brad Boimler's trigger a second time stacks to +2.
  let brad := namedPermanent boimlerOnce "Brad Boimler, Eager Ensign"
  let ship := namedPermanent boimlerOnce "Oberth-Class Starship"
  let g := setTapped boimlerOnce brad.id false
  let g := mustApply g ⟨0⟩ (.activate ship.id 0)
  let g := if g.pending == .activateManaAbilities ⟨0⟩ then mustApply g ⟨0⟩ .pay else g
  let g := mustApply g ⟨0⟩ (.choosePermanents #[brad.id])
  let g := passBoth (passBoth g)
  let ogre := namedPermanent g "Gray Ogre"
  let g := g.addCounters ogre .plusOnePlusOne 1
  (namedPermanent g "Gray Ogre").status.plusOnePlusOne == 3

/-!
## 1063–1066 — Facing a dilemma (CR 700.17)
-/

/-- Rulings 1063 & 1064: an ability triggering when you face a dilemma resolves
before the modal spell and still resolves even if that modal spell is countered
while the trigger is on the stack. -/
def dilemmaCountered : Game :=
  let g := addPermanent trkRulingMain sevenOfNine ⟨0⟩ ⟨0⟩
  let g := insertObject g commandDecision ⟨0⟩ (.hand ⟨0⟩) none
  let g := insertObject g highlyIllogical ⟨1⟩ (.hand ⟨1⟩) none
  let g := withWhiteMana g ⟨0⟩ 2
  let g := withBlueMana g ⟨1⟩ 2
  let cd := (g.objects.find? (fun o => o.name == "Command Decision" && o.zone == .hand ⟨0⟩)).get!
  let g := mustApply g ⟨0⟩ (.cast cd.id)
  let g := mustApply g ⟨0⟩ (.chooseMode 1)
  let g := mustApply g ⟨0⟩ .pay
  -- Pass priority to opponent while Seven of Nine's trigger AND Command Decision are on stack.
  let g := mustApply g ⟨0⟩ .pass
  let hi := (g.objects.find? (fun o => o.name == "Highly Illogical" && o.zone == .hand ⟨1⟩)).get!
  let cdOnStack := (g.objects.find? (fun o => o.name == "Command Decision" && o.zone == .stack)).get!
  let g := mustApply g ⟨1⟩ (.cast hi.id)
  let g := mustApply g ⟨1⟩ (.announceKicker false)
  let g := mustApply g ⟨1⟩ (.target (.card cdOnStack.id))
  let g := mustApply g ⟨1⟩ .pay
  -- Resolve Highly Illogical (counters Command Decision), then resolve Seven of Nine's trigger.
  passBoth (passBoth g)

#guard (trkRuling 1063).comment.contains "doesn't matter if that spell or ability goes on to resolve"
#guard (trkRuling 1064).comment.contains "resolve before the spell or ability that caused it to trigger"
#guard (trkRuling 1065).comment.contains "faced only one dilemma"
#guard (trkRuling 1066).comment.contains "did not face a dilemma"
#guard GameEvent.dilemmasFaced dilemmaCountered.events dilemmaCountered.turnNumber ⟨0⟩ == 1
#guard dilemmaCountered.objects.any (fun o => o.name == "Command Decision" && o.zone == .graveyard ⟨0⟩)
-- Seven of Nine's draw trigger still resolved (+1 card after casting Command Decision from hand).
#guard (dilemmaCountered.player ⟨0⟩).hand.size == (trkRulingMain.player ⟨0⟩).hand.size + 1
-- Ruling 1065: two-mode spell counts as 1 dilemma (verified in `Tests.StarTrek`).
#guard GameEvent.dilemmasFaced trkTwoModeDilemma.events trkTwoModeDilemma.turnNumber ⟨0⟩ == 1
-- Ruling 1066: choosing 0 modes does NOT record facing a dilemma.
#guard
  let g := trkRulingMain.record (GameEvent.announced trkRulingMain.turnNumber ⟨999⟩ (modes := #[]))
  GameEvent.dilemmasFaced g.events g.turnNumber ⟨0⟩ == 0

/-!
## 1076 — Dr. McCoy, Surly Surgeon
-/

#guard (trkRuling 1076).comment.contains "doesn't replace effects or costs that require you to sacrifice"
#guard
  -- Replaces destroy effect ("destroyPermanent").
  let g := addPermanent trkRulingMain drMcCoySurlySurgeon ⟨0⟩ ⟨0⟩
  let g := addPermanent g grayOgre ⟨0⟩ ⟨0⟩
  let ogre := namedPermanent g "Gray Ogre"
  let g := g.addPlusOnePlusOneTo ogre 1
  let g := g.destroyPermanent (namedPermanent g "Gray Ogre")
  g.battlefield.any (·.name == "Gray Ogre") &&
  (namedPermanent g "Gray Ogre").status.plusOnePlusOne == 0
#guard
  -- Does NOT replace sacrifice.
  let g := addPermanent trkRulingMain drMcCoySurlySurgeon ⟨0⟩ ⟨0⟩
  let g := addPermanent g grayOgre ⟨0⟩ ⟨0⟩
  let ogre := namedPermanent g "Gray Ogre"
  let g := g.addPlusOnePlusOneTo ogre 1
  let g := g.sacrificeToGraveyard (namedPermanent g "Gray Ogre") "sacrificed"
  !g.battlefield.any (·.name == "Gray Ogre")
#guard
  -- Does NOT replace toughness <= 0 SBA (CR 704.5f).
  let g := addPermanent trkRulingMain drMcCoySurlySurgeon ⟨0⟩ ⟨0⟩
  let g := addPermanent g grizzlyBears ⟨0⟩ ⟨0⟩
  let bear := namedPermanent g "Grizzly Bears"
  let g := g.addPlusOnePlusOneTo bear 1
  let g := g.createEffect (.pump bear.id (-3) (-3))
  let g := g.checkSBA
  !g.battlefield.any (·.name == "Grizzly Bears")

/-!
## 1080–1085, 1161, 1172 — Beam me up, Marooned & Scotty, Miracle Worker
-/

#guard (trkRuling 1080).comment.contains "returning a creature you control to its owner's hand"
#guard (trkRuling 1081).comment.contains "follow any timing restrictions"
#guard (trkRuling 1083).comment.contains "always be exiled afterward"
#guard (trkRuling 1084).comment.contains "without having been cast"
#guard (trkRuling 1161).comment.contains "still be the target of spells that were cast using their beam me up"
#guard (trkRuling 1172).comment.contains "can be returned to your hand to pay the beam me up cost of spells that are cast using their own"

-- Ruling 1081: sorcery with beam me up can't be cast on opponent's turn.
#guard
  let g := addPermanent (toNextUpkeep trkRulingMain) grayOgre ⟨0⟩ ⟨0⟩
  let g := skipTo g .precombatMain 40
  let g := insertObject g federationResupply ⟨0⟩ (.graveyard ⟨0⟩) none
  let g := withWhiteMana g ⟨0⟩ 4
  let g := mustApply g ⟨1⟩ .pass
  let ogre := namedPermanent g "Gray Ogre"
  let res := (g.objects.find? (fun o => o.name == "Federation Resupply" && o.zone == .graveyard ⟨0⟩)).get!
  g.activePlayer == ⟨1⟩ && rejects g ⟨0⟩ (.castWithBeamMeUp res.id ogre.id)

-- Ruling 1083: a spell cast via beam me up is exiled even if countered.
#guard
  let g := insertObject trkBeamSetup highlyIllogical ⟨1⟩ (.hand ⟨1⟩) none
  let g := withBlueMana g ⟨1⟩ 2
  let ogre := namedPermanent g "Gray Ogre"
  let res := (g.objects.find? (fun o => o.name == "Federation Resupply" && o.zone == .graveyard ⟨0⟩)).get!
  let g := mustApply g ⟨0⟩ (.castWithBeamMeUp res.id ogre.id)
  let g := mustApply g ⟨0⟩ .pay
  let g := mustApply g ⟨0⟩ .pass
  let hi := (g.objects.find? (fun o => o.name == "Highly Illogical" && o.zone == .hand ⟨1⟩)).get!
  let resStack := (g.objects.find? (fun o => o.name == "Federation Resupply" && o.zone == .stack)).get!
  let g := mustApply g ⟨1⟩ (.cast hi.id)
  let g := mustApply g ⟨1⟩ (.announceKicker false)
  let g := mustApply g ⟨1⟩ (.target (.card resStack.id))
  let g := mustApply g ⟨1⟩ .pay
  let g := passBoth g
  g.objects.any (fun o => o.name == "Federation Resupply" && o.zone == .exile) &&
  !g.objects.any (fun o => o.name == "Federation Resupply" && o.zone == .graveyard ⟨0⟩)

-- Ruling 1161: Marooned creature can't be beamed up, but CAN still be targeted by a beam-me-up spell.
#guard
  let g := addPermanent trkRulingMain grayOgre ⟨0⟩ ⟨0⟩
  let g := addPermanent g grizzlyBears ⟨0⟩ ⟨0⟩
  let ogre := namedPermanent g "Gray Ogre"
  let g := addAttachedAura g marooned ogre ⟨0⟩ ⟨0⟩
  let g := insertObject g pureEnergy ⟨0⟩ (.graveyard ⟨0⟩) none
  let g := withWhiteMana g ⟨0⟩ 3
  let pe := (g.objects.find? (fun o => o.name == "Pure Energy" && o.zone == .graveyard ⟨0⟩)).get!
  let bear := namedPermanent g "Grizzly Bears"
  -- Can't return Marooned ogre, CAN return bear and target Marooned ogre.
  let blocked := rejects g ⟨0⟩ (.castWithBeamMeUp pe.id ogre.id)
  let g := mustApply g ⟨0⟩ (.castWithBeamMeUp pe.id bear.id)
  let g := mustApply g ⟨0⟩ (.target (.permanent ogre.id))
  let g := mustApply g ⟨0⟩ .pay
  let g := passBoth g
  blocked && (namedPermanent g "Gray Ogre").status.plusOnePlusOne == 2

-- Ruling 1172: Scotty CANNOT be returned for his granted beam me up (Lightning Bolt),
-- but CAN be returned for a spell's OWN beam me up ability (Federation Resupply).
#guard
  let g := addPermanent trkRulingMain scottyMiracleWorker ⟨0⟩ ⟨0⟩
  let g := insertObject g lightningBolt ⟨0⟩ (.graveyard ⟨0⟩) none
  let g := insertObject g federationResupply ⟨0⟩ (.graveyard ⟨0⟩) none
  let g := withRedMana g ⟨0⟩ 1
  let g := withWhiteMana g ⟨0⟩ 4
  let scotty := namedPermanent g "Scotty, Miracle Worker"
  let bolt := (g.objects.find? (fun o => o.name == "Lightning Bolt" && o.zone == .graveyard ⟨0⟩)).get!
  let res := (g.objects.find? (fun o => o.name == "Federation Resupply" && o.zone == .graveyard ⟨0⟩)).get!
  let grantedBlocked := rejects g ⟨0⟩ (.castWithBeamMeUp bolt.id scotty.id)
  let gOwn := mustApply g ⟨0⟩ (.castWithBeamMeUp res.id scotty.id)
  let gOwn := mustApply gOwn ⟨0⟩ .pay
  let gOwn := passBoth gOwn
  let gOwn := if gOwn.pending != .none then mustApply gOwn ⟨0⟩ .decline else gOwn
  grantedBlocked &&
  gOwn.objects.any (fun o => o.name == "Scotty, Miracle Worker" && o.zone == .hand ⟨0⟩) &&
  gOwn.objects.any (fun o => o.name == "Federation Resupply" && o.zone == .exile)

/-!
## 1093–1105 — Station & Spacecraft
-/

#guard (trkRuling 1096).comment.contains "negative power, no charge counters are put onto or removed"
#guard (trkRuling 1100).comment.contains "doesn't have that power and toughness in any zone other than the battlefield"
#guard (trkRuling 1101).comment.contains "won't use any power and toughness values printed in its text box"
#guard (trkRuling 1104).comment.contains "you can still activate its station ability"
#guard (trkRuling 1105).comment.contains "doesn't matter how long it's been a creature"

-- Ruling 1096: tapping a negative-power creature adds 0 charge counters (doesn't remove existing ones).
#guard
  let g := addPermanent trkRulingMain oberthClassStarship ⟨0⟩ ⟨0⟩
  let g := addPermanent g grizzlyBears ⟨0⟩ ⟨0⟩
  let ship := namedPermanent g "Oberth-Class Starship"
  let bear := namedPermanent g "Grizzly Bears"
  let g := g.addCounters ship .charge 2
  let g := g.createEffect (.pump bear.id (-5) 0) -- bear now has -3 power
  let g := mustApply g ⟨0⟩ (.activate ship.id 0)
  let g := if g.pending == .activateManaAbilities ⟨0⟩ then mustApply g ⟨0⟩ .pay else g
  let g := mustApply g ⟨0⟩ (.choosePermanents #[bear.id])
  let g := passBoth g
  (namedPermanent g "Oberth-Class Starship").status.charge == 2

-- Ruling 1100: Spacecraft has no printed power/toughness in hand/graveyard/library.
#guard oberthClassStarship.power.isNone && oberthClassStarship.toughness.isNone

-- Ruling 1101: animating a Spacecraft below threshold uses the animating effect's base P/T, not box P/T.
#guard
  let g := addPermanent trkRulingMain oberthClassStarship ⟨0⟩ ⟨0⟩
  let ship := namedPermanent g "Oberth-Class Starship"
  let g := g.createEffect (.layered (.objects #[ship.id]) (.types .add #[.creature] #[] #[]) .indefinite)
  let g := g.createEffect (.layered (.objects #[ship.id]) (.ptSet 5 5) .indefinite)
  let s := namedPermanent g "Oberth-Class Starship"
  g.isCreature s && g.power s == 5 && g.toughness s == 5 && !g.hasFlying s

-- Ruling 1104 & 1105: already-animated Spacecraft controlled since start of turn can both
-- still activate Station for more charge counters AND attack this turn.
#guard
  let ent := namedPermanent trkAfterStation2 "U.S.S. Enterprise-D, Galaxy-Class"
  let g := addPermanent trkAfterStation2 (creature "Tellarite Tech" ManaCost.empty #[] 2 2) ⟨0⟩ ⟨0⟩
  let tech := namedPermanent g "Tellarite Tech"
  let g := mustApply g ⟨0⟩ (.activate ent.id 0)
  let g := if g.pending == .activateManaAbilities ⟨0⟩ then mustApply g ⟨0⟩ .pay else g
  let g := mustApply g ⟨0⟩ (.choosePermanents #[tech.id])
  let g := passBoth g
  let extraOk := (namedPermanent g "U.S.S. Enterprise-D, Galaxy-Class").status.charge == 9
  let gComb := passBoth (skipTo g .beginningOfCombat 40)
  let canAtk := (gComb.apply ⟨0⟩ (.declareAttackers #[ent.id])).isOk
  extraOk && canAtk

/-!
## 1108–1110 — Pet Sehlat
-/

#guard (trkRuling 1108).comment.contains "declared as an attacker only if another creature is declared"
#guard (trkRuling 1109).comment.contains "they can attack together"
#guard
  let g := addPermanent trkRulingMain petSehlat ⟨0⟩ ⟨0⟩
  let g := addPermanent g petSehlat ⟨0⟩ ⟨0⟩
  let g := passBoth (skipTo g .beginningOfCombat 40)
  let sehlats := g.battlefield.filter (·.name == "Pet Sehlat")
  sehlats.size == 2 &&
  rejects g ⟨0⟩ (.declareAttackers #[sehlats[0]!.id]) &&
  (g.apply ⟨0⟩ (.declareAttackers #[sehlats[0]!.id, sehlats[1]!.id])).isOk

/-!
## 1118, 1304 — Federation & Sarek, Federation Ambassador
-/

#guard (trkRuling 1118).comment.contains "Borg Noble and a Human Noble"
#guard (trkRuling 1304).comment.contains "between five and nine creature types"
#guard
  -- Ruling 1118: Borg Noble + Human Noble = 2 creature types (Human, Noble); Borg-only adds 0.
  let borgNoble := creature "Assimilated Noble" ManaCost.empty #["Borg", "Noble"] 2 2
  let humanNoble := creature "Vulcan Envoy" ManaCost.empty #["Human", "Noble"] 2 2
  let borgDrone := creature "Pure Borg" ManaCost.empty #["Borg", "Wizard", "Warrior"] 2 2
  let g := addPermanent trkRulingMain borgNoble ⟨0⟩ ⟨0⟩
  let g := addPermanent g humanNoble ⟨0⟩ ⟨0⟩
  let g := addPermanent g borgDrone ⟨0⟩ ⟨0⟩
  let fedExpr := ValueExpr.subtypeCount .creature
    (.inZones .battlefield (.all #[.hasType .creature, .not (.hasSubtype (.literal .borg)), .controlledBy .you]))
  EvalExpr.evalValue g { controller := ⟨0⟩ } fedExpr == 2
#guard
  -- Ruling 1304: Sarek draws floor(N / 5): 5 non-Borg creature types -> 1 card.
  let c1 := creature "Crew A" ManaCost.empty #["Human", "Officer", "Scout"] 1 1
  let c2 := creature "Crew B" ManaCost.empty #["Borg", "Wizard", "Warrior", "Shaman", "Cleric"] 1 1
  -- Sarek itself is Vulcan + Advisor (2 types) + Crew A (3 types) = 5 non-Borg types -> 1 draw.
  let g := addPermanent trkRulingMain sarekFederationAmbassador ⟨0⟩ ⟨0⟩
  let g := addPermanent g c1 ⟨0⟩ ⟨0⟩
  let g := addPermanent g c2 ⟨0⟩ ⟨0⟩
  let h0 := (g.player ⟨0⟩).hand.size
  let g := passBoth (skipTo g .beginningOfCombat 40)
  (g.player ⟨0⟩).hand.size == h0 + 1

/-!
## 1154–1156 — Kobayashi Maru Scenario
-/

#guard (trkRuling 1154).comment.contains "that mode has still been chosen"
#guard (trkRuling 1155).comment.contains "removed from the stack with no effect"
#guard (trkRuling 1156).comment.contains "opponent gains control of that Kobayashi Maru Scenario"

-- Ruling 1154: choosing Mode 0 (Hail) with a target that becomes illegal causes the trigger
-- to fizzle on resolution, yet Mode 0 remains chosen on the next upkeep.
#guard
  let g := addPermanent trkRulingMain kobayashiMaruScenario ⟨0⟩ ⟨0⟩
  let g := addPermanent g grizzlyBears ⟨1⟩ ⟨1⟩
  let bear := namedPermanent g "Grizzly Bears"
  -- Advance past player 1's turn to player 0's next upkeep (stopping at Kobayashi Maru's prompt).
  let g := toNextUpkeep (toNextUpkeep g)
  -- Choose Mode 0 (Hail), target opponent's Grizzly Bears.
  let g := mustApply g ⟨0⟩ (.chooseMode 0)
  let g := mustApply g ⟨0⟩ (.target (.permanent bear.id))
  -- Remove Grizzly Bears before resolution so Mode 0 fizzles (CR 608.2b).
  let g := g.sacrificeToGraveyard bear "sacrificed"
  let g := passBoth g
  let fizzled := g.log.any (fun s => mentions s "all its targets are illegal")
  -- Advance to player 0's next upkeep: Mode 0 must no longer be available!
  let g2 := toNextUpkeep (toNextUpkeep g)
  let avail :=
    match g2.pending with
    | .resolutionChoice _ (.stackTriggerUnusedMode _ _ av true) => av
    | _ => #[]
  fizzled && avail == #[1, 2, 3]

-- Rulings 1155 & 1156: after modes 0, 1, 2 are chosen and opponent gains control,
-- opponent can only choose mode 3; once all 4 modes are chosen, the trigger is removed from stack.
#guard
  let g := addPermanent trkRulingMain kobayashiMaruScenario ⟨0⟩ ⟨0⟩
  let km := namedPermanent g "Kobayashi Maru Scenario"
  let g := g.record (GameEvent.triggerModeChosen g.turnNumber km.id 0 (lifetime := true))
  let g := g.record (GameEvent.triggerModeChosen g.turnNumber km.id 1 (lifetime := true))
  let g := g.record (GameEvent.triggerModeChosen g.turnNumber km.id 2 (lifetime := true))
  -- Ruling 1156: player 1 gains control -> on player 1's upkeep, only mode 3 is available.
  let gSteal := g.changeControl km ⟨1⟩
  let gOppUpkeep := toNextUpkeep gSteal
  let oppAvail :=
    match gOppUpkeep.pending with
    | .resolutionChoice p (.stackTriggerUnusedMode _ _ av true) => (p, av)
    | _ => (⟨0⟩, #[])
  -- Ruling 1155: once mode 3 is also marked chosen, next upkeep trigger is removed from stack.
  let gAll4 := g.record (GameEvent.triggerModeChosen g.turnNumber km.id 3 (lifetime := true))
  let gNext := toNextUpkeep (toNextUpkeep gAll4)
  oppAvail == (⟨1⟩, #[3]) &&
  gNext.stack.isEmpty &&
  gNext.log.any (fun s => mentions s "all modes have been chosen")

/-!
## 1158 — Lieutenant Commander Data
-/

#guard (trkRuling 1158).comment.contains "stun counter from one creature, a -1/-1 counter from another creature, and a +1/+1 counter from a third creature"
#guard
  let g := addPermanent trkRulingMain lieutenantCommanderData ⟨0⟩ ⟨0⟩
  let g := addPermanent g grayOgre ⟨0⟩ ⟨0⟩
  let g := addPermanent g grizzlyBears ⟨0⟩ ⟨0⟩
  let g := withBlueMana g ⟨0⟩ 1
  let data := namedPermanent g "Lieutenant Commander Data"
  let ogre := namedPermanent g "Gray Ogre"
  let bear := namedPermanent g "Grizzly Bears"
  let g := g.addCounters data .stun 1
  let g := g.addCounters ogre .minusOneMinusOne 1
  let g := g.addCounters bear .plusOnePlusOne 1
  let h0 := (g.player ⟨0⟩).hand.size
  let g := mustApply g ⟨0⟩ (.activate data.id 0)
  let g := mustApply g ⟨0⟩ .pay
  let g := mustApply g ⟨0⟩ (.choosePermanents #[data.id, ogre.id, bear.id])
  let g := passBoth g
  (namedPermanent g "Lieutenant Commander Data").status.stun == 0 &&
  (namedPermanent g "Gray Ogre").status.minusOneMinusOne == 0 &&
  (namedPermanent g "Grizzly Bears").status.plusOnePlusOne == 0 &&
  (g.player ⟨0⟩).hand.size == h0 + 1

/-!
## 1165, 1167, 1168 — Nyota Uhura, Communications
-/

#guard (trkRuling 1165).comment.contains "include 0 and 10"
#guard (trkRuling 1167).comment.contains "use the value of X to determine if the spell's mana value is the chosen number"
#guard (trkRuling 1168).comment.contains "resolves before the spell that caused it to trigger"
#guard
  -- Ruling 1165: both 0 and 10 are legal choices.
  let g := insertObject trkRulingMain nyotaUhuraCommunications ⟨0⟩ (.hand ⟨0⟩) none
  let g := withBlueMana g ⟨0⟩ 3
  let u := (g.objects.find? (fun o => o.name == "Nyota Uhura, Communications" && o.zone == .hand ⟨0⟩)).get!
  let g := mustApply g ⟨0⟩ (.cast u.id)
  let g := mustApply g ⟨0⟩ .pay
  let gPrompt := passBoth g
  let pick0 := mustApply gPrompt ⟨0⟩ (.chooseMode 0)
  let pick10 := mustApply gPrompt ⟨0⟩ (.chooseMode 10)
  (namedPermanent pick0 "Nyota Uhura, Communications").status.chosenNumber == some 0 &&
  (namedPermanent pick10 "Nyota Uhura, Communications").status.chosenNumber == some 10 &&
  rejects gPrompt ⟨0⟩ (.chooseMode 11)
#guard
  -- Rulings 1167 & 1168: chosen number = 3; opponent casts Khaaaaaaaaaaaannn! ({X}{R}) with X = 2
  -- (MV = 3) -> triggers Nyota Uhura; her draw trigger resolves before the spell even if countered.
  let g := insertObject trkRulingMain nyotaUhuraCommunications ⟨0⟩ (.hand ⟨0⟩) none
  let g := addPermanent g grizzlyBears ⟨0⟩ ⟨0⟩
  let g := withBlueMana g ⟨0⟩ 5
  let u := (g.objects.find? (fun o => o.name == "Nyota Uhura, Communications" && o.zone == .hand ⟨0⟩)).get!
  let g := mustApply g ⟨0⟩ (.cast u.id)
  let g := mustApply g ⟨0⟩ .pay
  let g := passBoth g
  let g := mustApply g ⟨0⟩ (.chooseMode 3)
  let g := insertObject g khaaaaaaaaaaaannn ⟨1⟩ (.hand ⟨1⟩) none
  let g := withRedMana g ⟨1⟩ 3
  let h0 := (g.player ⟨0⟩).hand.size
  let g := mustApply g ⟨0⟩ .pass
  let khan := (g.objects.find? (fun o => o.name == "Khaaaaaaaaaaaannn!" && o.zone == .hand ⟨1⟩)).get!
  let bear := namedPermanent g "Grizzly Bears"
  let g := mustApply g ⟨1⟩ (.cast khan.id)
  let g := mustApply g ⟨1⟩ (.chooseX 2)
  let g := mustApply g ⟨1⟩ (.target (.permanent bear.id))
  let g := mustApply g ⟨1⟩ .pay
  -- Uhura's trigger is on top of stack above Khaaaaaaaaaaaannn!.
  let g := passBoth g
  (g.player ⟨0⟩).hand.size == h0 + 1

/-!
## 1169, 1241 — Romulan Bird-of-Prey & Sarcophagus, Ship of the Dead
-/

#guard (trkRuling 1169).comment.contains "check again as it resolves. If Romulan Bird-of-Prey is a creature"
#guard (trkRuling 1241).comment.contains "If Sarcophagus is a creature at that time"
#guard
  -- Ruling 1169: Romulan Bird-of-Prey triggers when noncreature, doesn't trigger once 8+ charge counters.
  let g := addPermanent trkRulingMain romulanBirdOfPrey ⟨0⟩ ⟨0⟩
  let g := insertObject g lightningBolt ⟨0⟩ (.hand ⟨0⟩) none
  let g := withRedMana g ⟨0⟩ 2
  let bolt := (g.objects.find? (fun o => o.name == "Lightning Bolt" && o.zone == .hand ⟨0⟩)).get!
  let g := mustApply g ⟨0⟩ (.cast bolt.id)
  let g := mustApply g ⟨0⟩ (.target (.player ⟨1⟩))
  let g := mustApply g ⟨0⟩ .pay
  let g := passBoth (passBoth g)
  let triggeredAt0 := (namedPermanent g "Romulan Bird-of-Prey").status.charge == 2
  -- Put to 8 charge counters (now a creature), cast another noncreature spell -> does NOT trigger.
  let ship := namedPermanent g "Romulan Bird-of-Prey"
  let g := g.addCounters ship .charge 6
  let g := insertObject g lightningBolt ⟨0⟩ (.hand ⟨0⟩) none
  let bolt2 := (g.objects.find? (fun o => o.name == "Lightning Bolt" && o.zone == .hand ⟨0⟩)).get!
  let g := mustApply g ⟨0⟩ (.cast bolt2.id)
  let g := mustApply g ⟨0⟩ (.target (.player ⟨1⟩))
  let g := mustApply g ⟨0⟩ .pay
  let g := passBoth g
  triggeredAt0 && (namedPermanent g "Romulan Bird-of-Prey").status.charge == 8

/-!
## 1189 — Assimilate preserves noncreature subtypes
-/

#guard (trkRuling 1189).comment.contains "Artifact Land Creature – Forest Borg"
#guard
  let dryadArbor : CardDef := {
    name := "Dryad Arbor"
    types := #[.land, .creature]
    subtypes := #["Forest", "Dryad"]
    power := some (.fixed 1)
    toughness := some (.fixed 1)
    colorIndicator := some (ColorSet.singleton .green)
  }
  let g := addPermanent trkRulingMain deathIsIrrelevant ⟨0⟩ ⟨0⟩
  let g := insertObject g dryadArbor ⟨1⟩ (.graveyard ⟨1⟩) none
  let g := passBoth (skipTo g .postcombatMain 40)
  let gyDryad := (g.objects.find? (fun o => o.name == "Dryad Arbor" && o.zone == .graveyard ⟨1⟩)).get!
  let g := mustApply g ⟨0⟩ (.target (.card gyDryad.id))
  let g := passBoth g
  let da := namedPermanent g "Dryad Arbor"
  g.isArtifact da && g.isLand da && g.isCreature da &&
  g.hasSubtype da .forest && g.hasSubtype da .borg && !g.hasSubtype da .dryad

/-!
## 1192–1194 — Georgiou, Terran Emperor
-/

#guard (trkRuling 1192).comment.contains "Georgiou leaves the battlefield, you'll lose the game"
#guard (trkRuling 1193).comment.contains "can't pay any amount of life except 0"
#guard (trkRuling 1194).comment.contains "ten or more poison counters"
#guard
  let g := trkGeorgiouSurvives -- life = 0, Georgiou on battlefield
  -- Ruling 1193: cannot pay > 0 life at 0 life.
  let cantPay := !(g.canPayLife ⟨0⟩ 1) && g.canPayLife ⟨0⟩ 0
  -- Ruling 1192: loses immediately when Georgiou leaves battlefield.
  let geo := namedPermanent g "Georgiou, Terran Emperor"
  let gLeft := (g.sacrificeToGraveyard geo "sacrificed").checkSBA
  -- Ruling 1194: still loses to 10 poison counters.
  let gPoison := (g.addPlayerCounters ⟨0⟩ .poison 10).checkSBA
  cantPay && gLeft.over && gPoison.over

/-!
## 1231, 1232 — Lwaxana Troi, Charming Guest
-/

#guard (trkRuling 1231).comment.contains "becomes untapped before her last ability resolves"
#guard (trkRuling 1232).comment.contains "causes the ability to trigger an additional time"
#guard
  -- Ruling 1232: while Lwaxana Troi stays tapped, chosen creature's triggers fire twice.
  let g := addPermanent trkRulingMain lwaxanaTroiCharmingGuest ⟨0⟩ ⟨0⟩
  let g := addPermanent g lieutenantCommanderData ⟨0⟩ ⟨0⟩
  let g := withRedMana g ⟨0⟩ 3
  let lwax := namedPermanent g "Lwaxana Troi, Charming Guest"
  let data := namedPermanent g "Lieutenant Commander Data"
  let g := mustApply g ⟨0⟩ (.activate lwax.id 0)
  let g := mustApply g ⟨0⟩ (.target (.permanent data.id))
  let g := mustApply g ⟨0⟩ .pay
  let g := passBoth g
  -- Cast Lightning Bolt (noncreature) -> Data triggers TWICE (+2 +1/+1 counters).
  let g := insertObject g lightningBolt ⟨0⟩ (.hand ⟨0⟩) none
  let bolt := (g.objects.find? (fun o => o.name == "Lightning Bolt" && o.zone == .hand ⟨0⟩)).get!
  let g := mustApply g ⟨0⟩ (.cast bolt.id)
  let g := mustApply g ⟨0⟩ (.target (.player ⟨1⟩))
  let g := mustApply g ⟨0⟩ .pay
  let g := match g.pending with | .chooseTriggerToStack p => mustApply g p (.stackTriggers #[0, 1]) | _ => g
  let g := passBoth (passBoth (passBoth g))
  (namedPermanent g "Lieutenant Commander Data").status.plusOnePlusOne == 2

#guard
  -- Ruling 1231: if Lwaxana Troi untaps BEFORE her ability resolves, no extra triggers occur.
  let g := addPermanent trkRulingMain lwaxanaTroiCharmingGuest ⟨0⟩ ⟨0⟩
  let g := addPermanent g lieutenantCommanderData ⟨0⟩ ⟨0⟩
  let g := withRedMana g ⟨0⟩ 3
  let lwax := namedPermanent g "Lwaxana Troi, Charming Guest"
  let data := namedPermanent g "Lieutenant Commander Data"
  let g := mustApply g ⟨0⟩ (.activate lwax.id 0)
  let g := mustApply g ⟨0⟩ (.target (.permanent data.id))
  let g := mustApply g ⟨0⟩ .pay
  -- Untap Lwaxana Troi while her ability is still on the stack.
  let g := setTapped g lwax.id false
  let g := passBoth g
  let g := insertObject g lightningBolt ⟨0⟩ (.hand ⟨0⟩) none
  let bolt := (g.objects.find? (fun o => o.name == "Lightning Bolt" && o.zone == .hand ⟨0⟩)).get!
  let g := mustApply g ⟨0⟩ (.cast bolt.id)
  let g := mustApply g ⟨0⟩ (.target (.player ⟨1⟩))
  let g := mustApply g ⟨0⟩ .pay
  let g := passBoth (passBoth g)
  (namedPermanent g "Lieutenant Commander Data").status.plusOnePlusOne == 1

/-!
## 1236, 1237 — Quark, Humble Proprietor
-/

#guard (trkRuling 1236).comment.contains "stops you from sacrificing Treasure tokens for any reason"
#guard (trkRuling 1237).comment.contains "must sacrifice one of those other artifacts"
#guard
  let g := addPermanent trkQuarkSetup engineeredExplosives ⟨0⟩ ⟨0⟩
  let treas := namedPermanent g "Treasure"
  let ee := namedPermanent g "Engineered Explosives"
  -- Rulings 1236 & 1237: cantSacrificeObject blocks Treasure and forces sacrificing other artifacts.
  let gTryTreas := g.sacrificeToGraveyard treas "sacrificed"
  let staysOnBf := gTryTreas.battlefield.any (·.id == treas.id)
  let sacArtEff : Effect := {
    body := .moveZone
      (.inZones .battlefield (.all #[.hasType .artifact, .controlledBy .you]))
      .graveyard .sacrifice
      { choice? := some { chooser := .controller, count := .exact (.const 1) } }
  }
  let gForced := g.applyUnifiedAbility ⟨0⟩ sacArtEff #[] none none none
  let forcedOther := gForced.battlefield.any (·.id == treas.id) &&
    !gForced.battlefield.any (·.id == ee.id)
  staysOnBf && forcedOther && g.cantSacrificeObject ⟨0⟩ treas && !g.cantSacrificeObject ⟨0⟩ ee

/-!
## 1254, 1259, 1281, 1328 — Mana abilities vs. stack abilities
-/

#guard (trkRuling 1254).comment.contains "isn't a mana ability even if the last mode is chosen"
#guard (trkRuling 1259).comment.contains "Jadzia Dax's first ability isn't a mana ability"
#guard (trkRuling 1281).comment.contains "Dal R'El's landfall ability isn't a mana ability"
#guard (trkRuling 1328).comment.contains "Starfleet Academy's last ability is a mana ability"
#guard !culberAndStametsStarCrossed.triggeredAbilities[0]!.isManaAbility
#guard !jadziaDaxLivingLegacy.triggeredAbilities[0]!.isManaAbility
#guard !dalRElAugmentOrphan.triggeredAbilities[0]!.isManaAbility
#guard starfleetAcademy.activatedAbilities[1]!.isManaAbility

/-!
## 1257 — Holo-Engineer
-/

#guard (trkRuling 1257).comment.contains "entirely replaced by a 3/3 colorless Illusion artifact creature token"
#guard
  let g := addPermanent trkRulingMain holoEngineer ⟨0⟩ ⟨0⟩
  -- Creating a tapped Food token (with activated ability) becomes a tapped 3/3 colorless
  -- Illusion artifact creature token with NO activated abilities.
  let (g, tok) := g.createToken ⟨0⟩ Catalog.foodToken (tapped := true)
  let obj := g.object! tok.id
  obj.name == "Illusion" &&
  obj.status.tapped &&
  g.isArtifact obj && g.isCreature obj &&
  g.hasSubtype obj .illusion &&
  !g.hasSubtype obj .food &&
  g.colors obj == ColorSet.empty &&
  g.power obj == 3 && g.toughness obj == 3 &&
  obj.printed.activatedAbilities.isEmpty

/-!
## 1273, 1274 — Warp Speed
-/

#guard (trkRuling 1273).comment.contains "simply put onto the battlefield tapped without a replacement effect"
#guard (trkRuling 1274).comment.contains "enter the battlefield at the same time a land you control would enter"
#guard
  -- Ruling 1273 (part 1): land directly put onto battlefield tapped enters untapped under Warp Speed.
  let g := addPermanent trkRulingMain warpSpeed ⟨0⟩ ⟨0⟩
  let g := enterCard g forest ⟨0⟩ (tapped := true)
  !(namedPermanent g "Forest").status.tapped
#guard
  -- Ruling 1273 (part 2): self-replacement enters-tapped land prompts CR 616.1 choice.
  let g := addPermanent trkRulingMain warpSpeed ⟨0⟩ ⟨0⟩
  let (g, fo) := g.allocObject federationOutpost ⟨0⟩ (.outside ⟨0⟩) none
  let (g, _) := g.putOntoBattlefield fo.id ⟨0⟩ (summoningSick := false)
  match g.pending with
  | .chooseReplacement p _ => p == ⟨0⟩
  | _ => false
#guard
  -- Ruling 1274: Warp Speed entering simultaneously with a tapped land does NOT untap that land.
  let preBf := trkRulingMain.battlefield
  let g := enterCard trkRulingMain warpSpeed ⟨0⟩ (tapped := false) (preBattlefield := some preBf)
  let g := enterCard g forest ⟨0⟩ (tapped := true) (preBattlefield := some preBf)
  (namedPermanent g "Forest").status.tapped

/-!
## 1276 — All Good Things . . . (vacuous truth)
-/

#guard (trkRuling 1276).comment.contains "vacuously true statements"
#guard
  -- Run All Good Things chapter IV with 0, 1, 2 same-type, and 2 distinct-type exiled cards.
  let runCh4 (exiled : Array CardDef) : Int :=
    let g := addPermanent trkRulingMain allGoodThings ⟨0⟩ ⟨0⟩
    let saga := namedPermanent g "All Good Things . . ."
    let g := exiled.foldl (fun g c =>
      let (g, o) := g.allocObject c ⟨0⟩ .exile none
      g.changeObject saga.id (.pushLinkedExile o.id)) g
    let ch4 := allGoodThings.triggeredAbilities.find? (fun t => t.chapterNumbers?.any (·.contains 4))
    let g := g.applyUnifiedAbility ⟨0⟩ ch4.get!.effect #[] (some saga.id) none none
    (g.player ⟨0⟩).life
  runCh4 #[] == 30 &&
  runCh4 #[grizzlyBears] == 30 &&
  runCh4 #[grizzlyBears, grayOgre] == 30 &&
  runCh4 #[grizzlyBears, lightningBolt] == 20

/-!
## 1278, 920 — The City on the Edge of Forever
-/

#guard (trkRuling 1278).comment.contains "Permanents can't phase in"
#guard (trkRuling 920).comment.contains "Phasing out doesn't cause any \"leaves the battlefield\" abilities"
#guard
  -- Chapter I phases out creatures/artifacts and creates the 0/1 Human token preventing phasing in.
  let g := addPermanent trkRulingMain grayOgre ⟨0⟩ ⟨0⟩
  let ogreId := (namedPermanent g "Gray Ogre").id
  let g := insertObject g theCityOnTheEdgeOfForever ⟨0⟩ (.hand ⟨0⟩) none
  let g := (withWhiteMana g ⟨0⟩ 4).addMana ⟨0⟩ (.colored .black) 1
  let city := (g.objects.find? (fun o => o.name == "The City on the Edge of Forever" && o.zone == .hand ⟨0⟩)).get!
  let g := mustApply g ⟨0⟩ (.cast city.id)
  let g := mustApply g ⟨0⟩ .pay
  let g := passBoth (passBoth g) -- resolves Saga + Chapter I trigger
  let ogrePhased := (g.object! ogreId).status.phasedOut
  let hasToken := g.battlefield.any (fun o => o.name == "Human" && o.printed.isToken)
  -- Next untap step for player 0: Gray Ogre STILL phased out while the Human token is on battlefield.
  let gUntap1 := g.beginStep .untap
  let stillPhased := (gUntap1.object! ogreId).status.phasedOut
  -- Remove the Human token, then next untap step: Gray Ogre phases back in!
  let tok := (gUntap1.battlefield.find? (fun o => o.name == "Human" && o.printed.isToken)).get!
  let gUntap2 := (gUntap1.sacrificeToGraveyard tok "sacrificed").beginStep .untap
  let phasedIn := (gUntap2.object! ogreId).zone == .battlefield && !(gUntap2.object! ogreId).status.phasedOut
  ogrePhased && hasToken && stillPhased && phasedIn

/-!
## 1295 — Live Long and Prosper & Deep Space Scan
-/

#guard (trkRuling 1295).comment.contains "If your life total is negative, lose that much life"
#guard
  -- Positive life doubles via life gain (20 -> 40) + no maximum hand size until next turn.
  let g := insertObject trkRulingMain liveLongAndProsper ⟨0⟩ (.hand ⟨0⟩) none
  let g := (withWhiteMana g ⟨0⟩ 6).addMana ⟨0⟩ (.colored .blue) 1
  let llap := (g.objects.find? (fun o => o.name == "Live Long and Prosper" && o.zone == .hand ⟨0⟩)).get!
  let g := mustApply g ⟨0⟩ (.cast llap.id)
  let g := mustApply g ⟨0⟩ .pay
  let g := passBoth g
  let posOk := (g.player ⟨0⟩).life == 40 && g.effectiveMaxHandSize ⟨0⟩ == none
  -- Negative life (-5 -> -10) with Georgiou doubles downward via life loss (not life gain!).
  let gNeg := addPermanent trkRulingMain georgiouTerranEmperor ⟨0⟩ ⟨0⟩
  let gNeg := gNeg.setLifeTotal ⟨0⟩ (-5)
  let gNeg := insertObject gNeg liveLongAndProsper ⟨0⟩ (.hand ⟨0⟩) none
  let gNeg := (withWhiteMana gNeg ⟨0⟩ 6).addMana ⟨0⟩ (.colored .blue) 1
  let llap2 := (gNeg.objects.find? (fun o => o.name == "Live Long and Prosper" && o.zone == .hand ⟨0⟩)).get!
  let gNeg := mustApply gNeg ⟨0⟩ (.cast llap2.id)
  let gNeg := mustApply gNeg ⟨0⟩ .pay
  let gNeg := passBoth gNeg
  let negOk := (gNeg.player ⟨0⟩).life == -10 &&
    gNeg.events.any (fun e => match e.change with | .rules (.life (.lost p amt _ _)) => p == ⟨0⟩ && amt == 5 | _ => false)
  posOk && negOk

/-!
## 1297 — Mirror Universe Intrusion
-/

#guard (trkRuling 1297).comment.contains "targets an opponent and doesn't target any creatures"
#guard
  let g := addPermanent trkRulingMain grayOgre ⟨1⟩ ⟨1⟩
  let g := addPermanent g grizzlyBears ⟨1⟩ ⟨1⟩
  let g := insertObject g mirrorUniverseIntrusion ⟨0⟩ (.hand ⟨0⟩) none
  let g := (withBlueMana g ⟨0⟩ 7).addMana ⟨0⟩ (.colored .black) 2
  let mui := (g.objects.find? (fun o => o.name == "Mirror Universe Intrusion" && o.zone == .hand ⟨0⟩)).get!
  let g := mustApply g ⟨0⟩ (.cast mui.id)
  let g := mustApply g ⟨0⟩ (.announceKicker true)
  -- Must target an opponent (player 1), not a creature.
  let ogre := namedPermanent g "Gray Ogre"
  let rejectsCreature := rejects g ⟨0⟩ (.target (.permanent ogre.id))
  let g := mustApply g ⟨0⟩ (.target (.player ⟨1⟩))
  let g := mustApply g ⟨0⟩ .pay
  let g := passBoth g
  let copiedOgre := g.battlefield.any (fun o => o.name == "Gray Ogre" && g.controlledBy o ⟨0⟩ && o.printed.isToken && g.hasMenace o)
  let copiedBear := g.battlefield.any (fun o => o.name == "Grizzly Bears" && g.controlledBy o ⟨0⟩ && o.printed.isToken && g.hasMenace o)
  rejectsCreature && copiedOgre && copiedBear

/-!
## 1299–1302 — Nog, Ambitious Cadet
-/

#guard (trkRuling 1299).comment.contains "None of Nog's activated abilities have a duration"
#guard (trkRuling 1300).comment.contains "regardless of what creature types he is"
#guard (trkRuling 1301).comment.contains "checks whether he's a Rogue"
#guard
  let g := addPermanent trkRulingMain nogAmbitiousCadet ⟨0⟩ ⟨0⟩
  let g := withGreenMana g ⟨0⟩ 7
  let nog := namedPermanent g "Nog, Ambitious Cadet"
  -- Ruling 1300: can activate ability 1 ({3}, Scout check) even while Nog is a Rogue -> does nothing.
  let gNoop := mustApply g ⟨0⟩ (.activate nog.id 1)
  let gNoop := mustApply gNoop ⟨0⟩ .pay
  let gNoop := passBoth gNoop
  let stillRogue := gNoop.hasSubtype (namedPermanent gNoop "Nog, Ambitious Cadet") .rogue &&
    !gNoop.hasSubtype (namedPermanent gNoop "Nog, Ambitious Cadet") .officer
  -- Activate ability 0 ({1}) -> becomes 3/4 Ferengi Scout indefinitely; then ability 1 ({3}) -> Officer.
  let gScout := mustApply gNoop ⟨0⟩ (.activate nog.id 0)
  let gScout := mustApply gScout ⟨0⟩ .pay
  let gScout := passBoth gScout
  let n1 := namedPermanent gScout "Nog, Ambitious Cadet"
  let isScout := gScout.hasSubtype n1 .scout && gScout.power n1 == 3 && gScout.toughness n1 == 4
  let gOff := mustApply gScout ⟨0⟩ (.activate nog.id 1)
  let gOff := mustApply gOff ⟨0⟩ .pay
  let gOff := passBoth gOff
  -- Advance to next turn: indefinite effects still hold (ruling 1299).
  let gNext := skipTo (toNextUpkeep gOff) .precombatMain 40
  let n2 := namedPermanent gNext "Nog, Ambitious Cadet"
  stillRogue && isScout && gNext.hasSubtype n2 .officer && gNext.power n2 == 3 && gNext.toughness n2 == 4

/-!
## 1162, 1187, 1251, 1305, 1311, 1312, 1322 — Sunburst, Shocklands, CDAs & Draw Doubling
-/

#guard (trkRuling 1162).comment.contains "doubles each card draw"
#guard (trkRuling 1187).comment.contains "applies in all zones"
#guard (trkRuling 1251).comment.contains "applies in all zones"
#guard (trkRuling 1305).comment.contains "applies in all zones"
#guard (trkRuling 1311).comment.contains "choose any value for X"
#guard (trkRuling 1312).comment.contains "Colorless mana won't give Engineered Explosives another charge counter"
#guard (trkRuling 1322).comment.contains "you may pay 2 life, but it still enters tapped"

-- Ruling 1312: Sunburst with {C}{R} for X = 2 enters with 1 charge counter (colorless is not a color).
#guard
  let g := insertObject trkRulingMain engineeredExplosives ⟨0⟩ (.hand ⟨0⟩) none
  let g := (g.addMana ⟨0⟩ .colorless 1).addMana ⟨0⟩ (.colored .red) 1
  let ee := (g.objects.find? (fun o => o.name == "Engineered Explosives" && o.zone == .hand ⟨0⟩)).get!
  let g := mustApply g ⟨0⟩ (.cast ee.id)
  let g := mustApply g ⟨0⟩ (.chooseX 2)
  let g := mustApply g ⟨0⟩ .pay
  let g := passBoth g
  (namedPermanent g "Engineered Explosives").status.charge == 1

-- Ruling 1322: shockland put onto battlefield tapped still enters tapped even if 2 life is paid.
#guard
  let g := enterCard trkRulingMain templeGarden ⟨0⟩ (tapped := true)
  let g :=
    match g.pending with
    | .chooseReplacement p choices =>
      match choices.find? (fun rid => match rid.kind with | .entersUntappedPayLife _ => true | _ => false) with
      | some payRid => mustApply g p (.chooseReplacement payRid)
      | none => g
    | _ => g
  (g.player ⟨0⟩).life == 18 && (namedPermanent g "Temple Garden").status.tapped

-- Ruling 1162: Mr. Spock doubles multi-card draws.
#guard
  let g := addPermanent trkRulingMain mrSpockScienceOfficer ⟨0⟩ ⟨0⟩
  let h0 := (g.player ⟨0⟩).hand.size
  let g := g.draw ⟨0⟩ 3
  (g.player ⟨0⟩).hand.size == h0 + 6

-- Rulings 1187, 1251, 1305: CDAs of Collective Drone, Captain Pike, and The Traveler apply in hand/graveyard.
#guard
  let g := addPermanent trkRulingMain plains ⟨0⟩ ⟨0⟩
  let g := addPermanent g island ⟨0⟩ ⟨0⟩
  let g := addPermanent g lieutenantCommanderData ⟨0⟩ ⟨0⟩ -- 1 artifact creature
  let g := insertObject g collectiveDrone ⟨0⟩ (.hand ⟨0⟩) none
  let g := insertObject g captainPikeFullnessOfTime ⟨0⟩ (.graveyard ⟨0⟩) none
  let g := insertObject g theTraveler ⟨0⟩ (.hand ⟨0⟩) none
  let drone := (g.objects.find? (·.name == "Collective Drone")).get!
  let pike := (g.objects.find? (·.name == "Captain Pike, Fullness of Time")).get!
  let trav := (g.objects.find? (·.name == "The Traveler")).get!
  g.power drone == 1 && g.power pike == 2 && g.toughness pike == 2 && g.power trav == 2

end Mtg.Engine.TrkRulingTests
