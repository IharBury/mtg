import Mtg.Engine.Catalog.StarTrek
import Mtg.Engine.Game
import Mtg.Engine.Tests.Auras
import Mtg.Engine.Tests.Helpers

/-!
# Star Trek (TRK)

Runtime gameplay tests for the TRK set mechanics:
- Station & Spacecraft threshold layers (CR 702.184 / 722.2)
- Beam me up alternative cost from graveyard & exile on leave stack (CR 702.196a–b)
- Facing a dilemma trigger & single-dilemma counting for multi-mode spells (CR 700.17)
- Assimilate from graveyard onto battlefield as a Borg artifact creature (CR 701.72a–b)
- Discover (CR 701.57a) cast-for-free and decline-to-hand paths
- Sunburst distinct-color charge counters (CR 702.44)
- Strange new worlds distinct land names (`Species 8472`)
- Static/replacement rules: `Georgiou`, `Quark`, `Pet Sehlat`, `Nyota Uhura`,
  `The Needs of the Many`, `Dr. McCoy, Surly Surgeon`, and `Marooned`
-/

namespace Mtg.Engine.Tests

open Mtg.Engine
open Mtg.Engine.Catalog

private def trkMain : Game :=
  skipTo started .precombatMain 40

/-! ### 1. Station & Spacecraft (CR 702.184 / 722.2) -/

/-- Before reaching 7+ charge counters, *U.S.S. Enterprise-D, Galaxy-Class* is an
artifact Spacecraft and not a creature. -/
def trkStationSetup : Game :=
  let g := addPermanent trkMain ussEnterpriseDGalaxyClass ⟨0⟩ ⟨0⟩
  let g := addPermanent g (creature "Vulcan Guard" ManaCost.empty #[] 4 4) ⟨0⟩ ⟨0⟩
  addPermanent g (creature "Andorian Officer" ManaCost.empty #[] 3 3) ⟨0⟩ ⟨0⟩

#guard !trkStationSetup.isCreature (namedPermanent trkStationSetup "U.S.S. Enterprise-D, Galaxy-Class")
#guard trkStationSetup.isArtifact (namedPermanent trkStationSetup "U.S.S. Enterprise-D, Galaxy-Class")
#guard !trkStationSetup.hasFlying (namedPermanent trkStationSetup "U.S.S. Enterprise-D, Galaxy-Class")

/-- First Station activation taps the 4/4 Vulcan Guard, puts 4 charge counters on
Enterprise-D (still noncreature at 4 < 7), and triggers its first-charge-counter
exile-top-card ability. -/
def trkAfterStation1 : Game :=
  let ent := namedPermanent trkStationSetup "U.S.S. Enterprise-D, Galaxy-Class"
  let guard := namedPermanent trkStationSetup "Vulcan Guard"
  let g := mustApply trkStationSetup ⟨0⟩ (.activate ent.id 0)
  let g := if g.pending == .activateManaAbilities ⟨0⟩ then mustApply g ⟨0⟩ .pay else g
  let g := mustApply g ⟨0⟩ (.choosePermanents #[guard.id])
  -- Resolve Station ability, then resolve the charge-counter trigger.
  passBoth (passBoth g)

#guard (namedPermanent trkAfterStation1 "U.S.S. Enterprise-D, Galaxy-Class").status.charge == 4
#guard (namedPermanent trkAfterStation1 "Vulcan Guard").status.tapped
#guard !trkAfterStation1.isCreature (namedPermanent trkAfterStation1 "U.S.S. Enterprise-D, Galaxy-Class")

/-- Second Station activation taps the 3/3 Andorian Officer, bringing Enterprise-D
to 7 charge counters: CR 722.2 makes it a 4/5 artifact creature with flying and vigilance. -/
def trkAfterStation2 : Game :=
  let ent := namedPermanent trkAfterStation1 "U.S.S. Enterprise-D, Galaxy-Class"
  let off := namedPermanent trkAfterStation1 "Andorian Officer"
  let g := mustApply trkAfterStation1 ⟨0⟩ (.activate ent.id 0)
  let g := if g.pending == .activateManaAbilities ⟨0⟩ then mustApply g ⟨0⟩ .pay else g
  let g := mustApply g ⟨0⟩ (.choosePermanents #[off.id])
  passBoth g

#guard (namedPermanent trkAfterStation2 "U.S.S. Enterprise-D, Galaxy-Class").status.charge == 7
#guard trkAfterStation2.isCreature (namedPermanent trkAfterStation2 "U.S.S. Enterprise-D, Galaxy-Class")
#guard trkAfterStation2.power (namedPermanent trkAfterStation2 "U.S.S. Enterprise-D, Galaxy-Class") == 4
#guard trkAfterStation2.toughness (namedPermanent trkAfterStation2 "U.S.S. Enterprise-D, Galaxy-Class") == 5
#guard trkAfterStation2.hasFlying (namedPermanent trkAfterStation2 "U.S.S. Enterprise-D, Galaxy-Class")
#guard trkAfterStation2.hasVigilance (namedPermanent trkAfterStation2 "U.S.S. Enterprise-D, Galaxy-Class")

/-! ### 2. Beam me up (CR 702.196a–b), Marooned & Scotty -/

/-- Casting *Federation Resupply* from the graveyard via Beam me up returns the chosen
creature to its owner's hand and exiles the spell when it leaves the stack. -/
def trkBeamSetup : Game :=
  let g := addPermanent trkMain grayOgre ⟨0⟩ ⟨0⟩
  let g := insertObject g federationResupply ⟨0⟩ (.graveyard ⟨0⟩) none
  withWhiteMana g ⟨0⟩ 4

def trkBeamResolved : Game :=
  let ogre := namedPermanent trkBeamSetup "Gray Ogre"
  let resupply := (trkBeamSetup.objects.find? (fun o => o.name == "Federation Resupply")).get!
  let g := mustApply trkBeamSetup ⟨0⟩ (.castWithBeamMeUp resupply.id ogre.id)
  let g := mustApply g ⟨0⟩ .pay
  let g := passBoth g
  -- Decline search (no Aura/Equipment/Spacecraft in testRedDeck) if prompted.
  if g.pending != .none then mustApply g ⟨0⟩ .decline else g

#guard !trkBeamResolved.battlefield.any (·.name == "Gray Ogre")
#guard trkBeamResolved.objects.any (fun o => o.name == "Gray Ogre" && o.zone == .hand ⟨0⟩)
#guard trkBeamResolved.objects.any (fun o => o.name == "Federation Resupply" && o.zone == .exile)
#guard !trkBeamResolved.objects.any (fun o => o.name == "Federation Resupply" && o.zone == .graveyard ⟨0⟩)

/-- *Marooned* prevents the enchanted creature from being beamed up. -/
def trkMaroonedSetup : Game :=
  let ogre := namedPermanent trkBeamSetup "Gray Ogre"
  addAttachedAura trkBeamSetup marooned ogre ⟨0⟩ ⟨0⟩

#guard
  let ogre := namedPermanent trkMaroonedSetup "Gray Ogre"
  let resupply := (trkMaroonedSetup.objects.find? (fun o => o.name == "Federation Resupply")).get!
  !(trkMaroonedSetup.apply ⟨0⟩ (.castWithBeamMeUp resupply.id ogre.id)).isOk

/-- *Scotty, Miracle Worker* grants beam me up to instants/sorceries in your graveyard
during your main phase, but Scotty himself can't be beamed up to cast a spell this way. -/
def trkScottySetup : Game :=
  let g := addPermanent trkMain scottyMiracleWorker ⟨0⟩ ⟨0⟩
  let g := addPermanent g grayOgre ⟨0⟩ ⟨0⟩
  let g := insertObject g lightningBolt ⟨0⟩ (.graveyard ⟨0⟩) none
  withRedMana g ⟨0⟩ 1

#guard
  let scotty := namedPermanent trkScottySetup "Scotty, Miracle Worker"
  let bolt := (trkScottySetup.objects.find? (fun o => o.name == "Lightning Bolt" && o.zone == .graveyard ⟨0⟩)).get!
  !(trkScottySetup.apply ⟨0⟩ (.castWithBeamMeUp bolt.id scotty.id)).isOk &&
  !(trkScottySetup.apply ⟨0⟩ (.cast bolt.id)).isOk

def trkScottyBeamed : Game :=
  let ogre := namedPermanent trkScottySetup "Gray Ogre"
  let bolt := (trkScottySetup.objects.find? (fun o => o.name == "Lightning Bolt" && o.zone == .graveyard ⟨0⟩)).get!
  let g := mustApply trkScottySetup ⟨0⟩ (.castWithBeamMeUp bolt.id ogre.id)
  let g := mustApply g ⟨0⟩ (.target (.player ⟨1⟩))
  let g := mustApply g ⟨0⟩ .pay
  passBoth g

#guard (trkScottyBeamed.player ⟨1⟩).life == 17
#guard trkScottyBeamed.objects.any (fun o => o.name == "Gray Ogre" && o.zone == .hand ⟨0⟩)
#guard trkScottyBeamed.objects.any (fun o => o.name == "Lightning Bolt" && o.zone == .exile)

/-! ### 3. Facing a dilemma (CR 700.17) -/

/-- Casting modal *Command Decision* with *Seven of Nine* on the battlefield faces
one dilemma and triggers Seven of Nine's draw ability. -/
def trkDilemmaSetup : Game :=
  let g := addPermanent trkMain sevenOfNine ⟨0⟩ ⟨0⟩
  let g := insertObject g commandDecision ⟨0⟩ (.hand ⟨0⟩) none
  withWhiteMana g ⟨0⟩ 2

def trkDilemmaResolved : Game :=
  let cd := (trkDilemmaSetup.objects.find? (fun o => o.name == "Command Decision")).get!
  let g := mustApply trkDilemmaSetup ⟨0⟩ (.cast cd.id)
  let g := mustApply g ⟨0⟩ (.chooseMode 1) -- "Draw a card."
  let g := mustApply g ⟨0⟩ .pay
  -- Resolve Seven of Nine trigger, then Command Decision.
  passBoth (passBoth g)

#guard GameEvent.dilemmasFaced trkDilemmaResolved.events trkDilemmaResolved.turnNumber ⟨0⟩ == 1
#guard (trkDilemmaResolved.player ⟨0⟩).hand.size == (trkDilemmaSetup.player ⟨0⟩).hand.size + 1

/-- CR 700.17: Choosing TWO modes for a single spell (*Pinecone Strike* choosing both
modes) still counts as facing only ONE dilemma. -/
def trkTwoModeDilemma : Game :=
  let g := addPermanent trkMain sevenOfNine ⟨0⟩ ⟨0⟩
  let g := addPermanent g grayOgre ⟨1⟩ ⟨1⟩
  let g := addPermanent g Catalog.treasureToken ⟨1⟩ ⟨1⟩
  let g := insertObject g pineconeStrike ⟨0⟩ (.hand ⟨0⟩) none
  let g := withRedMana g ⟨0⟩ 2
  let ps := (g.objects.find? (fun o => o.name == "Pinecone Strike")).get!
  let ogre := namedPermanent g "Gray Ogre"
  let treas := namedPermanent g "Treasure"
  let g := mustApply g ⟨0⟩ (.cast ps.id)
  let g := mustApply g ⟨0⟩ (.chooseMode 0)
  let g := mustApply g ⟨0⟩ (.chooseMode 1)
  let g := mustApply g ⟨0⟩ (.target (.permanent ogre.id))
  let g := mustApply g ⟨0⟩ (.target (.permanent treas.id))
  let g := mustApply g ⟨0⟩ .pay
  passBoth (passBoth g)

#guard GameEvent.dilemmasFaced trkTwoModeDilemma.events trkTwoModeDilemma.turnNumber ⟨0⟩ == 1

/-! ### 4. Assimilate (CR 701.72a–b) -/

/-- *Death Is Irrelevant* assimilates a creature card from a graveyard at end step:
enters under your control with a +1/+1 counter as a Borg artifact creature, losing
other creature types. -/
def trkAssimilateResolved : Game :=
  let g := addPermanent trkMain deathIsIrrelevant ⟨0⟩ ⟨0⟩
  let g := insertObject g grayOgre ⟨1⟩ (.graveyard ⟨1⟩) none
  let g := passBoth (skipTo g .postcombatMain 40)
  let gyOgre := (g.objects.find? (fun o => o.name == "Gray Ogre" && o.zone == .graveyard ⟨1⟩)).get!
  let g := mustApply g ⟨0⟩ (.target (.card gyOgre.id))
  passBoth g

#guard trkAssimilateResolved.battlefield.any (fun o =>
  o.name == "Gray Ogre" &&
  trkAssimilateResolved.controlledBy o ⟨0⟩ &&
  o.status.plusOnePlusOne == 1 &&
  trkAssimilateResolved.isArtifact o &&
  trkAssimilateResolved.isCreature o &&
  trkAssimilateResolved.hasSubtype o .borg &&
  !trkAssimilateResolved.hasSubtype o .ogre)

/-! ### 5. Discover (CR 701.57a) -/

/-- *U.S.S. Discovery, at Black Alert* enters and discovers 5: exiles top Forest (land,
skipped) and stops at *Gray Ogre* (nonland, MV 3 ≤ 5). Declining puts Gray Ogre in hand
and puts the missed Forest back on the bottom of the library. -/
def trkDiscoverPrompt : Game :=
  let g := emptyLibrary trkMain ⟨0⟩
  -- Top of library is the last inserted card.
  let g := insertObject g grayOgre ⟨0⟩ (.library ⟨0⟩) none
  let g := insertObject g forest ⟨0⟩ (.library ⟨0⟩) none
  let g := insertObject g ussDiscoveryAtBlackAlert ⟨0⟩ (.hand ⟨0⟩) none
  let g := withGreenMana g ⟨0⟩ 5
  let disc := (g.objects.find? (fun o => o.name == "U.S.S. Discovery, at Black Alert")).get!
  let g := mustApply g ⟨0⟩ (.cast disc.id)
  let g := mustApply g ⟨0⟩ .pay
  -- Resolve Discovery entering, then resolve its ETB discover 5 trigger.
  passBoth (passBoth g)

def trkDiscoverDeclined : Game :=
  mustApply trkDiscoverPrompt ⟨0⟩ .decline

#guard trkDiscoverDeclined.objects.any (fun o => o.name == "Gray Ogre" && o.zone == .hand ⟨0⟩)
#guard trkDiscoverDeclined.objects.any (fun o => o.name == "Forest" && o.zone == .library ⟨0⟩)
#guard !trkDiscoverDeclined.objects.any (fun o => o.name == "Gray Ogre" && o.zone == .exile)

def trkDiscoverCastFree : Game :=
  let hit := (trkDiscoverPrompt.objects.find? (fun o => o.name == "Gray Ogre" && o.zone == .exile)).get!
  let g := mustApply trkDiscoverPrompt ⟨0⟩ (.cast hit.id)
  let g := if g.pending == .activateManaAbilities ⟨0⟩ then mustApply g ⟨0⟩ .pay else g
  passBoth g

#guard trkDiscoverCastFree.battlefield.any (·.name == "Gray Ogre")
#guard trkDiscoverCastFree.objects.any (fun o => o.name == "Forest" && o.zone == .library ⟨0⟩)

/-- CR 701.57a / 107.3b: Discovering an `{X}` spell (*Khaaaaaaaaaaaannn!* `{X}{R}`)
casts it with `X = 0` (never opening `.chooseX`, resulting spell MV 1 ≤ 5). -/
def trkDiscoverXSpellPrompt : Game :=
  let g := emptyLibrary trkMain ⟨0⟩
  let g := addPermanent g grizzlyBears ⟨1⟩ ⟨1⟩
  let g := insertObject g khaaaaaaaaaaaannn ⟨0⟩ (.library ⟨0⟩) none
  let g := insertObject g ussDiscoveryAtBlackAlert ⟨0⟩ (.hand ⟨0⟩) none
  let g := withGreenMana g ⟨0⟩ 5
  let disc := (g.objects.find? (fun o => o.name == "U.S.S. Discovery, at Black Alert")).get!
  let g := mustApply g ⟨0⟩ (.cast disc.id)
  let g := mustApply g ⟨0⟩ .pay
  passBoth (passBoth g)

#guard
  let hit := (trkDiscoverXSpellPrompt.objects.find? (fun o => o.name == "Khaaaaaaaaaaaannn!" && o.zone == .exile)).get!
  let bear := namedPermanent trkDiscoverXSpellPrompt "Grizzly Bears"
  let gCast := mustApply trkDiscoverXSpellPrompt ⟨0⟩ (.cast hit.id)
  let noXPrompt := match gCast.pending with | .chooseTargets _ => true | _ => false
  let gTargeted := mustApply gCast ⟨0⟩ (.target (.permanent bear.id))
  let gStack := if gTargeted.pending == .activateManaAbilities ⟨0⟩ then mustApply gTargeted ⟨0⟩ .pay else gTargeted
  let onStack := gStack.stack.find? (fun e => (gStack.findObject? e.objectId).any (·.name == "Khaaaaaaaaaaaannn!"))
  let mvOk := onStack.any (fun e => (gStack.findObject? e.objectId).any (fun sp => gStack.objectManaValue sp == 1))
  let gRes := passBoth gStack
  noXPrompt && mvOk && (namedPermanent gRes "Grizzly Bears").status.damage == 0

/- CR 701.57a: `.mayCastCards` with `maxManaValue? := some 2` rejects casting a
MV 3 card, and `announceX` under `maxCastManaValue? := some 2` rejects any `X`
making the resulting spell's mana value exceed 2 (`{X}{R}` allows `X = 1`, rejects `X = 2`). -/
#guard
  let g := insertObject trkMain grayOgre ⟨0⟩ .exile none
  let ogre := (g.objects.find? (fun o => o.name == "Gray Ogre" && o.zone == .exile)).get!
  let gPrompt := g.beginResolutionChoice ⟨0⟩ (.mayCastCards #[ogre.id] true false (some 2)) "discover 2"
  let castRejected := !(gPrompt.apply ⟨0⟩ (.cast ogre.id)).isOk
  let defaultDeclines :=
    match Game.defaultChoiceAction gPrompt ⟨0⟩ (.mayCastCards #[ogre.id] true false (some 2)) with
    | .decline => true
    | _ => false
  -- Also verify `announceX` enforces `ProposedSpell.maxCastManaValue? = some 2` on `{X}{R}`:
  let gX := addPermanent trkMain grizzlyBears ⟨1⟩ ⟨1⟩
  let gX := insertObject gX khaaaaaaaaaaaannn ⟨0⟩ .exile none
  let khan := (gX.objects.find? (fun o => o.name == "Khaaaaaaaaaaaannn!" && o.zone == .exile)).get!
  let gX := gX.addMana ⟨0⟩ (.colored .red) 3
  let gXProp := gX.castAsPartOfResolution ⟨0⟩ khan.id (withoutManaCost := false) (maxManaValue? := some 2)
  let xTooHigh := !(gXProp.apply ⟨0⟩ (.chooseX 2)).isOk
  let xLegal := (gXProp.apply ⟨0⟩ (.chooseX 1)).isOk
  castRejected && defaultDeclines && xTooHigh && xLegal

/-! ### 6. Sunburst (CR 702.44) -/

/-- *Engineered Explosives* cast for X = 2 with {W}{U} enters with 2 charge counters;
cast for X = 2 with {R}{R} enters with 1 charge counter. -/
def trkSunburstTwoColors : Game :=
  let g := insertObject trkMain engineeredExplosives ⟨0⟩ (.hand ⟨0⟩) none
  let g := (g.addMana ⟨0⟩ (.colored .white) 1).addMana ⟨0⟩ (.colored .blue) 1
  let ee := (g.objects.find? (fun o => o.name == "Engineered Explosives")).get!
  let g := mustApply g ⟨0⟩ (.cast ee.id)
  let g := mustApply g ⟨0⟩ (.chooseX 2)
  let g := mustApply g ⟨0⟩ .pay
  passBoth g

def trkSunburstOneColor : Game :=
  let g := insertObject trkMain engineeredExplosives ⟨0⟩ (.hand ⟨0⟩) none
  let g := g.addMana ⟨0⟩ (.colored .red) 2
  let ee := (g.objects.find? (fun o => o.name == "Engineered Explosives")).get!
  let g := mustApply g ⟨0⟩ (.cast ee.id)
  let g := mustApply g ⟨0⟩ (.chooseX 2)
  let g := mustApply g ⟨0⟩ .pay
  passBoth g

#guard (namedPermanent trkSunburstTwoColors "Engineered Explosives").status.charge == 2
#guard (namedPermanent trkSunburstOneColor "Engineered Explosives").status.charge == 1

/-- CR 702.44a: Layer 4 type-changing effects (e.g. making a noncreature artifact
a creature during your turn) are ignored when Sunburst chooses +1/+1 counters vs.
charge counters. -/
def trkSunburstIgnoresLayer4 : Game :=
  let animatedSunburst : CardDef := {
    engineeredExplosives with
    name := "Animated Sunburst Relic"
    staticAbilities := #[
      .continuous (some .isYourTurn) { zones := .battlefield, pred := .sameAs .this }
        (.all #[.modifyTypes { mode := .add, types := #[.creature] },
                .setBasePT (some (.const 3)) (some (.const 3))])
    ]
  }
  let g := insertObject trkMain animatedSunburst ⟨0⟩ (.hand ⟨0⟩) none
  let g := (g.addMana ⟨0⟩ (.colored .white) 1).addMana ⟨0⟩ (.colored .blue) 1
  let ee := (g.objects.find? (fun o => o.name == "Animated Sunburst Relic")).get!
  let g := mustApply g ⟨0⟩ (.cast ee.id)
  let g := mustApply g ⟨0⟩ (.chooseX 2)
  let g := mustApply g ⟨0⟩ .pay
  passBoth g

#guard
  let ee := namedPermanent trkSunburstIgnoresLayer4 "Animated Sunburst Relic"
  trkSunburstIgnoresLayer4.isCreature ee && ee.status.charge == 2 && ee.status.plusOnePlusOne == 0

/-- CR 702.44d: Multiple instances of Sunburst each work separately. -/
def trkSunburstTwoInstances : Game :=
  let grantSunburst : CardDef := {
    name := "Sunburst Amplifier"
    types := #[.enchantment]
    staticAbilities := #[
      .continuous none { zones := .battlefield, pred := .all #[.hasType .artifact, .controlledBy .you] }
        (.grantKeywords #[.simple .sunburst])
    ]
  }
  let g := addPermanent trkMain grantSunburst ⟨0⟩ ⟨0⟩
  let g := insertObject g engineeredExplosives ⟨0⟩ (.hand ⟨0⟩) none
  let g := (g.addMana ⟨0⟩ (.colored .white) 1).addMana ⟨0⟩ (.colored .blue) 1
  let ee := (g.objects.find? (fun o => o.name == "Engineered Explosives")).get!
  let g := mustApply g ⟨0⟩ (.cast ee.id)
  let g := mustApply g ⟨0⟩ (.chooseX 2)
  let g := mustApply g ⟨0⟩ .pay
  passBoth g

#guard (namedPermanent trkSunburstTwoInstances "Engineered Explosives").status.charge == 4

/-! ### 7. Strange new worlds (distinct land names) & Species 8472 -/

/-- With 2 Plains, 1 Island, and 1 Forest (4 lands, 3 distinct names), *Species 8472*
gains 3 life on entering. -/
def trkStrangeNewWorlds : Game :=
  let g := addPermanent trkMain plains ⟨0⟩ ⟨0⟩
  let g := addPermanent g plains ⟨0⟩ ⟨0⟩
  let g := addPermanent g island ⟨0⟩ ⟨0⟩
  let g := addPermanent g forest ⟨0⟩ ⟨0⟩
  let g := insertObject g species8472 ⟨0⟩ (.hand ⟨0⟩) none
  let g := withGreenMana g ⟨0⟩ 6
  let sp := (g.objects.find? (fun o => o.name == "Species 8472")).get!
  let g := mustApply g ⟨0⟩ (.cast sp.id)
  let g := mustApply g ⟨0⟩ .pay
  passBoth (passBoth g)

#guard (trkStrangeNewWorlds.player ⟨0⟩).life == 23

/-! ### 8. TRK Static & Replacement Rules -/

/-- *Georgiou, Terran Emperor*: controller does not lose the game at 0 or less life. -/
def trkGeorgiouSurvives : Game :=
  let g := addPermanent trkMain georgiouTerranEmperor ⟨0⟩ ⟨0⟩
  (g.setLifeTotal ⟨0⟩ 0).checkSBA

#guard !trkGeorgiouSurvives.over
#guard (trkGeorgiouSurvives.player ⟨0⟩).life == 0

/-- *Quark, Humble Proprietor*: controller cannot sacrifice a Treasure token for mana. -/
def trkQuarkSetup : Game :=
  let g := addPermanent trkMain quarkHumbleProprietor ⟨0⟩ ⟨0⟩
  addPermanent g Catalog.treasureToken ⟨0⟩ ⟨0⟩

#guard
  let treas := namedPermanent trkQuarkSetup "Treasure"
  !(trkQuarkSetup.apply ⟨0⟩ (.activateManaAbility treas.id 0 #[.colored .red])).isOk

/-- *Pet Sehlat* can't attack alone, but can attack alongside another creature. -/
def trkSehlatCombat : Game :=
  let g := addPermanent trkMain petSehlat ⟨0⟩ ⟨0⟩
  let g := addPermanent g grayOgre ⟨0⟩ ⟨0⟩
  passBoth (skipTo g .beginningOfCombat 40)

#guard
  let sehlat := namedPermanent trkSehlatCombat "Pet Sehlat"
  !(trkSehlatCombat.apply ⟨0⟩ (.declareAttackers #[sehlat.id])).isOk

#guard
  let sehlat := namedPermanent trkSehlatCombat "Pet Sehlat"
  let ogre := namedPermanent trkSehlatCombat "Gray Ogre"
  (trkSehlatCombat.apply ⟨0⟩ (.declareAttackers #[sehlat.id, ogre.id])).isOk

/-- *Nyota Uhura, Communications*: chooses a number 0–10 as she enters; draws a card
whenever an opponent casts a spell with that mana value. -/
def trkUhuraEntered : Game :=
  let g := insertObject trkMain nyotaUhuraCommunications ⟨0⟩ (.hand ⟨0⟩) none
  let g := withBlueMana g ⟨0⟩ 3
  let uhura := (g.objects.find? (fun o => o.name == "Nyota Uhura, Communications")).get!
  let g := mustApply g ⟨0⟩ (.cast uhura.id)
  let g := mustApply g ⟨0⟩ .pay
  let g := passBoth g
  -- Choose number 1 (index 1 in 0..10).
  mustApply g ⟨0⟩ (.chooseMode 1)

#guard (namedPermanent trkUhuraEntered "Nyota Uhura, Communications").status.chosenNumber == some 1

def trkUhuraDraws : Game :=
  -- Pass priority to opponent so opponent casts Lightning Bolt (MV 1).
  let g := insertObject trkUhuraEntered lightningBolt ⟨1⟩ (.hand ⟨1⟩) none
  let g := withRedMana g ⟨1⟩ 1
  let g := mustApply g ⟨0⟩ .pass
  let bolt := (g.objects.find? (fun o => o.name == "Lightning Bolt" && o.zone == .hand ⟨1⟩)).get!
  let g := mustApply g ⟨1⟩ (.cast bolt.id)
  let g := mustApply g ⟨1⟩ (.target (.player ⟨0⟩))
  let g := mustApply g ⟨1⟩ .pay
  -- Resolve Nyota Uhura's draw trigger, then Lightning Bolt.
  passBoth (passBoth g)

#guard (trkUhuraDraws.player ⟨0⟩).hand.size == (trkUhuraEntered.player ⟨0⟩).hand.size + 1

/-- *The Needs of the Many*: prevents all damage that would be dealt to you this turn. -/
def trkNeedsPrevented : Game :=
  let g := addPermanent trkMain grayOgre ⟨0⟩ ⟨0⟩
  let g := insertObject g theNeedsOfTheMany ⟨0⟩ (.hand ⟨0⟩) none
  let g := insertObject g lightningBolt ⟨1⟩ (.hand ⟨1⟩) none
  let g := withWhiteMana g ⟨0⟩ 2
  let g := withRedMana g ⟨1⟩ 1
  let needs := (g.objects.find? (fun o => o.name == "The Needs of the Many")).get!
  let ogre := namedPermanent g "Gray Ogre"
  let g := mustApply g ⟨0⟩ (.cast needs.id)
  let g := mustApply g ⟨0⟩ .pay
  let g := mustApply g ⟨0⟩ (.sacrifice ogre.id)
  let g := passBoth g
  -- Opponent casts Lightning Bolt targeting player 0 (still legal target? Wait: player 0 has hexproof too!
  -- Deal non-targeted damage via Encounter the Unknown mode 1: 2 damage to each creature and each player.)
  let g := insertObject g encounterTheUnknown ⟨1⟩ (.hand ⟨1⟩) none
  let g := withRedMana g ⟨1⟩ 3
  let g := mustApply g ⟨0⟩ .pass
  let enc := (g.objects.find? (fun o => o.name == "Encounter the Unknown")).get!
  let g := mustApply g ⟨1⟩ (.cast enc.id)
  let g := mustApply g ⟨1⟩ (.chooseMode 1)
  let g := mustApply g ⟨1⟩ .pay
  passBoth g

#guard (trkNeedsPrevented.player ⟨0⟩).life == 20
#guard (trkNeedsPrevented.player ⟨1⟩).life == 18

/-- *Dr. McCoy, Surly Surgeon*: if another creature you control with a +1/+1 counter
would be destroyed by lethal damage, remove all +1/+1 counters and heal its damage instead. -/
def trkMcCoySaves : Game :=
  let g := addPermanent trkMain drMcCoySurlySurgeon ⟨0⟩ ⟨0⟩
  let g := addPermanent g grayOgre ⟨0⟩ ⟨0⟩
  let ogre := namedPermanent g "Gray Ogre"
  let g := g.addPlusOnePlusOneTo ogre 1
  let g := setMarkedDamage g ogre.id 3
  g.checkSBA

#guard trkMcCoySaves.battlefield.any (·.name == "Gray Ogre")
#guard (namedPermanent trkMcCoySaves "Gray Ogre").status.plusOnePlusOne == 0
#guard (namedPermanent trkMcCoySaves "Gray Ogre").status.damage == 0

/-! ### 9. Official Gatherer Oracle Text Fidelity -/

#guard hitIt.name == "Hit It!" && hitIt.modellingError?.isNone
#guard allGoodThings.name == "All Good Things . . ." && allGoodThings.modellingError?.isNone
#guard ussEnterpriseDGalaxyClass.power.isNone && ussEnterpriseDGalaxyClass.toughness.isNone

end Mtg.Engine.Tests
