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
import Mtg.Engine.Tests.Combat
import Mtg.Engine.Tests.Removal
import Mtg.Engine.Tests.Abilities

/-!
# Typecycling, menace, cost reductions, and linked exile.
-/

namespace Mtg.Engine.Tests

open Mtg.Engine
open Mtg.Engine.Catalog

/- Typecycling: Oliphaunt Mountaincycling and Troll of Khazad-dûm Swampcycling
(CR 702.29). -/

def oliphauntCycleAbility : ActivatedAbility :=
  oliphaunt.activatedAbilities[0]!

def trollCycleAbility : ActivatedAbility :=
  trollOfKhazadDum.activatedAbilities[0]!

/-- Nonbasic land with the Mountain type; Mountaincycling can find it (CR 305.7). -/
def stompingGround : CardDef :=
  land "Stomping Ground" "" (subtypes := #["Mountain", "Forest"])

#guard isLandTypeCard stompingGround "Mountain"
#guard !isBasicLandCard stompingGround

/-- Isolated library so the search finds a known card. -/
def withOnlyLibrary (g : Game) (p : PlayerId) (cards : Array CardDef) : Game :=
  let g := g.modifyPlayer p (fun pl => { pl with library := #[] })
  cards.foldl (fun g c => addToLibraryTop g c p) g

def oliphauntCycleReady : Game :=
  let g := readyMain (emptyHand afterDraw ⟨0⟩)
  let g := withOnlyLibrary g ⟨0⟩ #[mountain]
  withRedMana (addToHand g oliphaunt ⟨0⟩) ⟨0⟩ 1

#guard oliphauntCycleReady.canActivate ⟨0⟩
  (handCardNamed oliphauntCycleReady ⟨0⟩ "Oliphaunt") oliphauntCycleAbility
#guard !(oliphauntCycleReady.availableMana ⟨0⟩).canPay oliphaunt.manaCost
#guard
  let g := addPermanent afterDraw oliphaunt ⟨0⟩ ⟨0⟩
  !(g.canActivate ⟨0⟩ (namedPermanent g "Oliphaunt") oliphauntCycleAbility)
#guard
  let g := readyMain (addToGraveyard afterDraw oliphaunt ⟨0⟩)
  let g := withRedMana g ⟨0⟩ 1
  !(g.canActivate ⟨0⟩ (namedGraveyardCard g ⟨0⟩ "Oliphaunt") oliphauntCycleAbility)
#guard
  let g := addToHand afterDraw oliphaunt ⟨1⟩
  !(g.canActivate ⟨0⟩ (handCardNamed g ⟨1⟩ "Oliphaunt") oliphauntCycleAbility)

def oliphauntCycled : Game :=
  let g := oliphauntCycleReady
  let src := handCardNamed g ⟨0⟩ "Oliphaunt"
  let g := mustApply g ⟨0⟩ (.activate src.id 0)
  passBoth (mustApply g ⟨0⟩ .pay)

#guard (oliphauntCycled.handObjects ⟨0⟩).any (fun o => o.name == "Mountain")
#guard (oliphauntCycled.player ⟨0⟩).graveyard.any (fun id =>
  (oliphauntCycled.object! id).name == "Oliphaunt")
#guard !(oliphauntCycled.handObjects ⟨0⟩).any (fun o => o.name == "Oliphaunt")
#guard oliphauntCycled.log.any (fun s => mentions s "discards Oliphaunt")
#guard oliphauntCycled.log.any (fun s =>
  mentions s "reveals Mountain and puts it into their hand")
#guard oliphauntCycled.log.any (fun s => mentions s "shuffles their library")
#guard oliphauntCycled.stack.isEmpty

#guard
  match Agent.choose oliphauntCycleReady ⟨0⟩ with
  | some (.activate id 0) =>
    (oliphauntCycleReady.object! id).name == "Oliphaunt"
  | _ => false

/-- Enough mana to cast Oliphaunt: the heuristic casts instead of cycling. -/
def oliphauntCastReady : Game :=
  let g := readyMain (emptyHand afterDraw ⟨0⟩)
  withRedMana (addToHand g oliphaunt ⟨0⟩) ⟨0⟩ 6

#guard oliphauntCastReady.canCast ⟨0⟩
  (handCardNamed oliphauntCastReady ⟨0⟩ "Oliphaunt")
#guard
  match Agent.choose oliphauntCastReady ⟨0⟩ with
  | some (.cast id) => (oliphauntCastReady.object! id).name == "Oliphaunt"
  | _ => false

/-- No Mountain in the library: still discard and shuffle. -/
def oliphauntCycleMiss : Game :=
  let g := readyMain (emptyHand afterDraw ⟨0⟩)
  let g := withOnlyLibrary g ⟨0⟩ #[forest]
  let g := withRedMana (addToHand g oliphaunt ⟨0⟩) ⟨0⟩ 1
  let src := handCardNamed g ⟨0⟩ "Oliphaunt"
  let g := mustApply g ⟨0⟩ (.activate src.id 0)
  passBoth (mustApply g ⟨0⟩ .pay)

#guard oliphauntCycleMiss.log.any (fun s => mentions s "finds no Mountain card")
#guard oliphauntCycleMiss.log.any (fun s => mentions s "shuffles their library")
#guard (oliphauntCycleMiss.player ⟨0⟩).graveyard.any (fun id =>
  (oliphauntCycleMiss.object! id).name == "Oliphaunt")
#guard !(oliphauntCycleMiss.handObjects ⟨0⟩).any (fun o => o.name == "Mountain")

/-- A nonbasic Mountain is a legal find (CR 305.7). -/
def oliphauntCycleNonbasic : Game :=
  let g := readyMain (emptyHand afterDraw ⟨0⟩)
  let g := withOnlyLibrary g ⟨0⟩ #[stompingGround]
  let g := withRedMana (addToHand g oliphaunt ⟨0⟩) ⟨0⟩ 1
  let src := handCardNamed g ⟨0⟩ "Oliphaunt"
  let g := mustApply g ⟨0⟩ (.activate src.id 0)
  passBoth (mustApply g ⟨0⟩ .pay)

#guard (oliphauntCycleNonbasic.handObjects ⟨0⟩).any (fun o =>
  o.name == "Stomping Ground")
#guard oliphauntCycleNonbasic.log.any (fun s =>
  mentions s "reveals Stomping Ground and puts it into their hand")

/-- Typecycling is instant-speed (CR 702.29 / 117.1). -/
def oliphauntCycleAtEnd : Game :=
  let g := applyIdle (passBoth (skipTo afterDraw .end 80))
  let g := emptyHand g ⟨0⟩
  let g := withOnlyLibrary g ⟨0⟩ #[mountain]
  withRedMana (addToHand g oliphaunt ⟨0⟩) ⟨0⟩ 1

#guard !oliphauntCycleAtEnd.asSorcery? ⟨0⟩
#guard oliphauntCycleAtEnd.canActivate ⟨0⟩
  (handCardNamed oliphauntCycleAtEnd ⟨0⟩ "Oliphaunt") oliphauntCycleAbility
#guard !oliphauntCycleAtEnd.canCast ⟨0⟩
  (handCardNamed oliphauntCycleAtEnd ⟨0⟩ "Oliphaunt")

def trollCycleReady : Game :=
  let g := readyMain (emptyHand afterDraw ⟨0⟩)
  let g := withOnlyLibrary g ⟨0⟩ #[swamp]
  withBlackMana (addToHand g trollOfKhazadDum ⟨0⟩) ⟨0⟩ 1

#guard trollCycleReady.canActivate ⟨0⟩
  (handCardNamed trollCycleReady ⟨0⟩ "Troll of Khazad-dûm") trollCycleAbility
#guard !(trollCycleReady.availableMana ⟨0⟩).canPay trollOfKhazadDum.manaCost
#guard
  let g := addPermanent afterDraw trollOfKhazadDum ⟨0⟩ ⟨0⟩
  !(g.canActivate ⟨0⟩ (namedPermanent g "Troll of Khazad-dûm") trollCycleAbility)

def trollCycled : Game :=
  let g := trollCycleReady
  let src := handCardNamed g ⟨0⟩ "Troll of Khazad-dûm"
  let g := mustApply g ⟨0⟩ (.activate src.id 0)
  passBoth (mustApply g ⟨0⟩ .pay)

#guard (trollCycled.handObjects ⟨0⟩).any (fun o => o.name == "Swamp")
#guard (trollCycled.player ⟨0⟩).graveyard.any (fun id =>
  (trollCycled.object! id).name == "Troll of Khazad-dûm")
#guard trollCycled.log.any (fun s => mentions s "discards Troll of Khazad-dûm")
#guard trollCycled.log.any (fun s =>
  mentions s "reveals Swamp and puts it into their hand")
#guard trollCycled.log.any (fun s => mentions s "shuffles their library")
#guard
  match Agent.choose trollCycleReady ⟨0⟩ with
  | some (.activate id 0) =>
    (trollCycleReady.object! id).name == "Troll of Khazad-dûm"
  | _ => false

/- Gollum, Silent Slinker: menace (CR 702.111 / 509.1c). -/

#guard gollumSilentSlinker.keywords.menace
#guard gollumSilentSlinker.power == some 4
#guard gollumSilentSlinker.toughness == some 3
#guard withGollum.hasMenace (namedPermanent withGollum "Gollum, Silent Slinker")
#guard (withGollum.effectiveKeywords (namedPermanent withGollum "Gollum, Silent Slinker")).menace
#guard withGollum.legalBlockerCount
  (namedPermanent withGollum "Gollum, Silent Slinker") 0
#guard !withGollum.legalBlockerCount
  (namedPermanent withGollum "Gollum, Silent Slinker") 1
#guard withGollum.legalBlockerCount
  (namedPermanent withGollum "Gollum, Silent Slinker") 2
#guard withGollum.legalBlockerCount
  (namedPermanent withGollum "Gollum, Silent Slinker") 3

/-- Chandra's Gollum attacks; Nissa has one Grizzly Bears. Pairwise blocking
is legal, but a one-blocker declaration is not. -/
def gollumVsOneBear : Game :=
  addPermanent (addPermanent started gollumSilentSlinker ⟨0⟩ ⟨0⟩) grizzlyBears ⟨1⟩ ⟨1⟩

def gollumVsOneBearReadyToBlock : Game :=
  let g := passBoth (skipTo gollumVsOneBear .beginningOfCombat 80)
  let g := mustApply g ⟨0⟩ (.declareAttackers #[(namedPermanent g "Gollum, Silent Slinker").id])
  passBoth g

#guard gollumVsOneBearReadyToBlock.pending == .declareBlockers
#guard
  let g := gollumVsOneBearReadyToBlock
  g.canBlock (namedPermanent g "Grizzly Bears")
    (namedPermanent g "Gollum, Silent Slinker")
#guard
  match gollumVsOneBearReadyToBlock.apply ⟨1⟩ (.declareBlockers #[(
    (namedPermanent gollumVsOneBearReadyToBlock "Grizzly Bears").id,
    (namedPermanent gollumVsOneBearReadyToBlock "Gollum, Silent Slinker").id)]) with
  | .error msg => mentions msg "can't be blocked except by two or more creatures"
  | .ok _ => false

def gollumUnblockedDamage : Game :=
  passBoth (mustApply gollumVsOneBearReadyToBlock ⟨1⟩ (.declareBlockers #[]))

#guard (gollumUnblockedDamage.player ⟨1⟩).life == 16
#guard gollumUnblockedDamage.log.any (fun s =>
  mentions s "Gollum, Silent Slinker deals 4 combat damage to Nissa")
#guard !gollumUnblockedDamage.log.any (fun s =>
  mentions s "Grizzly Bears blocks Gollum, Silent Slinker")

/-- Two Bears can block Gollum. -/
def gollumVsTwoBears : Game :=
  addPermanent gollumVsOneBear grizzlyBears ⟨1⟩ ⟨1⟩

def gollumVsTwoBearsReadyToBlock : Game :=
  let g := passBoth (skipTo gollumVsTwoBears .beginningOfCombat 80)
  let g := mustApply g ⟨0⟩ (.declareAttackers #[(namedPermanent g "Gollum, Silent Slinker").id])
  passBoth g

#guard
  let g := gollumVsTwoBearsReadyToBlock
  let bears := g.battlefield.filter (fun o => o.name == "Grizzly Bears")
  g.canBlock bears[0]! (namedPermanent g "Gollum, Silent Slinker") &&
    g.canBlock bears[1]! (namedPermanent g "Gollum, Silent Slinker")

def twoBearsBlockGollum : Game :=
  let g := gollumVsTwoBearsReadyToBlock
  let gollum := namedPermanent g "Gollum, Silent Slinker"
  let bears := g.battlefield.filter (fun o => o.name == "Grizzly Bears")
  mustApply g ⟨1⟩ (.declareBlockers #[(bears[0]!.id, gollum.id), (bears[1]!.id, gollum.id)])

#guard (namedPermanent twoBearsBlockGollum "Gollum, Silent Slinker").status.blocked
#guard (twoBearsBlockGollum.battlefield.filter (fun o =>
  o.name == "Grizzly Bears" && o.status.blocking ==
    #[(namedPermanent twoBearsBlockGollum "Gollum, Silent Slinker").id])).size == 2
#guard twoBearsBlockGollum.log.any (fun s =>
  mentions s "Grizzly Bears blocks Gollum, Silent Slinker")
#guard twoBearsBlockGollum.legalBlockerCount
  (namedPermanent twoBearsBlockGollum "Gollum, Silent Slinker")
  (twoBearsBlockGollum.blockersOf
    (namedPermanent twoBearsBlockGollum "Gollum, Silent Slinker").id).size

/-- Combat damage goes to the blockers, not the defending player. -/
def afterGollumBlockedDamage : Game :=
  let g := passBoth twoBearsBlockGollum
  mustApply g ⟨0⟩ (.assignCombatDamage #[])

#guard (afterGollumBlockedDamage.player ⟨1⟩).life == 20
#guard afterGollumBlockedDamage.log.any (fun s =>
  mentions s "Gollum, Silent Slinker deals 4 combat damage to Grizzly Bears")
#guard !afterGollumBlockedDamage.log.any (fun s =>
  mentions s "deals 4 combat damage to Nissa")

/-- Gollum and Gray Ogre attack; one Bear blocks the Ogre rather than
illegally solo-blocking Gollum. -/
def gollumAndOgreVsOneBear : Game :=
  addPermanent gollumVsOneBear grayOgre ⟨0⟩ ⟨0⟩

def gollumAndOgreVsOneBearReadyToBlock : Game :=
  let g := passBoth (skipTo gollumAndOgreVsOneBear .beginningOfCombat 80)
  let gollum := namedPermanent g "Gollum, Silent Slinker"
  let ogre := namedPermanent g "Gray Ogre"
  let g := mustApply g ⟨0⟩ (.declareAttackers #[gollum.id, ogre.id])
  passBoth g

/-- Until-end-of-turn menace uses the same declaration restriction. -/
def ogreGrantedMenaceReadyToBlock : Game :=
  let g := readyToDeclareBlockers
  let ogre := namedPermanent g "Gray Ogre"
  g.setObject { ogre with status := ogre.status.grantUntilEot Keyword.menace }

#guard ogreGrantedMenaceReadyToBlock.hasMenace
  (namedPermanent ogreGrantedMenaceReadyToBlock "Gray Ogre")
#guard
  match ogreGrantedMenaceReadyToBlock.apply ⟨1⟩ (.declareBlockers #[(
    (namedPermanent ogreGrantedMenaceReadyToBlock "Grizzly Bears").id,
    (namedPermanent ogreGrantedMenaceReadyToBlock "Gray Ogre").id)]) with
  | .error msg => mentions msg "can't be blocked except by two or more creatures"
  | .ok _ => false

/- Bilbo's Deadly Slice: destroy target creature (CR 701.8 / 701.7b / 608.2b). -/

#guard bilbosDeadlySlice.isInstant
#guard !bilbosDeadlySlice.hasSorcerySpeed
#guard bilbosDeadlySlice.hasInstantSpeed
#guard bilbosDeadlySlice.spellEffect == some (Effect.destroyCreature)
#guard bilbosDeadlySlice.hasCastKind .destroyCreature
#guard bilbosDeadlySlice.requiresTarget
#guard mentions bilbosDeadlySlice.summary "Destroy target creature"

/-- Bilbo's Deadly Slice in hand, an opposing Grizzly Bears, enough mana. -/
def bilbosDeadlySliceSetup : Game :=
  let g := addPermanent afterDraw grizzlyBears ⟨1⟩ ⟨1⟩
  withBlackMana (addToHand g bilbosDeadlySlice ⟨0⟩) ⟨0⟩ 3

#guard bilbosDeadlySliceSetup.canCast ⟨0⟩
  (handCardNamed bilbosDeadlySliceSetup ⟨0⟩ "Bilbo's Deadly Slice")
#guard
  (bilbosDeadlySliceSetup.legalTargets ⟨0⟩ (Effect.destroyCreature)).contains
    (Target.permanent (namedPermanent bilbosDeadlySliceSetup "Grizzly Bears").id)

-- Cannot cast with no creature.
#guard
  let g := withBlackMana (addToHand afterDraw bilbosDeadlySlice ⟨0⟩) ⟨0⟩ 3
  !g.canCast ⟨0⟩ (handCardNamed g ⟨0⟩ "Bilbo's Deadly Slice")
#guard
  let g := addPermanent afterDraw forest ⟨1⟩ ⟨1⟩
  let g := withBlackMana (addToHand g bilbosDeadlySlice ⟨0⟩) ⟨0⟩ 3
  !g.canCast ⟨0⟩ (handCardNamed g ⟨0⟩ "Bilbo's Deadly Slice")
#guard
  let g := withBlackMana (addToHand afterDraw bilbosDeadlySlice ⟨0⟩) ⟨0⟩ 3
  match g.apply ⟨0⟩ (.cast (handCardNamed g ⟨0⟩ "Bilbo's Deadly Slice").id) with
  | .error msg => mentions msg "requires a target"
  | .ok _ => false

-- Own creatures and non-flying creatures are legal; hexproof on an opponent's
-- creature is not (CR 702.11b).
#guard
  let g := addPermanent afterDraw grizzlyBears ⟨0⟩ ⟨0⟩
  let g := withBlackMana (addToHand g bilbosDeadlySlice ⟨0⟩) ⟨0⟩ 3
  g.canCast ⟨0⟩ (handCardNamed g ⟨0⟩ "Bilbo's Deadly Slice") &&
    (g.legalTargets ⟨0⟩ (Effect.destroyCreature)).contains
      (Target.permanent (namedPermanent g "Grizzly Bears").id)
#guard
  let g := addPermanent afterDraw velvetwingButterflies ⟨1⟩ ⟨1⟩
  let g := withBlackMana (addToHand g bilbosDeadlySlice ⟨0⟩) ⟨0⟩ 3
  (g.legalTargets ⟨0⟩ (Effect.destroyCreature)).contains
    (Target.permanent (namedPermanent g "Velvetwing Butterflies").id)
#guard
  let g := addPermanent afterDraw hexproofFlyer ⟨1⟩ ⟨1⟩
  let g := withBlackMana (addToHand g bilbosDeadlySlice ⟨0⟩) ⟨0⟩ 3
  !g.canCast ⟨0⟩ (handCardNamed g ⟨0⟩ "Bilbo's Deadly Slice")

def proposedBilbosDeadlySlice : Game :=
  mustApply bilbosDeadlySliceSetup ⟨0⟩
    (.cast (handCardNamed bilbosDeadlySliceSetup ⟨0⟩ "Bilbo's Deadly Slice").id)

#guard proposedBilbosDeadlySlice.pending == .chooseTargets ⟨0⟩
#guard proposedBilbosDeadlySlice.log.any (fun s =>
  mentions s "begins casting Bilbo's Deadly Slice")
#guard proposedBilbosDeadlySlice.log.any (fun s =>
  mentions s "must choose a target (CR 601.2c)")

-- Cannot target a player or a land.
#guard
  match proposedBilbosDeadlySlice.apply ⟨0⟩ (.target (Target.player ⟨1⟩)) with
  | .error msg => mentions msg "Illegal target"
  | .ok _ => false
#guard
  let g := addPermanent bilbosDeadlySliceSetup forest ⟨1⟩ ⟨1⟩
  let g := mustApply g ⟨0⟩
    (.cast (handCardNamed g ⟨0⟩ "Bilbo's Deadly Slice").id)
  match g.apply ⟨0⟩ (.target (Target.permanent (namedPermanent g "Forest").id)) with
  | .error msg => mentions msg "Illegal target"
  | .ok _ => false

def targetedBilbosDeadlySlice : Game :=
  mustApply proposedBilbosDeadlySlice ⟨0⟩
    (.target (Target.permanent (namedPermanent proposedBilbosDeadlySlice
      "Grizzly Bears").id))

#guard targetedBilbosDeadlySlice.pending == .activateManaAbilities ⟨0⟩
#guard targetedBilbosDeadlySlice.stack.back!.targets ==
  #[Target.permanent (namedPermanent targetedBilbosDeadlySlice "Grizzly Bears").id]

#guard
  match Agent.choose proposedBilbosDeadlySlice ⟨0⟩ with
  | some (.target (Target.permanent tid)) =>
    (proposedBilbosDeadlySlice.object! tid).name == "Grizzly Bears"
  | _ => false

-- Prefer an opposing creature over your own (CR 601.2c heuristic).
#guard
  let g := addPermanent bilbosDeadlySliceSetup grayOgre ⟨0⟩ ⟨0⟩
  let g := mustApply g ⟨0⟩ (.cast (handCardNamed g ⟨0⟩ "Bilbo's Deadly Slice").id)
  match Agent.choose g ⟨0⟩ with
  | some (.target (Target.permanent tid)) =>
    (g.object! tid).name == "Grizzly Bears"
  | _ => false

def paidBilbosDeadlySlice : Game := mustApply targetedBilbosDeadlySlice ⟨0⟩ .pay

#guard paidBilbosDeadlySlice.hasPriority ⟨0⟩
#guard paidBilbosDeadlySlice.stack.size == 1
#guard paidBilbosDeadlySlice.log.any (fun s => mentions s "casts Bilbo's Deadly Slice")

def resolvedBilbosDeadlySlice : Game := passBoth paidBilbosDeadlySlice

#guard resolvedBilbosDeadlySlice.stack.isEmpty
#guard !(resolvedBilbosDeadlySlice.battlefield.any (fun o => o.name == "Grizzly Bears"))
#guard resolvedBilbosDeadlySlice.objects.any (fun o =>
  o.name == "Grizzly Bears" && o.zone == .graveyard ⟨1⟩)
#guard resolvedBilbosDeadlySlice.log.any (fun s =>
  mentions s "Grizzly Bears is destroyed")
#guard (resolvedBilbosDeadlySlice.player ⟨0⟩).graveyard.any (fun id =>
  (resolvedBilbosDeadlySlice.object! id).name == "Bilbo's Deadly Slice")

-- If the target leaves before resolution, the spell does nothing (CR 608.2b).
def bilbosDeadlySliceTargetGone : Game :=
  let id := (namedPermanent paidBilbosDeadlySlice "Grizzly Bears").id
  let (g, _) := paidBilbosDeadlySlice.move id (.graveyard ⟨1⟩) none
  passBoth g

#guard bilbosDeadlySliceTargetGone.log.any (fun s => mentions s "no longer in play")
#guard !(bilbosDeadlySliceTargetGone.battlefield.any (fun o =>
  o.name == "Grizzly Bears"))

-- Destroy does nothing to an indestructible creature (CR 701.7b / 702.12b).
#guard
  let g := addPermanent afterDraw indestructibleBeast ⟨1⟩ ⟨1⟩
  let g := g.applyEffect ⟨0⟩ (Effect.destroyCreature)
    #[Target.permanent (namedPermanent g "Indestructible Beast").id]
  g.battlefield.any (fun o => o.name == "Indestructible Beast") &&
    g.log.any (fun s => mentions s "is indestructible and isn't destroyed")

/-- The agent casts Bilbo's Deadly Slice when that is the playable spell. -/
def agentBilbosDeadlySliceOnly : Game :=
  let g := addPermanent afterDraw grizzlyBears ⟨1⟩ ⟨1⟩
  let g := clearHandPlayedLand g ⟨0⟩
  withBlackMana (addToHand g bilbosDeadlySlice ⟨0⟩) ⟨0⟩ 3

#guard
  match Agent.choose agentBilbosDeadlySliceOnly ⟨0⟩ with
  | some (.cast id) =>
    (agentBilbosDeadlySliceOnly.object! id).name == "Bilbo's Deadly Slice"
  | _ => false

/-- Magnificent End costs {3} less when it targets a tapped creature. -/
def magnificentEndSetup (tapped : Bool) : Game :=
  let g := addPermanent afterDraw grizzlyBears ⟨1⟩ ⟨1⟩
  let g :=
    if tapped then
      let o := namedPermanent g "Grizzly Bears"
      g.setObject { o with status := { o.status with tapped := true } }
    else g
  let g := readyMain (emptyHand g ⟨0⟩)
  withWhiteMana (addToHand g magnificentEnd ⟨0⟩) ⟨0⟩ 5

def magnificentEndFull : Game := magnificentEndSetup false
def magnificentEndCheap : Game := magnificentEndSetup true

#guard magnificentEnd.costReductionIfTargetTapped == 3
#guard
  match magnificentEndFull.apply ⟨0⟩
      (.cast (handCardNamed magnificentEndFull ⟨0⟩ "Magnificent End").id) with
  | .ok g' =>
    match g'.proposedSpell with
    | some prop => prop.cost.manaValue == 5
    | none => false
  | .error _ => false

def magnificentEndCheapLocked : Game :=
  let g := mustApply magnificentEndCheap ⟨0⟩
    (.cast (handCardNamed magnificentEndCheap ⟨0⟩ "Magnificent End").id)
  mustApply g ⟨0⟩
    (.target (Target.permanent (namedPermanent g "Grizzly Bears").id))

#guard
  match magnificentEndCheapLocked.proposedSpell with
  | some prop => prop.cost.manaValue == 2
  | none => false

/-- Fiend Hunter exiles another creature until it leaves (CR 610.3). -/
def fiendHunterLinked : Game :=
  let g := addPermanent afterDraw fiendHunter ⟨0⟩ ⟨0⟩
  let g := addPermanent g grizzlyBears ⟨1⟩ ⟨1⟩
  let hunter := namedPermanent g "Fiend Hunter"
  let bears := namedPermanent g "Grizzly Bears"
  g.exileUntilSourceLeaves (some hunter.id) bears

#guard !(fiendHunterLinked.battlefield.any (fun o => o.name == "Grizzly Bears"))
#guard fiendHunterLinked.objects.any (fun o => o.name == "Grizzly Bears" && o.zone == .exile)
#guard (namedPermanent fiendHunterLinked "Fiend Hunter").linkedExile.size == 1

def fiendHunterReturned : Game :=
  let hunter := namedPermanent fiendHunterLinked "Fiend Hunter"
  (fiendHunterLinked.move hunter.id (.graveyard ⟨0⟩) none).1

#guard fiendHunterReturned.battlefield.any (fun o => o.name == "Grizzly Bears")
#guard fiendHunterReturned.log.any (fun s => mentions s "returns to the battlefield")

/-- Mentor of the Meek: another small creature entering offers {1} to draw. -/
def mentorSmallEnters : Game :=
  let g := addPermanent afterDraw mentorOfTheMeek ⟨0⟩ ⟨0⟩
  let g := addPermanent g llanowarElves ⟨0⟩ ⟨0⟩
  let mentor := namedPermanent g "Mentor of the Meek"
  let elves := namedPermanent g "Llanowar Elves"
  let g := g.putMatchingSourceTriggers ⟨0⟩ mentor .anotherCreatureYouControlEnters
    (cause := some elves)
  g.receivePriority ⟨0⟩

#guard mentorSmallEnters.stack.size == 1
#guard (mentorSmallEnters.object! mentorSmallEnters.stack.back!.objectId).triggeredAbility ==
  some (.onAnotherCreatureYouControlPowerAtMostEntersMayPayDraw 2 1)

def mentorMayPay : Game := passBoth mentorSmallEnters

#guard
  match mentorMayPay.pending with
  | .mayPayGeneric ⟨0⟩ 1 => true
  | _ => false

#guard
  let g := addPermanent afterDraw mentorOfTheMeek ⟨0⟩ ⟨0⟩
  let g := addPermanent g hillGiant ⟨0⟩ ⟨0⟩
  let mentor := namedPermanent g "Mentor of the Meek"
  let giant := namedPermanent g "Hill Giant"
  let g := g.putMatchingSourceTriggers ⟨0⟩ mentor .anotherCreatureYouControlEnters
    (cause := some giant)
  let g := g.receivePriority ⟨0⟩
  g.stack.isEmpty

/-- Dawn of a New Age enters with a hope counter per creature you control. -/
def dawnWithCreature : Game :=
  let g := addPermanent afterDraw grizzlyBears ⟨0⟩ ⟨0⟩
  let g := addPermanent g dawnOfANewAge ⟨0⟩ ⟨0⟩
  g.afterPermanentEnters (namedPermanent g "Dawn of a New Age")

#guard (namedPermanent dawnWithCreature "Dawn of a New Age").status.hope == 1
#guard dawnWithCreature.log.any (fun s => mentions s "hope counter")

def dawnEndStep : Game :=
  let dawn := namedPermanent dawnWithCreature "Dawn of a New Age"
  let g := dawnWithCreature.putMatchingSourceTriggers ⟨0⟩ dawn .yourEndStep
  passBoth (g.receivePriority ⟨0⟩)

#guard !(dawnEndStep.battlefield.any (fun o => o.name == "Dawn of a New Age"))
#guard (dawnEndStep.player ⟨0⟩).life == 24
#guard dawnEndStep.log.any (fun s => mentions s "is sacrificed")

/-- Islandwalk: the defending player cannot block if they control an Island. -/
def islandwalkBlocked : Bool :=
  let g := addPermanent afterDraw colossalWhale ⟨0⟩ ⟨0⟩
  let g := addPermanent g island ⟨1⟩ ⟨1⟩
  let g := addPermanent g grizzlyBears ⟨1⟩ ⟨1⟩
  let whale := namedPermanent g "Colossal Whale"
  let g := g.setObject { whale with status := { whale.status with attacking := true } }
  !g.canBlock (namedPermanent g "Grizzly Bears") (g.object! whale.id)

def islandwalkOpen : Bool :=
  let g := addPermanent afterDraw colossalWhale ⟨0⟩ ⟨0⟩
  let g := addPermanent g grizzlyBears ⟨1⟩ ⟨1⟩
  let whale := namedPermanent g "Colossal Whale"
  let g := g.setObject { whale with status := { whale.status with attacking := true } }
  g.canBlock (namedPermanent g "Grizzly Bears") (g.object! whale.id)

#guard islandwalkBlocked
#guard islandwalkOpen

/-- Fog on the Barrow-Downs: enchanted creature cannot attack. -/
def fogCantAttack : Bool :=
  let g := addPermanent afterDraw grizzlyBears ⟨0⟩ ⟨0⟩
  let g := addPermanent g fogOnTheBarrowDowns ⟨1⟩ ⟨1⟩
  let bears := namedPermanent g "Grizzly Bears"
  let fog := namedPermanent g "Fog on the Barrow-Downs"
  let g := g.setObject { fog with attachedTo := some bears.id }
  !g.canAttack (namedPermanent g "Grizzly Bears")

#guard fogCantAttack

-- Fog overwrites creature types (CR 205.3m): only a Spirit, not a Bear.
#guard
  let g := addPermanent afterDraw grizzlyBears ⟨0⟩ ⟨0⟩
  let g := addPermanent g fogOnTheBarrowDowns ⟨1⟩ ⟨1⟩
  let bears := namedPermanent g "Grizzly Bears"
  let fog := namedPermanent g "Fog on the Barrow-Downs"
  let g := g.setObject { fog with attachedTo := some bears.id }
  let host := namedPermanent g "Grizzly Bears"
  g.hasSubtype host "Spirit" && !g.hasSubtype host "Bear"

-- Gaze in Wonder (Velvetwing adventure) taps one or two creatures.
def gazeSetup : Game :=
  let g := addPermanent afterDraw grizzlyBears ⟨1⟩ ⟨1⟩
  let g := addPermanent g grayOgre ⟨1⟩ ⟨1⟩
  let g := readyMain (emptyHand g ⟨0⟩)
  withWhiteMana (addToHand g velvetwingButterfliesCard ⟨0⟩) ⟨0⟩ 2

#guard Effect.tapOneOrTwoCreatures.maxTargetCount == 2
#guard
  match velvetwingButterfliesCard.adventure with
  | some adv => adv.spellEffect == some (Effect.tapOneOrTwoCreatures)
  | none => false

def gazeProposed : Game :=
  mustApply gazeSetup ⟨0⟩
    (.castAdventure (handCardNamed gazeSetup ⟨0⟩ "Velvetwing Butterflies").id)

#guard gazeProposed.pending == .chooseTargets ⟨0⟩

def gazeOneTarget : Game :=
  mustApply gazeProposed ⟨0⟩
    (.target (Target.permanent (namedPermanent gazeProposed "Grizzly Bears").id))

#guard gazeOneTarget.pending == .activateManaAbilities ⟨0⟩
#guard gazeOneTarget.stack.back!.targets ==
  #[Target.permanent (namedPermanent gazeOneTarget "Grizzly Bears").id]
#guard !gazeOneTarget.canFinishOptionalTargets (gazeOneTarget.object! gazeOneTarget.stack.back!.objectId)
#guard gazeProposed.announcingSameWordMultiTargets

-- A second `target` after choosing one creature is not a later announcement.
#guard
  match gazeOneTarget.apply ⟨0⟩
      (.target (Target.permanent (namedPermanent gazeOneTarget "Gray Ogre").id)) with
  | .error msg => mentions msg "Not time to choose targets"
  | .ok _ => false

-- Both creatures of this instance are announced together.
def gazeTwoTargets : Game :=
  mustApply gazeProposed ⟨0⟩
    (.targets #[
      Target.permanent (namedPermanent gazeProposed "Grizzly Bears").id,
      Target.permanent (namedPermanent gazeProposed "Gray Ogre").id])

#guard gazeTwoTargets.pending == .activateManaAbilities ⟨0⟩
#guard gazeTwoTargets.stack.back!.targets ==
  #[Target.permanent (namedPermanent gazeTwoTargets "Grizzly Bears").id,
    Target.permanent (namedPermanent gazeTwoTargets "Gray Ogre").id]

-- Sequential one-then-another announcement of the same instance is illegal.
#guard
  match gazeProposed.announceTargetChoices ⟨0⟩
      #[(Target.permanent (namedPermanent gazeProposed "Grizzly Bears").id, none)] with
  | .ok g =>
    match g.announceTargetChoices ⟨0⟩
        #[(Target.permanent (namedPermanent g "Gray Ogre").id, none)] with
    | .error msg => mentions msg "Not time to choose targets"
    | .ok _ => false
  | .error _ => false

-- Three creatures exceed “one or two”.
#guard
  let g := addPermanent gazeProposed ragingGoblin ⟨0⟩ ⟨0⟩
  match g.apply ⟨0⟩
      (.targets #[
        Target.permanent (namedPermanent g "Grizzly Bears").id,
        Target.permanent (namedPermanent g "Gray Ogre").id,
        Target.permanent (namedPermanent g "Raging Goblin").id]) with
  | .error msg => mentions msg "Cannot choose more than 2 targets"
  | .ok _ => false

def gazeResolvedTwo : Game :=
  passBoth (mustApply gazeTwoTargets ⟨0⟩ .pay)

#guard (namedPermanent gazeResolvedTwo "Grizzly Bears").status.tapped
#guard (namedPermanent gazeResolvedTwo "Gray Ogre").status.tapped

def gazeResolvedOne : Game :=
  passBoth (mustApply gazeOneTarget ⟨0⟩ .pay)

#guard (namedPermanent gazeResolvedOne "Grizzly Bears").status.tapped
#guard !(namedPermanent gazeResolvedOne "Gray Ogre").status.tapped

-- Finishing one creature does not use `decline`.
#guard
  match gazeOneTarget.apply ⟨0⟩ .decline with
  | .error msg => mentions msg "Not time to decline"
  | .ok _ => false

end Mtg.Engine.Tests
