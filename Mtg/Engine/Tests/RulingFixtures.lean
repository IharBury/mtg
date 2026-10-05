import Mtg.Engine.Catalog
import Mtg.Engine.Catalog.Hobbit
import Mtg.Engine.Catalog.HobbitEternal
import Mtg.Engine.Catalog.MarvelSuperHeroes
import Mtg.Engine.Game
import Mtg.Engine.Tests.Abilities
import Mtg.Engine.Tests.Auras
import Mtg.Engine.Tests.Helpers
import Mtg.Engine.Tests.Turns

/-!
# Small game states shared with Oracle ruling checks.

Kept out of the Combat-dependent test modules so those checks do not wait
on the combat suite.
-/

namespace Mtg.Engine.Tests

open Mtg.Engine
open Mtg.Engine.Catalog

def oliphauntCycleAbility : ActivatedAbility :=
  oliphaunt.activatedAbilities[0]!

/-- Isolated library so the search finds a known card. -/
def withOnlyLibrary (g : Game) (p : PlayerId) (cards : Array CardDef) : Game :=
  let g := g.modifyPlayer p (fun pl => { pl with library := #[] })
  cards.foldl (fun g c => addToLibraryTop g c p) g

def oliphauntCycleReady : Game :=
  let g := readyMain (emptyHand afterDraw ⟨0⟩)
  let g := withOnlyLibrary g ⟨0⟩ #[mountain]
  withRedMana (addToHand g oliphaunt ⟨0⟩) ⟨0⟩ 1

def oliphauntCycled : Game :=
  let g := oliphauntCycleReady
  let src := handCardNamed g ⟨0⟩ "Oliphaunt"
  let g := mustApply g ⟨0⟩ (.activate src.id 0)
  applyIdle (passBoth (mustApply g ⟨0⟩ .pay))

/-- Typecycling is instant-speed (CR 702.29 / 117.1). -/
def oliphauntCycleAtEnd : Game :=
  let g := applyIdle (passBoth (skipTo afterDraw .end 80))
  let g := emptyHand g ⟨0⟩
  let g := withOnlyLibrary g ⟨0⟩ #[mountain]
  withRedMana (addToHand g oliphaunt ⟨0⟩) ⟨0⟩ 1

/-- An opponent's land does not trigger your landfall. -/
def nissaLandVsAttercop : Game :=
  let g := addPermanent afterDraw attercop ⟨0⟩ ⟨0⟩
  let g := passBoth (skipTo g .end 80)
  let g := skipTo g .precombatMain 80
  let g := addToHand g forest ⟨1⟩
  mustApply g ⟨1⟩ (.playLand (handCardNamed g ⟨1⟩ "Forest").id)

/-- Wood Elves putting a Forest onto the battlefield also triggers landfall. -/
def attercopWoodElvesResolved : Game :=
  let g := addPermanent afterDraw attercop ⟨0⟩ ⟨0⟩
  let g := withGreenMana (addToHand g woodElves ⟨0⟩) ⟨0⟩
  let g := mustApply g ⟨0⟩ (.cast (handCardNamed g ⟨0⟩ "Wood Elves").id)
  let g := mustApply g ⟨0⟩ .pay
  let g := passBoth g
  let g := addToLibraryTop (addToLibraryTop g forest ⟨0⟩) mountain ⟨0⟩
  applyIdle (passBoth g)

/-- Cosmic Cube: attacking Bears, then Bolt / Mountain / Hill Giant on top. -/
def cosmicCubeSetup : Game :=
  let g := addPermanent afterDraw cosmicCube ⟨0⟩ ⟨0⟩
  let g := addPermanent g grizzlyBears ⟨0⟩ ⟨0⟩
  let bears := namedPermanent g "Grizzly Bears"
  let g := g.setObject { bears with status := { bears.status with attacking := true } }
  let g := addToLibraryTop g hillGiant ⟨0⟩
  let g := addToLibraryTop g mountain ⟨0⟩
  addToLibraryTop g lightningBolt ⟨0⟩

/-- Ruling 708: Cosmic Cube looks at the top six and waits for the controller. -/
def cosmicCubePending : Game :=
  let cube := namedPermanent cosmicCubeSetup "Cosmic Cube"
  cosmicCubeSetup.applyModeledTrigger ⟨0⟩ (.onYouAttacking Effect.youAttackingLookSixCast) (some cube.id)

end Mtg.Engine.Tests
