import Mtg.Engine.Catalog
import Mtg.Engine.Catalog.MarvelSuperHeroes
import Mtg.Engine.Game
import Mtg.Engine.Tests

/-!
# Cosmic Cube fixture

A small game used by the MSH ruling checks and by console render tests.
It lives here so those two modules can compile in parallel: the render
tests only need this fixture, not the rest of the ruling suite.
-/

namespace Mtg.Engine.MshRulingTests

open Mtg.Engine
open Mtg.Engine.Catalog
open Mtg.Engine.Tests

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

end Mtg.Engine.MshRulingTests
