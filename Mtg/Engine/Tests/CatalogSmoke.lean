import Mtg.Engine.Catalog.MarvelSuperHeroes
import Mtg.Engine.Catalog.Supported

/-!
# Catalog membership smoke test

Kept out of `Mtg.Engine.Tests.Marvel` so the 609-card name scan does not
block the MSH gameplay fixtures the demo checks import.
-/

namespace Mtg.Engine.Tests

open Mtg.Engine.Catalog

#guard
  let names := supportedCatalogCards.map (·.name)
  mshCards.size == 286 &&
    ["Brave Brawler", "Jennifer Walters", "The Sensational She-Hulk",
      "Stature, Size Shifter"].all names.contains

end Mtg.Engine.Tests
