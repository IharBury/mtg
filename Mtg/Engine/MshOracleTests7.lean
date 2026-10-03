import Mtg.Engine.Catalog.MarvelSuperHeroes
import Mtg.Engine.OracleData

/-!
# Engine behavior for unique Marvel Super Heroes (MSH) judge rulings (part 7)

Catalog coverage for cards named by MSH judge rulings. This module imports
only the Marvel catalog and the ruling table, so the name scan does not wait
on the gameplay tests.
-/

namespace Mtg.Engine.MshRulingTests

open Mtg.Engine
open Mtg.Engine.Catalog

/-- Catalog cards named by MSH rulings exist in `mshCards`. -/
def mshRulingCardsInCatalogOk : Bool :=
  let names := mshCards.map (·.name)
  uniqueMshOracleRulings.all (fun r =>
    r.cards.any (fun n =>
      names.any (· == n) ||
        n == "T'Challa, the Black Panther"))

#guard mshRulingCardsInCatalogOk

end Mtg.Engine.MshRulingTests
