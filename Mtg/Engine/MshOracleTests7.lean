import Mtg.Engine.Card
import Mtg.Engine.Catalog
import Mtg.Engine.Catalog.Hobbit
import Mtg.Engine.Catalog.HobbitEternal
import Mtg.Engine.Catalog.MarvelSuperHeroes
import Mtg.Engine.Game
import Mtg.Engine.OracleData
import Mtg.Engine.Tests.Abilities
import Mtg.Engine.Tests.Adventures
import Mtg.Engine.Tests.AttackTriggers
import Mtg.Engine.Tests.Auras
import Mtg.Engine.Tests.Effects
import Mtg.Engine.Tests.Elves
import Mtg.Engine.Tests.Equipment
import Mtg.Engine.Tests.Helpers
import Mtg.Engine.Tests.Pathmaker
import Mtg.Engine.Tests.Removal
import Mtg.Engine.Tests.RulingFixtures
import Mtg.Engine.Tests.Turns


/-!
# Engine behavior for unique Marvel Super Heroes (MSH) judge rulings (part 7)

Catalog coverage for cards named by MSH judge rulings.
-/

namespace Mtg.Engine.MshRulingTests

open Mtg.Engine
open Mtg.Engine.Catalog
open Mtg.Engine.Tests

/-- Catalog cards named by MSH rulings exist in `mshCards`. -/
def mshRulingCardsInCatalogOk : Bool :=
  let names := mshCards.map (·.name)
  uniqueMshOracleRulings.all (fun r =>
    r.cards.any (fun n =>
      names.any (· == n) ||
        n == "T'Challa, the Black Panther"))

#guard mshRulingCardsInCatalogOk

end Mtg.Engine.MshRulingTests
