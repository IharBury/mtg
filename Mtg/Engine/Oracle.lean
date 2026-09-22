import Mtg.Engine.Card
import Mtg.Engine.Catalog
import Mtg.Engine.Catalog.Hobbit
import Mtg.Engine.Catalog.HobbitEternal
import Mtg.Engine.Catalog.MarvelSuperHeroes

/-!
# Engine catalog

The cards the engine currently models, including stored Oracle text from
each printed set.
-/

namespace Mtg.Engine

namespace CardDef

/-- Unique strings, first occurrence kept. -/
def uniqueStrings (xs : List String) : List String :=
  xs.foldl (fun acc x => if acc.any (· == x) then acc else acc ++ [x]) []

end CardDef

open Catalog

/-- Every card in the engine catalog. -/
def supportedCatalogCards : Array CardDef :=
  #[grizzlyBears, grayOgre, hillGiant, canyonMinotaur, ragingGoblin,
    llanowarElves, crawWurm, centaurCourser, rumblingBaloth, giantSpider,
    lightningBolt, shock, giantGrowth]
    ++ Catalog.hobbitCards
    ++ Catalog.hobbitEternalCards
    ++ Catalog.mshCards

end Mtg.Engine
