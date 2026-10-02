import Mtg.Engine.Catalog
import Mtg.Engine.Catalog.Hobbit
import Mtg.Engine.Catalog.HobbitEternal
import Mtg.Engine.Catalog.MarvelSuperHeroes

/-!
# Supported catalog

Every card the engine can resolve by English name. Deck lists look names up
in `supportedCatalogCards`.
-/

namespace Mtg.Engine

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
