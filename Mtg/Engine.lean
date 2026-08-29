import Mtg.Engine.Agent
import Mtg.Engine.Card
import Mtg.Engine.Catalog
import Mtg.Engine.Catalog.Hobbit
import Mtg.Engine.Catalog.HobbitEternal
import Mtg.Engine.Color
import Mtg.Engine.Deck
import Mtg.Engine.Game
import Mtg.Engine.Mana
import Mtg.Engine.Oracle
import Mtg.Engine.Rules
import Mtg.Engine.Tests
import Mtg.Engine.Turn
import Mtg.Engine.TypeLine
import Mtg.Engine.Zone

/-!
# Mtg.Engine

A Lean 4 rules engine for *Magic: The Gathering*, following the Comprehensive
Rules effective 7 August 2026.
-/

namespace Mtg.Engine

/-- Library identification, including the Comprehensive Rules version. -/
def identification : String :=
  s!"Mtg.Engine ({Rules.identification})"

end Mtg.Engine
