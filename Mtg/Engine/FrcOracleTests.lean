import Mtg.Engine.Catalog.RealityFractureCommander
import Mtg.Engine.OracleData

/-!
# Reality Fracture Commander rulings

Every FRC judge comment is in `uniqueOracleRulings`, and every FRC card is
fully parsed. Gameplay checks for the set's effects live in
`Mtg.Engine.Tests.RealityFractureCommander`.
-/

namespace Mtg.Engine.FrcRulingTests

open Mtg.Engine
open Mtg.Engine.Catalog

/-- The FRC card a Scryfall ruling name refers to. -/
def frcCardNamed? (name : String) : Option CardDef :=
  realityFractureCommanderCards.find? (·.name == name)

#guard uniqueFrcOracleRulingCount == 180

/- Every FRC ruling names at least one card in this set. -/
#guard uniqueFrcOracleRulings.all (fun r =>
  r.cards.any (fun n => (frcCardNamed? n).isSome))

/- A comment that applies only to FRC names only FRC cards. -/
#guard uniqueFrcOracleRulings.all (fun r =>
  if r.sets.all (· == "frc") then r.cards.all (fun n => (frcCardNamed? n).isSome)
  else true)

/- Every FRC card is fully parsed with no modelling errors (all abilities are structured). -/
#guard realityFractureCommanderCards.all (fun c => c.modellingError?.isNone)

#guard realityFractureCommanderCards.size == 87

end Mtg.Engine.FrcRulingTests
