import Mtg.Engine.Catalog.StarTrek
import Mtg.Engine.OracleData

/-!
# Star Trek (TRK) Oracle rulings catalog & table invariants

Every official Gatherer judge ruling for *Magic: The Gathering | Star Trek*
(TRK) is recorded in `uniqueOracleRulings`, every card named by a TRK ruling
exists in `starTrekCards`, and every TRK card is fully parsed with no
modelling errors.

Runtime gameplay checks for TRK rulings live in `Mtg.Engine.TrkOracleTests2`
and `Mtg.Engine.Tests.StarTrek`.
-/

namespace Mtg.Engine.TrkRulingTests

open Mtg.Engine
open Mtg.Engine.Catalog

/-- Look up a unique judge ruling by 1-based id in `uniqueOracleRulings`. -/
def trkRuling (id : Nat) : OracleRuling :=
  uniqueOracleRulings[id - 1]!

/-- The TRK card a Gatherer ruling name refers to. -/
def trkCardNamed? (name : String) : Option CardDef :=
  starTrekCards.find? (·.name == name)

#guard uniqueOracleRulingCount == 1329
#guard uniqueTrkOracleRulingCount == 302
#guard uniqueTrkOracleRulings.all (fun r => (trkRuling r.id).id == r.id)
#guard uniqueTrkOracleRulings.all (fun r => r.sets.any (· == "trk"))

/- Every TRK ruling names at least one card in this set. -/
#guard uniqueTrkOracleRulings.all (fun r =>
  r.cards.any (fun n => (trkCardNamed? n).isSome))

/- A comment that applies only to TRK names only TRK cards. -/
#guard uniqueTrkOracleRulings.all (fun r =>
  if r.sets.all (· == "trk") then r.cards.all (fun n => (trkCardNamed? n).isSome)
  else true)

/- Official Gatherer has rulings on 207 unique TRK cards (738 unique
(ruling, TRK card) associations across 302 distinct ruling comments). -/
#guard
  ((uniqueTrkOracleRulings.foldl (fun acc r => acc ++ r.cards.toList) []).filter
    (fun n => (trkCardNamed? n).isSome)).eraseDups.length == 207

#guard
  (uniqueTrkOracleRulings.foldl
    (fun acc r => acc + (r.cards.filter (fun n => (trkCardNamed? n).isSome)).size) 0) == 738

/- Every TRK card is fully parsed with no modelling errors (all abilities are structured). -/
#guard starTrekCards.all (fun c => c.modellingError?.isNone)
#guard starTrekCards.size == 311

end Mtg.Engine.TrkRulingTests
