import Mtg.Engine.Catalog.MarvelSuperHeroes
import Mtg.Engine.Catalog.Supported

/-!
# Catalog membership smoke test

Kept out of `Mtg.Engine.Tests.Marvel` so the 609-card name scan does not
block the MSH gameplay fixtures the demo checks import.

Every supported card, including its back face, must parse with no leftover
rules line. Parsing itself rejects a card that is not fully parsed or whose
spell, mode, adventure, prepare face, Saga chapter, or activated ability
would not resolve.
-/

namespace Mtg.Engine.Tests

open Mtg.Engine
open Mtg.Engine.Catalog

def unmodeledSpellReport : String :=
  supportedCatalogCards.foldl (fun acc c =>
    match c.modellingError? with
    | some e => acc ++ e ++ "\n"
    | none => acc) ""

#guard
  if unmodeledSpellReport.isEmpty then true
  else panic! unmodeledSpellReport

#guard
  let names := supportedCatalogCards.map (·.name)
  mshCards.size == 286 &&
    realityFractureCards.size == 285 &&
    ["Brave Brawler", "Jennifer Walters", "The Sensational She-Hulk",
      "Stature, Size Shifter", "Academic Ascent", "Blossom-Blessed Angel",
      "Jace's Machinations"].all names.contains

end Mtg.Engine.Tests
