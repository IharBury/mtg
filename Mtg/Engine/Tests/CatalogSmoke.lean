import Mtg.Engine.Catalog.MarvelSuperHeroes
import Mtg.Engine.Catalog.Supported

/-!
# Catalog membership smoke test

Kept out of `Mtg.Engine.Tests.Marvel` so the 609-card name scan does not
block the MSH gameplay fixtures the demo checks import.

Every supported card, including its back face, must parse with no leftover
rules line. Every spell, mode, adventure, prepare face, and Saga chapter
must resolve through a real effect, and every activated ability must too.
-/

namespace Mtg.Engine.Tests

open Mtg.Engine
open Mtg.Engine.Catalog

/-- True when resolving this effect as a spell or chapter would do nothing.
Saga chapters carried as `.trigger (.chapter …)` are resolved by
`applyChapterEffect`, not by the spell-resolution table. -/
partial def resolutionDoesNothing (r : Resolution) : Bool :=
  match r with
  | .sequence rs => rs.any resolutionDoesNothing
  | .shuffleSource | .gainLife _ | .recruit | .addMana _ | .discard _ | .onSource _ => false
  | .fra _ | .empowerJace _ | .surveil _ | .millSelf _ | .mayDiscardDraw _
  | .createTokensLifeGained _ | .oppSacrificesGreatestMvGainLife _
  | .eachCreatureYouControlBecomesPrepared | .damageThenEmpowerExcess _
  | .exileTopMayCastElseDamageOpponents _ | .emblemCastSpellDamage _
  | .firstDealsStatDamageToSecond _ | .returnFromGyWithFinality
  | .copyNextInstantSorceryThisTurn | .proliferatePlaneswalkerTypesTimes
  | .copyEachCreatureOfTargetPlayer | .becomeCopyLegendRuleOff
  | .teamGain _ | .jaceLoyaltyAtInstantSpeed => false
  | .trigger (.chapter _ _) => false
  | .spell .unrecognized => true
  | r => ({ resolution := r } : Effect).spellResolution == .unrecognized

def spellEffectDoesNothing (e : Effect) : Bool :=
  resolutionDoesNothing e.resolution

def optEffect (o : Option Effect) : Array Effect :=
  match o with
  | some e => #[e]
  | none => #[]

def faceSpellEffects (c : CardDef) : Array Effect :=
  let modes := if c.spellModes.isEmpty then optEffect c.spellEffect else c.spellModes
  let adv := match c.adventure with
    | some a => optEffect a.spellEffect
    | none => #[]
  let prep := match c.prepareFace with
    | some a => optEffect a.spellEffect
    | none => #[]
  let chapters := match c.saga with
    | some s => s.chapters.filterMap (·.chapterEffect)
    | none => #[]
  modes ++ adv ++ prep ++ chapters

def keepsUnparsedLine (c : CardDef) : Bool :=
  c.staticAbilities.any (fun
    | .printed _ => true
    | _ => false) ||
    (c.adventure.any (fun a => !a.extraLines.isEmpty)) ||
    (c.prepareFace.any (fun a => !a.extraLines.isEmpty))

def activatedDoesNothing (e : Effect) : Bool :=
  match e.resolution with
  | .spell .unrecognized => true
  | .trigger .exileOppNonlandEachUntilLeaves => false
  | .trigger _ => true
  | .sequence rs => rs.any (fun r => match r with
      | .spell .unrecognized => true
      | .trigger .exileOppNonlandEachUntilLeaves => false
      | .trigger _ => true
      | _ => false)
  | _ => false

def unmodeledSpellReport : String :=
  supportedCatalogCards.foldl (fun acc c =>
    let report (acc : String) (name : String) (effects : Array Effect) : String :=
      effects.foldl (fun acc e =>
        if spellEffectDoesNothing e then
          acc ++ s!"{name}: {Effect.toNotation e}\n"
        else acc) acc
    let activated (acc : String) (name : String) (c : CardDef) : String :=
      c.activatedAbilities.foldl (fun acc ab =>
        if activatedDoesNothing ab.effect then
          acc ++ s!"{name} activated: {Effect.toNotation ab.effect}\n"
        else acc) acc
    let acc :=
      if keepsUnparsedLine c then acc ++ s!"{c.name}: unparsed rules line\n" else acc
    let acc := report acc c.name (faceSpellEffects c)
    let acc := activated acc c.name c
    match c.otherFace with
    | some back =>
      let acc :=
        if keepsUnparsedLine back then acc ++ s!"{back.name}: unparsed rules line\n" else acc
      let acc := report acc back.name (faceSpellEffects back)
      activated acc back.name back
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
