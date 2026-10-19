# Architecture & Build Guide

This document provides a high-level overview of the `Mtg.Engine` repository, its Lake library/plugin layout, module hierarchy, testing infrastructure, and core architectural invariants.

For detailed subsystem documentation, see:
- [`docs/CARD_MODEL_AND_PARSER.md`](./CARD_MODEL_AND_PARSER.md) — Card IR (`CardDef`, `Effect`, `Resolution`, selectors) and the prototype-driven Oracle parser.
- [`docs/GAME_ENGINE.md`](./GAME_ENGINE.md) — Runtime `Game` state machine, turn/priority loop, casting, continuous effects, resolution pipelines, and `Pending` choices.
- [`docs/REFACTORING_AND_EXTENSION_GUIDE.md`](./REFACTORING_AND_EXTENSION_GUIDE.md) — Concrete refactoring opportunities, ongoing unification patterns, and step-by-step extension playbooks.

---

## 1. System Overview

`Mtg.Engine` is a pure, deterministic [Lean 4](https://lean-lang.org/) rules engine for *Magic: The Gathering* following the Comprehensive Rules effective **25 September 2026**.

The repository is divided into five main layers:

```
┌────────────────────────────────────────────────────────────────────────────┐
│ 5. Console Demo & Replay Runner (Mtg/Demo.lean, Mtg/Demo/*, examples/*.txt)│
├────────────────────────────────────────────────────────────────────────────┤
│ 4. Compile-Time Test Suites (Mtg/Engine/Tests/*, *OracleTests*, Check0..9) │
├───────────────────────────────┬────────────────────────────────────────────┤
│ 3a. Card Catalogs             │ 3b. Heuristic Agent & Test Fixtures        │
│ (Mtg/Engine/Catalog.lean,     │ (Mtg/Engine/Agent.lean,                    │
│  Mtg/Engine/Catalog/*)        │  Mtg/Engine/Fixture.lean)                  │
├───────────────────────────────┴────────────────────────────────────────────┤
│ 2. Game Rules Engine (Mtg/Engine/Game.lean, Mtg/Engine/Game/*)             │
├────────────────────────────────────────────────────────────────────────────┤
│ 1. Card Model & Oracle Parser (Mtg/Engine/Card.lean, Mtg/Engine/Card/*,    │
│    Mtg/Engine/Color.lean, Mana.lean, TypeLine.lean, Turn.lean, Zone.lean)  │
└────────────────────────────────────────────────────────────────────────────┘
```

---

## 2. Lake Build & Precompiled Plugin Architecture (`lakefile.toml`)

Because nearly all tests in this repository are **compile-time `#guard` assertions** evaluated by Lean's elaborator during `lake build`, `lakefile.toml` splits the codebase into specific `[[lean_lib]]` targets to keep elaboration fast:

| Target (`lakefile.toml`) | `precompileModules` | Modules Included | Why Configured This Way |
| --- | --- | --- | --- |
| `Mtg.Engine.Card` | **`true`** | `Mtg.Engine.Card.*`, `Color`, `Mana`, `TypeLine` | Compiles the Card IR and `parseOracleCard` into **one native shared plugin** (`.so`/`.dll`). Downstream modules evaluate `#guard` and `parseOracleCard!` at native speed without loading a separate dynlib per module. |
| `Mtg.Engine.Catalog` | **`false`** (interpreted) | `Mtg.Engine.Catalog`, `Mtg.Engine.Catalog.*` | **Must remain interpreted.** Lake groups all `Mtg.Engine.Catalog.*` submodules under this library. If `precompileModules = true` were enabled here, every downstream `lake` worker process loading the plugin would run C module initializers that parse all **981 catalog cards** on startup. Keeping it interpreted (while marking card defs `@[irreducible, noinline]`) means `parseOracleCard!` runs native code via `Mtg.Engine.Card` only when a catalog module itself is built. |
| `Mtg.Engine.Game` | **`true`** | `Mtg.Engine.Game.*`, `Deck`, `Rng`, `Rules`, `Turn`, `Zone` | Compiles the entire game state machine and effect resolvers into **one native plugin**, so `#guard` game simulations run as compiled native code. |
| `Mtg.Engine.Fixture` | **`true`** | `Mtg.Engine.Fixture` | Precompiles shared test opening states (`started`, `afterDraw`, `drawnHands`, etc.) into a native plugin so `#guard` tests read pre-initialized `Game` values from memory instead of replaying game start and mulligans in every test file. |
| `Mtg.Engine` | `false` | `Mtg.Engine`, `Mtg.Engine.Tests.*`, `*OracleTests*`, `FraCardTests*` | Top-level library and compile-time test modules; elaborated in parallel across CPU cores. |
| `MtgDemo` | `false` | `Mtg.Demo.*` (`WelcomeDecks`, `DeckList`, `Render`, `RenderTests`, `Check0`..`Check9`) | Demo library and its 10 parallel `#guard` test shards (`Check0`..`Check9`). |
| `mtg-demo` (`lean_exe`) | Executable | `Mtg.Demo` | Console application (`--auto`, `--interactive`, `--multiplayer`, `--check`). |
| `oracle-roundtrip` (`lean_exe`) | Executable | `Mtg.OracleRoundtrip` | Quick CLI smoke test for `parseOracleCard`. |

---

## 3. Core Design Invariants

### 3.1 Catalog Cards Are Defined Exclusively by Printed Oracle Text
- Every card in `Mtg/Engine/Catalog.lean` and `Mtg/Engine/Catalog/*` (`Hobbit.lean`, `HobbitEternal.lean`, `MarvelSuperHeroes.lean`, `RealityFracture.lean`, `RealityFractureCommander.lean`) is constructed by passing its printed Gatherer/Scryfall text lines to `fromOracle` (`parseOracleCard!`) or `fromOracleKeeping` (`parseOracleCardKeeping`).
- **No unmodeled text allowed**: At the end of `parseOracleCard` (`Mtg/Engine/Card/ParseOracle.lean`), `CardDef.modellingError?` (`Mtg/Engine/Card/CardDef.lean`) verifies that:
  1. No `.printed line` fallback entries remain in `staticAbilities` on any face.
  2. No unparsed `extraLines` remain on `adventure` or `prepareFace`.
  3. Neither `doesNothingAsSpell` nor `doesNothingAsActivated` holds on any parsed spell or activated ability.
- All catalog card definitions are annotated with `@[irreducible, noinline]` so Lean's kernel/elaborator never unfolds their bodies into parser calls during downstream typechecking.

### 3.2 Pure Functional State Machine & Deterministic Execution
- `Game` (`Mtg/Engine/Game/Core.lean`) is a pure value struct. Every player action (`g.apply p action`), step transition (`g.advanceStep`), or trigger resolution returns a new `Game` (or `Except String Game`).
- Randomness is threaded explicitly through `g.rng : Rng` (`Mtg/Engine/Rng.lean`) when `g.norandom == false`.
- When `g.norandom == true` (`--norandom` in `mtg-demo`), the engine never touches `g.rng`; instead it pauses by setting `g.pending := .resolveRandom req` and recording the continuation in `g.afterRandom : Option AfterRandom` (`Mtg/Engine/Game/Pending.lean`) so external callers or replay scripts can supply exact shuffle orders, random picks, or coin flips (`shuffle`, `order`, `pick`, `random`, `flip`).

### 3.3 Lean 4's 243 Field-Bearing Constructor Tag Limit
- Lean 4's runtime and C code generator restrict any `inductive` type to at most **243 constructors that carry fields** (`tag <= 243`). Nullary constructors (no arguments) may follow field-bearing constructors without limit.
- Keep this constraint in mind when editing large sum types:
  - `Resolution` (`Mtg/Engine/Card/SpellResolution.lean`) has 39 constructors (33 field-bearing + 6 nullary) parameterized by compositional selectors (`ObjectSelector`, `PlayerSelector`, `NumberSelector`, `CostSelector`, `ConditionSelector`).
  - `ObjectSelector` (`Mtg/Engine/Card/SpellResolution.lean`) has 15 constructors (13 field-bearing + 2 nullary) aligned with CR 109 / CR 400 zone and object categories (`TargetObject`, `BattlefieldObject`, `GraveyardExileObject`, `LibraryHandObject`, `SacrificeStackObject`, plus target/player/set combinators).
  - `NumberSelector` (`Mtg/Engine/Card/SpellResolution.lean`) has 8 constructors (7 field-bearing + 1 nullary) aligned with CR 202.3 / CR 208 / CR 400 / CR 608 categories (`StatNumber`, `CountNumber`, `TurnEventNumber`, plus `.greatestPower`, `.fixed`, `.count`, `.power`, `.loyalty`).
  - `ConditionSelector` (`Mtg/Engine/Card/SpellResolution.lean`) has 6 field-bearing constructors aligned with CR 110 / CR 601 / CR 608 categories (`StateCondition`, `TurnHistoryCondition`, `StepNoteCondition`, plus `.atLeast`, `.not`, `.or`).
  - `TriggerGrantWhat` (`Mtg/Engine/Card/SpellResolution.lean`) has 7 field-bearing constructors aligned with CR 613 layers, CR 614/615 rule effects, and CR 701 keyword actions (`Layer6AbilityGrant`, `.copy`, `.control`, `Layer4TypeGrant`, `Layer7PtGrant`, `RuleEffectGrant`, `ActionStateGrant`).
  - `StaticAbility` (`Mtg/Engine/Card/StaticAbility.lean`) has 9 field-bearing constructors aligned with CR 604 / CR 613 / CR 614 categories (`TypeStatic`, `AbilityStatic`, `CdaStatic`, `PtStatic`, `CombatStatic`, `CostCastStatic`, `RuleStatic`, `KeywordStatic`, and `.printed`).
  - `TriggerEvent` (`Mtg/Engine/Card/TriggerEvent.lean`) has 14 constructors (12 field-bearing + 2 nullary) aligned with CR 603 categories (`EntersEvent`, `LeavesEvent`, `StepEvent`, `CastEvent`, `CombatEvent`, `DamageEvent`, `DrawEvent`, `DiscardEvent`, `TapEvent`, `CounterEvent`, `ActionEvent`, `.or`, `.cascade`, `.fromEffect`).
  - `EffectTargetKind` (`Mtg/Engine/Card/Targeting.lean`) has 9 constructors (8 field-bearing + 1 nullary) aligned with CR 115 categories (`BattlefieldTarget`, `GraveyardTarget`, `StackTarget`, `PlayerTarget`, `MultiTarget`, `.filtered`, `.multi`, `.pair`, `.none`).
  - `SharedTrigger` (`Mtg/Engine/Card/SharedTrigger.lean`) has 10 field-bearing constructors aligned with CR 603 / CR 608 / CR 701 effect categories (`LibraryTrigger`, `TokenCounterTrigger`, `CombatDamageTrigger`, `ZoneChangeTrigger`, `ContinuousTrigger`, `PermanentTrigger`, `EventLeftover`, `.chapter`, `.mayTo`, `.may`), and `ChapterResolution` (`Mtg/Engine/Card/Chapter.lean`, CR 714.3) has 1 field-bearing constructor (`| spell (s : ChapterSpell)`) wrapping `Resolution`.
  - `CostPick`, `ExtraActivationCost`, `ActivationCondition`, `ActivationCostReduction`, and `EquipRestriction` (`Mtg/Engine/Card/ActivatedAbility.lean`) unify chosen-object activation costs (CR 602.2b), non-mana activation costs (CR 602.1), activation restrictions (CR 602.5b), activation cost reductions (CR 602.2b / 601.2f), and equip target restrictions (CR 702.6) across all sets.
  - `EntersTappedRule` (CR 614.1c), `EntersWithCounters` (CR 614.1c), `AsEntersChoice` (CR 614.12), `SpellCostReduction` (CR 601.2f), and `SpellAdditionalCost` (CR 601.2b / 118.8) (`Mtg/Engine/Card/CardDef.lean`) unify ETB replacement/choice rules and printed spell cost modifiers on `CardDef` across all sets.
  - `InterveningCondition`, `SharedTriggerOpts`, and `TriggerTiming` (`Mtg/Engine/Card/SharedTrigger.lean`, `Mtg/Engine/Card/Trigger.lean`) unify intervening-"if" conditions (CR 603.4) and watched subtype parameters across all sets.
  - `ManaUse`, `ManaRestriction` (`| none | only (u : ManaUse)`), and `ManaPool` (`restricted : Array (ManaType × ManaUse)`) in `Mtg/Engine/Mana.lean` unify mana spending restrictions (CR 106.6 / CR 106.10) across all sets.
  - `Pending` (`Mtg/Engine/Game/Pending.lean`) has 6 constructors (5 field-bearing + 1 nullary) aligned with CR turn/combat, casting, resolution, and random choices (`TurnCombatPending`, `CastPending`, `ResolvePending`, `FraChoice`, `RandomRequest`), and `FraChoice` has 4 field-bearing constructors (`HandGraveyardChoice`, `LibraryChoice`, `BattlefieldChoice`, `CostModeChoice`). No inductive in `Mtg/Engine/` exceeds 33 field-bearing constructors.

---

## 4. Catalog & Test Suite Inventory

### 4.1 Supported Card Catalogs (`Mtg/Engine/Catalog/`)

`supportedCatalogCards` (`Mtg/Engine/Catalog/Supported.lean`) aggregates **981** card definitions:
- **`Mtg/Engine/Catalog.lean`**: 5 Basic Lands, 7 shared Token defs, and 13 core sample cards (`grizzlyBears`, `lightningBolt`, `llanowarElves`, etc.), plus typed card/ability builder helpers for tests.
- **`Mtg/Engine/Catalog/Hobbit.lean` (`HOB`)**: 193 cards (including Adventures separated by `//ADV//`).
- **`Mtg/Engine/Catalog/HobbitEternal.lean` (`HOC`)**: 117 cards.
- **`Mtg/Engine/Catalog/MarvelSuperHeroes.lean` (`MSH`)**: 286 cards (including transforming DFCs separated by `//`).
- **`Mtg/Engine/Catalog/RealityFracture.lean` (`FRA`)**: 285 cards (including Prepare spells separated by `//PREP//`).
- **`Mtg/Engine/Catalog/RealityFractureCommander.lean` (`FRC`)**: 87 cards.

### 4.2 Test Suites

All tests run automatically during `lake build --wfail` (plus CLI checks in CI):

1. **Card & Parser Guards (`Mtg/Engine/Card/Guards.lean`, `Mtg/Engine/Tests/ParseOracle.lean`, `Mtg/Engine/Tests/CardText.lean`, `Mtg/Engine/Tests/CatalogSmoke.lean`)**:
   - Verify Oracle normalization, `OracleArgs` slot collection/refilling, `Resolution` phrase roundtripping, and zero unmodeled cards across `supportedCatalogCards`.
2. **Engine Topic Tests (`Mtg/Engine/Tests.lean` & `Mtg/Engine/Tests/*.lean` — 68 files)**:
   - Granular `#guard` tests per mechanic and per `TriggerResolution` constructor (`Draw.lean`, `Destroy.lean`, `Exile.lean`, `MayCast.lean`, `PutCounters.lean`, `Sacrifice.lean`, `Combat.lean`, `Mulligans.lean`, `Marvel.lean`, `RealityFracture.lean`, `RealityFractureCommander.lean`, etc.).
   - Shared board setups live in `Mtg/Engine/Fixture.lean` (precompiled) and `Mtg/Engine/Tests/RulingFixtures.lean` (lightweight helper functions).
3. **Official Wizards Judge Rulings (`Mtg/Engine/OracleData.lean`, `Mtg/Engine/OracleRulings.lean`)**:
   - `uniqueOracleRulings` in `OracleData.lean` stores **1,057** official rulings across HOB/HOC (`1..359`), MSH (`360..728`), FRA (`729..893`), and FRC (`894..1057`).
   - Verified by executable `#guard` gameplay scenarios in:
     - `Mtg/Engine/OracleRulingTests.lean` (HOB/HOC rulings)
     - `Mtg/Engine/MshOracleTests.lean` .. `MshOracleTests7.lean` (MSH rulings)
     - `Mtg/Engine/FraOracleTests.lean` .. `FraOracleTests8.lean` (FRA rulings)
     - `Mtg/Engine/FraCardTests.lean` .. `FraCardTests3.lean` (every FRA spell, trigger, activated, loyalty, and static ability)
     - `Mtg/Engine/FrcOracleTests.lean` (FRC rulings & catalog validation)
     - `Mtg/Engine/CatalogModelTests.lean` (end-to-end HOB/HOC/MSH catalog card gameplay)
4. **Demo & Replay Verification (`Mtg/Demo/Check0.lean`..`Check9.lean`, `Mtg/Demo/RenderTests.lean`, `examples/*.txt`)**:
   - `Check0`..`Check9` verify CLI flags, interactive commands, pass-until shortcuts, `autopay`, `--norandom`, and `--check`.
   - `RenderTests.lean` verifies board rendering and hidden-information redaction (`--visible`).
   - CI (`.github/workflows/lean_action_ci.yml`) runs `.lake/build/bin/oracle-roundtrip` and replays all 9 full games in `examples/*.txt` via `.lake/build/bin/mtg-demo --check --input <file>`.
