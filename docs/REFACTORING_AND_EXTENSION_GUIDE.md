# Refactoring & Extension Guide

This document details the ongoing refactoring trajectory of `Mtg.Engine`, concrete high-impact opportunities to simplify and unify the codebase, and step-by-step playbooks for extending cards and game mechanics.

---

## 1. Recent Refactoring Trajectory

Recent commits have systematically moved the engine toward **one compositional IR** shared by spells, activated abilities, triggered abilities, and Saga chapters:
1. **Homogenized Selectors**:
   - Introduced and expanded `ObjectSelector` (including `.union`, `.intersection`, `.target (what : ObjectSelector)`), `PlayerSelector` (including `.target (who : PlayerSelector)`, `.controller (of : ObjectSelector)`), `NumberSelector`, `CostSelector` (`.mana`, `.sacrifice`, `.discard`, `.or`), `ConditionSelector` (`.and`, `.or`, `.not`, `.atLeast`, `.countAtLeast`), and `ActionSelector` in `Mtg/Engine/Card/SpellResolution.lean`.
2. **Unified `Resolution` Inductive & Constructor Consolidation**:
   - Merged `SpellResolution`, `TriggerResolution`, and `FraResolution` into a single `Resolution` inductive (`Mtg/Engine/Card/SpellResolution.lean:1800–3272`), with `SpellResolution` and `TriggerResolution` kept as `abbrev`s.
   - Consolidated **85 redundant spell, ability, trigger, and FRA constructors** across two batches into compositional `Resolution` + selector representations (`.pump`, `.dealDamage`, `.gainLife`, `.draw`, `.discard`, `.sacrifice`, `.destroy`, `.exile`, `.returnToHand`, `.put`, `.putCounters`, `.createTokens`, `.addMana`, `.tap`, `.fight`, `.becomePrepared`, `.searchBasicLand`, `.queueReflexive`), deleted `Resolution.ofSpellStep` and 5 redundant helper enums (`MutualFight`, `YouControlCounters`, `CreaturePumpScope`, `EachCreatureDamage`, `EachCreatureAmount`), and grouped all nullary constructors after `| frc (e : FrcEffect)`, reducing the maximum field-bearing constructor tag from **242** to **120** (freeing **123 field-bearing constructor slots**).

The sections below document the remaining duplication left over from earlier per-set iterations (`HOB`, `MSH`, `FRA`, `FRC`) and how to complete this unification cleanly.

---

## 2. Prioritized Refactoring Opportunities

### Priority 1: Collapse Remaining `PermanentAction` and Target-Indexed FRA Constructors in `Resolution`
- **Files**:
  - `Mtg/Engine/Card/SpellResolution.lean` (lines 1800–3272, 3760–3870)
  - `Mtg/Engine/Card/PermanentAction.lean` (lines 1–111)
  - `Mtg/Engine/Card/Effect.lean` (lines 325–390)
- **What remains duplicated**:
  1. **`.onPermanent (action : PermanentAction)` and `.onSource (action : PermanentAction)`**:
     - `TriggerResolution.ofPermanent` and `TriggerResolution.ofSource` (`SpellResolution.lean:3810–3827`) already translate all 21 `PermanentAction` constructors into compositional Stratum 1 constructors (`.pump`, `.destroy`, `.tap`, `.untap`, `.setBasePT`, `.exile`, `.grant`, `.putCounters`, `.putOnLibrary`, etc.).
  2. **Remaining Legacy Spell / FRA Target Constructors**:
     - `.countersOnCreatureTargets`, `.returnTargetToHand`, `.bounce`, `.exileTarget`, `.destroyTarget`, `.destroyAllCreatures`, `.damageSourceAt`, `.plusOneAt`, `.destroyAt`.
- **How to refactor**:
  1. Replace `.onPermanent action` and `.onSource action` with `TriggerResolution.ofPermanent action` and `TriggerResolution.ofSource action`, then delete `PermanentAction.lean`.
  2. Eliminate `TriggerResolution.ofSpell`, `Resolution.toSpellStep`, and `Effect.spellResolution`.
  3. Express remaining FRA target-indexed constructors (`.bounce`, `.exileTarget`, `.destroyTarget`, `.destroyAllCreatures`) using Stratum 1 constructors.

---

### Priority 2: Unify the Resolution Interpreters (`EffectResolution.lean` vs. `TriggeredAbilities.lean`) & Remove Legacy Dispatchers
- **Files**:
  - `Mtg/Engine/Game/EffectResolution.lean` (`applyUnified` L847, `applyUnifiedAbility` L1597, `applyFraResolution?` L59)
  - `Mtg/Engine/Game/TriggeredAbilities.lean` (`applyTriggeredAbility` L3777–4638)
  - `Mtg/Engine/Game/FraResolve.lean`, `Mtg/Engine/Game/FraAbilities.lean`, `Mtg/Engine/Game/FrcResolve.lean`
  - `Mtg/Engine/Game/ModeledTriggers.lean` (L675–860)
  - `Mtg/Engine/Game/Chapters.lean` (L130–215)
- **What is duplicated / dead**:
  1. **Dead & Test-Only Functions**:
     - `Game.applyLeftoverTextEffect` (`ModeledTriggers.lean:799–860`) has **zero callers** anywhere in the repository and can be deleted immediately.
     - `Game.applyModeledTrigger` (`ModeledTriggers.lean:675–797`) is **never called by the game engine** — it is only called directly by legacy unit tests in `CatalogModelTests.lean` (lines 1548–1613) and `MshOracleTests*.lean`. Migrating those ~35 test calls to `applyTriggeredAbility` (or normal stack resolution) allows deleting `applyModeledTrigger` (~125 lines).
     - `Game.applyChapterEffect` (`Chapters.lean:130–215`) is **never called by the game engine** (Saga chapters resolve via `applyTriggeredAbility` in `SpellResolution.lean:128`). It is only called twice in `MshOracleTests2.lean` (lines 1119, 1126). Migrating those 2 test lines allows deleting `applyChapterEffect` (~85 lines).
  2. **Duplicate Fallback Match in `TriggeredAbilities.lean`**:
     - `applyTriggeredAbility` (`TriggeredAbilities.lean:4594–4638`) has a fallback `match ab.effect.resolution` with 13 arms (`.sequence`, `.shuffleSource`, `.draw`, `.scry`, `.onPermanent`, `.onSource`, `.gainLife`, `.recruit`, `.amass`, `.createTokens`, `.addMana`, `.discard`) that duplicate `applyTriggeredAbility`'s main match and `applyUnified`/`applyUnifiedAbility`.
  3. **Duplicate Printed vs. Selector Arms in `TriggeredAbilities.lean`**:
     - `TriggeredAbilities.lean` is **4,885 lines** because each `apply*` helper (`applyTriggerPump`, `applyTriggerDamage`, `applyPutCounters`, `applyCreateTokens`, `applyExile`, `applySacrifice`, `applyDestroy`, `applyTriggerDraw`, `applyReturnToHand`, `applyPut`, `applyGrant`, `applyFight`, `applyMill`, `applyUntap`, `applyTap`, `applyLoseLife`, `applyGainLife`, `applyLose`, `applyCant`, `applySetBasePT`) has dozens of specialized pattern-match arms before falling back to the generic `TriggerArgs.lean` evaluators (`permanentsNamed`, `collectPlayers`, `triggerInt`, `triggerCount`). Collapsing arms whose behavior matches the generic `TriggerArgs` path will shrink `TriggeredAbilities.lean` by 1,500–2,000 lines.
  4. **Converging on One `Resolution` Interpreter**:
     - As Priority 1 replaces legacy spell/ability constructors with Stratum 1 compositional constructors, `applyUnified` and `applyUnifiedAbility` can delegate Stratum 1 constructors directly to the shared compositional handlers in `TriggeredAbilities.lean` (with `TriggerRead` populated from the spell/ability context).

---

### Priority 3: Eliminate `Effect.sharedTrigger : Option SharedTrigger`, `ChapterResolution`, and the 9 `*Leftover` Families
- **Files**:
  - `Mtg/Engine/Card/Effect.lean` (line 45)
  - `Mtg/Engine/Card/SharedTrigger.lean` (lines 15–560)
  - `Mtg/Engine/Card/Chapter.lean` & `Mtg/Engine/Card/ChapterEffects.lean`
  - `Mtg/Engine/Card/Trigger.lean` (`chapterTiming` L51–116, `SharedTrigger.timing` L216–1200)
  - `Mtg/Engine/Card/TriggerEffects.lean`
  - `Mtg/Engine/Card/TriggeredAbility.lean` (lines 19–51, 1876–2182)
  - `Mtg/Engine/Card/OracleArgs.lean` (lines 400–473, 513–518)
- **What is duplicated**:
  - Every HOB/HOC/MSH triggered ability and Saga chapter stores its payload **twice** on `Effect`: once as `resolution : Resolution` (computed via `SharedTrigger.timing` or `TriggeredAbility.chapterTiming`) and once as `sharedTrigger : Option SharedTrigger`.
  - Meanwhile, FRA triggers (`TriggeredAbility.fra` in `TriggeredAbility.lean:2204`) already work with `sharedTrigger := none`, storing their effect directly in `Effect.resolution` and their text in `SharedTriggerOpts.printed` / `Effect.phrase`.
- **How to refactor**:
  - Construct trigger and chapter `Effect`s directly with compositional `Resolution` trees and `Effect.phrase`.
  - Update `OracleArgs.takeEffect` and `TriggeredAbility.toNotation` to read `e.resolution` / `e.phrase` directly instead of branching on `e.sharedTrigger`.
  - Delete `SharedTrigger`, the 9 `*Leftover` enums (`EnterLeftover`, `StepLeftover`, `DeathLeftover`, `ThisAttackLeftover`, `EnterOrAttackLeftover`, `WatchLeftover`, `YouAttackLeftover`, `CastLeftover`, `ResourceLeftover`), `ChapterResolution`, and `TriggerEffects.lean` (~2,500 lines removed).

---

### Priority 4: Pause-Aware `.sequence` Execution for Spells and Activated Abilities
- **Files**:
  - `Mtg/Engine/Game/EffectResolution.lean` (lines 854–870, 1604–1620)
  - `Mtg/Engine/Game/TriggeredAbilities.lean` (lines 3852–3907, 4641)
  - `Mtg/Engine/Game/Core.lean` (lines 17–28, 217–310)
  - `Mtg/Engine/Game/Pending.lean` (`FraNext` lines 85–120)
- **Problem**:
  - `applyTriggeredAbility` has a pause-aware `.sequence` runner: if step $i$ sets `g.pending != .none`, remaining steps $i+1 \dots n$ are saved in `g.triggerSequenceRest` and automatically resumed via `g.resumeTriggerSequence` once the player finishes the choice.
  - `applyUnified` and `applyUnifiedAbility` instead run `steps.foldl` synchronously without checking `g.pending != .none`. To work around this, spells and abilities use ad-hoc continuation fields on `Game`: `pendingDrawAfterScry`, `fraAfterLook : Option (PlayerId × Option ObjectId × FraNext)`, `palantirAfterScry`, `plusOneAfterSearch`, `plusOneAfterDiscards`, and hardcoded `.sequence` pattern matches in `EffectResolution.lean` (lines 856, 863, 1606, 1614).
- **How to refactor**:
  - Use the same pause-aware sequence continuation (`triggerSequenceRest`, generalized to `resolutionSequenceRest`) in `applyUnified` and `applyUnifiedAbility`.
  - Delete `FraNext`, `fraAfterLook`, `pendingDrawAfterScry`, `plusOneAfterSearch`, `plusOneAfterDiscards`, and the special-cased `.sequence` matches in `EffectResolution.lean`.

---

### Priority 5: Consolidate `Pending` (43 Constructors) and `FraChoice` (74 Constructors)
- **Files**:
  - `Mtg/Engine/Game/Pending.lean` (lines 246–639)
  - `Mtg/Engine/Game/Decisions.lean`, `Mtg/Engine/Game/FraChoices.lean`, `Mtg/Engine/Game/Actions.lean`, `Mtg/Engine/Game/Leaving.lean`, `Mtg/Engine/Game.lean`
- **Problem**:
  - Top-level `Pending` has 43 constructors and `FraChoice` has 74 constructors, with heavy overlap across sacrifice prompts (13 variants), discard prompts (13 variants), optional mana payment prompts (7 variants), and may-cast prompts (9 variants).
  - Every top-level `Pending` constructor requires boilerplate arms in `Actions.actor` (`Actions.lean:119–180`), `Leaving.redirectPendingAfterLeave` (`Leaving.lean:89–194`), `Actions.applyAction`, `Decisions.lean`, `Demo/Render.lean`, and `Game.applyIdle`.
- **How to refactor**:
  1. Factor the deciding `PlayerId` to the top level (or move legacy card-specific `Pending` variants into `FraChoice` / a unified `ChoiceKind` payload paired with `player : PlayerId`), shrinking `Actions.actor` and `redirectPendingAfterLeave` to a few lines.
  2. Replace card-specific sacrifice/discard/pay/cast choice constructors with parameterized choice primitives (`selectObjects`, `mayPayCost`, `mayConfirm`, `mayCast`) composed with the pause-aware `.sequence` runner (Priority 4).

---

### Priority 6: Unify `EffectTargetKind` Around `TargetFilter`
- **Files**:
  - `Mtg/Engine/Card/Targeting.lean` (lines 48–642)
  - `Mtg/Engine/Game/Targeting.lean` (lines 108–425)
  - `Mtg/Engine/Card/OracleArgs.lean` (lines 215–233, 775–840)
- **Problem**:
  - `EffectTargetKind` has 70 hardcoded constructors (`.creature`, `.creatureWithFlying`, `.oppCreaturePowerAtMost`, etc.) alongside `.filtered (f : TargetFilter)`, `.multi`, and `.pair`. Each hardcoded constructor is duplicated in `EffectTargetKind.spec` (305 lines in `Card/Targeting.lean:321–626`) and `legalTargetsForAtomicKind` (200 lines in `Game/Targeting.lean:183–386`).
- **How to refactor**:
  - Turn the 70 hardcoded constructors into `abbrev` smart constructors that build `.filtered { ... }` (or `.multi` / `.pair`), leaving only `.none`, `.filtered`, `.multi`, and `.pair` on `EffectTargetKind`.

---

### Priority 7: Encapsulate `CardDef` Flags, `Game` Scratchpad Fields, `ManaPool` Restrictions, and Token Enums
1. **`CardDef` (`Mtg/Engine/Card/CardDef.lean:48–460`)**:
   - Group the ~21 `tapAdd*` fields into structured mana ability definitions, the ~15 `entersTapped*`/`entersWith*` fields into an ETB modifier list, and the ~17 `costReduction*`/`additionalCost*` fields into a spell cost modifier list.
2. **`Game` & `Player` Per-Turn / Per-Resolution State (`Mtg/Engine/Game/Core.lean`, `Player.lean`, `Turns.lean`)**:
   - Extract per-turn `Player` fields into `pl.thisTurn : PlayerTurnState` and per-turn `Game` fields into `g.thisTurn : GameTurnState` so `Turns.clearTurnActivations` (`Turns.lean:55–143`) resets them with `{ pl with thisTurn := {} }` instead of a 90-line manual field reset.
   - Extract the ~25 `*ThisWay` fields on `Game` (`milledIdsThisWay`, `exiledIdsThisWay`, `sacrificedPowerThisWay`, etc., `Core.lean:310–395`) into `g.thisWay : ResolutionNotes` reset at the start of each resolution.
3. **`ManaPool` (`Mtg/Engine/Mana.lean:285–795`)**:
   - Merge the 23 hardcoded LOTR/MSH restricted mana counters (`elfWhite`..`creatureColorless`) into `fraRestricted : Array (ManaType × FraManaUse)` (renamed to `restricted : Array (ManaType × ManaRestriction)`), cutting ~350 lines from `ManaPool.spendOne?`.
4. **Token Enums (`Token.lean`, `SpellResolution.lean:1303`, `FrcEffect.lean:15`)**:
   - Merge `TriggerToken` and `FrcToken` into `TokenKind` (or a unified `TokenSpec` struct).

---

## 3. Step-by-Step Extension Playbooks

### 3.1 Adding a New Card to the Catalog
1. Add the card definition in the appropriate `Mtg/Engine/Catalog/*.lean` file using `@[irreducible, noinline] def myCard : CardDef := fromOracle [ ... ]` with its exact Gatherer/Scryfall printed lines (use `//` between DFC faces, `//ADV//` before an Adventure face, or `//PREP//` before a Prepare face), and append it to the set's card array (`hobbitCards`, `mshCards`, `realityFractureCards`, or `realityFractureCommanderCards`).
2. If all abilities on the card match existing prototypes in `OracleCandidates.lean`, `lake build` will succeed immediately.
3. If `parseOracleCard!` fails at elaboration time, the error message will state either:
   - Which line was unrecognized (stored as `StaticAbility.printed line` and caught by `CardDef.modellingError?`), or
   - That a parsed effect is unmodeled (`doesNothingAsSpell` / `doesNothingAsActivated`).

### 3.2 Adding a New Spell, Trigger, or Activated Ability Pattern
Prefer using existing compositional constructors in `Resolution` (`SpellResolution.lean:1839–2883`) and selectors (`ObjectSelector`, `PlayerSelector`, `NumberSelector`, `CostSelector`, `ConditionSelector`) before adding any new constructor:
1. **If existing `Resolution` + selectors can express the effect**:
   - Add a helper constructor or prototype entry in `Mtg/Engine/Card/OracleCandidates.lean` (`spellEffects`, `triggeredAbilities`, `activatedAbilities`, or `staticAbilities`).
   - Ensure `SpellResolution.toPhrase` (`SpellResolution.lean`) or `TriggeredAbility.toNotation` (`TriggeredAbility.lean`) renders the exact normalized Oracle phrasing.
   - If the prototype has open parameters (`Nat`, `Int`, `String` subtype, `CardType`, `EffectTargetKind`, `CounterKind`), verify that `OracleArgs.lean` (`takeEffect` / `refillEffect`, etc.) visits those slots in the same order in both `.collect` and `.fill` modes.
2. **If a new selector or `Resolution` constructor is genuinely needed**:
   - **Card IR (`Mtg/Engine/Card/`)**:
     - Add the constructor to `ObjectSelector` / `NumberSelector` / `Resolution` in `SpellResolution.lean`. *(Respect Lean's 243 field-bearing constructor limit on `Resolution`: place field-bearing constructors before the nullary block around line 3309!)*
     - Add its English rendering in `SpellResolution.toPhrase` / `TriggeredAbility.toNotation`.
     - If it carries open slots, add traversal arms in `OracleArgs.lean`.
     - Register a prototype in `OracleCandidates.lean` and add a `#guard` roundtrip check in `Mtg/Engine/Card/Guards.lean`.
   - **Game Execution (`Mtg/Engine/Game/`)**:
     - For new selectors: add evaluation arms in `Mtg/Engine/Game/TriggerArgs.lean` (`permanentsNamed`, `collectPlayers`, `triggerInt`, `triggerCount`).
     - For new `Resolution` steps: implement execution in `TriggeredAbilities.lean` / `EffectResolution.lean`.
   - **Tests**:
     - Add a compile-time `#guard` test in the corresponding `Mtg/Engine/Tests/<Topic>.lean` file using fixtures from `Mtg/Engine/Fixture.lean` or `Mtg/Engine/Tests/RulingFixtures.lean`.

### 3.3 Verification Checklist Before Committing
Always run the same checks enforced by `.github/workflows/lean_action_ci.yml`:
```sh
# 1. Build all targets and run all compile-time #guard tests (failing on any warning)
lake build --wfail

# 2. Run the Oracle parser roundtrip executable
lake exe oracle-roundtrip

# 3. Verify all recorded example game replays
lake exe mtg-demo -- --check --input examples/FRA_draft_1.txt
lake exe mtg-demo -- --check --input examples/MSH_draft_1.txt
```
