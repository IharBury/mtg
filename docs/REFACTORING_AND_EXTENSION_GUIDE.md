# Refactoring & Extension Guide

This document details the ongoing refactoring trajectory of `Mtg.Engine`, concrete high-impact opportunities to simplify and unify the codebase, and step-by-step playbooks for extending cards and game mechanics.

---

## 1. Recent Refactoring Trajectory

Recent commits have systematically moved the engine toward **one compositional IR** shared by spells, activated abilities, triggered abilities, and Saga chapters:
1. **Homogenized Selectors**:
   - Introduced and expanded `ObjectSelector` (including `.union`, `.intersection`, `.target (what : ObjectSelector)`), `PlayerSelector` (including `.target (who : PlayerSelector)`, `.controller (of : ObjectSelector)`), `NumberSelector`, `CostSelector` (`.mana`, `.sacrifice`, `.discard`, `.or`), `ConditionSelector` (`.and`, `.or`, `.not`, `.atLeast`, `.countAtLeast`), and `ActionSelector` in `Mtg/Engine/Card/SpellResolution.lean`.
2. **Unified `Resolution` Inductive, Token Unification & Constructor Consolidation**:
   - Merged `SpellResolution`, `TriggerResolution`, `FraResolution`, and `FrcEffect` into a single `Resolution` inductive (`Mtg/Engine/Card/SpellResolution.lean:2228–3149`), with `SpellResolution` and `TriggerResolution` kept as `abbrev`s.
   - Unified all 23 constructors of `TriggeredAbility.TriggerToken` into `TokenKind` (`Mtg/Engine/Card/Token.lean`, CR 111), removed the duplicate `token` parameter from `Resolution.createTokens`, and consolidated token printed definitions in `Game.tokenPrinted` (`Mtg/Engine/Game/Tokens.lean`).
   - Consolidated **325 redundant spell, ability, trigger, FRA, and FRC constructors** across eleven batches into 33 compositional field-bearing `Resolution` primitives + CR-aligned `@[match_pattern] abbrev` aliases (`.pump`, `.dealDamage`, `.scry`/`.surveil`, `.draw`, `.searchLibrary`, `.discard`, `.pay`, `.putCounters`/`.removeCounters`/`.proliferate`, `.returnToHand`, `.put`, `.putOnLibrary`, `.createTokens`, `.amass`, `.exile`, `.sacrifice`, `.attach`, `.mayCast`, `.addMana`, `.chooseModes`/`.or`/`.ifElse`, `.destroy`, `.tap`/`.untap`, `.grant`/`.lose`/`.cant`/`.becomeArtifact`/`.becomePrepared`/`.setBasePT`/`.gainControl`/`.becomeCopy`/`.replace`/`.spellsCostLess`/`.investigate`/`.empowerJace`/`.recruit`/`.noteResolveThisTurn`/`.mshReflexive`, `.gainLife`/`.loseLife`, `.mill`, `.revealLibrary`/`.revealFromHand`, `.connive`, `.queueReflexive`, `.sequence`, `.may`, `.«if»`, `.fight`, `.onPermanent`/`.onSource`, `.unlessPays`), deleted `Mtg/Engine/Card/FrcEffect.lean` (`FrcEffect` and `FrcToken`), `Resolution.ofSpellStep`, `TriggerToken`, and 8 redundant helper enums (`LibrarySearch`, `MutualFight`, `YouControlCounters`, `CreaturePumpScope`, `EachCreatureDamage`, `EachCreatureAmount`, `ReturnTwoCreaturesOrLands`, `ReturnOneOrTwoNonlands`), and grouped all nullary constructors at the end of `Resolution`, reducing `Resolution` from **364** to **39 total constructors** with **33 field-bearing constructors** and **6 nullary constructors** (maximum field-bearing constructor tag reduced from **242** to **32**, freeing **211 of 244 field-bearing constructor slots**).
3. **Unified `TriggerEvent` Inductive (CR 603)**:
   - Merged the three separate trigger-event inductives — `TriggerEvent` (111 constructors), `FraEvent` (34 constructors), and `SharedTriggerWhen` (90 constructors), totaling **235 constructors across 3 inductives** — into a single CR 603-aligned `TriggerEvent` inductive (`Mtg/Engine/Card/TriggerEvent.lean`) with **14 total constructors** (**12 field-bearing** over 11 CR 603 event-filter sub-inductives `EntersEvent`..`ActionEvent` + `.or` + **2 nullary** `.cascade`, `.fromEffect`), with `FraEvent` and `SharedTriggerWhen` kept as `abbrev`s for `TriggerEvent` and `@[match_pattern] abbrev` aliases for all existing event names.
4. **Unified `StaticAbility` Inductive (CR 604 / CR 613 / CR 614)**:
   - Merged the three separate static-ability inductives — `StaticAbility` (109 constructors), `FraStatic` (43 constructors), and `StaticShape` (103 constructors), totaling **255 constructors across 3 inductives** — into a single CR 604 / CR 613 / CR 614-aligned `StaticAbility` inductive (`Mtg/Engine/Card/StaticAbility.lean`) with **9 field-bearing constructors** (`typeChange`, `ability`, `cda`, `pt`, `combat`, `costCast`, `rule`, `keyword`, `printed`), with `FraStatic` and `StaticShape` kept as `abbrev`s for `StaticAbility` and `@[match_pattern] abbrev` aliases for all existing constructor names.
5. **Unified `EffectTargetKind` Inductive (CR 115)**:
   - Grouped the 75 hardcoded targeting constructors of `EffectTargetKind` (`Mtg/Engine/Card/Targeting.lean`) into 5 CR 115 target-category sub-inductives (`BattlefieldTarget`, `GraveyardTarget`, `StackTarget`, `PlayerTarget`, `MultiTarget`) with `@[match_pattern] abbrev` aliases, reducing `EffectTargetKind` from **79** to **9 constructors** (**8 field-bearing** + **1 nullary** `.none`) and factoring both `EffectTargetKind.spec` (`Card/Targeting.lean`) and `Game.legalTargetsForAtomicKind` (`Game/Targeting.lean`) by CR 115 target category.
6. **Unified `ObjectSelector` (CR 109 / CR 400) and `SharedTrigger` (CR 603 / CR 608) Inductives**:
   - Grouped the 167 non-recursive leaf constructors of `ObjectSelector` (`Mtg/Engine/Card/SpellResolution.lean`) into 5 CR 109 / CR 400 zone and object-category sub-inductives (`TargetObject`, `BattlefieldObject`, `GraveyardExileObject`, `LibraryHandObject`, `SacrificeStackObject`) with `@[match_pattern] abbrev` aliases, reducing `ObjectSelector` from **177** to **15 constructors** (**13 field-bearing** + **2 nullary**).
   - Grouped the 166 effect and leftover constructors of `SharedTrigger` (`Mtg/Engine/Card/SharedTrigger.lean`) into 7 CR 603 / CR 608 / CR 701 effect-category sub-inductives (`LibraryTrigger`, `TokenCounterTrigger`, `CombatDamageTrigger`, `ZoneChangeTrigger`, `ContinuousTrigger`, `PermanentTrigger`, `EventLeftover`) with `@[match_pattern] abbrev` aliases and category-factored `SharedTrigger.timing` (`Mtg/Engine/Card/Trigger.lean`), reducing `SharedTrigger` from **169** to **10 constructors** (all **10 field-bearing**).
7. **Unified `ChapterResolution` (CR 714.3), `ActivationCost` / `CostPick` (CR 602.2b), and `ActivationCondition` (CR 602.5b)**:
   - Reduced `ChapterResolution` (`Mtg/Engine/Card/Chapter.lean`) from **24 constructors (9 field-bearing + 15 nullary)** to **1 constructor** (`| spell (s : ChapterSpell)`) wrapping `Resolution`, with all 23 named HOB/MSH chapter constructors retained as builder functions in `namespace ChapterResolution`, and simplified `Effect.ofChapter` (`ChapterEffects.lean`), `TriggeredAbility.chapterTiming` (`Trigger.lean`), and `takeChapter` (`OracleArgs.lean`) to a single `.spell s` arm.
   - Unified the 9 chosen-object boolean/option fields on `ActivationCost` (`discardACard`, `discardLegendarySameName`, `sacrificeLegendaryArtifact`, `sacrificeArtifact`, `sacrificeArtifactOrCreature`, `sacrificeArtifactOrDiscardNonland`, `sacrificeEquipmentAttachedToSource`, `tapAnUntappedCreatureYouControl`, `sacrificeAnotherSubtype`) into `picks : Array CostPick := #[]` (`Mtg/Engine/Card/ActivatedAbility.lean`, CR 602.2b).
   - Unified `FraActivationCondition` and the 5 `onlyIf*` fields on `ActivatedAbility` (`onlyIfYouControlLegendary`, `onlyIfYouAttackedWithTwoOrMore`, `onlyIfOpponentDealtNoncombatDamage`, `onlyIfYouControlCreatureToughnessAtLeast`, `onlyIfGyCreaturesAtLeast`) into a single CR 602.5b `ActivationCondition` inductive (`condition : ActivationCondition := .none` on `ActivatedAbility`) and aligned `ExtraActivationCost` (CR 602.1), `InterveningCondition` (CR 603.4), and `ManaUse` (CR 106.6) with CR terminology.
8. **Unified `ManaUse` / `ManaRestriction` / `ManaPool` (CR 106.4 / CR 106.6 / CR 106.10) and `InterveningCondition` / `SharedTriggerOpts` / `TriggerTiming` (CR 603.4)**:
   - Extended `ManaUse` (`Mtg/Engine/Mana.lean`, CR 106.6) with the 6 HOB/MSH spending restrictions (`.elf`, `.instantOrSorcery`, `.hero`, `.villain`, `.cantNonartifact`, `.creatureSource`), unified `ManaRestriction` (CR 106.10) into 2 constructors (`| none` and `| only (u : ManaUse)`), and replaced the 27 hardcoded restricted-mana `Nat` fields (`elfWhite`..`creatureGreen`, `cantNonartifact`, `cantNonartifactBlue`) and `fraRestricted` on `ManaPool` (CR 106.4) with a single `restricted : Array (ManaType × ManaUse) := #[]` field (reducing `ManaPool` from **34** to **7 fields**).
   - Extended `InterveningCondition` (`Mtg/Engine/Card/SharedTrigger.lean`, CR 603.4) with `.youControlCreatureWithPower`, `.gainedLifeAtLeast`, and `.anotherCreaturePowerAtMost`, and replaced the 8 mutually-exclusive condition and subtype fields on `SharedTriggerOpts` and 6 copied fields on `TriggerTiming` (`Mtg/Engine/Card/Trigger.lean`) with `condition : InterveningCondition := .none` and `subtype : Option String := none` (reducing `SharedTriggerOpts` from **13** to **7 fields** and `TriggerTiming` from **14** to **10 fields**).

The sections below document the remaining duplication left over from earlier per-set iterations (`HOB`, `MSH`, `FRA`, `FRC`) and how to complete this unification cleanly.

---

## 2. Prioritized Refactoring Opportunities

### Priority 1: Collapse `PermanentAction` (`Resolution.onPermanent`) into Compositional `Resolution` Steps
- **Files**:
  - `Mtg/Engine/Card/SpellResolution.lean` (lines 2228–3149, 3425–3518)
  - `Mtg/Engine/Card/PermanentAction.lean` (lines 1–111)
  - `Mtg/Engine/Card/Effect.lean` (lines 325–405)
- **What remains duplicated**:
  - **`.onPermanent (action : PermanentAction) (who : ObjectSelector := .target)`** (and `@[match_pattern] abbrev onSource (action : PermanentAction) : Resolution := .onPermanent action .source`):
    - `TriggerResolution.ofPermanent` and `TriggerResolution.ofSource` (`SpellResolution.lean:3495–3571`) already translate all 21 `PermanentAction` constructors into compositional Stratum 1 constructors (`.pump`, `.destroy`, `.tap`, `.untap`, `.setBasePT`, `.exile`, `.grant`, `.putCounters`, `.putOnLibrary`, etc.).
- **How to refactor**:
  1. Replace `.onPermanent action who` with `TriggerResolution.ofPermanent action` / `TriggerResolution.ofSource action`, then delete `PermanentAction.lean`.
  2. Eliminate `TriggerResolution.ofSpell`, `Resolution.toSpellStep`, and `Effect.spellResolution`.

---

### Priority 2: Unify the Resolution Interpreters (`EffectResolution.lean` vs. `TriggeredAbilities.lean`) & Remove Legacy Dispatchers
- **Files**:
  - `Mtg/Engine/Game/EffectResolution.lean` (`applyUnified`, `applyUnifiedAbility`, `applyFraResolution?`)
  - `Mtg/Engine/Game/TriggeredAbilities.lean` (`applyTriggeredAbility`)
  - `Mtg/Engine/Game/FraResolve.lean`, `Mtg/Engine/Game/FraAbilities.lean`, `Mtg/Engine/Game/FrcResolve.lean`
- **Completed**:
  - Deleted dead `Game.applyLeftoverTextEffect`, `Game.applyModeledTrigger`, `Game.resolveHarnessedFlicker`, `Game.applyChapterEffect`, and unused `FraChoice.mayPutMilledPermanent`; migrated all test callers to `Game.applyTriggeredAbility`.
  - Removed duplicate fallback arms (`.shuffleSource`, `.draw`, `.scry`, `.gainLife`, `.recruit`, `.amass`, `.createTokens`, `.addMana`, `.discard`, and `Resolution.toSpell`) from `applyTriggeredAbility` (`TriggeredAbilities.lean:4611–4625`), delegating directly to `applyUnifiedAbility`.
- **Remaining**:
  1. **Duplicate Printed vs. Selector Arms in `TriggeredAbilities.lean`**:
     - `TriggeredAbilities.lean` is ~4,870 lines because each `apply*` helper (`applyTriggerPump`, `applyTriggerDamage`, `applyPutCounters`, `applyCreateTokens`, `applyExile`, `applySacrifice`, `applyDestroy`, `applyTriggerDraw`, `applyReturnToHand`, `applyPut`, `applyGrant`, `applyFight`, `applyMill`, `applyUntap`, `applyTap`, `applyLoseLife`, `applyGainLife`, `applyLose`, `applyCant`, `applySetBasePT`) has dozens of specialized pattern-match arms before falling back to the generic `TriggerArgs.lean` evaluators (`permanentsNamed`, `collectPlayers`, `triggerInt`, `triggerCount`). Collapsing arms whose behavior matches the generic `TriggerArgs` path will shrink `TriggeredAbilities.lean` by 1,500–2,000 lines.
  2. **Converging on One `Resolution` Interpreter**:
     - As Priority 1 replaces legacy spell/ability constructors with Stratum 1 compositional constructors, `applyUnified` and `applyUnifiedAbility` can delegate Stratum 1 constructors directly to the shared compositional handlers in `TriggeredAbilities.lean` (with `TriggerRead` populated from the spell/ability context).

---

### Priority 3: Eliminate `Effect.sharedTrigger : Option SharedTrigger` and the 9 `*Leftover` Families
- **Files**:
  - `Mtg/Engine/Card/Effect.lean` (line 45)
  - `Mtg/Engine/Card/SharedTrigger.lean` (lines 15–560)
  - `Mtg/Engine/Card/Trigger.lean` (`SharedTrigger.timing` L216–1200)
  - `Mtg/Engine/Card/TriggerEffects.lean`
  - `Mtg/Engine/Card/TriggeredAbility.lean` (lines 19–51, 1876–2182)
  - `Mtg/Engine/Card/OracleArgs.lean` (lines 400–473, 513–518)
- **Completed**:
  - Unified `ChapterResolution` (`Mtg/Engine/Card/Chapter.lean`, CR 714.3) into a single constructor (`| spell (s : ChapterSpell)`) wrapping `Resolution`, eliminating the 23 duplicate Saga chapter constructors and the 24-arm match trees in `ChapterEffects.lean` and `Trigger.lean`.
- **What remains duplicated**:
  - Every HOB/HOC/MSH triggered ability stores its payload **twice** on `Effect`: once as `resolution : Resolution` (computed via `SharedTrigger.timing`) and once as `sharedTrigger : Option SharedTrigger`.
  - Meanwhile, FRA triggers (`TriggeredAbility.fra` in `TriggeredAbility.lean:2204`) already work with `sharedTrigger := none`, storing their effect directly in `Effect.resolution` and their text in `SharedTriggerOpts.printed` / `Effect.phrase`.
- **How to refactor**:
  - Construct trigger `Effect`s directly with compositional `Resolution` trees and `Effect.phrase`.
  - Update `OracleArgs.takeEffect` and `TriggeredAbility.toNotation` to read `e.resolution` / `e.phrase` directly instead of branching on `e.sharedTrigger`.
  - Delete `SharedTrigger`, the 9 `*Leftover` enums (`EnterLeftover`, `StepLeftover`, `DeathLeftover`, `ThisAttackLeftover`, `EnterOrAttackLeftover`, `WatchLeftover`, `YouAttackLeftover`, `CastLeftover`, `ResourceLeftover`), and `TriggerEffects.lean` (~2,500 lines removed).

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

### Priority 5: Further Parameterize `Pending` (6 Constructors) and `FraChoice` (4 Constructors) Sub-Inductives
- **Files**:
  - `Mtg/Engine/Game/Pending.lean`
  - `Mtg/Engine/Game/Decisions.lean`, `Mtg/Engine/Game/FraChoices.lean`, `Mtg/Engine/Game/Actions.lean`, `Mtg/Engine/Game/Leaving.lean`, `Mtg/Engine/Game.lean`
- **Completed**:
  - Grouped `Pending` from **45 constructors (42 field-bearing)** into **6 constructors (5 field-bearing + 1 nullary)**: `.none`, `.turnCombat (step : TurnCombatPending)`, `.cast (player : PlayerId) (step : CastPending)`, `.resolve (player : PlayerId) (choice : ResolvePending)`, `.fraChoice (player : PlayerId) (choice : FraChoice)`, and `.resolveRandom (req : RandomRequest)`, factoring `player : PlayerId` onto `.cast` and `.resolve` with `@[match_pattern] abbrev` aliases, and simplified `Actions.actor` (`Actions.lean`) and `Leaving.redirectPendingAfterLeave` (`Leaving.lean`) to match `.cast p _`, `.resolve p _`, and `.fraChoice p _` directly.
  - Grouped `FraChoice` from **93 constructors (89 field-bearing)** into **4 field-bearing constructors** aligned with CR zones and choice kinds: `.handGraveyard (c : HandGraveyardChoice)`, `.library (c : LibraryChoice)`, `.battlefield (c : BattlefieldChoice)`, and `.costMode (c : CostModeChoice)` with `@[match_pattern] abbrev` aliases.
- **Remaining**:
  1. Replace card-specific sacrifice/discard/pay/cast choice constructors inside `HandGraveyardChoice`, `LibraryChoice`, `BattlefieldChoice`, `CostModeChoice`, and `ResolvePending` with parameterized choice primitives (`selectObjects`, `mayPayCost`, `mayConfirm`, `mayCast`) composed with the pause-aware `.sequence` runner (Priority 4).

---

### Priority 6: Further Unify `EffectTargetKind` Sub-Inductives into `TargetFilter`
- **Files**:
  - `Mtg/Engine/Card/Targeting.lean`
  - `Mtg/Engine/Game/Targeting.lean`
  - `Mtg/Engine/Card/OracleArgs.lean`
- **Completed**:
  - Grouped the 75 named targeting constructors into 5 CR 115 target-category sub-inductives (`BattlefieldTarget`, `GraveyardTarget`, `StackTarget`, `PlayerTarget`, `MultiTarget`), reducing `EffectTargetKind` to 9 constructors (`.none`, `.battlefield`, `.graveyard`, `.stack`, `.playerTarget`, `.sequence`, `.filtered`, `.multi`, `.pair`).
- **Remaining**:
  - Extend `TargetFilter` with power/snapshot-power bounds, teamwork mana-value bypass, and stack-ability source predicates so the remaining sub-inductive constructors can be expressed as `.filtered { ... }` or `.multi`.

---

### Priority 7: Encapsulate `CardDef` Flags and `Game` Scratchpad Fields
1. **`CardDef` (`Mtg/Engine/Card/CardDef.lean`) & `ActivatedAbility` (`Mtg/Engine/Card/ActivatedAbility.lean`)**:
   - **Completed in Batch 19**:
     - Unified the 17 ETB fields on `CardDef` into `entersTappedRule : EntersTappedRule := .untapped` (CR 614.1c, 10 constructors), `entersWithCounters : EntersWithCounters := .none` (CR 614.1c, 5 constructors), and `asEntersChoose : AsEntersChoice := .none` (CR 614.12, 5 constructors).
     - Unified the 17 spell cost-reduction and additional-cost fields on `CardDef` into `spellCostReduction : SpellCostReduction := .none` (CR 601.2f, 12 constructors) and `additionalCost : SpellAdditionalCost := .none` (CR 601.2b / 118.8, 6 constructors), reducing `CardDef` from 116 to 87 fields.
     - Unified the 6 mutually-exclusive extra activation cost flags on `ActivationCost` into `extra : ExtraActivationCost := .none` (CR 602.1, 17 constructors, reducing `ActivationCost` from 14 to 8 fields), and unified the 4 cost-reduction fields and 2 equip fields on `ActivatedAbility` into `costReduction : ActivationCostReduction := .none` (CR 602.2b / 601.2f, 5 constructors) and `equipRestriction : EquipRestriction := .none` (CR 702.6, 3 constructors), reducing `ActivatedAbility` from 18 to 14 fields.
   - **Remaining**:
     - Group the ~20 `tapAdd*` fields on `CardDef` into structured mana ability definitions (CR 605).
2. **`Game` & `Player` Per-Turn / Per-Resolution State (`Mtg/Engine/Game/Core.lean`, `Player.lean`, `Turns.lean`)**:
   - Extract per-turn `Player` fields into `pl.thisTurn : PlayerTurnState` and per-turn `Game` fields into `g.thisTurn : GameTurnState` so `Turns.clearTurnActivations` (`Turns.lean:55–143`) resets them with `{ pl with thisTurn := {} }` instead of a 90-line manual field reset.
   - Extract the ~25 `*ThisWay` fields on `Game` (`milledIdsThisWay`, `exiledIdsThisWay`, `sacrificedPowerThisWay`, etc., `Core.lean:310–395`) into `g.thisWay : ResolutionNotes` reset at the start of each resolution.
3. **`ManaPool` (`Mtg/Engine/Mana.lean`) — Completed in Batch 18**:
   - Unified all 27 hardcoded restricted-mana `Nat` counters (`elfWhite`..`creatureGreen`, `cantNonartifact`, `cantNonartifactBlue`) and `fraRestricted` into `restricted : Array (ManaType × ManaUse) := #[]` on `ManaPool` (`Mtg/Engine/Mana.lean`, CR 106.4 / CR 106.6 / CR 106.10).

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
