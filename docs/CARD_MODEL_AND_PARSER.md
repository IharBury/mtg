# Card Model & Oracle Parser (`Mtg/Engine/Card/`)

This document explains the data structures in `Mtg/Engine/Card/` (and its foundational modules `Color`, `Mana`, `TypeLine`, `Turn`, `Zone`) and how the bidirectional prototype-driven Oracle parser (`ParseOracle.lean`) compiles raw card text into `CardDef` values.

---

## 1. Module Inventory

### Foundational Modules (`Mtg/Engine/*.lean`)

| File | Key Types & Responsibilities |
| --- | --- |
| `Mtg/Engine/Color.lean` | `Color` (`.white`, `.blue`, `.black`, `.red`, `.green` — CR 105.1) and `ColorSet` (5-Bool set with `count`, `isMonocolored`, `isMulticolored`, `isColorPair`, `colorPairs`). |
| `Mtg/Engine/Mana.lean` | `ManaType` (`.colored`, `.colorless`), `ManaSymbol` (`.generic`, `.colored`, `.colorless`, `.hybrid`, `.twobrid`, `.x`), `ManaCost` (`manaValue`, `substituteX`, `reduceGeneric`, `reduceByCost`), `FraManaUse` (10 spending restrictions), `ManaSpend`, and `ManaPool` (`spendOne?`, `pay?`, `coveredMana`). |
| `Mtg/Engine/TypeLine.lean` | `CardType` (15 types in CR 205.2a), `Supertype` (5 supertypes in CR 205.4a), `Subtype` (`String`), and complete CR 205.3 subtype tables (`allSubtypes` = 545 entries across 9 `SubtypeClass` categories) with singular/plural matching (`matchSubtypeForm`, `splitPrintedSubtypes`). |
| `Mtg/Engine/Turn.lean` | `Step` (12 turn steps in CR 500.1 from `.untap` to `.cleanup`) and phase/priority queries (`playersReceivePriority`, `next?`). |
| `Mtg/Engine/Zone.lean` | `PlayerId`, `ObjectId`, and `Zone` (`.library`, `.hand`, `.battlefield`, `.graveyard`, `.stack`, `.exile`, `.command`, `.ante`, `.outside` — CR 400.1). |

### Card IR & Parser Modules (`Mtg/Engine/Card/*.lean`)

| File | Role |
| --- | --- |
| `Keywords.lean` | `Keywords` (22 boolean flags + reflection table `Keywords.fields` mapping Oracle names to getters/setters) and `KeywordCounters` (8 boolean counter flags). |
| `Text.lean` | Shared English number/phrase formatting helpers (`englishNumber`, `timesPhrase`, `indefinite`, `signedStat`, etc.). |
| `Counter.lean` | `CounterKind` (29 counter kinds) with `oracleName`, `countersPhrase`, and token matcher `matchPhrase`. |
| `Token.lean` | `TokenKind` (37 predefined token kinds for HOB/HOC/MSH/FRA) and `createPhrase`. |
| `Targeting.lean` | `TargetZone`, `TargetController`, `TargetFilter` (28-field compositional filter), `TargetPreference`, and `EffectTargetKind` (70 named target kinds + `.filtered`, `.multi`, `.pair`). |
| `PermanentAction.lean` | `PermanentAction` (21 single-permanent actions such as `.pump`, `.destroy`, `.tap`, `.untap`, `.setBasePT`, `.exile`). |
| `AbilityResolution.lean` | `AbilityCastKind` heuristic categories for activated abilities. |
| `SpellResolution.lean` | Defines the compositional selector ASTs (`PlayerSelector`, `ObjectSelector`, `NumberSelector`, `CostSelector`, `ConditionSelector`, `ActionSelector`), modifier enums, and the unified `Resolution` inductive (`SpellResolution` and `TriggerResolution` are `abbrev`s for `Resolution`), plus `SpellResolution.toPhrase`. |
| `Effect.lean` | `Effect` struct unifying targeting, cast hints, `resolution : Resolution`, `sharedTrigger : Option SharedTrigger`, and `phrase : String`; plus conversion helpers (`Resolution.toSpellStep`, `Effect.spellResolution`). |
| `SpellEffects.lean` | Named `Effect.*` builders for spells and activated abilities, plus `ActivatedAbility.fra` and `FraCandidates.ab`. |
| `Chapter.lean` & `ChapterEffects.lean` | `ChapterSpell`, `ChapterResolution` (24 Saga chapter constructors), and `Effect.ofChapter` / `Effect.chapter*` builders. |
| `Saga.lean` | `SagaChapter`, `SagaDef`, and Roman numeral chapter header parsers. |
| `ActivatedAbility.lean` & `OracleActivate.lean` | `LoyaltySymbol`, `FraCost`, `FraActivationCondition`, `ActivationCost` (21 fields), `ActivatedAbility` (23 fields), and builder functions (`OracleActivate.activated`, `equipAbility`, `typecyclingAbility`). |
| `StaticAbility.lean` | Unified CR 604 / CR 613 / CR 614 `StaticAbility` inductive (9 field-bearing constructors over 8 CR category sub-inductives `TypeStatic`, `AbilityStatic`, `CdaStatic`, `PtStatic`, `CombatStatic`, `CostCastStatic`, `RuleStatic`, `KeywordStatic` + `.printed`), `FraStatic` and `StaticShape` as `abbrev`s for `StaticAbility`, `StaticMeta`/`StaticAbility.spec`, and `StaticAbility.toNotation`. |
| `TriggerEvent.lean` | Unified CR 603 `TriggerEvent` inductive (14 constructors: 12 field-bearing over 11 CR 603 event-filter sub-inductives `EntersEvent`..`ActionEvent` + `.or` + 2 nullary `.cascade`, `.fromEffect`), `FraEvent` and `SharedTriggerWhen` as `abbrev`s for `TriggerEvent`, `@[match_pattern] abbrev` aliases, `TriggerEvent.events`, and `TriggerEvent.spec`. |
| `SharedTrigger.lean` | 9 MSH `*Leftover` enums, `SharedTrigger` (116 constructors), `FraCondition`, and `SharedTriggerOpts`. |
| `Trigger.lean` | `TriggeredAbility` (`.triggered (when : TriggerEvent) effect opts`), `TriggerTiming`, `TriggeredAbility.chapterTiming`, and `SharedTrigger.timing` (compiles `SharedTrigger` into `Resolution`). |
| `TriggerEffects.lean` | `Effect.ofTrigger` and 92 `Effect.*` leftover trigger wrappers. |
| `TriggeredAbility.lean` | ~180 `TriggeredAbility.on*` catalog builders, `TriggeredAbility.fra`, and the Oracle text renderer (`TriggeredAbility.toNotation`). |
| `CardDef.lean` | `TapAddForEach`, `AdventureFace`, `CardDef` (~118 fields), `structuredAbilityLines`, and `modellingError?`. |
| `OracleNorm.lean` | Reminder-text stripping, ability-word stripping, number-word replacement, and 3-stage line normalization (`lightLine`, `normalizeStructural`, `normalizeUnit`). |
| `OracleArgs.lean` | Bidirectional `ArgM` slot collector/refiller (`takeEffect`, `takeStatic`, `takeActivated`, `takeTriggered`) and token pattern matcher (`Pat`, `patsOfLines`, `matchArgLines`, `splicePhrase`). |
| `OracleCandidates.lean` | The 4 prototype tables (`spellEffects`, `staticAbilities`, `triggeredAbilities`, `activatedAbilities`) + `chapterEffects`. |
| `FrcParse.lean` | `parseFrcLoyaltyEffect` and `parseFrcLine` fallback parser for Reality Fracture Commander cards. |
| `ParseOracle.lean` | Top-level card parser (`parseOracleCard`, `parseFace`, `parseRules`, `parseStructural`, `matchModeled`, `abilityBuckets`, `renderFullOracle`). |
| `Guards.lean` | Compile-time `#guard` tests for the card model and Oracle parser. |

---

## 2. The Card IR: `CardDef`, `Effect`, `Resolution`, and Selectors

### 2.1 `CardDef` (`Mtg/Engine/Card/CardDef.lean`)
A `CardDef` represents a printed card face (with optional `otherFace : Option CardDef` for DFCs, `adventure : Option AdventureFace` for `//ADV//`, and `prepareFace : Option AdventureFace` for `//PREP//`). Its fields fall into two groups:
1. **Core Printed & Modeled Collections**:
   - Identification & types: `name`, `manaCost`, `colorIndicator`, `supertypes`, `types`, `subtypes`, `power`, `toughness`, `startingLoyalty`, `startingDefense`, `isToken`, `daybound`, `nightbound`.
   - Keywords: `keywords : Keywords`.
   - Spell resolution: `spellEffect : Option Effect`, `spellModes : Array Effect`, `minSpellModes`, `maxSpellModes`, `allowRepeatModes`, `hasSpree`.
   - Abilities: `triggeredAbilities : Array TriggeredAbility`, `activatedAbilities : Array ActivatedAbility`, `staticAbilities : Array StaticAbility`, `saga : Option SagaDef`.
   - Modal trigger metadata: `fraTriggerModes : Array Effect`, `fraTriggerChooseUpTo : Bool`, `fraTriggerRepeatModes : Bool`, `fraTriggerIsAttack : Bool`, `fraTriggerSubtypeFilter : Option String`.
2. **Structural / Bespoke Card Flags (~85 fields)**:
   - Mana production flags (`tapAddMana`, `tapAddEach`, `tapAddAnyColor`, `tapSacrificeAddAnyColor`, `addAnyColorSpendOnlySubtype`, `fraAddRestricted`, `frcTapAddColors`, etc.).
   - Cost modifiers (`costReductionIfCreatureDied`, `costReductionPerSubtype`, `additionalCostSacrificeCreature`, `additionalCostOrPay`, `convoke`, `improvise`, `delve`, `hasAffinityForArtifacts`, `kickerCost`, `morphCost`, `impendingCost`, `flashbackCost`, `sneakCost`, etc.).
   - ETB replacement modifiers (`entersTapped`, `entersTappedUnlessTwoOtherLands`, `entersWithCounters`, `asEntersChooseColor`, `asEntersChooseCreatureType`, etc.).
   - Special static flags (`foodAlsoCreatesTreasure`, `tokenDoubling`, `exileOppCreaturesInstead`, `mayLookAtTopAnytime`, `mayCastCreaturesFromTop`, `mayPlayLandsFromTop`, etc.).

### 2.2 `Effect` (`Mtg/Engine/Card/Effect.lean`)
`Effect` is the shared carrier struct used for spells, spell modes, activated abilities, triggered abilities, and Saga chapters:
```lean
structure Effect where
  targeting          : EffectTargeting := {}
  allowsZeroTargets  : Bool := false
  maxTargets         : Option Nat := none
  dividedDamage      : Option Nat := none
  spellCastKind      : SpellCastKind := .other
  abilityCastKind    : AbilityCastKind := .other
  preferAsDefaultMode: Bool := false
  resolution         : Resolution := .none
  sharedTrigger      : Option SharedTrigger := none
  phrase             : String := ""
```

### 2.3 Compositional Selectors (`Mtg/Engine/Card/SpellResolution.lean:118–1128`)
Recent refactorings unified trigger and spell parameters around six composable selector inductives:
- **`PlayerSelector`** (mutual with `ObjectSelector`):
  - `.you`, `.eachPlayer`, `.eachOpponent`, `.activePlayer`, `.defendingPlayer`, `.attackedPlayer`, `.target (who : PlayerSelector)`, `.thatPlayer`, `.controller (of : ObjectSelector)`, `.owner (of : ObjectSelector)`.
- **`ObjectSelector`** (81 constructors):
  - Set combinators: `.union (a b : ObjectSelector)`, `.intersection (a b : ObjectSelector)`, `.other (of : ObjectSelector)`.
  - Announced targets: `.target (what : ObjectSelector)` (where `what` specifies the restriction, e.g. `.creatures`, `.Spells`, `.permanents`).
  - Contextual objects: `.source`, `.cause`, `.enchanted`, `.equipped`, `.it`, `.lookedAt`, `.revealed`, `.exiledWithSource`.
  - Battlefield/zone filters: `.youControl`, `.opponentsControl`, `.creatures`, `.artifacts`, `.lands`, `.nonlandPermanents`, `.ofSubtype (s : String)`, `.othersOfSubtype (s : String)`, `.withCounter (c : CounterKind)`, `.powerAtMost (n : NumberSelector)`, `.manaValueAtMost (n : NumberSelector)`, `.cardsInHand (who : PlayerSelector)`, `.cardsInGraveyard (who : PlayerSelector)`, etc.
- **`NumberSelector`** (36 constructors):
  - `.fixed (n : Int)`, `.negated (a : NumberSelector)`, `.count (of : ObjectSelector)`, `.power (of : ObjectSelector)`, `.toughness (of : ObjectSelector)`, `.manaValue (of : ObjectSelector)`, `.countersOn (c : CounterKind) (of : ObjectSelector)`, `.lifeGainedThisTurn`, `.cardsDrawnThisTurn`, `.xValue`, `.greatestPower (among : ObjectSelector)`, etc.
- **`CostSelector`**:
  - `.mana (cost : Array ManaSymbol)`, `.sacrifice (count : NumberSelector) (what : ObjectSelector)`, `.discard (count : NumberSelector) (what : ObjectSelector)`, `.or (a b : CostSelector)`.
- **`ConditionSelector`** (29 constructors):
  - `.and`, `.or`, `.not`, `.atLeast (actual min : NumberSelector)`, `.countAtLeast (what : ObjectSelector) (min : Int)`, `.controlsSubtype`, `.isYourTurn`, `.attackedThisTurn`, `.gainedLifeThisTurn`, `.lostLifeThisTurn`, `.wasCast`, etc.
- **`ActionSelector`**:
  - `.exile`, `.mayCast`, `.put`.

### 2.4 `Resolution` Structure (`Mtg/Engine/Card/SpellResolution.lean:2228–3149`)
`SpellResolution` and `TriggerResolution` are both type aliases (`abbrev`) for `Resolution`. After consolidating **325 redundant spell, ability, trigger, FRA, and FRC constructors** across eleven batches into compositional selector-parameterized constructors and CR-aligned `@[match_pattern] abbrev` aliases, `Resolution` has **39 total constructors** (**33 field-bearing** + **6 nullary**):

1. **Compositional Selector IR (lines 2228–3037)**:
   - Takes `ObjectSelector`, `PlayerSelector`, `NumberSelector`, `CostSelector`, and `ConditionSelector` arguments.
   - Its 33 field-bearing constructors are `.pump`, `.dealDamage`, `.scry` (also covering `.surveil` via `surveil : Option TriggerSurveilNote := none`, CR 701.25), `.draw`, `.searchLibrary`, `.discard`, `.pay`, `.putCounters` (also covering `.proliferate` via `.eachKindOnIt` and `.removeCounters` via `.remove`, CR 122 / CR 701.34), `.returnToHand`, `.put`, `.putOnLibrary`, `.createTokens`, `.amass`, `.exile`, `.sacrifice`, `.attach`, `.mayCast`, `.addMana`, `.chooseModes` (also covering `.or` via `.one` and `.ifElse` via `.ifElse cond`, CR 700.2 / CR 608.2c), `.destroy`, `.tap` (also covering `.untap` via `tapped : Bool := true`, CR 701.26), `.grant` (covering continuous effects across CR 613 Layers 1–7, CR 614 replacement effects, cost reductions, and keyword actions via `@[match_pattern] abbrev`s `.lose`, `.cant`, `.becomeArtifact`, `.becomePrepared`, `.setBasePT`, `.gainControl`, `.becomeCopy`, `.replace`, `.spellsCostLess`, `.investigate`, `.empowerJace`, `.recruit`, `.noteResolveThisTurn`, `.mshReflexive`), `.gainLife` (also covering `.loseLife` via `lose : Bool := false`, CR 119), `.mill`, `.revealLibrary` (also covering `.revealFromHand` via `.fromHand`, CR 701.16), `.connive`, `.queueReflexive`, `.sequence`, `.may`, `.«if»`, `.fight`, `.onPermanent` (with `@[match_pattern] abbrev onSource`), and `.unlessPays`.
2. **Nullary Block (lines 3038–3054)**:
   - All 33 field-bearing constructors are placed before the nullary block (max field-bearing constructor tag = **32**, leaving **211 of 244 field-bearing constructor slots** free below Lean's 243 limit), and all 6 nullary constructors (`.cascade`, `.ringTempts`, `.additionalCombatPhase`, `.winTheGame`, `.counter`, `.unrecognized`) are grouped at the end of `Resolution`.

### 2.5 `TriggerEvent` Structure (`Mtg/Engine/Card/TriggerEvent.lean`)
`FraEvent` and `SharedTriggerWhen` are both type aliases (`abbrev`) for `TriggerEvent`. After consolidating the 3 separate trigger-event inductives (previously 235 constructors across `TriggerEvent`, `FraEvent`, and `SharedTriggerWhen`), `TriggerEvent` has **14 total constructors** (**12 field-bearing** + **2 nullary**) aligned with the CR 603 trigger-event categories:
1. **CR 603 Event-Category Constructors (12 field-bearing)**:
   - `.enters (which : EntersEvent := .source)` — CR 603.6a enters-the-battlefield events
   - `.leaves (which : LeavesEvent := .dies)` — CR 603.6c / CR 603.10a leaves-the-battlefield, dies, and graveyard zone-change events
   - `.step (which : StepEvent := .yourUpkeep)` — CR 603.2b beginning-of-step/phase events
   - `.casts (which : CastEvent := .youSpell)` — CR 601.2i spell-cast events
   - `.combat (which : CombatEvent := .sourceAttacks)` — CR 508.1m / CR 509.1h attack and block events
   - `.damage (which : DamageEvent := .sourceCombatToPlayer)` — CR 120.2 / CR 510.2 damage events
   - `.draws (which : DrawEvent := .you)` — CR 121.1 card-draw events
   - `.discards (which : DiscardEvent := .you)` — CR 701.9 discard and cycling events
   - `.taps (which : TapEvent := .source)` — CR 603.2f / CR 701.26a becomes-tapped events
   - `.counters (which : CounterEvent := .youPutPlusOne)` — CR 122 / CR 714.2 counter-placement, proliferate, and Saga chapter events
   - `.action (which : ActionEvent := .becomesTarget)` — CR 602 / CR 701 / CR 119 activated-ability, targeting, token, sacrifice, life, scry/surveil, and Ring events
   - `.or (a b : TriggerEvent)` — compound disjunctive trigger conditions (`enterOrAttack`, `castGreenOrForestEnters`, `enterOrOpponentDrawsExceptFirst`)
2. **Nullary Constructors (2 nullary)**:
   - `.cascade` (CR 702.85a) and `.fromEffect` (deferred to the inner `SharedTrigger`'s timing).

### 2.6 `StaticAbility` Structure (`Mtg/Engine/Card/StaticAbility.lean`)
`FraStatic` and `StaticShape` are both type aliases (`abbrev`) for `StaticAbility`. After consolidating the 3 separate static-ability inductives (previously 255 constructors across `StaticAbility`, `FraStatic`, and `StaticShape`), `StaticAbility` has **9 total constructors** (all 9 field-bearing) aligned with the CR 604 / CR 613 / CR 614 static-ability categories:
- `.typeChange (which : TypeStatic)` — CR 613.1d Layer 4 type-changing static effects
- `.ability (which : AbilityStatic)` — CR 613.1f Layer 6 ability-adding and ability-removing static effects
- `.cda (which : CdaStatic)` — CR 604.3 / CR 613.4a Layer 7a characteristic-defining P/T abilities
- `.pt (which : PtStatic)` — CR 613.4c Layer 7c power/toughness-modifying static effects
- `.combat (which : CombatStatic)` — CR 508 / CR 509 / CR 510 combat requirements, restrictions, and damage assignment
- `.costCast (which : CostCastStatic)` — CR 601.2f / CR 601.3 / CR 305.1 cost modifiers, casting permissions, and casting restrictions
- `.rule (which : RuleStatic)` — CR 614 / CR 615 / CR 603.2d / CR 704 replacement, prevention, trigger-modification, and rule-modifying static effects
- `.keyword (which : KeywordStatic)` — CR 702 / CR 303.4 / CR 605 keyword, enchant, and intrinsic mana static abilities
- `.printed (text : String)` — fallback printed text for unmodeled lines

---

## 3. How the Oracle Parser Works

`parseOracleCard` (`Mtg/Engine/Card/ParseOracle.lean:2153`) parses raw multi-line card text into a `CardDef` in five stages:

```
Raw Oracle Text
  │
  ├─► 1. Face & Frame Splitting (`ParseOracle.lean`: `splitBackFace`, `splitAdventure`, `splitPrepare`, `parseTypeLine`, `parsePT`)
  │
  ├─► 2. Line Normalization (`OracleNorm.lean`: `dropReminderText`, `stripAbilityWords`, `lightLine`, `normalizeStructural`, `normalizeUnit`)
  │
  ├─► 3. Rule Line Dispatch (`ParseOracle.lean:parseRules`):
  │      ├─► Loyalty / Chapter / Keyword lines
  │      ├─► Structural card flags (`parseStructural`, `parseTap`)
  │      ├─► Modal headers (`parseTriggerModes`, `parseModes`)
  │      ├─► Prototype Bucket Lookup & Slot Refilling (`OracleCandidates` + `OracleArgs` + `matchModeled`)
  │      ├─► Multi-sentence spell sequence splitting (`spellSentenceSequence`)
  │      └─► FRC substring fallback (`FrcParse.parseFrcLine`)
  │
  └─► 4. Completeness Check (`CardDef.modellingError?`)
```

### 3.1 Normalization Levels (`Mtg/Engine/Card/OracleNorm.lean`)
Before matching a rules line, `OracleNorm` strips reminder text `( ... )`, `{CHAOS}` symbols, and 62+ ability words (`Landfall —`, `Ferocious —`, `Power-up —`, etc.), and produces three normalized views:
1. **`lightLine`**: Lowercases, converts number words (`"two"` → `"2"`), and strips punctuation, **preserving the literal card name and phrasing**. Exact matches on `lightLine` score higher than phrase-normalized matches.
2. **`normalizeStructural`**: Replaces card-name aliases (`"Gandalf, Spark Starter"` and `"Gandalf"` → `"this"`), folds `"this creature"` → `"this"`, drops leading `"this "`, and converts number words **without** collapsing phrase equivalences (preserving open subtype nouns).
3. **`normalizeUnit`**: Applies `normalizePhrases` (~50 canonical rewrites in `OracleNorm.lean:400–452`) on top of `normalizeStructural`.

### 3.2 Bidirectional Prototype Indexing (`OracleCandidates.lean` & `OracleArgs.lean`)
Instead of writing handwritten parser combinators for every ability, the parser learns token patterns from prototype ASTs listed in `Mtg/Engine/Card/OracleCandidates.lean` (`spellEffects`, `staticAbilities`, `triggeredAbilities`, `activatedAbilities`, `chapterEffects`):
1. **Render Prototype to Text**: Each prototype AST is rendered to canonical English using sentinel card name `"CARDNAME"` (`effectLines`, `StaticAbility.toNotation`, `TriggeredAbility.toNotation`, `printedActivated`).
2. **Collect Argument Slots (`.collect` mode in `OracleArgs.lean`)**:
   - `collectParsed` runs `takeEffect`, `takeStatic`, `takeActivated`, or `takeTriggered` in the `ArgM` state monad to extract an ordered `Array SlotVal` of parameters (`Nat`, `Int`, `String`, `CardType`, `Supertype`, `EffectTargetKind`, `CounterKind`) from the prototype AST.
3. **Build Token Pattern (`patsOfLines` in `OracleArgs.lean:1084–1112`)**:
   - Scans the prototype's normalized tokens against all textual renderings of each `SlotVal` (`hitsAt`) and replaces matching spans with typed pattern holes (`.nat i fmt`, `.int i fmt`, `.str i fmt`, `.ty i`, `.sup i`, `.kind i`, `.pt i j signed`, `.counterPhrase ni ki`), leaving fixed words as `.lit tok`.
4. **Hash-Bucket Indexing (`abilityBuckets` in `ParseOracle.lean:1379`)**:
   - Indexes prototypes into a `Std.HashMap String (Array Nat)` by first-line skeleton keys (`lineKeys` with digits replaced by `#`, `headWord`, `wildcardHead`, `abstractCyclingLine`, `abstractSubtypeLine`, `abstractCounterLine`).
5. **Match & Refill at Parse Time (`matchModeled` in `ParseOracle.lean:1478`)**:
   - When parsing a card line, `candidatesFor` retrieves candidate prototypes from `abilityBuckets`.
   - `matchArgLines` binds the line's tokens against the candidate's `Pat` holes to produce an updated `Array SlotVal`.
   - `refillParsed` runs `ArgM` in `.fill` mode (`refillEffect`, `refillStatic`, `refillActivated`, `refillTriggered`) to substitute the bound arguments back into the prototype AST, splices the updated values into `Effect.phrase` (`splicePhrase`), and recomputes `SharedTrigger.timing` when `sharedTrigger.isSome`.
   - Matches are ranked lexicographically by `(linesMatched, isLiteralMatch, priority, -catalogOrder)`.
Name-specific FRA/MSH prototypes that contain no open slots still match via the exact same bucket mechanism with zero holes.
