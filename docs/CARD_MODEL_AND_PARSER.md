# Card Model & Oracle Parser (`Mtg/Engine/Card/`)

This document explains the data structures in `Mtg/Engine/Card/` (and its foundational modules `Color`, `Mana`, `TypeLine`, `Turn`, `Zone`) and how the bidirectional prototype-driven Oracle parser (`ParseOracle.lean`) compiles raw card text into `CardDef` values.

---

## 1. Module Inventory

### Foundational Modules (`Mtg/Engine/*.lean`)

| File | Key Types & Responsibilities |
| --- | --- |
| `Mtg/Engine/Color.lean` | `Color` (`.white`, `.blue`, `.black`, `.red`, `.green` — CR 105.1) and `ColorSet` (5-Bool set with `count`, `isMonocolored`, `isMulticolored`, `isColorPair`, `colorPairs`). |
| `Mtg/Engine/Mana.lean` | `ManaType` (`.colored`, `.colorless`), `ManaSymbol` (`.generic`, `.colored`, `.colorless`, `.hybrid`, `.twobrid`, `.x`), `ManaCost` (`manaValue`, `substituteX`, `reduceGeneric`, `reduceByCost`), `ManaUse` (16 spending restrictions, CR 106.6, with `abbrev FraManaUse := ManaUse`), `ManaRestriction` (`.none` / `.only (u : ManaUse)`, CR 106.10), `ManaSpend`, and `ManaPool` (6 color/colorless counters + `restricted : Array (ManaType × ManaUse)`, `spendOne?`, `pay?`, `coveredMana`). |
| `Mtg/Engine/TypeLine.lean` | `CardType` (15 types in CR 205.2a), `Supertype` (5 supertypes in CR 205.4a), `Subtype` (`String`), and complete CR 205.3 subtype tables (`allSubtypes` = 545 entries across 9 `SubtypeClass` categories) with singular/plural matching (`matchSubtypeForm`, `splitPrintedSubtypes`). |
| `Mtg/Engine/Turn.lean` | `Step` (12 turn steps in CR 500.1 from `.untap` to `.cleanup`) and phase/priority queries (`playersReceivePriority`, `next?`). |
| `Mtg/Engine/Zone.lean` | `PlayerId`, `ObjectId`, and `Zone` (`.library`, `.hand`, `.battlefield`, `.graveyard`, `.stack`, `.exile`, `.command`, `.ante`, `.outside` — CR 400.1). |

### Card IR & Parser Modules (`Mtg/Engine/Card/*.lean`)

| File | Role |
| --- | --- |
| `Keywords.lean` | `Keywords` (22 boolean flags + reflection table `Keywords.fields` mapping Oracle names to getters/setters) and `KeywordCounters` (all 11 CR 122.1b keyword counter flags projected to `Keywords` via `KeywordCounters.toKeywords`). |
| `Text.lean` | Shared English number/phrase formatting helpers (`englishNumber`, `timesPhrase`, `indefinite`, `signedStat`, etc.). |
| `Counter.lean` | `CounterKind` (29 counter kinds) with `oracleName`, `countersPhrase`, and token matcher `matchPhrase`. |
| `Token.lean` | `TokenKind` (37 predefined token kinds for HOB/HOC/MSH/FRA) and `createPhrase`. |
| `Targeting.lean` | `TargetZone`, `TargetController`, `TargetFilter` (28-field compositional filter), `TargetPreference`, and unified CR 115 `EffectTargetKind` (9 constructors: 8 field-bearing over 5 CR 115 target-category sub-inductives `BattlefieldTarget`, `GraveyardTarget`, `StackTarget`, `PlayerTarget`, `MultiTarget` + `.filtered`, `.multi`, `.pair` + 1 nullary `.none`). |
| `SpellResolution.lean` | Defines the compositional selector ASTs (`PlayerSelector`, `ObjectSelector`, `NumberSelector`, `CostSelector`, `ConditionSelector`, `ActionSelector`), modifier enums, `SpellCastKind` and `AbilityCastKind`, and the unified `Resolution` inductive (`SpellResolution`, `TriggerResolution`, and `PermanentAction` are aliases for `Resolution`), plus `SpellResolution.toPhrase` and `PermanentAction.toNotation`. |
| `Effect.lean` | `Effect` struct unifying trigger events, targeting, cast hints, `resolution : Resolution`, and `phrase : String`; plus `Effect.toPhrase`. |
| `SpellEffects.lean` | Named `Effect.*` builders for spells and activated abilities, plus `ActivatedAbility.fra` and `FraCandidates.ab`. |
| `Saga.lean` | `SagaChapter`, `SagaDef`, Roman numeral chapter header parsers, and `Effect.chapter*` builders for Saga chapters (CR 714.2b / CR 714.3). |
| `ActivatedAbility.lean` & `OracleActivate.lean` | `LoyaltySymbol`, `CostPick` (16 chosen-object cost shapes, CR 602.2b), `ExtraActivationCost` (17 non-mana activation costs, CR 602.1, `abbrev FraCost`), `ActivationCondition` (10 activation restrictions, CR 602.5b, `abbrev FraActivationCondition`), `ActivationCostReduction` (5 activation cost reductions, CR 602.2b / 601.2f), `EquipRestriction` (3 equip target restrictions, CR 702.6), `ActivationCost` (8 fields including `picks : Array CostPick` and `extra : ExtraActivationCost`), `ActivatedAbility` (14 fields including `condition : ActivationCondition`, `costReduction : ActivationCostReduction`, and `equipRestriction : EquipRestriction`), and builder functions (`OracleActivate.activated`, `equipAbility`, `typecyclingAbility`). |
| `StaticAbility.lean` | Unified CR 604 / CR 613 / CR 614 `StaticAbility` inductive (9 field-bearing constructors over 8 CR category sub-inductives `TypeStatic`, `AbilityStatic`, `CdaStatic`, `PtStatic`, `CombatStatic`, `CostCastStatic`, `RuleStatic`, `KeywordStatic` + `.printed`), `FraStatic` and `StaticShape` as `abbrev`s for `StaticAbility`, `StaticMeta`/`StaticAbility.spec`, and `StaticAbility.toNotation`. |
| `TriggerEvent.lean` | Unified CR 603 `TriggerEvent` inductive (14 constructors: 12 field-bearing over 11 CR 603 event-filter sub-inductives `EntersEvent`..`ActionEvent` + `.or` + 2 nullary `.cascade`, `.fromEffect`), `FraEvent` and `SharedTriggerWhen` as `abbrev`s for `TriggerEvent`, `@[match_pattern] abbrev` aliases, `TriggerEvent.events`, and `TriggerEvent.spec`. |
| `Trigger.lean` | `InterveningCondition` (13 constructors, CR 603.4, `abbrev FraCondition`), `SharedTriggerOpts` (7 fields including `condition : InterveningCondition` and `subtype : Option String`), `TriggeredAbility` (`.triggered (when : TriggerEvent) effect opts`), `TriggerTiming` (10 fields including `condition : InterveningCondition` and `subtype : Option String`), and `SharedTrigger` (`Effect`) reusable trigger builders. |
| `TriggerEffects.lean` | `Effect.ofTrigger` and 91 `Effect.*` leftover trigger builders. |
| `TriggeredAbility.lean` | ~180 `TriggeredAbility.on*` catalog builders, `TriggeredAbility.fra`, and the Oracle text renderer (`TriggeredAbility.toNotation`). |
| `CardDef.lean` | `TapAddForEach`, `AdventureFace`, `EntersTappedRule` (10 ETB tapped replacement rules, CR 614.1c), `EntersWithCounters` (5 ETB counter rules, CR 614.1c), `AsEntersChoice` (5 ETB choice rules, CR 614.12), `SpellCostReduction` (12 spell cost reductions, CR 601.2f), `SpellAdditionalCost` (6 spell additional costs, CR 601.2b / 118.8), `SpellCastOption` (9 optional/alternative casting options, CR 118.8 / 118.9 / 702), `CastPermissionRule` (5 casting permissions/restrictions, CR 601.2 / 601.3 / 608.2a), `CardKeywordRule` (11 parameterized keyword/characteristic rules, CR 702 / 100.2a / 903.3a), `TapManaAbility` (21 activated mana ability variants, CR 605.1a), `ModalRule` (4 modal spell choice rules, CR 700.2), `TopOfLibraryRule` (6 top-of-library permissions, CR 401.5 / 601.3), `CardStaticRule` (22 continuous/replacement static rules, CR 604 / 613 / 614), `CardDef` (42 fields), `structuredAbilityLines`, and `modellingError?`. |
| `OracleNorm.lean` | Reminder-text stripping, ability-word stripping, number-word replacement, and 3-stage line normalization (`lightLine`, `normalizeStructural`, `normalizeUnit`). |
| `OracleArgs.lean` | Bidirectional `ArgM` slot collector/refiller (`takeEffect`, `takeStatic`, `takeActivated`, `takeTriggered`) and token pattern matcher (`Pat`, `patsOfLines`, `matchArgLines`, `splicePhrase`). |
| `OracleCandidates.lean` | The 4 prototype tables (`spellEffects`, `staticAbilities`, `triggeredAbilities`, `activatedAbilities`) + `chapterEffects`. |
| `FrcParse.lean` | `parseFrcLoyaltyEffect` and `parseFrcLine` fallback parser for Reality Fracture Commander cards. |
| `ParseOracle.lean` | Top-level card parser (`parseOracleCard`, `parseFace`, `parseRules`, `parseStructural`, `matchModeled`, `abilityBuckets`, `renderFullOracle`). |
| `Guards.lean` | Compile-time `#guard` tests for the card model and Oracle parser. |

---

## 2. The Card IR: `CardDef`, `Effect`, `Resolution`, and Selectors

### 2.1 `CardDef` (`Mtg/Engine/Card/CardDef.lean`)
A `CardDef` represents a printed card face (with optional `otherFace : Option CardDef` for DFCs, `adventure : Option AdventureFace` for `//ADV//`, and `prepareFace : Option AdventureFace` for `//PREP//`). Its 42 fields (reduced from 116 fields by 12 CR-aligned rule inductives) are organized by CR category:
1. **Printed Characteristics (CR 200–212)**:
   - `name`, `manaCost`, `colorIndicator`, `supertypes`, `types`, `subtypes`, `power`, `toughness`, `powerStar`, `toughnessStar`, `loyalty`, `defense`, `handModifier`, `lifeModifier`, `isToken`.
2. **Keywords & Characteristic Rules (CR 702 / 100.2a / 903.3a)**:
   - `keywords : Keywords`, `keywordRule : CardKeywordRule` (`.ward`, `.crew`, `.prowess`, `.protectionFromColors`, `.cycling`, `.daybound`, `.toxic`, `.cantBlock`, `.anyNumberInDeck`, `.canBeCommander`).
3. **Spell Resolution, Modal Rules, Casting Options & Cost Modifiers (CR 601 / 608 / 700 / 702)**:
   - `spellEffect : Option Effect`, `spellModes : Array Effect`, `modalRule : ModalRule` (CR 700.2), `additionalCost : SpellAdditionalCost` (CR 601.2b / 118.8), `spellCostReduction : SpellCostReduction` (CR 601.2f), `castOption : SpellCastOption` (CR 118.8 / 118.9 / 702), `castPermission : CastPermissionRule` (CR 601.2 / 601.3 / 608.2a), `empowerJace : Option Nat`.
4. **ETB Replacement & Choices (CR 614)**:
   - `entersTappedRule : EntersTappedRule` (CR 614.1c), `entersWithCounters : EntersWithCounters` (CR 614.1c), `asEntersChoose : AsEntersChoice` (CR 614.12), `entersPrepared : Bool`.
5. **Mana Abilities, Top-of-Library Permissions & Static/Activated/Triggered Abilities (CR 602–605 / 714)**:
   - `tapAddMana : Array ManaType`, `tapManaAbility : TapManaAbility` (CR 605.1a), `topOfLibraryRule : TopOfLibraryRule` (CR 401.5 / 601.3), `staticRule : CardStaticRule` (CR 604 / 613 / 614), `triggeredAbilities : Array TriggeredAbility`, `fraTriggerModes : Array Effect`, `activatedAbilities : Array ActivatedAbility`, `planeswalkersYouControlHave : Array ActivatedAbility`, `staticAbilities : Array StaticAbility`, `saga : Option SagaDef`.
6. **Multi-Part & Double-Faced Cards (CR 712 / 715)**:
   - `adventure : Option AdventureFace`, `prepareFace : Option AdventureFace`, `otherFace : Option CardDef`.

### 2.2 `Effect` (`Mtg/Engine/Card/Effect.lean`)
`Effect` is the shared carrier struct used for spells, spell modes, activated abilities, triggered abilities, and Saga chapters:
```lean
structure Effect where
  events               : Array TriggerEvent := #[]
  targeting            : EffectTargeting := .of .none
  allowsZeroTargets    : Bool := false
  maxTargets           : Nat := 0
  dividedDamage        : Option (Nat × Nat) := none
  onceEachTurn         : Bool := false
  optionalOnceEachTurn : Bool := false
  spellCastKind        : SpellCastKind := .extraLand
  abilityCastKind      : AbilityCastKind := .other
  preferAsDefaultMode  : Bool := false
  resolution           : Resolution := .draw 0
  phrase               : String := ""
```

### 2.3 Compositional Selectors (`Mtg/Engine/Card/SpellResolution.lean:202–1250`)
Recent refactorings unified trigger and spell parameters around six composable selector inductives:
- **`PlayerSelector`** (mutual with `ObjectSelector`):
  - `.you`, `.eachPlayer`, `.eachOpponent`, `.opponent`, `.player`, `.target (which : PlayerSelector)`, `.thatPlayer`, `.damagedPlayer`, `.announced`, `.controller (what : ObjectSelector)`, `.targetAt`, `.targetPlayers`, `.extort`, `.eachOpponentAndYouGain1`, `.youLose1Life`.
- **`ObjectSelector`** (**15 constructors**: 13 field-bearing + 2 nullary, down from 177 constructors by grouping 167 non-recursive leaf selectors into 5 CR 109 / CR 400 zone & object-category sub-inductives `TargetObject`, `BattlefieldObject`, `GraveyardExileObject`, `LibraryHandObject`, `SacrificeStackObject` with `@[match_pattern] abbrev` aliases):
  - Set combinators: `.union (what : List ObjectSelector)`, `.intersection (what : List ObjectSelector)`.
  - Announced targets & source: `.source`, `.any`, `.target (which : ObjectSelector := .any)`, `.targetObj (o : TargetObject)`.
  - CR 400 Zone & Object Categories: `.battlefield (o : BattlefieldObject)`, `.graveyardExile (o : GraveyardExileObject)`, `.libraryHand (o : LibraryHandObject)`, `.sacrificeStack (o : SacrificeStackObject)`.
  - Player-parameterized object selectors: `.player (who : PlayerSelector)`, `.cards (n : Nat := 1) (who : PlayerSelector := .you)`, `.creaturesControlledBy (who : PlayerSelector)`, `.graveyardCardsOfType (ty : CardType) (who : PlayerSelector)`, `.mayWheel (n : Nat) (who : PlayerSelector := .eachPlayer)`.
- **`NumberSelector`** (**8 constructors**: 7 field-bearing + 1 nullary, down from 51 constructors by grouping 46 leaf selectors into 3 CR-aligned sub-inductives `StatNumber`, `CountNumber`, and `TurnEventNumber` with `@[match_pattern] abbrev` aliases):
  - `.greatestPower`, `.fixed (n : Int)`, `.count (what : ObjectSelector)`, `.power (of : ObjectSelector)`, `.loyalty (of : ObjectSelector := .source)`, `.stat (s : StatNumber)`, `.countKind (c : CountNumber)`, `.turnEvent (e : TurnEventNumber)`.
- **`CostSelector`** (4 constructors):
  - `.mana (cost : Array ManaSymbol)`, `.sacrifice (count : NumberSelector) (what : ObjectSelector)`, `.discard (count : NumberSelector) (what : ObjectSelector)`, `.or (cs : List CostSelector)`.
- **`ConditionSelector`** (**6 constructors**: all 6 field-bearing, down from 32 constructors by grouping 29 leaf conditions into 3 CR-aligned sub-inductives `StateCondition`, `TurnHistoryCondition`, and `StepNoteCondition` with `@[match_pattern] abbrev` aliases):
  - `.atLeast (left right : NumberSelector)`, `.not (cond : ConditionSelector)`, `.or (conds : List ConditionSelector)`, `.state (s : StateCondition)`, `.turnHistory (t : TurnHistoryCondition)`, `.stepNote (n : StepNoteCondition)`.
- **`TriggerGrantWhat`** (**7 constructors**: all 7 field-bearing, down from 56 constructors by grouping 54 leaf/layer grants into 5 CR 613 / CR 614 / CR 701 sub-inductives `Layer4TypeGrant`, `Layer6AbilityGrant`, `Layer7PtGrant`, `RuleEffectGrant`, and `ActionStateGrant` with `@[match_pattern] abbrev` aliases):
  - `.layer6Ability (g : Layer6AbilityGrant)`, `.copy (of : ObjectSelector)`, `.control (how : TriggerControlHow)`, `.layer4Type (g : Layer4TypeGrant)`, `.layer7PT (g : Layer7PtGrant)`, `.ruleEffect (g : RuleEffectGrant)`, `.actionState (g : ActionStateGrant)`.
- **`ActionSelector`** (8 constructors):
  - `.beBlocked`, `.beBlockedExceptByHaste`, `.untapWhileYouControl`, `.block`, `.castSpellsThisTurn`, `.beCountered`, `.beBlockedByMostLifePlayer`, `.attackJaces`.

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

### 2.7 `EffectTargetKind` Structure (`Mtg/Engine/Card/Targeting.lean`)
`TriggerTargetKind` is a type alias (`abbrev`) for `EffectTargetKind`. After grouping its 75 named targeting shapes into 5 CR 115 target-category sub-inductives (`BattlefieldTarget`, `GraveyardTarget`, `StackTarget`, `PlayerTarget`, `MultiTarget`) with `@[match_pattern] abbrev` aliases, `EffectTargetKind` has **9 total constructors** (**8 field-bearing** + **1 nullary**):
- `.none` — untargeted (CR 115.1)
- `.battlefield (t : BattlefieldTarget)` — permanent targets on the battlefield (CR 115.1 / 110.1)
- `.graveyard (t : GraveyardTarget)` — card targets in a graveyard (CR 115.1 / 404.1)
- `.stack (t : StackTarget)` — spell and ability targets on the stack (CR 115.1 / 405.1)
- `.playerTarget (t : PlayerTarget)` — player and cross-category targets including "any target" (CR 115.1 / 115.4)
- `.sequence (t : MultiTarget)` — multi-target and sequential-slot targeting shapes (CR 115.1 / 601.2c)
- `.filtered (f : TargetFilter)` — one instance of "target" described by a `TargetFilter`
- `.multi (fs : Array TargetFilter) (optional : Array Nat)` — sequential instances of "target" per filter
- `.pair (a b : EffectTargetKind)` — combined target instances of two chosen modes (CR 700.2)

### 2.8 `SharedTrigger` Structure (`Mtg/Engine/Card/SharedTrigger.lean`)
After grouping its 166 effect and leftover constructors into 7 CR 603 / CR 608 / CR 701 effect-category sub-inductives (`LibraryTrigger`, `TokenCounterTrigger`, `CombatDamageTrigger`, `ZoneChangeTrigger`, `ContinuousTrigger`, `PermanentTrigger`, `EventLeftover`) with `@[match_pattern] abbrev` aliases, `SharedTrigger` has **10 total constructors** (all 10 field-bearing):
- `.library (t : LibraryTrigger)` — CR 121 / CR 701.13 / CR 701.18 / CR 701.20 / CR 701.25 / CR 701.48 draw, scry, surveil, mill, search/reveal library, connive, and cascade effects
- `.tokenCounter (t : TokenCounterTrigger)` — CR 111 / CR 122 / CR 701.36 / CR 701.47 token creation, amass, recruit, investigate, counter placement/removal, Ring tempts, and Plan effects
- `.combatDamage (t : CombatDamageTrigger)` — CR 119 / CR 120 / CR 506 / CR 701.3 / CR 701.12 damage, life gain/loss, P/T modification, Equipment attachment, fight, and extra combat effects
- `.zoneChange (t : ZoneChangeTrigger)` — CR 400 / CR 701.8 / CR 701.9 / CR 701.17 exile, return from graveyard/exile, put onto battlefield, sacrifice, destroy, and discard effects
- `.continuous (t : ContinuousTrigger)` — CR 611 / CR 700.2 / CR 701.21 / CR 706 continuous grants, tap/untap, control change, mana production, spell cast/copy, modal, and prepare effects
- `.permanent (t : PermanentTrigger)` — `PermanentAction` applied to target, source, enchanted, or attached permanent
- `.leftover (t : EventLeftover)` — event-specific leftover families (`enter`, `step`, `death`, `thisAttack`, `enterOrAttack`, `watch`, `youAttacking`, `casting`, `resource`)
- `.chapter (n : Nat) (e : ChapterResolution)` — CR 714 Saga chapter effects
- `.mayTo (can thenDo : SharedTrigger)` and `.may (action : SharedTrigger)` — CR 603.5 optional/reflexive trigger combinators

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
