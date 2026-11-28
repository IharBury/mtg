# Compositional Oracle Parser & Canonical `ToOracle` Printer

`Mtg.Engine.Card` parses official *Magic: The Gathering* Oracle card text through a five-stage compositional pipeline under `Mtg/Engine/Card/Parser/` and formats any `CardDef` back into canonical Oracle text purely via `ToOracle` instances—with zero stored raw-text strings and 100% structural `BEq CardDef` round-trip verification across all cards in `supportedCatalogCards`. Catalog Oracle text follows official Gatherer Oracle text; when Scryfall does not match Gatherer, Gatherer is authoritative.

See [`architecture.md`](./architecture.md) for the overall system map, [`card-and-ability-model.md`](./card-and-ability-model.md) for the AST types produced, and [`game-evaluation.md`](./game-evaluation.md) for how the runtime engine evaluates parsed abilities.

## Five-Stage Pipeline

```mermaid
flowchart LR
    S1["1. FrameSplit (DFC //, //ADV//, //PREP//, Header, TypeLine, Stats)"] --> S2["2. Lexer & OracleNorm (Reminder strip, Labels, Quoted spans)"]
    S2 --> S3["3. ParagraphClass (DeckLimit, Saga, Loyalty, Activated, Triggered, Keyword, Spell, Static)"]
    S3 --> S4["4. Compositional Sub-Grammars + Recursive Quoted-Ability Parser"]
    S4 --> S5["5. DiscourseBind (Anaphora, Instruction.bind, Reflexive Triggers)"]
```

Instead of template or prototype enumeration, the parser uses **deterministic leading-word/prefix dispatch** over quote-aware normalized clauses. Compositional sub-grammars allow $M$ triggers, $K$ conditions, and $N$ instructions to compose in $O(M + K + N)$ grammar rules, including unseen cross-product combinations outside the catalog.

## Module Map

| Module | Stage / Responsibility |
| :--- | :--- |
| [`OracleNorm.lean`](../Mtg/Engine/Card/OracleNorm.lean) | Linear `Array Char` text normalization (`replaceWord`, reminder-text and `{CHAOS}` stripping, flavor ability-word stripping, self-reference folding). |
| [`Parser/FrameSplit.lean`](../Mtg/Engine/Card/Parser/FrameSplit.lean) | **Stage 1**: Face splitting (`//`, `//ADV//`, `//PREP//`), name/mana header, `TypeLine`, P/T `PrintedStat`, color indicator, loyalty, defense, Vanguard modifiers, chapter & loyalty headers. |
| [`Parser/Lexer.lean`](../Mtg/Engine/Card/Parser/Lexer.lean) | **Stage 2**: Mechanic-label extraction (`MechanicLabel`), quote-aware span extraction (`extractQuotedSpans`), and top-level splitting (`splitTopLevelColon`, `splitTopLevelSentences`). |
| [`Parser/ParagraphClass.lean`](../Mtg/Engine/Card/Parser/ParagraphClass.lean) | **Stage 3**: Top-level [`parseOracleCardCompositional`](../Mtg/Engine/Card/Parser/ParagraphClass.lean) deterministic paragraph classification and face assembly. |
| [`Parser/SubGrammars.lean`](../Mtg/Engine/Card/Parser/SubGrammars.lean) | **Stage 4**: Shared clause parsers for noun phrases, `TargetSpec`, `ValueExpr`, `Condition`, `DurationExpr`, `CostSpec`, `KeywordAbility`, `ManaSpec`/`ManaProductionSpec`, static abilities, and trigger headers. |
| [`Parser/TokenEmblemGrammar.lean`](../Mtg/Engine/Card/Parser/TokenEmblemGrammar.lean) | **Stage 4**: Compositional parsers for `TokenSpec` (predefined, custom, copy + `CopyModification` + quoted `GrantedAbility`), `EnterMods`, and `EmblemSpec`. |
| [`Parser/InspectSearchGrammar.lean`](../Mtg/Engine/Card/Parser/InspectSearchGrammar.lean) | **Stage 4**: Compositional parsers for `InspectLibrarySpec`, `SearchLibrarySpec`, `GrantPlayPermSpec`, `MoveMods`, and `.targetsOf` / `.filter` object phrases. |
| [`Parser/InstructionGrammar.lean`](../Mtg/Engine/Card/Parser/InstructionGrammar.lean) | **Stage 4**: Verb-dispatched parser for atomic instructions, multi-sentence sequencing, `ModalSpec` headers, conditional branches, optional/reflexive folding, and `StackOp.counterStack` follow-ups. |
| [`Parser/AbilityGrammar.lean`](../Mtg/Engine/Card/Parser/AbilityGrammar.lean) | **Stage 4**: Recursive quoted `"..."` ability tie-in (`mkQuotedParsers`) and top-level static, activated, triggered, and effect parsers. |
| [`Parser/DiscourseBind.lean`](../Mtg/Engine/Card/Parser/DiscourseBind.lean) | **Stage 5**: `DiscourseCtx`, anaphora resolution (`"it"`, `"that player"`, `"exiled this way"`, `"where X is"`), automatic `Instruction.bind` wrapping, and `VarId` normalization. |
| [`ParseOracle.lean`](../Mtg/Engine/Card/ParseOracle.lean) | Public `@[irreducible, noinline]` entry points (`parseOracleCard`, `parseOracleCard!`), `renderFullOracle`, and structural `oracleRoundtripDiff`. |

---

## Stage-by-Stage Architecture

### Stage 1 — Frame Splitting ([`FrameSplit.lean`](../Mtg/Engine/Card/Parser/FrameSplit.lean))

[`splitCardFrame`](../Mtg/Engine/Card/Parser/FrameSplit.lean) divides raw printed text into structured face frames before rules-text parsing:

- **Multi-face markers**: Splits `//` back faces (CR 712) via [`splitBackFace`](../Mtg/Engine/Card/Parser/FrameSplit.lean) and `//ADV//` / `//PREP//` sub-faces (CR 716 Adventure / CR 723 Prepare) via [`splitAdventure`](../Mtg/Engine/Card/Parser/FrameSplit.lean) and [`splitPrepare`](../Mtg/Engine/Card/Parser/FrameSplit.lean).
- **Headers & printed stats**: Parses name + [`parseManaCost`](../Mtg/Engine/Card/Parser/FrameSplit.lean) (`{W}`, `{2/W}`, `{W/U}`, `{X}`, `{C}`), [`parseTypeLine`](../Mtg/Engine/Card/Parser/FrameSplit.lean) (supertypes, card types, and `CardSubtype`s via [`TypeLine.lean`](../Mtg/Engine/TypeLine.lean)), [`parseColorIndicator`](../Mtg/Engine/Card/Parser/FrameSplit.lean), `"Token"`, [`parsePT`](../Mtg/Engine/Card/Parser/FrameSplit.lean) (`2/2`, `*/*`, `1+*`, `*+1` into `PrintedStat`), [`parseLoyaltyLabel`](../Mtg/Engine/Card/Parser/FrameSplit.lean), [`parseDefenseLabel`](../Mtg/Engine/Card/Parser/FrameSplit.lean), and Vanguard modifiers ([`parseHandLifeLine`](../Mtg/Engine/Card/Parser/FrameSplit.lean), [`parseBareModifierPair`](../Mtg/Engine/Card/Parser/FrameSplit.lean)).
- **Chapter & loyalty headers**: Recognizes Roman chapter prefixes (`I, II — ...` via [`parseChapterHeader`](../Mtg/Engine/Card/Parser/FrameSplit.lean)) and loyalty activation headers (`[+1]:`, `[0]:`, `[-2]:`, `[-X]:` via [`parseLoyaltyAbilityLine`](../Mtg/Engine/Card/Parser/FrameSplit.lean)).

### Stage 2 — Normalization & Quote-Aware Lexing ([`Lexer.lean`](../Mtg/Engine/Card/Parser/Lexer.lean) & [`OracleNorm.lean`](../Mtg/Engine/Card/OracleNorm.lean))

- **Linear text normalization**: [`OracleNorm.lean`](../Mtg/Engine/Card/OracleNorm.lean) strips balanced reminder text `(...)` (CR 207.2a) and `{CHAOS}` headers (CR 207.4), performs linear `Array Char` word replacement ([`replaceWord`](../Mtg/Engine/Card/OracleNorm.lean)), and folds self-references (`<FullCardName>`, legend short names, `"this <type>"`) outside quoted strings.
- **Mechanic labels vs. flavor ability words**: [`extractLeadingLabel`](../Mtg/Engine/Card/Parser/Lexer.lean) extracts mechanic-carrying labels ([`MechanicLabel`](../Mtg/Engine/Card/Parser/Lexer.lean) — `Power-up —`, `Exhaust —`, `Boast —`, `Eminence —`, `Infinity —`, modal anchors, etc.) *before* stripping flavor-only CR 207.2c ability words (such as `Landfall —`).
- **Quote-aware delimiters**: [`extractQuotedSpans`](../Mtg/Engine/Card/Parser/Lexer.lean), [`splitTopLevelColon`](../Mtg/Engine/Card/Parser/Lexer.lean), and [`splitTopLevelSentences`](../Mtg/Engine/Card/Parser/Lexer.lean) ignore `:` and `.` inside `"..."` spans so granted abilities (`Other artifacts you control have "{T}: Add {C}."`, planeswalker emblem text, and token abilities) stay intact for recursive Stage 3–5 parsing.

### Stage 3 — Paragraph Classification ([`ParagraphClass.lean`](../Mtg/Engine/Card/Parser/ParagraphClass.lean))

[`parseOracleCardCompositional`](../Mtg/Engine/Card/Parser/ParagraphClass.lean) dispatches each rules paragraph deterministically in order:

1. **Deck-limit rules** (`"A deck can have any number / up to N cards named ..."` → `CardDef.deckLimitOverride : Option DeckLimit`).
2. **Saga chapters** (`I, II — <effect>` → `TriggeredAbility` with `BatchGrouping.counterThreshold .lore`).
3. **Loyalty abilities** (`[+N]:` / `[0]:` / `[-N]:` / `[-X]:` → `ActivatedAbility` with `CostItem.loyalty`).
4. **Activated abilities** (unquoted top-level `:` → `parseActivatedAbilityComp`, including all `{T}: Add ...` mana abilities; redundant basic-land reminder lines like `({T}: Add {R}.)` are omitted because CR 305.6 synthesizes them from Layer 4 basic land subtypes).
5. **Triggered abilities** (leading `When` / `Whenever` / `At`, or `If <cond>, when/whenever ...` → `parseTriggeredAbilityComp`).
6. **Keyword lines** (comma/semicolon keyword lists and standalone parameterized keywords, including `Equip` and `Cycling`/`Typecycling` stored directly on `CardDef.keywords` and expanded uniformly via `KeywordAbility.expand`).
7. **Spell abilities** (instant/sorcery/`SubFace` paragraphs → `SpellAbility`, detaching `"As an additional cost..."` into `SpellAbility.additionalCosts`, `"This spell costs..."` into `StaticAbility.costModifier`, `"This spell can't be countered"` into `StaticAbility.ruleModifying`, and modal `•` bullets into `Instruction.chooseModes`).
8. **Static abilities** (remaining permanent paragraphs → `StaticAbility`: `Enchant ...`, CDAs, `"As this enters..."`, `"This enters tapped..."`, `"If ... would ..., ... instead"`, CR 722.2 Station threshold striations `N+ | [P/T] ...`, and continuous characteristic/rule/cost modifiers).

### Stage 4 — Compositional Sub-Grammars & Recursive Quoted Abilities

- **Shared sub-grammars ([`SubGrammars.lean`](../Mtg/Engine/Card/Parser/SubGrammars.lean))**:
  - Expressions & targets: [`parseNounPhrase`](../Mtg/Engine/Card/Parser/SubGrammars.lean), [`parseTargetSlot`](../Mtg/Engine/Card/Parser/SubGrammars.lean), [`parseTargetSpec`](../Mtg/Engine/Card/Parser/SubGrammars.lean), [`parseTargetSpecPrefix`](../Mtg/Engine/Card/Parser/SubGrammars.lean), [`parseValueExpr`](../Mtg/Engine/Card/Parser/SubGrammars.lean), [`parseCondition`](../Mtg/Engine/Card/Parser/SubGrammars.lean), [`parseDuration`](../Mtg/Engine/Card/Parser/SubGrammars.lean).
  - Costs, keywords, & mana: [`parseCostItem`](../Mtg/Engine/Card/Parser/SubGrammars.lean), [`parseCostSpec`](../Mtg/Engine/Card/Parser/SubGrammars.lean), [`parseAdditionalCostSpec`](../Mtg/Engine/Card/Parser/SubGrammars.lean), [`parseKeywordAbility`](../Mtg/Engine/Card/Parser/SubGrammars.lean), [`parseKeywordLine`](../Mtg/Engine/Card/Parser/SubGrammars.lean), [`parseManaSpec`](../Mtg/Engine/Card/Parser/SubGrammars.lean), [`parseManaProductionSpec`](../Mtg/Engine/Card/Parser/SubGrammars.lean), [`parseManaAbilityLine`](../Mtg/Engine/Card/Parser/SubGrammars.lean).
  - Static & trigger headers: [`parseStaticAbilityLine`](../Mtg/Engine/Card/Parser/SubGrammars.lean), [`parseTriggerClauses`](../Mtg/Engine/Card/Parser/SubGrammars.lean), [`parseTriggerClause`](../Mtg/Engine/Card/Parser/SubGrammars.lean) (including folding printable `ManaSpentPred` intervening-`"if"` clauses onto `TriggerPattern.castSpell.manaSpent?`).
- **Tokens & emblems ([`TokenEmblemGrammar.lean`](../Mtg/Engine/Card/Parser/TokenEmblemGrammar.lean))**: [`parseTokenDesc?`](../Mtg/Engine/Card/Parser/TokenEmblemGrammar.lean) and [`parseEmblemSpec?`](../Mtg/Engine/Card/Parser/TokenEmblemGrammar.lean) parse predefined/custom/copy tokens, `EnterMods`, `CopyModification`s, and command-zone emblems, delegating quoted `"..."` abilities through `QuotedAbilityParsers`.
- **Library inspection, search & play permissions ([`InspectSearchGrammar.lean`](../Mtg/Engine/Card/Parser/InspectSearchGrammar.lean))**: [`parseInspectLibrarySeq?`](../Mtg/Engine/Card/Parser/InspectSearchGrammar.lean), [`parseSearchLibrarySeq?`](../Mtg/Engine/Card/Parser/InspectSearchGrammar.lean), and [`parseGrantPlayPermClause?`](../Mtg/Engine/Card/Parser/InspectSearchGrammar.lean) (distinguishing immediate CR 608.2g `castNow := true` from timed impulse permissions).
- **Instructions ([`InstructionGrammar.lean`](../Mtg/Engine/Card/Parser/InstructionGrammar.lean))**: [`parseAtomicInstr`](../Mtg/Engine/Card/Parser/InstructionGrammar.lean), [`parseSingleClause`](../Mtg/Engine/Card/Parser/InstructionGrammar.lean), and [`parseCompositionalEffect`](../Mtg/Engine/Card/Parser/InstructionGrammar.lean) dispatch on leading verbs, handle CR 611.2a indefinite vs. timed durations, fold `ModalSpec` bullets, and detect `StackOp.counterStack` follow-ups (exile / free cast).
- **Ability assembly & recursive quotes ([`AbilityGrammar.lean`](../Mtg/Engine/Card/Parser/AbilityGrammar.lean))**: [`mkQuotedParsers`](../Mtg/Engine/Card/Parser/AbilityGrammar.lean) ties [`parseStaticAbilityComp`](../Mtg/Engine/Card/Parser/AbilityGrammar.lean), [`parseActivatedAbilityComp`](../Mtg/Engine/Card/Parser/AbilityGrammar.lean), [`parseTriggeredAbilityComp`](../Mtg/Engine/Card/Parser/AbilityGrammar.lean), and [`parseEffectComp`](../Mtg/Engine/Card/Parser/AbilityGrammar.lean) together so arbitrarily nested quoted abilities become real AST values. `parseActivatedAbilityComp` also sets `CostSpec.bindVar?` automatically whenever `Effect.usesCostPaidObjects eff.body` is true, and `parseTriggeredAbilityComp` binds cast-target anaphors to `.filter (.targetsOf .triggerSubject)`.

### Stage 5 — Discourse & Anaphora Binding ([`DiscourseBind.lean`](../Mtg/Engine/Card/Parser/DiscourseBind.lean))

[`DiscourseCtx`](../Mtg/Engine/Card/Parser/DiscourseBind.lean) tracks accumulated target slots, cross-slot constraints, recent subjects/players, and lexical `VarId` bindings across clauses and sentences:

- [`resolveObjectAnaphor?`](../Mtg/Engine/Card/Parser/DiscourseBind.lean) resolves `"it"`, `"that creature"`, `"those creatures"`, and `"[cards/creatures/tokens] [exiled/milled/destroyed/created/sacrificed/discarded] this way"` into `.target slot`, `.stepObjects var`, or `.triggerSubject`.
- [`resolvePlayerAnaphor?`](../Mtg/Engine/Card/Parser/DiscourseBind.lean) resolves `"its controller"`, `"its owner"`, and `"that player"` into `.controllerOf ...`, `.ownerOf ...`, or `.target slot`.
- [`resolveStepMetric?`](../Mtg/Engine/Card/Parser/DiscourseBind.lean) resolves `"excess damage dealt this way"` and `"where X is ..."` counts into `.stepMetric ... var` (with [`substValueX`](../Mtg/Engine/Card/Parser/DiscourseBind.lean) / [`substInstrX`](../Mtg/Engine/Card/Parser/DiscourseBind.lean) substituting `X`).
- [`assembleBoundSteps`](../Mtg/Engine/Card/Parser/DiscourseBind.lean) wraps antecedent steps in `Instruction.bind var step cont`, [`mkReflexiveWhenYouDo`](../Mtg/Engine/Card/Parser/DiscourseBind.lean) folds `"You may <action>. When you do, <reflexive>."` into `Instruction.optional` + `Instruction.queueReflexiveTrigger` (CR 603.12), and [`normalizeBoundVars`](../Mtg/Engine/Card/Parser/DiscourseBind.lean) canonicalizes lexical `VarId` indices so structurally identical effects have identical ASTs.

---

## Entry Points, Canonical `ToOracle`, and Round-Trip Verification

- **Public parser API ([`ParseOracle.lean`](../Mtg/Engine/Card/ParseOracle.lean))**:
  - [`parseOracleCard`](../Mtg/Engine/Card/ParseOracle.lean) (`@[irreducible, noinline]`): delegates directly to `Parser.parseOracleCardCompositional`.
  - [`parseOracleCard!`](../Mtg/Engine/Card/ParseOracle.lean) (`@[irreducible, noinline]`): panics with the unrecognized line on failure; used by `Catalog.fromOracle` across all catalog cards.
- **Canonical `ToOracle` rendering**:
  - Every AST type implements `ToOracle` (`PrintCtx → α → String`), and [`CardDef.renderFullOracle`](../Mtg/Engine/Card/CardDef.lean) (re-exported as [`ParseOracle.renderFullOracle`](../Mtg/Engine/Card/ParseOracle.lean)) reconstructs the complete printed card—header, type line, stats, color indicator, keywords, spell/activated/triggered/static abilities, deck-limit override, `//` back face, and `//ADV//` / `//PREP//` sub-faces—purely from structured fields.
- **Structural `BEq CardDef` round-trip verification**:
  - [`oracleRoundtripDiff`](../Mtg/Engine/Card/ParseOracle.lean) compares `source == parsed` using structural `BEq CardDef`.
  - [`Mtg/OracleRoundtrip.lean`](../Mtg/OracleRoundtrip.lean) (`lake exe oracle-roundtrip`) checks smoke parses and verifies `parseOracleCard (renderFullOracle c) == .ok c` for every card in `supportedCatalogCards` in a few seconds.
  - [`Mtg/Engine/Tests/ParseOracle.lean`](../Mtg/Engine/Tests/ParseOracle.lean) enforces the full-catalog round-trip at compile time alongside unseen cross-product compositional cards, Stage 1–3 unit `#guard`s, and semantic AST checks covering tricky Stage 4–5 bindings.
