import Mtg.Engine.Card.Primitives
import Mtg.Engine.Card.ManaTypes
import Mtg.Engine.Card.Text
import Mtg.Engine.Card.Counter
import Mtg.Engine.Card.Expr
import Mtg.Engine.Card.Cost
import Mtg.Engine.Card.Keywords
import Mtg.Engine.Card.ManaSpec
import Mtg.Engine.Card.Token
import Mtg.Engine.Card.Targeting
import Mtg.Engine.Card.SpellResolution
import Mtg.Engine.Card.AbilityResolution
import Mtg.Engine.Card.Ability
import Mtg.Engine.Card.Effect
import Mtg.Engine.Card.ActivatedAbility
import Mtg.Engine.Card.TriggerPattern
import Mtg.Engine.Card.Trigger
import Mtg.Engine.Card.TriggeredAbility
import Mtg.Engine.Card.StaticAbility
import Mtg.Engine.Card.KeywordExpand
import Mtg.Engine.Card.CardDef
import Mtg.Engine.Card.OracleNorm
import Mtg.Engine.Card.Parser.FrameSplit
import Mtg.Engine.Card.Parser.Lexer
import Mtg.Engine.Card.Parser.SubGrammars
import Mtg.Engine.Card.Parser.DiscourseBind
import Mtg.Engine.Card.Parser.TokenEmblemGrammar
import Mtg.Engine.Card.Parser.InspectSearchGrammar
import Mtg.Engine.Card.Parser.InstructionGrammar
import Mtg.Engine.Card.Parser.AbilityGrammar
import Mtg.Engine.Card.Parser.ParagraphClass
import Mtg.Engine.Card.ParseOracle

/-!
# Card characteristics (CR 108, 109.3, section 2)

A card’s Oracle characteristics: name, mana cost, color, type line, rules
text, and (when applicable) power, toughness, keywords, and the static,
triggered, activated, and spell abilities we currently model.

This module re-exports the `Mtg.Engine.Card.*` files, one per abstraction:

- `Primitives`: shared zone, designation, cost, replacement-tier, type/color
  modification, and Layer 3 `TextChange`/`HasTextChange` primitives.
- `ManaTypes`: Layer-0 evaluated mana types (`ManaType`, `ManaOutput`) and
  compositional `ManaSpendRestriction` (CR 106), below `Mtg.Engine.Mana`.
- `Text`: shared Oracle-text phrase helpers.
- `Counter`: counter kinds a permanent can carry (CR 122, incl. all 15 CR 122.1b
  keyword counters).
- `Expr`: Layer-1 pure expression algebra (`VarId`, `LibraryPosSpec`,
  `PlayerFilter`/`PlayerExpr`, `ObjectPred`/`ObjectFilter`/`ObjectExpr`,
  `ValueExpr`, `Condition`, `DurationExpr`), `HasTextChange`, and `ToOracle`.
- `Cost`: Layer-2 compositional `CostSpec`/`CostItem`, `LoyaltySymbol`,
  `AdditionalCostSpec`, and `AlternativeCostSpec` (CR 118, 606.2–6).
- `Keywords`: Layer-2 parameterized `KeywordAbility` / `SimpleKeyword` and
  `CounterKind.grantedKeyword?` (CR 702, 122.1b).
- `ManaSpec`: symbolic `ManaPoolPalette` and `ManaSpec` generalized over
  `ValueExpr`, `ObjectExpr`, and `PlayerExpr` (CR 106 / 605).
- `Token`: unified parameterized `TokenSpec` (CR 111 / 707.9) over `ValueExpr`
  and `ObjectExpr`.
- `Targeting`: unified `TargetSpec` / `TargetSlot` / `TargetDomain` and
  `HasTargeting` (CR 115.1).
- `Parser.{FrameSplit, Lexer, SubGrammars, DiscourseBind, TokenEmblemGrammar,
  InspectSearchGrammar, InstructionGrammar, AbilityGrammar, ParagraphClass}`:
  five-stage compositional Oracle parser (CR 113.3 / 201–212 / 602–616 / 702).
- `ParseOracle`: public entry points (`parseOracleCard`, `renderFullOracle`,
  `formatPrintedCard`, `oracleRoundtripDiff`).
- `SpellResolution` / `AbilityResolution`: demo-agent
  `SpellCastKind`/`AbilityCastKind` classification enums.
- `Ability`: unified `Instruction` AST, `Effect`, `ActivatedAbility`,
  `TriggeredAbility`, `StaticAbility`, `GrantedAbility`, and `SpellAbility`.
- `Effect`: `Instruction` smart constructors, core generic `Effect` helpers,
  `ToOracle`, and pure computed agent classifiers
  (`classifyForAgent` / `classifyAbilityForAgent`).
- `ActivatedAbility` / `StaticAbility`: printed ability helpers (CR 602 / 604).
- `TriggerPattern` / `Trigger`: unified trigger event patterns, batch
  groupings, turn limits, CR 603.10a–f look-back, CR 605.1b triggered mana
  ability classification, and Saga chapter triggers (CR 603 / 715.2).
- `TriggeredAbility`: core triggered-ability constructors, `HasTargeting`, and
  canonical `ToOracle` rendering (test-only named builder tables live under
  `Mtg.Engine.Tests.Builders`).
- `KeywordExpand`: pure CR 702.1 `KeywordAbility.expand` lowering keywords directly
  into unified static/triggered/activated/additional/alternative/special-action/instruction rules.
- `CardDef`: `PrintedStat`, `DeckLimit`, `SubFace`, and the 21-field `CardDef`.
-/
