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
import Mtg.Engine.Card.PermanentAction
import Mtg.Engine.Card.SpellResolution
import Mtg.Engine.Card.AbilityResolution
import Mtg.Engine.Card.Chapter
import Mtg.Engine.Card.SharedTrigger
import Mtg.Engine.Card.Effect
import Mtg.Engine.Card.ActivatedAbility
import Mtg.Engine.Card.TriggerPattern
import Mtg.Engine.Card.Trigger
import Mtg.Engine.Card.ChapterEffects
import Mtg.Engine.Card.TriggerEffects
import Mtg.Engine.Card.SpellEffects
import Mtg.Engine.Card.TriggeredAbility
import Mtg.Engine.Card.StaticAbility
import Mtg.Engine.Card.KeywordExpand
import Mtg.Engine.Card.CardDef
import Mtg.Engine.Card.Parser.SubGrammars
import Mtg.Engine.Card.ParseOracle
import Mtg.Engine.Card.Guards

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
- `Parser.SubGrammars`: Stage-4 compositional expression, target, cost,
  keyword, static-ability, and trigger-clause parsers.
- `PermanentAction`: shared actions on permanents (CR 608.2b).
- `SpellResolution` / `AbilityCastKind` / `Chapter`: how spells resolve,
  how the demo agent classifies activated abilities, and Saga chapter
  resolutions (CR 608 / 714.2).
- `SharedTrigger`: reusable trigger payloads (CR 603).
- `Effect`: the unified one-shot `Effect` and `Resolution` vocabulary
  (activated-ability leftovers live on `Resolution`).
- `ActivatedAbility` / `StaticAbility`: printed abilities (CR 602 / 604).
- `TriggerPattern` / `Trigger`: unified trigger event patterns, batch
  groupings, turn limits, CR 603.10a–f look-back, CR 605.1b triggered mana
  ability classification, and Saga chapter triggers (CR 603 / 714.2).
- `ChapterEffects` / `TriggerEffects` / `SpellEffects`: named `Effect`
  constructors per family.
- `TriggeredAbility`: printed triggered abilities (CR 603 / 714.2).
- `KeywordExpand`: pure CR 702.1 `KeywordAbility.expand` lowering keywords into
  static/triggered/activated/additional/alternative/special-action/spell rules.
- `CardDef`: the printed card definition and `AdventureFace`.
- `Guards`: cross-abstraction `#guard` regression tests.
-/
