import Mtg.Engine.Card.Definition.Selector
import Mtg.Engine.Card.Definition.Cost
import Mtg.Engine.Card.Definition.Parts
import Mtg.Engine.Card.Definition.Continuous
import Mtg.Engine.Card.Definition.ActionLeftovers
import Mtg.Engine.Card.Definition.TokenLeftovers
import Mtg.Engine.Card.Definition.CompiledLeftovers
import Mtg.Engine.Card.Definition.Compile
import Mtg.Engine.Card.Definition.Ability
import Mtg.Engine.Card.Definition.CardFace
import Mtg.Engine.Card.Definition.Guards
import Mtg.Engine.Card.Definition.GuardsCatalog
import Mtg.Engine.Card.Definition.GuardsTrigger
import Mtg.Engine.Card.Definition.GuardsSaga

/-!
# Traditional card definitions

A printed card as a list of `CardPart`s: name, mana cost, type line,
abilities, and (for adventurer cards) an `alternative` face. Compiles to
`CardDef` so the engine and existing catalogs stay unchanged.

The compiler is split under `Definition/`:

- `Selector` flattens a `Selector` into a `Shape` and reads targeting.
- `Cost` is a payment in an activated ability or an additional cost.
- `Parts` is `Condition`, `CardState`, and the mutually inductive
  `Ability`, `ContinuousEffect`, `CardAction`, and `CardPart`, plus
  predefined Treasure and Food tokens.
- `Continuous` projects a `ContinuousEffect` and compiles a continuous
  action, a tap, an untap, or damage.
- `ActionLeftovers` recognizes one printed action: pumps, draws, counters,
  mana, enters replacements, searches, and exile.
- `TokenLeftovers` recovers a `TokenKind` and recognizes token creation,
  enters-the-battlefield actions, and mill-then-put.
- `CompiledLeftovers` recognizes actions that already name an `Effect`
  or a `TriggeredAbility`.
- `Compile` is `CardAction.compile`, `toEffect`, and `toAbilityEffect`.
- `Ability` compiles activated and triggered abilities.
- `CardFace` accumulates one face and `toCardDef` compiles it to `CardDef`.
- `Guards`, `GuardsCatalog`, `GuardsTrigger`, and `GuardsSaga` are the
  `#guard` regression tests, in that order. Add a new guard at the end
  of `GuardsSaga`.

Remaining supported catalog cards that are not yet in this syntax, and
the constructors they need, are listed in `TraditionalSyntaxGaps.md`.
-/
