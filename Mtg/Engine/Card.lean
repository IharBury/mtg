import Mtg.Engine.Card.Keywords
import Mtg.Engine.Card.Text
import Mtg.Engine.Card.Counter
import Mtg.Engine.Card.Token
import Mtg.Engine.Card.Targeting
import Mtg.Engine.Card.SpellResolution
import Mtg.Engine.Card.Effect
import Mtg.Engine.Card.ActivatedAbility
import Mtg.Engine.Card.StaticAbility
import Mtg.Engine.Card.TriggerEvent
import Mtg.Engine.Card.Trigger
import Mtg.Engine.Card.TriggerEffects
import Mtg.Engine.Card.SpellEffects
import Mtg.Engine.Card.TriggeredAbility
import Mtg.Engine.Card.Saga
import Mtg.Engine.Card.CardDef
import Mtg.Engine.Card.ParseOracle
import Mtg.Engine.Card.Guards

/-!
# Card characteristics (CR 108, 109.3, section 2)

A card’s Oracle characteristics: name, mana cost, color, type line, rules
text, and (when applicable) power, toughness, keywords, and the static,
triggered, activated, and spell abilities we currently model.

This module re-exports the `Mtg.Engine.Card.*` files, one per abstraction:

- `Keywords`: keyword abilities (CR 702).
- `Text`: shared Oracle-text phrase helpers.
- `Counter`: counter kinds a permanent can carry (CR 122).
- `Token`: token kinds (CR 111).
- `Targeting`: targeting shapes and `HasTargeting` (CR 115.1).
- `SpellResolution`: unified `Resolution`, selector vocabulary, and `PermanentAction` (CR 608).
- `Effect`: the unified one-shot `Effect` carrier (CR 608).
- `ActivatedAbility` / `StaticAbility`: printed abilities (CR 602 / 604).
- `TriggerEvent` / `Trigger`: trigger events, timing, intervening conditions, and `SharedTrigger` builders (CR 603).
- `TriggerEffects` / `SpellEffects`: named `Effect` constructors per family.
- `TriggeredAbility`: printed triggered abilities (CR 603).
- `Saga`: printed Sagas and `Effect.chapter*` constructors (CR 714).
- `CardDef`: the printed card definition and `AdventureFace`.
- `Guards`: cross-abstraction `#guard` regression tests.
-/
