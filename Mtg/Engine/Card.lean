import Mtg.Engine.Card.Keywords
import Mtg.Engine.Card.Text
import Mtg.Engine.Card.Token
import Mtg.Engine.Card.Targeting
import Mtg.Engine.Card.PermanentAction
import Mtg.Engine.Card.SpellResolution
import Mtg.Engine.Card.AbilityResolution
import Mtg.Engine.Card.Chapter
import Mtg.Engine.Card.SharedTrigger
import Mtg.Engine.Card.Effect
import Mtg.Engine.Card.ActivatedAbility
import Mtg.Engine.Card.StaticAbility
import Mtg.Engine.Card.TriggerEvent
import Mtg.Engine.Card.Trigger
import Mtg.Engine.Card.ChapterEffects
import Mtg.Engine.Card.TriggerEffects
import Mtg.Engine.Card.SpellEffects
import Mtg.Engine.Card.TriggeredAbility
import Mtg.Engine.Card.Saga
import Mtg.Engine.Card.CardDef
import Mtg.Engine.Card.Guards

/-!
# Card characteristics (CR 108, 109.3, section 2)

A card’s Oracle characteristics: name, mana cost, color, type line, rules
text, and (when applicable) power, toughness, keywords, and the static,
triggered, activated, and spell abilities we currently model.

This module re-exports the `Mtg.Engine.Card.*` files, one per abstraction:

- `Keywords`: keyword abilities (CR 702).
- `Text`: shared Oracle-text phrase helpers.
- `Token`: token kinds (CR 111).
- `Targeting`: targeting shapes and `HasTargeting` (CR 115.1).
- `PermanentAction`: shared actions on permanents (CR 608.2b).
- `SpellResolution` / `AbilityResolution` / `Chapter`: how spells,
  activated abilities, and Saga chapters resolve (CR 608 / 714.3).
- `SharedTrigger`: reusable trigger payloads (CR 603).
- `Effect`: the unified one-shot `Effect` and `Resolution` vocabulary.
- `ActivatedAbility` / `StaticAbility`: printed abilities (CR 602 / 604).
- `TriggerEvent` / `Trigger`: trigger events, timing, and resolutions.
- `ChapterEffects` / `TriggerEffects` / `SpellEffects`: named `Effect`
  constructors per family.
- `TriggeredAbility`: printed triggered abilities (CR 603).
- `Saga`: printed Sagas (CR 714).
- `CardDef`: the printed card definition and `AdventureFace`.
- `Guards`: cross-abstraction `#guard` regression tests.
-/
