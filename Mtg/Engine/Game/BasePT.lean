import Mtg.Engine.Game.Phasing

/-!
# Characteristic-defining P/T (CR 604.3)

Layer-7a characteristic-defining abilities: power/toughness equal to
lands you control, cards in hand, creatures you control, or subtype
counts, and the base P/T they define (CR 613.3a / 208.2a).
Defined in `Mtg.Engine.Game.Core` so `matchTriggers` can evaluate P/T
and intervening-if conditions at batch close.
-/
