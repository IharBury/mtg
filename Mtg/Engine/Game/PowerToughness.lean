import Mtg.Engine.Game.Keywords

/-!
# Current power and toughness (CR 613.4)

Final power and toughness after characteristic-defining abilities,
layer-7b base setting, lord and attachment bonuses, counters, and pumps,
plus greatest-power queries and blocker lookups.
Defined in `Mtg.Engine.Game.Core` so `matchTriggers` can evaluate P/T
and intervening-if conditions at batch close.
-/
