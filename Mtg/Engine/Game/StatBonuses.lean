import Mtg.Engine.Game.BasePT

/-!
# Continuous stat bonuses (CR 613)

Layer-7c power/toughness additions: lords, Auras and Equipment,
enduring-story bonuses, graveyard- and artifact-count pumps, and the
P/T snapshots used for last-known values (CR 113.7a).
Defined in `Mtg.Engine.Game.Core` so `matchTriggers` can evaluate P/T
and intervening-if conditions at batch close.
-/
