import Mtg.Engine.Game.StatBonuses

/-!
# Current keywords (CR 613.1f)

Which keyword abilities an object currently has: printed, granted until
end of turn, granted by attachments or leftover text, or lost with lose-
abilities effects — haste, flying, menace, hexproof, indestructible,
trample, and the attack and block permission checks built on them
(CR 509.1b).
Defined in `Mtg.Engine.Game.Core` so `matchTriggers` can evaluate
keywords and intervening-if conditions at batch close.
-/
