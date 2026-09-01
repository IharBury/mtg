/-!
# Activated-ability classification

How the demonstration agent classifies an activated-ability mode.
-/

namespace Mtg.Engine

/-- How the demonstration agent classifies an activated-ability mode. -/
inductive AbilityCastKind where
  /-- Damage to a creature. -/
  | creatureDamage
  /-- Destroy a colorless nonland permanent. -/
  | destroyColorless
  /-- Any other mode. -/
  | other
deriving Repr, Inhabited, BEq, DecidableEq

end Mtg.Engine
