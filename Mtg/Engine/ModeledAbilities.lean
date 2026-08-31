/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
Authors: MTG Engine Contributors
-/

import Mtg.Engine.Color
import Mtg.Engine.Mana

/-!
# Leftover modeled ability constructors

Reusable ability shapes live on `TriggeredAbility`, `StaticAbility`,
`SpellEffect`, `AbilityEffect`, and `CardDef` so any set can use them.
Reusable leftover *trigger* wordings now live on event-family effect
inductives (`StepEffect`, `DeathEffect`, `ThisAttackEffect`,
`EnterOrAttackEffect`, `WatchEffect`, `YouAttackEffect`, `CastEffect`,
`ResourceEffect`) with one `TriggeredAbility` constructor each.
Reusable leftover *statics* now live on `StaticAbility`. Reusable leftover
*spells* now live on `SpellEffect`. Reusable leftover *activations* now
live on `AbilityEffect` and `ActivatedAbility` / `ActivationCost` fields.
Reusable leftover *Saga chapters* now live on `ChapterEffect`.
-/

namespace Mtg.Engine
/-- How leftover “add one mana of any color; spend only …” restricts the mana. -/
inductive RestrictedManaSpend where
  /-- Hero spells and Hero sources. -/
  | hero
  /-- Villain spells and Villain sources. -/
  | villain
  /-- Artifact spells. -/
  | artifactSpell
deriving Repr, Inhabited, BEq

namespace RestrictedManaSpend

/-- Official Oracle “Spend this mana only …” clause. -/
def spendClause : RestrictedManaSpend → String
  | .hero => "to cast a Hero spell or to activate an ability of a Hero source"
  | .villain => "to cast a Villain spell or to activate an ability of a Villain source"
  | .artifactSpell => "to cast an artifact spell"

end RestrictedManaSpend

#guard RestrictedManaSpend.spendClause .hero ==
  "to cast a Hero spell or to activate an ability of a Hero source"
#guard RestrictedManaSpend.spendClause .villain ==
  "to cast a Villain spell or to activate an ability of a Villain source"
#guard RestrictedManaSpend.spendClause .artifactSpell ==
  "to cast an artifact spell"

end Mtg.Engine
