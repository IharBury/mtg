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
Leftover Saga chapters remain here on `ModeledChapter`.
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

/-- A leftover modeled Saga chapter that is not yet a shared shape. -/
inductive ModeledChapter where
  /-- Modeled MSH ability. -/
  | gainControlOfUpToTwoTargetCreaturesWith
  /-- Modeled MSH ability. -/
  | harnessTheMindStone
  /-- Modeled MSH ability. -/
  | thisSagaDeals2DamageToEachNonVillainCre
  /-- Modeled MSH ability. -/
  | thisSagaDealsXDamageToTargetOpponentWhe
deriving Repr, Inhabited, BEq

namespace ModeledChapter

/-- Official Oracle wording for this ModeledChapter. -/
def toNotation : ModeledChapter → String
  | .gainControlOfUpToTwoTargetCreaturesWith => "Gain control of up to two target creatures with total mana value 6 or less for as long as this Saga remains on the battlefield"
  | .harnessTheMindStone => "Harness The Mind Stone"
  | .thisSagaDeals2DamageToEachNonVillainCre => "This Saga deals 2 damage to each non-Villain creature and each opponent"
  | .thisSagaDealsXDamageToTargetOpponentWhe => "This Saga deals X damage to target opponent, where X is the greatest mana value among artifacts you control"

instance : ToString ModeledChapter where
  toString := toNotation

end ModeledChapter
end Mtg.Engine
