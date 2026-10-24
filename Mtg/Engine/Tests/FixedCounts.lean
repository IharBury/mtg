import Mtg.Engine.Fixture

/-!
# Remaining `TriggerResolution` counts

`empowerJace`, `spellsCostLess`, `lookAtTopRevealTypes`, and `becomePT`
read a `NumberSelector`. `.fixed` is the printed number. Every other
count is read the same way. A count of zero still runs that action.
-/

namespace Mtg.Engine.FixedCountTests

open Mtg.Engine
open Mtg.Engine.Tests

def caster : PlayerId := ⟨0⟩

def bear : CardDef := {
  name := "Count Bear"
  types := #[.creature]
  power := some 2
  toughness := some 2
}

def step (g : Game) (r : TriggeredAbility.TriggerResolution)
    (sourceId : Option ObjectId := none) : Game :=
  g.applyTriggeredAbility caster (.onEnterDraw 1) sourceId
    (resolutionOverride := some r)

def bearOf (g : Game) : GameObject :=
  match g.battlefield.find? (·.name == "Count Bear") with
  | some o => o
  | none => panic! "missing Count Bear"

/- Empower Jace 2 creates a token and puts two loyalty counters.
A count of other creatures is read the same way. Zero still creates
the token and puts no loyalty. -/
#guard
  let g := step afterDraw (.empowerJace (.fixed 2))
  match g.jacePlaneswalkerTokens caster with
  | #[o] => o.status.loyaltyCounters == 2
  | _ => false

#guard
  let g := step afterDraw (.empowerJace .perOtherCreature)
  match g.jacePlaneswalkerTokens caster with
  | #[o] => o.status.loyaltyCounters == 0 && logContains g "Empower Jace 0"
  | _ => false

#guard
  let g0 := addPermanent afterDraw bear caster caster
  let g := step g0 (.empowerJace .perOtherCreature)
  match g.jacePlaneswalkerTokens caster with
  | #[o] => o.status.loyaltyCounters == 1
  | _ => false

#guard (SharedTrigger.timing (.empowerJace 2)).resolution == .empowerJace (.fixed 2)

/- Artifact spells cost {1} less. Another count is read the same way. -/
#guard
  let g := step afterDraw (.spellsCostLess (.cardType .artifact) (.fixed 1))
  (g.player caster).typeSpellCostLessThisTurn == #[(.artifact, 1)]

#guard
  let g := step afterDraw (.spellsCostLess (.supertype .legendary) (.fixed 2))
  (g.player caster).supertypeSpellCostLessThisTurn == #[(.legendary, 2)]

#guard
  let g := step afterDraw (.spellsCostLess (.cardType .artifact) .perOtherCreature)
  (g.player caster).typeSpellCostLessThisTurn == #[(.artifact, 0)]

#guard
  let g0 := addPermanent afterDraw bear caster caster
  let g := step g0 (.spellsCostLess (.cardType .artifact) .perOtherCreature)
  (g.player caster).typeSpellCostLessThisTurn == #[(.artifact, 1)]

/- Looking at the top card offers the reveal. Another count looks at that many. -/
#guard
  let g := step afterDraw (.lookAtTopRevealTypes (.fixed 1) #["Creature"])
  match g.pending with
  | .fraChoice p _ => p == caster
  | _ => false

#guard
  let g := step afterDraw (.lookAtTopRevealTypes .perOtherCreature #["Creature"])
  match g.pending with
  | .fraChoice p _ => p == caster && logContains g "looks at the top 0"
  | _ => false

#guard
  let g0 := addPermanent afterDraw bear caster caster
  let g := step g0 (.lookAtTopRevealTypes .perOtherCreature #["Creature"])
  match g.pending with
  | .fraChoice p _ => p == caster && logContains g "looks at the top 1"
  | _ => false

#guard (SharedTrigger.timing (.lookAtTopRevealTypes 4 #["Dwarf", "Equipment"])).resolution ==
  .lookAtTopRevealTypes (.fixed 4) #["Dwarf", "Equipment"]

/- The source may become 3/3. Another count is the base that is offered. -/
#guard
  let g0 := addPermanent afterDraw bear caster caster
  let g := step g0 (.becomePT (.fixed 3) (.fixed 3)) (some (bearOf g0).id)
  match g.pending with
  | .fraChoice p (.mayBecomeBasePT id 3 3) => p == caster && id == (bearOf g0).id
  | _ => false

#guard
  let g0 := addPermanent afterDraw bear caster caster
  let g := step g0 (.becomePT .perOtherCreature (.fixed 3)) (some (bearOf g0).id)
  match g.pending with
  | .fraChoice p (.mayBecomeBasePT id 0 3) => p == caster && id == (bearOf g0).id
  | _ => false

#guard
  let g0 := addPermanent (addPermanent afterDraw bear caster caster) bear caster caster
  let source :=
    match g0.battlefield.find? (·.name == "Count Bear") with
    | some o => o.id
    | none => panic! "missing Count Bear"
  let g := step g0 (.becomePT .perOtherCreature (.fixed 3)) (some source)
  match g.pending with
  | .fraChoice _ (.mayBecomeBasePT _ 1 3) => true
  | _ => false

#guard (SharedTrigger.timing (.becomePT 1 1)).resolution ==
  .becomePT (.fixed 1) (.fixed 1)

end Mtg.Engine.FixedCountTests
