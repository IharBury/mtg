import Mtg.Engine.Fixture

/-!
# Remaining `TriggerResolution` counts

`empowerJace`, `spellsCostLess`, `lookAtTopRevealTypes`, and `becomePT`
read a `NumberSelector`. `.fixed` is the printed number. Any other
selector does nothing.
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
Any other selector empowers nothing. -/
#guard
  let g := step afterDraw (.empowerJace (.fixed 2))
  match g.jacePlaneswalkerTokens caster with
  | #[o] => o.status.loyaltyCounters == 2
  | _ => false

#guard
  let g := step afterDraw (.empowerJace .perOtherCreature)
  (g.jacePlaneswalkerTokens caster).isEmpty && g.log.size == afterDraw.log.size

#guard (SharedTrigger.timing (.empowerJace 2)).resolution == .empowerJace (.fixed 2)

/- Artifact spells cost {1} less. Any other amount changes nothing. -/
#guard
  let g := step afterDraw (.spellsCostLess (.cardType .artifact) (.fixed 1))
  (g.player caster).typeSpellCostLessThisTurn == #[(.artifact, 1)]

#guard
  let g := step afterDraw (.spellsCostLess (.supertype .legendary) (.fixed 2))
  (g.player caster).supertypeSpellCostLessThisTurn == #[(.legendary, 2)]

#guard
  let g := step afterDraw (.spellsCostLess (.cardType .artifact) .perOtherCreature)
  (g.player caster).typeSpellCostLessThisTurn.isEmpty &&
    g.log.size == afterDraw.log.size

/- Looking at the top card offers the reveal. Any other amount does not. -/
#guard
  let g := step afterDraw (.lookAtTopRevealTypes (.fixed 1) #["Creature"])
  match g.pending with
  | .fraChoice p _ => p == caster
  | _ => false

#guard
  let g := step afterDraw (.lookAtTopRevealTypes .perOtherCreature #["Creature"])
  g.pending == afterDraw.pending && g.log.size == afterDraw.log.size

#guard (SharedTrigger.timing (.lookAtTopRevealTypes 4 #["Dwarf", "Equipment"])).resolution ==
  .lookAtTopRevealTypes (.fixed 4) #["Dwarf", "Equipment"]

/- The source may become 3/3. Any other selector changes nothing. -/
#guard
  let g0 := addPermanent afterDraw bear caster caster
  let g := step g0 (.becomePT (.fixed 3) (.fixed 3)) (some (bearOf g0).id)
  match g.pending with
  | .fraChoice p (.mayBecomeBasePT id 3 3) => p == caster && id == (bearOf g0).id
  | _ => false

#guard
  let g0 := addPermanent afterDraw bear caster caster
  let g := step g0 (.becomePT .perOtherCreature (.fixed 3)) (some (bearOf g0).id)
  g.pending == g0.pending && g.log.size == g0.log.size

#guard (SharedTrigger.timing (.becomePT 1 1)).resolution ==
  .becomePT (.fixed 1) (.fixed 1)

end Mtg.Engine.FixedCountTests
