import Mtg.Engine.Fixture

/-!
# Dynamic `ValueExpr` counts across unified instructions

`empowerPlaneswalker`, `costMod`, `inspectLibrary`, and `setBasePT`
all read unified `ValueExpr` counts. `.const` is a printed number, and
dynamic counts (such as other creatures you control) evaluate the same way.
-/

namespace Mtg.Engine.FixedCountTests

open Mtg.Engine
open Mtg.Engine.Tests

def caster : PlayerId := ⟨0⟩

def bear : CardDef := {
  name := "Count Bear"
  types := #[.creature]
  power := some (.fixed 2)
  toughness := some (.fixed 2)
}

def otherCreaturesExpr : ValueExpr :=
  ValueExpr.count (.inZones .battlefield (.all #[.otherThan .this, .hasType .creature, .controlledBy .you]))

def step (g : Game) (body : Instruction)
    (sourceId : Option ObjectId := none) : Game :=
  g.applyTriggeredAbility caster (TriggeredAbility.mkTrigger .thisEnters { body }) sourceId

def bearOf (g : Game) : GameObject :=
  match g.battlefield.find? (·.name == "Count Bear") with
  | some o => o
  | none => panic! "missing Count Bear"

/- Empower Jace 2 creates a token and puts two loyalty counters.
A dynamic count of other creatures is read the same way. Zero still creates
the token and puts no loyalty. -/
#guard
  let g := step afterDraw (Instruction.empowerJace 2)
  match g.jacePlaneswalkerTokens caster with
  | #[o] => o.status.loyaltyCounters == 2
  | _ => false

#guard
  let g := step afterDraw (.player (.empowerPlaneswalker .jace otherCreaturesExpr))
  match g.jacePlaneswalkerTokens caster with
  | #[o] => o.status.loyaltyCounters == 0 && logContains g "Empower Jace 0"
  | _ => false

#guard
  let g0 := addPermanent afterDraw bear caster caster
  let g := step g0 (.player (.empowerPlaneswalker .jace otherCreaturesExpr))
  match g.jacePlaneswalkerTokens caster with
  | #[o] => o.status.loyaltyCounters == 1
  | _ => false

#guard (Effect.triggerEmpowerJace 2).body == Instruction.empowerJace 2

/- Artifact and legendary spells cost less by a fixed or dynamic `ValueExpr`. -/
#guard
  let g := step afterDraw (.installEffect (.applyRuleMod .untilEndOfTurn
    (.costMod (.spells .you (.hasType .artifact)) (.reduceGeneric (.const 1)))))
  g.typeSpellCostLessThisTurn caster == #[(.artifact, 1)]

#guard
  let g := step afterDraw (.installEffect (.applyRuleMod .untilEndOfTurn
    (.costMod (.spells .you (.hasSupertype .legendary)) (.reduceGeneric (.const 2)))))
  g.supertypeSpellCostLessThisTurn caster == #[(.legendary, 2)]

#guard
  let g := step afterDraw (.installEffect (.applyRuleMod .untilEndOfTurn
    (.costMod (.spells .you (.hasType .artifact)) (.reduceGeneric otherCreaturesExpr))))
  g.typeSpellCostLessThisTurn caster == #[(.artifact, 0)]

#guard
  let g0 := addPermanent afterDraw bear caster caster
  let g := step g0 (.installEffect (.applyRuleMod .untilEndOfTurn
    (.costMod (.spells .you (.hasType .artifact)) (.reduceGeneric otherCreaturesExpr))))
  g.typeSpellCostLessThisTurn caster == #[(.artifact, 1)]

/- Looking at the top cards with fixed or dynamic `ValueExpr` count. -/
def lookTopCreatures (n : ValueExpr) : Instruction :=
  .player (.inspectLibrary {
    source := .topCards .you n false
    action := .takeMatching (.hasType .creature) (.upTo (.const 1)) (.hand .controller) false true false
    rest := .bottomRandom
  })

#guard
  let g := step afterDraw (lookTopCreatures (.const 1))
  match g.pending with
  | .fraChoice p _ => p == caster
  | _ => false

#guard
  let g0 := addPermanent afterDraw bear caster caster
  let g := step g0 (lookTopCreatures otherCreaturesExpr)
  match g.pending with
  | .fraChoice p _ => p == caster && logContains g "looks at the top 1"
  | _ => false

#guard TriggeredAbility.toNotation (.onEnterLookAtTopRevealTypes 4 #["Dwarf", "Equipment"]) ==
  "When this permanent enters, look at the top 4 cards of your library. You may reveal a Dwarf or Equipment card from among them and put it into your hand. Put the rest on the bottom of your library in a random order."

/- Optional base P/T change (`triggerBecomePT`) reads fixed and dynamic `ValueExpr`s. -/
#guard
  let g0 := addPermanent afterDraw bear caster caster
  let g := step g0 (Effect.triggerBecomePT 3 3).body (some (bearOf g0).id)
  let accepted := mustApply g caster .accept
  let declined := mustApply g caster .decline
  g.pending != .none &&
    accepted.power (bearOf accepted) == 3 && accepted.toughness (bearOf accepted) == 3 &&
    declined.power (bearOf declined) == 2 && declined.toughness (bearOf declined) == 2

#guard
  let g0 := addPermanent (addPermanent afterDraw bear caster caster) bear caster caster
  let source := (g0.battlefield.find? (·.name == "Count Bear")).get!.id
  let dynPT : Instruction := Instruction.may .you none
    (.installEffect (.applyContinuous .untilEndOfTurn .this
      (.setBasePT (some otherCreaturesExpr) (some (.const 3)))))
  let g := mustApply (step g0 dynPT (some source)) caster .accept
  g.power (g.object! source) == 1 && g.toughness (g.object! source) == 3

end Mtg.Engine.FixedCountTests
