import Mtg.Engine.Tests.Builders
import Mtg.Engine.Fixture

/-!
# Unified reflexive and delayed triggered abilities (`Instruction.queueReflexiveTrigger` / `createDelayedTrigger`)

Plan completion reflexives, divided damage, milled spell copy reflexives,
arbitrary unified reflexive instructions, and delayed attack pumps execute
directly through `Game/Interpreter.lean`.
-/

namespace Mtg.Engine.ReflexiveTests

open Mtg.Engine
open Mtg.Engine.Tests hiding afterDraw

def afterDraw : Game := Mtg.Engine.Tests.afterDraw.change (.pushContinuationFrame {})

def caster : PlayerId := ⟨0⟩
def opp : PlayerId := ⟨1⟩

def planCard : CardDef := {
  name := "The Plan"
  types := #[.enchantment]
}

def bolt : CardDef := {
  name := "Copied Bolt"
  types := #[.instant]
}

def planOnBoard : Game :=
  addPermanent afterDraw planCard caster caster

def planId (g : Game) : ObjectId :=
  match g.battlefield.find? (·.name == "The Plan") with
  | some o => o.id
  | none => panic! "missing The Plan"

def putInGraveyard (g : Game) (card : CardDef) (p : PlayerId) : Game :=
  insertObject g card p (.graveyard p)

def stackEffect (g : Game) : Option Effect :=
  match g.stack.back? with
  | some e => (g.findObject? e.objectId).bind (·.abilityEffect)
  | none => none

/- Delayed trigger structure on chapter attack pump. -/
#guard
  match Effect.chapterGrantAttackPumpPerPlainsThisTurn.body with
  | .installEffect (.createDelayedTrigger spec) => spec.pattern == .youAttack
  | _ => false

/- Printed phrases stay intact. -/
#guard TriggeredAbility.resolutionPhrase TriggeredAbility.onFourthPlanDividedDamage.effect ==
  "sacrifice it. When you do, it deals 7 damage divided as you choose among up to 2 targets"
#guard TriggeredAbility.resolutionPhrase TriggeredAbility.onCastSecondSpellMillThenCopy.effect ==
  "each opponent mills two cards. When one or more cards are milled this way, exile target enchantment, instant, or sorcery card with equal or lesser mana value than that spell from an opponent's graveyard. Copy the exiled card. You may cast the copy without paying its mana cost"

/- Sacrificing the Plan queues its unified reflexive ability on the stack. -/
#guard
  let g0 := planOnBoard
  let sid := planId g0
  let g := g0.applyTriggeredAbility caster .onFourthPlanReturnInstants (some sid)
  let queued :=
    match stackEffect g with
    | some eff =>
      eff.targets == .single {
          domain := .object .yourGraveyard (.any #[.hasType .instant, .hasType .sorcery])
          count := .upTo 2
        } &&
        eff.toNotation.contains "from your graveyard"
    | none => false
  queued && !(g.battlefield.any (·.id == sid)) &&
    logContains g "reflexive"

/- A Plan that has already left the battlefield queues nothing. -/
#guard
  let g0 := planOnBoard
  let sid := planId g0
  let (gGone, _) := g0.move sid (.graveyard caster) none
  let g := gGone.applyTriggeredAbility caster .onFourthPlanIndestructible (some sid)
  g.stack.isEmpty

/- Divided damage plan reflexive carries `dividedDamage? == some (7, 2)` and its canonical text. -/
#guard
  let g0 := planOnBoard
  let sid := planId g0
  let g := g0.applyTriggeredAbility caster .onFourthPlanDividedDamage (some sid)
  match stackEffect g with
  | some eff =>
    eff.dividedDamage? == some (7, 2) &&
      eff.toNotation.contains "7 damage divided as you choose among one or two targets"
  | none => false

/- A milled instant in the opponent's graveyard becomes a legal target for the
mill-and-copy reflexive; with no legal card in graveyard, the reflexive is removed. -/
#guard
  let g0 := insertObject (emptyLibrary afterDraw opp) bolt opp (.library opp)
  let g := g0.applyTriggeredAbility caster .onCastSecondSpellMillThenCopy none
  !g.stack.isEmpty || g.pending != .none

#guard
  let g0 := emptyLibrary afterDraw opp
  let g := g0.applyTriggeredAbility caster .onCastSecondSpellMillThenCopy none
  g.stack.isEmpty

/- An arbitrary unified reflexive instruction is put on the stack and resolves cleanly. -/
#guard
  let g0 := afterDraw
  let hand := (g0.player caster).hand.size
  let reflAb : TriggeredAbility := TriggeredAbility.mkTrigger .thisEnters { body := Instruction.drawFixed 1 }
  let outerAb : TriggeredAbility := TriggeredAbility.mkTrigger .thisEnters { body := .queueReflexiveTrigger reflAb }
  let g := g0.applyTriggeredAbility caster outerAb none
  let resolved := passBoth g
  g.stack.size == g0.stack.size + 1 &&
    (resolved.player caster).hand.size == hand + 1

/- Each resolution of the chapter attack-pump installs one delayed attack trigger. -/
#guard
  let ab := TriggeredAbility.sagaChapter 1 Effect.chapterGrantAttackPumpPerPlainsThisTurn
  let g := afterDraw.applyTriggeredAbility caster ab none
  let again := g.applyTriggeredAbility caster ab none
  (g.delayedTriggers.filter (fun dt => dt.controller == caster && dt.kind == .attackPumpPerPlains)).size == 1 &&
    (again.delayedTriggers.filter (fun dt => dt.controller == caster && dt.kind == .attackPumpPerPlains)).size == 2

end Mtg.Engine.ReflexiveTests
