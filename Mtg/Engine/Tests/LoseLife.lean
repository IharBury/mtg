import Mtg.Engine.Catalog
import Mtg.Engine.Fixture

/-!
# Unified life loss instructions (`Instruction.loseLife`)

How much life is lost is a `ValueExpr`; who loses it is a `PlayerExpr`.
You lose `n` life, target opponent, each opponent, one life per burden
counter on the source, and controller-of-objects selectors all evaluate
through `EvalExpr` and `Interpreter`.
-/

namespace Mtg.Engine.LoseLifeTests

open Mtg.Engine
open Mtg.Engine.Catalog
open Mtg.Engine.Tests hiding afterDraw

def afterDraw : Game := Mtg.Engine.Tests.afterDraw.change (.pushContinuationFrame {})

def caster : PlayerId := ⟨0⟩
def opp : PlayerId := ⟨1⟩

def lifeOf (g : Game) (p : PlayerId) : Int :=
  (g.player p).life

def step (g : Game) (body : Instruction)
    (sourceId : Option ObjectId := none) (targets : Array Target := #[])
    (spec : TargetSpec := .none) : Game :=
  g.applyTriggeredAbility caster
    (TriggeredAbility.mkTrigger .thisEnters { targeting := .of spec, body })
    sourceId targets

def obj (g : Game) (name : String) : GameObject :=
  match g.battlefield.find? (·.name == name) with
  | some o => o
  | none => panic! s!"missing {name}"

def anyObj (g : Game) (name : String) : GameObject :=
  match g.objects.find? (·.name == name) with
  | some o => o
  | none => panic! s!"missing {name}"

def pid (g : Game) (name : String) : ObjectId :=
  (obj g name).id

def handSize (g : Game) (p : PlayerId) : Nat :=
  (g.player p).hand.size

def ring : CardDef := artifact "Ring" ManaCost.empty ""

def perBurden : Instruction :=
  Instruction.loseLife (.counterCount (some .burden) .this) .you

def targetOpp (n : Nat) : Instruction :=
  Instruction.loseLifeFixed n (.target 0)

def eachOpp (n : Nat) : Instruction :=
  Instruction.loseLifeFixed n .opponents

/- The controller loses the printed amount. Losing none changes nothing. -/
#guard
  let g := step afterDraw (Instruction.loseLifeFixed 4 .you)
  lifeOf g caster == lifeOf afterDraw caster - 4 &&
    lifeOf g opp == lifeOf afterDraw opp &&
    logContains g "loses 4 life"

#guard
  let g := step afterDraw (Instruction.loseLifeFixed 0 .you)
  lifeOf g caster == lifeOf afterDraw caster && g.log == afterDraw.log

/- The announced opponent loses the printed amount. The controller does not.
A missing target, the controller, and a permanent lose nothing. -/
#guard
  let g0 := afterDraw
  let g := step g0 (targetOpp 3) (targets := #[Target.player opp]) (spec := .opponent)
  lifeOf g opp == lifeOf g0 opp - 3 && lifeOf g caster == lifeOf g0 caster &&
    logContains g "loses 3 life"

#guard
  let g := step afterDraw (targetOpp 3) (spec := .opponent)
  lifeOf g opp == lifeOf afterDraw opp && lifeOf g caster == lifeOf afterDraw caster

#guard
  let g := step afterDraw (targetOpp 3) (targets := #[Target.player caster]) (spec := .opponent)
  lifeOf g caster == lifeOf afterDraw caster && lifeOf g opp == lifeOf afterDraw opp

#guard
  let g0 := addPermanent afterDraw (creature "Bear" ManaCost.empty #[] 2 2) opp opp
  let g := step g0 (targetOpp 3) (targets := #[Target.permanent (pid g0 "Bear")]) (spec := .opponent)
  lifeOf g opp == lifeOf g0 opp && lifeOf g caster == lifeOf g0 caster

#guard
  let g0 := afterDraw
  let g := g0.applyTriggeredAbility caster .onYouSacrificeTokenOppLosesLife none
    #[Target.player opp]
  lifeOf g opp == lifeOf g0 opp - 1 && lifeOf g caster == lifeOf g0 caster

/- Each opponent loses the printed amount. The controller does not.
Losing none changes nothing. -/
#guard
  let g := step afterDraw (eachOpp 2)
  lifeOf g opp == lifeOf afterDraw opp - 2 &&
    lifeOf g caster == lifeOf afterDraw caster &&
    logContains g "loses 2 life"

#guard
  let g := step afterDraw (eachOpp 0)
  lifeOf g opp == lifeOf afterDraw opp && g.log == afterDraw.log

/- One life for each burden counter on the found source. -/
#guard
  let g0 := addPermanent afterDraw ring caster caster
  let g0 := g0.addBurdenCounter (obj g0 "Ring") 4
  let g := step g0 perBurden (some (pid g0 "Ring"))
  lifeOf g caster == lifeOf g0 caster - 4 && lifeOf g opp == lifeOf g0 opp &&
    logContains g "loses 4 life"

#guard
  let g0 := addPermanent afterDraw ring caster caster
  let g := step g0 perBurden (some (pid g0 "Ring"))
  lifeOf g caster == lifeOf g0 caster && g.log == g0.log

#guard
  let g := step afterDraw perBurden
  lifeOf g caster == lifeOf afterDraw caster && g.log == afterDraw.log

#guard
  let g0 := addPermanent afterDraw ring caster caster
  let g0 := g0.addBurdenCounter (obj g0 "Ring") 3
  let g := g0.applyTriggeredAbility caster .onYourUpkeepLoseLifePerBurden
    (some (pid g0 "Ring"))
  lifeOf g caster == lifeOf g0 caster - 3 && (obj g "Ring").status.burden == 3

/- Drain and draw-and-lose still run alongside the plan counter. -/
#guard
  let g0 := addPermanent afterDraw ring caster caster
  let g := g0.applyTriggeredAbility caster (.onVillainYouControlEntersDrainAndPlan 2)
    (some (pid g0 "Ring"))
  lifeOf g opp == lifeOf g0 opp - 2 && lifeOf g caster == lifeOf g0 caster + 2 &&
    (obj g "Ring").status.plan == 1

#guard
  let g0 := addPermanent afterDraw ring caster caster
  let before := handSize g0 caster
  let g := g0.applyTriggeredAbility caster .onCreatureCardsToGyDrawLoseLifeAndPlan
    (some (pid g0 "Ring"))
  handSize g caster == before + 1 && lifeOf g caster == lifeOf g0 caster - 1 &&
    lifeOf g opp == lifeOf g0 opp && (obj g "Ring").status.plan == 1

/- Burden life loss uses the same count for every player expression. -/
#guard
  let g0 := addPermanent afterDraw ring caster caster
  let g0 := g0.addBurdenCounter (obj g0 "Ring") 5
  let crossed := step g0 (Instruction.loseLife (.counterCount (some .burden) .this) .opponents)
    (some (pid g0 "Ring"))
  let swapped := step g0 (Instruction.loseLife (.counterCount (some .burden) .this) (.target 0))
    (some (pid g0 "Ring")) (targets := #[Target.player opp]) (spec := .opponent)
  lifeOf crossed caster == lifeOf g0 caster && lifeOf crossed opp == lifeOf g0 opp - 5 &&
    lifeOf swapped caster == lifeOf g0 caster && lifeOf swapped opp == lifeOf g0 opp - 5

/- `PlayerExpr.controllerOf` resolves controllers of objects without duplicates. -/
#guard
  let g0 := addPermanent afterDraw (creature "Ogre" ManaCost.empty #[] 2 2) opp opp
  let g := step g0 (Instruction.loseLifeFixed 1 (.controllerOf .this)) (some (pid g0 "Ogre"))
  lifeOf g opp == lifeOf g0 opp - 1 && lifeOf g caster == lifeOf g0 caster

#guard
  let g0 := addPermanent afterDraw (creature "Mine" ManaCost.empty #[] 1 1) caster caster
  let g0 := addPermanent g0 (creature "Also" ManaCost.empty #[] 1 1) caster caster
  let g := step g0 (Instruction.loseLifeFixed 1
    (.controllerOf (.inZones .battlefield (.all #[.hasType .creature, .controlledBy .you]))))
  lifeOf g caster == lifeOf g0 caster - 1 && lifeOf g opp == lifeOf g0 opp

#guard
  let g0 := addPermanent afterDraw (creature "Mine" ManaCost.empty #[] 1 1) caster caster
  let g0 := addPermanent g0 (creature "Ogre" ManaCost.empty #[] 2 2) opp opp
  let g := step g0 (Instruction.loseLifeFixed 1
    (.controllerOf (.inZones .battlefield (.all #[.hasType .creature, .not (.hasSubtype (.literal .dragon))]))))
  lifeOf g caster == lifeOf g0 caster - 1 && lifeOf g opp == lifeOf g0 opp - 1

/- Printed notations stay intact. -/
#guard TriggeredAbility.toNotation .onYouSacrificeTokenOppLosesLife ==
  "Whenever you sacrifice a token, target opponent loses 1 life."
#guard TriggeredAbility.toNotation .onYourUpkeepLoseLifePerBurden ==
  "At the beginning of your upkeep, you lose 1 life for each burden counter on The One Ring."
#guard TriggeredAbility.resolutionPhrase (Effect.triggerDrainAndPlan 2) ==
  "each opponent loses 2 life and you gain 2 life. Put a plan counter on this enchantment"
#guard TriggeredAbility.resolutionPhrase Effect.triggerDrawLoseLifeAndPlan ==
  "you draw a card, lose 1 life, and put a plan counter on this enchantment"

end Mtg.Engine.LoseLifeTests
