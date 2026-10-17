import Mtg.Engine.Catalog
import Mtg.Engine.Fixture

/-!
# `TriggerResolution.loseLife`

How much life is lost is a `NumberSelector`. Who loses it is a
`PlayerSelector`. You lose `n` life is `.loseLife (.fixed n)`. The announced
opponent and each opponent use those players. One life for each burden
counter is `.loseLife .perBurden`. Any other selector loses nothing.
-/

namespace Mtg.Engine.LoseLifeTests

open Mtg.Engine
open Mtg.Engine.Catalog
open Mtg.Engine.Tests

def caster : PlayerId := ⟨0⟩
def opp : PlayerId := ⟨1⟩

def lifeOf (g : Game) (p : PlayerId) : Int :=
  (g.player p).life

def step (g : Game) (r : TriggeredAbility.TriggerResolution)
    (sourceId : Option ObjectId := none) (targets : Array Target := #[])
    (ab : TriggeredAbility := .onEnterDraw 1) : Game :=
  g.applyTriggeredAbility caster ab sourceId targets
    (resolutionOverride := some r)

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

def perBurden : TriggeredAbility.TriggerResolution :=
  .loseLife .perBurden

def targetOpp (n : Nat) : TriggeredAbility.TriggerResolution :=
  .loseLife (.fixed n) .targetOpponent

def eachOpp (n : Nat) : TriggeredAbility.TriggerResolution :=
  .loseLife (.fixed n) .eachOpponent

/- The controller loses the printed amount. Losing none changes nothing. -/
#guard
  let g := step afterDraw (.loseLife (.fixed 4))
  lifeOf g caster == lifeOf afterDraw caster - 4 &&
    lifeOf g opp == lifeOf afterDraw opp &&
    logContains g "loses 4 life"

#guard
  let g := step afterDraw (.loseLife (.fixed 0))
  lifeOf g caster == lifeOf afterDraw caster && g.log == afterDraw.log

#guard (.loseLife (.fixed 2) : TriggeredAbility.TriggerResolution) ==
  .loseLife (.fixed 2) .you

/- The announced opponent loses the printed amount. The controller does not.
A missing target, the controller, and a permanent lose nothing. -/
#guard
  let g0 := afterDraw
  let g := step g0 (targetOpp 3) (targets := #[Target.player opp])
    (ab := .onYouSacrificeTokenOppLosesLife)
  lifeOf g opp == lifeOf g0 opp - 3 && lifeOf g caster == lifeOf g0 caster &&
    logContains g "loses 3 life"

#guard
  let g := step afterDraw (targetOpp 3) (ab := .onYouSacrificeTokenOppLosesLife)
  lifeOf g opp == lifeOf afterDraw opp && lifeOf g caster == lifeOf afterDraw caster &&
    logContains g "The target is no longer legal"

#guard
  let g := step afterDraw (targetOpp 3) (targets := #[Target.player caster])
    (ab := .onYouSacrificeTokenOppLosesLife)
  lifeOf g caster == lifeOf afterDraw caster && lifeOf g opp == lifeOf afterDraw opp &&
    logContains g "The target is no longer legal"

#guard
  let g0 := addPermanent afterDraw (creature "Bear" ManaCost.empty #[] 2 2) opp opp
  let g := step g0 (targetOpp 3) (targets := #[Target.permanent (pid g0 "Bear")])
    (ab := .onYouSacrificeTokenOppLosesLife)
  lifeOf g opp == lifeOf g0 opp && lifeOf g caster == lifeOf g0 caster &&
    logContains g "The target is no longer legal"

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

/- One life for each burden counter on the found source. None, a missing
source, and a source that has left lose nothing. Counters do not travel
with the object, so the graveyard copy loses nothing unless it still has
burden counters. -/
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
  let g0 := g0.addBurdenCounter (obj g0 "Ring") 2
  let (g1, _) := g0.move (pid g0 "Ring") (.graveyard caster) none
  let g := step g1 perBurden (some (pid g0 "Ring"))
  lifeOf g caster == lifeOf g1 caster && g.log == g1.log

#guard
  let g0 := addPermanent afterDraw ring caster caster
  let g0 := g0.addBurdenCounter (obj g0 "Ring") 2
  let (g1, newId) := g0.move (pid g0 "Ring") (.graveyard caster) none
  let g := step g1 perBurden (some newId)
  lifeOf g caster == lifeOf g1 caster && (anyObj g "Ring").status.burden == 0 &&
    g.log == g1.log

#guard
  let g0 := addPermanent afterDraw ring caster caster
  let (g1, newId) := g0.move (pid g0 "Ring") (.graveyard caster) none
  let g1 := g1.mapObjectStatus (anyObj g1 "Ring") (fun s => { s with burden := 2 })
  let g := step g1 perBurden (some newId)
  lifeOf g caster == lifeOf g1 caster - 2

#guard
  let g0 := addPermanent afterDraw ring caster caster
  let g0 := g0.addBurdenCounter (obj g0 "Ring") 3
  let g := g0.applyTriggeredAbility caster .onYourUpkeepLoseLifePerBurden
    (some (pid g0 "Ring"))
  lifeOf g caster == lifeOf g0 caster - 3 && (obj g "Ring").status.burden == 3

/- Drain and draw-and-lose still run after the plan counter, and only while
the source is on the battlefield. -/
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

#guard
  let g0 := addPermanent afterDraw ring caster caster
  let id := pid g0 "Ring"
  let (g1, _) := g0.move id (.graveyard caster) none
  let g := g1.applyTriggeredAbility caster (.onVillainYouControlEntersDrainAndPlan 2) (some id)
  lifeOf g caster == lifeOf g1 caster && lifeOf g opp == lifeOf g1 opp &&
    logContains g "no longer"

/- Burden life loss uses the same count for every player selector.
The controller is unchanged. Each named player loses that much. -/
#guard
  let g0 := addPermanent afterDraw ring caster caster
  let g0 := g0.addBurdenCounter (obj g0 "Ring") 5
  let crossed := step g0 (.loseLife .perBurden .eachOpponent) (some (pid g0 "Ring"))
  let swapped := step g0 (.loseLife .perBurden .targetOpponent)
    (some (pid g0 "Ring")) (targets := #[Target.player opp])
    (ab := .onYouSacrificeTokenOppLosesLife)
  lifeOf crossed caster == lifeOf g0 caster && lifeOf crossed opp == lifeOf g0 opp - 5 &&
    logContains crossed "loses 5 life" &&
    lifeOf swapped caster == lifeOf g0 caster && lifeOf swapped opp == lifeOf g0 opp - 5 &&
    logContains swapped "loses 5 life"

/- A count of zero loses nothing. An offer is not a player who loses life. -/
#guard
  let g := step afterDraw (.loseLife .perOtherCreature)
  lifeOf g caster == lifeOf afterDraw caster && lifeOf g opp == lifeOf afterDraw opp &&
    g.log == afterDraw.log

#guard
  let g0 := afterDraw
  let g := step g0 (.loseLife (.fixed 3) .opponentHasYou)
    (targets := #[Target.player opp])
    (ab := .onYouSacrificeTokenOppLosesLife)
  lifeOf g caster == lifeOf g0 caster && lifeOf g opp == lifeOf g0 opp &&
    g.log == g0.log

#guard TriggeredAbility.resolution .onYouSacrificeTokenOppLosesLife == targetOpp 1
#guard TriggeredAbility.resolution .onYourUpkeepLoseLifePerBurden == perBurden
#guard TriggeredAbility.resolution (.onVillainYouControlEntersDrainAndPlan 2) ==
  .sequence [.putCounters (.ofKind .plan) .source, eachOpp 2, .gainLife (.fixed 2)]
#guard TriggeredAbility.resolution .onCreatureCardsToGyDrawLoseLifeAndPlan ==
  .sequence [.putCounters (.ofKind .plan) .source, .draw (.fixed 1), .loseLife (.fixed 1)]

#guard TriggeredAbility.resolutionPhrase { resolution := .loseLife (.fixed 3) } ==
  "you lose 3 life"
#guard TriggeredAbility.resolutionPhrase (SharedTrigger.timing (.targetOpponentLosesLife 1)) ==
  "target opponent loses 1 life"
#guard TriggeredAbility.resolutionPhrase { resolution := eachOpp 2 } ==
  "each opponent loses 2 life"
#guard TriggeredAbility.resolutionPhrase { resolution := perBurden } ==
  "you lose 1 life for each burden counter on this"
#guard TriggeredAbility.resolutionPhrase
    { resolution := .loseLife .perBurden .eachOpponent } == "lose life"
#guard TriggeredAbility.resolutionPhrase
    { resolution := .loseLife .perOtherCreature } == "lose life"

#guard TriggeredAbility.toNotation .onYouSacrificeTokenOppLosesLife ==
  "Whenever you sacrifice a token, target opponent loses 1 life."
#guard TriggeredAbility.toNotation .onYourUpkeepLoseLifePerBurden ==
  "At the beginning of your upkeep, you lose 1 life for each burden counter on The One Ring."
#guard TriggeredAbility.resolutionPhrase (SharedTrigger.timing (.drainAndPlan 2)) ==
  "each opponent loses 2 life and you gain 2 life. Put a plan counter on this enchantment"
#guard TriggeredAbility.resolutionPhrase (SharedTrigger.timing .drawLoseLifeAndPlan) ==
  "you draw a card, lose 1 life, and put a plan counter on this enchantment"

#guard TriggeredAbility.TriggerResolution.gollumModes[1]! ==
  .sequence [.loseLife (.fixed 2) .eachOpponent, .gainLife (.fixed 2)]
#guard TriggeredAbility.TriggerResolution.upToXModes[1]! == eachOpp 2

#guard (SharedTrigger.timing (.targetOpponentLosesLife 1)).resolution == targetOpp 1
#guard (SharedTrigger.timing .loseLifePerBurden).resolution == perBurden

end Mtg.Engine.LoseLifeTests
