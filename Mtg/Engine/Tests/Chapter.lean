import Mtg.Engine.Catalog
import Mtg.Engine.Fixture

/-!
# Saga chapters as unified `Instruction` `Effect`s (CR 714.2)

Each Saga chapter ability carries a unified `Instruction` body executed
directly by `Game/Interpreter.lean`.
-/

namespace Mtg.Engine.ChapterTests

open Mtg.Engine
open Mtg.Engine.Catalog
open Mtg.Engine.Tests

def caster : PlayerId := ⟨0⟩
def opp : PlayerId := ⟨1⟩

def step (g : Game) (e : Effect) (sourceId : Option ObjectId := none)
    (targets : Array Target := #[]) : Game :=
  g.applyTriggeredAbility caster (TriggeredAbility.sagaChapter 1 e) sourceId targets

def obj (g : Game) (name : String) : GameObject :=
  match g.objects.find? (·.name == name) with
  | some o => o
  | none => panic! s!"missing {name}"

def pid (g : Game) (name : String) : ObjectId :=
  (obj g name).id

def onBoard (g : Game) (name : String) : Bool :=
  match g.objects.find? (·.name == name) with
  | some o => o.isOnBattlefield
  | none => false

def saga : CardDef := enchantment "Saga" ManaCost.empty ""
def relic : CardDef := artifact "Relic" (ManaCost.ofGeneric 4) ""
def bear : CardDef := creature "Bear" ManaCost.empty #[] 2 2
def elf : CardDef := creature "Elf" ManaCost.empty #["Elf"] 1 1
def villain : CardDef := creature "Villain" ManaCost.empty #["Villain"] 2 2
def lost : CardDef := creature "Lost" ManaCost.empty #[] 1 1
def bolt : CardDef := { name := "Bolt", types := #[.instant] }

def withSaga : Game := addPermanent afterDraw saga caster caster

/- Every chapter effect smart constructor carries a non-noop unified `Instruction`. -/
#guard (Effect.chapterDealDamageToOppCreature 6).body != .noop
#guard Effect.chapterDestroyOppArtifact.body != .noop
#guard (Effect.chapterAddMana (.colored .red)).body != .noop
#guard Effect.chapterSearchBasicLandToHand.body != .noop
#guard Effect.chapterGainLandfallCreateElf.body != .noop
#guard (Effect.chapterElvesGetVigilance 1).body != .noop
#guard Effect.chapterOpponentDiscardsNonland.body != .noop
#guard (Effect.chapterAmassGoblins 1).body != .noop
#guard (Effect.chapterOpponentLosesYouGain 1).body != .noop
#guard Effect.chapterGrantHexproofWhileRemains.body != .noop
#guard Effect.chapterPreventDamageWhileRemains.body != .noop
#guard (Effect.chapterDraw 2).body != .noop
#guard (Effect.chapterSearchBasicPlainsExileGainLife 2 2).body != .noop
#guard Effect.chapterReturnLinkedExileToHand.body != .noop
#guard Effect.chapterGrantAttackPumpPerPlainsThisTurn.body != .noop
#guard Effect.chapterBlinkUntilEndStep.body != .noop
#guard Effect.chapterTreasureThenDragonIfFour.body != .noop
#guard Effect.chapterRecruit.body != .noop
#guard (Effect.chapterReturnCreatureFromGyMvAtMost 3).body != .noop
#guard Effect.chapterPlusOneUpToOne.body != .noop
#guard (Effect.chapterGainControlOfUpToTwoCreaturesTotalMvAtMost 6).body != .noop
#guard (Effect.chapterDealDamageToEachNonSubtypeAndOpponents 2 "Villain").body != .noop
#guard Effect.chapterDealXDamageToTargetOpponentGreatestArtifactMv.body != .noop

#guard (Effect.chapterDealDamageToOppCreature 6).targeting.spec == .oppCreature
#guard Effect.chapterPlusOneUpToOne.allowsZeroTargets
#guard Effect.chapterBlinkUntilEndStep.allowsZeroTargets
#guard !Effect.chapterDestroyOppArtifact.allowsZeroTargets

#guard toString (TriggeredAbility.sagaChapter 1 Effect.chapterRecruit) ==
  "When a lore counter is put on this Saga, recruit."
#guard toString (TriggeredAbility.sagaChapter 1 (Effect.chapterDraw 1)) ==
  "When a lore counter is put on this Saga, draw a card."

/- Drawing, adding mana, and recruiting go through those constructors. -/
#guard
  let before := (afterDraw.player caster).hand.size
  let g := step afterDraw (Effect.chapterDraw 1)
  (g.player caster).hand.size == before + 1 && logContains g "draws"

#guard
  let g := step afterDraw (Effect.chapterAddMana (.colored .red))
  (g.player caster).manaPool.get (.colored .red) == 1 &&
    logContains g "adds mana"

#guard
  let g := step afterDraw Effect.chapterRecruit
  (g.player caster).hand.size == (afterDraw.player caster).hand.size + 1 &&
    match g.pending with
    | .recruitDiscard p => p == caster
    | _ => false

/- The announced opposing artifact is destroyed. Yours stays. -/
#guard
  let g0 := addPermanent (addPermanent withSaga relic opp opp)
    (artifact "Mine" ManaCost.empty "") caster caster
  let g := step g0 Effect.chapterDestroyOppArtifact
    (targets := #[Target.permanent (pid g0 "Relic")])
  !onBoard g "Relic" && onBoard g "Mine"

/- Damage to the announced creature an opponent controls. -/
#guard
  let g0 := addPermanent withSaga bear opp opp
  let g := step g0 (Effect.chapterDealDamageToOppCreature 3)
    (targets := #[Target.permanent (pid g0 "Bear")])
  (obj g "Bear").status.damage == 3

/- The opponent loses life and you gain it. An illegal target does neither. -/
#guard
  let beforeYou := (afterDraw.player caster).life
  let beforeOpp := (afterDraw.player opp).life
  let g := step afterDraw (Effect.chapterOpponentLosesYouGain 2)
    (targets := #[Target.player opp])
  (g.player opp).life == beforeOpp - 2 &&
    (g.player caster).life == beforeYou + 2

#guard
  let g := step afterDraw (Effect.chapterOpponentLosesYouGain 2)
    (targets := #[Target.player caster])
  (g.player caster).life == (afterDraw.player caster).life &&
    (g.player opp).life == (afterDraw.player opp).life

/- Elves get +1/+0 and vigilance. Another creature does not. -/
#guard
  let g0 := addPermanent (addPermanent withSaga elf caster caster) bear caster caster
  let g := step g0 (Effect.chapterElvesGetVigilance 1)
  g.power (obj g "Elf") == 2 && g.hasVigilance (obj g "Elf") &&
    g.power (obj g "Bear") == 2 && !g.hasVigilance (obj g "Bear")

/- Hexproof and damage prevention last while the source remains.
Choosing no creature for prevention changes nothing. -/
#guard
  let g0 := addPermanent withSaga bear caster caster
  let sid := pid g0 "Saga"
  let g := step g0 Effect.chapterGrantHexproofWhileRemains (sourceId := some sid)
    (targets := #[Target.permanent (pid g0 "Bear")])
  g.hexproofGrantedBy (obj g "Bear") == #[sid]

#guard
  let g0 := addPermanent withSaga bear caster caster
  let sid := pid g0 "Saga"
  let g := step g0 Effect.chapterPreventDamageWhileRemains (sourceId := some sid)
    (targets := #[Target.permanent (pid g0 "Bear")])
  g.preventDamageGrantedBy (obj g "Bear") == #[sid]

#guard
  let g := step withSaga Effect.chapterPreventDamageWhileRemains
    (sourceId := some (pid withSaga "Saga"))
  !logContains g "no longer legal"

/- A +1/+1 counter on the announced creature. Choosing none is silent. -/
#guard
  let g0 := addPermanent withSaga bear caster caster
  let g := step g0 Effect.chapterPlusOneUpToOne
    (targets := #[Target.permanent (pid g0 "Bear")])
  (obj g "Bear").status.plusOnePlusOne == 1

#guard
  let g := step withSaga Effect.chapterPlusOneUpToOne
    (sourceId := some (pid withSaga "Saga"))
  !logContains g "no longer legal"

/- Exile until the next end step. Choosing none does nothing. -/
#guard
  let g0 := addPermanent withSaga bear caster caster
  let g := step g0 Effect.chapterBlinkUntilEndStep
    (targets := #[Target.permanent (pid g0 "Bear")])
  (obj g "Bear").zone == .exile &&
    logContains g "exiled until the beginning of the next end step"

/- The source gains landfall, and this turn's attacks pump per Plains. -/
#guard
  let g := step withSaga Effect.chapterGainLandfallCreateElf
    (sourceId := some (pid withSaga "Saga"))
  (g.triggeredAbilities (obj g "Saga")).size == 1 &&
    logContains g "gains landfall"

#guard
  let g := step withSaga Effect.chapterGrantAttackPumpPerPlainsThisTurn
  (g.delayedTriggers.filter (fun dt => dt.controller == caster && dt.kind == .attackPumpPerPlains)).size == 1

/- Non-Villain creatures and each opponent are dealt damage. -/
#guard
  let g0 := addPermanent (addPermanent withSaga bear opp opp) villain caster caster
  let before := (g0.player opp).life
  let g := step g0 (Effect.chapterDealDamageToEachNonSubtypeAndOpponents 2 "Villain")
  (obj g "Bear").status.damage == 2 && (obj g "Villain").status.damage == 0 &&
    (g.player opp).life == before - 2

/- X is the greatest mana value among artifacts you control. -/
#guard
  let g0 := addPermanent withSaga relic caster caster
  let before := (g0.player opp).life
  let g := step g0 Effect.chapterDealXDamageToTargetOpponentGreatestArtifactMv
    (targets := #[Target.player opp])
  (g.player opp).life == before - 4

/- Four Treasures sacrifice the Saga and create a Dragon. Three do not. -/
#guard
  let g0 := withSaga.createTreasureTokens caster 3
  let g := step g0 Effect.chapterTreasureThenDragonIfFour
    (sourceId := some (pid g0 "Saga"))
  !onBoard g "Saga" && g.battlefield.any (·.name == "Dragon") &&
    logContains g "Saga is sacrificed"

#guard
  let g0 := withSaga.createTreasureTokens caster 2
  let g := step g0 Effect.chapterTreasureThenDragonIfFour
    (sourceId := some (pid g0 "Saga"))
  onBoard g "Saga" && !g.battlefield.any (·.name == "Dragon")

/- Gain control while the source remains. A source that has left does not. -/
#guard
  let g0 := addPermanent withSaga bear opp opp
  let sid := pid g0 "Saga"
  let g := step g0 (Effect.chapterGainControlOfUpToTwoCreaturesTotalMvAtMost 6)
    (sourceId := some sid)
    (targets := #[Target.permanent (pid g0 "Bear")])
  g.controllerOf (obj g "Bear") == some caster &&
    g.controlUntilSourceLeaves (obj g "Bear") == some sid

#guard
  let g0 := addPermanent withSaga bear opp opp
  let sid := pid g0 "Saga"
  let (g1, _) := g0.move sid (.graveyard caster) none
  let g := step g1 (Effect.chapterGainControlOfUpToTwoCreaturesTotalMvAtMost 6)
    (sourceId := some sid)
    (targets := #[Target.permanent (pid g1 "Bear")])
  (obj g "Bear").controller == some opp &&
    logContains g "won't gain control"

/- A creature card in the graveyard returns. The exiled card returns to hand. -/
#guard
  let g0 := addPermanent withSaga lost caster caster
  let id := pid g0 "Lost"
  let (g1, newId) := g0.move id (.graveyard caster) none
  let g := step g1 (Effect.chapterReturnCreatureFromGyMvAtMost 3)
    (targets := #[Target.card newId])
  onBoard g "Lost" && logContains g "returns to the battlefield"

#guard
  let g0 := insertObject withSaga lost caster .exile
  let card := pid g0 "Lost"
  let src := obj g0 "Saga"
  let g0 := g0.changeObject src.id (.linkedExile #[card])
  let g := step g0 Effect.chapterReturnLinkedExileToHand
    (sourceId := some src.id)
  (obj g "Lost").zone == .hand caster &&
    (obj g "Saga").linkedExile.isEmpty

/- The opponent reveals a nonland and discards it. -/
#guard
  let g0 := insertObject (emptyHand withSaga opp) bolt opp (.hand opp)
  let g := step g0 Effect.chapterOpponentDiscardsNonland
    (targets := #[Target.player opp])
  (obj g "Bolt").zone == .graveyard opp &&
    logContains g "discards"

/- Searching for a basic land, and for Plains, waits on that search. -/
#guard
  let g := step afterDraw Effect.chapterSearchBasicLandToHand
  match g.pending with
  | .fraChoice _ (.searchLibrary _ _ .hand _ _) => true
  | _ => false

#guard
  let g0 := insertObject withSaga plains caster (.library caster)
  let g := step g0 (Effect.chapterSearchBasicPlainsExileGainLife 2 2)
    (sourceId := some (pid g0 "Saga"))
  match g.pending with
  | .fraChoice _ (.searchLibrary _ _ (.exileLinked _) _ _) => true
  | _ => false

end Mtg.Engine.ChapterTests
