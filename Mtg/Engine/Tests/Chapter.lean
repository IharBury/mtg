import Mtg.Engine.Catalog
import Mtg.Engine.Fixture

/-!
# Saga chapters as `TriggerResolution`

A printed chapter is still a `ChapterResolution`. Resolving it uses the
other `TriggerResolution` constructors: damage, destroy, mana, search,
draw, amass, recruit, exile, counters, and the chapter-only steps that
those constructors do not already name.
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

def timing (e : ChapterResolution) : TriggeredAbility.TriggerTiming :=
  TriggeredAbility.chapterTiming e

/- Each printed chapter resolves as a constructor that does not store
`ChapterResolution`. -/
#guard (timing (.dealDamageToOppCreature 6)).resolution == .dealDamage (.fixed 6) .target
#guard (timing .destroyOppArtifact).resolution == .destroy .target
#guard (timing (.addMana (.colored .red))).resolution == .addMana #[.colored .red]
#guard (timing .searchBasicLandToHand).resolution ==
  .searchLibrary (.returnToHand .basicLand)
#guard (timing .gainLandfallCreateElf).resolution == .grant .landfallCreateElf .source
#guard (timing (.elvesGetVigilance 1)).resolution ==
  .sequence [
    .pump (.fixed 1) (.fixed 0) (.intersection [.creaturesYouControl, .youControl (.subtype .elf)]),
    .grant (.keywords Keyword.vigilance) (.intersection [.creaturesYouControl, .youControl (.subtype .elf)])]
#guard (timing .opponentDiscardsNonland).resolution ==
  .discard .chosenNonland
#guard (timing (.amass 1)).resolution == .amass (.fixed 1)
#guard (timing (.opponentLosesYouGain 1)).resolution ==
  .sequence [.loseLife (.fixed 1) (.target .opponent), .gainLife (.fixed 1)]
#guard (timing .grantHexproofWhileRemains).resolution ==
  .grant .hexproofWhileSource .target
#guard (timing .preventDamageWhileRemains).resolution ==
  .grant .preventDamageWhileSource .target
#guard (timing (.draw 2)).resolution == .draw (.fixed 2)
#guard (timing (.searchBasicPlainsExileGainLife 2 2)).resolution ==
  .sequence [
    .searchLibrary (.exile (.basicUpTo .plains 2) .forLater .linked),
    .gainLife (.fixed 2)]
#guard (timing .returnLinkedExileToHand).resolution ==
  .returnToHand .linkedExile
#guard (timing .grantAttackPumpPerPlainsThisTurn).resolution ==
  .queueReflexive (.pump .perPlains .perPlains .target)
#guard (timing .blinkUntilEndStep).resolution == .exile .target .nextEndStep
#guard (timing .treasureThenDragonIfFour).resolution ==
  .sequence [
    .createTokens .treasure (.fixed 1) false,
    .«if» ((.atLeast (.count (.youControl (.subtype .treasure))) (.fixed 4))) (.sacrifice (.sacrificedSource .isSacrificed) .noted),
    .«if» .sourceWasSacrificed (.createTokens .dragon (.fixed 1) false)]
#guard (timing .recruit).resolution == .recruit
#guard (timing (.returnCreatureFromGyMvAtMost 3)).resolution ==
  .put (.creatureMvAtMost 3)
#guard (timing .plusOneUpToOne).resolution ==
  .putCounters (.ofKind .plusOnePlusOne) .permanent
#guard (timing (.gainControlOfUpToTwoCreaturesTotalMvAtMost 6)).resolution ==
  .gainControl .whileSourceRemains
#guard (timing (.dealDamageToEachNonSubtypeAndOpponents 2 .villain)).resolution ==
  .dealDamage (.fixed 2) (.eachNonSubtypeAndOpponents .villain)
#guard (timing .dealXDamageToTargetOpponentGreatestArtifactMv).resolution ==
  .dealDamage .greatestArtifactMv (.player (.target .opponent))
#guard (timing (.spell { resolution := .draw 1 })).resolution == .draw (.fixed 1)
#guard (timing (.spell { resolution := .scry 2 })).resolution == .scry (.fixed 2)
#guard (timing (.spell { resolution := .createTokens .villain21menace 2 })).resolution ==
  .createTokens .villain21menace (.fixed 2) false
#guard (timing (.spell { resolution := .createTokens .treasure (.perSubtype .villain) })).resolution ==
  .createTokens .treasure (.perSubtype .villain) false
#guard (timing (.spell { resolution := .mutualFight .upToOne })).resolution ==
  .fight .announced .upToOneOther
#guard (timing (.spell { resolution := .createGalactus })).resolution ==
  .createTokens .treasure (.fixed 1) false .galactus
#guard TriggeredAbility.resolutionPhrase
    { resolution := .createTokens .treasure .perOtherCreature false } ==
  "create a token"
#guard (timing (.spell { resolution := .nextFreeRGCreature })).resolution ==
  .mayCast .nextRedOrGreenCreature .unlimited .withoutPaying
#guard (timing (.spell { resolution := .plusOneOnEachYouControl })).resolution ==
  .putCounters (.ofKind .plusOnePlusOne) .youControl
#guard (timing (.spell { resolution := .plusOneOnCreatureN 3 })).resolution ==
  .putCounters (.ofKind .plusOnePlusOne 3) .permanent
#guard (timing (.spell { resolution := .loseLife 2 .eachOpponent })).resolution ==
  .loseLife (.fixed 2) .eachOpponent
#guard (timing (.spell { resolution := .destroyUpToOneNonland })).resolution == .destroy .target
#guard (timing (.spell { resolution := .mayPutHeroMvOrDraw 3 })).resolution ==
  .may (.put (.creatureFromHand .hero 3)) (.draw (.fixed 1))
#guard (timing (.spell { resolution := .mayDrawPerArtifactOppsDraw })).resolution ==
  .may (.draw (.perControlled .artifact)) (.draw (.fixed 1) (who := .eachOpponent)) .ifYouDo
#guard (timing (.spell { resolution := .spellsCostLessThisTurn (.cardType .artifact) 1 })).resolution ==
  .spellsCostLess (.cardType .artifact) (.fixed 1)
#guard (timing (.spell {
    resolution := .sequence [.creaturesPump 1 1, .teamGain Keyword.vigilance]
  })).resolution ==
  .sequence [.pump (.fixed 1) (.fixed 1) .creaturesYouControl, .grant (.keywords Keyword.vigilance) .creaturesYouControl]
#guard (timing (.spell {
    resolution := .sequence [
      .onPermanent .doublePowerAndToughness,
      .onPermanent (.grantKeywords Keyword.trample)]
  })).resolution ==
  .sequence [.pump .double .double .target, .grant (.keywords Keyword.trample) .target]

#guard (timing (.dealDamageToOppCreature 6)).targeting.kind == .oppCreature
#guard (timing .plusOneUpToOne).allowsZeroTargets
#guard (timing .blinkUntilEndStep).allowsZeroTargets
#guard !(timing .destroyOppArtifact).allowsZeroTargets

#guard toString (TriggeredAbility.sagaChapter 1 Effect.chapterRecruit) ==
  "When a lore counter is put on this Saga, recruit."
#guard toString (TriggeredAbility.sagaChapter 1 (Effect.chapterDraw 1)) ==
  "When a lore counter is put on this Saga, draw a card."

/- A selector createTokens does not use creates nothing. -/
#guard
  let g := afterDraw.applyTriggeredAbility caster (.onEnterDraw 1) none
    (resolutionOverride := some (.createTokens .treasure .perOtherCreature false))
  g.log.size == afterDraw.log.size

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
  (g.grantedTriggeredAbilities (obj g "Saga")).size == 1 &&
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
