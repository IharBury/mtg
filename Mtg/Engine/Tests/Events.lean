import Mtg.Engine.Fixture

/-!
# Game events

Each change that happens is a `GameEvent` on `Game.events`. A condition
asks that log whether the action happened. A trigger matches the change
that happened. A replacement matches the change that would happen, and the
replaced change is not recorded.
-/

namespace Mtg.Engine.EventTests

open Mtg.Engine
open Mtg.Engine.Catalog
open Mtg.Engine.Tests

def me : PlayerId := ⟨0⟩

def bear : CardDef :=
  creature "Event Bear" ManaCost.empty #["Bear"] 2 2

def hero : CardDef :=
  creature "Event Hero" ManaCost.empty #["Hero"] 2 2

def holds (g : Game) (cond : TriggeredAbility.ConditionSelector) : Game × Bool :=
  g.triggerIfHolds me (.onEnterDraw 1) none #[] none cond

def quiet (g : Game) : Game :=
  g.change .clearEvents

/- Drawing is recorded, and the draw condition reads the log after the
turn counter is cleared. -/
#guard
  let g := quiet afterDraw
  let (_, noDraw) := holds g (.atLeast .cardsDrawnThisTurn (.fixed 1))
  let g := (g.record (GameEvent.drew g.turnNumber me ⟨9⟩ 1)).record
    (GameEvent.drew g.turnNumber me ⟨8⟩ 2)
  let (_, two) := holds g (.atLeast .cardsDrawnThisTurn (.fixed 2))
  let (_, three) := holds g (.atLeast .cardsDrawnThisTurn (.fixed 3))
  !noDraw && two && !three && g.loggedDraws me == 2

/- Scrying and surveilling are the look events. Scry 0 does not count. -/
#guard
  let g := quiet afterDraw
  let (_, noScry) := holds g .scriedThisTurn
  let (_, noSurveil) := holds g .surveilledThisTurn
  let g := g.record (GameEvent.looked g.turnNumber me 0)
  let (_, zero) := holds g .scriedThisTurn
  let g := g.record (GameEvent.looked g.turnNumber me 2)
  let (_, scried) := holds g .scriedThisTurn
  let g := g.record (GameEvent.looked g.turnNumber me 1 true)
  let (_, surveilled) := holds g .surveilledThisTurn
  !noScry && !noSurveil && !zero && scried && surveilled

/- An artifact that entered is in the log, including after the flag is clear. -/
#guard
  let g := quiet afterDraw
  let (_, no) := holds g .artifactEnteredThisTurn
  let entered := GameEvent.moved g.turnNumber
    { id := ⟨4⟩, controller := some me, owner := me, types := #[.artifact] } .stack .battlefield
  let g := g.record entered
  let (_, yes) := holds g .artifactEnteredThisTurn
  !no && yes && entered.watches .wouldEnterBattlefield

/- A Hero that left after attacking still counts, from the attack event. -/
#guard
  let g := quiet afterDraw
  let attack := GameEvent.attacked g.turnNumber me
    { id := ⟨5⟩, controller := some me, owner := me, types := #[.creature], subtypes := #[.hero] } ⟨1⟩
  let entered := GameEvent.moved g.turnNumber
    { id := ⟨6⟩, controller := some me, owner := me, types := #[.creature], subtypes := #[.villain] } .stack .battlefield
  let g := (g.record attack).record entered
  let (_, yes) := holds g (.attackedWithSubtype .hero)
  let (_, no) := holds g (.attackedWithSubtype .goblin)
  yes && !no && attack.matchesTrigger me ⟨5⟩ .attacking &&
    entered.matchesTrigger me ⟨0⟩ (.subtypeYouControlEnters .villain) &&
    !entered.matchesTrigger me ⟨0⟩ (.subtypeYouControlEnters .hero) &&
    GameEvent.subtypeEntered g.events g.turnNumber me .villain &&
    !GameEvent.subtypeEntered g.events g.turnNumber me .goblin

/- A second draw matches the second-card triggers and not a first-card one.
A creature moving to a graveyard matches dies, and not once it is exiled
instead. -/
#guard
  let second := GameEvent.drew 1 me ⟨1⟩ 2
  let death := GameEvent.moved 1
    { id := ⟨7⟩, controller := some me, owner := me, types := #[.creature] } .battlefield (.graveyard me)
  let exiled := death.withDestination .exile false
  second.matchesTrigger me ⟨0⟩ .youDraw &&
    second.matchesTrigger me ⟨0⟩ .youDrawSecondCard &&
    second.matchesTrigger ⟨1⟩ ⟨0⟩ .opponentDrawsSecondCard &&
    !second.matchesTrigger ⟨1⟩ ⟨0⟩ .youDraw &&
    death.matchesTrigger me ⟨7⟩ .dying &&
    death.watches .wouldDie &&
    !exiled.isCreatureToGraveyard &&
    !exiled.watches .wouldDie &&
    (GameEvent.looked 1 me 3).matchesTrigger me ⟨0⟩ .youScry

/- The engine records a real draw and a real death, and an exile replacement
records the exile instead of the death. -/
#guard
  let g0 := quiet afterDraw
  let before := g0.events.size
  let g := g0.draw me 1
  let drew := g.events.any fun e =>
    match e.change with
    | .effectApplied _ (.drew p _ _ _) => p == me
    | _ => false
  let g := addPermanent g bear me me
  let b := (g.battlefield.filter (·.name == "Event Bear"))[0]!
  let (g, id) := g.move b.id (.graveyard me) none
  let died :=
    match g.events.back? with
    | some e => e.isCreatureToGraveyard && (g.object! id).zone == .graveyard me
    | none => false
  let g := addPermanent g hero me me
  let h := (g.battlefield.filter (·.name == "Event Hero"))[0]!
  let g := g.changeStatus h.id (.untilEotExileIfDies true)
  let (g, id) := g.move h.id (.graveyard me) none
  let replaced :=
    (g.object! id).zone == .exile &&
      match g.events.back? with
      | some e => !e.isCreatureToGraveyard &&
          match e.change with
          | .effectApplied _ (.moved _ _ .exile _ _) => true
          | _ => false
      | none => false
  g.events.size > before && drew && died && replaced

/- Rule 611: applying `effectCreated` and `effectExpired` directly via
`Game.applyChange` updates and reverts state in isolation. -/
#guard
  let g0 := addPermanent (quiet afterDraw) bear me me
  let b := (g0.battlefield.filter (·.name == "Event Bear"))[0]!
  let pump := ContinuousEffect.pump b.id 3 3
  let kw := ContinuousEffect.keywordsUntilEot b.id Keyword.trample
  let g1 := (g0.applyChange (.effectCreated ⟨100⟩ pump)).applyChange (.effectCreated ⟨101⟩ kw)
  let applied :=
    (g1.object! b.id).status.pump == (3, 3) &&
      (g1.object! b.id).status.untilEotKeywords == Keyword.trample
  let g2 := (g1.applyChange (.effectExpired ⟨100⟩ pump)).applyChange (.effectExpired ⟨101⟩ kw)
  let reverted :=
    (g2.object! b.id).status.pump == (0, 0) &&
      (g2.object! b.id).status.untilEotKeywords == Keywords.none
  applied && reverted

/- Rule 611.2a / 514.2: resolution-generated until-end-of-turn continuous
effects record `effectCreated` when created and `effectExpired` during cleanup. -/
#guard
  let g0 := quiet (addPermanent afterDraw bear me me)
  let b := (g0.battlefield.filter (·.name == "Event Bear"))[0]!
  let g1 := (g0.pumpPermanent b 2 2 (trample := true)).createEffect (.cantBlockUntilEot b.id)
  let created := GameEvent.createdEffects g1.events
  let hasCreated :=
    created.contains (.pump b.id 2 2) &&
      created.contains (.keywordsUntilEot b.id Keyword.trample) &&
      created.contains (.cantBlockUntilEot b.id)
  let g2 := (quiet g1).clearEOT
  let expired := GameEvent.expiredEffects g2.events
  let hasExpired :=
    expired.contains (.pump b.id 2 2) &&
      expired.contains (.keywordsUntilEot b.id Keyword.trample) &&
      expired.contains (.cantBlockUntilEot b.id) &&
      (g2.object! b.id).status.pump == (0, 0) &&
      (g2.object! b.id).status.untilEotKeywords == Keywords.none &&
      !(g2.object! b.id).status.cantBlockUntilEot
  hasCreated && hasExpired

/- Rule 611.2b: until-next-turn, while-source-remains, and until-cast / play
permission continuous effects record `effectCreated` and `effectExpired` when
their duration ends. -/
#guard
  let g0 := quiet (addPermanent (addPermanent afterDraw bear me me) hero me me)
  let b := (g0.battlefield.filter (·.name == "Event Bear"))[0]!
  let h := (g0.battlefield.filter (·.name == "Event Hero"))[0]!
  let prot := ContinuousEffect.protectionFromEverything me
  let untilTurnPump := ContinuousEffect.untilTurnOfPump b.id me (-2) (-2)
  let lock := ContinuousEffect.cantUntapWhileSource b.id h.id
  let perm : PlayPermission := { player := me, turnEndsRemaining := 1 }
  let g1 := (((g0.createEffect prot).createEffect untilTurnPump).createEffect lock).createEffect (.playPermission b.id perm)
  let created := GameEvent.createdEffects g1.events
  let hasCreated :=
    created.contains prot &&
      created.contains untilTurnPump &&
      created.contains lock &&
      created.contains (.playPermission b.id perm)
  -- Moving the source off the battlefield expires `cantUntapWhileSource`.
  let (g2, _) := (quiet g1).move h.id (.graveyard me) none
  let expiredOnLeave := GameEvent.expiredEffects g2.events
  -- Expiring until-next-turn effects for `me` expires `protectionFromEverything`, `untilTurnOfPump`, and the play permission.
  let g3 := (quiet g2).expireUntilNextTurnEffects me
  let expiredAtTurn := GameEvent.expiredEffects g3.events
  hasCreated &&
    expiredOnLeave.contains lock &&
    (g2.object! b.id).status.cantUntapGrantedBy == #[] &&
    expiredAtTurn.contains (.playPermission b.id perm) &&
    expiredAtTurn.contains prot &&
    expiredAtTurn.contains untilTurnPump &&
    !(g3.player me).protectionFromEverything &&
    (g3.object! b.id).status.untilTurnOfPump == #[]

/- Rule 611.3: static-ability continuous effects are created when a permanent
with static abilities enters the battlefield, expire if it loses all abilities,
are re-created when ability loss wears off, and expire when it leaves the
battlefield. -/
#guard
  let lordDef : CardDef :=
    { bear with
      name := "Bear Lord"
      staticAbilities := #[.fra .creaturesYouControlHaveTrample] }
  let g0 := quiet afterDraw
  let g1 := addPermanent g0 lordDef me me
  let lord := (g1.battlefield.filter (·.name == "Bear Lord"))[0]!
  let staticEff := ContinuousEffect.staticAbility lord.id (.fra .creaturesYouControlHaveTrample)
  let createdOnEnter := (GameEvent.createdEffects g1.events).contains staticEff
  let g2 := (quiet g1).createEffect (.losesAbilitiesUntilEot lord.id)
  let expiredOnLose := (GameEvent.expiredEffects g2.events).contains staticEff
  let g3 := (quiet g2).clearEOT
  let recreatedOnCleanup := (GameEvent.createdEffects g3.events).contains staticEff
  let (g4, _) := (quiet g3).move lord.id (.graveyard me) none
  let expiredOnLeave := (GameEvent.expiredEffects g4.events).contains staticEff
  createdOnEnter && expiredOnLose && recreatedOnCleanup && expiredOnLeave

/- Rule 610: applications of one-shot effects (drawing cards, moving objects
between zones, gaining/losing life, dealing damage, putting counters, tapping/
untapping permanents, creating tokens, scrying/surveilling) are recorded as
`GameChange.effectApplied` events with unique `EffectId`s. -/
#guard
  let g0 := quiet (addPermanent afterDraw bear me me)
  let b := (g0.battlefield.filter (·.name == "Event Bear"))[0]!
  let g1 := g0.draw me 1
  let g2 := g1.gainLife me 3
  let g3 := g2.loseLife me 2
  let g4 := g3.record (GameEvent.counters g3.turnNumber (some me) b.asEvent .plusOnePlusOne 2 false)
  let g5 := g4.record (GameEvent.tapped g4.turnNumber b.asEvent true true)
  let g6 := g5.record (GameEvent.untapped g5.turnNumber b.asEvent false)
  let g7 := g6.createTreasureTokens me 1
  let appliedWithIds := GameEvent.appliedEffectsWithId g7.events
  let ids := appliedWithIds.map Prod.fst
  let effs := appliedWithIds.map Prod.snd
  let uniqueIds :=
    Id.run do
      let mut seen : Array EffectId := #[]
      for id in ids do
        if !seen.contains id then
          seen := seen.push id
      return seen.size == ids.size
  let hasDraw := effs.any (fun | .drew p _ _ _ => p == me | _ => false)
  let hasMove := effs.any (fun | .moved _ (.library _) (.hand _) _ _ => true | _ => false)
  let hasGain := effs.any (fun | .life p 3 true _ _ => p == me | _ => false)
  let hasLoss := effs.any (fun | .life p 2 false _ _ => p == me | _ => false)
  let hasCounters := effs.any (fun | .counters _ obj .plusOnePlusOne 2 false => obj.id == b.id | _ => false)
  let hasTap := effs.any (fun | .tapped obj true true => obj.id == b.id | _ => false)
  let hasUntap := effs.any (fun | .untapped obj false => obj.id == b.id | _ => false)
  let hasToken := effs.any (fun | .created p obj => p == me && obj.token | _ => false)
  uniqueIds && ids.size >= 8 &&
    hasDraw && hasMove && hasGain && hasLoss &&
    hasCounters && hasTap && hasUntap && hasToken

/- Unique `EffectId`s across one-shot (Rule 610) and continuous (Rule 611)
effects: each effect receives a distinct `EffectId` from `g.nextEffectId`,
`effectExpired` carries the exact same `EffectId` as `effectCreated` (even when
multiple pumps are active on the same object), and `EffectId` allocation does
not interfere with `ObjectId` (`g.nextObjectId`). -/
#guard
  let g0 := quiet (addPermanent afterDraw bear me me)
  let b := (g0.battlefield.filter (·.name == "Event Bear"))[0]!
  let objIdBefore := g0.nextObjectId
  let effIdBefore := g0.nextEffectId
  -- Apply two separate pump continuous effects and a one-shot life gain without creating any objects.
  let g1 := ((g0.createEffect (.pump b.id 2 2)).gainLife me 4).createEffect (.pump b.id 1 3)
  let objIdUnchanged := g1.nextObjectId == objIdBefore
  let createdPairs := GameEvent.createdEffectsWithId g1.events
  let appliedPairs := GameEvent.appliedEffectsWithId g1.events
  -- Now create a token (which increments `nextObjectId` AND emits a one-shot `created` effect).
  let g2 := g1.createTreasureTokens me 1
  let objIdIncremented := g2.nextObjectId == objIdBefore + 1
  -- Expire until-end-of-turn continuous effects during cleanup.
  let g3 := (quiet g2).clearEOT
  let expiredPairs := GameEvent.expiredEffectsWithId g3.events
  let allCreationAndOneShotIds :=
    (createdPairs.map Prod.fst) ++ (appliedPairs.map Prod.fst)
  let allDistinct :=
    Id.run do
      let mut seen : Array EffectId := #[]
      for id in allCreationAndOneShotIds do
        if !seen.contains id then
          seen := seen.push id
      return seen.size == allCreationAndOneShotIds.size
  objIdUnchanged &&
    objIdIncremented &&
    g1.nextEffectId == effIdBefore + 3 &&
    createdPairs.size == 2 &&
    appliedPairs.size == 1 &&
    allDistinct &&
    expiredPairs == createdPairs &&
    (g3.object! b.id).status.pump == (0, 0) &&
    g3.activeEffects.all (fun (_, e) =>
      match e with
      | .pump id _ _ => id != b.id
      | _ => true)

end Mtg.Engine.EventTests
