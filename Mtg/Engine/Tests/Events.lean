import Mtg.Engine.Agent
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

def testCause : EventCause := .oneShotEffect (some ⟨1⟩) none (some me)

def bear : CardDef :=
  creature "Event Bear" ManaCost.empty #["Bear"] 2 2

def hero : CardDef :=
  creature "Event Hero" ManaCost.empty #["Hero"] 2 2

def holds (g : Game) (cond : TriggeredAbility.ConditionSelector) : Game × Bool :=
  g.triggerIfHolds me (.onEnterDraw 1) none #[] none cond

def quiet (g : Game) : Game :=
  { g with events := #[] }

/- Drawing is recorded, and the draw condition reads the log after the
turn counter is cleared. -/
#guard
  let g := quiet afterDraw
  let (_, noDraw) := holds g (.atLeast .cardsDrawnThisTurn (.fixed 1))
  let g := (g.record (GameEvent.drew g.turnNumber me ⟨9⟩ 1 (cause := testCause))).record
    (GameEvent.drew g.turnNumber me ⟨8⟩ 2 (cause := testCause))
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
    { id := some ⟨4⟩, controller := some me, owner := me, types := #[.artifact] } .stack .battlefield
    (cause := testCause)
  let g := g.record entered
  let (_, yes) := holds g .artifactEnteredThisTurn
  !no && yes && entered.watches .wouldEnterBattlefield

/- A Hero that left after attacking still counts, from the attack event. -/
#guard
  let g := quiet afterDraw
  let attack := GameEvent.attacked g.turnNumber me
    { id := some ⟨5⟩, controller := some me, owner := me, types := #[.creature], subtypes := #[.hero] } ⟨1⟩
  let entered := GameEvent.moved g.turnNumber
    { id := some ⟨6⟩, controller := some me, owner := me, types := #[.creature], subtypes := #[.villain] } .stack .battlefield
    (cause := testCause)
  let g := (g.record attack).record entered
  let (_, yes) := holds g (.attackedWithSubtype .hero)
  let (_, no) := holds g (.attackedWithSubtype .goblin)
  yes && !no && attack.matchesTrigger me (some ⟨5⟩) .attacking &&
    entered.matchesTrigger me none (.subtypeYouControlEnters .villain) &&
    !entered.matchesTrigger me none (.subtypeYouControlEnters .hero) &&
    GameEvent.subtypeEntered g.events g.turnNumber me .villain &&
    !GameEvent.subtypeEntered g.events g.turnNumber me .goblin

/- A second draw matches the second-card triggers and not a first-card one.
A creature moving to a graveyard matches dies, and not once it is exiled
instead. -/
#guard
  let second := GameEvent.drew 1 me ⟨1⟩ 2 (cause := testCause)
  let death := GameEvent.moved 1
    { id := some ⟨7⟩, controller := some me, owner := me, types := #[.creature] } .battlefield (.graveyard me)
    (cause := testCause)
  let exiled := GameEvent.moved 1
    { id := some ⟨7⟩, controller := some me, owner := me, types := #[.creature] } .battlefield .exile
    (cause := testCause)
  second.matchesTrigger me none .youDraw &&
    second.matchesTrigger me none .youDrawSecondCard &&
    second.matchesTrigger ⟨1⟩ none .opponentDrawsSecondCard &&
    !second.matchesTrigger ⟨1⟩ none .youDraw &&
    death.matchesTrigger me (some ⟨7⟩) .dying &&
    death.watches .wouldDie &&
    !exiled.isCreatureToGraveyard &&
    !exiled.watches .wouldDie &&
    (GameEvent.looked 1 me 3).matchesTrigger me none .youScry

/- The engine records a real draw and a real death, and an exile replacement
records the exile instead of the death. -/
#guard
  let g0 := quiet afterDraw
  let before := g0.events.size
  let g := g0.draw me 1
  let drew := g.events.any fun e =>
    match e.change with
    | .rules (.zone (.moved _ _ (.library p) (.hand q) (.draw _ _) (some actor) _ _)) =>
      p == me && q == me && actor == me
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
  let g := g.createEffect (.exileIfDiesUntilEot h.id)
  let (g, id) := g.move h.id (.graveyard me) none
  let lastZoneMove := g.events.findSomeRev? fun e =>
    match e.change with
    | .rules (.zone _) => some e
    | _ => none
  let replaced :=
    (g.object! id).zone == .exile &&
      match lastZoneMove with
      | some e => !e.isCreatureToGraveyard &&
          match e.change with
          | .rules (.zone (.moved _ _ _ .exile _ _ _ _)) => true
          | _ => false
      | none => false
  g.events.size > before && drew && died && replaced

/- Rule 611: applying `ContinuousEffectEvent.created` and
`ContinuousEffectEvent.expired` directly via `Game.applyChange` updates and
reverts state in isolation. -/
#guard
  let g0 := addPermanent (quiet afterDraw) bear me me
  let b := (g0.battlefield.filter (·.name == "Event Bear"))[0]!
  let pump := ContinuousEffectSpec.pump b.id 3 3
  let kw := ContinuousEffectSpec.keywordsUntilEot b.id Keyword.trample
  let g1 := (g0.applyChange (.rules (.continuousEffect (.created ⟨100⟩ pump)))).applyChange
    (.rules (.continuousEffect (.created ⟨101⟩ kw)))
  let applied :=
    g1.pumpOf (g1.object! b.id) == (3, 3) &&
      g1.currentKeywords (g1.object! b.id) == Keyword.trample
  let g2 := (g1.applyChange (.rules (.continuousEffect (.expired ⟨100⟩)))).applyChange
    (.rules (.continuousEffect (.expired ⟨101⟩)))
  let reverted :=
    g2.pumpOf (g2.object! b.id) == (0, 0) &&
      g2.currentKeywords (g2.object! b.id) == Keywords.none
  applied && reverted

/- Rule 611.2a / 514.2: resolution-generated until-end-of-turn continuous
effects record `ContinuousEffectEvent.created` when created and
`ContinuousEffectEvent.expired` during cleanup. -/
#guard
  let g0 := quiet (addPermanent afterDraw bear me me)
  let b := (g0.battlefield.filter (·.name == "Event Bear"))[0]!
  let g1 := (g0.pumpPermanent b 2 2 (trample := true)).createEffect (.cantBlockUntilEot b.id)
  let created := GameEvent.createdEffects g1.events
  let hasCreated :=
    created.contains (.pump b.id 2 2) &&
      created.contains (.keywordsUntilEot b.id Keyword.trample) &&
      created.contains (.cantBlockUntilEot b.id)
  let g2 := g1.clearEOT
  let expired := GameEvent.expiredEffects g2.events
  let hasExpired :=
    expired.contains (.pump b.id 2 2) &&
      expired.contains (.keywordsUntilEot b.id Keyword.trample) &&
      expired.contains (.cantBlockUntilEot b.id) &&
      g2.pumpOf (g2.object! b.id) == (0, 0) &&
      g2.currentKeywords (g2.object! b.id) == Keywords.none &&
      !g2.cantBlockUntilEot (g2.object! b.id)
  hasCreated && hasExpired

/- Rule 611.2a–b: until-next-turn, while-source-remains, and until-cast / play
permission continuous effects record `ContinuousEffectEvent.created` and
`ContinuousEffectEvent.expired` when their duration ends. -/
#guard
  let g0 := quiet (addPermanent (addPermanent afterDraw bear me me) hero me me)
  let b := (g0.battlefield.filter (·.name == "Event Bear"))[0]!
  let h := (g0.battlefield.filter (·.name == "Event Hero"))[0]!
  let prot := ContinuousEffectSpec.protectionFromEverything me
  let untilTurnPump := ContinuousEffectSpec.untilTurnOfPump b.id me (-2) (-2)
  let lock := ContinuousEffectSpec.cantUntapWhileSource b.id h.id
  let perm : PlayPermission := { player := me }
  let g1 := (((g0.createEffect prot).createEffect untilTurnPump).createEffect lock).createEffect (.playPermission b.id perm)
  let created := GameEvent.createdEffects g1.events
  let hasCreated :=
    created.contains prot &&
      created.contains untilTurnPump &&
      created.contains lock &&
      created.contains (.playPermission b.id perm)
  -- Moving the source off the battlefield expires `cantUntapWhileSource`.
  let (g2, _) := g1.move h.id (.graveyard me) none
  let expiredOnLeave := GameEvent.expiredEffects g2.events
  -- Expiring until-next-turn effects for `me` expires `protectionFromEverything`, `untilTurnOfPump`, and the play permission.
  let g3 := g2.expireUntilNextTurnEffects me
  let expiredAtTurn := GameEvent.expiredEffects g3.events
  hasCreated &&
    expiredOnLeave.contains lock &&
    g2.cantUntapGrantedBy (g2.object! b.id) == #[] &&
    expiredAtTurn.contains (.playPermission b.id perm) &&
    expiredAtTurn.contains prot &&
    expiredAtTurn.contains untilTurnPump &&
    !g3.protectionFromEverything me &&
    g3.untilTurnOfPump (g3.object! b.id) == #[]

/- Rule 611.3 / 613.1f: printed static abilities apply directly in Layer 6
without emitting continuous-effect journal events when the permanent enters,
loses all abilities, regains abilities, or leaves the battlefield. -/
#guard
  let lordDef : CardDef :=
    { bear with
      name := "Bear Lord"
      staticAbilities := #[.fra .creaturesYouControlHaveTrample] }
  let g0 := quiet afterDraw
  let g1 := addPermanent g0 lordDef me me
  let lord := (g1.battlefield.filter (·.name == "Bear Lord"))[0]!
  let createdOnEnter :=
    (GameEvent.createdEffects g1.events).isEmpty &&
    g1.hasTrample lord
  let n1 := g1.events.size
  let g2 := g1.createEffect (.losesAbilitiesUntilEot lord.id)
  let suppressedWithoutExpiry :=
    (GameEvent.expiredEffects (g2.events.extract n1 g2.events.size)).isEmpty &&
    !(g2.staticAbilities (g2.object! lord.id)).contains (.fra .creaturesYouControlHaveTrample) &&
    !g2.hasTrample (g2.object! lord.id)
  let n2 := g2.events.size
  let g3 := g2.clearEOT
  let resumedWithoutRecreate :=
    (GameEvent.createdEffects (g3.events.extract n2 g3.events.size)).isEmpty &&
    g3.hasTrample (g3.object! lord.id)
  let n3 := g3.events.size
  let (g4, _) := g3.move lord.id (.graveyard me) none
  let noExpireOnLeave :=
    (GameEvent.expiredEffects (g4.events.extract n3 g4.events.size)).isEmpty
  createdOnEnter && suppressedWithoutExpiry && resumedWithoutRecreate && noExpireOnLeave

/- Rule 610 / 400: applications of one-shot effects receive unique `EffectId`s
via `EventCause.oneShotEffect`, whereas non-one-shot `RulesEvent`s
(`.turnBased`, `.stateBased`, `.costPayment`, `.specialAction`, `.gameRule`)
do not mint `EffectId`s. -/
#guard
  let g0 := quiet (addPermanent afterDraw bear me me)
  let b := (g0.battlefield.filter (·.name == "Event Bear"))[0]!
  let effId0 := g0.nextEffectId
  let gNonOneShot :=
    (((g0.gainLife me 3 (cause := some (.turnBased .cleanupClear))).loseLife me 2
      (cause := some (.costPayment .life me))).record
      (GameEvent.tapped g0.turnNumber (g0.snapshot b) true true
        (cause := .turnBased .declareAttackers)))
  let nonOneShotDidNotAdvance :=
    gNonOneShot.nextEffectId == effId0 &&
      (GameEvent.oneShotEffectsWithId gNonOneShot.events).isEmpty
  let g1 := g0.draw me 1 (cause := some (.turnBased .drawStepDraw))
  let g2 := g1.gainLife me 3 (cause := some (.turnBased .cleanupClear))
  let g3 := g2.loseLife me 2 (cause := some (.costPayment .life me))
  let g4 := g3.record (GameEvent.counters g3.turnNumber (some me) (g3.snapshot b) .plusOnePlusOne 2 false
    (cause := .costPayment .removeCounters me))
  let g5 := g4.record (GameEvent.tapped g4.turnNumber (g4.snapshot b) true true
    (cause := .costPayment .tap me))
  let g6 := g5.record (GameEvent.untapped g5.turnNumber (g5.snapshot b)
    (cause := .turnBased .untapAll))
  let g7 := g6.withResolvingContext (some b.id) me (fun g => g.createTreasureTokens me 1)
  let g8 := ((g7.record (GameEvent.looked g7.turnNumber me 2)).record
    (GameEvent.resolved g7.turnNumber me 1 (g7.snapshot b))).record
    (GameEvent.proliferated g7.turnNumber me)
  let appliedWithIds := GameEvent.oneShotEffectsWithId g8.events
  let ids := appliedWithIds.map Prod.fst
  let uniqueIds :=
    Id.run do
      let mut seen : Array EffectId := #[]
      for id in ids do
        if !seen.contains id then
          seen := seen.push id
      return seen.size == ids.size
  let hasDrawMove := g8.events.any (fun e =>
    match e.change with
    | .rules (.zone (.moved _ _ (.library p) (.hand q) (.draw 1 _) (some actor) _ _)) =>
      p == me && q == me && actor == me
    | _ => false)
  let hasToken := g8.events.any (fun e =>
    match e.change with
    | .rules (.zone (.created obj p)) => p == me && obj.token
    | _ => false)
  let hasGain := g8.events.any (fun e => e.change == .rules (.life (.gained me 3)))
  let hasLoss := g8.events.any (fun e => e.change == .rules (.life (.lost me 2 false false)))
  let hasCounters := g8.events.any (fun e =>
    match e.change with
    | .rules (.permanent (.counters (.object obj) .plusOnePlusOne (.put 2) _)) => obj.id == some b.id
    | _ => false)
  let hasTap := g8.events.any (fun e =>
    match e.change with
    | .rules (.permanent (.tapped obj true)) => obj.id == some b.id
    | _ => false)
  let hasUntap := g8.events.any (fun e =>
    match e.change with
    | .rules (.permanent (.untapped obj)) => obj.id == some b.id
    | _ => false)
  nonOneShotDidNotAdvance && uniqueIds && ids.size == 4 &&
    hasDrawMove && hasGain && hasLoss &&
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
  -- Apply two separate pump continuous effects and a non-one-shot life gain without creating any objects.
  let g1 := ((g0.createEffect (.pump b.id 2 2)).gainLife me 4
    (cause := some (.turnBased .cleanupClear))).createEffect (.pump b.id 1 3)
  let objIdUnchanged := g1.nextObjectId == objIdBefore
  let createdPairs := GameEvent.createdEffectsWithId g1.events
  let appliedPairsBeforeToken := GameEvent.oneShotEffectsWithId g1.events
  -- Now create a token (which increments `nextObjectId` via `ZoneEvent.created`) and a one-shot look effect.
  let g2 := (g1.withResolvingContext (some b.id) me (fun g => g.createTreasureTokens me 1)).record
    (GameEvent.looked g1.turnNumber me 1)
  let appliedPairs := GameEvent.oneShotEffectsWithId g2.events
  let objIdIncremented := g2.nextObjectId == objIdBefore + 1
  -- Expire until-end-of-turn continuous effects during cleanup.
  let g3 := g2.clearEOT
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
    g1.nextEffectId == effIdBefore + 2 &&
    createdPairs.size == 2 &&
    appliedPairsBeforeToken.isEmpty &&
    appliedPairs.size == 2 &&
    allDistinct &&
    expiredPairs == createdPairs &&
    g3.pumpOf (g3.object! b.id) == (0, 0) &&
    g3.activeEffects.all (fun (_, e) =>
      match e with
      | .layered (.objects ids) (.ptModify _ _) _ => !ids.contains b.id
      | _ => true)

def opp : PlayerId := ⟨1⟩

/-- Active control-changing effects on `id`. -/
def controlEffectsOn (g : Game) (id : ObjectId) : Array (EffectId × ContinuousEffect) :=
  g.activeEffects.filter (fun (_, e) =>
    match e with
    | .layered (.objects #[oid]) (.control _) _ => oid == id
    | _ => false)

/- Rule 611 / 613.7: expiration removes only the entry recorded under its
`EffectId`, and an id that is not active rolls nothing back. -/
#guard
  let g0 := addPermanent (quiet afterDraw) bear me me
  let b := (g0.battlefield.filter (·.name == "Event Bear"))[0]!
  let pump := ContinuousEffectSpec.pump b.id 3 3
  let g1 := (g0.applyChange (.rules (.continuousEffect (.created ⟨100⟩ pump)))).applyChange
    (.rules (.continuousEffect (.created ⟨101⟩ pump)))
  let g2 := g1.applyChange (.rules (.continuousEffect (.expired ⟨101⟩)))
  let g3 := g2.applyChange (.rules (.continuousEffect (.expired ⟨999⟩)))
  g1.pumpOf (g1.object! b.id) == (6, 6) &&
    g2.pumpOf (g2.object! b.id) == (3, 3) &&
    g2.activeEffects.map Prod.fst == #[⟨100⟩] &&
    g3.pumpOf (g3.object! b.id) == (3, 3) &&
    g3.activeEffects.map Prod.fst == #[⟨100⟩] &&
    g3.nextEffectId == g2.nextEffectId

/- Expiring an effect that is not active records nothing and rolls nothing
back. -/
#guard
  let g0 := quiet (addPermanent afterDraw bear me me)
  let b := (g0.battlefield.filter (·.name == "Event Bear"))[0]!
  let g1 := g0.expireEffect (.cantBlockUntilEot b.id)
  g1.events.size == g0.events.size &&
    g1.nextEffectId == g0.nextEffectId &&
    !g1.cantBlockUntilEot (g1.object! b.id)

/- Expiring one until-end-of-turn keyword grant removes only that grant's
keywords; another grant on the same creature keeps applying. -/
#guard
  let g0 := quiet (addPermanent afterDraw bear me me)
  let b := (g0.battlefield.filter (·.name == "Event Bear"))[0]!
  let g1 := (g0.createEffect (.keywordsUntilEot b.id Keyword.flying)).createEffect
    (.keywordsUntilEot b.id Keyword.haste)
  let g2 := g1.expireEffect (.keywordsUntilEot b.id Keyword.flying)
  g1.currentKeywords (g1.object! b.id) == Keywords.merge Keyword.flying Keyword.haste &&
    g2.currentKeywords (g2.object! b.id) == Keyword.haste

/- A flag set by two continuous effects stays set until both have ended. A
second "loses all abilities" keeps the printed static abilities off. -/
#guard
  let lordDef : CardDef :=
    { bear with
      name := "Bear Lord"
      staticAbilities := #[.fra .creaturesYouControlHaveTrample] }
  let g0 := quiet (addPermanent afterDraw lordDef me me)
  let lord := (g0.battlefield.filter (·.name == "Bear Lord"))[0]!
  let g1 := (g0.createEffect (.cantBlockUntilEot lord.id)).createEffect (.cantBlockUntilEot lord.id)
  let g2 := g1.expireEffect (.cantBlockUntilEot lord.id)
  let g3 := g2.expireEffect (.cantBlockUntilEot lord.id)
  let g4 := (quiet ((g3.createEffect (.losesAbilitiesUntilEot lord.id)).createEffect
    (.losesAbilitiesUntilEot lord.id))).expireEffect (.losesAbilitiesUntilEot lord.id)
  g2.cantBlockUntilEot (g2.object! lord.id) &&
    !g3.cantBlockUntilEot (g3.object! lord.id) &&
    g4.losesAbilitiesUntilEot (g4.object! lord.id) &&
    !(g4.staticAbilities (g4.object! lord.id)).contains (.fra .creaturesYouControlHaveTrample) &&
    !g4.hasTrample (g4.object! lord.id)

/- Effects that used to be written straight onto the status are created as
continuous effects (CR 611.2): Smite-style damage, "can't be blocked this
turn", and an amassed subtype. -/
#guard
  let g0 := quiet (addPermanent afterDraw bear me me)
  let b := (g0.battlefield.filter (·.name == "Event Bear"))[0]!
  let g1 := (g0.dealDamageLoseIndestructibleExileTo b 1 (g0.snapshot b)).grantCantBeBlockedThisTurn b
  let created := GameEvent.createdEffects g1.events
  created.contains (.loseIndestructibleUntilEot b.id) &&
    created.contains (.exileIfDiesUntilEot b.id) &&
    created.contains (.keywordsUntilEot b.id Keyword.cantBeBlocked)

/- Rule 613.7: Mind Control (until the source leaves) then Act of Treason
(until end of turn). Cleanup ends only Treason; Mind Control keeps control
until its source leaves. -/
#guard
  let g0 := quiet (addPermanent (addPermanent afterDraw bear opp opp) hero me me)
  let b := (g0.battlefield.filter (·.name == "Event Bear"))[0]!
  let h := (g0.battlefield.filter (·.name == "Event Hero"))[0]!
  let g1 := g0.changeControl b me (untilSourceLeaves := some h.id)
  let g2 := g1.changeControl (g1.object! b.id) me (untilEot := true)
  let mindControlId := (controlEffectsOn g1 b.id)[0]!.1
  let g3 := (quiet g2).clearEOT
  let g4 := g3.expireWhileSourceEffects h.id
  (controlEffectsOn g2 b.id).size == 2 &&
    g3.controlledBy (g3.object! b.id) me &&
    (controlEffectsOn g3 b.id).map Prod.fst == #[mindControlId] &&
    g3.controlUntilSourceLeaves (g3.object! b.id) == some h.id &&
    g4.controlledBy (g4.object! b.id) opp &&
    (controlEffectsOn g4 b.id).isEmpty

/- Act of Treason then Mind Control: cleanup still ends Treason, and the Aura
leaving later returns the creature to its owner with no control effect left. -/
#guard
  let g0 := quiet (addPermanent (addPermanent afterDraw bear opp opp) hero me me)
  let b := (g0.battlefield.filter (·.name == "Event Bear"))[0]!
  let h := (g0.battlefield.filter (·.name == "Event Hero"))[0]!
  let g1 := g0.changeControl b me (untilEot := true)
  let g2 := g1.changeControl (g1.object! b.id) me (untilSourceLeaves := some h.id)
  let g3 := (quiet g2).clearEOT
  let g4 := g3.expireWhileSourceEffects h.id
  g2.controlUntilEot (g2.object! b.id) &&
    (controlEffectsOn g3 b.id).size == 1 &&
    g3.controlledBy (g3.object! b.id) me &&
    g4.controlledBy (g4.object! b.id) opp &&
    (controlEffectsOn g4 b.id).isEmpty

/- A control effect lasting until the end of its controller's next turn
stays active through the current turn's cleanup and expires in the next
turn's cleanup (Evil's Thrall, CR 611.2a). -/
#guard
  let g0 := quiet (addPermanent afterDraw bear opp opp)
  let b := (g0.battlefield.filter (·.name == "Event Bear"))[0]!
  let g1 := g0.changeControl b me (turnEndsLeft := 2)
  let eid := (controlEffectsOn g1 b.id)[0]!.1
  let g2 := g1.clearEOT
  let g3 := g2.record (GameEvent.turnBegan (g2.turnNumber + 1) me)
  let g4 := g3.clearEOT
  (g2.activeEffect? eid).isSome &&
    g2.controlledBy (g2.object! b.id) me &&
    g2.controlTurnEndsLeft (g2.object! b.id) == 2 &&
    g3.controlTurnEndsLeft (g3.object! b.id) == 1 &&
    (g4.activeEffect? eid).isNone &&
    g4.controlledBy (g4.object! b.id) opp

/- Cleanup does not look up a permanent that ending a control effect exiled
(CR 800.4c). -/
#guard
  let g0 := quiet (addPermanent afterDraw bear opp opp)
  let b := (g0.battlefield.filter (·.name == "Event Bear"))[0]!
  let g1 := (g0.changeControl b me (untilEot := true)).record
    (GameEvent.playerLost g0.turnNumber opp .conceded)
  let g2 := (quiet g1).clearEOT
  (g2.findObject? b.id).isNone &&
    g2.objects.any (fun o => o.name == "Event Bear" && o.zone == .exile)

/- Loki leaving uses `lastKnownBefore?` for his power when his delayed
trigger checks the next instant or sorcery cast, and end of turn expires
unfired Loki delayed triggers (MSH 109 / CR 603.7). -/
#guard
  let g0 := quiet (addPermanent afterDraw bear me me)
  let b := (g0.battlefield.filter (·.name == "Event Bear"))[0]!
  let g0 := g0.createEffect (.pump b.id 2 2)
  let dt : DelayedTrigger :=
    { controller := me
      source := some b
      kind := .lokiCopyNextInstantSorceryThisTurn (some b.id) 0
      cause := .oneShotEffect (some ⟨901⟩) (some b.id) (some me) }
  let g1 := g0.registerDelayedTrigger dt
  let (g2, _) := g1.move b.id (.graveyard me) none
  let lkiPw := (g2.lastKnownBefore? b.id).bind (·.power)
  let (gCast, spell) := g2.allocObject lightningBolt me .stack (some me)
  let gCast := gCast.putStackEntry me spell.id
  let gCast := ((gCast.putCastTriggersOnStack me (gCast.object! spell.id)).receivePriority me).resolveTop
  let copies := gCast.objects.filter (fun o =>
    o.zone == .stack && o.isCopy && o.printed.name == "Lightning Bolt")
  let g3 := g2.clearTurnActivations
  lkiPw == some 4 &&
    copies.size == 1 &&
    gCast.delayedTriggers.isEmpty &&
    g3.delayedTriggers.isEmpty

/- Multiple pending Loki delayed triggers: an opponent's later trigger does
not hide yours, and copying your spell fires only your matching delayed
trigger (MSH 109 / CR 603.7). -/
#guard
  let g0 := quiet (addPermanent afterDraw bear me me)
  let b := (g0.battlefield.filter (·.name == "Event Bear"))[0]!
  let dtMe : DelayedTrigger :=
    { controller := me
      source := some b
      kind := .lokiCopyNextInstantSorceryThisTurn (some b.id) 2
      cause := .oneShotEffect (some ⟨902⟩) (some b.id) (some me) }
  let dtOpp : DelayedTrigger :=
    { controller := opp
      source := none
      kind := .lokiCopyNextInstantSorceryThisTurn none 2
      cause := .oneShotEffect (some ⟨903⟩) none (some opp) }
  let g1 := (g0.registerDelayedTrigger dtMe).registerDelayedTrigger dtOpp
  let (g2, spell) := (quiet g1).allocObject lightningBolt me .stack (some me)
  let g2 := g2.putStackEntry me spell.id
  let g3 := ((g2.putCastTriggersOnStack me (g2.object! spell.id)).receivePriority me).resolveTop
  let copies := g3.objects.filter (fun o =>
    o.zone == .stack && o.isCopy && o.printed.name == "Lightning Bolt")
  copies.size == 1 &&
    g3.delayedTriggers == #[dtOpp]

/- Two pending Loki delayed triggers for the same player both see the next
matching cast: each copies the spell and ends. One whose power is too low
stays pending (MSH 109 / CR 603.7). -/
#guard
  let g0 := quiet afterDraw
  let dt2 : DelayedTrigger :=
    { controller := me, source := none, kind := .lokiCopyNextInstantSorceryThisTurn none 2
      cause := .oneShotEffect (some ⟨904⟩) none (some me) }
  let dt3 : DelayedTrigger :=
    { controller := me, source := none, kind := .lokiCopyNextInstantSorceryThisTurn none 3
      cause := .oneShotEffect (some ⟨905⟩) none (some me) }
  let dt0 : DelayedTrigger :=
    { controller := me, source := none, kind := .lokiCopyNextInstantSorceryThisTurn none 0
      cause := .oneShotEffect (some ⟨906⟩) none (some me) }
  let g1 := ((g0.registerDelayedTrigger dt2).registerDelayedTrigger dt3).registerDelayedTrigger dt0
  let (g2, spell) := (quiet g1).allocObject lightningBolt me .stack (some me)
  let g2 := g2.putStackEntry me spell.id
  let g3 := g2.putCastTriggersOnStack me (g2.object! spell.id)
  let g4 := applyIdle (g3.receivePriority me)
  let g5 := g4.resolveTop.resolveTop.resolveTop
  let copiedCount := (g5.events.filter (fun e =>
    match e.change with
    | .rules (.stackObject (.copied orig _ ctrl)) => orig == spell.id && ctrl == me
    | _ => false)).size
  copiedCount == 2 &&
    g5.delayedTriggers == #[dt0]

/- Stacked copy effects (CR 613.7 / 707): a "copy until this source leaves"
effect followed by a "copy until end of turn" effect reverts to the earlier
copy at cleanup and restores the original card only when the source leaves. -/
#guard
  let giant : CardDef :=
    creature "Event Giant" ManaCost.empty #["Giant"] 4 4
  let g0 := quiet (addPermanent (addPermanent (addPermanent afterDraw bear me me) hero me me) giant me me)
  let b := (g0.battlefield.filter (·.name == "Event Bear"))[0]!
  let h := (g0.battlefield.filter (·.name == "Event Hero"))[0]!
  let gt := (g0.battlefield.filter (·.name == "Event Giant"))[0]!
  let g1 := g0.becomeCopyOf b h (untilSourceLeaves := some h.id)
  let g2 := g1.becomeCopyOf (g1.object! b.id) gt (untilEot := true)
  let g3 := (quiet g2).clearEOT
  let g4 := g3.expireWhileSourceEffects h.id
  g2.name (g2.object! b.id) == "Event Giant" &&
    (g2.object! b.id).printed.name == "Event Bear" &&
    g2.copyUntilEot (g2.object! b.id) &&
    g3.name (g3.object! b.id) == "Event Hero" &&
    !(g3.copyUntilEot (g3.object! b.id)) &&
    g3.copyUntilSourceLeaves (g3.object! b.id) == some h.id &&
    ((g3.copyRestore (g3.object! b.id)).map CardDef.name) == some "Event Bear" &&
    g4.name (g4.object! b.id) == "Event Bear" &&
    (g4.copyRestore (g4.object! b.id)).isNone &&
    (g4.copyUntilSourceLeaves (g4.object! b.id)).isNone

/- A spell cast for its impending cost is still a creature spell on the stack
(ruling 967). The permanent it becomes enters with a `.notACreature`
continuous effect that has its own `EffectId`, expires when all counters are
removed (`withoutCounters`), and is created again with a fresh `EffectId` if
time counters are later moved onto it. A permanent that was not cast for its
impending cost stays a creature and does not lose time counters in the end
step (CR 702.176, ruling 970). -/
#guard
  let impDef : CardDef :=
    { bear with
      name := "Impending Bear"
      impending := some (1, ManaCost.empty) }
  let g0 := addPermanent afterDraw impDef me me
  let copyId := (g0.battlefield.filter (·.name == "Impending Bear"))[0]!.id
  let g0 := insertObject g0 impDef me (.hand me)
  let cardId := ((g0.player me).hand.filter (fun id => (g0.object! id).name == "Impending Bear"))[0]!
  match g0.apply me (.cast cardId) with
  | .error _ => false
  | .ok g0 =>
    let g0 := quiet g0
    let spellId := g0.stack.back!.objectId
    match g0.applyKickerToProposed true with
    | .error _ => false
    | .ok g1 =>
      let (g2, permId) := (quiet g1).move spellId .battlefield (some me)
      let created := GameEvent.createdEffectsWithId g2.events
      match created.find? (fun (_, e) => e == .notACreature permId) with
      | none => false
      | some (eid1, _) =>
        let g3 := g2.removeAllCountersFrom permId
        let g4 := g3.putCountersExceptPlusOne permId { counters := #[(.time, 2)] }
        let created4 := (GameEvent.createdEffectsWithId g4.events).filter (fun (id, e) =>
          id != eid1 && e == .notACreature permId)
        let g5OnStack := (g4.putCountersExceptPlusOne copyId { counters := #[(.time, 2)] }).beginStep .end
        let g5 := g5OnStack.resolveTop
        (GameEvent.createdEffectsWithId g1.events).isEmpty &&
          g1.isCreature (g1.object! spellId) &&
          !g2.wasKicked permId &&
          g2.loggedCastForImpending permId &&
          !g2.loggedCastForImpending copyId &&
          g2.activeEffect? eid1 == some (.notACreature permId) &&
          !g2.isCreature (g2.object! permId) &&
          (GameEvent.expiredEffectsWithId g3.events).map Prod.fst == #[eid1] &&
          (g3.activeEffect? eid1).isNone &&
          g3.isCreature (g3.object! permId) &&
          created4.size == 1 &&
          g4.activeEffect? created4[0]!.1 == some (.notACreature permId) &&
          !g4.isCreature (g4.object! permId) &&
          g5OnStack.stack.size == 1 &&
          (g5OnStack.object! permId).status.time == 2 &&
          g5.stack.isEmpty &&
          (g5.object! permId).status.time == 1 &&
          g5.isCreature (g5.object! copyId) &&
          (g5.object! copyId).status.time == 2

/- Phase 1 isolation: applying a single `PermanentEvent.tapped` or
`PermanentEvent.untapped` event yields the exact tapped state without separate
status setters (CR 701.26a / 701.26b). -/
#guard
  let g0 := quiet (addPermanent afterDraw bear me me)
  let b := (g0.battlefield.filter (·.name == "Event Bear"))[0]!
  let bEv := g0.snapshot b
  let g1 := g0.applyChange (.rules (.permanent (.tapped bEv true)))
  let g2 := g1.applyChange (.rules (.permanent (.untapped bEv)))
  (g1.object! b.id).status == { b.status with tapped := true } &&
    (g2.object! b.id).status == { b.status with tapped := false }

/- Phase 1 isolation: applying a single `PermanentEvent.counters` event puts or
removes counters on a permanent (including poison counters) or counters on a
player (poison and non-poison, CR 122.1). -/
#guard
  let g0 := quiet (addPermanent afterDraw bear me me)
  let b := (g0.battlefield.filter (·.name == "Event Bear"))[0]!
  let bEv := g0.snapshot b
  let g1 := g0.applyChange (.rules (.permanent (.counters (.object bEv) .plusOnePlusOne (.put 3) (some me))))
  let g2 := g1.applyChange (.rules (.permanent (.counters (.object bEv) .plusOnePlusOne (.removed 1) none)))
  let g3 := g2.applyChange (.rules (.permanent (.counters (.player me) .poison (.put 4) (some opp))))
  let g4 := g3.applyChange (.rules (.permanent (.counters (.player me) .poison (.removed 1) none)))
  let g5 := g4.applyChange (.rules (.permanent (.counters (.object bEv) .poison (.put 2) none)))
  let g6 := g5.applyChange (.rules (.permanent (.counters (.object bEv) .poison (.removed 1) none)))
  let g7 := g6.applyChange (.rules (.permanent (.counters (.player me) .charge (.put 3) none)))
  let g8 := g7.applyChange (.rules (.permanent (.counters (.player me) .charge (.removed 1) none)))
  (g1.object! b.id).status == { b.status with counters := #[(.plusOnePlusOne, 3)] } &&
    (g2.object! b.id).status == { b.status with counters := #[(.plusOnePlusOne, 2)] } &&
    (g3.player me) == { (g0.player me) with poison := 4 } &&
    (g4.player me) == { (g0.player me) with poison := 3 } &&
    (g5.object! b.id).status == { b.status with counters := #[(.plusOnePlusOne, 2), (.poison, 2)] } &&
    (g6.object! b.id).status == { b.status with counters := #[(.plusOnePlusOne, 2), (.poison, 1)] } &&
    (g7.player me).counterCount .charge == 3 &&
    (g8.player me).counterCount .charge == 2

/- Phase 1 isolation: applying a single `LifeEvent.gained` or `LifeEvent.lost`
event updates `Player.life` in isolation (CR 119.2 / 119.3). -/
#guard
  let g0 := quiet afterDraw
  let p0 := g0.player me
  let g1 := g0.applyChange (.rules (.life (.gained me 5)))
  let g2 := g1.applyChange (.rules (.life (.lost me 8 true true)))
  (g1.player me) == { p0 with life := p0.life + 5 } &&
    (g2.player me) == { p0 with life := p0.life - 3 }

/- Phase 1 isolation: `DamageEvent.dealt` is a pure fact and writes nothing,
`DamageEvent.marked` and `DamageEvent.markedCleared` update and clear
`Status.damage` in isolation (CR 120.3e / 514.2), and CR 704.5h queries
`DamageEvent.dealt` packets committed since the last SBA check (removing
marked damage does not end the CR 704.5h window). -/
#guard
  let g0 := quiet (addPermanent afterDraw bear me me)
  let b := (g0.battlefield.filter (·.name == "Event Bear"))[0]!
  let dtSource : EventObject := { keywords := { deathtouch := true } }
  let gDealtOnly := g0.record (GameEvent.damaged g0.turnNumber dtSource (g0.snapshot b) 1 false (cause := testCause))
  let g1 := gDealtOnly.applyChange (.rules (.damage (.marked b.id 1)))
  let g2 := g1.applyChange (.rules (.damage (.markedCleared #[b.id])))
  let gDestroyed := g2.checkSBA
  (g0.checkSBA).events.any (·.change == .engine .sbaChecked) &&
    (gDealtOnly.object! b.id).status == b.status &&
    g1.deathtouchDealtSinceLastSba b.id &&
    g2.deathtouchDealtSinceLastSba b.id &&
    (g1.object! b.id).status == { b.status with damage := 1 } &&
    (g2.object! b.id).status == { b.status with damage := 0 } &&
    (gDestroyed.battlefield.filter (·.id == b.id)).isEmpty

/- Phase 1 isolation: applying `PermanentEvent.attached`, `PermanentEvent.unattached`,
Layer 2 `ContinuousEffectSpec.control`, and `PermanentEvent.designation (.goaded byPlayer)`
updates `attachedTo`, `controllerOf`, `controlChanged`, `goaded`, and `goadedBy`
in isolation (CR 701.3 / 110.2 / 613.1b / 701.15b). -/
#guard
  let g0 := quiet (addPermanent (addPermanent afterDraw bear me me) hero me me)
  let b := (g0.battlefield.filter (·.name == "Event Bear"))[0]!
  let h := (g0.battlefield.filter (·.name == "Event Hero"))[0]!
  let bEv := g0.snapshot b
  let hEv := g0.snapshot h
  let g1 := g0.applyChange (.rules (.permanent (.attached hEv b.id none)))
  let g2 := g1.applyChange (.rules (.permanent (.unattached hEv b.id)))
  let g3 := g2.changeControl b opp
  let g4 := g3.changeControl (g3.object! b.id) me
  let g5 := g4.applyChange (.rules (.permanent (.designation bEv (.goaded me) true)))
  let g6 := g5.applyChange (.rules (.permanent (.designation bEv (.goaded opp) true)))
  let g7 := g6.expireGoadedFor me
  let g8 := g7.expireGoadedFor opp
  let heroToPlayer := GameEvent.damagedPlayer 1 hEv opp 2 true (cause := testCause)
  let bearToHero := GameEvent.damaged 1 bEv hEv 2 false (cause := testCause)
  (g1.object! h.id) == { h with attachedTo := some b.id, timestamp := g0.timestamp + 1 } &&
    (g2.object! h.id) == { h with attachedTo := none, timestamp := g0.timestamp + 1 } &&
    (g3.object! b.id) == b &&
    g3.controllerOf (g3.object! b.id) == some opp &&
    g3.controlChanged (g3.object! b.id) &&
    g4.controllerOf (g4.object! b.id) == some me &&
    (g5.object! b.id).status.goaded &&
    (g5.object! b.id).status.goadedBy == #[me] &&
    (g6.object! b.id).status.goaded &&
    (g6.object! b.id).status.goadedBy == #[me, opp] &&
    (g7.object! b.id).status.goaded &&
    (g7.object! b.id).status.goadedBy == #[opp] &&
    !(g8.object! b.id).status.goaded &&
    (g8.object! b.id).status.goadedBy.isEmpty &&
    (let gPerm := (g8.applyChange (.rules (.permanent (.designation bEv (.goaded me false) true)))).expireGoadedFor me
     (gPerm.object! b.id).status.goaded &&
       (gPerm.object! b.id).status.goadedBy == #[me] &&
       (gPerm.object! b.id).status.goadedUntilNextTurnOf.isEmpty) &&
    (let dtCreature : CardDef := { bear with name := "Deathtouch Bear", keywords := Keyword.deathtouch }
     let gDt := quiet (addPermanent afterDraw dtCreature me me)
     let c := (gDt.battlefield.filter (·.name == "Deathtouch Bear"))[0]!
     let gNoDt := gDt.markDamageOn c 1 "1 damage"
     let gWithDt := gDt.markDamageOn c 1 "1 deathtouch damage" (deathtouch := true)
     (gNoDt.events.any fun e =>
       match e.change with
       | .rules (.damage (.dealt pkts)) => pkts.any (·.source.id.isNone)
       | _ => false) &&
       !gNoDt.deathtouchDealtSinceLastSba c.id &&
       gWithDt.deathtouchDealtSinceLastSba c.id) &&
    heroToPlayer.matchesTrigger me h.id .heroesDealDamageToPlayer &&
    !bearToHero.matchesTrigger me h.id .heroesDealDamageToPlayer &&
    !(GameEvent.moved 1 { controller := some me, owner := me, types := #[.creature] }
      .stack .battlefield (cause := testCause)).matchesTrigger me b.id .anotherCreatureYouControlEnters

/- Phase 2 isolation: applying `ZoneEvent.moved`, `ZoneEvent.created`, and
`ZoneEvent.ceasedToExist` via `Game.applyChange` atomically updates `g.objects`,
zone lists (`hand`, `graveyard`, `library`), `nextObjectId`, and `timestamp`
(CR 400.7 / 111.1 / 704.5d). -/
#guard
  let g0 := quiet afterDraw
  let hand0 := (g0.player me).hand
  let cardId := hand0[0]!
  let card := g0.object! cardId
  let nextId0 := g0.nextObjectId
  let ts0 := g0.timestamp
  let newId : ObjectId := ⟨nextId0⟩
  let afterObj : EventObject :=
    { (g0.snapshot card) with
      id := some newId
      zone := .battlefield
      controller := some me
      tapped := true
      counters := #[(.plusOnePlusOne, 2)] }
  let g1 := g0.applyChange (.rules (.zone (.moved
    (g0.snapshot card) afterObj (.hand me) .battlefield
    .put (some me) #[(.plusOnePlusOne, 2)] none)))
  let tokId : ObjectId := ⟨g1.nextObjectId⟩
  let tokSnap : EventObject :=
    { id := some tokId
      name := "Treasure"
      owner := me
      controller := some me
      zone := .battlefield
      token := true
      types := #[.artifact]
      subtypes := #[.treasure]
      tapped := true }
  let g2 := g1.applyChange (.rules (.zone (.created tokSnap me)))
  let g3 := g2.applyChange (.rules (.zone (.ceasedToExist tokSnap)))
  !(g1.player me).hand.contains cardId &&
    (g1.findObject? cardId).isNone &&
    (g1.object! newId).zone == .battlefield &&
    (g1.object! newId).status.tapped &&
    (g1.object! newId).status.plusOnePlusOne == 2 &&
    g1.nextObjectId == nextId0 + 1 &&
    g1.timestamp == ts0 + 1 &&
    (g2.object! tokId).zone == .battlefield &&
    (g2.object! tokId).status.tapped &&
    g2.nextObjectId == nextId0 + 2 &&
    (g3.findObject? tokId).isNone

/- Phase 2 isolation: enters-with counters (planeswalker loyalty, printed +1/+1,
shield, indestructible, Saga first lore counter, and impending time counters)
and enters-tapped status are part of `ZoneEvent.moved.after` and `entersWith`
with zero post-entry counter or tap events, and `GameEvent.countersPut` includes
both `PermanentEvent.counters` and `ZoneEvent.moved.entersWith` (CR 122.6 /
306.5b / 614.1c / 614.12 / 714.3a). -/
#guard
  let tapPlusCreature : CardDef :=
    { bear with
      name := "Tapped Plus Bear"
      entersTapped := true
      entersWithPlusOneCounters := 2
      entersWithShield := 1
      entersWithIndestructibleCounter := true }
  let testPlaneswalker : CardDef :=
    { name := "Test Planeswalker"
      types := #[.planeswalker]
      subtypes := #["Jace"]
      loyalty := some 4 }
  let testSaga : CardDef :=
    { name := "Test Saga"
      types := #[.enchantment]
      subtypes := #["Saga"]
      saga := some {
        sacrificeAfter := "II"
        chapters := #[
          SagaChapter.of "I" "Gain 1 life." (.gainLife 1),
          SagaChapter.of "II" "Gain 2 life." (.gainLife 2)] } }
  let testImpending : CardDef :=
    { bear with
      name := "Impending Bear"
      impending := some (3, ManaCost.ofGeneric 1) }
  let g0 := insertObject (quiet afterDraw) tapPlusCreature me (.hand me)
  let g0 := insertObject g0 testPlaneswalker me (.hand me)
  let g0 := insertObject g0 testSaga me (.hand me)
  let g0 := insertObject g0 testImpending me .stack (some me) { counters := #[(.time, 3)] }
  let cid := ((g0.player me).hand.filter (fun id => (g0.object! id).name == "Tapped Plus Bear"))[0]!
  let pwid := ((g0.player me).hand.filter (fun id => (g0.object! id).name == "Test Planeswalker"))[0]!
  let sagaId := ((g0.player me).hand.filter (fun id => (g0.object! id).name == "Test Saga"))[0]!
  let impId := (g0.objects.filter (fun o => o.name == "Impending Bear" && o.zone == .stack))[0]!.id
  let (g1, permId) := (quiet g0).putOntoBattlefield cid me
  let g1 := g1.afterPermanentEnters (g1.object! permId)
  let (g1, pwPermId) := g1.putOntoBattlefield pwid me
  let g1 := g1.afterPermanentEnters (g1.object! pwPermId)
  let (g1, sagaPermId) := g1.putOntoBattlefield sagaId me
  let g1 := g1.afterPermanentEnters (g1.object! sagaPermId)
  let (g1, impPermId) := g1.putOntoBattlefield impId me
  let g1 := g1.afterPermanentEnters (g1.object! impPermId)
  let moveEvents := g1.events.filterMap (fun e =>
    match e.change with
    | .rules (.zone (.moved before after fromZone toZone _ _ entersWith _)) =>
      some (before, after, fromZone, toZone, entersWith)
    | _ => none)
  let separateCounterEvents := g1.events.filter (fun e =>
    match e.change with
    | .rules (.permanent (.counters _ _ _ _)) => true
    | _ => false)
  let separateTapEvents := g1.events.filter (fun e =>
    match e.change with
    | .rules (.permanent (.tapped _ _)) => true
    | _ => false)
  let putProjection := GameEvent.countersPut g1.events
  let (gTok, pwTok) := (quiet afterDraw).createToken me testPlaneswalker
  let gTok := gTok.afterPermanentEnters (gTok.object! pwTok.id)
  moveEvents.size == 4 &&
    separateCounterEvents.isEmpty &&
    separateTapEvents.isEmpty &&
    (let (_, after, _, toZone, entersWith) := moveEvents[0]!
     toZone == .battlefield &&
       after.tapped &&
       after.counters.count .plusOnePlusOne == 2 &&
       after.counters.count .shield == 1 &&
       after.counters.count .indestructible == 1 &&
       entersWith.count .plusOnePlusOne == 2 &&
       entersWith.count .shield == 1 &&
       entersWith.count .indestructible == 1) &&
    (let (_, after, _, _, entersWith) := moveEvents[1]!
     after.counters.count .loyalty == 4 &&
       entersWith.count .loyalty == 4) &&
    (let (_, after, _, _, entersWith) := moveEvents[2]!
     after.counters.count .lore == 1 &&
       entersWith.count .lore == 1) &&
    (let (_, after, _, _, entersWith) := moveEvents[3]!
     after.counters.count .time == 3 &&
       entersWith.count .time == 3) &&
    (gTok.object! pwTok.id).status.loyaltyCounters == 4 &&
    putProjection.any (fun (o, k, n, _) => o.id == some permId && k == .plusOnePlusOne && n == 2) &&
    putProjection.any (fun (o, k, n, _) => o.id == some permId && k == .shield && n == 1) &&
    putProjection.any (fun (o, k, n, _) => o.id == some permId && k == .indestructible && n == 1) &&
    putProjection.any (fun (o, k, n, _) => o.id == some pwPermId && k == .loyalty && n == 4) &&
    putProjection.any (fun (o, k, n, _) => o.id == some sagaPermId && k == .lore && n == 1) &&
    putProjection.any (fun (o, k, n, _) => o.id == some impPermId && k == .time && n == 3)

/- Phase 2 isolation: `followMoved`, `lastKnownBefore?`, and `lastKnownCounters`
are pure queries over `ZoneEvent.moved` in `g.events`, and `Game.snapshot`
populates characteristics and status on `before` when a permanent leaves the
battlefield (CR 400.7 / 113.7a / 608.2h). Also verifies that a sacrifice
redirected to exile by a replacement effect (CR 614.6 / 701.21a) preserves
`verb == .sacrifice` on the `.exile` move. -/
#guard
  let g0 := quiet (addPermanent afterDraw bear me me)
  let b := (g0.battlefield.filter (·.name == "Event Bear"))[0]!
  let g1 := (g0.addPlusOnePlusOneTo b 2).pumpPermanent (g0.object! b.id) 1 1
  let (g2, gyId) := g1.move b.id (.graveyard me) (verb := some .sacrifice) (actor := some me)
  let (g3, exId) := g2.move gyId .exile none
  let (g4, tok) := (quiet g0).createToken me treasureToken
  let g4 := g4.createEffect (.exileIfDiesUntilEot tok.id)
  let g5 := (quiet g4).sacrificeToGraveyard (g4.object! tok.id) "sacrificed"
  g3.followMoved b.id == exId &&
    g3.lastKnownCounters b.id == #[(.plusOnePlusOne, 2)] &&
    (match g3.lastKnownBefore? b.id with
     | some before =>
       before.name == "Event Bear" &&
         before.zone == .battlefield &&
         before.power == some 5 &&
         before.toughness == some 5 &&
         before.counters.count .plusOnePlusOne == 2
     | none => false) &&
    g2.events.any (fun e =>
      match e.change with
      | .rules (.zone (.moved _ _ .battlefield (.graveyard _) .sacrifice (some actor) _ _)) =>
        actor == me
      | _ => false) &&
    g5.events.any (fun e =>
      match e.change with
      | .rules (.zone (.moved before _ .battlefield .exile .sacrifice _ _ _)) =>
        before.id == some tok.id
      | _ => false) &&
    !g5.events.any (fun e =>
      match e.change with
      | .rules (.zone (.moved _ _ .battlefield (.graveyard _) _ _ _ _)) => true
      | _ => false)

/- Phase 2 isolation: `ZoneEvent.moved` and `ZoneEvent.created` are the sole
writers of the objects they install (preserving full `printed` `CardDef`,
`summoningSick`, `attackingWhom`, `returnedAsArtifact`, `onlyFoodArtifact`,
`wasCast`, and stack-copy metadata), with zero `EngineChange.setObject`
events. -/
#guard
  let g0 := insertObject (quiet afterDraw) bear me (.hand me)
  let cid := ((g0.player me).hand.filter (fun id => (g0.object! id).name == "Event Bear"))[0]!
  let (g1, permId) := (quiet g0).putOntoBattlefield cid me
    (tapped := true) (summoningSick := false)
    (attacking := true) (attackingTarget := some (.player opp))
    (returnedAsArtifact := true) (onlyFoodArtifact := true)
  let (_, tok) := (quiet g1).createToken me treasureToken
    (tapped := true) (attacking := true) (attackingTarget := some (.player opp))
  let perm := g1.object! permId
  perm.status.tapped &&
    !perm.status.summoningSick &&
    perm.status.attacking &&
    perm.status.attackingTarget == some (.player opp) &&
    g1.returnedAsArtifact perm &&
    g1.onlyFoodArtifact perm &&
    !g1.wasCast permId &&
    perm.printed == bear &&
    tok.printed.activatedAbilities.size == treasureToken.activatedAbilities.size &&
    tok.status.attacking &&
    tok.status.attackingTarget == some (.player opp)

/- Phase 3: `PlayerEvent` (`.scried`, `.surveilled`, `.beheld`, `.proliferated`,
`.sheHulkDealtDamage`, `.manaEmptied`, `.lost`, `.leftGame`), `StackObjectEvent`
(`.resolved`), and `PermanentEvent` (`.phasedOut`, `.phasedIn`, `.transformed`,
`.turnedFaceUp`, `.removedFromCombat`) record directly as `RulesEvent`s with
classified `EventCause`s; `applyPlayerEvent` and `applyPermanentEvent` update
game state in isolation; finished scry/surveil/proliferate populate their
chosen piles/targets; a resolving pump has cause `.oneShotEffect`; a cleanup
"this turn" expiry has cause `.turnBased .cleanupClear`; and an effect-behold
(`beholdAndMaybeUntap`) has cause `.oneShotEffect` rather than `.costPayment`
(CR 500.5 / 511.3 / 514.2 / 608 / 610 / 701.22 / 701.25 / 701.27 / 701.34 /
701.4 / 702.26 / 704.5a–c). -/
#guard
  let dfcBear : CardDef :=
    { bear with
      name := "Front Bear"
      otherFace := some { hero with name := "Back Hero" } }
  let g0 := quiet (addPermanent afterDraw dfcBear me me)
  let b := (g0.battlefield.filter (·.name == "Front Bear"))[0]!
  let g1 := g0.beholdQuality me .bear (cause := some (.costPayment .behold me (some b.id)))
  let g2 := g1.phaseOut (g1.object! b.id) (cause := some (.turnBased .phaseInOut))
  let g3 := g2.phaseInControlled me
  let g4 := g3.record (GameEvent.transformed g3.turnNumber (g3.snapshot (g3.object! b.id)) true
    (cause := .oneShotEffect (some ⟨g3.nextEffectId⟩) (some b.id) (some me)))
  let g5 := g4.record (GameEvent.resolved g4.turnNumber me 1 (g4.snapshot (g4.object! b.id)))
  let gPump := (quiet g0).withResolvingContext (some b.id) me (fun g =>
    g.createEffect (.pump b.id 2 2))
  let gCleanup := ((quiet gPump).clearEOT).clearTurnActivations
  let gBeholdEff :=
    ((quiet g0).becomeTapped (g0.object! b.id)
      (cause := some (.oneShotEffect (some ⟨g0.nextEffectId⟩) (some b.id) (some me)))).withResolvingContext
      (some b.id) me (fun g => g.beholdAndMaybeUntap me b.id .bear)
  let gScry0 := (quiet afterDraw).beginScry me 2
  let looked := gScry0.scryLookedIds me 2
  let topChoice := #[looked[0]!]
  let botChoice := #[looked[1]!]
  let gScryDone :=
    match gScry0.finishScry me topChoice botChoice with
    | .ok g => g
    | .error _ => gScry0
  let libAfter := (gScryDone.player me).library
  let gMana := ((quiet afterDraw).addMana me (.colored .red) 2).emptyManaPools
  let gCombat := ((quiet g0).markAttacking b.id).clearCombat
  g1.qualityWasBeheld me .bear &&
    g1.beheldQualities me == #[.bear] &&
    (g2.object! b.id).status.phasedOut &&
    !(g3.object! b.id).status.phasedOut &&
    (g4.object! b.id).status.transformed &&
    (g4.object! b.id).name == "Back Hero" &&
    g5.loggedResolutions me == 1 &&
    gScryDone.loggedScried me &&
    libAfter.back? == some topChoice[0]! &&
    libAfter[0]? == some botChoice[0]! &&
    g1.events.any (fun e =>
      e.change == .rules (.player (.beheld me .bear)) &&
        e.cause? == some (.costPayment .behold me (some b.id))) &&
    g2.events.any (fun e =>
      match e.change with
      | .rules (.permanent (.phasedOut o false)) => o.id == some b.id && e.cause? == some (.turnBased .phaseInOut)
      | _ => false) &&
    g3.events.any (fun e =>
      match e.change with
      | .rules (.permanent (.phasedIn o false)) => o.id == some b.id && e.cause? == some (.turnBased .phaseInOut)
      | _ => false) &&
    gPump.events.any (fun e =>
      match e.change, e.cause? with
      | .rules (.continuousEffect (.created _ (.layered (.objects #[id]) (.ptModify 2 2) .untilEndOfTurn))),
        some (.oneShotEffect _ (some sid) (some ctrl)) =>
        id == b.id && sid == b.id && ctrl == me
      | _, _ => false) &&
    gCleanup.events.any (fun e =>
      match e.change with
      | .rules (.continuousEffect (.expired _)) =>
        e.cause? == some (.turnBased .cleanupClear)
      | _ => false) &&
    gBeholdEff.events.any (fun e =>
      match e.change, e.cause? with
      | .rules (.player (.beheld p .bear)), some (.oneShotEffect _ _ (some ctrl)) =>
        p == me && ctrl == me
      | _, _ => false) &&
    gScryDone.events.any (fun e =>
      match e.change with
      | .rules (.player (.scried p top bottom 2 2)) =>
        p == me && top == topChoice && bottom == botChoice
      | _ => false) &&
    gMana.events.any (fun e =>
      e.change == .rules (.player (.manaEmptied me #[{ mana := .colored .red }, { mana := .colored .red }] false)) &&
        e.cause? == some (.turnBased .emptyManaPools)) &&
    (gMana.player me).manaPool.isEmpty &&
    gCombat.events.any (fun e =>
      match e.change with
      | .rules (.combat (.removedFromCombat o)) =>
        o.id == some b.id && e.cause? == some (.turnBased .removeFromCombatAtEndOfCombat)
      | _ => false) &&
    !(gCombat.object! b.id).status.attacking

/- Phase 3: scry preserves printed `asked` count and resolving spell/ability
controller; proliferate records `PermanentEvent.counters` for non-+1/+1
counters under the proliferate `.oneShotEffect` cause; delayed end-step
triggers retain the source and `EffectId` allocated when the delay was set up;
and `storeCombatAssignments` records `DamageEvent.combatAssigned` under
`.turnBased (.assignCombatDamage _)`. -/
#guard
  let g0 := quiet (addPermanent (addPermanent afterDraw bear me me) hero me me)
  let b := (g0.battlefield.filter (·.name == bear.name))[0]!
  let h := (g0.battlefield.filter (·.name == hero.name))[0]!
  let lib := (g0.player me).library
  let oneCard := lib.extract (lib.size - 1) lib.size
  let gScryOne :=
    (retainLibrary g0 me oneCard).withResolvingContext (some h.id) opp (fun g =>
      g.beginScry me 3)
  let gScryOneDone :=
    match gScryOne.finishScry me oneCard #[] with
    | .ok g => g
    | .error _ => gScryOne
  let gProlif0 :=
    ((quiet g0).recordPutCounters b.id .stun 1).withResolvingContext (some h.id) me (fun g =>
      g.change (.pending (.chooseProliferate me 1)))
  let gProlifDone :=
    match gProlif0.finishProliferate me #[.permanent b.id] with
    | .ok g => g
    | .error _ => gProlif0
  let gBlink :=
    (quiet g0).withResolvingContext (some h.id) me (fun g =>
      g.exileUntilNextEndStep (g.object! b.id))
  let exileCause? : Option EventCause :=
    gBlink.events.findSome? (fun e =>
      match e.change with
      | .rules (.zone (.moved _ _ .battlefield .exile ..)) => e.cause?
      | _ => none)
  let gReturned := ((quiet gBlink).beginStep .end).resolveTop
  let returnCause? : Option EventCause :=
    gReturned.events.findSome? (fun e =>
      match e.change with
      | .rules (.zone (.moved _ _ .exile .battlefield ..)) => e.cause?
      | _ => none)
  let gAssign :=
    match ((quiet g0).markAttacking b.id).storeCombatAssignments true #[] with
    | .ok g => g
    | .error _ => g0
  gScryOneDone.events.any (fun e =>
    match e.change, e.cause? with
    | .rules (.player (.scried p top bottom 1 3)), some (.oneShotEffect _ (some sid) (some ctrl)) =>
      p == me && top == oneCard && bottom.isEmpty && sid == h.id && ctrl == opp
    | _, _ => false) &&
  gProlifDone.events.any (fun e =>
    match e.change, e.cause? with
    | .rules (.permanent (.counters (.object o) .stun (.put 1) (some actor))),
      some (.oneShotEffect _ _ (some ctrl)) =>
      o.id == some b.id && actor == me && ctrl == me
    | _, _ => false) &&
  (match exileCause?, returnCause? with
   | some (.oneShotEffect (some id1) (some sid1) (some ctrl1)),
     some (.oneShotEffect (some id2) (some sid2) (some ctrl2)) =>
     id1 == id2 && sid1 == h.id && sid2 == h.id && ctrl1 == me && ctrl2 == me
   | _, _ => false) &&
  gAssign.events.any (fun e =>
    match e.change with
    | .rules (.combat (.damageAssigned false true _)) =>
      e.cause? == some (.turnBased (.assignCombatDamage false))
    | _ => false)

/- Phase 3: linked-exile returns preserve the exiling one-shot `EventCause`
(CR 610.3); Loki's pending-copy `effectUpdated` uses the move's `happenedCause`;
permanent, Aura, and Adventure spells finish resolving with `.gameRule` causes
(CR 608.3 / 303.4h / 715.3d); and declined crew / boast activations cease with
`.gameRule .reversedActivation` without logging `GameEvent.activated`, while
accepted boast exiles use `.costPayment .exile` (CR 602.2b / 733.1). -/
#guard
  let g0 := quiet (addPermanent (addPermanent afterDraw bear me me) hero me me)
  let b := (g0.battlefield.filter (·.name == bear.name))[0]!
  let h := (g0.battlefield.filter (·.name == hero.name))[0]!
  let (gLink0, sharedCause) := g0.allocDelayedCause (some me) (some h.id)
  let gLink1 := gLink0.exileUntilSourceLeaves (some h.id) b (cause := some sharedCause)
  let effIdAfterExile := gLink1.nextEffectId
  let gLinkReturn :=
    gLink1.withResolvingContext (some b.id) opp (fun g =>
      (g.move h.id (.graveyard me) none).1)
  let linkReturnCause? : Option EventCause :=
    gLinkReturn.events.findSomeRev? (fun e =>
      match e.change with
      | .rules (.zone (.moved _ _ .exile .battlefield ..)) => e.cause?
      | _ => none)
  let lokiInitCause := EventCause.oneShotEffect (some ⟨g0.nextEffectId⟩) (some h.id) (some me)
  let gLoki0 := g0.registerDelayedTrigger
    { controller := me, source := some h, kind := .lokiCopyNextInstantSorceryThisTurn (some h.id) 0, cause := lokiInitCause }
  let destroyCause := EventCause.oneShotEffect (some ⟨gLoki0.nextEffectId⟩) (some b.id) (some opp)
  let (gLokiLeft, _) := (quiet gLoki0).move h.id (.graveyard me) none (cause := some destroyCause)
  let gPermStack :=
    let (g, sid) := (quiet g0).move b.id .stack (some me) (verb := some .cast) (actor := some me)
      (cause := some (.gameRule .spellCast))
    (quiet (g.putStackEntry me sid)).resolveTop
  let vehicleDef : CardDef :=
    { name := "Test Vehicle"
      types := #[.artifact]
      subtypes := #["Vehicle"]
      power := some 4
      toughness := some 4
      crew := some 2
      activatedAbilities := #[ActivatedAbility.crewAbility 2] }
  let gCrew0 := quiet (addPermanent g0 vehicleDef me me)
  let v := (gCrew0.battlefield.filter (·.name == "Test Vehicle"))[0]!
  let gCrewStarted :=
    match gCrew0.activateAbility me v.id 0 with
    | .ok g => g
    | .error _ => gCrew0
  let gCrewUnpayable :=
    (gCrewStarted.becomeTapped (gCrewStarted.object! b.id)).becomeTapped (gCrewStarted.object! h.id)
  let gCrewDeclined :=
    match gCrewUnpayable.answerFraChoice me .decline with
    | .ok g => g
    | .error _ => gCrewUnpayable
  let blackCard : CardDef :=
    { name := "Dark Ritual15"
      manaCost := { symbols := Array.replicate 15 (.colored .black) }
      types := #[.instant] }
  let zemoDef : CardDef :=
    { name := "Baron Helmut Zemo"
      types := #[.creature]
      subtypes := #["Human", "Villain"]
      power := some 3
      toughness := some 3
      staticAbilities := #[.boast] }
  let (gZemo0, gyCardId) :=
    let g := addPermanent g0 blackCard me me
    let c := (g.battlefield.filter (·.name == "Dark Ritual15"))[0]!
    g.move c.id (.graveyard me) none
  let gZemo1 :=
    (addPermanent gZemo0 zemoDef me me).record (GameEvent.stepBegan gZemo0.turnNumber .declareAttackers me)
  let z := (gZemo1.battlefield.filter (·.name == "Baron Helmut Zemo"))[0]!
  let gZemo2 :=
    (quiet gZemo1).record (GameEvent.attackersDeclared gZemo1.turnNumber me #[(gZemo1.snapshot z, .player opp)])
  let gZemoStarted :=
    match gZemo2.activateAbility me z.id 0 with
    | .ok g => g
    | .error _ => gZemo2
  let gZemoAccepted :=
    match gZemoStarted.answerFraChoice me (.objects #[gyCardId]) with
    | .ok g => g
    | .error _ => gZemoStarted
  linkReturnCause? == some sharedCause &&
    gLinkReturn.nextEffectId == effIdAfterExile + 1 &&
    (gLokiLeft.lastKnownBefore? h.id).bind (·.power) == some (g0.power h) &&
    gLokiLeft.delayedTriggers.size == 1 &&
    gPermStack.events.any (fun e =>
      match e.change with
      | .rules (.zone (.moved _ _ .stack .battlefield ..)) =>
        e.cause? == some (EventCause.gameRule .permanentSpellResolved)
      | _ => false) &&
    !gCrewDeclined.events.any (fun e =>
      match e.change with
      | .rules (.cast (.abilityActivated ..)) => true
      | _ => false) &&
    !gCrewDeclined.events.any (fun e =>
      match e.change with
      | .rules (.zone (.ceasedToExist _)) => true
      | _ => false) &&
    gCrewDeclined.stack.isEmpty &&
    gZemoAccepted.events.any (fun e =>
      match e.change, e.cause? with
      | .rules (.zone (.moved _ _ (.graveyard _) .exile ..)), some (.costPayment .exile payer (some _)) =>
        payer == me
      | _, _ => false) &&
    gZemoAccepted.events.any (fun e =>
      match e.change with
      | .rules (.cast (.abilityActivated ..)) => e.cause? == some (EventCause.gameRule .abilityActivated)
      | _ => false)

/- Phase 3: `GameEvent.activated`, loyalty counter costs, and loyalty activation
triggers only fire when activation cost payment completes (`becomeActivated`,
CR 602.2b / 606.4), so reversing a proposed activation before cost payment
finishes (CR 733.1) leaves no `activated` event, loyalty counter cost event, or
waiting triggers; `.transformIncubator` records `PermanentEvent.transformed`
under a `.oneShotEffect` cause (CR 701.27f / 111.10i); and spell/ability
`phaseOut` records `PermanentEvent.phasedOut` under the resolving `.oneShotEffect`
cause without emitting spurious `ContinuousEffectEvent.expired` records for
printed static abilities (CR 702.26b / 702.26f). -/
#guard
  let pwWithMana : CardDef :=
    { name := "Test Planeswalker"
      types := #[.planeswalker]
      activatedAbilities :=
        #[{ cost := { mana := ManaCost.ofGeneric 2, loyalty := some (.plus 1) }
            effect := {} }] }
  let myWatcher : CardDef :=
    { name := "Loyalty Watcher"
      types := #[.enchantment]
      triggeredAbilities :=
        #[TriggeredAbility.fra .youActivateLoyaltyAbility "" (.draw 1),
          TriggeredAbility.fra (.fra .youPutLoyaltyCounters) "" (.draw 1)] }
  let oppWatcher : CardDef :=
    { name := "Opp Loyalty Watcher"
      types := #[.enchantment]
      triggeredAbilities :=
        #[TriggeredAbility.fra (.fra .opponentActivatesLoyaltyAbility) "" (.draw 1)] }
  let gPw0 :=
    let g := addPermanent afterDraw pwWithMana me me
    let pw := (g.battlefield.filter (·.name == "Test Planeswalker"))[0]!
    let g := g.recordPutCounters pw.id .loyalty 3
    let g := addPermanent (addPermanent g myWatcher me me) oppWatcher opp opp
    quiet g
  let pw := (gPw0.battlefield.filter (·.name == "Test Planeswalker"))[0]!
  let gPwProposed :=
    match gPw0.activateAbility me pw.id 0 with
    | .ok g => g
    | .error _ => gPw0
  let proposedAbId := gPwProposed.proposedSpell.get!.spellId
  let gPwReversed := gPwProposed.reverseProposedSpell
  let gPwPaid :=
    match (gPwProposed.addMana me .colorless 2).apply me .pay with
    | .ok g => g
    | .error _ => gPwProposed
  let gPwInGy :=
    ((gPwProposed.addMana me .colorless 2).move pw.id (.graveyard me) none).1
  let gPwInGyPaid :=
    match gPwInGy.apply me .pay with
    | .ok g => g
    | .error _ => gPwInGy
  let baubleDef : CardDef :=
    { name := "Test Bauble"
      types := #[.artifact]
      activatedAbilities :=
        #[{ cost := { mana := ManaCost.ofGeneric 2, sacrificeSource := true }
            effect := {} }] }
  let gWb0 :=
    let g := addPermanent afterDraw baubleDef me me
    let g := g.addMana me .colorless 2
    quiet g
  let wb := (gWb0.battlefield.filter (·.name == "Test Bauble"))[0]!
  let gWbPaid :=
    match gWb0.activateAbility me wb.id 0 with
    | .ok g =>
      match g.apply me .pay with
      | .ok g' => g'
      | .error _ => g
    | .error _ => gWb0
  let incDef : CardDef :=
    { name := "Incubator Token"
      types := #[.artifact]
      subtypes := #["Incubator"]
      otherFace := some
        { name := "Phyrexian"
          types := #[.artifact, .creature]
          subtypes := #["Phyrexian"]
          power := some 0
          toughness := some 0
          isToken := true } }
  let gInc0 := quiet (addPermanent afterDraw incDef me me)
  let inc := (gInc0.battlefield.filter (·.name == "Incubator Token"))[0]!
  let gIncTransformed :=
    gInc0.withResolvingContext (some inc.id) me (fun g =>
      g.applyFrc me default .transformIncubator #[] (some inc.id))
  let incAfter := gIncTransformed.object! inc.id
  let staticCreature : CardDef :=
    { name := "Static Bear"
      types := #[.creature]
      power := some 2
      toughness := some 2
      staticAbilities := #[.boast] }
  let gPhase0 := quiet (addPermanent (addPermanent afterDraw staticCreature me me) hero me me)
  let sb := (gPhase0.battlefield.filter (·.name == "Static Bear"))[0]!
  let h := (gPhase0.battlefield.filter (·.name == hero.name))[0]!
  let gPhasedOut :=
    gPhase0.withResolvingContext (some h.id) me (fun g => g.phaseOut sb)
  let expiredCause? : Option EventCause :=
    gPhasedOut.events.findSome? (fun e =>
      match e.change with
      | .rules (.continuousEffect (.expired _)) => e.cause?
      | _ => none)
  let phasedCause? : Option EventCause :=
    gPhasedOut.events.findSome? (fun e =>
      match e.change with
      | .rules (.permanent (.phasedOut o false)) =>
        if o.id == some sb.id then e.cause? else none
      | _ => none)
  !gPwProposed.loggedActivatedLoyalty me &&
    !gPwReversed.loggedActivatedLoyalty me &&
    gPwProposed.waitingTriggers.isEmpty &&
    gPwReversed.waitingTriggers.isEmpty &&
    gPwReversed.stack.isEmpty &&
    !gPwReversed.loyaltyActivatedThisTurn pw.id &&
    (gPwReversed.object! pw.id).status.loyaltyCounters == 3 &&
    !gPwReversed.log.any (fun s => mentions s "loyalty counter(s)") &&
    !gPwReversed.events.any (fun e =>
      match e.change with
      | .rules (.cast (.abilityActivated ..)) | .rules (.permanent (.counters ..)) => true
      | _ => false) &&
    proposedAbId != pw.id &&
    gPwPaid.events.any (fun e =>
      match e.change, e.cause? with
      | .rules (.permanent (.counters (.object o) .loyalty (.put 1) (some actor))),
        some (.costPayment .loyalty payer (some forId)) =>
        o.id == some pw.id && actor == me && payer == me && forId == proposedAbId
      | _, _ => false) &&
    !gPwInGy.sourceStillPayable gPwInGy.proposedSpell.get! &&
    gPwInGyPaid.stack.isEmpty &&
    !gPwInGyPaid.loggedActivatedLoyalty me &&
    !gPwInGyPaid.events.any (fun e =>
      match e.change with
      | .rules (.cast (.abilityActivated ..)) | .rules (.permanent (.counters ..)) => true
      | _ => false) &&
    gWbPaid.events.any (fun e =>
      match e.change with
      | .rules (.cast (.abilityActivated _ o p (.nonMana none false false false ..))) =>
        p == me && o.id == some wb.id && o.name == "Test Bauble" &&
          e.cause? == some (EventCause.gameRule .abilityActivated)
      | _ => false) &&
    incAfter.status.transformed &&
    incAfter.name == "Phyrexian" &&
    incAfter.printed.power == some 0 &&
    incAfter.printed.toughness == some 0 &&
    gIncTransformed.events.any (fun e =>
      match e.change, e.cause? with
      | .rules (.permanent (.transformed o true)), some (.oneShotEffect _ (some sid) (some ctrl)) =>
        o.id == some inc.id && sid == inc.id && ctrl == me
      | _, _ => false) &&
    (match expiredCause?, phasedCause? with
     | none, some (.oneShotEffect (some _) (some sid) (some ctrl)) =>
       sid == h.id && ctrl == me
     | _, _ => false)

/- Phase 3: `expirePlayPermissions` uses `.turnBased .cleanupClear` when a turn
ends (CR 514.2) and `.turnBased .expireAtStepBegin` when a left player's next
turn would begin (CR 611.2a / 800.4m); Kang's extra-turn `.powerUpsForbiddenThisTurn`
is created under the delayed `.oneShotEffect` cause allocated when `.extraTurn`
resolved (CR 500.7 / 611.2a) and expires under `.turnBased .cleanupClear`
(CR 514.2); `createTreasureTokens` from combat damage to a player or planeswalker
records `ZoneEvent.created` under `.turnBased (.dealCombatDamage false)` (CR 510.2);
`clearCombat` runs at end of combat (`advanceStep`, CR 511.3) while `beginStep .cleanup`
does not emit `removedFromCombat`; multi-permanent `phaseOut` instructions share
one `.oneShotEffect` cause (CR 610.1); and multiple `eaglesAreComing` delays
before the next upkeep keep each batch's delayed `.oneShotEffect` cause (CR 603.7). -/
#guard
  let g0 := quiet (addPermanent (addPermanent afterDraw bear me me) hero me me)
  let b := (g0.battlefield.filter (·.name == bear.name))[0]!
  let h := (g0.battlefield.filter (·.name == hero.name))[0]!
  -- 1. expirePlayPermissions: .cleanupClear at end of turn vs. .expireAtStepBegin in expireUntilNextTurnEffects
  let gPermTurnEnd :=
    (quiet (g0.createEffect (.playPermission b.id { player := me } 1))).startNextTurn
  let gPermNextTurn :=
    (quiet (g0.createEffect (.playPermission b.id { player := opp } 1))).expireUntilNextTurnEffects opp
  -- 2. Kang's extra turn: delayed .oneShotEffect cause on creation, .cleanupClear on expiry
  let effBeforeExtra := g0.nextEffectId
  let gExtraQueued :=
    g0.applyAbilityEffect me { resolution := .extraTurn } #[] (some h.id)
  let storedExtraCause? : Option EventCause :=
    gExtraQueued.events.findSome? (fun e =>
      match e.change with
      | .rules (.turn (.extraTurnAdded _)) => e.cause?
      | _ => none)
  let gExtraStarted := gExtraQueued.startNextTurn
  let gExtraClearedEot := (quiet gExtraStarted).clearEOT
  let gExtraEndedTurn := (quiet gExtraStarted).startNextTurn
  -- 3. Combat-damage Treasure triggers (1 Treasure to player vs Reaver Cleaver `that many` to planeswalker)
  let pwDef : CardDef :=
    { name := "Target PW"
      types := #[.planeswalker]
      loyalty := some 5 }
  let cleaver3Def : CardDef :=
    { name := "Target Cleaver"
      types := #[.artifact]
      subtypes := #["Equipment"]
      staticAbilities := #[.equippedGetsTrampleAndCombatTreasures 1 1] }
  let gTreasPlayer :=
    let g := (g0.markAttacking b.id).createEffect (.combatDamageCreatesTreasureUntilEot b.id)
    let g := g.record (GameEvent.rules g.turnNumber
      (.combat (.damageAssigned false true #[{ source := b.id, toPlayer := 2 }]))
      (.turnBased (.assignCombatDamage false)))
    (((quiet g).dealAssignedCombatDamage).receivePriority me).resolveTop
  let gTreasPw :=
    let g := addPermanent (addPermanent g0 pwDef opp opp) cleaver3Def me me
    let pw := (g.battlefield.filter (·.name == "Target PW"))[0]!
    let clv := (g.battlefield.filter (·.name == "Target Cleaver"))[0]!
    let g := (g.attachSourceTo clv (g.object! b.id)).markAttacking b.id (some (.planeswalker pw.id))
    let g := g.record (GameEvent.rules g.turnNumber
      (.combat (.damageAssigned false true #[{ source := b.id, toPlayer := 2 }]))
      (.turnBased (.assignCombatDamage false)))
    (((quiet g).dealAssignedCombatDamage).receivePriority me).resolveTop
  -- 4. clearCombat: .removeFromCombatAtEndOfCombat in advanceStep from .endOfCombat, none in beginStep .cleanup
  let gEndCombat :=
    (quiet ((g0.record (GameEvent.stepBegan g0.turnNumber .endOfCombat g0.activePlayer)).markAttacking b.id)).advanceStep
  let gCleanupCombat :=
    (quiet (g0.markAttacking b.id)).beginStep .cleanup
  -- 5. Multi-permanent phaseOut shares a single .oneShotEffect id
  let gKickedPhase :=
    (quiet g0).applyUnified me { resolution := .phaseOutKicker } #[Target.player me]
      (kicked := true) (sourceId := some h.id)
  let kickedPhaseCauses :=
    gKickedPhase.events.filterMap (fun e =>
      match e.change with
      | .rules (.permanent (.phasedOut _ false)) => e.cause?
      | _ => none)
  -- 6. Two eaglesAreComing / returnOwnedCreaturesScheduleBirds batches keep distinct delayed causes
  let gEagles1 := g0.returnOwnedCreaturesScheduleBirds me #[b.id]
  let gEagles2 := gEagles1.returnOwnedCreaturesScheduleBirds me #[h.id]
  let causeEagles1 := gEagles2.delayedTriggers[0]!.cause
  let causeEagles2 := gEagles2.delayedTriggers[1]!.cause
  let gEaglesUpkeep :=
    (mustApply ((quiet gEagles2).beginStep .upkeep) me (.stackTriggers #[0, 1])).resolveTop.resolveTop
  gPermTurnEnd.events.any (fun e =>
    match e.change with
    | .rules (.continuousEffect (.expired _)) =>
      e.cause? == some (EventCause.turnBased .cleanupClear)
    | _ => false) &&
    gPermNextTurn.events.any (fun e =>
      match e.change with
      | .rules (.continuousEffect (.expired _)) =>
        e.cause? == some (EventCause.turnBased .expireAtStepBegin)
      | _ => false) &&
    storedExtraCause? == some (EventCause.oneShotEffect (some ⟨effBeforeExtra⟩) (some h.id) (some me)) &&
    gExtraStarted.events.any (fun e =>
      match e.change with
      | .rules (.continuousEffect (.created _ (.gameRule .powerUpsForbidden .untilEndOfTurn))) =>
        e.cause? == storedExtraCause?
      | _ => false) &&
    gExtraClearedEot.events.any (fun e =>
      match e.change with
      | .rules (.continuousEffect (.expired _)) =>
        e.cause? == some (EventCause.turnBased .cleanupClear)
      | _ => false) &&
    gExtraEndedTurn.events.any (fun e =>
      match e.change with
      | .rules (.continuousEffect (.expired _)) =>
        e.cause? == some (EventCause.turnBased .cleanupClear)
      | _ => false) &&
    (gTreasPlayer.battlefield.filter (·.name == "Treasure")).size == 1 &&
    gTreasPlayer.events.any (fun e =>
      match e.change, e.cause? with
      | .rules (.zone (.created o p)), some (.oneShotEffect (some _) (some src) (some ctrl)) =>
        o.name == "Treasure" && p == me && src == b.id && ctrl == me
      | _, _ => false) &&
    (gTreasPw.battlefield.filter (·.name == "Treasure")).size == 2 &&
    gTreasPw.events.any (fun e =>
      match e.change, e.cause? with
      | .rules (.zone (.created o p)), some (.oneShotEffect (some _) (some src) (some ctrl)) =>
        o.name == "Treasure" && p == me && src == b.id && ctrl == me
      | _, _ => false) &&
    gEndCombat.events.any (fun e =>
      match e.change with
      | .rules (.combat (.removedFromCombat o)) =>
        o.id == some b.id && e.cause? == some (EventCause.turnBased .removeFromCombatAtEndOfCombat)
      | _ => false) &&
    !gCleanupCombat.events.any (fun e =>
      match e.change with
      | .rules (.combat (.removedFromCombat _)) => true
      | _ => false) &&
    kickedPhaseCauses.size == 2 &&
    kickedPhaseCauses[0]! == kickedPhaseCauses[1]! &&
    causeEagles1 != causeEagles2 &&
    gEaglesUpkeep.events.any (fun e =>
      match e.change with
      | .rules (.zone (.created o p)) =>
        o.name == "Bird Soldier" && p == me && e.cause? == some causeEagles1
      | _ => false) &&
    gEaglesUpkeep.events.any (fun e =>
      match e.change with
      | .rules (.zone (.created o p)) =>
        o.name == "Bird Soldier" && p == me && e.cause? == some causeEagles2
      | _ => false)

/- Phase 3: `createEffect` and `createEffects` inside a resolving context
allocate a distinct `.oneShotEffect` `EffectId` before assigning each continuous
effect's `EffectId` (CR 610.1 / 611.2a), and `createEffects` shares that one-shot
cause across all effects in the batch; `.exileThenReturnNextEnd` and
`.exileThenReturnYouControl` share one `.oneShotEffect` cause across both targets
(and their returns); `.syntheticDestiny` / `.sunfall` exile all affected
creatures under the single instruction cause (sharing the delayed reveal cause
for `.syntheticDestiny`, CR 603.7 / 610.3), while `.sunfall` incubates with
enters-with +1/+1 counters on `ZoneEvent.created` (without firing creature-only
`.youPutPlusOne` triggers on the noncreature Incubator token) and creates an
Incubator token with `otherFace` that transforms into a 0/0 Phyrexian via
`PermanentEvent.transformed`; `.massPolymorph` uses one shared `exileCause` for
battlefield exiles and one distinct shared `revealCause` across `revealUntil`,
`putHits`, and `restBottom`; and `.venserPerm` shares one cause across both token
creations, both haste continuous effects, and both delayed end-step sacrifices. -/
#guard
  let g0 := quiet (addPermanent (addPermanent afterDraw bear me me) hero me me)
  let b := (g0.battlefield.filter (·.name == bear.name))[0]!
  let h := (g0.battlefield.filter (·.name == hero.name))[0]!
  let srcCard : CardDef :=
    { name := "Source Artifact"
      types := #[.artifact]
      triggeredAbilities := #[.triggered .fromEffect Effect.resourcePlusOneCreateInsectOnce {}] }
  let gWithSrc := quiet (addPermanent g0 srcCard me me)
  let s := (gWithSrc.battlefield.filter (·.name == "Source Artifact"))[0]!
  -- 1. createEffect / createEffects inside resolving context: distinct one-shot vs. continuous EffectIds
  let eff0 := g0.nextEffectId
  let gEffBatch :=
    (quiet g0).withResolvingContext (some h.id) me (fun g =>
      g.createEffects #[.protectionFromEverything me, .lifeCantChange me])
  let createdIds := (GameEvent.createdEffectsWithId gEffBatch.events).map Prod.fst
  let oneShotIds :=
    gEffBatch.events.filterMap (fun e =>
      match e.change with
      | .rules (.continuousEffect (.created ..)) => e.cause?.bind EventCause.oneShotEffectId?
      | _ => none)
  -- 2. .exileThenReturnNextEnd and .exileThenReturnYouControl on two targets
  let twoTargets := #[Target.permanent b.id, Target.permanent h.id]
  let gNextEnd :=
    (quiet gWithSrc).withResolvingContext (some s.id) me (fun g =>
      g.applyUnifiedAbility me Effect.exileThenReturnNextEnd twoTargets
        (sourceId := some s.id))
  let nextEndExileCauses :=
    gNextEnd.events.filterMap (fun e =>
      match e.change with
      | .rules (.zone (.moved _ _ .battlefield .exile ..)) => e.cause?
      | _ => none)
  let gBlinkTwo :=
    (quiet gWithSrc).withResolvingContext (some s.id) me (fun g =>
      g.applyEffect me Effect.exileThenReturnYouControl twoTargets
        (sourceId := some s.id))
  let blinkMoveCauses :=
    gBlinkTwo.events.filterMap (fun e =>
      match e.change with
      | .rules (.zone (.moved ..)) => e.cause?
      | _ => none)
  -- 3. .syntheticDestiny and .sunfall share one cause across all exiled creatures,
  --    and .sunfall records enters-with +1/+1 counters on ZoneEvent.created without
  --    firing creature-only .youPutPlusOne on the noncreature Incubator, and
  --    transforms via otherFace without EngineChange.object (.printed _)
  let gSynth :=
    (quiet gWithSrc).withResolvingContext (some s.id) me (fun g =>
      g.applyFrc me default .syntheticDestiny #[] (some s.id))
  let synthStoredCause := gSynth.delayedTriggers[0]!.cause
  let synthExileCauses :=
    gSynth.events.filterMap (fun e =>
      match e.change with
      | .rules (.zone (.moved _ _ .battlefield .exile ..)) => e.cause?
      | _ => none)
  let gSunfall :=
    (quiet gWithSrc).withResolvingContext (some s.id) me (fun g =>
      g.applyFrc me default .sunfall #[] (some s.id))
  let sunfallExileCauses :=
    gSunfall.events.filterMap (fun e =>
      match e.change with
      | .rules (.zone (.moved _ _ .battlefield .exile ..)) => e.cause?
      | _ => none)
  let sunfallCreated? :=
    gSunfall.events.findSome? (fun e =>
      match e with
      | .rules _ (.zone (.created o p)) c _ =>
        if o.name == "Incubator" && p == me then some (o, c) else none
      | _ => none)
  let sunfallInc := (gSunfall.battlefield.filter (·.name == "Incubator"))[0]!
  let gSunfallTransformed :=
    (quiet gSunfall).withResolvingContext (some sunfallInc.id) me (fun g =>
      g.applyFrc me default .transformIncubator #[] (some sunfallInc.id))
  let sunfallIncAfter := gSunfallTransformed.object! sunfallInc.id
  -- 4. .massPolymorph shares one exileCause for battlefield exiles and one distinct
  --    revealCause across revealUntil, putHits, and restBottom
  let gMassPoly :=
    (quiet gWithSrc).withResolvingContext (some s.id) me (fun g =>
      g.applyFrc me default .massPolymorph #[] (some s.id))
  let polyBfExiles :=
    gMassPoly.events.filterMap (fun e =>
      match e.change with
      | .rules (.zone (.moved _ _ .battlefield .exile ..)) => e.cause?
      | _ => none)
  let polyRevealMoves :=
    gMassPoly.events.filterMap (fun e =>
      match e.change with
      | .rules (.player (.revealed ..))
      | .rules (.zone (.moved _ _ (.library _) .battlefield ..))
      | .rules (.zone (.moved _ _ (.library _) (.library _) ..)) => e.cause?
      | _ => none)
  let polyRestMoves :=
    gMassPoly.events.filterMap (fun e =>
      match e.change with
      | .rules (.zone (.moved _ _ (.library _) (.library _) ..)) => e.cause?
      | _ => none)
  -- 5. .venserPerm shares one cause across both token creations, both haste effects,
  --    and both delayed end-step sacrifices
  let gVenser :=
    (quiet gWithSrc).withResolvingContext (some s.id) me (fun g =>
      g.applyFrc me default .venserPerm #[Target.permanent b.id] (some s.id))
  let venserCreateCauses :=
    gVenser.events.filterMap (fun e =>
      match e.change with
      | .rules (.zone (.created ..)) => e.cause?
      | _ => none)
  let venserEffectCauses :=
    gVenser.events.filterMap (fun e =>
      match e.change with
      | .rules (.continuousEffect (.created ..)) => e.cause?
      | _ => none)
  -- 6. .jhoira shares one cause across revealUntil, putHits, loseLife, and the
  --    deferred RandomRequest.orderInto library return when 2+ cards remain
  let relicDef : CardDef :=
    { name := "Historic Relic"
      types := #[.artifact]
      manaCost := ManaCost.ofGeneric 2 }
  let gJhoiraSetup :=
    let g := addPermanent gWithSrc relicDef me me
    let r := (g.battlefield.filter (·.name == "Historic Relic"))[0]!
    let g := (g.move r.id (.library me) none (libraryPosition := some .top)).1
    let g := (g.move b.id (.library me) none (libraryPosition := some .top)).1
    let g := (g.move h.id (.library me) none (libraryPosition := some .top)).1
    quiet g
  let gJhoiraPending :=
    gJhoiraSetup.withResolvingContext (some s.id) me (fun g =>
      g.applyFrc me default .jhoira #[Target.player me] (some s.id))
  let jhoiraPendingOk :=
    match gJhoiraPending.pending with
    | .resolveRandom (.orderInto ids (.library p) (some _)) => p == me && ids.size == 2
    | _ => false
  let gJhoiraDone :=
    match (gJhoiraPending.change .popContinuationFrame).supplyOrder #[] with
    | .ok g' => g'
    | .error _ => gJhoiraPending
  let jhoiraMoveCauses :=
    gJhoiraDone.events.filterMap (fun e =>
      match e.change with
      | .rules (.zone (.moved ..)) => e.cause?
      | _ => none)
  let jhoiraRestCauses :=
    gJhoiraDone.events.filterMap (fun e =>
      match e.change with
      | .rules (.zone (.moved _ _ (.library _) (.library _) ..)) => e.cause?
      | _ => none)
  let jhoiraLifeCauses :=
    gJhoiraDone.events.filterMap (fun e =>
      match e.change with
      | .rules (.life (.lost _ 2 ..)) => e.cause?
      | _ => none)
  oneShotIds == #[⟨eff0⟩, ⟨eff0⟩] &&
    createdIds == #[⟨eff0 + 1⟩, ⟨eff0 + 2⟩] &&
    nextEndExileCauses.size == 2 &&
    nextEndExileCauses[0]! == nextEndExileCauses[1]! &&
    gNextEnd.delayedTriggers.size == 2 &&
    gNextEnd.delayedTriggers[0]!.cause == nextEndExileCauses[0]! &&
    gNextEnd.delayedTriggers[1]!.cause == nextEndExileCauses[0]! &&
    blinkMoveCauses.size == 4 &&
    blinkMoveCauses.all (· == blinkMoveCauses[0]!) &&
    synthExileCauses.size == 2 &&
    synthExileCauses.all (· == synthStoredCause) &&
    sunfallExileCauses.size == 2 &&
    sunfallExileCauses[0]! == sunfallExileCauses[1]! &&
    (match sunfallCreated? with
     | some (o, incCause) =>
       o.counters == #[(.plusOnePlusOne, 2)] &&
         incCause != sunfallExileCauses[0]! &&
         !gSunfall.events.any (fun e =>
           match e.change with
           | .rules (.permanent (.counters ..)) => true
           | _ => false)
     | none => false) &&
    gSunfall.waitingTriggers.isEmpty &&
    sunfallIncAfter.status.transformed &&
    sunfallIncAfter.name == "Phyrexian" &&
    sunfallIncAfter.printed.power == some 0 &&
    sunfallIncAfter.printed.toughness == some 0 &&
    sunfallIncAfter.status.plusOnePlusOne == 2 &&
    polyBfExiles.size == 2 &&
    polyBfExiles[0]! == polyBfExiles[1]! &&
    polyRestMoves.isEmpty &&
    polyRevealMoves.size == 3 &&
    polyRevealMoves.all (· == polyRevealMoves[0]!) &&
    polyRevealMoves[0]! != polyBfExiles[0]! &&
    venserCreateCauses.size == 2 &&
    venserEffectCauses.size == 2 &&
    gVenser.delayedTriggers.size == 2 &&
    venserCreateCauses.all (· == venserCreateCauses[0]!) &&
    venserEffectCauses.all (· == venserCreateCauses[0]!) &&
    gVenser.delayedTriggers.all (fun dt => dt.cause == venserCreateCauses[0]!) &&
    jhoiraPendingOk &&
    jhoiraMoveCauses.size == 3 &&
    jhoiraRestCauses.size == 2 &&
    jhoiraLifeCauses.size == 1 &&
    jhoiraMoveCauses.all (· == jhoiraMoveCauses[0]!) &&
    jhoiraLifeCauses[0]! == jhoiraMoveCauses[0]!

/- Phase 3: `applyRevealLibrary` (`untilSaga` / `untilCreature` / `resolveRandomCreatureReveal`),
`resolveCascade`, `applyExile` (`.landsYouControl .forLater .lands`, `.nextEndStep`,
`.playUntilNextTurn`, and `.playThisTurn`), `resolveExileTopPlayUntilEndOfNextTurn`,
and `exileTopForPlay` each share one `.oneShotEffect` `EventCause` across all
moves, play-permission `effectCreated` events, and bottom-of-library returns
produced by the single one-shot instruction (CR 610.1 / 701.18 / 702.85a). -/
#guard
  let landDef : CardDef := { name := "Event Forest", types := #[.land], subtypes := #["Forest"] }
  let g0 := addPermanent (addPermanent afterDraw landDef me me) landDef me me
  let lands := g0.battlefield.filter (·.name == "Event Forest")
  let l1 := lands[0]!
  let l2 := lands[1]!
  let g0 := addPermanent (addPermanent g0 bear me me) hero me me
  let b := (g0.battlefield.filter (·.name == bear.name))[0]!
  let h := (g0.battlefield.filter (·.name == hero.name))[0]!
  -- 1. `.landsYouControl .forLater .lands` shares one cause across all exiled lands
  let gLands :=
    (quiet g0).applyExile me default (some b.id) #[Target.permanent l1.id, Target.permanent l2.id]
      .landsYouControl .forLater .lands
  let landExileCauses :=
    gLands.events.filterMap (fun e =>
      match e.change with
      | .rules (.zone (.moved _ _ .battlefield .exile ..)) => e.cause?
      | _ => none)
  -- 2. `applyExile` with `.nextEndStep` on multiple permanents shares one cause
  let gNextEndTrig :=
    (quiet g0).applyExile me default (some b.id) #[Target.permanent b.id, Target.permanent h.id]
      .eachPermanent .nextEndStep .none
  let nextEndTrigCauses :=
    gNextEndTrig.events.filterMap (fun e =>
      match e.change with
      | .rules (.zone (.moved _ _ .battlefield .exile ..)) => e.cause?
      | _ => none)
  -- 3. `applyExile` `.playUntilNextTurn` and `.playThisTurn` share cause between
  --    `ZoneEvent.moved` and `effectCreated (.playPermission ...)`
  let gPlayNext :=
    (quiet g0).applyExile me default (some b.id) #[] .top .playUntilNextTurn .none
  let playNextMoveCauses :=
    gPlayNext.events.filterMap (fun e =>
      match e.change with
      | .rules (.zone (.moved _ _ (.library _) .exile ..)) => e.cause?
      | _ => none)
  let playNextEffCauses :=
    gPlayNext.events.filterMap (fun e =>
      match e.change with
      | .rules (.continuousEffect (.created ..)) => e.cause?
      | _ => none)
  let gPlayThis :=
    (quiet g0).applyExile me default (some b.id) #[] .top .playThisTurn .none
  let playThisMoveCauses :=
    gPlayThis.events.filterMap (fun e =>
      match e.change with
      | .rules (.zone (.moved _ _ (.library _) .exile ..)) => e.cause?
      | _ => none)
  let playThisEffCauses :=
    gPlayThis.events.filterMap (fun e =>
      match e.change with
      | .rules (.continuousEffect (.created ..)) => e.cause?
      | _ => none)
  -- 4. `applyRevealLibrary` `.untilCreature` shares one cause across revealed
  --    non-creature exiles, putting the creature onto the battlefield, and
  --    putting the rest on the bottom of the library (`putRestOnBottomRandom`)
  let gRevSetup :=
    let g := (g0.move b.id (.library me) none (libraryPosition := some .top)).1
    let g := (g.move l1.id (.library me) none (libraryPosition := some .top)).1
    let g := (g.move l2.id (.library me) none (libraryPosition := some .top)).1
    quiet g
  let gRevPending :=
    (gRevSetup.applyRevealLibrary me (some h.id) #[] .untilCreature
      (.ifElse .revealedManaValueAtMostLands
        (.put .revealed .asPrinted .none)
        (.returnToHand .revealed .none))
      .you).getD gRevSetup
  let gRevDone :=
    match (gRevPending.change .popContinuationFrame).supplyOrder #[] with
    | .ok g' => g'
    | .error _ => gRevPending
  let revMoveCauses :=
    gRevDone.events.filterMap (fun e =>
      match e.change with
      | .rules (.zone (.moved ..)) => e.cause?
      | _ => none)
  -- 5. `resolveCascade` + `.mayCastCascade` `.decline` shares one cause across
  --    exiling from library and returning the exiled cards to the bottom
  let gCascPending := gRevSetup.resolveCascade me 3
  let gCascChoice :=
    match gCascPending.answerFraChoice me .decline with
    | .ok g' => g'
    | .error _ => gCascPending
  let gCascDone :=
    match (gCascChoice.change .popContinuationFrame).supplyOrder #[] with
    | .ok g' => g'
    | .error _ => gCascChoice
  let cascMoveCauses :=
    gCascDone.events.filterMap (fun e =>
      match e.change with
      | .rules (.zone (.moved ..)) => e.cause?
      | _ => none)
  landExileCauses.size == 2 &&
    landExileCauses[0]! == landExileCauses[1]! &&
    nextEndTrigCauses.size == 2 &&
    nextEndTrigCauses[0]! == nextEndTrigCauses[1]! &&
    gNextEndTrig.delayedTriggers.size == 2 &&
    gNextEndTrig.delayedTriggers.all (fun dt => dt.cause == nextEndTrigCauses[0]!) &&
    playNextMoveCauses.size == 1 &&
    playNextEffCauses.size == 1 &&
    playNextMoveCauses[0]! == playNextEffCauses[0]! &&
    playThisMoveCauses.size == 1 &&
    playThisEffCauses.size == 1 &&
    playThisMoveCauses[0]! == playThisEffCauses[0]! &&
    revMoveCauses.size == 3 &&
    revMoveCauses.all (· == revMoveCauses[0]!) &&
    cascMoveCauses.size == 6 &&
    cascMoveCauses.all (· == cascMoveCauses[0]!)

/- Phase 3: `.mayRevealToHand` (`anyOrder := true`) + `.orderLibraryBottom`,
`.nickFuryPut` + `.nickFuryMayTransform` `.accept`,
`grimaExileUntilInstantOrSorcery` (`castTheCard := true`),
generic `TriggerResolution.revealLibrary` (`applyRevealLibrary == none`), and
`exileTopPlayIfYouControlSubtype` each share a single `.oneShotEffect` cause
across all constituent moves, transforms, and continuous-effect creations
(CR 608.2c / 610.1 / 701.18 / 701.27a). -/
#guard
  let landDef : CardDef :=
    { name := "Test Plains", types := #[.land], subtypes := #["Plains"] }
  let dfcHero : CardDef :=
    { hero with
      name := "Front Hero"
      otherFace := some { bear with name := "Back Bear" } }
  let shockDef : CardDef :=
    { name := "Test Shock", manaCost := ManaCost.ofGeneric 2, types := #[.instant] }
  let g0 :=
    quiet (addPermanent (addPermanent (addPermanent (addPermanent afterDraw bear me me) hero me me)
      landDef me me) landDef me me)
  let bs := g0.battlefield.filter (·.name == bear.name)
  let hs := g0.battlefield.filter (·.name == hero.name)
  let ls := g0.battlefield.filter (·.name == "Test Plains")
  let b := bs[0]!
  let h := hs[0]!
  let l1 := ls[0]!
  let l2 := ls[1]!
  let gLibSetup :=
    let g := (g0.move b.id (.library me) none (libraryPosition := some .top)).1
    let g := (g.move l1.id (.library me) none (libraryPosition := some .top)).1
    let g := (g.move l2.id (.library me) none (libraryPosition := some .top)).1
    quiet g
  -- 1. `.mayRevealToHand` (`anyOrder := true`) + `.orderLibraryBottom`
  let gMayRev0 :=
    gLibSetup.withResolvingContext (some h.id) me (fun g =>
      g.beginLookRevealToHand me 3 (fun _ => true) true)
  let looked3 := gLibSetup.scryLookedIds me 3
  let picked := looked3[0]!
  let rest2 := looked3.filter (· != picked)
  let gMayRev1 :=
    match gMayRev0.answerFraChoice me (.objects #[picked]) with
    | .ok g' => g'
    | .error _ => gMayRev0
  let gMayRevDone :=
    match gMayRev1.answerFraChoice me (.objects rest2.reverse) with
    | .ok g' => g'
    | .error _ => gMayRev1
  let mayRevCauses :=
    gMayRevDone.events.filterMap (fun e =>
      match e.change with
      | .rules (.zone (.moved ..)) => e.cause?
      | _ => none)
  -- 2. `.nickFuryPut` + `.nickFuryMayTransform` `.accept`
  let gNick0 := addPermanent g0 dfcHero me me
  let dfcObj := (gNick0.battlefield.filter (·.name == "Front Hero"))[0]!
  let gNickSetup :=
    let g := (gNick0.move l1.id (.library me) none (libraryPosition := some .top)).1
    let g := (g.move l2.id (.library me) none (libraryPosition := some .top)).1
    let g := (g.move dfcObj.id (.library me) none (libraryPosition := some .top)).1
    quiet g
  let dfcLibId := (gNickSetup.player me).library.back!
  let gNick1 :=
    gNickSetup.withResolvingContext (some h.id) me (fun g =>
      g.beginLookPutTypes me 3 #[.hero])
  let gNick2 :=
    match gNick1.answerFraChoice me (.objects #[dfcLibId]) with
    | .ok g' => g'
    | .error _ => gNick1
  let gNick3 :=
    match gNick2.answerFraChoice me .accept with
    | .ok g' => g'
    | .error _ => gNick2
  let gNickDone :=
    match gNick3.supplyOrder #[] with
    | .ok g' => g'
    | .error _ => gNick3
  let nickCauses :=
    gNickDone.events.filterMap (fun e =>
      match e.change with
      | .rules (.zone (.moved ..)) => e.cause?
      | .rules (.permanent (.transformed ..)) => e.cause?
      | _ => none)
  -- 3. `grimaExileUntilInstantOrSorcery` with `castTheCard := true`
  let gGrima0 :=
    insertObject g0 shockDef me (.library me)
  let gGrimaSetup :=
    let g := (gGrima0.move l1.id (.library me) none (libraryPosition := some .top)).1
    let g := (g.move l2.id (.library me) none (libraryPosition := some .top)).1
    quiet g
  let gGrimaPending :=
    gGrimaSetup.withResolvingContext (some h.id) me (fun g =>
      g.grimaExileUntilInstantOrSorcery me me true)
  let gGrimaDeclined :=
    match gGrimaPending.answerFraChoice me .decline with
    | .ok g' => g'
    | .error _ => gGrimaPending
  let gGrimaDone :=
    match gGrimaDeclined.supplyOrder #[] with
    | .ok g' => g'
    | .error _ => gGrimaDeclined
  let grimaCauses :=
    gGrimaDone.events.filterMap (fun e =>
      match e.change with
      | .rules (.zone (.moved ..)) => e.cause?
      | _ => none)
  -- 4. Generic `TriggerResolution.revealLibrary` (`applyRevealLibrary == none`)
  let gTrigRevPending :=
    gLibSetup.withResolvingContext (some h.id) me (fun g =>
      g.applyTriggeredAbility me (.onEnterDraw 1) (some h.id) #[] #[] none none "This creature"
        (some (.revealLibrary .untilCreature (.put .revealed .asPrinted .none) .you)))
  let gTrigRevDone :=
    match gTrigRevPending.supplyOrder #[] with
    | .ok g' => g'
    | .error _ => gTrigRevPending
  let trigRevCauses :=
    gTrigRevDone.events.filterMap (fun e =>
      match e.change with
      | .rules (.zone (.moved ..)) => e.cause?
      | _ => none)
  -- 5. `exileTopPlayIfYouControlSubtype` while resolving
  let gExTop :=
    gLibSetup.withResolvingContext (some h.id) me (fun g =>
      g.exileTopPlayIfYouControlSubtype me 2 .hero)
  let exTopCauses :=
    gExTop.events.filterMap (fun e =>
      match e.change with
      | .rules (.zone (.moved ..)) => e.cause?
      | .rules (.continuousEffect (.created _ (.permission _ (.playFromExile ..) _))) => e.cause?
      | _ => none)
  -- 6. `exileHandDrawPlayUntilNext` shares one cause across hand exiles, play permissions, and draws
  let handSize := (gLibSetup.player me).hand.size
  let gHex :=
    gLibSetup.withResolvingContext (some h.id) me (fun g =>
      g.exileHandDrawPlayUntilNext me)
  let hexCauses :=
    gHex.events.filterMap (fun e =>
      match e.change with
      | .rules (.zone (.moved ..)) => e.cause?
      | .rules (.continuousEffect (.created _ (.permission _ (.playFromExile ..) _))) => e.cause?
      | _ => none)
  -- 7. `.identityEcho` uses one cause for the exile and a distinct shared cause for the reveal/put/bottom
  let gEchoPending :=
    gLibSetup.withResolvingContext (some h.id) me (fun g =>
      g.applyFraAbility me { targeting := .of .creatureYouControl } .identityEcho #[.permanent h.id] (some h.id))
  let gEchoDone :=
    match gEchoPending.supplyOrder #[] with
    | .ok g' => g'
    | .error _ => gEchoPending
  let echoMoveCauses :=
    gEchoDone.events.filterMap (fun e =>
      match e.change with
      | .rules (.zone (.moved ..)) => e.cause?
      | _ => none)
  -- 8. `millThenChooseForHand` shares one cause across the mill and deferred `.chooseCards` `.toHand`,
  --    and only offers cards actually milled from the library even when `n` exceeds `library.size`
  let gShortLib :=
    let g := emptyLibrary g0 me
    let (g, gyLandId) := g.move l1.id (.graveyard me) none
    let g := (g.move b.id (.library me) none (libraryPosition := some .top)).1
    let g := (g.move l2.id (.library me) none (libraryPosition := some .top)).1
    (quiet g, gyLandId)
  let preExistingGyLand := gShortLib.2
  let gMillChoose0 :=
    gShortLib.1.withResolvingContext (some h.id) me (fun g =>
      g.millThenChooseForHand me 4 (fun o => o.printed.isLand) 2 false)
  let offeredIds :=
    match gMillChoose0.pending with
    | .fraChoice _ (.chooseCards ids _ _) => ids
    | _ => #[]
  let gMillChooseDone :=
    match gMillChoose0.answerFraChoice me (.objects offeredIds) with
    | .ok g' => g'
    | .error _ => gMillChoose0
  let millChooseCauses :=
    gMillChooseDone.events.filterMap (fun e =>
      match e.change with
      | .rules (.zone (.moved ..)) => e.cause?
      | _ => none)
  -- 9. `draw` and `mill` outside a resolving context record classified non-one-shot causes without
  --    bumping `nextEffectId`, while `drawThenLoseLife`, `drawEqualToughnessThenPutCreatures`,
  --    `.twoPlayersDraw`, `millCollected` / `.milledSubtype`, and `.palantirMayDraw` `.decline`
  --    share one `.oneShotEffect` cause across each instruction
  let gRawDraw := gLibSetup.draw me 2
  let rawDrawCauses :=
    gRawDraw.events.filterMap (fun e =>
      match e.change with
      | .rules (.zone (.moved ..)) => e.cause?
      | _ => none)
  let gRawMill := gLibSetup.mill me 2
  let rawMillCauses :=
    gRawMill.events.filterMap (fun e =>
      match e.change with
      | .rules (.zone (.moved ..)) => e.cause?
      | _ => none)
  let gDrawLose :=
    gLibSetup.withResolvingContext (some h.id) me (fun g =>
      g.drawThenLoseLife me 2 2)
  let drawLoseCauses :=
    gDrawLose.events.filterMap (fun e =>
      match e.change with
      | .rules (.zone (.moved ..)) => e.cause?
      | .rules (.life (.lost ..)) => e.cause?
      | _ => none)
  let gLastMarchSetup :=
    let g := (g0.move l1.id (.library me) none (libraryPosition := some .top)).1
    let g := (g.move l2.id (.library me) none (libraryPosition := some .top)).1
    let g := (g.move b.id (.library me) none (libraryPosition := some .top)).1
    quiet g
  let gLastMarch0 :=
    gLastMarchSetup.withResolvingContext (some h.id) me (fun g =>
      g.applyEffect me Effect.drawEqualToughnessThenPutCreatures #[] (sourceId := some h.id))
  let lastMarchOffered :=
    match gLastMarch0.pending with
    | .fraChoice _ (.chooseCards ids _ .creaturesToBattlefield) => ids
    | _ => #[]
  let gLastMarchDone :=
    match gLastMarch0.answerFraChoice me (.objects lastMarchOffered) with
    | .ok g' => g'
    | .error _ => gLastMarch0
  let lastMarchCauses :=
    gLastMarchDone.events.filterMap (fun e =>
      match e.change with
      | .rules (.zone (.moved ..)) => e.cause?
      | _ => none)
  let gTwoDraw :=
    gLibSetup.withResolvingContext (some h.id) me (fun g =>
      g.applyAbilityEffect me { resolution := .twoPlayersDraw } #[Target.player me, Target.player opp] (sourceId := some h.id))
  let twoDrawCauses :=
    gTwoDraw.events.filterMap (fun e =>
      match e.change with
      | .rules (.zone (.moved ..)) => e.cause?
      | _ => none)
  let gMillSubtype :=
    gLibSetup.withResolvingContext (some h.id) me (fun g =>
      g.applyTriggeredAbility me (.onEnterMillThenSubtypeToHand 3 "Bear") (some h.id) #[] #[] none none "This creature"
        (some (.sequence [.mill (.fixed 3) .you .milledCards, .returnToHand (.milledSubtype .bear)])))
  let millSubtypeCauses :=
    gMillSubtype.events.filterMap (fun e =>
      match e.change with
      | .rules (.zone (.moved ..)) => e.cause?
      | _ => none)
  let gPalantir0 :=
    (gGrimaSetup.recordPutCounters h.id .influence 3).change (.pending (.fraChoice opp (.palantirMayDraw me h.id)))
      |>.change (.pushContinuationFrame { resolvingContext := some (some h.id, me) })
  let gPalantirDone :=
    match gPalantir0.answerFraChoice opp .decline with
    | .ok g' => g'
    | .error _ => gPalantir0
  let palantirCauses :=
    gPalantirDone.events.filterMap (fun e =>
      match e.change with
      | .rules (.zone (.moved ..)) => e.cause?
      | .rules (.life (.lost ..)) => e.cause?
      | _ => none)
  let gPalantirRaw0 :=
    (gGrimaSetup.recordPutCounters h.id .influence 3).change (.pending (.fraChoice opp (.palantirMayDraw me h.id)))
  let gPalantirRawDone :=
    match gPalantirRaw0.answerFraChoice opp .decline with
    | .ok g' => g'
    | .error _ => gPalantirRaw0
  let palantirRawCauses :=
    gPalantirRawDone.events.filterMap (fun e =>
      match e.change with
      | .rules (.zone (.moved ..)) => e.cause?
      | .rules (.life (.lost ..)) => e.cause?
      | _ => none)
  let balinSeq : TriggeredAbility.TriggerResolution :=
    .sequence [.may (.discard .hand) (.sequence []), .draw .discardedHand]
  let gBalinRaw0 :=
    gLibSetup.change (.pending (.fraChoice me (.mayDiscardHandBalin (some h.id))))
  let gBalinRaw :=
    match gBalinRaw0.answerFraChoice me .accept with
    | .ok g' => g'
    | .error _ => gBalinRaw0
  let balinRawCauses :=
    gBalinRaw.events.filterMap (fun e =>
      match e.change with
      | .rules (.zone (.moved ..)) => e.cause?
      | _ => none)
  let gBalinRes0 :=
    gLibSetup.withResolvingContext (some h.id) me (fun g =>
      g.applyTriggeredAbility me (.onEnterDraw 1) (some h.id)
        (resolutionOverride := some balinSeq))
  let gBalinRes :=
    match gBalinRes0.answerFraChoice me .accept with
    | .ok g' => g'
    | .error _ => gBalinRes0
  let balinResCauses :=
    gBalinRes.events.filterMap (fun e =>
      match e.change with
      | .rules (.zone (.moved ..)) => e.cause?
      | _ => none)
  let gArmorEmpty0 :=
    (emptyLibrary gLibSetup me).change (.pending (.fraChoice me (.mayDrawThenEachOpponentDraws 1)))
      |>.change (.pushContinuationFrame { resolvingContext := some (some h.id, me) })
  let gArmorEmptyDone :=
    match gArmorEmpty0.answerFraChoice me .accept with
    | .ok g' => g'
    | .error _ => gArmorEmpty0
  let armorEmptyMoves :=
    gArmorEmptyDone.events.filterMap (fun e =>
      match e.change with
      | .rules (.zone (.moved ..)) => e.cause?
      | _ => none)
  let lifelinkHero : CardDef :=
    { hero with name := "Lifelink Hero", keywords := Keyword.lifelink }
  let gDmgSetup0 := addPermanent (addPermanent g0 lifelinkHero me me) bear opp opp
  let lh := (gDmgSetup0.battlefield.filter (·.name == "Lifelink Hero"))[0]!
  let oppBear := (gDmgSetup0.battlefield.filter (fun o => o.name == bear.name && o.controlledBy opp))[0]!
  let gDmgSetup := quiet gDmgSetup0
  let gDmgPermRaw := gDmgSetup.dealDamageFrom lh.name oppBear 1 (source := some lh)
  let dmgPermRawCauses :=
    gDmgPermRaw.events.filterMap (fun e =>
      match e.change with
      | .rules _ => e.cause?
      | _ => none)
  let gDmgPermRes :=
    gDmgSetup.withResolvingContext (some lh.id) me (fun g =>
      g.dealDamageFrom lh.name oppBear 1 (source := some lh))
  let dmgPermResCauses :=
    gDmgPermRes.events.filterMap (fun e =>
      match e.change with
      | .rules _ => e.cause?
      | _ => none)
  let gDmgPlayerRaw := gDmgSetup.dealDamageToPlayer opp 2 (source := some lh)
  let dmgPlayerRawCauses :=
    gDmgPlayerRaw.events.filterMap (fun e =>
      match e.change with
      | .rules _ => e.cause?
      | _ => none)
  let gDmgPlayerRes :=
    gDmgSetup.withResolvingContext (some lh.id) me (fun g =>
      g.dealDamageToPlayer opp 2 (source := some lh))
  let dmgPlayerResCauses :=
    gDmgPlayerRes.events.filterMap (fun e =>
      match e.change with
      | .rules _ => e.cause?
      | _ => none)
  let gSweepRes :=
    gDmgSetup.withResolvingContext (some lh.id) me (fun g =>
      g.applyTriggeredAbility me (.onEnterDraw 1) (some lh.id)
        (resolutionOverride := some (.dealDamage (.fixed 1) (.eachNonSubtypeAndOpponents .dragon))))
  let sweepResCauses :=
    gSweepRes.events.filterMap (fun e =>
      match e.change with
      | .rules _ => e.cause?
      | _ => none)
  let gNivRaw := gDmgSetup.applyFrc me default .nivPay #[] (some lh.id) (lastKnownPower := some 2)
  let nivRawCauses :=
    gNivRaw.events.filterMap (fun e =>
      match e.change with
      | .rules _ => e.cause?
      | _ => none)
  let gNivRes :=
    gDmgSetup.withResolvingContext (some lh.id) me (fun g =>
      g.applyFrc me default .nivPay #[] (some lh.id) (lastKnownPower := some 2))
  let nivResCauses :=
    gNivRes.events.filterMap (fun e =>
      match e.change with
      | .rules _ => e.cause?
      | _ => none)
  let gNivLocked :=
    quiet (gDmgSetup.createEffect (.lifeCantChange me))
      |>.withResolvingContext (some lh.id) me (fun g =>
        g.applyFrc me default .nivPay #[] (some lh.id) (lastKnownPower := some 2))
  let nivLockedEvents :=
    gNivLocked.events.filterMap (fun e =>
      match e.change with
      | .rules _ => e.cause?
      | _ => none)
  let gDreadRaw := gDmgSetup.applyFrc me default .dreadUpkeep #[] (some lh.id)
  let dreadRawCauses :=
    gDreadRaw.events.filterMap (fun e =>
      match e.change with
      | .rules _ => e.cause?
      | _ => none)
  let gDreadRes :=
    gDmgSetup.withResolvingContext (some lh.id) me (fun g =>
      g.applyFrc me default .dreadUpkeep #[] (some lh.id))
  let dreadResCauses :=
    gDreadRes.events.filterMap (fun e =>
      match e.change with
      | .rules _ => e.cause?
      | _ => none)
  let gSkrelvRaw := gDmgSetup.applyFrc me default .skrelv #[] (some lh.id)
  let skrelvRawCauses :=
    gSkrelvRaw.events.filterMap (fun e =>
      match e.change with
      | .rules _ => e.cause?
      | _ => none)
  let gSkrelvRes :=
    gDmgSetup.withResolvingContext (some lh.id) me (fun g =>
      g.applyFrc me default .skrelv #[] (some lh.id))
  let skrelvResCauses :=
    gSkrelvRes.events.filterMap (fun e =>
      match e.change with
      | .rules _ => e.cause?
      | _ => none)
  let gDrainPlanRaw :=
    gDmgSetup.applyTriggeredAbility me (.onVillainYouControlEntersDrainAndPlan 2) (some lh.id)
  let drainPlanRawCauses :=
    gDrainPlanRaw.events.filterMap (fun e =>
      match e.change with
      | .rules _ => e.cause?
      | _ => none)
  let gDrainPlanRes :=
    gDmgSetup.withResolvingContext (some lh.id) me (fun g =>
      g.applyTriggeredAbility me (.onVillainYouControlEntersDrainAndPlan 2) (some lh.id))
  let drainPlanResCauses :=
    gDrainPlanRes.events.filterMap (fun e =>
      match e.change with
      | .rules _ => e.cause?
      | _ => none)
  let isClassifiedNonOneShot (c : EventCause) : Bool :=
    c.oneShotEffectId?.isNone &&
      match c with
      | .oneShotEffect none _ _ => false
      | _ => true
  mayRevCauses.size == 3 &&
    mayRevCauses.all (· == mayRevCauses[0]!) &&
    nickCauses.size == 4 &&
    nickCauses.all (· == nickCauses[0]!) &&
    grimaCauses.size == 6 &&
    grimaCauses.all (· == grimaCauses[0]!) &&
    trigRevCauses.size == 3 &&
    trigRevCauses.all (· == trigRevCauses[0]!) &&
    exTopCauses.size == 4 &&
    exTopCauses.all (· == exTopCauses[0]!) &&
    handSize > 0 &&
    hexCauses.size == handSize * 3 &&
    hexCauses.all (· == hexCauses[0]!) &&
    echoMoveCauses.size == 4 &&
    echoMoveCauses[0]! != echoMoveCauses[1]! &&
    echoMoveCauses[1]! == echoMoveCauses[2]! &&
    echoMoveCauses[2]! == echoMoveCauses[3]! &&
    offeredIds.size == 1 &&
    !offeredIds.contains preExistingGyLand &&
    millChooseCauses.size == 3 &&
    millChooseCauses.all (· == millChooseCauses[0]!) &&
    rawDrawCauses.size == 2 &&
    rawDrawCauses.all isClassifiedNonOneShot &&
    gRawDraw.nextEffectId == gLibSetup.nextEffectId &&
    rawMillCauses.size == 2 &&
    rawMillCauses.all isClassifiedNonOneShot &&
    gRawMill.nextEffectId == gLibSetup.nextEffectId &&
    drawLoseCauses.size == 3 &&
    drawLoseCauses.all (· == drawLoseCauses[0]!) &&
    (match drawLoseCauses[0]! with | .oneShotEffect (some _) (some _) (some _) => true | _ => false) &&
    !lastMarchOffered.isEmpty &&
    lastMarchCauses.size >= 3 &&
    lastMarchCauses.all (· == lastMarchCauses[0]!) &&
    twoDrawCauses.size == 2 &&
    twoDrawCauses[0]! == twoDrawCauses[1]! &&
    millSubtypeCauses.size == 4 &&
    millSubtypeCauses.all (· == millSubtypeCauses[0]!) &&
    palantirCauses.size == 4 &&
    palantirCauses.all (· == palantirCauses[0]!) &&
    palantirRawCauses.size == 4 &&
    palantirRawCauses.all isClassifiedNonOneShot &&
    gPalantirRawDone.nextEffectId == gPalantirRaw0.nextEffectId &&
    balinRawCauses.size == handSize &&
    balinRawCauses.all isClassifiedNonOneShot &&
    gBalinRaw.nextEffectId == gBalinRaw0.nextEffectId &&
    balinResCauses.size == handSize * 2 &&
    (balinResCauses.extract 0 handSize).all (· == balinResCauses[0]!) &&
    (balinResCauses.extract handSize (handSize * 2)).all (· == balinResCauses[handSize]!) &&
    balinResCauses[0]! != balinResCauses[handSize]! &&
    armorEmptyMoves.isEmpty &&
    gArmorEmptyDone.drewFromEmpty me &&
    dmgPermRawCauses.size == 3 &&
    dmgPermRawCauses.all isClassifiedNonOneShot &&
    gDmgPermRaw.nextEffectId == gDmgSetup.nextEffectId &&
    dmgPermResCauses.size == 3 &&
    dmgPermResCauses.all (· == dmgPermResCauses[0]!) &&
    (match dmgPermResCauses[0]! with | .oneShotEffect (some _) (some _) (some _) => true | _ => false) &&
    dmgPlayerRawCauses.size == 3 &&
    dmgPlayerRawCauses.all isClassifiedNonOneShot &&
    gDmgPlayerRaw.nextEffectId == gDmgSetup.nextEffectId &&
    dmgPlayerResCauses.size == 3 &&
    dmgPlayerResCauses.all (· == dmgPlayerResCauses[0]!) &&
    (match dmgPlayerResCauses[0]! with | .oneShotEffect (some _) (some _) (some _) => true | _ => false) &&
    sweepResCauses.size >= 9 &&
    sweepResCauses.all (· == sweepResCauses[0]!) &&
    (match sweepResCauses[0]! with | .oneShotEffect (some _) (some _) (some _) => true | _ => false) &&
    nivRawCauses.size == 3 &&
    nivRawCauses[0]! == .costPayment .life me none &&
    isClassifiedNonOneShot nivRawCauses[1]! &&
    isClassifiedNonOneShot nivRawCauses[2]! &&
    gNivRaw.nextEffectId == gDmgSetup.nextEffectId &&
    nivResCauses.size == 3 &&
    nivResCauses[0]! == .costPayment .life me (some lh.id) &&
    nivResCauses[1]! == nivResCauses[2]! &&
    (match nivResCauses[1]! with | .oneShotEffect (some _) (some _) (some _) => true | _ => false) &&
    nivLockedEvents.isEmpty &&
    dreadRawCauses.size == 3 &&
    dreadRawCauses.all isClassifiedNonOneShot &&
    gDreadRaw.nextEffectId == gDmgSetup.nextEffectId &&
    dreadResCauses.size == 3 &&
    dreadResCauses.all (· == dreadResCauses[0]!) &&
    (match dreadResCauses[0]! with | .oneShotEffect (some _) (some _) (some _) => true | _ => false) &&
    skrelvRawCauses.size == 2 &&
    skrelvRawCauses.all isClassifiedNonOneShot &&
    gSkrelvRaw.nextEffectId == gDmgSetup.nextEffectId &&
    skrelvResCauses.size == 2 &&
    skrelvResCauses.all (· == skrelvResCauses[0]!) &&
    (match skrelvResCauses[0]! with | .oneShotEffect (some _) (some _) (some _) => true | _ => false) &&
    drainPlanRawCauses.size == 3 &&
    drainPlanRawCauses.all isClassifiedNonOneShot &&
    gDrainPlanRaw.nextEffectId == gDmgSetup.nextEffectId &&
    drainPlanResCauses.size == 3 &&
    drainPlanResCauses[0]! != drainPlanResCauses[1]! &&
    drainPlanResCauses[1]! == drainPlanResCauses[2]! &&
    (match drainPlanResCauses[1]! with | .oneShotEffect (some _) (some _) (some _) => true | _ => false)

/- `EffectId` `⟨0⟩` is a valid effect identifier (`Game.nextEffectId` starts at
`0`), while `Option EffectId := none` on `EventCause.oneShotEffect` allocates a
fresh `EffectId` when recorded. -/
#guard
  let g0 : Game := {}
  let g1 := g0.record (GameEvent.looked 1 me 1)
  let g2 := g1.record (GameEvent.looked 1 me 1)
  let g3 := g2.record (GameEvent.looked 1 me 1 (id := some ⟨0⟩))
  let ids := (GameEvent.oneShotEffectsWithId g3.events).map Prod.fst
  g0.nextEffectId == 0 &&
    g1.nextEffectId == 1 &&
    g2.nextEffectId == 2 &&
    g3.nextEffectId == 2 &&
    ids == #[⟨0⟩, ⟨1⟩, ⟨0⟩] &&
    (EventCause.oneShotEffect none none none).oneShotEffectId? == none &&
    (EventCause.oneShotEffect (some ⟨0⟩) none none).oneShotEffectId? == some ⟨0⟩

/- Phase 3 / Phase 10: every rules event in a full demo game carries a total `EventCause`. -/
#guard
  let g := Agent.play drawnHands 400
  let rulesClassified := g.events.all fun e =>
    match e with
    | .rules .. => e.cause?.isSome
    | .engine .. => e.cause?.isNone
  g.over && rulesClassified

/- Phase 4: `commitBatch` shares one `BatchId` and one minted `EffectId` across
all events in the batch, `commitBatchWithCauses` shares one `BatchId` while
preserving per-event causes, and sequential `record` / `applyEvent` calls
outside `withBatch` allocate distinct, strictly increasing `BatchId`s
(CR 603.2c / 608.2c / 704.3). -/
#guard
  let g0 := quiet afterDraw
  let b0 := g0.nextBatchId
  let e0 := g0.nextEffectId
  let g1 := g0.commitBatch (.oneShotEffect none none (some me)) #[
    .life (.gained me 2),
    .life (.lost opp 2 false)]
  let rules1 := g1.events.filter (fun e => match e.change with | .rules _ => true | _ => false)
  let g2 := (quiet g1).commitBatchWithCauses #[
    (.stateBased .lethalDamage, .life (.lost me 1 false)),
    (.stateBased .zeroOrLessToughness, .life (.lost opp 1 false))]
  let rules2 := g2.events.filter (fun e => match e.change with | .rules _ => true | _ => false)
  let g3 :=
    ((quiet g2).record (GameEvent.life g2.turnNumber me 1 true (cause := testCause))).record
      (GameEvent.life g2.turnNumber me 1 true (cause := testCause))
  let rules3 := g3.events.filter (fun e => match e.change with | .rules _ => true | _ => false)
  rules1.size == 2 &&
    rules1[0]!.batch == some ⟨b0⟩ &&
    rules1[1]!.batch == some ⟨b0⟩ &&
    rules1[0]!.cause? == some (.oneShotEffect (some ⟨e0⟩) none (some me)) &&
    rules1[1]!.cause? == some (.oneShotEffect (some ⟨e0⟩) none (some me)) &&
    g1.nextBatchId == b0 + 1 &&
    g1.nextEffectId == e0 + 1 &&
    rules2.size == 2 &&
    rules2[0]!.batch == some ⟨b0 + 1⟩ &&
    rules2[1]!.batch == some ⟨b0 + 1⟩ &&
    rules2[0]!.cause? == some (.stateBased .lethalDamage) &&
    rules2[1]!.cause? == some (.stateBased .zeroOrLessToughness) &&
    g2.nextBatchId == b0 + 2 &&
    rules3.size == 2 &&
    rules3[0]!.batch == some ⟨b0 + 2⟩ &&
    rules3[1]!.batch == some ⟨b0 + 3⟩ &&
    g3.nextBatchId == b0 + 4

/- Phase 4: first-strike and regular combat damage steps commit two distinct
`BatchId`s (CR 510.4 / 702.7b), and each SBA pass commits all simultaneous
state-based actions under one `BatchId` per pass (CR 704.3). -/
#guard
  let fsKnight : CardDef :=
    { (creature "First Striker" ManaCost.empty #["Knight"] 2 2) with
      keywords := Keyword.firstStrike }
  let gCombat0 :=
    addPermanent (addPermanent afterDraw fsKnight me me) bear me me
  let fk := (gCombat0.battlefield.filter (·.name == "First Striker"))[0]!
  let br := (gCombat0.battlefield.filter (·.name == bear.name))[0]!
  let gCombat1 :=
    quiet (gCombat0.markAttacking fk.id (some (.player opp))
      |>.markAttacking br.id (some (.player opp)))
  let gFs := gCombat1.combatDamage
  let gReg := gFs.combatDamage
  let fsEvents := gReg.events.filter (fun e =>
    match e.change with
    | .rules _ => e.cause? == some (.turnBased (.dealCombatDamage true))
    | _ => false)
  let regEvents := gReg.events.filter (fun e =>
    match e.change with
    | .rules _ => e.cause? == some (.turnBased (.dealCombatDamage false))
    | _ => false)
  let lordDef : CardDef :=
    { (creature "Bear Lord" ManaCost.empty #["Bear"] 2 2) with
      staticAbilities := #[.otherCreaturesGet #[.bear] 1 1] }
  let gSba0 :=
    let g := addPermanent (addPermanent (addPermanent afterDraw lordDef me me) bear me me) hero me me
    let ld := (g.battlefield.filter (·.name == "Bear Lord"))[0]!
    let b := (g.battlefield.filter (·.name == bear.name))[0]!
    let h := (g.battlefield.filter (·.name == hero.name))[0]!
    let g := setMarkedDamage (setMarkedDamage (setMarkedDamage g ld.id 2) h.id 3) b.id 2
    quiet g
  let ldId := (gSba0.battlefield.filter (·.name == "Bear Lord"))[0]!.id
  let hId := (gSba0.battlefield.filter (·.name == hero.name))[0]!.id
  let bId := (gSba0.battlefield.filter (·.name == bear.name))[0]!.id
  let gSbaDone := gSba0.checkSBA
  let batchOfMoved? (oid : ObjectId) : Option BatchId :=
    gSbaDone.events.findSome? (fun e =>
      match e.change with
      | .rules (.zone (.moved before ..)) =>
        if before.id == some oid && e.cause? == some (.stateBased .lethalDamage) then e.batch else none
      | _ => none)
  !fsEvents.isEmpty &&
    !regEvents.isEmpty &&
    fsEvents.all (·.batch == fsEvents[0]!.batch) &&
    regEvents.all (·.batch == regEvents[0]!.batch) &&
    fsEvents[0]!.batch != regEvents[0]!.batch &&
    (match batchOfMoved? ldId, batchOfMoved? hId, batchOfMoved? bId with
     | some bLd, some bH, some bB => bLd == bH && bLd != bB
     | _, _, _ => false)

/- Phase 4: batch multiplicity for "one or more" triggers vs. per-object
triggers (CR 603.2c). Simultaneous events in a single batch fire "one or more"
triggers once, while sequential batches fire them once per batch. -/
#guard
  let deathWatcher : CardDef :=
    { name := "Death Watcher"
      types := #[.enchantment]
      triggeredAbilities := #[
        TriggeredAbility.fra .oneOrMoreOtherCreaturesDie "" (.draw 1),
        TriggeredAbility.fra .nontokenYouControlDies "" (.gainLife (.fixed 1)),
        TriggeredAbility.fra .creatureCardsPutIntoYourGy "" (.draw 1),
        TriggeredAbility.fra (.fra .youCreateCreatureTokens) "" (.draw 1),
        TriggeredAbility.fra .creaturesYouControlBecomeTapped "" (.draw 1)] }
  let gBase :=
    let g := addPermanent (addPermanent (addPermanent afterDraw deathWatcher me me) bear me me) hero me me
    let g := addPermanent g bear me me
    let g := (g.move g.battlefield.back!.id (.library me) none (libraryPosition := some .top)).1
    let g := addPermanent g hero me me
    let g := (g.move g.battlefield.back!.id (.library me) none (libraryPosition := some .top)).1
    quiet g
  let b := (gBase.battlefield.filter (·.name == bear.name))[0]!
  let h := (gBase.battlefield.filter (·.name == hero.name))[0]!
  -- 1. Simultaneous vs. sequential creature deaths
  let gSimulDie := gBase.withBatch none (fun g =>
    (g.destroyPermanent (g.object! b.id)).destroyPermanent (g.object! h.id))
  let simulOneOrMore := gSimulDie.waitingTriggers.filter (·.event == .oneOrMoreOtherCreaturesDie)
  let simulEach := gSimulDie.waitingTriggers.filter (·.event == .nontokenYouControlDies)
  let gSeqDie := (gBase.destroyPermanent (gBase.object! b.id)).destroyPermanent (gBase.object! h.id)
  let seqOneOrMore := gSeqDie.waitingTriggers.filter (·.event == .oneOrMoreOtherCreaturesDie)
  -- 2. Simultaneous vs. sequential mill of creature cards into your graveyard
  let gSimulMill := gBase.mill me 2
  let simulMillTrig := gSimulMill.waitingTriggers.filter (·.event == .creatureCardsPutIntoYourGy)
  let gSeqMill := (gBase.mill me 1).mill me 1
  let seqMillTrig := gSeqMill.waitingTriggers.filter (·.event == .creatureCardsPutIntoYourGy)
  -- 3. Simultaneous vs. sequential creature token creation
  let gSimulTok := gBase.createKindTokens me .humanSoldier 2
  let simulTokTrig := gSimulTok.waitingTriggers.filter (·.event == .fra .youCreateCreatureTokens)
  let gSeqTok := (gBase.createKindTokens me .humanSoldier 1).createKindTokens me .humanSoldier 1
  let seqTokTrig := gSeqTok.waitingTriggers.filter (·.event == .fra .youCreateCreatureTokens)
  -- 4. Simultaneous vs. sequential tapping of creatures you control
  let gSimulTap := gBase.withBatch none (fun g =>
    (g.becomeTapped (g.object! b.id)).becomeTapped (g.object! h.id))
  let simulTapTrig := gSimulTap.waitingTriggers.filter (·.event == .creaturesYouControlBecomeTapped)
  let gSeqTap := (gBase.becomeTapped (gBase.object! b.id)).becomeTapped (gBase.object! h.id)
  let seqTapTrig := gSeqTap.waitingTriggers.filter (·.event == .creaturesYouControlBecomeTapped)
  simulOneOrMore.size == 1 &&
    simulEach.size == 2 &&
    seqOneOrMore.size == 2 &&
    simulMillTrig.size == 1 &&
    seqMillTrig.size == 2 &&
    simulTokTrig.size == 1 &&
    seqTokTrig.size == 2 &&
    simulTapTrig.size == 1 &&
    seqTapTrig.size == 2

/- Phase 4:
1. `discardEntireHand` commits one batch per player hand discard (queueing
   `.fra .playerDiscards` once for a multi-card hand), and a batch in which two
   players discard queues `.fra .playerDiscards` once per discarding player.
2. Unified `.youPutPlusOne` evaluation fires both `onceEachTurn` abilities
   (`plusOneCreateInsectOnce`, `plusOneOnThisOnce`) and Invisible Woman on
   printed enters-with +1/+1 counters and `.explore` (which also applies
   `countersYouPut` / Doc Samson), while setting `firedOnceEachTurn` so a second
   +1/+1 counter event in the same turn does not re-trigger them.
3. `eventSuppressedByKarn` suppresses enters triggers (`tokenYouControlEnters`)
   without suppressing counter-put triggers (`youPutCountersOnGoblinOrcArmy`,
   `.fra .youPutLoyaltyCounters`, `.youPutPlusOne`) on entering permanents
   (CR 122.6). -/
#guard
  -- 1. discardEntireHand batching and per-player .playerDiscards
  let discardWatcher : CardDef :=
    { name := "Discard Watcher"
      types := #[.enchantment]
      triggeredAbilities := #[TriggeredAbility.fra (.fra .playerDiscards) "" (.draw 1)] }
  let gDisc0 := quiet (addPermanent afterDraw discardWatcher me me)
  let gDisc1 := gDisc0.discardEntireHand me
  let discEvents1 := gDisc1.events.filter (fun e =>
    match e.change with
    | .rules (.zone (.moved _ _ (.hand _) (.graveyard _) .discard ..)) => true
    | _ => false)
  let discTrig1 := gDisc1.waitingTriggers.filter (·.event == .fra .playerDiscards)
  let gDiscBoth := gDisc0.withBatch none (fun g =>
    (g.discardEntireHand me).discardEntireHand opp)
  let discTrigBoth := gDiscBoth.waitingTriggers.filter (·.event == .fra .playerDiscards)
  -- 2. Unified .youPutPlusOne on printed entersWithPlusOneCounters and .explore + Doc Samson
  let insectWatcher : CardDef :=
    { (creature "Insect Watcher" ManaCost.empty #["Hero"] 1 1) with
      triggeredAbilities := #[.triggered .fromEffect Effect.resourcePlusOneCreateInsectOnce {}] }
  let selfOnceWatcher : CardDef :=
    { (creature "Self Once Watcher" ManaCost.empty #["Hero"] 2 2) with
      triggeredAbilities := #[.triggered .fromEffect Effect.resourcePlusOneOnThisOnce {}] }
  let wallWatcher : CardDef :=
    { (creature "Wall Watcher" ManaCost.empty #["Hero"] 1 4) with
      triggeredAbilities := #[.triggered .fromEffect Effect.resourcePlusOneOnHeroesCreateWall {}] }
  let entersHero : CardDef :=
    { (creature "Enters Hero" ManaCost.empty #["Hero", "Goblin"] 1 1) with
      entersWithPlusOneCounters := 2 }
  let docSamsonDef : CardDef :=
    { (creature "Doc Samson Test" ManaCost.empty #["Hero"] 3 3) with
      staticAbilities := #[.extraCounterOnPermanents] }
  let gPlus0 :=
    let g := addPermanent (addPermanent (addPermanent afterDraw insectWatcher me me) selfOnceWatcher me me) wallWatcher me me
    let g := addPermanent g { name := "Noncreature Artifact", types := #[.artifact] } me me
    let g := addPermanent g entersHero me me
    let ehId := g.battlefield.back!.id
    let g := (g.move ehId (.hand me) none).1
    quiet g
  let noncreatureArt := (gPlus0.battlefield.filter (·.name == "Noncreature Artifact"))[0]!
  let gPlusArt := gPlus0.addPlusOnePlusOneTo noncreatureArt 1
  let ehHandId := (gPlusArt.player me).hand.back!
  let (gPlusEntered, ehBfId) := gPlusArt.putOntoBattlefield ehHandId me
  let plusTrigs1 := gPlusEntered.waitingTriggers.filter (·.event == .youPutPlusOne)
  let gPlusSecond := gPlusEntered.addPlusOnePlusOneTo (gPlusEntered.object! ehBfId) 1
  let plusTrigs2 := gPlusSecond.waitingTriggers.filter (·.event == .youPutPlusOne)
  -- Explore with Doc Samson and nonland top card
  let gExp0 :=
    let g := addPermanent (addPermanent (addPermanent afterDraw insectWatcher me me) docSamsonDef me me) bear me me
    let g := addPermanent g bear me me
    let topId := g.battlefield.back!.id
    let g := (g.move topId (.library me) none (libraryPosition := some .top)).1
    quiet g
  let explorer := (gExp0.battlefield.filter (·.name == bear.name))[0]!
  let gExp1 := gExp0.applyFrc me default .explore #[] (some explorer.id)
  let explorerAfter := gExp1.object! explorer.id
  let expTrigs := gExp1.waitingTriggers.filter (·.event == .youPutPlusOne)
  -- 3. Karn suppresses tokenYouControlEnters but not counter-put triggers on entering permanents,
  --    and youPutCountersOnGoblinOrcArmy only triggers on a Goblin/Orc/Army you control
  let karnDef : CardDef :=
    { name := "Karn Test"
      types := #[.planeswalker]
      loyalty := some 5
      staticAbilities := #[.enteringArtifactsCreaturesDontTrigger] }
  let counterAndTokenWatcher : CardDef :=
    { name := "Counter And Token Watcher"
      types := #[.enchantment]
      triggeredAbilities := #[
        .triggered .fromEffect (Effect.ofTrigger (.watch .tokensEnterMayDraw)) {},
        TriggeredAbility.fra .youPutCountersOnGoblinOrcArmy "" (.draw 1),
        TriggeredAbility.fra (.fra .youPutLoyaltyCounters) "" (.draw 1),
        .triggered .fromEffect Effect.resourcePlusOneOnHeroesCreateWall {}] }
  let artifactWalker : CardDef :=
    { name := "Artifact Walker"
      types := #[.artifact, .planeswalker]
      loyalty := some 3 }
  let oppGoblinDef : CardDef :=
    creature "Opp Goblin" ManaCost.empty #["Goblin"] 1 1
  let gKarn0 :=
    let g := addPermanent (addPermanent (addPermanent afterDraw karnDef me me) counterAndTokenWatcher me me) oppGoblinDef opp opp
    let g := addPermanent g entersHero me me
    let ehId := g.battlefield.back!.id
    let g := (g.move ehId (.hand me) none).1
    let g := addPermanent g artifactWalker me me
    let awId := g.battlefield.back!.id
    let g := (g.move awId (.hand me) none).1
    quiet g
  let oppGoblin := (gKarn0.battlefield.filter (·.name == "Opp Goblin"))[0]!
  let gKarnOppGob := gKarn0.addPlusOnePlusOneTo oppGoblin 1 (byPlayer := some me)
  let karnHand := (gKarnOppGob.player me).hand
  let awHandId := karnHand.back!
  let ehKarnHandId := karnHand[karnHand.size - 2]!
  let (gKarn1, _) := gKarnOppGob.putOntoBattlefield ehKarnHandId me
  let (gKarn2, _) := gKarn1.putOntoBattlefield awHandId me
  let (gKarn3, _) := gKarn2.createToken me bear
  discEvents1.size >= 2 &&
    discEvents1.all (·.batch == discEvents1[0]!.batch) &&
    discTrig1.size == 1 &&
    discTrigBoth.size == 2 &&
    gPlusArt.waitingTriggers.isEmpty &&
    plusTrigs1.size == 3 &&
    plusTrigs2.size == 4 &&
    explorerAfter.status.plusOnePlusOne == 2 &&
    expTrigs.size == 1 &&
    (gKarnOppGob.waitingTriggers.filter (·.event == .youPutCountersOnGoblinOrcArmy)).isEmpty &&
    (gKarn3.waitingTriggers.filter (·.event == .tokenYouControlEnters)).isEmpty &&
    (gKarn3.waitingTriggers.filter (·.event == .youPutCountersOnGoblinOrcArmy)).size == 1 &&
    (gKarn3.waitingTriggers.filter (·.event == .fra .youPutLoyaltyCounters)).size == 1 &&
    (gKarn3.waitingTriggers.filter (·.event == .youPutPlusOne)).size == 1

def causeIsStamped : EventCause → Bool
  | .oneShotEffect none _ _ => false
  | .replaced _ orig => causeIsStamped orig
  | _ => true

def allRulesEventsClassified (g : Game) : Bool :=
  g.events.all fun e =>
    match e with
    | .rules .. =>
      match e.cause? with
      | some c => causeIsStamped c
      | none => false
    | .engine .. => e.cause?.isNone

def noOneShotCauses (g : Game) : Bool :=
  allRulesEventsClassified g &&
  g.events.all fun e =>
    match e.cause? with
    | some c => c.oneShotEffectId?.isNone
    | none => true

/- Phase 5.1 isolation: `TurnEvent` and `applyTurnEvent` drive `turnNumber`,
`activePlayer`, `step`, `isNight`, `extraTurns` (CR 500.7 LIFO), and
`additionalCombatPhases` (CR 500.8). Step/phase/turn transitions emit
`stepEnded`, `phaseEnded`, `phaseBegan`, `stepBegan`, `turnEnded`, and
`turnBegan`. -/
#guard
  let g0 := quiet afterDraw
  -- Extra turns LIFO (CR 500.7) and extra combat phase (CR 500.8)
  let g1 :=
    (g0.record (GameEvent.extraTurnAdded g0.turnNumber me .current
      (cause := .oneShotEffect (some ⟨97⟩) none (some me)))).record
      (GameEvent.extraTurnAdded g0.turnNumber opp .current
        (cause := .oneShotEffect (some ⟨98⟩) none (some me)))
  let g2 := g1.record (GameEvent.extraPhaseAdded g1.turnNumber .combat .current
    (cause := .oneShotEffect (some ⟨99⟩) none (some me)))
  let g3 := g2.record (GameEvent.turnBegan (g2.turnNumber + 1) opp (extra := true))
  let g4 := (g3.record (GameEvent.stepBegan g3.turnNumber .endOfCombat opp)).record
    (GameEvent.phaseBegan g3.turnNumber .combat)
  let g5 := g4.applyChange (.rules (.turn (.dayNightChanged true)))
  -- Step advance across phase boundary (draw -> precombatMain)
  let gStep := (quiet (afterDraw.record (GameEvent.stepBegan afterDraw.turnNumber .draw afterDraw.activePlayer))).advanceStep
  let turnEvents := gStep.events.filterMap (fun e =>
    match e.change with
    | .rules (.turn te) => some te
    | _ => none)
  g1.extraTurns == #[opp, me] &&
    g2.additionalCombatPhases == g0.additionalCombatPhases + 1 &&
    g3.turnNumber == g0.turnNumber + 1 &&
    g3.activePlayer == opp &&
    !g3.isFirstTurn &&
    g3.extraTurns == #[me] &&
    g4.additionalCombatPhases == g0.additionalCombatPhases &&
    g5.isNight &&
    turnEvents.contains (.stepEnded .draw) &&
    turnEvents.contains (.phaseEnded .beginning) &&
    turnEvents.contains (.phaseBegan .precombatMain) &&
    turnEvents.contains (.stepBegan .precombatMain me) &&
    allRulesEventsClassified g1 &&
    allRulesEventsClassified g2 &&
    allRulesEventsClassified gStep

/- Phase 5.2 isolation: `CombatEvent` (`attackersDeclared`, `becameAttacking`,
`blockersDeclared`, `becameBlocked`, `remainedUnblocked`, `damageAssigned`,
`removedFromCombat`) and `AttackTarget` (`player`, `planeswalker`, `battle`).
Verifies that `declareAttackers` batches `attackersDeclared` and non-vigilance
`PermanentEvent.tapped` under one `BatchId`, and that 508.4 `becameAttacking`
sets `attacking := true` and `attackingTarget` without firing "whenever …
attacks" triggers (CR 508.3a). -/
#guard
  let attackWatcher : CardDef :=
    { (creature "Attack Watcher" ManaCost.empty #["Hero"] 2 2) with
      triggeredAbilities := #[TriggeredAbility.fra (.fra .creatureYouControlAttacks) "" (.draw 1)] }
  let oppWalker : CardDef :=
    { name := "Opp Walker"
      types := #[.planeswalker]
      subtypes := #["Jace"]
      loyalty := some 4 }
  let g0 :=
    let g := addPermanent (addPermanent (addPermanent (addPermanent afterDraw attackWatcher me me) bear me me) hero me me) oppWalker opp opp
    let g := addPermanent g bear opp opp
    let g := (g.record (GameEvent.stepBegan g.turnNumber .declareAttackers g.activePlayer)).change (.pending .declareAttackers)
    quiet g
  let bMe := (g0.battlefield.filter (fun o => o.name == bear.name && o.controlledBy me))[0]!
  let hMe := (g0.battlefield.filter (fun o => o.name == hero.name && o.controlledBy me))[0]!
  let pwOpp := (g0.battlefield.filter (·.name == "Opp Walker"))[0]!
  let bOpp := (g0.battlefield.filter (fun o => o.name == bear.name && o.controlledBy opp))[0]!
  -- 1. 508.4 becameAttacking (targeting planeswalker) does NOT fire attack triggers
  let gBecame := g0.record (GameEvent.becameAttacking g0.turnNumber (g0.snapshot hMe) (.planeswalker pwOpp.id)
    (cause := .oneShotEffect (some ⟨77⟩) none (some me)))
  let hAfterBecame := gBecame.object! hMe.id
  let becameEvents := gBecame.events.filter (fun e =>
    match e.change with
    | .rules (.combat (.becameAttacking c (.planeswalker pid))) =>
      c.id == some hMe.id && pid == pwOpp.id
    | _ => false)
  -- 2. declareAttackers with bMe attacking opp
  let gAtk :=
    match g0.declareAttackers me #[bMe.id] (each := #[some opp]) with
    | .ok g => g
    | .error _ => g0
  let bAfterAtk := gAtk.object! bMe.id
  let atkCombatAndTap := gAtk.events.filter (fun e =>
    match e.change with
    | .rules (.combat (.attackersDeclared _ _)) => true
    | .rules (.permanent (.tapped o _)) => o.id == some bMe.id
    | _ => false)
  -- 3. declareBlockers with bOpp blocking bMe while hMe (made attacking) remains unblocked
  let gBothAtk := (quiet gAtk).record (GameEvent.becameAttacking gAtk.turnNumber (gAtk.snapshot (gAtk.object! hMe.id)) (.player opp)
    (cause := .oneShotEffect (some ⟨78⟩) none (some me)))
  let gToBlk := quiet ((gBothAtk.record (GameEvent.stepBegan gBothAtk.turnNumber .declareBlockers gBothAtk.activePlayer)).changes #[
    .pending .declareBlockers,
    .blockersQueue #[opp]
  ])
  let gBlk :=
    match gToBlk.declareBlockers opp #[(bOpp.id, bMe.id)] with
    | .ok g => g
    | .error _ => gToBlk
  let hasBlockersDeclared := gBlk.events.any (fun e =>
    match e.change with
    | .rules (.combat (.blockersDeclared p decls)) =>
      p == opp && decls.any (fun (b, aid) => b.id == some bOpp.id && aid == bMe.id)
    | _ => false)
  let hasBecameBlocked := gBlk.events.any (fun e =>
    match e.change with
    | .rules (.combat (.becameBlocked a bids)) =>
      a.id == some bMe.id && bids == #[bOpp.id]
    | _ => false)
  let hasRemainedUnblocked := gBlk.events.any (fun e =>
    match e.change with
    | .rules (.combat (.remainedUnblocked a)) => a.id == some hMe.id
    | _ => false)
  -- 4. CombatEvent.removedFromCombat clears combat status
  let gRem := (quiet gBlk).removeFromCombat (gBlk.object! bMe.id)
    (cause := some (.oneShotEffect (some ⟨79⟩) none (some me)))
  let bAfterRem := gRem.object! bMe.id
  let bOppAfterRem := gRem.object! bOpp.id
  -- 5. Entering attacking (default defendingPlayer vs planeswalker target via Sneak / tokens)
  let gEnter0 := insertObject (quiet g0) bear me (.graveyard me)
  let gyBearId := (gEnter0.objects.filter (fun o => o.name == bear.name && o.zone == .graveyard me))[0]!.id
  let (gEnterDefault, enteredDefId) := gEnter0.putOntoBattlefield gyBearId me (attacking := true)
    (cause := some (.oneShotEffect (some ⟨80⟩) none (some me)))
  let enteredDefMovedTarget := gEnterDefault.events.findSome? (fun e =>
    match e.change with
    | .rules (.zone (.moved _ after _ .battlefield _ _ _ _)) =>
      if after.id == some enteredDefId then after.attackingTarget else none
    | _ => none)
  let enteredDefBecameTarget := gEnterDefault.events.findSome? (fun e =>
    match e.change with
    | .rules (.combat (.becameAttacking c tgt)) =>
      if c.id == some enteredDefId then some tgt else none
    | _ => none)
  let gSneak0 :=
    let g := (quiet g0).record (GameEvent.becameAttacking g0.turnNumber (g0.snapshot hMe) (.planeswalker pwOpp.id)
      (cause := .oneShotEffect (some ⟨81⟩) none (some me)))
    let g := insertObject g bear me .stack (some me) {}
    let spId := (g.objects.filter (fun o => o.name == bear.name && o.zone == .stack))[0]!.id
    let g := g.putStackEntry me spId
    (g.record (GameEvent.stepBegan g.turnNumber .declareBlockers g.activePlayer)).change (.pending .none)
  let sneakSpellId := gSneak0.stack.back!.objectId
  let gSneak1 :=
    match gSneak0.paySneak me sneakSpellId hMe.id with
    | .ok g => g.resolveTop
    | .error _ => gSneak0
  let sneakEntered? := gSneak1.battlefield.find? (fun o =>
    o.name == bear.name && o.controlledBy me && o.id != bMe.id)
  let gTokPw := (quiet g0).createKindTokens me .spirit 1 (tapped := true)
    (attacking := true) (attackingTarget := some (.planeswalker pwOpp.id))
    (cause := some (.oneShotEffect (some ⟨82⟩) none (some me)))
  let tokPw? := gTokPw.battlefield.find? (·.printed.isToken)
  -- Andúril (ruling 181): when multiple legal attack targets exist (opp and pwOpp),
  -- each Spirit token is asked separately before entering and may attack a different target.
  let gAnduril0 := (quiet g0).createAndMarkTokensAttacking me .spirit 2 true true (some hMe.id)
  let gAnduril1 :=
    match gAnduril0.apply me (.chooseMode 1) with
    | .ok g1 => g1
    | .error _ => gAnduril0
  let gAnduril2 :=
    match gAnduril1.apply me (.chooseMode 0) with
    | .ok g2 => g2
    | .error _ => gAnduril1
  let andurilSpirits := gAnduril2.battlefield.filter (·.printed.isToken)
  let andurilCreatedTargets := gAnduril2.events.filterMap (fun e =>
    match e.change with
    | .rules (.zone (.created obj _)) => some (obj.attacking, obj.attackingTarget, e.batch)
    | _ => none)
  let andurilBecameTargets := gAnduril2.events.filterMap (fun e =>
    match e.change with
    | .rules (.combat (.becameAttacking _ tgt)) => some (tgt, e.batch)
    | _ => none)
  -- Grim Reaper / returnFromGyTappedAttackingFinality (CR 508.4): asks before entering when multiple targets exist
  let gReaper0 := insertObject (quiet g0) bear me (.graveyard me)
  let reaperGyId := (gReaper0.objects.filter (fun o => o.name == bear.name && o.zone == .graveyard me))[0]!.id
  let gReaper1 := gReaper0.returnFromGyTappedAttackingFinality me reaperGyId
  let gReaper2 :=
    match gReaper1.apply me (.chooseMode 1) with
    | .ok g => g
    | .error _ => gReaper1
  let reaperBear? := gReaper2.battlefield.find? (fun o =>
    o.name == bear.name && o.controlledBy me && o.id != bMe.id)
  let reaperMovedTarget := gReaper2.events.findSome? (fun e =>
    match e.change with
    | .rules (.zone (.moved _ after _ .battlefield ..)) => after.attackingTarget
    | _ => none)
  hAfterBecame.status.attacking &&
    hAfterBecame.status.attackingTarget == some (AttackTarget.planeswalker pwOpp.id) &&
    !gBecame.declaredAsAttackerThisTurn hAfterBecame.id &&
    gBecame.defendingPlayerOf hAfterBecame == opp &&
    becameEvents.size == 1 &&
    gBecame.waitingTriggers.isEmpty &&
    bAfterAtk.status.attacking &&
    bAfterAtk.status.attackingTarget == some (AttackTarget.player opp) &&
    gAtk.declaredAsAttackerThisTurn bAfterAtk.id &&
    atkCombatAndTap.size == 2 &&
    atkCombatAndTap[0]!.batch == atkCombatAndTap[1]!.batch &&
    atkCombatAndTap[0]!.cause? == some (.turnBased .declareAttackers) &&
    !gAtk.stack.isEmpty &&
    hasBlockersDeclared &&
    hasBecameBlocked &&
    hasRemainedUnblocked &&
    (gBlk.object! bMe.id).status.blocked &&
    (gBlk.object! bOpp.id).status.blocking == #[bMe.id] &&
    !bAfterRem.status.attacking &&
    bAfterRem.status.attackingTarget.isNone &&
    !bAfterRem.status.blocked &&
    !bOppAfterRem.status.blocking.isEmpty &&
    (gRem.creaturesBlockedBy bOppAfterRem).isEmpty &&
    (gRem.blockersOf bMe.id).isEmpty &&
    (gEnterDefault.object! enteredDefId).status.attackingTarget == some (AttackTarget.player gEnterDefault.defendingPlayer) &&
    enteredDefMovedTarget == some (AttackTarget.player gEnterDefault.defendingPlayer) &&
    enteredDefBecameTarget == some (AttackTarget.player gEnterDefault.defendingPlayer) &&
    (sneakEntered?.map (·.status.attackingTarget)) == some (some (AttackTarget.planeswalker pwOpp.id)) &&
    (tokPw?.map (·.status.attackingTarget)) == some (some (AttackTarget.planeswalker pwOpp.id)) &&
    !(gAnduril0.battlefield.any (·.printed.isToken)) &&
    !(gAnduril1.battlefield.any (·.printed.isToken)) &&
    andurilSpirits.size == 2 &&
    andurilSpirits[0]!.status.attackingTarget == some (AttackTarget.planeswalker pwOpp.id) &&
    andurilSpirits[1]!.status.attackingTarget == some (AttackTarget.player opp) &&
    andurilCreatedTargets.size == 2 &&
    andurilBecameTargets.size == 2 &&
    andurilCreatedTargets[0]!.1 &&
    andurilCreatedTargets[0]!.2.1 == some (AttackTarget.planeswalker pwOpp.id) &&
    andurilCreatedTargets[1]!.1 &&
    andurilCreatedTargets[1]!.2.1 == some (AttackTarget.player opp) &&
    andurilCreatedTargets[0]!.2.2 == andurilBecameTargets[0]!.2 &&
    andurilCreatedTargets[0]!.2.2 == andurilCreatedTargets[1]!.2.2 &&
    andurilCreatedTargets[0]!.2.2 == andurilBecameTargets[1]!.2 &&
    (gReaper1.object! reaperGyId).zone == .graveyard me &&
    (reaperBear?.map (·.status.attackingTarget)) == some (some (AttackTarget.planeswalker pwOpp.id)) &&
    reaperMovedTarget == some (AttackTarget.planeswalker pwOpp.id) &&
    allRulesEventsClassified gBecame &&
    allRulesEventsClassified gAtk &&
    allRulesEventsClassified gBlk &&
    allRulesEventsClassified gRem &&
    allRulesEventsClassified gEnterDefault &&
    allRulesEventsClassified gSneak1 &&
    allRulesEventsClassified gTokPw &&
    allRulesEventsClassified gAnduril2 &&
    allRulesEventsClassified gReaper2

/- Phase 5.3 isolation: `CastEvent` (`proposed`, `announced`, `targeted`,
`spellCast`, `abilityActivated`), `TriggerQueueEvent.putOnStack`,
`StackObjectEvent` (`copied`, `removedOnResolution`), and `GameEvent.landsPlayed`
via `ZoneEvent.moved` (`verb == .playLand`). Verifies that `applyStackObjectEvent`
copies `StackEntry` decisions (`targets`, `targetsAnnounced`, `chosenMode`,
`extraModes`, `dividedDamage`), `GameObject` stack/cast/adventure fields
(`chosenX`, `kicked`, `teamworkPaid`, `sneakPaid`, `sneakAttackWhom`,
`giftPromisedTo`, `adventurerCard`, `abilityEffect`, `triggeredAbility`,
`sourceId`), and `lastKnownPower` / `lastKnownToughness`. -/
#guard
  -- 1. Land play re-pointed at ZoneEvent.moved (.playLand) and recordLandPlayed helper
  let gLand0 := quiet afterDraw
  let gLand1 := gLand0.recordLandPlayed me
  let landMovedEvents := gLand1.events.filter (fun e =>
    match e.change with
    | .rules (.zone (.moved _ _ (.outside _) (.outside _) .playLand (some p) _ _)) =>
      p == me && e.cause? == some (.specialAction .playLand me)
    | _ => false)
  -- 2. CastEvent milestones via applyCastEvent
  let testModalSpell : CardDef :=
    { name := "Test Modal X Bolt"
      manaCost := { symbols := #[.x, .colored .red] }
      types := #[.instant]
      chooseOneOrBoth := true
      kicker := some (ManaCost.ofGeneric 1)
      giftTreasure := true
      spellModes := #[.dealDamage 2, .gainLife 2] }
  let gCast0 := insertObject (quiet afterDraw) testModalSpell me .stack (some me)
    (adventurerCard := some bear)
  let spId := (gCast0.objects.filter (·.name == "Test Modal X Bolt"))[0]!.id
  let gCast0 := gCast0.putStackEntry me spId
  let gCast1 := gCast0.record (GameEvent.proposed gCast0.turnNumber spId me (.graveyard me) (.alternative "flashback"))
  let gCast2 := gCast1.record (GameEvent.announced gCast1.turnNumber spId
    (modes := #[0, 1]) (x := some 3) (costs := #[.kicker, .gift opp, .teamwork #[⟨1⟩, ⟨2⟩]]))
  let gCast3 := gCast2.record (GameEvent.targeted gCast2.turnNumber spId
    #[Target.player opp] (division := #[2]))
  let gCast4 := gCast3.record (GameEvent.spellCast gCast3.turnNumber me
    (gCast3.snapshot (gCast3.object! spId)) (.graveyard me))
  let spObj := gCast4.object! spId
  let spEntry := (gCast4.stackEntry? spId).getD { objectId := spId, controller := me, targets := #[] }
  -- 3. StackObjectEvent.copied copies StackEntry decisions and GameObject fields across stack copiers
  let gCast4 := gCast4.record (GameEvent.announced gCast4.turnNumber spId
    (costs := #[.sneak ⟨99⟩ (some (.player opp))])
    (cause := some (.costPayment .returnToHand me (some spId))))
  let gCast4 := gCast4.setStackEntryLastKnown spId
    (lastKnownPower := some 5) (lastKnownToughness := some 6)
  let gCast4 := gCast4.createEffect (.exileInstantSorceryInstead spId)
      (cause := some (.oneShotEffect (some ⟨86⟩) none (some me)))
  let gCopy1 := gCast4.copyStackSpell (gCast4.object! spId) me
  let copy1Entry := gCopy1.stack.back!
  let copy1Obj := gCopy1.object! copy1Entry.objectId
  let trigSpecId : ObjectId := ⟨gCopy1.nextObjectId⟩
  let gTrigSpec := gCopy1.record (GameEvent.triggerPutOnStack gCopy1.turnNumber trigSpecId
    (gCopy1.snapshot (gCopy1.object! spId)) me
    (spec := {
      reflexiveResolution := some (.draw (.fixed 2) .you)
      fraCauseId := some ⟨71⟩
      fraCauseController := some opp
      fraCausePower := some 4
      fraCauseStatus := some { counters := #[(.plusOnePlusOne, 2)] }
      lastKnownPower := some 5
      lastKnownToughness := some 6 }))
  let gCopyTrig := gTrigSpec.copyStackSpell (gTrigSpec.object! trigSpecId) me
  let copyTrigObj := gCopyTrig.object! gCopyTrig.stack.back!.objectId
  -- Also test Loki and Way of the Cryomancer delayed spell-copy triggers
  let cryoCause : EventCause := .oneShotEffect (some ⟨87⟩) none (some me)
  let lokiCause : EventCause := .oneShotEffect (some ⟨88⟩) (some ⟨70⟩) (some me)
  let gCryoLoki0 :=
    let g := gCast4.registerDelayedTrigger
      { controller := me, source := none, kind := .copyNextInstantSorceryThisTurn, cause := cryoCause }
    g.registerDelayedTrigger
      { controller := me, source := none, kind := .lokiCopyNextInstantSorceryThisTurn (some ⟨70⟩) 10, cause := lokiCause }
  let gCryoLokiCast := gCryoLoki0.becomeCast me (gCryoLoki0.object! spId)
  let gCryoLokiStacked :=
    if gCryoLokiCast.pending != .none then applyIdle gCryoLokiCast
    else applyIdle (gCryoLokiCast.receivePriority me)
  let resolveCopyTrig (g : Game) : Game :=
    let g := g.resolveTop
    if g.pending != .none then applyIdle g else g
  let gCryoLoki := resolveCopyTrig (resolveCopyTrig (resolveCopyTrig gCryoLokiStacked))
  let copiedEvents := gCryoLoki.events.filterMap (fun e =>
    match e with
    | .rules _ (.stackObject (.copied orig copy ctrl)) c _ => some (orig, copy, ctrl, c)
    | _ => none)
  -- 4. TriggerQueueEvent.putOnStack and StackObjectEvent.removedOnResolution (CR 608.2b)
  let gTrig0 := addPermanent (quiet afterDraw) bear opp opp
  let oppBear := (gTrig0.battlefield.filter (fun o => o.name == bear.name && o.controlledBy opp))[0]!
  let trigAb := TriggeredAbility.fra .enter "When this enters, destroy target creature an opponent controls." (.destroy (.target .creature)) (kind := .oppCreature)
  let gTrigPut := gTrig0.putTriggeredAbilityOnStack me (gTrig0.object! oppBear.id) trigAb "enters"
  let gTrig1 := gTrigPut.setStackEntryTargets gTrigPut.stack.back!.objectId #[Target.permanent oppBear.id]
  let hasTrigPutOnStack := gTrig1.events.any (fun e =>
    match e.change with
    | .rules (.triggerQueue (.putOnStack stackId _ ctrl _)) =>
      ctrl == me && gTrig1.stack.any (·.objectId == stackId) &&
        e.cause? == some (.gameRule .triggeredAbility)
    | _ => false)
  let (gTrig2, _) := (quiet gTrig1).move oppBear.id (.graveyard opp) (verb := some .destroy)
    (cause := some (.oneShotEffect (some ⟨89⟩) none (some me)))
  let gTrig3 := gTrig2.resolveTop
  let hasRemovedOnResolution := gTrig3.events.any (fun e =>
    match e.change with
    | .rules (.stackObject (.removedOnResolution _)) =>
      e.cause? == some (.gameRule .abilityFinishedResolving)
    | _ => false)
  -- Spell fizzle on resolution records .instantOrSorceryFinishedResolving cause
  let gFizzle0 := addPermanent (quiet afterDraw) bear opp opp
  let fizzleBear := (gFizzle0.battlefield.filter (fun o => o.name == bear.name && o.controlledBy opp))[0]!
  let gFizzle0 := insertObject gFizzle0 lightningBolt me .stack (some me) {}
  let fizzleSpId := (gFizzle0.objects.filter (·.name == lightningBolt.name))[0]!.id
  let gFizzle0 := (gFizzle0.putStackEntry me fizzleSpId).setStackEntryTargets fizzleSpId #[Target.permanent fizzleBear.id]
  let (gFizzle1, _) := gFizzle0.move fizzleBear.id (.graveyard opp) (verb := some .destroy)
    (cause := some (.oneShotEffect (some ⟨90⟩) none (some me)))
  let gFizzle2 := (quiet gFizzle1).resolveTop
  let hasSpellRemovedOnResolution := gFizzle2.events.any (fun e =>
    match e.change with
    | .rules (.stackObject (.removedOnResolution _)) =>
      e.cause? == some (.gameRule .instantOrSorceryFinishedResolving)
    | _ => false)
  gLand1.loggedLandsPlayed me == 1 &&
    landMovedEvents.size == 1 &&
    !(gLand1.events.any GameEvent.enteredBattlefield) &&
    gCast4.castFromGraveyard spObj.id &&
    gCast4.wasCast spObj.id &&
    spObj.chosenX == some 3 &&
    gCast4.wasKicked spObj.id &&
    gCast4.giftPromisedTo? spObj.id == some opp &&
    gCast4.teamworkPaid spObj.id &&
    spEntry.chosenMode == some 0 &&
    spEntry.extraModes == #[1] &&
    spEntry.targets == #[Target.player opp] &&
    spEntry.dividedDamage == #[2] &&
    spEntry.targetsAnnounced &&
    copy1Obj.isCopy &&
    !gCopy1.wasCast copy1Obj.id &&
    !gCopy1.castFromGraveyard copy1Obj.id &&
    !gCopy1.castFromHand copy1Obj.id &&
    !gCopy1.exileInstantSorceryInstead copy1Obj &&
    !gCopy1.treasureManaSpent copy1Obj.id &&
    !gCopy1.isPreparedSpell copy1Obj.id &&
    (gCopy1.boastExiledOf copy1Obj.id).isEmpty &&
    copy1Obj.chosenX == some 3 &&
    gCopy1.wasKicked copy1Obj.id &&
    gCopy1.giftPromisedTo? copy1Obj.id == some opp &&
    gCopy1.teamworkPaid copy1Obj.id &&
    gCopy1.sneakPaid copy1Obj.id &&
    gCopy1.sneakAttackWhom? copy1Obj.id == some opp &&
    gCopy1.sneakAttackTarget? copy1Obj.id == some (.player opp) &&
    copy1Obj.adventurerCard == some bear &&
    copyTrigObj.reflexiveResolution == some (.draw (.fixed 2) .you) &&
    copyTrigObj.fraCauseId == some ⟨71⟩ &&
    copyTrigObj.fraCauseController == some opp &&
    copyTrigObj.fraCausePower == some 4 &&
    copyTrigObj.fraCauseStatus == some { counters := #[(.plusOnePlusOne, 2)] } &&
    gCopyTrig.lastKnownPowerOf? copyTrigObj.id == some 5 &&
    gCopyTrig.lastKnownToughnessOf? copyTrigObj.id == some 6 &&
    gCopy1.lastKnownPowerOf? copy1Obj.id == some 5 &&
    gCopy1.lastKnownToughnessOf? copy1Obj.id == some 6 &&
    copy1Entry.chosenMode == some 0 &&
    copy1Entry.extraModes == #[1] &&
    copy1Entry.targets == #[Target.player opp] &&
    copy1Entry.dividedDamage == #[2] &&
    copy1Entry.targetsAnnounced &&
    copiedEvents.size == 2 &&
    copiedEvents.all (fun (orig, _, ctrl, _) => orig == spId && ctrl == me) &&
    copiedEvents.any (fun (_, _, _, c) => c == cryoCause) &&
    copiedEvents.any (fun (_, _, _, c) => c == lokiCause) &&
    hasTrigPutOnStack &&
    hasRemovedOnResolution &&
    hasSpellRemovedOnResolution &&
    allRulesEventsClassified gLand1 &&
    allRulesEventsClassified gCast4 &&
    allRulesEventsClassified gCopy1 &&
    allRulesEventsClassified gCryoLoki &&
    allRulesEventsClassified gTrig1 &&
    allRulesEventsClassified gTrig3 &&
    allRulesEventsClassified gFizzle2

/- Phase 6: `matchTriggers (pre : GameSnapshot) (post : Game) (batch : Array GameEvent)`
evaluates all triggers at outermost batch close, covers CR 603.10a–f look-back
via `pre`, records `TriggerQueueEvent.triggered`
with `cause := .gameRule .triggeredAbility`, and queries once-each-turn
triggers from the event log instead of `Status.firedOnceEachTurn`. -/
#guard
  -- 1. Simultaneous deaths (CR 603.10a): two creatures with "whenever another
  --    creature you control dies" dying in the same batch both see each other
  --    on `pre` and both trigger.
  let deathWatcherAb : TriggeredAbility :=
    .triggered (.fra .anotherCreatureOrPlaneswalkerYouControlDies)
      { resolution := .gainLife (.fixed 1), phrase := "You gain 1 life" }
      {}
  let deathWatcherDef : CardDef :=
    { bear with
      name := "Simultaneous Watcher"
      triggeredAbilities := #[deathWatcherAb] }
  let gSim0 :=
    addPermanent (addPermanent (quiet afterDraw) deathWatcherDef me me) deathWatcherDef me me
  let watchers := gSim0.battlefield.filter (·.name == "Simultaneous Watcher")
  let w1 := watchers[0]!
  let w2 := watchers[1]!
  let simCause : EventCause := .oneShotEffect (some ⟨90⟩) none (some me)
  let gSim1 :=
    gSim0.withBatch (some simCause) fun g =>
      let g := g.moveToOwnerGraveyard w1 "w1 dies" (verb := some .destroy) (cause := some simCause)
      g.moveToOwnerGraveyard w2 "w2 dies" (verb := some .destroy) (cause := some simCause)
  let simTrigSources := gSim1.waitingTriggers.map (·.source.id)
  let simTrigEvents := gSim1.events.filterMap (fun e =>
    match e with
    | .rules _ (.triggerQueue (.triggered src ctrl ab origin)) c b =>
      some (src.id, ctrl, ab, origin, c, b)
    | _ => none)
  let simDeathsOk :=
    simTrigSources.size == 2 &&
    simTrigSources.contains w1.id &&
    simTrigSources.contains w2.id &&
    simTrigEvents.size == 2 &&
    simTrigEvents.all (fun (_, ctrl, ab, origin, cause, bid) =>
      ctrl == me && ab == deathWatcherAb && origin == bid &&
        cause == .gameRule .triggeredAbility)
  -- 3. Phasing out (CR 603.10b / 702.26b / 702.26d): phasing out emits a
  --    look-back `phasedOut` event, does not fire `.leaving` triggers, and a
  --    watcher that phases out in the same simultaneous batch as a dying
  --    creature still sees the death in `pre`.
  let leaveWatcherAb : TriggeredAbility :=
    .triggered .leaving
      { resolution := .gainLife (.fixed 2), phrase := "You gain 2 life" }
      {}
  let phaserDef : CardDef :=
    { bear with
      name := "Phasing Watcher"
      triggeredAbilities := #[leaveWatcherAb, deathWatcherAb] }
  let gPhase0 :=
    addPermanent (addPermanent (quiet afterDraw) phaserDef me me) bear me me
  let phaser := (gPhase0.battlefield.filter (·.name == "Phasing Watcher"))[0]!
  let victim := (gPhase0.battlefield.filter (·.name == bear.name))[0]!
  let phaseCause : EventCause := .oneShotEffect (some ⟨91⟩) none (some me)
  let gPhaseOnly := gPhase0.phaseOut phaser (cause := some phaseCause)
  let phaseOutNoLeaveOk :=
    gPhaseOnly.waitingTriggers.isEmpty &&
    gPhaseOnly.events.any (fun e =>
      match e.change with
      | .rules (.permanent (.phasedOut snap false)) =>
        snap.id == some phaser.id
      | _ => false)
  let gPhaseAndDie :=
    gPhase0.withBatch (some (.oneShotEffect (some ⟨91⟩) none (some me))) fun g =>
      let g := g.phaseOut phaser
      g.moveToOwnerGraveyard victim "Bear dies" (verb := some .destroy)
        (cause := some (.oneShotEffect (some ⟨91⟩) none (some me)))
  let phaseLookBackOk :=
    gPhaseAndDie.waitingTriggers.size == 1 &&
    gPhaseAndDie.waitingTriggers[0]!.source.id == phaser.id &&
    gPhaseAndDie.waitingTriggers[0]!.ability == deathWatcherAb
  -- 4. Once-each-turn triggers are tracked via `TriggerQueueEvent.triggered`
  --    in `g.events` (`g.loggedTriggeredThisTurn`) rather than `Status`.
  let onceAb : TriggeredAbility :=
    .triggered .youGainLife
      { resolution := .scry 1, phrase := "Scry 1" }
      { onceEachTurn := true }
  let onceDef : CardDef :=
    { bear with
      name := "Once Life Watcher"
      triggeredAbilities := #[onceAb] }
  let gOnce0 := addPermanent (quiet afterDraw) onceDef me me
  let onceObj := (gOnce0.battlefield.filter (·.name == "Once Life Watcher"))[0]!
  let gOnce1 := gOnce0.gainLife me 1 (cause := some (.oneShotEffect (some ⟨92⟩) none (some me)))
  let gOnce2 := gOnce1.gainLife me 1 (cause := some (.oneShotEffect (some ⟨93⟩) none (some me)))
  let gOnceNextTurn :=
    (gOnce2.record (GameEvent.turnBegan (gOnce2.turnNumber + 1) me)).gainLife me 1
      (cause := some (.oneShotEffect (some ⟨94⟩) none (some me)))
  let onceEachTurnOk :=
    gOnce1.loggedTriggeredThisTurn onceObj.id onceAb &&
    gOnce1.waitingTriggers.size == 1 &&
    gOnce2.waitingTriggers.size == 1 &&
    gOnceNextTurn.waitingTriggers.size == 2
  -- 5. Simultaneous batch damage to an attacking Hulk increments
  --    `enrageGrantsAdditionalCombat` once per batch, and `sourceDealtDamage`
  --    sums damage across packets/events in the batch before replicating
  --    `extraTriggerCopies` across distinct abilities.
  let hulkEnrageAb : TriggeredAbility :=
    .triggered .sourceDealtDamage (Effect.ofTrigger (.watch .hulk)) {}
  let hulkDef : CardDef :=
    { bear with
      name := "Test Hulk"
      power := some 6
      toughness := some 6
      triggeredAbilities := #[hulkEnrageAb] }
  let gHulk0 := addPermanent (quiet afterDraw) hulkDef me me
  let hulk0 := (gHulk0.battlefield.filter (·.name == "Test Hulk"))[0]!
  let gHulk0 := gHulk0.markAttacking hulk0.id
  let hulkCause : EventCause := .oneShotEffect (some ⟨95⟩) none (some me)
  let gHulkBatch :=
    gHulk0.withBatch (some hulkCause) fun g =>
      let h := g.object! hulk0.id
      let g := g.dealDamageToPermanent h 1 (source := some (g.snapshot h)) (cause := some hulkCause)
      let h := g.object! hulk0.id
      g.dealDamageToPermanent h 2 (source := some (g.snapshot h)) (cause := some hulkCause)
  let hulkBatchOk :=
    gHulkBatch.waitingTriggers.size == 1 &&
    gHulkBatch.waitingTriggers[0]!.lastKnownPower == some 3
  let dmgAb1 : TriggeredAbility :=
    .triggered .sourceDealtDamage
      { resolution := .gainLife (.fixed 1), phrase := "You gain 1 life" }
      {}
  let dmgAb2 : TriggeredAbility :=
    .triggered .sourceDealtDamage
      { resolution := .scry 1, phrase := "Scry 1" }
      {}
  let dmgWatcherDef : CardDef :=
    { bear with
      name := "Dual Damage Watcher"
      triggeredAbilities := #[dmgAb1, dmgAb2] }
  let doublerDef : CardDef :=
    { bear with
      name := "Trigger Doubler"
      staticAbilities := #[.extraTriggerAnotherYouControl #[] #[.creature]] }
  let gDmg0 :=
    addPermanent (addPermanent (quiet afterDraw) dmgWatcherDef me me) doublerDef me me
  let dmgWatcher := (gDmg0.battlefield.filter (·.name == "Dual Damage Watcher"))[0]!
  let dmgCause : EventCause := .oneShotEffect (some ⟨96⟩) none (some me)
  let gDmgBatch :=
    gDmg0.withBatch (some dmgCause) fun g =>
      let w := g.object! dmgWatcher.id
      let g := g.dealDamageToPermanent w 1 (source := some (g.snapshot w)) (cause := some dmgCause)
      let w := g.object! dmgWatcher.id
      g.dealDamageToPermanent w 1 (source := some (g.snapshot w)) (cause := some dmgCause)
  let dmgTrigEvents := gDmgBatch.events.filter (fun e =>
    match e.change with
    | .rules (.triggerQueue (.triggered ..)) => true
    | _ => false)
  let dmgBatchCopiesOk :=
    gDmgBatch.waitingTriggers.size == 4 &&
    (gDmgBatch.waitingTriggers.filter (·.ability == dmgAb1)).size == 2 &&
    (gDmgBatch.waitingTriggers.filter (·.ability == dmgAb2)).size == 2 &&
    gDmgBatch.waitingTriggers.all (·.lastKnownPower == some 2) &&
    dmgTrigEvents.size == 4
  simDeathsOk &&
    phaseOutNoLeaveOk &&
    phaseLookBackOk &&
    onceEachTurnOk &&
    hulkBatchOk &&
    dmgBatchCopiesOk &&
    allRulesEventsClassified gSim1 &&
    allRulesEventsClassified gPhaseOnly &&
    allRulesEventsClassified gPhaseAndDie &&
    allRulesEventsClassified gHulkBatch &&
    allRulesEventsClassified gDmgBatch

/- Phase 7 isolation (CR 614.5): each `ReplacementId` in `applied` applies at
most once to an event or any modified event that replaced it, even when
multiple replacement specs remain structurally applicable after the first
modification or share a `ReplacementId`. -/
#guard
  let gTerm0 := addPermanent (quiet afterDraw) bear me me
  let bTerm := (gTerm0.battlefield.filter (·.name == "Event Bear"))[0]!
  let idAddCtr : ReplacementId := { kind := .addCountersPut, object := some bTerm.id }
  let idMulCtr : ReplacementId := { kind := .multiplyCountersPut, object := some bTerm.id }
  let repDupA : ReplacementSpec :=
    { id := idAddCtr, source := some bTerm.id, controller := some me,
      affectedPlayer := me, kind := .modifyCountersPut (some bTerm.id) (some .plusOnePlusOne) (add := 1) (mult := 1) }
  let repDupB : ReplacementSpec :=
    { id := idAddCtr, source := some bTerm.id, controller := some me,
      affectedPlayer := me, kind := .modifyCountersPut (some bTerm.id) (some .plusOnePlusOne) (add := 10) (mult := 1) }
  let repSecond : ReplacementSpec :=
    { id := idMulCtr, source := some bTerm.id, controller := some me,
      affectedPlayer := me, kind := .modifyCountersPut (some bTerm.id) (some .plusOnePlusOne) (add := 0) (mult := 2) }
  let gTerm1 :=
    ((gTerm0.createEffect (.replacement repDupA)).createEffect
      (.replacement repDupB)).createEffect (.replacement repSecond)
  let baseCause : EventCause := .oneShotEffect (some ⟨701⟩) none (some me)
  let gTermPaused :=
    (quiet gTerm1).addPlusOnePlusOneTo (gTerm1.object! bTerm.id) 2 (cause := some baseCause)
  let gTerm2 :=
    ((quiet gTermPaused).apply me (.chooseReplacement idAddCtr)).toOption.getD gTermPaused
  -- `idAddCtr` applies once (2 -> 3), the duplicate `idAddCtr` is skipped by CR 614.5,
  -- and `idMulCtr` applies once (3 -> 6), then the loop terminates.
  let termCounterEvents := gTerm2.events.filter (fun e =>
    match e.change with
    | .rules (.permanent (.counters _ .plusOnePlusOne (.put n) _)) => n == 6
    | _ => false)
  (gTerm2.object! bTerm.id).status.plusOnePlusOne == 6 &&
    termCounterEvents.size == 1 &&
    termCounterEvents[0]!.cause? ==
      some (.replaced idMulCtr (.replaced idAddCtr baseCause)) &&
    allRulesEventsClassified gTerm2

/- Phase 7 isolation (CR 614.6): a replaced event never happens (is never
recorded in `g.events`), so abilities watching the replaced event do not
trigger, and the modified event carries `EventCause.replaced`. -/
#guard
  -- 2a. Death replaced by finality counter exile (CR 122.1h / 614.6).
  let diesWatcherAb : TriggeredAbility :=
    .triggered .dies
      { resolution := .gainLife (.fixed 5), phrase := "You gain 5 life" }
      {}
  let finalityBearDef : CardDef :=
    { bear with
      name := "Finality Bear"
      triggeredAbilities := #[diesWatcherAb] }
  let gFin0 := addPermanent (quiet afterDraw) finalityBearDef me me
  let finBear0 := (gFin0.battlefield.filter (·.name == "Finality Bear"))[0]!
  let gFin1 := gFin0.recordPutCounters finBear0.id .finality 1 (some me)
    (cause := some (.oneShotEffect (some ⟨702⟩) none (some me)))
  let finDeathCause : EventCause := .oneShotEffect (some ⟨703⟩) none (some me)
  let gFin2 :=
    (quiet gFin1).moveToOwnerGraveyard (gFin1.object! finBear0.id) "dies"
      (verb := some .destroy) (cause := some finDeathCause)
  let finHasGyMove := gFin2.events.any (fun e =>
    match e.change with
    | .rules (.zone (.moved _ _ .battlefield (.graveyard _) ..)) => true
    | _ => false)
  let finExileMoves := gFin2.events.filter (fun e =>
    match e.change with
    | .rules (.zone (.moved before _ .battlefield .exile .destroy _ _ _)) =>
      before.id == some finBear0.id
    | _ => false)
  let finalityId : ReplacementId := { kind := .finalityCounterExile, object := some finBear0.id }
  -- 2b. Destruction replaced by shield counter removal (CR 122.1c / 614.6).
  let gShd0 := addPermanent (quiet afterDraw) bear me me
  let shdBear0 := (gShd0.battlefield.filter (·.name == "Event Bear"))[0]!
  let gShd1 := gShd0.recordPutCounters shdBear0.id .shield 1 (some me)
    (cause := some (.oneShotEffect (some ⟨704⟩) none (some me)))
  let shdDestroyCause : EventCause := .oneShotEffect (some ⟨705⟩) none (some me)
  let gShd2 :=
    (quiet gShd1).destroyPermanent (gShd1.object! shdBear0.id) (cause := some shdDestroyCause)
  let shdId : ReplacementId := { kind := .shieldCounterDestroy, object := some shdBear0.id }
  let shdRemovedEvents := gShd2.events.filter (fun e =>
    match e.change with
    | .rules (.permanent (.counters (.object o) .shield (.removed 1) _)) =>
      o.id == some shdBear0.id
    | _ => false)
  -- 2c. Untap during untap step replaced by stun counter removal (CR 122.1d / 614.6).
  let gStun0 := addPermanent (quiet afterDraw) bear me me
  let stunBear0 := (gStun0.battlefield.filter (·.name == "Event Bear"))[0]!
  let gStun1 :=
    (gStun0.becomeTapped (gStun0.object! stunBear0.id)
      (cause := some (.oneShotEffect (some ⟨706⟩) none (some me)))).recordPutCounters
      stunBear0.id .stun 1 (some me)
      (cause := some (.oneShotEffect (some ⟨707⟩) none (some me)))
  let gStun2 := (quiet gStun1).beginStep .untap
  let stunId : ReplacementId := { kind := .stunCounterUntap, object := some stunBear0.id }
  let stunUntapEvents := gStun2.events.filter (fun e =>
    match e.change with
    | .rules (.permanent (.untapped o)) => o.id == some stunBear0.id
    | _ => false)
  let stunRemovedEvents := gStun2.events.filter (fun e =>
    match e.change with
    | .rules (.permanent (.counters (.object o) .stun (.removed 1) _)) =>
      o.id == some stunBear0.id
    | _ => false)
  -- 2d. Draw replaced by two draws (`drawTwoExceptFirstDrawStep`, CR 614.11 / 121.2).
  let drawReplaceDef : CardDef :=
    { bear with
      name := "Draw Replacer"
      drawTwoExceptFirstDrawStep := true }
  let gDrw0 := addPermanent (quiet afterDraw) drawReplaceDef me me
  let drwReplacer := (gDrw0.battlefield.filter (·.name == "Draw Replacer"))[0]!
  let drwCause : EventCause := .oneShotEffect (some ⟨708⟩) none (some me)
  let gDrw1 := (quiet gDrw0).draw me 1 (cause := some drwCause)
  let drwRepId : ReplacementId := { kind := .drawTwoExceptFirstDrawStep, object := some drwReplacer.id }
  let drwMoves := gDrw1.events.filter (fun e =>
    match e.change with
    | .rules (.zone (.moved _ _ (.library _) (.hand _) (.draw _) _ _ _)) => true
    | _ => false)
  -- 2e. Damage prevented by a prevention effect (CR 615.1 / 615.6).
  let gPrev0 := addPermanent (quiet afterDraw) bear me me
  let prevBear := (gPrev0.battlefield.filter (·.name == "Event Bear"))[0]!
  let prevSpec : PreventionSpec :=
    { id := { kind := .preventAllDamageToPermanent, object := some prevBear.id }, source := some prevBear.id, controller := some me,
      affectedPlayer := me, kind := .preventAllDamageToPermanent prevBear.id }
  let gPrev1 := gPrev0.createEffect (.prevention prevSpec)
  let prevCause : EventCause := .oneShotEffect (some ⟨709⟩) none (some me)
  let gPrev2 :=
    (quiet gPrev1).dealDamageToPermanent (gPrev1.object! prevBear.id) 3
      (source := some (gPrev1.snapshot prevBear)) (cause := some prevCause)
  let prevDealtEvents := gPrev2.events.filter (fun e =>
    match e.change with
    | .rules (.damage (.dealt ..)) => true
    | _ => false)
  let prevPreventedEvents := gPrev2.events.filter (fun e =>
    match e.change with
    | .rules (.damage (.prevented _ (.permanent p) 3)) => p.id == prevBear.id
    | _ => false)
  !finHasGyMove &&
    gFin2.waitingTriggers.isEmpty &&
    finExileMoves.size == 1 &&
    finExileMoves[0]!.cause? == some (.replaced finalityId finDeathCause) &&
    gShd2.events.all (fun e =>
      match e.change with
      | .rules (.zone (.moved ..)) => false
      | _ => true) &&
    (gShd2.object! shdBear0.id).zone == .battlefield &&
    (gShd2.object! shdBear0.id).status.shield == 0 &&
    shdRemovedEvents.size == 1 &&
    shdRemovedEvents[0]!.cause? == some (.replaced shdId shdDestroyCause) &&
    stunUntapEvents.isEmpty &&
    (gStun2.object! stunBear0.id).status.tapped &&
    (gStun2.object! stunBear0.id).status.stun == 0 &&
    stunRemovedEvents.size == 1 &&
    stunRemovedEvents[0]!.cause? == some (.replaced stunId (.turnBased .untapAll)) &&
    drwMoves.size == 2 &&
    drwMoves.all (fun e => e.cause? == some (.replaced drwRepId drwCause)) &&
    prevDealtEvents.isEmpty &&
    prevPreventedEvents.size == 1 &&
    prevPreventedEvents[0]!.cause? == some (.replaced prevSpec.id prevCause) &&
    (gPrev2.object! prevBear.id).status.damage == 0 &&
    allRulesEventsClassified gFin2 &&
    allRulesEventsClassified gShd2 &&
    allRulesEventsClassified gStun2 &&
    allRulesEventsClassified gDrw1 &&
    allRulesEventsClassified gPrev2

/- Phase 7 isolation (CR 616.1a–e): priority ordering (`self` -> `control` ->
`copy` -> `backFaceUp` -> `other`) applies in strict tier order even when
`g.replacementOrder` lists lower-priority tiers first. -/
#guard
  let dfcBackFace : CardDef :=
    { bear with name := "Back Face Bear", power := some 5, toughness := some 5 }
  let dfcFrontDef : CardDef :=
    { bear with
      name := "Front Face Bear"
      otherFace := some dfcBackFace }
  let copyTemplateDef : CardDef :=
    { hero with name := "Template Hero", otherFace := some dfcBackFace }
  let gTier0 :=
    insertObject (quiet afterDraw) dfcFrontDef opp (.hand opp)
  let enterCardId :=
    ((gTier0.player opp).hand.filter (fun id => (gTier0.object! id).name == "Front Face Bear"))[0]!
  let enteredExpectedId : ObjectId := ⟨gTier0.nextObjectId⟩
  let idSelf : ReplacementId :=
    { kind := .entersWithPlusOneCounters, object := some enteredExpectedId }
  let idControl : ReplacementId := { kind := .entersUnderControl }
  let idCopy : ReplacementId := { kind := .entersAsCopy }
  let idBack : ReplacementId := { kind := .entersBackFaceUp }
  let idOther : ReplacementId := { kind := .entersWithExtraCounters }
  let specSelf : ReplacementSpec :=
    { id := idSelf, source := some enteredExpectedId, controller := some opp,
      affectedPlayer := opp, kind := .entersWithCountersSelf enteredExpectedId .plusOnePlusOne 1 }
  let specControl : ReplacementSpec :=
    { id := idControl, source := none, controller := some me,
      affectedPlayer := opp, kind := .entersUnderControl none me }
  let specCopy : ReplacementSpec :=
    { id := idCopy, source := none, controller := some me,
      affectedPlayer := me, kind := .entersAsCopy none copyTemplateDef }
  let specBack : ReplacementSpec :=
    { id := idBack, source := none, controller := some me,
      affectedPlayer := me, kind := .entersBackFaceUp none }
  let specOther : ReplacementSpec :=
    { id := idOther, source := none, controller := some me,
      affectedPlayer := me, kind := .entersWithExtraCounters none .plusOnePlusOne 2 }
  let gTier1 :=
    (((((gTier0.createEffect (.replacement specSelf)).createEffect
        (.replacement specControl)).createEffect
        (.replacement specCopy)).createEffect
        (.replacement specBack)).createEffect
        (.replacement specOther)).change
      (.replacementOrder #[idOther, idBack, idCopy, idControl, idSelf])
  let etbBaseCause : EventCause := .oneShotEffect (some ⟨710⟩) none (some me)
  let enterCandidate : GameObject :=
    { (gTier1.object! enterCardId) with
      id := enteredExpectedId, controller := some opp, defaultController := some opp }
  let etbRes :=
    gTier1.applyEtbReplacements enterCandidate (cause := some etbBaseCause)
  let (gTier2, enteredPermId) :=
    (quiet gTier1).putOntoBattlefield enterCardId opp (cause := some etbBaseCause)
  let enteredPerm := gTier2.object! enteredPermId
  etbRes.applied == #[idSelf, idControl, idCopy, idBack, idOther] &&
    enteredPermId == enteredExpectedId &&
    enteredPerm.controller == some me &&
    enteredPerm.name == "Back Face Bear" &&
    enteredPerm.status.transformed &&
    !enteredPerm.status.tapped &&
    enteredPerm.status.plusOnePlusOne == 3 &&
    etbRes.cause ==
      some (.replaced idOther
        (.replaced idBack
          (.replaced idCopy
            (.replaced idControl
              (.replaced idSelf etbBaseCause))))) &&
    allRulesEventsClassified gTier2

/- Phase 7 isolation (CR 616.1e): player-chosen ordering within tier `616.1e`
(`g.replacementOrder` and `Pending.chooseReplacement` / `Action.chooseReplacement`),
resumption of paused events, non-sticky consumption of `replacementOrder`,
rejection of out-of-band `Action.chooseReplacement`, non-resolving `wrapReplacedCause`
preserving `nextEffectId`, `createAndMarkTokensAttacking` single-pass token
replacements, single-pass `replaceDamage` in `dealDamageFrom` / `dealDamageToPermanent`,
and Arwen + Doc Samson ETB counter replacement. -/
#guard
  let gOrd0 := addPermanent (quiet afterDraw) bear me me
  let ordBear := (gOrd0.battlefield.filter (·.name == "Event Bear"))[0]!
  let idAddDmg : ReplacementId := { kind := .addNoncombatDamage, object := some ordBear.id }
  let idMulDmg : ReplacementId := { kind := .multiplyDamage, object := some ordBear.id }
  let specAddDmg : ReplacementSpec :=
    { id := idAddDmg, source := some ordBear.id, controller := some me,
      affectedPlayer := opp, kind := .addNoncombatDamage (some ordBear.id) 2 }
  let specMulDmg : ReplacementSpec :=
    { id := idMulDmg, source := some ordBear.id, controller := some me,
      affectedPlayer := opp, kind := .multiplyDamage (some ordBear.id) 2 }
  let gOrd1 :=
    (gOrd0.createEffect (.replacement specAddDmg)).createEffect
      (.replacement specMulDmg)
  -- Out-of-band `Action.chooseReplacement` is rejected when no `.chooseReplacement` is pending.
  let outOfBandRejected :=
    match gOrd1.apply opp (.chooseReplacement idAddDmg) with
    | .error _ => true
    | .ok _ => false
  -- Live prompt: dealing 3 noncombat damage with both +2 and *2 active pauses on `.chooseReplacement`.
  let dmgOrdCause : EventCause := .oneShotEffect (some ⟨711⟩) none (some me)
  let gDmgPaused :=
    (quiet gOrd1).dealDamageToPlayer opp 3
      (source := some (gOrd1.object! ordBear.id)) (cause := some dmgOrdCause)
  let pausedPromptOk :=
    gDmgPaused.pending == .chooseReplacement opp #[idAddDmg, idMulDmg] &&
    (gDmgPaused.player opp).life == (gOrd0.player opp).life
  -- Choosing `idAddDmg` first resumes the damage event: (3 + 2) * 2 = 10 damage, and consumes `replacementOrder`.
  let gDmgAddFirst :=
    ((quiet gDmgPaused).apply opp (.chooseReplacement idAddDmg)).toOption.getD gDmgPaused
  -- Choosing `idMulDmg` first resumes the damage event: (3 * 2) + 2 = 8 damage, and consumes `replacementOrder`.
  let gDmgMulFirst :=
    ((quiet gDmgPaused).apply opp (.chooseReplacement idMulDmg)).toOption.getD gDmgPaused
  -- A subsequent damage event on `gDmgAddFirst` prompts again because `replacementOrder` was consumed.
  let gDmgSecondPaused :=
    (quiet gDmgAddFirst).dealDamageToPlayer opp 3
      (source := some (gDmgAddFirst.object! ordBear.id)) (cause := some dmgOrdCause)
  -- Competing graveyard replacements (Finality counter exile vs Head of the Hunt exile + Wolf trigger) prompt `chooseReplacement`.
  let gFinComp0 := addPermanent (addPermanent (quiet afterDraw) bear me me)
    { bear with name := "Head of the Hunt Test", staticAbilities := #[.exileOppDeathCreateWolf] } opp opp
  let finCompBear := (gFinComp0.battlefield.filter (·.name == "Event Bear"))[0]!
  let headSource := (gFinComp0.battlefield.filter (·.name == "Head of the Hunt Test"))[0]!
  let idFinExile : ReplacementId := { kind := .finalityCounterExile, object := some finCompBear.id }
  let idHeadWolf : ReplacementId := { kind := .exileOppDeath, object := some headSource.id }
  let gFinComp1 :=
    gFinComp0.recordPutCounters finCompBear.id .finality 1 (some me)
      (cause := some (.oneShotEffect (some ⟨713⟩) none (some me)))
  let gFinCompPaused :=
    (quiet gFinComp1).moveToOwnerGraveyard (gFinComp1.object! finCompBear.id) "dies"
      (verb := some .destroy) (cause := some (.oneShotEffect (some ⟨714⟩) none (some me)))
  let gFinChoseHead :=
    ((quiet gFinCompPaused).apply me (.chooseReplacement idHeadWolf)).toOption.getD gFinCompPaused
  let gFinChoseExile :=
    ((quiet gFinCompPaused).apply me (.chooseReplacement idFinExile)).toOption.getD gFinCompPaused
  let finChoiceOk :=
    gFinCompPaused.pending == .chooseReplacement me #[idFinExile, idHeadWolf] &&
    gFinChoseHead.objects.any (fun o => o.zone == .exile && o.name == "Event Bear") &&
    (gFinChoseHead.waitingTriggers.size + gFinChoseHead.stack.size) == 1 &&
    gFinChoseExile.objects.any (fun o => o.zone == .exile && o.name == "Event Bear") &&
    (gFinChoseExile.waitingTriggers.size + gFinChoseExile.stack.size) == 0
  -- Non-resolving replacement (`cause := none` outside a resolving spell/ability) does not mint an `EffectId`.
  let effBefore := gOrd1.nextEffectId
  let wrappedNonResolving := gOrd1.wrapReplacedCause idAddDmg none (some me)
  let nonResolvingCauseOk :=
    wrappedNonResolving == some (.replaced idAddDmg (.gameRule .continuousEffect)) &&
    gOrd1.nextEffectId == effBefore
  -- `createAndMarkTokensAttacking` with a token doubler + token-kind replacement applies each once.
  let specDoubleTok : ReplacementSpec :=
    { id := { kind := .multiplyTokenCreation, object := some ordBear.id }, source := some ordBear.id, controller := some me,
      affectedPlayer := me, kind := .multiplyTokenCreation me 2 }
  let specFoodTok : ReplacementSpec :=
    { id := { kind := .artifactTokensBecome, object := some ordBear.id }, source := some ordBear.id, controller := some me,
      affectedPlayer := me, kind := .artifactTokensBecome me foodToken }
  let gAtkTok0 :=
    ((gOrd0.createEffect (.replacement specDoubleTok)).createEffect
      (.replacement specFoodTok)).change (.resolvingAbility (some ordBear.id))
  let gAtkTok1 :=
    (quiet gAtkTok0).createAndMarkTokensAttacking me .treasure 1 false true
  let atkTokFoods := gAtkTok1.battlefield.filter (·.name == foodToken.name)
  let atkTokOk := atkTokFoods.size == 2
  -- Single-pass `replaceDamage` on `dealDamageFrom` and `dealDamageToPermanent` with a shield counter.
  let gShdDmg0 :=
    addPermanent (addPermanent (quiet afterDraw) bear me me)
      { bear with name := "Attacker Bear" } opp opp
  let shdVictim := (gShdDmg0.battlefield.filter (·.name == "Event Bear"))[0]!
  let shdAttacker := (gShdDmg0.battlefield.filter (·.name == "Attacker Bear"))[0]!
  let shdRepId : ReplacementId := { kind := .shieldCounterPreventDamage, object := some shdVictim.id }
  let gShdDmg1 :=
    gShdDmg0.recordPutCounters shdVictim.id .shield 1 (some me)
      (cause := some (.oneShotEffect (some ⟨715⟩) none (some me)))
  let shdDmgCause : EventCause := .oneShotEffect (some ⟨716⟩) none (some opp)
  let gShdFrom :=
    (quiet gShdDmg1).dealDamageFrom "Attacker Bear" (gShdDmg1.object! shdVictim.id) 2
      (source := some (gShdDmg1.object! shdAttacker.id)) (cause := some shdDmgCause)
  let shdFromRemoved := gShdFrom.events.filter (fun e =>
    match e.change with
    | .rules (.permanent (.counters (.object o) .shield (.removed 1) _)) =>
      o.id == some shdVictim.id
    | _ => false)
  let singlePassDamageOk :=
    (gShdFrom.object! shdVictim.id).status.shield == 0 &&
    (gShdFrom.object! shdVictim.id).status.damage == 0 &&
    shdFromRemoved.size == 1 &&
    shdFromRemoved[0]!.cause? == some (.replaced shdRepId shdDmgCause)
  -- Arwen (`othersEnterWithPlusOneEqualToughness := true`) + Doc Samson (`.extraCounterOnPermanents`) ETB counter replacement.
  let samsonDef : CardDef :=
    { bear with name := "Doc Samson Test", staticAbilities := #[.extraCounterOnPermanents] }
  let arwenDef : CardDef :=
    { bear with name := "Arwen Test", toughness := some 2, othersEnterWithPlusOneEqualToughness := true }
  let gArw0 :=
    insertObject
      (addPermanent (addPermanent (quiet afterDraw) samsonDef me me) arwenDef me me)
      { bear with name := "Newcomer Bear" } me (.hand me)
  let newcomerCardId :=
    ((gArw0.player me).hand.filter (fun id => (gArw0.object! id).name == "Newcomer Bear"))[0]!
  let arwCause : EventCause := .oneShotEffect (some ⟨717⟩) none (some me)
  let (gArw1, newcomerPermId) :=
    (quiet gArw0).putOntoBattlefield newcomerCardId me (cause := some arwCause)
  let arwenMovedBagOk := gArw1.events.any (fun e =>
    match e.change with
    | .rules (.zone (.moved _ after _ .battlefield _ _ bag _)) =>
      after.id == some newcomerPermId && bag.any (fun (k, c) => k == .plusOnePlusOne && c == 3)
    | _ => false)
  let arwenSamsonOk :=
    (gArw1.object! newcomerPermId).status.plusOnePlusOne == 3 &&
    arwenMovedBagOk
  -- Life gain replacement choice (`+2` vs `*2`) and APNAP tie-breaking.
  let idAddLife : ReplacementId := { kind := .addLifeGain, object := some ordBear.id }
  let idMulLife : ReplacementId := { kind := .multiplyLifeGain, object := some ordBear.id }
  let specAddLife : ReplacementSpec :=
    { id := idAddLife, source := some ordBear.id, controller := some me,
      affectedPlayer := me, kind := .modifyLifeGain me (add := 2) (mult := 1) }
  let specMulLife : ReplacementSpec :=
    { id := idMulLife, source := some ordBear.id, controller := some me,
      affectedPlayer := me, kind := .modifyLifeGain me (add := 0) (mult := 2) }
  let gLife0 :=
    (gOrd0.createEffect (.replacement specAddLife)).createEffect
      (.replacement specMulLife)
  let lifeCause : EventCause := .oneShotEffect (some ⟨712⟩) none (some me)
  let gLifePaused := (quiet gLife0).gainLife me 3 (cause := some lifeCause)
  let gLifeAddFirst :=
    ((quiet gLifePaused).apply me (.chooseReplacement idAddLife)).toOption.getD gLifePaused
  let gLifeMulFirst :=
    ((quiet gLifePaused).apply me (.chooseReplacement idMulLife)).toOption.getD gLifePaused
  let idLifeMe : ReplacementId := { kind := .addLifeGain, player := some me }
  let idLifeOpp : ReplacementId := { kind := .addLifeGain, player := some opp }
  let candMe : ReplacementCandidate :=
    (ReplacementOrPrevention.replacement {
      id := idLifeMe, affectedPlayer := me, kind := .modifyLifeGain me 1 1 }).toCandidate
  let candOpp : ReplacementCandidate :=
    (ReplacementOrPrevention.replacement {
      id := idLifeOpp, affectedPlayer := opp, kind := .modifyLifeGain opp 1 1 }).toCandidate
  let gActiveMe := gOrd0.record (GameEvent.turnBegan gOrd0.turnNumber me)
  let gActiveOpp := gOrd0.record (GameEvent.turnBegan (gOrd0.turnNumber + 1) opp)
  -- Simultaneous graveyard move and SBA sweep resumption across multiple dying creatures.
  let finSetupCause : EventCause := .oneShotEffect (some ⟨718⟩) none (some me)
  let gSim0 := addPermanent gFinComp1 { bear with name := "Sim Dying Two" } me me
  let simC1 := (gSim0.battlefield.filter (·.name == "Event Bear"))[0]!
  let simC2 := (gSim0.battlefield.filter (·.name == "Sim Dying Two"))[0]!
  let gSim0 := gSim0.recordPutCounters simC2.id .finality 1 (some me)
    (cause := some finSetupCause)
  let c1FinId : ReplacementId := { kind := .finalityCounterExile, object := some simC1.id }
  let c2FinId : ReplacementId := { kind := .finalityCounterExile, object := some simC2.id }
  let gSimPaused1 := (quiet gSim0).moveSimultaneousToGraveyard #[simC1.id, simC2.id]
    (cause := some finSetupCause)
  let gSimPaused2 :=
    (gSimPaused1.apply me (.chooseReplacement c1FinId)).toOption.getD gSimPaused1
  let gSimDone :=
    (gSimPaused2.apply me (.chooseReplacement c2FinId)).toOption.getD gSimPaused2
  let simMoveBatches := gSimDone.events.filterMap (fun e =>
    match e.change with
    | .rules (.zone (.moved ..)) => some e.batch
    | _ => none)
  let simMoveOk :=
    gSimPaused1.pending == .chooseReplacement me #[c1FinId, idHeadWolf] &&
    gSimPaused2.pending == .chooseReplacement me #[c2FinId, idHeadWolf] &&
    gSimDone.pending == .none &&
    !gSimDone.battlefield.any (fun o => o.id == simC1.id || o.id == simC2.id) &&
    simMoveBatches.size == 2 && simMoveBatches[0]! == simMoveBatches[1]!
  -- SBA sweep: Creature 1 has lethal damage + Finality + Head of the Hunt; Creature 2 has lethal damage.
  -- Choosing Finality on Creature 1 queues no trigger, and Creature 2 still dies in the same SBA batch.
  let gSba0 :=
    setMarkedDamage (setMarkedDamage gSim0 simC1.id 2) simC2.id 2
  let gSbaPaused := (quiet gSba0).checkSBA
  let gSbaAfter1 :=
    (gSbaPaused.apply me (.chooseReplacement c1FinId)).toOption.getD gSbaPaused
  let gSbaDone :=
    (gSbaAfter1.apply me (.chooseReplacement c2FinId)).toOption.getD gSbaAfter1
  let sbaMoveBatches := gSbaDone.events.filterMap (fun e =>
    match e.change with
    | .rules (.zone (.moved ..)) => some e.batch
    | _ => none)
  let sbaResumeOk :=
    gSbaPaused.pending == .chooseReplacement me #[c1FinId, idHeadWolf] &&
    gSbaAfter1.pending == .chooseReplacement me #[c2FinId, idHeadWolf] &&
    gSbaDone.pending == .none &&
    !gSbaDone.battlefield.any (fun o => o.id == simC1.id || o.id == simC2.id) &&
    sbaMoveBatches.size == 2 && sbaMoveBatches[0]! == sbaMoveBatches[1]!
  -- `fightCreatures` chains the second creature's fight damage after a replacement choice on the first.
  let gFight0 :=
    addPermanent (addPermanent gOrd0 { bear with name := "Fighter A" } me me)
      { bear with name := "Fighter B", toughness := some 10 } opp opp
  let fighterA := (gFight0.battlefield.filter (·.name == "Fighter A"))[0]!
  let fighterB := (gFight0.battlefield.filter (·.name == "Fighter B"))[0]!
  let idFightAdd : ReplacementId := { kind := .addNoncombatDamage, object := some fighterA.id }
  let idFightMul : ReplacementId := { kind := .multiplyDamage, object := some fighterA.id }
  let gFight0 :=
    (gFight0.createEffect (.replacement {
      id := idFightAdd, source := some fighterA.id, controller := some me,
      affectedPlayer := opp, kind := .addNoncombatDamage (some fighterA.id) 2 })
      (cause := some dmgOrdCause)).createEffect
      (.replacement {
        id := idFightMul, source := some fighterA.id, controller := some me,
        affectedPlayer := opp, kind := .multiplyDamage (some fighterA.id) 2 })
      (cause := some dmgOrdCause)
  let gFightPaused := (quiet gFight0).fightCreatures (gFight0.object! fighterA.id)
    (gFight0.object! fighterB.id) (cause := some dmgOrdCause)
  let gFightDone :=
    (gFightPaused.apply opp (.chooseReplacement idFightAdd)).toOption.getD gFightPaused
  let fightBatches := gFightDone.events.filterMap (fun e =>
    match e.change with
    | .rules (.damage (.dealt ..)) => some e.batch
    | _ => none)
  let fightResumeOk :=
    gFightPaused.pending == .chooseReplacement opp #[idFightAdd, idFightMul] &&
    gFightDone.pending == .none &&
    (gFightDone.object! fighterB.id).status.damage == 8 &&
    (gFightDone.object! fighterA.id).status.damage == 2 &&
    fightBatches.size == 2 && fightBatches[0]! == fightBatches[1]!
  -- `finishEnteringAttackCard` stops on a `.counter` mod that opens `.chooseReplacement` before running `afterPermanentEnters`.
  let gEntAtk0 :=
    insertObject gOrd0 { bear with name := "Entering Striker" } me (.hand me)
  let strikerHandId :=
    ((gEntAtk0.player me).hand.filter (fun id => (gEntAtk0.object! id).name == "Entering Striker"))[0]!
  let (gEntAtk0, strikerId) :=
    (quiet gEntAtk0).putOntoBattlefield strikerHandId me (cause := some arwCause)
  let idCtrAdd : ReplacementId := { kind := .addCountersPut, object := some strikerId }
  let idCtrMul : ReplacementId := { kind := .multiplyCountersPut, object := some strikerId }
  let gEntAtk0 :=
    (gEntAtk0.createEffect (.replacement {
      id := idCtrAdd, source := some strikerId, controller := some me,
      affectedPlayer := me, kind := .modifyCountersPut (some strikerId) (some .plusOnePlusOne) (add := 1) (mult := 1) })
      (cause := some arwCause)).createEffect
      (.replacement {
        id := idCtrMul, source := some strikerId, controller := some me,
        affectedPlayer := me, kind := .modifyCountersPut (some strikerId) (some .plusOnePlusOne) (add := 0) (mult := 2) })
      (cause := some arwCause)
  let gEntAtkPaused := gEntAtk0.finishEnteringAttackCard strikerId me "Entering Striker"
    [.counter .plusOnePlusOne 1 false, .counter .shield 1 false] .putOntoBattlefield (cause := some arwCause)
  let gEntAtkDone :=
    (gEntAtkPaused.apply me (.chooseReplacement idCtrAdd)).toOption.getD gEntAtkPaused
  let entAtkOk :=
    gEntAtkPaused.pending == .chooseReplacement me #[idCtrAdd, idCtrMul] &&
    (gEntAtkPaused.object! strikerId).status.shield == 0 &&
    gEntAtkDone.pending == .none &&
    (gEntAtkDone.object! strikerId).status.plusOnePlusOne == 4 &&
    (gEntAtkDone.object! strikerId).status.shield == 1
  -- Draw-step sub-draw pause: a `replaceDraw me 2 false` draws the first card of the draw step,
  -- then the second sub-draw pauses on competing `exceptFirst := true` replacements without restarting the first draw.
  let idDrwAll : ReplacementId := { kind := .replaceDraw, player := some me }
  let idDrwEx2 : ReplacementId := { kind := .drawTwoExceptFirstDrawStep, player := some me }
  let idDrwEx3 : ReplacementId := { kind := .drawThreeExceptFirstDrawStep, player := some me }
  let drwSubCause : EventCause := .oneShotEffect (some ⟨719⟩) none (some me)
  let gDrwSub0 :=
    (((((quiet started).record (GameEvent.turnBegan started.turnNumber me)).record
      (GameEvent.stepBegan started.turnNumber .draw me)).createEffect
      (.replacement {
        id := idDrwAll, source := none, controller := some me,
        affectedPlayer := me, kind := .replaceDraw me 2 false })
      (cause := some drwSubCause)).createEffect
      (.replacement {
        id := idDrwEx2, source := none, controller := some me,
        affectedPlayer := me, kind := .replaceDraw me 2 true })
      (cause := some drwSubCause))
    |>.createEffect
      (.replacement {
        id := idDrwEx3, source := none, controller := some me,
        affectedPlayer := me, kind := .replaceDraw me 3 true })
      (cause := some drwSubCause)
  let handBeforeDrwSub := (gDrwSub0.player me).hand.size
  let gDrwSubPaused := (quiet gDrwSub0).draw me 1
  let gDrwSubDone :=
    (gDrwSubPaused.apply me (.chooseReplacement idDrwEx2)).toOption.getD gDrwSubPaused
  let drwSubResumeOk :=
    gDrwSubPaused.pending == .chooseReplacement me #[idDrwEx2, idDrwEx3] &&
    (gDrwSubPaused.player me).hand.size - handBeforeDrwSub == 1 &&
    gDrwSubDone.pending == .none &&
    (gDrwSubDone.player me).hand.size - handBeforeDrwSub == 7
  -- `commitEnteringAttackItems` pauses on an as-enters `.fraChoice` (`asEntersChooseOddEven`) before putting the second card onto the battlefield, keeping both in one batch.
  let oddEvenDef1 : CardDef := { bear with name := "Parity Striker 1", asEntersChooseOddEven := true }
  let oddEvenDef2 : CardDef := { bear with name := "Parity Striker 2", asEntersChooseOddEven := true }
  let gFraEnt0 :=
    insertObject
      (insertObject gOrd0 oddEvenDef1 me (.hand me))
      oddEvenDef2 me (.hand me)
  let pCard1 := ((gFraEnt0.player me).hand.filter (fun id => (gFraEnt0.object! id).name == "Parity Striker 1"))[0]!
  let pCard2 := ((gFraEnt0.player me).hand.filter (fun id => (gFraEnt0.object! id).name == "Parity Striker 2"))[0]!
  let item1 : EnteringAttackItem :=
    .card pCard1 me me true false #[] [] .putOntoBattlefield #[.player opp]
  let item2 : EnteringAttackItem :=
    .card pCard2 me me true false #[] [] .putOntoBattlefield #[.player opp]
  let gFraEntPaused1 :=
    (quiet gFraEnt0).commitEnteringAttackItems #[(item1, some (.player opp)), (item2, some (.player opp))]
      (cause := some arwCause)
  let gFraEntPaused2 :=
    (gFraEntPaused1.apply me (.chooseMode 0)).toOption.getD gFraEntPaused1
  let entered1Id := ((gFraEntPaused2.battlefield.filter (·.name == "Parity Striker 1"))[0]!).id
  let gFraEntDone :=
    (gFraEntPaused2.apply me (.chooseMode 1)).toOption.getD gFraEntPaused2
  let entered2Id := ((gFraEntDone.battlefield.filter (·.name == "Parity Striker 2"))[0]!).id
  let entAtkFraBatches := gFraEntDone.events.filterMap (fun e =>
    match e.change with
    | .rules (.zone (.moved ..)) => some e.batch
    | _ => none)
  let entAtkFraOk :=
    (match gFraEntPaused1.pending with
     | .chooseReplacement p cs =>
       p == me && cs.any (fun c => c.object == some entered1Id && c.kind == .asEntersChooseOdd false)
     | _ => false) &&
    !gFraEntPaused1.battlefield.any (·.name == "Parity Striker 1") &&
    (match gFraEntPaused2.pending with
     | .chooseReplacement p cs =>
       p == me && cs.any (fun c => c.object == some entered2Id && c.kind == .asEntersChooseOdd true)
     | _ => false) &&
    (gFraEntPaused2.object! entered1Id).status.chosenOdd == some false &&
    gFraEntDone.pending == .none &&
    (gFraEntDone.object! entered2Id).status.chosenOdd == some true &&
    entAtkFraBatches.size == 2 && entAtkFraBatches[0]! == entAtkFraBatches[1]!
  -- `dealAssignedCombatDamage` consumes `replacementOrder` per damage packet rather than leaking across blockers (CR 616.1).
  let cbtLifelinkDef : CardDef :=
    { bear with name := "Lifelink Striker", keywords := { lifelink := true } }
  let idCbtMul : ReplacementId := { kind := .multiplyDamage }
  let idCbtLifeAdd : ReplacementId := { kind := .addLifeGain, player := some me }
  let idCbtLifeMul : ReplacementId := { kind := .multiplyLifeGain, player := some me }
  let gCbt0 :=
    addPermanent
      (addPermanent
        (addPermanent (quiet afterDraw) cbtLifelinkDef me me)
        { bear with name := "Second Striker" } me me)
      { bear with name := "Shield Blocker" } opp opp
  let cbtAtk1 := (gCbt0.battlefield.filter (·.name == "Lifelink Striker"))[0]!
  let cbtAtk2 := (gCbt0.battlefield.filter (·.name == "Second Striker"))[0]!
  let cbtBlk := (gCbt0.battlefield.filter (·.name == "Shield Blocker"))[0]!
  let idCbtBlkShield : ReplacementId := { kind := .shieldCounterPreventDamage, object := some cbtBlk.id }
  let gCbt1 :=
    (((((gCbt0.recordPutCounters cbtBlk.id .shield 1 (some opp)
          (cause := some (.oneShotEffect (some ⟨720⟩) none (some opp)))).createEffect
        (.replacement {
          id := idCbtMul, source := none, controller := some me,
          affectedPlayer := opp, kind := .multiplyDamage none 2 })
        (cause := some drwSubCause)).createEffect
        (.replacement {
          id := idCbtLifeAdd, source := none, controller := some me,
          affectedPlayer := me, kind := .modifyLifeGain me 2 1 })
        (cause := some drwSubCause)).createEffect
        (.replacement {
          id := idCbtLifeMul, source := none, controller := some me,
          affectedPlayer := me, kind := .modifyLifeGain me 0 2 })
        (cause := some drwSubCause)).change (.replacementOrder #[idCbtMul])).record
      (GameEvent.rules gCbt0.turnNumber (.combat (.damageAssigned false true #[
        { source := cbtAtk1.id, toCreatures := #[], toPlayer := 2 },
        { source := cbtAtk2.id, toCreatures := #[(cbtBlk.id, 2)], toPlayer := 0 }
      ])) (.turnBased (.assignCombatDamage false)))
  let gCbtPaused := (quiet gCbt1).dealAssignedCombatDamage
  let gCbtAfterDmg :=
    (gCbtPaused.apply opp (.chooseReplacement idCbtMul)).toOption.getD gCbtPaused
  let gCbtDone :=
    (gCbtAfterDmg.apply me (.chooseReplacement idCbtLifeAdd)).toOption.getD gCbtAfterDmg
  let cbtLifelinkOrderOk :=
    gCbtPaused.pending == .chooseReplacement opp #[idCbtBlkShield, idCbtMul] &&
    gCbtPaused.replacementOrder.isEmpty &&
    gCbtAfterDmg.pending == .chooseReplacement me #[idCbtLifeAdd, idCbtLifeMul] &&
    gCbtDone.pending == .none &&
    gCbtDone.replacementOrder.isEmpty &&
    (gCbt1.player opp).life - (gCbtDone.player opp).life == 4 &&
    (gCbtDone.player me).life - (gCbt1.player me).life == 12 &&
    (gCbtDone.object! cbtBlk.id).status.shield == 0 &&
    (gCbtDone.object! cbtBlk.id).status.damage == 0
  outOfBandRejected &&
    pausedPromptOk &&
    gDmgAddFirst.pending == Pending.none &&
    gDmgAddFirst.replacementOrder.isEmpty &&
    gDmgMulFirst.pending == Pending.none &&
    gDmgMulFirst.replacementOrder.isEmpty &&
    gDmgSecondPaused.pending == .chooseReplacement opp #[idAddDmg, idMulDmg] &&
    (gOrd0.player opp).life - (gDmgAddFirst.player opp).life == 10 &&
    (gOrd0.player opp).life - (gDmgMulFirst.player opp).life == 8 &&
    finChoiceOk &&
    nonResolvingCauseOk &&
    atkTokOk &&
    singlePassDamageOk &&
    arwenSamsonOk &&
    simMoveOk &&
    sbaResumeOk &&
    fightResumeOk &&
    entAtkOk &&
    drwSubResumeOk &&
    entAtkFraOk &&
    cbtLifelinkOrderOk &&
    (gLifeAddFirst.player me).life - (gOrd0.player me).life == 10 &&
    (gLifeMulFirst.player me).life - (gOrd0.player me).life == 8 &&
    (gActiveMe.selectNextReplacementStep #[candOpp, candMe] #[]) == .chosen candMe #[] &&
    (gActiveOpp.selectNextReplacementStep #[candOpp, candMe] #[]) == .chosen candOpp #[] &&
    allRulesEventsClassified gDmgAddFirst &&
    allRulesEventsClassified gDmgMulFirst &&
    allRulesEventsClassified gFinChoseHead &&
    allRulesEventsClassified gFinChoseExile &&
    allRulesEventsClassified gShdFrom &&
    allRulesEventsClassified gArw1 &&
    allRulesEventsClassified gSimDone &&
    allRulesEventsClassified gSbaDone &&
    allRulesEventsClassified gFightDone &&
    allRulesEventsClassified gEntAtkDone &&
    allRulesEventsClassified gDrwSubDone &&
    allRulesEventsClassified gFraEntDone &&
    allRulesEventsClassified gCbtDone &&
    allRulesEventsClassified gLifeAddFirst &&
    allRulesEventsClassified gLifeMulFirst

/- Phase 8 isolation (CR 611 / 613):
1. `ContinuousEffectEvent` (`created` / `expired`) and `ContinuousEffectSpec`
   evaluate Layers 1–7 (`copy`, `control`, `text`, `types` with `ObjectScope`
   dependency CR 613.8, `colors`, `abilities` add/remove, and `7a`–`7d` P/T
   sublayers `ptCda`, `ptSet`, `ptModify`, `ptSwitch`) purely from `g.activeEffects`.
2. `DelayedTrigger` (`CR 603.7`) table (`g.delayedTriggers`), including
   `.enrageAdditionalCombat` (`oneShot := true`).
3. `CounterBag` (`Status.counters` single source of truth), expanded `PlayerEvent`
   (`ringTempted`, `tookInitiative`, `completedDungeon`, `becameMonarch`,
   `ascended`, `becameDay`, `becameNight`), `CR 400.7d` cast metadata across
   `.stack -> .battlefield`, and `ContinuationFrame` stack (`g.continuations`). -/
#guard
  let g0 := addPermanent (addPermanent (quiet afterDraw) bear me me) hero me me
  let b := (g0.battlefield.filter (·.name == "Event Bear"))[0]!
  let h := (g0.battlefield.filter (·.name == "Event Hero"))[0]!
  let cause8 : EventCause := .oneShotEffect (some ⟨801⟩) (some h.id) (some me)
  -- Layer 3 (text), Layer 4 (types + conditional scope CR 613.8), Layer 5 (colors),
  -- Layer 6 (abilities add/remove), and Layer 7a–7d (ptCda, ptSet, ptModify, ptSwitch):
  -- Even when 7d (`ptSwitch`), 7c (`ptModify`), and 7b (`ptSet`) are created out of
  -- sublayer order, CR 613.4 applies 7b (4/1) -> 7c (+2/+3 = 6/4 +1/+1 counter = 7/5) -> 7d (5/7).
  let gLayers :=
    (((((((g0.recordPutCounters b.id .plusOnePlusOne 1 (some me) (cause := some cause8)).createEffect
        (.layered (.objects #[b.id]) .ptSwitch .untilEndOfTurn) (cause := some cause8)).createEffect
        (.layered (.objects #[b.id]) (.ptModify 2 3) .untilEndOfTurn) (cause := some cause8)).createEffect
        (.layered (.objects #[b.id]) (.ptSet 4 1) .untilEndOfTurn) (cause := some cause8)).createEffect
        (.layered (.objects #[b.id]) (.text (.replaceCreatureType .bear .elf)) .untilEndOfTurn) (cause := some cause8)).createEffect
        (.layered (.creaturesControlledBy me) (.types .add #[.artifact] #[.construct] #[.legendary]) .untilEndOfTurn) (cause := some cause8)).createEffect
        (.layered (.objects #[b.id]) (.colors .set { blue := true }) .untilEndOfTurn) (cause := some cause8)).createEffect
        (.layered (.objects #[b.id]) (.abilities { keywords := Keyword.flying } .none) .untilEndOfTurn) (cause := some cause8)
  let bAfter := gLayers.object! b.id
  let layersOk :=
    gLayers.power bAfter == 5 &&
    gLayers.toughness bAfter == 7 &&
    (gLayers.subtypes bAfter).contains .elf &&
    !(gLayers.subtypes bAfter).contains .bear &&
    (gLayers.subtypes bAfter).contains .construct &&
    gLayers.isArtifact bAfter &&
    gLayers.isLegendary bAfter &&
    gLayers.colors bAfter == ({ blue := true } : ColorSet) &&
    gLayers.hasFlying bAfter &&
    bAfter.status.counters == #[(.plusOnePlusOne, 1)]
  -- Delayed trigger `.endStepSacrifice` (CR 603.7): fires at `.end` step and removes itself (`isOneShot == true`).
  let gDelayed0 :=
    (g0.registerDelayedTrigger {
      controller := me
      source := some h
      kind := .endStepSacrifice b.id
      cause := cause8 }).record (GameEvent.stepBegan g0.turnNumber .postcombatMain g0.activePlayer)
  let gDelayed1 := (quiet gDelayed0).beginStep .end
  let delayedOk :=
    !gDelayed1.delayedTriggers.any (·.kind == .endStepSacrifice b.id) &&
    gDelayed1.stack.size == g0.stack.size + 1
  -- Expanded `PlayerEvent`s (`ringTempted`, `becameMonarch`, `gainedDesignation`) and `TurnEvent.dayNightChanged`
  let gPlEv :=
    (((((quiet g0).record (GameEvent.ringTempted g0.turnNumber me (some b.id) 1 (cause := some cause8))).record
      (GameEvent.becameMonarch g0.turnNumber me (cause := some cause8))).record
      (GameEvent.gainedDesignation g0.turnNumber me .citysBlessing (cause := some cause8))).record
      (GameEvent.rules g0.turnNumber (.turn (.dayNightChanged true)) cause8)).record
      (GameEvent.rules g0.turnNumber (.turn (.dayNightChanged false)) cause8)
  let plEvOk :=
    (gPlEv.player me).ringBearerId == some b.id &&
    (gPlEv.player me).theRingAbilities == 1 &&
    (gPlEv.player me).isMonarch &&
    (gPlEv.player me).citysBlessing &&
    !gPlEv.isNight
  -- ContinuationFrame stack (`g.continuations`): nested frame isolates scratch state and restores outer frame on pop.
  let gCont0 := (g0.change (.pushContinuationFrame {})).change (.continuation (.notedCountThisWay 7))
  let gContPushed := (gCont0.change (.pushContinuationFrame {})).change (.continuation (.notedCountThisWay 99))
  let gContInner :=
    if gContPushed.notedCountThisWay == 99 then gContPushed.change .popContinuationFrame
    else (gContPushed.change (.continuation (.notedCountThisWay 0))).change .popContinuationFrame
  let contOk :=
    gCont0.notedCountThisWay == 7 &&
    gContPushed.notedCountThisWay == 99 &&
    gContInner.notedCountThisWay == 7 &&
    gContInner.continuations.size == gCont0.continuations.size
  layersOk &&
    delayedOk &&
    plEvOk &&
    contOk &&
    allRulesEventsClassified gLayers &&
    allRulesEventsClassified gDelayed1 &&
    allRulesEventsClassified gPlEv

/- Extra-turn cause alignment when a lost player's extra turn is skipped
(CR 500.7 / 800.4k): `pendingExtraCauses` pops alongside `extraTurns` so the
surviving player's extra turn inherits its own cause, not the skipped player's. -/
#guard
  let opp : PlayerId := ⟨1⟩
  let g0 := quiet afterDraw
  let causeMe1 : EventCause := .oneShotEffect (some ⟨901⟩) none (some me)
  let causeMe2 : EventCause := .oneShotEffect (some ⟨902⟩) none (some me)
  let causeOpp : EventCause := .oneShotEffect (some ⟨903⟩) none (some opp)
  let gQueued :=
    (((g0.record (GameEvent.extraTurnAdded g0.turnNumber me .current (cause := causeMe1))).record
        (GameEvent.extraTurnAdded g0.turnNumber me .current (cause := causeMe2))).record
        (GameEvent.extraTurnAdded g0.turnNumber opp .current (cause := causeOpp))).record
        (GameEvent.playerLost g0.turnNumber opp .effect (cause := some causeMe1))
  let gExtra1 := gQueued.startNextTurn
  let powerUpsCause? (g : Game) : Option EventCause :=
    g.events.findSomeRev? fun e =>
      match e.change with
      | .rules (.continuousEffect (.created _ .powerUpsForbiddenThisTurn)) => e.cause?
      | _ => none
  let gExtra2 := (gExtra1.clearEOT).startNextTurn
  gQueued.extraTurns == #[opp, me, me] &&
    gExtra1.activePlayer == me &&
    gExtra1.extraTurns == #[me] &&
    powerUpsCause? gExtra1 == some causeMe2 &&
    gExtra2.activePlayer == me &&
    gExtra2.extraTurns.isEmpty &&
    powerUpsCause? gExtra2 == some causeMe1 &&
    allRulesEventsClassified gExtra2

/- `.untilEndOfNextTurnOf` play permissions and control effects (CR 514.2 /
611.2a): `.turnBased .cleanupClear` events emitted during the creation turn's
cleanup step (and any CR 514.3a extra cleanup or an opponent's turn) do not
count as a turn of `p` beginning, so both last until cleanup of `p`'s next turn. -/
#guard
  let opp : PlayerId := ⟨1⟩
  let g0 := addPermanent (addPermanent (quiet afterDraw) bear opp opp) hero me me
  let b := (g0.battlefield.filter (·.name == "Event Bear"))[0]!
  let h := (g0.battlefield.filter (·.name == "Event Hero"))[0]!
  let causeNext : EventCause := .oneShotEffect (some ⟨910⟩) (some h.id) (some me)
  let (g1, exId) := g0.move h.id .exile none (cause := some causeNext)
  let gInit :=
    (((g1.changeControl (g1.object! b.id) me (turnEndsLeft := 2)).createEffect
        (.playPermission exId { player := me } (turnEnds := 2)) (cause := some causeNext)).createEffect
        (.keywordsUntilEot b.id Keyword.haste) (cause := some causeNext)).record
        (GameEvent.damageMarked g1.turnNumber b.id 1 (cause := causeNext))
  let hasPlayPerm (g : Game) : Bool :=
    g.activeEffects.any fun (_, s) =>
      match s with
      | .permission p (.playFromExile oid _) _ => p == some me && oid == exId
      | _ => false
  -- Turn 1 cleanup (emits `.cleanupClear` events from haste expiration and marked damage)
  let gClean1 := gInit.clearEOT
  let hadCleanupClear := gClean1.events.any (fun e => e.cause? == some (.turnBased .cleanupClear))
  -- Second CR 514.3a cleanup in Turn 1
  let gClean1b := gClean1.clearEOT
  -- Advance to `opp`'s turn and run `opp`'s cleanup
  let gOppTurn := gClean1b.startNextTurn
  let gOppClean := gOppTurn.clearEOT
  -- Advance to `me`'s next turn (`TurnEvent.turnBegan me false` recorded)
  let gMeNext := gOppClean.startNextTurn
  -- Cleanup of `me`'s next turn finally expires both
  let gMeNextClean := gMeNext.clearEOT
  hadCleanupClear &&
    !gClean1.hasHaste (gClean1.object! b.id) &&
    gClean1.controllerOf (gClean1.object! b.id) == some me &&
    gClean1.controlTurnEndsLeft (gClean1.object! b.id) == 2 &&
    hasPlayPerm gClean1 &&
    gClean1b.controllerOf (gClean1b.object! b.id) == some me &&
    hasPlayPerm gClean1b &&
    gOppTurn.activePlayer == opp &&
    gOppClean.controllerOf (gOppClean.object! b.id) == some me &&
    gOppClean.controlTurnEndsLeft (gOppClean.object! b.id) == 2 &&
    hasPlayPerm gOppClean &&
    gMeNext.activePlayer == me &&
    gMeNext.controllerOf (gMeNext.object! b.id) == some me &&
    gMeNext.controlTurnEndsLeft (gMeNext.object! b.id) == 1 &&
    hasPlayPerm gMeNext &&
    gMeNextClean.controllerOf (gMeNextClean.object! b.id) == some opp &&
    gMeNextClean.controlTurnEndsLeft (gMeNextClean.object! b.id) == 0 &&
    !hasPlayPerm gMeNextClean

/- Layer 4 CR 613.7 timestamp order and CR 613.8 dependency ordering:
1. Later object-scoped `.set` overrides an earlier `.creaturesControlledBy`
   type-adding effect without re-adding the overwritten type.
2. Earlier `.creaturesControlledBy` waits for a later `.additionalCreature` on
   a noncreature permanent (CR 613.8) and then applies to it.
3. `.notACreature`, `.returnedAsArtifact`, and `.onlyFoodArtifact` apply at
   their own timestamps instead of overriding later type/subtype additions. -/
#guard
  let shrineDef : CardDef := enchantment "Event Shrine" ManaCost.empty ""
  let g0 := addPermanent (addPermanent (addPermanent (quiet afterDraw) bear me me) hero me me) shrineDef me me
  let b := (g0.battlefield.filter (·.name == "Event Bear"))[0]!
  let h := (g0.battlefield.filter (·.name == "Event Hero"))[0]!
  let s := (g0.battlefield.filter (·.name == "Event Shrine"))[0]!
  let c1 : EventCause := .oneShotEffect (some ⟨921⟩) none (some me)
  let c2 : EventCause := .oneShotEffect (some ⟨922⟩) none (some me)
  -- 1 & 2: earlier team artifact grant, then `b` becomes Enchantment Creature — God, and `s` becomes a creature
  let gSetOverride :=
    (((g0.createEffect
        (.layered (.creaturesControlledBy me) (.types .add #[.artifact] #[.construct] #[]) .untilEndOfTurn)
        (cause := some c1)).createEffect
        (.layered (.objects #[b.id]) (.types .set #[.enchantment, .creature] #[.god] #[.legendary]) .untilEndOfTurn)
        (cause := some c2)).createEffect
        (.additionalCreature s.id true) (cause := some c2))
  let bSet := gSetOverride.object! b.id
  let hSet := gSetOverride.object! h.id
  let sSet := gSetOverride.object! s.id
  let setAndDepOk :=
    gSetOverride.types bSet == #[.enchantment, .creature] &&
    !gSetOverride.isArtifact bSet &&
    gSetOverride.subtypes bSet == #[.god] &&
    gSetOverride.isLegendary bSet &&
    gSetOverride.isArtifact hSet &&
    (gSetOverride.subtypes hSet).contains .construct &&
    gSetOverride.isEnchantment sSet &&
    gSetOverride.isCreature sSet &&
    gSetOverride.isArtifact sSet &&
    (gSetOverride.subtypes sSet).contains .construct
  -- 3a: `.notACreature` / `.returnedAsArtifact` vs later `.additionalCreature`
  let gNotThenAdd :=
    ((g0.createEffect (.notACreature b.id) (cause := some c1)).createEffect
      (.additionalCreature b.id true) (cause := some c2))
  let gAddThenNot :=
    ((g0.createEffect (.additionalCreature s.id true) (cause := some c1)).createEffect
      (.notACreature s.id) (cause := some c2))
  let gRetThenAdd :=
    ((g0.createEffect (.returnedAsArtifact h.id) (cause := some c1)).createEffect
      (.additionalCreature h.id true) (cause := some c2))
  -- 3b: `.onlyFoodArtifact` vs `.additionalSubtype`
  let gFoodThenTreasure :=
    ((g0.createEffect (.onlyFoodArtifact b.id) (cause := some c1)).createEffect
      (.additionalSubtype b.id .treasure) (cause := some c2))
  let gTreasureThenFood :=
    ((g0.createEffect (.additionalSubtype b.id .treasure) (cause := some c1)).createEffect
      (.onlyFoodArtifact b.id) (cause := some c2))
  setAndDepOk &&
    gNotThenAdd.isCreature (gNotThenAdd.object! b.id) &&
    !gAddThenNot.isCreature (gAddThenNot.object! s.id) &&
    gRetThenAdd.isCreature (gRetThenAdd.object! h.id) &&
    gRetThenAdd.isArtifact (gRetThenAdd.object! h.id) &&
    gFoodThenTreasure.types (gFoodThenTreasure.object! b.id) == #[.artifact] &&
    gFoodThenTreasure.subtypes (gFoodThenTreasure.object! b.id) == #[.food, .treasure] &&
    gTreasureThenFood.subtypes (gTreasureThenFood.object! b.id) == #[.food] &&
    allRulesEventsClassified gSetOverride

/- Layer 6 CR 613.1f / 613.7c / 613.7e keyword-counter and ability-loss ordering:
1. Keyword counters (including `flying`, `shadow`, `deathtouch`, `lifelink`,
   `trample`, `indestructible`) placed BEFORE `.losesAbilitiesUntilEot` or
   BEFORE attaching a loses-abilities Aura are stripped.
2. Keyword counters placed AFTER ability loss grant their keywords while earlier
   printed and counter keywords remain lost.
3. Placing another counter of an earlier kind AFTER ability loss refreshes that
   counter kind's timestamp (CR 613.7c) and restores only that keyword. -/
#guard
  let wingedDef : CardDef :=
    creature "WingedGuard" ManaCost.empty #["Bird"] 2 2 (keywords := Keyword.vigilance)
  let freezeAura : CardDef :=
    { (enchantment "FreezeAura" ManaCost.empty "") with
      subtypes := #["Aura"]
      staticAbilities := #[.enchantedLosesAbilitiesCantUntap] }
  let g0 := addPermanent (addPermanent (quiet afterDraw) wingedDef me me) freezeAura me me
  let w := (g0.battlefield.filter (·.name == "WingedGuard"))[0]!
  let aura := (g0.battlefield.filter (·.name == "FreezeAura"))[0]!
  let c1 : EventCause := .oneShotEffect (some ⟨931⟩) none (some me)
  let c2 : EventCause := .oneShotEffect (some ⟨932⟩) none (some me)
  let c3 : EventCause := .oneShotEffect (some ⟨933⟩) none (some me)
  -- Put counters first, then lose all abilities until EOT
  let gCountersFirst :=
    (((((((g0.recordPutCounters w.id .flying 1 (some me) (cause := some c1)).recordPutCounters
        w.id .shadow 1 (some me) (cause := some c1)).recordPutCounters
        w.id .deathtouch 1 (some me) (cause := some c1)).recordPutCounters
        w.id .lifelink 1 (some me) (cause := some c1)).recordPutCounters
        w.id .trample 1 (some me) (cause := some c1)).recordPutCounters
        w.id .indestructible 1 (some me) (cause := some c1)).createEffect
        (.losesAbilitiesUntilEot w.id) (cause := some c2))
  let wLost := gCountersFirst.object! w.id
  let strippedOk :=
    !gCountersFirst.hasVigilance wLost &&
    !gCountersFirst.hasFlying wLost &&
    !gCountersFirst.hasShadow wLost &&
    !gCountersFirst.hasDeathtouch wLost &&
    !gCountersFirst.hasLifelink wLost &&
    !gCountersFirst.hasTrample wLost &&
    !gCountersFirst.hasIndestructible wLost &&
    gCountersFirst.effectiveKeywords wLost == Keywords.none
  -- Refresh `.flying` counter timestamp (CR 613.7c) and add new `.haste` counter after ability loss
  let gRefreshed :=
    (gCountersFirst.recordPutCounters w.id .flying 1 (some me) (cause := some c3)).recordPutCounters
      w.id .haste 1 (some me) (cause := some c3)
  let wRef := gRefreshed.object! w.id
  let refreshedOk :=
    gRefreshed.hasFlying wRef &&
    gRefreshed.hasHaste wRef &&
    !gRefreshed.hasVigilance wRef &&
    !gRefreshed.hasShadow wRef &&
    !gRefreshed.hasDeathtouch wRef &&
    !gRefreshed.hasLifelink wRef &&
    !gRefreshed.hasTrample wRef &&
    !gRefreshed.hasIndestructible wRef &&
    gRefreshed.effectiveKeywords wRef == { flying := true, haste := true }
  -- Attached loses-abilities Aura ordering (CR 613.7e vs 613.7c):
  -- Counter before attachment is stripped; counter after attachment applies.
  let gBeforeAura :=
    ((g0.recordPutCounters w.id .deathtouch 1 (some me) (cause := some c1)).record
      (GameEvent.attached g0.turnNumber (g0.snapshot aura) w.id (cause := c2))).recordPutCounters
      w.id .lifelink 1 (some me) (cause := some c3)
  let wAura := gBeforeAura.object! w.id
  let auraOk :=
    !gBeforeAura.hasVigilance wAura &&
    !gBeforeAura.hasDeathtouch wAura &&
    gBeforeAura.hasLifelink wAura &&
    gBeforeAura.effectiveKeywords wAura == Keyword.lifelink
  strippedOk && refreshedOk && auraOk &&
    allRulesEventsClassified gRefreshed &&
    allRulesEventsClassified gBeforeAura

/- Layer 6 CR 613.1f / 613.7 timestamp ordering for `triggeredAbilities`,
`matchTriggers` (including subtype-enter and combat-damage token arms),
`hasCantBeBlocked` (Bilbo's Ring and My Precious), and `prowessTriggers`
(printed and Equipment-granted prowess). -/
#guard
  let c1 : EventCause := .oneShotEffect (some ⟨941⟩) none (some me)
  let c2 : EventCause := .oneShotEffect (some ⟨942⟩) none (some me)
  let c3 : EventCause := .oneShotEffect (some ⟨943⟩) none (some me)
  let c4 : EventCause := .oneShotEffect (some ⟨944⟩) none (some me)
  -- 1. Triggered abilities (printed, granted, attached Equipment, subtype-enter, combat-damage token)
  let subEnterAb : TriggeredAbility := .onThisOrAnotherSubtypeEntersCreateTokens "Dwarf" .treasure 1
  let combatTokAb : TriggeredAbility := .onSubtypeYouControlCombatDamageCreateTokens "Dwarf" .treasure 2
  let preGrantAb : TriggeredAbility :=
    TriggeredAbility.fra .attack "Whenever this creature attacks, draw a card." (.draw 1)
  let postGrantAb : TriggeredAbility :=
    TriggeredAbility.fra .attack "Whenever this creature attacks, you gain 2 life." (.gainLife 2)
  let captainDef : CardDef :=
    creature "DwarfCaptain" ManaCost.empty #["Dwarf"] 2 2
      (triggeredAbilities := #[.onAttackScry 1, subEnterAb, combatTokAb])
  let strikerDef : CardDef :=
    creature "DwarfStriker" ManaCost.empty #["Dwarf"] 2 2
  let kitesailDef : CardDef :=
    { name := "Test Kitesail"
      types := #[.artifact]
      subtypes := #["Equipment"]
      staticAbilities := #[.fra .equippedMedicsKitesail] }
  let gT0 :=
    addPermanent
      (addPermanent
        (addPermanent (quiet afterDraw) captainDef me me)
        strikerDef me me)
      kitesailDef me me
  let cap := (gT0.battlefield.filter (·.name == "DwarfCaptain"))[0]!
  let striker := (gT0.battlefield.filter (·.name == "DwarfStriker"))[0]!
  let kitesail := (gT0.battlefield.filter (·.name == "Test Kitesail"))[0]!
  let gEquippedAndGranted :=
    ((gT0.record (GameEvent.attached gT0.turnNumber (gT0.snapshot kitesail) cap.id (cause := c1))).createEffect
      (.grantedTriggered cap.id preGrantAb false) (cause := some c1)).createEffect
      (.grantedTriggered cap.id (.onEnterDraw 1) true) (cause := some c1)
  let beforeTriggerCount := (gEquippedAndGranted.triggeredAbilities (gEquippedAndGranted.object! cap.id)).size
  let gCapLost :=
    gEquippedAndGranted.createEffect (.losesAbilitiesUntilEot cap.id) (cause := some c2)
  let capLostEmpty := (gCapLost.triggeredAbilities (gCapLost.object! cap.id)).isEmpty
  -- Attacking while abilities are lost queues 0 triggers (neither printed, pre-grant, nor Kitesail)
  let atkEv :=
    GameEvent.attackersDeclared gCapLost.turnNumber me
      #[(gCapLost.snapshot (gCapLost.object! cap.id), .player ⟨1⟩)] (cause := some c3)
  let gAtkLost := gCapLost.record atkEv
  -- Dwarf token created OR nontoken Dwarf moved onto battlefield while abilities are lost queues 0 triggers
  let (gEnterTokLost, _) := gCapLost.createToken me strikerDef (cause := some c3)
  let gEnterMoveLost := addPermanent gCapLost strikerDef me me
  -- Striker dealing combat damage to player or battle while DwarfCaptain lost abilities queues 0 triggers
  let strikeSnap := gCapLost.snapshot (gCapLost.object! striker.id)
  let gDmgPlayerLost :=
    gCapLost.record (GameEvent.damagedPlayer gCapLost.turnNumber strikeSnap ⟨1⟩ 2 true (cause := c3))
  let battleSnap : EventObject := { name := "TestBattle", owner := ⟨1⟩, zone := .battlefield }
  let gDmgBattleLost :=
    gCapLost.record
      (GameEvent.rules gCapLost.turnNumber
        (.damage (.dealt #[{ source := strikeSnap, recipient := .battle battleSnap, amount := 2, combat := true }]))
        c3)
  -- Post-removal grant and post-removal re-attachment ARE retained and DO fire
  let gPostGrant :=
    (gCapLost.createEffect (.grantedTriggered cap.id postGrantAb true) (cause := some c3)).record
      (GameEvent.attached gCapLost.turnNumber (gCapLost.snapshot (gCapLost.object! kitesail.id)) cap.id (cause := c4))
  let postTriggers := gPostGrant.triggeredAbilities (gPostGrant.object! cap.id)
  let gAtkPost :=
    gPostGrant.record
      (GameEvent.attackersDeclared gPostGrant.turnNumber me
        #[(gPostGrant.snapshot (gPostGrant.object! cap.id), .player ⟨1⟩)] (cause := some c4))
  let triggersOk :=
    beforeTriggerCount == 6 &&
    capLostEmpty &&
    gAtkLost.waitingTriggers.isEmpty &&
    gEnterTokLost.waitingTriggers.isEmpty &&
    gEnterMoveLost.waitingTriggers.isEmpty &&
    gDmgPlayerLost.waitingTriggers.isEmpty &&
    gDmgBattleLost.waitingTriggers.isEmpty &&
    postTriggers.size == 2 &&
    postTriggers.contains postGrantAb &&
    gAtkPost.waitingTriggers.size == 2
  -- 2. `hasCantBeBlocked` with Bilbo's Ring and My Precious
  let ringDef : CardDef :=
    { name := "Test Ring"
      types := #[.artifact]
      subtypes := #["Equipment"]
      staticAbilities := #[.equippedHexproofUnblockableDuringYourTurn] }
  let preciousDef : CardDef :=
    { name := "Test Precious"
      types := #[.artifact]
      subtypes := #["Equipment"]
      staticAbilities := #[.equippedCreatureHasKeywordsAndCantBeBlocked Keyword.hexproof] }
  let gEq0 :=
    addPermanent
      (addPermanent
        (addPermanent (quiet afterDraw) bear me me)
        ringDef me me)
      preciousDef me me
  let host := (gEq0.battlefield.filter (·.name == "Event Bear"))[0]!
  let ring := (gEq0.battlefield.filter (·.name == "Test Ring"))[0]!
  let precious := (gEq0.battlefield.filter (·.name == "Test Precious"))[0]!
  let gRingPre :=
    gEq0.record (GameEvent.attached gEq0.turnNumber (gEq0.snapshot ring) host.id (cause := c1))
  let gRingLost :=
    gRingPre.createEffect (.losesAbilitiesUntilEot host.id) (cause := some c2)
  let gRingRe :=
    gRingLost.record (GameEvent.attached gRingLost.turnNumber (gRingLost.snapshot (gRingLost.object! ring.id)) host.id (cause := c3))
  let gPrecPre :=
    gEq0.record (GameEvent.attached gEq0.turnNumber (gEq0.snapshot precious) host.id (cause := c1))
  let gPrecLost :=
    gPrecPre.createEffect (.losesAbilitiesUntilEot host.id) (cause := some c2)
  let gPrecRe :=
    gPrecLost.record (GameEvent.attached gPrecLost.turnNumber (gPrecLost.snapshot (gPrecLost.object! precious.id)) host.id (cause := c3))
  let unblockableOk :=
    gRingPre.hasCantBeBlocked (gRingPre.object! host.id) &&
    gRingPre.hasHexproof (gRingPre.object! host.id) &&
    !gRingLost.hasCantBeBlocked (gRingLost.object! host.id) &&
    !gRingLost.hasHexproof (gRingLost.object! host.id) &&
    gRingRe.hasCantBeBlocked (gRingRe.object! host.id) &&
    gRingRe.hasHexproof (gRingRe.object! host.id) &&
    gPrecPre.hasCantBeBlocked (gPrecPre.object! host.id) &&
    gPrecPre.hasHexproof (gPrecPre.object! host.id) &&
    !gPrecLost.hasCantBeBlocked (gPrecLost.object! host.id) &&
    !gPrecLost.hasHexproof (gPrecLost.object! host.id) &&
    gPrecRe.hasCantBeBlocked (gPrecRe.object! host.id) &&
    gPrecRe.hasHexproof (gPrecRe.object! host.id)
  -- 3. `prowessTriggers` with printed prowess and Wizard's Staff
  let mageDef : CardDef :=
    { (creature "ProwessMage" ManaCost.empty #["Wizard"] 1 2 (keywords := Keyword.prowess)) with
      prowessInstances := 1 }
  let staffDef : CardDef :=
    { name := "Test Staff"
      types := #[.artifact]
      subtypes := #["Equipment"]
      staticAbilities := #[.equippedCreatureHasKeywords Keyword.prowess] }
  let gPw0 :=
    addPermanent (addPermanent (quiet afterDraw) mageDef me me) staffDef me me
  let mage := (gPw0.battlefield.filter (·.name == "ProwessMage"))[0]!
  let staff := (gPw0.battlefield.filter (·.name == "Test Staff"))[0]!
  let gPwPre :=
    gPw0.record (GameEvent.attached gPw0.turnNumber (gPw0.snapshot staff) mage.id (cause := c1))
  let gPwLost :=
    gPwPre.createEffect (.losesAbilitiesUntilEot mage.id) (cause := some c2)
  let gPwRe :=
    gPwLost.record (GameEvent.attached gPwLost.turnNumber (gPwLost.snapshot (gPwLost.object! staff.id)) mage.id (cause := c3))
  let prowessOk :=
    (gPwPre.prowessTriggers (gPwPre.object! mage.id)).size == 2 &&
    (gPwLost.prowessTriggers (gPwLost.object! mage.id)).isEmpty &&
    !(gPwLost.effectiveKeywords (gPwLost.object! mage.id)).prowess &&
    (gPwRe.prowessTriggers (gPwRe.object! mage.id)).size == 1 &&
    (gPwRe.effectiveKeywords (gPwRe.object! mage.id)).prowess
  triggersOk && unblockableOk && prowessOk &&
    allRulesEventsClassified gAtkPost &&
    allRulesEventsClassified gRingRe &&
    allRulesEventsClassified gPrecRe &&
    allRulesEventsClassified gPwRe

/- Phase 8 (PR #584 review round 3): `combatDamageCreatesTreasure` (including
attached Reaver Cleaver), `ironFistTapGrants`, `canBlock` (`printed.cantBlock`
vs `.cantBlockUntilEot`), and `wardCostsOn` (printed ward, ward statics,
attached ward Equipment, and lord ward) all evaluate in Layer 6 timestamp
order (CR 613.1f / 613.7 / 702.21). -/
#guard
  let opp : PlayerId := ⟨1⟩
  let c1 : EventCause := .oneShotEffect (some ⟨1001⟩) none (some me)
  let c2 : EventCause := .oneShotEffect (some ⟨1002⟩) none (some me)
  let c3 : EventCause := .oneShotEffect (some ⟨1003⟩) none (some me)
  let c4 : EventCause := .oneShotEffect (some ⟨1004⟩) none (some me)
  -- 1. `combatDamageCreatesTreasure` & Reaver Cleaver timestamp ordering
  let cleaverDef : CardDef :=
    { name := "Test Cleaver"
      types := #[.artifact]
      subtypes := #["Equipment"]
      staticAbilities := #[.equippedGetsTrampleAndCombatTreasures 1 1] }
  let gTr0 := addPermanent (addPermanent (quiet afterDraw) bear me me) cleaverDef me me
  let atk := (gTr0.battlefield.filter (·.name == "Event Bear"))[0]!
  let cleaver := (gTr0.battlefield.filter (·.name == "Test Cleaver"))[0]!
  let gTrPre :=
    ((gTr0.markAttacking atk.id).record
      (GameEvent.attached gTr0.turnNumber (gTr0.snapshot cleaver) atk.id (cause := c1))).createEffect
      (.combatDamageCreatesTreasureUntilEot atk.id) (cause := some c1)
  let gTrLost :=
    gTrPre.createEffect (.losesAbilitiesUntilEot atk.id) (cause := some c2)
  let gTrLostCombat :=
    (((gTrLost.record (GameEvent.rules gTrLost.turnNumber
      (.combat (.damageAssigned false true #[{ source := atk.id, toPlayer := 2 }]))
      (.turnBased (.assignCombatDamage false)))).dealAssignedCombatDamage).receivePriority me).resolveTop
  let gTrRe :=
    gTrLost.record (GameEvent.attached gTrLost.turnNumber (gTrLost.snapshot (gTrLost.object! cleaver.id)) atk.id (cause := c3))
  let gTrReCombat :=
    (((gTrRe.record (GameEvent.rules gTrRe.turnNumber
      (.combat (.damageAssigned false true #[{ source := atk.id, toPlayer := 2 }]))
      (.turnBased (.assignCombatDamage false)))).dealAssignedCombatDamage).receivePriority me).resolveTop
  let gTrPostEff :=
    gTrLost.createEffect (.combatDamageCreatesTreasureUntilEot atk.id) (cause := some c4)
  let countTreasures (g : Game) : Nat :=
    (g.permanentsOf me).filter (fun o => g.hasSubtype o .treasure) |>.size
  let treasureOk :=
    (gTrPre.triggeredAbilities (gTrPre.object! atk.id)).size == 2 &&
    (gTrLost.triggeredAbilities (gTrLost.object! atk.id)).isEmpty &&
    countTreasures gTrLostCombat == 0 &&
    (gTrRe.triggeredAbilities (gTrRe.object! atk.id)).size == 1 &&
    countTreasures gTrReCombat == 2 &&
    (gTrPostEff.triggeredAbilities (gTrPostEff.object! atk.id)).size == 1
  -- 2. `ironFistTapGrants` timestamp ordering (effect removal + Aura removal)
  let stripAuraDef : CardDef :=
    { name := "Strip Aura"
      types := #[.enchantment]
      subtypes := #["Aura"]
      staticAbilities := #[.enchantedLosesAbilitiesCantUntap] }
  let gFist0 := addPermanent (addPermanent (quiet afterDraw) bear me me) stripAuraDef me me
  let fist := (gFist0.battlefield.filter (·.name == "Event Bear"))[0]!
  let stripAura := (gFist0.battlefield.filter (·.name == "Strip Aura"))[0]!
  let gFistPre :=
    (gFist0.createEffect (.ironFistTapUntilEot fist.id) (cause := some c1)).createEffect
      (.ironFistTapUntilEot fist.id) (cause := some c1)
  let gFistLost :=
    gFistPre.createEffect (.losesAbilitiesUntilEot fist.id) (cause := some c2)
  let gFistPost :=
    gFistLost.createEffect (.ironFistTapUntilEot fist.id) (cause := some c3)
  let gFistAuraLost :=
    gFistPost.record (GameEvent.attached gFistPost.turnNumber (gFistPost.snapshot (gFistPost.object! stripAura.id)) fist.id (cause := c4))
  let ironFistOk :=
    gFistPre.ironFistTapGrants (gFistPre.object! fist.id) == 2 &&
    gFistLost.ironFistTapGrants (gFistLost.object! fist.id) == 0 &&
    gFistPost.ironFistTapGrants (gFistPost.object! fist.id) == 1 &&
    gFistAuraLost.ironFistTapGrants (gFistAuraLost.object! fist.id) == 0
  -- 3. `canBlock`: `printed.cantBlock` is removed in Layer 6, `.cantBlockUntilEot` is not
  let cantBlockDef : CardDef :=
    { (creature "Reluctant Blocker" ManaCost.empty #["Human"] 2 2) with
      cantBlock := true }
  let gBlk0 :=
    addPermanent (addPermanent (quiet afterDraw) bear me me) cantBlockDef opp opp
  let attacker := (gBlk0.battlefield.filter (·.name == "Event Bear"))[0]!
  let blocker := (gBlk0.battlefield.filter (·.name == "Reluctant Blocker"))[0]!
  let gBlkAtk := gBlk0.markAttacking attacker.id (some (.player opp))
  let gBlkLost := gBlkAtk.createEffect (.losesAbilitiesUntilEot blocker.id) (cause := some c1)
  let gBlkRule := gBlkLost.createEffect (.cantBlockUntilEot blocker.id) (cause := some c2)
  let gBlkRuleThenLost :=
    (gBlkAtk.createEffect (.cantBlockUntilEot blocker.id) (cause := some c1)).createEffect
      (.losesAbilitiesUntilEot blocker.id) (cause := some c2)
  let canBlockOk :=
    !gBlkAtk.canBlock (gBlkAtk.object! blocker.id) (gBlkAtk.object! attacker.id) &&
    gBlkLost.canBlock (gBlkLost.object! blocker.id) (gBlkLost.object! attacker.id) &&
    !gBlkRule.canBlock (gBlkRule.object! blocker.id) (gBlkRule.object! attacker.id) &&
    !gBlkRuleThenLost.canBlock (gBlkRuleThenLost.object! blocker.id) (gBlkRuleThenLost.object! attacker.id)
  -- 4. `wardCostsOn`: printed ward, ward statics, attached ward Equipment, and lord ward
  let wardHeroDef : CardDef :=
    { (creature "Ward Hero" ManaCost.empty #["Hero"] 3 3) with
      supertypes := #[.legendary]
      ward := some 2
      staticAbilities := #[.wardDiscardOrPay 1] }
  let wardEqDef : CardDef :=
    { name := "Ward Cloak"
      types := #[.artifact]
      subtypes := #["Equipment"]
      staticAbilities := #[.equippedCreatureGetsAndWard 1 1 3] }
  let wardLordDef : CardDef :=
    { (creature "Ward Lord" ManaCost.empty #["Advisor"] 2 2) with
      staticAbilities := #[.legendaryCreaturesGetAndWard 1 1 4] }
  let gWd0 :=
    addPermanent
      (addPermanent
        (addPermanent (quiet afterDraw) wardLordDef me me)
        wardHeroDef me me)
      wardEqDef me me
  let wHero := (gWd0.battlefield.filter (·.name == "Ward Hero"))[0]!
  let wCloak := (gWd0.battlefield.filter (·.name == "Ward Cloak"))[0]!
  let wLord := (gWd0.battlefield.filter (·.name == "Ward Lord"))[0]!
  let gWdPre :=
    gWd0.record (GameEvent.attached gWd0.turnNumber (gWd0.snapshot wCloak) wHero.id (cause := c1))
  let preWards := gWdPre.wardCostsOn (gWdPre.object! wHero.id)
  let gWdLost :=
    gWdPre.createEffect (.losesAbilitiesUntilEot wHero.id) (cause := some c2)
  let lostWards := gWdLost.wardCostsOn (gWdLost.object! wHero.id)
  let gWdRe :=
    addPermanent
      (gWdLost.record (GameEvent.attached gWdLost.turnNumber (gWdLost.snapshot (gWdLost.object! wCloak.id)) wHero.id (cause := c3)))
      wardLordDef me me
  let reWards := gWdRe.wardCostsOn (gWdRe.object! wHero.id)
  let gWdLordLost :=
    gWdPre.createEffect (.losesAbilitiesUntilEot wLord.id) (cause := some c2)
  let lordLostWards := gWdLordLost.wardCostsOn (gWdLordLost.object! wHero.id)
  let wardOk :=
    preWards.size == 4 &&
    preWards.contains (.genericMana 2) &&
    preWards.contains (.discardOrPay 1) &&
    preWards.contains (.genericMana 3) &&
    preWards.contains (.genericMana 4) &&
    lostWards.isEmpty &&
    reWards == #[.genericMana 3, .genericMana 4] &&
    lordLostWards.size == 3 &&
    !lordLostWards.contains (.genericMana 4)
  treasureOk && ironFistOk && canBlockOk && wardOk &&
    allRulesEventsClassified gTrReCombat &&
    allRulesEventsClassified gFistAuraLost &&
    allRulesEventsClassified gWdRe

/- Phase 8 (PR #584 review round 4): `cantLoseGame` (battlefield + command zone),
`opponentsCantWin`, `unspentManaBecomesColorless`, `planeswalkersYouControlHave`
(timestamp order + Layer 4 `isPlaneswalker`), `grantedManaAbilities`
(`otherSubtypeHaveTapAddOneOf` + `grantCreaturesTapAddAnyColor` in timestamp
order), and `intrinsicLandMana` / `landsCouldProduce` (`grantLandsTapAnyColor` +
land ability removal) all obey Layer 6 (CR 104.2a / 106.7 / 605.1a / 613.1f / 613.7). -/
#guard
  let opp : PlayerId := ⟨1⟩
  let c1 : EventCause := .oneShotEffect (some ⟨1101⟩) none (some me)
  let c2 : EventCause := .oneShotEffect (some ⟨1102⟩) none (some me)
  -- 1. `cantLoseGame` & `opponentsCantWin` (battlefield + command zone)
  let angelDef : CardDef :=
    { (creature "Platinum Test" ManaCost.empty #["Angel"] 4 4) with
      cantLoseGame := true
      opponentsCantWin := true }
  let gAngel0 :=
    (addPermanent (quiet afterDraw) angelDef me me).setLifeTotal me 0
  let angel := (gAngel0.battlefield.filter (·.name == "Platinum Test"))[0]!
  let gAngelPre := gAngel0.checkSBA
  let gAngelLost :=
    (gAngel0.createEffect (.losesAbilitiesUntilEot angel.id) (cause := some c1)).checkSBA
  let (gCmd0, cmdObj) :=
    ((quiet afterDraw).setLifeTotal me 0).allocObject angelDef me .command (some me)
  let gCmdPre := gCmd0.checkSBA
  let gCmdLost :=
    (gCmd0.createEffect (.losesAbilitiesUntilEot cmdObj.id) (cause := some c1)).checkSBA
  let cantLoseWinOk :=
    !(gAngelPre.player me).lost &&
    gAngelPre.result.isNone &&
    (gAngelLost.player me).lost &&
    gAngelLost.result == some (.won opp) &&
    !(gCmdPre.player me).lost &&
    gCmdPre.result.isNone &&
    (gCmdLost.player me).lost &&
    gCmdLost.result == some (.won opp)
  -- 2. `unspentManaBecomesColorless`
  let horizonDef : CardDef :=
    { (creature "Horizon Test" ManaCost.empty #["Rogue"] 3 3) with
      unspentManaBecomesColorless := true }
  let gMana0 :=
    (addPermanent (quiet afterDraw) horizonDef me me).addMana me (.colored .red) 1
  let horizon := (gMana0.battlefield.filter (·.name == "Horizon Test"))[0]!
  let gManaKept := gMana0.emptyManaPools
  let gManaLost :=
    (gMana0.createEffect (.losesAbilitiesUntilEot horizon.id) (cause := some c1)).emptyManaPools
  let unspentManaOk :=
    (gManaKept.player me).manaPool.colorless == 1 &&
    (gManaKept.player me).manaPool.total == 1 &&
    (gManaLost.player me).manaPool.isEmpty
  -- 3. `planeswalkersYouControlHave` (Layer 6 timestamp order + Layer 4 `isPlaneswalker`)
  let loyaltyGrantAb : ActivatedAbility :=
    { cost := { loyalty := some (.plus 1) }
      effect := {} }
  let pwDef : CardDef :=
    { name := "Test Planeswalker"
      types := #[.planeswalker]
      loyalty := some 4 }
  let healerDef : CardDef :=
    { name := "Way of Test"
      types := #[.enchantment]
      planeswalkersYouControlHave := #[loyaltyGrantAb] }
  let gPw0 := addPermanent (addPermanent (quiet afterDraw) healerDef me me) pwDef me me
  let pw := (gPw0.battlefield.filter (·.name == "Test Planeswalker"))[0]!
  let gPwLost := gPw0.createEffect (.losesAbilitiesUntilEot pw.id) (cause := some c1)
  let gPwRe := addPermanent gPwLost healerDef me me
  let gPwFood := gPw0.createEffect (.onlyFoodArtifact pw.id) (cause := some c2)
  let pwGrantOk :=
    (gPw0.activatedAbilitiesOf (gPw0.object! pw.id)).size == 1 &&
    (gPwLost.activatedAbilitiesOf (gPwLost.object! pw.id)).isEmpty &&
    (gPwRe.activatedAbilitiesOf (gPwRe.object! pw.id)).size == 1 &&
    (gPwFood.activatedAbilitiesOf (gPwFood.object! pw.id)).isEmpty
  -- 4. `grantedManaAbilities` (`otherSubtypeHaveTapAddOneOf` + `grantCreaturesTapAddAnyColor`)
  let elfDef : CardDef := creature "Test Elf" ManaCost.empty #["Elf"] 1 1
  let subtypeLordDef : CardDef :=
    { (creature "Elf Mana Lord" ManaCost.empty #["Advisor"] 2 2) with
      staticAbilities := #[.otherSubtypeHaveTapAddOneOf #[.elf] #[.colored .green, .colored .blue]] }
  let chorusDef : CardDef :=
    { name := "Test Chorus"
      types := #[.enchantment]
      grantCreaturesTapAddAnyColor := true }
  let gGr0 :=
    addPermanent
      (addPermanent
        (addPermanent (quiet afterDraw) subtypeLordDef me me)
        chorusDef me me)
      elfDef me me
  let elf := (gGr0.battlefield.filter (·.name == "Test Elf"))[0]!
  let gGrLost := gGr0.createEffect (.losesAbilitiesUntilEot elf.id) (cause := some c1)
  let gGrRe := addPermanent gGrLost subtypeLordDef me me
  let grantedManaOk :=
    (gGr0.grantedManaAbilities (gGr0.object! elf.id)).size == 5 &&
    (gGrLost.grantedManaAbilities (gGrLost.object! elf.id)).isEmpty &&
    (gGrLost.manaAbilitiesOf (gGrLost.object! elf.id)).isEmpty &&
    gGrRe.grantedManaAbilities (gGrRe.object! elf.id) == #[.colored .green, .colored .blue]
  -- 5. `intrinsicLandMana` / `landsCouldProduce` (`grantLandsTapAnyColor` + land ability loss)
  let mtnDef : CardDef := { name := "Test Mountain", types := #[.land], subtypes := #["Mountain"] }
  let lanternDef : CardDef :=
    { name := "Test Lantern"
      types := #[.artifact]
      grantLandsTapAnyColor := true }
  let gLd0 := addPermanent (addPermanent (quiet afterDraw) lanternDef me me) mtnDef me me
  let mtn := (gLd0.battlefield.filter (·.name == "Test Mountain"))[0]!
  let lantern := (gLd0.battlefield.filter (·.name == "Test Lantern"))[0]!
  let gLanternLost := gLd0.createEffect (.losesAbilitiesUntilEot lantern.id) (cause := some c1)
  let gBothLost := gLanternLost.createEffect (.losesAbilitiesUntilEot mtn.id) (cause := some c2)
  let gMtnLost := gLd0.createEffect (.losesAbilitiesUntilEot mtn.id) (cause := some c1)
  let gMtnReLantern := addPermanent gMtnLost lanternDef me me
  let landManaOk :=
    (gLd0.intrinsicLandMana (gLd0.object! mtn.id)).size == 5 &&
    gLanternLost.intrinsicLandMana (gLanternLost.object! mtn.id) == #[.colored .red] &&
    (gBothLost.intrinsicLandMana (gBothLost.object! mtn.id)).isEmpty &&
    (gBothLost.landsCouldProduce #[gBothLost.object! mtn.id]).isEmpty &&
    (gMtnLost.intrinsicLandMana (gMtnLost.object! mtn.id)).isEmpty &&
    (gMtnLost.manaAbilityDefs (gMtnLost.object! mtn.id)).isEmpty &&
    (gMtnReLantern.intrinsicLandMana (gMtnReLantern.object! mtn.id)).size == 5 &&
    (gMtnReLantern.manaAbilityDefs (gMtnReLantern.object! mtn.id)).size == 1
  cantLoseWinOk && unspentManaOk && pwGrantOk && grantedManaOk && landManaOk &&
    allRulesEventsClassified gAngelLost &&
    allRulesEventsClassified gManaKept &&
    allRulesEventsClassified gManaLost &&
    allRulesEventsClassified gPwRe &&
    allRulesEventsClassified gGrRe &&
    allRulesEventsClassified gMtnReLantern

/- Phase 9 isolation suite (CR 613.1a–b / 707 / 800.4a): Layer 1 copy and
Layer 2 control effects are purely derived from `g.activeEffects` without
mutating `GameObject.printed` / `GameObject.controller` or emitting secondary
`ObjectChange` or `.staticAbility` churn on creation or expiry. Copy-of-copy
reads Layer 1 `copiableValues`. -/
#guard
  let opp : PlayerId := ⟨1⟩
  let giantDef : CardDef :=
    { creature "Phase9 Giant" ManaCost.empty #["Giant"] 4 5 with
      staticAbilities := #[.fra .creaturesYouControlHaveTrample] }
  let cloneDef : CardDef :=
    creature "Phase9 Clone" ManaCost.empty #["Shapeshifter"] 0 0
  let g0 :=
    addPermanent
      (addPermanent
        (addPermanent (quiet afterDraw) bear opp opp)
        giantDef me me)
      cloneDef me me
  let b := (g0.battlefield.filter (·.name == "Event Bear"))[0]!
  let gt := (g0.battlefield.filter (·.name == "Phase9 Giant"))[0]!
  let cl := (g0.battlefield.filter (·.name == "Phase9 Clone"))[0]!
  let gCopy1 := (quiet g0).becomeCopyOf b gt (untilEot := true)
  let gCopy2 := gCopy1.becomeCopyOf (gCopy1.object! cl.id) (gCopy1.object! b.id) (untilEot := true)
  let noPrintedMutation :=
    (gCopy1.object! b.id).printed.name == "Event Bear" &&
    (gCopy2.object! cl.id).printed.name == "Phase9 Clone"
  let copyValuesOk :=
    gCopy1.name (gCopy1.object! b.id) == "Phase9 Giant" &&
    gCopy1.power (gCopy1.object! b.id) == 4 &&
    gCopy1.toughness (gCopy1.object! b.id) == 5 &&
    gCopy2.name (gCopy2.object! cl.id) == "Phase9 Giant" &&
    gCopy2.hasTrample (gCopy2.object! cl.id)
  let gRevert := (quiet gCopy2).clearEOT
  let copyRevertClean :=
    gRevert.name (gRevert.object! b.id) == "Event Bear" &&
    gRevert.name (gRevert.object! cl.id) == "Phase9 Clone"
  let gCtrl := (quiet g0).changeControl b me (untilEot := true)
  let gCtrlEnd := (quiet gCtrl).clearEOT
  let layer2PureOk :=
    (gCtrl.object! b.id).controller == some opp &&
    gCtrl.controllerOf (gCtrl.object! b.id) == some me &&
    gCtrlEnd.controllerOf (gCtrlEnd.object! b.id) == some opp
  noPrintedMutation && copyValuesOk && copyRevertClean && layer2PureOk

/- Phase 9 isolation suite (CR 613.3 / 702.73a / 205.3d): Changeling applies
first in Layer 4 as a CDA so a later Layer 4 subtype-replacing effect overwrites
all creature subtypes, and losing `.creature` in Layer 4 strips creature subtypes. -/
#guard
  let changelingDef : CardDef :=
    { creature "Phase9 Changeling" ManaCost.empty #["Shapeshifter"] 2 2 with
      keywords := { changeling := true } }
  let g0 := addPermanent (quiet afterDraw) changelingDef me me
  let ch := (g0.battlefield.filter (·.name == "Phase9 Changeling"))[0]!
  let cdaOk :=
    g0.hasSubtype ch .bear &&
    g0.hasSubtype ch .elf &&
    g0.hasSubtype ch .construct &&
    (g0.snapshot ch).subtypes.contains .bear &&
    (g0.snapshot ch).changeling
  let gOverwrite := g0.createEffect (.replacedCreatureTypesUntilEot ch.id #[.construct, .hero])
  let ch1 := gOverwrite.object! ch.id
  let overwriteOk :=
    gOverwrite.subtypes ch1 == #[.construct, .hero] &&
    !gOverwrite.hasSubtype ch1 .bear &&
    !gOverwrite.hasSubtype ch1 .elf
  let gNonCreature := g0.createEffect (.notACreature ch.id)
  let ch2 := gNonCreature.object! ch.id
  let lostCreatureSubtypesOk :=
    !gNonCreature.isCreature ch2 &&
    (gNonCreature.subtypes ch2).isEmpty
  cdaOk && overwriteOk && lostCreatureSubtypesOk

/- Phase 9 isolation suite (CR 613.7a / 613.7e):
1. A static ability granted by an effect has timestamp
   `max(objectEntryTimestamp, grantingEffectTimestamp)` (CR 613.7a).
2. Reattaching an Equipment updates its attachment timestamp (CR 613.7e) so its
   ability grant overrides an earlier `.losesAbilitiesUntilEot` on the host. -/
#guard
  let kiteDef : CardDef :=
    { name := "Phase9 Kitesail"
      types := #[.artifact]
      subtypes := #["Equipment"]
      staticAbilities := #[.equippedCreatureHasKeywords { flying := true }] }
  let g0 :=
    addPermanent
      (addPermanent
        (addPermanent (quiet afterDraw) bear me me)
        hero me me)
      kiteDef me me
  let b := (g0.battlefield.filter (·.name == "Event Bear"))[0]!
  let h := (g0.battlefield.filter (·.name == "Event Hero"))[0]!
  let kite := (g0.battlefield.filter (·.name == "Phase9 Kitesail"))[0]!
  let handCount : Int := Int.ofNat (g0.player me).hand.size
  -- CR 613.7a: setBasePT (9, 9) -> grantedStatic powerEqualCardsInHand -> setBasePT (7, 7)
  let g1 := g0.createEffect (.setBasePTUntilEot b.id (9, 9))
  let g2 := g1.createEffect (.grantedStatic b.id .powerEqualCardsInHand)
  let g3 := g2.createEffect (.setBasePTUntilEot b.id (7, 7))
  let grantedTsOk :=
    g1.power (g1.object! b.id) == 9 &&
    g2.power (g2.object! b.id) == handCount &&
    g2.toughness (g2.object! b.id) == 9 &&
    g3.power (g3.object! b.id) == 7 &&
    g3.toughness (g3.object! b.id) == 7
  -- CR 613.7e: attach Kitesail to Bear -> Bear loses abilities -> reattach to Hero then Bear
  let gEq1 := g0.attachSourceTo kite b
  let gEqLost := gEq1.createEffect (.losesAbilitiesUntilEot b.id)
  let gEqOther := gEqLost.attachSourceTo (gEqLost.object! kite.id) (gEqLost.object! h.id)
  let gEqRe := gEqOther.attachSourceTo (gEqOther.object! kite.id) (gEqOther.object! b.id)
  let reattachTsOk :=
    gEq1.hasFlying (gEq1.object! b.id) &&
    !gEqLost.hasFlying (gEqLost.object! b.id) &&
    gEqRe.hasFlying (gEqRe.object! b.id)
  grantedTsOk && reattachTsOk

/- Phase 9 isolation suite (CR 613.8): Dependency ordering overrides timestamp
order across Layer 2 (controller-scoped control change), Layer 3 (chained text
changes), Layer 5 (subtype-scoped color grant vs text change), and Layer 6
(`ObjectScope.creaturesWithout` ability grant vs `AbilityRemoval.all`). -/
#guard
  let opp : PlayerId := ⟨1⟩
  let flyerDef : CardDef :=
    { creature "Phase9 Flyer" ManaCost.empty #["Bird"] 2 2 with
      keywords := { flying := true } }
  let g0 :=
    addPermanent
      (addPermanent (quiet afterDraw) bear opp opp)
      flyerDef me me
  let b := (g0.battlefield.filter (·.name == "Event Bear"))[0]!
  let fl := (g0.battlefield.filter (·.name == "Phase9 Flyer"))[0]!
  -- Layer 2: earlier `.creaturesControlledBy me -> opp` waits for later `.objects #[b] -> me`
  let gL2 :=
    (g0.createEffect (.layered (.creaturesControlledBy me) (.control opp) .untilEndOfTurn)).createEffect
      (.layered (.objects #[b.id]) (.control me) .untilEndOfTurn)
  let l2DepOk := gL2.controllerOf (gL2.object! b.id) == some opp
  -- Layer 5: earlier `.permanentsOfSubtype me .bear` color-add + later `.additionalSubtype`
  let gL5 :=
    (g0.createEffect
      (.layered (.permanentsOfSubtype me .bear) (.colors .add (ColorSet.singleton .green)) .untilEndOfTurn)).createEffect
      (.additionalSubtype fl.id .bear)
  let l5DepOk := (gL5.colors (gL5.object! fl.id)).contains .green
  -- Layer 6: earlier `.creaturesWithout flying -> vigilance` waits for later `losesAbilitiesUntilEot`
  let gL6 :=
    (g0.createEffect
      (.layered (.creaturesWithout { flying := true })
        (.abilities { keywords := { vigilance := true } } .none) .untilEndOfTurn)).createEffect
      (.losesAbilitiesUntilEot fl.id)
  let flAfter := gL6.object! fl.id
  let l6DepOk := !gL6.hasFlying flAfter && gL6.hasVigilance flAfter
  l2DepOk && l5DepOk && l6DepOk

/- Phase 9 isolation suite (CR 613.4b–d):
1. Layer 7b timestamp order across `setBasePTUntilEot`, `auraConstruct55` (5/5),
   and `cardsInHandPowerUntilEot`.
2. Layer 7c (`pumpPerArtifactUntilEot` and +1/+1 counters) applies after 7b
   regardless of timestamp, and Layer 7d (`ptSwitch`) applies after 7b and 7c. -/
#guard
  let baubleDef : CardDef := { name := "Phase9 Bauble", types := #[.artifact] }
  let g0 := addPermanent (addPermanent (quiet afterDraw) bear me me) baubleDef me me
  let b := (g0.battlefield.filter (·.name == "Event Bear"))[0]!
  let handCount : Int := Int.ofNat (g0.player me).hand.size
  -- 7b timestamp order: (8, 4) -> Construct 5/5 -> handSize -> (3, 6)
  let g7b1 := g0.createEffect (.setBasePTUntilEot b.id (8, 4))
  let g7b2 := g7b1.createEffect (.auraConstruct55 b.id)
  let g7b3 := g7b2.createEffect (.cardsInHandPowerUntilEot b.id)
  let g7b4 := g7b3.createEffect (.setBasePTUntilEot b.id (3, 6))
  let order7bOk :=
    (g7b1.power (g7b1.object! b.id), g7b1.toughness (g7b1.object! b.id)) == (8, 4) &&
    (g7b2.power (g7b2.object! b.id), g7b2.toughness (g7b2.object! b.id)) == (5, 5) &&
    (g7b3.power (g7b3.object! b.id), g7b3.toughness (g7b3.object! b.id)) == (handCount, 5) &&
    (g7b4.power (g7b4.object! b.id), g7b4.toughness (g7b4.object! b.id)) == (3, 6)
  -- 7c (`pumpPerArtifactUntilEot` + +1/+1 counter) created BEFORE 7b `(3, 6)` + 7d `ptSwitch`:
  -- 1 artifact (`Phase9 Bauble`) => +1/+1, +1/+1 counter => +1/+1, so (3+2, 6+2) = (5, 8), switched => (8, 5).
  let gSublayers :=
    (((g0.createEffect (.pumpPerArtifactUntilEot b.id)).addPlusOnePlusOneTo b 1).createEffect
      (.layered (.objects #[b.id]) .ptSwitch .untilEndOfTurn)).createEffect
      (.setBasePTUntilEot b.id (3, 6))
  let sublayersOk :=
    (gSublayers.power (gSublayers.object! b.id), gSublayers.toughness (gSublayers.object! b.id)) == (8, 5)
  order7bOk && sublayersOk

/- Phase 9 isolation suite (CR 302.6): A land played this turn enters with
`status.summoningSick = true`, can tap for mana while noncreature, becomes
summoning-sick (unable to activate `{T}` mana abilities or attack) if animated
into a creature on the same turn without haste, can act when granted haste, and
a creature whose controller changes mid-turn without haste becomes summoning-sick. -/
#guard
  let opp : PlayerId := ⟨1⟩
  let forestDef : CardDef :=
    { name := "Phase9 Forest", types := #[.land], subtypes := #["Forest"], supertypes := #[.basic] }
  let (g0, fObj) := (quiet afterDraw).allocObject forestDef me (.hand me) none
  let gPlayed :=
    match g0.playLand me fObj.id with
    | .ok g' => g'
    | .error _ => g0
  let land := (gPlayed.battlefield.filter (·.name == "Phase9 Forest"))[0]!
  let noncreatureLandOk :=
    land.status.summoningSick &&
    !gPlayed.hasSummoningSickness land &&
    (gPlayed.manaSources me).any (fun (s, _) => s.id == land.id)
  let gAnim := gPlayed.createEffect (.additionalCreature land.id (untilEot := true))
  let animLand := gAnim.object! land.id
  let animatedSickOk :=
    gAnim.isCreature animLand &&
    gAnim.hasSummoningSickness animLand &&
    !(gAnim.manaSources me).any (fun (s, _) => s.id == land.id)
  let gHaste := gAnim.createEffect (.keywordsUntilEot land.id Keyword.haste)
  let hasteLand := gHaste.object! land.id
  let hasteOk :=
    !gHaste.hasSummoningSickness hasteLand &&
    (gHaste.manaSources me).any (fun (s, _) => s.id == land.id)
  -- Creature controlled since start of turn (`summoningSick := false`) changing control mid-turn
  let gCreature0 := addPermanent (quiet afterDraw) bear opp opp
  let b0 := (gCreature0.battlefield.filter (·.name == "Event Bear"))[0]!
  let gCreatureReady := gCreature0
  let gStolen := gCreatureReady.changeControl (gCreatureReady.object! b0.id) me (untilEot := true)
  let controlSickOk :=
    !gCreatureReady.hasSummoningSickness (gCreatureReady.object! b0.id) &&
    gStolen.hasSummoningSickness (gStolen.object! b0.id)
  noncreatureLandOk && animatedSickOk && hasteOk && controlSickOk

/- Phase 9 isolation suite (CR 110.2 / 707.2 / 708.2 / 702.37e):
1. `initialControllerOf` starts from `defaultController` while that player is in
   the game, ignoring stale raw `o.controller` mutations (`none` or another
   player), and falls back cleanly when `defaultController` has left the game.
2. Layer 1 `copiableValues` includes Layer 1b face-down masking: copying a
   face-down permanent produces a nameless colorless 2/2 creature with no
   abilities, while `unmaskedCopiableValues` still exposes the original
   face-down permanent's morph cost. -/
#guard
  let opp : PlayerId := ⟨1⟩
  let morphDef : CardDef :=
    { creature "Phase9 Morph Angel" { symbols := #[.colored .white, .colored .white] } #["Angel"] 5 5 with
      keywords := { flying := true }
      morph := some (ManaCost.ofGeneric 3) }
  let cloneDef : CardDef := creature "Phase9 Copy" ManaCost.empty #["Shapeshifter"] 0 0
  let g0 :=
    addPermanent
      (addPermanent
        (addPermanent (quiet afterDraw) bear opp opp)
        morphDef me me)
      cloneDef me me
  let b := (g0.battlefield.filter (·.name == "Event Bear"))[0]!
  let m := (g0.battlefield.filter (·.name == "Phase9 Morph Angel"))[0]!
  let cl := (g0.battlefield.filter (·.name == "Phase9 Copy"))[0]!
  -- Divergent `o.controller` fixture does not override living `defaultController`
  let gRawNone := g0.change (.materializeObject { b with controller := none } none)
  let gRawMe := g0.change (.materializeObject { b with controller := some me } none)
  let gOppLost := gRawNone.record (GameEvent.playerLost gRawNone.turnNumber opp .conceded)
  let initCtrlOk :=
    gRawNone.controllerOf (gRawNone.object! b.id) == some opp &&
    gRawMe.controllerOf (gRawMe.object! b.id) == some opp &&
    gOppLost.controllerOf (gOppLost.object! b.id) == none
  -- Face-down permanent copied via `becomeCopyOf` and `createToken` (`copiableValues`)
  let gFd := setFaceDown g0 m.id true
  let gCopied := gFd.becomeCopyOf (gFd.object! cl.id) (gFd.object! m.id) (untilEot := true)
  let (gTok, tok) := gCopied.createToken me (gCopied.copiableValues (gCopied.object! m.id))
  let clAfter := gTok.object! cl.id
  let tokAfter := gTok.object! tok.id
  let mAfter := gTok.object! m.id
  let faceDownCopyOk :=
    !clAfter.status.faceDown &&
    gTok.name clAfter == "" &&
    gTok.power clAfter == 2 &&
    gTok.toughness clAfter == 2 &&
    gTok.colors clAfter == ColorSet.empty &&
    !gTok.hasFlying clAfter &&
    (gTok.activatedAbilitiesOf clAfter).isEmpty &&
    !tokAfter.status.faceDown &&
    gTok.name tokAfter == "" &&
    gTok.power tokAfter == 2 &&
    gTok.toughness tokAfter == 2 &&
    !gTok.hasFlying tokAfter &&
    (gTok.activatedAbilitiesOf tokAfter).isEmpty &&
    (gTok.activatedAbilitiesOf mAfter).size == 1
  initCtrlOk && faceDownCopyOk

/- Phase 9 isolation suite (CR 302.6 edge cases & evaluated battlefield helpers):
1. A no-op `changeControl` on a creature you already controlled since your turn
   began does not cause summoning sickness, nor does expiring a redundant
   control effect while another still gives you control.
2. A scoped `.creaturesControlledBy` control effect causes summoning sickness on
   the turn control changes and clears once the new controller's next turn begins.
3. Noncreature tokens (`createTreasureTokens`) and flickered lands/artifacts
   (`exileThenReturn`) become summoning-sick if animated on the same turn.
4. `chooseCreatureTypeFor`, `returnCreaturesNotOfType`, and
   `chooseCreaturesDestroyRest` evaluate Layer 4 types and subtypes. -/
#guard
  let opp : PlayerId := ⟨1⟩
  let relicDef : CardDef := { name := "Phase9 Relic", types := #[.artifact] }
  let landDef : CardDef :=
    { name := "Phase9 Wastes", types := #[.land] }
  let g0 :=
    addPermanent
      (addPermanent
        (addPermanent
          (addPermanent (quiet afterDraw) bear me me)
          hero opp opp)
        relicDef me me)
      landDef me me
  let bMe := (g0.battlefield.filter (·.name == "Event Bear"))[0]!
  let hOpp := (g0.battlefield.filter (·.name == "Event Hero"))[0]!
  let relic := (g0.battlefield.filter (·.name == "Phase9 Relic"))[0]!
  let land := (g0.battlefield.filter (·.name == "Phase9 Wastes"))[0]!
  -- 1a. No-op control effect on `me`'s own creature
  let gNoop := g0.changeControl bMe me (untilEot := true)
  let noopOk := !gNoop.hasSummoningSickness (gNoop.object! bMe.id)
  -- 1b. Redundant control effect expiring on `me`'s next turn while permanent control stays active
  let gPermSteal :=
    (g0.changeControl hOpp me).startNextTurn.startNextTurn
  let gRedundant := gPermSteal.changeControl (gPermSteal.object! hOpp.id) me (untilEot := true)
  let gRedundantExp := gRedundant.clearEOT
  let redundantOk :=
    !gPermSteal.hasSummoningSickness (gPermSteal.object! hOpp.id) &&
    !gRedundant.hasSummoningSickness (gRedundant.object! hOpp.id) &&
    gRedundantExp.controllerOf (gRedundantExp.object! hOpp.id) == some me &&
    !gRedundantExp.hasSummoningSickness (gRedundantExp.object! hOpp.id)
  -- 2. Scoped `.creaturesControlledBy opp -> .control me` effect
  let gScoped :=
    g0.createEffect (.layered (.creaturesControlledBy opp) (.control me) .indefinite)
  let gScopedNext := gScoped.startNextTurn.startNextTurn
  let scopedOk :=
    gScoped.controllerOf (gScoped.object! hOpp.id) == some me &&
    gScoped.hasSummoningSickness (gScoped.object! hOpp.id) &&
    gScopedNext.controllerOf (gScopedNext.object! hOpp.id) == some me &&
    !gScopedNext.hasSummoningSickness (gScopedNext.object! hOpp.id)
  -- 3. Treasure token & flickered land animated on the same turn
  let gTr := g0.createTreasureTokens me 1
  let tr := (gTr.battlefield.filter (·.name == "Treasure"))[0]!
  let gTrAnim := gTr.createEffect (.additionalCreature tr.id (untilEot := true))
  let gFlicker := g0.exileThenReturn land "flickers" (land := true)
  let flickLand := (gFlicker.battlefield.filter (·.name == "Phase9 Wastes"))[0]!
  let gFlickAnim := gFlicker.createEffect (.additionalCreature flickLand.id (untilEot := true))
  let noncreatureArrivalOk :=
    !gTr.hasSummoningSickness tr &&
    gTrAnim.hasSummoningSickness (gTrAnim.object! tr.id) &&
    !gFlicker.hasSummoningSickness flickLand &&
    gFlickAnim.hasSummoningSickness (gFlickAnim.object! flickLand.id)
  -- 4. Evaluated Layer 4 types/subtypes in battlefield helpers
  let gTyped :=
    ((gTrAnim.createEffect (.replacedCreatureTypesUntilEot bMe.id #[.elf])).createEffect
      (.additionalCreature relic.id (untilEot := true))).createEffect
      (.notACreature hOpp.id)
  let chosenTypeOk := gTyped.chooseCreatureTypeFor me == .elf
  let gBounced := gTyped.returnCreaturesNotOfType .elf
  let bounceOk :=
    (gBounced.findObject? bMe.id).any (·.isOnBattlefield) &&
    (gBounced.findObject? hOpp.id).any (·.isOnBattlefield) &&
    !(gBounced.findObject? relic.id).any (·.isOnBattlefield)
  let gDestroyed := gTyped.chooseCreaturesDestroyRest #[bMe.id]
  let destroyOk :=
    (gDestroyed.findObject? bMe.id).any (·.isOnBattlefield) &&
    (gDestroyed.findObject? hOpp.id).any (·.isOnBattlefield) &&
    !(gDestroyed.findObject? relic.id).any (·.isOnBattlefield)
  noopOk && redundantOk && scopedOk && noncreatureArrivalOk &&
    chosenTypeOk && bounceOk && destroyOk

/- Phase 9 isolation suite (CR 514.2 / CR 800.4a / CR 800.4c on non-singleton
Layer 2 control effects):
1. `clearEOT` ends `.untilEndOfTurn` and `.untilEndOfNextTurnOf` Layer 2
   control effects across `.creaturesControlledBy`, `.permanentsOfSubtype`,
   `.creaturesWithout`, and multi-id `.objects`, reverting control (and exiling
   under CR 800.4c when the default controller has left the game).
2. `playerLeavesGame` ends scoped Layer 2 control effects via the same
   per-permanent CR 800.4c check: exiling when the default controller already
   left, and keeping the permanent on the battlefield when another scoped
   control effect still gives a living player control. -/
#guard
  let opp : PlayerId := ⟨1⟩
  let p0 : PlayerId := ⟨0⟩
  let p1 : PlayerId := ⟨1⟩
  let p2 : PlayerId := ⟨2⟩
  let g3p :=
    match Start.start { seats := #[{ name := "P0", deck := testRedDeck },
                                   { name := "P1", deck := testRedDeck },
                                   { name := "P2", deck := testRedDeck }],
                        startingPlayer := some 0, seed := 7 } with
    | .ok g => quiet (keepOpeningHands g 16)
    | .error e => panic! e
  -- 1. Cleanup expires scoped & multi-id `.untilEndOfTurn` and `.untilEndOfNextTurnOf` control effects
  let g0 :=
    addPermanent
      (addPermanent (quiet afterDraw) bear me me)
      hero me me
  let b := (g0.battlefield.filter (·.name == "Event Bear"))[0]!
  let h := (g0.battlefield.filter (·.name == "Event Hero"))[0]!
  let gScopedEot :=
    g0.createEffect (.layered (.creaturesControlledBy me) (.control opp) .untilEndOfTurn)
  let gScopedClean := gScopedEot.clearEOT
  let gWithoutEot :=
    g0.createEffect (.layered (.creaturesWithout Keyword.flying) (.control opp) .untilEndOfTurn)
  let gWithoutClean := gWithoutEot.clearEOT
  let gMultiEot :=
    g0.createEffect (.layered (.objects #[b.id, h.id]) (.control opp) .untilEndOfTurn)
  let gMultiClean := gMultiEot.clearEOT
  let gNextTurnEnd :=
    g0.createEffect (.layered (.permanentsOfSubtype me .bear) (.control opp) (.untilEndOfNextTurnOf opp))
  let gNextTurnEndAfter1 := gNextTurnEnd.clearEOT
  let gNextTurnEndOpp := gNextTurnEndAfter1.startNextTurn
  let gNextTurnEndAfter2 := gNextTurnEndOpp.clearEOT
  let cleanupScopedOk :=
    gScopedEot.controllerOf (gScopedEot.object! b.id) == some opp &&
    gScopedClean.controllerOf (gScopedClean.object! b.id) == some me &&
    gScopedClean.activeEffects.isEmpty &&
    gWithoutEot.controllerOf (gWithoutEot.object! b.id) == some opp &&
    gWithoutClean.controllerOf (gWithoutClean.object! b.id) == some me &&
    gWithoutClean.activeEffects.isEmpty &&
    gMultiEot.controllerOf (gMultiEot.object! b.id) == some opp &&
    gMultiEot.controllerOf (gMultiEot.object! h.id) == some opp &&
    gMultiClean.controllerOf (gMultiClean.object! b.id) == some me &&
    gMultiClean.controllerOf (gMultiClean.object! h.id) == some me &&
    gNextTurnEndAfter1.controllerOf (gNextTurnEndAfter1.object! b.id) == some opp &&
    gNextTurnEndAfter2.controllerOf (gNextTurnEndAfter2.object! b.id) == some me
  -- 2a. Scoped control effect ending when leaving player leaves exiles permanent whose defaultController already left
  let gBribe := addPermanent g3p bear p2 p0
  let bb := (gBribe.battlefield.filter (·.name == "Event Bear"))[0]!
  let gScopedSteal :=
    gBribe.createEffect (.layered (.creaturesWithout Keyword.flying) (.control p1) .indefinite)
  let gP0Left := gScopedSteal.playerLeavesGame p0
  let gP1Left := gP0Left.playerLeavesGame p1
  let scopedLeaveExileOk :=
    gP0Left.controllerOf (gP0Left.object! bb.id) == some p1 &&
    !gP1Left.battlefield.any (·.name == "Event Bear") &&
    gP1Left.objects.any (fun o => o.name == "Event Bear" && o.zone == .exile)
  -- 2b. Singleton control effect ending while a scoped control effect still gives living `p2` control keeps permanent
  let gBoth :=
    (gBribe.createEffect
      (.layered (.creaturesWithout Keyword.flying) (.control p2) .indefinite)).changeControl bb p1
  let gBothP0Left := gBoth.playerLeavesGame p0
  let gBothP1Left := gBothP0Left.playerLeavesGame p1
  let bbSurv := (gBothP1Left.battlefield.filter (·.name == "Event Bear"))[0]?
  let scopedOthersRemainOk :=
    gBothP0Left.controllerOf (gBothP0Left.object! bb.id) == some p1 &&
    bbSurv.isSome &&
    gBothP1Left.controllerOf bbSurv.get! == some p2
  -- 3. CR 800.4m: `.untilEndOfNextTurnOf p1` control effect expires when left player `p1`'s turn would have begun
  let g3pOwn := addPermanent g3p bear p0 p0
  let bOwn := (g3pOwn.battlefield.filter (·.name == "Event Bear"))[0]!
  let gUntilP1End :=
    (g3pOwn.createEffect
      (.layered (.objects #[bOwn.id]) (.control p2) (.untilEndOfNextTurnOf p1))).playerLeavesGame p1
  let gSkippedP1 := gUntilP1End.startNextTurn
  let leftPlayerNextTurnEndOk :=
    gUntilP1End.controllerOf (gUntilP1End.object! bOwn.id) == some p2 &&
    gSkippedP1.activePlayer == p2 &&
    gSkippedP1.controllerOf (gSkippedP1.object! bOwn.id) == some p0
  g3p.players.size == 3 && cleanupScopedOk && scopedLeaveExileOk &&
    scopedOthersRemainOk && leftPlayerNextTurnEndOk

/- Phase 9 isolation suite (peer static preservation when skipping timestamps,
CR 611.2a vs CR 611.2b phasing durations, and CR 202.2 / 612.2 Layer 3 text
substitutions vs mana-derived colors):
1. `evalLayer6Aux` preserves printed and Layer-6-granted static abilities on
   peer permanents when `needStaticsTs == false` and `hasCwStaticEff == true`,
   while suppressing phased-out peers (CR 613.1f / 702.26b).
2. `EffectDuration.untilSourceLeaves` (CR 611.2a / 702.26d) keeps `"until ~
   leaves the battlefield"` copy and control effects active while the source is
   phased out and expires them when the source leaves `.battlefield`, whereas
   `EffectDuration.whileSourceOnBattlefield` (CR 611.2b / 702.26f) suspends
   `"for as long as ~ remains on the battlefield"` effects while phased out.
3. Layer 3 `.replaceColorWord` rewrites color words in rules-text abilities
   (protection, cast-color triggers, target filters) without altering colors
   derived from `manaCost` or `colorIndicator` (CR 202.2 / 612.1 / 612.2). -/
#guard
  let opp : PlayerId := ⟨1⟩
  -- 1. Peer static abilities preserved under `hasCwStaticEff && !needStaticsTs`
  let lordCard : CardDef :=
    { creature "Phase9 Trample Lord" ManaCost.empty #["Beast"] 3 3 with
      staticAbilities := #[.fra .creaturesYouControlHaveTrample] }
  let gPeer0 :=
    addPermanent
      (addPermanent (quiet afterDraw) lordCard me me)
      bear me me
  let lord := (gPeer0.battlefield.filter (·.name == "Phase9 Trample Lord"))[0]!
  let peerBear := (gPeer0.battlefield.filter (·.name == "Event Bear"))[0]!
  let gCw :=
    gPeer0.createEffect
      (.layered (.creaturesWithout Keyword.flying)
        (.abilities { staticAbilities := #[.noMaximumHandSize] } .none) .untilEndOfTurn)
  let gCwPhased := gCw.phaseOut (gCw.object! lord.id)
  let gGrantPeer :=
    ((addPermanent (addPermanent (quiet afterDraw) hero me me) bear me me).createEffect
      (.layered (.objects #[(addPermanent (addPermanent (quiet afterDraw) hero me me) bear me me |>.battlefield.filter (·.name == "Event Hero"))[0]!.id])
        (.abilities { staticAbilities := #[.fra .creaturesYouControlHaveTrample] } .none) .untilEndOfTurn)).createEffect
      (.layered (.creaturesWithout Keyword.flying)
        (.abilities { staticAbilities := #[.noMaximumHandSize] } .none) .untilEndOfTurn)
  let grantBear := (gGrantPeer.battlefield.filter (·.name == "Event Bear"))[0]!
  let peerStaticsOk :=
    gCw.hasTrample (gCw.object! peerBear.id) &&
    (gCw.staticAbilities (gCw.object! lord.id)).contains (.fra .creaturesYouControlHaveTrample) &&
    (gCw.staticAbilities (gCw.object! lord.id)).contains .noMaximumHandSize &&
    !gCwPhased.hasTrample (gCwPhased.object! peerBear.id) &&
    gGrantPeer.hasTrample grantBear
  -- 2. `untilSourceLeaves` vs `whileSourceOnBattlefield` across phasing
  let invCard : CardDef :=
    { name := "Phase9 Secret Invasion", manaCost := ManaCost.empty, types := #[.enchantment] }
  let gPh0 :=
    addPermanent
      (addPermanent
        (addPermanent (quiet afterDraw) bear me me)
        hero opp opp)
      invCard me me
  let host := (gPh0.battlefield.filter (·.name == "Event Bear"))[0]!
  let copied := (gPh0.battlefield.filter (·.name == "Event Hero"))[0]!
  let inv := (gPh0.battlefield.filter (·.name == "Phase9 Secret Invasion"))[0]!
  let gUntil :=
    (gPh0.becomeCopyOf host copied (untilSourceLeaves := some inv.id)).changeControl
      host opp (untilSourceLeaves := some inv.id)
  let gUntilPhased := gUntil.phaseOut (gUntil.object! inv.id)
  let gUntilLeft := gUntilPhased.moveToOwnerGraveyard (gUntilPhased.object! inv.id) "leaves"
  let gWhile :=
    (gPh0.createEffect (.controlWhileSource host.id opp inv.id)).createEffect
      (.hexproofWhileSource host.id inv.id)
  let gWhilePhased := gWhile.phaseOut (gWhile.object! inv.id)
  let phasingDurationOk :=
    (gUntilPhased.object! inv.id).status.phasedOut &&
    gUntilPhased.name (gUntilPhased.object! host.id) == "Event Hero" &&
    gUntilPhased.controllerOf (gUntilPhased.object! host.id) == some opp &&
    gUntilLeft.name (gUntilLeft.object! host.id) == "Event Bear" &&
    gUntilLeft.controllerOf (gUntilLeft.object! host.id) == some me &&
    gWhile.controllerOf (gWhile.object! host.id) == some opp &&
    gWhile.hasHexproof (gWhile.object! host.id) &&
    gWhilePhased.controllerOf (gWhilePhased.object! host.id) == some me &&
    !gWhilePhased.hasHexproof (gWhilePhased.object! host.id)
  -- 3. Layer 3 text substitutions vs mana-cost/color-indicator colors
  let blueMage : CardDef :=
    { bear with
      name := "Phase9 Blue Mage"
      manaCost := { symbols := #[.colored .blue] }
      protectionFromColors := #[.blue]
      triggeredAbilities := #[.onCastColorScry .blue 2] }
  let redGoblin : CardDef :=
    { bear with name := "Phase9 Red Goblin", manaCost := { symbols := #[.colored .red] } }
  let blueMerfolk : CardDef :=
    { bear with name := "Phase9 Blue Merfolk", manaCost := { symbols := #[.colored .blue] } }
  let whiteKnight : CardDef :=
    { bear with name := "Phase9 White Knight", manaCost := { symbols := #[.colored .white] } }
  let critCard : CardDef :=
    { name := "Phase9 Criticism"
      manaCost := { symbols := #[.colored .black] }
      types := #[.instant]
      spellEffect := some .terminalCriticism }
  let gTxt0 :=
    insertObject
      (addPermanent
        (addPermanent
          (addPermanent
            (addPermanent (quiet afterDraw) blueMage me me)
            redGoblin opp opp)
          blueMerfolk opp opp)
        whiteKnight opp opp)
      critCard me (.hand me)
  let u := (gTxt0.battlefield.filter (·.name == "Phase9 Blue Mage"))[0]!
  let rSrc := (gTxt0.battlefield.filter (·.name == "Phase9 Red Goblin"))[0]!
  let bSrc := (gTxt0.battlefield.filter (·.name == "Phase9 Blue Merfolk"))[0]!
  let wSrc := (gTxt0.battlefield.filter (·.name == "Phase9 White Knight"))[0]!
  let crit := (gTxt0.handObjects me |>.filter (·.name == "Phase9 Criticism"))[0]!
  let gTxt :=
    (gTxt0.createEffect
      (.layered (.objects #[u.id]) (.text (.replaceColorWord .blue .red)) .untilEndOfTurn)).createEffect
      (.layered (.objects #[crit.id]) (.text (.replaceColorWord .blue .white)) .untilEndOfTurn)
  let critTargets := gTxt.legalSpellTargets me (gTxt.object! crit.id)
  let textColorOk :=
    gTxt.colors (gTxt.object! u.id) == ColorSet.singleton .blue &&
    gTxt.frcProtectedFrom (gTxt.object! u.id) (gTxt.object! rSrc.id) &&
    !gTxt.frcProtectedFrom (gTxt.object! u.id) (gTxt.object! bSrc.id) &&
    gTxt.triggeredAbilities (gTxt.object! u.id) == #[.onCastColorScry .red 2] &&
    gTxt.colors (gTxt.object! crit.id) == ColorSet.singleton .black &&
    critTargets.contains (.permanent wSrc.id) &&
    critTargets.contains (.permanent rSrc.id) &&
    !critTargets.contains (.permanent bSrc.id)
  peerStaticsOk && phasingDurationOk && textColorOk

/- Phase 9 isolation suite (summoning sickness across phasing and arrival zone
continuity, plus `post.snapshot` in `.creatureYouControlDealtDamage` and
`.creatureYouControlTapped`):
1. Phasing a creature out and back in preserves `status.summoningSick` (CR
   302.6 / 702.26d), and `hasSummoningSickness` tracks `o`'s zone across arrival
   rather than pinning `oAt.zone` to `.battlefield` before `o` entered.
2. `matchTriggers` (`.creatureYouControlDealtDamage`) and `becomeTapped`
   (`.creatureYouControlTapped`) build event objects via `snapshot`, so creatures
   controlled via Layer 2 effects and noncreatures animated in Layer 4 queue the
   triggers for their evaluated controller. -/
#guard
  let opp : PlayerId := ⟨1⟩
  -- 1. Summoning sickness across phasing & arrival zone continuity
  let (gHand, handBear) := afterDraw.allocObject bear me (.hand me) none
  let (gArr, arrId) := gHand.putOntoBattlefield handBear.id me
  let gPhOut := gArr.phaseOut (gArr.object! arrId)
  let gPhIn := gPhOut.phaseIn (gPhOut.object! arrId)
  let arrObj := gArr.object! arrId
  let gUntapCleared :=
    gArr.change (.materializeObject { arrObj with status := { arrObj.status with summoningSick := false } } none)
  let (gGobHand, handGob) := afterDraw.allocObject ragingGoblin me (.hand me) none
  let (gGobArr, gobId) := gGobHand.putOntoBattlefield handGob.id me
  let gGobStripped :=
    gGobArr.createEffect (.layered (.objects #[gobId]) (.abilities {} .all) .untilEndOfTurn)
  let gPreExisting := addPermanent afterDraw hero me me
  let preHero := (gPreExisting.battlefield.filter (·.name == "Event Hero"))[0]!
  let gPrePhIn := (gPreExisting.phaseOut preHero).phaseIn ((gPreExisting.phaseOut preHero).object! preHero.id)
  let phaseSickOk :=
    (gPhIn.object! arrId).status.summoningSick &&
    gPhIn.hasSummoningSickness (gPhIn.object! arrId) &&
    !(gUntapCleared.object! arrId).status.summoningSick &&
    gUntapCleared.hasSummoningSickness (gUntapCleared.object! arrId) &&
    !gGobArr.hasSummoningSickness (gGobArr.object! gobId) &&
    gGobStripped.hasSummoningSickness (gGobStripped.object! gobId) &&
    !gPrePhIn.hasSummoningSickness (gPrePhIn.object! preHero.id)
  -- 2. `.creatureYouControlDealtDamage` and `.creatureYouControlTapped` with Layer 2 & Layer 4
  let dmgWatchAb : TriggeredAbility := .triggered .fromEffect Effect.watchSheHulkRedirectOnce {}
  let tapWatchAb : TriggeredAbility := .triggered .fromEffect Effect.watchFirstTapUntap {}
  let watcherDef : CardDef :=
    { name := "Phase9 Damage Tap Watcher"
      manaCost := ManaCost.empty
      types := #[.enchantment]
      triggeredAbilities := #[dmgWatchAb, tapWatchAb] }
  let relicDef : CardDef :=
    { name := "Phase9 Animated Relic", manaCost := ManaCost.empty, types := #[.artifact] }
  let gW0 :=
    addPermanent
      (addPermanent
        (addPermanent
          (addPermanent (quiet afterDraw) watcherDef me me)
          watcherDef opp opp)
        bear opp opp)
      relicDef me me
  let oppBear := (gW0.battlefield.filter (·.name == "Event Bear"))[0]!
  let relic := (gW0.battlefield.filter (·.name == "Phase9 Animated Relic"))[0]!
  let gLayered :=
    (gW0.createEffect (.layered (.objects #[oppBear.id]) (.control me) .untilEndOfTurn)).createEffect
      (.additionalCreature relic.id (untilEot := true))
  let cause1 : EventCause := .oneShotEffect (some ⟨201⟩) none (some me)
  let gDmgStolen :=
    gLayered.withBatch (some cause1) fun g =>
      let target := g.object! oppBear.id
      g.dealDamageToPermanent target 1 (source := some (g.snapshot target)) (cause := some cause1)
  let gDmgAnim :=
    gLayered.withBatch (some cause1) fun g =>
      let target := g.object! relic.id
      g.dealDamageToPermanent target 1 (source := some (g.snapshot target)) (cause := some cause1)
  let gTapStolen :=
    gLayered.withBatch (some cause1) fun g =>
      g.becomeTapped (g.object! oppBear.id) (cause := some cause1)
  let gTapAnim :=
    gLayered.withBatch (some cause1) fun g =>
      g.becomeTapped (g.object! relic.id) (cause := some cause1)
  let dmgAndTapSnapOk :=
    (gLayered.object! oppBear.id).controller == some opp &&
    gDmgStolen.waitingTriggers.any (fun wt => wt.controller == me && wt.ability == dmgWatchAb) &&
    !gDmgStolen.waitingTriggers.any (fun wt => wt.controller == opp && wt.ability == dmgWatchAb) &&
    gDmgAnim.waitingTriggers.any (fun wt => wt.controller == me && wt.ability == dmgWatchAb) &&
    gTapStolen.waitingTriggers.any (fun wt => wt.controller == me && wt.ability == tapWatchAb) &&
    gTapAnim.waitingTriggers.any (fun wt => wt.controller == me && wt.ability == tapWatchAb)
  phaseSickOk && dmgAndTapSnapOk

/- Phase 10 isolation:
1. `ManaPool` stores `ManaUnit` provenance (`source` and `restriction`, CR 106.4 /
   106.6) across `manaAdded`, `manaEmptied` (`keptColorless := true` under
   `unspentManaBecomesColorless`), and `manaSpent` (`treasureManaSpentOn` and
   `legendaryManaSpentOn`).
2. `shuffleLibrary` emits `PlayerEvent.shuffled` even on 0-card and 1-card
   libraries (CR 701.24e), and `closeBatch` emits `PlayerEvent.gainedDesignation`
   inside the closing batch.
3. `.fraEmblem` expiration emits `ZoneEvent.ceasedToExist` alongside a pure
   `applyContinuousEffectEvent` table update, and `ringBearerId` is the single
   stored Ring-bearer source of truth.
4. `DelayedTriggerEvent` (`created`, one-shot `consumed`, duration `expired`)
   records explicit `EventCause` provenance on every transition.
5. CR 608.2n / 608.2p / 608.3 mid-resolution stack residency keeps resolving
   spells on `g.stack` across `Pending` pauses, excludes self-targeting on the
   stack (CR 115.5), handles mid-resolution self-exile without moving to the
   graveyard, emits `StackObjectEvent.resolved` on completion, and drains
   `g.continuations` back to `#[]`. -/
#guard
  let opp : PlayerId := ⟨1⟩
  let p10Cause : EventCause := .oneShotEffect (some ⟨1001⟩) none (some me)
  -- 1. `ManaUnit` provenance across `manaAdded`, `manaEmptied` (`keptColorless := true`), and `manaSpent`
  let horizonDef : CardDef :=
    { (creature "Phase10 Horizon" ManaCost.empty #["Rogue"] 3 3) with
      unspentManaBecomesColorless := true }
  let gTr0 := (addPermanent (quiet afterDraw) horizonDef me me).createTreasureTokens me 1 (cause := some p10Cause)
  let trObj := (gTr0.battlefield.filter (·.printed.isToken))[0]!
  let gTrMana :=
    match gTr0.tapForMana me trObj.id (.colored .green) with
    | .ok g' => g'
    | .error _ => gTr0
  let unitLeg : ManaUnit :=
    { mana := .colored .green
      source := none
      restriction := some (.fra .legendarySpell) }
  let gManaAdded := gTrMana.record (GameEvent.manaAdded gTrMana.turnNumber me #[unitLeg] (cause := some p10Cause))
  let gManaConv := gManaAdded.emptyManaPools
  let convUnits := (gManaConv.player me).manaPool.units
  let targetSpellId : ObjectId := ⟨7777⟩
  let gManaSpent := gManaConv.record (GameEvent.manaSpent gManaConv.turnNumber me convUnits targetSpellId)
  let manaProvenanceOk :=
    convUnits.size == 2 &&
    convUnits.all (·.mana == .colorless) &&
    convUnits[0]!.source == some trObj.id &&
    convUnits[1]!.restriction == some (.fra .legendarySpell) &&
    gManaConv.events.any (fun e =>
      match e.change with
      | .rules (.player (.manaEmptied p us true)) =>
        p == me && us.size == 2 && us[0]!.source == some trObj.id &&
          us[1]!.restriction == some (.fra .legendarySpell)
      | _ => false) &&
    GameEvent.treasureManaSpentOn gManaSpent.events targetSpellId &&
    GameEvent.legendaryManaSpentOn gManaSpent.events targetSpellId
  -- 2. 0-card and 1-card `PlayerEvent.shuffled` (CR 701.24e) and `gainedDesignation` inside `closeBatch`
  let gEmptyLib0 :=
    quiet ((afterDraw.player me).library.foldl (fun acc id => (acc.move id .exile none (cause := some p10Cause)).1) afterDraw)
  let gShuf0 := gEmptyLib0.shuffleLibrary me
  let (gOneAlloc, oneRaw) := gEmptyLib0.allocObject bear me (.outside me) none
  let (gOneLib0, oneCardId) := gOneAlloc.move oneRaw.id (.library me) none (cause := some p10Cause)
  let gShuf1 := (quiet gOneLib0).shuffleLibrary me
  let storiedDef : CardDef :=
    { name := "Phase10 Storied Relic"
      manaCost := ManaCost.empty
      types := #[.artifact]
      keywords := Keyword.storied }
  let (gStoryH1, sCard1) := afterDraw.allocObject storiedDef me (.hand me) none
  let (gStoryH2, sCard2) := gStoryH1.allocObject storiedDef me (.hand me) none
  let (gStoryH3, sCard3) := gStoryH2.allocObject storiedDef me (.hand me) none
  let gStoryDone :=
    (quiet gStoryH3).withBatch (some p10Cause) fun g =>
      let (g, _) := g.putOntoBattlefield sCard1.id me (cause := some p10Cause)
      let (g, _) := g.putOntoBattlefield sCard2.id me (cause := some p10Cause)
      (g.putOntoBattlefield sCard3.id me (cause := some p10Cause)).1
  let shufAndDesigOk :=
    gShuf0.pending == .none &&
    gShuf0.events.any (fun e =>
      match e.change with
      | .rules (.player (.shuffled p ord)) => p == me && ord.isEmpty
      | _ => false) &&
    gShuf1.pending == .none &&
    gShuf1.events.any (fun e =>
      match e.change with
      | .rules (.player (.shuffled p ord)) => p == me && ord == #[oneCardId]
      | _ => false) &&
    (gStoryDone.player me).enduringStory &&
    gStoryDone.events.any (fun e =>
      match e.change with
      | .rules (.player (.gainedDesignation p .enduringStory)) => p == me && e.batch.any (·.raw > 0)
      | _ => false)
  -- 3. `.fraEmblem` expiration (`ZoneEvent.ceasedToExist` + pure `applyContinuousEffectEvent`) & `ringBearerId`
  let (gEmb0, embObj) := (quiet afterDraw).allocObject
    { name := "Phase10 Emblem", types := #[] } me .command (some me)
  let embEffId : EffectId := ⟨1050⟩
  let gEmbCreated :=
    gEmb0.record (GameEvent.effectCreated gEmb0.turnNumber embEffId
      (.fraEmblemUntilTurnOf embObj.id opp) p10Cause)
  let gEmbPureApplier :=
    gEmbCreated.applyChange (.rules (.continuousEffect (.expired embEffId)))
  let gEmbExpired := gEmbCreated.expireEffectById embEffId (cause := some (.turnBased .expireAtStepBegin))
  let gRing0 := addPermanent (quiet afterDraw) bear me me
  let ringBear := (gRing0.battlefield.filter (·.name == "Event Bear"))[0]!
  let gRing1 := gRing0.record (GameEvent.ringTempted gRing0.turnNumber me (some ringBear.id) 1 (cause := some p10Cause))
  let emblemAndRingOk :=
    !gEmbPureApplier.activeEffects.any (·.1 == embEffId) &&
    (gEmbPureApplier.findObject? embObj.id).isSome &&
    !gEmbExpired.activeEffects.any (·.1 == embEffId) &&
    (gEmbExpired.findObject? embObj.id).isNone &&
    gEmbExpired.events.any (fun e =>
      match e.change with
      | .rules (.zone (.ceasedToExist eo)) => eo.id == some embObj.id
      | _ => false) &&
    (gRing1.player me).ringBearerId == some ringBear.id &&
    gRing1.isRingBearer me (gRing1.object! ringBear.id)
  -- 4. `DelayedTriggerEvent` (`created`, one-shot `consumed`, duration `expired`) + cause totality
  let gDt0 := addPermanent (addPermanent (quiet afterDraw) bear me me) hero me me
  let dtBear := (gDt0.battlefield.filter (·.name == "Event Bear"))[0]!
  let dtHero := (gDt0.battlefield.filter (·.name == "Event Hero"))[0]!
  let dtOneShot : DelayedTrigger :=
    { controller := me, source := some dtHero, kind := .endStepSacrifice dtBear.id, cause := p10Cause }
  let dtUntilEot : DelayedTrigger :=
    { controller := me, source := some dtHero, kind := .attackPumpPerPlains, cause := p10Cause }
  let gDtReg := ((gDt0.registerDelayedTrigger dtOneShot).registerDelayedTrigger dtUntilEot).record
    (GameEvent.stepBegan gDt0.turnNumber .postcombatMain gDt0.activePlayer)
  let gDtConsumed := gDtReg.beginStep .end
  let gDtExpired := gDtConsumed.clearTurnActivations
  let delayedTriggerEventsOk :=
    gDtReg.events.any (fun e =>
      match e.change with
      | .rules (.delayedTrigger (.created dt)) => dt == dtOneShot
      | _ => false) &&
    gDtConsumed.events.any (fun e =>
      match e.change with
      | .rules (.delayedTrigger (.consumed dt)) => dt == dtOneShot
      | _ => false) &&
    !gDtConsumed.delayedTriggers.any (·.kind == .endStepSacrifice dtBear.id) &&
    gDtConsumed.delayedTriggers.any (·.kind == .attackPumpPerPlains) &&
    gDtExpired.events.any (fun e =>
      match e.change with
      | .rules (.delayedTrigger (.expired dt)) => dt == dtUntilEot
      | _ => false) &&
    gDtExpired.delayedTriggers.isEmpty &&
    allRulesEventsClassified gDtExpired
  -- 5. CR 608.2n / 608.2p / 608.3 mid-resolution stack residency, CR 115.5, self-exile, and `continuations == #[]`
  let scrySpellDef : CardDef :=
    { name := "Phase10 Scry Instant"
      manaCost := ManaCost.empty
      types := #[.instant]
      spellEffect := some (Effect.scry 2) }
  let (gSp0, spObj) := (quiet afterDraw).allocObject scrySpellDef me .stack (some me)
  let gSpOnStack := gSp0.putStackEntry me spObj.id
  let gSpMid := gSpOnStack.resolveTop
  let midStackOk :=
    (match gSpMid.pending with | .scry p 2 _ => p == me | _ => false) &&
    gSpMid.stack.any (·.objectId == spObj.id) &&
    (gSpMid.findObject? spObj.id).any (·.zone == .stack) &&
    gSpMid.resolvingSpell == some spObj.id &&
    !gSpMid.continuations.isEmpty &&
    !(gSpMid.legalStackSpellTargets (fun _ => true) (some spObj.id)).contains (.card spObj.id) &&
    !gSpMid.events.any (fun e =>
      match e.change with
      | .rules (.stackObject (.resolved ..)) => true
      | _ => false)
  let keepScry2 (g : Game) : Game :=
    match g.apply me (.scry (g.scryLookedIds me 2) #[]) with
    | .ok g' => g'
    | .error _ => g
  let gSpDone := keepScry2 gSpMid
  let doneStackOk :=
    gSpDone.pending == .none &&
    gSpDone.stack.isEmpty &&
    gSpDone.continuations.isEmpty &&
    gSpDone.resolvingSpell.isNone &&
    gSpDone.objects.any (fun o => o.name == "Phase10 Scry Instant" && o.zone == .graveyard me) &&
    gSpDone.events.any (fun e =>
      match e.change with
      | .rules (.stackObject (.resolved eo ..)) => eo.id == some spObj.id
      | _ => false) &&
    allRulesEventsClassified gSpDone
  let (gSpMidExiled, exiledSpId) := gSpMid.move spObj.id .exile none (cause := some p10Cause)
  let gSpSelfExileDone := keepScry2 gSpMidExiled
  let selfExileOk :=
    gSpSelfExileDone.stack.isEmpty &&
    gSpSelfExileDone.continuations.isEmpty &&
    (gSpSelfExileDone.findObject? exiledSpId).any (·.zone == .exile) &&
    !gSpSelfExileDone.objects.any (fun o => o.name == "Phase10 Scry Instant" && o.zone == .graveyard me) &&
    gSpSelfExileDone.events.any (fun e =>
      match e.change with
      | .rules (.stackObject (.resolved eo ..)) => eo.id == some spObj.id
      | _ => false) &&
    allRulesEventsClassified gSpSelfExileDone
  manaProvenanceOk &&
    shufAndDesigOk &&
    emblemAndRingOk &&
    delayedTriggerEventsOk &&
    midStackOk &&
    doneStackOk &&
    selfExileOk &&
    allRulesEventsClassified gManaSpent &&
    noOneShotCauses gShuf0 &&
    gShuf0.nextEffectId == gEmptyLib0.nextEffectId &&
    noOneShotCauses gShuf1 &&
    gShuf1.nextEffectId == gOneLib0.nextEffectId &&
    allRulesEventsClassified gStoryDone &&
    allRulesEventsClassified gEmbExpired &&
    allRulesEventsClassified gRing1

/- Phase 10 review-invariant suite:
1. Painland `activateManaAbility` records `.gameRule .abilityActivated` on life loss without bumping `nextEffectId` (even inside `withResolvingContext`).
2. `applyPermanentAction` (`.untap`, `.doubleStrikeCounter`, `.tapAndStun`) and `replaceUntap` / `wrapReplacedCause` outside `withResolvingContext` record non-one-shot causes and leave `nextEffectId` unchanged.
3. `temptWithTheRing`, `finishScry`, `finishSurveil`, and `supplyOrder` leave `nextEffectId` unchanged outside `withResolvingContext` and share one minted `EffectId` inside `withResolvingContext`.
4. `shuffleLibrary` on a 2+-card library transitions to `Pending.resolveRandom (.shuffleLibrary p)` even if `g.pending != .none`, and `shuffleThen` chains `PendingReplacement.shuffleThen` behind an as-enters choice instead of recording an unrandomized order.
5. `beholdAndMaybeUntap` mints two distinct `EffectId`s across its two instructions ("Behold X. If you do, untap") when resolving and allocates zero `EffectId`s outside resolution.
6. `becomePrepared`, `unprepare` (`.gameRule .spellCast`), and `phaseOut` (`.turnBased .phaseInOut`) allocate zero one-shot `EffectId`s outside `withResolvingContext` and share one `EffectId` inside `withResolvingContext`.
7. `Start.start` and `allocObject` / `insertObject` materialize objects via `EngineChange.materializeObject` without emitting `ZoneEvent.created`, driving tier-3 `materializedAt` timestamps and `hasSummoningSickness`. -/
#guard
  -- 1. Painland mana ability life-loss cause
  let painLandDef : CardDef :=
    { name := "Phase10 Painland"
      types := #[.land]
      tapAddOneOfDealsDamage := some (#[.colored .red, .colored .white], 1) }
  let gPain0 := quiet (addPermanent afterDraw painLandDef me me)
  let painObj := (gPain0.battlefield.filter (·.name == "Phase10 Painland"))[0]!
  let gPainQuiet :=
    match gPain0.activateManaAbility me painObj.id 0 #[.colored .red] with
    | .ok g' => g'
    | .error _ => gPain0
  let gPainRes :=
    gPain0.withResolvingContext (some painObj.id) me (fun g =>
      match g.activateManaAbility me painObj.id 0 #[.colored .red] with
      | .ok g' => g'
      | .error _ => g)
  let painCauses (g : Game) :=
    g.events.filterMap (fun e =>
      match e.change with
      | .rules (.life (.lost ..)) => e.cause?
      | _ => none)
  let painOk :=
    gPainQuiet.nextEffectId == gPain0.nextEffectId &&
    painCauses gPainQuiet == #[.gameRule .abilityActivated] &&
    gPainRes.nextEffectId == gPain0.nextEffectId &&
    painCauses gPainRes == #[.gameRule .abilityActivated] &&
    noOneShotCauses gPainQuiet &&
    noOneShotCauses gPainRes
  -- 2. `applyPermanentAction` and stun-counter `replaceUntap` outside resolution
  let gAct0 :=
    let g := addPermanent afterDraw bear me me
    let bid := (g.battlefield.filter (·.name == "Event Bear"))[0]!.id
    quiet (setTapped (g.recordPutCounters bid .stun 1) bid true)
  let actBear := (gAct0.battlefield.filter (·.name == "Event Bear"))[0]!
  let gUntapStun := gAct0.applyPermanentAction actBear .untap
  let gDbl := gAct0.applyPermanentAction actBear .doubleStrikeCounter
  let gTapStun := gAct0.applyPermanentAction actBear .tapAndStun
  let stunCauses :=
    gUntapStun.events.filterMap (fun e =>
      match e.change with
      | .rules _ => e.cause?
      | _ => none)
  let permActionOk :=
    gUntapStun.nextEffectId == gAct0.nextEffectId &&
    stunCauses == #[.replaced { kind := .stunCounterUntap, object := some actBear.id } (.turnBased .untapAll)] &&
    gDbl.nextEffectId == gAct0.nextEffectId &&
    gTapStun.nextEffectId == gAct0.nextEffectId &&
    noOneShotCauses gUntapStun &&
    noOneShotCauses gDbl &&
    noOneShotCauses gTapStun
  -- 3. `temptWithTheRing`, `finishScry`, `finishSurveil`, `supplyOrder` outside vs inside resolution
  let gRingQuiet := gAct0.temptWithTheRing me
  let gRingRes := gAct0.withResolvingContext (some actBear.id) me (fun g => g.temptWithTheRing me)
  let ringResIds := (GameEvent.oneShotEffectsWithId gRingRes.events).map Prod.fst
  let gScry0 := (gAct0.beginScry me 1)
  let gScryQuiet :=
    match gScry0.finishScry me (gScry0.scryLookedIds me 1) #[] with
    | .ok g' => g'
    | .error _ => gScry0
  let gSurv0 := (gAct0.beginSurveil me 1)
  let gSurvQuiet :=
    match gSurv0.finishSurveil me #[] (gSurv0.scryLookedIds me 1) with
    | .ok g' => g'
    | .error _ => gSurv0
  let resolvingHelpersOk :=
    gRingQuiet.nextEffectId == gAct0.nextEffectId &&
    gRingRes.nextEffectId == gAct0.nextEffectId + 1 &&
    ringResIds.size == 2 &&
    ringResIds[0]! == ringResIds[1]! &&
    gScryQuiet.nextEffectId == gAct0.nextEffectId &&
    gSurvQuiet.nextEffectId == gAct0.nextEffectId &&
    noOneShotCauses gRingQuiet &&
    noOneShotCauses gScryQuiet &&
    noOneShotCauses gSurvQuiet
  -- 4. `shuffleLibrary` with `pending != .none` and `shuffleThen` behind an as-enters choice
  let gPending2 := gAct0.change (.pending (.scry me 1 1))
  let gShufWhilePending := gPending2.shuffleLibrary me
  let roomDef : CardDef :=
    { name := "Phase10 Room"
      types := #[.land]
      staticAbilities := #[.fra .entersTappedChooseColor] }
  let gSearchAsEnters0 := quiet (insertObject afterDraw roomDef me (.library me))
  let roomLibId := ((gSearchAsEnters0.player me).library.filter (fun id => (gSearchAsEnters0.object! id).name == "Phase10 Room"))[0]!
  let gSearchAsEntersMid :=
    gSearchAsEnters0.withResolvingContext none me (fun g =>
      g.finishLibrarySearch me #[roomLibId] (.battlefield true) none "land card")
  let midNoPrematureShuffled :=
    (match gSearchAsEntersMid.pending with
     | .chooseReplacement p cs =>
       p == me && cs.any (fun c => match c.kind with | .asEntersChooseColor _ => true | _ => false)
     | _ => false) &&
    !gSearchAsEntersMid.events.any (fun e =>
      match e.change with | .rules (.player (.shuffled ..)) => true | _ => false)
  let gSearchAfterColor :=
    match gSearchAsEntersMid.apply me (.chooseMode 1) with
    | .ok g' => g'
    | .error _ => gSearchAsEntersMid
  let shuffleGuardOk :=
    (gAct0.player me).library.size > 1 &&
    gShufWhilePending.pending == .resolveRandom (.shuffleLibrary me) &&
    !gShufWhilePending.events.any (fun e =>
      match e.change with | .rules (.player (.shuffled ..)) => true | _ => false) &&
    midNoPrematureShuffled &&
    gSearchAfterColor.pending == .resolveRandom (.shuffleLibrary me)
  -- 5. `beholdAndMaybeUntap` mints two distinct `EffectId`s when resolving and zero outside resolution
  let dragonLandDef : CardDef :=
    { name := "Phase10 Dragon Roost"
      types := #[.land] }
  let dragonCreatureDef : CardDef :=
    creature "Phase10 Dragon" ManaCost.empty #["Dragon"] 4 4
  let gBeh0 :=
    let g := addPermanent (addPermanent afterDraw dragonLandDef me me) dragonCreatureDef me me
    let lid := (g.battlefield.filter (·.name == "Phase10 Dragon Roost"))[0]!.id
    quiet (setTapped g lid true)
  let dLand := (gBeh0.battlefield.filter (·.name == "Phase10 Dragon Roost"))[0]!
  let gBehQuiet := gBeh0.beholdAndMaybeUntap me dLand.id .dragon
  let gBehRes := gBeh0.withResolvingContext (some dLand.id) me (fun g =>
    g.beholdAndMaybeUntap me dLand.id .dragon)
  let behResIds := (GameEvent.oneShotEffectsWithId gBehRes.events).map Prod.fst
  let beholdUntapOk :=
    gBehQuiet.nextEffectId == gBeh0.nextEffectId &&
    !(gBehQuiet.object! dLand.id).status.tapped &&
    gBehRes.nextEffectId == gBeh0.nextEffectId + 2 &&
    behResIds.size == 2 &&
    behResIds[0]! != behResIds[1]! &&
    noOneShotCauses gBehQuiet &&
    allRulesEventsClassified gBehRes
  -- 6. `becomePrepared`, `unprepare`, and `phaseOut` outside vs inside resolution
  let prepDef : CardDef :=
    { creature "Phase10 Prepared" ManaCost.empty #["Knight"] 2 2 with
      prepareFace := some { name := "Phase10 Seed" } }
  let gPrep0 := quiet (addPermanent afterDraw prepDef me me)
  let prepObj := (gPrep0.battlefield.filter (·.name == "Phase10 Prepared"))[0]!
  let gPrepQuiet := gPrep0.becomePrepared prepObj
  let prepQuietOneShots := GameEvent.oneShotEffectsWithId gPrepQuiet.events
  let gUnprepQuiet := (quiet gPrepQuiet).unprepare (gPrepQuiet.object! prepObj.id)
  let unprepCauses :=
    gUnprepQuiet.events.filterMap (fun e =>
      match e.change with
      | .rules (.permanent (.designation _ .prepared false)) => e.cause?
      | _ => none)
  let gPrepRes := gPrep0.withResolvingContext (some prepObj.id) me (fun g => g.becomePrepared prepObj)
  let prepResIds := (GameEvent.oneShotEffectsWithId gPrepRes.events).map Prod.fst
  let prepEffOneShots :=
    gPrepRes.events.filterMap (fun e =>
      match e.change with
      | .rules (.continuousEffect (.created ..)) => e.cause?.bind EventCause.oneShotEffectId?
      | _ => none)
  let gPhaseQuiet := gPrep0.phaseOut prepObj
  let gPhaseRes := gPrep0.withResolvingContext (some prepObj.id) me (fun g => g.phaseOut prepObj)
  let phaseResIds := (GameEvent.oneShotEffectsWithId gPhaseRes.events).map Prod.fst
  let prepAndPhaseOk :=
    prepQuietOneShots.isEmpty &&
    gUnprepQuiet.nextEffectId == gPrepQuiet.nextEffectId &&
    unprepCauses == #[.gameRule .spellCast] &&
    prepResIds.size == 2 &&
    prepResIds[0]! == prepResIds[1]! &&
    prepEffOneShots == #[prepResIds[0]!] &&
    gPhaseQuiet.nextEffectId == gPrep0.nextEffectId &&
    gPhaseRes.nextEffectId == gPrep0.nextEffectId + 1 &&
    phaseResIds.size == 1 &&
    noOneShotCauses gPrepQuiet &&
    noOneShotCauses gUnprepQuiet &&
    noOneShotCauses gPhaseQuiet &&
    allRulesEventsClassified gPhaseRes
  -- 7. `allocObject` / `insertObject` materialize via `EngineChange.materializeObject` (0 `ZoneEvent.created`, tier-1 timestamps)
  let auraDef : CardDef := enchantment "Phase10 Aura" ManaCost.empty "Enchant creature"
  let gTs0 := insertObject (quiet started) bear me .battlefield (some me)
    { summoningSick := true, counters := #[(.plusOnePlusOne, 1)] }
  let tsBear := (gTs0.battlefield.filter (·.name == "Event Bear"))[0]!
  let (gTs1, tsAura) := gTs0.allocObject auraDef me .battlefield (some me) (attachedTo := some tsBear.id)
  let hasZoneCreated (evs : Array GameEvent) : Bool :=
    evs.any (fun e => match e.change with | .rules (.zone (.created ..)) => true | _ => false)
  let createdTsOk :=
    !hasZoneCreated started.events &&
    !hasZoneCreated gTs1.events &&
    (gTs1.objectEntryTimestamp tsBear).1 == 1 &&
    (gTs1.counterTimestamp tsBear.id .plusOnePlusOne).1 == 1 &&
    (gTs1.attachmentTimestamp tsAura tsBear.id).1 == 1 &&
    gTs1.hasSummoningSickness tsBear &&
    noOneShotCauses started &&
    noOneShotCauses gTs1
  -- 8. Round-2 continuation-frame & 0-card `shuffleThen` invariants:
  --    (a) `requestShuffle` with `after != .none` on a quiet board keeps `afterRandom` without minting `EffectId`
  --    (b) 0-card remaining library `shuffleThen` behind an as-enters choice waits for the choice before shuffling or running `onDone`
  --    (c) `applyGainLifeSearchBasicPlusOne` on a quiet board keeps `plusOneAfterSearch` and adds the +1/+1 counter without minting `EffectId`
  let gEmptyForReq :=
    quiet ((afterDraw.player me).library.foldl (fun acc id => (acc.move id .exile none (cause := some testCause)).1) afterDraw)
  let gReq0 := gEmptyForReq.requestShuffle me (.gainLife me 1)
  let gReqMany := gAct0.requestShuffle me (.gainLife me 1)
  let gReqManyDone :=
    match gReqMany.supplyOrder (gReqMany.player me).library with
    | .ok g' => g'
    | .error _ => gReqMany
  let gZeroAfterSearch0 :=
    let g := addPermanent gEmptyForReq dragonCreatureDef me me
    quiet (insertObject g roomDef me (.library me))
  let onlyRoomId := (gZeroAfterSearch0.player me).library[0]!
  let gZeroMid :=
    gZeroAfterSearch0.finishLibrarySearch me #[onlyRoomId] (.battlefieldTappedBeholdUntap .dragon) none "land card"
  let zeroMidDeferred :=
    (match gZeroMid.pending with
     | .chooseReplacement p cs =>
       p == me && cs.any (fun c => match c.kind with | .asEntersChooseColor _ => true | _ => false)
     | _ => false) &&
    !gZeroMid.events.any (fun e =>
      match e.change with
      | .rules (.player (.shuffled ..)) => true
      | .rules (.player (.beheld ..)) => true
      | _ => false)
  let gZeroDone :=
    match gZeroMid.apply me (.chooseMode 1) with
    | .ok g' => g'
    | .error _ => gZeroMid
  let basicPlainsDef : CardDef :=
    { name := "Plains", types := #[.land], supertypes := #[.basic], subtypes := #["Plains"] }
  let gRestTech0 :=
    let g := addPermanent gEmptyForReq bear me me
    quiet (insertObject g basicPlainsDef me (.library me))
  let restBear := (gRestTech0.battlefield.filter (·.name == "Event Bear"))[0]!
  let basicLibId := (gRestTech0.player me).library[0]!
  let gRestMid :=
    gRestTech0.applyGainLifeSearchBasicPlusOne me #[.player me, .permanent restBear.id] 2
  let gRestDone :=
    match gRestMid.answerFraChoice me (.objects #[basicLibId]) with
    | .ok g' => g'
    | .error _ => gRestMid
  let round2ContinuationOk :=
    gReq0.afterRandom == .gainLife me 1 &&
    gReq0.nextEffectId == gEmptyForReq.nextEffectId &&
    noOneShotCauses gReq0 &&
    gReqMany.afterRandom == .gainLife me 1 &&
    gReqManyDone.nextEffectId == gAct0.nextEffectId &&
    noOneShotCauses gReqManyDone &&
    zeroMidDeferred &&
    gZeroDone.events.any (fun e => match e.change with | .rules (.player (.shuffled ..)) => true | _ => false) &&
    gZeroDone.events.any (fun e => match e.change with | .rules (.player (.beheld _ .dragon)) => true | _ => false) &&
    gZeroDone.nextEffectId == gZeroMid.nextEffectId &&
    noOneShotCauses gZeroDone &&
    (gRestDone.object! restBear.id).status.plusOnePlusOne == 1 &&
    gRestDone.nextEffectId == gRestTech0.nextEffectId &&
    noOneShotCauses gRestDone
  painOk &&
    permActionOk &&
    resolvingHelpersOk &&
    shuffleGuardOk &&
    beholdUntapOk &&
    prepAndPhaseOk &&
    createdTsOk &&
    round2ContinuationOk

-- Phase 11: Non-token materialization vs `ZoneEvent.created`, `Game.snapshot`
-- Layer 1–7 snapshots, CR 614.12 / 702.34a replacements, `*/*` CDA creature
-- spells on the stack, and CR 702.73a off-battlefield changeling search/behold.
#guard
  let hasCreated (evs : Array GameEvent) : Bool :=
    evs.any fun e => match e.change with | .rules (.zone (.created ..)) => true | _ => false
  let hasMaterialized (evs : Array GameEvent) : Bool :=
    evs.any fun e => match e.change with | .engine (.materializeObject ..) => true | _ => false
  -- 1. Materialization vs `ZoneEvent.created` isolation
  let gSb0 := quiet (afterDraw.change (.player me (.sideboard #[bear])))
  let gSb1 := gSb0.materializeSideboard me
  let gEmb := (quiet afterDraw).createCommandObject me { name := "Phase11 Emblem", types := #[] }
  let actBearDef : CardDef := {
    bear with
    activatedAbilities := #[{ cost := {}, effect := {} }]
  }
  let gAb0 := quiet (addPermanent afterDraw actBearDef me me)
  let baseBear := (gAb0.battlefield.filter (·.name == "Event Bear"))[0]!
  let gAbStack := gAb0.putTriggeredAbilityOnStack me baseBear (.onEnterDraw 1) "enters"
  let gActStack :=
    match gAb0.activateAbility me baseBear.id 0 with
    | .ok g => g
    | .error _ => gAb0
  let (gTok, _) := gAb0.createToken me treasureToken
  let gPrepCopy := gAb0.createPreparedCopy baseBear { name := "Phase11 Seed" }
  let hasTrigPut (evs : Array GameEvent) : Bool :=
    evs.any fun e => match e.change with | .rules (.triggerQueue (.putOnStack ..)) => true | _ => false
  let materializeIsolationOk :=
    !hasCreated started.events && hasMaterialized started.events &&
    !hasCreated gSb1.events && hasMaterialized gSb1.events &&
    !hasCreated gEmb.events && hasMaterialized gEmb.events &&
    !hasCreated gAbStack.events && hasTrigPut gAbStack.events &&
    !hasCreated gActStack.events && hasMaterialized gActStack.events &&
    hasCreated gTok.events &&
    hasCreated gPrepCopy.events
  -- 2. `Game.snapshot` planeswalker loyalty, `attached` `previous`, and per-ability `resolved`
  let rockDef : CardDef := { name := "Phase11 Rock", types := #[.artifact] }
  let loyaltyWatcherDef : CardDef := {
    name := "Phase11 Loyalty Watcher"
    types := #[.enchantment]
    triggeredAbilities := #[TriggeredAbility.fra (.fra .youPutLoyaltyCounters) "" (.draw 1)]
  }
  let gPw0 := addPermanent (addPermanent afterDraw rockDef me me) loyaltyWatcherDef me me
  let pwRock := (gPw0.battlefield.filter (·.name == "Phase11 Rock"))[0]!
  let gPw1 := quiet (gPw0.createEffect
    (.layered (.objects #[pwRock.id]) (.types .add #[.planeswalker] #[.jace] #[]) .untilEndOfTurn))
  let gPw2 := gPw1.withBatch none fun g =>
    g.recordPutCounters pwRock.id .loyalty 1 (byPlayer := some me)
  let pwSnapOk :=
    gPw2.events.any (fun e =>
      match e.change with
      | .rules (.permanent (.counters (.object eo) .loyalty (.put 1) (some p))) =>
        eo.id == some pwRock.id && p == me && eo.types.contains .planeswalker
      | _ => false) &&
    gPw2.waitingTriggers.any (·.event == .fra .youPutLoyaltyCounters)
  let eqDef : CardDef := { name := "Phase11 Blade", types := #[.artifact], subtypes := #["Equipment"] }
  let bear2Def : CardDef := creature "Event Bear 2" ManaCost.empty #["Bear"] 2 2
  let gEq0 := quiet (addPermanent (addPermanent gAb0 bear2Def me me) eqDef me me)
  let eqObj := (gEq0.battlefield.filter (·.name == "Phase11 Blade"))[0]!
  let host1 := (gEq0.battlefield.filter (·.name == "Event Bear"))[0]!
  let host2 := (gEq0.battlefield.filter (·.name == "Event Bear 2"))[0]!
  let gEq1 := gEq0.attachSourceTo eqObj host1
  let gEq2 := gEq1.attachSourceTo (gEq1.object! eqObj.id) host2
  let eqAttached := gEq2.events.filterMap fun e =>
    match e.change with
    | .rules (.permanent (.attached eo hid prev)) => some (eo, hid, prev)
    | _ => none
  let attachedPrevOk :=
    eqAttached.size == 2 &&
    eqAttached[0]!.1.subtypes.contains .equipment &&
    eqAttached[0]!.2.1 == host1.id &&
    eqAttached[0]!.2.2 == none &&
    eqAttached[1]!.1.subtypes.contains .equipment &&
    eqAttached[1]!.2.1 == host2.id &&
    eqAttached[1]!.2.2 == some host1.id
  let abA : TriggeredAbility := .triggered .enter (Effect.ofTrigger .belladonnaTokenReward)
  let abB : TriggeredAbility := .triggered .yourUpkeep (Effect.ofTrigger .belladonnaTokenReward)
  let gRes0 := quiet gAb0
  let gRes1 := (gRes0.putTriggeredAbilityOnStack me baseBear abA "enters").resolveTop
  let gRes2 := (gRes1.putTriggeredAbilityOnStack me (gRes1.object! baseBear.id) abB "upkeep").resolveTop
  let gRes3 := (gRes2.putTriggeredAbilityOnStack me (gRes2.object! baseBear.id) abA "enters").resolveTop
  let resolvedEvents := gRes3.events.filterMap fun e =>
    match e.change with
    | .rules (.stackObject (.resolved obj ord sid ab?)) => some (ord, obj, sid, ab?)
    | _ => none
  let perAbilityResolvedOk :=
    resolvedEvents.size == 3 &&
    resolvedEvents[0]!.1 == 1 && resolvedEvents[0]!.2.2.1 == some baseBear.id && resolvedEvents[0]!.2.2.2 == some abA &&
    resolvedEvents[1]!.1 == 1 && resolvedEvents[1]!.2.2.1 == some baseBear.id && resolvedEvents[1]!.2.2.2 == some abB &&
    resolvedEvents[2]!.1 == 2 && resolvedEvents[2]!.2.2.1 == some baseBear.id && resolvedEvents[2]!.2.2.2 == some abA
  let snapshotAlignmentOk := pwSnapOk && attachedPrevOk && perAbilityResolvedOk
  -- 3. CR 614.12 clone & Layer 6 ability-loss ETB lookahead + CR 702.34a `.flashbackUntilEot`
  let tappedPwDef : CardDef := {
    name := "Phase11 Tapped Walker"
    types := #[.planeswalker]
    subtypes := #["Jace"]
    loyalty := some 4
    entersTapped := true
  }
  let (gClone0, cloneCand) := afterDraw.allocObject bear me (.outside me) (some me)
  let gClone1 := gClone0.createEffect (.layered (.objects #[cloneCand.id]) (.copy tappedPwDef) .indefinite)
  let cloneEtb := gClone1.applyEtbReplacements (gClone1.object! cloneCand.id)
  let humCreatureDef : CardDef := {
    name := "Phase11 Counters Bear"
    types := #[.creature]
    power := some 1
    toughness := some 1
    entersTapped := true
    entersWithPlusOneCounters := 2
  }
  let (gHum0, humCand) := afterDraw.allocObject humCreatureDef me (.outside me) (some me)
  let gHum1 := gHum0.createEffect (.layered (.creaturesControlledBy me) (.abilities {} .all) .indefinite)
  let humEtb := gHum1.applyEtbReplacements (gHum1.object! humCand.id)
  let boltDef : CardDef := { name := "Phase11 Bolt", types := #[.instant] }
  let (gFb0, fbSpell) := (quiet afterDraw).allocObject boltDef me .stack (some me)
  let gFb1 := quiet (gFb0.createEffect (.flashbackUntilEot fbSpell.id))
  let (gFbMoved, fbNewId) := gFb1.move fbSpell.id (.graveyard me) none
  let fbExiledOk :=
    (gFbMoved.object! fbNewId).zone == .exile &&
    gFbMoved.events.any (fun e =>
      match e.change, e.cause? with
      | .rules (.zone (.moved _ _ .stack .exile ..)), some (.replaced rep _) =>
        rep.kind == .flashbackExile && rep.object == some fbSpell.id
      | _, _ => false)
  let etbAndFlashbackOk :=
    cloneEtb.candidate.status.tapped &&
    cloneEtb.entersWith.count .loyalty == 4 &&
    !humEtb.candidate.status.tapped &&
    humEtb.entersWith.count .plusOnePlusOne == 0 &&
    fbExiledOk
  -- 4. `*/*` CDA creature spells on the stack
  let cdaSpellDef : CardDef := {
    name := "Phase11 Lands Avatar"
    types := #[.creature]
    subtypes := #["Avatar"]
    staticAbilities := #[.powerToughnessEqualLandsYouControl]
  }
  let forestDef : CardDef := { name := "Forest", types := #[.land], subtypes := #["Forest"] }
  let gCda0 := addPermanent (addPermanent (addPermanent afterDraw forestDef me me) forestDef me me) forestDef me me
  let (gCda1, cdaSpell) := gCda0.allocObject cdaSpellDef me .stack (some me)
  let gCda2 := gCda1.change (.pushStack { objectId := cdaSpell.id, controller := me, targets := #[] })
  let stackCdaOk :=
    gCda2.snapshotPower cdaSpell == 3 &&
    gCda2.snapshotToughness cdaSpell == 3 &&
    (gCda2.snapshot cdaSpell).power == some 3 &&
    (gCda2.snapshot cdaSpell).toughness == some 3 &&
    (gCda2.legalTargetsForAtomicKind opp (.creatureSpellPTAtMost 3) none).contains (.card cdaSpell.id) &&
    !(gCda2.legalTargetsForAtomicKind opp (.creatureSpellPTAtMost 2) none).contains (.card cdaSpell.id)
  -- 5. CR 702.73a off-battlefield changeling behold & subtype queries
  let changelingDef : CardDef := {
    name := "Phase11 Changeling"
    types := #[.creature]
    subtypes := #["Shapeshifter"]
    keywords := { changeling := true }
    power := some 2
    toughness := some 2
  }
  let gCh0 := quiet (insertObject (emptyHand afterDraw me) changelingDef me (.hand me))
  let gChDragon := gCh0.beholdQuality me .dragon (cause := some (.gameRule .spellCast))
  let gChForest := gCh0.beholdQuality me .forest (cause := some (.gameRule .spellCast))
  let changelingOffBfOk :=
    changelingDef.hasSubtype .dragon &&
    !changelingDef.hasSubtype .forest &&
    !changelingDef.hasSubtype .equipment &&
    gChDragon.events.any (fun e => match e.change with | .rules (.player (.beheld p .dragon)) => p == me | _ => false) &&
    !gChForest.events.any (fun e => match e.change with | .rules (.player (.beheld ..)) => true | _ => false)
  -- 6. Off-battlefield token-creation probe (Draconic Visitor ruling 782), CR 707.2
  --    `isToken` + arrival status preservation across `entersAsCopy` / `entersBackFaceUp`,
  --    and tier-1 timestamps for `TriggerQueueEvent.putOnStack` / `CastEvent.abilityActivated`.
  let bilboDef : CardDef := {
    name := "Phase11 Bilbo"
    types := #[.enchantment]
    foodAlsoCreatesTreasure := true
  }
  let visitorDef : CardDef := {
    name := "Phase11 Visitor"
    types := #[.enchantment]
    staticAbilities := #[.artifactTokensBecomeDragons]
  }
  let foodTemplate : CardDef := {
    name := "Food"
    types := #[.artifact]
    subtypes := #["Food"]
  }
  let gProbe0 := quiet (addPermanent (addPermanent afterDraw bilboDef me me) visitorDef me me)
  let gProbeBfLeaks :=
    quiet ((gProbe0.createEffect
      (.layered (.creaturesControlledBy me) (.types .add #[.artifact] #[.food] #[]) .indefinite)).createEffect
      (.layered (.creaturesControlledBy me) (.copy foodTemplate) .indefinite))
  let (probeBatchesPlain, probeAppPlain, probeChoicePlain) := gProbeBfLeaks.replaceTokenCreationChoice {
    controller := me
    printed := humanSoldierToken
    count := 1
  }
  let gProbeWildcard :=
    quiet (gProbeBfLeaks.createEffect
      (.replacement {
        id := { kind := .entersAsCopy }
        affectedPlayer := me
        kind := .entersAsCopy none foodTemplate
      } .untilEndOfTurn))
  let (_, _, probeChoiceCopy) := gProbeWildcard.replaceTokenCreationChoice {
    controller := me
    printed := humanSoldierToken
    count := 1
  }
  let tokenProbeOk :=
    probeBatchesPlain.size == 1 &&
    probeBatchesPlain[0]!.printed.name == "Human Soldier" &&
    probeAppPlain.isEmpty &&
    probeChoicePlain.isNone &&
    probeChoiceCopy.any (fun (p, cs) => p == me && cs.size == 2)
  let dfcNontokenTemplate : CardDef := {
    name := "Phase11 Siege Front"
    types := #[.enchantment]
    asEntersChooseMarduOrJeskai := true
    asEntersChooseCardType := true
    entersPrepared := true
    isToken := false
    otherFace := some {
      name := "Phase11 Siege Back"
      types := #[.creature]
      power := some 4
      toughness := some 4
      asEntersChooseMarduOrJeskai := true
      entersPrepared := true
      isToken := false
    }
  }
  let gTokCopy0 := quiet (afterDraw.createEffect
    (.replacement {
      id := { kind := .entersAsCopy }
      affectedPlayer := me
      kind := .entersAsCopy none dfcNontokenTemplate
    } .untilEndOfTurn))
  let (gTokCopy1a, _) := gTokCopy0.createOneToken me humanSoldierToken
  let gTokCopy1 := applyIdle (applyIdle gTokCopy1a)
  let placedTokCopied := (gTokCopy1.battlefield.filter (·.name == "Phase11 Siege Front"))[0]!
  let gTokBack0 := quiet (gTokCopy0.createEffect
    (.replacement {
      id := { kind := .entersBackFaceUp }
      affectedPlayer := me
      kind := .entersBackFaceUp none
    } .untilEndOfTurn))
  let (gTokBack1a, _) := gTokBack0.createOneToken me humanSoldierToken
  let gTokBack1 := applyIdle gTokBack1a
  let placedTokBack := (gTokBack1.battlefield.filter (·.name == "Phase11 Siege Back"))[0]!
  let tokenCopyStatusOk :=
    placedTokCopied.printed.isToken &&
    placedTokCopied.printed.otherFace.all (·.isToken) &&
    placedTokCopied.status.chosenAnchor == some "Mardu" &&
    placedTokCopied.status.prepared &&
    placedTokCopied.status.chosenCardType == some .creature &&
    gTokCopy1.isCreature placedTokCopied &&
    placedTokBack.status.transformed &&
    placedTokBack.printed.name == "Phase11 Siege Back" &&
    placedTokBack.printed.isToken &&
    placedTokBack.printed.otherFace.all (·.isToken) &&
    placedTokBack.status.chosenAnchor == some "Mardu" &&
    placedTokBack.status.prepared
  let gTrigBase := addPermanent afterDraw actBearDef me me
  let trigBear := (gTrigBase.battlefield.filter (·.name == "Event Bear"))[0]!
  let gTrigTs0 := gTrigBase.createEffect
    (.layered (.creaturesControlledBy me) (.abilities {} .all) .untilEndOfTurn)
  let effEid := gTrigTs0.activeEffects.back!.1
  let effPos := gTrigTs0.activeEffects.size - 1
  let effTs := gTrigTs0.effectTimestamp effEid effPos
  let gTrigTs1 := gTrigTs0.putTriggeredAbilityOnStack me (gTrigTs0.object! trigBear.id) (.onEnterDraw 1) "enters"
  let trigStackObj := gTrigTs1.object! gTrigTs1.stack.back!.objectId
  let trigTs := gTrigTs1.objectEntryTimestamp trigStackObj
  let directAbId : ObjectId := ⟨gTrigTs1.nextObjectId⟩
  let gDirectAct := gTrigTs1.record (GameEvent.abilityActivated gTrigTs1.turnNumber directAbId
    (gTrigTs1.snapshot (gTrigTs1.object! trigBear.id)) me (.nonMana none false false false (some 0) false))
  let directActObj := gDirectAct.object! directAbId
  let directActTs := gDirectAct.objectEntryTimestamp directActObj
  let bearBeforeBoastTs := gDirectAct.objectEntryTimestamp (gDirectAct.object! trigBear.id)
  let gAfterBoast := gDirectAct.markBoastUsed (gDirectAct.object! trigBear.id)
  let bearAfterBoastTs := gAfterBoast.objectEntryTimestamp (gAfterBoast.object! trigBear.id)
  let stackAbilityTsOk :=
    effTs.1 == 1 &&
    trigTs.1 == 1 && trigTs.2 > effTs.2 &&
    directActTs.1 == 1 && directActTs.2 > trigTs.2 &&
    bearBeforeBoastTs.1 == 1 && bearAfterBoastTs == bearBeforeBoastTs
  materializeIsolationOk &&
    snapshotAlignmentOk &&
    etbAndFlashbackOk &&
    stackCdaOk &&
    changelingOffBfOk &&
    tokenProbeOk &&
    tokenCopyStatusOk &&
    stackAbilityTsOk

/- Phase 12: CR 733.1 illegal-proposal reversal integrity, `Game.replayEvents`
fidelity from `({} : Game)`, `.exchangeControl` batch/cause & CR 701.12a–b,
second combat-damage step `TurnEvent`s (CR 510.4 / 702.7b / 500.9), Path of
Ancestry scry via `ManaUnit.source`, `matchTriggers` cast / target / Ward
triggers (CR 702.85a / 702.21a / 109.2), and `entersTappedUnlessPayLife` in the
unified CR 614.12 / 616.1 ETB replacement pipeline. -/
#guard
  -- 1. CR 733.1 proposal reversal: zero phantom events/triggers, intact `followMoved`,
  --    top-of-library exemption, `.crew` / `.zemoBoastExile` retraction, Chandra refund,
  --    and CR 733.1 library-visibility irreversibility guard.
  let tapWatcherDef : CardDef := {
    name := "Phase12 Tap Watcher"
    types := #[.enchantment]
    triggeredAbilities := #[
      TriggeredAbility.fra .creaturesYouControlBecomeTapped "" (.draw 1),
      TriggeredAbility.fra .youCastNoncreature "" (.draw 1)]
  }
  let manaDorkDef : CardDef := {
    name := "Phase12 Mana Dork"
    types := #[.creature]
    subtypes := #["Elf"]
    power := some 1
    toughness := some 1
    tapAddMana := #[.colored .green]
  }
  let twoGenericSorcery : CardDef := {
    name := "Phase12 Two-Mana Divination"
    manaCost := ManaCost.ofGeneric 2
    types := #[.sorcery]
    spellEffect := some { resolution := .draw 1, phrase := "Draw a card" }
  }
  let gPropBase0 :=
    let g := addPermanent (addPermanent afterDraw tapWatcherDef me me) manaDorkDef me me
    insertObject g twoGenericSorcery me (.hand me)
  let spellHandId :=
    ((gPropBase0.player me).hand.filter (fun id => (gPropBase0.object! id).name == "Phase12 Two-Mana Divination"))[0]!
  let dorkId := (gPropBase0.battlefield.filter (·.name == "Phase12 Mana Dork"))[0]!.id
  let preEvCount := gPropBase0.events.size
  let gProposed := mustApply gPropBase0 me (.cast spellHandId)
  let midReplayOk := Game.replayEvents gProposed.events == gProposed
  let gTappedDuring := mustApply gProposed me (.tapForMana dorkId (.colored .green))
  let gRev := mustApply gTappedDuring me .pay
  let postSlice := gRev.events.extract preEvCount gRev.events.size
  let noPhantomRules :=
    postSlice.all (fun e => match e.change with | .engine (.logMsg _) => true | _ => false)
  let spellRevOk :=
    midReplayOk &&
    noPhantomRules &&
    gRev.proposalCheckpoint.isNone &&
    gRev.proposedSpell.isNone &&
    gRev.pending == .none &&
    gRev.priority == gPropBase0.priority &&
    gRev.consecutivePasses == gPropBase0.consecutivePasses &&
    gRev.waitingTriggers.isEmpty &&
    gRev.stack.isEmpty &&
    !(gRev.object! dorkId).status.tapped &&
    !(gRev.becameTappedThisTurn dorkId) &&
    !(gRev.wasCast spellHandId) &&
    ((gRev.player me).hand.contains spellHandId) &&
    gRev.followMoved spellHandId == spellHandId &&
    gRev.nextObjectId == gPropBase0.nextObjectId &&
    gRev.nextBatchId == gPropBase0.nextBatchId &&
    Game.replayEvents gRev.events == gRev
  -- Top-of-library cast (Elven Chorus) reverses cleanly (`toZone == .stack` is exempted by CR 733.1)
  let chorusDef : CardDef := {
    name := "Phase12 Chorus"
    types := #[.enchantment]
    mayCastCreaturesFromTop := true
  }
  let costlyElfDef : CardDef := {
    name := "Phase12 Costly Elf"
    manaCost := ManaCost.ofGeneric 3
    types := #[.creature]
    subtypes := #["Elf"]
    power := some 2
    toughness := some 2
  }
  let gTop0 :=
    let g := addPermanent afterDraw chorusDef me me
    insertObject g costlyElfDef me (.library me)
  let topCardId := (gTop0.player me).library.back!
  let gTopProp := mustApply gTop0 me (.cast topCardId)
  let gTopRev := mustApply gTopProp me .pay
  let topRevOk :=
    gTopProp.castingFromTop &&
    !gTopRev.castingFromTop &&
    (gTopRev.player me).library.back? == some topCardId &&
    gTopRev.followMoved topCardId == topCardId &&
    Game.replayEvents gTopRev.events == gTopRev
  -- `.crew` and `.zemoBoastExile` non-`ProposedSpell` activation declines retract cleanly
  let boatDef : CardDef := {
    name := "Phase12 Boat"
    types := #[.artifact]
    subtypes := #["Vehicle"]
    power := some 4
    toughness := some 4
    crew := some 2
  }
  let gCrew0 := addPermanent (addPermanent afterDraw boatDef me me) grizzlyBears me me
  let boatId := (gCrew0.battlefield.filter (·.name == "Phase12 Boat"))[0]!.id
  let crewPilotId := (gCrew0.battlefield.filter (·.name == "Grizzly Bears"))[0]!.id
  let gCrewAsk := mustApply gCrew0 me (.activate boatId 0)
  let crewPayableDeclineBlocked := !(gCrewAsk.apply me .decline).isOk
  let gCrewUnpayable := gCrewAsk.becomeTapped (gCrewAsk.object! crewPilotId)
  let gCrewDec := mustApply gCrewUnpayable me .decline
  let crewRevOk :=
    crewPayableDeclineBlocked &&
    gCrewDec.stack.isEmpty &&
    gCrewDec.proposedSpell.isNone &&
    gCrewDec.nextObjectId == gCrew0.nextObjectId &&
    Game.replayEvents gCrewDec.events == gCrewDec
  let zemoDef : CardDef := {
    name := "Phase12 Zemo"
    types := #[.creature]
    power := some 3
    toughness := some 3
    staticAbilities := #[.boast]
  }
  let heavyBlackCard : CardDef := {
    name := "Phase12 Fifteen Black"
    manaCost := { symbols := Array.replicate 15 (.colored .black) }
    types := #[.creature]
    power := some 1
    toughness := some 1
  }
  let gZemo0 :=
    let g := addPermanent afterDraw zemoDef me me
    let g := insertObject g heavyBlackCard me (.graveyard me)
    let z := (g.battlefield.filter (·.name == "Phase12 Zemo"))[0]!
    g.record (GameEvent.attacked g.turnNumber me (g.snapshot z) opp)
  let zemoId := (gZemo0.battlefield.filter (·.name == "Phase12 Zemo"))[0]!.id
  let hvyId := (gZemo0.objects.filter (·.name == "Phase12 Fifteen Black"))[0]!.id
  let gZemoAsk := mustApply gZemo0 me (.activate zemoId 0)
  let zemoPayableDeclineBlocked := !(gZemoAsk.apply me .decline).isOk
  let (gZemoUnpayable, _) := gZemoAsk.move hvyId .exile none
  let gZemoDec := mustApply gZemoUnpayable me .decline
  let zemoRevOk :=
    zemoPayableDeclineBlocked &&
    gZemoDec.stack.isEmpty &&
    gZemoDec.proposedSpell.isNone &&
    gZemoDec.nextObjectId == gZemo0.nextObjectId &&
    Game.replayEvents gZemoDec.events == gZemoDec
  -- Chandra `castExiledAsAbilityResolves`: targeted exiled spell reversed restores mana & `.mayCastExiledElseDamage`
  let gChandra0 :=
    let g := insertObject afterDraw lightningBolt me .exile
    let g := g.addMana me (.colored .red) 1
    let boltExId := (g.objects.filter (fun o => o.name == "Lightning Bolt" && o.zone == .exile))[0]!.id
    g.change (.pending (.mayCastExiledElseDamage me boltExId 2 none))
  let boltExId := (gChandra0.objects.filter (fun o => o.name == "Lightning Bolt" && o.zone == .exile))[0]!.id
  let gChandraProp := mustApply gChandra0 me (.cast boltExId)
  let gChandraRev := gChandraProp.reverseProposedSpell
  let chandraRevOk :=
    gChandraRev.pending == .mayCastExiledElseDamage me boltExId 2 none &&
    (gChandraRev.player me).manaPool.red == 1 &&
    (gChandraRev.object! boltExId).zone == .exile &&
    gChandraRev.followMoved boltExId == boltExId &&
    Game.replayEvents gChandraRev.events == gChandraRev
  -- CR 733.1–733.2 library-event preservation: reversing an illegal cast still
  -- reverses the spell and restores priority, undoing hand reveals while
  -- keeping mill, library shuffle, and library-card reveal events.
  let handCardId := (gProposed.player me).hand[0]!
  let topLibId := (gProposed.player me).library.back!
  let libCardId := (gProposed.player me).library[0]!
  let shuffledOrder := (gProposed.player me).library.reverse
  let gHandRev :=
    (gProposed.record (GameEvent.revealed gProposed.turnNumber me #[handCardId]
      (cause := some (.gameRule .spellCast)))).reverseProposedSpell
  let gMillRev := (gProposed.mill me 1).reverseProposedSpell
  let gShuffleRev :=
    (gProposed.record (GameEvent.shuffled gProposed.turnNumber me shuffledOrder
      (cause := some (.gameRule .spellCast)))).reverseProposedSpell
  let gLibRevealRev :=
    (gProposed.record (GameEvent.revealed gProposed.turnNumber me #[libCardId]
      (cause := some (.gameRule .spellCast)))).reverseProposedSpell
  let baseRestored (g : Game) : Bool :=
    g.proposalCheckpoint.isNone &&
    g.proposedSpell.isNone &&
    g.stack.isEmpty &&
    g.priority == me &&
    (g.player me).hand.contains spellHandId
  let hasRevealOf (g : Game) (cid : ObjectId) : Bool :=
    (g.events.extract preEvCount g.events.size).any (fun e =>
      match e.change with
      | .rules (.player (.revealed p ids)) => p == me && ids == #[cid]
      | _ => false)
  let hasAnyRevealAfter (startIdx : Nat) (g : Game) : Bool :=
    (g.events.extract startIdx g.events.size).any (fun e =>
      match e.change with
      | .rules (.player (.revealed ..)) => true
      | _ => false)
  -- Chronological zone-at-reveal checks (CR 733.1):
  -- (i) Graveyard reveal of a card that is only *later* put into a library (even
  --     reusing the same `ObjectId` so `g.objects` ends with it in `.library`) is undone.
  let gPropGy0 := insertObject gPropBase0 bear me (.graveyard me)
  let gyCardId := (gPropGy0.player me).graveyard.back!
  let preGyEv := gPropGy0.events.size
  let gGyThenLibRev :=
    let g := mustApply gPropGy0 me (.cast spellHandId)
    let g := g.record (GameEvent.revealed g.turnNumber me #[gyCardId]
      (cause := some (.gameRule .spellCast)))
    let gySnap := g.snapshot (g.object! gyCardId)
    let libAfterSnap : EventObject := { gySnap with id := some gyCardId, zone := .library me }
    let g := g.record (GameEvent.moved g.turnNumber gySnap (.graveyard me) (.library me)
      (after := some libAfterSnap) (libraryPosition := some .top) (cause := .gameRule .spellCast))
    g.reverseProposedSpell
  -- (ii) Card that started in `.library`, moved to `.hand` earlier in the slice,
  --      and was then revealed is NOT kept as a library reveal.
  let gDrawnThenRev :=
    let g := gProposed.draw me 1
    let drawnHandId := (g.player me).hand.back!
    let g := g.record (GameEvent.revealed g.turnNumber me #[topLibId, drawnHandId]
      (cause := some (.gameRule .spellCast)))
    g.reverseProposedSpell
  -- (iii) Top-of-library spell (`.library -> .stack`) revealed after moving to `.stack`
  --       is NOT kept as a library reveal.
  let preTopEv := gTop0.events.size
  let topStackId := gTopProp.stack.back!.objectId
  let gTopStackRev :=
    (gTopProp.record (GameEvent.revealed gTopProp.turnNumber me #[topCardId, topStackId]
      (cause := some (.gameRule .spellCast)))).reverseProposedSpell
  -- (iv) Card moved into `.library` by an earlier kept move and *then* revealed IS kept.
  let (gPutLibMid, putLibId) :=
    gProposed.move handCardId (.library me) none (libraryPosition := some .top)
      (cause := some (.gameRule .spellCast))
  let gPutLibThenRev :=
    (gPutLibMid.record (GameEvent.revealed gPutLibMid.turnNumber me #[putLibId]
      (cause := some (.gameRule .spellCast)))).reverseProposedSpell
  let chronoRevealOk :=
    !hasAnyRevealAfter preGyEv gGyThenLibRev &&
    (gGyThenLibRev.player me).library.contains gyCardId &&
    Game.replayEvents gGyThenLibRev.events == gGyThenLibRev &&
    !hasAnyRevealAfter preEvCount gDrawnThenRev &&
    Game.replayEvents gDrawnThenRev.events == gDrawnThenRev &&
    !hasAnyRevealAfter preTopEv gTopStackRev &&
    (gTopStackRev.player me).library.back? == some topCardId &&
    Game.replayEvents gTopStackRev.events == gTopStackRev &&
    hasRevealOf gPutLibThenRev putLibId &&
    Game.replayEvents gPutLibThenRev.events == gPutLibThenRev
  let libGuardOk :=
    baseRestored gHandRev &&
    !hasRevealOf gHandRev handCardId &&
    Game.replayEvents gHandRev.events == gHandRev &&
    baseRestored gMillRev &&
    (gMillRev.object! (gMillRev.followMoved topLibId)).zone == .graveyard me &&
    (gMillRev.player me).graveyard.size == (gPropBase0.player me).graveyard.size + 1 &&
    Game.replayEvents gMillRev.events == gMillRev &&
    baseRestored gShuffleRev &&
    (gShuffleRev.player me).library == shuffledOrder &&
    Game.replayEvents gShuffleRev.events == gShuffleRev &&
    baseRestored gLibRevealRev &&
    hasRevealOf gLibRevealRev libCardId &&
    Game.replayEvents gLibRevealRev.events == gLibRevealRev &&
    chronoRevealOk
  -- Failed may-cast (split second on stack) clears caller `proposalCheckpoint`,
  -- and a subsequent `castAsPartOfResolution` takes its own fresh checkpoint
  -- rather than truncating back across events recorded in between.
  let splitSecondGranter : CardDef := {
    name := "Phase12 Split Granter"
    types := #[.enchantment]
    staticAbilities := #[.instantSorcerySplitSecond]
  }
  let targetCreatureSorcery : CardDef := {
    name := "Phase12 Impossible Removal"
    manaCost := ManaCost.empty
    types := #[.sorcery]
    spellEffect := some {
      targeting := .of .creature
      resolution := .destroyTarget
      phrase := "Destroy target creature"
    }
  }
  let gMayCastCkpt :=
    let g := addPermanent afterDraw splitSecondGranter opp opp
    let g := insertObject g lightningBolt opp (.hand opp)
    let ssHandId := ((g.player opp).hand.filter (fun id => (g.object! id).name == "Lightning Bolt"))[0]!
    let (g, ssStackId) := g.move ssHandId .stack (some opp) (verb := some .cast) (actor := some opp)
      (cause := some (.gameRule .spellCast))
    let g := g.putStackEntry opp ssStackId
    let g := insertObject g lightningBolt me (.hand me)
    let g := insertObject g targetCreatureSorcery me (.hand me)
    let boltH := ((g.player me).hand.filter (fun id => (g.object! id).name == "Lightning Bolt"))[0]!
    let remH := ((g.player me).hand.filter (fun id => (g.object! id).name == "Phase12 Impossible Removal"))[0]!
    let g := g.change (.pending (.fraChoice me (.mayCastInstantSorceryFromHand #[boltH])))
    let gBlocked :=
      match g.answerFraChoice me (.objects #[boltH]) with
      | .ok g' => g'
      | .error _ => g
    let clearedOnFail := gBlocked.proposalCheckpoint.isNone
    let (gMid, _) := gBlocked.move ssStackId (.graveyard opp) none (cause := some testCause)
    let gMid := gMid.gainLife me 5
    let gSecondRev := gMid.castAsPartOfResolution me remH
    (clearedOnFail, gSecondRev, remH)
  let mayCastCkptOk :=
    gMayCastCkpt.1 &&
    gMayCastCkpt.2.1.proposalCheckpoint.isNone &&
    gMayCastCkpt.2.1.proposedSpell.isNone &&
    (gMayCastCkpt.2.1.player me).life == (25 : Int) &&
    ((gMayCastCkpt.2.1.player me).hand.contains gMayCastCkpt.2.2) &&
    Game.replayEvents gMayCastCkpt.2.1.events == gMayCastCkpt.2.1
  let reversalAllOk :=
    spellRevOk && topRevOk && crewRevOk && zemoRevOk && chandraRevOk && libGuardOk && mayCastCkptOk

  -- 2. Full-game `Game.replayEvents g.events == g` from `({} : Game)` and empty `withBatch` non-bump
  let gFull := Agent.play drawnHands 400
  let gNoopBatch := afterDraw.withBatch none id
  let replayAllOk :=
    gFull.over &&
    Game.replayEvents gFull.events == gFull &&
    gNoopBatch.nextBatchId == afterDraw.nextBatchId &&
    Game.replayEvents gNoopBatch.events == gNoopBatch

  -- 3. `.exchangeControl` single-batch / single-cause & CR 701.12a–b guards
  let gExBase := quiet (addPermanent (addPermanent afterDraw bear me me) hero opp opp)
  let exBear := (gExBase.battlefield.filter (·.name == bear.name))[0]!
  let exHero := (gExBase.battlefield.filter (·.name == hero.name))[0]!
  let exEffect : Effect := {
    targeting := .of (.pair .creature .creature)
    resolution := .exchangeControl
    phrase := "Exchange control of two target creatures"
  }
  let gExDone :=
    gExBase.withResolvingContext (some exBear.id) me (fun g =>
      g.applyEffect me exEffect #[Target.permanent exBear.id, Target.permanent exHero.id]
        (sourceId := some exBear.id))
  let isCtrlEffectCreated (e : GameEvent) : Bool :=
    match e.change with
    | .rules (.continuousEffect (.created _ (.layered _ (.control _) _))) => true
    | _ => false
  let ctrlEvents := gExDone.events.filter isCtrlEffectCreated
  let gExSame :=
    let gSame0 := quiet (addPermanent (addPermanent afterDraw bear me me) hero me me)
    let b1 := (gSame0.battlefield.filter (·.name == bear.name))[0]!
    let h1 := (gSame0.battlefield.filter (·.name == hero.name))[0]!
    gSame0.applyEffect me exEffect #[Target.permanent b1.id, Target.permanent h1.id]
  let gExLost :=
    let gLost0 := quiet (gExBase.record (GameEvent.playerLost gExBase.turnNumber opp .conceded))
    gLost0.applyEffect me exEffect #[Target.permanent exBear.id, Target.permanent exHero.id]
  let gExMissing :=
    gExBase.applyEffect me exEffect #[Target.permanent exBear.id, Target.permanent ⟨99999⟩]
  let hasNoCtrlChange (g : Game) : Bool :=
    !g.events.any isCtrlEffectCreated
  -- Ring-bearer designation on BOTH exchanged permanents shares the exchange's
  -- single `BatchId` and resolved `.oneShotEffect (some eid)` cause (not `.staticAbility`).
  let gExRbInit := addPermanent (addPermanent afterDraw bear me me) hero opp opp
  let exRbBear := (gExRbInit.battlefield.filter (·.name == bear.name))[0]!
  let exRbHero := (gExRbInit.battlefield.filter (·.name == hero.name))[0]!
  let gExRb0 :=
    let g := gExRbInit.setRingBearer me (some exRbBear.id) (cause := some testCause)
    g.setRingBearer opp (some exRbHero.id) (cause := some testCause)
  let preExRbIdx := gExRb0.events.size
  let gExRbDone :=
    gExRb0.withResolvingContext (some exRbBear.id) me (fun g =>
      g.applyEffect me exEffect #[Target.permanent exRbBear.id, Target.permanent exRbHero.id]
        (sourceId := some exRbBear.id))
  let exRbSlice := gExRbDone.events.extract preExRbIdx gExRbDone.events.size
  let exRbRules := exRbSlice.filter (fun e =>
    match e.change with
    | .rules (.permanent (.designation _ .ringBearer false))
    | .rules (.continuousEffect (.created _ (.layered _ (.control _) _))) => true
    | _ => false)
  let exRbCauseOk :=
    exRbRules.size == 4 &&
    exRbRules.all (fun e => e.batch == exRbRules[0]!.batch && e.cause? == exRbRules[0]!.cause?) &&
    (match exRbRules[0]!.cause? with
     | some (.oneShotEffect (some _) (some src) (some ctrl)) => src == exRbBear.id && ctrl == me
     | _ => false) &&
    Game.replayEvents gExRbDone.events == gExRbDone
  let exchangeAllOk :=
    ctrlEvents.size == 2 &&
    ctrlEvents[0]!.batch == ctrlEvents[1]!.batch &&
    ctrlEvents[0]!.cause? == ctrlEvents[1]!.cause? &&
    (match ctrlEvents[0]!.cause? with | some (.oneShotEffect (some _) _ _) => true | _ => false) &&
    gExDone.controllerOf (gExDone.object! exBear.id) == some opp &&
    gExDone.controllerOf (gExDone.object! exHero.id) == some me &&
    exRbCauseOk &&
    hasNoCtrlChange gExSame &&
    hasNoCtrlChange gExLost &&
    hasNoCtrlChange gExMissing

  -- 4. Second combat-damage step `TurnEvent`s (CR 510.4 / 702.7b / 500.9) and derived helpers
  let fsAttackerDef : CardDef :=
    { (creature "Phase12 First Striker" ManaCost.empty #["Knight"] 2 2) with
      keywords := Keyword.firstStrike }
  let gCbt0 :=
    let g := addPermanent (addPermanent afterDraw fsAttackerDef me me) bear me me
    let fk := (g.battlefield.filter (·.name == "Phase12 First Striker"))[0]!
    let br := (g.battlefield.filter (·.name == bear.name))[0]!
    let g := g.beginStep .beginningOfCombat
    let g := mustApply (mustApply g me .pass) opp .pass
    let g := mustApply g me (.declareAttackers #[fk.id, br.id] none #[] #[])
    let g := mustApply (mustApply g me .pass) opp .pass
    let g := mustApply g opp (.declareBlockers #[])
    g
  let fkId := (gCbt0.battlefield.filter (·.name == "Phase12 First Striker"))[0]!.id
  -- Also check replacement pause mid-first-strike keeps derived flags `false`
  let gCbtPause0 :=
    let g := addPermanent (addPermanent (addPermanent afterDraw fsAttackerDef me me) bear me me) hero opp opp
    let fk := (g.battlefield.filter (·.name == "Phase12 First Striker"))[0]!
    let br := (g.battlefield.filter (·.name == bear.name))[0]!
    let blk := (g.battlefield.filter (·.name == hero.name))[0]!
    let g := g.recordPutCounters blk.id .shield 1 (some opp) (cause := some testCause)
    let g := g.createEffect
      (.prevention { id := { kind := .preventAllDamageToPermanent, object := some blk.id },
                     affectedPlayer := opp, kind := .preventAllDamageToPermanent blk.id } .untilEndOfTurn)
    let g := g.beginStep .beginningOfCombat
    let g := mustApply (mustApply g me .pass) opp .pass
    let g := mustApply g me (.declareAttackers #[fk.id, br.id] none #[] #[])
    let g := mustApply (mustApply g me .pass) opp .pass
    let g := mustApply g opp (.declareBlockers #[(blk.id, fk.id)])
    mustApply (mustApply g me .pass) opp .pass
  let pauseFlagsOk :=
    (match gCbtPause0.pending with | .chooseReplacement .. => true | _ => false) &&
    !gCbtPause0.firstStrikeDamageDone &&
    !gCbtPause0.pendingRegularCombatDamage &&
    gCbtPause0.firstStrikeAssignedThisCombat.isEmpty &&
    Game.replayEvents gCbtPause0.events == gCbtPause0
  -- Normal two-step combat progression through `Turns.advanceStep`
  let preFsOk :=
    !gCbt0.firstStrikeDamageDone &&
    !gCbt0.pendingRegularCombatDamage &&
    gCbt0.firstStrikeAssignedThisCombat.isEmpty
  let gAfterFs := mustApply (mustApply gCbt0 me .pass) opp .pass
  let afterFsOk :=
    gAfterFs.step == .combatDamage &&
    gAfterFs.firstStrikeDamageDone &&
    gAfterFs.pendingRegularCombatDamage &&
    gAfterFs.firstStrikeAssignedThisCombat == #[fkId] &&
    (gAfterFs.player opp).life == 18 &&
    gAfterFs.events.any (fun e =>
      match e.change with
      | .rules (.turn (.extraStepAdded .combatDamage .afterCurrent)) => true
      | _ => false)
  let preSecondStepIdx := gAfterFs.events.size
  let gAfterReg := mustApply (mustApply gAfterFs me .pass) opp .pass
  let regStepSlice := gAfterReg.events.extract preSecondStepIdx gAfterReg.events.size
  let afterRegOk :=
    gAfterReg.step == .combatDamage &&
    gAfterReg.firstStrikeDamageDone &&
    !gAfterReg.pendingRegularCombatDamage &&
    gAfterReg.firstStrikeAssignedThisCombat == #[fkId] &&
    (gAfterReg.player opp).life == 16 &&
    regStepSlice.any (fun e => match e.change with | .rules (.turn (.stepEnded .combatDamage)) => true | _ => false) &&
    regStepSlice.any (fun e => match e.change with | .rules (.turn (.stepBegan .combatDamage _)) => true | _ => false) &&
    Game.replayEvents gAfterReg.events == gAfterReg
  let combatStepAllOk := pauseFlagsOk && preFsOk && afterFsOk && afterRegOk

  -- 5. Path of Ancestry scry via `ManaUnit.source` (tapped during proposal, floated before proposal,
  --    and LKI when Path of Ancestry left the battlefield before `becomeCast`)
  let poaDef : CardDef := {
    name := "Phase12 Path of Ancestry"
    types := #[.land]
    entersTapped := true
    tapAddCommanderIdentity := true
    commanderIdentityScryCreature := true
  }
  let elfCmdrDef : CardDef := {
    name := "Phase12 Elf Commander"
    manaCost := ⟨#[.colored .green]⟩
    types := #[.creature]
    supertypes := #[.legendary]
    subtypes := #["Elf"]
    power := some 2
    toughness := some 2
  }
  let oneGreenElf : CardDef := {
    name := "Phase12 Llanowar Scout"
    manaCost := ⟨#[.colored .green]⟩
    types := #[.creature]
    subtypes := #["Elf"]
    power := some 1
    toughness := some 1
  }
  let oneGreenGoblin : CardDef := {
    name := "Phase12 Goblin Scout"
    manaCost := ⟨#[.colored .green]⟩
    types := #[.creature]
    subtypes := #["Goblin"]
    power := some 1
    toughness := some 1
  }
  let ancestryBase : Game :=
    match Start.start {
      seats := #[
        { name := "Chandra", deck := testRedDeck, commanders := #[elfCmdrDef] },
        { name := "Nissa", deck := testGreenDeck }
      ]
      format := .constructed
      seed := 1
      startingPlayer := some 0
    } with
    | .ok g => passBoth (keepOpeningHands g 8)
    | .error e => panic! e
  let mkAncestryGame (spellDef : CardDef) : Game × ObjectId × ObjectId :=
    let g := addPermanent ancestryBase poaDef me me
    let poa := (g.battlefield.filter (·.name == "Phase12 Path of Ancestry"))[0]!
    let g := insertObject g spellDef me (.hand me)
    let spId := ((g.player me).hand.filter (fun id => (g.object! id).name == spellDef.name))[0]!
    (g, poa.id, spId)
  -- (a) Tapped during proposal
  let (gPoaDuring0, poaIdA, elfIdA) := mkAncestryGame oneGreenElf
  let gPoaDuring :=
    let g := mustApply gPoaDuring0 me (.cast elfIdA)
    let g := mustApply g me (.tapForMana poaIdA (.colored .green))
    mustApply g me .pay
  -- (b) Floated before proposal, Path of Ancestry destroyed before `becomeCast` (LKI resolution)
  let (gPoaLki0, poaIdB, elfIdB) := mkAncestryGame oneGreenElf
  let gPoaLki :=
    let g := mustApply gPoaLki0 me (.tapForMana poaIdB (.colored .green))
    let g := g.destroyPermanent (g.object! poaIdB)
    let g := mustApply g me (.cast elfIdB)
    mustApply g me .pay
  -- (c) Non-matching creature subtype does not scry
  let (gPoaMiss0, poaIdC, gobIdC) := mkAncestryGame oneGreenGoblin
  let gPoaMiss :=
    let g := mustApply gPoaMiss0 me (.tapForMana poaIdC (.colored .green))
    let g := mustApply g me (.cast gobIdC)
    mustApply g me .pay
  -- (d) Copy-land LKI (CR 707.2 / 608.2h): a Forest copying `poaDef` under an
  --     exception name (`"Thespian's Stage"`) scries after dying, whereas a
  --     printed `poaDef` copying a basic Forest does NOT scry after dying.
  let (gPoaCopyHit0, poaTemplateId, elfIdD) := mkAncestryGame oneGreenElf
  let gPoaCopyHit :=
    let g := addPermanent gPoaCopyHit0 forest me me
    let fstObj := (g.battlefield.filter (·.name == "Forest"))[0]!
    let g := g.becomeCopyOf fstObj (g.object! poaTemplateId) (exceptName := some "Thespian's Stage")
    let g := mustApply g me (.tapForMana fstObj.id (.colored .green))
    let g := g.destroyPermanent (g.object! fstObj.id)
    let g := mustApply g me (.cast elfIdD)
    mustApply g me .pay
  let (gPoaCopyMiss0, poaOverwrittenId, elfIdE) := mkAncestryGame oneGreenElf
  let gPoaCopyMiss :=
    let g := addPermanent gPoaCopyMiss0 forest me me
    let fstObj := (g.battlefield.filter (·.name == "Forest"))[0]!
    let g := g.becomeCopyOf (g.object! poaOverwrittenId) fstObj
    let g := mustApply g me (.tapForMana poaOverwrittenId (.colored .green))
    let g := g.destroyPermanent (g.object! poaOverwrittenId)
    let g := mustApply g me (.cast elfIdE)
    mustApply g me .pay
  -- (e) Phased-out Path of Ancestry (CR 702.26d): tapping for `{G}` and phasing out
  --     before casting the creature spell still resolves the live `.battlefield` object
  --     (`isBattlefieldObject`) and scries; a phased-out copy overwritten onto Forest does not.
  let (gPoaPhased0, poaPhasedId, elfIdF) := mkAncestryGame oneGreenElf
  let gPoaPhased :=
    let g := mustApply gPoaPhased0 me (.tapForMana poaPhasedId (.colored .green))
    let g := g.phaseOut (g.object! poaPhasedId)
    let g := mustApply g me (.cast elfIdF)
    mustApply g me .pay
  let (gPoaPhasedCopy0, poaPhasedCopyId, elfIdG) := mkAncestryGame oneGreenElf
  let gPoaPhasedCopyMiss :=
    let g := addPermanent gPoaPhasedCopy0 forest me me
    let fstObj := (g.battlefield.filter (·.name == "Forest"))[0]!
    let g := g.becomeCopyOf (g.object! poaPhasedCopyId) fstObj
    let g := mustApply g me (.tapForMana poaPhasedCopyId (.colored .green))
    let g := g.phaseOut (g.object! poaPhasedCopyId)
    let g := mustApply g me (.cast elfIdG)
    mustApply g me .pay
  let hasScryPendingOrQueued (g : Game) : Bool :=
    (match g.pending with | .scry p 1 1 => p == me | _ => false) ||
      g.stack.any (fun e => (g.object! e.objectId).triggeredAbility.any (fun ab =>
        ab.effect.resolution == .scry 1))
  let ancestryAllOk :=
    hasScryPendingOrQueued gPoaDuring &&
    hasScryPendingOrQueued gPoaLki &&
    !hasScryPendingOrQueued gPoaMiss &&
    hasScryPendingOrQueued gPoaCopyHit &&
    !hasScryPendingOrQueued gPoaCopyMiss &&
    (gPoaPhased.object! poaPhasedId).status.phasedOut &&
    !(gPoaPhased.object! poaPhasedId).isOnBattlefield &&
    (gPoaPhased.object! poaPhasedId).isBattlefieldObject &&
    hasScryPendingOrQueued gPoaPhased &&
    !hasScryPendingOrQueued gPoaPhasedCopyMiss &&
    Game.replayEvents gPoaLki.events == gPoaLki &&
    Game.replayEvents gPoaCopyHit.events == gPoaCopyHit &&
    Game.replayEvents gPoaCopyMiss.events == gPoaCopyMiss &&
    Game.replayEvents gPoaPhased.events == gPoaPhased &&
    Game.replayEvents gPoaPhasedCopyMiss.events == gPoaPhasedCopyMiss

  -- 6. `matchTriggers`: `.onCastCascade` + CR 109.2 battlefield-doubler guard,
  --    Photon Blast Barrage `.copySourceSpellXTimes`, `.youTargetSomething` on targeted
  --    `.abilityActivated`, and Ward triggers on `WaitingTrigger` / `g.stack`.
  let doublerDef : CardDef := {
    name := "Phase12 Trigger Doubler"
    types := #[.enchantment]
    staticAbilities := #[.extraTriggerAnotherYouControl #[] #[.creature]]
  }
  let cascadeCreatureDef : CardDef := {
    name := "Phase12 Cascade Beast"
    manaCost := ManaCost.ofGeneric 3
    types := #[.creature]
    power := some 2
    toughness := some 2
    cascade := 1
  }
  let gCasc0 :=
    let g := addPermanent afterDraw doublerDef me me
    let g := insertObject g cascadeCreatureDef me (.hand me)
    g.addMana me .colorless 3
  let cascId := ((gCasc0.player me).hand.filter (fun id => (gCasc0.object! id).name == "Phase12 Cascade Beast"))[0]!
  let gCascCast := mustApply (mustApply gCasc0 me (.cast cascId)) me .pay
  let cascadeStackItems := gCascCast.stack.filter (fun se =>
    (gCascCast.object! se.objectId).triggeredAbility == some .onCastCascade)
  -- Photon Blast Barrage X=2 cast trigger via `matchTriggers`
  let pbbDef : CardDef := {
    name := "Phase12 Barrage"
    manaCost := { symbols := #[.x, .colored .red, .colored .red] }
    types := #[.sorcery]
    spellEffect := some {
      targeting := .of .creature
      resolution := .copyThisSpellXTimesThenDamage 1
      phrase := "Deal 1 damage to target creature"
    }
  }
  let gPbb0 :=
    let g := addPermanent afterDraw bear opp opp
    let g := insertObject g pbbDef me (.hand me)
    g.addMana me (.colored .red) 4
  let pbbHandId := ((gPbb0.player me).hand.filter (fun id => (gPbb0.object! id).name == "Phase12 Barrage"))[0]!
  let oppBearPbb := (gPbb0.battlefield.filter (fun o => o.name == bear.name && o.controlledBy opp))[0]!
  let gPbbCast :=
    let g := mustApply gPbb0 me (.cast pbbHandId)
    let g := mustApply g me (.chooseX 2)
    let g := mustApply g me (.target (.permanent oppBearPbb.id))
    mustApply g me .pay
  let pbbTriggerOnStack := gPbbCast.stack.any (fun se =>
    ((gPbbCast.object! se.objectId).triggeredAbility.map (·.effect.resolution)) == some .copySourceSpellXTimes)
  -- `.youTargetSomething` on targeted `.abilityActivated`
  let youTargetTrig : TriggeredAbility :=
    .triggered .fromEffect (Effect.ofTrigger (.watch .youTargetDrawOnce))
  let targetWatcherDef : CardDef := {
    name := "Phase12 Target Watcher"
    types := #[.enchantment]
    triggeredAbilities := #[youTargetTrig]
  }
  let pingerDef : CardDef := {
    name := "Phase12 Pinger"
    types := #[.artifact]
    activatedAbilities := #[{
      cost := { tap := true }
      effect := { targeting := .of .creature, resolution := .tapTargets, phrase := "Tap target creature" }
    }]
  }
  let gTgtAct0 :=
    addPermanent (addPermanent (addPermanent afterDraw targetWatcherDef me me) pingerDef me me) bear opp opp
  let pingerId := (gTgtAct0.battlefield.filter (·.name == "Phase12 Pinger"))[0]!.id
  let oppBearTgt := (gTgtAct0.battlefield.filter (fun o => o.name == bear.name && o.controlledBy opp))[0]!.id
  let gTgtAct1 :=
    let g := mustApply gTgtAct0 me (.activate pingerId 0)
    mustApply g me (.target (.permanent oppBearTgt))
  let youTargetActOk := gTgtAct1.stack.any (fun se =>
    (gTgtAct1.object! se.objectId).triggeredAbility == some youTargetTrig)
  -- Ward triggers: activated ability, triggered ability, retarget, fizzle when spell gone,
  -- decline counter cause, and uncounterable spell still prompting `.payWard`.
  let wardTwoBear : CardDef := { bear with name := "Phase12 Ward Bear", ward := some 2 }
  let gWardBase := addPermanent (addPermanent afterDraw pingerDef me me) wardTwoBear opp opp
  let wardBearId := (gWardBase.battlefield.filter (·.name == "Phase12 Ward Bear"))[0]!.id
  let wardPingerId := (gWardBase.battlefield.filter (·.name == "Phase12 Pinger"))[0]!.id
  -- (a) Activated ability targeting opponent's Ward creature queues Ward on stack
  let gWardAct :=
    let g := mustApply gWardBase me (.activate wardPingerId 0)
    mustApply g me (.target (.permanent wardBearId))
  let wardActOnStack := gWardAct.stack.any (fun se =>
    (gWardAct.object! se.objectId).triggeredAbility == some (.onWard (.genericMana 2)))
  -- (b) Triggered ability choosing opponent's Ward creature as target queues Ward
  let etbTapTrigger : TriggeredAbility :=
    .triggered .enter { targeting := .of .creature, resolution := .tapTargets, phrase := "Tap target creature" } {}
  let gWardTrig :=
    let g := gWardBase.putTriggeredAbilityOnStack me (gWardBase.object! wardPingerId) etbTapTrigger "enters"
    let g := g.promptTriggerTargetsIfNeeded
    mustApply g me (.target (.permanent wardBearId))
  let wardTrigQueued :=
    gWardTrig.stack.any (fun se => (gWardTrig.object! se.objectId).triggeredAbility == some (.onWard (.genericMana 2))) ||
      gWardTrig.waitingTriggers.any (·.ability == .onWard (.genericMana 2))
  -- (c) Retargeting a spell onto opponent's Ward creature queues Ward
  let gWardRetarget0 :=
    let g := addPermanent gWardBase hero opp opp
    let oppHeroId := (g.battlefield.filter (·.name == hero.name))[0]!.id
    let g := insertObject (g.addMana me (.colored .red) 1) lightningBolt me (.hand me)
    let boltId := ((g.player me).hand.filter (fun id => (g.object! id).name == "Lightning Bolt"))[0]!
    let g := mustApply g me (.cast boltId)
    let g := mustApply g me (.target (.permanent oppHeroId))
    mustApply g me .pay
  let retargetSpellId := gWardRetarget0.stack.back!.objectId
  let gWardRetarget1 := gWardRetarget0.retargetStackSpell retargetSpellId #[.permanent wardBearId]
  let wardRetargetQueued := gWardRetarget1.waitingTriggers.any (·.ability == .onWard (.genericMana 2))
  -- (c2) Retargeting one slot of a copied two-target spell does not re-ward a
  --      permanent that was already targeted on the copy (CR 702.21a / 603.2).
  let twoTargetTap : CardDef := {
    name := "Phase12 Twin Frost"
    manaCost := ManaCost.empty
    types := #[.instant]
    spellEffect := some {
      targeting := .of (.pair .creature .creature)
      resolution := .tapTargets
      phrase := "Tap two target creatures"
    }
  }
  let wardBear2Def : CardDef := { bear with name := "Phase12 Ward Bear Two", ward := some 3 }
  let gCopyDelta :=
    let g := addPermanent (addPermanent (addPermanent gWardBase hero opp opp) bear opp opp) wardBear2Def opp opp
    let oppHeroId := (g.battlefield.filter (·.name == hero.name))[0]!.id
    let oppBearId := (g.battlefield.filter (·.name == bear.name))[0]!.id
    let wardBear2Id := (g.battlefield.filter (·.name == "Phase12 Ward Bear Two"))[0]!.id
    let g := insertObject g twoTargetTap me (.hand me)
    let twinId := ((g.player me).hand.filter (fun id => (g.object! id).name == "Phase12 Twin Frost"))[0]!
    let g := mustApply g me (.cast twinId)
    let g := mustApply g me (.target (.permanent wardBearId))
    let g := mustApply g me (.target (.permanent oppHeroId))
    -- Clear initial cast Ward trigger so we measure only the copy's retarget delta
    let g := g.change (.waitingTriggers #[])
    let origStackId := (g.stack.filter (fun se => (g.object! se.objectId).name == "Phase12 Twin Frost"))[0]!.objectId
    let gCopied := g.copyStackSpell (g.object! origStackId) me
    let copyId := gCopied.stack.back!.objectId
    let gRetargetNonWard := gCopied.setSpellTargetAt copyId 1 (.permanent oppBearId)
    let gRetargetSecondWard := gCopied.setSpellTargetAt copyId 1 (.permanent wardBear2Id)
    (gRetargetNonWard.waitingTriggers, gRetargetSecondWard.waitingTriggers)
  let copyRetargetDeltaOk :=
    gCopyDelta.1.isEmpty &&
    gCopyDelta.2.size == 1 &&
    gCopyDelta.2[0]!.ability == .onWard (.genericMana 3)
  -- (d) Spell leaves stack before Ward resolves -> Ward resolves as no-op;
  --     Declining Ward counters with `.oneShotEffect` cause;
  --     Uncounterable spell still prompts `.payWard` and survives decline.
  let uncounterableBolt : CardDef :=
    { lightningBolt with name := "Phase12 Inescapable Bolt", cantBeCountered := true }
  let castAtWard (spellDef : CardDef) : Game :=
    let g := insertObject (gWardBase.addMana me (.colored .red) 1) spellDef me (.hand me)
    let sid := ((g.player me).hand.filter (fun id => (g.object! id).name == spellDef.name))[0]!
    let g := mustApply g me (.cast sid)
    let g := mustApply g me (.target (.permanent wardBearId))
    mustApply g me .pay
  let gWardSpellOnStack := castAtWard lightningBolt
  let boltStackId := (gWardSpellOnStack.stack.filter (fun se => (gWardSpellOnStack.object! se.objectId).name == "Lightning Bolt"))[0]!.objectId
  let gWardSpellRemoved :=
    let (g, _) := gWardSpellOnStack.move boltStackId .exile none (cause := some testCause)
    mustApply (mustApply g me .pass) opp .pass
  let wardFizzledOk := gWardSpellRemoved.pending == .none
  let gWardDeclined :=
    let g := mustApply (mustApply gWardSpellOnStack me .pass) opp .pass
    mustApply g me .decline
  let wardCounterCauseOk := gWardDeclined.events.any (fun e =>
    match e.change, e.cause? with
    | .rules (.zone (.moved _ _ .stack (.graveyard _) .counter ..)),
      some (.oneShotEffect (some _) (some src) (some ctrl)) =>
      src == wardBearId && ctrl == opp
    | _, _ => false)
  let gWardUnc :=
    let g := castAtWard uncounterableBolt
    mustApply (mustApply g me .pass) opp .pass
  let wardUncPrompted :=
    match gWardUnc.pending with
    | .payWard p _ (.genericMana 2) => p == me
    | _ => false
  let gWardUncDeclined := mustApply gWardUnc me .decline
  let wardUncSurvived := gWardUncDeclined.stack.any (fun se =>
    (gWardUncDeclined.object! se.objectId).name == "Phase12 Inescapable Bolt")
  let triggersAllOk :=
    cascadeStackItems.size == 1 &&
    pbbTriggerOnStack &&
    youTargetActOk &&
    wardActOnStack &&
    wardTrigQueued &&
    wardRetargetQueued &&
    copyRetargetDeltaOk &&
    wardFizzledOk &&
    wardCounterCauseOk &&
    wardUncPrompted &&
    wardUncSurvived

  -- 7. `CardDef.entersTappedUnlessPayLife` (The Black Gate) through CR 614.12 / 616.1
  let blackGateDef : CardDef := {
    name := "Phase12 Black Gate"
    supertypes := #[.legendary]
    types := #[.land]
    subtypes := #["Gate"]
    entersTappedUnlessPayLife := some 3
    tapAddMana := #[.colored .black]
  }
  let gBg0 := insertObject afterDraw blackGateDef me (.hand me)
  let bgHandId := ((gBg0.player me).hand.filter (fun id => (gBg0.object! id).name == "Phase12 Black Gate"))[0]!
  -- (a) `playLand` accept (pays 3 life, enters untapped) vs decline (no life lost, enters tapped)
  let gBgPlay := mustApply gBg0 me (.playLand bgHandId)
  let bgPlayAsked :=
    match gBgPlay.pending with
    | .chooseReplacement p cs => p == me && cs.any (·.kind == .entersUntappedPayLife 3)
    | _ => false
  let gBgPaid := mustApply gBgPlay me .accept
  let bgPaidPerm := (gBgPaid.battlefield.filter (·.name == "Phase12 Black Gate"))[0]!
  let gBgDeclined := mustApply gBgPlay me .decline
  let bgDeclinedPerm := (gBgDeclined.battlefield.filter (·.name == "Phase12 Black Gate"))[0]!
  -- (b) Non-`playLand` `putOntoBattlefield`
  let (gBgPut, _) := gBg0.putOntoBattlefield bgHandId me (cause := some testCause)
  let bgPutAsked :=
    match gBgPut.pending with
    | .chooseReplacement p cs => p == me && cs.any (·.kind == .entersUntappedPayLife 3)
    | _ => false
  let gBgPutPaid := mustApply gBgPut me .accept
  let bgPutPerm := (gBgPutPaid.battlefield.filter (·.name == "Phase12 Black Gate"))[0]!
  -- (c) CR 616.1c copy-entry onto The Black Gate
  let gBgCopy0 :=
    let g := insertObject afterDraw bear me (.hand me)
    let cid := ((g.player me).hand.filter (fun id => (g.object! id).name == bear.name))[0]!
    let g := g.createEffect
      (.replacement { id := { kind := .entersAsCopy }, affectedPlayer := me, kind := .entersAsCopy none blackGateDef } .untilEndOfTurn)
    (g.putOntoBattlefield cid me (cause := some testCause)).1
  let bgCopyAsked :=
    match gBgCopy0.pending with
    | .chooseReplacement p cs => p == me && cs.any (·.kind == .entersUntappedPayLife 3)
    | _ => false
  -- (d) Unpayable life (`lifeCantChange` or `life < 3`) auto-enters tapped without prompting
  let gBgLocked :=
    let g := gBg0.createEffect (.lifeCantChange me)
    mustApply g me (.playLand bgHandId)
  let bgLockedPerm := (gBgLocked.battlefield.filter (·.name == "Phase12 Black Gate"))[0]!
  let blackGateAllOk :=
    bgPlayAsked &&
    !bgPaidPerm.status.tapped && (gBgPaid.player me).life == 17 &&
    bgDeclinedPerm.status.tapped && (gBgDeclined.player me).life == 20 &&
    bgPutAsked && !bgPutPerm.status.tapped && (gBgPutPaid.player me).life == 17 &&
    bgCopyAsked &&
    gBgLocked.pending == .none && bgLockedPerm.status.tapped &&
    Game.replayEvents gBgPaid.events == gBgPaid &&
    Game.replayEvents gBgDeclined.events == gBgDeclined

  reversalAllOk &&
    replayAllOk &&
    exchangeAllOk &&
    combatStepAllOk &&
    ancestryAllOk &&
    triggersAllOk &&
    blackGateAllOk

/- Phase 13: CR 733.1 action-level mana-ability / library irreversibility &
`ProposalCheckpoint` batch-pause replay parity, mid-resolution cast reversal
continuations & deferred `PostCastCleanup`, interactive CR 614.1c / 614.12
as-enters choices without `StatusChange`, pausing `replaceUntap` / Saga
`replaceCountersPutChoice`, pain-land `DamageEvent.dealt`, CR 903.3 commander
zone-change persistence, CR 800.4d `leftGame` waiting-trigger cleanup, delayed
spell-copy / combat-Treasure / reflexive `WaitingTrigger` routing, pre-move
`PlayerEvent.revealed`, declined hand-or-library search shuffle, and
departed-source `lastKnownBefore?` LKI + Step 4 audits. -/
#guard
  let opp : PlayerId := ⟨1⟩

  -- 1. CR 733.1 action-level mana-ability / library irreversibility &
  --    `ProposalCheckpoint` batch-pause replay parity.
  let dorkDef : CardDef := {
    name := "Phase13 Mana Dork"
    types := #[.creature]
    subtypes := #["Elf"]
    power := some 1
    toughness := some 1
    tapAddMana := #[.colored .green]
  }
  let filterLandDef : CardDef := {
    name := "Phase13 Filter Land"
    types := #[.land]
    filterMana := some (ManaCost.ofGeneric 1, #[.colored .red, .colored .white])
  }
  let bigSorceryDef : CardDef := {
    name := "Phase13 Five-Mana Sorcery"
    manaCost := ManaCost.ofGeneric 5
    types := #[.sorcery]
    spellEffect := some { resolution := .draw 1, phrase := "Draw a card" }
  }
  let gAct0 :=
    let g := addPermanent (addPermanent (addPermanent afterDraw dorkDef me me) dorkDef me me) filterLandDef me me
    insertObject g bigSorceryDef me (.hand me)
  let dorks := gAct0.battlefield.filter (·.name == "Phase13 Mana Dork")
  let dork1Id := dorks[0]!.id
  let dork2Id := dorks[1]!.id
  let filterId := (gAct0.battlefield.filter (·.name == "Phase13 Filter Land"))[0]!.id
  let bigSpellH := ((gAct0.player me).hand.filter (fun id => (gAct0.object! id).name == "Phase13 Five-Mana Sorcery"))[0]!
  let gActProp := mustApply gAct0 me (.cast bigSpellH)
  -- Tap dork1 (upstream feeder) and dork2 (unrelated mana ability).
  let gActD1 := mustApply gActProp me (.tapForMana dork1Id (.colored .green))
  let gActD2 := mustApply gActD1 me (.tapForMana dork2Id (.colored .green))
  -- Simulate a discrete `.manaAbility (some filterId)` action that spends dork1's mana,
  -- taps `filterId`, adds `{R}{W}`, AND reveals/mills a library card inside the same action:
  -- CR 733.1 keeps the whole `filterId` mana ability AND upstream `dork1` (whose mana fed it),
  -- while reversing unrelated `dork2` and returning `bigSpellH` to hand.
  let gActRev :=
    let g := gActD2.change (.beginProposalAction (.manaAbility (some filterId)))
    let spentUnit : ManaUnit := { mana := .colored .green, source := some dork1Id }
    let g := g.record (GameEvent.manaSpent g.turnNumber me #[spentUnit] filterId
      (cause := some (.costPayment .mana me (some filterId))))
    let g := g.becomeTapped (g.object! filterId) (cause := some (.costPayment .tap me (some filterId)))
    let fSnap := g.snapshot (g.object! filterId)
    let g := g.record (GameEvent.abilityActivated g.turnNumber filterId fSnap me (.mana none))
    let g := g.record (GameEvent.manaAdded g.turnNumber me
      #[{ mana := .colored .red, source := some filterId },
        { mana := .colored .white, source := some filterId }])
    let g := g.mill me 1
    let g := g.change .endProposalAction
    mustApply g me .pay
  let actionIrrevOk :=
    gActRev.proposalCheckpoint.isNone &&
    gActRev.proposedSpell.isNone &&
    ((gActRev.player me).hand.contains bigSpellH) &&
    (gActRev.object! filterId).status.tapped &&
    (gActRev.object! dork1Id).status.tapped &&
    !(gActRev.object! dork2Id).status.tapped &&
    (gActRev.player me).manaPool.red == 1 &&
    (gActRev.player me).manaPool.white == 1 &&
    (gActRev.player me).manaPool.green == 0 &&
    (gActRev.player me).graveyard.size == (gAct0.player me).graveyard.size + 1 &&
    Game.replayEvents gActRev.events == gActRev

  -- `ProposalCheckpoint` batch-pause replay parity + pain-land `DamageEvent.dealt` (group 5):
  let painLandDef : CardDef := {
    name := "Phase13 Pain Land"
    types := #[.land]
    tapAddMana := #[.colorless]
    tapAddOneOfDealsDamage := some (#[.colored .red, .colored .white], 1)
  }
  let gPainCkpt0 :=
    let g := addPermanent afterDraw painLandDef me me
    let g := insertObject g bigSorceryDef me (.hand me)
    let pid := (g.battlefield.filter (·.name == "Phase13 Pain Land"))[0]!.id
    -- Two competing damage replacements so tapping painLand pauses on `Pending.chooseReplacement`
    -- while `proposalCheckpoint` is active!
    let g := g.createEffect
      (.replacement { id := { kind := .multiplyDamage, object := some pid, player := some me, grantor := some ⟨9001⟩ },
                      affectedPlayer := me, kind := .multiplyDamage (some pid) 2 } .untilEndOfTurn)
    g.createEffect
      (.replacement { id := { kind := .addNoncombatDamage, object := some pid, player := some me, grantor := some ⟨9002⟩ },
                      affectedPlayer := me, kind := .addNoncombatDamage (some pid) 1 } .untilEndOfTurn)
  let painCkptId := (gPainCkpt0.battlefield.filter (·.name == "Phase13 Pain Land"))[0]!.id
  let painSpellH := ((gPainCkpt0.player me).hand.filter (fun id => (gPainCkpt0.object! id).name == "Phase13 Five-Mana Sorcery"))[0]!
  let gPainProp := mustApply gPainCkpt0 me (.cast painSpellH)
  let gPainPaused := mustApply gPainProp me (.tapForMana painCkptId (.colored .red))
  let painPausedAtChoice :=
    match gPainPaused.pending with
    | .chooseReplacement p cs =>
      p == me && cs.size == 2 && gPainPaused.proposalCheckpoint.isSome
    | _ => false
  let painMidReplayOk := Game.replayEvents gPainPaused.events == gPainPaused
  let gPainResolved :=
    match gPainPaused.pending with
    | .chooseReplacement _ cs => mustApply gPainPaused me (.chooseReplacement cs[0]!)
    | _ => gPainPaused
  let gPainRev := mustApply gPainResolved me .pay
  let batchPauseReplayOk :=
    painPausedAtChoice &&
    painMidReplayOk &&
    gPainResolved.pending == .activateManaAbilities me &&
    (gPainResolved.player me).life == 17 && -- (1 * 2) + 1 = 3 damage dealt
    Game.replayEvents gPainResolved.events == gPainResolved &&
    gPainRev.proposalCheckpoint.isNone &&
    !(gPainRev.object! painCkptId).status.tapped &&
    (gPainRev.player me).life == 20 &&
    ((gPainRev.player me).hand.contains painSpellH) &&
    Game.replayEvents gPainRev.events == gPainRev

  -- 2. Mid-resolution cast reversal continuations & deferred `PostCastCleanup`.
  let impossibleRemDef : CardDef := {
    name := "Phase13 Impossible Removal"
    manaCost := ManaCost.empty
    types := #[.sorcery]
    spellEffect := some {
      targeting := .of .creature
      resolution := .destroyTarget
      phrase := "Destroy target creature"
    }
  }
  let freeDrawDef : CardDef := {
    name := "Phase13 Free Draw"
    manaCost := ManaCost.empty
    types := #[.sorcery]
    spellEffect := some { resolution := .draw 1, phrase := "Draw a card" }
  }
  -- (a) Deferred `PostCastCleanup.lookedBottom`: library order untouched while paused on
  --     `Pending.chooseTargets`, then bottomed when `becomeCast` completes OR when
  --     `reverseProposedSpell` aborts the cast.
  let gLook0 :=
    let g := addPermanent afterDraw bear opp opp
    let g := insertObject g freeDrawDef me (.library me)
    insertObject g impossibleRemDef me (.library me)
  let lookBearId := (gLook0.battlefield.filter (·.name == bear.name))[0]!.id
  let remLibId := (gLook0.player me).library.back!
  let drawLibId := (gLook0.player me).library[(gLook0.player me).library.size - 2]!
  let gLookAsk := gLook0.change (.pending (.mayCastFromLooked me #[remLibId, drawLibId] 10))
  -- Propose targeted `remLibId`: pauses at `Pending.chooseTargets` BEFORE bottoming `drawLibId`!
  let gLookPaused := mustApply gLookAsk me (.cast remLibId)
  let lookDeferredDuringTargets :=
    gLookPaused.pending == .chooseTargets me &&
    (gLookPaused.player me).library.back? == some drawLibId &&
    Game.replayEvents gLookPaused.events == gLookPaused
  -- Branch 1: choosing legal target completes `becomeCast` and runs `PostCastCleanup.lookedBottom` on `drawLibId`.
  let gLookCast :=
    let g1 := mustApply gLookPaused me (.target (.permanent lookBearId))
    match g1.pending with
    | .resolveRandom (.orderInto ..) => mustApply g1 me (.supplyOrder #[])
    | _ => g1
  let lookPostCastBottomOk :=
    gLookCast.stack.size == 1 &&
    (gLookCast.player me).library[0]? != some drawLibId ||
      (gLookCast.object! (gLookCast.followMoved drawLibId)).zone == .library me
  let lookCastBottomed :=
    gLookCast.stack.size == 1 &&
    gLookCast.postCastCleanup.isNone &&
    (gLookCast.player me).library[0]? == some (gLookCast.followMoved drawLibId) &&
    Game.replayEvents gLookCast.events == gLookCast
  -- Branch 2: reversing the paused proposal returns `remLibId` to `.library` and bottoms BOTH looked cards.
  let gLookRev :=
    let g1 := gLookPaused.reverseProposedSpell
    match g1.pending with
    | .resolveRandom (.orderInto ..) => mustApply g1 me (.supplyOrder #[])
    | _ => g1
  let lookRevRestored :=
    gLookRev.stack.isEmpty &&
    gLookRev.postCastCleanup.isNone &&
    lookPostCastBottomOk &&
    lookDeferredDuringTargets &&
    Game.replayEvents gLookRev.events == gLookRev
  let lookPostCastBottomOk := lookCastBottomed
  -- (b) Reversing a paused mid-resolution free cast (modal + kicker `{5}` failing `.pay`)
  --     resumes `triggerSequenceRest` (`gainLife 1`).
  let modalKickerDef : CardDef := {
    name := "Phase13 Modal Kicker"
    manaCost := ManaCost.empty
    types := #[.sorcery]
    kicker := some (ManaCost.ofGeneric 5)
    spellModes := #[
      { resolution := .draw 1, phrase := "Draw a card" },
      { resolution := .gainLife 1, phrase := "Gain 1 life" }
    ]
  }
  let gSeqRev :=
    let g := insertObject afterDraw modalKickerDef me (.hand me)
    let rid := ((g.player me).hand.filter (fun id => (g.object! id).name == "Phase13 Modal Kicker"))[0]!
    let g := (g.change (.pushContinuationFrame {})).change (.triggerSequenceRest (some {
      controller := me
      ability := TriggeredAbility.fra .youCastNoncreature "" (.draw 1)
      sourceId := none
      targets := #[]
      steps := [.gainLife (.fixed 1)]
    }))
    let gPaused := g.castAsPartOfResolution me rid
    let gMode := mustApply gPaused me (.chooseMode 0)
    let gKick := mustApply gMode me (.announceKicker true)
    mustApply gKick me .pay
  let seqContOk :=
    gSeqRev.triggerSequenceRest.isNone &&
    (gSeqRev.player me).life == 21 &&
    Game.replayEvents gSeqRev.events == gSeqRev
  -- (c) Doom Reigns `.mayCastUpToFromExile`: reversing a paused first exiled cast restores the choice for the second!
  let gQueueRev :=
    let g := insertObject (insertObject afterDraw modalKickerDef me .exile) freeDrawDef me .exile
    let exSac := (g.objects.filter (fun o => o.name == "Phase13 Modal Kicker" && o.zone == .exile))[0]!.id
    let exDraw := (g.objects.filter (fun o => o.name == "Phase13 Free Draw" && o.zone == .exile))[0]!.id
    let g := g.beginFraChoice me (.mayCastUpToFromExile #[exSac, exDraw] 2) "cast exiled"
    let gPaused := mustApply g me (.choosePermanents #[exSac])
    let gMode := mustApply gPaused me (.chooseMode 0)
    let gKick := mustApply gMode me (.announceKicker true)
    let gRev := mustApply gKick me .pay
    let gSecond := mustApply gRev me (.choosePermanents #[exDraw])
    let gDone := mustApply gSecond me .decline
    (gDone, exSac, exDraw)
  let queueContOk :=
    gQueueRev.1.pendingMayCastFromExile.isNone &&
    (gQueueRev.1.object! gQueueRev.2.1).zone == .exile &&
    gQueueRev.1.stack.size == 1 &&
    (gQueueRev.1.object! gQueueRev.1.stack[0]!.objectId).name == "Phase13 Free Draw" &&
    Game.replayEvents gQueueRev.1.events == gQueueRev.1
  let continuationsAllOk := lookRevRestored && lookPostCastBottomOk && seqContOk && queueContOk

  -- 3. Interactive CR 614.1c / 614.12 as-enters choices & `StatusChange` removal.
  let roomDef : CardDef := {
    name := "Phase13 Room of Refuge"
    types := #[.land]
    staticAbilities := #[.fra .entersTappedChooseColor, .fra .tapAddChosenColor]
  }
  let partyDef : CardDef := {
    name := "Phase13 Unexpected Party"
    types := #[.enchantment]
    asEntersChooseCreatureType := true
  }
  let gollumDef : CardDef := {
    name := "Phase13 Gollum"
    types := #[.creature]
    subtypes := #["Halfling"]
    power := some 2
    toughness := some 2
    asEntersChooseOddEven := true
  }
  let mageDef : CardDef := {
    name := "Phase13 Meddling Mage"
    types := #[.creature]
    subtypes := #["Human", "Wizard"]
    power := some 2
    toughness := some 2
    staticAbilities := #[.fra .entersChooseNonlandCardName]
  }
  let emissaryDef : CardDef := {
    name := "Phase13 Emissary"
    types := #[.creature]
    subtypes := #["Angel"]
    power := some 7
    toughness := some 7
    asEntersChooseCardType := true
  }
  let siegeDef : CardDef := {
    name := "Phase13 Windcrag Siege"
    types := #[.enchantment]
    asEntersChooseMarduOrJeskai := true
  }
  let mirrorDef : CardDef := {
    name := "Phase13 Cursed Mirror"
    types := #[.artifact]
    asEntersMayCopyCreatureHasteUntilEot := true
  }
  let sanctumDef : CardDef := {
    name := "Phase13 Sanctum"
    types := #[.land]
    entersTappedUnlessBehold := some .villain
  }
  let villainCard : CardDef :=
    creature "Phase13 Hand Villain" ManaCost.empty #["Villain"] 2 2
  let putAndResolve (base : Game) (cd : CardDef) (act : Game → Game) : Game :=
    let g := insertObject base cd me (.hand me)
    let hid := ((g.player me).hand.filter (fun id => (g.object! id).name == cd.name))[0]!
    let (g1, _) := g.putOntoBattlefield hid me (cause := some testCause)
    act g1
  let pickRepl (pred : ReplacementEffectKind → Bool) (g : Game) : Game :=
    match g.pending with
    | .chooseReplacement p cs =>
      match cs.find? (fun c => pred c.kind) with
      | some rid => mustApply g p (.chooseReplacement rid)
      | none => g
    | _ => g
  let gRoom := putAndResolve afterDraw roomDef
    (pickRepl (fun | .asEntersChooseColor .blue => true | _ => false))
  let roomPerm := (gRoom.battlefield.filter (·.name == "Phase13 Room of Refuge"))[0]!
  let roomMoveAfterOk :=
    gRoom.events.any (fun e =>
      match e.change with
      | .rules (.zone (.moved _ afterSnap _ .battlefield ..)) =>
        afterSnap.id == some roomPerm.id && afterSnap.chosenColor == some .blue
      | _ => false)
  let gParty := putAndResolve afterDraw partyDef (fun g => mustApply g me (.chooseName "Elf"))
  let partyPerm := (gParty.battlefield.filter (·.name == "Phase13 Unexpected Party"))[0]!
  let gGollum := putAndResolve afterDraw gollumDef
    (pickRepl (fun | .asEntersChooseOdd true => true | _ => false))
  let gollumPerm := (gGollum.battlefield.filter (·.name == "Phase13 Gollum"))[0]!
  let gMage := putAndResolve afterDraw mageDef (fun g => mustApply g me (.chooseName "Lightning Bolt"))
  let magePerm := (gMage.battlefield.filter (·.name == "Phase13 Meddling Mage"))[0]!
  let gEmissary := putAndResolve afterDraw emissaryDef
    (pickRepl (fun | .asEntersChooseCardType .creature => true | _ => false))
  let emissaryPerm := (gEmissary.battlefield.filter (·.name == "Phase13 Emissary"))[0]!
  let gSiege := putAndResolve afterDraw siegeDef
    (pickRepl (fun | .asEntersChooseAnchor "Mardu" => true | _ => false))
  let siegePerm := (gSiege.battlefield.filter (·.name == "Phase13 Windcrag Siege"))[0]!
  let gMirrorBase := addPermanent afterDraw hero opp opp
  let heroOnBfId := (gMirrorBase.battlefield.filter (·.name == hero.name))[0]!.id
  let gMirrorCopy := putAndResolve gMirrorBase mirrorDef
    (pickRepl (fun | .entersAsCopyCreatureUntilEot tid => tid == heroOnBfId | _ => false))
  let gMirrorDecl := putAndResolve gMirrorBase mirrorDef
    (pickRepl (fun | .declineEntersAsCopy => true | _ => false))
  let gSanctumBase := insertObject afterDraw villainCard me (.hand me)
  let villainHandId := ((gSanctumBase.player me).hand.filter (fun id => (gSanctumBase.object! id).name == "Phase13 Hand Villain"))[0]!
  let gSanctumAcc := putAndResolve gSanctumBase sanctumDef
    (pickRepl (fun | .entersUntappedBehold bid _ => bid == villainHandId | _ => false))
  let sanctumAccPerm := (gSanctumAcc.battlefield.filter (·.name == "Phase13 Sanctum"))[0]!
  let gSanctumDec := putAndResolve gSanctumBase sanctumDef
    (pickRepl (fun | .entersTappedDeclineBehold => true | _ => false))
  let sanctumDecPerm := (gSanctumDec.battlefield.filter (·.name == "Phase13 Sanctum"))[0]!
  let asEntersAllOk :=
    roomPerm.status.chosenColor == some .blue && roomMoveAfterOk &&
    partyPerm.status.chosenCreatureType == some CardSubtype.elf &&
    gollumPerm.status.chosenOdd == some true &&
    magePerm.status.chosenName == some "Lightning Bolt" &&
    emissaryPerm.status.chosenCardType == some .creature &&
    siegePerm.status.chosenAnchor == some "Mardu" &&
    (gMirrorCopy.battlefield.filter (fun o => gMirrorCopy.name o == hero.name)).size == 2 &&
    (gMirrorDecl.battlefield.filter (fun o => gMirrorDecl.name o == "Phase13 Cursed Mirror")).size == 1 &&
    !sanctumAccPerm.status.tapped &&
    gSanctumAcc.events.any (fun e =>
      match e.change with
      | .rules (.player (.revealed p ids)) => p == me && ids == #[villainHandId]
      | _ => false) &&
    sanctumDecPerm.status.tapped &&
    [gRoom, gParty, gGollum, gMage, gEmissary, gSiege, gMirrorCopy, gMirrorDecl, gSanctumAcc, gSanctumDec].all
      (fun g => Game.replayEvents g.events == g)

  -- 4. Pausing `replaceUntap` & Saga `addLoreCounters` `replaceCountersPutChoice`.
  let gUntap0 :=
    let g := addPermanent afterDraw bear me me
    let bid := (g.battlefield.filter (·.name == bear.name))[0]!.id
    let g := g.becomeTapped (g.object! bid) (cause := some testCause)
    let g := g.recordPutCounters bid .stun 2 (some me) (cause := some testCause)
    g.createEffect
      (.replacement { id := { kind := .stunCounterUntap, object := some bid, grantor := some ⟨8888⟩ },
                      affectedPlayer := me, kind := .stunCounterUntap bid } .untilEndOfTurn)
  let stunBearId := (gUntap0.battlefield.filter (·.name == bear.name))[0]!.id
  let gUntapPaused := gUntap0.untapPermanent (gUntap0.object! stunBearId) (cause := some testCause)
  let untapAsked :=
    match gUntapPaused.pending with
    | .chooseReplacement p cs => p == me && cs.size == 2
    | _ => false
  let gUntapDone :=
    match gUntapPaused.pending with
    | .chooseReplacement _ cs => mustApply gUntapPaused me (.chooseReplacement cs[0]!)
    | _ => gUntapPaused
  let stunAfter := gUntapDone.object! stunBearId
  let untapReplacedCauseOk :=
    gUntapDone.events.any (fun e =>
      match e.change, e.cause? with
      | .rules (.permanent (.counters (.object snap) .stun (.removed 1) _)), some (.replaced rid _) =>
        snap.id == some stunBearId && rid.kind == .stunCounterUntap
      | _, _ => false)
  -- `untapPermanent` with `duringUntapStep := true` records `PermanentEvent.untapped` (not stun removal)
  -- and respects an explicit caller `cause` while defaulting `none` to `.turnBased .untapAll`:
  let gUntapStep0 :=
    let g := addPermanent afterDraw bear me me
    let bid := (g.battlefield.filter (·.name == bear.name))[0]!.id
    (g.becomeTapped (g.object! bid) (cause := some testCause), bid)
  let preUntapStepIdx := gUntapStep0.1.events.size
  let gUntapStepDef := gUntapStep0.1.untapPermanent (gUntapStep0.1.object! gUntapStep0.2) (duringUntapStep := true)
  let gUntapStepExplicit :=
    gUntapStep0.1.untapPermanent (gUntapStep0.1.object! gUntapStep0.2)
      (duringUntapStep := true) (cause := some testCause)
  let untapStepSlice := gUntapStepDef.events.extract preUntapStepIdx gUntapStepDef.events.size
  let untapStepExplicitSlice := gUntapStepExplicit.events.extract preUntapStepIdx gUntapStepExplicit.events.size
  let untapStepFlagOk :=
    !(gUntapStepDef.object! gUntapStep0.2).status.tapped &&
    untapStepSlice.any (fun e =>
      match e.change, e.cause? with
      | .rules (.permanent (.untapped snap)), some (.turnBased .untapAll) =>
        snap.id == some gUntapStep0.2
      | _, _ => false) &&
    !untapStepSlice.any (fun e =>
      match e.change with
      | .rules (.permanent (.counters _ .stun _ _)) => true
      | _ => false) &&
    untapStepExplicitSlice.any (fun e =>
      match e.change, e.cause? with
      | .rules (.permanent (.untapped snap)), some c =>
        snap.id == some gUntapStep0.2 && c == testCause
      | _, _ => false) &&
    Game.replayEvents gUntapStepDef.events == gUntapStepDef &&
    Game.replayEvents gUntapStepExplicit.events == gUntapStepExplicit

  let sagaDef : CardDef := {
    name := "Phase13 Saga"
    types := #[.enchantment]
    subtypes := #["Saga"]
    saga := some {
      sacrificeAfter := "V"
      chapters := #[
        SagaChapter.of "I" "Gain 1 life." (.gainLife 1),
        SagaChapter.of "II" "Gain 1 life." (.gainLife 1),
        SagaChapter.of "III" "Gain 1 life." (.gainLife 1),
        SagaChapter.of "IV" "Gain 1 life." (.gainLife 1),
        SagaChapter.of "V" "Gain 1 life." (.gainLife 1)
      ]
    }
  }
  let gSaga0 :=
    let g := addPermanent afterDraw sagaDef me me
    let sid := (g.battlefield.filter (·.name == "Phase13 Saga"))[0]!.id
    let g := g.createEffect
      (.replacement { id := { kind := .addCountersPut, object := some sid, grantor := some ⟨8889⟩ },
                      affectedPlayer := me, kind := .modifyCountersPut (some sid) none (add := 1) (mult := 1) } .untilEndOfTurn)
    g.createEffect
      (.replacement { id := { kind := .multiplyCountersPut, object := some sid, grantor := some ⟨8890⟩ },
                      affectedPlayer := me, kind := .modifyCountersPut (some sid) none (add := 0) (mult := 2) } .untilEndOfTurn)
  let sagaId := (gSaga0.battlefield.filter (·.name == "Phase13 Saga"))[0]!.id
  let preLore := (gSaga0.object! sagaId).status.lore
  let gSagaPaused := gSaga0.addLoreCounters (gSaga0.object! sagaId) 1
  let sagaAsked :=
    match gSagaPaused.pending with
    | .chooseReplacement p cs => p == me && cs.size == 2
    | _ => false
  -- Choose `+1` first (`(1 + 1) * 2 = 4` lore counters added!).
  let gSagaDone :=
    pickRepl (fun | .addCountersPut => true | _ => false) gSagaPaused
  let sagaReplacedCauseOk :=
    gSagaDone.events.any (fun e =>
      match e.change, e.cause? with
      | .rules (.permanent (.counters (.object snap) .lore (.put 4) _)), some (.replaced ..) =>
        snap.id == some sagaId
      | _, _ => false)
  let untapAndSagaOk :=
    untapAsked && stunAfter.status.tapped && stunAfter.status.stun == 1 && untapReplacedCauseOk &&
    untapStepFlagOk &&
    Game.replayEvents gUntapDone.events == gUntapDone &&
    sagaAsked && (gSagaDone.object! sagaId).status.lore == preLore + 4 && sagaReplacedCauseOk &&
    Game.replayEvents gSagaDone.events == gSagaDone

  -- 5. Pain-land `DamageEvent.dealt` + prevention (CR 120.3a / 615).
  let gPainPlain0 := addPermanent afterDraw painLandDef me me
  let painPlainId := (gPainPlain0.battlefield.filter (·.name == "Phase13 Pain Land"))[0]!.id
  let prePainEv := gPainPlain0.events.size
  let gPainTapped := mustApply gPainPlain0 me (.tapForMana painPlainId (.colored .red))
  let painSlice := gPainTapped.events.extract prePainEv gPainTapped.events.size
  let painDealtEventOk :=
    painSlice.any (fun e =>
      match e.change with
      | .rules (.damage (.dealt pkts)) =>
        pkts.any (fun pkt =>
          pkt.recipient == .player me && pkt.amount == 1 && !pkt.combat &&
            pkt.source.id == some painPlainId)
      | _ => false) &&
    painSlice.any (fun e =>
      match e.change with
      | .rules (.life (.lost p 1 true false)) => p == me
      | _ => false)
  let gPainProt0 := gPainPlain0.createEffect (.protectionFromEverything me)
  let gPainProtTapped := mustApply gPainProt0 me (.tapForMana painPlainId (.colored .red))
  let painAllOk :=
    painDealtEventOk &&
    (gPainTapped.player me).life == 19 &&
    (gPainTapped.player me).manaPool.red == 1 &&
    (gPainProtTapped.player me).life == 20 &&
    (gPainProtTapped.player me).manaPool.red == 1 &&
    Game.replayEvents gPainTapped.events == gPainTapped &&
    Game.replayEvents gPainProtTapped.events == gPainProtTapped

  -- 6. CR 903.3 Commander zone-change persistence & `Start.materializeSeat`.
  let cmdDef : CardDef := {
    (creature "Phase13 Commander" (ManaCost.ofGeneric 2) #["Hero"] 3 3) with
    supertypes := #[.legendary]
  }
  let cmdCfg : StartConfig := {
    seats := #[
      { name := "Chandra", deck := testRedDeck, commanders := #[cmdDef] },
      { name := "Nissa", deck := testGreenDeck }
    ]
    format := .constructed
    seed := 7
    startingPlayer := some 0
  }
  let gCmdStart :=
    match Start.start cmdCfg with
    | .ok g => keepOpeningHands g 8
    | .error e => panic! e
  let cmdInit := (gCmdStart.objects.filter (fun o => o.name == "Phase13 Commander"))[0]!
  let (gCmd1, cmdStackId) := gCmdStart.move cmdInit.id .stack (some me) (cause := some testCause)
  let (gCmd2, cmdBfId) := gCmd1.move cmdStackId .battlefield (some me) (cause := some testCause)
  let (gCmd3, cmdGyId) := gCmd2.move cmdBfId (.graveyard me) none (cause := some testCause)
  let (gCmd4, cmdHandId) := gCmd3.move cmdGyId (.hand me) none (cause := some testCause)
  let (gCmd5, cmdLibId) := gCmd4.move cmdHandId (.library me) none (libraryPosition := some .top) (cause := some testCause)
  let (gCmd6, cmdExId) := gCmd5.move cmdLibId .exile none (cause := some testCause)
  let commanderAllOk :=
    cmdInit.zone == .command && cmdInit.isCommander &&
    (gCmd1.object! cmdStackId).isCommander &&
    (gCmd2.object! cmdBfId).isCommander &&
    (gCmd3.object! cmdGyId).isCommander &&
    (gCmd4.object! cmdHandId).isCommander &&
    (gCmd5.object! cmdLibId).isCommander &&
    (gCmd6.object! cmdExId).isCommander &&
    Game.replayEvents gCmd6.events == gCmd6

  -- 7. CR 800.4d `leftGame` waiting-trigger cleanup via single writer `applyPlayerEvent`.
  let threeCfg : StartConfig := {
    seats := #[
      { name := "Chandra", deck := testRedDeck },
      { name := "Nissa", deck := testGreenDeck },
      { name := "Liliana", deck := testRedDeck }
    ]
    format := .constructed
    seed := 3
    startingPlayer := some 0
  }
  let gThree0 :=
    match Start.start threeCfg with
    | .ok g => keepOpeningHands g 12
    | .error e => panic! e
  let gThreeQueued :=
    let g := gThree0.putReflexiveTrigger ⟨0⟩ none { resolution := .draw 1, phrase := "Draw a card" } (deferToPriority := true)
    g.putReflexiveTrigger ⟨1⟩ none { resolution := .draw 1, phrase := "Draw a card" } (deferToPriority := true)
  let gThreeConceded := gThreeQueued.concede ⟨0⟩
  -- Simultaneous SBA / leaving-caused reflexive triggers (Head of the Hunt, CR 800.4d):
  -- when player `⟨0⟩` loses the game in the same SBA sweep where an opponent's creature dies
  -- under `⟨0⟩`'s Head of the Hunt (or when `putReflexiveTrigger` runs after `⟨0⟩` left),
  -- no `waitingTriggers` controlled by `⟨0⟩` remain or are enqueued.
  let headTestDef : CardDef := {
    bear with
    name := "Phase13 Head of the Hunt"
    staticAbilities := #[.exileOppDeathCreateWolf]
  }
  let gThreeSba0 :=
    let g := addPermanent (addPermanent gThree0 headTestDef ⟨0⟩ ⟨0⟩) bear ⟨1⟩ ⟨1⟩
    let oppBear := (g.battlefield.filter (fun o => o.name == bear.name && o.owner == ⟨1⟩))[0]!
    let g := g.markDamageOn oppBear 2 "lethal" (cause := some testCause)
    g.loseLife ⟨0⟩ 20 (cause := some testCause)
  let gThreeSbaDone :=
    (gThreeSba0.checkSBA).putReflexiveTrigger ⟨0⟩ none
      { resolution := .draw 1, phrase := "Draw a card" } (deferToPriority := true)
  let leftGameTriggersOk :=
    gThreeQueued.waitingTriggers.size == 2 &&
    !gThreeConceded.over &&
    !gThreeConceded.waitingTriggers.any (·.controller == ⟨0⟩) &&
    (gThreeConceded.waitingTriggers.any (·.controller == ⟨1⟩) ||
      gThreeConceded.stack.any (·.controller == ⟨1⟩)) &&
    Game.replayEvents gThreeConceded.events == gThreeConceded &&
    (gThreeSbaDone.player ⟨0⟩).leftTheGame &&
    !gThreeSbaDone.waitingTriggers.any (·.controller == ⟨0⟩) &&
    Game.replayEvents gThreeSbaDone.events == gThreeSbaDone

  -- 8. Delayed spell-copy, combat-Treasure `matchTriggers`, & reflexive `WaitingTrigger` routing.
  let gDt0 :=
    let g := insertObject afterDraw freeDrawDef me (.hand me)
    let (g, dtCause1) := g.allocDelayedCause (some me)
    let g := g.registerDelayedTrigger { controller := me, kind := .copyNextInstantSorceryThisTurn, cause := dtCause1 }
    let (g, dtCause2) := g.allocDelayedCause (some me)
    g.registerDelayedTrigger { controller := me, kind := .lokiCopyNextInstantSorceryThisTurn none 2, cause := dtCause2 }
  let dtSpellH := ((gDt0.player me).hand.filter (fun id => (gDt0.object! id).name == "Phase13 Free Draw"))[0]!
  let handPreDt := (gDt0.player me).hand.size
  let gDtCast := mustApply gDt0 me (.cast dtSpellH)
  let gDtStacked := mustApply gDtCast me (.stackTriggers #[0, 1])
  -- Stack has [original, trig1, trig2]: resolve trig2 -> copy1, resolve copy1, resolve trig1 -> copy2, resolve copy2, resolve original!
  let gDtResolved := gDtStacked.resolveTop.resolveTop.resolveTop.resolveTop.resolveTop
  let dtEventsOk :=
    gDtResolved.delayedTriggers.isEmpty &&
    (gDtResolved.player me).hand.size == handPreDt - 1 + 3 &&
    gDtResolved.events.any (fun e => match e.change with | .rules (.delayedTrigger (.consumed _)) => true | _ => false) &&
    gDtResolved.events.any (fun e => match e.change with | .rules (.stackObject (.copied ..)) => true | _ => false) &&
    Game.replayEvents gDtResolved.events == gDtResolved
  -- Unconsumed delayed spell-copy expires at cleanup (`DelayedTriggerEvent.expired`).
  let gDtExp :=
    let (g, c) := afterDraw.allocDelayedCause (some me)
    let g := g.registerDelayedTrigger { controller := me, kind := .copyNextInstantSorceryThisTurn, cause := c }
    g.clearTurnActivations
  let dtExpireOk :=
    gDtExp.delayedTriggers.isEmpty &&
    gDtExp.events.any (fun e => match e.change with | .rules (.delayedTrigger (.expired _)) => true | _ => false) &&
    Game.replayEvents gDtExp.events == gDtExp

  -- Combat-damage Treasure separation: `combatDamageCreatesTreasureUntilEot` (1 Treasure on player only)
  -- vs Reaver Cleaver `equippedGetsTrampleAndCombatTreasures` (`that many` Treasures on player/planeswalker).
  let bigBear : CardDef := creature "Phase13 Big Bear" ManaCost.empty #["Bear"] 3 3
  let cleaverDef : CardDef := {
    name := "Phase13 Cleaver"
    types := #[.artifact]
    subtypes := #["Equipment"]
    staticAbilities := #[.equippedGetsTrampleAndCombatTreasures 1 1]
  }
  let gTrOne :=
    let g := addPermanent afterDraw bigBear me me
    let bid := (g.battlefield.filter (·.name == "Phase13 Big Bear"))[0]!.id
    let g := g.createEffect (.combatDamageCreatesTreasureUntilEot bid)
    let g := g.markAttacking bid (some (.player opp))
    let g := g.record (GameEvent.combatDamageAssigned g.turnNumber true #[{ source := bid, toPlayer := 3 }])
    (g.dealAssignedCombatDamage.receivePriority me).resolveTop
  let gTrCleaver :=
    let g := addPermanent (addPermanent afterDraw bigBear me me) cleaverDef me me
    let bearPerm := (g.battlefield.filter (·.name == "Phase13 Big Bear"))[0]!
    let cleaverPerm := (g.battlefield.filter (·.name == "Phase13 Cleaver"))[0]!
    let g := g.attachSourceTo cleaverPerm bearPerm
    let armed := (g.battlefield.filter (·.name == "Phase13 Big Bear"))[0]!
    let g := g.markAttacking armed.id (some (.player opp))
    let g := g.record (GameEvent.combatDamageAssigned g.turnNumber true #[{ source := armed.id, toPlayer := 4 }])
    (g.dealAssignedCombatDamage.receivePriority me).resolveTop
  let treasureRoutingOk :=
    gTrOne.countSubtype me .treasure == 1 &&
    gTrCleaver.countSubtype me .treasure == 4 &&
    Game.replayEvents gTrOne.events == gTrOne &&
    Game.replayEvents gTrCleaver.events == gTrCleaver &&
    dtEventsOk && dtExpireOk

  -- 9. Pre-move `PlayerEvent.revealed` & declined hand-or-library search shuffle.
  let preRevIdx := afterDraw.events.size
  let (gRevLib, hitId?, _) :=
    afterDraw.revealUntil me 5 (fun o => o.printed.isLand) #[] (cause := some testCause)
  let revSlice := gRevLib.events.extract preRevIdx gRevLib.events.size
  let preMoveRevealOk :=
    hitId?.isSome &&
    revSlice.any (fun e => match e.change with | .rules (.player (.revealed p ids)) => p == me && !ids.isEmpty | _ => false) &&
    !revSlice.any (fun e => match e.change with | .rules (.zone _) => true | _ => false) &&
    Game.replayEvents gRevLib.events == gRevLib

  let gSearch0 :=
    let g := insertObject (insertObject afterDraw bear me (.hand me)) bear me (.library me)
    g.beginLibrarySearch me (·.isCreature) "creature card" .battlefieldFromHandOrLibrary (alsoHand := true)
  let preSearchDecIdx := gSearch0.events.size
  let gSearchDeclined :=
    let g1 := mustApply gSearch0 me .decline
    match g1.pending with
    | .resolveRandom (.shuffleLibrary p) => mustApply g1 p (.supplyOrder #[])
    | _ => g1
  let decSlice := gSearchDeclined.events.extract preSearchDecIdx gSearchDeclined.events.size
  let searchDeclineOk :=
    decSlice.any (fun e => match e.change with | .rules (.player (.searched p _ _)) => p == me | _ => false) &&
    decSlice.any (fun e => match e.change with | .rules (.player (.shuffled p _)) => p == me | _ => false) &&
    Game.replayEvents gSearchDeclined.events == gSearchDeclined &&
    preMoveRevealOk

  -- 10. Departed-source `lastKnownBefore?` LKI & Step 4 audits (`effectiveMaxHandSize` timestamps,
  --     filter-scoped Layer 2 control expiration).
  let lethalLifelinker : CardDef := {
    (creature "Phase13 Lifelinker" ManaCost.empty #["Vampire"] 1 1) with
    keywords := Keywords.merge Keyword.lifelink Keyword.deathtouch
  }
  let toughBlocker : CardDef := creature "Phase13 Wall" ManaCost.empty #["Wall"] 0 5
  let gLki0 := addPermanent (addPermanent afterDraw lethalLifelinker me me) toughBlocker opp opp
  let vamp := (gLki0.battlefield.filter (·.name == "Phase13 Lifelinker"))[0]!
  let wall := (gLki0.battlefield.filter (·.name == "Phase13 Wall"))[0]!
  -- Vampire leaves battlefield BEFORE its 1 damage resolves: LKI preserves lifelink + deathtouch!
  let (gLkiLeft, _) := gLki0.move vamp.id .exile none (cause := some testCause)
  let vampLki? := gLkiLeft.lastKnownBefore? vamp.id
  let gLkiDmg :=
    (gLkiLeft.dealDamageToPermanent wall 1 (source := vampLki?) (cause := some testCause)).checkSBA
  -- CR 616.1 damage replacement choices on a departed source whose lifelink + deathtouch were
  -- granted on the battlefield (so `followMoved` to the graveyard card would drop them):
  let gLkiChoiceBase :=
    let g := addPermanent (addPermanent afterDraw bear me me) toughBlocker opp opp
    let bid := (g.battlefield.filter (·.name == bear.name))[0]!.id
    let g := g.createEffect
      (.keywordsUntilEot bid (Keywords.merge Keyword.lifelink Keyword.deathtouch))
      (cause := some testCause)
    let (g, _) := g.move bid (.graveyard me) none (cause := some testCause)
    let g := g.createEffect
      (.replacement { id := { kind := .noncombatDamagePlusOne, grantor := some ⟨8991⟩ },
                      affectedPlayer := opp, kind := .addNoncombatDamage none 1 } .untilEndOfTurn)
    let g := g.createEffect
      (.replacement { id := { kind := .equippedDealsDoubleDamage, grantor := some ⟨8992⟩ },
                      affectedPlayer := opp, kind := .multiplyDamage none 2 } .untilEndOfTurn)
    (g, bid)
  let depSrc? := gLkiChoiceBase.1.damageSourceById? gLkiChoiceBase.2
  let depSnap? := gLkiChoiceBase.1.lastKnownBefore? gLkiChoiceBase.2
  let wallChoiceObj := (gLkiChoiceBase.1.battlefield.filter (·.name == "Phase13 Wall"))[0]!
  -- (a) `dealDamageToPlayer` paused on `.chooseReplacement`: `(1 + 1) * 2 = 4` damage + 4 lifelink.
  let gChoicePlPaused :=
    gLkiChoiceBase.1.dealDamageToPlayer opp 1 (source := depSrc?) (cause := some testCause)
  let gChoicePlDone :=
    pickRepl (fun | .noncombatDamagePlusOne => true | _ => false) gChoicePlPaused
  -- (b) `dealDamageFrom` paused on `.chooseReplacement`: 4 damage (< 5 toughness) kills 0/5 wall via
  --     departed LKI deathtouch AND gains 4 life via departed LKI lifelink.
  let gChoiceFromPaused :=
    gLkiChoiceBase.1.dealDamageFrom bear.name wallChoiceObj 1 (source := depSrc?) (cause := some testCause)
  let gChoiceFromDone :=
    (pickRepl (fun | .noncombatDamagePlusOne => true | _ => false) gChoiceFromPaused).checkSBA
  -- (c) `markDamageOn` paused on `.chooseReplacement`: kills 0/5 wall via departed LKI deathtouch.
  let gChoiceMarkPaused :=
    gLkiChoiceBase.1.markDamageOn wallChoiceObj 1 "hit" (source := depSnap?) (cause := some testCause)
  let gChoiceMarkDone :=
    (pickRepl (fun | .noncombatDamagePlusOne => true | _ => false) gChoiceMarkPaused).checkSBA
  -- (d) `dealDamageToPlayers` across two opponents in `gThree0` with competing replacements:
  let gChoiceMulti0 :=
    let g := addPermanent gThree0 bear ⟨0⟩ ⟨0⟩
    let bid := (g.battlefield.filter (·.name == bear.name))[0]!.id
    let g := g.createEffect
      (.keywordsUntilEot bid Keyword.lifelink) (cause := some testCause)
    let (g, _) := g.move bid (.graveyard ⟨0⟩) none (cause := some testCause)
    let g := g.createEffect
      (.replacement { id := { kind := .noncombatDamagePlusOne, grantor := some ⟨8993⟩ },
                      affectedPlayer := ⟨1⟩, kind := .addNoncombatDamage none 1 } .untilEndOfTurn)
    let g := g.createEffect
      (.replacement { id := { kind := .equippedDealsDoubleDamage, grantor := some ⟨8994⟩ },
                      affectedPlayer := ⟨1⟩, kind := .multiplyDamage none 2 } .untilEndOfTurn)
    (g, bid)
  let gChoiceMultiP1 :=
    gChoiceMulti0.1.dealDamageToPlayers #[⟨1⟩, ⟨2⟩] 1
      (source := gChoiceMulti0.1.damageSourceById? gChoiceMulti0.2) (cause := some testCause)
  let gChoiceMultiP2 :=
    pickRepl (fun | .noncombatDamagePlusOne => true | _ => false) gChoiceMultiP1
  let gChoiceMultiDone :=
    pickRepl (fun | .noncombatDamagePlusOne => true | _ => false) gChoiceMultiP2
  let lkiOk :=
    vampLki?.isSome &&
    (gLkiDmg.player me).life == 21 &&
    (gLkiDmg.findObject? wall.id).isNone &&
    Game.replayEvents gLkiDmg.events == gLkiDmg &&
    (match gChoicePlPaused.pending with | .chooseReplacement p cs => p == opp && cs.size == 2 | _ => false) &&
    (gChoicePlDone.player opp).life == 16 &&
    (gChoicePlDone.player me).life == 24 &&
    (match gChoiceFromPaused.pending with | .chooseReplacement p cs => p == opp && cs.size == 2 | _ => false) &&
    (gChoiceFromDone.findObject? wallChoiceObj.id).isNone &&
    (gChoiceFromDone.player me).life == 24 &&
    (match gChoiceMarkPaused.pending with | .chooseReplacement p cs => p == opp && cs.size == 2 | _ => false) &&
    (gChoiceMarkDone.findObject? wallChoiceObj.id).isNone &&
    (gChoiceMultiDone.player ⟨1⟩).life == 16 &&
    (gChoiceMultiDone.player ⟨2⟩).life == 16 &&
    (gChoiceMultiDone.player ⟨0⟩).life == 28 &&
    [gChoicePlDone, gChoiceFromDone, gChoiceMarkDone, gChoiceMultiDone].all
      (fun g => Game.replayEvents g.events == g)

  -- CR 613.7a `effectiveMaxHandSize` timestamp ordering:
  let noMaxDef : CardDef := {
    name := "Phase13 Reliquary"
    types := #[.artifact]
    staticAbilities := #[.noMaximumHandSize]
  }
  let capTwoDef : CardDef := {
    name := "Phase13 Cursed Rack"
    types := #[.artifact]
    staticAbilities := #[.maximumHandSize 2]
  }
  let gHsCapLast := addPermanent (addPermanent afterDraw noMaxDef me me) capTwoDef me me
  let gHsNoMaxLast := addPermanent (addPermanent afterDraw capTwoDef me me) noMaxDef me me
  let maxHandTsOk :=
    gHsCapLast.effectiveMaxHandSize me == some 2 &&
    gHsNoMaxLast.effectiveMaxHandSize me == none

  -- Filter-scoped Layer 2 control effect (`ObjectScope.creaturesControlledBy`) reverts control &
  -- clears stolen ring-bearer designation on EOT expiration:
  let gFiltCtrl0 :=
    let g := addPermanent afterDraw bear opp opp
    let bid := (g.battlefield.filter (·.name == bear.name))[0]!.id
    let g := g.createEffect
      (.layered (.creaturesControlledBy opp) (.control me) .untilEndOfTurn)
      (cause := some testCause)
    let g := g.setRingBearer me (some bid) (cause := some testCause)
    (g, bid)
  let preExpIdx := gFiltCtrl0.1.events.size
  let gFiltExpired := gFiltCtrl0.1.clearEOT
  let expSlice := gFiltExpired.events.extract preExpIdx gFiltExpired.events.size
  let filterCtrlExpOk :=
    gFiltCtrl0.1.controllerOf (gFiltCtrl0.1.object! gFiltCtrl0.2) == some me &&
    (gFiltCtrl0.1.player me).ringBearerId == some gFiltCtrl0.2 &&
    gFiltExpired.controllerOf (gFiltExpired.object! gFiltCtrl0.2) == some opp &&
    (gFiltExpired.player me).ringBearerId == none &&
    expSlice.any (fun e =>
      match e.change with
      | .rules (.permanent (.designation snap .ringBearer false)) =>
        snap.id == some gFiltCtrl0.2
      | _ => false) &&
    Game.replayEvents gFiltExpired.events == gFiltExpired

  -- Continuation resumption (`finishFraChoice`) across activation cost-pick reversal
  -- (`beginActivationPayment` / `afterTargetsChosen`) and `chooseCastFromLooked`
  -- (`beginResolutionCastTargets` illegal mode/target, synchronous cast, and decline):
  let mkSeqFrame (g : Game) (gain : Nat) : Game :=
    (g.change (.pushContinuationFrame {})).change (.triggerSequenceRest (some {
      controller := me
      ability := TriggeredAbility.fra .youCastNoncreature "" (.draw 1)
      sourceId := none
      targets := #[]
      steps := [.gainLife (.fixed gain)]
    }))
  let sacArtEngineDef : CardDef := {
    name := "Phase13 Sac Artifact Engine"
    types := #[.artifact]
    activatedAbilities := #[{
      cost := { mana := ManaCost.ofGeneric 1, fra := .sacrificeAnotherArtifact }
      effect := { resolution := .draw 1, phrase := "Draw a card" }
    }]
  }
  let gActPayRev :=
    let g := (addPermanent afterDraw sacArtEngineDef me me).createTreasureTokens me 1 (cause := some testCause)
    let engId := (g.battlefield.filter (·.name == "Phase13 Sac Artifact Engine"))[0]!.id
    let trId := (g.battlefield.filter (·.printed.isToken))[0]!.id
    let g := mkSeqFrame g 4
    let gAct := mustApply g me (.activate engId 0)
    let gMana := mustApply gAct me (.tapForMana trId (.colored .red))
    (mustApply gMana me .pay, trId)
  let actPayRevOk :=
    gActPayRev.1.triggerSequenceRest.isNone &&
    gActPayRev.1.continuations.isEmpty &&
    (gActPayRev.1.player me).life == 24 &&
    (gActPayRev.1.findObject? gActPayRev.2).any (·.isOnBattlefield) &&
    gActPayRev.1.stack.isEmpty &&
    Game.replayEvents gActPayRev.1.events == gActPayRev.1
  let tapTwoTargetedDef : CardDef := {
    name := "Phase13 Tap Two Targeted Engine"
    types := #[.creature]
    subtypes := #["Artificer"]
    power := some 2
    toughness := some 2
    activatedAbilities := #[{
      cost := { fra := .tapTwoUntappedArtifacts }
      effect := {
        targeting := .of .player
        resolution := .gainLife 1
        phrase := "Target player gains 1 life"
      }
    }]
  }
  let gActTargetRev :=
    let g := (addPermanent afterDraw tapTwoTargetedDef me me).createTreasureTokens me 2 (cause := some testCause)
    let engId := (g.battlefield.filter (·.name == "Phase13 Tap Two Targeted Engine"))[0]!.id
    let tr0 := (g.battlefield.filter (·.printed.isToken))[0]!.id
    let g := mkSeqFrame g 4
    let gAct := mustApply g me (.activate engId 0)
    let gTapOne := gAct.becomeTapped (gAct.object! tr0) (cause := some testCause)
    mustApply gTapOne me (.target (.player me))
  let actTargetRevOk :=
    gActTargetRev.triggerSequenceRest.isNone &&
    gActTargetRev.continuations.isEmpty &&
    (gActTargetRev.player me).life == 24 &&
    gActTargetRev.stack.isEmpty &&
    Game.replayEvents gActTargetRev.events == gActTargetRev
  let impossibleModalDef : CardDef := {
    name := "Phase13 Impossible Modal"
    manaCost := ManaCost.empty
    types := #[.sorcery]
    spellModes := #[
      { targeting := .of .creature, resolution := .destroyTarget, phrase := "Destroy target creature" },
      { targeting := .of .creature, resolution := .exileTarget, phrase := "Exile target creature" }
    ]
  }
  let mkTopLook1 (d : CardDef) : Game × ObjectId :=
    let g := insertObject afterDraw d me (.library me)
    let cid := (g.player me).library.back!
    let g := mkSeqFrame g 3
    (g.beginMayCastFromLooked me 1 5, cid)
  let (gLookNoTgt0, lookNoTgtId) := mkTopLook1 impossibleRemDef
  let gLookNoTgt := mustApply gLookNoTgt0 me (.cast lookNoTgtId)
  let (gLookNoMode0, lookNoModeId) := mkTopLook1 impossibleModalDef
  let gLookNoMode := mustApply gLookNoMode0 me (.cast lookNoModeId)
  let (gLookSync0, lookSyncId) := mkTopLook1 freeDrawDef
  let gLookSync := mustApply gLookSync0 me (.cast lookSyncId)
  let gLookDec := mustApply gLookSync0 me .decline
  let lookedContAllOk :=
    gLookNoTgt.triggerSequenceRest.isNone && gLookNoTgt.continuations.isEmpty &&
    (gLookNoTgt.player me).life == 23 && gLookNoTgt.stack.isEmpty &&
    gLookNoTgt.log.any (fun s => mentions s "has no legal target and can't be cast") &&
    gLookNoMode.triggerSequenceRest.isNone && gLookNoMode.continuations.isEmpty &&
    (gLookNoMode.player me).life == 23 && gLookNoMode.stack.isEmpty &&
    gLookSync.triggerSequenceRest.isNone && gLookSync.continuations.isEmpty &&
    (gLookSync.player me).life == 23 && gLookSync.stack.size == 1 &&
    gLookDec.triggerSequenceRest.isNone && gLookDec.continuations.isEmpty &&
    (gLookDec.player me).life == 23 && gLookDec.stack.isEmpty &&
    [gLookNoTgt, gLookNoMode, gLookSync, gLookDec].all (fun g => Game.replayEvents g.events == g)
  let reviewRound2ContOk := actPayRevOk && actTargetRevOk && lookedContAllOk

  -- Successful ability activations (`becomeActivated`) preserve and resume open
  -- continuations across immediate, mana-paid, `.costPicks`, `.sacrificePermanent`,
  -- and `.crew` accept paths, while preserving CR 117.3c priority outside continuations:
  let freeActDef : CardDef := {
    name := "Phase13 Free Engine"
    types := #[.artifact]
    activatedAbilities := #[{
      cost := {}
      effect := { resolution := .draw 1, phrase := "Draw a card" }
    }]
  }
  let manaActDef : CardDef := {
    name := "Phase13 Mana Engine"
    types := #[.artifact]
    activatedAbilities := #[{
      cost := { mana := ManaCost.ofGeneric 1 }
      effect := { resolution := .draw 1, phrase := "Draw a card" }
    }]
  }
  let sacOtherActDef : CardDef := {
    name := "Phase13 Sac Other Engine"
    types := #[.artifact]
    activatedAbilities := #[{
      cost := { sacrificeAnotherCreatureOrArtifact := true }
      effect := { resolution := .draw 1, phrase := "Draw a card" }
    }]
  }
  let crewVehDef : CardDef := {
    name := "Phase13 Crew Skiff"
    types := #[.artifact]
    subtypes := #["Vehicle"]
    power := some 3
    toughness := some 3
    crew := some 2
  }
  let gFreeActPaid :=
    let g := addPermanent afterDraw freeActDef me me
    let engId := (g.battlefield.filter (·.name == "Phase13 Free Engine"))[0]!.id
    mustApply (mkSeqFrame g 4) me (.activate engId 0)
  let gManaActPaid :=
    let g := (addPermanent afterDraw manaActDef me me).createTreasureTokens me 1 (cause := some testCause)
    let engId := (g.battlefield.filter (·.name == "Phase13 Mana Engine"))[0]!.id
    let trId := (g.battlefield.filter (·.printed.isToken))[0]!.id
    let g := mkSeqFrame g 4
    let g := mustApply g me (.activate engId 0)
    let g := mustApply g me (.tapForMana trId (.colored .red))
    mustApply g me .pay
  let gCostPicksPaid :=
    let g := (addPermanent afterDraw sacArtEngineDef me me).createTreasureTokens me 2 (cause := some testCause)
    let engId := (g.battlefield.filter (·.name == "Phase13 Sac Artifact Engine"))[0]!.id
    let trs := (g.battlefield.filter (·.printed.isToken)).map (·.id)
    let g := mkSeqFrame g 4
    let g := mustApply g me (.activate engId 0)
    let g := mustApply g me (.tapForMana trs[0]! (.colored .red))
    let g := mustApply g me .pay
    mustApply g me (.choosePermanents #[trs[1]!])
  let gSacOtherPaid :=
    let g := (addPermanent afterDraw sacOtherActDef me me).createTreasureTokens me 1 (cause := some testCause)
    let engId := (g.battlefield.filter (·.name == "Phase13 Sac Other Engine"))[0]!.id
    let trId := (g.battlefield.filter (·.printed.isToken))[0]!.id
    let g := mkSeqFrame g 4
    let g := mustApply g me (.activate engId 0)
    let g := mustApply g me .pay
    mustApply g me (.sacrifice trId)
  let gCrewPaid :=
    let g := addPermanent (addPermanent afterDraw crewVehDef me me) tapTwoTargetedDef me me
    let vehId := (g.battlefield.filter (·.name == "Phase13 Crew Skiff"))[0]!.id
    let pilotId := (g.battlefield.filter (·.name == "Phase13 Tap Two Targeted Engine"))[0]!.id
    let g := mkSeqFrame g 4
    let g := mustApply g me (.activate vehId 0)
    mustApply g me (.choosePermanents #[pilotId])
  let gOppCrewPrio :=
    let g := addPermanent (addPermanent afterDraw crewVehDef opp opp) tapTwoTargetedDef opp opp
    let g := mustApply g me .pass
    let vehId := (g.battlefield.filter (·.name == "Phase13 Crew Skiff"))[0]!.id
    let pilotId := (g.battlefield.filter (·.name == "Phase13 Tap Two Targeted Engine"))[0]!.id
    let g := mustApply g opp (.activate vehId 0)
    mustApply g opp (.choosePermanents #[pilotId])
  let paidActStates := [gFreeActPaid, gManaActPaid, gCostPicksPaid, gSacOtherPaid, gCrewPaid]
  let reviewRound3ContOk :=
    paidActStates.all (fun g =>
      g.triggerSequenceRest.isNone &&
      g.continuations.isEmpty &&
      (g.player me).life == 24 &&
      g.stack.size == 1 &&
      Game.replayEvents g.events == g) &&
    gOppCrewPrio.priority == opp &&
    gOppCrewPrio.stack.size == 1 &&
    Game.replayEvents gOppCrewPrio.events == gOppCrewPrio

  -- Activation and spell costs that pause on `Pending.chooseReplacement` chain
  -- `.receivePriority caster` outside open continuations (checking SBAs, putting
  -- waiting triggers on the stack, and preserving non-active activator/caster
  -- priority per CR 117.3c) and chain `.finishFraChoice` when `triggerSequenceRest`,
  -- `pendingMayCastFromExile`, or an outer `pendingReplacement` is open:
  let headHuntDef : CardDef :=
    { bear with name := "Phase13 Head Hunt", staticAbilities := #[.exileOppDeathCreateWolf] }
  let zeroToughDef : CardDef :=
    { bear with name := "Phase13 Zero Tough", power := some 0, toughness := some 0 }
  let sacSpellDef : CardDef := {
    name := "Phase13 Altar Bolt"
    manaCost := ManaCost.empty
    types := #[.instant]
    additionalCostSacrificeCreature := true
    spellEffect := some { resolution := .draw 1, phrase := "Draw a card" }
  }
  -- (a) Non-active player `opp` activates `sacOtherActDef` sacrificing a creature
  -- with competing death replacements (finality counter vs `me`'s `headHuntDef`):
  let (gOppActRepPaused, gOppActRepDone, oppZeroId) :=
    let g := addPermanent (addPermanent (addPermanent afterDraw sacOtherActDef opp opp) bear opp opp) headHuntDef me me
    let g := mustApply g me .pass
    let engId := (g.battlefield.filter (·.name == "Phase13 Sac Other Engine"))[0]!.id
    let sacBearId := (g.battlefield.filter (fun o => o.name == "Event Bear" && o.controller == some opp))[0]!.id
    let headId := (g.battlefield.filter (·.name == "Phase13 Head Hunt"))[0]!.id
    let idHead : ReplacementId := { kind := .exileOppDeath, object := some headId }
    let g := g.recordPutCounters sacBearId .finality 1 (some opp) (cause := some testCause)
    let g := addPermanent g zeroToughDef me me
    let zeroId := (g.battlefield.filter (·.name == "Phase13 Zero Tough"))[0]!.id
    let g := mustApply g opp (.activate engId 0)
    let g := mustApply g opp .pay
    let gPaused := mustApply g opp (.sacrifice sacBearId)
    let gDone := mustApply gPaused opp (.chooseReplacement idHead)
    (gPaused, gDone, zeroId)
  let oppActRepOk :=
    (match gOppActRepPaused.pending with | .chooseReplacement p cs => p == opp && cs.size == 2 | _ => false) &&
    gOppActRepDone.pending == .none &&
    gOppActRepDone.continuations.isEmpty &&
    gOppActRepDone.waitingTriggers.isEmpty &&
    gOppActRepDone.stack.size == 2 &&
    gOppActRepDone.priority == opp &&
    (gOppActRepDone.findObject? oppZeroId).all (!·.isOnBattlefield) &&
    Game.replayEvents gOppActRepPaused.events == gOppActRepPaused &&
    Game.replayEvents gOppActRepDone.events == gOppActRepDone
  -- (b) Non-active player `opp` casts an instant with `additionalCostSacrificeCreature`
  -- whose sacrifice pauses on `Pending.chooseReplacement`:
  let (gOppSpellRepPaused, gOppSpellRepDone, oppSpellZeroId) :=
    let g := insertObject (addPermanent (addPermanent afterDraw bear opp opp) headHuntDef me me) sacSpellDef opp (.hand opp)
    let spellCardId := (g.player opp).hand.back!
    let g := mustApply g me .pass
    let sacBearId := (g.battlefield.filter (fun o => o.name == "Event Bear" && o.controller == some opp))[0]!.id
    let headId := (g.battlefield.filter (·.name == "Phase13 Head Hunt"))[0]!.id
    let idHead : ReplacementId := { kind := .exileOppDeath, object := some headId }
    let g := g.recordPutCounters sacBearId .finality 1 (some opp) (cause := some testCause)
    let g := addPermanent g zeroToughDef me me
    let zeroId := (g.battlefield.filter (·.name == "Phase13 Zero Tough"))[0]!.id
    let g := mustApply g opp (.cast spellCardId)
    let g := mustApply g opp .pay
    let gPaused := mustApply g opp (.sacrifice sacBearId)
    let gDone := mustApply gPaused opp (.chooseReplacement idHead)
    (gPaused, gDone, zeroId)
  let oppSpellRepOk :=
    (match gOppSpellRepPaused.pending with | .chooseReplacement p cs => p == opp && cs.size == 2 | _ => false) &&
    gOppSpellRepDone.pending == .none &&
    gOppSpellRepDone.continuations.isEmpty &&
    gOppSpellRepDone.waitingTriggers.isEmpty &&
    gOppSpellRepDone.stack.size == 2 &&
    gOppSpellRepDone.priority == opp &&
    (gOppSpellRepDone.findObject? oppSpellZeroId).all (!·.isOnBattlefield) &&
    Game.replayEvents gOppSpellRepPaused.events == gOppSpellRepPaused &&
    Game.replayEvents gOppSpellRepDone.events == gOppSpellRepDone
  -- (c) Doom Reigns `.mayCastUpToFromExile` + `triggerSequenceRest` across a spell
  -- sacrifice cost that pauses on `Pending.chooseReplacement`:
  let (gQueueSpellPaused, gQueueSpellDone) :=
    let g := addPermanent (addPermanent afterDraw bear me me) headHuntDef opp opp
    let sacBearId := (g.battlefield.filter (fun o => o.name == "Event Bear" && o.controller == some me))[0]!.id
    let headId := (g.battlefield.filter (·.name == "Phase13 Head Hunt"))[0]!.id
    let idHead : ReplacementId := { kind := .exileOppDeath, object := some headId }
    let g := g.recordPutCounters sacBearId .finality 1 (some me) (cause := some testCause)
    let g := insertObject (insertObject g sacSpellDef me .exile) freeDrawDef me .exile
    let exSac := (g.objects.filter (fun o => o.name == "Phase13 Altar Bolt" && o.zone == .exile))[0]!.id
    let exDraw := (g.objects.filter (fun o => o.name == "Phase13 Free Draw" && o.zone == .exile))[0]!.id
    let g := (mkSeqFrame g 4).change (.pending (.fraChoice me (.mayCastUpToFromExile #[exSac, exDraw] 2)))
    let g := mustApply g me (.choosePermanents #[exSac])
    let g := mustApply g me .pay
    let gPaused := mustApply g me (.sacrifice sacBearId)
    let gAfterFirst := mustApply gPaused me (.chooseReplacement idHead)
    let gDone := mustApply gAfterFirst me (.choosePermanents #[exDraw])
    (gPaused, gDone)
  let queueSpellRepOk :=
    (match gQueueSpellPaused.pending with | .chooseReplacement p cs => p == me && cs.size == 2 | _ => false) &&
    gQueueSpellDone.pending == .none &&
    gQueueSpellDone.pendingMayCastFromExile.isNone &&
    gQueueSpellDone.triggerSequenceRest.isNone &&
    gQueueSpellDone.continuations.isEmpty &&
    gQueueSpellDone.waitingTriggers.isEmpty &&
    (gQueueSpellDone.player me).life == 24 &&
    gQueueSpellDone.stack.size == 3 &&
    Game.replayEvents gQueueSpellPaused.events == gQueueSpellPaused &&
    Game.replayEvents gQueueSpellDone.events == gQueueSpellDone
  -- (d) Activation with `.costPicks` (`sacArtEngineDef`) while both `triggerSequenceRest`
  -- and an outer `pendingReplacement` are open, and the sacrificed artifact creature
  -- pauses on `Pending.chooseReplacement`:
  let artBearDef : CardDef :=
    { bear with name := "Phase13 Clockwork Bear", types := #[.artifact, .creature] }
  let (gActOuterPaused, gActOuterDone) :=
    let g := (addPermanent (addPermanent (addPermanent afterDraw sacArtEngineDef me me) artBearDef me me) headHuntDef opp opp).createTreasureTokens me 1 (cause := some testCause)
    let engId := (g.battlefield.filter (·.name == "Phase13 Sac Artifact Engine"))[0]!.id
    let artBearId := (g.battlefield.filter (·.name == "Phase13 Clockwork Bear"))[0]!.id
    let trId := (g.battlefield.filter (·.printed.isToken))[0]!.id
    let headId := (g.battlefield.filter (·.name == "Phase13 Head Hunt"))[0]!.id
    let idHead : ReplacementId := { kind := .exileOppDeath, object := some headId }
    let g := g.recordPutCounters artBearId .finality 1 (some me) (cause := some testCause)
    let g := (mkSeqFrame g 4).change (.pendingReplacement (some .checkSBA))
    let g := mustApply g me (.activate engId 0)
    let g := mustApply g me (.tapForMana trId (.colored .red))
    let g := mustApply g me .pay
    let gPaused := mustApply g me (.choosePermanents #[artBearId])
    let gDone := mustApply gPaused me (.chooseReplacement idHead)
    (gPaused, gDone)
  let actOuterRepOk :=
    (match gActOuterPaused.pending with | .chooseReplacement p cs => p == me && cs.size == 2 | _ => false) &&
    gActOuterDone.pending == .none &&
    gActOuterDone.triggerSequenceRest.isNone &&
    gActOuterDone.continuations.isEmpty &&
    gActOuterDone.waitingTriggers.isEmpty &&
    (gActOuterDone.player me).life == 24 &&
    gActOuterDone.stack.size == 2 &&
    Game.replayEvents gActOuterPaused.events == gActOuterPaused &&
    Game.replayEvents gActOuterDone.events == gActOuterDone
  let reviewRound4ContOk := oppActRepOk && oppSpellRepOk && queueSpellRepOk && actOuterRepOk

  let mustHold (label : String) (ok : Bool) : Bool :=
    if ok then true else panic! s!"Phase 13 guard failed: {label}"
  mustHold "actionIrrevOk" actionIrrevOk &&
    mustHold "batchPauseReplayOk" batchPauseReplayOk &&
    mustHold "continuationsAllOk" continuationsAllOk &&
    mustHold "asEntersAllOk" asEntersAllOk &&
    mustHold "untapAndSagaOk" untapAndSagaOk &&
    mustHold "painAllOk" painAllOk &&
    mustHold "commanderAllOk" commanderAllOk &&
    mustHold "leftGameTriggersOk" leftGameTriggersOk &&
    mustHold "treasureRoutingOk" treasureRoutingOk &&
    mustHold "searchDeclineOk" searchDeclineOk &&
    mustHold "lkiOk" lkiOk &&
    mustHold "maxHandTsOk" maxHandTsOk &&
    mustHold "filterCtrlExpOk" filterCtrlExpOk &&
    mustHold "reviewRound2ContOk" reviewRound2ContOk &&
    mustHold "reviewRound3ContOk" reviewRound3ContOk &&
    mustHold "reviewRound4ContOk" reviewRound4ContOk

/- Phase 13 Review Round 5 regressions: dual replacement pauses across
`CostPick` + `payActivationExtraCosts`, multi-step non-active priority
preservation via `proposalCheckpoint` (CR 117.3c), and deferred `becomeCast`
follow-ups (Path of Ancestry scry, `pendingMayCastFromExile`, and
`pendingFreeCopies`) after a cost pauses on `Pending.chooseReplacement`. -/
#guard
  let opp : PlayerId := ⟨1⟩
  let headHuntDef : CardDef :=
    { bear with name := "Phase13 Head Hunt", staticAbilities := #[.exileOppDeathCreateWolf] }
  let sacSpellDef : CardDef := {
    name := "Phase13 Altar Bolt"
    manaCost := ManaCost.empty
    types := #[.instant]
    additionalCostSacrificeCreature := true
    spellEffect := some { resolution := .draw 1, phrase := "Draw a card" }
  }
  let freeDrawDef : CardDef := {
    name := "Phase13 Free Draw"
    manaCost := ManaCost.empty
    types := #[.sorcery]
    spellEffect := some { resolution := .draw 1, phrase := "Draw a card" }
  }
  -- (a) `{T}, Sacrifice this, Sacrifice a legendary artifact` where BOTH the
  --     chosen legendary artifact AND the sacrificed source pause on
  --     `Pending.chooseReplacement` must defer `completeActivation` /
  --     `payActivationExtraCosts` until the first choice finishes instead of
  --     overwriting it:
  let mountDoomEngineDef : CardDef := {
    bear with
    name := "Phase13 Mount Doom Engine"
    activatedAbilities := #[{
      cost := { tap := true, sacrificeSource := true, sacrificeLegendaryArtifact := true }
      effect := { resolution := .draw 1, phrase := "Draw a card" }
    }]
  }
  let legArtBearDef : CardDef := {
    bear with
    name := "Phase13 Legendary Relic Bear"
    supertypes := #[.legendary]
    types := #[.artifact, .creature]
  }
  let (gMdPause1, gMdPause2, gMdDone, mdEngId, mdArtId) :=
    let g := addPermanent (addPermanent (addPermanent afterDraw mountDoomEngineDef me me) legArtBearDef me me) headHuntDef opp opp
    let engId := (g.battlefield.filter (·.name == "Phase13 Mount Doom Engine"))[0]!.id
    let artId := (g.battlefield.filter (·.name == "Phase13 Legendary Relic Bear"))[0]!.id
    let headId := (g.battlefield.filter (·.name == "Phase13 Head Hunt"))[0]!.id
    let idHead : ReplacementId := { kind := .exileOppDeath, object := some headId }
    let g := g.recordPutCounters engId .finality 1 (some me) (cause := some testCause)
    let g := g.recordPutCounters artId .finality 1 (some me) (cause := some testCause)
    let g := mustApply g me (.activate engId 0)
    let gP1 := mustApply g me (.choosePermanents #[artId])
    let gP2 := mustApply gP1 me (.chooseReplacement idHead)
    let gD := mustApply gP2 me (.chooseReplacement idHead)
    (gP1, gP2, gD, engId, artId)
  let mountDoomDualPauseOk :=
    (match gMdPause1.pending with | .chooseReplacement p cs => p == me && cs.size == 2 | _ => false) &&
    gMdPause1.proposedSpell.isSome &&
    (gMdPause1.findObject? mdEngId).any (fun o => o.isOnBattlefield && !o.status.tapped) &&
    (gMdPause1.findObject? mdArtId).any (·.isOnBattlefield) &&
    (match gMdPause2.pending with | .chooseReplacement p cs => p == me && cs.size == 2 | _ => false) &&
    (gMdPause2.findObject? mdArtId).all (!·.isOnBattlefield) &&
    (gMdPause2.findObject? mdEngId).any (fun o => o.isOnBattlefield && o.status.tapped) &&
    gMdDone.pending == .none &&
    gMdDone.continuations.isEmpty &&
    gMdDone.waitingTriggers.isEmpty &&
    (gMdDone.findObject? mdArtId).all (!·.isOnBattlefield) &&
    (gMdDone.findObject? mdEngId).all (!·.isOnBattlefield) &&
    gMdDone.stack.size == 3 &&
    gMdDone.priority == me &&
    Game.replayEvents gMdPause1.events == gMdPause1 &&
    Game.replayEvents gMdPause2.events == gMdPause2 &&
    Game.replayEvents gMdDone.events == gMdDone

  -- (b) Multi-step activation costs by non-active player `opp` where step 1 pauses
  --     on `Pending.chooseReplacement` (pushing a `ContinuationFrame`) and step 2
  --     does NOT pause must still return priority to `opp` (CR 117.3c) and drain
  --     `continuations`:
  let dualSacActDef : CardDef := {
    bear with
    name := "Phase13 Dual Sac Engine"
    activatedAbilities := #[{
      cost := { sacrificeSource := true, sacrificeAnotherCreatureOrArtifact := true }
      effect := { resolution := .draw 1, phrase := "Draw a card" }
    }]
  }
  let twoPickActDef : CardDef := {
    bear with
    name := "Phase13 Two Pick Engine"
    activatedAbilities := #[{
      cost := { sacrificeLegendaryArtifact := true, sacrificeAnotherCreature := true }
      effect := { resolution := .draw 1, phrase := "Draw a card" }
    }]
  }
  let gOppDualSacDone :=
    let g := addPermanent (addPermanent (addPermanent afterDraw dualSacActDef opp opp) bear opp opp) headHuntDef me me
    let g := mustApply g me .pass
    let engId := (g.battlefield.filter (·.name == "Phase13 Dual Sac Engine"))[0]!.id
    let plainBearId := (g.battlefield.filter (fun o => o.name == "Event Bear" && o.controller == some opp))[0]!.id
    let headId := (g.battlefield.filter (·.name == "Phase13 Head Hunt"))[0]!.id
    let idHead : ReplacementId := { kind := .exileOppDeath, object := some headId }
    let g := g.recordPutCounters engId .finality 1 (some opp) (cause := some testCause)
    let g := mustApply g opp (.activate engId 0)
    let g := mustApply g opp .pay
    let g := mustApply g opp (.chooseReplacement idHead)
    mustApply g opp (.sacrifice plainBearId)
  let gOppTwoPickDone :=
    let g := addPermanent (addPermanent (addPermanent (addPermanent afterDraw twoPickActDef opp opp) legArtBearDef opp opp) bear opp opp) headHuntDef me me
    let g := mustApply g me .pass
    let engId := (g.battlefield.filter (·.name == "Phase13 Two Pick Engine"))[0]!.id
    let legArtId := (g.battlefield.filter (fun o => o.name == "Phase13 Legendary Relic Bear" && o.controller == some opp))[0]!.id
    let plainBearId := (g.battlefield.filter (fun o => o.name == "Event Bear" && o.controller == some opp))[0]!.id
    let headId := (g.battlefield.filter (·.name == "Phase13 Head Hunt"))[0]!.id
    let idHead : ReplacementId := { kind := .exileOppDeath, object := some headId }
    let g := g.recordPutCounters legArtId .finality 1 (some opp) (cause := some testCause)
    let g := mustApply g opp (.activate engId 0)
    let g := mustApply g opp (.choosePermanents #[legArtId])
    let g := mustApply g opp (.chooseReplacement idHead)
    mustApply g opp (.choosePermanents #[plainBearId])
  let oppMultiStepPrioOk :=
    gOppDualSacDone.pending == .none &&
    gOppDualSacDone.continuations.isEmpty &&
    gOppDualSacDone.priority == opp &&
    gOppDualSacDone.stack.size == 3 &&
    Game.replayEvents gOppDualSacDone.events == gOppDualSacDone &&
    gOppTwoPickDone.pending == .none &&
    gOppTwoPickDone.continuations.isEmpty &&
    gOppTwoPickDone.priority == opp &&
    gOppTwoPickDone.stack.size == 3 &&
    Game.replayEvents gOppTwoPickDone.events == gOppTwoPickDone

  -- (c) Path of Ancestry scry after a creature spell's sacrifice cost pauses on
  --     `Pending.chooseReplacement` (for both active `me` and non-active `opp`):
  let poaDef5 : CardDef := {
    name := "Phase13 Path of Ancestry"
    types := #[.land]
    entersTapped := true
    tapAddCommanderIdentity := true
    commanderIdentityScryCreature := true
  }
  let elfCmdrDef5 : CardDef := {
    name := "Phase13 Elf Commander"
    manaCost := ⟨#[.colored .green]⟩
    types := #[.creature]
    supertypes := #[.legendary]
    subtypes := #["Elf"]
    power := some 2
    toughness := some 2
  }
  let elfSacCreatureDef : CardDef := {
    name := "Phase13 Altar Elf"
    manaCost := ⟨#[.colored .green]⟩
    types := #[.creature]
    subtypes := #["Elf"]
    keywords := { flash := true }
    power := some 1
    toughness := some 1
    additionalCostSacrificeCreature := true
  }
  let (gAncPaused, gAncScry, gAncDone) :=
    let g0 : Game :=
      match Start.start {
        seats := #[
          { name := "Chandra", deck := testRedDeck, commanders := #[elfCmdrDef5] },
          { name := "Nissa", deck := testGreenDeck }
        ]
        format := .constructed
        seed := 1
        startingPlayer := some 0
      } with
      | .ok g => passBoth (keepOpeningHands g 8)
      | .error e => panic! e
    let g := insertObject (addPermanent (addPermanent (addPermanent g0 poaDef5 me me) bear me me) headHuntDef opp opp) elfSacCreatureDef me (.hand me)
    let poaId := (g.battlefield.filter (fun (o : GameObject) => o.name == "Phase13 Path of Ancestry" && o.controller == some me))[0]!.id
    let sacBearId := (g.battlefield.filter (fun (o : GameObject) => o.name == "Event Bear" && o.controller == some me))[0]!.id
    let headId := (g.battlefield.filter (fun (o : GameObject) => o.name == "Phase13 Head Hunt"))[0]!.id
    let idHead : ReplacementId := { kind := .exileOppDeath, object := some headId }
    let elfSpellId := (g.player me).hand.back!
    let g := g.recordPutCounters sacBearId .finality 1 (some me) (cause := some testCause)
    let g := mustApply g me (.cast elfSpellId)
    let g := mustApply g me (.tapForMana poaId (.colored .green))
    let g := mustApply g me .pay
    let gPaused := mustApply g me (.sacrifice sacBearId)
    let gScry := mustApply gPaused me (.chooseReplacement idHead)
    let topId := (gScry.player me).library.back!
    let gDone := mustApply gScry me (.scry #[topId] #[])
    (gPaused, gScry, gDone)
  let gOppAncDone :=
    let g0 : Game :=
      match Start.start {
        seats := #[
          { name := "Chandra", deck := testRedDeck },
          { name := "Nissa", deck := testGreenDeck, commanders := #[elfCmdrDef5] }
        ]
        format := .constructed
        seed := 1
        startingPlayer := some 0
      } with
      | .ok g => passBoth (keepOpeningHands g 8)
      | .error e => panic! e
    let g := insertObject (addPermanent (addPermanent (addPermanent g0 poaDef5 opp opp) bear opp opp) headHuntDef me me) elfSacCreatureDef opp (.hand opp)
    let poaId := (g.battlefield.filter (fun (o : GameObject) => o.name == "Phase13 Path of Ancestry" && o.controller == some opp))[0]!.id
    let sacBearId := (g.battlefield.filter (fun (o : GameObject) => o.name == "Event Bear" && o.controller == some opp))[0]!.id
    let headId := (g.battlefield.filter (fun (o : GameObject) => o.name == "Phase13 Head Hunt"))[0]!.id
    let idHead : ReplacementId := { kind := .exileOppDeath, object := some headId }
    let elfSpellId := (g.player opp).hand.back!
    let g := g.recordPutCounters sacBearId .finality 1 (some opp) (cause := some testCause)
    let g := mustApply g me .pass
    let g := mustApply g opp (.cast elfSpellId)
    let g := mustApply g opp (.tapForMana poaId (.colored .green))
    let g := mustApply g opp .pay
    let g := mustApply g opp (.sacrifice sacBearId)
    let gScry := mustApply g opp (.chooseReplacement idHead)
    let topId := (gScry.player opp).library.back!
    mustApply gScry opp (.scry #[topId] #[])
  let ancestryAfterCostRepOk :=
    (match gAncPaused.pending with | .chooseReplacement p cs => p == me && cs.size == 2 | _ => false) &&
    (match gAncScry.pending with | .scry p 1 1 => p == me | _ => false) &&
    gAncDone.pending == Pending.none &&
    gAncDone.continuations.isEmpty &&
    gAncDone.priority == me &&
    gAncDone.stack.size == 2 &&
    gOppAncDone.pending == Pending.none &&
    gOppAncDone.continuations.isEmpty &&
    gOppAncDone.priority == opp &&
    gOppAncDone.stack.size == 2 &&
    Game.replayEvents gAncPaused.events == gAncPaused &&
    Game.replayEvents gAncScry.events == gAncScry &&
    Game.replayEvents gAncDone.events == gAncDone &&
    Game.replayEvents gOppAncDone.events == gOppAncDone

  -- (d) `pendingMayCastFromExile` and `pendingFreeCopies` offers must still run
  --     after a cast spell's sacrifice cost pauses on `Pending.chooseReplacement`:
  let (gMayExNext, gMayExDone) :=
    let g := addPermanent (addPermanent afterDraw bear me me) headHuntDef opp opp
    let sacBearId := (g.battlefield.filter (fun o => o.name == "Event Bear" && o.controller == some me))[0]!.id
    let headId := (g.battlefield.filter (·.name == "Phase13 Head Hunt"))[0]!.id
    let idHead : ReplacementId := { kind := .exileOppDeath, object := some headId }
    let g := g.recordPutCounters sacBearId .finality 1 (some me) (cause := some testCause)
    let g := insertObject (insertObject g sacSpellDef me .exile) freeDrawDef me .exile
    let exSac := (g.objects.filter (fun o => o.name == "Phase13 Altar Bolt" && o.zone == .exile))[0]!.id
    let exDraw := (g.objects.filter (fun o => o.name == "Phase13 Free Draw" && o.zone == .exile))[0]!.id
    let g := (g.change (.pushContinuationFrame {})).change (.pending (.fraChoice me (.mayCastUpToFromExile #[exSac, exDraw] 2)))
    let g := mustApply g me (.choosePermanents #[exSac])
    let g := mustApply g me .pay
    let g := mustApply g me (.sacrifice sacBearId)
    let gNext := mustApply g me (.chooseReplacement idHead)
    let gDone := mustApply gNext me (.choosePermanents #[exDraw])
    (gNext, gDone)
  let (gCopyNext, gCopyDone) :=
    let g := addPermanent (addPermanent afterDraw bear me me) headHuntDef opp opp
    let sacBearId := (g.battlefield.filter (fun o => o.name == "Event Bear" && o.controller == some me))[0]!.id
    let headId := (g.battlefield.filter (·.name == "Phase13 Head Hunt"))[0]!.id
    let idHead : ReplacementId := { kind := .exileOppDeath, object := some headId }
    let g := g.recordPutCounters sacBearId .finality 1 (some me) (cause := some testCause)
    let g := insertObject (insertObject g sacSpellDef me .exile) freeDrawDef me .exile
    let cpSac := (g.objects.filter (fun o => o.name == "Phase13 Altar Bolt" && o.zone == .exile))[0]!.id
    let cpDraw := (g.objects.filter (fun o => o.name == "Phase13 Free Draw" && o.zone == .exile))[0]!.id
    let g := (g.change (.pushContinuationFrame {})).change (.pending (.fraChoice me (.castCopiesFree #[cpSac, cpDraw] 4 2)))
    let g := mustApply g me (.cast cpSac)
    let g := mustApply g me .pay
    let g := mustApply g me (.sacrifice sacBearId)
    let gNext := mustApply g me (.chooseReplacement idHead)
    let gDone := mustApply gNext me (.cast cpDraw)
    (gNext, gDone)
  let exileAndCopyOffersAfterCostRepOk :=
    (match gMayExNext.pending with | .fraChoice p (.mayCastUpToFromExile ids left) => p == me && ids.size == 1 && left == 1 | _ => false) &&
    gMayExDone.pending == Pending.none &&
    gMayExDone.pendingMayCastFromExile.isNone &&
    gMayExDone.continuations.isEmpty &&
    gMayExDone.stack.size == 3 &&
    Game.replayEvents gMayExNext.events == gMayExNext &&
    Game.replayEvents gMayExDone.events == gMayExDone &&
    (match gCopyNext.pending with | .fraChoice p (.castCopiesFree ids _ left) => p == me && ids.size == 1 && left == 1 | _ => false) &&
    gCopyDone.pending == Pending.none &&
    gCopyDone.pendingFreeCopies.isNone &&
    gCopyDone.continuations.isEmpty &&
    gCopyDone.stack.size == 3 &&
    Game.replayEvents gCopyNext.events == gCopyNext &&
    Game.replayEvents gCopyDone.events == gCopyDone
  let reviewRound5ContOk :=
    mountDoomDualPauseOk && oppMultiStepPrioOk && ancestryAfterCostRepOk && exileAndCopyOffersAfterCostRepOk

  let mustHold (label : String) (ok : Bool) : Bool :=
    if ok then true else panic! s!"Phase 13 Round 5 guard failed: {label}"
  mustHold "mountDoomDualPauseOk" mountDoomDualPauseOk &&
    mustHold "oppMultiStepPrioOk" oppMultiStepPrioOk &&
    mustHold "ancestryAfterCostRepOk" ancestryAfterCostRepOk &&
    mustHold "exileAndCopyOffersAfterCostRepOk" exileAndCopyOffersAfterCostRepOk &&
    mustHold "reviewRound5ContOk" reviewRound5ContOk

/- Phase 14 isolation & replay tests:
   1. Paused `withProposalAction` / `activateManaAbility` CR 733.1 bracketing.
   2. Multi-step `payCostPickItems` `chooseReplacement` chaining & loyalty `+N`
      activation cost replacement (CR 118.11).
   3. Irreversible `lookedAt`, `searched`, and `drawFromEmptyAttempted` during
      CR 733.1 proposal reversal (plus SBA empty-library loss).
   4. Face-down morph `turnFaceUp` (`ProposalKind.turnFaceUp`, priority/control
      gates, CR 733.1 reversal, post-turn-face-up SBA) & mid-resolution `{X}`
      `castExiledAsAbilityResolves` (`resolutionCast := true`).
   5. Single-writer `entersWith` without duplicate post-entry counter events,
      Cursed Mirror EOT `isCopy == false`, `PendingReplacement.move` `attachedTo`
      preservation, replaced `ZoneVerb.discard` / `.sacrifice`,
      `recordPutCounters` replaced count `n'` (no double-multiply on
      `.tapAndStun` / `empowerJace`), and CR 119.5 `setLife` life gain.
   6. Combat `replaceDamage` CR 616.1 chooser, `DamageEvent.prevented`, and
      unpreventable shield + loyalty removal on planeswalkers (CR 120.3c / 122.1c).
   7. Simultaneous batch `preBattlefield` look-back, `.attackPumpPerPlains`
      `DelayedTrigger` routing & CR 608.2b fizzle, reflexive trigger CR 608.2b
      fizzle, and flicker `followMovedToZone?` isolation across a 2nd move.
   8. CR 800.4a/c/d/i/j multiplayer `concede` cleanup & replay determinism. -/
#guard
  let opp : PlayerId := ⟨1⟩
  let headHuntDef : CardDef :=
    { bear with name := "Phase14 Head Hunt", staticAbilities := #[.exileOppDeathCreateWolf] }
  let samsonDef14 : CardDef :=
    { bear with name := "Phase14 Doc Samson", staticAbilities := #[.extraCounterOnPermanents] }
  let pwPlusDef14 : CardDef := {
    name := "Phase14 Plus PW"
    supertypes := #[.legendary]
    types := #[.planeswalker]
    subtypes := #["Chandra"]
    loyalty := some 4
    activatedAbilities := #[{
      cost := { loyalty := some (.plus 1) }
      effect := { resolution := .draw 1, phrase := "Draw a card" }
    }]
  }
  let planDef14 : CardDef := {
    name := "Phase14 Plan"
    types := #[.enchantment]
  }
  let openProposalActionDepth (g : Game) : Nat :=
    g.events.foldl (fun d e =>
      match e.change with
      | .engine (.beginProposalAction _) => d + 1
      | .engine .endProposalAction => d - 1
      | _ => d) 0

  -- 1. Paused `activateManaAbility` CR 733.1 bracketing (pain land + damage choice + reversal).
  let rgSpellDef : CardDef := {
    name := "Phase14 RG Spell"
    manaCost := ⟨#[.colored .red, .colored .green]⟩
    types := #[.instant]
    spellEffect := some { resolution := .draw 1, phrase := "Draw a card" }
  }
  let painLandDef : CardDef := {
    name := "Phase14 Pain Land"
    types := #[.land]
    tapAddOneOfDealsDamage := some (#[.colored .red], 1)
  }
  let (gPainPaused, gPainResumed, gPainRev, painSpellId, painLandId) :=
    let g := addPermanent (addPermanent afterDraw bear opp opp) painLandDef me me
    let g := insertObject g rgSpellDef me (.hand me)
    let oppBearId := (g.battlefield.filter (fun o => o.name == "Event Bear" && o.controller == some opp))[0]!.id
    let landId := (g.battlefield.filter (·.name == "Phase14 Pain Land"))[0]!.id
    let spellId := (g.player me).hand.back!
    let idAddMe : ReplacementId := { kind := .addNoncombatDamage, object := some oppBearId }
    let idMulMe : ReplacementId := { kind := .multiplyDamage, object := some oppBearId }
    let g := (g.createEffect (.replacement {
      id := idAddMe, source := some oppBearId, controller := some opp,
      affectedPlayer := me, kind := .addNoncombatDamage (some landId) 2
    }) (cause := some testCause)).createEffect (.replacement {
      id := idMulMe, source := some oppBearId, controller := some opp,
      affectedPlayer := me, kind := .multiplyDamage (some landId) 2
    }) (cause := some testCause)
    let g := mustApply g me (.cast spellId)
    let gPaused := mustApply g me (.tapForMana landId (.colored .red))
    let gResumed := mustApply gPaused me (.chooseReplacement idAddMe)
    let gRev := mustApply gResumed me .pay
    (gPaused, gResumed, gRev, spellId, landId)
  let painLandBracketOk :=
    (match gPainPaused.pending with | .chooseReplacement p cs => p == me && cs.size == 2 | _ => false) &&
    openProposalActionDepth gPainPaused == 1 &&
    openProposalActionDepth gPainResumed == 0 &&
    gPainResumed.pending == .activateManaAbilities me &&
    (gPainResumed.player me).manaPool.red == 1 &&
    (gPainResumed.player me).life == 14 &&
    gPainRev.pending == .none &&
    gPainRev.proposedSpell.isNone &&
    gPainRev.proposalCheckpoint.isNone &&
    gPainRev.stack.isEmpty &&
    (gPainRev.player me).hand.contains painSpellId &&
    !(gPainRev.object! painLandId).status.tapped &&
    (gPainRev.player me).manaPool.total == 0 &&
    (gPainRev.player me).life == 20 &&
    [gPainPaused, gPainResumed, gPainRev].all (fun g =>
      Game.replayEvents g.events == g && allRulesEventsClassified g)

  -- 2. Multi-item `payCostPickItems` `chooseReplacement` chaining & loyalty `+N` replacement.
  let (gPickP1, gPickP2, gPickDone, pickB1, pickB2) :=
    let g := addPermanent (addPermanent (addPermanent afterDraw bear me me) hero me me) headHuntDef opp opp
    let b1 := (g.battlefield.filter (fun o => o.name == "Event Bear" && o.controller == some me))[0]!.id
    let b2 := (g.battlefield.filter (fun o => o.name == "Event Hero" && o.controller == some me))[0]!.id
    let headId := (g.battlefield.filter (·.name == "Phase14 Head Hunt"))[0]!.id
    let idHead : ReplacementId := { kind := .exileOppDeath, object := some headId }
    let g := g.recordPutCounters b1 .finality 1 (some me) (cause := some testCause)
    let g := g.recordPutCounters b2 .finality 1 (some me) (cause := some testCause)
    let gP1 := g.payCostPickItems me (some b1) (some b1) .sacrificeArtifactOrCreature #[b1, b2]
    let gP2 := mustApply gP1 me (.chooseReplacement idHead)
    let gD := mustApply gP2 me (.chooseReplacement idHead)
    (gP1, gP2, gD, b1, b2)
  let gLoyaltyPlus :=
    let g := addPermanent (addPermanent afterDraw samsonDef14 me me) pwPlusDef14 me me
    let pwId := (g.battlefield.filter (fun (o : GameObject) => o.name == "Phase14 Plus PW"))[0]!.id
    let g := g.recordPutCounters pwId .loyalty 2 (some me) (cause := some testCause)
    mustApply g me (.activate pwId 0)
  let chandraLoyaltyAfter :=
    (gLoyaltyPlus.battlefield.filter (fun (o : GameObject) => o.name == "Phase14 Plus PW"))[0]!.status.loyaltyCounters
  let costPickAndLoyaltyOk :=
    (match gPickP1.pending with | .chooseReplacement p cs => p == me && cs.size == 2 | _ => false) &&
    (gPickP1.findObject? pickB1).any (·.isOnBattlefield) &&
    (gPickP1.findObject? pickB2).any (·.isOnBattlefield) &&
    (match gPickP2.pending with | .chooseReplacement p cs => p == me && cs.size == 2 | _ => false) &&
    (gPickP2.findObject? pickB1).all (!·.isOnBattlefield) &&
    (gPickP2.findObject? pickB2).any (·.isOnBattlefield) &&
    (gPickDone.findObject? pickB2).all (!·.isOnBattlefield) &&
    gPickDone.pending == .none &&
    chandraLoyaltyAfter == 5 &&
    [gPickP1, gPickP2, gPickDone, gLoyaltyPlus].all (fun g =>
      Game.replayEvents g.events == g && allRulesEventsClassified g)

  -- 3. Irreversible `lookedAt`, `searched`, and `drawFromEmptyAttempted` across CR 733.1 reversal.
  let (gIrrevKeep, gEmptyDrawSba, libPeekId) :=
    let g0 := insertObject afterDraw rgSpellDef me (.hand me)
    let spId := (g0.player me).hand.back!
    let peekId := (g0.player me).library.back!
    let gProp := mustApply g0 me (.cast spId)
    let g1 := ((gProp.change (.beginProposalAction (.manaAbility none))).record
      (GameEvent.lookedAt gProp.turnNumber me #[peekId] (cause := some testCause))).record
      (GameEvent.searched gProp.turnNumber me me #[peekId] (cause := some testCause))
      |>.change .endProposalAction
    let gRev1 := mustApply g1 me .pay
    let g2 := ((gProp.change (.beginProposalAction (.manaAbility none))).record
      (GameEvent.drawFromEmptyAttempted gProp.turnNumber me (cause := some (.gameRule .abilityActivated))))
      |>.change .endProposalAction
    let gRev2 := (mustApply g2 me .pay).checkSBA
    (gRev1, gRev2, peekId)
  let irrevProposalEventsOk :=
    gIrrevKeep.stack.isEmpty &&
    gIrrevKeep.events.any (fun e =>
      match e.change with
      | .rules (.player (.lookedAt p ids)) => p == me && ids == #[libPeekId]
      | _ => false) &&
    gIrrevKeep.events.any (fun e =>
      match e.change with
      | .rules (.player (.searched p owner found)) => p == me && owner == me && found == #[libPeekId]
      | _ => false) &&
    gEmptyDrawSba.events.any (fun e =>
      match e.change with
      | .rules (.player (.drawFromEmptyAttempted p)) => p == me
      | _ => false) &&
    (gEmptyDrawSba.player me).lost &&
    [gIrrevKeep, gEmptyDrawSba].all (fun g =>
      Game.replayEvents g.events == g && allRulesEventsClassified g)

  -- 4. Face-down morph `turnFaceUp` & mid-resolution `{X}` `castExiledAsAbilityResolves`.
  let morphZeroDef : CardDef := {
    creature "Phase14 Fragile Morph" { symbols := #[.colored .blue] } #["Illusion"] 0 0 with
    morph := some ⟨#[.colored .blue]⟩
  }
  let islandDef : CardDef := {
    name := "Phase14 Island"
    types := #[.land]
    subtypes := #["Island"]
    tapAddOneOf := #[.colored .blue]
  }
  let redLandDef : CardDef := {
    name := "Phase14 Mountain"
    types := #[.land]
    subtypes := #["Mountain"]
    tapAddOneOf := #[.colored .red]
  }
  let (morphGatesOk, gMorphRev, gMorphTurned, morphId0, morphLandId) :=
    let g := addPermanent (addPermanent afterDraw morphZeroDef me me) redLandDef me me
    let g := addPermanent g islandDef me me
    let mId := (g.battlefield.filter (·.name == "Phase14 Fragile Morph"))[0]!.id
    let rLand := (g.battlefield.filter (·.name == "Phase14 Mountain"))[0]!.id
    let uLand := (g.battlefield.filter (·.name == "Phase14 Island"))[0]!.id
    let g := setFaceDown g mId true
    let oppCtrlRej := (g.apply opp (.activate mId 0)).isOk == false
    let gOppPrio := mustApply g me .pass
    let noPrioRej := (gOppPrio.apply me (.activate mId 0)).isOk == false
    let gProp := mustApply g me (.activate mId 0)
    let propKindOk := gProp.proposedSpell.any (·.kind == .turnFaceUp) && gProp.pending == .activateManaAbilities me
    let gTappedWrong := mustApply gProp me (.tapForMana rLand (.colored .red))
    let gRev := mustApply gTappedWrong me .pay
    let gProp2 := mustApply gRev me (.activate mId 0)
    let gPaid := mustApply (mustApply gProp2 me (.tapForMana uLand (.colored .blue))) me .pay
    (oppCtrlRej && noPrioRej && propKindOk, gRev, gPaid, mId, rLand)
  let xBurnDef : CardDef := {
    name := "Phase14 X Burn"
    manaCost := ⟨#[.x, .colored .red]⟩
    types := #[.sorcery]
    spellEffect := some { resolution := .draw 1, phrase := "Draw a card" }
  }
  let gResXDone :=
    let g := insertObject afterDraw xBurnDef opp .exile
    let exId := (g.objects.filter (fun o => o.name == "Phase14 X Burn" && o.zone == .exile))[0]!.id
    let g := g.addMana opp (.colored .red) 3
    let g := ((g.change (.priority opp)).change (.pushContinuationFrame {})).change
      (.pending (.mayCastExiledElseDamage opp exId 2 none))
    let g := mustApply g opp (.cast exId)
    let g := mustApply g opp (.chooseX 2)
    mustApply g opp .pay
  let morphAndResCastOk :=
    morphGatesOk &&
    (gMorphRev.object! morphId0).status.faceDown &&
    !(gMorphRev.object! morphLandId).status.tapped &&
    gMorphRev.priority == me &&
    (gMorphTurned.findObject? morphId0).all (!·.isOnBattlefield) &&
    gMorphTurned.events.any (fun e =>
      match e.change with
      | .rules (.permanent (.turnedFaceUp snap)) => snap.id == some morphId0
      | _ => false) &&
    gResXDone.pending == .none &&
    gResXDone.continuations.isEmpty &&
    gResXDone.stack.size == 1 &&
    gResXDone.priority == me &&
    (gResXDone.player opp).manaPool.total == 0 &&
    [gMorphRev, gMorphTurned, gResXDone].all (fun g =>
      Game.replayEvents g.events == g && allRulesEventsClassified g)

  -- 5. Single-writer `entersWith`, Cursed Mirror EOT `isCopy == false`, `PendingReplacement.move`
  --    `attachedTo` preservation, replaced `ZoneVerb.discard` / `.sacrifice`,
  --    `recordPutCounters` replaced count `n'`, and CR 119.5 `setLife` life gain.
  let (gSingleWriter, swStartIdx, swNewId) :=
    let g := addPermanent afterDraw samsonDef14 me me
    let g := insertObject g pwPlusDef14 me (.hand me)
    let cid := (g.player me).hand.back!
    let preIdx := g.events.size
    let (g1, nid) := g.putOntoBattlefield cid me (cause := some testCause)
    let g1 := g1.afterPermanentEnters (g1.object! nid)
    (g1, preIdx, nid)
  let swSlice := gSingleWriter.events.extract swStartIdx gSingleWriter.events.size
  let swHasLoyalty5 :=
    swSlice.any (fun e =>
      match e.change with
      | .rules (.zone (.moved _ _ _ .battlefield _ _ ew _)) => ew.contains (.loyalty, 5)
      | _ => false)
  let swZeroCounterEvents :=
    !swSlice.any (fun e =>
      match e.change with
      | .rules (.permanent (.counters ..)) => true
      | _ => false)
  let mirrorDef14 : CardDef := {
    name := "Phase14 Cursed Mirror"
    types := #[.artifact]
    asEntersMayCopyCreatureHasteUntilEot := true
  }
  let (gMirrorCopy14, gMirrorClean14, mirrorPermId) :=
    let g0 := addPermanent afterDraw hero opp opp
    let hId := (g0.battlefield.filter (fun (o : GameObject) => o.name == hero.name))[0]!.id
    let g0 := insertObject g0 mirrorDef14 me (.hand me)
    let mHand := (g0.player me).hand.back!
    let (g1, _) := g0.putOntoBattlefield mHand me (cause := some testCause)
    let rid :=
      match g1.pending with
      | .chooseReplacement _ cs =>
        (cs.find? (fun (c : ReplacementId) => c.kind == ReplacementEffectKind.entersAsCopyCreatureUntilEot hId)).get!
      | _ => panic! "expected mirror replacement choice"
    let gCopy := mustApply g1 me (.chooseReplacement rid)
    let mPerm := (gCopy.battlefield.filter (fun (o : GameObject) => o.printed.name == "Phase14 Cursed Mirror"))[0]!.id
    let gClean := gCopy.clearEOT
    (gCopy, gClean, mPerm)
  let auraOddEvenDef : CardDef := {
    name := "Phase14 Parity Aura"
    types := #[.enchantment]
    subtypes := #["Aura"]
    asEntersChooseOddEven := true
  }
  let (gAuraPaused, gAuraAttached, auraHostId, auraPermId) :=
    let g0 := addPermanent afterDraw bear me me
    let hostId := (g0.battlefield.filter (fun (o : GameObject) => o.name == "Event Bear"))[0]!.id
    let g0 := insertObject g0 auraOddEvenDef me (.hand me)
    let aHand := (g0.player me).hand.back!
    let (gP, _) := g0.move aHand .battlefield (some me) (attachedTo := some hostId) (cause := some testCause)
    let gA := mustApply gP me (.chooseMode 1)
    let aPerm := (gA.battlefield.filter (fun (o : GameObject) => o.name == "Phase14 Parity Aura"))[0]!.id
    (gP, gA, hostId, aPerm)
  let discardVerbPreserved :=
    let gD0 := insertObject afterDraw bear me (.hand me)
    let hid := ((gD0.player me).hand.filter (fun id => (gD0.object! id).name == bear.name))[0]!
    let gD0 := gD0.createEffect
      (.replacement { id := { kind := .finalityCounterExile, object := some hid },
                      affectedPlayer := me, kind := .exileInsteadOfGraveyard (some hid) false } .untilEndOfTurn)
    let (gD1, _) := gD0.move hid (.graveyard me) none (verb := some .discard) (cause := some testCause)
    gD1.events.any (fun e =>
      match e.change with
      | .rules (.zone (.moved _ _ (.hand _) .exile ZoneVerb.discard _ _ _)) => true
      | _ => false)
  let (gSacExile, sacExileVerbOk) :=
    let g0 := addPermanent afterDraw bear me me
    let bid := (g0.battlefield.filter (fun (o : GameObject) => o.name == "Event Bear"))[0]!.id
    let g0 := g0.recordPutCounters bid .finality 1 (some me) (cause := some testCause)
    let preIdx := g0.events.size
    let g1 := g0.sacrificeToGraveyard (g0.object! bid) "sacrifice bear" (cause := some testCause)
    let ok :=
      (g1.events.extract preIdx g1.events.size).any (fun e =>
        match e.change with
        | .rules (.zone (.moved _ _ .battlefield .exile ZoneVerb.sacrifice _ _ _)) => true
        | _ => false)
    (g1, ok)
  let (gCountersAndLife, countersAndLifeSubOk) :=
    let g0 := addPermanent (addPermanent afterDraw samsonDef14 me me) bear me me
    let bid := (g0.battlefield.filter (fun (o : GameObject) => o.name == "Event Bear"))[0]!.id
    let g1 := g0.applyPermanentAction (g0.object! bid) .tapAndStun
    let g2 := (g1.empowerJace me 2).empowerJace me 2
    let jaceLoyalty :=
      ((g2.battlefield.filter (fun (o : GameObject) => g2.hasSubtype o .jace))[0]!).status.loyaltyCounters
    let g3 := g2.setLife me 25 "set life to 25" (cause := some testCause)
    let ok :=
      (g3.object! bid).status.stun == 2 &&
      jaceLoyalty == 6 &&
      (g3.player me).life == 25 &&
      g3.loggedLifeGained me == 5
    (g3, ok)
  let singleWriterAndMirrorOk :=
    (gSingleWriter.object! swNewId).status.loyaltyCounters == 5 &&
    swHasLoyalty5 && swZeroCounterEvents &&
    (gMirrorCopy14.snapshot (gMirrorCopy14.object! mirrorPermId)).isCopy &&
    gMirrorCopy14.name (gMirrorCopy14.object! mirrorPermId) == hero.name &&
    !(gMirrorClean14.snapshot (gMirrorClean14.object! mirrorPermId)).isCopy &&
    gMirrorClean14.name (gMirrorClean14.object! mirrorPermId) == "Phase14 Cursed Mirror" &&
    (match gAuraPaused.pending with | Pending.chooseReplacement p _ => p == me | _ => false) &&
    (gAuraAttached.object! auraPermId).attachedTo == some auraHostId &&
    (gAuraAttached.object! auraPermId).status.chosenOdd == some true &&
    discardVerbPreserved && sacExileVerbOk && countersAndLifeSubOk &&
    [gSingleWriter, gMirrorCopy14, gMirrorClean14, gAuraPaused, gAuraAttached, gSacExile, gCountersAndLife].all
      (fun g => Game.replayEvents g.events == g && allRulesEventsClassified g)

  -- 6. Combat `replaceDamage` CR 616.1 chooser, `DamageEvent.prevented`, and planeswalker shield + loyalty.
  let (gCbtPrompt, gCbtResolved, cbtBlkId, idShieldCbt, cbtPrev6Ok) :=
    let g0 := addPermanent (addPermanent afterDraw { bear with power := some 3 } me me) { hero with toughness := some 4 } opp opp
    let atkId := (g0.battlefield.filter (fun (o : GameObject) => o.name == "Event Bear"))[0]!.id
    let blkId := (g0.battlefield.filter (fun (o : GameObject) => o.name == hero.name))[0]!.id
    let g0 := g0.recordPutCounters blkId .shield 1 (some opp) (cause := some testCause)
    let idShield : ReplacementId := { kind := .shieldCounterPreventDamage, object := some blkId }
    let idMul : ReplacementId := { kind := .multiplyDamage, object := some atkId }
    let g1 := ((g0.createEffect
      (.replacement {
        id := idMul, source := some atkId, controller := some me,
        affectedPlayer := me, kind := .multiplyDamage (some atkId) 2
      }) (cause := some testCause)).record
      (GameEvent.attackersDeclared g0.turnNumber me #[(g0.snapshot (g0.object! atkId), .player opp)])).record
      (GameEvent.combatDamageAssigned g0.turnNumber true #[{ source := atkId, toCreatures := #[(blkId, 3)], toPlayer := 0 }])
    let preIdx := g1.events.size
    let gP := g1.dealAssignedCombatDamage
    let gR := mustApply gP opp (.chooseReplacement idMul)
    let prev6 :=
      (gR.events.extract preIdx gR.events.size).any (fun e =>
        match e.change with
        | .rules (.damage (.prevented _ (.permanent snap) 6)) => snap.id == some blkId
        | _ => false)
    (gP, gR, blkId, idShield, prev6)
  let (gPrevEv, prevEvOk) :=
    let protDef : CardDef := { bear with name := "Phase14 Protected Bear", staticAbilities := #[.preventAllDamageToThis] }
    let g0 := addPermanent (addPermanent afterDraw bear me me) protDef opp opp
    let src := (g0.battlefield.filter (fun (o : GameObject) => o.name == "Event Bear" && o.controller == some me))[0]!
    let tgt := (g0.battlefield.filter (fun (o : GameObject) => o.name == "Phase14 Protected Bear"))[0]!
    let preIdx := g0.events.size
    let g1 := g0.dealDamageFrom "Event Bear" tgt 3 (source := some src) (cause := some testCause)
    let ok :=
      (g1.object! tgt.id).status.damage == 0 &&
      (g1.events.extract preIdx g1.events.size).any (fun e =>
        match e.change with
        | .rules (.damage (.prevented _ _ 3)) => true
        | _ => false)
    (g1, ok)
  let (gPwShield, pwShieldOk) :=
    let g0 := addPermanent (addPermanent afterDraw bear me me) pwPlusDef14 opp opp
    let src := (g0.battlefield.filter (fun (o : GameObject) => o.name == "Event Bear" && o.controller == some me))[0]!
    let pwId := (g0.battlefield.filter (fun (o : GameObject) => o.name == "Phase14 Plus PW"))[0]!.id
    let g0 := g0.recordPutCounters pwId .loyalty 4 (some opp) (cause := some testCause)
    let g0 := g0.recordPutCounters pwId .shield 1 (some opp) (cause := some testCause)
    let g1 := g0.markDamageOn (g0.object! pwId) 2 "Event Bear deals 2 damage"
      (source := some (g0.snapshot src)) (sourceObj := some src)
      (unpreventable := true) (cause := some testCause)
    let pwAfter := g1.object! pwId
    (g1, pwAfter.status.shield == 0 && pwAfter.status.loyaltyCounters == 2)
  let combatDmgAndShieldPwOk :=
    (match gCbtPrompt.pending with | Pending.chooseReplacement p cs => p == opp && cs.contains idShieldCbt | _ => false) &&
    (gCbtResolved.object! cbtBlkId).status.shield == 0 &&
    (gCbtResolved.object! cbtBlkId).status.damage == 0 &&
    cbtPrev6Ok && prevEvOk && pwShieldOk &&
    [gCbtPrompt, gCbtResolved, gPrevEv, gPwShield].all (fun g =>
      Game.replayEvents g.events == g && allRulesEventsClassified g)

  -- 7. Simultaneous batch `preBattlefield` look-back, `.attackPumpPerPlains` `DelayedTrigger`
  --    & CR 608.2b fizzle, reflexive trigger CR 608.2b fizzle, and flicker `followMovedToZone?`.
  let diesWatcherDef : CardDef := {
    bear with
    name := "Phase14 Dies Watcher"
    triggeredAbilities := #[
      TriggeredAbility.fra (.fra .anotherCreatureOrPlaneswalkerYouControlDies)
        "Whenever another creature or planeswalker you control dies, you gain 1 life."
        (.gainLife 1)
    ]
  }
  let (gSimDies, simDiesOk) :=
    let g0 := addPermanent (addPermanent afterDraw diesWatcherDef me me) diesWatcherDef me me
    let w1 := (g0.battlefield.filter (fun (o : GameObject) => o.name == "Phase14 Dies Watcher"))[0]!.id
    let w2 := (g0.battlefield.filter (fun (o : GameObject) => o.name == "Phase14 Dies Watcher"))[1]!.id
    let preBf := g0.battlefield
    let g1 := g0.withBatch (some testCause) fun g =>
      let g := g.destroyPermanent (g.object! w1) (cause := some testCause) (preBattlefield := some preBf)
      g.destroyPermanent (g.object! w2) (cause := some testCause) (preBattlefield := some preBf)
    (g1, g1.waitingTriggers.size == 2)
  let (gDtFizzle, gDtLki, dtFizzleOk) :=
    let g0 := addPermanent afterDraw bear me me
    let card0Present := (g0.findObject? ⟨0⟩).isSome
    let bId := (g0.battlefield.filter (fun (o : GameObject) => o.name == "Event Bear"))[0]!.id
    let g1 := g0.attackPumpPerPlains me
    let regOk := g1.delayedTriggers.any (fun (dt : DelayedTrigger) =>
      dt.kind == DelayedTriggerKind.attackPumpPerPlains && dt.source.isNone)
    let g2 := g1.record (GameEvent.attackersDeclared g1.turnNumber me #[(g1.snapshot (g1.object! bId), .player opp)])
    let g2 := g2.receivePriority me
    let sourcelessOk :=
      card0Present &&
      (match g2.stack.back?.bind (fun se => g2.findObject? se.objectId) with
       | some stObj => stObj.sourceId.isNone && stObj.name == "Roads Go Ever, Ever On's ability"
       | none => false) &&
      g2.events.any (fun e =>
        match e.change with
        | .rules (.triggerQueue (.triggered src _ ab _)) =>
          ab == TriggeredAbility.onYouAttackPumpTargetPerPlains &&
          src.id.isNone && src.name == "Roads Go Ever, Ever On"
        | _ => false)
    let g3 := mustApply g2 me (.target (Target.permanent bId))
    let (g4, _) := g3.move bId (.graveyard me) none (cause := some testCause)
    let preRes := g4.events.size
    let g5 := g4.resolveTop
    let fizzled :=
      g5.stack.isEmpty &&
      (g5.events.extract preRes g5.events.size).any (fun e =>
        match e.change with
        | .rules (.stackObject (.removedOnResolution _)) => true
        | _ => false)
    -- Also verify stored Saga LKI (`dt.source == some sagaLki`) preserves `sourceId == some sagaId`.
    let sagaPlaceholderDef : CardDef := {
      name := "Roads Go Ever, Ever On"
      types := #[.enchantment]
      subtypes := #["Saga"]
    }
    let gS0 := addPermanent (addPermanent afterDraw bear me me) sagaPlaceholderDef me me
    let sbId := (gS0.battlefield.filter (fun (o : GameObject) => o.name == "Event Bear"))[0]!.id
    let sagaId := (gS0.battlefield.filter (fun (o : GameObject) => o.name == "Roads Go Ever, Ever On"))[0]!.id
    let (gS1, _) := gS0.move sagaId (.graveyard me) none (cause := some testCause)
    let (gS1, dtCauseS) := gS1.allocDelayedCause (some me) (some sagaId)
    let gS1 := gS1.registerDelayedTrigger {
      controller := me
      source := gS1.damageSourceById? sagaId
      kind := .attackPumpPerPlains
      cause := dtCauseS
    }
    let gS2 := (gS1.record (GameEvent.attackersDeclared gS1.turnNumber me
      #[(gS1.snapshot (gS1.object! sbId), .player opp)])).receivePriority me
    let lkiSourceOk :=
      match gS2.stack.back?.bind (fun se => gS2.findObject? se.objectId) with
      | some stObj => stObj.sourceId == some sagaId && stObj.name == "Roads Go Ever, Ever On's ability"
      | none => false
    (g5, gS2, regOk && sourcelessOk && fizzled && lkiSourceOk)
  let (gReflFizzle, reflFizzleOk) :=
    let g0 := addPermanent (addPermanent afterDraw planDef14 me me) bear opp opp
    let planId := (g0.battlefield.filter (fun (o : GameObject) => o.name == "Phase14 Plan"))[0]!.id
    let bId := (g0.battlefield.filter (fun (o : GameObject) => o.name == "Event Bear" && o.controller == some opp))[0]!.id
    let g1 := mustApply (g0.queueModeledReflexive me (some planId) .divideSevenDamage) me
      (.divideDamage #[(Target.permanent bId, 7)])
    let (g2, _) := g1.move bId .exile none (cause := some testCause)
    let preRes := g2.events.size
    let g3 := g2.resolveTop
    let fizzled :=
      g3.stack.isEmpty &&
      (g3.events.extract preRes g3.events.size).any (fun e =>
        match e.change with
        | .rules (.stackObject (.removedOnResolution _)) => true
        | _ => false)
    (g3, fizzled)
  let (gFlickerIso, flickerIsoOk) :=
    let g0 := addPermanent afterDraw bear me me
    let origId := (g0.battlefield.filter (fun (o : GameObject) => o.name == "Event Bear"))[0]!.id
    let (g1, exId) := g0.move origId .exile none (cause := some testCause)
    let (g2, handId) := g1.move exId (.hand me) none (cause := some testCause)
    let ok :=
      (g1.followMovedToZone? origId (fun (z : Zone) => z == Zone.exile)).map (fun (o : GameObject) => o.id) == some exId &&
      (g2.followMovedToZone? origId (fun (z : Zone) => z == Zone.exile)).isNone &&
      (g2.followMovedToZone? exId (fun (z : Zone) => z == Zone.hand me)).map (fun (o : GameObject) => o.id) == some handId
    (g2, ok)
  let batchLookbackAndFlickerOk :=
    simDiesOk && dtFizzleOk && reflFizzleOk && flickerIsoOk &&
    [gSimDies, gDtFizzle, gDtLki, gReflFizzle, gFlickerIso].all (fun g =>
      Game.replayEvents g.events == g && allRulesEventsClassified g)

  -- 8. CR 800.4a/c/d/i/j multiplayer `concede` cleanup & replay determinism.
  let (gConcedeAfter, concedeSubOk) :=
    let p0 : PlayerId := ⟨0⟩
    let p1 : PlayerId := ⟨1⟩
    let p2 : PlayerId := ⟨2⟩
    let g0 : Game :=
      match Start.start {
        seats := #[
          { name := "Chandra", deck := testRedDeck },
          { name := "Nissa", deck := testGreenDeck },
          { name := "Liliana", deck := testRedDeck }
        ]
        format := .constructed
        seed := 3
        startingPlayer := some 0
      } with
      | .ok g => keepOpeningHands g 16
      | .error e => panic! e
    let g := addPermanent (addPermanent (addPermanent g0 bear p1 p1) hero p0 p0) { bear with name := "Phase14 Bribed Bear" } p2 p1
    let p1OwnId := (g.battlefield.filter (fun (o : GameObject) => o.name == "Event Bear" && o.owner == p1))[0]!.id
    let p0HeroId := (g.battlefield.filter (fun (o : GameObject) => o.name == "Event Hero" && o.owner == p0))[0]!.id
    let p2BribedId := (g.battlefield.filter (fun (o : GameObject) => o.name == "Phase14 Bribed Bear"))[0]!.id
    let g := g.createEffect (.control p0HeroId p1 (untilSourceLeaves := some p1OwnId)) (cause := some testCause)
    let g := g.registerDelayedTrigger { controller := p1, source := none, kind := .attackPumpPerPlains, cause := testCause }
    let gAfter := mustApply g p1 .concede
    let ok :=
      (gAfter.player p1).lost &&
      (gAfter.player p1).leftTheGame &&
      !gAfter.over &&
      (gAfter.findObject? p1OwnId).all (fun (o : GameObject) => !o.isOnBattlefield) &&
      (gAfter.findObject? p0HeroId).any (fun (o : GameObject) => o.isOnBattlefield && gAfter.controllerOf o == some p0) &&
      (gAfter.findObject? (gAfter.followMoved p2BribedId)).any (fun (o : GameObject) => o.zone == Zone.exile) &&
      !gAfter.delayedTriggers.any (fun (dt : DelayedTrigger) => dt.controller == p1)
    (gAfter, ok)
  let concedeCleanupOk :=
    concedeSubOk &&
    Game.replayEvents gConcedeAfter.events == gConcedeAfter &&
    allRulesEventsClassified gConcedeAfter

  -- 9. Multi-kind `proliferateTarget` CR 616.1 pause chaining & deferred `.proliferated` event.
  let prolifWatcherDef : CardDef := {
    bear with
    name := "Phase14 Prolif Watcher"
    triggeredAbilities := #[
      TriggeredAbility.fra (.fra .youProliferate)
        "Whenever you proliferate, you gain 1 life."
        (.gainLife 1)
    ]
  }
  let (gProlifP1, gProlifP2, gProlifDone, prolifSubOk) :=
    let g0 := addPermanent (addPermanent (addPermanent afterDraw bear me me) samsonDef14 me me) prolifWatcherDef me me
    let bId := (g0.battlefield.filter (fun (o : GameObject) => o.name == "Event Bear"))[0]!.id
    let docId := (g0.battlefield.filter (fun (o : GameObject) => o.name == "Phase14 Doc Samson"))[0]!.id
    let g0 := g0.record (GameEvent.counters g0.turnNumber (some me) (g0.snapshot (g0.object! bId)) .plusOnePlusOne 1 (cause := testCause))
    let g0 := g0.record (GameEvent.counters g0.turnNumber (some me) (g0.snapshot (g0.object! bId)) .shield 1 (cause := testCause))
    let idDocPlus : ReplacementId := { kind := .extraCounterOnPermanents, object := some docId, counterKind := some .plusOnePlusOne }
    let idDbl : ReplacementId := { kind := .multiplyCountersPut, object := some docId }
    let dblSpec : ReplacementSpec := {
      id := idDbl
      source := some docId
      controller := some me
      affectedPlayer := me
      kind := .modifyCountersPut (some bId) none 0 2
    }
    let g0 := g0.createEffect (.replacement dblSpec) (cause := some testCause)
    let preEvIdx := g0.events.size
    let hasProlifSince (g : Game) : Bool :=
      (g.events.extract preEvIdx g.events.size).any (fun e =>
        match e.change with
        | .rules (.player (.proliferated ..)) => true
        | _ => false)
    let gP1 := g0.proliferateTarget me #[Target.permanent bId]
    -- Prompt 1 (+1/+1): choose Doc Samson (+1) first, then *2 => (1 + 1) * 2 = 4 added (total 5).
    let gP2 := mustApply gP1 me (.chooseReplacement idDocPlus)
    -- Prompt 2 (.shield): choose *2 first, then Doc Samson (+1) => (1 * 2) + 1 = 3 added (total 4).
    let gDone := mustApply gP2 me (.chooseReplacement idDbl)
    let ok :=
      (match gP1.pending with | Pending.chooseReplacement p cs => p == me && cs.size == 2 | _ => false) &&
      !hasProlifSince gP1 &&
      gP1.waitingTriggers.isEmpty &&
      gP1.stack.isEmpty &&
      (gP1.object! bId).status.plusOnePlusOne == 1 &&
      (gP1.object! bId).status.shield == 1 &&
      (match gP2.pending with | Pending.chooseReplacement p cs => p == me && cs.size == 2 | _ => false) &&
      !hasProlifSince gP2 &&
      gP2.waitingTriggers.isEmpty &&
      gP2.stack.isEmpty &&
      (gP2.object! bId).status.plusOnePlusOne == 5 &&
      (gP2.object! bId).status.shield == 1 &&
      gDone.pending == .none &&
      hasProlifSince gDone &&
      (gDone.object! bId).status.plusOnePlusOne == 5 &&
      (gDone.object! bId).status.shield == 4 &&
      gDone.stack.size == 1
    (gP1, gP2, gDone, ok)
  let proliferateTargetPauseOk :=
    prolifSubOk &&
    [gProlifP1, gProlifP2, gProlifDone].all (fun g =>
      Game.replayEvents g.events == g && allRulesEventsClassified g)

  let mustHold14 (label : String) (ok : Bool) : Bool :=
    if ok then true else panic! s!"Phase 14 guard failed: {label}"

  [ mustHold14 "painLandBracketOk" painLandBracketOk,
    mustHold14 "costPickAndLoyaltyOk" costPickAndLoyaltyOk,
    mustHold14 "irrevProposalEventsOk" irrevProposalEventsOk,
    mustHold14 "morphAndResCastOk" morphAndResCastOk,
    mustHold14 "singleWriterAndMirrorOk" singleWriterAndMirrorOk,
    mustHold14 "combatDmgAndShieldPwOk" combatDmgAndShieldPwOk,
    mustHold14 "batchLookbackAndFlickerOk" batchLookbackAndFlickerOk,
    mustHold14 "concedeCleanupOk" concedeCleanupOk,
    mustHold14 "proliferateTargetPauseOk" proliferateTargetPauseOk ].all id

/- Phase 15 isolation & replay tests:
   1. Pause-safe `.sequence` resolution across interactive `Pending` + multi-object
      CR 616.1 `chooseReplacement` loops, plus `mayThen` replacement pause safety.
   2. CR 117.3c standalone mana-ability SBAs & non-active `pendingPriority`
      retention across SBA/trigger prompts.
   3. CR 601.2b/f/h teamwork tap ordering (untapped until 601.2h, CR 733.1
      reversal if tapped for mana during 601.2g) & paid `.mayCastCards` /
      `.mayCastFromGraveyard` CR 601.2g mana-ability unlock.
   4. CR 603.3b shared-source distinct trigger ordering (index-based
      `Action.stackTriggers`) vs. truly identical trigger auto-stacking.
   5. `openBatchStack` Ward `newlyTargeted` across batch close & nested
      `ProposalCheckpoint` (`outerProposalCheckpoints`) deterministic replay.
   6. Simultaneous-batch `moved.before` LKI + pre-batch `hasIndestructible` &
      multi-pass CR 704.3 / 704.8 SBAs.
   7. CR 510.4 / 122.1c / 702.19b–f / 802.5 / 506.4 combat alignment
      (first-strike/double-strike eligibility, simultaneous shield-counter
      prevention vs. lifelink/deathtouch, `.creatureYouControlDealtDamage`
      batch deduplication, tramplers vs. departed planeswalkers, APNAP
      multi-defender blocker combat damage assignment, CR 506.4 control change).
   8. CR 514.2 cleanup expiry (`"until end of turn"` ability grants & phased-out
      marked damage clearing).
   9. CR 800.4f/j leave-game combat/ward transitions (skip `.declareAttackers`
      when active player left, `.declareBlockers` `remainedUnblocked` when
      defender leaves, `.payOrLetCounter` / `.payWard` when caster leaves).
   10. Layer-7c `chosenCreatureType` scoping & `lastKnownBefore?` single-life LKI.
   11. `ObjectId ⟨0⟩` parity & `EngineChange.stackEntry` deterministic replay. -/
#guard
  let opp : PlayerId := ⟨1⟩
  let headHuntDef : CardDef :=
    { bear with name := "Phase15 Head Hunt", staticAbilities := #[.exileOppDeathCreateWolf] }

  -- 1. Pause-safe `.sequence` (scry -> multi-creature `destroyAllCreatures` with 2 CR 616.1 pauses -> draw 1)
  --    and `mayThen` replacement pause safety.
  let seqWipeSpellDef : CardDef := {
    name := "Phase15 Scry Wipe Draw"
    manaCost := ManaCost.empty
    types := #[.sorcery]
    spellEffect := some {
      resolution := .sequence [.scry (.fixed 1), .destroyAllCreatures, .draw (.fixed 1)]
      phrase := "Scry 1. Destroy all creatures. Draw a card."
    }
  }
  let (gSeqP1, gSeqP2, gSeqP3, gSeqDone, seqPauseOk) :=
    let g0 := addPermanent (addPermanent (addPermanent afterDraw bear me me) hero me me) headHuntDef opp opp
    let b1 := (g0.battlefield.filter (fun o => o.name == bear.name && o.controller == some me))[0]!.id
    let b2 := (g0.battlefield.filter (fun o => o.name == hero.name && o.controller == some me))[0]!.id
    let hOpp := (g0.battlefield.filter (·.name == "Phase15 Head Hunt"))[0]!.id
    let g0 := (g0.recordPutCounters b1 .finality 1 (some me) (cause := some testCause)).recordPutCounters
      b2 .finality 1 (some me) (cause := some testCause)
    let g0 := g0.recordPutCounters hOpp .indestructible 1 (some opp) (cause := some testCause)
    let g0 := insertObject g0 seqWipeSpellDef me (.hand me)
    let spId := (g0.player me).hand.back!
    let gCast := mustApply g0 me (.cast spId)
    let handBeforeResolve := (gCast.player me).hand.size
    let g1 := gCast.resolveTop
    let topLib := (g1.player me).library.back!
    let g2 := mustApply g1 me (.scry #[topLib] #[])
    let pickFin1 : ReplacementId := { kind := .finalityCounterExile, object := some b1 }
    let pickFin2 : ReplacementId := { kind := .finalityCounterExile, object := some b2 }
    let g3 := mustApply g2 me (.chooseReplacement pickFin1)
    let g4 := mustApply g3 me (.chooseReplacement pickFin2)
    let ok :=
      (match g1.pending with | .scry p _ _ => p == me | _ => false) &&
      (g1.player me).hand.size == handBeforeResolve &&
      (match g2.pending with | .chooseReplacement p cs => p == me && cs.contains pickFin1 | _ => false) &&
      (g2.player me).hand.size == handBeforeResolve &&
      (match g3.pending with | .chooseReplacement p cs => p == me && cs.contains pickFin2 | _ => false) &&
      (g3.player me).hand.size == handBeforeResolve &&
      g4.pending == .none &&
      g4.stack.isEmpty &&
      (g4.player me).hand.size == handBeforeResolve + 1 &&
      !(g4.battlefield.any (fun o => o.id == b1 || o.id == b2))
    (g1, g2, g3, g4, ok)
  let (gMayP1, gMayP2, gMayDone, mayThenPauseOk) :=
    let g0 := addPermanent (addPermanent (addPermanent afterDraw bear me me) hero me me) headHuntDef opp opp
    let srcId := (g0.battlefield.filter (fun o => o.name == hero.name && o.controller == some me))[0]!.id
    let vicId := (g0.battlefield.filter (fun o => o.name == bear.name && o.controller == some me))[0]!.id
    let g0 := g0.recordPutCounters vicId .finality 1 (some me) (cause := some testCause)
    let handPre := (g0.player me).hand.size
    let abObjId : ObjectId := ⟨g0.nextObjectId⟩
    let g0 := g0.record (GameEvent.triggerPutOnStack g0.turnNumber abObjId (g0.snapshot (g0.object! srcId)) me
      (spec := { sourceId := some srcId }))
    let g0 := g0.change (.pushContinuationFrame { resolvingAbility := some abObjId })
    let gP1 := g0.applyTriggeredAbility me (.onEnterDraw 1) (some srcId) #[] #[] none none "Hero"
      (some (.may (.pay (.sacrifice (.fixed 1) .another)) (.draw (.fixed 1)) .ifYouDo))
    let gP2 := mustApply gP1 me (.choosePermanents #[vicId])
    let pickFinV : ReplacementId := { kind := .finalityCounterExile, object := some vicId }
    let gDone := mustApply gP2 me (.chooseReplacement pickFinV)
    let ok :=
      (match gP1.pending with | .fraChoice p (.maySacrificeAnotherCreatureForPower _) => p == me | _ => false) &&
      (gP1.player me).hand.size == handPre &&
      (match gP2.pending with | .chooseReplacement p cs => p == me && cs.contains pickFinV | _ => false) &&
      (gP2.player me).hand.size == handPre &&
      gDone.pending == .none &&
      (gDone.player me).hand.size == handPre + 1
    (gP1, gP2, gDone, ok)
  let seqAndMayThenOk :=
    seqPauseOk && mayThenPauseOk &&
    [gSeqP1, gSeqP2, gSeqP3, gSeqDone, gMayP1, gMayP2, gMayDone].all (fun g =>
      Game.replayEvents g.events == g && allRulesEventsClassified g)

  -- 2. CR 117.3c standalone mana-ability SBAs & non-active `pendingPriority` retention across trigger prompts.
  let targetedDiesDef : CardDef := {
    bear with
    name := "Phase15 Targeted Dies"
    triggeredAbilities := #[.onDiesDealDamageEqualToPowerToOppCreature]
  }
  let (gStandaloneMana, gNonActivePrompt, gNonActiveRetained, manaAndPrioOk) :=
    let gBase := mustApply (addPermanent (addPermanent (addPermanent afterDraw forest opp opp) bear opp opp) targetedDiesDef me me) me .pass
    let fIdB := (gBase.battlefield.filter (fun o => o.name == "Forest" && o.controller == some opp))[0]!.id
    let oppTgtB := (gBase.battlefield.filter (fun o => o.name == bear.name && o.controller == some opp))[0]!.id
    let dIdB := (gBase.battlefield.filter (·.name == "Phase15 Targeted Dies"))[0]!.id
    let gDamaged := gBase.markDamageOn (gBase.object! dIdB) 2 "lethal while opp has priority" (cause := some testCause)
    -- Standalone `tapForMana` by `opp` runs `receivePriority opp`: SBA destroys `dIdB`, `me` is prompted to target
    -- the dies trigger, and once `me` chooses target `oppTgtB`, `pendingPriority` returns priority to `opp`!
    let gPrompt := mustApply gDamaged opp (.tapForMana fIdB (.colored .green))
    let gAfterTarget := mustApply gPrompt me (.target (.permanent oppTgtB))
    -- Pure standalone untargeted check: lethal Bear dies immediately on standalone `tapForMana` and `opp` keeps priority.
    let gBase2 := mustApply (addPermanent (addPermanent afterDraw forest opp opp) bear me me) me .pass
    let fId2 := (gBase2.battlefield.filter (fun o => o.name == "Forest" && o.controller == some opp))[0]!.id
    let bId2 := (gBase2.battlefield.filter (·.name == bear.name))[0]!.id
    let gDam2 := gBase2.markDamageOn (gBase2.object! bId2) 2 "lethal" (cause := some testCause)
    let gManaSba := mustApply gDam2 opp (.tapForMana fId2 (.colored .green))
    let ok :=
      !(gManaSba.battlefield.any (·.id == bId2)) &&
      gManaSba.priority == opp &&
      (gManaSba.player opp).manaPool.green == 1 &&
      !(gPrompt.battlefield.any (·.id == dIdB)) &&
      gPrompt.pending == .chooseTargets me &&
      gPrompt.pendingPriority == some opp &&
      gAfterTarget.pending == .none &&
      gAfterTarget.stack.size == 1 &&
      gAfterTarget.priority == opp &&
      gAfterTarget.pendingPriority.isNone
    (gManaSba, gPrompt, gAfterTarget, ok)
  let standaloneManaAndPrioOk :=
    manaAndPrioOk &&
    [gStandaloneMana, gNonActivePrompt, gNonActiveRetained].all (fun g =>
      Game.replayEvents g.events == g && allRulesEventsClassified g)

  -- 3. CR 601.2b/f/h teamwork tap ordering & paid `.mayCastCards` / `.mayCastFromGraveyard` CR 601.2g mana unlock.
  let whiteDorkDef : CardDef := {
    name := "Phase15 White Dork"
    manaCost := ManaCost.empty
    types := #[.creature]
    subtypes := #["Human", "Druid"]
    power := some 2
    toughness := some 2
    tapAddMana := #[ManaType.colored .white]
  }
  let wDrawDef : CardDef := {
    name := "Phase15 Paid Draw"
    manaCost := ⟨#[.colored .white]⟩
    types := #[.instant]
    spellEffect := some { resolution := .draw 1, phrase := "Draw a card" }
  }
  let teamworkStrikeDef : CardDef := {
    lightningBolt with
    name := "Phase15 Teamwork Strike"
    manaCost := ⟨#[.colored .white]⟩
    teamwork := some 2
  }
  let (gTwTarget, gTwReverted, gPaidCardsDone, gPaidGyDone, teamworkAndPaidCastOk) :=
    let g0 := addPermanent afterDraw whiteDorkDef me me
    let dorkId := (g0.battlefield.filter (·.name == "Phase15 White Dork"))[0]!.id
    let g0 := insertObject g0 bear opp .battlefield (some opp) { attacking := true, summoningSick := false }
    let ogreId := (g0.battlefield.filter (fun o => o.name == bear.name && o.controller == some opp))[0]!.id
    let g0 := insertObject g0 teamworkStrikeDef me (.hand me)
    let hsId := (g0.player me).hand.back!
    let gPreCast := g0
    let g1 := mustApply g0 me (.cast hsId)
    let g2 := mustApply g1 me (.announceTeamwork true)
    let g3 := mustApply g2 me (.choosePermanents #[dorkId])
    let g4 := mustApply g3 me (.target (.permanent ogreId))
    -- At CR 601.2b (`g3`) and CR 601.2c (`g4`), `dorkId` is STILL untapped on the battlefield,
    -- yet `tapForMana` rejects tapping `dorkId` because it is already chosen for teamwork!
    -- With 0 `{W}`, `.pay` reverses the proposal via CR 733.1 (`hsId` back in hand, `dorkId` untapped);
    -- with `{W}` in pool, `.pay` taps `dorkId` at CR 601.2h!
    let tapDorkRejected :=
      match g4.applyAction me (.tapForMana dorkId (.colored .white)) with
      | .error _ => true
      | .ok _ => false
    let gRev := mustApply g4 me .pay
    let gTwPaid := mustApply (g4.addMana me (.colored .white) 1) me .pay
    -- Paid `.mayCastCards` (`withoutPaying := false`) unlocks `tapForMana` during CR 601.2g:
    let gMc0 := addPermanent (insertObject afterDraw wDrawDef me .exile) plains me me
    let pId1 := (gMc0.battlefield.filter (·.name == "Plains"))[0]!.id
    let exCardId := (gMc0.objects.filter (fun o => o.name == "Phase15 Paid Draw" && o.zone == .exile))[0]!.id
    let gMc1 := (gMc0.change (.pushContinuationFrame {})).change
      (.pending (.fraChoice me (.mayCastCards #[exCardId] false false)))
    let gMc2 := mustApply gMc1 me (.cast exCardId)
    let gMc3 := mustApply gMc2 me (.tapForMana pId1 (.colored .white))
    let gMc4 := mustApply gMc3 me .pay
    -- Paid `.mayCastFromGraveyard` unlocks `tapForMana` during CR 601.2g:
    let gGy0 := addPermanent (insertObject afterDraw wDrawDef me (.graveyard me)) plains me me
    let pId2 := (gGy0.battlefield.filter (·.name == "Plains"))[0]!.id
    let gyCardId := ((gGy0.player me).graveyard.filter (fun id => (gGy0.object! id).name == "Phase15 Paid Draw"))[0]!
    let gGy1 := (gGy0.change (.pushContinuationFrame {})).change
      (.pending (.fraChoice me (.mayCastFromGraveyard #[gyCardId])))
    let gGy2 := mustApply gGy1 me (.cast gyCardId)
    let gGy3 := mustApply gGy2 me (.tapForMana pId2 (.colored .white))
    let gGy4 := mustApply gGy3 me .pay
    let ok :=
      !(g3.object! dorkId).status.tapped &&
      !(g4.object! dorkId).status.tapped &&
      tapDorkRejected &&
      !(gRev.object! dorkId).status.tapped &&
      (gRev.player me).manaPool.white == (gPreCast.player me).manaPool.white &&
      (gRev.player me).hand.contains hsId &&
      (gTwPaid.object! dorkId).status.tapped &&
      gTwPaid.stack.size == 1 &&
      gMc4.pending == .none &&
      gMc4.stack.size == 1 &&
      (gMc4.object! pId1).status.tapped &&
      gGy4.pending == .none &&
      gGy4.stack.size == 1 &&
      (gGy4.object! pId2).status.tapped
    (gTwPaid, gRev, gMc4, gGy4, ok)
  let twAndPaidAllOk :=
    teamworkAndPaidCastOk &&
    [gTwTarget, gTwReverted, gPaidCardsDone, gPaidGyDone].all (fun g =>
      Game.replayEvents g.events == g && allRulesEventsClassified g)

  -- 4. CR 603.3b shared-source distinct trigger ordering vs. truly identical auto-stacking.
  let dualEtbDef : CardDef := {
    bear with
    name := "Phase15 Dual ETB"
    triggeredAbilities := #[.onEnterDraw 1, .onEnterGainLife 3]
  }
  let identEtbDef : CardDef := {
    bear with
    name := "Phase15 Identical ETB"
    triggeredAbilities := #[.onEnterDraw 1, .onEnterDraw 1]
  }
  let (gDualPrompt, gDualOrdered, gDualFirstRes, gIdentAuto, cr6033bOk) :=
    let g0 := insertObject afterDraw dualEtbDef me (.hand me)
    let cId := (g0.player me).hand.back!
    let gCast := mustApply g0 me (.cast cId)
    let gRes := mustApply (mustApply gCast me .pass) opp .pass
    -- `[0]` is `.onEnterDraw 1`, `[1]` is `.onEnterGainLife 3`.
    -- `stackTriggers #[1, 0]` puts `[1]` on bottom and `[0]` on top, so resolving top draws first before life gain!
    let lifePre := (gRes.player me).life
    let handPre := (gRes.player me).hand.size
    let gOrd := mustApply gRes me (.stackTriggers #[1, 0])
    let gTop := mustApply (mustApply gOrd me .pass) opp .pass
    -- Identical triggers on the same source auto-stack without prompting `chooseTriggerToStack`:
    let gI0 := insertObject afterDraw identEtbDef me (.hand me)
    let icId := (gI0.player me).hand.back!
    let gICast := mustApply gI0 me (.cast icId)
    let gIRes := mustApply (mustApply gICast me .pass) opp .pass
    let ok :=
      gRes.pending == .chooseTriggerToStack me &&
      gRes.waitingTriggers.size == 2 &&
      gOrd.pending == .none &&
      gOrd.stack.size == 2 &&
      (gTop.player me).hand.size == handPre + 1 &&
      (gTop.player me).life == lifePre &&
      gIRes.pending == .none &&
      gIRes.waitingTriggers.isEmpty &&
      gIRes.stack.size == 2
    (gRes, gOrd, gTop, gIRes, ok)
  let triggerOrderingAllOk :=
    cr6033bOk &&
    [gDualPrompt, gDualOrdered, gDualFirstRes, gIdentAuto].all (fun g =>
      Game.replayEvents g.events == g && allRulesEventsClassified g)

  -- 5. `openBatchStack` Ward `newlyTargeted` across batch close & nested `ProposalCheckpoint` replay.
  let wardBearDef : CardDef := {
    bear with
    name := "Phase15 Ward Bear"
    ward := some 2
  }
  let pingAnyDef : CardDef := {
    lightningBolt with
    name := "Phase15 Ping"
    manaCost := ManaCost.empty
  }
  let painManaLandDef : CardDef := {
    name := "Phase15 Pain Land"
    types := #[.land]
    tapAddOneOfDealsDamage := some (#[ManaType.colored .white], 1)
  }
  let (gWardRetarget, gNestedInnerRev, gNestedOuterRev, batchStackAndNestedCpOk) :=
    -- Retarget a stack spell onto a Ward permanent inside an enclosing `withBatch`:
    -- `openBatchStack` preserves the pre-batch stack so `newlyTargeted` queues Ward when the batch closes!
    let g0 := addPermanent (addPermanent afterDraw bear opp opp) wardBearDef opp opp
    let plainOpp := (g0.battlefield.filter (·.name == bear.name))[0]!.id
    let wardOpp := (g0.battlefield.filter (·.name == "Phase15 Ward Bear"))[0]!.id
    let g0 := insertObject g0 pingAnyDef me (.hand me)
    let pingH := (g0.player me).hand.back!
    let gCast := mustApply (mustApply g0 me (.cast pingH)) me (.target (.permanent plainOpp))
    let spStackId := gCast.stack.back!.objectId
    let gRet := gCast.withBatch (some testCause) (fun g =>
      g.setStackEntryTargets spStackId #[.permanent wardOpp] #[])
    let gRetPrio := gRet.receivePriority me
    let gRetWardPrompt := mustApply (mustApply gRetPrio me .pass) opp .pass
    -- Nested `ProposalCheckpoint`: outer `saveProposalCheckpoint` (#1) + inner `castAsPartOfResolution`
    -- `saveProposalCheckpoint` (#2 -> `outerProposalCheckpoints.size == 1`); reversing inner `{W}` cast via `.pay`
    -- restores `exId` to `.exile` while popping checkpoint #1 back into `proposalCheckpoint`!
    let _ := painManaLandDef
    let gN0 := insertObject afterDraw wDrawDef me .exile
    let exId := (gN0.objects.filter (fun o => o.name == "Phase15 Paid Draw" && o.zone == .exile))[0]!.id
    let gN1 := (gN0.change .saveProposalCheckpoint).change (.pushContinuationFrame {})
    let gNPaused := gN1.castAsPartOfResolution me exId (withoutManaCost := false)
    let gNInnerRev := mustApply gNPaused me .pay
    let gNOuterCleared := (gNInnerRev.change .clearProposalCheckpoint).change .popContinuationFrame
    let ok :=
      gRetPrio.stack.size == 2 &&
      (match gRetWardPrompt.pending with | .payWard p _ (.genericMana 2) => p == me | _ => false) &&
      gNPaused.pending == .activateManaAbilities me &&
      gNPaused.outerProposalCheckpoints.size == 1 &&
      gNInnerRev.outerProposalCheckpoints.isEmpty &&
      gNInnerRev.proposalCheckpoint.isSome &&
      (gNInnerRev.objects.any (fun o => o.id == exId && o.zone == .exile)) &&
      gNOuterCleared.proposalCheckpoint.isNone
    (gRetWardPrompt, gNPaused, gNOuterCleared, ok)
  let wardAndNestedAllOk :=
    batchStackAndNestedCpOk &&
    [gWardRetarget, gNestedInnerRev, gNestedOuterRev].all (fun g =>
      Game.replayEvents g.events == g && allRulesEventsClassified g)

  -- 6. Simultaneous-batch `moved.before` LKI + pre-batch `hasIndestructible` & multi-pass CR 704.3 / 704.8 SBAs.
  let bearLordDef : CardDef := {
    bear with
    name := "Phase15 Bear Lord"
    staticAbilities := #[.otherCreaturesGet #[.bear] 1 1]
  }
  let planGrantorDef : CardDef := {
    name := "Phase15 Artifact Creature"
    manaCost := ManaCost.empty
    types := #[.artifact, .creature]
    subtypes := #["Construct"]
    power := some 2
    toughness := some 2
  }
  let condIndestDef : CardDef := {
    bear with
    name := "Phase15 Conditional Indestructible"
    staticAbilities := #[.indestructibleIfArtifactCreatureOrPlan]
  }
  let (gSimBatch, gMultiSba, batchLkiAndMultiSbaOk) :=
    -- Simultaneous `destroyAllCreatures`:
    -- (a) `Bear Lord` (2/2) + `Event Bear` (2/2, boosted to 3/3 by Lord) both die; `Event Bear`'s `moved.before`
    --     snapshot and `lastKnownPowerOf?` see pre-batch power 3 even though `Bear Lord` was destroyed first!
    -- (b) `Phase15 Artifact Creature` + `Phase15 Conditional Indestructible` face `destroyAllCreatures`;
    --     pre-batch `hasIndestructible` keeps `Phase15 Conditional Indestructible` alive even though the artifact
    --     creature is destroyed earlier in the same loop!
    let g0 := addPermanent (addPermanent (addPermanent (addPermanent afterDraw bearLordDef me me) bear me me)
      planGrantorDef me me) condIndestDef me me
    let lordId := (g0.battlefield.filter (·.name == "Phase15 Bear Lord"))[0]!.id
    let subBearId := (g0.battlefield.filter (·.name == bear.name))[0]!.id
    let artCrId := (g0.battlefield.filter (·.name == "Phase15 Artifact Creature"))[0]!.id
    let indCrId := (g0.battlefield.filter (·.name == "Phase15 Conditional Indestructible"))[0]!.id
    let gWiped := g0.applyUnified me { resolution := .destroyAllCreatures, phrase := "Destroy all creatures" } #[]
    let lkiPowerOk := gWiped.lastKnownPowerOf? subBearId == some 3
    let indSurvived :=
      !(gWiped.battlefield.any (fun o => o.id == lordId || o.id == subBearId || o.id == artCrId)) &&
      gWiped.battlefield.any (·.id == indCrId)
    -- Multi-pass CR 704.3 SBA:
    -- Pass 1 destroys `Bear Lord` (2/2 with 2 damage) while a 1/1 Bear (`tinyBear`) has 1 damage (currently 2/2).
    -- Pass 2 sees `tinyBear` is now 1/1 with 1 marked damage and destroys it in the same `checkSBA` call!
    let tinyBearDef : CardDef := { bear with name := "Phase15 Tiny Bear", power := some 1, toughness := some 1 }
    let gS0 := addPermanent (addPermanent afterDraw bearLordDef me me) tinyBearDef me me
    let sLordId := (gS0.battlefield.filter (·.name == "Phase15 Bear Lord"))[0]!.id
    let sTinyId := (gS0.battlefield.filter (·.name == "Phase15 Tiny Bear"))[0]!.id
    let gS1 := (gS0.markDamageOn (gS0.object! sLordId) 2 "lethal lord" (cause := some testCause)).markDamageOn
      (gS0.object! sTinyId) 1 "1 dmg tiny" (cause := some testCause)
    let gS2 := gS1.checkSBA
    let multiSbaOk :=
      !(gS2.battlefield.any (fun o => o.id == sLordId || o.id == sTinyId))
    (gWiped, gS2, lkiPowerOk && indSurvived && multiSbaOk)
  let lkiAndMultiSbaAllOk :=
    batchLkiAndMultiSbaOk &&
    [gSimBatch, gMultiSba].all (fun g =>
      Game.replayEvents g.events == g && allRulesEventsClassified g)

  -- 7. CR 510.4 / 122.1c / 702.19b–f / 802.5 / 506.4 combat alignment.
  let fsBearDef : CardDef := { bear with name := "Phase15 FS Bear", keywords := Keyword.firstStrike }
  let dtLifeDef : CardDef := {
    bear with
    name := "Phase15 DT Lifelinker"
    keywords := { deathtouch := true, lifelink := true }
  }
  let trampler4Def : CardDef := {
    bear with
    name := "Phase15 Trampler"
    power := some 4
    toughness := some 4
    keywords := Keyword.trample
  }
  let pwVictimDef : CardDef := {
    name := "Phase15 Target PW"
    supertypes := #[.legendary]
    types := #[.planeswalker]
    subtypes := #["Jace"]
    loyalty := some 3
  }
  let dmgOnceWatcherDef : CardDef := {
    name := "Phase15 Batch Damage Watcher"
    manaCost := ManaCost.empty
    types := #[.enchantment]
    triggeredAbilities := #[.triggered .fromEffect Effect.watchSheHulkRedirectOnce {}]
  }
  -- 7a. CR 510.4: first-strike attacker deals 2 in FS step; granting `Event Bear` first strike AFTER FS step does NOT
  --     exclude `Event Bear` from regular combat damage, while granting `FS Bear` double strike AFTER FS step lets `FS Bear`
  --     deal regular combat damage too!
  let (gCbt5104, cbt5104Ok) :=
    let g0 := addPermanent (addPermanent afterDraw fsBearDef me me) bear me me
    let fsId := (g0.battlefield.filter (·.name == "Phase15 FS Bear"))[0]!.id
    let brId := (g0.battlefield.filter (·.name == bear.name))[0]!.id
    let g1 := g0.beginStep .beginningOfCombat
    let g1 := mustApply (mustApply g1 me .pass) opp .pass
    let g1 := mustApply g1 me (.declareAttackers #[fsId, brId] none #[] #[])
    let g1 := mustApply (mustApply g1 me .pass) opp .pass
    let g1 := mustApply g1 opp (.declareBlockers #[])
    let gFs := mustApply (mustApply g1 me .pass) opp .pass
    -- After FS step (`opp` at 18): grant `fsId` double strike and `brId` first strike, then advance to regular combat damage:
    -- `fsId` (now double strike) deals 2 AND `brId` (didn't have FS at FS step) deals 2 => `opp` at 14!
    let gGrant := (gFs.createEffect (.keywordsUntilEot fsId Keyword.doubleStrike) (cause := some testCause)).createEffect
      (.keywordsUntilEot brId Keyword.firstStrike) (cause := some testCause)
    let gReg := mustApply (mustApply gGrant me .pass) opp .pass
    (gReg, (gFs.player opp).life == 18 && (gReg.player opp).life == 14)
  -- 7b. CR 122.1c simultaneous shield counter in combat vs. TWO deathtouch+lifelink blockers +
  --     `.creatureYouControlDealtDamage` single trigger on simultaneous combat damage to two creatures.
  let (gShieldSim, gBatchDmgTrig, shieldAndBatchTrigOk) :=
    let g0 := addPermanent (addPermanent (addPermanent afterDraw bear me me) dtLifeDef opp opp)
      { dtLifeDef with name := "Phase15 DT Lifelinker 2" } opp opp
    let atkId := (g0.battlefield.filter (·.name == bear.name))[0]!.id
    let blk1 := (g0.battlefield.filter (·.name == "Phase15 DT Lifelinker"))[0]!.id
    let blk2 := (g0.battlefield.filter (·.name == "Phase15 DT Lifelinker 2"))[0]!.id
    let g0 := g0.recordPutCounters atkId .shield 1 (some me) (cause := some testCause)
    let oppLifePre := (g0.player opp).life
    let g1 := g0.beginStep .beginningOfCombat
    let g1 := mustApply (mustApply g1 me .pass) opp .pass
    let g1 := mustApply g1 me (.declareAttackers #[atkId] none #[] #[])
    let g1 := mustApply (mustApply g1 me .pass) opp .pass
    let g1 := mustApply g1 opp (.declareBlockers #[(blk1, atkId), (blk2, atkId)])
    let g1 := mustApply (mustApply g1 me .pass) opp .pass
    let gDmg := mustApply g1 me (.assignCombatDamage #[{ source := atkId, toCreatures := #[(blk1, 2)], toPlayer := 0 }])
    let shieldOk :=
      gDmg.battlefield.any (·.id == atkId) &&
      (gDmg.object! atkId).status.shield == 0 &&
      (gDmg.object! atkId).status.damage == 0 &&
      (gDmg.player opp).life == oppLifePre
    -- Simultaneous combat damage to TWO creatures controlled by `opp` under `dmgOnceWatcherDef`:
    let gW0 := addPermanent (addPermanent (addPermanent (addPermanent (addPermanent afterDraw bear me me) hero me me)
      { bear with name := "Opp Wall 1", toughness := some 4 } opp opp)
      { bear with name := "Opp Wall 2", toughness := some 4 } opp opp) dmgOnceWatcherDef opp opp
    let a1 := (gW0.battlefield.filter (fun o => o.name == bear.name && o.controller == some me))[0]!.id
    let a2 := (gW0.battlefield.filter (fun o => o.name == hero.name && o.controller == some me))[0]!.id
    let w1 := (gW0.battlefield.filter (·.name == "Opp Wall 1"))[0]!.id
    let w2 := (gW0.battlefield.filter (·.name == "Opp Wall 2"))[0]!.id
    let gW1 := gW0.beginStep .beginningOfCombat
    let gW1 := mustApply (mustApply gW1 me .pass) opp .pass
    let gW1 := mustApply gW1 me (.declareAttackers #[a1, a2] none #[] #[])
    let gW1 := mustApply (mustApply gW1 me .pass) opp .pass
    let gW1 := mustApply gW1 opp (.declareBlockers #[(w1, a1), (w2, a2)])
    let gWDmg := mustApply (mustApply gW1 me .pass) opp .pass
    -- Two creatures dealt damage triggers `watchSheHulkRedirectOnce` twice; under CR 603.3b–d,
    -- the first copy is placed on `g.stack` and prompts `opp` for targets while the second stays
    -- in `waitingTriggers` (`ordered := true`) until `opp` announces the first copy's target.
    let gWDmg2 := mustApply gWDmg opp (.target (Target.player me))
    -- Single creature dealt simultaneous combat damage by two blockers triggers ONCE with summed `batchTotal == 4` (MSH 512):
    let gS0 := addPermanent (addPermanent (addPermanent (addPermanent afterDraw
      { bear with name := "Phase15 Big Attacker", toughness := some 5 } me me)
      dmgOnceWatcherDef me me) bear opp opp) hero opp opp
    let sAtk := (gS0.battlefield.filter (·.name == "Phase15 Big Attacker"))[0]!.id
    let sb1 := (gS0.battlefield.filter (fun o => o.name == bear.name && o.controller == some opp))[0]!.id
    let sb2 := (gS0.battlefield.filter (fun o => o.name == hero.name && o.controller == some opp))[0]!.id
    let gS1 := gS0.beginStep .beginningOfCombat
    let gS1 := mustApply (mustApply gS1 me .pass) opp .pass
    let gS1 := mustApply gS1 me (.declareAttackers #[sAtk] none #[] #[])
    let gS1 := mustApply (mustApply gS1 me .pass) opp .pass
    let gS1 := mustApply gS1 opp (.declareBlockers #[(sb1, sAtk), (sb2, sAtk)])
    let gS1 := mustApply (mustApply gS1 me .pass) opp .pass
    let gSDmg := mustApply gS1 me (.assignCombatDamage #[{ source := sAtk, toCreatures := #[(sb1, 2)], toPlayer := 0 }])
    let batchTrigOk :=
      gWDmg.pending == .chooseTargets opp &&
      gWDmg.stack.size == 1 &&
      gWDmg.waitingTriggers.size == 1 &&
      gWDmg.waitingTriggers[0]!.ordered &&
      gWDmg2.pending == .chooseTargets opp &&
      gWDmg2.stack.size == 2 &&
      gWDmg2.waitingTriggers.isEmpty &&
      gSDmg.pending == .chooseTargets me &&
      gSDmg.stack.size == 1 &&
      gSDmg.waitingTriggers.isEmpty &&
      gSDmg.stack[0]!.lastKnownPower == some 4 &&
      Game.replayEvents gWDmg2.events == gWDmg2 && allRulesEventsClassified gWDmg2 &&
      Game.replayEvents gSDmg.events == gSDmg && allRulesEventsClassified gSDmg
    (gDmg, gWDmg, shieldOk && batchTrigOk)
  -- 7c. CR 702.19b / 702.19f: unblocked & blocked tramplers attacking a planeswalker that left combat deal 0 to defending player;
  --     plus CR 506.4 control change removes creature from combat, and CR 802.5 APNAP multi-defender blocker assignment.
  let (gTrUnblk, gTrBlk, gCtrlRem, gMultiBlkDone, trampleCtrlAndApnapBlkOk) :=
    let mkPwCombat (blocked : Bool) : Game :=
      let g0 := addPermanent (addPermanent afterDraw trampler4Def me me) pwVictimDef opp opp
      let g0 := if blocked then addPermanent g0 bear opp opp else g0
      let trId := (g0.battlefield.filter (·.name == "Phase15 Trampler"))[0]!.id
      let pwId := (g0.battlefield.filter (·.name == "Phase15 Target PW"))[0]!.id
      let g0 := g0.recordPutCounters pwId .loyalty 3 (some opp) (cause := some testCause)
      let g1 := g0.beginStep .beginningOfCombat
      let g1 := mustApply (mustApply g1 me .pass) opp .pass
      let g1 := mustApply g1 me (.declareAttackers #[trId] none #[] #[some pwId])
      let g1 := mustApply (mustApply g1 me .pass) opp .pass
      let g1 :=
        if blocked then
          let blkId := (g1.battlefield.filter (fun o => o.name == bear.name && o.controller == some opp))[0]!.id
          let gB := mustApply g1 opp (.declareBlockers #[(blkId, trId)])
          let (gB, _) := gB.move blkId .exile none (cause := some testCause)
          gB
        else
          mustApply g1 opp (.declareBlockers #[])
      let (g2, _) := g1.move pwId .exile none (cause := some testCause)
      mustApply (mustApply g2 me .pass) opp .pass
    let gU := mkPwCombat false
    let gB := mkPwCombat true
    -- CR 506.4: gaining control of an attacking creature removes it from combat.
    let gC0 := addPermanent afterDraw bear me me
    let cAtk := (gC0.battlefield.filter (·.name == bear.name))[0]!.id
    let gC1 := gC0.beginStep .beginningOfCombat
    let gC1 := mustApply (mustApply gC1 me .pass) opp .pass
    let gC1 := mustApply gC1 me (.declareAttackers #[cAtk] none #[] #[])
    let gC2 := gC1.createEffect (.layered (.objects #[cAtk]) (.control opp) .untilEndOfTurn) (cause := some testCause)
    -- CR 802.5: 3-player game where defenders `⟨1⟩` and `⟨2⟩` each control a 3/3 blocker blocking 2 attackers;
    -- combat damage prompts `⟨1⟩` then `⟨2⟩` in APNAP order!
    let threeCfg15 : StartConfig := {
      seats := #[
        { name := "Chandra", deck := testRedDeck },
        { name := "Nissa", deck := testGreenDeck },
        { name := "Liliana", deck := testRedDeck }
      ]
      format := .constructed
      seed := 15
      startingPlayer := some 0
    }
    let g3Base :=
      match Start.start threeCfg15 with
      | .ok g => keepOpeningHands g 12
      | .error e => panic! e
    let bigBlkDef : CardDef := { bear with name := "Phase15 Multi Blocker", power := some 3, toughness := some 5 }
    let gM0 :=
      addPermanent (addPermanent (addPermanent (addPermanent (addPermanent (addPermanent g3Base
        bear ⟨0⟩ ⟨0⟩) { bear with name := "Atk1B" } ⟨0⟩ ⟨0⟩)
        { bear with name := "Atk2A" } ⟨0⟩ ⟨0⟩) { bear with name := "Atk2B" } ⟨0⟩ ⟨0⟩)
        bigBlkDef ⟨1⟩ ⟨1⟩) { bigBlkDef with name := "Phase15 Multi Blocker 2" } ⟨2⟩ ⟨2⟩
    let a1a := (gM0.battlefield.filter (fun o => o.name == bear.name && o.controller == some ⟨0⟩))[0]!.id
    let a1b := (gM0.battlefield.filter (·.name == "Atk1B"))[0]!.id
    let a2a := (gM0.battlefield.filter (·.name == "Atk2A"))[0]!.id
    let a2b := (gM0.battlefield.filter (·.name == "Atk2B"))[0]!.id
    let mb1 := (gM0.battlefield.filter (·.name == "Phase15 Multi Blocker"))[0]!.id
    let mb2 := (gM0.battlefield.filter (·.name == "Phase15 Multi Blocker 2"))[0]!.id
    let gM1 :=
      (((gM0.record (GameEvent.attackersDeclared gM0.turnNumber ⟨0⟩
        #[(gM0.snapshot (gM0.object! a1a), .player ⟨1⟩),
          (gM0.snapshot (gM0.object! a1b), .player ⟨1⟩),
          (gM0.snapshot (gM0.object! a2a), .player ⟨2⟩),
          (gM0.snapshot (gM0.object! a2b), .player ⟨2⟩)]
        (cause := some (.turnBased .declareAttackers)))).record
        (GameEvent.blockersDeclared gM0.turnNumber ⟨1⟩
          #[(gM0.snapshot (gM0.object! mb1), a1a), (gM0.snapshot (gM0.object! mb1), a1b)]
          (cause := some (.turnBased .declareBlockers)))).record
        (GameEvent.becameBlocked gM0.turnNumber (gM0.snapshot (gM0.object! a1a)) #[mb1]
          (cause := some (.turnBased .declareBlockers)))).record
        (GameEvent.becameBlocked gM0.turnNumber (gM0.snapshot (gM0.object! a1b)) #[mb1]
          (cause := some (.turnBased .declareBlockers)))
    let gM1 :=
      ((gM1.record
        (GameEvent.blockersDeclared gM1.turnNumber ⟨2⟩
          #[(gM1.snapshot (gM1.object! mb2), a2a), (gM1.snapshot (gM1.object! mb2), a2b)]
          (cause := some (.turnBased .declareBlockers)))).record
        (GameEvent.becameBlocked gM1.turnNumber (gM1.snapshot (gM1.object! a2a)) #[mb2]
          (cause := some (.turnBased .declareBlockers)))).record
        (GameEvent.becameBlocked gM1.turnNumber (gM1.snapshot (gM1.object! a2b)) #[mb2]
          (cause := some (.turnBased .declareBlockers)))
    let gMStart := gM1.combatDamage
    let gMAfter1 := mustApply gMStart ⟨1⟩ (.assignCombatDamage #[{ source := mb1, toCreatures := #[(a1a, 2), (a1b, 1)], toPlayer := 0 }])
    let gMAfter2 := mustApply gMAfter1 ⟨2⟩ (.assignCombatDamage #[{ source := mb2, toCreatures := #[(a2a, 1), (a2b, 2)], toPlayer := 0 }])
    let ok :=
      (gU.player opp).life == 20 &&
      (gB.player opp).life == 20 &&
      !(gC2.object! cAtk).status.attacking &&
      gC2.events.any (fun e => match e.change with | .rules (.combat (.removedFromCombat eo)) => eo.id == some cAtk | _ => false) &&
      gMStart.pending == .assignCombatDamage ⟨1⟩ false &&
      gMAfter1.pending == .assignCombatDamage ⟨2⟩ false &&
      gMAfter2.pending == .none &&
      !(gMAfter2.battlefield.any (·.id == a1a)) &&
      gMAfter2.battlefield.any (·.id == a1b) &&
      gMAfter2.battlefield.any (·.id == a2a) &&
      !(gMAfter2.battlefield.any (·.id == a2b))
    (gU, gB, gC2, gMAfter2, ok)
  let combatAlignmentAllOk :=
    cbt5104Ok && shieldAndBatchTrigOk && trampleCtrlAndApnapBlkOk &&
    [gCbt5104, gShieldSim, gBatchDmgTrig, gTrUnblk, gTrBlk, gCtrlRem, gMultiBlkDone].all (fun g =>
      Game.replayEvents g.events == g && allRulesEventsClassified g)

  -- 8. CR 514.2 cleanup expiry (`"until end of turn"` ability grants & phased-out marked damage clearing).
  let (gCleanEot, cleanupPhasedAndAbOk) :=
    let g0 := addPermanent (addPermanent afterDraw bear me me) hero me me
    let phId := (g0.battlefield.filter (·.name == bear.name))[0]!.id
    let abId := (g0.battlefield.filter (·.name == hero.name))[0]!.id
    let g1 := g0.markDamageOn (g0.object! phId) 1 "1 dmg before phase out" (cause := some testCause)
    let g1 := g1.record (GameEvent.phasedOut g1.turnNumber (g1.snapshot (g1.object! phId)) false (cause := testCause))
    let g1 := (g1.createEffect
      (.layered (.objects #[abId]) (.abilities { triggeredAbilities := #[.onEnterDraw 1] } .none) .untilEndOfTurn)
      (cause := some testCause)).createEffect
      (.layered (.objects #[abId]) (.abilities { keywords := Keyword.flying } .all) .untilEndOfTurn)
      (cause := some testCause)
    let hadFlyPre := g1.hasFlying (g1.object! abId)
    let g2 := g1.clearEOT
    let ok :=
      hadFlyPre &&
      (g2.object! phId).status.phasedOut &&
      (g2.object! phId).status.damage == 0 &&
      !g2.hasFlying (g2.object! abId) &&
      (g2.triggeredAbilities (g2.object! abId)).isEmpty
    (g2, ok)
  let cleanupAllOk :=
    cleanupPhasedAndAbOk &&
    Game.replayEvents gCleanEot.events == gCleanEot &&
    allRulesEventsClassified gCleanEot

  -- 9. CR 800.4f/j leave-game combat/ward transitions (3-player).
  let (gSkipDeclAtk, gBlkLeftUnblocked, gWardCasterLeft, leaveGameTransitionsOk) :=
    let threeCfg9 : StartConfig := {
      seats := #[
        { name := "Chandra", deck := testRedDeck },
        { name := "Nissa", deck := testGreenDeck },
        { name := "Liliana", deck := testRedDeck }
      ]
      format := .constructed
      seed := 9
      startingPlayer := some 0
    }
    let g3 :=
      match Start.start threeCfg9 with
      | .ok g => keepOpeningHands g 12
      | .error e => panic! e
    -- 9a. Active player `⟨0⟩` concedes during `.beginningOfCombat`: `.declareAttackers` skips `Pending.declareAttackers`
    --     (`gA1.pending == .none`), and passing priority skips `.declareBlockers` / `.combatDamage` to `.endOfCombat`!
    let gA0 := (g3.beginStep .beginningOfCombat).concede ⟨0⟩
    let gA1 := mustApply (mustApply gA0 ⟨1⟩ .pass) ⟨2⟩ .pass
    let gA2 := mustApply (mustApply gA1 ⟨1⟩ .pass) ⟨2⟩ .pass
    -- 9b. `⟨0⟩` attacks `⟨1⟩` and `⟨2⟩`; during `Pending.declareBlockers` for `⟨1⟩`, `⟨1⟩` concedes and `⟨2⟩` declares `#[]`:
    --     attacker against `⟨2⟩` still receives `CombatEvent.remainedUnblocked`!
    let gB0 := addPermanent (addPermanent g3 bear ⟨0⟩ ⟨0⟩) hero ⟨0⟩ ⟨0⟩
    let atk1 := (gB0.battlefield.filter (·.name == bear.name))[0]!.id
    let atk2 := (gB0.battlefield.filter (·.name == hero.name))[0]!.id
    let gB1 := gB0.beginStep .beginningOfCombat
    let gB1 := mustApply (mustApply (mustApply gB1 ⟨0⟩ .pass) ⟨1⟩ .pass) ⟨2⟩ .pass
    let gB1 := mustApply gB1 ⟨0⟩ (.declareAttackers #[atk1, atk2] none #[some ⟨1⟩, some ⟨2⟩] #[])
    let gB1 := mustApply (mustApply (mustApply gB1 ⟨0⟩ .pass) ⟨1⟩ .pass) ⟨2⟩ .pass
    let gBLeft := gB1.concede ⟨1⟩
    let gBBlk2 := mustApply gBLeft ⟨2⟩ (.declareBlockers #[])
    -- 9c. `⟨1⟩` casts a spell targeting `⟨2⟩`'s Ward creature; once Ward resolves into `Pending.payWard`,
    --     `⟨1⟩` conceding counters/cleans up the spell and clears `Pending.payWard`!
    let gW0 := addPermanent (mustApply g3 ⟨0⟩ .pass) wardBearDef ⟨2⟩ ⟨2⟩
    let wId := (gW0.battlefield.filter (·.name == "Phase15 Ward Bear"))[0]!.id
    let gW0 := insertObject gW0 pingAnyDef ⟨1⟩ (.hand ⟨1⟩)
    let pH := (gW0.player ⟨1⟩).hand.back!
    let gWCast := mustApply (mustApply gW0 ⟨1⟩ (.cast pH)) ⟨1⟩ (.target (.permanent wId))
    let gWPrompt := mustApply (mustApply (mustApply gWCast ⟨1⟩ .pass) ⟨2⟩ .pass) ⟨0⟩ .pass
    let gWConcede := gWPrompt.concede ⟨1⟩
    let ok :=
      gA1.step == .declareAttackers &&
      gA1.pending == .none &&
      gA2.step == .endOfCombat &&
      gBLeft.pending == .declareBlockers &&
      gBLeft.currentBlockersPlayer == ⟨2⟩ &&
      gBBlk2.pending == .none &&
      gBBlk2.events.any (fun e =>
        match e.change with
        | .rules (.combat (.remainedUnblocked eo)) => eo.id == some atk2
        | _ => false) &&
      (match gWPrompt.pending with | .payWard p _ (.genericMana 2) => p == ⟨1⟩ | _ => false) &&
      gWConcede.pending == .none &&
      gWConcede.stack.isEmpty
    (gA2, gBBlk2, gWConcede, ok)
  let leaveTransitionsAllOk :=
    leaveGameTransitionsOk &&
    [gSkipDeclAtk, gBlkLeftUnblocked, gWardCasterLeft].all (fun g =>
      Game.replayEvents g.events == g && allRulesEventsClassified g)

  -- 10. Layer-7c `chosenCreatureType` scoping (`lordPump?`) & `lastKnownBefore?` single-life LKI.
  let bannerDef15 : CardDef := {
    name := "Phase15 Banner"
    manaCost := ManaCost.empty
    types := #[.artifact]
    asEntersChooseCreatureType := true
    staticAbilities := #[.chosenTypeCreaturesGet 1 1]
  }
  let elfDef15 : CardDef := creature "Phase15 Elf" ManaCost.empty #["Elf"] 1 1
  let gobDef15 : CardDef := creature "Phase15 Goblin" ManaCost.empty #["Goblin"] 2 2
  let (gBanners, gSingleLifeLki, bannerAndLkiOk) :=
    let g0 := addPermanent (addPermanent afterDraw elfDef15 me me) gobDef15 me me
    let elfId := (g0.battlefield.filter (·.name == "Phase15 Elf"))[0]!.id
    let gobId := (g0.battlefield.filter (·.name == "Phase15 Goblin"))[0]!.id
    let g0 := insertObject (insertObject g0 bannerDef15 me (.hand me))
      { bannerDef15 with name := "Phase15 Banner 2" } opp (.hand opp)
    let b1H := ((g0.player me).hand.filter (fun id => (g0.object! id).name == "Phase15 Banner"))[0]!
    let b2H := ((g0.player opp).hand.filter (fun id => (g0.object! id).name == "Phase15 Banner 2"))[0]!
    let (g1, _) := g0.putOntoBattlefield b1H me (cause := some testCause)
    let g1 := mustApply g1 me (.chooseName "Elf")
    let (g2, _) := g1.putOntoBattlefield b2H me (cause := some testCause)
    let g2 := mustApply g2 me (.chooseName "Goblin")
    -- Also place a 3rd banner on `me` choosing Elf so Elf gets +2/+2 (3/3) while Goblin only gets +1/+1 (3/3, not +3/+3)!
    let g2 := insertObject g2 { bannerDef15 with name := "Phase15 Banner 3" } me (.hand me)
    let b3H := (g2.player me).hand.back!
    let (g3, _) := g2.putOntoBattlefield b3H me (cause := some testCause)
    let g3 := mustApply g3 me (.chooseName "Elf")
    let bannerOk :=
      g3.power (g3.object! elfId) == 3 &&
      g3.toughness (g3.object! elfId) == 3 &&
      g3.power (g3.object! gobId) == 3 &&
      g3.toughness (g3.object! gobId) == 3
    -- Single-life `lastKnownBefore?`: battlefield (`elfId` at 3/3) -> graveyard (`gyId` at 1/1) -> hand (`hId`).
    let (g4, gyId) := g3.move elfId (.graveyard me) none (cause := some testCause)
    let (g5, hId) := g4.move gyId (.hand me) none (cause := some testCause)
    let lkiOk :=
      g5.lastKnownPowerOf? elfId == some 3 &&
      (g4.lastKnownPowerOf? gyId).isNone &&
      g5.lastKnownPowerOf? gyId == some 1 &&
      (g5.lastKnownPowerOf? hId).isNone
    (g3, g5, bannerOk && lkiOk)
  let chosenTypeAndLkiAllOk :=
    bannerAndLkiOk &&
    [gBanners, gSingleLifeLki].all (fun g =>
      Game.replayEvents g.events == g && allRulesEventsClassified g)

  -- 11. `ObjectId ⟨0⟩` parity & `EngineChange.stackEntry` deterministic replay.
  let (gZeroIdAndStack, zeroIdParityOk) :=
    let g0 := afterDraw
    let zeroId : ObjectId := ⟨0⟩
    let obj0Present := (g0.findObject? zeroId).isSome
    -- Verify `ObjectId ⟨0⟩` is never matched by `none` source triggers and IS matched only by `some ⟨0⟩`!
    let zeroMoveEv := GameEvent.moved 1
      { id := some zeroId, controller := some me, owner := me, types := #[.creature] } .battlefield (.graveyard me)
      (cause := testCause)
    let otherMoveEv := GameEvent.moved 1
      { id := some ⟨7⟩, controller := some me, owner := me, types := #[.creature] } .battlefield (.graveyard me)
      (cause := testCause)
    let triggerZeroOk :=
      zeroMoveEv.matchesTrigger me (some zeroId) .dying &&
      !zeroMoveEv.matchesTrigger me none .dying &&
      !otherMoveEv.matchesTrigger me (some zeroId) .dying &&
      !otherMoveEv.matchesTrigger me none .dying
    let c0 := g0.object! zeroId
    let otherLibId := ((g0.player me).library.filter (· != zeroId))[0]!
    let gZ1 := g0.createEffect
      (.replacement { id := { kind := .finalityCounterExile, object := some zeroId },
                      affectedPlayer := c0.owner, kind := .exileInsteadOfGraveyard (some zeroId) false } .untilEndOfTurn)
      (cause := some testCause)
    let (gZ2, movedOther) := gZ1.move otherLibId (.graveyard me) none (verb := some .mill) (cause := some testCause)
    let (gZ3, movedZero) := gZ2.move zeroId (.graveyard c0.owner) none (verb := some .mill) (cause := some testCause)
    -- `EngineChange.stackEntry` mutation & deterministic replay:
    let gSt0 := addPermanent (addPermanent gZ3 bear opp opp) hero opp opp
    let t1 := (gSt0.battlefield.filter (fun (o : GameObject) => o.name == bear.name))[0]!.id
    let t2 := (gSt0.battlefield.filter (fun (o : GameObject) => o.name == hero.name))[0]!.id
    let gSt0 := insertObject gSt0 pingAnyDef me (.hand me)
    let pId := (gSt0.player me).hand.back!
    let gSt1 := mustApply (mustApply gSt0 me (.cast pId)) me (.target (.permanent t1))
    let stObjId := gSt1.stack.back!.objectId
    let gSt2 := (gSt1.setStackEntryTargets stObjId #[Target.permanent t2] #[]).markTargetsAnnounced stObjId true
    let ok :=
      obj0Present &&
      triggerZeroOk &&
      (gZ3.object! movedOther).zone == Zone.graveyard me &&
      (gZ3.object! movedZero).zone == Zone.exile &&
      (gSt2.stackEntry? stObjId).map (fun (se : StackEntry) => se.targets) == some #[Target.permanent t2]
    (gSt2, ok)
  let zeroParityAndStackAllOk :=
    zeroIdParityOk &&
    Game.replayEvents gZeroIdAndStack.events == gZeroIdAndStack &&
    allRulesEventsClassified gZeroIdAndStack

  -- ==========================================================================
  -- 12. `wasPermanentDestroyed` / `destroyPermanentsLoop` tally (CR 701.8a-c,
  --     CR 800.4c non-destroy exile exclusion, WotC Ruling 80 `ZoneVerb.destroy`
  --     preservation across graveyard-redirect replacements)
  -- ==========================================================================
  let destroyedTallyAllOk : Bool := Id.run do
    let threeCfg12 : StartConfig := {
      seats := #[
        { name := "Chandra", deck := testRedDeck },
        { name := "Nissa", deck := testGreenDeck },
        { name := "Liliana", deck := testRedDeck }
      ]
      format := .constructed
      seed := 12
      startingPlayer := some 0
    }
    let g0 :=
      match Start.start threeCfg12 with
      | .ok g => keepOpeningHands g 12
      | .error e => panic! e
    let indRelicDef : CardDef :=
      { name := "Phase15 Indestructible Relic", manaCost := ManaCost.empty,
        types := #[.artifact], keywords := { indestructible := true } }
    let shdRelicDef : CardDef :=
      { name := "Phase15 Shield Relic", manaCost := ManaCost.empty, types := #[.artifact] }
    let finRelicDef : CardDef :=
      { name := "Phase15 Finality Relic", manaCost := ManaCost.empty, types := #[.artifact] }
    let g0 := addPermanent g0 bear ⟨1⟩ ⟨1⟩
    let ctrlSrcId := (g0.battlefield.filter (·.name == bear.name))[0]!.id
    let g0 := addPermanent g0 hero ⟨2⟩ ⟨2⟩
    let stolenId := (g0.battlefield.filter (·.name == hero.name))[0]!.id
    let g0 := g0.changeControl (g0.object! stolenId) ⟨1⟩ (untilSourceLeaves := some ctrlSrcId) (cause := some testCause)
    let g0 := g0.concede ⟨2⟩
    let g0 := addPermanent g0 indRelicDef ⟨1⟩ ⟨1⟩
    let indId := (g0.battlefield.filter (·.name == "Phase15 Indestructible Relic"))[0]!.id
    let g0 := addPermanent g0 shdRelicDef ⟨1⟩ ⟨1⟩
    let shdId := (g0.battlefield.filter (·.name == "Phase15 Shield Relic"))[0]!.id
    let g0 := g0.recordPutCounters shdId .shield 1 (some ⟨1⟩) (cause := some testCause)
    let g0 := addPermanent g0 finRelicDef ⟨1⟩ ⟨1⟩
    let finId := (g0.battlefield.filter (·.name == "Phase15 Finality Relic"))[0]!.id
    let g0 := g0.recordPutCounters finId .finality 1 (some ⟨1⟩) (cause := some testCause)
    let cands := #[ctrlSrcId, stolenId, indId, shdId, finId]
    let gOut :=
      g0.withContinuationFrame fun g =>
        g.withBatch (some testCause) fun g =>
          g.destroyPermanentsLoop cands (allCandidates := cands) (countNote := true)
            (obGainLifeFor := some ⟨0⟩) (preBattlefield := some g.battlefield) (cause := some testCause)
    gOut.wasPermanentDestroyed ctrlSrcId &&
    !gOut.wasPermanentDestroyed stolenId &&
    !gOut.wasPermanentDestroyed indId &&
    !gOut.wasPermanentDestroyed shdId &&
    gOut.wasPermanentDestroyed finId &&
    (gOut.player ⟨0⟩).life == 22 &&
    !(gOut.findObject? stolenId).any (·.isOnBattlefield) &&
    (gOut.findObject? indId).any (·.isOnBattlefield) &&
    (gOut.findObject? shdId).any (fun o => o.isOnBattlefield && o.status.shield == 0) &&
    gOut.objects.any (fun o => o.name == "Phase15 Finality Relic" && o.zone == .exile) &&
    Game.replayEvents gOut.events == gOut &&
    allRulesEventsClassified gOut

  let mustHold15 (label : String) (ok : Bool) : Bool :=
    if ok then true else panic! s!"Phase 15 guard failed: {label}"

  [ mustHold15 "seqAndMayThenOk" seqAndMayThenOk,
    mustHold15 "standaloneManaAndPrioOk" standaloneManaAndPrioOk,
    mustHold15 "twAndPaidAllOk" twAndPaidAllOk,
    mustHold15 "triggerOrderingAllOk" triggerOrderingAllOk,
    mustHold15 "wardAndNestedAllOk" wardAndNestedAllOk,
    mustHold15 "lkiAndMultiSbaAllOk" lkiAndMultiSbaAllOk,
    mustHold15 "combatAlignmentAllOk" combatAlignmentAllOk,
    mustHold15 "cleanupAllOk" cleanupAllOk,
    mustHold15 "leaveTransitionsAllOk" leaveTransitionsAllOk,
    mustHold15 "chosenTypeAndLkiAllOk" chosenTypeAndLkiAllOk,
    mustHold15 "zeroParityAndStackAllOk" zeroParityAndStackAllOk,
    mustHold15 "destroyedTallyAllOk" destroyedTallyAllOk ].all id

/- Phase 16 isolation & replay tests:
   1. Pause-safe `amass` (fresh Army token & `+1/+1` counter `chooseReplacement`
      before `attachSourceTo`), library-reveal (`resolveRandomCreatureReveal`
      pausing before `putRestOnBottomRandom`), and mill-then-choose
      (`millThenPutFromGy` / `millThenChooseForHand` across replacement).
   2. `mayThen` `.maySacArtifactOrDiscard` (both sync and paused inside an active
      resolution frame before frame pop), `chooseTriggerOr` preserving outer
      `PendingReplacement`, and `turnFaceUp` (`SacrificeDiscard.sacrificeForActivation`
      deferring `turnedFaceUp` across `.chooseReplacement`).
   3. Sync-vs-paused replacement parity: Aura/permanent spell entry redirected to
      `.exile` (no `"enters the battlefield"` log or `afterPermanentEnters`, while
      normal paused Aura entry logs `"attached to {host}"`), and `Pumps` counter
      `putter` attribution + `n' == 0` early-exit + `.time` `syncImpendingNotACreature`.
   4. CR 603.2 / 603.4 `putQueuedTrigger` (already-triggered `wt.checked == true`
      not rechecked against post-event state), CR 603.4 / 608.2a resolution removal
      (`removedOnResolution` without `StackObjectEvent.resolved`), non-intervening
      trigger conditions unrechecked on resolution, and CR 702.176a Impending
      end-step trigger + intervening-`"if"` re-check.
   5. CR 608.2b / 115.1c / 702.16b target legality: targeted activated & non-FRA
      triggered ability all-targets-illegal removal, multi-slot spell per-slot
      validation & `skippedOptionalSlots : Array Nat` (`#[0]`), and CR 702.16b
      protection against ability sources.
   6. CR 704.3 / 704.8 SBA pre-704.5q counter-annihilation LKI & single-batch
      `Pending.chooseLegend` keeping Pass 1 open through `finishSbaSweep` (tokens
      704.5d, Sagas 714.4, Auras 704.5m, Equipment 704.5n).
   7. CR 111.8 token-flicker prohibition & simultaneous two-batch multi-target
      flicker.
   8. CR 603.10 `.creatureCardsPutIntoYourGy` (`after.creature && !after.token`)
      & CR 701.17c `ZoneVerb.mill` in public zones (`followMilledPublic?`).
   9. CR 800.4a/h leave-game continuation handling (`.chooseTargets` trigger
      checkpoint safety, `.chooseSacrificeCreature` last-player `finishChosenSacrifices`,
      multi-player `FraChoice` queue advance, and `.chooseReplacement` transfer).
   10. CR 702.131a/b/d `citysBlessing` / `enduringStory` batch evaluation in
       `Core.closeBatch` + instant/sorcery `ascend` in `resolveTop`, and
       `Option BatchId` (`none` vs `some ⟨0⟩`) envelope fidelity. -/
section Phase16EventAlignment

private def headHuntDef : CardDef :=
  { bear with name := "Phase16 Head Hunt", staticAbilities := #[.exileOppDeathCreateWolf] }
private def samsonDef16 : CardDef :=
  { bear with name := "Phase16 Doc Samson", staticAbilities := #[.extraCounterOnPermanents] }
private def equipDef16 : CardDef := {
  name := "Phase16 Sword"
  manaCost := ManaCost.empty
  types := #[.artifact]
  subtypes := #["Equipment"]
}
private def mustHold16 (label : String) (ok : Bool) : Bool :=
  if ok then true else panic! s!"Phase 16 guard failed: {label}"

-- 1. Pause-safe `amass`, library-reveal, and mill-then-choose.
#guard
  -- 1a1. `amass` fresh Army token creation pausing on two non-commuting `entersWithExtraCounters`
  --      (`+1` vs `+2` `.plusOnePlusOne`) BEFORE `finishAmassOn` and BEFORE `attachSourceTo`!
  let gAF0 : Game := addPermanent (addPermanent afterDraw equipDef16 me me) bear me me
  let eqFId := (gAF0.battlefield.filter (·.name == "Phase16 Sword"))[0]!.id
  let bFId := (gAF0.battlefield.filter (·.name == bear.name))[0]!.id
  let idEnt1 : ReplacementId := { kind := .entersWithExtraCounters, object := some eqFId, counterKind := some .plusOnePlusOne }
  let idEnt2 : ReplacementId := { kind := .entersWithExtraCounters, object := some bFId, counterKind := some .plusOnePlusOne }
  let gAF0 : Game := (gAF0.createEffect
    (.replacement { id := idEnt1, source := some eqFId, controller := some me, affectedPlayer := me,
                    kind := .entersWithExtraCounters none .plusOnePlusOne 1 }) (cause := some testCause)).createEffect
    (.replacement { id := idEnt2, source := some bFId, controller := some me, affectedPlayer := me,
                    kind := .entersWithExtraCounters none .plusOnePlusOne 2 }) (cause := some testCause)
  let gAFPaused : Game := gAF0.amass me .orc 2 (attach := some eqFId) (cause := some testCause)
  let freshArmyPausedOk : Bool :=
    (match gAFPaused.pending with | .chooseReplacement p cs => p == me && cs.size == 2 | _ => false) &&
    (gAFPaused.object! eqFId).attachedTo.isNone &&
    !(gAFPaused.permanentsOf me).any (fun o => gAFPaused.hasSubtype o .army)
  let gAFDone : Game := mustApply gAFPaused me (.chooseReplacement idEnt1)
  let freshArmiesDone := (gAFDone.permanentsOf me).filter (fun o => gAFDone.hasSubtype o .army)
  let freshArmyDoneOk : Bool :=
    gAFDone.pending == .none &&
    freshArmiesDone.size == 1 &&
    -- Entered with 1 + 2 = 3 `+1/+1` counters, then `finishAmassOn` added 2 -> 5 total, THEN `eqFId` attached!
    freshArmiesDone[0]!.status.plusOnePlusOne == 5 &&
    (gAFDone.object! eqFId).attachedTo == some freshArmiesDone[0]!.id

  -- 1a2. `finishAmassOn` pausing on two counter-put replacements (`+1` vs `×2`) BEFORE `attachSourceTo`!
  let gA0 : Game := addPermanent (addPermanent afterDraw equipDef16 me me) samsonDef16 me me
  let eqId := (gA0.battlefield.filter (·.name == "Phase16 Sword"))[0]!.id
  let docId := (gA0.battlefield.filter (·.name == "Phase16 Doc Samson"))[0]!.id
  let idDocPlus : ReplacementId := { kind := .extraCounterOnPermanents, object := some docId, counterKind := some .plusOnePlusOne }
  let idCntDbl : ReplacementId := { kind := .multiplyCountersPut, object := some eqId }
  let gA0 : Game := gA0.createEffect
    (.replacement { id := idCntDbl, source := some eqId, controller := some me, affectedPlayer := me,
                    kind := .modifyCountersPut none (some .plusOnePlusOne) 0 2 }) (cause := some testCause)
  let gAP2 : Game := gA0.amass me .orc 2 (attach := some eqId) (cause := some testCause)
  let armiesAtP2 := (gAP2.permanentsOf me).filter (fun o => gAP2.hasSubtype o .army)
  let amassPaused2 : Bool :=
    armiesAtP2.size == 1 &&
    (match gAP2.pending with | .chooseReplacement p cs => p == me && cs.size == 2 | _ => false) &&
    (gAP2.object! eqId).attachedTo.isNone
  let gADone : Game := mustApply gAP2 me (.chooseReplacement idDocPlus)
  let armiesDone := (gADone.permanentsOf me).filter (fun o => gADone.hasSubtype o .army)
  let amassFinishedOk : Bool :=
    gADone.pending == .none &&
    armiesDone.size == 1 &&
    armiesDone[0]!.status.plusOnePlusOne == 6 &&
    (gADone.object! eqId).attachedTo == some armiesDone[0]!.id

  -- 1b. `resolveRandomCreatureReveal` pausing on `chooseReplacement` before `putRestOnBottomRandom`.
  let oddCreatureDef : CardDef := { bear with name := "Phase16 Odd Bear", asEntersChooseOddEven := true }
  let gR0 : Game := insertObject afterDraw oddCreatureDef me (.library me)
  let lib := (gR0.player me).library
  let chosenId := lib.back!
  let restId := lib[lib.size - 2]!
  let gRP : Game := gR0.resolveRandomCreatureReveal me #[chosenId, restId] chosenId (cause := some testCause)
  let revPausedOk : Bool :=
    (match gRP.pending with | .chooseReplacement p _ => p == me | _ => false) &&
    (gRP.player me).library.back? == some chosenId &&
    (gRP.player me).library[0]? != some restId
  let gRD : Game := mustApply gRP me (.chooseMode 1)
  let movedRest? := (gRD.followMovedToZone? restId (· == .library me)).map (·.id)
  let revDoneOk : Bool :=
    gRD.pending == .none &&
    gRD.battlefield.any (fun o => o.name == "Phase16 Odd Bear" && o.status.chosenOdd == some true) &&
    movedRest?.isSome &&
    movedRest? != some restId &&
    (gRD.player me).library[0]? == movedRest?

  -- 1c. `millThenPutFromGy` pausing on `chooseReplacement` when two graveyard exile redirects compete,
  --     AND still finding the milled creature card in `.exile` via CR 701.17c `followMilledPublic?`!
  let gM0 : Game := insertObject afterDraw hero me (.library me)
  let topHero := (gM0.player me).library.back!
  let idEx1 : ReplacementId := { kind := .finalityCounterExile, object := some topHero }
  let idEx2 : ReplacementId := { kind := .exileOppDeath, object := some topHero }
  let gM0 : Game := (gM0.createEffect
    (.replacement { id := idEx1, affectedPlayer := me, kind := .exileInsteadOfGraveyard (some topHero) false })
    (cause := some testCause)).createEffect
    (.replacement { id := idEx2, affectedPlayer := me, kind := .exileInsteadOfGraveyard (some topHero) false })
    (cause := some testCause)
  let gMP : Game := gM0.millThenPutFromGy me 1 (fun o => gM0.isCreature o) (maxPut := some 1) (types := #[.creature])
  let millPausedOk : Bool :=
    (match gMP.pending with | .chooseReplacement p cs => p == me && cs.size == 2 | _ => false) &&
    !(gMP.player me).hand.any (fun id => (gMP.object! id).name == hero.name)
  let gMD : Game := mustApply gMP me (.chooseReplacement idEx1)
  let millDoneOk : Bool :=
    gMD.pending == .none &&
    (gMD.player me).hand.any (fun id => (gMD.object! id).name == hero.name)

  mustHold16 "1a1.freshArmyPausedOk" freshArmyPausedOk &&
  mustHold16 "1a1.freshArmyDoneOk" freshArmyDoneOk &&
  mustHold16 "1a2.amassPaused2" amassPaused2 &&
  mustHold16 "1a2.amassFinishedOk" amassFinishedOk &&
  mustHold16 "1b.revPausedOk" revPausedOk &&
  mustHold16 "1b.revDoneOk" revDoneOk &&
  mustHold16 "1c.millPausedOk" millPausedOk &&
  mustHold16 "1c.millDoneOk" millDoneOk &&
  mustHold16 "1.replay" ([gAFPaused, gAFDone, gAP2, gADone, gRP, gRD, gMP, gMD].all (fun g =>
    Game.replayEvents g.events == g && allRulesEventsClassified g))

-- 2. `mayThen` `.maySacArtifactOrDiscard`, `chooseTriggerOr`, and `turnFaceUp` continuation ordering.
#guard
  let (gMaySync, gMayPause, gMayPauseDone, gTrigOrPause, gTrigOrDone, gMorphSacPause, gMorphSacDone, step2ContOk) :=
    let relicDef : CardDef := { name := "Phase16 Relic", manaCost := ManaCost.empty, types := #[.artifact] }
    -- Sequence `[maySacArtifactOrDiscardDraw, gainLife 3]` so we prove `mayThenResume` (draw 1)
    -- runs BEFORE the outer sequence step (gain 3 life) and BEFORE frame pop in BOTH sync and paused cases!
    let seqRes : TriggeredAbility.TriggerResolution :=
      .sequence [
        .may (.pay (.or [.sacrifice (.fixed 1) .artifact, .discard (.fixed 1) .card]))
          (.draw (.fixed 1)) .ifYouDo,
        .gainLife (.fixed 3) ]
    let gS0 := addPermanent (addPermanent afterDraw bear me me) relicDef me me
    let srcId := (gS0.battlefield.filter (·.name == bear.name))[0]!.id
    let relId := (gS0.battlefield.filter (·.name == "Phase16 Relic"))[0]!.id
    let handBefore := (gS0.player me).hand.size
    -- 2a. Synchronous sacrifice inside `resolveTop` of `seqRes`:
    let gStSync := gS0.putTriggeredAbilityOnStack me (gS0.object! srcId) (.onEnterDraw 1) "enters"
      (eventCause := some testCause) (reflexiveResolution := some seqRes)
    let gPromptSync := gStSync.resolveTop
    let gSyncDone := mustApply gPromptSync me (.sacrifice relId)
    let syncMayOk :=
      (match gPromptSync.pending with | .maySacArtifactOrDiscard p 1 => p == me | _ => false) &&
      (gPromptSync.player me).life == 20 &&
      gSyncDone.pending == .none &&
      gSyncDone.stack.isEmpty &&
      gSyncDone.continuations.isEmpty &&
      (gSyncDone.player me).hand.size == handBefore + 1 &&
      (gSyncDone.player me).life == 23
    -- 2b. Paused sacrifice (`.finality` + `.untilEotExileIfDies` -> `Pending.chooseReplacement`) inside `resolveTop` of `seqRes`:
    let idExRel : ReplacementId := { kind := .untilEotExileIfDies, object := some relId }
    let gP0 := (gS0.createEffect
      (.replacement { id := idExRel, affectedPlayer := me, kind := .exileInsteadOfGraveyard (some relId) false })
      (cause := some testCause)).recordPutCounters relId .finality 1 (some me) (cause := some testCause)
    let gStP := gP0.putTriggeredAbilityOnStack me (gP0.object! srcId) (.onEnterDraw 1) "enters"
      (eventCause := some testCause) (reflexiveResolution := some seqRes)
    let gPromptP := gStP.resolveTop
    let gSacPaused := mustApply gPromptP me (.sacrifice relId)
    let gSacDone := mustApply gSacPaused me (.chooseReplacement idExRel)
    let pausedMayOk :=
      (match gSacPaused.pending with | .chooseReplacement p cs => p == me && cs.size == 2 | _ => false) &&
      (gSacPaused.player me).hand.size == handBefore &&
      (gSacPaused.player me).life == 20 &&
      !gSacPaused.stack.isEmpty &&
      gSacDone.pending == .none &&
      gSacDone.stack.isEmpty &&
      gSacDone.continuations.isEmpty &&
      (gSacDone.player me).hand.size == handBefore + 1 &&
      (gSacDone.player me).life == 23

    -- 2c. `chooseTriggerOr` preserving outer `PendingReplacement` (sequence step `.gainLife (.fixed 4)`):
    let orRes : TriggeredAbility.TriggerResolution :=
      .sequence [
        .or [.gainLife (.fixed 2), .draw (.fixed 1)],
        .gainLife (.fixed 4) ]
    let gOrSt := gS0.putTriggeredAbilityOnStack me (gS0.object! srcId) (.onEnterDraw 1) "enters"
      (eventCause := some testCause) (reflexiveResolution := some orRes)
    let gOrPrompt := gOrSt.resolveTop
    let gOrResolved := mustApply gOrPrompt me (.chooseMode 0)
    let trigOrOk :=
      (match gOrPrompt.pending with | .chooseTriggerOr p => p == me | _ => false) &&
      (gOrPrompt.player me).life == 20 &&
      gOrResolved.pending == .none &&
      gOrResolved.stack.isEmpty &&
      gOrResolved.continuations.isEmpty &&
      (gOrResolved.player me).life == 26

    -- 2d. `SacrificeDiscard.sacrificeForActivation` `.turnFaceUp` deferring `GameEvent.turnedFaceUp`
    --     across `Pending.chooseReplacement` when sacrificing a creature to turn face up:
    let morphFaceDef : CardDef := creature "Phase16 MorphSpy" ManaCost.empty #["Human"] 3 3
    let gMf0 := addPermanent (addPermanent afterDraw morphFaceDef me me) bear me me
    let mId := (gMf0.battlefield.filter (·.name == "Phase16 MorphSpy"))[0]!.id
    let fodderId := (gMf0.battlefield.filter (·.name == bear.name))[0]!.id
    let idExFod : ReplacementId := { kind := .untilEotExileIfDies, object := some fodderId }
    let gMf0 := ((setFaceDown gMf0 mId true).createEffect
      (.replacement { id := idExFod, affectedPlayer := me, kind := .exileInsteadOfGraveyard (some fodderId) false })
      (cause := some testCause)).recordPutCounters fodderId .finality 1 (some me) (cause := some testCause)
    let mObj := gMf0.object! mId
    let propMorph : ProposedSpell := {
      caster := me
      cost := ManaCost.empty
      spellId := mId
      sourceId := some mId
      original := mObj
      originalSnapshot := gMf0.snapshot mObj
      kind := .turnFaceUp
      needsSacrificeOther := true
    }
    let gMfPrompt := gMf0.changes #[.saveProposalCheckpoint, .proposedSpell (some propMorph), .pending (.sacrificePermanent me mId)]
    let gMfPaused := mustApply gMfPrompt me (.sacrifice fodderId)
    let gMfDone := mustApply gMfPaused me (.chooseReplacement idExFod)
    let morphSacOk :=
      (match gMfPaused.pending with | .chooseReplacement p cs => p == me && cs.size == 2 | _ => false) &&
      -- Still face-down while sacrifice replacement choice is pending (CR 708.8)!
      (gMfPaused.object! mId).status.faceDown &&
      !gMfPaused.events.any (fun e =>
        match e.change with | .rules (.permanent (.turnedFaceUp eo)) => eo.id == some mId | _ => false) &&
      gMfDone.pending == .none &&
      !(gMfDone.object! mId).status.faceDown &&
      gMfDone.proposalCheckpoint.isNone &&
      gMfDone.proposedSpell.isNone &&
      gMfDone.events.any (fun e =>
        match e.change with | .rules (.permanent (.turnedFaceUp eo)) => eo.id == some mId | _ => false)
    let _ := headHuntDef
    (gSyncDone, gSacPaused, gSacDone, gOrPrompt, gOrResolved, gMfPaused, gMfDone,
     syncMayOk && pausedMayOk && trigOrOk && morphSacOk)
  let step2AllOk :=
    step2ContOk &&
    [gMaySync, gMayPause, gMayPauseDone, gTrigOrPause, gTrigOrDone, gMorphSacPause, gMorphSacDone].all (fun g =>
      Game.replayEvents g.events == g && allRulesEventsClassified g)
  mustHold16 "step2AllOk" step2AllOk

-- 3. Sync-vs-paused replacement parity (Aura/permanent `.exileInsteadOfStackLeave` & `Pumps` counter putters).
#guard
  let etbAuraDef : CardDef :=
    aura "Phase16 Exile Aura" ManaCost.empty "Enchant creature\nWhen Phase16 Exile Aura enters, you gain 5 life."
      (triggeredAbilities := #[TriggeredAbility.fra .enter "When Phase16 Exile Aura enters, you gain 5 life." (.gainLife (.fixed 5))])
  let etbPermDef : CardDef := {
    bear with
    name := "Phase16 Exile Bear"
    triggeredAbilities := #[TriggeredAbility.fra .enter "When Phase16 Exile Bear enters, you gain 5 life." (.gainLife (.fixed 5))]
  }
  let gE0 : Game := addPermanent afterDraw bear me me
  let hostId := (gE0.battlefield.filter (·.name == bear.name))[0]!.id
  -- 3a. Aura spell redirected to `.exile` on stack leave: no `"enters the battlefield"` log, no ETB life gain!
  let gEA0 : Game := insertObject gE0 etbAuraDef me (.hand me)
  let auraH := (gEA0.player me).hand.back!
  let gEA1 : Game := mustApply (mustApply gEA0 me (.cast auraH)) me (.target (.permanent hostId))
  let auraSpellId := gEA1.stack.back!.objectId
  let gEA1 : Game := gEA1.createEffect
    (.replacement { id := { kind := .flashbackExile, object := some auraSpellId },
                    affectedPlayer := me, kind := .exileInsteadOfStackLeave (some auraSpellId) })
    (cause := some testCause)
  let logBeforeEA := gEA1.log.size
  let gEA2 : Game := gEA1.resolveTop
  let auraExileOk : Bool :=
    gEA2.objects.any (fun o => o.name == "Phase16 Exile Aura" && o.zone == .exile) &&
    !(gEA2.log.extract logBeforeEA gEA2.log.size).any (fun s => (s.splitOn "enters the battlefield").length > 1) &&
    gEA2.waitingTriggers.isEmpty &&
    (gEA2.player me).life == 20
  -- 3b. Creature spell redirected to `.exile` on stack leave: no `"enters the battlefield"` log, no ETB life gain!
  let gEP0 : Game := insertObject gE0 etbPermDef me (.hand me)
  let permH := (gEP0.player me).hand.back!
  let gEP1 : Game := mustApply gEP0 me (.cast permH)
  let permSpellId := gEP1.stack.back!.objectId
  let gEP1 : Game := gEP1.createEffect
    (.replacement { id := { kind := .flashbackExile, object := some permSpellId },
                    affectedPlayer := me, kind := .exileInsteadOfStackLeave (some permSpellId) })
    (cause := some testCause)
  let logBeforeEP := gEP1.log.size
  let gEP2 : Game := gEP1.resolveTop
  let permExileOk : Bool :=
    gEP2.objects.any (fun o => o.name == "Phase16 Exile Bear" && o.zone == .exile) &&
    !(gEP2.log.extract logBeforeEP gEP2.log.size).any (fun s => (s.splitOn "enters the battlefield").length > 1) &&
    gEP2.waitingTriggers.isEmpty &&
    (gEP2.player me).life == 20
  -- 3c. Normal paused Aura spell entry DOES log `"attached to Event Bear"` once the as-enters choice resolves!
  let oddAuraDef : CardDef := {
    aura "Phase16 Odd Aura" ManaCost.empty "Enchant creature" with
    asEntersChooseOddEven := true
  }
  let gOA0 : Game := insertObject gE0 oddAuraDef me (.hand me)
  let oddAuraH := (gOA0.player me).hand.back!
  let gOA1 : Game := mustApply (mustApply gOA0 me (.cast oddAuraH)) me (.target (.permanent hostId))
  let logBeforeOA := gOA1.log.size
  let gOAPaused : Game := gOA1.resolveTop
  let gOADone : Game := mustApply gOAPaused me (.chooseMode 1)
  let oddAuraAttachLogOk : Bool :=
    (gOADone.log.extract logBeforeOA gOADone.log.size).any (fun s =>
      (s.splitOn "Phase16 Odd Aura enters the battlefield attached to Event Bear").length > 1)
  -- 3d. `Pumps` counter `putter` attribution (`opp` resolving context -> `putter == some opp`),
  --     `n' == 0` early-exit (`mult := 0`), and `addCounters .time` `syncImpendingNotACreature`:
  let impBearDef16 : CardDef := { bear with name := "Phase16 Impending Bear", impending := some (1, ManaCost.empty) }
  let gPP0 : Game := insertObject gE0 impBearDef16 me (.hand me)
  let impH := (gPP0.player me).hand.back!
  let gPP1 : Game := mustApply (mustApply gPP0 me (.cast impH)) me (.announceKicker true)
  let gPP1Res : Game := gPP1.resolveTop
  let gPP2 : Game := gPP1Res.removeAllCountersFrom
    (gPP1Res.battlefield.filter (·.name == "Phase16 Impending Bear"))[0]!.id
    (byPlayer := some me) (cause := some testCause)
  let impPermId := (gPP2.battlefield.filter (·.name == "Phase16 Impending Bear"))[0]!.id
  let wasCreatureAtZero : Bool := gPP2.isCreature (gPP2.object! impPermId)
  let gPP3 : Game := gPP2.withResolvingContext none opp fun g =>
    g.addIndestructibleCounter (g.object! hostId) 1 (cause := some (.oneShotEffect none none (some opp)))
  let gPP4 : Game := gPP3.addCounters (gPP3.object! impPermId) .time 1 (cause := some testCause)
  let gPP5 : Game := gPP4.createEffect
    (.replacement { id := { kind := .multiplyCountersPut, object := some hostId },
                    affectedPlayer := me, kind := .modifyCountersPut (some hostId) (some .lifelink) 0 0 })
    (cause := some testCause)
  let evBeforeZero := gPP5.events.size
  let logBeforeZero := gPP5.log.size
  let gPP6 : Game := gPP5.addLifelinkCounter (gPP5.object! hostId) 1 (cause := some testCause)
  let pumpsSubOk : Bool :=
    mustHold16 "3d.wasCrea" wasCreatureAtZero &&
    mustHold16 "3d.notCrea" (!gPP4.isCreature (gPP4.object! impPermId)) &&
    mustHold16 "3d.putter" (gPP3.events.any (fun e =>
      match e.change with
      | .rules (.permanent (.counters (.object eo) .indestructible (.put 1) (some p))) =>
        p == opp && eo.id == some hostId
      | _ => false)) &&
    mustHold16 "3d.zeroCnt" ((gPP6.object! hostId).status.counters.count .lifelink == 0) &&
    mustHold16 "3d.zeroEv" (!(gPP6.events.extract evBeforeZero gPP6.events.size).any (fun e =>
      match e.change with | .rules (.permanent (.counters ..)) => true | _ => false)) &&
    mustHold16 "3d.zeroLog" (gPP6.log.size == logBeforeZero)
  mustHold16 "3a.auraExileOk" auraExileOk &&
  mustHold16 "3b.permExileOk" permExileOk &&
  mustHold16 "3c.oddAuraAttachLogOk" oddAuraAttachLogOk &&
  pumpsSubOk &&
  mustHold16 "3.replayEA" (Game.replayEvents gEA2.events == gEA2 && allRulesEventsClassified gEA2) &&
  mustHold16 "3.replayEP" (Game.replayEvents gEP2.events == gEP2 && allRulesEventsClassified gEP2) &&
  mustHold16 "3.replayOA" (Game.replayEvents gOADone.events == gOADone && allRulesEventsClassified gOADone) &&
  mustHold16 "3.replayPP" (Game.replayEvents gPP6.events == gPP6 && allRulesEventsClassified gPP6)

-- 4. CR 603.2 / 603.4 `putQueuedTrigger`, CR 603.4 / 608.2a `removedOnResolution` without `resolved`,
--    non-intervening trigger condition unrechecked on resolution, & CR 702.176a Impending trigger.
#guard
  let whipTrig := TriggeredAbility.onThisAttack Effect.thisAttackEquippedDrain
  let gQ0 : Game := addPermanent afterDraw bear me me
  let bId := (gQ0.battlefield.filter (·.name == bear.name))[0]!.id
  let wtChecked : WaitingTrigger := {
    controller := me
    source := gQ0.object! bId
    ability := whipTrig
    event := .attacking
    checked := true
  }
  let gQ1 : Game := (gQ0.enqueueWaitingTriggers #[wtChecked]).receivePriority me
  let queuedWentOnStack : Bool := gQ1.stack.size == 1
  let abStackId := gQ1.stack.back!.objectId
  let preResIdx := gQ1.events.size
  let gQ2 : Game := gQ1.resolveTop
  let resSlice := gQ2.events.extract preResIdx gQ2.events.size
  let intervRemovedNoResolved : Bool :=
    gQ2.stack.isEmpty &&
    (gQ2.player opp).life == 20 &&
    resSlice.any (fun e =>
      match e.change with
      | .rules (.stackObject (.removedOnResolution eo)) => eo.id == some abStackId
      | _ => false) &&
    !resSlice.any (fun e =>
      match e.change with
      | .rules (.stackObject (.resolved ..)) => true
      | _ => false)

  let harnTrig := TriggeredAbility.onStep Effect.stepHarnessedFlicker
  let (gN1, harnStObj) : Game × GameObject := gQ0.putStackAbility (gQ0.object! bId) me (triggeredAbility := some harnTrig)
  let preNIdx := gN1.events.size
  let gN2 : Game := gN1.resolveTop
  let nonIntervResolved : Bool :=
    gN2.stack.isEmpty &&
    (gN2.events.extract preNIdx gN2.events.size).any (fun e =>
      match e.change with
      | .rules (.stackObject (.resolved eo ..)) => eo.id == some harnStObj.id
      | _ => false)

  let impDef4 : CardDef := { bear with name := "Phase16 Impending Elemental", impending := some (2, ManaCost.empty) }
  let gI0 : Game := insertObject afterDraw impDef4 me (.hand me)
  let impCard := (gI0.player me).hand.back!
  let gI1 : Game := (mustApply (mustApply gI0 me (.cast impCard)) me (.announceKicker true)).resolveTop
  let impPerm := (gI1.battlefield.filter (·.name == "Phase16 Impending Elemental"))[0]!.id
  let gI2 : Game := gI1.beginStep .end
  let impTrigStackId := gI2.stack.back!.objectId
  let impOnStackOk : Bool :=
    gI2.stack.size == 1 &&
    (gI2.object! impPerm).status.time == 2 &&
    !gI2.isCreature (gI2.object! impPerm)
  let gI3 : Game := gI2.removeAllCountersFrom impPerm (byPlayer := some me) (cause := some testCause)
  let preImpRes := gI3.events.size
  let gI4 : Game := gI3.resolveTop
  let impSlice := gI4.events.extract preImpRes gI4.events.size
  let impFizzledOk : Bool :=
    gI4.stack.isEmpty &&
    gI4.isCreature (gI4.object! impPerm) &&
    impSlice.any (fun e =>
      match e.change with
      | .rules (.stackObject (.removedOnResolution eo)) => eo.id == some impTrigStackId
      | _ => false) &&
    !impSlice.any (fun e =>
      match e.change with
      | .rules (.stackObject (.resolved ..)) => true
      | _ => false)
  mustHold16 "4a.queuedWentOnStack" queuedWentOnStack &&
  mustHold16 "4a.intervRemovedNoResolved" intervRemovedNoResolved &&
  mustHold16 "4b.nonIntervResolved" nonIntervResolved &&
  mustHold16 "4c.impOnStackOk" impOnStackOk &&
  mustHold16 "4c.impFizzledOk" impFizzledOk &&
  mustHold16 "4.replay" ([gQ1, gQ2, gN2, gI2, gI4].all (fun g =>
    Game.replayEvents g.events == g && allRulesEventsClassified g))

-- 5. CR 608.2b / 115.1c / 702.16b multi-slot & ability target legality.
#guard
  let pingActDef : CardDef := {
    bear with
    name := "Phase16 Prodigal Bear"
    activatedAbilities := #[{
      cost := {}
      effect := Effect.dealDamageToTargetCreature 1
    }]
  }
  let gT0 : Game := addPermanent (addPermanent afterDraw pingActDef me me) hero opp opp
  let pingerId := (gT0.battlefield.filter (·.name == "Phase16 Prodigal Bear"))[0]!.id
  let tgtHero := (gT0.battlefield.filter (·.name == hero.name))[0]!.id
  let gAct1 : Game := mustApply (mustApply gT0 me (.activate pingerId 0)) me (.target (.permanent tgtHero))
  let actStId := gAct1.stack.back!.objectId
  let (gAct2, _) : Game × ObjectId := gAct1.move tgtHero .exile none (cause := some testCause)
  let preActRes := gAct2.events.size
  let gAct3 : Game := gAct2.resolveTop
  let actFizzledOk : Bool :=
    gAct3.stack.isEmpty &&
    (gAct3.events.extract preActRes gAct3.events.size).any (fun e =>
      match e.change with
      | .rules (.stackObject (.removedOnResolution eo)) => eo.id == some actStId
      | _ => false) &&
    !(gAct3.events.extract preActRes gAct3.events.size).any (fun e =>
      match e.change with | .rules (.stackObject (.resolved ..)) => true | _ => false)

  let gTr0 : Game := addPermanent afterDraw hero opp opp
  let trTgt := (gTr0.battlefield.filter (·.name == hero.name))[0]!.id
  let blinkAb := TriggeredAbility.onThisAttack Effect.thisAttackBlinkNontoken
  let (gTr1, trObj) : Game × GameObject := gTr0.putStackAbility (gTr0.object! trTgt) me (triggeredAbility := some blinkAb)
  let gTr1 : Game := (gTr1.setStackEntryTargets trObj.id #[Target.permanent trTgt] #[]).markTargetsAnnounced trObj.id true
  let (gTr2, _) : Game × ObjectId := gTr1.move trTgt (.graveyard opp) none (cause := some testCause)
  let preTrRes := gTr2.events.size
  let gTr3 : Game := gTr2.resolveTop
  let trigFizzledOk : Bool :=
    gTr3.stack.isEmpty &&
    (gTr3.events.extract preTrRes gTr3.events.size).any (fun e =>
      match e.change with
      | .rules (.stackObject (.removedOnResolution eo)) => eo.id == some trObj.id
      | _ => false) &&
    !(gTr3.events.extract preTrRes gTr3.events.size).any (fun e =>
      match e.change with | .rules (.stackObject (.resolved ..)) => true | _ => false)

  let mealSpellDef : CardDef := {
    name := "Phase16 Meal"
    manaCost := ManaCost.empty
    types := #[.sorcery]
    spellEffect := some (Effect.plusOneUpToOneAndPlayerGainsLife 2)
  }
  let gSlt0 : Game := insertObject (addPermanent afterDraw bear me me) mealSpellDef me (.hand me)
  let sltBear := (gSlt0.battlefield.filter (·.name == bear.name))[0]!.id
  let mealH := (gSlt0.player me).hand.back!
  let gSlt1 : Game := mustApply gSlt0 me (.cast mealH)
  let gSlt2 : Game := mustApply gSlt1 me .decline
  let gSlt3 : Game := mustApply gSlt2 me (.target (.player opp))
  let mealSpellId := gSlt3.stack.back!.objectId
  let skippedRecordedOk : Bool :=
    gSlt3.stack.back!.skippedOptionalSlots == #[0] &&
    gSlt3.events.any (fun e =>
      match e.change with
      | .rules (.cast (.targeted sid #[Target.player p] #[] #[0])) => sid == mealSpellId && p == opp
      | _ => false)
  let gSlt4 : Game := gSlt3.resolveTop
  let swappedSlotsIllegal : Bool :=
    gSlt4.targetsAllIllegalForKind me .upToOneCreatureThenPlayer
      #[Target.player opp, Target.permanent sltBear] (skippedOptionalSlots := #[])
  let skipSlotOk : Bool :=
    skippedRecordedOk &&
    (gSlt4.player opp).life == 22 &&
    (gSlt4.object! sltBear).status.plusOnePlusOne == 0 &&
    swappedSlotsIllegal

  let redPingerDef : CardDef := {
    pingActDef with
    name := "Phase16 Red Pinger"
    manaCost := ⟨#[.colored .red]⟩
  }
  let protRedDef : CardDef := {
    hero with
    name := "Phase16 Red-Proof Hero"
    protectionFromColors := #[.red]
  }
  let gPr0 : Game := addPermanent (addPermanent afterDraw redPingerDef me me) protRedDef opp opp
  let rPingId := (gPr0.battlefield.filter (·.name == "Phase16 Red Pinger"))[0]!.id
  let protId := (gPr0.battlefield.filter (·.name == "Phase16 Red-Proof Hero"))[0]!.id
  let legalsFromRed := gPr0.legalTargetsForKind me .creature (some rPingId)
  let protSourceOk : Bool :=
    !legalsFromRed.contains (Target.permanent protId) &&
    legalsFromRed.contains (Target.permanent rPingId)

  mustHold16 "5a.actFizzledOk" actFizzledOk &&
  mustHold16 "5b.trigFizzledOk" trigFizzledOk &&
  mustHold16 "5c.skipSlotOk" skipSlotOk &&
  mustHold16 "5d.protSourceOk" protSourceOk &&
  mustHold16 "5.replay" ([gAct3, gTr3, gSlt4, gPr0].all (fun g =>
    Game.replayEvents g.events == g && allRulesEventsClassified g))

-- 6. CR 704.3 / 704.8 pre-704.5q SBA LKI & single-batch `chooseLegend` resuming `finishSbaSweep`.
#guard
  let tinyDef : CardDef := creature "Phase16 Tiny" ManaCost.empty #["Spirit"] 1 1
  let gL0 : Game := addPermanent afterDraw tinyDef me me
  let tinyId := (gL0.battlefield.filter (·.name == "Phase16 Tiny"))[0]!.id
  let gL0 : Game := (gL0.recordPutCounters tinyId .plusOnePlusOne 1 (some me) (cause := some testCause)).recordPutCounters
    tinyId .minusOneMinusOne 2 (some me) (cause := some testCause)
  let preLIdx := gL0.events.size
  let gL1 : Game := gL0.checkSBA
  let lkiCountersOk : Bool :=
    (gL1.events.extract preLIdx gL1.events.size).any (fun e =>
      match e.change with
      | .rules (.zone (.moved before _ .battlefield (.graveyard _) _ _ _ _)) =>
        before.id == some tinyId &&
        before.counters.contains (.plusOnePlusOne, 1) &&
        before.counters.contains (.minusOneMinusOne, 2)
      | _ => false)

  let zeroDef : CardDef := creature "Phase16 Zero" ManaCost.empty #["Germ"] 0 0
  let legDef : CardDef := { bear with name := "Phase16 Twin Legend", supertypes := #[.legendary] }
  let saga1Def : CardDef :=
    saga "Phase16 One-Chapter Saga" ManaCost.empty "" "I" #[chapter "I" "You gain 1 life." (Effect.gainLife 1)]
  let bareAuraDef : CardDef := aura "Phase16 Stray Aura" ManaCost.empty "Enchant creature"
  let noncreaArtDef : CardDef := { name := "Phase16 Pedestal", manaCost := ManaCost.empty, types := #[.artifact] }
  let (gB0, tokBf) : Game × GameObject := afterDraw.createToken me
    { creature "Phase16 Dead Token" ManaCost.empty #["Construct"] 1 1 with isToken := true }
    (cause := some testCause)
  let (gB0, tokGyId) : Game × ObjectId := gB0.move tokBf.id (.graveyard me) none (cause := some testCause)
  let gB0 : Game := addPermanent (addPermanent (addPermanent (addPermanent (addPermanent gB0
    zeroDef me me) legDef me me) legDef me me) bareAuraDef me me) noncreaArtDef me me
  let gB0 : Game := insertObject gB0 saga1Def me .battlefield (some me) { counters := #[(.lore, 1)] }
  let gB0 : Game := addPermanent gB0 equipDef16 me me
  let zeroId := (gB0.battlefield.filter (·.name == "Phase16 Zero"))[0]!.id
  let legs := (gB0.battlefield.filter (·.name == "Phase16 Twin Legend")).map (·.id)
  let legKeep := legs[0]!
  let legDrop := legs[1]!
  let sagaId := (gB0.battlefield.filter (·.name == "Phase16 One-Chapter Saga"))[0]!.id
  let auraId := (gB0.battlefield.filter (·.name == "Phase16 Stray Aura"))[0]!.id
  let pedId := (gB0.battlefield.filter (·.name == "Phase16 Pedestal"))[0]!.id
  let eqId6 := (gB0.battlefield.filter (·.name == "Phase16 Sword"))[0]!.id
  let gB0 : Game := gB0.record
    (GameEvent.attached gB0.turnNumber (gB0.snapshot (gB0.object! eqId6)) pedId (cause := testCause))
  let preSbaIdx := gB0.events.size
  let gBPaused : Game := gB0.checkSBA
  let pausedBatchOk : Bool :=
    (match gBPaused.pending with | .chooseLegend p "Phase16 Twin Legend" ids => p == me && ids.size == 2 | _ => false) &&
    gBPaused.currentBatch.isSome &&
    (gBPaused.findObject? sagaId).any (·.isOnBattlefield) &&
    (gBPaused.findObject? auraId).any (·.isOnBattlefield) &&
    (gBPaused.findObject? tokGyId).isSome &&
    (gBPaused.object! eqId6).attachedTo == some pedId
  let gBResumed : Game := mustApply gBPaused me (.keepLegend legKeep)
  let sbaSlice : Array GameEvent := gBResumed.events.extract preSbaIdx gBResumed.events.size
  let batchOfPred (pred : RulesEvent → Bool) : Option BatchId :=
    (sbaSlice.find? (fun e => match e.change with | .rules r => pred r | _ => false)).bind (·.batch)
  let bZero := batchOfPred (fun | .zone (.moved b _ .battlefield _ _ _ _ _) => b.id == some zeroId | _ => false)
  let bLeg := batchOfPred (fun | .zone (.moved b _ .battlefield _ _ _ _ _) => b.id == some legDrop | _ => false)
  let bTok := batchOfPred (fun | .zone (.ceasedToExist eo) => eo.id == some tokGyId | _ => false)
  let bSaga := batchOfPred (fun | .zone (.moved b _ .battlefield _ _ _ _ _) => b.id == some sagaId | _ => false)
  let bAura := batchOfPred (fun | .zone (.moved b _ .battlefield _ _ _ _ _) => b.id == some auraId | _ => false)
  let bEq := batchOfPred (fun | .permanent (.unattached eo h) => eo.id == some eqId6 && h == pedId | _ => false)
  let sameSingleBatchOk : Bool :=
    gBResumed.pending == Pending.none &&
    gBResumed.currentBatch.isNone &&
    (gBResumed.findObject? legKeep).any (·.isOnBattlefield) &&
    bZero.isSome &&
    bZero == bLeg && bZero == bTok && bZero == bSaga && bZero == bAura && bZero == bEq

  mustHold16 "6a.lkiCountersOk" lkiCountersOk &&
  mustHold16 "6b.pausedBatchOk" pausedBatchOk &&
  mustHold16 "6b.sameSingleBatchOk" sameSingleBatchOk &&
  mustHold16 "6.replay" ([gL1, gBPaused, gBResumed].all (fun g =>
    Game.replayEvents g.events == g && allRulesEventsClassified g))

-- 7. CR 111.8 token-flicker prohibition & simultaneous two-batch multi-target flicker.
#guard
  let (gF0, tokObj) : Game × GameObject := (addPermanent (addPermanent afterDraw bear me me) hero me me).createToken me
    { creature "Phase16 Ephemeral Token" ManaCost.empty #["Spirit"] 1 1 with isToken := true }
    (cause := some testCause)
  let bId := (gF0.battlefield.filter (·.name == bear.name))[0]!.id
  let hId := (gF0.battlefield.filter (·.name == hero.name))[0]!.id
  let tId := tokObj.id
  let preFIdx := gF0.events.size
  let gF1 : Game := gF0.flickerPermanents #[bId, hId, tId] (cause := some testCause)
  let fSlice : Array GameEvent := gF1.events.extract preFIdx gF1.events.size
  let exileBatches := fSlice.filterMap fun e =>
    match e.change with
    | .rules (.zone (.moved _ _ .battlefield .exile _ _ _ _)) => e.batch
    | _ => none
  let returnBatches := fSlice.filterMap fun e =>
    match e.change with
    | .rules (.zone (.moved _ _ .exile .battlefield _ _ _ _)) => e.batch
    | _ => none
  let exTokId := (gF1.objects.filter (fun o => o.name == "Phase16 Ephemeral Token" && o.zone == Zone.exile))[0]!.id
  let (gF1Stay, stayId) : Game × ObjectId := gF1.move exTokId .battlefield (some me) (cause := some testCause)
  let gF2 : Game := gF1Stay.checkSBA
  let flickerOk : Bool :=
    exileBatches.size == 3 &&
    exileBatches[0]! == exileBatches[1]! && exileBatches[1]! == exileBatches[2]! &&
    returnBatches.size == 2 &&
    returnBatches[0]! == returnBatches[1]! &&
    exileBatches[0]! != returnBatches[0]! &&
    gF1.battlefield.any (·.name == bear.name) &&
    gF1.battlefield.any (·.name == hero.name) &&
    !gF1.battlefield.any (·.name == "Phase16 Ephemeral Token") &&
    stayId == exTokId &&
    (gF1Stay.object! exTokId).zone == Zone.exile &&
    (gF2.findObject? exTokId).isNone

  mustHold16 "7.flickerOk" flickerOk &&
  mustHold16 "7.replay" ([gF1Stay, gF2].all (fun g =>
    Game.replayEvents g.events == g && allRulesEventsClassified g))

-- 8. CR 603.10 `.creatureCardsPutIntoYourGy` (`after.creature && !after.token`) & CR 701.17c `ZoneVerb.mill`.
#guard
  let animArtMoved := GameEvent.moved 1
    { id := some ⟨200⟩, controller := some me, owner := me, types := #[.artifact, .creature] }
    .battlefield (.graveyard me)
    (after := some { id := some ⟨201⟩, owner := me, zone := .graveyard me, types := #[.artifact] })
    (cause := testCause)
  let impCreaMoved := GameEvent.moved 1
    { id := some ⟨202⟩, controller := some me, owner := me, types := #[.enchantment] }
    .battlefield (.graveyard me)
    (after := some { id := some ⟨203⟩, owner := me, zone := .graveyard me, types := #[.enchantment, .creature] })
    (cause := testCause)
  let tokCreaMoved := GameEvent.moved 1
    { id := some ⟨204⟩, controller := some me, owner := me, types := #[.creature], token := true }
    .battlefield (.graveyard me)
    (after := some { id := some ⟨205⟩, owner := me, zone := .graveyard me, types := #[.creature], token := true })
    (cause := testCause)
  let gyTriggerOk : Bool :=
    !animArtMoved.matchesTrigger me none .creatureCardsPutIntoYourGy &&
    impCreaMoved.matchesTrigger me none .creatureCardsPutIntoYourGy &&
    !tokCreaMoved.matchesTrigger me none .creatureCardsPutIntoYourGy

  let gM0 : Game := quiet afterDraw
  let lib0 := (gM0.player me).library
  let cMillEx := lib0.back!
  let cSurveilGy := lib0[lib0.size - 2]!
  let gM1 : Game := gM0.createEffect
    (.replacement { id := { kind := .finalityCounterExile, object := some cMillEx },
                    affectedPlayer := me, kind := .exileInsteadOfGraveyard (some cMillEx) false })
    (cause := some testCause)
  let gM2 : Game := gM1.mill me 1 (cause := some testCause)
  let (gM3, _) : Game × ObjectId := gM2.move cSurveilGy (.graveyard me) none (verb := some .put) (cause := some testCause)
  let millVerbOk : Bool :=
    GameEvent.milled gM3.events gM3.turnNumber me == 1 &&
    (gM3.followMilledPublic? cMillEx).any (fun o => o.zone == Zone.exile) &&
    (gM3.followMilledPublic? cSurveilGy).isNone
  let gMReplay : Game := (afterDraw.createEffect
    (.replacement { id := { kind := .finalityCounterExile, object := some ((afterDraw.player me).library.back!) },
                    affectedPlayer := me,
                    kind := .exileInsteadOfGraveyard (some ((afterDraw.player me).library.back!)) false })
    (cause := some testCause)).mill me 1 (cause := some testCause)

  mustHold16 "8a.gyTriggerOk" gyTriggerOk &&
  mustHold16 "8b.millVerbOk" millVerbOk &&
  mustHold16 "8.replay" (Game.replayEvents gMReplay.events == gMReplay && allRulesEventsClassified gMReplay)

-- 9. CR 800.4a/h leave-game continuation handling (3-player).
#guard
  let (gSacLeft, gWheelLeft, gRepLeft, gTrigTgtLeft, step9LeaveOk) :=
    let threeCfg16 : StartConfig := {
      seats := #[
        { name := "Chandra", deck := testRedDeck },
        { name := "Nissa", deck := testGreenDeck },
        { name := "Liliana", deck := testRedDeck }
      ]
      format := .constructed
      seed := 16
      startingPlayer := some 0
    }
    let g3 : Game :=
      match Start.start threeCfg16 with
      | .ok g => keepOpeningHands g 12
      | .error e => panic! e
    let p0 : PlayerId := ⟨0⟩
    let p1 : PlayerId := ⟨1⟩
    let p2 : PlayerId := ⟨2⟩
    -- 9a. `.chooseSacrificeCreature`: `p0` already chose `b0`, then last remaining chooser `p1` concedes ->
    --     `finishChosenSacrifices` runs and sacrifices `b0`!
    let gS0 := addPermanent (addPermanent g3 bear p0 p0) hero p1 p1
    let b0 := (gS0.battlefield.filter (fun o => o.name == bear.name && o.controller == some p0))[0]!.id
    let gS1 := gS0.change (.pending (.chooseSacrificeCreature p1 #[b0] #[]))
    let gS2 := gS1.concede p1
    let sacFinishOk :=
      gS2.pending == .none &&
      !(gS2.findObject? b0).any (·.isOnBattlefield)
    -- 9b. Multi-player `FraChoice` (`.mayWheel 2 #[p2]` on `p1`): `p1` conceding advances prompt to `p2`!
    let gW1 := g3.change (.pending (.fraChoice p1 (.mayWheel 2 #[p2])))
    let gW2 := gW1.concede p1
    let wheelAdvOk := gW2.pending == .fraChoice p2 (.mayWheel 2 #[])
    -- 9c. `.chooseReplacement`: `p1` conceding while `Pending.chooseReplacement p1 ...` is open during `p0`'s effect
    --     resumes `pendingReplacement` (putting counters on `p0`'s Bear) instead of wiping `pendingReplacement := none`!
    let gR0 := addPermanent (addPermanent g3 bear p0 p0) samsonDef16 p1 p1
    let bR0 := (gR0.battlefield.filter (fun o => o.name == bear.name && o.controller == some p0))[0]!.id
    let docR1 := (gR0.battlefield.filter (·.name == "Phase16 Doc Samson"))[0]!.id
    let idD1 : ReplacementId := { kind := .multiplyCountersPut, object := some docR1 }
    let idD2 : ReplacementId := { kind := .extraCounterOnPermanents, object := some docR1, counterKind := some .plusOnePlusOne }
    let gR0 := (gR0.createEffect
      (.replacement { id := idD1, source := some docR1, controller := some p1, affectedPlayer := p1,
                      kind := .modifyCountersPut (some bR0) none 0 2 }) (cause := some testCause)).createEffect
      (.replacement { id := idD2, source := some docR1, controller := some p1, affectedPlayer := p1,
                      kind := .modifyCountersPut (some bR0) none 1 1 }) (cause := some testCause)
    -- Prompt `p1` on `pendingReplacement` for `addPlusOnePlusOneTo` on `bR0`:
    let gRP := gR0.promptChooseReplacement p1 #[idD1, idD2]
      (.addPlusOnePlusOneTo bR0 2 false (some p0) (some testCause))
    let gRLeft := gRP.concede p1
    let repResumeOk :=
      gRLeft.pending == .none &&
      gRLeft.pendingReplacement.isNone &&
      -- `p1`'s replacement effects left with `docR1`, and `pendingReplacement` resumed so `bR0` got its 2 `+1/+1` counters!
      (gRLeft.object! bR0).status.plusOnePlusOne == 2
    -- 9d. `.chooseTargets p1` for a triggered ability while `p0` has an unrelated `proposalCheckpoint` does NOT pop `p0`'s checkpoint,
    --     and when `p0` concedes during `p0`'s own spell `.chooseTargets p0`, `.clearProposalCheckpoint` is emitted ONCE (not twice)!
    let gC0 := (g3.change .saveProposalCheckpoint).change (.pending (.chooseTargets p1))
    let gC1 := gC0.concede p1
    let unrelatedCpKept := gC1.proposalCheckpoint.isSome
    let gC1Clean := gC1.change .clearProposalCheckpoint
    let pingDef9 : CardDef := {
      lightningBolt with
      name := "Phase16 Target Bolt"
      manaCost := ManaCost.empty
    }
    let gOwn0 := insertObject g3 pingDef9 p0 (.hand p0)
    let boltH := (gOwn0.player p0).hand.back!
    let gOwn1 := mustApply gOwn0 p0 (.cast boltH)
    let preConcedeIdx := gOwn1.events.size
    let gOwn2 := gOwn1.concede p0
    let clearCpCount :=
      (gOwn2.events.extract preConcedeIdx gOwn2.events.size).filter (fun e =>
        e.change == .engine .clearProposalCheckpoint) |>.size
    let cpLeaveOk := unrelatedCpKept && gOwn2.proposalCheckpoint.isNone && clearCpCount == 1
    -- 9e. `.discardTwo`: an opponent leaving the game before discarding (CR 800.4) does NOT increment `draws`!
    let gD0 := (insertObject (insertObject g3 bear p2 (.hand p2)) bear p2 (.hand p2)).continueDiscardTwo p0 #[p1, p2] 0
    let p0HandBefore := (gD0.player p0).hand.size
    let gD1 := gD0.concede p1
    let p2Bears := ((gD1.player p2).hand.filter (fun id => (gD1.object! id).name == bear.name)).extract 0 2
    let gD2 := mustApply gD1 p2 (.choosePermanents p2Bears)
    let gDLast0 := g3.change (.pending (.fraChoice p1 (.discardTwo p0 #[] 1)))
    let gDLast1 := gDLast0.concede p1
    let discardTwoLeaveOk :=
      gD1.pending == .fraChoice p2 (.discardTwo p0 #[] 0) &&
      (gD2.player p0).hand.size == p0HandBefore &&
      (gDLast1.player p0).hand.size == (g3.player p0).hand.size + 1 &&
      [gD1, gD2, gDLast1].all (fun g => Game.replayEvents g.events == g && allRulesEventsClassified g)
    (gS2, gW2, gRLeft, gC1Clean, sacFinishOk && wheelAdvOk && repResumeOk && cpLeaveOk && discardTwoLeaveOk &&
      Game.replayEvents gOwn2.events == gOwn2 && allRulesEventsClassified gOwn2)
  let step9AllOk :=
    step9LeaveOk &&
    [gSacLeft, gWheelLeft, gRepLeft, gTrigTgtLeft].all (fun g =>
      Game.replayEvents g.events == g && allRulesEventsClassified g)
  mustHold16 "step9AllOk" step9AllOk

-- 10. CR 702.131a/b/d `citysBlessing` / `enduringStory` batch evaluation & `Option BatchId` envelope fidelity.
#guard
  let (gAscendPerm, gAscendSpellStack, gAscendSpellRes, step10BatchAndDesigOk) :=
    -- 10a. Player controls 10 permanents without Ascend; turning a 10th face-down Ascend creature face-up
    --      (no `ZoneEvent.moved` / `ZoneEvent.created` entry!) grants `citysBlessing` in `Core.closeBatch`!
    let ascendMorphDef : CardDef := {
      bear with
      name := "Phase16 Ascend Morph"
      keywords := { ascend := true }
      morph := some ManaCost.empty
    }
    let gAs0 := (List.range 9).foldl (fun g _ => addPermanent g bear me me) afterDraw
    let gAs0 := addPermanent gAs0 ascendMorphDef me me
    let amId := (gAs0.battlefield.filter (·.name == "Phase16 Ascend Morph"))[0]!.id
    let gAs0 := setFaceDown gAs0 amId true
    let noBlessingWhileFaceDown := !(gAs0.player me).citysBlessing && gAs0.permanentCount me == 10
    let gAs1 := mustApply gAs0 me (.activate amId 0)
    let blessingOnTurnFaceUp := (gAs1.player me).citysBlessing
    -- 10b. Instant/sorcery with `ascend` while controlling 10 permanents: does NOT grant `citysBlessing` on stack,
    --      DOES grant `citysBlessing` when `resolveTop` resolves it (CR 702.131a)!
    let ascendSpellDef : CardDef := {
      name := "Phase16 Ascend Insight"
      manaCost := ManaCost.empty
      types := #[.sorcery]
      keywords := { ascend := true }
      spellEffect := some (Effect.draw 1)
    }
    let gSp0 := (List.range 10).foldl (fun g _ => addPermanent g bear me me) afterDraw
    let gSp0 := insertObject gSp0 ascendSpellDef me (.hand me)
    let spH := (gSp0.player me).hand.back!
    let gSpCast := mustApply gSp0 me (.cast spH)
    let notOnStackOk := !(gSpCast.player me).citysBlessing
    let gSpRes := gSpCast.resolveTop
    let onResOk := (gSpRes.player me).citysBlessing
    -- 10c. `Option BatchId` envelope fidelity:
    --      - Unbatched / proposed `GameEvent`s carry `batch == none`.
    --      - Unstamped `.engine` changes carry `batch == none`.
    --      - The very first committed rules batch of a fresh game (`Start.start`) carries `some ⟨0⟩` (`!= none`)!
    let unbatchedProposed : GameEvent := GameEvent.drew 1 me ⟨9⟩ 1 (cause := testCause)
    let unstampedEngine : GameEvent := GameEvent.engine 1 (.logMsg "note")
    let firstRulesBatch :=
      afterDraw.events.findSome? fun e =>
        match e.change with
        | .rules _ => e.batch
        | _ => none
    let batchEnvelopeOk :=
      unbatchedProposed.batch == none &&
      unstampedEngine.batch == none &&
      firstRulesBatch == some ⟨0⟩ &&
      (unbatchedProposed.withBatch ⟨0⟩).batch == some ⟨0⟩ &&
      unbatchedProposed.batch != (unbatchedProposed.withBatch ⟨0⟩).batch
    (gAs1, gSpCast, gSpRes,
     noBlessingWhileFaceDown && blessingOnTurnFaceUp && notOnStackOk && onResOk && batchEnvelopeOk)
  let step10AllOk :=
    step10BatchAndDesigOk &&
    [gAscendPerm, gAscendSpellStack, gAscendSpellRes].all (fun g =>
      Game.replayEvents g.events == g && allRulesEventsClassified g)
  mustHold16 "step10AllOk" step10AllOk

end Phase16EventAlignment

/-! ### Phase 17 Event Alignment Isolation Tests (CR 500.4–5 / 514.3 / 603.3c–d / 603.4 / 608.2a–c / 608.3b–c,f / 610.3 / 611.2a / 704.3 / 704.5d–e,j / 707.10 / 707.12 / 733.1 / 800.4)

1. Nested-batch `currentBatch` replay & shared `EffectId` fidelity across `Pending.chooseReplacement`.
2. CR 733.1 `reverseToProposalCheckpoint?` filtering of `.waitingTriggers` and `DelayedTriggerEvent.consumed`.
3. Pause-safe continuations (`putShadowCounter`, `applyPut` `.asArtifact`, `untapUnblockable`, `finishPlaceSearched`, `factOrFictionGyLoop`, `castFreeCopy`, `pass`/`concede` `consecutivePasses` & `pendingPriority`) and `0`-counter log parity.
4. CR 603.3c–d modal trigger stack announcement (`chooseUpToXModes`, `stackHydeMode`, `oneUnused` / `oneUnusedThisTurn`), mandatory target removal (`putQueuedTrigger`), CR 707.10 stack-copy mode preservation, and CR 113.7a LKI resolution.
5. CR 603.4 / 608.2a intervening-`"if"` & trigger checks (`gingerbrute`, `obAngel`, `tamiyoStun`, `windcragSiege`, `copySelfNonlegendary`).
6. CR 704.5d–e / 707.10 / 707.12 card & permanent spell copy lifecycle (`.uldarosCopies`), CR 608.2b / 608.3b–c / 303.4a,c Aura resolution (`secretInvasion`, hexproof fizzle, copy cease), and multi-target retargeting validation.
7. CR 704.3 / 704.5j recursive `keepLegend` `preBf`, CR 610.3 post-departure `linkedExile` separate batch, CR 303.4f two-pass simultaneous entry Aura `preBattlefield` check (`placeSearchedBatch` & `returnLinkedExileLoop`), and *Worlds Within Worlds* separate sequential CR 608.2c batches.
8. CR 800.4 `mayThen` departure decline & pregame concessions (`declareMulligan` & `.mayBeginOnBattlefield`), silent cleanup `finishPostSbaCleanup` routing through `beginTurn`, and step/phase `EffectDuration` expiry (`CR 500.4–5 / 511.2 / 611.2a`). -/
section Phase17EventAlignment

private def samsonDef17 : CardDef :=
  { bear with name := "Phase17 Doc Samson", staticAbilities := #[.extraCounterOnPermanents] }

private def misterHydeDef17 : CardDef :=
  creature "Mister Hyde, Monster Within" { symbols := #[.generic 2, .colored .green] } #["Human", "Villain"] 2 2
    (supertypes := #[.legendary])
    (oracleText := "At the beginning of your upkeep, choose one —\n• Put a +1/+1 counter on Mister Hyde.\n• Remove a counter from a creature you control. If you do, draw a card.")

private def wreckingCrewDef17 : CardDef :=
  creature "The Ruinous Wrecking Crew" { symbols := #[.x, .colored .black, .colored .red] } #["Human", "Villain"] 2 2
    (supertypes := #[.legendary])
    (oracleText := "The Ruinous Wrecking Crew enters with X +1/+1 counters on it.\nWhen The Ruinous Wrecking Crew enters, choose up to X —\n• Discard a card, then draw a card.\n• Target opponent loses 2 life.\n• Destroy target token.\n• Each player sacrifices a creature of their choice.")

private def windcragDef17 : CardDef :=
  enchantment "Windcrag Siege" ManaCost.empty
    "As this enchantment enters, choose Mardu or Jeskai.\n• Mardu — If a creature attacking causes a triggered ability of a permanent you control to trigger, that ability triggers an additional time.\n• Jeskai — At the beginning of your upkeep, create a 1/1 red Goblin creature token. It gains lifelink and haste until end of turn."

private def secretInvasionDef17 : CardDef :=
  aura "Secret Invasion" ManaCost.empty "Enchant creature you control"

private def worldsDef17 : CardDef :=
  sorcery "Worlds Within Worlds" ManaCost.empty
    "Exile all creatures. Each player may put any number of creature cards from their hand onto the battlefield. Then put all cards exiled this way into their owners' hands. Exile Worlds Within Worlds."

private def mustHold17 (label : String) (ok : Bool) : Bool :=
  if ok then true else panic! s!"Phase 17 guard failed: {label}"

-- 1. Nested-batch `currentBatch` replay & shared `EffectId` fidelity across `Pending.chooseReplacement`.
#guard
  let gN0 : Game := addPermanent (addPermanent afterDraw bear me me) samsonDef17 me me
  let bId := (gN0.battlefield.filter (·.name == bear.name))[0]!.id
  let docId := (gN0.battlefield.filter (·.name == "Phase17 Doc Samson"))[0]!.id
  let idDocPlus : ReplacementId := { kind := .extraCounterOnPermanents, object := some docId, counterKind := some .plusOnePlusOne }
  let idCntDbl : ReplacementId := { kind := .multiplyCountersPut, object := some bId }
  let gN0 : Game := gN0.createEffect
    (.replacement { id := idCntDbl, source := some bId, controller := some me, affectedPlayer := me,
                    kind := .modifyCountersPut none (some .plusOnePlusOne) 0 2 }) (cause := some testCause)
  let gOuterPaused : Game :=
    gN0.withBatch none fun g =>
      g.addPlusOnePlusOneTo (g.object! bId) 1 (cause := some testCause)
  let outerOk : Bool :=
    match gOuterPaused.currentBatch, gOuterPaused.pending with
    | some (_, none), .chooseReplacement p cs => p == me && cs.size == 2
    | _, _ => false
  let nextEffBefore := gN0.nextEffectId
  let gNestedPaused : Game :=
    gN0.withBatch none fun g =>
      g.withBatch (some (.oneShotEffect none (some docId) (some me))) fun g =>
        let g := g.pumpPermanent (g.object! bId) 2 2
        g.addPlusOnePlusOneTo (g.object! bId) 1
  let mintedEffId : EffectId := ⟨nextEffBefore⟩
  let innerBatchOk : Bool :=
    (match gNestedPaused.currentBatch with
     | some (_, some (.oneShotEffect (some eid) (some s) (some c))) =>
       eid == mintedEffId && s == docId && c == me
     | _ => false) &&
    gNestedPaused.events.any (fun e =>
      match e.change, e.cause? with
      | .rules (.continuousEffect (.created _ _)), some (.oneShotEffect (some eid) (some s) (some c)) =>
        eid == mintedEffId && s == docId && c == me
      | _, _ => false)
  let gNestedResumed : Game := mustApply gNestedPaused me (.chooseReplacement idDocPlus)
  let resumedOk : Bool :=
    gNestedResumed.pending == .none &&
    gNestedResumed.currentBatch.isNone &&
    (gNestedResumed.object! bId).status.plusOnePlusOne == 4

  mustHold17 "1.outerOk" outerOk &&
  mustHold17 "1.innerBatchOk" innerBatchOk &&
  mustHold17 "1.resumedOk" resumedOk &&
  mustHold17 "1.replay" ([gOuterPaused, gNestedPaused, gNestedResumed].all (fun g =>
    Game.replayEvents g.events == g && allRulesEventsClassified g))

-- 2. CR 733.1 `reverseToProposalCheckpoint?` filtering of `.waitingTriggers` & `DelayedTriggerEvent.consumed`.
#guard
  let deathWatcherAb : TriggeredAbility :=
    .triggered .creatureYouControlDies
      { resolution := .gainLife (.fixed 2), phrase := "You gain 2 life" }
      {}
  let watcherDef : CardDef :=
    { bear with name := "Phase17 Watcher", triggeredAbilities := #[deathWatcherAb] }
  let gR0 : Game := addPermanent (addPermanent afterDraw watcherDef me me) hero me me
  let heroId := (gR0.battlefield.filter (·.name == hero.name))[0]!.id
  let dtSpec : DelayedTrigger := {
    controller := me
    kind := .copyNextInstantSorceryThisTurn
    cause := testCause
  }
  let gR0 : Game := gR0.record (GameEvent.delayedTriggerCreated gR0.turnNumber dtSpec)
  let gCkpt : Game := gR0.change .saveProposalCheckpoint
  let gAct0 : Game :=
    gCkpt.withProposalAction .costAction fun g =>
      let g := g.moveToOwnerGraveyard (g.object! heroId) "dies" (verb := some .sacrifice) (cause := some testCause)
      let g := g.change (.waitingTriggers g.waitingTriggers)
      g.record (GameEvent.delayedTriggerConsumed g.turnNumber dtSpec)
  let topLib := (gAct0.player me).library.back!
  let gAct1 : Game :=
    gAct0.withProposalAction .manaAbility fun g =>
      let g := g.record (GameEvent.revealed g.turnNumber me #[topLib] (cause := some (.gameRule .spellCast)))
      g.addMana me (.colored .red) (cause := some (.gameRule .spellCast))
  let preRevHasTrigAndConsumed : Bool :=
    gAct1.waitingTriggers.size == 1 && gAct1.delayedTriggers.isEmpty
  let gRev : Game :=
    match gAct1.reverseToProposalCheckpoint? with
    | .ok g => g
    | .error e => panic! e
  let revFilteredOk : Bool :=
    preRevHasTrigAndConsumed &&
    (gRev.findObject? heroId).any (·.isOnBattlefield) &&
    (gRev.player me).manaPool.red == 1 &&
    gRev.waitingTriggers.isEmpty &&
    gRev.delayedTriggers.contains dtSpec

  mustHold17 "2.revFilteredOk" revFilteredOk &&
  mustHold17 "2.replay" ([gAct1, gRev].all (fun g =>
    Game.replayEvents g.events == g && allRulesEventsClassified g))

-- 3. Pause-safe continuations & `0`-counter log parity.
#guard
  -- 3a. `putShadowCounter` across `Pending.chooseReplacement` and `0`-counter replacement guard.
  let gSh0 : Game := addPermanent (addPermanent afterDraw bear me me) samsonDef17 me me
  let shBear := (gSh0.battlefield.filter (·.name == bear.name))[0]!.id
  let docSh := (gSh0.battlefield.filter (·.name == "Phase17 Doc Samson"))[0]!.id
  let idDocSh : ReplacementId := { kind := .extraCounterOnPermanents, object := some docSh, counterKind := some .shadow }
  let idDblSh : ReplacementId := { kind := .multiplyCountersPut, object := some shBear }
  let gSh1 : Game := gSh0.createEffect
    (.replacement { id := idDblSh, source := some shBear, controller := some me, affectedPlayer := me,
                    kind := .modifyCountersPut (some shBear) (some .shadow) 0 2 }) (cause := some testCause)
  let logBeforeSh := gSh1.log.size
  let gShPaused : Game := gSh1.putShadowCounter (gSh1.object! shBear)
  let shPausedOk : Bool :=
    (match gShPaused.pending with | .chooseReplacement p cs => p == me && cs.size == 2 | _ => false) &&
    !(gShPaused.currentSubtypes (gShPaused.object! shBear)).contains .wraith &&
    !(gShPaused.log.extract logBeforeSh gShPaused.log.size).any (·.contains "shadow counter")
  let gShDone : Game := mustApply gShPaused me (.chooseReplacement idDocSh)
  let shDoneOk : Bool :=
    gShDone.pending == .none &&
    (gShDone.object! shBear).status.counterCount .shadow == 4 &&
    (gShDone.currentSubtypes (gShDone.object! shBear)).contains .wraith &&
    (gShDone.log.extract logBeforeSh gShDone.log.size).any (·.contains "gets a shadow counter")

  -- `0`-counter replacement guard for both `putShadowCounter` and `addPlusOnePlusOneTo`:
  let gZero0 : Game := addPermanent afterDraw bear me me
  let zBear := (gZero0.battlefield.filter (·.name == bear.name))[0]!.id
  let idZero : ReplacementId := { kind := .multiplyCountersPut, object := some zBear }
  let gZero1 : Game := gZero0.createEffect
    (.replacement { id := idZero, source := some zBear, controller := some me, affectedPlayer := me,
                    kind := .modifyCountersPut (some zBear) none 0 0 }) (cause := some testCause)
  let logBeforeZ := gZero1.log.size
  let gZero2 : Game := (gZero1.putShadowCounter (gZero1.object! zBear)).addPlusOnePlusOneTo (gZero1.object! zBear) 2 (cause := some testCause)
  let zeroCounterGuardOk : Bool :=
    (gZero2.object! zBear).status.plusOnePlusOne == 0 &&
    (gZero2.object! zBear).status.counterCount .shadow == 0 &&
    !(gZero2.currentSubtypes (gZero2.object! zBear)).contains .wraith &&
    gZero2.log.size == logBeforeZ

  -- 3b. `applyPut` (`.source, .asArtifact, .none`) across `Pending.chooseReplacement` & exile redirect.
  let oddHeroDef : CardDef := { hero with name := "Phase17 Odd Hero", asEntersChooseOddEven := true }
  let gArt0 : Game := insertObject afterDraw oddHeroDef me (.graveyard me)
  let gyHero := (gArt0.player me).graveyard.back!
  let logBeforeArt := gArt0.log.size
  let gArtPaused : Game := gArt0.applyPut me (.onEnterDraw 1) (some gyHero) #[] .source .asArtifact .none
  let artPausedOk : Bool :=
    (match gArtPaused.pending with | .chooseReplacement p _ => p == me | _ => false) &&
    !(gArtPaused.log.extract logBeforeArt gArtPaused.log.size).any (·.contains "returns as an artifact")
  let gArtDone : Game := mustApply gArtPaused me (.chooseMode 0)
  let enteredHero := (gArtDone.battlefield.filter (·.name == "Phase17 Odd Hero"))[0]!
  let artDoneOk : Bool :=
    gArtDone.pending == .none &&
    (gArtDone.types enteredHero).contains .artifact &&
    (gArtDone.log.extract logBeforeArt gArtDone.log.size).any (·.contains "returns as an artifact")

  -- 3c. `applyFra` `.untapUnblockable` across stun-counter `Pending.chooseReplacement`.
  let gUU0 : Game := addPermanent (addPermanent afterDraw bear me me) hero me me
  let uuBear := (gUU0.battlefield.filter (·.name == bear.name))[0]!.id
  let uuHero := (gUU0.battlefield.filter (·.name == hero.name))[0]!.id
  let idStunSelf : ReplacementId := { kind := .stunCounterUntap, object := some uuBear }
  let idStunExt : ReplacementId := { kind := .stunCounterUntap, object := some uuHero }
  let gUU1 : Game :=
    ((gUU0.becomeTapped (gUU0.object! uuBear) (cause := some testCause)).recordPutCounters
      uuBear .stun 1 (some me) (cause := some testCause)).createEffect
      (.replacement { id := idStunExt, source := some uuHero, controller := some me, affectedPlayer := me,
                      kind := .stunCounterUntap uuBear }) (cause := some testCause)
  let uuEff : Effect := { targeting := .of .creature, resolution := .untapUnblockable }
  let gUUPaused : Game := gUU1.applyFra me uuEff .untapUnblockable #[Target.permanent uuBear] (some uuHero)
  let uuPausedOk : Bool :=
    (match gUUPaused.pending with | .chooseReplacement p cs => p == me && cs.size == 2 | _ => false) &&
    !gUUPaused.hasKeyword (gUUPaused.object! uuBear) (·.cantBeBlocked)
  let gUUDone : Game := mustApply gUUPaused me (.chooseReplacement idStunSelf)
  let uuDoneOk : Bool :=
    gUUDone.pending == .none &&
    (gUUDone.object! uuBear).status.tapped &&
    (gUUDone.object! uuBear).status.stun == 0 &&
    gUUDone.hasKeyword (gUUDone.object! uuBear) (·.cantBeBlocked)

  -- 3d. `factOrFictionGyLoop` across competing graveyard-exile replacements.
  let gFoF0 : Game := insertObject (insertObject afterDraw bear me (.library me)) hero me (.library me)
  let libFoF := (gFoF0.player me).library
  let fofC1 := libFoF.back!
  let fofC2 := libFoF[libFoF.size - 2]!
  let idExA : ReplacementId := { kind := .finalityCounterExile, object := some fofC1 }
  let idExB : ReplacementId := { kind := .exileOppDeath, object := some fofC1 }
  let gFoF1 : Game := (gFoF0.createEffect
    (.replacement { id := idExA, affectedPlayer := me, kind := .exileInsteadOfGraveyard (some fofC1) false })
    (cause := some testCause)).createEffect
    (.replacement { id := idExB, affectedPlayer := me, kind := .exileInsteadOfGraveyard (some fofC1) false })
    (cause := some testCause)
  let gFoFPaused : Game := gFoF1.factOrFictionGyLoop me #[fofC1, fofC2]
  let fofPausedOk : Bool :=
    (match gFoFPaused.pending with | .chooseReplacement p cs => p == me && cs.size == 2 | _ => false) &&
    (gFoFPaused.object! fofC2).zone == .library me
  let gFoFDone : Game := mustApply gFoFPaused me (.chooseReplacement idExA)
  let fofDoneOk : Bool :=
    gFoFDone.pending == .none &&
    (gFoFDone.followMovedToZone? fofC1 (· == .exile)).isSome &&
    (gFoFDone.followMovedToZone? fofC2 (· == .graveyard me)).isSome

  -- 3e. `PriorityActions.pass` resets `consecutivePasses` before `resolveTop`.
  let instDrawDef : CardDef := {
    name := "Phase17 Quick Draw"
    manaCost := ManaCost.empty
    types := #[.instant]
    spellEffect := some (Effect.draw 1)
  }
  let gPass0 : Game := insertObject afterDraw instDrawDef me (.hand me)
  let qdId := (gPass0.player me).hand.back!
  let gPass1 : Game := mustApply gPass0 me (.cast qdId)
  let gPass2 : Game := mustApply (mustApply gPass1 me .pass) opp .pass
  let passResetOk : Bool := gPass2.consecutivePasses == 0 && gPass2.stack.isEmpty

  mustHold17 "3a.shPausedOk" shPausedOk &&
  mustHold17 "3a.shDoneOk" shDoneOk &&
  mustHold17 "3a.zeroCounterGuardOk" zeroCounterGuardOk &&
  mustHold17 "3b.artPausedOk" artPausedOk &&
  mustHold17 "3b.artDoneOk" artDoneOk &&
  mustHold17 "3c.uuPausedOk" uuPausedOk &&
  mustHold17 "3c.uuDoneOk" uuDoneOk &&
  mustHold17 "3d.fofPausedOk" fofPausedOk &&
  mustHold17 "3d.fofDoneOk" fofDoneOk &&
  mustHold17 "3e.passResetOk" passResetOk &&
  mustHold17 "3.replay" ([gShPaused, gShDone, gZero2, gArtPaused, gArtDone, gUUPaused, gUUDone, gFoFPaused, gFoFDone, gPass2].all (fun g =>
    Game.replayEvents g.events == g && allRulesEventsClassified g))

-- 4. CR 603.3c–d modal trigger stack announcement, mandatory target removal, stack-copy mode preservation, & LKI resolution.
#guard
  -- 4a. Mandatory-target non-FRA triggered ability with zero legal targets is removed in `putQueuedTrigger` (CR 603.3d).
  let mandTargetAb : TriggeredAbility :=
    .triggered .youGainLife
      { targeting := .of .oppCreature, resolution := .destroy .target, phrase := "Destroy target creature an opponent controls." }
      {}
  let mandWatcherDef : CardDef := { bear with name := "Phase17 Mandatory Watcher", triggeredAbilities := #[mandTargetAb] }
  let gMand0 : Game := addPermanent afterDraw mandWatcherDef me me
  let logBeforeMand := gMand0.log.size
  let gMand1 : Game := (gMand0.gainLife me 1 (cause := some testCause)).receivePriority me
  let mandRemovedOk : Bool :=
    gMand1.stack.isEmpty &&
    gMand1.waitingTriggers.isEmpty &&
    (gMand1.log.extract logBeforeMand gMand1.log.size).any (·.contains "no legal target")

  -- 4b. `.oneUnused` (`gollumMode`): announces mode on stack placement, copies preserve announced mode (CR 707.10),
  --     resolves using LKI even after source left `.battlefield` (CR 113.7a), and once all 3 modes are chosen,
  --     a 4th placement removes the ability with `noLegalMode` and WITHOUT `StackObjectEvent.resolved`!
  let gollumTrigAb : TriggeredAbility := .triggered .youGainLife (Effect.ofTrigger .gollumMode) {}
  let gollumTestDef : CardDef := { bear with name := "Phase17 Gollum Test", triggeredAbilities := #[gollumTrigAb] }
  let gGol0 : Game := addPermanent afterDraw gollumTestDef me me
  let golId := (gGol0.battlefield.filter (·.name == "Phase17 Gollum Test"))[0]!.id
  -- Trigger 1: choose mode 2 (draw a card), copy stack ability, destroy source before resolving, then resolve both!
  let gGolStack0 : Game := gGol0.putTriggeredAbilityOnStack me (gGol0.object! golId) gollumTrigAb "triggers" (eventCause := some testCause)
  let golPromptedOnStack : Bool :=
    match gGolStack0.pending with
    | .fraChoice p (.stackTriggerUnusedMode _ (some sid) avail true) => p == me && sid == golId && avail == #[0, 1, 2]
    | _ => false
  let gGolChosen0 : Game := mustApply gGolStack0 me (.chooseMode 2)
  let stackAbId := gGolChosen0.stack.back!.objectId
  let announcedOnStackOk : Bool := gGolChosen0.chosenModesOf (gGolChosen0.object! stackAbId) == #[2]
  let gGolCopied : Game := gGolChosen0.copyStackAbility (gGolChosen0.object! stackAbId) me
  let copyAbId := gGolCopied.stack.back!.objectId
  let copyPreservedModeOk : Bool := gGolCopied.chosenModesOf (gGolCopied.object! copyAbId) == #[2]
  -- Destroy `golId` before resolving either the copy or the original ability (CR 113.7a LKI):
  let gGolSrcDead : Game := gGolCopied.moveToOwnerGraveyard (gGolCopied.object! golId) "dies" (verb := some .destroy) (cause := some testCause)
  let handBeforeGol := (gGolSrcDead.player me).hand.size
  let gGolResBoth : Game := gGolSrcDead.resolveTop.resolveTop
  let golLkiAndCopyResOk : Bool := (gGolResBoth.player me).hand.size == handBeforeGol + 2

  -- Re-add a fresh source, choose modes 0, 1, and 2 across 3 placements, then verify a 4th placement is removed via `noLegalMode` without `resolved`:
  let gEx0 : Game := addPermanent afterDraw gollumTestDef me me
  let exSrc := (gEx0.battlefield.filter (·.name == "Phase17 Gollum Test"))[0]!.id
  let placeAndChoose (g : Game) (m : Nat) : Game :=
    let g1 := g.putTriggeredAbilityOnStack me (g.object! exSrc) gollumTrigAb "triggers" (eventCause := some testCause)
    (mustApply g1 me (.chooseMode m)).resolveTop
  let gEx3 : Game := placeAndChoose (placeAndChoose (placeAndChoose gEx0 0) 1) 2
  let preFourthIdx := gEx3.events.size
  let gEx4 : Game := gEx3.putTriggeredAbilityOnStack me (gEx3.object! exSrc) gollumTrigAb "triggers" (eventCause := some testCause)
  let fourthSlice := gEx4.events.extract preFourthIdx gEx4.events.size
  let fourthNoLegalModeOk : Bool :=
    gEx4.stack.isEmpty &&
    fourthSlice.any (fun e => e.cause? == some (.gameRule .noLegalMode)) &&
    !fourthSlice.any (fun e => match e.change with | .rules (.stackObject (.resolved ..)) => true | _ => false)

  -- 4c. *Mister Hyde* (`.stackHydeMode`) and *The Ruinous Wrecking Crew* (`.upToTriggerModes`):
  let gHyde0 : Game := addPermanent afterDraw misterHydeDef17 me me
  let hydeId := (gHyde0.battlefield.filter (·.name == misterHydeDef17.name))[0]!.id
  let hydeAb := misterHydeDef17.triggeredAbilities[0]!
  let gHydeStack : Game := gHyde0.putTriggeredAbilityOnStack me (gHyde0.object! hydeId) hydeAb "combat" (eventCause := some testCause)
  let hydePromptOk : Bool := gHydeStack.pending == .fraChoice me (.stackHydeMode gHydeStack.stack.back!.objectId)
  let gHydeMode0 : Game := (mustApply gHydeStack me (.chooseMode 0)).resolveTop
  let hydeResolvedOk : Bool := (gHydeMode0.object! hydeId).status.plusOnePlusOne == 1

  let gCrew0 : Game := insertObject afterDraw wreckingCrewDef17 me (.hand me)
  let crewHandId := (gCrew0.player me).hand.back!
  let gCrewMana : Game := ((gCrew0.addMana me (.colored .black) 2 (cause := some testCause)).addMana
    me (.colored .red) 2 (cause := some testCause))
  let gCrewCast : Game := mustApply (mustApply (mustApply gCrewMana me (.cast crewHandId)) me (.chooseX 2)) me .pay
  let gCrewEntered : Game := gCrewCast.resolveTop.receivePriority me
  let crewPromptOnStackOk : Bool :=
    match gCrewEntered.pending with
    | .fraChoice p (.upToTriggerModes _ 2 #[]) => p == me
    | _ => false
  let oppLifeBefore := (gCrewEntered.player opp).life
  -- Mode 1 is `"Target opponent loses 2 life"`, then decline 2nd mode (`choose up to X`) and target `opp`:
  let gCrewMode1 : Game := mustApply (mustApply (mustApply gCrewEntered me (.chooseMode 1)) me .decline) me (.target (.player opp))
  let gCrewResolved : Game := gCrewMode1.resolveTop
  let crewResolvedOk : Bool := (gCrewResolved.player opp).life == oppLifeBefore - 2

  mustHold17 "4a.mandRemovedOk" mandRemovedOk &&
  mustHold17 "4b.golPromptedOnStack" golPromptedOnStack &&
  mustHold17 "4b.announcedOnStackOk" announcedOnStackOk &&
  mustHold17 "4b.copyPreservedModeOk" copyPreservedModeOk &&
  mustHold17 "4b.golLkiAndCopyResOk" golLkiAndCopyResOk &&
  mustHold17 "4b.fourthNoLegalModeOk" fourthNoLegalModeOk &&
  mustHold17 "4c.hydePromptOk" hydePromptOk &&
  mustHold17 "4c.hydeResolvedOk" hydeResolvedOk &&
  mustHold17 "4c.crewPromptOnStackOk" crewPromptOnStackOk &&
  mustHold17 "4c.crewResolvedOk" crewResolvedOk &&
  mustHold17 "4.replay" ([gMand1, gGolChosen0, gGolCopied, gGolResBoth, gEx4, gHydeMode0, gCrewEntered, gCrewResolved].all (fun g =>
    Game.replayEvents g.events == g && allRulesEventsClassified g))

-- 5. CR 603.4 / 608.2a intervening-`"if"` & trigger checks (`gingerbrute`, `obAngel`, `tamiyoStun`, `windcragSiege`, `copySelfNonlegendary`).
#guard
  -- 5a. `FrcEffect.gingerbrute`: requires `isMonarch` on both trigger and resolution.
  let gingerAb : TriggeredAbility := TriggeredAbility.fra .yourUpkeep "At the beginning of your upkeep, if you're the monarch, create a Gingerbrute token." (.frc .gingerbrute)
  let gingerSrcDef : CardDef := { bear with name := "Phase17 Ginger Court", triggeredAbilities := #[gingerAb] }
  let gGin0 : Game := addPermanent afterDraw gingerSrcDef me me
  let gGinNoMonarch : Game := gGin0.record (GameEvent.stepped gGin0.turnNumber .upkeep me)
  let gGinMonarch0 : Game := gGin0.becomeMonarch me
  let gGinTrig : Game := (gGinMonarch0.record (GameEvent.stepped gGinMonarch0.turnNumber .upkeep me)).receivePriority me
  let gGinLostMonarch : Game := (gGinTrig.becomeMonarch opp).resolveTop
  let gGinKeptMonarch : Game := gGinTrig.resolveTop
  let gingerOk : Bool :=
    gGinNoMonarch.waitingTriggers.isEmpty &&
    gGinTrig.stack.size == 1 &&
    !(gGinLostMonarch.permanentsOf me).any (·.name == "Gingerbrute") &&
    gGinLostMonarch.events.any (fun e => match e.change with | .rules (.stackObject (.removedOnResolution ..)) => true | _ => false) &&
    (gGinKeptMonarch.permanentsOf me).any (·.name == "Gingerbrute")

  -- 5b. `FrcEffect.obAngel`: requires `loggedLifeGained > 0` on trigger and resolution.
  let obAb : TriggeredAbility := TriggeredAbility.fra .eachEndStep "At the beginning of each end step, if you gained life this turn, ..." (.frc .obAngel)
  let obSrcDef : CardDef := { bear with name := "Phase17 Angelic Watcher", triggeredAbilities := #[obAb] }
  let gOb0 : Game := addPermanent afterDraw obSrcDef me me
  let gObNoLife : Game := gOb0.record (GameEvent.stepped gOb0.turnNumber .end me)
  let gObLife : Game := (gOb0.gainLife me 1 (cause := some testCause)).record (GameEvent.stepped gOb0.turnNumber .end me)
  let obOk : Bool := gObNoLife.waitingTriggers.isEmpty && gObLife.waitingTriggers.size == 1

  -- 5c. `FrcEffect.tamiyoStun`: triggers ONLY if `me` is monarch at combat damage, does NOT recheck `isMonarch` at resolution,
  --     and taps + stuns ALL creatures that dealt combat damage to `me` in that batch!
  let tamAb : TriggeredAbility := TriggeredAbility.fra .combatDamageToYou "Whenever one or more creatures deal combat damage to you, if you were the monarch..." (.frc .tamiyoStun)
  let tamSrcDef : CardDef := { bear with name := "Phase17 Tamiyo Watcher", triggeredAbilities := #[tamAb] }
  let gTam0 : Game := addPermanent (addPermanent (addPermanent afterDraw tamSrcDef me me) bear opp opp) hero opp opp
  let oppBear := (gTam0.battlefield.filter (fun o => o.name == bear.name && o.controller == some opp))[0]!.id
  let oppHero := (gTam0.battlefield.filter (fun o => o.name == hero.name && o.controller == some opp))[0]!.id
  let combatCause : EventCause := .turnBased (.dealCombatDamage false)
  let dealCombatBatch (g : Game) : Game :=
    g.withBatch (some combatCause) fun (g : Game) =>
      let g : Game := g.record (GameEvent.damagedPlayer g.turnNumber
        (g.snapshotDamageSource (g.object! oppBear)) me 2 true (cause := combatCause))
      g.record (GameEvent.damagedPlayer g.turnNumber
        (g.snapshotDamageSource (g.object! oppHero)) me 2 true (cause := combatCause))
  let gTamNoMonarch : Game := dealCombatBatch gTam0
  let gTamMonarch : Game := (dealCombatBatch (gTam0.becomeMonarch me)).receivePriority me
  -- Even after `opp` steals the monarchy before `tamiyoStun` resolves, `tamiyoStun` STILL resolves and stuns BOTH `oppBear` and `oppHero`!
  let gTamRes : Game := (gTamMonarch.becomeMonarch opp).resolveTop
  let tamiyoOk : Bool :=
    gTamNoMonarch.waitingTriggers.isEmpty &&
    gTamMonarch.stack.size == 1 &&
    (gTamRes.object! oppBear).status.tapped && (gTamRes.object! oppBear).status.stun == 1 &&
    (gTamRes.object! oppHero).status.tapped && (gTamRes.object! oppHero).status.stun == 1

  -- 5d. *Windcrag Siege* (`windcragDef17`): `"Mardu"` does not trigger upkeep Goblin; `"Jeskai"` does!
  let putSiegeWithMode (modeIdx : Nat) : Game :=
    let g0 := insertObject afterDraw windcragDef17 me (.hand me)
    let cid := (g0.player me).hand.back!
    let (g1, _) := g0.putOntoBattlefield cid me (cause := some testCause)
    mustApply g1 me (.chooseMode modeIdx)
  let gMardu : Game := putSiegeWithMode 0
  let gMarduUpkeep : Game := gMardu.record (GameEvent.stepped gMardu.turnNumber .upkeep me)
  let gJeskai : Game := putSiegeWithMode 1
  let gJeskaiUpkeep : Game := ((gJeskai.record (GameEvent.stepped gJeskai.turnNumber .upkeep me)).receivePriority me).resolveTop
  let windcragOk : Bool :=
    gMarduUpkeep.waitingTriggers.isEmpty &&
    (gJeskaiUpkeep.permanentsOf me).any (fun o => o.printed.isToken && gJeskaiUpkeep.hasSubtype o .goblin)

  -- 5e. `copySelfNonlegendary`: nontoken triggers & resolves via LKI even if source left `.battlefield`, while token copy does NOT trigger!
  let selfCopyAb : TriggeredAbility := .triggered .enter (Effect.ofTrigger .copySelfNonlegendary) {}
  let selfCopyDef : CardDef := { bear with name := "Phase17 Clone Legend", supertypes := #[.legendary], triggeredAbilities := #[selfCopyAb] }
  let gSC0 : Game := insertObject afterDraw selfCopyDef me (.hand me)
  let scHandId := (gSC0.player me).hand.back!
  let (gSC1, scPermId) := gSC0.putOntoBattlefield scHandId me (cause := some testCause)
  let gSC1 := gSC1.afterPermanentEnters (gSC1.object! scPermId) |>.receivePriority me
  -- Destroy `scPermId` before its ETB resolves -> LKI still creates two nonlegendary token copies, and neither token copy re-triggers `selfCopyAb`!
  let gSC2 : Game := (gSC1.moveToOwnerGraveyard (gSC1.object! scPermId) "dies" (verb := some .destroy) (cause := some testCause)).resolveTop
  let tokenClones := (gSC2.permanentsOf me).filter (fun o => o.name == "Phase17 Clone Legend" && o.printed.isToken)
  let selfCopyOk : Bool :=
    tokenClones.size == 2 &&
    tokenClones.all (fun o => !(gSC2.supertypes o).contains .legendary) &&
    gSC2.waitingTriggers.isEmpty

  mustHold17 "5a.gingerOk" gingerOk &&
  mustHold17 "5b.obOk" obOk &&
  mustHold17 "5c.tamiyoOk" tamiyoOk &&
  mustHold17 "5d.windcragOk" windcragOk &&
  mustHold17 "5e.selfCopyOk" selfCopyOk &&
  mustHold17 "5.replay" ([gGinLostMonarch, gGinKeptMonarch, gObLife, gTamRes, gMarduUpkeep, gJeskaiUpkeep, gSC2].all (fun g =>
    Game.replayEvents g.events == g && allRulesEventsClassified g))

-- 6. CR 704.5d–e / 707.10 / 707.12 card & permanent spell copy lifecycle, CR 608.2b / 608.3b–c / 303.4a,c Aura resolution, & retargeting.
#guard
  -- 6a. `.uldarosCopies`: exiled card copies have `isToken == false && isCopy == true`, survive `checkSBA` in `.exile` and `.stack`,
  --     permanent card copies resolve onto `.battlefield` with `isToken == true` (CR 608.3f / 707.10f), instant/sorcery copies
  --     cease to exist on resolution, and declining remaining exiled copies sweeps them via CR 704.5e `copiesOutside`!
  let freeInstDef : CardDef := {
    name := "Phase17 Free Bolt"
    manaCost := ManaCost.ofGeneric 1
    types := #[.instant]
    spellEffect := some (Effect.gainLife 3)
  }
  let gUl0 : Game := insertObject (insertObject afterDraw bear me (.graveyard me)) freeInstDef me (.graveyard me)
  let gyBear := ((gUl0.player me).graveyard.filter (fun id => (gUl0.object! id).name == bear.name))[0]!
  let gyInst := ((gUl0.player me).graveyard.filter (fun id => (gUl0.object! id).name == "Phase17 Free Bolt"))[0]!
  let uldEff : Effect := { resolution := .uldarosCopies }
  let gUl1 : Game := gUl0.applyFra me uldEff .uldarosCopies #[Target.card gyBear, Target.card gyInst] none
  let exCopies := gUl1.objects.filter (fun o => o.zone == .exile && o.isCopy)
  let exileCopyStateOk : Bool :=
    exCopies.size == 2 && exCopies.all (fun o => !o.printed.isToken && o.isCopy)
  let bearCopyExId := (exCopies.filter (·.name == bear.name))[0]!.id
  let instCopyExId := (exCopies.filter (·.name == "Phase17 Free Bolt"))[0]!.id
  -- Cast the permanent card copy (`bearCopyExId`), decline the exiled instant copy, and also verify `checkSBA` sweeps
  -- non-token `isCopy` objects outside `.stack`/`.battlefield` (CR 704.5e) while keeping `stackBearCopy` on `.stack`!
  let gUlCastBear : Game := mustApply gUl1 me (.cast bearCopyExId)
  let gUlAfterDecline : Game := mustApply gUlCastBear me .decline
  let strayGyCopyId : ObjectId := ⟨gUlAfterDecline.nextObjectId⟩
  let strayGyCopyObj : GameObject := {
    id := strayGyCopyId
    printed := freeInstDef
    owner := me
    zone := .graveyard me
    timestamp := gUlAfterDecline.timestamp + 1
    isCopy := true
  }
  let gUlWithStrayGyCopy : Game :=
    gUlAfterDecline.record (GameEvent.created gUlAfterDecline.turnNumber me (gUlAfterDecline.snapshot strayGyCopyObj) (cause := testCause))
  let gUlAfterSba : Game := gUlWithStrayGyCopy.checkSBA
  let stackBearCopy := (gUlAfterSba.objects.filter (fun o => o.zone == .stack && o.name == bear.name))[0]!
  let stackAndSweptExileOk : Bool :=
    !stackBearCopy.printed.isToken &&
    stackBearCopy.isCopy &&
    !(gUlAfterSba.objects.any (fun o => o.zone == .exile && o.isCopy)) &&
    (gUlAfterSba.findObject? strayGyCopyId).isNone
  let gUlResolvedBear : Game := gUlAfterSba.resolveTop
  -- Also cast & resolve the instant copy (`instCopyExId`) + SBA check to verify non-permanent card copies cease to exist (CR 707.10a / 704.5e):
  let gUlResolvedInst : Game := (mustApply (mustApply gUl1 me (.cast instCopyExId)) me .decline).resolveTop.checkSBA
  let bfBearCopy := (gUlResolvedBear.permanentsOf me).filter (fun o => o.name == bear.name && o.printed.isToken)
  let bfTokenCopyOk : Bool :=
    bfBearCopy.size == 1 && bfBearCopy[0]!.printed.isToken && !bfBearCopy[0]!.isCopy &&
    (gUlResolvedInst.player me).life == (gUl1.player me).life + 3 &&
    !(gUlResolvedInst.objects.any (fun o => o.isCopy))

  -- 6b. Targeted Aura spell fizzles to graveyard with `removedOnResolution` when target gains hexproof (CR 608.2b / 608.3b),
  --     and *Secret Invasion* (`"Enchant creature you control"`) fizzles if target's controller changes to `opp`!
  let buffAuraDef : CardDef := aura "Phase17 Buff Aura" ManaCost.empty "Enchant creature"
  let gAu0 : Game := insertObject (addPermanent afterDraw bear opp opp) buffAuraDef me (.hand me)
  let oppBearId := (gAu0.battlefield.filter (·.name == bear.name))[0]!.id
  let auHandId := (gAu0.player me).hand.back!
  let gAuCast : Game := mustApply (mustApply gAu0 me (.cast auHandId)) me (.target (.permanent oppBearId))
  let gAuHex : Game := gAuCast.createEffect
    (.layered (.objects #[oppBearId]) (.abilities { keywords := { hexproof := true } } .none) .untilEndOfTurn)
    (cause := some testCause)
  let preAuRes := gAuHex.events.size
  let gAuFizzled : Game := gAuHex.resolveTop
  let auFizzleSlice := gAuFizzled.events.extract preAuRes gAuFizzled.events.size
  let auraHexproofFizzleOk : Bool :=
    !(gAuFizzled.permanentsOf me).any (·.name == "Phase17 Buff Aura") &&
    (gAuFizzled.player me).graveyard.any (fun id => (gAuFizzled.object! id).name == "Phase17 Buff Aura") &&
    auFizzleSlice.any (fun e => match e.change with | .rules (.stackObject (.removedOnResolution ..)) => true | _ => false)

  let gSI0 : Game := insertObject (addPermanent (addPermanent afterDraw bear me me) hero opp opp) secretInvasionDef17 me (.hand me)
  let myBearSI := (gSI0.battlefield.filter (fun o => o.name == bear.name && o.controller == some me))[0]!.id
  let oppHeroSI := (gSI0.battlefield.filter (fun o => o.name == hero.name && o.controller == some opp))[0]!.id
  let siHandId := (gSI0.player me).hand.back!
  let gSICast0 : Game := mustApply gSI0 me (.cast siHandId)
  let rejectOppCreatureOk : Bool :=
    match gSICast0.apply me (.target (.permanent oppHeroSI)) with
    | .error _ => true
    | .ok _ => false
  let gSICast1 : Game := mustApply gSICast0 me (.target (.permanent myBearSI))
  let gSIStolen : Game := (gSICast1.changeControl (gSICast1.object! myBearSI) opp (cause := some testCause)).resolveTop
  let secretInvasionCtrlOk : Bool :=
    rejectOppCreatureOk &&
    !(gSIStolen.permanentsOf me).any (·.name == secretInvasionDef17.name) &&
    (gSIStolen.player me).graveyard.any (fun id => (gSIStolen.object! id).name == secretInvasionDef17.name)

  -- 6c. Multi-target `setSpellTargetAt` enforces distinct-target constraints (`twoCreaturesOrLandsYouControl`).
  let twoTargetInst : CardDef := {
    name := "Phase17 Dual Rally"
    manaCost := ManaCost.empty
    types := #[.instant]
    spellEffect := some { targeting := .of .twoCreaturesOrLandsYouControl, resolution := .sequence [], phrase := "Choose two target creatures and/or lands you control." }
  }
  let gMT0 : Game := insertObject (addPermanent (addPermanent (addPermanent afterDraw bear me me) hero me me) samsonDef17 me me) twoTargetInst me (.hand me)
  let cA := (gMT0.battlefield.filter (·.name == bear.name))[0]!.id
  let cB := (gMT0.battlefield.filter (·.name == hero.name))[0]!.id
  let cC := (gMT0.battlefield.filter (·.name == "Phase17 Doc Samson"))[0]!.id
  let dtHand := (gMT0.player me).hand.back!
  let gMTCast : Game := mustApply (mustApply (mustApply gMT0 me (.cast dtHand)) me (.target (.permanent cA))) me (.target (.permanent cB))
  let spId := gMTCast.stack.back!.objectId
  let gMTDupRejected : Game := gMTCast.setSpellTargetAt spId 1 (.permanent cA)
  let gMTChanged : Game := gMTCast.setSpellTargetAt spId 1 (.permanent cC)
  let retargetDistinctOk : Bool :=
    (gMTDupRejected.stackEntry? spId).map (·.targets) == some #[.permanent cA, .permanent cB] &&
    (gMTChanged.stackEntry? spId).map (·.targets) == some #[.permanent cA, .permanent cC]

  mustHold17 "6a.exileCopyStateOk" exileCopyStateOk &&
  mustHold17 "6a.stackAndSweptExileOk" stackAndSweptExileOk &&
  mustHold17 "6a.bfTokenCopyOk" bfTokenCopyOk &&
  mustHold17 "6b.auraHexproofFizzleOk" auraHexproofFizzleOk &&
  mustHold17 "6b.secretInvasionCtrlOk" secretInvasionCtrlOk &&
  mustHold17 "6c.retargetDistinctOk" retargetDistinctOk &&
  mustHold17 "6.replay" ([gUl1, gUlAfterSba, gUlResolvedBear, gUlResolvedInst, gAuFizzled, gSIStolen, gMTDupRejected, gMTChanged].all (fun g =>
    Game.replayEvents g.events == g && allRulesEventsClassified g))

-- 7. CR 704.3 / 704.5j recursive `keepLegend` `preBf`, CR 610.3 post-departure `linkedExile` batch, CR 303.4f two-pass Aura entry, & *Worlds Within Worlds* batches.
#guard
  -- 7a. Recursive left-nested `.seq` in `keepLegend`: 3 simultaneous SBA actions alongside `chooseLegend` still preserve `preBf` LKI!
  let legWatcherAb : TriggeredAbility :=
    .triggered (.fra .anotherCreatureOrPlaneswalkerYouControlDies) { resolution := .gainLife (.fixed 4), phrase := "You gain 4 life." } {}
  let legDef17 : CardDef := { bear with name := "Phase17 Legend", supertypes := #[.legendary] }
  let zeroWatcher17 : CardDef := { creature "Phase17 Zero Watcher" ManaCost.empty #["Spirit"] 0 0 with triggeredAbilities := #[legWatcherAb] }
  let strayAura17 : CardDef := aura "Phase17 Stray Aura" ManaCost.empty "Enchant creature"
  let gLeg0 : Game :=
    addPermanent (addPermanent (addPermanent (addPermanent afterDraw legDef17 me me) legDef17 me me) zeroWatcher17 me me) strayAura17 me me
  let legs := gLeg0.battlefield.filter (·.name == "Phase17 Legend")
  let gyBeforeLeg := (gLeg0.player me).graveyard.size
  let gLegPaused : Game := gLeg0.finishCleanupStepAfterDiscard
  let rec leftNestedDepth? : PendingReplacement → Option Nat
    | .finishSbaSweep .. => some 0
    | .seq a _ => (· + 1) <$> leftNestedDepth? a
    | _ => none
  let nestedSeqPausedOk : Bool :=
    (gLegPaused.pendingReplacement.bind leftNestedDepth?).any (· >= 2)
  let gLegResumed : Game := mustApply gLegPaused me (.keepLegend legs[0]!.id)
  -- `zeroWatcher17` died in stage 0 yet still saw the unkept `Phase17 Legend` die via recursive `findSweepPreBf?`!
  let legNestedSeqOk : Bool :=
    nestedSeqPausedOk &&
    gLegResumed.stack.size == 1 &&
    (gLegResumed.player me).graveyard.size == gyBeforeLeg + 3

  -- 7b. Post-departure `linkedExile` separate batch (CR 610.3): simultaneous board wipe commits departures in batch B1 and `linkedExile` returns in batch B2 (`B1 != B2`)!
  let jailerDef : CardDef := { name := "Phase17 Jailer", manaCost := ManaCost.empty, types := #[.enchantment] }
  let gLink0 : Game := addPermanent (addPermanent afterDraw jailerDef me me) hero me me
  let jailerId := (gLink0.battlefield.filter (·.name == "Phase17 Jailer"))[0]!.id
  let heroWipeId := (gLink0.battlefield.filter (·.name == hero.name))[0]!.id
  let gLink0 : Game := insertObject gLink0 bear opp (.exile)
  let exiledBearId := (gLink0.objects.filter (fun o => o.name == bear.name && o.zone == .exile))[0]!.id
  let gLink1 : Game := gLink0.changeObject jailerId (.pushLinkedExile exiledBearId)
  let preWipeIdx := gLink1.events.size
  let wipeCause : EventCause := .oneShotEffect (some ⟨1701⟩) none (some me)
  let gWiped : Game :=
    gLink1.withBatch (some wipeCause) fun g =>
      let g := g.moveToOwnerGraveyard (g.object! jailerId) "destroyed" (verb := some .destroy) (cause := some wipeCause)
      g.moveToOwnerGraveyard (g.object! heroWipeId) "destroyed" (verb := some .destroy) (cause := some wipeCause)
  let wipeSlice := gWiped.events.extract preWipeIdx gWiped.events.size
  let destroyBatches := wipeSlice.filterMap fun e =>
    match e.change with
    | .rules (.zone (.moved _ _ .battlefield (.graveyard _) _ _ _ _)) => e.batch
    | _ => none
  let returnBatches := wipeSlice.filterMap fun e =>
    match e.change with
    | .rules (.zone (.moved _ _ .exile .battlefield _ _ _ _)) => e.batch
    | _ => none
  let linkedExileSeparateBatchOk : Bool :=
    destroyBatches.size == 2 &&
    destroyBatches[0]! == destroyBatches[1]! &&
    returnBatches.size == 1 &&
    returnBatches[0]! != destroyBatches[0]! &&
    (gWiped.permanentsOf opp).any (·.name == bear.name)

  -- 7c. Two-pass simultaneous entry Aura `preBattlefield` check (`placeSearchedBatch`, CR 303.4f):
  --     searching an Aura + creature onto an empty battlefield leaves the Aura in library (cannot attach to co-entering creature),
  --     whereas with an existing creature on `preBf`, both enter in the same batch with the Aura attached to the pre-existing creature!
  let searchAuraDef : CardDef := aura "Phase17 Search Aura" ManaCost.empty "Enchant creature"
  let gSrchEmpty0 : Game := insertObject (insertObject afterDraw bear me (.library me)) searchAuraDef me (.library me)
  let libE := (gSrchEmpty0.player me).library
  let srchAuraE := libE.back!
  let srchBearE := libE[libE.size - 2]!
  let gSrchEmpty1 : Game := gSrchEmpty0.placeSearchedBatch me #[srchBearE, srchAuraE] false (cause := some testCause)
  let emptyPreBfAuraStaysOk : Bool :=
    (gSrchEmpty1.permanentsOf me).any (·.name == bear.name) &&
    !(gSrchEmpty1.permanentsOf me).any (·.name == "Phase17 Search Aura") &&
    (gSrchEmpty1.object! srchAuraE).zone == .library me

  let gSrchHost0 : Game := insertObject (insertObject (addPermanent afterDraw hero me me) bear me (.library me)) searchAuraDef me (.library me)
  let preHostId := (gSrchHost0.battlefield.filter (·.name == hero.name))[0]!.id
  let libH := (gSrchHost0.player me).library
  let srchAuraH := libH.back!
  let srchBearH := libH[libH.size - 2]!
  let preSrchIdx := gSrchHost0.events.size
  let gSrchHost1 : Game := gSrchHost0.placeSearchedBatch me #[srchBearH, srchAuraH] false (cause := some testCause)
  let srchBatches := (gSrchHost1.events.extract preSrchIdx gSrchHost1.events.size).filterMap fun e =>
    match e.change with
    | .rules (.zone (.moved _ _ (.library _) .battlefield _ _ _ _)) => e.batch
    | _ => none
  let enteredSearchAura := (gSrchHost1.permanentsOf me).filter (·.name == "Phase17 Search Aura")
  let hostPreBfAuraAttachesOk : Bool :=
    srchBatches.size == 2 && srchBatches[0]! == srchBatches[1]! &&
    enteredSearchAura.size == 1 && enteredSearchAura[0]!.attachedTo == some preHostId

  -- 7d. *Worlds Within Worlds* (`worldsDef17`): creatures from hand, exiled cards to hand, and exiling the spell commit in 3 distinct batches!
  let gWWW0 : Game := insertObject (insertObject (addPermanent afterDraw bear me me) hero me (.hand me)) worldsDef17 me (.hand me)
  let wwwHand := (gWWW0.player me).hand.back!
  let heroInHand := ((gWWW0.player me).hand.filter (fun id => (gWWW0.object! id).name == hero.name))[0]!
  let gWWWCast : Game := mustApply gWWW0 me (.cast wwwHand)
  let preWWWRes := gWWWCast.events.size
  let gWWWPrmpt : Game := gWWWCast.resolveTop
  let gWWWDone : Game :=
    match gWWWPrmpt.pending with
    | .fraChoice p (.worldsPutCreatures _ _ _ _ _) => mustApply gWWWPrmpt p (.choosePermanents #[heroInHand])
    | _ => gWWWPrmpt
  let wwwSlice := gWWWDone.events.extract preWWWRes gWWWDone.events.size
  let bPutHandToBf := wwwSlice.findSome? fun e =>
    match e.change with | .rules (.zone (.moved _ _ (.hand _) .battlefield ..)) => e.batch | _ => none
  let bExileToHand := wwwSlice.findSome? fun e =>
    match e.change with | .rules (.zone (.moved _ _ .exile (.hand _) ..)) => e.batch | _ => none
  let bSpellToExile := wwwSlice.findSome? fun e =>
    match e.change with | .rules (.zone (.moved _ _ .stack .exile ..)) => e.batch | _ => none
  let wwwThreeBatchesOk : Bool :=
    bPutHandToBf.isSome && bExileToHand.isSome && bSpellToExile.isSome &&
    bPutHandToBf != bExileToHand && bExileToHand != bSpellToExile && bPutHandToBf != bSpellToExile &&
    gWWWDone.objects.any (fun o => o.name == worldsDef17.name && o.zone == .exile)

  mustHold17 "7a.legNestedSeqOk" legNestedSeqOk &&
  mustHold17 "7b.linkedExileSeparateBatchOk" linkedExileSeparateBatchOk &&
  mustHold17 "7c.emptyPreBfAuraStaysOk" emptyPreBfAuraStaysOk &&
  mustHold17 "7c.hostPreBfAuraAttachesOk" hostPreBfAuraAttachesOk &&
  mustHold17 "7d.wwwThreeBatchesOk" wwwThreeBatchesOk &&
  mustHold17 "7.replay" ([gLegPaused, gLegResumed, gWiped, gSrchEmpty1, gSrchHost1, gWWWDone].all (fun g =>
    Game.replayEvents g.events == g && allRulesEventsClassified g))

-- 8. CR 800.4 `mayThen` departure decline & pregame concessions, silent cleanup `beginTurn`, and step/phase `EffectDuration` expiry.
#guard
  let leylinesDef : CardDef := {
    name := "Phase17 Leyline"
    manaCost := ManaCost.ofGeneric 4
    types := #[.enchantment]
    anyNumberInDeck := true
    staticAbilities := #[.mayBeginOnBattlefield]
  }
  let leylineDeck : Array CardDef := Array.replicate 60 leylinesDef
  let threePregameCfg : StartConfig := {
    seats := #[
      { name := "Chandra", deck := leylineDeck },
      { name := "Nissa", deck := leylineDeck },
      { name := "Liliana", deck := testGreenDeck }
    ]
    format := .constructed
    seed := 17
    startingPlayer := some 0
  }
  let gPre0 : Game :=
    match Start.start threePregameCfg with
    | .ok g => g
    | .error e => panic! e
  let p0 : PlayerId := ⟨0⟩
  let p1 : PlayerId := ⟨1⟩
  let p2 : PlayerId := ⟨2⟩
  -- 8a1. `p0` concedes during `declareMulligan` -> `p1` and `p2` keep, `p1` gets `.mayBeginOnBattlefield`, and Turn 1 starts with `activePlayer == p1`!
  let gPre1 : Game := gPre0.concede p0
  let gPre2 : Game := keepOpeningHands gPre1 20
  let gPre3 : Game :=
    Id.run do
      let mut g := gPre2
      let mut fuel := 25
      while fuel > 0 do
        fuel := fuel - 1
        match g.pending with
        | .fraChoice q (.mayBeginOnBattlefield _) => g := mustApply g q .accept
        | _ => fuel := 0
      return g
  let pregameConcedeMulliganOk : Bool :=
    (gPre3.player p0).leftTheGame &&
    gPre3.activePlayer == p1 &&
    gPre3.turnNumber == 1 &&
    (gPre3.permanentsOf p1).any (·.name == "Phase17 Leyline")

  -- 8a2. `p0` keeps through mulligans so `.mayBeginOnBattlefield` opens for `p0`, THEN `p0` concedes during `.mayBeginOnBattlefield`!
  let gPreB0 : Game := keepOpeningHands gPre0 20
  let p0PromptedBeginOk : Bool :=
    match gPreB0.pending with
    | .fraChoice q (.mayBeginOnBattlefield _) => q == p0
    | _ => false
  let gPreB1 : Game := gPreB0.concede p0
  let gPreB2 : Game :=
    Id.run do
      let mut g := gPreB1
      let mut fuel := 25
      while fuel > 0 do
        fuel := fuel - 1
        match g.pending with
        | .fraChoice q (.mayBeginOnBattlefield _) => g := mustApply g q .decline
        | _ => fuel := 0
      return g
  let pregameConcedeBeginOk : Bool :=
    p0PromptedBeginOk &&
    gPreB2.pending == .none &&
    gPreB2.activePlayer == p1 &&
    gPreB2.turnNumber == 1

  -- 8a3. `mayThen` departure decline (CR 800.4f): `p2` conceding on `Pending.mayPayGeneric p2 ...` inside a sequence
  --      declines `"If you do"` (so `p1` does NOT lose 5 life)!
  let maySeq : TriggeredAbility.TriggerResolution :=
    .sequence [
      .may (.pay (.mana #[.generic 1])) (.loseLife (.fixed 5) .eachOpponent) .ifYouDo,
      .gainLife (.fixed 2) ]
  let gMay0 : Game := (addPermanent gPreB2 bear p1 p1).addMana p2 .colorless 1 (cause := some testCause)
  let bP1 := (gMay0.battlefield.filter (fun o => o.name == bear.name && o.controller == some p1))[0]!.id
  let gMaySt : Game := gMay0.putTriggeredAbilityOnStack p2 (gMay0.object! bP1) (.onEnterDraw 1) "enters"
    (eventCause := some testCause) (reflexiveResolution := some maySeq)
  let gMayPrompt : Game := gMaySt.resolveTop
  let p1LifeBefore := (gMayPrompt.player p1).life
  let gMayConceded : Game := gMayPrompt.concede p2
  let mayLeaveDeclinedOk : Bool := (gMayConceded.player p1).life == p1LifeBefore

  -- 8b. Silent cleanup `finishPostSbaCleanup false` routes through `beginTurn` and expires `.untilNextTurnOf opp`!
  let gProt0 : Game := (afterDraw.createEffect (.protectionFromEverything opp) (cause := some testCause)).createEffect
    (.lifeCantChange opp) (cause := some testCause)
  let protBeforeOk : Bool :=
    gProt0.activeEffects.any (fun (_, e) => match e with | .playerRule q .protectionFromEverything (.untilNextTurnOf _) => q == opp | _ => false)
  let gProtNextTurn : Game := gProt0.finishPostSbaCleanup false
  let silentCleanupExpiredOk : Bool :=
    protBeforeOk &&
    gProtNextTurn.activePlayer == opp &&
    !gProtNextTurn.activeEffects.any (fun (_, e) =>
      match e with
      | .playerRule _ .protectionFromEverything _ | .playerRule _ .lifeCantChange _ => true
      | _ => false) &&
    gProtNextTurn.events.any (fun e =>
      match e.change, e.cause? with
      | .rules (.continuousEffect (.expired _)), some (.turnBased .expireAtStepBegin) => true
      | _, _ => false)

  -- 8c. Step/phase `EffectDuration` expiry (`CR 500.4–5 / 511.2 / 611.2a`):
  let gDur0 : Game := addPermanent afterDraw bear me me
  let dBear := (gDur0.battlefield.filter (·.name == bear.name))[0]!.id
  let eUpkeepEnd : ContinuousEffectSpec := .layered (.objects #[dBear]) (.ptModify 1 1) (.untilEndOfStepOrPhase (.step .upkeep))
  let eMainBegin : ContinuousEffectSpec := .layered (.objects #[dBear]) (.ptModify 2 2) (.untilStepOrPhase (.phase .precombatMain))
  let eEndCombat : ContinuousEffectSpec := .layered (.objects #[dBear]) (.ptModify 3 3) (.untilEndOfCombat)
  let eNextTurnEnd : ContinuousEffectSpec := .layered (.objects #[dBear]) (.ptModify 4 4) (.untilEndOfNextTurnOf me)
  let gDur1 : Game := (((gDur0.createEffect eUpkeepEnd (cause := some testCause)).createEffect
    eMainBegin (cause := some testCause)).createEffect
    eEndCombat (cause := some testCause)).createEffect
    eNextTurnEnd (cause := some testCause)
  let pStart := gDur1.power (gDur1.object! dBear) -- 2 + 1 + 2 + 3 + 4 = 12
  let gDur2 : Game := gDur1.recordStepEnded .upkeep
  let pAfterUpkeepEnd := gDur2.power (gDur2.object! dBear) -- 11
  let gDur3 : Game := gDur2.recordPhaseBegan .precombatMain
  let pAfterMainBegin := gDur3.power (gDur3.object! dBear) -- 9
  let gDur4 : Game := gDur3.recordPhaseEnded .combat
  let pAfterCombatEnd := gDur4.power (gDur4.object! dBear) -- 6 (2 + 4)
  -- `clearEOT` on THIS turn does NOT expire `.untilEndOfNextTurnOf me` (`hasTurnBegunSince` is false),
  -- then after `turnBegan` for `me`, `clearEOT` DOES expire `.untilEndOfNextTurnOf me`!
  let gDur5 : Game := gDur4.clearEOT
  let pAfterThisEot := gDur5.power (gDur5.object! dBear) -- still 6!
  let gDur6 : Game := (gDur5.record (GameEvent.turnBegan (gDur5.turnNumber + 1) me)).clearEOT
  let pAfterNextTurnEot := gDur6.power (gDur6.object! dBear) -- back to 2!
  let durationsOk : Bool :=
    pStart == 12 &&
    pAfterUpkeepEnd == 11 &&
    pAfterMainBegin == 9 &&
    pAfterCombatEnd == 6 &&
    pAfterThisEot == 6 &&
    pAfterNextTurnEot == 2

  mustHold17 "8a1.pregameConcedeMulliganOk" pregameConcedeMulliganOk &&
  mustHold17 "8a2.pregameConcedeBeginOk" pregameConcedeBeginOk &&
  mustHold17 "8a3.mayLeaveDeclinedOk" mayLeaveDeclinedOk &&
  mustHold17 "8b.silentCleanupExpiredOk" silentCleanupExpiredOk &&
  mustHold17 "8c.durationsOk" durationsOk &&
  mustHold17 "8.replay" ([gPre3, gPreB2, gMayConceded, gProtNextTurn, gDur2, gDur3, gDur4, gDur5, gDur6].all (fun g =>
    Game.replayEvents g.events == g && allRulesEventsClassified g))

-- 9. PR #602 review regression guards:
--    (a) Post-choice return logs in `runLinkedExileBatch`, `returnLinkedExileLoop`, and `finishWorldsWithinWorldsTail`.
--    (b) `tricksterLibrary` concession by `caster` clears the prompt and leaves the creature on `.battlefield` (CR 800.4a/g/h).
--    (c) `commitEnteringAttackItems` (`applyPut` `.revealed`) checks entering Auras against `preBattlefield` (CR 303.4f).
#guard
  -- 9a1. `runLinkedExileBatch` & `returnLinkedExileLoop` with competing `.exileInsteadOfGraveyard` replacements:
  --      neither logs `"returns to ...'s graveyard"` while paused OR when redirected to `.exile`,
  --      and BOTH log `"returns to ...'s graveyard"` post-choice when the graveyard move actually succeeds!
  let gLnk0 : Game := insertObject (insertObject (addPermanent afterDraw hero opp opp) bear me .exile) bear me .exile
  let oppSrc := (gLnk0.battlefield.filter (fun o => o.name == hero.name && o.controller == some opp))[0]!.id
  let exBearIds := (gLnk0.objects.filter (fun o => o.name == bear.name && o.zone == .exile)).map (·.id)
  let exGy1 := exBearIds[0]!
  let exGy2 := exBearIds[1]!
  let gLnk1 : Game := (gLnk0.changeObject exGy1 (.returnToZone (some (.graveyard me)))).changeObject
    exGy2 (.returnToZone (some (.graveyard me)))
  let idRep1A : ReplacementId := { kind := .finalityCounterExile, object := some exGy1 }
  let idRep1B : ReplacementId := { kind := .exileOppDeath, object := some exGy1 }
  let idRep2A : ReplacementId := { kind := .finalityCounterExile, object := some exGy2 }
  let idRep2B : ReplacementId := { kind := .exileOppDeath, object := some exGy2 }
  let gLnkRedir : Game := ((gLnk1.createEffect
    (.replacement { id := idRep1A, affectedPlayer := me, kind := .exileInsteadOfGraveyard (some exGy1) false })
    (cause := some testCause)).createEffect
    (.replacement { id := idRep1B, affectedPlayer := me, kind := .exileInsteadOfGraveyard (some exGy1) false })
    (cause := some testCause))
  let logBeforeBatch := gLnkRedir.log.size
  let gBatchPaused : Game := gLnkRedir.returnLinkedExileMoves #[exGy1]
  let gBatchRedirDone : Game := mustApply gBatchPaused me (.chooseReplacement idRep1A)
  let batchNoPrematureOrFalseLogOk : Bool :=
    !(gBatchPaused.log.extract logBeforeBatch gBatchPaused.log.size).any (·.contains "returns to") &&
    !(gBatchRedirDone.log.extract logBeforeBatch gBatchRedirDone.log.size).any (·.contains "returns to") &&
    (gBatchRedirDone.followMovedToZone? exGy1 (· == .exile)).isSome

  -- Scope the two competing replacements on `exGy2` to `oppSrc` so removing `oppSrc` while paused lets the resumed move enter `.graveyard me`!
  let gLnkLoop0 : Game := ((gLnk1.createEffect
    (.replacement { id := idRep2A, affectedPlayer := me, kind := .exileInsteadOfGraveyard (some exGy2) false }
      (.whileSourceOnBattlefield oppSrc))
    (cause := some testCause)).createEffect
    (.replacement { id := idRep2B, affectedPlayer := me, kind := .exileInsteadOfGraveyard (some exGy2) false }
      (.whileSourceOnBattlefield oppSrc))
    (cause := some testCause))
  let logBeforeLoop := gLnkLoop0.log.size
  let gLoopPaused : Game := gLnkLoop0.withBatch none fun g => g.returnLinkedExileLoop #[exGy2]
  let loopPausedNoLogOk : Bool :=
    !(gLoopPaused.log.extract logBeforeLoop gLoopPaused.log.size).any (·.contains "returns to")
  let gLoopSrcGone : Game := gLoopPaused.expireWhileSourceEffects oppSrc
  let gLoopGyDone : Game := mustApply gLoopSrcGone me (.chooseReplacement idRep2A)
  let loopPostChoiceGyLogsOk : Bool :=
    loopPausedNoLogOk &&
    (gLoopGyDone.followMovedToZone? exGy2 (· == .graveyard me)).isSome &&
    (gLoopGyDone.log.extract logBeforeLoop gLoopGyDone.log.size).any (fun s =>
      s.contains "returns to " && s.contains "'s graveyard")

  -- 9a2. Hand return across an active `Pending.chooseReplacement` in `runLinkedExileBatch`, `returnLinkedExileLoop`, and `finishWorldsWithinWorldsTail`:
  let gHand0 : Game := insertObject (insertObject gLnkRedir hero me .exile) bear me .exile
  let exHeroHand := (gHand0.objects.filter (fun o => o.name == hero.name && o.zone == .exile))[0]!.id
  let exWWWHand := (gHand0.objects.filter (fun o => o.name == bear.name && o.zone == .exile)).back!.id
  let gHand1 : Game := gHand0.changeObject exHeroHand (.returnToZone (some (.hand me)))
  let gDummyPause : Game := gHand1.returnLinkedExileMoves #[exGy1]
  -- Chain `worldsReturnExiledLoop` behind `gDummyPause`'s `Pending.chooseReplacement`:
  let logBeforeWWW := gDummyPause.log.size
  let gWWWPaused : Game := gDummyPause.worldsReturnExiledLoop #[exWWWHand] none
  let wwwNoEarlyLogOk : Bool :=
    !(gWWWPaused.log.extract logBeforeWWW gWWWPaused.log.size).any (·.contains "returned to its owner's hand")
  let gWWWResumed : Game := mustApply gWWWPaused me (.chooseReplacement idRep1A)
  let wwwPostChoiceLogOk : Bool :=
    wwwNoEarlyLogOk &&
    (gWWWResumed.followMovedToZone? exWWWHand (· == .hand me)).isSome &&
    (gWWWResumed.log.extract logBeforeWWW gWWWResumed.log.size).any (·.contains "is returned to its owner's hand")

  let logBeforeLoopHand := gHand1.log.size
  let gLoopHandPaused : Game := gHand1.withBatch none fun g =>
    g.returnLinkedExileLoop #[exGy1, exHeroHand]
  let loopHandNoEarlyLogOk : Bool :=
    !(gLoopHandPaused.log.extract logBeforeLoopHand gLoopHandPaused.log.size).any (·.contains "returns to")
  let gLoopHandResumed : Game := mustApply gLoopHandPaused me (.chooseReplacement idRep1A)
  let loopHandPostChoiceOk : Bool :=
    loopHandNoEarlyLogOk &&
    (gLoopHandResumed.followMovedToZone? exHeroHand (· == .hand me)).isSome &&
    (gLoopHandResumed.log.extract logBeforeLoopHand gLoopHandResumed.log.size).any (·.contains s!"{hero.name} returns to {(gLoopHandResumed.player me).name}'s hand")

  -- 9b. `tricksterLibrary`: `caster` conceding while `q` is choosing clears `pending` and leaves `q`'s creature on `.battlefield`!
  let threeCfg9 : StartConfig := {
    seats := #[
      { name := "Caster", deck := testGreenDeck },
      { name := "Owner", deck := testGreenDeck },
      { name := "Third", deck := testGreenDeck }
    ]
    format := .constructed
    seed := 19
    startingPlayer := some 0
  }
  let gTr0 : Game :=
    match Start.start threeCfg9 with
    | .ok g => (keepOpeningHands g 20).advanceStep
    | .error e => panic! e
  let trCaster : PlayerId := ⟨0⟩
  let trOwner : PlayerId := ⟨1⟩
  let gTr1 : Game := addPermanent gTr0 bear trOwner trOwner
  let trBear := (gTr1.battlefield.filter (fun o => o.name == bear.name && o.owner == trOwner))[0]!.id
  let gTrPrompt : Game := gTr1.change (.pending (.fraChoice trOwner (.tricksterLibrary trCaster trBear none)))
  let gTrConceded : Game := gTrPrompt.concede trCaster
  let gTrNoopHelper : Game := gTrConceded.applyOwnerPutsLibraryThenConnive trCaster #[Target.permanent trBear]
  let tricksterCasterLeaveOk : Bool :=
    (gTrConceded.player trCaster).leftTheGame &&
    gTrConceded.pending == .none &&
    (gTrConceded.findObject? trBear).any (·.isOnBattlefield) &&
    !(gTrConceded.player trOwner).library.contains trBear &&
    (gTrNoopHelper.findObject? trBear).any (·.isOnBattlefield)

  -- 9c. `commitEnteringAttackItems` (`applyPut` `.revealed`): Aura checks `preBattlefield` per CR 303.4f!
  let revAuraDef : CardDef := aura "Phase17 Revealed Aura" ManaCost.empty "Enchant creature"
  -- 9c1. Empty `preBf`: revealed `[bear, revAuraDef]` leaves `revAuraDef` in `.library me` (does not enter unattached & die)!
  let gRevE0 : Game := insertObject (insertObject afterDraw bear me (.library me)) revAuraDef me (.library me)
  let libRevE := (gRevE0.player me).library
  let revAuraE := libRevE.back!
  let revBearE := libRevE[libRevE.size - 2]!
  let gRevE1 : Game := (gRevE0.change (.pushContinuationFrame { revealedIdsThisWay := #[revBearE, revAuraE] })).applyPut
    me (.onEnterDraw 0) none #[] .revealed .asPrinted .none
  let revEmptyAuraStaysOk : Bool :=
    (gRevE1.permanentsOf me).any (·.name == bear.name) &&
    !(gRevE1.permanentsOf me).any (·.name == "Phase17 Revealed Aura") &&
    (gRevE1.object! revAuraE).zone == .library me &&
    !(gRevE1.player me).graveyard.any (fun id => (gRevE1.object! id).name == "Phase17 Revealed Aura")

  -- 9c2. Non-empty `preBf` with `hero`: revealed `[bear, revAuraDef]` attaches `revAuraDef` to `hero` in the same batch!
  let gRevH0 : Game := insertObject (insertObject (addPermanent afterDraw hero me me) bear me (.library me)) revAuraDef me (.library me)
  let preHeroId := (gRevH0.battlefield.filter (·.name == hero.name))[0]!.id
  let libRevH := (gRevH0.player me).library
  let revAuraH := libRevH.back!
  let revBearH := libRevH[libRevH.size - 2]!
  let preRevHIdx := gRevH0.events.size
  let gRevH1 : Game := (gRevH0.change (.pushContinuationFrame { revealedIdsThisWay := #[revBearH, revAuraH] })).applyPut
    me (.onEnterDraw 0) none #[] .revealed .asPrinted .none
  let revHBatches := (gRevH1.events.extract preRevHIdx gRevH1.events.size).filterMap fun e =>
    match e.change with
    | .rules (.zone (.moved _ _ (.library _) .battlefield _ _ _ _)) => e.batch
    | _ => none
  let enteredRevAura := (gRevH1.permanentsOf me).filter (·.name == "Phase17 Revealed Aura")
  let revHostAuraAttachesOk : Bool :=
    revHBatches.size == 2 && revHBatches[0]! == revHBatches[1]! &&
    enteredRevAura.size == 1 && enteredRevAura[0]!.attachedTo == some preHeroId

  -- 9c3. Paused `commitEnteringAttackItems` on empty `preBf`: co-entering `asEntersChooseOddEven` creature pausing first still keeps `preBf` empty for the Aura!
  let oddCreature9 : CardDef := { bear with name := "Phase17 Odd Striker", asEntersChooseOddEven := true }
  let gPauseEnt0 : Game := insertObject (insertObject afterDraw oddCreature9 me (.hand me)) revAuraDef me (.hand me)
  let hPause := (gPauseEnt0.player me).hand
  let pauseAura := hPause.back!
  let pauseOdd := hPause[hPause.size - 2]!
  let itemOdd : EnteringAttackItem := .card pauseOdd me me false false #[] [] .putOntoBattlefield #[]
  let itemAura : EnteringAttackItem := .card pauseAura me me false false #[] [] .putOntoBattlefield #[]
  let gPauseEnt1 : Game := gPauseEnt0.commitEnteringAttackItems #[(itemOdd, none), (itemAura, none)] (cause := some testCause)
  let gPauseEntDone : Game := mustApply gPauseEnt1 me (.chooseMode 0)
  let pausedPreBfPreservedOk : Bool :=
    gPauseEntDone.pending == .none &&
    (gPauseEntDone.permanentsOf me).any (·.name == "Phase17 Odd Striker") &&
    !(gPauseEntDone.permanentsOf me).any (·.name == "Phase17 Revealed Aura") &&
    (gPauseEntDone.object! pauseAura).zone == .hand me

  mustHold17 "9a1.batchNoPrematureOrFalseLogOk" batchNoPrematureOrFalseLogOk &&
  mustHold17 "9a1.loopPostChoiceGyLogsOk" loopPostChoiceGyLogsOk &&
  mustHold17 "9a2.wwwPostChoiceLogOk" wwwPostChoiceLogOk &&
  mustHold17 "9a2.loopHandPostChoiceOk" loopHandPostChoiceOk &&
  mustHold17 "9b.tricksterCasterLeaveOk" tricksterCasterLeaveOk &&
  mustHold17 "9c1.revEmptyAuraStaysOk" revEmptyAuraStaysOk &&
  mustHold17 "9c2.revHostAuraAttachesOk" revHostAuraAttachesOk &&
  mustHold17 "9c3.pausedPreBfPreservedOk" pausedPreBfPreservedOk &&
  mustHold17 "9.replay" ([gBatchPaused, gBatchRedirDone, gLoopPaused, gLoopGyDone, gWWWPaused, gWWWResumed,
      gLoopHandPaused, gLoopHandResumed, gTrConceded, gRevE1, gRevH1, gPauseEnt1, gPauseEntDone].all (fun g =>
    Game.replayEvents g.events == g && allRulesEventsClassified g))

end Phase17EventAlignment

/-! ### Phase 18 Event Alignment Isolation Tests (CR 111.8 / 115.3 / 115.7d / 303.4f–g / 500.4 / 506.5 / 509.1g / 514.2 / 603.2d / 603.3c–d / 603.4 / 603.12 / 608.2b,h / 610.3 / 611.2a–b / 614.12 / 700.2 / 701.54 / 702.26b,d,f / 707.2 / 707.10c / 723.5 / 725.4 / 733.1 / 800.4)

1. Nested-batch `currentBatch` cause isolation, 0-event pause replay parity, and single-writer `PermanentEvent.designation _ .ringBearer false` on zone departure & `ceasedToExist`.
2. `outerPendingReplacements` / `endsWithPriorityGrant` priority deferral, `runLinkedExileBatch` Pass 2, `shuffleSourceIntoLibrary` replacement pause-safety, and reflexive-sacrifice pause-safety.
3. CR 733.1 `.crew` & `.zemoBoastExile` proposal reversal / `.costAction` batching, and `reverseToProposalCheckpoint?` scaffolding, interleaved-engine batch grouping, `.lookedAt` filtering, & `queuedLinkedExile` flush.
4. CR 603.2d / 603.3c–d sequential multi-copy modal trigger announcement, mandatory `count`-mode removal (`noLegalMode`), `tapOrUntapNonland` & `hawkeyeModes` stack-placement announcement, and `combineTriggerModes` `allowsZeroTargets` / `maxTargets`.
5. CR 506.5 `attacksAlonePlus2Indestructible` declared-attacker check, CR 603.4 / 608.2h `fraConditionHolds` LKI fallback, CR 702.26b `attachedEquipmentAtResolution` phased-out `0`, and CR 707.2 `.copySelfNonlegendary` `eo.copiable`.
6. CR 707.10c / 115.3 / 115.7d `.copyCauseSpell` & `.venserSpell` retargeting, cross-slot `[A, B] -> [B, A]` swaps (`.twoPlayers` & `.twoNonlandsSharingType` revert), and CR 608.2b multi-target per-slot legality.
7. CR 303.4f–g / 111.8 Aura entry & token-copy non-return, pre-batch host snapshots, and two-pass `createPermanentCopyTokens` simultaneous batching.
8. CR 800.4 / 725.4 / 509.1g / 723.5 multiplayer combat-damage departure safety, empty `defendingPlayers` blocker-skip, monarch succession, third-party leave prompt revalidation, blocker-retention, and `playerControl`.
9. CR 500.4 `beginTurn` turn-start expiry, CR 611.2a–b / 702.26f `durationActive` & counter/zone expiry, CR 800.4c,i,m phased-out control-expiry exile & departed-player `PlayerRule` / `.untilEndOfNextTurnOf` expiry, and CR 614.12 Arwen `preBfOk`. -/
section Phase18EventAlignment

private def opp18 : PlayerId := ⟨1⟩

private def mustHold18 (label : String) (ok : Bool) : Bool :=
  if ok then true else panic! s!"Phase 18 guard failed: {label}"

private def mkThreePlayer18 (seed : UInt64 := 18) : Game :=
  let cfg : StartConfig := {
    seats := #[
      { name := "Chandra", deck := testRedDeck },
      { name := "Nissa", deck := testGreenDeck },
      { name := "Liliana", deck := testRedDeck }
    ]
    format := .constructed
    seed
    startingPlayer := some 0
  }
  match Start.start cfg with
  | .ok g => (keepOpeningHands g 20).advanceStep
  | .error e => panic! e

private def mkTwoHeadedGiant18 (seed : UInt64 := 180) : Game :=
  let cfg : StartConfig := {
    seats := #[
      { name := "Chandra", deck := testRedDeck, teammate := some ⟨1⟩ },
      { name := "Nissa", deck := testGreenDeck, teammate := some ⟨0⟩ },
      { name := "Liliana", deck := testRedDeck, teammate := some ⟨3⟩ },
      { name := "Jace", deck := testGreenDeck, teammate := some ⟨2⟩ }
    ]
    format := .constructed
    seed
    startingPlayer := some 0
  }
  match Start.start cfg with
  | .ok g => (keepOpeningHands g 30).advanceStep
  | .error e => panic! e

-- 1. Nested-batch `currentBatch` cause isolation, 0-event pause replay parity, & single-writer `.ringBearer` clear.
#guard
  -- 1a. Outer `withBatch none` wrapping inner `withBatch (some innerCause)` restores `none` after inner batch finishes!
  let g0 : Game := addPermanent (addPermanent afterDraw bear me me) hero me me
  let bId := (g0.battlefield.filter (·.name == bear.name))[0]!.id
  let hId := (g0.battlefield.filter (·.name == hero.name))[0]!.id
  let innerCause : EventCause := .oneShotEffect (some ⟨77⟩) (some bId) (some me)
  let fallbackCause : EventCause := .oneShotEffect (some ⟨88⟩) (some hId) (some me)
  let preIdx := g0.events.size
  let gIso : Game :=
    g0.withBatch none fun g =>
      let g := g.withBatch (some innerCause) fun g =>
        g.becomeTapped (g.object! bId)
      g.becomeTapped (g.object! hId) (cause := some fallbackCause)
  let tappedCauses := (gIso.events.extract preIdx gIso.events.size).filterMap fun e =>
    match e.change with
    | .rules (.permanent (.tapped eo _)) => eo.id.map (·, e.cause?)
    | _ => none
  let nestedCauseIsoOk : Bool :=
    tappedCauses == #[(bId, some innerCause), (hId, some fallbackCause)] &&
    gIso.currentBatch.isNone

  -- 1b. 0-event pause replay parity (`withBatch` pausing on `chooseReplacement` before recording any `RulesEvent`):
  let idDrawA : ReplacementId := { kind := .drawTwoExceptFirstDrawStep, object := some bId }
  let idDrawB : ReplacementId := { kind := .drawThreeExceptFirstDrawStep, object := some hId }
  let gDr0 : Game :=
    (g0.createEffect
      (.replacement { id := idDrawA, source := some bId, controller := some me, affectedPlayer := me,
                      kind := .replaceDraw me 2 false }) (cause := some testCause)).createEffect
      (.replacement { id := idDrawB, source := some hId, controller := some me, affectedPlayer := me,
                      kind := .replaceDraw me 3 false }) (cause := some testCause)
  let preZeroIdx := gDr0.events.size
  let gZeroPaused : Game :=
    gDr0.withBatch (some testCause) fun g =>
      g.draw me 1 (cause := some testCause)
  let zeroRulesInSlice :=
    !(gZeroPaused.events.extract preZeroIdx gZeroPaused.events.size).any (fun e =>
      match e.change with | .rules _ => true | _ => false)
  let zeroPauseOk : Bool :=
    zeroRulesInSlice &&
    gZeroPaused.currentBatch.isSome &&
    (match gZeroPaused.pending with | .chooseReplacement p cs => p == me && cs.size == 2 | _ => false) &&
    Game.replayEvents gZeroPaused.events == gZeroPaused
  let gZeroResumed : Game :=
    let g1 := mustApply gZeroPaused me (.chooseReplacement idDrawA)
    match g1.pending with
    | .chooseReplacement _ cs => mustApply g1 me (.chooseReplacement cs[0]!)
    | _ => g1
  let zeroResumedOk : Bool :=
    gZeroResumed.pending == .none &&
    gZeroResumed.currentBatch.isNone

  -- 1c. Single-writer `PermanentEvent.designation _ .ringBearer false` on zone departure & token `ceasedToExist`:
  let gRb0 : Game := g0.setRingBearer me (some bId) (cause := some testCause)
  let rbPreMoveIdx := gRb0.events.size
  let (gRbMoved, _) := gRb0.move bId (.graveyard me) none (verb := some .destroy) (cause := some testCause)
  let rbClearCountMove := (gRbMoved.events.extract rbPreMoveIdx gRbMoved.events.size).filter (fun e =>
    match e.change with
    | .rules (.permanent (.designation eo .ringBearer false)) => eo.id == some bId
    | _ => false) |>.size
  let gTok0 : Game := (g0.createToken me bear (cause := some testCause)).1
  let tokId := (gTok0.battlefield.filter (·.printed.isToken))[0]!.id
  let gTokRb : Game := gTok0.setRingBearer me (some tokId) (cause := some testCause)
  let tokPreCeaseIdx := gTokRb.events.size
  let gTokCeased : Game := gTokRb.ceaseToExist tokId (cause := some (.stateBased .tokenOutsideBattlefield))
  let rbClearCountCease := (gTokCeased.events.extract tokPreCeaseIdx gTokCeased.events.size).filter (fun e =>
    match e.change with
    | .rules (.permanent (.designation eo .ringBearer false)) => eo.id == some tokId
    | _ => false) |>.size
  let ringBearerSingleWriterOk : Bool :=
    rbClearCountMove == 1 && (gRbMoved.player me).ringBearerId.isNone &&
    rbClearCountCease == 1 && (gTokCeased.player me).ringBearerId.isNone

  mustHold18 "1a.nestedCauseIsoOk" nestedCauseIsoOk &&
  mustHold18 "1b.zeroPauseOk" zeroPauseOk &&
  mustHold18 "1b.zeroResumedOk" zeroResumedOk &&
  mustHold18 "1c.ringBearerSingleWriterOk" ringBearerSingleWriterOk &&
  mustHold18 "1.replay" ([gIso, gZeroPaused, gZeroResumed, gRbMoved, gTokCeased].all (fun g =>
    Game.replayEvents g.events == g && allRulesEventsClassified g))

-- 2. `outerPendingReplacements` / `endsWithPriorityGrant`, `runLinkedExileBatch` Pass 2, `shuffleSourceIntoLibrary`, & reflexive-sacrifice pause-safety.
#guard
  -- 2a. `outerPendingReplacements` with `endsWithPriorityGrant`: inner `finishAndGrantPriority` defers priority grant!
  let gOut0 : Game :=
    (afterDraw.change (.pushContinuationFrame {})).change
      (.continuation (.pushOuterPendingReplacement (.receivePriority opp18)))
  let idCnt1 : ReplacementId := { kind := .extraCounterOnPermanents, object := some ⟨500⟩, counterKind := some .plusOnePlusOne }
  let idCnt2 : ReplacementId := { kind := .multiplyCountersPut, object := some ⟨501⟩ }
  let gOutB : Game := addPermanent gOut0 bear me me
  let outBear := (gOutB.battlefield.filter (·.name == bear.name))[0]!.id
  let gOutB : Game :=
    (gOutB.createEffect (.replacement { id := idCnt1, affectedPlayer := me, kind := .modifyCountersPut none (some .plusOnePlusOne) 1 1 }) (cause := some testCause)).createEffect
      (.replacement { id := idCnt2, affectedPlayer := me, kind := .modifyCountersPut none (some .plusOnePlusOne) 0 3 }) (cause := some testCause)
  let gOutPaused : Game :=
    (gOutB.addPlusOnePlusOneTo (gOutB.object! outBear) 1 (cause := some testCause)).finishAndGrantPriority me
  let endsCheckOk : Bool :=
    PendingReplacement.endsWithPriorityGrant (.receivePriority opp18) &&
    PendingReplacement.endsWithPriorityGrant .finishFraChoice &&
    PendingReplacement.endsWithPriorityGrant (.seq (.gainLife me 1 none) (.receivePriority me)) &&
    !PendingReplacement.endsWithPriorityGrant (.gainLife me 1 none)
  let gOutDone : Game :=
    let g1 := mustApply gOutPaused me (.chooseReplacement idCnt1)
    match g1.pending with
    | .chooseReplacement _ cs => mustApply g1 me (.chooseReplacement cs[0]!)
    | _ => g1
  -- Non-granting oldest outer frame (`[0] = .gainLife`) + priority-granting newer outer frame (`[1]`) or inner `pendingReplacement`:
  -- `finishAndGrantPriority` must still see the existing priority grant and not append a duplicate `.receivePriority`.
  let gNewerOuter0 : Game :=
    ((afterDraw.change (.pushContinuationFrame {})).change
      (.continuation (.pushOuterPendingReplacement (.gainLife me 1 (some testCause))))).change
      (.continuation (.pushOuterPendingReplacement (.receivePriority opp18)))
  let gNewerOuterB : Game := addPermanent gNewerOuter0 bear me me
  let newerBear := (gNewerOuterB.battlefield.filter (·.name == bear.name))[0]!.id
  let gNewerOuterB : Game :=
    (gNewerOuterB.createEffect (.replacement { id := idCnt1, affectedPlayer := me, kind := .modifyCountersPut none (some .plusOnePlusOne) 1 1 }) (cause := some testCause)).createEffect
      (.replacement { id := idCnt2, affectedPlayer := me, kind := .modifyCountersPut none (some .plusOnePlusOne) 0 3 }) (cause := some testCause)
  let gNewerOuterPaused : Game :=
    (gNewerOuterB.addPlusOnePlusOneTo (gNewerOuterB.object! newerBear) 1 (cause := some testCause)).finishAndGrantPriority me
  let newerPausedNoDup : Bool :=
    !gNewerOuterPaused.pendingReplacement.any PendingReplacement.endsWithPriorityGrant
  let gNewerOuterDone : Game :=
    let g1 := mustApply gNewerOuterPaused me (.chooseReplacement idCnt1)
    match g1.pending with
    | .chooseReplacement _ cs => mustApply g1 me (.chooseReplacement cs[0]!)
    | _ => g1
  let gInnerGrants0 : Game :=
    (afterDraw.change (.pushContinuationFrame {})).change
      (.continuation (.pushOuterPendingReplacement (.gainLife me 1 (some testCause))))
  let gInnerGrantsB : Game := addPermanent gInnerGrants0 bear me me
  let innerBear := (gInnerGrantsB.battlefield.filter (·.name == bear.name))[0]!.id
  let gInnerGrantsB : Game :=
    (gInnerGrantsB.createEffect (.replacement { id := idCnt1, affectedPlayer := me, kind := .modifyCountersPut none (some .plusOnePlusOne) 1 1 }) (cause := some testCause)).createEffect
      (.replacement { id := idCnt2, affectedPlayer := me, kind := .modifyCountersPut none (some .plusOnePlusOne) 0 3 }) (cause := some testCause)
  let gInnerGrantsPaused0 : Game :=
    (gInnerGrantsB.addPlusOnePlusOneTo (gInnerGrantsB.object! innerBear) 1 (cause := some testCause)).chainPendingReplacement (.receivePriority opp18)
  let gInnerGrantsPaused : Game := gInnerGrantsPaused0.finishAndGrantPriority me
  let innerNoDup : Bool :=
    gInnerGrantsPaused.pendingReplacement == gInnerGrantsPaused0.pendingReplacement
  let outerDeferPriorityOk : Bool :=
    endsCheckOk && gOutDone.priority == opp18 &&
    newerPausedNoDup && gNewerOuterDone.priority == opp18 &&
    innerNoDup

  -- 2b. `runLinkedExileBatch` Pass 2: returning a permanent with an ETB trigger via `linkedExile` runs Pass 2!
  let etbBearDef : CardDef := { bear with name := "Phase18 Linked ETB Bear", triggeredAbilities := #[.onEnterDraw 1] }
  let gLk0 : Game := addPermanent (insertObject afterDraw etbBearDef me .exile) hero me me
  let exBearId := (gLk0.objects.filter (fun o => o.name == "Phase18 Linked ETB Bear" && o.zone == .exile))[0]!.id
  let hostId := (gLk0.battlefield.filter (·.name == hero.name))[0]!.id
  let gLk1 : Game := gLk0.changeObject hostId (.linkedExile #[exBearId])
  let (gLk2, _) := gLk1.move hostId (.graveyard me) none (verb := some .destroy) (cause := some testCause)
  let linkedPass2Ok : Bool :=
    (gLk2.permanentsOf me).any (·.name == "Phase18 Linked ETB Bear") &&
    gLk2.waitingTriggers.any (fun wt => wt.source.name == "Phase18 Linked ETB Bear")

  -- 2c. `shuffleSourceIntoLibrary` owner-based shuffle + draw continuation:
  let gSh0 : Game := addPermanent afterDraw bear opp18 me
  let shBear := (gSh0.battlefield.filter (·.name == bear.name))[0]!.id
  let gShDone : Game := gSh0.withBatch (some testCause) fun g =>
    g.shuffleSourceIntoLibrary (some shBear) (.draw me 1)
  let shuffleOwnerDrawOk : Bool :=
    gShDone.pending == .resolveRandom (.shuffleLibrary opp18) &&
    gShDone.afterRandom == .draw opp18 1 &&
    (gShDone.player opp18).library.any (fun id => (gShDone.object! id).name == bear.name)

  -- 2d. Reflexive-sacrifice (`TriggeredAbilities.applySacrifice` + `queueReflexive`) pauses on `chooseReplacement` BEFORE `putReflexiveTrigger`!
  let idDieA : ReplacementId := { kind := .finalityCounterExile, object := some ⟨601⟩ }
  let idDieB : ReplacementId := { kind := .exileOppDeath, object := some ⟨602⟩ }
  let planDef18 : CardDef := { name := "The Plan", types := #[.enchantment] }
  let gSac0 : Game := addPermanent (addPermanent afterDraw bear me me) planDef18 me me
  let sacPlanObj := (gSac0.battlefield.filter (·.name == "The Plan"))[0]!
  let sacPlan := sacPlanObj.id
  let gSac0 : Game :=
    (gSac0.createEffect (.replacement { id := idDieA, affectedPlayer := me, kind := .exileInsteadOfGraveyard (some sacPlan) false }) (cause := some testCause)).createEffect
      (.replacement { id := idDieB, affectedPlayer := me, kind := .exileInsteadOfGraveyard (some sacPlan) true }) (cause := some testCause)
  let gSacStacked : Game :=
    gSac0.putTriggeredAbilityOnStack me sacPlanObj .onFourthPlanIndestructible "fourth" (eventCause := some testCause)
  let preRefIdx := gSacStacked.events.size
  let gSacChosen : Game := gSacStacked.resolveTop
  let sacPausedBeforeReflexive : Bool :=
    (match gSacChosen.pending with | .chooseReplacement p cs => p == me && cs.size == 2 | _ => false) &&
    gSacChosen.waitingTriggers.isEmpty &&
    !(gSacChosen.events.extract preRefIdx gSacChosen.events.size).any (fun e =>
      match e.change with | .rules (.triggerQueue (.triggered ..)) => true | _ => false)
  let gSacAfterRep : Game := mustApply gSacChosen me (.chooseReplacement idDieA)
  let sacQueuedAfterRep : Bool :=
    gSacAfterRep.pending == .chooseTargets me &&
    gSacAfterRep.stack.size == 1

  mustHold18 "2a.outerDeferPriorityOk" outerDeferPriorityOk &&
  mustHold18 "2b.linkedPass2Ok" linkedPass2Ok &&
  mustHold18 "2c.shuffleOwnerDrawOk" shuffleOwnerDrawOk &&
  mustHold18 "2d.sacPausedBeforeReflexive" sacPausedBeforeReflexive &&
  mustHold18 "2d.sacQueuedAfterRep" sacQueuedAfterRep &&
  mustHold18 "2.replay" ([gOutPaused, gOutDone, gNewerOuterPaused, gNewerOuterDone, gInnerGrantsPaused, gLk2, gShDone, gSacChosen, gSacAfterRep].all (fun g =>
    Game.replayEvents g.events == g && allRulesEventsClassified g))

-- 3. CR 733.1 `.crew` / `.zemoBoastExile` & `reverseToProposalCheckpoint?` batch/linkedExile/lookedAt fidelity.
#guard
  let boat18 : CardDef := {
    name := "Phase18 Skiff"
    types := #[.artifact]
    subtypes := #["Vehicle"]
    power := some 4
    toughness := some 4
    crew := some 2
  }
  let gCr0 : Game := addPermanent (addPermanent afterDraw boat18 me me) bear me me
  let skiffId := (gCr0.battlefield.filter (·.name == "Phase18 Skiff"))[0]!.id
  let pilotId := (gCr0.battlefield.filter (·.name == bear.name))[0]!.id
  -- 3a. Accepting `.crew` taps `pilotId` inside a `.costAction` `EventCause.costPayment .tap` batch; declining reverses cleanly!
  let gCrAsk : Game := mustApply gCr0 me (.activate skiffId 0)
  let gCrPaid : Game := mustApply gCrAsk me (.choosePermanents #[pilotId])
  let crewPaidOk : Bool :=
    (gCrPaid.object! pilotId).status.tapped &&
    gCrPaid.stack.size == 1 &&
    gCrPaid.events.any (fun e =>
      match e.change, e.cause? with
      | .rules (.permanent (.tapped eo _)), some (.costPayment .tap p _) => eo.id == some pilotId && p == me
      | _, _ => false)
  let crewDeclineBlocked : Bool := !(gCrAsk.apply me .decline).isOk
  let gCrDec : Game := mustApply (gCrAsk.becomeTapped (gCrAsk.object! pilotId)) me .decline
  let crewDecOk : Bool :=
    crewDeclineBlocked &&
    gCrDec.stack.isEmpty &&
    gCrDec.proposedSpell.isNone &&
    gCrDec.nextObjectId == gCr0.nextObjectId

  -- 3b. Accepting `.zemoBoastExile` across TWO graveyard cards exiles both in a single `BatchId`!
  let zemo18 : CardDef := {
    name := "Phase18 Zemo"
    types := #[.creature]
    power := some 3
    toughness := some 3
    staticAbilities := #[.boast]
  }
  let blk8Def : CardDef := {
    name := "Phase18 Eight Black"
    manaCost := { symbols := Array.replicate 8 (.colored .black) }
    types := #[.creature]
    power := some 1
    toughness := some 1
  }
  let gZm0 : Game :=
    let g := addPermanent afterDraw zemo18 me me
    let g := insertObject (insertObject g blk8Def me (.graveyard me)) { blk8Def with name := "Phase18 Eight Black B" } me (.graveyard me)
    let z := (g.battlefield.filter (·.name == "Phase18 Zemo"))[0]!
    g.record (GameEvent.attacked g.turnNumber me (g.snapshot z) opp18)
  let zmId := (gZm0.battlefield.filter (·.name == "Phase18 Zemo"))[0]!.id
  let gy2 := (gZm0.player me).graveyard
  let preZmIdx := gZm0.events.size
  let gZmPaid : Game := mustApply (mustApply gZm0 me (.activate zmId 0)) me (.choosePermanents gy2)
  let zmBatches := (gZmPaid.events.extract preZmIdx gZmPaid.events.size).filterMap fun e =>
    match e.change with
    | .rules (.zone (.moved _ _ (.graveyard _) .exile _ _ _ _)) => e.batch
    | _ => none
  let zemoBatchOk : Bool :=
    zmBatches.size == 2 && zmBatches[0]! == zmBatches[1]! && gZmPaid.stack.size == 1

  -- 3c. `reverseToProposalCheckpoint?`: kept irreversible action with consecutive `.engine` events inside one `BatchId`,
  --     `.lookedAt` filtering of non-library `cardIds`, and `queuedLinkedExile` flush!
  let gRev0 : Game := addPermanent (insertObject afterDraw bear me .exile) hero me me
  let linkedCard := (gRev0.objects.filter (fun o => o.name == bear.name && o.zone == .exile))[0]!.id
  let hostHero := (gRev0.battlefield.filter (·.name == hero.name))[0]!.id
  let gRev0 : Game := gRev0.changeObject hostHero (.linkedExile #[linkedCard])
  let liveTop := (gRev0.player me).library.back!
  let gRevCkpt : Game := gRev0.change .saveProposalCheckpoint
  let (gRevTmp, revTmpObj) := gRevCkpt.allocObject bear me .stack (some me)
  let gIrrev : Game :=
    gRevTmp.withProposalAction (.manaAbility (some hostHero)) fun g =>
      g.withBatchCore (some (.costPayment .sacrifice me (some hostHero))) fun g =>
        let (g, _) := g.move hostHero (.graveyard me) none (verb := some .sacrifice) (actor := some me)
          (cause := some (.costPayment .sacrifice me (some hostHero)))
        let g := (g.logMsg "interleaved log 1").logMsg "interleaved log 2"
        let g := g.addMana me (.colored .red) 1 (cause := some (.costPayment .sacrifice me (some hostHero)))
        g.record (GameEvent.lookedAt g.turnNumber me #[liveTop, revTmpObj.id] (cause := some (.costPayment .sacrifice me (some hostHero))))
  let gReversed : Game :=
    match gIrrev.reverseToProposalCheckpoint? with
    | .ok g' => g'
    | .error e => panic! s!"reverse failed: {e}"
  let keptMoveAndManaBatches := (gReversed.events.extract gRev0.events.size gReversed.events.size).filterMap fun e =>
    match e.change with
    | .rules (.zone (.moved _ _ .battlefield (.graveyard _) _ _ _ _))
    | .rules (.player (.manaAdded ..)) => e.batch
    | _ => none
  let lookedFiltered := (gReversed.events.extract gRev0.events.size gReversed.events.size).any fun e =>
    match e.change with
    | .rules (.player (.lookedAt _ ids)) => ids == #[liveTop]
    | _ => false
  let revKeepOk : Bool :=
    keptMoveAndManaBatches.size == 2 &&
    keptMoveAndManaBatches[0]! == keptMoveAndManaBatches[1]! &&
    lookedFiltered &&
    gReversed.queuedLinkedExile.isEmpty &&
    (gReversed.permanentsOf me).any (·.name == bear.name)

  mustHold18 "3a.crewPaidOk" crewPaidOk &&
  mustHold18 "3a.crewDecOk" crewDecOk &&
  mustHold18 "3b.zemoBatchOk" zemoBatchOk &&
  mustHold18 "3c.revKeepOk" revKeepOk &&
  mustHold18 "3.replay" ([gCrPaid, gCrDec, gZmPaid, gReversed].all (fun g =>
    Game.replayEvents g.events == g && allRulesEventsClassified g))

-- 4. CR 603.2d / 603.3c–d multi-copy modal triggers, mandatory `count`-mode removal, `tapOrUntapNonland`, `hawkeyeModes`, & `combineTriggerModes`.
#guard
  -- 4a. Sequential multi-copy modal trigger announcement via `extraTriggerAnotherYouControl`:
  let modalEtbDef : CardDef := {
    bear with
    name := "Phase18 Modal ETB"
    fraTriggerModes := #[
      { resolution := .gainLife (.fixed 3), phrase := "You gain 3 life" },
      { resolution := .draw (.fixed 1), phrase := "Draw a card" }
    ]
    triggeredAbilities := #[
      .triggered .enter { resolution := .chooseTriggerModes 1, phrase := "Choose one —" } {}
    ]
  }
  let doublerDef : CardDef := {
    hero with
    name := "Phase18 Trigger Doubler"
    staticAbilities := #[.extraTriggerAnotherYouControl #[] #[.creature]]
  }
  let gMod0 : Game := insertObject (addPermanent afterDraw doublerDef me me) modalEtbDef me (.hand me)
  let modH := (gMod0.player me).hand.back!
  let (gMod1, _) := gMod0.putOntoBattlefield modH me (cause := some testCause)
  let gModP1 : Game := gMod1.receivePriority me
  let copy0PausedOk : Bool :=
    (match gModP1.pending with | .fraChoice p (.triggerModes _ 1 #[]) => p == me | _ => false) &&
    gModP1.stack.size == 1 &&
    gModP1.waitingTriggers.size == 1 &&
    gModP1.waitingTriggers[0]!.ordered
  let gModP2 : Game := mustApply gModP1 me (.chooseMode 0)
  let copy1PausedOk : Bool :=
    (match gModP2.pending with | .fraChoice p (.triggerModes _ 1 #[]) => p == me | _ => false) &&
    gModP2.stack.size == 2 &&
    gModP2.waitingTriggers.isEmpty
  let lifePreMod := (gMod0.player me).life
  let handPreMod := (gMod1.player me).hand.size
  let gModDone : Game := ((mustApply gModP2 me (.chooseMode 1)).resolveTop).resolveTop
  let bothResolvedOk : Bool :=
    (gModDone.player me).life == lifePreMod + 3 &&
    (gModDone.player me).hand.size == handPreMod + 1

  -- 4b. Mandatory `"choose two —"` (`chooseTriggerModes 2`) removed (`noLegalMode`) when only 1 mode is choosable!
  let oppEnchFilter : TargetFilter := {
    noun := "target enchantment an opponent controls"
    zone := .battlefield
    types := #[.enchantment]
    controller := .opponent
  }
  let choose2Def : CardDef := {
    bear with
    name := "Phase18 Choose Two"
    fraTriggerModes := #[
      { resolution := .gainLife (.fixed 2), phrase := "You gain 2 life" },
      { targeting := .of .oppArtifact, resolution := .destroy .target, phrase := "Destroy target artifact an opponent controls" },
      { targeting := .of (.filtered oppEnchFilter), resolution := .destroy .target, phrase := "Destroy target enchantment an opponent controls" }
    ]
    triggeredAbilities := #[
      .triggered .enter { resolution := .chooseTriggerModes 2, phrase := "Choose two —" } {}
    ]
  }
  let gCh2_0 : Game := addPermanent afterDraw choose2Def me me
  let ch2Src := (gCh2_0.battlefield.filter (·.name == "Phase18 Choose Two"))[0]!
  let preCh2 := gCh2_0.events.size
  let gCh2_1 : Game := gCh2_0.putTriggeredAbilityOnStack me ch2Src choose2Def.triggeredAbilities[0]! "enter" (eventCause := some testCause)
  let ch2RemovedOk : Bool :=
    gCh2_1.stack.isEmpty &&
    gCh2_1.pending == .none &&
    (gCh2_1.events.extract preCh2 gCh2_1.events.size).any (fun e => e.cause? == some (.gameRule .noLegalMode))

  -- 4c. `SharedTrigger.tapOrUntapNonland` announces mode + target ON STACK PLACEMENT (`CastEvent.announced`)!
  let tapUntapAb : TriggeredAbility := .triggered .enter (Effect.ofTrigger .tapOrUntapNonland) {}
  let tapUntapDef : CardDef := { bear with name := "Phase18 Twiddler", triggeredAbilities := #[tapUntapAb] }
  let gTw0 : Game := addPermanent (addPermanent afterDraw tapUntapDef me me) hero opp18 opp18
  let twSrc := (gTw0.battlefield.filter (·.name == "Phase18 Twiddler"))[0]!
  let oppHeroId := (gTw0.battlefield.filter (·.name == hero.name))[0]!.id
  let gTwStack : Game := gTw0.putTriggeredAbilityOnStack me twSrc tapUntapAb "enter" (eventCause := some testCause)
  let twModePromptOnStack : Bool :=
    match gTwStack.pending with
    | .fraChoice p (.triggerModes _ 1 #[]) => p == me
    | _ => false
  let gTwMode0 : Game := mustApply gTwStack me (.chooseMode 0)
  let twTargetPromptOnStack : Bool := gTwMode0.pending == .chooseTargets me
  let gTwTargeted : Game := mustApply gTwMode0 me (.target (.permanent oppHeroId))
  let gTwRes : Game := gTwTargeted.resolveTop
  let twOk : Bool := twModePromptOnStack && twTargetPromptOnStack && (gTwRes.object! oppHeroId).status.tapped

  -- 4d. Hawkeye Trick Arrows (`Resolution.mshReflexive .trickArrows 2`): prompts `.hawkeyeModes` on stack placement; declining keeps 0-mode ability on stack!
  let gHk0 : Game := addPermanent (addPermanent afterDraw bear me me) hero opp18 opp18
  let hkSrc := (gHk0.battlefield.filter (·.name == bear.name))[0]!
  let gHkStack : Game :=
    gHk0.putReflexiveTrigger me (some hkSrc.id)
      { resolution := .mshReflexive .trickArrows 2, phrase := "Choose up to 2 Trick Arrows modes" }
  let hkPromptOnStack : Bool :=
    match gHkStack.pending with
    | .fraChoice p (.hawkeyeModes 2 #[] (some _)) => p == me
    | _ => false
  let gHkZero : Game := mustApply gHkStack me .decline
  let hkZeroStaysOnStack : Bool :=
    gHkZero.stack.size == 1 &&
    gHkZero.pending == .none &&
    gHkZero.events.any (fun e => match e.change with | .rules (.cast (.announced _ #[] none #[])) => true | _ => false)
  let gHkZeroRes : Game := gHkZero.resolveTop

  -- 4e. `combineTriggerModes`: preserves `allowsZeroTargets` & sums `maxTargets` across chosen modes!
  let mOpt1 : Effect := { targeting := .of .creature, allowsZeroTargets := true, maxTargets := 1, resolution := .tap .target, phrase := "Tap up to one" }
  let mOpt2 : Effect := { targeting := .of .opponent, allowsZeroTargets := true, maxTargets := 2, resolution := .loseLife (.fixed 1) (.target .opponent), phrase := "Up to two opps" }
  let mMand : Effect := { targeting := .of .creature, allowsZeroTargets := false, maxTargets := 1, resolution := .untap .target, phrase := "Untap target" }
  let combBothOpt := Game.combineTriggerModes #[mOpt1, mOpt2] #[0, 1]
  let combMixed := Game.combineTriggerModes #[mOpt1, mMand] #[0, 1]
  let combineModesOk : Bool :=
    (match combBothOpt with | some e => e.allowsZeroTargets && e.maxTargets == 3 | none => false) &&
    (match combMixed with | some e => !e.allowsZeroTargets && e.maxTargets == 2 | none => false)

  mustHold18 "4a.copy0PausedOk" copy0PausedOk &&
  mustHold18 "4a.copy1PausedOk" copy1PausedOk &&
  mustHold18 "4a.bothResolvedOk" bothResolvedOk &&
  mustHold18 "4b.ch2RemovedOk" ch2RemovedOk &&
  mustHold18 "4c.twOk" twOk &&
  mustHold18 "4d.hkPromptOnStack" hkPromptOnStack &&
  mustHold18 "4d.hkZeroStaysOnStack" hkZeroStaysOnStack &&
  mustHold18 "4e.combineModesOk" combineModesOk &&
  mustHold18 "4.replay" ([gModP1, gModP2, gModDone, gCh2_1, gTwStack, gTwTargeted, gTwRes, gHkStack, gHkZero, gHkZeroRes].all (fun g =>
    Game.replayEvents g.events == g && allRulesEventsClassified g))

-- 5. CR 506.5 `attacksAlonePlus2Indestructible`, CR 603.4 / 608.2h `fraConditionHolds` LKI, CR 702.26b `attachedEquipmentAtResolution`, & CR 707.2 `.copySelfNonlegendary`.
#guard
  -- 5a. CR 506.5: `attacksAlonePlus2Indestructible` checks declared attacker count (`decls.size == 1`)!
  let lonerAb : TriggeredAbility := TriggeredAbility.onThisAttack Effect.thisAttackAttacksAlonePlus2Indestructible
  let lonerDef : CardDef := { bear with name := "Phase18 Loner", triggeredAbilities := #[lonerAb] }
  let gLn0 : Game := addPermanent (addPermanent afterDraw lonerDef me me) hero me me
  let lnId := (gLn0.battlefield.filter (·.name == "Phase18 Loner"))[0]!.id
  let hrId := (gLn0.battlefield.filter (·.name == hero.name))[0]!.id
  let gLnTwo : Game :=
    let g1 := gLn0.beginStep .beginningOfCombat
    let g1 := mustApply (mustApply g1 me .pass) opp18 .pass
    mustApply g1 me (.declareAttackers #[lnId, hrId] none #[] #[])
  let gLnOne : Game :=
    let g1 := gLn0.beginStep .beginningOfCombat
    let g1 := mustApply (mustApply g1 me .pass) opp18 .pass
    (mustApply g1 me (.declareAttackers #[lnId] none #[] #[])).resolveTop
  let lonerOk : Bool :=
    gLnTwo.stack.isEmpty &&
    gLnOne.power (gLnOne.object! lnId) == 4 &&
    gLnOne.hasIndestructible (gLnOne.object! lnId)

  -- 5b. CR 603.4 / 608.2h `fraConditionHolds` LKI fallback when `source` left `.battlefield`:
  let gLki0 : Game := addPermanent afterDraw bear me me
  let lkiId := (gLki0.battlefield.filter (·.name == bear.name))[0]!.id
  let gLki1 : Game := gLki0.recordPutCounters lkiId .plusOnePlusOne 1 (some me) (cause := some testCause)
  let snapWithCounter := gLki1.object! lkiId
  let (gLkiGone, _) := gLki1.move lkiId (.graveyard me) none (verb := some .destroy) (cause := some testCause)
  let lkiCondOk : Bool :=
    gLkiGone.fraConditionHolds me .sourceHasCounters (some snapWithCounter) none &&
    !gLkiGone.fraConditionHolds me .sourceHasCounters (some (gLki0.object! lkiId)) none

  -- 5c. CR 702.26b: `attachedEquipmentAtResolution` returns `0` when the creature is phased out on `.battlefield` (not `lastKnownPower` 4)!
  let eqDef18 : CardDef := { name := "Phase18 Blade", manaCost := ManaCost.empty, types := #[.artifact], subtypes := #["Equipment"] }
  let gEq0 : Game := addPermanent (addPermanent afterDraw { bear with name := "Phase18 Wielder", power := some 4 } me me) eqDef18 me me
  let wldId := (gEq0.battlefield.filter (·.name == "Phase18 Wielder"))[0]!.id
  let bldId := (gEq0.battlefield.filter (·.name == "Phase18 Blade"))[0]!.id
  let gEq1 : Game := gEq0.record (GameEvent.attached gEq0.turnNumber (gEq0.snapshot (gEq0.object! bldId)) wldId (cause := testCause))
  let gEqPhased : Game := gEq1.phaseOut (gEq1.object! wldId) (cause := some testCause)
  let eqPhasedZeroOk : Bool :=
    gEq1.attachedEquipmentAtResolution (some wldId) (some 4) == 1 &&
    gEqPhased.attachedEquipmentAtResolution (some wldId) (some 4) == 0

  -- 5d. CR 707.2 `.copySelfNonlegendary`: uses `eo.copiable.getD eo.toCardDef` when source became a copy and left `.battlefield`!
  let selfCopyAb : TriggeredAbility := .triggered .enter (Effect.ofTrigger .copySelfNonlegendary) {}
  let templateHeroDef : CardDef := {
    hero with
    name := "Phase18 Legendary Template"
    supertypes := #[.legendary]
    power := some 5
    toughness := some 6
    triggeredAbilities := #[selfCopyAb]
  }
  let gCp0 : Game := addPermanent (addPermanent afterDraw bear me me) templateHeroDef me me
  let origBear := (gCp0.battlefield.filter (·.name == bear.name))[0]!.id
  let tmplId := (gCp0.battlefield.filter (·.name == "Phase18 Legendary Template"))[0]!.id
  let gCp1 : Game := gCp0.withBatch (some testCause) fun g =>
    g.becomeCopyOf (g.object! origBear) (g.object! tmplId)
  let gCpStack : Game := gCp1.putTriggeredAbilityOnStack me (gCp1.object! origBear) selfCopyAb "enter" (eventCause := some testCause)
  let (gCpGone, _) := gCpStack.move origBear (.graveyard me) none (verb := some .destroy) (cause := some testCause)
  let gCpRes : Game := gCpGone.resolveTop
  let cpTokens := (gCpRes.permanentsOf me).filter (fun o => o.printed.isToken && o.name == "Phase18 Legendary Template")
  let copyCopiableLkiOk : Bool :=
    cpTokens.size == 2 &&
    cpTokens.all (fun t => gCpRes.power t == 5 && gCpRes.toughness t == 6 && !(gCpRes.supertypes t).contains .legendary)

  mustHold18 "5a.lonerOk" lonerOk &&
  mustHold18 "5b.lkiCondOk" lkiCondOk &&
  mustHold18 "5c.eqPhasedZeroOk" eqPhasedZeroOk &&
  mustHold18 "5d.copyCopiableLkiOk" copyCopiableLkiOk &&
  mustHold18 "5.replay" ([gLnTwo, gLnOne, gLkiGone, gEqPhased, gCpRes].all (fun g =>
    Game.replayEvents g.events == g && allRulesEventsClassified g))

-- 6. CR 707.10c / 115.3 / 115.7d `.copyCauseSpell` & `.venserSpell` retargeting, cross-slot `[A, B] -> [B, A]` swaps, & CR 608.2b multi-target legality.
#guard
  let pingDef18 : CardDef := { lightningBolt with name := "Phase18 Bolt", manaCost := ManaCost.empty }
  let gRt0 : Game := addPermanent (addPermanent afterDraw bear opp18 opp18) hero opp18 opp18
  let tBear := (gRt0.battlefield.filter (·.name == bear.name))[0]!.id
  let tHero := (gRt0.battlefield.filter (·.name == hero.name))[0]!.id
  let gRt0 : Game := insertObject gRt0 pingDef18 opp18 (.hand opp18)
  let boltH := (gRt0.player opp18).hand.back!
  let gRtCast : Game := mustApply (mustApply (gRt0.change (.priority opp18)) opp18 (.cast boltH)) opp18 (.target (.permanent tBear))
  let boltStackId := gRtCast.stack.back!.objectId

  -- 6a. `.venserSpell` copies opponent's targeted spell twice and prompts `.newTargetsForCopies #[c1, c2]`!
  let venserEff : Effect := {
    targeting := .of (.filtered { noun := "target instant or sorcery spell an opponent controls", zone := .stack, types := #[.instant, .sorcery], controller := .opponent })
    resolution := .frc .venserSpell
    phrase := "Copy target instant or sorcery spell an opponent controls twice. You may choose new targets for the copies."
  }
  let gVenPrompt : Game := gRtCast.applyFrc me venserEff .venserSpell #[Target.card boltStackId] none
  let venCopiesPromptOk : Bool :=
    match gVenPrompt.pending with
    | .fraChoice p (.newTargetsForCopies cs) => p == me && cs.size == 2
    | _ => false
  let gVenRetargeted : Game :=
    let g1 := mustApply gVenPrompt me (.choosePermanents #[tHero])
    mustApply g1 me .decline

  -- `.copyCauseSpell` also prompts `.newTargetsForCopies #[copyId]`!
  let copyCauseEff : Effect := { resolution := .copyCauseSpell, phrase := "Copy that spell" }
  let abId : ObjectId := ⟨gRtCast.nextObjectId⟩
  let gCauseStacked : Game :=
    gRtCast.record (GameEvent.triggerPutOnStack gRtCast.turnNumber abId (gRtCast.snapshot (gRtCast.object! tBear)) me
      (spec := { abilityEffect := some copyCauseEff, sourceId := some tBear, fraCauseId := some boltStackId })
      (cause := testCause))
  let gCausePrompt : Game := gCauseStacked.resolveTop
  let copyCausePromptOk : Bool :=
    match gCausePrompt.pending with
    | .fraChoice p (.newTargetsForCopies cs) => p == me && cs.size == 1
    | _ => false
  let gCauseDone : Game := mustApply gCausePrompt me .decline

  -- 6b. Cross-slot `[A, B] -> [B, A]` swap on `.twoNonlandsSharingType`, plus revert when slot 1 is declined on incompatible type!
  let exchSpellDef : CardDef := {
    name := "Phase18 Swap Control"
    manaCost := ManaCost.empty
    types := #[.sorcery]
    spellEffect := some {
      targeting := .of .twoNonlandsSharingType
      resolution := .exchangeControl
      phrase := "Exchange control of two target nonland permanents that share a card type"
    }
  }
  let relicOnlyDef : CardDef := { name := "Phase18 Pure Relic", manaCost := ManaCost.empty, types := #[.artifact] }
  let relicTwoDef : CardDef := { name := "Phase18 Pure Relic 2", manaCost := ManaCost.empty, types := #[.artifact] }
  let gSw0 : Game :=
    insertObject (addPermanent (addPermanent (addPermanent (addPermanent afterDraw bear me me) hero opp18 opp18)
      relicOnlyDef me me) relicTwoDef opp18 opp18) exchSpellDef me (.hand me)
  let swBear := (gSw0.battlefield.filter (·.name == bear.name))[0]!.id
  let swHero := (gSw0.battlefield.filter (·.name == hero.name))[0]!.id
  let swRel1 := (gSw0.battlefield.filter (·.name == "Phase18 Pure Relic"))[0]!.id
  let swRel2 := (gSw0.battlefield.filter (·.name == "Phase18 Pure Relic 2"))[0]!.id
  let swCard := (gSw0.player me).hand.back!
  let gSwCast : Game :=
    mustApply (mustApply (mustApply gSw0 me (.cast swCard)) me (.target (.permanent swBear))) me (.target (.permanent swHero))
  let swSpellId := gSwCast.stack.back!.objectId
  -- Swap `[swBear, swHero]` -> `[swHero, swBear]` via `.newTargetsForCopies`:
  let gSwPrompt : Game := gSwCast.beginFraChoice me (.newTargetsForCopies #[swSpellId]) "retarget"
  let gSwSwapped : Game :=
    mustApply (mustApply gSwPrompt me (.choosePermanents #[swHero])) me (.choosePermanents #[swBear])
  let swapTargetsOk : Bool :=
    (gSwSwapped.stackEntry? swSpellId).map (·.targets) == some #[Target.permanent swHero, Target.permanent swBear]
  -- Incomplete edit: pick `swRel1` (artifact only) for slot 0, then `.decline` slot 1 (`swBear` is creature only) => reverts to `[swHero, swBear]`!
  let gSwInc0 : Game := gSwSwapped.beginFraChoice me (.newTargetsForCopies #[swSpellId]) "retarget incomplete"
  let gSwReverted : Game :=
    mustApply (mustApply gSwInc0 me (.choosePermanents #[swRel1])) me .decline
  let revertIncompleteOk : Bool :=
    (gSwReverted.stackEntry? swSpellId).map (·.targets) == some #[Target.permanent swHero, Target.permanent swBear]
  -- Valid switch to `[swRel1, swRel2]` works:
  let gSwValidArt : Game :=
    let g1 := gSwReverted.beginFraChoice me (.newTargetsForCopies #[swSpellId]) "retarget artifacts"
    mustApply (mustApply g1 me (.choosePermanents #[swRel1])) me (.choosePermanents #[swRel2])
  let validArtRetargetOk : Bool :=
    (gSwValidArt.stackEntry? swSpellId).map (·.targets) == some #[Target.permanent swRel1, Target.permanent swRel2]

  -- 6c. CR 608.2b multi-target per-slot legality: `.destroyEachTarget` skips target that gained hexproof while destroying remaining legal target!
  let destroyTwoEff : Effect := {
    targeting := .of (.multi #[TargetFilter.oppCreatureOrPlaneswalker, TargetFilter.oppCreatureOrPlaneswalker] #[])
    resolution := .destroyEachTarget
    phrase := "Destroy two target creatures or planeswalkers an opponent controls"
  }
  let gMt0 : Game := addPermanent (addPermanent afterDraw bear opp18 opp18) hero opp18 opp18
  let mtBear := (gMt0.battlefield.filter (·.name == bear.name))[0]!.id
  let mtHero := (gMt0.battlefield.filter (·.name == hero.name))[0]!.id
  let gMtHex : Game := gMt0.createEffect (.keywordsUntilEot mtBear Keyword.hexproof) (cause := some testCause)
  let gMtRes : Game := gMtHex.applyFra me destroyTwoEff .destroyEachTarget #[Target.permanent mtBear, Target.permanent mtHero] none
  let multiTargetPerSlotOk : Bool :=
    (gMtRes.findObject? mtBear).any (·.isOnBattlefield) &&
    !(gMtRes.findObject? mtHero).any (·.isOnBattlefield)

  mustHold18 "6a.venCopiesPromptOk" venCopiesPromptOk &&
  mustHold18 "6a.copyCausePromptOk" copyCausePromptOk &&
  mustHold18 "6b.swapTargetsOk" swapTargetsOk &&
  mustHold18 "6b.revertIncompleteOk" revertIncompleteOk &&
  mustHold18 "6b.validArtRetargetOk" validArtRetargetOk &&
  mustHold18 "6c.multiTargetPerSlotOk" multiTargetPerSlotOk &&
  mustHold18 "6.replay" ([gVenPrompt, gVenRetargeted, gCauseDone, gSwSwapped, gSwReverted, gSwValidArt, gMtRes].all (fun g =>
    Game.replayEvents g.events == g && allRulesEventsClassified g))

-- 7. CR 303.4f–g / 111.8 Aura entry & token-copy non-return, pre-batch host snapshots, & two-pass `createPermanentCopyTokens`.
#guard
  let aura18Def : CardDef := aura "Phase18 Aura" ManaCost.empty "Enchant creature"
  -- 7a1. Casting an Aura whose target leaves `.battlefield` before resolution fizzles (`removedOnResolution`), never entering unattached!
  let gAu0 : Game := insertObject (addPermanent afterDraw bear me me) aura18Def me (.hand me)
  let auHost := (gAu0.battlefield.filter (·.name == bear.name))[0]!.id
  let auCard := (gAu0.player me).hand.back!
  let gAuCast : Game := mustApply (mustApply gAu0 me (.cast auCard)) me (.target (.permanent auHost))
  let (gAuHostGone, _) := gAuCast.move auHost .exile none (cause := some testCause)
  let preAuRes := gAuHostGone.events.size
  let gAuFizzled : Game := gAuHostGone.resolveTop
  let auraFizzleOk : Bool :=
    !(gAuFizzled.permanentsOf me).any (·.name == "Phase18 Aura") &&
    (gAuFizzled.player me).graveyard.any (fun id => (gAuFizzled.object! id).name == "Phase18 Aura") &&
    (gAuFizzled.events.extract preAuRes gAuFizzled.events.size).any (fun e =>
      match e.change with | .rules (.stackObject (.removedOnResolution ..)) => true | _ => false)

  -- 7a2. CR 303.4f/g: `createPermanentCopyTokens` on an Aura template when NO creature is on `.battlefield` creates 0 tokens!
  let gAuTokEmpty : Game := afterDraw.createPermanentCopyTokens me aura18Def 2 (cause := some testCause)
  let auraTokenNoHostOk : Bool :=
    !(gAuTokEmpty.permanentsOf me).any (·.name == "Phase18 Aura")

  -- 7a3. CR 111.8: token `isCopy := true` exiled by `.exileThenReturnYouControl` ceases to exist and does NOT return to `.battlefield`!
  let (gTk0, tokCopyObj) := afterDraw.createToken me bear (cause := some testCause)
  let gTkFlicker : Game :=
    gTk0.applyUnified me
      { targeting := .of (.filtered TargetFilter.creatureYouControl)
        resolution := .exileThenReturnYouControl
        phrase := "Exile target creature you control, then return it to the battlefield" }
      #[Target.permanent tokCopyObj.id]
  let gTkChecked : Game := gTkFlicker.checkSBA
  let tokenCopyNoReturnOk : Bool :=
    !(gTkChecked.permanentsOf me).any (·.name == bear.name)

  -- 7c. Two-pass `createPermanentCopyTokens` (`remaining == 2`): both tokens enter in the same batch before Pass 2 haste + delayed sacrifice,
  --     and temporary `ContinuationFrame` is popped cleanly!
  let anotherEntersWatcherDef : CardDef := {
    hero with
    name := "Phase18 Co-Enter Copy"
    triggeredAbilities := #[
      .triggered .anotherCreatureYouControlEnters
        { resolution := .gainLife (.fixed 1), phrase := "Whenever another creature you control enters, you gain 1 life" } {}
    ]
  }
  let preContSize := afterDraw.continuations.size
  let preCpBatchIdx := afterDraw.events.size
  let gTwoPass : Game := afterDraw.createPermanentCopyTokens me anotherEntersWatcherDef 2 (cause := some testCause)
  let createdBatches := (gTwoPass.events.extract preCpBatchIdx gTwoPass.events.size).filterMap fun e =>
    match e.change with
    | .rules (.zone (.created ..)) => e.batch
    | _ => none
  -- Both copies entered simultaneously in Pass 1, so each sees the OTHER enter (`waitingTriggers.size == 2`), both have haste, and 2 delayed triggers!
  let twoPassCopies := (gTwoPass.permanentsOf me).filter (·.name == "Phase18 Co-Enter Copy")
  let twoPassCopyOk : Bool :=
    gTwoPass.continuations.size == preContSize &&
    createdBatches.size == 2 && createdBatches[0]! == createdBatches[1]! &&
    twoPassCopies.size == 2 &&
    twoPassCopies.all (gTwoPass.hasHaste ·) &&
    gTwoPass.delayedTriggers.size == 2 &&
    gTwoPass.waitingTriggers.size == 2

  mustHold18 "7a1.auraFizzleOk" auraFizzleOk &&
  mustHold18 "7a2.auraTokenNoHostOk" auraTokenNoHostOk &&
  mustHold18 "7a3.tokenCopyNoReturnOk" tokenCopyNoReturnOk &&
  mustHold18 "7c.twoPassCopyOk" twoPassCopyOk &&
  mustHold18 "7.replay" ([gAuFizzled, gAuTokEmpty, gTkChecked, gTwoPass].all (fun g =>
    Game.replayEvents g.events == g && allRulesEventsClassified g))

-- 8. CR 800.4 / 725.4 / 509.1g / 723.5 multiplayer combat, monarch, prompt-revalidation, blocker-retention, & `playerControl`.
#guard
  let g3Base : Game := mkThreePlayer18 28
  -- 8a. `dealAssignedCombatDamage` survives a blocker's controller conceding during `Pending.assignCombatDamage _ false`!
  let multiBlkDef18 : CardDef := { bear with name := "Phase18 Multi Blocker", power := some 3, toughness := some 5 }
  let gCd0 : Game :=
    addPermanent (addPermanent (addPermanent (addPermanent g3Base bear ⟨0⟩ ⟨0⟩) hero ⟨0⟩ ⟨0⟩)
      multiBlkDef18 ⟨1⟩ ⟨1⟩) { bear with name := "Atk vs P2" } ⟨0⟩ ⟨0⟩
  let ca1 := (gCd0.battlefield.filter (·.name == bear.name))[0]!.id
  let ca2 := (gCd0.battlefield.filter (·.name == hero.name))[0]!.id
  let ca3 := (gCd0.battlefield.filter (·.name == "Atk vs P2"))[0]!.id
  let cmb := (gCd0.battlefield.filter (·.name == "Phase18 Multi Blocker"))[0]!.id
  let gCd1 : Game :=
    let g1 := gCd0.beginStep .beginningOfCombat
    let g1 := mustApply (mustApply (mustApply g1 ⟨0⟩ .pass) ⟨1⟩ .pass) ⟨2⟩ .pass
    let g1 := mustApply g1 ⟨0⟩ (.declareAttackers #[ca1, ca2, ca3] none #[some ⟨1⟩, some ⟨1⟩, some ⟨2⟩] #[])
    let g1 := mustApply (mustApply (mustApply g1 ⟨0⟩ .pass) ⟨1⟩ .pass) ⟨2⟩ .pass
    let g1 := mustApply g1 ⟨1⟩ (.declareBlockers #[(cmb, ca1), (cmb, ca2)])
    let g1 := mustApply g1 ⟨2⟩ (.declareBlockers #[])
    mustApply (mustApply (mustApply g1 ⟨0⟩ .pass) ⟨1⟩ .pass) ⟨2⟩ .pass
  -- `gCd1.pending == .assignCombatDamage ⟨1⟩ false`; now `⟨1⟩` concedes!
  let p2LifePre := (gCd1.player ⟨2⟩).life
  let gCdConcede : Game := gCd1.concede ⟨1⟩
  let combatDepartSafeOk : Bool :=
    gCd1.pending == .assignCombatDamage ⟨1⟩ false &&
    gCdConcede.pending == .none &&
    (gCdConcede.player ⟨2⟩).life == p2LifePre - 2

  -- 8b. `beginStep .declareBlockers` when attacked player `⟨1⟩` conceded before `.declareBlockers`: skips `Pending.declareBlockers`!
  let gDb0 : Game := addPermanent g3Base bear ⟨0⟩ ⟨0⟩
  let dbAtk := (gDb0.battlefield.filter (·.name == bear.name))[0]!.id
  let gDb1 : Game :=
    let g1 := gDb0.beginStep .beginningOfCombat
    let g1 := mustApply (mustApply (mustApply g1 ⟨0⟩ .pass) ⟨1⟩ .pass) ⟨2⟩ .pass
    mustApply g1 ⟨0⟩ (.declareAttackers #[dbAtk] none #[some ⟨1⟩] #[])
  let gDbConceded : Game := gDb1.concede ⟨1⟩
  let gDbStep : Game := mustApply (mustApply gDbConceded ⟨0⟩ .pass) ⟨2⟩ .pass
  let skipBlockersEmptyDefOk : Bool :=
    gDbStep.step == .declareBlockers &&
    gDbStep.pending == .none &&
    gDbStep.blockersQueue.isEmpty

  -- 8c. CR 725.4 monarch succession on departure:
  -- (i) `⟨0⟩` active, `⟨1⟩` monarch -> `⟨1⟩` concedes => `⟨0⟩` (`activePlayer`) becomes monarch!
  let gMonA : Game := (g3Base.becomeMonarch ⟨1⟩).concede ⟨1⟩
  -- (ii) `⟨0⟩` active AND monarch -> `⟨0⟩` concedes => `⟨1⟩` (`nextLiving ⟨0⟩`) becomes monarch!
  let gMonB : Game := (g3Base.becomeMonarch ⟨0⟩).concede ⟨0⟩
  let monarchSuccessionOk : Bool :=
    (gMonA.player ⟨0⟩).isMonarch && !(gMonA.player ⟨1⟩).isMonarch &&
    (gMonB.player ⟨1⟩).isMonarch && !(gMonB.player ⟨0⟩).isMonarch

  -- 8d. Prompt revalidation on third-party departure (`redirectPendingAfterLeave` & `announceGift`):
  let giftSpellDef : CardDef := {
    name := "Phase18 Gift Card"
    manaCost := ManaCost.empty
    types := #[.instant]
    giftTreasure := true
    spellEffect := some { resolution := .draw (.fixed 1), phrase := "Draw a card" }
  }
  let gGf0 : Game := (insertObject g3Base giftSpellDef ⟨0⟩ (.hand ⟨0⟩)).concede ⟨1⟩
  let gfH := (gGf0.player ⟨0⟩).hand.back!
  let gGfAsk : Game := mustApply gGf0 ⟨0⟩ (.cast gfH)
  let departedGiftRejected : Bool := !(gGfAsk.applyAction ⟨0⟩ (.announceGift (some ⟨1⟩))).isOk
  let gGfValid : Game := mustApply gGfAsk ⟨0⟩ (.announceGift (some ⟨2⟩))

  -- Stacked trigger waiting on `.chooseTargets ⟨0⟩` whose only legal target belonged to `⟨1⟩` is removed when `⟨1⟩` concedes!
  let killOppCrAb : TriggeredAbility :=
    .triggered .enter { targeting := .of .oppCreature, resolution := .destroy .target, phrase := "Destroy target creature an opponent controls" } {}
  let gTg0 : Game := addPermanent (addPermanent g3Base { bear with name := "Phase18 Hunter", triggeredAbilities := #[killOppCrAb] } ⟨0⟩ ⟨0⟩) bear ⟨1⟩ ⟨1⟩
  let hntObj := (gTg0.battlefield.filter (·.name == "Phase18 Hunter"))[0]!
  let gTgPrompt : Game := (gTg0.putTriggeredAbilityOnStack ⟨0⟩ hntObj killOppCrAb "enter" (eventCause := some testCause)).promptTriggerTargetsIfNeeded
  let gTgConceded : Game := gTgPrompt.concede ⟨1⟩
  let triggerTargetLeaveClearedOk : Bool :=
    gTgPrompt.pending == .chooseTargets ⟨0⟩ &&
    gTgConceded.pending == .none &&
    gTgConceded.stack.isEmpty

  -- 8e. CR 509.1g blocker-retention: after `blk` blocks `atk` and `atk` leaves combat, `!blk.status.blocking.isEmpty && (g.creaturesBlockedBy blk).isEmpty`!
  let gBr0 : Game := addPermanent (addPermanent afterDraw bear me me) hero opp18 opp18
  let brAtk := (gBr0.battlefield.filter (·.name == bear.name))[0]!.id
  let brBlk := (gBr0.battlefield.filter (·.name == hero.name))[0]!.id
  let gBr1 : Game :=
    let g1 := gBr0.beginStep .beginningOfCombat
    let g1 := mustApply (mustApply g1 me .pass) opp18 .pass
    let g1 := mustApply g1 me (.declareAttackers #[brAtk] none #[] #[])
    let g1 := mustApply (mustApply g1 me .pass) opp18 .pass
    mustApply g1 opp18 (.declareBlockers #[(brBlk, brAtk)])
  let (gBrExiled, _) := gBr1.move brAtk .exile none (cause := some testCause)
  let blkObj := gBrExiled.object! brBlk
  let blockerRetentionOk : Bool :=
    !blkObj.status.blocking.isEmpty &&
    (gBrExiled.creaturesBlockedBy blkObj).isEmpty &&
    (gBrExiled.blockersOf brAtk).isEmpty

  -- 8f. CR 723.5 `playerControl`: `⟨0⟩` controlling `⟨1⟩` makes `⟨1⟩`'s priority/choice decisions, while only `⟨1⟩` (`rawActor`) may concede `⟨1⟩`!
  let gPc0 : Game := (g3Base.createEffect (.playerControl ⟨0⟩ ⟨1⟩ false) (cause := some testCause)).change (.priority ⟨1⟩)
  let controlledActorOk : Bool :=
    gPc0.actor == some ⟨0⟩ &&
    gPc0.rawActor == some ⟨1⟩ &&
    !(gPc0.applyAction ⟨1⟩ .pass).isOk &&
    (gPc0.applyAction ⟨0⟩ .concede).isOk
  let gPcPassedByController : Game := mustApply gPc0 ⟨0⟩ .pass
  let gPcControlledConcedes : Game := mustApply gPc0 ⟨1⟩ .concede
  let playerControlOk : Bool :=
    controlledActorOk &&
    (gPcControlledConcedes.player ⟨1⟩).leftTheGame &&
    !(gPcControlledConcedes.player ⟨0⟩).leftTheGame

  mustHold18 "8a.combatDepartSafeOk" combatDepartSafeOk &&
  mustHold18 "8b.skipBlockersEmptyDefOk" skipBlockersEmptyDefOk &&
  mustHold18 "8c.monarchSuccessionOk" monarchSuccessionOk &&
  mustHold18 "8d.departedGiftRejected" departedGiftRejected &&
  mustHold18 "8d.triggerTargetLeaveClearedOk" triggerTargetLeaveClearedOk &&
  mustHold18 "8e.blockerRetentionOk" blockerRetentionOk &&
  mustHold18 "8f.playerControlOk" playerControlOk &&
  mustHold18 "8.replay" ([gCdConcede, gDbStep, gMonA, gMonB, gGfValid, gTgConceded, gBrExiled, gPcPassedByController, gPcControlledConcedes].all (fun g =>
    Game.replayEvents g.events == g && allRulesEventsClassified g))

-- 9. CR 500.4 `beginTurn` turn-start expiry, CR 611.2a–b / 702.26f `durationActive` & counter/zone expiry, CR 800.4c,i,m phased-out control-expiry exile, & CR 614.12 Arwen `preBfOk`.
#guard
  -- 9a. CR 500.4: `.fraEmblemUntilTurnOf` and `goaded` expire in `beginTurn` BEFORE `phaseBegan .beginning`!
  let embCard : CardDef := { name := "Phase18 Sculptor Emblem", types := #[] }
  let gBt0 : Game := addPermanent (insertObject afterDraw embCard me .command) bear opp18 opp18
  let embId := (gBt0.objects.filter (fun o => o.name == "Phase18 Sculptor Emblem" && o.zone == .command))[0]!.id
  let goadBear := (gBt0.battlefield.filter (·.name == bear.name))[0]!.id
  let gBt1 : Game :=
    (gBt0.createEffect (.fraEmblemUntilTurnOf embId opp18) (cause := some testCause)).record
      (GameEvent.designation gBt0.turnNumber (gBt0.snapshot (gBt0.object! goadBear)) (.goaded opp18) true (cause := testCause))
  let preBtIdx := gBt1.events.size
  let gBt2 : Game := gBt1.startNextTurnCore true
  let btSlice := gBt2.events.extract preBtIdx gBt2.events.size
  let ceaseIdx? := btSlice.findIdx? (fun e => match e.change with | .rules (.zone (.ceasedToExist eo)) => eo.id == some embId | _ => false)
  let goadClearIdx? := btSlice.findIdx? (fun e => match e.change with | .rules (.permanent (.designation _ (.goaded p) false)) => p == opp18 | _ => false)
  let phaseBeganIdx? := btSlice.findIdx? (fun e => match e.change with | .rules (.turn (.phaseBegan .beginning)) => true | _ => false)
  let turnStartBeforePhaseOk : Bool :=
    match ceaseIdx?, goadClearIdx?, phaseBeganIdx? with
    | some ci, some gi, some pi => ci < pi && gi < pi && (gBt2.findObject? embId).isNone
    | _, _, _ => false

  -- 9b. CR 611.2b / 702.26f `durationActive` + `.whileSourceHasCounter` & `.whileInZone` expiration events:
  let gDu0 : Game := addPermanent (addPermanent (insertObject afterDraw lightningBolt me .exile) bear me me) hero opp18 opp18
  let duSrc := (gDu0.battlefield.filter (·.name == bear.name))[0]!.id
  let duTgt := (gDu0.battlefield.filter (·.name == hero.name))[0]!.id
  let duExCard := (gDu0.objects.filter (fun o => o.name == lightningBolt.name && o.zone == .exile))[0]!.id
  let gDu1 : Game := gDu0.recordPutCounters duSrc .plusOnePlusOne 1 (some me) (cause := some testCause)
  let gDu1 : Game :=
    ((gDu1.createEffect (.cantUntapWhileSource duTgt duSrc) (cause := some testCause)).createEffect
      (.layered (.objects #[duTgt]) (.ptModify 2 2) (.whileSourceHasCounter duSrc .plusOnePlusOne)) (cause := some testCause)).createEffect
      (.permission (some me) (.flashback duExCard) (.whileInZone duExCard .exile)) (cause := some testCause)
  let activePrePhase := gDu1.hostCantBecomeUntapped (gDu1.object! duTgt) && gDu1.power (gDu1.object! duTgt) == 4
  let gDuPhased : Game := gDu1.record (GameEvent.phasedOut gDu1.turnNumber (gDu1.snapshot (gDu1.object! duSrc)) false (cause := testCause))
  let inactiveWhilePhased := !gDuPhased.hostCantBecomeUntapped (gDuPhased.object! duTgt) && gDuPhased.power (gDuPhased.object! duTgt) == 2
  let gDuPhasedIn : Game := gDuPhased.record (GameEvent.phasedIn gDuPhased.turnNumber (gDuPhased.snapshot (gDuPhased.object! duSrc)) (cause := testCause))
  let gDuCounterRemoved : Game := gDuPhasedIn.recordRemoveCounters duSrc .plusOnePlusOne 1 (some me) (cause := some testCause)
  let (gDuExMoved, _) := gDuCounterRemoved.move duExCard (.graveyard me) none (cause := some testCause)
  let (gDuSrcMoved, _) := gDuExMoved.move duSrc (.graveyard me) none (verb := some .destroy) (cause := some testCause)
  let durationAndExpiryOk : Bool :=
    activePrePhase &&
    inactiveWhilePhased &&
    gDuCounterRemoved.power (gDuCounterRemoved.object! duTgt) == 2 &&
    gDuSrcMoved.activeEffects.isEmpty

  -- 9c. CR 800.4c,i,m & CR 702.26d: phased-out stolen permanent whose owner left is exiled at `clearEOT`,
  --     and departed player's `.untilEndOfTurn` `PlayerRule`s + `.untilEndOfNextTurnOf` copy effects expire!
  let g3Ph : Game := mkThreePlayer18 39
  let g3Ph0 : Game := addPermanent (addPermanent g3Ph bear ⟨0⟩ ⟨2⟩) hero ⟨0⟩ ⟨0⟩
  let p2Bear := (g3Ph0.battlefield.filter (·.name == bear.name))[0]!.id
  let p0Hero := (g3Ph0.battlefield.filter (·.name == hero.name))[0]!.id
  let g3Ph1 : Game :=
    (((g3Ph0.changeControl (g3Ph0.object! p2Bear) ⟨1⟩ (untilEot := true) (cause := some testCause)).createEffect
      (.playerRule ⟨2⟩ (.additionalLands 1) .untilEndOfTurn) (cause := some testCause)).createEffect
      (.layered (.objects #[p0Hero]) (.copy bear) (.untilEndOfNextTurnOf ⟨2⟩)) (cause := some testCause))
  let g3Ph2 : Game := g3Ph1.concede ⟨2⟩
  -- Phase out `p2Bear` under `⟨1⟩`'s temporary control, then run `clearEOT` AND `expireUntilNextTurnEffects ⟨2⟩`:
  let g3Ph3 : Game := g3Ph2.record (GameEvent.phasedOut g3Ph2.turnNumber (g3Ph2.snapshot (g3Ph2.object! p2Bear)) false (cause := testCause))
  let g3PhEot : Game := g3Ph3.clearEOT
  let g3PhNext : Game := g3PhEot.expireUntilNextTurnEffects ⟨2⟩
  let phasedControlAndDepartedRulesOk : Bool :=
    (g3PhEot.object! (g3PhEot.followMoved p2Bear)).zone == .exile &&
    !g3PhNext.activeEffects.any (fun (_, s) =>
      match s with
      | .playerRule q _ _ => q == ⟨2⟩
      | .layered _ (.copy ..) (.untilEndOfNextTurnOf q) => q == ⟨2⟩
      | _ => false) &&
    (g3PhNext.object! p0Hero).name == hero.name

  -- 9d. CR 614.12 Arwen (`othersEnterWithPlusOneEqualToughness`) simultaneous batch vs subsequent entry:
  let arwen18 : CardDef := { bear with name := "Phase18 Arwen", toughness := some 3, othersEnterWithPlusOneEqualToughness := true }
  let gArw0 : Game := insertObject (insertObject (insertObject afterDraw arwen18 me (.hand me)) bear me (.hand me))
    { bear with name := "Phase18 Later Bear" } me (.hand me)
  let hIds := (gArw0.player me).hand
  let laterId := hIds.back!
  let simBearId := hIds[hIds.size - 2]!
  let arwId := hIds[hIds.size - 3]!
  let gArwSim : Game :=
    gArw0.withBatch (some testCause) fun g =>
      let (g, _) := g.putOntoBattlefield arwId me (cause := some testCause)
      (g.putOntoBattlefield simBearId me (cause := some testCause)).1
  let (gArwSeq, _) := gArwSim.putOntoBattlefield laterId me (cause := some testCause)
  let simBearPerm := (gArwSeq.permanentsOf me).filter (·.name == bear.name)
  let laterBearPerm := (gArwSeq.permanentsOf me).filter (·.name == "Phase18 Later Bear")
  let arwenPreBfOk : Bool :=
    simBearPerm.size == 1 && simBearPerm[0]!.status.plusOnePlusOne == 0 &&
    laterBearPerm.size == 1 && laterBearPerm[0]!.status.plusOnePlusOne == 3

  -- 9e. CR 102.2 / 508.4c / 810.7 Two-Headed Giant with no living opponents: entering-attacking, `markAttacking`, `.leastPower`, and stamped player `AttackTarget`s never attack or damage self/teammate!
  let g2hg0 : Game := mkTwoHeadedGiant18
  let g2hgNoOpp : Game := (g2hg0.concede ⟨2⟩).concede ⟨3⟩
  let (g2hgTokCreated, createdTok2hg) := g2hgNoOpp.createOneToken ⟨0⟩ bear (attacking := true) (cause := some testCause)
  let g2hgHand1 : Game := insertObject g2hgTokCreated hero ⟨1⟩ (.hand ⟨1⟩)
  let h1CardId := (g2hgHand1.player ⟨1⟩).hand.back!
  let (g2hgPutAtk, putId2hg) := g2hgHand1.move h1CardId .battlefield (some ⟨1⟩) (attacking := true) (cause := some testCause)
  let g2hgMarked : Game := g2hgPutAtk.markAttacking putId2hg (cause := some testCause)
  let g2hgPrompted : Game :=
    g2hgMarked.promptEnteringAttackItems #[.token ⟨0⟩ .spirit false (g2hgMarked.legalEnteringAttackTargets ⟨0⟩)] (cause := some testCause)
  let g2hgSacStacked : Game :=
    g2hgPrompted.putTriggeredAbilityOnStack ⟨0⟩ (g2hgPrompted.object! createdTok2hg.id)
      (.triggered .attack (Effect.ofTrigger .defenderSacsLeastPower)) "attack" (eventCause := some testCause)
  let g2hgAfterLeastSac : Game := g2hgSacStacked.resolveTop
  let noOppEnteringSafeOk : Bool :=
    (g2hgNoOpp.livingOpponents ⟨0⟩).isEmpty &&
    (g2hgNoOpp.livingOpponents ⟨1⟩).isEmpty &&
    (g2hgNoOpp.legalEnteringAttackTargets ⟨0⟩).isEmpty &&
    (g2hgNoOpp.legalEnteringAttackTargets ⟨1⟩).isEmpty &&
    !(g2hgTokCreated.object! createdTok2hg.id).status.attacking &&
    (g2hgTokCreated.object! createdTok2hg.id).status.attackingTarget.isNone &&
    !(g2hgPutAtk.object! putId2hg).status.attacking &&
    (g2hgPutAtk.object! putId2hg).status.attackingTarget.isNone &&
    !(g2hgMarked.object! putId2hg).status.attacking &&
    !g2hgPrompted.battlefield.any (·.status.attacking) &&
    (g2hgAfterLeastSac.permanentsOf ⟨0⟩).size == (g2hgPrompted.permanentsOf ⟨0⟩).size &&
    (g2hgAfterLeastSac.permanentsOf ⟨1⟩).size == (g2hgPrompted.permanentsOf ⟨1⟩).size
  let atk2hgNone : ObjectId := ⟨g2hgNoOpp.nextObjectId⟩
  let tokObjNone : GameObject := {
    id := atk2hgNone
    printed := { bear with isToken := true }
    owner := ⟨0⟩
    controller := some ⟨0⟩
    defaultController := some ⟨0⟩
    zone := .battlefield
    status := { summoningSick := true, attacking := true, attackingTarget := none }
    timestamp := g2hgNoOpp.timestamp + 1
  }
  let g2hgUntargetedAtk : Game :=
    g2hgNoOpp.record (GameEvent.created g2hgNoOpp.turnNumber ⟨0⟩ (g2hgNoOpp.snapshot tokObjNone) (cause := testCause))
  let atk2hgSelf : ObjectId := ⟨g2hgUntargetedAtk.nextObjectId⟩
  let tokObjSelf : GameObject := {
    tokObjNone with
    id := atk2hgSelf
    status := { summoningSick := true, attacking := true, attackingTarget := some (.player ⟨0⟩) }
    timestamp := g2hgUntargetedAtk.timestamp + 1
  }
  let g2hgStampedSelf : Game :=
    g2hgUntargetedAtk.record (GameEvent.created g2hgUntargetedAtk.turnNumber ⟨0⟩ (g2hgUntargetedAtk.snapshot tokObjSelf) (cause := testCause))
  let atk2hgMate : ObjectId := ⟨g2hgStampedSelf.nextObjectId⟩
  let tokObjMate : GameObject := {
    tokObjNone with
    id := atk2hgMate
    status := { summoningSick := true, attacking := true, attackingTarget := some (.player ⟨1⟩) }
    timestamp := g2hgStampedSelf.timestamp + 1
  }
  let g2hgStampedBoth : Game :=
    g2hgStampedSelf.record (GameEvent.created g2hgStampedSelf.turnNumber ⟨0⟩ (g2hgStampedSelf.snapshot tokObjMate) (cause := testCause))
  let p0LifePre := (g2hgStampedBoth.player ⟨0⟩).life
  let p1LifePre := (g2hgStampedBoth.player ⟨1⟩).life
  let g2hgBlockStep : Game := g2hgStampedBoth.beginStep .declareBlockers
  let g2hgCombatStep : Game := g2hgBlockStep.beginStep .combatDamage
  let twoHeadedNoOppSafeOk : Bool :=
    noOppEnteringSafeOk &&
    g2hgNoOpp.opponent ⟨0⟩ == ⟨0⟩ &&
    g2hgNoOpp.opponent ⟨1⟩ == ⟨1⟩ &&
    !(g2hgNoOpp.resolveAttackDestination ⟨0⟩ none).isOk &&
    !(g2hgNoOpp.resolveAttackDestination ⟨1⟩ none).isOk &&
    g2hgUntargetedAtk.defendingPlayer == ⟨0⟩ &&
    !g2hgStampedBoth.hasLiveAttackDestination (g2hgStampedBoth.object! atk2hgNone) &&
    !g2hgStampedBoth.hasLiveAttackDestination (g2hgStampedBoth.object! atk2hgSelf) &&
    !g2hgStampedBoth.hasLiveAttackDestination (g2hgStampedBoth.object! atk2hgMate) &&
    g2hgBlockStep.step == .declareBlockers &&
    g2hgBlockStep.blockersQueue.isEmpty &&
    g2hgBlockStep.pending == .none &&
    g2hgBlockStep.priority == ⟨0⟩ &&
    (g2hgCombatStep.player ⟨0⟩).life == p0LifePre &&
    (g2hgCombatStep.player ⟨1⟩).life == p1LifePre

  mustHold18 "9a.turnStartBeforePhaseOk" turnStartBeforePhaseOk &&
  mustHold18 "9b.durationAndExpiryOk" durationAndExpiryOk &&
  mustHold18 "9c.phasedControlAndDepartedRulesOk" phasedControlAndDepartedRulesOk &&
  mustHold18 "9d.arwenPreBfOk" arwenPreBfOk &&
  mustHold18 "9e.twoHeadedNoOppSafeOk" twoHeadedNoOppSafeOk &&
  mustHold18 "9.replay" ([gBt2, gDuPhased, gDuCounterRemoved, gDuSrcMoved, g3PhEot, g3PhNext, gArwSim, gArwSeq, g2hgNoOpp, g2hgTokCreated, g2hgMarked, g2hgPrompted, g2hgAfterLeastSac, g2hgStampedBoth, g2hgBlockStep, g2hgCombatStep].all (fun g =>
    Game.replayEvents g.events == g && allRulesEventsClassified g))

end Phase18EventAlignment

section Phase19EventAlignment

def opp19 : PlayerId := ⟨1⟩

def mustHold19 (label : String) (ok : Bool) : Bool :=
  if ok then true else panic! s!"Phase 19 guard failed: {label}"

def mkThreePlayer19 (seed : UInt64 := 19) : Game :=
  let cfg : StartConfig := {
    seats := #[
      { name := "Chandra", deck := testRedDeck },
      { name := "Nissa", deck := testGreenDeck },
      { name := "Liliana", deck := testRedDeck }
    ]
    format := .constructed
    seed
    startingPlayer := some 0
  }
  match Start.start cfg with
  | .ok g => (keepOpeningHands g 24).advanceStep
  | .error e => panic! e

def mkTwoHeadedGiant19 (seed : UInt64 := 219) : Game :=
  let cfg : StartConfig := {
    seats := #[
      { name := "Chandra", deck := testRedDeck, teammate := some ⟨1⟩ },
      { name := "Nissa", deck := testGreenDeck, teammate := some ⟨0⟩ },
      { name := "Liliana", deck := testRedDeck, teammate := some ⟨3⟩ },
      { name := "Jace", deck := testGreenDeck, teammate := some ⟨2⟩ }
    ]
    format := .constructed
    seed
    startingPlayer := some 0
  }
  match Start.start cfg with
  | .ok g => (keepOpeningHands g 30).advanceStep
  | .error e => panic! e

-- 1. `Damage.gainLife` 3-replacement pause/resume ordering & phased-out Ring-bearer retention.
#guard
  -- 1a. CR 616.1f–g: 3 competing `.modifyLifeGain` effects (`+ 3`, `* 2`, `* 4`) on gaining 2 life:
  --     picking `* 2` first (`2 * 2 = 4`, leaving non-commuting `{+ 3, * 4}`), then `+ 3` (`4 + 3 = 7`),
  --     then auto-applying `* 4` (`7 * 4 = 28`) yields `20 + 28 = 48` life without re-applying `* 2` or restarting from `2`!
  let idAdd3 : ReplacementId := { kind := .addLifeGain, object := some ⟨901⟩ }
  let idMul2 : ReplacementId := { kind := .multiplyLifeGain, object := some ⟨902⟩ }
  let idMul4 : ReplacementId := { kind := .multiplyLifeGain, object := some ⟨903⟩ }
  let gGl0 : Game :=
    ((afterDraw.createEffect
      (.replacement { id := idAdd3, affectedPlayer := me, kind := .modifyLifeGain me 3 1 })
      (cause := some testCause)).createEffect
      (.replacement { id := idMul2, affectedPlayer := me, kind := .modifyLifeGain me 0 2 })
      (cause := some testCause)).createEffect
      (.replacement { id := idMul4, affectedPlayer := me, kind := .modifyLifeGain me 0 4 })
      (cause := some testCause)
  let gGlPause1 : Game := gGl0.gainLife me 2 (cause := some testCause)
  let gGlPause2 : Game := mustApply gGlPause1 me (.chooseReplacement idMul2)
  let gGlDone : Game := mustApply gGlPause2 me (.chooseReplacement idAdd3)
  let gainLifeOrderOk : Bool :=
    (match gGlPause1.pending with | .chooseReplacement p cs => p == me && cs.size == 3 | _ => false) &&
    (match gGlPause2.pending with | .chooseReplacement p cs => p == me && cs.size == 2 && !cs.contains idMul2 | _ => false) &&
    gGlDone.pending == .none &&
    (gGlDone.player me).life == 48

  -- 1b. CR 702.26b,g / 701.54a: phasing out a Ring-bearer keeps `ringBearerId` without emitting
  --     `PermanentEvent.designation _ .ringBearer false`, treats `isRingBearer` as `false` while phased out,
  --     and restores `isRingBearer == true` once phased in!
  let gRb0 : Game := addPermanent afterDraw bear me me
  let rbId := (gRb0.battlefield.filter (·.name == bear.name))[0]!.id
  let gRb1 : Game := gRb0.setRingBearer me (some rbId) (cause := some testCause)
  let prePhaseIdx := gRb1.events.size
  let gRbPhased : Game :=
    gRb1.withBatch (some testCause) fun g =>
      g.record (GameEvent.phasedOut g.turnNumber (g.snapshot (g.object! rbId)) false (cause := testCause))
  let hadClearOnPhaseOut := (gRbPhased.events.extract prePhaseIdx gRbPhased.events.size).any fun e =>
    match e.change with
    | .rules (.permanent (.designation _ .ringBearer false)) => true
    | _ => false
  let gRbPhasedIn : Game :=
    gRbPhased.withBatch (some testCause) fun g =>
      g.record (GameEvent.phasedIn g.turnNumber (g.snapshot (g.object! rbId)) (cause := testCause))
  let phasedRingBearerOk : Bool :=
    gRb1.isRingBearer me (gRb1.object! rbId) &&
    !hadClearOnPhaseOut &&
    (gRbPhased.player me).ringBearerId == some rbId &&
    !gRbPhased.isRingBearer me (gRbPhased.object! rbId) &&
    (gRbPhasedIn.player me).ringBearerId == some rbId &&
    gRbPhasedIn.isRingBearer me (gRbPhasedIn.object! rbId)

  mustHold19 "1a.gainLifeOrderOk" gainLifeOrderOk &&
  mustHold19 "1b.phasedRingBearerOk" phasedRingBearerOk &&
  mustHold19 "1.replay" ([gGlPause1, gGlPause2, gGlDone, gRbPhased, gRbPhasedIn].all (fun g =>
    Game.replayEvents g.events == g && allRulesEventsClassified g))

-- 2. Pause-safety of `applyRiddlesPiles`, `returnLinkedExileToHand`, multiplayer idle-priority `concede`, & `.payWard` decline.
#guard
  -- 2a. `applyRiddlesPiles` pauses cleanly per card on competing graveyard->exile replacements without dropping remaining cards!
  let idExA : ReplacementId := { kind := .exileOppDeath, object := some ⟨910⟩ }
  let idExB : ReplacementId := { kind := .exileOppDeath, object := some ⟨911⟩ }
  let gRid0 : Game :=
    (afterDraw.createEffect
      (.replacement { id := idExA, affectedPlayer := me, kind := .exileInsteadOfGraveyard none false })
      (cause := some testCause)).createEffect
      (.replacement { id := idExB, affectedPlayer := me, kind := .exileInsteadOfGraveyard none false })
      (cause := some testCause)
  let lib := (gRid0.player me).library
  let c1 := lib[lib.size - 1]!
  let c2 := lib[lib.size - 2]!
  let c3 := lib[lib.size - 3]!
  let gRidP1 : Game := gRid0.applyRiddlesPiles me #[c1, c2] #[c3] true
  let gRidP2 : Game := mustApply gRidP1 me (.chooseReplacement idExA)
  let gRidDone : Game := mustApply gRidP2 me (.chooseReplacement idExB)
  let riddlesPauseOk : Bool :=
    (match gRidP1.pending with | .chooseReplacement p cs => p == me && cs.size == 2 | _ => false) &&
    (gRidP1.object! c2).zone == .library me &&
    (match gRidP2.pending with | .chooseReplacement p cs => p == me && cs.size == 2 | _ => false) &&
    gRidDone.pending == .none &&
    (gRidDone.followMovedToZone? c1 (· == .exile)).isSome &&
    (gRidDone.followMovedToZone? c2 (· == .exile)).isSome &&
    (gRidDone.followMovedToZone? c3 (· == .hand me)).isSome

  -- 2b. `Chapters.returnLinkedExileToHand` clears `linkedExile` across `Pending.chooseReplacement` only after arrival,
  --     and preserves `linkedExile` when an exiled token cannot move out of exile (CR 111.8)!
  let sagaDummy : CardDef := { name := "Phase19 Link Saga", manaCost := ManaCost.empty, types := #[.enchantment] }
  let gLk0 : Game := addPermanent (insertObject afterDraw bear me .exile) sagaDummy me me
  let sagaId := (gLk0.battlefield.filter (·.name == "Phase19 Link Saga"))[0]!.id
  let exCardId := (gLk0.objects.filter (fun o => o.name == bear.name && o.zone == .exile))[0]!.id
  let gLk1 : Game := gLk0.change (.object sagaId (.pushLinkedExile exCardId))
  let gLkReturned : Game := gLk1.returnLinkedExileToHand (some sagaId)
  -- Exiled token (`CR 111.8`): `move` leaves it in exile, so `linkedExile` is not falsely cleared or logged returned!
  let (gTokLk0, tokLk) := (addPermanent afterDraw sagaDummy me me).createOneToken me { bear with name := "Phase19 Link Tok" }
    (cause := some testCause)
  let sagaTokId := (gTokLk0.battlefield.filter (·.name == "Phase19 Link Saga"))[0]!.id
  let (gTokLk1, exTokId) := gTokLk0.move tokLk.id .exile none (cause := some testCause)
  let gTokLk2 : Game := gTokLk1.change (.object sagaTokId (.pushLinkedExile exTokId))
  let gTokLkBlocked : Game := gTokLk2.returnLinkedExileToHand (some sagaTokId)
  let linkedReturnOk : Bool :=
    (gLkReturned.object! sagaId).linkedExile.isEmpty &&
    (gLkReturned.followMovedToZone? exCardId (· == .hand me)).isSome &&
    (gTokLkBlocked.object! sagaTokId).linkedExile == #[exTokId] &&
    (gTokLkBlocked.object! exTokId).zone == .exile

  -- 2c. Multiplayer idle-priority `concede`:
  --     (i) when `⟨0⟩` & `⟨1⟩` already passed (`consecutivePasses == 2`) and `⟨2⟩` concedes, step advances cleanly;
  --     (ii) when `⟨2⟩` controlled a legendary permanent owned by `⟨1⟩` and `⟨1⟩` already controls an identical legend,
  --          `concede ⟨2⟩` pauses on `chooseLegend` instead of advancing the step early!
  let g3Idle0 : Game := mkThreePlayer19 42
  let stepBefore := g3Idle0.step
  let g3Passed2 : Game := mustApply (mustApply g3Idle0 ⟨0⟩ .pass) ⟨1⟩ .pass
  let g3ConcedeAdv : Game := g3Passed2.concede ⟨2⟩
  let legDef19 : CardDef := { bear with name := "Phase19 Legend", supertypes := #[.legendary] }
  let g3Leg0 : Game := addPermanent (addPermanent (mkThreePlayer19 43) legDef19 ⟨1⟩ ⟨1⟩) legDef19 ⟨1⟩ ⟨1⟩
  let legIds := (g3Leg0.battlefield.filter (·.name == "Phase19 Legend")).map (·.id)
  let g3Leg1 : Game := g3Leg0.changeControl (g3Leg0.object! legIds[1]!) ⟨2⟩ (untilEot := true) (cause := some testCause)
  let g3LegPassed : Game := mustApply (mustApply g3Leg1 ⟨0⟩ .pass) ⟨1⟩ .pass
  let g3LegPaused : Game := g3LegPassed.concede ⟨2⟩
  let g3LegResolved : Game := mustApply g3LegPaused ⟨1⟩ (.keepLegend legIds[0]!)
  let concedeIdleOk : Bool :=
    g3ConcedeAdv.step != stepBefore &&
    g3LegPaused.step == g3LegPassed.step &&
    g3LegPaused.legendChoicePending? &&
    g3LegResolved.pending == .none

  -- 2d. `Decisions.decline` on `.payWard` clears `g.pending` and runs outer `pendingReplacement`!
  let gWd0 : Game := addPermanent (insertObject afterDraw lightningBolt me (.hand me)) bear opp19 opp19
  let boltId := (gWd0.player me).hand.back!
  let wardSrcId := (gWd0.battlefield.filter (·.name == bear.name))[0]!.id
  let (gWd1, boltStackId) := gWd0.move boltId .stack (some me) (verb := some .cast) (actor := some me)
    (cause := some (.gameRule .spellCast))
  let gWd1 : Game :=
    gWd1.change (.pushStack { objectId := boltStackId, controller := me, targets := #[Target.permanent wardSrcId], targetsAnnounced := true })
  let gWd2 : Game :=
    gWd1.changes #[
      .priority opp19,
      .pending (.payWard me boltStackId (.genericMana 2)),
      .pendingReplacement (some (.receivePriority me))]
  let gWdDeclined : Game := mustApply gWd2 me .decline
  let wardDeclineOk : Bool :=
    gWdDeclined.pending == .none &&
    gWdDeclined.stack.isEmpty &&
    gWdDeclined.priority == me

  mustHold19 "2a.riddlesPauseOk" riddlesPauseOk &&
  mustHold19 "2b.linkedReturnOk" linkedReturnOk &&
  mustHold19 "2c.concedeIdleOk" concedeIdleOk &&
  mustHold19 "2d.wardDeclineOk" wardDeclineOk &&
  mustHold19 "2.replay" ([gRidP1, gRidP2, gRidDone, gLkReturned, gTokLkBlocked, g3ConcedeAdv, g3LegPaused, g3LegResolved, gWdDeclined].all (fun g =>
    Game.replayEvents g.events == g && allRulesEventsClassified g))

-- 3. `Damage.markDamageOn` non-creature planeswalker damage, clamped loyalty removal, & lifelink provenance.
#guard
  -- 3a. Non-creature planeswalker dealt 2 damage loses 2 loyalty WITHOUT `DamageEvent.marked`, so animating into
  --     a 2/2 creature later in the turn does NOT destroy it via CR 704.5g!
  let pwDef19 : CardDef := {
    name := "Phase19 Walker"
    manaCost := ManaCost.empty
    supertypes := #[.legendary]
    types := #[.planeswalker]
    subtypes := #["Jace"]
    loyalty := some 5
  }
  let gPw0 : Game := addPermanent afterDraw pwDef19 me me
  let pwId := (gPw0.battlefield.filter (·.name == "Phase19 Walker"))[0]!.id
  let gPw0 : Game := gPw0.recordPutCounters pwId .loyalty 5 (some me) (cause := some testCause)
  let gPwDmg : Game := gPw0.markDamageOn (gPw0.object! pwId) 2 "2 dmg to walker" (cause := some testCause)
  let gPwAnim : Game :=
    (gPwDmg.setUntilEotForm (gPwDmg.object! pwId) (2, 2) Keywords.none "becomes 2/2 creature"
      (additionalCreature := true)).checkSBA
  -- 3b. Clamped loyalty removal: 2 loyalty dealt 5 damage removes 2 (not 5); 0 loyalty dealt 3 damage emits 0 counter events!
  let gPwClamp0 : Game := addPermanent afterDraw pwDef19 me me
  let pwClampId := (gPwClamp0.battlefield.filter (·.name == "Phase19 Walker"))[0]!.id
  let gPwClamp1 : Game := gPwClamp0.recordPutCounters pwClampId .loyalty 2 (some me) (cause := some testCause)
  let preClampIdx := gPwClamp1.events.size
  let gPwClamp2 : Game := gPwClamp1.markDamageOn (gPwClamp1.object! pwClampId) 5 "5 dmg to 2-loyalty walker" (cause := some testCause)
  let removedAmts := (gPwClamp2.events.extract preClampIdx gPwClamp2.events.size).filterMap fun e =>
    match e.change with
    | .rules (.permanent (.counters _ .loyalty (.removed k) _)) => some k
    | _ => none
  let preZeroLoyIdx := gPwClamp2.events.size
  let gPwZeroLoy : Game := gPwClamp2.markDamageOn (gPwClamp2.object! pwClampId) 3 "3 dmg at 0 loyalty" (cause := some testCause)
  let zeroLoyEvents := (gPwZeroLoy.events.extract preZeroLoyIdx gPwZeroLoy.events.size).filter fun e =>
    match e.change with
    | .rules (.permanent (.counters _ .loyalty (.removed _) _)) => true
    | _ => false
  let pwDamageAndLoyaltyOk : Bool :=
    (gPwDmg.object! pwId).status.counterCount .loyalty == 3 &&
    (gPwDmg.object! pwId).status.damage == 0 &&
    gPwAnim.battlefield.any (·.id == pwId) &&
    removedAmts == #[2] &&
    zeroLoyEvents.isEmpty

  -- 3c. Lifelink noncombat damage under `.multiplyDamage` passes `rep.cause` (`EventCause.replaced`) into `gainLife`!
  let llDef19 : CardDef := { bear with name := "Phase19 Lifelinker", keywords := Keyword.lifelink }
  let gLl0 : Game := addPermanent afterDraw llDef19 me me
  let llId := (gLl0.battlefield.filter (·.name == "Phase19 Lifelinker"))[0]!.id
  let idMulDmg : ReplacementId := { kind := .multiplyDamage, object := some llId }
  let gLl1 : Game :=
    gLl0.createEffect (.replacement { id := idMulDmg, source := some llId, controller := some me,
                                      affectedPlayer := opp19, kind := .multiplyDamage (some llId) 2 })
      (cause := some testCause)
  let preLlIdx := gLl1.events.size
  let gLlDone : Game :=
    gLl1.dealDamageToPlayer opp19 2 (source := some (gLl1.object! llId)) (cause := some testCause)
  let gainedReplaced := (gLlDone.events.extract preLlIdx gLlDone.events.size).any fun e =>
    match e.change, e.cause? with
    | .rules (.life (.gained p 4)), some (.replaced r _) => p == me && r == idMulDmg
    | _, _ => false

  mustHold19 "3ab.pwDamageAndLoyaltyOk" pwDamageAndLoyaltyOk &&
  mustHold19 "3c.gainedReplaced" gainedReplaced &&
  mustHold19 "3.replay" ([gPwDmg, gPwAnim, gPwClamp2, gPwZeroLoy, gLlDone].all (fun g =>
    Game.replayEvents g.events == g && allRulesEventsClassified g))

-- 4. CR 118.9 `payLifeEqualManaValue`, CR 119.4b/8 `canPayLife` & `payLifeCost`, `forObject`, & `.library`/`.command` `fromZone`.
#guard
  -- 4a. CR 118.9 / 601.2g: 0-MV exiled spell with `payLifeEqualManaValue` casts for 0 life;
  --     2-MV exiled spell with `payLifeEqualManaValue` and 0 mana in pool proposes cleanly, opens
  --     `.activateManaAbilities me`, and pays 2 life with `forObject == some spellId` on `.pay`!
  let mv2Bear : CardDef := creature "Phase19 2MV Bear" (ManaCost.ofGeneric 2) #["Bear"] 2 2
  let gPl0 : Game := insertObject (insertObject afterDraw bear me .exile) mv2Bear me .exile
  let exZeroId := (gPl0.objects.filter (fun o => o.name == bear.name && o.zone == .exile))[0]!.id
  let exTwoId := (gPl0.objects.filter (fun o => o.name == "Phase19 2MV Bear" && o.zone == .exile))[0]!.id
  let gPl1 : Game :=
    (gPl0.createEffect
      (.playPermission exZeroId { player := me, whileExiled := true, payLifeEqualManaValue := true })
      (cause := some testCause)).createEffect
      (.playPermission exTwoId { player := me, whileExiled := true, payLifeEqualManaValue := true })
      (cause := some testCause)
  let gCastZero : Game := mustApply gPl1 me (.cast exZeroId)
  let gCastTwoProp : Game := mustApply gPl1 me (.cast exTwoId)
  let twoStackId := gCastTwoProp.stack.back!.objectId
  let preAcceptIdx := gCastTwoProp.events.size
  let gCastTwoPaid : Game := mustApply gCastTwoProp me .pay
  let paidForSpell := (gCastTwoPaid.events.extract preAcceptIdx gCastTwoPaid.events.size).any fun e =>
    match e.change, e.cause? with
    | .rules (.life (.lost p 2 false)), some (.costPayment .life payer (some oid)) =>
      p == me && payer == me && oid == twoStackId
    | _, _ => false
  let payLifeMvOk : Bool :=
    gCastZero.pending == .none &&
    (gCastZero.player me).life == 20 &&
    gCastZero.stack.size == 1 &&
    gCastTwoProp.pending == .activateManaAbilities me &&
    (gCastTwoPaid.player me).life == 18 &&
    paidForSpell

  -- 4b. CR 119.4b / 119.8: `canPayLife` & `payLifeCost` forbid `n > 0` under `lifeCantChange` / `lifeLocked` while allowing `0`!
  let gLc : Game := afterDraw.createEffect (.lifeCantChange me) (cause := some testCause)
  let lifeLockCostOk : Bool :=
    gLc.canPayLife me 0 &&
    !gLc.canPayLife me 1 &&
    (gLc.payLifeCost me 0).isOk &&
    !(gLc.payLifeCost me 1).isOk

  -- 4c. `offerMayPayPick` with `sourceId := none` never leaks `noSourceSentinelId` into `forObject`;
  --     `activateManaAbility` on a `tapPayLifeAddOneOf` land stamps `forObject := some landId`!
  let painLand19 : CardDef := {
    name := "Phase19 Pain Land"
    manaCost := ManaCost.empty
    types := #[.land]
    tapPayLifeAddOneOf := some (1, #[.colored .red, .colored .green])
  }
  let gMp0 : Game := addPermanent afterDraw painLand19 me me
  let landId := (gMp0.battlefield.filter (·.name == "Phase19 Pain Land"))[0]!.id
  let preLandIdx := gMp0.events.size
  let gLandPaid : Game := mustApply gMp0 me (.activateManaAbility landId 0 #[.colored .red] #[])
  let landForObjOk := (gLandPaid.events.extract preLandIdx gLandPaid.events.size).any fun e =>
    match e.change, e.cause? with
    | .rules (.life (.lost _ 1 false)), some (.costPayment .life _ (some oid)) => oid == landId
    | _, _ => false
  let discId := (afterDraw.player me).hand.back!
  let gSourceless0 : Game :=
    (afterDraw.change (.pushContinuationFrame {})).offerMayPayPick me none .discardACard "Discard a card?"
  let preSlIdx := gSourceless0.events.size
  let gSourcelessPaid : Game := mustApply gSourceless0 me (.choosePermanents #[discId])
  let sourcelessForObjOk := (gSourcelessPaid.events.extract preSlIdx gSourcelessPaid.events.size).any fun e =>
    match e.change, e.cause? with
    | .rules (.zone (.moved _ _ (.hand _) (.graveyard _) ..)), some (.costPayment .discard _ forObj) => forObj == none
    | _, _ => false

  -- 4d. `CastEvent.spellCast` records actual `.library` `fromZone` when casting from top of library!
  let topCasterDef : CardDef := { bear with name := "Phase19 Top Caster", mayCastCreaturesFromTop := true }
  let gLib0 : Game := insertObject (addPermanent afterDraw topCasterDef me me) bear me (.library me)
  let topBearId := (gLib0.player me).library.back!
  let preLibCastIdx := gLib0.events.size
  let gLibCast : Game := mustApply gLib0 me (.cast topBearId)
  let libFromZoneOk := (gLibCast.events.extract preLibCastIdx gLibCast.events.size).any fun e =>
    match e.change with
    | .rules (.cast (.spellCast _ p z)) => p == me && z == .library me
    | _ => false

  mustHold19 "4a.payLifeMvOk" payLifeMvOk &&
  mustHold19 "4b.lifeLockCostOk" lifeLockCostOk &&
  mustHold19 "4c.forObjOk" (landForObjOk && sourcelessForObjOk) &&
  mustHold19 "4d.libFromZoneOk" libFromZoneOk &&
  mustHold19 "4.replay" ([gCastZero, gCastTwoProp, gCastTwoPaid, gLc, gLandPaid, gSourcelessPaid, gLibCast].all (fun g =>
    Game.replayEvents g.events == g && allRulesEventsClassified g))

-- 5. CR 603.3b–d per-trigger target prompting, departed-token `.stackTriggerUnusedMode`, 0-mode `announced`,
--    `applyHydeMode` Mode 1 on non-`+1/+1` counters, departed-opponent noncombat damage, & `.gainLifePlusOnes` protection.
#guard
  -- 5a. Ordered `putTriggerBatch` where trigger 1 requires a target and trigger 2 is untargeted:
  --     trigger 1 is placed on `g.stack` and prompts `chooseTargets me` BEFORE trigger 2 enters `g.stack`,
  --     and answering the target places trigger 2 without re-prompting `chooseTriggerToStack`!
  let tgtPingTrig : TriggeredAbility :=
    .triggered .enter {
      targeting := .of .opponent
      resolution := .dealDamage (.fixed 1) (.player (.target .opponent))
      phrase := "When this enters, deal 1 damage to target opponent."
    }
  let drawTrig : TriggeredAbility := .onEnterDraw 1
  let dualEnterDef : CardDef := {
    bear with
    name := "Phase19 Dual Enter"
    triggeredAbilities := #[tgtPingTrig, drawTrig]
  }
  let gTb0 : Game := insertObject afterDraw dualEnterDef me (.hand me)
  let deHandId := (gTb0.player me).hand.back!
  let gTbCast : Game := mustApply gTb0 me (.cast deHandId)
  let gTbOrderPrompt : Game := mustApply (mustApply gTbCast me .pass) opp19 .pass
  let gTbAfterOrder : Game := mustApply gTbOrderPrompt me (.stackTriggers #[0, 1])
  let gTbAfterTarget : Game := mustApply gTbAfterOrder me (.target (Target.player opp19))
  let perTriggerBatchOk : Bool :=
    gTbOrderPrompt.pending == .chooseTriggerToStack me &&
    gTbAfterOrder.pending == .chooseTargets me &&
    gTbAfterOrder.stack.size == 1 &&
    gTbAfterOrder.waitingTriggers.size == 1 &&
    gTbAfterOrder.waitingTriggers[0]!.ordered &&
    gTbAfterTarget.pending == .none &&
    gTbAfterTarget.stack.size == 2 &&
    gTbAfterTarget.waitingTriggers.isEmpty

  -- 5b. Departed-token `.stackTriggerUnusedMode` records `TriggerQueueEvent.modeChosen` even after `ceaseToExist`,
  --     and 0-mode `.chooseUpToXModes` (`chosenX := 0`) + `.upToTriggerModes` `.decline` emit `CastEvent.announced #[]`!
  let unusedAb : TriggeredAbility := .triggered .youGainLife (Effect.ofTrigger .gollumMode) {}
  let (gTokU0, tokU) := afterDraw.createOneToken me { bear with name := "Phase19 Mode Token", triggeredAbilities := #[unusedAb] }
    (cause := some testCause)
  let gTokU1 : Game := gTokU0.ceaseToExist tokU.id (cause := some testCause)
  let gTokU2 : Game := gTokU1.putTriggeredAbilityOnStack me tokU unusedAb "triggers" (eventCause := some testCause)
  let preUnusedIdx := gTokU2.events.size
  let gTokUModeChosen : Game := mustApply gTokU2 me (.chooseMode 0)
  let unusedModeRecorded := (gTokUModeChosen.events.extract preUnusedIdx gTokUModeChosen.events.size).any fun e =>
    match e.change with
    | .rules (.triggerQueue (.modeChosen sid 0 true)) => sid == tokU.id
    | _ => false
  let upToAb : TriggeredAbility := .triggered .enter Effect.enterChooseUpToXModes {}
  let xZeroSrc : GameObject := { (afterDraw.object! (afterDraw.player me).library[0]!) with chosenX := some 0 }
  let preX0Idx := afterDraw.events.size
  let gX0 : Game := afterDraw.putTriggeredAbilityOnStack me xZeroSrc upToAb "enters" (eventCause := some testCause)
  let x0Announced := (gX0.events.extract preX0Idx gX0.events.size).any fun e =>
    match e.change with
    | .rules (.cast (.announced _ #[] _ _)) => true
    | _ => false
  let xOneSrc : GameObject := { xZeroSrc with chosenX := some 1 }
  let gX1 : Game := afterDraw.putTriggeredAbilityOnStack me xOneSrc upToAb "enters" (eventCause := some testCause)
  let preDeclineIdx := gX1.events.size
  let gX1Declined : Game := mustApply gX1 me .decline
  let x1DeclineAnnounced := (gX1Declined.events.extract preDeclineIdx gX1Declined.events.size).any fun e =>
    match e.change with
    | .rules (.cast (.announced _ #[] _ _)) => true
    | _ => false

  -- 5c. `applyHydeMode` Mode 1 removes a non-`+1/+1` counter (`.shield`) from a creature and draws 1 card!
  let gHy0 : Game := addPermanent afterDraw bear me me
  let hyBear := (gHy0.battlefield.filter (·.name == bear.name))[0]!.id
  let gHy1 : Game := gHy0.recordPutCounters hyBear .shield 1 (some me) (cause := some testCause)
  let handBeforeHy := (gHy1.player me).hand.size
  let gHyDone : Game :=
    gHy1.withBatch (some testCause) fun g =>
      g.applyHydeMode me (some hyBear) 1 #[Target.permanent hyBear]
  let hydeShieldOk : Bool :=
    (gHyDone.object! hyBear).status.shield == 0 &&
    (gHyDone.player me).hand.size == handBeforeHy + 1

  -- 5d. CR 800.4i departed-opponent `.opponentDealtNoncombatDamageLastTurn` & `.gainLifePlusOnes` `sourceId` protection!
  let g3Nc0 : Game := mkThreePlayer19 44
  let g3Nc1 : Game := g3Nc0.dealDamageToPlayer ⟨1⟩ 2 (cause := some testCause)
  let g3Nc2 : Game := (g3Nc1.concede ⟨1⟩).startNextTurnAndBegin
  let depOppHeld := g3Nc2.fraConditionHolds ⟨0⟩ .opponentDealtNoncombatDamageLastTurn none
  let proWhiteBear : CardDef := { bear with name := "Phase19 ProWhite Bear", protectionFromColors := #[.white] }
  let whiteWatcher : CardDef := {
    bear with
    name := "Phase19 White Watcher"
    manaCost := ManaCost.ofColor .white
    triggeredAbilities := #[.triggered .youGainLife (Effect.ofTrigger (.resource .gainLifePlusOnes))]
  }
  let gPwProt0 : Game := addPermanent (addPermanent afterDraw proWhiteBear me me) whiteWatcher me me
  let pwBearId := (gPwProt0.battlefield.filter (·.name == "Phase19 ProWhite Bear"))[0]!.id
  let wSrc := gPwProt0.battlefield.filter (·.name == "Phase19 White Watcher") |>.getD 0 default
  let protTargetingOk : Bool :=
    !(gPwProt0.legalTriggerTargets me wSrc.printed.triggeredAbilities[0]! (some wSrc.id)).contains (Target.permanent pwBearId)

  mustHold19 "5a.perTriggerBatchOk" perTriggerBatchOk &&
  mustHold19 "5b.modesAndAnnouncedOk" (unusedModeRecorded && x0Announced && x1DeclineAnnounced) &&
  mustHold19 "5c.hydeShieldOk" hydeShieldOk &&
  mustHold19 "5d.depOppAndProtOk" (depOppHeld && protTargetingOk) &&
  mustHold19 "5.replay" ([gTbOrderPrompt, gTbAfterOrder, gTbAfterTarget, gTokUModeChosen, gX0, gX1Declined, gHyDone, g3Nc2].all (fun g =>
    Game.replayEvents g.events == g && allRulesEventsClassified g))

-- 6. CR 707.10c / 800.4d copy-retarget guards & CR 608.2b multi-target / shared-constraint legality.
#guard
  -- 6a. `copyCastTriggerSpell`: untargeted spell skips `.newTargetsForCopies`; `lost` controller skips `.newTargetsForCopies`;
  --     and a copy whose original target became hexproof may `.decline` to keep its illegal target (CR 707.10c)!
  let untargetedSorcery : CardDef := {
    name := "Phase19 Untargeted Draw"
    manaCost := ManaCost.empty
    types := #[.sorcery]
    spellEffect := some { resolution := .draw (.fixed 1), phrase := "Draw a card." }
  }
  let gCp0 : Game := addPermanent (insertObject afterDraw untargetedSorcery me (.hand me)) bear me me
  let cpSrc := (gCp0.battlefield.filter (·.name == bear.name))[0]!
  let uId := (gCp0.player me).hand.back!
  let (gCp1, uStackId) := gCp0.move uId .stack (some me) (verb := some .cast) (actor := some me) (cause := some testCause)
  let gCp1 : Game := gCp1.putStackEntry me uStackId
  let gCp1 : Game := gCp1.putTriggeredAbilityOnStack me cpSrc (.onEnterDraw 1) "cast"
    (cause := some (gCp1.object! uStackId)) (eventCause := some testCause)
  let gCp1 : Game := gCp1.changes #[.pushContinuationFrame {}, .resolvingAbility (some gCp1.stack.back!.objectId)]
  let gCpUntargeted : Game := gCp1.copyCastTriggerSpell me
  -- Targeted spell copied while original target gained hexproof: `.decline` keeps unchanged target!
  let gCpT0 : Game := addPermanent (addPermanent (insertObject afterDraw lightningBolt me (.hand me)) bear opp19 opp19) hero me me
  let cpTSrc := (gCpT0.battlefield.filter (·.name == hero.name))[0]!
  let bHand := (gCpT0.player me).hand.back!
  let oppBear := (gCpT0.battlefield.filter (·.name == bear.name))[0]!.id
  let (gCpT1, bStackId) := gCpT0.move bHand .stack (some me) (verb := some .cast) (actor := some me) (cause := some testCause)
  let gCpT1 : Game :=
    gCpT1.change (.pushStack { objectId := bStackId, controller := me, targets := #[Target.permanent oppBear], targetsAnnounced := true })
  let gCpT1 : Game := gCpT1.createEffect (.keywordsUntilEot oppBear Keyword.hexproof) (cause := some testCause)
  let gCpT2 : Game := gCpT1.putTriggeredAbilityOnStack me cpTSrc (.onEnterDraw 1) "cast"
    (cause := some (gCpT1.object! bStackId)) (eventCause := some testCause)
  let gCpT2 : Game := gCpT2.changes #[.pushContinuationFrame {}, .resolvingAbility (some gCpT2.stack.back!.objectId)]
  let gCpTPrompt : Game := gCpT2.copyCastTriggerSpell me
  let gCpTDeclined : Game := mustApply gCpTPrompt me .decline
  -- `lost` controller skips `.newTargetsForCopies` (CR 800.4d):
  let gCpLost : Game :=
    (gCpT2.record (GameEvent.playerLost gCpT2.turnNumber me .conceded (cause := some testCause))).copyCastTriggerSpell me
  let copyGuardsOk : Bool :=
    gCpUntargeted.pending == Pending.none &&
    gCpUntargeted.stack.size == 3 &&
    (match gCpTPrompt.pending with | .fraChoice p (.newTargetsForCopies _) => p == me | _ => false) &&
    gCpTDeclined.pending == Pending.none &&
    gCpLost.pending == Pending.none

  -- 6b. CR 608.2b shared-constraint legality (`targetsAllIllegalForKind` on `.twoNonlandsSharingType` &
  --     `.upToTwoCreaturesTotalMvAtMost 3`) + `putPalantirInfluence` player legality!
  let enchDef19 : CardDef := { name := "Phase19 Enchantment", manaCost := ManaCost.empty, types := #[.enchantment] }
  let gSh0 : Game := addPermanent (addPermanent (addPermanent afterDraw bear me me) hero me me) enchDef19 me me
  let shBear := (gSh0.battlefield.filter (·.name == bear.name))[0]!.id
  let shHero := (gSh0.battlefield.filter (·.name == hero.name))[0]!.id
  let shEnch := (gSh0.battlefield.filter (·.name == "Phase19 Enchantment"))[0]!.id
  let (gShOneLeft, _) := gSh0.move shHero (.graveyard me) none (cause := some testCause)
  let twoMvA : CardDef := creature "Phase19 2MV A" (ManaCost.ofGeneric 2) #["Bear"] 2 2
  let twoMvB : CardDef := creature "Phase19 2MV B" (ManaCost.ofGeneric 2) #["Bear"] 2 2
  let gMv0 : Game := addPermanent (addPermanent afterDraw twoMvA opp19 opp19) twoMvB opp19 opp19
  let mvAId := (gMv0.battlefield.filter (·.name == "Phase19 2MV A"))[0]!.id
  let mvBId := (gMv0.battlefield.filter (·.name == "Phase19 2MV B"))[0]!.id
  let gPal0 : Game := (addPermanent afterDraw { enchDef19 with name := "Phase19 Palantir" } me me).createEffect
    (.protectionFromEverything opp19) (cause := some testCause)
  let palId := (gPal0.battlefield.filter (·.name == "Phase19 Palantir"))[0]!.id
  let (gPalRefused, palRes) := gPal0.putPalantirInfluence palId (some opp19)
  let sharedLegalityOk : Bool :=
    !gSh0.targetsAllIllegalForKind me .twoNonlandsSharingType #[Target.permanent shBear, Target.permanent shHero] &&
    gSh0.targetsAllIllegalForKind me .twoNonlandsSharingType #[Target.permanent shBear, Target.permanent shEnch] &&
    !gShOneLeft.targetsAllIllegalForKind me .twoNonlandsSharingType #[Target.permanent shBear, Target.permanent shHero] &&
    gMv0.targetsAllIllegalForKind me (.upToTwoCreaturesTotalMvAtMost 3) #[Target.permanent mvAId, Target.permanent mvBId] &&
    !gMv0.targetsAllIllegalForKind me (.upToTwoCreaturesTotalMvAtMost 4) #[Target.permanent mvAId, Target.permanent mvBId] &&
    palRes.isNone

  mustHold19 "6a.copyGuardsOk" copyGuardsOk &&
  mustHold19 "6b.sharedLegalityOk" sharedLegalityOk &&
  mustHold19 "6.replay" ([gCpUntargeted, gCpTPrompt, gCpTDeclined, gCpLost, gShOneLeft, gPalRefused].all (fun g =>
    Game.replayEvents g.events == g && allRulesEventsClassified g))

-- 7. CR 704.5e off-stack copy zone moves, CR 303.4f–g non-cast Aura `putOntoBattlefield`, & batched `Pumps`.
#guard
  -- 7a. CR 704.5e / 707.10f / 707.12:
  --     (i) permanent spell copy resolving onto `.battlefield` becomes a token (`isToken == true`) and survives `checkSBA`;
  --     (ii) countered spell copy moved again (`.graveyard` -> `.hand`) before `checkSBA` keeps `isCopy == true` and ceases to exist in `checkSBA`!
  let gSc0 : Game := insertObject afterDraw bear me (.hand me)
  let bCardId := (gSc0.player me).hand.back!
  let gScCast : Game := mustApply gSc0 me (.cast bCardId)
  let origSpellObj := gScCast.object! gScCast.stack.back!.objectId
  let (gScCopied, _) := gScCast.copyStackSpellWithId origSpellObj me
  let gScPermResolved : Game := (gScCopied.resolveTop).checkSBA
  -- Countered copy moved `.stack` -> `.graveyard` -> `.hand` before SBAs:
  let (gScCopied2, gyCopyOpt) := gScCast.copyStackSpellWithId origSpellObj me
  let gyCopyId := gyCopyOpt.getD ⟨0⟩
  let (gCopyGy, gyArrId) := gScCopied2.move gyCopyId (.graveyard me) none (cause := some testCause)
  let (gCopyHand, handArrId) := gCopyGy.move gyArrId (.hand me) none (cause := some testCause)
  let gCopySba : Game := gCopyHand.checkSBA
  let offStackCopyOk : Bool :=
    gyCopyOpt.isSome &&
    (gScPermResolved.permanentsOf me).any (fun o => o.name == bear.name && o.printed.isToken) &&
    (gCopyGy.object! gyArrId).isCopy &&
    (gCopyHand.object! handArrId).isCopy &&
    (gCopySba.findObject? handArrId).isNone &&
    !(gCopySba.player me).hand.contains handArrId

  -- 7b. CR 303.4f–g single-card non-cast Aura `putOntoBattlefield`:
  --     0 hosts -> stays in graveyard; 1 hexproof opponent host -> attaches without targeting; 2 hosts -> prompts `.asEntersAttachAura`!
  let testAura19 : CardDef := aura "Phase19 Aura" (ManaCost.ofColor .green) "Enchant creature"
  let hexBear19 : CardDef := { bear with name := "Phase19 Hex Host", keywords := Keyword.hexproof }
  let gAuZero0 : Game := insertObject afterDraw testAura19 me (.graveyard me)
  let auZeroId := (gAuZero0.player me).graveyard.back!
  let (gAuZeroDone, _) := gAuZero0.putOntoBattlefield auZeroId me (cause := some testCause)
  let gAuOne0 : Game := addPermanent (insertObject afterDraw testAura19 me (.graveyard me)) hexBear19 opp19 opp19
  let auOneId := (gAuOne0.player me).graveyard.back!
  let hexHostId := (gAuOne0.battlefield.filter (·.name == "Phase19 Hex Host"))[0]!.id
  let (gAuOneDone, auEnteredId) := gAuOne0.putOntoBattlefield auOneId me (cause := some testCause)
  let gAuTwo0 : Game := addPermanent (insertObject gAuOne0 testAura19 me (.graveyard me)) bear me me
  let myHostId := (gAuTwo0.battlefield.filter (·.name == bear.name))[0]!.id
  let auTwoCardId := (gAuTwo0.player me).graveyard.back!
  let (gAuTwoPrompt, _) := gAuTwo0.putOntoBattlefield auTwoCardId me (cause := some testCause)
  let gAuTwoDone : Game :=
    match gAuTwoPrompt.pending with
    | .chooseReplacement _ cs =>
      let pick := cs.find? (fun r => r.kind == .asEntersAttachAura myHostId) |>.getD cs[0]!
      mustApply gAuTwoPrompt me (.chooseReplacement pick)
    | _ => gAuTwoPrompt
  let singleAuraPutOk : Bool :=
    (gAuZeroDone.object! auZeroId).zone == .graveyard me &&
    (gAuOneDone.object! auEnteredId).isOnBattlefield &&
    (gAuOneDone.object! auEnteredId).attachedTo == some hexHostId &&
    (match gAuTwoPrompt.pending with | .chooseReplacement p cs => p == me && cs.size == 2 | _ => false) &&
    gAuTwoDone.pending == .none &&
    gAuTwoDone.battlefield.any (fun o => o.name == "Phase19 Aura" && o.attachedTo == some myHostId)

  -- 7c. Batched `Pumps.pumpPermanent` (`trample := true`) & `Pumps.grantUntilEotKeywords` share one `BatchId`!
  let gPm0 : Game := addPermanent afterDraw bear me me
  let pmBear := (gPm0.battlefield.filter (·.name == bear.name))[0]!.id
  let prePmIdx := gPm0.events.size
  let gPm1 : Game := gPm0.pumpPermanent (gPm0.object! pmBear) 2 2 (trample := true)
  let pmBatches := (gPm1.events.extract prePmIdx gPm1.events.size).filterMap fun e =>
    match e.change with
    | .rules (.continuousEffect (.created ..)) => some e.batch
    | _ => none
  let preKwIdx := gPm1.events.size
  let gPm2 : Game := gPm1.grantUntilEotKeywords (gPm1.object! pmBear) [Keyword.flying, Keyword.vigilance]
  let kwBatches := (gPm2.events.extract preKwIdx gPm2.events.size).filterMap fun e =>
    match e.change with
    | .rules (.continuousEffect (.created ..)) => some e.batch
    | _ => none
  let batchedPumpsOk : Bool :=
    pmBatches.size == 2 && pmBatches[0]!.isSome && pmBatches[0]! == pmBatches[1]! &&
    kwBatches.size == 2 && kwBatches[0]!.isSome && kwBatches[0]! == kwBatches[1]!

  mustHold19 "7a.offStackCopyOk" offStackCopyOk &&
  mustHold19 "7b.singleAuraPutOk" singleAuraPutOk &&
  mustHold19 "7c.batchedPumpsOk" batchedPumpsOk &&
  mustHold19 "7.replay" ([gScPermResolved, gCopyGy, gCopyHand, gCopySba, gAuZeroDone, gAuOneDone, gAuTwoPrompt, gAuTwoDone, gPm1, gPm2].all (fun g =>
    Game.replayEvents g.events == g && allRulesEventsClassified g))

-- 8. CR 701.15b goad & `leftoverFlyingRestriction`, CR 508.8 combat step-skip fidelity,
--    CR 810 Two-Headed Giant Hexproof/Ward, CR 723.1 `playerControl` window/expiry, & `hasActiveEffect` `durationActive`.
#guard
  -- 8a. CR 701.15b goad non-goader player attacks & `leftoverFlyingRestriction`:
  --     in a 3-player game (`⟨0⟩` active, `⟨1⟩` goader with planeswalker `pw1`, `⟨2⟩` other opponent),
  --     a creature goaded by `⟨1⟩` MUST attack `⟨2⟩` (attacking `pw1` or `⟨1⟩` is illegal while attacking `⟨2⟩` is legal)!
  let pwGoadDef : CardDef := {
    name := "Phase19 Goader PW"
    manaCost := ManaCost.empty
    supertypes := #[.legendary]
    types := #[.planeswalker]
    subtypes := #["Jace"]
    loyalty := some 3
  }
  let gGd0 : Game := addPermanent (addPermanent (mkThreePlayer19 45) { bear with keywords := Keyword.haste } ⟨0⟩ ⟨0⟩) pwGoadDef ⟨1⟩ ⟨1⟩
  let gdAtk := (gGd0.battlefield.filter (·.name == bear.name))[0]!.id
  let gdPw := (gGd0.battlefield.filter (·.name == "Phase19 Goader PW"))[0]!.id
  let gGd0 : Game :=
    (gGd0.recordPutCounters gdPw .loyalty 3 (some ⟨1⟩) (cause := some testCause)).record
      (GameEvent.designation gGd0.turnNumber (gGd0.snapshot (gGd0.object! gdAtk)) (.goaded ⟨1⟩ true) true (cause := testCause))
  let gGd1 : Game := gGd0.beginStep .beginningOfCombat
  let gGd1 : Game := mustApply (mustApply (mustApply gGd1 ⟨0⟩ .pass) ⟨1⟩ .pass) ⟨2⟩ .pass
  let attackPwRejected := !(gGd1.apply ⟨0⟩ (.declareAttackers #[gdAtk] (some ⟨1⟩) #[] #[some gdPw])).isOk
  let attackGoaderRejected := !(gGd1.apply ⟨0⟩ (.declareAttackers #[gdAtk] (some ⟨1⟩) #[] #[none])).isOk
  let gGdAttackP2 : Game := mustApply gGd1 ⟨0⟩ (.declareAttackers #[gdAtk] (some ⟨2⟩) #[] #[none])
  -- `leftoverFlyingRestriction`: flying `.attacksEachCombatIfAble` creature is NOT forced to attack `opp` who has `.flyingCantAttackYouOrBlockYours`,
  -- unless `opp` controls a planeswalker (or when `opp` controls no planeswalker, `declareAttackers #[]` succeeds)!
  let moatLikeDef : CardDef := {
    name := "Phase19 AntiFlyer"
    manaCost := ManaCost.empty
    types := #[.enchantment]
    staticAbilities := #[.flyingCantAttackYouOrBlockYours]
  }
  let mustFlyerDef : CardDef := {
    bear with
    name := "Phase19 Must Flyer"
    keywords := { flying := true, haste := true }
    staticAbilities := #[.attacksEachCombatIfAble]
  }
  let gFl0 : Game := addPermanent (addPermanent afterDraw mustFlyerDef me me) moatLikeDef opp19 opp19
  let gFl1 : Game := mustApply (mustApply (gFl0.beginStep .beginningOfCombat) me .pass) opp19 .pass
  let gFlNoAtk : Game := mustApply gFl1 me (.declareAttackers #[] none #[] #[])
  let goadAndFlyerOk : Bool :=
    attackPwRejected && attackGoaderRejected &&
    (gGdAttackP2.object! gdAtk).status.attackingTarget == some (.player ⟨2⟩) &&
    gFlNoAtk.pending == .none

  -- 8b. CR 508.8 / 509.1 / 510.1 combat step-skip fidelity:
  --     0 attackers declared skips to `.endOfCombat`, whereas 1 attacker declared then exiled during `.declareAttackers`
  --     priority still enters `.declareBlockers` and `.combatDamage` (with NO empty `CombatEvent.damageAssigned`)!
  let gSkZero : Game := mustApply (mustApply gFlNoAtk me .pass) opp19 .pass
  let gSk0 : Game := addPermanent afterDraw { bear with keywords := Keyword.haste } me me
  let skAtk := (gSk0.battlefield.filter (·.name == bear.name))[0]!.id
  let gSk1 : Game := mustApply (mustApply (gSk0.beginStep .beginningOfCombat) me .pass) opp19 .pass
  let gSk2 : Game := mustApply gSk1 me (.declareAttackers #[skAtk] none #[] #[])
  let (gSk3, _) := gSk2.move skAtk .exile none (cause := some testCause)
  let gSkBlk : Game := mustApply (mustApply gSk3 me .pass) opp19 .pass
  let preDmgStepIdx := gSkBlk.events.size
  let gSkDmg : Game := mustApply (mustApply gSkBlk me .pass) opp19 .pass
  let hadEmptyDmgAssigned := (gSkDmg.events.extract preDmgStepIdx gSkDmg.events.size).any fun e =>
    match e.change with
    | .rules (.combat (.damageAssigned ..)) => true
    | _ => false
  let combatSkipFidelityOk : Bool :=
    gSkZero.step == .endOfCombat &&
    gSkBlk.step == .declareBlockers &&
    gSkBlk.pending == .none &&
    gSkDmg.step == .combatDamage &&
    gSkDmg.pending == .none &&
    !hadEmptyDmgAssigned

  -- 8c. CR 810 Two-Headed Giant Hexproof / Ward teammate vs opponent checks!
  let wardBear19 : CardDef := { bear with name := "Phase19 Ward Bear", ward := some 2 }
  let hexBear2hg : CardDef := { bear with name := "Phase19 2HG Hex", keywords := Keyword.hexproof }
  let freePing19 : CardDef := { lightningBolt with name := "Phase19 Free Ping", manaCost := ManaCost.empty }
  let g2h0 : Game := addPermanent (addPermanent mkTwoHeadedGiant19 wardBear19 ⟨1⟩ ⟨1⟩) hexBear2hg ⟨2⟩ ⟨2⟩
  let wbId := (g2h0.battlefield.filter (·.name == "Phase19 Ward Bear"))[0]!.id
  let hbId := (g2h0.battlefield.filter (·.name == "Phase19 2HG Hex"))[0]!.id
  let g2hBoltMate0 : Game := insertObject g2h0 freePing19 ⟨0⟩ (.hand ⟨0⟩)
  let bMateCard := (g2hBoltMate0.player ⟨0⟩).hand.back!
  let g2hMateCast : Game := mustApply (mustApply g2hBoltMate0 ⟨0⟩ (.cast bMateCard)) ⟨0⟩ (.target (Target.permanent wbId))
  let g2hBoltOpp0 : Game := (insertObject g2h0 freePing19 ⟨2⟩ (.hand ⟨2⟩)).change (.priority ⟨2⟩)
  let bOppCard := (g2hBoltOpp0.player ⟨2⟩).hand.back!
  let g2hOppCast : Game := mustApply (mustApply g2hBoltOpp0 ⟨2⟩ (.cast bOppCard)) ⟨2⟩ (.target (Target.permanent wbId))
  let twoHeadedHexWardOk : Bool :=
    !g2h0.canBeTargetedBy ⟨0⟩ (g2h0.object! hbId) &&
    !g2h0.canBeTargetedBy ⟨1⟩ (g2h0.object! hbId) &&
    g2h0.canBeTargetedBy ⟨3⟩ (g2h0.object! hbId) &&
    g2hMateCast.pending == .none &&
    g2hMateCast.stack.size == 1 &&
    g2hOppCast.pending == .none &&
    g2hOppCast.stack.size == 2

  -- 8d. CR 723.1 `playerControl` (`onNextTurn == true` vs `false`) & `Core.hasActiveEffect` `durationActive`!
  let gPcNext0 : Game := afterDraw.createEffect (.playerControl me opp19 true) (cause := some testCause)
  let gPcNextOpp : Game := gPcNext0.startNextTurnAndBegin
  let gPcNextAfter : Game := gPcNextOpp.startNextTurnAndBegin
  let gPcNow0 : Game := afterDraw.createEffect (.playerControl me opp19 false) (cause := some testCause)
  let gPcNowEot : Game := gPcNow0.clearEOT
  let gHa0 : Game := addPermanent afterDraw bear me me
  let haSrc := (gHa0.battlefield.filter (·.name == bear.name))[0]!.id
  let addLandSpec : ContinuousEffectSpec := .playerRule me (.additionalLands 1) (.whileSourceOnBattlefield haSrc)
  let gHa1 : Game := gHa0.createEffect addLandSpec (cause := some testCause)
  let gHaPhased : Game := gHa1.record (GameEvent.phasedOut gHa1.turnNumber (gHa1.snapshot (gHa1.object! haSrc)) false (cause := testCause))
  let gHaPhasedIn : Game := gHaPhased.record (GameEvent.phasedIn gHaPhased.turnNumber (gHaPhased.snapshot (gHaPhased.object! haSrc)) (cause := testCause))
  let ctrlAndDurationActiveOk : Bool :=
    !gPcNext0.controlsPlayer me opp19 &&
    !gPcNext0.controlOnNextTakenTurn.isEmpty &&
    gPcNextOpp.controlsPlayer me opp19 &&
    !gPcNextAfter.controlsPlayer me opp19 &&
    gPcNextAfter.controlOnNextTakenTurn.isEmpty &&
    gPcNow0.controlsPlayer me opp19 &&
    !gPcNowEot.controlsPlayer me opp19 &&
    gHa1.hasActiveEffect addLandSpec &&
    !gHaPhased.hasActiveEffect addLandSpec &&
    gHaPhasedIn.hasActiveEffect addLandSpec

  mustHold19 "8a.goadAndFlyerOk" goadAndFlyerOk &&
  mustHold19 "8b.combatSkipFidelityOk" combatSkipFidelityOk &&
  mustHold19 "8c.twoHeadedHexWardOk" twoHeadedHexWardOk &&
  mustHold19 "8d.ctrlAndDurationActiveOk" ctrlAndDurationActiveOk &&
  mustHold19 "8.replay" ([gGdAttackP2, gFlNoAtk, gSkZero, gSkBlk, gSkDmg, g2hMateCast, g2hOppCast, gPcNext0, gPcNextOpp, gPcNextAfter, gPcNow0, gPcNowEot, gHa1, gHaPhased, gHaPhasedIn].all (fun g =>
    Game.replayEvents g.events == g && allRulesEventsClassified g))

end Phase19EventAlignment

section Phase20EventAlignment

def opp20 : PlayerId := ⟨1⟩

def mustHold20 (label : String) (ok : Bool) : Bool :=
  if ok then true else panic! s!"Phase 20 guard failed: {label}"

def mkThreePlayer20 (seed : UInt64 := 20) : Game :=
  let cfg : StartConfig := {
    seats := #[
      { name := "Chandra", deck := testRedDeck },
      { name := "Nissa", deck := testGreenDeck },
      { name := "Liliana", deck := testRedDeck }
    ]
    format := .constructed
    seed
    startingPlayer := some 0
  }
  match Start.start cfg with
  | .ok g => (keepOpeningHands g 24).advanceStep
  | .error e => panic! e

def mkTwoHeadedGiant20 (seed : UInt64 := 220) : Game :=
  let cfg : StartConfig := {
    seats := #[
      { name := "Chandra", deck := testRedDeck, teammate := some ⟨1⟩ },
      { name := "Nissa", deck := testGreenDeck, teammate := some ⟨0⟩ },
      { name := "Liliana", deck := testRedDeck, teammate := some ⟨3⟩ },
      { name := "Jace", deck := testGreenDeck, teammate := some ⟨2⟩ }
    ]
    format := .constructed
    seed
    startingPlayer := some 0
  }
  match Start.start cfg with
  | .ok g => (keepOpeningHands g 30).advanceStep
  | .error e => panic! e

-- 1. Unified CR 303.4f–g,i `.asEntersAttachAura` across multi-card (`returnLinkedExile`),
--    token (`createToken`), CR 616.1c–d (`entersAsCopy` / `entersBackFaceUp`) Aura entries,
--    and Adventure spell copies (`obj.isCopy` ceasing to exist on `.stack` without `.playPermission`, CR 704.5e / 707.10 / 715.3d).
#guard
  let testAura20 : CardDef := aura "Phase20 Aura" (ManaCost.ofColor .green) "Enchant creature"
  let auraTokenDef20 : CardDef := { testAura20 with name := "Phase20 Aura Token", isToken := true }
  -- 1a. Multi-card `returnLinkedExile`: returning an Aura + a creature simultaneously when 2 hosts exist prompts `.asEntersAttachAura`!
  let gRet0 : Game :=
    addPermanent (addPermanent (addPermanent afterDraw bear me me) hero opp20 opp20)
      { bear with name := "Phase20 Jailer" } me me
  let hostA := (gRet0.battlefield.filter (·.name == bear.name))[0]!.id
  let hostB := (gRet0.battlefield.filter (·.name == hero.name))[0]!.id
  let jailerId := (gRet0.battlefield.filter (·.name == "Phase20 Jailer"))[0]!.id
  let gRet1 : Game := insertObject (insertObject gRet0 testAura20 me .exile) { bear with name := "Phase20 Returned Bear" } me .exile
  let exAuraId := (gRet1.objects.filter (fun o => o.name == "Phase20 Aura" && o.zone == .exile))[0]!.id
  let exBearId := (gRet1.objects.filter (fun o => o.name == "Phase20 Returned Bear" && o.zone == .exile))[0]!.id
  let gRet2 : Game := gRet1.changeObject jailerId (.linkedExile #[exAuraId, exBearId])
  let gRetPrompt : Game := gRet2.returnLinkedExile (gRet2.object! jailerId)
  let retPromptOk :=
    match gRetPrompt.pending with
    | .chooseReplacement p cs =>
      p == me && cs.any (fun r => r.kind == .asEntersAttachAura hostB)
    | _ => false
  let gRetDone : Game :=
    match gRetPrompt.pending with
    | .chooseReplacement _ cs =>
      let pick := cs.find? (fun r => r.kind == .asEntersAttachAura hostB) |>.getD cs[0]!
      mustApply gRetPrompt me (.chooseReplacement pick)
    | _ => gRetPrompt
  let multiReturnAuraOk : Bool :=
    retPromptOk &&
    gRetDone.pending == .none &&
    gRetDone.battlefield.any (fun o => o.name == "Phase20 Aura" && o.attachedTo == some hostB) &&
    gRetDone.battlefield.any (fun o => o.name == "Phase20 Returned Bear")

  -- 1b. Token Aura via `createToken`: 0 hosts -> does NOT enter `.battlefield`; 2 hosts -> prompts `.asEntersAttachAura`!
  let (gTokZero, _) := afterDraw.createToken me auraTokenDef20 (cause := some testCause)
  let gTokTwo0 : Game := addPermanent (addPermanent afterDraw bear me me) hero opp20 opp20
  let tokHostB := (gTokTwo0.battlefield.filter (·.name == hero.name))[0]!.id
  let (gTokPrompt, _) := gTokTwo0.createToken me auraTokenDef20 (cause := some testCause)
  let gTokDone : Game :=
    match gTokPrompt.pending with
    | .chooseReplacement _ cs =>
      let pick := cs.find? (fun r => r.kind == .asEntersAttachAura tokHostB) |>.getD cs[0]!
      mustApply gTokPrompt me (.chooseReplacement pick)
    | _ => gTokPrompt
  let tokenAuraOk : Bool :=
    !gTokZero.battlefield.any (·.name == "Phase20 Aura Token") &&
    (match gTokPrompt.pending with | .chooseReplacement p cs => p == me && cs.size == 2 | _ => false) &&
    gTokDone.battlefield.any (fun o => o.name == "Phase20 Aura Token" && o.attachedTo == some tokHostB)

  -- 1c. CR 616.1c–d: non-Aura entering as a copy of `testAura20` (and DFC entering back-face-up as Aura) prompts `.asEntersAttachAura`!
  let gCopyAura0 : Game :=
    (insertObject gTokTwo0 bear me (.hand me)).createEffect
      (.replacement { id := { kind := .entersAsCopy }, affectedPlayer := me, kind := .entersAsCopy none testAura20 } .untilEndOfTurn)
      (cause := some testCause)
  let handBearId := (gCopyAura0.player me).hand.back!
  let (gCopyAuraPrompt, _) := gCopyAura0.putOntoBattlefield handBearId me (cause := some testCause)
  let gCopyAuraDone : Game :=
    match gCopyAuraPrompt.pending with
    | .chooseReplacement _ cs =>
      let pick := cs.find? (fun r => r.kind == .asEntersAttachAura hostA) |>.orElse
        (fun _ => cs.find? (fun r => r.kind == .asEntersAttachAura tokHostB)) |>.getD cs[0]!
      mustApply gCopyAuraPrompt me (.chooseReplacement pick)
    | _ => gCopyAuraPrompt
  let dfcBackAura : CardDef := { bear with name := "Phase20 Front Creature", otherFace := some testAura20 }
  let gBackZero0 : Game :=
    (insertObject afterDraw dfcBackAura me (.graveyard me)).createEffect
      (.replacement { id := { kind := .entersBackFaceUp }, affectedPlayer := me, kind := .entersBackFaceUp none } .untilEndOfTurn)
      (cause := some testCause)
  let backGyId := (gBackZero0.player me).graveyard.back!
  let (gBackZeroDone, _) := gBackZero0.putOntoBattlefield backGyId me (cause := some testCause)
  let copyAndBackAuraOk : Bool :=
    (match gCopyAuraPrompt.pending with | .chooseReplacement p cs => p == me && cs.size == 2 | _ => false) &&
    gCopyAuraDone.battlefield.any (fun o => o.name == "Phase20 Aura" && o.attachedTo.isSome) &&
    (gBackZeroDone.object! backGyId).zone == .graveyard me &&
    !gBackZeroDone.battlefield.any (·.name == "Phase20 Aura")

  -- 1d. Adventure spell copy (`obj.isCopy == true`) resolving ceases to exist on `.stack` without `.playPermission` (CR 704.5e / 707.10 / 715.3d)!
  let advSpellFace : AdventureFace := {
    name := "Phase20 Adv Instant"
    manaCost := ManaCost.empty
    types := #[.instant]
    spellEffect := some { resolution := .ofSpell (.draw (.fixed 1) .you), phrase := "Draw a card" }
  }
  let advCardDef : CardDef := { bear with name := "Phase20 Adventurer", adventure := some advSpellFace }
  let gAdv0 : Game := insertObject afterDraw advCardDef me (.hand me)
  let advHandId := (gAdv0.player me).hand.back!
  let gAdvCast : Game := mustApply gAdv0 me (.castAdventure advHandId)
  let origAdvObj := gAdvCast.object! gAdvCast.stack.back!.objectId
  let (gAdvCopied, copyAdvId?) := gAdvCast.copyStackSpellWithId origAdvObj me
  let copyAdvId := copyAdvId?.getD ⟨0⟩
  let preCopyResEffects := gAdvCopied.activeEffects.size
  let gAdvCopyResolved : Game := gAdvCopied.resolveTop
  let gAdvOrigResolved : Game := gAdvCopyResolved.resolveTop
  let adventureCopyOk : Bool :=
    copyAdvId?.isSome &&
    (gAdvCopyResolved.findObject? copyAdvId).isNone &&
    gAdvCopyResolved.activeEffects.size == preCopyResEffects &&
    gAdvOrigResolved.objects.any (fun o => o.name == "Phase20 Adventurer" && o.zone == .exile && (gAdvOrigResolved.playPermission o).isSome)

  mustHold20 "1a.multiReturnAuraOk" multiReturnAuraOk &&
  mustHold20 "1b.tokenAuraOk" tokenAuraOk &&
  mustHold20 "1c.copyAndBackAuraOk" copyAndBackAuraOk &&
  mustHold20 "1d.adventureCopyOk" adventureCopyOk &&
  mustHold20 "1.replay" ([gRetPrompt, gRetDone, gTokZero, gTokPrompt, gTokDone, gCopyAuraPrompt, gCopyAuraDone, gBackZeroDone, gAdvCopied, gAdvCopyResolved, gAdvOrigResolved].all (fun g =>
    Game.replayEvents g.events == g && allRulesEventsClassified g))

-- 2. CR 607.2a `leaveTriggerExile` vs CR 610.3 `linkedExile` (`exileSearchedLinked`),
--    departed-source LKI on `onLeaveReturnExiled`, `Chapters.returnLinkedExileToHand`, and `FrcResolve` `.currencyReturn`.
#guard
  -- 2a. `exileSearchedLinked` stores `leaveTriggerExile` (NOT `linkedExile`), so source departure does NOT auto-return onto `.battlefield`!
  let gEx0 : Game := addPermanent (insertObject afterDraw plains me (.library me)) { name := "Phase20 Saga Box", types := #[.enchantment] } me me
  let sagaSrcId := (gEx0.battlefield.filter (·.name == "Phase20 Saga Box"))[0]!.id
  let libPlainsId := (gEx0.player me).library.back!
  let gEx1 : Game := gEx0.exileSearchedLinked me libPlainsId (some sagaSrcId) (cause := some testCause)
  let exPlainsId := (gEx1.objects.filter (fun o => o.name == plains.name && o.zone == .exile))[0]!.id
  let sagaObj1 := gEx1.object! sagaSrcId
  let (gSagaGone, _) := gEx1.move sagaSrcId (.graveyard me) none (verb := some .destroy) (cause := some testCause)
  let leaveTriggerVsLinkedOk : Bool :=
    sagaObj1.leaveTriggerExile == #[exPlainsId] &&
    sagaObj1.linkedExile.isEmpty &&
    (gSagaGone.object! exPlainsId).zone == .exile &&
    !gSagaGone.battlefield.any (·.name == plains.name)

  -- 2b. Departed-source LKI: `Chapters.returnLinkedExileToHand (some sagaSrcId)` & `FrcResolve` `.currencyReturn` find exiled cards after source departed!
  let gHandAfterDepart : Game := gSagaGone.returnLinkedExileToHand (some sagaSrcId)
  let gCur0 : Game := addPermanent (insertObject afterDraw plains me (.graveyard me)) { name := "Phase20 Currency Box", types := #[.artifact] } me me
  let curSrcId := (gCur0.battlefield.filter (·.name == "Phase20 Currency Box"))[0]!.id
  let gyPlainsId := (gCur0.player me).graveyard.back!
  let gCur1 : Game := gCur0.exileSearchedLinked me gyPlainsId (some curSrcId) (cause := some testCause)
  let curExId := (gCur1.objects.filter (fun o => o.name == plains.name && o.zone == .exile))[0]!.id
  let (gCurDeparted, _) := gCur1.move curSrcId (.graveyard me) none (verb := some .destroy) (cause := some testCause)
  let gCurResolved : Game :=
    gCurDeparted.withResolvingContext (some curSrcId) me fun g =>
      g.applyFrc me default .currencyReturn #[] (some curSrcId)
  let departedSagaAndCurrencyOk : Bool :=
    (gHandAfterDepart.player me).hand.any (fun id => (gHandAfterDepart.object! id).name == plains.name) &&
    !(gCurResolved.objects.any (fun o => o.id == curExId && o.zone == .exile)) &&
    gCurResolved.battlefield.any (fun o => gCurResolved.hasSubtype o .treasure)

  -- 2c. `onLeaveReturnExiled` reconstructs `leaveTriggerExile` via LKI when `sourceId` has already moved to `.graveyard`!
  let gFh0 : Game := addPermanent (addPermanent afterDraw { bear with name := "Phase20 Hunter" } me me) hero opp20 opp20
  let hunterId := (gFh0.battlefield.filter (·.name == "Phase20 Hunter"))[0]!.id
  let huntedObj := (gFh0.battlefield.filter (·.name == hero.name))[0]!
  let gFh1 : Game := gFh0.exileForLeaveTrigger (some hunterId) huntedObj (cause := some testCause)
  let (gFhDead, _) := gFh1.move hunterId (.graveyard me) none (verb := some .destroy) (cause := some testCause)
  let gFhReturned : Game :=
    gFhDead.withResolvingContext (some hunterId) me fun g =>
      g.applyTriggeredAbility me .onLeaveReturnExiled (some hunterId)
  let departedHunterLkiOk : Bool :=
    !gFhDead.battlefield.any (·.name == hero.name) &&
    gFhReturned.battlefield.any (fun o => o.name == hero.name && o.controller == some opp20)

  mustHold20 "2a.leaveTriggerVsLinkedOk" leaveTriggerVsLinkedOk &&
  mustHold20 "2b.departedSagaAndCurrencyOk" departedSagaAndCurrencyOk &&
  mustHold20 "2c.departedHunterLkiOk" departedHunterLkiOk &&
  mustHold20 "2.replay" ([gEx1, gSagaGone, gHandAfterDepart, gCur1, gCurDeparted, gCurResolved, gFh1, gFhDead, gFhReturned].all (fun g =>
    Game.replayEvents g.events == g && allRulesEventsClassified g))

-- 3. `finishConcedePriority` `hasWaitingTriggers` & active-prompt preservation across `concede`,
--    `afterWardResolved` post-ward continuation chaining, and CR 122.1c SBA shield-counter destruction & CR 800.4a departure guards.
#guard
  -- 3a. Active prompt (`Pending.scry`) on `⟨0⟩` is preserved when `⟨1⟩` concedes in 3-player game,
  --     and a `WaitingTrigger` queued on `⟨0⟩` when `⟨2⟩` concedes is flushed onto `g.stack` by `finishConcedePriority`!
  let g3p0 : Game := mkThreePlayer20 301
  let g3pScry : Game := g3p0.beginScry ⟨0⟩ 1
  let g3pAfterConcedePrompt : Game := g3pScry.concede ⟨1⟩
  let promptPreservedOk : Bool :=
    match g3pAfterConcedePrompt.pending with
    | .scry p _ _ => p == ⟨0⟩
    | _ => false
  let diesWatcher : CardDef := {
    bear with
    name := "Phase20 Dies Watcher"
    triggeredAbilities := #[.onEnterDraw 1]
  }
  let g3pTrig0 : Game := addPermanent (addPermanent (mkThreePlayer20 302) diesWatcher ⟨0⟩ ⟨0⟩) bear ⟨0⟩ ⟨2⟩
  -- Give `⟨2⟩` priority and queue a waiting trigger before `⟨2⟩` concedes so `finishConcedePriority` sees `hasWaitingTriggers`:
  let watcherObj := (g3pTrig0.battlefield.filter (·.name == "Phase20 Dies Watcher"))[0]!
  let wtConcede : WaitingTrigger := {
    controller := ⟨0⟩
    source := watcherObj
    ability := .onEnterDraw 1
    event := .leaving
    checked := true
    eventCause := testCause
  }
  let g3pTrig1 : Game := (g3pTrig0.change (.priority ⟨2⟩)).recordReflexiveTrigger wtConcede
  let g3pTrigConceded : Game := g3pTrig1.concede ⟨2⟩
  let concedeFlushedTriggersOk : Bool :=
    !g3pTrigConceded.hasWaitingTriggers &&
    g3pTrigConceded.stack.size == 1

  -- 3b. `afterWardResolved` / `finishWardAndDrain`: declining `.payWard` drains an outer `pendingReplacement` continuation!
  let wardTargetDef : CardDef := { bear with name := "Phase20 Ward Host", ward := some 2 }
  let gWd0 : Game := addPermanent (insertObject afterDraw { lightningBolt with manaCost := ManaCost.empty } me (.hand me)) wardTargetDef opp20 opp20
  let wdHostId := (gWd0.battlefield.filter (·.name == "Phase20 Ward Host"))[0]!.id
  let wdBoltId := (gWd0.player me).hand.back!
  let gWdCast : Game := mustApply (mustApply gWd0 me (.cast wdBoltId)) me (.target (Target.permanent wdHostId))
  let wdTrigEntry := gWdCast.stack.back!
  let gWdPrompt0 : Game := gWdCast.resolveTop
  -- Push a post-ward log continuation into `outerPendingReplacements` and verify declining ward drains it!
  let gWdPrompt : Game := gWdPrompt0.change (.continuation (.pushOuterPendingReplacement (.logMessage "Phase20 post-ward continuation ran")))
  let gWdDeclined : Game := mustApply gWdPrompt me .decline
  let wardContinuationOk : Bool :=
    (gWdCast.object! wdTrigEntry.objectId).triggeredAbility.isSome &&
    gWdDeclined.pending == .none &&
    gWdDeclined.pendingReplacement.isNone &&
    gWdDeclined.outerPendingReplacements.isEmpty &&
    gWdDeclined.log.any (·.contains "Phase20 post-ward continuation ran")

  -- 3c. CR 122.1c SBA shield-counter destruction & CR 800.4a damage/life departure guards!
  let gSh0 : Game := addPermanent afterDraw bear me me
  let shBearId := (gSh0.battlefield.filter (·.name == bear.name))[0]!.id
  let gSh1 : Game :=
    (gSh0.recordPutCounters shBearId .shield 1 (some me) (cause := some testCause)).record
      (GameEvent.damageMarked gSh0.turnNumber shBearId 2 (cause := testCause))
  let preSbaIdx := gSh1.events.size
  let gShAfterSba : Game := gSh1.checkSBA
  let sbaSlice := gShAfterSba.events.extract preSbaIdx gShAfterSba.events.size
  let shieldRemovedIdx? := sbaSlice.findIdx? fun e =>
    match e.change with
    | .rules (.permanent (.counters _ .shield (.removed 1) _)) => true
    | _ => false
  let destroyedIdx? := sbaSlice.findIdx? fun e =>
    match e.change with
    | .rules (.zone (.moved before _ .battlefield (.graveyard _) .destroy _ _ _)) => before.id == some shBearId
    | _ => false
  -- Departure guards on `gainLife`, `loseLife`, `setLife`, `dealDamageToPlayer`:
  let gDep0 : Game := (mkThreePlayer20 303).concede ⟨2⟩
  let preDepEvs := gDep0.events.size
  let gDepAfter : Game :=
    (((gDep0.gainLife ⟨2⟩ 5 (cause := some testCause)).loseLife ⟨2⟩ 3 (cause := some testCause)).setLife
      ⟨2⟩ 10 "set departed" (cause := some testCause)).dealDamageToPlayer ⟨2⟩ 4 (cause := some testCause)
  let sbaShieldAndDepartedLifeOk : Bool :=
    (match shieldRemovedIdx?, destroyedIdx? with | some si, some di => si < di | _, _ => false) &&
    gShAfterSba.log.any (·.contains "A shield counter is removed") &&
    gDepAfter.events.size == preDepEvs

  mustHold20 "3a.promptPreservedOk" promptPreservedOk &&
  mustHold20 "3a.concedeFlushedTriggersOk" concedeFlushedTriggersOk &&
  mustHold20 "3b.wardContinuationOk" wardContinuationOk &&
  mustHold20 "3c.sbaShieldAndDepartedLifeOk" sbaShieldAndDepartedLifeOk &&
  mustHold20 "3.replay" ([g3pAfterConcedePrompt, g3pTrigConceded, gWdDeclined, gShAfterSba, gDepAfter].all (fun g =>
    Game.replayEvents g.events == g && allRulesEventsClassified g))

-- 4. CR 601.2b,f,g pre-stack zone cost calculation (`announceX`), `payLife > 0` mana-ability window,
--    `Casting.canCast` (`payLifeEqualManaValue` & `cosmicAwarenessFlash`), and `forObject` provenance.
#guard
  -- 4a. Casting an `{X}{R}` spell from `.exile` while controlling `costReductionNotFromHand := 2`:
  --     `announceX` with `X = 2` evaluates `applyCastCostReductions` against `prop.original.zone == .exile` so `{2}{R}` reduces to `{R}`!
  let reducerDef : CardDef := { bear with name := "Phase20 Exile Reducer", costReductionNotFromHand := 2 }
  let xBurnDef : CardDef := {
    name := "Phase20 X Burn"
    manaCost := { symbols := #[.x, .colored .red] }
    types := #[.sorcery]
    spellEffect := some { resolution := .ofSpell (.draw (.fixed 1) .you), phrase := "Draw a card" }
  }
  let gExX0 : Game :=
    (addPermanent (insertObject afterDraw xBurnDef me .exile) reducerDef me me).addMana
      me (.colored .red) 1 (cause := some testCause)
  let exBurnId := (gExX0.objects.filter (fun o => o.name == "Phase20 X Burn" && o.zone == .exile))[0]!.id
  let gExX1 : Game := gExX0.createEffect (.playPermission exBurnId { player := me } 1) (cause := some testCause)
  let gExXCast : Game := mustApply gExX1 me (.cast exBurnId)
  let gExXChosen : Game := mustApply gExXCast me (.chooseX 2)
  let gExXPaid : Game := mustApply gExXChosen me .pay
  let preStackZoneCostOk : Bool :=
    gExXPaid.pending == .none &&
    gExXPaid.stack.size == 1 &&
    (gExXPaid.object! gExXPaid.stack.back!.objectId).chosenX == some 2

  -- 4b. `payLifeEqualManaValue` (`canCast` respects `lifeLocked` / `life < mv`; targeted cast opens `.activateManaAbilities` window and records `forObject`)
  --     & `cosmicAwarenessFlash` checks departed opponents while excluding 2HG teammates!
  let twoMvPingDef : CardDef := {
    lightningBolt with
    name := "Phase20 TwoMV Ping"
    manaCost := ManaCost.ofGeneric 2
  }
  let gLifeCast0 : Game := insertObject afterDraw twoMvPingDef me .exile
  let lifePingId := (gLifeCast0.objects.filter (fun o => o.name == "Phase20 TwoMV Ping" && o.zone == .exile))[0]!.id
  let gLifeCast1 : Game := gLifeCast0.createEffect (.playPermission lifePingId { player := me, payLifeEqualManaValue := true } 1) (cause := some testCause)
  let gLifeLocked : Game := gLifeCast1.createEffect (.lifeCantChange me) (cause := some testCause)
  let gLifeTarget : Game := mustApply (mustApply gLifeCast1 me (.cast lifePingId)) me (.target (Target.player opp20))
  let openedPayWindow := gLifeTarget.pending == .activateManaAbilities me
  let stackedPingId := gLifeTarget.proposedSpell.map (·.spellId) |>.getD ⟨0⟩
  let gLifePaid : Game := mustApply gLifeTarget me .pay
  let lifeCostHasForObj := gLifePaid.events.any fun e =>
    match e.change, e.cause? with
    | .rules (.life (.lost p 2 false false)), some (.costPayment .life q (some oid)) =>
      p == me && q == me && oid == stackedPingId
    | _, _ => false
  -- `cosmicAwarenessFlash`:
  let flashGrantDef : CardDef := {
    name := "Phase20 Cosmic Grant"
    types := #[.enchantment]
    staticAbilities := #[StaticAbility.flashIfOpponentCastThisTurn]
  }
  let gFlash2hg0 : Game := addPermanent mkTwoHeadedGiant20 flashGrantDef ⟨0⟩ ⟨0⟩
  let gFlash2hgMateCast : Game :=
    let g := insertObject gFlash2hg0 { lightningBolt with manaCost := ManaCost.empty } ⟨1⟩ (.hand ⟨1⟩)
    let cid := (g.player ⟨1⟩).hand.back!
    mustApply (mustApply (g.change (.priority ⟨1⟩)) ⟨1⟩ (.cast cid)) ⟨1⟩ (.target (Target.player ⟨2⟩))
  let gFlash3p0 : Game := addPermanent (mkThreePlayer20 402) flashGrantDef ⟨0⟩ ⟨0⟩
  let gFlash3pOppCast : Game :=
    let g := insertObject gFlash3p0 { lightningBolt with manaCost := ManaCost.empty } ⟨2⟩ (.hand ⟨2⟩)
    let cid := (g.player ⟨2⟩).hand.back!
    (mustApply (mustApply (g.change (.priority ⟨2⟩)) ⟨2⟩ (.cast cid)) ⟨2⟩ (.target (Target.player ⟨1⟩))).concede ⟨2⟩
  let lifeCastAndFlashOk : Bool :=
    gLifeCast1.canCast me (gLifeCast1.object! lifePingId) &&
    !gLifeLocked.canCast me (gLifeLocked.object! lifePingId) &&
    openedPayWindow &&
    lifeCostHasForObj &&
    !gFlash2hgMateCast.cosmicAwarenessFlash ⟨0⟩ &&
    gFlash3pOppCast.cosmicAwarenessFlash ⟨0⟩

  -- 4c. Optional mana payment in `FraChoices` (`mayPaySymbolsThen`) threads `forObject := some srcId`!
  let gMayPay0 : Game :=
    (addPermanent afterDraw hero me me).addMana me (.colored .red) 1 (cause := some testCause)
  let mpHeroId := (gMayPay0.battlefield.filter (·.name == hero.name))[0]!.id
  let preMpEvs := gMayPay0.events.size
  let gMayPayDone : Game :=
    gMayPay0.withResolvingContext (some mpHeroId) me fun g =>
      let gPrompt := g.change (.pending (.fraChoice me (.mayPaySymbolsThen #[.colored .red] (.gainLife 1) mpHeroId)))
      match gPrompt.answerFraChoice me .accept with
      | .ok g' => g'
      | .error e => panic! e
  let manaSpentForObjOk := (gMayPayDone.events.extract preMpEvs gMayPayDone.events.size).any fun e =>
    match e.change, e.cause? with
    | .rules (.player (.manaSpent p _ (some oid))), some (.costPayment .mana q (some oid2)) =>
      p == me && q == me && oid == mpHeroId && oid2 == mpHeroId
    | _, _ => false

  mustHold20 "4a.preStackZoneCostOk" preStackZoneCostOk &&
  mustHold20 "4b.lifeCastAndFlashOk" lifeCastAndFlashOk &&
  mustHold20 "4c.manaSpentForObjOk" manaSpentForObjOk &&
  mustHold20 "4.replay" ([gExXPaid, gLifeLocked, gLifeTarget, gLifePaid, gFlash2hgMateCast, gFlash3pOppCast, gMayPayDone].all (fun g =>
    Game.replayEvents g.events == g && allRulesEventsClassified g))

-- 5. Modal `.activatedAbility` `CastEvent.announced`, non-ability modal spell `resolvingModes` cleanup,
--    and `!wt.checked` multi-copy (`prowessTriggers`) `TriggerQueueEvent.triggered`.
#guard
  -- 5a. Modal activated ability emits exactly one `CastEvent.announced` with `modes := #[1]` and respects `sourceId` protection in `modeIsChoosable`!
  let modalActDef : CardDef := {
    name := "Phase20 Modal Rod"
    manaCost := ManaCost.ofColor .red
    types := #[.artifact]
    activatedAbilities := #[{
      cost := {}
      effect := {
        targeting := .of .creature
        resolution := .ofSpell (.onPermanent .tap)
        phrase := "Tap target creature"
      }
      otherModes := #[{
        resolution := .ofSpell (.draw (.fixed 1) .you)
        phrase := "Draw a card"
      }]
    }]
  }
  let protRedBear : CardDef := {
    bear with
    name := "Phase20 ProtRed Bear"
    protectionFromColors := #[.red]
  }
  -- Only creature on battlefield has protection from red, so Mode 0 is unchoosable for `modalActDef` (`sourceId`), while Mode 1 is choosable!
  let gModAct0 : Game := addPermanent (addPermanent afterDraw modalActDef me me) protRedBear opp20 opp20
  let rodId := (gModAct0.battlefield.filter (·.name == "Phase20 Modal Rod"))[0]!.id
  let preActIdx := gModAct0.events.size
  let gModAct1 : Game := mustApply gModAct0 me (.activate rodId 0)
  let mode0Rejected := !(gModAct1.apply me (.chooseMode 0)).isOk
  let gModActChosen : Game := mustApply gModAct1 me (.chooseMode 1)
  let actAnnouncedModes := (gModActChosen.events.extract preActIdx gModActChosen.events.size).filterMap fun e =>
    match e.change with
    | .rules (.cast (.announced _ ms _ _)) => some ms
    | _ => none
  let modalActivatedOk : Bool :=
    mode0Rejected &&
    actAnnouncedModes == #[#[1]] &&
    gModActChosen.stack.size == 1

  -- 5b. Non-ability modal spell clears `g.resolvingModes` after resolution!
  let modalSorcery20 : CardDef := {
    name := "Phase20 Modal Sorcery"
    manaCost := ManaCost.empty
    types := #[.sorcery]
    spellModes := #[
      { resolution := .ofSpell (.draw (.fixed 1) .you), phrase := "Draw a card" },
      { resolution := .ofSpell (.gainLife 2), phrase := "Gain 2 life" }
    ]
  }
  let gModSp0 : Game := insertObject afterDraw modalSorcery20 me (.hand me)
  let modSpId := (gModSp0.player me).hand.back!
  let gModSpStacked : Game := mustApply (mustApply gModSp0 me (.cast modSpId)) me (.chooseMode 0)
  let gModSpResolved : Game := gModSpStacked.resolveTop
  let resolvingModesClearedOk : Bool :=
    gModSpResolved.resolvingModes.isNone &&
    gModSpResolved.stack.isEmpty

  -- 5c. Double prowess (`prowessInstances := 2`) emits 2 `TriggerQueueEvent.triggered` events!
  let dblProwessDef : CardDef := {
    (creature "Phase20 Twin Monk" ManaCost.empty #["Monk"] 1 2 (keywords := Keyword.prowess)) with
    prowessInstances := 2
  }
  let gProw0 : Game := addPermanent (insertObject afterDraw modalSorcery20 me (.hand me)) dblProwessDef me me
  let monkId := (gProw0.battlefield.filter (·.name == "Phase20 Twin Monk"))[0]!.id
  let prowSpId := (gProw0.player me).hand.back!
  let preProwIdx := gProw0.events.size
  let gProwCast : Game := mustApply (mustApply gProw0 me (.cast prowSpId)) me (.chooseMode 1)
  let prowTriggeredCount := (gProwCast.events.extract preProwIdx gProwCast.events.size).filter (fun e =>
    match e.change with
    | .rules (.triggerQueue (.triggered s _ _ _)) => s.id == some monkId
    | _ => false) |>.size
  let doubleProwessTriggeredOk : Bool := prowTriggeredCount == 2

  mustHold20 "5a.modalActivatedOk" modalActivatedOk &&
  mustHold20 "5b.resolvingModesClearedOk" resolvingModesClearedOk &&
  mustHold20 "5c.doubleProwessTriggeredOk" doubleProwessTriggeredOk &&
  mustHold20 "5.replay" ([gModActChosen, gModSpStacked, gModSpResolved, gProwCast].all (fun g =>
    Game.replayEvents g.events == g && allRulesEventsClassified g))

-- 6. CR 707.10c `.copySourceSpellXTimes`, `.damageUpToOneAndPlayer` skipped-slot indexing,
--    `Targeting.spellPaidTeamwork` isolation, and CR 701.14b fight/target legality.
#guard
  -- 6a. `copyThisSpellXTimesThenDamage` cast with `X = 2` creates 2 stack copies and offers `.newTargetsForCopies` for both!
  let pbbDef20 : CardDef := {
    name := "Phase20 Barrage"
    manaCost := { symbols := #[.x, .colored .red, .colored .red] }
    types := #[.sorcery]
    spellEffect := some {
      targeting := .of .creature
      resolution := .copyThisSpellXTimesThenDamage 1
      phrase := "Deal 1 damage to target creature"
    }
  }
  let gPbb0 : Game :=
    (addPermanent (addPermanent (insertObject afterDraw pbbDef20 me (.hand me)) bear opp20 opp20) hero opp20 opp20).addMana
      me (.colored .red) 4 (cause := some testCause)
  let pbbHandId := (gPbb0.player me).hand.back!
  let oppBearId := (gPbb0.battlefield.filter (fun o => o.name == bear.name && o.controlledBy opp20))[0]!.id
  let oppHeroId := (gPbb0.battlefield.filter (fun o => o.name == hero.name && o.controlledBy opp20))[0]!.id
  let gPbbCast : Game :=
    mustApply (mustApply (mustApply (mustApply gPbb0 me (.cast pbbHandId)) me (.chooseX 2)) me (.target (Target.permanent oppBearId))) me .pay
  let gPbbTrigRes : Game := gPbbCast.resolveTop
  let gPbbRetargeted : Game :=
    mustApply (mustApply gPbbTrigRes me (.choosePermanents #[oppHeroId])) me .decline
  let copyXTimesOk : Bool :=
    (match gPbbTrigRes.pending with
     | .fraChoice p (.newTargetsForCopies cs) => p == me && cs.size == 2
     | _ => false) &&
    gPbbRetargeted.pending == .none &&
    gPbbRetargeted.stack.size == 3

  -- 6b. `.damageUpToOneAndPlayer 2` with slot `0` skipped (`resolvingSkippedSlots := #[0]`) deals 2 damage to `opp20`!
  let upToOneAndPlEff : Effect :=
    FraCandidates.ab (.damageUpToOneAndPlayer 2)
      "Deal 2 damage to up to one target creature or planeswalker and 2 damage to target player"
      (.multi #[
        { TargetFilter.creatureOrPlaneswalker with noun := "up to one target creature or planeswalker" },
        { noun := "target player", zone := .player }
      ] #[0])
  let gSkip0 : Game := addPermanent afterDraw bear me me
  let skipSrcId := (gSkip0.battlefield.filter (·.name == bear.name))[0]!.id
  let oppPreLife := (gSkip0.player opp20).life
  let gSkip1 : Game :=
    gSkip0.withResolvingContext (some skipSrcId) me fun g =>
      (g.change (.resolvingSkippedSlots #[0])).applyFraAbility
        me upToOneAndPlEff (.damageUpToOneAndPlayer 2) #[Target.player opp20] (some skipSrcId)
  let skippedSlotDamageOk : Bool := (gSkip1.player opp20).life == oppPreLife - 2

  -- 6c. `Targeting.spellPaidTeamwork` returns `false` when an unrelated teamwork spell sits on `g.stack`, and `true` when retargeting a teamwork copy!
  let gTw0 : Game := insertObject afterDraw bear me .stack (some me)
  let twSpId := (gTw0.objects.filter (fun o => o.name == bear.name && o.zone == .stack))[0]!.id
  let gTw1 : Game :=
    (gTw0.putStackEntry me twSpId).record
      (GameEvent.announced gTw0.turnNumber twSpId (costs := #[.teamwork #[⟨10⟩, ⟨11⟩]]))
  let gTwCopyPrompt : Game := gTw1.change (.pending (.fraChoice me (.newTargetsForCopies #[twSpId])))
  let teamworkIsolationOk : Bool :=
    !gTw1.spellPaidTeamwork &&
    gTwCopyPrompt.spellPaidTeamwork

  -- 6d. CR 701.14b fight legality: non-creature artifact or hexproof opponent creature cannot fight!
  let nonCreatureArt : CardDef := { name := "Phase20 Relic", manaCost := ManaCost.empty, types := #[.artifact] }
  let hexOppDef : CardDef := { bear with name := "Phase20 Hex Fighter", keywords := Keyword.hexproof }
  let gFg0 : Game := addPermanent (addPermanent (addPermanent afterDraw bear me me) nonCreatureArt opp20 opp20) hexOppDef opp20 opp20
  let myFighterId := (gFg0.battlefield.filter (fun o => o.name == bear.name && o.controlledBy me))[0]!.id
  let relicId := (gFg0.battlefield.filter (·.name == "Phase20 Relic"))[0]!.id
  let hexFighterId := (gFg0.battlefield.filter (·.name == "Phase20 Hex Fighter"))[0]!.id
  let gFgRelic : Game := gFg0.applyFight me (some myFighterId) #[Target.permanent relicId] .source .mutual
  let gFgHex : Game := gFg0.applyFight me (some myFighterId) #[Target.permanent hexFighterId] .source .mutual
  let fightLegalityOk : Bool :=
    (gFgRelic.object! myFighterId).status.damage == 0 &&
    gFgRelic.log.back? == some "The target is no longer legal" &&
    (gFgHex.object! myFighterId).status.damage == 0 &&
    gFgHex.log.back? == some "The target is no longer legal"

  mustHold20 "6a.copyXTimesOk" copyXTimesOk &&
  mustHold20 "6b.skippedSlotDamageOk" skippedSlotDamageOk &&
  mustHold20 "6c.teamworkIsolationOk" teamworkIsolationOk &&
  mustHold20 "6d.fightLegalityOk" fightLegalityOk &&
  mustHold20 "6.replay" ([gPbbCast, gPbbTrigRes, gPbbRetargeted, gSkip1, gTw1, gTwCopyPrompt, gFgRelic, gFgHex].all (fun g =>
    Game.replayEvents g.events == g && allRulesEventsClassified g))

-- 7. CR 508.8 combat-phase bound, empty-assigner `beginCombatDamageAssignment`,
--    player-only `attackTaxPerCreature`, `Agent.choose` `mustAttackIfAble`, and CR 506.5 `attackingAlone?`.
#guard
  -- 7a. CR 508.8: token created attacking in `.beginningOfCombat` advances into `.declareBlockers` even when `declareAttackers #[]` declares 0;
  --     and an extra `.combat` phase after a prior combat with attackers skips `.declareBlockers` when 0 attack in the extra combat!
  let gBoc0 : Game := afterDraw.beginStep .beginningOfCombat
  let (gBoc1, bocTok) := gBoc0.createOneToken me bear (attacking := true) (cause := some testCause)
  let gBocExiled : Game := (gBoc1.move bocTok.id .exile none (cause := some testCause)).1
  let gBocDecl : Game := mustApply (mustApply gBocExiled me .pass) opp20 .pass
  let gBocZeroDecl : Game := mustApply gBocDecl me (.declareAttackers #[] none #[] #[])
  let gBocAfterDecl : Game := mustApply (mustApply gBocZeroDecl me .pass) opp20 .pass
  -- Extra combat phase after a combat where `skBear` attacked (and was exiled before extra combat):
  let gExCb0 : Game := addPermanent afterDraw { bear with keywords := Keyword.haste } me me
  let exCbAtk := (gExCb0.battlefield.filter (·.name == bear.name))[0]!.id
  let gExCb1 : Game := mustApply (mustApply (gExCb0.beginStep .beginningOfCombat) me .pass) opp20 .pass
  let gExCb2 : Game := mustApply gExCb1 me (.declareAttackers #[exCbAtk] none #[] #[])
  let gExCb3 : Game := ((gExCb2.move exCbAtk .exile none (cause := some testCause)).1).record
    (GameEvent.extraPhaseAdded gExCb2.turnNumber .combat .current (cause := testCause))
  -- Advance out of first combat into postcombat / extra combat `.declareAttackers`:
  let gExCbBlk : Game := mustApply (mustApply gExCb3 me .pass) opp20 .pass
  let gExCbDmg : Game := mustApply (mustApply gExCbBlk me .pass) opp20 .pass
  let gExCbEoc : Game := mustApply (mustApply gExCbDmg me .pass) opp20 .pass
  let gExCb2Boc : Game := mustApply (mustApply gExCbEoc me .pass) opp20 .pass
  let gExCb2Decl : Game := mustApply (mustApply gExCb2Boc me .pass) opp20 .pass
  let gExCb2Zero : Game := mustApply gExCb2Decl me (.declareAttackers #[] none #[] #[])
  let gExCb2After : Game := mustApply (mustApply gExCb2Zero me .pass) opp20 .pass
  let combatPhaseBoundOk : Bool :=
    gBocAfterDecl.step == .declareBlockers &&
    gExCb2Boc.step.phase == .combat &&
    gExCb2Boc.step == .beginningOfCombat &&
    gExCb2After.step == .endOfCombat

  -- 7b. First-strike attacker (with no regular-damage assigners) deals damage in FS step and regular `.combatDamage` step grants priority without prompting!
  let fsHeroDef : CardDef := { bear with name := "Phase20 FS Hero", keywords := { firstStrike := true, haste := true } }
  let gFs0 : Game := addPermanent afterDraw fsHeroDef me me
  let fsId := (gFs0.battlefield.filter (·.name == "Phase20 FS Hero"))[0]!.id
  let gFs1 : Game := mustApply (mustApply (gFs0.beginStep .beginningOfCombat) me .pass) opp20 .pass
  let gFs2 : Game := mustApply gFs1 me (.declareAttackers #[fsId] none #[] #[])
  let gFsBlk : Game := mustApply (mustApply gFs2 me .pass) opp20 .pass
  let gFsBlkDone : Game := mustApply gFsBlk opp20 (.declareBlockers #[])
  let gFsDmg1 : Game := mustApply (mustApply gFsBlkDone me .pass) opp20 .pass
  let gFsDmg2 : Game := mustApply (mustApply gFsDmg1 me .pass) opp20 .pass
  let fsEmptySecondStepOk : Bool :=
    gFsDmg1.step == .combatDamage &&
    gFsDmg1.pending == .none &&
    (gFsDmg1.player opp20).life == (gFs0.player opp20).life - 2 &&
    gFsDmg2.step == .combatDamage &&
    gFsDmg2.pending == .none &&
    (gFsDmg2.player opp20).life == (gFs0.player opp20).life - 2

  -- 7c. Player-only `attackTaxPerCreature` (attacking planeswalker is untaxed) & `Agent.choose` prioritizes `mustAttackIfAble`!
  let taxEnchDef : CardDef := {
    name := "Phase20 Tax Ench"
    types := #[.enchantment]
    staticAbilities := #[.creaturesCantAttackYouUnlessPayIfEnduringStory 2]
  }
  let pwDef20 : CardDef := {
    name := "Phase20 Target PW"
    types := #[.planeswalker]
    loyalty := some 3
  }
  let mustBearDef : CardDef := {
    bear with
    name := "Phase20 Must Bear"
    keywords := Keyword.haste
    staticAbilities := #[.attacksEachCombatIfAble]
  }
  let gTax0 : Game :=
    (addPermanent (addPermanent (addPermanent (addPermanent afterDraw { bear with keywords := Keyword.haste } me me) mustBearDef me me) taxEnchDef opp20 opp20) pwDef20 opp20 opp20).record
      (GameEvent.gainedDesignation afterDraw.turnNumber opp20 .enduringStory (cause := some testCause))
  let optAtkId := (gTax0.battlefield.filter (fun o => o.name == bear.name && o.controlledBy me))[0]!.id
  let mustAtkId := (gTax0.battlefield.filter (·.name == "Phase20 Must Bear"))[0]!.id
  let oppPwId := (gTax0.battlefield.filter (·.name == "Phase20 Target PW"))[0]!.id
  let gTax0 : Game := gTax0.recordPutCounters oppPwId .loyalty 3 (some opp20) (cause := some testCause)
  let gTaxDecl : Game := mustApply (mustApply (gTax0.beginStep .beginningOfCombat) me .pass) opp20 .pass
  -- With 0 mana: attacking `opp20` directly fails, while attacking `oppPwId` with both creatures succeeds without paying tax!
  let directPlayerTaxed := !(gTaxDecl.apply me (.declareAttackers #[mustAtkId] (some opp20) #[] #[none])).isOk
  let gPwUntaxed : Game := mustApply gTaxDecl me (.declareAttackers #[optAtkId, mustAtkId] (some opp20) #[] #[some oppPwId, some oppPwId])
  -- With Tomik (`planeswalkersAttackedByOneAtMost`) limiting `oppPwId` to 1 attacker and 0 mana in pool,
  -- `Agent.choose` prioritizes `mustAtkId` (which `mustAttackIfAble`) over `optAtkId`!
  let tomikDef : CardDef := { bear with name := "Phase20 Tomik", staticAbilities := #[.fra .planeswalkersAttackedByOneAtMost] }
  let gTomikDecl : Game := addPermanent gTaxDecl tomikDef opp20 opp20
  let agentPickedMust : Bool :=
    match Agent.choose gTomikDecl me with
    | some act =>
      match gTomikDecl.apply me act with
      | .ok gAfter => (gAfter.object! mustAtkId).status.attacking && !(gAfter.object! optAtkId).status.attacking
      | .error _ => false
    | none => false
  let taxAndAgentOk : Bool :=
    gTaxDecl.attackTaxPerCreature opp20 == 2 &&
    directPlayerTaxed &&
    (gPwUntaxed.object! mustAtkId).status.attackingPlaneswalker? == some oppPwId &&
    agentPickedMust

  -- 7d. CR 506.5 `attackingAlone?`: in 2HG, when both `⟨0⟩` and teammate `⟨1⟩` control 1 attacking creature, neither attacks alone!
  let gAlone0 : Game := addPermanent (addPermanent mkTwoHeadedGiant20 { bear with keywords := Keyword.haste } ⟨0⟩ ⟨0⟩) { hero with keywords := Keyword.haste } ⟨1⟩ ⟨1⟩
  let a0 := (gAlone0.battlefield.filter (·.name == bear.name))[0]!.id
  let a1 := (gAlone0.battlefield.filter (·.name == hero.name))[0]!.id
  let gAloneOne : Game := gAlone0.markAttacking a0 (cause := some testCause)
  let gAloneBoth : Game := gAloneOne.markAttacking a1 (cause := some testCause)
  let attackingAlone2hgOk : Bool :=
    (gAloneOne.attackingAlone? ⟨0⟩).map (·.id) == some a0 &&
    (gAloneBoth.attackingAlone? ⟨0⟩).isNone &&
    (gAloneBoth.attackingAlone? ⟨1⟩).isNone

  mustHold20 "7a.combatPhaseBoundOk" combatPhaseBoundOk &&
  mustHold20 "7b.fsEmptySecondStepOk" fsEmptySecondStepOk &&
  mustHold20 "7c.taxAndAgentOk" taxAndAgentOk &&
  mustHold20 "7d.attackingAlone2hgOk" attackingAlone2hgOk &&
  mustHold20 "7.replay" ([gBocAfterDecl, gExCb2After, gFsDmg1, gFsDmg2, gPwUntaxed, gTomikDecl, gAloneOne, gAloneBoth].all (fun g =>
    Game.replayEvents g.events == g && allRulesEventsClassified g))

-- 8. CR 810 Two-Headed Giant win/loss/teammate & CR 800.4i departed-opponent queries,
--    CR 723.1 / 810.5 `playerControl` & self-control limits, and batched `createEffects` / multi-effect helpers.
#guard
  -- 8a. CR 810 Two-Headed Giant:
  --     - Opponent's `opponentsCantWin := true` blocks `.winTheGame` on `⟨0⟩`'s team;
  --     - Teammate's `.opponentsCantCastOnYourTurn` allows teammate `⟨1⟩` to cast while blocking opponent `⟨2⟩`;
  --     - `corruptedToxicLifelink` ignores teammate poison (`>= 3`) and activates on opponent poison (`>= 3`);
  --     - Departed opponent's `loggedNoncombatDamage` still grants `.flyingHasteIfOpponentDealtNoncombat` (CR 800.4i)!
  let cantWinDef : CardDef := { bear with name := "Phase20 NoWin Angel", cantLoseGame := true, opponentsCantWin := true }
  let abolisherDef : CardDef := { bear with name := "Phase20 Teammate Abolisher", staticAbilities := #[.opponentsCantCastOnYourTurn] }
  let corruptedDef : CardDef := { bear with name := "Phase20 Corrupted Bear", toxic := 1, corruptedToxicLifelink := true }
  let freeInstant20 : CardDef := { name := "Phase20 Free Opt", manaCost := ManaCost.empty, types := #[.instant], spellEffect := some { resolution := .ofSpell (.gainLife 1), phrase := "Gain 1 life" } }
  let g2hWin0 : Game := addPermanent (addPermanent (addPermanent mkTwoHeadedGiant20 cantWinDef ⟨2⟩ ⟨2⟩) abolisherDef ⟨0⟩ ⟨0⟩) corruptedDef ⟨0⟩ ⟨0⟩
  let corId := (g2hWin0.battlefield.filter (·.name == "Phase20 Corrupted Bear"))[0]!.id
  let g2hTryWin : Game :=
    g2hWin0.withResolvingContext none ⟨0⟩ fun g =>
      g.applyTriggeredAbility ⟨0⟩ (.onEnterDraw 1) none (resolutionOverride := some .winTheGame)
  let g2hMateSpell0 : Game := (insertObject g2hWin0 freeInstant20 ⟨1⟩ (.hand ⟨1⟩)).change (.priority ⟨1⟩)
  let mateSpId := (g2hMateSpell0.player ⟨1⟩).hand.back!
  let g2hMateCastOk : Game := mustApply g2hMateSpell0 ⟨1⟩ (.cast mateSpId)
  let g2hOppSpell0 : Game := (insertObject g2hWin0 freeInstant20 ⟨2⟩ (.hand ⟨2⟩)).change (.priority ⟨2⟩)
  let oppSpId := (g2hOppSpell0.player ⟨2⟩).hand.back!
  let oppCastBlocked := !(g2hOppSpell0.apply ⟨2⟩ (.cast oppSpId)).isOk
  let g2hMatePoison : Game := g2hWin0.record (GameEvent.poisoned g2hWin0.turnNumber ⟨1⟩ 3 (cause := testCause))
  let g2hOppPoison : Game := g2hMatePoison.record (GameEvent.poisoned g2hMatePoison.turnNumber ⟨2⟩ 3 (cause := testCause))
  -- CR 800.4i departed-opponent `loggedNoncombatDamage`:
  let noncombatFlierDef : CardDef := {
    bear with
    name := "Phase20 Noncombat Flier"
    staticAbilities := #[.fra .flyingHasteIfOpponentDealtNoncombat]
  }
  let gDepDmg0 : Game := addPermanent (mkThreePlayer20 801) noncombatFlierDef ⟨0⟩ ⟨0⟩
  let flierId := (gDepDmg0.battlefield.filter (·.name == "Phase20 Noncombat Flier"))[0]!.id
  let gDepDmg1 : Game := (gDepDmg0.dealDamageToPlayer ⟨2⟩ 1 (cause := some testCause)).concede ⟨2⟩
  let twoHeadedAndDepartedOk : Bool :=
    !g2hTryWin.over &&
    g2hMateCastOk.stack.size == 1 &&
    oppCastBlocked &&
    !g2hMatePoison.hasLifelink (g2hMatePoison.object! corId) &&
    g2hOppPoison.hasLifelink (g2hOppPoison.object! corId) &&
    gDepDmg1.hasFlying (gDepDmg1.object! flierId) &&
    gDepDmg1.hasHaste (gDepDmg1.object! flierId)

  -- 8b. CR 723.1 / 805.4 / 810.2,5 2HG shared-turn `playerControl` expiry, departed-teammate skip,
  --     extra-turn single-turn expiry, & self-control limits (`canChooseOutsideGame`, `canMakeTournamentDecision`)!
  let g2hCtrl0 : Game := mkTwoHeadedGiant20 802
  let g2hCtrl1 : Game :=
    g2hCtrl0.withResolvingContext none ⟨0⟩ fun g =>
      g.setPlayerControl ⟨0⟩ ⟨3⟩ (onNextTurn := true)
  -- `startNextTurnAndBegin` advances `⟨0⟩ -> ⟨1⟩` (still team 0/1), `⟨1⟩ -> ⟨2⟩` (teammate of `⟨3⟩`),
  -- `⟨2⟩ -> ⟨3⟩` (`⟨3⟩`'s own half of that shared turn), and `⟨3⟩ -> ⟨0⟩` (next opposing turn):
  let g2hCtrlMateTurn : Game := g2hCtrl1.startNextTurnAndBegin
  let g2hCtrlTeamSeat1 : Game := g2hCtrlMateTurn.startNextTurnAndBegin
  let g2hCtrlTeamSeat2 : Game := g2hCtrlTeamSeat1.startNextTurnAndBegin
  let g2hCtrlAfterTeamTurn : Game := g2hCtrlTeamSeat2.startNextTurnAndBegin
  -- Skipping a departed teammate `⟨2⟩` keeps `onNextTurn` control of still-living `⟨3⟩` for `⟨3⟩`'s turn:
  let g2hDepMate0 : Game := g2hCtrl1.playerLeavesGame ⟨2⟩
  let g2hDepMateTurn1 : Game := g2hDepMate0.startNextTurnAndBegin
  let g2hDepMateTargetTurn : Game := g2hDepMateTurn1.startNextTurnAndBegin
  let g2hDepMateAfter : Game := g2hDepMateTargetTurn.startNextTurnAndBegin
  -- Consecutive turns of the same non-teammate player (extra turn -> regular turn) still expire after 1 turn:
  let gExCtrl0 : Game :=
    (afterDraw.record (GameEvent.extraTurnAdded afterDraw.turnNumber opp20 .current (cause := testCause))).withResolvingContext none me fun g =>
      g.setPlayerControl me opp20 (onNextTurn := true)
  let gExCtrlTurn1 : Game := gExCtrl0.startNextTurnAndBegin
  let gExCtrlTurn2 : Game := gExCtrlTurn1.startNextTurnAndBegin
  let twoHeadedCtrlAndSelfOk : Bool :=
    g2hCtrl1.log.any (·.contains "Two-Headed Giant team") &&
    !g2hCtrlMateTurn.controlsPlayer ⟨0⟩ ⟨3⟩ &&
    g2hCtrlTeamSeat1.activePlayer == ⟨2⟩ &&
    g2hCtrlTeamSeat1.controlsPlayer ⟨0⟩ ⟨3⟩ &&
    g2hCtrlTeamSeat1.controlsPlayer ⟨0⟩ ⟨2⟩ &&
    g2hCtrlTeamSeat2.activePlayer == ⟨3⟩ &&
    g2hCtrlTeamSeat2.controlsPlayer ⟨0⟩ ⟨3⟩ &&
    g2hCtrlTeamSeat2.controlsPlayer ⟨0⟩ ⟨2⟩ &&
    g2hCtrlAfterTeamTurn.activePlayer == ⟨0⟩ &&
    !g2hCtrlAfterTeamTurn.controlsPlayer ⟨0⟩ ⟨3⟩ &&
    !g2hCtrlAfterTeamTurn.controlsPlayer ⟨0⟩ ⟨2⟩ &&
    g2hCtrlAfterTeamTurn.controlOnNextTakenTurn.isEmpty &&
    !g2hDepMateTurn1.controlsPlayer ⟨0⟩ ⟨3⟩ &&
    g2hDepMateTargetTurn.activePlayer == ⟨3⟩ &&
    g2hDepMateTargetTurn.controlsPlayer ⟨0⟩ ⟨3⟩ &&
    !g2hDepMateAfter.controlsPlayer ⟨0⟩ ⟨3⟩ &&
    gExCtrlTurn1.controlsPlayer me opp20 &&
    !gExCtrlTurn2.controlsPlayer me opp20 &&
    gExCtrlTurn2.controlOnNextTakenTurn.isEmpty &&
    g2hCtrlTeamSeat1.canChooseOutsideGame ⟨0⟩ ⟨0⟩ &&
    !g2hCtrlTeamSeat1.canChooseOutsideGame ⟨0⟩ ⟨3⟩ &&
    g2hCtrlTeamSeat1.canMakeTournamentDecision ⟨0⟩ ⟨0⟩ &&
    !g2hCtrlTeamSeat1.canMakeTournamentDecision ⟨0⟩ ⟨3⟩

  -- 8c. `createEffects` with `effs.size > 1` stamps all created continuous effects with one shared `BatchId`!
  let gBatchEff0 : Game := addPermanent afterDraw bear me me
  let beId := (gBatchEff0.battlefield.filter (·.name == bear.name))[0]!.id
  let preBeIdx := gBatchEff0.events.size
  let gBatchEff1 : Game := gBatchEff0.createEffects #[
    .pump beId 1 1,
    .keywordsUntilEot beId Keyword.flying
  ] (cause := some testCause)
  let beBatches := (gBatchEff1.events.extract preBeIdx gBatchEff1.events.size).filterMap fun e =>
    match e.change with
    | .rules (.continuousEffect (.created ..)) => some e.batch
    | _ => none
  let batchedCreateEffectsOk : Bool :=
    beBatches.size == 2 && beBatches[0]!.isSome && beBatches[0]! == beBatches[1]!

  mustHold20 "8a.twoHeadedAndDepartedOk" twoHeadedAndDepartedOk &&
  mustHold20 "8b.twoHeadedCtrlAndSelfOk" twoHeadedCtrlAndSelfOk &&
  mustHold20 "8c.batchedCreateEffectsOk" batchedCreateEffectsOk &&
  mustHold20 "8.replay" ([g2hTryWin, g2hMateCastOk, g2hMatePoison, g2hOppPoison, gDepDmg1, g2hCtrl1, g2hCtrlMateTurn, g2hCtrlTeamSeat1, g2hCtrlTeamSeat2, g2hCtrlAfterTeamTurn, g2hDepMate0, g2hDepMateTurn1, g2hDepMateTargetTurn, g2hDepMateAfter, gExCtrl0, gExCtrlTurn1, gExCtrlTurn2, gBatchEff1].all (fun g =>
    Game.replayEvents g.events == g && allRulesEventsClassified g))

end Phase20EventAlignment

section Phase21EventAlignment

def opp21 : PlayerId := ⟨1⟩

def mustHold21 (label : String) (ok : Bool) : Bool :=
  if ok then true else panic! s!"Phase 21 guard failed: {label}"

def mkThreePlayer21 (seed : UInt64 := 21) : Game :=
  let cfg : StartConfig := {
    seats := #[
      { name := "Chandra", deck := testRedDeck },
      { name := "Nissa", deck := testGreenDeck },
      { name := "Liliana", deck := testRedDeck }
    ]
    format := .constructed
    seed
    startingPlayer := some 0
  }
  match Start.start cfg with
  | .ok g => (keepOpeningHands g 24).advanceStep
  | .error e => panic! e

def mkTwoHeadedGiant21 (seed : UInt64 := 221) : Game :=
  let cfg : StartConfig := {
    seats := #[
      { name := "Chandra", deck := testRedDeck, teammate := some ⟨1⟩ },
      { name := "Nissa", deck := testGreenDeck, teammate := some ⟨0⟩ },
      { name := "Liliana", deck := testRedDeck, teammate := some ⟨3⟩ },
      { name := "Jace", deck := testGreenDeck, teammate := some ⟨2⟩ }
    ]
    format := .constructed
    seed
    startingPlayer := some 0
  }
  match Start.start cfg with
  | .ok g => (keepOpeningHands g 30).advanceStep
  | .error e => panic! e

-- 1. Concede `.restorePending` ordering after post-leave `checkSBA`, multi-teammate departure
--    pause chaining (`concedePlayersLoop`), and `flushUnlessPays` outer continuation preservation.
#guard
  let headWolf21 : CardDef := {
    bear with
    name := "Phase21 Head Wolf"
    staticAbilities := #[.exileOppDeathCreateWolf]
  }
  -- 1a. 3-player game: `⟨0⟩` is paused on `.scry ⟨0⟩ 1` while `⟨1⟩` concedes; `⟨1⟩` held temporary
  --     control of `⟨2⟩`'s lethal-damaged creature with `.finality` + `headWolf21` on `⟨0⟩`, so
  --     post-leave `checkSBA` pauses on `.chooseReplacement ⟨2⟩` BEFORE `.scry ⟨0⟩ 1` is restored!
  let g3p0 : Game :=
    let g := addPermanent (addPermanent mkThreePlayer21 headWolf21 ⟨0⟩ ⟨0⟩) bear ⟨2⟩ ⟨2⟩
    let victimId := (g.battlefield.filter (·.name == bear.name))[0]!.id
    let g := g.recordPutCounters victimId .finality 1 (some ⟨2⟩) (cause := some testCause)
    let g := setMarkedDamage g victimId 2
    let g := g.createEffect (.layered (.objects #[victimId]) (.control ⟨1⟩) .untilEndOfTurn) (cause := some testCause)
    g.change (.pending (.scry ⟨0⟩ 1))
  let victim3pId := (g3p0.battlefield.filter (·.name == bear.name))[0]!.id
  let fin3pId : ReplacementId := { kind := .finalityCounterExile, object := some victim3pId }
  let g3pConcede : Game := mustApply g3p0 ⟨1⟩ .concede
  let sbaPausedBeforeRestore : Bool :=
    match g3pConcede.pending with
    | .chooseReplacement p cs => p == ⟨2⟩ && cs.contains fin3pId
    | _ => false
  let g3pAfterSba : Game := mustApply g3pConcede ⟨2⟩ (.chooseReplacement fin3pId)
  let restoreAfterSbaOk : Bool :=
    sbaPausedBeforeRestore &&
    (g3pConcede.player ⟨1⟩).leftTheGame &&
    g3pAfterSba.pending == .scry ⟨0⟩ 1

  -- 1b. 2HG (`mkTwoHeadedGiant21`): Team A (`⟨0⟩, ⟨1⟩`) concedes -> both teammates leave;
  --     and in a 4-seat game with paired teammates (`⟨0⟩, ⟨1⟩`) vs `⟨2⟩` vs `⟨3⟩`, post-leave `checkSBA`
  --     pauses across BOTH returned lethal creatures before `.scry ⟨2⟩ 1` is restored!
  let g2hCon0 : Game := mkTwoHeadedGiant21
  let g2hCon1 : Game := mustApply g2hCon0 ⟨0⟩ .concede
  let teamBothLeftOk : Bool :=
    (g2hCon1.player ⟨0⟩).lost &&
    (g2hCon1.player ⟨1⟩).lost &&
    g2hCon1.over
  let g3pLoop0 : Game :=
    let cfg : StartConfig := {
      seats := #[
        { name := "P0", deck := testRedDeck, teammate := some ⟨1⟩ },
        { name := "P1", deck := testGreenDeck, teammate := some ⟨0⟩ },
        { name := "P2", deck := testRedDeck },
        { name := "P3", deck := testGreenDeck }
      ]
      format := .constructed
      seed := 222
      startingPlayer := some 0
    }
    let base :=
      match Start.start cfg with
      | .ok g => (keepOpeningHands g 30).advanceStep
      | .error e => panic! e
    let g := addPermanent (addPermanent (addPermanent base headWolf21 ⟨3⟩ ⟨3⟩) bear ⟨2⟩ ⟨2⟩) hero ⟨2⟩ ⟨2⟩
    let vA := (g.battlefield.filter (·.name == bear.name))[0]!.id
    let vB := (g.battlefield.filter (·.name == hero.name))[0]!.id
    let g := (g.recordPutCounters vA .finality 1 (some ⟨2⟩) (cause := some testCause)).recordPutCounters
      vB .finality 1 (some ⟨2⟩) (cause := some testCause)
    let g := setMarkedDamage (setMarkedDamage g vA 2) vB 2
    let g := (g.createEffect (.layered (.objects #[vA]) (.control ⟨0⟩) .untilEndOfTurn) (cause := some testCause)).createEffect
      (.layered (.objects #[vB]) (.control ⟨1⟩) .untilEndOfTurn) (cause := some testCause)
    g.change (.pending (.scry ⟨2⟩ 1))
  let vLoopA := (g3pLoop0.battlefield.filter (·.name == bear.name))[0]!.id
  let vLoopB := (g3pLoop0.battlefield.filter (·.name == hero.name))[0]!.id
  let finLoopA : ReplacementId := { kind := .finalityCounterExile, object := some vLoopA }
  let finLoopB : ReplacementId := { kind := .finalityCounterExile, object := some vLoopB }
  let gLoop1 : Game := mustApply g3pLoop0 ⟨0⟩ .concede
  let gLoop2 : Game := mustApply gLoop1 ⟨2⟩ (.chooseReplacement finLoopA)
  let gLoop3 : Game := mustApply gLoop2 ⟨2⟩ (.chooseReplacement finLoopB)
  let multiDepartChainOk : Bool :=
    teamBothLeftOk &&
    (gLoop1.player ⟨0⟩).leftTheGame &&
    (gLoop1.player ⟨1⟩).leftTheGame &&
    (match gLoop1.pending with | .chooseReplacement p cs => p == ⟨2⟩ && cs.contains finLoopA | _ => false) &&
    (match gLoop2.pending with | .chooseReplacement p cs => p == ⟨2⟩ && cs.contains finLoopB | _ => false) &&
    gLoop3.pending == .scry ⟨2⟩ 1

  -- 1c. `flushUnlessPays` preserves outer `pendingReplacement` (`PendingReplacement.restorePending`).
  let gFlush0 : Game :=
    ((afterDraw.change (.pushContinuationFrame {})).changes #[
      .continuation (.unlessPaysDue true),
      .continuation (.unlessPaysController me),
      .continuation (.unlessPaysInstead (some (.draw 1))),
      .continuation (.pendingReplacement (some (.restorePending (.scry me 1) false)))
    ])
  let handBeforeFlush := (gFlush0.player me).hand.size
  let gFlush1 : Game := gFlush0.flushUnlessPays
  let flushPreservesContOk : Bool :=
    (gFlush1.player me).hand.size == handBeforeFlush + 1 &&
    gFlush1.pending == .scry me 1

  mustHold21 "1a.restoreAfterSbaOk" restoreAfterSbaOk &&
  mustHold21 "1b.multiDepartChainOk" multiDepartChainOk &&
  mustHold21 "1c.flushPreservesContOk" flushPreservesContOk &&
  mustHold21 "1.replay" ([g3pConcede, g3pAfterSba, g2hCon1, gLoop1, gLoop2, gLoop3, gFlush1].all (fun g =>
    Game.replayEvents g.events == g && allRulesEventsClassified g))

-- 2. CR 702.26g indirectly phased-out attachment unattach & non-self phase-in, plus
--    CR 701.3a–b / 301.5c attachment legality and no-op re-attach timestamp preservation (CR 613.7e).
#guard
  let eqDef21 : CardDef := {
    name := "Phase21 Blade"
    types := #[.artifact]
    subtypes := #["Equipment"]
    manaCost := ManaCost.ofColor .white
  }
  let proWhiteBear21 : CardDef := {
    bear with
    name := "Phase21 ProWhite Bear"
    protectionFromColors := #[.white]
  }
  let relic21 : CardDef := { name := "Phase21 Noncreature Relic", types := #[.artifact] }
  let gPh0 : Game :=
    addPermanent (addPermanent (addPermanent (addPermanent afterDraw bear me me) eqDef21 me me) proWhiteBear21 me me) relic21 me me
  let hostId := (gPh0.battlefield.filter (·.name == bear.name))[0]!.id
  let eqId := (gPh0.battlefield.filter (·.name == "Phase21 Blade"))[0]!.id
  let proId := (gPh0.battlefield.filter (·.name == "Phase21 ProWhite Bear"))[0]!.id
  let relicId := (gPh0.battlefield.filter (·.name == "Phase21 Noncreature Relic"))[0]!.id
  -- 2a. Attach `eqId` to `hostId`; check no-op re-attach preserves `PermanentEvent.attached` count and timestamp!
  let gAtt1 : Game := gPh0.attachSourceTo (gPh0.object! eqId) (gPh0.object! hostId)
  let attCount1 := gAtt1.events.filter (fun e => match e.change with | .rules (.permanent (.attached ..)) => true | _ => false) |>.size
  let eqTs1 := gAtt1.objectEntryTimestamp (gAtt1.object! eqId)
  let gAttNoop : Game := gAtt1.attachSourceTo (gAtt1.object! eqId) (gAtt1.object! hostId)
  let attCount2 := gAttNoop.events.filter (fun e => match e.change with | .rules (.permanent (.attached ..)) => true | _ => false) |>.size
  -- Check `canAttachEquipmentTo` rejects noncreature, protection, self, and creature-Equipment (CR 301.5c):
  let gAnimEq : Game := gAtt1.createEffect (.additionalCreature eqId (untilEot := true)) (cause := some testCause)
  let attachLegalityOk : Bool :=
    attCount1 == 1 && attCount2 == 1 &&
    gAttNoop.objectEntryTimestamp (gAttNoop.object! eqId) == eqTs1 &&
    !gPh0.canAttachEquipmentTo (gPh0.object! eqId) (gPh0.object! relicId) &&
    !gPh0.canAttachEquipmentTo (gPh0.object! eqId) (gPh0.object! proId) &&
    !gAnimEq.canAttachEquipmentTo (gAnimEq.object! eqId) (gAnimEq.object! hostId)
  -- 2b. Phase out `oppHostId` (with `eqId` attached) -> `eqId` phases out indirectly (`phasedWith == some oppHostId`).
  --     `phaseInControlled me` does NOT phase `eqId` in by itself; when `oppHostId` leaves `.battlefield`
  --     (exiled), `eqId` unattaches (`attachedTo == none`) AND stays phased out on `phaseInControlled me` (CR 702.26g)!
  let gPhOpp0 : Game := addPermanent gAtt1 bear opp21 opp21
  let oppHostId := (gPhOpp0.battlefield.filter (fun o => o.name == bear.name && o.controller == some opp21))[0]!.id
  let gAttOpp : Game := gPhOpp0.attachSourceTo (gPhOpp0.object! eqId) (gPhOpp0.object! oppHostId)
  let gPhased : Game := gAttOpp.phaseOut (gAttOpp.object! oppHostId) (cause := some testCause)
  let gTrySelfIn : Game := gPhased.phaseInControlled me
  let (gHostExiled, _) := gPhased.move oppHostId .exile none (cause := some testCause)
  let gEqAfterIn : Game := gHostExiled.phaseInControlled me
  let indirectPhaseOk : Bool :=
    (gPhased.object! eqId).status.phasedOut &&
    (gPhased.object! eqId).status.phasedWith == some oppHostId &&
    (gTrySelfIn.object! eqId).status.phasedOut &&
    (gHostExiled.object! eqId).attachedTo == none &&
    (gEqAfterIn.object! eqId).status.phasedOut &&
    (gEqAfterIn.object! eqId).attachedTo == none

  mustHold21 "2a.attachLegalityOk" attachLegalityOk &&
  mustHold21 "2b.indirectPhaseOk" indirectPhaseOk &&
  mustHold21 "2.replay" ([gAtt1, gAttNoop, gAnimEq, gAttOpp, gPhased, gTrySelfIn, gHostExiled, gEqAfterIn].all (fun g =>
    Game.replayEvents g.events == g && allRulesEventsClassified g))

-- 3. CR 608.2b target revalidation (`.venserPerm`, `applyDestroy` `.forAmass`, `applyExile` `.copyAndHost`),
--    `.eaglesBirds` departed-player guard, and deferred post-replacement logs (`putCountersDeferredLog`).
#guard
  -- 3a. Target revalidation: `opp21`'s creature targeted by `.venserPerm` and `.forAmass` gains hexproof before resolution -> fizzles!
  let gVal0 : Game := addPermanent afterDraw bear opp21 opp21
  let oppBearId := (gVal0.battlefield.filter (·.name == bear.name))[0]!.id
  let gHex : Game := gVal0.createEffect (.keywordsUntilEot oppBearId Keyword.hexproof) (cause := some testCause)
  let gVenserFizzle : Game := gHex.applyFrc me default .venserPerm #[Target.permanent oppBearId] none
  let gAmassFizzle : Game := gHex.applyUnified me { resolution := .destroy .target .forAmass, targeting := .of .creature } #[Target.permanent oppBearId]
  let targetRevalOk : Bool :=
    (gVenserFizzle.permanentsOf me).isEmpty &&
    (gAmassFizzle.object! oppBearId).isOnBattlefield &&
    !gAmassFizzle.destroyedForAmassThisWay
  -- 3b. `.eaglesBirds` in 3-player where `⟨2⟩` has left the game does NOT create tokens for departed `⟨2⟩`!
  let gEagles0 : Game := mustApply mkThreePlayer21 ⟨2⟩ .concede
  let gEaglesLive : Game := gEagles0.resolveDelayedTrigger ⟨0⟩ (.eaglesBirds 2) testCause
  let gEaglesDeparted : Game := gEaglesLive.resolveDelayedTrigger ⟨2⟩ (.eaglesBirds 2) testCause
  let eaglesDepartedGuardOk : Bool :=
    (gEaglesDeparted.permanentsOf ⟨0⟩).size == 2 &&
    (gEaglesDeparted.permanentsOf ⟨2⟩).isEmpty
  -- 3c. `putCountersDeferredLog` logs modified post-replacement count (1 -> 2 under `modifyCountersPut`).
  let gLog0 : Game := addPermanent afterDraw bear me me
  let lbId := (gLog0.battlefield.filter (·.name == bear.name))[0]!.id
  let idDblCtr : ReplacementId := { kind := .multiplyCountersPut, object := some lbId }
  let gLog1 : Game := gLog0.createEffect (.replacement {
    id := idDblCtr, source := some lbId, controller := some me,
    affectedPlayer := me, kind := .modifyCountersPut (some lbId) (some .hone) (add := 0) (mult := 2)
  }) (cause := some testCause)
  let gLog2 : Game := gLog1.putCountersDeferredLog lbId .hone 1 (some me) .getsCount (cause := some testCause)
  let deferredLogOk : Bool :=
    (gLog2.object! lbId).status.hone == 2 &&
    gLog2.log.any (·.contains "gets 2 hone counter(s)") &&
    !gLog2.log.any (·.contains "gets 1 hone counter(s)")

  mustHold21 "3a.targetRevalOk" targetRevalOk &&
  mustHold21 "3b.eaglesDepartedGuardOk" eaglesDepartedGuardOk &&
  mustHold21 "3c.deferredLogOk" deferredLogOk &&
  mustHold21 "3.replay" ([gHex, gVenserFizzle, gAmassFizzle, gEagles0, gEaglesLive, gEaglesDeparted, gLog2].all (fun g =>
    Game.replayEvents g.events == g && allRulesEventsClassified g))

-- 4. CR 101.2 `cantCastSpellsThisTurn`, flash/`canCast` parity (`ignoreTiming`, `castOnlyIfGraveyardAtLeast`),
--    CR 601.2b,f,h caster-identity Thalia & `announceAdditionalCost` reduction order, *Countersculpt* behold
--    deferred to 601.2h, Morph / Impending `applyKickerToProposed` (no Thalia tax, `anyMana`), and CR 602.2b / 733.1 non-cancellation.
#guard
  -- 4a. CR 101.2 `cantCastSpellsThisTurn` blocks `canCast`, `castSpell`, `castFreeCopy`, and `castExiledAsAbilityResolves`.
  let freeShock21 : CardDef := { shock with name := "Phase21 Free Shock", manaCost := ManaCost.empty }
  let gSilence0 : Game :=
    let g := insertObject (insertObject afterDraw freeShock21 me (.hand me)) freeShock21 me .exile
    g.createEffect (.playerRule me .cantCastSpells .untilEndOfTurn) (cause := some testCause)
  let hShock := (gSilence0.player me).hand.back!
  let exShock := (gSilence0.objects.filter (fun o => o.name == "Phase21 Free Shock" && o.zone == .exile))[0]!.id
  let gSilenceEx : Game := gSilence0.change (.pending (.mayCastExiledElseDamage me exShock 2 none))
  let gSilenceCopy : Game := gSilence0.change (.pending (.fraChoice me (.castCopiesFree #[exShock] 1 1)))
  let silenceBlocksAllOk : Bool :=
    !gSilence0.canCast me (gSilence0.object! hShock) &&
    !(gSilence0.castSpell me hShock).isOk &&
    !(gSilenceEx.apply me (.cast exShock)).isOk &&
    !(gSilenceCopy.apply me (.cast exShock)).isOk

  -- 4b. `canCast` parity: `PlayPermission.ignoreTiming` allows sorcery on opponent's turn; `castOnlyIfGraveyardAtLeast` excludes self in graveyard!
  let sorc21 : CardDef := { name := "Phase21 Sorcery", manaCost := ManaCost.empty, types := #[.sorcery], spellEffect := some (Effect.draw 1) }
  let gyThresholdSorc21 : CardDef := {
    sorc21 with
    name := "Phase21 Threshold Sorc"
    castOnlyIfGraveyardAtLeast := some 2
  }
  let gOppTurn0 : Game :=
    let g := ((afterDraw.record (GameEvent.turnBegan (afterDraw.turnNumber + 1) opp21)).record
      (GameEvent.stepBegan (afterDraw.turnNumber + 1) .precombatMain opp21)).change (.priority me)
    let g := insertObject g sorc21 me .exile
    let exId := (g.objects.filter (fun o => o.name == "Phase21 Sorcery" && o.zone == .exile))[0]!.id
    g.createEffect (.playPermission exId { player := me, withoutManaCost := true, ignoreTiming := true }
      (d := .untilEndOfTurn)) (cause := some testCause)
  let exSorcId := (gOppTurn0.objects.filter (fun o => o.name == "Phase21 Sorcery" && o.zone == .exile))[0]!.id
  let gGyThresh0 : Game :=
    let g := insertObject (insertObject afterDraw gyThresholdSorc21 me (.graveyard me)) bear me (.graveyard me)
    let gyId := (g.objects.filter (·.name == "Phase21 Threshold Sorc"))[0]!.id
    g.createEffect (.playPermission gyId { player := me, withoutManaCost := true } (d := .untilEndOfTurn))
      (cause := some testCause)
  let gyThreshId := (gGyThresh0.objects.filter (·.name == "Phase21 Threshold Sorc"))[0]!.id
  let canCastParityOk : Bool :=
    gOppTurn0.canCast me (gOppTurn0.object! exSorcId) &&
    !gGyThresh0.canCast me (gGyThresh0.object! gyThreshId) &&
    !(gGyThresh0.castSpell me gyThreshId).isOk

  -- 4c. Non-owner caster Thalia tax, `announceAdditionalCost` reduction order, and *Countersculpt* behold deferred to 601.2h!
  let thalia21 : CardDef := { bear with name := "Phase21 Thalia", staticAbilities := #[.fra .opponentsNoncreatureSpellsCostMore] }
  let bilbo21 : CardDef := { bear with name := "Phase21 Bilbo", costReductionNotFromHand := 1 }
  let beholdInst21 : CardDef := {
    name := "Phase21 Behold Instant"
    manaCost := { symbols := #[.colored .blue, .colored .blue] }
    types := #[.instant]
    additionalCostBeholdOrPay := some (.jace, 1)
  }
  let jaceCard21 : CardDef := {
    name := "Phase21 Hand Jace"
    types := #[.planeswalker]
    subtypes := #["Jace"]
    loyalty := some 3
  }
  -- Non-owner caster Thalia: `opp21`'s exiled 0-cost noncreature spell cast by `me` under Thalia costs `{1}`!
  let gThaliaEx0 : Game :=
    let g := addPermanent (insertObject afterDraw sorc21 opp21 .exile) thalia21 opp21 opp21
    let exId := (g.objects.filter (fun o => o.name == "Phase21 Sorcery" && o.zone == .exile))[0]!.id
    g.createEffect (.playPermission exId { player := me, withoutManaCost := true } (d := .untilEndOfTurn))
      (cause := some testCause)
  let oppExSorcId := (gThaliaEx0.objects.filter (fun o => o.name == "Phase21 Sorcery" && o.zone == .exile))[0]!.id
  let gThaliaProp : Game := mustApply gThaliaEx0 me (.cast oppExSorcId)
  let thaliaNonOwnerTaxOk : Bool := gThaliaProp.proposedSpell.map (·.cost) == some (ManaCost.ofGeneric 1)
  -- `announceAdditionalCost true` from exile with `costReductionNotFromHand := 1`: `{U}{U} + {1} - {1} == {U}{U}`!
  let gBeholdEx0 : Game :=
    let g := addPermanent (insertObject (insertObject afterDraw beholdInst21 me .exile) jaceCard21 me (.hand me)) bilbo21 me me
    let exId := (g.objects.filter (fun o => o.name == "Phase21 Behold Instant" && o.zone == .exile))[0]!.id
    (g.createEffect (.playPermission exId { player := me } (d := .untilEndOfTurn))
      (cause := some testCause)).addMana me (.colored .blue) 2
  let exBehId := (gBeholdEx0.objects.filter (fun o => o.name == "Phase21 Behold Instant" && o.zone == .exile))[0]!.id
  let jaceHandId := (gBeholdEx0.objects.filter (·.name == "Phase21 Hand Jace"))[0]!.id
  let gBehPayGen : Game := mustApply (mustApply gBeholdEx0 me (.cast exBehId)) me (.chooseAdditionalCost true)
  let addCostReducedOk : Bool :=
    gBehPayGen.proposedSpell.map (·.cost) == some ({ symbols := #[.colored .blue, .colored .blue] } : ManaCost)
  -- Choosing behold (`chooseAdditionalCost false`) does NOT reveal at 601.2b; reveals at 601.2h (`pay`), and reverses if Jace leaves hand before `pay`!
  let gBehChoose : Game := mustApply (mustApply gBeholdEx0 me (.cast exBehId)) me (.chooseAdditionalCost false)
  let notRevealedAt6012b : Bool :=
    !gBehChoose.events.any (fun e => match e.change with | .rules (.player (.revealed ..)) => true | _ => false)
  let gBehPaid : Game := mustApply gBehChoose me .pay
  let revealedAt6012h : Bool :=
    gBehPaid.events.any (fun e => match e.change with | .rules (.player (.revealed p ids)) => p == me && ids == #[jaceHandId] | _ => false)
  let (gBehLostJace, _) := gBehChoose.move jaceHandId .exile none (cause := some testCause)
  let gBehReversed : Game := mustApply gBehLostJace me .pay
  let beholdTimingOk : Bool :=
    thaliaNonOwnerTaxOk && addCostReducedOk && notRevealedAt6012b && revealedAt6012h &&
    gBehReversed.stack.isEmpty && gBehReversed.proposedSpell.isNone

  -- 4d. Morph face-down cast under Thalia costs `{3}` (not `{4}`), and colored Impending under `PlayPermission.anyMana` becomes generic `{2}`!
  let morphNoncrDef21 : CardDef := {
    name := "Phase21 Morph Enchantment"
    manaCost := { symbols := #[.colored .blue] }
    types := #[.enchantment]
    morph := some (ManaCost.ofGeneric 2)
  }
  let impColoredDef21 : CardDef := {
    bear with
    name := "Phase21 Colored Impending"
    impending := some (2, { symbols := #[.colored .blue, .colored .blue] })
  }
  let gMorphThalia0 : Game :=
    let g := addPermanent (insertObject (insertObject afterDraw morphNoncrDef21 me .exile) impColoredDef21 me .exile) thalia21 opp21 opp21
    let exM := (g.objects.filter (fun o => o.name == "Phase21 Morph Enchantment" && o.zone == .exile))[0]!.id
    let exI := (g.objects.filter (fun o => o.name == "Phase21 Colored Impending" && o.zone == .exile))[0]!.id
    (g.createEffect (.playPermission exM { player := me, anyMana := true } (d := .untilEndOfTurn))
      (cause := some testCause)).createEffect (.playPermission exI { player := me, anyMana := true } (d := .untilEndOfTurn))
      (cause := some testCause)
  let exMorphId := (gMorphThalia0.objects.filter (fun o => o.name == "Phase21 Morph Enchantment" && o.zone == .exile))[0]!.id
  let exImpAnyId := (gMorphThalia0.objects.filter (fun o => o.name == "Phase21 Colored Impending" && o.zone == .exile))[0]!.id
  let gMorphProp : Game := mustApply (mustApply gMorphThalia0 me (.cast exMorphId)) me (.announceKicker true)
  let gImpAnyProp : Game := mustApply (mustApply gMorphThalia0 me (.cast exImpAnyId)) me (.announceKicker true)
  let morphCostOk : Bool :=
    gMorphProp.proposedSpell.map (·.cost) == some (ManaCost.ofGeneric 3) &&
    gImpAnyProp.proposedSpell.map (·.cost) == some (ManaCost.ofGeneric 2)

  -- 4e. CR 602.2b / 733.1 partial-payment non-cancellation: once `{1}` mana is paid on `{1}, Sacrifice another creature:`, `.decline` is blocked while a creature exists!
  let sacAbDef21 : CardDef := {
    name := "Phase21 Altar"
    types := #[.artifact]
    activatedAbilities := #[{
      cost := { mana := ManaCost.ofGeneric 1, sacrificeAnotherCreature := true }
      effect := Effect.draw 1
    }]
  }
  let gSacAb0 : Game := (addPermanent (addPermanent afterDraw sacAbDef21 me me) bear me me).addMana me .colorless 1
  let altarId := (gSacAb0.battlefield.filter (·.name == "Phase21 Altar"))[0]!.id
  let sacBearId := (gSacAb0.battlefield.filter (·.name == bear.name))[0]!.id
  let gSacAbPaidMana : Game := mustApply (mustApply gSacAb0 me (.activate altarId 0)) me .pay
  let declineBlockedAfterMana : Bool := !(gSacAbPaidMana.apply me .decline).isOk
  let (gSacAbNoCreature, _) := gSacAbPaidMana.move sacBearId .exile none (cause := some testCause)
  let gSacAbRev : Game := mustApply gSacAbNoCreature me .decline
  let partialPaymentNonCancelOk : Bool :=
    declineBlockedAfterMana &&
    gSacAbRev.stack.isEmpty &&
    gSacAbRev.proposedSpell.isNone &&
    (gSacAbRev.player me).manaPool.total == 1

  mustHold21 "4a.silenceBlocksAllOk" silenceBlocksAllOk &&
  mustHold21 "4b.canCastParityOk" canCastParityOk &&
  mustHold21 "4c.beholdTimingOk" beholdTimingOk &&
  mustHold21 "4d.morphCostOk" morphCostOk &&
  mustHold21 "4e.partialPaymentNonCancelOk" partialPaymentNonCancelOk &&
  mustHold21 "4.replay" ([gSilence0, gOppTurn0, gGyThresh0, gThaliaProp, gBehPayGen, gBehPaid, gBehReversed, gMorphProp, gImpAnyProp, gSacAbPaidMana, gSacAbRev].all (fun g =>
    Game.replayEvents g.events == g && allRulesEventsClassified g))

-- 5. Modal `chooseBothIfTeamwork` gating, CR 110.1 / 115.1c / 115.10a `.youTargetSomething`
--    player/permanent filter, CR 707.10 vs CR 707.12 copy cast semantics, and Impending / face-down Morph stack copies.
#guard
  -- 5a. Modal `chooseBothIfTeamwork`: only chooses both modes when ALL modes have legal targets!
  let twModalDef21 : CardDef := {
    name := "Phase21 Teamwork Command"
    manaCost := ManaCost.empty
    types := #[.sorcery]
    teamwork := some 2
    chooseBothIfTeamwork := true
    spellModes := #[
      Effect.canonicalDestroy .creature,
      Effect.canonicalDestroy .artifact
    ]
  }
  let relicTw21 : CardDef := { name := "Phase21 Target Artifact", types := #[.artifact] }
  let gTwOne0 : Game := insertObject (addPermanent afterDraw bear me me) twModalDef21 me (.hand me)
  let twBearId := (gTwOne0.battlefield.filter (·.name == bear.name))[0]!.id
  let twCard1 := (gTwOne0.player me).hand.back!
  let gTwOne1 : Game :=
    mustApply (mustApply (mustApply (mustApply gTwOne0 me (.cast twCard1)) me (.chooseMode 0)) me (.announceTeamwork true)) me (.choosePermanents #[twBearId])
  let gTwBoth0 : Game := addPermanent gTwOne0 relicTw21 opp21 opp21
  let gTwBoth1 : Game :=
    mustApply (mustApply (mustApply (mustApply gTwBoth0 me (.cast twCard1)) me (.chooseMode 0)) me (.announceTeamwork true)) me (.choosePermanents #[twBearId])
  let teamworkModalOk : Bool :=
    gTwOne1.chosenModesOf (gTwOne1.object! gTwOne1.proposedSpell.get!.spellId) == #[0] &&
    gTwBoth1.chosenModesOf (gTwBoth1.object! gTwBoth1.proposedSpell.get!.spellId) == #[0, 1]

  -- 5b. CR 110.1 / 115.1c / 115.10a `.youTargetSomething` fires on `.player` / `.permanent`, NOT `.card` (graveyard or stack)!
  let youTargetTrig21 : TriggeredAbility :=
    .triggered .fromEffect (Effect.ofTrigger (.watch .youTargetDrawOnce))
  let watcher21 : CardDef := {
    name := "Phase21 Target Watcher"
    types := #[.enchantment]
    triggeredAbilities := #[youTargetTrig21]
  }
  let targeterArt21 : CardDef := {
    name := "Phase21 Targeter"
    types := #[.artifact]
    activatedAbilities := #[
      { cost := {}, effect := Effect.returnCreatureFromGyThenAmass 0 },
      { cost := {}, effect := Effect.counterSpell },
      { cost := {}, effect := shock.spellEffect.get! }
    ]
  }
  let dummySorc21 : CardDef := {
    name := "Phase21 Stack Dummy"
    manaCost := ManaCost.empty
    types := #[.sorcery]
    spellEffect := some (Effect.draw 1)
  }
  let gYtBase : Game :=
    insertObject (insertObject (addPermanent (addPermanent (addPermanent afterDraw watcher21 me me) targeterArt21 me me) bear opp21 opp21) bear me (.graveyard me)) dummySorc21 me (.hand me)
  let targeterId := (gYtBase.battlefield.filter (·.name == "Phase21 Targeter"))[0]!.id
  let gyBearId := (gYtBase.objects.filter (fun o => o.name == bear.name && o.zone == .graveyard me))[0]!.id
  let dummySpId := (gYtBase.objects.filter (fun o => o.name == "Phase21 Stack Dummy" && o.zone == .hand me))[0]!.id
  let gYtWithSpell : Game := mustApply gYtBase me (.cast dummySpId)
  let stackSpellTargetId := gYtWithSpell.stack[0]!.objectId
  let gYtGy : Game := mustApply (mustApply gYtWithSpell me (.activate targeterId 0)) me (.target (.card gyBearId))
  let gyDidNotTrigger : Bool := gYtGy.stack.size == 2
  let gYtStack : Game := mustApply (mustApply gYtGy me (.activate targeterId 1)) me (.target (.card stackSpellTargetId))
  let stackSpellDidNotTrigger : Bool := gYtStack.stack.size == 3
  let gYtPing : Game := mustApply (mustApply gYtStack me (.activate targeterId 2)) me (.target (.player opp21))
  let playerDidTrigger : Bool := gYtPing.stack.size == 5
  let youTargetFilterOk : Bool := gyDidNotTrigger && stackSpellDidNotTrigger && playerDidTrigger

  -- 5c. CR 707.10 stack copies (`wasCast == false`, Impending & face-down Morph stack copies) vs CR 707.12 `createPreparedCopy` (`isCopy == true`, cast)!
  let impCopyDef21 : CardDef := { bear with name := "Phase21 Impending Copy", impending := some (2, ManaCost.empty) }
  let gImp0 : Game := insertObject afterDraw impCopyDef21 me (.hand me)
  let impCardId := (gImp0.player me).hand.back!
  let gImpStack : Game := mustApply (mustApply gImp0 me (.cast impCardId)) me (.announceKicker true)
  let origImpStackId := gImpStack.stack.back!.objectId
  let gImpCopied : Game := gImpStack.copyStackSpell (gImpStack.object! origImpStackId) me
  let copyImpStackId := gImpCopied.stack.back!.objectId
  let gImpCopyRes : Game := gImpCopied.resolveTop
  let copyImpPerm := (gImpCopyRes.battlefield.filter (·.name == "Phase21 Impending Copy"))[0]!
  let morphCopyDef21 : CardDef := { bear with name := "Phase21 Morph Copy", power := some 5, toughness := some 5, morph := some (ManaCost.ofGeneric 2) }
  let gMph0 : Game := (insertObject afterDraw morphCopyDef21 me (.hand me)).addMana me .colorless 3
  let mphCardId := (gMph0.player me).hand.back!
  let gMphStack : Game := mustApply (mustApply (mustApply gMph0 me (.cast mphCardId)) me (.announceKicker true)) me .pay
  let gMphCopied : Game := gMphStack.copyStackSpell (gMphStack.object! gMphStack.stack.back!.objectId) me
  let mphCopyStackObj := gMphCopied.object! gMphCopied.stack.back!.objectId
  let gMphCopyRes : Game := gMphCopied.resolveTop
  let mphCopyPerm := (gMphCopyRes.battlefield.filter (·.printed.isToken))[0]!
  -- CR 707.12 `createPreparedCopy`: `isCopy == true` in `.exile`, survives SBA while prepared (ruling 736),
  -- casting emits `CastEvent.announced`, and copy ceases to exist after resolving!
  let prepFace21 : AdventureFace := { name := "Phase21 Prepared Bolt", manaCost := ManaCost.empty, types := #[.instant], spellEffect := some (Effect.draw 1) }
  let prepHostDef21 : CardDef := { bear with name := "Phase21 Prepared Host", prepareFace := some prepFace21 }
  let gPrep0 : Game := addPermanent afterDraw prepHostDef21 me me
  let prepHost := (gPrep0.battlefield.filter (·.name == "Phase21 Prepared Host"))[0]!
  let gPrep1 : Game := gPrep0.becomePrepared prepHost (cause := some testCause)
  let prepCopyObj := (gPrep1.objects.filter (fun o => o.name == "Phase21 Prepared Bolt" && o.zone == .exile))[0]!
  let gPrepSba : Game := gPrep1.checkSBA
  let gPrepCast : Game := (mustApply gPrep1 me (.cast prepCopyObj.id)).resolveTop
  let copySemanticsOk : Bool :=
    !gImpCopied.wasCast copyImpStackId &&
    copyImpPerm.printed.isToken &&
    copyImpPerm.status.time == 2 &&
    !gImpCopyRes.isCreature copyImpPerm &&
    mphCopyStackObj.status.faceDown &&
    mphCopyPerm.printed.isToken &&
    mphCopyPerm.status.faceDown &&
    gMphCopyRes.name mphCopyPerm == "" &&
    gMphCopyRes.power mphCopyPerm == 2 &&
    gMphCopyRes.toughness mphCopyPerm == 2 &&
    prepCopyObj.isCopy &&
    (gPrepSba.objects.filter (fun o => o.name == "Phase21 Prepared Bolt" && o.zone == .exile)).size == 1 &&
    !(gPrepCast.player me).graveyard.any (fun id => (gPrepCast.object! id).name == "Phase21 Prepared Bolt") &&
    gPrepCast.events.any (fun e => match e.change with | .rules (.cast (.spellCast ..)) => true | _ => false)

  mustHold21 "5a.teamworkModalOk" teamworkModalOk &&
  mustHold21 "5b.youTargetFilterOk" youTargetFilterOk &&
  mustHold21 "5c.copySemanticsOk" copySemanticsOk &&
  mustHold21 "5.replay" ([gTwOne1, gTwBoth1, gYtGy, gYtStack, gYtPing, gImpCopied, gImpCopyRes, gMphCopied, gMphCopyRes, gPrep1, gPrepCast].all (fun g =>
    Game.replayEvents g.events == g && allRulesEventsClassified g))

-- 6. Two-Headed Giant CR 810.8d 15-poison team SBA, CR 805.10d–e / 810.7 shared team blocking &
--    `legalBlockerCount`, CR 500.4 / 514.2 / 723.1 / 805.4 / 810.2 mid-shared-turn `playerControl` &
--    `.untilNextTurnOf` expiry & 2HG opponent filters, and simultaneous `withBatch` invariants.
#guard
  -- 6a. CR 810.8d: 10 + 4 = 14 poison survives in 2HG, whereas 10 + 5 = 15 loses!
  let gPsn14 : Game :=
    ((mkTwoHeadedGiant21.record
      (GameEvent.poisoned mkTwoHeadedGiant21.turnNumber ⟨0⟩ 10 (cause := testCause))).record
      (GameEvent.poisoned mkTwoHeadedGiant21.turnNumber ⟨1⟩ 4 (cause := testCause))).checkSBA
  let gPsn15 : Game :=
    (gPsn14.record
      (GameEvent.poisoned gPsn14.turnNumber ⟨1⟩ 1 (cause := testCause))).checkSBA
  let poison2hgOk : Bool :=
    !gPsn14.over &&
    !(gPsn14.player ⟨0⟩).lost &&
    gPsn15.over &&
    (gPsn15.player ⟨0⟩).lost &&
    (gPsn15.player ⟨1⟩).lost

  -- 6b. CR 805.10d–e / 810.7: menace attacker blocked jointly by `⟨2⟩`'s creature + teammate `⟨3⟩`'s creature!
  let menaceAtk21 : CardDef := { bear with name := "Phase21 Menace", keywords := { menace := true, haste := true } }
  let gBlk2h0 : Game :=
    let g := addPermanent (addPermanent (addPermanent mkTwoHeadedGiant21 bear ⟨2⟩ ⟨2⟩) hero ⟨3⟩ ⟨3⟩) menaceAtk21 ⟨0⟩ ⟨0⟩
    g.beginStep .declareAttackers
  let mAtkId := (gBlk2h0.battlefield.filter (·.name == "Phase21 Menace"))[0]!.id
  let b2Id := (gBlk2h0.battlefield.filter (·.name == bear.name))[0]!.id
  let b3Id := (gBlk2h0.battlefield.filter (·.name == hero.name))[0]!.id
  let gBlk2hAtk : Game := mustApply gBlk2h0 ⟨0⟩ (.declareAttackers #[mAtkId] (some ⟨2⟩) #[] #[])
  let gBlk2hStep : Game := gBlk2hAtk.advanceStep
  let blkChooser := gBlk2hStep.currentBlockersPlayer
  let singleBlkRejected : Bool := !(gBlk2hStep.declareBlockers blkChooser #[(b2Id, mAtkId)]).isOk
  let gBlk2hJoint : Game := mustApply gBlk2hStep blkChooser (.declareBlockers #[(b2Id, mAtkId), (b3Id, mAtkId)])
  let sharedBlockingOk : Bool :=
    gBlk2hStep.legalBlockerCount (gBlk2hStep.object! mAtkId) 2 &&
    !gBlk2hStep.legalBlockerCount (gBlk2hStep.object! mAtkId) 1 &&
    singleBlkRejected &&
    (gBlk2hJoint.object! mAtkId).status.blocked &&
    (gBlk2hJoint.blockersOf mAtkId).size == 2

  -- 6c. Mid-shared-turn `playerControl` (`onNextTurn := true`) & `.untilNextTurnOf` wait for the NEXT shared turn,
  --     and `costReductionEqualOppArtifacts` ignores teammate artifacts in 2HG!
  let oppArtSpell21 : CardDef := {
    name := "Phase21 Opp Art Spell"
    manaCost := ManaCost.ofGeneric 3
    types := #[.sorcery]
    costReductionEqualOppArtifacts := true
  }
  let art21 : CardDef := { name := "Phase21 Art", types := #[.artifact] }
  let g2hArt0 : Game :=
    insertObject (addPermanent (addPermanent (addPermanent mkTwoHeadedGiant21 art21 ⟨1⟩ ⟨1⟩) art21 ⟨1⟩ ⟨1⟩) art21 ⟨2⟩ ⟨2⟩) oppArtSpell21 ⟨0⟩ (.hand ⟨0⟩)
  let artSpellObj := g2hArt0.object! (g2hArt0.player ⟨0⟩).hand.back!
  -- Teammate `⟨1⟩` has 2 artifacts (ignored!), opponent `⟨2⟩` has 1 artifact -> `{3}` reduced by 1 = `{2}`!
  let oppArtFilterOk : Bool := g2hArt0.playManaCost artSpellObj oppArtSpell21 == ManaCost.ofGeneric 2
  -- Start on Team B seat 1 (`⟨2⟩`, two seat advances from `⟨0⟩` -> `⟨1⟩` -> `⟨2⟩`), then grant `⟨0⟩` `playerControl ⟨0⟩ ⟨2⟩ true` and `.untilNextTurnOf ⟨2⟩`:
  let gMidTeamB1 : Game :=
    let g := mkTwoHeadedGiant21.startNextTurnAndBegin.startNextTurnAndBegin -- activePlayer == ⟨2⟩ (seat 1 of Team B's shared turn)
    let g := g.withResolvingContext none ⟨0⟩ fun g => g.setPlayerControl ⟨0⟩ ⟨2⟩ (onNextTurn := true)
    g.createEffect (.playerRule ⟨0⟩ (.additionalLands 1) (.untilNextTurnOf ⟨2⟩)) (cause := some testCause)
  let gMidTeamB2 : Game := gMidTeamB1.startNextTurnAndBegin -- activePlayer == ⟨3⟩ (seat 2 of SAME shared turn!)
  let gNextTeamA1 : Game := gMidTeamB2.startNextTurnAndBegin -- ⟨0⟩
  let gNextTeamA2 : Game := gNextTeamA1.startNextTurnAndBegin -- ⟨1⟩
  let gNextTeamB1 : Game := gNextTeamA2.startNextTurnAndBegin -- NEXT shared turn of Team B (`⟨2⟩`)!
  let gNextTeamB2 : Game := gNextTeamB1.startNextTurnAndBegin -- seat 2 (`⟨3⟩`) of Team B's NEXT shared turn!
  let gAfterNextTeamB : Game := gNextTeamB2.startNextTurnAndBegin -- back to `⟨0⟩` -> expires!
  let midSharedTurnOk : Bool :=
    oppArtFilterOk &&
    gMidTeamB1.activePlayer == ⟨2⟩ &&
    !gMidTeamB1.controlsPlayer ⟨0⟩ ⟨2⟩ &&
    gMidTeamB1.additionalLandsThisTurn ⟨0⟩ == 1 &&
    gMidTeamB2.activePlayer == ⟨3⟩ &&
    !gMidTeamB2.controlsPlayer ⟨0⟩ ⟨2⟩ &&
    !gMidTeamB2.controlsPlayer ⟨0⟩ ⟨3⟩ &&
    gMidTeamB2.additionalLandsThisTurn ⟨0⟩ == 1 &&
    gNextTeamB1.activePlayer == ⟨2⟩ &&
    gNextTeamB1.controlsPlayer ⟨0⟩ ⟨2⟩ &&
    gNextTeamB1.controlsPlayer ⟨0⟩ ⟨3⟩ &&
    gNextTeamB1.additionalLandsThisTurn ⟨0⟩ == 0 &&
    gNextTeamB2.activePlayer == ⟨3⟩ &&
    gNextTeamB2.controlsPlayer ⟨0⟩ ⟨2⟩ &&
    gNextTeamB2.controlsPlayer ⟨0⟩ ⟨3⟩ &&
    !gAfterNextTeamB.controlsPlayer ⟨0⟩ ⟨2⟩

  -- 6d. Simultaneous `withBatch`: `emptyManaPools`, `setRingBearer`, and two-batch `finishFrcRestBottom` (`applyDackOnHits`)!
  let gPool0 : Game := (afterDraw.addMana me (.colored .red) 1).addMana opp21 (.colored .green) 1
  let prePoolIdx := gPool0.events.size
  let gPool1 : Game := gPool0.emptyManaPools
  let poolBatches := (gPool1.events.extract prePoolIdx gPool1.events.size).filterMap fun e =>
    match e.change with | .rules (.player (.manaEmptied ..)) => some e.batch | _ => none
  let gRb0 : Game := addPermanent (addPermanent afterDraw bear me me) hero me me
  let rb1 := (gRb0.battlefield.filter (·.name == bear.name))[0]!.id
  let rb2 := (gRb0.battlefield.filter (·.name == hero.name))[0]!.id
  let gRb1 : Game := gRb0.setRingBearer me (some rb1) (cause := some testCause)
  let preRbIdx := gRb1.events.size
  let gRb2 : Game := gRb1.setRingBearer me (some rb2) (cause := some testCause)
  let rbBatches := (gRb2.events.extract preRbIdx gRb2.events.size).filterMap fun e =>
    match e.change with | .rules (.permanent (.designation _ .ringBearer _)) => some e.batch | _ => none
  let gDack0 : Game := addPermanent (addPermanent mkThreePlayer21 bear ⟨0⟩ ⟨0⟩) hero ⟨0⟩ ⟨0⟩
  let dHit1 := (gDack0.battlefield.filter (·.name == bear.name))[0]!.id
  let dHit2 := (gDack0.battlefield.filter (·.name == hero.name))[0]!.id
  let preDackIdx := gDack0.events.size
  let gDack1 : Game := gDack0.finishFrcRestBottom ⟨0⟩ #[] false (cause := some testCause) (dackTargets := #[dHit1, dHit2])
  let goadBatches := (gDack1.events.extract preDackIdx gDack1.events.size).filterMap fun e =>
    match e.change with | .rules (.permanent (.designation _ (.goaded ..) true)) => some e.batch | _ => none
  let ctrlBatches := (gDack1.events.extract preDackIdx gDack1.events.size).filterMap fun e =>
    match e.change with | .rules (.continuousEffect (.created _ (.layered _ (.control _) _))) => some e.batch | _ => none
  let batchInvariantsOk : Bool :=
    poolBatches.size == 2 && poolBatches[0]!.isSome && poolBatches[0]! == poolBatches[1]! &&
    rbBatches.size == 2 && rbBatches[0]!.isSome && rbBatches[0]! == rbBatches[1]! &&
    goadBatches.size == 2 && goadBatches[0]!.isSome && goadBatches[0]! == goadBatches[1]! &&
    ctrlBatches.size == 2 && ctrlBatches[0]!.isSome && ctrlBatches[0]! == ctrlBatches[1]! &&
    goadBatches[0]! != ctrlBatches[0]!

  mustHold21 "6a.poison2hgOk" poison2hgOk &&
  mustHold21 "6b.sharedBlockingOk" sharedBlockingOk &&
  mustHold21 "6c.midSharedTurnOk" midSharedTurnOk &&
  mustHold21 "6d.batchInvariantsOk" batchInvariantsOk &&
  mustHold21 "6.replay" ([gPsn14, gPsn15, gBlk2hJoint, g2hArt0, gMidTeamB1, gMidTeamB2, gNextTeamB1, gNextTeamB2, gAfterNextTeamB, gPool1, gRb2, gDack1].all (fun g =>
    Game.replayEvents g.events == g && allRulesEventsClassified g))

end Phase21EventAlignment

section Phase22EventAlignment

def opp22 : PlayerId := ⟨1⟩

def mustHold22 (label : String) (ok : Bool) : Bool :=
  if ok then true else panic! s!"Phase 22 guard failed: {label}"

-- 1. Typed `TriggerReflexiveKind` / `KeywordChoice` / `TriggerExileMode`, non-smuggled
--    `fraCauseId` / `fraCauseController` / `chosenMode` trigger reads, and sentinel-free
--    `Option ObjectId := none` prompts.
#guard
  -- 1a. Typed `TriggerReflexiveKind` (`.dealTwoDamage`, `.divideSevenDamage`) & `KeywordChoice`:
  let gRef2 : Game :=
    let g := addPermanent afterDraw bear opp22 opp22
    let bId := (g.battlefield.filter (·.name == bear.name))[0]!.id
    let g := g.queueModeledReflexive me none .dealTwoDamage
    let g := mustApply g me (.target (Target.permanent bId))
    g.resolveTop
  let bAfterRef2 := (gRef2.battlefield.filter (·.name == bear.name))[0]!
  let gKw0 : Game :=
    let g := addPermanent afterDraw bear me me
    let bId := (g.battlefield.filter (·.name == bear.name))[0]!.id
    g.change (.pending (.fraChoice me (.chooseKeyword bId #[.trample, .hexproof])))
  let gKw1 : Game := mustApply gKw0 me (.chooseMode 0)
  let kwBear := (gKw1.battlefield.filter (·.name == bear.name))[0]!
  let typedKindKwOk : Bool :=
    bAfterRef2.status.damage == 2 &&
    gKw1.pending == .none &&
    (gKw1.effectiveKeywords kwBear).trample &&
    !(gKw1.effectiveKeywords kwBear).hexproof &&
    TriggerExileMode.playUntilNextTurn != TriggerExileMode.playThisTurn

  -- 1b. Non-smuggled `fraCauseController`, `fraCauseId` (`.forestsExceptCause`, `villainConniveTarget?`),
  --     and `StackEntry.chosenMode` (`resolvingModes` on `.stepHydeChoose`):
  let gMillCtrl : Game :=
    let g := afterDraw
    let abId : ObjectId := ⟨g.nextObjectId⟩
    let snap : EventObject := { owner := me, controller := some me, name := "Phase22 Mill Src", zone := .battlefield }
    let ab : TriggeredAbility := .onPlayerLosesLifeMillThatMany
    let g := g.record (GameEvent.triggerPutOnStack g.turnNumber abId snap me
      (spec := { triggeredAbility := some ab, lastKnownPower := some 2, fraCauseController := some opp22 }))
    let preLib := (g.player opp22).library.size
    let g := g.resolveTop
    if (g.player opp22).library.size == preLib - 2 then g else panic! "mill count mismatch"
  let forest22 : CardDef := { name := "Phase22 Forest", types := #[.land], supertypes := #[.basic], subtypes := #["Forest"] }
  let gFor0 : Game := addPermanent (addPermanent (addPermanent afterDraw forest22 me me) forest22 me me) forest22 me me
  let fIds := (gFor0.battlefield.filter (·.name == "Phase22 Forest")).map (·.id)
  let abForId : ObjectId := ⟨gFor0.nextObjectId⟩
  let gFor1 : Game :=
    let g := gFor0.record (GameEvent.triggerPutOnStack gFor0.turnNumber abForId (gFor0.snapshot (gFor0.object! fIds[0]!)) me
      (spec := { sourceId := some fIds[0]!, fraCauseId := some fIds[0]! }))
    g.changes #[.popStack, .pushContinuationFrame { resolvingAbility := some abForId }]
  let (_, twoOtherForestsOk) := gFor1.triggerIfHolds me (.onEnterDraw 1) (some fIds[0]!) #[] none
    (.atLeast (.count .forestsExceptCause) (.fixed 2))
  let (_, threeOtherForestsOk) := gFor1.triggerIfHolds me (.onEnterDraw 1) (some fIds[0]!) #[] none
    (.atLeast (.count .forestsExceptCause) (.fixed 3))
  let villain22 : CardDef := { bear with name := "Phase22 Villain", subtypes := #["Villain"] }
  let gVil0 : Game := addPermanent (addPermanent afterDraw villain22 me me) bear me me
  let vilId := (gVil0.battlefield.filter (·.name == "Phase22 Villain"))[0]!.id
  let srcBearId := (gVil0.battlefield.filter (·.name == bear.name))[0]!.id
  let abVilId : ObjectId := ⟨gVil0.nextObjectId⟩
  let gVil1 : Game :=
    let g := gVil0.record (GameEvent.triggerPutOnStack gVil0.turnNumber abVilId (gVil0.snapshot (gVil0.object! srcBearId)) me
      (spec := { sourceId := some srcBearId, fraCauseId := some vilId }))
    g.changes #[.popStack, .pushContinuationFrame { resolvingAbility := some abVilId }]
  let vilTargetOk : Bool := gVil1.villainConniveTarget? me srcBearId #[] == some vilId
  let hydeAb : TriggeredAbility := .onStep Effect.stepHydeChoose
  let gHyde0 : Game :=
    let g := addPermanent afterDraw bear me me
    let bId := (g.battlefield.filter (·.name == bear.name))[0]!.id
    let abId : ObjectId := ⟨g.nextObjectId⟩
    let g := g.record (GameEvent.triggerPutOnStack g.turnNumber abId (g.snapshot (g.object! bId)) me
      (spec := { triggeredAbility := some hydeAb, sourceId := some bId }))
    let g := g.record (GameEvent.announced g.turnNumber abId (modes := #[0]))
    g.resolveTop
  let hydeBear := (gHyde0.battlefield.filter (·.name == bear.name))[0]!
  let nonSmuggledOk : Bool :=
    twoOtherForestsOk && !threeOtherForestsOk && vilTargetOk &&
    hydeBear.status.plusOnePlusOne == 1

  -- 1c. Sentinel-free `Option ObjectId := none` prompts:
  let gPlace0 : Game :=
    (afterDraw.change (.pushContinuationFrame {})).changes #[
      .continuation (.spellOr #[{ resolution := .ofSpell (.draw (.fixed 1) .you), phrase := "Draw a card" }]),
      .continuation (.spellOrController me),
      .pending (.chooseLibraryPlacement me none)]
  let gPlace1 : Game := mustApply gPlace0 me .chooseTop
  let gWardNone0 : Game :=
    let g := (afterDraw.change (.pushContinuationFrame {})).changes #[
      .continuation (.unlessPaysDue true),
      .continuation (.unlessPaysController me),
      .continuation (.unlessPaysInstead (some (.draw 1))),
      .pending (.payOrLetCounter me 2 none)]
    mustApply g me .decline
  let art22 : CardDef := { name := "Phase22 Art", types := #[.artifact] }
  let gPutArt0 : Game :=
    let g := insertObject afterDraw art22 me (.hand me)
    g.change (.pending (.mayPutArtifactFromHand me none))
  let gPutArt1 : Game := mustApply gPutArt0 me .decline
  let gHydeNone0 : Game :=
    afterDraw.change (.pending (.fraChoice me (.hydeMode none)))
  let gHydeNone1 : Game := mustApply gHydeNone0 me (.chooseMode 0)
  let gPickNone0 : Game :=
    let g := addPermanent afterDraw art22 me me
    g.change (.pending (.fraChoice me (.mayPayPickThen .sacrificeAnotherArtifact .searchBasicLandTapped none)))
  let artPermId := (gPickNone0.battlefield.filter (·.name == "Phase22 Art"))[0]!.id
  let gPickNone1 : Game := mustApply gPickNone0 me (.choosePermanents #[artPermId])
  let sentinelFreeOk : Bool :=
    gPlace1.pending == .none &&
    (gWardNone0.player me).hand.size == (afterDraw.player me).hand.size + 1 &&
    gPutArt1.pending == .none &&
    gHydeNone1.pending == .none &&
    !gPickNone1.battlefield.any (·.name == "Phase22 Art")

  mustHold22 "1a.typedKindKwOk" typedKindKwOk &&
  mustHold22 "1b.nonSmuggledOk" nonSmuggledOk &&
  mustHold22 "1c.sentinelFreeOk" sentinelFreeOk &&
  mustHold22 "1.replay" ([gRef2, gKw1, gMillCtrl, gFor1, gVil1, gHyde0, gPlace1, gWardNone0, gPutArt1, gHydeNone1, gPickNone1].all (fun g =>
    Game.replayEvents g.events == g && allRulesEventsClassified g))

-- 2. Pause-safe library-exile loops (`exileLibraryUntilNonlandLoop`, `resolveCascade`,
--    `grimaExileUntilInstantOrSorcery`) and `requestOrderInto` when entered under
--    `Pending.chooseReplacement` without spinning infinitely or clobbering `.chooseReplacement`.
#guard
  let idExA : ReplacementId := { kind := .exileOppDeath, object := some ⟨920⟩ }
  let idExB : ReplacementId := { kind := .exileOppDeath, object := some ⟨921⟩ }
  let land22 : CardDef := { name := "Phase22 Land", types := #[.land] }
  let bolt22 : CardDef := {
    name := "Phase22 Bolt"
    manaCost := ManaCost.ofGeneric 1
    types := #[.instant]
    spellEffect := some { resolution := .ofSpell (.draw (.fixed 1) .you), phrase := "Draw a card" }
  }
  let mkPausedGyMove (base : Game) : Game :=
    let g := (base.createEffect
      (.replacement { id := idExA, affectedPlayer := me, kind := .exileInsteadOfGraveyard none false })
      (cause := some testCause)).createEffect
      (.replacement { id := idExB, affectedPlayer := me, kind := .exileInsteadOfGraveyard none false })
      (cause := some testCause)
    let hId := (g.player me).hand.back!
    (g.move hId (.graveyard me) none (cause := some testCause)).1

  -- 2a. `exileLibraryUntilNonlandLoop` entered while `g.pending == .chooseReplacement`:
  let gNonland0 : Game :=
    let g := emptyLibrary afterDraw opp22
    let g := insertObject (insertObject g bolt22 opp22 (.library opp22)) land22 opp22 (.library opp22)
    let g := mkPausedGyMove g
    g.exileLibraryUntilNonlandLoop opp22 me none (some testCause)
  let nonlandPaused :=
    match gNonland0.pending with
    | .chooseReplacement p cs => p == me && cs.size == 2 && (gNonland0.player opp22).library.size == 2
    | _ => false
  let gNonland1 : Game := mustApply gNonland0 me (.chooseReplacement idExA)
  let nonlandDoneOk : Bool :=
    nonlandPaused &&
    (gNonland1.player opp22).library.isEmpty &&
    gNonland1.objects.any (fun o => o.name == "Phase22 Bolt" && o.zone == .exile && (gNonland1.playPermission o).isSome)

  -- 2b. `resolveCascade` entered while `g.pending == .chooseReplacement`:
  let gCas0 : Game :=
    let g := emptyLibrary afterDraw me
    let g := insertObject (insertObject g bolt22 me (.library me)) land22 me (.library me)
    let g := mkPausedGyMove g
    g.resolveCascade me 3
  let casPaused :=
    match gCas0.pending with
    | .chooseReplacement p cs => p == me && cs.size == 2 && (gCas0.player me).library.size == 2
    | _ => false
  let gCas1 : Game := mustApply gCas0 me (.chooseReplacement idExA)
  let gCas2 : Game := mustApply gCas1 me .decline
  let cascadeDoneOk : Bool :=
    casPaused &&
    (match gCas1.pending with | .fraChoice _ (.mayCastCascade ..) => true | _ => false) &&
    gCas2.pending == .none &&
    (gCas2.player me).library.size == 2

  -- 2c. `grimaExileUntilInstantOrSorcery` & `requestOrderInto` entered under `Pending.chooseReplacement`:
  let gGrima0 : Game :=
    let g := emptyLibrary afterDraw opp22
    let g := insertObject (insertObject g bolt22 opp22 (.library opp22)) land22 opp22 (.library opp22)
    let g := mkPausedGyMove g
    g.grimaExileUntilInstantOrSorcery me opp22 false
  let grimaPaused :=
    match gGrima0.pending with
    | .chooseReplacement p cs => p == me && cs.size == 2 && (gGrima0.player opp22).library.size == 2
    | _ => false
  let gGrima1 : Game := mustApply gGrima0 me (.chooseReplacement idExA)
  let gOrd0 : Game :=
    let g := insertObject (insertObject afterDraw bear opp22 .exile) hero opp22 .exile
    let exIds := (g.objects.filter (fun o => o.zone == .exile && o.owner == opp22)).map (·.id)
    let g := mkPausedGyMove g
    g.requestOrderInto exIds (.library opp22) "Phase22 order" (cause := some testCause)
  let ordPaused :=
    match gOrd0.pending with
    | .chooseReplacement p _ =>
      p == me && (gOrd0.objects.filter (fun o => o.zone == .exile && o.owner == opp22)).size == 2
    | _ => false
  let gOrd1 : Game := mustApply gOrd0 me (.chooseReplacement idExA)
  let grimaAndOrderOk : Bool :=
    grimaPaused &&
    gGrima1.pending == .none &&
    (gGrima1.player opp22).library.size == 2 &&
    ordPaused &&
    gOrd1.pending == .none &&
    (gOrd1.objects.filter (fun o => o.zone == .exile && o.owner == opp22)).isEmpty

  mustHold22 "2a.nonlandDoneOk" nonlandDoneOk &&
  mustHold22 "2b.cascadeDoneOk" cascadeDoneOk &&
  mustHold22 "2c.grimaAndOrderOk" grimaAndOrderOk &&
  mustHold22 "2.replay" ([gNonland0, gNonland1, gCas0, gCas1, gCas2, gGrima0, gGrima1, gOrd0, gOrd1].all (fun g =>
    Game.replayEvents g.events == g && allRulesEventsClassified g))

-- 3. `outerCont?` preservation in `.sarumanExileCopyMayCast`, `.fblthpSearch`, &
--    `castExiledAsAbilityResolves`, plus post-move `followMovedToZone?` in
--    `.exileReturnBrieflyIfMvAtMost`, `.exileFlicker`, and `.exileFromRevealedHand`.
#guard
  let boltDraw22 : CardDef := {
    name := "Phase22 Copy Bolt"
    manaCost := ManaCost.ofGeneric 1
    types := #[.instant]
    spellEffect := some { resolution := .ofSpell (.draw (.fixed 1) .you), phrase := "Draw a card" }
  }
  -- 3a. `.sarumanExileCopyMayCast` preserves `outerCont?` across both decline and accept:
  let gSar0 : Game :=
    let g := insertObject afterDraw boltDraw22 opp22 (.graveyard opp22)
    let bId := (g.player opp22).graveyard.back!
    let g := (g.change (.pushContinuationFrame {})).change
      (.continuation (.pendingReplacement (some (.restorePending (.scry me 1) false))))
    g.applyFraAbility me { targeting := .of (.filtered { noun := "card", zone := .anyGraveyard }), resolution := .sarumanExileCopyMayCast }
      .sarumanExileCopyMayCast #[Target.card bId] none
  let gSarDeclined : Game := mustApply gSar0 me .decline
  let gSarAccepted : Game := mustApply gSar0 me .accept
  let sarOuterOk : Bool :=
    gSarDeclined.pending == .scry me 1 &&
    gSarAccepted.pending == .scry me 1 &&
    gSarAccepted.stack.size == 1

  -- 3b. `.fblthpSearch` preserves `outerCont?`:
  let forestBasic22 : CardDef := { name := "Forest", types := #[.land], supertypes := #[.basic], subtypes := #["Forest"] }
  let gFbl0 : Game :=
    let g := addPermanent (insertObject (emptyLibrary afterDraw me) forestBasic22 me (.library me)) bear me me
    let srcId := (g.battlefield.filter (·.name == bear.name))[0]!.id
    let g := g.record (GameEvent.announced g.turnNumber srcId (x := some 1))
    let g := (g.change (.pushContinuationFrame {})).change
      (.continuation (.pendingReplacement (some (.restorePending (.scry me 1) false))))
    (g.applyFra me { resolution := .fblthpSearch } .fblthpSearch #[] (some srcId)).finishAndGrantPriority
  let fblOuterOk : Bool :=
    gFbl0.pending == .scry me 1 &&
    (gFbl0.player me).hand.any (fun id => (gFbl0.object! id).name == "Forest")

  -- 3c. `castExiledAsAbilityResolves` preserves `outerCont?` on cast AND on cost-reversal + decline:
  let gCastExBase : Game :=
    let g := insertObject afterDraw boltDraw22 me .exile
    let exId := (g.objects.filter (fun o => o.name == "Phase22 Copy Bolt" && o.zone == .exile))[0]!.id
    (g.change (.pushContinuationFrame {})).changes #[
      .continuation (.pendingReplacement (some (.restorePending (.scry me 1) false))),
      .pending (.mayCastExiledElseDamage me exId 2 none)]
  let exBoltId := (gCastExBase.objects.filter (fun o => o.name == "Phase22 Copy Bolt" && o.zone == .exile))[0]!.id
  let gCastExOk : Game :=
    let g := gCastExBase.addMana me (.colored .red) 1
    let g := mustApply g me (.cast exBoltId)
    mustApply g me .pay
  let gCastExCancel1 : Game :=
    let g := mustApply gCastExBase me (.cast exBoltId)
    mustApply g me .pay
  let gCastExCancel2 : Game := mustApply gCastExCancel1 me .decline
  let castExOuterOk : Bool :=
    gCastExOk.pending == .scry me 1 &&
    gCastExOk.stack.size == 1 &&
    (match gCastExCancel1.pending with | .mayCastExiledElseDamage .. => true | _ => false) &&
    gCastExCancel2.pending == .scry me 1 &&
    (gCastExCancel2.player opp22).life == (afterDraw.player opp22).life - 2

  -- 3d. Post-move `followMovedToZone?` in `.exileReturnBrieflyIfMvAtMost`, `.exileFlicker`, & `.exileFromRevealedHand`:
  let gBrief : Game :=
    let g := addPermanent afterDraw bear me me
    let bId := (g.battlefield.filter (·.name == bear.name))[0]!.id
    g.applyFra me { targeting := .of .creature, resolution := .exileReturnBrieflyIfMvAtMost 3 }
      (.exileReturnBrieflyIfMvAtMost 3) #[Target.permanent bId] none
  let briefBear := (gBrief.battlefield.filter (·.name == bear.name))[0]!
  let gFlicker : Game :=
    let g := addPermanent afterDraw bear me me
    let bId := (g.battlefield.filter (·.name == bear.name))[0]!.id
    g.applyModeledTrigger me (.onCasting (Effect.ofTrigger (.casting .exileFlicker))) none #[Target.permanent bId] "Flicker"
  let exiledBear? := gFlicker.objects.find? (fun o => o.name == bear.name && o.zone == .exile)
  let gRevHand0 : Game :=
    let g := addPermanent (insertObject afterDraw boltDraw22 opp22 (.hand opp22)) bear me me
    let srcId := (g.battlefield.filter (·.name == bear.name))[0]!.id
    let hId := (g.player opp22).hand.back!
    let g := g.change (.pending (.fraChoice me (.exileFromRevealedHand opp22 (some srcId))))
    mustApply g me (.choosePermanents #[hId])
  let revSrcId := (gRevHand0.battlefield.filter (·.name == bear.name))[0]!.id
  let exiledHandBolt? := gRevHand0.objects.find? (fun o => o.name == "Phase22 Copy Bolt" && o.zone == .exile)
  let followPostMoveOk : Bool :=
    briefBear.status.tapped &&
    exiledBear?.any (fun ex => ex.id != ⟨0⟩ && gFlicker.delayedTriggers.any (fun dt =>
      match dt.kind with | .endStepReturn oid => oid == ex.id | _ => false)) &&
    exiledHandBolt?.any (fun ex => ex.exiledBy == some revSrcId)

  mustHold22 "3a.sarOuterOk" sarOuterOk &&
  mustHold22 "3b.fblOuterOk" fblOuterOk &&
  mustHold22 "3c.castExOuterOk" castExOuterOk &&
  mustHold22 "3d.followPostMoveOk" followPostMoveOk &&
  mustHold22 "3.replay" ([gSarDeclined, gSarAccepted, gFbl0, gCastExOk, gCastExCancel1, gCastExCancel2, gBrief, gFlicker, gRevHand0].all (fun g =>
    Game.replayEvents g.events == g && allRulesEventsClassified g))

-- 4. Sequential `putCountersDeferredLog`, deferred post-replacement logs (`moveToOwnerGraveyard`,
--    `surveilMoveLoop`), and CR 614.6 arrival-zone checks (`sacrificedCreaturePower`).
#guard
  -- 4a. Sequential `putCountersDeferredLog` chains across `Pending.chooseReplacement` so the second
  --     counter-put reads `before` AFTER the first counter-put resolves (logging 4 and 4, never 8!):
  let idAddCtr22 : ReplacementId := { kind := .addCountersPut, object := some ⟨941⟩ }
  let idMulCtr22 : ReplacementId := { kind := .multiplyCountersPut, object := some ⟨942⟩ }
  let gSeq0 : Game :=
    let g := addPermanent afterDraw hero me me
    let hId := (g.battlefield.filter (·.name == hero.name))[0]!.id
    let g := (g.createEffect
      (.replacement { id := idAddCtr22, affectedPlayer := me, kind := .modifyCountersPut (some hId) (some .plusOnePlusOne) (add := 1) (mult := 1) })
      (cause := some testCause)).createEffect
      (.replacement { id := idMulCtr22, affectedPlayer := me, kind := .modifyCountersPut (some hId) (some .plusOnePlusOne) (add := 0) (mult := 2) })
      (cause := some testCause)
    let g := g.putCountersDeferredLog hId .plusOnePlusOne 1 (some me) (.playerPutsOn me) (cause := some testCause)
    g.putCountersDeferredLog hId .plusOnePlusOne 1 (some me) (.playerPutsOn me) (cause := some testCause)
  let gSeq1 : Game := mustApply gSeq0 me (.chooseReplacement idAddCtr22)
  let gSeq2 : Game := mustApply gSeq1 me (.chooseReplacement idAddCtr22)
  let heroAfterSeq := (gSeq2.battlefield.filter (·.name == hero.name))[0]!
  let seqLogsOk : Bool :=
    (match gSeq0.pending with | .chooseReplacement p cs => p == me && cs.size == 2 | _ => false) &&
    (match gSeq1.pending with | .chooseReplacement p cs => p == me && cs.size == 2 | _ => false) &&
    gSeq2.pending == .none &&
    heroAfterSeq.status.plusOnePlusOne == 8 &&
    !gSeq2.log.any (fun s => s.contains "8 +1/+1") &&
    (gSeq2.log.filter (fun s => s.contains "4 +1/+1")).size == 2

  -- 4b. Deferred post-replacement logs (`moveToOwnerGraveyard` & `surveilMoveLoop`) when replaced to `.exile`,
  --     plus CR 614.6 sacrifice-power check when sacrifice is exiled instead of put into graveyard:
  let idExA22 : ReplacementId := { kind := .exileOppDeath, object := some ⟨940⟩ }
  let gExOnly0 : Game :=
    afterDraw.createEffect
      (.replacement { id := idExA22, affectedPlayer := me, kind := .exileInsteadOfGraveyard none false })
      (cause := some testCause)
  let handCardId := (gExOnly0.player me).hand.back!
  let gMoveGyReplaced : Game :=
    gExOnly0.moveToOwnerGraveyard (gExOnly0.object! handCardId) "Card is put into its owner's graveyard" (cause := some testCause)
  let topLibId := (gExOnly0.player me).library.back!
  let gSurvReplaced : Game :=
    let g := (gExOnly0.change (.pushContinuationFrame {})).change (.continuation (.surveilReturnMvAtMost (some 10)))
    g.surveilMoveLoop me #[topLibId] (some testCause)
  let big44 : CardDef := { bear with name := "Phase22 Big 4/4", power := some 4, toughness := some 4 }
  let gSacPow0 : Game :=
    let g := addPermanent (addPermanent gExOnly0 big44 me me) bear me me
    let bigId := (g.battlefield.filter (·.name == "Phase22 Big 4/4"))[0]!.id
    let srcId := (g.battlefield.filter (·.name == bear.name))[0]!.id
    let g := (g.change (.pushContinuationFrame {})).change
      (.pending (.fraChoice me (.maySacrificeAnotherCreatureForPower srcId)))
    mustApply g me (.choosePermanents #[bigId])
  let deferredAndArrivalOk : Bool :=
    !gMoveGyReplaced.log.any (fun s => s.contains "owner's graveyard") &&
    (gMoveGyReplaced.followMovedToZone? handCardId (· == .exile)).isSome &&
    !gSurvReplaced.log.any (fun s => s.contains "(surveil)") &&
    !(gSurvReplaced.player me).hand.any (fun id => id == topLibId) &&
    (gSurvReplaced.followMovedToZone? topLibId (· == .exile)).isSome &&
    gSacPow0.objects.any (fun o => o.name == "Phase22 Big 4/4" && o.zone == .exile) &&
    (gSacPow0.battlefield.filter (·.name == bear.name))[0]!.status.plusOnePlusOne == 4

  mustHold22 "4a.seqLogsOk" seqLogsOk &&
  mustHold22 "4b.deferredAndArrivalOk" deferredAndArrivalOk &&
  mustHold22 "4.replay" ([gSeq0, gSeq1, gSeq2, gMoveGyReplaced, gSurvReplaced, gSacPow0].all (fun g =>
    Game.replayEvents g.events == g && allRulesEventsClassified g))

-- 5. `finishProposedSpellCosts` `outerCont?` preservation, CR 733.1 post-prior-cost reversal
--    (`paySneak` returning the caster's only creature before `additionalCostSacrificeCreature`),
--    and `Action.decline` reversal on `.sacrificePermanent` / `.discardForAdditionalCost` only
--    when zero legal choices remain.
#guard
  -- 5a. `finishProposedSpell` (`Action.pay`) preserves `outerCont?`:
  let oneInstant22 : CardDef := {
    name := "Phase22 One Instant"
    manaCost := ManaCost.ofGeneric 1
    types := #[.instant]
    spellEffect := some { resolution := .ofSpell (.draw (.fixed 1) .you), phrase := "Draw a card" }
  }
  let zeroInstant22 : CardDef := {
    name := "Phase22 Zero Instant"
    manaCost := ManaCost.empty
    types := #[.instant]
    spellEffect := some { resolution := .ofSpell (.draw (.fixed 1) .you), phrase := "Draw a card" }
  }
  let gPropOuterCast : Game :=
    let g := (insertObject afterDraw oneInstant22 me (.hand me)).addMana me (.colored .red) 1
    let spId := (g.player me).hand.back!
    let g := mustApply g me (.cast spId)
    let g := (g.change (.pushContinuationFrame {})).change
      (.continuation (.pendingReplacement (some (.restorePending (.scry me 1) false))))
    mustApply g me .pay
  let propOuterOk : Bool :=
    gPropOuterCast.pending == .scry me 1 &&
    gPropOuterCast.stack.size == 1

  -- 5b. Sneak + `additionalCostSacrificeCreature` when the unblocked attacker is `me`'s ONLY creature:
  --     `paySneak` returns that attacker to hand, leaving 0 creatures to sacrifice, so `.finalize`
  --     reverses the entire proposed spell per CR 733.1 (attacker is back on `.battlefield`, sneak spell in `.hand`!):
  let sneakSacCreature22 : CardDef := {
    bear with
    name := "Phase22 Sneak Sac"
    manaCost := ManaCost.ofGeneric 4
    additionalCostSacrificeCreature := true
    staticAbilities := #[.sneak ManaCost.empty]
  }
  let gSneak0 : Game :=
    let g := addPermanent (insertObject afterDraw sneakSacCreature22 me (.hand me)) bear me me
    let atkId := (g.battlefield.filter (·.name == bear.name))[0]!.id
    let g := g.beginStep .declareAttackers
    let g := mustApply g me (.declareAttackers #[atkId] none #[] #[])
    g.advanceStep
  let gSneakUnblocked : Game := mustApply gSneak0 opp22 (.declareBlockers #[])
  let sneakCardId := ((gSneakUnblocked.player me).hand.filter (fun id => (gSneakUnblocked.object! id).name == "Phase22 Sneak Sac"))[0]!
  let atkBearId := (gSneakUnblocked.battlefield.filter (·.name == bear.name))[0]!.id
  let sneakReversedOrRejected : Bool :=
    match (gSneakUnblocked.apply me (.castWithSneak sneakCardId atkBearId)).bind (fun g => g.apply me .pay) with
    | .error _ => false
    | .ok gAfter =>
      gAfter.proposedSpell.isNone &&
      gAfter.battlefield.any (·.name == bear.name) &&
      (gAfter.player me).hand.any (fun id => (gAfter.object! id).name == "Phase22 Sneak Sac")
  let gSneakWithExtra : Game :=
    let g := addPermanent gSneakUnblocked hero me me
    let g := mustApply g me (.castWithSneak sneakCardId atkBearId)
    mustApply g me .pay
  let sneakExtraPromptsSacOk : Bool :=
    (match gSneakWithExtra.pending with | .sacrificePermanent q _ => q == me | _ => false) &&
    !(gSneakWithExtra.apply me .decline).isOk

  -- 5c. `.sacrificePermanent` / `.discardForAdditionalCost` allow `Action.decline` reversal when 0 choices remain:
  let gZeroSac0 : Game :=
    let g := insertObject afterDraw sneakSacCreature22 me (.hand me)
    let spId := (g.player me).hand.back!
    let orig := g.object! spId
    let g := g.change .saveProposalCheckpoint
    let (g, newSpId) := g.move spId .stack (some me) (verb := some .cast) (actor := some me)
    g.changes #[
      .proposedSpell (some { caster := me, spellId := newSpId, original := orig, cost := ManaCost.empty, needsSacrificeOther := true }),
      .pending (.sacrificePermanent me newSpId)]
  let gZeroSacRev : Game := mustApply gZeroSac0 me .decline
  let gZeroDisc0 : Game :=
    let g := emptyHand afterDraw me
    let g := insertObject g zeroInstant22 me (.hand me)
    let spId := (g.player me).hand.back!
    let orig := g.object! spId
    let g := g.change .saveProposalCheckpoint
    let (g, newSpId) := g.move spId .stack (some me) (verb := some .cast) (actor := some me)
    g.changes #[
      .proposedSpell (some { caster := me, spellId := newSpId, original := orig, cost := ManaCost.empty, needsDiscardCard := true }),
      .pending (.discardForAdditionalCost me)]
  let gZeroDiscRev : Game := mustApply gZeroDisc0 me .decline
  let zeroChoiceDeclineRevOk : Bool :=
    sneakReversedOrRejected &&
    sneakExtraPromptsSacOk &&
    gZeroSacRev.pending == .none &&
    gZeroSacRev.proposedSpell.isNone &&
    (gZeroSacRev.player me).hand.any (fun id => (gZeroSacRev.object! id).name == "Phase22 Sneak Sac") &&
    gZeroDiscRev.pending == .none &&
    gZeroDiscRev.proposedSpell.isNone &&
    (gZeroDiscRev.player me).hand.any (fun id => (gZeroDiscRev.object! id).name == "Phase22 Zero Instant")

  mustHold22 "5a.propOuterOk" propOuterOk &&
  mustHold22 "5b_c.zeroChoiceDeclineRevOk" zeroChoiceDeclineRevOk &&
  mustHold22 "5.replay" ([gPropOuterCast, gSneakUnblocked, gSneakWithExtra, gZeroSacRev, gZeroDiscRev].all (fun g =>
    Game.replayEvents g.events == g && allRulesEventsClassified g))

-- 6. CR 614.12 simultaneous `preBfOk` (`selfEntersTapped`, `entersWithHopePerCreature`,
--    `replaceCountersPutChoice` `entersWith`) when `g.currentBatch.isNone`, plus unbatched
--    `Movement.move` sharing one arrival `BatchId` with `.entersUntappedPayLife`.
#guard
  let leg22 : CardDef := { bear with name := "Phase22 CoLegend", supertypes := #[.legendary] }
  let checkLand22 : CardDef := { name := "Phase22 CheckLand", types := #[.land], entersTappedUnlessLegendary := true }
  let hopeCr22 : CardDef := { bear with name := "Phase22 HopeCr", entersWithHopePerCreature := true }
  let doc22 : CardDef := { bear with name := "Phase22 CoDoc", staticAbilities := #[.extraCounterOnPermanents] }
  let plusCr22 : CardDef := { bear with name := "Phase22 PlusCr", entersWithPlusOneCounters := 1 }

  -- 6a. Simultaneous entry via `putToBattlefieldLoop` (`g.currentBatch == none`, `preBattlefield := some preBf`):
  --     none of the co-entering permanents were on `preBf`, so `CheckLand` enters tapped, `HopeCr` gets 1 hope
  --     (counting only itself, excluding co-entering `CoLegend` and `CoDoc`), and `PlusCr` gets 1 (NOT 2!) +1/+1 counter!
  let gSim0 : Game :=
    insertObject (insertObject (insertObject (insertObject (insertObject afterDraw
      leg22 me (.hand me))
      checkLand22 me (.hand me))
      hopeCr22 me (.hand me))
      doc22 me (.hand me))
      plusCr22 me (.hand me)
  let preBf22 := gSim0.battlefield
  let handTail := (gSim0.player me).hand.extract ((gSim0.player me).hand.size - 5) (gSim0.player me).hand.size
  let gSimDone : Game :=
    gSim0.putToBattlefieldLoop me handTail #[] false false false false false .none (some testCause) (some preBf22)
  let simLand := (gSimDone.battlefield.filter (·.name == "Phase22 CheckLand"))[0]!
  let simHope := (gSimDone.battlefield.filter (·.name == "Phase22 HopeCr"))[0]!
  let simPlus := (gSimDone.battlefield.filter (·.name == "Phase22 PlusCr"))[0]!
  -- Control check: when `CoDoc` and `CoLegend` ARE already on `preBattlefield`, `CheckLand` enters untapped,
  -- `HopeCr` gets 4 hope counters (2 pre-existing creatures + 1 self + 1 from `CoDoc`), and `PlusCr` gets 2 +1/+1 counters!
  let gSeqCtrl0 : Game :=
    insertObject (insertObject (insertObject (addPermanent (addPermanent afterDraw leg22 me me) doc22 me me)
      checkLand22 me (.hand me))
      hopeCr22 me (.hand me))
      plusCr22 me (.hand me)
  let ctrlTail := (gSeqCtrl0.player me).hand.extract ((gSeqCtrl0.player me).hand.size - 3) (gSeqCtrl0.player me).hand.size
  let gSeqCtrlDone : Game :=
    gSeqCtrl0.putToBattlefieldLoop me ctrlTail #[] false false false false false .none (some testCause) (some gSeqCtrl0.battlefield)
  let ctrlLand := (gSeqCtrlDone.battlefield.filter (·.name == "Phase22 CheckLand"))[0]!
  let ctrlHope := (gSeqCtrlDone.battlefield.filter (·.name == "Phase22 HopeCr"))[0]!
  let ctrlPlus := (gSeqCtrlDone.battlefield.filter (·.name == "Phase22 PlusCr"))[0]!
  let simultaneousPreBfOk : Bool :=
    simLand.status.tapped &&
    simHope.status.hope == 1 &&
    simPlus.status.plusOnePlusOne == 1 &&
    !ctrlLand.status.tapped &&
    ctrlHope.status.hope == 4 &&
    ctrlPlus.status.plusOnePlusOne == 2

  -- 6b. Unbatched `putOntoBattlefield` of a shock land (`entersTappedUnlessPayLife := some 2`):
  --     accepting `.entersUntappedPayLife 2` records `.life (.lost ...)` and `.zone (.moved ... .battlefield)`
  --     under the SAME non-`none` arrival `BatchId`!
  let shockLand22 : CardDef := { name := "Phase22 ShockLand", types := #[.land], entersTappedUnlessPayLife := some 2 }
  let gShock0 : Game := insertObject afterDraw shockLand22 me (.hand me)
  let shockId := (gShock0.player me).hand.back!
  let preShockIdx := gShock0.events.size
  let (gShockPrompt, _) := gShock0.putOntoBattlefield shockId me (cause := some testCause)
  let payLifeRid : ReplacementId :=
    match gShockPrompt.pending with
    | .chooseReplacement _ cs => (cs.find? (fun r => r.kind == .entersUntappedPayLife 2)).getD cs[0]!
    | _ => { kind := .entersUntappedPayLife 2 }
  let gShockPaid : Game := mustApply gShockPrompt me (.chooseReplacement payLifeRid)
  let shockSlice := gShockPaid.events.extract preShockIdx gShockPaid.events.size
  let lifeBatch? := shockSlice.findSome? fun e =>
    match e.change with | .rules (.life (.lost ..)) => some e.batch | _ => none
  let enterBatch? := shockSlice.findSome? fun e =>
    match e.change with | .rules (.zone (.moved _ _ _ .battlefield ..)) => some e.batch | _ => none
  let shockBatchOk : Bool :=
    lifeBatch?.any Option.isSome &&
    lifeBatch? == enterBatch? &&
    !(gShockPaid.battlefield.filter (·.name == "Phase22 ShockLand"))[0]!.status.tapped

  mustHold22 "6a.simultaneousPreBfOk" simultaneousPreBfOk &&
  mustHold22 "6b.shockBatchOk" shockBatchOk &&
  mustHold22 "6.replay" ([gSimDone, gSeqCtrlDone, gShockPrompt, gShockPaid].all (fun g =>
    Game.replayEvents g.events == g && allRulesEventsClassified g))

-- 7. CR 614.6 / 701.47a `finishFreshAmass` choice under `tokenDoubling`, `createdTokensThisWay`
--    across multiplied token creation (`.createAlienPerInvasion`), and CR 616.1
--    `enterWithPlusOnes` preserving unrelated `replacementOrder` entries.
#guard
  let doubler22 : CardDef := { bear with name := "Phase22 Doubler", tokenDoubling := true }
  -- 7a. `finishFreshAmass` under `tokenDoubling` prompts `.chooseCards` across the 2 fresh 0/0 Armies:
  let gAmass0 : Game := (addPermanent afterDraw doubler22 me me).amassGoblins me 3
  let amassPromptIds : Array ObjectId :=
    match gAmass0.pending with
    | .fraChoice q (.chooseCards ids 1 (.amassArmy .goblin 3 none)) =>
      if q == me && ids.size == 2 then ids else #[]
    | _ => #[]
  let chosenArmyId := amassPromptIds[1]!
  let gAmass1 : Game := mustApply gAmass0 me (.choosePermanents #[chosenArmyId])
  let survivingArmies := gAmass1.battlefield.filter (·.name == "Goblin Army")
  let freshAmassChoiceOk : Bool :=
    amassPromptIds.size == 2 &&
    survivingArmies.size == 1 &&
    survivingArmies[0]!.id == chosenArmyId &&
    survivingArmies[0]!.status.plusOnePlusOne == 3

  -- 7b. `createdTokensThisWay` across multiplied token creation (`.createAlienPerInvasion`):
  --     with 2 invasion counters and `tokenDoubling`, BOTH created Alien tokens get 2 +1/+1 counters!
  let gAlien0 : Game :=
    let g := addPermanent afterDraw doubler22 me me
    let dId := (g.battlefield.filter (·.name == "Phase22 Doubler"))[0]!.id
    let g := g.recordPutCounters dId .invasion 2 (some me) (cause := some testCause)
    g.applyTriggeredAbility me (.onCombatCreateAlienPerInvasion) (some dId)
  let aliens := gAlien0.battlefield.filter (fun o => o.printed.isToken && gAlien0.hasSubtype o .alien)
  let multipliedCreatedTokensOk : Bool :=
    aliens.size == 2 &&
    aliens.all (·.status.plusOnePlusOne == 2)

  -- 7c. CR 616.1 `enterWithPlusOnes` consumes ONLY applied counter-replacement IDs from `replacementOrder`,
  --     preserving unrelated queued `ReplacementId` entries!
  let docOrd22 : CardDef := { bear with name := "Phase22 OrdDoc", staticAbilities := #[.extraCounterOnPermanents] }
  let plusOne22 : CardDef := { bear with name := "Phase22 OrdPlus", entersWithPlusOneCounters := 1 }
  let unrelatedRid : ReplacementId := { kind := .exileOppDeath, object := some ⟨970⟩ }
  let gOrdKeep0 : Game :=
    let g := insertObject (addPermanent afterDraw docOrd22 me me) plusOne22 me (.hand me)
    let docId := (g.battlefield.filter (·.name == "Phase22 OrdDoc"))[0]!.id
    let docRid : ReplacementId := { kind := .extraCounterOnPermanents, object := some docId, counterKind := some .plusOnePlusOne }
    let g := (g.change (.pushContinuationFrame {})).change (.replacementOrder #[docRid, unrelatedRid])
    let pId := (g.player me).hand.back!
    (g.putOntoBattlefield pId me (cause := some testCause)).1
  let ordPlusPerm := (gOrdKeep0.battlefield.filter (·.name == "Phase22 OrdPlus"))[0]!
  let replacementOrderPreservedOk : Bool :=
    ordPlusPerm.status.plusOnePlusOne == 2 &&
    gOrdKeep0.replacementOrder == #[unrelatedRid]

  mustHold22 "7a.freshAmassChoiceOk" freshAmassChoiceOk &&
  mustHold22 "7b.multipliedCreatedTokensOk" multipliedCreatedTokensOk &&
  mustHold22 "7c.replacementOrderPreservedOk" replacementOrderPreservedOk &&
  mustHold22 "7.replay" ([gAmass0, gAmass1, gAlien0, gOrdKeep0].all (fun g =>
    Game.replayEvents g.events == g && allRulesEventsClassified g))

end Phase22EventAlignment

section Phase23EventAlignment

def opp23 : PlayerId := ⟨1⟩

def mustHold23 (label : String) (ok : Bool) : Bool :=
  if ok then true else panic! s!"Phase 23 guard failed: {label}"

-- 1. Pause-safe continuation & library ordering: `drainPendingContinuations`
--    `triggerSequenceRest`-before-`outerPendingReplacements`, non-mana `payWard`
--    `.afterWardResolved`-before-`outerCont?`, `beginResolutionCastTargets`
--    post-`becomeCast` pause chaining, `moveIdsInOrder` `.fromTop` offsets, and
--    `.lootLandEntersTapped` graveyard-only check.
#guard
  -- 1a. `drainPendingContinuations` drains `triggerSequenceRest` BEFORE `outerPendingReplacements`:
  let dummyTrig : TriggeredAbility := .triggered .enter (Effect.gainLife 1)
  let seqRest : TriggerSequenceRest := {
    controller := me
    ability := dummyTrig
    steps := [.gainLife 3]
  }
  let gDrain0 : Game :=
    afterDraw.change (.pushContinuationFrame {
      resolvingContext := some (none, me)
      triggerSequenceRest := some seqRest
      outerPendingReplacements := #[.restorePending (.scry me 1)]
    })
  let gDrain1 : Game := gDrain0.drainPendingContinuations
  let drainOrderOk : Bool :=
    (gDrain1.player me).life == (afterDraw.player me).life + 3 &&
    gDrain1.pending == .scry me 1 &&
    gDrain1.outerPendingReplacements.isEmpty

  -- 1b. Non-mana `payWard` (`.discardCard` & `.fivePoison`) runs `afterWardResolved` BEFORE `outerCont?`:
  let gWard0 : Game :=
    let g := insertObject (insertObject afterDraw bear me (.hand me)) hero me .stack (some me)
    let spId := (g.objects.filter (fun o => o.name == hero.name && o.zone == .stack))[0]!.id
    let g := g.putStackEntry me spId
    (g.changes #[
      .pushContinuationFrame {
        resolvingContext := some (none, opp23)
        pendingReplacement := some (.restorePending (.scry me 1))
      },
      .pending (.payWard me spId .discardCard)
    ])
  let handCardId := (gWard0.player me).hand.back!
  let gWardDisc : Game := mustApply gWard0 me (.discard handCardId)
  let gWardPsn0 : Game :=
    let spId := gWard0.stack[0]!.objectId
    gWard0.change (.pending (.payWard me spId .fivePoison))
  let gWardPsn : Game := mustApply gWardPsn0 me .pay
  let wardOrderOk : Bool :=
    gWardDisc.pending == .scry me 1 &&
    gWardDisc.pendingReplacement.isNone &&
    gWardPsn.pending == .scry me 1 &&
    (gWardPsn.player me).poison == 5

  -- 1c. `beginResolutionCastTargets`: 0-mana untargeted exiled creature cast via `.mayCastExiledElseDamage`
  --     chains outer continuation after `becomeCast` without losing the outer continuation!
  let gResCast0 : Game :=
    let g := insertObject afterDraw { bear with manaCost := ManaCost.empty } me .exile
    let exId := (g.objects.filter (fun o => o.name == bear.name && o.zone == .exile))[0]!.id
    g.changes #[
      .pushContinuationFrame {
        resolvingContext := some (none, me)
        pendingReplacement := some (.restorePending (.scry me 1))
      },
      .pending (.mayCastExiledElseDamage me exId 2 none)
    ]
  let exCastId := (gResCast0.objects.filter (fun o => o.name == bear.name && o.zone == .exile))[0]!.id
  let gResCast1 : Game := mustApply gResCast0 me (.cast exCastId)
  let resCastChainOk : Bool :=
    gResCast1.stack.size == 1 &&
    gResCast1.pending == .scry me 1

  -- 1d. `moveIdsInOrder` / `moveIdsInOrderLoop` `.fromTop` offsets preserve bottom-group ordering across pauses:
  let cTop : CardDef := { bear with name := "Phase23 Top" }
  let cBot : CardDef := { bear with name := "Phase23 Bot" }
  let cIns1 : CardDef := { bear with name := "Phase23 Ins1" }
  let cIns2 : CardDef := { bear with name := "Phase23 Ins2" }
  let gLib0 : Game :=
    insertObject (insertObject (insertObject (insertObject afterDraw cBot me (.library me)) cTop me (.library me)) cIns1 me (.graveyard me)) cIns2 me (.graveyard me)
  let ins1Id := (gLib0.objects.filter (·.name == "Phase23 Ins1"))[0]!.id
  let ins2Id := (gLib0.objects.filter (·.name == "Phase23 Ins2"))[0]!.id
  let gLibSync : Game := gLib0.moveIdsInOrder #[ins1Id, ins2Id] (.library me) (cause := some testCause)
  let libNames := (gLibSync.player me).library.map (fun id => (gLibSync.object! id).name)
  -- Bottom of library is `[0]!`: `Ins1` is `[0]!`, `Ins2` is `[1]!` (`fromTop (libSize - 1)`).
  let libHead := libNames.extract 0 2
  -- Resumed `moveIdsInOrderLoop` when `ins1Id` entered `.library me` vs when `ins1Id` was exiled instead:
  let gLibResumed : Game :=
    let (g1, _) := gLib0.move ins1Id (.library me) none (libraryPosition := some .bottom) (cause := some testCause)
    g1.moveIdsInOrderLoop #[ins2Id] (.library me) "" (some testCause) 0 (some (ins1Id, me))
  let resumedHead := ((gLibResumed.player me).library.map (fun id => (gLibResumed.object! id).name)).extract 0 2
  let gLibRedirected : Game :=
    let (g1, _) := gLib0.move ins1Id .exile none (cause := some testCause)
    g1.moveIdsInOrderLoop #[ins2Id] (.library me) "" (some testCause) 0 (some (ins1Id, me))
  let redirectedBottom := (gLibRedirected.object! (gLibRedirected.player me).library[0]!).name
  let fromTopOffsetOk : Bool :=
    libHead == #["Phase23 Ins1", "Phase23 Ins2"] &&
    resumedHead == #["Phase23 Ins1", "Phase23 Ins2"] &&
    redirectedBottom == "Phase23 Ins2"

  -- 1e. `.lootLandEntersTapped`: exiled discard (`.exileInsteadOfGraveyard`) does NOT put the land onto `.battlefield`!
  let lootLandDef : CardDef := { forest with name := "Phase23 Loot Forest" }
  let gLoot0 : Game :=
    let g := afterDraw
    let g := (g.player me).hand.foldl (fun acc hid => (acc.move hid .exile none (cause := some testCause)).1) g
    let g := insertObject (insertObject g bear me (.library me)) lootLandDef me (.library me)
    g.createEffect (.replacement {
      id := { kind := .exileOppDeath }
      source := none, controller := some opp23, affectedPlayer := me
      kind := .exileInsteadOfGraveyard none }) (cause := some testCause)
  let gLoot1 : Game := gLoot0.applyTriggeredAbility me (.triggered .enter (Effect.ofTrigger .lootLandEntersTapped)) none
  let lootHandLand := ((gLoot1.player me).hand.filter (fun id => (gLoot1.object! id).name == "Phase23 Loot Forest"))[0]!
  let gLoot2 : Game := mustApply gLoot1 me (.discard lootHandLand)
  let lootGyOnlyOk : Bool :=
    !(gLoot2.battlefield.any (·.name == "Phase23 Loot Forest")) &&
    gLoot2.objects.any (fun o => o.name == "Phase23 Loot Forest" && o.zone == .exile)

  mustHold23 "1a.drainOrderOk" drainOrderOk &&
  mustHold23 "1b.wardOrderOk" wardOrderOk &&
  mustHold23 "1c.resCastChainOk" resCastChainOk &&
  mustHold23 "1d.fromTopOffsetOk" fromTopOffsetOk &&
  mustHold23 "1e.lootGyOnlyOk" lootGyOnlyOk &&
  mustHold23 "1.replay" ([gDrain1, gWardDisc, gWardPsn, gResCast1, gLibSync, gLibResumed, gLibRedirected, gLoot2].all (fun g =>
    Game.replayEvents g.events == g && allRulesEventsClassified g))

-- 2. Sequential multi-target CR 608.2b legality across replacement pauses & CR 615.6 deferred damage logs.
#guard
  -- 2a. Multi-target `countersOnCreatureTargetsLoop` pauses on target 0's replacement choice BEFORE putting counters on target 1:
  let gSeqTgt0 : Game :=
    let g := addPermanent (addPermanent afterDraw bear me me) hero me me
    let bId := (g.battlefield.filter (·.name == bear.name))[0]!.id
    let rAdd : ReplacementId := { kind := .addCountersPut, object := some ⟨981⟩ }
    let rMul : ReplacementId := { kind := .multiplyCountersPut, object := some ⟨982⟩ }
    let g := g.createEffect (.replacement {
      id := rAdd, source := none, controller := some me, affectedPlayer := me
      kind := .modifyCountersPut (some bId) (some .plusOnePlusOne) (add := 1) (mult := 1) }) (cause := some testCause)
    g.createEffect (.replacement {
      id := rMul, source := none, controller := some me, affectedPlayer := me
      kind := .modifyCountersPut (some bId) (some .plusOnePlusOne) (add := 0) (mult := 2) }) (cause := some testCause)
  let t0Id := (gSeqTgt0.battlefield.filter (·.name == bear.name))[0]!.id
  let t1Id := (gSeqTgt0.battlefield.filter (·.name == hero.name))[0]!.id
  let rAdd23 : ReplacementId := { kind := .addCountersPut, object := some ⟨981⟩ }
  let gSeqPaused : Game :=
    gSeqTgt0.withBatch (some testCause) fun g =>
      g.countersOnCreatureTargetsLoop me #[.permanent t0Id, .permanent t1Id] .plusOnePlusOne 1 none
  let pausedBeforeSecond : Bool :=
    (match gSeqPaused.pending with | .chooseReplacement p _ => p == me | _ => false) &&
    (gSeqPaused.object! t1Id).status.plusOnePlusOne == 0
  let gSeqDone : Game := mustApply gSeqPaused me (.chooseReplacement rAdd23)
  let seqTargetsOk : Bool :=
    pausedBeforeSecond &&
    gSeqDone.pending == .none &&
    (gSeqDone.object! t0Id).status.plusOnePlusOne == 4 &&
    (gSeqDone.object! t1Id).status.plusOnePlusOne == 1

  -- 2b. CR 615.6 prevented damage (`dealt == 0`) suppresses damage logs in `dealDamageLoseIndestructibleExileTo`
  --     and `causeDealsDamageToOpponentsLoop`!
  let gPrev0 : Game :=
    let g := addPermanent afterDraw bear opp23 opp23
    let oppBearId := (g.battlefield.filter (·.name == bear.name))[0]!.id
    let prevSpec : PreventionSpec := {
      id := { kind := .preventAllDamageToPermanent, object := some oppBearId }
      source := some oppBearId, controller := some opp23, affectedPlayer := opp23
      kind := .preventAllDamageToPermanent oppBearId }
    (g.createEffect (.prevention prevSpec) (cause := some testCause)).createEffect
      (.protectionFromEverything opp23) (cause := some testCause)
  let oppBearId23 := (gPrev0.battlefield.filter (·.name == bear.name))[0]!.id
  let prePermLog := gPrev0.log.size
  let gSmitePrev : Game :=
    gPrev0.dealDamageLoseIndestructibleExileTo (gPrev0.object! oppBearId23) 2
      (gPrev0.snapshot (gPrev0.object! oppBearId23))
  let preOppLog := gPrev0.log.size
  let gOppDmgPrev : Game := gPrev0.causeDealsDamageToOpponentsLoop #[opp23] 2 "Phase23 Source" none (some testCause)
  let smiteLogs := gSmitePrev.log.extract prePermLog gSmitePrev.log.size
  let oppDmgLogs := gOppDmgPrev.log.extract preOppLog gOppDmgPrev.log.size
  let preventedNoSideEffectOk : Bool :=
    smiteLogs.any (·.contains "loses indestructible") &&
    !(smiteLogs.any (·.contains "is dealt")) &&
    !(oppDmgLogs.any (·.contains "Phase23 Source deals"))

  -- 2c. CR 614.6 arrival gating on Clash of Elements (`.topOrBottomDamage` / `.topOrBottomDamageFollowup`)
  --     and `FrcResolve` `handDiscard` / `.logHandDiscard` when replaced to `.exile`:
  let gTopExiled : Game :=
    let g := addPermanent afterDraw bear opp23 opp23
    let bid := (g.battlefield.filter (·.name == bear.name))[0]!.id
    let (g, _) := g.move bid .exile none (cause := some testCause)
    g.runPostStep (.topOrBottomDamageFollowup bid opp23 bear.name true 2 none)
  let clashShockDef23 : CardDef := {
    forest with
    name := "Phase23 Clash Linked Shock"
    entersTappedUnlessPayLife := some 2
  }
  let gTopPaused0 : Game :=
    let g := addPermanent (insertObject afterDraw clashShockDef23 me .exile) bear opp23 opp23
    let bid := (g.battlefield.filter (·.name == bear.name))[0]!.id
    let exId := (g.objects.filter (fun o => o.name == "Phase23 Clash Linked Shock" && o.zone == .exile))[0]!.id
    let g := (g.change (.object bid (.pushLinkedExile exId))).change (.pushContinuationFrame {})
    let g := g.change (.pending (.fraChoice opp23 (.topOrBottomDamage bid 2 none)))
    mustApply g opp23 .chooseTop
  let gTopPausedDone : Game :=
    match gTopPaused0.pending with
    | .chooseReplacement p cs => mustApply gTopPaused0 p (.chooseReplacement cs[0]!)
    | _ => gTopPaused0
  let idHdExA : ReplacementId := { kind := .exileOppDeath, object := some ⟨988⟩ }
  let idHdExB : ReplacementId := { kind := .exileOppDeath, object := some ⟨989⟩ }
  let gHdSync0 : Game :=
    afterDraw.createEffect
      (.replacement { id := idHdExA, affectedPlayer := me, kind := .exileInsteadOfGraveyard none false })
      (cause := some testCause)
  let preHdSyncLog := gHdSync0.log.size
  let hdSyncCard := (gHdSync0.player me).hand.back!
  let gHdSync1 : Game := gHdSync0.runFrcPostStep (.discardHand me)
  let gHdPause0 : Game :=
    gHdSync0.createEffect
      (.replacement { id := idHdExB, affectedPlayer := me, kind := .exileInsteadOfGraveyard none false })
      (cause := some testCause)
  let preHdPauseLog := gHdPause0.log.size
  let hdPauseCard := (gHdPause0.player me).hand.back!
  let gHdPause1 : Game := gHdPause0.runFrcPostStep (.discardHand me)
  let gHdPause2 : Game := mustApply gHdPause1 me (.chooseReplacement idHdExA)
  let preHdNormLog := afterDraw.log.size
  let gHdNorm : Game := afterDraw.runFrcPostStep (.discardHand me)
  let clashAndHandDiscardArrivalOk : Bool :=
    (gTopExiled.player opp23).life == 20 &&
    !gTopExiled.log.any (·.contains "on top of their library") &&
    (gTopPaused0.player opp23).life == 20 &&
    (gTopPausedDone.player opp23).life == 18 &&
    gTopPausedDone.log.any (·.contains "on top of their library") &&
    (gHdSync1.followMovedToZone? hdSyncCard (· == .exile)).isSome &&
    !(gHdSync1.log.extract preHdSyncLog gHdSync1.log.size).any (·.contains "discards ") &&
    (match gHdPause1.pending with | .chooseReplacement p cs => p == me && cs.size == 2 | _ => false) &&
    (gHdPause2.followMovedToZone? hdPauseCard (· == .exile)).isSome &&
    !(gHdPause2.log.extract preHdPauseLog gHdPause2.log.size).any (·.contains "discards ") &&
    (gHdNorm.log.extract preHdNormLog gHdNorm.log.size).any (·.contains "discards ")

  mustHold23 "2a.seqTargetsOk" seqTargetsOk &&
  mustHold23 "2b.preventedNoSideEffectOk" preventedNoSideEffectOk &&
  mustHold23 "2c.clashAndHandDiscardArrivalOk" clashAndHandDiscardArrivalOk &&
  mustHold23 "2.replay" ([gSeqPaused, gSeqDone, gSmitePrev, gOppDmgPrev,
      gTopExiled, gTopPaused0, gTopPausedDone, gHdSync1, gHdPause1, gHdPause2, gHdNorm].all (fun g =>
    Game.replayEvents g.events == g && allRulesEventsClassified g))

-- 3. 0-mana `sneakAttacker` bounce, reduced-`{0}` `activateAbility` `CastEvent.announced`,
--    spell-sacrifice `CastEvent.announced`, CR 106.6 `fromTreasure` & `.cantNonartifact`, and
--    `payWard` / `payOrLetCounter` `manaSpentOn` provenance.
#guard
  -- 3a. 0-mana `sneakAttacker` returns the unblocked attacker to hand and records `costs := #[.sneak atkId ...]`:
  let zeroSneakDef : CardDef := {
    bear with
    name := "Phase23 Zero Sneak"
    staticAbilities := #[.sneak ManaCost.empty]
  }
  let gSnk0 : Game :=
    let g := insertObject (addPermanent afterDraw { bear with keywords := Keyword.haste } me me) zeroSneakDef me (.hand me)
    let atkId := (g.battlefield.filter (·.name == bear.name))[0]!.id
    let g := mustApply (mustApply (g.beginStep .beginningOfCombat) me .pass) opp23 .pass
    let g := mustApply g me (.declareAttackers #[atkId] none #[] #[])
    let g := mustApply (mustApply g me .pass) opp23 .pass
    mustApply g opp23 (.declareBlockers #[])
  let snkAtkId := (gSnk0.battlefield.filter (·.name == bear.name))[0]!.id
  let snkCardId := (gSnk0.objects.filter (fun o => o.name == "Phase23 Zero Sneak" && o.zone == .hand me))[0]!.id
  let preSnkIdx := gSnk0.events.size
  let gSnk1 : Game := mustApply (mustApply gSnk0 me (.castWithSneak snkCardId snkAtkId)) me .pay
  let zeroSneakOk : Bool :=
    (gSnk1.player me).hand.any (fun id => (gSnk1.object! id).name == bear.name) &&
    !(gSnk1.battlefield.any (·.id == snkAtkId)) &&
    (gSnk1.events.extract preSnkIdx gSnk1.events.size).any (fun e =>
      match e.change with
      | .rules (.cast (.announced _ _ _ costs)) =>
        costs == #[.sneak snkAtkId (some (.player opp23))]
      | _ => false)

  -- 3b. Activated ability reduced from `{1}` to `{0}` (with no tap cost) finishes immediately and records `CastEvent.announced`!
  let oneManaArt23 : CardDef := {
    name := "Phase23 Zeroed Activator"
    types := #[.artifact]
    subtypes := #["Equipment"]
    activatedAbilities := #[{
      cost := { mana := ManaCost.ofGeneric 1 }
      costReductionPerEquipment := 1
      effect := Effect.draw 1
    }]
  }
  let gRedAb0 : Game := addPermanent afterDraw oneManaArt23 me me
  let actArtId := (gRedAb0.battlefield.filter (·.name == "Phase23 Zeroed Activator"))[0]!.id
  let preRedAbIdx := gRedAb0.events.size
  let gRedAb1 : Game := mustApply gRedAb0 me (.activate actArtId 0)
  let reducedActivateAnnouncedOk : Bool :=
    gRedAb1.pending == .none &&
    gRedAb1.stack.size == 1 &&
    (gRedAb1.events.extract preRedAbIdx gRedAb1.events.size).any (fun e =>
      match e.change with | .rules (.cast (.abilityActivated ..)) => true | _ => false)

  -- 3c. Spell with `additionalCostSacrificeCreature` records `CastEvent.announced` `costs := #[.sacrifice sacId]`!
  let sacSpellDef23 : CardDef := {
    name := "Phase23 Sac Sorcery"
    manaCost := ManaCost.empty
    types := #[.sorcery]
    additionalCostSacrificeCreature := true
    spellEffect := some (Effect.draw 1)
  }
  let gSacSp0 : Game := insertObject (addPermanent afterDraw bear me me) sacSpellDef23 me (.hand me)
  let sacVictimId := (gSacSp0.battlefield.filter (·.name == bear.name))[0]!.id
  let sacSpCardId := (gSacSp0.player me).hand.back!
  let preSacSpIdx := gSacSp0.events.size
  let gSacSp1 : Game :=
    mustApply (mustApply (mustApply gSacSp0 me (.cast sacSpCardId)) me .pay) me (.sacrifice sacVictimId)
  let sacSpellAnnouncedOk : Bool :=
    (gSacSp1.events.extract preSacSpIdx gSacSp1.events.size).any (fun e =>
      match e.change with
      | .rules (.cast (.announced _ _ _ costs)) => costs == #[.sacrifice sacVictimId]
      | _ => false)

  -- 3d. CR 106.6 `.fromTreasure` does NOT preempt `.elf`, `.cantNonartifact` pays Ward/counter but NOT non-artifact spell,
  --     and `payWard` / `payOrLetCounter` do NOT credit `manaSpentOn` to the targeted `spellId`!
  let poolTreasureAndElf : ManaPool :=
    (({} : ManaPool).addUnits #[
      { mana := .colored .red, restriction := some (.fra .fromTreasure) },
      { mana := .colored .green, restriction := some .elf }
    ])
  let afterElfGeneric := poolTreasureAndElf.pay? (ManaCost.ofGeneric 1) (allowElfRestricted := true)
  let poolCantNonart : ManaPool :=
    ({} : ManaPool).addUnits #[{ mana := .colored .blue, restriction := some .cantNonartifact }]
  let manaPriorityAndRestrOk : Bool :=
    afterElfGeneric.any (fun p => p.units.size == 1 && p.units[0]!.restriction == some (.fra .fromTreasure)) &&
    !poolCantNonart.canPay (ManaCost.ofGeneric 1) &&
    poolCantNonart.canPay (ManaCost.ofGeneric 1) (allowCantNonartifact := true)

  let gWardMana0 : Game :=
    let g := insertObject afterDraw bear me .stack (some me)
    let targetSpId := (g.objects.filter (fun o => o.name == bear.name && o.zone == .stack))[0]!.id
    let wardPermG := addPermanent (g.putStackEntry me targetSpId) hero opp23 opp23
    let wardPermId := (wardPermG.battlefield.filter (·.name == hero.name))[0]!.id
    let wardPermG := wardPermG.addManaUnits me #[{ mana := .colored .blue, restriction := some .cantNonartifact }]
      (cause := testCause)
    wardPermG.changes #[
      .pushContinuationFrame { resolvingContext := some (some wardPermId, opp23) },
      .pending (.payWard me targetSpId (.genericMana 1))
    ]
  let targetSpId23 := gWardMana0.stack[0]!.objectId
  let gWardMana1 : Game := mustApply gWardMana0 me .payGeneric
  let wardManaProvenanceOk : Bool :=
    manaPriorityAndRestrOk &&
    GameEvent.manaSpentOn gWardMana1.events targetSpId23 == 0

  mustHold23 "3a.zeroSneakOk" zeroSneakOk &&
  mustHold23 "3b.reducedActivateAnnouncedOk" reducedActivateAnnouncedOk &&
  mustHold23 "3c.sacSpellAnnouncedOk" sacSpellAnnouncedOk &&
  mustHold23 "3d.wardManaProvenanceOk" wardManaProvenanceOk &&
  mustHold23 "3.replay" ([gSnk1, gRedAb1, gSacSp1, gWardMana1].all (fun g =>
    Game.replayEvents g.events == g && allRulesEventsClassified g))

-- 4. `equipWorthy` / `equipSubtype` per-ability target fidelity, face-down Morph casting &
--    special-action Layer-6 ability indexing, face-up stack-copy `copiable`, and self-dies triggers.
#guard
  -- 4a. Equipment with both `equipWorthyAbility` (idx 0) and `equipAbility` (idx 1):
  --     idx 1 equips non-worthy Bear; idx 0 targets worthy Hero, and fizzles at CR 608.2b if Hero becomes Villain!
  let dualEquipDef : CardDef := {
    name := "Phase23 Hammer"
    types := #[.artifact]
    subtypes := #["Equipment"]
    activatedAbilities := #[
      equipWorthyAbility ManaCost.empty,
      equipAbility ManaCost.empty
    ]
  }
  let worthyHeroDef : CardDef := {
    hero with
    name := "Phase23 Worthy Hero"
    manaCost := ManaCost.ofColor .white
    supertypes := #[.legendary]
  }
  let gEq0 : Game := addPermanent (addPermanent (addPermanent afterDraw dualEquipDef me me) bear me me) worthyHeroDef me me
  let hammerId := (gEq0.battlefield.filter (·.name == "Phase23 Hammer"))[0]!.id
  let eqBearId := (gEq0.battlefield.filter (·.name == bear.name))[0]!.id
  let eqWorthyId := (gEq0.battlefield.filter (·.name == "Phase23 Worthy Hero"))[0]!.id
  let worthyRejectsBear : Bool := !(mustApply gEq0 me (.activate hammerId 0) |>.apply me (.target (.permanent eqBearId))).isOk
  let gPlainEq : Game := (mustApply (mustApply gEq0 me (.activate hammerId 1)) me (.target (.permanent eqBearId))).resolveTop
  let gWorthyStack : Game := mustApply (mustApply gEq0 me (.activate hammerId 0)) me (.target (.permanent eqWorthyId))
  -- Make `eqWorthyId` Villain in Layer 4 before `equipWorthy` resolves -> no longer worthy -> fizzles!
  let gWorthyVillain : Game :=
    (gWorthyStack.createEffect (.layered (.objects #[eqWorthyId]) (.types .add #[] #[.villain] #[]) .untilEndOfTurn)
      (cause := some testCause)).resolveTop
  let equipFidelityOk : Bool :=
    worthyRejectsBear &&
    (gPlainEq.object! hammerId).attachedTo == some eqBearId &&
    (gWorthyVillain.object! hammerId).attachedTo.isNone

  -- 4b. Face-down Morph casting when front face is a targetless Sorcery, plus Layer-6 ability + CR 702.61b turn-face-up on face-down permanent!
  let morphSorcDef : CardDef := {
    name := "Phase23 Morph Sorcery"
    manaCost := ManaCost.ofColor .blue
    types := #[.sorcery]
    morph := some ManaCost.empty
    spellEffect := some (Effect.canonicalDestroy .creature) -- no creatures in play!
  }
  let elfLooterDef : CardDef := {
    bear with
    name := "Phase23 Gy Elf"
    subtypes := #["Elf"]
    activatedAbilities := #[{ cost := {}, effect := Effect.draw 1 }]
  }
  let splitEnablerDef : CardDef := {
    bear with
    name := "Phase23 Split Enabler"
    staticAbilities := #[.instantSorcerySplitSecond]
  }
  let gMphCast0 : Game := (insertObject afterDraw morphSorcDef me (.hand me)).addMana me .colorless 3
  let mphSorcId := (gMphCast0.player me).hand.back!
  let gMphProposed : Game := mustApply gMphCast0 me (.cast mphSorcId)
  let frontFaceRejected : Bool := !(gMphProposed.apply me (.announceKicker false)).isOk
  let gMphOnBf : Game := (mustApply (mustApply gMphProposed me (.announceKicker true)) me .pay).resolveTop
  let fdPermId := (gMphOnBf.battlefield.filter (·.status.faceDown))[0]!.id
  -- Grant `.copyActivatedFromGySubtype .elf` in Layer 6 with `elfLooterDef` in graveyard -> `[morphAb, drawAb]`!
  let gFdLayer6 : Game :=
    let g := insertObject gMphOnBf elfLooterDef me (.graveyard me)
    g.createEffect (.layered (.objects #[fdPermId])
      (.abilities { staticAbilities := #[.copyActivatedFromGySubtype .elf] } .none) .untilEndOfTurn)
      (cause := some testCause)
  let fdAbs := gFdLayer6.activatedAbilitiesOf (gFdLayer6.object! fdPermId)
  -- Activate index 1 (Layer-6 granted `draw 1`) while face down -> goes on stack!
  let gFdAct1 : Game := mustApply gFdLayer6 me (.activate fdPermId 1)
  -- Put a split-second instant on the stack: index 0 (`turnFaceUp` special action) is STILL legal (CR 702.61b)!
  let gFdSplit : Game :=
    let g := addPermanent (insertObject gFdLayer6 shock me .stack (some me)) splitEnablerDef me me
    let spId := (g.objects.filter (fun o => o.name == shock.name && o.zone == .stack))[0]!.id
    g.putStackEntry me spId
  let morphSpecialAllowedUnderSplit : Bool :=
    gFdSplit.splitSecondOnStack &&
    gFdSplit.canActivate me (gFdSplit.object! fdPermId) fdAbs[0]! &&
    !gFdSplit.canActivate me (gFdSplit.object! fdPermId) fdAbs[1]!
  let morphAndLayer6Ok : Bool :=
    frontFaceRejected &&
    fdAbs.size == 2 &&
    gFdAct1.stack.size == 1 &&
    (gFdAct1.object! fdPermId).status.faceDown &&
    morphSpecialAllowedUnderSplit

  -- 4c. Face-up `copyStackSpell` preserves `printed`, and non-`"another"` `.creatureYouControlDies` self-triggers!
  let gCopyFace0 : Game :=
    let g := insertObject afterDraw shock me .stack (some me)
    let sid := (g.objects.filter (fun o => o.name == shock.name && o.zone == .stack))[0]!.id
    (g.putStackEntry me sid).setStackEntryTargets sid #[.player opp23]
  let origShockId := gCopyFace0.stack[0]!.objectId
  let gCopyFace1 : Game := gCopyFace0.copyStackSpell (gCopyFace0.object! origShockId) me
  let copyShockObj := gCopyFace1.object! gCopyFace1.stack.back!.objectId
  let selfDiesDef : CardDef := {
    bear with
    name := "Phase23 Self Dies"
    triggeredAbilities := #[
      .triggered .creatureYouControlDies { resolution := .gainLife (.fixed 2), phrase := "You gain 2 life." } {}
    ]
  }
  let gSelfDies0 : Game := addPermanent afterDraw selfDiesDef me me
  let sdId := (gSelfDies0.battlefield.filter (·.name == "Phase23 Self Dies"))[0]!.id
  let gSelfDies1 : Game := gSelfDies0.destroyPermanent (gSelfDies0.object! sdId)
  let copyAndSelfDiesOk : Bool :=
    copyShockObj.printed.name == shock.name &&
    gSelfDies1.waitingTriggers.size == 1 &&
    gSelfDies1.waitingTriggers[0]!.source.id == sdId

  mustHold23 "4a.equipFidelityOk" equipFidelityOk &&
  mustHold23 "4b.morphAndLayer6Ok" morphAndLayer6Ok &&
  mustHold23 "4c.copyAndSelfDiesOk" copyAndSelfDiesOk &&
  mustHold23 "4.replay" ([gPlainEq, gWorthyVillain, gMphOnBf, gFdAct1, gCopyFace1, gSelfDies1].all (fun g =>
    Game.replayEvents g.events == g && allRulesEventsClassified g))

-- 5. Shockland `n ≤ life < 2 * n` CR 616.1 re-entry, CR 616.1c->616.1e Clone copying `entersTapped`,
--    unified CR 616.1g ETB counter evaluation, CR 614.12 simultaneous lord isolation, and
--    single-prompt batched `replaceTokenCreationChoice`.
#guard
  -- 5a. Shockland (`entersTappedUnlessPayLife := some 2`) at `life == 3` (`2 ≤ life < 4`) alongside competing ETB effect:
  --     paying 2 life drops `life` to 1, and CR 616.1 loop re-entry does NOT re-offer `entersTappedSelf`!
  let shockLand23 : CardDef := { forest with name := "Phase23 Shock", entersTappedUnlessPayLife := some 2 }
  let gShk0 : Game :=
    let g := insertObject (afterDraw.loseLife me 17 (cause := some testCause)) shockLand23 me (.hand me)
    g.createEffect (.replacement {
      id := { kind := .entersWithExtraCounters }
      source := none, controller := some me, affectedPlayer := me
      kind := .entersWithExtraCounters none .charge 1 }) (cause := some testCause)
  let shkHandId := (gShk0.player me).hand.back!
  let gShk1 : Game := mustApply gShk0 me (.playLand shkHandId)
  let gShk2 : Game :=
    match gShk1.pending with
    | .chooseReplacement _ cs =>
      match cs.find? (fun r => r.kind == .entersUntappedPayLife 2) with
      | some payRid => mustApply gShk1 me (.chooseReplacement payRid)
      | none => gShk1
    | _ => gShk1
  let shkPerm := (gShk2.battlefield.filter (·.name == "Phase23 Shock"))[0]!
  let shockReentryOk : Bool :=
    (gShk2.player me).life == 1 &&
    !shkPerm.status.tapped &&
    shkPerm.status.counterCount .charge == 1

  -- 5b. CR 616.1c -> 616.1e: untapped card entering as a copy of a tapped-entering creature enters TAPPED!
  let tappedTargetDef : CardDef := { bear with name := "Phase23 Tapped Template", entersTapped := true }
  let untappedCloneCard : CardDef := { hero with name := "Phase23 Untapped Clone", entersTapped := false }
  let gCln0 : Game :=
    let g := insertObject afterDraw untappedCloneCard me (.hand me)
    let cid := (g.player me).hand.back!
    let g := g.createEffect (.replacement {
      id := { kind := .entersAsCopy }, source := none, controller := some me, affectedPlayer := me
      kind := .entersAsCopy none tappedTargetDef }) (cause := some testCause)
    (g.putOntoBattlefield cid me (cause := some testCause)).1
  let clnPerm := (gCln0.battlefield.filter (·.name == "Phase23 Tapped Template"))[0]!
  let cloneTappedTierOk : Bool := clnPerm.status.tapped

  -- 5c. Unified CR 616.1g ETB counter evaluation (`1` printed + `1` extra under `+1` `modifyCountersPut` => `3`, NOT `4`)
  --     AND CR 614.12 simultaneous batch isolation (`Doc Samson` co-entering with `1`-counter creature => `1`, NOT `2`)!
  let oneCounterBear : CardDef := { bear with name := "Phase23 Counter Bear", entersWithPlusOneCounters := 1 }
  let gUnif0 : Game :=
    let g := insertObject afterDraw oneCounterBear me (.hand me)
    let cid := (g.player me).hand.back!
    let g := g.createEffect (.replacement {
      id := { kind := .entersWithExtraCounters }, source := none, controller := some me, affectedPlayer := me
      kind := .entersWithExtraCounters none .plusOnePlusOne 1 }) (cause := some testCause)
    let g := g.createEffect (.replacement {
      id := { kind := .addCountersPut }, source := none, controller := some me, affectedPlayer := me
      kind := .modifyCountersPut none (some .plusOnePlusOne) (add := 1) (mult := 1) }) (cause := some testCause)
    (g.putOntoBattlefield cid me (cause := some testCause)).1
  let unifCounters := (gUnif0.battlefield.filter (·.name == "Phase23 Counter Bear"))[0]!.status.plusOnePlusOne
  let docLord23 : CardDef := { bear with name := "Phase23 CoEntering Doc", staticAbilities := #[.extraCounterOnPermanents] }
  let gSimEtb0 : Game :=
    let g := insertObject (insertObject afterDraw docLord23 me (.hand me)) oneCounterBear me (.hand me)
    let h := (g.player me).hand
    let docH := h[h.size - 2]!
    let bearH := h[h.size - 1]!
    g.withBatch (some testCause) fun g =>
      let (g, _) := g.putOntoBattlefield docH me (cause := some testCause)
      (g.putOntoBattlefield bearH me (cause := some testCause)).1
  let simBearCounters := (gSimEtb0.battlefield.filter (·.name == "Phase23 Counter Bear"))[0]!.status.plusOnePlusOne
  let etbCountersAndIsoOk : Bool :=
    unifCounters == 3 &&
    simBearCounters == 1

  -- 5d. Batched multi-token `createKindTokens me .food 2` with two non-commuting token replacements prompts ONCE!
  let rBecomeDragon : ReplacementId := { kind := .artifactTokensBecomeDragons, object := some ⟨991⟩ }
  let rExtraFood : ReplacementId := { kind := .foodAlsoCreatesTreasure, object := some ⟨992⟩ }
  let gTok0 : Game :=
    let g := afterDraw.createEffect (.replacement {
      id := rBecomeDragon, source := none, controller := some me, affectedPlayer := me
      kind := .artifactTokensBecome me Game.dragon55flyingToken }) (cause := some testCause)
    g.createEffect (.replacement {
      id := rExtraFood, source := none, controller := some me, affectedPlayer := me
      kind := .createExtraTokenWithFood me treasureToken }) (cause := some testCause)
  let gTokPaused : Game := gTok0.createKindTokens me .food 2 (cause := some testCause)
  let gTokDone : Game := mustApply gTokPaused me (.chooseReplacement rExtraFood)
  let gTokDoneAlt : Game := mustApply gTokPaused me (.chooseReplacement rBecomeDragon)
  let batchedMultiTokenOk : Bool :=
    (match gTokPaused.pending with | .chooseReplacement p cs => p == me && cs.size == 2 | _ => false) &&
    gTokDone.pending == .none &&
    (gTokDone.battlefield.filter (·.name == "Dragon")).size == 4 &&
    gTokDoneAlt.pending == .none &&
    (gTokDoneAlt.battlefield.filter (·.name == "Dragon")).size == 2

  mustHold23 "5a.shockReentryOk" shockReentryOk &&
  mustHold23 "5b.cloneTappedTierOk" cloneTappedTierOk &&
  mustHold23 "5c.etbCountersAndIsoOk" etbCountersAndIsoOk &&
  mustHold23 "5d.batchedMultiTokenOk" batchedMultiTokenOk &&
  mustHold23 "5.replay" ([gShk2, gCln0, gUnif0, gSimEtb0, gTokPaused, gTokDone, gTokDoneAlt].all (fun g =>
    Game.replayEvents g.events == g && allRulesEventsClassified g))

-- 6. CR 702.26g–h nested & direct+indirect phasing, batched Saga lore counters, CR 121.2c APNAP
--    `twoPlayersEachDraw`, CR 810 2HG shared life / first-turn draw skip / shared poison,
--    simultaneous CR 704.3 SBA before `pl.lost`, and `EventObject.blockingIds` LKI reconstruction.
#guard
  -- 6a. CR 702.26g–h: direct+indirect collapse (`#[host, eq]` -> `eq.status.phasedWith == some host`) & nested chain!
  let eqA23 : CardDef := { name := "Phase23 EqA", types := #[.artifact], subtypes := #["Equipment"] }
  let auraOnArt23 : CardDef := aura "Phase23 ArtAura" ManaCost.empty "Enchant artifact or non-Aura enchantment"
  let gPh0 : Game := addPermanent (addPermanent (addPermanent afterDraw bear me me) eqA23 me me) auraOnArt23 me me
  let phHost := (gPh0.battlefield.filter (·.name == bear.name))[0]!.id
  let phEq := (gPh0.battlefield.filter (·.name == "Phase23 EqA"))[0]!.id
  let phAura := (gPh0.battlefield.filter (·.name == "Phase23 ArtAura"))[0]!.id
  let gPh1 : Game := (gPh0.attachSourceTo (gPh0.object! phEq) (gPh0.object! phHost)).attachSourceTo
    (gPh0.object! phAura) (gPh0.object! phEq)
  let gPhOut : Game := gPh1.phaseOutPermanents #[gPh1.object! phHost, gPh1.object! phEq] (cause := some testCause)
  let gPhIn : Game := gPhOut.phaseInControlled me
  let phasingNestedAndCollapseOk : Bool :=
    (gPhOut.object! phHost).status.phasedOut &&
    (gPhOut.object! phHost).status.phasedWith.isNone &&
    (gPhOut.object! phEq).status.phasedOut &&
    (gPhOut.object! phEq).status.phasedWith == some phHost &&
    (gPhOut.object! phAura).status.phasedOut &&
    (gPhOut.object! phAura).status.phasedWith == some phEq &&
    !(gPhIn.object! phHost).status.phasedOut &&
    !(gPhIn.object! phEq).status.phasedOut &&
    !(gPhIn.object! phAura).status.phasedOut &&
    (gPhIn.object! phEq).attachedTo == some phHost &&
    (gPhIn.object! phAura).attachedTo == some phEq

  -- 6b. Batched `addLoreAfterDrawStep` across 2 Sagas & CR 121.2c APNAP `twoPlayersEachDraw opp23 me`!
  let sagaDef23 : CardDef :=
    saga "Phase23 Saga" ManaCost.empty "" "I" #[chapter "I" "You gain 1 life." (Effect.gainLife 1)]
  let gSg0 : Game := addPermanent (addPermanent afterDraw sagaDef23 me me) sagaDef23 me me
  let preSgIdx := gSg0.events.size
  let gSg1 : Game := gSg0.addLoreAfterDrawStep
  let sgBatches := (gSg1.events.extract preSgIdx gSg1.events.size).filterMap fun e =>
    match e.change with | .rules (.permanent (.counters _ .lore (.put 1) _)) => some e.batch | _ => none
  let preDrawIdx := afterDraw.events.size
  let gTwoDraw : Game :=
    match afterDraw.twoPlayersEachDraw opp23 me with
    | .ok g => g
    | .error e => panic! e
  let drawPlayers := (gTwoDraw.events.extract preDrawIdx gTwoDraw.events.size).filterMap fun e =>
    match e.change with
    | .rules (.zone (.moved _ _ (.library _) (.hand p) (.draw _) ..)) => some p
    | _ => none
  let sagaBatchAndApnapDrawOk : Bool :=
    sgBatches.size == 2 && sgBatches[0]!.isSome && sgBatches[0]! == sgBatches[1]! &&
    drawPlayers == #[me, opp23]

  -- 6c. CR 810 2HG: starting life 30, both starting teammates skip first-turn draw, shared life sync,
  --     poison `.removed` spill across teammates, and team-once poison proliferate!
  let g2hStart : Game :=
    match Start.start {
      seats := #[
        { name := "Chandra", deck := testRedDeck, teammate := some ⟨1⟩ },
        { name := "Nissa", deck := testGreenDeck, teammate := some ⟨0⟩ },
        { name := "Liliana", deck := testRedDeck, teammate := some ⟨3⟩ },
        { name := "Jace", deck := testGreenDeck, teammate := some ⟨2⟩ }
      ]
      format := .constructed
      seed := 223
      startingPlayer := some 0
    } with
    | .ok g => keepOpeningHands g 30
    | .error e => panic! e
  let start30Ok : Bool := g2hStart.players.all (·.life == 30)
  let skipSeat0 : Bool := g2hStart.skipsFirstDraw
  let g2hSeat1 : Game := g2hStart.startNextTurnAndBegin
  let skipSeat1 : Bool := g2hSeat1.activePlayer == ⟨1⟩ && g2hSeat1.skipsFirstDraw
  let g2hSeat2 : Game := g2hSeat1.startNextTurnAndBegin
  let noSkipSeat2 : Bool := g2hSeat2.activePlayer == ⟨2⟩ && !g2hSeat2.skipsFirstDraw
  let pre2hLifeIdx := g2hSeat2.events.size
  let g2hLost4 : Game := g2hSeat2.loseLife ⟨0⟩ 4 (cause := some testCause)
  let lifeLostEvts := (g2hLost4.events.extract pre2hLifeIdx g2hLost4.events.size).filter fun e =>
    match e.change with | .rules (.life (.lost ..)) => true | _ => false
  let g2hPsn0 : Game := g2hLost4.record (GameEvent.poisoned g2hLost4.turnNumber ⟨0⟩ 3 (cause := testCause))
  let g2hPsnSpill : Game := g2hPsn0.record
    (GameEvent.playerCounters g2hPsn0.turnNumber ⟨1⟩ .poison (.removed 2) (cause := testCause))
  let g2hProlif0 : Game := g2hPsnSpill.change (.pending (.chooseProliferate ⟨2⟩ 1))
  let g2hProlif1 : Game := mustApply g2hProlif0 ⟨2⟩ (.targets #[.player ⟨0⟩, .player ⟨1⟩])
  let twoHgAllOk : Bool :=
    start30Ok && skipSeat0 && skipSeat1 && noSkipSeat2 &&
    (g2hLost4.player ⟨0⟩).life == 26 && (g2hLost4.player ⟨1⟩).life == 26 &&
    lifeLostEvts.size == 1 &&
    g2hPsnSpill.teamPoison ⟨0⟩ == 1 &&
    g2hProlif1.teamPoison ⟨0⟩ == 2

  -- 6d. Simultaneous CR 704.3 SBA before `pl.lost` (in 3-player game so game continues) & `EventObject.blockingIds` LKI!
  let zeroSpirit23 : CardDef := { creature "Phase23 0/0 Spirit" ManaCost.empty #["Spirit"] 0 0 with }
  let watcherAnyDies23 : CardDef := {
    bear with
    name := "Phase23 Watcher"
    triggeredAbilities := #[
      .triggered .creatureYouControlDies { resolution := .gainLife (.fixed 1), phrase := "Gain 1." } {}
    ]
  }
  let g3pSba0 : Game :=
    let g := addPermanent (addPermanent mkThreePlayer21 watcherAnyDies23 ⟨2⟩ ⟨2⟩) zeroSpirit23 ⟨2⟩ ⟨2⟩
    g.loseLife ⟨1⟩ 20 (cause := some testCause)
  let g3pSba1 : Game := g3pSba0.checkSBA
  let sbaSimultaneousOk : Bool :=
    (g3pSba1.player ⟨1⟩).lost &&
    (g3pSba1.player ⟨1⟩).leftTheGame &&
    !(g3pSba1.battlefield.any (·.name == "Phase23 0/0 Spirit")) &&
    g3pSba1.waitingTriggers.size == 1

  let gBlkLki0 : Game := addPermanent (addPermanent (addPermanent afterDraw bear me me) hero me me) bear opp23 opp23
  let atkA := (gBlkLki0.battlefield.filter (fun o => o.name == bear.name && o.controller == some me))[0]!.id
  let atkB := (gBlkLki0.battlefield.filter (fun o => o.name == hero.name && o.controller == some me))[0]!.id
  let blkC := (gBlkLki0.battlefield.filter (fun o => o.name == bear.name && o.controller == some opp23))[0]!.id
  let blkSnapPre := gBlkLki0.snapshot (gBlkLki0.object! blkC)
  let gBlkLki1 : Game := gBlkLki0.record
    (GameEvent.blockersDeclared gBlkLki0.turnNumber opp23 #[(blkSnapPre, atkA), (blkSnapPre, atkB)])
  let blkSnap := gBlkLki1.snapshot (gBlkLki1.object! blkC)
  let blkReconstructed := Game.damageSourceObjectFromLki blkSnap
  let blockingIdsLkiOk : Bool :=
    blkSnap.blockingIds == #[atkA, atkB] &&
    blkReconstructed.status.blocking == #[atkA, atkB]

  mustHold23 "6a.phasingNestedAndCollapseOk" phasingNestedAndCollapseOk &&
  mustHold23 "6b.sagaBatchAndApnapDrawOk" sagaBatchAndApnapDrawOk &&
  mustHold23 "6c.twoHgAllOk" twoHgAllOk &&
  mustHold23 "6d.sbaSimultaneousOk" sbaSimultaneousOk &&
  mustHold23 "6e.blockingIdsLkiOk" blockingIdsLkiOk &&
  mustHold23 "6.replay" ([gPhOut, gPhIn, gSg1, gTwoDraw, g2hStart, g2hSeat1, g2hSeat2, g2hLost4, g2hPsnSpill, g2hProlif1, g3pSba1, gBlkLki1].all (fun g =>
    Game.replayEvents g.events == g && allRulesEventsClassified g))

end Phase23EventAlignment

end Mtg.Engine.EventTests
