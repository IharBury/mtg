import Mtg.Engine.Agent
import Mtg.Engine.Fixture
import Mtg.Engine.Catalog.RealityFracture
import Mtg.Engine.Catalog.RealityFractureCommander

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

def holds (g : Game) (cond : Condition) : Game × Bool :=
  (g, EvalExpr.evalCondition g { controller := me } cond)

def quiet (g : Game) : Game :=
  { g with events := #[] }

/- Drawing is recorded, and the draw condition reads the log after the
turn counter is cleared. -/
#guard
  let g := quiet afterDraw
  let (_, noDraw) := holds g (.cmp .ge (.playerMetric .cardsDrawnThisTurn .you) (.const 1))
  let g := (g.record (GameEvent.drew g.turnNumber me ⟨9⟩ 1 (cause := testCause))).record
    (GameEvent.drew g.turnNumber me ⟨8⟩ 2 (cause := testCause))
  let (_, two) := holds g (.cmp .ge (.playerMetric .cardsDrawnThisTurn .you) (.const 2))
  let (_, three) := holds g (.cmp .ge (.playerMetric .cardsDrawnThisTurn .you) (.const 3))
  !noDraw && two && !three && g.loggedDraws me == 2

/- Scrying and surveilling are the look events. Scry 0 does not count. -/
#guard
  let g := quiet afterDraw
  let (_, noScry) := holds g (.turnHistory (.scriedThisTurn { relation := .you, pred := .any }))
  let (_, noSurveil) := holds g (.turnHistory (.surveilledThisTurn { relation := .you, pred := .any }))
  let g := g.record (GameEvent.looked g.turnNumber me 0)
  let (_, zero) := holds g (.turnHistory (.scriedThisTurn { relation := .you, pred := .any }))
  let g := g.record (GameEvent.looked g.turnNumber me 2)
  let (_, scried) := holds g (.turnHistory (.scriedThisTurn { relation := .you, pred := .any }))
  let g := g.record (GameEvent.looked g.turnNumber me 1 true)
  let (_, surveilled) := holds g (.turnHistory (.surveilledThisTurn { relation := .you, pred := .any }))
  !noScry && !noSurveil && !zero && scried && surveilled

/- An artifact that entered is in the log, including after the flag is clear. -/
#guard
  let g := quiet afterDraw
  let artEnteredCond : Condition :=
    .turnHistory (.eventOccurredThisTurn { relation := .you, pred := .any } (.permanentEntered (.hasType .artifact)))
  let (_, no) := holds g artEnteredCond
  let entered := GameEvent.moved g.turnNumber
    { id := some ⟨4⟩, controller := some me, owner := me, types := #[.artifact] } .stack .battlefield
    (cause := testCause)
  let g := g.record entered
  let (_, yes) := holds g artEnteredCond
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
  let (_, yes) := holds g (.turnHistory (.eventOccurredThisTurn { relation := .you, pred := .any } (.attackedWith (.hasSubtype (.literal .hero)))))
  let (_, no) := holds g (.turnHistory (.eventOccurredThisTurn { relation := .you, pred := .any } (.attackedWith (.hasSubtype (.literal .goblin)))))
  yes && !no && attack.matchesTriggerPattern me (some ⟨5⟩) .thisAttacks &&
    entered.matchesTriggerPattern me none (.subtypeYouControlEnters .villain) &&
    !entered.matchesTriggerPattern me none (.subtypeYouControlEnters .hero) &&
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
  second.matchesTriggerPattern me none (.drawCard .you) &&
    second.matchesTriggerPattern me none (.drawCard .you) (limit := .nthEachTurn 2) &&
    second.matchesTriggerPattern ⟨1⟩ none (.drawCard .opponent) (limit := .nthEachTurn 2) &&
    !second.matchesTriggerPattern ⟨1⟩ none (.drawCard .you) &&
    death.matchesTriggerPattern me (some ⟨7⟩) .thisDies &&
    death.watches .wouldDie &&
    !exiled.isCreatureToGraveyard &&
    !exiled.watches .wouldDie &&
    (GameEvent.looked 1 me 3).matchesTriggerPattern me none (.playerAction .you .scry)

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
  let kw := ContinuousEffectSpec.keywordsUntilEot b.id #[Keyword.trample]
  let g1 := (g0.applyChange (.rules (.continuousEffect (.created ⟨100⟩ pump)))).applyChange
    (.rules (.continuousEffect (.created ⟨101⟩ kw)))
  let applied :=
    g1.pumpOf (g1.object! b.id) == (3, 3) &&
      g1.currentKeywords (g1.object! b.id) == #[Keyword.trample]
  let g2 := (g1.applyChange (.rules (.continuousEffect (.expired ⟨100⟩)))).applyChange
    (.rules (.continuousEffect (.expired ⟨101⟩)))
  let reverted :=
    g2.pumpOf (g2.object! b.id) == (0, 0) &&
      g2.currentKeywords (g2.object! b.id) == (#[] : Array KeywordAbility)
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
      created.contains (.keywordsUntilEot b.id #[Keyword.trample]) &&
      created.contains (.cantBlockUntilEot b.id)
  let g2 := g1.clearEOT
  let expired := GameEvent.expiredEffects g2.events
  let hasExpired :=
    expired.contains (.pump b.id 2 2) &&
      expired.contains (.keywordsUntilEot b.id #[Keyword.trample]) &&
      expired.contains (.cantBlockUntilEot b.id) &&
      g2.pumpOf (g2.object! b.id) == (0, 0) &&
      g2.currentKeywords (g2.object! b.id) == (#[] : Array KeywordAbility) &&
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
      staticAbilities := #[.creaturesYouControlHave #[Keyword.trample]] }
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
    !(g2.staticAbilities (g2.object! lord.id)).contains (.creaturesYouControlHave #[Keyword.trample]) &&
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
  let g1 := (g0.createEffect (.keywordsUntilEot b.id #[Keyword.flying])).createEffect
    (.keywordsUntilEot b.id #[Keyword.haste])
  let g2 := g1.expireEffect (.keywordsUntilEot b.id #[Keyword.flying])
  g1.currentKeywords (g1.object! b.id) == #[Keyword.flying, Keyword.haste] &&
    g2.currentKeywords (g2.object! b.id) == #[Keyword.haste]

/- A flag set by two continuous effects stays set until both have ended. A
second "loses all abilities" keeps the printed static abilities off. -/
#guard
  let lordDef : CardDef :=
    { bear with
      name := "Bear Lord"
      staticAbilities := #[.creaturesYouControlHave #[Keyword.trample]] }
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
    !(g4.staticAbilities (g4.object! lord.id)).contains (.creaturesYouControlHave #[Keyword.trample]) &&
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
    created.contains (.cantBeBlockedUntilEot b.id)

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
  let g1 := ((g0.changeControl b me (untilEot := true)).record
    (GameEvent.playerLost g0.turnNumber opp .conceded)).record
    (GameEvent.playerLeftGame g0.turnNumber opp)
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
      keywords := #[.impending 1 CostSpec.empty] }
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
  let dtSource : EventObject := { keywords := #[Keyword.deathtouch] }
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
    (let dtCreature : CardDef := { bear with name := "Deathtouch Bear", keywords := #[Keyword.deathtouch] }
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
    heroToPlayer.matchesTriggerPattern me (some h.id) .heroesYouControlDealDamageToPlayer &&
    !bearToHero.matchesTriggerPattern me (some h.id) .heroesYouControlDealDamageToPlayer &&
    !(GameEvent.moved 1 { controller := some me, owner := me, types := #[.creature] }
      .stack .battlefield (cause := testCause)).matchesTriggerPattern me (some b.id) .anotherCreatureYouControlEnters

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
      staticAbilities := #[
        .entersTapped,
        .entersWithPlusOneCounters 2,
        .entersWithShield 1,
        .entersWithIndestructibleCounter
      ] }
  let testPlaneswalker : CardDef :=
    { name := "Test Planeswalker"
      types := #[.planeswalker]
      subtypes := #["Jace"]
      loyalty := some 4 }
  let testSaga : CardDef :=
    { name := "Test Saga"
      types := #[.enchantment]
      subtypes := #["Saga"]
      triggeredAbilities := #[
        TriggeredAbility.sagaChapter 1 (Effect.gainLife 1),
        TriggeredAbility.sagaChapter 2 (Effect.gainLife 2)] }
  let testImpending : CardDef :=
    { bear with
      name := "Impending Bear"
      keywords := #[.impending 3 (CostSpec.ofGeneric 1)] }
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
  let (_, atkTok) := (quiet g1).createToken me { bear with name := "Token Bear", isToken := true }
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
    !tok.status.attacking &&
    tok.status.attackingTarget == none &&
    atkTok.status.attacking &&
    atkTok.status.attackingTarget == some (.player opp)

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
      | .rules (.continuousEffect (.expired ..)) =>
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
      power := some (.fixed 4)
      toughness := some (.fixed 4)
      keywords := #[.crew 2]
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
      power := some (.fixed 3)
      toughness := some (.fixed 3)
      activatedAbilities := #[ActivatedAbility.zemoBoastAbility] }
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
        #[{ cost := CostSpec.ofItems #[.mana (ManaCost.ofGeneric 2), .loyalty (.plus 1)]
            effect := {} }] }
  let myWatcher : CardDef :=
    { name := "Loyalty Watcher"
      types := #[.enchantment]
      triggeredAbilities :=
        #[TriggeredAbility.ofPattern (.youActivateLoyaltyAbility 0) (Instruction.drawFixed 1),
          TriggeredAbility.ofPattern .youPutLoyaltyCounters (Instruction.drawFixed 1)] }
  let oppWatcher : CardDef :=
    { name := "Opp Loyalty Watcher"
      types := #[.enchantment]
      triggeredAbilities :=
        #[TriggeredAbility.ofPattern .opponentActivatesLoyaltyAbility (Instruction.drawFixed 1)] }
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
        #[{ cost := CostSpec.ofItems #[.mana (ManaCost.ofGeneric 2), .sacrifice (.exact 1) .self]
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
          power := some (.fixed 0)
          toughness := some (.fixed 0)
          isToken := true } }
  let gInc0 := quiet (addPermanent afterDraw incDef me me)
  let inc := (gInc0.battlefield.filter (·.name == "Incubator Token"))[0]!
  let gIncTransformed :=
    gInc0.withResolvingContext (some inc.id) me (fun g =>
      g.applyAbilityEffect me { body := .permanent (.transform .this) } #[] (some inc.id))
  let incAfter := gIncTransformed.object! inc.id
  let staticCreature : CardDef :=
    { name := "Static Bear"
      types := #[.creature]
      power := some (.fixed 2)
      toughness := some (.fixed 2)
      activatedAbilities := #[ActivatedAbility.zemoBoastAbility] }
  let gPhase0 := quiet (addPermanent (addPermanent afterDraw staticCreature me me) hero me me)
  let sb := (gPhase0.battlefield.filter (·.name == "Static Bear"))[0]!
  let h := (gPhase0.battlefield.filter (·.name == hero.name))[0]!
  let gPhasedOut :=
    gPhase0.withResolvingContext (some h.id) me (fun g => g.phaseOut sb)
  let expiredCause? : Option EventCause :=
    gPhasedOut.events.findSome? (fun e =>
      match e.change with
      | .rules (.continuousEffect (.expired ..)) => e.cause?
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
    incAfter.printed.power == some (.fixed 0) &&
    incAfter.printed.toughness == some (.fixed 0) &&
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
    g0.applyAbilityEffect me { body := .turn (.extraTurn .you) } #[] (some h.id)
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
    (quiet g0).applyUnified me { Effect.phaseOutKicker with targets := .player } #[Target.player me]
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
    | .rules (.continuousEffect (.expired ..)) =>
      e.cause? == some (EventCause.turnBased .cleanupClear)
    | _ => false) &&
    gPermNextTurn.events.any (fun e =>
      match e.change with
      | .rules (.continuousEffect (.expired ..)) =>
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
      | .rules (.continuousEffect (.expired ..)) =>
        e.cause? == some (EventCause.turnBased .cleanupClear)
      | _ => false) &&
    gExtraEndedTurn.events.any (fun e =>
      match e.change with
      | .rules (.continuousEffect (.expired ..)) =>
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
      triggeredAbilities := #[TriggeredAbility.resourcePlusOneCreateInsectOnce] }
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
      g.applyEffect me syntheticDestiny.spellEffect.get! #[] (sourceId := some s.id))
  let synthStoredCause := gSynth.delayedTriggers[0]!.cause
  let synthExileCauses :=
    gSynth.events.filterMap (fun e =>
      match e.change with
      | .rules (.zone (.moved _ _ .battlefield .exile ..)) => e.cause?
      | _ => none)
  let gSunfall :=
    (quiet gWithSrc).withResolvingContext (some s.id) me (fun g =>
      g.applyEffect me sunfall.spellEffect.get! #[] (sourceId := some s.id))
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
      g.applyAbilityEffect me { body := .permanent (.transform .this) } #[] (some sunfallInc.id))
  let sunfallIncAfter := gSunfallTransformed.object! sunfallInc.id
  -- 4. .massPolymorph shares one exileCause for battlefield exiles and one distinct
  --    revealCause across revealUntil, putHits, and restBottom
  let gMassPoly :=
    (quiet gWithSrc).withResolvingContext (some s.id) me (fun g =>
      g.applyEffect me massPolymorph.spellEffect.get! #[] (sourceId := some s.id))
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
      g.applyAbilityEffect me { venserFerventForger.triggeredAbilities[0]!.modeEffects[1]! with targets := .none } #[Target.permanent b.id] (some s.id))
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
      g.applyAbilityEffect me { jhoiraWeatherlightCorsair.triggeredAbilities[0]!.effect with targets := .none } #[Target.player me] (some s.id))
  let jhoiraPendingOk :=
    match gJhoiraPending.pending with
    | .resolveRandom (.orderInto ids (.library p) (some _)) => p == me && ids.size == 2
    | _ => false
  let gJhoiraDone :=
    match gJhoiraPending.supplyOrder #[] with
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
    sunfallIncAfter.name == "Phyrexian Token" &&
    sunfallIncAfter.printed.power == some (.fixed 0) &&
    sunfallIncAfter.printed.toughness == some (.fixed 0) &&
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
  -- 1. Exiling multiple lands you control shares one cause across all exiled lands
  let gLands :=
    (quiet g0).applyAbilityEffect me
      { targets := (.single {
          domain := .object .battlefield (.all #[.hasType .land, .controlledBy .you])
          count := .upTo 3 })
        body := Instruction.exile .allTargets { linkToSource := true } }
      #[Target.permanent l1.id, Target.permanent l2.id] (some b.id)
  let landExileCauses :=
    gLands.events.filterMap (fun e =>
      match e.change with
      | .rules (.zone (.moved _ _ .battlefield .exile ..)) => e.cause?
      | _ => none)
  -- 2. Exiling multiple permanents until next end step shares one cause
  let gNextEndTrig :=
    (quiet g0).applyAbilityEffect me
      { targets := (.single { domain := .object .battlefield .anyObject, count := .upTo 2 })
        body := Instruction.exile .allTargets { delayedReturn? := some (.atNextEndStep false .owner) } }
      #[Target.permanent b.id, Target.permanent h.id] (some b.id)
  let nextEndTrigCauses :=
    gNextEndTrig.events.filterMap (fun e =>
      match e.change with
      | .rules (.zone (.moved _ _ .battlefield .exile ..)) => e.cause?
      | _ => none)
  -- 3. Impulse exile until next turn / this turn shares cause between
  --    `ZoneEvent.moved` and `effectCreated (.playPermission ...)`
  let gPlayNext :=
    (quiet g0).applyAbilityEffect me
      { body := Instruction.exile (.topOfLibrary .you (.const 1)) {
          grantPlayPerm? := some { duration := .untilEndOfNextTurnOf .you, landsAllowed := true } } }
      #[] (some b.id)
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
    (quiet g0).applyAbilityEffect me
      { body := Instruction.exile (.topOfLibrary .you (.const 1)) {
          grantPlayPerm? := some { duration := .untilEndOfTurn, landsAllowed := true } } }
      #[] (some b.id)
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
  -- 4. Reveal-until-creature shares one cause across putting the creature onto
  --    the battlefield and putting the rest on the bottom of the library
  let gRevSetup :=
    let g := (g0.move b.id (.library me) none (libraryPosition := some .top)).1
    let g := (g.move l1.id (.library me) none (libraryPosition := some .top)).1
    let g := (g.move l2.id (.library me) none (libraryPosition := some .top)).1
    quiet g
  let gRevPending :=
    gRevSetup.applyTriggeredAbility me (.onEnter Effect.triggerRevealUntilCreature) (some h.id)
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
generic `.inspectLibrary` (`.revealUntil`), and
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
      g.applyAbilityEffect me
        { body := .player (.inspectLibrary {
            source := .topCards .you (.const 3) false
            action := .takeMatching .anyObject (.upTo (.const 1)) (.hand .controller) {} true false
            rest := .bottomAnyOrder }) }
        #[] (some h.id))
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
      g.applyAbilityEffect me
        { body := .player (.inspectLibrary {
            source := .topCards .you (.const 3) false
            action := .takeMatching (.hasSubtype (.literal .hero)) (.upTo (.const 1))
              (.battlefield .controller) { mayTransformOnEnter := true } false false
            rest := .bottomRandom }) }
        #[] (some h.id))
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
  -- 4. Generic `inspectLibrary` (`.revealUntil` onto battlefield, rest on bottom random)
  let gTrigRevPending :=
    gLibSetup.withResolvingContext (some h.id) me (fun g =>
      g.applyTriggeredAbility me (TriggeredAbility.ofPattern .thisEnters
        (.player (.inspectLibrary {
          source := .revealUntil .you (.hasType .creature) (.const 1)
          action := .moveAll (.battlefield .controller) {}
          rest := .bottomRandom
        }))) (some h.id))
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
      g.applyAbilityEffect me Effect.exileHandDrawPlayUntilNext #[] (some h.id))
  let hexCauses :=
    gHex.events.filterMap (fun e =>
      match e.change with
      | .rules (.zone (.moved ..)) => e.cause?
      | .rules (.continuousEffect (.created _ (.permission _ (.playFromExile ..) _))) => e.cause?
      | _ => none)
  -- 7. `.identityEcho` uses one cause for the exile and a distinct shared cause for the reveal/put/bottom
  let gEchoPending :=
    gLibSetup.withResolvingContext (some h.id) me (fun g =>
      g.applyAbilityEffect me identityEcho.activatedAbilities[0]!.effect #[.permanent h.id] (some h.id))
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
      g.applyAbilityEffect me Effect.twoPlayersDraw #[Target.player me, Target.player opp] (sourceId := some h.id))
  let twoDrawCauses :=
    gTwoDraw.events.filterMap (fun e =>
      match e.change with
      | .rules (.zone (.moved ..)) => e.cause?
      | _ => none)
  let gMillSubtype :=
    gLibSetup.withResolvingContext (some h.id) me (fun g =>
      g.applyTriggeredAbility me (.onEnterMillThenSubtypeToHand 3 "Bear") (some h.id) #[] #[] none none "This creature")
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
  let balinAb : TriggeredAbility :=
    TriggeredAbility.ofPattern .thisEnters Effect.triggerDiscardHandDrawDamageIfStory.body
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
      g.applyTriggeredAbility me balinAb (some h.id))
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
    { hero with name := "Lifelink Hero", keywords := #[Keyword.lifelink] }
  let gDmgSetup0 := addPermanent (addPermanent g0 lifelinkHero me me) bear opp opp
  let lh := (gDmgSetup0.battlefield.filter (·.name == "Lifelink Hero"))[0]!
  let oppBear := (gDmgSetup0.battlefield.filter (fun o => o.name == bear.name && gDmgSetup0.controlledBy o opp))[0]!
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
      g.applyTriggeredAbility me
        (TriggeredAbility.mkTrigger .thisEnters {
          body := Instruction.dealDamageFixed
            (.both (.inZones .battlefield (.all #[.hasType .creature, .not (.hasSubtype (.literal .dragon))])) .opponents) 1
        }) (some lh.id))
  let sweepResCauses :=
    gSweepRes.events.filterMap (fun e =>
      match e.change with
      | .rules _ => e.cause?
      | _ => none)
  let gNivRaw := gDmgSetup.applyAbilityEffect me nivMizzetGhostCounsel.triggeredAbilities[0]!.effect #[] (some lh.id) (lastKnownPower := some 2)
  let nivRawCauses :=
    gNivRaw.events.filterMap (fun e =>
      match e.change with
      | .rules _ => e.cause?
      | _ => none)
  let gNivRes :=
    gDmgSetup.withResolvingContext (some lh.id) me (fun g =>
      g.applyAbilityEffect me nivMizzetGhostCounsel.triggeredAbilities[0]!.effect #[] (some lh.id) (lastKnownPower := some 2))
  let nivResCauses :=
    gNivRes.events.filterMap (fun e =>
      match e.change with
      | .rules _ => e.cause?
      | _ => none)
  let gNivLocked :=
    quiet (gDmgSetup.createEffect (.lifeCantChange me))
      |>.withResolvingContext (some lh.id) me (fun g =>
        g.applyAbilityEffect me nivMizzetGhostCounsel.triggeredAbilities[0]!.effect #[] (some lh.id) (lastKnownPower := some 2))
  let nivLockedEvents :=
    gNivLocked.events.filterMap (fun e =>
      match e.change with
      | .rules _ => e.cause?
      | _ => none)
  let gDreadRaw := gDmgSetup.applyAbilityEffect me dreadhordeInvasion.triggeredAbilities[0]!.effect #[] (some lh.id)
  let dreadRawCauses :=
    gDreadRaw.events.filterMap (fun e =>
      match e.change with
      | .rules _ => e.cause?
      | _ => none)
  let gDreadRes :=
    gDmgSetup.withResolvingContext (some lh.id) me (fun g =>
      g.applyAbilityEffect me dreadhordeInvasion.triggeredAbilities[0]!.effect #[] (some lh.id))
  let dreadResCauses :=
    gDreadRes.events.filterMap (fun e =>
      match e.change with
      | .rules _ => e.cause?
      | _ => none)
  let gSkrelvRaw := gDmgSetup.applyAbilityEffect me skrelvsHive.triggeredAbilities[0]!.effect #[] (some lh.id)
  let skrelvRawCauses :=
    gSkrelvRaw.events.filterMap (fun e =>
      match e.change with
      | .rules _ => e.cause?
      | _ => none)
  let gSkrelvRes :=
    gDmgSetup.withResolvingContext (some lh.id) me (fun g =>
      g.applyAbilityEffect me skrelvsHive.triggeredAbilities[0]!.effect #[] (some lh.id))
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
    balinRawCauses.size == handSize * 2 &&
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
      keywords := #[Keyword.firstStrike] }
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
        TriggeredAbility.ofPattern .otherCreaturesDie (Instruction.drawFixed 1) (grouping := .oncePerBatch),
        TriggeredAbility.ofPattern .nontokenCreatureYouControlDies (Instruction.gainLifeFixed 1),
        TriggeredAbility.ofPattern .creatureCardPutIntoYourGy (Instruction.drawFixed 1) (grouping := .oncePerBatch),
        TriggeredAbility.ofPattern (.createTokens .you (.hasType .creature)) (Instruction.drawFixed 1) (grouping := .oncePerBatch),
        TriggeredAbility.ofPattern .creaturesYouControlBecomeTapped (Instruction.drawFixed 1) (grouping := .oncePerBatch)] }
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
  let simulOneOrMore := gSimulDie.waitingTriggers.filter (·.pattern == .otherCreaturesDie)
  let simulEach := gSimulDie.waitingTriggers.filter (·.pattern == .nontokenCreatureYouControlDies)
  let gSeqDie := (gBase.destroyPermanent (gBase.object! b.id)).destroyPermanent (gBase.object! h.id)
  let seqOneOrMore := gSeqDie.waitingTriggers.filter (·.pattern == .otherCreaturesDie)
  -- 2. Simultaneous vs. sequential mill of creature cards into your graveyard
  let gSimulMill := gBase.mill me 2
  let simulMillTrig := gSimulMill.waitingTriggers.filter (·.pattern == .creatureCardPutIntoYourGy)
  let gSeqMill := (gBase.mill me 1).mill me 1
  let seqMillTrig := gSeqMill.waitingTriggers.filter (·.pattern == .creatureCardPutIntoYourGy)
  -- 3. Simultaneous vs. sequential creature token creation
  let gSimulTok := gBase.createKindTokens me .humanSoldier 2
  let simulTokTrig := gSimulTok.waitingTriggers.filter (·.pattern == .createTokens .you (.hasType .creature))
  let gSeqTok := (gBase.createKindTokens me .humanSoldier 1).createKindTokens me .humanSoldier 1
  let seqTokTrig := gSeqTok.waitingTriggers.filter (·.pattern == .createTokens .you (.hasType .creature))
  -- 4. Simultaneous vs. sequential tapping of creatures you control
  let gSimulTap := gBase.withBatch none (fun g =>
    (g.becomeTapped (g.object! b.id)).becomeTapped (g.object! h.id))
  let simulTapTrig := gSimulTap.waitingTriggers.filter (·.pattern == .creaturesYouControlBecomeTapped)
  let gSeqTap := (gBase.becomeTapped (gBase.object! b.id)).becomeTapped (gBase.object! h.id)
  let seqTapTrig := gSeqTap.waitingTriggers.filter (·.pattern == .creaturesYouControlBecomeTapped)
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
   `.discard .any` with `.perPlayerInBatch` once for a multi-card hand), and a batch in which two
   players discard queues it once per discarding player.
2. Unified `+1/+1` counter put evaluation fires both `onceEachTurn` abilities
   (`plusOneCreateInsectOnce`, `plusOneOnThisOnce`) and Invisible Woman on
   printed enters-with +1/+1 counters and `.explore` (which also applies
   `countersYouPut` / Doc Samson), while recording triggered events so a second
   +1/+1 counter event in the same turn does not re-trigger them.
3. `eventSuppressedByKarn` suppresses enters triggers (`tokenYouControlEnters`)
   without suppressing counter-put triggers (`youPutCountersOnGoblinOrcArmy`,
   `youPutLoyaltyCounters`, `youPutPlusOneOnOtherHeroYouControl`) on entering permanents
   (CR 122.6). -/
#guard
  let isYouPutPlusOne (wt : WaitingTrigger) : Bool :=
    match wt.pattern with
    | .putCounters (some .you) (some .plusOnePlusOne) _ => true
    | _ => false
  -- 1. discardEntireHand batching and per-player discard
  let discardWatcher : CardDef :=
    { name := "Discard Watcher"
      types := #[.enchantment]
      triggeredAbilities := #[TriggeredAbility.ofPattern (.discard .any) (Instruction.drawFixed 1)
        (grouping := .perPlayerInBatch)] }
  let gDisc0 := quiet (addPermanent afterDraw discardWatcher me me)
  let gDisc1 := gDisc0.discardEntireHand me
  let discEvents1 := gDisc1.events.filter (fun e =>
    match e.change with
    | .rules (.zone (.moved _ _ (.hand _) (.graveyard _) .discard ..)) => true
    | _ => false)
  let discTrig1 := gDisc1.waitingTriggers.filter (·.pattern == .discard .any)
  let gDiscBoth := gDisc0.withBatch none (fun g =>
    (g.discardEntireHand me).discardEntireHand opp)
  let discTrigBoth := gDiscBoth.waitingTriggers.filter (·.pattern == .discard .any)
  -- 2. Unified +1/+1 counter put on printed entersWithPlusOneCounters and .explore + Doc Samson
  let insectWatcher : CardDef :=
    { (creature "Insect Watcher" ManaCost.empty #["Hero"] 1 1) with
      triggeredAbilities := #[TriggeredAbility.resourcePlusOneCreateInsectOnce] }
  let selfOnceWatcher : CardDef :=
    { (creature "Self Once Watcher" ManaCost.empty #["Hero"] 2 2) with
      triggeredAbilities := #[TriggeredAbility.resourcePlusOneOnThisOnce] }
  let wallWatcher : CardDef :=
    { (creature "Wall Watcher" ManaCost.empty #["Hero"] 1 4) with
      triggeredAbilities := #[TriggeredAbility.resourcePlusOneOnHeroesCreateWall] }
  let entersHero : CardDef :=
    { (creature "Enters Hero" ManaCost.empty #["Hero", "Goblin"] 1 1) with
      staticAbilities := #[.entersWithPlusOneCounters 2] }
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
  let plusTrigs1 := gPlusEntered.waitingTriggers.filter isYouPutPlusOne
  let gPlusSecond := gPlusEntered.addPlusOnePlusOneTo (gPlusEntered.object! ehBfId) 1
  let plusTrigs2 := gPlusSecond.waitingTriggers.filter isYouPutPlusOne
  -- Explore with Doc Samson and nonland top card
  let gExp0 :=
    let g := addPermanent (addPermanent (addPermanent afterDraw insectWatcher me me) docSamsonDef me me) bear me me
    let g := addPermanent g bear me me
    let topId := g.battlefield.back!.id
    let g := (g.move topId (.library me) none (libraryPosition := some .top)).1
    quiet g
  let explorer := (gExp0.battlefield.filter (·.name == bear.name))[0]!
  let gExp1 := gExp0.applyAbilityEffect me { body := .player (.explore .this) } #[] (some explorer.id)
  let explorerAfter := gExp1.object! explorer.id
  let expTrigs := gExp1.waitingTriggers.filter isYouPutPlusOne
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
        TriggeredAbility.watchTokensEnterMayDraw,
        TriggeredAbility.ofPattern .youPutCountersOnGoblinOrcArmy (Instruction.drawFixed 1) (grouping := .oncePerBatch),
        TriggeredAbility.ofPattern .youPutLoyaltyCounters (Instruction.drawFixed 1),
        TriggeredAbility.resourcePlusOneOnHeroesCreateWall] }
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
    (gKarnOppGob.waitingTriggers.filter (·.pattern == .youPutCountersOnGoblinOrcArmy)).isEmpty &&
    (gKarn3.waitingTriggers.filter (·.pattern == .tokenYouControlEnters)).isEmpty &&
    (gKarn3.waitingTriggers.filter (·.pattern == .youPutCountersOnGoblinOrcArmy)).size == 1 &&
    (gKarn3.waitingTriggers.filter (·.pattern == .youPutLoyaltyCounters)).size == 1 &&
    (gKarn3.waitingTriggers.filter isYouPutPlusOne).size == 1

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

def mkTwoHeadedGiant18 (seed : UInt64 := 180) : Game :=
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

def mkThreePlayer27i1 (seed : UInt64 := 2710) : Game :=
  let cfg : StartConfig := {
    seats := #[
      { name := "Alice", deck := testRedDeck },
      { name := "Bob", deck := testGreenDeck },
      { name := "Charlie", deck := testRedDeck }
    ]
    format := .constructed
    seed
    startingPlayer := some 0
  }
  match Start.start cfg with
  | .ok g => (keepOpeningHands g 24).advanceStep
  | .error e => panic! e

def mkTwoHeadedGiant27i4 (seed : UInt64 := 2740) : Game :=
  let cfg : StartConfig := {
    seats := #[
      { name := "TeamA1", deck := testRedDeck, teammate := some ⟨1⟩ },
      { name := "TeamA2", deck := testGreenDeck, teammate := some ⟨0⟩ },
      { name := "TeamB1", deck := testRedDeck, teammate := some ⟨3⟩ },
      { name := "TeamB2", deck := testGreenDeck, teammate := some ⟨2⟩ }
    ]
    format := .constructed
    seed
    startingPlayer := some 0
  }
  match Start.start cfg with
  | .ok g => (keepOpeningHands g 40).advanceStep
  | .error e => panic! e

end Mtg.Engine.EventTests
