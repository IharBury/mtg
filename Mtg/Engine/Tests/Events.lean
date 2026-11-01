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
  yes && !no && attack.matchesTrigger me ⟨5⟩ .attacking &&
    entered.matchesTrigger me ⟨0⟩ (.subtypeYouControlEnters .villain) &&
    !entered.matchesTrigger me ⟨0⟩ (.subtypeYouControlEnters .hero) &&
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
      g1.untilEotKeywords (g1.object! b.id) == Keyword.trample
  let g2 := (g1.applyChange (.rules (.continuousEffect (.expired ⟨100⟩)))).applyChange
    (.rules (.continuousEffect (.expired ⟨101⟩)))
  let reverted :=
    g2.pumpOf (g2.object! b.id) == (0, 0) &&
      g2.untilEotKeywords (g2.object! b.id) == Keywords.none
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
      g2.untilEotKeywords (g2.object! b.id) == Keywords.none &&
      !g2.cantBlockUntilEot (g2.object! b.id)
  hasCreated && hasExpired

/- Rule 611.2b: until-next-turn, while-source-remains, and until-cast / play
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
      (GameEvent.tapped g0.turnNumber b.asEvent true true
        (cause := .turnBased .declareAttackers)))
  let nonOneShotDidNotAdvance :=
    gNonOneShot.nextEffectId == effId0 &&
      (GameEvent.oneShotEffectsWithId gNonOneShot.events).isEmpty
  let g1 := g0.draw me 1 (cause := some (.turnBased .drawStepDraw))
  let g2 := g1.gainLife me 3 (cause := some (.turnBased .cleanupClear))
  let g3 := g2.loseLife me 2 (cause := some (.costPayment .life me))
  let g4 := g3.record (GameEvent.counters g3.turnNumber (some me) b.asEvent .plusOnePlusOne 2 false
    (cause := .costPayment .removeCounters me))
  let g5 := g4.record (GameEvent.tapped g4.turnNumber b.asEvent true true
    (cause := .costPayment .tap me))
  let g6 := g5.record (GameEvent.untapped g5.turnNumber b.asEvent
    (cause := .turnBased .untapAll))
  let g7 := g6.withResolvingContext (some b.id) me (fun g => g.createTreasureTokens me 1)
  let g8 := ((g7.record (GameEvent.looked g7.turnNumber me 2)).record
    (GameEvent.resolved g7.turnNumber me 1 b.asEvent)).record
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
  g1.untilEotKeywords (g1.object! b.id) == Keywords.merge Keyword.flying Keyword.haste &&
    g2.untilEotKeywords (g2.object! b.id) == Keyword.haste

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
  let g1 := (g0.dealDamageLoseIndestructibleExileTo b 1 b.asEvent).grantCantBeBlockedThisTurn b
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
        let g5 := (g4.putCountersExceptPlusOne copyId { counters := #[(.time, 2)] }).beginStep .end
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
          (g5.object! permId).status.time == 1 &&
          g5.isCreature (g5.object! copyId) &&
          (g5.object! copyId).status.time == 2

/- Phase 1 isolation: applying a single `PermanentEvent.tapped` or
`PermanentEvent.untapped` event yields the exact tapped state without separate
status setters (CR 701.26a / 701.26b). -/
#guard
  let g0 := quiet (addPermanent afterDraw bear me me)
  let b := (g0.battlefield.filter (·.name == "Event Bear"))[0]!
  let g1 := g0.applyChange (.rules (.permanent (.tapped b.asEvent true)))
  let g2 := g1.applyChange (.rules (.permanent (.untapped b.asEvent)))
  (g1.object! b.id).status == { b.status with tapped := true } &&
    (g2.object! b.id).status == { b.status with tapped := false }

/- Phase 1 isolation: applying a single `PermanentEvent.counters` event puts or
removes counters on a permanent (including poison counters) or counters on a
player (poison and non-poison, CR 122.1). -/
#guard
  let g0 := quiet (addPermanent afterDraw bear me me)
  let b := (g0.battlefield.filter (·.name == "Event Bear"))[0]!
  let g1 := g0.applyChange (.rules (.permanent (.counters (.object b.asEvent) .plusOnePlusOne (.put 3) (some me))))
  let g2 := g1.applyChange (.rules (.permanent (.counters (.object b.asEvent) .plusOnePlusOne (.removed 1) none)))
  let g3 := g2.applyChange (.rules (.permanent (.counters (.player me) .poison (.put 4) (some opp))))
  let g4 := g3.applyChange (.rules (.permanent (.counters (.player me) .poison (.removed 1) none)))
  let g5 := g4.applyChange (.rules (.permanent (.counters (.object b.asEvent) .poison (.put 2) none)))
  let g6 := g5.applyChange (.rules (.permanent (.counters (.object b.asEvent) .poison (.removed 1) none)))
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
  let gDealtOnly := g0.record (GameEvent.damaged g0.turnNumber dtSource b.asEvent 1 false (cause := testCause))
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
  let g1 := g0.applyChange (.rules (.permanent (.attached h.asEvent b.id none)))
  let g2 := g1.applyChange (.rules (.permanent (.unattached h.asEvent b.id)))
  let g3 := g2.changeControl b opp
  let g4 := g3.changeControl (g3.object! b.id) me
  let g5 := g4.applyChange (.rules (.permanent (.designation b.asEvent (.goaded me) true)))
  let g6 := g5.applyChange (.rules (.permanent (.designation b.asEvent (.goaded opp) true)))
  let g7 := g6.expireGoadedFor me
  let g8 := g7.expireGoadedFor opp
  let heroToPlayer := GameEvent.damagedPlayer 1 h.asEvent opp 2 true (cause := testCause)
  let bearToHero := GameEvent.damaged 1 b.asEvent h.asEvent 2 false (cause := testCause)
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
    (let gPerm := (g8.applyChange (.rules (.permanent (.designation b.asEvent (.goaded me false) true)))).expireGoadedFor me
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
  let g4 := g3.record (GameEvent.transformed g3.turnNumber (g3.object! b.id).asEvent true
    (cause := .oneShotEffect (some ⟨g3.nextEffectId⟩) (some b.id) (some me)))
  let g5 := g4.record (GameEvent.resolved g4.turnNumber me 1 (g4.object! b.id).asEvent)
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
  let gCrewDeclined :=
    match gCrewStarted.answerFraChoice me .decline with
    | .ok g => g
    | .error _ => gCrewStarted
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
    (quiet gZemo1).record (GameEvent.attackersDeclared gZemo1.turnNumber me #[(z.asEvent, .player opp)])
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
turn would begin (CR 611.2b / 800.4m); Kang's extra-turn `.powerUpsForbiddenThisTurn`
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
    let g := { g with assignedCombatDamage := #[{ source := b.id, toPlayer := 2 }] }
    (((quiet g).dealAssignedCombatDamage).receivePriority me).resolveTop
  let gTreasPw :=
    let g := addPermanent (addPermanent g0 pwDef opp opp) cleaver3Def me me
    let pw := (g.battlefield.filter (·.name == "Target PW"))[0]!
    let clv := (g.battlefield.filter (·.name == "Target Cleaver"))[0]!
    let g := (g.attachSourceTo clv (g.object! b.id)).markAttacking b.id (some (.planeswalker pw.id))
    let g := { g with assignedCombatDamage := #[{ source := b.id, toPlayer := 2 }] }
    (((quiet g).dealAssignedCombatDamage).receivePriority me).resolveTop
  -- 4. clearCombat: .removeFromCombatAtEndOfCombat in advanceStep from .endOfCombat, none in beginStep .cleanup
  let gEndCombat :=
    (quiet ({ g0 with step := .endOfCombat }.markAttacking b.id)).advanceStep
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
  let gEaglesUpkeep := ((quiet gEagles2).beginStep .upkeep).resolveTop.resolveTop
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
    rules1[0]!.batch == ⟨b0⟩ &&
    rules1[1]!.batch == ⟨b0⟩ &&
    rules1[0]!.cause? == some (.oneShotEffect (some ⟨e0⟩) none (some me)) &&
    rules1[1]!.cause? == some (.oneShotEffect (some ⟨e0⟩) none (some me)) &&
    g1.nextBatchId == b0 + 1 &&
    g1.nextEffectId == e0 + 1 &&
    rules2.size == 2 &&
    rules2[0]!.batch == ⟨b0 + 1⟩ &&
    rules2[1]!.batch == ⟨b0 + 1⟩ &&
    rules2[0]!.cause? == some (.stateBased .lethalDamage) &&
    rules2[1]!.cause? == some (.stateBased .zeroOrLessToughness) &&
    g2.nextBatchId == b0 + 2 &&
    rules3.size == 2 &&
    rules3[0]!.batch == ⟨b0 + 2⟩ &&
    rules3[1]!.batch == ⟨b0 + 3⟩ &&
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
        if before.id == some oid && e.cause? == some (.stateBased .lethalDamage) then some e.batch else none
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
  let gStep := (quiet { afterDraw with step := .draw }).advanceStep
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
    let g := { g with step := .declareAttackers, pending := .declareAttackers }
    quiet g
  let bMe := (g0.battlefield.filter (fun o => o.name == bear.name && o.controlledBy me))[0]!
  let hMe := (g0.battlefield.filter (fun o => o.name == hero.name && o.controlledBy me))[0]!
  let pwOpp := (g0.battlefield.filter (·.name == "Opp Walker"))[0]!
  let bOpp := (g0.battlefield.filter (fun o => o.name == bear.name && o.controlledBy opp))[0]!
  -- 1. 508.4 becameAttacking (targeting planeswalker) does NOT fire attack triggers
  let gBecame := g0.record (GameEvent.becameAttacking g0.turnNumber hMe.asEvent (.planeswalker pwOpp.id)
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
  let gBothAtk := (quiet gAtk).record (GameEvent.becameAttacking gAtk.turnNumber (gAtk.object! hMe.id).asEvent (.player opp)
    (cause := .oneShotEffect (some ⟨78⟩) none (some me)))
  let gToBlk := quiet { gBothAtk with
    step := .declareBlockers
    pending := .declareBlockers
    blockersQueue := #[opp] }
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
    let g := (quiet g0).record (GameEvent.becameAttacking g0.turnNumber hMe.asEvent (.planeswalker pwOpp.id)
      (cause := .oneShotEffect (some ⟨81⟩) none (some me)))
    let g := insertObject g bear me .stack (some me) {}
    let spId := (g.objects.filter (fun o => o.name == bear.name && o.zone == .stack))[0]!.id
    let g := g.putStackEntry me spId
    { g with step := .declareBlockers, pending := .none }
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
    bOppAfterRem.status.blocking.isEmpty &&
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
    .triggered .creatureYouControlDies
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
      let g := g.dealDamageToPermanent h 1 (source := some h.asEvent) (cause := some hulkCause)
      let h := g.object! hulk0.id
      g.dealDamageToPermanent h 2 (source := some h.asEvent) (cause := some hulkCause)
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
      let g := g.dealDamageToPermanent w 1 (source := some w.asEvent) (cause := some dmgCause)
      let w := g.object! dmgWatcher.id
      g.dealDamageToPermanent w 1 (source := some w.asEvent) (cause := some dmgCause)
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
      affectedPlayer := me, kind := .modifyCountersPut bTerm.id (some .plusOnePlusOne) (add := 1) (mult := 1) }
  let repDupB : ReplacementSpec :=
    { id := idAddCtr, source := some bTerm.id, controller := some me,
      affectedPlayer := me, kind := .modifyCountersPut bTerm.id (some .plusOnePlusOne) (add := 10) (mult := 1) }
  let repSecond : ReplacementSpec :=
    { id := idMulCtr, source := some bTerm.id, controller := some me,
      affectedPlayer := me, kind := .modifyCountersPut bTerm.id (some .plusOnePlusOne) (add := 0) (mult := 2) }
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
    | .rules (.zone (.moved before _ .battlefield .exile .exile _ _ _)) =>
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
      (source := some prevBear.asEvent) (cause := some prevCause)
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
      entersTapped := true
      otherFace := some dfcBackFace }
  let copyTemplateDef : CardDef :=
    { hero with name := "Template Hero", otherFace := some dfcBackFace }
  let gTier0 :=
    insertObject (quiet afterDraw) dfcFrontDef opp (.hand opp)
  let enterCardId :=
    ((gTier0.player opp).hand.filter (fun id => (gTier0.object! id).name == "Front Face Bear"))[0]!
  let idSelf : ReplacementId := { kind := .entersTappedSelf, object := some enterCardId }
  let idControl : ReplacementId := { kind := .entersUnderControl }
  let idCopy : ReplacementId := { kind := .entersAsCopy }
  let idBack : ReplacementId := { kind := .entersBackFaceUp }
  let idOther : ReplacementId := { kind := .entersWithExtraCounters }
  let specControl : ReplacementSpec :=
    { id := idControl, source := none, controller := some me,
      affectedPlayer := opp, kind := .entersUnderControl ⟨0⟩ me }
  let specCopy : ReplacementSpec :=
    { id := idCopy, source := none, controller := some me,
      affectedPlayer := me, kind := .entersAsCopy ⟨0⟩ copyTemplateDef }
  let specBack : ReplacementSpec :=
    { id := idBack, source := none, controller := some me,
      affectedPlayer := me, kind := .entersBackFaceUp ⟨0⟩ }
  let specOther : ReplacementSpec :=
    { id := idOther, source := none, controller := some me,
      affectedPlayer := me, kind := .entersWithExtraCounters ⟨0⟩ .plusOnePlusOne 2 }
  let gTier1 :=
    ((((gTier0.createEffect (.replacement specControl)).createEffect
        (.replacement specCopy)).createEffect
        (.replacement specBack)).createEffect
        (.replacement specOther)).change
      (.replacementOrder #[idOther, idBack, idCopy, idControl, idSelf])
  let etbBaseCause : EventCause := .oneShotEffect (some ⟨710⟩) none (some me)
  let enterCandidate : GameObject :=
    { (gTier1.object! enterCardId) with controller := some opp, defaultController := some opp }
  let etbRes :=
    gTier1.applyEtbReplacements enterCandidate (cause := some etbBaseCause)
  let (gTier2, enteredPermId) :=
    (quiet gTier1).putOntoBattlefield enterCardId opp (cause := some etbBaseCause)
  let enteredPerm := gTier2.object! enteredPermId
  etbRes.applied == #[idSelf, idControl, idCopy, idBack, idOther] &&
    enteredPerm.controller == some me &&
    enteredPerm.name == "Back Face Bear" &&
    enteredPerm.status.transformed &&
    enteredPerm.status.tapped &&
    enteredPerm.status.plusOnePlusOne == 2 &&
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
      affectedPlayer := opp, kind := .addNoncombatDamage ordBear.id 2 }
  let specMulDmg : ReplacementSpec :=
    { id := idMulDmg, source := some ordBear.id, controller := some me,
      affectedPlayer := opp, kind := .multiplyDamage ordBear.id 2 }
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
  let gActiveMe := { gOrd0 with activePlayer := me }
  let gActiveOpp := { gOrd0 with activePlayer := opp }
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
      affectedPlayer := opp, kind := .addNoncombatDamage fighterA.id 2 })
      (cause := some dmgOrdCause)).createEffect
      (.replacement {
        id := idFightMul, source := some fighterA.id, controller := some me,
        affectedPlayer := opp, kind := .multiplyDamage fighterA.id 2 })
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
      affectedPlayer := me, kind := .modifyCountersPut strikerId (some .plusOnePlusOne) (add := 1) (mult := 1) })
      (cause := some arwCause)).createEffect
      (.replacement {
        id := idCtrMul, source := some strikerId, controller := some me,
        affectedPlayer := me, kind := .modifyCountersPut strikerId (some .plusOnePlusOne) (add := 0) (mult := 2) })
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
    (({ quiet started with step := .draw, activePlayer := me }.createEffect
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
    { ((((gCbt0.recordPutCounters cbtBlk.id .shield 1 (some opp)
          (cause := some (.oneShotEffect (some ⟨720⟩) none (some opp)))).createEffect
        (.replacement {
          id := idCbtMul, source := none, controller := some me,
          affectedPlayer := opp, kind := .multiplyDamage ⟨0⟩ 2 })
        (cause := some drwSubCause)).createEffect
        (.replacement {
          id := idCbtLifeAdd, source := none, controller := some me,
          affectedPlayer := me, kind := .modifyLifeGain me 2 1 })
        (cause := some drwSubCause)).createEffect
        (.replacement {
          id := idCbtLifeMul, source := none, controller := some me,
          affectedPlayer := me, kind := .modifyLifeGain me 0 2 })
        (cause := some drwSubCause)).change (.replacementOrder #[idCbtMul]) with
      assignedCombatDamage := #[
        { source := cbtAtk1.id, toCreatures := #[], toPlayer := 2 },
        { source := cbtAtk2.id, toCreatures := #[(cbtBlk.id, 2)], toPlayer := 0 }
      ] }
  let gCbtPaused := (quiet gCbt1).dealAssignedCombatDamage
  let gCbtAfterLife :=
    (gCbtPaused.apply me (.chooseReplacement idCbtLifeAdd)).toOption.getD gCbtPaused
  let gCbtDone :=
    (gCbtAfterLife.apply opp (.chooseReplacement idCbtMul)).toOption.getD gCbtAfterLife
  let cbtLifelinkOrderOk :=
    gCbtPaused.pending == .chooseReplacement me #[idCbtLifeAdd, idCbtLifeMul] &&
    gCbtPaused.replacementOrder.isEmpty &&
    gCbtAfterLife.pending == .chooseReplacement opp #[idCbtBlkShield, idCbtMul] &&
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
    { (g0.registerDelayedTrigger {
        controller := me
        source := some h
        kind := .endStepSacrifice b.id
        cause := cause8 }) with step := .postcombatMain }
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
      | .permission p (.playFromExile oid _) _ => p == me && oid == exId
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
      #[((gCapLost.object! cap.id).asEvent, .player ⟨1⟩)] (cause := some c3)
  let gAtkLost := gCapLost.record atkEv
  -- Dwarf token created OR nontoken Dwarf moved onto battlefield while abilities are lost queues 0 triggers
  let (gEnterTokLost, _) := gCapLost.createToken me strikerDef (cause := some c3)
  let gEnterMoveLost := addPermanent gCapLost strikerDef me me
  -- Striker dealing combat damage to player or battle while DwarfCaptain lost abilities queues 0 triggers
  let strikeSnap := (gCapLost.object! striker.id).asEvent
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
        #[((gPostGrant.object! cap.id).asEvent, .player ⟨1⟩)] (cause := some c4))
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
    (({ gTrLost with assignedCombatDamage := #[{ source := atk.id, toPlayer := 2 }] }.dealAssignedCombatDamage).receivePriority me).resolveTop
  let gTrRe :=
    gTrLost.record (GameEvent.attached gTrLost.turnNumber (gTrLost.snapshot (gTrLost.object! cleaver.id)) atk.id (cause := c3))
  let gTrReCombat :=
    (({ gTrRe with assignedCombatDamage := #[{ source := atk.id, toPlayer := 2 }] }.dealAssignedCombatDamage).receivePriority me).resolveTop
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
  let gRawNone := { g0 with objects := g0.objects.map (fun (o : GameObject) => if o.id == b.id then { o with controller := none } else o) }
  let gRawMe := { g0 with objects := g0.objects.map (fun (o : GameObject) => if o.id == b.id then { o with controller := some me } else o) }
  let gOppLost := gRawNone.record (GameEvent.playerLost gRawNone.turnNumber opp .conceded)
  let initCtrlOk :=
    gRawNone.controllerOf (gRawNone.object! b.id) == some opp &&
    gRawMe.controllerOf (gRawMe.object! b.id) == some opp &&
    gOppLost.controllerOf (gOppLost.object! b.id) == none
  -- Face-down permanent copied via `becomeCopyOf` and `copyBattlefieldPermanent`
  let gFd := setFaceDown g0 m.id true
  let gCopied := gFd.becomeCopyOf (gFd.object! cl.id) (gFd.object! m.id) (untilEot := true)
  let (gTok, tok) := gCopied.copyBattlefieldPermanent (gCopied.object! m.id) me
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
  let gUntapCleared :=
    { gArr with
      objects := gArr.objects.map fun (obj : GameObject) =>
        if obj.id == arrId then { obj with status := { obj.status with summoningSick := false } }
        else obj }
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
      g.dealDamageToPermanent target 1 (source := some target.asEvent) (cause := some cause1)
  let gDmgAnim :=
    gLayered.withBatch (some cause1) fun g =>
      let target := g.object! relic.id
      g.dealDamageToPermanent target 1 (source := some target.asEvent) (cause := some cause1)
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
      | .rules (.player (.gainedDesignation p .enduringStory)) => p == me && e.batch.raw > 0
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
  let gDtReg := { ((gDt0.registerDelayedTrigger dtOneShot).registerDelayedTrigger dtUntilEot) with step := .postcombatMain }
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
        kind := .entersAsCopy ⟨0⟩ foodTemplate
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
      kind := .entersAsCopy ⟨0⟩ dfcNontokenTemplate
    } .untilEndOfTurn))
  let (gTokCopy1a, _) := gTokCopy0.createOneToken me humanSoldierToken
  let gTokCopy1 := applyIdle (applyIdle gTokCopy1a)
  let placedTokCopied := (gTokCopy1.battlefield.filter (·.name == "Phase11 Siege Front"))[0]!
  let gTokBack0 := quiet (gTokCopy0.createEffect
    (.replacement {
      id := { kind := .entersBackFaceUp }
      affectedPlayer := me
      kind := .entersBackFaceUp ⟨0⟩
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
  let crewPreEv := gCrew0.events.size
  let gCrewAsk := mustApply gCrew0 me (.activate boatId 0)
  let gCrewDec := mustApply gCrewAsk me .decline
  let crewRevOk :=
    gCrewDec.stack.isEmpty &&
    gCrewDec.nextObjectId == gCrew0.nextObjectId &&
    (gCrewDec.events.extract crewPreEv gCrewDec.events.size).all
      (fun e => match e.change with | .engine (.logMsg _) => true | _ => false) &&
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
  let zemoPreEv := gZemo0.events.size
  let gZemoAsk := mustApply gZemo0 me (.activate zemoId 0)
  let gZemoDec := mustApply gZemoAsk me .decline
  let zemoRevOk :=
    gZemoDec.stack.isEmpty &&
    gZemoDec.nextObjectId == gZemo0.nextObjectId &&
    (gZemoDec.events.extract zemoPreEv gZemoDec.events.size).all
      (fun e => match e.change with | .engine (.logMsg _) => true | _ => false) &&
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
      (.replacement { id := { kind := .entersAsCopy }, affectedPlayer := me, kind := .entersAsCopy ⟨0⟩ blackGateDef } .untilEndOfTurn)
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
                      affectedPlayer := me, kind := .multiplyDamage pid 2 } .untilEndOfTurn)
    g.createEffect
      (.replacement { id := { kind := .addNoncombatDamage, object := some pid, player := some me, grantor := some ⟨9002⟩ },
                      affectedPlayer := me, kind := .addNoncombatDamage pid 1 } .untilEndOfTurn)
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
  -- (c) Doom Reigns `pendingCastExiledQueue`: reversing a paused first exiled cast advances to second!
  let gQueueRev :=
    let g := insertObject (insertObject afterDraw modalKickerDef me .exile) freeDrawDef me .exile
    let exSac := (g.objects.filter (fun o => o.name == "Phase13 Modal Kicker" && o.zone == .exile))[0]!.id
    let exDraw := (g.objects.filter (fun o => o.name == "Phase13 Free Draw" && o.zone == .exile))[0]!.id
    let g := (g.change (.pushContinuationFrame {})).change (.pendingCastExiledQueue (some (me, #[exDraw])))
    let gPaused := g.castAsPartOfResolution me exSac
    let gMode := mustApply gPaused me (.chooseMode 0)
    let gKick := mustApply gMode me (.announceKicker true)
    (mustApply gKick me .pay, exSac, exDraw)
  let queueContOk :=
    gQueueRev.1.pendingCastExiledQueue.isNone &&
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
                      affectedPlayer := me, kind := .modifyCountersPut sid none (add := 1) (mult := 1) } .untilEndOfTurn)
    g.createEffect
      (.replacement { id := { kind := .multiplyCountersPut, object := some sid, grantor := some ⟨8890⟩ },
                      affectedPlayer := me, kind := .modifyCountersPut sid none (add := 0) (mult := 2) } .untilEndOfTurn)
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
      | .rules (.permanent (.counters (.object snap) .lore (.put 1) _)), some (.replaced ..) =>
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
  -- Stack has [original, trig1, trig2]: resolve trig2 -> copy1, resolve copy1, resolve trig1 -> copy2, resolve copy2, resolve original!
  let gDtResolved := gDtCast.resolveTop.resolveTop.resolveTop.resolveTop.resolveTop
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
                      affectedPlayer := opp, kind := .addNoncombatDamage ⟨0⟩ 1 } .untilEndOfTurn)
    let g := g.createEffect
      (.replacement { id := { kind := .equippedDealsDoubleDamage, grantor := some ⟨8992⟩ },
                      affectedPlayer := opp, kind := .multiplyDamage ⟨0⟩ 2 } .untilEndOfTurn)
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
                      affectedPlayer := ⟨1⟩, kind := .addNoncombatDamage ⟨0⟩ 1 } .untilEndOfTurn)
    let g := g.createEffect
      (.replacement { id := { kind := .equippedDealsDoubleDamage, grantor := some ⟨8994⟩ },
                      affectedPlayer := ⟨1⟩, kind := .multiplyDamage ⟨0⟩ 2 } .untilEndOfTurn)
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
  -- `pendingCastExiledQueue`, or an outer `pendingReplacement` is open:
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
  -- (c) Exile-cast queue (`castExiledAsResolves`) + `triggerSequenceRest` across a spell
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
    let g := (mkSeqFrame g 4).change (.pendingCastExiledQueue (some (me, #[exSac, exDraw])))
    let g := g.advanceCastExiledQueue
    let g := mustApply g me .pay
    let gPaused := mustApply g me (.sacrifice sacBearId)
    let gDone := mustApply gPaused me (.chooseReplacement idHead)
    (gPaused, gDone)
  let queueSpellRepOk :=
    (match gQueueSpellPaused.pending with | .chooseReplacement p cs => p == me && cs.size == 2 | _ => false) &&
    gQueueSpellDone.pending == .none &&
    gQueueSpellDone.pendingCastExiledQueue.isNone &&
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
      affectedPlayer := me, kind := .addNoncombatDamage landId 2
    }) (cause := some testCause)).createEffect (.replacement {
      id := idMulMe, source := some oppBearId, controller := some opp,
      affectedPlayer := me, kind := .multiplyDamage landId 2
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
    let gP1 := g.payCostPickItems me b1 b1 .sacrificeArtifactOrCreature #[b1, b2]
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
    let ev := GameEvent.moved 1 { id := some ⟨42⟩, owner := me } (.hand me) (.graveyard me)
      (discarded := true) (cause := testCause)
    match (ev.withDestination .exile false).change with
    | .rules (.zone (.moved _ _ (.hand _) .exile ZoneVerb.discard _ _ _)) => true
    | _ => false
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
        affectedPlayer := me, kind := .multiplyDamage atkId 2
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
  let (gDtFizzle, dtFizzleOk) :=
    let g0 := addPermanent afterDraw bear me me
    let bId := (g0.battlefield.filter (fun (o : GameObject) => o.name == "Event Bear"))[0]!.id
    let g1 := g0.attackPumpPerPlains me
    let regOk := g1.delayedTriggers.any (fun (dt : DelayedTrigger) => dt.kind == DelayedTriggerKind.attackPumpPerPlains)
    let g2 := g1.record (GameEvent.attackersDeclared g1.turnNumber me #[(g1.snapshot (g1.object! bId), .player opp)])
    let g2 := g2.receivePriority me
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
    (g5, regOk && fizzled)
  let (gReflFizzle, reflFizzleOk) :=
    let g0 := addPermanent (addPermanent afterDraw planDef14 me me) bear opp opp
    let planId := (g0.battlefield.filter (fun (o : GameObject) => o.name == "Phase14 Plan"))[0]!.id
    let bId := (g0.battlefield.filter (fun (o : GameObject) => o.name == "Event Bear" && o.controller == some opp))[0]!.id
    let g1 := mustApply (g0.queueModeledReflexive me (some planId) 10) me
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
    [gSimDies, gDtFizzle, gReflFizzle, gFlickerIso].all (fun g =>
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

  let mustHold14 (label : String) (ok : Bool) : Bool :=
    if ok then true else panic! s!"Phase 14 guard failed: {label}"
  [ mustHold14 "painLandBracketOk" painLandBracketOk,
    mustHold14 "costPickAndLoyaltyOk" costPickAndLoyaltyOk,
    mustHold14 "irrevProposalEventsOk" irrevProposalEventsOk,
    mustHold14 "morphAndResCastOk" morphAndResCastOk,
    mustHold14 "singleWriterAndMirrorOk" singleWriterAndMirrorOk,
    mustHold14 "combatDmgAndShieldPwOk" combatDmgAndShieldPwOk,
    mustHold14 "batchLookbackAndFlickerOk" batchLookbackAndFlickerOk,
    mustHold14 "concedeCleanupOk" concedeCleanupOk ].all id

end Mtg.Engine.EventTests
