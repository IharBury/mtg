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
    { id := some ⟨4⟩, controller := some me, owner := me, types := #[.artifact] } .stack .battlefield
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
    { id := some ⟨7⟩, controller := some me, owner := me, types := #[.creature] } .battlefield (.graveyard me)
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
  let g := g.changeStatus h.id (.untilEotExileIfDies true)
  let (g, id) := g.move h.id (.graveyard me) none
  let replaced :=
    (g.object! id).zone == .exile &&
      match g.events.back? with
      | some e => !e.isCreatureToGraveyard &&
          match e.change with
          | .rules (.zone (.moved _ _ _ .exile _ _ _ _)) => true
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
  let g1 := (g0.applyChange (.rules (.effectCreated ⟨100⟩ pump))).applyChange (.rules (.effectCreated ⟨101⟩ kw))
  let applied :=
    (g1.object! b.id).status.pump == (3, 3) &&
      (g1.object! b.id).status.untilEotKeywords == Keyword.trample
  let g2 := (g1.applyChange (.rules (.effectExpired ⟨100⟩ pump))).applyChange (.rules (.effectExpired ⟨101⟩ kw))
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
        (cause := some (.turnBased .declareAttackers))))
  let nonOneShotDidNotAdvance :=
    gNonOneShot.nextEffectId == effId0 &&
      (GameEvent.oneShotEffectsWithId gNonOneShot.events).isEmpty
  let g1 := g0.draw me 1 (cause := some (.turnBased .drawStepDraw))
  let g2 := g1.gainLife me 3 (cause := some (.turnBased .cleanupClear))
  let g3 := g2.loseLife me 2 (cause := some (.costPayment .life me))
  let g4 := g3.record (GameEvent.counters g3.turnNumber (some me) b.asEvent .plusOnePlusOne 2 false
    (cause := some (.costPayment .removeCounters me)))
  let g5 := g4.record (GameEvent.tapped g4.turnNumber b.asEvent true true
    (cause := some (.costPayment .tap me)))
  let g6 := g5.record (GameEvent.untapped g5.turnNumber b.asEvent false
    (cause := some (.turnBased .untapAll)))
  let g7 := g6.withResolvingContext (some b.id) me (fun g => g.createTreasureTokens me 1)
  let g8 := ((g7.record (GameEvent.looked g7.turnNumber me 2)).record
    (GameEvent.resolved g7.turnNumber me 1)).record
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
    g1.nextEffectId == effIdBefore + 2 &&
    createdPairs.size == 2 &&
    appliedPairsBeforeToken.isEmpty &&
    appliedPairs.size == 2 &&
    allDistinct &&
    expiredPairs == createdPairs &&
    (g3.object! b.id).status.pump == (0, 0) &&
    g3.activeEffects.all (fun (_, e) =>
      match e with
      | .pump id _ _ => id != b.id
      | _ => true)

def opp : PlayerId := ⟨1⟩

/-- Active control-changing effects on `id`. -/
def controlEffectsOn (g : Game) (id : ObjectId) : Array (EffectId × ContinuousEffect) :=
  g.activeEffects.filter (fun (_, e) =>
    match e with
    | .control oid _ _ _ _ => oid == id
    | _ => false)

/- Rule 611 / 613.7: expiration removes only the entry recorded under its
`EffectId`, and an id that is not active rolls nothing back. -/
#guard
  let g0 := addPermanent (quiet afterDraw) bear me me
  let b := (g0.battlefield.filter (·.name == "Event Bear"))[0]!
  let pump := ContinuousEffect.pump b.id 3 3
  let g1 := (g0.applyChange (.rules (.effectCreated ⟨100⟩ pump))).applyChange (.rules (.effectCreated ⟨101⟩ pump))
  let g2 := g1.applyChange (.rules (.effectExpired ⟨101⟩ pump))
  let g3 := g2.applyChange (.rules (.effectExpired ⟨999⟩ pump))
  (g1.object! b.id).status.pump == (6, 6) &&
    (g2.object! b.id).status.pump == (3, 3) &&
    g2.activeEffects.map Prod.fst == #[⟨100⟩] &&
    (g3.object! b.id).status.pump == (3, 3) &&
    g3.activeEffects.map Prod.fst == #[⟨100⟩] &&
    g3.nextEffectId == g2.nextEffectId

/- Expiring an effect that is not active records nothing and rolls nothing
back, even when the status flag was set some other way. -/
#guard
  let g0 := quiet (addPermanent afterDraw bear me me)
  let b := (g0.battlefield.filter (·.name == "Event Bear"))[0]!
  let g0 := quiet (g0.changeStatus b.id (.cantBlockUntilEot true))
  let g1 := g0.expireEffect (.cantBlockUntilEot b.id)
  g1.events.size == g0.events.size &&
    g1.nextEffectId == g0.nextEffectId &&
    (g1.object! b.id).status.cantBlockUntilEot

/- Expiring one until-end-of-turn keyword grant removes only that grant's
keywords; another grant on the same creature keeps applying. -/
#guard
  let g0 := quiet (addPermanent afterDraw bear me me)
  let b := (g0.battlefield.filter (·.name == "Event Bear"))[0]!
  let g1 := (g0.createEffect (.keywordsUntilEot b.id Keyword.flying)).createEffect
    (.keywordsUntilEot b.id Keyword.haste)
  let g2 := g1.expireEffect (.keywordsUntilEot b.id Keyword.flying)
  (g1.object! b.id).status.untilEotKeywords == Keywords.merge Keyword.flying Keyword.haste &&
    (g2.object! b.id).status.untilEotKeywords == Keyword.haste

/- A flag set by two continuous effects stays set until both have ended. A
second "loses all abilities" keeps the printed static abilities off. -/
#guard
  let lordDef : CardDef :=
    { bear with
      name := "Bear Lord"
      staticAbilities := #[.fra .creaturesYouControlHaveTrample] }
  let g0 := quiet (addPermanent afterDraw lordDef me me)
  let lord := (g0.battlefield.filter (·.name == "Bear Lord"))[0]!
  let staticEff := ContinuousEffect.staticAbility lord.id (.fra .creaturesYouControlHaveTrample)
  let g1 := (g0.createEffect (.cantBlockUntilEot lord.id)).createEffect (.cantBlockUntilEot lord.id)
  let g2 := g1.expireEffect (.cantBlockUntilEot lord.id)
  let g3 := g2.expireEffect (.cantBlockUntilEot lord.id)
  let g4 := (quiet ((g3.createEffect (.losesAbilitiesUntilEot lord.id)).createEffect
    (.losesAbilitiesUntilEot lord.id))).expireEffect (.losesAbilitiesUntilEot lord.id)
  (g2.object! lord.id).status.cantBlockUntilEot &&
    !(g3.object! lord.id).status.cantBlockUntilEot &&
    (g4.object! lord.id).status.losesAbilitiesUntilEot &&
    !(GameEvent.createdEffects g4.events).contains staticEff &&
    !g4.hasActiveEffect staticEff

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
    (g3.object! b.id).controlledBy me &&
    (controlEffectsOn g3 b.id).map Prod.fst == #[mindControlId] &&
    (g3.object! b.id).controlUntilSourceLeaves == some h.id &&
    (g4.object! b.id).controlledBy opp &&
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
  (g2.object! b.id).status.controlUntilEot &&
    (controlEffectsOn g3 b.id).size == 1 &&
    (g3.object! b.id).controlledBy me &&
    (g4.object! b.id).controlledBy opp &&
    (controlEffectsOn g4 b.id).isEmpty

/- A control effect lasting a number of its controller's turns counts down
under its own `EffectId` (Evil's Thrall). -/
#guard
  let g0 := quiet (addPermanent afterDraw bear opp opp)
  let b := (g0.battlefield.filter (·.name == "Event Bear"))[0]!
  let g1 := g0.changeControl b me (turnEndsLeft := 2)
  let eid := (controlEffectsOn g1 b.id)[0]!.1
  let g2 := (quiet g1).clearEOT
  let counted :=
    match g2.activeEffect? eid with
    | some (.control _ _ _ n _) => n == 1
    | _ => false
  counted &&
    (g2.object! b.id).controlledBy me &&
    (g2.object! b.id).status.controlTurnEndsLeft == 1 &&
    (GameEvent.expiredEffects g2.events).isEmpty

/- Cleanup does not look up a permanent that ending a control effect exiled
(CR 800.4c). -/
#guard
  let g0 := quiet (addPermanent afterDraw bear opp opp)
  let b := (g0.battlefield.filter (·.name == "Event Bear"))[0]!
  let g1 := (g0.changeControl b me (untilEot := true)).changePlayer opp (.lost true)
  let g2 := (quiet g1).clearEOT
  (g2.findObject? b.id).isNone &&
    g2.objects.any (fun o => o.name == "Event Bear" && o.zone == .exile)

/- Loki leaving keeps his pending copy effect under the same `EffectId` with
his last known power, and the end of turn expires that same id (MSH 109). -/
#guard
  let g0 := quiet (addPermanent afterDraw bear me me)
  let b := (g0.battlefield.filter (·.name == "Event Bear"))[0]!
  let g1 := g0.createEffect (.pendingLokiCopy me (some b.id) 2)
  let eid := (GameEvent.createdEffectsWithId g1.events)[0]!.1
  let (g2, _) := g1.move b.id (.graveyard me) none
  let updated :=
    match g2.activeEffect? eid with
    | some (.pendingLokiCopy p none _) => p == me
    | _ => false
  let g3 := (quiet g2).clearTurnActivations
  updated &&
    (match g2.pendingLokiCopy with
      | some (_, none, _) => true
      | _ => false) &&
    (GameEvent.expiredEffectsWithId g3.events).map Prod.fst == #[eid] &&
    g3.pendingLokiCopy.isNone

/- Multiple pending Loki copies: an opponent's later effect does not hide
yours, and copying your spell expires only your matching effect (MSH 109). -/
#guard
  let g0 := quiet (addPermanent afterDraw bear me me)
  let b := (g0.battlefield.filter (·.name == "Event Bear"))[0]!
  let g1 := g0.createEffect (.pendingLokiCopy me (some b.id) 2)
  let eidMe := (GameEvent.createdEffectsWithId g1.events)[0]!.1
  let g2 := (quiet g1).createEffect (.pendingLokiCopy opp none 2)
  let eidOpp := (GameEvent.createdEffectsWithId g2.events)[0]!.1
  let (g3, spell) := (quiet g2).allocObject lightningBolt me .stack (some me)
  let g3 := g3.putStackEntry me spell.id
  let g4 := g3.putCastTriggersOnStack me (g3.object! spell.id)
  let copies := g4.objects.filter (fun o =>
    o.zone == .stack && o.isCopy && o.printed.name == "Lightning Bolt")
  copies.size == 1 &&
    (GameEvent.expiredEffectsWithId g4.events).map Prod.fst == #[eidMe] &&
    (g4.activeEffect? eidOpp).isSome &&
    g4.pendingLokiCopy == some (opp, none, 2)

/- Two pending Loki copies for the same player both see the next matching
cast: each copies the spell and ends. One whose power is too low stays
pending (MSH 109). -/
#guard
  let g0 := quiet afterDraw
  let g1 := ((g0.createEffect (.pendingLokiCopy me none 2)).createEffect
    (.pendingLokiCopy me none 3)).createEffect (.pendingLokiCopy me none 0)
  let ids := (GameEvent.createdEffectsWithId g1.events).map Prod.fst
  let (g2, spell) := (quiet g1).allocObject lightningBolt me .stack (some me)
  let g2 := g2.putStackEntry me spell.id
  let g3 := g2.putCastTriggersOnStack me (g2.object! spell.id)
  let copies := g3.objects.filter (fun o =>
    o.zone == .stack && o.isCopy && o.printed.name == "Lightning Bolt")
  ids.size == 3 &&
    copies.size == 2 &&
    (GameEvent.expiredEffectsWithId g3.events).map Prod.fst == #[ids[0]!, ids[1]!] &&
    (g3.activeEffect? ids[2]!).isSome

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
  (g2.object! b.id).name == "Event Giant" &&
    (g2.object! b.id).copyUntilEot &&
    (g3.object! b.id).name == "Event Hero" &&
    !((g3.object! b.id).copyUntilEot) &&
    (g3.object! b.id).copyUntilSourceLeaves == some h.id &&
    ((g3.object! b.id).copyRestore.map CardDef.name) == some "Event Bear" &&
    (g4.object! b.id).name == "Event Bear" &&
    (g4.object! b.id).copyRestore.isNone &&
    (g4.object! b.id).copyUntilSourceLeaves.isNone

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
  let g0 := insertObject g0 impDef me (.hand me) none {} (fun id _ => #[.pushHand id])
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
        let g3 := g2.changeStatus permId .withoutCounters
        let g4 := g3.changeStatus permId (.addCountersExceptPlusOne { time := 2 })
        let created4 := (GameEvent.createdEffectsWithId g4.events).filter (fun (id, e) =>
          id != eid1 && e == .notACreature permId)
        let g5 := (g4.changeStatus copyId (.addCountersExceptPlusOne { time := 2 })).beginStep .end
        (GameEvent.createdEffectsWithId g1.events).isEmpty &&
          (g1.object! spellId).isCreature &&
          !(g2.object! permId).kicked &&
          g2.loggedCastForImpending permId &&
          !g2.loggedCastForImpending copyId &&
          g2.activeEffect? eid1 == some (.notACreature permId) &&
          !(g2.object! permId).isCreature &&
          (GameEvent.expiredEffectsWithId g3.events).map Prod.fst == #[eid1] &&
          (g3.activeEffect? eid1).isNone &&
          (g3.object! permId).isCreature &&
          created4.size == 1 &&
          g4.activeEffect? created4[0]!.1 == some (.notACreature permId) &&
          !(g4.object! permId).isCreature &&
          (g5.object! permId).status.time == 1 &&
          (g5.object! copyId).isCreature &&
          (g5.object! copyId).status.time == 2

/- Phase 1 isolation: applying a single `PermanentEvent.tapped` or
`PermanentEvent.untapped` event yields the exact tapped state without separate
status setters (CR 701.26a / 701.26b). -/
#guard
  let g0 := quiet (addPermanent afterDraw bear me me)
  let b := (g0.battlefield.filter (·.name == "Event Bear"))[0]!
  let g1 := g0.applyChange (.rules (.permanent (.tapped b.asEvent true)))
  let g2 := g1.applyChange (.rules (.permanent (.untapped b.asEvent)))
  (g1.object! b.id).status == { b.status with tapped := true, becameTappedThisTurn := true } &&
    (g2.object! b.id).status == { b.status with tapped := false, becameTappedThisTurn := true }

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
  (g1.object! b.id).status == { b.status with plusOnePlusOne := 3, gotPlusOneThisTurn := true } &&
    (g2.object! b.id).status == { b.status with plusOnePlusOne := 2, gotPlusOneThisTurn := true } &&
    (g3.player me) == { (g0.player me) with poison := 4 } &&
    (g4.player me) == { (g0.player me) with poison := 3 } &&
    (g5.object! b.id).status == { b.status with plusOnePlusOne := 2, gotPlusOneThisTurn := true, poison := 2 } &&
    (g6.object! b.id).status == { b.status with plusOnePlusOne := 2, gotPlusOneThisTurn := true, poison := 1 } &&
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
  let gDealtOnly := g0.record (GameEvent.damaged g0.turnNumber dtSource b.asEvent 1 false)
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
`PermanentEvent.controlChanged`, and `PermanentEvent.designation (.goaded byPlayer)`
updates `attachedTo`, `controller`, `controlChanged`, `goaded`, and `goadedBy`
in isolation (CR 701.3 / 110.2 / 701.15b). -/
#guard
  let g0 := quiet (addPermanent (addPermanent afterDraw bear me me) hero me me)
  let b := (g0.battlefield.filter (·.name == "Event Bear"))[0]!
  let h := (g0.battlefield.filter (·.name == "Event Hero"))[0]!
  let g1 := g0.applyChange (.rules (.permanent (.attached h.asEvent b.id none)))
  let g2 := g1.applyChange (.rules (.permanent (.unattached h.asEvent b.id)))
  let g3 := g2.applyChange (.rules (.permanent (.controlChanged b.asEvent me opp)))
  let g4 := g3.applyChange (.rules (.permanent (.controlChanged b.asEvent opp me)))
  let g5 := g4.applyChange (.rules (.permanent (.designation b.asEvent (.goaded me) true)))
  let g6 := g5.applyChange (.rules (.permanent (.designation b.asEvent (.goaded opp) true)))
  let g7 := g6.expireGoadedFor me
  let g8 := g7.expireGoadedFor opp
  let heroToPlayer := GameEvent.damagedPlayer 1 h.asEvent opp 2 true
  let bearToHero := GameEvent.damaged 1 b.asEvent h.asEvent 2 false
  (g1.object! h.id) == { h with attachedTo := some b.id } &&
    (g2.object! h.id) == { h with attachedTo := none } &&
    (g3.object! b.id) == { b with controller := some opp, controlChanged := true } &&
    (g4.object! b.id) == { b with controller := some me, controlChanged := false } &&
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
      .stack .battlefield).matchesTrigger me b.id .anotherCreatureYouControlEnters

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
  let g0 := insertObject (quiet afterDraw) tapPlusCreature me (.hand me) none {} (fun id _ => #[.pushHand id])
  let g0 := insertObject g0 testPlaneswalker me (.hand me) none {} (fun id _ => #[.pushHand id])
  let g0 := insertObject g0 testSaga me (.hand me) none {} (fun id _ => #[.pushHand id])
  let g0 := insertObject g0 testImpending me .stack (some me) { time := 3 } (fun _ _ => #[])
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
replaced by exile (CR 614.6) is journaled with `verb == .exile` rather than
`.sacrifice`. -/
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
      | .rules (.zone (.moved before _ .battlefield .exile .exile _ _ _)) =>
        before.id == some tok.id
      | _ => false) &&
    !g5.events.any (fun e =>
      match e.change with
      | .rules (.zone (.moved _ _ .battlefield _ .sacrifice _ _ _)) => true
      | _ => false)

/- Phase 2 isolation: `ZoneEvent.moved` and `ZoneEvent.created` are the sole
writers of the objects they install (preserving full `printed` `CardDef`,
`summoningSick`, `attackingWhom`, `returnedAsArtifact`, `onlyFoodArtifact`,
`wasCast`, and stack-copy metadata), with zero `EngineChange.setObject`
events. -/
#guard
  let g0 := insertObject (quiet afterDraw) bear me (.hand me) none {} (fun id _ => #[.pushHand id])
  let cid := ((g0.player me).hand.filter (fun id => (g0.object! id).name == "Event Bear"))[0]!
  let (g1, permId) := (quiet g0).putOntoBattlefield cid me
    (tapped := true) (summoningSick := false)
    (attacking := true) (attackingWhom := some opp)
    (returnedAsArtifact := true) (onlyFoodArtifact := true) (wasCast := some true)
  let (g2, tok) := (quiet g1).createToken me treasureToken
    (tapped := true) (attacking := true) (attackingWhom := some opp)
  let hasSetObject (evs : Array GameEvent) : Bool :=
    evs.any (fun e =>
      match e.change with
      | .engine (.setObject _) => true
      | _ => false)
  let perm := g1.object! permId
  !hasSetObject g1.events &&
    !hasSetObject g2.events &&
    perm.status.tapped &&
    !perm.status.summoningSick &&
    perm.status.attacking &&
    perm.status.attackingWhom == some opp &&
    perm.status.returnedAsArtifact &&
    perm.status.onlyFoodArtifact &&
    perm.wasCast &&
    perm.printed == bear &&
    tok.printed.activatedAbilities.size == treasureToken.activatedAbilities.size &&
    tok.status.attacking &&
    tok.status.attackingWhom == some opp

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
701.62 / 702.26 / 704.5a–c). -/
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
    (cause := some (.oneShotEffect ⟨g3.nextEffectId⟩ (some b.id) (some me))))
  let g5 := g4.record (GameEvent.resolved g4.turnNumber me 1)
  let gPump := (quiet g0).withResolvingContext (some b.id) me (fun g =>
    g.createEffect (.pump b.id 2 2))
  let gCleanup := ((quiet gPump).clearEOT).clearTurnActivations
  let gBeholdEff := ((quiet g0).becomeTapped (g0.object! b.id)
    (cause := some (.oneShotEffect ⟨g0.nextEffectId⟩ (some b.id) (some me)))).beholdAndMaybeUntap me b.id .bear
  let gScry0 := (quiet afterDraw).beginScry me 2
  let looked := gScry0.scryLookedIds me 2
  let topChoice := #[looked[0]!]
  let botChoice := #[looked[1]!]
  let gScryDone :=
    match gScry0.finishScry me topChoice botChoice with
    | .ok g => g
    | .error _ => gScry0
  let libAfter := (gScryDone.player me).library
  let gMana := ((quiet afterDraw).changePlayer me (.addMana (.colored .red) 2)).emptyManaPools
  let gCombat := ((quiet g0).changeStatus b.id (.attacking true)).clearCombat
  g1.qualityWasBeheld me .bear &&
    (g1.player me).beheldQualities == #[.bear] &&
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
        e.cause == .costPayment .behold me (some b.id)) &&
    g2.events.any (fun e =>
      match e.change with
      | .rules (.permanent (.phasedOut o false)) => o.id == some b.id && e.cause == .turnBased .phaseInOut
      | _ => false) &&
    g3.events.any (fun e =>
      match e.change with
      | .rules (.permanent (.phasedIn o false)) => o.id == some b.id && e.cause == .turnBased .phaseInOut
      | _ => false) &&
    gPump.events.any (fun e =>
      match e.change, e.cause with
      | .rules (.effectCreated _ (.pump id 2 2)), .oneShotEffect _ (some sid) (some ctrl) =>
        id == b.id && sid == b.id && ctrl == me
      | _, _ => false) &&
    gCleanup.events.any (fun e =>
      match e.change with
      | .rules (.effectExpired _ (.pump id 2 2)) =>
        id == b.id && e.cause == .turnBased .cleanupClear
      | _ => false) &&
    gBeholdEff.events.any (fun e =>
      match e.change, e.cause with
      | .rules (.player (.beheld p .bear)), .oneShotEffect _ _ (some ctrl) =>
        p == me && ctrl == me
      | _, _ => false) &&
    gScryDone.events.any (fun e =>
      match e.change with
      | .rules (.player (.scried p top bottom 2 2)) =>
        p == me && top == topChoice && bottom == botChoice
      | _ => false) &&
    gMana.events.any (fun e =>
      e.change == .rules (.player (.manaEmptied me 2 false)) &&
        e.cause == .turnBased .emptyManaPools) &&
    (gMana.player me).manaPool.isEmpty &&
    gCombat.events.any (fun e =>
      match e.change with
      | .rules (.permanent (.removedFromCombat o)) =>
        o.id == some b.id && e.cause == .turnBased .removeFromCombatAtEndOfCombat
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
    (g0.changePlayer me (.library oneCard)).withResolvingContext (some h.id) opp (fun g =>
      g.beginScry me 3)
  let gScryOneDone :=
    match gScryOne.finishScry me oneCard #[] with
    | .ok g => g
    | .error _ => gScryOne
  let gProlif0 :=
    ((quiet g0).changeStatus b.id (.addCounters .stun 1)).change
      (.pending (.chooseProliferate me 1))
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
      | .rules (.zone (.moved _ _ .battlefield .exile ..)) => some e.cause
      | _ => none)
  let gReturned := (quiet gBlink).beginStep .end
  let returnCause? : Option EventCause :=
    gReturned.events.findSome? (fun e =>
      match e.change with
      | .rules (.zone (.moved _ _ .exile .battlefield ..)) => some e.cause
      | _ => none)
  let gAssign :=
    match ((quiet g0).changeStatus b.id (.attacking true)).storeCombatAssignments true #[] with
    | .ok g => g
    | .error _ => g0
  gScryOneDone.events.any (fun e =>
    match e.change, e.cause with
    | .rules (.player (.scried p top bottom 1 3)), .oneShotEffect _ (some sid) (some ctrl) =>
      p == me && top == oneCard && bottom.isEmpty && sid == h.id && ctrl == opp
    | _, _ => false) &&
  gProlifDone.events.any (fun e =>
    match e.change, e.cause with
    | .rules (.permanent (.counters (.object o) .stun (.put 1) (some actor))),
      .oneShotEffect _ _ (some ctrl) =>
      o.id == some b.id && actor == me && ctrl == me
    | _, _ => false) &&
  (match exileCause?, returnCause? with
   | some (.oneShotEffect id1 (some sid1) (some ctrl1)),
     some (.oneShotEffect id2 (some sid2) (some ctrl2)) =>
     id1 == id2 && sid1 == h.id && sid2 == h.id && ctrl1 == me && ctrl2 == me
   | _, _ => false) &&
  gAssign.events.any (fun e =>
    match e.change with
    | .rules (.damage (.combatAssigned true _)) =>
      e.cause == .turnBased (.assignCombatDamage false)
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
    (quiet gLink1).withResolvingContext (some b.id) opp (fun g =>
      (g.move h.id (.graveyard me) none).1)
  let linkReturnCause? : Option EventCause :=
    gLinkReturn.events.findSome? (fun e =>
      match e.change with
      | .rules (.zone (.moved _ _ .exile .battlefield ..)) => some e.cause
      | _ => none)
  let gLoki0 := g0.createEffect (.pendingLokiCopy me (some h.id) 3)
    (cause := some (.oneShotEffect ⟨g0.nextEffectId⟩ (some h.id) (some me)))
  let destroyCause := EventCause.oneShotEffect ⟨gLoki0.nextEffectId⟩ (some b.id) (some opp)
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
    (addPermanent gZemo0 zemoDef me me).change (.step .declareAttackers)
  let z := (gZemo1.battlefield.filter (·.name == "Baron Helmut Zemo"))[0]!
  let gZemo2 :=
    quiet (gZemo1.changeStatuses z.id #[.attacking true, .declaredAsAttackerThisTurn true])
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
    gLokiLeft.events.any (fun e =>
      match e.change with
      | .rules (.effectUpdated _ (.pendingLokiCopy _ none _)) => e.cause == destroyCause
      | _ => false) &&
    gPermStack.events.any (fun e =>
      match e.change with
      | .rules (.zone (.moved _ _ .stack .battlefield ..)) =>
        e.cause == EventCause.gameRule .permanentSpellResolved
      | _ => false) &&
    !gCrewDeclined.events.any (fun e =>
      match e.change with
      | .rules (.activated ..) => true
      | _ => false) &&
    gCrewDeclined.events.any (fun e =>
      match e.change with
      | .rules (.zone (.ceasedToExist o)) =>
        o.zone == .stack && e.cause == EventCause.gameRule .reversedActivation
      | _ => false) &&
    gZemoAccepted.events.any (fun e =>
      match e.change, e.cause with
      | .rules (.zone (.moved _ _ (.graveyard _) .exile ..)), .costPayment .exile payer (some _) =>
        payer == me
      | _, _ => false) &&
    gZemoAccepted.events.any (fun e =>
      match e.change with
      | .rules (.activated ..) => e.cause == EventCause.gameRule .abilityActivated
      | _ => false)

/- Phase 3: `GameEvent.activated`, loyalty counter costs, and loyalty activation
triggers only fire when activation cost payment completes (`becomeActivated`,
CR 602.2b / 606.4), so reversing a proposed activation before cost payment
finishes (CR 733.1) leaves no `activated` event, loyalty counter cost event, or
waiting triggers; `.transformIncubator` records `PermanentEvent.transformed`
under a `.oneShotEffect` cause (CR 701.27f / 111.10i); and spell/ability
`phaseOut` expires printed static abilities under the resolving `.oneShotEffect`
cause rather than `.gameRule .leavingZone` (CR 702.26b). -/
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
    let g := addPermanent (addPermanent (addPermanent afterDraw pwWithMana me me) myWatcher me me) oppWatcher opp opp
    let pw := (g.battlefield.filter (·.name == "Test Planeswalker"))[0]!
    quiet (g.changeStatus pw.id (.addCounters .loyalty 3))
  let pw := (gPw0.battlefield.filter (·.name == "Test Planeswalker"))[0]!
  let gPwProposed :=
    match gPw0.activateAbility me pw.id 0 with
    | .ok g => g
    | .error _ => gPw0
  let proposedAbId := gPwProposed.proposedSpell.get!.spellId
  let gPwReversed := gPwProposed.reverseProposedSpell
  let gPwPaid :=
    match (gPwProposed.changePlayer me (.addMana .colorless 2)).apply me .pay with
    | .ok g => g
    | .error _ => gPwProposed
  let gPwInGy :=
    (gPwProposed.changePlayer me (.addMana .colorless 2)).changeObject pw.id (.zone (.graveyard me))
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
    let g := g.changePlayer me (.addMana .colorless 2)
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
      subtypes := #["Incubator"] }
  let gInc0 := quiet (addPermanent afterDraw incDef me me)
  let inc := (gInc0.battlefield.filter (·.name == "Incubator Token"))[0]!
  let gIncTransformed :=
    gInc0.applyFrc me default .transformIncubator #[] (some inc.id)
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
      | .rules (.effectExpired _ (.staticAbility id .boast)) =>
        if id == sb.id then some e.cause else none
      | _ => none)
  let phasedCause? : Option EventCause :=
    gPhasedOut.events.findSome? (fun e =>
      match e.change with
      | .rules (.permanent (.phasedOut o false)) =>
        if o.id == some sb.id then some e.cause else none
      | _ => none)
  !gPwProposed.loggedActivatedLoyalty me &&
    !gPwReversed.loggedActivatedLoyalty me &&
    gPwProposed.waitingTriggers.isEmpty &&
    gPwReversed.waitingTriggers.isEmpty &&
    gPwReversed.stack.isEmpty &&
    !(gPwReversed.object! pw.id).status.loyaltyActivatedThisTurn &&
    (gPwReversed.object! pw.id).status.loyaltyCounters == 3 &&
    !gPwReversed.log.any (fun s => mentions s "loyalty counter(s)") &&
    !gPwReversed.events.any (fun e =>
      match e.change with
      | .rules (.activated ..) | .rules (.permanent (.counters ..)) => true
      | _ => false) &&
    proposedAbId != pw.id &&
    gPwPaid.events.any (fun e =>
      match e.change, e.cause with
      | .rules (.permanent (.counters (.object o) .loyalty (.put 1) (some actor))),
        .costPayment .loyalty payer (some forId) =>
        o.id == some pw.id && actor == me && payer == me && forId == proposedAbId
      | _, _ => false) &&
    !gPwInGy.sourceStillPayable gPwInGy.proposedSpell.get! &&
    gPwInGyPaid.stack.isEmpty &&
    !gPwInGyPaid.loggedActivatedLoyalty me &&
    !gPwInGyPaid.events.any (fun e =>
      match e.change with
      | .rules (.activated ..) | .rules (.permanent (.counters ..)) => true
      | _ => false) &&
    gWbPaid.events.any (fun e =>
      match e.change with
      | .rules (.activated p o false false) =>
        p == me && o.id == some wb.id && o.name == "Test Bauble" &&
          e.cause == EventCause.gameRule .abilityActivated
      | _ => false) &&
    incAfter.status.transformed &&
    incAfter.name == "Phyrexian" &&
    gIncTransformed.events.any (fun e =>
      match e.change, e.cause with
      | .rules (.permanent (.transformed o true)), .oneShotEffect _ (some sid) (some ctrl) =>
        o.id == some inc.id && sid == inc.id && ctrl == me
      | _, _ => false) &&
    (match expiredCause?, phasedCause? with
     | some (.oneShotEffect id1 (some sid1) (some ctrl1)),
       some (.oneShotEffect id2 (some sid2) (some ctrl2)) =>
       id1 == id2 && sid1 == h.id && sid2 == h.id && ctrl1 == me && ctrl2 == me
     | _, _ => false)

/- Phase 3: no rules event in a full demo game has `e.cause == .unclassified`. -/
#guard
  let g := Agent.play drawnHands 400
  let rec causeHasUnclassified : EventCause → Bool
    | .unclassified => true
    | .replaced _ orig => causeHasUnclassified orig
    | _ => false
  let hasUnclassifiedRules (e : GameEvent) : Bool :=
    match e.change with
    | .rules _ => causeHasUnclassified e.cause
    | .engine _ => false
  g.over && !g.events.any hasUnclassifiedRules

end Mtg.Engine.EventTests
