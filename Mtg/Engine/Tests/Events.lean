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
  let staticEff := ContinuousEffectSpec.staticAbility lord.id (.fra .creaturesYouControlHaveTrample)
  let createdOnEnter := (GameEvent.createdEffects g1.events).contains staticEff
  let g2 := g1.createEffect (.losesAbilitiesUntilEot lord.id)
  let expiredOnLose := (GameEvent.expiredEffects g2.events).contains staticEff
  let n2 := g2.events.size
  let g3 := g2.clearEOT
  let recreatedOnCleanup := (GameEvent.createdEffects (g3.events.extract n2 g3.events.size)).contains staticEff
  let (g4, _) := g3.move lord.id (.graveyard me) none
  let expiredOnLeave := ((GameEvent.expiredEffects g4.events).filter (· == staticEff)).size == 2
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
  let staticEff := ContinuousEffectSpec.staticAbility lord.id (.fra .creaturesYouControlHaveTrample)
  let g1 := (g0.createEffect (.cantBlockUntilEot lord.id)).createEffect (.cantBlockUntilEot lord.id)
  let g2 := g1.expireEffect (.cantBlockUntilEot lord.id)
  let g3 := g2.expireEffect (.cantBlockUntilEot lord.id)
  let g4 := (quiet ((g3.createEffect (.losesAbilitiesUntilEot lord.id)).createEffect
    (.losesAbilitiesUntilEot lord.id))).expireEffect (.losesAbilitiesUntilEot lord.id)
  g2.cantBlockUntilEot (g2.object! lord.id) &&
    !g3.cantBlockUntilEot (g3.object! lord.id) &&
    g4.losesAbilitiesUntilEot (g4.object! lord.id) &&
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
    g3.controlUntilSourceLeaves (g3.object! b.id) == some h.id &&
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
  g2.controlUntilEot (g2.object! b.id) &&
    (controlEffectsOn g3 b.id).size == 1 &&
    (g3.object! b.id).controlledBy me &&
    (g4.object! b.id).controlledBy opp &&
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
    (g2.object! b.id).controlledBy me &&
    g2.controlTurnEndsLeft (g2.object! b.id) == 2 &&
    g3.controlTurnEndsLeft (g3.object! b.id) == 1 &&
    (g4.activeEffect? eid).isNone &&
    (g4.object! b.id).controlledBy opp

/- Cleanup does not look up a permanent that ending a control effect exiled
(CR 800.4c). -/
#guard
  let g0 := quiet (addPermanent afterDraw bear opp opp)
  let b := (g0.battlefield.filter (·.name == "Event Bear"))[0]!
  let g1 := (g0.changeControl b me (untilEot := true)).changePlayer opp (.lost true)
  let g2 := (quiet g1).clearEOT
  (g2.findObject? b.id).isNone &&
    g2.objects.any (fun o => o.name == "Event Bear" && o.zone == .exile)

/- Loki leaving replaces his pending copy effect with one holding his last
known power, and the end of turn expires that effect (MSH 109). -/
#guard
  let g0 := quiet (addPermanent afterDraw bear me me)
  let b := (g0.battlefield.filter (·.name == "Event Bear"))[0]!
  let g1 := g0.createEffect (.pendingLokiCopy me (some b.id) 2)
  let eid := (GameEvent.createdEffectsWithId g1.events)[0]!.1
  let (g2, _) := g1.move b.id (.graveyard me) none
  let eid2 := (GameEvent.createdEffectsWithId g2.events).back!.1
  let updated :=
    (g2.activeEffect? eid).isNone &&
      match g2.activeEffect? eid2 with
      | some (.playerRule p (.pendingLokiCopy none 2) _) => p == me
      | _ => false
  let g3 := g2.clearTurnActivations
  updated &&
    (match g2.pendingLokiCopy with
      | some (_, none, _) => true
      | _ => false) &&
    (GameEvent.expiredEffectsWithId g3.events).map Prod.fst == #[eid, eid2] &&
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
  let expiredIds := g4.events.filterMap (fun e =>
    match e.change with
    | .rules (.continuousEffect (.expired id)) => some id
    | _ => none)
  copies.size == 1 &&
    expiredIds == #[eidMe] &&
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
  let expiredIds := g3.events.filterMap (fun e =>
    match e.change with
    | .rules (.continuousEffect (.expired id)) => some id
    | _ => none)
  ids.size == 3 &&
    copies.size == 2 &&
    expiredIds == #[ids[0]!, ids[1]!] &&
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
    g2.copyUntilEot (g2.object! b.id) &&
    (g3.object! b.id).name == "Event Hero" &&
    !(g3.copyUntilEot (g3.object! b.id)) &&
    g3.copyUntilSourceLeaves (g3.object! b.id) == some h.id &&
    ((g3.copyRestore (g3.object! b.id)).map CardDef.name) == some "Event Bear" &&
    (g4.object! b.id).name == "Event Bear" &&
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
    (g3.object! b.id) == { b with controller := some opp } &&
    g3.controlChanged (g3.object! b.id) &&
    (g4.object! b.id) == { b with controller := some me } &&
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
  let g0 := insertObject g0 testImpending me .stack (some me) { counters := #[(.time, 3)] } (fun _ _ => #[])
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
    (attacking := true) (attackingTarget := some (.player opp))
    (returnedAsArtifact := true) (onlyFoodArtifact := true)
  let (g2, tok) := (quiet g1).createToken me treasureToken
    (tapped := true) (attacking := true) (attackingTarget := some (.player opp))
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
    (cause := some (.oneShotEffect (some ⟨g3.nextEffectId⟩) (some b.id) (some me))))
  let g5 := g4.record (GameEvent.resolved g4.turnNumber me 1)
  let gPump := (quiet g0).withResolvingContext (some b.id) me (fun g =>
    g.createEffect (.pump b.id 2 2))
  let gCleanup := ((quiet gPump).clearEOT).clearTurnActivations
  let gBeholdEff := ((quiet g0).becomeTapped (g0.object! b.id)
    (cause := some (.oneShotEffect (some ⟨g0.nextEffectId⟩) (some b.id) (some me)))).beholdAndMaybeUntap me b.id .bear
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
      | .rules (.continuousEffect (.created _ (.layered (.objects #[id]) (.ptModify 2 2) .untilEndOfTurn))),
        .oneShotEffect _ (some sid) (some ctrl) =>
        id == b.id && sid == b.id && ctrl == me
      | _, _ => false) &&
    gCleanup.events.any (fun e =>
      match e.change with
      | .rules (.continuousEffect (.expired _)) =>
        e.cause == .turnBased .cleanupClear
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
      e.change == .rules (.player (.manaEmptied me #[{ mana := .colored .red }, { mana := .colored .red }] false)) &&
        e.cause == .turnBased .emptyManaPools) &&
    (gMana.player me).manaPool.isEmpty &&
    gCombat.events.any (fun e =>
      match e.change with
      | .rules (.combat (.removedFromCombat o)) =>
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
    ((quiet g0).recordPutCounters b.id .stun 1).change
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
  let gReturned := ((quiet gBlink).beginStep .end).resolveTop
  let returnCause? : Option EventCause :=
    gReturned.events.findSome? (fun e =>
      match e.change with
      | .rules (.zone (.moved _ _ .exile .battlefield ..)) => some e.cause
      | _ => none)
  let gAssign :=
    match ((quiet g0).markAttacking b.id).storeCombatAssignments true #[] with
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
   | some (.oneShotEffect (some id1) (some sid1) (some ctrl1)),
     some (.oneShotEffect (some id2) (some sid2) (some ctrl2)) =>
     id1 == id2 && sid1 == h.id && sid2 == h.id && ctrl1 == me && ctrl2 == me
   | _, _ => false) &&
  gAssign.events.any (fun e =>
    match e.change with
    | .rules (.combat (.damageAssigned false true _)) =>
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
    gLink1.withResolvingContext (some b.id) opp (fun g =>
      (g.move h.id (.graveyard me) none).1)
  let linkReturnCause? : Option EventCause :=
    gLinkReturn.events.findSomeRev? (fun e =>
      match e.change with
      | .rules (.zone (.moved _ _ .exile .battlefield ..)) => some e.cause
      | _ => none)
  let gLoki0 := g0.createEffect (.pendingLokiCopy me (some h.id) 3)
    (cause := some (.oneShotEffect (some ⟨g0.nextEffectId⟩) (some h.id) (some me)))
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
    gLokiLeft.events.any (fun e =>
      match e.change with
      | .rules (.continuousEffect (.created _ (.playerRule _ (.pendingLokiCopy none _) _))) => e.cause == destroyCause
      | _ => false) &&
    gPermStack.events.any (fun e =>
      match e.change with
      | .rules (.zone (.moved _ _ .stack .battlefield ..)) =>
        e.cause == EventCause.gameRule .permanentSpellResolved
      | _ => false) &&
    !gCrewDeclined.events.any (fun e =>
      match e.change with
      | .rules (.cast (.abilityActivated ..)) => true
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
      | .rules (.cast (.abilityActivated ..)) => e.cause == EventCause.gameRule .abilityActivated
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
      | .rules (.continuousEffect (.expired _)) => some e.cause
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
    !gPwReversed.loyaltyActivatedThisTurn pw.id &&
    (gPwReversed.object! pw.id).status.loyaltyCounters == 3 &&
    !gPwReversed.log.any (fun s => mentions s "loyalty counter(s)") &&
    !gPwReversed.events.any (fun e =>
      match e.change with
      | .rules (.cast (.abilityActivated ..)) | .rules (.permanent (.counters ..)) => true
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
      | .rules (.cast (.abilityActivated ..)) | .rules (.permanent (.counters ..)) => true
      | _ => false) &&
    gWbPaid.events.any (fun e =>
      match e.change with
      | .rules (.cast (.abilityActivated _ o p (.nonMana none false false false ..))) =>
        p == me && o.id == some wb.id && o.name == "Test Bauble" &&
          e.cause == EventCause.gameRule .abilityActivated
      | _ => false) &&
    incAfter.status.transformed &&
    incAfter.name == "Phyrexian" &&
    incAfter.printed.power == some 0 &&
    incAfter.printed.toughness == some 0 &&
    !gIncTransformed.events.any (fun e =>
      match e.change with
      | .engine (.object _ (.printed _)) => true
      | _ => false) &&
    gIncTransformed.events.any (fun e =>
      match e.change, e.cause with
      | .rules (.permanent (.transformed o true)), .oneShotEffect _ (some sid) (some ctrl) =>
        o.id == some inc.id && sid == inc.id && ctrl == me
      | _, _ => false) &&
    (match expiredCause?, phasedCause? with
     | some (.oneShotEffect (some id1) (some sid1) (some ctrl1)),
       some (.oneShotEffect (some id2) (some sid2) (some ctrl2)) =>
       id1 == id2 && sid1 == h.id && sid2 == h.id && ctrl1 == me && ctrl2 == me
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
      | .rules (.turn (.extraTurnAdded _)) => some e.cause
      | _ => none)
  let gExtraStarted := gExtraQueued.startNextTurn
  let gExtraClearedEot := (quiet gExtraStarted).clearEOT
  let gExtraEndedTurn := (quiet gExtraStarted).startNextTurn
  -- 3. Combat-damage Treasure creation (to player and to planeswalker) uses .turnBased (.dealCombatDamage false)
  let pwDef : CardDef :=
    { name := "Target PW"
      types := #[.planeswalker]
      loyalty := some 5 }
  let gTreasPlayer :=
    let g := (g0.markAttacking b.id).createEffect (.combatDamageCreatesTreasureUntilEot b.id)
    let g := { g with assignedCombatDamage := #[{ source := b.id, toPlayer := 2 }] }
    (quiet g).dealAssignedCombatDamage
  let gTreasPw :=
    let g := addPermanent g0 pwDef opp opp
    let pw := (g.battlefield.filter (·.name == "Target PW"))[0]!
    let g := (g.markAttacking b.id (some (.planeswalker pw.id))).createEffect (.combatDamageCreatesTreasureUntilEot b.id)
    let g := { g with assignedCombatDamage := #[{ source := b.id, toPlayer := 1 }] }
    (quiet g).dealAssignedCombatDamage
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
      | .rules (.permanent (.phasedOut _ false)) => some e.cause
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
      e.cause == EventCause.turnBased .cleanupClear
    | _ => false) &&
    gPermNextTurn.events.any (fun e =>
      match e.change with
      | .rules (.continuousEffect (.expired _)) =>
        e.cause == EventCause.turnBased .expireAtStepBegin
      | _ => false) &&
    storedExtraCause? == some (EventCause.oneShotEffect (some ⟨effBeforeExtra⟩) (some h.id) (some me)) &&
    gExtraStarted.events.any (fun e =>
      match e.change with
      | .rules (.continuousEffect (.created _ (.gameRule .powerUpsForbidden .untilEndOfTurn))) =>
        some e.cause == storedExtraCause?
      | _ => false) &&
    gExtraClearedEot.events.any (fun e =>
      match e.change with
      | .rules (.continuousEffect (.expired _)) =>
        e.cause == EventCause.turnBased .cleanupClear
      | _ => false) &&
    gExtraEndedTurn.events.any (fun e =>
      match e.change with
      | .rules (.continuousEffect (.expired _)) =>
        e.cause == EventCause.turnBased .cleanupClear
      | _ => false) &&
    gTreasPlayer.events.any (fun e =>
      match e.change with
      | .rules (.zone (.created o p)) =>
        o.name == "Treasure" && p == me && e.cause == EventCause.turnBased (.dealCombatDamage false)
      | _ => false) &&
    gTreasPw.events.any (fun e =>
      match e.change with
      | .rules (.zone (.created o p)) =>
        o.name == "Treasure" && p == me && e.cause == EventCause.turnBased (.dealCombatDamage false)
      | _ => false) &&
    gEndCombat.events.any (fun e =>
      match e.change with
      | .rules (.combat (.removedFromCombat o)) =>
        o.id == some b.id && e.cause == EventCause.turnBased .removeFromCombatAtEndOfCombat
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
        o.name == "Bird Soldier" && p == me && e.cause == causeEagles1
      | _ => false) &&
    gEaglesUpkeep.events.any (fun e =>
      match e.change with
      | .rules (.zone (.created o p)) =>
        o.name == "Bird Soldier" && p == me && e.cause == causeEagles2
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
      | .rules (.continuousEffect (.created ..)) => e.cause.oneShotEffectId?
      | _ => none)
  -- 2. .exileThenReturnNextEnd and .exileThenReturnYouControl on two targets
  let twoTargets := #[Target.permanent b.id, Target.permanent h.id]
  let gNextEnd :=
    (quiet gWithSrc).applyUnifiedAbility me Effect.exileThenReturnNextEnd twoTargets
      (sourceId := some s.id)
  let nextEndExileCauses :=
    gNextEnd.events.filterMap (fun e =>
      match e.change with
      | .rules (.zone (.moved _ _ .battlefield .exile ..)) => some e.cause
      | _ => none)
  let gBlinkTwo :=
    (quiet gWithSrc).applyEffect me Effect.exileThenReturnYouControl twoTargets
      (sourceId := some s.id)
  let blinkMoveCauses :=
    gBlinkTwo.events.filterMap (fun e =>
      match e.change with
      | .rules (.zone (.moved ..)) => some e.cause
      | _ => none)
  -- 3. .syntheticDestiny and .sunfall share one cause across all exiled creatures,
  --    and .sunfall records enters-with +1/+1 counters on ZoneEvent.created without
  --    firing creature-only .youPutPlusOne on the noncreature Incubator, and
  --    transforms via otherFace without EngineChange.object (.printed _)
  let gSynth :=
    (quiet gWithSrc).applyFrc me default .syntheticDestiny #[] (some s.id)
  let synthStoredCause := gSynth.delayedTriggers[0]!.cause
  let synthExileCauses :=
    gSynth.events.filterMap (fun e =>
      match e.change with
      | .rules (.zone (.moved _ _ .battlefield .exile ..)) => some e.cause
      | _ => none)
  let gSunfall :=
    (quiet gWithSrc).applyFrc me default .sunfall #[] (some s.id)
  let sunfallExileCauses :=
    gSunfall.events.filterMap (fun e =>
      match e.change with
      | .rules (.zone (.moved _ _ .battlefield .exile ..)) => some e.cause
      | _ => none)
  let sunfallCreated? :=
    gSunfall.events.findSome? (fun e =>
      match e.change with
      | .rules (.zone (.created o p)) =>
        if o.name == "Incubator" && p == me then some (o, e.cause) else none
      | _ => none)
  let sunfallInc := (gSunfall.battlefield.filter (·.name == "Incubator"))[0]!
  let gSunfallTransformed :=
    (quiet gSunfall).applyFrc me default .transformIncubator #[] (some sunfallInc.id)
  let sunfallIncAfter := gSunfallTransformed.object! sunfallInc.id
  -- 4. .massPolymorph shares one exileCause for battlefield exiles and one distinct
  --    revealCause across revealUntil, putHits, and restBottom
  let gMassPoly :=
    (quiet gWithSrc).applyFrc me default .massPolymorph #[] (some s.id)
  let polyBfExiles :=
    gMassPoly.events.filterMap (fun e =>
      match e.change with
      | .rules (.zone (.moved _ _ .battlefield .exile ..)) => some e.cause
      | _ => none)
  let polyRevealMoves :=
    gMassPoly.events.filterMap (fun e =>
      match e.change with
      | .rules (.zone (.moved _ _ (.library _) .exile ..))
      | .rules (.zone (.moved _ _ .exile .battlefield ..))
      | .rules (.zone (.moved _ _ .exile (.library _) ..)) => some e.cause
      | _ => none)
  let polyRestMoves :=
    gMassPoly.events.filterMap (fun e =>
      match e.change with
      | .rules (.zone (.moved _ _ .exile (.library _) ..)) => some e.cause
      | _ => none)
  -- 5. .venserPerm shares one cause across both token creations, both haste effects,
  --    and both delayed end-step sacrifices
  let gVenser :=
    (quiet gWithSrc).applyFrc me default .venserPerm #[Target.permanent b.id] (some s.id)
  let venserCreateCauses :=
    gVenser.events.filterMap (fun e =>
      match e.change with
      | .rules (.zone (.created ..)) => some e.cause
      | _ => none)
  let venserEffectCauses :=
    gVenser.events.filterMap (fun e =>
      match e.change with
      | .rules (.continuousEffect (.created ..)) => some e.cause
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
    gJhoiraSetup.applyFrc me default .jhoira #[Target.player me] (some s.id)
  let jhoiraPendingOk :=
    match gJhoiraPending.pending with
    | .resolveRandom (.orderInto ids (.library p) (some _)) => p == me && ids.size == 2
    | _ => false
  let gJhoiraDone :=
    match (gJhoiraPending.change (.resolvingContext none)).supplyOrder #[] with
    | .ok g' => g'
    | .error _ => gJhoiraPending
  let jhoiraMoveCauses :=
    gJhoiraDone.events.filterMap (fun e =>
      match e.change with
      | .rules (.zone (.moved ..)) => some e.cause
      | _ => none)
  let jhoiraRestCauses :=
    gJhoiraDone.events.filterMap (fun e =>
      match e.change with
      | .rules (.zone (.moved _ _ .exile (.library _) ..)) => some e.cause
      | _ => none)
  let jhoiraLifeCauses :=
    gJhoiraDone.events.filterMap (fun e =>
      match e.change with
      | .rules (.life (.lost _ 2 ..)) => some e.cause
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
    !gSunfallTransformed.events.any (fun e =>
      match e.change with
      | .engine (.object _ (.printed _)) => true
      | _ => false) &&
    polyBfExiles.size == 2 &&
    polyBfExiles[0]! == polyBfExiles[1]! &&
    polyRestMoves.size > 0 &&
    polyRevealMoves.size >= 5 &&
    polyRevealMoves.all (· == polyRevealMoves[0]!) &&
    polyRevealMoves[0]! != polyBfExiles[0]! &&
    venserCreateCauses.size == 2 &&
    venserEffectCauses.size == 2 &&
    gVenser.delayedTriggers.size == 2 &&
    venserCreateCauses.all (· == venserCreateCauses[0]!) &&
    venserEffectCauses.all (· == venserCreateCauses[0]!) &&
    gVenser.delayedTriggers.all (fun dt => dt.cause == venserCreateCauses[0]!) &&
    jhoiraPendingOk &&
    jhoiraMoveCauses.size == 6 &&
    jhoiraRestCauses.size == 2 &&
    jhoiraLifeCauses.size == 1 &&
    jhoiraMoveCauses.all (· == jhoiraMoveCauses[0]!) &&
    jhoiraLifeCauses[0]! == jhoiraMoveCauses[0]!

/- Phase 3: `applyRevealLibrary` (`untilSaga` / `untilCreature` / `resolveRandomCreatureReveal`),
`resolveCascade`, `applyExile` (`.landsYouControl .forLater .lands`, `.nextEndStep`,
`.playUntilNextTurn`, and `.playThisTurn`), `resolveExileTopPlayUntilEndOfNextTurn`,
and `exileTopForPlay` each share one `.oneShotEffect` `EventCause` across all
moves, play-permission `effectCreated` events, and bottom-of-library returns
produced by the single one-shot instruction (CR 610.1 / 701.14 / 702.85a). -/
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
      | .rules (.zone (.moved _ _ .battlefield .exile ..)) => some e.cause
      | _ => none)
  -- 2. `applyExile` with `.nextEndStep` on multiple permanents shares one cause
  let gNextEndTrig :=
    (quiet g0).applyExile me default (some b.id) #[Target.permanent b.id, Target.permanent h.id]
      .eachPermanent .nextEndStep .none
  let nextEndTrigCauses :=
    gNextEndTrig.events.filterMap (fun e =>
      match e.change with
      | .rules (.zone (.moved _ _ .battlefield .exile ..)) => some e.cause
      | _ => none)
  -- 3. `applyExile` `.playUntilNextTurn` and `.playThisTurn` share cause between
  --    `ZoneEvent.moved` and `effectCreated (.playPermission ...)`
  let gPlayNext :=
    (quiet g0).applyExile me default (some b.id) #[] .top .playUntilNextTurn .none
  let playNextMoveCauses :=
    gPlayNext.events.filterMap (fun e =>
      match e.change with
      | .rules (.zone (.moved _ _ (.library _) .exile ..)) => some e.cause
      | _ => none)
  let playNextEffCauses :=
    gPlayNext.events.filterMap (fun e =>
      match e.change with
      | .rules (.continuousEffect (.created ..)) => some e.cause
      | _ => none)
  let gPlayThis :=
    (quiet g0).applyExile me default (some b.id) #[] .top .playThisTurn .none
  let playThisMoveCauses :=
    gPlayThis.events.filterMap (fun e =>
      match e.change with
      | .rules (.zone (.moved _ _ (.library _) .exile ..)) => some e.cause
      | _ => none)
  let playThisEffCauses :=
    gPlayThis.events.filterMap (fun e =>
      match e.change with
      | .rules (.continuousEffect (.created ..)) => some e.cause
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
    match (gRevPending.change (.resolvingContext none)).supplyOrder #[] with
    | .ok g' => g'
    | .error _ => gRevPending
  let revMoveCauses :=
    gRevDone.events.filterMap (fun e =>
      match e.change with
      | .rules (.zone (.moved ..)) => some e.cause
      | _ => none)
  -- 5. `resolveCascade` + `.mayCastCascade` `.decline` shares one cause across
  --    exiling from library and returning the exiled cards to the bottom
  let gCascPending := gRevSetup.resolveCascade me 3
  let gCascChoice :=
    match gCascPending.answerFraChoice me .decline with
    | .ok g' => g'
    | .error _ => gCascPending
  let gCascDone :=
    match (gCascChoice.change (.resolvingContext none)).supplyOrder #[] with
    | .ok g' => g'
    | .error _ => gCascChoice
  let cascMoveCauses :=
    gCascDone.events.filterMap (fun e =>
      match e.change with
      | .rules (.zone (.moved ..)) => some e.cause
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
    revMoveCauses.size == 5 &&
    revMoveCauses.all (· == revMoveCauses[0]!) &&
    cascMoveCauses.size == 6 &&
    cascMoveCauses.all (· == cascMoveCauses[0]!)

/- Phase 3: `.mayRevealToHand` (`anyOrder := true`) + `.orderLibraryBottom`,
`.nickFuryPut` + `.nickFuryMayTransform` `.accept`,
`grimaExileUntilInstantOrSorcery` (`castTheCard := true`),
generic `TriggerResolution.revealLibrary` (`applyRevealLibrary == none`), and
`exileTopPlayIfYouControlSubtype` each share a single `.oneShotEffect` cause
across all constituent moves, transforms, and continuous-effect creations
(CR 608.2c / 610.1 / 701.14 / 701.27a). -/
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
      | .rules (.zone (.moved ..)) => some e.cause
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
  let gNick1 := gNickSetup.beginLookPutTypes me 3 #[.hero]
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
      | .rules (.zone (.moved ..)) => some e.cause
      | .rules (.permanent (.transformed ..)) => some e.cause
      | _ => none)
  -- 3. `grimaExileUntilInstantOrSorcery` with `castTheCard := true`
  let gGrima0 :=
    insertObject g0 shockDef me (.library me) none {} (fun id _ => #[.pushLibrary id])
  let gGrimaSetup :=
    let g := (gGrima0.move l1.id (.library me) none (libraryPosition := some .top)).1
    let g := (g.move l2.id (.library me) none (libraryPosition := some .top)).1
    quiet g
  let gGrimaPending :=
    gGrimaSetup.withResolvingContext (some h.id) me (fun g =>
      g.grimaExileUntilInstantOrSorcery me me true)
  let gGrimaDone :=
    match gGrimaPending.supplyOrder #[] with
    | .ok g' => g'
    | .error _ => gGrimaPending
  let grimaCauses :=
    gGrimaDone.events.filterMap (fun e =>
      match e.change with
      | .rules (.zone (.moved ..)) => some e.cause
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
      | .rules (.zone (.moved ..)) => some e.cause
      | _ => none)
  -- 5. `exileTopPlayIfYouControlSubtype` while resolving
  let gExTop :=
    gLibSetup.withResolvingContext (some h.id) me (fun g =>
      g.exileTopPlayIfYouControlSubtype me 2 .hero)
  let exTopCauses :=
    gExTop.events.filterMap (fun e =>
      match e.change with
      | .rules (.zone (.moved ..)) => some e.cause
      | .rules (.continuousEffect (.created _ (.permission _ (.playFromExile ..) _))) => some e.cause
      | _ => none)
  -- 6. `exileHandDrawPlayUntilNext` shares one cause across hand exiles, play permissions, and draws
  let handSize := (gLibSetup.player me).hand.size
  let gHex :=
    gLibSetup.withResolvingContext (some h.id) me (fun g =>
      g.exileHandDrawPlayUntilNext me)
  let hexCauses :=
    gHex.events.filterMap (fun e =>
      match e.change with
      | .rules (.zone (.moved ..)) => some e.cause
      | .rules (.continuousEffect (.created _ (.permission _ (.playFromExile ..) _))) => some e.cause
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
      | .rules (.zone (.moved ..)) => some e.cause
      | _ => none)
  -- 8. `millThenChooseForHand` shares one cause across the mill and deferred `.chooseCards` `.toHand`,
  --    and only offers cards actually milled from the library even when `n` exceeds `library.size`
  let gShortLib :=
    let g := g0.changePlayer me (.library #[])
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
      | .rules (.zone (.moved ..)) => some e.cause
      | _ => none)
  -- 9. `draw` and `mill` outside a resolving context leave `.unclassified`, while `drawThenLoseLife`,
  --    `drawEqualToughnessThenPutCreatures`, `.twoPlayersDraw`, `millCollected` / `.milledSubtype`,
  --    and `.palantirMayDraw` `.decline` share one `.oneShotEffect` cause across each instruction
  let gRawDraw := gLibSetup.draw me 2
  let rawDrawCauses :=
    gRawDraw.events.filterMap (fun e =>
      match e.change with
      | .rules (.zone (.moved ..)) => some e.cause
      | _ => none)
  let gRawMill := gLibSetup.mill me 2
  let rawMillCauses :=
    gRawMill.events.filterMap (fun e =>
      match e.change with
      | .rules (.zone (.moved ..)) => some e.cause
      | _ => none)
  let gDrawLose :=
    gLibSetup.withResolvingContext (some h.id) me (fun g =>
      g.drawThenLoseLife me 2 2)
  let drawLoseCauses :=
    gDrawLose.events.filterMap (fun e =>
      match e.change with
      | .rules (.zone (.moved ..)) => some e.cause
      | .rules (.life (.lost ..)) => some e.cause
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
      | .rules (.zone (.moved ..)) => some e.cause
      | _ => none)
  let gTwoDraw :=
    gLibSetup.withResolvingContext (some h.id) me (fun g =>
      g.applyAbilityEffect me { resolution := .twoPlayersDraw } #[Target.player me, Target.player opp] (sourceId := some h.id))
  let twoDrawCauses :=
    gTwoDraw.events.filterMap (fun e =>
      match e.change with
      | .rules (.zone (.moved ..)) => some e.cause
      | _ => none)
  let gMillSubtype :=
    gLibSetup.withResolvingContext (some h.id) me (fun g =>
      g.applyTriggeredAbility me (.onEnterMillThenSubtypeToHand 3 "Bear") (some h.id) #[] #[] none none "This creature"
        (some (.sequence [.mill (.fixed 3) .you .milledCards, .returnToHand (.milledSubtype .bear)])))
  let millSubtypeCauses :=
    gMillSubtype.events.filterMap (fun e =>
      match e.change with
      | .rules (.zone (.moved ..)) => some e.cause
      | _ => none)
  let gPalantir0 :=
    (gGrimaSetup.recordPutCounters h.id .influence 3).change (.pending (.fraChoice opp (.palantirMayDraw me h.id)))
      |>.change (.resolvingContext (some (some h.id, me)))
  let gPalantirDone :=
    match gPalantir0.answerFraChoice opp .decline with
    | .ok g' => g'
    | .error _ => gPalantir0
  let palantirCauses :=
    gPalantirDone.events.filterMap (fun e =>
      match e.change with
      | .rules (.zone (.moved ..)) => some e.cause
      | .rules (.life (.lost ..)) => some e.cause
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
      | .rules (.zone (.moved ..)) => some e.cause
      | .rules (.life (.lost ..)) => some e.cause
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
      | .rules (.zone (.moved ..)) => some e.cause
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
      | .rules (.zone (.moved ..)) => some e.cause
      | _ => none)
  let gArmorEmpty0 :=
    (gLibSetup.changePlayer me (.library #[])).change (.pending (.fraChoice me (.mayDrawThenEachOpponentDraws 1)))
      |>.change (.resolvingContext (some (some h.id, me)))
  let gArmorEmptyDone :=
    match gArmorEmpty0.answerFraChoice me .accept with
    | .ok g' => g'
    | .error _ => gArmorEmpty0
  let armorEmptyMoves :=
    gArmorEmptyDone.events.filterMap (fun e =>
      match e.change with
      | .rules (.zone (.moved ..)) => some e.cause
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
      | .rules _ => some e.cause
      | _ => none)
  let gDmgPermRes :=
    gDmgSetup.withResolvingContext (some lh.id) me (fun g =>
      g.dealDamageFrom lh.name oppBear 1 (source := some lh))
  let dmgPermResCauses :=
    gDmgPermRes.events.filterMap (fun e =>
      match e.change with
      | .rules _ => some e.cause
      | _ => none)
  let gDmgPlayerRaw := gDmgSetup.dealDamageToPlayer opp 2 (source := some lh)
  let dmgPlayerRawCauses :=
    gDmgPlayerRaw.events.filterMap (fun e =>
      match e.change with
      | .rules _ => some e.cause
      | _ => none)
  let gDmgPlayerRes :=
    gDmgSetup.withResolvingContext (some lh.id) me (fun g =>
      g.dealDamageToPlayer opp 2 (source := some lh))
  let dmgPlayerResCauses :=
    gDmgPlayerRes.events.filterMap (fun e =>
      match e.change with
      | .rules _ => some e.cause
      | _ => none)
  let gSweepRes :=
    gDmgSetup.withResolvingContext (some lh.id) me (fun g =>
      g.applyTriggeredAbility me (.onEnterDraw 1) (some lh.id)
        (resolutionOverride := some (.dealDamage (.fixed 1) (.eachNonSubtypeAndOpponents .dragon))))
  let sweepResCauses :=
    gSweepRes.events.filterMap (fun e =>
      match e.change with
      | .rules _ => some e.cause
      | _ => none)
  let gNivRaw := gDmgSetup.applyFrc me default .nivPay #[] (some lh.id) (lastKnownPower := some 2)
  let nivRawCauses :=
    gNivRaw.events.filterMap (fun e =>
      match e.change with
      | .rules _ => some e.cause
      | _ => none)
  let gNivRes :=
    gDmgSetup.withResolvingContext (some lh.id) me (fun g =>
      g.applyFrc me default .nivPay #[] (some lh.id) (lastKnownPower := some 2))
  let nivResCauses :=
    gNivRes.events.filterMap (fun e =>
      match e.change with
      | .rules _ => some e.cause
      | _ => none)
  let gNivLocked :=
    quiet (gDmgSetup.createEffect (.lifeCantChange me))
      |>.withResolvingContext (some lh.id) me (fun g =>
        g.applyFrc me default .nivPay #[] (some lh.id) (lastKnownPower := some 2))
  let nivLockedEvents :=
    gNivLocked.events.filterMap (fun e =>
      match e.change with
      | .rules _ => some e.cause
      | _ => none)
  let gDreadRaw := gDmgSetup.applyFrc me default .dreadUpkeep #[] (some lh.id)
  let dreadRawCauses :=
    gDreadRaw.events.filterMap (fun e =>
      match e.change with
      | .rules _ => some e.cause
      | _ => none)
  let gDreadRes :=
    gDmgSetup.withResolvingContext (some lh.id) me (fun g =>
      g.applyFrc me default .dreadUpkeep #[] (some lh.id))
  let dreadResCauses :=
    gDreadRes.events.filterMap (fun e =>
      match e.change with
      | .rules _ => some e.cause
      | _ => none)
  let gSkrelvRaw := gDmgSetup.applyFrc me default .skrelv #[] (some lh.id)
  let skrelvRawCauses :=
    gSkrelvRaw.events.filterMap (fun e =>
      match e.change with
      | .rules _ => some e.cause
      | _ => none)
  let gSkrelvRes :=
    gDmgSetup.withResolvingContext (some lh.id) me (fun g =>
      g.applyFrc me default .skrelv #[] (some lh.id))
  let skrelvResCauses :=
    gSkrelvRes.events.filterMap (fun e =>
      match e.change with
      | .rules _ => some e.cause
      | _ => none)
  let gDrainPlanRaw :=
    gDmgSetup.applyTriggeredAbility me (.onVillainYouControlEntersDrainAndPlan 2) (some lh.id)
  let drainPlanRawCauses :=
    gDrainPlanRaw.events.filterMap (fun e =>
      match e.change with
      | .rules _ => some e.cause
      | _ => none)
  let gDrainPlanRes :=
    gDmgSetup.withResolvingContext (some lh.id) me (fun g =>
      g.applyTriggeredAbility me (.onVillainYouControlEntersDrainAndPlan 2) (some lh.id))
  let drainPlanResCauses :=
    gDrainPlanRes.events.filterMap (fun e =>
      match e.change with
      | .rules _ => some e.cause
      | _ => none)
  mayRevCauses.size == 3 &&
    mayRevCauses.all (· == mayRevCauses[0]!) &&
    nickCauses.size == 4 &&
    nickCauses.all (· == nickCauses[0]!) &&
    grimaCauses.size == 6 &&
    grimaCauses.all (· == grimaCauses[0]!) &&
    trigRevCauses.size == 5 &&
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
    rawDrawCauses.all (· == .unclassified) &&
    rawMillCauses.size == 2 &&
    rawMillCauses.all (· == .unclassified) &&
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
    palantirRawCauses.all (· == .unclassified) &&
    balinRawCauses.size == handSize &&
    balinRawCauses.all (· == .unclassified) &&
    balinResCauses.size == handSize * 2 &&
    (balinResCauses.extract 0 handSize).all (· == balinResCauses[0]!) &&
    (balinResCauses.extract handSize (handSize * 2)).all (· == balinResCauses[handSize]!) &&
    balinResCauses[0]! != balinResCauses[handSize]! &&
    armorEmptyMoves.isEmpty &&
    gArmorEmptyDone.drewFromEmpty me &&
    dmgPermRawCauses.size == 3 &&
    dmgPermRawCauses.all (· == .unclassified) &&
    dmgPermResCauses.size == 3 &&
    dmgPermResCauses.all (· == dmgPermResCauses[0]!) &&
    (match dmgPermResCauses[0]! with | .oneShotEffect (some _) (some _) (some _) => true | _ => false) &&
    dmgPlayerRawCauses.size == 3 &&
    dmgPlayerRawCauses.all (· == .unclassified) &&
    dmgPlayerResCauses.size == 3 &&
    dmgPlayerResCauses.all (· == dmgPlayerResCauses[0]!) &&
    (match dmgPlayerResCauses[0]! with | .oneShotEffect (some _) (some _) (some _) => true | _ => false) &&
    sweepResCauses.size >= 9 &&
    sweepResCauses.all (· == sweepResCauses[0]!) &&
    (match sweepResCauses[0]! with | .oneShotEffect (some _) (some _) (some _) => true | _ => false) &&
    nivRawCauses.size == 3 &&
    nivRawCauses.all (· == .unclassified) &&
    nivResCauses.size == 3 &&
    nivResCauses[0]! == .costPayment .life me (some lh.id) &&
    nivResCauses[1]! == nivResCauses[2]! &&
    (match nivResCauses[1]! with | .oneShotEffect (some _) (some _) (some _) => true | _ => false) &&
    nivLockedEvents.isEmpty &&
    dreadRawCauses.size == 3 &&
    dreadRawCauses.all (· == .unclassified) &&
    dreadResCauses.size == 3 &&
    dreadResCauses.all (· == dreadResCauses[0]!) &&
    (match dreadResCauses[0]! with | .oneShotEffect (some _) (some _) (some _) => true | _ => false) &&
    skrelvRawCauses.size == 2 &&
    skrelvRawCauses.all (· == .unclassified) &&
    skrelvResCauses.size == 2 &&
    skrelvResCauses.all (· == skrelvResCauses[0]!) &&
    (match skrelvResCauses[0]! with | .oneShotEffect (some _) (some _) (some _) => true | _ => false) &&
    drainPlanRawCauses.size == 3 &&
    drainPlanRawCauses.all (· == .unclassified) &&
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
    ((quiet g2).record (GameEvent.life g2.turnNumber me 1 true)).record
      (GameEvent.life g2.turnNumber me 1 true)
  let rules3 := g3.events.filter (fun e => match e.change with | .rules _ => true | _ => false)
  rules1.size == 2 &&
    rules1[0]!.batch == ⟨b0⟩ &&
    rules1[1]!.batch == ⟨b0⟩ &&
    rules1[0]!.cause == .oneShotEffect (some ⟨e0⟩) none (some me) &&
    rules1[1]!.cause == .oneShotEffect (some ⟨e0⟩) none (some me) &&
    g1.nextBatchId == b0 + 1 &&
    g1.nextEffectId == e0 + 1 &&
    rules2.size == 2 &&
    rules2[0]!.batch == ⟨b0 + 1⟩ &&
    rules2[1]!.batch == ⟨b0 + 1⟩ &&
    rules2[0]!.cause == .stateBased .lethalDamage &&
    rules2[1]!.cause == .stateBased .zeroOrLessToughness &&
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
    | .rules _ => e.cause == .turnBased (.dealCombatDamage true)
    | _ => false)
  let regEvents := gReg.events.filter (fun e =>
    match e.change with
    | .rules _ => e.cause == .turnBased (.dealCombatDamage false)
    | _ => false)
  let lordDef : CardDef :=
    { (creature "Bear Lord" ManaCost.empty #["Bear"] 2 2) with
      staticAbilities := #[.otherCreaturesGet #[.bear] 1 1] }
  let gSba0 :=
    let g := addPermanent (addPermanent (addPermanent afterDraw lordDef me me) bear me me) hero me me
    let ld := (g.battlefield.filter (·.name == "Bear Lord"))[0]!
    let b := (g.battlefield.filter (·.name == bear.name))[0]!
    let h := (g.battlefield.filter (·.name == hero.name))[0]!
    let g := ((g.changeStatus ld.id (.damage 2)).changeStatus h.id (.damage 3)).changeStatus b.id (.damage 2)
    quiet g
  let ldId := (gSba0.battlefield.filter (·.name == "Bear Lord"))[0]!.id
  let hId := (gSba0.battlefield.filter (·.name == hero.name))[0]!.id
  let bId := (gSba0.battlefield.filter (·.name == bear.name))[0]!.id
  let gSbaDone := gSba0.checkSBA
  let batchOfMoved? (oid : ObjectId) : Option BatchId :=
    gSbaDone.events.findSome? (fun e =>
      match e.change with
      | .rules (.zone (.moved before ..)) =>
        if before.id == some oid && e.cause == .stateBased .lethalDamage then some e.batch else none
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

def noUnclassifiedRulesEvents (g : Game) : Bool :=
  let rec causeHasUnclassified : EventCause → Bool
    | .unclassified => true
    | .replaced _ orig => causeHasUnclassified orig
    | _ => false
  !g.events.any (fun e =>
    match e.change with
    | .rules _ => causeHasUnclassified e.cause
    | .engine _ => false)

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
      (cause := some (.oneShotEffect (some ⟨97⟩) none (some me))))).record
      (GameEvent.extraTurnAdded g0.turnNumber opp .current
        (cause := some (.oneShotEffect (some ⟨98⟩) none (some me))))
  let g2 := g1.record (GameEvent.extraPhaseAdded g1.turnNumber .combat .current
    (cause := some (.oneShotEffect (some ⟨99⟩) none (some me))))
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
    noUnclassifiedRulesEvents g1 &&
    noUnclassifiedRulesEvents g2 &&
    noUnclassifiedRulesEvents gStep

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
    (cause := some (.oneShotEffect (some ⟨77⟩) none (some me))))
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
    (cause := some (.oneShotEffect (some ⟨78⟩) none (some me))))
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
  let gEnter0 := insertObject (quiet g0) bear me (.graveyard me) none {} (fun id _ =>
    #[.pushGraveyard id])
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
      (cause := some (.oneShotEffect (some ⟨81⟩) none (some me))))
    let g := insertObject g bear me .stack (some me) {}
    let spId := (g.objects.filter (fun o => o.name == bear.name && o.zone == .stack))[0]!.id
    let g := g.putStackEntry me spId
    { g with step := .declareBlockers }
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
  let gReaper0 := insertObject (quiet g0) bear me (.graveyard me) none {} (fun id _ =>
    #[.pushGraveyard id])
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
    atkCombatAndTap[0]!.cause == .turnBased .declareAttackers &&
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
    noUnclassifiedRulesEvents gBecame &&
    noUnclassifiedRulesEvents gAtk &&
    noUnclassifiedRulesEvents gBlk &&
    noUnclassifiedRulesEvents gRem &&
    noUnclassifiedRulesEvents gEnterDefault &&
    noUnclassifiedRulesEvents gSneak1 &&
    noUnclassifiedRulesEvents gTokPw &&
    noUnclassifiedRulesEvents gAnduril2 &&
    noUnclassifiedRulesEvents gReaper2

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
      p == me && e.cause == .specialAction .playLand me
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
  let gCast0 := insertObject (quiet afterDraw) testModalSpell me .stack (some me) {} (fun _ _ => #[])
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
  let gCast4 := (gCast4.changeObjects spId #[
    .adventurerCard (some bear),
    .reflexiveResolution (some (.draw (.fixed 2) .you)),
    .fraCauseId (some ⟨71⟩),
    .fraCauseController (some opp),
    .fraCausePower (some 4),
    .fraCauseStatus (some { counters := #[(.plusOnePlusOne, 2)] })]).createEffect
      (.exileInstantSorceryInstead spId)
      (cause := some (.oneShotEffect (some ⟨86⟩) none (some me)))
  let gCopy1 := gCast4.copyStackSpell (gCast4.object! spId) me
  let copy1Entry := gCopy1.stack.back!
  let copy1Obj := gCopy1.object! copy1Entry.objectId
  -- Also test Loki and Way of the Cryomancer in becomeCast
  let cryoCause : EventCause := .oneShotEffect (some ⟨87⟩) none (some me)
  let lokiCause : EventCause := .oneShotEffect (some ⟨88⟩) (some ⟨70⟩) (some me)
  let gCryoLoki0 :=
    let g := gCast4.createEffect (.copyNextInstantSorceryThisTurn me 1)
      (cause := some cryoCause)
    g.createEffect (.pendingLokiCopy me (some ⟨70⟩) 10)
      (cause := some lokiCause)
  let gCryoLoki := gCryoLoki0.becomeCast me (gCryoLoki0.object! spId)
  let copiedEvents := gCryoLoki.events.filterMap (fun e =>
    match e.change with
    | .rules (.stackObject (.copied orig copy ctrl)) => some (orig, copy, ctrl, e.cause)
    | _ => none)
  -- 4. TriggerQueueEvent.putOnStack and StackObjectEvent.removedOnResolution (CR 608.2b)
  let gTrig0 := addPermanent (quiet afterDraw) bear opp opp
  let oppBear := (gTrig0.battlefield.filter (fun o => o.name == bear.name && o.controlledBy opp))[0]!
  let trigAb := TriggeredAbility.fra .enter "When this enters, destroy target creature an opponent controls." (.destroy (.target .creature)) (kind := .oppCreature)
  let gTrigPut := gTrig0.putTriggeredAbilityOnStack me (gTrig0.object! oppBear.id) trigAb "enters"
  let gTrig1 := gTrigPut.setStackEntryTargets gTrigPut.stack.back!.objectId #[Target.permanent oppBear.id]
  let hasTrigPutOnStack := gTrig1.events.any (fun e =>
    match e.change with
    | .rules (.triggerQueue (.putOnStack stackId _ ctrl)) =>
      ctrl == me && gTrig1.stack.any (·.objectId == stackId) &&
        e.cause == .gameRule .triggeredAbility
    | _ => false)
  let (gTrig2, _) := (quiet gTrig1).move oppBear.id (.graveyard opp) (verb := some .destroy)
    (cause := some (.oneShotEffect (some ⟨89⟩) none (some me)))
  let gTrig3 := gTrig2.resolveTop
  let hasRemovedOnResolution := gTrig3.events.any (fun e =>
    match e.change with
    | .rules (.stackObject (.removedOnResolution _)) =>
      e.cause == .gameRule .abilityFinishedResolving
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
      e.cause == .gameRule .instantOrSorceryFinishedResolving
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
    copy1Obj.reflexiveResolution == some (.draw (.fixed 2) .you) &&
    copy1Obj.fraCauseId == some ⟨71⟩ &&
    copy1Obj.fraCauseController == some opp &&
    copy1Obj.fraCausePower == some 4 &&
    copy1Obj.fraCauseStatus == some { counters := #[(.plusOnePlusOne, 2)] } &&
    gCopy1.lastKnownPowerOf? copy1Obj.id == some 5 &&
    gCopy1.lastKnownToughnessOf? copy1Obj.id == some 6 &&
    copy1Entry.chosenMode == some 0 &&
    copy1Entry.extraModes == #[1] &&
    copy1Entry.targets == #[Target.player opp] &&
    copy1Entry.dividedDamage == #[2] &&
    copy1Entry.targetsAnnounced &&
    copiedEvents.size == 2 &&
    copiedEvents.all (fun (orig, _, ctrl, _) => orig == spId && ctrl == me) &&
    copiedEvents[0]!.2.2.2 == cryoCause &&
    copiedEvents[1]!.2.2.2 == lokiCause &&
    hasTrigPutOnStack &&
    hasRemovedOnResolution &&
    hasSpellRemovedOnResolution &&
    noUnclassifiedRulesEvents gLand1 &&
    noUnclassifiedRulesEvents gCast4 &&
    noUnclassifiedRulesEvents gCopy1 &&
    noUnclassifiedRulesEvents gCryoLoki &&
    noUnclassifiedRulesEvents gTrig1 &&
    noUnclassifiedRulesEvents gTrig3 &&
    noUnclassifiedRulesEvents gFizzle2

/- Phase 6: `matchTriggers (pre : GameSnapshot) (post : Game) (batch : Array GameEvent)`
evaluates all triggers at outermost batch close, covers CR 603.10a–f look-back
via `pre` and `GameEvent.isLookBack`, records `TriggerQueueEvent.triggered`
with `cause := .gameRule .triggeredAbility`, and queries once-each-turn
triggers from the event log instead of `Status.firedOnceEachTurn`. -/
#guard
  -- 1. CR 603.10a–f look-back classification on `GameEvent.isLookBack`
  let snapA : EventObject := { id := some ⟨1⟩, owner := me, controller := some me, types := #[.creature] }
  let evLtb := GameEvent.moved 1 snapA .battlefield (.graveyard me)
  let evSac := GameEvent.moved 1 snapA .battlefield (.graveyard me) (verb := some .sacrifice)
  let evLeaveGy := GameEvent.moved 1 snapA (.graveyard me) .exile
  let evBounce := GameEvent.moved 1 snapA .battlefield (.hand me)
  let evTuck := GameEvent.moved 1 snapA .exile (.library me)
  let evPhaseOut := GameEvent.phasedOut 1 snapA false
  let evPhaseIn := GameEvent.phasedIn 1 snapA false
  let evUnattach := GameEvent.unattached 1 snapA ⟨2⟩
  let evControl := GameEvent.control 1 ⟨1⟩ me opp
  let evCounter := GameEvent.moved 1 snapA .stack (.graveyard me) (verb := some .counter)
  let evPlayerLost := GameEvent.playerLost 1 opp
  let evEtb := GameEvent.moved 1 snapA (.hand me) .battlefield
  let evDiscard := GameEvent.moved 1 snapA (.hand me) (.graveyard me) (discarded := true)
  let lookBackFlagsOk :=
    evLtb.isLookBack &&
    evSac.isLookBack &&
    evLeaveGy.isLookBack &&
    evBounce.isLookBack &&
    evTuck.isLookBack &&
    evPhaseOut.isLookBack &&
    !evPhaseIn.isLookBack &&
    evUnattach.isLookBack &&
    evControl.isLookBack &&
    evCounter.isLookBack &&
    evPlayerLost.isLookBack &&
    !evEtb.isLookBack &&
    !evDiscard.isLookBack
  -- 2. Simultaneous deaths (CR 603.10a): two creatures with "whenever another
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
    match e.change with
    | .rules (.triggerQueue (.triggered src ctrl ab origin)) =>
      some (src.id, ctrl, ab, origin, e.cause, e.batch)
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
        snap.id == some phaser.id && e.isLookBack
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
  lookBackFlagsOk &&
    simDeathsOk &&
    phaseOutNoLeaveOk &&
    phaseLookBackOk &&
    onceEachTurnOk &&
    hulkBatchOk &&
    dmgBatchCopiesOk &&
    noUnclassifiedRulesEvents gSim1 &&
    noUnclassifiedRulesEvents gPhaseOnly &&
    noUnclassifiedRulesEvents gPhaseAndDie &&
    noUnclassifiedRulesEvents gHulkBatch &&
    noUnclassifiedRulesEvents gDmgBatch

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
    termCounterEvents[0]!.cause ==
      .replaced idMulCtr (.replaced idAddCtr baseCause) &&
    noUnclassifiedRulesEvents gTerm2

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
  let prevDamageEvents := gPrev2.events.filter (fun e =>
    match e.change with
    | .rules (.damage _) => true
    | _ => false)
  !finHasGyMove &&
    gFin2.waitingTriggers.isEmpty &&
    finExileMoves.size == 1 &&
    finExileMoves[0]!.cause == .replaced finalityId finDeathCause &&
    gShd2.events.all (fun e =>
      match e.change with
      | .rules (.zone (.moved ..)) => false
      | _ => true) &&
    (gShd2.object! shdBear0.id).zone == .battlefield &&
    (gShd2.object! shdBear0.id).status.shield == 0 &&
    shdRemovedEvents.size == 1 &&
    shdRemovedEvents[0]!.cause == .replaced shdId shdDestroyCause &&
    stunUntapEvents.isEmpty &&
    (gStun2.object! stunBear0.id).status.tapped &&
    (gStun2.object! stunBear0.id).status.stun == 0 &&
    stunRemovedEvents.size == 1 &&
    stunRemovedEvents[0]!.cause == .replaced stunId (.turnBased .untapAll) &&
    drwMoves.size == 2 &&
    drwMoves.all (fun e => e.cause == .replaced drwRepId drwCause) &&
    prevDamageEvents.isEmpty &&
    (gPrev2.object! prevBear.id).status.damage == 0 &&
    noUnclassifiedRulesEvents gFin2 &&
    noUnclassifiedRulesEvents gShd2 &&
    noUnclassifiedRulesEvents gStun2 &&
    noUnclassifiedRulesEvents gDrw1 &&
    noUnclassifiedRulesEvents gPrev2

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
    insertObject (quiet afterDraw) dfcFrontDef opp (.hand opp) none {} (fun id _ => #[.pushHand id])
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
    noUnclassifiedRulesEvents gTier2

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
    wrappedNonResolving == some (.replaced idAddDmg .unclassified) &&
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
    shdFromRemoved[0]!.cause == .replaced shdRepId shdDmgCause
  -- Arwen (`othersEnterWithPlusOneEqualToughness := true`) + Doc Samson (`.extraCounterOnPermanents`) ETB counter replacement.
  let samsonDef : CardDef :=
    { bear with name := "Doc Samson Test", staticAbilities := #[.extraCounterOnPermanents] }
  let arwenDef : CardDef :=
    { bear with name := "Arwen Test", toughness := some 2, othersEnterWithPlusOneEqualToughness := true }
  let gArw0 :=
    insertObject
      (addPermanent (addPermanent (quiet afterDraw) samsonDef me me) arwenDef me me)
      { bear with name := "Newcomer Bear" } me (.hand me) none {} (fun id _ => #[.pushHand id])
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
    (gSim0.changeStatus simC1.id (.damage 2)).changeStatus simC2.id (.damage 2)
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
    insertObject gOrd0 { bear with name := "Entering Striker" } me (.hand me) none {}
      (fun id _ => #[.pushHand id])
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
      (insertObject gOrd0 oddEvenDef1 me (.hand me) none {} (fun id _ => #[.pushHand id]))
      oddEvenDef2 me (.hand me) none {} (fun id _ => #[.pushHand id])
  let pCard1 := ((gFraEnt0.player me).hand.filter (fun id => (gFraEnt0.object! id).name == "Parity Striker 1"))[0]!
  let pCard2 := ((gFraEnt0.player me).hand.filter (fun id => (gFraEnt0.object! id).name == "Parity Striker 2"))[0]!
  let item1 : EnteringAttackItem :=
    .card pCard1 me me true false #[] [] .putOntoBattlefield #[.player opp]
  let item2 : EnteringAttackItem :=
    .card pCard2 me me true false #[] [] .putOntoBattlefield #[.player opp]
  let gFraEntPaused1 :=
    (quiet gFraEnt0).commitEnteringAttackItems #[(item1, some (.player opp)), (item2, some (.player opp))]
      (cause := some arwCause)
  let entered1Id := ((gFraEntPaused1.battlefield.filter (·.name == "Parity Striker 1"))[0]!).id
  let gFraEntPaused2 :=
    (gFraEntPaused1.apply me (.chooseMode 0)).toOption.getD gFraEntPaused1
  let entered2Id := ((gFraEntPaused2.battlefield.filter (·.name == "Parity Striker 2"))[0]!).id
  let gFraEntDone :=
    (gFraEntPaused2.apply me (.chooseMode 1)).toOption.getD gFraEntPaused2
  let entAtkFraBatches := gFraEntDone.events.filterMap (fun e =>
    match e.change with
    | .rules (.zone (.moved ..)) => some e.batch
    | _ => none)
  let entAtkFraOk :=
    gFraEntPaused1.pending == .fraChoice me (.entersOddEven entered1Id) &&
    !gFraEntPaused1.battlefield.any (·.name == "Parity Striker 2") &&
    gFraEntPaused2.pending == .fraChoice me (.entersOddEven entered2Id) &&
    (gFraEntPaused2.object! entered1Id).status.chosenOdd == some false &&
    gFraEntDone.pending == .none &&
    (gFraEntDone.object! entered2Id).status.chosenOdd == some true &&
    entAtkFraBatches.size == 2 && entAtkFraBatches[0]! == entAtkFraBatches[1]!
  -- `dealAssignedCombatDamage` preserves `replacementOrder` across a mid-step lifelink `.chooseReplacement` pause and consumes `allApplied` once at the end.
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
  let gCbtDone :=
    (gCbtPaused.apply me (.chooseReplacement idCbtLifeAdd)).toOption.getD gCbtPaused
  let cbtLifelinkOrderOk :=
    gCbtPaused.pending == .chooseReplacement me #[idCbtLifeAdd, idCbtLifeMul] &&
    gCbtPaused.replacementOrder == #[idCbtMul] &&
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
    (gActiveMe.selectNextReplacement #[candOpp, candMe] #[]).map (·.id) == some idLifeMe &&
    (gActiveOpp.selectNextReplacement #[candOpp, candMe] #[]).map (·.id) == some idLifeOpp &&
    noUnclassifiedRulesEvents gDmgAddFirst &&
    noUnclassifiedRulesEvents gDmgMulFirst &&
    noUnclassifiedRulesEvents gFinChoseHead &&
    noUnclassifiedRulesEvents gFinChoseExile &&
    noUnclassifiedRulesEvents gShdFrom &&
    noUnclassifiedRulesEvents gArw1 &&
    noUnclassifiedRulesEvents gSimDone &&
    noUnclassifiedRulesEvents gSbaDone &&
    noUnclassifiedRulesEvents gFightDone &&
    noUnclassifiedRulesEvents gEntAtkDone &&
    noUnclassifiedRulesEvents gDrwSubDone &&
    noUnclassifiedRulesEvents gFraEntDone &&
    noUnclassifiedRulesEvents gCbtDone &&
    noUnclassifiedRulesEvents gLifeAddFirst &&
    noUnclassifiedRulesEvents gLifeMulFirst

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
    { (g0.change (.pushDelayedTrigger {
        controller := me
        source := some h
        kind := .endStepSacrifice b.id
        cause := cause8 })) with step := .postcombatMain }
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
  let gCont0 := g0.change (.continuation (.notedCountThisWay 7))
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
    noUnclassifiedRulesEvents gLayers &&
    noUnclassifiedRulesEvents gDelayed1 &&
    noUnclassifiedRulesEvents gPlEv

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
    (((g0.record (GameEvent.extraTurnAdded g0.turnNumber me .current (cause := some causeMe1))).record
        (GameEvent.extraTurnAdded g0.turnNumber me .current (cause := some causeMe2))).record
        (GameEvent.extraTurnAdded g0.turnNumber opp .current (cause := some causeOpp))).record
        (GameEvent.playerLost g0.turnNumber opp .effect (cause := some causeMe1))
  let gExtra1 := gQueued.startNextTurn
  let powerUpsCause? (g : Game) : Option EventCause :=
    g.events.findSomeRev? fun e =>
      match e.change with
      | .rules (.continuousEffect (.created _ .powerUpsForbiddenThisTurn)) => some e.cause
      | _ => none
  let gExtra2 := (gExtra1.clearEOT).startNextTurn
  gQueued.extraTurns == #[opp, me, me] &&
    gExtra1.activePlayer == me &&
    gExtra1.extraTurns == #[me] &&
    powerUpsCause? gExtra1 == some causeMe2 &&
    gExtra2.activePlayer == me &&
    gExtra2.extraTurns.isEmpty &&
    powerUpsCause? gExtra2 == some causeMe1 &&
    noUnclassifiedRulesEvents gExtra2

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
        (GameEvent.damageMarked g1.turnNumber b.id 1 (cause := some causeNext))
  let hasPlayPerm (g : Game) : Bool :=
    g.activeEffects.any fun (_, s) =>
      match s with
      | .permission p (.playFromExile oid _) _ => p == me && oid == exId
      | _ => false
  -- Turn 1 cleanup (emits `.cleanupClear` events from haste expiration and marked damage)
  let gClean1 := gInit.clearEOT
  let hadCleanupClear := gClean1.events.any (fun e => e.cause == .turnBased .cleanupClear)
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
    (gClean1.object! b.id).controller == some me &&
    gClean1.controlTurnEndsLeft (gClean1.object! b.id) == 2 &&
    hasPlayPerm gClean1 &&
    (gClean1b.object! b.id).controller == some me &&
    hasPlayPerm gClean1b &&
    gOppTurn.activePlayer == opp &&
    (gOppClean.object! b.id).controller == some me &&
    gOppClean.controlTurnEndsLeft (gOppClean.object! b.id) == 2 &&
    hasPlayPerm gOppClean &&
    gMeNext.activePlayer == me &&
    (gMeNext.object! b.id).controller == some me &&
    gMeNext.controlTurnEndsLeft (gMeNext.object! b.id) == 1 &&
    hasPlayPerm gMeNext &&
    (gMeNextClean.object! b.id).controller == some opp &&
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
    noUnclassifiedRulesEvents gSetOverride

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
      (GameEvent.attached g0.turnNumber aura.id w.id (cause := some c2))).recordPutCounters
      w.id .lifelink 1 (some me) (cause := some c3)
  let wAura := gBeforeAura.object! w.id
  let auraOk :=
    !gBeforeAura.hasVigilance wAura &&
    !gBeforeAura.hasDeathtouch wAura &&
    gBeforeAura.hasLifelink wAura &&
    gBeforeAura.effectiveKeywords wAura == Keyword.lifelink
  strippedOk && refreshedOk && auraOk &&
    noUnclassifiedRulesEvents gRefreshed &&
    noUnclassifiedRulesEvents gBeforeAura

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
    ((gT0.record (GameEvent.attached gT0.turnNumber kitesail.id cap.id (cause := some c1))).createEffect
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
    gCapLost.record (GameEvent.damagedPlayer gCapLost.turnNumber strikeSnap ⟨1⟩ 2 true (cause := some c3))
  let battleSnap : EventObject := { name := "TestBattle", owner := ⟨1⟩, zone := .battlefield }
  let gDmgBattleLost :=
    gCapLost.record
      { turn := gCapLost.turnNumber
        cause := c3
        change := .rules (.damage (.dealt #[{ source := strikeSnap, recipient := .battle battleSnap, amount := 2, combat := true }])) }
  -- Post-removal grant and post-removal re-attachment ARE retained and DO fire
  let gPostGrant :=
    (gCapLost.createEffect (.grantedTriggered cap.id postGrantAb true) (cause := some c3)).record
      (GameEvent.attached gCapLost.turnNumber kitesail.id cap.id (cause := some c4))
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
    gEq0.record (GameEvent.attached gEq0.turnNumber ring.id host.id (cause := some c1))
  let gRingLost :=
    gRingPre.createEffect (.losesAbilitiesUntilEot host.id) (cause := some c2)
  let gRingRe :=
    gRingLost.record (GameEvent.attached gRingLost.turnNumber ring.id host.id (cause := some c3))
  let gPrecPre :=
    gEq0.record (GameEvent.attached gEq0.turnNumber precious.id host.id (cause := some c1))
  let gPrecLost :=
    gPrecPre.createEffect (.losesAbilitiesUntilEot host.id) (cause := some c2)
  let gPrecRe :=
    gPrecLost.record (GameEvent.attached gPrecLost.turnNumber precious.id host.id (cause := some c3))
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
    gPw0.record (GameEvent.attached gPw0.turnNumber staff.id mage.id (cause := some c1))
  let gPwLost :=
    gPwPre.createEffect (.losesAbilitiesUntilEot mage.id) (cause := some c2)
  let gPwRe :=
    gPwLost.record (GameEvent.attached gPwLost.turnNumber staff.id mage.id (cause := some c3))
  let prowessOk :=
    (gPwPre.prowessTriggers (gPwPre.object! mage.id)).size == 2 &&
    (gPwLost.prowessTriggers (gPwLost.object! mage.id)).isEmpty &&
    !(gPwLost.effectiveKeywords (gPwLost.object! mage.id)).prowess &&
    (gPwRe.prowessTriggers (gPwRe.object! mage.id)).size == 1 &&
    (gPwRe.effectiveKeywords (gPwRe.object! mage.id)).prowess
  triggersOk && unblockableOk && prowessOk &&
    noUnclassifiedRulesEvents gAtkPost &&
    noUnclassifiedRulesEvents gRingRe &&
    noUnclassifiedRulesEvents gPrecRe &&
    noUnclassifiedRulesEvents gPwRe

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
      (GameEvent.attached gTr0.turnNumber cleaver.id atk.id (cause := some c1))).createEffect
      (.combatDamageCreatesTreasureUntilEot atk.id) (cause := some c1)
  let gTrLost :=
    gTrPre.createEffect (.losesAbilitiesUntilEot atk.id) (cause := some c2)
  let gTrLostCombat :=
    { gTrLost with assignedCombatDamage := #[{ source := atk.id, toPlayer := 2 }] }.dealAssignedCombatDamage
  let gTrRe :=
    gTrLost.record (GameEvent.attached gTrLost.turnNumber cleaver.id atk.id (cause := some c3))
  let gTrReCombat :=
    { gTrRe with assignedCombatDamage := #[{ source := atk.id, toPlayer := 2 }] }.dealAssignedCombatDamage
  let gTrPostEff :=
    gTrLost.createEffect (.combatDamageCreatesTreasureUntilEot atk.id) (cause := some c4)
  let countTreasures (g : Game) : Nat :=
    (g.permanentsOf me).filter (fun o => g.hasSubtype o .treasure) |>.size
  let treasureOk :=
    gTrPre.combatDamageCreatesTreasure (gTrPre.object! atk.id) &&
    !gTrLost.combatDamageCreatesTreasure (gTrLost.object! atk.id) &&
    countTreasures gTrLostCombat == 0 &&
    gTrRe.combatDamageCreatesTreasure (gTrRe.object! atk.id) &&
    countTreasures gTrReCombat == 2 &&
    gTrPostEff.combatDamageCreatesTreasure (gTrPostEff.object! atk.id)
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
    gFistPost.record (GameEvent.attached gFistPost.turnNumber stripAura.id fist.id (cause := some c4))
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
    gWd0.record (GameEvent.attached gWd0.turnNumber wCloak.id wHero.id (cause := some c1))
  let preWards := gWdPre.wardCostsOn (gWdPre.object! wHero.id)
  let gWdLost :=
    gWdPre.createEffect (.losesAbilitiesUntilEot wHero.id) (cause := some c2)
  let lostWards := gWdLost.wardCostsOn (gWdLost.object! wHero.id)
  let gWdRe :=
    addPermanent
      (gWdLost.record (GameEvent.attached gWdLost.turnNumber wCloak.id wHero.id (cause := some c3)))
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
    noUnclassifiedRulesEvents gTrReCombat &&
    noUnclassifiedRulesEvents gFistAuraLost &&
    noUnclassifiedRulesEvents gWdRe

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
    (addPermanent (quiet afterDraw) angelDef me me).changePlayer me (.life 0)
  let angel := (gAngel0.battlefield.filter (·.name == "Platinum Test"))[0]!
  let gAngelPre := gAngel0.checkSBA
  let gAngelLost :=
    (gAngel0.createEffect (.losesAbilitiesUntilEot angel.id) (cause := some c1)).checkSBA
  let (gCmd0, cmdObj) :=
    ((quiet afterDraw).changePlayer me (.life 0)).allocObject angelDef me .command (some me)
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
    (addPermanent (quiet afterDraw) horizonDef me me).changePlayer me
      (.manaPool ((ManaPool.empty).add (.colored .red)))
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
    noUnclassifiedRulesEvents gAngelLost &&
    noUnclassifiedRulesEvents gManaKept &&
    noUnclassifiedRulesEvents gManaLost &&
    noUnclassifiedRulesEvents gPwRe &&
    noUnclassifiedRulesEvents gGrRe &&
    noUnclassifiedRulesEvents gMtnReLantern

end Mtg.Engine.EventTests
