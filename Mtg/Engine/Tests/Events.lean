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
  let g1 := (g0.applyChange (.effectCreated ⟨100⟩ pump)).applyChange (.effectCreated ⟨101⟩ pump)
  let g2 := g1.applyChange (.effectExpired ⟨101⟩ pump)
  let g3 := g2.applyChange (.effectExpired ⟨999⟩ pump)
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
  let g1 := (g0.dealDamageLoseIndestructibleExileTo b 1).grantCantBeBlockedThisTurn b
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
time counters are later moved onto it (CR 702.176, ruling 970). -/
#guard
  let impDef : CardDef :=
    { bear with
      name := "Impending Bear"
      impending := some (1, ManaCost.empty) }
  let g0 := insertObject afterDraw impDef me (.hand me) none {} (fun id _ => #[.pushHand id])
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
        let g3 := (quiet g2).changeStatus permId .withoutCounters
        let g4 := (quiet g3).changeStatus permId (.addCountersExceptPlusOne { time := 2 })
        let created4 := GameEvent.createdEffectsWithId g4.events
        (GameEvent.createdEffectsWithId g1.events).isEmpty &&
          (g1.object! spellId).isCreature &&
          g2.activeEffect? eid1 == some (.notACreature permId) &&
          !(g2.object! permId).isCreature &&
          (GameEvent.expiredEffectsWithId g3.events).map Prod.fst == #[eid1] &&
          (g3.activeEffect? eid1).isNone &&
          (g3.object! permId).isCreature &&
          created4.size == 1 &&
          created4[0]!.1 != eid1 &&
          g4.activeEffect? created4[0]!.1 == some (.notACreature permId) &&
          !(g4.object! permId).isCreature

end Mtg.Engine.EventTests
