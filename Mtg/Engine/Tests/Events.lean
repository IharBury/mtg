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
    | .rules (.effectApplied _ (.drew p _ _ _)) => p == me
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
          | .rules (.effectApplied _ (.moved _ _ .exile _ _)) => true
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

/- Rule 610: applications of one-shot effects (drawing cards, moving objects
between zones, creating tokens, scrying/surveilling) receive unique `EffectId`s,
whereas durable `RulesEvent`s (`LifeEvent`, `PermanentEvent`, `DamageEvent`)
record state changes directly without minting synthetic `OneShotEffect`s. -/
#guard
  let g0 := quiet (addPermanent afterDraw bear me me)
  let b := (g0.battlefield.filter (·.name == "Event Bear"))[0]!
  let effId0 := g0.nextEffectId
  let gUnclassified :=
    ((g0.gainLife me 3).loseLife me 2).record
      (GameEvent.tapped g0.turnNumber b.asEvent true true)
  let unclassifiedDidNotAdvance :=
    gUnclassified.nextEffectId == effId0 &&
      (GameEvent.appliedEffectsWithId gUnclassified.events).isEmpty
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
  let hasToken := effs.any (fun | .created p obj => p == me && obj.token | _ => false)
  let hasGain := g7.events.any (fun e => e.change == .rules (.life (.gained me 3)))
  let hasLoss := g7.events.any (fun e => e.change == .rules (.life (.lost me 2 false false)))
  let hasCounters := g7.events.any (fun e =>
    match e.change with
    | .rules (.permanent (.counters (.object obj) .plusOnePlusOne (.put 2) _)) => obj.id == b.id
    | _ => false)
  let hasTap := g7.events.any (fun e =>
    match e.change with
    | .rules (.permanent (.tapped obj true)) => obj.id == b.id
    | _ => false)
  let hasUntap := g7.events.any (fun e =>
    match e.change with
    | .rules (.permanent (.untapped obj)) => obj.id == b.id
    | _ => false)
  unclassifiedDidNotAdvance && uniqueIds && ids.size >= 3 &&
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
  -- Apply two separate pump continuous effects and a life gain without creating any objects.
  let g1 := ((g0.createEffect (.pump b.id 2 2)).gainLife me 4).createEffect (.pump b.id 1 3)
  let objIdUnchanged := g1.nextObjectId == objIdBefore
  let createdPairs := GameEvent.createdEffectsWithId g1.events
  let appliedPairsBeforeToken := GameEvent.appliedEffectsWithId g1.events
  -- Now create a token (which increments `nextObjectId` AND emits a one-shot `created` effect).
  let g2 := g1.createTreasureTokens me 1
  let appliedPairs := GameEvent.appliedEffectsWithId g2.events
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
    !bearToHero.matchesTrigger me h.id .heroesDealDamageToPlayer

end Mtg.Engine.EventTests
