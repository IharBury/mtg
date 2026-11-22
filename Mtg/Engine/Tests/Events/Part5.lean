import Mtg.Engine.Tests.Events.Base

namespace Mtg.Engine.EventTests

open Mtg.Engine
open Mtg.Engine.Catalog
open Mtg.Engine.Tests

section Phase24Item4EventAlignment

def opp24i4 : PlayerId := ⟨1⟩

def mustHold24i4 (label : String) (ok : Bool) : Bool :=
  if ok then true else panic! s!"Phase 24 item 4 guard failed: {label}"

def replayOk24i4 (gs : Array Game) : Bool :=
  gs.all (fun g => Game.replayEvents g.events == g && allRulesEventsClassified g)

def mkTwoHeadedGiant24i4 (seed : UInt64 := 244) : Game :=
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

def mkThreePlayer24i4 (seed : UInt64 := 245) : Game :=
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

-- 1. CR 514.2 / 602.5b / 603.2h / 606.3 / 805.4 / 805.4c / 810.2:
--    Two-Headed Giant shared-turn `turnNumber`, `"this turn"` queries, cleanup expiry, and `damageMarkedCleared`.
#guard
  let zeroZero24i4 : CardDef := creature "P24i4 0/0" ManaCost.empty #["Spirit"] 0 0
  let onceAbDef : CardDef := {
    bear with
    name := "P24i4 Once-Per-Turn Bear"
    activatedAbilities := #[
      activated (Effect.gainLife 1) (ManaCost.empty) (turnLimit? := some 1)
    ]
  }
  let pwDef : CardDef := {
    name := "P24i4 Shared-Turn Walker"
    types := #[.planeswalker]
    loyalty := some 4
    activatedAbilities := #[
      { cost := CostSpec.ofItems #[.loyalty (.plus 1)], effect := Effect.gainLife 1 }
    ]
  }
  let g0 : Game :=
    addPermanent
      (insertObject (addPermanent mkTwoHeadedGiant24i4 onceAbDef ⟨0⟩ ⟨0⟩) pwDef ⟨0⟩ .battlefield (some ⟨0⟩)
        { summoningSick := false, counters := #[(.loyalty, 4)] })
      zeroZero24i4 ⟨0⟩ ⟨0⟩
  let bearId := (g0.battlefield.filter (·.name == onceAbDef.name))[0]!.id
  let pwId := (g0.battlefield.filter (·.name == pwDef.name))[0]!.id
  -- Mark 1 nonlethal damage, grant +1/+1 until EOT, die 1 creature, activate once-each-turn & loyalty, play 1 land for `⟨0⟩`:
  let g1 : Game :=
    let g := g0.checkSBA
    let g := g.dealDamageToPermanent (g.object! bearId) 1 (cause := some testCause)
    let g := g.createEffect (.pump bearId 1 1) (cause := some testCause)
    let g := mustApply g ⟨0⟩ (.activate bearId 0)
    let g := mustApply (mustApply (mustApply (mustApply g ⟨0⟩ .pass) ⟨1⟩ .pass) ⟨2⟩ .pass) ⟨3⟩ .pass
    let g := mustApply g ⟨0⟩ (.activate pwId 0)
    let g := mustApply (mustApply (mustApply (mustApply g ⟨0⟩ .pass) ⟨1⟩ .pass) ⟨2⟩ .pass) ⟨3⟩ .pass
    let mtnCard := insertObject g mountain ⟨0⟩ (.hand ⟨0⟩)
    let mtnId := ((mtnCard.player ⟨0⟩).hand.filter (fun id => (mtnCard.object! id).name == mountain.name))[0]!
    mustApply mtnCard ⟨0⟩ (.playLand mtnId)
  let preAdvanceIdx := g1.events.size
  -- Run Seat `⟨0⟩`'s cleanup step -> advances to teammate Seat `⟨1⟩` (still the same shared turn!):
  let gSeat1 : Game := g1.beginStep .cleanup
  let midClearedEvts := (gSeat1.events.extract preAdvanceIdx gSeat1.events.size).filter fun e =>
    match e.change with | .rules (.damage (.markedCleared _)) => true | _ => false
  -- Run Seat `⟨1⟩`'s cleanup step (`isSharedTurnFinalSeat`) -> clears EOT & damage and advances to opposing Seat `⟨2⟩`:
  let preFinalIdx := gSeat1.events.size
  let gSeat2 : Game := gSeat1.beginStep .cleanup
  let finalClearedEvts := (gSeat2.events.extract preFinalIdx gSeat2.events.size).filter fun e =>
    match e.change with | .rules (.damage (.markedCleared _)) => true | _ => false

  let sharedTurnLifecycleOk :=
    !g1.isSharedTurnFinalSeat &&
    g1.turnNumber == 1 &&
    -- On Seat `⟨1⟩`, `turnNumber` stays 1, EOT pump & marked damage persist, and `"this turn"` queries stay active:
    gSeat1.activePlayer == ⟨1⟩ &&
    gSeat1.turnNumber == 1 &&
    gSeat1.isSharedTurnFinalSeat &&
    (gSeat1.object! bearId).status.damage == 1 &&
    gSeat1.power (gSeat1.object! bearId) == 3 &&
    midClearedEvts.isEmpty &&
    gSeat1.activationsThisTurn bearId == 1 &&
    (gSeat1.abilitiesActivatedThisTurn bearId).contains 0 &&
    gSeat1.loyaltyActivatedThisTurn pwId &&
    gSeat1.loggedCreatureDeaths == 1 &&
    -- Per-player land play count (CR 805.4c): `⟨0⟩` played 1 land this turn, while `⟨1⟩` played 0:
    gSeat1.loggedLandsPlayed ⟨0⟩ == 1 &&
    gSeat1.loggedLandsPlayed ⟨1⟩ == 0 &&
    -- After Seat `⟨1⟩` finishes the shared turn, `turnNumber` increments to 2, EOT & damage clear, and `"this turn"` resets:
    gSeat2.activePlayer == ⟨2⟩ &&
    gSeat2.turnNumber == 2 &&
    (gSeat2.object! bearId).status.damage == 0 &&
    gSeat2.power (gSeat2.object! bearId) == 2 &&
    finalClearedEvts.size == 1 &&
    gSeat2.activationsThisTurn bearId == 0 &&
    !gSeat2.loyaltyActivatedThisTurn pwId &&
    gSeat2.loggedCreatureDeaths == 0

  mustHold24i4 "1.sharedTurnLifecycleOk" sharedTurnLifecycleOk &&
  mustHold24i4 "1.replay" (replayOk24i4 #[g1, gSeat1, gSeat2])

-- 2. CR 805.4a / 810.2: Active-team `"during your turn"` / `"on your turn"` checks across all 7 sites.
#guard
  let duringAbDef : CardDef := {
    bear with
    name := "P24i4 During-Your-Turn Bear"
    activatedAbilities := #[
      activated (Effect.gainLife 1) (ManaCost.empty) (condition? := some .isYourTurn)
    ]
  }
  let fsSelfDef : CardDef := {
    bear with
    name := "P24i4 First Strike Self"
    staticAbilities := #[.firstStrikeDuringYourTurn]
  }
  let eqLordDef : CardDef := {
    bear with
    name := "P24i4 Equipped Team Lord"
    staticAbilities := #[.equippedCreaturesHaveKeywordsDuringYourTurn #[Keyword.vigilance]]
  }
  let eqHexUnblockDef : CardDef := {
    name := "P24i4 Cloak Equipment"
    types := #[.artifact]
    subtypes := #["Equipment"]
    staticAbilities := #[.equippedHexproofUnblockableDuringYourTurn]
  }
  let plainEqDef : CardDef := {
    name := "P24i4 Plain Equipment"
    types := #[.artifact]
    subtypes := #["Equipment"]
  }
  let oppCombatDmgWatcherDef : CardDef := {
    bear with
    name := "P24i4 Combat Dmg Watcher"
    triggeredAbilities := #[
      TriggeredAbility.mkTrigger .opponentsDealtCombatDamageYourTurn
        { body := Instruction.gainLifeFixed 1, phrase := "You gain 1 life." }
        (grouping := .oncePerBatch)
    ]
  }
  -- Active player is `⟨0⟩` (Team A = `⟨0⟩, ⟨1⟩`; Team B = `⟨2⟩, ⟨3⟩`):
  let gBase := mkTwoHeadedGiant24i4
  let gAct :=
    (addPermanent (addPermanent gBase duringAbDef ⟨1⟩ ⟨1⟩) duringAbDef ⟨2⟩ ⟨2⟩)
  let mateAbId := (gAct.battlefield.filter (fun o => o.name == duringAbDef.name && o.controller == some ⟨1⟩))[0]!.id
  let oppAbId := (gAct.battlefield.filter (fun o => o.name == duringAbDef.name && o.controller == some ⟨2⟩))[0]!.id
  let mateActOk := ((gAct.change (.priority ⟨1⟩)).apply ⟨1⟩ (.activate mateAbId 0)).isOk
  let oppActBlocked := !((gAct.change (.priority ⟨2⟩)).apply ⟨2⟩ (.activate oppAbId 0)).isOk

  let gKw :=
    let g := addPermanent (addPermanent gBase fsSelfDef ⟨1⟩ ⟨1⟩) fsSelfDef ⟨2⟩ ⟨2⟩
    let g := addPermanent (addPermanent g eqLordDef ⟨1⟩ ⟨1⟩) eqLordDef ⟨2⟩ ⟨2⟩
    let g := addPermanent (addPermanent g bear ⟨1⟩ ⟨1⟩) bear ⟨2⟩ ⟨2⟩
    let g := addPermanent (addPermanent g plainEqDef ⟨1⟩ ⟨1⟩) plainEqDef ⟨2⟩ ⟨2⟩
    let g := addPermanent (addPermanent g eqHexUnblockDef ⟨1⟩ ⟨1⟩) eqHexUnblockDef ⟨2⟩ ⟨2⟩
    let mateBear := (g.battlefield.filter (fun o => o.name == bear.name && o.controller == some ⟨1⟩))[0]!
    let oppBear := (g.battlefield.filter (fun o => o.name == bear.name && o.controller == some ⟨2⟩))[0]!
    let mateEq := (g.battlefield.filter (fun o => o.name == plainEqDef.name && o.controller == some ⟨1⟩))[0]!
    let oppEq := (g.battlefield.filter (fun o => o.name == plainEqDef.name && o.controller == some ⟨2⟩))[0]!
    let mateCloak := (g.battlefield.filter (fun o => o.name == eqHexUnblockDef.name && o.controller == some ⟨1⟩))[0]!
    let oppCloak := (g.battlefield.filter (fun o => o.name == eqHexUnblockDef.name && o.controller == some ⟨2⟩))[0]!
    let g := ((g.attachSourceTo mateEq mateBear).attachSourceTo oppEq oppBear)
    let g := ((g.attachSourceTo mateCloak (g.object! mateBear.id)).attachSourceTo oppCloak (g.object! oppBear.id))
    (g.createEffect (.firstStrikeOnYourTurn mateBear.id) (cause := some testCause)).createEffect
      (.firstStrikeOnYourTurn oppBear.id) (cause := some testCause)
  let mateSelf := (gKw.battlefield.filter (fun o => o.name == fsSelfDef.name && o.controller == some ⟨1⟩))[0]!
  let oppSelf := (gKw.battlefield.filter (fun o => o.name == fsSelfDef.name && o.controller == some ⟨2⟩))[0]!
  let mateHost := (gKw.battlefield.filter (fun o => o.name == bear.name && o.controller == some ⟨1⟩))[0]!
  let oppHost := (gKw.battlefield.filter (fun o => o.name == bear.name && o.controller == some ⟨2⟩))[0]!

  -- `.opponentsDealtCombatDamageYourTurn`: combat damage to `⟨2⟩` during `⟨0⟩`'s turn fires `⟨1⟩`'s watcher, not `⟨3⟩`'s:
  let gTrig0 :=
    addPermanent (addPermanent gBase oppCombatDmgWatcherDef ⟨1⟩ ⟨1⟩) oppCombatDmgWatcherDef ⟨3⟩ ⟨3⟩
  let mateWId := (gTrig0.battlefield.filter (fun o => o.name == oppCombatDmgWatcherDef.name && o.controller == some ⟨1⟩))[0]!.id
  let gTrig1 := gTrig0.withBatch (some testCause) fun g =>
    g.record (GameEvent.damagedPlayer g.turnNumber (g.snapshot (g.object! mateWId)) ⟨2⟩ 2 (combat := true) (cause := testCause))

  -- `Triggers.becomeTapped`: `during == true` for teammate `⟨1⟩` and `false` for opponent `⟨2⟩`:
  let gTap1 := gKw.becomeTapped mateHost (cause := some testCause)
  let gTap2 := gTap1.becomeTapped oppHost (cause := some testCause)
  let tapDuringOf (oid : ObjectId) : Option Bool :=
    gTap2.events.findSomeRev? fun e =>
      match e.change with
      | .rules (.permanent (.tapped eo d)) => if eo.id == some oid then some d else none
      | _ => none

  -- Jace tax trigger: no-op for active teammate `⟨1⟩`, prompts `⟨0⟩` with `{2}` for opponent `⟨2⟩`, and scopes `.cantAttackJaces` to `⟨2⟩`'s Jaces on decline:
  let jacePw24i4 : CardDef := { name := "Jace, Test Sculptor", types := #[.planeswalker], subtypes := #["Jace"], loyalty := some 3 }
  let gJaceBoard :=
    insertObject
      (insertObject gBase jacePw24i4 ⟨2⟩ .battlefield (some ⟨2⟩) { summoningSick := false, counters := #[(.loyalty, 3)] })
      jacePw24i4 ⟨3⟩ .battlefield (some ⟨3⟩) { summoningSick := false, counters := #[(.loyalty, 3)] }
  let jace2Obj := (gJaceBoard.battlefield.filter (fun o => o.name == jacePw24i4.name && o.controller == some ⟨2⟩))[0]!
  let jace3Obj := (gJaceBoard.battlefield.filter (fun o => o.name == jacePw24i4.name && o.controller == some ⟨3⟩))[0]!
  let jaceTaxEff := jaceMultiverseArchitect.triggeredAbilities[0]!.effect
  let gJaceMate := gJaceBoard.applyAbilityEffect ⟨1⟩ jaceTaxEff #[]
  let gJacePrompt := (gJaceBoard.change (.pushContinuationFrame {})).applyAbilityEffect ⟨2⟩ jaceTaxEff #[]
  let gJaceOpp := mustApply gJacePrompt ⟨0⟩ .decline

  let activeTeamDuringYourTurnOk :=
    gBase.isOnActiveTeam ⟨0⟩ &&
    gBase.isOnActiveTeam ⟨1⟩ &&
    !gBase.isOnActiveTeam ⟨2⟩ &&
    mateActOk &&
    oppActBlocked &&
    gKw.hasFirstStrike mateSelf &&
    !gKw.hasFirstStrike oppSelf &&
    gKw.hasVigilance mateHost &&
    !gKw.hasVigilance oppHost &&
    gKw.hasHexproof mateHost &&
    gKw.hasCantBeBlocked mateHost &&
    !gKw.hasHexproof oppHost &&
    !gKw.hasCantBeBlocked oppHost &&
    gKw.hasFirstStrike mateHost &&
    !gKw.hasFirstStrike oppHost &&
    gTrig1.waitingTriggers.size == 1 &&
    gTrig1.waitingTriggers[0]!.controller == ⟨1⟩ &&
    tapDuringOf mateHost.id == some true &&
    tapDuringOf oppHost.id == some false &&
    gJaceMate.pending == .none &&
    !gJaceMate.cantAttackJace ⟨0⟩ jace2Obj &&
    (match gJacePrompt.pending with | .payOrLetCounter ⟨0⟩ 2 none => true | _ => false) &&
    gJaceOpp.cantAttackJace ⟨0⟩ (gJaceOpp.object! jace2Obj.id) &&
    !gJaceOpp.cantAttackJace ⟨0⟩ (gJaceOpp.object! jace3Obj.id)

  mustHold24i4 "2.activeTeamDuringYourTurnOk" activeTeamDuringYourTurnOk &&
  mustHold24i4 "2.replay" (replayOk24i4 #[gKw, gTrig1, gTap2, gJaceMate, gJacePrompt, gJaceOpp])

-- 3. CR 102.3 / 103.1a / 723.5 / 800.4a,m / 805.3 / 805.8 / 805.10a / 810.2 / 810.8a / 810.11:
--    Starting team first seat (`Start.startWithRng`), CR 805.8 shared team extra turns,
--    all 6 `matchesTrigger` `opp` arms, player-control edge cases, and `3+`-seat team win logs.
#guard
  -- 3a. `Start.startWithRng` with `startingPlayer := none` picks only team first seats (`⟨0⟩` or `⟨2⟩`):
  let startSeats := (Array.range 16).map fun s =>
    match Start.start {
      seats := #[
        { name := "Chandra", deck := testRedDeck, teammate := some ⟨1⟩ },
        { name := "Nissa", deck := testGreenDeck, teammate := some ⟨0⟩ },
        { name := "Liliana", deck := testRedDeck, teammate := some ⟨3⟩ },
        { name := "Jace", deck := testGreenDeck, teammate := some ⟨2⟩ }
      ]
      format := .constructed
      seed := (s + 1).toUInt64
      startingPlayer := none
    } with
    | .ok g => g.startingPlayer
    | .error e => panic! e
  let startTeamFirstSeatOk :=
    startSeats.all (fun p => p == ⟨0⟩ || p == ⟨2⟩) &&
    startSeats.contains ⟨0⟩ &&
    startSeats.contains ⟨2⟩

  -- 3b. CR 805.8 shared team extra turns:
  --     On Seat `⟨0⟩`'s regular turn 1, `Effect.extraTurn` for teammate `⟨1⟩` queues `#[⟨0⟩, ⟨1⟩]`,
  --     finishes regular Seat `⟨1⟩` (turn 1) first, then runs extra Seat `⟨0⟩` -> extra Seat `⟨1⟩` (both turn 2,
  --     `powerUpsForbidden`), then advances to opposing Seat `⟨2⟩` (turn 3, `!powerUpsForbidden`):
  let gEx0 := mkTwoHeadedGiant24i4
  let gExQueued := gEx0.applyEffect ⟨1⟩ { body := .turn (.extraTurn .you) } #[]
  let gExRegMate := gExQueued.startNextTurnAndBegin
  let gExTurnSeat0 := gExRegMate.startNextTurnAndBegin
  let gExTurnSeat1 := gExTurnSeat0.startNextTurnAndBegin
  let gExAfter := gExTurnSeat1.startNextTurnAndBegin
  let sharedExtraTurnOk :=
    gExQueued.log.any (·.contains "Chandra and Nissa take an extra turn") &&
    gExQueued.extraTurns == #[⟨0⟩, ⟨1⟩] &&
    gExRegMate.activePlayer == ⟨1⟩ &&
    gExRegMate.turnNumber == 1 &&
    !gExRegMate.powerUpsForbidden &&
    gExRegMate.extraTurns == #[⟨0⟩, ⟨1⟩] &&
    gExTurnSeat0.activePlayer == ⟨0⟩ &&
    gExTurnSeat0.turnNumber == 2 &&
    gExTurnSeat0.powerUpsForbidden &&
    gExTurnSeat0.extraTurns == #[⟨1⟩] &&
    !gExTurnSeat0.isSharedTurnFinalSeat &&
    gExTurnSeat1.activePlayer == ⟨1⟩ &&
    gExTurnSeat1.turnNumber == 2 &&
    gExTurnSeat1.powerUpsForbidden &&
    gExTurnSeat1.extraTurns.isEmpty &&
    gExTurnSeat1.isSharedTurnFinalSeat &&
    gExAfter.activePlayer == ⟨2⟩ &&
    gExAfter.turnNumber == 3 &&
    !gExAfter.powerUpsForbidden

  -- 3c. All 6 `GameEvent.matchesTrigger` `opp` arms exclude teammates (`⟨1⟩`) and match opponents (`⟨2⟩`):
  let gSnap := addPermanent gEx0 bear ⟨1⟩ ⟨1⟩
  let smallSnap := { (gSnap.snapshot (gSnap.battlefield[0]!)) with power := some 1 }
  let isMate := fun (p : PlayerId) => p == ⟨1⟩
  let eAtkYouMate := GameEvent.attackersDeclared 1 ⟨1⟩ #[(smallSnap, .player ⟨0⟩)]
  let eAtkYouOpp := GameEvent.attackersDeclared 1 ⟨2⟩ #[(smallSnap, .player ⟨0⟩)]
  let eAtkOppVsMate := GameEvent.attackersDeclared 1 ⟨0⟩ #[(smallSnap, .player ⟨1⟩)]
  let eAtkOppVsOpp := GameEvent.attackersDeclared 1 ⟨0⟩ #[(smallSnap, .player ⟨2⟩)]
  let eBlkMate := GameEvent.blockersDeclared 1 ⟨1⟩ #[({ smallSnap with controller := some ⟨1⟩ }, ⟨99⟩)]
  let eBlkOpp := GameEvent.blockersDeclared 1 ⟨2⟩ #[({ smallSnap with controller := some ⟨2⟩ }, ⟨99⟩)]
  let eBegCombatMate := GameEvent.stepBegan 1 .beginningOfCombat (active := ⟨1⟩)
  let eBegCombatOpp := GameEvent.stepBegan 1 .beginningOfCombat (active := ⟨2⟩)
  let eDrawStepMate := GameEvent.stepBegan 1 .draw (active := ⟨1⟩)
  let eDrawStepOpp := GameEvent.stepBegan 1 .draw (active := ⟨2⟩)
  let eLoyaltyMate := GameEvent.abilityActivated 1 ⟨99002⟩ smallSnap ⟨1⟩
    (.nonMana (some 1) false false false none false) (cause := some testCause)
  let eLoyaltyOpp := GameEvent.abilityActivated 1 ⟨99003⟩ smallSnap ⟨2⟩
    (.nonMana (some 1) false false false none false) (cause := some testCause)
  let matchesOppArmsOk :=
    !eAtkYouMate.matchesTriggerPattern ⟨0⟩ none .creatureAttacksYouOrYourPlaneswalker (isTeammate := isMate) &&
    eAtkYouOpp.matchesTriggerPattern ⟨0⟩ none .creatureAttacksYouOrYourPlaneswalker (isTeammate := isMate) &&
    !eAtkOppVsMate.matchesTriggerPattern ⟨0⟩ none .creaturesAttackYourOpponent (isTeammate := isMate) &&
    eAtkOppVsOpp.matchesTriggerPattern ⟨0⟩ none .creaturesAttackYourOpponent (isTeammate := isMate) &&
    !eBlkMate.matchesTriggerPattern ⟨0⟩ none .opponentSmallCreatureBlocks (isTeammate := isMate) &&
    eBlkOpp.matchesTriggerPattern ⟨0⟩ none .opponentSmallCreatureBlocks (isTeammate := isMate) &&
    !eBegCombatMate.matchesTriggerPattern ⟨0⟩ none (.stepBegins .beginningOfCombat (.player .opponent)) (isTeammate := isMate) &&
    eBegCombatOpp.matchesTriggerPattern ⟨0⟩ none (.stepBegins .beginningOfCombat (.player .opponent)) (isTeammate := isMate) &&
    !eDrawStepMate.matchesTriggerPattern ⟨0⟩ none .stepEachOpponentDrawStep (isTeammate := isMate) &&
    eDrawStepOpp.matchesTriggerPattern ⟨0⟩ none .stepEachOpponentDrawStep (isTeammate := isMate) &&
    !eLoyaltyMate.matchesTriggerPattern ⟨0⟩ none .opponentActivatesLoyaltyAbility (isTeammate := isMate) &&
    eLoyaltyOpp.matchesTriggerPattern ⟨0⟩ none .opponentActivatesLoyaltyAbility (isTeammate := isMate)

  -- 3d. Player-control edge cases:
  --     (i) `.controlsPlayer ⟨2⟩ true` in `expireUntilNextTurnEffects ⟨3⟩` stays while teammate `⟨2⟩` lives,
  --         and expires via `g.areTeammates ⟨2⟩ ⟨3⟩` once both teammates have `.lost == true`;
  --     (ii) `controllingPlayerOf?` returns `some ⟨1⟩` while `⟨1⟩` lives and `none` once `(g.player ⟨1⟩).lost`:
  let gCtrlEdge0 :=
    gEx0.createEffect (.playerControl ⟨0⟩ ⟨2⟩ true) (cause := some testCause)
  let gCtrlMateAlive := gCtrlEdge0.expireUntilNextTurnEffects ⟨3⟩
  let gCtrlTeamLost :=
    ((gCtrlEdge0.record (GameEvent.playerLost 1 ⟨2⟩ .lifeZeroOrLess (cause := some (.stateBased .lifeZeroOrLess)))).record
      (GameEvent.playerLost 1 ⟨3⟩ .lifeZeroOrLess (cause := some (.stateBased .lifeZeroOrLess)))).expireUntilNextTurnEffects ⟨3⟩
  let gLiveCtrl0 := mkThreePlayer24i4.createEffect (.playerControl ⟨1⟩ ⟨2⟩ false) (cause := some testCause)
  let gLostCtrl0 :=
    gLiveCtrl0.record (GameEvent.playerLost 1 ⟨1⟩ .lifeZeroOrLess (cause := some (.stateBased .lifeZeroOrLess)))
  let playerControlEdgeOk :=
    !gCtrlMateAlive.controlOnNextTakenTurn.isEmpty &&
    gCtrlTeamLost.controlOnNextTakenTurn.isEmpty &&
    gLiveCtrl0.controllingPlayerOf? ⟨2⟩ == some ⟨1⟩ &&
    gLostCtrl0.controllingPlayerOf? ⟨2⟩ == none

  -- 3e. `3+`-seat team win logs in `Leaving.decideGameIfFinished` and `TriggeredAbilities`:
  let gTriTeam : Game :=
    match Start.start {
      seats := #[
        { name := "P0", deck := testRedDeck, teammate := some ⟨1⟩ },
        { name := "P1", deck := testGreenDeck, teammate := some ⟨2⟩ },
        { name := "P2", deck := testRedDeck, teammate := some ⟨0⟩ },
        { name := "P3", deck := testGreenDeck }
      ]
      format := .constructed
      seed := 246
      startingPlayer := some 0
    } with
    | .ok g => (keepOpeningHands g 30).advanceStep
    | .error e => panic! e
  let gTriConcede := gTriTeam.concede ⟨3⟩
  let winTrigAb : TriggeredAbility :=
    TriggeredAbility.mkTrigger .stepYourUpkeep (Effect.gainLife 1)
  let gTriTrigWin := gTriTeam.applyTriggeredAbility ⟨0⟩ winTrigAb none (resolutionOverride := some .winTheGame)
  let threeSeatWinLogsOk :=
    gTriConcede.over &&
    gTriConcede.log.any (· == "P0, P1, and P2 win the game") &&
    gTriTrigWin.over &&
    gTriTrigWin.log.any (· == "P0, P1, and P2 win the game")

  mustHold24i4 "3a.startTeamFirstSeatOk" startTeamFirstSeatOk &&
  mustHold24i4 "3b.sharedExtraTurnOk" sharedExtraTurnOk &&
  mustHold24i4 "3c.matchesOppArmsOk" matchesOppArmsOk &&
  mustHold24i4 "3d.playerControlEdgeOk" playerControlEdgeOk &&
  mustHold24i4 "3e.threeSeatWinLogsOk" threeSeatWinLogsOk &&
  mustHold24i4 "3.replay" (replayOk24i4 #[gExQueued, gExRegMate, gExTurnSeat0, gExTurnSeat1, gExAfter, gCtrlMateAlive, gCtrlTeamLost, gLiveCtrl0, gLostCtrl0, gTriConcede, gTriTrigWin])

-- 4. CR 704.3 / 704.5j / 704.8 / 800.4a:
--    Start-of-pass CR 704.5j `legendRuleGroups` evaluated before
--    `GameEvent.playerLost`, CR 704.5q counter annihilation, `dyingCreatures`, and `pwMoves`.
#guard
  let zeroZero24i4 : CardDef := creature "P24i4 0/0" ManaCost.empty #["Spirit"] 0 0
  let legDiesWatcherDef : CardDef := {
    legendaryCreature "P24i4 Dying Legend" ManaCost.empty #["Spirit"] 2 2 with
    triggeredAbilities := #[
      TriggeredAbility.mkTrigger .thisDies { body := Instruction.gainLifeFixed 1, phrase := "You gain 1 life." }
    ]
  }
  -- 4a. Before `GameEvent.playerLost`: in a 3-player game, `⟨1⟩` at 0 life controls two copies of `⟨0⟩`'s
  --     legendary creature; Pass 1 still applies CR 704.5j before `⟨1⟩` leaves the game at end of Pass 1:
  let gLostLeg0 : Game :=
    let g := addPermanent (addPermanent mkThreePlayer24i4 legDiesWatcherDef ⟨0⟩ ⟨1⟩) legDiesWatcherDef ⟨0⟩ ⟨1⟩
    g.loseLife ⟨1⟩ 20 (cause := some testCause)
  let gLostLeg1 := gLostLeg0.checkSBA
  let beforePlayerLostOk :=
    (gLostLeg1.player ⟨1⟩).lost &&
    (gLostLeg1.player ⟨1⟩).leftTheGame &&
    ((gLostLeg1.player ⟨0⟩).graveyard.any (fun id => (gLostLeg1.object! id).name == legDiesWatcherDef.name)) &&
    gLostLeg1.log.any (·.contains "legend rule, CR 704.5j")

  -- 4b. Before CR 704.5q counter annihilation: `annihHost` loses its `+1/+1` counter in 704.5q,
  --     yet two `Grizzly Bears` made Legendary by `.whileSourceHasCounter annihHostId .plusOnePlusOne`
  --     at start of Pass 1 still pause on `Pending.chooseLegend`:
  let gAnnih0 : Game :=
    let g := addPermanent (addPermanent (addPermanent afterDraw hero me me) bear me me) bear me me
    let hostId := (g.battlefield.filter (·.name == hero.name))[0]!.id
    let bIds := (g.battlefield.filter (·.name == bear.name)).map (·.id)
    let g := (g.recordPutCounters hostId .plusOnePlusOne 1).recordPutCounters hostId .minusOneMinusOne 1
    g.createEffect (.layered (.objects bIds) (.types .add #[] #[] #[.legendary])
      (.whileSourceHasCounter hostId .plusOnePlusOne)) (cause := some testCause)
  let gAnnih1 := gAnnih0.checkSBA
  let gAnnihKept :=
    match gAnnih1.pending with
    | .chooseLegend p _ ids => mustApply gAnnih1 p (.keepLegend ids[0]!)
    | _ => gAnnih1
  let beforeCounterAnnihOk :=
    (match gAnnih1.pending with
     | .chooseLegend p nm ids => p == me && nm == bear.name && ids.size == 2
     | _ => false) &&
    (gAnnihKept.battlefield.filter (·.name == bear.name)).size == 1

  -- 4c. Before `dyingCreatures` (both directions):
  --     (i) 0/0 `zeroZero24i4` granting `.legendary` dies in `dyingCreatures`, yet Pass 1 still pauses on `chooseLegend`;
  --     (ii) 0/0 `zeroZero24i4` suppressing legend rule (`.legendRuleOff`) keeps Pass 1 from prompting `chooseLegend`,
  --          then Pass 2 prompts `chooseLegend` after the 0/0 dies!
  let gZeroGrant0 : Game :=
    let g := addPermanent (addPermanent (addPermanent afterDraw zeroZero24i4 me me) bear me me) bear me me
    let zId := (g.battlefield.filter (·.name == zeroZero24i4.name))[0]!.id
    let bIds := (g.battlefield.filter (·.name == bear.name)).map (·.id)
    g.createEffect (.layered (.objects bIds) (.types .add #[] #[] #[.legendary])
      (.whileSourceOnBattlefield zId)) (cause := some testCause)
  let gZeroGrant1 := gZeroGrant0.checkSBA
  let gZeroBox0 : Game :=
    let g := addPermanent (addPermanent (addPermanent afterDraw zeroZero24i4 me me) legDiesWatcherDef me me) legDiesWatcherDef me me
    let zId := (g.battlefield.filter (·.name == zeroZero24i4.name))[0]!.id
    g.createEffect (.playerRule me .legendRuleOff (.whileSourceOnBattlefield zId)) (cause := some testCause)
  let (gZeroBoxPass1, _) := gZeroBox0.checkSBACounted
  let gZeroBoxAll := gZeroBox0.checkSBA
  let beforeDyingCreaturesOk :=
    !(gZeroGrant1.battlefield.any (·.name == zeroZero24i4.name)) &&
    (match gZeroGrant1.pending with
     | .chooseLegend p nm ids => p == me && nm == bear.name && ids.size == 2
     | _ => false) &&
    !(gZeroBoxPass1.battlefield.any (·.name == zeroZero24i4.name)) &&
    gZeroBoxPass1.pending == .none &&
    (match gZeroBoxAll.pending with
     | .chooseLegend p nm ids => p == me && nm == legDiesWatcherDef.name && ids.size == 2
     | _ => false)

  -- 4d. Before `pwMoves`: 0-loyalty planeswalker granting `.legendary` leaves in `pwMoves`, yet Pass 1 still pauses on `chooseLegend`:
  let zeroPwDef : CardDef := {
    name := "P24i4 Zero Loyalty PW"
    types := #[.planeswalker]
    loyalty := some 0
  }
  let gPwGrant0 : Game :=
    let g := addPermanent (addPermanent (addPermanent afterDraw zeroPwDef me me) bear me me) bear me me
    let pwId := (g.battlefield.filter (·.name == zeroPwDef.name))[0]!.id
    let bIds := (g.battlefield.filter (·.name == bear.name)).map (·.id)
    g.createEffect (.layered (.objects bIds) (.types .add #[] #[] #[.legendary])
      (.whileSourceOnBattlefield pwId)) (cause := some testCause)
  let gPwGrant1 := gPwGrant0.checkSBA
  let beforePwMovesOk :=
    !(gPwGrant1.battlefield.any (·.name == zeroPwDef.name)) &&
    (match gPwGrant1.pending with
     | .chooseLegend p nm ids => p == me && nm == bear.name && ids.size == 2
     | _ => false)

  mustHold24i4 "4a.beforePlayerLostOk" beforePlayerLostOk &&
  mustHold24i4 "4b.beforeCounterAnnihOk" beforeCounterAnnihOk &&
  mustHold24i4 "4c.beforeDyingCreaturesOk" beforeDyingCreaturesOk &&
  mustHold24i4 "4d.beforePwMovesOk" beforePwMovesOk &&
  mustHold24i4 "4.replay" (replayOk24i4 #[gLostLeg1, gAnnih1, gAnnihKept, gZeroGrant1, gZeroBoxPass1, gZeroBoxAll, gPwGrant1])

-- 5. CR 613.1d,f / 703.4f / 704.5s / 714.2d / 714.3c / 714.4:
--    Layer 4 (`g.hasSubtype o .saga`) and Layer 6 (`g.retainsPrintedAbilities o`) Saga checks across
--    `StateBasedActions.checkSBACounted`, `Triggers.addLoreAfterDrawStep`, `Core.loreAmongSagas`, and `Entering.finishOneResolution`.
#guard
  let sagaDef24 : CardDef :=
    saga "P24i4 Saga" ManaCost.empty "" "I" #[chapter "I" "You gain 1 life." (Effect.gainLife 1)]
  let tomDef24 : CardDef := {
    legendaryCreature "P24i4 Tom Watcher" ManaCost.empty #["God", "Bard"] 4 4 with
    staticAbilities := #[.hexproofIndestructibleIfLore 4]
  }
  let gBase :=
    insertObject (addPermanent afterDraw tomDef24 me me) sagaDef24 me .battlefield (some me)
      { summoningSick := false, counters := #[(.lore, 1)] }
  let sagaId := (gBase.battlefield.filter (·.name == sagaDef24.name))[0]!.id
  let sagaSnap := gBase.snapshot (gBase.object! sagaId)

  -- 5a. Layer 6 ability removal (`.abilities {} .all`): retains `.saga` subtype (`loreAmongSagas == 1`),
  --     but `retainsPrintedAbilities == false`, so `addLoreAfterDrawStep`, `checkSBA` 704.5s, and `finalSagaPlayer?` do NOT fire:
  let gL6 := gBase.createEffect (.layered (.objects #[sagaId]) (.abilities {} .all) .indefinite) (cause := some testCause)
  let gL6AfterDraw := gL6.addLoreAfterDrawStep
  let gL6AfterSba := gL6.checkSBA
  let gL6Fin := gL6.finishOneResolution (.ability ⟨99901⟩ sagaSnap me (some sagaId) (some 1))
  let layer6SagaOk :=
    gL6.hasSubtype (gL6.object! sagaId) .saga &&
    !gL6.retainsPrintedAbilities (gL6.object! sagaId) &&
    gL6.loreAmongSagas me == 1 &&
    (gL6AfterDraw.object! sagaId).status.lore == 1 &&
    (gL6AfterSba.object! sagaId).isOnBattlefield &&
    !gL6Fin.log.any (·.contains "last ability triggers")

  -- 5b. Layer 4 subtype removal (`.types .set #[.artifact] #[] #[]`): loses `.saga` subtype (`loreAmongSagas == 0`),
  --     even while `retainsPrintedAbilities == true`, so `addLoreAfterDrawStep`, `checkSBA` 704.5s, and `finalSagaPlayer?` do NOT fire:
  let gL4 := gBase.createEffect (.layered (.objects #[sagaId]) (.types .set #[.artifact] #[] #[]) .indefinite) (cause := some testCause)
  let gL4AfterDraw := gL4.addLoreAfterDrawStep
  let gL4AfterSba := gL4.checkSBA
  let gL4Fin := gL4.finishOneResolution (.ability ⟨99902⟩ sagaSnap me (some sagaId) (some 1))
  let layer4SagaOk :=
    !gL4.hasSubtype (gL4.object! sagaId) .saga &&
    gL4.retainsPrintedAbilities (gL4.object! sagaId) &&
    gL4.loreAmongSagas me == 0 &&
    (gL4AfterDraw.object! sagaId).status.lore == 1 &&
    (gL4AfterSba.object! sagaId).isOnBattlefield &&
    !gL4Fin.log.any (·.contains "last ability triggers")

  -- Control check: without Layer 4/6 overrides, `finishOneResolution` logs Tom's trigger and `checkSBA` sacrifices the Saga!
  let gNormalFin := gBase.finishOneResolution (.ability ⟨99903⟩ sagaSnap me (some sagaId) (some 1))
  let gNormalSba := gBase.checkSBA
  let normalControlOk :=
    gNormalFin.log.any (·.contains "last ability triggers") &&
    !gNormalSba.battlefield.any (·.id == sagaId)

  mustHold24i4 "5a.layer6SagaOk" layer6SagaOk &&
  mustHold24i4 "5b.layer4SagaOk" layer4SagaOk &&
  mustHold24i4 "5c.normalControlOk" normalControlOk &&
  mustHold24i4 "5.replay" (replayOk24i4 #[gL6AfterDraw, gL6AfterSba, gL6Fin, gL4AfterDraw, gL4AfterSba, gL4Fin, gNormalFin, gNormalSba])

end Phase24Item4EventAlignment

section Phase25Item1EventAlignment

def mustHold25i1 (label : String) (ok : Bool) : Bool :=
  if ok then true else panic! s!"Phase 25 item 1 guard failed: {label}"

def replayOk25i1 (gs : Array Game) : Bool :=
  gs.all (fun g => Game.replayEvents g.events == g && allRulesEventsClassified g)

def mkThreePlayer25i1 (seed : UInt64 := 251) : Game :=
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

-- 1. CR 117.3 / 603.2c / 603.3b / 610.3 / 616.1 / 800.4a,f,h:
--    Generalized paused-batch preservation (`restorePausedBatch` for non-discard `currentBatch`)
--    and brand-new `Pending.chooseReplacement` opened inside `redirectPendingAfterLeave`.
#guard
  let p0 : PlayerId := ⟨0⟩
  let p1 : PlayerId := ⟨1⟩
  let p2 : PlayerId := ⟨2⟩
  let gBase := mkThreePlayer25i1
  let leylineA : CardDef := { name := "P25i1 Leyline A", types := #[.enchantment] }
  let leylineB : CardDef := { name := "P25i1 Leyline B", types := #[.enchantment] }
  let gWithBears :=
    addPermanent (addPermanent (addPermanent (addPermanent gBase bear p0 p0) bear p2 p2) leylineA p0 p0) leylineB p0 p0
  let b0 := (gWithBears.battlefield.filter (fun o => o.name == bear.name && o.controller == some p0))[0]!.id
  let b2 := (gWithBears.battlefield.filter (fun o => o.name == bear.name && o.controller == some p2))[0]!.id
  let leyA := (gWithBears.battlefield.filter (·.name == leylineA.name))[0]!.id
  let leyB := (gWithBears.battlefield.filter (·.name == leylineB.name))[0]!.id
  let ridExileA : ReplacementId := { kind := .exileOppDeath, object := some leyA }
  let ridExileB : ReplacementId := { kind := .exileOppDeath, object := some leyB }
  let gTwoExiles :=
    (gWithBears.createEffect
      (.replacement { id := ridExileA, source := some leyA, controller := some p0, affectedPlayer := p2,
                      kind := .exileInsteadOfGraveyard (some b2) false }) (cause := some testCause)).createEffect
      (.replacement { id := ridExileB, source := some leyB, controller := some p0, affectedPlayer := p2,
                      kind := .exileInsteadOfGraveyard (some b2) false }) (cause := some testCause)

  -- 1a. Non-discard `origBid` paused on `Pending.chooseReplacement p2`: `p1` concedes mid-batch;
  --     `leaveBid` runs independently (`leaveBid != origBid`), `origBid` is restored via `restorePausedBatch`,
  --     and once `p2` resolves the replacement choice both `b0` and `b2` share `origBid`:
  let preSacIdx := gTwoExiles.events.size
  let gPausedBatch :=
    gTwoExiles.withBatch (some testCause) fun g =>
      g.sacrificePermanentsLoop #[(p0, b0), (p2, b2)] (preBattlefield := some g.battlefield) (cause := some testCause)
  let origBid? := gPausedBatch.currentBatch.map Prod.fst
  let gAfterP1Concede := mustApply gPausedBatch p1 .concede
  let leaveEvtBatch? :=
    ((gAfterP1Concede.events.extract preSacIdx gAfterP1Concede.events.size).find? (fun e =>
      match e.change with
      | .rules (.player (.leftGame q)) => q == p1
      | _ => false)).bind (·.batch)
  let gResolvedBatch :=
    match gAfterP1Concede.pending with
    | .chooseReplacement chooser cs => mustApply gAfterP1Concede chooser (.chooseReplacement cs[0]!)
    | _ => gAfterP1Concede
  let b0MoveBatch? :=
    ((gResolvedBatch.events.extract preSacIdx gResolvedBatch.events.size).find? (fun e =>
      match e.change with
      | .rules (.zone (.moved prev _ .battlefield ..)) => prev.id == some b0
      | _ => false)).bind (·.batch)
  let b2MoveBatch? :=
    ((gResolvedBatch.events.extract preSacIdx gResolvedBatch.events.size).find? (fun e =>
      match e.change with
      | .rules (.zone (.moved prev _ .battlefield .exile ..)) => prev.id == some b2
      | _ => false)).bind (·.batch)
  let nonDiscardPausedBatchOk :=
    origBid?.isSome &&
    leaveEvtBatch?.isSome &&
    leaveEvtBatch? != origBid? &&
    gAfterP1Concede.currentBatch.map Prod.fst == origBid? &&
    (match gAfterP1Concede.pending with | .chooseReplacement q _ => q == p2 | _ => false) &&
    gResolvedBatch.currentBatch.isNone &&
    gResolvedBatch.pending == .none &&
    b0MoveBatch? == origBid? &&
    b2MoveBatch? == origBid?

  -- 1b. Brand-new `Pending.chooseReplacement` opened inside `redirectPendingAfterLeave`
  --     (`.chooseSacrificeCreature p1 #[b2] #[]` when `p1` concedes): `leaveBid` stays paused on
  --     `Pending.chooseReplacement p2` instead of stashing `.chooseReplacement` into `savedPreLeavePending?`,
  --     and once `p2` resolves it `leaveBid` closes and priority is granted to a living player:
  let gRedirAsk := gTwoExiles.change (.pending (.chooseSacrificeCreature p1 #[b2] #[]))
  let gRedirConcede := mustApply gRedirAsk p1 .concede
  let gRedirDone :=
    match gRedirConcede.pending with
    | .chooseReplacement chooser cs => mustApply gRedirConcede chooser (.chooseReplacement cs[0]!)
    | _ => gRedirConcede
  let redirectNewReplacementOk :=
    (match gRedirConcede.pending with | .chooseReplacement q _ => q == p2 | _ => false) &&
    gRedirConcede.currentBatch.isSome &&
    gRedirDone.currentBatch.isNone &&
    gRedirDone.pending == .none &&
    !(gRedirDone.findObject? b2).any (·.isOnBattlefield) &&
    gRedirDone.stillInGame gRedirDone.priority

  mustHold25i1 "1a.nonDiscardPausedBatchOk" nonDiscardPausedBatchOk &&
  mustHold25i1 "1b.redirectNewReplacementOk" redirectNewReplacementOk &&
  mustHold25i1 "1.replay" (replayOk25i1 #[gPausedBatch, gAfterP1Concede, gResolvedBatch, gRedirConcede, gRedirDone])

-- 2. CR 400.3 / 608.2c / 614.6 / 616.1 / 701.50 / 800.4a,f–h:
--    Outer `g.pendingReplacement` preservation across `redirectPendingAfterLeave` & `commitEnteringAttackItems`,
--    `.chooseDiscardCard` departure cleanup (`conniveSource` + `plusOneAfterDiscards`), and arrival-gated `.extrapolatePick`.
#guard
  let p0 : PlayerId := ⟨0⟩
  let p1 : PlayerId := ⟨1⟩
  let gBase := mkThreePlayer25i1

  -- 2a. `.chooseDiscardCard` final-discarder departure clears `conniveSource` and runs `finishPlusOneAfterDiscards`:
  let gConn0 := addPermanent gBase bear p0 p0
  let connBearId := (gConn0.battlefield.filter (·.name == bear.name))[0]!.id
  let gConnAsk :=
    ((gConn0.change (.pushContinuationFrame {})).changes #[
      .conniveSource (some connBearId),
      .plusOneAfterDiscards (some connBearId),
      .pending (.chooseDiscardCard p1 #[])])
  let gConnLeft := mustApply gConnAsk p1 .concede
  let discardCleanupOk :=
    gConnLeft.pending == .none &&
    gConnLeft.conniveSource.isNone &&
    gConnLeft.plusOneAfterDiscards.isNone &&
    (gConnLeft.object! connBearId).status.plusOnePlusOne == 1 &&
    gConnLeft.log.any (·.contains "No card is discarded; the conniving creature does not receive a +1/+1 counter")

  -- 2b. Outer `g.pendingReplacement` preserved across `redirectPendingAfterLeave` (`.palantirMayDraw`)
  --     and `ResolutionEffects.commitEnteringAttackItems` `.card` branch:
  let palDef : CardDef := { name := "P25i1 Palantir", types := #[.artifact] }
  let gPal0 := insertObject gBase palDef p0 .battlefield (some p0) { counters := #[(.influence, 2)] }
  let palId := (gPal0.battlefield.filter (·.name == palDef.name))[0]!.id
  let p0LifeBefore := (gPal0.player p0).life
  let p0LibBefore := (gPal0.player p0).library.size
  let gPalAsk :=
    (gPal0.chainPendingReplacement (.finishPostStep (.gainLifePlayer p0 5))).change
      (.pending (.fraChoice p1 (.palantirMayDraw p0 palId)))
  let gPalLeft := mustApply gPalAsk p1 .concede

  let colorCardDef : CardDef := {
    bear with
    name := "P25i1 Entering Attacker"
    staticAbilities := #[.entersTappedUnlessPayLife 2]
  }
  let gAtk0 := insertObject gBase colorCardDef p0 (.graveyard p0)
  let atkCardId := (gAtk0.player p0).graveyard.back!
  let atkLifeBefore := (gAtk0.player p0).life
  let atkItem : EnteringAttackItem :=
    .card atkCardId p0 p0 false false #[] [] .putOntoBattlefield #[.player p1]
  let gAtkPaused :=
    (gAtk0.chainPendingReplacement (.finishPostStep (.gainLifePlayer p0 4))).commitEnteringAttackItems
      #[(atkItem, some (.player p1))] (some testCause)
  let gAtkDone :=
    match gAtkPaused.pending with
    | .chooseReplacement chooser _ => mustApply gAtkPaused chooser .decline
    | _ => gAtkPaused

  mustHold25i1 "2a.discardCleanupOk" discardCleanupOk &&
  mustHold25i1 s!"2b.palLife:{(gPalLeft.player p0).life}!={p0LifeBefore + 5}" ((gPalLeft.player p0).life == p0LifeBefore + 5) &&
  mustHold25i1 s!"2b.palLib:{(gPalLeft.player p0).library.size}!={p0LibBefore - 2}" ((gPalLeft.player p0).library.size == p0LibBefore - 2) &&
  mustHold25i1 "2b.atkPaused" (match gAtkPaused.pending with | .chooseReplacement q _ => q == p0 | _ => false) &&
  mustHold25i1 "2b.atkDonePending" (gAtkDone.pending == .none) &&
  mustHold25i1 s!"2b.atkDoneLife:{(gAtkDone.player p0).life}!={atkLifeBefore + 4}" ((gAtkDone.player p0).life == atkLifeBefore + 4) &&
  mustHold25i1 "2b.atkDoneBf" (gAtkDone.battlefield.any (fun o => o.name == colorCardDef.name && o.status.attacking)) &&
  mustHold25i1 "2.replay" (replayOk25i1 #[gConnLeft, gPalLeft, gAtkPaused, gAtkDone])

-- 3. CR 101.4 / 118.12a / 121.2 / 121.2c / 603.2c / 701.9b–c:
--    Simultaneous discard batching for *Thirst for Knowledge*, *Garruk, Veiled Butcher* (`continueDiscardTwo`),
--    and *Variable Chaser // Arc of Fortune* (`eachPlayerMayWheel`).
#guard
  let p0 : PlayerId := ⟨0⟩
  let p1 : PlayerId := ⟨1⟩
  let p2 : PlayerId := ⟨2⟩
  let discardWatcherDef : CardDef := {
    bear with
    name := "P25i1 Discard Watcher"
    triggeredAbilities := #[
      TriggeredAbility.ofPattern (.discard .any)
        "Whenever a player discards one or more cards, you gain 1 life." (Instruction.gainLifeFixed 1)
        (grouping := .perPlayerInBatch)
    ]
  }

  -- 3a. *Thirst for Knowledge*: single `discardBatch` across two non-artifacts, `.decline` + two artifacts,
  --     and simultaneous `.choosePermanents #[art1, art2]`, firing `.playerDiscards` once in each case:
  let thirstStoneDef : CardDef := { name := "P25i1 Mind Stone", types := #[.artifact] }
  let gThirst0 :=
    insertObject
      (insertObject
        (insertObject
          (insertObject (addPermanent afterDraw discardWatcherDef p0 p0) thirstStoneDef p0 (.hand p0))
          thirstStoneDef p0 (.hand p0))
        bear p0 (.hand p0))
      hero p0 (.hand p0)
  let stones := ((gThirst0.player p0).hand.filter (fun id => (gThirst0.object! id).name == thirstStoneDef.name)).extract 0 2
  let nonArts := #[
    ((gThirst0.player p0).hand.filter (fun id => (gThirst0.object! id).name == bear.name))[0]!,
    ((gThirst0.player p0).hand.filter (fun id => (gThirst0.object! id).name == hero.name))[0]!
  ]
  let runThirstSeq :=
    let g1 := gThirst0.applyEffect p0 Effect.drawThreeDiscardUnlessArtifact #[]
    let g2 := mustApply g1 p0 (.discard nonArts[0]!)
    mustApply g2 p0 (.discard nonArts[1]!)
  let runThirstDeclineTwoArts :=
    let g1 := mustApply (gThirst0.applyEffect p0 Effect.drawThreeDiscardUnlessArtifact #[]) p0 .decline
    let g2 := mustApply g1 p0 (.discard stones[0]!)
    mustApply g2 p0 (.discard stones[1]!)
  let runThirstSimultaneousTwoArts :=
    let g1 := gThirst0.applyEffect p0 Effect.drawThreeDiscardUnlessArtifact #[]
    mustApply g1 p0 (.choosePermanents stones)
  let oneDiscardTrig (g : Game) : Bool :=
    let moves := (g.events.extract gThirst0.events.size g.events.size).filter (fun e =>
      match e.change with
      | .rules (.zone (.moved _ _ (.hand _) (.graveyard _) .discard ..)) => true
      | _ => false)
    g.pending == .none && g.discardBatch.isNone &&
      moves.size == 2 && moves[0]!.batch.isSome && moves[0]!.batch == moves[1]!.batch &&
      (g.waitingTriggers.size + g.stack.size) == 1
  let thirstBatchOk :=
    oneDiscardTrig runThirstSeq &&
    oneDiscardTrig runThirstDeclineTwoArts &&
    oneDiscardTrig runThirstSimultaneousTwoArts

  -- 3b. *Garruk, Veiled Butcher* (`continueDiscardTwo`): APNAP choices collected before moving any card,
  --     all 4 chosen cards discarded in one shared batch, and `controller` draws 1 card for `p1` (< 2 nonlands):
  let gGarruk0 :=
    insertObject
      (insertObject
        (insertObject
          (insertObject (addPermanent mkThreePlayer25i1 discardWatcherDef p0 p0) bear p1 (.hand p1))
          mountain p1 (.hand p1))
        bear p2 (.hand p2))
      hero p2 (.hand p2)
  let p0HandBefore := (gGarruk0.player p0).hand.size
  let p1Pick := #[
    ((gGarruk0.player p1).hand.filter (fun id => (gGarruk0.object! id).name == bear.name))[0]!,
    ((gGarruk0.player p1).hand.filter (fun id => (gGarruk0.object! id).name == mountain.name))[0]!
  ]
  let p2Pick := #[
    ((gGarruk0.player p2).hand.filter (fun id => (gGarruk0.object! id).name == bear.name))[0]!,
    ((gGarruk0.player p2).hand.filter (fun id => (gGarruk0.object! id).name == hero.name))[0]!
  ]
  let gGarrukStart := gGarruk0.continueDiscardTwo p0 #[p1, p2] 0
  let gGarrukMid := mustApply gGarrukStart p1 (.choosePermanents p1Pick)
  let p1StillInHandMid := p1Pick.all (gGarrukMid.player p1).hand.contains
  let gGarrukDone := mustApply gGarrukMid p2 (.choosePermanents p2Pick)
  let garrukMoves := (gGarrukDone.events.extract gGarruk0.events.size gGarrukDone.events.size).filter (fun e =>
    match e.change with
    | .rules (.zone (.moved _ _ (.hand _) (.graveyard _) .discard ..)) => true
    | _ => false)
  let garrukBatchOk :=
    p1StillInHandMid &&
    gGarrukDone.pending == .none &&
    garrukMoves.size == 4 &&
    garrukMoves[0]!.batch.isSome &&
    garrukMoves.all (fun e => e.batch == garrukMoves[0]!.batch) &&
    (gGarrukDone.player p0).hand.size == p0HandBefore + 1 &&
    (gGarrukDone.waitingTriggers.size + gGarrukDone.stack.size) == 2

  -- 3c. *Variable Chaser // Arc of Fortune* (`eachPlayerMayWheel`): APNAP yes/no choices collected before
  --     discarding all accepting players' hands in one shared batch, followed by individual CR 121.2 draws:
  let gWheel0 := addPermanent mkThreePlayer25i1 discardWatcherDef p0 p0
  let p0HandPreWheel := (gWheel0.player p0).hand
  let wheel2Eff : Effect := {
    body := .forEach (.eachPlayer .any) ⟨0⟩
      (Instruction.may (.stepPlayers ⟨0⟩) none
        (.seq #[
          .moveZone (.inZones (.handOf (.stepPlayers ⟨0⟩)) .anyObject) .graveyard .discard {},
          Instruction.drawFixed 2 (.stepPlayers ⟨0⟩)
        ]))
  }
  let gWheelAsk0 := gWheel0.applyEffect p0 wheel2Eff #[]
  let gWheelAsk1 := mustApply gWheelAsk0 p0 .accept
  let p0IntactDuringChoices := (gWheelAsk1.player p0).hand == p0HandPreWheel
  let gWheelAsk2 := mustApply gWheelAsk1 p1 .decline
  let gWheelDone := mustApply gWheelAsk2 p2 .accept
  let wheelMoves := (gWheelDone.events.extract gWheel0.events.size gWheelDone.events.size).filter (fun e =>
    match e.change with
    | .rules (.zone (.moved _ _ (.hand _) (.graveyard _) .discard ..)) => true
    | _ => false)
  let wheelDraws := (gWheelDone.events.extract gWheel0.events.size gWheelDone.events.size).filter (fun e =>
    match e.change with
    | .rules (.zone (.moved _ _ (.library _) (.hand _) (.draw ..) ..)) => true
    | _ => false)
  let wheelBatchOk :=
    p0IntactDuringChoices &&
    gWheelDone.pending == .none &&
    !wheelMoves.isEmpty &&
    wheelMoves[0]!.batch.isSome &&
    wheelMoves.all (fun e => e.batch == wheelMoves[0]!.batch) &&
    wheelDraws.size == 4 &&
    wheelDraws.all (fun e => e.batch != wheelMoves[0]!.batch) &&
    (gWheelDone.player p0).hand.size == 2 &&
    (gWheelDone.player p2).hand.size == 2 &&
    gWheelDone.log.any (·.contains "keeps their hand") &&
    (gWheelDone.waitingTriggers.size + gWheelDone.stack.size) == 2

  mustHold25i1 "3a.thirstBatchOk" thirstBatchOk &&
  mustHold25i1 "3b.garrukBatchOk" garrukBatchOk &&
  mustHold25i1 "3c.wheelBatchOk" wheelBatchOk &&
  mustHold25i1 "3.replay" (replayOk25i1 #[
    runThirstSeq, runThirstDeclineTwoArts, runThirstSimultaneousTwoArts,
    gGarrukStart, gGarrukMid, gGarrukDone,
    gWheelAsk0, gWheelAsk1, gWheelAsk2, gWheelDone
  ])

end Phase25Item1EventAlignment

section Phase25Item2EventAlignment

def mustHold25i2 (label : String) (ok : Bool) : Bool :=
  if ok then true else panic! s!"Phase 25 item 2 guard failed: {label}"

def replayOk25i2 (gs : Array Game) : Bool :=
  gs.all (fun g => Game.replayEvents g.events == g && allRulesEventsClassified g)

-- 1. Multi-target / multi-slot target announcement & castability legality:
--    `.upToTwoCreaturesTotalMvAtMost` announcement cap, `.twoNonlandsSharingType` lookahead,
--    and `effectHasEnoughTargets` across cast / mode / trigger / resolution-cast entry points.
#guard
  let p0 : PlayerId := ⟨0⟩
  let p1 : PlayerId := ⟨1⟩
  let mvCapSpell : CardDef := {
    name := "P25i2 Cap Grab"
    types := #[.sorcery]
    spellEffect := some {
      targeting := .of (.upToTwoCreaturesTotalMvAtMost 3)
      allowsZeroTargets := true
      maxTargets := 2
    }
  }
  let oneMvCub : CardDef := {
    name := "P25i2 Cub"
    manaCost := { symbols := #[.colored .green] }
    types := #[.creature]
    power := some 1
    toughness := some 1
  }
  let g0 := emptyHand afterDraw p0
  let (gMv, mvCapObj) :=
    (addPermanent (addPermanent (addPermanent g0 grizzlyBears p0 p0) grizzlyBears p1 p1) oneMvCub p0 p0).allocObject
      mvCapSpell p0 (.hand p0)
  let bears := gMv.battlefield.filter (·.name == grizzlyBears.name)
  let cubId := (gMv.battlefield.filter (·.name == "P25i2 Cub"))[0]!.id
  let gMvProp := mustApply gMv p0 (.cast mvCapObj.id)
  let mvOverRejected :=
    (gMvProp.announceTargetChoices p0
      #[(Target.permanent bears[0]!.id, none), (Target.permanent bears[1]!.id, none)]).toOption.isNone
  let gMvOk :=
    match gMvProp.announceTargetChoices p0
        #[(Target.permanent bears[0]!.id, none), (Target.permanent cubId, none)] with
    | .ok g' => g'
    | .error e => panic! e

  let shareSpell : CardDef := {
    name := "P25i2 Share"
    types := #[.sorcery]
    spellEffect := some { targeting := .of .twoNonlandsSharingType }
  }
  let artA : CardDef := { name := "P25i2 Art A", types := #[.artifact] }
  let artB : CardDef := { name := "P25i2 Art B", types := #[.artifact] }
  let loneEnch : CardDef := { name := "P25i2 Ench", types := #[.enchantment] }
  let (gSh, shareObj) :=
    (addPermanent (addPermanent (addPermanent g0 artA p0 p0) artB p0 p0) loneEnch p0 p0).allocObject
      shareSpell p0 (.hand p0)
  let artAId := (gSh.battlefield.filter (·.name == "P25i2 Art A"))[0]!.id
  let artBId := (gSh.battlefield.filter (·.name == "P25i2 Art B"))[0]!.id
  let enchId := (gSh.battlefield.filter (·.name == "P25i2 Ench"))[0]!.id
  let gShProp := mustApply gSh p0 (.cast shareObj.id)
  let slot0 := gShProp.legalProposedTargets p0 (gShProp.object! gShProp.stack.back!.objectId)
  let (validPairOk, gShOk) :=
    match gShProp.announceTargets p0 #[.permanent artAId, .permanent artBId] with
    | .ok g' => (true, g')
    | .error _ => (false, gShProp)
  let invalidPairRejected :=
    match gShProp.announceTargets p0 #[.permanent artAId, .permanent enchId] with
    | .error _ => true
    | .ok _ => false
  let lookaheadOk :=
    slot0.contains (.permanent artAId) &&
    slot0.contains (.permanent artBId) &&
    !slot0.contains (.permanent enchId) &&
    validPairOk &&
    invalidPairRejected

  -- Trigger mode and resolution-cast `effectHasEnoughTargets`:
  let twoArtEff : Effect := { targeting := .of .twoArtifactsYouControl, phrase := "Tap two target artifacts you control" }
  let gOneArt := addPermanent g0 artA p0 p0
  let oneArtObj := (gOneArt.battlefield.filter (·.name == "P25i2 Art A"))[0]!
  let trigNotChoosable := !gOneArt.triggerModeChoosable p0 oneArtObj twoArtEff
  let twoArtSpell : CardDef := { name := "P25i2 Dual Art", types := #[.sorcery], spellEffect := some twoArtEff }
  let (gOneArtHand, twoArtCard) := gOneArt.allocObject twoArtSpell p0 (.hand p0)
  let twoArtCardId := twoArtCard.id
  let gResReversed := gOneArtHand.castAsPartOfResolution p0 twoArtCardId
  let resCastReversedOk :=
    !gOneArtHand.canCastFrontFace p0 (gOneArtHand.object! twoArtCardId) &&
    gResReversed.proposedSpell.isNone &&
    gResReversed.stack.isEmpty &&
    (gResReversed.object! twoArtCardId).zone == .hand p0

  mustHold25i2 "1.mvCap" (mvOverRejected && gMvOk.stack.back!.targets.size == 2) &&
  mustHold25i2 "1.lookahead" lookaheadOk &&
  mustHold25i2 "1.enoughTargets" (trigNotChoosable && resCastReversedOk) &&
  mustHold25i2 "1.replay" (replayOk25i2 #[gMvProp, gMvOk, gShProp, gShOk, gResReversed])

-- 2. CR 118.9a,c alternative-cost exclusivity, `actualCastManaValue`, and `payLifeEqualManaValue`
--    resolution casts (including `{X}` updating `payLife` via `ProposalChange.payLife`) without
--    leaking onto `withoutManaCost := true` casts.
#guard
  let p0 : PlayerId := ⟨0⟩
  let xSpell : CardDef := {
    name := "P25i2 X Drain"
    manaCost := { symbols := #[.x, .colored .black] }
    types := #[.sorcery]
    spellEffect := some { body := Instruction.drawFixed 1 }
  }
  let fixedThreeMv : CardDef := {
    name := "P25i2 Three Drop"
    manaCost := { symbols := #[.generic 2, .colored .blue] }
    types := #[.sorcery]
    spellEffect := some { body := Instruction.drawFixed 1 }
  }
  let g0 := emptyHand afterDraw p0
  let (gHand0, xCard) := g0.allocObject xSpell p0 (.hand p0)
  let (gHand, threeCard) := gHand0.allocObject fixedThreeMv p0 (.hand p0)
  let xId := xCard.id
  let threeId := threeCard.id
  let lifePerm : PlayPermission := { player := p0, payLifeEqualManaValue := true }
  let gPerm :=
    (gHand.createEffect (.playPermission xId lifePerm) (cause := some testCause)).createEffect
      (.playPermission threeId lifePerm) (cause := some testCause)

  -- 2a. `withoutManaCost := true` resolution cast ignores unrelated `payLifeEqualManaValue` permission:
  let gFreeRes := gPerm.castAsPartOfResolution p0 threeId (withoutManaCost := true)
  let freeNoLifeLeak :=
    (gFreeRes.player p0).life == 20 &&
    gFreeRes.stack.size == 1 &&
    gFreeRes.proposedSpell.isNone

  -- 2b. `withoutManaCost := false` resolution cast with `payLifeEqualManaValue` pays 3 life for MV 3,
  --     and `{X}{B}` forces X=0 (CR 107.3b / Ruling 153) paying 1 life:
  let gLifeThreeProp := gPerm.castAsPartOfResolution p0 threeId (withoutManaCost := false)
  let gLifeThreePaid := mustApply gLifeThreeProp p0 .pay
  let gLifeXProp := gPerm.castAsPartOfResolution p0 xId (withoutManaCost := false)
  let gLifeXPaid := mustApply gLifeXProp p0 .pay
  let lifePermOk :=
    gLifeThreeProp.proposedSpell.any (·.payLife == 3) &&
    (gLifeThreePaid.player p0).life == 17 &&
    gLifeXProp.proposedSpell.any (·.payLife == 1) &&
    (gLifeXPaid.player p0).life == 19

  -- 2c. CR 119.4 / 601.1a / 608.2g: player at 2 life cannot pay 3 life for MV 3 spell via
  --     `payLifeEqualManaValue` (reversing cleanly to exile on `.pay`), while `castAsPartOfResolution
  --     (withoutManaCost := false)` skips the unpayable life grant (`payLife == 0`) for `{2}{U}`:
  let (gExLife0, threeExCard) := (gPerm.setLifeTotal p0 2).allocObject fixedThreeMv p0 .exile none
  let gExLife :=
    gExLife0.createEffect (.permission (some p0) (.playFromExile threeExCard.id lifePerm) .indefinite)
      (cause := some testCause)
  let gExLifeProp := mustApply gExLife p0 (.cast threeExCard.id)
  let gExLifeRejected := mustApply gExLifeProp p0 .pay
  let gLowLife := gPerm.setLifeTotal p0 2
  let gLowResProp := gLowLife.castAsPartOfResolution p0 threeId (withoutManaCost := false)
  let gLowRejected := mustApply gLowResProp p0 .pay
  let lowLifeRejectedOk :=
    gExLifeProp.proposedSpell.any (·.payLife == 3) &&
    gExLifeRejected.stack.isEmpty &&
    (gExLifeRejected.object! threeExCard.id).zone == .exile &&
    (gExLifeRejected.player p0).life == 2 &&
    gLowResProp.proposedSpell.any (·.payLife == 0) &&
    gLowRejected.stack.isEmpty &&
    (gLowRejected.object! threeId).zone == .hand p0 &&
    (gLowRejected.player p0).life == 2

  mustHold25i2 "2a.freeNoLifeLeak" freeNoLifeLeak &&
  mustHold25i2 "2b.lifePermOk" lifePermOk &&
  mustHold25i2 "2c.lowLifeRejectedOk" lowLifeRejectedOk &&
  mustHold25i2 "2.replay" (replayOk25i2 #[
    gFreeRes, gLifeThreeProp, gLifeThreePaid, gLifeXProp, gLifeXPaid,
    gExLifeProp, gExLifeRejected, gLowResProp, gLowRejected
  ])

-- 3. CR 733.1 proposal-checkpoint ordering & upfront `mayCast*` checks:
--    - reversing an unpayable/targetless Cascade cast restores `Pending.fraChoice p0 (.mayCastCascade ...)`
--      with `postCastCleanup == none` and card still in `.exile`;
--    - `defaultFraAction` declines uncastable Cascade hits cleanly;
--    - `mayCastFromLookedError` rejects under `splitSecondOnStack` (CR 702.61a);
--    - `.mayCastUpToFromExile` preserves `left` on an illegal pick (mandatory sacrifice unpayable / prohibited).
#guard
  let p0 : PlayerId := ⟨0⟩
  let needCreatureTarget : CardDef := {
    name := "P25i2 Target Creature Spell"
    manaCost := { symbols := #[.colored .red] }
    types := #[.sorcery]
    spellEffect := some { targeting := .of .creature, body := Instruction.drawFixed 1 }
  }
  let sacCostSpell : CardDef := {
    name := "P25i2 Sac Creature Spell"
    manaCost := { symbols := #[.colored .black] }
    types := #[.sorcery]
    additionalCosts := #[AdditionalCostSpec.mandatory CostSpec.sacrificeCreature]
    spellEffect := some { body := Instruction.drawFixed 1 }
  }
  let drawSpell : CardDef := {
    name := "P25i2 Clean Draw"
    manaCost := { symbols := #[.colored .blue] }
    types := #[.sorcery]
    spellEffect := some { body := Instruction.drawFixed 1 }
  }
  let samutGrant : CardDef := {
    name := "P25i2 Samut"
    types := #[.creature]
    power := some 2
    toughness := some 2
    staticAbilities := #[.instantSorcerySplitSecond]
  }
  let g0 := emptyHand afterDraw p0
  let (gEx0, hitCard) := g0.allocObject needCreatureTarget p0 .exile none
  let (gEx1, otherEx) := gEx0.allocObject drawSpell p0 .exile none
  let (gEx2, sacEx) := gEx1.allocObject sacCostSpell p0 .exile none

  -- 3a. `.mayCastCascade` on targetless `hitCard`: `defaultFraAction` declines, and accepting reverses cleanly to `.mayCastCascade`!
  let cascChoice : FraChoice := .mayCastCascade hitCard.id #[otherEx.id]
  let gCascPrompt := gEx2.change (.pending (.fraChoice p0 cascChoice))
  let defaultDeclines :=
    match gCascPrompt.defaultFraAction p0 cascChoice with
    | .decline => true
    | _ => false
  let gCascAccepted := mustApply gCascPrompt p0 .accept
  let cascReversedCleanly :=
    gCascAccepted.pending == Pending.fraChoice p0 cascChoice &&
    gCascAccepted.postCastCleanup.isNone &&
    gCascAccepted.continuations.isEmpty &&
    (gCascAccepted.object! hitCard.id).zone == Zone.exile

  -- 3b. `.mayCastUpToFromExile` with `left := 2`: picking `sacEx` (no creature to sacrifice) throws upfront
  --     and preserves `left == 2`, allowing `otherEx` to still be cast without paying mana!
  let exFreeSpell : CardDef := {
    name := "P25i2 Zero Mana Draw"
    types := #[.sorcery]
    spellEffect := some { body := Instruction.drawFixed 1 }
  }
  let (gEx3, freeEx) := gEx2.allocObject exFreeSpell p0 .exile none
  let exChoice : FraChoice := .mayCastUpToFromExile #[sacEx.id, freeEx.id] 2
  let gUpToPrompt := (gEx3.change (.pushContinuationFrame {})).change (.pending (.fraChoice p0 exChoice))
  let sacPickRejected := (gUpToPrompt.apply p0 (.choosePermanents #[sacEx.id])).toOption.isNone
  let gUpToValid := mustApply gUpToPrompt p0 (.choosePermanents #[freeEx.id])
  let upToPreservedOk :=
    sacPickRejected &&
    gUpToValid.pending == Pending.fraChoice p0 (.mayCastUpToFromExile #[sacEx.id] 1)

  -- 3c. `mayCastFromLookedError` rejects when a spell with split second is on the stack (CR 702.61a):
  let gSamut := addPermanent g0 samutGrant p0 p0
  let (gLib0, topLooked) := gSamut.allocObject drawSpell p0 (.library p0) none
  let (gLib1, ssObj) := gLib0.allocObject drawSpell p0 .stack (some p0)
  let gLibSs := gLib1.putStackEntry p0 ssObj.id
  let splitSecLookedRejected :=
    gLibSs.splitSecondOnStack && (gLibSs.mayCastFromLookedError p0 #[topLooked.id] 10 topLooked.id).isSome

  mustHold25i2 "3a.cascadeCheckpointAndDefault" (defaultDeclines && cascReversedCleanly) &&
  mustHold25i2 "3b.upToFromExileLeftPreserved" upToPreservedOk &&
  mustHold25i2 "3c.splitSecLookedRejected" splitSecLookedRejected &&
  mustHold25i2 "3.replay" (replayOk25i2 #[gCascPrompt, gCascAccepted, gUpToPrompt, gUpToValid, gLibSs])

-- 4. CR 106.6 agent/default mana restrictions across `defaultFraAction` and `Agent`:
--    `.cantNonartifact` mana cannot pay for a nonartifact sorcery in `.mayCastFromGraveyard` / `Agent.choose`,
--    while paying cleanly for an artifact card!
#guard
  let p0 : PlayerId := ⟨0⟩
  let sorcOne : CardDef := {
    name := "P25i2 One Mana Sorc"
    manaCost := ManaCost.ofGeneric 1
    types := #[.sorcery]
    spellEffect := some { body := Instruction.drawFixed 1 }
  }
  let artOne : CardDef := {
    name := "P25i2 One Mana Construct"
    manaCost := ManaCost.ofGeneric 1
    types := #[.artifact, .creature]
    power := some 2
    toughness := some 2
  }
  let g0 := emptyHand afterDraw p0
  let (gGy0, sorcGy) := g0.allocObject sorcOne p0 (.graveyard p0) none
  let (gGy1, artGy) := gGy0.allocObject artOne p0 (.graveyard p0) none
  let gRestrictedPool := gGy1.addMana p0 .colorless 1 (restriction := some .cantNonartifact) (cause := some testCause)
  let gySorcOnly : FraChoice := .mayCastFromGraveyard #[sorcGy.id]
  let gyBoth : FraChoice := .mayCastFromGraveyard #[sorcGy.id, artGy.id]
  let defaultSorcDeclines :=
    match gRestrictedPool.defaultFraAction p0 gySorcOnly with
    | .decline => true
    | _ => false
  let defaultPicksArt :=
    match gRestrictedPool.defaultFraAction p0 gyBoth with
    | .cast cid => cid == artGy.id
    | _ => false

  let (gHandSorc, _) := gRestrictedPool.allocObject sorcOne p0 (.hand p0)
  let agentSkipsNonartifact :=
    match Agent.choose gHandSorc p0 with
    | some (.cast _) => false
    | _ => true
  let (gHandArt, artHand) := gRestrictedPool.allocObject artOne p0 (.hand p0)
  let agentCastsArtifact :=
    match Agent.choose gHandArt p0 with
    | some (.cast cid) => cid == artHand.id
    | _ => false

  mustHold25i2 "4.defaultFraManaRestrictions" (defaultSorcDeclines && defaultPicksArt) &&
  mustHold25i2 "4.agentManaRestrictions" (agentSkipsNonartifact && agentCastsArtifact) &&
  mustHold25i2 "4.replay" (replayOk25i2 #[gRestrictedPool, gHandSorc, gHandArt])

end Phase25Item2EventAlignment

section Phase25Item3EventAlignment

private def mustHold25i3 (label : String) (ok : Bool) : Bool :=
  if ok then true else panic! s!"Phase25Item3EventAlignment failed: {label}"

private def replayOk25i3 (gs : Array Game) : Bool :=
  gs.all fun g => Game.replayEvents g.events == g && allRulesEventsClassified g

-- 1. Wildcard `consumeReplacementOrder` cleanup, `ZoneEvent.created` creator-vs-controller
--    matching, `.wouldPutCounter` watching on counter-bearing created tokens, and
--    Andúril `triggerIfHolds` failure-arm log cleanup:
#guard
  let p0 : PlayerId := ⟨0⟩
  let p1 : PlayerId := ⟨1⟩
  let g0 := addPermanent (addPermanent afterDraw bear p0 p0) bear p1 p1
  let p0Bear := (g0.permanentsOf p0).find? (·.name == bear.name) |>.get!

  -- 1a. Pre-seeded unstamped wildcard `ReplacementId` (`counterKind := none`) is stripped
  --     by `consumeReplacementOrder` when `applied` contains a stamped `cid` with
  --     `{ cid with counterKind := none } == prefId` (CR 616.1 / 616.1g):
  let wildPref : ReplacementId := { kind := .addCountersPut, object := some p0Bear.id, counterKind := none }
  let stampedApp : ReplacementId := { kind := .addCountersPut, object := some p0Bear.id, counterKind := some .plusOnePlusOne }
  let otherPref : ReplacementId := { kind := .multiplyDamage, object := some p0Bear.id, counterKind := none }
  let gSeeded := g0.change (.replacementOrder #[wildPref, otherPref])
  let gConsumed := gSeeded.consumeReplacementOrder #[stampedApp]
  let wildcardStrippedOk := gConsumed.replacementOrder == #[otherPref]

  -- 1b. `ZoneEvent.created` creator `ctrl` vs entering battlefield controller `enterCtrl`,
  --     `Tokens.logCreatedTokensSummary` creator filter, and `.wouldPutCounter` watching:
  let creatorWatcher : CardDef := {
    name := "P25i3 Creator Watcher", types := #[.enchantment]
    triggeredAbilities := #[TriggeredAbility.ofPattern (.createTokens .you (.hasType .creature))
      "Whenever you create one or more creature tokens, draw a card." (Instruction.drawFixed 1) (grouping := .oncePerBatch)]
  }
  let mrFantasticWatcher : CardDef := {
    name := "P25i3 Tokens Enter Watcher", types := #[.enchantment]
    triggeredAbilities := #[SharedTrigger.watch .tokensEnterMayDraw |>.toTriggeredAbility]
  }
  let plusOneWatcher : CardDef := {
    name := "P25i3 PlusOne Watcher", types := #[.enchantment]
    triggeredAbilities := #[SharedTrigger.resource .plusOneCreateInsectOnce |>.toTriggeredAbility]
  }
  let gWatch0 :=
    addPermanent
      (addPermanent
        (addPermanent
          (addPermanent
            (addPermanent
              (addPermanent g0 creatorWatcher p0 p0)
              creatorWatcher p1 p1)
            mrFantasticWatcher p0 p0)
          mrFantasticWatcher p1 p1)
        plusOneWatcher p0 p0)
      plusOneWatcher p1 p1
  let armyTokDef : CardDef := {
    name := "Orc Army"
    types := #[.creature, .artifact]
    subtypes := #["Orc", "Army"]
    power := some 0
    toughness := some 0
    isToken := true
  }
  let armySnap : EventObject := {
    id := some ⟨gWatch0.nextObjectId⟩
    name := armyTokDef.name
    owner := p1
    controller := some p1
    zone := .battlefield
    types := armyTokDef.types
    subtypes := #[.orc, .army]
    power := some 0
    toughness := some 0
    counters := #[(.plusOnePlusOne, 2)]
    token := true
    printed := some armyTokDef
  }
  let (gWatch0, createCause) := gWatch0.allocDelayedCause (some p0)
  let preCreateIdx := gWatch0.events.size
  let createdRaw := GameEvent.created gWatch0.turnNumber p0 armySnap (cause := createCause)
  let watchesCounterOk := createdRaw.watches .wouldPutCounter
  let matchesDirectOk :=
    createdRaw.matchesTriggerPattern p0 none (.createTokens .you (.hasType .creature)) &&
    !createdRaw.matchesTriggerPattern p1 none (.createTokens .you (.hasType .creature)) &&
    createdRaw.matchesTriggerPattern p1 none .tokenYouControlEnters &&
    !createdRaw.matchesTriggerPattern p0 none .tokenYouControlEnters &&
    createdRaw.matchesTriggerPattern p1 none .youPutPlusOneOnCreature &&
    !createdRaw.matchesTriggerPattern p0 none .youPutPlusOneOnCreature &&
    createdRaw.matchesTriggerPattern p1 none .youPutCountersOnGoblinOrcArmy &&
    !createdRaw.matchesTriggerPattern p0 none .youPutCountersOnGoblinOrcArmy
  let gWatch1 := gWatch0.record createdRaw
  let putInEv := gWatch1.events[preCreateIdx]!.countersPutInEvent
  let enterTriggerRoutingOk :=
    putInEv.size == 1 && putInEv[0]!.2.2.2 == some p1 &&
    GameEvent.artifactEntered gWatch1.events gWatch1.turnNumber p1 &&
    !GameEvent.artifactEntered gWatch1.events gWatch1.turnNumber p0 &&
    GameEvent.subtypeEntered gWatch1.events gWatch1.turnNumber p1 .orc &&
    !GameEvent.subtypeEntered gWatch1.events gWatch1.turnNumber p0 .orc &&
    gWatch1.waitingTriggers.any (fun wt => wt.controller == p0 && wt.source.name == "P25i3 Creator Watcher") &&
    !gWatch1.waitingTriggers.any (fun wt => wt.controller == p1 && wt.source.name == "P25i3 Creator Watcher") &&
    gWatch1.waitingTriggers.any (fun wt => wt.controller == p1 && wt.source.name == "P25i3 Tokens Enter Watcher") &&
    !gWatch1.waitingTriggers.any (fun wt => wt.controller == p0 && wt.source.name == "P25i3 Tokens Enter Watcher") &&
    gWatch1.waitingTriggers.any (fun wt => wt.controller == p1 && wt.source.name == "P25i3 PlusOne Watcher") &&
    !gWatch1.waitingTriggers.any (fun wt => wt.controller == p0 && wt.source.name == "P25i3 PlusOne Watcher")
  let logStart0 := gWatch1.log.size
  let gLoggedP0 := gWatch1.logCreatedTokensSummary p0 preCreateIdx
  let gLoggedP1 := gWatch1.logCreatedTokensSummary p1 preCreateIdx
  let creatorSummaryOk :=
    gLoggedP0.log.size == logStart0 + 1 &&
    gLoggedP1.log.size == logStart0

  -- 1c. Andúril `triggerIfHolds` failure arm emits no premature Spirit-tokens log:
  let swordDef : CardDef := { name := "P25i3 Sword", types := #[.artifact], subtypes := #["Equipment"] }
  let gAnd0 := addPermanent g0 swordDef p0 p0
  let swordObj := (gAnd0.permanentsOf p0).find? (·.name == "P25i3 Sword") |>.get!
  let gAnd1 := gAnd0.attachSourceTo swordObj p0Bear
  let andLogBefore := gAnd1.log.size
  let (gAnd2, holdsNonLegend) :=
    gAnd1.triggerIfHolds p0 (.onEnterDraw 1) (some swordObj.id) #[] none
      (.atLeast (.count (.intersection [.equipped, .legendaryCreaturesYouControl])) (.fixed 1))
  let andurilNoPrematureLog := !holdsNonLegend && gAnd2.log.size == andLogBefore

  mustHold25i3 "1a.wildcardConsume" wildcardStrippedOk &&
  mustHold25i3 "1b.watchesAndDirect" (watchesCounterOk && matchesDirectOk) &&
  mustHold25i3 "1b.enterTriggerRouting" (enterTriggerRoutingOk && creatorSummaryOk) &&
  mustHold25i3 "1c.andurilLog" andurilNoPrematureLog &&
  mustHold25i3 "1.replay" (replayOk25i3 #[gConsumed, gWatch1, gLoggedP0, gAnd2])

-- 2. Unbatched CR 121.2 / 101.4 APNAP `applyTriggerDraw` & `.checkDrawThenOpponentsDraw`:
#guard
  let p0 : PlayerId := ⟨0⟩
  let p1 : PlayerId := ⟨1⟩
  let p2 : PlayerId := ⟨2⟩
  let p3 : PlayerId := ⟨3⟩
  let g4 :=
    match Start.start {
      seats := #[{ name := "P0", deck := testRedDeck },
                 { name := "P1", deck := testRedDeck },
                 { name := "P2", deck := testRedDeck },
                 { name := "P3", deck := testRedDeck }]
      startingPlayer := some 2
      seed := 19 } with
    | .ok g => keepOpeningHands g 24
    | .error e => panic! e
  let g4 := g4.change (.pushContinuationFrame {})
  -- Active player is `p2`, so APNAP order of `p0`'s opponents is `[p2, p3, p1]`!
  let idxFixed := g4.events.size
  let gFixed := g4.applyTriggerDraw p0 none (.fixed 1) .eachOpponent
  let fixedDraws := (gFixed.events.extract idxFixed gFixed.events.size).filter fun e =>
    match e.change with
    | .rules (.zone (.moved _ _ _ _ (.draw _ _) _ _ _)) => true
    | _ => false
  let fixedDrawers := fixedDraws.filterMap fun e =>
    match e.change with
    | .rules (.zone (.moved _ _ _ _ (.draw _ _) q _ _)) => q
    | _ => none
  let fixedBatches := fixedDraws.filterMap (·.batch)
  let fixedCauses := fixedDraws.filterMap (·.cause?)
  let fixedOk :=
    fixedDrawers == #[p2, p3, p1] &&
    fixedBatches.size == 3 &&
    fixedBatches[0]! != fixedBatches[1]! &&
    fixedBatches[1]! != fixedBatches[2]! &&
    fixedCauses.size == 3 &&
    fixedCauses.all (· == fixedCauses[0]!)

  -- Catch-all `(who, amount)` arm (`perControlled` for `.eachOpponent`) also unbatches & follows APNAP:
  let gWithArt := addPermanent g4 { name := "P25i3 Relic", types := #[.artifact] } p0 p0
  let idxCatch := gWithArt.events.size
  let gCatch := gWithArt.applyTriggerDraw p0 none (.perControlled .artifact) .eachOpponent
  let catchDraws := (gCatch.events.extract idxCatch gCatch.events.size).filter fun e =>
    match e.change with
    | .rules (.zone (.moved _ _ _ _ (.draw _ _) _ _ _)) => true
    | _ => false
  let catchDrawers := catchDraws.filterMap fun e =>
    match e.change with
    | .rules (.zone (.moved _ _ _ _ (.draw _ _) q _ _)) => q
    | _ => none
  let catchBatches := catchDraws.filterMap (·.batch)
  let catchCauses := catchDraws.filterMap (·.cause?)
  let catchOk :=
    catchDrawers == #[p2, p3, p1] &&
    catchBatches.size == 3 &&
    catchBatches[0]! != catchBatches[1]! &&
    catchBatches[1]! != catchBatches[2]! &&
    catchCauses.size == 3 &&
    catchCauses.all (· == catchCauses[0]!)

  -- `.checkDrawThenOpponentsDraw` in `Decisions.runPostStep` also draws in APNAP order `[p2, p3, p1]`:
  let (gBefore0, drawCause) := g4.allocDelayedCause (some p0)
  let gBeforeDraw := gBefore0.draw p0 1 (cause := some drawCause)
  let idxOppLoop := gBeforeDraw.events.size
  let gOppLoop := gBeforeDraw.runPostStep (.checkDrawThenOpponentsDraw p0 0)
  let loopDraws := (gOppLoop.events.extract idxOppLoop gOppLoop.events.size).filter fun e =>
    match e.change with
    | .rules (.zone (.moved _ _ _ _ (.draw _ _) _ _ _)) => true
    | _ => false
  let loopDrawers := loopDraws.filterMap fun e =>
    match e.change with
    | .rules (.zone (.moved _ _ _ _ (.draw _ _) q _ _)) => q
    | _ => none
  let loopBatches := loopDraws.filterMap (·.batch)
  let loopCauses := loopDraws.filterMap (·.cause?)
  let oppLoopOk :=
    loopDrawers == #[p2, p3, p1] &&
    loopBatches.size == 3 &&
    loopBatches[0]! != loopBatches[1]! &&
    loopBatches[1]! != loopBatches[2]! &&
    loopCauses.size == 3 &&
    loopCauses.all (· == loopCauses[0]!)

  mustHold25i3 "2a.fixedEachOppUnbatchedApnap" fixedOk &&
  mustHold25i3 "2b.catchAllUnbatchedApnap" catchOk &&
  mustHold25i3 "2c.checkDrawThenOpponentsDrawApnap" oppLoopOk &&
  mustHold25i3 "2.replay" (replayOk25i3 #[gFixed, gCatch, gOppLoop])

-- 3. CR 702.15b lifelink aggregation & `Pending.chooseReplacement` pause-safety across
--    remaining multi-recipient noncombat damage sites + `dealDamageLoseIndestructibleExileTo`:
#guard
  let p0 : PlayerId := ⟨0⟩
  let p1 : PlayerId := ⟨1⟩
  let p2 : PlayerId := ⟨2⟩
  let llSourceDef : CardDef := {
    bear with
    name := "P25i3 Lifelink Source"
    keywords := #[Keyword.lifelink]
  }
  let toughVictimDef : CardDef := {
    bear with
    name := "P25i3 Tough Victim"
    power := some 1
    toughness := some 6
  }
  let g3 :=
    match Start.start {
      seats := #[{ name := "P0", deck := testRedDeck },
                 { name := "P1", deck := testRedDeck },
                 { name := "P2", deck := testRedDeck }]
      startingPlayer := some 0
      seed := 23 } with
    | .ok g => keepOpeningHands g 16
    | .error e => panic! e
  let gBase :=
    (addPermanent
      (addPermanent
        (addPermanent g3 llSourceDef p0 p0)
        toughVictimDef p1 p1)
      toughVictimDef p2 p2).change (.pushContinuationFrame {})
  let llSrc := (gBase.permanentsOf p0).find? (·.name == "P25i3 Lifelink Source") |>.get!
  let v1 := (gBase.permanentsOf p1).find? (·.name == "P25i3 Tough Victim") |>.get!
  let _ := (gBase.permanentsOf p2).find? (·.name == "P25i3 Tough Victim") |>.get!

  -- Helper: install two competing non-commuting damage replacement effects (+1 vs ×2)
  -- controlled by `p0` on `llSrc` so every noncombat damage packet opens `Pending.chooseReplacement`!
  let addTwoDmgReps (g : Game) : Game :=
    let add1 : ReplacementSpec := {
      id := { kind := .addNoncombatDamage, object := some llSrc.id }
      source := some llSrc.id, controller := some p0, affectedPlayer := p0
      kind := .addNoncombatDamage (some llSrc.id) 1 }
    let dbl : ReplacementSpec := {
      id := { kind := .multiplyDamage, object := some v1.id }
      source := some v1.id, controller := some p0, affectedPlayer := p0
      kind := .multiplyDamage (some llSrc.id) 2 }
    (g.createEffect (.replacement add1) (cause := some testCause)).createEffect
      (.replacement dbl) (cause := some testCause)

  let resolveAllRepChoices (g : Game) : Game := Id.run do
    let mut cur := g
    let mut fuel := 16
    while fuel > 0 do
      fuel := fuel - 1
      match cur.pending with
      | .chooseReplacement chooser choices =>
        cur := mustApply cur chooser (.chooseReplacement choices[0]!)
      | _ => fuel := 0
    return cur

  let countLifeGainsSince (g : Game) (sIdx : Nat) : Array (PlayerId × Nat × Option BatchId) :=
    (g.events.extract sIdx g.events.size).filterMap fun e =>
      match e.change with
      | .rules (.life (.gained q amt)) => some (q, amt, e.batch)
      | _ => none

  -- 3a. Unified `Instruction.dealDamageFixed` to each player:
  let gEachPl0 := addTwoDmgReps gBase
  let sEachPl := gEachPl0.events.size
  let gEachPlPaused :=
    gEachPl0.applyAbilityEffect p0 { body := Instruction.dealDamageFixed (.players .eachPlayer) 1 } #[] (some llSrc.id)
  let eachPlPausedOk := match gEachPlPaused.pending with | .chooseReplacement .. => true | _ => false
  let gEachPlDone := resolveAllRepChoices gEachPlPaused
  let eachPlGains := countLifeGainsSince gEachPlDone sEachPl
  -- Selecting `+1` then `×2` deals `(1 + 1) * 2 = 4` to each of the 3 players => single `12` life gain!
  let eachPlOk := eachPlPausedOk && eachPlGains.size == 1 && eachPlGains[0]!.1 == p0 && eachPlGains[0]!.2.1 == 12

  -- 3b. Unified `Instruction.dealDamageFixed` to each creature except your tokens:
  let gTok0 := addTwoDmgReps gBase
  let (gTok1, _) := gTok0.createToken p0 Game.humanSoldierToken (cause := some testCause)
  let sExceptTok := gTok1.events.size
  let gExceptPaused :=
    gTok1.applyAbilityEffect p0
      { body := Instruction.dealDamageFixed
          (.objects (.inZones .battlefield (.all #[.hasType .creature, .not (.all #[.isToken true, .controlledBy .you])]))) 1 }
      #[] (some llSrc.id)
  let exceptPausedOk := match gExceptPaused.pending with | .chooseReplacement .. => true | _ => false
  let gExceptDone := resolveAllRepChoices gExceptPaused
  let exceptGains := countLifeGainsSince gExceptDone sExceptTok
  -- Hits `llSrc`, `v1`, `v2` (3 non-token creatures, skipping `p0`'s Soldier token) for 4 each => single `12` life gain!
  let soldierStillUndamaged :=
    gExceptDone.battlefield.any (fun o => o.printed.isToken && o.status.damage == 0)
  let exceptTokOk :=
    exceptPausedOk && soldierStillUndamaged &&
    exceptGains.size == 1 && exceptGains[0]!.1 == p0 && exceptGains[0]!.2.1 == 12

  -- 3c. Unified `Instruction.dealDamageFixed` to each creature or planeswalker an opponent controls:
  let gOppCp0 := addTwoDmgReps gBase
  let sOppCp := gOppCp0.events.size
  let gOppCpPaused :=
    gOppCp0.applyAbilityEffect p0
      { body := Instruction.dealDamageFixed
          (.objects (.inZones .battlefield (.all #[.any #[.hasType .creature, .hasType .planeswalker], .controlledBy .opponent]))) 1 }
      #[] (some llSrc.id)
  let oppCpPausedOk := match gOppCpPaused.pending with | .chooseReplacement .. => true | _ => false
  let gOppCpDone := resolveAllRepChoices gOppCpPaused
  let oppCpGains := countLifeGainsSince gOppCpDone sOppCp
  -- Hits `v1` and `v2` for 4 each => single `8` life gain!
  let oppCpOk := oppCpPausedOk && oppCpGains.size == 1 && oppCpGains[0]!.1 == p0 && oppCpGains[0]!.2.1 == 8

  -- 3d. Unified `Instruction.dealDamageFixed` to up to one creature/planeswalker and target player:
  let upToOneAndPlEff : Effect := {
    targeting := .of { slots := #[
      { domain := .creatureOrPlaneswalker, count := .upTo 1 },
      .of .anyPlayer
    ] }
    body := Instruction.dealDamageFixed .allTargets 1
    phrase := "Deal 1 damage to up to one target creature or planeswalker and 1 damage to target player"
  }
  let gUpTo0 := addTwoDmgReps gBase
  let sUpTo := gUpTo0.events.size
  let gUpToPaused :=
    gUpTo0.applyAbilityEffect p0 upToOneAndPlEff
      #[Target.permanent v1.id, Target.player p2] (some llSrc.id)
  let upToPausedOk := match gUpToPaused.pending with | .chooseReplacement .. => true | _ => false
  let gUpToDone := resolveAllRepChoices gUpToPaused
  let upToGains := countLifeGainsSince gUpToDone sUpTo
  let upToOk := upToPausedOk && upToGains.size == 1 && upToGains[0]!.1 == p0 && upToGains[0]!.2.1 == 8

  -- 3e. `causeDealsDamageToOpponentsLoop`:
  let gCauseOpp0 := addTwoDmgReps gBase
  let sCauseOpp := gCauseOpp0.events.size
  let gCauseOppPaused :=
    gCauseOpp0.withBatch (some testCause) fun g =>
      g.causeDealsDamageToOpponentsLoop #[p1, p2] 1 "P25i3 Lifelink Source"
        (some (g.snapshot llSrc)) (some testCause) none (some sCauseOpp)
  let causeOppPausedOk := match gCauseOppPaused.pending with | .chooseReplacement .. => true | _ => false
  let gCauseOppDone := resolveAllRepChoices gCauseOppPaused
  let causeOppGains := countLifeGainsSince gCauseOppDone sCauseOpp
  let causeOppOk :=
    causeOppPausedOk && causeOppGains.size == 1 && causeOppGains[0]!.1 == p0 && causeOppGains[0]!.2.1 == 8

  -- 3f. `TriggeredAbilities.applyTriggerDamage` (`.divided` and multi-permanent `objs`) +
  --     `Pumps.dealDamageLoseIndestructibleExileTo` across `Pending.chooseReplacement`:
  let gTrig0 := addTwoDmgReps gBase
  let sDiv := gTrig0.events.size
  let divAb : TriggeredAbility := .onEnterDraw 1
  let gDivPaused :=
    gTrig0.applyTriggerDamage p0 divAb (some llSrc.id)
      #[Target.permanent v1.id, Target.player p2] none "P25i3 Lifelink Source"
      (.fixed 2) .target .divided
  let divPausedOk := match gDivPaused.pending with | .chooseReplacement .. => true | _ => false
  let gDivDone := resolveAllRepChoices gDivPaused
  let divGains := countLifeGainsSince gDivDone sDiv
  let divOk := divPausedOk && divGains.size == 1 && divGains[0]!.1 == p0 && divGains[0]!.2.1 == 8

  let sObjs := gTrig0.events.size
  let gObjsPaused :=
    gTrig0.applyTriggerDamage p0 divAb (some llSrc.id)
      #[] none "P25i3 Lifelink Source"
      (.fixed 1) .opponentsCreatures .none
  let objsPausedOk := match gObjsPaused.pending with | .chooseReplacement .. => true | _ => false
  let gObjsDone := resolveAllRepChoices gObjsPaused
  let objsGains := countLifeGainsSince gObjsDone sObjs
  let objsOk := objsPausedOk && objsGains.size == 1 && objsGains[0]!.1 == p0 && objsGains[0]!.2.1 == 8

  let sSmite := gTrig0.events.size
  let gSmitePaused := gTrig0.dealDamageLoseIndestructibleExileTo v1 1 (gTrig0.snapshot llSrc)
  let smitePausedOk := match gSmitePaused.pending with | .chooseReplacement .. => true | _ => false
  let gSmiteDone := resolveAllRepChoices gSmitePaused
  let smiteGains := countLifeGainsSince gSmiteDone sSmite
  let smiteOk :=
    smitePausedOk && smiteGains.size == 1 && smiteGains[0]!.1 == p0 && smiteGains[0]!.2.1 == 4 &&
    gSmiteDone.untilEotLosesIndestructible (gSmiteDone.object! v1.id) &&
    gSmiteDone.untilEotExileIfDies (gSmiteDone.object! v1.id)

  mustHold25i3 "3a.damageEachPlayer" eachPlOk &&
  mustHold25i3 "3b.damageEachCreatureExceptYourTokens" exceptTokOk &&
  mustHold25i3 "3c.damageEachOppCreatureAndPw" oppCpOk &&
  mustHold25i3 "3d.damageUpToOneAndPlayer" upToOk &&
  mustHold25i3 "3e.causeDealsDamageToOpponents" causeOppOk &&
  mustHold25i3 "3f.triggerDividedAndSmite" (divOk && objsOk && smiteOk) &&
  mustHold25i3 "3.replay"
    (replayOk25i3 #[gEachPlDone, gExceptDone, gOppCpDone, gUpToDone, gCauseOppDone, gDivDone, gObjsDone, gSmiteDone])

end Phase25Item3EventAlignment

section Phase25Item4EventAlignment

def mustHold25i4 (label : String) (ok : Bool) : Bool :=
  if ok then true else panic! s!"Phase 25 item 4 guard failed: {label}"

def replayOk25i4 (gs : Array Game) : Bool :=
  gs.all (fun g => Game.replayEvents g.events == g && allRulesEventsClassified g)

def mkSixSeatThreeTeams25i4 (seed : UInt64 := 2540) : Game :=
  let cfg : StartConfig := {
    seats := #[
      { name := "Chandra", deck := testRedDeck, teammate := some ⟨1⟩ },
      { name := "Nissa", deck := testGreenDeck, teammate := some ⟨0⟩ },
      { name := "Liliana", deck := testRedDeck, teammate := some ⟨3⟩ },
      { name := "Jace", deck := testGreenDeck, teammate := some ⟨2⟩ },
      { name := "Ajani", deck := testRedDeck, teammate := some ⟨5⟩ },
      { name := "Gideon", deck := testGreenDeck, teammate := some ⟨4⟩ }
    ]
    format := .constructed
    seed
    startingPlayer := some 0
  }
  match Start.start cfg with
  | .ok g => (keepOpeningHands g 40).advanceStep
  | .error e => panic! e

-- 1. CR 725.2 / 725.4 / 113.8 / 800.4a,d / 805.4, 805.4a (Rulings 937, 938, 940):
--    Inherent sourceless monarch end-step draw & combat-damage triggers + 2HG succession.
#guard
  -- 1a. 2HG monarch end-step draw fires once on the shared turn's final seat (`⟨1⟩`),
  --     stays sourceless (`ctxSrc = none`, CR 113.8), and still draws for `⟨0⟩` if `⟨2⟩`
  --     steals the monarchy before resolution (Ruling 938):
  let gMon2hg0 := (mkTwoHeadedGiant24i4 2541).becomeMonarch ⟨0⟩
  let gSeat0End := gMon2hg0.record (GameEvent.stepped gMon2hg0.turnNumber .end ⟨0⟩)
  let gSeat1 := (gSeat0End.startNextTurnCore false).record (GameEvent.stepped gMon2hg0.turnNumber .end ⟨1⟩)
  let seat1TrigQueued :=
    gSeat0End.waitingTriggers.isEmpty &&
    gSeat1.waitingTriggers.size == 1 &&
    gSeat1.waitingTriggers[0]!.controller == ⟨0⟩ &&
    gSeat1.waitingTriggers[0]!.source.id == noSourceSentinelId
  let gSeat1Stacked := gSeat1.receivePriority ⟨1⟩
  let stackObj? := gSeat1Stacked.stack.back?.bind (fun se => gSeat1Stacked.findObject? se.objectId)
  let sourcelessOnStack := stackObj?.any (fun so => so.sourceId == none)
  let hand0Before := (gSeat1Stacked.player ⟨0⟩).hand.size
  let sDraw := gSeat1Stacked.events.size
  let gSeat1StolenRes := (gSeat1Stacked.becomeMonarch ⟨2⟩).resolveTop
  let drawMovedSourceless :=
    (gSeat1StolenRes.events.extract sDraw gSeat1StolenRes.events.size).any fun e =>
      match e.change, e.cause? with
      | .rules (.zone (.moved _ _ (.library ⟨0⟩) (.hand ⟨0⟩) ..)), some (.oneShotEffect _ src _) =>
        src == none
      | _, _ => false
  let endStepDrawOk :=
    seat1TrigQueued &&
    sourcelessOnStack &&
    (gSeat1StolenRes.player ⟨2⟩).isMonarch &&
    (gSeat1StolenRes.player ⟨0⟩).hand.size == hand0Before + 1 &&
    drawMovedSourceless

  -- 1b. Multiple creatures dealing combat damage to the monarch queue one sourceless
  --     monarch trigger per attacking creature (ordered by the monarch, Ruling 940);
  --     lethal combat damage removes the monarch's waiting trigger via CR 800.4a,d (Ruling 937):
  let g3 := (mkThreePlayer24i4 2542).becomeMonarch ⟨0⟩
  let g3Bears := addPermanent (addPermanent g3 bear ⟨1⟩ ⟨1⟩) bear ⟨2⟩ ⟨2⟩
  let b1 := (g3Bears.battlefield.filter (fun o => o.name == bear.name && o.controller == some ⟨1⟩))[0]!.id
  let b2 := (g3Bears.battlefield.filter (fun o => o.name == bear.name && o.controller == some ⟨2⟩))[0]!.id
  let combatCause : EventCause := .turnBased (.dealCombatDamage false)
  let g3Hit := g3Bears.withBatch (some combatCause) fun g =>
    let g := g.record (GameEvent.damagedPlayer g.turnNumber
      (g.snapshotDamageSource (g.object! b1)) ⟨0⟩ 2 true (cause := combatCause))
    g.record (GameEvent.damagedPlayer g.turnNumber
      (g.snapshotDamageSource (g.object! b2)) ⟨0⟩ 2 true (cause := combatCause))
  let g3Prio := g3Hit.receivePriority ⟨0⟩
  let twoPrompted :=
    g3Hit.waitingTriggers.size == 2 &&
    g3Hit.waitingTriggers.all (fun w => w.controller == ⟨0⟩ && w.source.id == noSourceSentinelId) &&
    (match g3Prio.pending with | .chooseTriggerToStack ⟨0⟩ => true | _ => false)
  let g3Stacked := mustApply g3Prio ⟨0⟩ (.stackTriggers #[0, 1])
  let g3ResTop := g3Stacked.resolveTop
  let g3ResBot := g3ResTop.resolveTop
  let monarchCauseSourceless :=
    match g3ResBot.events.findRev? (fun e => match e.change with | .rules (.player (.becameMonarch ..)) => true | _ => false) with
    | some e => match e.cause? with | some (.oneShotEffect _ src _) => src == none | _ => false
    | none => false
  let multiHitOk :=
    twoPrompted &&
    (g3ResTop.player ⟨2⟩).isMonarch &&
    (g3ResBot.player ⟨1⟩).isMonarch &&
    monarchCauseSourceless

  -- Lethal combat damage: `⟨0⟩` is at 2 life on `⟨2⟩`'s turn; `⟨1⟩`'s bear deals 2 combat damage to `⟨0⟩`.
  -- `⟨0⟩`'s monarch trigger is removed when `⟨0⟩` loses/leaves (CR 800.4a,d), so active player `⟨2⟩`
  -- inherits the monarchy via CR 725.4 and `⟨1⟩` never steals it from a dead trigger!
  let g3Lethal0 := ((g3Bears.startNextTurnCore false).startNextTurnCore false).loseLife ⟨0⟩ 18 (cause := some testCause)
  let g3LethalHit := g3Lethal0.withBatch (some combatCause) fun g =>
    let g := g.record (GameEvent.damagedPlayer g.turnNumber
      (g.snapshotDamageSource (g.object! b1)) ⟨0⟩ 2 true (cause := combatCause))
    g.record (GameEvent.life g.turnNumber ⟨0⟩ 2 false true true (cause := combatCause))
  let g3LethalAfter := g3LethalHit.receivePriority ⟨2⟩
  let lethalOk :=
    g3LethalHit.waitingTriggers.size == 1 &&
    (g3LethalAfter.player ⟨0⟩).leftTheGame &&
    g3LethalAfter.waitingTriggers.isEmpty &&
    g3LethalAfter.stack.isEmpty &&
    (g3LethalAfter.player ⟨2⟩).isMonarch &&
    !(g3LethalAfter.player ⟨1⟩).isMonarch

  -- 1c. CR 725.4 2HG succession: when active player `⟨0⟩` has already departed on Seat `⟨0⟩`
  --     while teammate `⟨1⟩`'s seat has not yet begun (`!isSharedTurnFinalSeat`), an opponent
  --     monarch `⟨4⟩` leaving passes monarchy to `⟨1⟩` (`nextLiving activePlayer`), whereas on
  --     final Seat `⟨1⟩` (`isSharedTurnFinalSeat`), `⟨1⟩` leaving passes monarchy to `⟨2⟩`:
  let g6 := (mkSixSeatThreeTeams25i4 2543).becomeMonarch ⟨4⟩
  let g6MidLeave := (g6.playerLeavesGame ⟨0⟩).playerLeavesGame ⟨4⟩
  let g6FinalSeat := ((mkSixSeatThreeTeams25i4 2544).startNextTurnCore false).becomeMonarch ⟨1⟩
  let g6FinalLeave := g6FinalSeat.playerLeavesGame ⟨1⟩
  let successionOk :=
    (g6MidLeave.player ⟨1⟩).isMonarch &&
    (g6FinalLeave.player ⟨2⟩).isMonarch

  mustHold25i4 "1a.endStepDraw" endStepDrawOk &&
  mustHold25i4 "1b.multiHitAndLethal" (multiHitOk && lethalOk) &&
  mustHold25i4 "1c.succession2hg" successionOk &&
  mustHold25i4 "1.replay" (replayOk25i4 #[gSeat1StolenRes, g3ResBot, g3LethalAfter, g6MidLeave, g6FinalLeave])

-- 2. CR 302.6 / 101.2 / 800.4k,m / 805.4a / 810.2:
--    2HG shared-turn summoning sickness, active-team `opponentsCantCastOnActiveTurn` / `canCastForSneak`,
--    and `startNextTurnCore` `departed` deduplication.
#guard
  let g0 := mkTwoHeadedGiant24i4 2545
  let gIns := insertObject (insertObject g0 bear ⟨0⟩ (.hand ⟨0⟩)) bear ⟨1⟩ (.hand ⟨1⟩)
  let c0Card := (gIns.player ⟨0⟩).hand.back!
  let c1Card := (gIns.player ⟨1⟩).hand.back!
  let (gPut0, c0Id) := gIns.putOntoBattlefield c0Card ⟨0⟩ (cause := some testCause)
  let (gPut1, c1Id) := gPut0.putOntoBattlefield c1Card ⟨1⟩ (cause := some testCause)
  let gWithOpp := addPermanent gPut1 bear ⟨2⟩ ⟨2⟩
  let stolenId := (gWithOpp.battlefield.filter (fun o => o.name == bear.name && o.controller == some ⟨2⟩))[0]!.id
  let gStolen := gWithOpp.createEffect (.layered (.objects #[stolenId]) (.control ⟨1⟩) .indefinite) (cause := some testCause)
  -- Advance from Seat `⟨0⟩` into Seat `⟨1⟩` of the SAME shared turn (including `⟨1⟩`'s untap step):
  let gMateSeat := gStolen.startNextTurnAndBegin
  let stillSickOnMateSeat :=
    gMateSeat.activePlayer == ⟨1⟩ &&
    (gMateSeat.object! c0Id).status.summoningSick &&
    (gMateSeat.object! c1Id).status.summoningSick &&
    gMateSeat.hasSummoningSickness (gMateSeat.object! c0Id) &&
    gMateSeat.hasSummoningSickness (gMateSeat.object! c1Id) &&
    gMateSeat.hasSummoningSickness (gMateSeat.object! stolenId)
  -- Advance through Team B (`⟨2⟩`, `⟨3⟩`) back to Team A's next shared turn (`⟨0⟩`):
  let gNextTeamA := ((gMateSeat.startNextTurnAndBegin).startNextTurnAndBegin).startNextTurnAndBegin
  let clearedOnNextSharedTurn :=
    gNextTeamA.activePlayer == ⟨0⟩ &&
    !(gNextTeamA.object! c0Id).status.summoningSick &&
    !(gNextTeamA.object! c1Id).status.summoningSick &&
    !gNextTeamA.hasSummoningSickness (gNextTeamA.object! c0Id) &&
    !gNextTeamA.hasSummoningSickness (gNextTeamA.object! c1Id) &&
    !gNextTeamA.hasSummoningSickness (gNextTeamA.object! stolenId)

  -- Active-team `opponentsCantCastOnActiveTurn` & `canCastForSneak`:
  let grandAbolisherDef : CardDef := {
    bear with
    name := "P25i4 Team Abolisher"
    staticAbilities := #[.opponentsCantCastOnYourTurn]
  }
  let gAbol := addPermanent g0 grandAbolisherDef ⟨1⟩ ⟨1⟩
  let gBlk := gAbol.record (GameEvent.stepped gAbol.turnNumber .declareBlockers ⟨0⟩)
  let activeTeamChecksOk :=
    !gBlk.opponentsCantCastOnActiveTurn ⟨0⟩ &&
    !gBlk.opponentsCantCastOnActiveTurn ⟨1⟩ &&
    gBlk.opponentsCantCastOnActiveTurn ⟨2⟩ &&
    gBlk.canCastForSneak ⟨0⟩ &&
    gBlk.canCastForSneak ⟨1⟩ &&
    !gBlk.canCastForSneak ⟨2⟩

  -- `Turns.startNextTurnCore` deduplicates `departed` when a player with multiple queued extra turns leaves:
  let g3Ex0 := addPermanent (mkThreePlayer24i4 2546) bear ⟨0⟩ ⟨0⟩
  let exBearId := (g3Ex0.battlefield.filter (·.name == bear.name))[0]!.id
  let g3Ex1 := (g3Ex0.record (GameEvent.extraTurnAdded g3Ex0.turnNumber ⟨1⟩ (cause := testCause)))
    |>.record (GameEvent.extraTurnAdded g3Ex0.turnNumber ⟨1⟩ (cause := testCause))
  let g3Ex3 := g3Ex1.createEffect
    (.layered (.objects #[exBearId]) (.ptModify 1 1) (.untilEndOfNextTurnOf ⟨1⟩))
    (cause := some testCause)
  let g3ExDeparted := (g3Ex3.concede ⟨1⟩).startNextTurnCore false
  let departedDedupOk :=
    g3ExDeparted.activePlayer == ⟨2⟩ &&
    g3ExDeparted.activeEffects.isEmpty &&
    g3ExDeparted.power (g3ExDeparted.object! exBearId) == 2

  mustHold25i4 "2a.sharedTurnSummoningSickness" (stillSickOnMateSeat && clearedOnNextSharedTurn) &&
  mustHold25i4 "2b.activeTeamAndDeparted" (activeTeamChecksOk && departedDedupOk) &&
  mustHold25i4 "2.replay" (replayOk25i4 #[gStolen, gMateSeat, gNextTeamA, gBlk, g3ExDeparted])

-- 3. CR 109.2 / 118.12a / 205.3j / 508.1d / 508.4c / 603.7c / 608.2h:
--    *Jace, Multiverse Architect* `{2}` tax & controller/subtype-scoped `cantAttackJace`,
--    plus `.merfolkAttackPlayer`, `.creatureAttacksYouOrYourPlaneswalker`, and *Garruk, Curse Breaker* scoping.
#guard
  let jaceSubDef : CardDef := { name := "Sculptor of Minds", types := #[.planeswalker], subtypes := #["Jace"], loyalty := some 4 }
  let fakeJaceNameDef : CardDef := { name := "Jace Impostor", types := #[.planeswalker], subtypes := #["Bolas"], loyalty := some 4 }
  let addPw4 (g : Game) (c : CardDef) (p : PlayerId) : Game :=
    insertObject g c p .battlefield (some p) { summoningSick := false, counters := #[(.loyalty, 4)] }
  let g2hg := mkTwoHeadedGiant24i4 2547
  let gJ0 := addPw4 (addPw4 (addPw4 g2hg jaceSubDef ⟨2⟩) jaceSubDef ⟨3⟩) fakeJaceNameDef ⟨2⟩
  let j2Id := (gJ0.battlefield.filter (fun o => o.name == jaceSubDef.name && o.controller == some ⟨2⟩))[0]!.id
  let j3Id := (gJ0.battlefield.filter (fun o => o.name == jaceSubDef.name && o.controller == some ⟨3⟩))[0]!.id
  let fakeId := (gJ0.battlefield.filter (fun o => o.name == fakeJaceNameDef.name))[0]!.id
  let handBeforePay := (gJ0.player ⟨0⟩).hand.size
  let gJWithMana := gJ0.addMana ⟨0⟩ .colorless 2
  let jaceTaxEff := jaceMultiverseArchitect.triggeredAbilities[0]!.effect
  let gJPromptPay := (gJWithMana.change (.pushContinuationFrame {})).applyAbilityEffect ⟨2⟩ jaceTaxEff #[] (some j2Id)
  let gJPaid := mustApply gJPromptPay ⟨0⟩ .payGeneric
  let paidOk :=
    gJPaid.pending == .none &&
    (gJPaid.player ⟨0⟩).hand.size == handBeforePay &&
    !gJPaid.cantAttackJace ⟨0⟩ (gJPaid.object! j2Id)

  let gJPromptDec := (gJ0.change (.pushContinuationFrame {})).applyAbilityEffect ⟨2⟩ jaceTaxEff #[] (some j2Id)
  let gJDeclined := mustApply gJPromptDec ⟨0⟩ .decline
  let declinedScopedOk :=
    gJDeclined.cantAttackJace ⟨0⟩ (gJDeclined.object! j2Id) &&
    !gJDeclined.cantAttackJace ⟨0⟩ (gJDeclined.object! j3Id) &&
    !gJDeclined.cantAttackJace ⟨0⟩ (gJDeclined.object! fakeId)

  -- Conceding in a 3-player game while `.payOrLetCounter` is pending cleanly flushes `unlessPays`:
  let g3J0 := addPw4 (mkThreePlayer24i4 2548) jaceSubDef ⟨1⟩
  let j3pId := (g3J0.battlefield.filter (·.name == jaceSubDef.name))[0]!.id
  let g3JPrompt := (g3J0.change (.pushContinuationFrame {})).applyAbilityEffect ⟨1⟩ jaceTaxEff #[] (some j3pId)
  let g3JConcede := g3JPrompt.concede ⟨0⟩
  let concedeFlushOk :=
    (g3JConcede.player ⟨0⟩).leftTheGame &&
    g3JConcede.pending != .payOrLetCounter ⟨0⟩ 2 none &&
    g3JConcede.unlessPaysInstead.isNone

  -- `.merfolkAttackPlayer`, `.creatureAttacksYouOrYourPlaneswalker`, and *Garruk, Curse Breaker* locked attackers:
  let merfolkDef : CardDef := creature "P25i4 Merfolk" ManaCost.empty #["Merfolk"] 2 2
  let merfolkWatcherDef : CardDef := {
    bear with
    name := "P25i4 Merfolk Watcher"
    triggeredAbilities := #[TriggeredAbility.onWatch Effect.watchMerfolkAttackDraw]
  }
  let revengeWatcherDef : CardDef := {
    bear with
    name := "P25i4 Revenge Watcher"
    triggeredAbilities := #[TriggeredAbility.ofPattern .creatureAttacksYouOrYourPlaneswalker "" (Instruction.gainLifeFixed 1)]
  }
  let garrukWatcherDef : CardDef := {
    bear with
    name := "P25i4 Garruk Watcher"
    triggeredAbilities := #[TriggeredAbility.ofPattern .creaturesAttackYourOpponent "" (Instruction.pumpAndTrample .triggerSubject 2 2) (grouping := .perPlayerInBatch)]
  }
  let battleDef : CardDef := {
    name := "P25i4 Siege Battle"
    types := #[.battle]
    subtypes := #["Siege"]
    defense := some 4
  }
  let gComb0 :=
    let g := mkThreePlayer24i4 2549
    let g := addPermanent (addPermanent g merfolkDef ⟨0⟩ ⟨0⟩) merfolkWatcherDef ⟨0⟩ ⟨0⟩
    let g := addPermanent (addPermanent (addPw4 g jaceSubDef ⟨1⟩) battleDef ⟨1⟩ ⟨1⟩) revengeWatcherDef ⟨1⟩ ⟨1⟩
    addPermanent g garrukWatcherDef ⟨2⟩ ⟨2⟩
  let mfId := (gComb0.battlefield.filter (·.name == merfolkDef.name))[0]!.id
  let pw1Id := (gComb0.battlefield.filter (·.name == jaceSubDef.name))[0]!.id
  let bat1Id := (gComb0.battlefield.filter (·.name == battleDef.name))[0]!.id
  let declCause := some (EventCause.turnBased .declareAttackers)
  -- Attacking a planeswalker: fires `.creatureAttacksYouOrYourPlaneswalker` for `⟨1⟩`, NOT `.merfolkAttackPlayer` or Garruk!
  let mfSnapPw := { (gComb0.snapshot (gComb0.object! mfId)) with attacking := true, attackingTarget := some (.planeswalker pw1Id) }
  let gAtkPw := gComb0.record (GameEvent.attackersDeclared gComb0.turnNumber ⟨0⟩ #[(mfSnapPw, .planeswalker pw1Id)] (cause := declCause))
  let atkPwOk :=
    gAtkPw.waitingTriggers.size == 1 &&
    gAtkPw.waitingTriggers[0]!.controller == ⟨1⟩ &&
    gAtkPw.waitingTriggers[0]!.pattern == .creatureAttacksYouOrYourPlaneswalker
  -- Attacking a battle: fires NEITHER `.merfolkAttackPlayer` NOR `.creatureAttacksYouOrYourPlaneswalker` NOR Garruk!
  let mfSnapBat := { (gComb0.snapshot (gComb0.object! mfId)) with attacking := true, attackingTarget := some (.battle bat1Id) }
  let gAtkBat := gComb0.record (GameEvent.attackersDeclared gComb0.turnNumber ⟨0⟩ #[(mfSnapBat, .battle bat1Id)] (cause := declCause))
  let atkBatOk := gAtkBat.waitingTriggers.isEmpty
  -- Attacking player `⟨1⟩`: fires `.merfolkAttackPlayer`, `.creatureAttacksYouOrYourPlaneswalker`, AND `⟨2⟩`'s Garruk (locking `#[mfId]`):
  let mfSnapPl := { (gComb0.snapshot (gComb0.object! mfId)) with attacking := true, attackingTarget := some (.player ⟨1⟩) }
  let gAtkPl0 := gComb0.record (GameEvent.attackersDeclared gComb0.turnNumber ⟨0⟩ #[(mfSnapPl, .player ⟨1⟩)] (cause := declCause))
  let gAtkPlStacked := gAtkPl0.receivePriority ⟨0⟩
  -- Put a second creature onto the battlefield tapped & attacking `⟨1⟩` BEFORE Garruk's trigger on top of stack resolves:
  let gAtkWithLate := insertObject gAtkPlStacked bear ⟨0⟩ (.hand ⟨0⟩)
  let lateCard := (gAtkWithLate.player ⟨0⟩).hand.back!
  let (gAtkLateEntered, lateId) := gAtkWithLate.putOntoBattlefield lateCard ⟨0⟩
    (tapped := true) (attacking := true) (attackingTarget := some (.player ⟨1⟩)) (cause := some testCause)
  -- APNAP puts `⟨0⟩` bottom, `⟨1⟩` middle, `⟨2⟩` (Garruk) on top! Resolve top (Garruk):
  let gGarrukRes := gAtkLateEntered.resolveTop
  let garrukLockedOk :=
    gGarrukRes.power (gGarrukRes.object! mfId) == 4 &&
    gGarrukRes.toughness (gGarrukRes.object! mfId) == 4 &&
    gGarrukRes.hasTrample (gGarrukRes.object! mfId) &&
    gGarrukRes.power (gGarrukRes.object! lateId) == 2 &&
    !gGarrukRes.hasTrample (gGarrukRes.object! lateId)

  mustHold25i4 "3a.jaceTaxPayDeclineConcede" (paidOk && declinedScopedOk && concedeFlushOk) &&
  mustHold25i4 "3b.combatTriggerScoping" (atkPwOk && atkBatOk && garrukLockedOk) &&
  mustHold25i4 "3.replay" (replayOk25i4 #[gJPaid, gJDeclined, g3JConcede, gAtkPw, gAtkBat, gGarrukRes])

-- 4. CR 122.1c–d / 611.2a / 613.1a,c / 704.5q / 800.4c:
--    Shield, stun, and CR 704.5q counter removals routed through `recordRemoveCounters`
--    (`.whileSourceHasCounter` expiry + CR 800.4c control exile) and layer-resolved `g.name` logs.
#guard
  let gBase := addPermanent afterDraw bear me me
  let bId := (gBase.battlefield.filter (·.name == bear.name))[0]!.id
  -- 4a. Shield counter removals (`destroyPermanent`, prevented `markDamageOn`, unpreventable `markDamageOn`):
  let mkShielded : Game :=
    let g := gBase.recordPutCounters bId .shield 1 (byPlayer := some me) (cause := some testCause)
    g.createEffect (.layered (.objects #[bId]) (.ptModify 3 3) (.whileSourceHasCounter bId .shield))
      (cause := some testCause)
  let gShieldDestroy := mkShielded.destroyPermanent (mkShielded.object! bId) (cause := some testCause)
  let gShieldPrevDmg := mkShielded.markDamageOn (mkShielded.object! bId) 2 "" (cause := some testCause)
  let gShieldUnprevDmg := mkShielded.markDamageOn (mkShielded.object! bId) 1 "" (unpreventable := true) (cause := some testCause)
  let shieldExpiryOk :=
    gShieldDestroy.power (gShieldDestroy.object! bId) == 2 &&
    gShieldPrevDmg.power (gShieldPrevDmg.object! bId) == 2 &&
    gShieldUnprevDmg.power (gShieldUnprevDmg.object! bId) == 2 &&
    (gShieldUnprevDmg.object! bId).status.damage == 1

  -- 4b. Stun counter removals (`untapStepPermanents` and `untapPermanent`):
  let mkStunned : Game :=
    let g := (gBase.becomeTapped (gBase.object! bId) (cause := some testCause))
      |>.recordPutCounters bId .stun 1 (byPlayer := some me) (cause := some testCause)
    g.createEffect (.layered (.objects #[bId]) (.ptModify 2 2) (.whileSourceHasCounter bId .stun))
      (cause := some testCause)
  let gStunStep := mkStunned.untapStepPermanents #[bId]
  let gStunEffect := mkStunned.untapPermanent (mkStunned.object! bId) (cause := some testCause)
  let stunExpiryOk :=
    (gStunStep.object! bId).status.tapped &&
    (gStunStep.object! bId).status.stun == 0 &&
    gStunStep.power (gStunStep.object! bId) == 2 &&
    (gStunEffect.object! bId).status.tapped &&
    (gStunEffect.object! bId).status.stun == 0 &&
    gStunEffect.power (gStunEffect.object! bId) == 2

  -- 4c. CR 704.5q counter annihilation expires `.whileSourceHasCounter` Layer 2 control
  --     via `endControlEffectById` BEFORE `expireMatching`, exiling `victimId` under CR 800.4c
  --     when its default controller `⟨1⟩` has left the game:
  let g3 := mkThreePlayer24i4 2550
  let g3Src := addPermanent g3 bear ⟨0⟩ ⟨0⟩
  let srcId := (g3Src.battlefield.filter (·.name == bear.name))[0]!.id
  let g3Ins := insertObject g3Src bear ⟨0⟩ (.hand ⟨0⟩)
  let vCard := (g3Ins.player ⟨0⟩).hand.back!
  -- `⟨0⟩` owns `vCard`, put onto battlefield under `⟨1⟩`'s control (`defaultController = some ⟨1⟩`):
  let (g3Put, victimId) := g3Ins.putOntoBattlefield vCard ⟨1⟩ (cause := some testCause)
  let g3Plus := g3Put.recordPutCounters srcId .plusOnePlusOne 1 (byPlayer := some ⟨0⟩) (cause := some testCause)
  let g3Ctrl := g3Plus.createEffect
    (.layered (.objects #[victimId]) (.control ⟨2⟩) (.whileSourceHasCounter srcId .plusOnePlusOne))
    (cause := some testCause)
  -- `⟨1⟩` concedes (`victimId` is owned by `⟨0⟩` and controlled by `⟨2⟩`, so it remains on battlefield):
  let g3AfterConcede := g3Ctrl.concede ⟨1⟩
  let stillOnBfBefore7045q := (g3AfterConcede.object! victimId).isOnBattlefield
  -- Put a `-1/-1` counter on `srcId` and run SBAs (CR 704.5q removes `+1/+1` & `-1/-1` pair -> CR 800.4c exiles `victimId`!):
  let g3Annihilated := (g3AfterConcede.recordPutCounters srcId .minusOneMinusOne 1
    (byPlayer := some ⟨0⟩) (cause := some testCause)).checkSBA
  let cr7045q8004cOk :=
    stillOnBfBefore7045q &&
    (g3Annihilated.object! srcId).status.plusOnePlusOne == 0 &&
    (g3Annihilated.object! srcId).status.minusOneMinusOne == 0 &&
    (g3Annihilated.findObject? victimId).isNone &&
    (g3Annihilated.object! (g3Annihilated.followMoved victimId)).zone == .exile &&
    g3Annihilated.log.any (fun s => s.contains "CR 800.4c")

  -- 4d. Layer-resolved `g.name` in pump & lethal-damage SBA logs (CR 613.1a,c):
  let renamedDef : CardDef := creature "Renamed Champion" ManaCost.empty #["Hero"] 2 2
  let gCopy := gBase.createEffect
    (.layered (.objects #[bId]) (.copy renamedDef) .untilEndOfTurn)
    (cause := some testCause)
  let gPumped := gCopy.pumpPermanent (gCopy.object! bId) 1 1
  let gLethal := (gPumped.markDamageOn (gPumped.object! bId) 3 "" (cause := some testCause)).checkSBA
  let layerNameLogOk :=
    gPumped.log.any (fun s => s.contains "Renamed Champion gets +1/+1") &&
    gLethal.log.any (fun s => s.contains "Renamed Champion dies from lethal damage")

  mustHold25i4 "4a.shieldExpiry" shieldExpiryOk &&
  mustHold25i4 "4b.stunExpiry" stunExpiryOk &&
  mustHold25i4 "4c.cr7045qAnd8004c" cr7045q8004cOk &&
  mustHold25i4 "4d.layerNameLog" layerNameLogOk &&
  mustHold25i4 "4.replay" (replayOk25i4 #[gShieldDestroy, gShieldPrevDmg, gShieldUnprevDmg, gStunStep, gStunEffect, g3Annihilated, gLethal])

end Phase25Item4EventAlignment

section Phase26Item1EventAlignment

def mustHold26i1 (label : String) (ok : Bool) : Bool :=
  if ok then true else panic! s!"Phase 26 item 1 guard failed: {label}"

def replayOk26i1 (gs : Array Game) : Bool :=
  gs.all (fun g => Game.replayEvents g.events == g && allRulesEventsClassified g)

def mkThreePlayer26i1 (seed : UInt64 := 2610) : Game :=
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

def mkSixSeatThreeTeams26i1 (seed : UInt64 := 2611) : Game :=
  let cfg : StartConfig := {
    seats := #[
      { name := "Chandra", deck := testRedDeck, teammate := some ⟨1⟩ },
      { name := "Nissa", deck := testGreenDeck, teammate := some ⟨0⟩ },
      { name := "Liliana", deck := testRedDeck, teammate := some ⟨3⟩ },
      { name := "Jace", deck := testGreenDeck, teammate := some ⟨2⟩ },
      { name := "Ajani", deck := testRedDeck, teammate := some ⟨5⟩ },
      { name := "Gideon", deck := testGreenDeck, teammate := some ⟨4⟩ }
    ]
    format := .constructed
    seed
    startingPlayer := some 0
  }
  match Start.start cfg with
  | .ok g => (keepOpeningHands g 40).advanceStep
  | .error e => panic! e

def openProposalActionDepth26i1 (g : Game) : Nat :=
  g.events.foldl (fun d e =>
    match e.change with
    | .engine (.beginProposalAction _) => d + 1
    | .engine .endProposalAction => d - 1
    | _ => d) 0

-- 1. CR 104.3a / 610.3 / 733.1 / 800.4a:
--    Mid-proposal player departure inside a paused `depth > 0` `.action` bracket is partitioned
--    outside the cost action and preserved across `reverseToProposalCheckpointCore?`, remapping
--    `ZoneEvent.ceasedToExist` and CR 800.4a `ZoneEvent.moved` onto `ckpt` object IDs.
#guard
  let p0 : PlayerId := ⟨0⟩
  let p1 : PlayerId := ⟨1⟩
  let p2 : PlayerId := ⟨2⟩
  let rggSpellDef : CardDef := {
    name := "P26i1 RGG Spell"
    manaCost := ⟨#[.colored .red, .colored .green, .colored .green]⟩
    types := #[.instant]
    spellEffect := some { body := Instruction.drawFixed 1, phrase := "Draw a card" }
  }
  let painLandDef : CardDef := {
    name := "P26i1 Pain Land"
    types := #[.land]
    activatedAbilities := #[ActivatedAbility.manaAbility (.sequence #[(.colored .red, .const 1)]) (damageYou := 1)]
  }
  let treasureCardDef : CardDef := {
    name := "P26i1 Lotus Petal"
    types := #[.artifact]
    activatedAbilities := #[ActivatedAbility.manaTapSacrificeAnyColor]
  }
  let gBase := mkThreePlayer26i1 2612
  -- `p1` owns `treasureCardDef` controlled by `p0`; `p2` owns `bear` controlled by `p1`:
  let g0 :=
    insertObject
      (addPermanent
        (addPermanent
          (addPermanent
            (addPermanent gBase bear p1 p1)
            painLandDef p0 p0)
          treasureCardDef p1 p0)
        bear p2 p1)
      rggSpellDef p0 (.hand p0)
  let p1OwnBearId := (g0.battlefield.filter (fun o => o.name == bear.name && o.owner == p1))[0]!.id
  let p2BearUnderP1Id := (g0.battlefield.filter (fun o => o.name == bear.name && o.owner == p2))[0]!.id
  let painLandId := (g0.battlefield.filter (·.name == painLandDef.name))[0]!.id
  let treasId := (g0.battlefield.filter (·.name == treasureCardDef.name))[0]!.id
  let spellId := (g0.player p0).hand.back!
  let idAdd : ReplacementId := { kind := .addNoncombatDamage, object := some p1OwnBearId }
  let idMul : ReplacementId := { kind := .multiplyDamage, object := some p1OwnBearId }
  let gWithReps :=
    (g0.createEffect (.replacement {
      id := idAdd, source := some p1OwnBearId, controller := some p2,
      affectedPlayer := p0, kind := .addNoncombatDamage (some painLandId) 2
    }) (cause := some testCause)).createEffect (.replacement {
      id := idMul, source := some p1OwnBearId, controller := some p2,
      affectedPlayer := p0, kind := .multiplyDamage (some painLandId) 2
    }) (cause := some testCause)
  -- `p0` proposes `rggSpellDef`, sacrifices `p1`-owned `treasId` for `{R}` (`treasId -> treasGyId`),
  -- then taps `painLandId` (`openProposalActionDepth26i1 == 1`, paused on `Pending.chooseReplacement p0`):
  let gCast := mustApply gWithReps p0 (.cast spellId)
  let gAfterTreas := mustApply gCast p0 (.tapForMana treasId (.colored .red))
  let treasGyId := gAfterTreas.followMoved treasId
  let gPaused := mustApply gAfterTreas p0 (.tapForMana painLandId (.colored .red))
  -- While `openProposalActionDepth26i1 == 1`, `p1` concedes!
  let gAfterConcede := mustApply gPaused p1 .concede
  let gResumed :=
    match gAfterConcede.pending with
    | .chooseReplacement q cs => mustApply gAfterConcede q (.chooseReplacement cs[0]!)
    | _ => gAfterConcede
  -- Insufficient mana (`{R}{R}` vs `{R}{G}{G}`) reverses the proposal via CR 733.1:
  let gRev := mustApply gResumed p0 .pay
  let ckptDepartureOk :=
    openProposalActionDepth26i1 gPaused == 1 &&
    treasGyId != treasId &&
    (gAfterConcede.player p1).leftTheGame &&
    gRev.proposalCheckpoint.isNone &&
    gRev.proposedSpell.isNone &&
    gRev.pending == .none &&
    (gRev.player p1).leftTheGame &&
    (gRev.findObject? treasId).isNone &&
    (gRev.findObject? treasGyId).isNone &&
    (gRev.findObject? p1OwnBearId).isNone &&
    (gRev.findObject? p2BearUnderP1Id).isNone &&
    (gRev.object! (gRev.followMoved p2BearUnderP1Id)).zone == .exile &&
    !(gRev.object! painLandId).status.tapped &&
    (gRev.player p0).life == 20 &&
    (gRev.player p0).manaPool.total == 0 &&
    (gRev.player p0).hand.contains spellId
  mustHold26i1 "1.ckptDeparturePreserved" ckptDepartureOk &&
  mustHold26i1 "1.replay" (replayOk26i1 #[gPaused, gAfterConcede, gResumed, gRev])

-- 2. CR 601.2 / 800.4a / 810.8a:
--    Non-owner `proposedSpell` abort, `.mayCastUpToFromExile` pruning, post-cast cleanup,
--    2HG `concedePlayersLoop` proposal abort, and CR 800.4a opponent-owned controlled stack-card exile.
#guard
  let p0 : PlayerId := ⟨0⟩
  let p1 : PlayerId := ⟨1⟩
  let p2 : PlayerId := ⟨2⟩
  let gBase := mkThreePlayer26i1 2613
  let redInstDef : CardDef := {
    name := "P26i1 Red Instant"
    manaCost := ⟨#[.colored .red]⟩
    types := #[.instant]
    spellEffect := some { body := Instruction.drawFixed 1, phrase := "Draw a card" }
  }
  let freeInstDef : CardDef := {
    name := "P26i1 Free Instant"
    manaCost := ManaCost.empty
    types := #[.instant]
    spellEffect := some { body := Instruction.drawFixed 1, phrase := "Draw a card" }
  }

  -- 2a. Non-owner `proposedSpell` abort (`p0` proposing `p1`'s exiled card) & `.mayCastUpToFromExile` pruning:
  let gEx0 :=
    insertObject (insertObject gBase redInstDef p1 .exile) redInstDef p2 .exile
  let p1ExId := (gEx0.objects.filter (fun o => o.zone == .exile && o.owner == p1))[0]!.id
  let p2ExId := (gEx0.objects.filter (fun o => o.zone == .exile && o.owner == p2))[0]!.id
  let gExPerm :=
    (gEx0.createEffect (.permission p0 (.playFromExile p1ExId { player := p0 }) .untilEndOfTurn) (cause := some testCause)).createEffect
      (.permission p0 (.playFromExile p2ExId { player := p0 }) .untilEndOfTurn) (cause := some testCause)
  let gPrunePrompt := gExPerm.change (.pending (.fraChoice p0 (.mayCastUpToFromExile #[p1ExId, p2ExId] 2)))
  let gPruned := mustApply gPrunePrompt p1 .concede
  let prunePromptOk :=
    (gPruned.player p1).leftTheGame &&
    (gPruned.findObject? p1ExId).isNone &&
    (match gPruned.pending with
     | .fraChoice q (.mayCastUpToFromExile ids left) => q == p0 && ids == #[p2ExId] && left == 2
     | _ => false)

  -- `p0` proposes `p1ExId` (paused at `.activateManaAbilities p0`) with `pendingMayCastFromExile` waiting;
  -- `p1` concedes -> `p0`'s proposal of `p1`'s card is aborted and `p2ExId` is re-offered!
  let gNonOwnerProp :=
    (mustApply (gExPerm.change (.pushContinuationFrame {})) p0 (.cast p1ExId)).changes #[
      .clearProposalCheckpoint,
      .continuation (.pendingMayCastFromExile (some (p0, #[p1ExId, p2ExId], 1))) ]
  let gNonOwnerAborted := mustApply gNonOwnerProp p1 .concede
  let nonOwnerAbortOk :=
    gNonOwnerProp.proposedSpell.isSome &&
    (gNonOwnerAborted.player p1).leftTheGame &&
    gNonOwnerAborted.proposedSpell.isNone &&
    gNonOwnerAborted.proposalCheckpoint.isNone &&
    (gNonOwnerAborted.findObject? p1ExId).isNone &&
    (match gNonOwnerAborted.pending with
     | .fraChoice q (.mayCastUpToFromExile ids left) => q == p0 && ids == #[p2ExId] && left == 1
     | _ => false)

  -- 2b. 6-seat (3-team) 2HG `concedePlayersLoop` proposal abort when teammate `⟨0⟩` concedes
  --     while `⟨1⟩` is `prop.caster` (including when `Pending.chooseReplacement` is on `⟨2⟩ != prop.caster`):
  let g6 := mkSixSeatThreeTeams26i1 2614
  let g6Hand := mustApply (insertObject g6 redInstDef ⟨1⟩ (.hand ⟨1⟩)) ⟨0⟩ .pass
  let s1SpellId := (g6Hand.player ⟨1⟩).hand.back!
  let g6Prop := mustApply g6Hand ⟨1⟩ (.cast s1SpellId)
  let g6OtherChooser :=
    let g := addPermanent (addPermanent g6Prop bear ⟨2⟩ ⟨2⟩) bear ⟨2⟩ ⟨2⟩
    let bA := (g.battlefield.filter (·.controller == some ⟨2⟩))[0]!.id
    let bB := (g.battlefield.filter (·.controller == some ⟨2⟩))[1]!.id
    let rA : ReplacementId := { kind := .addNoncombatDamage, object := some bA }
    let rB : ReplacementId := { kind := .multiplyDamage, object := some bB }
    g.change (.pending (.chooseReplacement ⟨2⟩ #[rA, rB]))
  let g6Conceded := mustApply g6OtherChooser ⟨0⟩ .concede
  let twoHgAbortOk :=
    (g6Conceded.player ⟨0⟩).leftTheGame &&
    (g6Conceded.player ⟨1⟩).leftTheGame &&
    g6Conceded.proposedSpell.isNone &&
    g6Conceded.proposalCheckpoint.isNone &&
    g6Conceded.pending == .none &&
    g6Conceded.stillInGame g6Conceded.priority

  -- 2c. CR 800.4a opponent-owned card spell on `.stack` controlled by departing `p1` is EXILED
  --     (and `.payWard` / `.payOrLetCounter` skip countering it into `p0`'s graveyard):
  let gSt0 := insertObject gBase freeInstDef p0 .exile
  let p0FreeExId := (gSt0.objects.filter (fun o => o.zone == .exile && o.owner == p0))[0]!.id
  let gStPerm :=
    (gSt0.createEffect (.permission p1 (.playFromExile p0FreeExId { player := p1, withoutManaCost := true }) .untilEndOfTurn)
      (cause := some testCause))
  let gP1Prio := mustApply gStPerm p0 .pass
  let gOnStack := mustApply gP1Prio p1 (.cast p0FreeExId)
  let stackCardId := gOnStack.stack.back!.objectId
  let gDirectLeave := mustApply gOnStack p1 .concede
  let gWardLeave := mustApply (gOnStack.change (.pending (.payWard p1 stackCardId (CostSpec.ofGeneric 2)))) p1 .concede
  let gCounterLeave := mustApply (gOnStack.change (.pending (.payOrLetCounter p1 2 (some stackCardId)))) p1 .concede
  let exiledNotGrave (g : Game) : Bool :=
    let finalObj := g.object! (g.followMoved stackCardId)
    g.stack.isEmpty && finalObj.zone == .exile && !(g.player p0).graveyard.contains finalObj.id
  let stackExileOk :=
    (gOnStack.object! stackCardId).owner == p0 &&
    (gOnStack.object! stackCardId).controller == some p1 &&
    exiledNotGrave gDirectLeave &&
    exiledNotGrave gWardLeave &&
    exiledNotGrave gCounterLeave

  mustHold26i1 "2a.prunePromptOk" prunePromptOk &&
  mustHold26i1 "2a.nonOwnerAbortOk" nonOwnerAbortOk &&
  mustHold26i1 "2b.twoHgAbortOk" twoHgAbortOk &&
  mustHold26i1 "2c.stackExileOk" stackExileOk &&
  mustHold26i1 "2.replay"
    (replayOk26i1 #[gPruned, gNonOwnerAborted, g6Conceded, gOnStack, gDirectLeave, gWardLeave, gCounterLeave])

-- 3. CR 608.2b / 701.22 / 701.25 / 800.4a,c,f:
--    `popOuter` single-pop preservation across paused post-leave SBA continuations,
--    stale-ID `.mayMoveAllCounters` & `surveilMoveLoop`, `.tricksterLibrary` connive tail,
--    `.scry`/`.surveil` departure `declineMayThenCore` + `finishLibraryLookCore`,
--    `finishDiscardTwoDraws` departed-opponent filter, and `Library.draw` departed-player no-op.
#guard
  let p0 : PlayerId := ⟨0⟩
  let p1 : PlayerId := ⟨1⟩
  let p2 : PlayerId := ⟨2⟩
  let gBase := mkThreePlayer26i1 2615

  -- 3a. `popOuter` preserved once across paused post-leave SBA replacement choice (`saved? == none, popOuter == true`):
  let zeroZeroDef : CardDef := creature "P26i1 Fragile" ManaCost.empty #[] 0 0
  let leyA : CardDef := { name := "P26i1 Leyline A", types := #[.enchantment] }
  let leyB : CardDef := { name := "P26i1 Leyline B", types := #[.enchantment] }
  let anthemDef : CardDef := { name := "P26i1 Anthem", types := #[.enchantment] }
  let gPop0 :=
    addPermanent (addPermanent (addPermanent (addPermanent gBase zeroZeroDef p2 p2) leyA p0 p0) leyB p0 p0) anthemDef p1 p1
  let fragId := (gPop0.battlefield.filter (·.name == zeroZeroDef.name))[0]!.id
  let leyAId := (gPop0.battlefield.filter (·.name == leyA.name))[0]!.id
  let leyBId := (gPop0.battlefield.filter (·.name == leyB.name))[0]!.id
  let anthId := (gPop0.battlefield.filter (·.name == anthemDef.name))[0]!.id
  let ridA : ReplacementId := { kind := .exileOppDeath, object := some leyAId }
  let ridB : ReplacementId := { kind := .exileOppDeath, object := some leyBId }
  let gPopSetup :=
    (((gPop0.createEffect (.layered (.objects #[fragId]) (.ptModify 1 1) (.whileInZone anthId .battlefield))
        (cause := some testCause)).createEffect
      (.replacement { id := ridA, source := some leyAId, controller := some p0, affectedPlayer := p2,
                      kind := .exileInsteadOfGraveyard (some fragId) false })
      (cause := some testCause)).createEffect
      (.replacement { id := ridB, source := some leyBId, controller := some p0, affectedPlayer := p2,
                      kind := .exileInsteadOfGraveyard (some fragId) false })
      (cause := some testCause)).change
        (.pending (.mayCastExiledElseDamage p1 leyAId 4 none))
  let p0LifeBefore := (gPopSetup.player p0).life
  let gPausedSba := mustApply gPopSetup p1 .concede
  let gAfterSba :=
    match gPausedSba.pending with
    | .chooseReplacement q cs => mustApply gPausedSba q (.chooseReplacement cs[0]!)
    | _ => gPausedSba
  let popOuterOnceOk :=
    (match gPausedSba.pending with | .chooseReplacement q _ => q == p2 | _ => false) &&
    !gPausedSba.outerPendingReplacements.isEmpty &&
    (gPausedSba.player p0).life == p0LifeBefore &&
    gAfterSba.pending == .none &&
    gAfterSba.outerPendingReplacements.isEmpty &&
    (gAfterSba.player p0).life == p0LifeBefore - 4

  -- 3b. `.mayMoveAllCounters` stale `toId` after `removeAllCountersFrom` triggers CR 800.4c exile of `toId`,
  --     and `surveilMoveLoop` stale-ID safety:
  let gMv0 := addPermanent (insertObject gBase bear p0 (.hand p0)) bear p0 p0
  let srcBearId := (gMv0.battlefield.filter (·.name == bear.name))[0]!.id
  let handBearId := (gMv0.player p0).hand.back!
  let (gMvPut, dstBearId) := gMv0.putOntoBattlefield handBearId p1 (cause := some testCause)
  let gMvCnt := gMvPut.recordPutCounters srcBearId .plusOnePlusOne 2 (byPlayer := some p0) (cause := some testCause)
  let gMvCtrl :=
    gMvCnt.createEffect
      (.layered (.objects #[dstBearId]) (.control p0) (.whileSourceHasCounter srcBearId .plusOnePlusOne))
      (cause := some testCause)
  let gMvP1Left := mustApply gMvCtrl p1 .concede
  let gMvAsk := gMvP1Left.change (.pending (.fraChoice p0 (.mayMoveAllCounters srcBearId dstBearId)))
  let gMvAccepted := mustApply gMvAsk p0 .accept
  let gSurveilStale := gBase.surveilMoveLoop p0 #[⟨999999⟩] none
  let staleIdSafetyOk :=
    (gMvP1Left.object! dstBearId).isOnBattlefield &&
    gMvAccepted.pending == .none &&
    (gMvAccepted.object! srcBearId).status.plusOnePlusOne == 0 &&
    (gMvAccepted.findObject? dstBearId).isNone &&
    (gMvAccepted.object! (gMvAccepted.followMoved dstBearId)).zone == .exile &&
    gSurveilStale.events.size == gBase.events.size

  -- 3c. `.tricksterLibrary` target departure runs `.conniveTricksterTarget`,
  --     `.surveil` departure runs `declineMayThenCore` + `finishLibraryLookCore`,
  --     `finishDiscardTwoDraws` ignores departed opponents, and `Library.draw` no-ops on departed player:
  let gTr0 := addPermanent (addPermanent gBase bear p0 p0) bear p1 p1
  let conniveBearId := (gTr0.battlefield.filter (·.controller == some p0))[0]!.id
  let targetBearId := (gTr0.battlefield.filter (·.controller == some p1))[0]!.id
  let p0HandBeforeTr := (gTr0.player p0).hand.size
  let gTrAsk := gTr0.change (.pending (.fraChoice p1 (.tricksterLibrary p0 targetBearId (some conniveBearId) none)))
  let gTrLeft := mustApply gTrAsk p1 .concede
  -- `p0` drew a card into hand and is now prompted to discard for connive!
  let tricksterConniveTailOk :=
    (gTrLeft.player p1).leftTheGame &&
    (gTrLeft.player p0).hand.size == p0HandBeforeTr + 1 &&
    (match gTrLeft.pending with | .chooseDiscardCard q _ => q == p0 | _ => false)

  let p0HandBeforeSurv := (gBase.player p0).hand.size
  let gSurvAsk :=
    ((gBase.change (.pushContinuationFrame {})).changes #[
      .mayThenDrop 1,
      .surveilReturnMvAtMost (some 3),
      .surveilReturnNoncreatureNonland true,
      .continuation (.pendingDrawAfterScry (some (p0, 1))),
      .pending (.surveil p1 1 1)
    ])
  let gSurvLeft := mustApply gSurvAsk p1 .concede
  let surveilLeaveOk :=
    gSurvLeft.pending == .none &&
    gSurvLeft.mayThenDrop == 0 &&
    gSurvLeft.surveilReturnMvAtMost.isNone &&
    !gSurvLeft.surveilReturnNoncreatureNonland &&
    (gSurvLeft.player p0).hand.size == p0HandBeforeSurv + 1

  let gDiscBase := mustApply (insertObject (insertObject gBase bear p2 (.hand p2)) hero p2 (.hand p2)) p1 .concede
  let p2Nonlands := ((gDiscBase.player p2).hand.filter (fun id => !(gDiscBase.object! id).printed.types.contains .land)).extract 0 2
  let startDiscIdx := gDiscBase.events.size
  let gDiscMoved := gDiscBase.withBatch none fun g =>
    g.discardMultiHandIdsLoop #[(p2, p2Nonlands[0]!), (p2, p2Nonlands[1]!)]
  let p0HandBeforeFinish := (gDiscMoved.player p0).hand.size
  let gDiscFinished := gDiscMoved.finishDiscardTwoDraws p0 0 #[p1, p2] startDiscIdx
  let gDeadDraw := gDiscFinished.draw p1 2
  let deadDrawAndShortOk :=
    (gDiscFinished.player p0).hand.size == p0HandBeforeFinish &&
    gDeadDraw.events.size == gDiscFinished.events.size

  mustHold26i1 "3a.popOuterOnceOk" popOuterOnceOk &&
  mustHold26i1 "3b.staleIdSafetyOk" staleIdSafetyOk &&
  mustHold26i1 "3c.tricksterConniveTailOk" tricksterConniveTailOk &&
  mustHold26i1 "3c.surveilLeaveOk" surveilLeaveOk &&
  mustHold26i1 "3c.deadDrawAndShortOk" deadDrawAndShortOk &&
  mustHold26i1 "3.replay"
    (replayOk26i1 #[gPausedSba, gAfterSba, gMvAccepted, gTrLeft, gSurvLeft, gDiscFinished])

end Phase26Item1EventAlignment

/-!
## Phase 26 Item 2 — Modal `allowsZeroTargets` & Layer-3 `announceMode`, CR 118.9a,d / 118.14 Sneak / `anyMana` / *The Ur-Sphinx* Ruling 942, multi-mode / `eachOpponent` targeting, and `Agent` mana checks
-/
section Phase26Item2EventAlignment

def mustHold26i2 (label : String) (ok : Bool) : Bool :=
  if ok then true else panic! s!"Phase 26 item 2 guard failed: {label}"

def replayOk26i2 (gs : Array Game) : Bool :=
  gs.all (fun g => Game.replayEvents g.events == g && allRulesEventsClassified g)

-- 1. CR 115.1c / 612 / 613.1c / 700.2a–b:
--    Modal `allowsZeroTargets` choosability (`spellModeIsChoosable`, `effectHasEnoughTargets`) and
--    Layer-3 `TextChange` evaluation at `announceMode` `.spell` and resolution.
#guard
  let p0 : PlayerId := ⟨0⟩
  let p1 : PlayerId := ⟨1⟩
  let zeroMode : Effect := {
    targeting := .of .creature
    body := Instruction.destroy (.target 0)
    phrase := "Destroy up to one target creature"
    allowsZeroTargets := true
  }
  let reqElfMode : Effect := {
    targeting := .of (.ofDomain (.object .battlefield (ObjectPred.andAll #[.hasSubtype (.literal .elf), .hasType .creature])))
    body := Instruction.putPlusOne (.target 0) 1
    phrase := "Put a +1/+1 counter on target Elf"
  }
  let modalZeroDef : CardDef := {
    name := "P26i2 Modal Zero"
    manaCost := ManaCost.empty
    types := #[.instant]
    spellModes := #[zeroMode, reqElfMode]
  }
  let gEmpty := insertObject afterDraw modalZeroDef p0 (.hand p0)
  let zeroSpellId := (gEmpty.player p0).hand.back!
  -- With 0 creatures on the battlefield, mode 0 (`allowsZeroTargets := true`) is choosable, mode 1 is not:
  let gCast0 := mustApply gEmpty p0 (.cast zeroSpellId)
  let zeroChoosableOk :=
    gEmpty.effectHasEnoughTargets p0 zeroMode &&
    !gEmpty.effectHasEnoughTargets p0 reqElfMode &&
    gCast0.pending == .chooseMode p0 &&
    !(gCast0.apply p0 (.chooseMode 1)).isOk
  let gMode0 := mustApply gCast0 p0 (.chooseMode 0)
  let gDecl0 := mustApply gMode0 p0 .decline
  let gRes0 := mustApply (mustApply gDecl0 p0 .pass) p1 .pass
  -- Layer 3 text change (`Elf` -> `Bear`) on the proposed modal spell makes mode 1 choosable against a Bear:
  let gWithBear := insertObject (addPermanent afterDraw bear p1 p1) modalZeroDef p0 (.hand p0)
  let bearId := (gWithBear.battlefield.filter (·.name == bear.name))[0]!.id
  let bearSpellId := (gWithBear.player p0).hand.back!
  let gCastL3 := mustApply gWithBear p0 (.cast bearSpellId)
  let stackSpellId := gCastL3.proposedSpell.get!.spellId
  let gTextChanged :=
    gCastL3.createEffect
      (.layered (.objects #[stackSpellId]) (.text (.replaceCreatureType .elf .bear)) .indefinite)
      (cause := some testCause)
  let gMode1 := mustApply gTextChanged p0 (.chooseMode 1)
  let gTgt1 := mustApply gMode1 p0 (.target (.permanent bearId))
  let gRes1 := mustApply (mustApply gTgt1 p0 .pass) p1 .pass
  let layer3ModalOk :=
    !(gCastL3.apply p0 (.chooseMode 1)).isOk &&
    (gRes1.object! bearId).status.plusOnePlusOne == 1 &&
    gRes0.stack.isEmpty && gRes1.stack.isEmpty
  mustHold26i2 "1.zeroChoosableOk" zeroChoosableOk &&
  mustHold26i2 "1.layer3ModalOk" layer3ModalOk &&
  mustHold26i2 "1.replay" (replayOk26i2 #[gRes0, gRes1])

-- 2. CR 107.3 / 107.4e / 109.5 / 118.8 / 118.9 / 118.9a,d / 118.14 / 400.7h / 608.2g / 701.17c; Ruling 942:
--    Sneak + permission / Flashback rejection, `ManaCost.asAnyMana` (`.x` + `.twobrid`), and *The Ur-Sphinx*.
#guard
  let p0 : PlayerId := ⟨0⟩
  let p1 : PlayerId := ⟨1⟩
  -- 2a. `ManaCost.asAnyMana` preserves `.x` and converts `.twobrid` to `{1}`:
  let xTwobridCost : ManaCost := ⟨#[.x, .twobrid .white, .colored .blue]⟩
  let twobridCard : CardDef := {
    name := "P26i2 X Twobrid"
    manaCost := xTwobridCost
    types := #[.instant]
    spellEffect := some { body := Instruction.drawFixed 1, phrase := "Draw a card" }
  }
  let gAny0 := insertObject afterDraw twobridCard p0 .exile
  let exTwobridId := gAny0.objects.back!.id
  let anyPerm : PlayPermission := { player := p0, anyMana := true }
  let computedAnyCost :=
    gAny0.playManaCost { (gAny0.object! exTwobridId) with controller := some p0 } twobridCard
      (origPerm := some anyPerm)
  let nullSummonerDef : CardDef := { bear with name := "P26i2 Null Summoner", staticAbilities := #[.castExiledWithSevenInGraveyard] }
  let gNullBase := (List.range 7).foldl (fun g _ => insertObject g bear p0 (.graveyard p0)) gAny0
  let gNull0 := addPermanent gNullBase nullSummonerDef p0 p0
  let summonerId := (gNull0.battlefield.filter (·.name == nullSummonerDef.name))[0]!.id
  let nullExiledObj : GameObject :=
    { (gNull0.object! exTwobridId) with controller := some p0, exiledBy := some summonerId }
  let computedNullCost := gNull0.playManaCost nullExiledObj twobridCard
  let asAnyManaOk :=
    xTwobridCost.asAnyMana == ⟨#[.x, .generic 2]⟩ &&
    computedAnyCost == ⟨#[.x, .generic 2]⟩ &&
    computedNullCost == ⟨#[.x, .generic 2]⟩

  -- 2b. CR 118.9a: `.castWithSneak` cannot combine with `origPerm` (`withoutManaCost`) or `Flashback`:
  let sneakFlashDef : CardDef := {
    name := "P26i2 Sneak Creature"
    manaCost := ManaCost.ofGeneric 3
    types := #[.creature]
    subtypes := #["Ninja"]
    power := some 2
    toughness := some 2
    keywords := #[.flashback CostSpec.empty, .sneak CostSpec.empty]
  }
  let gSnkSetup : Game :=
    let g := addPermanent afterDraw { bear with keywords := #[Keyword.haste] } p0 p0
    let atkId := (g.battlefield.filter (·.name == bear.name))[0]!.id
    let g := mustApply (mustApply (g.beginStep .beginningOfCombat) p0 .pass) p1 .pass
    let g := mustApply g p0 (.declareAttackers #[atkId] none #[] #[])
    let g := mustApply (mustApply g p0 .pass) p1 .pass
    mustApply g p1 (.declareBlockers #[])
  let atkBearId := (gSnkSetup.battlefield.filter (·.name == bear.name))[0]!.id
  let gSnkEx := insertObject gSnkSetup sneakFlashDef p0 .exile
  let exSnkId := gSnkEx.objects.back!.id
  let gSnkPerm :=
    gSnkEx.createEffect
      (.permission (some p0) (.playFromExile exSnkId { player := p0, withoutManaCost := true }) .untilEndOfTurn)
      (cause := some testCause)
  let gSnkGy := insertObject gSnkSetup sneakFlashDef p0 (.graveyard p0)
  let gySnkId := (gSnkGy.player p0).graveyard.back!
  let gSnkHand := insertObject gSnkSetup sneakFlashDef p0 (.hand p0)
  let handSnkId := (gSnkHand.player p0).hand.back!
  let gSnkLegal := mustApply (mustApply gSnkHand p0 (.castWithSneak handSnkId atkBearId)) p0 .pay
  let sneakAltExclusionOk :=
    !(gSnkPerm.apply p0 (.castWithSneak exSnkId atkBearId)).isOk &&
    !(gSnkGy.apply p0 (.castWithSneak gySnkId atkBearId)).isOk &&
    gSnkLegal.stack.size == 1

  -- 2c. *The Ur-Sphinx* Ruling 942: simultaneous mill, `controller` casts up to one milled card per player
  --     (`withoutPaying := true`, sorcery timing ignored, `X = 0`) while the trigger is still on the stack,
  --     and no residual graveyard cast permission persists once the trigger finishes resolving:
  let urSphinxDef : CardDef :=
    fromOracleKeeping [
      "The Ur-Sphinx",
      "{6}{W}{U}{B}",
      "Legendary Creature — Sphinx Avatar",
      "10/10",
      "Flying",
      "Whenever one or more Sphinxes you control attack, each player mills that many cards. For each player, you may cast a card that player milled this way without paying its mana cost."
    ]
  let sorcGain3Def : CardDef := {
    name := "P26i2 Milled Sorcery"
    manaCost := ManaCost.ofGeneric 4
    types := #[.sorcery]
    spellEffect := some { body := Instruction.gainLifeFixed 3, phrase := "You gain 3 life" }
  }
  let sorcXDrawDef : CardDef := {
    name := "P26i2 Milled X Sorcery"
    manaCost := ⟨#[.x, .colored .blue]⟩
    types := #[.sorcery]
    spellEffect := some { body := Instruction.gainLifeFixed 2, phrase := "You gain 2 life" }
  }
  let gUr0 : Game :=
    let g := addPermanent afterDraw { urSphinxDef with keywords := #[Keyword.flying, Keyword.haste] } p0 p0
    let g := insertObject g sorcGain3Def p0 (.library p0)
    let g := insertObject g sorcXDrawDef p1 (.library p1)
    mustApply (mustApply (g.beginStep .beginningOfCombat) p0 .pass) p1 .pass
  let sphinxId := (gUr0.battlefield.filter (·.name == "The Ur-Sphinx"))[0]!.id
  let gUrAtk := mustApply gUr0 p0 (.declareAttackers #[sphinxId] none #[] #[])
  -- Pass priority so *The Ur-Sphinx*'s attack trigger begins resolving:
  let gUrTrigRes := mustApply (mustApply gUrAtk p0 .pass) p1 .pass
  -- Trigger is STILL on the stack while `p0` is prompted to cast from `p0`'s milled bucket:
  let bucket0Id :=
    match gUrTrigRes.pending with
    | .fraChoice q (.mayCastCards ids true false) => if q == p0 && ids.size == 1 then ids[0]! else ⟨0⟩
    | _ => ⟨0⟩
  let triggerOnStackDuringBucket0 :=
    bucket0Id != ⟨0⟩ && !gUrTrigRes.stack.isEmpty && gUrTrigRes.resolvingAbility.isSome
  -- `p0` casts `sorcGain3Def` (`withoutPaying := true`, sorcery during declareAttackers!), which then advances to `p1`'s bucket:
  let gAfterBucket0 := mustApply gUrTrigRes p0 (.cast bucket0Id)
  let bucket1Id :=
    match gAfterBucket0.pending with
    | .fraChoice q (.mayCastCards ids true false) => if q == p0 && ids.size == 1 then ids[0]! else ⟨0⟩
    | _ => ⟨0⟩
  let triggerStillOnStackDuringBucket1 :=
    bucket1Id != ⟨0⟩ && gAfterBucket0.stack.size == 2 && gAfterBucket0.resolvingAbility.isSome
  -- `p0` declines `p1`'s bucket (`sorcXDrawDef` stays in `p1`'s graveyard); trigger finishes resolving, leaving only `sorcGain3Def` on the stack, and neither `p0` nor `p1` can cast `sorcXDrawDef` from graveyard afterwards:
  let gAfterBucket1 := mustApply gAfterBucket0 p0 .decline
  let urSphinxOk :=
    triggerOnStackDuringBucket0 &&
    triggerStillOnStackDuringBucket1 &&
    gAfterBucket1.pending == .none &&
    gAfterBucket1.stack.size == 1 &&
    (gAfterBucket1.object! gAfterBucket1.stack[0]!.objectId).name == sorcGain3Def.name &&
    !(gAfterBucket1.apply p0 (.cast bucket1Id)).isOk &&
    !(gAfterBucket1.apply p1 (.cast bucket1Id)).isOk

  mustHold26i2 "2a.asAnyManaOk" asAnyManaOk &&
  mustHold26i2 "2b.sneakAltExclusionOk" sneakAltExclusionOk &&
  mustHold26i2 "2c.urSphinxOk" urSphinxOk &&
  mustHold26i2 "2.replay" (replayOk26i2 #[gSnkLegal, gUrTrigRes, gAfterBucket0, gAfterBucket1])

-- 3. CR 115.1c / 601.2c / 602.2b / 608.2b / 700.2d:
--    Multi-mode variable target structure (*Atlantis Attacks* Teamwork) and `controller := .eachOpponent`
--    per-opponent expansion (*Bilbo's Burglaring* with CR 608.2b per-slot controller check, plus modal activated ability).
#guard
  let p0 : PlayerId := ⟨0⟩
  let p1 : PlayerId := ⟨1⟩
  let p2 : PlayerId := ⟨2⟩
  -- 3a. *Atlantis Attacks* cast with Teamwork chooses both modes (1 player slot + 1-or-2 nonland slots):
  let atlantisDef : CardDef :=
    fromOracle [
      "Atlantis Attacks",
      "{5}{U}{U}",
      "Sorcery",
      "Teamwork 4 (As an additional cost to cast this spell, you may tap any number of creatures you control with total power 4 or more.)",
      "Choose one. If this spell was cast using teamwork, choose both instead.",
      "• Target player creates a 6/5 blue Leviathan creature token with hexproof.",
      "• Return one or two target nonland permanents to their owners' hands."
    ]
  let bigHelper : CardDef := creature "P26i2 Helper 4/4" ManaCost.empty #["Merfolk"] 4 4
  let artDef1 : CardDef := { name := "P26i2 Relic One", types := #[.artifact] }
  let artDef2 : CardDef := { name := "P26i2 Relic Two", types := #[.artifact] }
  let gAtl0 : Game :=
    let g := addPermanent (addPermanent (addPermanent afterDraw bigHelper p0 p0) artDef1 p1 p1) artDef2 p1 p1
    insertObject g { atlantisDef with manaCost := ManaCost.empty } p0 (.hand p0)
  let helperId := (gAtl0.battlefield.filter (·.name == bigHelper.name))[0]!.id
  let relic1Id := (gAtl0.battlefield.filter (·.name == artDef1.name))[0]!.id
  let relic2Id := (gAtl0.battlefield.filter (·.name == artDef2.name))[0]!.id
  let atlId := (gAtl0.player p0).hand.back!
  let gAtlCast := mustApply gAtl0 p0 (.cast atlId)
  let gAtlMode := mustApply gAtlCast p0 (.chooseMode 0)
  let gAtlAnnTeam := mustApply gAtlMode p0 (.announceTeamwork true)
  let gAtlTeam := mustApply gAtlAnnTeam p0 (.choosePermanents #[helperId])
  -- Mode 0 takes `Target.player p0`; Mode 1 ("one or two target nonland permanents") accepts either
  -- 1 target via `.target` (auto-skipping optional slot 2) or 2 targets simultaneously via `.targets`:
  let gAtlT0 := mustApply gAtlTeam p0 (.target (.player p0))
  let gAtlT1 := mustApply gAtlT0 p0 (.target (.permanent relic1Id))
  let gAtlRes1 := mustApply (mustApply gAtlT1 p0 .pass) p1 .pass
  let gAtlBoth := mustApply gAtlT0 p0 (.targets #[.permanent relic1Id, .permanent relic2Id])
  let gAtlRes2 := mustApply (mustApply gAtlBoth p0 .pass) p1 .pass
  let atlantisTeamworkOk :=
    gAtlRes1.battlefield.any (fun o => o.controller == some p0 && o.name == "Leviathan") &&
    !(gAtlRes1.battlefield.any (·.id == relic1Id)) &&
    gAtlRes1.battlefield.any (·.id == relic2Id) &&
    (gAtlRes1.player p1).hand.any (fun id => (gAtlRes1.object! id).name == artDef1.name) &&
    gAtlRes2.battlefield.any (fun o => o.controller == some p0 && o.name == "Leviathan") &&
    !(gAtlRes2.battlefield.any (·.id == relic1Id)) &&
    !(gAtlRes2.battlefield.any (·.id == relic2Id))

  -- 3b. *Bilbo's Burglaring* (`controller := .eachOpponent`, `allowsZeroTargets := true`) in 3-player game:
  --     `p0` targets `p1`'s artifact for slot 0 and `p2`'s artifact for slot 1; if `p1`'s artifact changes
  --     control to `p2` before resolution, slot 0 becomes illegal under CR 608.2b while slot 1 still resolves!
  let bilboDef : CardDef :=
    fromOracle [
      "Bilbo's Burglaring",
      "{4}{U}{U}",
      "Sorcery",
      "For each opponent, gain control of up to one target artifact that player controls."
    ]
  let gBilbo0 : Game :=
    let g := (mkThreePlayer26i1 2623).beginStep .precombatMain
    let g := addPermanent (addPermanent g artDef1 p1 p1) artDef2 p2 p2
    insertObject g { bilboDef with manaCost := ManaCost.empty } p0 (.hand p0)
  let bArt1Id := (gBilbo0.battlefield.filter (·.name == artDef1.name))[0]!.id
  let bArt2Id := (gBilbo0.battlefield.filter (·.name == artDef2.name))[0]!.id
  let bilboSpellId := (gBilbo0.player p0).hand.back!
  let gBCast := mustApply gBilbo0 p0 (.cast bilboSpellId)
  -- Slot 0 rejects `bArt2Id` (controlled by `p2`, not `p1`!):
  let slot0RejectsWrongOpp := !(gBCast.apply p0 (.target (.permanent bArt2Id))).isOk
  let gBT0 := mustApply gBCast p0 (.target (.permanent bArt1Id))
  let gBT1 := mustApply gBT0 p0 (.target (.permanent bArt2Id))
  -- Before resolution, `p2` gains control of `bArt1Id` (so `bArt1Id` is still controlled by an opponent,
  -- yet NO LONGER controlled by slot 0's opponent `p1`!):
  let gBShifted :=
    gBT1.createEffect (.layered (.objects #[bArt1Id]) (.control p2) .untilEndOfTurn) (cause := some testCause)
  let gBRes := mustApply (mustApply (mustApply gBShifted p0 .pass) p1 .pass) p2 .pass
  let bilboPerSlotOk :=
    slot0RejectsWrongOpp &&
    gBRes.controlledBy (gBRes.object! bArt1Id) p2 &&
    gBRes.controlledBy (gBRes.object! bArt2Id) p0

  -- 3c. Modal activated ability with `controller := .eachOpponent` expands per-opponent slots at `announceMode` and resolution:
  let modalEachOppActivator : CardDef := {
    name := "P26i2 Modal EachOpp Rod"
    types := #[.artifact]
    activatedAbilities := #[ActivatedAbility.mkModal CostSpec.empty #[
      { targeting := .of (.forEachOpponentControlled (.hasType .creature) (.exact 1))
        body := Instruction.tapAndStun .allTargets
        phrase := "For each opponent, tap target creature that player controls and put a stun counter on it" },
      { body := Instruction.gainLifeFixed 1, phrase := "You gain 1 life" }
    ]]
  }
  let gAct0 : Game :=
    let g := mkThreePlayer26i1 2624
    addPermanent (addPermanent (addPermanent g modalEachOppActivator p0 p0) bear p1 p1) hero p2 p2
  let rodId := (gAct0.battlefield.filter (·.name == modalEachOppActivator.name))[0]!.id
  let p1BearId := (gAct0.battlefield.filter (·.name == bear.name))[0]!.id
  let p2HeroId := (gAct0.battlefield.filter (·.name == hero.name))[0]!.id
  let gAct1 := mustApply gAct0 p0 (.activate rodId 0)
  let gActMode0 := mustApply gAct1 p0 (.chooseMode 0)
  let gActT0 := mustApply gActMode0 p0 (.target (.permanent p1BearId))
  let gActT1 := mustApply gActT0 p0 (.target (.permanent p2HeroId))
  let gActRes := mustApply (mustApply (mustApply gActT1 p0 .pass) p1 .pass) p2 .pass
  let modalActivatedEachOppOk :=
    (gActRes.object! p1BearId).status.tapped &&
    (gActRes.object! p1BearId).status.stun == 1 &&
    (gActRes.object! p2HeroId).status.tapped &&
    (gActRes.object! p2HeroId).status.stun == 1

  mustHold26i2 "3a.atlantisTeamworkOk" atlantisTeamworkOk &&
  mustHold26i2 "3b.bilboPerSlotOk" bilboPerSlotOk &&
  mustHold26i2 "3c.modalActivatedEachOppOk" modalActivatedEachOppOk &&
  mustHold26i2 "3.replay" (replayOk26i2 #[gAtlRes1, gAtlRes2, gBRes, gActRes])

-- 4. `Agent.lean` CR 106.6 / 116.2b / 118.9d mana checks:
--    `chooseActivate` rejects creature-only mana for synthetic `.frc .turnFaceUp`,
--    `chooseCast` checks taxes under `withoutManaCost`, and `payGenericOrTapFirstSource` declines
--    when only restricted or insufficient mana is available.
#guard
  let p0 : PlayerId := ⟨0⟩
  let p1 : PlayerId := ⟨1⟩
  let emptyHand (g : Game) (pl : PlayerId) : Game :=
    (g.player pl).hand.foldl (fun acc hid =>
      (acc.move hid (.graveyard pl) none (cause := some testCause)).1) g
  -- 4a. Face-down Morph permanent with `{1}` morph cost cannot be turned face up using `.creatureSource` mana,
  --     whereas unrestricted `{C}` mana DOES let `Agent.choose` turn it face up:
  let morphDef : CardDef := {
    name := "P26i2 Morph Spy"
    manaCost := ManaCost.ofGeneric 3
    types := #[.creature]
    subtypes := #["Elf"]
    power := some 2
    toughness := some 2
    keywords := #[.morph (CostSpec.ofGeneric 1)]
  }
  let gMorphBase : Game :=
    let g := emptyHand (addPermanent afterDraw morphDef p0 p0) p0
    let mid := (g.battlefield.filter (·.name == morphDef.name))[0]!.id
    setFaceDown g mid true
  let morphPermId := (gMorphBase.battlefield.filter (·.status.faceDown))[0]!.id
  let gMorphRestricted :=
    gMorphBase.record (GameEvent.manaAdded gMorphBase.turnNumber p0
      #[{ mana := .colorless, restriction := some .creatureSource }] (cause := some testCause))
  let gMorphUnrestricted := gMorphBase.addMana p0 .colorless 1
  let agentSkipsTurnFaceUpWithCreatureMana :=
    (match Agent.choose gMorphRestricted p0 with | some .pass => true | _ => false) &&
    (match Agent.choose gMorphUnrestricted p0 with
     | some (.activate id 0) => id == morphPermId
     | _ => false)

  -- 4b. Exiled noncreature draw spell with `withoutManaCost := true`:
  --     castable at 0 mana when untaxed, skipped by `chooseCast` at 0 mana under opponent's `{1}` tax:
  let taxPermDef : CardDef := {
    name := "P26i2 Tax Statue"
    types := #[.artifact]
    staticAbilities := #[.opponentsNoncreatureSpellsCostMore]
  }
  let freeSorcDef : CardDef := {
    name := "P26i2 Taxed Free Sorcery"
    manaCost := ManaCost.ofGeneric 2
    types := #[.sorcery]
    spellEffect := some { body := Instruction.drawFixed 1, phrase := "Draw a card" }
  }
  let gUntaxedFree : Game :=
    let g := insertObject (emptyHand afterDraw p0) freeSorcDef p0 .exile
    let exId := g.objects.back!.id
    g.createEffect
      (.permission (some p0) (.playFromExile exId { player := p0, withoutManaCost := true }) .untilEndOfTurn)
      (cause := some testCause)
  let untaxedExId := gUntaxedFree.objects.back!.id
  let gTax0 := addPermanent gUntaxedFree taxPermDef p1 p1
  let agentSkipsUnpayableTaxedFreeCast :=
    (match Agent.choose gUntaxedFree p0 with
     | some (.cast id) => id == untaxedExId
     | _ => false) &&
    (match Agent.choose gTax0 p0 with | some .pass => true | _ => false)

  -- 4c. `payGenericOrTapFirstSource` declines without tapping a restricted mana source or single land for `{2}`:
  let instOnlyManaLand : CardDef := {
    name := "P26i2 Spell Haven"
    types := #[.land]
    activatedAbilities := #[ActivatedAbility.manaAbility (.oneOf .anyColor (.const 1)) (restriction := some .instantOrSorcery)]
  }
  let gRestrictedLand := addPermanent afterDraw instOnlyManaLand p0 p0
  let gOneForest := addPermanent afterDraw forest p0 p0
  let payGenericCheckOk :=
    (match Agent.payGenericOrTapFirstSource gRestrictedLand p0 1 with | some .decline => true | _ => false) &&
    (match Agent.payGenericOrTapFirstSource gOneForest p0 2 with | some .decline => true | _ => false) &&
    (match Agent.payGenericOrTapFirstSource gOneForest p0 1 with
     | some (.tapForMana _ _) => true
     | _ => false)

  mustHold26i2 "4a.turnFaceUpManaOk" agentSkipsTurnFaceUpWithCreatureMana &&
  mustHold26i2 "4b.taxedFreeCastOk" agentSkipsUnpayableTaxedFreeCast &&
  mustHold26i2 "4c.payGenericCheckOk" payGenericCheckOk

end Phase26Item2EventAlignment

section Phase26Item3EventAlignment

private def mustHold26i3 (label : String) (b : Bool) : Bool :=
  if b then true else panic! s!"Phase26Item3 check failed: {label}"

private def replayOk26i3 (gs : Array Game) : Bool :=
  gs.all fun g =>
    Game.replayEvents g.events == g && allRulesEventsClassified g

-- 1. Impending ETB `.time` counter replacements (CR 122.6 / 614.1c / 614.12 / 616.1g / 702.176a)
--    and `GameEvent.enteredBattlefield` matching token `ZoneEvent.created` and rejecting
--    battlefield-to-battlefield `.moved` (CR 111.6 / 614.1c):
#guard
  let p0 : PlayerId := ⟨0⟩
  let impDef : CardDef := {
    bear with
    name := "P26i3 Impending Overlord"
    types := #[.enchantment, .creature]
    keywords := #[.impending 2 CostSpec.empty]
  }
  let samsonDef : CardDef := {
    bear with
    name := "P26i3 Doc Samson"
    staticAbilities := #[.extraCounterOnPermanents]
  }
  -- 1a. Competing `.extraCounterOnPermanents` (+1) and `.modifyCountersPut` (×2) on Impending 2:
  --     pauses on `Pending.chooseReplacement` and enters with `(2 + 1) * 2 = 6` `.time` counters
  --     (single `entersWith`, zero duplicate post-entry `countersPut`, not a creature):
  let g0 := addPermanent (insertObject (emptyHand afterDraw p0) impDef p0 (.hand p0)) samsonDef p0 p0
  let samsonId := (g0.permanentsOf p0).find? (·.name == "P26i3 Doc Samson") |>.get!.id
  let dblSpec : ReplacementSpec := {
    id := { kind := .multiplyCountersPut, object := some samsonId, counterKind := some .time }
    source := some samsonId, controller := some p0, affectedPlayer := p0
    kind := .modifyCountersPut none (some .time) 0 2
  }
  let g1 := g0.createEffect (.replacement dblSpec) (cause := some testCause)
  let impHandId := (g1.player p0).hand[0]!
  let gCast := mustApply (mustApply g1 p0 (.cast impHandId)) p0 (.announceKicker true)
  let gPaused := passBoth gCast
  let pausedOk :=
    match gPaused.pending with
    | .chooseReplacement chooser choices => chooser == p0 && choices.size == 2
    | _ => false
  -- Choose `+1` first so `(2 + 1) * 2 = 6`:
  let addChoice :=
    match gPaused.pending with
    | .chooseReplacement _ choices =>
      choices.find? (fun rid => rid.kind == .extraCounterOnPermanents) |>.getD choices[0]!
    | _ => default
  let gEntered := mustApply gPaused p0 (.chooseReplacement addChoice)
  let enteredPerm := (gEntered.permanentsOf p0).find? (·.name == "P26i3 Impending Overlord") |>.get!
  let postMoveCountersPut :=
    (gEntered.events.extract gCast.events.size gEntered.events.size).any fun e =>
      match e.change with
      | .rules (.permanent (.counters (.object obj) _ (.put _) _)) => obj.id == some enteredPerm.id
      | _ => false
  let modOk :=
    pausedOk &&
    enteredPerm.status.counterCount .time == 6 &&
    !gEntered.isCreature enteredPerm &&
    gEntered.isEnchantment enteredPerm &&
    !postMoveCountersPut

  -- 1b. Prevention / zeroing (`mult := 0`, e.g. Solemnity or opponent Vorinclex on 1):
  --     `0` placed `.time` counters leaves the permanent a creature immediately (CR 702.176a):
  let gZeroBase := insertObject (emptyHand afterDraw p0) impDef p0 (.hand p0)
  let zeroSpec : ReplacementSpec := {
    id := { kind := .multiplyCountersPut, object := none, counterKind := some .time }
    source := none, controller := some p0, affectedPlayer := p0
    kind := .modifyCountersPut none (some .time) 0 0
  }
  let gZero0 := gZeroBase.createEffect (.replacement zeroSpec) (cause := some testCause)
  let zeroHandId := (gZero0.player p0).hand[0]!
  let gZeroCast := mustApply (mustApply gZero0 p0 (.cast zeroHandId)) p0 (.announceKicker true)
  let gZeroEntered := passBoth gZeroCast
  let zeroPerm := (gZeroEntered.permanentsOf p0).find? (·.name == "P26i3 Impending Overlord") |>.get!
  let zeroOk :=
    zeroPerm.status.counterCount .time == 0 &&
    gZeroEntered.isCreature zeroPerm &&
    !gZeroEntered.activeEffects.any (fun (_, eff) => eff == .notACreature zeroPerm.id)

  -- 1c. `GameEvent.enteredBattlefield` matches token `ZoneEvent.created` on `.battlefield`,
  --     rejects non-battlefield `ZoneEvent.created`, matches `.stack → .battlefield` `.moved`,
  --     and rejects `.battlefield → .battlefield` `.moved`:
  let (gTok, _) := afterDraw.createToken p0 Game.humanSoldierToken (cause := some testCause)
  let tokEv? :=
    (gTok.events.extract afterDraw.events.size gTok.events.size).find? fun e =>
      match e.change with
      | .rules (.zone (.created ..)) => true
      | _ => false
  let nonBfObj : EventObject := { id := some ⟨999⟩, name := "Copy", zone := .stack }
  let nonBfCreatedEv : GameEvent := GameEvent.created 1 p0 nonBfObj testCause
  let bfToBfMovedEv : GameEvent :=
    GameEvent.moved 1 { nonBfObj with zone := .battlefield } .battlefield .battlefield (cause := testCause)
  let stackToBfEv? :=
    (gZeroEntered.events.extract gZeroCast.events.size gZeroEntered.events.size).find? fun e =>
      match e.change with
      | .rules (.zone (.moved _ _ .stack .battlefield _ _ _ _)) => true
      | _ => false
  let etbEventOk :=
    tokEv?.any (·.enteredBattlefield) &&
    !nonBfCreatedEv.enteredBattlefield &&
    !bfToBfMovedEv.enteredBattlefield &&
    stackToBfEv?.any (·.enteredBattlefield)

  mustHold26i3 "1a.impendingModifiedCountersOk" modOk &&
  mustHold26i3 "1b.impendingZeroCountersCreatureOk" zeroOk &&
  mustHold26i3 "1c.enteredBattlefieldPredicateOk" etbEventOk &&
  mustHold26i3 "1.replay" (replayOk26i3 #[gEntered, gZeroEntered, gTok])

-- 2. Pause-safe `TriggerResolution.dividedDamage`, tight `startEventIdx` capture across queued
--    steps, and `.opponentsControl` / `!hasSubtype` recipient re-verification (CR 119.9 /
--    120.3f / 608.2c / 616.1 / 702.15b):
#guard
  let p0 : PlayerId := ⟨0⟩
  let p1 : PlayerId := ⟨1⟩
  let p2 : PlayerId := ⟨2⟩
  let g3 :=
    match Start.start {
      seats := #[{ name := "P0", deck := testRedDeck },
                 { name := "P1", deck := testRedDeck },
                 { name := "P2", deck := testRedDeck }]
      startingPlayer := some 0
      seed := 26 } with
    | .ok g => keepOpeningHands g 16
    | .error e => panic! e
  let divLifelinkDef : CardDef := {
    bear with
    name := "P26i3 Lifelink Titan"
    keywords := #[Keyword.lifelink]
    triggeredAbilities := #[.onEnterDealDividedDamage 3 3]
  }
  let toughDef : CardDef := {
    bear with
    name := "P26i3 Tough Target"
    power := some 1
    toughness := some 8
  }
  let gBase :=
    (addPermanent
      (addPermanent
        (addPermanent g3 divLifelinkDef p0 p0)
        toughDef p1 p1)
      toughDef p2 p2).change (.pushContinuationFrame {})
  let src := (gBase.permanentsOf p0).find? (·.name == "P26i3 Lifelink Titan") |>.get!
  let v1 := (gBase.permanentsOf p1).find? (·.name == "P26i3 Tough Target") |>.get!
  let v2 := (gBase.permanentsOf p2).find? (·.name == "P26i3 Tough Target") |>.get!

  let addTwoDmgReps (g : Game) : Game :=
    let add1 : ReplacementSpec := {
      id := { kind := .addNoncombatDamage, object := some src.id }
      source := some src.id, controller := some p0, affectedPlayer := p0
      kind := .addNoncombatDamage (some src.id) 1 }
    let dbl : ReplacementSpec := {
      id := { kind := .multiplyDamage, object := some v1.id }
      source := some v1.id, controller := some p0, affectedPlayer := p0
      kind := .multiplyDamage (some src.id) 2 }
    (g.createEffect (.replacement add1) (cause := some testCause)).createEffect
      (.replacement dbl) (cause := some testCause)

  let resolveAllRepChoices (g : Game) : Game := Id.run do
    let mut cur := g
    let mut fuel := 16
    while fuel > 0 do
      fuel := fuel - 1
      match cur.pending with
      | .chooseReplacement chooser choices =>
        let pick :=
          choices.find? (fun rid => rid.kind == .addNoncombatDamage) |>.getD choices[0]!
        cur := mustApply cur chooser (.chooseReplacement pick)
      | _ => fuel := 0
    return cur

  let countLifeGainsSince (g : Game) (sIdx : Nat) : Array (PlayerId × Nat) :=
    (g.events.extract sIdx g.events.size).filterMap fun e =>
      match e.change with
      | .rules (.life (.gained q amt)) => some (q, amt)
      | _ => none

  -- 2a. `applyTriggeredAbility` `.dividedDamage` pauses across `Pending.chooseReplacement`
  --     and aggregates CR 702.15b lifelink into a single `LifeEvent.gained` (`(2+1)*2 + (1+1)*2 = 10`),
  --     and checks target 2's legality ONLY after target 1's replacement choice completes:
  let gDiv0 := addTwoDmgReps gBase
  let sDiv := gDiv0.events.size
  let divAb : TriggeredAbility := .onEnterDealDividedDamage 3 3
  let gDivPaused :=
    gDiv0.applyTriggeredAbility p0 divAb (some src.id)
      #[Target.permanent v1.id, Target.permanent v2.id] #[2, 1] none none "P26i3 Lifelink Titan"
  let divPausedOk :=
    (match gDivPaused.pending with | .chooseReplacement .. => true | _ => false) &&
    (gDivPaused.object! v2.id).status.damage == 0
  let gDivDone := resolveAllRepChoices gDivPaused
  let divGains := countLifeGainsSince gDivDone sDiv
  -- Also verify mid-pause hexproof on target 2 causes target 2 to be skipped when resumed:
  let gDivHexMid :=
    gDivPaused.createEffect (.keywordsUntilEot v2.id #[Keyword.hexproof]) (cause := some testCause)
  let gDivHexDone := resolveAllRepChoices gDivHexMid
  let divHexGains := countLifeGainsSince gDivHexDone sDiv
  let divTrigOk :=
    divPausedOk &&
    (gDivDone.object! v1.id).status.damage == 6 &&
    (gDivDone.object! v2.id).status.damage == 4 &&
    divGains == #[(p0, 10)] &&
    (gDivHexDone.object! v1.id).status.damage == 6 &&
    (gDivHexDone.object! v2.id).status.damage == 0 &&
    divHexGains == #[(p0, 6)]

  -- 2b. Tight `startEventIdx` capture when queued behind an earlier paused step from the SAME
  --     lifelink source `src`: Step 1 deals `(1+1)*2 = 4` damage + 4 lifelink, then queued
  --     `dealDamageLoseIndestructibleExileTo` deals `(1+1)*2 = 4` damage + 4 lifelink (NOT 8!):
  let gTight0 := addTwoDmgReps gBase
  let sTight := gTight0.events.size
  let gStep1Paused :=
    gTight0.dealDamageToPlayer p1 1 (source := some src) (cause := some testCause)
  let gStep2Queued :=
    gStep1Paused.dealDamageLoseIndestructibleExileTo v2 1 (gStep1Paused.snapshot src)
  let gTightDone := resolveAllRepChoices gStep2Queued
  let tightGains := countLifeGainsSince gTightDone sTight
  -- Also test `divideSevenDamageLoop` queued behind `gStep1Paused`:
  let gDiv7Queued :=
    gStep1Paused.divideSevenDamageLoop p0 .anyTarget #[(0, Target.player p2)] #[1] (some src.id)
  let gDiv7Done := resolveAllRepChoices gDiv7Queued
  let div7Gains := countLifeGainsSince gDiv7Done sTight
  let tightWindowOk :=
    tightGains == #[(p0, 4), (p0, 4)] &&
    div7Gains == #[(p0, 4), (p0, 4)]

  -- 2c. `.opponentsControl` (`onlyOpponentsOf`) and `dealDamageToEachNonSubtypeAndOpponents`
  --     (`onlyNonSubtype`) re-verify recipient predicates after `Pending.chooseReplacement` pauses:
  let gReverify0 := addTwoDmgReps gBase
  let gOppPaused :=
    gReverify0.applyEffect p0
      { body := Instruction.dealDamageFixed
          (.objects (.inZones .battlefield (.all #[.hasType .creature, .controlledBy .opponent]))) 1 }
      #[] (sourceId := some src.id)
  -- Gain control of `v2` for `p0` while paused after `v1`'s prompt:
  let gOppSteal :=
    gOppPaused.createEffect (.control v2.id p0) (cause := some testCause)
  let gOppDone := resolveAllRepChoices gOppSteal
  let oppReverifyOk :=
    (gOppDone.object! v1.id).status.damage == 4 &&
    (gOppDone.object! v2.id).status.damage == 0

  let sNonSub := gReverify0.events.size
  let gNonSubPaused :=
    gReverify0.dealDamageToEachNonSubtypeAndOpponents p0 1 .dragon (some src.id) (cause := some testCause)
  -- Grant `.dragon` subtype to `v2` while paused on `src`'s prompt:
  let gNonSubGrant :=
    gNonSubPaused.createEffect (.additionalSubtype v2.id .dragon) (cause := some testCause)
  let gNonSubDone := resolveAllRepChoices gNonSubGrant
  let nonSubGains := countLifeGainsSince gNonSubDone sNonSub
  -- `src` (4 dmg), `v1` (4 dmg), `v2` skipped (became Dragon!), `p1` (4 dmg), `p2` (4 dmg) => single 16 life gain!
  let nonSubReverifyOk :=
    (gNonSubDone.object! v1.id).status.damage == 4 &&
    (gNonSubDone.object! v2.id).status.damage == 0 &&
    nonSubGains == #[(p0, 16)]

  mustHold26i3 "2a.dividedDamageLoopOk" divTrigOk &&
  mustHold26i3 "2b.tightStartEventIdxOk" tightWindowOk &&
  mustHold26i3 "2c.recipientReverifyOk" (oppReverifyOk && nonSubReverifyOk) &&
  mustHold26i3 "2.replay"
    (replayOk26i3 #[gDivDone, gDivHexDone, gTightDone, gDiv7Done, gOppDone, gNonSubDone])

-- 3. `.equippedBecomesTapped` (*Hawkeye's Bow*), *Balin, Loremaster*, and *Eye of Jace* LKI
--    (CR 101.3 / 113.7a / 301.5d / 603.3a / 608.2h / 609.3 / 702.15b):
#guard
  let p0 : PlayerId := ⟨0⟩
  let p1 : PlayerId := ⟨1⟩
  -- 3a. *Hawkeye's Bow* controlled by `p0` attached to `p1`'s creature `c1`:
  --     tapping `c1` queues `.equippedBecomesTapped` for `p0` (`eqCtrl`), and when attached to
  --     `p0`'s lifelink creature `c0` that leaves the battlefield before resolution, `c0`'s LKI
  --     still deals the 1 damage to `p1` and grants `p0` 1 lifelink life!
  let bowDef : CardDef :=
    fromOracle [
      "Hawkeye's Bow",
      "{R}",
      "Artifact — Equipment",
      "Equipped creature gets +1/+0 and has reach.",
      "Whenever equipped creature becomes tapped, it deals 1 damage to each opponent.",
      "Equip {1} ({1}: Attach to target creature you control. Equip only as a sorcery.)"
    ]
  let llBearDef : CardDef := { bear with name := "P26i3 Lifelink Archer", keywords := #[Keyword.lifelink] }
  let gBow0 :=
    addPermanent (addPermanent (emptyHand afterDraw p0) bowDef p0 p0) bear p1 p1
  let bowId0 := (gBow0.permanentsOf p0).find? (·.name == "Hawkeye's Bow") |>.get!.id
  let oppCreatureId := (gBow0.permanentsOf p1).find? (·.name == bear.name) |>.get!.id
  let gBowOnOpp :=
    gBow0.attachSourceTo (gBow0.object! bowId0) (gBow0.object! oppCreatureId) (cause := some testCause)
  let gOppTapped :=
    (gBowOnOpp.becomeTapped (gBowOnOpp.object! oppCreatureId) (cause := some testCause)).receivePriority p0
  let bowQueuedForEqCtrl :=
    gOppTapped.stack.any (fun e =>
      e.controller == p0 && (gOppTapped.object! e.objectId).sourceId == some bowId0)
  let gBowOppResolved := gOppTapped.resolveTop
  let bowOnOppOk :=
    bowQueuedForEqCtrl && (gBowOppResolved.player p1).life == 19

  -- Detached / departed triggering lifelink creature LKI:
  let gBowLki0 :=
    addPermanent (addPermanent (emptyHand afterDraw p0) bowDef p0 p0) llBearDef p0 p0
  let bowId1 := (gBowLki0.permanentsOf p0).find? (·.name == "Hawkeye's Bow") |>.get!.id
  let archerId := (gBowLki0.permanentsOf p0).find? (·.name == "P26i3 Lifelink Archer") |>.get!.id
  let gBowAttached :=
    gBowLki0.attachSourceTo (gBowLki0.object! bowId1) (gBowLki0.object! archerId) (cause := some testCause)
  let gBowTriggered :=
    (gBowAttached.becomeTapped (gBowAttached.object! archerId) (cause := some testCause)).receivePriority p0
  -- Destroy `P26i3 Lifelink Archer` BEFORE Hawkeye's Bow trigger resolves:
  let (gArcherGone, _) := gBowTriggered.move archerId (.graveyard p0) none (cause := some testCause)
  let gBowLkiResolved := gArcherGone.resolveTop
  let bowLkiDmgSrcOk :=
    gBowLkiResolved.events.any fun e =>
      match e.change with
      | .rules (.damage (.dealt pkts)) =>
        pkts.any (fun pkt => pkt.source.id == some archerId && pkt.amount == 1)
      | _ => false
  let bowLkiOk :=
    bowLkiDmgSrcOk &&
    (gBowLkiResolved.player p1).life == 19 &&
    (gBowLkiResolved.player p0).life == 21

  -- 3b. *Balin, Loremaster* LKI: `p0` has `.enduringStory`, Balin has lifelink, Balin triggers
  --     and leaves the battlefield BEFORE the trigger resolves -> accepting `.mayDiscardHandBalin`
  --     discards 2 cards, draws 2 cards, deals 2 damage to `p1` from Balin's LKI, and gains 2 life!
  let balinBase : CardDef :=
    fromOracle [
      "Balin, Loremaster",
      "{3}{R}{R}",
      "Legendary Creature — Dwarf Bard",
      "4/4",
      "Storied (If you control three or more artifacts, legendaries, and/or Sagas, you have an enduring story for the rest of the game.)",
      "Whenever Balin or another Dwarf you control enters, you may discard your hand. Draw X cards, where X is the number of cards discarded this way. If you have an enduring story, Balin deals X damage to each opponent."
    ]
  let balinLlDef : CardDef := {
    balinBase with
    keywords := KeywordAbility.add balinBase.keywords Keyword.lifelink
  }
  let gBalin0 :=
    (insertObject (insertObject (emptyHand afterDraw p0) forest p0 (.hand p0)) forest p0 (.hand p0)).record
      (GameEvent.gainedDesignation afterDraw.turnNumber p0 .enduringStory (cause := some testCause))
  let gBalin1 := addPermanent gBalin0 balinLlDef p0 p0
  let balinId := (gBalin1.permanentsOf p0).find? (·.name == "Balin, Loremaster") |>.get!.id
  let (gBalinGone, _) := gBalin1.move balinId (.graveyard p0) none (cause := some testCause)
  let gBalinPrompt :=
    (gBalinGone.change (.pushContinuationFrame
      { resolvingContext := some (some balinId, p0) })).applyTriggeredAbility
      p0 (.onThisOrAnotherSubtypeEntersDiscardHand "Dwarf") (some balinId)
  let gBalinDone := mustApply gBalinPrompt p0 .accept
  let balinOk :=
    (gBalinDone.player p0).hand.size == 2 &&
    (gBalinDone.player p1).life == 18 &&
    (gBalinDone.player p0).life == 22

  -- 3c. *Eye of Jace* LKI: with 7+ cards in `p0`'s graveyard and lifelink on *Eye of Jace*,
  --     both normal sacrifice AND pre-check departure deal 2 LKI damage to `p1` (+2 lifelink)
  --     and gain 2 life (`+4` total for `p0`):
  let eyeBase : CardDef :=
    fromOracleKeeping [
      "Eye of Jace",
      "{1}",
      "Artifact",
      "At the beginning of your upkeep, surveil 1. Then if there are seven or more cards in your graveyard, sacrifice this artifact, it deals 2 damage to each opponent, and you gain 2 life. (To surveil 1, look at the top card of your library. You may put it into your graveyard.)"
    ]
  let eyeLlDef : CardDef := {
    eyeBase with
    keywords := #[Keyword.lifelink]
  }
  let gEyeBase : Game := Id.run do
    let mut g := addPermanent (emptyHand afterDraw p0) eyeLlDef p0 p0
    for _ in [0:7] do
      g := insertObject g forest p0 (.graveyard p0)
    return g
  let eyeId := (gEyeBase.permanentsOf p0).find? (·.name == "Eye of Jace") |>.get!.id
  let withEyeCtx (g : Game) : Game :=
    ((g.change (.pushContinuationFrame
      { resolvingContext := some (some eyeId, p0) })).applyAbilityEffect
      p0 (Game.fraNextToEffect .eyeOfJaceCheck) #[] (some eyeId)).change .popContinuationFrame
  -- Case i: normal sacrifice during `.eyeOfJaceCheck`:
  let gEyeSac := withEyeCtx gEyeBase
  let eyeSacOk :=
    !(gEyeSac.permanentsOf p0).any (·.name == "Eye of Jace") &&
    (gEyeSac.player p1).life == 18 &&
    (gEyeSac.player p0).life == 24
  -- Case ii: *Eye of Jace* removed BEFORE `.eyeOfJaceCheck` runs (CR 101.3 / 608.2h):
  let (gEyeGone, _) := gEyeBase.move eyeId .exile none (cause := some testCause)
  let gEyeDeparted := withEyeCtx gEyeGone
  let eyeDepartedOk :=
    (gEyeDeparted.player p1).life == 18 &&
    (gEyeDeparted.player p0).life == 24

  mustHold26i3 "3a.hawkeyeBowLkiOk" (bowOnOppOk && bowLkiOk) &&
  mustHold26i3 "3b.balinLkiOk" balinOk &&
  mustHold26i3 "3c.eyeOfJaceLkiOk" (eyeSacOk && eyeDepartedOk) &&
  mustHold26i3 "3.replay"
    (replayOk26i3 #[gBowOppResolved, gBowLkiResolved, gBalinDone, gEyeSac, gEyeDeparted])

end Phase26Item3EventAlignment

/-! ### Phase 26 Item 4: `recordRemoveCounters` routing (6 sites), CR 725.2–3 per-creature /
resolution-controller / idempotent monarch triggers, CR 805.3–7 2HG APNAP / shared-step /
combat triggers, layer-resolved battlefield `g.name`, and dead-scaffolding retirement -/
section Phase26Item4EventAlignment

private def mustHold26i4 (label : String) (ok : Bool) : Bool :=
  if ok then true else panic! s!"Phase26Item4EventAlignment failed: {label}"

private def replayOk26i4 (gs : Array Game) : Bool :=
  gs.all (fun g => Game.replayEvents g.events == g && allRulesEventsClassified g)

private def mkThreePlayer26i4 (seed : UInt64 := 2640) : Game :=
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

private def mkTwoHeadedGiant26i4 (seed : UInt64 := 2641) (startingSeat : Nat := 0) : Game :=
  let cfg : StartConfig := {
    seats := #[
      { name := "TeamA1", deck := testRedDeck, teammate := some ⟨1⟩ },
      { name := "TeamA2", deck := testGreenDeck, teammate := some ⟨0⟩ },
      { name := "TeamB1", deck := testRedDeck, teammate := some ⟨3⟩ },
      { name := "TeamB2", deck := testGreenDeck, teammate := some ⟨2⟩ }
    ]
    format := .constructed
    seed
    startingPlayer := some startingSeat
  }
  match Start.start cfg with
  | .ok g => (keepOpeningHands g 40).advanceStep
  | .error e => panic! e

-- 1. CR 118.3 / 120.3c / 122.1 / 606.4 / 611.2a / 800.4c:
--    Remaining 6 counter-removal sites routed through `Leaving.recordRemoveCounters`
--    immediately expire `.whileSourceHasCounter` effects and exile permanents whose
--    resulting controller has left the game.
#guard
  let p0 : PlayerId := ⟨0⟩
  let p1 : PlayerId := ⟨1⟩
  let p2 : PlayerId := ⟨2⟩
  let gBase3 := mkThreePlayer26i4 2642
  let pwDef : CardDef := {
    name := "Test Walker 26i4"
    types := #[.planeswalker]
    loyalty := some 2
  }
  -- Helper: create a permanent owned by `p2`, put onto the battlefield under `p1`'s
  -- control (`defaultController = some p1`, with `n` counters of `kind`), grant `p0`
  -- control of it via `.whileSourceHasCounter pid kind`, then have `p1` concede so
  -- `p0` only controls `pid` while it retains `kind` counters (CR 611.2a / 800.4c).
  let setupCounterControl (card : CardDef) (kind : CounterKind) (n : Nat) : Game × ObjectId :=
    let gIns := insertObject gBase3 card p2 (.hand p2)
    let vCard := (gIns.player p2).hand.back!
    let (gPut, pid) := gIns.putOntoBattlefield vCard p1 (cause := some testCause)
    let g1 :=
      if (gPut.object! pid).status.counterCount kind == n then gPut
      else gPut.recordPutCounters pid kind n (byPlayer := some p0) (cause := some testCause)
    let g2 := g1.createEffect
      (.layered (.objects #[pid]) (.control p0) (.whileSourceHasCounter pid kind))
      (cause := some testCause)
    let g3 := g2.concede p1
    (g3, pid)
  let exitedAndExpired (gBefore gAfter : Game) (pid : ObjectId) (kind : CounterKind) : Bool :=
    let slice := gAfter.events.extract gBefore.events.size gAfter.events.size
    let hasRemoved := slice.any fun e =>
      match e.change with
      | .rules (.permanent (.counters (.object eo) k (.removed m) _)) =>
        eo.id == some pid && k == kind && m > 0
      | _ => false
    let hasExpired := slice.any fun e =>
      match e.change with
      | .rules (.continuousEffect (.expired ..)) => true
      | _ => false
    let exiledBy800_4c := slice.any fun e =>
      match e.change, e.cause? with
      | .rules (.zone (.moved before _ .battlefield .exile ..)), some (.gameRule .playerLeftGame) =>
        before.id == some pid
      | _, _ => false
    hasRemoved && hasExpired && exiledBy800_4c &&
      (gAfter.findObject? pid).isNone &&
      (gAfter.followMovedToZone? pid (· == .exile)).isSome

  -- 1a & 1b. Both planeswalker loyalty-removal arms in `Damage.markDamageOn` (normal
  --          and `rep.shieldRemoved && unpreventable`):
  let (gPwNoSrc0, pwNoSrcId) := setupCounterControl pwDef .loyalty 2
  let gPwNoSrc1 := gPwNoSrc0.markDamageOn (gPwNoSrc0.object! pwNoSrcId) 2 ""
  let pwNoSrcOk := exitedAndExpired gPwNoSrc0 gPwNoSrc1 pwNoSrcId .loyalty

  let (gPwWithSrc0, pwWithSrcId) := setupCounterControl pwDef .loyalty 2
  let gPwWithSrc0' := gPwWithSrc0.recordPutCounters pwWithSrcId .shield 1 (byPlayer := some p0) (cause := some testCause)
  let gPwWithSrc1 := gPwWithSrc0'.markDamageOn (gPwWithSrc0'.object! pwWithSrcId) 2 "" (unpreventable := true)
  let pwWithSrcOk := exitedAndExpired gPwWithSrc0' gPwWithSrc1 pwWithSrcId .loyalty

  -- 1c. `ActivationCosts.payRemoveIndestructibleCounter`:
  let (gInd0, indId) := setupCounterControl bear .indestructible 1
  let gInd1 :=
    match gInd0.payRemoveIndestructibleCounter (gInd0.object! indId) (some indId) with
    | Except.ok g' => g'
    | Except.error _ => gInd0
  let indOk := exitedAndExpired gInd0 gInd1 indId .indestructible

  -- 1d. `ActivationCosts.payActivationExtraCosts` `removeStoryCounter`:
  let (gStory0, storyId) := setupCounterControl bear .story 1
  let storyAb : ActivatedAbility := {
    cost := CostSpec.ofItems #[.removeCounters (.exact 1) (some .story) .self]
    effect := {}
  }
  let gStory1 :=
    match gStory0.payActivationExtraCosts p0 storyId false false (ab := some storyAb) with
    | Except.ok g' => g'
    | Except.error _ => gStory0
  let storyOk := exitedAndExpired gStory0 gStory1 storyId .story

  -- 1e. `ActivationCosts.payActivationExtraCosts` `removePlusOnes > 0` (and `0` no-op):
  let (gPlus0, plusId) := setupCounterControl bear .plusOnePlusOne 2
  let plusAb : ActivatedAbility := { cost := CostSpec.ofItems #[.removeCounters .anyNumber (some .plusOnePlusOne) .self], effect := {} }
  let gPlusNoop :=
    match gPlus0.payActivationExtraCosts p0 plusId false false (ab := some plusAb) (removePlusOnes := 0) with
    | Except.ok g' => g'
    | Except.error _ => gPlus0
  let plusNoopOk :=
    !(gPlusNoop.events.extract gPlus0.events.size gPlusNoop.events.size).any (fun e =>
      match e.change with | .rules _ => true | _ => false) &&
    (gPlusNoop.object! plusId).isOnBattlefield &&
    (gPlusNoop.object! plusId).status.plusOnePlusOne == 2
  let gPlus1 :=
    match gPlus0.payActivationExtraCosts p0 plusId false false (ab := some plusAb) (removePlusOnes := 2) with
    | Except.ok g' => g'
    | Except.error _ => gPlus0
  let plusOk := plusNoopOk && exitedAndExpired gPlus0 gPlus1 plusId .plusOnePlusOne

  -- 1f. `Casting.payLoyaltyCost` (`k < 0`):
  let (gLoy0, loyId) := setupCounterControl pwDef .loyalty 2
  let gLoy1 := gLoy0.payLoyaltyCost p0 (gLoy0.object! loyId) (.minus 2) (forObject := some loyId)
  let loyOk := exitedAndExpired gLoy0 gLoy1 loyId .loyalty

  mustHold26i4 "1a.pwNoSrcOk" pwNoSrcOk &&
  mustHold26i4 "1b.pwWithSrcOk" pwWithSrcOk &&
  mustHold26i4 "1c.indOk" indOk &&
  mustHold26i4 "1d.storyOk" storyOk &&
  mustHold26i4 "1e.plusOk" plusOk &&
  mustHold26i4 "1f.loyOk" loyOk &&
  mustHold26i4 "1.replay"
    (replayOk26i4 #[gPwNoSrc1, gPwWithSrc1, gInd1, gStory1, gPlusNoop, gPlus1, gLoy1])

-- 2. CR 603.2c,e / 608.2h / 725.2–3 (Rulings 935, 940):
--    Per-creature monarch combat-damage triggers, resolution-time battlefield controller
--    with LKI fallback, and idempotent `.monarch` resolution when `heir` is already monarch.
#guard
  let p0 : PlayerId := ⟨0⟩
  let p1 : PlayerId := ⟨1⟩
  let p2 : PlayerId := ⟨2⟩
  let combatCause : EventCause := .turnBased (.dealCombatDamage false)
  let g3 := (mkThreePlayer26i4 2643).becomeMonarch p0
  let g3TwoBears := addPermanent (addPermanent g3 bear p1 p1) bear p1 p1
  let p1Bears := g3TwoBears.permanentsOf p1
  let b1 := p1Bears[0]!.id
  let b2 := p1Bears[1]!.id
  -- Both creatures controlled by `p1` deal combat damage to the monarch (`p0`) in one batch:
  let gHit := g3TwoBears.withBatch (some combatCause) fun g =>
    let g := g.record (GameEvent.damagedPlayer g.turnNumber
      (g.snapshotDamageSource (g.object! b1)) p0 2 true (cause := combatCause))
    g.record (GameEvent.damagedPlayer g.turnNumber
      (g.snapshotDamageSource (g.object! b2)) p0 2 true (cause := combatCause))
  let twoPerCreatureQueued :=
    gHit.waitingTriggers.size == 2 &&
    gHit.waitingTriggers[0]!.causeId == some b1 &&
    gHit.waitingTriggers[1]!.causeId == some b2 &&
    gHit.waitingTriggers.all (fun w => w.causeController == some p1)

  -- 2a. Idempotent resolution when `p1` still controls both creatures (CR 725.3):
  let gPrio := gHit.receivePriority p0
  let gStacked := mustApply gPrio p0 (.stackTriggers #[0, 1])
  let sIdemp := gStacked.events.size
  let gIdemp1 := gStacked.resolveTop
  let gIdemp2 := gIdemp1.resolveTop
  let becameEvents := (gIdemp2.events.extract sIdemp gIdemp2.events.size).filter fun e =>
    match e.change with
    | .rules (.player (.becameMonarch ..)) => true
    | _ => false
  let idempOk :=
    (gIdemp2.player p1).isMonarch &&
    becameEvents.size == 1

  -- 2b. Resolution-time controller change on top trigger (`b2` -> `p2`) + LKI fallback
  --     when `b1` leaves the battlefield before the bottom trigger resolves (Ruling 935):
  let gStolen := gStacked.createEffect (.layered (.objects #[b2]) (.control p2) .untilEndOfTurn)
  let (gStolenAndExiled, _) := gStolen.move b1 .exile none (cause := some testCause)
  let gResTop := gStolenAndExiled.resolveTop
  let topGaveP2Monarch := (gResTop.player p2).isMonarch && !(gResTop.player p1).isMonarch
  let gResBot := gResTop.resolveTop
  let botLkiGaveP1Monarch := (gResBot.player p1).isMonarch && !(gResBot.player p2).isMonarch

  mustHold26i4 "2.twoPerCreatureQueued" twoPerCreatureQueued &&
  mustHold26i4 "2a.idempOk" idempOk &&
  mustHold26i4 "2b.resolutionCtrlAndLkiOk" (topGaveP2Monarch && botLkiGaveP1Monarch) &&
  mustHold26i4 "2.replay" (replayOk26i4 #[gIdemp2, gResBot])

-- 3. CR 103.1a / 805.3 / 805.4 / 805.4a,b,d / 805.6–7:
--    2HG starting-team seat normalization, `apnapPlayers` active-team ordering,
--    shared-step trigger gating across teammates, and `firstOfTheirDrawStep` / `firstOfYourDrawStep`.
#guard
  -- 3a. `Start.startWithRng` normalizes `startingPlayer := some 1` to Team A's first seat `⟨0⟩`:
  let gStartNorm := mkTwoHeadedGiant26i4 2644 (startingSeat := 1)
  let startNormOk := gStartNorm.startingPlayer == ⟨0⟩ && gStartNorm.activePlayer == ⟨0⟩

  -- 3b. `apnapPlayers` places all living members of the active team first in seat order:
  let gSeat1Active := gStartNorm.record (GameEvent.turnBegan gStartNorm.turnNumber ⟨1⟩ false)
  let gSeat3Active := gStartNorm.record (GameEvent.turnBegan (gStartNorm.turnNumber + 1) ⟨3⟩ false)
  let apnapOk :=
    gStartNorm.apnapPlayers == #[⟨0⟩, ⟨1⟩, ⟨2⟩, ⟨3⟩] &&
    gSeat1Active.apnapPlayers == #[⟨0⟩, ⟨1⟩, ⟨2⟩, ⟨3⟩] &&
    gSeat3Active.apnapPlayers == #[⟨2⟩, ⟨3⟩, ⟨0⟩, ⟨1⟩]

  -- 3c. Shared-step triggers fire for both teammates on the first/final seat and not twice:
  let upkeepWatcher (nm : String) : CardDef := {
    name := nm
    types := #[.enchantment]
    triggeredAbilities := #[TriggeredAbility.mkTrigger .stepYourUpkeep { body := Instruction.gainLifeFixed 1 }]
  }
  let mainWatcher (nm : String) : CardDef := {
    name := nm
    types := #[.enchantment]
    triggeredAbilities := #[TriggeredAbility.mkTrigger .stepYourFirstMain { body := Instruction.gainLifeFixed 1 }]
  }
  let combatWatcher (nm : String) : CardDef := {
    name := nm
    types := #[.enchantment]
    triggeredAbilities := #[TriggeredAbility.mkTrigger .stepYourBeginCombat { body := Instruction.gainLifeFixed 1 }]
  }
  let endWatcher (nm : String) : CardDef := {
    name := nm
    types := #[.enchantment]
    triggeredAbilities := #[TriggeredAbility.mkTrigger .stepYourEndStep { body := Instruction.gainLifeFixed 1 }]
  }
  let eachUpkeepWatcher : CardDef := {
    name := "Each Upkeep 26i4"
    types := #[.enchantment]
    triggeredAbilities := #[TriggeredAbility.mkTrigger .stepEachUpkeep { body := Instruction.gainLifeFixed 1 }]
  }
  let eachEndWatcher : CardDef := {
    name := "Each End 26i4"
    types := #[.enchantment]
    triggeredAbilities := #[TriggeredAbility.mkTrigger .stepEachEndStep { body := Instruction.gainLifeFixed 1 }]
  }
  let g2hg :=
    addPermanent (addPermanent (addPermanent (addPermanent
      (addPermanent (addPermanent (addPermanent (addPermanent
        (addPermanent (addPermanent gStartNorm
          (upkeepWatcher "Up0") ⟨0⟩ ⟨0⟩)
          (upkeepWatcher "Up1") ⟨1⟩ ⟨1⟩)
        (mainWatcher "Main0") ⟨0⟩ ⟨0⟩)
        (mainWatcher "Main1") ⟨1⟩ ⟨1⟩)
      (combatWatcher "Comb0") ⟨0⟩ ⟨0⟩)
      (combatWatcher "Comb1") ⟨1⟩ ⟨1⟩)
    (endWatcher "End0") ⟨0⟩ ⟨0⟩)
    (endWatcher "End1") ⟨1⟩ ⟨1⟩)
    eachUpkeepWatcher ⟨2⟩ ⟨2⟩)
    eachEndWatcher ⟨2⟩ ⟨2⟩
  -- Seat 0 (`isSharedTurnFirstSeat = true`, `isSharedTurnFinalSeat = false`):
  let gUp0 := (g2hg.change (.waitingTriggers #[])).record (GameEvent.stepped g2hg.turnNumber .upkeep ⟨0⟩)
  let gMain0 := (g2hg.change (.waitingTriggers #[])).record (GameEvent.stepped g2hg.turnNumber .precombatMain ⟨0⟩)
  let gComb0 := (g2hg.change (.waitingTriggers #[])).record (GameEvent.stepped g2hg.turnNumber .beginningOfCombat ⟨0⟩)
  let gEnd0 := (g2hg.change (.waitingTriggers #[])).record (GameEvent.stepped g2hg.turnNumber .end ⟨0⟩)
  let seat0StepsOk :=
    gUp0.waitingTriggers.size == 3 &&
    gMain0.waitingTriggers.size == 2 &&
    gComb0.waitingTriggers.size == 2 &&
    gEnd0.waitingTriggers.isEmpty
  -- Seat 1 (`isSharedTurnFirstSeat = false`, `isSharedTurnFinalSeat = true`):
  let g2hgSeat1 := g2hg.startNextTurnCore false
  let gUp1 := (g2hgSeat1.change (.waitingTriggers #[])).record (GameEvent.stepped g2hgSeat1.turnNumber .upkeep ⟨1⟩)
  let gMain1 := (g2hgSeat1.change (.waitingTriggers #[])).record (GameEvent.stepped g2hgSeat1.turnNumber .precombatMain ⟨1⟩)
  let gComb1 := (g2hgSeat1.change (.waitingTriggers #[])).record (GameEvent.stepped g2hgSeat1.turnNumber .beginningOfCombat ⟨1⟩)
  let gComb1Extra :=
    ((g2hgSeat1.change (.waitingTriggers #[])).record (GameEvent.phaseEnded g2hgSeat1.turnNumber .combat)).record
      (GameEvent.stepped g2hgSeat1.turnNumber .beginningOfCombat ⟨1⟩)
  let gEnd1 := (g2hgSeat1.change (.waitingTriggers #[])).record (GameEvent.stepped g2hgSeat1.turnNumber .end ⟨1⟩)
  let seat1StepsOk :=
    gUp1.waitingTriggers.isEmpty &&
    gMain1.waitingTriggers.isEmpty &&
    gComb1.waitingTriggers.isEmpty &&
    gComb1Extra.waitingTriggers.size == 2 &&
    gEnd1.waitingTriggers.size == 3

  -- 3d. `firstOfTheirDrawStep` is `true` for teammate `⟨1⟩`'s first draw during the shared draw step (CR 805.4b):
  let gDrawStep := gStartNorm.record (GameEvent.stepped gStartNorm.turnNumber .draw ⟨0⟩)
  let sDraw1 := gDrawStep.events.size
  let gDrawn1 := gDrawStep.draw ⟨1⟩ 1
  let firstDrawMarked :=
    (gDrawn1.events.extract sDraw1 gDrawn1.events.size).any fun e =>
      match e.change with
      | .rules (.zone (.moved _ _ (.library ⟨1⟩) (.hand ⟨1⟩) (.draw 1 true) (some ⟨1⟩) ..)) => true
      | _ => false

  mustHold26i4 "3a.startNormOk" startNormOk &&
  mustHold26i4 "3b.apnapOk" apnapOk &&
  mustHold26i4 "3c.sharedStepsOk" (seat0StepsOk && seat1StepsOk) &&
  mustHold26i4 "3d.firstDrawMarked" firstDrawMarked &&
  mustHold26i4 "3.replay" (replayOk26i4 #[gUp0, gMain0, gComb0, gComb1Extra, gEnd1, gDrawn1])

-- 4. CR 301.5d / 506.5–6 / 508.3d / 603.2c / 613.1a,c:
--    Battle-excluded attack triggers, cross-controller `.equippedAttacksAlone`,
--    layer-resolved battlefield `g.name`, and 88-field `ContinuationFrame` witness.
#guard
  let p0 : PlayerId := ⟨0⟩
  let p1 : PlayerId := ⟨1⟩
  let p2 : PlayerId := ⟨2⟩
  let g0 := mkThreePlayer26i4 2645
  let battleDef : CardDef := {
    name := "Test Battle 26i4"
    types := #[.battle]
    defense := some 4
  }
  let aloneWatcher : CardDef := {
    name := "Alone Watcher 26i4"
    types := #[.enchantment]
    triggeredAbilities := #[TriggeredAbility.mkTrigger .creatureYouControlAttacksPlayerAlone { body := Instruction.gainLifeFixed 1 }]
  }
  let twoWatcher : CardDef := {
    name := "Two Watcher 26i4"
    types := #[.enchantment]
    triggeredAbilities := #[TriggeredAbility.mkTrigger .youAttackWithTwoOrMoreToPlayer { body := Instruction.gainLifeFixed 1 } (grouping := .perPlayerInBatch)]
  }
  let eqAloneDef : CardDef := {
    name := "Cross Equipment 26i4"
    types := #[.artifact]
    subtypes := #["Equipment"]
    triggeredAbilities := #[TriggeredAbility.mkTrigger .equippedAttacksAlone { body := Instruction.gainLifeFixed 1 }]
  }
  let gBattle0 :=
    addPermanent (addPermanent (addPermanent (addPermanent (addPermanent g0
      battleDef p1 p1) aloneWatcher p0 p0) twoWatcher p0 p0) bear p0 p0) bear p0 p0
  let battleId := (gBattle0.permanentsOf p1).find? (·.name == "Test Battle 26i4") |>.get!.id
  let p0Bears := (gBattle0.permanentsOf p0).filter (·.name == bear.name)
  let a1 := p0Bears[0]!.id
  let a2 := p0Bears[1]!.id

  -- 4a. Two creatures attacking a battle trigger neither `.creatureYouControlAttacksPlayerAlone`
  --     nor `.youAttackWithTwoOrMoreToPlayer` (CR 506.6 / 508.3d):
  let gAtkBattle :=
    ((gBattle0.change (.waitingTriggers #[])).record
      (GameEvent.attackersDeclared gBattle0.turnNumber p0 #[
        (gBattle0.snapshot (gBattle0.object! a1), .battle battleId),
        (gBattle0.snapshot (gBattle0.object! a2), .battle battleId)
      ]))
  let battleExcludedOk := gAtkBattle.waitingTriggers.isEmpty

  -- One creature attacking `p1` and one creature attacking `battleId` triggers
  -- `.creatureYouControlAttacksPlayerAlone` for `a1`, and not `.youAttackWithTwoOrMoreToPlayer`:
  let gAtkSplit :=
    ((gBattle0.change (.waitingTriggers #[])).record
      (GameEvent.attackersDeclared gBattle0.turnNumber p0 #[
        (gBattle0.snapshot (gBattle0.object! a1), .player p1),
        (gBattle0.snapshot (gBattle0.object! a2), .battle battleId)
      ]))
  let splitAloneOk :=
    gAtkSplit.waitingTriggers.size == 1 &&
    gAtkSplit.waitingTriggers[0]!.pattern == .creatureYouControlAttacksPlayerAlone &&
    gAtkSplit.waitingTriggers[0]!.causeId == some a1

  -- Two creatures attacking `p1` and two creatures attacking `p2` queue `.youAttackWithTwoOrMoreToPlayer`
  -- twice (once per attacked player, CR 508.3d / 603.2c):
  let gFourBears := addPermanent (addPermanent gBattle0 bear p0 p0) bear p0 p0
  let fourIds := ((gFourBears.permanentsOf p0).filter (·.name == bear.name)).map (·.id)
  let gAtkTwoPlayers :=
    ((gFourBears.change (.waitingTriggers #[])).record
      (GameEvent.attackersDeclared gFourBears.turnNumber p0 #[
        (gFourBears.snapshot (gFourBears.object! fourIds[0]!), .player p1),
        (gFourBears.snapshot (gFourBears.object! fourIds[1]!), .player p1),
        (gFourBears.snapshot (gFourBears.object! fourIds[2]!), .player p2),
        (gFourBears.snapshot (gFourBears.object! fourIds[3]!), .player p2)
      ]))
  let twoOrMoreCount :=
    (gAtkTwoPlayers.waitingTriggers.filter (·.pattern == .youAttackWithTwoOrMoreToPlayer)).size
  let twoPlayersOk := twoOrMoreCount == 2

  -- 4b. `.equippedAttacksAlone` fires for `p1`'s Equipment attached to `p0`'s sole attacker (CR 301.5d / 506.5):
  let gEq0 := addPermanent gBattle0 eqAloneDef p1 p1
  let eqId := (gEq0.permanentsOf p1).find? (·.name == "Cross Equipment 26i4") |>.get!.id
  let gEqAttached := gEq0.attachSourceTo (gEq0.object! eqId) (gEq0.object! a1)
  let gEqAlone :=
    ((gEqAttached.change (.waitingTriggers #[])).record
      (GameEvent.attackersDeclared gEqAttached.turnNumber p0 #[
        (gEqAttached.snapshot (gEqAttached.object! a1), .player p1)
      ]))
  let eqAloneOk :=
    gEqAlone.waitingTriggers.any (fun w =>
      w.pattern == .equippedAttacksAlone && w.controller == p1 && w.source.id == eqId)

  -- 4c. Layer-resolved `g.name` on battlefield permanents (CR 613.1a,c / 707.2):
  let copyCard : CardDef := { bear with name := "Copied Hero" }
  let gRenamed := gBattle0.createEffect (.layered (.objects #[a1]) (.copy copyCard) .untilEndOfTurn)
  let gExiledRenamed :=
    gRenamed.applyEffect p0 { targeting := .of .creature, body := Instruction.exile (.target 0) } #[.permanent a1]
  let renamedLogOk := gExiledRenamed.log.any (· == "Copied Hero is exiled")

  -- 4d. 88-field `ContinuationFrame` witness (`palantirAfterScry` retired):
  let cf88 : ContinuationFrame := {
    pendingDrawAfterScry := none
    discardedCardThisWay := none
    recentTokenIds := #[]
    fraAfterLook := none
    pendingFreeCopies := none
    pendingMayCastFromExile := none
    postCastCleanup := none
    humansTappedThisWay := 0
    permanentsDestroyedThisWay := 0
    removedHopeThisWay := false
    permanentDealtDamageThisWay := none
    returnedPermanentThisWay := false
    nthResolveThisWay := none
    skipTriggerSequenceRest := false
    excessDamageThisWay := 0
    destroyedForAmassThisWay := false
    amassAmountThisWay := 0
    amassYouControlledThisWay := false
    milledIdsThisWay := #[]
    revealedIdsThisWay := #[]
    opponentsMilledThisWay := false
    palantirChoiceReady := none
    grimaImpulseReady := false
    grimaImpulseVictim := none
    grimaImpulseFound := none
    grimaImpulseOthers := #[]
    planWasSacrificed := false
    sourceWasSacrificed := false
    exiledIdsThisWay := #[]
    notedCopyObject := none
    notedHostId := none
    handDiscardedThisWay := none
    notedSourceThisWay := none
    equipmentAttachedHost := none
    notedCountThisWay := 0
    createdTokensThisWay := #[]
    putArtifactThisWay := none
    playExiledThisWay := none
    armSurveilReturn := false
    triggerSequenceRest := none
    mayThenDrop := 0
    mayThenSkip := 0
    mayThenConditional := none
    mayOnAccept := none
    mayOnDecline := none
    mayContext := none
    sacrificedPowerThisWay := none
    mayThenResume := false
    triggerOr := none
    chooseModesRest := none
    unlessPaysInstead := none
    unlessPaysController := ⟨0⟩
    unlessPaysTargets := #[]
    unlessPaysSource := none
    unlessPaysDue := false
    mayEffect := none
    mayController := ⟨0⟩
    mayTargets := #[]
    maySource := none
    spellOr := #[]
    spellOrController := ⟨0⟩
    spellOrTargets := #[]
    spellOrSource := none
    spellOrLibrary := false
    surveilReturnMvAtMost := none
    surveilReturnNoncreatureNonland := false
    pendingReplacement := none
    outerPendingReplacements := #[]
    conniveSource := none
    plusOneAfterDiscards := none
    plusOneAfterSearch := none
    thirstDiscardsLeft := 0
    thirstDiscardType := .artifact
    pendingDiscardsLeft := 0
    discardCountPerPlayer := 0
    discardBatch := none
    stagedAttackTokenBatches := #[]
    untapSearchedIfLands := none
    resolvingContext := none
    stashedCause := none
    resolvingSpell := none
    resolvingAbility := none
    resolvingModes := none
    resolvingDivision := #[]
    resolvingSkippedSlots := #[]
    afterRandom := .none
    resolutionFinish := none
    pendingResolvedEvent := none
  }

  mustHold26i4 "4a.battleAndTwoPlayersOk" (battleExcludedOk && splitAloneOk && twoPlayersOk) &&
  mustHold26i4 "4b.eqAloneOk" eqAloneOk &&
  mustHold26i4 "4c.renamedLogOk" renamedLogOk &&
  mustHold26i4 "4d.cf88Ok" (cf88 == {}) &&
  mustHold26i4 "4.replay" (replayOk26i4 #[gAtkBattle, gAtkSplit, gAtkTwoPlayers, gEqAlone, gExiledRenamed])

end Phase26Item4EventAlignment

/-! ### Phase 27 Item 1: Non-replacement `inDepSpan` & `cleanupRemappedLeavingId`,
multi-departure `popOuter` accumulation, stack-ability `representedByCard` ownership,
`!g.stillInGame` CR 800.4 guards, and `FraChoices` accept-cast `outerPendingReplacements` stashing -/
section Phase27Item1EventAlignment

private def mustHold27i1 (label : String) (ok : Bool) : Bool :=
  if ok then true else panic! s!"Phase27Item1EventAlignment failed: {label}"

private def replayOk27i1 (gs : Array Game) : Bool :=
  gs.all (fun g => Game.replayEvents g.events == g && allRulesEventsClassified g)

-- 1. CR 104.3a / 610.3 / 704.3 / 733.1 / 800.4a:
--    Non-replacement `inDepSpan` preservation of CR 800.4a control-loss exiles, CR 610.3
--    linked-exile returns, post-departure SBAs, and `depReplacementPending` cost payments
--    across `reverseToProposalCheckpointCore?`, plus `cleanupRemappedLeavingId` continuous-effect
--    and prepared-copy cleanup and `applyKeptEvent` `.unattached` / `.designation` remapping.
#guard
  let p0 : PlayerId := ⟨0⟩
  let p1 : PlayerId := ⟨1⟩
  let p2 : PlayerId := ⟨2⟩
  let gBase := mkThreePlayer27i1 2712
  let rggSpellDef : CardDef := {
    name := "P27i1 RGG Spell"
    manaCost := ⟨#[.colored .red, .colored .green, .colored .green]⟩
    types := #[.instant]
    spellEffect := some { body := Instruction.drawFixed 1, phrase := "Draw a card" }
  }
  let shockLandDef : CardDef := {
    name := "P27i1 Shock Land"
    types := #[.land]
    subtypes := #["Mountain", "Forest"]
    staticAbilities := #[.entersTappedUnlessPayLife 2]
  }
  let treasureCardDef : CardDef := {
    name := "P27i1 Lotus Petal"
    types := #[.artifact]
    activatedAbilities := #[ActivatedAbility.manaTapSacrificeAnyColor]
    prepareFace := some {
      name := "P27i1 Prepared Bolt"
      manaCost := ManaCost.empty
      types := #[.instant]
      spellEffect := some { body := Instruction.gainLifeFixed 1, phrase := "You gain 1 life" }
    }
  }
  let equipDef : CardDef := {
    name := "P27i1 Sword"
    types := #[.artifact]
    subtypes := #["Equipment"]
  }
  -- `p1` owns `jailer` (holding `p2`'s `shockLandDef` in linked exile), `p2` owns `stolenBear`
  -- controlled by `p1` via a Layer-2 control effect, and `p0` controls `p1`-owned `treas` (which
  -- also has `.whileSourceOnBattlefield`, `.untilSourceLeaves`, `.whileSourceHasCounter`, `.cantUntap`,
  -- and a prepared copy in `.exile`):
  let g0 :=
    insertObject
      (insertObject
        (addPermanent
          (addPermanent
            (addPermanent
              (addPermanent gBase bear p1 p1)
              bear p2 p2)
            treasureCardDef p1 p0)
          equipDef p2 p2)
        shockLandDef p2 .exile)
      rggSpellDef p0 (.hand p0)
  let jailerId := (g0.battlefield.filter (fun o => o.name == bear.name && o.owner == p1))[0]!.id
  let stolenBearId := (g0.battlefield.filter (fun o => o.name == bear.name && o.owner == p2))[0]!.id
  let treasId := (g0.battlefield.filter (·.name == treasureCardDef.name))[0]!.id
  let equipId := (g0.battlefield.filter (·.name == equipDef.name))[0]!.id
  let spellId := (g0.player p0).hand.back!
  let shockExId := (g0.objects.filter (fun o => o.zone == .exile && o.name == shockLandDef.name))[0]!.id
  -- Link `shockExId` to `jailerId` (`linkedExile := #[shockExId]`):
  let gLinked := g0.changeObject jailerId (.linkedExile #[shockExId])
  -- Prepare `treasId` so it creates a prepared copy in `.exile`, put a `+1/+1` counter on `treasId`,
  -- and attach continuous effects keyed to `treasId` plus `p1`'s Layer-2 control of `stolenBearId`:
  let gPrepared :=
    let g1 := gLinked.record (GameEvent.designation gLinked.turnNumber (gLinked.snapshot (gLinked.object! treasId)) .prepared true (cause := testCause))
    let g2 := g1.ensurePreparedCopy (g1.object! treasId)
    let g3 := g2.recordPutCounters treasId .plusOnePlusOne 1 (byPlayer := some p0) (cause := some testCause)
    let g4 := g3.createEffect (.layered (.objects #[stolenBearId]) (.control p1) .indefinite) (cause := some testCause)
    let g5 := g4.createEffect (.layered (.objects #[stolenBearId]) (.ptModify 1 1) (.whileSourceOnBattlefield treasId)) (cause := some testCause)
    let g6 := g5.createEffect (.layered (.objects #[stolenBearId]) (.ptModify 1 1) (.untilSourceLeaves treasId)) (cause := some testCause)
    let g7 := g6.createEffect (.layered (.objects #[stolenBearId]) (.ptModify 1 1) (.whileSourceHasCounter treasId .plusOnePlusOne)) (cause := some testCause)
    g7.createEffect (.gameRule (.cantUntap stolenBearId treasId) .indefinite) (cause := some testCause)
  let prepCopyId := (gPrepared.preparedCopyOf? treasId).get!.id

  -- `p0` proposes `rggSpellDef` (entering non-replacement `.activateManaAbilities p0`),
  -- sacrifices `treasId` for `{R}` (`treasId -> treasGyId`), and then `p1` concedes!
  -- During `p1`'s departure:
  --  * `jailerId` leaves the game and `shockLinkedId` returns to the battlefield under CR 610.3,
  --    opening `.chooseReplacement p2` for `.entersUntappedPayLife 2`, where `p2` pays 2 life
  --    (`depReplacementPending == true` `.costPayment .life p2`!).
  let gCast := mustApply gPrepared p0 (.cast spellId)
  let gAfterTreas := mustApply gCast p0 (.tapForMana treasId (.colored .red))
  let gConcedePaused := mustApply gAfterTreas p1 .concede
  let shockChoicePaused :=
    match gConcedePaused.pending with
    | .chooseReplacement chooser choices =>
      chooser == p2 && choices.any (·.kind == .entersUntappedPayLife 2)
    | _ => false
  let payLifeChoice :=
    match gConcedePaused.pending with
    | .chooseReplacement _ choices =>
      choices.find? (·.kind == .entersUntappedPayLife 2) |>.get!
    | _ => default
  let gAfterConcede := mustApply gConcedePaused p2 (.chooseReplacement payLifeChoice)
  -- Now `gAfterConcede.pending == .activateManaAbilities p0`; `p0` attempts `.pay` with only `{R}`,
  -- reversing the proposal via `reverseToProposalCheckpointCore?`:
  let gRev := mustApply gAfterConcede p0 .pay
  let shockBf := (gRev.permanentsOf p2).find? (·.name == shockLandDef.name)
  let nonRepDepSpanAndCleanupOk :=
    shockChoicePaused &&
    gAfterConcede.pending == .activateManaAbilities p0 &&
    gRev.proposalCheckpoint.isNone &&
    gRev.proposedSpell.isNone &&
    gRev.pending == .none &&
    (gRev.player p1).leftTheGame &&
    -- `p2`'s shock land returned untapped and `p2`'s 2-life payment was preserved across reversal:
    shockBf.any (fun o => !o.status.tapped) &&
    (gRev.player p2).life == 18 &&
    -- `treasId` (moved during the reversed proposal and owned by departing `p1`) and its prepared copy
    -- and `treasId`-scoped continuous effects were all cleaned up by `cleanupRemappedLeavingId`:
    (gRev.findObject? treasId).isNone &&
    (gRev.findObject? prepCopyId).isNone &&
    !gRev.activeEffects.any (fun (_, eff) =>
      eff.duration == .whileSourceOnBattlefield treasId ||
      eff.duration == .untilSourceLeaves treasId ||
      eff.duration == .whileSourceHasCounter treasId .plusOnePlusOne ||
      (match eff with
       | .gameRule (.cantUntap _ s) _ => s == treasId
       | .permission _ (.playFromExile _ perm) _ => perm.prepareSource == some treasId
       | _ => false)) &&
    (gRev.player p0).manaPool.total == 0 &&
    (gRev.player p0).hand.contains spellId

  -- Also verify `applyKeptEvent` remaps `.unattached` when a permanent `equipId`
  -- became unattached during a kept departure:
  let gAttach0 :=
    gPrepared.attachSourceTo (gPrepared.object! equipId) (gPrepared.object! jailerId) (cause := some testCause)
  let gAttachCast := mustApply gAttach0 p0 (.cast spellId)
  let gAttachConcedeP := mustApply gAttachCast p1 .concede
  let gAttachConcede :=
    match gAttachConcedeP.pending with
    | .chooseReplacement q cs => mustApply gAttachConcedeP q (.chooseReplacement cs[0]!)
    | _ => gAttachConcedeP
  let gAttachRev := mustApply gAttachConcede p0 .pay
  let unattachAndDesigOk :=
    (gAttachRev.object! equipId).attachedTo.isNone

  mustHold27i1 "1a.nonRepDepSpanAndCleanupOk" nonRepDepSpanAndCleanupOk &&
  mustHold27i1 "1b.unattachAndDesigOk" unattachAndDesigOk &&
  mustHold27i1 "1.replay"
    (replayOk27i1 #[gConcedePaused, gAfterConcede, gRev, gAttachConcede, gAttachRev])

-- 2. CR 108.3 / 113.8 / 601.2 / 800.4a / 810.8a:
--    Multi-departure `concedePlayersLoop` / `leavePlayersWhoLost` `popOuter` accumulation,
--    and stack-ability `!representedByCard` non-owner survival on owner departure.
#guard
  let p0 : PlayerId := ⟨0⟩
  let p1 : PlayerId := ⟨1⟩
  let p2 : PlayerId := ⟨2⟩
  -- 2a. `leavePlayersWhoLost` with two departing players (`p1` and `p2`) where `p1`'s departure
  --     populates `saved?` (`po = false`) and `p2`'s departure sets `po = true` (after pushing
  --     an outer continuation): `popOuter := popOuter || po` preserves `popOuter == true`!
  let gBase := mkThreePlayer27i1 2713
  let pingArtDef : CardDef := {
    name := "P27i1 Ping Relic"
    types := #[.artifact]
    activatedAbilities := #[{
      cost := CostSpec.ofItems #[.mana (ManaCost.ofGeneric 2)]
      effect := { body := Instruction.gainLifeFixed 2, phrase := "You gain 2 life" }
    }]
  }
  let gLost0 :=
    ((gBase.change (.pushContinuationFrame {})).record
      (GameEvent.playerLost gBase.turnNumber p1 .lifeZeroOrLess (cause := some (.stateBased .lifeZeroOrLess)))).record
      (GameEvent.playerLost gBase.turnNumber p2 .lifeZeroOrLess (cause := some (.stateBased .lifeZeroOrLess)))
  let gLostWithOuter :=
    (gLost0.change (.pendingReplacement (some (.finishPostStep (.beginScryOne p0))))).change
      (.pending (.scry p0 1))
  let gAfterBothLeft := gLostWithOuter.leavePlayersWhoLost
  let multiLeavePopOuterOk :=
    (gAfterBothLeft.player p1).leftTheGame &&
    (gAfterBothLeft.player p2).leftTheGame &&
    gAfterBothLeft.pending == .scry p0 1 &&
    gAfterBothLeft.outerPendingReplacements.isEmpty &&
    gAfterBothLeft.pendingReplacement == some (.finishPostStep (.beginScryOne p0))

  -- 2b. Stack ability (`!representedByCard o`) controlled by `p0` from a `p1`-owned permanent
  --     survives when `p1` leaves the game (both when already on `.stack` and when proposed in
  --     `g.proposedSpell` with `prop.kind == .activatedAbility`):
  let gAb0 := addPermanent (gBase.addMana p0 .colorless 2) pingArtDef p1 p0
  let relicId := (gAb0.permanentsOf p0).find? (·.name == pingArtDef.name) |>.get!.id
  let gActivated := mustApply (mustApply gAb0 p0 (.activate relicId 0)) p0 .pay
  let stackAbId := gActivated.stack.back!.objectId
  let gOwnerConceded := mustApply gActivated p1 .concede
  let gAbResolved := mustApply (mustApply gOwnerConceded p0 .pass) p2 .pass
  -- Also test `isProposalAbortedByLeave` when `p0` is proposing the activation of `p1`-owned `relicId2`:
  let gAb2 := addPermanent gBase pingArtDef p1 p0
  let relicId2 := (gAb2.permanentsOf p0).find? (·.name == pingArtDef.name) |>.get!.id
  let gPropAb := mustApply gAb2 p0 (.activate relicId2 0)
  let gPropAfterP2Leaves := mustApply gPropAb p2 .concede
  let gPropAfterP1Leaves := mustApply gPropAb p1 .concede
  let gPropAfterP0Leaves := mustApply gPropAb p0 .concede
  let abNotAbortedByOwnerLeave :=
    gPropAb.proposedSpell.isSome &&
    gPropAfterP2Leaves.proposedSpell.isSome &&
    gPropAfterP1Leaves.proposedSpell.isNone &&
    gPropAfterP0Leaves.proposedSpell.isNone
  let stackAbSurvivesOk :=
    (gActivated.object! stackAbId).owner == p1 &&
    (gActivated.object! stackAbId).controller == some p0 &&
    (gActivated.object! stackAbId).abilityEffect.isSome &&
    gOwnerConceded.stack.any (·.objectId == stackAbId) &&
    (gAbResolved.player p0).life == 22 &&
    abNotAbortedByOwnerLeave

  -- 2c. When `redirectPendingAfterLeave` preserves a surviving player's prompt in `curPending`
  --     (e.g. `.payWard p0 ...`) while `wasAbortedProposal == true` and `postCastCleanup` has 2+
  --     exiled cards (`.cascadeBottom`), `orderBottomInCleanup` orders the cards directly via
  --     `moveIdsInOrder` instead of opening `.resolveRandom (.orderInto ...)`, preserving `.payWard`:
  let gCasc0 :=
    insertObject
      (insertObject
        (insertObject
          (insertObject (gBase.change (.pushContinuationFrame {})) bear p0 .exile)
          bear p0 .exile)
        hero p0 .stack (some p0))
      bear p1 (.hand p1)
  let cascExIds := (gCasc0.objects.filter (fun o => o.zone == .exile && o.owner == p0)).map (·.id)
  let cCard0 := cascExIds[0]!
  let cCard1 := cascExIds[1]!
  let wardSpellId := (gCasc0.objects.filter (fun o => o.zone == .stack && o.owner == p0))[0]!.id
  let p1HandSpellId := (gCasc0.player p1).hand.back!
  let propP1 : ProposedSpell := {
    caster := p1
    cost := default
    spellId := p1HandSpellId
    original := gCasc0.object! p1HandSpellId
  }
  let gCascWard :=
    ((gCasc0.putStackEntry p0 wardSpellId).changes #[
      .pending (.payWard p0 wardSpellId default),
      .proposedSpell (some propP1),
      .postCastCleanup (some (.cascadeBottom p0 cCard0 #[cCard1]))
    ])
  let gAfterCascLeave := gCascWard.playerLeavesGame p1
  let keepArmAndBottomOrderPreservedOk :=
    gAfterCascLeave.pending == .payWard p0 wardSpellId default &&
    gAfterCascLeave.postCastCleanup.isNone &&
    (gAfterCascLeave.followMovedToZone? cCard0 (· == .library p0)).isSome &&
    (gAfterCascLeave.followMovedToZone? cCard1 (· == .library p0)).isSome

  -- 2d. When an aborted proposal (`wasAbortedProposal == true`, including from `.chooseReplacement`)
  --     activates `pendingMayCastFromExile`, `.pending (.fraChoice ...)` is restored via
  --     `savedPreLeavePending?` AFTER `runEndControlExileLoop` so control-loss exiles remain inside
  --     `inDepSpan`:
  let nonLandSpellDef : CardDef := {
    name := "P27i1 Exiled Bolt"
    manaCost := ⟨#[.colored .red]⟩
    types := #[.instant]
    spellEffect := some { body := Instruction.gainLifeFixed 1, phrase := "You gain 1 life" }
  }
  let gMayEx0 :=
    insertObject
      (addPermanent gCasc0 bear p2 p1)
      nonLandSpellDef p0 .exile
  let p2PermId := (gMayEx0.permanentsOf p1).find? (fun o => o.name == bear.name && o.owner == p2) |>.get!.id
  let exBoltId := (gMayEx0.objects.filter (fun o => o.zone == .exile && o.name == nonLandSpellDef.name))[0]!.id
  let gMayEx1 :=
    gMayEx0.changes #[
      .pending (.chooseReplacement p1 #[]),
      .proposedSpell (some propP1),
      .pendingMayCastFromExile (some (p0, #[exBoltId], 1))
    ]
  let gAfterMayExLeave := gMayEx1.playerLeavesGame p1
  let expectedFra := Pending.fraChoice p0 (.mayCastUpToFromExile #[exBoltId] 1)
  let exileIdx? := gAfterMayExLeave.events.findIdx? (fun ev =>
    match ev with
    | .rules _ (.zone (.moved _ _ .battlefield .exile ..)) _ _ => true
    | _ => false)
  let fraPendingIdx? := gAfterMayExLeave.events.findIdx? (fun ev =>
    ev == .engine gAfterMayExLeave.turnNumber (.pending expectedFra) none)
  let mayCastFromExileDepSpanOk :=
    gAfterMayExLeave.pending == expectedFra &&
    gAfterMayExLeave.pendingMayCastFromExile.isNone &&
    (gAfterMayExLeave.followMovedToZone? p2PermId (· == .exile)).isSome &&
    match exileIdx?, fraPendingIdx? with
    | some eIdx, some pIdx => eIdx < pIdx
    | _, _ => false

  -- 2e. When `redirectPendingAfterLeave` hands off a prompt to the next player
  --     (e.g. `.chooseDiscardCard p1 #[p2]` -> `.chooseDiscardCard p2 #[]`), it returns the
  --     next `Pending` without journaling `.pending` inside `playerLeavesGameCore`'s batch, so
  --     control-loss exiles still precede `restoreSavedPostLeave`'s `.pending` event:
  let gDiscHandoff0 :=
    (insertObject gMayEx0 bear p2 (.hand p2)).change
      (.pending (.chooseDiscardCard p1 #[p2]))
  let gAfterDiscHandoffLeave := gDiscHandoff0.playerLeavesGame p1
  let expectedDisc := Pending.chooseDiscardCard p2 #[]
  let discExileIdx? := gAfterDiscHandoffLeave.events.findIdx? (fun ev =>
    match ev with
    | .rules _ (.zone (.moved _ _ .battlefield .exile ..)) _ _ => true
    | _ => false)
  let discPendingIdx? := gAfterDiscHandoffLeave.events.findIdx? (fun ev =>
    ev == .engine gAfterDiscHandoffLeave.turnNumber (.pending expectedDisc) none)
  let discardHandoffDepSpanOk :=
    gAfterDiscHandoffLeave.pending == expectedDisc &&
    (gAfterDiscHandoffLeave.followMovedToZone? p2PermId (· == .exile)).isSome &&
    match discExileIdx?, discPendingIdx? with
    | some eIdx, some pIdx => eIdx < pIdx
    | _, _ => false

  mustHold27i1 "2a.multiLeavePopOuterOk" multiLeavePopOuterOk &&
  mustHold27i1 "2b.stackAbSurvivesOk" stackAbSurvivesOk &&
  mustHold27i1 "2c.keepArmAndBottomOrderPreservedOk" keepArmAndBottomOrderPreservedOk &&
  mustHold27i1 "2d.mayCastFromExileDepSpanOk" mayCastFromExileDepSpanOk &&
  mustHold27i1 "2e.discardHandoffDepSpanOk" discardHandoffDepSpanOk &&
  mustHold27i1 "2.replay" (replayOk27i1 #[gAfterBothLeft, gActivated, gOwnerConceded, gAbResolved, gPropAb, gPropAfterP1Leaves, gPropAfterP0Leaves, gAfterCascLeave, gAfterMayExLeave, gAfterDiscHandoffLeave])

-- 3. CR 608.2g / 701.22 / 701.23 / 701.25 / 800.4a,c–d:
--    `beginLibrarySearch` / `beginScry` / `beginSurveil` & `!g.stillInGame` guards on a player
--    with `leftTheGame == true` (even if `lost == false`), plus `FraChoices.answerFraChoice`
--    stashing `pendingReplacement` onto `outerPendingReplacements` across accept-cast branches.
#guard
  let p0 : PlayerId := ⟨0⟩
  let p1 : PlayerId := ⟨1⟩
  let gBase := mkThreePlayer27i1 2714
  -- Record `.leftGame p1` directly so `(g.player p1).leftTheGame == true` while `lost == false`:
  let gLeftOnly :=
    gBase.record (GameEvent.playerLeftGame gBase.turnNumber p1 (cause := some (.gameRule .playerLeftGame)))
  let stillInGameCheck :=
    !gLeftOnly.stillInGame p1 &&
    !gLeftOnly.livingPlayers.any (·.id == p1)
  -- `beginLibrarySearch`, `beginScry`, `beginSurveil`, `offerMaySearchBasics`, `createToken`,
  -- `createOneToken`, `makeFrc` (`.gingerbrute` when monarch), and `resolveDelayedTrigger`
  -- (`.endStepReturn` / `.endStepGraveReturn`) all no-op for `p1`:
  let sIdx := gLeftOnly.events.size
  let gSearch := gLeftOnly.beginLibrarySearch p1 isBasicLandCard "a basic land card" .hand 1
  let gScry := gLeftOnly.beginScry p1 2
  let gSurveil := gLeftOnly.beginSurveil p1 2
  let gOffer := gLeftOnly.offerMaySearchBasics p1 1
  let (gTokObjs, tokObj) := gLeftOnly.createToken p1 bear (count := 2)
  let (gOneTok, oneTokObj) := gLeftOnly.createOneToken p1 bear
  let gMonarchLeft :=
    (gBase.becomeMonarch p1).record
      (GameEvent.playerLeftGame gBase.turnNumber p1 (cause := some (.gameRule .playerLeftGame)))
  let gMakeFrc :=
    gMonarchLeft.applyAbilityEffect p1
      { body := Instruction.ifThen (.playerPred .you .isMonarch) (Instruction.createTokensFixed .gingerbrute 1) } #[] none
  let gExBear := insertObject gLeftOnly bear p1 .exile
  let exBearId := gExBear.objects.back!.id
  let gGyBear := insertObject gExBear bear p1 (.graveyard p1)
  let gyBearId := (gGyBear.player p1).graveyard.back!
  let gEndRet := gGyBear.resolveDelayedTrigger p1 (.endStepReturn exBearId) testCause none none #[]
  let gEndGyRet := gEndRet.resolveDelayedTrigger p1 (.endStepGraveReturn gyBearId p1) testCause none none #[]
  let guardsOk :=
    stillInGameCheck &&
    gSearch.events.size == sIdx && gSearch.pending == .none &&
    gScry.log == gLeftOnly.log && gScry.continuations.isEmpty && gScry.pending == .none &&
    gSurveil.log == gLeftOnly.log && gSurveil.continuations.isEmpty && gSurveil.pending == .none &&
    gOffer.events.size == sIdx && gOffer.pending == .none &&
    tokObj.id == noSourceSentinelId && gTokObjs.battlefield.size == gLeftOnly.battlefield.size &&
    oneTokObj.id == noSourceSentinelId && gOneTok.battlefield.size == gLeftOnly.battlefield.size &&
    gMakeFrc.battlefield.size == gMonarchLeft.battlefield.size &&
    (gEndGyRet.object! exBearId).zone == .exile &&
    (gEndGyRet.object! gyBearId).zone == .graveyard p1

  -- `FraChoices.answerFraChoice` stashes `g.pendingReplacement` onto `outerPendingReplacements`
  -- when accepting `.mayCastCascade`, `.mayCastGrima`, `.mayCastCopy`, `.mayCastInstantSorceryFromHand`,
  -- `.mayCastUpToFromExile`, and `.mayCastFromGraveyard`:
  let rSpellDef : CardDef := {
    name := "P27i1 Red Inst"
    manaCost := ⟨#[.colored .red]⟩
    types := #[.instant]
    additionalCosts := #[AdditionalCostSpec.mandatory CostSpec.sacrificeCreature]
    spellEffect := some { body := Instruction.gainLifeFixed 1, phrase := "You gain 1 life" }
  }
  let stashedCont : PendingReplacement := .finishPostStep (.beginScryOne p0)
  let gStash0 :=
    ((insertObject (insertObject (insertObject (addPermanent gBase bear p0 p0) rSpellDef p0 .exile) rSpellDef p0 (.hand p0))
      rSpellDef p0 (.graveyard p0)).change (.pushContinuationFrame {})).change
      (.pendingReplacement (some stashedCont))
  let exId := (gStash0.objects.filter (fun o => o.zone == .exile && o.name == rSpellDef.name))[0]!.id
  let handId := (gStash0.player p0).hand.back!
  let gyId := (gStash0.player p0).graveyard.back!
  let checkStashed (fc : FraChoice) (act : Action) : Bool :=
    let gAsk := gStash0.change (.pending (.fraChoice p0 fc))
    let gAcc := mustApply gAsk p0 act
    gAcc.pendingReplacement.isNone &&
      gAcc.outerPendingReplacements.back? == some stashedCont &&
      Game.replayEvents gAcc.events == gAcc
  let stashOk :=
    checkStashed (.mayCastCascade exId #[exId]) .accept &&
    checkStashed (.mayCastGrima exId #[] p1) .accept &&
    checkStashed (.mayCastCopy exId) .accept &&
    checkStashed (.mayCastInstantSorceryFromHand #[handId]) (.choosePermanents #[handId]) &&
    checkStashed (.mayCastUpToFromExile #[exId] 1) (.choosePermanents #[exId]) &&
    checkStashed (.mayCastFromGraveyard #[gyId]) (.choosePermanents #[gyId])

  mustHold27i1 "3a.guardsOk" guardsOk &&
  mustHold27i1 "3b.stashOk" stashOk &&
  mustHold27i1 "3.replay" (replayOk27i1 #[gLeftOnly, gEndGyRet])

end Phase27Item1EventAlignment

/-! ### Phase 27 Item 2: Slot-0 optional target entry, final-optional-slot `Action.decline`
(`GameEvent.targeted` & `prevDone`), modal triggered-ability optional modes & Layer-3 /
`eachOpponent` / `dividedDamage` helpers, CR 115.7d relational-group retargeting exemptions,
`canPayAnnouncedAdditional` `flashback` forwarding, and `enterProposalWindow` non-mana activation -/
section Phase27Item2EventAlignment

private def mustHold27i2 (label : String) (ok : Bool) : Bool :=
  if ok then true else panic! s!"Phase27Item2EventAlignment failed: {label}"

private def replayOk27i2 (gs : Array Game) : Bool :=
  gs.all (fun g => Game.replayEvents g.events == g && allRulesEventsClassified g)

-- 1. CR 115.1c–d / 601.2c / 603.2 / 700.2d / 702.21a:
--    Slot-0 optional entry in `beginResolutionCastTargets` & `afterAdditionalCostAnnounced`,
--    and `Action.decline` on final optional slot(s) recording `GameEvent.targeted` (`targetsAnnounced`)
--    and firing deferred `.ward` / `.becomesTarget` / `.youTargetSomething` triggers (`prevDone == false`).
#guard
  let p0 : PlayerId := ⟨0⟩
  let p1 : PlayerId := ⟨1⟩
  let optArtMode : Effect := {
    targeting := .of .artifact
    body := Instruction.destroy (.target 0)
    phrase := "Destroy up to one target artifact"
    allowsZeroTargets := true
  }
  let reqCreatureMode : Effect := {
    targeting := .of .creature
    body := Instruction.putPlusOne (.target 0) 1
    phrase := "Put a +1/+1 counter on target creature"
  }
  let twoModeSpellDef : CardDef := {
    name := "P27i2 Two Mode Spell"
    manaCost := ManaCost.empty
    types := #[.sorcery]
    keywords := #[.teamwork 2]
    spellEffect := some {
      body := .chooseModes {
        altCountIf? := some (.castPred (.teamworkPaid .this), .const 2, .const 2)
        modes := #[optArtMode, reqCreatureMode]
      }
    }
  }
  let wardBearDef : CardDef := {
    bear with
    name := "P27i2 Ward Bear"
    keywords := #[.ward (CostSpec.ofGeneric 1)]
    triggeredAbilities := #[TriggeredAbility.mkTrigger .thisBecomesTargetByOpponent { body := Instruction.gainLifeFixed 1 }]
  }
  let youTargetWatcherDef : CardDef := {
    name := "P27i2 Target Watcher"
    types := #[.enchantment]
    triggeredAbilities := #[SharedTrigger.watch .youTargetDrawOnce |>.toTriggeredAbility]
  }
  let g0 :=
    insertObject
      (addPermanent
        (addPermanent (emptyHand afterDraw p0) wardBearDef p1 p1)
        youTargetWatcherDef p0 p0)
      twoModeSpellDef p0 (.hand p0)
  let wardBearId := (g0.permanentsOf p1).find? (·.name == wardBearDef.name) |>.get!.id
  let spellId := (g0.player p0).hand.back!
  -- 1a. `afterAdditionalCostAnnounced` (`teamwork` choose-both with 0 artifacts on battlefield):
  --     slot 0 (`optArtMode`) is optional with 0 legal targets while slot 1 (`reqCreatureMode`) has
  --     `wardBearId`, so entering with both modes enters `.chooseTargets p0` instead of reversing!
  let gWithHelper := addPermanent g0 bear p0 p0
  let helperId := (gWithHelper.permanentsOf p0).find? (·.name == bear.name) |>.get!.id
  let gCastBoth := mustApply (mustApply (mustApply gWithHelper p0 (.cast spellId)) p0 (.chooseMode 0)) p0 (.announceTeamwork true)
  let gAfterTeamwork := mustApply gCastBoth p0 (.choosePermanents #[helperId])
  -- Slot 0 has 0 legal targets (no artifacts on battlefield), yet `gAfterTeamwork.pending == .chooseTargets p0`;
  -- `p0` declines optional slot 0, then targets `wardBearId` for mandatory slot 1!
  let gDeclSlot0 := mustApply gAfterTeamwork p0 .decline
  let gDoneBoth := mustApply gDeclSlot0 p0 (.target (.permanent wardBearId))
  let slot0EntryOk :=
    gAfterTeamwork.pending == .chooseTargets p0 &&
    gDeclSlot0.pending == .chooseTargets p0 &&
    gDoneBoth.stack.size >= 1

  -- 1b. Declining the FINAL optional slot records `GameEvent.targeted` with `targetsAnnounced == true`
  --     and fires `.ward`, `.becomesTarget`, and `.youTargetSomething` for the target chosen in slot 0!
  let reqFirstOptSecondDef : CardDef := {
    name := "P27i2 Req Then Opt"
    manaCost := ManaCost.empty
    types := #[.sorcery]
    keywords := #[.teamwork 2]
    spellEffect := some {
      body := .chooseModes {
        altCountIf? := some (.castPred (.teamworkPaid .this), .const 2, .const 2)
        modes := #[reqCreatureMode, optArtMode]
      }
    }
  }
  let g1 := insertObject gWithHelper reqFirstOptSecondDef p0 (.hand p0)
  let reqOptId := (g1.player p0).hand.back!
  let gCastRO := mustApply (mustApply (mustApply g1 p0 (.cast reqOptId)) p0 (.chooseMode 0)) p0 (.announceTeamwork true)
  let gAfterTeamRO := mustApply gCastRO p0 (.choosePermanents #[helperId])
  -- Slot 0: choose `wardBearId` (mandatory); Slot 1 (`optArtMode`) is still unchosen, so triggers wait:
  let gSlot0Chosen := mustApply gAfterTeamRO p0 (.target (.permanent wardBearId))
  let sBeforeDecl := gSlot0Chosen.events.size
  -- Slot 1: decline the final optional slot!
  let gFinalDecl := mustApply gSlot0Chosen p0 .decline
  let targetedRecorded :=
    (gFinalDecl.events.extract sBeforeDecl gFinalDecl.events.size).any fun e =>
      match e.change with
      | .rules (.cast (.targeted _ tgts _ skipped)) =>
        tgts == #[Target.permanent wardBearId] && skipped == #[1]
      | _ => false
  -- Both `.ward`, `.becomesTarget`, and `.youTargetSomething` fired (putting triggers on stack / waiting):
  let finalDeclTriggersOk :=
    targetedRecorded &&
    (gFinalDecl.stack.size + gFinalDecl.waitingTriggers.size >= 3)

  -- Also verify `beginResolutionCastTargets` allows entering `.chooseTargets` when slot 0 is optional
  -- and has 0 legal targets:
  let gExTwo := (insertObject gWithHelper { twoModeSpellDef with keywords := #[], spellEffect := some { body := .chooseModes { modes := #[optArtMode, reqCreatureMode] } } } p0 .exile).change (.pushContinuationFrame {})
  let exTwoId := gExTwo.objects.back!.id
  let gAskCasc := gExTwo.change (.pending (.fraChoice p0 (.mayCastCascade exTwoId #[])))
  let gResCast := mustApply (mustApply gAskCasc p0 .accept) p0 (.chooseMode 0)
  let gResDecl := mustApply gResCast p0 .decline
  let resCastZeroOk :=
    gResCast.pending == .chooseTargets p0 &&
    gResDecl.stack.size == 1 &&
    gResDecl.stack[0]!.targetsAnnounced

  mustHold27i2 "1a.slot0EntryOk" slot0EntryOk &&
  mustHold27i2 "1b.finalDeclTriggersOk" finalDeclTriggersOk &&
  mustHold27i2 "1c.resCastZeroOk" resCastZeroOk &&
  mustHold27i2 "1.replay" (replayOk27i2 #[gDoneBoth, gFinalDecl, gResDecl])

-- 2. CR 115.1c–d / 115.7d / 118.9a / 602.2b / 603.3c–d / 612 / 700.2 / 702.34a:
--    Modal triggered-ability optional mode `decline` & `Agent`, 2-player `eachOpponent` trigger
--    termination, `triggerModesOf` Layer-3 & `triggerModeChoosable` `eachOpponent` / `dividedDamage`,
--    CR 115.7d relational-group retargeting exemptions, `canPayAnnouncedAdditional` `flashback`
--    forwarding, and `enterProposalWindow` non-mana ability activation.
#guard
  let p0 : PlayerId := ⟨0⟩
  let p1 : PlayerId := ⟨1⟩
  -- 2a. 2-player non-modal `eachOpponent` optional trigger (`1` slot in `spec.slots`) terminates cleanly
  --     when `p0` declines slot 0 (marking `targetsAnnounced == true` instead of re-prompting!),
  --     and modal triggered ability with a single optional-target mode (`obj.triggeredAbility.isSome &&
  --     obj.abilityEffect.any (·.allowsZeroTargets)`) allows `.decline` and `Agent.choose`:
  let eachOppOptAb : TriggeredAbility := TriggeredAbility.mkTrigger .thisEnters {
    targeting := .of (.forEachOpponentControlled (.hasType .artifact) (.upTo 1))
    allowsZeroTargets := true
    body := Instruction.gainLifeFixed 1
    phrase := "For each opponent, up to one target artifact that player controls"
  }
  let eachOppPermDef : CardDef := {
    bear with
    name := "P27i2 EachOpp Trigger"
    triggeredAbilities := #[eachOppOptAb]
  }
  let artDef : CardDef := { name := "P27i2 Opp Artifact", types := #[.artifact] }
  let gEo0 := addPermanent afterDraw artDef p1 p1
  let gEo1 := insertObject gEo0 eachOppPermDef p0 (.hand p0)
  let eoHandId := (gEo1.player p0).hand.back!
  let (gEoPut, eoPermId) := gEo1.putOntoBattlefield eoHandId p0 (cause := some testCause)
  let gEoTrig := (gEoPut.afterPermanentEnters (gEoPut.object! eoPermId)).receivePriority p0
  let gEoDecl := mustApply gEoTrig p0 .decline
  let eachOppDeclineTerminatesOk :=
    gEoTrig.pending == .chooseTargets p0 &&
    gEoDecl.pending == .none &&
    gEoDecl.stack.size == 1 &&
    gEoDecl.stack[0]!.targetsAnnounced &&
    gEoDecl.stack[0]!.targets.isEmpty

  -- Modal triggered ability with `modes` where mode 0 has `allowsZeroTargets := true`:
  let modalOptMode0 : Effect := {
    targeting := .of (.ofDomain (.object .battlefield (ObjectPred.andAll #[.hasSubtype (.literal .elf), .hasType .creature])) (.upTo 1))
    allowsZeroTargets := true
    body := Instruction.putPlusOne (.target 0) 1
    phrase := "Put a +1/+1 counter on up to one target Elf"
  }
  let modalUntargetedMode1 : Effect := {
    body := Instruction.gainLifeFixed 2
    phrase := "You gain 2 life"
  }
  let modalTrigPermDef : CardDef := {
    bear with
    name := "P27i2 Modal Trigger"
    triggeredAbilities := #[
      TriggeredAbility.mkModal .thisEnters #[modalOptMode0, modalUntargetedMode1]
        (headerPhrase := "Choose one —")
    ]
  }
  let gMt0 := insertObject afterDraw modalTrigPermDef p0 (.hand p0)
  let mtHandId := (gMt0.player p0).hand.back!
  let (gMtPut, mtPermId) := gMt0.putOntoBattlefield mtHandId p0 (cause := some testCause)
  -- Layer-3 text change on `mtPermId` (`Elf` -> `Bear`) is seen by `g.triggerModesOf`
  -- AND updates canonical `ToOracle` rendering (Phase 3 retires stale `noun : String`):
  let gMtL3 :=
    gMtPut.createEffect
      (.layered (.objects #[mtPermId]) (.text (.replaceCreatureType .elf .bear)) .indefinite)
      (cause := some testCause)
  let gMtTrig := (gMtL3.afterPermanentEnters (gMtL3.object! mtPermId)).receivePriority p0
  let trigStackObj := gMtTrig.object! gMtTrig.stack[0]!.objectId
  let modesL3 := gMtTrig.triggerModesOf trigStackObj
  let triggerModesL3Ok :=
    modesL3[0]!.targetSpec ==
      .ofDomain (.object .battlefield (ObjectPred.andAll #[.hasSubtype (.literal .bear), .hasType .creature])) (.upTo 1) &&
    modesL3[0]!.targetSpec.noun == "up to one target Bear creature"
  -- Choose mode 1 (untargeted): `.triggerModes` marks `targetsAnnounced == true` immediately!
  let gMtMode1 := mustApply gMtTrig p0 (.chooseMode 1)
  let untargetedModeMarksAnnouncedOk :=
    gMtMode1.pending == .none && gMtMode1.stack[0]!.targetsAnnounced
  -- Choose mode 0 (`allowsZeroTargets := true`) when no other Bear is targeted -> `Agent.choose`
  -- or `Action.decline` declines cleanly!
  let gMtNoBearTrig := (gMtTrig.move mtPermId .exile none (cause := some testCause)).1
  let gMtMode0 := mustApply gMtNoBearTrig p0 (.chooseMode 0)
  let agentDeclinesModalOpt :=
    gMtMode0.pending == .chooseTargets p0 &&
    (match Agent.choose gMtMode0 p0 with | some .decline => true | _ => false)
  let gMtMode0Decl := mustApply gMtMode0 p0 .decline
  let modalOptDeclineOk :=
    agentDeclinesModalOpt &&
    gMtMode0Decl.pending == .none &&
    gMtMode0Decl.stack[0]!.targetsAnnounced

  -- 2b. CR 115.7d relational-group retargeting exemption in `validTargetArrayForEntry`:
  --     if group 0 (`#[0, 1]` in `constraintPosGroups`) no longer shares a card type on the board,
  --     keeping slots 0 and 1 unchanged while changing slot 2 (`#[2]`) is STILL legal under
  --     `allowUnchangedIllegal := true`!
  let relSpec : TargetSpec := TargetSpec.twoNonlandsSharingType.append .creature
  let gRel0 := addPermanent (addPermanent (addPermanent (addPermanent afterDraw bear p0 p0) artDef p0 p0) bear p1 p1) bear p1 p1
  let c0 := (gRel0.permanentsOf p0).find? (·.name == bear.name) |>.get!.id
  let a0 := (gRel0.permanentsOf p0).find? (·.name == artDef.name) |>.get!.id
  let p1Bears := (gRel0.permanentsOf p1).filter (·.name == bear.name)
  let c1 := p1Bears[0]!.id
  let c2 := p1Bears[1]!.id
  let relEntry : StackEntry := {
    objectId := c0
    controller := p0
    targets := #[.permanent c0, .permanent a0, .permanent c1]
    targetsAnnounced := true
  }
  let candidateChangedSlot2 : Array Target := #[.permanent c0, .permanent a0, .permanent c2]
  -- `c0` (creature) and `a0` (artifact) do not currently share a card type, yet slots 0 and 1
  -- are unchanged while slot 2 changes from `c1` to `c2`:
  let relRetargetOk :=
    !gRel0.validTargetArrayForEntry relEntry (gRel0.object! c0) relSpec candidateChangedSlot2 (allowUnchangedIllegal := false) &&
    gRel0.validTargetArrayForEntry relEntry (gRel0.object! c0) relSpec candidateChangedSlot2 (allowUnchangedIllegal := true)

  -- 2c. `canPayAnnouncedAdditional` `flashback := some false` forwarding and
  --     `enterProposalWindow` non-mana activated ability skipping `.activateManaAbilities`:
  let beholdFlashCard : CardDef := {
    name := "P27i2 Behold Flashback"
    manaCost := ManaCost.ofGeneric 5
    types := #[.sorcery]
    additionalCosts := #[AdditionalCostSpec.mandatory (CostSpec.beholdOrPayGeneric .dragon 2)]
    keywords := #[.flashback CostSpec.empty]
    spellEffect := some { body := Instruction.gainLifeFixed 1, phrase := "You gain 1 life" }
  }
  let gBf0 := insertObject (emptyHand afterDraw p0) beholdFlashCard p0 (.graveyard p0)
  let bfGyId := (gBf0.player p0).graveyard.back!
  -- With 0 mana and no Dragon to behold, `flashback := none` would inspect `flashback := some 0`
  -- in graveyard, whereas `flashback := some false` (`withoutPaying := false` on `.mayCastCards`)
  -- sees `{5} + {2}` and returns `false`, so `defaultFraAction` declines!
  let canPayFlashbackFalseOk :=
    !gBf0.canPayAnnouncedAdditional p0 (gBf0.object! bfGyId) (gBf0.availableMana p0) (flashback := some false) &&
    (match gBf0.defaultFraAction p0 (.mayCastCards #[bfGyId] false false) with | .decline => true | _ => false)

  -- `enterProposalWindow` for a non-mana activated ability (`tap := true, mana := empty`) after
  -- choosing a mode skips `.activateManaAbilities` and activates directly onto `.stack`:
  let modalTapArtDef : CardDef := {
    name := "P27i2 Modal Tap Relic"
    types := #[.artifact]
    activatedAbilities := #[ActivatedAbility.mkModal (CostSpec.ofItems #[.tapSelf]) #[
      { body := Instruction.gainLifeFixed 1, phrase := "You gain 1 life" },
      { body := Instruction.gainLifeFixed 2, phrase := "You gain 2 life" }
    ]]
  }
  let gTap0 := addPermanent afterDraw modalTapArtDef p0 p0
  let tapRelicId := (gTap0.permanentsOf p0).find? (·.name == modalTapArtDef.name) |>.get!.id
  let gTapAct := mustApply gTap0 p0 (.activate tapRelicId 0)
  let gTapMode := mustApply gTapAct p0 (.chooseMode 1)
  let nonManaProposalWindowOk :=
    gTapMode.pending == .none &&
    gTapMode.proposedSpell.isNone &&
    gTapMode.stack.size == 1 &&
    (gTapMode.object! tapRelicId).status.tapped

  mustHold27i2 "2a.eachOppDeclineTerminatesOk" eachOppDeclineTerminatesOk &&
  mustHold27i2 "2a.triggerModesL3AndModalOptOk" (triggerModesL3Ok && untargetedModeMarksAnnouncedOk && modalOptDeclineOk) &&
  mustHold27i2 "2b.relRetargetOk" relRetargetOk &&
  mustHold27i2 "2c.canPayFlashbackAndNonManaWindowOk" (canPayFlashbackFalseOk && nonManaProposalWindowOk) &&
  mustHold27i2 "2.replay" (replayOk27i2 #[gEoDecl, gMtMode1, gMtMode0Decl, gTapMode])

end Phase27Item2EventAlignment

/-! ### Phase 27 Item 3: CR 616.1 `affectedPlayer` stamping across 5 replacement gatherers,
pause-safe `makeFrc` / `exileTopPlayIfYouControlSubtype` / `.untapPermanent`,
LKI damage-source / power / counter / MV fallbacks, and Saga `applyChapterEffect` `sourceId` -/
section Phase27Item3EventAlignment

private def mustHold27i3 (label : String) (ok : Bool) : Bool :=
  if ok then true else panic! s!"Phase27Item3EventAlignment failed: {label}"

private def replayOk27i3 (gs : Array Game) : Bool :=
  gs.all (fun g => Game.replayEvents g.events == g && allRulesEventsClassified g)

-- 1. CR 616.1 / 616.1g:
--    `affectedPlayer` stamping across `replaceCountersPutChoice`, `gainLife`,
--    `drawOneWithReplacements`, `applyConnive`, and `replaceTokenBatchesChoice`
--    routes competing replacement choices to the affected player `p1` (even when `spec.affectedPlayer`
--    was initialized to `p0` at effect creation).
#guard
  let p0 : PlayerId := ⟨0⟩
  let p1 : PlayerId := ⟨1⟩
  let gBase := addPermanent afterDraw bear p1 p1
  let p1BearId := (gBase.permanentsOf p1).find? (·.name == bear.name) |>.get!.id
  -- 1a. `replaceCountersPutChoice` on `p1`'s permanent prompts `p1`:
  let cntAdd : ReplacementSpec := {
    id := { kind := .extraCounterOnPermanents, object := some p1BearId, counterKind := some .plusOnePlusOne }
    source := some p1BearId, controller := some p0, affectedPlayer := p0
    kind := .modifyCountersPut none (some .plusOnePlusOne) 1 1
  }
  let cntMul : ReplacementSpec := {
    id := { kind := .multiplyCountersPut, object := none, counterKind := some .plusOnePlusOne }
    source := none, controller := some p0, affectedPlayer := p0
    kind := .modifyCountersPut none (some .plusOnePlusOne) 0 2
  }
  let gCnt :=
    ((gBase.createEffect (.replacement cntAdd) (cause := some testCause)).createEffect
      (.replacement cntMul) (cause := some testCause)).addCounters
      (gBase.object! p1BearId) .plusOnePlusOne 1 (byPlayer := some p0) (cause := some testCause)
  let cntChooserOk :=
    match gCnt.pending with
    | .chooseReplacement chooser cs => chooser == p1 && cs.size == 2
    | _ => false

  -- 1b. `gainLife` for `p1` prompts `p1`:
  let lifeAdd : ReplacementSpec := {
    id := { kind := .addLifeGain, object := some p1BearId }
    source := some p1BearId, controller := some p0, affectedPlayer := p0
    kind := .modifyLifeGain p1 1 1
  }
  let lifeMul : ReplacementSpec := {
    id := { kind := .multiplyLifeGain, object := none }
    source := none, controller := some p0, affectedPlayer := p0
    kind := .modifyLifeGain p1 0 2
  }
  let gLife :=
    ((gBase.createEffect (.replacement lifeAdd) (cause := some testCause)).createEffect
      (.replacement lifeMul) (cause := some testCause)).gainLife p1 2
  let lifeChooserOk :=
    match gLife.pending with
    | .chooseReplacement chooser cs => chooser == p1 && cs.size == 2
    | _ => false

  -- 1c. `drawOneWithReplacements` for `p1` prompts `p1`:
  let drawR1 : ReplacementSpec := {
    id := { kind := .drawTwoExceptFirstDrawStep, object := some p1BearId }
    source := some p1BearId, controller := some p0, affectedPlayer := p0
    kind := .replaceDraw p1 2 false
  }
  let drawR2 : ReplacementSpec := {
    id := { kind := .drawTwoExceptFirstDrawStep, object := none }
    source := none, controller := some p0, affectedPlayer := p0
    kind := .replaceDraw p1 3 false
  }
  let gDraw :=
    ((gBase.createEffect (.replacement drawR1) (cause := some testCause)).createEffect
      (.replacement drawR2) (cause := some testCause)).draw p1 1
  let drawChooserOk :=
    match gDraw.pending with
    | .chooseReplacement chooser cs => chooser == p1 && cs.size == 2
    | _ => false

  -- 1d. `applyConnive` on `p1`'s creature prompts `p1`:
  let conAdd : ReplacementSpec := {
    id := { kind := .asEntersChooseCardNamePrompt, object := some p1BearId }
    source := some p1BearId, controller := some p0, affectedPlayer := p0
    kind := .extraDrawOnConnive p1 1
  }
  let conMul : ReplacementSpec := {
    id := { kind := .extraDrawOnConnive, object := none }
    source := none, controller := some p0, affectedPlayer := p0
    kind := .extraDrawOnConnive p1 2
  }
  let gCon :=
    ((gBase.createEffect (.replacement conAdd) (cause := some testCause)).createEffect
      (.replacement conMul) (cause := some testCause)).applyConnive p1 (some p1BearId)
  let conniveChooserOk :=
    match gCon.pending with
    | .chooseReplacement chooser cs => chooser == p1 && cs.size == 2
    | _ => false

  -- 1e. `replaceTokenBatchesChoice` for `p1` prompts `p1`:
  let tokAdd : ReplacementSpec := {
    id := { kind := .foodAlsoCreatesTreasure, object := some p1BearId }
    source := some p1BearId, controller := some p0, affectedPlayer := p0
    kind := .createExtraTokenWithFood p1 Game.treasureToken
  }
  let tokMul : ReplacementSpec := {
    id := { kind := .artifactTokensBecomeDragons, object := none }
    source := none, controller := some p0, affectedPlayer := p0
    kind := .artifactTokensBecome p1 Game.dragon55flyingToken
  }
  let (gTok, _) :=
    ((gBase.createEffect (.replacement tokAdd) (cause := some testCause)).createEffect
      (.replacement tokMul) (cause := some testCause)).createToken p1 Game.foodToken (cause := some testCause)
  let tokChooserOk :=
    match gTok.pending with
    | .chooseReplacement chooser cs => chooser == p1 && cs.size == 2
    | _ => false

  mustHold27i3 "1.affectedPlayerStampingOk"
    (cntChooserOk && lifeChooserOk && drawChooserOk && conniveChooserOk && tokChooserOk) &&
  mustHold27i3 "1.replay" (replayOk27i3 #[gCnt, gLife, gDraw, gCon, gTok])

-- 2. Pause-safe `makeFrc`, `exileTopPlayIfYouControlSubtypeLoop`, `.untapPermanent` resume checks,
--    LKI damage-source / power / counter / MV fallbacks, and Saga `applyChapterEffect` `sourceId`.
#guard
  let p0 : PlayerId := ⟨0⟩
  let p1 : PlayerId := ⟨1⟩
  let gBase := addPermanent afterDraw bear p0 p0
  let p0BearId := (gBase.permanentsOf p0).find? (·.name == bear.name) |>.get!.id

  -- 2a. `makeFrc` called while `g.pending` is already `.chooseReplacement` preserves `g.recentTokenIds`:
  let rA : ReplacementId := { kind := .tokenDoubling, object := some p0BearId }
  let rB : ReplacementId := { kind := .tokenDoubling, object := none }
  let gPausedFrc :=
    (((gBase.becomeMonarch p0).change (.pushContinuationFrame {})).change
      (.recentTokenIds #[p0BearId])).change
      (.pending (.chooseReplacement p0 #[rA, rB]))
  let gAfterMakeFrc :=
    gPausedFrc.applyAbilityEffect p0
      { body := Instruction.ifThen (.playerPred .you .isMonarch) (Instruction.createTokensFixed .gingerbrute 1) } #[] none
  let makeFrcPreservesRecentOk :=
    gAfterMakeFrc.recentTokenIds == #[p0BearId] &&
    gAfterMakeFrc.pendingReplacement.isSome

  -- 2b. `exileTopPlayIfYouControlSubtypeLoop` pauses across `Pending.chooseReplacement` after card 1's
  --     exile move, grants the face-down play permission to the post-move exile object once the
  --     replacement choice finishes, and then exiles card 2:
  let topLibId := (gBase.player p0).library.back!
  let cntAdd0 : ReplacementSpec := {
    id := { kind := .extraCounterOnPermanents, object := some p0BearId, counterKind := some .plusOnePlusOne }
    source := some p0BearId, controller := some p0, affectedPlayer := p0
    kind := .modifyCountersPut none (some .plusOnePlusOne) 1 1
  }
  let cntMul0 : ReplacementSpec := {
    id := { kind := .multiplyCountersPut, object := none, counterKind := some .plusOnePlusOne }
    source := none, controller := some p0, affectedPlayer := p0
    kind := .modifyCountersPut none (some .plusOnePlusOne) 0 2
  }
  let gExSub0 :=
    ((gBase.createEffect (.replacement cntAdd0) (cause := some testCause)).createEffect
      (.replacement cntMul0) (cause := some testCause)).change (.pushContinuationFrame {})
  let (gMoved1, _) := gExSub0.move topLibId .exile none (cause := some testCause)
  let gPausedOnCnt := gMoved1.addCounters (gMoved1.object! p0BearId) .plusOnePlusOne 1 (byPlayer := some p0) (cause := some testCause)
  let gExSubPaused := gPausedOnCnt.exileTopPlayIfYouControlSubtypeLoop p0 .elf 1 (some testCause) (some topLibId)
  let gExSubDone :=
    match gExSubPaused.pending with
    | .chooseReplacement q cs => mustApply gExSubPaused q (.chooseReplacement cs[0]!)
    | _ => gExSubPaused
  let exPerms := gExSubDone.activeEffects.filter fun (_, eff) =>
    match eff with
    | .permission (some q) (.playFromExile _ perm) _ =>
      q == p0 && perm.whileExiled && perm.requireSubtype == some .elf && perm.faceDown
    | _ => false
  let exileTopLoopOk :=
    (match gExSubPaused.pending with | .chooseReplacement .. => true | _ => false) &&
    gExSubDone.pending == .none &&
    exPerms.size == 2

  -- 2c. `Decisions.resumePendingReplacement` `.untapPermanent` respects `hostCantBecomeUntapped`:
  let gTappedBear :=
    (gBase.becomeTapped (gBase.object! p0BearId)).createEffect
      (.gameRule (.cantUntap p0BearId p0BearId) (.whileSourceOnBattlefield p0BearId)) (cause := some testCause)
  let gResumeUntap := gTappedBear.resumePendingReplacement (.untapPermanent p0BearId false true none)
  let untapGuardOk :=
    (gResumeUntap.object! p0BearId).status.tapped &&
    gResumeUntap.log.any (·.contains "can't become untapped")

  -- 2d. LKI fallbacks when source leaves before resolution:
  --     * `applyUnifiedAbility` `.addAnyColorEqualToSourcePower` uses `lastKnownPower` (`4` green mana),
  --     * `applyCreateTokens` `.alien` reads departed source's `.invasion` counters via `lastKnownCounterStatus?`,
  --     * `applyTriggeredAbility` `.cascade` reads departed spell's `manaValue` via `lastKnownBefore?`,
  --     * Saga chapter resolution via `Interpreter` forwards `(sourceId := sourceId)` so a
  --       lifelink Saga whose chapter deals damage via `Effect` credits lifelink to the Saga's controller!
  let (gDepartedBear, _) :=
    (gBase.recordPutCounters p0BearId .invasion 3 (byPlayer := some p0) (cause := some testCause)).move
      p0BearId (.graveyard p0) none (cause := some testCause)
  let gManaLki :=
    gDepartedBear.applyUnifiedAbility p0
      Effect.addAnyColorEqualToSourcePower #[] (some p0BearId) (some 4) none
  let gAlienLki :=
    (gDepartedBear.change (.pushContinuationFrame {})).applyCreateTokens p0
      (some p0BearId) #[] none .alien (.fixed 1) false .you .invasion
  let cascadeSpellDef : CardDef := {
    name := "P27i3 Cascade 3"
    manaCost := ManaCost.ofGeneric 3
    types := #[.sorcery]
  }
  let cheapInstDef : CardDef := {
    name := "P27i3 Cheap 1"
    manaCost := ManaCost.ofGeneric 1
    types := #[.instant]
    spellEffect := some { body := Instruction.gainLifeFixed 2, phrase := "You gain 2 life" }
  }
  let gCasc0 := insertObject (insertObject gBase cheapInstDef p0 (.library p0)) cascadeSpellDef p0 .stack
  let cascSpellId := (gCasc0.objects.filter (·.name == cascadeSpellDef.name))[0]!.id
  let (gCascDeparted, _) := gCasc0.move cascSpellId (.graveyard p0) none (cause := some testCause)
  let gCascResolved :=
    gCascDeparted.applyTriggeredAbility p0 (SharedTrigger.cascade.toTriggeredAbility) (some cascSpellId)
  let cascadeLkiOk :=
    match gCascResolved.pending with
    | .fraChoice q (.mayCastCascade hitId _) =>
      q == p0 && (gCascResolved.object! hitId).name == cheapInstDef.name
    | _ => false

  -- Saga `applyChapterEffect` forwarding `sourceId` on a chapter that deals damage via `Effect`:
  let llSagaDef : CardDef := {
    name := "P27i3 Lifelink Saga"
    types := #[.enchantment]
    subtypes := #["Saga"]
    keywords := #[Keyword.lifelink]
  }
  let gSaga0 := addPermanent gBase llSagaDef p0 p0
  let sagaId := (gSaga0.permanentsOf p0).find? (·.name == llSagaDef.name) |>.get!.id
  let chapterEff : Effect := Effect.dealDamage 2
  let gSagaChap := gSaga0.applyAbilityEffect p0 chapterEff #[.player p1] (some sagaId)
  let sagaSourceForwardedOk :=
    (gSagaChap.player p1).life == 18 &&
    (gSagaChap.player p0).life == 22

  -- `resolvingDamageSource?` does not widen to `currentResolvingContext?` (`maySource` / bare
  -- `resolvingContext`), while `resolvingMovedDamageSource?` and `resolvingDamageSourceEvent?`
  -- still resolve a departed `resolvingContext` source via `resolvingDepartedSourceId?`:
  let gLiveMaySrc := gBase.change (.maySource (some p0BearId))
  let gDepCtx := gDepartedBear.change (.pushContinuationFrame { resolvingContext := some (some p0BearId, p0) })
  let contextDamageSourceScopeOk :=
    gLiveMaySrc.resolvingDamageSource?.isNone &&
    gDepCtx.resolvingDamageSource?.isNone &&
    (gDepCtx.resolvingMovedDamageSource?.map (·.id)) == some p0BearId &&
    (gDepCtx.resolvingDamageSourceEvent?.bind (·.id)) == some p0BearId

  mustHold27i3 "2a.makeFrcPreservesRecentOk" makeFrcPreservesRecentOk &&
  mustHold27i3 "2b.exileTopLoopOk" exileTopLoopOk &&
  mustHold27i3 "2c.untapGuardOk" untapGuardOk &&
  mustHold27i3 "2d.manaLkiOk" ((gManaLki.player p0).manaPool.green == 4) &&
  mustHold27i3 "2d.alienLkiOk" (gAlienLki.notedCountThisWay == 3 && !gAlienLki.createdTokensThisWay.isEmpty) &&
  mustHold27i3 "2d.cascadeLkiOk" cascadeLkiOk &&
  mustHold27i3 "2d.sagaSourceForwardedOk" (sagaSourceForwardedOk && contextDamageSourceScopeOk) &&
  mustHold27i3 "2.replay"
    (replayOk27i3 #[gExSubPaused, gExSubDone, gResumeUntap, gManaLki, gAlienLki, gCascResolved, gSagaChap])

end Phase27Item3EventAlignment

/-! ### Phase 27 Item 4: 2HG & multiplayer combat `Event.matchesTrigger` / `Core.matchTriggers`,
`Turns.lean` `.legendRuleOffThisTurn` / `.playFromExile` / `.declareBlockers`,
remaining `g.name` reads, and dead-helper retirement -/
section Phase27Item4EventAlignment

private def mustHold27i4 (label : String) (ok : Bool) : Bool :=
  if ok then true else panic! s!"Phase27Item4EventAlignment failed: {label}"

private def replayOk27i4 (gs : Array Game) : Bool :=
  gs.all (fun g => Game.replayEvents g.events == g && allRulesEventsClassified g)

-- 1. CR 506.4c / 508.1 / 800.4i / 805.4a / 805.10:
--    2HG combat `Event.matchesTrigger` & `Core.matchTriggers` per-attacker (`attCtrl`) and
--    controller-scoped (`mAttackers`) triggers across teammates `⟨0⟩` and `⟨1⟩`, single-defender
--    `.creatureAttacksYouOrYourPlaneswalker` (CR 805.10b,e), and `Turns.lean`
--    `.legendRuleOffThisTurn` / `.playFromExile` / `.declareBlockers`.
#guard
  let p0 : PlayerId := ⟨0⟩
  let p1 : PlayerId := ⟨1⟩
  let p2 : PlayerId := ⟨2⟩
  let p3 : PlayerId := ⟨3⟩
  let g2hg := mkTwoHeadedGiant27i4 2741
  let elfAtkWatcherDef : CardDef := {
    name := "P27i4 Elf Watcher"
    types := #[.enchantment]
    triggeredAbilities := #[
      TriggeredAbility.mkTrigger .youAttack { body := Instruction.gainLifeFixed 1 } (grouping := .oncePerBatch),
      TriggeredAbility.mkTrigger (.youAttackWithSubtype .elf) { body := Instruction.gainLifeFixed 1 } (grouping := .oncePerBatch),
      TriggeredAbility.mkTrigger .creatureYouControlAttacks { body := Instruction.gainLifeFixed 1 }
    ]
  }
  let defWatcherDef (nm : String) : CardDef := {
    name := nm
    types := #[.enchantment]
    triggeredAbilities := #[
      TriggeredAbility.mkTrigger .creatureAttacksYouOrYourPlaneswalker { body := Instruction.gainLifeFixed 1 }
    ]
  }
  let elfCreatureDef : CardDef := {
    bear with
    name := "P27i4 Teammate Elf"
    subtypes := #["Elf"]
    triggeredAbilities := #[TriggeredAbility.mkTrigger .thisAttacks { body := Instruction.gainLifeFixed 1 }]
  }
  -- Teammate `p1` controls `elfAtkWatcherDef` and `elfCreatureDef`; defending team members `p2`
  -- and `p3` each control a `defWatcherDef`:
  let gCombat0 :=
    addPermanent
      (addPermanent
        (addPermanent
          (addPermanent g2hg elfAtkWatcherDef p1 p1)
          elfCreatureDef p1 p1)
        (defWatcherDef "Def2") p2 p2)
      (defWatcherDef "Def3") p3 p3
  let p1ElfId := (gCombat0.permanentsOf p1).find? (·.name == elfCreatureDef.name) |>.get!.id
  -- `activePlayer` is `p0`, and `p1`'s creature `p1ElfId` is declared attacking `p2` in the shared
  -- `attackersDeclared p0` event:
  let gAtk :=
    ((gCombat0.change (.waitingTriggers #[])).record
      (GameEvent.attackersDeclared gCombat0.turnNumber p0 #[
        (gCombat0.snapshot (gCombat0.object! p1ElfId), .player p2)
      ]))
  let p1AttackTriggersFired :=
    gAtk.waitingTriggers.any (fun w => w.controller == p1 && w.pattern == .thisAttacks) &&
    gAtk.waitingTriggers.any (fun w => w.controller == p1 && w.pattern == .youAttack && w.ability.grouping == .oncePerBatch) &&
    gAtk.waitingTriggers.any (fun w => w.controller == p1 && w.pattern == .youAttackWithSubtype .elf) &&
    gAtk.waitingTriggers.any (fun w => w.controller == p1 && w.pattern == .creatureYouControlAttacks && w.ability.grouping == .perOccurrence)
  -- `.creatureAttacksYouOrYourPlaneswalker` queues for the attacked player `p2` ONLY, not `p3` (CR 805.10e):
  let singleDefenderTriggerOk :=
    gAtk.waitingTriggers.any (fun w => w.controller == p2 && w.pattern == .creatureAttacksYouOrYourPlaneswalker) &&
    !gAtk.waitingTriggers.any (fun w => w.controller == p3 && w.pattern == .creatureAttacksYouOrYourPlaneswalker)

  -- `Turns.lean`:
  --  * `.legendRuleOffThisTurn p2` is preserved by `clearTurnActivations` / `clearEOT` when `p2.lost`
  --    (CR 800.4i) and expired by `expireUntilNextTurnEffects p2`,
  --  * `startNextTurnCore` expires non-active living player `p3`'s `.playFromExile _ .untilEndOfTurn`
  --    permission at the end of the turn:
  let gTurns0 :=
    insertObject
      (g2hg.createEffect (.legendRuleOffThisTurn p2) (cause := some testCause))
      bear p2 .exile
  let exCardId := gTurns0.objects.back!.id
  let gTurns1 :=
    (gTurns0.createEffect
      (.permission (some p2) (.playFromExile exCardId { player := p2 }) .untilEndOfTurn)
      (cause := some testCause)).createEffect
      (.permission (some p3) (.playFromExile exCardId { player := p3 }) .untilEndOfTurn)
      (cause := some testCause)
  -- Mark `p2` as lost and advance to `p1` (final seat of Team A's shared turn):
  let gP2Lost :=
    (gTurns1.record (GameEvent.playerLost gTurns1.turnNumber p2 .lifeZeroOrLess (cause := some (.stateBased .lifeZeroOrLess)))).startNextTurnCore false
  -- At the end of `p1`'s seat (`isSharedTurnFinalSeat == true`), `clearEOT` keeps `p2`'s
  -- `.legendRuleOffThisTurn p2` (since `p2.lost == true` per CR 800.4i), while `startNextTurnCore`
  -- expires living non-active `p3`'s `.playFromExile _ .untilEndOfTurn` and then
  -- `expireUntilNextTurnEffects p2` expires `p2`'s `.legendRuleOffThisTurn p2`:
  let gAfterClearEot := gP2Lost.clearEOT
  let legendKeptAcrossClearEot :=
    gAfterClearEot.hasActiveEffect (.legendRuleOffThisTurn p2)
  let gNextTurn := gP2Lost.startNextTurnCore false
  let legendExpiredAndNonActivePermExpired :=
    !gNextTurn.hasActiveEffect (.legendRuleOffThisTurn p2) &&
    !gNextTurn.activeEffects.any (fun (_, eff) =>
      match eff with
      | .permission (some q) (.playFromExile _ _) .untilEndOfTurn => q == p3
      | _ => false)

  mustHold27i4 "1a.twoHgCombatTriggersOk" (p1AttackTriggersFired && singleDefenderTriggerOk) &&
  mustHold27i4 "1b.turnsLegendAndPlayFromExileOk" (legendKeptAcrossClearEot && legendExpiredAndNonActivePermExpired) &&
  mustHold27i4 "1.replay" (replayOk27i4 #[gAtk, gAfterClearEot, gNextTurn])

end Phase27Item4EventAlignment

/-! ### Phase 28 Item 1: Multi-departure `pendingIn` forwarding (`concedePlayersLoop` /
`leavePlayersWhoLostCore`), `checkSBACountedWithLeaves` deferred `restoreSavedPostLeave`,
unified `.restorePending` / `replacementChoiceValid`, and `Leaving` / `Movement` / `Core`
batch-cause & `.pending` hygiene -/
section Phase28Item1EventAlignment

private def mustHold28i1 (label : String) (ok : Bool) : Bool :=
  if ok then true else panic! s!"Phase28Item1EventAlignment failed: {label}"

private def replayOk28i1 (gs : Array Game) : Bool :=
  gs.all (fun g => Game.replayEvents g.events == g && allRulesEventsClassified g)

-- 1. Multi-departure `pendingIn` forwarding in `leavePlayersWhoLost` and `concedePlayersLoop`,
--    `checkSBACountedWithLeaves` deferred `restoreSavedPostLeave`, and unified `.restorePending` /
--    `replacementChoiceValid` revalidation (CR 608.2c / 616.1 / 704.3–4 / 800.4a / 810.8a).
#guard
  let p0 : PlayerId := ⟨0⟩
  let p1 : PlayerId := ⟨1⟩
  let p2 : PlayerId := ⟨2⟩
  let g3 := mkThreePlayer27i1 2811

  -- 1a. Multi-departure `pendingIn` forwarding in `leavePlayersWhoLost`:
  --     Both `p1` and `p2` have lost (`lost == true, leftTheGame == false`), and `g.pending` is
  --     `.chooseDiscardCard p1 #[p2]` with 1 card in each of `p1`'s and `p2`'s hands.
  --     `p1`'s departure redirects `.chooseDiscardCard p1 #[p2]` to `.chooseDiscardCard p2 #[]`
  --     in `saved?`; `leavePlayersWhoLostCore` forwards `pendingIn := saved?` into `p2`'s
  --     departure, which redirects `.chooseDiscardCard p2 #[]` through `continueAfterDiscard`
  --     so `g.pending == .none` after both depart!
  let gLostBoth0 :=
    ((insertObject (insertObject (g3.change (.pushContinuationFrame { discardCountPerPlayer := 1 })) bear p1 (.hand p1))
      bear p2 (.hand p2)).record
      (GameEvent.playerLost g3.turnNumber p1 .lifeZeroOrLess (cause := some (.stateBased .lifeZeroOrLess)))).record
      (GameEvent.playerLost g3.turnNumber p2 .lifeZeroOrLess (cause := some (.stateBased .lifeZeroOrLess)))
  let gLostBoth1 := gLostBoth0.change (.pending (.chooseDiscardCard p1 #[p2]))
  let gAfterBothLostLeave := gLostBoth1.leavePlayersWhoLost
  let multiLostPendingInOk :=
    (gAfterBothLostLeave.player p1).leftTheGame &&
    (gAfterBothLostLeave.player p2).leftTheGame &&
    gAfterBothLostLeave.pending == .none

  -- 1b. Multi-departure `pendingIn` forwarding in 6-seat (3-team) 2HG `concedePlayersLoop`:
  --     Teammates `⟨0⟩` and `⟨1⟩` have `.chooseDiscardCard ⟨0⟩ #[⟨1⟩, ⟨2⟩]` active when `⟨0⟩`
  --     concedes (`mustApply _ ⟨0⟩ .concede`). `⟨0⟩`'s departure hands `.chooseDiscardCard` off
  --     to `⟨1⟩` in `saved?`, and `concedePlayersLoop` forwards `pendingIn := saved?` to `⟨1⟩`'s
  --     departure, which hands `.chooseDiscardCard` off to surviving opponent `⟨2⟩`!
  let p3 : PlayerId := ⟨3⟩
  let g2hg := mkSixSeatThreeTeams26i1 2812
  let g2hgDisc0 :=
    (insertObject (insertObject (insertObject (g2hg.change (.pushContinuationFrame { discardCountPerPlayer := 1 }))
      bear p0 (.hand p0)) bear p1 (.hand p1)) bear p2 (.hand p2)).change
      (.pending (.chooseDiscardCard p0 #[p1, p2]))
  let g2hgAfterConcede := mustApply g2hgDisc0 p0 .concede
  let twoHgConcedePendingInOk :=
    (g2hgAfterConcede.player p0).leftTheGame &&
    (g2hgAfterConcede.player p1).leftTheGame &&
    (g2hgAfterConcede.stillInGame p2) &&
    (g2hgAfterConcede.stillInGame p3) &&
    g2hgAfterConcede.pending == .chooseDiscardCard p2 #[]

  -- 1c. `replacementChoiceValid`, `.restorePending` (`resumePoppedIfNoPrompt`), and
  --     `checkSBACountedWithLeaves` deferred `restoreSavedPostLeave`:
  let gBase := addPermanent g3 bear p0 p0
  let p0BearId := (gBase.permanentsOf p0).find? (·.name == bear.name) |>.get!.id
  let missingId : ObjectId := ⟨999999⟩
  let rDrawValid : ReplacementId := { kind := .drawTwoExceptFirstDrawStep, object := some p0BearId }
  let rConniveValid : ReplacementId := { kind := .extraDrawOnConnive, object := none }
  let rColorValid : ReplacementId := { kind := .asEntersChooseColor .red, object := some p0BearId }
  let rColorStale : ReplacementId := { kind := .asEntersChooseColor .red, object := some missingId }
  let rCopyValid : ReplacementId := { kind := .entersAsCopyCreatureUntilEot p0BearId, object := some p0BearId }
  let rCopyStale : ReplacementId := { kind := .entersAsCopyCreatureUntilEot missingId, object := some p0BearId }
  let rDrawSpec : ReplacementSpec := {
    id := rDrawValid
    source := some p0BearId, controller := some p0, affectedPlayer := p0
    kind := .replaceDraw p0 2 false
  }
  let gWithDrawSpec := gBase.createEffect (.replacement rDrawSpec) (cause := some testCause)
  let replacementChoiceValidOk :=
    gWithDrawSpec.replacementChoiceValid p0 #[rDrawValid] &&
    gWithDrawSpec.replacementChoiceValid p0 #[rConniveValid] &&
    gWithDrawSpec.replacementChoiceValid p0 #[rColorValid] &&
    gWithDrawSpec.replacementChoiceValid p0 #[rCopyValid] &&
    !gWithDrawSpec.replacementChoiceValid p0 #[rColorStale] &&
    !gWithDrawSpec.replacementChoiceValid p0 #[rCopyStale]

  -- When `.restorePending (.chooseReplacement p0 #[rColorStale]) true` runs and all choices are
  -- filtered out (`valid.isEmpty`), or when `.restorePending (.sacrificePermanent p1 none) true`
  -- runs with `g.proposedSpell.isNone` and no legal sacrifice candidates, `resumePoppedIfNoPrompt`
  -- pops `outerPendingReplacements` and immediately executes the popped continuation
  -- (`.finishPostStep (.beginScryOne p0)`):
  let gRestorePopped0 :=
    ((gWithDrawSpec.change (.pushContinuationFrame {})).change
      (.pushOuterPendingReplacement (.finishPostStep (.beginScryOne p0)))).resumePendingReplacement
      (.restorePending (.chooseReplacement p0 #[rColorStale]) true)
  let gRestoreCostNoProp :=
    ((gWithDrawSpec.change (.pushContinuationFrame {})).change
      (.pushOuterPendingReplacement (.finishPostStep (.beginScryOne p0)))).resumePendingReplacement
      (.restorePending (.sacrificePermanent p1 p0BearId) true)
  let restorePoppedImmediateOk :=
    gRestorePopped0.outerPendingReplacements.isEmpty &&
    gRestorePopped0.pending == .scry p0 1 &&
    gRestoreCostNoProp.outerPendingReplacements.isEmpty &&
    gRestoreCostNoProp.pendingReplacement.isNone &&
    gRestoreCostNoProp.pending == .scry p0 1

  -- When `checkSBACountedWithLeaves` causes `p1` (at 0 life) to lose and leave while `p0` had
  -- `.scry p0 1` saved in `savedIn`, it defers `restoreSavedPostLeave` until the end of the SBA fixpoint:
  let gSbaDefer0 :=
    (gWithDrawSpec.change (.pushContinuationFrame {})).loseLife p1 20 (cause := some testCause)
  let (gSbaDefer1, _, _) := gSbaDefer0.checkSBACountedWithLeaves (some (.scry p0 1)) false
  let sbaDeferredRestoreOk :=
    (gSbaDefer1.player p1).leftTheGame &&
    gSbaDefer1.pending == .scry p0 1

  mustHold28i1 "1a.multiLostPendingInOk" multiLostPendingInOk &&
  mustHold28i1 "1b.twoHgConcedePendingInOk" twoHgConcedePendingInOk &&
  mustHold28i1 "1c.replacementChoiceValidOk" replacementChoiceValidOk &&
  mustHold28i1 "1c.restorePoppedImmediateOk" restorePoppedImmediateOk &&
  mustHold28i1 "1c.sbaDeferredRestoreOk" sbaDeferredRestoreOk &&
  mustHold28i1 "1.replay" (replayOk28i1 #[gAfterBothLostLeave, g2hgAfterConcede, gRestorePopped0, gRestoreCostNoProp, gSbaDefer1])

-- 2. `Leaving.redirectPendingAfterLeave` (`.chooseDiscardCard`, `.mayCastGrima`),
--    `orderBottomInCleanup`, `Decisions` `.orderInto` (`moveIdsInOrder`), `Movement.finishChosenSacrifices`,
--    and `Core.applyBlackGateUnblockable` batch-cause & `.pending` hygiene.
#guard
  let p0 : PlayerId := ⟨0⟩
  let p1 : PlayerId := ⟨1⟩
  let g3 := mkThreePlayer27i1 2815

  -- 2a. `redirectPendingAfterLeave` `.chooseDiscardCard p1 #[]` clears `g.pending` to `.none`
  --     before calling `continueAfterDiscard`, so a follow-up continuation (`pendingReplacement :=
  --     some (.finishPostStep (.beginScryOne p0))`) opens `.scry p0 1` without being clobbered:
  let gDiscLast0 :=
    ((insertObject g3 bear p1 (.hand p1)).change
      (.pushContinuationFrame {
        discardCountPerPlayer := 1
        pendingReplacement := some (.finishPostStep (.beginScryOne p0))
      })).change (.pending (.chooseDiscardCard p1 #[]))
  let gDiscLastAfterLeave := gDiscLast0.playerLeavesGame p1
  let discLastContOk :=
    (gDiscLastAfterLeave.player p1).leftTheGame &&
    gDiscLastAfterLeave.pending == .scry p0 1

  -- 2b. `redirectPendingAfterLeave` `.mayCastGrima`: when `p1` leaves while prompted with
  --     `.fraChoice p1 (.mayCastGrima cardId #[ex1, ex2] p0)`, the exiled cards open
  --     `.resolveRandom (.orderInto #[ex1, ex2, grimaCardId] (.library p0) (some testCause))`:
  let gGrimaHand :=
    insertObject (insertObject (insertObject g3 bear p0 (.hand p0)) bear p0 (.hand p0)) bear p0 (.hand p0)
  let hIds := (gGrimaHand.player p0).hand
  let (gGrimaM1, grimaCardId) := gGrimaHand.move hIds[0]! .exile none (cause := some testCause)
  let (gGrimaM2, ex1) := gGrimaM1.move hIds[1]! .exile none (cause := some testCause)
  let (gGrima0, ex2) := gGrimaM2.move hIds[2]! .exile none (cause := some testCause)
  let gGrima1 :=
    (gGrima0.change (.pushContinuationFrame {})).change
      (.pending (.fraChoice p1 (.mayCastGrima grimaCardId #[ex1, ex2] p0)))
  let gGrimaAfterLeave := gGrima1.playerLeavesGame p1
  let grimaOrderRandomOk :=
    gGrimaAfterLeave.pending ==
      .resolveRandom (.orderInto #[ex1, ex2, grimaCardId] (.library p0) (some testCause))

  -- 2c. `orderBottomInCleanup`:
  --     * When `p1` leaves with `wasAbortedProposal == true`, `postCastCleanup := some (.cascadeBottom p0 ex1 #[ex2])`,
  --       and `g.pending == .activateManaAbilities p1` (`curPending == .none`), `orderBottomInCleanup`
  --       opens `.resolveRandom (.orderInto #[ex2, ex1] (.library p0) (some testCause))`:
  let gOrdClean0 := insertObject gGrima0 bear p1 (.hand p1)
  let p1HandId := (gOrdClean0.player p1).hand.back!
  let propP1 : ProposedSpell := {
    caster := p1, cost := default, spellId := p1HandId, original := gOrdClean0.object! p1HandId
  }
  let gOrdClean1 :=
    (gOrdClean0.change (.pushContinuationFrame {})).changes #[
      .pending (.activateManaAbilities p1),
      .proposedSpell (some propP1),
      .postCastCleanup (some (.cascadeBottom p0 ex1 #[ex2]))
    ]
  let gOrdCleanAfterLeave := gOrdClean1.playerLeavesGame p1
  let orderBottomCleanupOk :=
    gOrdCleanAfterLeave.pending ==
      .resolveRandom (.orderInto #[ex2, ex1] (.library p0) (some testCause))

  -- 2d. `supplyOrder` on `.orderInto #[ex2, ex1] (.library p0) (some testCause)` batches both
  --     `.moved` events under one `BatchId` with `cause == some testCause`:
  let preSupplyEvCount := gOrdCleanAfterLeave.events.size
  let gLookedResolved :=
    match gOrdCleanAfterLeave.supplyOrder #[ex2, ex1] with
    | .ok g' => g'
    | .error e => panic! e
  let movedBottomEvents := (gLookedResolved.events.extract preSupplyEvCount gLookedResolved.events.size).filter fun ev =>
    match ev with
    | .rules _ (.zone (.moved _ _ .exile (.library _) ..)) _ _ => true
    | _ => false
  let lookedBottomBatchOk :=
    movedBottomEvents.size == 2 &&
    match movedBottomEvents[0]!, movedBottomEvents[1]! with
    | .rules _ _ c1 b1, .rules _ _ c2 b2 =>
      b1.isSome && b1 == b2 && c1 == testCause && c2 == testCause
    | _, _ => false

  -- 2e. `Movement.finishChosenSacrifices`: when `g.pending == .none` before calling
  --     `finishChosenSacrifices`, it does not emit a redundant `.engine _ (.pending .none)` event:
  let gSac0 := addPermanent afterDraw bear p0 p0
  let sacBearId := (gSac0.permanentsOf p0).find? (·.name == bear.name) |>.get!.id
  let preEvCount := gSac0.events.size
  let gSacDone := gSac0.finishChosenSacrifices #[sacBearId]
  let noRedundantPendingNoneOk :=
    gSacDone.pending == .none &&
    !(gSacDone.events.extract preEvCount gSacDone.events.size).any (fun ev =>
      ev == .engine gSacDone.turnNumber (.pending .none) none)

  -- 2f. `Core.applyBlackGateUnblockable` stamps `cause := some effCause` from `allocDelayedCause`:
  let gBg0 :=
    (gSac0.change (.pushContinuationFrame { resolvingContext := some (some sacBearId, p0) })).applyBlackGateUnblockable
      sacBearId p1
  let bgCauseOk :=
    gBg0.events.any fun ev =>
      match ev with
      | .rules _ (.continuousEffect (.created _ (.cantBeBlockedByPlayerUntilEot _ _))) (.oneShotEffect _ src ctrl) _ =>
        src == some sacBearId && ctrl == some p0
      | _ => false

  mustHold28i1 "2a.discLastContOk" discLastContOk &&
  mustHold28i1 "2b.grimaOrderRandomOk" grimaOrderRandomOk &&
  mustHold28i1 "2c.orderBottomCleanupOk" orderBottomCleanupOk &&
  mustHold28i1 "2d.lookedBottomBatchOk" lookedBottomBatchOk &&
  mustHold28i1 "2e.noRedundantPendingNoneOk" noRedundantPendingNoneOk &&
  mustHold28i1 "2f.bgCauseOk" bgCauseOk &&
  mustHold28i1 "2.replay"
    (replayOk28i1 #[gDiscLastAfterLeave, gGrimaAfterLeave, gOrdCleanAfterLeave, gLookedResolved, gSacDone, gBg0])

end Phase28Item1EventAlignment

end Mtg.Engine.EventTests
