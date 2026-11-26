import Mtg.Engine.Game.Mulligans

/-!
# Decision handlers

Handlers for `Pending` decisions: finishing scry and surveil, discarding, paying
generic costs, library-side and permanent choices, declining, keeping
the opening hand, the legend rule, ordering triggers, taking mulligans,
and supplying outside randomness.
-/

namespace Mtg.Engine
namespace Game

/-- Exile each remaining graveyard card in `remainingIds` to pay Baron Helmut
Zemo's boast cost inside the caller's batch, pausing and chaining
`.finishPostStep .exileZemoBoastCards` if a CR 616.1 replacement choice opens. -/
def exileZemoBoastCards (g : Game) (p : PlayerId) (abilityId : ObjectId)
    (remainingIds : Array ObjectId) : Game := Id.run do
  let cause := some (EventCause.costPayment .exile p (some abilityId))
  let mut g := g
  for i in [0:remainingIds.size] do
    let id := remainingIds[i]!
    if (g.player p).graveyard.contains id then
      let (g', _) := g.move id .exile none (actor := some p) (cause := cause)
      g := g'
      if let .chooseReplacement .. := g.pending then
        let rem := remainingIds.extract (i + 1) remainingIds.size
        if !rem.isEmpty then
          g := g.chainPendingReplacement
            (.finishPostStep (.exileZemoBoastCards p abilityId rem))
        return g
  return g

/-- CR 103.3: shuffle remaining libraries, then draw opening hands. -/
partial def continueOpeningShuffles (g : Game) (next : Nat) : Game :=
  if next >= g.players.size then
    Id.run do
      let mut g := g.changes #[.pregameRandom .none, .pending .none]
      for pl in g.players do
        if g.stillInGame pl.id then
          g := g.draw pl.id (g.player pl.id).startingHandSize
            (cause := some (.gameRule .openingHandDraw))
      return g.beginMulliganRound
  else
    let p : PlayerId := ⟨next⟩
    if !g.stillInGame p then
      continueOpeningShuffles g (next + 1)
    else
      let g := (g.change (.pregameRandom (.openingShuffles (next + 1)))).shuffleLibrary p
      match g.pendingRandom? with
      | some _ => g
      | none =>
        let g := g.change (.pregameRandom .none)
        continueOpeningShuffles g (next + 1)

/-- Pop any trailing empty `ContinuationFrame` (`f == {}`, such as one pushed by
`promptChooseReplacement` or left after an aborted proposal) when no pending
decision, replacement continuation, or suspended interpreter wait is active
(CR 800.4a / 800.4i). -/
def popEmptyContinuationFrames (g : Game) : Game := Id.run do
  let mut g := g
  while g.pending == .none && g.pendingReplacement.isNone &&
      g.outerPendingReplacements.isEmpty && g.currentInterpWait?.isNone do
    match g.continuations.back? with
    | some f =>
      if f == {} then
        g := g.change .popContinuationFrame
      else
        break
    | none => break
  return g

/-- Pop any trailing empty `ContinuationFrame {}` on top of `g.continuations`
right before resuming a `PendingReplacement` continuation (CR 616.1 / 800.4a). -/
def popEmptyTopContinuationFrames (g : Game) : Game := Id.run do
  let mut g := g
  while g.continuations.back? == some {} do
    g := g.change .popContinuationFrame
  return g

/-- Whether a proposal-cost `Pending` prompt for `caster` still belongs to an
active `g.proposedSpell` of `caster` and still has enough live candidates to be
payable (CR 601.2f–h / 602.2b / 733.1 / 800.4a). -/
@[export mtg_game_proposal_cost_prompt_still_payable]
def proposalCostPromptStillPayable (g : Game) (caster : PlayerId) (p : Pending) : Bool :=
  !g.over && g.stillInGame caster &&
    match g.proposedSpell with
    | none => false
    | some prop =>
      prop.caster == caster &&
        (g.findObject? prop.spellId).any (fun o =>
          if prop.kind == .turnFaceUp then o.isOnBattlefield else o.zone == .stack) &&
        (prop.kind == .activatedAbility || g.sourceStillPayable prop) &&
        match p with
        | .resolutionChoice q (.costPicks sid picks _) =>
          let sacSrc :=
            prop.sacrificeSource ||
              prop.activation.any (fun a => a.cost.sacrificeSource || a.cost.exileSourceFromBattlefield)
          let discSrc :=
            prop.discardSource ||
              prop.activation.any (fun a => a.cost.discardSource || a.cost.exileSourceFromHand)
          let allPicks := costPicksWithSacrificeOther picks prop.needsSacrificeOther
          q == caster && g.sourceStillPayable prop && g.canPayLife caster prop.payLife &&
            (allPicks.isEmpty ||
              g.costPicksPayable caster (some sid) allPicks
                (tapSource := prop.tapSource)
                (sacrificeOrExileSource := sacSrc)
                (discardOrExileHandSource := discSrc))
        | .resolutionChoice q (.crew _ vehicleId n) =>
          let sacSrc :=
            prop.sacrificeSource ||
              prop.activation.any (fun a => a.cost.sacrificeSource || a.cost.exileSourceFromBattlefield)
          let discSrc :=
            prop.discardSource ||
              prop.activation.any (fun a => a.cost.discardSource || a.cost.exileSourceFromHand)
          let allPicks :=
            costPicksWithSacrificeOther ((prop.activation.map costPicksOf).getD #[])
              prop.needsSacrificeOther
          q == caster && g.sourceStillPayable prop && g.canPayLife caster prop.payLife &&
            (g.firstPayableCrewSelection? caster vehicleId n allPicks
              (tapSource := prop.tapSource)
              (sacrificeOrExileSource := sacSrc)
              (discardOrExileHandSource := discSrc)).isSome
        | .resolutionChoice q (.zemoBoastExile _ sourceId) =>
          q == caster && g.sourceStillPayable prop && g.canPayLife caster prop.payLife &&
            let col :=
              match g.findObject? sourceId <|> some prop.original with
              | some src => TextChange.applyColor (g.evalLayer3 src) .black
              | none => .black
            let allCands := (g.player caster).graveyard.filter (fun id =>
              (g.findObject? id).any (fun card => isDiscardableCard card && (g.colors card).contains col))
            g.canPayZemoBoast caster allCands col
        | .chooseTeamworkCreatures q need =>
          q == caster && g.canPayLife caster prop.payLife &&
            ((g.creaturesControlledBy caster).filter (fun c =>
              !c.status.tapped && g.power c > 0)).foldl
              (fun acc c => acc + g.power c) 0 ≥ (need : Int)
        | .sacrificePermanent q excludeId =>
          let loyaltyOk :=
            if prop.kind != .activatedAbility then true
            else
              let x := ((g.findObject? prop.spellId).bind (·.chosenX)).getD 0
              match prop.activation.bind (·.cost.netLoyaltyDelta x) with
              | none => true
              | some k =>
                prop.loyaltyPaid ||
                  g.sourceCounterCostPaidFor excludeId (some prop.spellId) .loyalty
                    (some .loyalty) ((g.targetProposalCheckpoint?.map (·.eventsSize)).getD 0) ||
                  (g.findObject? excludeId).any (fun src =>
                    src.isOnBattlefield && g.controlledBy src caster &&
                      !g.loyaltyActivatedThisTurn src.id &&
                      (k ≥ 0 || (src.status.loyaltyCounters : Int) ≥ -k))
          q == caster && loyaltyOk && !(g.sacrificeCreatureOrArtifactChoices caster excludeId).isEmpty
        | .discardForAdditionalCost q =>
          q == caster && !(g.discardableHandIds caster).isEmpty
        | _ => false

/-- Resolve a `ReplacementId` for heuristic/idle agents and step probes,
filling in open-ended `*Prompt` replacement kinds with a legal creature type
or nonland card name. -/
def defaultReplacementId (g : Game) (p : PlayerId) (choices : Array ReplacementId)
    (payLifeIfSafe : Bool := false) : Option ReplacementId :=
  let base? :=
    (if payLifeIfSafe then
      choices.find? (fun c =>
        match c.kind with
        | .entersUntappedPayLife n => (g.player p).life > (n : Int)
        | _ => false)
     else none)
    |>.orElse (fun _ =>
      choices.find? (fun c =>
        match c.kind with
        | .entersTappedDeclinePayLife | .entersTappedDeclineBehold | .declineEntersAsCopy => true
        | _ => false))
    |>.orElse (fun _ => choices[0]?)
  base?.map fun c =>
    match c.kind with
    | .asEntersChooseCreatureTypePrompt =>
      let yours :=
        (g.permanentsOf p).foldl (fun acc o =>
          (g.subtypes o).foldl (fun acc s =>
            if s.isCreatureType && !acc.contains s then acc.push s else acc) acc) #[]
      { c with kind := .asEntersChooseCreatureType (yours[0]?.getD .human) }
    | .asEntersChooseCardNamePrompt =>
      let opp := g.objects.find? (fun o => o.owner != p && !g.isLand o)
      let any := g.knownCardFaces.find? (fun card => !card.isLand)
      let nm := (opp.map (·.name)).getD ((any.map (·.name)).getD "Grizzly Bears")
      { c with kind := .asEntersChooseCardName nm }
    | _ => c

private def recordProbeFirstReplacement (g : Game) : Game :=
  match g.pending with
  | .chooseReplacement q choices =>
    match g.defaultReplacementId q choices with
    | some chosen =>
      let order := (g.replacementOrder.filter (· != chosen)).push chosen
      if order == g.replacementOrder then g
      else g.change (.replacementOrder order)
    | none => g
  | .chooseLegend _ _ ids =>
    (ids.extract 1 ids.size).foldl (fun acc id =>
      match acc.findObject? id with
      | some o =>
        if o.isOnBattlefield then
          (acc.move id (.graveyard o.owner) none (cause := some (.stateBased .legendRule))
            (suppressInteractive := true)).1
        else acc
      | none => acc) g
  | _ => g

private def clearProbeReplacement (g : Game) : Game :=
  match g.pending with
  | .chooseReplacement .. => (recordProbeFirstReplacement g).change (.pending .none)
  | _ => g

mutual
private partial def drainProbeNonPriorityCont (g : Game) : PendingReplacement → Game
  | .seq a b =>
    let g := drainProbeNonPriorityCont g a
    if g.over then g
    else if g.pending != .none || g.afterRandom != .none || g.pendingReplacement.isSome then
      g.chainPendingReplacement b
    else drainProbeNonPriorityCont g b
  | .finishPostStep (.discardCleanupIds p remainingIds _) =>
    let g := clearProbeReplacement g
    drainProbePausedStep (g.discardCleanupIds p remainingIds)
  | .endControlExileLoop remaining cause pendingLog extraSkipIds fromEventIdx? deferPlayFromExileLogs =>
    let g := clearProbeReplacement g
    drainProbePausedStep (g.runEndControlExileLoop remaining (cause := cause)
      (pendingLog := pendingLog) (extraSkipIds := extraSkipIds)
      (fromEventIdx? := fromEventIdx?)
      (deferPlayFromExileLogs := deferPlayFromExileLogs))
  | .leavePlayersWhoLost savedPending popOuter departed rewindProposal fromEventIdx? =>
    let g := clearProbeReplacement g
    let (g', _, sOut, poOut, depOut, rwOut, effFromIdx?) :=
      g.checkSBACountedWithLeavesCoreWithIdx savedPending popOuter departed rewindProposal
        (deferRestore := true) (deferPlayFromExileLogs := false)
        (fromEventIdx? := fromEventIdx?)
    let g' := if depOut.isEmpty then g' else g'.appendDepartedManyToContinuations depOut
    let g' :=
      if g'.over then g'
      else if g'.sbaPaused then
        if g'.players.any (fun r => r.lost && !r.leftTheGame) || sOut.isSome || poOut ||
            !depOut.isEmpty || rwOut.isSome then
          g'.chainPendingReplacement (.leavePlayersWhoLost sOut poOut depOut rwOut effFromIdx?)
        else g'
      else if sOut.isSome || poOut || rwOut.isSome then
        g'.chainPendingReplacement
          (.restorePending (sOut.getD .none) poOut none depOut rwOut)
      else g'
    drainProbePausedStep g'
  | pr@(.gainLife ..)
  | pr@(.dealDamageToPlayer ..)
  | pr@(.runModalManaEffect ..)
  | pr@(.finishManaAbilityMountainTrigger ..)
  | pr@(.endProposalAction ..)
  | pr@(.finishPostStep (.logExpiredPlayFromExile ..))
  | pr@(.finishPostStep (.conniveTricksterTarget ..))
  | pr@(.finishPostStep (.finishAbilityResolution ..))
  | pr@(.finishPostStep (.grantAdventureExilePermission ..))
  | pr@(.logMessage ..)
  | pr@(.recordPutCounters ..)
  | pr@(.putCountersDeferredLog ..)
  | pr@(.logPutCounterDelta ..)
  | pr@(.finishPostStep (.logDiscardIfInGraveyard ..))
  | pr@(.finishPostStep (.logExiledIfInExile ..))
  | pr@(.finishPostStep (.logReturnedToHand ..))
  | pr@(.finishPostStep (.logPutsIntoHand ..))
  | pr@(.finishPostStep (.logPutOnOwnerLibrary ..))
  | pr@(.finishPostStep (.logIfCountersIncreased ..))
  | pr@(.finishPostStep (.finishMoveToOwnerGraveyardLog ..))
  | pr@(.finishPostStep (.logDiscardedCount ..))
  | pr@(.finishPostStep (.logGiftTreasureGiven ..))
  | pr@(.finishPostStep (.logCreatedTokensSummary ..))
  | pr@(.finishPostStep (.logDelayedBirdSoldiersCreated ..))
  | pr@(.finishPostStep (.applyAggregatedLifelink ..))
  | pr@(.finishPostStep (.sheHulkAfterDamage ..))
  | pr@(.finishPostStep .markNonManaCostPaid)
  | pr@(.finishPostStep (.recordCostSacrificedPower ..))
  | pr@(.closeBatch ..)
  | pr@(.restorePausedBatch ..)
  | pr@(.counterStackSpell ..)
  | pr@(.sacrificePermanentsLoop ..)
  | pr@(.continueInterpreter ..)
  | pr@(.markDamageOn ..)
  | pr@(.returnLinkedExileLoop ..)
  | pr@(.finishLinkedExileMove ..)
  | pr@(.phaseOutPermanentsLoop ..)
  | pr@(.phaseInControlled ..)
  | pr@(.phaseInControlledLoop ..)
  | pr@(.untapStepPermanents ..)
  | pr@(.finishPostStep .untapStepAfterPhaseIn)
  | pr@(.finishPostStep .recordUntapStepEnded)
  | pr@(.move ..)
  | pr@(.moveSimultaneousToGraveyard ..)
  | pr@(.moveCardsToGraveyardLoop ..)
  | pr@(.addLoreCounters ..)
  | pr@(.addLoreAfterDrawStep ..)
  | pr@(.finishSbaSweep ..)
  | pr@(.checkSBA ..)
  | pr@(.afterLastPermanentEnters ..)
  | pr@(.draw ..)
  | pr@(.drawOne ..)
  | pr@(.drawSubDraws ..)
  | pr@(.dealAssignedCombatDamage ..)
  | pr@(.addExtraCombatDamageStep) =>
    let g := clearProbeReplacement g
    drainProbePausedStep (g.resumePendingReplacementFwd pr)
  | other => g.chainPendingReplacement other

private partial def drainProbePausedStep (g : Game) : Game :=
  if g.over then g
  else
    match g.pending with
    | .chooseReplacement q choices =>
      let alreadyOrderedCycle :=
        (g.defaultReplacementId q choices).any g.replacementOrder.contains
      if alreadyOrderedCycle then g
      else
        let origPending := g.pending
        let g := (recordProbeFirstReplacement g).change (.pending .none)
        match g.pendingReplacement with
        | none => g
        | some pr =>
          let g := g.change (.pendingReplacement none)
          let g2 := drainProbeNonPriorityCont g pr
          if g2.pending == .none && g2.pendingReplacement == some pr then
            g2.change (.pending origPending)
          else g2
    | _ => g
end

private def livingPriorityInstead? (g : Game) (q : PlayerId) : Option PlayerId :=
  if g.over || g.livingPlayers.isEmpty then none
  else some (g.priorityInstead q)

/-- Forward reference to `firstContinuationPriorityGrant?` for `finishAndGrantPriority`'s default parameter. -/
@[extern "mtg_game_first_continuation_priority_grant"]
opaque firstContinuationPriorityGrantFwd? (g : Game) : Option (Option PlayerId) := none

inductive ConcedePriorityOutcome where
  | noGrant
  | settlesPromptOrOver
  | implicitResolutionChoice
  | grants (explicit? : Option PlayerId)
deriving BEq, Inhabited

/-- Forward reference to `classifyFinishAndGrantPriorityFuel` so `receivePriorityOutcomeFuel`
can live outside the main `mutual` block. -/
@[extern "mtg_game_classify_finish_and_grant_priority_fuel"]
private opaque classifyFinishAndGrantPriorityFuelFwd (g : Game) (p : PlayerId) (fuel : Nat) :
    ConcedePriorityOutcome := .settlesPromptOrOver

private def seqOptPendingReplacement (a? b? : Option PendingReplacement) : Option PendingReplacement :=
  match a?, b? with
  | some a, some b => some (.seq a b)
  | some a, none => some a
  | none, some b => some b
  | none, none => none

private structure PreparedRestoreReverse where
  g : Game
  caster : PlayerId
  freshCont? : Option PendingReplacement
  hasBlockingPrompt : Bool
  poppedTail? : Option PendingReplacement
  restoreCkptPending? : Option PendingReplacement
  restored? : Option PendingReplacement
  ckptWasRandom : Bool
  hadConsumedOrig : Bool
deriving Inhabited

private def isSelfSettlingPending : Pending → Bool
  | .none | .chooseReplacement .. => false
  | _ => true

private inductive RestoreProbeOutcome where
  | paused (g : Game) (queued : Bool) (settles : Bool := true)
  | delegate (g : Game) (queued : Bool) (nextPr : PendingReplacement)
deriving Inhabited

private inductive CostStageProjection where
  | failed
  | paused (g : Game)
  | ready (g : Game)
deriving Inhabited

private structure ProbeAdvanceResult where
  game : Game
  hasQueuedPending : Bool
  reversedProposal : Bool := false
  preReverseGame? : Option Game := none
deriving Inhabited

private def isCarrierOnlyFrame (f : ContinuationFrame) : Bool :=
  { f with
    pendingReplacement := none
    outerPendingReplacements := #[]
    interpWait? := none } == {}

private def isManaAbilityContinuation : PendingReplacement → Bool
  | .finishActivateManaAbilityPicks .. | .finishActivateManaAbilityPostSac .. => true
  | _ => false

private def isNonProposalGrantLeaf : PendingReplacement → Bool
  | .finishBecomeCast .. | .finishPostCast .. | .finishProposedSpellCosts ..
  | .completeActivation .. | .finishBecomeActivated ..
  | .finishPostLoyaltyActivated .. | .finishTurnFaceUp .. => false
  | _ => true

private def probeGameForPendingReplacement (g : Game) : Game :=
  let g := if g.sbaPaused then (recordProbeFirstReplacement g).change (.pending .none) else g
  let g := if g.pendingReplacement.isSome then g.change (.pendingReplacement none) else g
  g.popEmptyTopContinuationFrames

private def simulateFinishPostCastBody (g : Game) (caster : PlayerId) : Game :=
  let g := if g.sbaPaused then (recordProbeFirstReplacement g).change (.pending .none) else g
  let g := if g.proposedSpell.isSome then g.change (.proposedSpell none) else g
  let g := g.runPostCastCleanup
  let g : Game :=
    match g.pendingMayCastFromExile with
    | some (q, ids, left) =>
      if q != caster || g.pending != Pending.none then g
      else
        let alive := ids.filter (fun id =>
          (g.findObject? id).any (fun (o : GameObject) =>
            o.zone == Zone.exile && isCastableObject o && !g.isLand o))
        let g := g.change (.pendingMayCastFromExile none)
        if !g.stillInGame q || alive.isEmpty || left == 0 then g
        else
          g.beginResolutionChoice q (.mayCastUpToFromExile alive left) ""
    | none => g
  let g : Game :=
    match g.pendingFreeCopies with
    | some (q, ids, budget, castsLeft) =>
      if q != caster || g.pending != Pending.none then g
      else
        let alive := ids.filter (fun id => (g.findObject? id).any (fun (o : GameObject) => o.zone == Zone.exile))
        let castable := alive.filter (fun id =>
          (g.findObject? id).any (fun o => g.objectManaValue o ≤ budget))
        if !g.stillInGame q || castable.isEmpty || castsLeft == 0 then
          let g :=
            if alive.isEmpty then g
            else
              g.withBatch (some (.stateBased .copyOutsideStackOrBf)) fun g =>
                alive.foldl (fun g id =>
                  g.ceaseToExist id (cause := some (.stateBased .copyOutsideStackOrBf))) g
          g.change (.pendingFreeCopies none)
        else
          (g.change (.pendingFreeCopies none)).beginResolutionChoice q (.castCopiesFree alive budget castsLeft) ""
    | none => g
  g

private def spellOpensAncestryScry (g : Game) (p : PlayerId) (spellId : ObjectId) : Bool :=
  g.stillInGame p && !(g.player p).library.isEmpty &&
    match g.findObject? spellId with
    | none => false
    | some spell =>
      let liveCmds := g.objects.filter (fun o => o.owner == p && o.isCommander)
      let cmdTypes :=
        if !liveCmds.isEmpty then
          liveCmds.foldl (fun acc o => acc ++ (g.subtypes o).filter CardSubtype.isCreatureType) #[]
        else
          (g.player p).commanderCreatureTypes
      g.isCreature spell &&
        g.ancestryManaSpentOn spell.id &&
        (g.subtypes spell).any (fun sub => sub.isCreatureType && cmdTypes.contains sub)

private def containsFinishTurnFaceUp : PendingReplacement → Bool
  | .finishTurnFaceUp .. => true
  | .seq a b => containsFinishTurnFaceUp a || containsFinishTurnFaceUp b
  | _ => false

private def removeExactPendingReplacement (target : PendingReplacement) :
    PendingReplacement → Option PendingReplacement
  | .seq a b =>
    seqOptPendingReplacement
      (removeExactPendingReplacement target a)
      (removeExactPendingReplacement target b)
  | pr => if pr == target then none else some pr

private def prefixBeforeFinishTurnFaceUp (caster : PlayerId) (spellId : ObjectId)
    (hadOuter : Bool) : PendingReplacement → Option PendingReplacement × Bool
  | .finishTurnFaceUp c sid ho =>
    if c == caster && sid == spellId && ho == hadOuter then (none, true)
    else (some (.finishTurnFaceUp c sid ho), false)
  | .seq a b =>
    let (preA?, foundA) := prefixBeforeFinishTurnFaceUp caster spellId hadOuter a
    if foundA then (preA?, true)
    else
      let (preB?, foundB) := prefixBeforeFinishTurnFaceUp caster spellId hadOuter b
      if foundB then (seqOptPendingReplacement preA? preB?, true)
      else (some (.seq a b), false)
  | pr => (some pr, false)

/-- Prepare `g` for probing `.finishTurnFaceUp caster spellId hadOuter` without
re-entering `Casting.completeTurnFaceUp`'s open-`.chooseReplacement` deferral
(`Casting.lean:1818-1819`). Returns `none` if draining the open replacement
ends the game, opens a non-replacement prompt, or leaves an unrelated nested
`.finishTurnFaceUp` ahead of this leaf. -/
private def prepareGameForTurnFaceUpProbe (g : Game) (caster : PlayerId)
    (spellId : ObjectId) (hadOuter : Bool) : Option Game :=
  if g.over || g.livingPlayers.isEmpty then none
  else if let .chooseReplacement .. := g.pending then
    let gD := drainProbePausedStep g
    if gD.over || gD.livingPlayers.isEmpty then none
    else
      let gClean? : Option Game :=
        if gD.pending == .none && gD.afterRandom == .none then some gD
        else if let .chooseReplacement .. := gD.pending then
          some ((recordProbeFirstReplacement gD).change (.pending .none))
        else none
      match gClean? with
      | none => none
      | some gClean =>
        if gClean.over || gClean.livingPlayers.isEmpty then none
        else
          let stripped? : Option PendingReplacement :=
            gClean.pendingReplacement.bind fun pr =>
              (prefixBeforeFinishTurnFaceUp caster spellId hadOuter pr).1
          let gClean :=
            if stripped? == gClean.pendingReplacement then gClean
            else gClean.change (.pendingReplacement stripped?)
          if gClean.pendingReplacement.any containsFinishTurnFaceUp then none
          else some gClean
  else some g

/-- Pure probe classifying `Entering.receivePriority g p recheckSba`
(`Entering.lean:455-555`) into a priority grant, implicit resolution-choice
grant, or prompt/game-over settlement. Matches runtime: saves `pendingPriority`
before `reopenDeferredExileCasts`, delegates post-reopen continuations to
`classifyFinishAndGrantPriorityFuel`, uses `runSbaNow := true` after draining
`.chooseReplacement`, and recurses with `runSbaNow := true` when
`waitingTriggers` is empty and `runSbaNow == false` (CR 704.3 / 117.5). -/
private partial def receivePriorityOutcomeFuel (g : Game) (p : PlayerId)
    (runSbaNow : Bool) : Nat → ConcedePriorityOutcome
  | 0 => .settlesPromptOrOver
  | fuel + 1 =>
    if g.over || g.livingPlayers.isEmpty then .settlesPromptOrOver
    else
      let p := g.priorityInstead p
      let hadEntryPending := g.pending != .none
      let savePendingP (gCur : Game) (prio : PlayerId) : Game :=
        let target := gCur.priorityInstead prio
        if gCur.pendingPriority == some target then gCur
        else gCur.change (.pendingPriority (some target))
      let implicitToOutcome (gCur : Game) (prio : PlayerId) : ConcedePriorityOutcome :=
        if !hadEntryPending || gCur.pendingPriority.isNone then
          match livingPriorityInstead? gCur prio with
          | some q => .grants (some q)
          | none => .settlesPromptOrOver
        else .implicitResolutionChoice
      if g.pending == .none && g.afterRandom == .none &&
          g.proposedSpell.isNone &&
          (g.pendingMayCastFromExile.isSome || g.pendingFreeCopies.isSome) then
        let oldP := p
        let g := (savePendingP g p).reopenDeferredExileCasts
        let p := g.priorityInstead p
        if g.over || g.livingPlayers.isEmpty then .settlesPromptOrOver
        else if let .chooseReplacement .. := g.pending then
          let g :=
            if g.anyContinuationSettlesControlFlowFwd && g.pendingPriority == some oldP && oldP != p then
              savePendingP g p
            else g
          match g.firstContinuationPriorityGrantFwd? with
          | some (some q) => .grants (some q)
          | some none => implicitToOutcome g p
          | none =>
            if g.anyContinuationGrantsPriorityFwd then .grants none
            else if g.anyContinuationSettlesControlFlowFwd then .settlesPromptOrOver
            else
              let gD := drainProbePausedStep g
              if gD.over || gD.livingPlayers.isEmpty || gD.pending != .none ||
                  gD.afterRandom != .none || gD.pendingReplacement.isSome then
                .settlesPromptOrOver
              else classifyFinishAndGrantPriorityFuelFwd gD p fuel
        else if g.pending != .none || g.afterRandom != .none then .settlesPromptOrOver
        else if g.currentInterpWait?.isSome ||
            g.pendingReplacement.isSome || !g.outerPendingReplacements.isEmpty then
          classifyFinishAndGrantPriorityFuelFwd g p fuel
        else
          receivePriorityOutcomeFuel g p runSbaNow fuel
      else
        let g :=
          if g.pending == .none && g.afterRandom == .none then g.completeActiveResolutions
          else g
        let p := g.priorityInstead p
        if g.over || g.livingPlayers.isEmpty then .settlesPromptOrOver
        else if g.legendChoicePending? then .settlesPromptOrOver
        else if let .chooseReplacement .. := g.pending then
          match g.firstContinuationPriorityGrantFwd? with
          | some (some q) => .grants (some q)
          | some none => implicitToOutcome g p
          | none =>
            if g.anyContinuationGrantsPriorityFwd then .grants none
            else if g.anyContinuationSettlesControlFlowFwd then .settlesPromptOrOver
            else
              let gD := drainProbePausedStep g
              if gD.over || gD.livingPlayers.isEmpty || gD.pending != .none ||
                  gD.afterRandom != .none || gD.pendingReplacement.isSome then
                .settlesPromptOrOver
              else classifyFinishAndGrantPriorityFuelFwd gD p fuel
        else if g.pending != .none then .settlesPromptOrOver
        else
          let g := if runSbaNow then g.checkSBA else g
          let p := g.priorityInstead p
          if g.over || g.livingPlayers.isEmpty then .settlesPromptOrOver
          else if g.legendChoicePending? then .settlesPromptOrOver
          else if let .chooseReplacement .. := g.pending then
            match g.firstContinuationPriorityGrantFwd? with
            | some (some q) => .grants (some q)
            | some none => implicitToOutcome g p
            | none =>
              if g.anyContinuationGrantsPriorityFwd then .grants none
              else if g.anyContinuationSettlesControlFlowFwd then .settlesPromptOrOver
              else
                let gD := drainProbePausedStep g
                if gD.over || gD.livingPlayers.isEmpty || gD.pending != .none ||
                    gD.afterRandom != .none || gD.pendingReplacement.isSome then
                  .settlesPromptOrOver
                else classifyFinishAndGrantPriorityFuelFwd gD p fuel
          else if g.pending != .none then .settlesPromptOrOver
          else
            match g.nextTriggerStackingPlayer? with
            | none =>
              if g.waitingTriggers.isEmpty then
                if runSbaNow then
                  match livingPriorityInstead? g p with
                  | some q => .grants (some q)
                  | none => .settlesPromptOrOver
                else
                  receivePriorityOutcomeFuel g p true fuel
              else
                let g := g.putTriggerBatch g.currentTriggerBatch
                let p := g.priorityInstead p
                if g.over || g.livingPlayers.isEmpty || g.pending != .none then
                  .settlesPromptOrOver
                else
                  receivePriorityOutcomeFuel g p true fuel
            | some q =>
              let mine := g.waitingTriggersOf q
              let allIdentical :=
                mine.size ≤ 1 ||
                  mine.all (fun w =>
                    w.source.id == mine[0]!.source.id &&
                      w.ability == mine[0]!.ability &&
                      w.pattern == mine[0]!.pattern &&
                      w.causeId == mine[0]!.causeId &&
                      w.causeIds == mine[0]!.causeIds &&
                      w.causeController == mine[0]!.causeController &&
                      w.lastKnownPower == mine[0]!.lastKnownPower &&
                      w.lastKnownToughness == mine[0]!.lastKnownToughness &&
                      w.delayedTrigger == mine[0]!.delayedTrigger &&
                      w.abilityEffect == mine[0]!.abilityEffect &&
                      w.isReflexive == mine[0]!.isReflexive)
              if allIdentical || mine.all (·.ordered) then
                let g := g.putTriggerBatch mine
                let p := g.priorityInstead p
                if g.over || g.livingPlayers.isEmpty || g.pending != .none then
                  .settlesPromptOrOver
                else
                  receivePriorityOutcomeFuel g p false fuel
              else
                .settlesPromptOrOver

private partial def receivePriorityOutcome (g : Game) (p : PlayerId)
    (recheckSba : Bool := true) (fuel : Nat := 16) : ConcedePriorityOutcome :=
  receivePriorityOutcomeFuel g p recheckSba fuel

private partial def receivePriorityRecipient? (g : Game) (p : PlayerId)
    (recheckSba : Bool := true) : Option PlayerId :=
  match receivePriorityOutcome g p (recheckSba := recheckSba) with
  | .grants (some q) => some q
  | _ => none

/-- Pure probe classifying `Combat.beginCombatDamageAssignment` (`forAttackers := true`)
or `Combat.continueBlockerCombatAssignment` (`forAttackers := false`). -/
private partial def probeCombatDamageResumeOutcome (g : Game) (forAttackers : Bool) :
    ConcedePriorityOutcome :=
  if g.over || g.livingPlayers.isEmpty then .settlesPromptOrOver
  else
    let gPost :=
      if forAttackers then g.beginCombatDamageAssignment
      else g.continueBlockerCombatAssignment
    if gPost.over || gPost.livingPlayers.isEmpty then .settlesPromptOrOver
    else if let .chooseReplacement .. := gPost.pending then
      let gD := drainProbePausedStep gPost
      if gD.over || gD.livingPlayers.isEmpty || gD.pending != .none ||
          gD.afterRandom != .none then
        .settlesPromptOrOver
      else
        match gD.pendingReplacement with
        | none => receivePriorityOutcome gD gD.activePlayer (recheckSba := true)
        | some (.receivePriority q) =>
          receivePriorityOutcome (gD.change (.pendingReplacement none)) q (recheckSba := true)
        | some _ => .settlesPromptOrOver
    else if gPost.pending != .none || gPost.afterRandom != .none then
      .settlesPromptOrOver
    else if gPost.playersReceivePriority then
      match livingPriorityInstead? gPost gPost.priority with
      | some q => .grants (some q)
      | none => .settlesPromptOrOver
    else .settlesPromptOrOver

mutual
private partial def continueStartNextTurnRecipient? (g : Game) (nextP : PlayerId)
    (remainingDeparted : Array PlayerId) (runBeginTurn : Bool)
    (alreadyExpired : Array PlayerId) : Option PlayerId := Id.run do
  if !runBeginTurn || g.over then
    return none
  let mut g := g
  let mut alreadyExpired := alreadyExpired
  for i in [0:remainingDeparted.size] do
    let dep := remainingDeparted[i]!
    if !alreadyExpired.contains dep then
      if !(g.teamMembers dep).any g.stillInGame then
        for m in g.teamMembers dep do
          if !alreadyExpired.contains m then
            alreadyExpired := alreadyExpired.push m
      else
        alreadyExpired := alreadyExpired.push dep
      let gExp0 := g.expireUntilNextTurnEffects dep
      if gExp0.over || gExp0.livingPlayers.isEmpty ||
          (match gExp0.pending with | .chooseLegend .. => true | _ => false) then
        return none
      g := drainProbePausedStep gExp0
      if g.over || g.livingPlayers.isEmpty || g.pending != .none ||
          g.pendingReplacement.isSome then
        return none
  let (seats, seatsExtra) := g.currentSharedTurnState
  let midRegularShared := !seatsExtra && !g.isSharedTurnFinalSeat
  let inProgressExtraSeats := g.countInProgressSharedExtraSeats seats seatsExtra g.extraTurns
  let lastReg := g.lastRegularTurnSeat
  let regEnd := (g.teamMembers lastReg).back? |>.getD lastReg
  let (targetP, targetExtra) : PlayerId × Bool := Id.run do
    if !midRegularShared then
      let mut sIdx := 0
      while sIdx < g.extraTurns.size && !g.stillInGame g.extraTurns[sIdx]! do
        sIdx := sIdx + 1
      if let some q := (g.extraTurns.extract sIdx g.extraTurns.size)[0]? then
        return (q, true)
    let n := g.players.size
    let fromExtra := !midRegularShared && g.extraTurns.contains nextP
    if fromExtra || !g.stillInGame nextP then
      let startIdx := if fromExtra then regEnd.idx + 1 else nextP.idx
      for k in [0:n] do
        let q : PlayerId := ⟨(startIdx + k) % n⟩
        if g.stillInGame q then
          return (q, false)
    return (nextP, false)
  let sameShared :=
    g.stillInGame targetP && targetExtra == seatsExtra && !seats.isEmpty &&
      g.areTeammates seats[0]! targetP && !seats.contains targetP
  let endingCurrentRegularShared (q : PlayerId) : Bool :=
    !seatsExtra && !sameShared && seats.any (fun s => s == q || g.areTeammates s q)
  let endingCurrentExtraShared (q : PlayerId) : Bool :=
    seatsExtra && !sameShared && seats.any (fun s => s == q || g.areTeammates s q)
  let mut skipIdx := 0
  let mut unexpiredExtra : Array PlayerId := #[]
  if !midRegularShared then
    while skipIdx < g.extraTurns.size && !g.stillInGame g.extraTurns[skipIdx]! do
      let d := g.extraTurns[skipIdx]!
      let extraSeatEnding :=
        seatsExtra && !sameShared && skipIdx < inProgressExtraSeats
      if !extraSeatEnding && !alreadyExpired.contains d && !unexpiredExtra.contains d then
        unexpiredExtra := unexpiredExtra.push d
      skipIdx := skipIdx + 1
  let nextExtra? :=
    if midRegularShared then none
    else (g.extraTurns.extract skipIdx g.extraTurns.size)[0]?
  if !sameShared && g.stillInGame targetP then
    for tm in g.teamMembers targetP do
      if !g.stillInGame tm &&
          !alreadyExpired.contains tm && !unexpiredExtra.contains tm then
        unexpiredExtra := unexpiredExtra.push tm
  if (!g.stillInGame nextP || !unexpiredExtra.isEmpty) && !g.over &&
      g.players.any (fun pl => g.stillInGame pl.id) then
    match nextExtra? with
    | some q =>
      if q != nextP || !unexpiredExtra.isEmpty then
        return continueStartNextTurnRecipient? g q unexpiredExtra runBeginTurn alreadyExpired
    | none =>
      let n := g.players.size
      let fromExtra := !midRegularShared && g.extraTurns.contains nextP
      let appendDepartedTeammates (base : Array PlayerId) (q : PlayerId) : Array PlayerId :=
        if !sameShared then
          (g.teamMembers q).foldl (fun acc tm =>
            if !g.stillInGame tm &&
                !alreadyExpired.contains tm && !acc.contains tm then
              acc.push tm
            else acc) base
        else base
      let (nextP', newlyDeparted) := Id.run do
        let mut newly := unexpiredExtra
        if fromExtra then
          if !endingCurrentExtraShared nextP && !alreadyExpired.contains nextP &&
              !newly.contains nextP then
            newly := newly.push nextP
          for k in [1:n+1] do
            let q : PlayerId := ⟨(regEnd.idx + k) % n⟩
            if !g.stillInGame q then
              if !endingCurrentRegularShared q && !alreadyExpired.contains q && !newly.contains q then
                newly := newly.push q
            else
              return (q, appendDepartedTeammates newly q)
          return (regEnd, newly)
        else
          for k in [0:n] do
            let q : PlayerId := ⟨(nextP.idx + k) % n⟩
            if !g.stillInGame q then
              if !endingCurrentRegularShared q && !alreadyExpired.contains q && !newly.contains q then
                newly := newly.push q
            else
              return (q, appendDepartedTeammates newly q)
          return (nextP, newly)
      if g.stillInGame nextP' && (nextP' != nextP || !newlyDeparted.isEmpty) then
        return continueStartNextTurnRecipient? g nextP' newlyDeparted runBeginTurn alreadyExpired
  let (gNext, didBeginTurn) : Game × Bool :=
    match nextExtra? with
    | some q =>
      let sameShared :=
        seatsExtra && !seats.isEmpty && g.areTeammates seats[0]! q && !seats.contains q
      let nextTurnNum := if sameShared then g.turnNumber else g.turnNumber + 1
      let g := g.record (GameEvent.turnBegan nextTurnNum q (extra := true))
      let g := g.expireFinishedNextTurnPlayerControl
      let g := g.change (.cleanupGivesPriority false)
      let g :=
        if !g.powerUpsForbidden then
          g.createEffect .powerUpsForbiddenThisTurn (cause := some (.gameRule .continuousEffect))
        else g
      (g, true)
    | none =>
      if g.stillInGame nextP then
        let sameShared :=
          !seatsExtra && !seats.isEmpty &&
            g.areTeammates seats[0]! nextP && !seats.contains nextP
        let nextTurnNum := if sameShared then g.turnNumber else g.turnNumber + 1
        let g := g.record (GameEvent.turnBegan nextTurnNum nextP (extra := false))
        let g := g.expireFinishedNextTurnPlayerControl
        let g := g.change (.cleanupGivesPriority false)
        (g, true)
      else (g, false)
  if runBeginTurn && didBeginTurn && !gNext.over && gNext.stillInGame gNext.activePlayer then
    let gStart0 := gNext.beginTurnStartExpiryPrefix
    if gStart0.over || gStart0.livingPlayers.isEmpty then
      return none
    else if (match gStart0.pending with | .chooseLegend .. => true | _ => false) then
      return none
    else
      let gStart := drainProbePausedStep gStart0
      if gStart.over || gStart.livingPlayers.isEmpty || gStart.pending != .none ||
          gStart.pendingReplacement.isSome then
        return none
      else
        return beginTurnAfterStartExpiryRecipient? gStart
  else
    return none

private partial def startNextTurnAndBeginRecipient? (g : Game) : Option PlayerId :=
  if g.over || g.livingPlayers.isEmpty then none
  else
    let (g1, nextP, departed) := g.prepareStartNextTurn
    let g1 := drainProbePausedStep g1
    if g1.over || g1.livingPlayers.isEmpty || g1.pending != .none ||
        g1.pendingReplacement.isSome then none
    else continueStartNextTurnRecipient? g1 nextP departed true #[]

private partial def endTurnAfterCleanupStepEndedRecipient? (g : Game) : Option PlayerId :=
  if g.over || g.livingPlayers.isEmpty then none
  else
    let g1 := drainProbePausedStep (g.recordPhaseEnded .ending)
    if g1.over || g1.livingPlayers.isEmpty || g1.pending != .none ||
        g1.pendingReplacement.isSome then none
    else startNextTurnAndBeginRecipient? g1

private partial def postSbaCleanupRecipient? (g : Game) (sba : Bool) : Option PlayerId :=
  if g.over || g.livingPlayers.isEmpty then none
  else if sba || g.hasWaitingTriggers then
    receivePriorityRecipient? g g.activePlayer (recheckSba := true)
  else
    let g1 := drainProbePausedStep (g.emptyManaPools.recordStepEnded .cleanup)
    if g1.over || g1.livingPlayers.isEmpty || g1.pending != .none ||
        g1.pendingReplacement.isSome then none
    else endTurnAfterCleanupStepEndedRecipient? g1

private partial def finishCleanupAfterClearEotRecipient? (g : Game) : Option PlayerId :=
  if g.over || g.livingPlayers.isEmpty then none
  else
    let (g1, sba, _) := g.checkSBACountedWithLeaves
    if g1.over || g1.livingPlayers.isEmpty then none
    else
      match g1.pending with
      | .chooseLegend .. => none
      | .chooseReplacement .. =>
        let g2 := drainProbePausedStep g1
        if g2.over || g2.livingPlayers.isEmpty || g2.pending != .none ||
            g2.pendingReplacement.isSome then none
        else postSbaCleanupRecipient? g2 sba
      | .none =>
        postSbaCleanupRecipient? g1 sba
      | _ => none

private partial def cleanupStepAfterDiscardRecipient? (g : Game) : Option PlayerId :=
  if g.over || g.livingPlayers.isEmpty then none
  else
    let gClean := drainProbePausedStep g.clearEOT
    if gClean.over || gClean.livingPlayers.isEmpty || gClean.pending != .none ||
        gClean.pendingReplacement.isSome then none
    else finishCleanupAfterClearEotRecipient? gClean

private partial def stepPriorityRecipient? (g : Game) (st : Step) : Option PlayerId :=
  if g.over || g.livingPlayers.isEmpty then none
  else
    match st with
    | .untap => none
    | .draw =>
      if g.skipsFirstDraw then
        let gClean := drainProbePausedStep (g.recordPhaseEnded .beginning)
        if gClean.over || gClean.livingPlayers.isEmpty || gClean.pending != .none ||
            gClean.afterRandom != .none || gClean.pendingReplacement.isSome then none
        else beginStepContRecipient? gClean .precombatMain
      else
        let gDraw := drainProbePausedStep
          (g.draw g.activePlayer 1 (cause := some (.turnBased .drawStepDraw)))
        if gDraw.over || gDraw.livingPlayers.isEmpty || gDraw.pending != .none ||
            gDraw.afterRandom != .none || gDraw.pendingReplacement.isSome then none
        else receivePriorityRecipient? gDraw gDraw.activePlayer (recheckSba := true)
    | .declareAttackers =>
      if !g.stillInGame g.activePlayer then
        receivePriorityRecipient? g g.activePlayer (recheckSba := true)
      else none
    | .declareBlockers =>
      let attackers := g.battlefield.filter (·.status.attacking)
      if attackers.isEmpty then
        receivePriorityRecipient? g g.activePlayer (recheckSba := true)
      else
        let ps := g.defendingPlayers
        let teamQueue := ps.foldl (fun (acc : Array PlayerId) pid =>
          if acc.any (fun q => q == pid || g.areTeammates q pid) then acc
          else acc.push pid) #[]
        if teamQueue.isEmpty then
          let opp := g.defendingPlayer
          if attackers.any (·.status.attackingTarget.isNone) &&
              (g.livingOpponents g.activePlayer).any (fun pl => pl.id == opp) then
            none
          else
            receivePriorityRecipient? g g.activePlayer (recheckSba := true)
        else
          none
    | .combatDamage =>
      let gCd := g.changes #[.pending .none, .pendingBlockerAssignments #[]]
      if (gCd.creaturesAssigningCombatDamage true).isEmpty &&
          (gCd.creaturesAssigningCombatDamage false).isEmpty then
        receivePriorityRecipient? gCd gCd.activePlayer (recheckSba := true)
      else if gCd.needsCombatDamageChoice true then
        none
      else
        let assigningBlockers := gCd.creaturesAssigningCombatDamage false
        let blockerNeedsPrompt := gCd.apnapOrder.any (fun p =>
          p != gCd.activePlayer && gCd.stillInGame p &&
            assigningBlockers.any (fun o =>
              gCd.controlledBy o p &&
                (gCd.legalCombatDamageRecipients o false).size ≥ 2 &&
                gCd.combatDamageAmount o > 0))
        if blockerNeedsPrompt then none
        else
          match probeCombatDamageResumeOutcome gCd true with
          | .grants (some q) => some q
          | _ => none
    | .cleanup =>
      let gClean := drainProbePausedStep g.discardToMaxHandSize
      if gClean.over || gClean.livingPlayers.isEmpty || gClean.pending != .none ||
          gClean.afterRandom != .none || gClean.pendingReplacement.isSome then none
      else cleanupStepAfterDiscardRecipient? gClean
    | .precombatMain =>
      let gLore := drainProbePausedStep g.addLoreAfterDrawStep
      if gLore.over || gLore.livingPlayers.isEmpty || gLore.pending != .none ||
          gLore.afterRandom != .none || gLore.pendingReplacement.isSome then none
      else receivePriorityRecipient? gLore gLore.activePlayer (recheckSba := true)
    | .upkeep | .beginningOfCombat | .end | .endOfCombat | .postcombatMain =>
      receivePriorityRecipient? g g.activePlayer (recheckSba := true)

private partial def beginStepAfterPhaseBeganRecipient? (g : Game) (st : Step) : Option PlayerId :=
  if g.over || g.livingPlayers.isEmpty then none
  else
    let g1 := if st == .draw && g.skipsFirstDraw then g else g.recordStepBegan st
    let gClean := drainProbePausedStep g1
    if gClean.over || gClean.livingPlayers.isEmpty || gClean.pending != .none ||
        gClean.pendingReplacement.isSome then none
    else stepPriorityRecipient? gClean st

private partial def beginStepContRecipient? (g : Game) (st : Step) : Option PlayerId :=
  if g.over || g.livingPlayers.isEmpty then none
  else
    let g := if g.step == .endOfCombat && st != .endOfCombat then g.clearCombat else g
    let g := g.changes #[
      .pending .none,
      .consecutivePasses 0,
      .cleanupGivesPriority false,
      .proposedSpell none ]
    let isPhaseStart :=
      match st with
      | .untap | .precombatMain | .beginningOfCombat | .postcombatMain | .end => true
      | _ => false
    let g1 :=
      if st == .draw && g.skipsFirstDraw then g
      else if isPhaseStart then g.recordPhaseBegan st.phase
      else g
    let gClean := drainProbePausedStep g1
    if gClean.over || gClean.livingPlayers.isEmpty || gClean.pending != .none ||
        gClean.pendingReplacement.isSome then none
    else beginStepAfterPhaseBeganRecipient? gClean st

private partial def beginTurnAfterStartExpiryRecipient? (g : Game) : Option PlayerId :=
  let g := drainProbePausedStep g
  if g.over || g.livingPlayers.isEmpty || g.pending != .none ||
      g.pendingReplacement.isSome then none
  else
    let p := g.activePlayer
    let needDeferred :=
      g.isSharedTurnFirstSeat &&
        (g.teamMembers p).any (fun q =>
          g.activeEffects.any (fun (_, s) =>
            s == .lifeCantChange q || s == .protectionFromEverything q ||
              (match s with
               | .playerRule r (.protectionFrom _ _ _) (.untilNextTurnOf r') => r == q && r' == q
               | _ => false)))
    let g :=
      if needDeferred then
        let g0 := g.withBatch none (fun g => g.expireTurnStartProtectionAndLife p)
        if g0.over || g0.livingPlayers.isEmpty || g0.legendChoicePending? then g0
        else drainProbePausedStep g0
      else g
    if g.over || g.livingPlayers.isEmpty || g.pending != .none ||
        g.pendingReplacement.isSome then none
    else
      let g := Id.run do
        let mut g := g
        while g.proposalCheckpoint.isSome do
          g := g.change .clearProposalCheckpoint
        return g
      let g := g.changes #[
        .pending .none,
        .consecutivePasses 0,
        .cleanupGivesPriority false,
        .proposedSpell none ]
      let g := drainProbePausedStep (g.recordPhaseBegan .beginning)
      if g.over || g.livingPlayers.isEmpty || g.pending != .none ||
          g.pendingReplacement.isSome then none
      else
        let g := drainProbePausedStep (g.recordStepBegan .untap)
        if g.over || g.livingPlayers.isEmpty || g.pending != .none ||
            g.pendingReplacement.isSome then none
        else
          let g :=
            if g.isSharedTurnFirstSeat then
              let g0 := g.phaseInControlled g.activePlayer (includeTeammates := true)
              if g0.over || g0.livingPlayers.isEmpty || g0.legendChoicePending? then g0
              else drainProbePausedStep g0
            else g
          if g.over || g.livingPlayers.isEmpty || g.pending != .none ||
              g.pendingReplacement.isSome then none
          else
            let g0 := g.runUntapStepAfterPhaseIn
            let g :=
              if g0.over || g0.livingPlayers.isEmpty || g0.legendChoicePending? then g0
              else drainProbePausedStep g0
            if g.over || g.livingPlayers.isEmpty || g.pending != .none ||
                g.pendingReplacement.isSome then none
            else
              beginStepContRecipient? g .upkeep

private partial def advanceAfterStepEndedRecipient? (g : Game) : Option PlayerId :=
  if g.over || g.livingPlayers.isEmpty then none
  else if g.step == .endOfCombat && g.additionalCombatPhases > 0 then
    let gClean := drainProbePausedStep (g.recordPhaseEnded .combat)
    if gClean.over || gClean.livingPlayers.isEmpty || gClean.pending != .none ||
        gClean.pendingReplacement.isSome then none
    else beginStepContRecipient? gClean .beginningOfCombat
  else
    match g.step.next? with
    | some st =>
      let gClean :=
        if g.step.phase != st.phase then
          drainProbePausedStep (g.recordPhaseEnded g.step.phase)
        else g
      if gClean.over || gClean.livingPlayers.isEmpty || gClean.pending != .none ||
          gClean.pendingReplacement.isSome then none
      else beginStepContRecipient? gClean st
    | none => none

private partial def advanceStepRecipient? (g : Game) : Option PlayerId :=
  if g.over || g.livingPlayers.isEmpty then none
  else
    let g := drainProbePausedStep g.emptyManaPools
    if g.over || g.livingPlayers.isEmpty || g.pending != .none ||
        g.pendingReplacement.isSome then none
    else
      match g.step.next? with
      | some _ =>
        let attackers := g.battlefield.filter (·.status.attacking)
        let hadAttackersThisCombat : Bool :=
          if g.step != .declareAttackers then true
          else
            let combatBoundIdx? :=
              (List.range g.events.size).reverse.find? fun idx =>
                let e := g.events[idx]!
                e.turn == g.turnNumber &&
                  match e.change with
                  | .rules (.turn (.phaseBegan .combat))
                  | .rules (.turn (.phaseEnded .combat)) => true
                  | _ => false
            let slice : Array GameEvent :=
              match combatBoundIdx? with
              | some boundIdx => g.events.extract (boundIdx + 1) g.events.size
              | none =>
                let stepStartIdx? :=
                  (List.range g.events.size).reverse.find? fun idx =>
                    let e : GameEvent := g.events[idx]!
                    e.turn == g.turnNumber &&
                      match e.change with
                      | .rules (.turn (.stepBegan .declareAttackers _)) => true
                      | _ => false
                match stepStartIdx? with
                | some startIdx => g.events.extract (startIdx + 1) g.events.size
                | none => g.events.filter (·.turn == g.turnNumber)
            !attackers.isEmpty ||
              slice.any fun e =>
                match e.change with
                | .rules (.combat (.attackersDeclared _ decls)) => !decls.isEmpty
                | .rules (.combat (.becameAttacking ..)) => true
                | _ => false
        if g.step == .declareAttackers && !hadAttackersThisCombat then
          let gClean := drainProbePausedStep (g.recordStepEnded g.step)
          if gClean.over || gClean.livingPlayers.isEmpty || gClean.pending != .none ||
              gClean.pendingReplacement.isSome then none
          else beginStepContRecipient? gClean .endOfCombat
        else if g.step == .combatDamage && g.pendingRegularCombatDamage then
          let gClean := drainProbePausedStep (g.recordStepEnded .combatDamage)
          if gClean.over || gClean.livingPlayers.isEmpty || gClean.pending != .none ||
              gClean.pendingReplacement.isSome then none
          else beginStepContRecipient? gClean .combatDamage
        else if g.step == .endOfCombat && g.additionalCombatPhases > 0 then
          let g1 := drainProbePausedStep (g.recordStepEnded .endOfCombat)
          if g1.over || g1.livingPlayers.isEmpty || g1.pending != .none ||
              g1.pendingReplacement.isSome then none
          else advanceAfterStepEndedRecipient? g1
        else
          let g1 := drainProbePausedStep (g.recordStepEnded g.step)
          if g1.over || g1.livingPlayers.isEmpty || g1.pending != .none ||
              g1.pendingReplacement.isSome then none
          else advanceAfterStepEndedRecipient? g1
      | none =>
        let gClean := drainProbePausedStep (g.recordStepEnded .cleanup)
        if gClean.over || gClean.livingPlayers.isEmpty || gClean.pending != .none ||
            gClean.pendingReplacement.isSome then none
        else if gClean.cleanupGivesPriority then
          beginStepContRecipient? gClean .cleanup
        else
          let gEnd := drainProbePausedStep (gClean.recordPhaseEnded .ending)
          if gEnd.over || gEnd.livingPlayers.isEmpty || gEnd.pending != .none ||
              gEnd.pendingReplacement.isSome then none
          else startNextTurnAndBeginRecipient? gEnd
end

set_option maxHeartbeats 400000 in
mutual
private partial def pausedPromptSettles (gCur : Game) (hq : Bool) (pOpened : Pending) : Bool :=
  gCur.over || isSelfSettlingPending pOpened || gCur.afterRandom != .none ||
    match pOpened with
    | .chooseReplacement .. =>
      anyContinuationSettlesControlFlowWithQueued gCur hq
    | _ => false

private partial def prepareReverseInRestorePending (g : Game)
    (popped? : Option PendingReplacement) (departed : Array PlayerId) : PreparedRestoreReverse :=
  let g := g.popNestedManaProposalCheckpoint
  let caster : PlayerId := (g.proposedSpell.map (·.caster)).getD g.activePlayer
  let allDeparted : Array PlayerId :=
    match g.proposalCheckpoint with
    | some ckpt => g.playersDepartedSinceCheckpoint ckpt departed
    | none => departed
  let ckptPending : Pending := (g.proposalCheckpoint.map (·.pending)).getD .none
  let ckptOrigCont? : Option PendingReplacement :=
    g.proposalCheckpoint.bind fun ckpt =>
      (ckpt.continuations.back?.getD {}).pendingReplacement
  let ckptOuters : Array PendingReplacement :=
    g.proposalCheckpoint.map (fun ckpt =>
      (ckpt.continuations.back?.getD {}).outerPendingReplacements) |>.getD #[]
  let preRewindOuters : Array PendingReplacement := g.outerPendingReplacements
  let ckptMovedToOuter : Bool :=
    g.proposalCheckpoint.any fun ckpt =>
      ((ckpt.continuations.back?.getD {}).pendingReplacement).any fun ckptCont => Id.run do
        let slice := g.events.extract (min ckpt.eventsSize g.events.size) g.events.size
        for ev in slice do
          match ev with
          | .engine _ (.continuation (.pushOuterPendingReplacement pushed)) _ =>
            if pushed == ckptCont then return true
          | .engine _ (.beginProposalAction _) _
          | .engine _ (.proposedSpell (some _)) _
          | .engine _ (.continuation .popOuterPendingReplacement) _
          | .rules _ (.player (.lost ..)) _ _
          | .rules _ (.player (.leftGame ..)) _ _ =>
            return false
          | _ => pure ()
        return false
  let ckptUntouchedBeforeLeave : Bool :=
    g.proposalCheckpoint.any fun ckpt =>
      g.ckptPendingReplacementUntouchedBeforeLeave ckpt allDeparted (poppedOuter? := popped?)
  let hadConsumedOrig : Bool :=
    ckptOrigCont?.isSome && !(ckptMovedToOuter || ckptUntouchedBeforeLeave)
  let startExtraIdx :=
    if ckptMovedToOuter && ckptOuters.size < preRewindOuters.size then
      ckptOuters.size + 1
    else
      ckptOuters.size
  let extraDepartureOuters : Array PendingReplacement :=
    if startExtraIdx < preRewindOuters.size then
      (preRewindOuters.extract startExtraIdx preRewindOuters.size).map
        (PendingReplacement.appendDepartedMany allDeparted)
    else #[]
  let g := g.reverseProposedSpell (resumeContinuation := false) (skipDepartureReconcile := true)
  let g :=
    match ckptOrigCont?, g.pendingReplacement with
    | some origCont, some curCont =>
      let stripped? := PendingReplacement.dropTargetModDeparted origCont curCont
      if stripped? != some curCont then g.change (.pendingReplacement stripped?) else g
    | _, _ => g
  let rawCkptRestoreTarget : Option PendingReplacement :=
    if !g.over && ckptPending != .none && (popped?.isSome || !allDeparted.isEmpty) then
      some (.restorePending ckptPending false)
    else none
  let (g, strippedDeferredCkptPending) : Game × Bool :=
    match rawCkptRestoreTarget, g.pendingReplacement with
    | some target, some curCont =>
      if PendingReplacement.containsModDeparted target curCont then
        let stripped? := PendingReplacement.dropTargetModDeparted target curCont
        (if stripped? != some curCont then g.change (.pendingReplacement stripped?) else g, true)
      else
        (g, false)
    | _, _ => (g, false)
  let g :=
    if !g.over && g.afterRandom.player?.any (fun r => allDeparted.contains r || !g.stillInGame r) then
      g.change (.afterRandom .none)
    else g
  let g :=
    if hadConsumedOrig && g.pending == .none && g.afterRandom == .none then
      g.popEmptyTopContinuationFrames
    else g
  let g :=
    if !allDeparted.isEmpty then g.appendDepartedManyToContinuations allDeparted else g
  let (depOnlyOuter?, _) : Option PendingReplacement × Bool :=
    match popped?, ckptOrigCont? with
    | some outer, some origCont =>
      if !g.over && (ckptMovedToOuter || ckptUntouchedBeforeLeave) &&
          PendingReplacement.containsModDeparted origCont outer then
        (PendingReplacement.dropTargetModDeparted origCont outer, true)
      else
        (some outer, false)
    | outer?, _ => (outer?, false)
  let keepOrigCont? : Option PendingReplacement :=
    if !g.over && (ckptMovedToOuter || ckptUntouchedBeforeLeave) then
      match (if ckptMovedToOuter && ckptOuters.size < preRewindOuters.size then
               some preRewindOuters[ckptOuters.size]!
             else ckptOrigCont?).map (·.appendDepartedMany allDeparted) with
      | some origDep =>
        if depOnlyOuter?.any (PendingReplacement.containsModDeparted origDep) ||
            extraDepartureOuters.any (PendingReplacement.containsModDeparted origDep) then
          none
        else
          some origDep
      | none => none
    else none
  let extraToPush : Array PendingReplacement :=
    if ckptMovedToOuter && !extraDepartureOuters.isEmpty then
      match keepOrigCont? with
      | some keepOrig =>
        extraDepartureOuters.set! 0 (.seq extraDepartureOuters[0]! keepOrig)
      | none => extraDepartureOuters
    else
      extraDepartureOuters
  let g :=
    if extraToPush.isEmpty then g
    else
      let g := if g.continuations.isEmpty then g.change (.pushContinuationFrame {}) else g
      extraToPush.foldl (fun acc o => acc.change (.pushOuterPendingReplacement o)) g
  let restored? : Option PendingReplacement :=
    if ckptMovedToOuter && !extraDepartureOuters.isEmpty then none else keepOrigCont?
  let (g, restoreCkptPending?) : Game × Option PendingReplacement :=
    if !g.over && !g.sbaPaused && ckptPending != .none && g.pending == ckptPending &&
        (popped?.isSome || !allDeparted.isEmpty) then
      (g.change (.pending .none),
        some (.restorePending ckptPending false none allDeparted none))
    else if !g.over && strippedDeferredCkptPending then
      (g, some (.restorePending ckptPending false none allDeparted none))
    else
      (g, none)
  let ckptWasRandom : Bool :=
    match ckptPending with | .resolveRandom _ => true | _ => false
  let freshCont? := g.pendingReplacement
  let hasBlockingPrompt : Bool :=
    g.sbaPaused || g.pending != .none ||
      (g.afterRandom != .none && !(ckptWasRandom && restoreCkptPending?.isSome))
  let poppedTail? : Option PendingReplacement :=
    if popped?.isSome then
      seqOptPendingReplacement depOnlyOuter? (seqOptPendingReplacement restoreCkptPending? restored?)
    else none
  { g, caster, freshCont?, hasBlockingPrompt, poppedTail?,
    restoreCkptPending?, restored?, ckptWasRandom, hadConsumedOrig }

private partial def probeRestorePendingCore (g : Game) (hasQueuedPending : Bool)
    (pr : PendingReplacement)
    (followedByFinishChoice : Bool := false)
    (followedByExplicitPriority? : Option PlayerId := none) : RestoreProbeOutcome :=
  match pr with
  | .restorePending p popOuter promptLog departed rewindProposal => Id.run do
    let popped? : Option PendingReplacement :=
      if popOuter then g.outerPendingReplacements.back? else none
    let g0 :=
      let g1 := if popped?.isSome then g.change .popOuterPendingReplacement else g
      g1.popEmptyTopContinuationFrames
    let probeOpenPromptWith (gIn : Game) (pop? : Option PendingReplacement) (p' : Pending) : Game :=
      let g1 :=
        match pop? with
        | some popped => gIn.chainPendingReplacement popped
        | none => gIn
      let g2 :=
        if g1.continuations.isEmpty &&
            (match p' with | .resolutionChoice .. | .chooseReplacement .. => true | _ => false) then
          g1.change (.pushContinuationFrame {})
        else g1
      g2.change (.pending p')
    let shouldSplitBatch : Bool :=
      g0.openBatchAwaitedPausePrompt &&
        match rewindProposal with
        | some _ => !g0.isPreProposalCheckpointBatch && !g0.batchPausePromptValid p
        | none => g0.pending == .none && g0.batchPausePromptGoneOrInvalid p
    if shouldSplitBatch then
      if let some (curBid, _) := g0.currentBatch then
        let fullCont? : Option PendingReplacement :=
          match g0.pendingReplacement, popped? with
          | some prior, some popped => some (.seq prior popped)
          | some prior, none => some prior
          | none, some popped => some popped
          | none, none => none
        if let some (closePrefix, afterClose?) := fullCont?.bind (splitAfterCloseBatchFor? curBid) then
          let (gSplit, splitCont) : Game × PendingReplacement :=
            match rewindProposal, afterClose? with
            | some _, some after =>
              let gS := if g0.continuations.isEmpty then g0.change (.pushContinuationFrame {}) else g0
              let gS := gS.change (.pushOuterPendingReplacement after)
              (gS, .seq closePrefix (.restorePending p true promptLog departed rewindProposal))
            | _, some after =>
              let tailRestore : PendingReplacement :=
                .restorePending p false promptLog departed rewindProposal
              (g0, .seq closePrefix (.seq tailRestore after))
            | _, none =>
              let tailRestore : PendingReplacement :=
                .restorePending p false promptLog departed rewindProposal
              (g0, .seq closePrefix tailRestore)
          let gSplitClean :=
            if gSplit.pendingReplacement.isSome then gSplit.change (.pendingReplacement none)
            else gSplit
          return .delegate gSplitClean hasQueuedPending splitCont
    if rewindProposal.isSome && g0.batchPausePromptValid p then
      let (gDefer, deferPopped?) :=
        match g0.currentBatch, popped? with
        | some (curBid, _), some popped =>
          match splitAfterCloseBatchFor? curBid popped with
          | some (closePrefix, some after) =>
            let g1 := if g0.continuations.isEmpty then g0.change (.pushContinuationFrame {}) else g0
            let g1 := g1.change (.pushOuterPendingReplacement after)
            let tailRewind : PendingReplacement :=
              .restorePending .none true none departed rewindProposal
            (g1, some (.seq closePrefix tailRewind))
          | some (closePrefix, none) =>
            let tailRewind : PendingReplacement :=
              .restorePending .none false none departed rewindProposal
            (g0, some (.seq closePrefix tailRewind))
          | none =>
            let tailRewind : PendingReplacement :=
              .restorePending .none false none departed rewindProposal
            (g0, some (.seq popped tailRewind))
        | _, some popped =>
          let tailRewind : PendingReplacement :=
            .restorePending .none false none departed rewindProposal
          (g0, some (.seq popped tailRewind))
        | _, none =>
          let tailRewind : PendingReplacement :=
            .restorePending .none false none departed rewindProposal
          (g0, some tailRewind)
      let gOpened := probeOpenPromptWith gDefer deferPopped? p
      return .paused gOpened hasQueuedPending (pausedPromptSettles gOpened hasQueuedPending p)
    let mut gCur := g0
    let mut curPopped? := popped?
    let mut curP := p
    if let some hadPreBodyCont := rewindProposal then
      let (gRw, poppedRw?) := gCur.rewindAbortedProposalOnLeave departed curPopped? hadPreBodyCont
      let gRw := gRw.popEmptyTopContinuationFrames
      if gRw.sbaPaused then
        let gRw :=
          if curP != .none then
            gRw.chainPendingReplacement (.restorePending curP false promptLog departed none)
          else gRw
        let gRw :=
          match poppedRw? with
          | some popped => gRw.chainPendingReplacement popped
          | none => gRw
        return .paused gRw hasQueuedPending (pausedPromptSettles gRw hasQueuedPending gRw.pending)
      let savedIn? := if curP == .none then none else some curP
      let (gStash, savedOut?, poppedStash?) := gRw.stashPostRewindPending savedIn? poppedRw? departed
      gCur := gStash
      curPopped? := poppedStash?
      curP := savedOut?.getD Pending.none
    let flushUnlessPaysWait (gNext : Game) : Game :=
      if !gNext.sbaPaused && gNext.pending == .none &&
          gNext.currentInterpWait?.any (fun st =>
            match st.stack.back? with | some (.unlessPays ..) => true | _ => false) &&
          (gNext.currentStepEnv.find? (·.1 == ⟨999⟩)).isSome then
        gNext.resumeInterpWaitIfReady
      else gNext
    let resumePopped (gNext : Game) (queued : Bool) (withFlush : Bool := false) : RestoreProbeOutcome :=
      match curPopped? with
      | some popped =>
        let priorCont? := gNext.pendingReplacement
        let gClean := if priorCont?.isSome then gNext.change (.pendingReplacement none) else gNext
        let toRun :=
          match priorCont? with
          | some prior => .seq prior popped
          | none => popped
        .delegate gClean queued toRun
      | none =>
        let gNext := if withFlush then flushUnlessPaysWait gNext else gNext
        if !gNext.over && gNext.pending == .none && gNext.afterRandom == .none then
          match gNext.pendingReplacement with
          | some inner =>
            if inner != pr then
              let gClean := (gNext.change (.pendingReplacement none)).popEmptyTopContinuationFrames
              .delegate gClean queued inner
            else .paused gNext (queued || true) false
          | none => .paused gNext queued false
        else
          let settles :=
            gNext.over || isSelfSettlingPending gNext.pending || gNext.afterRandom != .none ||
              gNext.pendingReplacement.any
                (fun nextPr =>
                  continuationSettlesControlFlow (probeGameForPendingReplacement gNext) queued nextPr)
          .paused gNext (queued || (gNext.pending == .none && gNext.pendingReplacement.isSome)) settles
    let reverseOrPopped (gNext : Game) : RestoreProbeOutcome :=
      if gNext.proposedSpell.isSome then
        let prep := prepareReverseInRestorePending gNext curPopped? departed
        match prep.poppedTail? with
        | some tailSeq =>
          let afterPrompt : PendingReplacement :=
            if followedByFinishChoice then tailSeq.ensureEndsWithFinishResolutionChoice
            else
              match followedByExplicitPriority? with
              | some prio => .seq tailSeq (.receivePriority prio)
              | none => tailSeq
          let toRun : PendingReplacement :=
            match prep.freshCont? with
            | some fc => .seq fc afterPrompt
            | none => afterPrompt
          if prep.hasBlockingPrompt then
            let g1 := if prep.g.continuations.isEmpty then prep.g.change (.pushContinuationFrame {}) else prep.g
            let g2 := if g1.pendingReplacement == some toRun then g1 else g1.change (.pendingReplacement (some toRun))
            let q := if g2.pending == .none && g2.afterRandom != .none then true else hasQueuedPending
            .paused g2 q (pausedPromptSettles g2 q g2.pending)
          else
            let g1 := if prep.g.pendingReplacement.isSome then prep.g.change (.pendingReplacement none) else prep.g
            let g2 := g1.popEmptyTopContinuationFrames
            .delegate g2 hasQueuedPending toRun
        | none =>
          let gAfter :=
            if !prep.g.sbaPaused && prep.g.pending == .none && prep.ckptWasRandom &&
                prep.restoreCkptPending?.isSome && prep.freshCont?.isNone then
              let g1 :=
                if prep.g.pendingReplacement.isSome then prep.g.change (.pendingReplacement none)
                else prep.g
              let g2 :=
                match prep.restoreCkptPending? with
                | some rp => (advanceProbeOnResume g1 false rp).1
                | none => g1
              match prep.restored? with
              | some rest =>
                let g3 := if g2.continuations.isEmpty then g2.change (.pushContinuationFrame {}) else g2
                g3.chainPendingReplacement rest
              | none => g2
            else
              let combinedCont? :=
                seqOptPendingReplacement prep.freshCont?
                  (seqOptPendingReplacement prep.restoreCkptPending? prep.restored?)
              match combinedCont? with
              | some combined =>
                let g1 := if prep.g.continuations.isEmpty then prep.g.change (.pushContinuationFrame {}) else prep.g
                if g1.pendingReplacement == some combined then g1
                else g1.change (.pendingReplacement (some combined))
              | none =>
                let g1 :=
                  if prep.g.pendingReplacement.isSome then prep.g.change (.pendingReplacement none)
                  else prep.g
                if g1.pending == .none && g1.afterRandom == .none then g1.popEmptyTopContinuationFrames else g1
          if followedByFinishChoice && gAfter.sbaPaused then
            let gFinal :=
              if let some cur := gAfter.pendingReplacement then
                let next := cur.ensureEndsWithFinishResolutionChoice
                if next == cur then gAfter else gAfter.change (.pendingReplacement (some next))
              else
                let g1 := if gAfter.continuations.isEmpty then gAfter.change (.pushContinuationFrame {}) else gAfter
                g1.change (.pendingReplacement (some .finishResolutionChoice))
            .paused gFinal hasQueuedPending (pausedPromptSettles gFinal hasQueuedPending gFinal.pending)
          else if let some prio := (if !followedByFinishChoice then followedByExplicitPriority? else none) then
            if gAfter.sbaPaused then
              let g1 := if gAfter.continuations.isEmpty then gAfter.change (.pushContinuationFrame {}) else gAfter
              let gFinal := g1.chainPendingReplacement (.receivePriority prio)
              .paused gFinal hasQueuedPending (pausedPromptSettles gFinal hasQueuedPending gFinal.pending)
            else if gAfter.over then
              .paused gAfter hasQueuedPending true
            else
              .delegate gAfter hasQueuedPending (.receivePriority prio)
          else if gAfter.over || gAfter.sbaPaused then
            .paused gAfter hasQueuedPending
              (if gAfter.over then true else pausedPromptSettles gAfter hasQueuedPending gAfter.pending)
          else if gAfter.pending != .none then
            .paused gAfter false (pausedPromptSettles gAfter false gAfter.pending)
          else if gAfter.afterRandom != .none then
            .paused gAfter (hasQueuedPending || gAfter.pendingReplacement.isSome) true
          else if let some comb := gAfter.pendingReplacement then
            let gClean := (gAfter.change (.pendingReplacement none)).popEmptyTopContinuationFrames
            .delegate gClean hasQueuedPending comb.ensureEndsWithFinishResolutionChoice
          else if !gAfter.continuations.isEmpty || followedByFinishChoice then
            .delegate gAfter hasQueuedPending .finishResolutionChoice
          else if prep.hadConsumedOrig then
            .delegate gAfter hasQueuedPending (.receivePriority (gAfter.priorityInstead prep.caster))
          else
            .paused gAfter false false
      else
        resumePopped gNext hasQueuedPending
    match curP with
    | .none =>
      resumePopped gCur hasQueuedPending (withFlush := true)
    | .resolutionChoice caster (.costPicks ..)
    | .resolutionChoice caster (.crew ..)
    | .resolutionChoice caster (.zemoBoastExile ..)
    | .chooseTeamworkCreatures caster _
    | .sacrificePermanent caster _
    | .discardForAdditionalCost caster =>
      if gCur.proposalCostPromptStillPayable caster curP then
        .paused (probeOpenPromptWith gCur curPopped? curP) hasQueuedPending true
      else reverseOrPopped gCur
    | .activateManaAbilities caster | .chooseX caster
    | .chooseAdditionalCost caster | .chooseKicker caster
    | .chooseGift caster | .chooseTeamwork caster =>
      if !gCur.over && gCur.stillInGame caster &&
          gCur.proposedSpell.any (fun prop =>
            prop.caster == caster &&
              (gCur.findObject? prop.spellId).any (fun o =>
                if prop.kind == .turnFaceUp then o.isOnBattlefield else o.zone == .stack) &&
              gCur.sourceStillPayable prop) then
        .paused (probeOpenPromptWith gCur curPopped? curP) hasQueuedPending true
      else
        reverseOrPopped gCur
    | .chooseLegend q name ids =>
      let liveIds := gCur.validLegendChoiceIds q name ids
      if !gCur.stillInGame q || liveIds.size < 2 then resumePopped gCur hasQueuedPending
      else
        .paused (probeOpenPromptWith gCur curPopped? (.chooseLegend q name liveIds)) hasQueuedPending true
    | .chooseReplacement q choices =>
      if gCur.replacementChoiceValid q choices then
        let gOpened := probeOpenPromptWith gCur curPopped? curP
        .paused gOpened hasQueuedPending (pausedPromptSettles gOpened hasQueuedPending curP)
      else resumePopped gCur hasQueuedPending
    | .assignCombatDamage q forAttackers =>
      let cleanAsgns := gCur.pendingBlockerAssignments.filter fun a =>
        (gCur.findObject? a.source).any (·.isOnBattlefield) &&
          a.toCreatures.all (fun (tid, _) => (gCur.findObject? tid).any (·.isOnBattlefield))
      let gA :=
        if cleanAsgns != gCur.pendingBlockerAssignments then
          gCur.change (.pendingBlockerAssignments cleanAsgns)
        else gCur
      let already := cleanAsgns.map (·.source)
      let playerStillNeeds (r : PlayerId) : Bool :=
        (gA.creaturesAssigningCombatDamage forAttackers).any fun o =>
          (if forAttackers then gA.isOnActiveTeam r && (gA.controllerOf o).any gA.isOnActiveTeam
           else gA.controlledBy o r) &&
            !already.contains o.id &&
            (gA.legalCombatDamageRecipients o forAttackers).size ≥ 2 &&
            gA.combatDamageAmount o > 0
      if gA.stillInGame q && playerStillNeeds q then
        .paused (probeOpenPromptWith gA curPopped? curP) hasQueuedPending true
      else if forAttackers then
        match (if !gA.stillInGame q then
            (gA.teamMembers q).find? (fun r => r != q && gA.stillInGame r && playerStillNeeds r)
          else none) with
        | some r =>
          .paused (probeOpenPromptWith gA curPopped? (.assignCombatDamage r true)) hasQueuedPending true
        | none =>
          let gB :=
            if !gA.stillInGame q && !gA.pendingBlockerAssignments.isEmpty then
              gA.change (.pendingBlockerAssignments #[])
            else gA
          resumePopped gB hasQueuedPending
      else
        match gA.apnapPlayers.find? (fun r =>
            r != q && !gA.isOnActiveTeam r && gA.stillInGame r && playerStillNeeds r) with
        | some r =>
          .paused (probeOpenPromptWith gA curPopped? (.assignCombatDamage r false)) hasQueuedPending true
        | none =>
          resumePopped gA hasQueuedPending
    | .resolutionChoice q (.tricksterLibrary caster id connive sourceId) =>
      if gCur.stillInGame q && gCur.stillInGame caster &&
          (gCur.findObject? id).any (fun o => o.isOnBattlefield && gCur.isCreature o) then
        .paused (probeOpenPromptWith gCur curPopped? curP) hasQueuedPending true
      else if gCur.stillInGame caster && connive.isSome then
        let outerCont? := gCur.pendingReplacement
        let g1 := if outerCont?.isSome then gCur.change (.pendingReplacement none) else gCur
        if curPopped?.isSome then
          let g1 := g1.chainPendingReplacement (.finishPostStep (.conniveTricksterTarget caster connive sourceId))
          let g1 :=
            match outerCont? with
            | some outer => g1.chainPendingReplacement outer
            | none => g1
          resumePopped g1 hasQueuedPending
        else
          let g1 :=
            if let .chooseReplacement .. := g1.pending then
              g1.chainPendingReplacement (.finishPostStep (.conniveTricksterTarget caster connive sourceId))
            else
              g1.conniveTricksterTarget caster connive (sourceId := sourceId)
          let g1 :=
            match outerCont? with
            | some outer => g1.chainPendingReplacement outer
            | none => g1
          if g1.over || g1.pending != .none || g1.afterRandom != .none then
            .paused g1 hasQueuedPending
              (if g1.over then true else pausedPromptSettles g1 hasQueuedPending g1.pending)
          else
            resumePopped g1 hasQueuedPending
      else
        resumePopped gCur hasQueuedPending
    | _ =>
      let promptSeat? : Option PlayerId :=
        match curP with
        | .declareAttackers => some gCur.activePlayer
        | .declareBlockers => some gCur.currentBlockersPlayer
        | .resolveRandom (.chooseObject _) | .resolveRandom (.chooseIndex _) =>
          if gCur.pregameRandom == .none then
            gCur.afterRandom.player?.orElse (fun _ => gCur.currentResolvingContext?.bind Prod.snd)
          else curP.promptPlayer?
        | _ => curP.promptPlayer?
      let effectiveDeparted :=
        match promptSeat? with
        | some q =>
          if !gCur.stillInGame q then #[q] ++ departed.filter (· != q)
          else departed
        | none => departed
      if effectiveDeparted.isEmpty then
        match curP with
        | .resolveRandom (.chooseObject ids) =>
          if ids.any (fun id => (gCur.findObject? id).isNone) then
            let liveIds := ids.filter (fun id => (gCur.findObject? id).isSome)
            if gCur.afterRandom.player?.any (fun r => !gCur.stillInGame r) then
              let g1 := gCur.changes #[.afterRandom .none, .stashedCause none]
              resumePopped g1 hasQueuedPending
            else if liveIds.isEmpty then
              match gCur.afterRandom with
              | .revealRandomCreatureThenBottom ctrl revealed =>
                if gCur.stillInGame ctrl then
                  let cause := gCur.stashedCause
                  let outerCont? := gCur.pendingReplacement
                  let g1 :=
                    gCur.changes
                      (#[EngineChange.afterRandom .none, EngineChange.stashedCause none] ++
                       (if outerCont?.isSome then #[EngineChange.pendingReplacement none] else #[]))
                  let g1 := g1.putRestOnBottomRandom ctrl
                    (revealed.filter (fun id => (g1.findObject? id).isSome))
                    (cause := cause)
                  let g1 :=
                    match outerCont? with
                    | some outer => g1.chainPendingReplacement outer
                    | none => g1
                  if g1.pending != .none then
                    let g1 :=
                      match curPopped? with
                      | some popped => g1.chainPendingReplacement popped
                      | none => g1
                    .paused g1 hasQueuedPending (pausedPromptSettles g1 hasQueuedPending g1.pending)
                  else
                    resumePopped g1 hasQueuedPending
                else
                  let g1 := gCur.changes #[.afterRandom .none, .stashedCause none]
                  resumePopped g1 hasQueuedPending
              | _ =>
                let g1 := gCur.changes #[.afterRandom .none, .stashedCause none]
                resumePopped g1 hasQueuedPending
            else if liveIds.size == 1 then
              let outerCont? := gCur.pendingReplacement
              let g1 := if outerCont?.isSome then gCur.change (.pendingReplacement none) else gCur
              let g1 := g1.autoResolveSingleChooseObjectCore liveIds[0]!
              let g1 :=
                match outerCont? with
                | some outer => g1.chainPendingReplacement outer
                | none => g1
              if g1.pending != .none then
                let g1 :=
                  match curPopped? with
                  | some popped => g1.chainPendingReplacement popped
                  | none => g1
                .paused g1 hasQueuedPending (pausedPromptSettles g1 hasQueuedPending g1.pending)
              else
                resumePopped g1 hasQueuedPending
            else
              .paused (probeOpenPromptWith gCur curPopped? (.resolveRandom (.chooseObject liveIds)))
                hasQueuedPending true
          else
            .paused (probeOpenPromptWith gCur curPopped? curP) hasQueuedPending true
        | _ =>
          let gOpened := probeOpenPromptWith gCur curPopped? curP
          .paused gOpened hasQueuedPending (pausedPromptSettles gOpened hasQueuedPending curP)
      else
        let gProbe0 :=
          if gCur.pending != .none then gCur.change (.pending .none) else gCur
        let (gAfter, nextP) := effectiveDeparted.foldl (fun (acc, nextCurP) dep =>
          if nextCurP == .none then (acc, .none)
          else acc.redirectPendingAfterLeave dep (pending := nextCurP)) (gProbe0, curP)
        if nextP != .none || gAfter.pending != .none then
          let effP := if nextP != .none then nextP else gAfter.pending
          let gOpened := probeOpenPromptWith gAfter curPopped? effP
          .paused gOpened hasQueuedPending (pausedPromptSettles gOpened hasQueuedPending effP)
        else
          resumePopped gAfter hasQueuedPending (withFlush := true)
  | _ => .paused g hasQueuedPending false

private partial def probeLeavePlayersWhoLost (g : Game) (hasQueuedPending : Bool)
    (savedPending : Option Pending) (popOuter : Bool)
    (departed : Array PlayerId) (rewindProposal : Option Bool)
    (fromEventIdx? : Option Nat := none) : RestoreProbeOutcome :=
  let g1 :=
    drainProbeNonPriorityCont g
      (.leavePlayersWhoLost savedPending popOuter departed rewindProposal fromEventIdx?)
  if g1.over || g1.pending != .none || g1.afterRandom != .none then
    .paused g1 hasQueuedPending
      (if g1.over then true else pausedPromptSettles g1 hasQueuedPending g1.pending)
  else
    match g1.pendingReplacement with
    | some rp =>
      let gClean := (g1.change (.pendingReplacement none)).popEmptyTopContinuationFrames
      .delegate gClean hasQueuedPending rp
    | none =>
      .paused g1 hasQueuedPending false

/-- Advance probe `Game` (popping consumed `outerPendingReplacements` frames) and
track whether resuming a `PendingReplacement` step leaves a freshly queued
continuation unresumed on `g.pendingReplacement` while `g.pending == .none` so
the next step in `.seq` immediately runs with `g.pendingReplacement.isSome`. -/
private partial def advanceProbeOnResumeCore (g : Game) (hasQueuedPending : Bool)
    (pr : PendingReplacement)
    (followedByFinishChoice : Bool := false)
    (followedByExplicitPriority? : Option PlayerId := none) : ProbeAdvanceResult :=
  match pr with
  | .seq a b =>
    let (resA, _, _) :=
      seqFollowForReversal g hasQueuedPending a b followedByFinishChoice followedByExplicitPriority?
    let openedNewPrompt :=
      (g.pending == .none && resA.game.pending != .none) ||
      (g.afterRandom == .none && resA.game.afterRandom != .none)
    if resA.reversedProposal then
      resA
    else if !g.over && resA.game.over && !b.hasCheckpointReplay then
      resA
    else if openedNewPrompt then
      { game := resA.game.chainPendingReplacement b, hasQueuedPending := true }
    else
      advanceProbeOnResumeCore resA.game resA.hasQueuedPending b
        followedByFinishChoice followedByExplicitPriority?
  | .continueConnives _ ids =>
    { game := g, hasQueuedPending := if ids.size > 1 && g.afterRandom != .none then true else hasQueuedPending }
  | pr@(.restorePending _ _ _ _ rewindProposal) =>
    match probeRestorePendingCore g hasQueuedPending pr
        followedByFinishChoice followedByExplicitPriority? with
    | .paused g' q' _ =>
      let revHere := rewindProposal.isNone && !g.hasActiveManaProposalCheckpoint &&
        g.proposedSpell.isSome && g.proposalCheckpoint.isSome && g'.proposedSpell.isNone
      { game := g', hasQueuedPending := q',
        reversedProposal := revHere,
        preReverseGame? := if revHere then some g else none }
    | .delegate g' q' nextPr =>
      let revHere := rewindProposal.isNone && !g.hasActiveManaProposalCheckpoint &&
        g.proposedSpell.isSome && g.proposalCheckpoint.isSome && g'.proposedSpell.isNone
      let res := advanceProbeOnResumeCore g' q' nextPr followedByFinishChoice followedByExplicitPriority?
      { res with
        reversedProposal := res.reversedProposal || revHere,
        preReverseGame? := res.preReverseGame? <|> (if revHere then some g else none) }
  | .leavePlayersWhoLost savedPending popOuter departed rewindProposal fromEventIdx? =>
    match probeLeavePlayersWhoLost g hasQueuedPending savedPending popOuter departed rewindProposal fromEventIdx? with
    | .paused g' q' _ =>
      { game := g', hasQueuedPending := q',
        reversedProposal := false,
        preReverseGame? := none }
    | .delegate g' q' nextPr =>
      advanceProbeOnResumeCore g' q' nextPr followedByFinishChoice followedByExplicitPriority?
  | .finishResolutionChoice | .receivePriority _ =>
    { game := g, hasQueuedPending := if g.afterRandom == .none then false else hasQueuedPending }
  | .finishPostCast caster grantPriority hadOuter _ =>
    let clearChanges : Array EngineChange :=
      (if g.proposedSpell.isSome then #[.proposedSpell none] else #[]) ++
      (if g.proposalCheckpoint.isSome then #[.clearProposalCheckpoint] else #[]) ++
      #[.castingFromTop false]
    let g1 := simulateFinishPostCastBody (g.changes clearChanges) caster
    if !grantPriority || hadOuter then
      { game := g1, hasQueuedPending := if g1.pending != .none || g1.afterRandom != .none then true else hasQueuedPending }
    else
      { game := g1, hasQueuedPending := if g1.pending != .none || g1.afterRandom != .none then true else false }
  | .finishBecomeCast caster spellId grantPriority hadOuter _ =>
    if let .chooseReplacement .. := g.pending then
      { game := g.change (.consecutivePasses 0), hasQueuedPending := true }
    else
      let clearChanges : Array EngineChange :=
        (if g.proposedSpell.isSome then #[.proposedSpell none] else #[]) ++
        (if g.proposalCheckpoint.isSome then #[.clearProposalCheckpoint] else #[]) ++
        #[.castingFromTop false]
      if g.stillInGame caster && (g.findObject? spellId).any (·.zone == .stack) then
        let g1 := g.changes clearChanges
        let g1 :=
          match g1.findObject? spellId with
          | some sp => g1.putCastTriggersOnStack caster sp
          | none => g1
        if g1.over || g1.pending != .none || g1.afterRandom != .none then
          { game := g1, hasQueuedPending := true }
        else if spellOpensAncestryScry g1 caster spellId then
          { game := g1.beginScry caster 1, hasQueuedPending := true }
        else
          let g2 := simulateFinishPostCastBody g1 caster
          if !grantPriority || hadOuter then
            { game := g2, hasQueuedPending := if g2.pending != .none || g2.afterRandom != .none then true else hasQueuedPending }
          else
            { game := g2, hasQueuedPending := if g2.pending != .none || g2.afterRandom != .none then true else false }
      else if g.proposedSpell.isSome && g.proposalCheckpoint.isSome then
        let gR := g.reverseProposedSpell (resumeContinuation := true)
          (followedByFinishChoice := followedByFinishChoice)
          (followedByExplicitPriority? := followedByExplicitPriority?)
        { game := gR,
          hasQueuedPending := if gR.pending != .none || gR.afterRandom != .none then true else hasQueuedPending,
          reversedProposal := gR.proposedSpell.isNone,
          preReverseGame? := if gR.proposedSpell.isNone then some g else none }
      else
        { game := g.changes clearChanges, hasQueuedPending := if !grantPriority || hadOuter then hasQueuedPending else false }
  | .finishProposedSpellCosts stage grantPriority hadOuter openCont =>
    match g.proposedSpell with
    | none => { game := g, hasQueuedPending }
    | some prop =>
      if let .chooseReplacement .. := g.pending then
        -- `finishProposedSpellCosts` (`Decisions.lean:5526-5528`) returns immediately
        -- while `.chooseReplacement` is open (for every stage) without inspecting
        -- stage failures, sacrifice/discard costs, or permanent status.
        { game := g.change (.consecutivePasses 0), hasQueuedPending := true }
      else
        let reverseFrom (gRev : Game) : ProbeAdvanceResult :=
          if gRev.proposalCheckpoint.isSome then
            let gR := gRev.reverseProposedSpell (resumeContinuation := true)
              (followedByFinishChoice := followedByFinishChoice)
              (followedByExplicitPriority? := followedByExplicitPriority?)
            { game := gR,
              hasQueuedPending := if gR.pending != .none || gR.afterRandom != .none then true else hasQueuedPending,
              reversedProposal := gR.proposedSpell.isNone,
              preReverseGame? := if gR.proposedSpell.isNone then some gRev else none }
          else { game := gRev, hasQueuedPending }
        match projectProposedSpellCostStages g prop stage grantPriority hadOuter openCont with
        | .failed => reverseFrom g
        | .paused gP => { game := gP, hasQueuedPending := true }
        | .ready gFin =>
          let clearChanges : Array EngineChange :=
            #[.proposedSpell none] ++
            (if gFin.proposalCheckpoint.isSome then #[.clearProposalCheckpoint] else #[]) ++
            #[.castingFromTop false]
          let excludeId := prop.sourceId.getD prop.spellId
          if prop.needsSacrificeOther &&
              !(gFin.sacrificeCreatureOrArtifactChoices prop.caster excludeId).isEmpty then
            { game := gFin.change (.pending (.sacrificePermanent prop.caster excludeId)), hasQueuedPending := true }
          else if prop.needsSacrificeOther then reverseFrom gFin
          else if prop.needsDiscardCard && !(gFin.discardableHandIds prop.caster).isEmpty then
            { game := gFin.change (.pending (.discardForAdditionalCost prop.caster)), hasQueuedPending := true }
          else if prop.needsDiscardCard then reverseFrom gFin
          else if prop.kind == .turnFaceUp then
            if !(gFin.stillInGame prop.caster &&
                (gFin.findObject? prop.spellId).any (fun o =>
                  o.isOnBattlefield && o.status.faceDown && gFin.controlledBy o prop.caster)) then
              reverseFrom gFin
            else
              let selfLeaf : PendingReplacement :=
                .finishProposedSpellCosts .finalize grantPriority hadOuter openCont
              let localOuter? :=
                gFin.pendingReplacement.bind (removeExactPendingReplacement selfLeaf)
              let effHadOuter := hadOuter || localOuter?.isSome
              let wrapOuter (outer : PendingReplacement) : PendingReplacement :=
                if hadOuter then outer else outer.ensureEndsWithFinishResolutionChoice
              let g0 :=
                let g0 := if gFin.pendingReplacement.isSome then gFin.change (.pendingReplacement none) else gFin
                g0.changes #[.pending .none, .consecutivePasses 0]
              let (g1, callerShouldResume) :=
                g0.completeTurnFaceUp prop.caster prop.spellId (hadOuterReplacement := effHadOuter)
                  (followedByFinishChoice := followedByFinishChoice)
                  (followedByExplicitPriority? := followedByExplicitPriority?)
              let g1 :=
                match localOuter? with
                | some outer => g1.chainPendingReplacement (wrapOuter outer)
                | none => g1
              let paused := match g1.pending with | .chooseReplacement .. => true | _ => false
              let g1 :=
                if !paused && !hadOuter && (callerShouldResume ||
                    (g1.pending == .none && !g1.over && localOuter?.isSome)) then
                  g1.resumeAfterBecomeCastFwd
                else g1
              { game := g1, hasQueuedPending := if g1.pending != .none || g1.afterRandom != .none then true else if hadOuter then hasQueuedPending else false }
          else if gFin.stillInGame prop.caster && (gFin.findObject? prop.spellId).any (·.zone == .stack) then
            let g1 := gFin.changes clearChanges
            let g1 :=
              match g1.findObject? prop.spellId with
              | some sp => g1.putCastTriggersOnStack prop.caster sp
              | none => g1
            if g1.over || g1.pending != .none || g1.afterRandom != .none then
              { game := g1, hasQueuedPending := true }
            else if spellOpensAncestryScry g1 prop.caster prop.spellId then
              { game := g1.beginScry prop.caster 1, hasQueuedPending := true }
            else
              let g2 := simulateFinishPostCastBody g1 prop.caster
              { game := g2, hasQueuedPending := if g2.pending != .none || g2.afterRandom != .none then true else if hadOuter then hasQueuedPending else false }
          else reverseFrom gFin
  | .completeActivation hadOuter openCont =>
    if let .chooseReplacement .. := g.pending then
      { game := g.change (.consecutivePasses 0), hasQueuedPending := true }
    else
      match g.proposedSpell with
      | none => { game := g, hasQueuedPending }
      | some prop =>
        let reverseFrom (gRev : Game) : ProbeAdvanceResult :=
          if gRev.proposalCheckpoint.isSome then
            let gR := gRev.reverseProposedSpell (resumeContinuation := true)
              (followedByFinishChoice := followedByFinishChoice)
              (followedByExplicitPriority? := followedByExplicitPriority?)
            { game := gR,
              hasQueuedPending := if gR.pending != .none || gR.afterRandom != .none then true else hasQueuedPending,
              reversedProposal := gR.proposedSpell.isNone,
              preReverseGame? := if gR.proposedSpell.isNone then some gRev else none }
          else { game := gRev, hasQueuedPending }
        match prop.sourceId with
        | none => reverseFrom g
        | some sid =>
          let x := ((g.findObject? prop.spellId).bind (·.chosenX)).getD 0
          let srcSnap := (g.findObject? sid).map g.snapshot |>.orElse (fun _ => some prop.originalSnapshot)
          let fallbackName :=
            if prop.originalSnapshot.name.isEmpty then g.name prop.original
            else prop.originalSnapshot.name
          let srcName := (g.findObject? sid).map g.name |>.getD fallbackName
          let localOuter? := g.pendingReplacement
          let effHadOuter := hadOuter || localOuter?.isSome
          let wrapOuter (outer : PendingReplacement) : PendingReplacement :=
            if hadOuter then outer else outer.ensureEndsWithFinishResolutionChoice
          let g0 := if localOuter?.isSome then g.change (.pendingReplacement none) else g
          match g0.payActivationExtraCosts prop.caster sid prop.tapSource prop.sacrificeSource
              prop.payLife prop.discardSource prop.activation (if prop.removePlusOneX then x else 0)
              (callerOuter? := localOuter?)
              (followedByFinishChoice := followedByFinishChoice)
              (followedByExplicitPriority? := followedByExplicitPriority?) with
          | .error _ => reverseFrom g
          | .ok g1 =>
            if g1.proposedSpell.isNone then
              { game := g1,
                hasQueuedPending := if g1.pending != .none || g1.afterRandom != .none then true else hasQueuedPending,
                reversedProposal := g.proposalCheckpoint.isSome,
                preReverseGame? := if g.proposalCheckpoint.isSome then some g else none }
            else if prop.needsSacrificeOther then
              if let .chooseReplacement .. := g1.pending then
                let gP := (g1.change (.consecutivePasses 0)).chainPendingReplacement
                  (.restorePending (.sacrificePermanent prop.caster sid))
                let gP :=
                  match localOuter? with
                  | some outer => gP.chainPendingReplacement outer
                  | none => gP
                { game := gP, hasQueuedPending := true }
              else if (g1.sacrificeCreatureOrArtifactChoices prop.caster sid).isEmpty then
                reverseFrom g
              else
                let gP :=
                  match localOuter? with
                  | some outer => g1.chainPendingReplacement outer
                  | none => g1
                { game := gP.change (.pending (.sacrificePermanent prop.caster sid)), hasQueuedPending := true }
            else if let .chooseReplacement .. := g1.pending then
              let gP := (g1.change (.consecutivePasses 0)).chainPendingReplacement
                (.finishBecomeActivated prop.caster srcName prop.sourceId prop.activation
                  (some prop.spellId) srcSnap (some prop.original) effHadOuter openCont)
              let gP :=
                match localOuter? with
                | some outer => gP.chainPendingReplacement (wrapOuter outer)
                | none => gP
              { game := gP, hasQueuedPending := true }
            else
              let g2 :=
                match localOuter? with
                | some outer => g1.chainPendingReplacement (wrapOuter outer)
                | none => g1
              let g2 := g2.changes #[.pending .none, .consecutivePasses 0]
              advanceProbeOnResumeCore g2 hasQueuedPending
                (.finishBecomeActivated prop.caster srcName prop.sourceId prop.activation
                  (some prop.spellId) srcSnap (some prop.original) effHadOuter openCont)
                followedByFinishChoice followedByExplicitPriority?
  | .finishBecomeActivated caster srcName srcId act abId srcSnap srcOrig hadOuter openCont =>
    if let .chooseReplacement .. := g.pending then
      { game := g.change (.consecutivePasses 0), hasQueuedPending := true }
    else
      let activation := act <|> g.proposedSpell.bind (·.activation)
      let abilityId := abId <|> g.proposedSpell.map (·.spellId) <|> g.stack.back?.map (·.objectId)
      let chosenX := ((abilityId.bind g.findObject?).bind (·.chosenX)).getD 0
      let sinceIdx := (g.targetProposalCheckpoint?.map (·.eventsSize)).getD 0
      let unpaidLoyaltyUnpayable : Bool :=
        match activation.bind (·.cost.netLoyaltyDelta chosenX) with
        | none => false
        | some k =>
          if g.proposedSpell.any ProposedSpell.loyaltyPaid ||
              srcId.any (fun sid =>
                g.sourceCounterCostPaidFor sid abilityId .loyalty (some .loyalty) sinceIdx) then
            false
          else
            match srcId.bind g.findObject? with
            | none => true
            | some src =>
              !src.isOnBattlefield || !g.controlledBy src caster ||
                g.loyaltyActivatedThisTurn src.id ||
                (k < 0 && (src.status.loyaltyCounters : Int) < -k)
      if unpaidLoyaltyUnpayable then
        if g.proposedSpell.isSome && g.proposalCheckpoint.isSome then
          let gR := g.reverseProposedSpell (resumeContinuation := true)
            (followedByFinishChoice := followedByFinishChoice)
            (followedByExplicitPriority? := followedByExplicitPriority?)
          { game := gR,
            hasQueuedPending := if gR.pending != .none || gR.afterRandom != .none then true else hasQueuedPending,
            reversedProposal := gR.proposedSpell.isNone,
            preReverseGame? := if gR.proposedSpell.isNone then some g else none }
        else
          let clearChanges : Array EngineChange :=
            (if g.proposedSpell.isSome then #[.proposedSpell none] else #[]) ++
            (if g.proposalCheckpoint.isSome then #[.clearProposalCheckpoint] else #[])
          { game := g.changes clearChanges, hasQueuedPending := if hadOuter then hasQueuedPending else false }
      else
        let localOuter? := g.pendingReplacement
        let effHadOuter := hadOuter || localOuter?.isSome
        let wrapOuter (outer : PendingReplacement) : PendingReplacement :=
          if hadOuter then outer else outer.ensureEndsWithFinishResolutionChoice
        let g0 := if localOuter?.isSome then g.change (.pendingReplacement none) else g
        let gL :=
          match activation.bind (·.cost.netLoyaltyDelta chosenX) with
          | some k =>
            match srcId.bind g0.findObject? with
            | some src =>
              if !(g0.proposedSpell.any ProposedSpell.loyaltyPaid) &&
                  !g0.sourceCounterCostPaidFor src.id abilityId .loyalty (some .loyalty) sinceIdx then
                g0.payLoyaltyDelta caster src k (forObject := abilityId)
              else g0
            | none => g0
          | none => g0
        if let .chooseReplacement .. := gL.pending then
          let gP := gL.chainPendingReplacement
            (.finishPostLoyaltyActivated caster srcName srcId activation abilityId srcSnap srcOrig
              effHadOuter openCont)
          let gP :=
            match localOuter? with
            | some outer => gP.chainPendingReplacement (wrapOuter outer)
            | none => gP
          { game := gP, hasQueuedPending := true }
        else
          let gL :=
            match localOuter? with
            | some outer => gL.chainPendingReplacement (wrapOuter outer)
            | none => gL
          advanceProbeOnResumeCore gL hasQueuedPending
            (.finishPostLoyaltyActivated caster srcName srcId activation abilityId srcSnap srcOrig
              effHadOuter openCont)
            followedByFinishChoice followedByExplicitPriority?
  | .finishPostLoyaltyActivated caster _ srcId _ abId _ _ hadOuter _ =>
    if g.over || !g.stillInGame caster ||
        !abId.all (fun aid => srcId == some aid || (g.findObject? aid).any (·.zone == .stack)) then
      if g.proposedSpell.isSome && g.proposalCheckpoint.isSome then
        let gR := g.reverseProposedSpell (resumeContinuation := true)
          (followedByFinishChoice := followedByFinishChoice)
          (followedByExplicitPriority? := followedByExplicitPriority?)
        { game := gR,
          hasQueuedPending := if gR.pending != .none || gR.afterRandom != .none then true else hasQueuedPending,
          reversedProposal := gR.proposedSpell.isNone,
          preReverseGame? := if gR.proposedSpell.isNone then some g else none }
      else
        let clearChanges : Array EngineChange :=
          (if g.proposedSpell.isSome then #[.proposedSpell none] else #[]) ++
          (if g.proposalCheckpoint.isSome then #[.clearProposalCheckpoint] else #[])
        { game := g.changes clearChanges, hasQueuedPending := if hadOuter then hasQueuedPending else false }
    else
      let clearChanges : Array EngineChange :=
        (if g.proposedSpell.isSome then #[.proposedSpell none] else #[]) ++
        (if g.proposalCheckpoint.isSome then #[.clearProposalCheckpoint] else #[])
      { game := g.changes clearChanges, hasQueuedPending := if hadOuter then hasQueuedPending else false }
  | .finishTurnFaceUp caster spellId hadOuter =>
    match prepareGameForTurnFaceUpProbe g caster spellId hadOuter with
    | none => { game := g, hasQueuedPending := true }
    | some gClean =>
      if gClean.stillInGame caster &&
          (gClean.findObject? spellId).any (fun o =>
            o.isOnBattlefield && o.status.faceDown && gClean.controlledBy o caster) then
        let (g1, callerShouldResume) := gClean.completeTurnFaceUp caster spellId (hadOuterReplacement := hadOuter)
          (followedByFinishChoice := followedByFinishChoice)
          (followedByExplicitPriority? := followedByExplicitPriority?)
        let g1 := if callerShouldResume && !hadOuter then g1.resumeAfterBecomeCastFwd else g1
        { game := g1, hasQueuedPending := if g1.pending != .none || g1.afterRandom != .none then true else if hadOuter then hasQueuedPending else false }
      else if gClean.proposedSpell.isSome && gClean.proposalCheckpoint.isSome then
        let gR := gClean.reverseProposedSpell (resumeContinuation := true)
          (followedByFinishChoice := followedByFinishChoice)
          (followedByExplicitPriority? := followedByExplicitPriority?)
        { game := gR,
          hasQueuedPending := if gR.pending != .none || gR.afterRandom != .none then true else hasQueuedPending,
          reversedProposal := gR.proposedSpell.isNone,
          preReverseGame? := if gR.proposedSpell.isNone then some gClean else none }
      else
        let (g1, callerShouldResume) := gClean.completeTurnFaceUp caster spellId (hadOuterReplacement := hadOuter)
          (followedByFinishChoice := followedByFinishChoice)
          (followedByExplicitPriority? := followedByExplicitPriority?)
        let g1 := if callerShouldResume && !hadOuter then g1.resumeAfterBecomeCastFwd else g1
        { game := g1, hasQueuedPending := if g1.pending != .none || g1.afterRandom != .none then true else if hadOuter then hasQueuedPending else false }
  | .finishPostStep (.resumeChooseModeAfterLeave p) =>
    if let .chooseReplacement .. := g.pending then { game := g, hasQueuedPending := true }
    else
      let g1 := runPostStep g (.resumeChooseModeAfterLeave p)
        (followedByFinishChoice := followedByFinishChoice)
        (followedByExplicitPriority? := followedByExplicitPriority?)
      let rev := !g.hasActiveManaProposalCheckpoint && g.proposedSpell.isSome && g.proposalCheckpoint.isSome && g1.proposedSpell.isNone
      { game := g1,
        hasQueuedPending := if g1.pending != .none || g1.afterRandom != .none then true else hasQueuedPending,
        reversedProposal := rev,
        preReverseGame? := if rev then some g else none }
  | .finishPostStep (.resumeChooseTargetsAfterLeave p) =>
    if let .chooseReplacement .. := g.pending then { game := g, hasQueuedPending := true }
    else
      let g1 := runPostStep g (.resumeChooseTargetsAfterLeave p)
        (followedByFinishChoice := followedByFinishChoice)
        (followedByExplicitPriority? := followedByExplicitPriority?)
      let rev := !g.hasActiveManaProposalCheckpoint && g.proposedSpell.isSome && g.proposalCheckpoint.isSome && g1.proposedSpell.isNone
      { game := g1,
        hasQueuedPending := if g1.pending != .none || g1.afterRandom != .none then true else hasQueuedPending,
        reversedProposal := rev,
        preReverseGame? := if rev then some g else none }
  | .finishPostStep .afterTriggerTargetsChosen =>
    if g.sbaPaused then { game := g, hasQueuedPending := true }
    else
      let g0 :=
        match g.pending with
        | .chooseTargets _ => g.change (.pending .none)
        | _ => g
      if g0.pending != .none || g0.afterRandom != .none then
        { game := g0, hasQueuedPending := true }
      else if g0.triggerNeedingTargets.isSome then
        let g1 := g0.promptTriggerTargetsIfNeeded
        { game := g1,
          hasQueuedPending := if g1.pending != .none || g1.afterRandom != .none then true else false }
      else if g0.proposedSpell.any (fun prop =>
          !g0.stillInGame prop.caster || (g0.findObject? prop.spellId).isNone) then
        let g1 := g0.afterTriggerTargetsChosen
        let rev := !g0.hasActiveManaProposalCheckpoint && g0.proposedSpell.isSome && g0.proposalCheckpoint.isSome && g1.proposedSpell.isNone
        { game := g1,
          hasQueuedPending := if g1.pending != .none || g1.afterRandom != .none then true else hasQueuedPending,
          reversedProposal := rev,
          preReverseGame? := if rev then some g0 else none }
      else
        { game := g0, hasQueuedPending := if g0.afterRandom == .none then false else hasQueuedPending }
  | .finishPostStep (.resumeTriggerModesAfterLeave p objectId remaining chosen) =>
    if g.over || !g.stillInGame p then
      { game := g, hasQueuedPending := if g.afterRandom == .none then false else hasQueuedPending }
    else
      match g.findObject? objectId with
      | some obj =>
        if obj.zone != .stack then
          { game := g, hasQueuedPending := if g.afterRandom == .none then false else hasQueuedPending }
        else
          let tModes := g.triggerModesOf obj
          let validChosen := chosen.filter (fun i =>
            tModes[i]?.any (g.triggerModeChoosable p obj))
          let needed := remaining + (chosen.size - validChosen.size)
          let choosableLeft :=
            ((List.range tModes.size).filter (fun i =>
              !validChosen.contains i && (tModes[i]?.any (g.triggerModeChoosable p obj)))).length
          if needed == 0 then
            let sorted := validChosen.qsort (· < ·)
            let g1 := g.record (GameEvent.announced g.turnNumber obj.id (modes := sorted))
            let g1 :=
              match combineTriggerModes (tModes.map (fun m => g1.expandEachOpponentEffect p m (some obj.id))) sorted with
              | none => g1
              | some eff =>
                let g1 := g1.changeObject obj.id (.abilityEffect (some eff))
                if !eff.requiresTarget then g1.change (.stackEntry obj.id (.targetsAnnounced true)) else g1
            { game := g1, hasQueuedPending := if g1.afterRandom == .none then false else hasQueuedPending }
          else if choosableLeft < needed then
            let g1 := g.ceaseToExist obj.id (cause := some (.gameRule .noLegalMode))
            { game := g1, hasQueuedPending := if g1.afterRandom == .none then false else hasQueuedPending }
          else
            let g1 := g.change (.pending (.resolutionChoice p (.triggerModes obj.id needed validChosen)))
            { game := g1, hasQueuedPending := true }
      | none =>
        { game := g, hasQueuedPending := if g.afterRandom == .none then false else hasQueuedPending }
  | .finishPostStep (.resumeUpToTriggerModesAfterLeave p objectId remaining chosen) =>
    if g.over || !g.stillInGame p then
      { game := g, hasQueuedPending := if g.afterRandom == .none then false else hasQueuedPending }
    else
      match g.findObject? objectId with
      | some obj =>
        if obj.zone != .stack then
          { game := g, hasQueuedPending := if g.afterRandom == .none then false else hasQueuedPending }
        else
          let modes := g.triggerModesOf obj
          let validChosen := chosen.filter (fun i =>
            modes[i]?.any (g.triggerModeChoosable p obj))
          let remaining := remaining + (chosen.size - validChosen.size)
          let anyChoosableLeft :=
            (List.range modes.size).any (fun i =>
              !validChosen.contains i && (modes[i]?.any (g.triggerModeChoosable p obj)))
          if remaining > 0 && anyChoosableLeft then
            let g1 := g.change (.pending (.resolutionChoice p (.upToTriggerModes obj.id remaining validChosen)))
            { game := g1, hasQueuedPending := true }
          else if validChosen.isEmpty then
            let noop : Effect := { body := .noop }
            let g1 := g.record (GameEvent.announced g.turnNumber obj.id (modes := #[]))
            let g1 := g1.changes #[
              .object obj.id (.abilityEffect (some noop)),
              .stackEntry obj.id (.targetsAnnounced true)]
            { game := g1, hasQueuedPending := if g1.afterRandom == .none then false else hasQueuedPending }
          else
            let sorted := validChosen.qsort (· < ·)
            let g1 := g.record (GameEvent.announced g.turnNumber obj.id (modes := sorted))
            let g1 :=
              match combineTriggerModes (modes.map (fun m => g1.expandEachOpponentEffect p m (some obj.id))) sorted with
              | none => g1
              | some eff =>
                let g1 := g1.changeObject obj.id (.abilityEffect (some eff))
                if !eff.requiresTarget then g1.change (.stackEntry obj.id (.targetsAnnounced true)) else g1
            { game := g1, hasQueuedPending := if g1.afterRandom == .none then false else hasQueuedPending }
      | none =>
        { game := g, hasQueuedPending := if g.afterRandom == .none then false else hasQueuedPending }
  | .finishPostStep (.resumeHawkeyeModesAfterLeave p objectId left chosen) =>
    if g.over || !g.stillInGame p then
      { game := g, hasQueuedPending := if g.afterRandom == .none then false else hasQueuedPending }
    else
      match g.findObject? objectId with
      | some obj =>
        if obj.zone != .stack then
          { game := g, hasQueuedPending := if g.afterRandom == .none then false else hasQueuedPending }
        else
          let validChosen := chosen.filter (fun i =>
            hawkeyeModeEffects[i]?.any (g.triggerModeChoosable p obj))
          let anyMoreChoosable :=
            (List.range hawkeyeModeEffects.size).any (fun i =>
              !validChosen.contains i && (hawkeyeModeEffects[i]?.any (g.triggerModeChoosable p obj)))
          if validChosen.size < left && anyMoreChoosable then
            let g1 := g.change (.pending (.resolutionChoice p (.hawkeyeModes left validChosen (some obj.id))))
            { game := g1, hasQueuedPending := true }
          else
            let sorted := validChosen.qsort (· < ·)
            let eff : Effect :=
              if sorted.isEmpty then { body := .noop }
              else hawkeyeArrowsEffect sorted
            let g1 := g.record (GameEvent.announced g.turnNumber obj.id (modes := sorted))
            let g1 := g1.changeObject obj.id (.abilityEffect (some eff))
            let g1 := if !eff.requiresTarget then g1.change (.stackEntry obj.id (.targetsAnnounced true)) else g1
            { game := g1, hasQueuedPending := if g1.afterRandom == .none then false else hasQueuedPending }
      | none =>
        { game := g, hasQueuedPending := if g.afterRandom == .none then false else hasQueuedPending }
  | .finishPostStep (.resumeProposalCostAfterLeave p savedP) =>
    if let .chooseReplacement .. := g.pending then { game := g, hasQueuedPending := true }
    else
      let g1 := runPostStep g (.resumeProposalCostAfterLeave p savedP)
        (followedByFinishChoice := followedByFinishChoice)
        (followedByExplicitPriority? := followedByExplicitPriority?)
      let rev := !g.hasActiveManaProposalCheckpoint && g.proposedSpell.isSome && g.proposalCheckpoint.isSome && g1.proposedSpell.isNone
      { game := g1,
        hasQueuedPending := if g1.pending != .none || g1.afterRandom != .none then true else hasQueuedPending,
        reversedProposal := rev,
        preReverseGame? := if rev then some g else none }
  | .payCostPickItems p abilityId sourceId pick remainingIds =>
    if let .chooseReplacement .. := g.pending then { game := g, hasQueuedPending := true }
    else
      let g1 := g.payCostPickItems p abilityId sourceId pick remainingIds
        (followedByFinishChoice := followedByFinishChoice)
        (followedByExplicitPriority? := followedByExplicitPriority?)
      let rev := !g.hasActiveManaProposalCheckpoint && g.proposedSpell.isSome && g.proposalCheckpoint.isSome && g1.proposedSpell.isNone
      { game := g1,
        hasQueuedPending := if g1.pending != .none || g1.afterRandom != .none then true else hasQueuedPending,
        reversedProposal := rev,
        preReverseGame? := if rev then some g else none }
  | .finishActivationExtraCosts p sourceId forObject sacrificeSource exileSource stage sinceIdx =>
    if let .chooseReplacement .. := g.pending then { game := g, hasQueuedPending := true }
    else
      let g1 := g.finishActivationExtraCosts p sourceId forObject sacrificeSource exileSource stage
        (sinceIdx := sinceIdx)
        (followedByFinishChoice := followedByFinishChoice)
        (followedByExplicitPriority? := followedByExplicitPriority?)
      let rev := !g.hasActiveManaProposalCheckpoint && g.proposedSpell.isSome && g.proposalCheckpoint.isSome && g1.proposedSpell.isNone
      { game := g1,
        hasQueuedPending := if g1.pending != .none || g1.afterRandom != .none then true else hasQueuedPending,
        reversedProposal := rev,
        preReverseGame? := if rev then some g else none }
  | pr@(.finishActivateManaAbilityPicks ..)
  | pr@(.finishActivateManaAbilityPostSac ..) =>
    let g1 := runManaAbilityProbeStep g pr
    { game := g1, hasQueuedPending := if g1.pending != .none || g1.afterRandom != .none then true else hasQueuedPending }
  | .continueStartNextTurn nextP remainingDeparted runBeginTurn alreadyExpired =>
    if (continueStartNextTurnRecipient? (drainProbePausedStep g) nextP remainingDeparted runBeginTurn alreadyExpired).isSome then
      { game := g, hasQueuedPending := false }
    else { game := g, hasQueuedPending }
  | .beginTurnAfterStartExpiry =>
    if (beginTurnAfterStartExpiryRecipient? g).isSome then { game := g, hasQueuedPending := false }
    else { game := g, hasQueuedPending }
  | .beginStepCont st =>
    if st == .untap then { game := g, hasQueuedPending }
    else if (beginStepContRecipient? (drainProbePausedStep g) st).isSome then { game := g, hasQueuedPending := false }
    else { game := g, hasQueuedPending }
  | .finishPostStep (.beginStepBody st) =>
    if st == .untap then { game := g, hasQueuedPending }
    else if (stepPriorityRecipient? (drainProbePausedStep g) st).isSome then { game := g, hasQueuedPending := false }
    else { game := g, hasQueuedPending }
  | .finishPostStep (.beginStepAfterPhaseBegan st) =>
    if st == .untap then { game := g, hasQueuedPending }
    else if (beginStepAfterPhaseBeganRecipient? (drainProbePausedStep g) st).isSome then { game := g, hasQueuedPending := false }
    else { game := g, hasQueuedPending }
  | .finishPostStep .advanceAfterStepEnded =>
    let gR := drainProbePausedStep g
    if gR.step == .endOfCombat && gR.additionalCombatPhases > 0 then
      if (advanceAfterStepEndedRecipient? gR).isSome then { game := g, hasQueuedPending := false }
      else { game := g, hasQueuedPending }
    else
      match gR.step.next? with
      | none | some .untap => { game := g, hasQueuedPending }
      | some _ =>
        if (advanceAfterStepEndedRecipient? gR).isSome then { game := g, hasQueuedPending := false }
        else { game := g, hasQueuedPending }
  | pr@(.finishPostStep (.discardCleanupIds ..))
  | pr@(.finishPostStep (.logExpiredPlayFromExile ..))
  | pr@(.finishPostStep (.conniveTricksterTarget ..))
  | pr@(.finishPostStep (.finishAbilityResolution ..))
  | pr@(.finishPostStep (.grantAdventureExilePermission ..))
  | pr@(.logMessage ..)
  | pr@(.recordPutCounters ..)
  | pr@(.putCountersDeferredLog ..)
  | pr@(.logPutCounterDelta ..)
  | pr@(.finishPostStep (.logDiscardIfInGraveyard ..))
  | pr@(.finishPostStep (.logExiledIfInExile ..))
  | pr@(.finishPostStep (.logReturnedToHand ..))
  | pr@(.finishPostStep (.logPutsIntoHand ..))
  | pr@(.finishPostStep (.logPutOnOwnerLibrary ..))
  | pr@(.finishPostStep (.logIfCountersIncreased ..))
  | pr@(.finishPostStep (.finishMoveToOwnerGraveyardLog ..))
  | pr@(.finishPostStep (.logDiscardedCount ..))
  | pr@(.finishPostStep (.logGiftTreasureGiven ..))
  | pr@(.finishPostStep (.logCreatedTokensSummary ..))
  | pr@(.finishPostStep (.logDelayedBirdSoldiersCreated ..))
  | pr@(.finishPostStep (.applyAggregatedLifelink ..))
  | pr@(.finishPostStep (.sheHulkAfterDamage ..))
  | pr@(.finishPostStep .markNonManaCostPaid)
  | pr@(.finishPostStep (.recordCostSacrificedPower ..))
  | pr@(.gainLife ..)
  | pr@(.dealDamageToPlayer ..)
  | pr@(.runModalManaEffect ..)
  | pr@(.finishManaAbilityMountainTrigger ..)
  | pr@(.endProposalAction ..)
  | pr@(.endControlExileLoop ..)
  | pr@(.closeBatch ..)
  | pr@(.restorePausedBatch ..)
  | pr@(.counterStackSpell ..)
  | pr@(.sacrificePermanentsLoop ..)
  | pr@(.continueInterpreter ..)
  | pr@(.markDamageOn ..)
  | pr@(.returnLinkedExileLoop ..)
  | pr@(.finishLinkedExileMove ..)
  | pr@(.phaseOutPermanentsLoop ..)
  | pr@(.phaseInControlled ..)
  | pr@(.phaseInControlledLoop ..)
  | pr@(.untapStepPermanents ..)
  | pr@(.finishPostStep .untapStepAfterPhaseIn)
  | pr@(.finishPostStep .recordUntapStepEnded)
  | pr@(.addLoreCounters ..)
  | pr@(.addLoreAfterDrawStep ..)
  | pr@(.finishSbaSweep ..)
  | pr@(.checkSBA ..)
  | pr@(.afterLastPermanentEnters ..)
  | pr@(.draw ..)
  | pr@(.drawOne ..)
  | pr@(.drawSubDraws ..)
  | pr@(.moveSimultaneousToGraveyard ..)
  | pr@(.moveCardsToGraveyardLoop ..)
  | pr@(.dealAssignedCombatDamage ..)
  | pr@(.addExtraCombatDamageStep)
  | pr@(.move ..) =>
    let g1 := drainProbeNonPriorityCont g pr
    { game := g1,
      hasQueuedPending :=
        if g1.pending != .none || g1.afterRandom != .none then true
        else pr.nextQueuedPending hasQueuedPending }
  | pr =>
    { game := g, hasQueuedPending := pr.nextQueuedPending hasQueuedPending }

private partial def advanceProbeOnResume (g : Game) (hasQueuedPending : Bool)
    (pr : PendingReplacement) : Game × Bool :=
  let res := advanceProbeOnResumeCore g hasQueuedPending pr
  (res.game, res.hasQueuedPending)

private partial def nextQueuedPendingOnResume (g : Game) (hasQueuedPending : Bool)
    (pr : PendingReplacement) : Bool :=
  (advanceProbeOnResumeCore g hasQueuedPending pr).hasQueuedPending

/-- When `.restorePending` does not pause on a live prompt, return the post-step
probe `Game`, updated `hasQueuedPending`, and delegated continuation to inspect next. -/
private partial def nonPausingRestorePoppedOuter? (g : Game) (hasQueuedPending : Bool)
    (pr : PendingReplacement)
    (followedByFinishChoice : Bool := false)
    (followedByExplicitPriority? : Option PlayerId := none) :
    Option (Game × Bool × PendingReplacement) :=
  match pr with
  | pr@(.restorePending ..) =>
    match probeRestorePendingCore g hasQueuedPending pr
        followedByFinishChoice followedByExplicitPriority? with
    | .paused _ _ _ => none
    | .delegate g' q' nextPr => some (g', q', nextPr)
  | _ => none

private partial def classifyFinishConcedePriority (g : Game) (wasIdlePriority : Bool)
    (savedPendingPrio : Option PlayerId)
    (wasAssigningCombatDamage : Option Bool := none)
    (savedPending : Option Pending := none)
    (popOuter : Bool := false)
    (runSba : Bool := false)
    (departed : Array PlayerId := #[])
    (rewindProposal : Option Bool := none)
    (fuel : Nat := 8) : ConcedePriorityOutcome :=
  let g := if g.sbaPaused then g.change (.pending .none) else g
  let g := g.popEmptyContinuationFrames
  let (g, popOuter) :=
    if runSba && !g.over then (g, popOuter)
    else g.flushDismissedPausedBatch savedPending popOuter (hasDeferredRewind := rewindProposal.isSome)
  let (g, savedPending, popOuter, rewindProposal) :=
    match rewindProposal with
    | some hadPreBodyCont =>
      if !g.sbaPaused && (g.currentBatch.isNone || g.isPreProposalCheckpointBatch) then
        let (g', s', po') := g.applyDeferredProposalRewind savedPending popOuter departed hadPreBodyCont
        (g', s', po', none)
      else
        (g, savedPending, popOuter, rewindProposal)
    | none =>
      (g, savedPending, popOuter, none)
  let (g, _, savedPending, popOuter, departed, rewindProposal) :=
    if runSba && !g.over then
      g.checkSBACountedWithLeavesCore savedPending popOuter departed rewindProposal
        (deferRestore := true)
    else
      (g, false, savedPending, popOuter, departed, rewindProposal)
  if g.over || g.livingPlayers.isEmpty then .settlesPromptOrOver
  else if let .chooseReplacement .. := g.pending then
    if g.anyContinuationSettlesControlFlow then
      match g.firstContinuationPriorityGrant? with
      | some (some q) => .grants (some q)
      | some none => .implicitResolutionChoice
      | none => if g.anyContinuationGrantsPriority then .grants none else .settlesPromptOrOver
    else if fuel == 0 then .settlesPromptOrOver
    else
      let gD := drainProbePausedStep g
      if gD.over || gD.livingPlayers.isEmpty || gD.pending != .none ||
          gD.afterRandom != .none || gD.pendingReplacement.isSome then
        .settlesPromptOrOver
      else
        classifyFinishConcedePriority gD wasIdlePriority savedPendingPrio
          wasAssigningCombatDamage savedPending popOuter (runSba := true)
          (departed := departed) (rewindProposal := rewindProposal) (fuel := fuel - 1)
  else if g.sbaPaused then .settlesPromptOrOver
  else
    let g : Game :=
      match savedPending with
      | some sp =>
        if g.pending == Pending.none then
          resumePendingReplacement g
            (.restorePending sp popOuter (departed := departed) (rewindProposal := rewindProposal))
        else g
      | none =>
        if rewindProposal.isSome then
          if g.pending == Pending.none then
            resumePendingReplacement g
              (.restorePending Pending.none popOuter (departed := departed) (rewindProposal := rewindProposal))
          else g
        else if popOuter then
          match g.outerPendingReplacements.back? with
          | some popped => (g.change .popOuterPendingReplacement).chainPendingReplacement popped
          | none => g
        else g
    if g.over then .settlesPromptOrOver
    else if let .chooseReplacement .. := g.pending then
      match g.firstContinuationPriorityGrant? with
      | some (some q) => .grants (some q)
      | some none => .implicitResolutionChoice
      | none =>
        if g.anyContinuationGrantsPriority then .grants none
        else if g.anyContinuationSettlesControlFlow then .settlesPromptOrOver
        else .noGrant
    else if g.pending != Pending.none then .settlesPromptOrOver
    else if let some fa := wasAssigningCombatDamage then
      probeCombatDamageResumeOutcome g fa
    else
      let g := g.popEmptyContinuationFrames
      if !g.continuations.isEmpty || g.pendingReplacement.isSome ||
          !g.outerPendingReplacements.isEmpty ||
          g.currentInterpWait?.isSome ||
          (g.proposedSpell.isNone &&
            (g.pendingMayCastFromExile.isSome || g.pendingFreeCopies.isSome)) then
        classifyFinishResolutionChoice g
      else if wasIdlePriority && g.playersReceivePriority && !g.hasWaitingTriggers &&
          g.consecutivePasses ≥ g.livingPlayers.size then
        let g0 := g.change (.consecutivePasses 0)
        if !g0.stack.isEmpty then
          let g1 := g0.resolveTop
          if g1.over || g1.livingPlayers.isEmpty then .settlesPromptOrOver
          else if let .chooseReplacement .. := g1.pending then
            match g1.firstContinuationPriorityGrant? with
            | some (some q) => .grants (some q)
            | some none => .implicitResolutionChoice
            | none =>
              if g1.anyContinuationGrantsPriority then .grants none
              else if g1.anyContinuationSettlesControlFlow then .settlesPromptOrOver
              else
                let gD := drainProbePausedStep g1
                if gD.over || gD.livingPlayers.isEmpty || gD.pending != .none ||
                    gD.afterRandom != .none || gD.pendingReplacement.isSome then
                  .settlesPromptOrOver
                else receivePriorityOutcome gD gD.activePlayer (recheckSba := true)
          else if g1.pending != Pending.none || g1.afterRandom != .none then
            .settlesPromptOrOver
          else
            receivePriorityOutcome g1 g1.activePlayer (recheckSba := true)
        else
          match advanceStepRecipient? g0 with
          | some q => .grants (some q)
          | none => .settlesPromptOrOver
      else if g.playersReceivePriority && !g.livingPlayers.isEmpty then
        let rawPrio := (savedPendingPrio.orElse (fun _ => g.pendingPriority)).getD g.priority
        let nextP := if g.stillInGame rawPrio then rawPrio else g.nextLiving rawPrio
        let g := g.promptTriggerTargetsIfNeeded
        if g.pending != Pending.none then .settlesPromptOrOver
        else
          let out := receivePriorityOutcome g nextP (recheckSba := true)
          if savedPendingPrio.isNone then
            match out with
            | .grants _ => .implicitResolutionChoice
            | other => other
          else out
      else .noGrant

/-- Helper computing the explicit priority recipient (if any) of
`finishConcedePriority` (`600–659`) without entering `resolveTop` / `advanceStep`. -/
private partial def finishConcedePriorityRecipient? (g : Game) (wasIdlePriority : Bool)
    (savedPendingPrio : Option PlayerId)
    (wasAssigningCombatDamage : Option Bool := none)
    (savedPending : Option Pending := none)
    (popOuter : Bool := false)
    (runSba : Bool := false)
    (departed : Array PlayerId := #[])
    (rewindProposal : Option Bool := none) : Option PlayerId :=
  match classifyFinishConcedePriority g wasIdlePriority savedPendingPrio
      wasAssigningCombatDamage savedPending popOuter runSba departed rewindProposal with
  | .grants explicit? => explicit?
  | _ => none

private partial def classifyConcedePlayersLoop (g : Game) (remaining : Array PlayerId)
    (wasIdlePriority : Bool)
    (savedPendingPrio : Option PlayerId)
    (wasAssigningCombatDamage : Option Bool := none)
    (savedIn : Option Pending := none)
    (popOuterIn : Bool := false)
    (departedIn : Array PlayerId := #[])
    (rewindProposalIn : Option Bool := none)
    (midResolutionOrBatch : Bool := false)
    (fuel : Nat := 8) : ConcedePriorityOutcome := Id.run do
  let mut g := if g.sbaPaused then g.change (.pending .none) else g
  if g.over then
    return .settlesPromptOrOver
  let mut saved? := savedIn
  let mut popOuter := popOuterIn
  let mut departed := departedIn
  let mut rewindProposal := rewindProposalIn
  for i in [0:remaining.size] do
    if g.over then
      return .settlesPromptOrOver
    let pid := remaining[i]!
    if !(g.player pid).leftTheGame then
      let wasSbaPaused := g.sbaPaused
      let (gf, pof) := g.flushDismissedPausedBatch saved? popOuter (hasDeferredRewind := rewindProposal.isSome)
      g := gf
      popOuter := pof
      if g.over then
        return .settlesPromptOrOver
      if !wasSbaPaused then
        match g.pending with
        | .chooseLegend r _ _ =>
          let remHere := remaining.extract i remaining.size
          if !remHere.contains r then
            return .settlesPromptOrOver
        | .chooseReplacement r _ =>
          let remHere := remaining.extract i remaining.size
          if !remHere.contains r then
            if g.anyContinuationSettlesControlFlow then
              return match g.firstContinuationPriorityGrant? with
                | some (some q) => .grants (some q)
                | some none => .implicitResolutionChoice
                | none => if g.anyContinuationGrantsPriority then .grants none else .settlesPromptOrOver
            else if fuel == 0 then
              return .settlesPromptOrOver
            else
              let gD := drainProbePausedStep g
              if gD.over || gD.livingPlayers.isEmpty || gD.pending != .none ||
                  gD.afterRandom != .none || gD.pendingReplacement.isSome then
                return .settlesPromptOrOver
              else
                return classifyConcedePlayersLoop gD remHere wasIdlePriority savedPendingPrio
                  wasAssigningCombatDamage saved? popOuter
                  (departedIn := departed) (rewindProposalIn := rewindProposal)
                  (midResolutionOrBatch := midResolutionOrBatch) (fuel := fuel - 1)
        | _ => pure ()
      if let some hadPreBodyCont := rewindProposal then
        if !g.sbaPaused && (g.currentBatch.isNone || g.isPreProposalCheckpointBatch) then
          let (g', s', po') := g.applyDeferredProposalRewind saved? popOuter departed hadPreBodyCont
          g := g'
          saved? := s'
          popOuter := po'
          rewindProposal := none
          match g.pending with
          | .chooseLegend r _ _ =>
            let remHere := remaining.extract i remaining.size
            if !remHere.contains r then
              return .settlesPromptOrOver
          | .chooseReplacement r _ =>
            let remHere := remaining.extract i remaining.size
            if !remHere.contains r then
              if g.anyContinuationSettlesControlFlow then
                return match g.firstContinuationPriorityGrant? with
                  | some (some q) => .grants (some q)
                  | some none => .implicitResolutionChoice
                  | none => if g.anyContinuationGrantsPriority then .grants none else .settlesPromptOrOver
              else if fuel == 0 then
                return .settlesPromptOrOver
              else
                let gD := drainProbePausedStep g
                if gD.over || gD.livingPlayers.isEmpty || gD.pending != .none ||
                    gD.afterRandom != .none || gD.pendingReplacement.isSome then
                  return .settlesPromptOrOver
                else
                  return classifyConcedePlayersLoop gD remHere wasIdlePriority savedPendingPrio
                    wasAssigningCombatDamage saved? popOuter
                    (departedIn := departed) (rewindProposalIn := none)
                    (midResolutionOrBatch := midResolutionOrBatch) (fuel := fuel - 1)
          | _ => pure ()
      let prePopCont? : Option (Option PendingReplacement) :=
        if popOuter then some g.pendingReplacement else none
      if popOuter then
        if let some popped := g.outerPendingReplacements.back? then
          g := (g.change .popOuterPendingReplacement).chainPendingReplacement popped
        popOuter := false
      let pendingIn := if g.pending == .none then saved? else none
      if pendingIn.isSome then
        saved? := none
      else if g.isProposalAbortedByLeave pid then
        if let some prop := g.proposedSpell then
          if saved?.any (isProposalPromptFor prop.caster) then
            saved? := none
      let (g', newlySaved?, po, rw) :=
        g.playerLeavesGameCore pid (deferRestore := true) (pendingIn := pendingIn)
          (departedIn := departed) (rewindProposalIn := rewindProposal)
          (prePopCont? := prePopCont?)
      g := g'
      departed := if departed.contains pid then departed else departed.push pid
      popOuter := popOuter || po
      match saved?, newlySaved? with
      | none, s => saved? := s
      | some .none, s => saved? := s.orElse (fun _ => some .none)
      | some oldP, some newP =>
        if newP != .none then
          let popped? : Option PendingReplacement :=
            if popOuter then g.outerPendingReplacements.back? else none
          if popped?.isSome then
            g := g.change .popOuterPendingReplacement
          let restoreOld : PendingReplacement := .restorePending oldP false (departed := departed)
          let outer := g.chainRestoreAfterOpenBatch restoreOld popped?
          if g.continuations.isEmpty then
            g := g.change (.pushContinuationFrame {})
          g := g.change (.pushOuterPendingReplacement outer)
          popOuter := true
          saved? := some newP
      | some _, none => pure ()
      rewindProposal :=
        match rewindProposal, rw with
        | some a, some _ => some a
        | some a, none =>
          if g.proposedSpell.isSome && g.proposalCheckpoint.isSome then some a else none
        | none, some b => some b
        | none, none => none
      let rem := remaining.extract (i + 1) remaining.size
      match g.pending with
      | .chooseLegend r _ _ =>
        if !rem.contains r then
          return .settlesPromptOrOver
      | .chooseReplacement r _ =>
        if !rem.contains r then
          if g.anyContinuationSettlesControlFlow then
            return match g.firstContinuationPriorityGrant? with
              | some (some q) => .grants (some q)
              | some none => .implicitResolutionChoice
              | none => if g.anyContinuationGrantsPriority then .grants none else .settlesPromptOrOver
          else if fuel == 0 then
            return .settlesPromptOrOver
          else
            let gD := drainProbePausedStep g
            if gD.over || gD.livingPlayers.isEmpty || gD.pending != .none ||
                gD.afterRandom != .none || gD.pendingReplacement.isSome then
              return .settlesPromptOrOver
            else
              return classifyConcedePlayersLoop gD rem wasIdlePriority savedPendingPrio
                wasAssigningCombatDamage saved? popOuter
                (departedIn := departed) (rewindProposalIn := rewindProposal)
                (midResolutionOrBatch := midResolutionOrBatch) (fuel := fuel - 1)
      | _ => pure ()
  let (gf, pof) := g.flushDismissedPausedBatch saved? popOuter (hasDeferredRewind := rewindProposal.isSome)
  g := gf
  popOuter := pof
  if g.over then
    return .settlesPromptOrOver
  if let some hadPreBodyCont := rewindProposal then
    if !g.sbaPaused && (g.currentBatch.isNone || g.isPreProposalCheckpointBatch) then
      let (g', s', po') := g.applyDeferredProposalRewind saved? popOuter departed hadPreBodyCont
      g := g'
      saved? := s'
      popOuter := po'
      rewindProposal := none
  if saved?.isNone && !g.sbaPaused && g.pending != .none then
    saved? := some g.pending
    g := g.change (.pending .none)
  if midResolutionOrBatch then
    if let .chooseReplacement .. := g.pending then
      if g.anyContinuationSettlesControlFlow then
        return match g.firstContinuationPriorityGrant? with
          | some (some q) => .grants (some q)
          | some none => .implicitResolutionChoice
          | none => if g.anyContinuationGrantsPriority then .grants none else .settlesPromptOrOver
      else if fuel == 0 then
        return .settlesPromptOrOver
      else
        let gD := drainProbePausedStep g
        if gD.over || gD.livingPlayers.isEmpty || gD.pending != .none ||
            gD.afterRandom != .none || gD.pendingReplacement.isSome then
          return .settlesPromptOrOver
        else
          return classifyConcedePlayersLoop gD #[] wasIdlePriority savedPendingPrio
            wasAssigningCombatDamage saved? popOuter
            (departedIn := departed) (rewindProposalIn := rewindProposal)
            (midResolutionOrBatch := true) (fuel := fuel - 1)
    else if g.sbaPaused then
      return .settlesPromptOrOver
    else
      g :=
        match saved? with
        | some sp =>
          if g.pending == .none then
            resumePendingReplacement g
              (.restorePending sp popOuter (departed := departed) (rewindProposal := rewindProposal))
          else g
        | none =>
          if rewindProposal.isSome then
            if g.pending == .none then
              resumePendingReplacement g
                (.restorePending .none popOuter (departed := departed) (rewindProposal := rewindProposal))
            else g
          else if popOuter then
            match g.outerPendingReplacements.back? with
            | some popped => (g.change .popOuterPendingReplacement).chainPendingReplacement popped
            | none => g
          else g
      if g.over then
        return .settlesPromptOrOver
      else if let .chooseReplacement .. := g.pending then
        if g.anyContinuationSettlesControlFlow then
          match g.firstContinuationPriorityGrant? with
          | some (some q) => return .grants (some q)
          | some none => return .implicitResolutionChoice
          | none =>
            return if g.anyContinuationGrantsPriority then .grants none else .settlesPromptOrOver
        else
          return .noGrant
      else if g.pending != .none then
        return .settlesPromptOrOver
      else
        g := g.popEmptyContinuationFrames
        let runSba :=
          g.continuations.isEmpty && g.currentBatch.isNone &&
            g.pendingReplacement.isNone && g.outerPendingReplacements.isEmpty &&
            g.currentInterpWait?.isNone
        return classifyFinishConcedePriority g wasIdlePriority savedPendingPrio wasAssigningCombatDamage
          none false (runSba := runSba) (departed := departed) (fuel := fuel)
  else if let .chooseReplacement .. := g.pending then
    if g.anyContinuationSettlesControlFlow then
      return match g.firstContinuationPriorityGrant? with
        | some (some q) => .grants (some q)
        | some none => .implicitResolutionChoice
        | none => if g.anyContinuationGrantsPriority then .grants none else .settlesPromptOrOver
    else if fuel == 0 then
      return .settlesPromptOrOver
    else
      let gD := drainProbePausedStep g
      if gD.over || gD.livingPlayers.isEmpty || gD.pending != .none ||
          gD.afterRandom != .none || gD.pendingReplacement.isSome then
        return .settlesPromptOrOver
      else
        return classifyFinishConcedePriority gD wasIdlePriority savedPendingPrio wasAssigningCombatDamage
          saved? popOuter (runSba := true) (departed := departed) (rewindProposal := rewindProposal)
          (fuel := fuel - 1)
  else if g.sbaPaused then
    return .settlesPromptOrOver
  else
    return classifyFinishConcedePriority g wasIdlePriority savedPendingPrio wasAssigningCombatDamage
      saved? popOuter (runSba := true) (departed := departed) (rewindProposal := rewindProposal)
      (fuel := fuel)

/-- Helper computing the explicit priority recipient (if any) of a non-pregame
`concedePlayersLoop` (`!wasPregame`, `673–788, 865–871`). -/
private partial def concedePlayersLoopRecipient? (g : Game) (remaining : Array PlayerId)
    (wasIdlePriority : Bool)
    (savedPendingPrio : Option PlayerId)
    (wasAssigningCombatDamage : Option Bool := none)
    (savedIn : Option Pending := none)
    (popOuterIn : Bool := false)
    (departedIn : Array PlayerId := #[])
    (rewindProposalIn : Option Bool := none)
    (midResolutionOrBatch : Bool := false) : Option PlayerId :=
  match classifyConcedePlayersLoop g remaining wasIdlePriority savedPendingPrio
      wasAssigningCombatDamage savedIn popOuterIn
      (departedIn := departedIn) (rewindProposalIn := rewindProposalIn)
      (midResolutionOrBatch := midResolutionOrBatch) with
  | .grants explicit? => explicit?
  | _ => none

private partial def classifyFinishResolutionChoiceFuel (g : Game) : Nat → ConcedePriorityOutcome
  | 0 => .settlesPromptOrOver
  | fuel + 1 =>
    if g.over || g.livingPlayers.isEmpty then .settlesPromptOrOver
    else if let .chooseReplacement .. := g.pending then
      if g.anyContinuationSettlesControlFlow then
        match g.firstContinuationPriorityGrant? with
        | some (some q) => .grants (some q)
        | some none => .implicitResolutionChoice
        | none => if g.anyContinuationGrantsPriority then .grants none else .settlesPromptOrOver
      else
        let gD := drainProbePausedStep g
        if gD.over || gD.livingPlayers.isEmpty || gD.pending != .none ||
            gD.afterRandom != .none || gD.pendingReplacement.isSome then
          .settlesPromptOrOver
        else classifyFinishResolutionChoiceFuel gD fuel
    else if g.pending != .none || g.afterRandom != .none then .settlesPromptOrOver
    else
      let alreadyGrants : Bool :=
        g.pending == .none && g.afterRandom == .none && g.anyContinuationGrantsPriority
      let explicitGrant? : Option PlayerId :=
        if alreadyGrants then
          match g.firstContinuationPriorityGrant? with
          | some (some q) => some q
          | _ => none
        else none
      let g := g.drainPendingContinuations
      if g.over || g.livingPlayers.isEmpty then .settlesPromptOrOver
      else if let .chooseReplacement .. := g.pending then
        if g.anyContinuationSettlesControlFlow then
          match g.firstContinuationPriorityGrant? with
          | some (some q) => .grants (some q)
          | some none => .implicitResolutionChoice
          | none => if g.anyContinuationGrantsPriority then .grants none else .settlesPromptOrOver
        else
          let gD := drainProbePausedStep g
          if gD.over || gD.livingPlayers.isEmpty || gD.pending != .none ||
              gD.afterRandom != .none || gD.pendingReplacement.isSome then
            .settlesPromptOrOver
          else classifyFinishResolutionChoiceFuel gD fuel
      else if g.pending != .none || g.afterRandom != .none then .settlesPromptOrOver
      else
        let g := g.popEmptyContinuationFrames
        if g.proposedSpell.any (fun prop =>
            !g.stillInGame prop.caster || (g.findObject? prop.spellId).isNone) then
          if g.proposalCheckpoint.isNone then .noGrant
          else
            let gPreRev := if g.pending == .none then g else g.change (.pending .none)
            match gPreRev.reverseProposedSpellCore? (resumeContinuation := true)
                (alwaysGrantPriority := true) with
            | .error _ => .noGrant
            | .ok (gR, needsFinish) =>
              if needsFinish then
                classifyFinishResolutionChoiceFuel gR fuel
              else if gR.over || gR.livingPlayers.isEmpty then .settlesPromptOrOver
              else if let .chooseReplacement .. := gR.pending then
                if gR.anyContinuationSettlesControlFlow then
                  match gR.firstContinuationPriorityGrant? with
                  | some (some q) => .grants (some q)
                  | some none => .implicitResolutionChoice
                  | none => if gR.anyContinuationGrantsPriority then .grants none else .settlesPromptOrOver
                else .settlesPromptOrOver
              else if gR.pending != .none || gR.afterRandom != .none then .settlesPromptOrOver
              else if gR.proposedSpell.isNone &&
                  (gR.pendingMayCastFromExile.isSome || gR.pendingFreeCopies.isSome) then
                classifyFinishResolutionChoiceFuel gR fuel
              else if gR.continuations.isEmpty && gR.triggerNeedingTargets.isSome then
                if (gR.promptTriggerTargetsIfNeeded).pending != .none then .settlesPromptOrOver
                else .implicitResolutionChoice
              else if gR.proposedSpell.isSome then .noGrant
              else if gR.playersReceivePriority then
                match livingPriorityInstead? gR gR.priority with
                | some q => .grants (some q)
                | none => .settlesPromptOrOver
              else .settlesPromptOrOver
        else if g.proposedSpell.isSome then .noGrant
        else if g.pendingMayCastFromExile.isSome || g.pendingFreeCopies.isSome then
          let g2 := g.reopenDeferredExileCasts
          if g2.over || g2.livingPlayers.isEmpty then .settlesPromptOrOver
          else if let .chooseReplacement .. := g2.pending then
            if g2.anyContinuationSettlesControlFlow then
              match g2.firstContinuationPriorityGrant? with
              | some (some q) => .grants (some q)
              | some none => .implicitResolutionChoice
              | none => if g2.anyContinuationGrantsPriority then .grants none else .settlesPromptOrOver
            else
              let gD := drainProbePausedStep g2
              if gD.over || gD.livingPlayers.isEmpty || gD.pending != .none ||
                  gD.afterRandom != .none || gD.pendingReplacement.isSome then
                .settlesPromptOrOver
              else classifyFinishResolutionChoiceFuel gD fuel
          else if g2.pending != .none || g2.afterRandom != .none then .settlesPromptOrOver
          else if g2.currentInterpWait?.isSome || g2.pendingReplacement.isSome ||
              !g2.outerPendingReplacements.isEmpty then
            classifyFinishResolutionChoiceFuel g2 fuel
          else if g2.triggerNeedingTargets.isSome &&
              (g2.promptTriggerTargetsIfNeeded).pending != .none then
            .settlesPromptOrOver
          else if alreadyGrants then
            match explicitGrant? with
            | some q =>
              match livingPriorityInstead? g2 q with
              | some q' => .grants (some q')
              | none => .settlesPromptOrOver
            | none => .implicitResolutionChoice
          else
            let g2 := g2.popEmptyContinuationFrames
            let prio := g2.pendingPriority.getD g2.activePlayer
            match receivePriorityOutcome g2 prio (recheckSba := true) with
            | .grants _ | .implicitResolutionChoice => .implicitResolutionChoice
            | other => other
        else if g.triggerNeedingTargets.isSome &&
            (g.promptTriggerTargetsIfNeeded).pending != .none then
          .settlesPromptOrOver
        else if alreadyGrants then
          match explicitGrant? with
          | some q =>
            match livingPriorityInstead? g q with
            | some q' => .grants (some q')
            | none => .settlesPromptOrOver
          | none => .implicitResolutionChoice
        else
          let prio := g.pendingPriority.getD g.activePlayer
          match receivePriorityOutcome g prio (recheckSba := true) with
          | .grants _ | .implicitResolutionChoice => .implicitResolutionChoice
          | other => other

private partial def classifyFinishResolutionChoice (g : Game) : ConcedePriorityOutcome :=
  classifyFinishResolutionChoiceFuel g 8

private partial def finishResolutionChoiceGrantsPriority (g : Game) : Bool :=
  match classifyFinishResolutionChoice g with
  | .implicitResolutionChoice | .grants _ => true
  | _ => false

private partial def classifyFinishAndGrantPriorityFuel (g : Game) (p : PlayerId) :
    Nat → ConcedePriorityOutcome
  | 0 => .settlesPromptOrOver
  | fuel + 1 =>
    if g.over || g.livingPlayers.isEmpty then .settlesPromptOrOver
    else
      let alreadyGrants : Bool :=
        g.pending == .none && g.afterRandom == .none && g.anyContinuationGrantsPriority
      let entryExplicitGrant : Bool := alreadyGrants && !g.hasImplicitPriorityContinuation
      let hadEntryPending : Bool := g.pending != .none
      let explicitGrant? : Option PlayerId :=
        if alreadyGrants then
          match g.firstContinuationPriorityGrant? with
          | some (some q) => some q
          | _ => none
        else none
      let target0 := g.priorityInstead p
      let g :=
        if !entryExplicitGrant && g.hasImplicitPendingPriorityContinuation &&
            (!hadEntryPending || g.pendingPriority.isNone) && g.pendingPriority != some target0 then
          g.change (.pendingPriority (some target0))
        else g
      let preDrainPendingPrio := g.pendingPriority
      let preDrainEvSize := g.events.size
      let g := g.drainPendingContinuations
      let drainedSetPendingPrio : Bool :=
        g.pendingPriority.isSome &&
          (g.pendingPriority != preDrainPendingPrio ||
            (g.events.extract preDrainEvSize g.events.size).any fun
              | .engine _ (.pendingPriority (some _)) _ => true
              | _ => false)
      let effP := (if drainedSetPendingPrio then g.pendingPriority else none).getD p
      let g := if g.pending == .none && g.afterRandom == .none then g.popEmptyContinuationFrames else g
      if g.over || g.livingPlayers.isEmpty then .settlesPromptOrOver
      else if let .chooseReplacement .. := g.pending then
        if g.anyContinuationSettlesControlFlow then
          match g.firstContinuationPriorityGrant? with
          | some (some q) => .grants (some q)
          | some none =>
            if drainedSetPendingPrio then
              match g.pendingPriority with
              | some dp =>
                match livingPriorityInstead? g dp with
                | some q => .grants (some q)
                | none => .settlesPromptOrOver
              | none => .implicitResolutionChoice
            else if !entryExplicitGrant && (!hadEntryPending || g.pendingPriority.isNone) then
              match livingPriorityInstead? g p with
              | some q => .grants (some q)
              | none => .settlesPromptOrOver
            else .implicitResolutionChoice
          | none => if g.anyContinuationGrantsPriority then .grants none else .settlesPromptOrOver
        else
          let prio := (if entryExplicitGrant || drainedSetPendingPrio then g.pendingPriority else none).getD p
          let gD := drainProbePausedStep g
          if gD.over || gD.livingPlayers.isEmpty || gD.pending != .none ||
              gD.afterRandom != .none || gD.pendingReplacement.isSome then
            .settlesPromptOrOver
          else
            classifyFinishAndGrantPriorityFuel gD (gD.priorityInstead prio) fuel
      else if g.pending != .none || g.afterRandom != .none then .settlesPromptOrOver
      else if alreadyGrants then
        match explicitGrant? with
        | some q =>
          match livingPriorityInstead? g q with
          | some q' => .grants (some q')
          | none => .settlesPromptOrOver
        | none =>
          match livingPriorityInstead? g effP with
          | some q' => .grants (some q')
          | none => .settlesPromptOrOver
      else if g.proposedSpell.any (fun prop =>
          !g.stillInGame prop.caster || (g.findObject? prop.spellId).isNone) then
        if g.proposalCheckpoint.isNone then .noGrant
        else
          let gPreRev := if g.pending == .none then g else g.change (.pending .none)
          match gPreRev.reverseProposedSpellCore? (resumeContinuation := true)
              (alwaysGrantPriority := true) with
          | .error _ => .noGrant
          | .ok (gR, needsFinish) =>
            if needsFinish then
              classifyFinishResolutionChoiceFuel gR fuel
            else if gR.over || gR.livingPlayers.isEmpty then .settlesPromptOrOver
            else if let .chooseReplacement .. := gR.pending then
              if gR.anyContinuationSettlesControlFlow then
                match gR.firstContinuationPriorityGrant? with
                | some (some q) => .grants (some q)
                | some none => .implicitResolutionChoice
                | none => if gR.anyContinuationGrantsPriority then .grants none else .settlesPromptOrOver
              else .settlesPromptOrOver
            else if gR.pending != .none || gR.afterRandom != .none then .settlesPromptOrOver
            else if gR.proposedSpell.isNone &&
                (gR.pendingMayCastFromExile.isSome || gR.pendingFreeCopies.isSome) then
              classifyFinishAndGrantPriorityFuel gR effP fuel
            else if gR.continuations.isEmpty && gR.triggerNeedingTargets.isSome then
              if (gR.promptTriggerTargetsIfNeeded).pending != .none then .settlesPromptOrOver
              else .implicitResolutionChoice
            else if gR.proposedSpell.isSome then .noGrant
            else if gR.playersReceivePriority then
              match livingPriorityInstead? gR gR.priority with
              | some q => .grants (some q)
              | none => .settlesPromptOrOver
            else .settlesPromptOrOver
      else if g.proposedSpell.isSome then .noGrant
      else if g.pendingMayCastFromExile.isSome || g.pendingFreeCopies.isSome then
        let target := g.priorityInstead effP
        let wroteTarget :=
          !entryExplicitGrant && !drainedSetPendingPrio && (!hadEntryPending || g.pendingPriority.isNone)
        let g :=
          if wroteTarget && g.pendingPriority != some target then
            g.change (.pendingPriority (some target))
          else g
        let g2 := g.reopenDeferredExileCasts
        let mapImplicit (gCur : Game) : ConcedePriorityOutcome :=
          if wroteTarget || drainedSetPendingPrio then
            let prio := (if drainedSetPendingPrio then gCur.pendingPriority else none).getD effP
            match livingPriorityInstead? gCur prio with
            | some q => .grants (some q)
            | none => .settlesPromptOrOver
          else .implicitResolutionChoice
        if g2.over || g2.livingPlayers.isEmpty then .settlesPromptOrOver
        else if let .chooseReplacement .. := g2.pending then
          if g2.anyContinuationSettlesControlFlow then
            match g2.firstContinuationPriorityGrant? with
            | some (some q) => .grants (some q)
            | some none => mapImplicit g2
            | none => if g2.anyContinuationGrantsPriority then .grants none else .settlesPromptOrOver
          else
            let gD := drainProbePausedStep g2
            if gD.over || gD.livingPlayers.isEmpty || gD.pending != .none ||
                gD.afterRandom != .none || gD.pendingReplacement.isSome then
              .settlesPromptOrOver
            else if gD.currentInterpWait?.isSome then
              match classifyFinishResolutionChoiceFuel gD fuel with
              | .implicitResolutionChoice => mapImplicit gD
              | other => other
            else
              classifyFinishAndGrantPriorityFuel gD (gD.priorityInstead effP) fuel
        else if g2.pending != .none || g2.afterRandom != .none then .settlesPromptOrOver
        else if g2.currentInterpWait?.isSome || g2.pendingReplacement.isSome ||
            !g2.outerPendingReplacements.isEmpty then
          match classifyFinishResolutionChoiceFuel g2 fuel with
          | .implicitResolutionChoice => mapImplicit g2
          | other => other
        else if g2.triggerNeedingTargets.isSome &&
            (g2.promptTriggerTargetsIfNeeded).pending != .none then
          .settlesPromptOrOver
        else
          receivePriorityOutcome (g2.popEmptyContinuationFrames) effP (recheckSba := true) (fuel := fuel)
      else if g.triggerNeedingTargets.isSome &&
          (g.promptTriggerTargetsIfNeeded).pending != .none then
        .settlesPromptOrOver
      else
        receivePriorityOutcome g effP (recheckSba := true) (fuel := fuel)

private partial def classifyFinishAndGrantPriority (g : Game) (p : PlayerId) :
    ConcedePriorityOutcome :=
  classifyFinishAndGrantPriorityFuel g p 8

private partial def classifyProposedSpellReversal (g : Game) (prop : ProposedSpell)
    (followedByFinishChoice : Bool := false)
    (followedByExplicitPriority? : Option PlayerId := none)
    (alwaysGrantPriority : Bool := false) :
    ConcedePriorityOutcome :=
  if g.over || g.livingPlayers.isEmpty then .settlesPromptOrOver
  else if g.proposalCheckpoint.isNone then .noGrant
  else
    let hadProposal := g.proposedSpell.isSome
    match g.reverseProposedSpellCore? (resumeContinuation := true)
        (alwaysGrantPriority := alwaysGrantPriority)
        (followedByFinishChoice := followedByFinishChoice)
        (followedByExplicitPriority? := followedByExplicitPriority?) with
    | .error _ => .noGrant
    | .ok (gR, needsFinish) =>
      if needsFinish then
        match (if !followedByFinishChoice && hadProposal then followedByExplicitPriority? else none) with
        | some prio => classifyFinishAndGrantPriority gR (gR.priorityInstead prio)
        | none => classifyFinishResolutionChoice gR
      else if gR.over || gR.livingPlayers.isEmpty then .settlesPromptOrOver
      else if let .chooseReplacement .. := gR.pending then
        if gR.anyContinuationSettlesControlFlow then
          match gR.firstContinuationPriorityGrant? with
          | some (some q) => .grants (some q)
          | some none => .implicitResolutionChoice
          | none => if gR.anyContinuationGrantsPriority then .grants none else .settlesPromptOrOver
        else .settlesPromptOrOver
      else if gR.pending != .none || gR.afterRandom != .none then .settlesPromptOrOver
      else if alwaysGrantPriority && gR.continuations.isEmpty && gR.triggerNeedingTargets.isSome &&
          (gR.promptTriggerTargetsIfNeeded).pending != .none then
        .settlesPromptOrOver
      else if !gR.continuations.isEmpty || gR.pendingReplacement.isSome ||
          !gR.outerPendingReplacements.isEmpty || gR.currentInterpWait?.isSome then
        classifyFinishResolutionChoice gR
      else if gR.playersReceivePriority then
        let expectedCaster :=
          match (if !followedByFinishChoice && hadProposal then followedByExplicitPriority? else none) with
          | some q => q
          | none => prop.caster
        let prio :=
          if gR.priority == expectedCaster || !gR.stillInGame expectedCaster then gR.priority
          else gR.priorityInstead expectedCaster
        match livingPriorityInstead? gR prio with
        | some q => .grants (some q)
        | none => .settlesPromptOrOver
      else .settlesPromptOrOver

private partial def classifyChainFinishChoice (gC : Game) (prioTarget : PlayerId) :
    ConcedePriorityOutcome :=
  if gC.anyContinuationSettlesControlFlow then
    match gC.firstContinuationPriorityGrant? with
    | some (some q) => .grants (some q)
    | some none =>
      if gC.pendingPriority.isNone then
        match livingPriorityInstead? gC prioTarget with
        | some q => .grants (some q)
        | none => .settlesPromptOrOver
      else .implicitResolutionChoice
    | none => if gC.anyContinuationGrantsPriority then .grants none else .settlesPromptOrOver
  else
    let wrotePrio := gC.pendingPriority.isNone
    let gC' :=
      if wrotePrio then gC.change (.pendingPriority (some (gC.priorityInstead prioTarget)))
      else gC
    match classifyFinishResolutionChoice gC' with
    | .implicitResolutionChoice =>
      if wrotePrio then
        match livingPriorityInstead? gC' prioTarget with
        | some q => .grants (some q)
        | none => .settlesPromptOrOver
      else .implicitResolutionChoice
    | other => other

private partial def finishPostCastOutcome (g : Game) (caster : PlayerId)
    (hadOpenContinuation : Bool) (grantPriority : Bool := true)
    (spellId? : Option ObjectId := none)
    (delegateFinishChoice : Bool := false) : ConcedePriorityOutcome :=
  if g.over || g.livingPlayers.isEmpty then .settlesPromptOrOver
  else
    let g0 :=
      match spellId? with
      | some sid =>
        let clearChanges : Array EngineChange :=
          (if g.proposedSpell.isSome then #[EngineChange.proposedSpell none] else #[]) ++
          (if g.proposalCheckpoint.isSome then #[EngineChange.clearProposalCheckpoint] else #[]) ++
          #[EngineChange.castingFromTop false]
        let g1 := g.changes clearChanges
        match g1.findObject? sid with
        | some spell => g1.putCastTriggersOnStack caster spell
        | none => g1
      | none => g
    if g0.over || g0.livingPlayers.isEmpty then .settlesPromptOrOver
    else if let .chooseReplacement .. := g0.pending then
      if !grantPriority && !delegateFinishChoice then
        if pausedPromptSettles g0 false g0.pending then .settlesPromptOrOver else .noGrant
      else .settlesPromptOrOver
    else if g0.pending != .none || g0.afterRandom != .none then .settlesPromptOrOver
    else if spellId?.any (fun sid => spellOpensAncestryScry g0 caster sid) then .settlesPromptOrOver
    else
      let g1 := simulateFinishPostCastBody g0 caster
      let prioTarget := if hadOpenContinuation then g1.activePlayer else caster
      if g1.over || g1.livingPlayers.isEmpty then .settlesPromptOrOver
      else if !grantPriority then
        if delegateFinishChoice then classifyFinishResolutionChoice g1
        else if let .chooseReplacement .. := g1.pending then
          if pausedPromptSettles g1 false g1.pending then .settlesPromptOrOver else .noGrant
        else if g1.pending != .none || g1.afterRandom != .none then .settlesPromptOrOver
        else .noGrant
      else if let .chooseReplacement .. := g1.pending then
        if g1.anyContinuationSettlesControlFlow then
          match g1.firstContinuationPriorityGrant? with
          | some (some q) => .grants (some q)
          | some none =>
            if g1.pendingPriority.isNone then
              match livingPriorityInstead? g1 prioTarget with
              | some q => .grants (some q)
              | none => .settlesPromptOrOver
            else .implicitResolutionChoice
          | none => if g1.anyContinuationGrantsPriority then .grants none else .settlesPromptOrOver
        else if g1.currentInterpWait?.isSome then
          let wrotePrio := g1.pendingPriority.isNone
          let g1' :=
            if wrotePrio then g1.change (.pendingPriority (some (g1.priorityInstead prioTarget)))
            else g1
          let gD := drainProbePausedStep g1'
          if gD.over || gD.livingPlayers.isEmpty || gD.pending != .none ||
              gD.afterRandom != .none || gD.pendingReplacement.isSome then
            .settlesPromptOrOver
          else
            match classifyFinishResolutionChoice gD with
            | .implicitResolutionChoice =>
              if wrotePrio then
                match livingPriorityInstead? gD prioTarget with
                | some q => .grants (some q)
                | none => .settlesPromptOrOver
              else .implicitResolutionChoice
            | other => other
        else
          let gD := drainProbePausedStep g1
          if gD.over || gD.livingPlayers.isEmpty || gD.pending != .none ||
              gD.afterRandom != .none || gD.pendingReplacement.isSome then
            .settlesPromptOrOver
          else classifyFinishAndGrantPriority gD prioTarget
      else if g1.pending != .none || g1.afterRandom != .none then .settlesPromptOrOver
      else if g1.currentInterpWait?.isSome || g1.pendingReplacement.isSome ||
          !g1.outerPendingReplacements.isEmpty then
        classifyChainFinishChoice g1 prioTarget
      else
        receivePriorityOutcome g1 prioTarget (recheckSba := true)

private partial def probeCompleteTurnFaceUpClean (g : Game) (caster : PlayerId)
    (spellId : ObjectId) (hadOuter : Bool)
    (followedByFinishChoice : Bool := false)
    (followedByExplicitPriority? : Option PlayerId := none) : ConcedePriorityOutcome :=
  if g.over || g.livingPlayers.isEmpty then .settlesPromptOrOver
  else if !(g.stillInGame caster &&
      (g.findObject? spellId).any (fun o =>
        o.isOnBattlefield && o.status.faceDown && g.controlledBy o caster)) then
    match g.proposedSpell with
    | some prop =>
      if g.proposalCheckpoint.isSome then
        classifyProposedSpellReversal g prop followedByFinishChoice followedByExplicitPriority?
      else
        let wasIdle := g.pending == .none || isProposalPromptFor caster g.pending
        let clearPending : Array EngineChange :=
          if isProposalPromptFor caster g.pending then #[.pending .none] else #[]
        let clearCkpt : Array EngineChange :=
          if g.proposalCheckpoint.isSome then #[.clearProposalCheckpoint] else #[]
        let gC := g.changes (clearPending ++ #[.proposedSpell none, .consecutivePasses 0] ++ clearCkpt)
        if gC.over || gC.livingPlayers.isEmpty then .settlesPromptOrOver
        else if gC.pending != .none then
          if isSelfSettlingPending gC.pending then .settlesPromptOrOver else .noGrant
        else if hadOuter then .noGrant
        else if gC.pendingReplacement.isSome || !gC.outerPendingReplacements.isEmpty ||
            gC.currentInterpWait?.isSome then
          classifyChainFinishChoice gC caster
        else if gC.continuations.isEmpty && (!g.stillInGame caster || wasIdle) then
          receivePriorityOutcome gC (gC.priorityInstead caster) (recheckSba := true)
        else .noGrant
    | none =>
      let wasIdle := g.pending == .none || isProposalPromptFor caster g.pending
      let clearPending : Array EngineChange :=
        if isProposalPromptFor caster g.pending then #[.pending .none] else #[]
      let clearCkpt : Array EngineChange :=
        if g.proposalCheckpoint.isSome then #[.clearProposalCheckpoint] else #[]
      let gC := g.changes (clearPending ++ #[.proposedSpell none, .consecutivePasses 0] ++ clearCkpt)
      if gC.over || gC.livingPlayers.isEmpty then .settlesPromptOrOver
      else if gC.pending != .none then
        if isSelfSettlingPending gC.pending then .settlesPromptOrOver else .noGrant
      else if hadOuter then .noGrant
      else if gC.pendingReplacement.isSome || !gC.outerPendingReplacements.isEmpty ||
          gC.currentInterpWait?.isSome then
        classifyChainFinishChoice gC caster
      else if gC.continuations.isEmpty && (!g.stillInGame caster || wasIdle) then
        receivePriorityOutcome gC (gC.priorityInstead caster) (recheckSba := true)
      else .noGrant
  else
    let hadPreReconcileCont :=
      g.currentInterpWait?.isSome || g.pendingReplacement.isSome || !g.outerPendingReplacements.isEmpty
    let hadPrePrio := g.pendingPriority.isSome
    let preExplicitGrant? : Option PlayerId :=
      if !hadOuter && hadPreReconcileCont then
        let gPre := if g.proposedSpell.isSome then g.change (.proposedSpell none) else g
        match gPre.firstContinuationPriorityGrant? with
        | some (some q) => some q
        | _ => none
      else none
    let (g1, callerShouldResume) := g.completeTurnFaceUp caster spellId (hadOuterReplacement := hadOuter)
    let g1 := if callerShouldResume && !hadOuter then g1.resumeAfterBecomeCastFwd else g1
    if g1.over || g1.livingPlayers.isEmpty then .settlesPromptOrOver
    else if let .chooseReplacement .. := g1.pending then
      if g1.pendingReplacement.any containsFinishTurnFaceUp then
        if hadOuter then .noGrant else .settlesPromptOrOver
      else if g1.anyContinuationSettlesControlFlow then
        match g1.firstContinuationPriorityGrant? with
        | some (some q) => .grants (some q)
        | some none =>
          if !hadOuter && hadPreReconcileCont && !hadPrePrio then
            match livingPriorityInstead? g1 caster with
            | some q => .grants (some q)
            | none => .settlesPromptOrOver
          else .implicitResolutionChoice
        | none => if g1.anyContinuationGrantsPriority then .grants none else .settlesPromptOrOver
      else if hadOuter then .noGrant
      else
        let gD := drainProbePausedStep g1
        if gD.over || gD.livingPlayers.isEmpty || gD.pending != .none ||
            gD.afterRandom != .none || gD.pendingReplacement.isSome then
          .settlesPromptOrOver
        else receivePriorityOutcome gD caster (recheckSba := true)
    else if g1.pending != .none || g1.afterRandom != .none then .settlesPromptOrOver
    else if hadOuter then
      match g1.pendingReplacement with
      | some pr1 =>
        if containsFinishTurnFaceUp pr1 then .noGrant
        else
          let gProbe1 := probeGameForPendingReplacement g1
          match firstPriorityGrantRecipient? gProbe1 false pr1 with
          | some (some q) => .grants (some q)
          | some none => .implicitResolutionChoice
          | none =>
            if continuationGrantsPriority gProbe1 false pr1 then .grants none
            else if continuationSettlesControlFlow gProbe1 false pr1 then .settlesPromptOrOver
            else .noGrant
      | none => .noGrant
    else if g1.proposedSpell.isSome then .noGrant
    else if hadPreReconcileCont then
      match preExplicitGrant? with
      | some q =>
        match livingPriorityInstead? g1 q with
        | some q' => .grants (some q')
        | none => .settlesPromptOrOver
      | none =>
        if !hadPrePrio then
          match livingPriorityInstead? g1 caster with
          | some q' => .grants (some q')
          | none => .settlesPromptOrOver
        else .implicitResolutionChoice
    else
      match livingPriorityInstead? g1 g1.priority with
      | some q => .grants (some q)
      | none => .settlesPromptOrOver

private partial def probeCompleteTurnFaceUpOutcome (g : Game) (caster : PlayerId)
    (spellId : ObjectId) (hadOuter : Bool)
    (followedByFinishChoice : Bool := false)
    (followedByExplicitPriority? : Option PlayerId := none) : ConcedePriorityOutcome :=
  if g.over || g.livingPlayers.isEmpty then .settlesPromptOrOver
  else
    match prepareGameForTurnFaceUpProbe g caster spellId hadOuter with
    | some gClean =>
      probeCompleteTurnFaceUpClean gClean caster spellId hadOuter
        followedByFinishChoice followedByExplicitPriority?
    | none =>
      if let .chooseReplacement .. := g.pending then
        let gD := drainProbePausedStep g
        if gD.over || gD.livingPlayers.isEmpty ||
            (gD.pending != .none && (match gD.pending with | .chooseReplacement .. => false | _ => true)) ||
            gD.afterRandom != .none then
          .settlesPromptOrOver
        else if hadOuter then .noGrant else .settlesPromptOrOver
      else .settlesPromptOrOver

private partial def projectProposedSpellCostStages (g : Game) (prop : ProposedSpell)
    (stage : ProposedSpellCostStage) (grantPriority hadOuter openCont : Bool) :
    CostStageProjection :=
  let selfLeaf : PendingReplacement :=
    .finishProposedSpellCosts stage grantPriority hadOuter openCont
  let localOuter? :=
    g.pendingReplacement.bind (removeExactPendingReplacement selfLeaf)
  let effHadOuter := hadOuter || localOuter?.isSome
  let wrapOuter (outer : PendingReplacement) : PendingReplacement :=
    if hadOuter then outer else outer.ensureEndsWithFinishResolutionChoice
  let g0 := if g.pendingReplacement.isSome then g.change (.pendingReplacement none) else g
  let restoreLocal (gIn : Game) : Game :=
    match localOuter? with
    | some outer => gIn.chainPendingReplacement outer
    | none => gIn
  let pauseWith (gIn : Game) (nextStage : ProposedSpellCostStage) : Game :=
    let g1 := gIn.chainPendingReplacement
      (.finishProposedSpellCosts nextStage grantPriority effHadOuter openCont)
    match localOuter? with
    | some outer => g1.chainPendingReplacement (wrapOuter outer)
    | none => g1
  match stage with
  | .teamwork =>
    if prop.teamworkPaid && !prop.teamworkCreatures.isEmpty then
      match g0.tapTeamworkCreaturesForProposed prop with
      | .error _ => .failed
      | .ok g1 =>
        if let .chooseReplacement .. := g1.pending then
          .paused (pauseWith g1 .behold)
        else if g1.over || g1.livingPlayers.isEmpty || g1.pending != .none || g1.afterRandom != .none then
          .paused (restoreLocal g1)
        else
          projectProposedSpellCostStages (restoreLocal g1) prop .behold grantPriority hadOuter openCont
    else
      projectProposedSpellCostStages g prop .behold grantPriority hadOuter openCont
  | .behold =>
    if prop.needsBehold.isSome then
      match g0.payBeholdForProposed prop with
      | .error _ => .failed
      | .ok g1 =>
        if let .chooseReplacement .. := g1.pending then
          .paused (pauseWith g1 .sneak)
        else if g1.over || g1.livingPlayers.isEmpty || g1.pending != .none || g1.afterRandom != .none then
          .paused (restoreLocal g1)
        else
          projectProposedSpellCostStages (restoreLocal g1) prop .sneak grantPriority hadOuter openCont
    else
      projectProposedSpellCostStages g prop .sneak grantPriority hadOuter openCont
  | .sneak =>
    match prop.sneakAttacker with
    | some a =>
      match g0.withProposalActionM .costAction (fun g => g.paySneak prop.caster prop.spellId a) with
      | .error _ => .failed
      | .ok g1 =>
        if let .chooseReplacement .. := g1.pending then
          .paused (pauseWith g1 .finalize)
        else if g1.over || g1.livingPlayers.isEmpty || g1.pending != .none || g1.afterRandom != .none then
          .paused (restoreLocal g1)
        else
          projectProposedSpellCostStages (restoreLocal g1) prop .finalize grantPriority hadOuter openCont
    | none =>
      projectProposedSpellCostStages g prop .finalize grantPriority hadOuter openCont
  | .finalize => .ready g

private partial def classifyFinishProposedSpellCosts (g : Game)
    (stage : ProposedSpellCostStage) (grantPriority hadOuter openCont : Bool)
    (followedByFinishChoice : Bool := false)
    (followedByExplicitPriority? : Option PlayerId := none) :
    ConcedePriorityOutcome :=
  if g.over || g.livingPlayers.isEmpty then .settlesPromptOrOver
  else
    match g.proposedSpell with
    | none => .noGrant
    | some prop =>
      if let .chooseReplacement .. := g.pending then
        -- `finishProposedSpellCosts` (`Decisions.lean:5526-5528`) returns immediately
        -- while `.chooseReplacement` is open (for every stage) without inspecting
        -- stage failures, sacrifice/discard costs, or permanent status.
        if hadOuter then .noGrant else .settlesPromptOrOver
      else
        match projectProposedSpellCostStages g prop stage grantPriority hadOuter openCont with
        | .failed =>
          classifyProposedSpellReversal g prop followedByFinishChoice followedByExplicitPriority?
        | .paused gP =>
          if gP.over || gP.livingPlayers.isEmpty then .settlesPromptOrOver
          else if let .chooseReplacement .. := gP.pending then
            if gP.anyContinuationSettlesControlFlow then
              match gP.firstContinuationPriorityGrant? with
              | some (some q) => .grants (some q)
              | some none => .implicitResolutionChoice
              | none => if gP.anyContinuationGrantsPriority then .grants none else .settlesPromptOrOver
            else if hadOuter then .noGrant
            else .settlesPromptOrOver
          else .settlesPromptOrOver
        | .ready gFin =>
          let excludeId := prop.sourceId.getD prop.spellId
          if prop.needsSacrificeOther &&
              !(gFin.sacrificeCreatureOrArtifactChoices prop.caster excludeId).isEmpty then
            .settlesPromptOrOver
          else if prop.needsSacrificeOther then
            classifyProposedSpellReversal gFin prop followedByFinishChoice followedByExplicitPriority?
          else if prop.needsDiscardCard && !(gFin.discardableHandIds prop.caster).isEmpty then
            .settlesPromptOrOver
          else if prop.needsDiscardCard then
            classifyProposedSpellReversal gFin prop followedByFinishChoice followedByExplicitPriority?
          else if prop.kind == .turnFaceUp then
            if !(gFin.stillInGame prop.caster &&
                (gFin.findObject? prop.spellId).any (fun o =>
                  o.isOnBattlefield && o.status.faceDown && gFin.controlledBy o prop.caster)) then
              classifyProposedSpellReversal gFin prop followedByFinishChoice followedByExplicitPriority?
            else
              let selfLeaf : PendingReplacement :=
                .finishProposedSpellCosts .finalize grantPriority hadOuter openCont
              let localOuter? :=
                gFin.pendingReplacement.bind (removeExactPendingReplacement selfLeaf)
              let effHadOuter := hadOuter || localOuter?.isSome
              let g0 :=
                let g0 := if gFin.pendingReplacement.isSome then gFin.change (.pendingReplacement none) else gFin
                g0.changes #[.pending .none, .consecutivePasses 0]
              match localOuter? with
              | none =>
                probeCompleteTurnFaceUpClean g0 prop.caster prop.spellId hadOuter
                  followedByFinishChoice followedByExplicitPriority?
              | some outer =>
                let appendedFinishChoice := !hadOuter && !outer.endsWithPriorityGrant
                let (gTurned, callerShouldResume) :=
                  g0.completeTurnFaceUp prop.caster prop.spellId (hadOuterReplacement := effHadOuter)
                let g1Raw := gTurned.chainProposalOuterCont prop.caster outer
                  (grantPriority := grantPriority) (hadOuterReplacement := hadOuter) (openCont := openCont)
                let paused := match g1Raw.pending with | .chooseReplacement .. => true | _ => false
                let g1 :=
                  if !paused && !hadOuter && (callerShouldResume ||
                      (g1Raw.pending == .none && !g1Raw.over)) then
                    g1Raw.resumeAfterBecomeCastFwd
                  else g1Raw
                if g1.over || g1.livingPlayers.isEmpty then .settlesPromptOrOver
                else if let .chooseReplacement .. := g1.pending then
                  if g1.anyContinuationSettlesControlFlow then
                    match g1.firstContinuationPriorityGrant? with
                    | some (some q) => .grants (some q)
                    | some none => .implicitResolutionChoice
                    | none => if g1.anyContinuationGrantsPriority then .grants none else .settlesPromptOrOver
                  else if hadOuter then .noGrant
                  else .settlesPromptOrOver
                else if g1.pending != .none || g1.afterRandom != .none then .settlesPromptOrOver
                else if hadOuter then
                  match g1.pendingReplacement with
                  | some pr1 =>
                    let gProbe1 := probeGameForPendingReplacement g1
                    match firstPriorityGrantRecipient? gProbe1 false pr1 with
                    | some (some q) => .grants (some q)
                    | some none => .implicitResolutionChoice
                    | none =>
                      if continuationGrantsPriority gProbe1 false pr1 then .grants none
                      else if continuationSettlesControlFlow gProbe1 false pr1 then .settlesPromptOrOver
                      else .noGrant
                  | none => .noGrant
                else if g1.proposedSpell.isSome then .noGrant
                else if appendedFinishChoice then
                  -- `chainProposalOuterCont` appended `.finishResolutionChoice` after `outer`
                  -- (saving `prop.caster` in `pendingPriority` when `grantPriority && !openCont`
                  -- and `pendingPriority.isNone`): execute `outer` alone to get `gMid` and classify
                  -- the trailing `.finishResolutionChoice` on `gMid`.
                  let preMidPrio := gTurned.pendingPriority
                  let preMidEvSize := gTurned.events.size
                  let gTurnedWithPrio :=
                    if !gTurned.over && grantPriority && !hadOuter && !openCont &&
                        !outer.endsWithPriorityGrant && gTurned.pendingPriority.isNone then
                      gTurned.change (.pendingPriority (some (gTurned.priorityInstead prop.caster)))
                    else gTurned
                  let gMid0 := gTurnedWithPrio.chainPendingReplacement outer
                  let gMid :=
                    if !paused && (callerShouldResume || (gMid0.pending == .none && !gMid0.over)) then
                      gMid0.resumeAfterBecomeCastFwd
                    else gMid0
                  if gMid.over || gMid.livingPlayers.isEmpty ||
                      gMid.pending != .none || gMid.afterRandom != .none then
                    .settlesPromptOrOver
                  else
                    let wroteOrChangedPrio : Bool :=
                      gMid.pendingPriority.isSome &&
                        (gMid.pendingPriority != preMidPrio ||
                          (gMid.events.extract preMidEvSize gMid.events.size).any fun
                            | .engine _ (.pendingPriority (some _)) _ => true
                            | _ => false)
                    match classifyFinishResolutionChoice gMid with
                    | .implicitResolutionChoice =>
                      if wroteOrChangedPrio then
                        match gMid.pendingPriority with
                        | some q =>
                          match livingPriorityInstead? gMid q with
                          | some q' => .grants (some q')
                          | none => .settlesPromptOrOver
                        | none => .implicitResolutionChoice
                      else .implicitResolutionChoice
                    | other => other
                else
                  let gProbe := probeGameForPendingReplacement gTurned
                  let effOuter :=
                    match gTurned.pendingReplacement with
                    | some prePr => .seq prePr outer
                    | none => outer
                  match firstPriorityGrantRecipient? gProbe false effOuter with
                  | some (some q) =>
                    match livingPriorityInstead? g1 q with
                    | some q' => .grants (some q')
                    | none => .settlesPromptOrOver
                  | some none => .implicitResolutionChoice
                  | none =>
                    if continuationGrantsPriority gProbe false effOuter then .grants none
                    else if continuationSettlesControlFlow gProbe false effOuter then .settlesPromptOrOver
                    else .noGrant
          else if gFin.stillInGame prop.caster && (gFin.findObject? prop.spellId).any (·.zone == .stack) then
            let selfLeaf : PendingReplacement :=
              .finishProposedSpellCosts .finalize grantPriority hadOuter openCont
            let localOuter? :=
              gFin.pendingReplacement.bind (removeExactPendingReplacement selfLeaf)
            match localOuter? with
            | none =>
              if hadOuter then
                finishPostCastOutcome gFin prop.caster openCont false (some prop.spellId)
              else if grantPriority then
                finishPostCastOutcome gFin prop.caster openCont true (some prop.spellId)
              else if prop.resolutionCast then
                finishPostCastOutcome gFin prop.caster openCont false (some prop.spellId)
                  (delegateFinishChoice := true)
              else
                finishPostCastOutcome gFin prop.caster openCont false (some prop.spellId)
            | some outer =>
              let wrapOuter (o : PendingReplacement) : PendingReplacement :=
                if hadOuter then o else o.ensureEndsWithFinishResolutionChoice
              let wrapped := wrapOuter outer
              let g0 :=
                (if gFin.pendingReplacement.isSome then gFin.change (.pendingReplacement none) else gFin).changes
                  #[.pending .none, .consecutivePasses 0]
              let clearChanges : Array EngineChange :=
                (if g0.proposedSpell.isSome then #[EngineChange.proposedSpell none] else #[]) ++
                (if g0.proposalCheckpoint.isSome then #[EngineChange.clearProposalCheckpoint] else #[]) ++
                #[EngineChange.castingFromTop false]
              let gCast0 := g0.changes clearChanges
              let gCast0 :=
                match gCast0.findObject? prop.spellId with
                | some sp => gCast0.putCastTriggersOnStack prop.caster sp
                | none => gCast0
              let savesOuterPrio (gCur : Game) : Bool :=
                !gCur.over && grantPriority && !hadOuter && !openCont &&
                  !outer.endsWithPriorityGrant && gCur.pendingPriority.isNone
              if gCast0.over || gCast0.livingPlayers.isEmpty then .settlesPromptOrOver
              else if let .chooseReplacement .. := gCast0.pending then
                let wrotePrio := savesOuterPrio gCast0
                let gP := gCast0.chainProposalOuterCont prop.caster outer
                  (grantPriority := grantPriority) (hadOuterReplacement := hadOuter) (openCont := openCont)
                if gP.anyContinuationSettlesControlFlow then
                  match gP.firstContinuationPriorityGrant? with
                  | some (some q) => .grants (some q)
                  | some none =>
                    if wrotePrio then
                      match livingPriorityInstead? gP prop.caster with
                      | some q => .grants (some q)
                      | none => .settlesPromptOrOver
                    else .implicitResolutionChoice
                  | none => if gP.anyContinuationGrantsPriority then .grants none else .settlesPromptOrOver
                else if hadOuter then .noGrant
                else .settlesPromptOrOver
              else if gCast0.pending != .none || gCast0.afterRandom != .none ||
                  spellOpensAncestryScry gCast0 prop.caster prop.spellId then
                .settlesPromptOrOver
              else
                let gCast1 := simulateFinishPostCastBody gCast0 prop.caster
                if gCast1.over || gCast1.livingPlayers.isEmpty then .settlesPromptOrOver
                else if let .chooseReplacement .. := gCast1.pending then
                  let wrotePrio := savesOuterPrio gCast1
                  let gP := gCast1.chainProposalOuterCont prop.caster outer
                    (grantPriority := grantPriority) (hadOuterReplacement := hadOuter) (openCont := openCont)
                  if gP.anyContinuationSettlesControlFlow then
                    match gP.firstContinuationPriorityGrant? with
                    | some (some q) => .grants (some q)
                    | some none =>
                      if wrotePrio then
                        match livingPriorityInstead? gP prop.caster with
                        | some q => .grants (some q)
                        | none => .settlesPromptOrOver
                      else .implicitResolutionChoice
                    | none => if gP.anyContinuationGrantsPriority then .grants none else .settlesPromptOrOver
                  else if hadOuter then .noGrant
                  else .settlesPromptOrOver
                else if gCast1.pending != .none || gCast1.afterRandom != .none then .settlesPromptOrOver
                else
                  let wrotePrio := savesOuterPrio gCast1
                  let gCast1' :=
                    if wrotePrio then gCast1.change (.pendingPriority (some (gCast1.priorityInstead prop.caster)))
                    else gCast1
                  let gProbe := probeGameForPendingReplacement gCast1'
                  match firstPriorityGrantRecipient? gProbe false wrapped with
                  | some (some q) => .grants (some q)
                  | some none =>
                    if wrotePrio then
                      match livingPriorityInstead? gCast1' prop.caster with
                      | some q => .grants (some q)
                      | none => .settlesPromptOrOver
                    else .implicitResolutionChoice
                  | none =>
                    if continuationGrantsPriority gProbe false wrapped then .grants none
                    else if continuationSettlesControlFlow gProbe false wrapped then .settlesPromptOrOver
                    else .noGrant
          else
            classifyProposedSpellReversal gFin prop followedByFinishChoice followedByExplicitPriority?

private partial def classifyFinishBecomeCast (g : Game) (caster : PlayerId) (spellId : ObjectId)
    (grantPriority hadOuter openCont : Bool)
    (followedByFinishChoice : Bool := false)
    (followedByExplicitPriority? : Option PlayerId := none) : ConcedePriorityOutcome :=
  if g.over || g.livingPlayers.isEmpty then .settlesPromptOrOver
  else if let .chooseReplacement .. := g.pending then
    if hadOuter then .noGrant else .settlesPromptOrOver
  else if g.stillInGame caster && (g.findObject? spellId).any (·.zone == .stack) then
    finishPostCastOutcome g caster openCont (grantPriority && !hadOuter) (some spellId)
  else if let some prop := g.proposedSpell then
    if g.proposalCheckpoint.isSome then
      classifyProposedSpellReversal g prop followedByFinishChoice followedByExplicitPriority?
    else
      let clearChanges : Array EngineChange :=
        #[EngineChange.proposedSpell none]
      let gC := g.changes clearChanges
      if gC.over || gC.livingPlayers.isEmpty then .settlesPromptOrOver
      else if gC.pending != .none then
        if isSelfSettlingPending gC.pending then .settlesPromptOrOver else .noGrant
      else if !hadOuter && (gC.pendingReplacement.isSome ||
          !gC.outerPendingReplacements.isEmpty || gC.currentInterpWait?.isSome) then
        classifyChainFinishChoice gC (if openCont then gC.activePlayer else caster)
      else if !hadOuter && grantPriority then
        receivePriorityOutcome gC (gC.priorityInstead (if openCont then gC.activePlayer else caster))
          (recheckSba := true)
      else .noGrant
  else
    let clearChanges : Array EngineChange :=
      if g.proposalCheckpoint.isSome then #[EngineChange.clearProposalCheckpoint] else #[]
    let gC := if clearChanges.isEmpty then g else g.changes clearChanges
    if gC.over || gC.livingPlayers.isEmpty then .settlesPromptOrOver
    else if gC.pending != .none then
      if isSelfSettlingPending gC.pending then .settlesPromptOrOver else .noGrant
    else if !hadOuter && (gC.pendingReplacement.isSome ||
        !gC.outerPendingReplacements.isEmpty || gC.currentInterpWait?.isSome) then
      classifyChainFinishChoice gC (if openCont then gC.activePlayer else caster)
    else if !hadOuter && grantPriority then
      receivePriorityOutcome gC (gC.priorityInstead (if openCont then gC.activePlayer else caster))
        (recheckSba := true)
    else .noGrant

private partial def classifyFinishPostLoyaltyActivated (g : Game) (p : PlayerId)
    (sourceId : Option ObjectId) (abilityId : Option ObjectId)
    (hadOuter openCont : Bool)
    (followedByFinishChoice : Bool := false)
    (followedByExplicitPriority? : Option PlayerId := none) : ConcedePriorityOutcome :=
  if g.over || g.livingPlayers.isEmpty then .settlesPromptOrOver
  else if !g.stillInGame p ||
      !abilityId.all (fun aid =>
        sourceId == some aid || (g.findObject? aid).any (·.zone == .stack)) then
    match g.proposedSpell with
    | some prop =>
      if g.proposalCheckpoint.isSome then
        classifyProposedSpellReversal g prop followedByFinishChoice followedByExplicitPriority?
      else
        let gC := g.change (.proposedSpell none)
        if gC.over || gC.livingPlayers.isEmpty then .settlesPromptOrOver
        else if gC.pending != .none then
          if isSelfSettlingPending gC.pending then .settlesPromptOrOver else .noGrant
        else if hadOuter then .noGrant
        else if gC.pendingReplacement.isSome || !gC.outerPendingReplacements.isEmpty ||
            gC.currentInterpWait?.isSome then
          classifyChainFinishChoice gC (if openCont then gC.activePlayer else p)
        else
          receivePriorityOutcome gC (gC.priorityInstead (if openCont then gC.activePlayer else p))
            (recheckSba := true)
    | none =>
      let gC := if g.proposalCheckpoint.isSome then g.change .clearProposalCheckpoint else g
      if gC.over || gC.livingPlayers.isEmpty then .settlesPromptOrOver
      else if gC.pending != .none then
        if isSelfSettlingPending gC.pending then .settlesPromptOrOver else .noGrant
      else if hadOuter then .noGrant
      else if gC.pendingReplacement.isSome || !gC.outerPendingReplacements.isEmpty ||
          gC.currentInterpWait?.isSome then
        classifyChainFinishChoice gC (if openCont then gC.activePlayer else p)
      else
        receivePriorityOutcome gC (gC.priorityInstead (if openCont then gC.activePlayer else p))
          (recheckSba := true)
  else
    let clearProp := if g.proposedSpell.isSome then #[EngineChange.proposedSpell none] else #[]
    let clearCkpt := if g.proposalCheckpoint.isSome then #[EngineChange.clearProposalCheckpoint] else #[]
    let gC := if clearProp.isEmpty && clearCkpt.isEmpty then g else g.changes (clearProp ++ clearCkpt)
    if gC.pending != .none then
      if isSelfSettlingPending gC.pending then .settlesPromptOrOver else .noGrant
    else if hadOuter then .noGrant
    else if gC.currentInterpWait?.isSome || gC.pendingReplacement.isSome ||
        !gC.outerPendingReplacements.isEmpty then
      classifyChainFinishChoice gC (if openCont then gC.activePlayer else p)
    else
      receivePriorityOutcome gC (if openCont then gC.activePlayer else p) (recheckSba := true)

private partial def classifyFinishBecomeActivated (g : Game) (p : PlayerId) (sourceName : String)
    (sourceId : Option ObjectId) (activation : Option ActivatedAbility)
    (abilityId : Option ObjectId) (sourceSnap : Option EventObject)
    (srcObj? : Option GameObject) (hadOuter openCont : Bool)
    (followedByFinishChoice : Bool := false)
    (followedByExplicitPriority? : Option PlayerId := none) : ConcedePriorityOutcome :=
  if g.over || g.livingPlayers.isEmpty then .settlesPromptOrOver
  else if let .chooseReplacement .. := g.pending then
    if hadOuter then .noGrant else .settlesPromptOrOver
  else
    let activation := activation <|> g.proposedSpell.bind (·.activation)
    let abilityId := abilityId <|> g.proposedSpell.map (·.spellId) <|> g.stack.back?.map (·.objectId)
    let chosenX := ((abilityId.bind g.findObject?).bind (·.chosenX)).getD 0
    let sinceIdx := (g.targetProposalCheckpoint?.map (·.eventsSize)).getD 0
    let unpaidLoyaltyUnpayable : Bool :=
      match activation.bind (·.cost.netLoyaltyDelta chosenX) with
      | none => false
      | some k =>
        if g.proposedSpell.any ProposedSpell.loyaltyPaid ||
            sourceId.any (fun sid =>
              g.sourceCounterCostPaidFor sid abilityId .loyalty (some .loyalty) sinceIdx) then
          false
        else
          match sourceId.bind g.findObject? with
          | none => true
          | some src =>
            !src.isOnBattlefield || !g.controlledBy src p ||
              g.loyaltyActivatedThisTurn src.id ||
              (k < 0 && (src.status.loyaltyCounters : Int) < -k)
    if unpaidLoyaltyUnpayable then
      match g.proposedSpell with
      | some prop =>
        if g.proposalCheckpoint.isSome then
          classifyProposedSpellReversal g prop followedByFinishChoice followedByExplicitPriority?
        else
          let gC := g.change (.proposedSpell none)
          if gC.over || gC.livingPlayers.isEmpty then .settlesPromptOrOver
          else if gC.pending != .none then
            if isSelfSettlingPending gC.pending then .settlesPromptOrOver else .noGrant
          else if !hadOuter && (gC.pendingReplacement.isSome ||
              !gC.outerPendingReplacements.isEmpty || gC.currentInterpWait?.isSome) then
            classifyChainFinishChoice gC (if openCont then gC.activePlayer else p)
          else if !hadOuter then
            receivePriorityOutcome gC (gC.priorityInstead (if openCont then gC.activePlayer else p))
              (recheckSba := true)
          else .noGrant
      | none =>
        let gC := if g.proposalCheckpoint.isSome then g.change .clearProposalCheckpoint else g
        if gC.over || gC.livingPlayers.isEmpty then .settlesPromptOrOver
        else if gC.pending != .none then
          if isSelfSettlingPending gC.pending then .settlesPromptOrOver else .noGrant
        else if !hadOuter && (gC.pendingReplacement.isSome ||
            !gC.outerPendingReplacements.isEmpty || gC.currentInterpWait?.isSome) then
          classifyChainFinishChoice gC (if openCont then gC.activePlayer else p)
        else if !hadOuter then
          receivePriorityOutcome gC (gC.priorityInstead (if openCont then gC.activePlayer else p))
            (recheckSba := true)
        else .noGrant
    else
      let localOuter? := g.pendingReplacement
      let effHadOuter := hadOuter || localOuter?.isSome
      let g0 := if localOuter?.isSome then g.change (.pendingReplacement none) else g
      let gL :=
        match activation.bind (·.cost.netLoyaltyDelta chosenX) with
        | some k =>
          match sourceId.bind g0.findObject? with
          | some src =>
            if !(g0.proposedSpell.any ProposedSpell.loyaltyPaid) &&
                !g0.sourceCounterCostPaidFor src.id abilityId .loyalty (some .loyalty) sinceIdx then
              g0.payLoyaltyDelta p src k (forObject := abilityId)
            else g0
          | none => g0
        | none => g0
      let wrapOuter (outer : PendingReplacement) : PendingReplacement :=
        if hadOuter then outer else outer.ensureEndsWithFinishResolutionChoice
      if let .chooseReplacement .. := gL.pending then
        let wrotePrio :=
          localOuter?.any fun outer =>
            !gL.over && !hadOuter && !openCont && !outer.endsWithPriorityGrant && gL.pendingPriority.isNone
        let gP := gL.chainPendingReplacement (.finishPostLoyaltyActivated p sourceName sourceId
          activation abilityId sourceSnap srcObj? effHadOuter openCont)
        let gP :=
          match localOuter? with
          | some outer => gP.chainProposalOuterCont p outer (hadOuterReplacement := hadOuter) (openCont := openCont)
          | none => gP
        if gP.anyContinuationSettlesControlFlow then
          match gP.firstContinuationPriorityGrant? with
          | some (some q) => .grants (some q)
          | some none =>
            if wrotePrio then
              match livingPriorityInstead? gP p with
              | some q => .grants (some q)
              | none => .settlesPromptOrOver
            else .implicitResolutionChoice
          | none => if gP.anyContinuationGrantsPriority then .grants none else .settlesPromptOrOver
        else if hadOuter then .noGrant
        else .settlesPromptOrOver
      else
        match localOuter? with
        | none =>
          classifyFinishPostLoyaltyActivated gL p sourceId abilityId hadOuter openCont
            followedByFinishChoice followedByExplicitPriority?
        | some outer =>
          let wrapped := wrapOuter outer
          if gL.over || !gL.stillInGame p ||
              !abilityId.all (fun aid =>
                sourceId == some aid || (gL.findObject? aid).any (·.zone == .stack)) then
            match gL.proposedSpell with
            | some prop =>
              if gL.proposalCheckpoint.isSome then
                classifyProposedSpellReversal (gL.chainPendingReplacement wrapped) prop
                  followedByFinishChoice followedByExplicitPriority?
              else if gL.over || gL.livingPlayers.isEmpty then .settlesPromptOrOver
              else
                let gC := gL.change (.proposedSpell none)
                if gC.pending != .none then
                  if isSelfSettlingPending gC.pending then .settlesPromptOrOver else .noGrant
                else
                  let gProbe := probeGameForPendingReplacement gC
                  match firstPriorityGrantRecipient? gProbe false wrapped with
                  | some (some q) => .grants (some q)
                  | some none => .implicitResolutionChoice
                  | none =>
                    if continuationGrantsPriority gProbe false wrapped then .grants none
                    else if continuationSettlesControlFlow gProbe false wrapped then .settlesPromptOrOver
                    else .noGrant
            | none =>
              if gL.over || gL.livingPlayers.isEmpty then .settlesPromptOrOver
              else
                let gC := if gL.proposalCheckpoint.isSome then gL.change .clearProposalCheckpoint else gL
                if gC.pending != .none then
                  if isSelfSettlingPending gC.pending then .settlesPromptOrOver else .noGrant
                else
                  let gProbe := probeGameForPendingReplacement gC
                  match firstPriorityGrantRecipient? gProbe false wrapped with
                  | some (some q) => .grants (some q)
                  | some none => .implicitResolutionChoice
                  | none =>
                    if continuationGrantsPriority gProbe false wrapped then .grants none
                    else if continuationSettlesControlFlow gProbe false wrapped then .settlesPromptOrOver
                    else .noGrant
          else if hadOuter then
            let clearProp := if gL.proposedSpell.isSome then #[EngineChange.proposedSpell none] else #[]
            let clearCkpt := if gL.proposalCheckpoint.isSome then #[EngineChange.clearProposalCheckpoint] else #[]
            let gC := if clearProp.isEmpty && clearCkpt.isEmpty then gL else gL.changes (clearProp ++ clearCkpt)
            let gProbe := probeGameForPendingReplacement gC
            match firstPriorityGrantRecipient? gProbe false wrapped with
            | some (some q) => .grants (some q)
            | some none => .implicitResolutionChoice
            | none =>
              if continuationGrantsPriority gProbe false wrapped then .grants none
              else if continuationSettlesControlFlow gProbe false wrapped then .settlesPromptOrOver
              else .noGrant
          else
            let clearProp := if gL.proposedSpell.isSome then #[EngineChange.proposedSpell none] else #[]
            let clearCkpt := if gL.proposalCheckpoint.isSome then #[EngineChange.clearProposalCheckpoint] else #[]
            let gC := if clearProp.isEmpty && clearCkpt.isEmpty then gL else gL.changes (clearProp ++ clearCkpt)
            match firstPriorityGrantRecipient? gC false wrapped with
            | some (some q) => .grants (some q)
            | some none => .implicitResolutionChoice
            | none =>
              if continuationSettlesControlFlow gC false wrapped then .settlesPromptOrOver
              else .noGrant

private partial def classifyCompleteActivation (g : Game) (hadOuter openCont : Bool)
    (followedByFinishChoice : Bool := false)
    (followedByExplicitPriority? : Option PlayerId := none) :
    ConcedePriorityOutcome :=
  if g.over || g.livingPlayers.isEmpty then .settlesPromptOrOver
  else if let .chooseReplacement .. := g.pending then
    if hadOuter then .noGrant else .settlesPromptOrOver
  else
    match g.proposedSpell with
    | none => .noGrant
    | some prop =>
      match prop.sourceId with
      | none =>
        classifyProposedSpellReversal g prop followedByFinishChoice followedByExplicitPriority?
      | some sid =>
        let x := ((g.findObject? prop.spellId).bind (·.chosenX)).getD 0
        let srcSnap := (g.findObject? sid).map g.snapshot |>.orElse (fun _ => some prop.originalSnapshot)
        let fallbackName :=
          if prop.originalSnapshot.name.isEmpty then g.name prop.original
          else prop.originalSnapshot.name
        let srcName := (g.findObject? sid).map g.name |>.getD fallbackName
        let localOuter? := g.pendingReplacement
        let effHadOuter := hadOuter || localOuter?.isSome
        let g0 := if localOuter?.isSome then g.change (.pendingReplacement none) else g
        match g0.payActivationExtraCosts prop.caster sid prop.tapSource prop.sacrificeSource
            prop.payLife prop.discardSource prop.activation (if prop.removePlusOneX then x else 0)
            (callerOuter? := localOuter?) with
        | .error _ =>
          classifyProposedSpellReversal g prop followedByFinishChoice followedByExplicitPriority?
        | .ok g1 =>
          if g1.proposedSpell.isNone then
            classifyProposedSpellReversal g prop followedByFinishChoice followedByExplicitPriority?
          else if prop.needsSacrificeOther then
            if let .chooseReplacement .. := g1.pending then
              let gP := (g1.change (.consecutivePasses 0)).chainPendingReplacement
                (.restorePending (.sacrificePermanent prop.caster sid))
              let gP :=
                match localOuter? with
                | some outer => gP.chainPendingReplacement outer
                | none => gP
              if gP.anyContinuationSettlesControlFlow then
                match gP.firstContinuationPriorityGrant? with
                | some (some q) => .grants (some q)
                | some none => .implicitResolutionChoice
                | none => if gP.anyContinuationGrantsPriority then .grants none else .settlesPromptOrOver
              else if hadOuter then .noGrant
              else .settlesPromptOrOver
            else if (g1.sacrificeCreatureOrArtifactChoices prop.caster sid).isEmpty then
              classifyProposedSpellReversal g prop followedByFinishChoice followedByExplicitPriority?
            else .settlesPromptOrOver
          else
            let paused := match g1.pending with | .chooseReplacement .. => true | _ => false
            let wrapOuter (outer : PendingReplacement) : PendingReplacement :=
              if hadOuter then outer else outer.ensureEndsWithFinishResolutionChoice
            if paused then
              let gP := (g1.change (.consecutivePasses 0)).chainPendingReplacement
                (.finishBecomeActivated prop.caster srcName prop.sourceId prop.activation
                  (some prop.spellId) srcSnap (some prop.original) effHadOuter openCont)
              let gP :=
                match localOuter? with
                | some outer => gP.chainPendingReplacement (wrapOuter outer)
                | none => gP
              if gP.anyContinuationSettlesControlFlow then
                match gP.firstContinuationPriorityGrant? with
                | some (some q) => .grants (some q)
                | some none => .implicitResolutionChoice
                | none => if gP.anyContinuationGrantsPriority then .grants none else .settlesPromptOrOver
              else if hadOuter then .noGrant
              else .settlesPromptOrOver
            else
              let g2 :=
                match localOuter? with
                | some outer => g1.chainPendingReplacement (wrapOuter outer)
                | none => g1
              let g2 := g2.changes #[.pending .none, .consecutivePasses 0]
              classifyFinishBecomeActivated g2 prop.caster srcName prop.sourceId prop.activation
                (some prop.spellId) srcSnap (some prop.original) hadOuter openCont
                followedByFinishChoice followedByExplicitPriority?

private partial def classifyAfterWardResolvedFuel (g : Game) : Nat → ConcedePriorityOutcome
  | 0 => .settlesPromptOrOver
  | fuel + 1 =>
    let replaceTopOuters (gIn : Game) (popCount : Nat) (toPush : Array PendingReplacement) : Game :=
      let gPop := (Array.replicate popCount EngineChange.popOuterPendingReplacement).foldl Game.change gIn
      if toPush.isEmpty then gPop
      else
        let gPop := if gPop.continuations.isEmpty then gPop.change (.pushContinuationFrame {}) else gPop
        (toPush.map EngineChange.pushOuterPendingReplacement).foldl Game.change gPop
    let rec drainTriggerWithDeferredExile (gIn : Game) : Nat → Game
      | 0 => gIn
      | k + 1 =>
        let gD := gIn.drainPendingContinuations
        if !gD.over && gD.currentInterpWait?.isSome &&
            gD.pending == .none && gD.afterRandom == .none && gD.proposedSpell.isNone &&
            (gD.pendingMayCastFromExile.isSome || gD.pendingFreeCopies.isSome) then
          let gR := gD.reopenDeferredExileCasts
          if !gR.over && gR.pending == .none && gR.afterRandom == .none then
            drainTriggerWithDeferredExile gR k
          else gR
        else gD
    let g :=
      match g.pending with
      | .payWard .. => g.change (.pending .none)
      | _ => g
    if g.over || g.livingPlayers.isEmpty then .settlesPromptOrOver
    else if g.currentInterpWait?.isSome &&
        (match g.pending with | .none | .chooseReplacement .. => false | _ => true) then
      .settlesPromptOrOver
    else if g.currentInterpWait?.isSome && g.afterRandom != .none then
      .settlesPromptOrOver
    else
      let g :=
        if g.currentInterpWait?.isSome && g.pending == .none && g.afterRandom == .none then
          let stashedPending := g.pendingReplacement
          let stashedOuters := g.outerPendingReplacements
          let g0 := if stashedPending.isSome then g.change (.pendingReplacement none) else g
          let g0 := (Array.replicate stashedOuters.size EngineChange.popOuterPendingReplacement).foldl Game.change g0
          let gD := drainTriggerWithDeferredExile g0 8
          if gD.over then gD
          else
            let drainSuffix :=
              if gD.pending != .none || gD.afterRandom != .none then gD.outerPendingReplacements
              else #[]
            if gD.currentInterpWait?.isSome then
              let wardTail :=
                match stashedPending with
                | some c => stashedOuters.push c
                | none => stashedOuters
              replaceTopOuters gD drainSuffix.size (wardTail ++ drainSuffix)
            else
              if gD.pending != .none || gD.afterRandom != .none then
                let wardTail :=
                  match stashedPending with
                  | some c => stashedOuters.push c
                  | none => stashedOuters
                if wardTail.isEmpty then gD
                else replaceTopOuters gD drainSuffix.size (wardTail ++ drainSuffix)
              else
                let gD :=
                  match stashedPending with
                  | some c => gD.chainPendingReplacement c
                  | none => gD
                if stashedOuters.isEmpty then gD
                else replaceTopOuters gD drainSuffix.size (stashedOuters ++ drainSuffix)
        else g
      if g.over || g.livingPlayers.isEmpty then .settlesPromptOrOver
      else if let .chooseReplacement .. := g.pending then
        if g.anyContinuationSettlesControlFlow then
          match g.firstContinuationPriorityGrant? with
          | some (some q) => .grants (some q)
          | some none => .implicitResolutionChoice
          | none => if g.anyContinuationGrantsPriority then .grants none else .settlesPromptOrOver
        else
          let gD := drainProbePausedStep g
          if gD.over || gD.livingPlayers.isEmpty || gD.pending != .none ||
              gD.afterRandom != .none || gD.pendingReplacement.isSome then
            .settlesPromptOrOver
          else classifyAfterWardResolvedFuel gD fuel
      else if g.pending != .none || g.afterRandom != .none then .settlesPromptOrOver
      else if let some pr := g.pendingReplacement then
        let gClean := (g.change (.pendingReplacement none)).popEmptyTopContinuationFrames
        match firstPriorityGrantRecipient? gClean false pr with
        | some (some q) => .grants (some q)
        | some none => .implicitResolutionChoice
        | none =>
          if continuationSettlesControlFlow gClean false pr then .settlesPromptOrOver
          else
            let (gAfter, _) := advanceProbeOnResume gClean false pr
            classifyAfterWardResolvedFuel gAfter fuel
      else if let some outer := g.outerPendingReplacements.back? then
        let gClean := (g.change .popOuterPendingReplacement).popEmptyTopContinuationFrames
        match firstPriorityGrantRecipient? gClean false outer with
        | some (some q) => .grants (some q)
        | some none => .implicitResolutionChoice
        | none =>
          if continuationSettlesControlFlow gClean false outer then .settlesPromptOrOver
          else
            let (gAfter, _) := advanceProbeOnResume gClean false outer
            classifyAfterWardResolvedFuel gAfter fuel
      else if g.proposedSpell.isNone &&
          (g.pendingMayCastFromExile.isSome || g.pendingFreeCopies.isSome) then
        let g2 := g.reopenDeferredExileCasts
        if g2.over || g2.livingPlayers.isEmpty then .settlesPromptOrOver
        else if let .chooseReplacement .. := g2.pending then
          if g2.anyContinuationSettlesControlFlow then
            match g2.firstContinuationPriorityGrant? with
            | some (some q) => .grants (some q)
            | some none => .implicitResolutionChoice
            | none => if g2.anyContinuationGrantsPriority then .grants none else .settlesPromptOrOver
          else
            let gD := drainProbePausedStep g2
            if gD.over || gD.livingPlayers.isEmpty || gD.pending != .none ||
                gD.afterRandom != .none || gD.pendingReplacement.isSome then
              .settlesPromptOrOver
            else classifyAfterWardResolvedFuel gD fuel
        else if g2.pending != .none || g2.afterRandom != .none then .settlesPromptOrOver
        else classifyAfterWardResolvedFuel g2 fuel
      else
        let g := g.completeActiveResolutions
        if g.over || g.livingPlayers.isEmpty then .settlesPromptOrOver
        else if let .chooseReplacement .. := g.pending then
          if g.anyContinuationSettlesControlFlow then
            match g.firstContinuationPriorityGrant? with
            | some (some q) => .grants (some q)
            | some none => .implicitResolutionChoice
            | none => if g.anyContinuationGrantsPriority then .grants none else .settlesPromptOrOver
          else
            let gD := drainProbePausedStep g
            if gD.over || gD.livingPlayers.isEmpty || gD.pending != .none ||
                gD.afterRandom != .none || gD.pendingReplacement.isSome then
              .settlesPromptOrOver
            else classifyAfterWardResolvedFuel gD fuel
        else if g.pending != .none || g.afterRandom != .none then
          .settlesPromptOrOver
        else if g.triggerNeedingTargets.isSome then
          if (g.promptTriggerTargetsIfNeeded).pending != .none then .settlesPromptOrOver
          else .implicitResolutionChoice
        else if g.proposedSpell.any (fun prop =>
            !g.stillInGame prop.caster || (g.findObject? prop.spellId).isNone) then
          if g.proposalCheckpoint.isNone then .noGrant
          else
            let gPreRev := if g.pending == .none then g else g.change (.pending .none)
            match gPreRev.reverseProposedSpellCore? (resumeContinuation := true)
                (alwaysGrantPriority := true) with
            | .error _ => .noGrant
            | .ok (gR, needsFinish) =>
              if needsFinish then classifyFinishResolutionChoiceFuel gR fuel
              else if gR.over || gR.livingPlayers.isEmpty then .settlesPromptOrOver
              else if let .chooseReplacement .. := gR.pending then
                if gR.anyContinuationSettlesControlFlow then
                  match gR.firstContinuationPriorityGrant? with
                  | some (some q) => .grants (some q)
                  | some none => .implicitResolutionChoice
                  | none => if gR.anyContinuationGrantsPriority then .grants none else .settlesPromptOrOver
                else .settlesPromptOrOver
              else if gR.pending != .none || gR.afterRandom != .none then .settlesPromptOrOver
              else if gR.continuations.isEmpty && gR.triggerNeedingTargets.isSome then
                if (gR.promptTriggerTargetsIfNeeded).pending != .none then .settlesPromptOrOver
                else .implicitResolutionChoice
              else if gR.proposedSpell.isSome then .noGrant
              else if gR.playersReceivePriority then
                match livingPriorityInstead? gR gR.priority with
                | some q => .grants (some q)
                | none => .settlesPromptOrOver
              else .settlesPromptOrOver
        else if g.proposedSpell.isSome then .noGrant
        else
          let prio := g.pendingPriority.getD g.activePlayer
          match receivePriorityOutcome g prio (recheckSba := true) with
          | .grants _ | .implicitResolutionChoice => .implicitResolutionChoice
          | other => other

private partial def classifyAfterWardResolved (g : Game) : ConcedePriorityOutcome :=
  classifyAfterWardResolvedFuel g 8

private partial def runManaAbilityProbeStep (g : Game) : PendingReplacement → Game
  | .finishActivateManaAbilityPicks p id oname mana remainingPicks remainingCostIds tap sacrificeSelf activatedIdx restriction damageYou isMountain prevPending exileSelf powerUp exhaust riders exileFromZone? discardSelf exileSymIds extraEffect? =>
    g.finishActivateManaAbilityPicks p id oname mana remainingPicks remainingCostIds tap sacrificeSelf activatedIdx restriction damageYou isMountain prevPending
      (exileSelf := exileSelf) (powerUp := powerUp) (exhaust := exhaust) (riders := riders)
      (exileFromZone? := exileFromZone?) (discardSelf := discardSelf) (exileSymIds := exileSymIds)
      (extraEffect? := extraEffect?) (hasFollowingSeq := true)
  | .finishActivateManaAbilityPostSac p id oname srcSnap mana tap activatedIdx restriction damageYou isMountain prevPending powerUp exhaust riders extraEffect? =>
    g.finishActivateManaAbilityPostSac p id oname srcSnap mana tap activatedIdx restriction damageYou isMountain prevPending
      (powerUp := powerUp) (exhaust := exhaust) (riders := riders)
      (extraEffect? := extraEffect?) (hasFollowingSeq := true)
  | _ => g

private partial def classifyManaAbilityPostStep (g : Game) (p : PlayerId) (prevPending : Pending)
    (pr : PendingReplacement) : ConcedePriorityOutcome :=
  if g.over || g.livingPlayers.isEmpty then .settlesPromptOrOver
  else
    let g0 :=
      if prevPending == .none then
        match g.pendingReplacement with
        | some outer =>
          let g1 := if g.continuations.isEmpty then g.change (.pushContinuationFrame {}) else g
          g1.changes #[.pendingReplacement none, .pushOuterPendingReplacement outer]
        | none => g
      else g
    let g1 := runManaAbilityProbeStep g0 pr
    let didActivate : Bool :=
      (g1.events.extract g0.events.size g1.events.size).any fun e =>
        match e with
        | .rules _ (.cast (.abilityActivated _ _ _ (.mana ..))) _ _ => true
        | _ => false
    let didAbort : Bool := !didActivate
    if g1.over || g1.livingPlayers.isEmpty then .settlesPromptOrOver
    else if let .chooseReplacement .. := g1.pending then
      if g1.anyContinuationSettlesControlFlow then
        match g1.firstContinuationPriorityGrant? with
        | some (some q) => .grants (some q)
        | some none =>
          if prevPending == .none then
            let prio := if g1.stillInGame p then g1.priorityInstead p else g1.priorityInstead g1.activePlayer
            match livingPriorityInstead? g1 prio with
            | some q => .grants (some q)
            | none => .settlesPromptOrOver
          else .implicitResolutionChoice
        | none => if g1.anyContinuationGrantsPriority then .grants none else .settlesPromptOrOver
      else if prevPending == .none then
        let gD := drainProbePausedStep g1
        if gD.over || gD.livingPlayers.isEmpty || gD.pending != .none ||
            gD.afterRandom != .none || gD.pendingReplacement.isSome then
          .settlesPromptOrOver
        else
          let prio := if gD.stillInGame p then gD.priorityInstead p else gD.priorityInstead gD.activePlayer
          if gD.continuations.all isCarrierOnlyFrame && gD.outerPendingReplacements.isEmpty &&
              gD.currentInterpWait?.isNone then
            classifyFinishAndGrantPriority gD prio
          else if !gD.outerPendingReplacements.isEmpty || gD.currentInterpWait?.isSome then
            match classifyFinishResolutionChoice (gD.change (.pendingPriority (some prio))) with
            | .implicitResolutionChoice =>
              match livingPriorityInstead? gD prio with
              | some q => .grants (some q)
              | none => .settlesPromptOrOver
            | other => other
          else .noGrant
      else .noGrant
    else if g1.pending != .none || g1.afterRandom != .none then .settlesPromptOrOver
    else if prevPending == .none || !g1.stillInGame p || didAbort then
      let prio := if g1.stillInGame p then g1.priorityInstead p else g1.priorityInstead g1.activePlayer
      if g1.continuations.all isCarrierOnlyFrame then
        classifyFinishAndGrantPriority g1 prio
      else if g1.pendingReplacement.isSome || !g1.outerPendingReplacements.isEmpty ||
          g1.currentInterpWait?.isSome then
        if g1.anyContinuationSettlesControlFlow then
          match g1.firstContinuationPriorityGrant? with
          | some (some q) =>
            match livingPriorityInstead? g1 q with
            | some q' => .grants (some q')
            | none => .settlesPromptOrOver
          | some none =>
            match livingPriorityInstead? g1 prio with
            | some q' => .grants (some q')
            | none => .settlesPromptOrOver
          | none => if g1.anyContinuationGrantsPriority then .grants none else .settlesPromptOrOver
        else
          match classifyFinishResolutionChoice (g1.change (.pendingPriority (some prio))) with
          | .implicitResolutionChoice =>
            match livingPriorityInstead? g1 prio with
            | some q' => .grants (some q')
            | none => .settlesPromptOrOver
          | other => other
      else .noGrant
    else if g1.pendingReplacement.isSome || !g1.outerPendingReplacements.isEmpty then
      match g1.firstContinuationPriorityGrant? with
      | some (some q) => .grants (some q)
      | some none => .implicitResolutionChoice
      | none =>
        if g1.anyContinuationGrantsPriority then .grants none
        else if g1.anyContinuationSettlesControlFlow then .settlesPromptOrOver
        else .noGrant
    else if g.proposedSpell.isSome && g1.proposedSpell.isNone then
      if !g1.continuations.isEmpty || g1.currentInterpWait?.isSome then
        classifyFinishResolutionChoice g1
      else if g1.playersReceivePriority then
        match livingPriorityInstead? g1 g1.priority with
        | some q => .grants (some q)
        | none => .settlesPromptOrOver
      else .settlesPromptOrOver
    else .noGrant

private partial def seqFollowForReversal (g : Game) (hasQueuedPending : Bool)
    (a b : PendingReplacement)
    (followedByFinishChoice : Bool := false)
    (followedByExplicitPriority? : Option PlayerId := none)
    (followedByNonProposalPriorityGrant : Bool := false) :
    ProbeAdvanceResult × Bool × Option PlayerId :=
  let resA0 :=
    advanceProbeOnResumeCore g hasQueuedPending a followedByFinishChoice followedByExplicitPriority?
  if !resA0.reversedProposal then
    (resA0, followedByFinishChoice, followedByExplicitPriority?)
  else
    let gBaseRest := resA0.preReverseGame?.getD g
    let gProbeRest :=
      if gBaseRest.proposedSpell.isSome then gBaseRest.change (.proposedSpell none)
      else gBaseRest
    let (nextFbFc, nextFbEp) :=
      match firstPriorityGrantLeaf? gProbeRest hasQueuedPending b
          followedByFinishChoice followedByExplicitPriority? followedByNonProposalPriorityGrant with
      | some (leaf, explicit?) =>
        if leaf.endsWithFinishResolutionChoice then (true, explicit?)
        else if explicit?.isSome then (false, explicit?)
        else (followedByFinishChoice, followedByExplicitPriority?)
      | none => (followedByFinishChoice || b.endsWithFinishResolutionChoice, followedByExplicitPriority?)
    if nextFbFc == followedByFinishChoice && nextFbEp == followedByExplicitPriority? then
      (resA0, nextFbFc, nextFbEp)
    else
      (advanceProbeOnResumeCore g hasQueuedPending a nextFbFc nextFbEp, nextFbFc, nextFbEp)

private partial def classifyAfterTriggerTargetsChosenFuel (g : Game) : Nat → ConcedePriorityOutcome
  | 0 => .settlesPromptOrOver
  | fuel + 1 =>
    if g.over || g.livingPlayers.isEmpty then .settlesPromptOrOver
    else if g.sbaPaused then .settlesPromptOrOver
    else
      let g :=
        match g.pending with
        | .chooseTargets _ => g.change (.pending .none)
        | _ => g
      if g.pending != .none || g.afterRandom != .none then .settlesPromptOrOver
      else if g.proposedSpell.isNone &&
          (g.pendingMayCastFromExile.isSome || g.pendingFreeCopies.isSome) then
        let g2 := g.reopenDeferredExileCasts
        if g2.over || g2.livingPlayers.isEmpty then .settlesPromptOrOver
        else if let .chooseReplacement .. := g2.pending then
          if g2.anyContinuationSettlesControlFlow then
            match g2.firstContinuationPriorityGrant? with
            | some (some q) => .grants (some q)
            | some none => .implicitResolutionChoice
            | none => if g2.anyContinuationGrantsPriority then .grants none else .settlesPromptOrOver
          else
            let gD := drainProbePausedStep g2
            if gD.over || gD.livingPlayers.isEmpty || gD.pending != .none ||
                gD.afterRandom != .none || gD.pendingReplacement.isSome then
              .settlesPromptOrOver
            else classifyFinishResolutionChoiceFuel gD fuel
        else if g2.pending != .none || g2.afterRandom != .none then .settlesPromptOrOver
        else if g2.currentInterpWait?.isSome ||
            g2.pendingReplacement.isSome || !g2.outerPendingReplacements.isEmpty then
          classifyFinishResolutionChoiceFuel g2 fuel
        else classifyAfterTriggerTargetsChosenFuel g2 fuel
      else
        match g.triggerNeedingTargets with
        | some _ =>
          if (g.promptTriggerTargetsIfNeeded).pending != .none then .settlesPromptOrOver
          else .implicitResolutionChoice
        | none =>
          if g.proposedSpell.any (fun prop =>
              !g.stillInGame prop.caster || (g.findObject? prop.spellId).isNone) then
            match g.proposedSpell with
            | some prop => classifyProposedSpellReversal g prop (alwaysGrantPriority := true)
            | none => .noGrant
          else if g.proposedSpell.isSome then .noGrant
          else
            let prio := g.pendingPriority.getD g.activePlayer
            match receivePriorityOutcome g prio (recheckSba := false) with
            | .grants _ | .implicitResolutionChoice => .implicitResolutionChoice
            | other => other

private partial def classifyResumeTriggerModesAfterLeave (g : Game)
    (step : PostStep) : ConcedePriorityOutcome :=
  if g.over || g.livingPlayers.isEmpty then .settlesPromptOrOver
  else
    match step with
    | .resumeTriggerModesAfterLeave p objectId remaining chosen =>
      if !g.stillInGame p then classifyFinishResolutionChoice g
      else
        match g.findObject? objectId with
        | some obj =>
          if obj.zone != .stack then classifyFinishResolutionChoice g
          else
            let tModes := g.triggerModesOf obj
            let validChosen := chosen.filter (fun i =>
              tModes[i]?.any (g.triggerModeChoosable p obj))
            let needed := remaining + (chosen.size - validChosen.size)
            let choosableLeft :=
              ((List.range tModes.size).filter (fun i =>
                !validChosen.contains i && (tModes[i]?.any (g.triggerModeChoosable p obj)))).length
            if needed == 0 then
              let sorted := validChosen.qsort (· < ·)
              let g1 := g.record (GameEvent.announced g.turnNumber obj.id (modes := sorted))
              let g1 :=
                match combineTriggerModes (tModes.map (fun m => g1.expandEachOpponentEffect p m (some obj.id))) sorted with
                | none => g1
                | some eff =>
                  let g1 := g1.changeObject obj.id (.abilityEffect (some eff))
                  if !eff.requiresTarget then g1.change (.stackEntry obj.id (.targetsAnnounced true)) else g1
              classifyFinishResolutionChoice g1
            else if choosableLeft < needed then
              let g1 := g.ceaseToExist obj.id (cause := some (.gameRule .noLegalMode))
              classifyFinishResolutionChoice g1
            else .settlesPromptOrOver
        | none => classifyFinishResolutionChoice g
    | .resumeUpToTriggerModesAfterLeave p objectId remaining chosen =>
      if !g.stillInGame p then classifyFinishResolutionChoice g
      else
        match g.findObject? objectId with
        | some obj =>
          if obj.zone != .stack then classifyFinishResolutionChoice g
          else
            let modes := g.triggerModesOf obj
            let validChosen := chosen.filter (fun i =>
              modes[i]?.any (g.triggerModeChoosable p obj))
            let remaining := remaining + (chosen.size - validChosen.size)
            let anyChoosableLeft :=
              (List.range modes.size).any (fun i =>
                !validChosen.contains i && (modes[i]?.any (g.triggerModeChoosable p obj)))
            if remaining > 0 && anyChoosableLeft then .settlesPromptOrOver
            else if validChosen.isEmpty then
              let noop : Effect := { body := .noop }
              let g1 := g.record (GameEvent.announced g.turnNumber obj.id (modes := #[]))
              let g1 := g1.changes #[
                .object obj.id (.abilityEffect (some noop)),
                .stackEntry obj.id (.targetsAnnounced true)]
              classifyFinishResolutionChoice g1
            else
              let sorted := validChosen.qsort (· < ·)
              let g1 := g.record (GameEvent.announced g.turnNumber obj.id (modes := sorted))
              let g1 :=
                match combineTriggerModes (modes.map (fun m => g1.expandEachOpponentEffect p m (some obj.id))) sorted with
                | none => g1
                | some eff =>
                  let g1 := g1.changeObject obj.id (.abilityEffect (some eff))
                  if !eff.requiresTarget then g1.change (.stackEntry obj.id (.targetsAnnounced true)) else g1
              classifyFinishResolutionChoice g1
        | none => classifyFinishResolutionChoice g
    | .resumeHawkeyeModesAfterLeave p objectId left chosen =>
      if !g.stillInGame p then classifyFinishResolutionChoice g
      else
        match g.findObject? objectId with
        | some obj =>
          if obj.zone != .stack then classifyFinishResolutionChoice g
          else
            let validChosen := chosen.filter (fun i =>
              hawkeyeModeEffects[i]?.any (g.triggerModeChoosable p obj))
            let anyMoreChoosable :=
              (List.range hawkeyeModeEffects.size).any (fun i =>
                !validChosen.contains i && (hawkeyeModeEffects[i]?.any (g.triggerModeChoosable p obj)))
            if validChosen.size < left && anyMoreChoosable then .settlesPromptOrOver
            else
              let sorted := validChosen.qsort (· < ·)
              let eff : Effect :=
                if sorted.isEmpty then { body := .noop }
                else hawkeyeArrowsEffect sorted
              let g1 := g.record (GameEvent.announced g.turnNumber obj.id (modes := sorted))
              let g1 := g1.changeObject obj.id (.abilityEffect (some eff))
              let g1 := if !eff.requiresTarget then g1.change (.stackEntry obj.id (.targetsAnnounced true)) else g1
              classifyFinishResolutionChoice g1
        | none => classifyFinishResolutionChoice g
    | _ => .noGrant

private partial def classifyResumeChooseModeAfterLeave (g : Game) (p : PlayerId)
    (followedByFinishChoice : Bool := false)
    (followedByExplicitPriority? : Option PlayerId := none) : ConcedePriorityOutcome :=
  if g.over || g.livingPlayers.isEmpty then .settlesPromptOrOver
  else if !g.stillInGame p then
    match g.proposedSpell with
    | some prop =>
      if prop.caster == p then
        classifyProposedSpellReversal g prop followedByFinishChoice followedByExplicitPriority?
          (alwaysGrantPriority := true)
      else .noGrant
    | none => .noGrant
  else
    match g.proposedSpell with
    | none => .noGrant
    | some prop =>
      if prop.caster != p then .noGrant
      else
        match prop.kind with
        | .activatedAbility =>
          if g.sourceStillPayable prop &&
              (g.findObject? prop.spellId).any (·.zone == .stack) &&
              prop.abilityModes.any (fun m => g.modeIsChoosable p m prop.sourceId) then
            .settlesPromptOrOver
          else
            classifyProposedSpellReversal g prop followedByFinishChoice followedByExplicitPriority?
              (alwaysGrantPriority := true)
        | .spell =>
          match g.findObject? prop.spellId with
          | none =>
            classifyProposedSpellReversal g prop followedByFinishChoice followedByExplicitPriority?
              (alwaysGrantPriority := true)
          | some spell =>
            if spell.zone != .stack || !g.sourceStillPayable prop then
              classifyProposedSpellReversal g prop followedByFinishChoice followedByExplicitPriority?
                (alwaysGrantPriority := true)
            else
              let face := g.baseCard spell
              let effModes := g.evalSpellModes p spell
              let chosen := g.chosenModesOf spell
              let validChosen := chosen.filter (fun i =>
                effModes[i]?.any (fun m => g.spellModeIsChoosable p m (some spell.id)))
              let more := (List.range effModes.size).any (fun i =>
                !validChosen.contains i && g.spellModeIsChoosable p effModes[i]! (some spell.id))
              if validChosen.size < g.maxModesFor p face && more then
                .settlesPromptOrOver
              else if !validChosen.isEmpty then
                let g1 :=
                  if validChosen == chosen then g
                  else g.record (GameEvent.announced g.turnNumber spell.id (modes := validChosen))
                let g2 := g1.afterModesChosen p
                if g2.over || g2.livingPlayers.isEmpty then .settlesPromptOrOver
                else if let .chooseReplacement .. := g2.pending then
                  if pausedPromptSettles g2 false g2.pending then .settlesPromptOrOver else .noGrant
                else if g2.pending != .none || g2.afterRandom != .none then .settlesPromptOrOver
                else if g2.proposedSpell.isNone && g.proposalCheckpoint.isSome then
                  classifyProposedSpellReversal g prop followedByFinishChoice followedByExplicitPriority?
                    (alwaysGrantPriority := true)
                else .noGrant
              else if isReturnUpToTwoGyModal face || face.allowsZeroTargets then
                .settlesPromptOrOver
              else
                classifyProposedSpellReversal g prop followedByFinishChoice followedByExplicitPriority?
                  (alwaysGrantPriority := true)
        | .turnFaceUp =>
          if g.sourceStillPayable prop && (g.findObject? prop.spellId).any (·.isOnBattlefield) then .noGrant
          else
            classifyProposedSpellReversal g prop followedByFinishChoice followedByExplicitPriority?
              (alwaysGrantPriority := true)

private partial def classifyResumeChooseTargetsAfterLeave (g : Game) (p : PlayerId)
    (followedByFinishChoice : Bool := false)
    (followedByExplicitPriority? : Option PlayerId := none) : ConcedePriorityOutcome :=
  let ownPropNeedsReverse :=
    g.proposedSpell.any (fun prop =>
      prop.caster == p &&
        (!g.stillInGame p || (g.findObject? prop.spellId).isNone || !g.sourceStillPayable prop))
  if ownPropNeedsReverse then
    match g.proposedSpell with
    | some prop =>
      let gPre := if g.pending == .none then g else g.change (.pending .none)
      classifyProposedSpellReversal gPre prop followedByFinishChoice followedByExplicitPriority?
        (alwaysGrantPriority := true)
    | none => .noGrant
  else if g.over || g.livingPlayers.isEmpty then .settlesPromptOrOver
  else
    match g.objectAwaitingTargets with
    | none => classifyAfterTriggerTargetsChosenFuel g 8
    | some obj =>
      let isPropSpell := g.proposedSpell.any (·.spellId == obj.id)
      let caster :=
        match g.proposedSpell with
        | some prop =>
          if prop.spellId == obj.id then prop.caster
          else (g.stack.find? (·.objectId == obj.id)).map (·.controller) |>.getD p
        | none =>
          (g.stack.find? (·.objectId == obj.id)).map (·.controller) |>.getD p
      if !g.stillInGame caster then
        if isPropSpell then
          match g.proposedSpell with
          | some prop =>
            classifyProposedSpellReversal g prop followedByFinishChoice followedByExplicitPriority?
              (alwaysGrantPriority := true)
          | none => .noGrant
        else
          classifyAfterTriggerTargetsChosenFuel
            (g.ceaseToExist obj.id (cause := some (.gameRule .triggeredAbility))) 8
      else
        let hasLegal := !(g.legalProposedTargets caster obj).isEmpty
        let allowZero :=
          (g.targetSpecOf obj).allowsZero ||
          match obj.triggeredAbility with
          | some ab => ab.allowsZeroTargets || obj.abilityEffect.any (·.allowsZeroTargets)
          | none =>
            match g.currentSpellEffect obj with
            | some e => e.allowsZeroTargets
            | none => obj.abilityEffect.any (·.allowsZeroTargets)
        let canDeclineOrPick :=
          hasLegal || g.canSkipCurrentOptionalSlot obj || g.canFinishOptionalTargets obj || allowZero
        if canDeclineOrPick then .settlesPromptOrOver
        else if isPropSpell then
          match g.proposedSpell with
          | some prop =>
            classifyProposedSpellReversal g prop followedByFinishChoice followedByExplicitPriority?
              (alwaysGrantPriority := true)
          | none => .noGrant
        else
          classifyAfterTriggerTargetsChosenFuel
            (g.ceaseToExist obj.id (cause := some (.gameRule .triggeredAbility))) 8

private partial def classifyResumeProposalCostAfterLeave (g : Game) (p : PlayerId)
    (savedP : Pending)
    (followedByFinishChoice : Bool := false)
    (followedByExplicitPriority? : Option PlayerId := none) : ConcedePriorityOutcome :=
  if g.proposalCostPromptStillPayable p savedP then .settlesPromptOrOver
  else if g.proposedSpell.any (·.caster == p) then
    match g.proposedSpell with
    | some prop =>
      classifyProposedSpellReversal g prop followedByFinishChoice followedByExplicitPriority?
        (alwaysGrantPriority := true)
    | none => .noGrant
  else if g.over || g.livingPlayers.isEmpty then .settlesPromptOrOver
  else .noGrant

private partial def classifyPayCostPickItems (g : Game) (p : PlayerId)
    (abilityId sourceId : Option ObjectId) (pick : CostPick) (remainingIds : Array ObjectId)
    (followedByFinishChoice : Bool := false)
    (followedByExplicitPriority? : Option PlayerId := none) : ConcedePriorityOutcome :=
  if g.over || g.livingPlayers.isEmpty then .settlesPromptOrOver
  else if let .chooseReplacement .. := g.pending then .noGrant
  else
    let (g1, ok) := g.payCostPickItemsChecked p abilityId sourceId pick remainingIds
      (followedByFinishChoice := followedByFinishChoice)
      (followedByExplicitPriority? := followedByExplicitPriority?)
    if !ok then
      if !g.hasActiveManaProposalCheckpoint && g.currentBatch.isNone then
        match g.proposedSpell with
        | some prop =>
          classifyProposedSpellReversal g prop followedByFinishChoice followedByExplicitPriority?
        | none => .noGrant
      else .noGrant
    else if g1.over || g1.livingPlayers.isEmpty then .settlesPromptOrOver
    else if let .chooseReplacement .. := g1.pending then
      if g1.anyContinuationSettlesControlFlow then
        match g1.firstContinuationPriorityGrant? with
        | some (some q) => .grants (some q)
        | some none => .implicitResolutionChoice
        | none => if g1.anyContinuationGrantsPriority then .grants none else .settlesPromptOrOver
      else .noGrant
    else if g1.pending != .none || g1.afterRandom != .none then .settlesPromptOrOver
    else .noGrant

private partial def classifyFinishActivationExtraCosts (g : Game) (p : PlayerId)
    (sourceId : ObjectId) (forObject : Option ObjectId)
    (sacrificeSource exileSource : Bool) (stage : ActivationExtraCostStage) (sinceIdx : Nat)
    (followedByFinishChoice : Bool := false)
    (followedByExplicitPriority? : Option PlayerId := none) : ConcedePriorityOutcome :=
  if g.over || g.livingPlayers.isEmpty then .settlesPromptOrOver
  else if let .chooseReplacement .. := g.pending then .noGrant
  else
    let g1 := g.finishActivationExtraCosts p sourceId forObject sacrificeSource exileSource stage
      (sinceIdx := sinceIdx)
      (followedByFinishChoice := followedByFinishChoice)
      (followedByExplicitPriority? := followedByExplicitPriority?)
    if !g.hasActiveManaProposalCheckpoint && g.proposedSpell.isSome && g1.proposedSpell.isNone then
      match g.proposedSpell with
      | some prop =>
        classifyProposedSpellReversal g prop followedByFinishChoice followedByExplicitPriority?
      | none => .noGrant
    else if g1.over || g1.livingPlayers.isEmpty then .settlesPromptOrOver
    else if let .chooseReplacement .. := g1.pending then
      if g1.anyContinuationSettlesControlFlow then
        match g1.firstContinuationPriorityGrant? with
        | some (some q) => .grants (some q)
        | some none => .implicitResolutionChoice
        | none => if g1.anyContinuationGrantsPriority then .grants none else .settlesPromptOrOver
      else .noGrant
    else if g1.pending != .none || g1.afterRandom != .none then .settlesPromptOrOver
    else .noGrant

/-- `Game`-aware check whether a `PendingReplacement` continuation ends by granting priority. -/
partial def continuationGrantsPriority (g : Game) (hasQueuedPending : Bool := false)
    (pr : PendingReplacement)
    (followedByFinishChoice : Bool := false)
    (followedByExplicitPriority? : Option PlayerId := none)
    (followedByNonProposalPriorityGrant : Bool := false) : Bool :=
  match pr with
  | .seq a b =>
    let (resA, nextFbFc, nextFbEp) :=
      seqFollowForReversal g hasQueuedPending a b
        followedByFinishChoice followedByExplicitPriority? followedByNonProposalPriorityGrant
    let openedNewPrompt :=
      (g.pending == .none && resA.game.pending != .none) ||
      (g.afterRandom == .none && resA.game.afterRandom != .none)
    let stoppedByPrompt :=
      resA.game.pending != .none || (g.afterRandom == .none && resA.game.afterRandom != .none)
    let bGrantLeaf? :=
      if !resA.reversedProposal && !(!g.over && resA.game.over && !b.hasCheckpointReplay) &&
          !openedNewPrompt && !stoppedByPrompt then
        firstPriorityGrantLeaf? resA.game resA.hasQueuedPending b
          followedByFinishChoice followedByExplicitPriority? followedByNonProposalPriorityGrant
      else none
    let nextFbFcForA : Bool :=
      match bGrantLeaf? with
      | some (leaf, explicit?) =>
        if leaf.endsWithFinishResolutionChoice then true
        else if explicit?.isSome then false
        else followedByFinishChoice
      | none => followedByFinishChoice || b.endsWithFinishResolutionChoice
    let nextFbEpForA : Option PlayerId :=
      match bGrantLeaf? with
      | some (leaf, explicit?) =>
        if leaf.endsWithFinishResolutionChoice then explicit?
        else if explicit?.isSome then explicit?
        else followedByExplicitPriority?
      | none => followedByExplicitPriority?
    let nextFbNonProp : Bool :=
      followedByNonProposalPriorityGrant || b.endsWithNonProposalPriorityGrant ||
        bGrantLeaf?.any (fun (leaf, _) => isNonProposalGrantLeaf leaf)
    let suppressesPostCastFinish : Bool :=
      match a with
      | .finishPostCast _ false false _ =>
        nextFbFcForA || nextFbNonProp || nextFbEpForA.isSome
      | _ => false
    let skipStandaloneA : Bool :=
      (isManaAbilityContinuation a && !b.isPurePostLog) || suppressesPostCastFinish
    if resA.reversedProposal then
      continuationGrantsPriority g hasQueuedPending a
        nextFbFc nextFbEp followedByNonProposalPriorityGrant
    else if !skipStandaloneA && !b.hasCheckpointReplay &&
        continuationGrantsPriority g hasQueuedPending a
          nextFbFcForA nextFbEpForA nextFbNonProp then
      true
    else if !g.over && resA.game.over && !b.hasCheckpointReplay then
      false
    else if openedNewPrompt then
      if let .chooseReplacement .. := resA.game.pending then
        (resA.game.chainPendingReplacement b).anyContinuationGrantsPriority
      else false
    else if stoppedByPrompt then
      false
    else if !skipStandaloneA && !b.hasCheckpointReplay &&
        continuationSettlesControlFlow g false a
          nextFbFcForA nextFbEpForA nextFbNonProp then
      false
    else
      continuationGrantsPriority resA.game resA.hasQueuedPending b
        followedByFinishChoice followedByExplicitPriority? followedByNonProposalPriorityGrant
  | .receivePriority p =>
    match classifyFinishAndGrantPriority g p with
    | .implicitResolutionChoice | .grants _ => true
    | _ => false
  | .finishResolutionChoice => finishResolutionChoiceGrantsPriority g
  | .afterWardResolved =>
    match classifyAfterWardResolved g with
    | .implicitResolutionChoice | .grants _ => true
    | _ => false
  | .finishPostCast caster grantPriority hadOuter openCont =>
    if hadOuter || g.over || g.livingPlayers.isEmpty then false
    else
      let delegateFc := !grantPriority && !followedByFinishChoice &&
        followedByExplicitPriority?.isNone && !followedByNonProposalPriorityGrant
      match finishPostCastOutcome g caster openCont grantPriority none
          (delegateFinishChoice := delegateFc) with
      | .implicitResolutionChoice | .grants _ => true
      | _ => false
  | .finishBecomeCast caster spellId grantPriority hadOuter openCont =>
    match classifyFinishBecomeCast g caster spellId grantPriority hadOuter openCont
        followedByFinishChoice followedByExplicitPriority? with
    | .implicitResolutionChoice | .grants _ => true
    | _ => false
  | .finishProposedSpellCosts stage grantPriority hadOuter openCont =>
    if g.over || g.livingPlayers.isEmpty then false
    else
      match classifyFinishProposedSpellCosts g stage grantPriority hadOuter openCont
          followedByFinishChoice followedByExplicitPriority? with
      | .implicitResolutionChoice | .grants _ => true
      | _ => false
  | .completeActivation hadOuter openCont =>
    match classifyCompleteActivation g hadOuter openCont
        followedByFinishChoice followedByExplicitPriority? with
    | .implicitResolutionChoice | .grants _ => true
    | _ => hadOuter && hasQueuedPending
  | .finishBecomeActivated caster srcName srcId act abId srcSnap srcOrig hadOuter openCont =>
    match classifyFinishBecomeActivated g caster srcName srcId act abId srcSnap srcOrig hadOuter openCont
        followedByFinishChoice followedByExplicitPriority? with
    | .implicitResolutionChoice | .grants _ => true
    | _ => hadOuter && hasQueuedPending
  | .finishPostLoyaltyActivated caster _ srcId _ abId _ _ hadOuter openCont =>
    match classifyFinishPostLoyaltyActivated g caster srcId abId hadOuter openCont
        followedByFinishChoice followedByExplicitPriority? with
    | .implicitResolutionChoice | .grants _ => true
    | _ => hadOuter && hasQueuedPending
  | .finishTurnFaceUp caster spellId hadOuter =>
    if hadOuter then
      hasQueuedPending ||
        match probeCompleteTurnFaceUpOutcome g caster spellId true
            followedByFinishChoice followedByExplicitPriority? with
        | .implicitResolutionChoice | .grants _ => true
        | _ => false
    else
      match probeCompleteTurnFaceUpOutcome g caster spellId false
          followedByFinishChoice followedByExplicitPriority? with
      | .implicitResolutionChoice | .grants _ => true
      | _ => false
  | .finishPostStep (.resumeChooseModeAfterLeave p) =>
    match classifyResumeChooseModeAfterLeave g p
        followedByFinishChoice followedByExplicitPriority? with
    | .implicitResolutionChoice | .grants _ => true
    | _ => false
  | .finishPostStep (.resumeChooseTargetsAfterLeave p) =>
    match classifyResumeChooseTargetsAfterLeave g p
        followedByFinishChoice followedByExplicitPriority? with
    | .implicitResolutionChoice | .grants _ => true
    | _ => false
  | .finishPostStep .afterTriggerTargetsChosen =>
    match classifyAfterTriggerTargetsChosenFuel g 16 with
    | .implicitResolutionChoice | .grants _ => true
    | _ => false
  | .finishPostStep step@(.resumeTriggerModesAfterLeave ..)
  | .finishPostStep step@(.resumeUpToTriggerModesAfterLeave ..)
  | .finishPostStep step@(.resumeHawkeyeModesAfterLeave ..) =>
    match classifyResumeTriggerModesAfterLeave g step with
    | .implicitResolutionChoice | .grants _ => true
    | _ => false
  | .finishPostStep (.resumeProposalCostAfterLeave p savedP) =>
    match classifyResumeProposalCostAfterLeave g p savedP
        followedByFinishChoice followedByExplicitPriority? with
    | .implicitResolutionChoice | .grants _ => true
    | _ => false
  | .payCostPickItems p abilityId sourceId pick remainingIds =>
    match classifyPayCostPickItems g p abilityId sourceId pick remainingIds
        followedByFinishChoice followedByExplicitPriority? with
    | .implicitResolutionChoice | .grants _ => true
    | _ => false
  | .finishActivationExtraCosts p sourceId forObject sacrificeSource exileSource stage sinceIdx =>
    match classifyFinishActivationExtraCosts g p sourceId forObject sacrificeSource exileSource stage sinceIdx
        followedByFinishChoice followedByExplicitPriority? with
    | .implicitResolutionChoice | .grants _ => true
    | _ => false
  | pr@(.finishActivateManaAbilityPicks p _ _ _ _ _ _ _ _ _ _ _ prevPending ..)
  | pr@(.finishActivateManaAbilityPostSac p _ _ _ _ _ _ _ _ _ prevPending ..) =>
    match classifyManaAbilityPostStep g p prevPending pr with
    | .implicitResolutionChoice | .grants _ => true
    | _ => false
  | .finishConcede wasIdlePriority savedPendingPrio wasAssigningCombatDamage savedPending popOuter departed rewindProposal _ =>
    match classifyFinishConcedePriority g wasIdlePriority savedPendingPrio
        wasAssigningCombatDamage savedPending popOuter (runSba := true)
        (departed := departed) (rewindProposal := rewindProposal) with
    | .implicitResolutionChoice | .grants _ => true
    | _ => false
  | .concedePlayersLoop remaining wp mid wasIdlePriority savedPendingPrio wasAssigningCombatDamage savedPending popOuter departed rewindProposal _ =>
    !wp &&
      match classifyConcedePlayersLoop g remaining wasIdlePriority savedPendingPrio
          wasAssigningCombatDamage savedPending popOuter
          (departedIn := departed) (rewindProposalIn := rewindProposal)
          (midResolutionOrBatch := mid) with
      | .implicitResolutionChoice | .grants _ => true
      | _ => false
  | .continueStartNextTurn nextP remainingDeparted runBeginTurn alreadyExpired =>
    (continueStartNextTurnRecipient? (drainProbePausedStep g) nextP remainingDeparted runBeginTurn alreadyExpired).isSome
  | .beginTurnAfterStartExpiry =>
    (beginTurnAfterStartExpiryRecipient? g).isSome
  | .finishPostStep .startNextTurnAndBegin =>
    (startNextTurnAndBeginRecipient? (drainProbePausedStep g)).isSome
  | .finishPostStep .endTurnAfterCleanupStepEnded =>
    (endTurnAfterCleanupStepEndedRecipient? (drainProbePausedStep g)).isSome
  | .finishPostStep (.postSbaCleanup sba) =>
    (postSbaCleanupRecipient? (drainProbePausedStep g) sba).isSome
  | .finishCleanupAfterClearEot =>
    (finishCleanupAfterClearEotRecipient? (drainProbePausedStep g)).isSome
  | .finishPostStep .cleanupStepAfterDiscard =>
    (cleanupStepAfterDiscardRecipient? (drainProbePausedStep g)).isSome
  | .beginStepCont st =>
    if st == .untap then hasQueuedPending
    else (beginStepContRecipient? (drainProbePausedStep g) st).isSome
  | .finishPostStep (.beginStepBody st) =>
    if st == .untap then hasQueuedPending
    else (stepPriorityRecipient? (drainProbePausedStep g) st).isSome
  | .finishPostStep (.beginStepAfterPhaseBegan st) =>
    if st == .untap then hasQueuedPending
    else (beginStepAfterPhaseBeganRecipient? (drainProbePausedStep g) st).isSome
  | .finishPostStep .advanceAfterStepEnded =>
    let gR := drainProbePausedStep g
    if gR.step == .endOfCombat && gR.additionalCombatPhases > 0 then
      (advanceAfterStepEndedRecipient? gR).isSome
    else
      match gR.step.next? with
      | none => false
      | some .untap => hasQueuedPending
      | some _ => (advanceAfterStepEndedRecipient? gR).isSome
  | pr@(.restorePending ..) =>
    match nonPausingRestorePoppedOuter? g hasQueuedPending pr
        followedByFinishChoice followedByExplicitPriority? with
    | some (g', q', nextPr) =>
      continuationGrantsPriority g' q' nextPr
        followedByFinishChoice followedByExplicitPriority? followedByNonProposalPriorityGrant
    | none => pr.endsWithPriorityGrant hasQueuedPending
  | .leavePlayersWhoLost savedPending popOuter departed rewindProposal fromEventIdx? =>
    match probeLeavePlayersWhoLost g hasQueuedPending savedPending popOuter departed rewindProposal fromEventIdx? with
    | .delegate g' q' nextPr =>
      continuationGrantsPriority g' q' nextPr
        followedByFinishChoice followedByExplicitPriority? followedByNonProposalPriorityGrant
    | .paused _ _ _ => false
  | pr => pr.endsWithPriorityGrant hasQueuedPending

/-- `Game`-aware check whether resuming `pr` deterministically settles control flow —
either by granting priority (`continuationGrantsPriority`), opening a self-settling
blocking prompt (`Pending != .none` / `afterRandom != .none`), or ending the game (`g.over`)
(CR 117.3 / 508.1 / 509.1 / 510.1 / 616.1 / 800.4). -/
partial def continuationSettlesControlFlow (g : Game) (hasQueuedPending : Bool := false)
    (pr : PendingReplacement)
    (followedByFinishChoice : Bool := false)
    (followedByExplicitPriority? : Option PlayerId := none)
    (followedByNonProposalPriorityGrant : Bool := false) : Bool :=
  match pr with
  | .seq a b =>
    let (resA, nextFbFc, nextFbEp) :=
      seqFollowForReversal g hasQueuedPending a b
        followedByFinishChoice followedByExplicitPriority? followedByNonProposalPriorityGrant
    let openedNewPrompt :=
      (g.pending == .none && resA.game.pending != .none) ||
      (g.afterRandom == .none && resA.game.afterRandom != .none)
    let stoppedByPrompt :=
      resA.game.pending != .none || (g.afterRandom == .none && resA.game.afterRandom != .none)
    let bGrantLeaf? :=
      if !resA.reversedProposal && !(!g.over && resA.game.over && !b.hasCheckpointReplay) &&
          !openedNewPrompt && !stoppedByPrompt then
        firstPriorityGrantLeaf? resA.game resA.hasQueuedPending b
          followedByFinishChoice followedByExplicitPriority? followedByNonProposalPriorityGrant
      else none
    let nextFbFcForA : Bool :=
      match bGrantLeaf? with
      | some (leaf, explicit?) =>
        if leaf.endsWithFinishResolutionChoice then true
        else if explicit?.isSome then false
        else followedByFinishChoice
      | none => followedByFinishChoice || b.endsWithFinishResolutionChoice
    let nextFbEpForA : Option PlayerId :=
      match bGrantLeaf? with
      | some (leaf, explicit?) =>
        if leaf.endsWithFinishResolutionChoice then explicit?
        else if explicit?.isSome then explicit?
        else followedByExplicitPriority?
      | none => followedByExplicitPriority?
    let nextFbNonProp : Bool :=
      followedByNonProposalPriorityGrant || b.endsWithNonProposalPriorityGrant ||
        bGrantLeaf?.any (fun (leaf, _) => isNonProposalGrantLeaf leaf)
    if resA.reversedProposal then
      continuationSettlesControlFlow g hasQueuedPending a
        nextFbFc nextFbEp followedByNonProposalPriorityGrant
    else if !g.over && resA.game.over && !b.hasCheckpointReplay then
      true
    else if openedNewPrompt then
      if let .chooseReplacement .. := resA.game.pending then
        pausedPromptSettles (resA.game.chainPendingReplacement b) resA.hasQueuedPending resA.game.pending
      else true
    else if resA.game.pending != .none then
      continuationSettlesControlFlow g hasQueuedPending a
        nextFbFcForA nextFbEpForA nextFbNonProp
    else if continuationSettlesControlFlow resA.game resA.hasQueuedPending b
        followedByFinishChoice followedByExplicitPriority? followedByNonProposalPriorityGrant then true
    else
      let suppressesPostCastFinish : Bool :=
        match a with
        | .finishPostCast _ false false _ =>
          nextFbFcForA || nextFbNonProp || nextFbEpForA.isSome
        | _ => false
      !(isManaAbilityContinuation a && !b.isPurePostLog) && !suppressesPostCastFinish &&
        !b.hasCheckpointReplay &&
        continuationSettlesControlFlow g hasQueuedPending a
          nextFbFcForA nextFbEpForA nextFbNonProp
  | pr@(.restorePending ..) =>
    match probeRestorePendingCore g hasQueuedPending pr
        followedByFinishChoice followedByExplicitPriority? with
    | .paused _ _ settles => settles
    | .delegate g' q' nextPr =>
      continuationSettlesControlFlow g' q' nextPr
        followedByFinishChoice followedByExplicitPriority? followedByNonProposalPriorityGrant
  | .leavePlayersWhoLost savedPending popOuter departed rewindProposal fromEventIdx? =>
    match probeLeavePlayersWhoLost g hasQueuedPending savedPending popOuter departed rewindProposal fromEventIdx? with
    | .paused _ _ settles => settles
    | .delegate g' q' nextPr =>
      continuationSettlesControlFlow g' q' nextPr
        followedByFinishChoice followedByExplicitPriority? followedByNonProposalPriorityGrant
  | pr =>
    if g.over || continuationGrantsPriority g hasQueuedPending pr
        followedByFinishChoice followedByExplicitPriority? followedByNonProposalPriorityGrant then true
    else
      match pr with
      | .receivePriority p =>
        !g.livingPlayers.isEmpty && classifyFinishAndGrantPriority g p != .noGrant
      | .finishResolutionChoice =>
        !g.livingPlayers.isEmpty && classifyFinishResolutionChoice g != .noGrant
      | .afterWardResolved =>
        !g.livingPlayers.isEmpty && classifyAfterWardResolved g != .noGrant
      | .beginStepCont st
      | .finishPostStep (.beginStepBody st)
      | .finishPostStep (.beginStepAfterPhaseBegan st) =>
        st != .untap && !g.livingPlayers.isEmpty
      | .finishPostStep .advanceAfterStepEnded =>
        let gR := drainProbePausedStep g
        if gR.over then true
        else if gR.step == .endOfCombat && gR.additionalCombatPhases > 0 then
          !gR.livingPlayers.isEmpty
        else
          match gR.step.next? with
          | some st => st != .untap && !gR.livingPlayers.isEmpty
          | none => false
      | .continueStartNextTurn _ _ runBeginTurn _ =>
        let gR := drainProbePausedStep g
        gR.over || (runBeginTurn && !gR.livingPlayers.isEmpty)
      | .beginTurnAfterStartExpiry
      | .finishPostStep .startNextTurnAndBegin
      | .finishPostStep .endTurnAfterCleanupStepEnded
      | .finishPostStep (.postSbaCleanup _)
      | .finishCleanupAfterClearEot
      | .finishPostStep .cleanupStepAfterDiscard =>
        let gR := drainProbePausedStep g
        gR.over || !gR.livingPlayers.isEmpty
      | .finishConcede wasIdlePriority savedPendingPrio wasAssigningCombatDamage savedPending popOuter departed rewindProposal _ =>
        classifyFinishConcedePriority g wasIdlePriority savedPendingPrio
          wasAssigningCombatDamage savedPending popOuter (runSba := true)
          (departed := departed) (rewindProposal := rewindProposal) != .noGrant
      | .concedePlayersLoop remaining wp mid wasIdlePriority savedPendingPrio wasAssigningCombatDamage savedPending popOuter departed rewindProposal _ =>
        if wp then true
        else
          classifyConcedePlayersLoop g remaining wasIdlePriority savedPendingPrio
            wasAssigningCombatDamage savedPending popOuter
            (departedIn := departed) (rewindProposalIn := rewindProposal)
            (midResolutionOrBatch := mid) != .noGrant
      | .finishPostCast caster grantPriority hadOuter openCont =>
        let delegateFc := !grantPriority && !hadOuter && !followedByFinishChoice &&
          followedByExplicitPriority?.isNone && !followedByNonProposalPriorityGrant
        let out :=
          finishPostCastOutcome g caster openCont (grantPriority && !hadOuter) none
            (delegateFinishChoice := delegateFc)
        out != .noGrant || (hadOuter && hasQueuedPending)
      | .finishBecomeCast caster spellId grantPriority hadOuter openCont =>
        classifyFinishBecomeCast g caster spellId grantPriority hadOuter openCont
            followedByFinishChoice followedByExplicitPriority? != .noGrant ||
          (hadOuter && hasQueuedPending)
      | .finishProposedSpellCosts stage grantPriority hadOuter openCont =>
        classifyFinishProposedSpellCosts g stage grantPriority hadOuter openCont
            followedByFinishChoice followedByExplicitPriority? != .noGrant ||
          (hadOuter && hasQueuedPending)
      | .completeActivation hadOuter openCont =>
        classifyCompleteActivation g hadOuter openCont
            followedByFinishChoice followedByExplicitPriority? != .noGrant ||
          (hadOuter && hasQueuedPending)
      | .finishBecomeActivated caster srcName srcId act abId srcSnap srcOrig hadOuter openCont =>
        classifyFinishBecomeActivated g caster srcName srcId act abId srcSnap srcOrig hadOuter openCont
            followedByFinishChoice followedByExplicitPriority? != .noGrant ||
          (hadOuter && hasQueuedPending)
      | .finishPostLoyaltyActivated caster _ srcId _ abId _ _ hadOuter openCont =>
        classifyFinishPostLoyaltyActivated g caster srcId abId hadOuter openCont
            followedByFinishChoice followedByExplicitPriority? != .noGrant ||
          (hadOuter && hasQueuedPending)
      | .finishTurnFaceUp caster spellId hadOuter =>
        probeCompleteTurnFaceUpOutcome g caster spellId hadOuter
            followedByFinishChoice followedByExplicitPriority? != .noGrant ||
          (hadOuter && hasQueuedPending)
      | .finishPostStep (.resumeChooseModeAfterLeave p) =>
        classifyResumeChooseModeAfterLeave g p
          followedByFinishChoice followedByExplicitPriority? != .noGrant
      | .finishPostStep (.resumeChooseTargetsAfterLeave p) =>
        classifyResumeChooseTargetsAfterLeave g p
          followedByFinishChoice followedByExplicitPriority? != .noGrant
      | .finishPostStep .afterTriggerTargetsChosen =>
        classifyAfterTriggerTargetsChosenFuel g 16 != .noGrant
      | .finishPostStep step@(.resumeTriggerModesAfterLeave ..)
      | .finishPostStep step@(.resumeUpToTriggerModesAfterLeave ..)
      | .finishPostStep step@(.resumeHawkeyeModesAfterLeave ..) =>
        classifyResumeTriggerModesAfterLeave g step != .noGrant
      | .finishPostStep (.resumeProposalCostAfterLeave p savedP) =>
        classifyResumeProposalCostAfterLeave g p savedP
          followedByFinishChoice followedByExplicitPriority? != .noGrant
      | .payCostPickItems p abilityId sourceId pick remainingIds =>
        classifyPayCostPickItems g p abilityId sourceId pick remainingIds
          followedByFinishChoice followedByExplicitPriority? != .noGrant
      | .finishActivationExtraCosts p sourceId forObject sacrificeSource exileSource stage sinceIdx =>
        classifyFinishActivationExtraCosts g p sourceId forObject sacrificeSource exileSource stage sinceIdx
          followedByFinishChoice followedByExplicitPriority? != .noGrant
      | .finishActivateManaAbilityPicks p _ _ _ _ _ _ _ _ _ _ _ prevPending ..
      | .finishActivateManaAbilityPostSac p _ _ _ _ _ _ _ _ _ prevPending .. =>
        classifyManaAbilityPostStep g p prevPending pr != .noGrant
      | pr@(.dealDamageToPlayer ..)
      | pr@(.runModalManaEffect ..)
      | pr@(.finishManaAbilityMountainTrigger ..) =>
        let g1 := drainProbeNonPriorityCont g pr
        g1.over || isSelfSettlingPending g1.pending || g1.afterRandom != .none ||
          (match g1.pending with
           | .chooseReplacement .. => pausedPromptSettles g1 hasQueuedPending g1.pending
           | _ => false) ||
          g1.pendingReplacement.any (fun nextPr =>
            continuationSettlesControlFlow (probeGameForPendingReplacement g1) hasQueuedPending nextPr)
      | .finishPostStep (.logInfluenceThenScryTwo sourceId _) =>
        (g.findObject? sourceId).any fun src =>
          src.isOnBattlefield && g.stillInGame (g.you src) && !(g.player (g.you src)).library.isEmpty
      | .finishDrawThenBeginDiscard p discardRounds =>
        !g.over && (discardRounds > 0 || g.thirstDiscardsLeft > 0) &&
          g.stillInGame p && !(g.discardableHandIds p).isEmpty
      | .finishBeginRecruit p =>
        !g.over && g.stillInGame p && !(g.discardableHandIds p).isEmpty
      | .shuffleThen p onDone =>
        if g.over then false
        else
          let g1 := g.shuffleThen p onDone
          g1.over || g1.pending != .none || g1.afterRandom != .none
      | _ => false

/-- Explicit priority recipient encoded by a priority-granting pending
replacement leaf (e.g. `.finishPostCast` for a non-active caster, CR 117.3c). -/
partial def priorityRecipientOfContinuation? (g : Game) (hasQueuedPending : Bool := false)
    (pr : PendingReplacement)
    (followedByFinishChoice : Bool := false)
    (followedByExplicitPriority? : Option PlayerId := none)
    (followedByNonProposalPriorityGrant : Bool := false) : Option PlayerId :=
  match pr with
  | .seq a b =>
    let (resA, nextFbFc, nextFbEp) :=
      seqFollowForReversal g hasQueuedPending a b
        followedByFinishChoice followedByExplicitPriority? followedByNonProposalPriorityGrant
    let openedNewPrompt :=
      (g.pending == .none && resA.game.pending != .none) ||
      (g.afterRandom == .none && resA.game.afterRandom != .none)
    let stoppedByPrompt :=
      resA.game.pending != .none || (g.afterRandom == .none && resA.game.afterRandom != .none)
    let bGrantLeaf? :=
      if !resA.reversedProposal && !(!g.over && resA.game.over && !b.hasCheckpointReplay) &&
          !openedNewPrompt && !stoppedByPrompt then
        firstPriorityGrantLeaf? resA.game resA.hasQueuedPending b
          followedByFinishChoice followedByExplicitPriority? followedByNonProposalPriorityGrant
      else none
    let nextFbFcForA : Bool :=
      match bGrantLeaf? with
      | some (leaf, explicit?) =>
        if leaf.endsWithFinishResolutionChoice then true
        else if explicit?.isSome then false
        else followedByFinishChoice
      | none => followedByFinishChoice || b.endsWithFinishResolutionChoice
    let nextFbEpForA : Option PlayerId :=
      match bGrantLeaf? with
      | some (leaf, explicit?) =>
        if leaf.endsWithFinishResolutionChoice then explicit?
        else if explicit?.isSome then explicit?
        else followedByExplicitPriority?
      | none => followedByExplicitPriority?
    let nextFbNonProp : Bool :=
      followedByNonProposalPriorityGrant || b.endsWithNonProposalPriorityGrant ||
        bGrantLeaf?.any (fun (leaf, _) => isNonProposalGrantLeaf leaf)
    let suppressesPostCastFinish : Bool :=
      match a with
      | .finishPostCast _ false false _ =>
        nextFbFcForA || nextFbNonProp || nextFbEpForA.isSome
      | _ => false
    let skipStandaloneA : Bool :=
      (isManaAbilityContinuation a && !b.isPurePostLog) || suppressesPostCastFinish
    let probeOpenedRep : Option PlayerId :=
      if let .chooseReplacement .. := resA.game.pending then
        match (resA.game.chainPendingReplacement b).firstContinuationPriorityGrant? with
        | some (some q) => some q
        | _ => none
      else none
    if resA.reversedProposal then
      priorityRecipientOfContinuation? g hasQueuedPending a
        nextFbFc nextFbEp followedByNonProposalPriorityGrant
    else if !skipStandaloneA && !b.hasCheckpointReplay then
      match priorityRecipientOfContinuation? g hasQueuedPending a
          nextFbFcForA nextFbEpForA nextFbNonProp with
      | some q => some q
      | none =>
        if (firstPriorityGrantLeaf? g hasQueuedPending a
            nextFbFcForA nextFbEpForA nextFbNonProp).isSome ||
            (!g.over && resA.game.over && !b.hasCheckpointReplay) then none
        else if openedNewPrompt then probeOpenedRep
        else if stoppedByPrompt then none
        else if continuationSettlesControlFlow g false a
            nextFbFcForA nextFbEpForA nextFbNonProp then none
        else priorityRecipientOfContinuation? resA.game resA.hasQueuedPending b
          followedByFinishChoice followedByExplicitPriority? followedByNonProposalPriorityGrant
    else if !g.over && resA.game.over && !b.hasCheckpointReplay then
      none
    else if openedNewPrompt then
      probeOpenedRep
    else if stoppedByPrompt then
      none
    else
      priorityRecipientOfContinuation? resA.game resA.hasQueuedPending b
        followedByFinishChoice followedByExplicitPriority? followedByNonProposalPriorityGrant
  | .finishResolutionChoice =>
    match classifyFinishResolutionChoice g with
    | .grants (some q) => some q
    | _ => none
  | .afterWardResolved =>
    match classifyAfterWardResolved g with
    | .grants (some q) => some q
    | _ => none
  | .finishPostCast caster grantPriority false hadOpenContinuation =>
    let delegateFc := !grantPriority && !followedByFinishChoice &&
      followedByExplicitPriority?.isNone && !followedByNonProposalPriorityGrant
    match finishPostCastOutcome g caster hadOpenContinuation grantPriority none
        (delegateFinishChoice := delegateFc) with
    | .grants (some q) => some q
    | _ => none
  | .finishBecomeCast caster spellId grantPriority hadOuter openCont =>
    if g.over || g.livingPlayers.isEmpty || hasQueuedPending then none
    else
      match classifyFinishBecomeCast g caster spellId grantPriority hadOuter openCont
          followedByFinishChoice followedByExplicitPriority? with
      | .grants (some q) => some q
      | _ => none
  | .finishProposedSpellCosts stage grantPriority hadOuter openCont =>
    if g.over || g.livingPlayers.isEmpty || hasQueuedPending then none
    else
      match classifyFinishProposedSpellCosts g stage grantPriority hadOuter openCont
          followedByFinishChoice followedByExplicitPriority? with
      | .grants (some q) => some q
      | _ => none
  | .receivePriority p =>
    match classifyFinishAndGrantPriority g p with
    | .grants (some q) => some q
    | _ => none
  | .completeActivation hadOuter openCont =>
    if g.over || g.livingPlayers.isEmpty || hasQueuedPending then none
    else
      match classifyCompleteActivation g hadOuter openCont
          followedByFinishChoice followedByExplicitPriority? with
      | .grants (some q) => some q
      | _ => none
  | .finishBecomeActivated caster srcName srcId act abId srcSnap srcOrig hadOuter openCont =>
    if g.over || g.livingPlayers.isEmpty || hasQueuedPending then none
    else
      match classifyFinishBecomeActivated g caster srcName srcId act abId srcSnap srcOrig hadOuter openCont
          followedByFinishChoice followedByExplicitPriority? with
      | .grants (some q) => some q
      | _ => none
  | .finishPostLoyaltyActivated caster _ srcId _ abId _ _ hadOuter openCont =>
    if g.over || g.livingPlayers.isEmpty || hasQueuedPending then none
    else
      match classifyFinishPostLoyaltyActivated g caster srcId abId hadOuter openCont
          followedByFinishChoice followedByExplicitPriority? with
      | .grants (some q) => some q
      | _ => none
  | .finishTurnFaceUp caster spellId hadOuter =>
    if g.over || g.livingPlayers.isEmpty || hasQueuedPending then none
    else
      match probeCompleteTurnFaceUpOutcome g caster spellId hadOuter
          followedByFinishChoice followedByExplicitPriority? with
      | .grants (some q) => some q
      | _ => none
  | .finishPostStep (.resumeChooseModeAfterLeave p) =>
    if g.over || g.livingPlayers.isEmpty || hasQueuedPending then none
    else
      match classifyResumeChooseModeAfterLeave g p
          followedByFinishChoice followedByExplicitPriority? with
      | .grants (some q) => some q
      | _ => none
  | .finishPostStep (.resumeChooseTargetsAfterLeave p) =>
    if g.over || g.livingPlayers.isEmpty || hasQueuedPending then none
    else
      match classifyResumeChooseTargetsAfterLeave g p
          followedByFinishChoice followedByExplicitPriority? with
      | .grants (some q) => some q
      | _ => none
  | .finishPostStep .afterTriggerTargetsChosen =>
    if g.over || g.livingPlayers.isEmpty || hasQueuedPending then none
    else
      match classifyAfterTriggerTargetsChosenFuel g 16 with
      | .grants (some q) => some q
      | _ => none
  | .finishPostStep step@(.resumeTriggerModesAfterLeave ..)
  | .finishPostStep step@(.resumeUpToTriggerModesAfterLeave ..)
  | .finishPostStep step@(.resumeHawkeyeModesAfterLeave ..) =>
    if g.over || g.livingPlayers.isEmpty || hasQueuedPending then none
    else
      match classifyResumeTriggerModesAfterLeave g step with
      | .grants (some q) => some q
      | _ => none
  | .finishPostStep (.resumeProposalCostAfterLeave p savedP) =>
    if g.over || g.livingPlayers.isEmpty || hasQueuedPending then none
    else
      match classifyResumeProposalCostAfterLeave g p savedP
          followedByFinishChoice followedByExplicitPriority? with
      | .grants (some q) => some q
      | _ => none
  | .payCostPickItems p abilityId sourceId pick remainingIds =>
    if g.over || g.livingPlayers.isEmpty || hasQueuedPending then none
    else
      match classifyPayCostPickItems g p abilityId sourceId pick remainingIds
          followedByFinishChoice followedByExplicitPriority? with
      | .grants (some q) => some q
      | _ => none
  | .finishActivationExtraCosts p sourceId forObject sacrificeSource exileSource stage sinceIdx =>
    if g.over || g.livingPlayers.isEmpty || hasQueuedPending then none
    else
      match classifyFinishActivationExtraCosts g p sourceId forObject sacrificeSource exileSource stage sinceIdx
          followedByFinishChoice followedByExplicitPriority? with
      | .grants (some q) => some q
      | _ => none
  | pr@(.finishActivateManaAbilityPicks p _ _ _ _ _ _ _ _ _ _ _ prevPending ..)
  | pr@(.finishActivateManaAbilityPostSac p _ _ _ _ _ _ _ _ _ prevPending ..) =>
    if g.over || g.livingPlayers.isEmpty || hasQueuedPending then none
    else
      match classifyManaAbilityPostStep g p prevPending pr with
      | .grants (some q) => some q
      | _ => none
  | .finishConcede wasIdlePriority savedPendingPrio wasAssigningCombatDamage savedPending popOuter departed rewindProposal _ =>
    finishConcedePriorityRecipient? g wasIdlePriority savedPendingPrio wasAssigningCombatDamage
      savedPending popOuter (runSba := true) (departed := departed)
      (rewindProposal := rewindProposal)
  | .concedePlayersLoop remaining false mid wasIdlePriority savedPendingPrio wasAssigningCombatDamage savedPending popOuter departed rewindProposal _ =>
    concedePlayersLoopRecipient? g remaining wasIdlePriority savedPendingPrio
      wasAssigningCombatDamage savedPending popOuter
      (departedIn := departed) (rewindProposalIn := rewindProposal)
      (midResolutionOrBatch := mid)
  | .continueStartNextTurn nextP remainingDeparted runBeginTurn alreadyExpired =>
    continueStartNextTurnRecipient? (drainProbePausedStep g) nextP remainingDeparted runBeginTurn alreadyExpired
  | .beginTurnAfterStartExpiry =>
    beginTurnAfterStartExpiryRecipient? g
  | .finishPostStep .startNextTurnAndBegin =>
    startNextTurnAndBeginRecipient? (drainProbePausedStep g)
  | .finishPostStep .endTurnAfterCleanupStepEnded =>
    endTurnAfterCleanupStepEndedRecipient? (drainProbePausedStep g)
  | .finishPostStep (.postSbaCleanup sba) =>
    postSbaCleanupRecipient? (drainProbePausedStep g) sba
  | .finishCleanupAfterClearEot =>
    finishCleanupAfterClearEotRecipient? (drainProbePausedStep g)
  | .finishPostStep .cleanupStepAfterDiscard =>
    cleanupStepAfterDiscardRecipient? (drainProbePausedStep g)
  | .beginStepCont st =>
    beginStepContRecipient? (drainProbePausedStep g) st
  | .finishPostStep (.beginStepAfterPhaseBegan st) =>
    beginStepAfterPhaseBeganRecipient? (drainProbePausedStep g) st
  | .finishPostStep (.beginStepBody st) =>
    stepPriorityRecipient? (drainProbePausedStep g) st
  | .finishPostStep .advanceAfterStepEnded =>
    advanceAfterStepEndedRecipient? (drainProbePausedStep g)
  | pr@(.restorePending ..) =>
    match nonPausingRestorePoppedOuter? g hasQueuedPending pr
        followedByFinishChoice followedByExplicitPriority? with
    | some (g', q', nextPr) =>
      priorityRecipientOfContinuation? g' q' nextPr
        followedByFinishChoice followedByExplicitPriority? followedByNonProposalPriorityGrant
    | none => none
  | .leavePlayersWhoLost savedPending popOuter departed rewindProposal fromEventIdx? =>
    match probeLeavePlayersWhoLost g hasQueuedPending savedPending popOuter departed rewindProposal fromEventIdx? with
    | .delegate g' q' nextPr =>
      priorityRecipientOfContinuation? g' q' nextPr
        followedByFinishChoice followedByExplicitPriority? followedByNonProposalPriorityGrant
    | .paused _ _ _ => none
  | _ => none

/-- Find the first priority-granting continuation leaf in execution order
(left-to-right across `.seq a b`), returning `some (leaf, some q)` for an
explicit recipient `q`, `some (leaf, none)` only when `leaf` itself performs or
chains an implicit `g.pendingPriority` grant, or `none` when no leaf grants
priority (never classifying `hasQueuedPending`-only carry-through bits on
`.untap` or `hadOuter == true` leaves as `some none`). -/
private partial def firstPriorityGrantLeaf? (g : Game) (hasQueuedPending : Bool := false)
    (pr : PendingReplacement)
    (followedByFinishChoice : Bool := false)
    (followedByExplicitPriority? : Option PlayerId := none)
    (followedByNonProposalPriorityGrant : Bool := false) :
    Option (PendingReplacement × Option PlayerId) :=
  match pr with
  | .seq a b =>
    let (resA, nextFbFc, nextFbEp) :=
      seqFollowForReversal g hasQueuedPending a b
        followedByFinishChoice followedByExplicitPriority? followedByNonProposalPriorityGrant
    let openedNewPrompt :=
      (g.pending == .none && resA.game.pending != .none) ||
      (g.afterRandom == .none && resA.game.afterRandom != .none)
    let stoppedByPrompt :=
      resA.game.pending != .none || (g.afterRandom == .none && resA.game.afterRandom != .none)
    let bGrantLeaf? :=
      if !resA.reversedProposal && !(!g.over && resA.game.over && !b.hasCheckpointReplay) &&
          !openedNewPrompt && !stoppedByPrompt then
        firstPriorityGrantLeaf? resA.game resA.hasQueuedPending b
          followedByFinishChoice followedByExplicitPriority? followedByNonProposalPriorityGrant
      else none
    let nextFbFcForA : Bool :=
      match bGrantLeaf? with
      | some (leaf, explicit?) =>
        if leaf.endsWithFinishResolutionChoice then true
        else if explicit?.isSome then false
        else followedByFinishChoice
      | none => followedByFinishChoice || b.endsWithFinishResolutionChoice
    let nextFbEpForA : Option PlayerId :=
      match bGrantLeaf? with
      | some (leaf, explicit?) =>
        if leaf.endsWithFinishResolutionChoice then explicit?
        else if explicit?.isSome then explicit?
        else followedByExplicitPriority?
      | none => followedByExplicitPriority?
    let nextFbNonProp : Bool :=
      followedByNonProposalPriorityGrant || b.endsWithNonProposalPriorityGrant ||
        bGrantLeaf?.any (fun (leaf, _) => isNonProposalGrantLeaf leaf)
    let suppressesPostCastFinish : Bool :=
      match a with
      | .finishPostCast _ false false _ =>
        nextFbFcForA || nextFbNonProp || nextFbEpForA.isSome
      | _ => false
    let skipStandaloneA : Bool :=
      (isManaAbilityContinuation a && !b.isPurePostLog) || suppressesPostCastFinish
    let probeOpenedRepLeaf : Option (PendingReplacement × Option PlayerId) :=
      if let .chooseReplacement .. := resA.game.pending then
        firstContinuationPriorityGrantLeaf? (resA.game.chainPendingReplacement b)
      else none
    if resA.reversedProposal then
      firstPriorityGrantLeaf? g hasQueuedPending a
        nextFbFc nextFbEp followedByNonProposalPriorityGrant
    else if !skipStandaloneA && !b.hasCheckpointReplay then
      match firstPriorityGrantLeaf? g hasQueuedPending a
          nextFbFcForA nextFbEpForA nextFbNonProp with
      | some res => some res
      | none =>
        if !g.over && resA.game.over && !b.hasCheckpointReplay then none
        else if openedNewPrompt then probeOpenedRepLeaf
        else if stoppedByPrompt then none
        else if continuationSettlesControlFlow g false a
            nextFbFcForA nextFbEpForA nextFbNonProp then none
        else bGrantLeaf?
    else if !g.over && resA.game.over && !b.hasCheckpointReplay then
      none
    else if openedNewPrompt then
      probeOpenedRepLeaf
    else if stoppedByPrompt then
      none
    else
      bGrantLeaf?
  | pr@(.restorePending ..) =>
    match nonPausingRestorePoppedOuter? g hasQueuedPending pr
        followedByFinishChoice followedByExplicitPriority? with
    | some (g', q', nextPr) =>
      firstPriorityGrantLeaf? g' q' nextPr
        followedByFinishChoice followedByExplicitPriority? followedByNonProposalPriorityGrant
    | none => none
  | .leavePlayersWhoLost savedPending popOuter departed rewindProposal fromEventIdx? =>
    match probeLeavePlayersWhoLost g hasQueuedPending savedPending popOuter departed rewindProposal fromEventIdx? with
    | .delegate g' q' nextPr =>
      firstPriorityGrantLeaf? g' q' nextPr
        followedByFinishChoice followedByExplicitPriority? followedByNonProposalPriorityGrant
    | .paused _ _ _ => none
  | pr =>
    if !continuationGrantsPriority g hasQueuedPending pr
        followedByFinishChoice followedByExplicitPriority? followedByNonProposalPriorityGrant then none
    else
      match priorityRecipientOfContinuation? g hasQueuedPending pr
          followedByFinishChoice followedByExplicitPriority? followedByNonProposalPriorityGrant with
      | some q => some (pr, some q)
      | none =>
        let isImplicitGrant : Bool :=
          match pr with
          | .receivePriority p =>
            match classifyFinishAndGrantPriority g p with
            | .implicitResolutionChoice | .grants none => true
            | _ => false
          | .finishResolutionChoice => true
          | .afterWardResolved =>
            match classifyAfterWardResolved g with
            | .implicitResolutionChoice | .grants none => true
            | _ => false
          | .finishPostCast caster grantPriority false openCont =>
            let delegateFc := !grantPriority && !followedByFinishChoice &&
              followedByExplicitPriority?.isNone && !followedByNonProposalPriorityGrant
            match finishPostCastOutcome g caster openCont grantPriority none
                (delegateFinishChoice := delegateFc) with
            | .implicitResolutionChoice | .grants none => true
            | _ => false
          | .finishBecomeCast caster spellId grantPriority hadOuter openCont =>
            match classifyFinishBecomeCast g caster spellId grantPriority hadOuter openCont
                followedByFinishChoice followedByExplicitPriority? with
            | .implicitResolutionChoice | .grants none => true
            | _ => false
          | .completeActivation hadOuter openCont =>
            match classifyCompleteActivation g hadOuter openCont
                followedByFinishChoice followedByExplicitPriority? with
            | .implicitResolutionChoice | .grants none => true
            | _ => false
          | .finishBecomeActivated caster srcName srcId act abId srcSnap srcOrig hadOuter openCont =>
            match classifyFinishBecomeActivated g caster srcName srcId act abId srcSnap srcOrig hadOuter openCont
                followedByFinishChoice followedByExplicitPriority? with
            | .implicitResolutionChoice | .grants none => true
            | _ => false
          | .finishPostLoyaltyActivated caster _ srcId _ abId _ _ hadOuter openCont =>
            match classifyFinishPostLoyaltyActivated g caster srcId abId hadOuter openCont
                followedByFinishChoice followedByExplicitPriority? with
            | .implicitResolutionChoice | .grants none => true
            | _ => false
          | .finishTurnFaceUp caster spellId hadOuter =>
            match probeCompleteTurnFaceUpOutcome g caster spellId hadOuter
                followedByFinishChoice followedByExplicitPriority? with
            | .implicitResolutionChoice | .grants none => true
            | _ => false
          | .finishProposedSpellCosts stage grantPriority hadOuter openCont =>
            match classifyFinishProposedSpellCosts g stage grantPriority hadOuter openCont
                followedByFinishChoice followedByExplicitPriority? with
            | .implicitResolutionChoice | .grants none => true
            | _ => false
          | .finishPostStep (.resumeChooseModeAfterLeave p) =>
            match classifyResumeChooseModeAfterLeave g p
                followedByFinishChoice followedByExplicitPriority? with
            | .implicitResolutionChoice | .grants none => true
            | _ => false
          | .finishPostStep (.resumeChooseTargetsAfterLeave p) =>
            match classifyResumeChooseTargetsAfterLeave g p
                followedByFinishChoice followedByExplicitPriority? with
            | .implicitResolutionChoice | .grants none => true
            | _ => false
          | .finishPostStep .afterTriggerTargetsChosen =>
            match classifyAfterTriggerTargetsChosenFuel g 16 with
            | .implicitResolutionChoice | .grants none => true
            | _ => false
          | .finishPostStep step@(.resumeTriggerModesAfterLeave ..)
          | .finishPostStep step@(.resumeUpToTriggerModesAfterLeave ..)
          | .finishPostStep step@(.resumeHawkeyeModesAfterLeave ..) =>
            match classifyResumeTriggerModesAfterLeave g step with
            | .implicitResolutionChoice | .grants none => true
            | _ => false
          | .finishPostStep (.resumeProposalCostAfterLeave p savedP) =>
            match classifyResumeProposalCostAfterLeave g p savedP
                followedByFinishChoice followedByExplicitPriority? with
            | .implicitResolutionChoice | .grants none => true
            | _ => false
          | .payCostPickItems p abilityId sourceId pick remainingIds =>
            match classifyPayCostPickItems g p abilityId sourceId pick remainingIds
                followedByFinishChoice followedByExplicitPriority? with
            | .implicitResolutionChoice | .grants none => true
            | _ => false
          | .finishActivationExtraCosts p sourceId forObject sacrificeSource exileSource stage sinceIdx =>
            match classifyFinishActivationExtraCosts g p sourceId forObject sacrificeSource exileSource stage sinceIdx
                followedByFinishChoice followedByExplicitPriority? with
            | .implicitResolutionChoice | .grants none => true
            | _ => false
          | .finishActivateManaAbilityPicks p _ _ _ _ _ _ _ _ _ _ _ prevPending ..
          | .finishActivateManaAbilityPostSac p _ _ _ _ _ _ _ _ _ prevPending .. =>
            match classifyManaAbilityPostStep g p prevPending pr with
            | .implicitResolutionChoice | .grants none => true
            | _ => false
          | .finishConcede wasIdlePriority savedPendingPrio wasAssigningCombatDamage savedPending popOuter departed rewindProposal _ =>
            match classifyFinishConcedePriority g wasIdlePriority savedPendingPrio
                wasAssigningCombatDamage savedPending popOuter (runSba := true)
                (departed := departed) (rewindProposal := rewindProposal) with
            | .implicitResolutionChoice | .grants none => true
            | _ => false
          | .concedePlayersLoop remaining false mid wasIdlePriority savedPendingPrio wasAssigningCombatDamage savedPending popOuter departed rewindProposal _ =>
            match classifyConcedePlayersLoop g remaining wasIdlePriority savedPendingPrio
                wasAssigningCombatDamage savedPending popOuter
                (departedIn := departed) (rewindProposalIn := rewindProposal)
                (midResolutionOrBatch := mid) with
            | .implicitResolutionChoice | .grants none => true
            | _ => false
          | _ => false
        if isImplicitGrant then some (pr, none) else none

/-- Resolve the first priority-granting continuation leaf in execution order
(left-to-right across `.seq a b`), returning `some (some q)` for an explicit
recipient `q`, `some none` for an implicit grant (such as `.finishResolutionChoice`),
or `none` when no leaf grants priority (CR 117.3c / 605.3b / 616.1). -/
partial def firstPriorityGrantRecipient? (g : Game) (hasQueuedPending : Bool := false)
    (pr : PendingReplacement)
    (followedByFinishChoice : Bool := false)
    (followedByExplicitPriority? : Option PlayerId := none)
    (followedByNonProposalPriorityGrant : Bool := false) : Option (Option PlayerId) :=
  (firstPriorityGrantLeaf? g hasQueuedPending pr
    followedByFinishChoice followedByExplicitPriority? followedByNonProposalPriorityGrant).map Prod.snd

/-- Whether `pr` relies on `g.pendingPriority` (either directly granting via
`g.pendingPriority.getD g.activePlayer` or opening an intermediate prompt such
as `pendingMayCastFromExile`, `pendingFreeCopies`, `triggerNeedingTargets`, or
an interpreter wait that resumes into `finishResolutionChoice`). -/
private partial def continuationUsesImplicitPendingPriority (g : Game)
    (hasQueuedPending : Bool := false)
    (pr : PendingReplacement)
    (followedByFinishChoice : Bool := false)
    (followedByExplicitPriority? : Option PlayerId := none)
    (followedByNonProposalPriorityGrant : Bool := false) : Bool :=
  let opensExplicitPrompt (gCheck : Game) : Bool :=
    (match gCheck.pending with
     | .declareAttackers .. | .declareBlockers .. | .assignCombatDamage .. => true
     | _ => false) ||
    gCheck.proposedSpell.any (fun prop =>
      !prop.resolutionCast && isProposalPromptFor prop.caster gCheck.pending)
  match pr with
  | .seq a b =>
    let (resA, nextFbFc, nextFbEp) :=
      seqFollowForReversal g hasQueuedPending a b
        followedByFinishChoice followedByExplicitPriority? followedByNonProposalPriorityGrant
    let openedNewPrompt :=
      (g.pending == .none && resA.game.pending != .none) ||
      (g.afterRandom == .none && resA.game.afterRandom != .none)
    let stoppedByPrompt :=
      resA.game.pending != .none || (g.afterRandom == .none && resA.game.afterRandom != .none)
    let bGrantLeaf? :=
      if !resA.reversedProposal && !(!g.over && resA.game.over && !b.hasCheckpointReplay) &&
          !openedNewPrompt && !stoppedByPrompt then
        firstPriorityGrantLeaf? resA.game resA.hasQueuedPending b
          followedByFinishChoice followedByExplicitPriority? followedByNonProposalPriorityGrant
      else none
    let nextFbFcForA : Bool :=
      match bGrantLeaf? with
      | some (leaf, explicit?) =>
        if leaf.endsWithFinishResolutionChoice then true
        else if explicit?.isSome then false
        else followedByFinishChoice
      | none => followedByFinishChoice || b.endsWithFinishResolutionChoice
    let nextFbEpForA : Option PlayerId :=
      match bGrantLeaf? with
      | some (leaf, explicit?) =>
        if leaf.endsWithFinishResolutionChoice then explicit?
        else if explicit?.isSome then explicit?
        else followedByExplicitPriority?
      | none => followedByExplicitPriority?
    let nextFbNonProp : Bool :=
      followedByNonProposalPriorityGrant || b.endsWithNonProposalPriorityGrant ||
        bGrantLeaf?.any (fun (leaf, _) => isNonProposalGrantLeaf leaf)
    let suppressesPostCastFinish : Bool :=
      match a with
      | .finishPostCast _ false false _ =>
        nextFbFcForA || nextFbNonProp || nextFbEpForA.isSome
      | _ => false
    let skipStandaloneA : Bool :=
      (isManaAbilityContinuation a && !b.isPurePostLog) || suppressesPostCastFinish
    if resA.reversedProposal then
      continuationUsesImplicitPendingPriority g hasQueuedPending a
        nextFbFc nextFbEp followedByNonProposalPriorityGrant
    else if !g.over && resA.game.over && !b.hasCheckpointReplay then
      false
    else if openedNewPrompt then
      let gCh := resA.game.chainPendingReplacement b
      if let .chooseReplacement .. := gCh.pending then
        gCh.hasImplicitPendingPriorityContinuation
      else
        match gCh.firstContinuationPriorityGrant? with
        | some (some _) => false
        | some none => true
        | none => !opensExplicitPrompt gCh
    else if resA.game.pending != .none then
      !skipStandaloneA &&
        continuationUsesImplicitPendingPriority g hasQueuedPending a
          nextFbFcForA nextFbEpForA nextFbNonProp
    else if !skipStandaloneA && !b.hasCheckpointReplay &&
        (priorityRecipientOfContinuation? g hasQueuedPending a
          nextFbFcForA nextFbEpForA nextFbNonProp).isSome then
      false
    else if !skipStandaloneA && !b.hasCheckpointReplay &&
        continuationUsesImplicitPendingPriority g hasQueuedPending a
          nextFbFcForA nextFbEpForA nextFbNonProp then
      true
    else if !skipStandaloneA && !b.hasCheckpointReplay &&
        (firstPriorityGrantLeaf? g hasQueuedPending a
          nextFbFcForA nextFbEpForA nextFbNonProp).isSome then
      false
    else if !skipStandaloneA && !b.hasCheckpointReplay &&
        continuationSettlesControlFlow g false a
          nextFbFcForA nextFbEpForA nextFbNonProp then
      false
    else
      continuationUsesImplicitPendingPriority resA.game resA.hasQueuedPending b
        followedByFinishChoice followedByExplicitPriority? followedByNonProposalPriorityGrant
  | pr@(.restorePending ..) =>
    match probeRestorePendingCore g hasQueuedPending pr
        followedByFinishChoice followedByExplicitPriority? with
    | .delegate g' q' nextPr =>
      continuationUsesImplicitPendingPriority g' q' nextPr
        followedByFinishChoice followedByExplicitPriority? followedByNonProposalPriorityGrant
    | .paused gOpened _ settles =>
      if gOpened.over || gOpened.livingPlayers.isEmpty then false
      else if let .chooseReplacement .. := gOpened.pending then
        gOpened.hasImplicitPendingPriorityContinuation
      else if gOpened.pending != .none || gOpened.afterRandom != .none then
        match gOpened.firstContinuationPriorityGrant? with
        | some (some _) => false
        | some none => true
        | none =>
          settles && !opensExplicitPrompt gOpened &&
            (gOpened.hasImplicitPendingPriorityContinuation ||
              (gOpened.pendingReplacement.isNone && gOpened.outerPendingReplacements.isEmpty))
      else false
  | .leavePlayersWhoLost savedPending popOuter departed rewindProposal fromEventIdx? =>
    match probeLeavePlayersWhoLost g hasQueuedPending savedPending popOuter departed rewindProposal fromEventIdx? with
    | .delegate g' q' nextPr =>
      continuationUsesImplicitPendingPriority g' q' nextPr
        followedByFinishChoice followedByExplicitPriority? followedByNonProposalPriorityGrant
    | .paused gOpened _ settles =>
      if gOpened.over || gOpened.livingPlayers.isEmpty then false
      else if let .chooseReplacement .. := gOpened.pending then
        gOpened.hasImplicitPendingPriorityContinuation
      else if gOpened.pending != .none || gOpened.afterRandom != .none then
        match gOpened.firstContinuationPriorityGrant? with
        | some (some _) => false
        | some none => true
        | none =>
          settles && !opensExplicitPrompt gOpened &&
            (gOpened.hasImplicitPendingPriorityContinuation ||
              (gOpened.pendingReplacement.isNone && gOpened.outerPendingReplacements.isEmpty))
      else false
  | .receivePriority p =>
    if g.over || g.livingPlayers.isEmpty then false
    else
      match classifyFinishAndGrantPriority g p with
      | .implicitResolutionChoice => true
      | _ => false
  | .finishResolutionChoice =>
    match classifyFinishResolutionChoice g with
    | .implicitResolutionChoice => true
    | .settlesPromptOrOver => !g.over && !g.livingPlayers.isEmpty
    | _ => false
  | .afterWardResolved =>
    match classifyAfterWardResolved g with
    | .implicitResolutionChoice => true
    | .settlesPromptOrOver => !g.over && !g.livingPlayers.isEmpty
    | _ => false
  | .finishPostCast caster grantPriority hadOuter openCont =>
    if hadOuter || g.over || g.livingPlayers.isEmpty then false
    else
      let delegateFc := !grantPriority && !followedByFinishChoice &&
        followedByExplicitPriority?.isNone && !followedByNonProposalPriorityGrant
      match finishPostCastOutcome g caster openCont grantPriority none
          (delegateFinishChoice := delegateFc) with
      | .implicitResolutionChoice => true
      | .settlesPromptOrOver => delegateFc
      | _ => false
  | .finishBecomeCast caster spellId grantPriority hadOuter openCont =>
    if g.over || g.livingPlayers.isEmpty then false
    else
      match classifyFinishBecomeCast g caster spellId grantPriority hadOuter openCont
          followedByFinishChoice followedByExplicitPriority? with
      | .implicitResolutionChoice => true
      | .settlesPromptOrOver => !grantPriority && !hadOuter
      | _ => false
  | .finishProposedSpellCosts stage grantPriority hadOuter openCont =>
    if g.over || g.livingPlayers.isEmpty then false
    else
      match classifyFinishProposedSpellCosts g stage grantPriority hadOuter openCont
          followedByFinishChoice followedByExplicitPriority? with
      | .implicitResolutionChoice => true
      | .settlesPromptOrOver => !grantPriority && !hadOuter
      | _ => false
  | .finishPostStep (.resumeChooseModeAfterLeave p) =>
    if g.over || g.livingPlayers.isEmpty then false
    else
      match classifyResumeChooseModeAfterLeave g p
          followedByFinishChoice followedByExplicitPriority? with
      | .implicitResolutionChoice => true
      | _ => false
  | .finishPostStep (.resumeChooseTargetsAfterLeave p) =>
    if g.over || g.livingPlayers.isEmpty then false
    else
      match classifyResumeChooseTargetsAfterLeave g p
          followedByFinishChoice followedByExplicitPriority? with
      | .implicitResolutionChoice => true
      | _ => false
  | .finishPostStep .afterTriggerTargetsChosen =>
    if g.over || g.livingPlayers.isEmpty then false
    else
      match classifyAfterTriggerTargetsChosenFuel g 16 with
      | .implicitResolutionChoice => true
      | _ => false
  | .finishPostStep step@(.resumeTriggerModesAfterLeave ..)
  | .finishPostStep step@(.resumeUpToTriggerModesAfterLeave ..)
  | .finishPostStep step@(.resumeHawkeyeModesAfterLeave ..) =>
    if g.over || g.livingPlayers.isEmpty then false
    else
      match classifyResumeTriggerModesAfterLeave g step with
      | .implicitResolutionChoice => true
      | _ => false
  | .finishPostStep (.resumeProposalCostAfterLeave p savedP) =>
    if g.over || g.livingPlayers.isEmpty then false
    else
      match classifyResumeProposalCostAfterLeave g p savedP
          followedByFinishChoice followedByExplicitPriority? with
      | .implicitResolutionChoice => true
      | _ => false
  | .payCostPickItems p abilityId sourceId pick remainingIds =>
    if g.over || g.livingPlayers.isEmpty then false
    else
      match classifyPayCostPickItems g p abilityId sourceId pick remainingIds
          followedByFinishChoice followedByExplicitPriority? with
      | .implicitResolutionChoice => true
      | _ => false
  | .finishActivationExtraCosts p sourceId forObject sacrificeSource exileSource stage sinceIdx =>
    if g.over || g.livingPlayers.isEmpty then false
    else
      match classifyFinishActivationExtraCosts g p sourceId forObject sacrificeSource exileSource stage sinceIdx
          followedByFinishChoice followedByExplicitPriority? with
      | .implicitResolutionChoice => true
      | _ => false
  | pr@(.dealDamageToPlayer ..)
  | pr@(.runModalManaEffect ..)
  | pr@(.finishManaAbilityMountainTrigger ..) =>
    if g.over || g.livingPlayers.isEmpty then false
    else
      let g1 := drainProbeNonPriorityCont g pr
      if g1.over || g1.livingPlayers.isEmpty then false
      else if let .chooseReplacement .. := g1.pending then
        g1.hasImplicitPendingPriorityContinuation
      else if g1.pending != .none || g1.afterRandom != .none then
        match g1.firstContinuationPriorityGrant? with
        | some (some _) => false
        | some none => true
        | none =>
          !opensExplicitPrompt g1 &&
            (g1.hasImplicitPendingPriorityContinuation ||
              (g1.pendingReplacement.isNone && g1.outerPendingReplacements.isEmpty))
      else false
  | .finishConcede wasIdlePriority savedPendingPrio wasAssigningCombatDamage savedPending popOuter departed rewindProposal _ =>
    if g.over || g.livingPlayers.isEmpty then false
    else
      match classifyFinishConcedePriority g wasIdlePriority savedPendingPrio
          wasAssigningCombatDamage savedPending popOuter (runSba := true)
          (departed := departed) (rewindProposal := rewindProposal) with
      | .implicitResolutionChoice => true
      | .settlesPromptOrOver => savedPendingPrio.isNone
      | _ => false
  | .concedePlayersLoop remaining wp mid wasIdlePriority savedPendingPrio wasAssigningCombatDamage savedPending popOuter departed rewindProposal _ =>
    if wp || g.over || g.livingPlayers.isEmpty then false
    else
      match classifyConcedePlayersLoop g remaining wasIdlePriority savedPendingPrio
          wasAssigningCombatDamage savedPending popOuter
          (departedIn := departed) (rewindProposalIn := rewindProposal)
          (midResolutionOrBatch := mid) with
      | .implicitResolutionChoice => true
      | .settlesPromptOrOver => savedPendingPrio.isNone
      | _ => false
  | .finishPostStep (.logInfluenceThenScryTwo sourceId _) =>
    !g.over &&
      (g.findObject? sourceId).any fun src =>
        src.isOnBattlefield && g.stillInGame (g.you src) && !(g.player (g.you src)).library.isEmpty
  | .finishDrawThenBeginDiscard p discardRounds =>
    !g.over && (discardRounds > 0 || g.thirstDiscardsLeft > 0) &&
      g.stillInGame p && !(g.discardableHandIds p).isEmpty
  | .finishBeginRecruit p =>
    !g.over && g.stillInGame p && !(g.discardableHandIds p).isEmpty
  | .shuffleThen p onDone =>
    if g.over then false
    else
      let g1 := g.shuffleThen p onDone
      !g1.over && (g1.pending != .none || g1.afterRandom != .none)
  | pr =>
    match firstPriorityGrantLeaf? g hasQueuedPending pr
        followedByFinishChoice followedByExplicitPriority? followedByNonProposalPriorityGrant with
    | some (_, none) => true
    | _ => false

private partial def advanceLiveQueueStep (gStep : Game) (curQueued : Bool)
    (step : PendingReplacement) : Option (Game × Bool) :=
  let adv := advanceProbeOnResumeCore gStep curQueued step
  let openedNewPrompt :=
    (gStep.pending == .none && adv.game.pending != .none) ||
    (gStep.afterRandom == .none && adv.game.afterRandom != .none)
  if adv.reversedProposal || (!gStep.over && adv.game.over) then
    none
  else if openedNewPrompt then
    match adv.game.pending with
    | .chooseReplacement q choices =>
      if adv.game.afterRandom != .none then none
      else
        let alreadyOrderedCycle :=
          (adv.game.defaultReplacementId q choices).any adv.game.replacementOrder.contains
        let nextG :=
          if alreadyOrderedCycle then
            let gCleared := adv.game.change (.pending .none)
            if gCleared.pendingReplacement == some step then gCleared.change (.pendingReplacement none)
            else gCleared
          else
            (recordProbeFirstReplacement adv.game).change (.pending .none)
        some (nextG, adv.hasQueuedPending)
    | _ => none
  else
    some (adv.game, adv.hasQueuedPending)

private partial def firstContinuationPriorityGrantLeafLoop (curG : Game) (curQueued : Bool)
    (stepsLeft : Nat) : Option (PendingReplacement × Option PlayerId) :=
  if stepsLeft == 0 then none
  else
    let nextStep? : Option (Game × PendingReplacement) :=
      match curG.pendingReplacement with
      | some pr => some ((curG.change (.pendingReplacement none)).popEmptyTopContinuationFrames, pr)
      | none =>
        curG.outerPendingReplacements.back?.map fun outer =>
          ((curG.change .popOuterPendingReplacement).popEmptyTopContinuationFrames, outer)
    match nextStep? with
    | none => none
    | some (gStep, step) =>
      if let some res := firstPriorityGrantLeaf? gStep curQueued step then some res
      else if continuationSettlesControlFlow gStep curQueued step then none
      else match advanceLiveQueueStep gStep curQueued step with
        | none => none
        | some (nextG, nextQ) =>
          firstContinuationPriorityGrantLeafLoop nextG nextQ (stepsLeft - 1)

/-- Resolve the first priority-granting continuation leaf across `g.pendingReplacement`
followed by `g.outerPendingReplacements` from top (`size - 1`) down to `0`,
advancing `g` across non-settling steps and stopping at any settling, prompt-opening,
proposal-reversing, or game-ending continuation. -/
private partial def firstContinuationPriorityGrantLeaf? (g : Game) :
    Option (PendingReplacement × Option PlayerId) :=
  let g0 := if g.sbaPaused then (recordProbeFirstReplacement g).change (.pending .none) else g
  firstContinuationPriorityGrantLeafLoop g0 false 64

/-- Resolve the first priority-granting continuation across `g.pendingReplacement`
followed by `g.outerPendingReplacements` from top (`size - 1`) down to `0`. -/
@[export mtg_game_first_continuation_priority_grant]
partial def firstContinuationPriorityGrant? (g : Game) : Option (Option PlayerId) :=
  (firstContinuationPriorityGrantLeaf? g).map Prod.snd

private partial def anyContinuationGrantsPriorityLoop (curG : Game) (curQueued : Bool)
    (stepsLeft : Nat) : Bool :=
  if stepsLeft == 0 then false
  else
    let nextStep? : Option (Game × PendingReplacement) :=
      match curG.pendingReplacement with
      | some pr => some ((curG.change (.pendingReplacement none)).popEmptyTopContinuationFrames, pr)
      | none =>
        curG.outerPendingReplacements.back?.map fun outer =>
          ((curG.change .popOuterPendingReplacement).popEmptyTopContinuationFrames, outer)
    match nextStep? with
    | none => false
    | some (gStep, step) =>
      if continuationGrantsPriority gStep curQueued step then true
      else if continuationSettlesControlFlow gStep curQueued step then false
      else match advanceLiveQueueStep gStep curQueued step with
        | none => false
        | some (nextG, nextQ) =>
          anyContinuationGrantsPriorityLoop nextG nextQ (stepsLeft - 1)

/-- Whether `g.pendingReplacement` or `g.outerPendingReplacements` already
contains a continuation that grants priority (CR 117.3 / 616.1). -/
@[export mtg_game_any_continuation_grants_priority]
partial def anyContinuationGrantsPriority (g : Game) : Bool :=
  let g0 := if g.sbaPaused then (recordProbeFirstReplacement g).change (.pending .none) else g
  anyContinuationGrantsPriorityLoop g0 false 64

private partial def anyContinuationSettlesControlFlowLoop (curG : Game) (curQueued : Bool)
    (stepsLeft : Nat) : Bool :=
  if stepsLeft == 0 then false
  else
    let nextStep? : Option (Game × PendingReplacement) :=
      match curG.pendingReplacement with
      | some pr => some ((curG.change (.pendingReplacement none)).popEmptyTopContinuationFrames, pr)
      | none =>
        curG.outerPendingReplacements.back?.map fun outer =>
          ((curG.change .popOuterPendingReplacement).popEmptyTopContinuationFrames, outer)
    match nextStep? with
    | none => false
    | some (gStep, step) =>
      if continuationSettlesControlFlow gStep curQueued step then true
      else match advanceLiveQueueStep gStep curQueued step with
        | none => true
        | some (nextG, nextQ) =>
          anyContinuationSettlesControlFlowLoop nextG nextQ (stepsLeft - 1)

private partial def anyContinuationSettlesControlFlowWithQueued (g : Game)
    (initialQueued : Bool) : Bool :=
  let g0 := if g.sbaPaused then (recordProbeFirstReplacement g).change (.pending .none) else g
  anyContinuationSettlesControlFlowLoop g0 initialQueued 64

/-- Whether `g.pendingReplacement` or `g.outerPendingReplacements` already
contains a continuation that deterministically settles control flow (either by
granting priority, opening a blocking prompt, or ending the game, CR 117.3 / 616.1). -/
@[export mtg_game_any_continuation_settles_control_flow]
partial def anyContinuationSettlesControlFlow (g : Game) : Bool :=
  anyContinuationSettlesControlFlowWithQueued g false

/-- Whether the first priority-granting continuation in execution order is
implicit (e.g. `.finishResolutionChoice`, which reads
`g.pendingPriority.getD g.activePlayer`, CR 117.3c / 605.3b). -/
@[export mtg_game_has_implicit_priority_continuation]
partial def hasImplicitPriorityContinuation (g : Game) : Bool :=
  firstContinuationPriorityGrant? g == some none

private partial def hasImplicitPendingPriorityContinuationLoop (curG : Game) (curQueued : Bool)
    (stepsLeft : Nat) : Bool :=
  if stepsLeft == 0 then false
  else
    let nextStep? : Option (Game × PendingReplacement) :=
      match curG.pendingReplacement with
      | some pr => some ((curG.change (.pendingReplacement none)).popEmptyTopContinuationFrames, pr)
      | none =>
        curG.outerPendingReplacements.back?.map fun outer =>
          ((curG.change .popOuterPendingReplacement).popEmptyTopContinuationFrames, outer)
    match nextStep? with
    | none => false
    | some (gStep, step) =>
      if continuationUsesImplicitPendingPriority gStep curQueued step then true
      else if continuationSettlesControlFlow gStep curQueued step then false
      else match advanceLiveQueueStep gStep curQueued step with
        | none => false
        | some (nextG, nextQ) =>
          hasImplicitPendingPriorityContinuationLoop nextG nextQ (stepsLeft - 1)

/-- Whether the active continuation queue has no explicit priority recipient and
will read `g.pendingPriority.getD g.activePlayer` either directly or after an
intermediate prompt (CR 117.3c / 603.3d / 616.1). -/
@[export mtg_game_has_implicit_pending_priority_continuation]
partial def hasImplicitPendingPriorityContinuation (g : Game) : Bool :=
  match g.firstContinuationPriorityGrant? with
  | some (some _) => false
  | some none => true
  | none =>
    let g0 := if g.sbaPaused then (recordProbeFirstReplacement g).change (.pending .none) else g
    hasImplicitPendingPriorityContinuationLoop g0 false 64

/-- Drain queued `g.pendingReplacement` continuations and paused
`currentInterpWait?` steps while no interactive `Pending` or `afterRandom`
choice is open. -/
@[export mtg_game_drain_pending_continuations]
partial def drainPendingContinuations (g : Game) : Game :=
  if g.over || g.pending != .none || g.afterRandom != .none then g
  else
    match g.pendingReplacement with
    | some cont =>
      let g := ((g.change (.pendingReplacement none)).popEmptyTopContinuationFrames).resumePendingReplacement cont
      g.drainPendingContinuations
    | none =>
      if g.currentInterpWait?.isSome &&
          !(g.proposedSpell.isNone && (g.pendingMayCastFromExile.isSome || g.pendingFreeCopies.isSome)) then
        let g := g.resumeInterpWaitIfReady
        g.drainPendingContinuations
      else
        match g.outerPendingReplacements.back? with
        | some outer =>
          let g := ((g.change .popOuterPendingReplacement).popEmptyTopContinuationFrames).resumePendingReplacement outer
          g.drainPendingContinuations
        | none => g

/-- Drain active continuations, chain `.receivePriority p` if a CR 616.1
`Pending.chooseReplacement` pause opened, or grant priority to `p` when idle. -/
partial def finishAndGrantPriority (g : Game)
    (p : PlayerId :=
      (match g.firstContinuationPriorityGrantFwd? with
       | some (some q) => some q
       | _ => none)
        |>.getD (g.pendingPriority.getD g.activePlayer)) : Game :=
  let alreadyGrants : Bool :=
    g.pending == .none && g.afterRandom == .none && g.anyContinuationGrantsPriority
  let entryExplicitGrant : Bool := alreadyGrants && !g.hasImplicitPriorityContinuation
  let hadEntryPending : Bool := g.pending != .none
  let g :=
    let target := g.priorityInstead p
    if !entryExplicitGrant && g.hasImplicitPendingPriorityContinuation &&
        (!hadEntryPending || g.pendingPriority.isNone) && g.pendingPriority != some target then
      g.change (.pendingPriority (some target))
    else g
  let preDrainPendingPrio := g.pendingPriority
  let preDrainEvSize := g.events.size
  let g := g.drainPendingContinuations
  let drainedSetPendingPrio : Bool :=
    g.pendingPriority.isSome &&
      (g.pendingPriority != preDrainPendingPrio ||
        (g.events.extract preDrainEvSize g.events.size).any fun
          | .engine _ (.pendingPriority (some _)) _ => true
          | _ => false)
  let effP := (if drainedSetPendingPrio then g.pendingPriority else none).getD p
  let g := if g.pending == .none && g.afterRandom == .none then g.popEmptyContinuationFrames else g
  if g.over then
    let g :=
      if g.proposedSpell.any (fun prop =>
          !g.stillInGame prop.caster || (g.findObject? prop.spellId).isNone) then
        (if g.pending == .none then g else g.change (.pending .none)).reverseProposedSpell
          (resumeContinuation := true) (alwaysGrantPriority := true)
      else g
    g.completeActiveResolutions
  else if let .chooseReplacement .. := g.pending then
    if g.anyContinuationSettlesControlFlow then
      let target := g.priorityInstead p
      if !entryExplicitGrant && !drainedSetPendingPrio && g.hasImplicitPendingPriorityContinuation &&
          (!hadEntryPending || g.pendingPriority.isNone) && g.pendingPriority != some target then
        g.change (.pendingPriority (some target))
      else g
    else
      let prio := (if entryExplicitGrant || drainedSetPendingPrio then g.pendingPriority else none).getD p
      g.chainPendingReplacement (.receivePriority (g.priorityInstead prio))
  else if let .chooseLegend .. := g.pending then
    let target := g.priorityInstead p
    if entryExplicitGrant || drainedSetPendingPrio || hadEntryPending || g.pendingPriority == some target then g
    else g.change (.pendingPriority (some target))
  else if g.pending != .none || g.afterRandom != .none || alreadyGrants then
    let target := g.priorityInstead p
    let openedPrompt := g.pending != .none || g.afterRandom != .none
    let hasExplicitPostGrant :=
      match g.firstContinuationPriorityGrant? with
      | some (some _) => true
      | _ => false
    if !entryExplicitGrant && !drainedSetPendingPrio &&
        ((openedPrompt && !hasExplicitPostGrant) || g.hasImplicitPendingPriorityContinuation) &&
        (!hadEntryPending || g.pendingPriority.isNone) && g.pendingPriority != some target then
      g.change (.pendingPriority (some target))
    else g
  else if g.proposedSpell.any (fun prop =>
      !g.stillInGame prop.caster || (g.findObject? prop.spellId).isNone) then
    let g :=
      (if g.pending == .none then g else g.change (.pending .none)).reverseProposedSpell
        (resumeContinuation := true) (alwaysGrantPriority := true)
    if !g.over && g.pending == .none && g.afterRandom == .none &&
        g.proposedSpell.isNone &&
        (g.pendingMayCastFromExile.isSome || g.pendingFreeCopies.isSome) then
      g.finishAndGrantPriority effP
    else if !g.over && g.pending == .none && g.continuations.isEmpty &&
        g.triggerNeedingTargets.isSome then
      g.promptTriggerTargetsIfNeeded
    else g
  else if g.proposedSpell.isSome then
    if g.pending == .none then g else g.change (.pending .none)
  else if g.pendingMayCastFromExile.isSome || g.pendingFreeCopies.isSome then
    let target := g.priorityInstead effP
    let g :=
      if !entryExplicitGrant && !drainedSetPendingPrio && (!hadEntryPending || g.pendingPriority.isNone) &&
          g.pendingPriority != some target then
        g.change (.pendingPriority (some target))
      else g
    let g := g.reopenDeferredExileCasts
    if let .chooseReplacement .. := g.pending then
      if g.anyContinuationSettlesControlFlow then g
      else if g.currentInterpWait?.isSome then g.chainPendingReplacement .finishResolutionChoice
      else g.chainPendingReplacement (.receivePriority (g.priorityInstead effP))
    else if g.pending != .none then g
    else if g.currentInterpWait?.isSome || g.pendingReplacement.isSome ||
        !g.outerPendingReplacements.isEmpty then
      g.finishResolutionChoice
    else if g.triggerNeedingTargets.isSome then
      (g.popEmptyContinuationFrames).promptTriggerTargetsIfNeeded
    else
      (g.popEmptyContinuationFrames).receivePriority effP
  else if g.triggerNeedingTargets.isSome then
    let target := g.priorityInstead effP
    let g := if g.pendingPriority == some target then g else g.change (.pendingPriority (some target))
    g.promptTriggerTargetsIfNeeded
  else g.receivePriority effP

@[export mtg_game_finish_and_grant_priority]
partial def finishAndGrantPriorityExport (g : Game) (prio : PlayerId) : Game :=
  g.finishAndGrantPriority prio

/-- Run pending continuations and suspended interpreter waits, then give priority
when nothing else is pending. -/
partial def resumeSequenceThenPriority (g : Game) : Game :=
  g.finishAndGrantPriority

/-- Continue a discard chain. -/
partial def continueAfterDiscard (g : Game) (players : Array PlayerId)
    (samePlayer : Bool := false) (count : Nat := 1) : Game :=
  g.beginDiscardCards players (count := count) (samePlayer := samePlayer) (resuming := true)

/-- Finish a `Pending.resolutionChoice` and let the game continue: chain
`.finishResolutionChoice` through an open replacement, return while any other
prompt is open, then drain continuations and resume interpreter waits / priority. -/
partial def finishResolutionChoice (g : Game) : Game :=
  if let .chooseReplacement .. := g.pending then
    if g.anyContinuationSettlesControlFlow then g
    else g.chainPendingReplacement .finishResolutionChoice
  else if g.pending != .none then g
  else
    let alreadyGrants : Bool :=
      g.pending == .none && g.afterRandom == .none && g.anyContinuationGrantsPriority
    let g := g.drainPendingContinuations
    if g.over then
      let g :=
        if g.proposedSpell.any (fun prop =>
            !g.stillInGame prop.caster || (g.findObject? prop.spellId).isNone) then
          (if g.pending == .none then g else g.change (.pending .none)).reverseProposedSpell
            (resumeContinuation := true) (alwaysGrantPriority := true)
        else g
      (g.popEmptyContinuationFrames).completeActiveResolutions
    else if let .chooseReplacement .. := g.pending then
      if g.anyContinuationSettlesControlFlow then g
      else g.chainPendingReplacement .finishResolutionChoice
    else if g.pending != .none || g.afterRandom != .none then g
    else
      let g := g.popEmptyContinuationFrames
      if g.proposedSpell.any (fun prop =>
          !g.stillInGame prop.caster || (g.findObject? prop.spellId).isNone) then
        let g :=
          (if g.pending == .none then g else g.change (.pending .none)).reverseProposedSpell
            (resumeContinuation := true) (alwaysGrantPriority := true)
        if !g.over && g.pending == .none && g.afterRandom == .none &&
            g.proposedSpell.isNone &&
            (g.pendingMayCastFromExile.isSome || g.pendingFreeCopies.isSome) then
          g.finishResolutionChoice
        else if !g.over && g.pending == .none && g.continuations.isEmpty &&
            g.triggerNeedingTargets.isSome then
          g.promptTriggerTargetsIfNeeded
        else g
      else if g.proposedSpell.isSome then
        if g.pending == .none then g else g.change (.pending .none)
      else if g.pendingMayCastFromExile.isSome || g.pendingFreeCopies.isSome then
        let g := g.reopenDeferredExileCasts
        if let .chooseReplacement .. := g.pending then
          if g.anyContinuationSettlesControlFlow then g
          else g.chainPendingReplacement .finishResolutionChoice
        else if g.pending != .none then g
        else if g.currentInterpWait?.isSome || g.pendingReplacement.isSome ||
            !g.outerPendingReplacements.isEmpty then
          g.finishResolutionChoice
        else if g.triggerNeedingTargets.isSome then
          (g.popEmptyContinuationFrames).promptTriggerTargetsIfNeeded
        else if alreadyGrants then g.popEmptyContinuationFrames
        else
          let prio := g.pendingPriority.getD g.activePlayer
          (g.popEmptyContinuationFrames).receivePriority prio
      else if g.triggerNeedingTargets.isSome then
        g.promptTriggerTargetsIfNeeded
      else if alreadyGrants then g
      else
        let prio := g.pendingPriority.getD g.activePlayer
        g.receivePriority prio

/-- Clear `.payWard` and drain any queued `pendingReplacement` /
`outerPendingReplacements` continuations before priority or trigger targets. -/
partial def finishWardAndDrain (g : Game)
    (outerCont? : Option PendingReplacement := none) : Game :=
  let g := g.reattachOuterCont outerCont?
  let g := g.afterWardResolved
  let g := g.drainPendingContinuations
  if g.over then g.completeActiveResolutions
  else if g.pending == .none && g.afterRandom == .none then g.popEmptyContinuationFrames
  else g

/-- Finish an idle-priority or combat-assignment concession after any CR 616.1 /
704.5j SBA pause inside `playerLeavesGame` or `checkSBA` completes (CR 800.4a /
117.3). -/
partial def finishConcedePriority (g : Game) (wasIdlePriority : Bool)
    (savedPendingPrio : Option PlayerId)
    (wasAssigningCombatDamage : Option Bool := none)
    (savedPending : Option Pending := none)
    (popOuter : Bool := false)
    (runSba : Bool := false)
    (departed : Array PlayerId := #[])
    (rewindProposal : Option Bool := none)
    (fromEventIdx? : Option Nat := none) : Game :=
  let finishFromIdx := fromEventIdx?.getD g.events.size
  let preFinish :=
    match fromEventIdx? with
    | some idx => g.mkHistoricalGameAt idx
    | none => g
  let g := g.popEmptyContinuationFrames
  let (g, popOuter) :=
    if runSba && !g.over then (g, popOuter)
    else g.flushDismissedPausedBatch savedPending popOuter (hasDeferredRewind := rewindProposal.isSome)
  let (g, savedPending, popOuter, rewindProposal) :=
    match rewindProposal with
    | some hadPreBodyCont =>
      if !g.sbaPaused && (g.currentBatch.isNone || g.isPreProposalCheckpointBatch) then
        let (g', s', po') := g.applyDeferredProposalRewind savedPending popOuter departed hadPreBodyCont
        (g', s', po', none)
      else
        (g, savedPending, popOuter, rewindProposal)
    | none =>
      (g, savedPending, popOuter, none)
  let (g, _, savedPending, popOuter, departed, rewindProposal, sbaFromIdx?) :=
    if runSba && !g.over then
      g.checkSBACountedWithLeavesCoreWithIdx savedPending popOuter departed rewindProposal
        (deferRestore := true) (fromEventIdx? := some finishFromIdx)
    else
      (g, false, savedPending, popOuter, departed, rewindProposal, some finishFromIdx)
  let effFinishFromIdx :=
    match sbaFromIdx? with
    | some idx => min finishFromIdx idx
    | none => finishFromIdx
  let preFinish :=
    if effFinishFromIdx < finishFromIdx then g.mkHistoricalGameAt effFinishFromIdx
    else preFinish
  if g.over then g.completeActiveResolutions
  else if g.sbaPaused then
    g.chainPendingReplacement
      (.finishConcede wasIdlePriority savedPendingPrio wasAssigningCombatDamage
        savedPending popOuter departed rewindProposal (some effFinishFromIdx))
  else
    let g := emitExpiredPlayFromExileLogs preFinish g effFinishFromIdx
    let g :=
      match savedPending with
      | some sp =>
        if g.pending == .none then
          g.resumePendingReplacement
            (.restorePending sp popOuter (departed := departed) (rewindProposal := rewindProposal))
        else g
      | none =>
        if rewindProposal.isSome then
          if g.pending == .none then
            g.resumePendingReplacement
              (.restorePending .none popOuter (departed := departed) (rewindProposal := rewindProposal))
          else g
        else if popOuter then
          match g.outerPendingReplacements.back? with
          | some popped => (g.change .popOuterPendingReplacement).chainPendingReplacement popped
          | none => g
        else g
    if g.pending != .none then g
    else if let some fa := wasAssigningCombatDamage then
      if fa then g.beginCombatDamageAssignment else g.continueBlockerCombatAssignment
    else
      let g := g.popEmptyContinuationFrames
      if !g.continuations.isEmpty || g.pendingReplacement.isSome ||
          !g.outerPendingReplacements.isEmpty ||
          g.currentInterpWait?.isSome ||
          (g.proposedSpell.isNone &&
            (g.pendingMayCastFromExile.isSome || g.pendingFreeCopies.isSome)) then
        g.finishResolutionChoice
      else if wasIdlePriority && g.playersReceivePriority && !g.hasWaitingTriggers &&
          g.consecutivePasses ≥ g.livingPlayers.size then
        let g := g.change (.consecutivePasses 0)
        if !g.stack.isEmpty then
          let g := g.resolveTop
          if let .chooseReplacement .. := g.pending then
            if g.anyContinuationSettlesControlFlow then g
            else g.chainPendingReplacement (.receivePriority g.activePlayer)
          else if g.pending != .none || g.afterRandom != .none then g
          else g.receivePriority g.activePlayer
        else
          g.advanceStep
      else if g.playersReceivePriority then
        let rawPrio := (savedPendingPrio.orElse (fun _ => g.pendingPriority)).getD g.priority
        let nextP := if g.stillInGame rawPrio then rawPrio else g.nextLiving rawPrio
        let g :=
          if g.triggerNeedingTargets.isSome then
            let target := g.priorityInstead nextP
            if g.pendingPriority == some target then g
            else g.change (.pendingPriority (some target))
          else g
        let g := g.promptTriggerTargetsIfNeeded
        if g.pending != .none then g
        else g.receivePriority nextP
      else g

/-- Pause-safe departure loop for conceding player(s) `remaining` (including
teammates under CR 810.8a), deferring restoration of any non-departed player's
`savedPending` / `popOuter` until all departing teammates and post-departure
SBAs finish (CR 608.2c / 704.3–4 / 800.4a,f / 810.8a). -/
partial def concedePlayersLoop (g : Game) (remaining : Array PlayerId)
    (wasPregame midResolutionOrBatch wasIdlePriority : Bool)
    (savedPendingPrio : Option PlayerId)
    (wasAssigningCombatDamage : Option Bool := none)
    (savedIn : Option Pending := none)
    (popOuterIn : Bool := false)
    (departedIn : Array PlayerId := #[])
    (rewindProposalIn : Option Bool := none)
    (fromEventIdx? : Option Nat := none) : Game := Id.run do
  if g.over then
    return g.completeActiveResolutions
  let concedeFromIdx := fromEventIdx?.getD g.events.size
  let preConcede :=
    match fromEventIdx? with
    | some idx => g.mkHistoricalGameAt idx
    | none => g
  let mut g := g
  let mut saved? := savedIn
  let mut popOuter := popOuterIn
  let mut departed := departedIn
  let mut rewindProposal := rewindProposalIn
  for i in [0:remaining.size] do
    if g.over then
      return g.completeActiveResolutions
    let pid := remaining[i]!
    if !(g.player pid).leftTheGame then
      let wasSbaPaused := g.sbaPaused
      let (gf, pof) := g.flushDismissedPausedBatch saved? popOuter (hasDeferredRewind := rewindProposal.isSome)
      g := gf
      popOuter := pof
      if g.over then
        return g.completeActiveResolutions
      if !wasSbaPaused then
        match g.pending with
        | .chooseReplacement r _ | .chooseLegend r _ _ =>
          let remHere := remaining.extract i remaining.size
          if !remHere.contains r then
            return g.chainPendingReplacement
              (.concedePlayersLoop remHere wasPregame midResolutionOrBatch wasIdlePriority
                savedPendingPrio wasAssigningCombatDamage saved? popOuter departed rewindProposal
                (some concedeFromIdx))
        | _ => pure ()
      if let some hadPreBodyCont := rewindProposal then
        if !g.sbaPaused && (g.currentBatch.isNone || g.isPreProposalCheckpointBatch) then
          let (g', s', po') := g.applyDeferredProposalRewind saved? popOuter departed hadPreBodyCont
          g := g'
          saved? := s'
          popOuter := po'
          rewindProposal := none
          match g.pending with
          | .chooseReplacement r _ | .chooseLegend r _ _ =>
            let remHere := remaining.extract i remaining.size
            if !remHere.contains r then
              return g.chainPendingReplacement
                (.concedePlayersLoop remHere wasPregame midResolutionOrBatch wasIdlePriority
                  savedPendingPrio wasAssigningCombatDamage saved? popOuter departed none
                  (some concedeFromIdx))
          | _ => pure ()
      let prePopCont? : Option (Option PendingReplacement) :=
        if popOuter then some g.pendingReplacement else none
      if popOuter then
        if let some popped := g.outerPendingReplacements.back? then
          g := (g.change .popOuterPendingReplacement).chainPendingReplacement popped
        popOuter := false
      let pendingIn := if g.pending == .none then saved? else none
      if pendingIn.isSome then
        saved? := none
      else if g.isProposalAbortedByLeave pid then
        if let some prop := g.proposedSpell then
          if saved?.any (isProposalPromptFor prop.caster) then
            saved? := none
      let (g', newlySaved?, po, rw) :=
        g.playerLeavesGameCore pid (deferRestore := true) (pendingIn := pendingIn)
          (departedIn := departed) (rewindProposalIn := rewindProposal)
          (prePopCont? := prePopCont?) (deferPlayFromExileLogs := true)
      g := g'
      departed := if departed.contains pid then departed else departed.push pid
      popOuter := popOuter || po
      match saved?, newlySaved? with
      | none, s => saved? := s
      | some .none, s => saved? := s.orElse (fun _ => some .none)
      | some oldP, some newP =>
        if newP != .none then
          let popped? : Option PendingReplacement :=
            if popOuter then g.outerPendingReplacements.back? else none
          if popped?.isSome then
            g := g.change .popOuterPendingReplacement
          let restoreOld : PendingReplacement := .restorePending oldP false (departed := departed)
          let outer := g.chainRestoreAfterOpenBatch restoreOld popped?
          if g.continuations.isEmpty then
            g := g.change (.pushContinuationFrame {})
          g := g.change (.pushOuterPendingReplacement outer)
          popOuter := true
          saved? := some newP
      | some _, none => pure ()
      rewindProposal :=
        match rewindProposal, rw with
        | some a, some _ => some a
        | some a, none =>
          if g.proposedSpell.isSome && g.proposalCheckpoint.isSome then some a else none
        | none, some b => some b
        | none, none => none
      let rem := remaining.extract (i + 1) remaining.size
      match g.pending with
      | .chooseReplacement r _ | .chooseLegend r _ _ =>
        if !rem.contains r then
          let alreadySettles := g.anyContinuationSettlesControlFlow
          if !rem.isEmpty || wasPregame || !midResolutionOrBatch || !alreadySettles ||
              wasAssigningCombatDamage.isSome || saved?.isSome || popOuter ||
              rewindProposal.isSome then
            return g.chainPendingReplacement
              (.concedePlayersLoop rem wasPregame midResolutionOrBatch wasIdlePriority
                savedPendingPrio wasAssigningCombatDamage saved? popOuter departed rewindProposal
                (some concedeFromIdx))
          else
            return emitExpiredPlayFromExileLogs preConcede g concedeFromIdx
      | _ => pure ()
  let (gf, pof) := g.flushDismissedPausedBatch saved? popOuter (hasDeferredRewind := rewindProposal.isSome)
  g := gf
  popOuter := pof
  if g.over then
    return g.completeActiveResolutions
  if let some hadPreBodyCont := rewindProposal then
    if !g.sbaPaused && (g.currentBatch.isNone || g.isPreProposalCheckpointBatch) then
      let (g', s', po') := g.applyDeferredProposalRewind saved? popOuter departed hadPreBodyCont
      g := g'
      saved? := s'
      popOuter := po'
      rewindProposal := none
  if saved?.isNone && !g.sbaPaused && g.pending != .none then
    saved? := some g.pending
    g := g.change (.pending .none)
  if wasPregame then
    if g.sbaPaused then
      return g.chainPendingReplacement
        (.concedePlayersLoop #[] true midResolutionOrBatch wasIdlePriority
          savedPendingPrio wasAssigningCombatDamage saved? popOuter departed rewindProposal
          (some concedeFromIdx))
    g := emitExpiredPlayFromExileLogs preConcede g concedeFromIdx
    g :=
      match saved? with
      | some sp =>
        if g.pending == .none then
          g.resumePendingReplacement
            (.restorePending sp popOuter (departed := departed) (rewindProposal := rewindProposal))
        else g
      | none =>
        if rewindProposal.isSome then
          if g.pending == .none then
            g.resumePendingReplacement
              (.restorePending .none popOuter (departed := departed) (rewindProposal := rewindProposal))
          else g
        else if popOuter then
          match g.outerPendingReplacements.back? with
          | some popped => (g.change .popOuterPendingReplacement).chainPendingReplacement popped
          | none => g
        else g
    if g.pending != .none then return g
    else if g.pregameRandom != .none then return finishAfterRandom g true
    else if !g.mulliganToDeclare.isEmpty then return g.promptMulligan g.mulliganToDeclare[0]!
    else if !g.willMulligan.isEmpty then return g.resolveDeclaredMulligans
    else if !g.mulliganToBottom.isEmpty then return g.promptBottom g.mulliganToBottom[0]!
    else if g.awaitingOpeningBegin then return g.continueOpeningBegin #[]
    else return g.beginMulliganRound
  else if midResolutionOrBatch then
    if g.sbaPaused then
      let alreadySettles := g.anyContinuationSettlesControlFlow
      if !alreadySettles || wasAssigningCombatDamage.isSome || saved?.isSome || popOuter ||
          rewindProposal.isSome then
        return g.chainPendingReplacement
          (.concedePlayersLoop #[] false true wasIdlePriority
            savedPendingPrio wasAssigningCombatDamage saved? popOuter departed rewindProposal
            (some concedeFromIdx))
      else
        return emitExpiredPlayFromExileLogs preConcede g concedeFromIdx
    else
      g := emitExpiredPlayFromExileLogs preConcede g concedeFromIdx
      g :=
        match saved? with
        | some sp =>
          if g.pending == .none then
            g.resumePendingReplacement
              (.restorePending sp popOuter (departed := departed) (rewindProposal := rewindProposal))
          else g
        | none =>
          if rewindProposal.isSome then
            if g.pending == .none then
              g.resumePendingReplacement
                (.restorePending .none popOuter (departed := departed) (rewindProposal := rewindProposal))
            else g
          else if popOuter then
            match g.outerPendingReplacements.back? with
            | some popped => (g.change .popOuterPendingReplacement).chainPendingReplacement popped
            | none => g
          else g
      if g.pending != .none then return g
      else
        g := g.popEmptyContinuationFrames
        let runSba :=
          g.continuations.isEmpty && g.currentBatch.isNone &&
            g.pendingReplacement.isNone && g.outerPendingReplacements.isEmpty &&
            g.currentInterpWait?.isNone
        return g.finishConcedePriority wasIdlePriority savedPendingPrio wasAssigningCombatDamage
          none false (runSba := runSba) (departed := departed)
          (fromEventIdx? := some concedeFromIdx)
  else if g.sbaPaused then
    return g.chainPendingReplacement
      (.finishConcede wasIdlePriority savedPendingPrio wasAssigningCombatDamage
        saved? popOuter departed rewindProposal (some concedeFromIdx))
  else
    return g.finishConcedePriority wasIdlePriority savedPendingPrio wasAssigningCombatDamage
      saved? popOuter (runSba := true) (departed := departed) (rewindProposal := rewindProposal)
      (fromEventIdx? := some concedeFromIdx)

/-- Whether `curPr` (or a continuation delegated by `.leavePlayersWhoLost` /
`.restorePending` without `rewindProposal`) can legally reverse an active
proposal under CR 733.1. -/
private partial def stepCanReverseProposal (origPr : PendingReplacement) (gCur : Game)
    (outerDepth : Nat) (curPr : PendingReplacement) (fuel : Nat := 16) : Bool × Nat :=
  if fuel == 0 then (false, outerDepth)
  else
    let fuel' := fuel - 1
    match curPr with
    | .seq a b =>
      let (canA, depthAfterA) := stepCanReverseProposal origPr gCur outerDepth a fuel'
      if canA then (true, depthAfterA)
      else stepCanReverseProposal origPr gCur depthAfterA b fuel'
    | .leavePlayersWhoLost savedPending popOuter departed rewindProposal fromEventIdx? =>
      let gL := probeGameForPendingReplacement gCur
      match probeLeavePlayersWhoLost gL false savedPending popOuter departed rewindProposal fromEventIdx? with
      | .paused _ _ _ => (false, outerDepth)
      | .delegate g' _ nextPr =>
        stepCanReverseProposal origPr g' g'.outerPendingReplacements.size nextPr fuel'
    | .restorePending (.resolutionChoice _ (.costPicks ..)) popOuter _ _ rewindProposal
    | .restorePending (.resolutionChoice _ (.crew ..)) popOuter _ _ rewindProposal
    | .restorePending (.resolutionChoice _ (.zemoBoastExile ..)) popOuter _ _ rewindProposal
    | .restorePending (.chooseTeamworkCreatures ..) popOuter _ _ rewindProposal
    | .restorePending (.sacrificePermanent ..) popOuter _ _ rewindProposal
    | .restorePending (.discardForAdditionalCost ..) popOuter _ _ rewindProposal
    | .restorePending (.activateManaAbilities ..) popOuter _ _ rewindProposal
    | .restorePending (.chooseX ..) popOuter _ _ rewindProposal
    | .restorePending (.chooseAdditionalCost ..) popOuter _ _ rewindProposal
    | .restorePending (.chooseKicker ..) popOuter _ _ rewindProposal
    | .restorePending (.chooseGift ..) popOuter _ _ rewindProposal
    | .restorePending (.chooseTeamwork ..) popOuter _ _ rewindProposal
    | .restorePending (.chooseMode ..) popOuter _ _ rewindProposal
    | .restorePending (.chooseTargets ..) popOuter _ _ rewindProposal =>
      (rewindProposal.isNone, if popOuter then outerDepth - 1 else outerDepth)
    | .restorePending _ popOuter _ _ rewindProposal =>
      if !popOuter then (false, outerDepth)
      else if outerDepth == 0 then (false, 0)
      else
        let nextDepth := outerDepth - 1
        if rewindProposal.isSome then (false, nextDepth)
        else
          let outer := gCur.outerPendingReplacements[nextDepth]!
          if outer == origPr || outer == curPr then (false, nextDepth)
          else stepCanReverseProposal origPr gCur nextDepth outer fuel'
    | .finishPostStep (.resumeProposalCostAfterLeave ..)
    | .finishPostStep (.resumeChooseModeAfterLeave ..)
    | .finishPostStep (.resumeChooseTargetsAfterLeave ..)
    | .payCostPickItems ..
    | .finishActivationExtraCosts ..
    | .finishBecomeCast ..
    | .finishTurnFaceUp ..
    | .finishBecomeActivated ..
    | .finishPostLoyaltyActivated ..
    | .completeActivation ..
    | .finishProposedSpellCosts .. => (true, outerDepth)
    | _ => (false, outerDepth)

/-- Resume the rules event that paused on `Pending.chooseReplacement` (CR 616.1). -/
@[export mtg_game_resume_pending_replacement]
partial def resumePendingReplacement (g : Game) (pr : PendingReplacement)
    (followedByFinishChoice : Bool := false) : Game :=
  g.resumePendingReplacementCore pr (followedByFinishChoice := followedByFinishChoice)

/-- Internal core for `resumePendingReplacement` carrying `hasFollowingSeq` so
steps inside `.seq first rest` know when an un-queued `rest` waits after them. -/
partial def resumePendingReplacementCore (g : Game) (pr : PendingReplacement)
    (followedByFinishChoice : Bool := false) (hasFollowingSeq : Bool := false)
    (followedByNonProposalPriorityGrant : Bool := false)
    (followedByExplicitPriority? : Option PlayerId := none) : Game :=
  match pr with
  | .seq first rest =>
    let checkReversal : Bool :=
      !g.hasActiveManaProposalCheckpoint && g.proposedSpell.isSome &&
        (stepCanReverseProposal pr g g.outerPendingReplacements.size first 16).1
    let spellId? := g.proposedSpell.map (·.spellId)
    let wasTurnFaceUp := g.proposedSpell.any (·.kind == .turnFaceUp)
    let g0 := g
    let gProbe := probeGameForPendingReplacement g0
    let resFirst :=
      advanceProbeOnResumeCore gProbe false first followedByFinishChoice followedByExplicitPriority?
    let gBaseRest :=
      if resFirst.reversedProposal then resFirst.preReverseGame?.getD gProbe
      else resFirst.game
    let gProbeRest :=
      if gBaseRest.proposedSpell.isSome then gBaseRest.change (.proposedSpell none)
      else gBaseRest
    let restQueued := if resFirst.reversedProposal then false else resFirst.hasQueuedPending
    let restGrantLeaf? :=
      firstPriorityGrantLeaf? gProbeRest restQueued rest
        followedByFinishChoice followedByExplicitPriority? followedByNonProposalPriorityGrant
    let (nextFollowedByFinishChoice, nextFollowedByExplicit?) :=
      match restGrantLeaf? with
      | some (leaf, explicit?) =>
        if leaf.endsWithFinishResolutionChoice then (true, explicit?)
        else if explicit?.isSome then (false, explicit?)
        else (followedByFinishChoice, followedByExplicitPriority?)
      | none => (followedByFinishChoice || rest.endsWithFinishResolutionChoice, followedByExplicitPriority?)
    let nextFollowedByNonProposal :=
      followedByNonProposalPriorityGrant || rest.endsWithNonProposalPriorityGrant ||
        restGrantLeaf?.any (fun (leaf, _) => isNonProposalGrantLeaf leaf)
    let g := g.resumePendingReplacementCore first
      (followedByFinishChoice := nextFollowedByFinishChoice)
      (hasFollowingSeq := hasFollowingSeq || !rest.isPurePostLog)
      (followedByNonProposalPriorityGrant := nextFollowedByNonProposal)
      (followedByExplicitPriority? := nextFollowedByExplicit?)
    let newlyDeparted :=
      g.players.foldl (fun acc pl =>
        if pl.leftTheGame && !(g0.player pl.id).leftTheGame && !acc.contains pl.id then
          acc.push pl.id
        else acc) first.collectDeparted
    let rest :=
      if newlyDeparted.isEmpty then rest
      else PendingReplacement.appendDepartedMany newlyDeparted rest
    let g :=
      if newlyDeparted.isEmpty then g
      else g.appendDepartedManyToContinuations newlyDeparted
    let completedOnStackOrBf :=
      spellId?.any fun sid =>
        (g.findObject? sid).any fun o =>
          if wasTurnFaceUp then o.isOnBattlefield && !o.status.faceDown
          else o.zone == .stack
    let reversed :=
      checkReversal && g.proposedSpell.isNone && !completedOnStackOrBf
    if reversed then g
    else if g.over && !rest.hasCheckpointReplay then g
    else if g.pending != .none || (g0.afterRandom == .none && g.afterRandom != .none) then
      g.chainPendingReplacement rest
    else if g0.pendingReplacement.isNone then
      match g.pendingReplacement with
      | some inner =>
        let g := (g.change (.pendingReplacement none)).popEmptyTopContinuationFrames
        g.resumePendingReplacementCore (.seq inner rest)
          (followedByFinishChoice := followedByFinishChoice)
          (hasFollowingSeq := hasFollowingSeq)
          (followedByNonProposalPriorityGrant := followedByNonProposalPriorityGrant)
          (followedByExplicitPriority? := followedByExplicitPriority?)
      | none =>
        g.resumePendingReplacementCore rest
          (followedByFinishChoice := followedByFinishChoice)
          (hasFollowingSeq := hasFollowingSeq)
          (followedByNonProposalPriorityGrant := followedByNonProposalPriorityGrant)
          (followedByExplicitPriority? := followedByExplicitPriority?)
    else
      g.resumePendingReplacementCore rest
        (followedByFinishChoice := followedByFinishChoice)
        (hasFollowingSeq := hasFollowingSeq)
        (followedByNonProposalPriorityGrant := followedByNonProposalPriorityGrant)
        (followedByExplicitPriority? := followedByExplicitPriority?)
  | .shuffleThen p onDone =>
    g.shuffleThen p onDone
  | .dealDamageToPlayer p n source unpreventable cause suppressLifelink =>
    let srcObj := g.damageSourceObjFromSnapshot? source
    g.dealDamageToPlayer p (Int.ofNat n) (preventable := !unpreventable)
      (source := srcObj) (sourceSnap := source) (cause := cause)
      (suppressLifelink := suppressLifelink)
  | .dealDamageToPlayers players n source cause startEventIdx suppressLifelink =>
    let srcObj := g.damageSourceObjFromSnapshot? source
    g.dealDamageToPlayers players (Int.ofNat n) (source := srcObj) (sourceSnap := source)
      (cause := cause) (startEventIdx := startEventIdx) (suppressLifelink := suppressLifelink)
  | .dealDamageFrom sourceName source targetId n deathtouch cause suppressLifelink =>
    match g.findObject? targetId with
    | some tgt =>
      let srcObj? := g.damageSourceObjFromSnapshot? source
      g.dealDamageFrom sourceName tgt (Int.ofNat n) (deathtouch := deathtouch)
        (source := srcObj?) (sourceSnap := source) (cause := cause)
        (suppressLifelink := suppressLifelink)
    | none => g
  | .dealFightDamage sourceId targetId cause amount =>
    match g.findObject? sourceId, g.findObject? targetId with
    | some src, some dest =>
      if src.isOnBattlefield && dest.isOnBattlefield && g.isCreature src && g.isCreature dest then
        g.dealFightDamage src dest (cause := cause) (amount := amount)
      else g
    | _, _ => g
  | .dealDamageToPermanent targetId n source cause suppressLifelink =>
    match g.findObject? targetId with
    | some tgt =>
      g.dealDamageToPermanent tgt (Int.ofNat n) (source := source) (cause := cause)
        (suppressLifelink := suppressLifelink)
    | none => g
  | .markDamageOn targetId n msg deathtouch source combat unpreventable cause =>
    match g.findObject? targetId with
    | some tgt =>
      let srcObj := g.damageSourceObjFromSnapshot? source
      g.markDamageOn tgt (Int.ofNat n) msg (deathtouch := deathtouch) (combat := combat)
        (source := source) (sourceObj := srcObj) (unpreventable := unpreventable)
        (cause := cause)
    | none => g
  | .dealAssignedCombatDamage startIdx =>
    g.dealAssignedCombatDamage startIdx
  | .gainLife p n cause =>
    g.gainLife p n (cause := cause)
  | .addPlusOnePlusOneTo targetId n entersWith byPlayer cause =>
    match g.findObject? targetId with
    | some tgt =>
      g.addPlusOnePlusOneTo tgt n (entersWith := entersWith) (byPlayer := byPlayer)
        (cause := cause)
    | none => g
  | .addCounters targetId kind n entersWith byPlayer cause =>
    match g.findObject? targetId with
    | some tgt =>
      g.addCounters tgt kind n (entersWith := entersWith) (byPlayer := byPlayer)
        (cause := cause)
    | none => g
  | .recordPutCounters targetId kind n byPlayer cause =>
    g.recordPutCounters targetId kind n byPlayer (cause := cause)
  | .putCountersDeferredLog targetId kind n byPlayer logKind cause =>
    g.putCountersDeferredLog targetId kind n byPlayer logKind (cause := cause)
  | .logPutCounterDelta targetId kind before logKind =>
    g.logPutCounterDelta targetId kind before logKind
  | .move id dest controller verb actor faceDown tapped
      attacking attackingTarget transformed returnedAsArtifact onlyFoodArtifact
      extraEntersWith libraryPosition fromStackTime applyHope preBattlefield
      isCopy overridePrinted adventurerCard summoningSick attachedTo enterMods cause
      lkiController? skipUnattachIds deferPlayFromExileLogs =>
    (g.move id dest controller (tapped := tapped) (summoningSick := summoningSick)
      (attachedTo := attachedTo) (applyHope := applyHope)
      (attacking := attacking) (attackingTarget := attackingTarget)
      (returnedAsArtifact := returnedAsArtifact) (onlyFoodArtifact := onlyFoodArtifact)
      (nightBack := transformed) (extraEntersWith := extraEntersWith)
      (verb := verb) (actor := actor) (libraryPosition := libraryPosition)
      (preBattlefield := preBattlefield) (isCopy := isCopy)
      (overridePrinted := overridePrinted) (adventurerCard := adventurerCard)
      (faceDown? := some faceDown) (fromStackTime? := some fromStackTime)
      (enterMods := enterMods) (cause := cause)
      (lkiController? := lkiController?) (skipUnattachIds := skipUnattachIds)
      (deferPlayFromExileLogs := deferPlayFromExileLogs)).1
  | .moveSimultaneousToGraveyard ids preBattlefield cause deferPlayFromExileLogs fromEventIdx? =>
    g.moveSimultaneousToGraveyard ids (preBattlefield := preBattlefield) (cause := cause)
      (deferPlayFromExileLogs := deferPlayFromExileLogs) (fromEventIdx? := fromEventIdx?)
  | .destroyPermanent targetId cause preBattlefield reason deferPlayFromExileLogs =>
    match g.findObject? targetId with
    | some tgt =>
      g.destroyPermanent tgt (preBattlefield := preBattlefield) (cause := cause) (reason := reason)
        (deferPlayFromExileLogs := deferPlayFromExileLogs)
    | none => g
  | .createToken controller card tapped attacking attackingTarget applyFoodBonus extraCounters recordRecent cause count =>
    (g.createToken controller card (tapped := tapped) (attacking := attacking)
      (attackingTarget := attackingTarget) (applyFoodBonus := applyFoodBonus)
      (extraCounters := extraCounters) (recordRecent := recordRecent)
      (cause := cause) (count := count)).1
  | .createTokenBatches batches attacking attackingTarget extraCounters recordRecent cause =>
    (g.createTokenBatches batches (attacking := attacking) (attackingTarget := attackingTarget)
      (extraCounters := extraCounters) (recordRecent := recordRecent) (cause := cause)).1
  | .createTreasureTokens controller n tapped cause =>
    g.createTreasureTokens controller n (tapped := tapped) (cause := cause)
  | .createKindTokens controller kind n tapped attacking attackingTarget resetRecent cause copyEnv =>
    g.createKindTokens controller kind n (tapped := tapped) (attacking := attacking)
      (attackingTarget := attackingTarget) (resetRecent := resetRecent) (cause := cause)
      (copyEnv := copyEnv)
  | .createAndMarkTokensAttacking controller kind n tapped holds sourceId cause copyEnv =>
    g.createAndMarkTokensAttacking controller kind n tapped holds (sourceId := sourceId)
      (cause := cause) (copyEnv := copyEnv)
  | .commitEnteringAttackItems chosen cause resetRecent postEntries preBattlefield =>
    g.commitEnteringAttackItems chosen (cause := cause) (resetRecent := resetRecent)
      (postEntries := postEntries) (preBattlefield := preBattlefield)
  | .finishEnteringAttackCards postEntries cause =>
    g.finishEnteringAttackCards postEntries (cause := cause)
  | .finishEnteringAttackCard newId? effectController cardName mods logKind cause =>
    match newId?.bind (fun id => g.followMovedToZone? id (· == .battlefield)) with
    | some entered =>
      g.finishEnteringAttackCard entered.id effectController cardName mods logKind (cause := cause)
    | none => g
  | .afterLastPermanentEnters fromId isPlayLand attachedToHost =>
    match fromId.bind (fun id => g.followMovedToZone? id (· == .battlefield)) with
    | some entered =>
      if isPlayLand then
        let g := if entered.status.tapped then g.logMsg s!"{g.name entered} enters tapped" else g
        g.afterLandEnters entered
      else
        let g :=
          match (attachedToHost <|> entered.attachedTo).bind g.findObject? with
          | some host => g.logMsg s!"{g.name entered} enters the battlefield attached to {g.name host}"
          | none => g.logMsg s!"{g.name entered} enters the battlefield"
        g.afterPermanentEnters entered
    | none => g
  | .addExtraCombatDamageStep =>
    g.record (GameEvent.extraStepAdded g.turnNumber .combatDamage .afterCurrent
      (cause := .gameRule .stepAdvance))
  | .finishResolutionChoice =>
    g.finishResolutionChoice
  | .draw p n cause =>
    g.draw p n (cause := cause)
  | .drawOne p applied drawStepFirst cause =>
    g.drawOneWithReplacements p (applied := applied)
      (firstOfYourDrawStep? := some drawStepFirst) (cause := cause)
  | .drawSubDraws p remaining applied cause =>
    g.drawSubDraws p remaining applied (cause := cause)
  | .connive controller sourceId =>
    g.applyConnive controller sourceId
  | .finishSbaSweep moves preBattlefield stage pwMoves sagaMoves tokensOutsideBf copiesOutside illegalAuras illegalEquips illegalCreatureAtts legendGroups deferPlayFromExileLogs =>
    (g.finishSbaSweep moves preBattlefield stage pwMoves sagaMoves tokensOutsideBf
      copiesOutside illegalAuras illegalEquips illegalCreatureAtts legendGroups
      (deferPlayFromExileLogs := deferPlayFromExileLogs)).1
  | .untapPermanent targetId duringUntapStep logUntap cause =>
    match g.findObject? targetId with
    | some tgt =>
      if tgt.isOnBattlefield && !duringUntapStep && logUntap then
        if g.hostCantBecomeUntapped tgt then
          g.logMsg s!"{g.name tgt} can't become untapped"
        else if !tgt.status.tapped then
          g.logMsg s!"{g.name tgt} is already untapped"
        else
          g.untapPermanent tgt (duringUntapStep := duringUntapStep)
            (logUntap := logUntap) (cause := cause)
      else
        g.untapPermanent tgt (duringUntapStep := duringUntapStep)
          (logUntap := logUntap) (cause := cause)
    | none => g
  | .untapStepPermanents ids =>
    g.untapStepPermanents ids
  | .moveCardsToGraveyardLoop ids cause fromEventIdx? =>
    g.moveCardsToGraveyardLoop ids cause (fromEventIdx? := fromEventIdx?)
  | .placeSearchedGraveyardLoop ids cause pendingLog =>
    g.placeSearchedGraveyardLoop ids cause pendingLog
  | .finishConcede wasIdlePriority savedPendingPrio wasAssigningCombatDamage savedPending popOuter departed rewindProposal fromEventIdx? =>
    g.finishConcedePriority wasIdlePriority savedPendingPrio wasAssigningCombatDamage
      savedPending popOuter (runSba := true) (departed := departed) (rewindProposal := rewindProposal)
      (fromEventIdx? := fromEventIdx?)
  | .concedePlayersLoop remaining wasPregame midResolutionOrBatch wasIdlePriority savedPendingPrio wasAssigningCombatDamage savedPending popOuter departed rewindProposal fromEventIdx? =>
    g.concedePlayersLoop remaining wasPregame midResolutionOrBatch wasIdlePriority
      savedPendingPrio wasAssigningCombatDamage savedPending popOuter
      (departedIn := departed) (rewindProposalIn := rewindProposal)
      (fromEventIdx? := fromEventIdx?)
  | .afterWardResolved =>
    g.afterWardResolved
  | .addLoreCounters sagaId n cause =>
    match g.findObject? sagaId with
    | some saga => g.addLoreCounters saga n (cause := cause)
    | none => g
  | .addLoreAfterDrawStep sagaIds =>
    g.addLoreAfterDrawStepIds sagaIds
  | .copyNontokenCreatures controller snapshots cause =>
    g.copyNontokenCreaturesStep controller snapshots cause
  | .copyPermanentTokens controller card remaining cause priorRecentCount pushedFrame =>
    g.createPermanentCopyTokens controller card remaining cause (some priorRecentCount) pushedFrame
  | .finishArtifactCopyToken =>
    g.finishArtifactCopyTokens
  | .finishManaAbilityMountainTrigger player sourceId =>
    g.finishManaAbilityMountainTrigger player sourceId
  | .restorePending p popOuter promptLog departed rewindProposal => Id.run do
    let popped? : Option PendingReplacement :=
      if popOuter then g.outerPendingReplacements.back? else none
    let g := if popped?.isSome then g.change .popOuterPendingReplacement else g
    let g := g.popEmptyTopContinuationFrames
    let shouldSplitBatch : Bool :=
      g.openBatchAwaitedPausePrompt &&
        match rewindProposal with
        | some _ => !g.isPreProposalCheckpointBatch && !g.batchPausePromptValid p
        | none => g.pending == .none && g.batchPausePromptGoneOrInvalid p
    if shouldSplitBatch then
      if let some (curBid, _) := g.currentBatch then
        let fullCont? : Option PendingReplacement :=
          match g.pendingReplacement, popped? with
          | some prior, some popped => some (.seq prior popped)
          | some prior, none => some prior
          | none, some popped => some popped
          | none, none => none
        if let some (closePrefix, afterClose?) := fullCont?.bind (splitAfterCloseBatchFor? curBid) then
          let (g, splitCont) : Game × PendingReplacement :=
            match rewindProposal, afterClose? with
            | some _, some after =>
              let g := if g.continuations.isEmpty then g.change (.pushContinuationFrame {}) else g
              let g := g.change (.pushOuterPendingReplacement after)
              (g, .seq closePrefix (.restorePending p true promptLog departed rewindProposal))
            | _, some after =>
              let tailRestore : PendingReplacement :=
                .restorePending p false promptLog departed rewindProposal
              (g, .seq closePrefix (.seq tailRestore after))
            | _, none =>
              let tailRestore : PendingReplacement :=
                .restorePending p false promptLog departed rewindProposal
              (g, .seq closePrefix tailRestore)
          let g := if g.pendingReplacement.isSome then g.change (.pendingReplacement none) else g
          return g.resumePendingReplacementCore splitCont
            (followedByFinishChoice := followedByFinishChoice)
            (hasFollowingSeq := hasFollowingSeq)
            (followedByNonProposalPriorityGrant := followedByNonProposalPriorityGrant)
            (followedByExplicitPriority? := followedByExplicitPriority?)
    let validReplForDefer :=
      rewindProposal.isSome && g.batchPausePromptValid p
    let (g, popped?, p) : Game × Option PendingReplacement × Pending ← do
      if validReplForDefer then
        let (g, popped?) :=
          match g.currentBatch, popped? with
          | some (curBid, _), some popped =>
            match splitAfterCloseBatchFor? curBid popped with
            | some (closePrefix, some after) =>
              let g := if g.continuations.isEmpty then g.change (.pushContinuationFrame {}) else g
              let g := g.change (.pushOuterPendingReplacement after)
              let tailRewind : PendingReplacement :=
                .restorePending .none true none departed rewindProposal
              (g, some (.seq closePrefix tailRewind))
            | some (closePrefix, none) =>
              let tailRewind : PendingReplacement :=
                .restorePending .none false none departed rewindProposal
              (g, some (.seq closePrefix tailRewind))
            | none =>
              let tailRewind : PendingReplacement :=
                .restorePending .none false none departed rewindProposal
              (g, some (.seq popped tailRewind))
          | _, some popped =>
            let tailRewind : PendingReplacement :=
              .restorePending .none false none departed rewindProposal
            (g, some (.seq popped tailRewind))
          | _, none =>
            let tailRewind : PendingReplacement :=
              .restorePending .none false none departed rewindProposal
            (g, some tailRewind)
        pure (g, popped?, p)
      else
        match rewindProposal with
        | some hadPreBodyCont =>
          let (g, popped?) := g.rewindAbortedProposalOnLeave departed popped? hadPreBodyCont
          let g := g.popEmptyTopContinuationFrames
          if g.sbaPaused then
            let g :=
              if p != .none then
                g.chainPendingReplacement (.restorePending p false promptLog departed none)
              else g
            let g :=
              match popped? with
              | some popped => g.chainPendingReplacement popped
              | none => g
            return g
          let savedIn? := if p == .none then none else some p
          let (g, savedOut?, popped?) := g.stashPostRewindPending savedIn? popped? departed
          pure (g, popped?, savedOut?.getD Pending.none)
        | none =>
          pure (g, popped?, p)
    let openPromptWith (g : Game) (p' : Pending) : Game :=
      let g :=
        match popped? with
        | some popped => g.chainPendingReplacement popped
        | none => g
      let g :=
        if g.continuations.isEmpty &&
            (match p' with | .resolutionChoice .. | .chooseReplacement .. => true | _ => false) then
          g.change (.pushContinuationFrame {})
        else g
      let g := g.change (.pending p')
      match promptLog with
      | some msg => g.logMsg msg
      | none => g
    let openPrompt (g : Game) : Game := openPromptWith g p
    let resumePoppedIfNoPrompt (g : Game) : Game :=
      match popped? with
      | some popped =>
        let priorCont? := g.pendingReplacement
        let g := if priorCont?.isSome then g.change (.pendingReplacement none) else g
        let toRun :=
          match priorCont? with
          | some prior => .seq prior popped
          | none => popped
        g.resumePendingReplacementCore toRun
          (followedByFinishChoice := followedByFinishChoice)
          (hasFollowingSeq := hasFollowingSeq)
          (followedByNonProposalPriorityGrant := followedByNonProposalPriorityGrant)
          (followedByExplicitPriority? := followedByExplicitPriority?)
      | none => g
    let reverseOrResumePopped (g : Game) : Game :=
      if g.proposedSpell.isSome then
        let prep := prepareReverseInRestorePending g popped? departed
        let g := prep.g
        let caster := prep.caster
        let freshCont? := prep.freshCont?
        let hasBlockingPrompt := prep.hasBlockingPrompt
        let poppedTail? := prep.poppedTail?
        let restoreCkptPending? := prep.restoreCkptPending?
        let restored? := prep.restored?
        let ckptWasRandom := prep.ckptWasRandom
        let hadConsumedOrig := prep.hadConsumedOrig
        match poppedTail? with
        | some tailSeq =>
          let afterPrompt : PendingReplacement :=
            if followedByFinishChoice then tailSeq.ensureEndsWithFinishResolutionChoice
            else
              match followedByExplicitPriority? with
              | some prio => .seq tailSeq (.receivePriority prio)
              | none => tailSeq
          let toRun : PendingReplacement :=
            match freshCont? with
            | some fc => .seq fc afterPrompt
            | none => afterPrompt
          if hasBlockingPrompt then
            let g := if g.continuations.isEmpty then g.change (.pushContinuationFrame {}) else g
            if g.pendingReplacement == some toRun then g
            else g.change (.pendingReplacement (some toRun))
          else
            let g := if g.pendingReplacement.isSome then g.change (.pendingReplacement none) else g
            let g := g.popEmptyTopContinuationFrames
            g.resumePendingReplacementCore toRun
              (followedByFinishChoice := followedByFinishChoice)
              (hasFollowingSeq := hasFollowingSeq)
              (followedByNonProposalPriorityGrant := followedByNonProposalPriorityGrant)
              (followedByExplicitPriority? := followedByExplicitPriority?)
        | none =>
          let g :=
            if !g.sbaPaused && g.pending == .none && ckptWasRandom &&
                restoreCkptPending?.isSome && freshCont?.isNone then
              let g :=
                if g.pendingReplacement.isSome then g.change (.pendingReplacement none) else g
              let g :=
                match restoreCkptPending? with
                | some rp =>
                  g.resumePendingReplacementCore rp
                    (hasFollowingSeq := restored?.isSome || hasFollowingSeq)
                | none => g
              match restored? with
              | some rest =>
                let g := if g.continuations.isEmpty then g.change (.pushContinuationFrame {}) else g
                g.chainPendingReplacement rest
              | none => g
            else
              let combinedCont? :=
                seqOptPendingReplacement freshCont?
                  (seqOptPendingReplacement restoreCkptPending? restored?)
              match combinedCont? with
              | some combined =>
                let g := if g.continuations.isEmpty then g.change (.pushContinuationFrame {}) else g
                if g.pendingReplacement == some combined then g
                else g.change (.pendingReplacement (some combined))
              | none =>
                let g := if g.pendingReplacement.isSome then g.change (.pendingReplacement none) else g
                if g.pending == .none && g.afterRandom == .none then g.popEmptyTopContinuationFrames else g
          if followedByFinishChoice && g.sbaPaused then
            if let some cur := g.pendingReplacement then
              let next := cur.ensureEndsWithFinishResolutionChoice
              if next == cur then g else g.change (.pendingReplacement (some next))
            else
              let g := if g.continuations.isEmpty then g.change (.pushContinuationFrame {}) else g
              g.change (.pendingReplacement (some .finishResolutionChoice))
          else if let some prio := (if !followedByFinishChoice then followedByExplicitPriority? else none) then
            if g.sbaPaused then
              let g := if g.continuations.isEmpty then g.change (.pushContinuationFrame {}) else g
              g.chainPendingReplacement (.receivePriority prio)
            else if !g.over then
              g.finishAndGrantPriority prio
            else g
          else if !g.over && !g.sbaPaused &&
              (!g.continuations.isEmpty || g.pendingReplacement.isSome || followedByFinishChoice) then
            g.finishResolutionChoice
          else if hadConsumedOrig && !g.over && !g.sbaPaused &&
              g.pending == .none && g.afterRandom == .none && g.continuations.isEmpty then
            g.finishAndGrantPriority (g.priorityInstead caster)
          else g
      else
        resumePoppedIfNoPrompt g
    let flushUnlessPaysWait (g : Game) : Game :=
      if !g.sbaPaused && g.pending == .none &&
          g.currentInterpWait?.any (fun st =>
            match st.stack.back? with | some (.unlessPays ..) => true | _ => false) &&
          (g.currentStepEnv.find? (·.1 == ⟨999⟩)).isSome then
        g.resumeInterpWaitIfReady
      else g
    match p with
    | .none =>
      flushUnlessPaysWait (resumePoppedIfNoPrompt g)
    | .resolutionChoice caster (.costPicks ..)
    | .resolutionChoice caster (.crew ..)
    | .resolutionChoice caster (.zemoBoastExile ..)
    | .chooseTeamworkCreatures caster _
    | .sacrificePermanent caster _
    | .discardForAdditionalCost caster =>
      if g.proposalCostPromptStillPayable caster p then openPrompt g
      else reverseOrResumePopped g
    | .activateManaAbilities caster | .chooseX caster
    | .chooseAdditionalCost caster | .chooseKicker caster
    | .chooseGift caster | .chooseTeamwork caster =>
      if !g.over && g.stillInGame caster &&
          g.proposedSpell.any (fun prop =>
            prop.caster == caster &&
              (g.findObject? prop.spellId).any (fun o =>
                if prop.kind == .turnFaceUp then o.isOnBattlefield else o.zone == .stack) &&
              g.sourceStillPayable prop) then
        openPrompt g
      else
        reverseOrResumePopped g
    | .chooseLegend q name ids =>
      let liveIds := g.validLegendChoiceIds q name ids
      if !g.stillInGame q || liveIds.size < 2 then resumePoppedIfNoPrompt g
      else openPromptWith g (.chooseLegend q name liveIds)
    | .chooseReplacement q choices =>
      if g.replacementChoiceValid q choices then
        openPrompt g
      else resumePoppedIfNoPrompt g
    | .assignCombatDamage q forAttackers =>
      let cleanAsgns := g.pendingBlockerAssignments.filter fun a =>
        (g.findObject? a.source).any (·.isOnBattlefield) &&
          a.toCreatures.all (fun (tid, _) => (g.findObject? tid).any (·.isOnBattlefield))
      let g :=
        if cleanAsgns != g.pendingBlockerAssignments then
          g.change (.pendingBlockerAssignments cleanAsgns)
        else g
      let already := cleanAsgns.map (·.source)
      let playerStillNeeds (r : PlayerId) : Bool :=
        (g.creaturesAssigningCombatDamage forAttackers).any fun o =>
          (if forAttackers then g.isOnActiveTeam r && (g.controllerOf o).any g.isOnActiveTeam
           else g.controlledBy o r) &&
            !already.contains o.id &&
            (g.legalCombatDamageRecipients o forAttackers).size ≥ 2 &&
            g.combatDamageAmount o > 0
      if g.stillInGame q && playerStillNeeds q then
        openPrompt g
      else if forAttackers then
        if !g.stillInGame q then
          let nextAtk? := (g.teamMembers q).find? (fun r =>
            r != q && g.stillInGame r && playerStillNeeds r)
          match nextAtk? with
          | some nextAtk =>
            openPromptWith (g.logMsg s!"{(g.player nextAtk).name} assigns combat damage (CR 800.4h)")
              (.assignCombatDamage nextAtk true)
          | none =>
            let g :=
              g.changes
                ((if g.pending == .none then #[] else #[EngineChange.pending .none]) ++
                 #[EngineChange.pendingBlockerAssignments #[]])
            let g := g.logMsg "no active player assigns combat damage (CR 800.4j)"
            resumePoppedIfNoPrompt g
        else
          let g := if g.pending == .none then g else g.change (.pending .none)
          resumePoppedIfNoPrompt g
      else
        let nextP? := g.apnapPlayers.find? fun r =>
          r != q && !g.isOnActiveTeam r && g.stillInGame r && playerStillNeeds r
        match nextP? with
        | some nextP =>
          openPromptWith (g.logMsg s!"{(g.player nextP).name} assigns combat damage (CR 800.4h)")
            (.assignCombatDamage nextP false)
        | none =>
          let g := if g.pending == .none then g else g.change (.pending .none)
          resumePoppedIfNoPrompt g
    | .resolutionChoice q (.tricksterLibrary caster id connive sourceId) =>
      if g.stillInGame q && g.stillInGame caster &&
          (g.findObject? id).any (fun o => o.isOnBattlefield && g.isCreature o) then
        openPrompt g
      else
        let g := g.change (.pending .none)
        let g :=
          if g.stillInGame q && g.stillInGame caster &&
              !(g.findObject? id).any (fun o => o.isOnBattlefield && g.isCreature o) then
            g.logMsg "The target is no longer legal"
          else g
        if g.stillInGame caster && connive.isSome then
          let outerCont? := g.pendingReplacement
          let g := if outerCont?.isSome then g.change (.pendingReplacement none) else g
          if popped?.isSome then
            let g := g.chainPendingReplacement (.finishPostStep (.conniveTricksterTarget caster connive sourceId))
            let g :=
              match outerCont? with
              | some outer => g.chainPendingReplacement outer
              | none => g
            resumePoppedIfNoPrompt g
          else
            let g :=
              if let .chooseReplacement .. := g.pending then
                g.chainPendingReplacement (.finishPostStep (.conniveTricksterTarget caster connive sourceId))
              else
                g.conniveTricksterTarget caster connive (sourceId := sourceId)
            match outerCont? with
            | some outer => g.chainPendingReplacement outer
            | none => g
        else
          resumePoppedIfNoPrompt g
    | _ =>
      let promptSeat? : Option PlayerId :=
        match p with
        | .declareAttackers => some g.activePlayer
        | .declareBlockers => some g.currentBlockersPlayer
        | .resolveRandom (.chooseObject _) | .resolveRandom (.chooseIndex _) =>
          if g.pregameRandom == .none then
            g.afterRandom.player?.orElse (fun _ => g.currentResolvingContext?.bind Prod.snd)
          else p.promptPlayer?
        | _ => p.promptPlayer?
      let effectiveDeparted :=
        match promptSeat? with
        | some q =>
          if !g.stillInGame q then #[q] ++ departed.filter (· != q)
          else departed
        | none => departed
      if effectiveDeparted.isEmpty then
        match p with
        | .resolveRandom (.chooseObject ids) =>
          if ids.any (fun id => (g.findObject? id).isNone) then
            let liveIds := ids.filter (fun id => (g.findObject? id).isSome)
            if g.afterRandom.player?.any (fun r => !g.stillInGame r) then
              let g := g.changes #[.afterRandom .none, .stashedCause none]
              resumePoppedIfNoPrompt g
            else if liveIds.isEmpty then
              match g.afterRandom with
              | .revealRandomCreatureThenBottom ctrl revealed =>
                if g.stillInGame ctrl then
                  let cause := g.stashedCause
                  let outerCont? := g.pendingReplacement
                  let g :=
                    g.changes
                      (#[EngineChange.afterRandom .none, EngineChange.stashedCause none] ++
                       (if outerCont?.isSome then #[EngineChange.pendingReplacement none] else #[]))
                  let g := g.putRestOnBottomRandom ctrl
                    (revealed.filter (fun id => (g.findObject? id).isSome))
                    (cause := cause)
                  let g :=
                    match outerCont? with
                    | some outer => g.chainPendingReplacement outer
                    | none => g
                  if g.pending != .none then
                    match popped? with
                    | some popped => g.chainPendingReplacement popped
                    | none => g
                  else
                    resumePoppedIfNoPrompt g
                else
                  let g := g.changes #[.afterRandom .none, .stashedCause none]
                  resumePoppedIfNoPrompt g
              | _ =>
                let g := g.changes #[.afterRandom .none, .stashedCause none]
                resumePoppedIfNoPrompt g
            else if liveIds.size == 1 then
              let outerCont? := g.pendingReplacement
              let g := if outerCont?.isSome then g.change (.pendingReplacement none) else g
              let g := g.autoResolveSingleChooseObjectCore liveIds[0]!
              let g :=
                match outerCont? with
                | some outer => g.chainPendingReplacement outer
                | none => g
              if g.pending != .none then
                match popped? with
                | some popped => g.chainPendingReplacement popped
                | none => g
              else
                resumePoppedIfNoPrompt g
            else
              openPromptWith g (.resolveRandom (.chooseObject liveIds))
          else
            openPrompt g
        | _ => openPrompt g
      else
        let (g, nextP) := effectiveDeparted.foldl (fun (g, curP) dep =>
          if curP == .none then (g, .none)
          else g.redirectPendingAfterLeave dep (pending := curP)) (g, p)
        if nextP != .none then
          openPromptWith g nextP
        else
          flushUnlessPaysWait (resumePoppedIfNoPrompt g)
  | .closeBatch batchId startIdx =>
    g.finishOpenBatchAndLinkedExile batchId startIdx
  | .restorePausedBatch batchId startIdx wasDiscard cause objects players effects pending stack closeIfOrphaned queuedLinkedExile =>
    g.restorePausedBatch batchId startIdx wasDiscard cause objects players effects pending stack closeIfOrphaned queuedLinkedExile
  | .checkSBA fromEventIdx? =>
    let (g, _, departed) := g.checkSBACountedWithLeaves (fromEventIdx? := fromEventIdx?)
    if departed.isEmpty then g else g.appendDepartedManyToContinuations departed
  | .receivePriority p =>
    g.finishAndGrantPriority p
  | .completeActivation hadOuter hadOpenCont =>
    match g.proposedSpell with
    | none => g
    | some prop =>
      match g.completeActivation prop
          (hadOuterReplacement := hadOuter)
          (hadOpenContinuation := some hadOpenCont)
          (followedByFinishChoice := followedByFinishChoice)
          (followedByExplicitPriority? := followedByExplicitPriority?) with
      | .ok g' =>
        if hadOuter then g' else resumeAfterBecomeCast g'
      | .error _ =>
        g.reverseProposedSpell (resumeContinuation := true)
          (followedByFinishChoice := followedByFinishChoice)
          (followedByExplicitPriority? := followedByExplicitPriority?)
  | .finishBecomeActivated caster srcName srcId act abId srcSnap srcOrig hadOuter hadOpenCont =>
    let g := g.becomeActivated caster srcName srcId act
      (abilityId := abId)
      (sourceSnapshot := srcSnap)
      (sourceOriginal := srcOrig)
      (hadOuterReplacement := hadOuter)
      (hadOpenContinuation := some hadOpenCont)
      (followedByFinishChoice := followedByFinishChoice)
      (followedByExplicitPriority? := followedByExplicitPriority?)
    if hadOuter then g else resumeAfterBecomeCast g
  | .finishBecomeCast caster spellId grantPriority hadOuter hadOpenCont =>
    if let .chooseReplacement .. := g.pending then
      (g.change (.consecutivePasses 0)).chainPendingReplacement
        (.finishBecomeCast caster spellId grantPriority hadOuter hadOpenCont)
    else if !g.over && g.stillInGame caster && (g.findObject? spellId).any (·.zone == .stack) then
      let spell := g.object! spellId
      let g := g.becomeCast caster spell
        (grantPriority := grantPriority)
        (hadOuterReplacement := hadOuter)
        (hadOpenContinuation := some hadOpenCont)
      if hadOuter then g else resumeAfterBecomeCast g
    else if g.proposedSpell.isSome && g.proposalCheckpoint.isSome then
      g.reverseProposedSpell (resumeContinuation := true)
        (followedByFinishChoice := followedByFinishChoice)
        (followedByExplicitPriority? := followedByExplicitPriority?)
    else
      let clearChanges : Array EngineChange :=
        (if g.proposedSpell.isSome then #[EngineChange.proposedSpell none] else #[]) ++
        (if g.proposalCheckpoint.isSome then #[EngineChange.clearProposalCheckpoint] else #[])
      let g := if clearChanges.isEmpty then g else g.changes clearChanges
      if g.over || g.pending != .none then g
      else if !hadOuter && (g.pendingReplacement.isSome ||
          !g.outerPendingReplacements.isEmpty || g.currentInterpWait?.isSome) then
        let prio := if hadOpenCont then g.activePlayer else caster
        let g := g.chainFinishChoicePreservingPriority prio
        if !g.over && g.pending == .none then
          if g.pendingReplacement.isSome then resumeAfterBecomeCast g
          else g.finishResolutionChoice
        else g
      else if !hadOuter && grantPriority then
        g.receivePriority (g.priorityInstead (if hadOpenCont then g.activePlayer else caster))
      else g
  | .finishPostCast caster grantPriority hadOuter hadOpenCont =>
    let g := g.finishPostCast caster
      (grantPriority := grantPriority)
      (hadOuterReplacement := hadOuter)
      (hadOpenContinuation := hadOpenCont)
    if hadOuter then g
    else if !grantPriority && !followedByFinishChoice && !followedByNonProposalPriorityGrant &&
        followedByExplicitPriority?.isNone then
      g.finishResolutionChoice
    else resumeAfterBecomeCast g
  | .finishProposedSpellCosts stage grantPriority hadOuter hadOpenCont =>
    match g.finishProposedSpellCosts stage grantPriority hadOuter hadOpenCont
        (followedByFinishChoice := followedByFinishChoice)
        (followedByExplicitPriority? := followedByExplicitPriority?) with
    | .ok g' =>
      if hadOuter then g' else resumeAfterBecomeCast g'
    | .error _ =>
      g.reverseProposedSpell (resumeContinuation := true)
        (followedByFinishChoice := followedByFinishChoice)
        (followedByExplicitPriority? := followedByExplicitPriority?)
  | .finishTurnFaceUp caster spellId hadOuter =>
    let (g, callerShouldResume) := g.completeTurnFaceUp caster spellId (hadOuterReplacement := hadOuter)
      (followedByFinishChoice := followedByFinishChoice)
      (followedByExplicitPriority? := followedByExplicitPriority?)
    if callerShouldResume && !hadOuter then resumeAfterBecomeCast g else g
  | .endProposalAction clearCkpt =>
    let g := if clearCkpt && g.proposalCheckpoint.isSome then g.change .clearProposalCheckpoint else g
    if g.proposalCheckpoint.isSome then g.change .endProposalAction else g
  | .payCostPickItems p abilityId sourceId pick remainingIds =>
    g.payCostPickItems p abilityId sourceId pick remainingIds
      (followedByFinishChoice := followedByFinishChoice)
      (followedByExplicitPriority? := followedByExplicitPriority?)
  | .finishActivationExtraCosts p sourceId forObject sacrificeSource exileSource stage sinceIdx =>
    g.finishActivationExtraCosts p sourceId forObject sacrificeSource exileSource stage
      (sinceIdx := sinceIdx)
      (followedByFinishChoice := followedByFinishChoice)
      (followedByExplicitPriority? := followedByExplicitPriority?)
  | .finishPostLoyaltyActivated caster srcName srcId act abId srcSnap srcOrig hadOuter hadOpenCont =>
    let g := g.finishPostLoyaltyActivated caster srcName srcId act abId srcSnap srcOrig hadOuter hadOpenCont
      (followedByFinishChoice := followedByFinishChoice)
      (followedByExplicitPriority? := followedByExplicitPriority?)
    if hadOuter then g else resumeAfterBecomeCast g
  | .finishActivateManaAbilityPicks p id oname mana remainingPicks remainingCostIds tap sacrificeSelf activatedIdx restriction damageYou isMountain prevPending exileSelf powerUp exhaust riders exileFromZone? discardSelf exileSymIds extraEffect? =>
    g.finishActivateManaAbilityPicks p id oname mana remainingPicks remainingCostIds tap sacrificeSelf activatedIdx restriction damageYou isMountain prevPending
      (exileSelf := exileSelf) (powerUp := powerUp) (exhaust := exhaust) (riders := riders)
      (exileFromZone? := exileFromZone?) (discardSelf := discardSelf) (exileSymIds := exileSymIds)
      (extraEffect? := extraEffect?) (hasFollowingSeq := hasFollowingSeq)
  | .finishActivateManaAbilityPostSac p id oname srcSnap mana tap activatedIdx restriction damageYou isMountain prevPending powerUp exhaust riders extraEffect? =>
    g.finishActivateManaAbilityPostSac p id oname srcSnap mana tap activatedIdx restriction damageYou isMountain prevPending
      (powerUp := powerUp) (exhaust := exhaust) (riders := riders)
      (extraEffect? := extraEffect?) (hasFollowingSeq := hasFollowingSeq)
  | .runModalManaEffect p sourceId eff =>
    g.applyUnifiedAbility p eff #[] (some sourceId)
  | .finishBeginRecruit p =>
    g.finishBeginRecruit p
  | .finishDrawThenBeginDiscard p discardRounds =>
    g.beginDiscardCards #[p] discardRounds
  | .finishConniveDraws controller extraDraws conniveDrawCause stage =>
    g.finishConniveDraws controller extraDraws conniveDrawCause stage
  | .amass controller subtype n attach cause =>
    g.amass controller subtype n (attach := attach) (cause := cause)
  | .finishAmassOn controller armyId subtype n attach stage cause =>
    g.finishAmassOn controller armyId subtype n (attach := attach) (stage := stage) (cause := cause)
  | .finishFreshAmass controller subtype n attach cause startEventIdx =>
    g.finishFreshAmass controller subtype n attach (cause := cause) (startEventIdx := startEventIdx)
  | .finishDealDamageLoseIndestructibleExile targetId targetName n cause =>
    g.finishDealDamageLoseIndestructibleExile targetId targetName n cause
  | .finishPlaceSearched p fromId name tapped _ =>
    g.finishPlaceSearched p fromId name tapped
  | .placeSearchedBatch p remainingIds tapped cause entered preBattlefield =>
    g.placeSearchedBatch p remainingIds tapped (cause := cause)
      (entered := entered) (preBattlefield := preBattlefield)
  | .finishSearchAfterPlace p fromId dest after fromLibrary handRest cause =>
    g.finishSearchAfterPlace p fromId dest after fromLibrary handRest cause
  | .surveilMoveLoop p remainingGy cause =>
    g.surveilMoveLoop p remainingGy cause
  | .finishSurveilPostMove p card fromId remainingGy cause =>
    g.finishSurveilPostMove p card fromId remainingGy cause
  | .finishLibraryLook =>
    g.finishLibraryLookCore
  | .requestOrderInto ids dest log cause =>
    g.requestOrderInto ids dest log (cause := cause)
  | .finishProliferateEachKind controller targetId remainingKinds hasPlusOne effCause =>
    g.finishProliferateEachKind controller targetId remainingKinds hasPlusOne effCause
  | .finishProliferateTarget p targetId remainingKinds hasPlusOne remainingTargets permIds playerIds chosenEmpty remainingRounds cause =>
    g.finishProliferateTarget p targetId remainingKinds hasPlusOne remainingTargets permIds playerIds chosenEmpty remainingRounds cause
  | .finishDiscardForDrawMay p n =>
    g.finishDiscardForDrawMay p n
  | .finishSacArtifactOrDiscardDraw p n =>
    g.finishSacArtifactOrDiscardDraw p n
  | .finishChooseDiscardCard p card remaining =>
    g.finishChooseDiscardCard p card remaining
  | .finishRecruitDiscard p isLand =>
    g.finishRecruitDiscard p isLand
  | .finishPutLandFromHand fromId =>
    g.finishPutLandFromHand fromId
  | .finishBeginOnBattlefield fromId remainingIds =>
    g.finishBeginOnBattlefield fromId remainingIds
  | .addFinalityTo targetId n byPlayer entersWith cause =>
    match g.findObject? targetId with
    | some tgt =>
      g.addFinalityTo tgt n (byPlayer := byPlayer) (entersWith := entersWith) (cause := cause)
    | none => g
  | .loseLifeAfterDraw p life cause =>
    g.loseLife p life (cause := cause)
  | .continueInterpreter st =>
    g.withContinuationFrame fun g => g.resumeInterpreter st
  | .continueSpellModes controller modeEffects remainingTargets castFromGraveyard kicked giftPromised chosenX sourceId skippedOptionalSlots lastKnownPower lastKnownToughness =>
    g.runSpellModesAndEmpower controller modeEffects remainingTargets castFromGraveyard kicked giftPromised chosenX sourceId skippedOptionalSlots lastKnownPower lastKnownToughness
  | .empowerJace controller n stage targetId cause =>
    g.empowerJaceStep controller n stage targetId cause
  | .continueConnives controller remainingIds =>
    g.runConniveObjects controller remainingIds
  | .dealDamageToEachCreatureMatching remainingIds n onlyNonSubtype exceptControllerTokens onlyOpponentsOf source cause startEventIdx suppressLifelink =>
    g.dealDamageToEachCreatureMatchingIds remainingIds n
      (onlyNonSubtype := onlyNonSubtype)
      (exceptControllerTokens := exceptControllerTokens)
      (onlyOpponentsOf := onlyOpponentsOf)
      (source := source) (cause := cause)
      (startEventIdx := startEventIdx) (suppressLifelink := suppressLifelink)
  | .destroyPermanentsLoop remainingIds allCandidates countNote obGainLifeFor logMsgAfter preBattlefield cause fromEventIdx? =>
    g.destroyPermanentsLoop remainingIds
      (allCandidates := allCandidates) (countNote := countNote)
      (obGainLifeFor := obGainLifeFor) (logMsgAfter := logMsgAfter)
      (preBattlefield := preBattlefield) (cause := cause)
      (fromEventIdx? := fromEventIdx?)
  | .sacrificePermanentsLoop remaining preBattlefield cause createBeastFor passiveLog fromEventIdx? =>
    g.sacrificePermanentsLoop remaining
      (preBattlefield := preBattlefield) (cause := cause)
      (createBeastFor := createBeastFor) (passiveLog := passiveLog)
      (fromEventIdx? := fromEventIdx?)
  | .putToBattlefieldLoop controller remainingIds enteredFromIds useCardOwner haste tapped isLandEnters onlyFoodArtifact entryLog cause preBattlefield =>
    g.putToBattlefieldLoop controller remainingIds
      (enteredFromIds := enteredFromIds) (useCardOwner := useCardOwner)
      (haste := haste) (tapped := tapped) (isLandEnters := isLandEnters)
      (onlyFoodArtifact := onlyFoodArtifact) (entryLog := entryLog) (cause := cause)
      (preBattlefield := preBattlefield)
  | .returnLinkedExileLoop remainingIds cause enteredFromIds preBattlefield pendingLog =>
    g.returnLinkedExileLoop remainingIds (cause := cause)
      (enteredFromIds := enteredFromIds) (preBattlefield := preBattlefield)
      (pendingLog := pendingLog)
  | .putShadowCounter targetId =>
    match g.findObject? targetId with
    | some o => g.putShadowCounter o
    | none => g
  | .finishShadowCounter targetId before =>
    g.finishShadowCounter targetId before
  | .finishLinkedExileMove remainingIds preBattlefield pendingLog enteredFromIds =>
    if preBattlefield.isSome || pendingLog.isSome || !enteredFromIds.isEmpty then
      g.runLinkedExileBatch remainingIds preBattlefield pendingLog enteredFromIds
    else
      g.returnLinkedExileMoves remainingIds
  | .untapPermanentsLoop remainingIds cause =>
    g.untapPermanentsLoop remainingIds (cause := cause)
  | .millCardsLoop p remainingIds emptyTail cause logCard freshCount =>
    g.millCardsLoop p remainingIds (emptyTail := emptyTail) (cause := cause)
      (logCard := logCard) (freshCount := freshCount)
  | .exilePermanentsLoop remainingIds logExile cause logCard fromEventIdx? =>
    g.exilePermanentsLoop remainingIds (logExile := logExile) (cause := cause)
      (logCard := logCard) (fromEventIdx? := fromEventIdx?)
  | .flickerLoop remainingIds exiledPreIds enteredFromIds logText stage tapped onlyLandTapped clearExileFields cause preBattlefield fromEventIdx? =>
    g.resumeFlickerLoop remainingIds exiledPreIds enteredFromIds logText stage
      tapped onlyLandTapped clearExileFields cause preBattlefield fromEventIdx?
  | .finishMillChooseForHand p preIds types matchedPreIds max mustOne allMatches maxPut cause =>
    if allMatches then
      let pred : GameObject → Bool :=
        if types.isEmpty then (g.isPermanentCard ·)
        else (fun o => types.any (g.hasType o ·))
      g.finishMillThenPutFromPublic p preIds pred maxPut cause
    else
      let pred : ObjectId → GameObject → Bool :=
        if !types.isEmpty then (fun _ o => types.any (g.hasType o ·))
        else (fun preId _ => matchedPreIds.contains preId)
      g.finishMillChooseForHand p preIds pred max mustOne (cause := cause)
  | .finishPostStep step =>
    g.runPostStep step (followedByFinishChoice := followedByFinishChoice)
      (followedByExplicitPriority? := followedByExplicitPriority?)
  | .setLife p life msg cause =>
    g.setLife p life msg (cause := cause)
  | .logMessage msg =>
    g.logMsg msg
  | .counterStackSpell spellId exilePermanent grantFreeCast ctrl cause postMove name =>
    if postMove then
      g.finishCounterStackSpell spellId grantFreeCast ctrl (cause.getD (.gameRule .spellCast)) name
    else
      g.counterStackSpell spellId exilePermanent grantFreeCast ctrl
  | .returnStackSpell spellId owner name postMove =>
    if postMove then
      g.finishReturnStackSpell spellId owner name
    else
      g.returnStackSpell spellId
  | .leavePlayersWhoLost savedPending popOuter departed rewindProposal fromEventIdx? =>
    let (g, _, _, _, departed, _) :=
      g.checkSBACountedWithLeavesCore savedPending popOuter departed rewindProposal
        (deferRestore := false) (fromEventIdx? := fromEventIdx?)
    if departed.isEmpty then g else g.appendDepartedManyToContinuations departed
  | .endControlExileLoop remaining cause pendingLog extraSkipIds fromEventIdx? deferPlayFromExileLogs =>
    g.runEndControlExileLoop remaining (cause := cause) (pendingLog := pendingLog)
      (extraSkipIds := extraSkipIds) (fromEventIdx? := fromEventIdx?)
      (deferPlayFromExileLogs := deferPlayFromExileLogs)
  | .beginStepCont st =>
    g.beginStepCont st
  | .finishCleanupAfterClearEot =>
    g.finishCleanupAfterClearEot
  | .continueStartNextTurn nextP remainingDeparted runBeginTurn alreadyExpired =>
    g.continueStartNextTurn nextP remainingDeparted runBeginTurn alreadyExpired
  | .beginTurnAfterStartExpiry =>
    g.beginTurnAfterStartExpiry
  | .runPostCastCleanup cleanup =>
    if g.over || g.suppressInteractiveReplay then g
    else
      let g := if g.continuations.isEmpty then g.change (.pushContinuationFrame {}) else g
      let g := ((g.change (.postCastCleanup (some cleanup))).runPostCastCleanup).drainLocalPendingReplacement
      if g.pending == .none && g.afterRandom == .none then g.popEmptyTopContinuationFrames else g
  | .continueCheckpointReplay remainingStream fullKeptStream revMap liveObjMap effRevMap minPostCkptEffId suppressInteractive keptOrigNextEffs =>
    let quiet := suppressInteractive || g.over || g.suppressInteractiveReplay
    let g := g.replayKeptStreamCore remainingStream fullKeptStream revMap liveObjMap effRevMap
      (minPostCkptEffId := minPostCkptEffId)
      (suppressInteractive := quiet)
      (keptOrigNextEffs := keptOrigNextEffs)
      (runBatch := if quiet then
        (fun g0 f =>
          (g0.withBatchCore none f (suppressInteractive := true)).flushQueuedLinkedExile
            (suppressInteractive := true))
      else
        (fun g0 f => g0.withBatch none f))
    if g.players.any (·.leftTheGame) &&
        !g.sbaPaused && !g.pendingReplacement.any PendingReplacement.hasCheckpointReplay then
      g.reconcilePostReplayDepartures (suppressInteractive := quiet)
    else g
  | .phaseOutPermanentsLoop remainingIds cause preSnaps startEventIdx reconcile =>
    g.phaseOutPermanentsLoop remainingIds (cause := cause) (preSnaps := preSnaps)
      (startEventIdx := startEventIdx) (reconcile := reconcile)
  | .phaseInControlled p includeTeammates =>
    g.phaseInControlled p (includeTeammates := includeTeammates)
  | .phaseInControlledLoop remainingIds cause startEventIdx reconcile allowDirectSingle =>
    g.phaseInControlledLoop remainingIds (cause := cause) (startEventIdx := startEventIdx)
      (reconcile := reconcile) (allowDirectSingle := allowDirectSingle)

/-- Execute a deferred `PostStep` continuation after a CR 616.1
`Pending.chooseReplacement` pause finishes. -/
partial def runPostStep (g : Game) (step : PostStep)
    (followedByFinishChoice : Bool := false)
    (followedByExplicitPriority? : Option PlayerId := none) : Game :=
  match step with
  | .putArtifactOntoBattlefield p cardId _ =>
    match g.followMovedToZone? cardId (· == .battlefield) with
    | some entered =>
      let g := g.logMsg s!"{(g.player p).name} puts {g.name entered} onto the battlefield"
      g.afterPermanentEnters entered
    | none => g
  | .continueDiscardTwo controller rest draws chosen =>
    g.continueDiscardTwo controller rest draws chosen
  | .finishDiscardTwoDraws controller baseDraws oppIds startIdx =>
    g.finishDiscardTwoDraws controller baseDraws oppIds startIdx
  | .enteredBattlefieldPutRestBottomRandom p cardId rest cause =>
    let g :=
      match g.followMovedToZone? cardId (· == .battlefield) with
      | some entered => (g.logMsg s!"{g.name entered} enters the battlefield").afterPermanentEnters entered
      | none => g
    if rest.isEmpty then g
    else
      g.requestOrderInto rest (.library p)
        s!"{(g.player p).name} puts the rest on the bottom of their library in a random order"
        (cause := cause)
  | .hawkeyeArrows controller modes targets targetIdx sourceId =>
    g.runHawkeyeArrows controller modes targets targetIdx sourceId
  | .addPlusOnesForLoggedDiscards p sourceId =>
    if !g.stillInGame p then g
    else
      let cnt := g.loggedDiscards p
      match sourceId.bind (fun id => (g.findObject? id).filter (·.isOnBattlefield)) with
      | some o => if cnt > 0 then g.addPlusOnePlusOneTo o cnt else g
      | none => g
  | .enteredBattlefieldSilent cardId isLand
  | .returnedBattlefieldEndStep cardId isLand
  | .returnedToBattlefield cardId isLand =>
    match g.followMovedToZone? cardId (· == .battlefield) with
    | some entered =>
      let g :=
        match step with
        | .returnedBattlefieldEndStep .. =>
          match entered.attachedTo.bind g.findObject? with
          | some host =>
            g.logMsg s!"{g.name entered} returns to the battlefield attached to {g.name host} (beginning of end step)"
          | none =>
            g.logMsg s!"{g.name entered} returns to the battlefield (beginning of end step)"
        | .returnedToBattlefield .. =>
          match entered.attachedTo.bind g.findObject? with
          | some host =>
            g.logMsg s!"{g.name entered} returns to the battlefield attached to {g.name host}"
          | none =>
            g.logMsg s!"{g.name entered} returns to the battlefield"
        | _ => g
      if isLand then g.afterLandEnters entered else g.afterPermanentEnters entered
    | none => g
  | .putOntoBattlefieldHasteAtFour p cardId x shuffle =>
    let g :=
      match g.followMovedToZone? cardId (· == .battlefield) with
      | some entered =>
        let name := g.name entered
        let g := g.afterPermanentEnters entered
        let g := if x >= 4 then g.grantUntilEotLogged (g.object! entered.id) #[Keyword.haste] else g
        g.logMsg s!"{name} is put onto the battlefield"
      | none => g
    if shuffle then g.shuffleThen p .none else g
  | .revealPutCreaturesStep p remaining put enteredFromIds cause =>
    g.finishRevealPutCreaturesStep p remaining put enteredFromIds (cause := cause)
  | .shuffleThenGainLife p life =>
    g.withContinuationFrame fun g =>
      (g.requestShuffle p (.gainLife p life)).continueIfShuffled
  | .dealDamageToEachOpponent p amount sourceId cause startEventIdx =>
    g.dealDamageToEachOpponent p amount (source := sourceId.bind g.damageSourceById?)
      (cause := cause) (startEventIdx := startEventIdx)
  | .discardCleanupIds p remainingIds justDiscarded =>
    let g :=
      match justDiscarded with
      | some (cid, owner) =>
        match g.followMovedToZone? cid (· == Zone.graveyard owner) with
        | some _ =>
          let name :=
            match g.findObject? cid with
            | some o => g.name o
            | none => ((g.lastKnownBefore? cid).map (fun (eo : EventObject) => eo.name)).getD "card"
          g.logMsg s!"{(g.player p).name} discards {name} (cleanup)"
        | none => g
      | none => g
    g.discardCleanupIds p remainingIds
  | .postSbaCleanup sba =>
    g.finishPostSbaCleanup sba
  | .cleanupStepAfterDiscard =>
    g.finishCleanupStepAfterDiscard
  | .wheelDrawThenOfferNext p cards rest =>
    let g := g.draw p cards
    if let .chooseReplacement .. := g.pending then
      g.chainPendingReplacement (.finishPostStep (.wheelOfferNext cards rest #[]))
    else
      g.runPostStep (.wheelOfferNext cards rest #[])
  | .wheelOfferNext cards rest accepted =>
    let restLiving := rest.filter g.stillInGame
    match restLiving[0]? with
    | some next =>
      g.beginResolutionChoice next (.mayWheel cards (restLiving.extract 1 restLiving.size) accepted)
        s!"{(g.player next).name} may discard their hand and draw {cards} cards"
    | none =>
      let acceptedLiving := accepted.filter g.stillInGame
      if acceptedLiving.isEmpty then g
      else
        let pairs := acceptedLiving.foldl (fun acc q =>
          acc ++ ((g.discardableHandIds q).map (fun id => (q, id)))) #[]
        let g :=
          if pairs.isEmpty then g
          else
            g.withBatch none fun g =>
              g.discardMultiHandIdsLoop pairs (logEach := true)
        if let .chooseReplacement .. := g.pending then
          g.chainPendingReplacement (.finishPostStep (.wheelDrawsLoop cards acceptedLiving))
        else
          g.runPostStep (.wheelDrawsLoop cards acceptedLiving)
  | .wheelDrawsLoop cards remainingPlayers =>
    let living := remainingPlayers.filter g.stillInGame
    match living[0]? with
    | none => g
    | some q =>
      let more := living.extract 1 living.size
      let g := if cards > 0 then g.draw q cards else g
      if more.isEmpty then g
      else if let .chooseReplacement .. := g.pending then
        g.chainPendingReplacement (.finishPostStep (.wheelDrawsLoop cards more))
      else
        g.runPostStep (.wheelDrawsLoop cards more)
  | .searchLibraryPlaneswalker p =>
    g.resolveSearchLibrary p (·.isPlaneswalker) false "planeswalker card"
  | .searchLibrarySphinx p =>
    g.resolveSearchLibrary p (fun c => c.isCreature && c.hasSubtype .sphinx) false
      "Sphinx creature card"
  | .drawOneThenPlusOnesForDiscards p sourceId =>
    if !g.stillInGame p then g
    else
      let g := g.draw p 1
      if let .chooseReplacement .. := g.pending then
        g.chainPendingReplacement (.finishPostStep (.addPlusOnesForLoggedDiscards p sourceId))
      else
        g.runPostStep (.addPlusOnesForLoggedDiscards p sourceId)
  | .queueTapAndStunReflexive p nonlandCount sourceId =>
    if nonlandCount == 0 then g
    else
      g.putReflexiveTrigger p sourceId
        { targets := TargetSpec.creature.asUpTo nonlandCount
          body := .seq #[
            .permanent (.setTapped .allTargets true),
            .permanent (.modifyCounters (.put .stun (.const 1)) .allTargets)] }
        (deferToPriority := true)
  | .nickFuryMayTransformOrBottom p cardId rest cause =>
    if !g.stillInGame p then g
    else
      match g.followMovedToZone? cardId (· == .battlefield) with
      | some o =>
        if (g.baseCard o).otherFace.isSome && !g.cantTransform o then
          g.beginResolutionChoice p (.nickFuryMayTransform o.id rest)
            s!"{(g.player p).name} may transform {g.name o}"
        else g.putRestOnBottomRandom p rest (cause := cause)
      | none => g.putRestOnBottomRandom p rest (cause := cause)
  | .checkDrawThenOpponentsDraw p beforeDraws =>
    if g.loggedDraws p == beforeDraws then g
    else
      let (src, ctrl) :=
        match g.currentResolvingContext? with
        | some (s, c) => (s, c.orElse (fun _ => some p))
        | none => (none, some p)
      let (g, c) := g.allocDelayedCause ctrl src
      let opps := g.apnapOrder.filter (g.isLivingOpponentOf p ·)
      g.runPostStep (.opponentsDrawOneLoop p opps (some c))
  | .opponentsDrawOneLoop drawer remainingOpponents cause =>
    let living := remainingOpponents.filter g.stillInGame
    match living[0]? with
    | none =>
      if g.stillInGame drawer then
        g.logMsg s!"{(g.player drawer).name} draws, so each opponent draws a card"
      else g
    | some opp =>
      let rest := living.extract 1 living.size
      let g := g.draw opp 1 (cause := cause)
      if let .chooseReplacement .. := g.pending then
        g.chainPendingReplacement (.finishPostStep (.opponentsDrawOneLoop drawer rest cause))
      else
        g.runPostStep (.opponentsDrawOneLoop drawer rest cause)
  | .loseLifeForMilledManaValue p tops cause =>
    if !g.stillInGame p then g
    else
      let milled := tops.filterMap (fun id => g.followMilledPublic? id)
      let mv := milled.foldl (fun acc o => acc + g.objectManaValue o) 0
      g.loseLife p mv (cause := cause)
  | .addPlusOnesToSource sourceId count =>
    match g.findObject? sourceId with
    | some src => if src.isOnBattlefield then g.addPlusOnePlusOneTo src count else g
    | none => g
  | .beginDiscardCardsStep players =>
    g.beginDiscardCards players (resuming := g.thirstDiscardsLeft > 0 || g.discardBatch.isSome)
  | .continueAfterDiscardStep remaining samePlayer count =>
    g.continueAfterDiscard remaining (samePlayer := samePlayer) (count := count)
  | .discardHandIdsLoop p ids logEach cause =>
    g.discardHandIdsLoop p ids (logEach := logEach) (cause := cause)
  | .discardMultiHandIdsLoop remaining logEach cause =>
    g.discardMultiHandIdsLoop remaining (logEach := logEach) (cause := cause)
  | .closeDiscardBatchStep =>
    g.closeCurrentDiscardBatch
  | .logPutsIntoHand revealer fromId cardName =>
    if (g.followMovedToZone? fromId (· == .hand revealer)).isSome then
      g.logMsg s!"{(g.player revealer).name} puts {cardName} into their hand"
    else g
  | .logInfluenceThenScryTwo sourceId beforeInfluence =>
    match g.findObject? sourceId with
    | some src =>
      if src.isOnBattlefield then
        let g :=
          if src.status.influence > beforeInfluence then
            g.logMsg s!"{g.name src} gets an influence counter"
          else g
        g.beginScry (g.you src) 2
      else g
    | none => g
  | .logCreatedTokensSummary controller startEventIdx =>
    g.logCreatedTokensSummary controller startEventIdx
  | .putRestOnBottomRandom p rest cause =>
    g.putRestOnBottomRandom p rest (cause := cause)
  | .returnToHandLoop remainingIds cause fromEventIdx? =>
    g.returnPermanentsToHandLoop remainingIds (cause := cause) (fromEventIdx? := fromEventIdx?)
  | .millSourceInfluenceCount controller sourceId =>
    if g.stillInGame controller then
      let n := ((g.damageSourceById? sourceId).map (·.status.influence)).getD 0
      g.mill controller n
    else g
  | .continueOpeningBegin remainingIds =>
    g.continueOpeningBegin remainingIds
  | .resumeChooseModeAfterLeave p =>
    let promptIfTriggersNeedTargets (g : Game) : Game :=
      if !g.over && g.pending == .none && g.continuations.isEmpty &&
          g.triggerNeedingTargets.isSome then
        g.promptTriggerTargetsIfNeeded
      else g
    if g.over then
      let g :=
        if g.proposedSpell.any (fun prop =>
            !g.stillInGame prop.caster || (g.findObject? prop.spellId).isNone) then
          (if g.pending == .none then g else g.change (.pending .none)).reverseProposedSpell
            (resumeContinuation := true) (alwaysGrantPriority := true)
            (followedByFinishChoice := followedByFinishChoice)
            (followedByExplicitPriority? := followedByExplicitPriority?)
        else g
      g.completeActiveResolutions
    else if !g.stillInGame p then
      if g.proposedSpell.any (·.caster == p) then
        promptIfTriggersNeedTargets
          (g.reverseProposedSpell (resumeContinuation := true) (alwaysGrantPriority := true)
            (followedByFinishChoice := followedByFinishChoice)
            (followedByExplicitPriority? := followedByExplicitPriority?))
      else g
    else
      match g.proposedSpell with
      | none => g
      | some prop =>
        if prop.caster != p then g
        else
          match prop.kind with
          | .activatedAbility =>
            if g.sourceStillPayable prop &&
                (g.findObject? prop.spellId).any (·.zone == .stack) &&
                prop.abilityModes.any (fun m => g.modeIsChoosable p m prop.sourceId) then
              g.change (.pending (.chooseMode p))
            else
              promptIfTriggersNeedTargets
                (g.reverseProposedSpell (resumeContinuation := true) (alwaysGrantPriority := true)
                  (followedByFinishChoice := followedByFinishChoice)
                  (followedByExplicitPriority? := followedByExplicitPriority?))
          | .spell =>
            match g.findObject? prop.spellId with
            | none =>
              promptIfTriggersNeedTargets
                (g.reverseProposedSpell (resumeContinuation := true) (alwaysGrantPriority := true)
                  (followedByFinishChoice := followedByFinishChoice)
                  (followedByExplicitPriority? := followedByExplicitPriority?))
            | some spell =>
              if spell.zone != .stack || !g.sourceStillPayable prop then
                promptIfTriggersNeedTargets
                  (g.reverseProposedSpell (resumeContinuation := true) (alwaysGrantPriority := true)
                    (followedByFinishChoice := followedByFinishChoice)
                    (followedByExplicitPriority? := followedByExplicitPriority?))
              else
              let face := g.baseCard spell
              let effModes := g.evalSpellModes p spell
              let chosen := g.chosenModesOf spell
              let validChosen := chosen.filter (fun i =>
                effModes[i]?.any (fun m => g.spellModeIsChoosable p m (some spell.id)))
              let g :=
                if validChosen == chosen then g
                else if validChosen.isEmpty then
                  g.change (.stackEntry spell.id .clearChosenModes)
                else
                  g.record (GameEvent.announced g.turnNumber spell.id (modes := validChosen))
              let more := (List.range effModes.size).any (fun i =>
                !validChosen.contains i && g.spellModeIsChoosable p effModes[i]! (some spell.id))
              if validChosen.size < g.maxModesFor p face && more then
                g.change (.pending (.chooseMode p))
              else if !validChosen.isEmpty then
                g.afterModesChosen p
              else if isReturnUpToTwoGyModal face || face.allowsZeroTargets then
                g.change (.pending (.chooseMode p))
              else
                promptIfTriggersNeedTargets
                  (g.reverseProposedSpell (resumeContinuation := true) (alwaysGrantPriority := true)
                    (followedByFinishChoice := followedByFinishChoice)
                    (followedByExplicitPriority? := followedByExplicitPriority?))
          | .turnFaceUp =>
            if g.sourceStillPayable prop && (g.findObject? prop.spellId).any (·.isOnBattlefield) then g
            else
              promptIfTriggersNeedTargets
                (g.reverseProposedSpell (resumeContinuation := true) (alwaysGrantPriority := true)
                  (followedByFinishChoice := followedByFinishChoice)
                  (followedByExplicitPriority? := followedByExplicitPriority?))
  | .resumeChooseTargetsAfterLeave p =>
    let promptIfTriggersNeedTargets (g : Game) : Game :=
      if !g.over && g.pending == .none && g.continuations.isEmpty &&
          g.triggerNeedingTargets.isSome then
        g.promptTriggerTargetsIfNeeded
      else g
    let ownPropNeedsReverse :=
      g.proposedSpell.any (fun prop =>
        prop.caster == p &&
          (!g.stillInGame p || (g.findObject? prop.spellId).isNone || !g.sourceStillPayable prop))
    let g :=
      if ownPropNeedsReverse then
        (if g.pending == .none then g else g.change (.pending .none)).reverseProposedSpell
          (resumeContinuation := true) (alwaysGrantPriority := true)
          (followedByFinishChoice := followedByFinishChoice)
          (followedByExplicitPriority? := followedByExplicitPriority?)
      else g
    let pendingBlocksTargets :=
      match g.pending with
      | .none | .chooseTargets _ => false
      | _ => true
    if g.over then
      if ownPropNeedsReverse then g
      else g.afterTriggerTargetsChosen
    else if ownPropNeedsReverse && (pendingBlocksTargets || g.afterRandom != .none) then
      g
    else
      match g.objectAwaitingTargets with
      | none =>
        if ownPropNeedsReverse then
          promptIfTriggersNeedTargets g
        else
          g.afterTriggerTargetsChosen
      | some obj =>
        let isPropSpell := g.proposedSpell.any (·.spellId == obj.id)
        let caster :=
          match g.proposedSpell with
          | some prop =>
            if prop.spellId == obj.id then prop.caster
            else (g.stack.find? (·.objectId == obj.id)).map (·.controller) |>.getD p
          | none =>
            (g.stack.find? (·.objectId == obj.id)).map (·.controller) |>.getD p
        if !g.stillInGame caster then
          if isPropSpell then
            promptIfTriggersNeedTargets
              (g.reverseProposedSpell (resumeContinuation := true) (alwaysGrantPriority := true)
                (followedByFinishChoice := followedByFinishChoice)
                (followedByExplicitPriority? := followedByExplicitPriority?))
          else
            (g.ceaseToExist obj.id (cause := some (.gameRule .triggeredAbility))).afterTriggerTargetsChosen
        else
          let hasLegal := !(g.legalProposedTargets caster obj).isEmpty
          let allowZero :=
            (g.targetSpecOf obj).allowsZero ||
            match obj.triggeredAbility with
            | some ab => ab.allowsZeroTargets || obj.abilityEffect.any (·.allowsZeroTargets)
            | none =>
              match g.currentSpellEffect obj with
              | some e => e.allowsZeroTargets
              | none => obj.abilityEffect.any (·.allowsZeroTargets)
          let canDeclineOrPick :=
            hasLegal || g.canSkipCurrentOptionalSlot obj || g.canFinishOptionalTargets obj || allowZero
          if canDeclineOrPick then
            if g.pending == .chooseTargets caster then g
            else g.change (.pending (.chooseTargets caster))
          else if isPropSpell then
            promptIfTriggersNeedTargets
              (g.reverseProposedSpell (resumeContinuation := true)
                (extraLog := some s!"{g.name obj} has no legal target and can't be cast")
                (alwaysGrantPriority := true)
                (followedByFinishChoice := followedByFinishChoice)
                (followedByExplicitPriority? := followedByExplicitPriority?))
          else
            let objName := g.name obj
            let g := g.ceaseToExist obj.id (cause := some (.gameRule .triggeredAbility))
              |>.logMsg s!"{objName}'s triggered ability has no legal target and is removed from the stack (CR 603.3d)"
            g.afterTriggerTargetsChosen
  | .resumeTriggerModesAfterLeave p objectId remaining chosen =>
    if g.over || !g.stillInGame p then g.finishResolutionChoice
    else
      match g.findObject? objectId with
      | some obj =>
        if obj.zone != .stack then g.finishResolutionChoice
        else
          let tModes := g.triggerModesOf obj
          let validChosen := chosen.filter (fun i =>
            tModes[i]?.any (g.triggerModeChoosable p obj))
          let needed := remaining + (chosen.size - validChosen.size)
          let choosableLeft :=
            ((List.range tModes.size).filter (fun i =>
              !validChosen.contains i && (tModes[i]?.any (g.triggerModeChoosable p obj)))).length
          if needed == 0 then
            let sorted := validChosen.qsort (· < ·)
            let g := g.record (GameEvent.announced g.turnNumber obj.id (modes := sorted))
            match combineTriggerModes (tModes.map (fun m => g.expandEachOpponentEffect p m (some obj.id))) sorted with
            | none => g.finishResolutionChoice
            | some eff =>
              let g := g.changeObject obj.id (.abilityEffect (some eff))
              let g := if !eff.requiresTarget then g.change (.stackEntry obj.id (.targetsAnnounced true)) else g
              g.finishResolutionChoice
          else if choosableLeft < needed then
            let objName := g.name obj
            (g.ceaseToExist obj.id (cause := some (.gameRule .noLegalMode))
              |>.logMsg s!"{objName}'s triggered ability has too few legal modes and is removed from the stack (CR 603.3c)").finishResolutionChoice
          else
            g.change (.pending (.resolutionChoice p (.triggerModes obj.id needed validChosen)))
      | none => g.finishResolutionChoice
  | .resumeUpToTriggerModesAfterLeave p objectId remaining chosen =>
    if g.over || !g.stillInGame p then g.finishResolutionChoice
    else
      match g.findObject? objectId with
      | some obj =>
        if obj.zone != .stack then g.finishResolutionChoice
        else
          let modes := g.triggerModesOf obj
          let validChosen := chosen.filter (fun i =>
            modes[i]?.any (g.triggerModeChoosable p obj))
          let remaining := remaining + (chosen.size - validChosen.size)
          let anyChoosableLeft :=
            (List.range modes.size).any (fun i =>
              !validChosen.contains i && (modes[i]?.any (g.triggerModeChoosable p obj)))
          if remaining > 0 && anyChoosableLeft then
            g.change (.pending (.resolutionChoice p (.upToTriggerModes obj.id remaining validChosen)))
          else if validChosen.isEmpty then
            let noop : Effect := { body := .noop }
            let g := g.record (GameEvent.announced g.turnNumber obj.id (modes := #[]))
            let g := g.changes #[
              .object obj.id (.abilityEffect (some noop)),
              .stackEntry obj.id (.targetsAnnounced true)]
            g.finishResolutionChoice
          else
            let sorted := validChosen.qsort (· < ·)
            let g := g.record (GameEvent.announced g.turnNumber obj.id (modes := sorted))
            match combineTriggerModes (modes.map (fun m => g.expandEachOpponentEffect p m (some obj.id))) sorted with
            | none => g.finishResolutionChoice
            | some eff =>
              let g := g.changeObject obj.id (.abilityEffect (some eff))
              let g := if !eff.requiresTarget then g.change (.stackEntry obj.id (.targetsAnnounced true)) else g
              g.finishResolutionChoice
      | none => g.finishResolutionChoice
  | .resumeHawkeyeModesAfterLeave p objectId left chosen =>
    if g.over || !g.stillInGame p then g.finishResolutionChoice
    else
      match g.findObject? objectId with
      | some obj =>
        if obj.zone != .stack then g.finishResolutionChoice
        else
          let validChosen := chosen.filter (fun i =>
            hawkeyeModeEffects[i]?.any (g.triggerModeChoosable p obj))
          let anyMoreChoosable :=
            (List.range hawkeyeModeEffects.size).any (fun i =>
              !validChosen.contains i && (hawkeyeModeEffects[i]?.any (g.triggerModeChoosable p obj)))
          if validChosen.size < left && anyMoreChoosable then
            g.change (.pending (.resolutionChoice p (.hawkeyeModes left validChosen (some obj.id))))
          else
            let sorted := validChosen.qsort (· < ·)
            let eff : Effect :=
              if sorted.isEmpty then { body := .noop }
              else hawkeyeArrowsEffect sorted
            let g := g.record (GameEvent.announced g.turnNumber obj.id (modes := sorted))
            let g := g.changeObject obj.id (.abilityEffect (some eff))
            let g := if !eff.requiresTarget then g.change (.stackEntry obj.id (.targetsAnnounced true)) else g
            g.finishResolutionChoice
      | none => g.finishResolutionChoice
  | .resumeProposalCostAfterLeave p savedP =>
    if g.proposalCostPromptStillPayable p savedP then
      g.change (.pending savedP)
    else if g.proposedSpell.any (·.caster == p) then
      let g := g.reverseProposedSpell (resumeContinuation := true) (alwaysGrantPriority := true)
        (followedByFinishChoice := followedByFinishChoice)
        (followedByExplicitPriority? := followedByExplicitPriority?)
      if !g.over && g.pending == .none && g.continuations.isEmpty &&
          g.triggerNeedingTargets.isSome then
        g.promptTriggerTargetsIfNeeded
      else g
    else if g.over then
      g.completeActiveResolutions
    else g
  | .runAfterRandom after =>
    g.runInGameAfterRandom after (guardDeparted := true)
  | .grantLifelinkUntilEot cardId cause =>
    match g.findObject? cardId with
    | some cur =>
      if cur.isOnBattlefield then
        let g := g.createEffect (.keywordsUntilEot cur.id #[Keyword.lifelink]) (cause := cause)
        g.logMsg s!"{g.name cur} gains lifelink until end of turn"
      else g
    | none => g
  | .endTurnAfterCleanupStepEnded =>
    g.endTurnAfterCleanupStepEnded
  | .startNextTurnAndBegin =>
    g.startNextTurnAndBegin
  | .advanceAfterStepEnded =>
    if g.step == .endOfCombat && g.additionalCombatPhases > 0 then
      let g := g.recordPhaseEnded .combat
      if let .chooseReplacement .. := g.pending then
        g.chainPendingReplacement (.beginStepCont .beginningOfCombat)
      else
        g.beginStepCont .beginningOfCombat
    else
      match g.step.next? with
      | some st =>
        let g := g.recordPhaseEnded g.step.phase
        if let .chooseReplacement .. := g.pending then
          g.chainPendingReplacement (.beginStepCont st)
        else
          g.beginStepCont st
      | none => g
  | .recordUntapStepEnded =>
    g.recordStepEnded .untap
  | .untapStepAfterPhaseIn =>
    g.runUntapStepAfterPhaseIn
  | .beginStepAfterPhaseBegan st =>
    g.beginStepAfterPhaseBegan st
  | .beginStepBody st =>
    g.beginStepBody st
  | .exileZemoBoastCards p abilityId remainingIds =>
    g.exileZemoBoastCards p abilityId remainingIds
  | .grantAdventureExilePermission controller cardId cause =>
    match g.followMovedToZone? cardId (· == .exile) with
    | some o =>
      if !g.stillInGame controller then
        g.logMsg s!"{g.name o} is exiled"
      else
        (g.createEffect (.playPermission o.id { player := controller, fromAdventure := true }) (cause := cause))
          |>.logMsg s!"{g.name o} is exiled. {(g.player controller).name} may cast it for as long as it remains exiled (CR 715.3d)"
    | none => g
  | .exileSearchedLinkedLoop p remainingIds sourceId cause pendingFromId =>
    g.exileSearchedLinkedLoop p remainingIds sourceId cause pendingFromId
  | .grantPlayUntilEndOfNextTurn p cardId cause =>
    match g.followMovedToZone? cardId (· == .exile) with
    | some moved =>
      if !g.stillInGame p then
        g.logMsg s!"{(g.player p).name} exiles {g.name moved}"
      else
        (g.createEffect (.playPermission moved.id { player := p } (turnEnds := 2)) (cause := cause))
          |>.logMsg s!"{(g.player p).name} exiles {g.name moved} and may play it until the end of their next turn"
    | none => g
  | .finishExileUntilSourceLeaves sourceId fromId =>
    g.finishExileUntilSourceLeaves sourceId fromId
  | .finishExileForLeaveTrigger sourceId fromId =>
    g.finishExileForLeaveTrigger sourceId fromId
  | .exileTopForPlayLoop fromPlayer caster remaining mayCastStyle cause pendingFromId =>
    g.exileTopForPlayLoop fromPlayer caster remaining mayCastStyle cause pendingFromId
  | .exileTopPlayIfYouControlSubtypeLoop p subtype remaining cause movedId =>
    g.exileTopPlayIfYouControlSubtypeLoop p subtype remaining cause movedId
  | .exileTopMayCastUpToLoop fromPlayer caster remaining casts cause exiled pendingFromId =>
    g.exileTopMayCastUpToLoop fromPlayer caster remaining casts cause exiled pendingFromId
  | .offerMayCastUpToFromExile caster preIds casts =>
    let arrived := preIds.filterMap (fun pid => (g.followMovedToZone? pid (· == Zone.exile)).map GameObject.id)
    g.finishExileTopMayCastUpToOffer caster arrived casts
  | .finishExileUntilNextEndStep controller fromId cause =>
    g.finishExileUntilNextEndStep controller fromId cause
  | .logDiscardedCount p preDiscards =>
    let discarded := g.loggedDiscards p - preDiscards
    g.logMsg s!"{(g.player p).name} discards {discarded} card(s)"
  | .logGiftTreasureGiven recipient =>
    if g.stillInGame recipient then g.logMsg s!"{(g.player recipient).name} is given a Treasure (gift)" else g
  | .logDelayedBirdSoldiersCreated controller startEventIdx =>
    if g.stillInGame controller then
      let cnt := (g.tokensCreatedSince startEventIdx).size
      g.logMsg s!"{(g.player controller).name}'s delayed triggered ability creates {cnt} Bird Soldier token(s)"
    else g
  | .resolveCascadeLoop p maxMv cause exiled pendingFromId =>
    g.resolveCascadeLoop p maxMv cause exiled pendingFromId
  | .exileUntilInstantOrSorceryLoop victim controller castTheCard cause others pendingFromId =>
    g.exileUntilInstantOrSorceryLoop victim controller castTheCard cause others pendingFromId
  | .finishGrimaDirectCast controller victim fromId others cause =>
    g.finishGrimaDirectCast controller victim fromId others cause
  | .exileFromRevealedHandAfterMove p victim fromId cardName sourceId =>
    match g.followMovedToZone? fromId (· == .exile) with
    | some ex =>
      let g := g.changeObject ex.id (.exiledBy sourceId)
      g.logMsg s!"{(g.player p).name} exiles {cardName} from {(g.player victim).name}'s hand"
    | none => g
  | .logExiledIfInExile fromId msg =>
    if (g.followMovedToZone? fromId (· == .exile)).isSome then g.logMsg msg else g
  | .logExpiredPlayFromExile ids startEventIdx =>
    g.logExpiredPlayFromExileIds ids startEventIdx
  | .recordCostSacrificedPower abilityId fromId pw =>
    if !(g.findObject? fromId).any (·.isOnBattlefield) then
      match abilityId with
      | some aid =>
        if (g.findObject? aid).isSome then
          g.setStackEntryLastKnown aid (lastKnownPower := some pw)
        else g
      | none => g
    else g
  | .logReturnedToHand fromId to cardName =>
    if (g.followMovedToZone? fromId (· == .hand to)).isSome then
      g.logMsg s!"{cardName} is returned to {(g.player to).name}'s hand"
    else g
  | .finishPaySneak p spellId attackerId atkTarget cause =>
    let g := g.record (GameEvent.announced g.turnNumber spellId
      (costs := #[.sneak attackerId atkTarget]) (cause := cause))
    g.logMsg s!"{(g.player p).name} pays a sneak cost"
  | .finishMoveToOwnerGraveyardLog fromId fromZone owner cardName reason verb =>
    g.finishMoveToOwnerGraveyardLog fromId fromZone owner cardName reason verb
  | .finishSurveilHandMove p fromId cardName remainingGy cause =>
    let g :=
      if (g.followMovedToZone? fromId (· == .hand p)).isSome then
        g.logMsg s!"{(g.player p).name} puts {cardName} into their hand"
      else g
    g.surveilMoveLoop p remainingGy cause
  | .logPutOnOwnerLibrary fromId owner cardName top msgOverride =>
    if (g.followMovedToZone? fromId (· == .library owner)).isSome then
      let side := if top then "top" else "bottom"
      g.logMsg (msgOverride.getD s!"{(g.player owner).name} puts {cardName} on the {side} of their library")
    else g
  | .finishZemoBoastExileLogs p sourceId preIds =>
    let g := if g.proposedSpell.isSome then g.changeProposal (.choiceCostPaid true) else g
    let exiledCount := (preIds.filter (fun id => (g.followMovedToZone? id (· == .exile)).isSome)).size
    let g :=
      if exiledCount > 0 then
        g.logMsg s!"{(g.player p).name} exiles {exiledCount} card(s) from their graveyard"
      else g
    if g.proposedSpell.isSome then g
    else
      match g.findObject? sourceId with
      | some src => g.logMsg s!"{g.name src}'s boast ability is activated"
      | none => g
  | .markNonManaCostPaid =>
    if g.proposedSpell.isSome then g.changeProposal (.choiceCostPaid true) else g
  | .moveIdsInOrderLoop ids dest log cause placedCount prevMoved =>
    g.moveIdsInOrderLoop ids dest log cause placedCount prevMoved
  | .incrementPlanSource controller sourceId =>
    g.incrementPlanSource controller sourceId
  | .millOpponentsOnly opponents n cause =>
    g.millOpponentsOnly opponents n cause
  | .conniveTricksterTarget caster connive sourceId =>
    g.conniveTricksterTarget caster connive (sourceId := sourceId)
  | .topOrBottomDamageFollowup fromId owner cardName top damage sourceId =>
    let arrived := (g.followMovedToZone? fromId (· == .library owner)).isSome
    let g :=
      if arrived then
        let side := if top then "top" else "the bottom"
        g.logMsg s!"{(g.player owner).name} puts {cardName} on {side} of their library"
      else g
    if arrived && top && damage > 0 then
      g.dealDamageToPlayer owner damage (source := sourceId.bind g.damageSourceById?)
    else g
  | .gainLifePlayer p amount cause =>
    g.gainLife p amount (cause := cause)
  | .drawCardsPlayer p amount cause =>
    g.draw p amount (cause := cause)
  | .sheHulkAfterDamage p startIdx =>
    if g.damageDealtSince startIdx > 0 then
      (g.record (GameEvent.sheHulkDealtDamage g.turnNumber p))
        |>.logMsg "The Sensational She-Hulk deals damage (only once each turn)"
    else g
  | .damageUpToOneAndPlayerLoop controller kind remaining n srcName sourceId cause startEventIdx =>
    g.damageUpToOneAndPlayerLoop controller kind remaining n srcName sourceId cause startEventIdx
  | .applyAggregatedLifelink startEventIdx cause =>
    g.applyAggregatedLifelinkSince startEventIdx (cause := cause)
  | .dealDamageLoseIndestructibleExileTo targetId n source =>
    match (g.findObject? targetId).filter (·.isOnBattlefield) with
    | some o => g.dealDamageLoseIndestructibleExileTo o n source
    | none => g
  | .dealDamageToEachNonSubtypeAndOpponents controller n subtype sourceId cause =>
    g.dealDamageToEachNonSubtypeAndOpponents controller n subtype sourceId (cause := cause)
  | .movePublicCardsToHandLoop p remainingIds maxLeft playerPutsStyle cause pendingCard requirePublicZone =>
    g.movePublicCardsToHandLoop p remainingIds maxLeft playerPutsStyle cause pendingCard requirePublicZone
  | .exileOpponentLibrariesLoop remainingOpps curOpp curIds movedAnyForCur pendingId =>
    g.exileOpponentLibrariesLoop remainingOpps curOpp curIds movedAnyForCur pendingId
  | .logDiscardIfInGraveyard cardId owner msg =>
    if (g.followMovedToZone? cardId (· == .graveyard owner)).isSome then g.logMsg msg else g
  | .chooseCardsToHandLoop p remainingIds cause pendingCard =>
    g.chooseCardsToHandLoop p remainingIds cause pendingCard
  | .logIfCountersIncreased targetId before msg =>
    g.logIfCountersIncreased targetId before msg
  | .afterTriggerTargetsChosen =>
    g.afterTriggerTargetsChosen
  | .finishAbilityResolution snap controller sourceId sagaChapter ab? alreadyResolved =>
    g.finishAbilityResolutionTail snap controller sourceId sagaChapter ab? alreadyResolved

/-- Ask `prop.caster` to choose what pays the first of `picks` (reversing under
CR 733.1 if `cands.size < pick.count`), or finish the activation when none remain. -/
partial def continueCostPicks (g : Game) (prop : ProposedSpell) (picks : Array CostPick)
    (paid : Bool) (hadOuterReplacement : Bool := false)
    (hadOpenContinuation : Option Bool := none) :
    Except String Game := do
  let openCont := g.proposalHadOpenContinuation hadOpenContinuation
  match picks[0]?, prop.sourceId with
  | some pick, some sid =>
    if let .chooseReplacement .. := g.pending then
      let nextPending := Pending.resolutionChoice prop.caster (.costPicks sid picks paid)
      return (g.change (.consecutivePasses 0)).chainPendingReplacement
        (.restorePending nextPending
          (promptLog := some s!"{(g.player prop.caster).name} chooses how to {pick.phrase}"))
    else if !(g.sourceStillPayable prop && g.canPayLife prop.caster prop.payLife) ||
        !g.costPicksPayable prop.caster (some sid)
          (costPicksWithSacrificeOther picks prop.needsSacrificeOther)
          (tapSource := prop.tapSource)
          (sacrificeOrExileSource :=
            prop.sacrificeSource ||
              prop.activation.any (fun a => a.cost.sacrificeSource || a.cost.exileSourceFromBattlefield))
          (discardOrExileHandSource :=
            prop.discardSource ||
              prop.activation.any (fun a => a.cost.discardSource || a.cost.exileSourceFromHand)) then
      g.reverseProposedSpell? (resumeContinuation := true)
    else
      let g := g.changes #[.pending (.resolutionChoice prop.caster (.costPicks sid picks paid)), .consecutivePasses 0]
      return g.logMsg s!"{(g.player prop.caster).name} chooses how to {pick.phrase}"
  | _, _ =>
    if prop.kind == .turnFaceUp then
      if let .chooseReplacement .. := g.pending then
        return (g.change (.consecutivePasses 0)).chainPendingReplacement
          (.finishTurnFaceUp prop.caster prop.spellId hadOuterReplacement)
      else if !(g.stillInGame prop.caster &&
          (g.findObject? prop.spellId).any (fun o =>
            o.isOnBattlefield && o.status.faceDown && g.controlledBy o prop.caster)) then
        g.reverseProposedSpell? (resumeContinuation := true)
      else
        let localOuter? := g.pendingReplacement
        let hadOuter := hadOuterReplacement || localOuter?.isSome
        let g0 := if localOuter?.isSome then g.change (.pendingReplacement none) else g
        let (g, callerShouldResume) :=
          g0.completeTurnFaceUp prop.caster prop.spellId (hadOuterReplacement := hadOuter)
        let g :=
          match localOuter? with
          | some outer =>
            g.chainProposalOuterCont prop.caster outer (hadOuterReplacement := hadOuterReplacement)
              (openCont := openCont)
          | none => g
        return if !hadOuterReplacement && (callerShouldResume ||
            (g.pending == .none && !g.over && localOuter?.isSome)) then
          g.resumeAfterBecomeCast
        else g
    else if let .chooseReplacement .. := g.pending then
      return (g.change (.consecutivePasses 0)).chainPendingReplacement
        (.completeActivation hadOuterReplacement openCont)
    else
      match g.completeActivation prop
          (hadOuterReplacement := hadOuterReplacement)
          (hadOpenContinuation := some openCont) with
      | .ok g' => return g'
      | .error _ => g.reverseProposedSpell? (resumeContinuation := true)

/-- Clear the finished scry or surveil and draw any follow-up cards without
draining outer continuations or granting priority. -/
partial def finishLibraryLookCore (g : Game) : Game :=
  if let .chooseReplacement .. := g.pending then
    g.chainPendingReplacement .finishLibraryLook
  else
    let g := g.changes #[
      .pending .none,
      .surveilReturnMvAtMost none ]
    let g :=
      match g.pendingDrawAfterScry with
      | some (q, n) =>
        let g := g.change (.pendingDrawAfterScry none)
        if g.stillInGame q then g.draw q n else g
      | none => g
    if let .chooseReplacement .. := g.pending then
      g.chainPendingReplacement .finishLibraryLook
    else g

/-- Clear the finished scry or surveil, draw any follow-up cards, and give the
active player priority. -/
partial def finishLibraryLook (g : Game) : Game :=
  g.finishLibraryLookCore.finishAndGrantPriority

/-- Move remaining surveil graveyard cards sequentially, chaining
`finishSurveilPostMove` whenever a move pauses on `Pending.chooseReplacement`. -/
partial def surveilMoveLoop (g : Game) (p : PlayerId) (remainingGy : Array ObjectId)
    (cause : Option EventCause) : Game :=
  if !g.stillInGame p then g
  else
    match remainingGy[0]? with
    | none => g
    | some id =>
      let rest := remainingGy.extract 1 remainingGy.size
      match g.findObject? id with
      | none => g.surveilMoveLoop p rest cause
      | some card =>
        let (g, _) := g.move id (.graveyard p) none (cause := cause)
        if let .chooseReplacement .. := g.pending then
          g.chainPendingReplacement (.finishSurveilPostMove p card id rest cause)
        else
          g.finishSurveilPostMove p card id rest cause

/-- Run post-graveyard-move surveil-to-hand checks and continue `surveilMoveLoop`. -/
partial def finishSurveilPostMove (g : Game) (p : PlayerId) (card : GameObject)
    (fromId : ObjectId) (remainingGy : Array ObjectId) (cause : Option EventCause) : Game :=
  match g.followMovedToZone? fromId (· == Zone.graveyard p) with
  | none =>
    g.surveilMoveLoop p remainingGy cause
  | some gyObj =>
    let g := g.logMsg s!"{(g.player p).name} puts {g.name card} into their graveyard (surveil)"
    if !g.stillInGame p then g
    else
      let returnToHand : Bool :=
        match g.surveilReturnMvAtMost with
        | some n => g.objectManaValue card ≤ n
        | none => false
      if returnToHand then
        let (g', _) := g.move gyObj.id (.hand p) none (cause := cause)
        if let .chooseReplacement .. := g'.pending then
          g'.chainPendingReplacement (.finishPostStep (.finishSurveilHandMove p gyObj.id (g.name card) remainingGy cause))
        else
          let g' :=
            if (g'.followMovedToZone? gyObj.id (· == .hand p)).isSome then
              g'.logMsg s!"{(g'.player p).name} puts {g'.name card} into their hand"
            else g'
          g'.surveilMoveLoop p remainingGy cause
      else
        g.surveilMoveLoop p remainingGy cause

/-- Put remaining counter kinds and any `+1/+1` counter on `targetId` during
proliferate, chaining `.finishProliferateTarget` on `Pending.chooseReplacement`. -/
partial def finishProliferateTarget (g : Game) (p : PlayerId) (targetId : ObjectId)
    (remainingKinds : Array CounterKind) (hasPlusOne : Bool)
    (remainingTargets : Array Target) (permIds : Array ObjectId)
    (playerIds : Array PlayerId) (chosenEmpty : Bool)
    (remainingRounds : Nat) (cause : Option EventCause) : Game :=
  let effCause := g.resolveOptionalCause cause (fallbackCtrl := some p)
  match remainingKinds[0]? with
  | some kind =>
    let restKinds := remainingKinds.extract 1 remainingKinds.size
    let g := g.recordPutCounters targetId kind 1 (byPlayer := some p) (cause := some effCause)
    if let .chooseReplacement .. := g.pending then
      g.chainPendingReplacement (.finishProliferateTarget p targetId restKinds hasPlusOne
        remainingTargets permIds playerIds chosenEmpty remainingRounds cause)
    else
      g.finishProliferateTarget p targetId restKinds hasPlusOne
        remainingTargets permIds playerIds chosenEmpty remainingRounds cause
  | none =>
    let g := g.syncImpendingNotACreature targetId (cause := some effCause)
    if hasPlusOne then
      let g :=
        match g.findObject? targetId with
        | some o => g.addPlusOnePlusOneTo o 1 (byPlayer := some p) (cause := some effCause)
        | none => g
      if let .chooseReplacement .. := g.pending then
        g.chainPendingReplacement (.finishProliferateTarget p targetId #[] false
          remainingTargets permIds playerIds chosenEmpty remainingRounds cause)
      else
        let oName := ((g.findObject? targetId).map g.name).getD "permanent"
        let g := g.logMsg s!"{(g.player p).name} proliferates {oName}"
        g.finishProliferateLoop p remainingTargets (permIds.push targetId) playerIds
          chosenEmpty remainingRounds cause
    else
      let oName := ((g.findObject? targetId).map g.name).getD "permanent"
      let g := g.logMsg s!"{(g.player p).name} proliferates {oName}"
      g.finishProliferateLoop p remainingTargets (permIds.push targetId) playerIds
        chosenEmpty remainingRounds cause

/-- Process remaining proliferate targets and emit `GameEvent.proliferated`. -/
partial def finishProliferateLoop (g : Game) (p : PlayerId)
    (remainingTargets : Array Target) (permIds : Array ObjectId)
    (playerIds : Array PlayerId) (chosenEmpty : Bool)
    (remainingRounds : Nat) (cause : Option EventCause) : Game :=
  let effCause := g.resolveOptionalCause cause (fallbackCtrl := some p)
  match (remainingTargets[0]? : Option Target) with
  | some (Target.permanent id) =>
    let restTargets := remainingTargets.extract 1 remainingTargets.size
    match g.findObject? id with
    | some o =>
      if !o.isOnBattlefield then
        g.finishProliferateLoop p restTargets permIds playerIds chosenEmpty remainingRounds cause
      else
        let bag := o.status.toCounterBag
        let nonPlusKinds := bag.filterMap (fun (k, _) => if k != .plusOnePlusOne then some k else none)
        let hasPlusOne := o.status.plusOnePlusOne > 0
        g.finishProliferateTarget p id nonPlusKinds hasPlusOne restTargets permIds playerIds
          chosenEmpty remainingRounds cause
    | none =>
      g.finishProliferateLoop p restTargets permIds playerIds chosenEmpty remainingRounds cause
  | some (.player pid) =>
    let restTargets := remainingTargets.extract 1 remainingTargets.size
    if !g.stillInGame pid then
      g.finishProliferateLoop p restTargets permIds playerIds chosenEmpty remainingRounds cause
    else
      let pl := g.player pid
      let g :=
        if g.teamPoison pid > 0 && !playerIds.any (g.areTeammates pid ·) then
          let g := g.record (GameEvent.poisoned g.turnNumber pid 1 (byPlayer := some p) (cause := effCause))
          g.logMsg s!"{(g.player p).name} gives {pl.name} another poison counter"
        else g
      let g := pl.counters.foldl (fun acc (kind, cnt) =>
        if kind != .poison && cnt > 0 then
          let acc := acc.record (GameEvent.playerCounters acc.turnNumber pid kind (.put 1)
            (byPlayer := some p) (cause := effCause))
          acc.logMsg s!"{(acc.player p).name} gives {pl.name} another {kind.oracleName} counter"
        else acc) g
      g.finishProliferateLoop p restTargets permIds (playerIds.push pid) chosenEmpty
        remainingRounds cause
  | some (.card _) =>
    let restTargets := remainingTargets.extract 1 remainingTargets.size
    g.finishProliferateLoop p restTargets permIds playerIds chosenEmpty remainingRounds cause
  | none =>
    let g := g.record (GameEvent.proliferated g.turnNumber p
      (permanents := permIds) (players := playerIds) (cause := cause))
    if chosenEmpty then
      g.logMsg s!"{(g.player p).name} proliferates, choosing nothing"
    else g

/-- Finish the post-discard steps of `.mayDiscardDraw`. -/
partial def finishDiscardForDrawMay (g : Game) (p : PlayerId) (n : Nat) : Game :=
  g.draw p n

/-- Finish the post-discard steps of `.chooseDiscardCard`. -/
partial def finishChooseDiscardCard (g : Game) (p : PlayerId) (card : GameObject)
    (remaining : Array PlayerId) : Game :=
  let g := g.finishConniveDiscard card
  if g.thirstDiscardsLeft > 0 then
    let left :=
      if g.hasType card g.thirstDiscardType then 0 else g.thirstDiscardsLeft - 1
    let g := g.change (.thirstDiscardsLeft left)
    if left == 0 then
      if let .chooseReplacement .. := g.pending then
        g.chainPendingReplacement (.finishPostStep .closeDiscardBatchStep)
      else
        (g.change (.pending .none)).closeCurrentDiscardBatch
    else if let .chooseReplacement .. := g.pending then
      g.chainPendingReplacement (.finishPostStep (.beginDiscardCardsStep #[p]))
    else
      g.beginDiscardCards #[p] (resuming := true)
  else if g.pendingDiscardsLeft > 0 then
    let left := g.pendingDiscardsLeft - 1
    let g := g.change (.pendingDiscardsLeft left)
    let perPlayer := max 1 g.discardCountPerPlayer
    let (next, samePlayer) :=
      if left == 0 then (remaining, false) else (#[p] ++ remaining, true)
    if let .chooseReplacement .. := g.pending then
      g.chainPendingReplacement
        (.finishPostStep (.continueAfterDiscardStep next samePlayer perPlayer))
    else
      g.continueAfterDiscard next (samePlayer := samePlayer) (count := perPlayer)
  else
    let perPlayer := max 1 g.discardCountPerPlayer
    if let .chooseReplacement .. := g.pending then
      g.chainPendingReplacement
        (.finishPostStep (.continueAfterDiscardStep remaining false perPlayer))
    else
      g.continueAfterDiscard remaining (samePlayer := false) (count := perPlayer)

/-- Finish the post-discard token creation of `.recruitDiscard`. -/
partial def finishRecruitDiscard (g : Game) (p : PlayerId) (isLand : Bool) : Game :=
  if isLand then g
  else (g.createToken p humanSoldierToken).1

/-- Tap the creatures announced for teamwork at CR 601.2h (CR 702.194 / 601.2h).
Fails with `.error` (triggering CR 733.1 proposal reversal at the caller) if any
announced creature is no longer an untapped creature on the battlefield under
`prop.caster`'s control. -/
partial def tapTeamworkCreaturesForProposed (g : Game) (prop : ProposedSpell) :
    Except String Game := do
  if !prop.teamworkPaid || prop.teamworkCreatures.isEmpty then
    return g
  g.withProposalActionM .costAction fun g => do
    let (g, _) ← g.withBatchExcept
        (some (.costPayment .teamwork prop.caster (some prop.spellId))) fun g => do
      let mut g := g
      for id in prop.teamworkCreatures do
        let some o := g.findObject? id | throw "A creature chosen for teamwork left the battlefield"
        if !(o.isOnBattlefield && g.isCreature o && g.controlledBy o prop.caster && !o.status.tapped) then
          throw s!"{g.name o} can no longer be tapped for teamwork"
        g := g.becomeTapped o (cause := some (.costPayment .teamwork prop.caster (some prop.spellId)))
      return (g, ())
    return g.logMsg s!"{(g.player prop.caster).name} pays a teamwork cost"

/-- Pay a deferred additional-cost behold (`CostItem.behold`) at CR
601.2h (CR 701.4 / 601.2h). Fails with `.error` (triggering CR 733.1 proposal
reversal at the caller) if `prop.caster` no longer controls or holds a card of
the required subtype. -/
partial def payBeholdForProposed (g : Game) (prop : ProposedSpell) :
    Except String Game := do
  match prop.needsBehold with
  | none => return g
  | some quality =>
    let chosenPerm? := (g.permanentsOf prop.caster).find? (fun o => g.hasSubtype o quality) |>.map (·.id)
    let chosenHand? :=
      (g.player prop.caster).hand.find? (fun id =>
        (g.findObject? id).any (fun card => isDiscardableCard card && g.hasSubtype card quality))
    let some chosenId := chosenPerm?.orElse (fun _ => chosenHand?)
      | throw s!"{(g.player prop.caster).name} can no longer behold a {quality}"
    let cause := EventCause.costPayment .behold prop.caster (some prop.spellId)
    g.withProposalActionM .costAction fun g => do
      let g := g.record (GameEvent.announced g.turnNumber prop.spellId
        (costs := #[.behold chosenId]) (cause := some cause))
      return g.beholdQuality prop.caster quality (cause := some cause)

/-- Reverse a proposed spell or activated ability to its pre-proposal checkpoint,
preserving CR 733.1 irreversible library actions, running any deferred post-cast
cleanup, and resuming an active continuation via `finishResolutionChoice` when
`resumeContinuation == true` (CR 601.2 / 602.2 / 733.1–733.2). -/
@[export mtg_game_reverse_proposed_spell_except]
partial def reverseProposedSpell? (g : Game) (resumeContinuation : Bool := false)
    (extraLog : Option String := none)
    (alwaysGrantPriority : Bool := false)
    (skipDepartureReconcile : Bool := false)
    (followedByFinishChoice : Bool := false)
    (followedByExplicitPriority? : Option PlayerId := none) : Except String Game := do
  let hadProposal := g.proposedSpell.isSome
  let (g, needsFinish) ← g.reverseProposedSpellCore?
    (resumeContinuation := resumeContinuation) (extraLog := extraLog)
    (alwaysGrantPriority := alwaysGrantPriority)
    (skipDepartureReconcile := skipDepartureReconcile)
    (followedByFinishChoice := followedByFinishChoice)
    (followedByExplicitPriority? := followedByExplicitPriority?)
  if !needsFinish then
    return g
  else
    match (if !followedByFinishChoice && hadProposal then followedByExplicitPriority? else none) with
    | some prio => return g.finishAndGrantPriority (g.priorityInstead prio)
    | none => return g.finishResolutionChoice

/-- Non-monadic wrapper around `reverseProposedSpell?`. -/
@[export mtg_game_reverse_proposed_spell]
partial def reverseProposedSpell (g : Game) (resumeContinuation : Bool := false)
    (extraLog : Option String := none)
    (alwaysGrantPriority : Bool := false)
    (skipDepartureReconcile : Bool := false)
    (followedByFinishChoice : Bool := false)
    (followedByExplicitPriority? : Option PlayerId := none) : Game :=
  match g.reverseProposedSpell? (resumeContinuation := resumeContinuation)
      (extraLog := extraLog) (alwaysGrantPriority := alwaysGrantPriority)
      (skipDepartureReconcile := skipDepartureReconcile)
      (followedByFinishChoice := followedByFinishChoice)
      (followedByExplicitPriority? := followedByExplicitPriority?) with
  | .ok g' => g'
  | .error msg => g.logMsg msg

/-- Execute the sequential non-mana spell cost stages (`ProposedSpellCostStage`:
`.teamwork` → `.behold` → `.sneak` → `.finalize`), pausing across
`Pending.chooseReplacement` and preserving any enclosing `pendingReplacement`
continuation without shadowing or duplicating it (CR 601.2h / 616.1 / 733.1). -/
partial def finishProposedSpellCosts (g : Game) (stage : ProposedSpellCostStage)
    (grantPriority hadOuterReplacement openCont : Bool)
    (followedByFinishChoice : Bool := false)
    (followedByExplicitPriority? : Option PlayerId := none) : Except String Game := do
  let some prop := g.proposedSpell | return g
  if let .chooseReplacement .. := g.pending then
    return (g.change (.consecutivePasses 0)).chainPendingReplacement
      (.finishProposedSpellCosts stage grantPriority hadOuterReplacement openCont)
  let localOuter? := g.pendingReplacement
  let hadOuter := hadOuterReplacement || localOuter?.isSome
  let chainOuter (gCur : Game) (outer : PendingReplacement) : Game :=
    gCur.chainProposalOuterCont prop.caster outer (grantPriority := grantPriority)
      (hadOuterReplacement := hadOuterReplacement) (openCont := openCont)
  let g0 := if localOuter?.isSome then g.change (.pendingReplacement none) else g
  match stage with
  | .teamwork =>
    if prop.teamworkPaid && !prop.teamworkCreatures.isEmpty then
      match g0.tapTeamworkCreaturesForProposed prop with
      | .ok g =>
        if let .chooseReplacement .. := g.pending then
          let g := g.chainPendingReplacement
            (.finishProposedSpellCosts .behold grantPriority hadOuter openCont)
          return match localOuter? with
            | some outer => chainOuter g outer
            | none => g
        else
          let g := match localOuter? with
            | some outer => g.chainPendingReplacement outer
            | none => g
          g.finishProposedSpellCosts .behold grantPriority hadOuterReplacement openCont
            (followedByFinishChoice := followedByFinishChoice)
            (followedByExplicitPriority? := followedByExplicitPriority?)
      | .error _ =>
        g.reverseProposedSpell? (resumeContinuation := true)
          (followedByFinishChoice := followedByFinishChoice)
          (followedByExplicitPriority? := followedByExplicitPriority?)
    else
      g.finishProposedSpellCosts .behold grantPriority hadOuterReplacement openCont
        (followedByFinishChoice := followedByFinishChoice)
        (followedByExplicitPriority? := followedByExplicitPriority?)
  | .behold =>
    if prop.needsBehold.isSome then
      match g0.payBeholdForProposed prop with
      | .ok g =>
        if let .chooseReplacement .. := g.pending then
          let g := g.chainPendingReplacement
            (.finishProposedSpellCosts .sneak grantPriority hadOuter openCont)
          return match localOuter? with
            | some outer => chainOuter g outer
            | none => g
        else
          let g := match localOuter? with
            | some outer => g.chainPendingReplacement outer
            | none => g
          g.finishProposedSpellCosts .sneak grantPriority hadOuterReplacement openCont
            (followedByFinishChoice := followedByFinishChoice)
            (followedByExplicitPriority? := followedByExplicitPriority?)
      | .error _ =>
        g.reverseProposedSpell? (resumeContinuation := true)
          (followedByFinishChoice := followedByFinishChoice)
          (followedByExplicitPriority? := followedByExplicitPriority?)
    else
      g.finishProposedSpellCosts .sneak grantPriority hadOuterReplacement openCont
        (followedByFinishChoice := followedByFinishChoice)
        (followedByExplicitPriority? := followedByExplicitPriority?)
  | .sneak =>
    match prop.sneakAttacker with
    | some a =>
      match g0.withProposalActionM .costAction (fun g => g.paySneak prop.caster prop.spellId a) with
      | .ok g =>
        if let .chooseReplacement .. := g.pending then
          let g := g.chainPendingReplacement
            (.finishProposedSpellCosts .finalize grantPriority hadOuter openCont)
          return match localOuter? with
            | some outer => chainOuter g outer
            | none => g
        else
          let g := match localOuter? with
            | some outer => g.chainPendingReplacement outer
            | none => g
          g.finishProposedSpellCosts .finalize grantPriority hadOuterReplacement openCont
            (followedByFinishChoice := followedByFinishChoice)
            (followedByExplicitPriority? := followedByExplicitPriority?)
      | .error _ =>
        g.reverseProposedSpell? (resumeContinuation := true)
          (followedByFinishChoice := followedByFinishChoice)
          (followedByExplicitPriority? := followedByExplicitPriority?)
    | none =>
      g.finishProposedSpellCosts .finalize grantPriority hadOuterReplacement openCont
        (followedByFinishChoice := followedByFinishChoice)
        (followedByExplicitPriority? := followedByExplicitPriority?)
  | .finalize =>
    if prop.needsSacrificeOther then
      let excludeId := prop.sourceId.getD prop.spellId
      if (g0.sacrificeCreatureOrArtifactChoices prop.caster excludeId).isEmpty then
        return (← g.reverseProposedSpell? (resumeContinuation := true)
          (followedByFinishChoice := followedByFinishChoice)
          (followedByExplicitPriority? := followedByExplicitPriority?))
      let g := match localOuter? with
        | some outer => g0.chainPendingReplacement outer
        | none => g0
      let g := g.changes #[.pending (.sacrificePermanent prop.caster excludeId), .consecutivePasses 0]
      return g.logMsg s!"{(g.player prop.caster).name} must sacrifice an artifact or creature"
    else if prop.needsDiscardCard then
      if (g0.discardableHandIds prop.caster).isEmpty then
        return (← g.reverseProposedSpell? (resumeContinuation := true)
          (followedByFinishChoice := followedByFinishChoice)
          (followedByExplicitPriority? := followedByExplicitPriority?))
      let g := match localOuter? with
        | some outer => g0.chainPendingReplacement outer
        | none => g0
      let g := g.changes #[.pending (.discardForAdditionalCost prop.caster), .consecutivePasses 0]
      return g.logMsg s!"{(g.player prop.caster).name} must discard a card"
    else if prop.kind == .turnFaceUp then
      if !(g0.stillInGame prop.caster &&
          (g0.findObject? prop.spellId).any (fun o =>
            o.isOnBattlefield && o.status.faceDown && g0.controlledBy o prop.caster)) then
        return (← g.reverseProposedSpell? (resumeContinuation := true)
          (followedByFinishChoice := followedByFinishChoice)
          (followedByExplicitPriority? := followedByExplicitPriority?))
      let g := g0.changes #[.pending .none, .consecutivePasses 0]
      let (g, callerShouldResume) :=
        g.completeTurnFaceUp prop.caster prop.spellId (hadOuterReplacement := hadOuter)
          (followedByFinishChoice := followedByFinishChoice)
          (followedByExplicitPriority? := followedByExplicitPriority?)
      let g :=
        match localOuter? with
        | some outer => chainOuter g outer
        | none => g
      let paused := match g.pending with | .chooseReplacement .. => true | _ => false
      if paused || hadOuterReplacement then
        return g
      else if callerShouldResume || (!g.over && g.pending == .none && localOuter?.isSome) then
        return g.resumeAfterBecomeCast
      else
        return g
    else
      if !(g0.stillInGame prop.caster && (g0.findObject? prop.spellId).any (·.zone == .stack)) then
        return (← g.reverseProposedSpell? (resumeContinuation := true)
          (followedByFinishChoice := followedByFinishChoice)
          (followedByExplicitPriority? := followedByExplicitPriority?))
      let isResCast := prop.resolutionCast
      let g := g0.changes #[.pending .none, .consecutivePasses 0]
      let g := g.becomeCast prop.caster (g.object! prop.spellId)
        (grantPriority := grantPriority)
        (hadOuterReplacement := hadOuter)
        (hadOpenContinuation := some openCont)
      let paused := match g.pending with | .chooseReplacement .. => true | _ => false
      if paused then
        let g :=
          match localOuter? with
          | some outer => chainOuter g outer
          | none =>
            if isResCast && !hadOuterReplacement && !g.anyContinuationSettlesControlFlow then
              g.chainPendingReplacement .finishResolutionChoice
            else g
        return g
      else
        let g :=
          match localOuter? with
          | some outer => chainOuter g outer
          | none => g
        if hadOuterReplacement then
          return g
        else if isResCast then
          if (match g.pending with | .chooseReplacement .. => true | _ => false) &&
              g.anyContinuationSettlesControlFlow then
            return g
          else
            return g.finishResolutionChoice
        else
          return g.resumeAfterBecomeCast

/-- Announce `{X}`, modes, additional/optional costs, and targets of a spell
cast while an ability resolves (CR 601.2b–c), then finish casting it. A spell
that needs a target but has none can't be cast and returns to where it was
(CR 601.2c / 733.1). -/
partial def beginResolutionCastTargets (g : Game) (p : PlayerId) (prop : ProposedSpell) :
    Game :=
  let prop := { prop with resolutionCast := true }
  let g := g.change (.proposedSpell (some prop))
  let spell := g.object! prop.spellId
  let face := g.baseCard spell
  let hasMorphChoice := !prop.kickerAnnounced && g.proposalCanChooseMorph prop
  let needsKicker :=
    !prop.kickerAnnounced &&
      (face.kicker.isSome || hasMorphChoice || g.proposalCanChooseImpending prop)
  if hasMorphChoice then
    g.change (.pending (.chooseKicker p))
      |>.logMsg s!"{(g.player p).name} may kick the spell (CR 702.33 / 601.2b)"
  else if prop.cost.containsX then
    g.change (.pending (.chooseX p))
      |>.logMsg s!"{(g.player p).name} must choose a value for X (CR 107.3a / 601.2b)"
  else if isModalSpellFace face then
    let tcs := g.evalLayer3 spell
    if !(effectiveSpellModes face).any (fun e =>
        let m := if tcs.isEmpty then e else TextChange.applyEffect tcs e
        g.spellModeIsChoosable p m (some prop.spellId)) &&
        !isReturnUpToTwoGyModal face && !face.allowsZeroTargets then
      g.reverseProposedSpell (resumeContinuation := true)
    else
      g.change (.pending (.chooseMode p))
        |>.logMsg s!"{(g.player p).name} must choose a mode (CR 601.2b)"
  else if face.announcesAdditionalCost then
    g.change (.pending (.chooseAdditionalCost p))
      |>.logMsg s!"{(g.player p).name} must choose an additional cost (CR 601.2b)"
  else if needsKicker then
    g.change (.pending (.chooseKicker p))
      |>.logMsg s!"{(g.player p).name} may kick the spell (CR 702.33 / 601.2b)"
  else if face.hasGift && !prop.giftAnnounced then
    g.change (.pending (.chooseGift p))
      |>.logMsg s!"{(g.player p).name} may promise a gift (CR 702.174)"
  else if face.teamwork.isSome && !prop.teamworkAnnounced then
    g.change (.pending (.chooseTeamwork p))
      |>.logMsg s!"{(g.player p).name} may pay a teamwork cost (CR 702.194)"
  else if g.proposedNeedsTarget prop then
    -- CR 601.2c / 702.33d,g: check the targeting of the spell as proposed (kicked or not).
    let zeroOk := face.allowsZeroTargets ||
      (g.currentSpellEffect spell).any (·.allowsZeroTargets) ||
      g.canSkipCurrentOptionalSlot spell
    let noLegal :=
      if g.isAura spell && (g.currentSpellEffect spell).isNone then
        (g.legalAuraTargets p face (some spell.id)).isEmpty
      else
        (g.legalProposedTargets p spell).isEmpty ||
          (g.currentSpellEffect spell).any (fun eff =>
            eff.requiresTarget && !g.effectHasEnoughTargets p eff (some spell.id))
    if noLegal && !zeroOk then
      g.reverseProposedSpell (resumeContinuation := true)
        (extraLog := some s!"{face.name} has no legal target and can't be cast")
    else
      let what := if g.isAura spell then "a target to enchant" else "a target"
      g.change (.pending (.chooseTargets p))
        |>.logMsg s!"{(g.player p).name} must choose {what} (CR 601.2c)"
  else if prop.cost.includesManaPayment || prop.payLife > 0 || prop.needsSacrificeOther || prop.needsDiscardCard then
    g.change (.pending (.activateManaAbilities p))
      |>.logMsg s!"{(g.player p).name} may activate mana abilities (CR 601.2g)"
  else
    let outerCont? := g.pendingReplacement
    let openCont := g.proposalHadOpenContinuation
    let g0 := if outerCont?.isSome then g.change (.pendingReplacement none) else g
    match g0.tapTeamworkCreaturesForProposed prop with
    | .error _ => g.reverseProposedSpell (resumeContinuation := true)
    | .ok g1 =>
      if let .chooseReplacement .. := g1.pending then
        let g1 := g1.chainPendingReplacement
          (.finishProposedSpellCosts .behold false outerCont?.isSome openCont)
        match outerCont? with
        | some outer => g1.chainProposalOuterCont p outer (grantPriority := false) (openCont := openCont)
        | none => g1
      else
        match g1.payBeholdForProposed prop with
        | .error _ => g.reverseProposedSpell (resumeContinuation := true)
        | .ok g =>
          let pausedPreCast := match g.pending with | .chooseReplacement .. => true | _ => false
          let g := if pausedPreCast then g else g.change (.pending .none)
          let g := g.becomeCast p (g.object! prop.spellId) (grantPriority := false)
            (hadOuterReplacement := outerCont?.isSome)
            (hadOpenContinuation := some openCont)
          let isResolutionChoicePrompt := match g.pending with | .resolutionChoice .. => true | _ => false
          if g.pending != .none || g.afterRandom != .none then
            match outerCont? with
            | some outer =>
              if isResolutionChoicePrompt then g.chainPendingReplacement outer
              else g.chainProposalOuterCont p outer (grantPriority := false) (openCont := openCont)
            | none =>
              if openCont && !isResolutionChoicePrompt && !g.anyContinuationSettlesControlFlow then
                g.chainPendingReplacement .finishResolutionChoice
              else g
          else
            match outerCont? with
            | some outer => g.chainPendingReplacement outer
            | none => g

/-- Put a card onto the stack as an ability is resolving. Timing may be
ignored. The permission does not last after this ability finishes.
An Aura still announces a target to enchant (CR 601.2c / 303.4). -/
partial def castAsPartOfResolution (g : Game) (p : PlayerId) (id : ObjectId)
    (ignoreTiming := true) (withoutManaCost := true)
    (exileInstantSorceryInstead := false) (callerCheckpoint := false) : Game :=
  let clearCkpt (g : Game) : Game :=
    if g.proposalCheckpoint.isSome then g.change .clearProposalCheckpoint else g
  match g.findObject? id with
  | none => (clearCkpt g).logMsg "There is no card to cast"
  | some o =>
    if !isCastableObject o then
      (clearCkpt g).logMsg s!"{g.name o} can't be cast"
    else
    let face := { g.baseCard o with keywords := g.currentKeywords o }
    let rawPerm :=
      if withoutManaCost then none
      else g.paidResolutionOrigPerm? p o ignoreTiming (face? := some face)
    let hasZonePerms :=
      !(g.playPermissionsFor p o).isEmpty || (o.zone == .exile && g.mayCastExiledBySource p o)
    let cleanPerms :=
      (g.playPermissionsFor p o).filter (fun pm =>
        !pm.withoutManaCost && !pm.payLifeEqualManaValue && pm.prepareSource.isNone) ++
      (if o.zone == .exile && g.mayCastExiledBySource p o then
        #[{ player := p, anyMana := true }]
       else #[]) ++
      (if !withoutManaCost then
        #[{ player := p, ignoreTiming := ignoreTiming }]
       else #[])
    let morphTimingOk :=
      ignoreTiming ||
        (if hasZonePerms then
          cleanPerms.any (fun pm => pm.ignoreTiming || g.timingAllowsCast p morphSpellFace (ignorePending := true))
         else
          g.timingAllowsCast p morphSpellFace (ignorePending := true))
    let canMorph :=
      !withoutManaCost && face.morph.isSome && face.kicker.isNone &&
        o.zone != .graveyard o.owner &&
        !g.spellNameForbidden "" &&
        morphTimingOk
    let frontTimingOk :=
      ignoreTiming || rawPerm.any (·.ignoreTiming) ||
        g.timingAllowsCast p face (ignorePending := true) (card? := some o)
    let frontLegalExceptTiming :=
      !g.spellNameForbidden face.name && g.graveyardCastThresholdMet p o.id face
    if g.cantCastSpellsThisTurn p then
      (clearCkpt g).logMsg "You can't cast spells this turn (CR 101.2)"
    else if g.splitSecondOnStack then
      (clearCkpt g).logMsg s!"{g.name o} can't be cast while a spell with split second is on the stack (ruling 839)"
    else if g.combatLocksNonManaAbilities then
      (clearCkpt g).logMsg "During combat, players can't cast spells (Yuriko, Blade of the Mighty)"
    else if g.opponentsCantCastOnActiveTurn p then
      (clearCkpt g).logMsg "Opponents can't cast spells during that player's turn"
    else if !canMorph && g.spellNameForbidden face.name then
      (clearCkpt g).logMsg s!"Spells named {face.name} can't be cast"
    else if !canMorph && !g.graveyardCastThresholdMet p o.id face then
      (clearCkpt g).logMsg s!"{face.name} cannot be cast right now"
    else if !(if frontLegalExceptTiming then frontTimingOk || canMorph else canMorph) then
      (clearCkpt g).logMsg s!"{g.name o} cannot be cast now (timing)"
    else
      let name := g.name o
      let original := o
      let origSnap := g.snapshot o
      let fromGy := original.zone == .graveyard original.owner
      let origPerm : Option PlayPermission :=
        if withoutManaCost then
          some { player := p, withoutManaCost := true, ignoreTiming := ignoreTiming }
        else
          some (rawPerm.getD { player := p, ignoreTiming := ignoreTiming })
      let altCostUsed :=
        withoutManaCost ||
          origPerm.any (fun pm => pm.withoutManaCost || pm.payLifeEqualManaValue)
      let wasCopy := original.isCopy
      let g :=
        if callerCheckpoint && g.proposalCheckpoint.isSome then g
        else
          let g := g.change .saveProposalCheckpoint
          match g.pendingReplacement with
          | some outer =>
            let g := if g.continuations.isEmpty then g.change (.pushContinuationFrame {}) else g
            g.changes #[.pushOuterPendingReplacement outer, .pendingReplacement none]
          | none => g
      let (g, newId) := g.move id .stack (some p) (verb := some .cast) (actor := some p)
        (isCopy := some wasCopy)
      match (g.findObject? newId).filter (·.zone == .stack) with
      | none =>
        (clearCkpt g).logMsg s!"{name} cannot be moved to the stack"
      | some spellObj =>
        let g :=
          if exileInstantSorceryInstead && fromGy then
            g.createEffect (.exileInstantSorceryInstead newId)
          else g
        let stackFace := g.baseCard spellObj
        let g := g.putStackEntry p newId
        let way : CastWay :=
          if withoutManaCost then .alternative "withoutManaCost"
          else if rawPerm.isSome then .alternative "permission"
          else .normal
        let g := g.record (GameEvent.proposed g.turnNumber newId p original.zone way)
        let g := g.logMsg s!"{(g.player p).name} casts {name} as the ability resolves"
        let preSpell := { spellObj with
          id := original.id
          zone := original.zone
          exiledBy := original.exiledBy
          controller := some p }
        -- CR 702.34a: casting as an ability resolves is never a Flashback cast, so a
        -- graveyard card (Bilbo's `mayCastFromGraveyard`) pays its normal mana cost.
        let cost := g.playManaCost preSpell stackFace (origPerm := origPerm)
          (flashback := some false)
          (explicitAltCost := false)
          (useImplicitPermissions := false)
        let lifeInstead :=
          if !withoutManaCost && origPerm.any (·.payLifeEqualManaValue) then
            g.objectManaValue spellObj
          else 0
        let needsSacrifice := (g.mandatorySacrificeFilterFor? spellObj stackFace).isSome
        g.beginResolutionCastTargets p {
          caster := p
          cost
          spellId := newId
          original
          originalSnapshot := origSnap
          origPerm
          needsSacrificeOther := needsSacrifice
          payLife := lifeInstead
          alternativeCost := altCostUsed
          resolutionCast := true
          resolutionIgnoreTiming := ignoreTiming
        }

/-- Resume any deferred `PendingReplacement` (such as `.finishResolutionChoice`) queued
by `becomeCast` or `becomeActivated` once the spell or ability finishes going
onto the stack without opening a new `Pending`. -/
@[export mtg_game_resume_after_become_cast]
partial def resumeAfterBecomeCast (g : Game) : Game :=
  if g.pending == .none && g.pendingReplacement.isSome && !g.over then
    match g.pendingReplacement with
    | some cont => (g.change (.pendingReplacement none)).resumePendingReplacement cont
    | none => g
  else g

/-- Cast one looked-at card as Cosmic Cube resolves, or decline (`none`). -/
partial def chooseCastFromLooked (g : Game) (p : PlayerId) (castId : Option ObjectId) :
    Except String Game := do
  match g.pending with
  | .mayCastFromLooked q ids maxMv =>
    if p != q then
      throw s!"Only {(g.player q).name} may choose whether to cast a spell"
    match castId with
    | none =>
      let outerCont? := g.pendingReplacement
      let g := if outerCont?.isSome then g.change (.pendingReplacement none) else g
      let g := (g.change (.pending .none)).logMsg s!"{(g.player p).name} declines to cast a spell"
      let rest :=
        ids.filter (fun id =>
          match g.findObject? id with
          | some o => o.zone == .library p
          | none => false)
      let msg :=
        s!"{(g.player p).name} puts the rest on the bottom of their library in a random order"
      let g := if rest.isEmpty then g else g.requestOrderInto rest (.library p) msg
      let g := g.reattachOuterCont outerCont?
      return g.finishResolutionChoice
    | some id =>
      match g.mayCastFromLookedError p ids maxMv id with
      | some err => throw err
      | none =>
        -- CR 733.1 / 601.2: checkpoint while the Cosmic Cube choice is still pending, so
        -- reversing an illegal proposal restores `mayCastFromLooked` (cards still on top,
        -- no continuation frame or bottoming cleanup yet).
        let g := g.change .saveProposalCheckpoint
        let g :=
          if g.continuations.isEmpty then g.change (.pushContinuationFrame {}) else g
        let g :=
          match g.pendingReplacement with
          | some outer =>
            g.changes #[.pushOuterPendingReplacement outer, .pendingReplacement none]
          | none => g
        let g := g.changes #[
          .postCastCleanup (some (.lookedBottom p id ids)),
          .pending .none
        ]
        let g := g.castAsPartOfResolution p id (callerCheckpoint := true)
        if g.pending != .none then
          return g
        else if g.proposedSpell.isNone && g.postCastCleanup.isSome then
          let g := g.runPostCastCleanup
          return g.finishResolutionChoice
        else if (g.followMovedToZone? id (· == .stack)).isSome then
          return g.finishResolutionChoice
        else
          return g
  | _ => throw "Not time to choose a spell from among looked-at cards"

/-- After a trigger's targets (and any damage division) are fully announced,
prompt the next trigger that needs targets or continue the CR 603.3b
process (remaining waiting triggers, then SBAs). -/
partial def afterTriggerTargetsChosen (g : Game) : Game :=
  if g.over then
    let g :=
      if g.proposedSpell.any (fun prop =>
          !g.stillInGame prop.caster || (g.findObject? prop.spellId).isNone) then
        (if g.pending == .none || g.sbaPaused then g else g.change (.pending .none)).reverseProposedSpell
          (resumeContinuation := true) (alwaysGrantPriority := true)
      else g
    g.completeActiveResolutions
  else if g.sbaPaused then
    g.chainPendingReplacement (.finishPostStep .afterTriggerTargetsChosen)
  else
    let g :=
      match g.pending with
      | .chooseTargets _ => g.change (.pending .none)
      | _ => g
    if g.pending != .none || g.afterRandom != .none then
      g
    else if g.proposedSpell.isNone &&
        (g.pendingMayCastFromExile.isSome || g.pendingFreeCopies.isSome) then
      let g := g.reopenDeferredExileCasts
      if let .chooseReplacement .. := g.pending then
        if g.anyContinuationSettlesControlFlow then g
        else g.chainPendingReplacement .finishResolutionChoice
      else if g.pending != .none || g.afterRandom != .none then g
      else if g.currentInterpWait?.isSome ||
          g.pendingReplacement.isSome || !g.outerPendingReplacements.isEmpty then
        g.finishResolutionChoice
      else g.afterTriggerTargetsChosen
    else
      match g.triggerNeedingTargets with
      | some _ =>
        g.promptTriggerTargetsIfNeeded
      | none =>
        if g.proposedSpell.any (fun prop =>
            !g.stillInGame prop.caster || (g.findObject? prop.spellId).isNone) then
          let g :=
            g.reverseProposedSpell (resumeContinuation := true) (alwaysGrantPriority := true)
          if !g.over && g.pending == .none && g.continuations.isEmpty &&
              g.triggerNeedingTargets.isSome then
            g.promptTriggerTargetsIfNeeded
          else g
        else if g.proposedSpell.isSome then
          g
        else
          let prio := g.pendingPriority.getD g.activePlayer
          receivePriority g prio false

/-- Start paying the proposed activation's costs that need chosen objects,
reversing it if they can't be paid (CR 601.2h / 733.1). -/
partial def beginActivationPayment (g : Game) (prop : ProposedSpell) : Except String Game := do
  if g.over || !g.stillInGame prop.caster ||
      (prop.sourceId != some prop.spellId && !(g.findObject? prop.spellId).any (·.zone == .stack)) ||
      !g.sourceStillPayable prop || !g.canPayLife prop.caster prop.payLife then
    return (← g.reverseProposedSpell? (resumeContinuation := true))
  let picks := (prop.activation.map costPicksOf).getD #[]
  let allPicks := costPicksWithSacrificeOther picks prop.needsSacrificeOther
  let sacSrc :=
    prop.sacrificeSource ||
      prop.activation.any (fun a => a.cost.sacrificeSource || a.cost.exileSourceFromBattlefield)
  let discSrc :=
    prop.discardSource ||
      prop.activation.any (fun a => a.cost.discardSource || a.cost.exileSourceFromHand)
  let payable :=
    match prop.sourceId with
    | some sid =>
      allPicks.isEmpty ||
        g.costPicksPayable prop.caster (some sid) allPicks
          (tapSource := prop.tapSource)
          (sacrificeOrExileSource := sacSrc)
          (discardOrExileHandSource := discSrc)
    | none => true
  if !prop.choiceCostPaid then
    match prop.sourceId with
    | some sid =>
      if prop.activation.any (·.cost.exileManaSymbols?.isSome) then
        let col :=
          match g.findObject? sid <|> some prop.original with
          | some src => TextChange.applyColor (g.evalLayer3 src) .black
          | none => .black
        let allCands := (g.player prop.caster).graveyard.filter (fun id =>
          (g.findObject? id).any (fun card => isDiscardableCard card && (g.colors card).contains col))
        if !payable || !g.canPayZemoBoast prop.caster allCands col then
          return (← g.reverseProposedSpell? (resumeContinuation := true))
        let prompt := s!"{(g.player prop.caster).name} chooses black cards to exile from their graveyard"
        if let .chooseReplacement .. := g.pending then
          return (g.change (.consecutivePasses 0)).chainPendingReplacement
            (.restorePending (.resolutionChoice prop.caster (.zemoBoastExile prop.spellId sid))
              (promptLog := some prompt))
        let g := g.changes #[
          .pending (.resolutionChoice prop.caster (.zemoBoastExile prop.spellId sid)),
          .consecutivePasses 0]
        return g.logMsg prompt
      else if let some n := prop.activation.bind (·.cost.crewPower?) then
        let crewOk :=
          (g.firstPayableCrewSelection? prop.caster sid n allPicks
            (tapSource := prop.tapSource)
            (sacrificeOrExileSource := sacSrc)
            (discardOrExileHandSource := discSrc)).isSome
        if !payable || !crewOk then
          return (← g.reverseProposedSpell? (resumeContinuation := true))
        let fallbackName :=
          if prop.originalSnapshot.name.isEmpty then g.name prop.original
          else prop.originalSnapshot.name
        let vName := ((g.findObject? sid).map g.name).getD fallbackName
        let prompt :=
          s!"{(g.player prop.caster).name} chooses untapped creatures with total power {n} or more to crew {vName}"
        if let .chooseReplacement .. := g.pending then
          return (g.change (.consecutivePasses 0)).chainPendingReplacement
            (.restorePending (.resolutionChoice prop.caster (.crew prop.spellId sid n))
              (promptLog := some prompt))
        let g := g.changes #[
          .pending (.resolutionChoice prop.caster (.crew prop.spellId sid n)),
          .consecutivePasses 0]
        return g.logMsg prompt
    | none => pure ()
  if !payable then return (← g.reverseProposedSpell? (resumeContinuation := true))
  let g ← g.continueCostPicks prop picks (prop.cost.includesManaPayment || prop.choiceCostPaid)
  if g.proposedSpell.isNone && !(g.findObject? prop.spellId).any (fun o => o.zone == .stack) then
    return g
  return g.resumeAfterBecomeCast

/-- Continue after CR 601.2c: determine the total cost (601.2f), then mana
abilities (601.2g). Additional-cost *choices* are announced earlier, at 601.2b. -/
partial def afterTargetsChosen (g : Game) : Game :=
  match g.proposedSpell with
  | none => g
  | some _ =>
    let g := g.lockInTargetCostReduction
    match g.proposedSpell with
    | none => g
    | some prop =>
      if prop.cost.includesManaPayment || prop.payLife > 0 || prop.needsSacrificeOther ||
          prop.needsDiscardCard then
        (g.change (.pending (.activateManaAbilities prop.caster))).logMsg
          s!"{(g.player prop.caster).name} may activate mana abilities (CR 601.2g)"
      else if prop.kind == .activatedAbility then
        match g.beginActivationPayment prop with
        | .ok g => g
        | .error _ => g.reverseProposedSpell (resumeContinuation := true)
      else
        let isResCast := prop.resolutionCast
        let openCont := g.proposalHadOpenContinuation
        match g.finishProposedSpellCosts .teamwork (!isResCast) false openCont with
        | .ok g => g
        | .error _ => g.reverseProposedSpell (resumeContinuation := true)

/-- After CR 601.2b additional-cost announcement, continue through optional
costs (kicker, gift, teamwork), then targets (601.2c) or cost determination (601.2f). -/
partial def afterAdditionalCostAnnounced (g : Game) : Game :=
  match g.proposedSpell, g.proposedSpell.bind (fun prop => g.findObject? prop.spellId) with
  | some prop, some spell =>
    let p := prop.caster
    let face := g.baseCard spell
    let needsKicker :=
      !prop.kickerAnnounced &&
        (face.kicker.isSome || g.proposalCanChooseMorph prop || g.proposalCanChooseImpending prop)
    if needsKicker then
      (g.change (.pending (.chooseKicker p))).logMsg
        s!"{(g.player p).name} may kick the spell (CR 702.33 / 601.2b)"
    else if face.hasGift && !prop.giftAnnounced then
      (g.change (.pending (.chooseGift p))).logMsg
        s!"{(g.player p).name} may promise a gift (CR 702.174)"
    else if face.teamwork.isSome && !prop.teamworkAnnounced then
      (g.change (.pending (.chooseTeamwork p))).logMsg
        s!"{(g.player p).name} may pay a teamwork cost (CR 702.194)"
    else if g.proposedNeedsTarget prop then
      -- CR 601.2c / 702.33d,g / 733.1: the targets announced now are those of the spell as
      -- proposed (kicked or not). A target-replacing kicker may have been the only route to
      -- a legal target; declining it (or kicking with no kicked target) leaves no legal
      -- choice, so the proposal is reversed for every cast, not only resolution casts.
      let zeroOk := face.allowsZeroTargets ||
        (g.currentSpellEffect spell).any (·.allowsZeroTargets) ||
        g.canSkipCurrentOptionalSlot spell
      let noLegal :=
        if g.isAura spell && (g.currentSpellEffect spell).isNone then
          (g.legalAuraTargets p face (some spell.id)).isEmpty
        else
          (g.legalProposedTargets p spell).isEmpty ||
            (g.currentSpellEffect spell).any (fun eff =>
              eff.requiresTarget && !g.effectHasEnoughTargets p eff (some spell.id))
      if prop.kind == .spell && noLegal && !zeroOk then
        g.reverseProposedSpell (resumeContinuation := true)
          (extraLog := some s!"{face.name} has no legal target and can't be cast")
      else
        let what := if g.isAura spell then "a target to enchant" else "a target"
        (g.change (.pending (.chooseTargets p))).logMsg
          s!"{(g.player p).name} must choose {what} (CR 601.2c)"
    else
      g.afterTargetsChosen
  | some prop, none =>
    if g.proposedNeedsTarget prop then
      (g.change (.pending (.chooseTargets prop.caster))).logMsg
        s!"{(g.player prop.caster).name} must choose a target (CR 601.2c)"
    else
      g.afterTargetsChosen
  | none, _ => g

/-- After the modes are chosen: additional costs, kicker, gift, and teamwork,
then targets (CR 601.2b–c). -/
partial def afterModesChosen (g : Game) (p : PlayerId) : Game :=
  match g.proposedSpell, g.proposedSpell.bind (fun prop => g.findObject? prop.spellId) with
  | some prop, some spell =>
    let face := g.baseCard spell
    let needsKicker :=
      !prop.kickerAnnounced &&
        (face.kicker.isSome || g.proposalCanChooseMorph prop || g.proposalCanChooseImpending prop)
    if face.announcesAdditionalCost then
      (g.change (.pending (.chooseAdditionalCost p))).logMsg
        s!"{(g.player p).name} must choose an additional cost (CR 601.2b)"
    else if needsKicker then
      (g.change (.pending (.chooseKicker p))).logMsg
        s!"{(g.player p).name} may kick the spell (CR 702.33 / 601.2b)"
    else if face.hasGift && !prop.giftAnnounced then
      (g.change (.pending (.chooseGift p))).logMsg s!"{(g.player p).name} may promise a gift (CR 702.174)"
    else if face.teamwork.isSome && !prop.teamworkAnnounced then
      (g.change (.pending (.chooseTeamwork p))).logMsg
        s!"{(g.player p).name} may pay a teamwork cost (CR 702.194)"
    else g.afterAdditionalCostAnnounced
  | _, _ => g

/-- Finish an in-game `--norandom` result after re-attaching any outer
`g.pendingReplacement` continuation: drain active continuations, chain
`.receivePriority` on a CR 616.1 pause, or grant priority and complete active
resolutions when idle. -/
partial def finishHostRandom (g : Game) : Game :=
  if g.over then g.completeActiveResolutions
  else if !g.openingHandsPending && !g.players.isEmpty &&
      g.afterRandom == .none && g.pendingRandom?.isNone then
    let g := finishAndGrantPriority g
    if g.over || (g.pending == .none && g.afterRandom == .none) then
      g.completeActiveResolutions
    else g
  else g

/-- Execute an in-game `AfterRandom` continuation (used by `finishAfterRandom`
and `PostStep.runAfterRandom`). -/
partial def runInGameAfterRandom (g : Game) (after : AfterRandom)
    (guardDeparted : Bool := false) : Game :=
  match after with
  | .none => g
  | .draw p n => if guardDeparted && !g.stillInGame p then g else g.draw p n
  | .gainLife p n => if guardDeparted && !g.stillInGame p then g else g.gainLife p n
  | .revealRandomCreatureThenBottom _ _ => g
  | .putOnTop p ids => g.putIdsOnTop p ids
  | .beholdUntap p landId subtype => g.beholdAndMaybeUntap p landId subtype
  | .discardRandom p =>
    if guardDeparted && !g.stillInGame p then g
    else
      let hand := g.discardableHandIds p
      if hand.isEmpty then g
      else if hand.size == 1 then g.discardFromHandRandomly p hand[0]!
      else g.changes #[.pending (.resolveRandom (.chooseObject hand)), .afterRandom (.discardRandom p)]
  | .continueInterpreter _ =>
    g.resumeInterpWaitIfReady

/-- Resolve a single-object `--norandom` `.chooseObject` choice without host
priority wrapping (shared by `supplyOrder`, `.restorePending`, and
`Leaving.redirectPendingAfterLeave`). -/
partial def autoResolveSingleChooseObjectCore (g : Game) (id : ObjectId) : Game :=
  match g.afterRandom with
  | .revealRandomCreatureThenBottom controller revealed =>
    let g := g.changes #[.pending .none, .afterRandom .none]
    g.resolveRandomCreatureReveal controller revealed id
  | .discardRandom controller =>
    let g := g.changes #[.pending .none, .afterRandom .none]
    (g.discardFromHandRandomly controller id).finishAfterRandom false
  | _ =>
    (g.change (.pending .none)).finishAfterRandom false

/-- Run the stored after-action. `grantPriority` is true when the host just
supplied a `--norandom` result (the original caller is no longer on the
stack). -/
partial def finishAfterRandom (g : Game) (grantPriority : Bool) : Game :=
  if g.pregameRandom != .none then
    let pre := g.pregameRandom
    let g := g.change (.pregameRandom .none)
    match pre with
    | .none => g
    | .openingShuffles next => continueOpeningShuffles g next
    | .mulliganDraw p n =>
      if g.stillInGame p then g.draw p n (cause := some (.gameRule .mulligan)) else g
    | .mulliganQueue p rest =>
      let g :=
        if g.stillInGame p then
          g.draw p (g.player p).startingHandSize (cause := some (.gameRule .mulligan))
        else g
      executeMulliganQueue g rest
    | .setStartingPlayer i =>
      let n := g.players.size
      let i := if n == 0 then 0 else i % n
      let sp0 : PlayerId := ((g.teamMembers ⟨i⟩).find? g.stillInGame).getD ⟨i⟩
      let sp := if g.stillInGame sp0 then sp0 else g.nextLiving sp0
      let g := g.changes #[.startingPlayer sp, .priority sp]
      let g := g.logMsg s!"Starting player: {(g.player sp).name}"
      continueOpeningShuffles g 0
  else
    let after := g.afterRandom
    let g := g.change (.afterRandom .none)
    let g := g.runInGameAfterRandom after
    if grantPriority then finishHostRandom g else g
end

@[export mtg_game_classify_finish_and_grant_priority_fuel]
def classifyFinishAndGrantPriorityFuelExport (g : Game) (p : PlayerId) (fuel : Nat) :
    ConcedePriorityOutcome :=
  classifyFinishAndGrantPriorityFuel g p fuel

@[export mtg_game_auto_resolve_choose_object]
def autoResolveSingleChooseObject (g : Game) (id : ObjectId) : Game :=
  g.autoResolveSingleChooseObjectCore id

/-- Continue the proposal window after kicker / gift announcements. -/
def afterOptionalAdditionalCost (g : Game) (p : PlayerId) : Game :=
  match g.proposedSpell, g.proposedSpell.bind (fun prop => g.findObject? prop.spellId) with
  | some prop, some spell =>
    let face := g.baseCard spell
    if face.hasGift && !prop.giftAnnounced then
      let g := g.change (.pending (.chooseGift p))
      g.logMsg s!"{(g.player p).name} may promise a gift (CR 702.174)"
    else if face.teamwork.isSome && !prop.teamworkAnnounced then
      let g := g.change (.pending (.chooseTeamwork p))
      g.logMsg s!"{(g.player p).name} may pay a teamwork cost (CR 702.194)"
    else
      g.afterAdditionalCostAnnounced
  | _, _ => g

def announceKicker (g : Game) (p : PlayerId) (kick : Bool) : Except String Game := do
  match g.pending with
  | .chooseKicker caster =>
    if caster != p then
      throw s!"Only {(g.player caster).name} may announce kicker"
    let origFace? :=
      g.proposedSpell.bind (fun prop => g.findObject? prop.spellId) |>.map g.baseCard
    let g ← g.applyKickerToProposed kick
    let g := g.logMsg
      (if kick && (origFace?.bind (·.morph)).isSome then s!"{(g.player p).name} casts the spell face down"
       else if kick && (origFace?.bind (·.impending)).isSome then s!"{(g.player p).name} casts the spell for its impending cost"
       else if kick then s!"{(g.player p).name} kicks the spell"
       else s!"{(g.player p).name} pays the printed cost")
    if !kick && origFace?.any (fun f => f.morph.isSome && f.kicker.isNone) then
      match g.proposedSpell, g.proposedSpell.bind (fun prop => g.findObject? prop.spellId) with
      | some prop, some spell =>
        let face := g.baseCard spell
        if prop.cost.containsX then
          return g.change (.pending (.chooseX p))
            |>.logMsg s!"{(g.player p).name} must choose a value for X (CR 107.3a / 601.2b)"
        else if isModalSpellFace face then
          if prop.resolutionCast &&
              !(g.evalSpellModes p spell).any (g.spellModeIsChoosable p · (some prop.spellId)) &&
              !isReturnUpToTwoGyModal face && !face.allowsZeroTargets then
            return g.reverseProposedSpell (resumeContinuation := true)
          else
            return g.change (.pending (.chooseMode p))
              |>.logMsg s!"{(g.player p).name} must choose a mode (CR 601.2b)"
        else if face.announcesAdditionalCost then
          return g.change (.pending (.chooseAdditionalCost p))
            |>.logMsg s!"{(g.player p).name} must choose an additional cost (CR 601.2b)"
        else
          return g.afterOptionalAdditionalCost p
      | _, _ => return g.afterOptionalAdditionalCost p
    else
      return g.afterOptionalAdditionalCost p
  | _ => throw "Not time to announce kicker"

def announceGift (g : Game) (p : PlayerId) (to : Option PlayerId) : Except String Game := do
  match g.pending with
  | .chooseGift caster =>
    if caster != p then
      throw s!"Only {(g.player caster).name} may promise a gift"
    if let some opp := to then
      if opp.idx >= g.players.size || opp == p || !g.stillInGame opp ||
          g.areTeammates p opp then
        throw "You must promise the gift to an opponent"
    let g ← g.applyGiftToProposed to
    let g :=
      match to with
      | some opp =>
        g.logMsg s!"{(g.player p).name} promises a gift to {(g.player opp).name}"
      | none =>
        g.logMsg s!"{(g.player p).name} does not promise a gift"
    return g.afterOptionalAdditionalCost p
  | _ => throw "Not time to promise a gift"

def announceTeamwork (g : Game) (p : PlayerId) (pay : Bool) : Except String Game := do
  match g.pending with
  | .chooseTeamwork caster =>
    if caster != p then
      throw s!"Only {(g.player caster).name} may announce teamwork"
    let some prop := g.proposedSpell | throw "No spell is waiting for teamwork"
    if !pay then
      let g := g.changeProposals #[.teamworkPaid false, .teamworkAnnounced true]
      let g := g.logMsg s!"{(g.player p).name} does not pay a teamwork cost"
      return g.afterOptionalAdditionalCost p
    match (g.baseCard prop.original).teamwork.orElse (fun () =>
        (g.findObject? prop.spellId).bind (fun o => (g.baseCard o).teamwork)) with
    | none => throw "That spell has no teamwork"
    | some need =>
      let g := g.change (.pending (.chooseTeamworkCreatures p need))
        |>.changeProposal (.teamworkAnnounced true)
      return g.logMsg
        s!"{(g.player p).name} chooses creatures to tap for teamwork {need}"
  | _ => throw "Not time to announce teamwork"

def payTeamworkCreatures (g : Game) (p : PlayerId) (ids : Array ObjectId) :
    Except String Game := do
  match g.pending with
  | .chooseTeamworkCreatures caster need =>
    if caster != p then
      throw s!"Only {(g.player caster).name} may tap creatures for teamwork"
    let some prop := g.proposedSpell | throw "No spell is waiting for teamwork"
    if !g.proposalCostPromptStillPayable p g.pending then
      return (← g.reverseProposedSpell? (resumeContinuation := true))
    let mut total : Int := 0
    let mut seen : Array ObjectId := #[]
    for id in ids do
      if seen.contains id then
        throw "A creature cannot be tapped twice for the same teamwork cost"
      seen := seen.push id
      let some o := g.findObject? id | throw "no such object"
      if !(o.isOnBattlefield && g.isCreature o && g.controlledBy o p) then
        throw s!"{g.name o} is not a creature you control"
      if o.status.tapped then
        throw s!"{g.name o} is already tapped"
      total := total + g.power o
    if total < (need : Int) then
      throw s!"Tapped creatures must have total power {need} or more"
    let some spell := g.findObject? prop.spellId | throw "The spell left the stack"
    let face := g.baseCard spell
    let mut g := g.record (GameEvent.announced g.turnNumber spell.id (costs := #[.teamwork ids])
      (cause := some (.costPayment .teamwork p (some spell.id))))
    g := g.change (.pending .none)
      |>.changeProposals #[.teamworkPaid true, .teamworkAnnounced true, .teamworkCreatures ids]
    g := g.logMsg s!"{(g.player p).name} announces teamwork"
    -- “If this spell was cast using teamwork, choose both instead.”
    let effModes := g.evalSpellModes p spell
    let teamworkBoth := face.modalSpec?.any fun ms =>
      match ms.altCountIf? with
      | some (.castPred (.teamworkPaid .this), _, _) => true
      | _ => false
    if teamworkBoth &&
        effModes.all (fun m => g.spellModeIsChoosable p m (some spell.id)) then
      let chosen := g.chosenModesOf spell
      for i in [0:effModes.size] do
        if !chosen.contains i then
          g := (if (g.chosenModesOf spell).isEmpty then g.setProposedMode i else g.addProposedExtraMode i)
      g := g.logMsg s!"{(g.player p).name} chooses both modes (teamwork)"
    return g.afterOptionalAdditionalCost p
  | _ => throw "Not time to tap creatures for teamwork"

def uniqueObjectIds (ids : Array ObjectId) : Bool :=
  Id.run do
    let mut seen : Array ObjectId := #[]
    for id in ids do
      if seen.contains id then
        return false
      seen := seen.push id
    return true

def isPermutation (a b : Array ObjectId) : Bool :=
  a.size == b.size && uniqueObjectIds a && a.all (fun x => b.contains x)

/-- Check that `top ++ rest` rearranges the `count` cards `p` is looking at
as `q`'s pending scry or surveil. -/
def checkLookedPiles (g : Game) (p q : PlayerId) (count : Nat)
    (top rest : Array ObjectId) (verb rule : String) : Except String Unit := do
  if p != q then
    throw s!"Only {(g.player q).name} may {verb}"
  if !uniqueObjectIds (top ++ rest) then
    throw "Duplicate card"
  if !isPermutation (top ++ rest) (g.scryLookedIds p count) then
    throw s!"{verb.capitalize} must rearrange the cards you looked at ({rule})"

/-- Log putting `top` back on top, unless they stay in the looked-at order. -/
def logPutOnTop (g : Game) (p : PlayerId) (looked top : Array ObjectId) : Game :=
  Id.run do
    let mut g := g
    if top != looked then
      for id in top do
        g := g.logMsg
          s!"{(g.player p).name} puts {g.name (g.object! id)} on top of their library"
    return g

/-- Finish scrying: put `bottom` on the bottom (first = new bottom) and `top`
on top (last = new top) of the library, each pile in the given order (CR 701.22). -/
def finishScry (g : Game) (p : PlayerId) (top bottom : Array ObjectId) :
    Except String Game := do
  match g.pending with
  | .scry q count asked =>
    g.checkLookedPiles p q count top bottom "scry" "CR 701.22"
    let outerCont? := g.pendingReplacement
    let g := if outerCont?.isSome then g.change (.pendingReplacement none) else g
    let looked := g.scryLookedIds p count
    let cause := some (g.resolvingOrRuleCause p)
    let mut g := g.change (.pending .none)
    for id in bottom do
      g := g.logMsg
        s!"{(g.player p).name} puts {g.name (g.object! id)} on the bottom of their library"
    g := g.logPutOnTop p looked top
    let happened :=
      GameEvent.looked g.turnNumber p count false asked
        (top := top) (rest := bottom) (cause := cause)
    g := (g.record happened).finishLibraryLookCore
    let rec startsWithFinishPostCast : PendingReplacement → Bool
      | .finishPostCast .. => true
      | .seq a _ => startsWithFinishPostCast a
      | _ => false
    g :=
      match outerCont? with
      | some outer =>
        if startsWithFinishPostCast outer then g.chainPendingReplacement outer
        else g.reattachOuterCont (some outer)
      | none => g
    return g.finishAndGrantPriority
  | .surveil .. => throw "You are surveilling, not scrying; use surveil (CR 701.25)"
  | _ => throw "Not time to scry (CR 701.22)"

/-- Finish surveilling: put `graveyard` into the graveyard in that order and
`top` back on top (last = new top) of the library (CR 701.25). -/
def finishSurveil (g : Game) (p : PlayerId) (top graveyard : Array ObjectId) :
    Except String Game := do
  match g.pending with
  | .surveil q count asked =>
    g.checkLookedPiles p q count top graveyard "surveil" "CR 701.25"
    let outerCont? := g.pendingReplacement
    let g := if outerCont?.isSome then g.change (.pendingReplacement none) else g
    let looked := g.scryLookedIds p count
    let cause := some (g.resolvingOrRuleCause p)
    let g := ((g.change (.pending .none)).logPutOnTop p looked top).withBatch cause fun g =>
      let happened :=
        GameEvent.looked g.turnNumber p count true asked
          (top := top) (rest := graveyard) (cause := cause)
      (g.record happened).surveilMoveLoop p graveyard cause
    let g := g.finishLibraryLookCore
    let g := g.reattachOuterCont outerCont?
    return g.finishAndGrantPriority
  | .scry .. => throw "You are scrying, not surveilling; use scry (CR 701.22)"
  | _ => throw "Not time to surveil (CR 701.25)"

/-- Remove one symbol a convoking creature of `colors` can pay: a colored
(or hybrid) symbol of one of its colors, else one generic mana (ruling 865). -/
def convokePayOne (cost : ManaCost) (colors : ColorSet) : Option ManaCost :=
  let syms := cost.symbols
  let without (i : Nat) : Array ManaSymbol := syms.extract 0 i ++ syms.extract (i + 1) syms.size
  let colored := syms.findIdx? (fun s =>
    match s with
    | .colored c => colors.contains c
    | .hybrid a b => colors.contains a || colors.contains b
    | .twobrid c => colors.contains c
    | _ => false)
  match colored with
  | some i => some { symbols := without i }
  | none =>
    match syms.findIdx? (fun s => match s with | .generic n => n > 0 | _ => false) with
    | some i =>
      match syms[i]! with
      | .generic n =>
        if n == 1 then some { symbols := without i }
        else some { symbols := syms.set! i (.generic (n - 1)) }
      | _ => none
    | none => none

/-- Convoke (CR 702.51a) and improvise (CR 702.126a): while paying for a spell
with convoke, tap untapped creatures you control; each pays for {1} or one
mana of its colors. With improvise, tap untapped artifacts you control; each
pays for {1}. Both apply to the total cost after alternative and additional
costs and don't change the mana value (rulings 864 / 869). A permanent
already tapped, for example for mana, can't be tapped again (ruling 863).
Summoning sickness doesn't matter, and an attacking creature stays attacking
(rulings 866 / 867). A creature artifact pays for convoke when the spell has
convoke. -/
def convoke (g : Game) (p : PlayerId) (ids : Array ObjectId) : Except String Game := do
  match g.pending, g.proposedSpell with
  | .activateManaAbilities q, some prop =>
    if p != q then
      throw s!"Only {(g.player q).name} may pay"
    let some spell := g.findObject? prop.spellId | throw "The spell left the stack"
    let hasConvoke := prop.kind == .spell && KeywordAbility.hasConvoke (g.currentKeywords spell)
    let hasImprovise := prop.kind == .spell && g.spellHasImprovise (g.baseCard spell) p
    if !hasConvoke && !hasImprovise then
      throw s!"{g.name spell} doesn't have convoke or improvise (CR 702.51 / 702.126)"
    g.withProposalActionM .costAction fun g => do
      let (g, (cost, tapped)) ← g.withBatchExcept none fun g => do
        let mut g := g
        let mut cost := prop.cost
        let mut tapped := prop.tapped
        for id in ids do
          let some o := g.findObject? id | throw "no such object"
          if !(o.isOnBattlefield && g.controlledBy o p) then
            throw s!"You don't control {g.name o}"
          if o.status.tapped then
            throw s!"{g.name o} is already tapped (ruling 863)"
          if prop.teamworkCreatures.contains id then
            throw s!"{g.name o} was already chosen for teamwork"
          if hasConvoke && g.isCreature o then
            match convokePayOne cost (g.colors o) with
            | none => throw s!"{g.name o} can't pay for any of the remaining cost"
            | some c => cost := c
            g := g.becomeTapped o (cause := some (.costPayment .convoke p (some prop.spellId)))
            g := g.logMsg s!"{(g.player p).name} taps {g.name o} to convoke {g.name spell}"
          else if hasImprovise && g.isArtifact o then
            if cost.genericCount == 0 then
              throw s!"No generic mana is left for {g.name o} to pay (CR 702.126a)"
            cost := cost.reduceGeneric 1
            g := g.becomeTapped o (cause := some (.costPayment .tap p (some prop.spellId)))
            g := g.logMsg s!"{(g.player p).name} taps {g.name o} for improvise"
          else
            throw s!"{g.name o} can't help pay for {g.name spell}"
          tapped := tapped.push id
        return (g, (cost, tapped))
      return g.changeProposals #[.cost cost, .tapped tapped]
  | _, _ => throw "No spell is being paid for (CR 601.2h)"

/-- Proliferate once (CR 701.34a): give each chosen permanent and player
another counter of each kind already there. Any subset may be chosen,
including none and opponents' permanents (rulings 881 / 882); cards in other
zones can't be (ruling 881). No player can act between proliferations
(ruling 880), and each one may choose a different set (ruling 886). -/
def finishProliferate (g : Game) (p : PlayerId) (chosen : Array Target) :
    Except String Game := do
  match g.pending with
  | .chooseProliferate q remaining =>
    if p != q then
      throw s!"Only {(g.player q).name} may proliferate"
    if chosen.toList.eraseDups.length != chosen.size then
      throw "Choose each permanent or player at most once"
    for t in chosen do
      match t with
      | .permanent id =>
        let some o := g.findObject? id | throw "no such object"
        if !o.isOnBattlefield then
          throw s!"{g.name o} is not a permanent on the battlefield (CR 701.34a)"
        if !o.status.hasCounters then
          throw s!"{g.name o} has no counters"
      | .player pid =>
        let pl := g.player pid
        if !g.stillInGame pid then
          throw s!"{pl.name} is no longer in the game (CR 701.34a / 800.4a)"
        if g.teamPoison pid == 0 && !pl.counters.any (fun (_, c) => c > 0) then
          throw s!"{pl.name} has no counters"
      | .card _ =>
        throw "Only permanents and players can be chosen (CR 701.34a)"
    let outerCont? := g.pendingReplacement
    let g := if outerCont?.isSome then g.change (.pendingReplacement none) else g
    let cause := some (g.resolvingOrRuleCause p)
    let g := (g.change (.pending .none)).withBatch cause fun g =>
      g.finishProliferateLoop p chosen #[] #[] chosen.isEmpty 0 cause
    if let .chooseReplacement .. := g.pending then
      let g :=
        if remaining > 1 then
          g.chainPendingReplacement (.restorePending (.chooseProliferate p (remaining - 1)))
        else g
      let g := g.reattachOuterCont outerCont?
      return if remaining > 1 then g else g.finishResolutionChoice
    else if remaining > 1 then
      let g := g.change (.pending (.chooseProliferate p (remaining - 1)))
      return g.reattachOuterCont outerCont?
    else
      let g := g.reattachOuterCont outerCont?
      return g.finishResolutionChoice
  | _ => throw "Not time to proliferate (CR 701.34)"

/-- Shared pending-discard core (CR 701.9): `p` must be the pending player
`q` and `id` must be in `p`'s hand; the discard is logged (with `logSuffix`)
and the card moves to its owner's graveyard. The move records the discard.
Returns the discarded card. -/
def discardPendingCard (g : Game) (p q : PlayerId) (id : ObjectId)
    (logSuffix : String := "") (cause : Option EventCause := none) :
    Except String (Game × GameObject) := do
  if p != q then
    throw s!"Only {(g.player q).name} may discard"
  if !(g.player p).hand.contains id then
    throw "That card is not in your hand"
  let some card := g.findObject? id | throw "no such object"
  if !isDiscardableCard card then
    throw s!"{g.name card} is not a card and can't be discarded (CR 108.2b / 111.8)"
  let owner := card.owner
  let msg := s!"{(g.player p).name} discards {g.name card}{logSuffix}"
  let g := g.change (.pending .none)
  let (g, _) := g.move id (.graveyard owner) none (verb := some .discard)
    (actor := some p) (cause := cause)
  let g :=
    if let .chooseReplacement .. := g.pending then
      g.chainPendingReplacement (.finishPostStep (.logDiscardIfInGraveyard id owner msg))
    else if (g.followMovedToZone? id (· == .graveyard owner)).isSome then
      g.logMsg msg
    else g
  return (g, card)

/-- Discard `id` from hand; if this finishes a pending “may discard, then draw”,
draw that many cards (CR 701.9). -/
def discardForDraw (g : Game) (p : PlayerId) (id : ObjectId) : Except String Game := do
  match g.pending with
  | .mayDiscardDraw q n =>
    let outerCont? := g.pendingReplacement
    let g0 := if outerCont?.isSome then g.change (.pendingReplacement none) else g
    let (g, _) ← g0.discardPendingCard p q id
    let g :=
      if let .chooseReplacement .. := g.pending then
        g.chainPendingReplacement (.finishDiscardForDrawMay p n)
      else
        g.finishDiscardForDrawMay p n
    let g := g.reattachOuterCont outerCont?
    return g.finishAndGrantPriority
  | .maySacArtifactOrDiscard q n =>
    let outerCont? := g.pendingReplacement
    let g0 := if outerCont?.isSome then g.change (.pendingReplacement none) else g
    let (g, _) ← g0.discardPendingCard p q id
    let g := g.finishSacArtifactOrDiscardDraw p n
    let g := g.reattachOuterCont outerCont?
    return g.finishAndGrantPriority
  | .chooseDiscardCard q remaining =>
    let outerCont? := g.pendingReplacement
    let g0 := if outerCont?.isSome then g.change (.pendingReplacement none) else g
    let (g, card) ← g0.discardPendingCard p q id
    let g :=
      if let .chooseReplacement .. := g.pending then
        g.chainPendingReplacement (.finishChooseDiscardCard p card remaining)
      else
        g.finishChooseDiscardCard p card remaining
    let g := g.reattachOuterCont outerCont?
    return g.finishAndGrantPriority
  | .recruitDiscard q =>
    let outerCont? := g.pendingReplacement
    let g0 := if outerCont?.isSome then g.change (.pendingReplacement none) else g
    let (g, card) ← g0.discardPendingCard p q id
    let isLand := g.isLand card
    let g :=
      if let .chooseReplacement .. := g.pending then
        g.chainPendingReplacement (.finishRecruitDiscard p isLand)
      else
        g.finishRecruitDiscard p isLand
    let g := g.reattachOuterCont outerCont?
    return g.finishAndGrantPriority
  | .discardForAdditionalCost q =>
    if q != p then
      throw s!"Only {(g.player q).name} may discard"
    let some prop := g.proposedSpell | throw "No spell is waiting for an additional cost"
    if !g.proposalCostPromptStillPayable p g.pending then
      return (← g.reverseProposedSpell? (resumeContinuation := true))
    let isResCast := prop.resolutionCast
    let outerCont? := g.pendingReplacement
    let openCont := g.proposalHadOpenContinuation
    let g0 := if outerCont?.isSome then g.change (.pendingReplacement none) else g
    let g ← g0.withProposalActionM .costAction fun g => do
      let (g, _) ← g.discardPendingCard p q id
        (cause := some (.costPayment .discard p (some prop.spellId)))
      return g.record (GameEvent.announced g.turnNumber prop.spellId (costs := #[.discard id])
        (cause := some (.costPayment .discard p (some prop.spellId))))
    let paused := match g.pending with | .chooseReplacement .. => true | _ => false
    if prop.kind == .turnFaceUp then
      let willReverse := !paused && !g.over && g.proposedSpell.isSome && g.proposalCheckpoint.isSome &&
        !(g.stillInGame prop.caster &&
          (g.findObject? prop.spellId).any (fun cur =>
            cur.isOnBattlefield && cur.status.faceDown && g.controlledBy cur prop.caster))
      let (g, callerShouldResume) := g.completeTurnFaceUp prop.caster prop.spellId
        (hadOuterReplacement := outerCont?.isSome)
      let g :=
        if willReverse then g
        else
          match outerCont? with
          | some outer => g.chainProposalOuterCont prop.caster outer (openCont := openCont)
          | none => g
      return if !willReverse && (callerShouldResume || (!g.over && g.pending == .none && outerCont?.isSome)) then
        g.resumeAfterBecomeCast
      else g
    let clearPending : Array EngineChange :=
      if paused then #[] else #[.pending .none]
    let g := g.changes (clearPending ++ #[EngineChange.consecutivePasses 0])
    let g := g.becomeCast prop.caster (g.object! prop.spellId)
      (grantPriority := !isResCast)
      (hadOuterReplacement := outerCont?.isSome)
      (hadOpenContinuation := some openCont)
    let pausedAfter := match g.pending with | .chooseReplacement .. => true | _ => false
    let g :=
      match outerCont? with
      | some outer =>
        g.chainProposalOuterCont prop.caster outer (grantPriority := !isResCast) (openCont := openCont)
      | none =>
        if pausedAfter && isResCast && !g.anyContinuationSettlesControlFlow then
          g.chainPendingReplacement .finishResolutionChoice
        else g
    if pausedAfter then
      return g
    else if isResCast then
      if (match g.pending with | .chooseReplacement .. => true | _ => false) &&
          g.anyContinuationSettlesControlFlow then
        return g
      else
        return g.finishResolutionChoice
    else
      return g.resumeAfterBecomeCast
  | .payWard q spellId cost _ =>
    if p != q then
      throw s!"Only {(g.player q).name} may discard for ward"
    let env : EvalEnv := { controller := p }
    let itemAllowsDiscard : CostItem → Bool
      | .discard _ .hand => true
      | .discard _ (.matching pred) =>
        (g.findObject? id).any fun o => EvalExpr.evalObjectPred g env (.live o) pred
      | _ => false
    let legal :=
      cost.items.any fun
        | .or choices => choices.any fun ch => ch.items.any itemAllowsDiscard
        | item => itemAllowsDiscard item
    if !legal then
      throw "That card cannot pay this ward"
    let outerCont? := g.pendingReplacement
    let g0 := if outerCont?.isSome then g.change (.pendingReplacement none) else g
    let (g, _) ← g0.discardPendingCard p q id (logSuffix := " (ward)")
      (cause := some (.costPayment .ward p (some spellId)))
    return g.finishWardAndDrain outerCont?
  | _ => throw "Not time to discard a card (CR 701.9)"

/-- Pay a pending generic-mana “you may pay” or “unless pays” cost. -/
def payGeneric (g : Game) (p : PlayerId) : Except String Game := do
  match g.pending with
  | .mayPayGeneric q n =>
    if p != q then
      throw s!"Only {(g.player q).name} may pay \{{n}}"
    if !(g.player p).manaPool.canPay (ManaCost.ofGeneric n) then
      throw s!"{(g.player p).name} cannot pay \{{n}}"
    let outerCont? := g.pendingReplacement
    let g := if outerCont?.isSome then g.change (.pendingReplacement none) else g
    let forObj :=
      g.resolvingAbility <|> g.resolvingSpell <|> (g.currentResolvingContext?.bind Prod.fst)
    let g ← g.payCost p (ManaCost.ofGeneric n) (forObject := forObj)
    let g := g.logMsg s!"{(g.player p).name} pays \{{n}}"
    let g := (g.change (.pending .none)).draw p 1
    let g := g.reattachOuterCont outerCont?
    return g.finishAndGrantPriority
  | .payOrLetCounter q n _ =>
    if p != q then
      throw s!"Only {(g.player q).name} may pay \{{n}}"
    if !(g.player p).manaPool.canPay (ManaCost.ofGeneric n) then
      throw s!"{(g.player p).name} cannot pay \{{n}}"
    let outerCont? := g.pendingReplacement
    let g := if outerCont?.isSome then g.change (.pendingReplacement none) else g
    let forObj :=
      g.resolvingAbility <|> g.resolvingSpell <|> (g.currentResolvingContext?.bind Prod.fst)
    let g ← g.payCost p (ManaCost.ofGeneric n) (forObject := forObj)
    let g := g.logMsg s!"{(g.player p).name} pays \{{n}}"
    let g := g.changes #[
      .pending .none,
      .bindStepOutcome interpChoiceVar { succeeded := true }]
    let g := g.reattachOuterCont outerCont?
    return g.finishAndGrantPriority
  | .payWard q _ cost _ =>
    if p != q then
      throw s!"Only {(g.player q).name} may pay ward"
    let manaToPay? : Option ManaCost :=
      if cost.isManaOnly && cost.mana.includesManaPayment then some cost.mana
      else
        cost.items.findSome? fun
          | .or choices =>
            choices.findSome? fun ch =>
              if ch.isManaOnly && ch.mana.includesManaPayment then some ch.mana else none
          | _ => none
    let some mc := manaToPay? | throw "Not time to pay generic mana"
    if !(g.player p).manaPool.canPay mc then
      throw s!"{(g.player p).name} cannot pay {mc}"
    let outerCont? := g.pendingReplacement
    let g := if outerCont?.isSome then g.change (.pendingReplacement none) else g
    let forObj :=
      g.resolvingAbility <|> g.resolvingSpell <|> (g.currentResolvingContext?.bind Prod.fst)
    let g ← g.payCost p mc (forObject := forObj)
    let g := g.logMsg s!"{(g.player p).name} pays {mc} (ward)"
    return g.finishWardAndDrain outerCont?
  | _ => throw "Not time to pay generic mana"

/-- Accept an optional interpreter choice (`Pending.mayResolve`) and resume. -/
def acceptMay (g : Game) (p : PlayerId) : Except String Game := do
  match g.pending with
  | .mayResolve q =>
    if p != q then
      throw s!"Only {(g.player q).name} may accept"
    let outerCont? := g.pendingReplacement
    let g := if outerCont?.isSome then g.change (.pendingReplacement none) else g
    let g := g.changes #[
      .pending .none,
      .bindStepOutcome interpChoiceVar { succeeded := true }]
    let g := g.reattachOuterCont outerCont?
    return g.finishAndGrantPriority
  | _ => throw "Nothing to accept now"

/-- Apply alternative `idx` of a pending resolution-time `chooseModes` choice
(`Pending.chooseTriggerOr`), resuming the suspended `InterpCont.chooseBranch`. -/
def chooseTriggerOr (g : Game) (p : PlayerId) (idx : Nat) : Except String Game := do
  match g.pending with
  | .chooseTriggerOr q =>
    if p != q then throw s!"Only {(g.player q).name} may choose"
    let validIdx : Bool :=
      match g.currentInterpWait? with
      | some st =>
        match st.stack.back? with
        | some (.chooseBranch branches _) => idx < branches.size
        | _ => false
      | none => false
    if !validIdx then throw "No such choice"
    let g :=
      match g.pendingReplacement with
      | some outer => g.changes #[.pendingReplacement none, .pushOuterPendingReplacement outer]
      | none => g
    let g := g.changes #[
      .pending .none,
      .bindStepOutcome interpChoiceVar { movedCount := idx, succeeded := true }]
    return g.finishAndGrantPriority
  | _ => throw "Not time to choose"

/-- Apply alternative `idx` of a pending `Pending.chooseLibraryPlacement` choice
(either an interpreter `chooseBranch` or direct top=0 / bottom=1 placement). -/
def chooseSpellOr (g : Game) (p : PlayerId) (idx : Nat) : Except String Game := do
  match g.pending with
  | .chooseTriggerOr _ => g.chooseTriggerOr p idx
  | .chooseLibraryPlacement q id? =>
    let branch? : Option (Array Instruction × Bool) :=
      g.currentInterpWait?.bind fun st =>
        match st.stack.back? with
        | some (.chooseBranch branches isLib) => some (branches, isLib)
        | _ => none
    match branch? with
    | some (branches, isLib) =>
      if p != q then
        let what := if isLib then "top or bottom" else "an effect"
        throw s!"Only {(g.player q).name} may choose {what}"
      if idx >= branches.size then
        throw "No such choice"
      if isLib then
        let some id := id? | throw "no such object"
        let some o := g.findObject? id | throw "no such object"
        if !o.isOnBattlefield then
          throw s!"{g.name o} is no longer on the battlefield"
      let outerCont? := g.pendingReplacement
      let g := if outerCont?.isSome then g.change (.pendingReplacement none) else g
      let g := g.changes #[
        .pending .none,
        .bindStepOutcome interpChoiceVar { movedCount := idx, succeeded := true }]
      let g := g.reattachOuterCont outerCont?
      return g.finishAndGrantPriority
    | none =>
      if p != q then
        throw s!"Only {(g.player q).name} may choose top or bottom"
      if idx > 1 then throw "No such choice"
      let some id := id? | throw "no such object"
      let some o := g.findObject? id | throw "no such object"
      if !o.isOnBattlefield then
        throw s!"{g.name o} is no longer on the battlefield"
      let outerCont? := g.pendingReplacement
      let g := if outerCont?.isSome then g.change (.pendingReplacement none) else g
      let g := (g.change (.pending .none)).putOnOwnerLibrary o (top := idx == 0)
      let g := g.reattachOuterCont outerCont?
      return g.finishAndGrantPriority
  | _ => throw "Not time to choose library placement"

/-- Put the pending card on top or bottom of its owner's library.
When an interpreter `chooseBranch` is suspended, top is index 0 and bottom is index 1. -/
def chooseLibrarySide (g : Game) (p : PlayerId) (top : Bool) : Except String Game := do
  let hasBranch : Bool :=
    match g.currentInterpWait? with
    | some st =>
      match st.stack.back? with
      | some (.chooseBranch _ _) => true
      | _ => false
    | none => false
  if hasBranch then
    g.chooseSpellOr p (if top then 0 else 1)
  else
    match g.pending with
    | .chooseLibraryPlacement q id? =>
      if p != q then
        throw s!"Only {(g.player q).name} may choose top or bottom"
      let some id := id? | throw "no such object"
      let some o := g.findObject? id | throw "no such object"
      if !o.isOnBattlefield then
        throw s!"{g.name o} is no longer on the battlefield"
      let outerCont? := g.pendingReplacement
      let g := if outerCont?.isSome then g.change (.pendingReplacement none) else g
      let g := (g.change (.pending .none)).putOnOwnerLibrary o (top := top)
      let g := g.reattachOuterCont outerCont?
      return g.finishAndGrantPriority
    | _ => throw "Not time to choose library placement"

/-- Attach Equipment or tap Humans, depending on pending. -/
def choosePermanents (g : Game) (p : PlayerId) (ids : Array ObjectId) :
    Except String Game := do
  match g.pending with
  | .mayAttachEquipment q hostId sourceId =>
    if p != q then
      throw s!"Only {(g.player q).name} may attach Equipment"
    if ids.size != 1 then
      throw "Choose one Equipment to attach"
    let some eq := g.findObject? ids[0]! | throw "no such object"
    if !(eq.isOnBattlefield && g.isEquipment eq && g.controlledBy eq p) then
      throw s!"{g.name eq} is not an Equipment you control"
    let some host := g.findObject? hostId | throw "The creature is no longer in play"
    if !host.isOnBattlefield then
      throw s!"{g.name host} is no longer on the battlefield"
    if sourceId.isSome && !g.canBeTargetedBy p host sourceId then
      throw "The target is no longer legal"
    let outerCont? := g.pendingReplacement
    let g := if outerCont?.isSome then g.change (.pendingReplacement none) else g
    let g :=
      if g.canAttachEquipmentTo eq host then
        (g.change (.pending .none)).attachSourceTo eq host
      else
        g.change (.pending .none)
    let g := g.reattachOuterCont outerCont?
    return g.finishAndGrantPriority
  | .tapHumans q =>
    if p != q then
      throw s!"Only {(g.player q).name} may tap Humans"
    if !uniqueObjectIds ids then
      throw "Duplicate card"
    let outerCont? := g.pendingReplacement
    let g := if outerCont?.isSome then g.change (.pendingReplacement none) else g
    let (g, _) ← (g.change (.pending .none)).withBatchExcept none fun g => do
      let mut g := g
      let mut n : Nat := 0
      for id in ids do
        let some o := g.findObject? id | throw "no such object"
        if !(o.isOnBattlefield && g.controlledBy o p && g.hasSubtype o .human &&
            !o.status.tapped) then
          throw s!"{g.name o} is not an untapped Human you control"
        g := g.becomeTapped o
        n := n + 1
      return (g, n)
    let g := g.reattachOuterCont outerCont?
    return g.finishAndGrantPriority
  | .chooseTeamworkCreatures _ _ =>
    g.payTeamworkCreatures p ids
  | .chooseDiscardCard q remaining =>
    if p != q then
      throw s!"Only {(g.player q).name} may discard"
    if !uniqueObjectIds ids then
      throw "Duplicate card"
    let hand := g.discardableHandIds p
    if !ids.all hand.contains then
      throw "That card is not in your hand"
    if g.thirstDiscardsLeft > 0 then
      let nReq := Nat.min g.thirstDiscardsLeft hand.size
      let isSingleEscape :=
        ids.size == 1 && (g.findObject? ids[0]!).any (fun c => g.hasType c g.thirstDiscardType)
      let isFullDiscard := ids.size == nReq && ids.size > 0
      if !isSingleEscape && !isFullDiscard then
        throw s!"Choose one {g.thirstDiscardType.oracleWord} card or {nReq} card(s) from your hand"
    else
      let want := if g.pendingDiscardsLeft > 0 then g.pendingDiscardsLeft else 1
      let nReq := Nat.min want hand.size
      if ids.size != nReq || ids.isEmpty then
        throw s!"Choose {nReq} card(s) from your hand"
    let outerCont? := g.pendingReplacement
    let g := if outerCont?.isSome then g.change (.pendingReplacement none) else g
    let g := g.changes #[.pending .none, .thirstDiscardsLeft 0, .pendingDiscardsLeft 0]
    let pairs := ids.map (fun cid => (p, cid))
    let g :=
      if g.discardBatch.isSome then
        let g := g.discardMultiHandIdsLoop pairs (logEach := true)
        if let .chooseReplacement .. := g.pending then
          let g := g.chainPendingReplacement (.finishPostStep .closeDiscardBatchStep)
          if !remaining.isEmpty then
            g.chainPendingReplacement
              (.finishPostStep (.continueAfterDiscardStep remaining false (max 1 g.discardCountPerPlayer)))
          else g
        else
          let g := g.closeCurrentDiscardBatch
          if !remaining.isEmpty then
            g.continueAfterDiscard remaining (samePlayer := false) (count := max 1 g.discardCountPerPlayer)
          else g
      else
        let g := g.withBatch none fun g =>
          g.discardMultiHandIdsLoop pairs (logEach := true)
        if !remaining.isEmpty then
          if let .chooseReplacement .. := g.pending then
            g.chainPendingReplacement
              (.finishPostStep (.continueAfterDiscardStep remaining false (max 1 g.discardCountPerPlayer)))
          else
            g.continueAfterDiscard remaining (samePlayer := false) (count := max 1 g.discardCountPerPlayer)
        else g
    let g := g.reattachOuterCont outerCont?
    return g.finishAndGrantPriority
  | _ => throw "Not time to choose permanents"

/-- Cast the card Chandra, Torch of Defiance exiled, as her ability resolves.
Timing permissions are ignored, but its costs are paid (rulings 857 /
859). A land can't be cast (ruling 855). -/
def castExiledAsAbilityResolves (g : Game) (p : PlayerId) (id : ObjectId) :
    Except String Game := do
  match g.pending with
  | .mayCastExiledElseDamage q cardId .. =>
    if p != q then
      throw s!"Only {(g.player q).name} may cast that card"
    if id != cardId then
      throw "That isn't the exiled card"
    let some card := g.findObject? id | throw "no such object"
    let origSnap := g.snapshot card
    let face := g.baseCard card
    let rawPerm := g.paidResolutionOrigPerm? p card (face? := some face)
    let origPerm : Option PlayPermission :=
      some (rawPerm.getD { player := p, ignoreTiming := true })
    if g.cantCastSpellsThisTurn p then
      throw "You can't cast spells this turn (CR 101.2)"
    if g.splitSecondOnStack then
      throw "A spell with split second is on the stack (CR 702.61a)"
    if g.combatLocksNonManaAbilities then
      throw "During combat, players can't cast spells (Yuriko, Blade of the Mighty)"
    if g.opponentsCantCastOnActiveTurn p then
      throw "Opponents can't cast spells during that player's turn"
    if !isCastableObject card then
      throw s!"{g.name card} can't be cast"
    if g.isLand card then
      throw "An effect that lets you cast a card doesn't let you play a land (ruling 855)"
    let canMorph :=
      face.morph.isSome && face.kicker.isNone &&
        !g.spellNameForbidden ""
    if !canMorph then
      if g.spellNameForbidden face.name then
        throw s!"Spells named {face.name} can't be cast"
      if let some err := g.castRestrictionError? p card.id face then
        throw err
      let tcs := g.evalLayer3 card
      if isModalSpellFace face &&
          !(effectiveSpellModes face).any (fun e =>
            let m := if tcs.isEmpty then e else TextChange.applyEffect tcs e
            g.spellModeIsChoosable p m (some card.id)) &&
          !isReturnUpToTwoGyModal face && !face.allowsZeroTargets then
        throw s!"{face.name} has no mode with a legal target"
      if !isModalSpellFace face && (face.requiresTarget || face.isAura) &&
          !g.castFaceHasLegalTarget p face tcs (some card.id) && !face.allowsZeroTargets then
        throw s!"{face.name} requires a target"
      if let some err := g.mandatorySacrificeError? p card.id face then
        throw err
    let g := g.change .saveProposalCheckpoint
    let g :=
      match g.pendingReplacement with
      | some outer =>
        let g := if g.continuations.isEmpty then g.change (.pushContinuationFrame {}) else g
        g.changes #[.pushOuterPendingReplacement outer, .pendingReplacement none]
      | none => g
    let g := g.change (.pending .none)
    let (g, newId) := g.move id .stack (some p) (verb := some .cast) (actor := some p)
      (cause := some (.gameRule .spellCast))
    let some spellObj := (g.findObject? newId).filter (·.zone == .stack)
      | throw s!"{face.name} cannot be moved to the stack"
    let stackFace := g.baseCard spellObj
    let g := g.putStackEntry p newId
    let g := g.record (GameEvent.proposed g.turnNumber newId p card.zone
      (.alternative "permission"))
    let g := g.logMsg s!"{(g.player p).name} casts {stackFace.name} as the ability resolves"
    let preSpell := { spellObj with
      id := card.id
      zone := card.zone
      exiledBy := card.exiledBy
      controller := some p }
    let altCostUsed := origPerm.any (fun pm => pm.withoutManaCost || pm.payLifeEqualManaValue)
    let cost := g.playManaCost preSpell stackFace (origPerm := origPerm)
      (flashback := some false) (explicitAltCost := false)
      (useImplicitPermissions := false)
    let lifeInstead :=
      if origPerm.any (·.payLifeEqualManaValue) then g.objectManaValue spellObj else 0
    let needsSacrifice := (g.mandatorySacrificeFilterFor? spellObj stackFace).isSome
    let prop : ProposedSpell := {
      caster := p
      cost
      spellId := newId
      original := card
      originalSnapshot := origSnap
      origPerm
      needsSacrificeOther := needsSacrifice
      payLife := lifeInstead
      alternativeCost := altCostUsed
      resolutionCast := true
      resolutionIgnoreTiming := true
    }
    let g' := g.beginResolutionCastTargets p prop
    return if g'.pending == .none && (g'.findObject? newId).any (·.zone == .stack) then
      g'.finishResolutionChoice
    else g'
  | _ => throw "No exiled card may be cast now"

/-- Decline an optional discard (CR 608.2d) or choose no target for an
“up to one” trigger (CR 601.2c / 115.1c). -/
def decline (g : Game) (p : PlayerId) : Except String Game := do
  match g.pending with
  | .chooseMode q =>
    if p != q then throw s!"Only {(g.player q).name} may choose modes"
    if let some prop := g.proposedSpell then
      if !g.sourceStillPayable prop then
        return (← g.reverseProposedSpell? (resumeContinuation := true))
    match g.proposedSpell.bind (fun prop => g.findObject? prop.spellId) with
    | some spell =>
      if (g.chosenModesOf spell).isEmpty then
        if Game.minModesFor (g.baseCard spell) == 0 then
          let g := g.record (GameEvent.announced g.turnNumber spell.id (modes := #[]))
          return (g.logMsg s!"{(g.player p).name} chooses no modes (CR 700.2)").afterModesChosen p
        throw "Choose a mode (CR 700.2)"
      return (g.logMsg s!"{(g.player p).name} chooses no more modes").afterModesChosen p
    | none => throw "Choose a mode (CR 700.2)"
  | .mayCastExiledElseDamage q _ n sid =>
    if p != q then
      throw s!"Only {(g.player q).name} may decline to cast"
    let outerCont? := g.pendingReplacement
    let g := if outerCont?.isSome then g.change (.pendingReplacement none) else g
    let src? := sid.bind g.damageSourceById?
    let g := (g.change (.pending .none)).logMsg s!"{(g.player p).name} doesn't cast the exiled card"
    let g := g.dealDamageToEachOpponent p n (source := src?)
    let g := g.reattachOuterCont outerCont?
    return g.finishAndGrantPriority
  | .mayDiscardDraw q _ =>
    if p != q then
      throw s!"Only {(g.player q).name} may decline to discard"
    let outerCont? := g.pendingReplacement
    let g := if outerCont?.isSome then g.change (.pendingReplacement none) else g
    let g := (g.change (.pending .none)).logMsg s!"{(g.player p).name} declines to discard a card"
    let g := g.reattachOuterCont outerCont?
    return g.finishAndGrantPriority
  | .chooseTargets caster =>
    if caster != p then
      throw s!"Only {(g.player caster).name} may choose targets (CR 601.2c)"
    let some obj := g.objectAwaitingTargets | throw "No spell is waiting for a target (CR 601.2c)"
    if g.canSkipCurrentOptionalSlot obj then
      let spec := g.targetSpecOf obj
      let curPos := g.currentTargetSlot obj
      let (_, grpEnd) := spec.instanceGroupBounds curPos
      let span := ((List.range grpEnd).drop curPos)
      if !span.all spec.isOptionalPos then
        let reqCount := span.filter (!spec.isOptionalPos ·) |>.length
        throw s!"Choose at least {reqCount} target(s) (CR 601.2c)"
      let g := span.foldl (fun acc _ => acc.skipOptionalTargetSlot obj.id) g
      let g := g.logMsg
        s!"{(g.player p).name} chooses no target (CR 603.3d / 601.2c)"
      if g.currentTargetSlot obj < spec.totalPositions then
        return g.change (.pending (.chooseTargets p))
      let g :=
        match g.stackEntry? obj.id with
        | some e => g.setStackEntryTargets obj.id e.targets e.dividedDamage
        | none => g
      if g.proposedSpell.any (·.spellId == obj.id) then
        return g.afterTargetsChosen
      return g.afterTriggerTargetsChosen
    else if g.canFinishOptionalTargets obj then
      let startPos := g.currentTargetSlot obj
      let totalPos := (g.targetSpecOf obj).totalPositions
      let g := (List.range (totalPos - startPos)).foldl
        (fun acc _ => acc.skipOptionalTargetSlot obj.id) g
      let g := g.logMsg
        s!"{(g.player p).name} finishes choosing targets (CR 601.2c)"
      let g :=
        match g.stackEntry? obj.id with
        | some e => g.setStackEntryTargets obj.id e.targets e.dividedDamage
        | none => g
      if g.proposedSpell.any (·.spellId == obj.id) then
        return g.afterTargetsChosen
      return g.afterTriggerTargetsChosen
    else
      match obj.triggeredAbility with
      | some ab =>
        if !(ab.allowsZeroTargets || ab.targetSpec.allowsZero ||
            obj.abilityEffect.any (fun e => e.allowsZeroTargets || e.effectiveTargetSpec.allowsZero)) then
          throw "That ability requires a target (CR 601.2c)"
        let g := g.setStackEntryTargets obj.id #[]
        let g := g.logMsg
          s!"{(g.player p).name} chooses no target (CR 603.3d / 601.2c)"
        return g.afterTriggerTargetsChosen
      | none =>
        let allowZero :=
          (g.targetSpecOf obj).allowsZero ||
          match g.currentSpellEffect obj with
          | some e => e.allowsZeroTargets
          | none =>
            match obj.abilityEffect with
            | some e => e.allowsZeroTargets
            | none => false
        if allowZero then
          let g := g.setStackEntryTargets obj.id #[]
          let g := g.logMsg
            s!"{(g.player p).name} chooses no target (CR 603.3d / 601.2c)"
          if g.proposedSpell.any (·.spellId == obj.id) then
            return g.afterTargetsChosen
          return g.afterTriggerTargetsChosen
        throw "That spell requires a target (CR 601.2c)"
  | .mayPayGeneric q _ =>
    if p != q then
      throw s!"Only {(g.player q).name} may decline to pay"
    let outerCont? := g.pendingReplacement
    let g := if outerCont?.isSome then g.change (.pendingReplacement none) else g
    let g := (g.change (.pending .none)).logMsg s!"{(g.player p).name} declines to pay"
    let g := g.reattachOuterCont outerCont?
    return g.finishAndGrantPriority
  | .payOrLetCounter q _ spellId =>
    if p != q then
      throw s!"Only {(g.player q).name} may decline to pay"
    let outerCont? := g.pendingReplacement
    let g := if outerCont?.isSome then g.change (.pendingReplacement none) else g
    let g := g.logMsg s!"{(g.player p).name} does not pay"
    let caster := (g.currentResolvingContext?.bind Prod.snd).getD (g.opponent p)
    let g := g.changes #[
      .pending .none,
      .bindStepOutcome interpChoiceVar { succeeded := false }]
    let g :=
      match spellId with
      | some sid => g.counterStackSpell sid (controller := some caster)
      | none => g
    let g := g.reattachOuterCont outerCont?
    return g.finishAndGrantPriority
  | .payWard q spellId _ chosen =>
    if !chosen.isEmpty then
      throw s!"{(g.player p).name} already began sacrificing permanents for ward and must finish"
    if p != q then
      throw s!"Only {(g.player q).name} may decline to pay ward"
    let outerCont? := g.pendingReplacement
    let g := if outerCont?.isSome then g.change (.pendingReplacement none) else g
    let g := (g.change (.pending .none)).logMsg s!"{(g.player p).name} does not pay ward"
    let wardCtrl := (g.resolvingAbilityObject?.bind (·.controller)).getD (g.opponent p)
    let g := g.counterStackSpell spellId (controller := some wardCtrl)
    return g.finishWardAndDrain outerCont?
  | .mayAttachEquipment q .. =>
    if p != q then
      throw s!"Only {(g.player q).name} may decline to attach Equipment"
    let outerCont? := g.pendingReplacement
    let g := if outerCont?.isSome then g.change (.pendingReplacement none) else g
    let g := (g.change (.pending .none)).logMsg s!"{(g.player p).name} declines to attach Equipment"
    let g := g.reattachOuterCont outerCont?
    return g.finishAndGrantPriority
  | .mayResolve q =>
    if p != q then
      throw s!"Only {(g.player q).name} may decline"
    let outerCont? := g.pendingReplacement
    let g := if outerCont?.isSome then g.change (.pendingReplacement none) else g
    let g := g.logMsg s!"{(g.player p).name} declines"
    let g := g.changes #[
      .pending .none,
      .bindStepOutcome interpChoiceVar { succeeded := false }]
    let g := g.reattachOuterCont outerCont?
    return g.finishAndGrantPriority
  | .tapHumans q =>
    if p != q then
      throw s!"Only {(g.player q).name} may decline to tap Humans"
    let outerCont? := g.pendingReplacement
    let g := if outerCont?.isSome then g.change (.pendingReplacement none) else g
    let g := (g.change (.pending .none)).logMsg s!"{(g.player p).name} taps no Humans"
    let g := g.reattachOuterCont outerCont?
    return g.finishAndGrantPriority
  | .maySacrificeAnotherBolg q _ =>
    if p != q then
      throw s!"Only {(g.player q).name} may decline to sacrifice"
    let outerCont? := g.pendingReplacement
    let g := if outerCont?.isSome then g.change (.pendingReplacement none) else g
    let g := (g.change (.pending .none)).logMsg
      s!"{(g.player p).name} declines to sacrifice a creature to Bolg"
    let g := g.reattachOuterCont outerCont?
    return g.finishAndGrantPriority
  | .mayCastFromLooked q _ _ =>
    if p != q then
      throw s!"Only {(g.player q).name} may decline to cast a spell"
    g.chooseCastFromLooked p none
  | .mayPutLandFromHand q =>
    if p != q then
      throw s!"Only {(g.player q).name} may decline to put a land onto the battlefield"
    let outerCont? := g.pendingReplacement
    let g := if outerCont?.isSome then g.change (.pendingReplacement none) else g
    let g := (g.change (.pending .none)).logMsg
      s!"{(g.player p).name} declines to put a land onto the battlefield"
    let g := g.reattachOuterCont outerCont?
    return g.finishAndGrantPriority
  | .maySacArtifactOrDiscard q _ =>
    if p != q then
      throw s!"Only {(g.player q).name} may decline"
    let outerCont? := g.pendingReplacement
    let g := if outerCont?.isSome then g.change (.pendingReplacement none) else g
    let g := (g.change (.pending .none)).logMsg
      s!"{(g.player p).name} declines to sacrifice an artifact or discard a card"
    let g := g.reattachOuterCont outerCont?
    return g.finishAndGrantPriority
  | .mayPutArtifactFromHand q _ =>
    if p != q then
      throw s!"Only {(g.player q).name} may decline to put an artifact onto the battlefield"
    let outerCont? := g.pendingReplacement
    let g := if outerCont?.isSome then g.change (.pendingReplacement none) else g
    let g := (g.change (.pending .none)).logMsg
      s!"{(g.player p).name} declines to put an artifact onto the battlefield"
    let g := g.reattachOuterCont outerCont?
    return g.finishAndGrantPriority
  | .mayHaveVillainConnive q _ _ =>
    if p != q then
      throw s!"Only {(g.player q).name} may decline to have the Villain connive"
    let outerCont? := g.pendingReplacement
    let g := if outerCont?.isSome then g.change (.pendingReplacement none) else g
    let g := (g.change (.pending .none)).logMsg s!"{(g.player p).name} declines to have the Villain connive"
    let g := g.reattachOuterCont outerCont?
    return g.finishAndGrantPriority
  | .sacrificePermanent q excludeId =>
    if p != q then
      throw s!"Only {(g.player q).name} may act on that cost"
    if (g.proposedSpell.isNone || g.proposalCostPromptStillPayable p g.pending) &&
        !(g.sacrificeCreatureOrArtifactChoices q excludeId).isEmpty then
      throw "You must sacrifice an artifact or creature"
    g.reverseProposedSpell? (resumeContinuation := true)
  | .discardForAdditionalCost q =>
    if p != q then
      throw s!"Only {(g.player q).name} may act on that cost"
    if (g.proposedSpell.isNone || g.proposalCostPromptStillPayable p g.pending) &&
        !(g.discardableHandIds q).isEmpty then
      throw "You must discard a card"
    g.reverseProposedSpell? (resumeContinuation := true)
  | .chooseDiscardCard q remaining =>
    if g.thirstDiscardsLeft == 0 then
      throw "Not time to decline"
    if p != q then
      throw s!"Only {(g.player q).name} may decline"
    let n := g.thirstDiscardsLeft
    let perPlayer := if n > 1 then n else 0
    let tyWord := g.thirstDiscardType.oracleWord
    let art :=
      match tyWord.toList[0]? with
      | some 'a' | some 'e' | some 'i' | some 'o' | some 'u' => "an"
      | _ => "a"
    let g := g.changes #[
      .thirstDiscardsLeft 0,
      .discardCountPerPlayer perPlayer,
      .pendingDiscardsLeft perPlayer]
    let g := g.logMsg
      s!"{(g.player p).name} declines to discard {art} {tyWord} card; {(g.player p).name} must discard {n} card(s)"
    if (g.discardableHandIds p).isEmpty then
      let outerCont? := g.pendingReplacement
      let g := if outerCont?.isSome then g.change (.pendingReplacement none) else g
      let g := g.continueAfterDiscard (#[p] ++ remaining) (samePlayer := true) (count := max 1 n)
      let g := g.reattachOuterCont outerCont?
      return g.finishAndGrantPriority
    else
      return g
  | .chooseTeamworkCreatures q need =>
    if p != q then
      throw s!"Only {(g.player q).name} may act on that cost"
    if (g.proposedSpell.isNone || g.proposalCostPromptStillPayable p g.pending) &&
        ((g.creaturesControlledBy q).filter (fun c =>
          !c.status.tapped && g.power c > 0)).foldl
          (fun acc c => acc + g.power c) 0 ≥ (need : Int) then
      throw s!"You must tap creatures with total power {need} or more"
    g.reverseProposedSpell? (resumeContinuation := true)
  | _ => throw "Not time to decline"

def keepOpeningHand (g : Game) (p : PlayerId) : Except String Game := do
  match g.pending with
  | .declareMulligan q =>
    if p != q then
      throw "It's not your turn to declare a mulligan (CR 103.5)"
    let g := g.changePlayer p (.keptOpeningHand true)
    let g := g.logMsg
      s!"{g.player p |>.name} keeps their opening hand of {(g.player p).hand.size}"
    return g.afterDeclaration p
  | _ => throw "Not time to keep an opening hand (CR 103.5)"

/-- Choose which legendary permanent to keep; the rest go to their owners'
graveyards (CR 704.5j). Then resume the CR 704.3 loop: recheck state-based
actions, put waiting triggers on the stack if none remain, and grant
priority only once that process is idle. -/
def keepLegend (g : Game) (p : PlayerId) (id : ObjectId) : Except String Game := do
  match g.pending with
  | .chooseLegend q name ids =>
    if p != q then
      throw s!"Only {(g.player q).name} may choose which {name} to keep (CR 704.5j)"
    let preBatchLegendIds := g.preBatchLegendChoiceIds p name ids
    let liveIds := g.validLegendChoiceIds p name ids
    if liveIds.size < 2 then
      let outerCont? := g.pendingReplacement
      let g := if outerCont?.isSome then g.change (.pendingReplacement none) else g
      let g := g.change (.pending .none)
      let g :=
        match outerCont? with
        | some outer => g.chainPendingReplacement outer
        | none => g
      return g.finishAndGrantPriority
    if !liveIds.contains id then
      throw s!"Choose one of the legendary permanents named {name} (CR 704.5j)"
    let some kept := g.findObject? id | throw "no such object"
    let outerCont? := g.pendingReplacement
    let g := if outerCont?.isSome then g.change (.pendingReplacement none) else g
    let others := liveIds.filter (· != id)
    let rec findSweepPreBf? : PendingReplacement → Option (Array GameObject)
      | .finishSbaSweep _ pbf .. => some pbf
      | .seq a b => findSweepPreBf? a <|> findSweepPreBf? b
      | _ => none
    let sweepPreBf? :=
      (outerCont?.bind findSweepPreBf?).orElse
        (fun _ => g.outerPendingReplacements.findSomeRev? findSweepPreBf?)
    let rec hasFinishSbaSweep : PendingReplacement → Bool
      | .finishSbaSweep .. => true
      | .seq a b => hasFinishSbaSweep a || hasFinishSbaSweep b
      | _ => false
    let deferOuter : Bool :=
      outerCont?.any hasFinishSbaSweep || g.outerPendingReplacements.any hasFinishSbaSweep
    let preBf :=
      sweepPreBf?.getD
        (if g.currentBatch.isSome then g.openBatchObjects.filter GameObject.isOnBattlefield
         else g.battlefield)
    let g := g.change (.pending .none) |>.logMsg
      s!"{(g.player p).name} keeps {g.name kept} (legend rule, CR 704.5j)"
    let preLegend := g
    let legFromIdx := g.events.size
    let g := g.withBatch
      (some (.stateBased .legendRule)) fun g => Id.run do
        let mut g := g
        for i in [0:others.size] do
          let other := others[i]!
          match g.findObject? other with
          | some o =>
            if g.isMatchingLegendCandidate p name preBatchLegendIds o then
              g := g.moveToOwnerGraveyard o
                s!"{g.name o} is put into its owner's graveyard (legend rule, CR 704.5j)"
                (preBattlefield := some preBf)
                (cause := some (.stateBased .legendRule))
                (deferPlayFromExileLogs := true)
              if let .chooseReplacement .. := g.pending then
                let rem := (others.extract (i + 1) others.size).filter fun rid =>
                  (g.findObject? rid).any (g.isMatchingLegendCandidate p name preBatchLegendIds)
                if !rem.isEmpty || !deferOuter then
                  g := g.chainPendingReplacement
                    (.moveSimultaneousToGraveyard rem (some preBf) (some (.stateBased .legendRule))
                      deferOuter (if deferOuter then none else some legFromIdx))
                return g
          | none => pure ()
        return g
    let g :=
      match outerCont? with
      | some outer => g.chainPendingReplacement outer
      | none => g
    let g :=
      if !deferOuter && !g.sbaPaused then emitExpiredPlayFromExileLogs preLegend g legFromIdx
      else g
    return g.finishAndGrantPriority
  | _ => throw "Not time to apply the legend rule (CR 704.5j)"

/-- Put this player's waiting triggered abilities on the stack in the listed
0-based index order into `g.waitingTriggersOf p` (CR 603.3b). First listed is
put first (farthest from the top). -/
def stackTriggers (g : Game) (p : PlayerId) (order : Array Nat) : Except String Game := do
  match g.pending with
  | .chooseTriggerToStack q =>
    if p != q then
      throw s!"Only {(g.player q).name} may choose the order of triggered abilities (CR 603.3b)"
    let mine := g.waitingTriggersOf p
    if order.size != mine.size then
      throw "List each waiting triggered ability index once (CR 603.3b)"
    let mut seen : Array Nat := #[]
    let mut ordered : Array WaitingTrigger := #[]
    for idx in order do
      if idx >= mine.size || seen.contains idx then
        throw "List each waiting triggered ability index once (CR 603.3b)"
      seen := seen.push idx
      ordered := ordered.push mine[idx]!
    let g := (g.change (.pending .none)).logMsg
      s!"{(g.player p).name} chooses the order of triggered abilities (CR 603.3b)"
    let g := g.putTriggerBatch ordered
    if g.over || g.pending != .none then
      return g
    let prio := g.pendingPriority.getD g.activePlayer
    return g.receivePriority prio false
  | _ => throw "Not time to choose triggered-ability order (CR 603.3b)"

/-- Record that this player will mulligan. The mulligan itself is taken only
after every remaining player has declared (CR 103.5). -/
def takeMulligan (g : Game) (p : PlayerId) : Except String Game := do
  match g.pending with
  | .declareMulligan q =>
    if p != q then
      throw "It's not your turn to declare a mulligan (CR 103.5)"
    if (g.player p).keptOpeningHand then
      throw "You already kept your opening hand (CR 103.5)"
    if !g.canTakeMulligan p then
      throw "A player may not take further mulligans after their opening hand would be zero cards (CR 103.5)"
    let g := g.change (.pushWillMulligan p)
    let g := g.logMsg s!"{g.player p |>.name} will take a mulligan (CR 103.5)"
    return g.afterDeclaration p
  | _ => throw "Not time to take a mulligan (CR 103.5)"

/-- Place the listed cards on the bottom of `p`'s library. The first listed
card becomes the new bottom; later cards sit above it. -/
def putCardsOnBottom (g : Game) (p : PlayerId) (ids : Array ObjectId) : Except String Game := do
  match g.pending with
  | .putOnBottom q n =>
    if p != q then
      throw "Only the player who took a mulligan may put cards on the bottom (CR 103.5)"
    if ids.size != n then
      throw s!"Put exactly {n} card(s) on the bottom of your library (CR 103.5)"
    if !uniqueObjectIds ids then
      throw "Duplicate card"
    let pl := g.player p
    for id in ids do
      match g.findObject? id with
      | none => throw "no such object"
      | some o =>
        if !pl.hand.contains id then
          throw "That card is not in your hand"
        if !isDiscardableCard o then
          throw "You can only put a card from your hand on the bottom of your library"
    let isInGame := g.mulliganToBottom.isEmpty
    let bottomCause : EventCause :=
      if isInGame then g.resolvingOrRuleCause p else .gameRule .mulligan
    let outerCont? := g.pendingReplacement
    let g := if outerCont?.isSome then g.change (.pendingReplacement none) else g
    let g := if isInGame then g.change (.pending .none) else g
    let g := g.withBatch (some bottomCause) fun g => Id.run do
      let mut g := g
      let mut placed : Nat := 0
      for i in [0:ids.size] do
        let id := ids[i]!
        match g.findObject? id with
        | none => pure ()
        | some card =>
          let cardName := g.name card
          let ownerName := (g.player p).name
          let libSize := ((g.player p).library.filter (· != id)).size
          let pos : LibraryPosition :=
            if placed == 0 then .bottom else .fromTop (libSize - Nat.min placed libSize)
          let (g', newId) := g.move id (.library p) (libraryPosition := some pos)
            (cause := some bottomCause)
          g := g'
          if let .chooseReplacement .. := g.pending then
            let msg := s!"{ownerName} puts {cardName} on the bottom of their library"
            g := g.chainPendingReplacement
              (.finishPostStep (.logPutOnOwnerLibrary id p cardName false (some msg)))
            let rem := ids.extract (i + 1) ids.size
            if !rem.isEmpty then
              g := g.chainPendingReplacement
                (.finishPostStep (.moveIdsInOrderLoop rem (.library p) "" (some bottomCause) placed (some (id, .library p))))
              for rid in rem do
                if let some rcard := g.findObject? rid then
                  let rname := g.name rcard
                  let rmsg := s!"{ownerName} puts {rname} on the bottom of their library"
                  g := g.chainPendingReplacement
                    (.finishPostStep (.logPutOnOwnerLibrary rid p rname false (some rmsg)))
            return g
          if (g.findObject? newId).any (·.zone == .library p) then
            placed := placed + 1
            g := g.logMsg s!"{ownerName} puts {cardName} on the bottom of their library"
      return g
    let g := g.reattachOuterCont outerCont?
    let mut g := g
    if isInGame then
      return g.finishAndGrantPriority
    -- After a mulligan to zero, the player may not take further mulligans.
    if !g.canTakeMulligan p then
      g := g.changePlayer p (.keptOpeningHand true)
      g := g.logMsg
        s!"{g.player p |>.name} keeps their opening hand of {(g.player p).hand.size}"
    return g.afterBottom p
  | _ => throw "Not time to put cards on the bottom (CR 103.5)"

/-- Apply a `--norandom` permutation or chosen object. -/
def supplyOrder (g : Game) (ids : Array ObjectId) : Except String Game := do
  match g.pending with
  | .resolveRandom req =>
    let outerCont? := if g.pregameRandom == .none then g.pendingReplacement else none
    let g := if outerCont?.isSome then g.change (.pendingReplacement none) else g
    let reattachAndFinish (g : Game) : Game :=
      let g := g.reattachOuterCont outerCont?
      g.finishHostRandom
    match req with
    | .shuffleLibrary p =>
      let pl := g.player p
      let ids := if ids.isEmpty then pl.library else ids
      if !isPermutation ids pl.library then
        throw "Shuffle must list each library card once (bottom first), or omit the ids to keep the current order"
      let isPregame := g.pregameRandom != .none
      let shuffleCause : EventCause :=
        match g.pregameRandom with
        | .openingShuffles _ => .gameRule .openingHandDraw
        | .mulliganDraw .. | .mulliganQueue .. => .gameRule .mulligan
        | _ => g.resolvingOrRuleCause p
      let g := g.change (.pending .none)
      let g := g.record (GameEvent.shuffled g.turnNumber p ids (cause := some shuffleCause))
      if isPregame then return g.finishAfterRandom true
      else return reattachAndFinish (g.finishAfterRandom false)
    | .orderInto expected dest cause =>
      let ids := if ids.isEmpty then expected else ids
      if !isPermutation ids expected then
        throw "Order must list each of those cards once, or omit the ids to keep their current order"
      let g := g.change (.pending .none)
      let g := g.moveIdsInOrder ids dest (cause := cause)
      if let .chooseReplacement .. := g.pending then
        let after := g.afterRandom
        let g :=
          if after != .none then
            (g.change (.afterRandom .none)).chainPendingReplacement
              (.finishPostStep (.runAfterRandom after))
          else g
        return reattachAndFinish g
      return reattachAndFinish (g.finishAfterRandom false)
    | .chooseObject choices =>
      match ids[0]?, ids.size with
      | some id, 1 =>
        if !choices.contains id then
          throw "That is not one of the random choices"
        return reattachAndFinish (g.autoResolveSingleChooseObject id)
      | _, _ => throw "Pick exactly one of the listed objects"
    | .chooseIndex _ =>
      throw "Supply an index (random <n> or flip heads/tails)"
  | _ => throw "No random event is waiting for a result"

/-- Apply a `--norandom` index (starting player, coin toss). -/
def supplyIndex (g : Game) (i : Nat) : Except String Game := do
  match g.pending with
  | .resolveRandom (.chooseIndex n) =>
    if i >= n then
      throw s!"Choose a number from 0 to {n - 1}"
    let outerCont? := if g.pregameRandom == .none then g.pendingReplacement else none
    let g := if outerCont?.isSome then g.change (.pendingReplacement none) else g
    let g := g.change (.pending .none)
    match g.pregameRandom with
    | .setStartingPlayer _ =>
      return finishAfterRandom (g.change (.pregameRandom (.setStartingPlayer i))) true
    | _ =>
      let g := g.finishAfterRandom false
      let g := g.reattachOuterCont outerCont?
      return g.finishHostRandom
  | .resolveRandom _ =>
    throw "This random event needs an order or a chosen object, not an index"
  | _ => throw "No random event is waiting for a result"

/-- Supply one random answer from `rng` when `g` is waiting on
`Pending.resolveRandom`. -/
def resolveOneRandom (g : Game) (rng : Rng) : Rng × Game :=
  match g.pending with
  | .resolveRandom (.shuffleLibrary p) =>
    let (rng, ordered) := rng.shuffle (g.player p).library
    match g.supplyOrder ordered with
    | .ok g' => (rng, g')
    | .error _ => (rng, g)
  | .resolveRandom (.orderInto ids _ _) =>
    let (rng, ordered) := rng.shuffle ids
    match g.supplyOrder ordered with
    | .ok g' => (rng, g')
    | .error _ => (rng, g)
  | .resolveRandom (.chooseObject choices) =>
    if choices.isEmpty then (rng, g)
    else
      let (rng, r) := rng.next
      let chosen := choices[(r.toNat % choices.size)]!
      match g.supplyOrder #[chosen] with
      | .ok g' => (rng, g')
      | .error _ => (rng, g)
  | .resolveRandom (.chooseIndex n) =>
    if n == 0 then (rng, g)
    else
      let (rng, r) := rng.next
      match g.supplyIndex (r.toNat % n) with
      | .ok g' => (rng, g')
      | .error _ => (rng, g)
  | _ => (rng, g)

/-- Resolve all chained `Pending.resolveRandom` requests using `rng`. -/
partial def resolvePendingRandom (g : Game) (rng : Rng) : Rng × Game :=
  match g.pending with
  | .resolveRandom _ =>
    let (rng', g') := g.resolveOneRandom rng
    if g'.pending == g.pending then (rng', g')
    else g'.resolvePendingRandom rng'
  | _ => (rng, g)

/-- Resolve all chained `Pending.resolveRandom` requests using `rng`
(defaulting to seed 1). -/
def resolveRandom (g : Game) (rng : Rng := Rng.ofSeed 1) : Game :=
  (g.resolvePendingRandom rng).2

/-- Choose which applicable replacement or prevention effect to apply next (CR 616.1). -/
def chooseReplacement (g : Game) (p : PlayerId) (id : ReplacementId) : Except String Game := do
  match g.pending with
  | .chooseReplacement q choices =>
    if !g.decidesFor p q then
      throw s!"Only {(g.player q).name} may choose a replacement effect"
    let validOpenPrompt : Bool ←
      match id.kind with
      | .asEntersChooseCreatureTypePrompt =>
        throw "Name a creature type"
      | .asEntersChooseCardNamePrompt =>
        throw "Name a nonland card"
      | .asEntersChooseCreatureType sub =>
        if !sub.isCreatureType then
          throw s!"{sub.englishName} is not a creature type"
        pure (choices.contains { id with kind := .asEntersChooseCreatureTypePrompt })
      | .asEntersChooseCardName nm =>
        if !g.isNonlandCardName nm then
          throw s!"{nm} isn't the name of a nonland card (CR 201.4a)"
        pure (choices.contains { id with kind := .asEntersChooseCardNamePrompt })
      | _ => pure false
    let effectiveId :=
      if choices.contains id then id
      else if id.counterKind.isNone then
        (choices.find? (fun c => { c with counterKind := none } == id)).getD id
      else id
    if !choices.contains effectiveId && !validOpenPrompt then
      throw "Replacement effect is not among the applicable choices"
    let chooser := effectiveId.player.getD q
    let g ←
      match effectiveId.kind with
      | .entersUntappedPayLife n =>
        g.payLifeCost chooser n (forObject := effectiveId.object)
      | .entersUntappedBehold beholdId subtype =>
        let okPerm :=
          (g.findObject? beholdId).any (fun o =>
            o.isOnBattlefield && g.controlledBy o chooser && g.hasSubtype o subtype)
        let okHand :=
          (g.player chooser).hand.contains beholdId &&
            (g.findObject? beholdId).any (fun o => isDiscardableCard o && g.hasSubtype o subtype)
        if !okPerm && !okHand then
          throw s!"{(g.player chooser).name} cannot behold that {subtype}"
        let cause := EventCause.costPayment .behold chooser effectiveId.object
        let g := g.withBatch (some cause) fun g =>
          let g :=
            if okHand then
              g.record (GameEvent.revealed g.turnNumber chooser #[beholdId] (cause := some cause))
            else g
          g.record (GameEvent.beheld g.turnNumber chooser subtype (cause := cause))
        pure (g.logMsg s!"{(g.player chooser).name} beholds a {subtype}")
      | .asEntersChooseColor col =>
        pure (g.logMsg s!"{(g.player chooser).name} chooses {col.englishName}")
      | .asEntersChooseCreatureType sub =>
        pure (g.logMsg s!"{(g.player chooser).name} chooses {sub.englishName}")
      | .asEntersChooseOdd odd =>
        let word := if odd then "odd" else "even"
        pure (g.logMsg s!"{(g.player chooser).name} chooses {word}")
      | .asEntersChooseCardName nm =>
        pure (g.logMsg s!"{(g.player chooser).name} chooses {nm}")
      | .asEntersChooseCardType ct =>
        pure (g.logMsg s!"{(g.player chooser).name} chooses {ct}")
      | .asEntersChooseAnchor anch =>
        pure (g.logMsg s!"{(g.player chooser).name} chooses {anch}")
      | .entersAsCopyCreatureUntilEot tid =>
        let nm := ((g.findObject? tid).map g.name).getD "a creature"
        pure (g.logMsg s!"{(g.player chooser).name} chooses {nm}")
      | .asEntersAttachAura hid =>
        let nm := ((g.findObject? hid).map g.name).getD "a permanent"
        pure (g.logMsg s!"{(g.player chooser).name} attaches it to {nm}")
      | _ => pure g
    let order := (g.replacementOrder.filter (· != effectiveId)).push effectiveId
    let cont? := g.pendingReplacement
    let g := (g.changes #[.replacementOrder order, .pending .none, .pendingReplacement none]).popEmptyTopContinuationFrames
    let g :=
      match cont? with
      | some cont => g.resumePendingReplacement cont
      | none => g
    let g := g.drainPendingContinuations
    let g :=
      if !g.over && g.pending == .none && g.afterRandom == .none &&
          g.proposedSpell.isNone &&
          (g.pendingMayCastFromExile.isSome || g.pendingFreeCopies.isSome) then
        let g := g.reopenDeferredExileCasts
        if let .chooseReplacement .. := g.pending then
          if g.anyContinuationSettlesControlFlow then g
          else g.chainPendingReplacement .finishResolutionChoice
        else if !g.over && g.pending == .none && g.afterRandom == .none then
          g.finishResolutionChoice
        else g
      else g
    let g :=
      if g.over || (g.pending == .none && g.afterRandom == .none) then
        g.completeActiveResolutions
      else g
    return g
  | _ =>
    throw "No replacement effect choice is pending"

end Game
end Mtg.Engine
