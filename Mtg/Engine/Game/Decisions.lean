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

/-- Explicit priority recipient encoded by a pending replacement continuation
(e.g. `.finishPostCast` for a non-active caster, CR 117.3c). -/
private def priorityRecipientOfContinuation? (g : Game) : PendingReplacement → Option PlayerId
  | .finishPostCast caster true _ false => some caster
  | .finishBecomeCast caster _ true false false => some caster
  | .finishProposedSpellCosts _ true false false => g.proposedSpell.map (·.caster)
  | .receivePriority p => some p
  | .seq a b =>
    priorityRecipientOfContinuation? g b |>.orElse (fun _ => priorityRecipientOfContinuation? g a)
  | _ => none

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

mutual
/-- Drain queued `g.pendingReplacement` continuations and paused
`triggerSequenceRest` steps while no interactive `Pending` or `afterRandom`
choice is open. -/
partial def drainPendingContinuations (g : Game) : Game :=
  if g.over || g.pending != .none || g.afterRandom != .none then g
  else if g.mayThenResume then
    g.acceptMayThenCore.drainPendingContinuations
  else
    match g.pendingReplacement with
    | some cont =>
      let g := (g.change (.pendingReplacement none)).resumePendingReplacement cont
      g.drainPendingContinuations
    | none =>
      if g.triggerSequenceRest.isSome then
        let g := g.resumeTriggerSequence
        g.drainPendingContinuations
      else
        match g.outerPendingReplacements.back? with
        | some outer =>
          let g := (g.change .popOuterPendingReplacement).resumePendingReplacement outer
          g.drainPendingContinuations
        | none => g

/-- Drain active continuations, chain `.receivePriority p` if a CR 616.1
`Pending.chooseReplacement` pause opened, or grant priority to `p` when idle. -/
partial def finishAndGrantPriority (g : Game)
    (p : PlayerId :=
      (g.pendingReplacement.bind (priorityRecipientOfContinuation? g)).orElse
        (fun _ => g.outerPendingReplacements.findSomeRev? (priorityRecipientOfContinuation? g))
        |>.getD g.activePlayer) : Game :=
  let anyContinuationGrantsPriority (g : Game) : Bool :=
    g.pendingReplacement.any PendingReplacement.endsWithPriorityGrant ||
      g.outerPendingReplacements.any PendingReplacement.endsWithPriorityGrant
  let alreadyGrants : Bool :=
    g.pending == .none && g.afterRandom == .none && anyContinuationGrantsPriority g
  let g := g.drainPendingContinuations
  if g.over then g
  else if let .chooseReplacement .. := g.pending then
    if anyContinuationGrantsPriority g then g
    else g.chainPendingReplacement (.receivePriority p)
  else if g.pending != .none || g.afterRandom != .none || alreadyGrants then g
  else g.receivePriority p

/-- Run trigger-sequence steps and pending continuations, then give priority when
nothing else is pending. -/
partial def resumeSequenceThenPriority (g : Game) : Game :=
  g.finishAndGrantPriority

/-- Clear `mayThen` state when its optional action was performed, running its
conditional before any outer continuation, or chain `.acceptMayThen` if the
optional action paused on `Pending.chooseReplacement`. -/
partial def acceptMayThenCore (g : Game) : Game :=
  if let .chooseReplacement .. := g.pending then
    g.chainPendingReplacement .acceptMayThen
  else
    let g :=
      match g.pendingReplacement with
      | some outer => g.changes #[.pendingReplacement none, .pushOuterPendingReplacement outer]
      | none => g
    let g := g.changes #[
      .pending .none,
      .mayThenDrop 0,
      .mayThenConditional none,
      .mayThenResume false ]
    if g.afterRandom == .none && g.triggerSequenceRest.isSome then
      g.resumeTriggerSequence
    else g

/-- The optional action of `mayThen` was performed. Run its conditional, or
defer via `.acceptMayThen` if the optional action paused on `Pending.chooseReplacement`. -/
partial def acceptMayThen (g : Game) : Game :=
  g.acceptMayThenCore.resumeSequenceThenPriority

/-- The optional action of `mayThen` was declined. Skip its conditional and
continue any later sequence steps. -/
partial def declineMayThen (g : Game) : Game :=
  g.declineMayThenCore.resumeSequenceThenPriority

/-- Continue a discard chain. When no one is left to discard, put the waiting
+1/+1 counter (Ninja of the Hand) if any. -/
partial def continueAfterDiscard (g : Game) (players : Array PlayerId)
    (samePlayer : Bool := false) (count : Nat := 1) : Game :=
  let g := g.beginDiscardCards players (count := count) (samePlayer := samePlayer) (resuming := true)
  if g.pending != .none then g
  else if g.plusOneAfterDiscards.isSome then g.finishPlusOneAfterDiscards
  else g

/-- Clear a finished Reality Fracture choice and let the game continue. Any
pending replacement/batch continuation runs first, then a paused trigger
sequence runs its remaining steps. -/
partial def finishFraChoice (g : Game) : Game :=
  if let .chooseReplacement .. := g.pending then
    if g.pendingReplacement.any (·.endsWithFinishFra) then g
    else g.chainPendingReplacement .finishFraChoice
  else if g.pending != .none then g
  else
    let g := g.drainPendingContinuations
    if let .chooseReplacement .. := g.pending then
      g.chainPendingReplacement .finishFraChoice
    else if g.pending != .none || g.afterRandom != .none || g.over then g
    else
      let prio := g.pendingPriority.getD g.activePlayer
      let g := g.promptTriggerTargetsIfNeeded
      if g.pending == .none then g.receivePriority prio else g

/-- Clear `.payWard` and drain any queued `pendingReplacement` /
`outerPendingReplacements` continuations before priority or trigger targets. -/
partial def finishWardAndDrain (g : Game)
    (outerCont? : Option PendingReplacement := none) : Game :=
  let g := g.afterWardResolved
  let g :=
    match outerCont? with
    | some outer => g.chainPendingReplacement outer
    | none => g
  g.drainPendingContinuations

/-- Apply the stashed `unlessPaysInstead` fallback effect when the payer of a
pending `.payOrLetCounter` leaves the game (CR 800.4a / 800.4f), preserving any
queued `pendingReplacement` continuation and resuming active continuations via
`finishAndGrantPriority` (matching `decline` `.payOrLetCounter`). -/
partial def flushUnlessPays (g : Game) : Game :=
  if !g.unlessPaysDue then g
  else
    let outerCont? := g.pendingReplacement
    let g := if outerCont?.isSome then g.change (.pendingReplacement none) else g
    let instead := g.unlessPaysInstead
    let caster := g.unlessPaysController
    let targets := g.unlessPaysTargets
    let sourceId := g.unlessPaysSource
    let g := g.clearUnlessPays
    let g :=
      match instead with
      | some effect => g.applyUnified caster effect targets (sourceId := sourceId)
      | none => g
    let g :=
      match outerCont? with
      | some outer => g.chainPendingReplacement outer
      | none => g
    g.finishAndGrantPriority

/-- Finish an idle-priority or combat-assignment concession after any CR 616.1 /
704.5j SBA pause inside `playerLeavesGame` or `checkSBA` completes (CR 800.4a /
117.3). -/
partial def finishConcedePriority (g : Game) (wasIdlePriority : Bool)
    (savedPendingPrio : Option PlayerId)
    (wasAssigningCombatDamage : Option Bool := none)
    (savedPending : Option Pending := none)
    (popOuter : Bool := false)
    (runSba : Bool := false) : Game :=
  let g := if runSba && !g.over then g.checkSBA else g
  if g.over then g
  else if g.sbaPaused then
    g.chainPendingReplacement
      (.finishConcede wasIdlePriority savedPendingPrio wasAssigningCombatDamage savedPending popOuter)
  else if g.unlessPaysDue then
    g.flushUnlessPays
  else
    let g :=
      match savedPending with
      | some sp =>
        if g.pending == .none then g.resumePendingReplacement (.restorePending sp popOuter) else g
      | none => g
    if g.pending != .none then g
    else if let some fa := wasAssigningCombatDamage then
      if fa then g.beginCombatDamageAssignment else g.continueBlockerCombatAssignment
    else if !g.continuations.isEmpty || g.pendingReplacement.isSome ||
        !g.outerPendingReplacements.isEmpty ||
        g.triggerSequenceRest.isSome then
      g.finishFraChoice
    else if wasIdlePriority && g.playersReceivePriority && !g.hasWaitingTriggers &&
        g.consecutivePasses ≥ g.livingPlayers.size then
      let g := g.change (.consecutivePasses 0)
      if !g.stack.isEmpty then
        let g := g.resolveTop
        if let .chooseReplacement .. := g.pending then
          g.chainPendingReplacement (.receivePriority g.activePlayer)
        else if g.pending != .none then g
        else g.receivePriority g.activePlayer
      else
        g.advanceStep
    else if g.playersReceivePriority then
      let rawPrio := savedPendingPrio.getD g.priority
      let nextP := if g.stillInGame rawPrio then rawPrio else g.nextLiving rawPrio
      g.receivePriority nextP
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
    (popOuterIn : Bool := false) : Game := Id.run do
  if g.over then
    return g
  let mut g := g
  let mut saved? := savedIn
  let mut popOuter := popOuterIn
  for i in [0:remaining.size] do
    if g.over then
      return g
    let pid := remaining[i]!
    if !(g.player pid).leftTheGame then
      if saved?.isSome && !g.sbaPaused && g.pendingReplacement.isNone then
        g := g.restoreSavedPostLeave saved? popOuter
        saved? := none
        popOuter := false
      let (g', newlySaved?) := g.playerLeavesGameCore pid (deferRestore := true)
      g := g'
      if let some (sp, po) := newlySaved? then
        if saved?.isNone then
          saved? := some sp
          popOuter := po
      let rem := remaining.extract (i + 1) remaining.size
      if let .chooseReplacement r _ := g.pending then
        if !rem.contains r then
          let alreadyGrants :=
            g.pendingReplacement.any PendingReplacement.endsWithPriorityGrant ||
              g.outerPendingReplacements.any PendingReplacement.endsWithPriorityGrant
          if !rem.isEmpty || wasPregame || !midResolutionOrBatch || !alreadyGrants ||
              wasAssigningCombatDamage.isSome || saved?.isSome || g.unlessPaysDue then
            g := g.chainPendingReplacement
              (.concedePlayersLoop rem wasPregame midResolutionOrBatch wasIdlePriority
                savedPendingPrio wasAssigningCombatDamage saved? popOuter)
          return g
  if g.over then
    return g
  if saved?.isNone && !g.sbaPaused && g.pending != .none then
    saved? := some g.pending
    g := g.change (.pending .none)
  if wasPregame then
    if g.sbaPaused then
      return g.chainPendingReplacement
        (.concedePlayersLoop #[] true midResolutionOrBatch wasIdlePriority
          savedPendingPrio wasAssigningCombatDamage saved? popOuter)
    g :=
      match saved? with
      | some sp =>
        if g.pending == .none then g.resumePendingReplacement (.restorePending sp popOuter) else g
      | none => g
    if g.pending != .none then return g
    else if g.pregameRandom != .none then return finishAfterRandom g true
    else if !g.mulliganToDeclare.isEmpty then return g.promptMulligan g.mulliganToDeclare[0]!
    else if !g.willMulligan.isEmpty then return g.resolveDeclaredMulligans
    else if !g.mulliganToBottom.isEmpty then return g.promptBottom g.mulliganToBottom[0]!
    else if g.awaitingOpeningBegin then return g.continueOpeningBegin #[]
    else return g.beginMulliganRound
  else if midResolutionOrBatch then
    if g.sbaPaused then
      let alreadyGrants :=
        g.pendingReplacement.any PendingReplacement.endsWithPriorityGrant ||
          g.outerPendingReplacements.any PendingReplacement.endsWithPriorityGrant
      if !alreadyGrants || wasAssigningCombatDamage.isSome || saved?.isSome || g.unlessPaysDue then
        return g.chainPendingReplacement
          (.concedePlayersLoop #[] false true wasIdlePriority
            savedPendingPrio wasAssigningCombatDamage saved? popOuter)
      else
        return g
    else if g.unlessPaysDue then
      return g.flushUnlessPays
    else
      g :=
        match saved? with
        | some sp =>
          if g.pending == .none then g.resumePendingReplacement (.restorePending sp popOuter) else g
        | none => g
      if g.pending != .none then return g
      else
        return g.finishConcedePriority wasIdlePriority savedPendingPrio wasAssigningCombatDamage
          none false (runSba := false)
  else if g.sbaPaused then
    return g.chainPendingReplacement
      (.finishConcede wasIdlePriority savedPendingPrio wasAssigningCombatDamage saved? popOuter)
  else
    return g.finishConcedePriority wasIdlePriority savedPendingPrio wasAssigningCombatDamage
      saved? popOuter (runSba := true)

/-- Resume the rules event that paused on `Pending.chooseReplacement` (CR 616.1). -/
partial def resumePendingReplacement (g : Game) (pr : PendingReplacement)
    (followedByFinishFra : Bool := false) : Game :=
  match pr with
  | .seq first rest =>
    let checkReversal : Bool :=
      match first with
      | .restorePending (.fraChoice _ (.costPicks ..)) ..
      | .restorePending (.sacrificePermanent ..) ..
      | .restorePending (.discardForAdditionalCost ..) ..
      | .completeActivation ..
      | .finishProposedSpellCosts .. =>
        g.proposedSpell.isSome
      | _ => false
    let spellId? := g.proposedSpell.map (·.spellId)
    let g := g.resumePendingReplacement first
      (followedByFinishFra := followedByFinishFra || rest.endsWithFinishFra)
    let reversed :=
      checkReversal && g.proposedSpell.isNone &&
        !spellId?.any (fun sid => (g.findObject? sid).any (·.zone == .stack))
    if reversed then g
    else if g.pending != .none then
      g.chainPendingReplacement rest
    else
      g.resumePendingReplacement rest (followedByFinishFra := followedByFinishFra)
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
      let src := g.damageSourceFromSnapshot source
      g.dealDamageFrom sourceName tgt (Int.ofNat n) (deathtouch := deathtouch)
        (source := some src) (sourceSnap := some source) (cause := cause)
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
      isCopy overridePrinted adventurerCard summoningSick attachedTo enterMods cause =>
    (g.move id dest controller (tapped := tapped) (summoningSick := summoningSick)
      (attachedTo := attachedTo) (applyHope := applyHope)
      (attacking := attacking) (attackingTarget := attackingTarget)
      (returnedAsArtifact := returnedAsArtifact) (onlyFoodArtifact := onlyFoodArtifact)
      (nightBack := transformed) (extraEntersWith := extraEntersWith)
      (verb := verb) (actor := actor) (libraryPosition := libraryPosition)
      (preBattlefield := preBattlefield) (isCopy := isCopy)
      (overridePrinted := overridePrinted) (adventurerCard := adventurerCard)
      (faceDown? := some faceDown) (fromStackTime? := some fromStackTime)
      (enterMods := enterMods) (cause := cause)).1
  | .moveSimultaneousToGraveyard ids preBattlefield cause =>
    g.moveSimultaneousToGraveyard ids (preBattlefield := preBattlefield) (cause := cause)
  | .destroyPermanent targetId cause preBattlefield reason =>
    match g.findObject? targetId with
    | some tgt =>
      g.destroyPermanent tgt (preBattlefield := preBattlefield) (cause := cause) (reason := reason)
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
  | .createKindTokens controller kind n tapped attacking attackingTarget resetRecent cause =>
    g.createKindTokens controller kind n (tapped := tapped) (attacking := attacking)
      (attackingTarget := attackingTarget) (resetRecent := resetRecent) (cause := cause)
  | .createAndMarkTokensAttacking controller kind n tapped holds sourceId cause =>
    g.createAndMarkTokensAttacking controller kind n tapped holds (sourceId := sourceId)
      (cause := cause)
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
        let g := if entered.status.tapped then g.logMsg s!"{entered.name} enters tapped" else g
        g.afterLandEnters entered
      else
        let g :=
          match (attachedToHost <|> entered.attachedTo).bind g.findObject? with
          | some host => g.logMsg s!"{g.name entered} enters the battlefield attached to {g.name host}"
          | none => g.logMsg s!"{entered.name} enters the battlefield"
        g.afterPermanentEnters entered
    | none => g
  | .addExtraCombatDamageStep =>
    g.record (GameEvent.extraStepAdded g.turnNumber .combatDamage .afterCurrent
      (cause := .gameRule .stepAdvance))
  | .finishFraChoice =>
    g.finishFraChoice
  | .draw p n cause =>
    g.draw p n (cause := cause)
  | .drawOne p applied drawStepFirst cause =>
    g.drawOneWithReplacements p (applied := applied)
      (firstOfYourDrawStep? := some drawStepFirst) (cause := cause)
  | .drawSubDraws p remaining applied cause =>
    g.drawSubDraws p remaining applied (cause := cause)
  | .connive controller sourceId =>
    g.applyConnive controller sourceId
  | .finishSbaSweep moves preBattlefield stage pwMoves sagaMoves tokensOutsideBf copiesOutside illegalAuras illegalEquips illegalCreatureAtts legendGroups =>
    (g.finishSbaSweep moves preBattlefield stage pwMoves sagaMoves tokensOutsideBf
      copiesOutside illegalAuras illegalEquips illegalCreatureAtts legendGroups).1
  | .untapPermanent targetId duringUntapStep logUntap cause =>
    match g.findObject? targetId with
    | some tgt =>
      g.untapPermanent tgt (duringUntapStep := duringUntapStep)
        (logUntap := logUntap) (cause := cause)
    | none => g
  | .untapStepPermanents ids =>
    g.untapStepPermanents ids
  | .moveCardsToGraveyardLoop ids cause =>
    g.moveCardsToGraveyardLoop ids cause
  | .placeSearchedGraveyardLoop ids cause pendingLog =>
    g.placeSearchedGraveyardLoop ids cause pendingLog
  | .returnLinkedExileToHandLoop srcId ids pendingItem =>
    g.returnLinkedExileToHandLoop srcId ids pendingItem
  | .finishConcede wasIdlePriority savedPendingPrio wasAssigningCombatDamage savedPending popOuter =>
    g.finishConcedePriority wasIdlePriority savedPendingPrio wasAssigningCombatDamage
      savedPending popOuter (runSba := true)
  | .concedePlayersLoop remaining wasPregame midResolutionOrBatch wasIdlePriority savedPendingPrio wasAssigningCombatDamage savedPending popOuter =>
    g.concedePlayersLoop remaining wasPregame midResolutionOrBatch wasIdlePriority
      savedPendingPrio wasAssigningCombatDamage savedPending popOuter
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
  | .restorePending p popOuter promptLog =>
    let g :=
      if popOuter then
        match g.outerPendingReplacements.back? with
        | some popped => (g.change .popOuterPendingReplacement).chainPendingReplacement popped
        | none => g
      else g
    let openPrompt (g : Game) : Game :=
      let g := g.change (.pending p)
      match promptLog with
      | some msg => g.logMsg msg
      | none => g
    match p with
    | .fraChoice caster (.costPicks sid picks _) =>
      match picks[0]? with
      | some pick =>
        if (g.costPickCandidates caster (some sid) pick).size < pick.count then
          g.reverseProposedSpell (resumeContinuation := true)
        else
          openPrompt g
      | none => openPrompt g
    | .sacrificePermanent caster excludeId =>
      if (g.sacrificeCreatureOrArtifactChoices caster excludeId).isEmpty then
        g.reverseProposedSpell (resumeContinuation := true)
      else
        openPrompt g
    | .discardForAdditionalCost caster =>
      if (g.player caster).hand.isEmpty then
        g.reverseProposedSpell (resumeContinuation := true)
      else
        openPrompt g
    | .chooseLegend q name ids =>
      let liveIds := ids.filter fun id =>
        (g.findObject? id).any (fun o => o.isOnBattlefield && g.controlledBy o q)
      if !g.stillInGame q || liveIds.size < 2 then g
      else
        let g := g.change (.pending (.chooseLegend q name liveIds))
        match promptLog with
        | some msg => g.logMsg msg
        | none => g
    | .chooseReplacement q choices =>
      if g.stillInGame q &&
          choices.all (fun c => c.object.all (fun oid => (g.findObject? oid).isSome)) then
        openPrompt g
      else g
    | _ => openPrompt g
  | .closeBatch batchId startIdx =>
    g.finishOpenBatchAndLinkedExile batchId startIdx
  | .restorePausedBatch batchId startIdx wasDiscard cause objects players effects pending stack =>
    g.restorePausedBatch batchId startIdx wasDiscard cause objects players effects pending stack
  | .checkSBA =>
    g.checkSBA
  | .receivePriority p =>
    g.finishAndGrantPriority p
  | .completeActivation hadOuter hadOpenCont =>
    match g.proposedSpell with
    | none => g
    | some prop =>
      match g.completeActivation prop
          (hadOuterReplacement := hadOuter)
          (hadOpenContinuation := some hadOpenCont) with
      | .ok g' =>
        if hadOuter then g' else resumeAfterBecomeCast g'
      | .error _ =>
        g.reverseProposedSpell (resumeContinuation := true)
  | .finishBecomeActivated caster srcName srcId act abId srcSnap srcOrig hadOuter hadOpenCont =>
    let g := g.becomeActivated caster srcName srcId act
      (abilityId := abId)
      (sourceSnapshot := srcSnap)
      (sourceOriginal := srcOrig)
      (hadOuterReplacement := hadOuter)
      (hadOpenContinuation := some hadOpenCont)
    if hadOuter then g else resumeAfterBecomeCast g
  | .finishBecomeCast caster spellId grantPriority hadOuter hadOpenCont =>
    match g.findObject? spellId with
    | some spell =>
      let g := g.becomeCast caster spell
        (grantPriority := grantPriority)
        (hadOuterReplacement := hadOuter)
        (hadOpenContinuation := some hadOpenCont)
      if hadOuter then g else resumeAfterBecomeCast g
    | none => g
  | .finishPostCast caster grantPriority hadOuter hadOpenCont =>
    let g := g.finishPostCast caster
      (grantPriority := grantPriority)
      (hadOuterReplacement := hadOuter)
      (hadOpenContinuation := hadOpenCont)
    if hadOuter then g
    else if !grantPriority && !followedByFinishFra then g.finishFraChoice
    else resumeAfterBecomeCast g
  | .finishProposedSpellCosts stage grantPriority hadOuter hadOpenCont =>
    match g.finishProposedSpellCosts stage grantPriority hadOuter hadOpenCont with
    | .ok g' =>
      if hadOuter then g' else resumeAfterBecomeCast g'
    | .error _ =>
      g.reverseProposedSpell (resumeContinuation := true)
  | .finishTurnFaceUp caster spellId hadOuter =>
    g.completeTurnFaceUp caster spellId (hadOuterReplacement := hadOuter)
  | .endProposalAction =>
    if g.proposalCheckpoint.isSome then g.change .endProposalAction else g
  | .payCostPickItems p abilityId sourceId pick remainingIds =>
    g.payCostPickItems p abilityId sourceId pick remainingIds
  | .finishActivationExtraCosts p sourceId forObject sacrificeSource exileSource stage =>
    g.finishActivationExtraCosts p sourceId forObject sacrificeSource exileSource stage
  | .finishPostLoyaltyActivated caster srcName srcId act abId srcSnap srcOrig hadOuter hadOpenCont =>
    let g := g.finishPostLoyaltyActivated caster srcName srcId act abId srcSnap srcOrig hadOuter hadOpenCont
    if hadOuter then g else resumeAfterBecomeCast g
  | .finishActivateManaAbilityPicks p id oname mana remainingPicks remainingCostIds tap sacrificeSelf activatedIdx restriction damageYou isMountain prevPending =>
    g.finishActivateManaAbilityPicks p id oname mana remainingPicks remainingCostIds tap sacrificeSelf activatedIdx restriction damageYou isMountain prevPending
  | .finishActivateManaAbilityPostSac p id oname srcSnap mana tap activatedIdx restriction damageYou isMountain prevPending =>
    g.finishActivateManaAbilityPostSac p id oname srcSnap mana tap activatedIdx restriction damageYou isMountain prevPending
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
  | .finishPlaceSearched p fromId name tapped cause =>
    g.finishPlaceSearched p fromId name tapped (cause := cause)
  | .finishSearchedUntap p landId name =>
    g.finishSearchedUntap p landId name
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
  | .continueUnified controller effect steps targets castFromGraveyard kicked giftPromised chosenX sourceId =>
    g.runUnifiedSteps controller effect steps targets castFromGraveyard kicked giftPromised chosenX sourceId
  | .continueUnifiedAbility controller effect steps targets sourceId lastKnownPower chosenX =>
    g.runUnifiedAbilitySteps controller effect steps targets sourceId lastKnownPower chosenX
  | .continueSpellModes controller modeEffects remainingTargets castFromGraveyard kicked giftPromised chosenX sourceId empowerJaceN skippedOptionalSlots lastKnownPower =>
    g.runSpellModesAndEmpower controller modeEffects remainingTargets castFromGraveyard kicked giftPromised chosenX sourceId empowerJaceN skippedOptionalSlots lastKnownPower
  | .empowerJace controller n stage targetId cause =>
    g.empowerJaceStep controller n stage targetId cause
  | .continueTriggeredSequence controller steps sourceId targets dividedDamage lastKnownPower lastKnownToughness sourceName =>
    g.runTriggeredSequenceSteps controller steps sourceId targets dividedDamage lastKnownPower lastKnownToughness sourceName
  | .continueTriggeredModes controller ab remainingModes sourceId targets dividedDamage lastKnownPower lastKnownToughness sourceName =>
    g.runChosenTriggeredModes controller ab remainingModes sourceId targets dividedDamage lastKnownPower lastKnownToughness sourceName
  | .continueConnives controller remainingIds =>
    g.runConniveObjects controller remainingIds
  | .dealDamageToEachCreatureMatching remainingIds n onlyNonSubtype exceptControllerTokens source cause startEventIdx suppressLifelink =>
    g.dealDamageToEachCreatureMatchingIds remainingIds n
      (onlyNonSubtype := onlyNonSubtype)
      (exceptControllerTokens := exceptControllerTokens)
      (source := source) (cause := cause)
      (startEventIdx := startEventIdx) (suppressLifelink := suppressLifelink)
  | .destroyPermanentsLoop remainingIds allCandidates countNote obGainLifeFor logMsgAfter preBattlefield cause =>
    g.destroyPermanentsLoop remainingIds
      (allCandidates := allCandidates) (countNote := countNote)
      (obGainLifeFor := obGainLifeFor) (logMsgAfter := logMsgAfter)
      (preBattlefield := preBattlefield) (cause := cause)
  | .sacrificePermanentsLoop remaining preBattlefield cause createBeastFor passiveLog =>
    g.sacrificePermanentsLoop remaining
      (preBattlefield := preBattlefield) (cause := cause)
      (createBeastFor := createBeastFor) (passiveLog := passiveLog)
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
  | .exilePermanentsLoop remainingIds logExile cause logCard =>
    g.exilePermanentsLoop remainingIds (logExile := logExile) (cause := cause)
      (logCard := logCard)
  | .causeDealsDamageToOpponentsLoop remainingOpps n name causeSrc cause pendingDmg =>
    g.causeDealsDamageToOpponentsLoop remainingOpps n name causeSrc cause pendingDmg
  | .flickerLoop remainingIds exiledPreIds enteredFromIds logText stage tapped onlyLandTapped clearExileFields cause preBattlefield =>
    g.resumeFlickerLoop remainingIds exiledPreIds enteredFromIds logText stage
      tapped onlyLandTapped clearExileFields cause preBattlefield
  | .finishMillSubtypeOrEnchantment p preIds subtype =>
    g.finishMillSubtypeOrEnchantment p preIds subtype
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
  | .makeFrcLoop p kind remaining x extraCounters cause =>
    g.makeFrcLoop p kind remaining x extraCounters cause
  | .finishFrcRestBottom p rest shuffle cause dackTargets =>
    g.finishFrcRestBottom p rest shuffle (cause := cause) (dackTargets := dackTargets)
  | .finishFrcPostStep step =>
    g.runFrcPostStep step
  | .finishPostStep step =>
    g.runPostStep step
  | .acceptMayThen =>
    g.acceptMayThenCore
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
  | .leavePlayersWhoLost savedPending popOuter =>
    g.leavePlayersWhoLost savedPending popOuter
  | .endControlExileLoop remaining cause pendingLog =>
    g.runEndControlExileLoop remaining (cause := cause) (pendingLog := pendingLog)
  | .beginStepCont st =>
    g.beginStepCont st
  | .finishCleanupAfterClearEot =>
    g.finishCleanupAfterClearEot
  | .continueStartNextTurn nextP remainingDeparted runBeginTurn =>
    g.continueStartNextTurn nextP remainingDeparted runBeginTurn
  | .beginTurnAfterStartExpiry =>
    g.beginTurnAfterStartExpiry

/-- Execute a deferred `PostStep` continuation after a CR 616.1
`Pending.chooseReplacement` pause finishes. -/
partial def runPostStep (g : Game) (step : PostStep) : Game :=
  match step with
  | .putArtifactOntoBattlefield p cardId hostId =>
    match g.followMovedToZone? cardId (· == .battlefield) with
    | some entered =>
      let g := g.logMsg s!"{(g.player p).name} puts {entered.name} onto the battlefield"
      let g := g.afterPermanentEnters entered
      if let some hid := hostId then g.change (.putArtifactThisWay (some (entered.id, hid))) else g
    | none => g
  | .copyEnteredArtifact controller artifactId =>
    g.copyEnteredArtifact controller artifactId
  | .grantHandSizePower sourceId =>
    g.grantHandSizePower sourceId
  | .beginScryOne p =>
    g.beginScry p 1
  | .copyCastTriggerSpell p =>
    g.copyCastTriggerSpell p
  | .destroyTargetLandThenOfferSearchBasics controller sourceId cardId =>
    match cardId.bind g.findObject? with
    | some o =>
      if o.isOnBattlefield && g.isLand o && g.canBeTargetedBy controller o sourceId then
        let owner := o.owner
        let g := g.destroyPermanent o
        if let .chooseReplacement .. := g.pending then
          g.chainPendingReplacement (.finishPostStep (.offerMaySearchBasics owner))
        else
          g.offerMaySearchBasics owner
      else g.logMsg "The target is no longer legal"
    | none => g.logMsg "The target is no longer legal"
  | .offerMaySearchBasics owner =>
    g.offerMaySearchBasics owner
  | .continueDiscardTwo controller rest draws chosen =>
    g.continueDiscardTwo controller rest draws chosen
  | .finishDiscardTwoDraws controller baseDraws oppIds startIdx =>
    g.finishDiscardTwoDraws controller baseDraws oppIds startIdx
  | .enteredBattlefieldPutRestBottomRandom p cardId rest cause =>
    let g :=
      match g.followMovedToZone? cardId (· == .battlefield) with
      | some entered => (g.logMsg s!"{entered.name} enters the battlefield").afterPermanentEnters entered
      | none => g
    if rest.isEmpty then g
    else
      g.requestOrderInto rest (.library p)
        s!"{(g.player p).name} puts the rest on the bottom of their library in a random order"
        (cause := cause)
  | .hawkeyeArrows controller modes targets targetIdx sourceId =>
    g.runHawkeyeArrows controller modes targets targetIdx sourceId
  | .loseLifeForLoggedDraws p beforeDraws =>
    let drawn := g.loggedDraws p - beforeDraws
    g.loseLife p drawn
  | .returnTappedWithEndStepExile controller cardId sourceId cause =>
    match g.followMovedToZone? cardId (· == .battlefield) with
    | some entered =>
      let g := g.logMsg s!"{entered.name} returns to the battlefield tapped under {(g.player controller).name}'s control"
      let src := (sourceId.bind g.findObject?).orElse (fun _ => some entered)
      let g := g.registerDelayedTrigger
        { controller, source := src, kind := .endStepExile entered.id, cause }
      g.afterPermanentEnters entered
    | none => g
  | .beginDiscardThenStun controller sourceId =>
    let cnt := Nat.min 2 (g.player controller).hand.size
    if cnt == 0 then g
    else
      g.beginFraChoice controller (.discardThenStun cnt sourceId)
        s!"{(g.player controller).name} discards {cnt} card(s)"
  | .afterRecentTokensEnter =>
    g.recentTokenIds.foldl (fun g tid =>
      match g.findObject? tid with
      | some entered => if entered.isOnBattlefield then g.afterPermanentEnters entered else g
      | none => g) g
  | .drainOpponents controller amount sourceId cause =>
    g.drainOpponents controller amount (sourceId.bind g.findObject?) (cause := cause)
  | .addPlusOnesForLoggedDiscards p sourceId =>
    let cnt := g.loggedDiscards p
    match sourceId.bind (fun id => (g.findObject? id).filter (·.isOnBattlefield)) with
    | some o => if cnt > 0 then g.addPlusOnePlusOneTo o cnt else g
    | none => g
  | .addRedManaIfPositive p count sourceId =>
    if count > 0 then g.addManaLogged p #[.colored .red] (source := sourceId) else g
  | .enteredBattlefieldSilent cardId isLand
  | .returnedBattlefieldEndStep cardId isLand
  | .returnedToBattlefield cardId isLand
  | .returnedToBattlefieldTapped cardId isLand
  | .enteredBattlefieldTapped cardId isLand =>
    match g.followMovedToZone? cardId (· == .battlefield) with
    | some entered =>
      let g :=
        match step with
        | .returnedBattlefieldEndStep .. =>
          match entered.attachedTo.bind g.findObject? with
          | some host =>
            g.logMsg s!"{entered.name} returns to the battlefield attached to {g.name host} (beginning of end step)"
          | none =>
            g.logMsg s!"{entered.name} returns to the battlefield (beginning of end step)"
        | .returnedToBattlefield .. =>
          match entered.attachedTo.bind g.findObject? with
          | some host =>
            g.logMsg s!"{entered.name} returns to the battlefield attached to {g.name host}"
          | none =>
            g.logMsg s!"{entered.name} returns to the battlefield"
        | .returnedToBattlefieldTapped .. =>
          g.logMsg s!"{entered.name} returns to the battlefield tapped"
        | .enteredBattlefieldTapped .. =>
          g.logMsg s!"{entered.name} enters the battlefield tapped"
        | _ => g
      if isLand then g.afterLandEnters entered else g.afterPermanentEnters entered
    | none => g
  | .empowerJaceExcessDamage controller targetId lethal startIdx =>
    let dealt := g.damageDealtToPermanentSince targetId startIdx
    let excess := dealt - lethal
    if excess > 0 then g.empowerJace controller excess else g
  | .searchBasicLandTapped p =>
    g.beginLibrarySearch p isBasicLandCard "a basic land card" (.battlefield true)
  | .fightTargetOpponentCreature controller sourceId targets =>
    g.withLegalKindPermanent controller .oppCreature targets (fun g tgt =>
      match sourceId.bind g.findObject? with
      | some src =>
        if src.isOnBattlefield && tgt.isOnBattlefield && g.isCreature src && g.isCreature tgt then
          g.fightCreatures src tgt
        else g.logMsg "The source is no longer in play"
      | none => g.logMsg "The source is no longer in play")
      sourceId (some "The target is no longer legal")
  | .enteredOfferAttachEquipment controller cardId =>
    match g.followMovedToZone? cardId (· == .battlefield) with
    | some entered =>
      let name := entered.name
      let g := g.afterPermanentEnters entered
      if g.pending != .none then g
      else if (g.permanentsOf controller).any (g.isEquipment ·) then
        g.change (.pending (.mayAttachEquipment controller entered.id))
          |>.logMsg s!"{(g.player controller).name} may attach an Equipment to {name}"
      else g
    | none => g
  | .putOntoBattlefieldHasteAtFour p cardId x shuffle =>
    let g :=
      match g.followMovedToZone? cardId (· == .battlefield) with
      | some entered =>
        let name := entered.name
        let g := g.afterPermanentEnters entered
        let g := if x >= 4 then g.grantUntilEotLogged (g.object! entered.id) Keyword.haste else g
        g.logMsg s!"{name} is put onto the battlefield"
      | none => g
    if shuffle then g.shuffleThen p .none else g
  | .revealPutCreaturesStep p remaining put enteredFromIds cause =>
    g.finishRevealPutCreaturesStep p remaining put enteredFromIds (cause := cause)
  | .shuffleThenGainLife p life =>
    (g.requestShuffle p (.gainLife p life)).continueIfShuffled
  | .offerCreaturesFromHandToBattlefield controller cause =>
    let creatures := (g.player controller).hand.filter (fun id => (g.findObject? id).any (g.isCreature ·))
    g.offerCardChoice controller creatures creatures.size .creaturesToBattlefield
      s!"{(g.player controller).name} may put any number of creature cards from their hand onto the battlefield"
      (cause := cause)
  | .enteredAttachedToSource attachmentId hostId =>
    match g.followMovedToZone? attachmentId (· == .battlefield) with
    | some entered =>
      let hostName := ((g.findObject? hostId).map g.name).getD "permanent"
      let g := g.logMsg s!"{g.name entered} enters the battlefield attached to {hostName}"
      g.afterPermanentEnters entered
    | none => g
  | .treasureThenDragonAfterCreate controller sourceId =>
    g.treasureThenDragonAfterCreate controller sourceId
  | .treasureThenDragonCreateDragon controller =>
    g.treasureThenDragonCreateDragon controller
  | .logAndEnterRecentTokens =>
    g.recentTokenIds.foldl (fun g tid =>
      match g.findObject? tid with
      | some entered =>
        if entered.isOnBattlefield then
          (g.logMsg s!"{entered.name} enters the battlefield").afterPermanentEnters entered
        else g
      | none => g) g
  | .dealDamageToEachOpponent p amount sourceId cause startEventIdx =>
    g.dealDamageToEachOpponent p amount (source := sourceId.bind g.damageSourceById?)
      (cause := cause) (startEventIdx := startEventIdx)
  | .noteExcessDamageDealt targetId lethal startIdx =>
    let dealt := g.damageDealtToPermanentSince targetId startIdx
    g.change (.excessDamageThisWay (dealt - lethal))
  | .notePermanentDealtDamage targetId startIdx =>
    let marked := (g.findObject? targetId).any (·.isOnBattlefield) && g.damageDealtToPermanentSince targetId startIdx > 0
    if marked then g.change (.permanentDealtDamageThisWay (some targetId)) else g
  | .logTwoNonlegendaryCopyTokens sourceId startEventIdx =>
    if !(g.tokensCreatedSince startEventIdx).isEmpty then
      let srcName :=
        match sourceId.bind g.findObject? with
        | some src => if src.isOnBattlefield then g.name src else src.name
        | none => ((sourceId.bind g.lastKnownBefore?).map (fun (eo : EventObject) => eo.name)).getD "source"
      g.logMsg s!"two nonlegendary tokens that are copies of {srcName} are created"
    else g
  | .discardCleanupIds p remainingIds justDiscarded =>
    let g :=
      match justDiscarded with
      | some (cid, owner) =>
        match g.followMovedToZone? cid (· == Zone.graveyard owner) with
        | some _ =>
          let name :=
            match g.findObject? cid with
            | some o => o.name
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
      g.beginFraChoice next (.mayWheel cards (restLiving.extract 1 restLiving.size) accepted)
        s!"{(g.player next).name} may discard their hand and draw {cards} cards"
    | none =>
      let acceptedLiving := accepted.filter g.stillInGame
      if acceptedLiving.isEmpty then g
      else
        let pairs := acceptedLiving.foldl (fun acc q =>
          acc ++ ((g.player q).hand.map (fun id => (q, id)))) #[]
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
    let g := g.draw p 1
    if let .chooseReplacement .. := g.pending then
      g.chainPendingReplacement (.finishPostStep (.addPlusOnesForLoggedDiscards p sourceId))
    else
      g.runPostStep (.addPlusOnesForLoggedDiscards p sourceId)
  | .queueTapAndStunReflexive p nonlandCount sourceId =>
    if nonlandCount == 0 then g
    else
      g.putReflexiveTrigger p sourceId
        { targeting := .of (.filtered TargetFilter.creature), maxTargets := nonlandCount
          allowsZeroTargets := true, resolution := .tapAndStunPerOpponent
          phrase := "Tap up to that many target creatures and put a stun counter on each of them" }
        (deferToPriority := true)
  | .nickFuryMayTransformOrBottom p cardId rest cause =>
    match g.followMovedToZone? cardId (· == .battlefield) with
    | some o =>
      if (g.baseCard o).otherFace.isSome && !g.cantTransform o then
        g.beginFraChoice p (.nickFuryMayTransform o.id rest)
          s!"{(g.player p).name} may transform {g.name o}"
      else g.putRestOnBottomRandom p rest (cause := cause)
    | none => g.putRestOnBottomRandom p rest (cause := cause)
  | .noteHandDiscardedCount count sourceId =>
    g.changes #[.handDiscardedThisWay (some count), .notedSourceThisWay sourceId]
  | .checkDrawThenOpponentsDraw p beforeDraws =>
    if g.loggedDraws p == beforeDraws then g
    else
      let (g, oppCause?) : Game × Option EventCause :=
        match g.currentResolvingContext? with
        | some (src, ctrl) =>
          let (g, c) := g.allocDelayedCause (ctrl.orElse (fun _ => some p)) src
          (g, some c)
        | none => (g, none)
      let opps := (g.livingOpponents p).map (·.id)
      g.runPostStep (.opponentsDrawOneLoop p opps oppCause?)
  | .opponentsDrawOneLoop drawer remainingOpponents cause =>
    match remainingOpponents[0]? with
    | none =>
      g.logMsg s!"{(g.player drawer).name} draws, so each opponent draws a card"
    | some opp =>
      let rest := remainingOpponents.extract 1 remainingOpponents.size
      let g := g.draw opp 1 (cause := cause)
      if let .chooseReplacement .. := g.pending then
        g.chainPendingReplacement (.finishPostStep (.opponentsDrawOneLoop drawer rest cause))
      else
        g.runPostStep (.opponentsDrawOneLoop drawer rest cause)
  | .loseLifeForMilledManaValue p tops cause =>
    let milled := tops.filterMap (fun id => g.followMilledPublic? id)
    let mv := milled.foldl (fun acc o => acc + g.objectManaValue o) 0
    g.loseLife p mv (cause := cause)
  | .eaglesReturnCreaturesLoop controller returnedCount sourceId remainingIds cause targeted pendingReturn =>
    g.eaglesReturnCreaturesLoop controller returnedCount sourceId remainingIds cause targeted pendingReturn
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
  | .finishPlusOneAfterDiscards =>
    g.finishPlusOneAfterDiscards
  | .closeDiscardBatchStep =>
    g.closeCurrentDiscardBatch
  | .logPutsIntoHand revealer fromId cardName =>
    if g.stillInGame revealer && (g.followMovedToZone? fromId (· == .hand revealer)).isSome then
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
  | .finishPalantirInfluence controller sourceId beforeInfluence targetOpponent =>
    let after := ((g.findObject? sourceId).map (·.status.influence)).getD beforeInfluence
    let g :=
      match g.findObject? sourceId with
      | some src =>
        if src.isOnBattlefield && after > beforeInfluence then
          g.logMsg s!"{g.name src} gets an influence counter"
        else g
      | none => g
    match targetOpponent with
    | some opp =>
      if after > beforeInfluence then
        g.change (.palantirChoiceReady (some (controller, opp, sourceId)))
      else g
    | none => g
  | .noteMilledIds tops =>
    let milled := tops.filterMap (fun id => (g.followMilledPublic? id).map (·.id))
    g.change (.milledIdsThisWay milled)
  | .noteOpponentsMilled opponents startIdx =>
    g.change (.opponentsMilledThisWay (g.anyOpponentMilledSince opponents startIdx))
  | .logCreatedTokensSummary controller startEventIdx =>
    g.logCreatedTokensSummary controller startEventIdx
  | .offerWorldsCreatures controller startIdx creatureIds sourceId =>
    let exiled := creatureIds.filterMap (fun id =>
      if g.wasPermanentExiled id startIdx then
        (g.followMovedToZone? id (· == .exile)).map (·.id)
      else none)
    let order := let apnap := g.apnapOrder; if apnap.isEmpty then #[controller] else apnap
    g.offerWorldsCreatures order.toList exiled #[] sourceId
  | .identityEchoAfterExile controller exiledId sourceId =>
    let oName := (g.lastKnownBefore? exiledId).map (·.name) |>.getD "The permanent"
    g.finishIdentityEchoAfterExile controller exiledId sourceId oName
  | .logShuffleIntoLibrary owner cardId =>
    let g :=
      if (g.followMovedToZone? cardId (· == .library owner)).isSome then
        let oName := (g.lastKnownBefore? cardId).map (·.name) |>.getD "it"
        g.logMsg s!"{(g.player owner).name} shuffles {oName} into their library"
      else g
    g.shuffleThen owner .none
  | .empowerJaceExiledCount controller startIdx creatureIds =>
    let count := creatureIds.foldl (fun acc id => if g.wasPermanentExiled id startIdx then acc + 1 else acc) 0
    g.empowerJace controller count
  | .reflexiveReturnLandTapped controller sourceId =>
    g.applyFra controller default .reflexiveReturnLandTapped #[] sourceId
  | .offerPutMilledPermanentOrGainLife controller preIds life =>
    let choices := preIds.filterMap (fun id =>
      match g.followMilledPublic? id with
      | some o => if g.isPermanentCard o then some o.id else none
      | none => none)
    if choices.isEmpty then g.gainLife controller life
    else
      g.beginFraChoice controller (.mayPutMilledPermanent choices life)
        s!"{(g.player controller).name} may put a permanent card milled this way into their hand"
  | .worldsWithinWorlds exiled chosen sourceId =>
    g.finishWorldsWithinWorlds exiled chosen sourceId
  | .millMayPutPermanentGainLife p tops life =>
    g.finishMillMayPutPermanentGainLife p tops life
  | .offerSearchBasicsExiledCount p startIdx attackerIds =>
    let count := attackerIds.foldl (fun acc id => if g.wasPermanentExiled id startIdx then acc + 1 else acc) 0
    g.offerMaySearchBasics p count
  | .enteredThenPutRestBottomRandom cardId libraryOwner rest cause =>
    let g :=
      match g.followMovedToZone? cardId (· == .battlefield) with
      | some entered =>
        (g.logMsg s!"{g.name entered} enters the battlefield").afterPermanentEnters entered
      | none => g
    g.putRestOnBottomRandom libraryOwner rest (cause := cause)
  | .createdTokenNote controller followup startEventIdx =>
    g.finishCreatedTokenNote controller followup startEventIdx
  | .noteExiledIds eligible =>
    let exiled := eligible.filterMap (fun id => (g.followMovedToZone? id (· == .exile)).map (·.id))
    g.change (.exiledIdsThisWay exiled)
  | .logReturnsToBattlefieldAndEnter cardId =>
    match g.followMovedToZone? cardId (· == .battlefield) with
    | some entered =>
      (g.logMsg s!"{entered.name} returns to the battlefield").afterPermanentEnters entered
    | none => g
  | .logPutUnderOwnerControlAndEnter cardId =>
    match g.followMovedToZone? cardId (· == .battlefield) with
    | some entered =>
      (g.logMsg s!"{entered.name} is put onto the battlefield under its owner's control").afterPermanentEnters entered
    | none => g
  | .returnNotedLandsStep remaining entered =>
    g.returnNotedLandsStep remaining entered
  | .putRestOnBottomRandom p rest cause =>
    g.putRestOnBottomRandom p rest (cause := cause)
  | .millSourceInfluenceCount controller sourceId =>
    if g.stillInGame controller then
      let n := ((g.damageSourceById? sourceId).map (·.status.influence)).getD 0
      g.mill controller n
    else g
  | .grantCantBeBlockedIfOnBattlefield cardId =>
    match g.findObject? cardId with
    | some cur =>
      if cur.isOnBattlefield then g.applyPermanentAction cur .cantBeBlocked else g
    | none => g
  | .logReturnsAsArtifactAndEnter cardId =>
    match g.followMovedToZone? cardId (· == .battlefield) with
    | some entered =>
      if entered.isOnBattlefield then
        (g.logMsg s!"{entered.name} returns as an artifact").afterPermanentEnters entered
      else g
    | none => g
  | .worldsWithinWorldsExileSelf sourceId =>
    g.finishWorldsWithinWorldsExileSelf sourceId
  | .notedLandsEntered entered =>
    g.finishNotedLandsEntered entered
  | .noteSacrificedSource ids =>
    let anySac := ids.any (fun id => !(g.findObject? id).any GameObject.isOnBattlefield)
    if anySac then g.change (.sourceWasSacrificed true) else g
  | .noteSacrificedPlan ids =>
    let anySac := ids.any (fun id => !(g.findObject? id).any GameObject.isOnBattlefield)
    if anySac then g.change (.planWasSacrificed true) else g
  | .continueOpeningBegin remainingIds =>
    g.continueOpeningBegin remainingIds
  | .worldsReturnExiledLoop remainingIds pendingCard =>
    g.worldsReturnExiledLoop remainingIds pendingCard
  | .logMovedToExile cardId =>
    match g.followMovedToZone? cardId (· == .exile) with
    | some moved => g.logMsg s!"{moved.name} is exiled"
    | none => g
  | .resumeChooseModeAfterLeave p =>
    match g.proposedSpell with
    | none => g
    | some prop =>
      match prop.kind with
      | .activatedAbility =>
        if prop.abilityModes.any (fun m => g.modeIsChoosable p m prop.sourceId) then
          g.change (.pending (.chooseMode p))
        else
          g.reverseProposedSpell (resumeContinuation := true)
      | .spell =>
        match g.findObject? prop.spellId with
        | none => g.reverseProposedSpell (resumeContinuation := true)
        | some spell =>
          let face := g.baseCard spell
          let effModes := effectiveSpellModes face
          let chosen := g.chosenModesOf spell
          let more := (List.range effModes.size).any (fun i =>
            !chosen.contains i && g.spellModeIsChoosable p effModes[i]! (some spell.id))
          if more then
            g.change (.pending (.chooseMode p))
          else if !chosen.isEmpty then
            g.afterModesChosen p
          else if isReturnUpToTwoGyModal face || face.allowsZeroTargets then
            g.change (.pending (.chooseMode p))
          else
            g.reverseProposedSpell (resumeContinuation := true)
      | .turnFaceUp => g
  | .resumeChooseTargetsAfterLeave p =>
    match g.objectAwaitingTargets with
    | none =>
      if g.proposedSpell.isSome then g.reverseProposedSpell (resumeContinuation := true)
      else g.afterTriggerTargetsChosen
    | some obj =>
      let hasLegal := !(g.legalProposedTargets p obj).isEmpty
      let allowZero :=
        match obj.triggeredAbility with
        | some ab => ab.allowsZeroTargets
        | none =>
          match g.currentSpellEffect obj with
          | some e => e.allowsZeroTargets
          | none => obj.abilityEffect.any (·.allowsZeroTargets)
      let canDeclineOrPick :=
        hasLegal || g.canSkipCurrentOptionalSlot obj || g.canFinishOptionalTargets obj || allowZero
      if canDeclineOrPick then
        g.change (.pending (.chooseTargets p))
      else if g.proposedSpell.isSome then
        g.reverseProposedSpell (resumeContinuation := true)
          (extraLog := some s!"{obj.name} has no legal target and can't be cast")
      else
        let g := g.ceaseToExist obj.id (cause := some (.gameRule .triggeredAbility))
          |>.logMsg s!"{obj.name}'s triggered ability has no legal target and is removed from the stack (CR 603.3d)"
        g.afterTriggerTargetsChosen
  | .resumeTriggerModesAfterLeave p objectId remaining chosen =>
    match g.findObject? objectId with
    | some obj =>
      if obj.zone != .stack then g.finishFraChoice
      else
        let tModes := g.triggerModesOf obj
        let choosableLeft :=
          ((List.range tModes.size).filter (fun i =>
            !chosen.contains i && (tModes[i]?.any (g.triggerModeChoosable p obj)))).length
        if choosableLeft < remaining then
          (g.ceaseToExist obj.id (cause := some (.gameRule .noLegalMode))
            |>.logMsg s!"{obj.name}'s triggered ability has too few legal modes and is removed from the stack (CR 603.3c)").finishFraChoice
        else
          g.change (.pending (.fraChoice p (.triggerModes obj.id remaining chosen)))
    | none => g.finishFraChoice
  | .grantLifelinkUntilEot cardId cause =>
    match g.findObject? cardId with
    | some cur =>
      if cur.isOnBattlefield then
        let g := g.createEffect (.keywordsUntilEot cur.id Keyword.lifelink) (cause := cause)
        g.logMsg s!"{g.name cur} gains lifelink until end of turn"
      else g
    | none => g
  | .grantHasteUntilEotSilent cardId cause =>
    match g.findObject? cardId with
    | some cur =>
      if cur.isOnBattlefield then
        g.createEffect (.keywordsUntilEot cur.id Keyword.haste) (cause := cause)
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
  | .beginStepAfterPhaseBegan st =>
    g.beginStepAfterPhaseBegan st
  | .beginStepBody st =>
    g.beginStepBody st
  | .tapAndStunTargetsLoop controller remaining sourceId cause =>
    let kind :=
      (g.resolvingSpell.bind g.findObject? |>.bind g.currentSpellEffect |>.map (·.targetKind)).orElse
        (fun _ =>
          g.resolvingAbility.bind g.findObject? |>.bind fun o =>
            (o.abilityEffect.map (·.targetKind)).orElse (fun _ => o.triggeredAbility.map (·.targetKind)))
        |>.getD .creature
    g.tapAndStunTargetsLoop controller kind remaining sourceId cause
  | .exileZemoBoastCards p abilityId remainingIds =>
    g.exileZemoBoastCards p abilityId remainingIds
  | .grantAdventureExilePermission controller cardId cause =>
    match g.followMovedToZone? cardId (· == .exile) with
    | some o =>
      (g.createEffect (.playPermission o.id { player := controller, fromAdventure := true }) (cause := cause))
        |>.logMsg s!"{o.name} is exiled. {(g.player controller).name} may cast it for as long as it remains exiled (CR 715.3d)"
    | none => g
  | .exileSearchedLinkedLoop p remainingIds sourceId cause pendingFromId =>
    g.exileSearchedLinkedLoop p remainingIds sourceId cause pendingFromId
  | .grantPlayUntilEndOfNextTurn p cardId cause =>
    match g.followMovedToZone? cardId (· == .exile) with
    | some moved =>
      (g.createEffect (.playPermission moved.id { player := p } (turnEnds := 2)) (cause := cause))
        |>.logMsg s!"{(g.player p).name} exiles {moved.name} and may play it until the end of their next turn"
    | none => g
  | .exileCreaturesFromGraveyardLoop controller remainingIds cause pendingFromId =>
    g.exileCreaturesFromGraveyardLoop controller remainingIds cause pendingFromId
  | .finishExileUntilSourceLeaves sourceId fromId =>
    g.finishExileUntilSourceLeaves sourceId fromId
  | .finishExileForLeaveTrigger sourceId fromId =>
    g.finishExileForLeaveTrigger sourceId fromId
  | .exileTopForPlayLoop fromPlayer caster remaining mayCastStyle cause pendingFromId =>
    g.exileTopForPlayLoop fromPlayer caster remaining mayCastStyle cause pendingFromId
  | .exileTopMayCastUpToLoop fromPlayer caster remaining casts cause exiled pendingFromId =>
    g.exileTopMayCastUpToLoop fromPlayer caster remaining casts cause exiled pendingFromId
  | .offerMayCastUpToFromExile caster preIds casts =>
    let arrived := preIds.filterMap (fun pid => (g.followMovedToZone? pid (· == Zone.exile)).map GameObject.id)
    g.finishExileTopMayCastUpToOffer caster arrived casts
  | .finishExileUntilNextEndStep controller fromId cause =>
    g.finishExileUntilNextEndStep controller fromId cause
  | .finishFraExileUntilSourceLeaves sourceId fromId =>
    g.finishFraExileUntilSourceLeaves sourceId fromId
  | .uldarosCopiesLoop controller sourceId remainingIds cause pendingFromId =>
    g.uldarosCopiesLoop controller sourceId remainingIds cause pendingFromId
  | .finishUldarosCopiesOffer controller cause =>
    g.finishUldarosCopiesOffer controller cause
  | .finishExileTopMayCastElseDamage controller fromId damage sourceId =>
    g.finishExileTopMayCastElseDamage controller fromId damage sourceId
  | .exileHandDrawLoop p remainingIds cause pendingFromId =>
    g.exileHandDrawLoop p remainingIds cause pendingFromId
  | .finishExileHandDrawPlayUntilNext p drawCount cause =>
    g.finishExileHandDrawPlayUntilNext p drawCount cause
  | .exileTopXOppPlayForLifeLoop controller fromPlayer remaining cause pendingFromId =>
    g.exileTopXOppPlayForLifeLoop controller fromPlayer remaining cause pendingFromId
  | .exileIdsUntilSourceLeavesLoop sourceId remainingIds cause =>
    g.exileIdsUntilSourceLeavesLoop sourceId remainingIds cause
  | .exileThenReturnNextEndLoop controller sourceId remainingIds cause justMovedFrom wasNontoken movedName =>
    g.exileThenReturnNextEndLoop controller sourceId remainingIds cause justMovedFrom wasNontoken movedName
  | .finishDaredevilExile sourceId cardId =>
    g.finishDaredevilExile sourceId cardId
  | .notePlayExiledThisWay cardId =>
    match g.followMovedToZone? cardId (· == .exile) with
    | some moved => g.change (.playExiledThisWay (some moved.id))
    | none => g
  | .triggerExileLoop controller sourceId mode remainingIds accMovedPreIds cause justMovedFrom matchedPreMove movedName =>
    g.runTriggerExileLoop controller sourceId mode remainingIds accMovedPreIds cause justMovedFrom matchedPreMove movedName
  | .logDiscardedCount p preDiscards =>
    let discarded := g.loggedDiscards p - preDiscards
    g.logMsg s!"{(g.player p).name} discards {discarded} card(s)"
  | .loyaltyOnPlaneswalkersLoop p remainingIds =>
    g.loyaltyOnPwsLoop p remainingIds
  | .honeControlledEquipmentLoop controller remainingIds =>
    if let .chooseReplacement .. := g.pending then
      g.chainPendingReplacement (.finishPostStep (.honeControlledEquipmentLoop controller remainingIds))
    else Id.run do
      let mut g := g
      for i in [0:remainingIds.size] do
        let id := remainingIds[i]!
        if let some eq := g.findObject? id then
          if eq.isOnBattlefield && g.isEquipment eq then
            g := g.putCountersDeferredLog eq.id .hone 1 (some controller) .received
            if let .chooseReplacement .. := g.pending then
              let rem := remainingIds.extract (i + 1) remainingIds.size
              if !rem.isEmpty then
                g := g.chainPendingReplacement (.finishPostStep (.honeControlledEquipmentLoop controller rem))
              return g
      return g
  | .putDoubleStrikeCounter targetId byPlayer =>
    g.putCountersDeferredLog targetId .doubleStrike 1 byPlayer .gets
  | .logGiftTreasureGiven recipient =>
    if g.stillInGame recipient then g.logMsg s!"{(g.player recipient).name} is given a Treasure (gift)" else g
  | .logDelayedBirdSoldiersCreated controller startEventIdx =>
    if g.stillInGame controller then
      let cnt := (g.tokensCreatedSince startEventIdx).size
      g.logMsg s!"{(g.player controller).name}'s delayed triggered ability creates {cnt} Bird Soldier token(s)"
    else g
  | .copyMissingKeywordsStep srcIds otherId startKw =>
    g.copyMissingKeywordsStep srcIds otherId startKw
  | .exileLibraryUntilNonlandLoop pid controller sourceId cause pendingFromId =>
    g.exileLibraryUntilNonlandLoop pid controller sourceId cause pendingFromId
  | .resolveCascadeLoop p maxMv cause exiled pendingFromId =>
    g.resolveCascadeLoop p maxMv cause exiled pendingFromId
  | .exileUntilInstantOrSorceryLoop victim mode cause others pendingFromId =>
    g.exileUntilInstantOrSorceryLoop victim mode cause others pendingFromId
  | .finishGrimaDirectCast controller victim fromId others cause =>
    g.finishGrimaDirectCast controller victim fromId others cause
  | .sarumanExileCopyMayCast controller fromId cause =>
    g.finishSarumanExileCopyMayCast controller fromId cause
  | .exileReturnBrieflyAfterExile controller fromId cardName returnable sourceId cause =>
    g.finishExileReturnBrieflyAfterExile controller fromId cardName returnable sourceId cause
  | .exileFlickerAfterExile controller fromId cardName sourceId cause =>
    g.finishExileFlickerAfterExile controller fromId cardName sourceId cause
  | .exileFromRevealedHandAfterMove p victim fromId cardName sourceId =>
    match g.followMovedToZone? fromId (· == .exile) with
    | some ex =>
      let g := g.changeObject ex.id (.exiledBy sourceId)
      g.logMsg s!"{(g.player p).name} exiles {cardName} from {(g.player victim).name}'s hand"
    | none => g
  | .evilsThrallGrantHaste targetId =>
    match g.findObject? targetId with
    | some o => if o.isOnBattlefield then g.grantUntilEotLogged o Keyword.haste else g
    | none => g
  | .noteReturnedPermanentIfInHand fromIds =>
    if fromIds.any (fun fid => (g.followMovedToZone? fid (fun | .hand _ => true | _ => false)).isSome) then
      g.change (.returnedPermanentThisWay true)
    else g
  | .logExiledIfInExile fromId msg =>
    if (g.followMovedToZone? fromId (· == .exile)).isSome then g.logMsg msg else g
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
  | .logDealDamageEachOpposingCreature amount =>
    g.logMsg s!"deals {amount} damage to each opposing creature"
  | .finishZemoBoastExileLogs p sourceId preIds =>
    let exiledCount := (preIds.filter (fun id => (g.followMovedToZone? id (· == .exile)).isSome)).size
    let g :=
      if exiledCount > 0 then
        g.logMsg s!"{(g.player p).name} exiles {exiledCount} card(s) from their graveyard"
      else g
    match g.findObject? sourceId with
    | some src => g.logMsg s!"{src.name}'s boast ability is activated"
    | none => g
  | .plusOneOnCreatedTokensLoop controller remainingIds amount =>
    g.plusOneOnCreatedTokensLoop controller remainingIds amount
  | .moveIdsInOrderLoop ids dest log cause placedCount prevLibraryMoved =>
    g.moveIdsInOrderLoop ids dest log cause placedCount prevLibraryMoved
  | .createMerfolkForBlueSymbols controller lastKnownPower =>
    g.createMerfolkForBlueSymbols controller lastKnownPower
  | .incrementPlanSource controller sourceId =>
    g.incrementPlanSource controller sourceId
  | .millOpponentsOnly opponents n cause =>
    g.millOpponentsOnly opponents n cause
  | .millOpponentsAndNote opponents allPids n cause =>
    g.millOpponentsAndNote opponents allPids n cause
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
  | .copyNontokenCreaturesAfterEnter startEventIdx =>
    g.finishCopyNontokenCreaturesAfterEnter startEventIdx
  | .countersOnCreatureTargetsLoop controller remaining kind n sourceId =>
    g.countersOnCreatureTargetsLoop controller remaining kind n sourceId
  | .targetPlayersGainLifeLoop controller remaining n sourceId cause =>
    g.targetPlayersGainLifeLoop controller remaining n sourceId cause
  | .twoPlayersDrawSecond controller second sourceId cause =>
    g.twoPlayersDrawSecond controller second sourceId cause
  | .twoPlayersEachDrawSecond second cards cause =>
    g.draw second cards (cause := cause)
  | .bounceEachTargetLoop controller kind remaining sourceId =>
    g.bounceEachTargetLoop controller kind remaining sourceId
  | .untapTargetsLoop controller kind remaining sourceId =>
    g.untapTargetsLoop controller kind remaining sourceId
  | .damageUpToOneAndPlayerLoop controller kind remaining n srcName sourceId cause =>
    g.damageUpToOneAndPlayerLoop controller kind remaining n srcName sourceId cause
  | .plusOneOnEachTargetLoop controller kind remaining n sourceId =>
    g.plusOneOnEachTargetLoop controller kind remaining n sourceId
  | .minusOnesPerOpponentLoop controller kind remaining x sourceId =>
    g.minusOnesPerOpponentLoop controller kind remaining x sourceId
  | .divideSevenDamageLoop controller kind remaining division sourceId startEventIdx =>
    g.divideSevenDamageLoop controller kind remaining division sourceId startEventIdx
  | .returnInstantsLoop controller kind remaining sourceId =>
    g.returnInstantsLoop controller kind remaining sourceId
  | .putPlusOnesUpToLastKnownLoop controller remaining sourceId =>
    g.putPlusOnesUpToLastKnownLoop controller remaining sourceId
  | .attachEquipmentToHostLoop controller kind hostId remaining sourceId =>
    g.attachEquipmentToHostLoop controller kind hostId remaining sourceId
  | .copyTokenOfSourceAfterCreate controller cardName startEventIdx =>
    g.copyTokenOfSourceAfterCreate controller cardName startEventIdx
  | .fblthpMoveToHandLoop controller remainingIds cause =>
    g.fblthpMoveToHandLoop controller remainingIds cause
  | .fblthpShuffleAfterHand controller =>
    g.shuffleThen controller .none
  | .putSourceCountersPlusOneAndLog targetId plusOnes byPlayer hadOtherCounters beforeTotal =>
    let totalCounters (s : Status) : Nat :=
      s.toCounterBag.foldl (fun acc (_, c) => acc + c) 0
    match g.findObject? targetId with
    | none => g
    | some cur =>
      let otherPlaced := hadOtherCounters || totalCounters cur.status > beforeTotal
      if plusOnes > 0 then
        let beforeNext := totalCounters cur.status
        let g := g.addPlusOnePlusOneTo cur plusOnes (byPlayer := byPlayer)
        if let .chooseReplacement .. := g.pending then
          g.chainPendingReplacement
            (.finishPostStep (.putSourceCountersPlusOneAndLog cur.id 0 byPlayer otherPlaced beforeNext))
        else
          match g.findObject? cur.id with
          | some cur2 =>
            if otherPlaced || totalCounters cur2.status > beforeNext then
              g.logMsg s!"The counters are put on {g.name cur2}"
            else g
          | none => g
      else if otherPlaced then
        g.logMsg s!"The counters are put on {g.name cur}"
      else g
  | .logInvestigateClueCreated controller startEventIdx =>
    if !(g.tokensCreatedSince startEventIdx).isEmpty then
      g.logMsg s!"{(g.player controller).name} investigates"
    else g
  | .revealUntilCreatureToHandAfterMove controller cardId cardName rest cause =>
    let g :=
      if (g.followMovedToZone? cardId (· == .hand controller)).isSome then
        g.logMsg s!"{cardName} is put into {(g.player controller).name}'s hand"
      else g
    g.putRestOnBottomRandom controller rest (cause := some cause)
  | .logSacrificedIfInGraveyard cardId owner cardName =>
    if (g.followMovedToZone? cardId (· == .graveyard owner)).isSome then
      g.logMsg s!"{cardName} is sacrificed"
    else g
  | .movePublicCardsToHandLoop p remainingIds maxLeft playerPutsStyle cause pendingCard requirePublicZone =>
    g.movePublicCardsToHandLoop p remainingIds maxLeft playerPutsStyle cause pendingCard requirePublicZone
  | .exileOpponentLibrariesLoop remainingOpps curOpp curIds movedAnyForCur pendingId =>
    g.exileOpponentLibrariesLoop remainingOpps curOpp curIds movedAnyForCur pendingId
  | .worldsWithinWorldsAfterPut exiled validChosen sourceId =>
    g.finishWorldsWithinWorldsAfterPut exiled validChosen sourceId
  | .logDiscardIfInGraveyard cardId owner msg =>
    if (g.followMovedToZone? cardId (· == .graveyard owner)).isSome then g.logMsg msg else g
  | .chooseCardsToHandLoop p remainingIds cause pendingCard =>
    g.chooseCardsToHandLoop p remainingIds cause pendingCard
  | .logIfCountersIncreased targetId before msg =>
    g.logIfCountersIncreased targetId before msg

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
      let nextPending := Pending.fraChoice prop.caster (.costPicks sid picks paid)
      return (g.change (.consecutivePasses 0)).chainPendingReplacement
        (.restorePending nextPending
          (promptLog := some s!"{(g.player prop.caster).name} chooses how to {pick.phrase}"))
    else if (g.costPickCandidates prop.caster (some sid) pick).size < pick.count then
      g.reverseProposedSpell? (resumeContinuation := true)
    else
      let g := g.changes #[.pending (.fraChoice prop.caster (.costPicks sid picks paid)), .consecutivePasses 0]
      return g.logMsg s!"{(g.player prop.caster).name} chooses how to {pick.phrase}"
  | _, _ =>
    if let .chooseReplacement .. := g.pending then
      return (g.change (.consecutivePasses 0)).chainPendingReplacement
        (.completeActivation hadOuterReplacement openCont)
    else
      match g.completeActivation prop
          (hadOuterReplacement := hadOuterReplacement)
          (hadOpenContinuation := some openCont) with
      | .ok g' => return g'
      | .error _ => g.reverseProposedSpell? (resumeContinuation := true)

/-- Clear the finished scry or surveil, draw any follow-up cards, and offer
Palantír's opponent their choice without draining outer continuations or
granting priority. -/
partial def finishLibraryLookCore (g : Game) : Game :=
  if let .chooseReplacement .. := g.pending then
    g.chainPendingReplacement .finishLibraryLook
  else
    let g := g.changes #[
      .pending .none,
      .surveilReturnMvAtMost none,
      .surveilReturnNoncreatureNonland false ]
    let g :=
      match g.fraAfterLook with
      | some (c, src, next) =>
        (g.change (.fraAfterLook none)).applyFra c default next.toResolution #[] src
      | none => g
    if let .chooseReplacement .. := g.pending then
      g.chainPendingReplacement .finishLibraryLook
    else
      let g :=
        match g.pendingDrawAfterScry with
        | some (q, n) =>
          let g := g.change (.pendingDrawAfterScry none)
          g.draw q n
        | none => g
      if let .chooseReplacement .. := g.pending then
        g.chainPendingReplacement .finishLibraryLook
      else if g.pending != .none then g
      else
        match g.palantirAfterScry with
        | some (controller, opp, sid) =>
          (g.change (.palantirAfterScry none)).offerPalantirChoice controller opp sid
        | none => g

/-- Clear the finished scry or surveil, draw any follow-up cards, offer
Palantír's opponent their choice, and give the active player priority. -/
partial def finishLibraryLook (g : Game) : Game :=
  g.finishLibraryLookCore.finishAndGrantPriority

/-- Move remaining surveil graveyard cards sequentially, chaining
`finishSurveilPostMove` whenever a move pauses on `Pending.chooseReplacement`. -/
partial def surveilMoveLoop (g : Game) (p : PlayerId) (remainingGy : Array ObjectId)
    (cause : Option EventCause) : Game :=
  match remainingGy[0]? with
  | none => g
  | some id =>
    let rest := remainingGy.extract 1 remainingGy.size
    let card := g.object! id
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
    let g := g.logMsg s!"{(g.player p).name} puts {card.name} into their graveyard (surveil)"
    let returnToHand : Bool :=
      match g.surveilReturnMvAtMost with
      | some n => g.objectManaValue card ≤ n
      | none => g.surveilReturnNoncreatureNonland && !g.isCreature card && !g.isLand card
    if returnToHand then
      let (g', _) := g.move gyObj.id (.hand p) none (cause := cause)
      if let .chooseReplacement .. := g'.pending then
        g'.chainPendingReplacement (.finishPostStep (.finishSurveilHandMove p gyObj.id card.name remainingGy cause))
      else
        let g' :=
          if (g'.followMovedToZone? gyObj.id (· == .hand p)).isSome then
            g'.logMsg s!"{(g'.player p).name} puts {card.name} into their hand"
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
        let oName := ((g.findObject? targetId).map (·.name)).getD "permanent"
        let g := g.logMsg s!"{(g.player p).name} proliferates {oName}"
        g.finishProliferateLoop p remainingTargets (permIds.push targetId) playerIds
          chosenEmpty remainingRounds cause
    else
      let oName := ((g.findObject? targetId).map (·.name)).getD "permanent"
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
  if g.mayThenDrop > 0 then
    g.acceptMayThenCore
  else
    g.draw p n

/-- Finish the post-discard steps of `.chooseDiscardCard`. -/
partial def finishChooseDiscardCard (g : Game) (p : PlayerId) (card : GameObject)
    (remaining : Array PlayerId) : Game :=
  let g : Game :=
    match g.triggerSequenceRest with
    | some rest =>
      if rest.steps.any (· == .put .discardedLand (how := .tapped)) then
        match g.followMovedToZone? card.id (fun
          | .graveyard _ | .exile | .battlefield | .stack | .command => true
          | _ => false) with
        | some moved => g.change (.discardedCardThisWay (some (p, moved.id)))
        | none => g
      else g
    | none => g
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

/-- Pay a deferred additional-cost behold (`additionalCostBeholdOrPay`) at CR
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
        (g.findObject? id).any (fun card => g.hasSubtype card quality))
    let some chosenId := chosenPerm?.orElse (fun _ => chosenHand?)
      | throw s!"{(g.player prop.caster).name} can no longer behold a {quality}"
    let cause := EventCause.costPayment .behold prop.caster (some prop.spellId)
    g.withProposalActionM .costAction fun g => do
      let g := g.record (GameEvent.announced g.turnNumber prop.spellId
        (costs := #[.behold chosenId]) (cause := some cause))
      return g.beholdQuality prop.caster quality (cause := some cause)

/-- Reverse a proposed spell or activated ability to its pre-proposal checkpoint,
preserving CR 733.1 irreversible library actions, running any deferred post-cast
cleanup, and resuming an active continuation via `finishFraChoice` when
`resumeContinuation == true` (CR 601.2 / 602.2 / 733.1–733.2). -/
partial def reverseProposedSpell? (g : Game) (resumeContinuation : Bool := false)
    (extraLog : Option String := none) : Except String Game := do
  let (g, needsFinish) ← g.reverseProposedSpellCore?
    (resumeContinuation := resumeContinuation) (extraLog := extraLog)
  return if needsFinish then g.finishFraChoice else g

/-- Non-monadic wrapper around `reverseProposedSpell?`. -/
partial def reverseProposedSpell (g : Game) (resumeContinuation : Bool := false)
    (extraLog : Option String := none) : Game :=
  match g.reverseProposedSpell? (resumeContinuation := resumeContinuation) (extraLog := extraLog) with
  | .ok g' => g'
  | .error msg => g.logMsg msg

/-- Execute the sequential non-mana spell cost stages (`ProposedSpellCostStage`:
`.teamwork` → `.behold` → `.sneak` → `.finalize`), pausing across
`Pending.chooseReplacement` and preserving any enclosing `pendingReplacement`
continuation without shadowing or duplicating it (CR 601.2h / 616.1 / 733.1). -/
partial def finishProposedSpellCosts (g : Game) (stage : ProposedSpellCostStage)
    (grantPriority hadOuterReplacement openCont : Bool) : Except String Game := do
  let some prop := g.proposedSpell | return g
  if let .chooseReplacement .. := g.pending then
    return (g.change (.consecutivePasses 0)).chainPendingReplacement
      (.finishProposedSpellCosts stage grantPriority hadOuterReplacement openCont)
  let localOuter? := g.pendingReplacement
  let hadOuter := hadOuterReplacement || localOuter?.isSome
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
            | some outer => g.chainPendingReplacement outer.ensureEndsWithFinishFra
            | none => g
        else
          let g := match localOuter? with
            | some outer => g.chainPendingReplacement outer
            | none => g
          g.finishProposedSpellCosts .behold grantPriority hadOuterReplacement openCont
      | .error _ =>
        g.reverseProposedSpell? (resumeContinuation := true)
    else
      g.finishProposedSpellCosts .behold grantPriority hadOuterReplacement openCont
  | .behold =>
    if prop.needsBehold.isSome then
      match g0.payBeholdForProposed prop with
      | .ok g =>
        if let .chooseReplacement .. := g.pending then
          let g := g.chainPendingReplacement
            (.finishProposedSpellCosts .sneak grantPriority hadOuter openCont)
          return match localOuter? with
            | some outer => g.chainPendingReplacement outer.ensureEndsWithFinishFra
            | none => g
        else
          let g := match localOuter? with
            | some outer => g.chainPendingReplacement outer
            | none => g
          g.finishProposedSpellCosts .sneak grantPriority hadOuterReplacement openCont
      | .error _ =>
        g.reverseProposedSpell? (resumeContinuation := true)
    else
      g.finishProposedSpellCosts .sneak grantPriority hadOuterReplacement openCont
  | .sneak =>
    match prop.sneakAttacker with
    | some a =>
      match g0.withProposalActionM .costAction (fun g => g.paySneak prop.caster prop.spellId a) with
      | .ok g =>
        if let .chooseReplacement .. := g.pending then
          let g := g.chainPendingReplacement
            (.finishProposedSpellCosts .finalize grantPriority hadOuter openCont)
          return match localOuter? with
            | some outer => g.chainPendingReplacement outer.ensureEndsWithFinishFra
            | none => g
        else
          let g := match localOuter? with
            | some outer => g.chainPendingReplacement outer
            | none => g
          g.finishProposedSpellCosts .finalize grantPriority hadOuterReplacement openCont
      | .error _ =>
        g.reverseProposedSpell? (resumeContinuation := true)
    | none =>
      g.finishProposedSpellCosts .finalize grantPriority hadOuterReplacement openCont
  | .finalize =>
    if prop.needsSacrificeOther then
      let excludeId := prop.sourceId.getD prop.spellId
      if (g0.sacrificeCreatureOrArtifactChoices prop.caster excludeId).isEmpty then
        return (← g.reverseProposedSpell? (resumeContinuation := true))
      let g := match localOuter? with
        | some outer => g0.chainPendingReplacement outer
        | none => g0
      let g := g.changes #[.pending (.sacrificePermanent prop.caster excludeId), .consecutivePasses 0]
      return g.logMsg s!"{(g.player prop.caster).name} must sacrifice an artifact or creature"
    else if prop.needsDiscardCard then
      if (g0.player prop.caster).hand.isEmpty then
        return (← g.reverseProposedSpell? (resumeContinuation := true))
      let g := match localOuter? with
        | some outer => g0.chainPendingReplacement outer
        | none => g0
      let g := g.changes #[.pending (.discardForAdditionalCost prop.caster), .consecutivePasses 0]
      return g.logMsg s!"{(g.player prop.caster).name} must discard a card"
    else
      let isResCast := prop.resolutionCast
      let g := g0.changes #[.pending .none, .proposedSpell none, .consecutivePasses 0]
      let g := g.becomeCast prop.caster (g.object! prop.spellId)
        (grantPriority := grantPriority)
        (hadOuterReplacement := hadOuter)
        (hadOpenContinuation := some openCont)
      let paused := match g.pending with | .chooseReplacement .. => true | _ => false
      if paused then
        let g :=
          match localOuter? with
          | some outer => g.chainPendingReplacement outer.ensureEndsWithFinishFra
          | none =>
            if isResCast && !hadOuterReplacement then
              g.chainPendingReplacement .finishFraChoice
            else g
        return g
      else
        let g :=
          match localOuter? with
          | some outer => g.chainPendingReplacement outer.ensureEndsWithFinishFra
          | none => g
        if hadOuterReplacement then
          return g
        else if isResCast then
          if (match g.pending with | .chooseReplacement .. => true | _ => false) &&
              g.pendingReplacement.any (·.endsWithFinishFra) then
            return g
          else
            return g.finishFraChoice
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
  let hasMorphChoice :=
    !prop.kickerAnnounced && !prop.alternativeCost && face.morph.isSome &&
      face.kicker.isNone && (prop.origPerm.bind (·.prepareSource)).isNone &&
      prop.original.zone != .graveyard prop.original.owner
  let needsKicker :=
    !prop.kickerAnnounced &&
      (face.kicker.isSome || (!prop.alternativeCost && (face.morph.isSome || face.impending.isSome)))
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
  else if face.giftTreasure && !prop.giftAnnounced then
    g.change (.pending (.chooseGift p))
      |>.logMsg s!"{(g.player p).name} may promise a gift (CR 702.174)"
  else if face.teamwork.isSome && !prop.teamworkAnnounced then
    g.change (.pending (.chooseTeamwork p))
      |>.logMsg s!"{(g.player p).name} may pay a teamwork cost (CR 702.194)"
  else if g.proposedNeedsTarget prop then
    -- CR 601.2c / 702.33d,g: check the targeting of the spell as proposed (kicked or not).
    let zeroOk := face.allowsZeroTargets ||
      (g.currentSpellEffect spell).any (·.allowsZeroTargets)
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
        | some outer => g1.chainPendingReplacement outer.ensureEndsWithFinishFra
        | none => g1
      else
        match g1.payBeholdForProposed prop with
        | .error _ => g.reverseProposedSpell (resumeContinuation := true)
        | .ok g =>
          let pausedPreCast := match g.pending with | .chooseReplacement .. => true | _ => false
          let clearPending : Array EngineChange := if pausedPreCast then #[] else #[.pending .none]
          let g := g.changes (clearPending ++ #[.proposedSpell none])
          let g := g.becomeCast p (g.object! prop.spellId) (grantPriority := false)
            (hadOuterReplacement := outerCont?.isSome)
            (hadOpenContinuation := some openCont)
          let isFraPrompt := match g.pending with | .fraChoice .. => true | _ => false
          if g.pending != .none || g.afterRandom != .none then
            match outerCont? with
            | some outer =>
              if isFraPrompt then g.chainPendingReplacement outer
              else g.chainPendingReplacement outer.ensureEndsWithFinishFra
            | none =>
              if openCont && !isFraPrompt && !g.pendingReplacement.any (·.endsWithFinishFra) then
                g.chainPendingReplacement .finishFraChoice
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
    let face := g.baseCard o
    let rawPerm := if withoutManaCost then none else g.playPermission o
    let canMorph :=
      !withoutManaCost && face.morph.isSome && face.kicker.isNone &&
        o.zone != .graveyard o.owner &&
        !(rawPerm.any (fun pm => pm.withoutManaCost || pm.payLifeEqualManaValue)) &&
        !g.spellNameForbidden ""
    if g.cantCastSpellsThisTurn p then
      (clearCkpt g).logMsg "You can't cast spells this turn (CR 101.2)"
    else if g.splitSecondOnStack then
      (clearCkpt g).logMsg s!"{o.name} can't be cast while a spell with split second is on the stack (ruling 839)"
    else if g.combatLocksNonManaAbilities then
      (clearCkpt g).logMsg "During combat, players can't cast spells (Yuriko, Blade of the Mighty)"
    else if g.opponentsCantCastOnActiveTurn p then
      (clearCkpt g).logMsg "Opponents can't cast spells during that player's turn"
    else if !canMorph && g.spellNameForbidden face.name then
      (clearCkpt g).logMsg s!"Spells named {face.name} can't be cast"
    else if !canMorph && !g.graveyardCastThresholdMet p o.id face then
      (clearCkpt g).logMsg s!"{face.name} cannot be cast right now"
    else if !ignoreTiming && !g.timingAllowsCast p (if canMorph then morphSpellFace else face) then
      (clearCkpt g).logMsg s!"{o.name} cannot be cast now (timing)"
    else if !withoutManaCost && rawPerm.any (·.payLifeEqualManaValue) &&
        !g.canPayLife p (g.objectManaValue o) then
      (clearCkpt g).logMsg s!"{(g.player p).name} can't pay {g.objectManaValue o} life to cast {o.name} (CR 119.4)"
    else
      let name := o.name
      let original := o
      let origSnap := g.snapshot o
      let fromGy := original.zone == .graveyard original.owner
      let isFreeFromGy := !withoutManaCost && fromGy && g.freeCastFromGraveyard original
      let origPerm : Option PlayPermission :=
        if withoutManaCost then some { player := p, withoutManaCost := true }
        else rawPerm
      let altCostUsed :=
        withoutManaCost || isFreeFromGy ||
          origPerm.any (fun pm => pm.withoutManaCost || pm.payLifeEqualManaValue)
      let wasCopy := original.isCopy
      let g :=
        if callerCheckpoint && g.proposalCheckpoint.isSome then g
        else g.change .saveProposalCheckpoint
      let (g, newId) := g.move id .stack (some p) (verb := some .cast) (actor := some p)
        (isCopy := some wasCopy)
      let g :=
        if exileInstantSorceryInstead && fromGy then
          g.createEffect (.exileInstantSorceryInstead newId)
        else g
      let spellObj := g.object! newId
      let stackFace := g.baseCard spellObj
      let g := g.putStackEntry p newId
      let way : CastWay :=
        if withoutManaCost then .alternative "withoutManaCost"
        else if isFreeFromGy || origPerm.isSome then .alternative "permission"
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
        (isFreeFromGy := some isFreeFromGy) (flashback := some false)
        (explicitAltCost := altCostUsed)
      let lifeInstead :=
        if !withoutManaCost && origPerm.any (·.payLifeEqualManaValue) then
          g.objectManaValue spellObj
        else 0
      let needsSacrifice :=
        stackFace.additionalCostSacrificeCreature ||
          (stackFace.additionalCostSacrificeArtifactOrCreature && stackFace.additionalCostOrPayGeneric.isNone)
      g.beginResolutionCastTargets p {
        caster := p
        cost
        spellId := newId
        original
        originalSnapshot := origSnap
        origPerm
        isFreeFromGy
        needsSacrificeOther := needsSacrifice
        payLife := lifeInstead
        alternativeCost := altCostUsed
        resolutionCast := true
      }

/-- Resume any deferred `PendingReplacement` (such as `.finishFraChoice`) queued
by `becomeCast` or `becomeActivated` once the spell or ability finishes going
onto the stack without opening a new `Pending`. -/
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
      let g :=
        match outerCont? with
        | some outer => g.chainPendingReplacement outer
        | none => g
      return if g.pending != .none then g else g.finishFraChoice
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
        let g := g.changes #[
          .postCastCleanup (some (.lookedBottom p id ids)),
          .pending .none
        ]
        let g := g.castAsPartOfResolution p id (callerCheckpoint := true)
        if g.pending != .none then
          return g
        else if g.proposedSpell.isNone && g.postCastCleanup.isSome then
          let g := g.runPostCastCleanup
          return if g.pending != .none then g else g.finishFraChoice
        else if (g.followMovedToZone? id (· == .stack)).isSome then
          return g.finishFraChoice
        else
          return g
  | _ => throw "Not time to choose a spell from among looked-at cards"

/-- After a trigger's targets (and any damage division) are fully announced,
prompt the next trigger that needs targets or continue the CR 603.3b
process (remaining waiting triggers, then SBAs). -/
partial def afterTriggerTargetsChosen (g : Game) : Game :=
  match g.triggerNeedingTargets with
  | some _ =>
    promptTriggerTargetsIfNeeded (g.change (.pending .none))
  | none =>
    let prio := g.pendingPriority.getD g.activePlayer
    receivePriority (g.change (.pending .none)) prio false

/-- Start paying the proposed activation's costs that need chosen objects,
reversing it if they can't be paid (CR 601.2h / 733.1). -/
partial def beginActivationPayment (g : Game) (prop : ProposedSpell) : Except String Game := do
  let picks := (prop.activation.map costPicksOf).getD #[]
  let payable :=
    match prop.sourceId with
    | some sid => g.costPicksPayable prop.caster (some sid) picks
    | none => true
  if !payable then return (← g.reverseProposedSpell? (resumeContinuation := true))
  let g ← g.continueCostPicks prop picks prop.cost.includesManaPayment
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
        (face.kicker.isSome || (!prop.alternativeCost && (face.morph.isSome || face.impending.isSome)))
    if needsKicker then
      (g.change (.pending (.chooseKicker p))).logMsg
        s!"{(g.player p).name} may kick the spell (CR 702.33 / 601.2b)"
    else if face.giftTreasure && !prop.giftAnnounced then
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
        (g.currentSpellEffect spell).any (·.allowsZeroTargets)
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
        (face.kicker.isSome || (!prop.alternativeCost && (face.morph.isSome || face.impending.isSome)))
    if face.announcesAdditionalCost then
      (g.change (.pending (.chooseAdditionalCost p))).logMsg
        s!"{(g.player p).name} must choose an additional cost (CR 601.2b)"
    else if needsKicker then
      (g.change (.pending (.chooseKicker p))).logMsg
        s!"{(g.player p).name} may kick the spell (CR 702.33 / 601.2b)"
    else if face.giftTreasure && !prop.giftAnnounced then
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
  if !g.openingHandsPending && !g.over && !g.players.isEmpty &&
      g.afterRandom == .none && g.pendingRandom?.isNone then
    let g := finishAndGrantPriority g
    if g.pending == .none && g.afterRandom == .none then
      g.completeActiveResolutions
    else g
  else g

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
    let g :=
      match after with
      | .none => g
      | .draw p n => g.draw p n
      | .gainLife p n => g.gainLife p n
      | .revealRandomCreatureThenBottom _ _ => g
      | .putOnTop p ids => g.putIdsOnTop p ids
      | .beholdUntap p landId subtype => g.beholdAndMaybeUntap p landId subtype
      | .plusOne id ctrl srcId => g.addPlusOneIfStillCreature id ctrl srcId
      | .discardRandom p =>
        let hand := (g.player p).hand
        if hand.isEmpty then g
        else if hand.size == 1 then g.discardFromHandRandomly p hand[0]!
        else g.changes #[.pending (.resolveRandom (.chooseObject hand)), .afterRandom (.discardRandom p)]
    if grantPriority then finishHostRandom g else g
end

/-- Continue the proposal window after kicker / gift announcements. -/
def afterOptionalAdditionalCost (g : Game) (p : PlayerId) : Game :=
  match g.proposedSpell, g.proposedSpell.bind (fun prop => g.findObject? prop.spellId) with
  | some prop, some spell =>
    let face := g.baseCard spell
    if face.giftTreasure && !prop.giftAnnounced then
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
              !(effectiveSpellModes face).any (g.spellModeIsChoosable p · (some prop.spellId)) &&
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
    let effModes := effectiveSpellModes face
    if face.chooseBothIfTeamwork &&
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
          s!"{(g.player p).name} puts {(g.object! id).name} on top of their library"
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
        s!"{(g.player p).name} puts {(g.object! id).name} on the bottom of their library"
    g := g.logPutOnTop p looked top
    let happened :=
      GameEvent.looked g.turnNumber p count false asked
        (top := top) (rest := bottom) (cause := cause)
    g := (g.record happened).finishLibraryLookCore
    g :=
      match outerCont? with
      | some outer => g.chainPendingReplacement outer
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
    let g :=
      match outerCont? with
      | some outer => g.chainPendingReplacement outer
      | none => g
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
    let hasConvoke := prop.kind == .spell && (g.currentKeywords spell).convoke
    let hasImprovise := prop.kind == .spell && g.spellHasImprovise (g.baseCard spell) p
    if !hasConvoke && !hasImprovise then
      throw s!"{spell.name} doesn't have convoke or improvise (CR 702.51 / 702.126)"
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
            g := g.logMsg s!"{(g.player p).name} taps {g.name o} to convoke {spell.name}"
          else if hasImprovise && g.isArtifact o then
            if cost.genericCount == 0 then
              throw s!"No generic mana is left for {g.name o} to pay (CR 702.126a)"
            cost := cost.reduceGeneric 1
            g := g.becomeTapped o (cause := some (.costPayment .tap p (some prop.spellId)))
            g := g.logMsg s!"{(g.player p).name} taps {g.name o} for improvise"
          else
            throw s!"{g.name o} can't help pay for {spell.name}"
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
          throw s!"{o.name} is not a permanent on the battlefield (CR 701.34a)"
        if !o.status.hasCounters then
          throw s!"{o.name} has no counters"
      | .player pid =>
        let pl := g.player pid
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
      let g :=
        match outerCont? with
        | some outer => g.chainPendingReplacement outer
        | none => g
      return if remaining > 1 then g else g.finishFraChoice
    else if remaining > 1 then
      let g := g.change (.pending (.chooseProliferate p (remaining - 1)))
      return match outerCont? with
        | some outer => g.chainPendingReplacement outer
        | none => g
    else
      let g :=
        match outerCont? with
        | some outer => g.chainPendingReplacement outer
        | none => g
      return g.finishFraChoice
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
  let owner := card.owner
  let msg := s!"{(g.player p).name} discards {card.name}{logSuffix}"
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
    let inMayThen := g.mayThenDrop > 0
    let outerCont? := g.pendingReplacement
    let g0 := if outerCont?.isSome then g.change (.pendingReplacement none) else g
    let (g, _) ← g0.discardPendingCard p q id
    let g :=
      if let .chooseReplacement .. := g.pending then
        g.chainPendingReplacement (.finishDiscardForDrawMay p n)
      else
        g.finishDiscardForDrawMay p n
    let g :=
      match outerCont? with
      | some outer =>
        if inMayThen then g.change (.pushOuterPendingReplacement outer)
        else g.chainPendingReplacement outer
      | none => g
    return g.finishAndGrantPriority
  | .maySacArtifactOrDiscard q n =>
    let inMayThen := g.mayThenDrop > 0
    let outerCont? := g.pendingReplacement
    let g0 := if outerCont?.isSome then g.change (.pendingReplacement none) else g
    let (g, _) ← g0.discardPendingCard p q id
    let g := g.finishSacArtifactOrDiscardDraw p n
    let g :=
      match outerCont? with
      | some outer =>
        if inMayThen then g.change (.pushOuterPendingReplacement outer)
        else g.chainPendingReplacement outer
      | none => g
    return if g.mayThenResume then g.acceptMayThen else g.finishAndGrantPriority
  | .chooseDiscardCard q remaining =>
    let outerCont? := g.pendingReplacement
    let g0 := if outerCont?.isSome then g.change (.pendingReplacement none) else g
    let (g, card) ← g0.discardPendingCard p q id
    let g :=
      if let .chooseReplacement .. := g.pending then
        g.chainPendingReplacement (.finishChooseDiscardCard p card remaining)
      else
        g.finishChooseDiscardCard p card remaining
    let g :=
      match outerCont? with
      | some outer => g.chainPendingReplacement outer
      | none => g
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
    let g :=
      match outerCont? with
      | some outer => g.chainPendingReplacement outer
      | none => g
    return g.finishAndGrantPriority
  | .discardForAdditionalCost q =>
    let some prop := g.proposedSpell | throw "No spell is waiting for an additional cost"
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
    let g :=
      if !paused then
        match outerCont? with
        | some outer => g.chainPendingReplacement outer
        | none => g
      else g
    if prop.kind == .turnFaceUp then
      let g := g.completeTurnFaceUp prop.caster prop.spellId
        (hadOuterReplacement := outerCont?.isSome)
      let g :=
        if paused then
          match outerCont? with
          | some outer => g.chainPendingReplacement outer.ensureEndsWithFinishFra
          | none => g
        else g
      return g.resumeAfterBecomeCast
    let clearPending : Array EngineChange :=
      if paused then #[] else #[.pending .none]
    let g := g.changes (clearPending ++ #[.proposedSpell none, .consecutivePasses 0])
    let g := g.becomeCast prop.caster (g.object! prop.spellId)
      (grantPriority := !isResCast)
      (hadOuterReplacement := outerCont?.isSome)
      (hadOpenContinuation := some openCont)
    let g :=
      if paused then
        match outerCont? with
        | some outer => g.chainPendingReplacement outer.ensureEndsWithFinishFra
        | none => if isResCast then g.chainPendingReplacement .finishFraChoice else g
      else g
    if isResCast then
      if (match g.pending with | .chooseReplacement .. => true | _ => false) &&
          g.pendingReplacement.any (·.endsWithFinishFra) then
        return g
      else
        return g.finishFraChoice
    else
      return g.resumeAfterBecomeCast
  | .payWard q spellId cost =>
    if p != q then
      throw s!"Only {(g.player q).name} may discard for ward"
    let legal :=
      match cost with
      | .discardEnchantmentInstantOrSorcery =>
        match g.findObject? id with
        | some o =>
          g.isEnchantment o || g.isInstantOrSorcery o
        | none => false
      | .discardOrPay _ => true
      | .discardCard => true
      | _ => false
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
    if !(g.player p).manaPool.canPay (ManaCost.ofGeneric n) (allowCantNonartifact := true) then
      throw s!"{(g.player p).name} cannot pay \{{n}}"
    let outerCont? := g.pendingReplacement
    let g := if outerCont?.isSome then g.change (.pendingReplacement none) else g
    let forObj :=
      (g.currentResolvingContext?.bind Prod.fst) <|> g.resolvingAbility <|> g.resolvingSpell
    let g ← g.payCost p (ManaCost.ofGeneric n) (allowCantNonartifact := true) (forObject := forObj)
    let g := g.logMsg s!"{(g.player p).name} pays \{{n}}"
    if g.mayThenDrop > 0 then
      let g := g.acceptMayThenCore
      let g :=
        match outerCont? with
        | some outer => g.change (.pushOuterPendingReplacement outer)
        | none => g
      return g.finishAndGrantPriority
    else
      let g := (g.change (.pending .none)).draw p 1
      let g :=
        match outerCont? with
        | some outer => g.chainPendingReplacement outer
        | none => g
      return g.finishAndGrantPriority
  | .payOrLetCounter q n _ =>
    if p != q then
      throw s!"Only {(g.player q).name} may pay \{{n}}"
    if !(g.player p).manaPool.canPay (ManaCost.ofGeneric n) (allowCantNonartifact := true) then
      throw s!"{(g.player p).name} cannot pay \{{n}}"
    let outerCont? := g.pendingReplacement
    let g := if outerCont?.isSome then g.change (.pendingReplacement none) else g
    let forObj :=
      (g.currentResolvingContext?.bind Prod.fst) <|> g.resolvingAbility <|> g.resolvingSpell
    let g ← g.payCost p (ManaCost.ofGeneric n) (allowCantNonartifact := true) (forObject := forObj)
    let g := g.logMsg s!"{(g.player p).name} pays \{{n}}"
    let g := (g.change (.pending .none)).clearUnlessPays
    let g :=
      match outerCont? with
      | some outer => g.chainPendingReplacement outer
      | none => g
    return g.finishAndGrantPriority
  | .payWard q _ (.genericMana n) | .payWard q _ (.discardOrPay n) =>
    if p != q then
      throw s!"Only {(g.player q).name} may pay ward"
    if !(g.player p).manaPool.canPay (ManaCost.ofGeneric n) (allowCantNonartifact := true) then
      throw s!"{(g.player p).name} cannot pay \{{n}}"
    let outerCont? := g.pendingReplacement
    let g := if outerCont?.isSome then g.change (.pendingReplacement none) else g
    let forObj :=
      (g.currentResolvingContext?.bind Prod.fst) <|> g.resolvingAbility <|> g.resolvingSpell
    let g ← g.payCost p (ManaCost.ofGeneric n) (allowCantNonartifact := true) (forObject := forObj)
    let g := g.logMsg s!"{(g.player p).name} pays \{{n}} (ward)"
    return g.finishWardAndDrain outerCont?
  | _ => throw "Not time to pay generic mana"

/-- Resolve the effect stashed by `SpellResolution.may`. -/
def acceptMay (g : Game) (p : PlayerId) : Except String Game := do
  match g.pending with
  | .mayResolve q =>
    if p != q then
      throw s!"Only {(g.player q).name} may accept"
    let outerCont? := g.pendingReplacement
    let g := if outerCont?.isSome then g.change (.pendingReplacement none) else g
    match g.mayOnAccept, g.mayContext with
    | some action, some _ =>
      let g := (g.changes #[
        .pending .none,
        .mayOnAccept none,
        .mayOnDecline none,
        .setTriggerSequenceRestFromMay [action] ]).clearMay
      let g := g.resumeTriggerSequence
      let g :=
        match outerCont? with
        | some outer => g.chainPendingReplacement outer
        | none => g
      return g.finishAndGrantPriority
    | _, _ =>
      let some effect := g.mayEffect | throw "Nothing to resolve"
      let controller := g.mayController
      let targets := g.mayTargets
      let sourceId := g.maySource
      let g := (g.change (.pending .none)).clearMay
      let g := g.applyUnified controller effect targets (sourceId := sourceId)
      let g :=
        match outerCont? with
        | some outer => g.chainPendingReplacement outer
        | none => g
      return g.finishAndGrantPriority
  | _ => throw "Nothing to accept now"

/-- Apply alternative `idx` of a pending `TriggerResolution.or`, preserving
outer `PendingReplacement` continuations and resuming via `finishAndGrantPriority`. -/
def chooseTriggerOr (g : Game) (p : PlayerId) (idx : Nat) : Except String Game := do
  match g.pending, g.triggerOr with
  | .chooseTriggerOr q, some rest =>
    if p != q then throw s!"Only {(g.player q).name} may choose"
    match rest.alternatives[idx]? with
    | none => throw "No such choice"
    | some r =>
      let g :=
        match g.pendingReplacement with
        | some outer => g.changes #[.pendingReplacement none, .pushOuterPendingReplacement outer]
        | none => g
      let g := g.changes #[.pending .none, .triggerOr none]
      let g := g.applyTriggeredAbility rest.controller rest.ability rest.sourceId
        rest.targets rest.dividedDamage rest.lastKnownPower rest.lastKnownToughness
        rest.sourceName (some r) rest.cardPower
      return g.finishAndGrantPriority
  | _, _ => throw "Not time to choose"

/-- Apply alternative `idx` of a pending `SpellResolution.or`. -/
def chooseSpellOr (g : Game) (p : PlayerId) (idx : Nat) : Except String Game := do
  match g.pending with
  | .chooseLibraryPlacement q id? =>
    if p != q then
      let what := if g.spellOrLibrary then "top or bottom" else "an effect"
      throw s!"Only {(g.player q).name} may choose {what}"
    if idx >= g.spellOr.size then
      throw "No such choice"
    if g.spellOrLibrary then
      let some id := id? | throw "no such object"
      let some o := g.findObject? id | throw "no such object"
      if !o.isOnBattlefield then
        throw s!"{o.name} is no longer on the battlefield"
    let outerCont? := g.pendingReplacement
    let g := if outerCont?.isSome then g.change (.pendingReplacement none) else g
    let effect := g.spellOr[idx]!
    let controller := g.spellOrController
    let targets := g.spellOrTargets
    let sourceId := g.spellOrSource
    let g := (g.change (.pending .none)).clearSpellOr
    let g := g.applyUnified controller effect targets (sourceId := sourceId)
    let g :=
      match outerCont? with
      | some outer => g.chainPendingReplacement outer
      | none => g
    return g.finishAndGrantPriority
  | _ => throw "Not time to choose library placement"

/-- Put the pending card on top or bottom of its owner's library.
When `spellOr` is set, top is the first alternative and bottom the second. -/
def chooseLibrarySide (g : Game) (p : PlayerId) (top : Bool) : Except String Game := do
  if !g.spellOr.isEmpty then
    g.chooseSpellOr p (if top then 0 else 1)
  else
    match g.pending with
    | .chooseLibraryPlacement q id? =>
      if p != q then
        throw s!"Only {(g.player q).name} may choose top or bottom"
      let some id := id? | throw "no such object"
      let some o := g.findObject? id | throw "no such object"
      if !o.isOnBattlefield then
        throw s!"{o.name} is no longer on the battlefield"
      let outerCont? := g.pendingReplacement
      let g := if outerCont?.isSome then g.change (.pendingReplacement none) else g
      let g := (g.change (.pending .none)).putOnOwnerLibrary o (top := top)
      let g :=
        match outerCont? with
        | some outer => g.chainPendingReplacement outer
        | none => g
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
    let g :=
      match outerCont? with
      | some outer => g.chainPendingReplacement outer
      | none => g
    return g.finishAndGrantPriority
  | .tapHumans q =>
    if p != q then
      throw s!"Only {(g.player q).name} may tap Humans"
    if !uniqueObjectIds ids then
      throw "Duplicate card"
    let outerCont? := g.pendingReplacement
    let g := if outerCont?.isSome then g.change (.pendingReplacement none) else g
    let (g, n) ← (g.change (.pending .none)).withBatchExcept none fun g => do
      let mut g := g
      let mut n : Nat := 0
      for id in ids do
        let some o := g.findObject? id | throw "no such object"
        if !(o.isOnBattlefield && g.controlledBy o p && g.hasSubtype o .human &&
            !o.status.tapped) then
          throw s!"{g.name o} is not an untapped Human you control"
        g := g.applyPermanentAction o .tap
        n := n + 1
      return (g, n)
    let mut g := g.change (.humansTappedThisWay n)
    g := g.resumeTriggerSequence
    g :=
      match outerCont? with
      | some outer => g.chainPendingReplacement outer
      | none => g
    return g.finishAndGrantPriority
  | .chooseTeamworkCreatures _ _ =>
    g.payTeamworkCreatures p ids
  | .chooseDiscardCard q remaining =>
    if g.thirstDiscardsLeft == 0 then
      throw "Not time to choose permanents"
    if p != q then
      throw s!"Only {(g.player q).name} may discard"
    if !uniqueObjectIds ids then
      throw "Duplicate card"
    let hand := (g.player p).hand
    if !ids.all hand.contains then
      throw "That card is not in your hand"
    let nReq := Nat.min g.thirstDiscardsLeft hand.size
    let isSingleEscape :=
      ids.size == 1 && (g.findObject? ids[0]!).any (fun c => g.hasType c g.thirstDiscardType)
    let isFullDiscard := ids.size == nReq && ids.size > 0
    if !isSingleEscape && !isFullDiscard then
      throw s!"Choose one {g.thirstDiscardType.oracleWord} card or {nReq} card(s) from your hand"
    let outerCont? := g.pendingReplacement
    let g := if outerCont?.isSome then g.change (.pendingReplacement none) else g
    let g := g.changes #[.pending .none, .thirstDiscardsLeft 0]
    let pairs := ids.map (fun cid => (p, cid))
    let g :=
      if g.discardBatch.isSome then
        let g := g.discardMultiHandIdsLoop pairs (logEach := true)
        if let .chooseReplacement .. := g.pending then
          let g := g.chainPendingReplacement (.finishPostStep .closeDiscardBatchStep)
          if !remaining.isEmpty || g.plusOneAfterDiscards.isSome then
            g.chainPendingReplacement
              (.finishPostStep (.continueAfterDiscardStep remaining false (max 1 g.discardCountPerPlayer)))
          else g
        else
          let g := g.closeCurrentDiscardBatch
          if !remaining.isEmpty || g.plusOneAfterDiscards.isSome then
            g.continueAfterDiscard remaining (samePlayer := false) (count := max 1 g.discardCountPerPlayer)
          else g
      else
        let g := g.withBatch none fun g =>
          g.discardMultiHandIdsLoop pairs (logEach := true)
        if !remaining.isEmpty || g.plusOneAfterDiscards.isSome then
          if let .chooseReplacement .. := g.pending then
            g.chainPendingReplacement
              (.finishPostStep (.continueAfterDiscardStep remaining false (max 1 g.discardCountPerPlayer)))
          else
            g.continueAfterDiscard remaining (samePlayer := false) (count := max 1 g.discardCountPerPlayer)
        else g
    let g :=
      match outerCont? with
      | some outer => g.chainPendingReplacement outer
      | none => g
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
    let origPerm := g.playPermission card
    if g.cantCastSpellsThisTurn p then
      throw "You can't cast spells this turn (CR 101.2)"
    if g.splitSecondOnStack then
      throw "A spell with split second is on the stack (CR 702.61a)"
    if g.combatLocksNonManaAbilities then
      throw "During combat, players can't cast spells (Yuriko, Blade of the Mighty)"
    if g.opponentsCantCastOnActiveTurn p then
      throw "Opponents can't cast spells during that player's turn"
    if g.isLand card then
      throw "An effect that lets you cast a card doesn't let you play a land (ruling 855)"
    let canMorph :=
      face.morph.isSome && face.kicker.isNone &&
        !(origPerm.any (fun pm => pm.withoutManaCost || pm.payLifeEqualManaValue)) &&
        !g.spellNameForbidden ""
    if !canMorph then
      if g.spellNameForbidden face.name then
        throw s!"Spells named {face.name} can't be cast"
      if !g.graveyardCastThresholdMet p card.id face then
        let n := face.castOnlyIfGraveyardAtLeast.getD 0
        throw s!"{face.name} can be cast only with {n} or more other cards in your graveyard"
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
      if origPerm.any (·.payLifeEqualManaValue) &&
          !g.canPayLife p (g.objectManaValue card) then
        throw s!"{(g.player p).name} can't pay {g.objectManaValue card} life to cast {face.name} (CR 119.4)"
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
    let spellObj := g.object! newId
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
    let cost := g.playManaCost preSpell stackFace (origPerm := origPerm) (isFreeFromGy := some false)
      (flashback := some false) (explicitAltCost := altCostUsed)
    let lifeInstead :=
      if origPerm.any (·.payLifeEqualManaValue) then g.objectManaValue spellObj else 0
    let needsSacrifice :=
      stackFace.additionalCostSacrificeCreature ||
        (stackFace.additionalCostSacrificeArtifactOrCreature && stackFace.additionalCostOrPayGeneric.isNone)
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
    }
    let g' := g.beginResolutionCastTargets p prop
    return if g'.pending == .none && (g'.findObject? newId).any (·.zone == .stack) then
      g'.finishFraChoice
    else g'
  | _ => throw "No exiled card may be cast now"

/-- Decline an optional discard (CR 608.2d) or choose no target for an
“up to one” trigger (CR 601.2c / 115.1c). -/
def decline (g : Game) (p : PlayerId) : Except String Game := do
  match g.pending with
  | .chooseMode q =>
    if p != q then throw s!"Only {(g.player q).name} may choose modes"
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
    let g :=
      match outerCont? with
      | some outer => g.chainPendingReplacement outer
      | none => g
    return g.finishAndGrantPriority
  | .mayDiscardDraw q _ =>
    if p != q then
      throw s!"Only {(g.player q).name} may decline to discard"
    let outerCont? := g.pendingReplacement
    let g := if outerCont?.isSome then g.change (.pendingReplacement none) else g
    let g := g.logMsg s!"{(g.player p).name} declines to discard a card"
    let g := if g.mayThenDrop > 0 then g.declineMayThenCore else g.change (.pending .none)
    let g :=
      match outerCont? with
      | some outer => g.chainPendingReplacement outer
      | none => g
    return g.finishAndGrantPriority
  | .chooseTargets caster =>
    if caster != p then
      throw s!"Only {(g.player caster).name} may choose targets (CR 601.2c)"
    let some obj := g.objectAwaitingTargets | throw "No spell is waiting for a target (CR 601.2c)"
    if g.canSkipCurrentOptionalSlot obj then
      let g := g.skipOptionalTargetSlot obj.id
      let g := g.logMsg
        s!"{(g.player p).name} chooses no target (CR 603.3d / 601.2c)"
      if g.currentTargetSlot obj < (g.targetingOf obj).kind.spec.slots.size then
        return g.change (.pending (.chooseTargets p))
      if g.proposedSpell.isSome then
        return g.afterTargetsChosen
      let g :=
        match g.stackEntry? obj.id with
        | some e =>
          if e.targets.isEmpty then g.markTargetsAnnounced obj.id true
          else g.setStackEntryTargets obj.id e.targets e.dividedDamage
        | none => g
      return g.afterTriggerTargetsChosen
    else if g.canFinishOptionalTargets obj then
      let startSlot := g.currentTargetSlot obj
      let totalSlots := (g.targetingOf obj).kind.spec.slots.size
      let g := (List.range (totalSlots - startSlot)).foldl
        (fun acc _ => acc.skipOptionalTargetSlot obj.id) g
      let g := g.logMsg
        s!"{(g.player p).name} finishes choosing targets (CR 601.2c)"
      if g.proposedSpell.isSome then
        return g.afterTargetsChosen
      let g :=
        match g.stackEntry? obj.id with
        | some e =>
          if e.targets.isEmpty then g.markTargetsAnnounced obj.id true
          else g.setStackEntryTargets obj.id e.targets e.dividedDamage
        | none => g
      return g.afterTriggerTargetsChosen
    else
      match obj.triggeredAbility with
      | some ab =>
        if !ab.allowsZeroTargets then
          throw "That ability requires a target (CR 601.2c)"
        let g := g.setStackEntryTargets obj.id #[]
        let g := g.logMsg
          s!"{(g.player p).name} chooses no target (CR 603.3d / 601.2c)"
        return g.afterTriggerTargetsChosen
      | none =>
        let allowZero :=
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
          if g.proposedSpell.isSome then
            return g.afterTargetsChosen
          return g.afterTriggerTargetsChosen
        throw "That spell requires a target (CR 601.2c)"
  | .mayPayGeneric q _ =>
    if p != q then
      throw s!"Only {(g.player q).name} may decline to pay"
    let outerCont? := g.pendingReplacement
    let g := if outerCont?.isSome then g.change (.pendingReplacement none) else g
    let g := g.logMsg s!"{(g.player p).name} declines to pay"
    let g := if g.mayThenDrop > 0 then g.declineMayThenCore else g.change (.pending .none)
    let g :=
      match outerCont? with
      | some outer => g.chainPendingReplacement outer
      | none => g
    return g.finishAndGrantPriority
  | .payOrLetCounter q _ spellId =>
    if p != q then
      throw s!"Only {(g.player q).name} may decline to pay"
    let outerCont? := g.pendingReplacement
    let g := if outerCont?.isSome then g.change (.pendingReplacement none) else g
    let g := g.logMsg s!"{(g.player p).name} does not pay"
    let instead := g.unlessPaysInstead
    let caster := g.unlessPaysController
    let targets := g.unlessPaysTargets
    let sourceId := g.unlessPaysSource
    let g := (g.change (.pending .none)).clearUnlessPays
    let g :=
      match instead with
      | some effect => g.applyUnified caster effect targets (sourceId := sourceId)
      | none =>
        match spellId with
        | some sid => g.counterStackSpell sid (controller := some caster)
        | none => g
    let g :=
      match outerCont? with
      | some outer => g.chainPendingReplacement outer
      | none => g
    return g.finishAndGrantPriority
  | .payWard _ _ (.sacrificePermanents _ (_ + 1) _) =>
    throw s!"{(g.player p).name} already began sacrificing permanents for ward and must finish"
  | .payWard q spellId _ =>
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
    let g :=
      match outerCont? with
      | some outer => g.chainPendingReplacement outer
      | none => g
    return g.finishAndGrantPriority
  | .mayResolve q =>
    if p != q then
      throw s!"Only {(g.player q).name} may decline"
    let outerCont? := g.pendingReplacement
    let g := if outerCont?.isSome then g.change (.pendingReplacement none) else g
    let g := g.logMsg s!"{(g.player p).name} declines"
    let g :=
      match g.mayOnDecline, g.mayContext with
      | some follow, some _ =>
        let g := (g.changes #[
          .pending .none,
          .mayOnAccept none,
          .mayOnDecline none,
          .setTriggerSequenceRestFromMay [follow] ]).clearMay
        g.resumeTriggerSequence
      | _, _ =>
        (g.changes #[.pending .none, .mayOnAccept none, .mayOnDecline none, .mayContext none]).clearMay
    let g :=
      match outerCont? with
      | some outer => g.chainPendingReplacement outer
      | none => g
    return g.finishAndGrantPriority
  | .tapHumans q =>
    if p != q then
      throw s!"Only {(g.player q).name} may decline to tap Humans"
    let outerCont? := g.pendingReplacement
    let g := if outerCont?.isSome then g.change (.pendingReplacement none) else g
    let g := g.logMsg s!"{(g.player p).name} taps no Humans"
    let g := (g.changes #[.pending .none, .humansTappedThisWay 0]).resumeTriggerSequence
    let g :=
      match outerCont? with
      | some outer => g.chainPendingReplacement outer
      | none => g
    return g.finishAndGrantPriority
  | .maySacrificeAnotherBolg q _ =>
    if p != q then
      throw s!"Only {(g.player q).name} may decline to sacrifice"
    let outerCont? := g.pendingReplacement
    let g := if outerCont?.isSome then g.change (.pendingReplacement none) else g
    let g := (g.change (.pending .none)).logMsg
      s!"{(g.player p).name} declines to sacrifice a creature to Bolg"
    let g :=
      match outerCont? with
      | some outer => g.chainPendingReplacement outer
      | none => g
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
    let g :=
      match outerCont? with
      | some outer => g.chainPendingReplacement outer
      | none => g
    return g.finishAndGrantPriority
  | .maySacArtifactOrDiscard q _ =>
    if p != q then
      throw s!"Only {(g.player q).name} may decline"
    let outerCont? := g.pendingReplacement
    let g := if outerCont?.isSome then g.change (.pendingReplacement none) else g
    let g := g.logMsg
      s!"{(g.player p).name} declines to sacrifice an artifact or discard a card"
    let g := if g.mayThenDrop > 0 then g.declineMayThenCore else g.change (.pending .none)
    let g :=
      match outerCont? with
      | some outer => g.chainPendingReplacement outer
      | none => g
    return g.finishAndGrantPriority
  | .mayPutArtifactFromHand q _ =>
    if p != q then
      throw s!"Only {(g.player q).name} may decline to put an artifact onto the battlefield"
    let outerCont? := g.pendingReplacement
    let g := if outerCont?.isSome then g.change (.pendingReplacement none) else g
    let g := g.logMsg
      s!"{(g.player p).name} declines to put an artifact onto the battlefield"
    let g := g.changes #[.pending .none, .putArtifactThisWay none]
    let g :=
      match outerCont? with
      | some outer => g.chainPendingReplacement outer
      | none => g
    return g.finishAndGrantPriority
  | .mayHaveVillainConnive q _ _ =>
    if p != q then
      throw s!"Only {(g.player q).name} may decline to have the Villain connive"
    let outerCont? := g.pendingReplacement
    let g := if outerCont?.isSome then g.change (.pendingReplacement none) else g
    let g := (g.change (.pending .none)).logMsg s!"{(g.player p).name} declines to have the Villain connive"
    let g :=
      match outerCont? with
      | some outer => g.chainPendingReplacement outer
      | none => g
    return g.finishAndGrantPriority
  | .sacrificePermanent q excludeId =>
    if p != q then
      throw s!"Only {(g.player q).name} may act on that cost"
    if !(g.sacrificeCreatureOrArtifactChoices q excludeId).isEmpty then
      throw "You must sacrifice an artifact or creature"
    g.reverseProposedSpell? (resumeContinuation := true)
  | .discardForAdditionalCost q =>
    if p != q then
      throw s!"Only {(g.player q).name} may act on that cost"
    if !(g.player q).hand.isEmpty then
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
    if (g.player p).hand.isEmpty then
      let outerCont? := g.pendingReplacement
      let g := if outerCont?.isSome then g.change (.pendingReplacement none) else g
      let g := g.continueAfterDiscard (#[p] ++ remaining) (samePlayer := true) (count := max 1 n)
      let g :=
        match outerCont? with
        | some outer => g.chainPendingReplacement outer
        | none => g
      return g.finishAndGrantPriority
    else
      return g
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
    if !ids.contains id then
      throw s!"Choose one of the legendary permanents named {name} (CR 704.5j)"
    let some kept := g.findObject? id | throw "no such object"
    if !kept.isOnBattlefield then
      throw s!"{g.name kept} is not on the battlefield"
    let outerCont? := g.pendingReplacement
    let g := if outerCont?.isSome then g.change (.pendingReplacement none) else g
    let others := ids.filter (· != id)
    let rec findSweepPreBf? : PendingReplacement → Option (Array GameObject)
      | .finishSbaSweep _ pbf .. => some pbf
      | .seq a b => findSweepPreBf? a <|> findSweepPreBf? b
      | _ => none
    let sweepPreBf? :=
      (outerCont?.bind findSweepPreBf?).orElse
        (fun _ => g.outerPendingReplacements.findSomeRev? findSweepPreBf?)
    let preBf :=
      sweepPreBf?.getD
        (if g.currentBatch.isSome then g.openBatchObjects.filter GameObject.isOnBattlefield
         else g.battlefield)
    let g := (g.change (.pending .none) |>.logMsg
      s!"{(g.player p).name} keeps {g.name kept} (legend rule, CR 704.5j)").withBatch
      (some (.stateBased .legendRule)) fun g => Id.run do
        let mut g := g
        for i in [0:others.size] do
          let other := others[i]!
          match g.findObject? other with
          | some o =>
            if o.isOnBattlefield then
              g := g.moveToOwnerGraveyard o
                s!"{g.name o} is put into its owner's graveyard (legend rule, CR 704.5j)"
                (preBattlefield := some preBf)
                (cause := some (.stateBased .legendRule))
              if let .chooseReplacement .. := g.pending then
                let rem := others.extract (i + 1) others.size
                if !rem.isEmpty then
                  g := g.chainPendingReplacement
                    (.moveSimultaneousToGraveyard rem (some preBf) (some (.stateBased .legendRule)))
                return g
          | none => pure ()
        return g
    let g :=
      match outerCont? with
      | some outer => g.chainPendingReplacement outer
      | none => g
    let prio := g.pendingPriority.getD g.activePlayer
    return g.finishAndGrantPriority prio
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
      if (g.findObject? id).isNone then
        throw "no such object"
      if !pl.hand.contains id then
        throw "That card is not in your hand"
    let g := g.withBatch (some (.gameRule .mulligan)) fun g => Id.run do
      let mut g := g
      for i in [0:ids.size] do
        let id := ids[i]!
        let card := g.object! id
        let ownerName := (g.player p).name
        let libSize := ((g.player p).library.filter (· != id)).size
        let pos : LibraryPosition :=
          if i == 0 then .bottom else .fromTop (libSize - Nat.min i libSize)
        let (g', _) := g.move id (.library p) (libraryPosition := some pos)
          (cause := some (.gameRule .mulligan))
        g := g'
        g := g.logMsg s!"{ownerName} puts {card.name} on the bottom of their library"
      return g
    let mut g := g
    if g.mulliganToBottom.isEmpty then
      g := g.change (.pending .none)
      return g.receivePriority g.activePlayer
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
      let g :=
        match outerCont? with
        | some outer => g.chainPendingReplacement outer
        | none => g
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
      return reattachAndFinish (g.finishAfterRandom false)
    | .chooseObject choices =>
      match ids[0]?, ids.size with
      | some id, 1 =>
        if !choices.contains id then
          throw "That is not one of the random choices"
        match g.afterRandom with
        | .revealRandomCreatureThenBottom controller revealed =>
          let g := g.changes #[.pending .none, .afterRandom .none]
          let g := g.resolveRandomCreatureReveal controller revealed id
          return reattachAndFinish g
        | .discardRandom controller =>
          let g := g.changes #[.pending .none, .afterRandom .none]
          let g := g.discardFromHandRandomly controller id
          return reattachAndFinish (g.finishAfterRandom false)
        | _ =>
          let g := g.change (.pending .none)
          return reattachAndFinish (g.finishAfterRandom false)
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
      let g :=
        match outerCont? with
        | some outer => g.chainPendingReplacement outer
        | none => g
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
            (g.findObject? beholdId).any (fun o => g.hasSubtype o subtype)
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
    let g := g.changes #[.replacementOrder order, .pending .none, .pendingReplacement none]
    let g :=
      match cont? with
      | some cont => g.resumePendingReplacement cont
      | none => g
    let g := g.drainPendingContinuations
    let g :=
      if g.pending == .none && g.afterRandom == .none then
        g.completeActiveResolutions
      else g
    return g
  | _ =>
    throw "No replacement effect choice is pending"

end Game
end Mtg.Engine
