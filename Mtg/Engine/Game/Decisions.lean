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
private def priorityRecipientOfContinuation? : PendingReplacement → Option PlayerId
  | .finishPostCast caster true _ false => some caster
  | .receivePriority p => some p
  | .seq a b => priorityRecipientOfContinuation? b |>.orElse (fun _ => priorityRecipientOfContinuation? a)
  | _ => none

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
      match g.outerPendingReplacements.back? with
      | some outer =>
        let g := (g.change .popOuterPendingReplacement).resumePendingReplacement outer
        g.drainPendingContinuations
      | none =>
        if g.triggerSequenceRest.isSome then
          let g := g.resumeTriggerSequence
          g.drainPendingContinuations
        else g

/-- Drain active continuations, chain `.receivePriority p` if a CR 616.1
`Pending.chooseReplacement` pause opened, or grant priority to `p` when idle. -/
partial def finishAndGrantPriority (g : Game)
    (p : PlayerId :=
      (g.pendingReplacement.bind priorityRecipientOfContinuation?).orElse
        (fun _ => g.outerPendingReplacements.findSomeRev? priorityRecipientOfContinuation?)
        |>.getD g.activePlayer) : Game :=
  let g := g.drainPendingContinuations
  if g.over then g
  else if let .chooseReplacement .. := g.pending then
    g.chainPendingReplacement (.receivePriority p)
  else if g.pending != .none || g.afterRandom != .none then g
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

/-- Skip the conditional steps of `mayThen` without draining outer continuations
or granting priority. -/
partial def declineMayThenCore (g : Game) : Game :=
  let n := g.mayThenDrop
  let g := g.changes #[
    .pending .none,
    .mayThenDrop 0,
    .mayThenConditional none,
    .mayThenResume false,
    .sacrificedPowerThisWay none ]
  match g.triggerSequenceRest with
  | none => g
  | some rest => g.change (.setTriggerSequenceRestSteps (rest.steps.drop n))

/-- The optional action of `mayThen` was declined. Skip its conditional and
continue any later sequence steps. -/
partial def declineMayThen (g : Game) : Game :=
  g.declineMayThenCore.resumeSequenceThenPriority

/-- Continue a discard chain. When no one is left to discard, put the waiting
+1/+1 counter (Ninja of the Hand) if any. -/
partial def continueAfterDiscard (g : Game) (players : Array PlayerId) : Game :=
  let g := g.beginDiscardCards players
  if g.pending != .none then g
  else if g.plusOneAfterDiscards.isSome then g.finishPlusOneAfterDiscards
  else g

/-- Clear a finished Reality Fracture choice and let the game continue. Any
pending replacement/batch continuation runs first, then a paused trigger
sequence runs its remaining steps. -/
partial def finishFraChoice (g : Game) : Game :=
  if let .chooseReplacement .. := g.pending then
    g.chainPendingReplacement .finishFraChoice
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

/-- Resume the rules event that paused on `Pending.chooseReplacement` (CR 616.1). -/
partial def resumePendingReplacement (g : Game) (pr : PendingReplacement)
    (followedByFinishFra : Bool := false) : Game :=
  match pr with
  | .seq first rest =>
    let checkReversal : Bool :=
      match first with
      | .restorePending (.fraChoice _ (.costPicks ..)) | .completeActivation .. =>
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
  | .dealDamageToPlayer p n source unpreventable cause =>
    let srcObj := g.damageSourceObjFromSnapshot? source
    g.dealDamageToPlayer p (Int.ofNat n) (preventable := !unpreventable)
      (source := srcObj) (sourceSnap := source) (cause := cause)
  | .dealDamageToPlayers players n source cause =>
    let srcObj := g.damageSourceObjFromSnapshot? source
    g.dealDamageToPlayers players (Int.ofNat n) (source := srcObj) (sourceSnap := source)
      (cause := cause)
  | .dealDamageFrom sourceName source targetId n deathtouch cause =>
    match g.findObject? targetId with
    | some tgt =>
      let src := g.damageSourceFromSnapshot source
      g.dealDamageFrom sourceName tgt (Int.ofNat n) (deathtouch := deathtouch)
        (source := some src) (sourceSnap := some source) (cause := cause)
    | none => g
  | .dealFightDamage sourceId targetId cause =>
    match g.findObject? sourceId, g.findObject? targetId with
    | some src, some dest =>
      g.dealFightDamage src dest (cause := cause)
    | _, _ => g
  | .dealDamageToPermanent targetId n source cause =>
    match g.findObject? targetId with
    | some tgt =>
      g.dealDamageToPermanent tgt (Int.ofNat n) (source := source) (cause := cause)
    | none => g
  | .markDamageOn targetId n msg deathtouch source combat unpreventable cause =>
    match g.findObject? targetId with
    | some tgt =>
      let srcObj := g.damageSourceObjFromSnapshot? source
      g.markDamageOn tgt (Int.ofNat n) msg (deathtouch := deathtouch) (combat := combat)
        (source := source) (sourceObj := srcObj) (unpreventable := unpreventable)
        (cause := cause)
    | none => g
  | .dealAssignedCombatDamage applied startIdx =>
    g.dealAssignedCombatDamage applied startIdx
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
  | .destroyPermanent targetId cause preBattlefield =>
    match g.findObject? targetId with
    | some tgt => g.destroyPermanent tgt (preBattlefield := preBattlefield) (cause := cause)
    | none => g
  | .createToken controller card tapped attacking attackingTarget applyFoodBonus extraCounters recordRecent cause =>
    (g.createToken controller card (tapped := tapped) (attacking := attacking)
      (attackingTarget := attackingTarget) (applyFoodBonus := applyFoodBonus)
      (extraCounters := extraCounters) (recordRecent := recordRecent)
      (cause := cause)).1
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
  | .commitEnteringAttackItems chosen cause resetRecent =>
    g.commitEnteringAttackItems chosen (cause := cause) (resetRecent := resetRecent)
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
          match attachedToHost.bind g.findObject? with
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
  | .finishSbaSweep moves preBattlefield stage pwMoves sagaMoves tokensOutsideBf copiesOutside illegalAuras illegalEquips illegalCreatureAtts =>
    (g.finishSbaSweep moves preBattlefield stage pwMoves sagaMoves tokensOutsideBf
      copiesOutside illegalAuras illegalEquips illegalCreatureAtts).1
  | .untapPermanent targetId duringUntapStep logUntap cause =>
    match g.findObject? targetId with
    | some tgt =>
      g.untapPermanent tgt (duringUntapStep := duringUntapStep)
        (logUntap := logUntap) (cause := cause)
    | none => g
  | .untapStepPermanents ids =>
    g.untapStepPermanents ids
  | .beginStepAfterUntap =>
    (g.record (GameEvent.stepEnded g.turnNumber .untap
      (cause := some (.gameRule .stepAdvance)))).beginStep .upkeep
  | .addLoreCounters sagaId n cause =>
    match g.findObject? sagaId with
    | some saga => g.addLoreCounters saga n (cause := cause)
    | none => g
  | .addLoreAfterDrawStep sagaIds =>
    g.addLoreAfterDrawStepIds sagaIds
  | .copyNontokenCreatures controller snapshots cause =>
    g.copyNontokenCreaturesStep controller snapshots cause
  | .copyPermanentTokens controller card remaining cause =>
    g.createPermanentCopyTokens controller card remaining cause
  | .finishArtifactCopyToken =>
    g.finishArtifactCopyTokens
  | .finishManaAbilityMountainTrigger player sourceId =>
    g.finishManaAbilityMountainTrigger player sourceId
  | .restorePending p =>
    match p with
    | .fraChoice caster (.costPicks sid picks _) =>
      match picks[0]? with
      | some pick =>
        if (g.costPickCandidates caster sid pick).size < pick.count then
          g.reverseProposedSpell (resumeContinuation := true)
        else
          g.change (.pending p)
      | none => g.change (.pending p)
    | _ => g.change (.pending p)
  | .closeBatch batchId startIdx =>
    g.finishOpenBatch batchId startIdx
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
  | .finishTurnFaceUp caster spellId hadOuter =>
    g.completeTurnFaceUp caster spellId (hadOuterReplacement := hadOuter)
  | .endProposalAction =>
    if g.proposalCheckpoint.isSome then g.change .endProposalAction else g
  | .payCostPickItems p abilityId sourceId pick remainingIds =>
    g.payCostPickItems p abilityId sourceId pick remainingIds
  | .finishActivationExtraCosts p sourceId forObject removePlusOnes sacrificeSource exileSource stage =>
    g.finishActivationExtraCosts p sourceId forObject removePlusOnes sacrificeSource exileSource stage
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
  | .finishFreshAmass controller subtype n attach cause minId =>
    g.finishFreshAmass controller subtype n attach (cause := cause) (minId := minId)
  | .finishDealDamageLoseIndestructibleExile targetId targetName n cause =>
    g.finishDealDamageLoseIndestructibleExile targetId targetName n cause
  | .finishPlaceSearched p fromId name tapped cause =>
    g.finishPlaceSearched p fromId name tapped (cause := cause)
  | .placeSearchedBatch p remainingIds tapped cause =>
    g.placeSearchedBatch p remainingIds tapped (cause := cause)
  | .finishSearchAfterPlace p fromId dest after fromLibrary handRest cause =>
    g.finishSearchAfterPlace p fromId dest after fromLibrary handRest cause
  | .finishSurveilPostMove p card fromId remainingGy cause =>
    g.finishSurveilPostMove p card fromId remainingGy cause
  | .finishLibraryLook =>
    g.finishLibraryLookCore
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
  | .continueSpellModes controller modeEffects remainingTargets castFromGraveyard kicked giftPromised chosenX sourceId empowerJaceN skippedOptionalSlots =>
    g.runSpellModesAndEmpower controller modeEffects remainingTargets castFromGraveyard kicked giftPromised chosenX sourceId empowerJaceN skippedOptionalSlots
  | .empowerJace controller n stage targetId cause =>
    g.empowerJaceStep controller n stage targetId cause
  | .continueTriggeredSequence controller steps sourceId targets dividedDamage lastKnownPower lastKnownToughness sourceName =>
    g.runTriggeredSequenceSteps controller steps sourceId targets dividedDamage lastKnownPower lastKnownToughness sourceName
  | .continueTriggeredModes controller ab remainingModes sourceId targets dividedDamage lastKnownPower lastKnownToughness sourceName =>
    g.runChosenTriggeredModes controller ab remainingModes sourceId targets dividedDamage lastKnownPower lastKnownToughness sourceName
  | .continueConnives controller remainingIds =>
    g.runConniveObjects controller remainingIds
  | .dealDamageToEachCreatureMatching remainingIds n onlyNonSubtype exceptControllerTokens source cause =>
    g.dealDamageToEachCreatureMatchingIds remainingIds n
      (onlyNonSubtype := onlyNonSubtype)
      (exceptControllerTokens := exceptControllerTokens)
      (source := source) (cause := cause)
  | .destroyPermanentsLoop remainingIds allCandidates countNote obGainLifeFor logMsgAfter preBattlefield cause =>
    g.destroyPermanentsLoop remainingIds
      (allCandidates := allCandidates) (countNote := countNote)
      (obGainLifeFor := obGainLifeFor) (logMsgAfter := logMsgAfter)
      (preBattlefield := preBattlefield) (cause := cause)
  | .sacrificePermanentsLoop remaining preBattlefield cause createBeastFor =>
    g.sacrificePermanentsLoop remaining
      (preBattlefield := preBattlefield) (cause := cause)
      (createBeastFor := createBeastFor)
  | .putToBattlefieldLoop controller remainingIds enteredFromIds useCardOwner haste tapped isLandEnters onlyFoodArtifact cause =>
    g.putToBattlefieldLoop controller remainingIds
      (enteredFromIds := enteredFromIds) (useCardOwner := useCardOwner)
      (haste := haste) (tapped := tapped) (isLandEnters := isLandEnters)
      (onlyFoodArtifact := onlyFoodArtifact) (cause := cause)
  | .returnLinkedExileLoop remainingIds cause =>
    g.returnLinkedExileLoop remainingIds (cause := cause)
  | .finishLinkedExileMove remainingIds =>
    g.returnLinkedExileMoves remainingIds
  | .untapPermanentsLoop remainingIds cause =>
    g.untapPermanentsLoop remainingIds (cause := cause)
  | .millCardsLoop p remainingIds emptyTail cause logCard freshCount =>
    g.millCardsLoop p remainingIds (emptyTail := emptyTail) (cause := cause)
      (logCard := logCard) (freshCount := freshCount)
  | .exilePermanentsLoop remainingIds logExile cause logCard =>
    g.exilePermanentsLoop remainingIds (logExile := logExile) (cause := cause)
      (logCard := logCard)
  | .flickerLoop remainingIds exiledPreIds enteredFromIds logText stage tapped onlyLandTapped clearExileFields cause =>
    g.resumeFlickerLoop remainingIds exiledPreIds enteredFromIds logText stage
      tapped onlyLandTapped clearExileFields cause
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
  | .finishFrcRestBottom p rest shuffle cause dackTargets jhoiraLife =>
    g.finishFrcRestBottom p rest shuffle (cause := cause)
      (dackTargets := dackTargets) (jhoiraLife := jhoiraLife)
  | .finishFrcPostStep tag p n1 cardId shuffle cause ids =>
    g.runFrcPostStep tag p n1 cardId shuffle cause ids
  | .finishPostStep tag p n sourceId cardId ids targets modes shuffle cause =>
    g.runPostStep tag p n sourceId cardId ids targets modes shuffle cause
  | .acceptMayThen =>
    g.acceptMayThenCore

/-- Execute a deferred post-step continuation (`tag` `1..77`) after a CR 616.1
`Pending.chooseReplacement` pause finishes. -/
partial def runPostStep (g : Game) (tag : Nat) (p : PlayerId) (n : Nat := 0)
    (sourceId : Option ObjectId := none) (cardId : Option ObjectId := none)
    (ids : Array ObjectId := #[]) (targets : Array Target := #[])
    (modes : Array Nat := #[]) (shuffle : Bool := false)
    (cause : Option EventCause := none) : Game :=
  match tag with
  | 1 =>
    match cardId.bind (fun id => g.followMovedToZone? id (· == .battlefield)) with
    | some entered =>
      let g := g.logMsg s!"{(g.player p).name} puts {entered.name} onto the battlefield"
      let g := g.afterPermanentEnters entered
      if let some hid := sourceId then g.change (.putArtifactThisWay (some (entered.id, hid))) else g
    | none => g
  | 2 =>
    g.finishWorldsWithinWorldsTail ids sourceId
  | 3 =>
    if let some cid := cardId then g.copyEnteredArtifact p cid else g
  | 4 =>
    g.grantHandSizePower sourceId
  | 5 =>
    g.beginScry p 1
  | 6 =>
    g.copyCastTriggerSpell p
  | 7 =>
    g.pumpControlledCreatures p 1 0
  | 8 =>
    match cardId.bind g.findObject? with
    | some o =>
      let owner := o.owner
      let g := g.destroyPermanent o
      if let .chooseReplacement .. := g.pending then
        g.chainPendingReplacement (.finishPostStep 9 owner)
      else
        g.offerMaySearchBasics owner
    | none => g
  | 9 =>
    g.offerMaySearchBasics p
  | 10 =>
    g.continueDiscardTwo p (modes.map (⟨·⟩)) n
  | 11 =>
    let g :=
      match cardId.bind (fun id => g.followMovedToZone? id (· == .battlefield)) with
      | some entered => (g.logMsg s!"{entered.name} enters the battlefield").afterPermanentEnters entered
      | none => g
    if ids.isEmpty then g
    else
      g.requestOrderInto ids (.library p)
        s!"{(g.player p).name} puts the rest on the bottom of their library in a random order"
        (cause := cause)
  | 12 =>
    g.runHawkeyeArrows p modes targets n sourceId
  | 13 =>
    let drawn := g.loggedDraws p - n
    g.loseLife p drawn
  | 14 =>
    match cardId.bind (fun id => g.followMovedToZone? id (· == .battlefield)) with
    | some entered =>
      let g := g.logMsg s!"{entered.name} returns to the battlefield tapped under {(g.player p).name}'s control"
      let src := (sourceId.bind g.findObject?).orElse (fun _ => some entered)
      let g := g.registerDelayedTrigger
        { controller := p, source := src, kind := .endStepExile entered.id
          cause := cause.getD (.gameRule .spellCast) }
      g.afterPermanentEnters entered
    | none => g
  | 15 =>
    let cnt := Nat.min 2 (g.player p).hand.size
    if cnt == 0 then g
    else
      g.beginFraChoice p (.discardThenStun cnt sourceId)
        s!"{(g.player p).name} discards {cnt} card(s)"
  | 16 =>
    g.recentTokenIds.foldl (fun g tid =>
      match g.findObject? tid with
      | some entered => if entered.isOnBattlefield then g.afterPermanentEnters entered else g
      | none => g) g
  | 17 =>
    g.drainOpponents p n (sourceId.bind g.findObject?) (cause := cause)
  | 18 =>
    let cnt := g.loggedDiscards p
    match sourceId.bind (fun id => (g.findObject? id).filter (·.isOnBattlefield)) with
    | some o => if cnt > 0 then g.addPlusOnePlusOneTo o cnt else g
    | none => g
  | 19 =>
    if n > 0 then g.addManaLogged p #[.colored .red] (source := sourceId) else g
  | 20 =>
    match cardId.bind (fun id => g.followMovedToZone? id (· == .battlefield)) with
    | some entered =>
      if shuffle then g.afterLandEnters entered else g.afterPermanentEnters entered
    | none => g
  | 21 =>
    let startIdx := modes[0]?.getD 0
    let dealt :=
      match cardId with
      | some oid => g.damageDealtToPermanentSince oid startIdx
      | none => 0
    let excess := dealt - n
    if excess > 0 then g.empowerJace p excess else g
  | 22 =>
    g.beginLibrarySearch p isBasicLandCard "a basic land card" (.battlefield true)
  | 23 =>
    g.withLegalKindPermanent p .oppCreature targets (fun g tgt =>
      match sourceId.bind g.findObject? with
      | some src =>
        if src.isOnBattlefield && g.isCreature src then g.fightCreatures src tgt
        else g.logMsg "The source is no longer in play"
      | none => g.logMsg "The source is no longer in play")
      sourceId (some "The target is no longer legal")
  | 24 =>
    match cardId.bind (fun id => g.followMovedToZone? id (· == .battlefield)) with
    | some entered =>
      let name := entered.name
      let g := g.afterPermanentEnters entered
      if g.pending != .none then g
      else if (g.permanentsOf p).any (g.isEquipment ·) then
        g.change (.pending (.mayAttachEquipment p entered.id))
          |>.logMsg s!"{(g.player p).name} may attach an Equipment to {name}"
      else g
    | none => g
  | 25 =>
    let g :=
      match cardId.bind (fun id => g.followMovedToZone? id (· == .battlefield)) with
      | some entered =>
        let name := entered.name
        let g := g.afterPermanentEnters entered
        let g := if n >= 4 then g.grantUntilEotLogged (g.object! entered.id) Keyword.haste else g
        g.logMsg s!"{name} is put onto the battlefield"
      | none => g
    if shuffle then g.shuffleThen p .none else g
  | 26 =>
    g.finishRevealPutCreaturesStep p ids
      (targets.filterMap fun | Target.card id => some id | _ => none)
      (modes.map (⟨·⟩)) (cause := cause)
  | 27 =>
    (g.requestShuffle p (.gainLife p n)).continueIfShuffled
  | 28 =>
    let creatures := (g.player p).hand.filter (fun id => (g.findObject? id).any (g.isCreature ·))
    g.offerCardChoice p creatures creatures.size .creaturesToBattlefield
      s!"{(g.player p).name} may put any number of creature cards from their hand onto the battlefield"
      (cause := cause)
  | 29 =>
    match cardId.bind (fun id => g.followMovedToZone? id (· == .battlefield)) with
    | some entered =>
      let hostName := ((sourceId.bind g.findObject?).map g.name).getD "permanent"
      let g := g.logMsg s!"{g.name entered} enters the battlefield attached to {hostName}"
      g.afterPermanentEnters entered
    | none => g
  | 30 =>
    g.treasureThenDragonAfterCreate p sourceId
  | 31 =>
    g.treasureThenDragonCreateDragon p
  | 32 =>
    g.recentTokenIds.foldl (fun g tid =>
      match g.findObject? tid with
      | some entered =>
        if entered.isOnBattlefield then
          (g.logMsg s!"{entered.name} enters the battlefield").afterPermanentEnters entered
        else g
      | none => g) g
  | 33 =>
    g.dealDamageToEachOpponent p n (source := sourceId.bind g.damageSourceById?) (cause := cause)
  | 34 =>
    let startIdx := modes[0]?.getD 0
    let dealt :=
      match cardId with
      | some oid => g.damageDealtToPermanentSince oid startIdx
      | none => 0
    g.change (.excessDamageThisWay (dealt - n))
  | 35 =>
    match cardId with
    | some oid =>
      let marked := (g.findObject? oid).any (·.isOnBattlefield) && g.damageDealtToPermanentSince oid n > 0
      if marked then g.change (.permanentDealtDamageThisWay (some oid)) else g
    | none => g
  | 36 =>
    let srcName :=
      match sourceId.bind g.findObject? with
      | some src => if src.isOnBattlefield then g.name src else src.name
      | none => ((sourceId.bind g.lastKnownBefore?).map (fun (eo : EventObject) => eo.name)).getD "source"
    g.logMsg s!"two nonlegendary tokens that are copies of {srcName} are created"
  | 38 =>
    g.discardCleanupIds p ids
  | 39 =>
    g.finishPostSbaCleanup (n > 0)
  | 40 =>
    g.finishCleanupStepAfterDiscard
  | 41 =>
    let g := g.draw p n
    if let .chooseReplacement .. := g.pending then
      g.chainPendingReplacement (.finishPostStep 42 p (n := n) (modes := modes))
    else
      g.runPostStep 42 p (n := n) (modes := modes)
  | 42 =>
    match modes.toList with
    | [] => g
    | nextIdx :: more =>
      let next : PlayerId := ⟨nextIdx⟩
      g.beginFraChoice next (.mayWheel n (more.toArray.map (⟨·⟩)))
        s!"{(g.player next).name} may discard their hand and draw {n} cards"
  | 43 =>
    g.resolveSearchLibrary p (·.isPlaneswalker) false "planeswalker card"
  | 44 =>
    g.resolveSearchLibrary p (fun c => c.isCreature && c.hasSubtype .sphinx) false
      "Sphinx creature card"
  | 45 =>
    let g := g.draw p 1
    if let .chooseReplacement .. := g.pending then
      g.chainPendingReplacement (.finishPostStep 18 p (sourceId := sourceId))
    else
      g.runPostStep 18 p (sourceId := sourceId)
  | 46 =>
    if n == 0 then g
    else
      g.putReflexiveTrigger p sourceId
        { targeting := .of (.filtered TargetFilter.creature), maxTargets := n
          allowsZeroTargets := true, resolution := .tapAndStunPerOpponent
          phrase := "Tap up to that many target creatures and put a stun counter on each of them" }
        (deferToPriority := true)
  | 47 =>
    match cardId.bind (fun id => g.followMovedToZone? id (· == .battlefield)) with
    | some o =>
      if (g.baseCard o).otherFace.isSome && !g.cantTransform o then
        g.beginFraChoice p (.nickFuryMayTransform o.id ids)
          s!"{(g.player p).name} may transform {g.name o}"
      else g.putRestOnBottomRandom p ids (cause := cause)
    | none => g.putRestOnBottomRandom p ids (cause := cause)
  | 48 =>
    g.changes #[.handDiscardedThisWay (some n), .notedSourceThisWay sourceId]
  | 49 =>
    if g.loggedDraws p == n then g
    else
      let (g, oppCause?) : Game × Option EventCause :=
        match g.currentResolvingContext? with
        | some (src, ctrl) =>
          let (g, c) := g.allocDelayedCause (ctrl.orElse (fun _ => some p)) src
          (g, some c)
        | none => (g, none)
      let opps := (g.livingOpponents p).map (·.id.idx)
      g.runPostStep 50 p (modes := opps) (cause := oppCause?)
  | 50 =>
    match modes[0]? with
    | none =>
      g.logMsg s!"{(g.player p).name} draws, so each opponent draws a card"
    | some oppIdx =>
      let rest := modes.extract 1 modes.size
      let g := g.draw ⟨oppIdx⟩ 1 (cause := cause)
      if let .chooseReplacement .. := g.pending then
        g.chainPendingReplacement (.finishPostStep 50 p (modes := rest) (cause := cause))
      else
        g.runPostStep 50 p (modes := rest) (cause := cause)
  | 51 =>
    let milled := ids.filterMap (fun id => g.followMilledPublic? id)
    let mv := milled.foldl (fun acc o => acc + g.objectManaValue o) 0
    g.loseLife p mv (cause := cause)
  | 52 =>
    Id.run do
      if let .chooseReplacement .. := g.pending then
        return g.chainPendingReplacement
          (.finishPostStep 52 p (n := n) (sourceId := sourceId) (ids := ids) (cause := cause))
      let mut g := g
      let mut count := n
      for i in [0:ids.size] do
        let id := ids[i]!
        match g.findObject? id with
        | some o =>
          if o.isOnBattlefield && g.isCreature o && o.owner == p then
            let name := g.name o
            let owner := o.owner
            let (g', _) := g.move o.id (.hand owner) none (cause := cause)
            g := g'.logMsg s!"{name} is returned to {(g'.player owner).name}'s hand"
            count := count + 1
            if let .chooseReplacement .. := g.pending then
              let rem := ids.extract (i + 1) ids.size
              return g.chainPendingReplacement
                (.finishPostStep 52 p (n := count) (sourceId := sourceId) (ids := rem) (cause := cause))
        | none => pure ()
      if count > 0 then
        let src := sourceId.bind g.damageSourceById?
        g := g.registerDelayedTrigger
          { controller := p, source := src, kind := .eaglesBirds count
            cause := cause.getD (.gameRule .spellCast) }
        g := g.logMsg
          s!"At the beginning of the next upkeep, {count} Bird Soldier token(s) will be created"
      return g
  | 53 =>
    match sourceId.bind g.findObject? with
    | some src => if src.isOnBattlefield then g.addPlusOnePlusOneTo src n else g
    | none => g
  | 54 =>
    let ps : Array PlayerId := modes.map (⟨·⟩)
    if n == 0 then g.beginDiscardCards ps
    else g.continueAfterDiscard ps
  | 55 =>
    g.discardHandIdsLoop p ids (logEach := n != 0) (cause := cause)
  | 56 =>
    match sourceId.bind g.findObject? with
    | some src =>
      if src.isOnBattlefield then
        (g.logMsg s!"{g.name src} gets an influence counter").beginScry (g.you src) 2
      else g
    | none => g
  | 57 =>
    let g :=
      match sourceId.bind g.findObject? with
      | some src =>
        if src.isOnBattlefield then g.logMsg s!"{g.name src} gets an influence counter" else g
      | none => g
    let after := ((sourceId.bind g.findObject?).map (·.status.influence)).getD n
    match targets[0]?, sourceId with
    | some (Target.player opp), some sid =>
      if after > n then g.change (.palantirChoiceReady (some (p, opp, sid))) else g
    | _, _ => g
  | 58 =>
    let milled := ids.filterMap (fun id => (g.followMilledPublic? id).map (·.id))
    g.change (.milledIdsThisWay milled)
  | 59 =>
    let opps := targets.filterMap (fun | Target.player pid => some pid | _ => none)
    g.change (.opponentsMilledThisWay (g.anyOpponentMilledSince opps n))
  | 60 =>
    g.logMsg s!"{(g.player p).name} creates two tapped and attacking Spirit tokens"
  | 61 =>
    let exiled := ids.filterMap (fun id =>
      if g.wasPermanentExiled id n then
        (g.followMovedToZone? id (· == .exile)).map (·.id)
      else none)
    let order := let apnap := g.apnapOrder; if apnap.isEmpty then #[p] else apnap
    g.offerWorldsCreatures order.toList exiled #[] sourceId
  | 62 =>
    let oName := (cardId.bind g.lastKnownBefore?).map (·.name) |>.getD "The permanent"
    g.finishIdentityEchoAfterExile p sourceId oName
  | 63 =>
    let oName := (cardId.bind g.lastKnownBefore?).map (·.name) |>.getD "it"
    (g.logMsg s!"{(g.player p).name} shuffles {oName} into their library").shuffleThen p .none
  | 64 =>
    let count := ids.foldl (fun acc id => if g.wasPermanentExiled id n then acc + 1 else acc) 0
    g.empowerJace p count
  | 65 =>
    g.applyFra p default .reflexiveReturnLandTapped #[] sourceId
  | 66 =>
    let choices := ids.filterMap (fun id =>
      match g.followMilledPublic? id with
      | some o => if g.isPermanentCard o then some o.id else none
      | none => none)
    if choices.isEmpty then g.gainLife p n
    else
      g.beginFraChoice p (.mayPutMilledPermanent choices n)
        s!"{(g.player p).name} may put a permanent card milled this way into their hand"
  | 67 =>
    g.finishWorldsWithinWorlds ids (targets.filterMap (fun | Target.card id => some id | _ => none)) sourceId
  | 68 =>
    g.finishMillMayPutPermanentGainLife p ids n
  | 69 =>
    let count := ids.foldl (fun acc id => if g.wasPermanentExiled id n then acc + 1 else acc) 0
    g.offerMaySearchBasics p count
  | 70 =>
    let g :=
      match cardId.bind (fun id => g.followMovedToZone? id (· == .battlefield)) with
      | some entered =>
        (g.logMsg s!"{g.name entered} enters the battlefield").afterPermanentEnters entered
      | none => g
    g.putRestOnBottomRandom ⟨n⟩ ids (cause := cause)
  | 71 =>
    g.finishCreatedTokenNote p n sourceId modes
  | 72 =>
    let exiled := ids.filterMap (fun id => (g.followMovedToZone? id (· == .exile)).map (·.id))
    g.change (.exiledIdsThisWay exiled)
  | 73 =>
    match cardId.bind (fun id => g.followMovedToZone? id (· == .battlefield)) with
    | some entered =>
      (g.logMsg s!"{entered.name} returns to the battlefield").afterPermanentEnters entered
    | none => g
  | 74 =>
    match cardId.bind (fun id => g.followMovedToZone? id (· == .battlefield)) with
    | some entered =>
      (g.logMsg s!"{entered.name} is put onto the battlefield under its owner's control").afterPermanentEnters entered
    | none => g
  | 75 =>
    match cardId.bind (fun id => g.followMovedToZone? id (· == .battlefield)) with
    | some entered =>
      (g.logMsg s!"{entered.name} is exiled, then returned tapped").afterLandEnters entered
    | none => g
  | 76 =>
    g.returnNotedLandsStep ids
  | 77 =>
    g.putRestOnBottomRandom p ids (cause := cause)
  | _ => g

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
      let g := (g.change (.consecutivePasses 0)).chainPendingReplacement
        (.restorePending nextPending)
      return g.logMsg s!"{(g.player prop.caster).name} chooses how to {pick.phrase}"
    else if (g.costPickCandidates prop.caster sid pick).size < pick.count then
      g.reverseProposedSpell? (resumeContinuation := true)
    else
      let g := g.changes #[.pending (.fraChoice prop.caster (.costPicks sid picks paid)), .consecutivePasses 0]
      return g.logMsg s!"{(g.player prop.caster).name} chooses how to {pick.phrase}"
  | _, _ =>
    if let .chooseReplacement .. := g.pending then
      return (g.change (.consecutivePasses 0)).chainPendingReplacement
        (.completeActivation hadOuterReplacement openCont)
    else
      g.completeActivation prop
        (hadOuterReplacement := hadOuterReplacement)
        (hadOpenContinuation := some openCont)

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
    let g := g.logMsg s!"{(g.player p).name} puts {card.name} into their graveyard (surveil)"
    if let .chooseReplacement .. := g.pending then
      g.chainPendingReplacement (.finishSurveilPostMove p card id rest cause)
    else
      g.finishSurveilPostMove p card id rest cause

/-- Run post-graveyard-move surveil-to-hand checks and continue `surveilMoveLoop`. -/
partial def finishSurveilPostMove (g : Game) (p : PlayerId) (card : GameObject)
    (fromId : ObjectId) (remainingGy : Array ObjectId) (cause : Option EventCause) : Game :=
  let g :=
    match g.followMovedToZone? fromId (· == Zone.graveyard p) with
    | none => g
    | some gyObj =>
      match g.surveilReturnMvAtMost with
      | some n =>
        if g.objectManaValue card ≤ n then
          let (g', _) := g.move gyObj.id (.hand p) none (cause := cause)
          g'.logMsg s!"{(g.player p).name} puts {card.name} into their hand"
        else g
      | none =>
        if g.surveilReturnNoncreatureNonland && !g.isCreature card && !g.isLand card then
          let (g', _) := g.move gyObj.id (.hand p) none (cause := cause)
          g'.logMsg s!"{(g.player p).name} puts {card.name} into their hand"
        else g
  if let .chooseReplacement .. := g.pending then
    if remainingGy.isEmpty then g
    else g.chainPendingReplacement (.finishSurveilPostMove p card noSourceSentinelId remainingGy cause)
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
    let g := g.record (GameEvent.poisoned g.turnNumber pid 1 (byPlayer := some p) (cause := effCause))
    let g := g.logMsg s!"{(g.player p).name} gives {pl.name} another poison counter"
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
      if let .chooseReplacement .. := g.pending then g
      else g.change (.pending .none)
    else if let .chooseReplacement .. := g.pending then
      g.chainPendingReplacement (.finishPostStep 54 p (n := 0) (modes := #[p.idx]))
    else
      g.beginDiscardCards #[p]
  else if g.pendingDiscardsLeft > 0 then
    let left := g.pendingDiscardsLeft - 1
    let g := g.change (.pendingDiscardsLeft left)
    let next := if left == 0 then remaining else #[p]
    if let .chooseReplacement .. := g.pending then
      g.chainPendingReplacement (.finishPostStep 54 p (n := 1) (modes := next.map (·.idx)))
    else
      g.continueAfterDiscard next
  else if let .chooseReplacement .. := g.pending then
    g.chainPendingReplacement (.finishPostStep 54 p (n := 1) (modes := remaining.map (·.idx)))
  else
    g.continueAfterDiscard remaining

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
  let needsKicker :=
    !prop.kickerAnnounced &&
      (face.kicker.isSome || (!prop.alternativeCost && (face.morph.isSome || face.impending.isSome)))
  if prop.cost.containsX then
    g.change (.pending (.chooseX p))
      |>.logMsg s!"{(g.player p).name} must choose a value for X (CR 107.3a / 601.2b)"
  else if face.isModal then
    if !face.spellModes.any (g.spellModeIsChoosable p) && !face.allowsZeroTargets then
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
    if (g.legalCastTargets p face).isEmpty && !face.allowsZeroTargets then
      g.reverseProposedSpell (resumeContinuation := true)
        (extraLog := some s!"{face.name} has no legal target and can't be cast")
    else
      let what := if g.isAura spell then "a target to enchant" else "a target"
      g.change (.pending (.chooseTargets p))
        |>.logMsg s!"{(g.player p).name} must choose {what} (CR 601.2c)"
  else if prop.cost.includesManaPayment || prop.needsSacrificeOther || prop.needsDiscardCard then
    g.change (.pending (.activateManaAbilities p))
      |>.logMsg s!"{(g.player p).name} may activate mana abilities (CR 601.2g)"
  else
    let outerCont? := g.pendingReplacement
    let openCont := g.proposalHadOpenContinuation
    let g0 := if outerCont?.isSome then g.change (.pendingReplacement none) else g
    match g0.tapTeamworkCreaturesForProposed prop with
    | .error _ => g.reverseProposedSpell (resumeContinuation := true)
    | .ok g =>
      let paused := match g.pending with | .chooseReplacement .. => true | _ => false
      let g :=
        if !paused then
          match outerCont? with
          | some outer => g.chainPendingReplacement outer
          | none => g
        else g
      let clearPending : Array EngineChange := if paused then #[] else #[.pending .none]
      let g := g.changes (clearPending ++ #[.proposedSpell none])
      let g := g.becomeCast p (g.object! prop.spellId) (grantPriority := false)
        (hadOuterReplacement := outerCont?.isSome)
        (hadOpenContinuation := some openCont)
      if paused then
        match outerCont? with
        | some outer => g.chainPendingReplacement outer.ensureEndsWithFinishFra
        | none => g.chainPendingReplacement .finishFraChoice
      else g

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
    if g.splitSecondOnStack then
      (clearCkpt g).logMsg s!"{o.name} can't be cast while a spell with split second is on the stack (ruling 839)"
    else if !ignoreTiming && !g.timingAllowsCast p face then
      (clearCkpt g).logMsg s!"{o.name} cannot be cast now (timing)"
    else
      let name := o.name
      let original := o
      let origSnap := g.snapshot o
      let fromGy := original.zone == .graveyard original.owner
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
        if withoutManaCost then .alternative "withoutManaCost" else .normal
      let g := g.record (GameEvent.proposed g.turnNumber newId p original.zone way)
      let g := g.logMsg s!"{(g.player p).name} casts {name} as the ability resolves"
      let cost :=
        if withoutManaCost then ManaCost.empty else g.playManaCost spellObj stackFace
      let needsSacrifice :=
        stackFace.additionalCostSacrificeCreature ||
          (stackFace.additionalCostSacrificeArtifactOrCreature && stackFace.additionalCostOrPayGeneric.isNone)
      g.beginResolutionCastTargets p {
        caster := p
        cost
        spellId := newId
        original
        originalSnapshot := origSnap
        needsSacrificeOther := needsSacrifice
        alternativeCost := withoutManaCost
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
end

/-- After the Cosmic Cube choice, put unchosen looked-at cards on the bottom
in a random order, then resume active continuations or grant priority unless
another choice is pending (for example choosing a target for an Aura just cast). -/
def finishMayCastFromLooked (g : Game) (p : PlayerId) (rest : Array ObjectId) :
    Game :=
  let rest :=
    rest.filter (fun id =>
      match g.findObject? id with
      | some o => o.zone == .library p
      | none => false)
  let msg :=
    s!"{(g.player p).name} puts the rest on the bottom of their library in a random order"
  let g :=
    if rest.isEmpty then g
    else g.requestOrderInto rest (.library p) msg
  if g.pending != .none then g
  else g.finishFraChoice

/-- Cast one looked-at card as Cosmic Cube resolves, or decline (`none`). -/
def chooseCastFromLooked (g : Game) (p : PlayerId) (castId : Option ObjectId) :
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
        let g :=
          if g.continuations.isEmpty then g.change (.pushContinuationFrame {}) else g
        let g := g.changes #[
          .postCastCleanup (some (.lookedBottom p id ids)),
          .pending .none,
          .saveProposalCheckpoint
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
def afterTriggerTargetsChosen (g : Game) : Game :=
  match g.triggerNeedingTargets with
  | some _ =>
    promptTriggerTargetsIfNeeded (g.change (.pending .none))
  | none =>
    let prio := g.pendingPriority.getD g.activePlayer
    receivePriority (g.change (.pending .none)) prio false

/-- Start paying the proposed activation's costs that need chosen objects,
reversing it if they can't be paid (CR 601.2h / 733.1). -/
def beginActivationPayment (g : Game) (prop : ProposedSpell) : Except String Game := do
  let picks := (prop.activation.map costPicksOf).getD #[]
  let payable :=
    match prop.sourceId with
    | some sid => g.costPicksPayable prop.caster sid picks
    | none => true
  if !payable then return (← g.reverseProposedSpell? (resumeContinuation := true))
  let g ← g.continueCostPicks prop picks false
  if g.proposedSpell.isNone && !(g.findObject? prop.spellId).any (·.zone == .stack) then
    return g
  return g.resumeAfterBecomeCast

/-- Continue after CR 601.2c: determine the total cost (601.2f), then mana
abilities (601.2g). Additional-cost *choices* are announced earlier, at 601.2b. -/
def afterTargetsChosen (g : Game) : Game :=
  match g.proposedSpell with
  | none => g
  | some _ =>
    let g := g.lockInTargetCostReduction
    match g.proposedSpell with
    | none => g
    | some prop =>
      if prop.cost.includesManaPayment || prop.needsSacrificeOther ||
          prop.needsDiscardCard then
        (g.change (.pending (.activateManaAbilities prop.caster))).logMsg
          s!"{(g.player prop.caster).name} may activate mana abilities (CR 601.2g)"
      else if prop.kind == .activatedAbility then
        match g.beginActivationPayment prop with
        | .ok g => g
        | .error _ => g.reverseProposedSpell (resumeContinuation := true)
      else
        let isResCast := prop.resolutionCast
        let outerCont? := g.pendingReplacement
        let openCont := g.proposalHadOpenContinuation
        let g0 := if outerCont?.isSome then g.change (.pendingReplacement none) else g
        match g0.tapTeamworkCreaturesForProposed prop with
        | .error _ => g.reverseProposedSpell (resumeContinuation := true)
        | .ok g =>
          let paused := match g.pending with | .chooseReplacement .. => true | _ => false
          let g :=
            if !paused then
              match outerCont? with
              | some outer => g.chainPendingReplacement outer
              | none => g
            else g
          let clearPending : Array EngineChange := if paused then #[] else #[.pending .none]
          let spell := g.object! prop.spellId
          let g := g.changes (clearPending ++ #[.proposedSpell none, .consecutivePasses 0])
          let g := g.becomeCast prop.caster spell (grantPriority := !isResCast)
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
                g.pendingReplacement.any (·.endsWithFinishFra) then g
            else g.finishFraChoice
          else g.resumeAfterBecomeCast

/-- After CR 601.2b additional-cost announcement, continue through optional
costs (kicker, gift, teamwork), then targets (601.2c) or cost determination (601.2f). -/
def afterAdditionalCostAnnounced (g : Game) : Game :=
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
      if prop.resolutionCast &&
          (g.legalCastTargets p face).isEmpty && !face.allowsZeroTargets then
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
def afterModesChosen (g : Game) (p : PlayerId) : Game :=
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
    return g.afterOptionalAdditionalCost p
  | _ => throw "Not time to announce kicker"

def announceGift (g : Game) (p : PlayerId) (to : Option PlayerId) : Except String Game := do
  match g.pending with
  | .chooseGift caster =>
    if caster != p then
      throw s!"Only {(g.player caster).name} may promise a gift"
    if let some opp := to then
      if opp == p then throw "You must promise the gift to an opponent"
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
    if face.chooseBothIfTeamwork then
      let chosen := g.chosenModesOf spell
      for i in [0:face.spellModes.size] do
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
        if pl.poison == 0 then
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
  let g := (g.change (.pending .none)).logMsg s!"{(g.player p).name} discards {card.name}{logSuffix}"
  let (g, _) := g.move id (.graveyard card.owner) none (verb := some .discard)
    (actor := some p) (cause := cause)
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
    let g :=
      match outerCont? with
      | some outer => g.chainPendingReplacement outer
      | none => g
    return g.finishAndGrantPriority
  | .maySacArtifactOrDiscard q n =>
    let outerCont? := g.pendingReplacement
    let g0 := if outerCont?.isSome then g.change (.pendingReplacement none) else g
    let (g, _) ← g0.discardPendingCard p q id
    let g := g.finishSacArtifactOrDiscardDraw p n
    let g :=
      match outerCont? with
      | some outer => g.chainPendingReplacement outer
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
    let (g, _) ← g.discardPendingCard p q id (logSuffix := " (ward)")
      (cause := some (.costPayment .ward p (some spellId)))
    return g.afterWardResolved
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
    let g ← g.payCost p (ManaCost.ofGeneric n)
    let g := g.logMsg s!"{(g.player p).name} pays \{{n}}"
    if g.mayThenDrop > 0 then
      let g := (g.change (.mayPayAlsoPlusOneOn none)).acceptMayThenCore
      let g :=
        match outerCont? with
        | some outer => g.chainPendingReplacement outer
        | none => g
      return g.finishAndGrantPriority
    else
      let g := g.change (.pending .none)
      let g :=
        match g.mayPayAlsoPlusOneOn.bind g.findObject? with
        | some o => if o.isOnBattlefield then g.addPlusOnePlusOneTo o 1 else g
        | none => g
      let g := g.change (.mayPayAlsoPlusOneOn none)
      let g := g.draw p 1
      let g :=
        match outerCont? with
        | some outer => g.chainPendingReplacement outer
        | none => g
      return g.finishAndGrantPriority
  | .payOrLetCounter q n _spellId =>
    if p != q then
      throw s!"Only {(g.player q).name} may pay \{{n}}"
    if !(g.player p).manaPool.canPay (ManaCost.ofGeneric n) then
      throw s!"{(g.player p).name} cannot pay \{{n}}"
    let outerCont? := g.pendingReplacement
    let g := if outerCont?.isSome then g.change (.pendingReplacement none) else g
    let g ← g.payCost p (ManaCost.ofGeneric n)
    let g := g.logMsg s!"{(g.player p).name} pays \{{n}}"
    let g := (g.change (.pending .none)).clearUnlessPays
    let g :=
      match outerCont? with
      | some outer => g.chainPendingReplacement outer
      | none => g
    return g.finishAndGrantPriority
  | .payWard q spellId (.genericMana n) | .payWard q spellId (.discardOrPay n) =>
    if p != q then
      throw s!"Only {(g.player q).name} may pay ward"
    if !(g.player p).manaPool.canPay (ManaCost.ofGeneric n) then
      throw s!"{(g.player p).name} cannot pay \{{n}}"
    let g ← g.payCost p (ManaCost.ofGeneric n) (forObject := some spellId)
    let g := g.logMsg s!"{(g.player p).name} pays \{{n}} (ward)"
    return g.afterWardResolved
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
      let g := (g.change (.pending .none)).clearMay
      let g := g.applyUnified controller effect targets
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
  | .chooseLibraryPlacement q id =>
    if p != q then
      let what := if g.spellOrLibrary then "top or bottom" else "an effect"
      throw s!"Only {(g.player q).name} may choose {what}"
    if idx >= g.spellOr.size then
      throw "No such choice"
    if g.spellOrLibrary then
      let some o := g.findObject? id | throw "no such object"
      if !o.isOnBattlefield then
        throw s!"{o.name} is no longer on the battlefield"
    let outerCont? := g.pendingReplacement
    let g := if outerCont?.isSome then g.change (.pendingReplacement none) else g
    let effect := g.spellOr[idx]!
    let controller := g.spellOrController
    let targets := g.spellOrTargets
    let g := (g.change (.pending .none)).clearSpellOr
    let g := g.applyUnified controller effect targets
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
    | .chooseLibraryPlacement q id =>
      if p != q then
        throw s!"Only {(g.player q).name} may choose top or bottom"
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
  | .mayAttachEquipment q hostId =>
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
    let outerCont? := g.pendingReplacement
    let g := if outerCont?.isSome then g.change (.pendingReplacement none) else g
    let g := (g.change (.pending .none)).attachSourceTo eq host
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
    if g.isLand card then
      throw "An effect that lets you cast a card doesn't let you play a land (ruling 855)"
    if face.isModal && !face.spellModes.any (g.spellModeIsChoosable p) && !face.allowsZeroTargets then
      throw s!"{face.name} has no mode with a legal target"
    if !face.isModal && (face.requiresTarget || face.isAura) &&
        (g.legalCastTargets p face).isEmpty && !face.allowsZeroTargets then
      throw s!"{face.name} requires a target"
    let g := (g.change .saveProposalCheckpoint).change (.pending .none)
    let (g, newId) := g.move id .stack (some p) (verb := some .cast) (actor := some p)
      (cause := some (.gameRule .spellCast))
    let spellObj := g.object! newId
    let stackFace := g.baseCard spellObj
    let g := g.putStackEntry p newId
    let g := g.record (GameEvent.proposed g.turnNumber newId p card.zone
      (.alternative "permission"))
    let g := g.logMsg s!"{(g.player p).name} casts {stackFace.name} as the ability resolves"
    let cost := g.playManaCost spellObj stackFace
    let needsSacrifice :=
      stackFace.additionalCostSacrificeCreature ||
        (stackFace.additionalCostSacrificeArtifactOrCreature && stackFace.additionalCostOrPayGeneric.isNone)
    let prop : ProposedSpell := {
      caster := p
      cost
      spellId := newId
      original := card
      originalSnapshot := origSnap
      needsSacrificeOther := needsSacrifice
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
      if (g.chosenModesOf spell).isEmpty then throw "Choose a mode (CR 700.2)"
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
    let g := (g.change (.mayPayAlsoPlusOneOn none)).logMsg s!"{(g.player p).name} declines to pay"
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
    let g := (g.change (.pending .none)).clearUnlessPays
    let g :=
      match instead with
      | some effect => g.applyUnified caster effect targets
      | none => g.counterStackSpell spellId (controller := some caster)
    let g :=
      match outerCont? with
      | some outer => g.chainPendingReplacement outer
      | none => g
    return g.finishAndGrantPriority
  | .payWard _ _ (.sacrificePermanents _ (_ + 1)) =>
    throw s!"{(g.player p).name} already began sacrificing permanents for ward and must finish"
  | .payWard q spellId _ =>
    if p != q then
      throw s!"Only {(g.player q).name} may decline to pay ward"
    let g := g.logMsg s!"{(g.player p).name} does not pay ward"
    let wardCtrl := (g.resolvingAbilityObject?.bind (·.controller)).getD (g.opponent p)
    let g := g.counterStackSpell spellId (controller := some wardCtrl)
    return g.afterWardResolved
  | .mayAttachEquipment q _ =>
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
      throw s!"{kept.name} is not on the battlefield"
    let outerCont? := g.pendingReplacement
    let g := if outerCont?.isSome then g.change (.pendingReplacement none) else g
    let others := ids.filter (· != id)
    let sweepPreBf? : Option (Array GameObject) :=
      match outerCont? with
      | some (.finishSbaSweep _ pbf ..)
      | some (.seq (.finishSbaSweep _ pbf ..) _) => some pbf
      | _ => none
    let preBf := sweepPreBf?.getD g.battlefield
    let g := (g.change (.pending .none) |>.logMsg
      s!"{(g.player p).name} keeps {kept.name} (legend rule, CR 704.5j)").withBatch
      (some (.stateBased .legendRule)) fun g => Id.run do
        let mut g := g
        for i in [0:others.size] do
          let other := others[i]!
          match g.findObject? other with
          | some o =>
            if o.isOnBattlefield then
              g := g.moveToOwnerGraveyard o
                s!"{o.name} is put into its owner's graveyard (legend rule, CR 704.5j)"
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

/-- CR 103.3: shuffle remaining libraries, then draw opening hands. -/
partial def continueOpeningShuffles (g : Game) (next : Nat) : Game :=
  if next >= g.players.size then
    Id.run do
      let mut g := g.changes #[.pregameRandom .none, .pending .none]
      for pl in g.players do
        g := g.draw pl.id (g.player pl.id).startingHandSize
          (cause := some (.gameRule .openingHandDraw))
      return g.beginMulliganRound
  else
    let p : PlayerId := ⟨next⟩
    let g := (g.change (.pregameRandom (.openingShuffles (next + 1)))).shuffleLibrary p
    match g.pendingRandom? with
    | some _ => g
    | none =>
      let g := g.change (.pregameRandom .none)
      continueOpeningShuffles g (next + 1)

/-- Finish an in-game `--norandom` result after re-attaching any outer
`g.pendingReplacement` continuation: drain active continuations, chain
`.receivePriority` on a CR 616.1 pause, or grant priority and complete active
resolutions when idle. -/
def finishHostRandom (g : Game) : Game :=
  if !g.openingHandsPending && !g.over && !g.players.isEmpty &&
      g.afterRandom == .none && g.pendingRandom?.isNone then
    let g := g.finishAndGrantPriority
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
      g.draw p n (cause := some (.gameRule .mulligan))
    | .mulliganQueue p rest =>
      let g := g.draw p (g.player p).startingHandSize
        (cause := some (.gameRule .mulligan))
      executeMulliganQueue g rest
    | .setStartingPlayer i =>
      let n := g.players.size
      let i := if n == 0 then 0 else i % n
      let sp : PlayerId := ⟨i⟩
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
      | .plusOne id => g.addPlusOneIfStillCreature id
      | .discardRandom p =>
        let hand := (g.player p).hand
        if hand.isEmpty then g
        else if hand.size == 1 then g.discardFromHandRandomly p hand[0]!
        else g.changes #[.pending (.resolveRandom (.chooseObject hand)), .afterRandom (.discardRandom p)]
    if grantPriority then g.finishHostRandom else g

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
    if !choices.contains id && !validOpenPrompt then
      throw "Replacement effect is not among the applicable choices"
    let chooser := id.player.getD q
    let g ←
      match id.kind with
      | .entersUntappedPayLife n =>
        g.payLifeCost chooser n (forObject := id.object)
      | .entersUntappedBehold beholdId subtype =>
        let okPerm :=
          (g.findObject? beholdId).any (fun o =>
            o.isOnBattlefield && g.controlledBy o chooser && g.hasSubtype o subtype)
        let okHand :=
          (g.player chooser).hand.contains beholdId &&
            (g.findObject? beholdId).any (fun o => g.hasSubtype o subtype)
        if !okPerm && !okHand then
          throw s!"{(g.player chooser).name} cannot behold that {subtype}"
        let cause := EventCause.costPayment .behold chooser id.object
        let g :=
          if okHand then
            g.record (GameEvent.revealed g.turnNumber chooser #[beholdId] (cause := some cause))
          else g
        let g := g.record (GameEvent.beheld g.turnNumber chooser subtype (cause := cause))
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
      | _ => pure g
    let order := (g.replacementOrder.filter (· != id)).push id
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
