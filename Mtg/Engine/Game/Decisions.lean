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

mutual
/-- Clear a finished Reality Fracture choice and let the game continue. Any
pending replacement/batch continuation runs first, then pending exile-cast
queues and a paused trigger sequence run their remaining steps. -/
partial def finishFraChoice (g : Game) : Game :=
  if let .chooseReplacement .. := g.pending then
    g.chainPendingReplacement .finishFraChoice
  else if g.pending != .none then g
  else
    let g :=
      match g.pendingReplacement with
      | some cont =>
        let g := g.change (.pendingReplacement none)
        g.resumePendingReplacement cont
      | none => g
    if let .chooseReplacement .. := g.pending then
      g.chainPendingReplacement .finishFraChoice
    else if g.pending != .none then g
    else
      let g := g.advanceCastExiledQueue
      if let .chooseReplacement .. := g.pending then
        g.chainPendingReplacement .finishFraChoice
      else if g.pending != .none then g
      else
        let g := g.resumeTriggerSequence
        if let .chooseReplacement .. := g.pending then
          g.chainPendingReplacement .finishFraChoice
        else if g.pending != .none then g
        else
          let g := g.promptTriggerTargetsIfNeeded
          if g.pending == .none then g.receivePriority g.activePlayer else g

/-- Resume the rules event that paused on `Pending.chooseReplacement` (CR 616.1). -/
partial def resumePendingReplacement (g : Game) : PendingReplacement → Game
  | .seq first rest =>
    let g := g.resumePendingReplacement first
    if g.pending != .none then
      g.chainPendingReplacement rest
    else
      g.resumePendingReplacement rest
  | .shuffleThen p onDone =>
    g.shuffleThen p onDone
  | .dealDamageToPlayer p n _ source _ unpreventable cause =>
    let srcObj := g.damageSourceObjFromSnapshot? source
    g.dealDamageToPlayer p (Int.ofNat n) (preventable := !unpreventable)
      (source := srcObj) (sourceSnap := source) (cause := cause)
  | .dealDamageToPlayers players n source cause =>
    let srcObj := g.damageSourceObjFromSnapshot? source
    g.dealDamageToPlayers players (Int.ofNat n) (source := srcObj) (sourceSnap := source)
      (cause := cause)
  | .dealDamageFrom sourceName source targetId n deathtouch _ _ cause =>
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
  | .dealDamageToPermanent targetId n source _ _ cause =>
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
  | .gainLife p n _ cause =>
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
  | .move id dest controller _ _ verb actor _ tapped
      attacking attackingTarget transformed returnedAsArtifact onlyFoodArtifact
      extraEntersWith libraryPosition _ applyHope preBattlefield
      isCopy overridePrinted adventurerCard cause =>
    (g.move id dest controller (tapped := tapped) (applyHope := applyHope)
      (attacking := attacking) (attackingTarget := attackingTarget)
      (returnedAsArtifact := returnedAsArtifact) (onlyFoodArtifact := onlyFoodArtifact)
      (nightBack := transformed) (extraEntersWith := extraEntersWith)
      (verb := verb) (actor := actor) (libraryPosition := libraryPosition)
      (preBattlefield := preBattlefield) (isCopy := isCopy)
      (overridePrinted := overridePrinted) (adventurerCard := adventurerCard)
      (cause := cause)).1
  | .moveSimultaneousToGraveyard ids preBattlefield cause =>
    g.moveSimultaneousToGraveyard ids (preBattlefield := preBattlefield) (cause := cause)
  | .destroyPermanent targetId cause =>
    match g.findObject? targetId with
    | some tgt => g.destroyPermanent tgt (cause := cause)
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
  | .createAndMarkTokensAttacking controller kind n tapped holds sourceId =>
    g.createAndMarkTokensAttacking controller kind n tapped holds (sourceId := sourceId)
  | .commitEnteringAttackItems chosen cause resetRecent =>
    g.commitEnteringAttackItems chosen (cause := cause) (resetRecent := resetRecent)
  | .finishEnteringAttackCard newId? effectController cardName mods logKind cause =>
    let target? :=
      match newId? with
      | some id => g.findObject? id
      | none => g.objects.back?
    match target? with
    | some entered =>
      if entered.isOnBattlefield then
        g.finishEnteringAttackCard entered.id effectController cardName mods logKind (cause := cause)
      else g
    | none => g
  | .afterLastPermanentEnters fromId isPlayLand =>
    let target? :=
      (fromId.map g.followMoved |>.bind g.findObject?).orElse (fun _ => g.objects.back?)
    match target? with
    | some entered =>
      if entered.isOnBattlefield then
        if isPlayLand then
          let g := if entered.status.tapped then g.logMsg s!"{entered.name} enters tapped" else g
          g.afterLandEnters entered
        else
          let g := g.logMsg s!"{entered.name} enters the battlefield"
          g.afterPermanentEnters entered
      else g
    | none => g
  | .addExtraCombatDamageStep =>
    g.record (GameEvent.extraStepAdded g.turnNumber .combatDamage .afterCurrent
      (cause := .gameRule .stepAdvance))
  | .finishFraChoice =>
    g.finishFraChoice
  | .draw p n _ cause =>
    g.draw p n (cause := cause)
  | .drawOne p applied drawStepFirst cause =>
    g.drawOneWithReplacements p (applied := applied)
      (firstOfYourDrawStep? := some drawStepFirst) (cause := cause)
  | .drawSubDraws p remaining applied cause =>
    g.drawSubDraws p remaining applied (cause := cause)
  | .connive controller sourceId =>
    g.applyConnive controller sourceId
  | .finishSbaSweep moves preBattlefield stage =>
    (g.finishSbaSweep moves preBattlefield stage).1
  | .untapPermanent targetId cause =>
    match g.findObject? targetId with
    | some tgt => g.untapPermanent tgt (cause := cause)
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
  | .finishArtifactCopyToken _ =>
    g.finishArtifactCopyTokens
  | .finishManaAbilityMountainTrigger player sourceId =>
    g.finishManaAbilityMountainTrigger player sourceId
  | .restorePending p =>
    let g := if g.proposalCheckpoint.isSome then g.change .endProposalAction else g
    g.change (.pending p)
  | .closeBatch batchId startIdx =>
    g.finishOpenBatch batchId startIdx
  | .checkSBA =>
    g.checkSBA
  | .receivePriority p =>
    let g := if g.pending == .none then g.resumeTriggerSequence else g
    if let .chooseReplacement .. := g.pending then
      g.chainPendingReplacement (.receivePriority p)
    else if g.pending != .none then g
    else g.receivePriority p

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

/-- Announce the modes and targets of a spell cast while an ability resolves
(CR 601.2b–c), then finish casting it. A spell that needs a target but has
none can't be cast and returns to where it was (CR 601.2c / 733.1). -/
partial def beginResolutionCastTargets (g : Game) (p : PlayerId) (prop : ProposedSpell) :
    Game :=
  let face := g.baseCard prop.original
  let g := g.change (.proposedSpell (some prop))
  if face.isModal then
    if !face.spellModes.any (g.spellModeIsChoosable p) && !face.allowsZeroTargets then
      g.reverseProposedSpell (resumeContinuation := true)
    else
      g.change (.pending (.chooseMode p))
        |>.logMsg s!"{(g.player p).name} must choose a mode (CR 601.2b)"
  else if face.announcesAdditionalCost then
    g.change (.pending (.chooseAdditionalCost p))
      |>.logMsg s!"{(g.player p).name} must choose an additional cost (CR 601.2b)"
  else if face.requiresTarget || face.isAura then
    if (g.legalCastTargets p face).isEmpty && !face.allowsZeroTargets then
      g.reverseProposedSpell (resumeContinuation := true)
        (extraLog := some s!"{face.name} has no legal target and can't be cast")
    else
      let what := if face.isAura then "a target to enchant" else "a target"
      g.change (.pending (.chooseTargets p))
        |>.logMsg s!"{(g.player p).name} must choose {what} (CR 601.2c)"
  else if prop.cost.includesManaPayment || prop.needsSacrificeOther || prop.needsDiscardCard then
    g.change (.pending (.activateManaAbilities p))
      |>.logMsg s!"{(g.player p).name} may activate mana abilities (CR 601.2g)"
  else
    let g := g.change (.proposedSpell none)
    g.becomeCast p (g.object! prop.spellId) (grantPriority := false)

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
    else if !withoutManaCost &&
        !(g.player p).manaPool.canPay (g.playManaCost o face) then
      (clearCkpt g).logMsg s!"{o.name} cannot be cast (costs)"
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
      let g := g.putStackEntry p newId
      let way : CastWay :=
        if withoutManaCost then .alternative "withoutManaCost" else .normal
      let g := g.record (GameEvent.proposed g.turnNumber newId p original.zone way)
      let g := g.logMsg s!"{(g.player p).name} casts {name} as the ability resolves"
      let cost :=
        if withoutManaCost then ManaCost.empty else g.playManaCost original face
      let needsSacrifice :=
        face.additionalCostSacrificeCreature ||
          (face.additionalCostSacrificeArtifactOrCreature && face.additionalCostOrPayGeneric.isNone)
      g.beginResolutionCastTargets p {
        caster := p
        cost
        spellId := newId
        original
        originalSnapshot := origSnap
        needsSacrificeOther := needsSacrifice
      }

/-- Advance the pending Doom Reigns exile-cast queue one card at a time,
pausing whenever a proposed spell requires interactive mode, target, or cost
choices and resuming after `becomeCast` or `reverseProposedSpell?`. -/
partial def advanceCastExiledQueue (g : Game) : Game :=
  if g.pending != .none || g.proposedSpell.isSome then g
  else
    match g.pendingCastExiledQueue with
    | none => g
    | some (p, ids) =>
      match ids[0]? with
      | none => g.change (.pendingCastExiledQueue none)
      | some id =>
        let rest := ids.extract 1 ids.size
        let g :=
          if rest.isEmpty then g.change (.pendingCastExiledQueue none)
          else g.change (.pendingCastExiledQueue (some (p, rest)))
        let g := g.castAsPartOfResolution p id
        if g.pending != .none || g.proposedSpell.isSome then g
        else g.advanceCastExiledQueue
end

/-- Resume any deferred `PendingReplacement` (such as `.finishFraChoice`) queued
by `becomeCast` or `becomeActivated` once the spell or ability finishes going
onto the stack without opening a new `Pending`. -/
def resumeAfterBecomeCast (g : Game) : Game :=
  if g.pending == .none && g.pendingReplacement.isSome && !g.over then
    match g.pendingReplacement with
    | some cont => (g.change (.pendingReplacement none)).resumePendingReplacement cont
    | none => g
  else g

/-- Cast the first instant or sorcery card with mana value at most `maxMv`
from `p`'s hand as part of a resolution, without paying its mana cost. -/
def castInstantSorceryFromHandMvAtMost (g : Game) (p : PlayerId) (maxMv : Nat) : Game :=
  match (g.player p).hand.findSome? (fun id =>
    match g.findObject? id with
    | some o =>
      if o.printed.isInstantOrSorcery && o.printed.manaValue <= maxMv then some id
      else none
    | none => none) with
  | none => g.logMsg "No instant or sorcery to cast"
  | some id => g.castAsPartOfResolution p id

/-- Cast up to `n` cards that currently have a free-cast exile permission,
one at a time as the ability resolves (Doom Reigns; MSH 357). -/
def castExiledAsResolves (g : Game) (p : PlayerId) (n : Nat) : Game :=
  let ids :=
    (g.objects.filter (fun o =>
      o.zone == .exile &&
        match g.playPermission o with
        | some perm => perm.player == p && perm.withoutManaCost
        | none => false)).map (·.id)
  let chosen := ids.take n
  if chosen.isEmpty then g
  else
    let pushedFrame := g.continuations.isEmpty
    let g := if pushedFrame then g.change (.pushContinuationFrame {}) else g
    let g := g.change (.pendingCastExiledQueue (some (p, chosen)))
    let g := g.advanceCastExiledQueue
    if pushedFrame && !g.continuations.isEmpty && g.pending == .none && g.proposedSpell.isNone &&
        g.pendingCastExiledQueue.isNone && g.pendingReplacement.isNone then
      g.change .popContinuationFrame
    else g

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
      let g := g.logMsg s!"{(g.player p).name} declines to cast a spell"
      return finishMayCastFromLooked (g.change (.pending .none)) p ids
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
        else if (g.findObject? (g.followMoved id)).any (·.zone == .stack) then
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
    receivePriority (g.change (.pending .none)) g.activePlayer false

/-- Start paying the proposed activation's costs that need chosen objects,
reversing it if they can't be paid (CR 601.2h / 733.1). -/
def beginActivationPayment (g : Game) (prop : ProposedSpell) : Except String Game := do
  let picks := (prop.activation.map costPicksOf).getD #[]
  let payable :=
    match prop.sourceId with
    | some sid => g.costPicksPayable prop.caster sid picks
    | none => true
  if !payable then return (← g.reverseProposedSpell? (resumeContinuation := true))
  return (← g.continueCostPicks prop picks false).resumeAfterBecomeCast

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
        let spell := g.object! prop.spellId
        let g := g.changes #[.pending .none, .proposedSpell none, .consecutivePasses 0]
        (g.becomeCast prop.caster spell).resumeAfterBecomeCast

/-- After CR 601.2b additional-cost announcement, continue to targets (601.2c)
or cost determination (601.2f). -/
def afterAdditionalCostAnnounced (g : Game) : Game :=
  match g.proposedSpell with
  | none => g
  | some prop =>
    if g.proposedNeedsTarget prop then
      (g.change (.pending (.chooseTargets prop.caster))).logMsg
        s!"{(g.player prop.caster).name} must choose a target (CR 601.2c)"
    else
      g.afterTargetsChosen

/-- After the modes are chosen: additional costs, kicker, gift, and teamwork,
then targets (CR 601.2b–c). -/
def afterModesChosen (g : Game) (p : PlayerId) : Game :=
  match g.proposedSpell, g.proposedSpell.bind (fun prop => g.findObject? prop.spellId) with
  | some prop, some spell =>
    let face := g.baseCard spell
    if face.announcesAdditionalCost then
      (g.change (.pending (.chooseAdditionalCost p))).logMsg
        s!"{(g.player p).name} must choose an additional cost (CR 601.2b)"
    else if face.kicker.isSome && !prop.kickerAnnounced then
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
    if spell.printed.giftTreasure && !prop.giftAnnounced then
      let g := g.change (.pending (.chooseGift p))
      g.logMsg s!"{(g.player p).name} may promise a gift (CR 702.174)"
    else if spell.printed.teamwork.isSome && !prop.teamworkAnnounced then
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
    let g ← g.applyKickerToProposed kick
    let face? := g.proposedSpell.bind (fun prop => g.findObject? prop.spellId) |>.map (·.printed)
    let g := g.logMsg
      (if kick && (face?.bind (·.morph)).isSome then s!"{(g.player p).name} casts the spell face down"
       else if kick && (face?.bind (·.impending)).isSome then s!"{(g.player p).name} casts the spell for its impending cost"
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
    match prop.original.printed.teamwork.orElse (fun () =>
        (g.findObject? prop.spellId).bind (fun o => o.printed.teamwork)) with
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
    let mut g := g
    for id in ids do
      match g.findObject? id with
      | none => pure ()
      | some o =>
        g := g.becomeTapped o (cause := some (.costPayment .teamwork p (some prop.spellId)))
    let some spell := g.findObject? prop.spellId | throw "The spell left the stack"
    g := g.record (GameEvent.announced g.turnNumber spell.id (costs := #[.teamwork ids])
      (cause := some (.costPayment .teamwork p (some spell.id))))
    g := g.change (.pending .none)
      |>.changeProposals #[.teamworkPaid true, .teamworkAnnounced true]
    g := g.logMsg s!"{(g.player p).name} pays a teamwork cost"
    -- “If this spell was cast using teamwork, choose both instead.”
    if spell.printed.chooseBothIfTeamwork then
      let chosen := g.chosenModesOf spell
      for i in [0:spell.printed.spellModes.size] do
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

/-- Clear the finished scry or surveil, draw any follow-up cards, offer
Palantír's opponent their choice, and give the active player priority. -/
def finishLibraryLook (g : Game) : Game :=
  let g := g.changes #[
    .pending .none,
    .surveilReturnMvAtMost none,
    .surveilReturnNoncreatureNonland false ]
  let g :=
    match g.fraAfterLook with
    | some (c, src, next) =>
      (g.change (.fraAfterLook none)).applyFra c default next.toResolution #[] src
    | none => g
  let g :=
    match g.pendingDrawAfterScry with
    | some (q, n) =>
      let g := g.change (.pendingDrawAfterScry none)
      g.draw q n
    | none => g
  if g.pending != .none then g
  else
    match g.palantirAfterScry with
    | some (controller, opp, sid) =>
      (g.change (.palantirAfterScry none)).offerPalantirChoice controller opp sid
    | none =>
      let g := g.resumeTriggerSequence
      if g.pending != .none then g else g.receivePriority g.activePlayer

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
    let looked := g.scryLookedIds p count
    let cause := some (g.resolvingOrRuleCause p)
    let mut g := g
    for id in bottom do
      g := g.logMsg
        s!"{(g.player p).name} puts {(g.object! id).name} on the bottom of their library"
    g := g.logPutOnTop p looked top
    let happened :=
      GameEvent.looked g.turnNumber p count false asked
        (top := top) (rest := bottom) (cause := cause)
    g := g.record happened
    return g.finishLibraryLook
  | .surveil .. => throw "You are surveilling, not scrying; use surveil (CR 701.25)"
  | _ => throw "Not time to scry (CR 701.22)"

/-- Finish surveilling: put `graveyard` into the graveyard in that order and
`top` back on top (last = new top) of the library (CR 701.25). -/
def finishSurveil (g : Game) (p : PlayerId) (top graveyard : Array ObjectId) :
    Except String Game := do
  match g.pending with
  | .surveil q count asked =>
    g.checkLookedPiles p q count top graveyard "surveil" "CR 701.25"
    let looked := g.scryLookedIds p count
    let cause := some (g.resolvingOrRuleCause p)
    let g := (g.logPutOnTop p looked top).withBatch cause fun g => Id.run do
      let mut g := g
      let happened :=
        GameEvent.looked g.turnNumber p count true asked
          (top := top) (rest := graveyard) (cause := cause)
      g := g.record happened
      for id in graveyard do
        let card := g.object! id
        let (g', newId) := g.move id (.graveyard p) none (cause := cause)
        g := g'.logMsg s!"{(g.player p).name} puts {card.name} into their graveyard (surveil)"
        match g.surveilReturnMvAtMost with
        | some n =>
          if g.objectManaValue card ≤ n then
            let (g', _) := g.move newId (.hand p) none (cause := cause)
            g := g'.logMsg s!"{(g.player p).name} puts {card.name} into their hand"
        | none =>
          if g.surveilReturnNoncreatureNonland && !card.printed.isCreature &&
              !card.printed.isLand then
            let (g', _) := g.move newId (.hand p) none (cause := cause)
            g := g'.logMsg s!"{(g.player p).name} puts {card.name} into their hand"
      return g
    return g.finishLibraryLook
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
    let cause := some (g.resolvingOrRuleCause p)
    let g ← g.withBatchM cause fun g0 => do
      let effCause := g0.resolveOptionalCause cause (fallbackCtrl := some p)
      let mut g := g0
      let mut permIds : Array ObjectId := #[]
      let mut playerIds : Array PlayerId := #[]
      for t in chosen do
        match t with
        | .permanent id =>
          let some o := g.findObject? id | throw "no such object"
          if !o.isOnBattlefield then
            throw s!"{o.name} is not a permanent on the battlefield (CR 701.34a)"
          if !o.status.hasCounters then
            throw s!"{o.name} has no counters"
          let bag := o.status.toCounterBag
          for (kind, _) in bag do
            if kind != .plusOnePlusOne then
              let cur := g.object! id
              g := g.record (GameEvent.counters g.turnNumber (some p) (g.snapshot cur) kind 1 false
                (cause := effCause))
          g := g.syncImpendingNotACreature id (cause := some effCause)
          let o := g.object! id
          g := if o.status.plusOnePlusOne > 0 then g.addPlusOnePlusOneTo o 1 (cause := some effCause) else g
          permIds := permIds.push id
          g := g.logMsg s!"{(g.player p).name} proliferates {o.name}"
        | .player pid =>
          let pl := g.player pid
          if pl.poison == 0 then
            throw s!"{pl.name} has no counters"
          g := g.record (GameEvent.poisoned g.turnNumber pid 1 (byPlayer := some p) (cause := effCause))
          playerIds := playerIds.push pid
          g := g.logMsg s!"{(g.player p).name} gives {pl.name} another poison counter"
        | .card _ => throw "Only permanents and players can be chosen (CR 701.34a)"
      -- “Whenever you proliferate” triggers even if nothing was chosen (ruling 884).
      return g.record (GameEvent.proliferated g.turnNumber p
        (permanents := permIds) (players := playerIds) (cause := cause))
    let mut g := g
    if chosen.isEmpty then
      g := g.logMsg s!"{(g.player p).name} proliferates, choosing nothing"
    if remaining > 1 then
      return g.change (.pending (.chooseProliferate p (remaining - 1)))
    else
      return (g.change (.pending .none)).receivePriority g.activePlayer
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
  let g := g.logMsg s!"{(g.player p).name} discards {card.name}{logSuffix}"
  let (g, _) := g.move id (.graveyard card.owner) none (cause := cause)
  return (g, card)

/-- Run trigger-sequence steps that waited on this discard, then give
priority when nothing else is pending. -/
def resumeSequenceThenPriority (g : Game) : Game :=
  let g := g.resumeTriggerSequence
  if g.pending != .none then g else g.receivePriority g.activePlayer

/-- The optional action of `mayThen` was performed. Run its conditional. -/
def acceptMayThen (g : Game) : Game :=
  let g := g.changes #[
    .pending .none,
    .mayThenDrop 0,
    .mayThenConditional none,
    .mayThenResume false ]
  g.resumeSequenceThenPriority

/-- The optional action of `mayThen` was declined. Skip its conditional and
continue any later sequence steps. -/
def declineMayThen (g : Game) : Game :=
  let n := g.mayThenDrop
  let g := g.changes #[
    .pending .none,
    .mayThenDrop 0,
    .mayThenConditional none,
    .sacrificedPowerThisWay none,
    .mayThenResume false ]
  let g :=
    match g.triggerSequenceRest with
    | none => g
    | some rest => g.change (.setTriggerSequenceRestSteps (rest.steps.drop n))
  g.resumeSequenceThenPriority

/-- Continue a discard chain. When no one is left to discard, put the waiting
+1/+1 counter (Ninja of the Hand) and finish a paused trigger sequence. -/
def continueAfterDiscard (g : Game) (players : Array PlayerId) : Except String Game := do
  let waiting := g.triggerSequenceRest.isSome || g.plusOneAfterDiscards.isSome
  let g := g.beginDiscardCards players
  if g.pending != .none || !waiting then return g
  let g :=
    if g.plusOneAfterDiscards.isSome then g.finishPlusOneAfterDiscards else g
  return g.resumeSequenceThenPriority

/-- Discard `id` from hand; if this finishes a pending “may discard, then draw”,
draw that many cards (CR 701.9). -/
def discardForDraw (g : Game) (p : PlayerId) (id : ObjectId) : Except String Game := do
  match g.pending with
  | .mayDiscardDraw q n =>
    let (g, _) ← g.discardPendingCard p q id
    if g.mayThenDrop > 0 then
      return g.acceptMayThen
    else
      let g := g.draw p n
      let g := g.change (.pending .none)
      return g.receivePriority g.activePlayer
  | .maySacArtifactOrDiscard q n =>
    let (g, _) ← g.discardPendingCard p q id
    return g.finishSacArtifactOrDiscardDraw p n
  | .chooseDiscardCard q remaining =>
    let (g, card) ← g.discardPendingCard p q id
    let g := g.finishConniveDiscard card
    let g : Game :=
      match g.triggerSequenceRest with
      | some rest =>
        if rest.steps.any (· == .put .discardedLand (how := .tapped)) then
          g.change (.discardedCardThisWay (some (q, g.followMoved card.id)))
        else g
      | none => g
    if g.thirstDiscardsLeft > 0 then
      let left :=
        if card.printed.hasType g.thirstDiscardType then 0 else g.thirstDiscardsLeft - 1
      let g := g.change (.thirstDiscardsLeft left)
      if left == 0 then
        return (g.change (.pending .none)).resumeSequenceThenPriority
      else
        return g.beginDiscardCards #[p]
    if g.pendingDiscardsLeft > 0 then
      let left := g.pendingDiscardsLeft - 1
      let g := g.change (.pendingDiscardsLeft left)
      if left == 0 then
        g.continueAfterDiscard remaining
      else
        g.continueAfterDiscard #[p]
    else
      g.continueAfterDiscard remaining
  | .recruitDiscard q =>
    let (g, card) ← g.discardPendingCard p q id
    let g := g.change (.pending .none)
    let g :=
      if card.printed.isLand then g
      else
        let (g, _) := g.createToken p humanSoldierToken
        g
    return g.receivePriority g.activePlayer
  | .discardForAdditionalCost q =>
    let some prop := g.proposedSpell | throw "No spell is waiting for an additional cost"
    let outerCont? := g.pendingReplacement
    let hadOpenCont := !g.continuations.isEmpty
    let g0 := if outerCont?.isSome then g.change (.pendingReplacement none) else g
    let g ← g0.withProposalActionM .costAction fun g => do
      let (g, _) ← g.discardPendingCard p q id
        (cause := some (.costPayment .discard p (some prop.spellId)))
      return g.record (GameEvent.announced g.turnNumber prop.spellId (costs := #[.discard id])
        (cause := some (.costPayment .discard p (some prop.spellId))))
    let g :=
      match outerCont? with
      | some outer => g.chainPendingReplacement outer
      | none => g
    let clearPending : Array EngineChange :=
      if let .chooseReplacement .. := g.pending then #[] else #[.pending .none]
    let g := g.changes (clearPending ++ #[.proposedSpell none, .consecutivePasses 0])
    return (g.becomeCast prop.caster (g.object! prop.spellId)
      (hadOuterReplacement := outerCont?.isSome)
      (hadOpenContinuation := hadOpenCont)).resumeAfterBecomeCast
  | .payWard q spellId cost =>
    if p != q then
      throw s!"Only {(g.player q).name} may discard for ward"
    let legal :=
      match cost with
      | .discardEnchantmentInstantOrSorcery =>
        match g.findObject? id with
        | some o =>
          o.printed.isEnchantment || o.printed.isInstant || o.printed.isSorcery
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
    let g ← g.payCost p (ManaCost.ofGeneric n)
    let g := g.logMsg s!"{(g.player p).name} pays \{{n}}"
    if g.mayThenDrop > 0 then
      return (g.change (.mayPayAlsoPlusOneOn none)).acceptMayThen
    else
      let g := g.change (.pending .none)
      let g :=
        match g.mayPayAlsoPlusOneOn.bind g.findObject? with
        | some o => if o.isOnBattlefield then g.addPlusOnePlusOneTo o 1 else g
        | none => g
      let g := g.change (.mayPayAlsoPlusOneOn none)
      let g := g.draw p 1
      return g.receivePriority g.activePlayer
  | .payOrLetCounter q n _spellId =>
    if p != q then
      throw s!"Only {(g.player q).name} may pay \{{n}}"
    if !(g.player p).manaPool.canPay (ManaCost.ofGeneric n) then
      throw s!"{(g.player p).name} cannot pay \{{n}}"
    let g ← g.payCost p (ManaCost.ofGeneric n)
    let g := g.logMsg s!"{(g.player p).name} pays \{{n}}"
    let g := (g.change (.pending .none)).clearUnlessPays
    return g.receivePriority g.activePlayer
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
    match g.mayOnAccept, g.mayContext with
    | some action, some _ =>
      let g := (g.changes #[
        .pending .none,
        .mayOnAccept none,
        .mayOnDecline none,
        .setTriggerSequenceRestFromMay [action] ]).clearMay
      let g := g.resumeTriggerSequence
      if g.pending != .none || g.over then return g
      return g.receivePriority g.activePlayer
    | _, _ =>
      let some effect := g.mayEffect | throw "Nothing to resolve"
      let controller := g.mayController
      let targets := g.mayTargets
      let g := (g.change (.pending .none)).clearMay
      let g := g.applyUnified controller effect targets
      if g.pending != .none || g.over then return g
      return g.receivePriority g.activePlayer
  | _ => throw "Nothing to accept now"

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
    let effect := g.spellOr[idx]!
    let controller := g.spellOrController
    let targets := g.spellOrTargets
    let g := (g.change (.pending .none)).clearSpellOr
    let g := g.applyUnified controller effect targets
    if g.pending != .none || g.over then return g
    return g.receivePriority g.activePlayer
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
      let g := g.putOnOwnerLibrary o (top := top)
      let g := g.change (.pending .none)
      return g.receivePriority g.activePlayer
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
    let g := g.attachSourceTo eq host
    let g := g.change (.pending .none)
    return g.receivePriority g.activePlayer
  | .tapHumans q =>
    if p != q then
      throw s!"Only {(g.player q).name} may tap Humans"
    if !uniqueObjectIds ids then
      throw "Duplicate card"
    let (g, n) ← g.withBatchExcept none fun g => do
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
    let mut g := g.changes #[.pending .none, .humansTappedThisWay n]
    g := g.resumeTriggerSequence
    if g.pending != .none then return g
    return g.receivePriority g.activePlayer
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
    if face.requiresTarget && (g.legalCastTargets p face).isEmpty && !face.allowsZeroTargets then
      throw s!"{face.name} requires a target"
    let cost := g.playManaCost card face
    let pl := g.player p
    let some (_, spentUnits) := pl.manaPool.payUnits? cost
      | throw s!"{pl.name} cannot pay {cost}"
    let g := g.change .saveProposalCheckpoint
    let (g, newId) := g.move id .stack (some p) (verb := some .cast) (actor := some p)
      (cause := some (.gameRule .spellCast))
    let g := g.putStackEntry p newId
    let g := g.record (GameEvent.proposed g.turnNumber newId p card.zone
      (.alternative "permission"))
    let g :=
      if spentUnits.isEmpty && !cost.includesManaPayment then g
      else
        g.withProposalAction .costAction fun g =>
          g.record (GameEvent.manaSpent g.turnNumber p spentUnits newId
            (cause := some (.costPayment .mana p (some newId))))
    let g := g.change (.pending .none)
    let g := g.logMsg s!"{(g.player p).name} casts {face.name} as the ability resolves"
    if face.requiresTarget then
      let prop : ProposedSpell := {
        caster := p, cost := ManaCost.empty, spellId := newId, original := card
        originalSnapshot := origSnap }
      return g.changes #[.pending (.chooseTargets p), .proposedSpell (some prop)]
    else
      return (g.becomeCast p (g.object! newId)).resumeAfterBecomeCast
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
    let src? := sid.bind g.damageSourceById?
    let g := g.logMsg s!"{(g.player p).name} doesn't cast the exiled card"
    let g := g.dealDamageToEachOpponent p n (source := src?)
    let g := g.change (.pending .none)
    return g.receivePriority g.activePlayer
  | .mayDiscardDraw q _ =>
    if p != q then
      throw s!"Only {(g.player q).name} may decline to discard"
    let g := g.logMsg s!"{(g.player p).name} declines to discard a card"
    if g.mayThenDrop > 0 then
      return g.declineMayThen
    else
      let g := g.change (.pending .none)
      return g.receivePriority g.activePlayer
  | .chooseTargets caster =>
    if caster != p then
      throw s!"Only {(g.player caster).name} may choose targets (CR 601.2c)"
    let some obj := g.objectAwaitingTargets | throw "No spell is waiting for a target (CR 601.2c)"
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
        | none => false
      if allowZero then
        let g := g.setStackEntryTargets obj.id #[]
        let g := g.logMsg
          s!"{(g.player p).name} chooses no target (CR 603.3d / 601.2c)"
        if g.proposedSpell.isSome then
          return g.afterTargetsChosen
        return g.afterTriggerTargetsChosen
      else if g.canSkipCurrentOptionalSlot obj then
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
      throw "That spell requires a target (CR 601.2c)"
  | .mayPayGeneric q _ =>
    let g := g.change (.mayPayAlsoPlusOneOn none)
    if p != q then
      throw s!"Only {(g.player q).name} may decline to pay"
    let g := g.logMsg s!"{(g.player p).name} declines to pay"
    if g.mayThenDrop > 0 then
      return g.declineMayThen
    else
      let g := g.change (.pending .none)
      return g.receivePriority g.activePlayer
  | .payOrLetCounter q _ spellId =>
    if p != q then
      throw s!"Only {(g.player q).name} may decline to pay"
    let g := g.logMsg s!"{(g.player p).name} does not pay"
    let instead := g.unlessPaysInstead
    let caster := g.unlessPaysController
    let targets := g.unlessPaysTargets
    let g := (g.change (.pending .none)).clearUnlessPays
    let g :=
      match instead with
      | some effect => g.applyUnified caster effect targets
      | none => g.counterStackSpell spellId
    return g.receivePriority g.activePlayer
  | .payWard _ _ (.sacrificePermanents _ (_ + 1)) =>
    throw s!"{(g.player p).name} already began sacrificing permanents for ward and must finish"
  | .payWard q spellId _ =>
    if p != q then
      throw s!"Only {(g.player q).name} may decline to pay ward"
    let g := g.logMsg s!"{(g.player p).name} does not pay ward"
    let wardCtrl := (g.resolvingAbilityObject?.bind (·.controller)).getD (g.opponent p)
    let g := g.counterStackSpell spellId (controller := wardCtrl)
    return g.afterWardResolved
  | .mayAttachEquipment q _ =>
    if p != q then
      throw s!"Only {(g.player q).name} may decline to attach Equipment"
    let g := g.logMsg s!"{(g.player p).name} declines to attach Equipment"
    let g := g.change (.pending .none)
    return g.receivePriority g.activePlayer
  | .mayResolve q =>
    if p != q then
      throw s!"Only {(g.player q).name} may decline"
    let g := g.logMsg s!"{(g.player p).name} declines"
    match g.mayOnDecline, g.mayContext with
    | some follow, some _ =>
      let g := (g.changes #[
        .pending .none,
        .mayOnAccept none,
        .mayOnDecline none,
        .setTriggerSequenceRestFromMay [follow] ]).clearMay
      let g := g.resumeTriggerSequence
      if g.pending != .none || g.over then return g
      return g.receivePriority g.activePlayer
    | _, _ =>
      let g := (g.changes #[.pending .none, .mayOnAccept none, .mayOnDecline none, .mayContext none]).clearMay
      return g.receivePriority g.activePlayer
  | .tapHumans q =>
    if p != q then
      throw s!"Only {(g.player q).name} may decline to tap Humans"
    let g := g.logMsg s!"{(g.player p).name} taps no Humans"
    let g := g.changes #[.pending .none, .humansTappedThisWay 0]
    let g := g.resumeTriggerSequence
    if g.pending != .none then return g
    return g.receivePriority g.activePlayer
  | .maySacrificeAnotherBolg q _ =>
    if p != q then
      throw s!"Only {(g.player q).name} may decline to sacrifice"
    let g := g.logMsg
      s!"{(g.player p).name} declines to sacrifice a creature to Bolg"
    let g := g.change (.pending .none)
    return g.receivePriority g.activePlayer
  | .mayCastFromLooked q _ _ =>
    if p != q then
      throw s!"Only {(g.player q).name} may decline to cast a spell"
    g.chooseCastFromLooked p none
  | .mayPutLandFromHand q =>
    if p != q then
      throw s!"Only {(g.player q).name} may decline to put a land onto the battlefield"
    let g := g.logMsg
      s!"{(g.player p).name} declines to put a land onto the battlefield"
    let g := g.change (.pending .none)
    return g.receivePriority g.activePlayer
  | .maySacArtifactOrDiscard q _ =>
    if p != q then
      throw s!"Only {(g.player q).name} may decline"
    let g := g.logMsg
      s!"{(g.player p).name} declines to sacrifice an artifact or discard a card"
    if g.mayThenDrop > 0 then
      return g.declineMayThen
    else
      let g := g.change (.pending .none)
      return g.receivePriority g.activePlayer
  | .mayPutArtifactFromHand q _ =>
    if p != q then
      throw s!"Only {(g.player q).name} may decline to put an artifact onto the battlefield"
    let g := g.logMsg
      s!"{(g.player p).name} declines to put an artifact onto the battlefield"
    let g := g.changes #[.pending .none, .putArtifactThisWay none]
    return g.resumeSequenceThenPriority
  | .mayHaveVillainConnive q _ _ =>
    if p != q then
      throw s!"Only {(g.player q).name} may decline to have the Villain connive"
    let g := g.logMsg s!"{(g.player p).name} declines to have the Villain connive"
    let g := g.change (.pending .none)
    return g.receivePriority g.activePlayer
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
    let others := ids.filter (· != id)
    let preBf := g.battlefield
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
    return g.receivePriority g.activePlayer
  | _ => throw "Not time to apply the legend rule (CR 704.5j)"

/-- Put this player's waiting triggered abilities on the stack in the listed
source order (CR 603.3b). First listed is put first (farthest from the top). -/
def stackTriggers (g : Game) (p : PlayerId) (ids : Array ObjectId) : Except String Game := do
  match g.pending with
  | .chooseTriggerToStack q =>
    if p != q then
      throw s!"Only {(g.player q).name} may choose the order of triggered abilities (CR 603.3b)"
    let mine := g.waitingTriggersOf p
    if ids.size != mine.size then
      throw "List each waiting triggered ability's source once (CR 603.3b)"
    let mut remaining := mine
    let mut ordered : Array WaitingTrigger := #[]
    for id in ids do
      match remaining.findIdx? (fun wt => wt.source.id == id) with
      | none =>
        throw "That permanent has no waiting triggered ability to put on the stack (CR 603.3b)"
      | some i =>
        ordered := ordered.push remaining[i]!
        remaining := remaining.eraseIdx! i
    let g := (g.change (.pending .none)).logMsg
      s!"{(g.player p).name} chooses the order of triggered abilities (CR 603.3b)"
    let g := g.putTriggerBatch ordered
    if g.over || g.pending != .none then
      return g
    return g.receivePriority g.activePlayer false
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
    if grantPriority && g.pending == .none && g.afterRandom == .none &&
        !g.openingHandsPending && !g.over && !g.players.isEmpty then
      let g :=
        match g.pendingReplacement with
        | some cont =>
          let g := g.change (.pendingReplacement none)
          g.resumePendingReplacement cont
        | none => g
      if g.pending != .none || g.afterRandom != .none || g.over then g
      else
        let g := g.advanceCastExiledQueue
        if g.pending != .none || g.afterRandom != .none || g.over then g
        else
          let g := g.resumeTriggerSequence
          if g.pending != .none || g.afterRandom != .none || g.over then g
          else
            let g := g.completeActiveResolutions
            if g.pending != .none || g.afterRandom != .none || g.over then g
            else g.receivePriority g.activePlayer
    else g

/-- Apply a `--norandom` permutation or chosen object. -/
def supplyOrder (g : Game) (ids : Array ObjectId) : Except String Game := do
  match g.pending with
  | .resolveRandom req =>
    match req with
    | .shuffleLibrary p =>
      let pl := g.player p
      let ids := if ids.isEmpty then pl.library else ids
      if !isPermutation ids pl.library then
        throw "Shuffle must list each library card once (bottom first), or omit the ids to keep the current order"
      let shuffleCause : EventCause :=
        match g.pregameRandom with
        | .openingShuffles _ => .gameRule .openingHandDraw
        | .mulliganDraw .. | .mulliganQueue .. => .gameRule .mulligan
        | _ => g.resolvingOrRuleCause p
      let g := g.change (.pending .none)
      let g := g.record (GameEvent.shuffled g.turnNumber p ids (cause := some shuffleCause))
      return g.finishAfterRandom true
    | .orderInto expected dest cause =>
      let ids := if ids.isEmpty then expected else ids
      if !isPermutation ids expected then
        throw "Order must list each of those cards once, or omit the ids to keep their current order"
      let g := g.change (.pending .none)
      let g := g.moveIdsInOrder ids dest (cause := cause)
      return g.finishAfterRandom true
    | .chooseObject choices =>
      match ids[0]?, ids.size with
      | some id, 1 =>
        if !choices.contains id then
          throw "That is not one of the random choices"
        match g.afterRandom with
        | .revealRandomCreatureThenBottom controller revealed =>
          let g := g.changes #[.pending .none, .afterRandom .none]
          let g := g.resolveRandomCreatureReveal controller revealed id
          match g.pendingRandom? with
          | some _ => return g
          | none => return g.finishAfterRandom true
        | .discardRandom controller =>
          let g := g.changes #[.pending .none, .afterRandom .none]
          let g := g.discardFromHandRandomly controller id
          return g.finishAfterRandom true
        | _ =>
          let g := g.change (.pending .none)
          return g.finishAfterRandom true
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
    let g := g.change (.pending .none)
    match g.pregameRandom with
    | .setStartingPlayer _ =>
      return finishAfterRandom (g.change (.pregameRandom (.setStartingPlayer i))) true
    | _ =>
      return g.finishAfterRandom true
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
          throw s!"{nm} isn't the name of a nonland card (CR 201.3)"
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
    let g := if g.pending == .none then g.resumeTriggerSequence else g
    let g :=
      if g.pending == .none && g.afterRandom == .none then
        g.completeActiveResolutions
      else g
    return g
  | _ =>
    throw "No replacement effect choice is pending"

end Game
end Mtg.Engine
