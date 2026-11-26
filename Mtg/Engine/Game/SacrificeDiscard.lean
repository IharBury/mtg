import Mtg.Engine.Game.Choices

/-!
# Sacrifice and discard prompts (CR 701.21 / 701.9)

Multi-player sacrifice and discard flows resolved in APNAP order,
connive (CR 701.50), and sacrifices paid for activations.
-/

namespace Mtg.Engine
namespace Game

/-- Ask the next player who can sacrifice a creature, or finish if none remain. -/
def beginSacrificeCreatures (g : Game) (players : Array PlayerId)
    (chosen : Array ObjectId := #[]) : Game :=
  let players := players.filter g.stillInGame
  match g.nextActorWithCreatures players with
  | none =>
    let skipped := players.filter (fun p => (g.creaturesControlledBy p).isEmpty)
    let g := g.logForPlayers skipped (fun p =>
      s!"{(g.player p).name} has no creature to sacrifice")
    g.finishChosenSacrifices chosen
  | some (p, rest) =>
    (g.change (.pending (.chooseSacrificeCreature p chosen rest))).logMsg
      s!"{(g.player p).name} must sacrifice a creature"

/-- Close `g.discardBatch` when it owns `g.currentBatch`, evaluating batch-level
discard and graveyard-arrival triggers once (CR 603.2c / 701.9b). -/
def closeCurrentDiscardBatch (g : Game) : Game :=
  match g.discardBatch with
  | some (dbBid, dbStartIdx) =>
    let g := g.change (.discardBatch none)
    if g.currentBatch.map Prod.fst == some dbBid then
      g.finishOpenBatchAndLinkedExile dbBid dbStartIdx
    else g
  | none => g

/-- Ask the next player who has a card to discard, or resume priority.
`count` is how many cards each player in `players` must discard, one at a time.
Across multi-card / multi-player prompts (`count > 1`, `thirstDiscardsLeft > 1`,
or multiple players), `discardCountPerPlayer` preserves `count` for later players
in `players` and a shared `pausedBatch` (`discardBatch`) stays open across the
individual per-card `.discard` moves so batch-level discard / graveyard-arrival
triggers evaluate once when the instruction finishes (CR 101.4 / 118.12a /
603.2c / 701.9b). -/
def beginDiscardCards (g : Game) (players : Array PlayerId) (count : Nat := 1)
    (samePlayer : Bool := false) (resuming : Bool := false) : Game :=
  if !resuming && count == 0 && g.thirstDiscardsLeft == 0 then g
  else
    match g.nextActorWithHandCard players with
    | none =>
      let skipped := players.filter (fun p => g.stillInGame p && (g.discardableHandIds p).isEmpty)
      let g := g.logForPlayers skipped (fun p =>
        s!"{(g.player p).name} has no card to discard")
      let g :=
        if g.conniveSource.isSome then
          (g.change (.conniveSource none)).logMsg
            "No card is discarded; the conniving creature does not receive a +1/+1 counter"
        else g
      let g := g.changes #[
        .pending .none, .thirstDiscardsLeft 0,
        .pendingDiscardsLeft 0, .discardCountPerPlayer 0]
      g.closeCurrentDiscardBatch
    | some (p, rest) =>
      let prefixIdx := players.findIdx? (· == p) |>.getD 0
      let skipped := (players.extract 0 prefixIdx).filter (fun q =>
        g.stillInGame q && (g.discardableHandIds q).isEmpty)
      let g := g.logForPlayers skipped (fun q =>
        s!"{(g.player q).name} has no card to discard")
      let keptSamePlayer := resuming && samePlayer && players[0]? == some p
      let isNonThirstMulti := g.thirstDiscardsLeft == 0 && (count > 1 || !rest.isEmpty)
      let needsBatch := isNonThirstMulti || g.thirstDiscardsLeft > 1
      let g :=
        if (count > 1 || needsBatch) && g.continuations.isEmpty then
          g.change (.pushContinuationFrame {})
        else g
      let g :=
        if !resuming && g.thirstDiscardsLeft == 0 then
          let perPlayer := if count > 1 then count else 0
          if g.discardCountPerPlayer != perPlayer then g.change (.discardCountPerPlayer perPlayer)
          else g
        else g
      let g :=
        if !keptSamePlayer && g.thirstDiscardsLeft == 0 then
          let nextLeft := if count > 1 then count else 0
          if g.pendingDiscardsLeft != nextLeft then g.change (.pendingDiscardsLeft nextLeft)
          else g
        else g
      let g :=
        if !resuming && needsBatch && g.currentBatch.isNone && g.discardBatch.isNone then
          let batchId : BatchId := ⟨g.nextBatchId⟩
          let startIdx := g.events.size
          let batchCause :=
            g.currentResolvingContext?.map fun (src, ctrl) => .oneShotEffect none src ctrl
          let g := g.change (.pauseBatch batchId batchCause
            g.objects g.players g.activeEffects g.pending g.stack)
          g.change (.discardBatch (some (batchId, startIdx)))
        else g
      (g.change (.pending (.chooseDiscardCard p rest))).logMsg
        s!"{(g.player p).name} must discard a card"

/-- Draw `cards`, then start `discardRounds` discard choices for `p`. -/
def drawThenBeginDiscard (g : Game) (p : PlayerId) (cards : Nat := 1)
    (discardRounds : Nat := 1) : Game :=
  let g := g.draw p cards
  if let .chooseReplacement .. := g.pending then
    g.chainPendingReplacement (.finishDrawThenBeginDiscard p discardRounds)
  else
    g.beginDiscardCards #[p] discardRounds

/-- Execute the remaining `extraDraws`, connive draw, and discard prompt of
`applyConnive`. -/
def finishConniveDraws (g : Game) (controller : PlayerId)
    (extraDraws : Array (Nat × ReplacementId))
    (conniveDrawCause : Option EventCause)
    (stage : ConniveDrawStage := .draws) : Game := Id.run do
  if let .chooseReplacement .. := g.pending then
    return g.chainPendingReplacement
      (.finishConniveDraws controller extraDraws conniveDrawCause stage)
  if !g.stillInGame controller then
    return g
  let mut g := g
  if stage == .draws then
    for i in [0:extraDraws.size] do
      let (n, rid) := extraDraws[i]!
      let c := g.wrapReplacedCause rid none (some controller)
      g := g.draw controller n (cause := c)
      if let .chooseReplacement .. := g.pending then
        let rem := extraDraws.extract (i + 1) extraDraws.size
        return g.chainPendingReplacement
          (.finishConniveDraws controller rem conniveDrawCause .draws)
    g := g.draw controller 1 (cause := conniveDrawCause)
    if let .chooseReplacement .. := g.pending then
      return g.chainPendingReplacement
        (.finishConniveDraws controller #[] conniveDrawCause .discardOnly)
  if (g.discardableHandIds controller).isEmpty then
    g := g.change (.conniveSource none)
    return g.logMsg "No card is discarded; the conniving creature does not receive a +1/+1 counter"
  else
    return g.beginDiscardCards #[controller]

/-- Draw, then discard. If a nonland is discarded and the source is still on
the battlefield, put a +1/+1 counter on it. The creature still connives if it
has left (MSH / CR 701.50). -/
def applyConnive (g : Game) (controller : PlayerId) (sourceId : Option ObjectId) : Game :=
  if let .chooseReplacement .. := g.pending then
    g.chainPendingReplacement (.connive controller sourceId)
  else if !g.stillInGame controller then g
  else
  let run (g : Game) : Game :=
    -- CR 616.1 replacement loop for Leader's `.extraDrawOnConnive` ("If a
    -- creature you control would connive, draw a card, then that creature
    -- connives instead", CR 614.5).
    let (extraDraws, curApplied, choice?) :
        Array (Nat × ReplacementId) × Array ReplacementId × Option (PlayerId × Array ReplacementId) := Id.run do
      let mut draws : Array (Nat × ReplacementId) := #[]
      let mut curApplied : Array ReplacementId := #[]
      let mut choice? : Option (PlayerId × Array ReplacementId) := none
      let mut fuel := 32
      while fuel > 0 do
        fuel := fuel - 1
        let mut specs : Array (ReplacementSpec × Nat) := #[]
        for o in g.battlefield do
          let srcCtrl := (g.controllerOf o).getD o.owner
          let env : EvalEnv := { controller := srcCtrl, sourceId := some o.id }
          for ab in g.staticAbilities o do
            match ab with
            | .replacement cond? spec =>
              if cond?.all (EvalExpr.evalCondition g env) then
                for sp in spec.flatten do
                  match sp with
                  | .extraDrawOnConnive who sc n =>
                    let conniverOk :=
                      match sourceId.bind (EvalExpr.resolveObjectView? g env) with
                      | some v => EvalExpr.evalObjectPred g env v sc.pred
                      | none => true
                    if n > 0 && EvalExpr.matchesPlayerFilter g env who controller && conniverOk then
                      specs := specs.push (
                        { id := { kind := .extraDrawOnConnive, object := some o.id }
                          source := some o.id
                          controller := some srcCtrl
                          affectedPlayer := controller
                          kind := .extraDrawOnConnive controller n }, n)
                  | _ => pure ()
            | _ => pure ()
        for (_, eff) in g.activeEffects do
          match eff with
          | .replacement spec d =>
            if g.durationActive d then
              match spec.kind with
              | .extraDrawOnConnive who n =>
                if who == controller then specs := specs.push ({ spec with affectedPlayer := controller }, n)
              | _ => pure ()
          | _ => pure ()
        let candidates := specs.map (fun (s, _) => (ReplacementOrPrevention.replacement s).toCandidate)
        match g.selectNextReplacementStep candidates curApplied with
        | .none => fuel := 0
        | .needChoice chooser choices _ =>
          choice? := some (chooser, choices)
          fuel := 0
        | .chosen chosen _ =>
          match specs.find? (fun (s, _) => s.id == chosen.id) with
          | none => fuel := 0
          | some (_, n) =>
            curApplied := curApplied.push chosen.id
            draws := draws.push (n, chosen.id)
      return (draws, curApplied, choice?)
    match choice? with
    | some (chooser, choices) =>
      g.promptChooseReplacement chooser choices (.connive controller sourceId)
    | none =>
      let g := g.consumeReplacementOrder curApplied
      let g := g.change (.conniveSource sourceId)
      let g := g.logMsg s!"{(g.player controller).name}'s creature connives"
      let conniveDrawCause :=
        extraDraws.foldl (fun acc (_, rid) =>
          g.wrapReplacedCause rid acc (some controller)) none
      g.finishConniveDraws controller extraDraws conniveDrawCause .draws
  g.withContinuationFrame run

/-- Finish a pending connive after a card is discarded. -/
def finishConniveDiscard (g : Game) (discarded : GameObject) : Game :=
  match g.conniveSource with
  | none => g
  | some sid =>
    let g := g.change (.conniveSource none)
    if g.isLand discarded then
      g.logMsg "A land was discarded; the conniving creature does not receive a +1/+1 counter"
    else
      match g.findObject? sid with
      | some o =>
        if o.isOnBattlefield then
          g.addPlusOnePlusOneTo o 1 (byPlayer := g.controllerOf o)
        else
          g.logMsg "The conniving creature has left the battlefield; no +1/+1 counter is put"
      | none =>
        g.logMsg "The conniving creature has left the battlefield; no +1/+1 counter is put"

/-- Villain that would connive for Baron Strucker: an announced target, the
causing object's id stored in `triggerCauseId`, or the newest other Villain
that entered this turn. -/
def villainConniveTarget? (g : Game) (controller : PlayerId) (sourceId : ObjectId)
    (targets : Array Target) : Option ObjectId :=
  match targets[0]? with
  | some (Target.permanent id) => some id
  | _ =>
    match (g.resolvingAbility.bind g.findObject?).bind (·.triggerCauseId) with
    | some cid => some cid
    | none =>
      let cands :=
        (g.permanentsOf controller).filter (fun x =>
          x.id != sourceId && g.hasSubtype x .villain && g.loggedEntered x.id)
      if cands.isEmpty then none
      else
        some (cands.foldl (fun acc x =>
          if x.timestamp > acc.timestamp then x else acc) cands[0]!).id

/-- Ask whether to have the entering Villain connive (MSH 422). -/
def beginMayHaveVillainConnive (g : Game) (controller : PlayerId)
    (sourceId villainId : ObjectId) : Game :=
  if !g.stillInGame controller then g
  else
    let who :=
      match g.findObject? villainId with
      | some o => g.name o
      | none => "the Villain"
    (g.change (.pending (.mayHaveVillainConnive controller sourceId villainId))).logMsg
      s!"{(g.player controller).name} may have {who} connive (do this only once each turn)"

/-- Accept Baron Strucker's optional connive (MSH 422). -/
def haveVillainConnive (g : Game) (p : PlayerId) : Except String Game := do
  match g.pending with
  | .mayHaveVillainConnive q sourceId villainId =>
    if p != q then
      throw s!"Only {(g.player q).name} may have the Villain connive"
    let outerCont? := g.pendingReplacement
    let g := if outerCont?.isSome then g.change (.pendingReplacement none) else g
    let g := g.change (.pending .none)
    let g :=
      if (g.findObject? sourceId).isSome then
        g.record (GameEvent.optionalOnceActed g.turnNumber p sourceId
          (cause := some (.oneShotEffect none (some sourceId) (some p))))
      else g
    let g := g.applyConnive p (some villainId)
    return g.reattachOuterCont outerCont?
  | _ => throw "Not time to have a Villain connive"

/-- After paying an optional sacrifice-artifact-or-discard cost, draw `n` cards
(when `n > 0`; `n == 0` leaves follow-up work to the unified interpreter). -/
def finishSacArtifactOrDiscardDraw (g : Game) (p : PlayerId) (n : Nat) : Game :=
  if let .chooseReplacement .. := g.pending then
    g.chainPendingReplacement (.finishSacArtifactOrDiscardDraw p n)
  else
    let g := g.change (.pending .none)
    if n == 0 then g else g.draw p n

/-- After mana is paid, sacrifice an artifact or creature (CR 601.2h / 602.2b), or sacrifice a creature a resolved trigger requires (CR 608.2d / 701.21). -/
def sacrificeForActivation (g : Game) (p : PlayerId) (id : ObjectId) : Except String Game := do
  match g.pending with
  | .sacrificePermanent caster sourceId =>
    if caster != p then
      throw s!"Only {(g.player caster).name} may sacrifice"
    if g.proposedSpell.isSome && !g.proposalCostPromptStillPayableFwd p g.pending then
      return (← g.reverseProposedSpellExceptFwd (resumeContinuation := true))
    let some sac := g.findObject? id | throw "no such object"
    if !g.canSacrificeAsCreatureOrArtifact p sourceId sac then
      throw s!"Can't sacrifice {g.name sac}"
    let forObject := g.proposedSpell.map (·.spellId) <|> some sourceId
    let outerCont? := g.pendingReplacement
    let openCont := g.proposalHadOpenContinuation
    let g := if outerCont?.isSome then g.change (.pendingReplacement none) else g
    let spellPropId? :=
      g.proposedSpell.bind (fun pr => if pr.kind == .spell then some pr.spellId else none)
    let g := g.withProposalAction .costAction fun g =>
      let g := g.sacrificeToGraveyard sac
        s!"{(g.player p).name} sacrifices {g.name sac}"
        (cause := some (.costPayment .sacrifice p forObject))
      match spellPropId? with
      | some sid =>
        g.record (GameEvent.announced g.turnNumber sid (costs := #[.sacrifice sac.id])
          (cause := some (.costPayment .sacrifice p (some sid))))
      | none => g
    let paused := match g.pending with | .chooseReplacement .. => true | _ => false
    let clearPending : Array EngineChange :=
      if paused then #[] else #[.pending .none]
    if let some prop := g.proposedSpell then
      if prop.needsDiscardCard then
        let g :=
          if !paused then
            match outerCont? with
            | some outer => g.chainPendingReplacement outer
            | none => g
          else g
        if !paused && (g.discardableHandIds prop.caster).isEmpty then
          return (← g.reverseProposedSpellExceptFwd (resumeContinuation := true))
        let prompt := s!"{(g.player prop.caster).name} must discard a card"
        if paused then
          let g := (g.change (.consecutivePasses 0)).chainPendingReplacement
            (.restorePending (.discardForAdditionalCost prop.caster) (promptLog := some prompt))
          return match outerCont? with
            | some outer => g.chainPendingReplacement outer
            | none => g
        else
          let g := g.changes #[.pending (.discardForAdditionalCost prop.caster), .consecutivePasses 0]
          return g.logMsg prompt
    let (g, callerShouldResume) : Game × Bool ←
      match g.proposedSpell with
      | some prop =>
        if prop.kind == ProposalKind.turnFaceUp then
          let willReverse := !paused && !g.over && g.proposalCheckpoint.isSome &&
            !(g.stillInGame prop.caster &&
              (g.findObject? prop.spellId).any (fun o =>
                o.isOnBattlefield && o.status.faceDown && g.controlledBy o prop.caster))
          let (g, shouldRes) :=
            g.completeTurnFaceUp prop.caster prop.spellId
              (hadOuterReplacement := outerCont?.isSome)
          let g :=
            if willReverse then g
            else
              match outerCont? with
              | some outer => g.chainProposalOuterCont prop.caster outer (openCont := openCont)
              | none => g
          pure (g, !willReverse && (shouldRes || (!g.over && g.pending == .none && outerCont?.isSome)))
        else
          let isResCast := prop.resolutionCast
          match prop.kind with
          | .spell =>
            match g.findObject? prop.spellId with
            | some spellObj =>
              let g := g.changes (clearPending ++ #[EngineChange.consecutivePasses 0])
              let g := g.becomeCast prop.caster spellObj
                (grantPriority := !isResCast)
                (hadOuterReplacement := outerCont?.isSome)
                (hadOpenContinuation := some openCont)
              let nowPaused := match g.pending with | .chooseReplacement .. => true | _ => false
              match outerCont? with
              | some outer =>
                let g := g.chainProposalOuterCont prop.caster outer
                  (grantPriority := !isResCast) (openCont := openCont)
                pure (g, !g.over && g.pending == .none)
              | none =>
                if isResCast then
                  if nowPaused then
                    let g :=
                      if !g.over && !g.anyContinuationSettlesControlFlowFwd then
                        g.chainPendingReplacement .finishResolutionChoice
                      else g
                    pure (g, false)
                  else
                    pure (g.resumePendingReplacementFwd .finishResolutionChoice, false)
                else
                  pure (g, !g.over && g.pending == .none && g.pendingReplacement.isSome)
            | none =>
              let g ← g.reverseProposedSpellExceptFwd (resumeContinuation := true)
              return g
          | .activatedAbility =>
            let hadPropCkpt := !paused && g.proposalCheckpoint.isSome
            let g := g.changes (clearPending ++ #[EngineChange.consecutivePasses 0])
            let g := g.becomeActivated p prop.originalSnapshot.name prop.sourceId prop.activation
              (abilityId := some prop.spellId)
              (sourceSnapshot := some prop.originalSnapshot)
              (sourceOriginal := some prop.original)
              (hadOuterReplacement := outerCont?.isSome)
              (hadOpenContinuation := some openCont)
            let didRev := hadPropCkpt && g.proposedSpell.isNone &&
              !g.stack.any (·.objectId == prop.spellId)
            let g :=
              if didRev then g
              else
                match outerCont? with
                | some outer => g.chainProposalOuterCont p outer (openCont := openCont)
                | none => g
            pure (g, !didRev && !g.over && g.pending == .none &&
              (outerCont?.isSome || g.pendingReplacement.isSome))
          | .turnFaceUp => pure (g, false)
      | none =>
        let g := g.changes (clearPending ++ #[EngineChange.proposedSpell none, EngineChange.consecutivePasses 0])
        match g.findObject? sourceId with
        | some srcObj =>
          let g := g.becomeActivated p (g.name srcObj) (some sourceId)
            (hadOuterReplacement := outerCont?.isSome)
            (hadOpenContinuation := some openCont)
          let g :=
            match outerCont? with
            | some outer => g.chainProposalOuterCont p outer (openCont := openCont)
            | none => g
          pure (g, !g.over && g.pending == .none && (outerCont?.isSome || g.pendingReplacement.isSome))
        | none =>
          match outerCont? with
          | some outer =>
            let g := g.chainProposalOuterCont p outer (openCont := openCont)
            pure (g, !g.over && g.pending == .none)
          | none =>
            if !paused && !g.over && g.pending == .none then
              let prio := if openCont then g.activePlayer else p
              if g.pendingReplacement.isSome || !g.outerPendingReplacements.isEmpty ||
                  g.currentInterpWait?.isSome then
                let g := g.chainFinishChoicePreservingPriority prio
                if !g.over && g.pending == .none then
                  if g.pendingReplacement.isSome then pure (g, true)
                  else pure (g.resumePendingReplacementFwd .finishResolutionChoice, false)
                else pure (g, false)
              else
                pure (g.receivePriority (g.priorityInstead prio), false)
            else pure (g, false)
    return if callerShouldResume then g.resumeAfterBecomeCastFwd else g
  | .chooseSacrificeCreature q chosen remaining =>
    if q != p then
      throw s!"Only {(g.player q).name} may sacrifice"
    let some sac := g.findObject? id | throw "no such object"
    if !sac.isOnBattlefield || !g.isCreature sac || !g.controlledBy sac p then
      throw s!"Can't sacrifice {g.name sac}"
    let outerCont? := g.pendingReplacement
    let g := if outerCont?.isSome then g.change (.pendingReplacement none) else g
    let g := g.beginSacrificeCreatures remaining (chosen.push id)
    return g.reattachOuterCont outerCont?
  | .sacrificeCreature q =>
    if p != q then
      throw s!"Only {(g.player q).name} may sacrifice"
    let some sac := g.findObject? id | throw "no such object"
    if !g.canSacrificeCreature p sac then
      throw s!"Can't sacrifice {g.name sac}"
    let outerCont? := g.pendingReplacement
    let g := if outerCont?.isSome then g.change (.pendingReplacement none) else g
    let g := (g.change (.pending .none)).sacrificeToGraveyard sac
      s!"{(g.player p).name} sacrifices {g.name sac}"
    return g.reattachOuterCont outerCont?
  | .maySacrificeAnotherBolg q bolgId =>
    if p != q then
      throw s!"Only {(g.player q).name} may sacrifice"
    let some sac := g.findObject? id | throw "no such object"
    if !sac.isOnBattlefield || !g.isCreature sac || !g.controlledBy sac p ||
        sac.id == bolgId then
      throw s!"Can't sacrifice {g.name sac} to Bolg"
    let outerCont? := g.pendingReplacement
    let g := if outerCont?.isSome then g.change (.pendingReplacement none) else g
    let bolgCause := some (EventCause.oneShotEffect none (some bolgId) (some p))
    let g := g.withBatch bolgCause fun g =>
      let g := g.sacrificeToGraveyard sac
        s!"{(g.player p).name} sacrifices {g.name sac} (Bolg)"
        (cause := bolgCause)
      if let .chooseReplacement .. := g.pending then g
      else g.change (.pending .none)
    return g.reattachOuterCont outerCont?
  | .payWard q spellId cost chosen =>
    if p != q then
      throw s!"Only {(g.player q).name} may sacrifice for ward"
    let some sac := g.findObject? id | throw "no such object"
    match cost.items.toList with
    | [.sacrifice (.count (.const n)) (.filter pred)] =>
      let need := if n > 0 then n.toNat else 1
      let env : EvalEnv := { controller := p }
      let legal := g.battlefield.filter fun o =>
        g.controlledBy o p && EvalExpr.evalObjectPred g env (.live o) pred
      if !sac.isOnBattlefield || !g.controlledBy sac p || chosen.contains id ||
          !legal.any (·.id == id) then
        throw s!"Can't sacrifice {g.name sac} to pay ward"
      if chosen.isEmpty && legal.size < need then
        throw s!"{(g.player p).name} can't sacrifice {need} permanents"
      let chosen' := chosen.push id
      if chosen'.size < need then
        return g.change (.pending (.payWard q spellId cost chosen'))
      else if need == 1 then
        let outerCont? := g.pendingReplacement
        let g := if outerCont?.isSome then g.change (.pendingReplacement none) else g
        let g := (g.change (.pending .none)).sacrificeToGraveyard sac
          s!"{(g.player p).name} sacrifices {g.name sac} (ward)"
          (cause := some (.costPayment .ward p (some spellId)))
        let g := g.reattachOuterCont outerCont?
        return g.afterWardResolved
      else
        let preBf := g.battlefield
        let wardCause := EventCause.costPayment .ward p (some spellId)
        let outerCont? := g.pendingReplacement
        let g := if outerCont?.isSome then g.change (.pendingReplacement none) else g
        let g := g.change (.pending .none)
        let g := g.withBatch (some wardCause) fun g =>
          g.sacrificePermanentsLoop (chosen'.map ((p, ·)))
            (preBattlefield := some preBf)
            (cause := some wardCause)
        let g := g.reattachOuterCont outerCont?
        return g.afterWardResolved
    | _ =>
      throw "Not time to sacrifice a permanent"
  | .maySacArtifactOrDiscard q n =>
    if p != q then
      throw s!"Only {(g.player q).name} may sacrifice"
    let some sac := g.findObject? id | throw "no such object"
    if !sac.isOnBattlefield || !g.isArtifact sac || !g.controlledBy sac p then
      throw s!"Can't sacrifice {g.name sac}"
    let outerCont? := g.pendingReplacement
    let g := if outerCont?.isSome then g.change (.pendingReplacement none) else g
    let g := (g.change (.pending .none)).sacrificeToGraveyard sac
      s!"{(g.player p).name} sacrifices {g.name sac}"
    let g := g.finishSacArtifactOrDiscardDraw p n
    return g.reattachOuterCont outerCont?
  | _ => throw "Not time to sacrifice a permanent"

/-- `p` discards `id` from their hand (CR 701.9 / 614.6). With `atRandom`, a
leading `"discards a card at random"` line is logged too. Logs only once the card
arrives in its owner's graveyard (CR 614.6 / 701.9a). -/
def discardFromHand (g : Game) (p : PlayerId) (id : ObjectId) (chooser : Option PlayerId := none)
    (cause : Option EventCause := none) (atRandom : Bool := false)
    (deferPlayFromExileLogs : Bool := false) :
    Game :=
  match g.findObject? id with
  | none => g
  | some card =>
    if card.zone != .hand p || !isDiscardableCard card then g
    else
      let owner := card.owner
      let msg :=
        match chooser with
        | some c => s!"{(g.player c).name} chooses {g.name card}. {(g.player p).name} discards it"
        | none => s!"{(g.player p).name} discards {g.name card}"
      let randomMsg := s!"{(g.player p).name} discards a card at random"
      let (g, _) := g.move id (.graveyard owner) none (verb := some .discard)
        (actor := some p) (cause := cause)
        (deferPlayFromExileLogs := deferPlayFromExileLogs)
      if let .chooseReplacement .. := g.pending then
        let g :=
          if atRandom then
            g.chainPendingReplacement (.finishPostStep (.logDiscardIfInGraveyard id owner randomMsg))
          else g
        g.chainPendingReplacement (.finishPostStep (.logDiscardIfInGraveyard id owner msg))
      else if (g.followMovedToZone? id (· == .graveyard owner)).isSome then
        let g := if atRandom then g.logMsg randomMsg else g
        g.logMsg msg
      else g

/-- `p` discards `id`, chosen at random (CR 701.9). -/
def discardFromHandRandomly (g : Game) (p : PlayerId) (id : ObjectId) : Game :=
  g.discardFromHand p id (atRandom := true)

/-- Ask the next player in `players` to sacrifice a creature, or sacrifice the
chosen creatures simultaneously in one batch and finish. -/
def continueSacrificeEach (g : Game) (controller : PlayerId) (players : Array PlayerId)
    (chosen : Array ObjectId) : Game :=
  match (players.filter (fun p => !(g.creaturesControlledBy p).isEmpty)).toList with
  | p :: rest =>
    g.beginResolutionChoice p (.sacrificeCreatureEach controller rest.toArray chosen)
      s!"{(g.player p).name} sacrifices a creature"
  | [] =>
    let youSacrificed := chosen.any (fun id =>
      (g.findObject? id).any (fun o => o.isOnBattlefield && g.controlledBy o controller))
    let pairs := chosen.filterMap (fun id =>
      match g.findObject? id with
      | some o =>
        if o.isOnBattlefield then some ((g.controllerOf o).getD o.owner, id)
        else none
      | none => none)
    let preBf := g.battlefield
    g.withBatch none fun g =>
      g.sacrificePermanentsLoop pairs (preBattlefield := some preBf)
        (createBeastFor := if youSacrificed then some controller else none)

/-- Count nonland cards actually discarded by each opponent in `oppIds` since
`startIdx` (CR 701.9c: face-up nonland cards moved from that opponent's hand to
a different public zone with `.discard`) and draw `baseDraws + shortCount`
cards for `controller` (CR 101.4 / 603.2c / 614.6 / 701.9b–c). -/
def finishDiscardTwoDraws (g : Game) (controller : PlayerId) (baseDraws : Nat)
    (oppIds : Array PlayerId) (startIdx : Nat) : Game :=
  let nonlandDiscardedBy (opp : PlayerId) : Nat :=
    (g.events.extract startIdx g.events.size).foldl (fun acc e =>
      match e.change with
      | .rules (.zone (.moved _ after (.hand q) toZone .discard _ _ _)) =>
        if q == opp && toZone != .hand q && isPublicZone toZone &&
            !after.faceDown && !after.types.contains .land then
          acc + 1
        else acc
      | _ => acc) 0
  let shortCount := (oppIds.filter (fun opp => g.stillInGame opp && nonlandDiscardedBy opp < 2)).size
  let totalDraws := baseDraws + shortCount
  if g.stillInGame controller && totalDraws > 0 then
    g.draw controller totalDraws
  else g

/-- Collect each living opponent's two-card discard choice in APNAP order, then
discard all chosen cards simultaneously inside one shared batch and draw a card
for each opponent who didn't discard two nonland cards
(CR 101.4 / 603.2c / 614.6 / 701.9b–c). -/
partial def continueDiscardTwo (g : Game) (controller : PlayerId) (players : Array PlayerId)
    (draws : Nat) (chosen : Array (PlayerId × Array ObjectId) := #[]) : Game :=
  let living := players.filter g.stillInGame
  match living.toList with
  | [] =>
    let livingChosen := chosen.filter (fun (p, _) => g.stillInGame p)
    let oppIds := livingChosen.map Prod.fst
    let pairs := livingChosen.foldl (fun acc (p, ids) =>
      acc ++ ids.map (fun id => (p, id))) #[]
    let startIdx := g.events.size
    let g :=
      if pairs.isEmpty then g
      else
        g.withBatch none fun g =>
          g.discardMultiHandIdsLoop pairs (logEach := true)
    if let .chooseReplacement .. := g.pending then
      g.chainPendingReplacement
        (.finishPostStep (.finishDiscardTwoDraws controller draws oppIds startIdx))
    else
      g.finishDiscardTwoDraws controller draws oppIds startIdx
  | p :: rest =>
    let hand := g.discardableHandIds p
    if hand.size ≤ 2 then
      let g :=
        if hand.isEmpty then g.logMsg s!"{(g.player p).name} has no cards to discard" else g
      g.continueDiscardTwo controller rest.toArray draws (chosen.push (p, hand))
    else
      g.beginResolutionChoice p (.discardTwo controller rest.toArray draws chosen)
        s!"{(g.player p).name} discards two cards"

end Game
end Mtg.Engine
