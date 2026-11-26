import Mtg.Engine.Game.Activation

/-!
# Passing, paying, and conceding

`pay` while a cost is proposed, announcing optional additional generic
costs, `pass` (CR 117.3d), and `concede` (CR 104.3a).
-/

namespace Mtg.Engine
namespace Game

/-- Pay the locked-in cost (CR 601.2h / 602.2b). Spells and abilities that still
need an artifact or creature sacrificed, or a card discarded, wait for
that action. -/
def finishProposedSpell (g : Game) : Except String Game := do
  let some prop := g.proposedSpell | throw "No spell or ability is waiting to be paid for"
  let spend := g.proposedManaSpend prop
  if !(g.player prop.caster).manaPool.canPay prop.cost spend ||
      !g.sourceStillPayable prop ||
      !g.canPayLife prop.caster prop.payLife then
    return (← g.reverseProposedSpell? (resumeContinuation := true))
  let gSneak := if prop.kind == .spell then g.probeAfterUnpaidSneak prop else g
  if prop.needsSacrificeOther then
    let excludeId := prop.sourceId.getD prop.spellId
    if (gSneak.sacrificeCreatureOrArtifactChoices prop.caster excludeId).isEmpty then
      return (← g.reverseProposedSpell? (resumeContinuation := true))
  if prop.needsDiscardCard && (gSneak.discardableHandIds prop.caster).isEmpty then
    return (← g.reverseProposedSpell? (resumeContinuation := true))
  if prop.teamworkPaid && !prop.teamworkCreatures.isEmpty then
    let teamworkOk := prop.teamworkCreatures.all fun id =>
      (g.findObject? id).any fun o =>
        o.isOnBattlefield && g.isCreature o && g.controlledBy o prop.caster && !o.status.tapped
    if !teamworkOk then
      return (← g.reverseProposedSpell? (resumeContinuation := true))
  if let some quality := prop.needsBehold then
    let hasPerm := (g.permanentsOf prop.caster).any (fun o => g.hasSubtype o quality)
    let hasHand :=
      (g.player prop.caster).hand.any (fun id =>
        (g.findObject? id).any (fun card => isDiscardableCard card && g.hasSubtype card quality))
    if !(hasPerm || hasHand) then
      return (← g.reverseProposedSpell? (resumeContinuation := true))
  let countCantBeCountered (g : Game) :=
    ((g.player prop.caster).manaPool.units.filter (·.hasRider .cantBeCountered)).size
  let g ← g.withProposalActionM .costAction fun g0 => do
    let paid ← g0.payCost prop.caster prop.cost spend (forObject := some prop.spellId)
    let paid ←
      if prop.kind == .activatedAbility then pure paid
      else paid.payLifeCost prop.caster prop.payLife (forObject := some prop.spellId)
    let spentCantBeCountered := countCantBeCountered paid < countCantBeCountered g0
    pure <|
      match prop.kind, paid.findObject? prop.spellId with
      | .spell, some o =>
        if spentCantBeCountered then
          paid.createEffect (.uncounterableThisCast o.id)
            |>.logMsg s!"{paid.name o} can't be countered (Delighted Halfling)"
        else paid
      | _, _ => paid
  if prop.kind == .turnFaceUp && !prop.needsSacrificeOther && !prop.needsDiscardCard then
    let localOuter? := g.pendingReplacement
    let g0 := if localOuter?.isSome then g.change (.pendingReplacement none) else g
    let paused0 := match g0.pending with | .chooseReplacement .. => true | _ => false
    let willReverse := !paused0 && !g0.over && g0.proposedSpell.isSome && g0.proposalCheckpoint.isSome &&
      !(g0.stillInGame prop.caster &&
        (g0.findObject? prop.spellId).any (fun cur =>
          cur.isOnBattlefield && cur.status.faceDown && g0.controlledBy cur prop.caster))
    let (g, callerShouldResume) :=
      g0.completeTurnFaceUp prop.caster prop.spellId (hadOuterReplacement := localOuter?.isSome)
    let g :=
      if willReverse then g
      else
        match localOuter? with
        | some outer => g.chainProposalOuterCont prop.caster outer
        | none => g
    return if !willReverse && (callerShouldResume || (!g.over && g.pending == .none && localOuter?.isSome)) then
      g.resumeAfterBecomeCast
    else g
  if prop.kind == .activatedAbility then
    return (← g.beginActivationPayment prop)
  let openCont := g.proposalHadOpenContinuation
  g.finishProposedSpellCosts .teamwork (!prop.resolutionCast) false openCont

/-- Pay the proposed spell or ability (CR 601.2h / 602.2b). If the cost
cannot be paid, the action is reversed (CR 733.1). -/
def pay (g : Game) (p : PlayerId) : Except String Game := do
  match g.pending with
  | .activateManaAbilities caster =>
    if caster != p then
      throw s!"Only {(g.player caster).name} may pay (CR 601.2h)"
    g.finishProposedSpell
  | .chooseMode _ =>
    throw "Choose a mode first (CR 601.2b)"
  | .chooseX _ =>
    throw "Choose a value for X first (CR 107.3a / 601.2b)"
  | .chooseTargets _ =>
    throw "Choose a target first (CR 601.2c)"
  | .chooseAdditionalCost _ =>
    throw "Choose an additional cost first (CR 601.2b)"
  | .payWard q spellId cost _ =>
    if p != q then
      throw s!"Only {(g.player q).name} may pay ward"
    match cost.solePoisonCounters? with
    | some n =>
      let outerCont? := g.pendingReplacement
      let g := if outerCont?.isSome then g.change (.pendingReplacement none) else g
      let g := g.record
        (GameEvent.poisoned g.turnNumber p n (cause := .costPayment .ward p (some spellId)))
      let phrase :=
        if n == 1 then "a poison counter" else s!"{englishNumber n} poison counters"
      let g := g.logMsg s!"{(g.player p).name} gets {phrase} (ward)"
      return g.finishWardAndDrain outerCont?
    | none =>
      match cost.items.toList with
      | [.payLife (.const n)] =>
        if n < 0 then throw "Invalid ward life cost"
        let outerCont? := g.pendingReplacement
        let g := if outerCont?.isSome then g.change (.pendingReplacement none) else g
        let g ← g.payLifeCost p n.toNat (forObject := some spellId)
          (cause := some (.costPayment .ward p (some spellId)))
        return g.finishWardAndDrain outerCont?
      | _ => throw "No spell or ability is waiting to be paid for (CR 601.2h)"
  | _ => throw "No spell or ability is waiting to be paid for (CR 601.2h)"

/-- Prefer paying extra generic mana when the non-mana additional-cost
option cannot be paid. -/
def additionalCostChoosesGeneric (g : Game) (p : PlayerId) (prop : ProposedSpell) :
    Bool :=
  match g.findObject? prop.spellId with
  | none => true
  | some spell =>
    let face := g.baseCard spell
    let gSneak := g.probeAfterUnpaidSneak prop
    let hasSacChoice :=
      !(gSneak.sacrificeCreatureOrArtifactChoices p prop.spellId).isEmpty
    match g.additionalChoiceCostFor? spell face with
    | none => !hasSacChoice
    | some branches =>
      let behold? := branches.findSome? fun cs =>
        cs.items.findSome? fun | .behold q => some q | _ => none
      let hasDiscard := branches.any fun cs =>
        cs.items.any fun | .discard .. => true | _ => false
      match behold? with
      | some quality =>
        let hasPerm := (g.permanentsOf p).any (fun o => g.hasSubtype o quality)
        let hasHand :=
          (g.player p).hand.any (fun id =>
            (g.findObject? id).any (fun card => isDiscardableCard card && g.hasSubtype card quality))
        !(hasPerm || hasHand)
      | none =>
        if hasDiscard then (gSneak.discardableHandIds p).isEmpty
        else !hasSacChoice

/-- Announce whether to pay extra generic mana or the non-mana option
(sacrifice an artifact or creature, or discard a card) as an additional
cost (CR 601.2b), before targets (CR 601.2c). -/
def announceAdditionalCost (g : Game) (p : PlayerId) (payGeneric : Bool) :
    Except String Game := do
  match g.pending with
  | .chooseAdditionalCost q =>
    if p != q then
      throw s!"Only {(g.player q).name} may choose an additional cost (CR 601.2b)"
    let some prop := g.proposedSpell
      | throw "No spell is waiting for an additional cost (CR 601.2b)"
    let some spell := g.findObject? prop.spellId
      | throw "The spell left the stack"
    let baseFace := g.baseCard spell
    let costFace :=
      match prop.sneakAttacker, baseFace.sneakCost with
      | some _, some sc => { baseFace with manaCost := sc }
      | _, _ => baseFace
    let preSpell := { spell with
      id := prop.original.id
      zone := prop.original.zone
      exiledBy := prop.original.exiledBy
      controller := some p }
    let announceExtraGeneric (g : Game) (n : Nat) : Game :=
      let g := g.record (GameEvent.announced g.turnNumber spell.id
        (costs := #[.genericMana n]))
      let newCost := g.playManaCost preSpell costFace (ManaCost.ofGeneric n)
        (origPerm := prop.origPerm)
        (flashback := some (GameEvent.castWithFlashback g.events prop.spellId))
        (explicitAltCost := prop.sneakAttacker.isSome)
        (useImplicitPermissions := false)
      g.changeProposals #[
        .cost newCost,
        .additionalGeneric n,
        .needsBehold none,
        .needsSacrificeOther false,
        .needsDiscardCard false ]
        |>.logMsg
          s!"{(g.player p).name} chooses to pay \{{n}} as an additional cost (CR 601.2b)"
    let some branches := g.additionalChoiceCostFor? spell baseFace
      | throw "That spell has no alternative additional cost"
    let genericN : Nat :=
      (branches.findSome? CostSpec.soleGenericMana?).getD 0
    let behold? := branches.findSome? fun cs =>
      cs.items.findSome? fun | .behold quality => some quality | _ => none
    let hasSac := branches.any fun cs =>
      cs.items.any fun | .sacrifice .. => true | _ => false
    let hasDisc := branches.any fun cs =>
      cs.items.any fun | .discard .. => true | _ => false
    if payGeneric then
      return (announceExtraGeneric g genericN).afterAdditionalCostAnnounced
    else
      match behold? with
      | some quality =>
        let hasPerm := (g.permanentsOf p).any (fun o => g.hasSubtype o quality)
        let hasHand :=
          (g.player p).hand.any (fun id =>
            (g.findObject? id).any (fun card => isDiscardableCard card && g.hasSubtype card quality))
        if !(hasPerm || hasHand) then
          throw s!"{g.name spell} requires beholding a {quality}"
        let g := g.changeProposals #[
          .additionalGeneric 0,
          .needsBehold (some quality),
          .needsSacrificeOther false,
          .needsDiscardCard false ]
        let g := g.logMsg
          s!"{(g.player p).name} chooses to behold a {quality} as an additional cost (CR 601.2b)"
        return g.afterAdditionalCostAnnounced
      | none =>
        let gSneak := g.probeAfterUnpaidSneak prop
        if hasSac then
          if (gSneak.sacrificeCreatureOrArtifactChoices p prop.spellId).isEmpty then
            throw s!"{g.name spell} requires sacrificing an artifact or creature"
          let g := g.changeProposals #[
            .additionalGeneric 0,
            .needsBehold none,
            .needsSacrificeOther true,
            .needsDiscardCard false ]
          let g := g.logMsg
            s!"{(g.player p).name} chooses to sacrifice an artifact or creature (CR 601.2b)"
          return g.afterAdditionalCostAnnounced
        else if hasDisc then
          if (gSneak.discardableHandIds p).isEmpty then
            throw s!"{g.name spell} requires discarding a card"
          let g := g.changeProposals #[
            .additionalGeneric 0,
            .needsBehold none,
            .needsSacrificeOther false,
            .needsDiscardCard true ]
          let g := g.logMsg
            s!"{(g.player p).name} chooses to discard a card as an additional cost (CR 601.2b)"
          return g.afterAdditionalCostAnnounced
        else
          throw "That spell has no alternative additional cost"
  | _ => throw "Not time to choose an additional cost (CR 601.2b)"

def pass (g : Game) (p : PlayerId) : Except String Game := do
  if g.over then
    throw "The game is over"
  if g.pending != .none then
    throw "A required choice is still pending"
  if !g.playersReceivePriority then
    throw "No player receives priority right now (CR 117.3a / 514.3)"
  if g.priority != p then
    throw "You don't have priority"
  let g := g.logMsg s!"{g.player p |>.name} passes priority"
  let g := g.change (.consecutivePasses (g.consecutivePasses + 1))
  if g.consecutivePasses ≥ g.livingPlayers.size then
    let g := g.change (.consecutivePasses 0)
    if !g.stack.isEmpty then
      let g := g.resolveTop
      if let .chooseReplacement .. := g.pending then
        return if g.anyContinuationSettlesControlFlowFwd then g
          else g.chainPendingReplacement (.receivePriority g.activePlayer)
      if g.pending != .none || g.afterRandom != .none then
        return g
      return g.receivePriority g.activePlayer
    else
      return g.advanceStep
  else
    return g.change (.priority (g.nextLiving p))

def concede (g : Game) (p : PlayerId) : Game :=
  if !g.stillInGame p then g
  else
    let pl := g.player p
    let mates :=
      g.players.filter (fun m => m.id != p && g.stillInGame m.id && g.areTeammates p m.id) |>.map (·.id)
    let g := g.record (GameEvent.playerLost g.turnNumber p .conceded (cause := some (.gameRule .playerLeftGame)))
    let g := g.logMsg s!"{pl.name} concedes (CR 104.3a)"
    let g :=
      mates.foldl (fun acc mid =>
        let mpl := acc.player mid
        let acc := acc.record (GameEvent.playerLost acc.turnNumber mid .conceded
          (cause := some (.gameRule .playerLeftGame)))
        acc.logMsg s!"{mpl.name} concedes with their team (CR 810.8a)") g
    match g.decideGameIfFinished with
    | some finished => finished.completeActiveResolutions
    | none =>
      let wasPregame :=
        g.pregameRandom != .none || !g.mulliganToDeclare.isEmpty ||
          !g.willMulligan.isEmpty || !g.mulliganToBottom.isEmpty ||
          g.awaitingOpeningBegin ||
          match g.pending with
          | .declareMulligan _ => true
          | _ => false
      let wasIdlePriority := g.pending == .none && g.pendingPriority.isNone
      let savedPendingPrio := g.pendingPriority
      let wasAssigningCombatDamage : Option Bool :=
        match g.pending with
        | .assignCombatDamage _ fa => some fa
        | _ => none
      let midResolutionOrBatch :=
        g.currentBatch.isSome || g.pendingReplacement.isSome ||
          !g.outerPendingReplacements.isEmpty ||
          !g.continuations.isEmpty || g.currentInterpWait?.isSome
      g.concedePlayersLoop (#[p] ++ mates) wasPregame midResolutionOrBatch
        wasIdlePriority savedPendingPrio wasAssigningCombatDamage

end Game
end Mtg.Engine
