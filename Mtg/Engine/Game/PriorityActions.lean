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
  let allowElf := g.proposedAllowsElfRestricted prop
  let allowInst := g.proposedAllowsInstRestricted prop
  let allowHero := g.proposedAllowsHeroRestricted prop
  let allowVillain := g.proposedAllowsVillainRestricted prop
  let allowCant := g.proposedAllowsCantNonartifact prop
  let allowCreature := g.proposedAllowsCreatureRestricted prop
  let spend := g.proposedManaSpend prop
  if !(g.player prop.caster).manaPool.canPay prop.cost allowElf allowInst
        allowHero allowVillain allowCant allowCreature spend ||
      !g.sourceStillPayable prop ||
      !g.canPayLife prop.caster prop.payLife then
    return (← g.reverseProposedSpell? (resumeContinuation := true))
  if prop.needsSacrificeOther then
    let excludeId := prop.sourceId.getD prop.spellId
    if (g.sacrificeCreatureOrArtifactChoices prop.caster excludeId).isEmpty then
      return (← g.reverseProposedSpell? (resumeContinuation := true))
  if prop.needsDiscardCard && (g.player prop.caster).hand.isEmpty then
    return (← g.reverseProposedSpell? (resumeContinuation := true))
  let count (g : Game) (u : FraManaUse) :=
    ((g.player prop.caster).manaPool.fraRestricted.filter (·.2 == u)).size
  let g ← g.withProposalActionM .costAction fun g0 => do
    let paid ← g0.payCost prop.caster prop.cost allowElf allowInst
      allowHero allowVillain allowCant allowCreature spend (forObject := some prop.spellId)
    let spent (u : FraManaUse) := count paid u < count g0 u
    pure <|
      match prop.kind, paid.findObject? prop.spellId with
      | .spell, some o =>
        if spent .legendarySpell then
          paid.createEffect (.uncounterableThisCast o.id)
            |>.logMsg s!"{o.name} can't be countered (Delighted Halfling)"
        else paid
      | _, _ => paid
  if prop.kind == .activatedAbility then
    return (← g.beginActivationPayment prop)
  let outerCont? := g.pendingReplacement
  let openCont := g.proposalHadOpenContinuation
  let g ←
    match prop.sneakAttacker with
    | some a =>
      let g0 := if outerCont?.isSome then g.change (.pendingReplacement none) else g
      match g0.withProposalActionM .costAction (fun g => g.paySneak prop.caster prop.spellId a) with
      | .ok g =>
        let paused := match g.pending with | .chooseReplacement .. => true | _ => false
        pure (if !paused then
          match outerCont? with
          | some outer => g.chainPendingReplacement outer
          | none => g
        else g)
      | .error _ => return (← g.reverseProposedSpell? (resumeContinuation := true))
    | none => pure g
  match prop.kind, prop.needsSacrificeOther, prop.needsDiscardCard with
  | _, true, _ =>
    if let .chooseReplacement .. := g.pending then
      let g := (g.change (.consecutivePasses 0)).chainPendingReplacement
        (.restorePending (.sacrificePermanent prop.caster prop.spellId))
      let g :=
        match outerCont? with
        | some outer => g.chainPendingReplacement outer
        | none => g
      return g.logMsg
        s!"{(g.player prop.caster).name} must sacrifice an artifact or creature"
    else
      let g := g.changes #[.pending (.sacrificePermanent prop.caster prop.spellId), .consecutivePasses 0]
      return g.logMsg
        s!"{(g.player prop.caster).name} must sacrifice an artifact or creature"
  | _, _, true =>
    if let .chooseReplacement .. := g.pending then
      let g := (g.change (.consecutivePasses 0)).chainPendingReplacement
        (.restorePending (.discardForAdditionalCost prop.caster))
      let g :=
        match outerCont? with
        | some outer => g.chainPendingReplacement outer
        | none => g
      return g.logMsg
        s!"{(g.player prop.caster).name} must discard a card"
    else
      let g := g.changes #[.pending (.discardForAdditionalCost prop.caster), .consecutivePasses 0]
      return g.logMsg
        s!"{(g.player prop.caster).name} must discard a card"
  | _, _, _ =>
    let paused := match g.pending with | .chooseReplacement .. => true | _ => false
    let clearPending : Array EngineChange :=
      if paused then #[] else #[.pending .none]
    let g := g.changes (clearPending ++ #[.proposedSpell none, .consecutivePasses 0])
    let g := g.becomeCast prop.caster (g.object! prop.spellId)
      (hadOuterReplacement := outerCont?.isSome)
      (hadOpenContinuation := some openCont)
    let g :=
      if paused then
        match outerCont? with
        | some outer => g.chainPendingReplacement outer.ensureEndsWithFinishFra
        | none => g
      else g
    return g.resumeAfterBecomeCast

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
  | .payWard q _ .fivePoison =>
    if p != q then
      throw s!"Only {(g.player q).name} may pay ward"
    let g := g.record
      (GameEvent.poisoned g.turnNumber p 5 (cause := .costPayment .ward p))
    let g := g.logMsg s!"{(g.player p).name} gets five poison counters (ward)"
    return g.afterWardResolved
  | _ => throw "No spell or ability is waiting to be paid for (CR 601.2h)"

/-- Prefer paying extra generic mana when the non-mana additional-cost
option cannot be paid. -/
def additionalCostChoosesGeneric (g : Game) (p : PlayerId) (prop : ProposedSpell) :
    Bool :=
  match g.findObject? prop.spellId with
  | none => true
  | some spell =>
    let face := g.baseCard spell
    if face.additionalCostBeholdOrPay.isSome then
      match face.additionalCostBeholdOrPay with
      | some (quality, _) =>
        let hasPerm := (g.permanentsOf p).any (fun o => g.hasSubtype o quality)
        let hasHand :=
          (g.player p).hand.any (fun id =>
            match g.findObject? id with
            | some card => g.hasSubtype card quality
            | none => false)
        !(hasPerm || hasHand)
      | none => true
    else if face.additionalCostDiscardOrPayGeneric.isSome then
      (g.player p).hand.isEmpty
    else
      (g.sacrificeCreatureOrArtifactChoices p prop.spellId).isEmpty

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
    match (g.baseCard spell).additionalCostBeholdOrPay with
    | some (quality, n) =>
      if payGeneric then
        let g := g.changeProposals #[
          .addGenericCost n,
          .needsSacrificeOther false,
          .needsDiscardCard false ]
        let g := g.logMsg
          s!"{(g.player p).name} chooses to pay \{{n}} as an additional cost (CR 601.2b)"
        return g.afterAdditionalCostAnnounced
      else
        let g := g.withProposalAction .costAction fun g =>
          g.beholdQuality p quality
            (cause := some (.costPayment .behold p (some prop.spellId)))
        if !(g.qualityWasBeheld p quality) then
          throw s!"{spell.name} requires beholding a {quality}"
        return g.afterAdditionalCostAnnounced
    | none =>
    let face := g.baseCard spell
    match face.additionalCostOrPayGeneric,
          face.additionalCostDiscardOrPayGeneric with
    | some n, _ =>
      if payGeneric then
        let g := g.changeProposals #[
          .addGenericCost n,
          .needsSacrificeOther false,
          .needsDiscardCard false ]
        let g := g.logMsg
          s!"{(g.player p).name} chooses to pay \{{n}} as an additional cost (CR 601.2b)"
        return g.afterAdditionalCostAnnounced
      else
        if (g.sacrificeCreatureOrArtifactChoices p prop.spellId).isEmpty then
          throw s!"{spell.name} requires sacrificing an artifact or creature"
        let g := g.changeProposals #[
          .needsSacrificeOther true,
          .needsDiscardCard false ]
        let g := g.logMsg
          s!"{(g.player p).name} chooses to sacrifice an artifact or creature (CR 601.2b)"
        return g.afterAdditionalCostAnnounced
    | none, some n =>
      if payGeneric then
        let g := g.changeProposals #[
          .addGenericCost n,
          .needsSacrificeOther false,
          .needsDiscardCard false ]
        let g := g.logMsg
          s!"{(g.player p).name} chooses to pay \{{n}} as an additional cost (CR 601.2b)"
        return g.afterAdditionalCostAnnounced
      else
        if (g.player p).hand.isEmpty then
          throw s!"{spell.name} requires discarding a card"
        let g := g.changeProposals #[
          .needsSacrificeOther false,
          .needsDiscardCard true ]
        let g := g.logMsg
          s!"{(g.player p).name} chooses to discard a card as an additional cost (CR 601.2b)"
        return g.afterAdditionalCostAnnounced
    | none, none => throw "That spell has no alternative additional cost"
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
    if !g.stack.isEmpty then
      let g := g.resolveTop
      if let .chooseReplacement .. := g.pending then
        return g.chainPendingReplacement (.receivePriority g.activePlayer)
      if g.pending != .none then
        return g
      return g.receivePriority g.activePlayer
    else
      return g.advanceStep
  else
    return g.change (.priority (g.nextLiving p))

def concede (g : Game) (p : PlayerId) : Game :=
  if (g.player p).lost then g
  else
    let pl := g.player p
    let g := g.record (GameEvent.playerLost g.turnNumber p .conceded (cause := some (.gameRule .playerLeftGame)))
    let g := g.logMsg s!"{pl.name} concedes (CR 104.3a)"
    match g.decideGameIfFinished with
    | some finished => finished
    | none => g.playerLeavesGame p |>.checkSBA

end Game
end Mtg.Engine
