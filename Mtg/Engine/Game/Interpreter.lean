import Mtg.Engine.Game.ResolutionCompat

/-!
# Unified `Instruction` Interpreter & `stepEnv` (CR 608 / 614.6 / 616.1)

Single resumable continuation-stack interpreter for all Phase-8 `Instruction`
bodies across spells, activated abilities, Saga chapters, and migrated
triggered abilities (HOB, HOC, MSH, FRA, FRC, Supported).

Key properties:
- **Lexical `stepEnv` (CR 608.2c / 614.6)**: `Instruction.bind v step body`
  allocates a fresh `EffectId`, records `startEventIdx`, runs `step`, then
  summarizes post-replacement `RulesEvent`s in `g.events[startEventIdx..]`
  matching `EventCause.oneShotEffectId? == some eid` into a `StepOutcome`
  bound to `v` in `ContinuationFrame.stepEnv` before running `body`.
- **Full pause/resume across replacements, interactive choices, and random
  ordering**:
  - `Pending.chooseReplacement` chains `PendingReplacement.continueInterpreter st`.
  - Interactive `Pending` choices stash `some st` in `ContinuationFrame.interpWait?`
    and resume via `Game.resumeInterpWaitIfReady` when `g.pending == .none`.
  - `Pending.randomOrder` stashes `some st` in `interpWait?` with
    `AfterRandom.continueInterpreter`.
-/

namespace Mtg.Engine
namespace Game

/-! ### `FraNext.toEffect` (replacing retired `FraNext.toResolution`) -/

/-- Convert a deferred `FraNext` follow-up action into a unified Phase-8 `Effect`. -/
def fraNextToEffect : FraNext → Effect
  | .searchBasicLandTapped => Effect.searchBasicLandTapped
  | .searchLandsTapped n =>
    { body := .player (.searchLibrary {
        filter := .hasType .land
        count := .upTo (.const (Int.ofNat n))
        dest := .battlefield .controller
        mods := { tapped := true } })
      phrase := s!"Search your library for up to {n} land cards, put them onto the battlefield tapped, then shuffle" }
  | .searchEnchantmentToHand =>
    { body := .player (.searchLibrary {
        filter := .hasType .enchantment
        count := .upTo (.const 1)
        dest := .hand .controller })
      phrase := "Search your library for an enchantment card, reveal it, put it into your hand, then shuffle" }
  | .tappedHeartwoods n =>
    { body := Instruction.createTokensFixed .heartwood n (tapped := true)
      phrase := s!"Create {n} tapped Heartwood tokens" }
  | .eachOpponentSacrificesCreature =>
    { body := .forEach (.eachPlayer .opponent) ⟨0⟩
        (.moveZone
          (.inZones .battlefield (.all #[.hasType .creature, .controlledBy (.ofExpr (.stepPlayers ⟨0⟩))]))
          .graveyard .sacrifice
          { choice? := some { chooser := .player (.stepPlayers ⟨0⟩), count := .exact (.const 1) } })
      phrase := "Each opponent sacrifices a creature" }
  | .drawThenCountersPerDiscard =>
    { body := .seq #[
        Instruction.drawFixed 1 .you,
        Instruction.putCounters .triggerSubject .plusOnePlusOne (.playerMetric .cardsDiscardedThisTurn .you)
      ]
      phrase := "Draw a card, then put a +1/+1 counter on that creature for each card you've discarded this turn" }
  | .eyeOfJaceCheck =>
    { body := Instruction.ifThen
        (.cmp .ge (.playerMetric .graveyardSize .you) (.const 7))
        (.seq #[
          .moveZone .this .graveyard .sacrifice {},
          Instruction.dealDamageFixed (.players .opponents) 2,
          .life (.gain .you (.const 2))
        ])
      phrase := "If there are seven or more cards in your graveyard, sacrifice this artifact, it deals 2 damage to each opponent, and you gain 2 life" }
  | .reflexiveDamageAnyTarget n =>
    { body := .queueReflexiveTrigger (TriggeredAbility.mkTrigger .thisEnters {
        targeting := .of .anyTarget
        body := Instruction.dealDamageFixed (.targetSlot 0) n
        phrase := s!"This deals {n} damage to any target" })
      phrase := s!"When you do, this deals {n} damage to any target" }
  | .reflexiveDestroyPerOpponent =>
    { body := .queueReflexiveTrigger (TriggeredAbility.mkTrigger .thisEnters {
        targeting := .of (.forEachOpponentControlled (.any #[.hasType .creature, .hasType .planeswalker]) (.upTo 1))
        allowsZeroTargets := true
        body := Instruction.destroy .allTargets
        phrase := "For each opponent, destroy up to one target creature or planeswalker that player controls" })
      phrase := "When you do, for each opponent, destroy up to one target creature or planeswalker that player controls" }
  | .reflexiveReturnLandTapped =>
    { body := .queueReflexiveTrigger (TriggeredAbility.mkTrigger .thisEnters {
        targeting := .of (.ofDomain (.object .yourGraveyard (ObjectPred.andAll #[.isKind .card, .hasType .land])))
        body := .moveZone (.target 0) (.battlefield .controller) .put { tapped := true }
        phrase := "Return target land card from your graveyard to the battlefield tapped" })
      phrase := "When you do, return target land card from your graveyard to the battlefield tapped" }
  | .beastToken =>
    { body := Instruction.createTokensFixed .beast44trample 1
      phrase := "Create a 4/4 green Beast creature token with trample" }
  | .proliferate times =>
    { body := .player (.proliferate .you (.const (Int.ofNat times)))
      phrase := s!"Proliferate {times} time(s)" }
  | .mshReflexive kind paid =>
    { resolution? := some (.queueMshReflexive kind paid) }
  | .gainLife n =>
    { body := Instruction.gainLifeFixed n
      phrase := s!"You gain {n} life" }
  | .returnSourceToHand =>
    { body := Instruction.bounce .this
      phrase := "Return this card to its owner's hand" }

/-! ### CR 614.6 Event-Slice `StepOutcome` Summarization -/

private def pushUniq {α : Type} [BEq α] (xs : Array α) (x : α) : Array α :=
  if xs.contains x then xs else xs.push x

/-- Summarize post-replacement `RulesEvent`s recorded in `g.events[startIdx..]`
whose `EventCause.oneShotEffectId?` matches `eid` (CR 608.2c / 614.6). Events
explicitly tagged with a different `EffectId` are excluded; untagged events from
interactive sub-choices inside the bound scope are included when no other
`EffectId` claims them. `override?` merges explicit choice/excess metadata. -/
def summarizeStepOutcome (g : Game) (startIdx : Nat) (eid : EffectId)
    (override? : Option StepOutcome := none) : StepOutcome := Id.run do
  let mut out : StepOutcome := {}
  let hi := g.events.size
  for i in [startIdx:hi] do
    let e := g.events[i]!
    let causeMatch : Bool :=
      match e.cause? with
      | none => true
      | some c =>
        match c.oneShotEffectId? with
        | some id => id == eid
        | none =>
          match c with
          | .stateBased _ | .turnBased _ => false
          | _ => true
    if causeMatch then
      match e.change with
      | .rules r =>
        match r with
        | .zone (.moved before after _ _ _ _ _ _) =>
          out := { out with movedCount := out.movedCount + 1, succeeded := true }
          if let some oid := after.id.orElse (fun _ => before.id) then
            out := { out with objects := pushUniq out.objects oid }
          let pw := (before.power.orElse (fun _ => after.power)).getD 0
          out := { out with sumPower := out.sumPower + pw }
        | .zone (.created eo _) =>
          out := { out with createdCount := out.createdCount + 1, succeeded := true }
          if let some oid := eo.id then
            out := { out with objects := pushUniq out.objects oid }
          out := { out with sumPower := out.sumPower + eo.power.getD 0 }
        | .damage (.dealt pkts) =>
          for pkt in pkts do
            if pkt.amount > 0 then
              out := { out with damageDealt := out.damageDealt + pkt.amount, succeeded := true }
              match pkt.recipient with
              | .permanent eo | .battle eo =>
                if let some oid := eo.id then
                  out := { out with objects := pushUniq out.objects oid }
              | .player pid =>
                out := { out with players := pushUniq out.players pid }
        | .life (.gained p n) =>
          if n > 0 then
            out := { out with
              lifeChanged := out.lifeChanged + Int.ofNat n
              players := pushUniq out.players p
              succeeded := true }
        | .life (.lost p n _ _) =>
          if n > 0 then
            out := { out with
              lifeChanged := out.lifeChanged + Int.ofNat n
              players := pushUniq out.players p
              succeeded := true }
        | .permanent (.counters (.object eo) _ (.put n) _)
        | .permanent (.counters (.object eo) _ (.removed n) _) =>
          if n > 0 then
            out := { out with countersChanged := out.countersChanged + Int.ofNat n, succeeded := true }
            if let some oid := eo.id then
              out := { out with objects := pushUniq out.objects oid }
        | .permanent (.counters (.player p) _ (.put n) _)
        | .permanent (.counters (.player p) _ (.removed n) _) =>
          if n > 0 then
            out := { out with
              countersChanged := out.countersChanged + Int.ofNat n
              players := pushUniq out.players p
              succeeded := true }
        | .permanent (.tapped eo _) | .permanent (.untapped eo)
        | .permanent (.transformed eo _) | .permanent (.turnedFaceUp eo)
        | .permanent (.phasedOut eo _) | .permanent (.phasedIn eo _) =>
          out := { out with succeeded := true }
          if let some oid := eo.id then
            out := { out with objects := pushUniq out.objects oid }
        | .permanent (.attached att _) =>
          out := { out with succeeded := true }
          if let some oid := att.id then
            out := { out with objects := pushUniq out.objects oid }
        | .player (.scried p ..) | .player (.surveilled p ..)
        | .player (.proliferated p ..) | .player (.ringTempted p ..) =>
          out := { out with players := pushUniq out.players p, succeeded := true }
        | .player (.searched p _ found) =>
          let objs := found.foldl pushUniq out.objects
          out := { out with
            players := pushUniq out.players p
            objects := objs
            succeeded := out.succeeded || !found.isEmpty }
        | .player (.revealed p ids) =>
          let objs := ids.foldl pushUniq out.objects
          out := { out with
            players := pushUniq out.players p
            objects := objs
            succeeded := out.succeeded || !ids.isEmpty }
        | .stackObject (.copied _ copy _) =>
          out := { out with createdCount := out.createdCount + 1, succeeded := true }
          if let some oid := copy.id then
            out := { out with objects := pushUniq out.objects oid }
        | .cast (.spellCast eo p _) =>
          out := { out with players := pushUniq out.players p, succeeded := true }
          if let some oid := eo.id then
            out := { out with objects := pushUniq out.objects oid }
        | _ => pure ()
      | .engine _ => pure ()
  match override? with
  | none => return out
  | some ov =>
    if ov == {} then
      return {}
    else
      return {
        objects := if ov.objects.isEmpty then out.objects else ov.objects
        players := if ov.players.isEmpty then out.players else ov.players
        movedCount := max out.movedCount ov.movedCount
        createdCount := max out.createdCount ov.createdCount
        damageDealt := max out.damageDealt ov.damageDealt
        excessDamage := max out.excessDamage ov.excessDamage
        lifeChanged := if ov.lifeChanged != 0 then ov.lifeChanged else out.lifeChanged
        countersChanged := if ov.countersChanged != 0 then ov.countersChanged else out.countersChanged
        sumPower := if ov.sumPower != 0 then ov.sumPower else out.sumPower
        chosenNumber := if ov.chosenNumber != 0 then ov.chosenNumber else out.chosenNumber
        chosenSubtype? := ov.chosenSubtype?.orElse (fun _ => out.chosenSubtype?)
        chosenParity? := ov.chosenParity?.orElse (fun _ => out.chosenParity?)
        chosenKeywords := if ov.chosenKeywords.isEmpty then out.chosenKeywords else ov.chosenKeywords
        succeeded := out.succeeded || ov.succeeded
      }

/-! ### Target Slot Construction & CR 608.2b Validation -/

/-- Partition flat announced `targets` into per-slot arrays using `spec` and
`skippedOptionalSlots`, validating each target against its slot at resolution
entry (CR 608.2b). Returns `(legalSlots, illegalTargets)`. -/
def buildLegalTargetSlots (g : Game) (controller : PlayerId) (spec : TargetSpec)
    (targets : Array Target) (sourceId : Option ObjectId)
    (skipped : Array Nat := #[]) : Array (Array Target) × Array Target := Id.run do
  let stackSelf := g.resolvingAbility.orElse (fun _ => g.resolvingSpell)
  if spec.slots.isEmpty then
    return (#[targets], #[])
  let mut slotsOut : Array (Array Target) := #[]
  let mut illegals : Array Target := #[]
  let mut pos : Nat := 0
  let numSlots := spec.slots.size
  for i in [0:numSlots] do
    let slot := spec.slots[i]!
    if skipped.contains i then
      slotsOut := slotsOut.push #[]
    else
      let maxTake : Nat :=
        if i + 1 == numSlots then targets.size - pos
        else
          match slot.count with
          | .exact n | .upTo n => n
          | .between _ hi => hi
          | .anyNumber => targets.size - pos
      let legal := g.legalTargetsForSlot controller slot sourceId stackSelf
      let isLegalTarget (t : Target) : Bool :=
        legal.contains t ||
          (g.stack.isEmpty && slot.targetsStackSpell &&
            match t with
            | .card id => (g.findObject? id).any (·.zone == .stack)
            | _ => false)
      let skippedImplicitly : Bool :=
        slot.allowsZero && targets.size - pos < numSlots - i && i + 1 < numSlots && pos < targets.size &&
          !isLegalTarget targets[pos]! &&
          (g.legalTargetsForSlot controller spec.slots[i + 1]! sourceId stackSelf).contains targets[pos]!
      if skippedImplicitly then
        slotsOut := slotsOut.push #[]
      else
        let mut slotLegal : Array Target := #[]
        let take := min maxTake (targets.size - pos)
        for _ in [0:take] do
          if pos < targets.size then
            let t := targets[pos]!
            pos := pos + 1
            if isLegalTarget t then
              slotLegal := slotLegal.push t
            else
              illegals := illegals.push t
        slotsOut := slotsOut.push slotLegal
  return (slotsOut, illegals)

/-! ### Evaluation Helpers for `InterpCtx` -/

private def interpCause (g : Game) (ctx : InterpCtx) : EventCause :=
  if ctx.oneShotEffectId.raw != 0 then
    .oneShotEffect (some ctx.oneShotEffectId) ctx.sourceId (some ctx.controller)
  else
    g.resolveOptionalCause none (fallbackSrc := ctx.sourceId) (fallbackCtrl := some ctx.controller)

private def interpEnv (g : Game) (ctx : InterpCtx) : EvalEnv :=
  let base := EvalEnv.ofInterpCtx g ctx
  let srcSnap0 :=
    ctx.sourceSnapshot.orElse fun _ => ctx.sourceId.bind g.lastKnownBefore?
  let srcSnap :=
    match ctx.lastKnownPower, ctx.lastKnownToughness with
    | none, none => srcSnap0
    | p?, t? =>
      match srcSnap0 with
      | some eo =>
        some { eo with
          power := p?.orElse (fun _ => eo.power)
          toughness := t?.orElse (fun _ => eo.toughness) }
      | none =>
        some { (default : EventObject) with
          id := ctx.sourceId, owner := ctx.controller, controller := some ctx.controller,
          types := #[.creature], power := p?, toughness := t? }
  let trigSnap :=
    ctx.triggerSubjectSnapshot.orElse fun _ => ctx.triggerSubjectId.bind g.lastKnownBefore?
  let costPaid :=
    if !base.costPaidObjects.isEmpty then base.costPaidObjects
    else (g.resolvingAbility.map g.boastExiledOf).getD #[]
  let eventAmt :=
    if ctx.lastKnownPower.isSome then base.eventAmount
    else (g.resolvingAbility.bind g.lastKnownPowerOf?).getD base.eventAmount
  { base with
    sourceSnapshot := srcSnap
    triggerSubjectSnapshot := trigSnap
    costPaidObjects := costPaid
    eventAmount := eventAmt }

private def evalInterpCountRange (g : Game) (env : EvalEnv) (r : ExprCountRange) : Nat × Nat :=
  match r with
  | .exact v =>
    let n := (EvalExpr.evalValue g env v).toNat
    (n, n)
  | .upTo v => (0, (EvalExpr.evalValue g env v).toNat)
  | .between lo hi =>
    ((EvalExpr.evalValue g env lo).toNat, (EvalExpr.evalValue g env hi).toNat)
  | .anyNumber => (0, 1000)

private def resolveDestPlayer (g : Game) (env : EvalEnv) (o : GameObject) (who : DestOwnerSpec) :
    PlayerId :=
  match who with
  | .owner => o.owner
  | .controller => env.controller
  | .player pe => (EvalExpr.evalPlayer g env pe)[0]?.getD env.controller

private def resolveLiveObjects (g : Game) (env : EvalEnv) (expr : ObjectExpr) : Array GameObject :=
  (EvalExpr.evalObjects g env expr).filterMap ObjectView.live?

private def resolveObjectIds (g : Game) (env : EvalEnv) (expr : ObjectExpr) : Array ObjectId :=
  (EvalExpr.evalObjects g env expr).filterMap ObjectView.id?

private def resolvePlayPerm (g : Game) (env : EvalEnv) (spec : GrantPlayPermSpec) :
    PlayPermission × EffectDuration :=
  let dur := (EvalExpr.evalDuration g env spec.duration).getD .untilEndOfTurn
  let whileEx :=
    match spec.duration with
    | .whileInZone _ .exile | .indefinite => true
    | _ =>
      match dur with | .whileInZone _ .exile | .indefinite => true | _ => false
  let reqSub? : Option CardSubtype :=
    match spec.condition? with
    | some (.exists (.inZones .battlefield (.all #[.hasSubtype (.literal sub), .controlledBy .you]))) =>
      some sub
    | _ => none
  let perm : PlayPermission := {
    player := env.controller
    whileExiled := whileEx
    withoutManaCost := spec.freeCast
    payLifeEqualManaValue := spec.payLifeInsteadOfMana
    anyMana := spec.anyManaColor
    requireSubtype := reqSub?
    ignoreTiming := spec.freeCast
  }
  (perm, dur)

private def grantPlayPermToMoved (g : Game) (env : EvalEnv) (fromId : ObjectId)
    (spec : GrantPlayPermSpec) (cause : EventCause) : Game :=
  match g.followMovedToZone? fromId (· == .exile) with
  | none => g
  | some moved =>
    if !g.stillInGame env.controller then g
    else if spec.asFlashback then
      g.createEffect (.flashbackUntilEot moved.id) (cause := some cause)
    else
      let (perm0, dur0) := resolvePlayPerm g env spec
      let (perm, dur) : PlayPermission × EffectDuration :=
        match spec.duration with
        | .whileInZone _ .exile | .indefinite =>
          ({ perm0 with whileExiled := true }, EffectDuration.whileInZone moved.id .exile)
        | _ => (perm0, dur0)
      let turnEnds :=
        match dur with
        | .untilEndOfNextTurnOf _ => 2
        | .whileInZone _ .exile | .indefinite => 0
        | _ => 1
      g.createEffect (.playPermission moved.id perm (turnEnds := turnEnds) (d := dur))
        (cause := some cause)

/-! ### Action Family 1: `moveZone` -/

private def applyEnterModsToMoved (g : Game) (env : EvalEnv) (ctx : InterpCtx)
    (enteredId : ObjectId) (mods : MoveMods) (cause : EventCause) : Game :=
  match g.findObject? enteredId with
  | none => g
  | some entered =>
    if !entered.isOnBattlefield then g
    else
      let g :=
        if mods.goaded then
          g.record (GameEvent.designation g.turnNumber (g.snapshot entered)
            (.goaded ctx.controller false) true (cause := cause))
        else g
      let g :=
        if !mods.enterKeywords.isEmpty then
          g.grantKeywordsUntilEot (g.object! enteredId) mods.enterKeywords
        else g
      let g :=
        if mods.enterLoseAllAbilities then
          g.createEffect (.layered (.objects #[enteredId]) (.abilities {} .all) .indefinite) (cause := some cause)
        else g
      let g :=
        match mods.enterTypeMod? with
        | some tm =>
          g.createEffect (.layered (.objects #[enteredId])
            (.types tm.mode tm.types tm.subtypes tm.supertypes tm.removeTypes) .indefinite) (cause := some cause)
        | none => g
      let g :=
        match mods.enterAsPredefined? with
        | some .food =>
          g.createEffect (.onlyFoodArtifact enteredId) (cause := some cause)
        | _ => g
      let g :=
        match mods.attachTo? with
        | some hostExpr =>
          match (resolveLiveObjects g env hostExpr)[0]? with
          | some host =>
            if host.isOnBattlefield then g.attachSourceTo (g.object! enteredId) host else g
          | none => g
        | none => g
      g

private def moveOneObject (g : Game) (env : EvalEnv) (ctx : InterpCtx) (o : GameObject)
    (dest : DestZoneSpec) (verb : ZoneVerb) (mods : MoveMods) (cause : EventCause) : Game :=
  let oName := g.name o
  match dest, verb with
  | .graveyard, .destroy =>
    if o.isOnBattlefield then g.destroyPermanent o (cause := some cause) else g
  | .graveyard, .sacrifice =>
    if o.isOnBattlefield then
      let msg :=
        if some o.id == ctx.sourceId then s!"{oName} is sacrificed"
        else s!"{(g.player (g.controllerOf o |>.getD ctx.controller)).name} sacrifices {oName}"
      g.sacrificeToGraveyard o msg (cause := some cause)
    else g
  | .graveyard, .discard =>
    let p := match o.zone with | .hand q => q | _ => o.owner
    g.discardFromHand p o.id (chooser := some ctx.controller) (cause := some cause)
  | .graveyard, _ =>
    let (g, _) := g.move o.id (.graveyard o.owner) none (verb := some verb) (cause := some cause)
    g
  | .hand toWho, _ =>
    let dstP := resolveDestPlayer g env o toWho
    if o.zone == .stack then g.returnStackSpell o.id
    else g.returnToHand o.id dstP (cause := some cause)
  | .exile, _ =>
    if mods.exileUntilSourceLeaves then
      if o.isOnBattlefield then g.exileUntilSourceLeaves ctx.sourceId o (cause := some cause)
      else g
    else
      match mods.delayedReturn? with
      | some (.immediately tapped under) =>
        let dstP := resolveDestPlayer g env o under
        if dstP == o.owner then
          g.exileThenReturn o s!"{oName} is exiled and returns to the battlefield"
            (tapped := tapped) (land := g.isLand o) (cause := some cause)
        else
          let (g, _) := g.move o.id .exile none (cause := some cause)
          match g.followMovedToZone? o.id (· == .exile) with
          | some moved =>
            let (g, newId) := g.putOntoBattlefield moved.id dstP (tapped := tapped) (cause := some cause)
            let g := applyEnterModsToMoved g env ctx newId mods cause
            if let some ent := g.findObject? newId then
              if ent.isOnBattlefield then g.afterPermanentEnters ent else g
            else g
          | none => g
      | some (.atNextEndStep _ _) =>
        g.exileUntilNextEndStep o (cause := some cause)
      | some (.returnThenExileAtEndStep tapped under) =>
        let dstP := resolveDestPlayer g env o under
        let (g, _) := g.move o.id .exile none (cause := some cause)
        match g.followMovedToZone? o.id (· == .exile) with
        | some moved =>
          let (g, newId) := g.putOntoBattlefield moved.id dstP (tapped := tapped) (cause := some cause)
          let g := applyEnterModsToMoved g env ctx newId mods cause
          let src := (ctx.sourceId.bind g.findObject?).orElse (fun _ => g.findObject? newId)
          let g := g.registerDelayedTrigger { controller := ctx.controller, source := src, kind := .endStepExile newId, cause }
          if let some ent := g.findObject? newId then
            if ent.isOnBattlefield then g.afterPermanentEnters ent else g
          else g
        | none => g
      | some (.returnIfThenExileAtEndStep pred _tapped under) =>
        let ok := EvalExpr.evalObjectPred g env (.live o) pred
        let dstP := resolveDestPlayer g env o under
        let (g, _) := g.move o.id .exile none (cause := some cause)
        if let .chooseReplacement .. := g.pending then
          g.chainPendingReplacement
            (.finishPostStep (.exileReturnBrieflyAfterExile dstP o.id oName ok ctx.sourceId cause))
        else
          g.finishExileReturnBrieflyAfterExile dstP o.id oName ok ctx.sourceId cause
      | none =>
        let (g, _) := g.move o.id .exile none
          (faceDown? := if mods.enterFaceDown then some true else none) (cause := some cause)
        let g :=
          if mods.linkToSource then
            match ctx.sourceId, g.followMovedToZone? o.id (· == .exile) with
            | some sid, some moved =>
              if (g.findObject? sid).isSome then g.changeObject sid (.pushLinkedExile moved.id) else g
            | _, _ => g
          else g
        let g :=
          match mods.grantPlayPerm? with
          | some gp => grantPlayPermToMoved g env o.id gp cause
          | none => g
        if (g.followMovedToZone? o.id (· == .exile)).isSome then
          let impulseNextTurn := mods.grantPlayPerm?.any fun gp =>
            match gp.duration with | .untilEndOfNextTurnOf _ => true | _ => false
          if impulseNextTurn then
            g.logMsg s!"{(g.player ctx.controller).name} exiles {oName} and may play it until the end of their next turn"
          else
            g.logMsg s!"{oName} is exiled"
        else g
  | .battlefield under, _ =>
    let dstP := resolveDestPlayer g env o under
    let extraCounters : CounterBag := mods.enterCounters.filterMap fun (k, ve) =>
      let n := (EvalExpr.evalValue g env ve).toNat
      if n > 0 then some (k, n) else none
    let (g, newId) := g.putOntoBattlefield o.id dstP
      (tapped := mods.tapped) (extraEntersWith := extraCounters)
      (onlyFoodArtifact := mods.enterAsPredefined? == some .food) (cause := some cause)
    if let .chooseReplacement .. := g.pending then
      g.chainPendingReplacement
        (.finishPostStep (if mods.tapped then .returnedToBattlefieldTapped o.id false else .returnedToBattlefield o.id false))
    else
      let g := applyEnterModsToMoved g env ctx newId mods cause
      match g.findObject? newId with
      | some entered =>
        if entered.isOnBattlefield then
          let fromGyOrExile := match o.zone with | .graveyard _ | .exile => true | _ => false
          let verbTxt := if fromGyOrExile then "returns to" else "enters"
          let tappedTxt := if mods.tapped then " tapped" else ""
          let g := g.logMsg s!"{g.name entered} {verbTxt} the battlefield{tappedTxt}"
          g.afterPermanentEnters entered
        else g
      | none => g
  | .library whose pos ownerChoosesTopBottom, _ =>
    let dstP := resolveDestPlayer g env o whose
    if ownerChoosesTopBottom && o.isOnBattlefield then
      let topInstr : Instruction := .moveZone (.target 0) (.library whose pos false) verb { mods with choice? := none }
      let botInstr : Instruction := .moveZone (.target 0) (.library whose .bottom false) verb { mods with choice? := none }
      let eff : Effect := { targeting := .of ctx.targetSpec, body := topInstr }
      g.beginSpellOr ctx.controller eff #[.permanent o.id] [topInstr, botInstr] ctx.sourceId (libraryTopBottom := true)
    else
      let lpos := EvalExpr.evalLibraryPos g env pos
      let (g, _) := g.move o.id (.library dstP) none (verb := some verb) (libraryPosition := some lpos) (cause := some cause)
      let g :=
        if mods.shuffleAfter || verb == .shuffleIntoLibrary || lpos == .shuffledIn then
          let g :=
            if (g.followMovedToZone? o.id (· == .library dstP)).isSome then
              g.logMsg s!"{(g.player dstP).name} shuffles {oName} into their library"
            else g
          g.shuffleThen dstP .none
        else if (g.followMovedToZone? o.id (· == .library dstP)).isSome then
          let side := match lpos with | .top => "top" | .bottom => "bottom" | _ => "library"
          g.logMsg s!"{(g.player dstP).name} puts {oName} on the {side} of their library"
        else g
      g

private def execMoveZone (g : Game) (ctx : InterpCtx) (objs : ObjectExpr) (dest : DestZoneSpec)
    (verb : ZoneVerb) (mods : MoveMods) : Game :=
  let env := interpEnv g ctx
  let cause := interpCause g ctx
  -- Fast-path: mill top N of library via `Game.mill` (preserves CR 701.17 & replacement pauses)
  match objs, dest, verb with
  | .topOfLibrary whoExpr countExpr, .graveyard, .mill =>
    let n := (EvalExpr.evalValue g env countExpr).toNat
    let pids := EvalExpr.evalPlayer g env whoExpr
    pids.foldl (fun g p => g.mill p n (cause := some cause)) g
  | _, _, _ =>
    -- Handle interactive `MoveMods.choice?` (sacrifice/discard/put-from-hand/keep-destroy-rest)
    match mods.choice? with
    | some ch =>
      let chooser : PlayerId :=
        match ch.chooser with
        | .controller => ctx.controller
        | .owner => ctx.controller
        | .player pe => (EvalExpr.evalPlayer g env pe)[0]?.getD ctx.controller
      let cands := resolveLiveObjects g env objs
      let cands :=
        match ch.filter? with
        | some fp => cands.filter (fun o => EvalExpr.evalObjectPred g env (.live o) fp)
        | none => cands
      let cands : Array GameObject :=
        match ch.extremeMetric? with
        | none => cands
        | some (wantMax, metric) =>
          let scored : Array (GameObject × Int) := cands.filterMap fun o =>
            let val? : Option Int :=
              match metric with
              | .one => some 1
              | .stat sk => EvalExpr.viewStat? g (.live o) sk
              | .counterCount k? => some (Int.ofNat (EvalExpr.viewCounterCount (.live o) k?))
              | .colorCount => some (Int.ofNat (g.colors o).count)
            val?.map (o, ·)
          match scored[0]? with
          | none => #[]
          | some (_, v0) =>
            let best := scored.foldl (fun acc (_, v) => if wantMax then max acc v else min acc v) v0
            (scored.filter (·.2 == best)).map Prod.fst
      let (lo, hi) := evalInterpCountRange g env ch.count
      if ch.revealFirst then
        match verb, objs with
        | .discard, .inZones (.handOf victimExpr) pred =>
          let permanentOnly :=
            match pred with
            | .isKind .permanentCard => true
            | .all ps => ps.contains (.isKind .permanentCard)
            | _ => false
          match (EvalExpr.evalPlayer g env victimExpr)[0]? with
          | some victim =>
            let choices := g.revealedHandChoices victim permanentOnly
            if choices.size == 1 && lo == 1 && hi == 1 then
              let g := g.revealHand victim
              g.discardFromHand victim choices[0]! (chooser := some chooser)
            else
              g.beginRevealDiscard chooser victim permanentOnly
          | none => g
        | .exile, .inZones (.handOf victimExpr) _ =>
          match (EvalExpr.evalPlayer g env victimExpr)[0]? with
          | some victim =>
            let g := g.revealHand victim
            if (g.revealedHandChoices victim false).isEmpty then
              g.logMsg s!"{(g.player victim).name} has no nonland card"
            else
              g.beginFraChoice chooser (.exileFromRevealedHand victim ctx.sourceId)
                s!"{(g.player chooser).name} chooses a nonland card to exile"
          | none => g
        | _, _ =>
          let owner? : Option PlayerId := cands[0]?.map GameObject.owner
          let g :=
            match owner? with
            | some own =>
              let revNames := String.intercalate ", " (cands.toList.map g.name)
              (g.record (GameEvent.revealed g.turnNumber own (cands.map GameObject.id) (cause := some cause))).logMsg
                s!"{(g.player own).name} reveals {revNames}"
            | none => g
          let pick : Array GameObject := cands.extract 0 (min hi cands.size)
          g.withBatch (some cause) fun g =>
            pick.foldl (fun g (o : GameObject) =>
              match g.findObject? o.id with
              | some cur => moveOneObject g env ctx cur dest verb { mods with choice? := none } cause
              | none => g) g
      else if verb == .discard && !ch.invertSelection then
        let choosers : Array PlayerId :=
          match ch.chooser with
          | .controller | .owner => #[ctx.controller]
          | .player pe => EvalExpr.evalPlayer g env pe
        if ch.atRandom then
          if cands.isEmpty || hi == 0 then
            g.logMsg s!"{(g.player chooser).name} has no card to discard"
          else if cands.size == 1 then
            g.discardFromHandRandomly chooser cands[0]!.id
          else
            g.changes #[
              .pending (.resolveRandom (.chooseObject (cands.map (·.id)))),
              .afterRandom (.discardRandom chooser)]
        else if hi == 0 then
          g
        else if let some (.hasType ty) := ch.unlessMatching? then
          let g := g.changes #[.thirstDiscardsLeft lo, .thirstDiscardType ty]
          g.beginDiscardCards choosers
        else if ch.filter?.isNone then
          g.beginDiscardCards choosers lo
        else if cands.isEmpty then
          g.logMsg s!"{(g.player chooser).name} has no card to discard"
        else if cands.size ≤ lo then
          g.withBatch (some cause) fun g =>
            cands.foldl (fun g o =>
              match g.findObject? o.id with
              | some cur => g.discardFromHand chooser cur.id (cause := some cause)
              | none => g) g
        else
          g.beginDiscardCards choosers lo
      else if verb == .sacrifice && !ch.invertSelection then
        if cands.isEmpty || hi == 0 then
          g.logMsg s!"{(g.player chooser).name} has no permanent to sacrifice"
        else if cands.size ≤ lo then
          g.withBatch (some cause) fun g =>
            cands.foldl (fun g o =>
              match g.findObject? o.id with
              | some cur =>
                if cur.isOnBattlefield then
                  g.sacrificeToGraveyard cur s!"{(g.player chooser).name} sacrifices {g.name cur}" (cause := some cause)
                else g
              | none => g) g
        else if lo == 1 && hi == 1 && cands.all (g.isCreature ·) then
          g.beginSacrificeCreature chooser
        else
          let pick := cands.extract 0 lo
          g.withBatch (some cause) fun g =>
            pick.foldl (fun g o =>
              match g.findObject? o.id with
              | some cur =>
                if cur.isOnBattlefield then
                  g.sacrificeToGraveyard cur s!"{(g.player chooser).name} sacrifices {g.name cur}" (cause := some cause)
                else g
              | none => g) g
      else if ch.invertSelection && verb == .destroy then
        let ids := cands.map (·.id)
        g.offerCardChoice chooser ids hi .keepDestroyRest
          s!"{(g.player chooser).name} chooses up to {hi} creatures to keep" (cause := some cause)
      else if dest == .battlefield .controller && cands.all (fun o => o.zone == .hand chooser && g.isCreature o) then
        g.offerCardChoice chooser (cands.map (·.id)) hi .creaturesToBattlefield
          s!"{(g.player chooser).name} may put creature cards from their hand onto the battlefield"
          (cause := some cause)
      else
        let pick := cands.extract 0 (min hi cands.size)
        let g := g.withBatch (some cause) fun g =>
          pick.foldl (fun g o =>
            match g.findObject? o.id with
            | some cur => moveOneObject g env ctx cur dest verb { mods with choice? := none } cause
            | none => g) g
        match objs with
        | .linkedExile srcExpr =>
          let movedIds := pick.map (·.id)
          (resolveLiveObjects g env srcExpr).foldl (fun g src =>
            let g := g.changeObject src.id (.linkedExile (src.linkedExile.filter (!movedIds.contains ·)))
            g.changeObject src.id (.leaveTriggerExile (src.leaveTriggerExile.filter (!movedIds.contains ·)))) g
        | _ => g
    | none =>
      let targets :=
        let live := resolveLiveObjects g env objs
        if !live.isEmpty then live
        else
          -- CR 400.7c / 400.7e: Zone-change triggers moving `.triggerSubject` track the
          -- card into the public zone (graveyard/exile) it moved to.
          match objs with
          | .triggerSubject =>
            let rawIds :=
              if !ctx.triggerSubjectIds.isEmpty then ctx.triggerSubjectIds
              else match ctx.triggerSubjectId with | some id => #[id] | none => #[]
            rawIds.filterMap fun id =>
              g.followMovedToZone? id (fun
                | .graveyard _ | .exile => true
                | _ => false)
          | _ => #[]
      if targets.isEmpty then
        match objs, dest with
        | .this, _ => g.logMsg "The source is no longer in play"
        | .topOfLibrary whoExpr _, .exile =>
          if mods.grantPlayPerm?.isSome then
            (EvalExpr.evalPlayer g env whoExpr).foldl (fun g p =>
              g.logMsg s!"{(g.player p).name} has no cards in their library to exile") g
          else g
        | _, _ => g
      else if verb == .destroy && dest == .graveyard && targets.size > 1 then
        let preBf := g.battlefield
        let ids := targets.filterMap fun o => if o.isOnBattlefield then some o.id else none
        g.withBatch (some cause) fun g =>
          g.destroyPermanentsLoop ids (preBattlefield := some preBf) (cause := some cause)
      else if dest == .exile && mods.exileUntilSourceLeaves && targets.size > 1 then
        g.withBatch (some cause) fun g =>
          g.exileIdsUntilSourceLeavesLoop ctx.sourceId (targets.map (·.id)) (some cause)
      else if dest == .exile && mods.grantPlayPerm?.any (·.copyAndCast) then
        match mods.grantPlayPerm? with
        | some gp =>
          let (g, exiledIds) := g.withBatchReturn (some cause) fun g =>
            targets.foldl (fun (acc : Game × Array ObjectId) o =>
              let (g, xs) := acc
              match g.findObject? o.id with
              | some cur =>
                let oName := g.name cur
                let (g, _) := g.move cur.id .exile none (cause := some cause)
                match g.followMovedToZone? cur.id (· == .exile) with
                | some moved => (g.logMsg s!"{oName} is exiled", xs.push moved.id)
                | none => (g, xs)
              | none => (g, xs)) (g, #[])
          let (g, copies) := g.withBatchReturn (some cause) fun g =>
            exiledIds.foldl (fun (acc : Game × Array ObjectId) id =>
              let (g, cs) := acc
              match g.findObject? id with
              | some card =>
                if card.zone != .exile then (g, cs)
                else
                  let base := g.copiableValues card
                  let copyId : ObjectId := ⟨g.nextObjectId⟩
                  let copyObj : GameObject := {
                    id := copyId
                    printed := { base with
                      isToken := false
                      otherFace := base.otherFace.map (fun f => { f with isToken := false }) }
                    owner := ctx.controller
                    controller := some ctx.controller
                    zone := .exile
                    timestamp := g.timestamp + 1
                    isCopy := true
                  }
                  let g := g.record (GameEvent.created g.turnNumber ctx.controller (g.snapshot copyObj) (cause := cause))
                  let g := g.createEffect (.playPermission copyId {
                    player := ctx.controller, whileExiled := true,
                    withoutManaCost := gp.freeCast, ignoreTiming := true }) (cause := some cause)
                  (g, cs.push copyId)
              | none => (g, cs)) (g, #[])
          if copies.isEmpty then g
          else if gp.maxCasts? == some 1 && gp.maxTotalManaValue?.isNone && copies.size == 1 then
            let copyId := copies[0]!
            let copyName := (g.findObject? copyId).map g.name |>.getD "the card"
            g.beginFraChoice ctx.controller (.mayCastCopy copyId)
              s!"{(g.player ctx.controller).name} may cast the copy of {copyName} without paying its mana cost"
          else
            let maxMv := gp.maxTotalManaValue?.map (fun v => (EvalExpr.evalValue g env v).toNat) |>.getD 1000
            let maxCasts := gp.maxCasts?.getD copies.size
            g.beginFraChoice ctx.controller (.castCopiesFree copies maxMv maxCasts)
              s!"{(g.player ctx.controller).name} may cast copies without paying their mana costs"
        | none => g
      else
        g.withBatch (some cause) fun g =>
          targets.foldl (fun g o =>
            match g.findObject? o.id with
            | some cur => moveOneObject g env ctx cur dest verb mods cause
            | none => g) g

/-! ### Action Family 2: `create` -/

private def execCreate (g : Game) (ctx : InterpCtx) (op : CreateOp) : Game :=
  let env := interpEnv g ctx
  let cause := interpCause g ctx
  match op with
  | .tokens whoExpr countExpr spec mods =>
    let n := (EvalExpr.evalValue g env countExpr).toNat
    if n == 0 then g
    else
      let pids := EvalExpr.evalPlayer g env whoExpr
      let extraCounters : CounterBag := mods.counters.filterMap fun (k, ve) =>
        let c := (EvalExpr.evalValue g env ve).toNat
        if c > 0 then some (k, c) else none
      let copyCtx : CopyTokenContext := {
        sourceId := ctx.sourceId
        targetId :=
          match (ctx.targets[0]? : Option Target) with
          | some (.permanent tid) | some (.card tid) => some tid
          | _ => none
        triggerSubjectId := ctx.triggerSubjectId
      }
      pids.foldl (fun g p =>
        if !g.stillInGame p then g
        else
          let startIdx := g.events.size
          let g :=
            if mods.tapped || mods.attacking then
              match g.resolveTokenPrinted? spec ctx.chosenX copyCtx (controller := p) with
              | none => g.logMsg "no token is created (CR 111.5 / 111.12)"
              | some printed =>
                g.withBatch (some cause) fun g =>
                  (g.createToken p printed (tapped := mods.tapped) (attacking := mods.attacking)
                    (extraCounters := extraCounters) (recordRecent := true)
                    (cause := some cause) (count := n)).1
            else
              g.makeTokenSpecBatched p spec n ctx.chosenX extraCounters (some cause) copyCtx
          let createdIds := g.tokensCreatedSince startIdx
          let g := createdIds.foldl (fun g tid =>
            match g.findObject? tid with
            | none => g
            | some tok =>
              if !tok.isOnBattlefield then g
              else
                let g :=
                  if !mods.grantKeywordsUntilEot.isEmpty then
                    (g.createEffect (.keywordsUntilEot tok.id mods.grantKeywordsUntilEot) (cause := some cause))
                      |>.logMsg s!"{g.name tok} gains {KeywordAbility.joinedAnd mods.grantKeywordsUntilEot} until end of turn"
                  else g
                let g :=
                  if mods.goaded then
                    g.record (GameEvent.designation g.turnNumber (g.snapshot tok)
                      (.goaded ctx.controller false) true (cause := cause))
                  else g
                let g :=
                  match mods.attachTo? with
                  | some hostExpr =>
                    match (resolveLiveObjects g env hostExpr)[0]? with
                    | some host =>
                      if host.isOnBattlefield then g.attachSourceTo (g.object! tid) host else g
                    | none => g
                  | none => g
                let g :=
                  match mods.delayedAction? with
                  | some .sacrificeAtEndStep | some (.sacrificeAtEndStepUnless _) =>
                    g.registerDelayedTrigger { controller := p, source := some tok, kind := .endStepSacrifice tid, cause }
                  | some .exileAtEndStep | some .exileAtEndOfCombat =>
                    g.registerDelayedTrigger { controller := p, source := some tok, kind := .endStepExile tid, cause }
                  | none => g
                g) g
          g) g
  | .emblem whoExpr emb =>
    let pids := EvalExpr.evalPlayer g env whoExpr
    let srcName := g.fraSourceName ctx.sourceId
    let emblemCard : CardDef := {
      name := s!"{srcName} Emblem"
      types := #[]
      staticAbilities := emb.staticAbilities
      triggeredAbilities := emb.triggeredAbilities
      activatedAbilities := emb.activatedAbilities
    }
    pids.foldl (fun g p =>
      if !g.stillInGame p then g
      else
        (g.createCommandObject p emblemCard).logMsg s!"{(g.player p).name} gets an emblem") g

/-! ### Action Family 3: `permanent` -/

private def execPermanent (g : Game) (ctx : InterpCtx) (op : PermanentOp) : Game :=
  let env := interpEnv g ctx
  let cause := interpCause g ctx
  match op with
  | .setTapped objs tapped =>
    let live := (resolveLiveObjects g env objs).filter (·.isOnBattlefield)
    if live.isEmpty then g
    else
      g.withBatch (some cause) fun g =>
        live.foldl (fun g o =>
          match g.findObject? o.id with
          | some cur =>
            if !cur.isOnBattlefield then g
            else if tapped then g.becomeTapped cur (cause := some cause)
            else g.untapPermanentLogged cur (sourceId := ctx.sourceId)
          | none => g) g
  | .modifyCounters mode objs =>
    let live := (resolveLiveObjects g env objs).filter (·.isOnBattlefield)
    if live.isEmpty then
      if objs == .this then g.logMsg "The source is no longer in play" else g
    else
      g.withBatch (some cause) fun g =>
        live.foldl (fun g o =>
          match g.findObject? o.id with
          | none => g
          | some cur =>
            if !cur.isOnBattlefield then g
            else
              match mode with
              | .put kind countExpr =>
                let n := (EvalExpr.evalValue g env countExpr).toNat
                if n == 0 then g
                else if kind == .plusOnePlusOne then
                  g.addPlusOnePlusOneTo cur n (byPlayer := some ctx.controller) (cause := some cause)
                else
                  g.putCountersDeferredLog cur.id kind n (some ctx.controller) .isPutOn (cause := some cause)
              | .remove kind? range =>
                let (_, hi) := evalInterpCountRange g env range
                if hi == 0 then g
                else
                  match kind? with
                  | some k =>
                    let haveN := cur.status.counters.count k
                    let rem := min hi haveN
                    if rem == 0 then g
                    else g.recordRemoveCounters cur.id k rem (cause := some cause)
                  | none =>
                    -- Remove up to `hi` counters across all kinds present on `cur`
                    let bag := cur.status.toCounterBag
                    (bag.foldl (fun (acc : Game × Nat) (k, cnt) =>
                      if acc.2 == 0 then acc
                      else
                        let take := min acc.2 cnt
                        (acc.1.recordRemoveCounters cur.id k take (cause := some cause), acc.2 - take)) (g, hi)).1
              | .moveAll fromExpr kind? =>
                match (resolveLiveObjects g env fromExpr)[0]? with
                | none => g
                | some src =>
                  if !src.isOnBattlefield || !src.status.hasCounters then g
                  else
                    let bag := src.status.toCounterBag.filter fun (k, _) => kind?.all (· == k)
                    bag.foldl (fun g (k, cnt) =>
                      let g := g.recordRemoveCounters src.id k cnt (cause := some cause)
                      if k == .plusOnePlusOne then
                        match g.findObject? cur.id with
                        | some liveCur => g.addPlusOnePlusOneTo liveCur cnt (byPlayer := some ctx.controller) (cause := some cause)
                        | none => g
                      else
                        g.putCountersDeferredLog cur.id k cnt (some ctx.controller) .isPutOn (cause := some cause)) g
              | .moveOne fromExpr kind =>
                match (resolveLiveObjects g env fromExpr)[0]? with
                | none => g
                | some src =>
                  if !src.isOnBattlefield || src.status.counters.count kind == 0 then g
                  else
                    let g := g.recordRemoveCounters src.id kind 1 (cause := some cause)
                    if kind == .plusOnePlusOne then
                      match g.findObject? cur.id with
                      | some liveCur => g.addPlusOnePlusOneTo liveCur 1 (byPlayer := some ctx.controller) (cause := some cause)
                      | none => g
                    else
                      g.putCountersDeferredLog cur.id kind 1 (some ctx.controller) .isPutOn (cause := some cause)
              | .copyFromLki fromExpr =>
                let bag? : Option CounterBag :=
                  if fromExpr == .triggerSubject then
                    (g.resolvingAbilityObject?.bind (·.fraCauseStatus)).map (·.toCounterBag)
                      |>.orElse fun _ =>
                        (EvalExpr.evalObjects g env fromExpr)[0]?.map fun
                          | .live fo => fo.status.toCounterBag
                          | .lki eo => eo.counters
                  else
                    (EvalExpr.evalObjects g env fromExpr)[0]?.map fun
                      | .live fo => fo.status.toCounterBag
                      | .lki eo => eo.counters
                match bag? with
                | none => g
                | some bag =>
                  let dstBefore := cur.status.toCounterBag
                  let dstName := g.name cur
                  let g := bag.foldl (fun g (k, cnt) =>
                    if cnt == 0 then g
                    else if !(g.findObject? cur.id).any (·.isOnBattlefield) then g
                    else g.recordPutCounters cur.id k cnt (byPlayer := some ctx.controller) (cause := some cause)) g
                  let msg := s!"Counters are put on {dstName}"
                  if let .chooseReplacement .. := g.pending then
                    g.chainPendingReplacement (.finishPostStep (.logIfCountersIncreased cur.id dstBefore msg))
                  else
                    g.logIfCountersIncreased cur.id dstBefore msg
              | .double kind? =>
                let bag := cur.status.toCounterBag.filter fun (k, _) => kind?.all (· == k)
                bag.foldl (fun g (k, cnt) =>
                  if cnt == 0 then g
                  else if k == .plusOnePlusOne then
                    match g.findObject? cur.id with
                    | some liveCur => g.addPlusOnePlusOneTo liveCur cnt (byPlayer := some ctx.controller) (cause := some cause)
                    | none => g
                  else
                    g.putCountersDeferredLog cur.id k cnt (some ctx.controller) .isPutOn (cause := some cause)) g) g
  | .attach attExpr toExpr chooseFromPool =>
    let hosts := (resolveLiveObjects g env toExpr).filter (·.isOnBattlefield)
    match hosts[0]? with
    | none => g
    | some host =>
      if chooseFromPool then
        let atts := (resolveLiveObjects g env attExpr).filter (·.isOnBattlefield)
        if atts.isEmpty then g
        else
          g.change (.pending (.mayAttachEquipment ctx.controller host.id ctx.sourceId))
            |>.logMsg s!"{(g.player ctx.controller).name} may attach an Equipment to {g.name host}"
      else
        match (resolveLiveObjects g env attExpr)[0]? with
        | some att =>
          if att.isOnBattlefield then g.attachSourceTo att host else g
        | none => g
  | .transform objs =>
    let live := (resolveLiveObjects g env objs).filter (·.isOnBattlefield)
    live.foldl (fun g o => g.transformPermanent ctx.controller (some o.id) (cause := some cause)) g
  | .turnFaceUp objs =>
    let live := (resolveLiveObjects g env objs).filter (fun o => o.isOnBattlefield && o.status.faceDown)
    live.foldl (fun g o => (g.completeTurnFaceUp ctx.controller o.id).1) g
  | .phaseOut objs _ =>
    let live := (resolveLiveObjects g env objs).filter (fun o => o.isOnBattlefield && !o.status.phasedOut)
    if live.isEmpty then g
    else g.phaseOutPermanents live (cause := some cause)
  | .setDesignation objs tag value =>
    let live := (resolveLiveObjects g env objs).filter (·.isOnBattlefield)
    live.foldl (fun g o =>
      match tag with
      | .prepared =>
        if value then g.becomePrepared o (cause := some cause)
        else g.record (GameEvent.designation g.turnNumber (g.snapshot o) .prepared false (cause := cause))
      | .harnessed =>
        let g := g.record (GameEvent.designation g.turnNumber (g.snapshot o) .harnessed value (cause := cause))
        if value then g.logMsg s!"{g.name o} is harnessed" else g
      | .goaded =>
        g.record (GameEvent.designation g.turnNumber (g.snapshot o) (.goaded ctx.controller false) value (cause := cause))
      | .ringBearer =>
        if value then g.setRingBearer ctx.controller (some o.id) (cause := some cause) else g) g

/-! ### Action Family 4: `damage` -/

private def execDamage (g : Game) (ctx : InterpCtx) (op : DamageOp) : Game × Option StepOutcome :=
  let env := interpEnv g ctx
  let cause := interpCause g ctx
  match op with
  | .deal srcExpr recExpr amtExpr flags =>
    let amt := (EvalExpr.evalValue g env amtExpr).toNat
    if amt == 0 then (g, none)
    else
      let srcView? : Option ObjectView := (EvalExpr.evalObjects g env srcExpr)[0]?
      let srcObj? : Option GameObject :=
        match srcView? with
        | some (.live o) => some o
        | some (.lki eo) => eo.id.bind g.damageSourceById?
        | none => ctx.sourceId.bind g.damageSourceById?
      let srcSnap? : Option EventObject :=
        match srcView? with
        | some (.live o) => some (g.snapshotDamageSource o)
        | some (.lki eo) => some eo
        | none => srcObj?.map g.snapshotDamageSource
      let srcName := (srcObj?.map g.name).orElse (fun _ => srcSnap?.map (·.name)) |>.getD "The source"
      let dealOne (g : Game) (t : Target) (n : Nat) (evCause : EventCause := cause) : Game × Nat :=
        if n == 0 then (g, 0)
        else
          match t with
          | .permanent oid =>
            match g.findObject? oid with
            | some o =>
              if !o.isOnBattlefield then (g, 0)
              else
                let lethal := if flags.trackExcess then g.lethalDamageThreshold o else 0
                let pIdx := g.events.size
                let g := g.dealDamageFrom srcName o (Int.ofNat n)
                  (source := srcObj?) (sourceSnap := srcSnap?) (cause := some evCause)
                  (suppressLifelink := true)
                let excess :=
                  if flags.trackExcess then
                    let dealt := g.damageDealtToPermanentSince oid pIdx
                    dealt - lethal
                  else 0
                (g, excess)
            | none => (g, 0)
          | .player pid =>
            if !g.stillInGame pid then (g, 0)
            else
              let g := g.dealDamageToPlayer pid n (source := srcObj?) (sourceSnap := srcSnap?)
                (cause := some evCause) (suppressLifelink := true)
              (g, 0)
          | .card _ => (g, 0)
      let recipients : Array Target :=
        match recExpr with
        | .objects oe => (resolveLiveObjects g env oe).filter (·.isOnBattlefield) |>.map (fun o => .permanent o.id)
        | .players pe => (EvalExpr.evalPlayer g env pe).map Target.player
        | .targetSlot slot => env.targetSlots[slot]?.getD #[]
        | .both oe pe =>
          ((resolveLiveObjects g env oe).filter (·.isOnBattlefield) |>.map (fun o => .permanent o.id)) ++
            ((EvalExpr.evalPlayer g env pe).map Target.player)
        | .allTargets => env.targetSlots.foldl (· ++ ·) #[]
      if recipients.isEmpty then (g, none)
      else if !flags.divided && !flags.trackExcess then
        let allPlayers := recipients.all fun | .player _ => true | _ => false
        let allPerms := recipients.all fun | .permanent _ => true | _ => false
        if allPlayers then
          let pids := recipients.filterMap fun | .player pid => some pid | _ => none
          (g.dealDamageToPlayers pids (Int.ofNat amt)
            (source := srcObj?) (sourceSnap := srcSnap?) (cause := some cause), none)
        else if allPerms then
          let oids := recipients.filterMap fun | .permanent oid => some oid | _ => none
          let permNote : PermanentDamageLoopNote :=
            match recExpr with
            | .objects (.inZones .battlefield (.all #[.hasType .creature, .controlledBy .opponent]))
            | .objects (.inZones .battlefield (.all #[.any #[.hasType .creature, .hasType .planeswalker], .controlledBy .opponent])) =>
              .oppCreatureOrPlaneswalker ctx.controller
            | _ => .none
          let g := g.withBatch (some cause) fun g =>
            g.dealDamageFromPermanentsLoop oids amt srcName srcSnap? (some cause) (note := permNote)
          (g, none)
        else
          let indexed : Array (Nat × Target) :=
            match recExpr with
            | .allTargets | .both (.target _) (.target _) =>
              Id.run do
                let mut pairs : Array (Nat × Target) := #[]
                for si in [0:env.targetSlots.size] do
                  for t in env.targetSlots[si]! do
                    pairs := pairs.push (si, t)
                return pairs
            | _ => #[]
          if !indexed.isEmpty && !ctx.targetSpec.slots.isEmpty then
            let g := g.withBatch (some cause) fun g =>
              g.damageUpToOneAndPlayerLoop ctx.controller ctx.targetSpec indexed amt
                srcName ctx.sourceId (some cause)
            (g, none)
          else
            let (g, batchCause) :=
              if ctx.oneShotEffectId.raw != 0 then (g, cause)
              else g.allocDelayedCause (some ctx.controller) ctx.sourceId
            let startIdx := g.events.size
            let (g, _) := g.withBatchReturn (some batchCause) fun g =>
              Id.run do
                let mut g := g
                for r in recipients do
                  let (g', _) := dealOne g r amt batchCause
                  g := g'
                if g.pending == .none then
                  g := g.applyAggregatedLifelinkSince startIdx (cause := some batchCause)
                return (g, 0)
            let g :=
              if let .chooseReplacement .. := g.pending then
                g.chainPendingReplacement (.finishPostStep (.applyAggregatedLifelink startIdx (some batchCause)))
              else g
            (g, none)
      else
        let startIdx := g.events.size
        let div := g.resolvingDivision
        let (g, totalExcess) := g.withBatchReturn (some cause) fun g =>
          Id.run do
            let mut g := g
            let mut ex : Nat := 0
            for i in [0:recipients.size] do
              let r := recipients[i]!
              let n := if flags.divided && i < div.size then div[i]! else amt
              let (g', e1) := dealOne g r n
              g := g'
              ex := ex + e1
            return (g, ex)
        let g :=
          if let .chooseReplacement .. := g.pending then
            g.chainPendingReplacement (.finishPostStep (.applyAggregatedLifelink startIdx (some cause)))
          else
            g.applyAggregatedLifelinkSince startIdx (cause := some cause)
        if flags.trackExcess then
          (g, some { excessDamage := totalExcess })
        else (g, none)
  | .fight aExpr bExpr oneWay =>
    match (resolveLiveObjects g env aExpr)[0]?, (resolveLiveObjects g env bExpr)[0]? with
    | some a, some b =>
      if a.isOnBattlefield && g.isCreature a && b.isOnBattlefield && g.isCreature b then
        if oneWay then
          let pw := (g.power a).toNat
          if pw == 0 then (g, none)
          else (g.dealDamageFrom (g.name a) b (Int.ofNat pw) (source := some a) (cause := some cause), none)
        else
          (g.fightCreatures a b (cause := some cause), none)
      else if !oneWay && a.isOnBattlefield && g.isCreature a then
        (g.logMsg s!"{g.name a} has nothing to fight", none)
      else (g, none)
    | some a, none =>
      if !oneWay && a.isOnBattlefield && g.isCreature a then
        (g.logMsg s!"{g.name a} has nothing to fight", none)
      else (g, none)
    | _, _ => (g, none)

/-! ### Action Family 5: `life` -/

private def execLife (g : Game) (ctx : InterpCtx) (op : LifeOp) : Game :=
  let env := interpEnv g ctx
  let cause := interpCause g ctx
  match op with
  | .gain whoExpr amtExpr =>
    let n := (EvalExpr.evalValue g env amtExpr).toNat
    if n == 0 then g
    else (EvalExpr.evalPlayer g env whoExpr).foldl (fun g p => g.gainLife p n (cause := some cause)) g
  | .lose whoExpr amtExpr =>
    let n := (EvalExpr.evalValue g env amtExpr).toNat
    if n == 0 then g
    else (EvalExpr.evalPlayer g env whoExpr).foldl (fun g p => g.loseLife p n (cause := some cause)) g
  | .set whoExpr amtExpr =>
    let targetLife := EvalExpr.evalValue g env amtExpr
    (EvalExpr.evalPlayer g env whoExpr).foldl (fun g p =>
      g.setLife p targetLife s!"{(g.player p).name}'s life total becomes {targetLife}" (cause := some cause)) g

/-! ### Action Family 6: `player` -/

/-- Execute CR 701.44a/c & CR 400.3 Explore for `explorer?` (live permanent or LKI). -/
private def execExploreOne (g : Game) (ctx : InterpCtx) (explorer? : Option GameObject) : Game :=
  let explorerLki? :=
    if explorer?.isNone then ctx.sourceId.bind g.lastKnownBefore? else none
  let explorerCtrl :=
    match explorer? with
    | some o => (g.controllerOf o).getD ctx.controller
    | none =>
      (explorerLki?.bind (fun eo => eo.controller.orElse (fun _ => some eo.owner))).getD ctx.controller
  if !g.stillInGame explorerCtrl then g
  else
    let explorerPl := g.player explorerCtrl
    let lib := explorerPl.library
    if lib.isEmpty then
      let g := g.logMsg s!"{explorerPl.name} explores (empty library)"
      match explorer? with
      | some o =>
        if o.isOnBattlefield then g.addPlusOnePlusOneTo o 1 (byPlayer := some explorerCtrl) else g
      | none => g
    else
      let top := lib.back!
      let card := g.object! top
      let cName := g.name card
      let g := g.record (GameEvent.revealed g.turnNumber explorerCtrl #[top]
        (cause := some (interpCause g ctx)))
      if g.isLand card then
        let destOwner := card.owner
        let (g, _) := g.move top (.hand destOwner) none
        if let .chooseReplacement .. := g.pending then
          g.chainPendingReplacement
            (.finishFrcPostStep (.logExploreLandToHand explorerCtrl top destOwner cName))
        else if (g.followMovedToZone? top (· == .hand destOwner)).isSome then
          let destDesc :=
            if destOwner == explorerCtrl then "their hand"
            else s!"{(g.player destOwner).name}'s hand"
          g.logMsg s!"{explorerPl.name} explores and puts {cName} into {destDesc}"
        else g
      else
        let g := g.logMsg s!"{explorerPl.name} explores and reveals {cName}"
        let g :=
          match explorer? with
          | some o =>
            if o.isOnBattlefield then g.addPlusOnePlusOneTo o 1 (byPlayer := some explorerCtrl) else g
          | none => g
        if let .chooseReplacement .. := g.pending then
          g.chainPendingReplacement (.finishFrcPostStep (.offerExploreMayGraveyard explorerCtrl top))
        else
          g.offerExploreMayGraveyard explorerCtrl top

private def execInspectLibrary (g : Game) (env : EvalEnv) (ctx : InterpCtx)
    (spec : InspectLibrarySpec) (cause : EventCause) : Game :=
  let chooser := (EvalExpr.evalPlayer g env spec.chooser)[0]?.getD ctx.controller
  match spec.source with
  | .topCards whoExpr countExpr reveal =>
    let p := (EvalExpr.evalPlayer g env whoExpr)[0]?.getD ctx.controller
    let n := (EvalExpr.evalValue g env countExpr).toNat
    if !g.stillInGame p || n == 0 then g
    else
      let looked := g.scryLookedIds p n
      let g :=
        if reveal then
          let g := g.record (GameEvent.revealed g.turnNumber p looked (cause := some cause))
          looked.foldl (fun g id =>
            match g.findObject? id with
            | some c => g.logMsg s!"{(g.player p).name} reveals {g.name c}"
            | none => g) g
        else g.logLookAtTop p looked.size looked
      if looked.isEmpty then g
      else
        match spec.action with
        | .none => g
        | .moveAll dest mods =>
          g.withBatch (some cause) fun g =>
            looked.foldl (fun g id =>
              match g.findObject? id with
              | some o => moveOneObject g env ctx o dest .put mods cause
              | none => g) g
        | .takeMatching filter cnt dest mods _ =>
          let (_, hi) := evalInterpCountRange g env cnt
          let eligible := looked.filter fun id =>
            (g.findObject? id).any fun o => EvalExpr.evalObjectPred g env (.live o) filter
          let anyOrder := spec.rest == .bottomAnyOrder
          match dest with
          | .hand _ =>
            if hi == 1 && (spec.rest == .bottomRandom || spec.rest == .bottomAnyOrder) then
              if eligible.isEmpty then
                if anyOrder then g.offerBottomAnyOrder p looked (cause := some cause)
                else g.putRestOnBottomRandom p looked (cause := some cause)
              else
                g.beginFraChoice chooser (.mayRevealToHand looked eligible anyOrder)
                  s!"{(g.player chooser).name} may reveal a card from among them and put it into their hand"
            else
              let chosen := eligible.extract 0 (min hi eligible.size)
              let rest := looked.filter (!chosen.contains ·)
              let g := g.withBatch (some cause) fun g =>
                chosen.foldl (fun g id =>
                  match g.findObject? id with
                  | some o => moveOneObject g env ctx o dest .put mods cause
                  | none => g) g
              match spec.rest with
              | .bottomRandom => g.putRestOnBottomRandom p rest (cause := some cause)
              | .bottomAnyOrder => g.offerBottomAnyOrder p rest (cause := some cause)
              | .shuffleIntoLibrary => g.shuffleThen p .none
              | .graveyard =>
                g.withBatch (some cause) fun g =>
                  rest.foldl (fun g id => (g.move id (.graveyard p) none (cause := some cause)).1) g
              | .exile =>
                g.withBatch (some cause) fun g =>
                  rest.foldl (fun g id => (g.move id .exile none (cause := some cause)).1) g
              | .leaveInPlace => g
          | .battlefield _ =>
            if mods.tapped && spec.rest == .shuffleIntoLibrary && hi ≥ 100 then
              g.offerCardChoice chooser eligible hi (.landsTappedGainLife 0)
                s!"{(g.player chooser).name} chooses land cards to put onto the battlefield tapped"
                (cause := some cause)
            else if spec.rest == .graveyard && (hi ≥ 100 || hi == 1) then
              let anyNum := hi ≥ 100
              if eligible.isEmpty then g.finishRevealPutCreatures p looked #[]
              else
                g.beginFraChoice chooser (.revealPutCreatures looked eligible anyNum)
                  (if anyNum then s!"{(g.player chooser).name} may put any number of matching cards onto the battlefield"
                   else s!"{(g.player chooser).name} may put a creature card from among them onto the battlefield")
            else if spec.rest == .bottomRandom && hi == 1 && mods.mayTransformOnEnter then
              if eligible.isEmpty then g.putRestOnBottomRandom p looked (cause := some cause)
              else
                g.beginFraChoice chooser (.nickFuryPut looked eligible)
                  s!"{(g.player chooser).name} may put a card from among them onto the battlefield"
            else
              let chosen := eligible.extract 0 (min hi eligible.size)
              let rest := looked.filter (!chosen.contains ·)
              let g := g.withBatch (some cause) fun g =>
                chosen.foldl (fun g id =>
                  match g.findObject? id with
                  | some o => moveOneObject g env ctx o dest .put mods cause
                  | none => g) g
              match spec.rest with
              | .bottomRandom => g.putRestOnBottomRandom p rest (cause := some cause)
              | .bottomAnyOrder => g.offerBottomAnyOrder p rest (cause := some cause)
              | .shuffleIntoLibrary => g.shuffleThen p .none
              | .graveyard =>
                g.withBatch (some cause) fun g =>
                  rest.foldl (fun g id => (g.move id (.graveyard p) none (cause := some cause)).1) g
              | .exile =>
                g.withBatch (some cause) fun g =>
                  rest.foldl (fun g id => (g.move id .exile none (cause := some cause)).1) g
              | .leaveInPlace => g
          | _ =>
            let chosen := eligible.extract 0 (min hi eligible.size)
            let rest := looked.filter (!chosen.contains ·)
            let g := g.withBatch (some cause) fun g =>
              chosen.foldl (fun g id =>
                match g.findObject? id with
                | some o => moveOneObject g env ctx o dest .put mods cause
                | none => g) g
            match spec.rest with
            | .bottomRandom => g.putRestOnBottomRandom p rest (cause := some cause)
            | .bottomAnyOrder => g.offerBottomAnyOrder p rest (cause := some cause)
            | .shuffleIntoLibrary => g.shuffleThen p .none
            | _ => g
        | .splitIntoPiles splitterExpr _ _ _ _ _ =>
          if splitterExpr == .you then
            g.beginFraChoice p (.riddlesSplit looked)
              s!"{(g.player p).name} separates {looked.size} cards into a face-up pile and a face-down pile"
          else
            let splitter := (EvalExpr.evalPlayer g env splitterExpr)[0]?.getD (g.firstLivingOpponent? p |>.getD p)
            let half := (looked.size + 1) / 2
            let pileA := looked.extract 0 half
            let pileB := looked.extract half looked.size
            let _ := splitter
            g.factOrFictionHandLoop p pileA pileB
        | .distributeEachOpponent _ _ =>
          g.putHitsToBattlefield p looked (cause := some cause)
  | .revealUntil whoExpr matchPred countExpr _ =>
    let p := (EvalExpr.evalPlayer g env whoExpr)[0]?.getD ctx.controller
    let limit := (EvalExpr.evalValue g env countExpr).toNat
    if !g.stillInGame p || limit == 0 then g
    else
      let (g, hits, rest) := g.revealUntilCards p
        (fun o => EvalExpr.evalObjectPred g env (.live o) matchPred) limit (cause := some cause)
      let shuffle := spec.rest == .shuffleIntoLibrary
      match spec.action with
      | .moveAll (.battlefield _) mods =>
        let g := g.putHitsToBattlefield p hits (haste := mods.enterKeywords.contains Keyword.haste)
          (tapped := mods.tapped) (cause := some cause)
        if let .chooseReplacement .. := g.pending then
          g.chainPendingReplacement (.finishFrcRestBottom p rest shuffle (some cause))
        else
          g.restBottomCards p rest shuffle (cause := some cause)
      | .distributeEachOpponent _ _ =>
        let g := g.putHitsToBattlefield p hits (cause := some cause)
        if let .chooseReplacement .. := g.pending then
          g.chainPendingReplacement (.finishFrcRestBottom p rest shuffle (some cause) hits)
        else
          g.finishFrcRestBottom p rest shuffle (some cause) hits
      | .moveAll dest mods =>
        let g := g.withBatch (some cause) fun g =>
          hits.foldl (fun g id =>
            match g.findObject? id with
            | some o => moveOneObject g env ctx o dest .put mods cause
            | none => g) g
        if let .chooseReplacement .. := g.pending then
          g.chainPendingReplacement (.finishFrcRestBottom p rest shuffle (some cause))
        else
          g.restBottomCards p rest shuffle (cause := some cause)
      | _ =>
        g.restBottomCards p rest shuffle (cause := some cause)
  | .millCards whoExpr countExpr =>
    let p := (EvalExpr.evalPlayer g env whoExpr)[0]?.getD ctx.controller
    let n := (EvalExpr.evalValue g env countExpr).toNat
    if !g.stillInGame p then g
    else
      match spec.action with
      | .takeMatching filter cnt (.hand _) _ _ =>
        let types : Array CardType :=
          match filter with
          | .hasType ty => #[ty]
          | .any ps => ps.filterMap fun | .hasType ty => some ty | _ => none
          | _ => #[]
        match cnt with
        | .anyNumber =>
          g.millThenPutFromGy p n (fun o => EvalExpr.evalObjectPred g env (.live o) filter) (types := types)
        | _ =>
          let (lo, hi) := evalInterpCountRange g env cnt
          g.millThenChooseForHand p n (fun o => EvalExpr.evalObjectPred g env (.live o) filter) hi (lo > 0) (types := types)
      | _ => g.mill p n (cause := some cause)
  | .allButBottom whoExpr =>
    let pids := EvalExpr.evalPlayer g env whoExpr
    g.withBatch (some cause) fun g =>
      g.exileOpponentLibrariesLoop pids
  | .outsideTheGame _ _ => g

private def execSearchLibrary (g : Game) (env : EvalEnv) (ctx : InterpCtx)
    (spec : SearchLibrarySpec) : Game :=
  let searcher := (EvalExpr.evalPlayer g env spec.searcher)[0]?.getD ctx.controller
  if !g.stillInGame searcher then g
  else
    let (_, hi) := evalInterpCountRange g env spec.count
    if spec.groupConstraint? == some .distinctNames && spec.dest == .hand .controller then
      let (pickedIds, _) := (g.player searcher).library.foldl
        (fun (acc : Array ObjectId × Array String) id =>
          let (picked, names) := acc
          if names.size >= hi then acc
          else
            match g.findObject? id with
            | some o =>
              if EvalExpr.evalObjectPred g env (.live o) spec.filter && !names.contains (g.name o) then
                (picked.push id, names.push (g.name o))
              else acc
            | none => acc) (#[], #[])
      let (g, cause) := g.allocDelayedCause (some searcher) ctx.sourceId
      let g := g.record (GameEvent.searched g.turnNumber searcher searcher pickedIds (cause := some cause))
      let g :=
        if pickedIds.isEmpty then g
        else g.record (GameEvent.revealed g.turnNumber searcher pickedIds (cause := some cause))
      let g :=
        if pickedIds.isEmpty then g
        else
          g.withBatch (some cause) fun g =>
            g.fblthpMoveToHandLoop searcher pickedIds cause
      if let .chooseReplacement .. := g.pending then
        g.chainPendingReplacement (.finishPostStep (.fblthpShuffleAfterHand searcher))
      else
        g.shuffleThen searcher .none
    else
      let pred (c : CardDef) : Bool :=
        let fake : GameObject := {
          printed := c
          id := ⟨0⟩
          owner := searcher
          controller := some searcher
          zone := .library searcher
        }
        EvalExpr.evalObjectPred g env (.live fake) spec.filter
      let rawLabel := ToOracle.toOracle {} spec.filter
      let label :=
        if rawLabel.endsWith " card" || rawLabel.endsWith " cards" then rawLabel
        else s!"{rawLabel} card"
      let sdest : SearchDest :=
        if spec.zones.zones.contains .hand && spec.zones.zones.contains .library then
          .battlefieldFromHandOrLibrary
        else
          match spec.dest, spec.secondDest? with
          | .battlefield _, some (.hand _, _) => .battlefieldTappedThenHand
          | .battlefield _, _ => .battlefield spec.mods.tapped
          | .hand _, _ => .hand
          | .graveyard, _ => .graveyard
          | .exile, _ => .exileLinked (if spec.mods.linkToSource then ctx.sourceId else none)
          | .library _ .top _, _ => .topAfterShuffle
          | .library _ _ _, _ => .topAfterShuffle
      g.beginLibrarySearch searcher pred label sdest (count := max 1 hi)

private def execPlayer (g : Game) (ctx : InterpCtx) (op : PlayerOp) : Game × Option StepOutcome :=
  let env := interpEnv g ctx
  let cause := interpCause g ctx
  match op with
  | .drawCards whoExpr amtExpr =>
    let n :=
      match amtExpr with
      | .aggregate .sum (.stat .power) .costPaidObjects =>
        if env.costPaidObjects.isEmpty then env.eventAmount.toNat
        else (EvalExpr.evalValue g env amtExpr).toNat
      | _ => (EvalExpr.evalValue g env amtExpr).toNat
    if n == 0 then (g, none)
    else
      ((EvalExpr.evalPlayer g env whoExpr).foldl (fun g p => g.draw p n (cause := some cause)) g, none)
  | .scry whoExpr amtExpr =>
    let n := (EvalExpr.evalValue g env amtExpr).toNat
    match (EvalExpr.evalPlayer g env whoExpr)[0]? with
    | some p => (g.beginScry p n, none)
    | none => (g, none)
  | .surveil whoExpr amtExpr =>
    let n := (EvalExpr.evalValue g env amtExpr).toNat
    match (EvalExpr.evalPlayer g env whoExpr)[0]? with
    | some p => (g.beginSurveil p n, none)
    | none => (g, none)
  | .inspectLibrary spec =>
    let preIdx := g.events.size
    let g := execInspectLibrary g env ctx spec cause
    match spec.source, spec.action with
    | .revealUntil .., .moveAll (.battlefield _) _ =>
      let placedIds : Array ObjectId := (g.events.extract preIdx g.events.size).filterMap fun e =>
        match e.change with
        | .rules (.zone (.moved _ after _ .battlefield ..)) => after.id
        | _ => none
      let ov : StepOutcome := { objects := placedIds, movedCount := placedIds.size, succeeded := !placedIds.isEmpty }
      (g, some ov)
    | _, _ => (g, none)
  | .searchLibrary spec =>
    (execSearchLibrary g env ctx spec, none)
  | .reveal whoExpr objsExpr =>
    let p := (EvalExpr.evalPlayer g env whoExpr)[0]?.getD ctx.controller
    let ids := resolveObjectIds g env objsExpr
    if ids.isEmpty then (g, none)
    else
      let g := g.record (GameEvent.revealed g.turnNumber p ids (cause := some cause))
      let g := ids.foldl (fun g id =>
        match g.findObject? id with
        | some c => g.logMsg s!"{(g.player p).name} reveals {g.name c}"
        | none => g) g
      (g, some { objects := ids, succeeded := true })
  | .shuffle whoExpr =>
    ((EvalExpr.evalPlayer g env whoExpr).foldl (fun g p => g.shuffleThen p .none) g, none)
  | .addMana whoExpr mp =>
    let out := g.evalManaSpec env mp.spec
    let pids := EvalExpr.evalPlayer g env whoExpr
    match out, mp.restriction with
    | .combination _ n, some rest =>
      if n > 0 then
        match pids[0]? with
        | some p =>
          if !g.stillInGame p then (g, none)
          else
            (g.beginFraChoice p (.addManaColors n rest)
              s!"{(g.player p).name} chooses the colors of {englishNumber n} mana ({rest.label})", none)
        | none => (g, none)
      else (g, none)
    | _, _ =>
      let manaTypes : Array ManaType :=
        match out with
        | .fixed ts => ts
        | .oneOf ts n =>
          if ts == anyColorMana then
            let defaultColor : Color :=
              match mp.restriction with
              | none => .green
              | some (.onlyForAbilities (.sourceMatches (.hasType .creature))) => .green
              | some (.onlyForSpellsOrAbilities (.hasSubtype .elf) _ _) => .green
              | some (.onlyForSpellsOrAbilities (.hasSubtype .villain) _ _) => .black
              | some _ => .white
            Array.replicate n (.colored defaultColor)
          else
            match ts[0]? with
            | some t => Array.replicate n t
            | none => #[]
        | .combination ts n =>
          match ts[0]? with
          | some t => Array.replicate n t
          | none => #[]
        | .colorAmong ts incC =>
          match ts[0]? with
          | some t => #[t]
          | none => if incC then #[.colorless] else #[]
      let g := pids.foldl (fun g p =>
        if !g.stillInGame p || manaTypes.isEmpty then g
        else
          let units := manaTypes.map fun t =>
            { mana := t, source := ctx.sourceId, restriction := mp.restriction, riders := mp.allRiders : ManaUnit }
          let g := g.addManaUnits p units (cause := some cause)
          let g := if mp.damageYou > 0 then g.dealDamageToPlayer p mp.damageYou (source := ctx.sourceId.bind g.damageSourceById?) (cause := some cause) else g
          g.logMsg s!"{(g.player p).name} adds mana ({String.intercalate "" (manaTypes.toList.map toString)})") g
      (g, none)
  | .proliferate whoExpr timesExpr tgtOnly? =>
    let times := (EvalExpr.evalValue g env timesExpr).toNat
    if times == 0 then (g, none)
    else
      match tgtOnly? with
      | some tgtExpr =>
        let ts : Array Target := (resolveLiveObjects g env tgtExpr).map (fun o => .permanent o.id)
        if ts.isEmpty then (g, none)
        else (g.proliferateTarget ctx.controller ts (sourceId := ctx.sourceId), none)
      | none =>
        match (EvalExpr.evalPlayer g env whoExpr)[0]? with
        | some p =>
          ((g.change (.pending (.chooseProliferate p times))).logMsg
            s!"{(g.player p).name} proliferates {times} time(s)", none)
        | none => (g, none)
  | .temptWithRing whoExpr =>
    ((EvalExpr.evalPlayer g env whoExpr).foldl (fun g p => g.temptWithTheRing p) g, none)
  | .explore objsExpr =>
    let live := resolveLiveObjects g env objsExpr
    if live.isEmpty then
      -- CR 701.44c: if the exploring permanent left the battlefield, still explore using LKI!
      (execExploreOne g ctx none, none)
    else
      (live.foldl (fun g o => execExploreOne g ctx (some o)) g, none)
  | .amass whoExpr subtype amtExpr =>
    let n := (EvalExpr.evalValue g env amtExpr).toNat
    ((EvalExpr.evalPlayer g env whoExpr).foldl (fun g p => g.amass p subtype n (cause := some cause)) g, none)
  | .connive objsExpr =>
    let live := (resolveLiveObjects g env objsExpr).filter (·.isOnBattlefield)
    (live.foldl (fun g o => g.applyConnive ((g.controllerOf o).getD ctx.controller) (some o.id)) g, none)
  | .empowerPlaneswalker _ amtExpr =>
    let n := (EvalExpr.evalValue g env amtExpr).toNat
    (g.empowerJace ctx.controller n (cause := some cause), none)
  | .setStatus whoExpr kind cond? =>
    let ok := cond?.all (EvalExpr.evalCondition g env)
    if !ok then (g, none)
    else
      let pids := EvalExpr.evalPlayer g env whoExpr
      let g := pids.foldl (fun g p =>
        if !g.stillInGame p then g
        else
          match kind with
          | .monarch =>
            if (g.player p).isMonarch then g
            else
              let prev := g.players.find? (·.isMonarch) |>.map (·.id)
              (g.record (GameEvent.becameMonarch g.turnNumber p prev (cause := some cause))).logMsg
                s!"{(g.player p).name} becomes the monarch"
          | .designation .citysBlessing =>
            g.grantDesignationIfNeeded p (·.citysBlessing) (fun _ _ => true) .citysBlessing "gets the city's blessing"
          | .designation .enduringStory =>
            g.grantDesignationIfNeeded p (·.enduringStory) (fun _ _ => true) .enduringStory "has an enduring story") g
      (g, none)
  | .choose whoExpr kind =>
    let chooser := (EvalExpr.evalPlayer g env whoExpr)[0]?.getD ctx.controller
    match kind with
    | .creatureType =>
      let pref := g.chooseCreatureTypeFor chooser
      let types := #[pref] ++ g.battlefieldCreatureTypes.filter (· != pref)
      (g.beginFraChoice chooser (.chooseCreatureType types)
        s!"{(g.player chooser).name} chooses a creature type", none)
    | .oddOrEven =>
      (g.beginFraChoice chooser (.oddOrEvenDestroy ctx.sourceId)
        s!"{(g.player chooser).name} chooses odd or even", none)
    | .keyword options =>
      let kwChoices : Array KeywordChoice := options.filterMap fun
        | .simple .trample => some .trample
        | .hexproof none => some .hexproof
        | .simple .haste => some .haste
        | .simple .deathtouch => some .deathtouch
        | _ => none
      match ctx.sourceId.bind g.findObject? with
      | some o =>
        if o.isOnBattlefield && !kwChoices.isEmpty then
          (g.beginChooseKeyword chooser o.id kwChoices, none)
        else (g, none)
      | none => (g, none)
    | .playerWithMostLife =>
      let living := g.players.filter (fun pl => g.stillInGame pl.id)
      match living[0]? with
      | none => (g, none)
      | some p0 =>
        let best := living.foldl (fun b pl => if pl.life > b.life then pl else b) p0
        (g, some { players := #[best.id], succeeded := true })

/-! ### Action Family 7: `turn` -/

private def execTurn (g : Game) (ctx : InterpCtx) (op : TurnOp) : Game :=
  let env := interpEnv g ctx
  match op with
  | .extraTurn whoExpr rule? =>
    let pids := EvalExpr.evalPlayer g env whoExpr
    let (g, cause) :=
      if ctx.oneShotEffectId.raw != 0 then (g, interpCause g ctx)
      else g.allocDelayedCause (some ctx.controller) ctx.sourceId
    pids.foldl (fun g p =>
      if !g.stillInGame p then g
      else
        let teamSeats := (g.teamMembers p).filter g.stillInGame
        let firstSeat := teamSeats[0]?.getD p
        let whoVerb :=
          if teamSeats.size ≤ 1 then s!"{(g.player p).name} takes"
          else s!"{g.formatPlayerNames teamSeats} take"
        let g := g.record (GameEvent.extraTurnAdded g.turnNumber firstSeat (cause := cause))
        let suffix :=
          match rule? with
          | some (.player (.forbidAbilityActivation _ .powerUp)) =>
            ". During that turn, power-up abilities can't be activated."
          | _ => ""
        g.logMsg s!"{whoVerb} an extra turn after this one{suffix}") g
  | .extraPhase _ _ | .extraStep _ _ => g

/-! ### Action Family 8: `stack` -/

private def execStack (g : Game) (ctx : InterpCtx) (op : StackOp) : Game :=
  let env := interpEnv g ctx
  let cause := interpCause g ctx
  match op with
  | .counterStack objsExpr exileInstead ifPermCastFree =>
    let objs := resolveLiveObjects g env objsExpr
    objs.foldl (fun g o =>
      if o.zone != .stack then g
      else
        g.counterStackSpell o.id (exilePermanent := exileInstead)
          (grantFreeCast := ifPermCastFree) (controller := some ctx.controller)) g
  | .copyStackObject objsExpr copiesExpr mayNewTargets =>
    let copiesN := (EvalExpr.evalValue g env copiesExpr).toNat
    if copiesN == 0 then g
    else
      let objs := resolveLiveObjects g env objsExpr
      objs.foldl (fun g spell =>
        if spell.zone != .stack then
          g.logMsg s!"{g.name spell} is no longer on the stack"
        else
          let (g, copies) := (List.range copiesN).foldl (fun (acc : Game × Array ObjectId) _ =>
            let (g, cid?) := acc.1.copyStackSpellWithId spell ctx.controller
            match cid? with
            | some cid => (g, acc.2.push cid)
            | none => (g, acc.2)) (g, #[])
          let targeted := copies.any fun cid =>
            ((g.stackEntry? cid).map (!·.targets.isEmpty)).getD false
          if !mayNewTargets || copies.isEmpty || !targeted then g
          else
            g.beginFraChoice ctx.controller (.newTargetsForCopies copies)
              s!"{(g.player ctx.controller).name} may choose new targets for the copies") g
  | .mayCastOrPlay objsExpr permSpec =>
    let ids := resolveObjectIds g env objsExpr
    if ids.isEmpty then g
    else if permSpec.asFlashback then
      ids.foldl (fun g id =>
        match g.findObject? id with
        | some o =>
          (g.createEffect (.flashbackUntilEot o.id) (cause := some cause)).logMsg
            s!"{g.name o} gains flashback until end of turn"
        | none => g) g
    else if permSpec.copyAndCast then
      let (g, copies) := g.withBatchReturn (some cause) fun g =>
        ids.foldl (fun (acc : Game × Array ObjectId) id =>
          let (g, cs) := acc
          match g.findObject? id with
          | some card =>
            if card.zone != .exile then (g, cs)
            else
              let base := g.copiableValues card
              let copyId : ObjectId := ⟨g.nextObjectId⟩
              let copyObj : GameObject := {
                id := copyId
                printed := { base with
                  isToken := false
                  otherFace := base.otherFace.map (fun f => { f with isToken := false }) }
                owner := ctx.controller
                controller := some ctx.controller
                zone := .exile
                timestamp := g.timestamp + 1
                isCopy := true
              }
              let g := g.record (GameEvent.created g.turnNumber ctx.controller (g.snapshot copyObj) (cause := cause))
              let g := g.createEffect (.playPermission copyId {
                player := ctx.controller, whileExiled := true,
                withoutManaCost := permSpec.freeCast, ignoreTiming := true }) (cause := some cause)
              (g, cs.push copyId)
          | none => (g, cs)) (g, #[])
      if copies.isEmpty then g
      else if permSpec.maxCasts? == some 1 && permSpec.maxTotalManaValue?.isNone && copies.size == 1 then
        let copyId := copies[0]!
        let copyName := (g.findObject? copyId).map g.name |>.getD "the card"
        g.beginFraChoice ctx.controller (.mayCastCopy copyId)
          s!"{(g.player ctx.controller).name} may cast the copy of {copyName} without paying its mana cost"
      else
        let maxMv := permSpec.maxTotalManaValue?.map (fun v => (EvalExpr.evalValue g env v).toNat) |>.getD 1000
        let maxCasts := permSpec.maxCasts?.getD copies.size
        g.beginFraChoice ctx.controller (.castCopiesFree copies maxMv maxCasts)
          s!"{(g.player ctx.controller).name} may cast copies without paying their mana costs"
    else
      let (perm, dur) := resolvePlayPerm g env permSpec
      let turnEnds :=
        match dur with
        | .untilEndOfNextTurnOf _ => 2
        | .whileInZone _ .exile | .indefinite => 0
        | _ => 1
      let eligible := ids.filter fun id =>
        (g.findObject? id).any fun o =>
          (!g.isLand o || permSpec.landsAllowed) &&
            permSpec.filter?.all (EvalExpr.evalObjectPred g env (.live o))
      let g := eligible.foldl (fun g id =>
        g.createEffect (.playPermission id perm (turnEnds := turnEnds) (d := dur)) (cause := some cause)) g
      if permSpec.freeCast && !eligible.isEmpty then
        g.beginFraChoice ctx.controller (.mayCastCards eligible true false)
          s!"{(g.player ctx.controller).name} may cast a spell without paying its mana cost"
      else g

/-! ### Action Family 9: `installEffect` -/

private partial def applyContinuousModToObj (g : Game) (env : EvalEnv) (ctx : InterpCtx)
    (o : GameObject) (dur : EffectDuration) (mod : ContinuousModification)
    (cause : EventCause) : Game :=
  match mod with
  | .all mods =>
    mods.foldl (fun g m => applyContinuousModToObj g env ctx o dur m cause) g
  | .modifyPT pwExpr twExpr =>
    let pw := EvalExpr.evalValue g env pwExpr
    let tw := EvalExpr.evalValue g env twExpr
    match dur with
    | .untilEndOfTurn => g.pumpPermanent o pw tw
    | _ =>
      (g.createEffect (.layered (.objects #[o.id]) (.ptModify pw tw) dur) (cause := some cause)).logMsg
        s!"{g.name o} gets {signedStat pw}/{signedStat tw}"
  | .setBasePT pw? tw? =>
    let pw := (pw?.map (EvalExpr.evalValue g env)).getD (g.power o)
    let tw := (tw?.map (EvalExpr.evalValue g env)).getD (g.toughness o)
    match dur with
    | .untilEndOfTurn => g.setBasePTUntilEotLogged o pw tw
    | _ =>
      (g.createEffect (.layered (.objects #[o.id]) (.ptSet pw tw) dur) (cause := some cause)).logMsg
        s!"{g.name o} has base power and toughness {pw}/{tw}"
  | .grantKeywords ks =>
    match dur with
    | .untilEndOfTurn => g.grantUntilEotLogged o ks
    | _ =>
      (g.createEffect (.layered (.objects #[o.id]) (.abilities { keywords := ks } .none) dur) (cause := some cause)).logMsg
        s!"{g.name o} gains {KeywordAbility.joinedAnd ks}"
  | .loseKeywords ks =>
    if ks.contains Keyword.indestructible && dur == .untilEndOfTurn then
      g.loseIndestructibleUntilEot o
    else
      let rem : AbilityRemoval :=
        if ks.contains Keyword.indestructible then .loseIndestructible else .all
      g.createEffect (.layered (.objects #[o.id]) (.abilities {} rem) dur) (cause := some cause)
  | .loseAllAbilities =>
    g.createEffect (.layered (.objects #[o.id]) (.abilities {} .all) dur) (cause := some cause)
      |>.logMsg s!"{g.name o} loses all abilities"
  | .modifyTypes tm =>
    let g :=
      if tm.types.contains .creature && g.isEquipment o then
        match o.attachedTo with
        | some hostId =>
          (g.record (GameEvent.unattached g.turnNumber (g.snapshot o) hostId (cause := cause)))
            |>.logMsg s!"{g.name o} becomes unattached"
        | none => g
      else g
    let g := g.createEffect (.layered (.objects #[o.id])
      (.types tm.mode tm.types tm.subtypes tm.supertypes tm.removeTypes) dur) (cause := some cause)
    if tm.types.contains .creature && !tm.subtypes.isEmpty then
      let subStr := String.intercalate " " (tm.subtypes.toList.map CardSubtype.englishName)
      g.logMsg s!"{g.name o} becomes a {subStr} creature"
    else g
  | .addAllCreatureTypes =>
    g.createEffect (.layered (.objects #[o.id]) (.abilities { keywords := #[.simple .changeling] } .none) dur)
      (cause := some cause)
  | .modifyColors cm =>
    g.createEffect (.layered (.objects #[o.id]) (.colors cm.mode cm.colors) dur) (cause := some cause)
  | .grantActivated abs =>
    g.createEffect (.layered (.objects #[o.id])
      (.abilities { staticAbilities := #[.continuous none StaticAbility.scopeSelf (.grantActivated abs)] } .none) dur)
      (cause := some cause)
  | .grantTriggered abs =>
    let msg :=
      if abs.any (·.pattern == .landYouControlEnters) then s!"{g.name o} gains landfall"
      else s!"{g.name o} gains a triggered ability"
    (g.createEffect (.layered (.objects #[o.id]) (.abilities { triggeredAbilities := abs } .none) dur)
      (cause := some cause)).logMsg msg
  | .grantStatic abs =>
    g.createEffect (.layered (.objects #[o.id]) (.abilities { staticAbilities := abs } .none) dur)
      (cause := some cause)
  | .copyActivatedFrom _ => g
  | .gainControl newCtrlExpr =>
    match (EvalExpr.evalPlayer g env newCtrlExpr)[0]? with
    | none => g
    | some newCtrl =>
      if !g.stillInGame newCtrl then g
      else
        (g.createEffect (.layered (.objects #[o.id]) (.control newCtrl) dur) (cause := some cause)).logMsg
          s!"{(g.player newCtrl).name} gains control of {g.name o}"
  | .exchangeControl otherExpr =>
    match (resolveLiveObjects g env otherExpr)[0]? with
    | none => g
    | some other =>
      if !other.isOnBattlefield then g
      else
        match g.controllerOf o, g.controllerOf other with
        | some c1, some c2 =>
          if c1 == c2 || !g.stillInGame c1 || !g.stillInGame c2 then g
          else
            g.withBatch (some cause) fun g =>
              let g := g.createEffect (.layered (.objects #[o.id]) (.control c2) dur) (cause := some cause)
              let g := g.createEffect (.layered (.objects #[other.id]) (.control c1) dur) (cause := some cause)
              g.logMsg s!"{(g.player c1).name} and {(g.player c2).name} exchange control of {g.name o} and {g.name other}"
        | _, _ => g
  | .becomeCopyOf srcExpr mods =>
    match (resolveLiveObjects g env srcExpr)[0]? with
    | none => g
    | some src =>
      let base := g.copiableValues src
      let printed := mods.foldl applyCopyModification base
      (g.createEffect (.layered (.objects #[o.id]) (.copy printed) dur) (cause := some cause)).logMsg
        s!"{g.name o} becomes a copy of {g.name src}"
  | .applyRule rule =>
    match rule with
    | .combat (.cantBeBlocked _) =>
      if dur == .untilEndOfTurn then g.grantCantBeBlockedThisTurn o
      else g.createEffect (.layered (.objects #[o.id]) (.abilities { staticAbilities := #[.cantBeBlocked] } .none) dur) (cause := some cause)
    | .combat (.cantBlock _) =>
      g.createEffect (.gameRule (.cantBlock o.id) dur) (cause := some cause)
        |>.logMsg s!"{g.name o} can't block"
    | .combat (.cantBeBlockedBy _ blockerPred) =>
      match blockerPred with
      | .controlledBy { pred := .matchesExpr pe, .. } =>
        (EvalExpr.evalPlayer g env pe).foldl (fun g p =>
          g.createEffect (.cantBeBlockedByPlayerUntilEot o.id p) (cause := some cause)) g
      | .not (.hasKeyword .haste) =>
        g.createEffect (.cantBeBlockedExceptByHasteUntilEot o.id) (cause := some cause)
      | _ =>
        g.createEffect (.layered (.objects #[o.id]) (.abilities { staticAbilities := #[.ruleModifying none rule] } .none) dur)
          (cause := some cause)
    | _ =>
      g.createEffect (.layered (.objects #[o.id]) (.abilities { staticAbilities := #[.ruleModifying none rule] } .none) dur)
        (cause := some cause)

private partial def applyRuleMod (g : Game) (env : EvalEnv) (ctx : InterpCtx)
    (dur : EffectDuration) (rule : RuleModification) (cause : EventCause) : Game :=
  match rule with
  | .all rules => rules.foldl (fun g r => applyRuleMod g env ctx dur r cause) g
  | .player pr =>
    match pr with
    | .additionalLands who n =>
      (EvalExpr.evalPlayerFilter g env who).foldl (fun g p =>
        let msg :=
          if n == 1 then s!"{(g.player p).name} may play an additional land this turn"
          else s!"{(g.player p).name} may play {n} additional lands this turn"
        (g.createEffect (.playerRule p (.additionalLands n) dur) (cause := some cause)).logMsg msg) g
    | .cantCastSpells who _ =>
      (EvalExpr.evalPlayerFilter g env who).foldl (fun g p =>
        (g.createEffect (.playerRule p .cantCastSpells dur) (cause := some cause)).logMsg
          s!"{(g.player p).name} can't cast spells this turn") g
    | .lifeTotalCantChange who =>
      (EvalExpr.evalPlayerFilter g env who).foldl (fun g p =>
        let r : PlayerRule := match dur with | .untilEndOfTurn => .lifeLocked | _ => .lifeCantChange
        (g.createEffect (.playerRule p r dur) (cause := some cause)).logMsg
          s!"{(g.player p).name}'s life total can't change") g
    | .protectionFrom who .everything =>
      (EvalExpr.evalPlayerFilter g env who).foldl (fun g p =>
        (g.createEffect (.protectionFromEverything p) (cause := some cause)).logMsg
          s!"{(g.player p).name} has protection from everything until their next turn") g
    | .forbidAbilityActivation _ .powerUp =>
      g.createEffect (.gameRule .powerUpsForbidden dur) (cause := some cause)
    | _ => g
  | .play pr =>
    match pr with
    | .nextSpellCantBeCountered who _ =>
      (EvalExpr.evalPlayerFilter g env who).foldl (fun g p =>
        (g.createEffect (.nextSpellCantBeCounteredThisTurn p) (cause := some cause)).logMsg
          s!"The next spell {(g.player p).name} casts this turn can't be countered") g
    | .activateLoyaltyAsInstant who _ =>
      (EvalExpr.evalPlayerFilter g env who).foldl (fun g p =>
        (g.createEffect (.jaceLoyaltyAtInstantSpeedThisTurn p) (cause := some cause)).logMsg
          s!"Until end of turn, {(g.player p).name} may activate loyalty abilities of planeswalkers they control any time they could cast an instant") g
    | _ => g
  | .combat cr =>
    match cr with
    | .cantBlock _ =>
      g.createEffect (.gameRule .creaturesWithoutFlyingCantBlock dur) (cause := some cause)
        |>.logMsg "Creatures without flying can't block this turn"
    | .assignCombatDamageByToughness _ _ =>
      g.createEffect (.assignCombatDamageEqualToughnessUntilEot ctx.controller) (cause := some cause)
        |>.logMsg s!"Creatures {(g.player ctx.controller).name} controls assign combat damage equal to their toughness this turn"
    | .cantAttackPlayer atkPred _ (some _) =>
      let attackers : Array PlayerId :=
        match ctx.targets[0]? with
        | some (Target.player pid) => if g.stillInGame pid then #[pid] else #[]
        | _ =>
          match atkPred with
          | .all ps =>
            let pf? := ps.findSome? fun | .controlledBy pf => some pf | _ => none
            match pf? with
            | some pf => (EvalExpr.evalPlayerFilter g env pf).filter g.stillInGame
            | none => (g.livingOpponents ctx.controller).map (·.id)
          | _ => (g.livingOpponents ctx.controller).map (·.id)
      attackers.foldl (fun g pid =>
        (g.createEffect (.cantAttackJacesThisTurn pid ctx.controller) (cause := some cause)).logMsg
          s!"{(g.player pid).name}'s creatures can't attack Jaces {(g.player ctx.controller).name} controls this turn") g
    | _ => g
  | .game gr =>
    match gr with
    | .legendRuleDisabled who =>
      (EvalExpr.evalPlayerFilter g env who).foldl (fun g p =>
        (g.createEffect (.legendRuleOffThisTurn p) (cause := some cause)).logMsg
          s!"The legend rule doesn't apply to permanents {(g.player p).name} controls this turn") g
    | _ => g
  | .costMod target mod _ =>
    match target, mod with
    | .spells who pred _ _ _, .reduceGeneric amtExpr =>
      let n := (EvalExpr.evalValue g env amtExpr).toNat
      let pids := EvalExpr.evalPlayerFilter g env who
      match pred with
      | .hasType ty => pids.foldl (fun g p => g.grantTypeCostLessThisTurn p ty n) g
      | .hasSupertype sup => pids.foldl (fun g p => g.grantSupertypeCostLessThisTurn p sup n) g
      | _ => g
    | .spells who _ _ _ _, .alternativeFree =>
      (EvalExpr.evalPlayerFilter g env who).foldl (fun g p =>
        g.createEffect (.pendingFreeRGCreatureThisTurn p) (cause := some cause)) g
    | _, _ => g
  | .trigger _ => g

private def execInstallEffect (g : Game) (ctx : InterpCtx) (op : InstallEffectOp) : Game :=
  let env := interpEnv g ctx
  let cause := interpCause g ctx
  match op with
  | .applyContinuous durExpr affectedExpr mod =>
    match EvalExpr.evalDuration g env durExpr with
    | none =>
      match mod with
      | .gainControl _ =>
        g.logMsg s!"{g.fraSourceName ctx.sourceId} has left the battlefield. You won't gain control."
      | _ => g
    | some dur =>
      let durStillValid : Bool :=
        match dur with
        | .whileSourceOnBattlefield sid | .untilSourceLeaves sid =>
          (g.findObject? sid).any (·.isOnBattlefield)
        | _ => true
      if !durStillValid then
        match mod with
        | .gainControl _ =>
          g.logMsg s!"{g.fraSourceName ctx.sourceId} has left the battlefield. You won't gain control."
        | _ => g
      else
        let live := (resolveLiveObjects g env affectedExpr).filter (·.isOnBattlefield)
        if live.isEmpty then
          if affectedExpr == .this then g.logMsg "The source is no longer in play" else g
        else
          match mod with
          | .exchangeControl otherExpr =>
            let pair? : Option (GameObject × GameObject) :=
              match (resolveLiveObjects g env otherExpr).filter (·.isOnBattlefield) with
              | others =>
                match live[0]?, others[0]? with
                | some a, some b => some (a, b)
                | some a, none =>
                  match live[1]? with
                  | some b => some (a, b)
                  | none => none
                | _, _ => none
            match pair? with
            | none => g
            | some (a, b) =>
              match g.controllerOf a, g.controllerOf b with
              | some c1, some c2 =>
                if c1 == c2 || !g.stillInGame c1 || !g.stillInGame c2 then g
                else
                  g.withBatch (some cause) fun g =>
                    let g := g.createEffect (.layered (.objects #[a.id]) (.control c2) dur) (cause := some cause)
                    let g := g.createEffect (.layered (.objects #[b.id]) (.control c1) dur) (cause := some cause)
                    g.logMsg s!"{(g.player c1).name} and {(g.player c2).name} exchange control of {g.name a} and {g.name b}"
              | _, _ => g
          | _ =>
            g.withBatch (some cause) fun g =>
              live.foldl (fun g o =>
                match g.findObject? o.id with
                | some cur =>
                  if cur.isOnBattlefield then applyContinuousModToObj g env ctx cur dur mod cause else g
                | none => g) g
  | .applyRule durExpr rule =>
    match EvalExpr.evalDuration g env durExpr with
    | none => g
    | some dur => applyRuleMod g env ctx dur rule cause
  | .applyReplacement durExpr spec =>
    match EvalExpr.evalDuration g env durExpr with
    | none => g
    | some dur =>
      match spec with
      | .exileOnLeaveStack => g.teferiExileSpell
      | .exileInsteadOfDying scope _ =>
        let live := (resolveLiveObjects g env scope.toExpr).filter (·.isOnBattlefield)
        live.foldl (fun g o =>
          (g.createEffect (.exileIfDiesUntilEot o.id) (cause := some cause)).logMsg
            s!"If {g.name o} would die this turn, exile it instead") g
      | .preventDamage subj _ =>
        let srcId? : Option ObjectId :=
          match dur with
          | .whileSourceOnBattlefield sid => some sid
          | _ => ctx.sourceId
        match subj, srcId? with
        | .self, some sid =>
          match (resolveLiveObjects g env (.target 0))[0]? with
          | some o => g.createEffect (.preventDamageWhileSource o.id sid) (cause := some cause)
          | none => g
        | .matching filter, some sid =>
          let live := (resolveLiveObjects g env filter.toExpr).filter (·.isOnBattlefield)
          live.foldl (fun g o => g.createEffect (.preventDamageWhileSource o.id sid) (cause := some cause)) g
        | _, _ => g
      | _ => g
  | .createDelayedTrigger spec =>
    let src := ctx.sourceId.bind g.damageSourceById?
    let stepEnv := g.currentStepEnv
    match spec.pattern with
    | .stepEachUpkeep =>
      let count : Nat :=
        match spec.effect.body with
        | .create (.tokens _ cntExpr _ _) => (EvalExpr.evalValue g env cntExpr).toNat
        | _ => 1
      if count == 0 then g
      else
        g.registerDelayedTrigger {
          controller := ctx.controller, source := src, kind := .eaglesBirds count,
          cause, stepEnv, instruction? := some spec.effect.body }
          |>.logMsg s!"At the beginning of the next upkeep, {count} Bird Soldier token(s) will be created"
    | .stepEachEndStep =>
      let count : Nat :=
        match spec.effect.body with
        | .player (.inspectLibrary { source := .revealUntil _ _ cntExpr _, .. }) =>
          (EvalExpr.evalValue g env cntExpr).toNat
        | _ => 0
      g.registerDelayedTrigger {
        controller := ctx.controller, source := src, kind := .endStepSynthetic count,
        cause, stepEnv, instruction? := some spec.effect.body }
        |>.logMsg "Those creatures return as revealed cards at the next end step"
    | .youAttack =>
      g.attackPumpPerPlains ctx.controller
    | .youCastInstantOrSorcery =>
      g.registerDelayedTrigger {
        controller := ctx.controller, source := src, kind := .copyNextInstantSorceryThisTurn,
        cause, stepEnv, instruction? := some spec.effect.body }
        |>.logMsg s!"When {(g.player ctx.controller).name} next casts an instant or sorcery spell this turn, it is copied"
    | .castSpell .you (.all #[.any #[.hasType .instant, .hasType .sorcery], .stat .manaValue .le (.objectStat .power .this)]) =>
      let pw := g.sourcePowerAtResolution ctx.sourceId ctx.lastKnownPower
      g.registerDelayedTrigger {
        controller := ctx.controller, source := src,
        kind := .lokiCopyNextInstantSorceryThisTurn ctx.sourceId pw,
        cause, stepEnv, instruction? := some spec.effect.body }
        |>.logMsg s!"The next instant or sorcery with mana value {pw} or less will be copied"
    | .activateAbility _ _ .manaAbility =>
      g.createEffect (.mountainExtraRedThisTurn ctx.controller 1) (cause := some cause)
        |>.logMsg s!"Until end of turn, whenever {(g.player ctx.controller).name} taps a Mountain for mana, add an additional \{R}"
    | _ =>
      -- Generic delayed trigger materialized as a temporary command-zone object
      let trigAb : TriggeredAbility := {
        word := .when
        pattern := spec.pattern
        grouping := spec.grouping
        interveningIf? := spec.interveningIf?
        effect := spec.effect
      }
      let effectCard : CardDef := {
        name := s!"{g.fraSourceName ctx.sourceId} effect", types := #[]
        triggeredAbilities := #[trigAb]
      }
      let untilTurnOf :=
        match spec.duration with
        | .untilNextTurnOf _ => some ctx.controller
        | _ => none
      g.createCommandObject ctx.controller effectCard (untilTurnOf := untilTurnOf)

/-! ### Resumable Continuation-Stack Interpreter Core -/

private def pauseIfNeeded (g : Game) (st : InterpState) (pendingBefore : Pending)
    (randomBefore : AfterRandom) : Game × Bool :=
  if g.pending == .none && g.afterRandom == .none then (g, false)
  else if let .chooseReplacement .. := g.pending then
    (g.chainPendingReplacement (.continueInterpreter st), true)
  else if g.pending != pendingBefore && g.pending != .none then
    match g.pending with
    | .resolveRandom .. =>
      let g := g.change (.interpWait? (some st))
      let g := if g.afterRandom == .none then g.change (.afterRandom (.continueInterpreter st.ctx.controller)) else g
      (g, true)
    | _ =>
      (g.change (.interpWait? (some st)), true)
  else if g.afterRandom != randomBefore && g.afterRandom != .none then
    (g.change (.interpWait? (some st)), true)
  else (g, false)

private partial def evalCondWithCtx (g : Game) (env : EvalEnv) (ctx : InterpCtx)
    (cond : Condition) : Bool :=
  match cond with
  | .castPred (.castFrom .graveyard .this) =>
    ctx.castFromGraveyard || EvalExpr.evalCondition g env cond
  | .castPred (.castFrom .hand .this) =>
    if ctx.castFromGraveyard then false else EvalExpr.evalCondition g env cond
  | .castPred (.wasKicked .this) =>
    ctx.kicked || EvalExpr.evalCondition g env cond
  | .castPred (.giftPromised .this) =>
    ctx.giftPromised || EvalExpr.evalCondition g env cond
  | .not inner => !evalCondWithCtx g env ctx inner
  | .all cs => cs.all (evalCondWithCtx g env ctx)
  | .any cs => cs.any (evalCondWithCtx g env ctx)
  | _ => EvalExpr.evalCondition g env cond

/-- Resume the unified `Instruction` continuation-stack machine from `st`. -/
partial def resumeInterpreter (g : Game) (st : InterpState) : Game := Id.run do
  let mut g := g
  let mut ctx := st.ctx
  let mut queue := st.queue
  let mut stack := st.stack
  let mut fuel : Nat := 2000
  while fuel > 0 do
    fuel := fuel - 1
    -- If a replacement or interactive pause is already open, suspend immediately.
    if let .chooseReplacement .. := g.pending then
      return g.chainPendingReplacement (.continueInterpreter { ctx, queue, stack })
    if g.pending != .none then
      return g.change (.interpWait? (some { ctx, queue, stack }))
    match queue[0]? with
    | none =>
      -- Pop the top continuation frame on `stack`.
      match stack.back? with
      | none => return g
      | some cont =>
        stack := stack.pop
        match cont with
        | .seqRest rest =>
          queue := rest
        | .bindClose v startEventIdx stepEffectId body override? =>
          let outcome := g.summarizeStepOutcome startEventIdx stepEffectId override?
          g := g.change (.bindStepOutcome v outcome)
          let shareCause : Bool :=
            match body with
            | .installEffect (.createDelayedTrigger ..) => true
            | .life (.lose _ (.aggregate .sum (.stat .manaValue) (.stepObjects _))) => true
            | _ => false
          if shareCause then
            ctx := { ctx with oneShotEffectId := stepEffectId }
          else if g.currentResolvingContext?.isSome then
            let id : EffectId := ⟨max 1 g.nextEffectId⟩
            g := g.change (.nextEffectId (id.raw + 1))
            ctx := { ctx with oneShotEffectId := id }
          else
            ctx := { ctx with oneShotEffectId := ⟨0⟩ }
          queue := #[body]
        | .forEachPlayerRest v players body =>
          match players[0]? with
          | none => pure ()
          | some p =>
            let rem := players.extract 1 players.size
            if !rem.isEmpty then
              stack := stack.push (.forEachPlayerRest v rem body)
            g := g.change (.bindStepOutcome v { players := #[p], succeeded := true })
            queue := #[body]
        | .forEachObjectRest v objects body =>
          match objects[0]? with
          | none => pure ()
          | some oid =>
            let rem := objects.extract 1 objects.size
            if !rem.isEmpty then
              stack := stack.push (.forEachObjectRest v rem body)
            g := g.change (.bindStepOutcome v { objects := #[oid], succeeded := true })
            queue := #[body]
        | .branchOnChoice onYes onNo =>
          -- Used when an external choice records a boolean in `stepEnv`
          let ok := (g.currentStepEnv.find? (·.1 == ⟨999⟩)).any (·.2.succeeded)
          queue := #[if ok then onYes else onNo]
        | .bindChosenAndRun _ body =>
          queue := #[body]
    | some instr =>
      let restQueue := queue.extract 1 queue.size
      queue := restQueue
      -- Recruit canonical pattern preserves `Pending.recruitDiscard` expected by Recruit rulings/tests
      if instr == Instruction.recruit .you then
        let pendingBefore := g.pending
        let randomBefore := g.afterRandom
        g := g.beginRecruit ctx.controller
        let (g', paused) := pauseIfNeeded g { ctx, queue, stack } pendingBefore randomBefore
        if paused then return g'
        g := g'
      else
        match instr with
        | .noop => pure ()
        | .seq steps =>
          let env := interpEnv g ctx
          let pendingBefore := g.pending
          let randomBefore := g.afterRandom
          match steps.toList with
          | [.player (.inspectLibrary {
                source := .millCards .you nExpr
                action := .takeMatching (.isKind .permanentCard) (.upTo (.const 1)) (.hand .controller)
                rest := .leaveInPlace, .. }),
             .life (.gain .you lifeExpr)] =>
            let n := (EvalExpr.evalValue g env nExpr).toNat
            let life := (EvalExpr.evalValue g env lifeExpr).toNat
            let lib := (g.player ctx.controller).library
            let take := Nat.min n lib.size
            let preIds := lib.extract (lib.size - take) lib.size
            g := g.mill ctx.controller n
            if let .chooseReplacement .. := g.pending then
              g := g.chainPendingReplacement
                (.finishPostStep (.offerPutMilledPermanentOrGainLife ctx.controller preIds life))
            else
              let choices := preIds.filterMap fun id =>
                match g.followMilledPublic? id with
                | some o => if g.isPermanentCard o then some o.id else none
                | none => none
              if choices.isEmpty then
                g := g.gainLife ctx.controller life
              else
                g := g.beginFraChoice ctx.controller (.mayPutMilledPermanent choices life)
                  s!"{(g.player ctx.controller).name} may put a permanent card milled this way into their hand"
            let (g', paused) := pauseIfNeeded g { ctx, queue, stack } pendingBefore randomBefore
            if paused then return g'
            g := g'
          | [.moveZone (.target 0) (.library .owner (.fromTop (.const 2)) true) .put _,
             .player (.connive (.target 1))] =>
            let connive? : Option ObjectId :=
              (resolveLiveObjects g env (.target 1))[0]?.map GameObject.id
            match (resolveLiveObjects g env (.target 0))[0]? with
            | some o =>
              if o.isOnBattlefield then
                g := g.beginFraChoice o.owner (.tricksterLibrary ctx.controller o.id connive? ctx.sourceId)
                  s!"{(g.player o.owner).name} puts {g.name o} second from the top or on the bottom of their library"
              else if let some cid := connive? then
                g := g.applyConnive ctx.controller (some cid)
            | none =>
              if let some cid := connive? then
                g := g.applyConnive ctx.controller (some cid)
            let (g', paused) := pauseIfNeeded g { ctx, queue, stack } pendingBefore randomBefore
            if paused then return g'
            g := g'
          | [.player (.inspectLibrary {
                source := .topCards whoExpr nExpr false
                action := .takeMatching (.hasType .land) .anyNumber (.battlefield .controller) { tapped := true, .. }
                rest := .shuffleIntoLibrary, .. }),
             .life (.gain .you lifeExpr)] =>
            let p := (EvalExpr.evalPlayer g env whoExpr)[0]?.getD ctx.controller
            let n := (EvalExpr.evalValue g env nExpr).toNat
            let life := (EvalExpr.evalValue g env lifeExpr).toNat
            let ids := g.scryLookedIds p n
            g := g.logLookAtTop p ids.size ids ctx.sourceId
            let lands := ids.filter fun id => (g.findObject? id).any (g.isLand ·)
            if lands.isEmpty then
              g := (g.requestShuffle p (.gainLife p life)).continueIfShuffled
            else
              g := g.offerCardChoice p lands lands.size (.landsTappedGainLife life)
                s!"{(g.player p).name} may put any number of land cards from among them onto the battlefield tapped"
            let (g', paused) := pauseIfNeeded g { ctx, queue, stack } pendingBefore randomBefore
            if paused then return g'
            g := g'
          | [.player (.drawCards .you (.const 2)),
             .bind _ (.moveZone (.inZones (.handOf .you) .anyObject) .graveyard .discard _)
               (.ifCond (.exists (.filter (.stepObjects _) (.not (.hasType .land)))) (.queueReflexiveTrigger _) .noop)] =>
            g := g.draw ctx.controller 2
            if let .chooseReplacement .. := g.pending then
              g := g.chainPendingReplacement (.finishPostStep (.beginDiscardThenStun ctx.controller ctx.sourceId))
            else
              let cnt := Nat.min 2 (g.player ctx.controller).hand.size
              if cnt > 0 then
                g := g.beginFraChoice ctx.controller (.discardThenStun cnt ctx.sourceId)
                  s!"{(g.player ctx.controller).name} discards {cnt} card(s)"
            let (g', paused) := pauseIfNeeded g { ctx, queue, stack } pendingBefore randomBefore
            if paused then return g'
            g := g'
          | [.player (.reveal victimExpr (.inZones (.handOf _) .anyObject)),
             .moveZone (.inZones (.handOf _) (.not (.hasType .land))) .exile .exile
               { exileUntilSourceLeaves := true, choice? := some { revealFirst := true, .. }, .. }] =>
            match (EvalExpr.evalPlayer g env victimExpr)[0]? with
            | some victim =>
              g := g.revealHand victim
              if (g.revealedHandChoices victim false).isEmpty then
                g := g.logMsg s!"{(g.player victim).name} has no nonland card"
              else
                g := g.beginFraChoice ctx.controller (.exileFromRevealedHand victim ctx.sourceId)
                  s!"{(g.player ctx.controller).name} chooses a nonland card to exile"
            | none => pure ()
            let (g', paused) := pauseIfNeeded g { ctx, queue, stack } pendingBefore randomBefore
            if paused then return g'
            g := g'
          | [.moveZone (.inZones (.handOf .you) .anyObject) .graveyard .discard _,
             .player (.drawCards .you (.const 1)),
             .permanent (.modifyCounters (.put .plusOnePlusOne (.playerMetric .cardsDiscardedThisTurn .you)) .triggerSubject)] =>
            if (g.player ctx.controller).hand.isEmpty then
              g := g.draw ctx.controller 1
              if let .chooseReplacement .. := g.pending then
                g := g.chainPendingReplacement
                  (.finishPostStep (.addPlusOnesForLoggedDiscards ctx.controller ctx.triggerSubjectId))
              else
                let n := g.loggedDiscards ctx.controller
                match ctx.triggerSubjectId.bind g.findObject? with
                | some o => if o.isOnBattlefield && n > 0 then g := g.addPlusOnePlusOneTo o n
                | none => pure ()
            else
              g := g.beginFraChoice ctx.controller
                (.discardThen .drawThenCountersPerDiscard ctx.sourceId ctx.triggerSubjectId)
                s!"{(g.player ctx.controller).name} discards a card"
            let (g', paused) := pauseIfNeeded g { ctx, queue, stack } pendingBefore randomBefore
            if paused then return g'
            g := g'
          | [.stack (.mayCastOrPlay .this { duration := .whileInZone .this .exile, landsAllowed := false, .. }),
             .installEffect (.applyContinuous (.whileInZone .this .exile) (.target 0) (.grantActivated _))] =>
            match ctx.sourceId.bind (fun id => g.followMovedToZone? id (· == Zone.exile)) with
            | none => pure ()
            | some card =>
              let targets := resolveLiveObjects g env (.target 0)
              g := g.withBatch none fun g =>
                let perm : PlayPermission := { player := ctx.controller, whileExiled := true }
                let g := (g.createEffect (.playPermission card.id perm)).logMsg
                  s!"{(g.player ctx.controller).name} may cast {g.name card} for as long as it remains exiled"
                targets.foldl (fun g land =>
                  if land.isOnBattlefield then
                    let g := g.createEffect (.colorlessGrantUntilCast land.id card.id)
                    g.logMsg s!"{g.name land} gains \"\{T}: Add \{C}\{C}\" until {g.name card} is cast from exile"
                  else g) g
            let (g', paused) := pauseIfNeeded g { ctx, queue, stack } pendingBefore randomBefore
            if paused then return g'
            g := g'
          | _ =>
            if !steps.isEmpty then
              if !queue.isEmpty then
                stack := stack.push (.seqRest queue)
              queue := steps
        | .bind v step body =>
          let env := interpEnv g ctx
          let pendingBefore := g.pending
          let randomBefore := g.afterRandom
          let handledSpecial : Bool × Game :=
            match step, body with
            | .stack (.mayCastOrPlay objsExpr perm),
              .ifCond (.not (.stepSucceeded v'))
                (.damage (.deal .this (.players (.matching .opponent .any)) amtExpr _))
                .noop =>
              if v == v' && !perm.landsAllowed && !perm.freeCast && !perm.copyAndCast && !perm.asFlashback then
                let cause := interpCause g ctx
                let dmg := (EvalExpr.evalValue g env amtExpr).toNat
                let exiledNonland? := (resolveObjectIds g env objsExpr).findSome? fun cid =>
                  match g.findObject? cid with
                  | some o => if o.zone == .exile && !g.isLand o then some o else none
                  | none => none
                let g1 :=
                  match exiledNonland? with
                  | some card =>
                    (g.change (.pending (.mayCastExiledElseDamage ctx.controller card.id dmg ctx.sourceId))).logMsg
                      s!"{(g.player ctx.controller).name} may cast {g.name card} (or deal {dmg} damage to each opponent)"
                  | none =>
                    g.dealDamageToEachOpponent ctx.controller dmg
                      (source := ctx.sourceId.bind g.damageSourceById?) (cause := some cause)
                (true, g1)
              else (false, g)
            | .player (.choose whoExpr .creatureType),
              .moveZone (.inZones .battlefield (.all #[.hasType .creature, .not (.hasSubtype (.fromStep v'))]))
                (.hand .owner) .returnToHand _ =>
              if v == v' then
                let chooser := (EvalExpr.evalPlayer g env whoExpr)[0]?.getD ctx.controller
                let types := g.battlefieldCreatureTypes
                let g1 :=
                  if types.isEmpty then
                    g.logMsg s!"{(g.player chooser).name} has no creature type to choose"
                  else
                    g.beginFraChoice chooser (.palisadeCreatureType types)
                      s!"{(g.player chooser).name} chooses a creature type"
                (true, g1)
              else (false, g)
            | .player (.choose whoExpr .playerWithMostLife),
              .installEffect (.applyContinuous .untilEndOfTurn (.target 0)
                (.applyRule (.combat (.cantBeBlockedBy .self (.controlledBy (.ofExpr (.stepPlayers v'))))))) =>
              if v == v' then
                let chooser := (EvalExpr.evalPlayer g env whoExpr)[0]?.getD ctx.controller
                let g1 :=
                  match (resolveLiveObjects g env (.target 0))[0]? with
                  | some o =>
                    if o.isOnBattlefield && g.isCreature o then
                      let tied := g.playersWithMostLife
                      match tied.toList with
                      | [] => g
                      | [pid] => g.applyBlackGateUnblockable o.id pid
                      | _ =>
                        g.beginFraChoice chooser (.blackGatePlayer o.id tied)
                          s!"{(g.player chooser).name} chooses a player with the most life"
                    else g.logMsg "The target is no longer legal"
                  | none => g.logMsg "The target is no longer legal"
                (true, g1)
              else (false, g)
            | .forEach (.eachPlayer .any) _ (.moveZone _ .graveyard .sacrifice _),
              .ifCond (.exists (.filter (.stepObjects v') (.controlledBy .you)))
                (.create (.tokens .you (.const 1) .beast44trample _)) .noop =>
              if v == v' then
                (true, g.continueSacrificeEach ctx.controller g.apnapOrder #[])
              else (false, g)
            | .player (.searchLibrary sp),
              .optional .you (some cost) (.permanent (.setTapped (.stepObjects v') false)) .noop =>
              if v == v' && sp.filter == (.all #[.hasSupertype .basic, .hasType .land]) && sp.mods.tapped then
                match (cost.items[0]? : Option CostItem) with
                | some (.behold sub) =>
                  (true, g.beginLibrarySearch ctx.controller isBasicLandCard "a basic land card"
                    (.battlefieldTappedBeholdUntap sub))
                | _ => (false, g)
              else (false, g)
            | .moveZone (.inZones .battlefield (.hasType .creature)) .exile .exile _,
              .seq #[
                .forEach (.eachPlayer .any) v1
                  (.moveZone (.inZones (.handOf (.stepPlayers v2)) (.hasType .creature))
                    (.battlefield (.player (.stepPlayers v3))) .put { choice? := some { count := .anyNumber, .. }, .. }),
                .moveZone (.stepObjects v0) (.hand .owner) .put _,
                .installEffect (.applyReplacement .untilEndOfTurn .exileOnLeaveStack)
              ] =>
              if v == v0 && v1 == v2 && v2 == v3 then
                (true, g.applyWorldsWithinWorlds ctx.controller (ctx.sourceId.orElse (fun _ => g.resolvingSpell)))
              else (false, g)
            | _, _ => (false, g)
          if handledSpecial.1 then
            g := handledSpecial.2
            let (g', paused) := pauseIfNeeded g { ctx, queue, stack } pendingBefore randomBefore
            if paused then return g'
            g := g'
          else
            let (g', eid) : Game × EffectId :=
              let id : EffectId := ⟨max 1 g.nextEffectId⟩
              (g.change (.nextEffectId (id.raw + 1)), id)
            g := g'
            let startIdx := g.events.size
            if !queue.isEmpty then
              stack := stack.push (.seqRest queue)
            stack := stack.push (.bindClose v startIdx eid body none)
            ctx := { ctx with oneShotEffectId := eid }
            queue := #[step]
        | .ifCond cond thenBranch elseBranch =>
          let env := interpEnv g ctx
          let holds := evalCondWithCtx g env ctx cond
          if holds then
            -- Mark optionalOnceActed when an `optionalOnceUnusedThisTurn` guard passes
            if cond == .turnHistory .optionalOnceUnusedThisTurn then
              if let some sid := ctx.sourceId then
                g := g.record (GameEvent.optionalOnceActed g.turnNumber ctx.controller sid (cause := some (interpCause g ctx)))
            if !queue.isEmpty then
              stack := stack.push (.seqRest queue)
            queue := #[thenBranch]
          else if elseBranch != .noop then
            if !queue.isEmpty then
              stack := stack.push (.seqRest queue)
            queue := #[elseBranch]
        | .forEach iter v body =>
          let env := interpEnv g ctx
          if !queue.isEmpty then
            stack := stack.push (.seqRest queue)
          match iter with
          | .eachPlayer pf =>
            let ps := EvalExpr.evalPlayerFilter g env pf
            let wheelDrawExpr? : Option ValueExpr :=
              match pf, body with
              | .any, .optional (.stepPlayers v1) none
                  (.seq #[.moveZone (.inZones (.handOf (.stepPlayers v2)) .anyObject) .graveyard .discard _,
                          .player (.drawCards (.stepPlayers v3) amtExpr)]) .noop =>
                if v == v1 && v == v2 && v == v3 then some amtExpr else none
              | _, _ => none
            match wheelDrawExpr? with
            | some amtExpr =>
              let n := (EvalExpr.evalValue g env amtExpr).toNat
              let pendingBefore := g.pending
              let randomBefore := g.afterRandom
              let psLiving := ps.filter g.stillInGame
              match psLiving[0]? with
              | some next =>
                g := g.beginFraChoice next (.mayWheel n (psLiving.extract 1 psLiving.size) #[])
                  s!"{(g.player next).name} may discard their hand and draw {n} cards"
              | none => pure ()
              queue := #[]
              let (g', paused) := pauseIfNeeded g { ctx, queue, stack } pendingBefore randomBefore
              if paused then return g'
              g := g'
            | none =>
              match ps[0]? with
              | none => queue := #[]
              | some p0 =>
                let rem := ps.extract 1 ps.size
                if !rem.isEmpty then
                  stack := stack.push (.forEachPlayerRest v rem body)
                g := g.change (.bindStepOutcome v { players := #[p0], succeeded := true })
                queue := #[body]
          | .eachObject oe =>
            let oids := resolveObjectIds g env oe
            let batchCopy? : Option (PlayerExpr × Array CopyModification) :=
              match body with
              | .create (.tokens whoExpr (.const 1) (.copyOf (.stepObjects v') copyMods) tokMods) =>
                if v == v' && tokMods == {} then some (whoExpr, copyMods) else none
              | _ => none
            match batchCopy? with
            | some (whoExpr, copyMods) =>
              let cause := interpCause g ctx
              let pendingBefore := g.pending
              let randomBefore := g.afterRandom
              let pids := EvalExpr.evalPlayer g env whoExpr
              for p in pids do
                if g.stillInGame p && !oids.isEmpty then
                  let startEventIdx := g.events.size
                  let snapshots : Array CardDef := oids.filterMap fun oid =>
                    g.resolveTokenPrinted? (.copyOf .this copyMods) ctx.chosenX
                      { sourceId := some oid } (controller := p)
                  if !snapshots.isEmpty then
                    g := g.withBatch (some cause) fun g =>
                      g.copyNontokenCreaturesStep p snapshots
                    if let .chooseReplacement .. := g.pending then
                      g := g.chainPendingReplacement
                        (.finishPostStep (.copyNontokenCreaturesAfterEnter startEventIdx))
                    else
                      g := g.finishCopyNontokenCreaturesAfterEnter startEventIdx
              queue := #[]
              let (g', paused) := pauseIfNeeded g { ctx, queue, stack } pendingBefore randomBefore
              if paused then return g'
              g := g'
            | none =>
              match oids[0]? with
              | none => queue := #[]
              | some o0 =>
                let rem := oids.extract 1 oids.size
                if !rem.isEmpty then
                  stack := stack.push (.forEachObjectRest v rem body)
                g := g.change (.bindStepOutcome v { objects := #[o0], succeeded := true })
                queue := #[body]
          | .eachTargetSlot =>
            queue := #[body]
          | .repeatTimes cntExpr =>
            let n := (EvalExpr.evalValue g env cntExpr).toNat
            queue := Array.replicate n body
        | .optional whoExpr cost? onYes onNo =>
          let env := interpEnv g ctx
          let chooser := (EvalExpr.evalPlayer g env whoExpr)[0]?.getD ctx.controller
          let pendingBefore := g.pending
          let randomBefore := g.afterRandom
          let eff : Effect := { targeting := .of ctx.targetSpec, body := onYes }
          match cost? with
          | some cost =>
            if cost == CostSpec.ofMana { symbols := #[.hybrid .white .black] } then
              -- CR 702.101a Extort
              g := g.beginFraChoice chooser (.mayPayExtort ctx.sourceId)
                s!"{(g.player chooser).name} may pay \{W/B} (extort)"
            else if cost == CostSpec.sacrificeArtifactOrDiscardCard then
              let n := match onYes with | .player (.drawCards _ (.const k)) => k.toNat | _ => 1
              g := (g.change (.pending (.maySacArtifactOrDiscard chooser n))).logMsg
                s!"{(g.player chooser).name} may sacrifice an artifact or discard a card to draw {n}"
            else
              match (cost.items[0]? : Option CostItem) with
              | some (.discard _ _) =>
                match onYes with
                | .player (.drawCards _ (.const n)) =>
                  g := g.beginMayDiscardDraw chooser n.toNat
                | .player (.searchLibrary sp) =>
                  if sp.filter == .hasType .enchantment && !(g.player chooser).hand.isEmpty then
                    g := g.beginFraChoice chooser (.mayDiscardThen .searchEnchantmentToHand ctx.sourceId)
                      s!"{(g.player chooser).name} may discard a card"
                  else if !(g.player chooser).hand.isEmpty then
                    g := g.beginMay chooser eff ctx.targets onYes ctx.sourceId
                | .queueReflexiveTrigger ab =>
                  match ab.effect.body with
                  | .damage (.deal _ (.targetSlot 0) (.const n) _) =>
                    if !(g.player chooser).hand.isEmpty then
                      g := g.beginFraChoice chooser (.mayDiscardThen (.reflexiveDamageAnyTarget n.toNat) ctx.sourceId)
                        s!"{(g.player chooser).name} may discard a card"
                  | _ =>
                    g := g.beginMay chooser eff ctx.targets onYes ctx.sourceId
                | _ =>
                  g := g.beginMay chooser eff ctx.targets onYes ctx.sourceId
              | some (.mana mc) =>
                let gen := mc.genericCount
                match onYes with
                | .player (.proliferate _ (.const times) _) =>
                  g := g.beginFraChoice chooser (.mayPayThen gen (.proliferate times.toNat) ctx.sourceId)
                    s!"{(g.player chooser).name} may pay \{{gen}}"
                | .queueReflexiveTrigger ab =>
                  let nxt? : Option FraNext :=
                    match ab.effect.body with
                    | .moveZone .allTargets .graveyard .destroy _ => some .reflexiveDestroyPerOpponent
                    | .moveZone (.target 0) (.battlefield .controller) .put mods =>
                      if mods.tapped then some .reflexiveReturnLandTapped else none
                    | .damage (.deal _ (.targetSlot 0) (.const n) _) => some (.reflexiveDamageAnyTarget n.toNat)
                    | _ => none
                  match nxt? with
                  | some nxt =>
                    g := g.beginFraChoice chooser (.mayPayThen gen nxt ctx.sourceId)
                      s!"{(g.player chooser).name} may pay \{{gen}}"
                  | none =>
                    g := g.beginMay chooser eff ctx.targets onYes ctx.sourceId
                | .moveZone .this (.hand .owner) .returnToHand _ =>
                  g := g.beginFraChoice chooser (.mayPayThen gen .returnSourceToHand ctx.sourceId)
                    s!"{(g.player chooser).name} may pay \{{gen}}"
                | _ =>
                  g := g.beginMay chooser eff ctx.targets onYes ctx.sourceId
              | some (.sacrifice _ (.filter pred)) =>
                let types : Array CardType :=
                  match pred with
                  | .hasType t => #[t]
                  | .any ps => ps.filterMap fun | .hasType t => some t | _ => none
                  | _ => #[.creature]
                let eligible := (g.permanentsOf chooser).filter fun o => EvalExpr.evalObjectPred g env (.live o) pred
                if !eligible.isEmpty then
                  match onYes with
                  | .player (.searchLibrary sp) =>
                    if pred == .hasType .planeswalker && sp.filter == .hasType .planeswalker then
                      g := g.beginFraChoice chooser .maySacrificePlaneswalker
                        s!"{(g.player chooser).name} may sacrifice a planeswalker"
                    else
                      let resCtx : SpellResolutionCtx := {
                        castFromGraveyard := ctx.castFromGraveyard, kicked := ctx.kicked,
                        giftPromised := ctx.giftPromised, chosenX := some ctx.chosenX,
                        lastKnownPower := ctx.lastKnownPower, lastKnownToughness := ctx.lastKnownToughness }
                      g := g.beginMay chooser eff ctx.targets onYes ctx.sourceId (resCtx := resCtx)
                  | _ =>
                    let next? : Option FraNext :=
                      match onYes with
                      | .create (.tokens _ (.const n) .heartwood _) => some (.tappedHeartwoods n.toNat)
                      | .create (.tokens _ (.const 1) .beast44trample _) => some .beastToken
                      | .forEach (.eachPlayer .opponent) _ (.moveZone _ .graveyard .sacrifice _) =>
                        some .eachOpponentSacrificesCreature
                      | _ => none
                    match next? with
                    | some nxt =>
                      g := g.beginFraChoice chooser (.maySacrificeThen types nxt ctx.sourceId)
                        s!"{(g.player chooser).name} may sacrifice a permanent"
                    | none =>
                      let resCtx : SpellResolutionCtx := {
                        castFromGraveyard := ctx.castFromGraveyard, kicked := ctx.kicked,
                        giftPromised := ctx.giftPromised, chosenX := some ctx.chosenX,
                        lastKnownPower := ctx.lastKnownPower, lastKnownToughness := ctx.lastKnownToughness }
                      g := g.beginMay chooser eff ctx.targets onYes ctx.sourceId (resCtx := resCtx)
              | some (.removeCounters _ (some .plusOnePlusOne) .self) =>
                match ctx.sourceId.bind g.findObject? with
                | some src =>
                  if src.isOnBattlefield && src.status.plusOnePlusOne > 0 then
                    g := g.beginFraChoice chooser (.mayMovePlusOne src.id)
                      s!"{(g.player chooser).name} may remove a +1/+1 counter from {g.name src}"
                | none => pure ()
              | some (.payLife amtExpr) =>
                let n := (EvalExpr.evalValue g env amtExpr).toNat
                let pl := g.player chooser
                if pl.life > Int.ofNat n && n > 0 then
                  let before := pl.life
                  let payCause : Option EventCause :=
                    g.currentResolvingContext?.map fun (src, _) =>
                      .costPayment .life chooser
                        (g.resolvingAbility <|> g.resolvingSpell <|> ctx.sourceId <|> src)
                  match g.payLifeCost chooser n (cause := payCause) with
                  | .ok g' =>
                    g := g'
                    if (g.player chooser).life < before then
                      if !queue.isEmpty then
                        stack := stack.push (.seqRest queue)
                      queue := #[onYes]
                  | .error _ =>
                    g := g.logMsg s!"{pl.name} declines to pay {n} life"
                else
                  g := g.logMsg s!"{pl.name} declines to pay {n} life"
              | some (.exile _ .stack .self) =>
                match g.resolvingSpell.bind g.findObject? with
                | some spell =>
                  if spell.zone == .stack && !spell.isCopy &&
                      (g.sphinxsApproachesInGraveyard chooser).size ≥ 4 then
                    g := g.beginFraChoice chooser (.sphinxsApproach spell.id)
                      s!"{(g.player chooser).name} may exile Sphinx's Approach and four cards named Sphinx's Approach"
                | none => pure ()
              | _ =>
                let resCtx : SpellResolutionCtx := {
                  castFromGraveyard := ctx.castFromGraveyard, kicked := ctx.kicked,
                  giftPromised := ctx.giftPromised, chosenX := some ctx.chosenX,
                  lastKnownPower := ctx.lastKnownPower, lastKnownToughness := ctx.lastKnownToughness }
                g := g.beginMay chooser eff ctx.targets onYes ctx.sourceId (resCtx := resCtx)
          | none =>
            let topOrBotDmg? : Option ValueExpr :=
              match onYes, onNo with
              | .seq #[.moveZone (.target 0) (.library .owner .top false) .put _,
                       .damage (.deal _ _ dmgExpr _)],
                .moveZone (.target 0) (.library .owner .bottom false) .put _ =>
                some dmgExpr
              | .moveZone (.target 0) (.library .owner .top false) .put _,
                .moveZone (.target 0) (.library .owner .bottom false) .put _ =>
                some (.const 0)
              | _, _ => none
            match topOrBotDmg? with
            | some dmgExpr =>
              match (resolveLiveObjects g env (.target 0))[0]? with
              | some o =>
                if o.isOnBattlefield then
                  let dmg := (EvalExpr.evalValue g env dmgExpr).toNat
                  let sid := ctx.sourceId.orElse (fun _ => g.resolvingSpell)
                  g := g.beginFraChoice o.owner (.topOrBottomDamage o.id dmg sid)
                    s!"{(g.player o.owner).name} may put {g.name o} on top of their library"
              | none => pure ()
            | none =>
              let resCtx : SpellResolutionCtx := {
                castFromGraveyard := ctx.castFromGraveyard, kicked := ctx.kicked,
                giftPromised := ctx.giftPromised, chosenX := some ctx.chosenX,
                lastKnownPower := ctx.lastKnownPower, lastKnownToughness := ctx.lastKnownToughness }
              match onYes with
              | .permanent (.attach _ _ true) =>
                g := g.beginMay chooser eff ctx.targets onYes ctx.sourceId (resCtx := resCtx)
              | .permanent (.modifyCounters (.moveAll .this none) (.target 0)) =>
                match ctx.sourceId.bind g.findObject?, (resolveLiveObjects g env (.target 0))[0]? with
                | some src, some tgt =>
                  if src.isOnBattlefield && src.status.hasCounters && tgt.isOnBattlefield then
                    g := g.beginFraChoice chooser (.mayMoveAllCounters src.id tgt.id)
                      s!"{(g.player chooser).name} may move all counters from {g.name src} onto {g.name tgt}"
                | _, _ => pure ()
              | .player (.searchLibrary sp) =>
                if sp.filter == (.all #[.hasSupertype .basic, .hasType .land]) && sp.mods.tapped then
                  let (_, hi) := evalInterpCountRange g env sp.count
                  g := g.offerMaySearchBasics chooser hi
                else if sp.filter == .hasType .land && sp.mods.tapped && sp.count == .upTo .eventAmount then
                  let (_, hi) := evalInterpCountRange g env sp.count
                  if hi > 0 then
                    g := g.beginFraChoice chooser (.mayThen (.searchLandsTapped hi) ctx.sourceId)
                      s!"{(g.player chooser).name} may search for up to {hi} land cards"
                else
                  g := g.beginMay chooser eff ctx.targets onYes ctx.sourceId (resCtx := resCtx)
              | .player (.inspectLibrary { source := .outsideTheGame _ _, .. }) =>
                let g1 := g.materializeSideboard chooser
                let names := (g1.outsideCards chooser).foldl (fun acc o =>
                  let nm := g1.name o
                  if acc.contains nm then acc else acc.push nm) (#[] : Array String)
                if names.size < 2 then
                  g := g1.logMsg s!"{(g1.player chooser).name} has no two cards with different names outside the game"
                else
                  g := g1.beginFraChoice chooser .extrapolateReveal
                    s!"{(g1.player chooser).name} may reveal two cards with different names from outside the game"
              | _ =>
                g := g.beginMay chooser eff ctx.targets onYes ctx.sourceId (resCtx := resCtx)
          let _ := onNo
          let (g', paused) := pauseIfNeeded g { ctx, queue, stack } pendingBefore randomBefore
          if paused then return g'
          g := g'
        | .unlessPays payerExpr cost ifUnpaid =>
          let gen := cost.mana.genericCount
          let pendingBefore := g.pending
          let randomBefore := g.afterRandom
          let eff : Effect := {
            targeting := if ifUnpaid.mentionsTarget then .of ctx.targetSpec else .of .none
            body := ifUnpaid
          }
          let resCtx : SpellResolutionCtx := {
            castFromGraveyard := ctx.castFromGraveyard, kicked := ctx.kicked,
            giftPromised := ctx.giftPromised, chosenX := some ctx.chosenX,
            lastKnownPower := ctx.lastKnownPower, lastKnownToughness := ctx.lastKnownToughness }
          if ifUnpaid == Instruction.counter .triggerSubject then
            -- CR 702.21a: Ward trigger opens `Pending.payWard` against the targeting stack object.
            let abObj? := g.resolvingAbilityObject?
            let causeId? := abObj?.bind (·.fraCauseId)
            let payer? :=
              (abObj?.bind (·.fraCauseController)).orElse (fun _ =>
                causeId?.bind (fun cid => (g.stackEntry? cid).map (·.controller)))
            match causeId?, payer? with
            | some spellId, some payer =>
              match g.findObject? spellId with
              | some o =>
                if o.zone == .stack then
                  let who := (g.player payer).name
                  let costPhrase :=
                    match cost.soleGenericMana? with
                    | some n => s!"pay \{{n}}"
                    | none =>
                      if cost == CostSpec.sacrificeLegendaryArtifactOrCreature then
                        "sacrifice a legendary artifact or creature"
                      else
                        match cost.items.toList with
                        | [.sacrifice (.count (.const n)) (.filter .anyObject)] =>
                          if n == 1 then "sacrifice a permanent" else s!"sacrifice {n} permanents"
                        | [.mana m] => s!"pay {m}"
                        | _ => cost.toInlinePhrase
                  let msg := s!"{who} may {costPhrase} or the spell is countered (ward)"
                  g := (g.change (.pending (.payWard payer spellId cost))).logMsg msg
              | none => pure ()
            | _, _ => pure ()
          else if payerExpr == .activePlayer then
            if !g.isOnActiveTeam ctx.controller && g.stillInGame g.activePlayer then
              let ap := g.activePlayer
              g := (g.changes #[
                .pending (.payOrLetCounter ap gen none),
                .unlessPaysInstead (some eff),
                .unlessPaysController ctx.controller,
                .unlessPaysTargets #[.player ap],
                .unlessPaysSource ctx.sourceId,
                .unlessPaysDue false,
                .unlessPaysResCtx resCtx]).logMsg
                s!"{(g.player ap).name} may pay \{{gen}} or their creatures can't attack Jaces {(g.player ctx.controller).name} controls this turn"
          else
            g := g.beginUnlessPays ctx.controller eff ctx.targets ifUnpaid gen ctx.sourceId (resCtx := resCtx)
          let (g', paused) := pauseIfNeeded g { ctx, queue, stack } pendingBefore randomBefore
          if paused then return g'
          g := g'
        | .chooseModes spec =>
          -- Modes announced on the stack are already selected in `SpellResolution`/`TriggeredAbilities`;
          -- resolution-time `chooseModes` opens `beginSpellOr` when multiple branches exist.
          if spec.chooseAtResolution && spec.modes.size > 1 then
            let pendingBefore := g.pending
            let randomBefore := g.afterRandom
            let eff : Effect := { targeting := .of ctx.targetSpec, body := .noop }
            let resCtx : SpellResolutionCtx := {
              castFromGraveyard := ctx.castFromGraveyard, kicked := ctx.kicked,
              giftPromised := ctx.giftPromised, chosenX := some ctx.chosenX,
              lastKnownPower := ctx.lastKnownPower, lastKnownToughness := ctx.lastKnownToughness }
            g := g.beginSpellOr ctx.controller eff ctx.targets
              (spec.modes.toList.map (·.body)) ctx.sourceId (resCtx := resCtx) (libraryTopBottom := false)
            let (g', paused) := pauseIfNeeded g { ctx, queue, stack } pendingBefore randomBefore
            if paused then return g'
            g := g'
          else if let some m0 := spec.modes[0]? then
            if !queue.isEmpty then
              stack := stack.push (.seqRest queue)
            queue := #[m0.body]
        | .queueReflexiveTrigger whenDone =>
          g := g.putReflexiveTrigger ctx.controller ctx.sourceId whenDone.effect
        | .moveZone objs dest verb mods =>
          let pendingBefore := g.pending
          let randomBefore := g.afterRandom
          g := execMoveZone g ctx objs dest verb mods
          let (g', paused) := pauseIfNeeded g { ctx, queue, stack } pendingBefore randomBefore
          if paused then return g'
          g := g'
        | .create op =>
          let pendingBefore := g.pending
          let randomBefore := g.afterRandom
          g := execCreate g ctx op
          let (g', paused) := pauseIfNeeded g { ctx, queue, stack } pendingBefore randomBefore
          if paused then return g'
          g := g'
        | .permanent op =>
          let pendingBefore := g.pending
          let randomBefore := g.afterRandom
          g := execPermanent g ctx op
          let (g', paused) := pauseIfNeeded g { ctx, queue, stack } pendingBefore randomBefore
          if paused then return g'
          g := g'
        | .damage op =>
          let pendingBefore := g.pending
          let randomBefore := g.afterRandom
          let (g1, ov?) := execDamage g ctx op
          g := g1
          if let some ov := ov? then
            if let some (.bindClose v sIdx eid body _) := stack.back? then
              stack := stack.pop.push (.bindClose v sIdx eid body (some ov))
          let (g', paused) := pauseIfNeeded g { ctx, queue, stack } pendingBefore randomBefore
          if paused then return g'
          g := g'
        | .life op =>
          let pendingBefore := g.pending
          let randomBefore := g.afterRandom
          g := execLife g ctx op
          let (g', paused) := pauseIfNeeded g { ctx, queue, stack } pendingBefore randomBefore
          if paused then return g'
          g := g'
        | .player op =>
          let pendingBefore := g.pending
          let randomBefore := g.afterRandom
          let next? : Option Instruction := queue[0]?
          match op, next? with
          | .scry whoExpr scryAmt, some (.player (.drawCards whoExpr' drawAmt)) =>
            let env := interpEnv g ctx
            let p? := (EvalExpr.evalPlayer g env whoExpr)[0]?
            let drawN := (EvalExpr.evalValue g env drawAmt).toNat
            if whoExpr == whoExpr' && p?.isSome && drawN > 0 then
              queue := queue.extract 1 queue.size
              let scryN := (EvalExpr.evalValue g env scryAmt).toNat
              g := g.scryThenDraw p?.get! scryN drawN
            else
              let (g1, ov?) := execPlayer g ctx op
              g := g1
              if let some ov := ov? then
                if let some (.bindClose v sIdx eid body _) := stack.back? then
                  stack := stack.pop.push (.bindClose v sIdx eid body (some ov))
          | _, _ =>
            let (g1, ov?) := execPlayer g ctx op
            g := g1
            if let some ov := ov? then
              if let some (.bindClose v sIdx eid body _) := stack.back? then
                stack := stack.pop.push (.bindClose v sIdx eid body (some ov))
          let (g', paused) := pauseIfNeeded g { ctx, queue, stack } pendingBefore randomBefore
          if paused then return g'
          g := g'
        | .turn op =>
          let pendingBefore := g.pending
          let randomBefore := g.afterRandom
          g := execTurn g ctx op
          let (g', paused) := pauseIfNeeded g { ctx, queue, stack } pendingBefore randomBefore
          if paused then return g'
          g := g'
        | .stack op =>
          let pendingBefore := g.pending
          let randomBefore := g.afterRandom
          g := execStack g ctx op
          let (g', paused) := pauseIfNeeded g { ctx, queue, stack } pendingBefore randomBefore
          if paused then return g'
          g := g'
        | .installEffect op =>
          let pendingBefore := g.pending
          let randomBefore := g.afterRandom
          g := execInstallEffect g ctx op
          let (g', paused) := pauseIfNeeded g { ctx, queue, stack } pendingBefore randomBefore
          if paused then return g'
          g := g'
  return g

/-- Run a single `Instruction` under `ctx` inside a fresh continuation frame (or
reusing the active frame when already inside one). -/
def runInstruction (g : Game) (ctx : InterpCtx) (instr : Instruction) : Game :=
  match instr with
  | .create (.emblem .you _) =>
    if !g.stillInGame ctx.controller then g
    else
      g.withContinuationFrame fun g =>
        let (g, ctx) :=
          if ctx.oneShotEffectId.raw == 0 then
            match g.currentResolvingContext? with
            | some _ =>
              let id : EffectId := ⟨max 1 g.nextEffectId⟩
              (g.change (.nextEffectId (id.raw + 1)), { ctx with oneShotEffectId := id })
            | none => (g, ctx)
          else (g, ctx)
        g.resumeInterpreter { ctx, queue := #[instr], stack := #[] }
  | _ =>
    g.withContinuationFrame fun g =>
      let (g, ctx) :=
        if ctx.oneShotEffectId.raw == 0 then
          match g.currentResolvingContext? with
          | some _ =>
            let id : EffectId := ⟨max 1 g.nextEffectId⟩
            (g.change (.nextEffectId (id.raw + 1)), { ctx with oneShotEffectId := id })
          | none => (g, ctx)
        else (g, ctx)
      g.resumeInterpreter { ctx, queue := #[instr], stack := #[] }

/-- Resume any suspended interpreter continuation stored in `ContinuationFrame.interpWait?`
once `g.pending == .none`. -/
def resumeInterpWaitIfReady (g : Game) : Game :=
  if g.pending != .none then g
  else
    match g.currentInterpWait? with
    | none => g
    | some st =>
      let g := g.change (.interpWait? none)
      g.withContinuationFrame fun g => g.resumeInterpreter st

/-! ### Unified Public Effect Entrypoints (Spells, Activated, Saga chapters, Triggers) -/

/-- Execute a Phase-9 legacy `Resolution` payload when `Effect.resolution?` is `some`. -/
private def runLegacyResolution (g : Game) (controller : PlayerId) (effect : Effect)
    (r : Resolution) (targets : Array Target) (sourceId : Option ObjectId)
    (chosenX : Option Nat := none)
    (lastKnownPower : Option Int := none)
    (lastKnownToughness : Option Int := none) : Game :=
  let trCtx : TriggerRead := {
    controller, sourceId, targets, lastKnownPower, lastKnownToughness, chosenX }
  match r with
  | .queueMshReflexive kind paid =>
    g.queueModeledReflexive controller sourceId kind paid
  | .mshReflexive kind paid =>
    g.resolveModeledReflexive controller sourceId kind paid targets g.resolvingDivision
  | .hawkeyeArrows modes =>
    g.runHawkeyeArrows controller modes.toArray targets 0 sourceId
  | .createTokens tokIdx amt _ =>
    let tok := effect.legacyToken tokIdx
    let n := (g.triggerCount trCtx amt).getD 0
    g.makeTokenSpecBatched controller tok n (chosenX.getD 0)
  | .gainLife amt =>
    let n := (g.triggerCount trCtx amt).getD 0
    if n == 0 then g else g.gainLife controller n
  | .loseLife amt who =>
    let n := (g.triggerCount trCtx amt).getD 0
    if n == 0 then g
    else
      match who with
      | .you => g.loseLife controller n
      | .eachOpponent =>
        (g.livingOpponents controller).foldl (fun g opp => g.loseLife opp.id n) g
      | .target _ =>
        match targets[0]? with
        | some (Target.player pid) => if g.stillInGame pid then g.loseLife pid n else g
        | _ => g
      | _ => g.loseLife controller n
  | .draw amt who =>
    let n := (g.triggerCount trCtx amt).getD 0
    if n == 0 then g
    else
      match who with
      | .you => g.draw controller n
      | .target _ =>
        match targets[0]? with
        | some (Target.player pid) => if g.stillInGame pid then g.draw pid n else g
        | _ => g
      | _ => g.draw controller n
  | .scry amt =>
    let n := (g.triggerCount trCtx amt).getD 0
    if n == 0 then g else g.beginScry controller n
  | .surveil amt =>
    let n := (g.triggerCount trCtx amt).getD 0
    if n == 0 then g else g.beginSurveil controller n
  | .addMana mana amt =>
    g.applyAddMana controller sourceId mana amt (chosenX := chosenX)
      (lastKnownPower := lastKnownPower) (lastKnownToughness := lastKnownToughness)
  | .exile (.target .eachPermanent) .untilSourceLeaves .none
  | .exile .eachPermanent .untilSourceLeaves .none =>
    g.withSourceStillOnBattlefield sourceId fun g _ =>
      let legal := g.legalTargetsForSpec controller effect.effectiveTargetSpec sourceId
      let (g, validIds) := targets.foldl (fun (acc : Game × Array ObjectId) t =>
        let (g, xs) := acc
        match t with
        | Target.permanent oid =>
          if legal.contains t then (g, xs.push oid)
          else (g.illegalAbilityTarget t, xs)
        | _ => (g, xs)) (g, #[])
      if validIds.isEmpty then g
      else
        let (g, linkCause) := g.allocDelayedCause (some controller) sourceId
        g.withBatch (some linkCause) fun g =>
          g.exileIdsUntilSourceLeavesLoop sourceId validIds (some linkCause)
  | _ => g

/-- Resolve a unified `Effect` as a spell (CR 608). -/
def applyUnified (g : Game) (controller : PlayerId) (effect : Effect)
    (targets : Array Target) (castFromGraveyard := false)
    (kicked := false) (giftPromised := false) (chosenX : Option Nat := none)
    (sourceId : Option ObjectId := none)
    (skippedOptionalSlots : Array Nat := #[])
    (lastKnownPower : Option Int := none)
    (lastKnownToughness : Option Int := none)
    (isSpell : Bool := false) : Game :=
  let resolvedX :=
    (chosenX <|> g.resolvingSpell.bind g.chosenXOf? <|>
      g.resolvingAbility.bind g.chosenXOf? <|> sourceId.bind g.chosenXOf?).getD 0
  let spec := effect.effectiveTargetSpec
  let hasSyntheticStackCardTarget : Bool :=
    g.stack.isEmpty && spec.targetsStackSpell &&
      targets.any fun
        | .card id => (g.findObject? id).any (·.zone == .stack)
        | _ => false
  if !hasSyntheticStackCardTarget && g.sequenceAllTargetsIllegal controller effect targets sourceId then
    let g := g.logIllegalSequenceTargets targets
    if isSpell then g.logMsg "The spell doesn't resolve" else g
  else
    match effect.resolution? with
    | some r =>
      runLegacyResolution g controller effect r targets sourceId
        (some resolvedX) lastKnownPower lastKnownToughness
    | none =>
      let effectiveSkipped :=
        if skippedOptionalSlots.isEmpty then g.resolvingSkippedSlots else skippedOptionalSlots
      let (legalSlots, illegals) := g.buildLegalTargetSlots controller spec targets sourceId effectiveSkipped
      let g := illegals.foldl (fun g t => g.illegalAbilityTarget t) g
      let trigSubj? := g.resolvingAbilityObject?.bind (·.fraCauseId)
      let trigSubjs := (g.resolvingAbilityObject?.map (·.fraCauseIds)).getD #[]
      let trigCtrl? := g.resolvingAbilityObject?.bind (·.fraCauseController)
      let trigSubjCtrl? :=
        ((trigSubj?.bind g.findObject?).bind fun o =>
          if o.isOnBattlefield then g.controllerOf o else none)
        |>.orElse (fun _ => (trigSubj?.bind g.lastKnownBefore?).bind (·.controller))
        |>.orElse (fun _ => trigCtrl?)
      let trigPlayers : Array (TriggerPlayerRole × PlayerId) :=
        (match trigSubjCtrl? with | some p => #[(.controllerOfSubject, p)] | none => #[]) ++
        (match trigCtrl? with | some p => #[(.actor, p)] | none => #[])
      let ctx : InterpCtx := {
        controller
        sourceId := sourceId.orElse (fun _ => g.resolvingSpell)
        sourceSnapshot := (sourceId.orElse (fun _ => g.resolvingSpell)).bind g.lastKnownBefore?
        targets
        targetSlots := legalSlots
        targetSpec := spec
        triggerSubjectId := trigSubj?
        triggerSubjectIds := trigSubjs
        triggerSubjectSnapshot := trigSubj?.bind g.lastKnownBefore?
        triggerPlayers := trigPlayers
        chosenX := resolvedX
        castFromGraveyard
        kicked
        giftPromised
        lastKnownPower
        lastKnownToughness
        skippedOptionalSlots := effectiveSkipped
      }
      g.runInstruction ctx effect.body

/-- Execute remaining legacy `Resolution` steps for `PendingReplacement.continueUnified`. -/
def runUnifiedSteps (g : Game) (controller : PlayerId) (effect : Effect)
    (steps : Array Resolution) (targets : Array Target)
    (castFromGraveyard kicked giftPromised : Bool) (chosenX : Option Nat)
    (sourceId : Option ObjectId)
    (lastKnownPower : Option Int := none)
    (lastKnownToughness : Option Int := none) : Game :=
  let _ := (castFromGraveyard, kicked, giftPromised)
  steps.foldl (fun g r =>
    runLegacyResolution g controller effect r targets sourceId chosenX lastKnownPower lastKnownToughness) g

/-- Resolve a unified `Effect` as a spell (convenience wrapper over `applyUnified`). -/
def applyEffect (g : Game) (controller : PlayerId) (effect : Effect)
    (targets : Array Target) (castFromGraveyard := false)
    (kicked := false) (giftPromised := false) (chosenX : Option Nat := none)
    (sourceId : Option ObjectId := none)
    (skippedOptionalSlots : Array Nat := #[]) : Game :=
  g.applyUnified controller effect targets castFromGraveyard kicked giftPromised chosenX sourceId
    (skippedOptionalSlots := skippedOptionalSlots) (isSpell := true)

/-- Resolve a unified `Effect` as an activated or triggered ability (CR 608). -/
def applyUnifiedAbility (g : Game) (controller : PlayerId) (effect : Effect)
    (targets : Array Target) (sourceId : Option ObjectId := none)
    (lastKnownPower : Option Int := none) (chosenX : Option Nat := none)
    (lastKnownToughness : Option Int := none) : Game :=
  g.applyUnified controller effect targets
    (chosenX := chosenX) (sourceId := sourceId)
    (lastKnownPower := lastKnownPower) (lastKnownToughness := lastKnownToughness)

/-- Execute remaining legacy `Resolution` steps for `PendingReplacement.continueUnifiedAbility`. -/
def runUnifiedAbilitySteps (g : Game) (controller : PlayerId) (effect : Effect)
    (steps : Array Resolution) (targets : Array Target)
    (sourceId : Option ObjectId) (lastKnownPower : Option Int) (chosenX : Option Nat := none)
    (lastKnownToughness : Option Int := none) : Game :=
  steps.foldl (fun g r =>
    runLegacyResolution g controller effect r targets sourceId chosenX lastKnownPower lastKnownToughness) g

/-- Resolve a unified `Effect` as an activated ability (convenience wrapper). -/
def applyAbilityEffect (g : Game) (controller : PlayerId) (effect : Effect)
    (targets : Array Target) (sourceId : Option ObjectId := none)
    (lastKnownPower : Option Int := none) (chosenX : Option Nat := none)
    (lastKnownToughness : Option Int := none) : Game :=
  g.applyUnifiedAbility controller effect targets sourceId lastKnownPower chosenX
    (lastKnownToughness := lastKnownToughness)

end Game
end Mtg.Engine
