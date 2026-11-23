import Mtg.Engine.Game.CastExtras
import Mtg.Engine.Game.FraAbilities

/-!
# Unified `Instruction` Interpreter & `stepEnv` (CR 608 / 614.6 / 616.1)

Single resumable continuation-stack interpreter for all `Instruction`
bodies across spells, activated abilities, Saga chapters, and triggered
abilities (HOB, HOC, MSH, FRA, FRC, Supported).

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

/-- Reserved `stepEnv` slot used by interactive prompts (`Pending.mayResolve`,
`Pending.chooseLibraryPlacement`, `Pending.chooseTriggerOr`, `Pending.payOrLetCounter`,
`Pending.tapHumans`, `FraChoice.worldsPutCreatures`, optional-cost prompts) to hand
their outcome back to suspended `InterpCont` frames. -/
def interpChoiceVar : VarId := ⟨999⟩

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
        | some id => id.raw >= eid.raw
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
        | .permanent (.tapped eo _) | .permanent (.untapped eo) =>
          out := { out with movedCount := out.movedCount + 1, succeeded := true }
          if let some oid := eo.id then
            out := { out with objects := pushUniq out.objects oid }
        | .permanent (.transformed eo _) | .permanent (.turnedFaceUp eo)
        | .permanent (.phasedOut eo _) | .permanent (.phasedIn eo _) =>
          out := { out with succeeded := true }
          if let some oid := eo.id then
            out := { out with objects := pushUniq out.objects oid }
        | .permanent (.attached _ hostId) =>
          out := { out with succeeded := true, objects := pushUniq out.objects hostId }
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
        match mods.enterTypeMod? with
        | some tm =>
          -- `returnedAsArtifact` (`mode == .set && types == #[.artifact]`) and
          -- `additionalSubtype` (`mode == .add && types.isEmpty && !subtypes.isEmpty`)
          -- are already installed by `putOntoBattlefield` via `enterMods`.
          let alreadyHandled :=
            (tm.mode == .set && tm.types == #[.artifact]) ||
              (tm.mode == .add && tm.types.isEmpty && tm.supertypes.isEmpty && tm.removeTypes.isEmpty)
          if alreadyHandled then g
          else
            g.createEffect (.layered (.objects #[enteredId])
              (.types tm.mode tm.types tm.subtypes tm.supertypes tm.removeTypes) .indefinite) (cause := some cause)
        | none => g
      let g :=
        match mods.attachTo? with
        | some hostExpr =>
          match (resolveLiveObjects g env hostExpr)[0]? with
          | some host =>
            if host.isOnBattlefield then g.attachSourceTo (g.object! enteredId) host else g
          | none => g
        | none => g
      g

/-- Create the spell-exile replacement effect (e.g. Teferi's Protection, CR 608.2c / 614.6). -/
def teferiExileSpell (g : Game) : Game :=
  match g.resolvingSpell.bind g.findObject? with
  | some spell =>
    g.createEffect (.exileInstantSorceryInstead spell.id)
      |>.logMsg s!"{g.name spell} will be exiled"
  | none => g

private def applyDackOnHits (g : Game) (controller : PlayerId) (hits : Array ObjectId)
    (cause : EventCause) : Game :=
  let g :=
    if hits.any (fun id => (g.followMovedToZone? id (· == Zone.battlefield)).isSome) then
      g.withBatch (some cause) fun g =>
        hits.foldl (fun g id =>
          match g.followMovedToZone? id (· == Zone.battlefield) with
          | some o =>
            g.record (GameEvent.designation g.turnNumber (g.snapshot o) (.goaded controller false) true (cause := cause))
          | none => g) g
    else g
  let opps := g.livingOpponents controller
  if opps.isEmpty || !hits.any (fun id => (g.followMovedToZone? id (· == Zone.battlefield)).isSome) then g
  else
    g.withBatch (some cause) fun g =>
      Id.run do
        let mut g := g
        let mut i := 0
        for id in hits do
          match opps[i]?, g.followMovedToZone? id (· == Zone.battlefield) with
          | some opp, some o =>
            g := g.changeControl o opp.id (cause := some cause)
            i := i + 1
          | _, _ => pure ()
        return g

private def finishPutToBattlefield (g : Game) (env : EvalEnv) (ctx : InterpCtx)
    (fromId : ObjectId) (fromGyOrExile : Bool) (mods : MoveMods) (cause : EventCause) : Game :=
  match g.followMovedToZone? fromId (· == .battlefield) with
  | none => g
  | some entered =>
    let g := applyEnterModsToMoved g env ctx entered.id mods cause
    match g.findObject? entered.id with
    | some ent =>
      if ent.isOnBattlefield then
        let returnedAsArtifact :=
          mods.enterTypeMod?.any fun tm => tm.mode == .set && tm.types == #[.artifact]
        let verbTxt := if fromGyOrExile then "returns to" else "enters"
        let tappedTxt := if mods.tapped then " tapped" else ""
        let ownerTxt := if fromGyOrExile then " under its owner's control" else ""
        let ctrTxt :=
          if mods.enterCounters.isEmpty then ""
          else
            let parts := mods.enterCounters.toList.map fun (k, _) => s!"a {k.oracleName} counter"
            s!" and enters with {String.intercalate ", " parts}"
        let loseTxt := if mods.enterLoseAllAbilities then " and loses all abilities" else ""
        let msg :=
          if returnedAsArtifact then s!"{g.name ent} returns as an artifact"
          else s!"{g.name ent} {verbTxt} the battlefield{tappedTxt}{ownerTxt}{ctrTxt}{loseTxt}"
        let g := g.logMsg msg
        g.afterPermanentEnters ent
      else g
    | none => g

private def finishReturnTappedEndStepExile (g : Game) (ctx : InterpCtx) (dstP : PlayerId)
    (fromId : ObjectId) (cardName : String) (cause : EventCause) : Game :=
  match g.followMovedToZone? fromId (· == .battlefield) with
  | none => g
  | some entered =>
    if entered.isOnBattlefield then
      let g := g.logMsg s!"{cardName} returns to the battlefield tapped under {(g.player dstP).name}'s control"
      let src := (ctx.sourceId.bind g.findObject?).orElse (fun _ => some entered)
      let g := g.registerDelayedTrigger { controller := dstP, source := src, kind := .endStepExile entered.id, cause }
      g.afterPermanentEnters entered
    else g

private def finishExileReturnBriefly (g : Game) (ctx : InterpCtx) (dstP : PlayerId)
    (fromId : ObjectId) (cardName : String) (returnable : Bool) (cause : EventCause) : Game :=
  match g.followMovedToZone? fromId (· == .exile) with
  | none => g
  | some moved =>
    let g := g.logMsg s!"{cardName} is exiled"
    if returnable then
      let (g, _) := g.putOntoBattlefield moved.id dstP (tapped := true) (cause := some cause)
      if let .chooseReplacement .. := g.pending then
        g.chainPendingReplacement (.continueInterpreter {
          ctx, queue := #[], stack := #[.afterReturnTappedEndStepExile dstP moved.id cardName cause] })
      else
        finishReturnTappedEndStepExile g ctx dstP moved.id cardName cause
    else g

private def applyAfterTokensEnter (g : Game) (env : EvalEnv) (ctx : InterpCtx)
    (startEventIdx : Nat) (p : PlayerId) (mods : EnterMods) (cause : EventCause) : Game :=
  let createdIds := g.tokensCreatedSince startEventIdx
  let (g, anyPrompt) := createdIds.foldl (fun (acc : Game × Bool) tid =>
    let (g, anyP) := acc
    match g.findObject? tid with
    | none => (g, anyP)
    | some tok =>
      if !tok.isOnBattlefield then (g, anyP)
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
        let prompted :=
          match g.findObject? tid with
          | some cur => cur.isOnBattlefield && !g.enteringCausesNoTriggers cur
          | none => false
        (g, anyP || prompted)) (g, false)
  if anyPrompt && g.currentBatch.isNone && g.pending == .none then
    g.promptTriggerTargetsIfNeeded
  else g

private def enterModsOfMoveMods (mods : MoveMods) : Array EnterMod := Id.run do
  let mut em : Array EnterMod := #[]
  if mods.enterLoseAllAbilities then em := em.push .loseAllAbilities
  if !mods.enterKeywords.isEmpty then em := em.push (.keywords mods.enterKeywords)
  if let some tm := mods.enterTypeMod? then
    for s in tm.subtypes do
      em := em.push (.additionalSubtype s)
  if mods.attacking then em := em.push .attacking
  return em

/-- Ask each opponent in `opponents` to sacrifice a creature that dealt combat
damage to `controller` this turn, then sacrifice all chosen creatures together
(Witch-king of Angmar). -/
partial def beginSacDamagers (g : Game) (controller : PlayerId)
    (opponents : Array PlayerId)
    (chosen : Array (PlayerId × ObjectId) := #[]) : Game :=
  match opponents[0]? with
  | none =>
    if chosen.isEmpty then g
    else
      let preBf := g.battlefield
      g.withBatch none fun g =>
        g.sacrificePermanentsLoop chosen (preBattlefield := some preBf)
  | some p =>
    let rest := opponents.extract 1 opponents.size
    let ids :=
      ((g.creaturesControlledBy p).filter (fun o =>
        (g.combatDamageToPlayers o.id).contains controller)).map (·.id)
    if ids.isEmpty then
      let g :=
        g.logMsg s!"{(g.player p).name} controls no creature that dealt combat damage this turn"
      g.beginSacDamagers controller rest chosen
    else if ids.size == 1 then
      g.beginSacDamagers controller rest (chosen.push (p, ids[0]!))
    else
      g.beginFraChoice p (.sacrificeDamager ids rest controller chosen)
        s!"{(g.player p).name} chooses a creature that dealt combat damage to sacrifice"

private def moveOneObject (g : Game) (env : EvalEnv) (ctx : InterpCtx) (o : GameObject)
    (dest : DestZoneSpec) (verb : ZoneVerb) (mods : MoveMods) (cause : EventCause) :
    Game × Option InterpCont :=
  let oName := g.name o
  match dest, verb with
  | .graveyard, .destroy =>
    (if o.isOnBattlefield then g.destroyPermanent o (cause := some cause) else g, none)
  | .graveyard, .sacrifice =>
    if o.isOnBattlefield then
      let msg :=
        if some o.id == ctx.sourceId then s!"{oName} is sacrificed"
        else s!"{(g.player (g.controllerOf o |>.getD ctx.controller)).name} sacrifices {oName}"
      (g.sacrificeToGraveyard o msg (cause := some cause), none)
    else (g, none)
  | .graveyard, .discard =>
    let p := match o.zone with | .hand q => q | _ => o.owner
    (g.discardFromHand p o.id (chooser := some ctx.controller) (cause := some cause), none)
  | .graveyard, _ =>
    let (g, _) := g.move o.id (.graveyard o.owner) none (verb := some verb) (cause := some cause)
    (g, none)
  | .hand toWho, _ =>
    let dstP := resolveDestPlayer g env o toWho
    if o.zone == .stack then (g.returnStackSpell o.id, none)
    else (g.returnToHand o.id dstP (cause := some cause), none)
  | .exile, _ =>
    if mods.exileUntilSourceLeaves then
      let hasSource := (ctx.sourceId.bind g.findObject?).any (·.isOnBattlefield)
      if !hasSource then
        (g.logMsg "The source has left the battlefield. Nothing is exiled.", none)
      else
        let canExile := o.isOnBattlefield || (match o.zone with | .hand _ => true | _ => false)
        (if canExile then g.exileUntilSourceLeaves ctx.sourceId o (cause := some cause)
         else g, none)
    else
      match mods.delayedReturn? with
      | some (.immediately tapped under) =>
        let dstP := resolveDestPlayer g env o under
        if dstP == o.owner then
          (g.flickerPermanents #[o.id] (logText := s!"{oName} is exiled, then returned to the battlefield")
            (tapped := tapped) (cause := some cause), none)
        else
          let (g, _) := g.move o.id .exile none (cause := some cause)
          match g.followMovedToZone? o.id (· == .exile) with
          | some moved =>
            let (g, newId) := g.putOntoBattlefield moved.id dstP (tapped := tapped) (cause := some cause)
            let g := applyEnterModsToMoved g env ctx newId mods cause
            if let some ent := g.findObject? newId then
              (if ent.isOnBattlefield then g.afterPermanentEnters ent else g, none)
            else (g, none)
          | none => (g, none)
      | some (.atNextEndStep _ _) =>
        (g.exileUntilNextEndStep o (cause := some cause), none)
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
            (if ent.isOnBattlefield then g.afterPermanentEnters ent else g, none)
          else (g, none)
        | none => (g, none)
      | some (.returnIfThenExileAtEndStep pred _tapped under) =>
        let ok := EvalExpr.evalObjectPred g env (.live o) pred
        let dstP := resolveDestPlayer g env o under
        let (g, _) := g.move o.id .exile none (cause := some cause)
        if let .chooseReplacement .. := g.pending then
          (g.chainPendingReplacement (.continueInterpreter {
            ctx, queue := #[], stack := #[.afterExileReturnBriefly dstP o.id oName ok cause] }), none)
        else
          (finishExileReturnBriefly g ctx dstP o.id oName ok cause, none)
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
        let g :=
          if (g.followMovedToZone? o.id (· == .exile)).isSome then
            let impulseNextTurn := mods.grantPlayPerm?.any fun gp =>
              match gp.duration with | .untilEndOfNextTurnOf _ => true | _ => false
            if impulseNextTurn then
              g.logMsg s!"{(g.player ctx.controller).name} exiles {oName} and may play it until the end of their next turn"
            else
              g.logMsg s!"{oName} is exiled"
          else g
        (g, none)
  | .battlefield under, _ =>
    let dstP := resolveDestPlayer g env o under
    let extraCounters : CounterBag := mods.enterCounters.filterMap fun (k, ve) =>
      let n := (EvalExpr.evalValue g env ve).toNat
      if n > 0 then some (k, n) else none
    let returnedAsArtifact :=
      mods.enterTypeMod?.any fun tm => tm.mode == .set && tm.types == #[.artifact]
    let enterMods := enterModsOfMoveMods mods
    if mods.attacking then
      let logKind : EnteringAttackLog :=
        if extraCounters.any (fun (k, _) => k == .finality) then .grimReaper
        else .putOntoBattlefield
      let options := g.legalEnteringAttackTargets dstP
      let item := EnteringAttackItem.card o.id dstP ctx.controller mods.tapped returnedAsArtifact
        extraCounters enterMods.toList logKind options
      (g.promptEnteringAttackItems #[item] (cause := some cause), none)
    else
      let fromGyOrExile := match o.zone with | .graveyard _ | .exile => true | _ => false
      let (g, _) := g.putOntoBattlefield o.id dstP
        (tapped := mods.tapped) (returnedAsArtifact := returnedAsArtifact)
        (extraEntersWith := extraCounters)
        (onlyFoodArtifact := mods.enterAsPredefined? == some .food)
        (enterMods := enterMods) (cause := some cause)
      if let .chooseReplacement .. := g.pending then
        (g.chainPendingReplacement (.continueInterpreter {
          ctx, queue := #[], stack := #[.afterPutToBattlefield o.id fromGyOrExile mods cause] }), none)
      else
        (finishPutToBattlefield g env ctx o.id fromGyOrExile mods cause, none)
  | .library whose pos ownerChoosesTopBottom, _ =>
    let dstP := resolveDestPlayer g env o whose
    if ownerChoosesTopBottom && o.isOnBattlefield then
      let topInstr : Instruction := .moveZone (.target 0) (.library whose pos false) verb { mods with choice? := none }
      let botInstr : Instruction := .moveZone (.target 0) (.library whose .bottom false) verb { mods with choice? := none }
      let g :=
        (g.change (.pending (.chooseLibraryPlacement o.owner (some o.id)))).logMsg
          s!"{(g.player o.owner).name} chooses top or bottom of their library for {oName}"
      (g, some (.chooseBranch #[topInstr, botInstr] true))
    else if pos == .bottomRandom then
      (g.requestOrderInto #[o.id] (.library dstP)
        s!"{(g.player dstP).name} puts {oName} on the bottom of their library in a random order"
        (cause := some cause), none)
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
      (g, none)

private partial def execMoveLoopStep (g : Game) (env : EvalEnv) (ctx : InterpCtx)
    (ids : Array ObjectId) (dest : DestZoneSpec) (verb : ZoneVerb) (mods : MoveMods)
    (cause : EventCause) : Game := Id.run do
  let mut g := g
  for i in [0:ids.size] do
    let id := ids[i]!
    match g.findObject? id with
    | none => pure ()
    | some cur =>
      let (g1, _) := moveOneObject g env ctx cur dest verb mods cause
      g := g1
      if let .chooseReplacement .. := g.pending then
        let rem := ids.extract (i + 1) ids.size
        if !rem.isEmpty then
          g := g.chainPendingReplacement (.continueInterpreter {
            ctx, queue := #[], stack := #[.afterMoveLoop rem dest verb mods cause] })
        return g
  return g

private def execMoveZone (g : Game) (ctx : InterpCtx) (objs : ObjectExpr) (dest : DestZoneSpec)
    (verb : ZoneVerb) (mods : MoveMods) : Game × Array InterpCont :=
  let env := interpEnv g ctx
  let cause := interpCause g ctx
  -- Fast-path: mill top N of library via `Game.mill` (preserves CR 701.17 & replacement pauses)
  match objs, dest, verb with
  | .topOfLibrary whoExpr countExpr, .graveyard, .mill =>
    let n := (EvalExpr.evalValue g env countExpr).toNat
    let pids := EvalExpr.evalPlayer g env whoExpr
    (pids.foldl (fun g p => g.mill p n (cause := some cause)) g, #[])
  | _, _, _ =>
    -- Handle interactive `MoveMods.choice?` (sacrifice/discard/put-from-hand/keep-destroy-rest)
    match mods.choice? with
    | some ch =>
      let chooser? : Option PlayerId :=
        match ch.chooser with
        | .controller => some ctx.controller
        | .owner => some ctx.controller
        | .player pe => (EvalExpr.evalPlayer g env pe)[0]?
      match chooser? with
      | none => (g, #[])
      | some chooser =>
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
              (g.discardFromHand victim choices[0]! (chooser := some chooser), #[])
            else
              (g.beginRevealDiscard chooser victim permanentOnly, #[])
          | none => (g, #[])
        | .exile, .inZones (.handOf victimExpr) _ =>
          match (EvalExpr.evalPlayer g env victimExpr)[0]? with
          | some victim =>
            let g := g.revealHand victim
            if (g.revealedHandChoices victim false).isEmpty then
              (g.logMsg s!"{(g.player victim).name} has no nonland card", #[])
            else
              (g.beginFraChoice chooser (.exileFromRevealedHand victim ctx.sourceId)
                s!"{(g.player chooser).name} chooses a nonland card to exile", #[])
          | none => (g, #[])
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
          (g.withBatch (some cause) fun g =>
            execMoveLoopStep g env ctx (pick.map (·.id)) dest verb { mods with choice? := none } cause, #[])
      else if verb == .discard && !ch.invertSelection then
        let choosers : Array PlayerId :=
          match ch.chooser with
          | .controller | .owner => #[ctx.controller]
          | .player pe => EvalExpr.evalPlayer g env pe
        if ch.atRandom then
          if cands.isEmpty || hi == 0 then
            (g.logMsg s!"{(g.player chooser).name} has no card to discard", #[])
          else if cands.size == 1 then
            (g.discardFromHandRandomly chooser cands[0]!.id, #[])
          else
            (g.changes #[
              .pending (.resolveRandom (.chooseObject (cands.map (·.id)))),
              .afterRandom (.discardRandom chooser)], #[])
        else if hi == 0 then
          (g, #[])
        else if let some (.hasType ty) := ch.unlessMatching? then
          let g := g.changes #[.thirstDiscardsLeft lo, .thirstDiscardType ty]
          (g.beginDiscardCards choosers, #[])
        else if ch.filter?.isNone then
          (g.beginDiscardCards choosers lo, #[])
        else if cands.isEmpty then
          (g.logMsg s!"{(g.player chooser).name} has no card to discard", #[])
        else if cands.size ≤ lo then
          (g.withBatch (some cause) fun g =>
            cands.foldl (fun g o =>
              match g.findObject? o.id with
              | some cur => g.discardFromHand chooser cur.id (cause := some cause)
              | none => g) g, #[])
        else
          (g.beginDiscardCards choosers lo, #[])
      else if verb == .sacrifice && !ch.invertSelection then
        let isCreatureSac :=
          match objs with
          | .inZones .battlefield (.all ps) => ps.contains (.hasType .creature)
          | .inZones .battlefield (.hasType .creature) => true
          | _ => false
        if cands.isEmpty || hi == 0 then
          if isCreatureSac then
            (g.logMsg s!"{(g.player chooser).name} has no creature to sacrifice", #[])
          else
            (g.logMsg s!"{(g.player chooser).name} has no permanent to sacrifice", #[])
        else if ch.extremeMetric?.isNone && lo == 1 && hi == 1 && cands.all (g.isCreature ·) then
          (g.beginSacrificeCreature chooser, #[])
        else if cands.size ≤ lo then
          (g.withBatch (some cause) fun g =>
            cands.foldl (fun g o =>
              match g.findObject? o.id with
              | some cur =>
                if cur.isOnBattlefield then
                  g.sacrificeToGraveyard cur s!"{(g.player chooser).name} sacrifices {g.name cur}" (cause := some cause)
                else g
              | none => g) g, #[])
        else if ch.extremeMetric? == some (false, .stat .power) && lo == 1 && hi == 1 then
          (g.beginFraChoice chooser (.sacrificeLeastPower (cands.map (·.id)))
            s!"{(g.player chooser).name} has creatures tied for least power and chooses one to sacrifice", #[])
        else
          let pick := cands.extract 0 lo
          (g.withBatch (some cause) fun g =>
            pick.foldl (fun g o =>
              match g.findObject? o.id with
              | some cur =>
                if cur.isOnBattlefield then
                  g.sacrificeToGraveyard cur s!"{(g.player chooser).name} sacrifices {g.name cur}" (cause := some cause)
                else g
              | none => g) g, #[])
      else if ch.invertSelection && verb == .destroy then
        let ids := cands.map (·.id)
        (g.offerCardChoice chooser ids hi .keepDestroyRest
          s!"{(g.player chooser).name} chooses up to {hi} creatures to keep" (cause := some cause), #[])
      else if dest == .battlefield .controller && cands.all (fun o => o.zone == .hand chooser && g.isCreature o) then
        (g.offerCardChoice chooser (cands.map (·.id)) hi .creaturesToBattlefield
          s!"{(g.player chooser).name} may put creature cards from their hand onto the battlefield"
          (cause := some cause), #[])
      else if dest == .library .owner .bottom && verb == .put &&
          cands.all (fun o => o.zone == .hand chooser) then
        let cnt := min hi (g.player chooser).hand.size
        if cnt == 0 then (g, #[])
        else
          ((g.change (.pending (.putOnBottom chooser cnt))).logMsg
            s!"{(g.player chooser).name} puts a card from their hand on the bottom of their library", #[])
      else
        let pick := cands.extract 0 (min hi cands.size)
        let g := g.withBatch (some cause) fun g =>
          execMoveLoopStep g env ctx (pick.map (·.id)) dest verb { mods with choice? := none } cause
        let g :=
          match objs with
          | .linkedExile srcExpr =>
            let movedIds := (pick.map (·.id)).filter fun oid =>
              !(g.findObject? oid).any (·.zone == .exile)
            if movedIds.isEmpty then g
            else
              (resolveLiveObjects g env srcExpr).foldl (fun g src =>
                let g := g.changeObject src.id (.linkedExile (src.linkedExile.filter (!movedIds.contains ·)))
                g.changeObject src.id (.leaveTriggerExile (src.leaveTriggerExile.filter (!movedIds.contains ·)))) g
          | _ => g
        (g, #[])
    | none =>
      let targets :=
        let live :=
          let raw := resolveLiveObjects g env objs
          -- CR 400.7: exiling `.this` from a permanent ability only finds the battlefield permanent;
          -- returning a discarded land card to the battlefield tapped only finds it in the graveyard.
          if objs == .this && dest == .exile && verb == .exile then
            raw.filter (·.isOnBattlefield)
          else if dest == .battlefield .controller && mods.tapped &&
              (match objs with | .filter (.stepObjects _) (.hasType .land) => true | _ => false) then
            raw.filter (fun o => match o.zone with | .graveyard _ => true | _ => false)
          else raw
        if !live.isEmpty then live
        else
          -- CR 400.7c / 400.7e: Zone-change triggers moving `.triggerSubject` or `.this`
          -- track the card into the public zone (graveyard/exile) it moved to.
          match objs with
          | .triggerSubject =>
            let rawIds :=
              if !ctx.triggerSubjectIds.isEmpty then ctx.triggerSubjectIds
              else match ctx.triggerSubjectId with
                | some id => #[id]
                | none =>
                  if dest == .hand .owner then
                    match g.loggedLastDiedAttacker with | some id => #[id] | none => #[]
                  else #[]
            rawIds.filterMap fun id =>
              g.followMovedToZone? id (fun
                | .graveyard _ | .exile => true
                | _ => false)
          | .filter .triggerSubject pred =>
            let rawIds :=
              if !ctx.triggerSubjectIds.isEmpty then ctx.triggerSubjectIds
              else match ctx.triggerSubjectId with
                | some id => #[id]
                | none =>
                  match ctx.targets[0]? with
                  | some (Target.card id) | some (Target.permanent id) => #[id]
                  | _ => #[]
            (rawIds.filterMap fun id =>
              match g.findObject? id with
              | some o =>
                match o.zone with
                | .graveyard _ | .exile => some o
                | _ => g.followMovedToZone? id (fun | .graveyard _ | .exile => true | _ => false)
              | none =>
                g.followMovedToZone? id (fun | .graveyard _ | .exile => true | _ => false)).filter
              fun o => EvalExpr.evalObjectPred g env (.live o) pred
          | .inZones .anyGraveyard (.sameAs .this) =>
            match ctx.sourceId.bind (fun id =>
              match g.findObject? id with
              | some o =>
                if o.isOnBattlefield then none
                else match o.zone with
                  | .graveyard _ => some o
                  | _ => g.followMovedToZone? id (fun | .graveyard _ => true | _ => false)
              | none =>
                g.followMovedToZone? id (fun | .graveyard _ => true | _ => false)) with
            | some o => #[o]
            | none => #[]
          | .this =>
            if dest == .exile && verb == .exile then #[]
            else
              match ctx.sourceId.bind (fun id =>
                g.followMovedToZone? id (fun | .graveyard _ | .exile => true | _ => false)) with
              | some o => #[o]
              | none => #[]
          | _ => #[]
      if targets.isEmpty then
        let g :=
          match objs, dest with
          | .this, .battlefield .owner
          | .inZones .anyGraveyard (.sameAs .this), .battlefield .owner =>
            if mods.enterLoseAllAbilities then g.logMsg "Hellcat is no longer in the graveyard"
            else g.logMsg "The ability's source is no longer in the graveyard"
          | .this, _ => g.logMsg "The source is no longer in play"
          | .triggerSubject, .hand .owner =>
            g.logMsg "The attacking creature is no longer in the graveyard"
          | .topOfLibrary whoExpr _, .exile =>
            if mods.grantPlayPerm?.isSome then
              (EvalExpr.evalPlayer g env whoExpr).foldl (fun g p =>
                g.logMsg s!"{(g.player p).name} has no cards in their library to exile") g
            else g
          | _, _ => g
        (g, #[])
      else if objs == .triggerSubject && dest == .hand .owner &&
          targets.size == 1 && targets[0]!.printed.isToken then
        (g.logMsg s!"{g.name targets[0]!} ceases to exist", #[])
      else if objs == .linkedExile .this && dest == .battlefield .owner && verb == .put then
        (g.withBatch (some cause) fun g =>
          g.returnLinkedExileLoop (targets.map (·.id)) (cause := some cause), #[])
      else if verb == .destroy && dest == .graveyard && targets.size > 1 then
        let preBf := g.battlefield
        let ids := targets.filterMap fun o => if o.isOnBattlefield then some o.id else none
        (g.withBatch (some cause) fun g =>
          g.destroyPermanentsLoop ids (preBattlefield := some preBf) (cause := some cause), #[])
      else if dest == .exile && mods.exileUntilSourceLeaves && targets.size > 1 then
        (g.withBatch (some cause) fun g =>
          execMoveLoopStep g env ctx (targets.map (·.id)) .exile .exile mods cause, #[])
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
          let g :=
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
          (g, #[])
        | none => (g, #[])
      else if targets.size == 1 then
        let o := targets[0]!
        match dest with
        | .library _ _ true =>
          let (g, cont?) := moveOneObject g env ctx o dest verb mods cause
          (g, cont?.toArray)
        | _ =>
          let (g, cont?) := g.withBatchReturn (some cause) fun g =>
            match g.findObject? o.id with
            | some cur => moveOneObject g env ctx cur dest verb mods cause
            | none => (g, none)
          (g, cont?.toArray)
      else
        match dest with
        | .library whose .bottomRandom false =>
          let ids := targets.map (·.id)
          let dstP := resolveDestPlayer g env targets[0]! whose
          (g.requestOrderInto ids (.library dstP)
            s!"{(g.player dstP).name} puts those cards on the bottom of their library in a random order"
            (cause := some cause), #[])
        | _ =>
          (g.withBatch (some cause) fun g =>
            execMoveLoopStep g env ctx (targets.map (·.id)) dest verb mods cause, #[])

/-! ### Action Family 2: `create` -/

private def execCreate (g : Game) (ctx : InterpCtx) (op : CreateOp) : Game × Array InterpCont :=
  let env := interpEnv g ctx
  let cause := interpCause g ctx
  match op with
  | .tokens whoExpr countExpr spec mods =>
    let n := (EvalExpr.evalValue g env countExpr).toNat
    if n == 0 then
      match countExpr with
      | .manaSymbols (some .blue) _ => (g.logMsg "No blue mana symbols", #[])
      | _ => (g, #[])
    else
      let pids := EvalExpr.evalPlayer g env whoExpr
      let extraCounters : CounterBag := mods.counters.filterMap fun (k, ve) =>
        let c := (EvalExpr.evalValue g env ve).toNat
        if c > 0 then some (k, c) else none
      let copyEnv : StoredEvalEnv := env.toStored
      let hasPostMods : Bool :=
        !mods.grantKeywordsUntilEot.isEmpty || mods.goaded ||
          mods.attachTo?.isSome || mods.delayedAction?.isSome
      let (g, conts) := pids.foldl (fun (acc : Game × Array InterpCont) p =>
        let (g, cs) := acc
        if !g.stillInGame p then (g, cs)
        else
          let startIdx := g.events.size
          let g :=
            if mods.tapped || mods.attacking then
              g.createKindTokens p spec n (tapped := mods.tapped) (attacking := mods.attacking)
                (cause := some cause) (copyEnv := copyEnv) (x := ctx.chosenX)
                (extraCounters := extraCounters)
            else
              let g := g.makeTokenSpecBatched p spec n ctx.chosenX extraCounters (some cause) copyEnv
              if spec == .clue && n == 1 then g.logMsg s!"{(g.player p).name} investigates" else g
          if g.pending != .none then
            let cs := if hasPostMods then cs.push (.afterTokensEnter startIdx p mods cause) else cs
            (g, cs)
          else
            (applyAfterTokensEnter g env ctx startIdx p mods cause, cs)) (g, #[])
      (g, conts)
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
    let g := pids.foldl (fun g p =>
      if !g.stillInGame p then g
      else
        (g.createCommandObject p emblemCard).logMsg s!"{(g.player p).name} gets an emblem") g
    (g, #[])

/-! ### Action Family 3: `permanent` -/

private def interpKeywordCounterSpecs : Array ((Game → GameObject → Bool) × CounterKind) := #[
  (Game.hasHaste, .haste),
  (Game.hasFlying, .flying),
  ((fun g o => g.hasSimpleKeyword o .firstStrike), .firstStrike),
  (Game.hasDoubleStrike, .doubleStrike),
  (Game.hasDeathtouch, .deathtouch),
  (Game.hasIndestructible, .indestructible),
  (Game.hasLifelink, .lifelink),
  (Game.hasMenace, .menace),
  ((fun g o => g.hasSimpleKeyword o .reach), .reach),
  (Game.hasTrample, .trample),
  (Game.hasVigilance, .vigilance)
]

private def execPermanent (g : Game) (ctx : InterpCtx) (op : PermanentOp) : Game :=
  let env := interpEnv g ctx
  let cause := interpCause g ctx
  match op with
  | .setTapped objs tapped choice? =>
    let live :=
      let raw := (resolveLiveObjects g env objs).filter (·.isOnBattlefield)
      if !raw.isEmpty then raw
      else if !tapped && objs == .triggerSubject && ctx.triggerSubjectId.isNone then
        match g.loggedLastBecameTapped.bind g.findObject? with
        | some o => if o.isOnBattlefield then #[o] else #[]
        | none => #[]
      else #[]
    match choice? with
    | some ch =>
      let chooser : PlayerId :=
        match ch.chooser with
        | .controller | .owner => ctx.controller
        | .player pe => (EvalExpr.evalPlayer g env pe)[0]?.getD ctx.controller
      let cands :=
        match ch.filter? with
        | some fp => live.filter (fun o => EvalExpr.evalObjectPred g env (.live o) fp)
        | none => live
      if tapped && ch.count == .anyNumber && cands.all (fun o => g.hasSubtype o .human && !o.status.tapped) then
        (g.change (.pending (.tapHumans chooser))).logMsg
          s!"{(g.player chooser).name} may tap any number of untapped Humans they control"
      else
        let (_, hi) := evalInterpCountRange g env ch.count
        let pick := cands.extract 0 (min hi cands.size)
        if pick.isEmpty then g
        else
          g.withBatch (some cause) fun g =>
            pick.foldl (fun g o =>
              match g.findObject? o.id with
              | some cur =>
                if !cur.isOnBattlefield then g
                else if tapped then g.becomeTapped cur (cause := some cause)
                else g.untapPermanentLogged cur (sourceId := ctx.sourceId)
              | none => g) g
    | none =>
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
  | .modifyCounters mode objs choice? =>
    let live := (resolveLiveObjects g env objs).filter (·.isOnBattlefield)
    match choice?, mode with
    | some ch, .remove none _ =>
      let chooser : PlayerId :=
        match ch.chooser with
        | .controller | .owner => ctx.controller
        | .player pe => (EvalExpr.evalPlayer g env pe)[0]?.getD ctx.controller
      let withCounters := live.filter (·.status.hasCounters)
      match ctx.targets[0]? with
      | some (Target.permanent id) =>
        match g.findObject? id with
        | some cur =>
          if withCounters.any (·.id == cur.id) then
            let kind? : Option CounterKind :=
              if cur.status.plusOnePlusOne > 0 then some .plusOnePlusOne
              else if cur.status.indestructibleCounters > 0 then some .indestructible
              else cur.status.toCounterBag[0]?.map (·.1)
            match kind? with
            | some k =>
              let nm := g.name cur
              (g.recordRemoveCounters cur.id k 1 (byPlayer := some chooser) (cause := some cause))
                |>.logMsg s!"A counter is removed from {nm}"
            | none => g
          else
            g.logMsg "You must remove a counter from a creature you control if you can"
        | none =>
          g.logMsg "You must remove a counter from a creature you control if you can"
      | _ =>
        if withCounters.isEmpty then
          g.logMsg s!"{(g.player chooser).name} controls no creature with counters"
        else
          g.logMsg "You must remove a counter from a creature you control if you can"
    | _, _ =>
      if live.isEmpty then
        if objs == .this then g.logMsg "The triggered ability's source is no longer in play. No counter is put." else g
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
                      g.chainPendingReplacement (.continueInterpreter {
                        ctx, queue := #[], stack := #[.logIfCountersIncreased cur.id dstBefore msg] })
                    else
                      g.logIfCountersIncreased cur.id dstBefore msg
                | .copyMissingKeywords fromExpr =>
                  match (resolveLiveObjects g env fromExpr)[0]? with
                  | none => g
                  | some other =>
                    if !other.isOnBattlefield then g
                    else
                      interpKeywordCounterSpecs.foldl (fun g (has, kind) =>
                        match g.findObject? cur.id, g.findObject? other.id with
                        | some liveCur, some liveOther =>
                          if liveCur.isOnBattlefield && has g liveOther && !has g liveCur then
                            g.putCountersDeferredLog liveCur.id kind 1 (g.controllerOf liveCur) .gets (cause := some cause)
                          else g
                        | _, _ => g) g
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
    | none =>
      if toExpr == .attachedHost then
        g.logMsg "The enchanted creature has left. Equipment stays where it is."
      else if attExpr == .target 0 && toExpr == .target 1 then
        g.logMsg "The Equipment won't move"
      else g
    | some host =>
      if chooseFromPool then
        let atts := (resolveLiveObjects g env attExpr).filter (·.isOnBattlefield)
        if atts.isEmpty then g
        else if attExpr == .inZones .battlefield (.all #[.hasSubtype (.literal .equipment), .controlledBy .you]) &&
            toExpr == .target 0 then
          g.beginFraChoice ctx.controller (.attachAnyEquipment host.id (atts.map (·.id)))
            s!"{(g.player ctx.controller).name} may attach any number of Equipment to {g.name host}"
        else
          g.change (.pending (.mayAttachEquipment ctx.controller host.id ctx.sourceId))
            |>.logMsg s!"{(g.player ctx.controller).name} may attach an Equipment to {g.name host}"
      else
        let atts := (resolveLiveObjects g env attExpr).filter (·.isOnBattlefield)
        if atts.isEmpty && attExpr == .target 0 && toExpr == .target 1 then
          if ctx.targets.size ≤ 1 then g.logMsg "No Equipment was chosen"
          else g.logMsg "The Equipment won't move"
        else
          atts.foldl (fun g att =>
            match g.findObject? att.id, g.findObject? host.id with
            | some liveAtt, some liveHost =>
              if liveAtt.isOnBattlefield && liveHost.isOnBattlefield then g.attachSourceTo liveAtt liveHost else g
            | _, _ => g) g
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

private def dealDamagePermanentsStep (g : Game) (ctx : InterpCtx)
    (remainingIds : Array ObjectId) (amt : Nat) (srcName : String)
    (srcSnap? : Option EventObject) (oppOnlyCtrl? : Option PlayerId)
    (startEventIdx : Nat) (cause : EventCause) : Game := Id.run do
  let mut g := g
  let srcObj? := srcSnap?.map g.damageSourceFromSnapshot
  for i in [0:remainingIds.size] do
    let oid := remainingIds[i]!
    match g.findObject? oid with
    | none => pure ()
    | some o =>
      let ok :=
        o.isOnBattlefield &&
          match oppOnlyCtrl? with
          | none => true
          | some c =>
            (g.isCreature o || g.isPlaneswalker o) &&
              (g.controllerOf o).any (g.isLivingOpponentOf c)
      if ok then
        g := g.dealDamageFrom srcName o (Int.ofNat amt)
          (source := srcObj?) (sourceSnap := srcSnap?)
          (cause := some cause) (suppressLifelink := true)
        if let .chooseReplacement .. := g.pending then
          let rem := remainingIds.extract (i + 1) remainingIds.size
          g := g.chainPendingReplacement (.continueInterpreter {
            ctx, queue := #[],
            stack := #[.afterDamagePermanentsLoop rem amt srcName srcSnap? oppOnlyCtrl? startEventIdx cause] })
          return g
  return g.applyAggregatedLifelinkSince startEventIdx (cause := some cause)

private def dealDividedDamageStep (g : Game) (ctx : InterpCtx)
    (remaining : Array (Nat × Target × Nat)) (srcName : String)
    (srcSnap? : Option EventObject) (startEventIdx : Nat) (cause : EventCause) : Game := Id.run do
  let mut g := g
  let srcObj? := srcSnap?.map g.damageSourceFromSnapshot
  let stackSelf := g.resolvingAbility.orElse (fun _ => g.resolvingSpell)
  for i in [0:remaining.size] do
    let (slotIdx, r, n) := remaining[i]!
    let legal : Bool :=
      match ctx.targetSpec.slots[slotIdx]? with
      | some slot => (g.legalTargetsForSlot ctx.controller slot ctx.sourceId stackSelf).contains r
      | none => true
    if legal && n > 0 then
      match r with
      | .permanent oid =>
        if let some o := g.findObject? oid then
          if o.isOnBattlefield then
            g := g.dealDamageFrom srcName o (Int.ofNat n)
              (source := srcObj?) (sourceSnap := srcSnap?)
              (cause := some cause) (suppressLifelink := true)
      | .player pid =>
        if g.stillInGame pid then
          g := g.dealDamageToPlayer pid n (source := srcObj?) (sourceSnap := srcSnap?)
            (cause := some cause) (suppressLifelink := true)
      | .card _ => pure ()
      if let .chooseReplacement .. := g.pending then
        let rem := remaining.extract (i + 1) remaining.size
        g := g.chainPendingReplacement (.continueInterpreter {
          ctx, queue := #[],
          stack := #[.afterDividedDamageLoop rem srcName srcSnap? startEventIdx cause] })
        return g
  return g.applyAggregatedLifelinkSince startEventIdx (cause := some cause)

private def execDamage (g : Game) (ctx : InterpCtx) (op : DamageOp) : Game × Option StepOutcome :=
  let env := interpEnv g ctx
  let cause := interpCause g ctx
  match op with
  | .deal srcExpr recExpr amtExpr flags =>
    let rawAmt := (EvalExpr.evalValue g env amtExpr).toNat
    let amt :=
      if rawAmt == 0 &&
          (amtExpr == .objectStat .manaValue .triggerSubject ||
            amtExpr == .objectStat .power .triggerSubject) &&
          (EvalExpr.evalObjects g env .triggerSubject).isEmpty then
        (ctx.lastKnownPower.getD 0).toNat
      else rawAmt
    if amt == 0 then (g, none)
    else
      let srcView? : Option ObjectView :=
        match (EvalExpr.evalObjects g env srcExpr)[0]? with
        | some v => some v
        | none =>
          if srcExpr == .attachedHost then
            (EvalExpr.evalObjects g env .triggerSubject)[0]?
          else none
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
      let blockingSelfNeedsSource :=
        match recExpr with
        | .objects (.inZones .battlefield (.all #[.hasType .creature, .combatRole (.blockingObject .this)])) => true
        | _ => false
      if blockingSelfNeedsSource && !(ctx.sourceId.bind g.findObject?).any (·.isOnBattlefield) then
        (g.logMsg "The triggered ability's source is no longer in play", none)
      else
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
          let oppOnlyCtrl? : Option PlayerId :=
            match recExpr with
            | .objects (.inZones .battlefield (.all #[.hasType .creature, .controlledBy .opponent]))
            | .objects (.inZones .battlefield (.all #[.any #[.hasType .creature, .hasType .planeswalker], .controlledBy .opponent])) =>
              some ctx.controller
            | _ => none
          let startIdx := g.events.size
          let g := g.withBatch (some cause) fun g =>
            dealDamagePermanentsStep g ctx oids amt srcName srcSnap? oppOnlyCtrl? startIdx cause
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
                g.chainPendingReplacement (.continueInterpreter {
                  ctx, queue := #[], stack := #[.applyAggregatedLifelink startIdx batchCause] })
              else g
            (g, none)
      else if let .chooseReplacement .. := g.pending then
        (g.chainPendingReplacement (.continueInterpreter {
          ctx, queue := #[.damage op], stack := #[] }), none)
      else if flags.divided && !flags.trackExcess then
        let startIdx := g.events.size
        let div := g.resolvingDivision
        let items : Array (Nat × Target × Nat) := Id.run do
          let mut out : Array (Nat × Target × Nat) := #[]
          if !ctx.targets.isEmpty then
            for i in [0:ctx.targets.size] do
              let r := ctx.targets[i]!
              if recipients.contains r then
                let n := if i < div.size then div[i]! else amt
                let slotIdx := if ctx.targetSpec.slots.size <= 1 then 0 else min i (ctx.targetSpec.slots.size - 1)
                out := out.push (slotIdx, r, n)
          else
            for i in [0:recipients.size] do
              let r := recipients[i]!
              let n := if i < div.size then div[i]! else amt
              let slotIdx := if ctx.targetSpec.slots.size <= 1 then 0 else min i (ctx.targetSpec.slots.size - 1)
              out := out.push (slotIdx, r, n)
          return out
        let g := g.withBatch (some cause) fun g =>
          dealDividedDamageStep g ctx items srcName srcSnap? startIdx cause
        (g, none)
      else
        let startIdx := g.events.size
        let div := g.resolvingDivision
        let (g, totalExcess) := g.withBatchReturn (some cause) fun g =>
          Id.run do
            let mut g := g
            let mut ex : Nat := 0
            if flags.divided && !ctx.targets.isEmpty then
              for i in [0:ctx.targets.size] do
                let r := ctx.targets[i]!
                if recipients.contains r then
                  let n := if i < div.size then div[i]! else amt
                  let (g', e1) := dealOne g r n
                  g := g'
                  ex := ex + e1
            else
              for i in [0:recipients.size] do
                let r := recipients[i]!
                let n := if flags.divided && i < div.size then div[i]! else amt
                let (g', e1) := dealOne g r n
                g := g'
                ex := ex + e1
            return (g, ex)
        let g :=
          if let .chooseReplacement .. := g.pending then
            g.chainPendingReplacement (.continueInterpreter {
              ctx, queue := #[], stack := #[.applyAggregatedLifelink startIdx cause] })
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
    if n == 0 then
      match amtExpr with
      | .aggregate .count .one (.inZones .battlefield (.all #[.hasSubtype (.literal .equipment), .attachedTo .this])) =>
        g.logMsg s!"{g.fraSourceName ctx.sourceId} isn't equipped"
      | _ => g
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
          g.chainPendingReplacement (.continueInterpreter {
            ctx, queue := #[], stack := #[.exploreAfterLandMove explorerCtrl top destOwner cName] })
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
          g.chainPendingReplacement (.continueInterpreter {
            ctx, queue := #[], stack := #[.exploreOfferGraveyard explorerCtrl top] })
        else
          g.offerExploreMayGraveyard explorerCtrl top

/-- Put `chosen` from the revealed cards onto the battlefield, then the other
revealed cards on the bottom of their owner's library in a random order. -/
def resolveRandomCreatureReveal (g : Game) (p : PlayerId) (revealed : Array ObjectId)
    (chosen : ObjectId) (cause : Option EventCause := none) : Game :=
  let stashed :=
    cause.orElse (fun _ => g.stashedCause.orElse (fun _ => revealed[0]?.bind g.lastMoveCauseOf?))
  let g := if g.stashedCause.isSome then g.change (.stashedCause none) else g
  let (g, cause) : Game × Option EventCause :=
    match stashed with
    | some c => (g, some c)
    | none =>
      let (g, c) := g.allocDelayedCause (some p)
      (g, some c)
  let rest := revealed.filter (fun id => id != chosen && (g.findObject? id).isSome)
  let libraryOwner :=
    match rest[0]?.bind g.findObject? with
    | some o => o.owner
    | none => p
  match g.findObject? chosen with
  | some _ =>
    let (g, newId) := g.putOntoBattlefield chosen p (cause := cause)
    if let .chooseReplacement .. := g.pending then
      g.chainPendingReplacement
        (.finishPostStep (.enteredBattlefieldPutRestBottomRandom libraryOwner chosen rest cause))
    else
      let g :=
        match g.findObject? newId with
        | some entered =>
          if entered.isOnBattlefield then
            (g.logMsg s!"{g.name entered} enters the battlefield").afterPermanentEnters entered
          else g
        | none => g
      g.putRestOnBottomRandom libraryOwner rest (cause := cause)
  | none =>
    g.putRestOnBottomRandom libraryOwner rest (cause := cause)

private def distinctSearchMoveStep (g : Game) (ctx : InterpCtx) (controller : PlayerId)
    (remainingIds : Array ObjectId) (cause : EventCause) : Game := Id.run do
  if !g.stillInGame controller then return g
  let mut g := g
  for i in [0:remainingIds.size] do
    let id := remainingIds[i]!
    match g.findObject? id with
    | some o =>
      let name := g.name o
      g := g.logMsg s!"{(g.player controller).name} reveals {name}"
      let (g', _) := g.move id (.hand controller) none (cause := some cause)
      g := g'
      if let .chooseReplacement .. := g.pending then
        let rem := remainingIds.extract (i + 1) remainingIds.size
        if !rem.isEmpty then
          g := g.chainPendingReplacement (.continueInterpreter {
            ctx, queue := #[], stack := #[.afterDistinctSearchMove controller rem cause] })
        return g
      if !g.stillInGame controller then return g
    | none => pure ()
  return g

private def execInspectLibrary (g : Game) (env : EvalEnv) (ctx : InterpCtx)
    (spec : InspectLibrarySpec) (cause : EventCause) :
    Game × Option StepOutcome × Array InterpCont :=
  let chooser := (EvalExpr.evalPlayer g env spec.chooser)[0]?.getD ctx.controller
  match spec.source with
  | .topCards whoExpr countExpr reveal =>
    let p := (EvalExpr.evalPlayer g env whoExpr)[0]?.getD ctx.controller
    let n := (EvalExpr.evalValue g env countExpr).toNat
    if !g.stillInGame p || n == 0 then (g, none, #[])
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
      if looked.isEmpty then (g, some { objects := #[], succeeded := false }, #[])
      else
        match spec.action with
        | .none => (g, some { objects := looked, succeeded := true }, #[])
        | .moveAll dest mods =>
          let g := g.withBatch (some cause) fun g =>
            execMoveLoopStep g env ctx looked dest .put mods cause
          (g, none, #[])
        | .takeMatching filter cnt dest mods _ chooseRandom =>
          let (_, hi) := evalInterpCountRange g env cnt
          let eligible := looked.filter fun id =>
            (g.findObject? id).any fun o => EvalExpr.evalObjectPred g env (.live o) filter
          let anyOrder := spec.rest == .bottomAnyOrder
          if chooseRandom && dest == .battlefield .controller && spec.rest == .bottomRandom then
            if eligible.isEmpty then
              let g := g.logMsg "No creature card was revealed"
              (g.putRestOnBottomRandom p looked (cause := some cause), none, #[])
            else if eligible.size == 1 then
              (g.resolveRandomCreatureReveal p looked eligible[0]! (cause := some cause), none, #[])
            else
              let g := g.changes #[
                .stashedCause (some cause),
                .pending (.resolveRandom (.chooseObject eligible)),
                .afterRandom (.revealRandomCreatureThenBottom p looked)]
              (g, none, #[])
          else
            match dest with
            | .hand _ =>
              if hi == 1 && (spec.rest == .bottomRandom || spec.rest == .bottomAnyOrder) then
                if eligible.isEmpty then
                  if anyOrder then (g.offerBottomAnyOrder p looked (cause := some cause), none, #[])
                  else (g.putRestOnBottomRandom p looked (cause := some cause), none, #[])
                else
                  (g.beginFraChoice chooser (.mayRevealToHand looked eligible anyOrder)
                    s!"{(g.player chooser).name} may reveal a card from among them and put it into their hand",
                   none, #[])
              else
                let chosen := eligible.extract 0 (min hi eligible.size)
                let rest := looked.filter (!chosen.contains ·)
                let g := g.withBatch (some cause) fun g =>
                  execMoveLoopStep g env ctx chosen dest .put mods cause
                let g :=
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
                (g, none, #[])
            | .battlefield _ =>
              if mods.tapped && spec.rest == .shuffleIntoLibrary && hi ≥ 100 then
                (g.offerCardChoice chooser eligible hi (.landsTappedGainLife 0)
                  s!"{(g.player chooser).name} chooses land cards to put onto the battlefield tapped"
                  (cause := some cause), none, #[])
              else if spec.rest == .graveyard && (hi ≥ 100 || hi == 1) then
                let anyNum := hi ≥ 100
                if eligible.isEmpty then (g.finishRevealPutCreatures p looked #[], none, #[])
                else
                  (g.beginFraChoice chooser (.revealPutCreatures looked eligible anyNum)
                    (if anyNum then s!"{(g.player chooser).name} may put any number of matching cards onto the battlefield"
                     else s!"{(g.player chooser).name} may put a creature card from among them onto the battlefield"),
                   none, #[])
              else if spec.rest == .bottomRandom && hi == 1 && mods.mayTransformOnEnter then
                if eligible.isEmpty then (g.putRestOnBottomRandom p looked (cause := some cause), none, #[])
                else
                  (g.beginFraChoice chooser (.nickFuryPut looked eligible)
                    s!"{(g.player chooser).name} may put a card from among them onto the battlefield",
                   none, #[])
              else
                let chosen := eligible.extract 0 (min hi eligible.size)
                let rest := looked.filter (!chosen.contains ·)
                let g := g.withBatch (some cause) fun g =>
                  execMoveLoopStep g env ctx chosen dest .put mods cause
                let g :=
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
                (g, none, #[])
            | _ =>
              let chosen := eligible.extract 0 (min hi eligible.size)
              let rest := looked.filter (!chosen.contains ·)
              let g := g.withBatch (some cause) fun g =>
                execMoveLoopStep g env ctx chosen dest .put mods cause
              let g :=
                match spec.rest with
                | .bottomRandom => g.putRestOnBottomRandom p rest (cause := some cause)
                | .bottomAnyOrder => g.offerBottomAnyOrder p rest (cause := some cause)
                | .shuffleIntoLibrary => g.shuffleThen p .none
                | _ => g
              (g, none, #[])
        | .splitIntoPiles splitterExpr _ _ _ _ _ =>
          if splitterExpr == .you then
            (g.beginFraChoice p (.riddlesSplit looked)
              s!"{(g.player p).name} separates {looked.size} cards into a face-up pile and a face-down pile",
             none, #[])
          else
            let half := (looked.size + 1) / 2
            let pileA := looked.extract 0 half
            let pileB := looked.extract half looked.size
            let g :=
              if pileA.isEmpty || !g.stillInGame p then g
              else
                g.withBatch (some cause) fun g =>
                  execMoveLoopStep g env ctx pileA (.hand .controller) .put {} cause
            let conts : Array InterpCont :=
              if pileB.isEmpty then #[]
              else #[.afterMoveLoop pileB .graveyard .put {} cause]
            (g, none, conts)
        | .distributeEachOpponent _ _ =>
          (g.putHitsToBattlefield p looked (cause := some cause), none, #[])
  | .revealUntil whoExpr matchPred countExpr exileWhileRevealing =>
    let p? : Option PlayerId :=
      match (EvalExpr.evalPlayer g env whoExpr)[0]? with
      | some pid => some pid
      | none =>
        if whoExpr == .triggerPlayer .damagedPlayer then
          (match ctx.targets[0]? with | some (Target.player q) => some q | _ => none)
            |>.orElse (fun _ => g.loggedLastCombatDamagePlayer)
            |>.orElse (fun _ => if exileWhileRevealing then none else g.firstLivingOpponent? ctx.controller)
        else some ctx.controller
    match p? with
    | none =>
      let g :=
        if exileWhileRevealing then g.logMsg s!"{g.fraSourceName ctx.sourceId} didn't deal combat damage"
        else g
      (g, some { objects := #[], succeeded := false }, #[])
    | some p =>
    let limit := (EvalExpr.evalValue g env countExpr).toNat
    if !g.stillInGame p || limit == 0 then (g, some { objects := #[], succeeded := false }, #[])
    else if exileWhileRevealing then
      let (g, hits) := Id.run do
        let mut g := g
        let mut hits : Array ObjectId := #[]
        while hits.size < limit && g.stillInGame p && !(g.player p).library.isEmpty do
          let top := (g.player p).library.back!
          let (g', _) := g.move top .exile none (cause := some cause)
          g := g'
          if let .chooseReplacement .. := g.pending then
            return (g, hits)
          match g.followMovedToZone? top (· == .exile) with
          | some moved =>
            g := g.logMsg s!"{(g.player p).name} exiles {g.name moved}"
            if EvalExpr.evalObjectPred g env (.live moved) matchPred then
              hits := hits.push moved.id
          | none => pure ()
        return (g, hits)
      (g, some { objects := hits, movedCount := hits.size, succeeded := !hits.isEmpty }, #[])
    else
      let (g, effCause) :=
        match cause with
        | .oneShotEffect .. => (g, cause)
        | _ => g.allocDelayedCause (some ctx.controller) ctx.sourceId
      let (g, hits, rest) := g.revealUntilCards p
        (fun o => EvalExpr.evalObjectPred g env (.live o) matchPred) limit (cause := some effCause)
      let shuffle := spec.rest == .shuffleIntoLibrary
      match spec.action with
      | .none =>
        let postConts : Array InterpCont :=
          if rest.isEmpty && !shuffle then #[]
          else #[.afterRevealUntil p rest shuffle #[] effCause]
        (g, some { objects := hits, movedCount := hits.size, succeeded := !hits.isEmpty }, postConts)
      | .moveAll (.battlefield _) mods =>
        let g := g.putHitsToBattlefield p hits (haste := mods.enterKeywords.contains Keyword.haste)
          (tapped := mods.tapped) (cause := some effCause)
        let g :=
          if let .chooseReplacement .. := g.pending then
            g.chainPendingReplacement (.continueInterpreter {
              ctx, queue := #[], stack := #[.afterRevealUntil p rest shuffle #[] effCause] })
          else
            g.restBottomCards p rest shuffle (cause := some effCause)
        (g, none, #[])
      | .distributeEachOpponent _ _ =>
        let g := g.putHitsToBattlefield p hits (cause := some effCause)
        let g :=
          if let .chooseReplacement .. := g.pending then
            g.chainPendingReplacement (.continueInterpreter {
              ctx, queue := #[], stack := #[.afterRevealUntil p rest shuffle hits effCause] })
          else
            let g := applyDackOnHits g p hits effCause
            g.restBottomCards p rest shuffle (cause := some effCause)
        (g, none, #[])
      | .moveAll dest mods =>
        let g := g.withBatch (some effCause) fun g =>
          execMoveLoopStep g env ctx hits dest .put mods effCause
        let g :=
          if let .chooseReplacement .. := g.pending then
            g.chainPendingReplacement (.continueInterpreter {
              ctx, queue := #[], stack := #[.afterRevealUntil p rest shuffle #[] effCause] })
          else
            g.restBottomCards p rest shuffle (cause := some effCause)
        (g, none, #[])
      | _ =>
        (g.restBottomCards p rest shuffle (cause := some effCause), none, #[])
  | .millCards whoExpr countExpr =>
    let p := (EvalExpr.evalPlayer g env whoExpr)[0]?.getD ctx.controller
    let n := (EvalExpr.evalValue g env countExpr).toNat
    if !g.stillInGame p then (g, none, #[])
    else
      let g :=
        match spec.action with
        | .takeMatching filter cnt (.hand _) _ _ _ =>
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
      (g, none, #[])
  | .allButBottom whoExpr =>
    let pids := EvalExpr.evalPlayer g env whoExpr
    let g := g.withBatch (some cause) fun g =>
      g.exileOpponentLibrariesLoop pids
    (g, none, #[])
  | .outsideTheGame _ _ => (g, none, #[])

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
            distinctSearchMoveStep g ctx searcher pickedIds cause
      if let .chooseReplacement .. := g.pending then
        g.chainPendingReplacement (.shuffleThen searcher .none)
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
        (alsoHand := spec.zones.zones.contains .hand)
        (optional := sdest == .topAfterShuffle)

private def execPlayer (g : Game) (ctx : InterpCtx) (op : PlayerOp) :
    Game × Option StepOutcome × Array InterpCont :=
  let env := interpEnv g ctx
  let cause := interpCause g ctx
  match op with
  | .drawCards whoExpr amtExpr =>
    let pids := EvalExpr.evalPlayer g env whoExpr
    if pids.isEmpty && whoExpr == .controllerOf .attachedHost then
      (g.logMsg "The enchanted creature has left. No card is drawn.", none, #[])
    else
      let n :=
        match amtExpr with
        | .aggregate .sum (.stat .power) .costPaidObjects =>
          if env.costPaidObjects.isEmpty then env.eventAmount.toNat
          else (EvalExpr.evalValue g env amtExpr).toNat
        | _ => (EvalExpr.evalValue g env amtExpr).toNat
      if n == 0 then
        let g :=
          match amtExpr with
          | .binary .max (.const 0) (.binary .sub (.const k) (.playerMetric .handSize .you)) =>
            if k == 10 then g.logMsg "You already have ten or more cards in hand"
            else g.logMsg s!"You already have {k} or more cards in hand"
          | .playerMetric .one (.matching .anyPlayer (.metric .graveyardSize .ge (.const 7))) =>
            pids.foldl (fun g p => g.logMsg s!"{(g.player p).name} draws no cards") g
          | _ => g
        (g, none, #[])
      else
        (pids.foldl (fun g p => g.draw p n (cause := some cause)) g, none, #[])
  | .scry whoExpr amtExpr =>
    let n := (EvalExpr.evalValue g env amtExpr).toNat
    match (EvalExpr.evalPlayer g env whoExpr)[0]? with
    | some p => (g.beginScry p n, none, #[])
    | none => (g, none, #[])
  | .surveil whoExpr amtExpr =>
    let n := (EvalExpr.evalValue g env amtExpr).toNat
    match (EvalExpr.evalPlayer g env whoExpr)[0]? with
    | some p => (g.beginSurveil p n, none, #[])
    | none => (g, none, #[])
  | .inspectLibrary spec =>
    let preIdx := g.events.size
    let (g, ov?, conts) := execInspectLibrary g env ctx spec cause
    match ov?, spec.source, spec.action with
    | some ov, _, _ => (g, some ov, conts)
    | none, .revealUntil .., .moveAll (.battlefield _) _ =>
      let placedIds : Array ObjectId := (g.events.extract preIdx g.events.size).filterMap fun e =>
        match e.change with
        | .rules (.zone (.moved _ after _ .battlefield ..)) => after.id
        | _ => none
      let ov : StepOutcome := { objects := placedIds, movedCount := placedIds.size, succeeded := !placedIds.isEmpty }
      (g, some ov, conts)
    | none, _, _ => (g, none, conts)
  | .searchLibrary spec =>
    (execSearchLibrary g env ctx spec, none, #[])
  | .reveal whoExpr objsExpr count? =>
    match (EvalExpr.evalPlayer g env whoExpr)[0]? with
    | none => (g, none, #[])
    | some p =>
      if !g.stillInGame p then (g, none, #[])
      else
        match objsExpr, count? with
        | .inZones (.handOf _) .anyObject, some (.exact nExpr) =>
          let n := (EvalExpr.evalValue g env nExpr).toNat
          let hand := (g.player p).hand
          let shownIds := if hand.size ≤ n then hand else hand.take n
          let g :=
            if shownIds.isEmpty then g
            else g.record (GameEvent.revealed g.turnNumber p shownIds (cause := some cause))
          let g := (g.revealHand p (recordEvent := false)).logMsg
            s!"{(g.player p).name} reveals {shownIds.size} card(s) (all, if fewer than {n})"
          (g, some { objects := shownIds, succeeded := !shownIds.isEmpty }, #[])
        | .inZones (.handOf _) .anyObject, none =>
          let hand := (g.player p).hand
          let g := g.revealHand p
          (g, some { objects := hand, succeeded := !hand.isEmpty }, #[])
        | _, _ =>
          let rawIds := resolveObjectIds g env objsExpr
          let ids :=
            match count? with
            | some cr =>
              let (_, hi) := evalInterpCountRange g env cr
              rawIds.extract 0 (min hi rawIds.size)
            | none => rawIds
          if ids.isEmpty then (g, none, #[])
          else
            let g := g.record (GameEvent.revealed g.turnNumber p ids (cause := some cause))
            let g := ids.foldl (fun g id =>
              match g.findObject? id with
              | some c => g.logMsg s!"{(g.player p).name} reveals {g.name c}"
              | none => g) g
            (g, some { objects := ids, succeeded := true }, #[])
  | .shuffle whoExpr =>
    ((EvalExpr.evalPlayer g env whoExpr).foldl (fun g p => g.shuffleThen p .none) g, none, #[])
  | .addMana whoExpr mp =>
    let out := g.evalManaSpec env mp.spec
    let pids := EvalExpr.evalPlayer g env whoExpr
    match out, mp.restriction with
    | .combination _ n, some rest =>
      if n > 0 then
        match pids[0]? with
        | some p =>
          if !g.stillInGame p then (g, none, #[])
          else
            (g.beginFraChoice p (.addManaColors n rest)
              s!"{(g.player p).name} chooses the colors of {englishNumber n} mana ({rest.label})",
             none, #[])
        | none => (g, none, #[])
      else (g, none, #[])
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
      (g, none, #[])
  | .proliferate whoExpr timesExpr tgtOnly? =>
    let times := (EvalExpr.evalValue g env timesExpr).toNat
    if times == 0 then (g, none, #[])
    else
      match tgtOnly? with
      | some tgtExpr =>
        let ts : Array Target := (resolveLiveObjects g env tgtExpr).map (fun o => .permanent o.id)
        if ts.isEmpty then (g, none, #[])
        else (g.proliferateTarget ctx.controller ts (sourceId := ctx.sourceId), none, #[])
      | none =>
        match (EvalExpr.evalPlayer g env whoExpr)[0]? with
        | some p =>
          ((g.change (.pending (.chooseProliferate p times))).logMsg
            s!"{(g.player p).name} proliferates {times} time(s)", none, #[])
        | none => (g, none, #[])
  | .temptWithRing whoExpr =>
    ((EvalExpr.evalPlayer g env whoExpr).foldl (fun g p => g.temptWithTheRing p) g, none, #[])
  | .explore objsExpr =>
    let live := resolveLiveObjects g env objsExpr
    if live.isEmpty then
      -- CR 701.44c: if the exploring permanent left the battlefield, still explore using LKI!
      (execExploreOne g ctx none, none, #[])
    else
      (live.foldl (fun g o => execExploreOne g ctx (some o)) g, none, #[])
  | .amass whoExpr subtype amtExpr =>
    let n := (EvalExpr.evalValue g env amtExpr).toNat
    ((EvalExpr.evalPlayer g env whoExpr).foldl (fun g p => g.amass p subtype n (cause := some cause)) g, none, #[])
  | .connive objsExpr =>
    let live := (resolveLiveObjects g env objsExpr).filter (·.isOnBattlefield)
    (live.foldl (fun g o => g.applyConnive ((g.controllerOf o).getD ctx.controller) (some o.id)) g, none, #[])
  | .empowerPlaneswalker _ amtExpr =>
    let n := (EvalExpr.evalValue g env amtExpr).toNat
    (g.empowerJace ctx.controller n (cause := some cause), none, #[])
  | .setStatus whoExpr kind cond? =>
    let ok := cond?.all (EvalExpr.evalCondition g env)
    if !ok then (g, none, #[])
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
            g.grantDesignationIfNeeded p (·.enduringStory) (fun _ _ => true) .enduringStory "has an enduring story"
          | .winGame =>
            -- CR 104.2b / 810.8b: a player or Two-Headed Giant team can't win while
            -- an opponent controls an `opponentsCantWin` effect on `.battlefield` or `.command`.
            let teamCantWin :=
              g.playerCantWin p ||
                g.livingPlayers.any (fun pl => g.areTeammates p pl.id && g.playerCantWin pl.id)
            if g.over || !g.stillInGame p || teamCantWin then g
            else
              let mates := g.livingPlayers.filter (fun pl => pl.id != p && g.areTeammates p pl.id)
              let msg := g.formatWinMessage (#[p] ++ mates.map (·.id))
              (g.record (GameEvent.gameEnded g.turnNumber (.won p) (cause := some cause))).logMsg msg) g
      (g, none, #[])
  | .choose whoExpr kind =>
    let chooser := (EvalExpr.evalPlayer g env whoExpr)[0]?.getD ctx.controller
    match kind with
    | .creatureType =>
      let pref := g.chooseCreatureTypeFor chooser
      let types := #[pref] ++ g.battlefieldCreatureTypes.filter (· != pref)
      (g.beginFraChoice chooser (.chooseCreatureType types)
        s!"{(g.player chooser).name} chooses a creature type", none, #[])
    | .oddOrEven =>
      (g.beginFraChoice chooser (.oddOrEvenDestroy ctx.sourceId)
        s!"{(g.player chooser).name} chooses odd or even", none, #[])
    | .keyword options =>
      match ctx.sourceId.bind g.findObject? with
      | some o =>
        if o.isOnBattlefield && !options.isEmpty then
          (g.beginChooseKeyword chooser o.id options, none, #[])
        else (g, none, #[])
      | none => (g, none, #[])
    | .playerWithMostLife =>
      let living := g.players.filter (fun pl => g.stillInGame pl.id)
      match living[0]? with
      | none => (g, none, #[])
      | some p0 =>
        let best := living.foldl (fun b pl => if pl.life > b.life then pl else b) p0
        (g, some { players := #[best.id], succeeded := true }, #[])

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
  | .extraPhase .combat _ =>
    let cause := interpCause g ctx
    (g.record (GameEvent.extraPhaseAdded g.turnNumber .combat (cause := cause))).logMsg
      "Attacking creatures untap. After this phase, there is an additional combat phase"
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
  | .chooseNewTargets objsExpr _ =>
    let objs := resolveLiveObjects g env objsExpr
    if objs.isEmpty && objsExpr == .triggerSubject then
      let targetingSource (e : StackEntry) : Bool :=
        e.targets.any fun t =>
          match t, ctx.sourceId with
          | Target.permanent id, some sid => id == sid
          | _, _ => false
      let fromStack :=
        g.stack.foldl (fun acc e => if targetingSource e then some e.objectId else acc) none
      match fromStack with
      | some spellId => g.offerSpellRetarget ctx.controller spellId 0
      | none => g
    else
      objs.foldl (fun g o =>
        if o.zone == .stack then g.offerSpellRetarget ctx.controller o.id 0
        else g) g
  | .mayCastOrPlay objsExpr permSpec =>
    let ids := resolveObjectIds g env objsExpr
    let maxMv? := permSpec.maxTotalManaValue?.map (fun v => (EvalExpr.evalValue g env v).toNat)
    let eligible := ids.filter fun id =>
      (g.findObject? id).any fun o =>
        (!g.isLand o || permSpec.landsAllowed) &&
          permSpec.filter?.all (EvalExpr.evalObjectPred g env (.live o)) &&
          maxMv?.all (fun m => g.objectManaValue o ≤ m)
    if permSpec.asFlashback then
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
        let maxMv := maxMv?.getD 1000
        let maxCasts := permSpec.maxCasts?.getD copies.size
        g.beginFraChoice ctx.controller (.castCopiesFree copies maxMv maxCasts)
          s!"{(g.player ctx.controller).name} may cast copies without paying their mana costs"
    else if permSpec.castNow then
      if !permSpec.freeCast && permSpec.exileOnResolveInstead then
        if eligible.isEmpty then
          g.logMsg s!"{(g.player ctx.controller).name} has no artifact, instant, or sorcery card in their graveyard to cast"
        else
          g.beginFraChoice ctx.controller (.mayCastFromGraveyard eligible)
            s!"{(g.player ctx.controller).name} may cast an artifact, instant, or sorcery card from their graveyard"
      else if permSpec.freeCast then
        match permSpec.maxCasts? with
        | some k =>
          if k > 1 then
            if eligible.isEmpty then g else g.offerExileCasts ctx.controller eligible k
          else if eligible.isEmpty then g
          else
            g.beginFraChoice ctx.controller (.mayCastCards eligible true permSpec.exileOnResolveInstead)
              s!"{(g.player ctx.controller).name} may cast a spell without paying its mana cost"
        | none =>
          match objsExpr with
          | .inZones (.handOf .you) (.any #[.hasType .instant, .hasType .sorcery]) =>
            let maxMv := maxMv?.getD 1000
            if eligible.isEmpty then
              g.logMsg s!"{(g.player ctx.controller).name} has no instant or sorcery with mana value {maxMv} or less"
            else
              g.beginFraChoice ctx.controller (.mayCastInstantSorceryFromHand eligible)
                s!"{(g.player ctx.controller).name} may cast an instant or sorcery spell with mana value {maxMv} or less without paying its mana cost"
          | _ =>
            if eligible.isEmpty then g
            else
              g.beginFraChoice ctx.controller (.mayCastCards eligible true permSpec.exileOnResolveInstead)
                s!"{(g.player ctx.controller).name} may cast a spell without paying its mana cost"
      else
        if eligible.isEmpty then g
        else
          g.beginFraChoice ctx.controller (.mayCastCards eligible false permSpec.exileOnResolveInstead)
            s!"{(g.player ctx.controller).name} may cast a spell"
    else if !permSpec.freeCast && permSpec.anyManaColor then
      g.grantWidowCast ctx.controller eligible[0]? (cause := some cause)
    else
      if ids.isEmpty then g
      else
        let (perm, dur) := resolvePlayPerm g env permSpec
        let turnEnds :=
          match dur with
          | .untilEndOfNextTurnOf _ => 2
          | .whileInZone _ .exile | .indefinite => 0
          | _ => 1
        let g := eligible.foldl (fun g id =>
          g.createEffect (.playPermission id perm (turnEnds := turnEnds) (d := dur)) (cause := some cause)) g
        if permSpec.freeCast && !eligible.isEmpty then
          g.beginFraChoice ctx.controller (.mayCastCards eligible true permSpec.exileOnResolveInstead)
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
  | .setBasePT (some (.playerMetric .handSize .you)) none =>
    if dur == .untilEndOfTurn then
      (g.createEffect (.cardsInHandPowerUntilEot o.id) (cause := some cause)).logMsg
        s!"{g.name o}'s base power becomes equal to the number of cards in hand until end of turn"
    else
      let pw := EvalExpr.evalValue g env (.playerMetric .handSize .you)
      let tw := g.toughness o
      (g.createEffect (.layered (.objects #[o.id]) (.ptSet pw tw) dur) (cause := some cause)).logMsg
        s!"{g.name o} has base power and toughness {pw}/{tw}"
  | .setBasePT pw? tw? =>
    let pw := (pw?.map (EvalExpr.evalValue g env)).getD (g.power o)
    let tw := (tw?.map (EvalExpr.evalValue g env)).getD (g.toughness o)
    match dur with
    | .untilEndOfTurn =>
      let isDynamic :=
        match pw?, tw? with
        | some (.objectStat ..), some (.objectStat ..) => true
        | _, _ => false
      if isDynamic then
        (g.createEffect (.setBasePTUntilEot o.id (pw, tw)) (cause := some cause)).logMsg
          s!"{g.name o}'s base power and toughness become {pw}/{tw} until end of turn"
      else
        g.setBasePTUntilEotLogged o pw tw
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
    if dur == .untilEndOfTurn && abs.any (fun a =>
        a.cost == CostSpec.tapOnly &&
          a.effect.body == Instruction.dealDamage (.targetSlot 0) (.objectStat .power .this)) then
      (g.createEffect (.ironFistTapUntilEot o.id 1) (cause := some cause)).logMsg
        s!"{g.name o} gains the tap damage ability until end of turn"
    else
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
    | none =>
      if mods.any (fun | .setName "Absorbing Man" => true | _ => false) then
        match ctx.targets[0]? with
        | none => g.logMsg s!"{g.name o} doesn't become a copy"
        | some _ => g.logMsg "The target isn't an artifact, non-Aura enchantment, or land"
      else g
    | some src =>
      let base := { g.copiableValues src with isToken := o.printed.isToken }
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
    | .game (.cantBecomeUntapped .self) =>
      match dur with
      | .whileSourceOnBattlefield sid =>
        g.createEffect (.cantUntapWhileSource o.id sid) (cause := some cause)
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
    | .controlPlayer who =>
      (EvalExpr.evalPlayerFilter g env who).foldl (fun g p =>
        g.setPlayerControl ctx.controller p (onNextTurn := true)) g
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
        let live :=
          let raw := (resolveLiveObjects g env affectedExpr).filter (·.isOnBattlefield)
          if !raw.isEmpty then raw
          else if affectedExpr == .triggerSubject && ctx.triggerSubjectId.isNone then
            match ctx.sourceId.bind g.findObject? with
            | some o => if o.isOnBattlefield then #[o] else #[]
            | none => #[]
          else #[]
        if live.isEmpty then
          if affectedExpr == .this then g.logMsg "The source is no longer in play"
          else if affectedExpr == .target 0 && ctx.targets.isEmpty &&
              (match mod with | .setBasePT (some (.objectStat ..)) _ => true | _ => false) then
            g.logMsg "No target was chosen"
          else g
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
      | .exileOnLeaveStack =>
        match g.resolvingSpell with
        | some _ => g.teferiExileSpell
        | none =>
          match ctx.sourceId.bind g.findObject? with
          | some spell =>
            if spell.zone == .stack then
              (g.move spell.id .exile none (cause := some cause)).1
            else g.teferiExileSpell
          | none => g.teferiExileSpell
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
  else if st.queue.isEmpty && st.stack.isEmpty then
    if g.pending != pendingBefore || g.afterRandom != randomBefore then
      match g.pending with
      | .fraChoice _ (.visionMode ..) => (g.change (.interpWait? (some st)), true)
      | _ => (g, true)
    else (g, false)
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
  | .exists .this =>
    (ctx.sourceId.bind g.findObject?).any (·.isOnBattlefield)
  | .castPred (.castFrom .graveyard .this) =>
    ctx.castFromGraveyard || EvalExpr.evalCondition g env cond
  | .castPred (.castFrom .hand .this) =>
    if ctx.castFromGraveyard then false else EvalExpr.evalCondition g env cond
  | .castPred (.wasKicked .this) =>
    ctx.kicked || EvalExpr.evalCondition g env cond
  | .castPred (.giftPromised .this) =>
    ctx.giftPromised || EvalExpr.evalCondition g env cond
  | .not inner => !evalCondWithCtx g env ctx inner
  | .all #[.exists .this, .forAll .this _] => EvalExpr.evalCondition g env cond
  | .all cs => cs.all (evalCondWithCtx g env ctx)
  | .any cs => cs.any (evalCondWithCtx g env ctx)
  | _ => EvalExpr.evalCondition g env cond

private def shiftObjTargetSlot (delta : Nat) : ObjectExpr → ObjectExpr
  | .target s => .target (s + delta)
  | .filter e p => .filter (shiftObjTargetSlot delta e) p
  | .union xs => .union (xs.map (shiftObjTargetSlot delta))
  | .diff a b => .diff (shiftObjTargetSlot delta a) (shiftObjTargetSlot delta b)
  | other => other

private def shiftPlayerTargetSlot (delta : Nat) : PlayerExpr → PlayerExpr
  | .target s => .target (s + delta)
  | .controllerOf e => .controllerOf (shiftObjTargetSlot delta e)
  | .ownerOf e => .ownerOf (shiftObjTargetSlot delta e)
  | other => other

private def shiftRecipientTargetSlot (delta : Nat) : RecipientExpr → RecipientExpr
  | .targetSlot s => .targetSlot (s + delta)
  | .objects e => .objects (shiftObjTargetSlot delta e)
  | .players p => .players (shiftPlayerTargetSlot delta p)
  | .both e p => .both (shiftObjTargetSlot delta e) (shiftPlayerTargetSlot delta p)
  | .allTargets => .allTargets

private partial def shiftInstrTargetSlots (delta : Nat) : Instruction → Instruction
  | i =>
    if delta == 0 then i
    else
      match i with
      | .seq ss => .seq (ss.map (shiftInstrTargetSlots delta))
      | .bind v s b => .bind v (shiftInstrTargetSlots delta s) (shiftInstrTargetSlots delta b)
      | .ifCond c t e => .ifCond c (shiftInstrTargetSlots delta t) (shiftInstrTargetSlots delta e)
      | .optional w c y n m =>
        .optional (shiftPlayerTargetSlot delta w) c
          (shiftInstrTargetSlots delta y) (shiftInstrTargetSlots delta n) m
      | .unlessPays p c u =>
        .unlessPays (shiftPlayerTargetSlot delta p) c (shiftInstrTargetSlots delta u)
      | .forEach it v b => .forEach it v (shiftInstrTargetSlots delta b)
      | .moveZone o d v m => .moveZone (shiftObjTargetSlot delta o) d v m
      | .permanent (.setTapped o t c) => .permanent (.setTapped (shiftObjTargetSlot delta o) t c)
      | .permanent (.modifyCounters op o c) => .permanent (.modifyCounters op (shiftObjTargetSlot delta o) c)
      | .permanent (.attach a b m) =>
        .permanent (.attach (shiftObjTargetSlot delta a) (shiftObjTargetSlot delta b) m)
      | .permanent (.transform o) => .permanent (.transform (shiftObjTargetSlot delta o))
      | .permanent (.turnFaceUp o) => .permanent (.turnFaceUp (shiftObjTargetSlot delta o))
      | .permanent (.phaseOut o u) => .permanent (.phaseOut (shiftObjTargetSlot delta o) u)
      | .permanent (.setDesignation o t v) => .permanent (.setDesignation (shiftObjTargetSlot delta o) t v)
      | .damage (.deal s r a f) =>
        .damage (.deal (shiftObjTargetSlot delta s) (shiftRecipientTargetSlot delta r) a f)
      | .damage (.fight a b o) =>
        .damage (.fight (shiftObjTargetSlot delta a) (shiftObjTargetSlot delta b) o)
      | .life (.gain w a) => .life (.gain (shiftPlayerTargetSlot delta w) a)
      | .life (.lose w a) => .life (.lose (shiftPlayerTargetSlot delta w) a)
      | .life (.set w a) => .life (.set (shiftPlayerTargetSlot delta w) a)
      | .player (.drawCards w a) => .player (.drawCards (shiftPlayerTargetSlot delta w) a)
      | .player (.connive o) => .player (.connive (shiftObjTargetSlot delta o))
      | .player (.explore o) => .player (.explore (shiftObjTargetSlot delta o))
      | .stack (.counterStack o e f) => .stack (.counterStack (shiftObjTargetSlot delta o) e f)
      | .stack (.copyStackObject o c m) => .stack (.copyStackObject (shiftObjTargetSlot delta o) c m)
      | .stack (.chooseNewTargets o m) => .stack (.chooseNewTargets (shiftObjTargetSlot delta o) m)
      | .installEffect (.applyContinuous d aff m) =>
        .installEffect (.applyContinuous d (shiftObjTargetSlot delta aff) m)
      | other => other

private partial def hasNthResolutionCheck : Instruction → Bool
  | .ifCond cond t e => condHasNth cond || hasNthResolutionCheck t || hasNthResolutionCheck e
  | .seq ss => ss.any hasNthResolutionCheck
  | .bind _ s b => hasNthResolutionCheck s || hasNthResolutionCheck b
  | _ => false
where
  condHasNth : Condition → Bool
    | .turnHistory (.nthResolutionThisTurn _) => true
    | .all cs | .any cs => cs.any condHasNth
    | .not c => condHasNth c
    | _ => false

/-- Freeze dynamic `.objectStat .manaValue .triggerSubject` bounds inside a
reflexive trigger's `TargetSpec` against the resolving outer ability's `env`
(CR 603.12 / 608.2h) so target legality queries on the queued reflexive ability
do not depend on outer trigger context. -/
private partial def freezeReflexivePred (g : Game) (env : EvalEnv) : ObjectPred → ObjectPred
  | .stat st op (.objectStat .manaValue .triggerSubject) =>
    let mv : Int :=
      match env.triggerSubjectId with
      | some cid =>
        match g.findObject? cid with
        | some spell => Int.ofNat (g.objectManaValue spell (includeLkiX := true))
        | none =>
          match g.lastKnownBefore? cid with
          | some eo => Int.ofNat eo.manaValue
          | none => 0
      | none => 0
    .stat st op (.const mv)
  | .all ps => .all (ps.map (freezeReflexivePred g env))
  | .any ps => .any (ps.map (freezeReflexivePred g env))
  | .not p => .not (freezeReflexivePred g env p)
  | other => other

private def freezeReflexiveTargetEffect (g : Game) (env : EvalEnv) (eff : Effect) : Effect :=
  let freezeSlot (sl : TargetSlot) : TargetSlot :=
    match sl.domain with
    | .object z p => { sl with domain := .object z (freezeReflexivePred g env p) }
    | .anyOf ds =>
      { sl with domain := .anyOf (ds.map fun
          | .object z p => .object z (freezeReflexivePred g env p)
          | d => d) }
    | _ => sl
  let spec := eff.targets
  { eff with targets := { spec with slots := spec.slots.map freezeSlot } }

/-- Resume the unified `Instruction` continuation-stack machine from `st`. -/
partial def resumeInterpreter (g : Game) (st : InterpState) : Game := Id.run do
  let mut g := g
  let initialPending := g.pending
  let mut ctx := st.ctx
  let mut queue := st.queue
  let mut stack := st.stack
  let mut fuel : Nat := 2000
  while fuel > 0 do
    fuel := fuel - 1
    -- If a replacement or interactive pause was newly opened, suspend immediately.
    if g.pending != initialPending then
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
            | .player (.drawCards _ (.stepMetric .movedCount _)) => true
            | .ifCond _ (.moveZone (.stepObjects _) ..) _ => true
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
        | .repeatRest remaining body =>
          if remaining > 0 then
            if remaining > 1 then
              stack := stack.push (.repeatRest (remaining - 1) body)
            queue := #[body]
        | .branchOnChoice onYes onNo =>
          let ok := (g.currentStepEnv.find? (·.1 == interpChoiceVar)).any (·.2.succeeded)
          g := g.change (.bindStepOutcome interpChoiceVar {})
          queue := #[if ok then onYes else onNo]
        | .bindChosenAndRun v body =>
          let chosen := (g.currentStepEnv.find? (·.1 == interpChoiceVar)).map Prod.snd |>.getD {}
          g := g.change (.bindStepOutcome interpChoiceVar {})
          g := g.change (.bindStepOutcome v chosen)
          queue := #[body]
        | .chooseBranch branches _ =>
          let idx := (g.currentStepEnv.find? (·.1 == interpChoiceVar)).map (·.2.movedCount) |>.getD 0
          g := g.change (.bindStepOutcome interpChoiceVar {})
          if let some br := branches[idx]? then
            queue := #[br]
        | .unlessPays _ ifUnpaid =>
          let paid := (g.currentStepEnv.find? (·.1 == interpChoiceVar)).any (·.2.succeeded)
          g := g.change (.bindStepOutcome interpChoiceVar {})
          if !paid then
            queue := #[ifUnpaid]
        | .afterOptionalCost who cost onYes onNo startEventIdx maxExtra =>
          let paid := (g.currentStepEnv.find? (·.1 == interpChoiceVar)).any (·.2.succeeded)
          g := g.change (.bindStepOutcome interpChoiceVar {})
          if paid then
            if let some bv := cost.bindVar? then
              let outcome := g.summarizeStepOutcome startEventIdx ⟨0⟩ none
              g := g.change (.bindStepOutcome bv outcome)
            if maxExtra > 0 then
              stack := stack.push (.repeatOptional who (some cost) onYes maxExtra)
            queue := #[onYes]
          else if onNo != .noop then
            queue := #[onNo]
        | .repeatOptional who cost? onYes remaining =>
          if remaining > 0 then
            queue := #[.optional who cost? onYes .noop remaining]
        | .afterPutToBattlefield fromId fromGyOrExile mods cause =>
          let env := interpEnv g ctx
          g := finishPutToBattlefield g env ctx fromId fromGyOrExile mods cause
        | .afterExileReturnBriefly dstP fromId cardName returnable cause =>
          g := finishExileReturnBriefly g ctx dstP fromId cardName returnable cause
        | .afterReturnTappedEndStepExile dstP fromId cardName cause =>
          g := finishReturnTappedEndStepExile g ctx dstP fromId cardName cause
        | .logIfCountersIncreased targetId before msg =>
          if let some o := g.findObject? targetId then
            if o.status.counters.any (fun (k, c) => c > before.count k) then
              g := g.logMsg msg
        | .applyAggregatedLifelink startEventIdx cause =>
          g := g.applyAggregatedLifelinkSince startEventIdx (cause := some cause)
        | .exploreAfterLandMove controller cardId destOwner cardName =>
          if (g.followMovedToZone? cardId (· == .hand destOwner)).isSome then
            let destDesc :=
              if destOwner == controller then "their hand"
              else s!"{(g.player destOwner).name}'s hand"
            g := g.logMsg s!"{(g.player controller).name} explores and puts {cardName} into {destDesc}"
        | .exploreOfferGraveyard controller cardId =>
          g := g.offerExploreMayGraveyard controller cardId
        | .afterRevealUntil p rest shuffle dackTargets cause =>
          if !dackTargets.isEmpty then
            g := applyDackOnHits g p dackTargets cause
          g := g.restBottomCards p rest shuffle (cause := some cause)
        | .afterDistinctSearchMove p remainingIds cause =>
          g := distinctSearchMoveStep g ctx p remainingIds cause
        | .afterMillOfferPermanentOrGainLife p preIds life =>
          if g.stillInGame p then
            let choices := preIds.filterMap fun id =>
              match g.followMilledPublic? id with
              | some o => if g.isPermanentCard o then some o.id else none
              | none => none
            if choices.isEmpty then
              g := g.gainLife p life
            else
              g := g.beginFraChoice p (.mayPutMilledPermanent choices life)
                s!"{(g.player p).name} may put a permanent card milled this way into their hand"
        | .afterDrawBeginDiscardThenStun p count =>
          let cnt := Nat.min count (g.player p).hand.size
          if cnt > 0 then
            g := g.beginFraChoice p (.discardThenStun cnt ctx.sourceId)
              s!"{(g.player p).name} discards {cnt} card(s)"
        | .afterDrawAddPlusOnesForDiscards p targetId? =>
          let n := g.loggedDiscards p
          match targetId?.bind g.findObject? with
          | some o => if o.isOnBattlefield && n > 0 then g := g.addPlusOnePlusOneTo o n
          | none => pure ()
        | .afterTokensEnter startEventIdx p mods cause =>
          let env := interpEnv g ctx
          g := applyAfterTokensEnter g env ctx startEventIdx p mods cause
        | .worldsCollectPlayers exiledVar rest chosen =>
          let picked := (g.currentStepEnv.find? (·.1 == interpChoiceVar)).map (·.2.objects) |>.getD #[]
          g := g.change (.bindStepOutcome interpChoiceVar {})
          let allChosen := chosen ++ picked
          let mut rem := rest
          let mut prompted := false
          while !rem.isEmpty && !prompted do
            let pid := rem[0]!
            rem := rem.extract 1 rem.size
            if g.stillInGame pid then
              let eligible := (g.player pid).hand.filter fun id => (g.findObject? id).any g.isCreature
              if !eligible.isEmpty then
                stack := stack.push (.worldsCollectPlayers exiledVar rem allChosen)
                g := g.beginFraChoice pid (.worldsPutCreatures eligible)
                  s!"{(g.player pid).name} may put any number of creature cards from their hand onto the battlefield"
                prompted := true
          if !prompted then
            let validChosen : Array (ObjectId × PlayerId × String) := allChosen.filterMap fun id =>
              match g.findObject? id with
              | some o =>
                if o.zone == .hand o.owner && g.isCreature o then some (id, o.owner, g.name o) else none
              | none => none
            let validIds := validChosen.map (·.1)
            let cause := interpCause g ctx
            g := g.withBatch (some cause) fun g =>
              g.putToBattlefieldLoop g.activePlayer validIds (useCardOwner := true)
            stack := stack.push (.worldsAfterPut exiledVar validChosen)
        | .worldsAfterPut exiledVar validChosen =>
          for (cid, owner, name) in validChosen do
            if (g.followMovedToZone? cid (· == .battlefield)).isSome then
              g := g.logMsg s!"{(g.player owner).name} puts {name} onto the battlefield"
          let exiled := (g.currentStepEnv.find? (·.1 == exiledVar)).map (·.2.objects) |>.getD #[]
          let stillExiled := exiled.filter fun id => (g.findObject? id).any (·.zone == .exile)
          g := g.change (.bindStepOutcome exiledVar {
            objects := stillExiled, movedCount := stillExiled.size, succeeded := !stillExiled.isEmpty })
        | .afterMoveLoop remainingIds dest verb mods cause =>
          let env := interpEnv g ctx
          if g.currentBatch.isSome then
            g := execMoveLoopStep g env ctx remainingIds dest verb mods cause
          else
            g := g.withBatch (some cause) fun g =>
              execMoveLoopStep g env ctx remainingIds dest verb mods cause
        | .afterDamagePermanentsLoop remainingIds amt srcName srcSnap? oppOnlyCtrl? startEventIdx cause =>
          g := dealDamagePermanentsStep g ctx remainingIds amt srcName srcSnap? oppOnlyCtrl? startEventIdx cause
        | .afterDividedDamageLoop remaining srcName srcSnap? startEventIdx cause =>
          g := dealDividedDamageStep g ctx remaining srcName srcSnap? startEventIdx cause
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
                action := .takeMatching (.isKind .permanentCard) (.upTo (.const 1)) (.hand .controller) _ _ _
                rest := .leaveInPlace, .. }),
             .life (.gain .you lifeExpr)] =>
            let n := (EvalExpr.evalValue g env nExpr).toNat
            let life := (EvalExpr.evalValue g env lifeExpr).toNat
            let lib := (g.player ctx.controller).library
            let take := Nat.min n lib.size
            let preIds := lib.extract (lib.size - take) lib.size
            g := g.mill ctx.controller n
            if let .chooseReplacement .. := g.pending then
              g := g.chainPendingReplacement (.continueInterpreter {
                ctx, queue := #[], stack := #[.afterMillOfferPermanentOrGainLife ctx.controller preIds life] })
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
                action := .takeMatching (.hasType .land) .anyNumber (.battlefield .controller) { tapped := true, .. } _ _
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
              g := g.chainPendingReplacement (.continueInterpreter {
                ctx, queue := #[], stack := #[.afterDrawBeginDiscardThenStun ctx.controller 2] })
            else
              let cnt := Nat.min 2 (g.player ctx.controller).hand.size
              if cnt > 0 then
                g := g.beginFraChoice ctx.controller (.discardThenStun cnt ctx.sourceId)
                  s!"{(g.player ctx.controller).name} discards {cnt} card(s)"
            let (g', paused) := pauseIfNeeded g { ctx, queue, stack } pendingBefore randomBefore
            if paused then return g'
            g := g'
          | [.player (.reveal victimExpr (.inZones (.handOf _) .anyObject) none),
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
          | [.player (.reveal (.target 0) (.inZones (.handOf (.target 0)) .anyObject) none),
             .ifCond (.exists .this) (.moveZone (.target 1) .exile .exile { exileUntilSourceLeaves := true, .. }) .noop] =>
            match (EvalExpr.evalPlayer g env (.target 0))[0]? with
            | some victim =>
              g := g.revealHand victim
              if (ctx.sourceId.bind g.findObject?).any (·.isOnBattlefield) then
                match ctx.targets[1]? with
                | some (Target.permanent id) =>
                  match g.findObject? id with
                  | some o =>
                    if o.isOnBattlefield && g.isCreature o && g.controlledBy o victim &&
                        g.canBeTargetedBy ctx.controller o ctx.sourceId then
                      g := g.exileUntilSourceLeaves ctx.sourceId o (cause := some (interpCause g ctx))
                    else
                      g := g.logMsg "The creature is an illegal target. The ability may still resolve."
                  | none =>
                    g := g.logMsg "The creature is an illegal target. The ability may still resolve."
                | some (Target.card id) =>
                  if let some o := g.findObject? id then
                    if o.zone == .hand victim && !g.isLand o then
                      g := g.exileUntilSourceLeaves ctx.sourceId o (cause := some (interpCause g ctx))
                | _ => pure ()
              else
                g := g.logMsg "Cloak and Dagger have left the battlefield. Nothing is exiled."
            | none => pure ()
            let (g', paused) := pauseIfNeeded g { ctx, queue, stack } pendingBefore randomBefore
            if paused then return g'
            g := g'
          | [planStep@(.permanent (.modifyCounters (.put .plan (.const 1)) .this none)),
             loseStep@(.life (.lose ..)),
             gainStep@(.life (.gain ..))] =>
            g := execPermanent g ctx (.modifyCounters (.put .plan (.const 1)) .this none)
            if g.currentResolvingContext?.isSome then
              let id : EffectId := ⟨max 1 g.nextEffectId⟩
              g := g.change (.nextEffectId (id.raw + 1))
              ctx := { ctx with oneShotEffectId := id }
            if !queue.isEmpty then stack := stack.push (.seqRest queue)
            queue := #[loseStep, gainStep]
            let _ := planStep
          | [.moveZone (.inZones (.handOf .you) .anyObject) .graveyard .discard _,
             .player (.drawCards .you (.const 1)),
             .permanent (.modifyCounters (.put .plusOnePlusOne (.playerMetric .cardsDiscardedThisTurn .you)) .triggerSubject _)] =>
            let afterDiscard : Instruction := .seq #[
              Instruction.drawFixed 1,
              .permanent (.modifyCounters (.put .plusOnePlusOne (.playerMetric .cardsDiscardedThisTurn .you)) .triggerSubject)
            ]
            if (g.player ctx.controller).hand.isEmpty then
              g := g.draw ctx.controller 1
              if let .chooseReplacement .. := g.pending then
                g := g.chainPendingReplacement (.continueInterpreter {
                  ctx, queue := #[], stack := #[.afterDrawAddPlusOnesForDiscards ctx.controller ctx.triggerSubjectId] })
              else
                let n := g.loggedDiscards ctx.controller
                match ctx.triggerSubjectId.bind g.findObject? with
                | some o => if o.isOnBattlefield && n > 0 then g := g.addPlusOnePlusOneTo o n
                | none => pure ()
            else
              g := g.beginFraChoice ctx.controller
                (.discardThen afterDiscard ctx.sourceId ctx.triggerSubjectId)
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
          | [.permanent (.modifyCounters (.put .influence (.const 1)) .this _),
             .player (.scry .you (.const 2)),
             step3@(.optional (.target 0) none (.player (.drawCards .you (.const 1))) _ _)] =>
            -- Palantír of Orthanc: illegal opponent target skips influence, scry, draw, and mill.
            let opp? := (EvalExpr.evalPlayer g env (.target 0))[0]?
            match ctx.sourceId with
            | some sid =>
              let before := ((g.findObject? sid).map (·.status.influence)).getD 0
              let (g1, ok) := g.putPalantirInfluence sid opp?
              g := g1
              match ok with
              | none => pure ()
              | some none =>
                g := g.chainPendingReplacement (.finishPostStep (.logInfluenceThenScryTwo sid before))
                if !queue.isEmpty then stack := stack.push (.seqRest queue)
                queue := #[step3]
              | some (some _) =>
                if let some src := g.findObject? sid then
                  g := g.beginScry (g.you src) 2
                if !queue.isEmpty then stack := stack.push (.seqRest queue)
                queue := #[step3]
            | none => pure ()
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
          let cause := interpCause g ctx
          if (match g.pending, step with
              | .chooseReplacement .., .player (.inspectLibrary { source := .revealUntil _ _ _ true, .. }) => true
              | _, _ => false) then
            if !queue.isEmpty then stack := stack.push (.seqRest queue)
            g := g.chainPendingReplacement (.continueInterpreter { ctx, queue := #[.bind v step body], stack })
            return g
          let handledSpecial : Bool × Game × Option Instruction :=
            match step, body with
            | .stack (.mayCastOrPlay objsExpr perm),
              .ifCond (.not (.stepSucceeded v'))
                (.damage (.deal .this (.players (.matching .opponent .any)) amtExpr _))
                .noop =>
              if v == v' && !perm.landsAllowed && !perm.freeCast && !perm.copyAndCast && !perm.asFlashback then
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
                (true, g1, none)
              else (false, g, none)
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
                (true, g1, none)
              else (false, g, none)
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
                (true, g1, none)
              else (false, g, none)
            | .forEach (.eachPlayer .any) _ (.moveZone _ .graveyard .sacrifice _),
              .ifCond (.exists (.filter (.stepObjects v') (.controlledBy .you)))
                (.create (.tokens .you (.const 1) .beast44trample _)) .noop =>
              if v == v' then
                (true, g.continueSacrificeEach ctx.controller g.apnapOrder #[], none)
              else (false, g, none)
            | .player (.searchLibrary sp),
              .optional .you (some cost) (.permanent (.setTapped (.stepObjects v') false _)) .noop _ =>
              if v == v' && sp.filter == (.all #[.hasSupertype .basic, .hasType .land]) && sp.mods.tapped then
                match (cost.items[0]? : Option CostItem) with
                | some (.behold sub) =>
                  (true, g.beginLibrarySearch ctx.controller isBasicLandCard "a basic land card"
                    (.battlefieldTappedBeholdUntap sub), none)
                | _ => (false, g, none)
              else (false, g, none)
            | .player (.inspectLibrary {
                source := .revealUntil .you (.all #[.not (.hasType .land), .stat .manaValue .lt (.objectStat .manaValue .this)]) (.const 1) true
                action := .none, rest := .leaveInPlace, .. }),
              .seq #[.stack (.mayCastOrPlay _ { freeCast := true, castNow := true, .. }),
                     .moveZone (.stepObjects v') (.library .owner .bottomRandom) .put _] =>
              if v == v' then
                let maxMv :=
                  let mv := (EvalExpr.evalValue g env (.objectStat .manaValue .this)).toNat
                  if mv > 0 then mv else (ctx.lastKnownPower.getD 0).toNat
                (true, g.resolveCascade ctx.controller maxMv, none)
              else (false, g, none)
            | .player (.inspectLibrary {
                source := .revealUntil (.triggerPlayer .damagedPlayer) (.any #[.hasType .instant, .hasType .sorcery]) (.const 1) true
                action := .none, rest := .leaveInPlace, .. }),
              .seq #[.stack (.mayCastOrPlay _ { freeCast := true, castNow := true, .. }),
                     .moveZone (.stepObjects v') (.library .owner .bottomRandom) .put _] =>
              if v == v' then
                let victim? :=
                  (EvalExpr.evalPlayer g env (.triggerPlayer .damagedPlayer))[0]?
                    |>.orElse (fun _ => g.loggedLastCombatDamagePlayer)
                    |>.orElse (fun _ => g.firstLivingOpponent? ctx.controller)
                let g1 :=
                  match victim? with
                  | none => g
                  | some victim =>
                    if !g.stillInGame victim then g
                    else
                      let (g0, exCause) := g.allocDelayedCause (some ctx.controller) ctx.sourceId
                      Id.run do
                        let mut g := g0
                        let mut others : Array ObjectId := #[]
                        let mut found? : Option ObjectId := none
                        while found?.isNone && g.stillInGame victim && !(g.player victim).library.isEmpty do
                          let top := (g.player victim).library.back!
                          let name := g.name (g.object! top)
                          let (g', _) := g.move top .exile none (cause := some exCause)
                          g := g'
                          if let .chooseReplacement .. := g.pending then
                            return g
                          if let some moved := g.followMovedToZone? top (· == .exile) then
                            g := g.logMsg s!"{(g.player victim).name} exiles {name} face up"
                            if g.isInstantOrSorcery moved then found? := some moved.id
                            else others := others.push moved.id
                        match found? with
                        | none =>
                          if !g.stillInGame victim then return g
                          else
                            return g.requestOrderInto others (.library victim)
                              s!"{(g.player victim).name} randomizes the exiled cards; they become that player's library"
                              (cause := some exCause)
                        | some cid =>
                          return g.beginFraChoice ctx.controller (.mayCastGrima cid others victim)
                            s!"{(g.player ctx.controller).name} may cast {g.name (g.object! cid)} without paying its mana cost"
                (true, g1, none)
              else (false, g, none)
            | .player (.inspectLibrary {
                source := .topCards .you nExpr false, action := .none, rest := .leaveInPlace, .. }),
              .seq #[.stack (.mayCastOrPlay (.stepObjects v1) { freeCast := true, castNow := true, maxTotalManaValue? := some maxExpr, .. }),
                     .moveZone (.stepObjects v2) (.library .owner .bottomRandom) .put _] =>
              if v == v1 && v == v2 then
                let n := (EvalExpr.evalValue g env nExpr).toNat
                let maxMv := EvalExpr.evalValue g env maxExpr
                (true, g.beginMayCastFromLooked ctx.controller n maxMv, none)
              else (false, g, none)
            | .player (.surveil .you nExpr),
              .moveZone (.filter (.stepObjects v') (.stat .manaValue .le mvExpr)) (.hand .owner) .put _ =>
              if v == v' then
                let n := (EvalExpr.evalValue g env nExpr).toNat
                let mv := (EvalExpr.evalValue g env mvExpr).toNat
                let g1 := g.beginSurveil ctx.controller n
                let g1 :=
                  match g1.pending with
                  | .surveil .. => g1.change (.surveilReturnMvAtMost (some mv))
                  | _ => g1
                (true, g1, none)
              else (false, g, none)
            | .optional .you none
                (.moveZone (.inZones (.handOf .you) (.all #[
                    .hasSubtype (.literal .hero), .hasType .creature, .stat .manaValue .le mvExpr]))
                  (.battlefield .controller) .put _) .noop _,
              .ifCond (.not (.stepSucceeded v')) (.player (.drawCards .you (.const 1))) .noop =>
              if v == v' then
                let maxMv := (EvalExpr.evalValue g env mvExpr).toNat
                let eligible := (g.player ctx.controller).hand.filter fun id =>
                  (g.findObject? id).any fun o =>
                    g.hasSubtype o .hero && g.isCreature o && g.objectManaValue o ≤ maxMv
                let g1 :=
                  if eligible.isEmpty then g.draw ctx.controller 1
                  else
                    g.beginFraChoice ctx.controller (.mayPutHeroFromHandOrDraw eligible)
                      s!"{(g.player ctx.controller).name} may put a Hero creature card from their hand onto the battlefield"
                (true, g1, none)
              else (false, g, none)
            | .player (.amass .you subtype amtExpr),
              .permanent (.attach .this (.stepObjects v') false) =>
              if v == v' then
                let n := (EvalExpr.evalValue g env amtExpr).toNat
                (true, g.amass ctx.controller subtype n (attach := ctx.sourceId) (cause := some cause), none)
              else (false, g, none)
            | _, _ => (false, g, none)
          if handledSpecial.1 then
            g := handledSpecial.2.1
            let (g', paused) := pauseIfNeeded g { ctx, queue, stack } pendingBefore randomBefore
            if paused then return g'
            g := g'
          else
            let effBody := handledSpecial.2.2.getD body
            let (g', eid) : Game × EffectId :=
              let id : EffectId := ⟨max 1 g.nextEffectId⟩
              (g.change (.nextEffectId (id.raw + 1)), id)
            g := g'
            let startIdx := g.events.size
            if !queue.isEmpty then
              stack := stack.push (.seqRest queue)
            stack := stack.push (.bindClose v startIdx eid effBody none)
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
          else
            if cond == TriggeredAbility.condSourceHarnessed then
              g := g.logMsg "The Mind Stone is not harnessed"
            else if cond == .cmp .ge (.objectStat .power .this) (.const 4) then
              g := g.logMsg "Viv Vision's power is not 4 or greater"
            else if cond == .exists (.target 0) && ctx.targets.isEmpty then
              match thenBranch with
              | .seq #[.moveZone (.target 0) .graveyard .destroy _, .player (.amass ..), _] =>
                g := g.logMsg "No target was chosen. Its controller is undefined and no player amasses Goblins."
              | _ => pure ()
        | .forEach iter v body =>
          let env := interpEnv g ctx
          if !queue.isEmpty then
            stack := stack.push (.seqRest queue)
          match iter with
          | .eachPlayer pf =>
            let ps := EvalExpr.evalPlayerFilter g env pf
            let isWorldsSimultaneous : Bool :=
              match pf, body with
              | .any, .moveZone (.inZones (.handOf (.stepPlayers v2)) (.hasType .creature))
                  (.battlefield (.player (.stepPlayers v3))) .put { choice? := some { count := .anyNumber, .. }, .. } =>
                v == v2 && v == v3
              | _, _ => false
            let isSacEachCreature : Bool :=
              match pf, body with
              | .any, .moveZone (.inZones .battlefield (.all #[
                  .hasType .creature, .controlledBy (.ofExpr (.stepPlayers v2))]))
                  .graveyard .sacrifice { choice? := some _, .. }
              | .opponent, .moveZone (.inZones .battlefield (.all #[
                  .hasType .creature, .controlledBy (.ofExpr (.stepPlayers v2))]))
                  .graveyard .sacrifice { choice? := some _, .. } => v == v2
              | _, _ => false
            let isNontokenSacEach : Bool :=
              match pf, body with
              | .opponent, .moveZone (.inZones .battlefield (.all #[
                  .hasType .creature, .isToken false, .controlledBy (.ofExpr (.stepPlayers v2))]))
                  .graveyard .sacrifice { choice? := some _, .. } => v == v2
              | _, _ => false
            let isSacDamagersEach : Bool :=
              match pf, body with
              | .opponent, .moveZone (.inZones .battlefield (.all #[
                  .hasType .creature, .controlledBy (.ofExpr (.stepPlayers v2)),
                  .dealtDamageThisTurn true (some (.player .you)) true]))
                  .graveyard .sacrifice { choice? := some _, .. } => v == v2
              | _, _ => false
            let wheelDrawExpr? : Option ValueExpr :=
              match pf, body with
              | .any, .optional (.stepPlayers v1) none
                  (.seq #[.moveZone (.inZones (.handOf (.stepPlayers v2)) .anyObject) .graveyard .discard _,
                          .player (.drawCards (.stepPlayers v3) amtExpr)]) .noop _ =>
                if v == v1 && v == v2 && v == v3 then some amtExpr else none
              | _, _ => none
            if isWorldsSimultaneous then
              let order :=
                let apnap := g.apnapOrder
                if apnap.isEmpty then #[ctx.controller] else apnap
              g := g.change (.bindStepOutcome interpChoiceVar {})
              stack := stack.push (.worldsCollectPlayers ⟨0⟩ order #[])
              queue := #[]
            else if isSacEachCreature then
              let pendingBefore := g.pending
              let randomBefore := g.afterRandom
              g := g.beginSacrificeCreatures (if pf == .any then g.apnapOrder else ps)
              queue := #[]
              let (g', paused) := pauseIfNeeded g { ctx, queue, stack } pendingBefore randomBefore
              if paused then return g'
              g := g'
            else if isNontokenSacEach then
              let pendingBefore := g.pending
              let randomBefore := g.afterRandom
              g := g.continueNontokenSacrifices ps #[]
              queue := #[]
              let (g', paused) := pauseIfNeeded g { ctx, queue, stack } pendingBefore randomBefore
              if paused then return g'
              g := g'
            else if isSacDamagersEach then
              let pendingBefore := g.pending
              let randomBefore := g.afterRandom
              g := g.beginSacDamagers ctx.controller ps #[]
              queue := #[]
              let (g', paused) := pauseIfNeeded g { ctx, queue, stack } pendingBefore randomBefore
              if paused then return g'
              g := g'
            else
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
                      { env.toStored with sourceId := some oid } (controller := p)
                  if !snapshots.isEmpty then
                    g := g.withBatch (some cause) fun g =>
                      g.copyNontokenCreaturesStep p snapshots (cause := some cause)
                    if let .chooseReplacement .. := g.pending then
                      g := g.chainPendingReplacement (.continueInterpreter {
                        ctx, queue := #[], stack := #[.afterTokensEnter startEventIdx p {} cause] })
                    else
                      g := applyAfterTokensEnter g env ctx startEventIdx p {} cause
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
            if n == 0 then queue := #[]
            else
              if n > 1 then
                stack := stack.push (.repeatRest (n - 1) body)
              queue := #[body]
        | .optional whoExpr cost? onYes onNo maxTimes =>
          let env := interpEnv g ctx
          let chooser := (EvalExpr.evalPlayer g env whoExpr)[0]?.getD ctx.controller
          let pendingBefore := g.pending
          let randomBefore := g.afterRandom
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
            else if cost == CostSpec.sacrificeArtifactOrDiscardNonland then
              let hasArt := (g.permanentsOf chooser).any g.isArtifact
              let hasNonland := (g.player chooser).hand.any fun id =>
                (g.findObject? id).any (fun o => !g.isLand o)
              if hasArt || hasNonland then
                g := g.beginFraChoice chooser (.mayPayPickThen .sacrificeArtifactOrDiscardNonland onYes ctx.sourceId)
                  s!"{(g.player chooser).name} may sacrifice an artifact or discard a nonland card"
            else if cost == CostSpec.sacrificeAnotherCreatureOrArtifactSpec then
              if let some sid := ctx.sourceId then
                let hasOther := (g.permanentsOf chooser).any fun o =>
                  o.id != sid && (g.isCreature o || g.isArtifact o)
                if hasOther then
                  g := g.beginFraChoice chooser (.maySacrificeAnotherForDrawTreasure sid)
                    s!"{(g.player chooser).name} may sacrifice another creature or artifact"
            else if cost == CostSpec.tapOnly then
              if let some sid := ctx.sourceId then
                if (g.findObject? sid).any (fun o => o.isOnBattlefield && !o.status.tapped) then
                  g := g.beginFraChoice chooser (.mayTapSourceThen onYes sid)
                    s!"{(g.player chooser).name} may tap {g.fraSourceName (some sid)}"
            else if cost.items == #[.sacrifice (.count (.const 1)) (.filter (.all #[.otherThan .this, .hasType .creature]))] then
              let hasOther := (g.creaturesControlledBy chooser).any fun o => some o.id != ctx.sourceId
              if hasOther then
                match onYes with
                | .queueReflexiveTrigger ab =>
                  if ab.pattern == .youSacrificeOtherCreature then
                    if let some sid := ctx.sourceId then
                      g := (g.change (.pending (.maySacrificeAnotherBolg chooser sid))).logMsg
                        s!"{(g.player chooser).name} may sacrifice another creature"
                  else
                    g := g.beginFraChoice chooser (.mayPayPickThen .sacrificeAnotherCreature onYes ctx.sourceId)
                      s!"{(g.player chooser).name} may sacrifice another creature"
                | .permanent (.modifyCounters (.put .plusOnePlusOne (.stepMetric .sumPower _)) .this _) =>
                  if let some sid := ctx.sourceId then
                    g := g.beginFraChoice chooser (.maySacrificeAnotherCreatureForPower sid)
                      s!"{(g.player chooser).name} may sacrifice another creature"
                | _ =>
                  g := g.beginFraChoice chooser (.mayPayPickThen .sacrificeAnotherCreature onYes ctx.sourceId)
                    s!"{(g.player chooser).name} may sacrifice another creature"
            else
              match (cost.items[0]? : Option CostItem) with
              | some (item@(.discard _ _)) =>
                let need := CostPick.count (.custom item)
                if need > 1 then
                  if (g.player chooser).hand.size ≥ need then
                    g := g.beginFraChoice chooser (.mayPayPickThen (.custom item) onYes ctx.sourceId)
                      s!"{(g.player chooser).name} may discard {need} cards"
                else
                  match onYes with
                  | .player (.drawCards _ (.const n)) =>
                    g := g.beginMayDiscardDraw chooser n.toNat
                  | _ =>
                    if !(g.player chooser).hand.isEmpty then
                      g := g.beginFraChoice chooser (.mayDiscardThen onYes ctx.sourceId)
                        s!"{(g.player chooser).name} may discard a card"
              | some (.mana mc) =>
                let gen := mc.genericCount
                let pureGeneric := mc.symbols.all fun | .generic _ => true | _ => false
                match onYes with
                | .queueReflexiveTrigger ab =>
                  g := g.offerPayForReflexive chooser ctx.sourceId mc.symbols ab.effect (maxTimes := maxTimes)
                | .bind _ (.create (.tokens _ (.const 1) (.copyOf .triggerSubject _) _)) _ =>
                  if pureGeneric && gen == 2 then
                    let artId? :=
                      ctx.triggerSubjectId.orElse fun _ =>
                        match ctx.targets[0]? with
                        | some (Target.permanent id) => some id
                        | _ => none
                    if let some artId := artId? then
                      g := g.beginFraChoice chooser (.ultronMayPay artId)
                        s!"{(g.player chooser).name} may pay \{2} to create a token copy"
                  else if pureGeneric then
                    g := g.beginFraChoice chooser (.mayPayThen gen onYes ctx.sourceId)
                      s!"{(g.player chooser).name} may pay \{{gen}}"
                  else if let some sid := ctx.sourceId then
                    g := g.beginFraChoice chooser (.mayPaySymbolsThen mc.symbols onYes sid)
                      s!"{(g.player chooser).name} may pay {mc}"
                | .player (.drawCards .you (.const 1)) =>
                  if pureGeneric then
                    g := (g.change (.pending (.mayPayGeneric chooser gen))).logMsg
                      s!"{(g.player chooser).name} may pay \{{gen}} to draw a card"
                  else if let some sid := ctx.sourceId then
                    g := g.beginFraChoice chooser (.mayPaySymbolsThen mc.symbols onYes sid)
                      s!"{(g.player chooser).name} may pay {mc}"
                | _ =>
                  if pureGeneric then
                    g := g.beginFraChoice chooser (.mayPayThen gen onYes ctx.sourceId)
                      s!"{(g.player chooser).name} may pay \{{gen}}"
                  else if let some sid := ctx.sourceId then
                    g := g.beginFraChoice chooser (.mayPaySymbolsThen mc.symbols onYes sid)
                      s!"{(g.player chooser).name} may pay {mc}"
                  else
                    if !queue.isEmpty then stack := stack.push (.seqRest queue)
                    queue := #[]
                    stack := stack.push (.afterOptionalCost whoExpr cost onYes onNo g.events.size (maxTimes - 1))
                    g := (g.changes #[
                      .bindStepOutcome interpChoiceVar {},
                      .pending (.mayResolve chooser)]).logMsg
                      s!"{(g.player chooser).name} may pay {mc}"
              | some (item@(.sacrifice _ (.filter pred))) =>
                let need := CostPick.count (.custom item)
                let types : Array CardType :=
                  match pred with
                  | .hasType t => #[t]
                  | .any ps => ps.filterMap fun | .hasType t => some t | _ => none
                  | _ => #[.creature]
                let eligible := (g.permanentsOf chooser).filter fun o => EvalExpr.evalObjectPred g env (.live o) pred
                if need > 1 then
                  if eligible.size ≥ need then
                    g := g.beginFraChoice chooser (.mayPayPickThen (.custom item) onYes ctx.sourceId)
                      s!"{(g.player chooser).name} may sacrifice {need} permanents"
                else if !eligible.isEmpty then
                  match onYes with
                  | .player (.searchLibrary sp) =>
                    if pred == .hasType .planeswalker && sp.filter == .hasType .planeswalker then
                      g := g.beginFraChoice chooser .maySacrificePlaneswalker
                        s!"{(g.player chooser).name} may sacrifice a planeswalker"
                    else
                      g := g.beginFraChoice chooser (.maySacrificeThen types onYes ctx.sourceId)
                        s!"{(g.player chooser).name} may sacrifice a permanent"
                  | _ =>
                    g := g.beginFraChoice chooser (.maySacrificeThen types onYes ctx.sourceId)
                      s!"{(g.player chooser).name} may sacrifice a permanent"
              | some (.removeCounters _ (some .plusOnePlusOne) .self) =>
                match ctx.sourceId.bind g.findObject? with
                | some src =>
                  if src.isOnBattlefield && src.status.plusOnePlusOne > 0 then
                    g := g.beginFraChoice chooser (.mayMovePlusOne src.id)
                      s!"{(g.player chooser).name} may remove a +1/+1 counter from {g.name src}"
                | none => pure ()
              | some (.payLife amtExpr) =>
                let n := (EvalExpr.evalValue g env amtExpr).toNat
                match onYes with
                | .installEffect (.applyRule .untilEndOfTurn (.combat (.assignCombatDamageByToughness ..))) =>
                  if n == 2 then
                    g := g.offerPay2LifeToughness chooser
                  else if g.canPayLife chooser n then
                    match g.payLifeCost chooser n with
                    | .ok g' =>
                      g := g'
                      if !queue.isEmpty then stack := stack.push (.seqRest queue)
                      queue := #[onYes]
                    | .error _ => pure ()
                | _ =>
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
                if !queue.isEmpty then stack := stack.push (.seqRest queue)
                queue := #[]
                stack := stack.push (.afterOptionalCost whoExpr cost onYes onNo g.events.size (maxTimes - 1))
                g := (g.changes #[
                  .bindStepOutcome interpChoiceVar {},
                  .pending (.mayResolve chooser)]).logMsg
                  s!"{(g.player chooser).name} may pay {cost.toNotation}"
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
              match onYes, onNo with
              | .permanent (.modifyCounters (.put .plusOnePlusOne (.const 1)) .this _),
                .stack (.mayCastOrPlay objsExpr { anyManaColor := true, .. }) =>
                let nonland? := (resolveObjectIds g env objsExpr)[0]?
                g := g.beginFraChoice chooser (.widowMayCounter ctx.sourceId nonland?)
                  "You may put a +1/+1 counter on Black Widow"
              | .player (.drawCards .you (.const 1)),
                .bind _ (.moveZone (.topOfLibrary _ (.counterCount (some .influence) .this)) .graveyard .mill _) _ =>
                if let some sid := ctx.sourceId then
                  if !g.stillInGame ctx.controller then pure ()
                  else if !g.stillInGame chooser then
                    let n := ((g.damageSourceById? sid).map (·.status.influence)).getD 0
                    g := g.mill ctx.controller n
                  else
                    g := g.beginFraChoice chooser (.palantirMayDraw ctx.controller sid)
                      s!"{(g.player chooser).name} may have {(g.player ctx.controller).name} draw a card"
              | .bind _ (.moveZone (.inZones (.handOf .you) .anyObject) .graveyard .discard _)
                  (.seq #[.player (.drawCards .you (.stepMetric .movedCount _)), .ifCond _ (.damage ..) .noop]),
                .noop =>
                g := g.beginFraChoice chooser (.mayDiscardHandBalin ctx.sourceId)
                  s!"{(g.player chooser).name} may discard their hand"
              | .bind _ (.moveZone (.inZones (.handOf .you) .anyObject) .graveyard .discard _)
                  (.player (.drawCards .you (.const n))),
                .noop =>
                g := g.beginFraChoice chooser (.mayDiscardHandDrawFixed n.toNat)
                  s!"{(g.player chooser).name} may discard their hand and draw {n.toNat} cards"
              | .seq #[.player (.drawCards .you amtExpr), .player (.drawCards .opponents (.const 1))],
                .noop =>
                let n := (EvalExpr.evalValue g env amtExpr).toNat
                if n == 0 then
                  g := g.logMsg s!"{(g.player chooser).name} controls no artifacts"
                else
                  g := g.beginFraChoice chooser (.mayDrawThenEachOpponentDraws n)
                    s!"{(g.player chooser).name} may draw {n} cards; if they do, each opponent draws a card"
              | .seq #[.player (.drawCards .you (.manaSpent .triggerSubject)),
                       .ifCond _ (.moveZone _ .graveyard .discard { choice? := some { count := .exact (.const n), .. }, .. }) .noop],
                .noop =>
                let spent := (EvalExpr.evalValue g env (.manaSpent .triggerSubject)).toNat
                if spent == 0 then
                  g := g.logMsg "No mana was spent to cast that spell"
                else
                  let disc := if n == 2 then "two" else toString n
                  g := g.beginFraChoice chooser (.mayDrawThenDiscard spent n.toNat)
                    s!"{(g.player chooser).name} may draw {spent} cards, then discard {disc}"
              | .bind v (.moveZone (.inZones (.handOf .you) (.hasType .artifact)) (.battlefield .controller) .put _) body,
                .noop =>
                let hasArt := (g.player chooser).hand.any fun id => (g.findObject? id).any g.isArtifact
                if hasArt then
                  let id : EffectId := ⟨max 1 g.nextEffectId⟩
                  g := g.change (.nextEffectId (id.raw + 1))
                  let startIdx := g.events.size
                  if !queue.isEmpty then stack := stack.push (.seqRest queue)
                  stack := stack.push (.bindClose v startIdx id body none)
                  ctx := { ctx with oneShotEffectId := id }
                  queue := #[]
                  g := (g.change (.pending (.mayPutArtifactFromHand chooser ctx.sourceId))).logMsg
                    s!"{(g.player chooser).name} may put an artifact card from their hand onto the battlefield"
              | .moveZone (.inZones (.handOf .you) (.hasType .land)) (.battlefield .controller) .put { tapped := true, .. },
                .noop =>
                let hasLand := (g.player chooser).hand.any fun id => (g.findObject? id).any g.isLand
                if hasLand then
                  g := (g.change (.pending (.mayPutLandFromHand chooser))).logMsg
                    s!"{(g.player chooser).name} may put a land card from their hand onto the battlefield tapped"
              | .damage (.deal .this (.targetSlot 0) .eventAmount _), .noop =>
                if g.loggedSheHulkDealtDamage then
                  g := g.logMsg "The Sensational She-Hulk already dealt damage this turn. The ability has no effect."
                else if let some tgt := ctx.targets[0]? then
                  let amt := env.eventAmount
                  if amt > 0 then
                    g := g.beginFraChoice chooser (.sheHulkMayDamage amt tgt ctx.sourceId)
                      s!"{(g.player chooser).name} may have {g.fraSourceName ctx.sourceId} deal {amt} damage"
              | .player (.connive .triggerSubject), .noop =>
                match ctx.sourceId with
                | some sid =>
                  match g.villainConniveTarget? chooser sid ctx.targets with
                  | some vid => g := g.beginMayHaveVillainConnive chooser sid vid
                  | none => pure ()
                | none => pure ()
              | .bind _ (.moveZone (.topOfLibrary .you (.const 1)) .exile .exile { grantPlayPerm? := some _, .. })
                  (.ifCond (.exists (.filter (.stepObjects _) (.hasSubtype (.literal .hero)))) _ .noop),
                .noop =>
                g := g.offerExileTopHeroPump chooser ctx.sourceId
              | .moveZone .triggerSubject .exile .exile { grantPlayPerm? := some { duration := .untilEndOfNextTurnOf .you, .. }, .. },
                .noop =>
                let card? := ctx.triggerSubjectId.bind fun id =>
                  g.followMovedToZone? id (fun | .graveyard q => q == chooser | _ => false)
                match card? with
                | some card =>
                  g := g.beginFraChoice chooser (.moonstoneMayExile card.id)
                    s!"You may exile {g.name card} from your graveyard"
                | none =>
                  if ctx.triggerSubjectId.isSome then
                    g := g.logMsg "The discarded card is no longer in your graveyard"
                  else
                    g := g.logMsg "No discarded card is in the graveyard"
              | .create (.tokens .you cntExpr spec tokMods), .noop =>
                let n := (EvalExpr.evalValue g env cntExpr).toNat
                if tokMods == {} then
                  if n > 0 then
                    let tokPhrase :=
                      if spec == .wall04defender && n == 1 then "a 0/4 Wall creature token with defender"
                      else spec.createdTokensPhrase n false
                    g := g.beginFraChoice chooser (.mayCreateTokens spec n env.toStored)
                      s!"{(g.player chooser).name} may create {tokPhrase}"
                else
                  if !queue.isEmpty then stack := stack.push (.seqRest queue)
                  queue := #[]
                  stack := stack.push (.branchOnChoice onYes onNo)
                  g := (g.changes #[
                    .bindStepOutcome interpChoiceVar {},
                    .pending (.mayResolve chooser)]).logMsg
                    s!"{(g.player chooser).name} may choose whether to resolve the optional effect"
              | .installEffect (.applyContinuous .untilEndOfTurn aff (.setBasePT (some pExpr) (some tExpr))), .noop =>
                if let some o := (resolveLiveObjects g env aff)[0]? then
                  if o.isOnBattlefield then
                    let pVal := EvalExpr.evalValue g env pExpr
                    let tVal := EvalExpr.evalValue g env tExpr
                    g := g.beginFraChoice chooser (.mayBecomeBasePT o.id pVal tVal)
                      s!"{(g.player chooser).name} may have {g.name o}'s base power and toughness become {pVal}/{tVal} until end of turn"
              | .permanent (.attach _ hostExpr true), .noop =>
                if let some host := (resolveLiveObjects g env hostExpr)[0]? then
                  if host.isOnBattlefield then
                    g := (g.change (.pending (.mayAttachEquipment chooser host.id ctx.sourceId))).logMsg
                      s!"{(g.player chooser).name} may attach an Equipment to {g.name host}"
              | .permanent (.modifyCounters (.moveAll .this none) (.target 0) _), .noop =>
                match ctx.sourceId.bind g.findObject?, (resolveLiveObjects g env (.target 0))[0]? with
                | some src, some tgt =>
                  if src.isOnBattlefield && src.status.hasCounters && tgt.isOnBattlefield then
                    g := g.beginFraChoice chooser (.mayMoveAllCounters src.id tgt.id)
                      s!"{(g.player chooser).name} may move all counters from {g.name src} onto {g.name tgt}"
                | _, _ => pure ()
              | .player (.searchLibrary sp), .noop =>
                if sp.filter == (.all #[.hasSupertype .basic, .hasType .land]) && sp.mods.tapped then
                  let (_, hi) := evalInterpCountRange g env sp.count
                  g := g.offerMaySearchBasics chooser hi
                else if sp.filter == .hasType .land && sp.mods.tapped && sp.count == .upTo .eventAmount then
                  let (_, hi) := evalInterpCountRange g env sp.count
                  if hi > 0 then
                    g := g.beginFraChoice chooser (.mayThen onYes ctx.sourceId)
                      s!"{(g.player chooser).name} may search for up to {hi} land cards"
                else
                  if !queue.isEmpty then stack := stack.push (.seqRest queue)
                  queue := #[]
                  stack := stack.push (.branchOnChoice onYes onNo)
                  g := (g.changes #[
                    .bindStepOutcome interpChoiceVar {},
                    .pending (.mayResolve chooser)]).logMsg
                    s!"{(g.player chooser).name} may choose whether to resolve the optional effect"
              | .player (.inspectLibrary { source := .outsideTheGame _ _, .. }), .noop =>
                let g1 := g.materializeSideboard chooser
                let names := (g1.outsideCards chooser).foldl (fun acc o =>
                  let nm := g1.name o
                  if acc.contains nm then acc else acc.push nm) (#[] : Array String)
                if names.size < 2 then
                  g := g1.logMsg s!"{(g1.player chooser).name} has no two cards with different names outside the game"
                else
                  g := g1.beginFraChoice chooser .extrapolateReveal
                    s!"{(g1.player chooser).name} may reveal two cards with different names from outside the game"
              | _, _ =>
                if !queue.isEmpty then stack := stack.push (.seqRest queue)
                queue := #[]
                stack := stack.push (.branchOnChoice onYes onNo)
                g := (g.changes #[
                  .bindStepOutcome interpChoiceVar {},
                  .pending (.mayResolve chooser)]).logMsg
                  s!"{(g.player chooser).name} may choose whether to resolve the optional effect"
          let (g', paused) := pauseIfNeeded g { ctx, queue, stack } pendingBefore randomBefore
          if paused then return g'
          g := g'
        | .unlessPays payerExpr cost ifUnpaid =>
          let env := interpEnv g ctx
          let gen := cost.mana.genericCount
          let pendingBefore := g.pending
          let randomBefore := g.afterRandom
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
          else if ifUnpaid == Instruction.counter (.target 0) then
            match (resolveLiveObjects g env (.target 0))[0]? with
            | some spell =>
              if spell.zone == .stack then
                let payer := (g.stackEntry? spell.id).map (·.controller) |>.getD spell.owner
                g := (g.change (.pending (.payOrLetCounter payer gen (some spell.id)))).logMsg
                  s!"{(g.player payer).name} may pay \{{gen}} or {g.name spell} is countered"
            | none => pure ()
          else if payerExpr == .activePlayer then
            if !g.isOnActiveTeam ctx.controller && g.stillInGame g.activePlayer then
              let ap := g.activePlayer
              if !queue.isEmpty then stack := stack.push (.seqRest queue)
              queue := #[]
              stack := stack.push (.unlessPays ap ifUnpaid)
              ctx := { ctx with targets := #[.player ap], targetSlots := #[#[.player ap]] }
              g := (g.changes #[
                .bindStepOutcome interpChoiceVar {},
                .pending (.payOrLetCounter ap gen none)]).logMsg
                s!"{(g.player ap).name} may pay \{{gen}} or their creatures can't attack Jaces {(g.player ctx.controller).name} controls this turn"
          else
            match (EvalExpr.evalPlayer g env payerExpr)[0]? with
            | some payer =>
              if g.stillInGame payer then
                if !queue.isEmpty then stack := stack.push (.seqRest queue)
                queue := #[]
                stack := stack.push (.unlessPays payer ifUnpaid)
                g := (g.changes #[
                  .bindStepOutcome interpChoiceVar {},
                  .pending (.payOrLetCounter payer gen none)]).logMsg
                  s!"{(g.player payer).name} may pay \{{gen}}"
            | none => pure ()
          let (g', paused) := pauseIfNeeded g { ctx, queue, stack } pendingBefore randomBefore
          if paused then return g'
          g := g'
        | .chooseModes spec =>
          let pendingBefore := g.pending
          let randomBefore := g.afterRandom
          if spec.chooseAtResolution && spec.modes.size > 1 then
            if !queue.isEmpty then stack := stack.push (.seqRest queue)
            queue := #[]
            stack := stack.push (.chooseBranch (spec.modes.map (·.body)) false)
            let phrases := String.intercalate " or " (spec.modes.toList.map (·.toNotation))
            g := (g.changes #[
              .bindStepOutcome interpChoiceVar {},
              .pending (.chooseTriggerOr ctx.controller)]).logMsg
              s!"{(g.player ctx.controller).name} chooses one: {phrases}"
          else if let some chosenModes := g.resolvingModes then
            if chosenModes.isEmpty then
              pure ()
            else if spec.modes == Effect.hawkeyeModeEffects then
              g := g.runHawkeyeArrows ctx.controller chosenModes ctx.targets 0 ctx.sourceId
            else
              if !ctx.targets.isEmpty then
                let combinedSlots := chosenModes.foldl (fun acc mi =>
                  match spec.modes[mi]? with
                  | some m => acc ++ m.targets.slots
                  | none => acc) #[]
                if !combinedSlots.isEmpty then
                  let (modeSlots, _) := g.buildLegalTargetSlots ctx.controller
                    { slots := combinedSlots } ctx.targets ctx.sourceId ctx.skippedOptionalSlots
                  ctx := { ctx with targetSlots := modeSlots, targetSpec := { slots := combinedSlots } }
              if chosenModes.size == 1 then
                if let some m := spec.modes[chosenModes[0]!]? then
                  if !queue.isEmpty then stack := stack.push (.seqRest queue)
                  queue := #[m.body]
              else
                let modeInstrs : Array Instruction := Id.run do
                  let mut acc : Array Instruction := #[]
                  let mut slotOff : Nat := 0
                  for mi in chosenModes do
                    if let some m := spec.modes[mi]? then
                      acc := acc.push (shiftInstrTargetSlots slotOff m.body)
                      slotOff := slotOff + m.targets.slots.size
                  return acc
                if !modeInstrs.isEmpty then
                  if !queue.isEmpty then stack := stack.push (.seqRest queue)
                  queue := modeInstrs
          else if spec.unusedThisTurn && spec.modes.size == 3 then
            let isVision := Instruction.chooseModes spec == Effect.castingVisionModes.body
            if isVision then
              match ctx.sourceId with
              | none => g := g.logMsg "The ability is removed from the stack with no effect"
              | some sid =>
                let available := unusedModes (g.modesChosenThisTurn sid) #[0, 1, 2]
                if available.isEmpty then
                  g := g.logMsg "The Vision's ability is removed from the stack with no effect"
                else
                  g := g.beginFraChoice ctx.controller (.visionMode sid available)
                    "Choose one that hasn't been chosen this turn"
            else
              match ctx.sourceId.bind g.findObject? with
              | none => g := g.logMsg "The ability is removed from the stack with no effect"
              | some src =>
                let available := unusedModes (g.modesChosenThisTurn src.id) #[0, 1, 2]
                if available.isEmpty then
                  g := g.logMsg "all three modes have been chosen this turn. The ability is removed from the stack with no effect"
                else
                  g := g.beginFraChoice ctx.controller (.allianceMode src.id available)
                    s!"{(g.player ctx.controller).name} chooses an Alliance mode that hasn't been chosen this turn"
          else if spec.unusedEver && spec.modes.size == 3 then
            match ctx.sourceId.bind g.findObject? with
            | none => g := g.logMsg "The ability is removed from the stack with no effect"
            | some src =>
              let available := unusedModes (g.modesChosenEver src.id) #[0, 1, 2]
              if available.isEmpty then
                g := g.logMsg "all three modes have been chosen. The ability is removed from the stack with no effect"
              else
                g := g.beginFraChoice ctx.controller (.gollumMode src.id available)
                  s!"{(g.player ctx.controller).name} chooses a mode that hasn't been chosen"
          else if Instruction.chooseModes spec == Effect.stepHydeChoose.body then
            g := g.offerHydeChoice ctx.controller ctx.sourceId
          else if spec.maxModes == .chosenX && spec.modes.size == 4 then
            let chosenModes := (ctx.sourceId.map g.modesChosenEver).getD #[]
            for mi in chosenModes do
              match mi with
              | 0 =>
                g := g.drawThenBeginDiscard ctx.controller 1 1
              | 1 =>
                g := g.loseLifeEachOpponent ctx.controller 2 (cause := some (interpCause g ctx))
              | 2 =>
                match ctx.targets[0]? with
                | some (Target.permanent id) =>
                  if let some o := g.findObject? id then
                    if o.isOnBattlefield && o.printed.isToken && g.canBeTargetedBy ctx.controller o ctx.sourceId then
                      g := g.destroyPermanent o (cause := some (interpCause g ctx))
                | _ => pure ()
              | 3 =>
                match ctx.targets[1]? with
                | some (Target.permanent id) =>
                  match g.findObject? id with
                  | some o =>
                    if o.isOnBattlefield then
                      let actor := (g.controllerOf o).getD o.owner
                      let (g1, _) := g.move id (.graveyard o.owner) none (verb := some .sacrifice) (actor := some actor)
                      g := if (g1.followMovedToZone? id (· == .graveyard o.owner)).isSome then
                        g1.logMsg s!"{g.name o} is sacrificed" else g1
                    else
                      g := g.logMsg "The token was already destroyed and can't be sacrificed"
                  | none =>
                    g := g.logMsg "The token was already destroyed and can't be sacrificed"
                | _ =>
                  g := g.logMsg "The token was already destroyed and can't be sacrificed"
              | _ => pure ()
          else if let some m0 := spec.modes[0]? then
            if !queue.isEmpty then
              stack := stack.push (.seqRest queue)
            queue := #[m0.body]
          let (g', paused) := pauseIfNeeded g { ctx, queue, stack } pendingBefore randomBefore
          if paused then return g'
          g := g'
        | .queueReflexiveTrigger whenDone =>
          let eff := freezeReflexiveTargetEffect g (interpEnv g ctx) whenDone.effect
          let boundObj? :=
            (g.currentStepEnv.find? (·.1 == ⟨0⟩)).bind (fun (_, o) => o.objects[0]?)
          let causeId? := boundObj?.orElse (fun _ => ctx.triggerSubjectId)
          g := g.putReflexiveTrigger ctx.controller ctx.sourceId eff
            (causeIds := ctx.triggerSubjectIds) (causeId := causeId?)
            (lastKnownPower := ctx.lastKnownPower) (lastKnownToughness := ctx.lastKnownToughness)
        | .moveZone objs dest verb mods =>
          let pendingBefore := g.pending
          let randomBefore := g.afterRandom
          let (g1, conts) := execMoveZone g ctx objs dest verb mods
          g := g1
          if !conts.isEmpty then
            if !queue.isEmpty then stack := stack.push (.seqRest queue)
            queue := #[]
            stack := stack ++ conts
          let (g', paused) := pauseIfNeeded g { ctx, queue, stack } pendingBefore randomBefore
          if paused then return g'
          g := g'
        | .create op =>
          let pendingBefore := g.pending
          let randomBefore := g.afterRandom
          let (g1, conts) := execCreate g ctx op
          g := g1
          if !conts.isEmpty then
            if !queue.isEmpty then stack := stack.push (.seqRest queue)
            queue := #[]
            stack := stack ++ conts
          let (g', paused) := pauseIfNeeded g { ctx, queue, stack } pendingBefore randomBefore
          if paused then return g'
          g := g'
        | .permanent op =>
          let pendingBefore := g.pending
          let randomBefore := g.afterRandom
          match op with
          | .modifyCounters (.put kind countExpr) objs none =>
            let env := interpEnv g ctx
            let live := (resolveLiveObjects g env objs).filter (·.isOnBattlefield)
            if live.size > 1 then
              let n := (EvalExpr.evalValue g env countExpr).toNat
              if n > 0 then
                let cause := interpCause g ctx
                let (g1, rest) := g.withBatchCoreReturn (some cause) fun g => Id.run do
                  let mut g := g
                  let mut rest : Array ObjectId := #[]
                  for i in [:live.size] do
                    let o := live[i]!
                    if let some cur := g.findObject? o.id then
                      if cur.isOnBattlefield then
                        g :=
                          if kind == .plusOnePlusOne then
                            g.addPlusOnePlusOneTo cur n (byPlayer := some ctx.controller) (cause := some cause)
                          else
                            g.putCountersDeferredLog cur.id kind n (some ctx.controller) .isPutOn (cause := some cause)
                        if g.pending != pendingBefore && g.pending != .none then
                          rest := (live.extract (i + 1) live.size).map (·.id)
                          break
                  return (g, rest)
                g := g1
                if !rest.isEmpty then
                  if !queue.isEmpty then stack := stack.push (.seqRest queue)
                  queue := #[]
                  stack := stack.push (.forEachObjectRest ⟨997⟩ rest
                    (.permanent (.modifyCounters (.put kind (.const (Int.ofNat n))) (.stepObjects ⟨997⟩) none)))
            else
              g := execPermanent g ctx op
          | _ =>
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
              let (g1, ov?, conts) := execPlayer g ctx op
              g := g1
              if let some ov := ov? then
                if let some (.bindClose v sIdx eid body _) := stack.back? then
                  stack := stack.pop.push (.bindClose v sIdx eid body (some ov))
              if !conts.isEmpty then
                match stack.back? with
                | some (bc@(.bindClose ..)) =>
                  stack := (stack.pop ++ conts).push bc
                | _ =>
                  if !queue.isEmpty then stack := stack.push (.seqRest queue)
                  queue := #[]
                  stack := stack ++ conts
          | _, _ =>
            let (g1, ov?, conts) := execPlayer g ctx op
            g := g1
            if let some ov := ov? then
              if let some (.bindClose v sIdx eid body _) := stack.back? then
                stack := stack.pop.push (.bindClose v sIdx eid body (some ov))
            if !conts.isEmpty then
              match stack.back? with
              | some (bc@(.bindClose ..)) =>
                stack := (stack.pop ++ conts).push bc
              | _ =>
                if !queue.isEmpty then stack := stack.push (.seqRest queue)
                queue := #[]
                stack := stack ++ conts
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

/-- Resolve a unified `Effect` as a spell, activated ability, Saga chapter, or
triggered ability (CR 608). -/
def applyUnified (g : Game) (controller : PlayerId) (effect : Effect)
    (targets : Array Target) (castFromGraveyard := false)
    (kicked := false) (giftPromised := false) (chosenX : Option Nat := none)
    (sourceId : Option ObjectId := none)
    (skippedOptionalSlots : Array Nat := #[])
    (lastKnownPower : Option Int := none)
    (lastKnownToughness : Option Int := none)
    (isSpell : Bool := false) : Game :=
  -- While-source guard: if an effect is gated by `Condition.exists .this` and `.this` is not
  -- on the battlefield, do nothing silently before target validation (e.g. UntapTests).
  let missingWhileSource : Bool :=
    match effect.body with
    | .ifCond (.exists .this) _ .noop => !(sourceId.bind g.findObject?).any (·.isOnBattlefield)
    | _ => false
  if missingWhileSource then g
  else
  -- Heroic Feast (`Effect.resourceGainLifePlusOnes`): cap targets at life gained (CR 608.2b).
  -- Call Damage Control (`Effect.returnUpToTwoGyModal`): validate each target against its chosen mode type.
  let targets :=
    if !isSpell && effect.targets == Effect.resourceGainLifePlusOnes.targets &&
        effect.body == Effect.resourceGainLifePlusOnes.body then
      targets.extract 0 (lastKnownPower.getD 0).toNat
    else if effect.body == Effect.returnUpToTwoGyModal.body &&
        effect.targets == Effect.returnUpToTwoGyModal.targets then
      match g.resolvingModes with
      | some modes =>
        Id.run do
          let mut out : Array Target := #[]
          for i in [0:targets.size] do
            let t := targets[i]!
            let ok :=
              match modes[i]?, t with
              | some m, .card id =>
                (g.findObject? id).any fun o =>
                  match m with
                  | 0 => g.isArtifact o
                  | 1 => g.isCreature o
                  | 2 => g.isEnchantment o
                  | 3 => g.isLand o
                  | _ => true
              | _, _ => true
            if ok then out := out.push t
          return out
      | none => targets
    else targets
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
    let g :=
      if effect.body == Effect.stepCopyAbsorbingMan.body && !targets.isEmpty then
        g.logMsg "The target isn't an artifact, non-Aura enchantment, or land"
      else if effect.body == Effect.watchVillainAttachEquipment.body then
        g.logMsg "The Equipment won't move"
      else g
    if isSpell then g.logMsg "The spell doesn't resolve" else g
  else
    let effectiveSkipped :=
      if skippedOptionalSlots.isEmpty then g.resolvingSkippedSlots else skippedOptionalSlots
    let (legalSlots, illegals) := g.buildLegalTargetSlots controller spec targets sourceId effectiveSkipped
    let g := illegals.foldl (fun g t => g.illegalAbilityTarget t) g
    let srcId? := sourceId.orElse (fun _ => g.resolvingSpell)
    -- Record nth-resolution event before evaluating `EventHistoryPred.nthResolutionThisTurn`
    -- (e.g. Belladonna Took); `Entering.finishAbilityResolution` skips double-recording.
    let g :=
      if hasNthResolutionCheck effect.body then
        let ab? := g.resolvingAbilityObject?.bind (·.triggeredAbility)
        let n := g.loggedResolutions controller srcId? ab? + 1
        let abSnap :=
          (g.resolvingAbilityObject?.map g.snapshot).getD
            (g.snapshot (g.abilitySourceFor controller srcId?))
        let g := g.record (GameEvent.resolved g.turnNumber controller n abSnap
          (sourceId := srcId?) (ability := ab?)
          (cause := some (.gameRule .abilityFinishedResolving)))
        if n > 3 then
          g.logMsg s!"{g.fraSourceName srcId?}'s ability has no effect (resolved {n} times this turn)"
        else g
      else g
    let trigSubj? := g.resolvingAbilityObject?.bind (·.fraCauseId)
    let trigSubjs := (g.resolvingAbilityObject?.map (·.fraCauseIds)).getD #[]
    let trigCtrl? := g.resolvingAbilityObject?.bind (·.fraCauseController)
    let trigSubjCtrl? :=
      ((trigSubj?.bind g.findObject?).bind fun o =>
        if o.isOnBattlefield then g.controllerOf o else none)
      |>.orElse (fun _ => (trigSubj?.bind g.lastKnownBefore?).bind (·.controller))
      |>.orElse (fun _ => trigCtrl?)
    let damagedP? := trigCtrl?.orElse (fun _ => g.loggedLastCombatDamagePlayer)
    let trigPlayers : Array (TriggerPlayerRole × PlayerId) :=
      (match trigSubjCtrl? with | some p => #[(.controllerOfSubject, p)] | none => #[]) ++
      (match trigCtrl? with | some p => #[(.actor, p)] | none => #[]) ++
      (match damagedP? with | some p => #[(.damagedPlayer, p)] | none => #[])
    let ctx : InterpCtx := {
      controller
      sourceId := srcId?
      sourceSnapshot := srcId?.bind g.lastKnownBefore?
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
    -- Wire `CostSpec.bindVar?` on resolving activated abilities / spells into `stepEnv`.
    let costBindVar? : Option VarId :=
      (g.resolvingAbility.bind fun aid =>
        (g.findObject? aid).bind fun aObj =>
          aObj.sourceId.bind fun sid =>
            (g.findObject? sid).bind fun srcObj =>
              (g.activatedAbilitiesOf srcObj).findSome? fun ab =>
                if ab.effect == effect then ab.cost.bindVar? else none)
      |>.orElse fun _ =>
        g.resolvingSpell.bind fun sid =>
          (g.findObject? sid).bind fun sObj =>
            sObj.printed.additionalCosts.findSome? fun ac => ac.cost.bindVar?
    g.withContinuationFrame fun g =>
      let g :=
        match costBindVar? with
        | some bv =>
          let paidObjs := (g.resolvingAbility.map g.boastExiledOf).getD #[]
          let sumPw := lastKnownPower.getD 0
          let out : StepOutcome := {
            objects := paidObjs
            movedCount := paidObjs.size
            sumPower := sumPw
            succeeded := !paidObjs.isEmpty || sumPw != 0
          }
          g.change (.bindStepOutcome bv out)
        | none => g
      g.runInstruction ctx effect.body

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

/-- Resolve a unified `Effect` as an activated ability (convenience wrapper). -/
def applyAbilityEffect (g : Game) (controller : PlayerId) (effect : Effect)
    (targets : Array Target) (sourceId : Option ObjectId := none)
    (lastKnownPower : Option Int := none) (chosenX : Option Nat := none)
    (lastKnownToughness : Option Int := none) : Game :=
  g.applyUnifiedAbility controller effect targets sourceId lastKnownPower chosenX
    (lastKnownToughness := lastKnownToughness)

end Game
end Mtg.Engine
