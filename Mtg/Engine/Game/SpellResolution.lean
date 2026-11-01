import Mtg.Engine.Game.TriggeredAbilities

/-!
# Spell resolution (CR 608)

Aura spells attaching as they resolve (CR 303.4), Adventure spells going
to exile (CR 715.3d), and `resolveTop` for the top of the stack.
-/

namespace Mtg.Engine
namespace Game

/-- CR 608.2b: an ability whose targets are all illegal doesn't resolve.
Applied to Reality Fracture triggered abilities, each target checked against
its own instance of “target”. -/
def fraAbilityTargetsAllIllegal (g : Game) (controller : PlayerId) (obj : GameObject)
    (t : TriggeredAbility) (targets : Array Target) : Bool :=
  let tcs := g.evalLayer3 obj
  let isFra :=
    obj.abilityEffect.isSome ||
      match t.effect.resolution with
      | .sequence rs => rs.any Resolution.isFra
      | r => r.isFra || !t.opts.printed.isEmpty
  let rawE := obj.abilityEffect.getD t.effect
  let e := if tcs.isEmpty then rawE else TextChange.applyEffect tcs rawE
  let kind := e.targetKind
  isFra && !targets.isEmpty &&
    (List.range targets.size).all (fun i =>
      !(g.legalTargetsForAtomicKind controller (kind.slotKind (if kind.spec.slots.isEmpty then 0 else i))
        obj.sourceId).contains targets[i]!)

/-- Resolve a CR 603.7 delayed triggered ability on the stack. -/
def resolveDelayedTrigger (g : Game) (controller : PlayerId) (kind : DelayedTriggerKind)
    (cause : EventCause) (causeId : Option ObjectId := none)
    (sourceId : Option ObjectId := none) (targets : Array Target := #[]) : Game :=
  match kind with
  | .eaglesBirds n =>
    if n > 0 then
      let g :=
        if g.stillInGame controller then
          g.createKindTokens controller .birdSoldier n (cause := some cause)
        else g
      g.logMsg s!"{(g.player controller).name}'s delayed triggered ability creates {n} Bird Soldier token(s)"
    else g
  | .attackPumpPerPlains =>
    let n : Int := g.countSubtype controller .plains
    g.withLegalKindPermanent controller .creatureYouControl targets
      (fun g o => g.pumpPermanent o n n)
      sourceId (some "No target was chosen")
  | .endStepReturn id =>
    match g.findObject? id with
    | none => g
    | some o =>
      if o.zone == .exile then
        let owner := o.owner
        if (g.player owner).lost then
          g.logMsg s!"{o.name} remains in its current zone (CR 800.4b)"
        else
          let name := o.name
          let isLand := g.isLand o
          let (g', newId) := g.putOntoBattlefield id owner (cause := some cause)
          let g' := g'.logMsg s!"{name} returns to the battlefield (beginning of end step)"
          if let .chooseReplacement .. := g'.pending then
            g'.chainPendingReplacement (.finishPostStep 20 owner 0 none (some id) (shuffle := isLand))
          else
            let back := g'.object! newId
            if g'.isLand back then g'.afterLandEnters back
            else g'.afterPermanentEnters back
      else g
  | .endStepExile id =>
    match g.findObject? id with
    | some o =>
      if o.isOnBattlefield then
        let (g', _) := g.move id .exile none (cause := some cause)
        g'.logMsg s!"{o.name} is exiled (beginning of end step)"
      else g
    | none => g
  | .endStepSacrifice id =>
    match g.findObject? id with
    | some o =>
      if o.isOnBattlefield then
        g.sacrificeToGraveyard o s!"{o.name} is sacrificed" (cause := some cause)
      else g
    | none => g
  | .endStepGraveReturn id who =>
    match g.findObject? id with
    | some o =>
      if o.zone == .graveyard o.owner && !(g.player who).lost then
        let name := o.name
        let isLand := g.isLand o
        let (g', newId) := g.putOntoBattlefield id who (cause := some cause)
        let g' := g'.logMsg s!"{name} returns to the battlefield"
        if let .chooseReplacement .. := g'.pending then
          g'.chainPendingReplacement (.finishPostStep 20 who 0 none (some id) (shuffle := isLand))
        else
          g'.afterPermanentEnters (g'.object! newId)
      else g
    | none => g
  | .endStepSynthetic n =>
    g.applyOneDelayedSynthetic controller n cause
  | .copyNextInstantSorceryThisTurn
  | .lokiCopyNextInstantSorceryThisTurn _ _ =>
    match causeId.bind g.findObject? with
    | some spell =>
      if spell.zone == .stack then
        let (g, copyId?) := g.copyStackSpellWithId spell controller (cause := some cause)
        match copyId? with
        | some copyId => g.offerSpellRetarget controller copyId 0
        | none => g
      else g
    | none => g

/-- Step through `modeEffects` in printed order (each with its own slice of
`remainingTargets`), pausing and chaining `.continueSpellModes` if any mode opens
a pending choice or `--norandom` request, then running `empowerJace` when done. -/
partial def runSpellModesAndEmpower (g : Game) (controller : PlayerId)
    (modeEffects : Array Effect) (remainingTargets : Array Target)
    (castFromGraveyard kicked giftPromised : Bool) (chosenX : Nat)
    (sourceId : Option ObjectId) (empowerJaceN : Option Nat) : Game :=
  match modeEffects[0]? with
  | none =>
    match empowerJaceN with
    | some n => g.empowerJace controller n
    | none => g
  | some e =>
    let restModes := modeEffects.extract 1 modeEffects.size
    let n := Nat.min remainingTargets.size
      (if e.targetKind.spec.slots.isEmpty then e.targetKind.targetCount
       else e.targetKind.spec.slots.size)
    let n := if restModes.isEmpty then remainingTargets.size else n
    let curTargets := remainingTargets.extract 0 n
    let restTargets := remainingTargets.extract n remainingTargets.size
    let pendingBefore := g.pending
    let randomBefore := g.afterRandom
    let g := g.applyUnified controller e curTargets
      (castFromGraveyard := castFromGraveyard)
      (kicked := kicked)
      (giftPromised := giftPromised)
      (chosenX := chosenX)
      (sourceId := sourceId)
    if restModes.isEmpty && empowerJaceN.isNone then g
    else if (g.pending != pendingBefore && g.pending != .none) ||
        (g.afterRandom != randomBefore && g.afterRandom != .none) then
      g.chainPendingReplacement
        (.continueSpellModes controller restModes restTargets
          castFromGraveyard kicked giftPromised chosenX sourceId empowerJaceN)
    else
      g.runSpellModesAndEmpower controller restModes restTargets
        castFromGraveyard kicked giftPromised chosenX sourceId empowerJaceN

def resolveTop (g : Game) : Game :=
  if g.stack.isEmpty then g
  else
    let entry := g.stack.back!
    match g.findObject? entry.objectId with
    | none => (g.change .popStack).logMsg "The spell left the stack unexpectedly"
    | some obj =>
      let ctxSrc := obj.sourceId.orElse (fun _ => some obj.id)
      if let some (dtKind, dtCause) := entry.delayedTrigger then
        if dtKind == .attackPumpPerPlains && !entry.targets.isEmpty &&
            !(g.legalTargetsForKind entry.controller .creatureYouControl obj.sourceId).contains entry.targets[0]! then
          let g := g.withResolvingContext ctxSrc entry.controller fun g =>
            let g := g.record (GameEvent.removedOnResolution g.turnNumber (g.snapshot obj))
            let g := entry.targets.foldl (fun (g : Game) (tg : Target) => g.illegalAbilityTarget tg) g
            g.logMsg s!"{obj.name} doesn't resolve because all its targets are illegal (CR 608.2b)"
          g.ceaseToExist obj.id (cause := some (.gameRule .abilityFinishedResolving))
        else
          let snap := g.snapshot obj
          let g := g.change (.pushContinuationFrame {
            resolvingContext := some (ctxSrc, entry.controller)
            resolvingAbility := some obj.id
            resolutionFinish := some (.ability obj.id snap entry.controller obj.sourceId) })
          let g := g.withBatch (some dtCause) (fun g =>
            g.resolveDelayedTrigger entry.controller dtKind dtCause obj.fraCauseId obj.sourceId entry.targets)
          g.completeActiveResolutions
      else if let some rawE := obj.abilityEffect then
        let tcs := g.evalLayer3 obj
        let e := if tcs.isEmpty then rawE else TextChange.applyEffect tcs rawE
        match obj.triggeredAbility with
        | some rawT =>
          let t := if tcs.isEmpty then rawT else TextChange.applyTriggeredAbility tcs rawT
          if g.fraAbilityTargetsAllIllegal entry.controller obj t entry.targets then
            let g := g.withResolvingContext ctxSrc entry.controller fun g =>
              let g := g.record (GameEvent.removedOnResolution g.turnNumber (g.snapshot obj))
              let g := entry.targets.foldl (fun (g : Game) (tg : Target) => g.illegalAbilityTarget tg) g
              g.logMsg s!"{obj.name} doesn't resolve because all its targets are illegal (CR 608.2b)"
            g.ceaseToExist obj.id (cause := some (.gameRule .abilityFinishedResolving))
          else if !g.fraConditionHolds entry.controller t.opts.fraCondition (obj.sourceId.bind g.findObject?)
              obj.fraCauseStatus then
            let g := g.logMsg "The intervening condition is no longer true. The ability doesn't resolve."
            g.ceaseToExist obj.id (cause := some (.gameRule .abilityFinishedResolving))
          else
            let snap := g.snapshot obj
            let g := g.change (.pushContinuationFrame {
              resolvingContext := some (ctxSrc, entry.controller)
              resolvingAbility := some obj.id
              resolvingDivision := entry.dividedDamage
              resolutionFinish := some (.ability obj.id snap entry.controller obj.sourceId) })
            let g := g.applyUnifiedAbility entry.controller e entry.targets obj.sourceId
              entry.lastKnownPower ((g.chosenXOf? obj.id).getD 0)
            g.completeActiveResolutions
        | none =>
          let snap := g.snapshot obj
          let g := g.change (.pushContinuationFrame {
            resolvingContext := some (ctxSrc, entry.controller)
            resolvingAbility := some obj.id
            resolvingDivision := entry.dividedDamage
            resolutionFinish := some (.ability obj.id snap entry.controller obj.sourceId) })
          let g := g.applyUnifiedAbility entry.controller e entry.targets obj.sourceId
            entry.lastKnownPower ((g.chosenXOf? obj.id).getD 0)
          g.completeActiveResolutions
      else if let some rawT := obj.triggeredAbility then
        let tcs := g.evalLayer3 obj
        let t := if tcs.isEmpty then rawT else TextChange.applyTriggeredAbility tcs rawT
        if g.fraAbilityTargetsAllIllegal entry.controller obj t entry.targets then
          let g := g.withResolvingContext ctxSrc entry.controller fun g =>
            let g := g.record (GameEvent.removedOnResolution g.turnNumber (g.snapshot obj))
            let g := entry.targets.foldl (fun (g : Game) (tg : Target) => g.illegalAbilityTarget tg) g
            g.logMsg s!"{obj.name} doesn't resolve because all its targets are illegal (CR 608.2b)"
          g.ceaseToExist obj.id (cause := some (.gameRule .abilityFinishedResolving))
        else if !g.fraConditionHolds entry.controller t.opts.fraCondition (obj.sourceId.bind g.findObject?)
            obj.fraCauseStatus then
          let g := g.logMsg "The intervening condition is no longer true. The ability doesn't resolve."
          g.ceaseToExist obj.id (cause := some (.gameRule .abilityFinishedResolving))
        else
          let sagaChapter :=
            match t.shared with
            | .chapter n _ => some n
            | _ => none
          let snap := g.snapshot obj
          let srcName := obj.printed.name.replace "'s ability" ""
          let g := g.change (.pushContinuationFrame {
            resolvingContext := some (ctxSrc, entry.controller)
            resolvingAbility := some obj.id
            resolvingDivision := entry.dividedDamage
            resolutionFinish := some (.ability obj.id snap entry.controller obj.sourceId sagaChapter) })
          let g := g.applyTriggeredAbility entry.controller t obj.sourceId
            entry.targets entry.dividedDamage entry.lastKnownPower entry.lastKnownToughness srcName
            (resolutionOverride := obj.reflexiveResolution)
          g.completeActiveResolutions
      else
        -- CR 608.2b: an instant or sorcery whose targets are all illegal
        -- doesn't resolve, so none of its effects happen (rulings 734 / 749).
        -- Each target is checked against its own slot.
        let kicked := g.wasKicked obj.id
        let fromGy := g.castFromGraveyard obj.id
        let giftTo := g.giftPromisedTo? obj.id
        let chosenX := (g.chosenXOf? obj.id).getD 0
        let allTargetsIllegal :=
          g.isInstantOrSorcery obj && !entry.targets.isEmpty &&
            match g.spellEffectOf obj entry.chosenMode entry.extraModes (kicked := kicked) with
            | some e =>
              let kind := e.targetKind
              let legal :=
                if kind.spec.slots.isEmpty then
                  g.legalTargetsForKind entry.controller kind (some obj.id)
                else
                  kind.spec.slots.foldl (fun acc k =>
                    acc ++ g.legalTargetsForAtomicKind entry.controller k (some obj.id)) #[]
              entry.targets.all (fun t => !legal.contains t)
            | none => false
        if allTargetsIllegal then
          let finishCause := some (EventCause.gameRule .instantOrSorceryFinishedResolving)
          let g := g.record (GameEvent.removedOnResolution g.turnNumber (g.snapshot obj)
            (cause := finishCause))
          let g := entry.targets.foldl (fun g t => g.illegalAbilityTarget t) g
          let g := g.logMsg
            s!"{obj.name} doesn't resolve because all its targets are illegal (CR 608.2b)"
          let hasFlashback :=
            GameEvent.castWithFlashback g.events obj.id || g.flashbackUntilEot obj ||
              (fromGy && !g.freeCastFromGraveyard obj &&
                ((g.baseCard obj).flashback.isSome || g.hasFlashbackPermission obj))
          if obj.isCopy then
            (g.ceaseToExist obj.id (cause := some (.stateBased .copyOutsideStackOrBf))).logMsg
              s!"The copy of {obj.name} ceases to exist (CR 704.5e)"
          else if hasFlashback then
            let (g, _) := g.move obj.id .exile none (cause := finishCause)
            g.logMsg s!"{obj.name} is exiled (flashback)"
          else
            -- An Adventure that doesn't resolve isn't exiled (ruling 5).
            let permName := (obj.adventurerCard.getD obj.printed).name
            g.moveToOwnerGraveyard obj s!"{permName} goes to the graveyard"
              (cause := finishCause)
        else
          let snap := g.snapshot obj
          let g := g.change (.pushContinuationFrame {
            resolvingContext := some (ctxSrc, entry.controller)
            resolvingSpell := some obj.id
            resolutionFinish := some (.spell entry snap fromGy) })
          let bc := g.baseCard obj
          let tcs := g.evalLayer3 obj
          let modeEffects : Array Effect :=
            if entry.extraModes.isEmpty then (g.spellEffectOf obj entry.chosenMode (kicked := kicked)).toArray
            else
              ((entry.chosenMode.toArray ++ entry.extraModes).qsort (· < ·)).filterMap fun i =>
                bc.spellModes[i]?.map fun e => if tcs.isEmpty then e else TextChange.applyEffect tcs e
          let empowerJaceN := bc.empowerJace
          let g :=
            match giftTo, g.isInstantOrSorcery obj with
            | some to, true => g.givePromisedGift to
            | _, _ => g
          -- Several chosen modes resolve in printed order, each with the targets
          -- announced for its own instances of “target” (CR 700.2 / 608.2c).
          let g :=
            if g.pending != .none || g.afterRandom != .none then
              if !modeEffects.isEmpty || empowerJaceN.isSome then
                g.chainPendingReplacement
                  (.continueSpellModes entry.controller modeEffects entry.targets
                    fromGy kicked giftTo.isSome chosenX (some obj.id) empowerJaceN)
              else g
            else
              g.runSpellModesAndEmpower entry.controller modeEffects entry.targets
                fromGy kicked giftTo.isSome chosenX (some obj.id) empowerJaceN
          g.completeActiveResolutions

end Game
end Mtg.Engine
