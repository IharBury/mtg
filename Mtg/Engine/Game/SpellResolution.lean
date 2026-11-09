import Mtg.Engine.Game.TriggeredAbilities

/-!
# Spell resolution (CR 608)

Aura spells attaching as they resolve (CR 303.4), Adventure spells going
to exile (CR 715.3d), and `resolveTop` for the top of the stack.
-/

namespace Mtg.Engine
namespace Game

/-- CR 608.2b / 115.1c: true when `targets` is non-empty, `kind` has targets,
and every announced target is illegal for its own non-skipped instance of
“target” (checking `sourceId` for CR 702.16b protection and “another” rules). -/
def targetsAllIllegalForKind (g : Game) (controller : PlayerId)
    (kind : EffectTargetKind) (targets : Array Target)
    (skippedOptionalSlots : Array Nat := #[])
    (sourceId : Option ObjectId := none) : Bool :=
  if kind == .none || targets.isEmpty then false
  else
    let chosenSlots : Array Nat :=
      if kind.spec.slots.isEmpty then #[]
      else (List.range kind.spec.slots.size).toArray.filter (fun s => !skippedOptionalSlots.contains s)
    let survivingPairs : Array (Nat × Target) :=
      (List.range targets.size).toArray.filterMap fun i =>
        let t := targets[i]!
        let slotIdx := chosenSlots[i]?.getD i
        let legal :=
          if kind.spec.slots.isEmpty then
            g.legalTargetsForKind controller kind sourceId
          else
            let slotKind := kind.slotKind slotIdx
            if slotKind.spec.slots.isEmpty then
              g.legalTargetsForAtomicKind controller slotKind sourceId
            else
              g.legalTargetsForKind controller slotKind sourceId
        if legal.contains t then some (slotIdx, t) else none
    if survivingPairs.isEmpty then true
    else
      let badShareSlots : Array Nat :=
        kind.sharesTypeGroups.foldl (fun acc grp =>
          let picked :=
            if kind.spec.slots.isEmpty then survivingPairs.map Prod.snd
            else survivingPairs.filterMap fun (s, t) => if grp.contains s then some t else none
          let invalid : Bool :=
            match picked[0]?, picked[1]? with
            | some (Target.permanent a), some (Target.permanent b) =>
              a == b ||
                match g.findObject? a, g.findObject? b with
                | some oa, some ob => !g.sharesCardType oa ob
                | _, _ => true
            | _, _ => decide (picked.size >= 2)
          if invalid == true then acc ++ grp else acc) #[]
      let badMvSlots : Array Nat :=
        kind.totalMvCapGroups.foldl (fun acc (cap, grp) =>
          let picked :=
            if kind.spec.slots.isEmpty then survivingPairs.map Prod.snd
            else survivingPairs.filterMap fun (s, t) => if grp.contains s then some t else none
          let totalMv := picked.foldl (fun sum t =>
            match t with
            | Target.permanent id =>
              sum + ((g.findObject? id).map g.objectManaValue |>.getD 0)
            | _ => sum) 0
          if totalMv > cap then acc ++ grp else acc) #[]
      if kind.spec.slots.isEmpty then
        !badShareSlots.isEmpty || !badMvSlots.isEmpty
      else
        (survivingPairs.filter fun (s, _) =>
          !badShareSlots.contains s && !badMvSlots.contains s).isEmpty

/-- CR 608.2b: an activated or triggered ability with targets whose targets are
all illegal doesn't resolve. Each announced target is checked against its own
non-skipped instance of “target”. -/
def abilityTargetsAllIllegal (g : Game) (controller : PlayerId) (obj : GameObject)
    (e : Option Effect) (t : Option TriggeredAbility)
    (targets : Array Target) (skippedOptionalSlots : Array Nat := #[]) : Bool :=
  let kind :=
    match e with
    | some eff => eff.targetKind
    | none =>
      match t with
      | some ab => (g.expandEachOpponentEffect controller ab.effect (some obj.id)).targetKind
      | none => .none
  g.targetsAllIllegalForKind controller kind targets
    (skippedOptionalSlots := skippedOptionalSlots)
    (sourceId := obj.sourceId)

/-- Resolve a CR 603.7 delayed triggered ability on the stack. -/
def resolveDelayedTrigger (g : Game) (controller : PlayerId) (kind : DelayedTriggerKind)
    (cause : EventCause) (causeId : Option ObjectId := none)
    (sourceId : Option ObjectId := none) (targets : Array Target := #[]) : Game :=
  match kind with
  | .eaglesBirds n =>
    if n > 0 && g.stillInGame controller then
      let startEventIdx := g.events.size
      let g := g.createKindTokens controller .birdSoldier n (cause := some cause)
      if let .chooseReplacement .. := g.pending then
        g.chainPendingReplacement (.finishPostStep (.logDelayedBirdSoldiersCreated controller startEventIdx))
      else
        let created := (g.tokensCreatedSince startEventIdx).size
        g.logMsg s!"{(g.player controller).name}'s delayed triggered ability creates {created} Bird Soldier token(s)"
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
        if !g.stillInGame owner then
          g.logMsg s!"{g.name o} remains in its current zone (CR 800.4b)"
        else
          let isLand := g.isLand o
          let (g', _) := g.putOntoBattlefield id owner (cause := some cause)
          if let .chooseReplacement .. := g'.pending then
            g'.chainPendingReplacement (.finishPostStep (.returnedBattlefieldEndStep id isLand))
          else
            match g'.followMovedToZone? id (· == .battlefield) with
            | some back =>
              let g' :=
                match back.attachedTo with
                | some hid =>
                  let hostName := (g'.findObject? hid).map g'.name |>.getD "permanent"
                  g'.logMsg s!"{g'.name back} returns to the battlefield attached to {hostName} (beginning of end step)"
                | none =>
                  g'.logMsg s!"{g'.name back} returns to the battlefield (beginning of end step)"
              if g'.isLand back then g'.afterLandEnters back else g'.afterPermanentEnters back
            | none => g'
      else g
  | .endStepExile id =>
    match g.findObject? id with
    | some o =>
      if o.isOnBattlefield then
        let msg := s!"{g.name o} is exiled (beginning of end step)"
        let (g', _) := g.move id .exile none (cause := some cause)
        if let .chooseReplacement .. := g'.pending then
          g'.chainPendingReplacement (.finishPostStep (.logExiledIfInExile id msg))
        else if (g'.followMovedToZone? id (· == .exile)).isSome then
          g'.logMsg msg
        else g'
      else g
    | none => g
  | .endStepSacrifice id =>
    match g.findObject? id with
    | some o =>
      if o.isOnBattlefield then
        g.sacrificeToGraveyard o s!"{g.name o} is sacrificed" (cause := some cause)
      else g
    | none => g
  | .endStepGraveReturn id who =>
    match g.findObject? id with
    | some o =>
      if o.zone == .graveyard o.owner && g.stillInGame who then
        let isLand := g.isLand o
        let (g', _) := g.putOntoBattlefield id who (cause := some cause)
        if let .chooseReplacement .. := g'.pending then
          g'.chainPendingReplacement (.finishPostStep (.returnedToBattlefield id isLand))
        else
          match g'.followMovedToZone? id (· == .battlefield) with
          | some back =>
            let g' :=
              match back.attachedTo with
              | some hid =>
                let hostName := (g'.findObject? hid).map g'.name |>.getD "permanent"
                g'.logMsg s!"{g'.name back} returns to the battlefield attached to {hostName}"
              | none =>
                g'.logMsg s!"{g'.name back} returns to the battlefield"
            if g'.isLand back then g'.afterLandEnters back else g'.afterPermanentEnters back
          | none => g'
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
    (sourceId : Option ObjectId) (empowerJaceN : Option Nat)
    (skippedOptionalSlots : Array Nat := #[])
    (lastKnownPower : Option Int := none) : Game :=
  match modeEffects[0]? with
  | none =>
    match empowerJaceN with
    | some n => g.empowerJace controller n
    | none => g
  | some e =>
    let e := g.expandEachOpponentEffect controller e
      (if g.resolvingAbility.isSome then g.resolvingAbility else g.resolvingSpell)
    let restModes := modeEffects.extract 1 modeEffects.size
    let modeSlots :=
      if !e.requiresTarget then 0
      else
        let ek := modeTargetKind e
        if ek.spec.slots.isEmpty then ek.targetCount else ek.spec.slots.size
    let curSkipped := skippedOptionalSlots.filter (· < modeSlots)
    let skippedHere := curSkipped.size
    let restSkipped :=
      skippedOptionalSlots.filterMap (fun s => if s >= modeSlots then some (s - modeSlots) else none)
    let n := Nat.min remainingTargets.size (modeSlots - skippedHere)
    let n := if restModes.isEmpty then remainingTargets.size else n
    let curTargets := remainingTargets.extract 0 n
    let restTargets := remainingTargets.extract n remainingTargets.size
    let g :=
      if g.continuations.isEmpty then g
      else g.change (.resolvingSkippedSlots curSkipped)
    let pendingBefore := g.pending
    let randomBefore := g.afterRandom
    let g :=
      if g.resolvingAbility.isSome then
        g.applyUnifiedAbility controller e curTargets sourceId lastKnownPower (chosenX := chosenX)
      else
        g.applyUnified controller e curTargets
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
          castFromGraveyard kicked giftPromised chosenX sourceId empowerJaceN restSkipped lastKnownPower)
    else
      g.runSpellModesAndEmpower controller restModes restTargets
        castFromGraveyard kicked giftPromised chosenX sourceId empowerJaceN restSkipped lastKnownPower

def resolveTop (g : Game) : Game :=
  if g.stack.isEmpty then g
  else
    let entry := g.stack.back!
    match g.findObject? entry.objectId with
    | none => (g.change .popStack).logMsg "The spell left the stack unexpectedly"
    | some obj =>
      let isAbility :=
        entry.delayedTrigger.isSome || obj.abilityEffect.isSome || obj.triggeredAbility.isSome
      let ctxSrc :=
        if isAbility then obj.sourceId
        else obj.sourceId.orElse (fun _ => some obj.id)
      let resolvingModes? : Option (Array Nat) :=
        let ms := entry.chosenMode.toArray ++ entry.extraModes
        if ms.isEmpty then none else some ms
      if let some (dtKind, dtCause) := entry.delayedTrigger then
        if dtKind == .attackPumpPerPlains && !entry.targets.isEmpty &&
            !(g.legalTargetsForKind entry.controller .creatureYouControl obj.sourceId).contains entry.targets[0]! then
          let g := g.withResolvingContext ctxSrc entry.controller fun g =>
            let g := g.record (GameEvent.removedOnResolution g.turnNumber (g.snapshot obj))
            let g := entry.targets.foldl (fun (g : Game) (tg : Target) => g.illegalAbilityTarget tg) g
            g.logMsg s!"{g.name obj} doesn't resolve because all its targets are illegal (CR 608.2b)"
          g.ceaseToExist obj.id (cause := some (.gameRule .abilityFinishedResolving))
        else
          let snap := g.snapshot obj
          let g := g.change (.pushContinuationFrame {
            resolvingContext := some (ctxSrc, entry.controller)
            resolvingAbility := some obj.id
            resolvingSkippedSlots := entry.skippedOptionalSlots
            resolvingModes := resolvingModes?
            resolutionFinish := some (.ability obj.id snap entry.controller obj.sourceId) })
          let g := g.withBatch (some dtCause) (fun g =>
            g.resolveDelayedTrigger entry.controller dtKind dtCause obj.fraCauseId obj.sourceId entry.targets)
          g.completeActiveResolutions
      else if let some rawE := obj.abilityEffect then
        let tcs := g.evalLayer3 obj
        let e0 := if tcs.isEmpty then rawE else TextChange.applyEffect tcs rawE
        let e := g.expandEachOpponentEffect entry.controller e0 (some obj.id)
        let runAbilityBody (g : Game) : Game :=
          let chosenX := (g.chosenXOf? obj.id).getD 0
          let trigModes := g.triggerModesOf obj
          if !entry.extraModes.isEmpty && !trigModes.isEmpty then
            let modeEffects :=
              ((entry.chosenMode.toArray ++ entry.extraModes).qsort (· < ·)).filterMap fun i =>
                trigModes[i]?.map fun mEff =>
                  if tcs.isEmpty then mEff else TextChange.applyEffect tcs mEff
            g.runSpellModesAndEmpower entry.controller modeEffects entry.targets
              false false false chosenX obj.sourceId none entry.skippedOptionalSlots
              entry.lastKnownPower
          else
            g.applyUnifiedAbility entry.controller e entry.targets obj.sourceId
              entry.lastKnownPower chosenX
        match obj.triggeredAbility with
        | some rawT =>
          let t := if tcs.isEmpty then rawT else TextChange.applyTriggeredAbility tcs rawT
          if g.abilityTargetsAllIllegal entry.controller obj (some e) (some t) entry.targets
              entry.skippedOptionalSlots then
            let g := g.withResolvingContext ctxSrc entry.controller fun g =>
              let g := g.record (GameEvent.removedOnResolution g.turnNumber (g.snapshot obj))
              let g := entry.targets.foldl (fun (g : Game) (tg : Target) => g.illegalAbilityTarget tg) g
              g.logMsg s!"{g.name obj} doesn't resolve because all its targets are illegal (CR 608.2b)"
            g.ceaseToExist obj.id (cause := some (.gameRule .abilityFinishedResolving))
          else if obj.reflexiveResolution.isNone &&
              !g.triggerInterveningHolds entry.controller t obj.sourceId
                entry.targets entry.lastKnownPower obj.fraCauseId obj.fraCauseStatus then
            let g := g.withResolvingContext ctxSrc entry.controller fun g =>
              let g := g.record (GameEvent.removedOnResolution g.turnNumber (g.snapshot obj))
              g.logMsg "The intervening condition is no longer true. The ability doesn't resolve."
            g.ceaseToExist obj.id (cause := some (.gameRule .abilityFinishedResolving))
          else
            let snap := g.snapshot obj
            let g := g.change (.pushContinuationFrame {
              resolvingContext := some (ctxSrc, entry.controller)
              resolvingAbility := some obj.id
              resolvingDivision := entry.dividedDamage
              resolvingSkippedSlots := entry.skippedOptionalSlots
              resolvingModes := resolvingModes?
              resolutionFinish := some (.ability obj.id snap entry.controller obj.sourceId) })
            let g := runAbilityBody g
            g.completeActiveResolutions
        | none =>
          if g.abilityTargetsAllIllegal entry.controller obj (some e) none entry.targets
              entry.skippedOptionalSlots then
            let g := g.withResolvingContext ctxSrc entry.controller fun g =>
              let g := g.record (GameEvent.removedOnResolution g.turnNumber (g.snapshot obj))
              let g := entry.targets.foldl (fun (g : Game) (tg : Target) => g.illegalAbilityTarget tg) g
              g.logMsg s!"{g.name obj} doesn't resolve because all its targets are illegal (CR 608.2b)"
            g.ceaseToExist obj.id (cause := some (.gameRule .abilityFinishedResolving))
          else
            let snap := g.snapshot obj
            let g := g.change (.pushContinuationFrame {
              resolvingContext := some (ctxSrc, entry.controller)
              resolvingAbility := some obj.id
              resolvingDivision := entry.dividedDamage
              resolvingSkippedSlots := entry.skippedOptionalSlots
              resolvingModes := resolvingModes?
              resolutionFinish := some (.ability obj.id snap entry.controller obj.sourceId) })
            let g := runAbilityBody g
            g.completeActiveResolutions
      else if let some rawT := obj.triggeredAbility then
        let tcs := g.evalLayer3 obj
        let t := if tcs.isEmpty then rawT else TextChange.applyTriggeredAbility tcs rawT
        if g.abilityTargetsAllIllegal entry.controller obj none (some t) entry.targets
            entry.skippedOptionalSlots then
          let g := g.withResolvingContext ctxSrc entry.controller fun g =>
            let g := g.record (GameEvent.removedOnResolution g.turnNumber (g.snapshot obj))
            let g := entry.targets.foldl (fun (g : Game) (tg : Target) => g.illegalAbilityTarget tg) g
            g.logMsg s!"{g.name obj} doesn't resolve because all its targets are illegal (CR 608.2b)"
          g.ceaseToExist obj.id (cause := some (.gameRule .abilityFinishedResolving))
        else if obj.reflexiveResolution.isNone &&
            !g.triggerInterveningHolds entry.controller t obj.sourceId
              entry.targets entry.lastKnownPower obj.fraCauseId obj.fraCauseStatus then
          let g := g.withResolvingContext ctxSrc entry.controller fun g =>
            let g := g.record (GameEvent.removedOnResolution g.turnNumber (g.snapshot obj))
            g.logMsg "The intervening condition is no longer true. The ability doesn't resolve."
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
            resolvingSkippedSlots := entry.skippedOptionalSlots
            resolvingModes := resolvingModes?
            resolutionFinish := some (.ability obj.id snap entry.controller obj.sourceId sagaChapter) })
          let g := g.applyTriggeredAbility entry.controller t obj.sourceId
            entry.targets entry.dividedDamage entry.lastKnownPower entry.lastKnownToughness srcName
            (resolutionOverride := obj.reflexiveResolution)
          g.completeActiveResolutions
      else
        -- CR 608.2b / 608.3b: an instant, sorcery, or targeted Aura spell whose
        -- targets are all illegal doesn't resolve, so none of its effects happen
        -- (rulings 734 / 749). Each target is checked against its own non-skipped slot.
        let kicked := g.wasKicked obj.id
        let fromGy := g.castFromGraveyard obj.id
        let giftTo := g.giftPromisedTo? obj.id
        let chosenX := (g.chosenXOf? obj.id).getD 0
        let auraTargetsAllIllegal :=
          g.isAura obj && !entry.targets.isEmpty &&
            !entry.targets.any fun
              | Target.permanent tid =>
                match g.findObject? tid with
                | some host =>
                  let effCtrl := (g.controllerOf obj).getD entry.controller
                  let auraAsPerm := { obj with controller := some effCtrl }
                  host.isOnBattlefield &&
                    g.canBeTargetedBy entry.controller host (some obj.id) &&
                    g.auraObjCanEnchant host auraAsPerm
                | none => false
              | _ => false
        let allTargetsIllegal :=
          auraTargetsAllIllegal ||
            (g.isInstantOrSorcery obj && !entry.targets.isEmpty &&
              match g.spellEffectOf obj entry.chosenMode entry.extraModes (kicked := kicked) with
              | some e =>
                g.targetsAllIllegalForKind entry.controller e.targetKind entry.targets
                  (skippedOptionalSlots := entry.skippedOptionalSlots)
                  (sourceId := some obj.id)
              | none => false)
        if allTargetsIllegal then
          let finishCause :=
            some (EventCause.gameRule
              (if auraTargetsAllIllegal then .permanentSpellResolved
               else .instantOrSorceryFinishedResolving))
          let g := g.record (GameEvent.removedOnResolution g.turnNumber (g.snapshot obj)
            (cause := finishCause))
          let g := entry.targets.foldl (fun g t => g.illegalAbilityTarget t) g
          let g := g.logMsg
            s!"{g.name obj} doesn't resolve because all its targets are illegal (CR 608.2b)"
          -- CR 702.34a: only a spell actually cast via Flashback is exiled.
          let hasFlashback := g.castViaFlashback obj
          if obj.isCopy then
            let copyMsg :=
              if auraTargetsAllIllegal then
                s!"{g.name obj} ceases to exist (illegal Aura target, CR 704.5e)"
              else
                s!"The copy of {g.name obj} ceases to exist (CR 704.5e)"
            (g.ceaseToExist obj.id (cause := some (.stateBased .copyOutsideStackOrBf))).logMsg copyMsg
          else if hasFlashback then
            let msg := s!"{g.name obj} is exiled (flashback)"
            let (g, _) := g.move obj.id .exile none (cause := finishCause)
            if let .chooseReplacement .. := g.pending then
              g.chainPendingReplacement (.finishPostStep (.logExiledIfInExile obj.id msg))
            else if (g.followMovedToZone? obj.id (· == .exile)).isSome then
              g.logMsg msg
            else g
          else if auraTargetsAllIllegal then
            g.moveToOwnerGraveyard obj s!"{g.name obj} goes to the graveyard (illegal Aura target)"
              (cause := finishCause)
          else
            -- An Adventure that doesn't resolve isn't exiled (ruling 5).
            let permName := (obj.adventurerCard.map (·.name)).getD (g.name obj)
            g.moveToOwnerGraveyard obj s!"{permName} goes to the graveyard"
              (cause := finishCause)
        else
          let snap := g.snapshot obj
          let chosenSpellModes : Array Nat :=
            if entry.extraModes.isEmpty then entry.chosenMode.toArray
            else (entry.chosenMode.toArray ++ entry.extraModes).qsort (· < ·)
          let g := g.change (.pushContinuationFrame {
            resolvingContext := some (ctxSrc, entry.controller)
            resolvingSpell := some obj.id
            resolvingModes := chosenSpellModes
            resolvingSkippedSlots := entry.skippedOptionalSlots
            resolutionFinish := some (.spell entry snap fromGy) })
          let bc := g.baseCard obj
          let modeEffects : Array Effect :=
            if entry.extraModes.isEmpty || isReturnUpToTwoGyModal bc then
              (g.spellEffectOf obj entry.chosenMode entry.extraModes (kicked := kicked)).toArray
            else
              let evalModes := g.evalSpellModes entry.controller obj
              ((entry.chosenMode.toArray ++ entry.extraModes).qsort (· < ·)).filterMap (evalModes[·]?)
          let empowerJaceN := bc.empowerJace
          -- CR 702.131a: Ascend on a resolving instant or sorcery spell is a spell ability.
          let g :=
            if g.isInstantOrSorcery obj && g.hasKeyword obj (·.ascend) then
              g.grantDesignationIfNeeded entry.controller (·.citysBlessing)
                (fun g p => g.permanentCount p ≥ 10) .citysBlessing "has the city's blessing"
            else g
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
                    fromGy kicked giftTo.isSome chosenX (some obj.id) empowerJaceN
                    entry.skippedOptionalSlots entry.lastKnownPower)
              else g
            else
              g.runSpellModesAndEmpower entry.controller modeEffects entry.targets
                fromGy kicked giftTo.isSome chosenX (some obj.id) empowerJaceN
                entry.skippedOptionalSlots entry.lastKnownPower
          g.completeActiveResolutions

end Game
end Mtg.Engine
