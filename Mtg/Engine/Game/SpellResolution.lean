import Mtg.Engine.Game.TriggeredAbilities

/-!
# Spell resolution (CR 608)

Aura spells attaching as they resolve (CR 303.4), Adventure spells going
to exile (CR 715.3d), and `resolveTop` for the top of the stack.
-/

namespace Mtg.Engine
namespace Game

/-- Whether `host` is a legal Enchant-creature attachment (CR 303.4). -/
def isLegalAuraHost (g : Game) (host : GameObject) : Bool :=
  host.isOnBattlefield && g.isCreature host

/-- Resolve an Aura spell, attaching it or putting it into the graveyard (CR 303.4, 608.3a). -/
def resolveAuraSpell (g : Game) (entry : StackEntry) (obj : GameObject) : Game :=
  let finishCause := some (EventCause.gameRule .permanentSpellResolved)
  let toGraveyard (g : Game) : Game :=
    g.moveToOwnerGraveyard obj s!"{obj.name} goes to the graveyard (illegal Aura target)"
      (cause := finishCause)
  match entry.targets[0]? with
  | some (Target.permanent hostId) =>
    match g.findObject? hostId with
    | some host =>
      if g.auraCanEnchant host obj.printed then
        let hostName := g.name host
        let (g, newId) := g.putOntoBattlefield obj.id entry.controller
          (attachedTo := some host.id) (verb := some .resolve) (actor := some entry.controller)
          (cause := finishCause)
        let o := g.object! newId
        let g := g.logMsg s!"{g.name o} enters the battlefield attached to {hostName}"
        g.afterPermanentEnters (g.object! newId)
      else
        toGraveyard g
    | none => toGraveyard g
  | _ => toGraveyard g

/-- Resolve an Adventure: apply its effect, then exile the card and grant
permission to cast the permanent (CR 715.3d). -/
def resolveAdventureSpell (g : Game) (entry : StackEntry) (obj : GameObject) : Game :=
  let finishCause := some (EventCause.gameRule .adventureSpellResolved)
  let orig := obj.adventurerCard.getD obj.printed
  let g := g.changeObjects obj.id #[.printed orig, .adventurerCard none]
  let obj := g.object! obj.id
  let (g, newId) := g.move obj.id .exile none
    (verb := some .resolve) (actor := some entry.controller) (cause := finishCause)
  let o := g.object! newId
  let g := g.createEffect (.playPermission o.id {
      player := entry.controller
      fromAdventure := true })
    (cause := finishCause)
  g.logMsg
    s!"{o.name} is exiled. {(g.player entry.controller).name} may cast it for as long as it remains exiled (CR 715.3d)"

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
    (cause : EventCause) : Game :=
  match kind with
  | .eaglesBirds n =>
    if n > 0 then
      let g :=
        if g.stillInGame controller then
          g.createKindTokens controller .birdSoldier n (cause := some cause)
        else g
      g.logMsg s!"{(g.player controller).name}'s delayed triggered ability creates {n} Bird Soldier token(s)"
    else g
  | .attackPumpPerPlains => g
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
          let sick := !o.printed.keywords.haste
          let (g', newId) := g.putOntoBattlefield id owner (summoningSick := sick) (cause := some cause)
          let g' := g'.logMsg s!"{name} returns to the battlefield (beginning of end step)"
          let back := g'.object! newId
          if back.printed.isLand then g'.afterLandEnters back
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
        let (g', newId) := g.putOntoBattlefield id who
          (summoningSick := !o.printed.keywords.haste) (cause := some cause)
        let g' := g'.logMsg s!"{name} returns to the battlefield"
        g'.afterPermanentEnters (g'.object! newId)
      else g
    | none => g
  | .endStepSynthetic n =>
    g.applyOneDelayedSynthetic controller n cause

def resolveTop (g : Game) : Game :=
  if g.stack.isEmpty then g
  else
    let entry := g.stack.back!
    let g := g.change .popStack
    match g.findObject? entry.objectId with
    | none => g.logMsg "The spell left the stack unexpectedly"
    | some obj =>
      let ctxSrc := obj.sourceId.orElse (fun _ => some obj.id)
      if let some (dtKind, dtCause) := entry.delayedTrigger then
        g.withResolvingContext ctxSrc entry.controller fun g =>
          let g := g.change (.resolvingAbility (some obj.id))
          let g := g.withBatch (some dtCause) (fun g =>
            g.resolveDelayedTrigger entry.controller dtKind dtCause)
          let g := g.change (.resolvingAbility none)
          g.ceaseToExist obj.id (cause := some (.gameRule .abilityFinishedResolving))
      else if let some rawE := obj.abilityEffect then
        let tcs := g.evalLayer3 obj
        let e := if tcs.isEmpty then rawE else TextChange.applyEffect tcs rawE
        g.withResolvingContext ctxSrc entry.controller fun g =>
        let g := g.changes #[.resolvingAbility (some obj.id), .resolvingDivision entry.dividedDamage]
        let g :=
          match obj.triggeredAbility with
          | some rawT =>
            let t := if tcs.isEmpty then rawT else TextChange.applyTriggeredAbility tcs rawT
            if g.fraAbilityTargetsAllIllegal entry.controller obj t entry.targets then
              let g := g.record (GameEvent.removedOnResolution g.turnNumber obj.asEvent)
              let g := entry.targets.foldl (fun (g : Game) (tg : Target) => g.illegalAbilityTarget tg) g
              g.logMsg s!"{obj.name} doesn't resolve because all its targets are illegal (CR 608.2b)"
            else if g.fraConditionHolds entry.controller t.opts.fraCondition (obj.sourceId.bind g.findObject?)
                obj.fraCauseStatus then
              g.applyUnifiedAbility entry.controller e entry.targets obj.sourceId
                entry.lastKnownPower ((g.chosenXOf? obj.id).getD 0)
            else g.logMsg "The intervening condition is no longer true. The ability doesn't resolve."
          | none =>
            g.applyUnifiedAbility entry.controller e entry.targets obj.sourceId
              entry.lastKnownPower ((g.chosenXOf? obj.id).getD 0)
        let g := g.changes #[.resolvingAbility none, .resolvingDivision #[]]
        -- CR 608.2m: after resolution the ability ceases to exist.
        g.ceaseToExist obj.id (cause := some (.gameRule .abilityFinishedResolving))
      else if let some rawT := obj.triggeredAbility then
        let tcs := g.evalLayer3 obj
        let t := if tcs.isEmpty then rawT else TextChange.applyTriggeredAbility tcs rawT
        g.withResolvingContext ctxSrc entry.controller fun g =>
        let srcName := obj.printed.name.replace "'s ability" ""
        let g := g.change (.resolvingAbility (some obj.id))
        let g :=
          if g.fraAbilityTargetsAllIllegal entry.controller obj t entry.targets then
            let g := g.record (GameEvent.removedOnResolution g.turnNumber obj.asEvent)
            let g := entry.targets.foldl (fun (g : Game) (tg : Target) => g.illegalAbilityTarget tg) g
            g.logMsg s!"{obj.name} doesn't resolve because all its targets are illegal (CR 608.2b)"
          else if g.fraConditionHolds entry.controller t.opts.fraCondition (obj.sourceId.bind g.findObject?)
                obj.fraCauseStatus then
            g.applyTriggeredAbility entry.controller t obj.sourceId
              entry.targets entry.dividedDamage entry.lastKnownPower entry.lastKnownToughness srcName
              (resolutionOverride := obj.reflexiveResolution)
          else g.logMsg "The intervening condition is no longer true. The ability doesn't resolve."
        let g := g.change (.resolvingAbility none)
        let g := g.ceaseToExist obj.id (cause := some (.gameRule .abilityFinishedResolving))
        match t.shared with
        | .chapter n _ =>
          match obj.sourceId.bind g.findObject? with
          | some src =>
            match (g.baseCard src).saga, g.controllerOf src with
            | some s, some p =>
              if n == s.finalChapterNumber then g.finishSagaFinalChapter p else g
            | _, _ => g
          | none => g
        | _ => g
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
          let g := g.record (GameEvent.removedOnResolution g.turnNumber obj.asEvent
            (cause := finishCause))
          let g := entry.targets.foldl (fun g t => g.illegalAbilityTarget t) g
          let g := g.logMsg
            s!"{obj.name} doesn't resolve because all its targets are illegal (CR 608.2b)"
          if obj.isCopy then
            (g.ceaseToExist obj.id (cause := some (.stateBased .copyOutsideStackOrBf))).logMsg
              s!"The copy of {obj.name} ceases to exist (CR 704.5e)"
          else if fromGy then
            let (g, _) := g.move obj.id .exile none (cause := finishCause)
            g.logMsg s!"{obj.name} is exiled (flashback)"
          else
            -- An Adventure that doesn't resolve isn't exiled (ruling 5).
            let g := g.changeObjects obj.id #[
              .printed (obj.adventurerCard.getD obj.printed),
              .adventurerCard none]
            g.moveToOwnerGraveyard (g.object! obj.id) s!"{obj.name} goes to the graveyard"
              (cause := finishCause)
        else
        let g :=
          g.withResolvingContext ctxSrc entry.controller fun g =>
            let g :=
              match giftTo, g.isInstantOrSorcery obj with
              | some to, true => g.givePromisedGift to
              | _, _ => g
            let bc := g.baseCard obj
            let tcs := g.evalLayer3 obj
            let modeEffects : Array Effect :=
              if entry.extraModes.isEmpty then (g.spellEffectOf obj entry.chosenMode (kicked := kicked)).toArray
              else
                ((entry.chosenMode.toArray ++ entry.extraModes).qsort (· < ·)).filterMap fun i =>
                  bc.spellModes[i]?.map fun e => if tcs.isEmpty then e else TextChange.applyEffect tcs e
            -- Several chosen modes resolve in printed order, each with the targets
            -- announced for its own instances of “target” (CR 700.2 / 608.2c).
            let g := g.change (.resolvingSpell (some obj.id))
            let (g, _) := modeEffects.foldl (fun (acc : Game × Array Target) e =>
              let (g, rest) := acc
              let n := Nat.min rest.size
                (if e.targetKind.spec.slots.isEmpty then e.targetKind.targetCount
                 else e.targetKind.spec.slots.size)
              let n := if modeEffects.size == 1 then rest.size else n
              let g := g.applyUnified entry.controller e (rest.extract 0 n)
                (castFromGraveyard := fromGy)
                (kicked := kicked)
                (giftPromised := giftTo.isSome)
                (chosenX := chosenX)
              (g, rest.extract n rest.size)) (g, entry.targets)
            let g := g.change (.resolvingSpell none)
            match obj.printed.empowerJace with
            | some n => g.empowerJace entry.controller n
            | none => g
        if obj.isAdventureSpell then
          g.resolveAdventureSpell entry (g.object! obj.id)
        else if obj.printed.isAura then
          g.resolveAuraSpell entry obj
        else if obj.printed.isPermanentCard && !obj.printed.isLand then
          let sick := !obj.printed.keywords.haste
          let sneak := g.sneakPaid obj.id
          let sneakWhom := g.sneakAttackWhom? obj.id
          let sneakTarget :=
            if sneak then
              (g.sneakAttackTarget? obj.id).orElse (fun _ => sneakWhom.map AttackTarget.player)
            else none
          let (g, newId) := g.putOntoBattlefield obj.id entry.controller
            (tapped := sneak)
            (summoningSick := sick)
            (attacking := sneak)
            (attackingTarget := sneakTarget)
            (verb := some .resolve)
            (actor := some entry.controller)
            (cause := some (.gameRule .permanentSpellResolved))
          if let .chooseReplacement .. := g.pending then
            g.chainPendingReplacement .afterLastPermanentEnters
          else
            let o := g.object! newId
            let g := g.logMsg s!"{o.name} enters the battlefield"
            g.afterPermanentEnters (g.object! newId)
        else
          let finishCause := some (EventCause.gameRule .instantOrSorceryFinishedResolving)
          if obj.isCopy then
            (g.ceaseToExist obj.id (cause := some (.stateBased .copyOutsideStackOrBf))).logMsg
              s!"The copy of {obj.name} ceases to exist (CR 704.5e)"
          else if fromGy then
            let (g, _) := g.move obj.id .exile none
              (verb := some .resolve) (actor := some entry.controller) (cause := finishCause)
            g.logMsg s!"{obj.name} is exiled (flashback)"
          else
            g.moveToOwnerGraveyard obj s!"{obj.name} goes to the graveyard"
              (verb := some .resolve) (actor := some entry.controller) (cause := finishCause)

end Game
end Mtg.Engine
