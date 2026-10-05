import Mtg.Engine.Game.TriggeredAbilities

/-!
# Spell resolution (CR 608)

Aura spells attaching as they resolve (CR 303.4), Adventure spells going
to exile (CR 715.3d), and `resolveTop` for the top of the stack.
-/

namespace Mtg.Engine
namespace Game

/-- Whether `host` is a legal Enchant-creature attachment (CR 303.4). -/
def isLegalAuraHost (host : GameObject) : Bool :=
  host.isOnBattlefield && host.isCreature

/-- Resolve an Aura spell, attaching it or putting it into the graveyard (CR 303.4, 608.3a). -/
def resolveAuraSpell (g : Game) (entry : StackEntry) (obj : GameObject) : Game :=
  let toGraveyard (g : Game) : Game :=
    g.moveToOwnerGraveyard obj s!"{obj.name} goes to the graveyard (illegal Aura target)"
  match entry.targets[0]? with
  | some (Target.permanent hostId) =>
    match g.findObject? hostId with
    | some host =>
      if host.auraCanEnchant obj.printed then
        let (g, newId) := g.putOntoBattlefield obj.id entry.controller
          (attachedTo := some host.id)
        let o := g.object! newId
        let g := g.logMsg s!"{o.name} enters the battlefield attached to {host.name}"
        g.afterPermanentEnters (g.object! newId)
      else
        toGraveyard g
    | none => toGraveyard g
  | _ => toGraveyard g

/-- Resolve an Adventure: apply its effect, then exile the card and grant
permission to cast the permanent (CR 715.3d). -/
def resolveAdventureSpell (g : Game) (entry : StackEntry) (obj : GameObject) : Game :=
  let orig := obj.adventurerCard.getD obj.printed
  let g := g.setObject { obj with printed := orig, adventurerCard := none }
  let obj := g.object! obj.id
  let (g, newId) := g.move obj.id .exile none
  let o := g.object! newId
  let g := g.setObject { o with
    playPermission := some {
      player := entry.controller
      turnEndsRemaining := 0
      fromAdventure := true } }
  g.logMsg
    s!"{o.name} is exiled. {(g.player entry.controller).name} may cast it for as long as it remains exiled (CR 715.3d)"

/-- CR 608.2b: an ability whose targets are all illegal doesn't resolve.
Applied to Reality Fracture triggered abilities, each target checked against
its own instance of “target”. -/
def fraAbilityTargetsAllIllegal (g : Game) (controller : PlayerId) (obj : GameObject)
    (t : TriggeredAbility) (targets : Array Target) : Bool :=
  let isFra :=
    obj.abilityEffect.isSome ||
      match t.effect.resolution with
      | .fra _ => true
      | .sequence rs => rs.any (fun r => match r with | .fra _ => true | _ => false)
      | _ => !t.opts.printed.isEmpty
  let e := obj.abilityEffect.getD t.effect
  let kind := e.targetKind
  isFra && !targets.isEmpty &&
    (List.range targets.size).all (fun i =>
      !(g.legalTargetsForAtomicKind controller (kind.slotKind (if kind.spec.slots.isEmpty then 0 else i))
        obj.sourceId).contains targets[i]!)

def resolveTop (g : Game) : Game :=
  if g.stack.isEmpty then g
  else
    let entry := g.stack.back!
    let g := { g with stack := g.stack.pop }
    match g.findObject? entry.objectId with
    | none => g.logMsg "The spell left the stack unexpectedly"
    | some obj =>
      if let some e := obj.abilityEffect then
        let g := { g with resolvingAbility := some obj.id }
        let g :=
          match obj.triggeredAbility with
          | some t =>
            if g.fraAbilityTargetsAllIllegal entry.controller obj t entry.targets then
              let g := entry.targets.foldl (fun (g : Game) (tg : Target) => g.illegalAbilityTarget tg) g
              g.logMsg s!"{obj.name} doesn't resolve because all its targets are illegal (CR 608.2b)"
            else if g.fraConditionHolds entry.controller t.opts.fraCondition (obj.sourceId.bind g.findObject?) then
              g.applyUnifiedAbility entry.controller e entry.targets obj.sourceId
                obj.lastKnownPower (obj.chosenX.getD 0)
            else g.logMsg "The intervening condition is no longer true. The ability doesn't resolve."
          | none =>
            g.applyUnifiedAbility entry.controller e entry.targets obj.sourceId
              obj.lastKnownPower (obj.chosenX.getD 0)
        let g := { g with resolvingAbility := none }
        -- CR 608.2m: after resolution the ability ceases to exist.
        g.ceaseToExist obj.id
      else if let some t := obj.triggeredAbility then
        let srcName := obj.printed.name.replace "'s ability" ""
        let g := { g with resolvingAbility := some obj.id }
        let g :=
          if g.fraAbilityTargetsAllIllegal entry.controller obj t entry.targets then
            let g := entry.targets.foldl (fun (g : Game) (tg : Target) => g.illegalAbilityTarget tg) g
            g.logMsg s!"{obj.name} doesn't resolve because all its targets are illegal (CR 608.2b)"
          else if g.fraConditionHolds entry.controller t.opts.fraCondition (obj.sourceId.bind g.findObject?) then
            g.applyTriggeredAbility entry.controller t obj.sourceId
              entry.targets entry.dividedDamage obj.lastKnownPower obj.lastKnownToughness srcName
          else g.logMsg "The intervening condition is no longer true. The ability doesn't resolve."
        let g := { g with resolvingAbility := none }
        let g := g.ceaseToExist obj.id
        match t.shared with
        | .chapter n _ =>
          match obj.sourceId.bind g.findObject? with
          | some src =>
            match src.printed.saga, src.controller with
            | some s, some p =>
              if n == s.finalChapterNumber then g.finishSagaFinalChapter p else g
            | _, _ => g
          | none => g
        | _ => g
      else
        -- CR 608.2b: an instant or sorcery whose targets are all illegal
        -- doesn't resolve, so none of its effects happen (rulings 734 / 749).
        -- Each target is checked against its own slot.
        let allTargetsIllegal :=
          obj.printed.isInstantOrSorcery && !entry.targets.isEmpty &&
            match spellEffectOf obj entry.chosenMode with
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
          let g := entry.targets.foldl (fun g t => g.illegalAbilityTarget t) g
          let g := g.logMsg
            s!"{obj.name} doesn't resolve because all its targets are illegal (CR 608.2b)"
          if obj.isCopy then
            (g.ceaseToExist obj.id).logMsg
              s!"The copy of {obj.name} ceases to exist (CR 704.5e)"
          else if obj.castFromGraveyard then
            let (g, _) := g.move obj.id .exile none
            g.logMsg s!"{obj.name} is exiled (flashback)"
          else
            -- An Adventure that doesn't resolve isn't exiled (ruling 5).
            let g := g.setObject { obj with
              printed := obj.adventurerCard.getD obj.printed, adventurerCard := none }
            g.moveToOwnerGraveyard (g.object! obj.id) s!"{obj.name} goes to the graveyard"
        else
        let g :=
          match obj.giftPromisedTo, obj.printed.isInstantOrSorcery with
          | some to, true => g.givePromisedGift to
          | _, _ => g
        let g :=
          match spellEffectOf obj entry.chosenMode with
          | some e =>
            let g := { g with resolvingSpell := some obj.id }
            let g := g.applyUnified entry.controller e entry.targets
              (castFromGraveyard := obj.castFromGraveyard)
              (kicked := obj.kicked)
              (giftPromised := obj.giftPromisedTo.isSome)
              (chosenX := obj.chosenX.getD 0)
            { g with resolvingSpell := none }
          | none => g
        let g :=
          match obj.printed.empowerJace with
          | some n => g.empowerJace entry.controller n
          | none => g
        if obj.isAdventureSpell then
          g.resolveAdventureSpell entry (g.object! obj.id)
        else if obj.printed.isAura then
          g.resolveAuraSpell entry obj
        else if obj.printed.isPermanentCard && !obj.printed.isLand then
          let sick := !obj.printed.keywords.haste
          let sneak := obj.sneakPaid
          let sneakWhom := obj.sneakAttackWhom
          let (g, newId) := g.putOntoBattlefield obj.id entry.controller
            (tapped := sneak || g.entersTapped entry.controller obj.printed)
            (summoningSick := sick)
          -- The permanent remembers X (CR 107.3m) and whether it was cast.
          let o := g.object! newId
          let g := g.setObject { o with chosenX := obj.chosenX, wasCast := !obj.isCopy }
          let o := g.object! newId
          let g :=
            if sneak then
              g.setObject { o with status := { o.status with
                attacking := true
                attackingWhom := sneakWhom } }
            else g
          let o := g.object! newId
          let g := g.logMsg s!"{o.name} enters the battlefield"
          g.afterPermanentEnters (g.object! newId)
        else if obj.isCopy then
          (g.ceaseToExist obj.id).logMsg
            s!"The copy of {obj.name} ceases to exist (CR 704.5e)"
        else if obj.castFromGraveyard then
          let (g, _) := g.move obj.id .exile none
          g.logMsg s!"{obj.name} is exiled (flashback)"
        else
          g.moveToOwnerGraveyard obj s!"{obj.name} goes to the graveyard"

end Game
end Mtg.Engine
