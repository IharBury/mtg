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
      if isLegalAuraHost host then
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

def resolveTop (g : Game) : Game :=
  if g.stack.isEmpty then g
  else
    let entry := g.stack.back!
    let g := { g with stack := g.stack.pop }
    match g.findObject? entry.objectId with
    | none => g.logMsg "The spell left the stack unexpectedly"
    | some obj =>
      if let some e := obj.abilityEffect then
        let g := g.applyUnifiedAbility entry.controller e entry.targets obj.sourceId
          obj.lastKnownPower (obj.chosenX.getD 0)
        -- CR 608.2m: after resolution the ability ceases to exist.
        g.ceaseToExist obj.id
      else if let some t := obj.triggeredAbility then
        let srcName := obj.printed.name.replace "'s ability" ""
        let g := g.applyTriggeredAbility entry.controller t obj.sourceId
          entry.targets entry.dividedDamage obj.lastKnownPower obj.lastKnownToughness srcName
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
        let g :=
          match obj.giftPromisedTo, obj.printed.isInstantOrSorcery with
          | some to, true => g.givePromisedGift to
          | _, _ => g
        let g :=
          match spellEffectOf obj entry.chosenMode with
          | some e => g.applyUnified entry.controller e entry.targets
            (castFromGraveyard := obj.castFromGraveyard)
            (kicked := obj.kicked)
            (giftPromised := obj.giftPromisedTo.isSome)
            (chosenX := obj.chosenX.getD 0)
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
        else if obj.castFromGraveyard then
          let (g, _) := g.move obj.id .exile none
          g.logMsg s!"{obj.name} is exiled (flashback)"
        else
          g.moveToOwnerGraveyard obj s!"{obj.name} goes to the graveyard"

end Game
end Mtg.Engine
