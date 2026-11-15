import Mtg.Engine.Game.Tokens

/-!
# Attach and unattach (CR 701.3)

Attaching a source to a host, a token ceasing to exist (CR 111.7),
zone-list bookkeeping, and unattaching from a leaving host.
-/

namespace Mtg.Engine
namespace Game

/-- Whether `eq` can legally become attached to `host` as an Equipment
(CR 301.5c / 701.3a–b / 702.16d / 702.26b). -/
def canAttachEquipmentTo (g : Game) (eq host : GameObject) : Bool :=
  eq.isOnBattlefield && host.isOnBattlefield && eq.id != host.id &&
    g.isEquipment eq && g.isCreature host &&
    !g.isCreature eq && !g.isBattle eq &&
    !g.frcProtectedFrom host eq

/-- Attach `src` to `host` (CR 301.5 / 303.4 / 701.3a–b). Does nothing if either
permanent is not phased in on `.battlefield`, `src.id == host.id`, `src` is
already attached to `host` (preserving its CR 613.7e timestamp), or `src` cannot
legally attach to `host`. -/
def attachSourceTo (g : Game) (src host : GameObject)
    (cause : Option EventCause := none) : Game :=
  match g.findObject? src.id, g.findObject? host.id with
  | some src, some host =>
    let legalAttachment :=
      if g.isCreature src || g.isBattle src then false
      else if g.isAura src then g.auraObjCanEnchant host src
      else if g.isEquipment src then g.isCreature host && !g.frcProtectedFrom host src
      else false
    if !src.isOnBattlefield || !host.isOnBattlefield ||
        src.id == host.id || src.attachedTo == some host.id || !legalAttachment then
      g
    else
      let effCause := g.resolveOptionalCause cause (fallbackSrc := some src.id) (fallbackCtrl := g.controllerOf src)
      let g := g.record (GameEvent.attached g.turnNumber (g.snapshot src) host.id (previous := src.attachedTo) (cause := effCause))
      g.logMsg s!"{g.name (g.object! src.id)} attaches to {g.name (g.object! host.id)}"
  | _, _ => g

/-- An object ceases to exist (CR 111.7 / 704.5d / 704.5e).
The object is deleted and its id is removed from the zone it occupied, so a
graveyard, hand, library, or stack keeps nothing of it. -/
def ceaseToExist (g : Game) (id : ObjectId) (cause : Option EventCause := none)
    (reconcileControl : Bool := true) (suppressReturnLog : Bool := false)
    (preState? : Option Game := none) : Game :=
  let effCause :=
    g.resolveOptionalCause cause (fallbackSrc := some id)
      (defaultCause := .gameRule .leavingZone)
  match g.findObject? id with
  | some old =>
    let pre := preState?.getD g
    let snap :=
      { (pre.snapshot ((pre.findObject? id).getD old)) with
        id := some old.id
        zone := old.zone }
    let g := g.record (GameEvent.ceasedToExist g.turnNumber snap (cause := effCause))
    let expCause := cause.orElse (fun _ => some (.gameRule .leavingZone))
    let g := g.expireEffectsOnLeavingObject old (cause := expCause) (reconcileControl := false)
    let g :=
      if old.zone == .battlefield then
        g.expireWhileSourceEffects id (cause := expCause) (preState? := some pre)
          (reconcileControl := false) (suppressReturnLog := suppressReturnLog)
      else g
    if reconcileControl then
      reconcileControlAfterTransitionFwd pre g (cause := expCause)
    else g
  | none =>
    g.record (GameEvent.ceasedToExist g.turnNumber { id := some id } (cause := effCause))

/-- Cease every command-zone object referenced by an active `.gameRule (.fraEmblem id) d`
matching `pred eid d`, recording `ceasedToExist` before `effectExpired` and logging
`s!"{embName} ends"` (CR 114.5 / 611.2a). -/
def ceaseEndingFraEmblemsWhere (g : Game) (pred : EffectId → EffectDuration → Bool)
    (cause : Option EventCause := none) (reconcileControl : Bool := false)
    (preState? : Option Game := none) : Game :=
  let pre := preState?.getD g
  let endingIds : Array ObjectId :=
    g.activeEffects.foldl (fun acc (eid, e) =>
      match e with
      | .gameRule (.fraEmblem id) d =>
        if pred eid d && !acc.contains id then acc.push id else acc
      | _ => acc) #[]
  endingIds.foldl (fun acc id =>
    match acc.findObject? id with
    | some o =>
      if o.zone == .command then
        let embName := acc.name o
        (acc.ceaseToExist o.id (cause := cause) (reconcileControl := reconcileControl)
          (suppressReturnLog := true) (preState? := some pre)).logMsg s!"{embName} ends"
      else acc
    | none => acc) g

/-- Move an object to a new zone, assigning a new object identity (CR 400.7).
Auras and Equipment attached to a permanent that leaves the battlefield
(including indirectly phased-out attachments, CR 702.26g / 800.4a) become
unattached and remain on the battlefield (CR 701.3d). -/
def unattachFrom (g : Game) (hostId : ObjectId) (skipIds : Array ObjectId := #[])
    (preState? : Option Game := none) : Game :=
  let pre := preState?.getD g
  Id.run do
    let mut g := g
    for o in g.objects.filter (·.isBattlefieldObject) do
      if o.attachedTo == some hostId && !skipIds.contains o.id then
        let oName := g.name o
        let snap :=
          { (pre.snapshot ((pre.findObject? o.id).getD o)) with
            id := some o.id
            zone := o.zone
            attachedTo := o.attachedTo }
        g := g.record (GameEvent.unattached g.turnNumber snap hostId
          (cause := .gameRule .unattachOnHostLeave))
        g := g.logMsg s!"{oName} becomes unattached"
    return g

end Game
end Mtg.Engine
