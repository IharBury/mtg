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
    (preState? : Option Game := none)
    (skipLogIds : Array ObjectId := #[])
    (suppressEmblemLog : Bool := false) : Game :=
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
    let allEmbIds := if old.zone == .command then g.expandTransitiveCommandEmblems #[id] else #[]
    let cmdControlSingles : Array (ObjectId × GameObject × String) :=
      if old.zone != .command || suppressReturnLog then #[]
      else
        g.activeEffects.foldl (fun singles (_, e) =>
          if !allEmbIds.any (fun embId => g.effectExpiresWithLeavingObj embId .command allEmbIds e) then
            singles
          else
            match e with
            | .layered (.objects #[tid]) (.control _) _ =>
              if singles.any (·.1 == tid) then singles
              else
                match g.findObject? tid with
                | some o =>
                  let preObj := (pre.findObject? tid).getD o
                  singles.push (tid, preObj, pre.name preObj)
                | none => singles
            | _ => singles) #[]
    let g :=
      if old.zone == .command then
        g.restoreCopiesWhere
          (fun acc cEid _ _ =>
            match acc.activeEffect? cEid with
            | some ce =>
              allEmbIds.any (fun embId => acc.effectExpiresWithLeavingObj embId .command allEmbIds ce)
            | none => false)
          (cause := expCause) (reconcileControl := false) (skipLogIds := skipLogIds)
      else g
    let g := g.expireEffectsOnLeavingObject old (cause := expCause) (reconcileControl := false)
      (preState? := some pre) (suppressEmblemLog := suppressEmblemLog)
      (suppressReturnLog := if old.zone == .command then true else suppressReturnLog)
      (skipLogIds := skipLogIds)
      (coLeavingIds := allEmbIds)
    let g :=
      if old.zone == .command && !suppressReturnLog then
        cmdControlSingles.foldl (fun acc (tid, o, objName) =>
          if skipLogIds.contains tid then acc
          else
            match acc.findObject? tid with
            | none => acc
            | some cur =>
              let prevCtrl := pre.controllerOf ((pre.findObject? tid).getD o)
              let curCtrl := acc.controllerOf cur
              if curCtrl == prevCtrl then acc
              else
                let p := (cur.defaultController.orElse (fun _ => cur.controller)).getD cur.owner
                let othersRemain := !(acc.appliedControlEffectIds cur).isEmpty
                if othersRemain then
                  match curCtrl with
                  | some q =>
                    if (acc.player q).leftTheGame then acc
                    else acc.logMsg s!"{objName} returns to {(acc.player q).name}'s control"
                  | none => acc
                else if (acc.player p).leftTheGame then
                  acc
                else
                  acc.logMsg s!"{objName} returns to {(acc.player p).name}'s control") g
      else g
    let g :=
      if old.zone == .battlefield then
        g.expireWhileSourceEffects id (cause := expCause) (preState? := some pre)
          (reconcileControl := false) (suppressReturnLog := suppressReturnLog)
          (skipLogIds := skipLogIds) (suppressEmblemLog := suppressEmblemLog)
      else g
    if reconcileControl then
      reconcileControlAfterTransitionFwd pre g (cause := expCause)
    else g
  | none =>
    g.record (GameEvent.ceasedToExist g.turnNumber { id := some id } (cause := effCause))

/-- Cease every command-zone object referenced by an active `.gameRule (.fraEmblem id) d`
matching `pred eid d` (plus transitive child emblems), recording `ceasedToExist` before
`effectExpired` and logging `s!"{embName} ends"` (CR 114.5 / 611.2a). -/
def ceaseEndingFraEmblemsWhere (g : Game) (pred : EffectId → EffectDuration → Bool)
    (cause : Option EventCause := none) (reconcileControl : Bool := false)
    (preState? : Option Game := none)
    (skipLogIds : Array ObjectId := #[]) : Game :=
  let pre := preState?.getD g
  let seedIds : Array ObjectId :=
    g.activeEffects.foldl (fun acc (eid, e) =>
      match e with
      | .gameRule (.fraEmblem id) d =>
        if pred eid d && !acc.contains id then acc.push id else acc
      | _ => acc) #[]
  let endingIds := g.expandTransitiveCommandEmblems seedIds
  let embEntries : Array (ObjectId × String) :=
    endingIds.filterMap fun id =>
      match g.findObject? id with
      | some o =>
        if o.zone == .command then
          some (id, pre.name ((pre.findObject? id).getD o))
        else none
      | none => none
  let g :=
    embEntries.foldl (fun acc (id, _) =>
      match acc.findObject? id with
      | some o =>
        if o.zone == .command then
          acc.ceaseToExist o.id (cause := cause) (reconcileControl := reconcileControl)
            (suppressReturnLog := true) (preState? := some pre)
            (skipLogIds := skipLogIds) (suppressEmblemLog := true)
        else acc
      | none => acc) g
  embEntries.foldl (fun acc (_, embName) => acc.logMsg s!"{embName} ends") g

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
        let preObj := (pre.findObject? o.id).getD o
        let oName := pre.name preObj
        let snap :=
          { (pre.snapshot preObj) with
            id := some o.id
            zone := o.zone
            attachedTo := o.attachedTo
            counters := o.status.toCounterBag }
        g := g.record (GameEvent.unattached g.turnNumber snap hostId
          (cause := .gameRule .unattachOnHostLeave))
        g := g.logMsg s!"{oName} becomes unattached"
    return g

end Game
end Mtg.Engine
