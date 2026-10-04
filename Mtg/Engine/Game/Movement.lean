import Mtg.Engine.Game.StatBonuses

/-!
# Zone changes (CR 400)

Exile-instead-of-dying replacement effects (CR 614.6), dying triggers,
`move` — the single zone-change routine — simultaneous moves to the
graveyard, and putting cards onto the battlefield (CR 611.3 / 603.6).
-/

namespace Mtg.Engine
namespace Game

/-- True when `o` replaces an opposing creature dying with exile. -/
def exilesOppDeath? (o : GameObject) : Bool :=
  o.printed.exileOppCreaturesInstead ||
    o.staticAbilities.any (fun
      | .exileOppDeathCreateWolf => true
      | _ => false)

/-- True when `o` also creates a Wolf after that replacement (Head of the Hunt). -/
def createsWolfOnOppExileDeath? (o : GameObject) : Bool :=
  o.staticAbilities.any (fun
    | .exileOppDeathCreateWolf => true
    | _ => false)

/-- Permanents that exile opposing creatures that would die. Uses the SBA
snapshot when one is locked so a simultaneous death of the source still
applies (CR 614.4 / 614.6). -/
def deathReplacementObjects (g : Game) : Array GameObject :=
  match g.lockedDeathReplacements with
  | some xs => xs
  | none => g.battlefield.filter exilesOppDeath?

/-- Controller of a Head-of-the-Hunt-style replacement, if `dying` is an
opposing creature that would go to a graveyard. -/
def exileInsteadSource? (g : Game) (dying : GameObject) : Option GameObject :=
  g.deathReplacementObjects.find? (fun o =>
    o.id != dying.id &&
      match o.controller, dying.controller with
      | some p, some q => p != q
      | _, _ => false)

/-- Controller of a Head-of-the-Hunt-style replacement, if `dying` is an
opposing creature that would go to a graveyard. -/
def exileInsteadController? (g : Game) (dying : GameObject) : Option PlayerId :=
  (g.exileInsteadSource? dying).bind (·.controller)

/-- CR 614.6: if this death would be replaced with exile, the die event
never happens. -/
def wouldExileInsteadOfDying (g : Game) (dying : GameObject) : Bool :=
  dying.status.untilEotExileIfDies || (g.exileInsteadSource? dying).isSome

/-- Dies triggers of a creature leaving the battlefield for a graveyard
(CR 700.4 / 603.6c). A replaced death never happens (CR 614.6), so this
is empty when `dest` is not a graveyard. -/
def dyingTriggers (g : Game) (old : GameObject) (dest : Zone) : Array WaitingTrigger :=
  if old.zone == .battlefield && old.isCreature then
    match dest, old.controller with
    | .graveyard _, some p =>
      old.waitingTriggersFor p .dying (some (g.snapshotPower old))
    | _, _ => (#[] : Array WaitingTrigger)
  else (#[] : Array WaitingTrigger)

/-- `partial` because linked-exile returns recurse into `move` (CR 610.3). -/
partial def move (g : Game) (id : ObjectId) (dest : Zone)
    (controller : Option PlayerId := none) : Game × ObjectId :=
  let old := g.object! id
  let wouldGoToGy :=
    match dest with
    | .graveyard _ => true
    | _ => false
  -- Snapshot the replacement source before the object leaves so a
  -- simultaneous death of Head of the Hunt still applies (CR 614.6).
  let headSource :=
    if old.zone == .battlefield && old.isCreature && wouldGoToGy then
      g.exileInsteadSource? old
    else none
  let headExile := headSource.isSome
  let smiteExile :=
    old.zone == .battlefield && old.status.untilEotExileIfDies && wouldGoToGy
  let finalityExile :=
    old.zone == .battlefield && wouldGoToGy && old.status.finality > 0
  let exileInstead := headExile || smiteExile || finalityExile
  -- CR 614.6: the original move-to-graveyard event never happens.
  let dest := if exileInstead then Zone.exile else dest
  let g :=
    if finalityExile then
      g.logMsg s!"A finality counter exiles {old.name} instead of putting it into a graveyard"
    else g
  let died :=
    old.zone == .battlefield && old.isCreature &&
      match dest with
      | .graveyard _ => true
      | _ => false
  let dying := g.dyingTriggers old dest
  let leaving :=
    if old.zone == .battlefield then
      match old.controller with
      | some p => old.waitingTriggersFor p .leaving
      | none => (#[] : Array WaitingTrigger)
    else (#[] : Array WaitingTrigger)
  let othersDie :=
    if died && !g.suppressOthersDie then
      g.battlefield.foldl (fun acc o =>
        if o.id == old.id then acc
        else
          match o.controller with
          | some p => acc ++ o.waitingTriggersFor p .oneOrMoreOtherCreaturesDie
          | none => acc) (#[] : Array WaitingTrigger)
    else (#[] : Array WaitingTrigger)
  let g :=
    if old.zone == .battlefield then g.unattachFrom id else g
  let g := g.removeFromZoneList id old.zone
  let (g, newId) := g.allocId
  let (g, ts) := g.bumpTime
  let leavingPlay :=
    (old.zone == .battlefield || old.zone == .stack) &&
      dest != .battlefield && dest != .stack
  let printed :=
    if leavingPlay && old.status.transformed then
      match old.printed.otherFace with
      | some front =>
        { front with otherFace := some { old.printed with otherFace := none } }
      | none => old.printed
    else old.printed
  let fresh : GameObject := {
    id := newId
    printed
    owner := old.owner
    controller := controller
    defaultController := if dest == .battlefield then controller else none
    zone := dest
    status := {}
    timestamp := ts
  }
  let g : Game :=
    { g with objects := g.objects.filter (fun (o : GameObject) => o.id != id) |>.push fresh }
  let g :=
    match dest with
    | .library p => g.modifyPlayer p (fun pl => { pl with library := pl.library.push newId })
    | .hand p => g.modifyPlayer p (fun pl => { pl with hand := pl.hand.push newId })
    | .graveyard p => g.modifyPlayer p (fun pl => { pl with graveyard := pl.graveyard.push newId })
    | _ => g
  let gyLeave :=
    match old.zone, old.owner with
    | .graveyard owner, _ =>
      if old.printed.isCreature &&
          (match dest with | .graveyard _ => false | _ => true) then
        (g.permanentsOf owner).foldl (fun acc o =>
          acc ++ o.waitingTriggersFor owner .creatureCardLeavesYourGy) #[]
      else (#[] : Array WaitingTrigger)
    | _, _ => (#[] : Array WaitingTrigger)
  let nontokenDie :=
    if died && !old.printed.isToken then
      match old.controller with
      | some p =>
        g.battlefield.foldl (fun acc o =>
          if o.id == old.id then acc
          else
            match o.controller with
            | some q =>
              if q == p then
                acc ++ o.waitingTriggersFor q .nontokenYouControlDies
              else acc
            | none => acc) (#[] : Array WaitingTrigger)
      | none => (#[] : Array WaitingTrigger)
    else (#[] : Array WaitingTrigger)
  let goblinOrcArmyDie :=
    if died then
      match old.controller with
      | some p =>
        if g.hasSubtype old "Goblin" || g.hasSubtype old "Orc" ||
            g.hasSubtype old "Army" then
          g.battlefield.foldl (fun acc o =>
            if o.id == old.id then acc
            else
              match o.controller with
              | some q =>
                if q == p then
                  acc ++ o.waitingTriggersFor q .anotherGoblinOrcArmyDies
                else acc
              | none => acc) (#[] : Array WaitingTrigger)
        else (#[] : Array WaitingTrigger)
      | none => (#[] : Array WaitingTrigger)
    else (#[] : Array WaitingTrigger)
  let attackingDie :=
    if died && old.status.attacking then
      match old.controller with
      | some p =>
        let fromOthers :=
          g.battlefield.foldl (fun acc o =>
            match o.controller with
            | some q =>
              if q == p then
                acc ++ o.waitingTriggersFor q .attackingCreatureYouControlDies
              else acc
            | none => acc) (#[] : Array WaitingTrigger)
        fromOthers ++ old.waitingTriggersFor p .attackingCreatureYouControlDies
      | none => (#[] : Array WaitingTrigger)
    else (#[] : Array WaitingTrigger)
  -- After the object has left: sources still on the battlefield see
  -- creature cards going to a graveyard (Robot Domination; MSH 138).
  let creatureCardToGy :=
    if g.suppressCreatureCardsToGy then (#[] : Array WaitingTrigger)
    else
      match dest with
      | .graveyard owner =>
        if old.printed.isCreature && !old.printed.isToken then
          g.battlefield.foldl (fun acc o =>
            match o.controller with
            | some p =>
              if p == owner then
                acc ++ o.waitingTriggersFor p .creatureCardsPutIntoYourGy
              else acc
            | none => acc) (#[] : Array WaitingTrigger)
        else (#[] : Array WaitingTrigger)
      | _ => (#[] : Array WaitingTrigger)
  let g := { g with
    waitingTriggers :=
      g.waitingTriggers ++ dying ++ othersDie ++ leaving ++ gyLeave ++
        nontokenDie ++ goblinOrcArmyDie ++ attackingDie ++ creatureCardToGy
    creatureDiedThisTurn := g.creatureDiedThisTurn || died }
  let g :=
    if died then
      { g with battlefieldCreaturesToGyThisTurn :=
        g.battlefieldCreaturesToGyThisTurn.push newId }
    else g
  let g :=
    if died && old.status.attacking then
      { g with lastDiedAttacker := some newId }
    else g
  let g :=
    if exileInstead then
      g.logMsg s!"{old.name} is exiled instead of dying (CR 614.6)"
    else g
  let g :=
    if old.zone == .battlefield && !old.linkedExile.isEmpty then
      Id.run do
        let mut g := g
        for exId in old.linkedExile do
          match g.findObject? exId with
          | some o =>
            if o.zone == .exile then
              let name := o.name
              match o.returnToZone with
              | some (.hand p) =>
                let (g', _) := g.move o.id (.hand p) none
                g := g'
                g := g.logMsg s!"{name} returns to {(g.player p).name}'s hand"
              | some (.graveyard p) =>
                let (g', _) := g.move o.id (.graveyard p) none
                g := g'
                g := g.logMsg s!"{name} returns to {(g.player p).name}'s graveyard"
              | _ =>
              if o.printed.isAura then
                match g.battlefield.find? (fun h => h.isCreature) with
                | none =>
                  g := g.logMsg
                    s!"{name} remains in exile (can't be attached legally; CR 614.6)"
                | some host =>
                  let hostId := host.id
                  let (g', returnedId) := g.move o.id .battlefield (some o.owner)
                  g := g'
                  let returned := g.object! returnedId
                  g := g.setObject { returned with attachedTo := some hostId }
                  g := g.logMsg
                    s!"{name} returns attached to {host.name} (does not target)"
                  let returned := g.object! returnedId
                  match returned.controller with
                  | some p =>
                    g := { g with waitingTriggers :=
                      g.waitingTriggers ++ returned.waitingTriggersFor p .entering }
                  | none => pure ()
              else
                let (g', returnedId) := g.move o.id .battlefield (some o.owner)
                g := g'
                let returned := g.object! returnedId
                let sick := !returned.printed.keywords.haste
                g := g.setObject { returned with
                  status := { returned.status with summoningSick := sick } }
                g := g.logMsg s!"{name} returns to the battlefield"
                let returned := g.object! returnedId
                match returned.controller with
                | some p =>
                  g := { g with waitingTriggers :=
                    g.waitingTriggers ++ returned.waitingTriggersFor p .entering }
                | none => pure ()
          | none => pure ()
        return g
    else g
  -- The modified exile event may include creating a Wolf (Head of the Hunt).
  -- Use the snapshot source: the original die event never happened (CR 614.6).
  let g :=
    match headSource with
    | some src =>
      if createsWolfOnOppExileDeath? src then
        match src.controller with
        | some p =>
          let (g, _) := g.createToken p wolfToken
          g.logMsg s!"{(g.player p).name} creates a Wolf (exiled instead of dying)"
        | none => g
      else g
    | none => g
  let g :=
    if old.zone == .battlefield then
      let g := g.restoreCopiesUntilSourceLeaves old.id
      g.restoreControlUntilSourceLeaves old.id
    else g
  let g :=
    match g.pendingLokiCopy with
    | some (p, some id, _) =>
      if id == old.id then
        { g with pendingLokiCopy := some (p, none, old.lastKnownPower.getD old.power) }
      else g
    | _ => g
  (g, newId)

/-- Move `o` to its owner's graveyard and log `reason`. Exile-if-dies
replacements are applied by `move` (CR 614.1 / 614.6). -/
def moveToOwnerGraveyard (g : Game) (o : GameObject) (reason : String) : Game :=
  let g := g.logMsg reason
  (g.move o.id (.graveyard o.owner) none).1

/-- Move several objects to their owners' graveyards as one event.
Sources that also leave do not see “creature cards put into your
graveyard” (Robot Domination; MSH 138). -/
def moveSimultaneousToGraveyard (g : Game) (ids : Array ObjectId) : Game :=
  let objs := ids.filterMap g.findObject?
  let leavingIds := objs.map (·.id)
  let gyOwners :=
    objs.foldl (fun acc o =>
      if o.printed.isCreature && !o.printed.isToken &&
          !acc.any (· == o.owner) then
        acc.push o.owner
      else acc) (#[] : Array PlayerId)
  let extra :=
    if gyOwners.isEmpty then (#[] : Array WaitingTrigger)
    else
      g.battlefield.foldl (fun acc o =>
        if leavingIds.any (· == o.id) then acc
        else
          match o.controller with
          | some p =>
            if gyOwners.any (· == p) then
              acc ++ o.waitingTriggersFor p .creatureCardsPutIntoYourGy
            else acc
          | none => acc) (#[] : Array WaitingTrigger)
  let g := { g with
    waitingTriggers := g.waitingTriggers ++ extra
    suppressCreatureCardsToGy := true }
  let g :=
    objs.foldl (fun g o =>
      match g.findObject? o.id with
      | some o => g.moveToOwnerGraveyard o s!"{o.name} is put into its owner's graveyard"
      | none => g) g
  { g with suppressCreatureCardsToGy := false }

/-- Put `id` onto the battlefield under `controller`, then set tap, sickness,
and optional attachment. `applyHope` applies Arwen-style enter-with-counters
using weavers that were already present. -/
def putOntoBattlefield (g : Game) (id : ObjectId) (controller : PlayerId)
    (tapped := false) (summoningSick := true)
    (attachedTo : Option ObjectId := none) (applyHope := true) : Game × ObjectId :=
  if (g.player controller).lost then
    let name := (g.object! id).name
    (g.logMsg s!"{name} remains in its current zone (CR 800.4b)", id)
  else
    let asOf := g.timestamp
    let (g, newId) := g.move id .battlefield (some controller)
    let o := g.object! newId
    let o := { o with
      status := { o.status with tapped := tapped, summoningSick := summoningSick } }
    let o :=
      match attachedTo with
      | some host => { o with attachedTo := some host }
      | none => o
    let g := g.setObject o
    let g := if applyHope then g.applyHopeEnterCounters (g.object! newId) asOf else g
    (g, newId)

end Game
end Mtg.Engine
