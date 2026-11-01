import Mtg.Engine.Game.ActivationCosts

/-!
# Damage, destruction, and life (CR 120 / 119)

Destroying permanents (CR 701.8), marking damage with replacement
effects (shield counters, prevention, multipliers), damage to players,
fights (CR 701.14), and life loss and gain (CR 119).
-/

namespace Mtg.Engine
namespace Game

/-- The resolving spell, or the source of the resolving ability, as the
default damage source when an effect deals damage without naming another
source (CR 609.7 / 113.7 / 120.2). -/
def resolvingDamageSource? (g : Game) : Option GameObject :=
  match g.resolvingSpell.bind g.findObject? with
  | some s => some s
  | none =>
  match (g.resolvingAbility.bind g.findObject?).bind (fun ab => ab.sourceId.bind g.findObject?) with
  | some s => some s
  | none =>
  match g.triggerSequenceRest.bind (fun r => r.sourceId.bind g.findObject?) with
  | some s => some s
  | none =>
  match g.mayContext.bind (fun r => r.sourceId.bind g.findObject?) with
  | some s => some s
  | none =>
  match g.triggerOr.bind (fun r => r.sourceId.bind g.findObject?) with
  | some s => some s
  | none =>
  match g.chooseModesRest.bind (fun r => r.sourceId.bind g.findObject?) with
  | some s => some s
  | none =>
  match g.fraAfterLook.bind (fun (_, sid?, _) => sid?.bind g.findObject?) with
  | some s => some s
  | none => none

/-- Reconstruct an LKI `GameObject` from an `EventObject` snapshot so damage
replacement, protection, and lifelink queries on a departed source use its
last known characteristics and controller (CR 113.7a / 608.2h). -/
def damageSourceObjectFromLki (eo : EventObject) : GameObject :=
  let basePrinted := eo.toCardDef
  let printed : CardDef :=
    { basePrinted with
      name := eo.name
      manaCost :=
        if basePrinted.manaValue == eo.manaValue then basePrinted.manaCost
        else ManaCost.ofGeneric eo.manaValue
      colorIndicator := some eo.colors
      types := eo.types
      subtypes := eo.subtypes.map CardSubtype.englishName
      supertypes := eo.supertypes
      power := eo.power
      toughness := eo.toughness
      keywords := { eo.keywords with changeling := eo.keywords.changeling || eo.changeling }
      toxic := eo.toxic
      staticAbilities := eo.staticAbilities
      isToken := eo.token }
  { id := eo.id.getD noSourceSentinelId
    printed := printed
    owner := eo.owner
    controller := eo.controller
    defaultController := eo.controller
    zone := eo.zone
    status := {
      tapped := eo.tapped
      attacking := eo.attacking
      attackingTarget := eo.attackingTarget
      phasedOut := eo.phasedOut
      faceDown := eo.faceDown
      transformed := eo.transformed
      chosenOdd := eo.chosenOdd
      chosenCreatureType := eo.chosenCreatureType
      chosenColor := eo.chosenColor
      chosenName := eo.chosenColor.elim eo.chosenName (fun _ => eo.chosenName)
      chosenCardType := eo.chosenCardType
      chosenAnchor := eo.chosenAnchor
    }
    attachedTo := eo.attachedTo
    isCopy := eo.isCopy
    isCommander := eo.isCommander }

/-- Look up a damage source by `id`: live `GameObject` if still at `id`,
otherwise its `lastKnownBefore?` LKI snapshot (CR 113.7a / 608.2h). -/
def damageSourceById? (g : Game) (sid : ObjectId) : Option GameObject :=
  (g.findObject? sid).orElse (fun _ => (g.lastKnownBefore? sid).map damageSourceObjectFromLki)

/-- Snapshot a damage source by `id`: live `g.snapshot` if still at `id`,
otherwise `g.lastKnownBefore? sid` (CR 113.7a / 608.2h). -/
def damageSourceEventById? (g : Game) (sid : ObjectId) : Option EventObject :=
  match g.findObject? sid with
  | some s => some (g.snapshot s)
  | none => g.lastKnownBefore? sid

/-- Snapshot a `GameObject` damage source: live `g.snapshot` if still at `src.id`,
otherwise its frozen `lastKnownBefore?` LKI snapshot (CR 113.7a / 608.2h). -/
def snapshotDamageSource (g : Game) (src : GameObject) : EventObject :=
  if (g.findObject? src.id).isSome then g.snapshot src
  else (g.lastKnownBefore? src.id).getD (g.snapshot src)

/-- Resolve a stored damage-source `EventObject` snapshot to a `GameObject`:
returns the live `GameObject` if still at `eo.id`, otherwise reconstructs an
LKI `GameObject` via `damageSourceObjectFromLki` without calling `followMoved`
(which would pick up the post-move object and drop battlefield LKI, CR 113.7a /
608.2h). -/
def damageSourceFromSnapshot (g : Game) (eo : EventObject) : GameObject :=
  match eo.id.bind g.findObject? with
  | some live => live
  | none => damageSourceObjectFromLki eo

/-- Optional wrapper around `damageSourceFromSnapshot`. -/
def damageSourceObjFromSnapshot? (g : Game) (source : Option EventObject) : Option GameObject :=
  source.map g.damageSourceFromSnapshot

/-- Refresh a stored `EventObject` snapshot if its `id` is still live in `g`,
or keep the frozen LKI snapshot when the original `id` has departed. -/
def refreshOrKeepDamageSnapshot (g : Game) (eo : EventObject) : EventObject :=
  match eo.id.bind g.findObject? with
  | some live => g.snapshot live
  | none => eo

/-- Source `ObjectId` of the currently resolving ability/continuation when the
source is no longer at its original `ObjectId`. -/
private def resolvingDepartedSourceId? (g : Game) : Option ObjectId :=
  (g.resolvingAbility.bind g.findObject?).bind (·.sourceId)
    |>.orElse (fun _ => g.triggerSequenceRest.bind (·.sourceId))
    |>.orElse (fun _ => g.mayContext.bind (·.sourceId))
    |>.orElse (fun _ => g.triggerOr.bind (·.sourceId))
    |>.orElse (fun _ => g.chooseModesRest.bind (·.sourceId))
    |>.orElse (fun _ => g.fraAfterLook.bind (fun (_, s, _) => s))

/-- The resolving damage source object, using `lastKnownBefore?` LKI if the
source left its zone before its ability resolved (CR 113.7a / 608.2h). -/
def resolvingMovedDamageSource? (g : Game) : Option GameObject :=
  match g.resolvingDamageSource? with
  | some s => some s
  | none => g.resolvingDepartedSourceId?.bind g.damageSourceById?

/-- Snapshot the resolving damage source as an `EventObject`, using
`lastKnownBefore?` LKI if the source left its zone before its ability resolved
(CR 113.7a / 608.2h). -/
def resolvingDamageSourceEvent? (g : Game) : Option EventObject :=
  match g.resolvingDamageSource? with
  | some s => some (g.snapshot s)
  | none => g.resolvingDepartedSourceId?.bind g.damageSourceEventById?

/-- Reconstruct the pre-batch board state when `o.id` already existed on the
battlefield at the start of an enclosing simultaneous batch (CR 608.2c / 701.8b). -/
private def preBatchDestroyCheck (g : Game) (o : GameObject) : Game × GameObject :=
  if g.currentBatch.isSome && !g.openBatchObjects.isEmpty then
    let preG : Game :=
      { g with
        objects := g.openBatchObjects
        players := g.openBatchPlayers
        activeEffects := g.openBatchEffects
        stack := g.openBatchStack }
    match preG.findObject? o.id with
    | some preO =>
      if preO.isOnBattlefield then (preG, preO) else (g, o)
    | none => (g, o)
  else (g, o)

/-- Destroy a permanent (CR 701.8). Indestructible permanents aren't destroyed
(CR 702.12b). A shield counter replaces destruction with removing a
shield counter via the CR 616.1 replacement loop (CR 122.1c / 614.6). If it
would die this turn under an exile replacement, `move` sends it to exile instead
of the graveyard (CR 614.1). -/
def destroyPermanent (g : Game) (o : GameObject)
    (cause : Option EventCause := none)
    (preBattlefield : Option (Array GameObject) := none) : Game :=
  if let .chooseReplacement .. := g.pending then
    g.chainPendingReplacement (.destroyPermanent o.id cause preBattlefield)
  else
  let (checkG, checkO) := g.preBatchDestroyCheck o
  if checkG.hasIndestructible checkO then
    g.logMsg s!"{g.name o} is indestructible and isn't destroyed"
  else
  let ctrl := g.controllerOf o
  let affected := ctrl.getD o.owner
  let mutSpecs : Array ReplacementSpec := Id.run do
    let mut s : Array ReplacementSpec := #[]
    if o.status.shield > 0 then
      s := s.push {
        id := { kind := .shieldCounterDestroy, object := some o.id }
        source := some o.id
        controller := ctrl
        affectedPlayer := affected
        kind := .shieldCounterDestroy o.id
      }
    for (_, eff) in g.activeEffects do
      match eff with
      | .replacement spec _ =>
        match spec.kind with
        | .shieldCounterDestroy tid =>
          if tid == o.id && o.status.shield > 0 then
            s := s.push { spec with affectedPlayer := affected }
        | _ => pure ()
      | _ => pure ()
    return s
  let candidates := mutSpecs.map (fun s => (ReplacementOrPrevention.replacement s).toCandidate)
  match g.selectNextReplacementStep candidates #[] with
  | .needChoice chooser choices _ =>
    g.promptChooseReplacement chooser choices (.destroyPermanent o.id cause preBattlefield)
  | .chosen chosen _ =>
    let g := g.consumeReplacementOrder #[chosen.id]
    let cause' := g.wrapReplacedCause chosen.id cause ctrl
    let finalCause := g.resolveOptionalCause cause' (fallbackCtrl := ctrl)
    let oName := g.name o
    let g := g.record (GameEvent.counters g.turnNumber ctrl (g.snapshot o) .shield 1 true (cause := finalCause))
    g.logMsg s!"A shield counter is removed from {oName} instead of destroying it"
  | .none =>
    g.moveToOwnerGraveyard o s!"{g.name o} is destroyed" (verb := some .destroy)
      (preBattlefield := preBattlefield) (cause := cause)

/-- True when all damage that would be dealt to `o` is prevented. -/
def preventsAllDamageTo (g : Game) (o : GameObject) : Bool :=
  (g.staticAbilities o).any (fun
    | .preventAllDamageToThis => true
    | _ => false) ||
  g.activeEffects.any (fun (_, eff) =>
    match eff with
    | .prevention spec _ =>
      match spec.kind with
      | .preventAllDamageToPermanent tid => tid == o.id
      | _ => false
    | _ => false)

/-- Result of running the CR 616.1 replacement and prevention loop on proposed damage. -/
structure DamageReplacementResult where
  amount : Int
  prevented : Bool := false
  preventedAmount : Nat := 0
  shieldRemoved : Bool := false
  shieldRemoveCause : Option EventCause := none
  applied : Array ReplacementId := #[]
  cause : Option EventCause := none
  choice? : Option (PlayerId × Array ReplacementId) := none
deriving Repr, Inhabited, BEq

/-- True when a `.shield` counter was already removed from `oid` earlier in the
currently open combat-damage batch (CR 510.2 / 122.1c). -/
def shieldRemovedInCurrentCombatBatch (g : Game) (oid : ObjectId) : Bool :=
  match g.currentBatch with
  | some (bid, _) =>
    g.events.any (fun e =>
      e.batch == some bid &&
        match e.change with
        | .rules (.permanent (.counters (.object eo) .shield (.removed _) _)) =>
          eo.id == some oid
        | _ => false)
  | none => false

/-- Run the CR 616.1 replacement and prevention loop on `n` damage from `src?`
to `recipientPerm?` or `recipientPlayer?` (CR 614.1a / 615.1 / 616.1; rulings
MSH 177–179, 237, 305). -/
def replaceDamage (g : Game) (n : Int)
    (src? : Option GameObject := none)
    (srcEvent? : Option EventObject := none)
    (recipientPerm? : Option GameObject := none)
    (recipientPlayer? : Option PlayerId := none)
    (combat : Bool := false)
    (unpreventable : Bool := false)
    (applied : Array ReplacementId := #[])
    (cause : Option EventCause := none) : DamageReplacementResult := Id.run do
  if n <= 0 then
    return { amount := n, applied := applied, cause := cause }
  let recipientCtrl? : Option PlayerId :=
    recipientPlayer?.orElse (fun _ => recipientPerm?.bind g.controllerOf)
  let affected : PlayerId :=
    recipientCtrl?.orElse (fun _ => recipientPerm?.map (·.owner))
      |>.orElse (fun _ => src?.bind g.controllerOf)
      |>.getD g.activePlayer
  let srcEvent : EventObject :=
    srcEvent?.orElse (fun _ => src?.map g.snapshotDamageSource)
      |>.orElse (fun _ => g.resolvingDamageSourceEvent?)
      |>.getD default
  let propCause := g.resolveOptionalCause cause (fallbackSrc := srcEvent.id) (fallbackCtrl := some affected)
  let proposed? : Option GameEvent :=
    match recipientPerm?, recipientPlayer? with
    | some o, _ => some (GameEvent.damaged g.turnNumber srcEvent (g.snapshot o) n.toNat combat (cause := propCause))
    | none, some pid => some (GameEvent.damagedPlayer g.turnNumber srcEvent pid n.toNat combat (cause := propCause))
    | none, none => none
  if proposed?.any (!·.watches .wouldDealDamage) then
    return { amount := 0, prevented := true, applied := applied, cause := cause }
  -- Unpreventable damage to a permanent with a shield counter still removes a
  -- shield counter via its replacement effect without preventing the damage (CR 122.1c).
  -- In a simultaneous combat-damage batch (CR 510.2 / 122.1c), a single shield
  -- counter removed earlier in the batch prevents all remaining preventable
  -- combat damage to that permanent without removing a second shield counter.
  let alreadyRemovedShield : Bool :=
    combat && recipientPerm?.any (fun o => g.shieldRemovedInCurrentCombatBatch o.id)
  let mut shieldRemoved := false
  let mut shieldRemoveCause : Option EventCause := none
  let mut curAmount := n
  let mut curApplied := applied
  let mut curCause := cause
  let mut curOrder := g.replacementOrder
  let mut choice? : Option (PlayerId × Array ReplacementId) := none
  let mut prevented := false
  let mut preventedAmt : Nat := 0
  if unpreventable then
    if let some o := recipientPerm? then
      if o.status.shield > 0 && !alreadyRemovedShield then
        let sid : ReplacementId := { kind := .shieldCounterPreventDamage, object := some o.id }
        curApplied := curApplied.push sid
        shieldRemoved := true
        shieldRemoveCause := g.wrapReplacedCause sid curCause (g.controllerOf o)
        curCause := shieldRemoveCause
  let mut fuel := 32
  while fuel > 0 do
    fuel := fuel - 1
    if curAmount <= 0 then
      fuel := 0
    else
      let mut items : Array ReplacementOrPrevention := #[]
      -- 1. Preventions (when damage is preventable)
      if !unpreventable then
        if let some src := src? then
          for gid in g.preventDamageGrantedBy src do
            if g.grantorStillInPlay gid then
              items := items.push (.prevention {
                id := { kind := .preventDamageGrantedBy, object := some src.id, grantor := some gid }
                source := some gid
                controller := (g.findObject? gid).bind g.controllerOf
                affectedPlayer := affected
                kind := .preventAllDamageFromSource src.id
              })
        if let some o := recipientPerm? then
          if let some src := src? then
            if g.frcProtectedFrom o src then
              items := items.push (.prevention {
                id := { kind := .protectionPreventDamage, object := some o.id }
                source := some o.id
                controller := g.controllerOf o
                affectedPlayer := affected
                kind := .protectionPreventDamage o.id src.id
              })
          if (g.staticAbilities o).any (· == .preventAllDamageToThis) then
            items := items.push (.prevention {
              id := { kind := .preventAllDamageToThis, object := some o.id }
              source := some o.id
              controller := g.controllerOf o
              affectedPlayer := affected
              kind := .preventAllDamageToPermanent o.id
            })
          let shieldId : ReplacementId := { kind := .shieldCounterPreventDamage, object := some o.id }
          if (o.status.shield > 0 || alreadyRemovedShield) && !shieldRemoved &&
              !curApplied.contains shieldId then
            items := items.push (.prevention {
              id := shieldId
              source := some o.id
              controller := g.controllerOf o
              affectedPlayer := affected
              kind := .shieldCounterPreventDamage o.id
            })
        if let some pid := recipientPlayer? then
          if g.protectionFromEverything pid then
            items := items.push (.prevention {
              id := { kind := .protectionFromEverythingPlayer, player := some pid }
              source := none
              controller := some pid
              affectedPlayer := pid
              kind := .protectionFromEverythingPlayer pid
            })
        for (_, eff) in g.activeEffects do
          match eff with
          | .prevention spec _ =>
            let matchesTarget : Bool :=
              match spec.kind with
              | .preventAllDamageToPermanent tid =>
                recipientPerm?.any (·.id == tid)
              | .preventAllDamageFromSource sid =>
                src?.any (·.id == sid)
              | .protectionPreventDamage tid sid =>
                recipientPerm?.any (·.id == tid) && src?.any (·.id == sid)
              | .protectionFromEverythingPlayer pid =>
                recipientPlayer? == some pid
              | .shieldCounterPreventDamage tid =>
                recipientPerm?.any (fun o => o.id == tid && (o.status.shield > 0 || alreadyRemovedShield)) &&
                  !shieldRemoved && !curApplied.contains spec.id
            if matchesTarget then
              items := items.push (.prevention { spec with affectedPlayer := affected })
          | _ => pure ()
      -- 2. Damage-increasing and damage-multiplying replacements
      if let some src := src? then
        -- Hawkeye, Young Avenger (`.noncombatDamagePlusSourcePower`)
        if !combat then
          match g.controllerOf src, recipientCtrl? with
          | some p, some r =>
            if p != r then
              for o in g.permanentsOf p do
                if (g.staticAbilities o).any (· == .noncombatDamagePlusSourcePower) then
                  let bonus := (g.power o).toNat
                  if bonus > 0 then
                    items := items.push (.replacement {
                      id := { kind := .noncombatDamagePlusSourcePower, object := some o.id }
                      source := some o.id
                      controller := some p
                      affectedPlayer := affected
                      kind := .addNoncombatDamage (some src.id) bonus
                    })
          | _, _ => pure ()
        -- Mjölnir (`.equippedDealsDoubleDamage`)
        for eq in g.battlefield do
          if eq.attachedTo == some src.id &&
              (g.staticAbilities eq).any (· == .equippedDealsDoubleDamage) then
            items := items.push (.replacement {
              id := { kind := .equippedDealsDoubleDamage, object := some eq.id }
              source := some eq.id
              controller := g.controllerOf eq
              affectedPlayer := affected
              kind := .multiplyDamage (some src.id) 2
            })
        -- Tomik, Izzet Sparkmage (`.fra .noncombatDamagePlusOne`)
        if !combat then
          match g.controllerOf src, recipientCtrl? with
          | some p, some r =>
            if p != r then
              for o in g.permanentsOf p do
                if (g.staticAbilities o).any (· == .fra .noncombatDamagePlusOne) then
                  items := items.push (.replacement {
                    id := { kind := .noncombatDamagePlusOne, object := some o.id }
                    source := some o.id
                    controller := some p
                    affectedPlayer := affected
                    kind := .addNoncombatDamage (some src.id) 1
                  })
          | _, _ => pure ()
      for (_, eff) in g.activeEffects do
        match eff with
        | .replacement spec _ =>
          match spec.kind with
          | .addNoncombatDamage sid bonus =>
            if !combat && (sid.isNone || src?.any (fun s => some s.id == sid)) && bonus > 0 then
              items := items.push (.replacement { spec with affectedPlayer := affected })
          | .multiplyDamage sid _ =>
            if sid.isNone || src?.any (fun s => some s.id == sid) then
              items := items.push (.replacement { spec with affectedPlayer := affected })
          | _ => pure ()
        | _ => pure ()
      let candidates := items.map ReplacementOrPrevention.toCandidate
      match g.selectNextReplacementStep candidates curApplied curOrder with
      | .none => fuel := 0
      | .needChoice chooser choices ord' =>
        curOrder := ord'
        choice? := some (chooser, choices)
        fuel := 0
      | .chosen chosen ord' =>
        curOrder := ord'
        match items.find? (fun it => it.replacementId == chosen.id) with
        | none => fuel := 0
        | some (.prevention pspec) =>
          curApplied := curApplied.push chosen.id
          curCause := g.wrapReplacedCause chosen.id curCause (some affected)
          if curAmount > 0 then
            preventedAmt := preventedAmt + curAmount.toNat
          curAmount := 0
          prevented := true
          match pspec.kind with
          | .shieldCounterPreventDamage _ =>
            if !alreadyRemovedShield then
              shieldRemoved := true
              shieldRemoveCause := curCause
          | _ => pure ()
        | some (.replacement rspec) =>
          curApplied := curApplied.push chosen.id
          curCause := g.wrapReplacedCause chosen.id curCause (some affected)
          match rspec.kind with
          | .addNoncombatDamage _ bonus =>
            curAmount := curAmount + Int.ofNat bonus
          | .multiplyDamage _ factor =>
            curAmount := curAmount * Int.ofNat factor
          | _ => pure ()
  return {
    amount := curAmount
    prevented := prevented
    preventedAmount := preventedAmt
    shieldRemoved := shieldRemoved
    shieldRemoveCause := shieldRemoveCause
    applied := curApplied
    cause := curCause
    choice? := choice?
  }

def markDamageOn (g : Game) (o : GameObject) (n : Int) (msg : String)
    (deathtouch := false) (combat := false) (unpreventable := false)
    (source : Option EventObject := none)
    (sourceObj : Option GameObject := none)
    (replaced : Option DamageReplacementResult := none)
    (applied : Array ReplacementId := #[])
    (consumeOrder : Bool := true)
    (cause : Option EventCause := none) : Game :=
  let srcSnap :=
    source.orElse (fun _ => sourceObj.map g.snapshotDamageSource)
      |>.orElse (fun _ => g.resolvingDamageSourceEvent?)
  if replaced.isNone && (match g.pending with | .chooseReplacement .. => true | _ => false) then
    g.chainPendingReplacement
      (.markDamageOn o.id n.toNat msg deathtouch srcSnap combat unpreventable cause)
  else
  let src? :=
    sourceObj.orElse (fun _ => g.damageSourceObjFromSnapshot? srcSnap)
      |>.orElse (fun _ => g.resolvingMovedDamageSource?)
  let rep :=
    replaced.getD
      (g.replaceDamage n (src? := src?) (srcEvent? := srcSnap) (recipientPerm? := some o)
        (combat := combat) (unpreventable := unpreventable) (applied := applied) (cause := cause))
  match rep.choice? with
  | some (chooser, choices) =>
    g.promptChooseReplacement chooser choices
      (.markDamageOn o.id n.toNat msg deathtouch srcSnap combat unpreventable cause)
  | none =>
  let g := if consumeOrder then g.consumeReplacementOrder rep.applied else g
  let srcEvent : EventObject :=
    let base := srcSnap.getD default
    { base with keywords := { base.keywords with deathtouch := base.keywords.deathtouch || deathtouch } }
  if n > 0 && !unpreventable && rep.prevented && !rep.shieldRemoved then
    let g :=
      if rep.preventedAmount > 0 then
        let prevCause :=
          g.resolveOptionalCause rep.cause (fallbackSrc := srcEvent.id)
            (fallbackCtrl := (src?.bind g.controllerOf).orElse (fun _ => g.controllerOf o))
        g.record (GameEvent.damagePrevented g.turnNumber srcEvent (.permanent (g.snapshot o))
          rep.preventedAmount prevCause)
      else g
    g.logMsg s!"Damage that would be dealt to {o.name} is prevented"
  else
  let cause := rep.cause
  let defaultCause :=
    cause.orElse (fun _ =>
      if n <= 0 then none
      else g.currentResolvingContext?.map fun (src, ctrl) => .oneShotEffect none src ctrl)
  g.withBatch defaultCause fun g =>
  let healsOther :=
    (g.staticAbilities o).any (fun
      | .healOtherDamageWhenDealt => true
      | _ => false)
  let dmgCause :=
    g.resolveOptionalCause cause (fallbackSrc := srcEvent.id) (fallbackCtrl := src?.bind g.controllerOf)
  let shieldCause :=
    g.resolveOptionalCause rep.shieldRemoveCause (fallbackCtrl := g.controllerOf o)
  let g :=
    if healsOther && n > 0 then
      g.record (GameEvent.damageMarkedCleared g.turnNumber #[o.id] (cause := dmgCause))
    else g
  let o := g.findObject? o.id |>.getD o
  let oName := g.name o
  if n > 0 && rep.shieldRemoved && !unpreventable then
    let g :=
      if rep.preventedAmount > 0 then
        g.record (GameEvent.damagePrevented g.turnNumber srcEvent (.permanent (g.snapshot o))
          rep.preventedAmount shieldCause)
      else g
    let g := g.record (GameEvent.counters g.turnNumber (g.controllerOf o) (g.snapshot o) .shield 1 true (cause := shieldCause))
    g.logMsg s!"A shield counter is removed from {oName} instead of damage"
  else if n > 0 && rep.shieldRemoved && unpreventable then
    let g := g.record (GameEvent.counters g.turnNumber (g.controllerOf o) (g.snapshot o) .shield 1 true (cause := shieldCause))
    let g := g.logMsg s!"A shield counter is removed from {oName} (unpreventable damage)"
    let marked := g.object! o.id
    let amt := rep.amount.toNat
    let g :=
      if amt > 0 then
        let happened := GameEvent.damaged g.turnNumber srcEvent (g.snapshot marked) amt combat (cause := dmgCause)
        let g := g.record happened |>.record (GameEvent.damageMarked g.turnNumber marked.id amt (cause := dmgCause))
        if g.isPlaneswalker marked then
          g.record (GameEvent.counters g.turnNumber none (g.snapshot marked) .loyalty amt true (cause := dmgCause))
        else g
      else g
    g.logMsg msg
  else
  -- CR 120.3c: damage dealt to a planeswalker removes that many loyalty counters.
  let n := rep.amount
  let happened := GameEvent.damaged g.turnNumber srcEvent (g.snapshot o) n.toNat combat (cause := dmgCause)
  let g := if n > 0 then g.record happened else g
  let g :=
    let g :=
      if n > 0 then
        g.record (GameEvent.damageMarked g.turnNumber o.id n.toNat (cause := dmgCause))
      else g
    let g :=
      if g.isPlaneswalker o && n > 0 then
        g.record (GameEvent.counters g.turnNumber none (g.snapshot o) .loyalty n.toNat true (cause := dmgCause))
      else g
    g.logMsg msg
  g

/-- Increase `p`'s life total (CR 119.3), running the CR 616.1 replacement loop
for any active `.modifyLifeGain` replacement effects. Gaining 0 life does
nothing (CR 119.9). -/
def gainLife (g : Game) (p : PlayerId) (n : Nat)
    (cause : Option EventCause := none) : Game :=
  if let .chooseReplacement .. := g.pending then
    g.chainPendingReplacement (.gainLife p n "" cause)
  else
  let propCause := g.resolveOptionalCause cause (fallbackCtrl := some p)
  let proposed := GameEvent.life g.turnNumber p n true (cause := propCause)
  if n == 0 || !proposed.watches .wouldGainLife then g
  else if (g.livingOpponents p).any (fun opp =>
      (g.permanentsOf opp.id).any (fun o =>
        (g.baseCard o).opponentsCantGainLife && g.retainsPrintedAbilities o)) then
    g.logMsg s!"{(g.player p).name} can't gain life"
  else
    let pl := g.player p
    if g.lifeLocked p || g.lifeCantChange p then
      g.logMsg s!"{pl.name}'s life total can't change"
    else
      let (n, applied, cause', choice?) :
          Nat × Array ReplacementId × Option EventCause × Option (PlayerId × Array ReplacementId) := Id.run do
        let mut curN := n
        let mut curApplied : Array ReplacementId := #[]
        let mut curCause := cause
        let mut curOrder := g.replacementOrder
        let mut choice? : Option (PlayerId × Array ReplacementId) := none
        let mut fuel := 32
        while fuel > 0 do
          fuel := fuel - 1
          if curN == 0 then
            fuel := 0
          else
            let mut specs : Array (ReplacementSpec × Nat × Nat) := #[]
            for (_, eff) in g.activeEffects do
              match eff with
              | .replacement spec _ =>
                match spec.kind with
                | .modifyLifeGain who add mult =>
                  if who == p then specs := specs.push (spec, add, mult)
                | _ => pure ()
              | _ => pure ()
            let candidates := specs.map (fun (s, _, _) => (ReplacementOrPrevention.replacement s).toCandidate)
            match g.selectNextReplacementStep candidates curApplied curOrder with
            | .none => fuel := 0
            | .needChoice chooser choices ord' =>
              curOrder := ord'
              choice? := some (chooser, choices)
              fuel := 0
            | .chosen chosen ord' =>
              curOrder := ord'
              match specs.find? (fun (s, _, _) => s.id == chosen.id) with
              | none => fuel := 0
              | some (_, add, mult) =>
                curN := curN * mult + add
                curApplied := curApplied.push chosen.id
                curCause := g.wrapReplacedCause chosen.id curCause (some p)
        return (curN, curApplied, curCause, choice?)
      match choice? with
      | some (chooser, choices) =>
        g.promptChooseReplacement chooser choices (.gainLife p n "" cause)
      | none =>
        let g := g.consumeReplacementOrder applied
        if n == 0 then g
        else
          let before := pl.life
          let finalCause := g.resolveOptionalCause cause' (fallbackCtrl := some p)
          let happened := GameEvent.life g.turnNumber p n true (cause := finalCause)
          (g.record happened).logMsg
            s!"{pl.name} gains {n} life ({before + (n : Int)} life)"

/-- Deal `n` damage to a creature and log the generic “is dealt” message. -/
def dealDamageToPermanent (g : Game) (o : GameObject) (n : Int)
    (source : Option EventObject := none)
    (cause : Option EventCause := none) : Game :=
  let srcEvent? := source.orElse (fun _ => g.resolvingDamageSourceEvent?)
  if let .chooseReplacement .. := g.pending then
    g.chainPendingReplacement
      (.dealDamageToPermanent o.id n.toNat srcEvent? false false cause)
  else
  let srcObj? :=
    (g.damageSourceObjFromSnapshot? srcEvent?).orElse (fun _ => g.resolvingMovedDamageSource?)
  let rep :=
    g.replaceDamage n (src? := srcObj?) (srcEvent? := srcEvent?) (recipientPerm? := some o)
      (cause := cause)
  match rep.choice? with
  | some (chooser, choices) =>
    g.promptChooseReplacement chooser choices
      (.dealDamageToPermanent o.id n.toNat srcEvent? false false cause)
  | none =>
    let g := g.consumeReplacementOrder rep.applied
    let dealtAmt := rep.amount
    let prevented := rep.prevented || g.preventsAllDamageTo o || o.status.shield > 0
    let defaultCause :=
      cause.orElse (fun _ =>
        if dealtAmt <= 0 && !rep.shieldRemoved then none
        else g.currentResolvingContext?.map fun (ctxSrc, ctrl) =>
          .oneShotEffect none
            (ctxSrc.orElse (fun _ => srcEvent?.bind (·.id)))
            (ctrl.orElse (fun _ => srcEvent?.bind (·.controller))))
    g.withBatch defaultCause fun g =>
    let g :=
      g.markDamageOn o n s!"{g.name o} is dealt {dealtAmt} damage"
        (source := srcEvent?) (sourceObj := srcObj?) (replaced := some rep) (cause := cause)
    -- CR 702.15b: damage dealt by a source with lifelink.
    match srcEvent?.bind (fun src => if src.keywords.lifelink then src.controller else none) with
    | some c =>
      if dealtAmt > 0 && !prevented then g.gainLife c dealtAmt.toNat (cause := cause) else g
    | none => g

/-- Deal `n` damage from a named source (fight, dies trigger, blocked trigger). -/
def dealDamageFrom (g : Game) (sourceName : String) (o : GameObject) (n : Int)
    (deathtouch := false) (source : Option GameObject := none)
    (sourceSnap : Option EventObject := none)
    (cause : Option EventCause := none) : Game :=
  let resolvedSrc? :=
    source.orElse (fun _ => g.damageSourceObjFromSnapshot? sourceSnap)
      |>.orElse (fun _ => g.resolvingMovedDamageSource?)
  if let .chooseReplacement .. := g.pending then
    let srcEvent :=
      (sourceSnap.map g.refreshOrKeepDamageSnapshot)
        |>.orElse (fun _ => resolvedSrc?.map g.snapshotDamageSource)
        |>.getD default
    g.chainPendingReplacement
      (.dealDamageFrom sourceName srcEvent o.id n.toNat deathtouch false false cause)
  else
  match resolvedSrc? with
  | some src =>
    let srcSnap :=
      (sourceSnap.map g.refreshOrKeepDamageSnapshot).getD (g.snapshotDamageSource src)
    let rep :=
      g.replaceDamage n (src? := some src) (srcEvent? := some srcSnap)
        (recipientPerm? := some o) (cause := cause)
    match rep.choice? with
    | some (chooser, choices) =>
      g.promptChooseReplacement chooser choices
        (.dealDamageFrom sourceName srcSnap o.id n.toNat deathtouch false false cause)
    | none =>
      let g := g.consumeReplacementOrder rep.applied
      if rep.prevented && !rep.shieldRemoved && !g.preventsAllDamageTo o then
        let g :=
          if rep.preventedAmount > 0 then
            let isLive := (g.findObject? src.id).isSome
            let srcEvent := if isLive then g.snapshot src else srcSnap
            let prevCause :=
              g.resolveOptionalCause rep.cause (fallbackSrc := srcEvent.id)
                (fallbackCtrl := (if isLive then g.controllerOf src else srcEvent.controller).orElse (fun _ => g.controllerOf o))
            g.record (GameEvent.damagePrevented g.turnNumber srcEvent (.permanent (g.snapshot o))
              rep.preventedAmount prevCause)
          else g
        g.logMsg s!"damage from {g.name src} is prevented"
      else
        let dealtAmt := rep.amount
        let prevented := rep.prevented || g.preventsAllDamageTo o || o.status.shield > 0
        let isLive := (g.findObject? src.id).isSome
        let srcCtrl? := if isLive then g.controllerOf src else srcSnap.controller
        let defaultCause :=
          cause.orElse (fun _ =>
            if dealtAmt <= 0 && !rep.shieldRemoved then none
            else g.currentResolvingContext?.map fun (ctxSrc, ctrl) =>
              .oneShotEffect none
                (ctxSrc.orElse (fun _ => some src.id))
                (ctrl.orElse (fun _ => srcCtrl?)))
        g.withBatch defaultCause fun g =>
        let isLive := (g.findObject? src.id).isSome
        let srcEvent := if isLive then g.snapshot src else srcSnap
        let hasDt := if isLive then g.hasDeathtouch src else srcEvent.keywords.deathtouch
        let hasLl := if isLive then g.hasLifelink src else srcEvent.keywords.lifelink
        let ctrl? := if isLive then g.controllerOf src else srcEvent.controller
        let g :=
          g.markDamageOn o n s!"{sourceName} deals {dealtAmt} damage to {g.name o}"
            (deathtouch || hasDt) (source := some srcEvent)
            (sourceObj := some src) (replaced := some rep) (cause := rep.cause)
        -- CR 702.15b: damage dealt by a source with lifelink.
        match ctrl? with
        | some c =>
          if dealtAmt > 0 && !prevented && hasLl then g.gainLife c dealtAmt.toNat (cause := cause) else g
        | none => g
  | none =>
    g.markDamageOn o n s!"{sourceName} deals {n} damage to {g.name o}" deathtouch (cause := cause)

/-- Deal `n` damage to a player and log the resulting life total (CR 120). -/
def dealDamageToPlayer (g : Game) (pid : PlayerId) (n : Int)
    (preventable := true) (source : Option GameObject := none)
    (sourceSnap : Option EventObject := none)
    (cause : Option EventCause := none) : Game :=
  let source :=
    source.orElse (fun _ => g.damageSourceObjFromSnapshot? sourceSnap)
      |>.orElse (fun _ => g.resolvingMovedDamageSource?)
  let srcSnap :=
    (sourceSnap.map g.refreshOrKeepDamageSnapshot)
      |>.orElse (fun _ => source.map g.snapshotDamageSource)
      |>.orElse (fun _ => g.resolvingDamageSourceEvent?)
  let pl := g.player pid
  if let .chooseReplacement .. := g.pending then
    let msg := s!"{pl.name} is dealt {n} damage"
    g.chainPendingReplacement
      (.dealDamageToPlayer pid n.toNat msg srcSnap false (!preventable) cause)
  else
  let rep :=
    g.replaceDamage n (src? := source) (srcEvent? := srcSnap) (recipientPlayer? := some pid)
      (unpreventable := !preventable) (cause := cause)
  match rep.choice? with
  | some (chooser, choices) =>
    let msg := s!"{pl.name} is dealt {n} damage"
    g.promptChooseReplacement chooser choices
      (.dealDamageToPlayer pid n.toNat msg srcSnap false (!preventable) cause)
  | none =>
  let g := g.consumeReplacementOrder rep.applied
  let recordPlayerPrevented (g : Game) : Game :=
    if rep.preventedAmount > 0 then
      let srcEvent :=
        ((srcSnap.map g.refreshOrKeepDamageSnapshot)
          |>.orElse (fun _ => source.map g.snapshotDamageSource)
          |>.orElse (fun _ => g.resolvingDamageSourceEvent?)).getD default
      let prevCause :=
        g.resolveOptionalCause rep.cause (fallbackSrc := srcEvent.id)
          (fallbackCtrl := (source.bind (fun src =>
            if (g.findObject? src.id).isSome then g.controllerOf src else srcEvent.controller)).orElse
            (fun _ => srcEvent.controller.orElse (fun _ => some pid)))
      g.record (GameEvent.damagePrevented g.turnNumber srcEvent (.player pid)
        rep.preventedAmount prevCause)
    else g
  if rep.prevented && preventable && g.protectionFromEverything pid &&
      !(source.any (fun src => (g.preventDamageGrantedBy src).any g.grantorStillInPlay)) then
    (recordPlayerPrevented g).logMsg s!"damage to {pl.name} is prevented (protection from everything)"
  else if (rep.prevented || rep.amount == 0) && source.isSome then
    (recordPlayerPrevented g).logMsg s!"damage from the source is prevented"
  else if rep.prevented then
    (recordPlayerPrevented g).logMsg s!"damage to {pl.name} is prevented"
  else
    let n := rep.amount
    let defaultCause :=
      cause.orElse (fun _ =>
        if n <= 0 then none
        else g.currentResolvingContext?.map fun (ctxSrc, ctrl) =>
          .oneShotEffect none
            (ctxSrc.orElse (fun _ => source.map (·.id)))
            (ctrl.orElse (fun _ =>
              (source.bind (fun src =>
                if (g.findObject? src.id).isSome then g.controllerOf src
                else srcSnap.bind (·.controller))).orElse (fun _ => srcSnap.bind (·.controller)))))
    g.withBatch defaultCause fun g =>
    let srcEvent :=
      ((srcSnap.map g.refreshOrKeepDamageSnapshot)
        |>.orElse (fun _ => source.map g.snapshotDamageSource)
        |>.orElse (fun _ => g.resolvingDamageSourceEvent?)).getD default
    let dmgCause :=
      g.resolveOptionalCause rep.cause (fallbackSrc := srcEvent.id)
        (fallbackCtrl := (source.bind (fun src =>
          if (g.findObject? src.id).isSome then g.controllerOf src else srcEvent.controller)).orElse
          (fun _ => srcEvent.controller))
    let happened := GameEvent.damagedPlayer g.turnNumber srcEvent pid n.toNat false (cause := dmgCause)
    let g := if n > 0 then g.record happened else g
    let g :=
      if (g.lifeLocked pid || g.lifeCantChange pid) && n != 0 then
        g.logMsg s!"{pl.name}'s life total can't change"
      else if n > 0 then
        (g.record (GameEvent.life g.turnNumber pid n.toNat false true false (cause := dmgCause))).logMsg
          s!"{pl.name} is dealt {n} damage ({pl.life - n} life)"
      else
        g.logMsg s!"{pl.name} is dealt {n} damage ({pl.life - n} life)"
    -- CR 702.15b: damage dealt by a source with lifelink (including departed LKI, CR 113.7a).
    let lifelinkCtrl? : Option PlayerId :=
      match source with
      | some src =>
        if (g.findObject? src.id).isSome then
          if g.hasLifelink src then g.controllerOf src else none
        else
          if srcEvent.keywords.lifelink then srcEvent.controller else none
      | none => if srcEvent.keywords.lifelink then srcEvent.controller else none
    match lifelinkCtrl? with
    | some c => if n > 0 then g.gainLife c n.toNat (cause := cause) else g
    | none => g

/-- Deal `n` damage to each living player in `players`, stopping if a replacement
choice opens so the remaining players resume after the choice is answered. -/
def dealDamageToPlayers (g : Game) (players : Array PlayerId) (n : Int)
    (source : Option GameObject := none)
    (sourceSnap : Option EventObject := none)
    (cause : Option EventCause := none) : Game :=
  let source :=
    source.orElse (fun _ => g.damageSourceObjFromSnapshot? sourceSnap)
      |>.orElse (fun _ => g.resolvingMovedDamageSource?)
  let srcSnap :=
    (sourceSnap.map g.refreshOrKeepDamageSnapshot)
      |>.orElse (fun _ => source.map g.snapshotDamageSource)
      |>.orElse (fun _ => g.resolvingDamageSourceEvent?)
  if let .chooseReplacement .. := g.pending then
    g.chainPendingReplacement (.dealDamageToPlayers players n.toNat srcSnap cause)
  else
  g.withBatch cause fun g => Id.run do
    let mut g := g
    let c := cause.orElse (fun _ => g.currentBatch.bind (·.2))
    for i in [0:players.size] do
      let pid := players[i]!
      if !(g.player pid).lost then
        g := g.dealDamageToPlayer pid n (source := source) (sourceSnap := srcSnap) (cause := c)
        if let .chooseReplacement .. := g.pending then
          let rem := players.extract (i + 1) players.size
          if !rem.isEmpty then
            g := g.chainPendingReplacement
              (.dealDamageToPlayers rem n.toNat srcSnap c)
          return g
    return g

/-- Deal `n` damage to each opponent of `controller` under a single shared
`.oneShotEffect` cause when resolving (CR 120 / 610.1). -/
def dealDamageToEachOpponent (g : Game) (controller : PlayerId) (n : Int)
    (source : Option GameObject := none)
    (cause : Option EventCause := none) : Game :=
  let source := source.orElse (fun _ => g.resolvingMovedDamageSource?)
  let defaultCause :=
    cause.orElse (fun _ =>
      if n <= 0 || (g.livingOpponents controller).isEmpty then none
      else g.currentResolvingContext?.map fun (ctxSrc, ctrl) =>
        .oneShotEffect none
          (ctxSrc.orElse (fun _ => source.map (·.id)))
          (ctrl.orElse (fun _ => some controller)))
  g.dealDamageToPlayers ((g.livingOpponents controller).map (·.id)) n
    (source := source) (cause := defaultCause)

/-- Deal this creature's power as damage to `dest` (one side of a fight). -/
def dealFightDamage (g : Game) (src dest : GameObject)
    (cause : Option EventCause := none) : Game :=
  g.dealDamageFrom (g.name src) dest (g.power src).toNat (source := some src) (cause := cause)

/-- Both sides of a fight deal damage simultaneously-looking: `src` first,
then `dest` if both are still in play. -/
def fightCreatures (g : Game) (src dest : GameObject)
    (cause : Option EventCause := none) : Game :=
  let defaultCause :=
    cause.orElse (fun _ =>
      g.currentResolvingContext?.map fun (ctxSrc, ctrl) =>
        .oneShotEffect none
          (ctxSrc.orElse (fun _ => some src.id))
          (ctrl.orElse (fun _ => g.controllerOf src)))
  g.withBatch defaultCause fun g =>
  let c := cause.orElse (fun _ => g.currentBatch.bind (·.2))
  let g := g.dealFightDamage src dest (cause := c)
  if let .chooseReplacement .. := g.pending then
    g.chainPendingReplacement (.dealFightDamage dest.id src.id c)
  else
    match g.findObject? dest.id, g.findObject? src.id with
    | some dest, some src => g.dealFightDamage dest src (cause := c)
    | _, _ => g

/-- Decrease `p`'s life total (CR 119.3). Losing 0 life does nothing
(CR 119.3). Loss of life is not damage (CR 119.3 / 120.3). -/
def loseLife (g : Game) (p : PlayerId) (n : Nat)
    (cause : Option EventCause := none) : Game :=
  if n == 0 then g
  else
    let pl := g.player p
    if g.lifeLocked p || g.lifeCantChange p then
      g.logMsg s!"{pl.name}'s life total can't change"
    else
      let effCause := g.resolveOptionalCause cause (fallbackCtrl := some p)
      (g.record (GameEvent.life g.turnNumber p n false (cause := effCause))).logMsg
        s!"{pl.name} loses {n} life ({pl.life - (n : Int)} life)"

/-- Set `p`'s life total to `life` and log `msg` (CR 119.5): if `life` is
greater than `p`'s current life total, `p` gains the difference via `gainLife`;
if less, `p` loses the difference. -/
def setLife (g : Game) (p : PlayerId) (life : Int) (msg : String)
    (cause : Option EventCause := none) : Game :=
  let pl := g.player p
  if g.lifeLocked p || g.lifeCantChange p then
    g.logMsg msg
  else if life > pl.life then
    (g.gainLife p (life - pl.life).toNat (cause := cause)).logMsg msg
  else if life < pl.life then
    let effCause := g.resolveOptionalCause cause (fallbackCtrl := some p)
    (g.record (GameEvent.life g.turnNumber p (pl.life - life).toNat false (cause := effCause))).logMsg msg
  else
    g.logMsg msg

/-- Each opponent of `controller` loses `n` life under one shared
`.oneShotEffect` cause when resolving (CR 119.3 / 610.1). -/
def loseLifeEachOpponent (g : Game) (controller : PlayerId) (n : Nat)
    (cause : Option EventCause := none) : Game :=
  let defaultCause :=
    cause.orElse (fun _ =>
      if n == 0 || (g.livingOpponents controller).isEmpty then none
      else g.currentResolvingContext?.map fun (src, ctrl) =>
        .oneShotEffect none src (ctrl.orElse (fun _ => some controller)))
  g.withBatch defaultCause fun g =>
  g.forEachOpponent controller (fun g pid => g.loseLife pid n (cause := cause))

/-- Each opponent of `controller` loses `n` life and `controller` gains `n`
life under one shared `.oneShotEffect` cause when resolving (CR 119 / 610.1). -/
def eachOpponentLosesYouGain (g : Game) (controller : PlayerId) (n : Nat)
    (cause : Option EventCause := none) : Game :=
  let defaultCause :=
    cause.orElse (fun _ =>
      if n == 0 then none
      else g.currentResolvingContext?.map fun (src, ctrl) =>
        .oneShotEffect none src (ctrl.orElse (fun _ => some controller)))
  g.withBatch defaultCause fun g =>
  let g := g.forEachOpponent controller (fun g pid => g.loseLife pid n (cause := cause))
  g.gainLife controller n (cause := cause)

/-- Draw `cards`, then lose `life` (Night's Whisper, MSH draw-and-lose). -/
def drawThenLoseLife (g : Game) (p : PlayerId) (cards life : Nat) : Game :=
  let defaultCause :=
    g.currentResolvingContext?.map fun (src, ctrl) =>
      .oneShotEffect none src (ctrl.orElse (fun _ => some p))
  if let .chooseReplacement .. := g.pending then
    let g := g.chainPendingReplacement (.draw p cards false defaultCause)
    g.chainPendingReplacement (.loseLifeAfterDraw p life defaultCause)
  else
    g.withBatch defaultCause fun g =>
      let g := g.draw p cards (cause := defaultCause)
      if let .chooseReplacement .. := g.pending then
        g.chainPendingReplacement (.loseLifeAfterDraw p life defaultCause)
      else
        g.loseLife p life (cause := defaultCause)

/-- If a shuffle is waiting for a `--norandom` result, leave it. Otherwise
run a stored draw or life-gain after-action. -/
def continueIfShuffled (g : Game) : Game :=
  match g.pendingRandom? with
  | some _ => g
  | none =>
    let after := g.afterRandom
    let g := g.change (.afterRandom .none)
    match after with
    | .draw p n => g.draw p n
    | .gainLife p n => g.gainLife p n
    | other => g.change (.afterRandom other)

/-- Deal `n` damage to an already-legal player or permanent target. -/
def dealDamageToTarget (g : Game) (t : Target) (n : Int)
    (source : Option GameObject := none)
    (cause : Option EventCause := none) : Game :=
  -- The source is the resolving spell, or the source of the resolving
  -- ability (CR 609.7 / 113.7); departed sources are resolved via LKI inside
  -- `dealDamageToPlayer` / `dealDamageToPermanent` (CR 113.7a).
  let src := source.orElse (fun _ => g.resolvingDamageSource?)
  match t with
  | Target.player pid => g.dealDamageToPlayer pid n (source := src) (cause := cause)
  | Target.permanent oid =>
    match g.findObject? oid with
    | some o =>
      match src with
      | some s => g.dealDamageFrom s.name o n (source := some s) (cause := cause)
      | none => g.dealDamageToPermanent o n (cause := cause)
    | none => g.logMsg "The target is no longer in play"
  | Target.card _ => g.logMsg "The target is no longer legal"

/-- Total damage dealt to permanent `oid` recorded in `g.events[startIdx:]`
(CR 120.2 / 120.10). -/
def damageDealtToPermanentSince (g : Game) (oid : ObjectId) (startIdx : Nat) : Nat := Id.run do
  let mut total : Nat := 0
  for i in [startIdx : g.events.size] do
    if let .rules (.damage (.dealt pkts)) := g.events[i]!.change then
      for pkt in pkts do
        match pkt.recipient with
        | .permanent eo | .battle eo =>
          if eo.id == some oid then total := total + pkt.amount
        | .player _ => pure ()
  return total

/-- Lethal damage threshold of `o` before dealing damage (CR 120.4a; ruling 790):
remaining toughness for a creature, loyalty for a planeswalker, and the greater
of the two when it is both. -/
def lethalDamageThreshold (g : Game) (o : GameObject) : Nat :=
  let creatureLethal :=
    if g.isCreature o then (g.toughness o - o.status.damage).toNat else 0
  let loyalty := if g.isPlaneswalker o then o.status.loyaltyCounters else 0
  Nat.max creatureLethal loyalty

end Game
end Mtg.Engine
