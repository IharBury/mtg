import Mtg.Engine.Game.PowerToughness

/-!
# Object allocation

Fresh object ids and timestamps, materializing new `GameObject`s, and
putting spells and activated abilities on the stack (CR 405).
-/

namespace Mtg.Engine
namespace Game

/-- Materialize a new object identity and timestamp via `EngineChange.materializeObject`
without emitting `ZoneEvent.created` (CR 103.2 / 114 / 405 / 602.2a). -/
def allocObject (g : Game) (printed : CardDef) (owner : PlayerId) (zone : Zone)
    (controller : Option PlayerId := none) (status : Status := {})
    (abilityEffect : Option Effect := none)
    (triggeredAbility : Option TriggeredAbility := none)
    (sourceId : Option ObjectId := none)
    (attachedTo : Option ObjectId := none)
    (adventurerCard : Option CardDef := none)
    (isCommander : Bool := false) : Game × GameObject :=
  let id : ObjectId := ⟨g.nextObjectId⟩
  let ts : Nat := g.timestamp + 1
  let obj : GameObject := {
    id, printed, owner, controller, zone, status,
    timestamp := ts,
    abilityEffect, triggeredAbility, sourceId,
    attachedTo := if zone == .battlefield then attachedTo else none,
    adventurerCard,
    isCommander,
    defaultController := if zone == .battlefield then controller else none
  }
  let g := g.change (.materializeObject obj)
  (g, g.object! id)

/-- Push a stack entry for an already-allocated object (CR 601.2a / 602.2a / 603.3). -/
def putStackEntry (g : Game) (controller : PlayerId) (objectId : ObjectId)
    (delayedTrigger : Option (DelayedTriggerKind × EventCause) := none)
    (lastKnownPower : Option Int := none)
    (lastKnownToughness : Option Int := none) : Game :=
  g.changes #[
    .pushStack { objectId, controller, targets := #[], delayedTrigger, lastKnownPower, lastKnownToughness },
    .consecutivePasses 0]

/-- Allocate a stack object representing an activated or triggered ability of
`source` (CR 602.2a / 603.3). -/
def allocStackAbility (g : Game) (source : GameObject) (controller : PlayerId)
    (abilityEffect : Option Effect := none)
    (triggeredAbility : Option TriggeredAbility := none) : Game × GameObject :=
  g.allocObject
    { name := s!"{source.name}'s ability", types := #[] }
    source.owner .stack (some controller)
    (abilityEffect := abilityEffect) (triggeredAbility := triggeredAbility)
    (sourceId := some source.id)

/-- Allocate a stack ability of `source` and push it onto the stack. -/
def putStackAbility (g : Game) (source : GameObject) (controller : PlayerId)
    (abilityEffect : Option Effect := none)
    (triggeredAbility : Option TriggeredAbility := none)
    (lastKnownPower : Option Int := none)
    (lastKnownToughness : Option Int := none)
    (delayedTrigger : Option (DelayedTriggerKind × EventCause) := none) : Game × GameObject :=
  let (g, obj) := g.allocStackAbility source controller abilityEffect triggeredAbility
  (g.putStackEntry controller obj.id delayedTrigger lastKnownPower lastKnownToughness, obj)

/-- The copy of `srcId`'s prepare spell in exile, if any. -/
def preparedCopyOf? (g : Game) (srcId : ObjectId) : Option GameObject :=
  g.objects.find? (fun o =>
    o.zone == .exile && ((g.playPermission o).bind (·.prepareSource)) == some srcId)

/-- Create the exiled copy of `o`'s prepare spell and grant permission to cast
it while `o` remains prepared (ruling 742). -/
def createPreparedCopy (g : Game) (o : GameObject) (face : AdventureFace)
    (cause : Option EventCause := none) : Game :=
  let p := (g.controllerOf o).getD o.owner
  let copyId : ObjectId := ⟨g.nextObjectId⟩
  let copyTs := g.timestamp + 1
  let copyObj : GameObject := {
    id := copyId
    printed := face.toCardDef
    owner := p
    zone := .exile
    timestamp := copyTs
    isCopy := true
  }
  let resolvedCause := g.resolveOptionalCause cause (fallbackSrc := some o.id) (fallbackCtrl := some p)
  let g := g.record (GameEvent.created g.turnNumber p (g.snapshot copyObj) (cause := resolvedCause))
  g.createEffect (.playPermission copyId {
    player := p
    whileExiled := true
    prepareSource := some o.id }) (cause := some resolvedCause)

/-- Ensure the exiled copy of `o`'s prepare spell exists when `o` enters
already prepared (CR 614.1c, ruling 742). -/
def ensurePreparedCopy (g : Game) (o : GameObject) : Game :=
  if !o.status.prepared || (g.preparedCopyOf? o.id).isSome then g
  else
    match (g.baseCard o).prepareFace with
    | none => g
    | some face =>
      let g := g.createPreparedCopy o face (cause := some (.gameRule .staticAbility))
      g.logMsg s!"{o.name} becomes prepared. A copy of {face.name} is exiled"

/-- Karn, Argent Defender: an artifact or creature entering doesn't cause
abilities to trigger. Checked with the permanent as it exists on the
battlefield (rulings 891–893). Replacement effects still apply (ruling 890). -/
def enteringCausesNoTriggers (g : Game) (o : GameObject) : Bool :=
  (g.isCreature o || (g.types o).contains .artifact) &&
    g.battlefield.any (fun src =>
      (g.staticAbilities src).any (fun
        | .enteringArtifactsCreaturesDontTrigger => true
        | _ => false))

/-- CR 306.5b: a planeswalker enters with loyalty counters equal to its
printed loyalty (placed in `entersWith` during the zone change). -/
def enterWithLoyalty (g : Game) (o : GameObject) : Game :=
  if o.status.faceDown then g
  else
    let bc := g.baseCard o
    match g.isPlaneswalker o, bc.loyalty with
    | true, some n =>
      if n > 0 && o.status.loyaltyCounters > 0 then
        let k := o.status.loyaltyCounters
        g.logMsg s!"{g.name o} enters with {k} loyalty counter(s)"
      else g
    | _, _ => g

/-- Reconstruct the applied CR 616.1 `ReplacementId` order and pre-arrival
battlefield snapshot for `oid`'s latest battlefield arrival event in `g.events`,
so post-entry `entersWith` counter logging reproduces player-chosen replacement
orders and CR 614.12 simultaneous-entry isolation after `consumeReplacementOrder`
has cleared `g.replacementOrder`. -/
private def arrivalCounterContext (g : Game) (oid : ObjectId) :
    Array ReplacementId × Option (Array GameObject) := Id.run do
  let isBfArrivalOf (ev : GameEvent) (pid : ObjectId) : Bool :=
    match ev.change with
    | .rules (.zone (.moved _ after _ .battlefield ..)) => after.id == some pid
    | .rules (.zone (.created snap _)) => snap.id == some pid && snap.zone == .battlefield
    | .engine (.materializeObject obj _) => obj.id == pid && obj.zone == .battlefield
    | _ => false
  let mut found? : Option (Nat × EventCause × Option BatchId) := none
  let mut idx := g.events.size
  while idx > 0 do
    idx := idx - 1
    let ev := g.events[idx]!
    match ev with
    | .rules _ (.zone (.moved _ after _ .battlefield ..)) cause batch =>
      if after.id == some oid then
        found? := some (idx, cause, batch)
        break
    | .rules _ (.zone (.created snap _)) cause batch =>
      if snap.id == some oid && snap.zone == .battlefield then
        found? := some (idx, cause, batch)
        break
    | _ => pure ()
  match found? with
  | none => return (g.replacementOrder, none)
  | some (arrIdx, arrCause, arrBatch?) =>
    let coOrLater (pid : ObjectId) : Bool := Id.run do
      for j in [0:g.events.size] do
        let ev := g.events[j]!
        if isBfArrivalOf ev pid &&
            (j >= arrIdx || (arrBatch?.isSome && ev.batch == arrBatch?)) then
          return true
      return false
    let preBf := g.battlefield.filter (fun pObj => pObj.id != oid && !coOrLater pObj.id)
    return (arrCause.replacedBy, some preBf)

/-- “This creature enters with N +1/+1 counters on it” (placed in `entersWith`
during the zone change). -/
def enterWithPlusOnes (g : Game) (o : GameObject) : Game :=
  if o.status.faceDown || !g.retainsPrintedAbilities o then g
  else
    let base := (g.baseCard o).entersWithPlusOneCounters
    if base == 0 || o.status.plusOnePlusOne == 0 then g
    else
      let (arrivalOrder, preBf?) := g.arrivalCounterContext o.id
      let (n, _, _) :=
        g.replaceCountersPut o .plusOnePlusOne base (putter := g.controllerOf o)
          (entersWith := true) (entering := some o)
          (order := arrivalOrder) (preBattlefield := preBf?)
      if n == 0 then g
      else g.logMsg s!"{g.name o} enters with {n} +1/+1 counter(s)"

def enterWithIndestructibleCounter (g : Game) (o : GameObject) : Game :=
  if !o.status.faceDown && g.retainsPrintedAbilities o &&
      (g.baseCard o).entersWithIndestructibleCounter &&
      o.status.indestructibleCounters > 0 then
    let phrase := CounterKind.indestructible.countersPhrase o.status.indestructibleCounters
    g.logMsg s!"{g.name o} enters with {phrase}"
  else g

def enterWithShield (g : Game) (o : GameObject) : Game :=
  if o.status.faceDown || !g.retainsPrintedAbilities o then g
  else
    let base := (g.baseCard o).entersWithShield
    if base == 0 || o.status.shield == 0 then g
    else
      let n := o.status.shield
      g.logMsg s!"{g.name o} enters with {n} shield counter(s)"

def enterWithXPlusOnes (g : Game) (o : GameObject) : Game :=
  if !o.status.faceDown && (g.staticAbilities o).any (fun
      | .entersWithXPlusOne => true
      | _ => false) && o.status.plusOnePlusOne > 0 then
    let (arrivalOrder, preBf?) := g.arrivalCounterContext o.id
    let (n, _, _) :=
      g.replaceCountersPut o .plusOnePlusOne ((g.chosenXOf? o.id).getD 0) (putter := g.controllerOf o)
        (entersWith := true) (entering := some o)
        (order := arrivalOrder) (preBattlefield := preBf?)
    if n == 0 then g
    else g.logMsg s!"{g.name o} enters with {n} +1/+1 counter(s)"
  else g

def enterWithHope (g : Game) (o : GameObject) : Game :=
  if !o.status.faceDown && g.retainsPrintedAbilities o &&
      (g.baseCard o).entersWithHopePerCreature && o.status.hope > 0 then
    g.logMsg s!"{g.name o} enters with {o.status.hope} hope counter(s)"
  else g

/-- Counters and statuses a permanent enters with (CR 614.1c / 614.12):
loyalty, +1/+1, indestructible, shield, X +1/+1, prepared, and hope. The
counters and `prepared` status are placed in `moved.after` / `created.object`
and `entersWith` during the atomic zone change; this step logs the entry
effects, queues loyalty-put triggers, and creates the exiled prepare copy. -/
def applyEntersWith (g : Game) (o : GameObject) : Game :=
  let id := o.id
  let g := g.enterWithLoyalty (g.object! id)
  let g := g.enterWithPlusOnes (g.object! id)
  let g := g.enterWithIndestructibleCounter (g.object! id)
  let g := g.enterWithShield (g.object! id)
  let g := g.enterWithXPlusOnes (g.object! id)
  let g := g.ensurePreparedCopy (g.object! id)
  g.enterWithHope (g.object! id)

/-- As a Saga enters, put a lore counter on it (CR 714.3a). The lore counter(s)
are placed in `entersWith` during the zone change, so we log the lore
counter(s) on `o`. -/
def addLoreAsSagaEnters (g : Game) (o : GameObject) : Game :=
  match g.controllerOf o, (g.baseCard o).saga with
  | some _, some _ =>
    if o.status.faceDown || o.status.lore == 0 then g
    else
      let oName := g.name o
      Id.run do
        let mut g := g
        for i in [0:o.status.lore] do
          let lore := i + 1
          g := g.logMsg s!"{oName} gets a lore counter ({lore})"
        return g
  | _, _ => g

/-- Batch-scoped post-entry effects (`applyEntersWith`, `addLoreAsSagaEnters`,
and Karn's trigger-suppression log) without prompting stack-placement trigger
targets yet (used inside simultaneous-entry batches such as `runLinkedExileBatch`). -/
def afterPermanentEntersInBatch (g : Game) (o : GameObject) : Game :=
  match g.findObject? o.id with
  | none => g
  | some cur =>
    if !cur.isOnBattlefield then
      if let .chooseReplacement .. := g.pending then
        g.chainPendingReplacement (.afterLastPermanentEnters (some o.id))
      else g
    else
      let g := g.applyEntersWith (g.object! o.id)
      let o := g.object! o.id
      let g := g.addLoreAsSagaEnters o
      let o := g.object! o.id
      if g.enteringCausesNoTriggers o then
        g.logMsg s!"{g.name o} entering doesn't cause abilities to trigger"
      else g

end Game
end Mtg.Engine
