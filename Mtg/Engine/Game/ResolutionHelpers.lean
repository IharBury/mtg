import Mtg.Engine.Game.LibrarySearch

/-!
# Resolution target helpers (CR 608.2b)

Re-checking target legality as an effect resolves, direct permanent helpers,
beginning scry, mill (CR 701.17), and damage to each matching creature.
-/

namespace Mtg.Engine
namespace Game

/-- Log why a targeted ability failed to affect its announced target (CR 608.2b). -/
def illegalAbilityTarget (g : Game) : Target → Game
  | Target.player _ => g.logMsg "The target is no longer legal"
  | Target.permanent oid =>
    match g.findObject? oid with
    | some o =>
      if o.isOnBattlefield then g.logMsg "The target is no longer legal"
      else g.logMsg "The target is no longer in play"
    | none => g.logMsg "The target is no longer in play"
  | Target.card oid =>
    match g.findObject? oid with
    | some o =>
      match o.zone with
      | .graveyard _ => g.logMsg "The target is no longer legal"
      | _ => g.logMsg "The target is no longer in the graveyard"
    | none => g.logMsg "The target is no longer in the graveyard"

/-- Apply `f` when the announced target is still in `legal` (CR 608.2b).
`missing` is logged when no target was announced; `none` leaves the game unchanged. -/
def withLegalTarget (g : Game) (legal : Array Target) (targets : Array Target)
    (f : Game → Target → Game) (missing : Option String := none) : Game :=
  match targets[0]? with
  | none =>
    match missing with
    | some msg => g.logMsg msg
    | none => g
  | some t =>
    if legal.contains t then f g t else g.illegalAbilityTarget t

/-- Apply `f` to a still-legal permanent target. -/
def withLegalPermanentTarget (g : Game) (legal : Array Target) (targets : Array Target)
    (f : Game → GameObject → Game) (missing : Option String := none) : Game :=
  g.withLegalTarget legal targets (fun g t =>
    match t with
    | Target.permanent oid =>
      match g.findObject? oid with
      | none => g.logMsg "The target is no longer in play"
      | some o => f g o
    | Target.player _ | Target.card _ => g.logMsg "The target is no longer legal")
    missing

/-- Apply `f` when the announced target is still legal for `spec` (CR 608.2b / 115.5). -/
def withLegalSpecTarget (g : Game) (controller : PlayerId) (spec : TargetSpec)
    (targets : Array Target) (f : Game → Target → Game)
    (sourceId : Option ObjectId := none) (missing : Option String := none) : Game :=
  let stackSelf := g.resolvingAbility.orElse (fun _ => g.resolvingSpell)
  g.withLegalTarget (g.legalTargetsForSpec controller spec sourceId stackSelf) targets f missing

/-- Apply `f` to a still-legal permanent target of `spec`. -/
def withLegalSpecPermanent (g : Game) (controller : PlayerId) (spec : TargetSpec)
    (targets : Array Target) (f : Game → GameObject → Game)
    (sourceId : Option ObjectId := none) (missing : Option String := none) : Game :=
  let stackSelf := g.resolvingAbility.orElse (fun _ => g.resolvingSpell)
  g.withLegalPermanentTarget (g.legalTargetsForSpec controller spec sourceId stackSelf) targets f
    missing

/-- Apply `f` to a still-legal player target of `spec`. -/
def withLegalSpecPlayer (g : Game) (controller : PlayerId) (spec : TargetSpec)
    (targets : Array Target) (f : Game → PlayerId → Game)
    (sourceId : Option ObjectId := none) (missing : Option String := none) : Game :=
  g.withLegalSpecTarget controller spec targets (fun g tgt =>
    match tgt with
    | Target.player pid => f g pid
    | Target.permanent _ | Target.card _ => g.logMsg "The target is no longer legal")
    sourceId missing

/-- Whether `t` is still a legal target for the `i`th instance of “target”
of `spec` (CR 608.2b), accounting for `g.resolvingSkippedSlots` when optional
slots were skipped at announcement. -/
def targetLegalAt (g : Game) (controller : PlayerId) (spec : TargetSpec) (i : Nat)
    (t : Target) (sourceId : Option ObjectId) : Bool :=
  let pos :=
    if g.resolvingSkippedSlots.isEmpty || !spec.isMultiSlot then i
    else Id.run do
      let mut s := 0
      let mut rem := i
      let total := spec.totalPositions
      while s < total do
        if g.resolvingSkippedSlots.contains s then
          s := s + 1
        else if rem == 0 then
          return s
        else
          rem := rem - 1
          s := s + 1
      return s
  let stackSelf := g.resolvingAbility.orElse (fun _ => g.resolvingSpell)
  (g.legalTargetsForSlot controller (spec.slotAtPos pos) sourceId stackSelf).contains t

/-- The source's name for effect and damage logs. -/
def effectSourceName (g : Game) (sourceId : Option ObjectId) : String :=
  match g.resolvingSpell.bind g.findLiveSourceObject? with
  | some o => g.name o
  | none =>
    match sourceId.bind g.findLiveSourceObject? with
    | some o => g.name o
    | none =>
      ((sourceId.bind g.damageSourceById?).map g.name).orElse
        (fun _ => (sourceId.bind g.lastKnownBefore?).map (·.name))
        |>.getD "The effect"

/-- The resolving activated or triggered ability's stack object. -/
def resolvingAbilityObject? (g : Game) : Option GameObject :=
  g.resolvingAbility.bind g.findObject?

/-- Put `o` on the top (`top`) or bottom of its owner's library, deferring the
log across `Pending.chooseReplacement` and emitting it only if `o` actually
arrives in `.library owner`. -/
def putOnOwnerLibrary (g : Game) (o : GameObject) (top : Bool) : Game :=
  let side := if top then "top" else "bottom"
  let name := g.name o
  let owner := o.owner
  let pos : LibraryPosition := if top then .top else .bottom
  let (g, _) := g.move o.id (.library owner) none (libraryPosition := some pos)
  if let .chooseReplacement .. := g.pending then
    g.chainPendingReplacement (.finishPostStep (.logPutOnOwnerLibrary o.id owner name top))
  else if (g.followMovedToZone? o.id (· == .library owner)).isSome then
    g.logMsg s!"{(g.player owner).name} puts {name} on the {side} of their library"
  else g

/-- Untap permanent `o` during resolution, respecting replacement pauses and
"can't become untapped" restrictions (CR 701.21). -/
def untapPermanentLogged (g : Game) (o : GameObject)
    (sourceId : Option ObjectId := none) : Game :=
  if let .chooseReplacement .. := g.pending then
    let baseCause :=
      g.resolveOptionalCause none (fallbackSrc := sourceId) (fallbackCtrl := g.controllerOf o)
        (defaultCause := .turnBased .untapAll)
    g.chainPendingReplacement (.untapPermanent o.id false true (some baseCause))
  else if g.hostCantBecomeUntapped o then
    g.logMsg s!"{g.name o} can't become untapped"
  else if !o.status.tapped then
    g.logMsg s!"{g.name o} is already untapped"
  else
    let baseCause :=
      g.resolveOptionalCause none (fallbackSrc := sourceId) (fallbackCtrl := g.controllerOf o)
        (defaultCause := .turnBased .untapAll)
    g.untapPermanent o (cause := some baseCause)

/-- Make `o` lose indestructible until end of turn. -/
def loseIndestructibleUntilEot (g : Game) (o : GameObject) : Game :=
  let g := g.createEffect (.loseIndestructibleUntilEot o.id)
  g.logMsg s!"{g.name o} loses indestructible until end of turn"

/-- Tap `o` and put a stun counter on it (Ruling 764: an already tapped permanent
still receives the stun counter). -/
def tapAndStunPermanent (g : Game) (o : GameObject)
    (sourceId : Option ObjectId := none) : Game :=
  let cause := g.resolveOptionalCause none (fallbackSrc := sourceId) (fallbackCtrl := g.controllerOf o)
  g.withBatch (some cause) fun g =>
    let g := if o.status.tapped then g else g.becomeTapped o (cause := some cause)
    let cur := g.object! o.id
    g.putCountersDeferredLog cur.id .stun 1 (g.controllerOf cur) .isPutOn (cause := some cause)

/-- Set `o`'s base power and toughness to `pw`/`tw` until end of turn. -/
def setBasePTUntilEotLogged (g : Game) (o : GameObject) (pw tw : Int) : Game :=
  let g := g.createEffect (.setBasePTUntilEot o.id (pw, tw))
  g.logMsg s!"{g.name o} has base power and toughness {pw}/{tw} until end of turn"

/-- Double `o`'s power and toughness until end of turn (CR 701.10). -/
def doublePowerAndToughness (g : Game) (o : GameObject) : Game :=
  g.pumpPermanent o (g.power o) (g.toughness o)

/-- Start surveilling `n` during resolution (CR 701.25): look at the top
`n` cards, put any number into the graveyard and the rest back on top in any
order. -/
def beginSurveil (g : Game) (p : PlayerId) (n : Nat) : Game :=
  g.withContinuationFrame fun g =>
    if !g.stillInGame p then g
    else
      let pl := g.player p
      let count := min n pl.library.size
      if n == 0 then
        g.logMsg s!"{pl.name} surveils {n} (no cards to look at)"
      else if count == 0 then
        let happened :=
          GameEvent.looked g.turnNumber p 0 true n (cause := some (g.resolvingOrRuleCause p))
        let g := g.record happened
        g.logMsg s!"{pl.name} surveils {n} (no cards to look at)"
      else
        (g.change (.pending (.surveil p count n))).logMsg
          s!"{pl.name} surveils {n}"

/-- Mill each card in `remainingIds` (or `freshCount` top cards when resuming a
deferred player mill) sequentially inside an open or standalone batch, pausing
on `Pending.chooseReplacement` (CR 701.17 / 616.1). -/
def millCardsLoop (g : Game) (p : PlayerId) (remainingIds : Array ObjectId)
    (emptyTail : Bool := false) (cause : Option EventCause := none)
    (logCard : Option String := none) (freshCount : Option Nat := none) : Game := Id.run do
  if let .chooseReplacement .. := g.pending then
    return g.chainPendingReplacement
      (.millCardsLoop p remainingIds emptyTail cause logCard freshCount)
  let mut g := g
  if let some name := logCard then
    g := g.logMsg s!"{(g.player p).name} mills {name}"
  if !g.stillInGame p then
    return g
  let mut ids := remainingIds
  let mut tail := emptyTail
  if let some n := freshCount then
    let pl := g.player p
    if n > 0 && pl.library.isEmpty then
      return g.logMsg s!"{pl.name} mills nothing (empty library)"
    let count := min n pl.library.size
    ids := (pl.library.extract (pl.library.size - count) pl.library.size).reverse
    tail := count < n
  for i in [0:ids.size] do
    let top := ids[i]!
    match g.findObject? top with
    | some o =>
      if o.zone == .library p then
        let name := g.name o
        let (g', _) := g.move top (.graveyard p) none (verb := some .mill) (actor := some p)
          (cause := cause)
        g := g'
        if let .chooseReplacement .. := g.pending then
          let rem := ids.extract (i + 1) ids.size
          return g.chainPendingReplacement (.millCardsLoop p rem tail cause (some name) none)
        g := g.logMsg s!"{(g.player p).name} mills {name}"
    | none => pure ()
  if tail then
    g := g.logMsg s!"{(g.player p).name} mills nothing (empty library)"
  return g

/-- Put the top `n` cards of `p`'s library into their graveyard (CR 701.17). -/
def mill (g : Game) (p : PlayerId) (n : Nat) (cause : Option EventCause := none) : Game :=
  if !g.stillInGame p then g
  else
    let defaultCause :=
      cause.orElse (fun _ =>
        if n == 0 || (g.player p).library.isEmpty then none
        else g.currentResolvingContext?.map fun (src, ctrl) =>
          .oneShotEffect none src (ctrl.orElse (fun _ => some p)))
    if let .chooseReplacement .. := g.pending then
      if n == 0 then g
      else g.chainPendingReplacement (.millCardsLoop p #[] false defaultCause none (some n))
    else
      g.withBatch defaultCause fun g =>
        let pl := g.player p
        if n > 0 && pl.library.isEmpty then
          g.logMsg s!"{pl.name} mills nothing (empty library)"
        else
          let count := min n pl.library.size
          let tops := (pl.library.extract (pl.library.size - count) pl.library.size).reverse
          g.millCardsLoop p tops (emptyTail := count < n) (cause := defaultCause)

/-- Move up to `maxLeft` public cards from `remainingIds` into `p`'s hand inside
an open or standalone batch, pausing on `Pending.chooseReplacement` and logging
arrival only if each card enters `.hand p` (CR 614.6 / 701.17c). -/
def movePublicCardsToHandLoop (g : Game) (p : PlayerId) (remainingIds : Array ObjectId)
    (maxLeft : Nat) (playerPutsStyle : Bool) (cause : Option EventCause)
    (pendingCard : Option (ObjectId × String) := none)
    (requirePublicZone : Bool := true) : Game := Id.run do
  if let .chooseReplacement .. := g.pending then
    return g.chainPendingReplacement
      (.finishPostStep (.movePublicCardsToHandLoop p remainingIds maxLeft playerPutsStyle cause pendingCard requirePublicZone))
  let mut g := g
  let mut left := maxLeft
  if let some (cid, cname) := pendingCard then
    if (g.followMovedToZone? cid (· == .hand p)).isSome then
      g := g.logMsg
        (if playerPutsStyle then s!"{(g.player p).name} puts {cname} into their hand"
         else s!"{cname} is put into {(g.player p).name}'s hand")
  if !g.stillInGame p then
    return g
  for i in [0:remainingIds.size] do
    let id := remainingIds[i]!
    match g.findObject? id with
    | some o =>
      if left > 0 && (!requirePublicZone || isPublicZone o.zone) then
        let name := g.name o
        left := left - 1
        let (g', _) := g.move id (.hand p) none (cause := cause)
        g := g'
        if let .chooseReplacement .. := g.pending then
          let rem := remainingIds.extract (i + 1) remainingIds.size
          return g.chainPendingReplacement
            (.finishPostStep (.movePublicCardsToHandLoop p rem left playerPutsStyle cause (some (id, name)) requirePublicZone))
        if (g.followMovedToZone? id (· == .hand p)).isSome then
          g := g.logMsg
            (if playerPutsStyle then s!"{(g.player p).name} puts {name} into their hand"
             else s!"{name} is put into {(g.player p).name}'s hand")
    | none => pure ()
  return g

/-- Move milled cards matching `pred` from the public zone they entered into
`p`'s hand (CR 701.17c). -/
def finishMillThenPutFromPublic (g : Game) (p : PlayerId) (preIds : Array ObjectId)
    (pred : GameObject → Bool) (maxPut : Option Nat := none)
    (cause : Option EventCause := none) : Game :=
  let milled :=
    preIds.filterMap fun id =>
      match g.followMilledPublic? id with
      | some o => if isPublicZone o.zone && pred o then some o.id else none
      | none => none
  if milled.isEmpty then g
  else
    g.withBatch cause fun g =>
      g.movePublicCardsToHandLoop p milled (maxPut.getD milled.size) true cause

/-- Mill `n`, then put matching milled cards from the public zone they entered
into hand (CR 701.17c). `maxPut` limits how many are returned (`none` means all
matches). -/
def millThenPutFromGy (g : Game) (p : PlayerId) (n : Nat)
    (pred : GameObject → Bool) (maxPut : Option Nat := none)
    (types : Array CardType := #[]) : Game :=
  let lib := (g.player p).library
  let count := min n lib.size
  let tops := (lib.extract (lib.size - count) lib.size).reverse
  let (g, cause?) : Game × Option EventCause :=
    if n == 0 || lib.isEmpty then (g, none)
    else
      match g.currentResolvingContext? with
      | some (src, ctrl) =>
        let (g, c) := g.allocDelayedCause (ctrl.orElse (fun _ => some p)) src
        (g, some c)
      | none => (g, none)
  let g := g.mill p n (cause := cause?)
  if let .chooseReplacement .. := g.pending then
    g.chainPendingReplacement
      (.finishMillChooseForHand p tops types #[] 0 false true maxPut cause?)
  else
    g.finishMillThenPutFromPublic p tops pred maxPut cause?

/-- Deal `n` damage to each still-matching creature in `remainingIds`, pausing
and chaining `.dealDamageToEachCreatureMatching` if a CR 616.1 choice opens, and
aggregating CR 702.15b lifelink life gain once after all matching creatures'
damage has been dealt (unless `suppressLifelink` defers lifelink to an outer
combined damage instruction). -/
def dealDamageToEachCreatureMatchingIds (g : Game) (remainingIds : Array ObjectId) (n : Nat)
    (onlyNonSubtype : Option CardSubtype := none)
    (exceptControllerTokens : Option PlayerId := none)
    (onlyOpponentsOf : Option PlayerId := none)
    (source : Option EventObject := none)
    (cause : Option EventCause := none)
    (startEventIdx : Option Nat := none)
    (suppressLifelink : Bool := false) : Game := Id.run do
  if let .chooseReplacement .. := g.pending then
    return g.chainPendingReplacement
      (.dealDamageToEachCreatureMatching remainingIds n onlyNonSubtype exceptControllerTokens onlyOpponentsOf source cause startEventIdx suppressLifelink)
  let mut g := g
  let sIdx := startEventIdx.getD g.events.size
  let c := cause.orElse (fun _ => g.currentBatch.bind (·.2))
  for i in [0:remainingIds.size] do
    let id := remainingIds[i]!
    match g.findObject? id with
    | some o =>
      if o.isOnBattlefield && g.isCreature o &&
          (onlyNonSubtype.all (fun s => !g.hasSubtype o s)) &&
          (exceptControllerTokens.all (fun p => !(o.printed.isToken && g.controlledBy o p))) &&
          (onlyOpponentsOf.all (fun p => (g.controllerOf o).any (g.isLivingOpponentOf p ·))) then
        g := g.dealDamageToPermanent o n (source := source) (cause := c) (suppressLifelink := true)
        if let .chooseReplacement .. := g.pending then
          let rem := remainingIds.extract (i + 1) remainingIds.size
          if !rem.isEmpty || !suppressLifelink then
            g := g.chainPendingReplacement
              (.dealDamageToEachCreatureMatching rem n onlyNonSubtype exceptControllerTokens onlyOpponentsOf source c (some sIdx) suppressLifelink)
          return g
    | none => pure ()
  if !suppressLifelink then
    g := g.applyAggregatedLifelinkSince sIdx (cause := c)
  return g

/-- Deal `n` damage to each creature matching `pred`. -/
def dealDamageToEachCreatureMatching (g : Game) (n : Nat)
    (pred : GameObject → Bool := fun _ => true)
    (onlyOpponentsOf : Option PlayerId := none)
    (source : Option EventObject := none)
    (cause : Option EventCause := none)
    (suppressLifelink : Bool := false) : Game :=
  let defaultCause :=
    cause.orElse (fun _ =>
      if n == 0 then none
      else g.currentResolvingContext?.map fun (src, ctrl) => .oneShotEffect none src ctrl)
  let ids := (g.battlefield.filter (fun o => g.isCreature o && pred o)).map (·.id)
  if let .chooseReplacement .. := g.pending then
    g.dealDamageToEachCreatureMatchingIds ids n (onlyOpponentsOf := onlyOpponentsOf)
      (source := source) (cause := defaultCause) (suppressLifelink := suppressLifelink)
  else
    g.withBatch defaultCause fun g =>
      g.dealDamageToEachCreatureMatchingIds ids n (onlyOpponentsOf := onlyOpponentsOf)
        (source := source) (cause := defaultCause) (suppressLifelink := suppressLifelink)

/-- Deal `n` damage to each creature that is not `subtype`. -/
def dealDamageToEachNonDragon (g : Game) (n : Nat) (subtype : CardSubtype := .dragon)
    (source : Option EventObject := none)
    (cause : Option EventCause := none)
    (suppressLifelink : Bool := false) : Game :=
  let defaultCause :=
    cause.orElse (fun _ =>
      if n == 0 then none
      else g.currentResolvingContext?.map fun (src, ctrl) => .oneShotEffect none src ctrl)
  let ids := (g.battlefield.filter (fun o => g.isCreature o && !g.hasSubtype o subtype)).map (·.id)
  if let .chooseReplacement .. := g.pending then
    g.dealDamageToEachCreatureMatchingIds ids n (onlyNonSubtype := some subtype)
      (source := source) (cause := defaultCause) (suppressLifelink := suppressLifelink)
  else
    g.withBatch defaultCause fun g =>
      g.dealDamageToEachCreatureMatchingIds ids n (onlyNonSubtype := some subtype)
        (source := source) (cause := defaultCause) (suppressLifelink := suppressLifelink)

/-- Deal `n` damage to each creature that isn't `subtype` and each opponent of
`controller`, deferring `startIdx` capture if an earlier step is paused on
`Pending.chooseReplacement` and aggregating CR 702.15b lifelink once across both. -/
def dealDamageToEachNonSubtypeAndOpponents (g : Game) (controller : PlayerId)
    (n : Nat) (subtype : CardSubtype) (sourceId : Option ObjectId)
    (cause : Option EventCause := none) : Game :=
  if n == 0 then g
  else if let .chooseReplacement .. := g.pending then
    g.chainPendingReplacement
      (.finishPostStep (.dealDamageToEachNonSubtypeAndOpponents controller n subtype sourceId cause))
  else
    let src? := sourceId.bind g.damageSourceById?
    let srcSnap? := sourceId.bind g.damageSourceEventById?
    let (g, cause?) : Game × Option EventCause :=
      match cause with
      | some c => (g, some c)
      | none =>
        match g.currentResolvingContext? with
        | some (src, ctrl) =>
          let (g, c) := g.allocDelayedCause (ctrl.orElse (fun _ => some controller)) (src.orElse (fun _ => sourceId))
          (g, some c)
        | none =>
          let (g, c) := g.allocDelayedCause (some controller) sourceId
          (g, some c)
    let startIdx := g.events.size
    g.withBatch cause? fun g =>
      let batchCause := cause?.orElse (fun _ => g.currentBatch.bind (·.2))
      let g :=
        g.dealDamageToEachNonDragon n subtype
          (source := srcSnap?) (cause := batchCause) (suppressLifelink := true)
      if let .chooseReplacement .. := g.pending then
        g.chainPendingReplacement
          (.finishPostStep (.dealDamageToEachOpponent controller n sourceId batchCause (some startIdx)))
      else
        g.dealDamageToEachOpponent controller n (source := src?) (cause := batchCause)
          (startEventIdx := some startIdx)

/-- True when permanent `id` was actually destroyed (CR 701.8a–c): its departure
`ZoneEvent.moved` moved it from `.battlefield` with verb `.destroy`. Indestructible
permanents (CR 702.12b), shield-counter replacements (CR 122.1c), and non-destroy
battlefield departures (CR 701.8b, such as CR 800.4c control-loss exile or sacrifice)
do not emit `.destroy`; graveyard-redirect replacements (finality counters CR 122.1h,
`untilEotExileIfDies`, `.exileInsteadOfGraveyard`) preserve `ZoneVerb.destroy` into
`.exile` so `.dies` does not trigger (CR 700.4) while `"destroyed this way"` still
counts them per WotC Judge Ruling 80 (`OracleData.lean`). -/
def wasPermanentDestroyed (g : Game) (id : ObjectId) : Bool :=
  match g.events.findSomeRev? (fun e =>
    match e.change with
    | .rules (.zone (.moved before _ fromZone _ verb _ _ _)) =>
      if before.id == some id && fromZone == .battlefield then
        some (verb == .destroy)
      else none
    | _ => none) with
  | some b => b
  | none => false

/-- Destroy each permanent in `remainingIds` sequentially inside an open or
standalone batch, pausing on `Pending.chooseReplacement` and optionally
gaining life per destroyed permanent (`obGainLifeFor`) or logging `logMsgAfter`
once all finish. -/
def destroyPermanentsLoop (g : Game) (remainingIds : Array ObjectId)
    (allCandidates : Array ObjectId := #[])
    (countNote : Bool := false)
    (obGainLifeFor : Option PlayerId := none)
    (logMsgAfter : Option String := none)
    (preBattlefield : Option (Array GameObject) := none)
    (cause : Option EventCause := none) : Game := Id.run do
  if let .chooseReplacement .. := g.pending then
    return g.chainPendingReplacement
      (.destroyPermanentsLoop remainingIds allCandidates countNote
        obGainLifeFor logMsgAfter preBattlefield cause)
  let mut g := g
  let preBf := preBattlefield.getD g.battlefield
  let allCands :=
    if allCandidates.isEmpty && (countNote || obGainLifeFor.isSome) then remainingIds
    else allCandidates
  for i in [0:remainingIds.size] do
    let id := remainingIds[i]!
    match g.findObject? id with
    | some o =>
      if o.isOnBattlefield then
        g := g.destroyPermanent o (cause := cause) (preBattlefield := some preBf)
        if let .chooseReplacement .. := g.pending then
          let rem := remainingIds.extract (i + 1) remainingIds.size
          if !rem.isEmpty || countNote || obGainLifeFor.isSome || logMsgAfter.isSome then
            g := g.chainPendingReplacement
              (.destroyPermanentsLoop rem allCands countNote
                obGainLifeFor logMsgAfter (some preBf) cause)
          return g
    | none => pure ()
  let destroyedCount :=
    if obGainLifeFor.isSome then
      allCands.foldl (fun acc id =>
        if g.wasPermanentDestroyed id then acc + 1 else acc) 0
    else 0
  if let some pid := obGainLifeFor then
    if destroyedCount > 0 then
      g := g.gainLife pid destroyedCount (cause := cause)
  if let some msg := logMsgAfter then
    g := g.logMsg msg
  return g

/-- Exile each still-present permanent in `remainingIds` sequentially inside an
open or standalone batch, pausing on `Pending.chooseReplacement` and logging
exile only if the object arrives in `.exile` (CR 614.6). -/
def exilePermanentsLoop (g : Game) (remainingIds : Array ObjectId)
    (logExile : Bool := true) (cause : Option EventCause := none)
    (logCard : Option (ObjectId × String) := none) : Game := Id.run do
  if let .chooseReplacement .. := g.pending then
    return g.chainPendingReplacement
      (.exilePermanentsLoop remainingIds logExile cause logCard)
  let mut g := g
  if let some (oid, name) := logCard then
    if logExile && (g.followMovedToZone? oid (· == .exile)).isSome then
      g := g.logMsg s!"{name} is exiled"
  for i in [0:remainingIds.size] do
    let id := remainingIds[i]!
    match g.findObject? id with
    | some o =>
      if o.isOnBattlefield then
        let name := g.name o
        let (g', _) := g.move id .exile none (cause := cause)
        g := g'
        if let .chooseReplacement .. := g.pending then
          let rem := remainingIds.extract (i + 1) remainingIds.size
          if !rem.isEmpty || logExile then
            g := g.chainPendingReplacement
              (.exilePermanentsLoop rem logExile cause (if logExile then some (id, name) else none))
          return g
        if logExile && (g.followMovedToZone? id (· == .exile)).isSome then
          g := g.logMsg s!"{name} is exiled"
    | none => pure ()
  return g

/-- Post-return stage of `flickerPermanents`: log and run `afterPermanentEnters`
for each exiled card in `enteredFromIds` that returned to the battlefield. -/
private def flickerPostReturn (g : Game) (enteredFromIds : Array ObjectId)
    (logText : String) : Game := Id.run do
  let mut g := g
  for k in [0:enteredFromIds.size] do
    let eid := enteredFromIds[k]!
    match g.followMovedToZone? eid (· == .battlefield) with
    | some retObj =>
      g := g.logMsg s!"{g.name retObj} {logText}"
      g := g.afterPermanentEnters retObj
      if let .chooseReplacement .. := g.pending then
        let rem := enteredFromIds.extract (k + 1) enteredFromIds.size
        if !rem.isEmpty then
          g := g.chainPendingReplacement (.flickerLoop #[] #[] rem logText .postReturn)
        return g
    | none => pure ()
  return g

/-- Return-batch stage of `flickerPermanents`: inside the return batch, move each
exiled card in `remainingIds` back to the battlefield under its owner's control. -/
private def flickerReturnBatchLoop (g : Game) (remainingIds : Array ObjectId)
    (exiledPreIds : Array ObjectId) (enteredFromIds : Array ObjectId)
    (logText : String) (tapped : Bool) (onlyLandTapped : Bool)
    (clearExileFields : Bool) (cause : Option EventCause)
    (preBattlefield : Option (Array GameObject) := none) : Game := Id.run do
  let preBf := preBattlefield.getD g.battlefield
  let mut g := g
  for i in [0:remainingIds.size] do
    let eid := remainingIds[i]!
    match g.findObject? eid with
    | some o =>
      if o.zone == .exile && !o.printed.isToken then
        if clearExileFields then
          g := g.changeObject eid (.linkedExile #[])
        let enterTapped := tapped || (onlyLandTapped && g.isLand o)
        let (g', _) := g.move eid .battlefield (some o.owner)
          (tapped := enterTapped) (preBattlefield := some preBf) (cause := cause)
        g := g'
        if let .chooseReplacement .. := g.pending then
          let rem := remainingIds.extract (i + 1) remainingIds.size
          if !rem.isEmpty then
            g := g.chainPendingReplacement
              (.flickerLoop rem exiledPreIds enteredFromIds logText .returnBatch tapped onlyLandTapped clearExileFields cause (some preBf))
          return g
    | none => pure ()
  return g

/-- Start-return-batch stage of `flickerPermanents`: after the exile batch closes,
return all nontoken exiled cards simultaneously in a second batch
(CR 111.8 / 400.7 / 603.6a). -/
private def flickerStartReturnBatch (g : Game) (exiledPreIds : Array ObjectId)
    (logText : String) (tapped : Bool) (onlyLandTapped : Bool)
    (clearExileFields : Bool) (cause : Option EventCause) : Game :=
  let exiledObjs := exiledPreIds.filterMap (fun id => g.followMovedToZone? id (· == .exile))
  let g :=
    exiledObjs.foldl (fun acc o =>
      if o.printed.isToken then acc.logMsg s!"{acc.name o} is exiled" else acc) g
  let returnableIds := (exiledObjs.filter (fun o => !o.printed.isToken)).map (·.id)
  if returnableIds.isEmpty then g
  else
    let preBf := g.battlefield
    let g := g.withBatch cause fun g =>
      g.flickerReturnBatchLoop returnableIds exiledPreIds returnableIds logText
        tapped onlyLandTapped clearExileFields cause (some preBf)
    if let .chooseReplacement .. := g.pending then
      g.chainPendingReplacement
        (.flickerLoop #[] exiledPreIds returnableIds logText .postReturn tapped onlyLandTapped clearExileFields cause (some preBf))
    else
      g.flickerPostReturn returnableIds logText

/-- Exile-batch stage of `flickerPermanents`: inside the exile batch, move each
target in `remainingIds` to `.exile`. -/
private def flickerExileBatchLoop (g : Game) (remainingIds : Array ObjectId)
    (exiledPreIds : Array ObjectId) (logText : String) (tapped : Bool)
    (onlyLandTapped : Bool) (clearExileFields : Bool)
    (cause : Option EventCause) : Game := Id.run do
  let mut g := g
  for i in [0:remainingIds.size] do
    let id := remainingIds[i]!
    match g.findObject? id with
    | some o =>
      if o.zone != .exile then
        let (g', _) := g.move id .exile none (cause := cause)
        g := g'
        if let .chooseReplacement .. := g.pending then
          let rem := remainingIds.extract (i + 1) remainingIds.size
          if !rem.isEmpty then
            g := g.chainPendingReplacement
              (.flickerLoop rem exiledPreIds #[] logText .exileBatch tapped onlyLandTapped clearExileFields cause)
          return g
    | none => pure ()
  return g

/-- Exile all permanents in `targetIds` in one simultaneous batch, then return
all exiled nontoken cards to the battlefield under their owners' control in a
second simultaneous batch (CR 111.8 / 400.7 / 603.6a / 616.1). -/
def flickerPermanents (g : Game) (targetIds : Array ObjectId)
    (logText : String := "is exiled, then returned to the battlefield")
    (tapped : Bool := false) (onlyLandTapped : Bool := false)
    (clearExileFields : Bool := false) (cause : Option EventCause := none) : Game :=
  if targetIds.isEmpty then g
  else
    let (g, cause) : Game × Option EventCause :=
      match cause with
      | some c => (g, some c)
      | none =>
        match g.currentResolvingContext? with
        | some (src, ctrl) =>
          let (g, c) := g.allocDelayedCause ctrl src
          (g, some c)
        | none => (g, none)
    if let .chooseReplacement .. := g.pending then
      g.chainPendingReplacement
        (.flickerLoop targetIds targetIds #[] logText .beforeExileBatch tapped onlyLandTapped clearExileFields cause)
    else
      let g := g.withBatch cause fun g =>
        g.flickerExileBatchLoop targetIds targetIds logText tapped onlyLandTapped clearExileFields cause
      if let .chooseReplacement .. := g.pending then
        g.chainPendingReplacement
          (.flickerLoop #[] targetIds #[] logText .startReturnBatch tapped onlyLandTapped clearExileFields cause)
      else
        g.flickerStartReturnBatch targetIds logText tapped onlyLandTapped clearExileFields cause

/-- Resume a paused `PendingReplacement.flickerLoop` stage. -/
def resumeFlickerLoop (g : Game) (remainingIds : Array ObjectId)
    (exiledPreIds : Array ObjectId := #[])
    (enteredFromIds : Array ObjectId := #[])
    (logText : String := "is exiled, then returned to the battlefield")
    (stage : FlickerStage := .exileBatch) (tapped : Bool := false) (onlyLandTapped : Bool := false)
    (clearExileFields : Bool := false) (cause : Option EventCause := none)
    (preBattlefield : Option (Array GameObject) := none) : Game :=
  if let .chooseReplacement .. := g.pending then
    g.chainPendingReplacement
      (.flickerLoop remainingIds exiledPreIds enteredFromIds logText stage tapped onlyLandTapped clearExileFields cause preBattlefield)
  else
    match stage with
    | .exileBatch => g.flickerExileBatchLoop remainingIds exiledPreIds logText tapped onlyLandTapped clearExileFields cause
    | .startReturnBatch => g.flickerStartReturnBatch exiledPreIds logText tapped onlyLandTapped clearExileFields cause
    | .returnBatch => g.flickerReturnBatchLoop remainingIds exiledPreIds enteredFromIds logText tapped onlyLandTapped clearExileFields cause preBattlefield
    | .postReturn => g.flickerPostReturn enteredFromIds logText
    | .beforeExileBatch =>
      g.flickerPermanents remainingIds (logText := logText) (tapped := tapped)
        (onlyLandTapped := onlyLandTapped) (clearExileFields := clearExileFields) (cause := cause)

/-! ### Reveal, Choice, Proliferate, and Transform Helpers -/

def revealUntilCards (g : Game) (p : PlayerId) (pred : GameObject → Bool) (limit : Nat)
    (cause : Option EventCause := none) :
    Game × Array ObjectId × Array ObjectId :=
  Id.run do
    let mut g := g
    let mut hits : Array ObjectId := #[]
    let mut rest : Array ObjectId := #[]
    let mut shown : Array ObjectId := #[]
    let lib := (g.player p).library
    let mut idx := lib.size
    while hits.size < limit && idx > 0 do
      idx := idx - 1
      let cid := lib[idx]!
      let card := g.object! cid
      shown := shown.push cid
      g := g.logMsg s!"{(g.player p).name} reveals {g.name card}"
      if pred card then hits := hits.push cid
      else rest := rest.push cid
    if !shown.isEmpty then
      g := g.record (GameEvent.revealed g.turnNumber p shown
        (cause := some (cause.getD (g.resolvingOrRuleCause p))))
    return (g, hits, rest)

def putHitsToBattlefield (g : Game) (p : PlayerId) (hits : Array ObjectId) (haste := false)
    (tapped := false) (cause : Option EventCause := none) : Game :=
  g.withBatch cause fun g =>
    g.putToBattlefieldLoop p hits (tapped := tapped) (haste := haste) (cause := cause)

def restBottomCards (g : Game) (p : PlayerId) (rest : Array ObjectId) (shuffle : Bool)
    (cause : Option EventCause := none) : Game :=
  if shuffle then g.shuffleThen p .none
  else if rest.isEmpty then g
  else
    g.requestOrderInto rest (.library p)
      s!"{(g.player p).name} puts the rest on the bottom of their library in a random order"
      (cause := cause)

def proliferateTarget (g : Game) (controller : PlayerId) (targets : Array Target)
    (sourceId : Option ObjectId := none) : Game :=
  g.withLegalSpecTarget controller .permanentOrPlayer targets (fun g t =>
    let cause := some (g.resolvingOrRuleCause controller)
    g.withBatch cause fun g =>
      let effCause := g.resolveOptionalCause cause (fallbackCtrl := some controller)
      match t with
      | Target.permanent id =>
        match g.findObject? id with
        | some o =>
          if o.isOnBattlefield && o.status.hasCounters then
            let hasPlusOne := o.status.plusOnePlusOne > 0
            let nonPlusKinds :=
              o.status.toCounterBag.filterMap (fun (kind, _) =>
                if kind == .plusOnePlusOne then none else some kind)
            g.finishProliferateEachKind controller id nonPlusKinds hasPlusOne effCause
          else g.logMsg s!"{g.name o} has no counters"
        | none => g.logMsg "The target is no longer legal"
      | Target.player pid =>
        let pl := g.player pid
        let hasPoison := g.teamPoison pid > 0
        let otherKinds := pl.counters.filterMap fun (k, cnt) =>
          if k != .poison && cnt > 0 then some k else none
        if hasPoison || !otherKinds.isEmpty then
          let g :=
            if hasPoison then
              (g.record (GameEvent.poisoned g.turnNumber pid 1 (byPlayer := some controller) (cause := effCause)))
                |>.logMsg s!"{pl.name} gets a poison counter"
            else g
          let g :=
            otherKinds.foldl (fun g kind =>
              (g.record (GameEvent.playerCounters g.turnNumber pid kind (.put 1)
                (byPlayer := some controller) (cause := effCause)))
                |>.logMsg s!"{pl.name} gets another counter") g
          g.record (GameEvent.proliferated g.turnNumber controller (players := #[pid]) (cause := effCause))
        else g.logMsg s!"{pl.name} has no counters"
      | Target.card _ => g.logMsg "The target is no longer legal") sourceId
    (some "The target is no longer legal")

private def logChosenCardToHand (g : Game) (p : PlayerId) (id : ObjectId)
    (owner : PlayerId) (name : String) : Game :=
  if (g.followMovedToZone? id (· == .hand owner)).isSome then
    if owner == p then g.logMsg s!"{(g.player p).name} puts {name} into their hand"
    else g.logMsg s!"{(g.player p).name} puts {name} into {(g.player owner).name}'s hand"
  else g

def chooseCardsToHandLoop (g : Game) (p : PlayerId) (remainingIds : Array ObjectId)
    (cause : Option EventCause) (pendingCard : Option (ObjectId × PlayerId × String) := none) :
    Game := Id.run do
  if let .chooseReplacement .. := g.pending then
    return g.chainPendingReplacement
      (.finishPostStep (.chooseCardsToHandLoop p remainingIds cause pendingCard))
  let mut g := g
  if let some (cid, owner, name) := pendingCard then
    g := g.logChosenCardToHand p cid owner name
  for i in [0:remainingIds.size] do
    let id := remainingIds[i]!
    match g.findObject? id with
    | some o =>
      if isPublicZone o.zone || o.zone == .hand o.owner then
        let owner := o.owner
        let name := g.name o
        let (g', _) := g.move id (.hand owner) none (cause := cause)
        g := g'
        if let .chooseReplacement .. := g.pending then
          let rem := remainingIds.extract (i + 1) remainingIds.size
          return g.chainPendingReplacement
            (.finishPostStep (.chooseCardsToHandLoop p rem cause (some (id, owner, name))))
        g := g.logChosenCardToHand p id owner name
    | none => pure ()
  return g

@[export mtg_game_finish_choose_cards]
def finishChooseCards (g : Game) (p : PlayerId) (chosen : Array ObjectId)
    (purpose : CardChoice) (cause : Option EventCause := none) : Game :=
  let stashed := cause.orElse (fun _ => g.stashedCause.orElse (fun _ => chosen[0]?.bind g.lastMoveCauseOf?))
  let g := if g.stashedCause.isSome then g.change (.stashedCause none) else g
  let allocIfResolving (g : Game) : Game × Option EventCause :=
    match g.currentResolvingContext? with
    | some (src, ctrl) =>
      let (g, c) := g.allocDelayedCause (ctrl.orElse (fun _ => some p)) src
      (g, some c)
    | none => (g, none)
  match purpose with
  | .toHand _ =>
    let (g, cause?) : Game × Option EventCause :=
      if chosen.isEmpty then (g, none)
      else
        match stashed with
        | some c => (g, some c)
        | none => allocIfResolving g
    g.withBatch cause? fun g => g.chooseCardsToHandLoop p chosen cause?
  | .creaturesToBattlefield =>
    let valid := chosen.filter fun id =>
      (g.findObject? id).any (fun o => o.zone == .hand o.owner && g.isCreature o)
    let (g, cause?) : Game × Option EventCause :=
      if valid.isEmpty then (g, none)
      else
        match stashed with
        | some c => (g, some c)
        | none => allocIfResolving g
    g.withBatch cause? fun g =>
      g.putToBattlefieldLoop p valid (entryLog := .enters) (cause := cause?)
  | .landsTappedGainLife life =>
    let valid := chosen.filter fun id =>
      (g.findObject? id).any (fun o => g.isLand o && o.zone == .library o.owner)
    let (g, cause?) : Game × Option EventCause :=
      if valid.isEmpty then (g, none)
      else
        match stashed with
        | some c => (g, some c)
        | none => allocIfResolving g
    let g := g.withBatch cause? fun g =>
      g.putToBattlefieldLoop p valid (tapped := true) (isLandEnters := true)
        (entryLog := .entersTapped) (cause := cause?)
    if let .chooseReplacement .. := g.pending then
      g.chainPendingReplacement (.finishPostStep (.shuffleThenGainLife p life))
    else
      g.withContinuationFrame fun g =>
        (g.requestShuffle p (.gainLife p life)).continueIfShuffled
  | .keepDestroyRest =>
    let preBf := g.battlefield
    let doomed := (preBf.filter (fun o => g.isCreature o && !chosen.contains o.id)).map (·.id)
    let (g, cause?) : Game × Option EventCause :=
      if !doomed.isEmpty then
        match stashed with
        | some c => (g, some c)
        | none => allocIfResolving g
      else (g, none)
    g.withBatch cause? fun g =>
      g.destroyPermanentsLoop doomed
        (logMsgAfter := some "Chosen creatures are kept; the rest are destroyed")
        (preBattlefield := some preBf) (cause := cause?)
  | .amassArmy subtype n attach =>
    match chosen[0]? with
    | some id => g.finishAmassOn p id subtype n attach (cause := stashed)
    | none => g.logMsg s!"{(g.player p).name} doesn't choose an Army"

def offerCardChoice (g : Game) (p : PlayerId) (ids : Array ObjectId) (max : Nat)
    (purpose : CardChoice) (msg : String) (cause : Option EventCause := none) : Game :=
  if ids.isEmpty || max == 0 then g.finishChooseCards p #[] purpose (cause := cause)
  else
    let g := g.beginResolutionChoice p (.chooseCards ids max purpose) msg
    match cause with
    | some c => g.change (.stashedCause (some c))
    | none => g

def finishMillChooseForHand (g : Game) (p : PlayerId) (preIds : Array ObjectId)
    (pred : ObjectId → GameObject → Bool) (max : Nat) (mustOne : Bool)
    (cause : Option EventCause := none) : Game :=
  let eligible := preIds.filterMap (fun id =>
    match g.followMilledPublic? id with
    | some o => if pred id o then some o.id else none
    | none => none)
  if eligible.isEmpty then g
  else if mustOne && eligible.size == 1 then
    g.finishChooseCards p eligible (.toHand true) (cause := cause)
  else
    g.offerCardChoice p eligible max (.toHand mustOne)
      s!"{(g.player p).name} chooses cards to put into their hand"
      (cause := cause)

def millThenChooseForHand (g : Game) (p : PlayerId) (n : Nat)
    (pred : GameObject → Bool) (max : Nat) (mustOne : Bool)
    (types : Array CardType := #[]) : Game :=
  let lib := (g.player p).library
  let count := min n lib.size
  let tops := (lib.extract (lib.size - count) lib.size).reverse
  let matchedPreIds := tops.filter (fun id => (g.findObject? id).any pred)
  let (g, cause?) : Game × Option EventCause :=
    if n == 0 || lib.isEmpty then (g, none)
    else
      match g.currentResolvingContext? with
      | some (src, ctrl) =>
        let (g, c) := g.allocDelayedCause (ctrl.orElse (fun _ => some p)) src
        (g, some c)
      | none => (g, none)
  let g := g.mill p n (cause := cause?)
  if let .chooseReplacement .. := g.pending then
    g.chainPendingReplacement
      (.finishMillChooseForHand p tops types matchedPreIds max mustOne false none cause?)
  else
    g.finishMillChooseForHand p tops (fun _ o => pred o) max mustOne (cause := cause?)

@[export mtg_game_sequence_all_targets_illegal]
def sequenceAllTargetsIllegal (g : Game) (controller : PlayerId) (effect : Effect)
    (targets : Array Target) (sourceId : Option ObjectId := none) : Bool :=
  let spec := effect.effectiveTargetSpec
  let stackSelf := g.resolvingAbility.orElse (fun _ => g.resolvingSpell)
  effect.requiresTarget &&
    !((effect.allowsZeroTargets || spec.allowsZero) && targets.isEmpty) &&
    (targets.isEmpty ||
      targets.all fun t =>
        spec.slots.all fun slot =>
          !(g.legalTargetsForSlot controller slot sourceId stackSelf).contains t)

def logIllegalSequenceTargets (g : Game) (targets : Array Target) : Game :=
  if targets.isEmpty then
    g.logMsg "The target is no longer legal"
  else
    targets.foldl (fun g t => g.illegalAbilityTarget t) g

def offerBottomAnyOrder (g : Game) (p : PlayerId) (ids : Array ObjectId)
    (cause : Option EventCause := none) : Game :=
  if !g.stillInGame p then g
  else
    let (g, cause) : Game × Option EventCause :=
      match cause with
      | some c => (g, some c)
      | none =>
        if ids.isEmpty then (g, none)
        else
          match g.currentResolvingContext? with
          | some (src, ctrl) =>
            let (g, c) := g.allocDelayedCause ctrl src
            (g, some c)
          | none => (g, none)
    if ids.size ≤ 1 then
      g.moveIdsInOrder ids (.library p) (cause := cause)
        (log := s!"{(g.player p).name} puts the rest on the bottom of their library")
    else
      let g :=
        g.beginResolutionChoice p (.orderLibraryBottom ids)
          s!"{(g.player p).name} puts the rest on the bottom of their library in any order"
      match cause with
      | some c => g.change (.stashedCause (some c))
      | none => g

def transformPermanent (g : Game) (controller : PlayerId) (sourceId : Option ObjectId)
    (cause : Option EventCause := none) : Game :=
  g.withSourceOnBattlefield sourceId fun g o =>
    if g.cantTransform o then
      g.logMsg s!"{g.name o} can't transform (entered back face up at night)"
    else
      match (g.baseCard o).otherFace with
      | none => g.logMsg s!"{g.name o} has no other face"
      | some face =>
        let oldName := g.name o
        let batchCause :=
          cause.orElse (fun _ =>
            g.currentResolvingContext?.map fun (s, c) =>
              .oneShotEffect none (s.orElse (fun _ => some o.id)) (c.orElse (fun _ => some controller)))
        g.withBatch batchCause fun g =>
          let fallback := batchCause.getD (.gameRule .spellCast)
          let pre := g
          let g := g.record
            (GameEvent.transformed g.turnNumber (g.snapshot o) (!o.status.transformed)
              (cause := fallback))
          let g := g.logMsg s!"{oldName} transforms into {face.name}"
          reconcileControlAfterTransition pre g (cause := some fallback)

/-- Cards `p` owns outside the game. -/
def outsideCards (g : Game) (p : PlayerId) : Array GameObject :=
  g.objects.filter (fun o => o.zone == .outside p)

/-- Give `p`'s sideboard cards object identities outside the game, so an
effect can reveal or move them (CR 400.11b). -/
def materializeSideboard (g : Game) (p : PlayerId) : Game :=
  let side := (g.player p).sideboard
  let g := g.changePlayer p (.sideboard #[])
  side.foldl (fun g card => (g.allocObject card p (.outside p)).1) g

/-- Cards named `cardName` in `p`'s graveyard. -/
def graveyardCardsNamed (g : Game) (p : PlayerId) (cardName : String) : Array ObjectId :=
  (g.player p).graveyard.filter (fun id =>
    (g.findObject? id).any (fun o => g.name o == cardName))

/-- Give `p` an emblem or effect object in the command zone (CR 114.1–114.5). -/
def createCommandObject (g : Game) (p : PlayerId) (card : CardDef)
    (untilTurnOf : Option PlayerId := none) : Game :=
  if !g.stillInGame p then g
  else
    let (g, obj) := g.allocObject card p .command (some p)
    match untilTurnOf with
    | some q =>
      let effCause :=
        g.resolveOptionalCause none (fallbackCtrl := some p) (defaultCause := .gameRule .spellCast)
      g.createEffect (.commandEmblemUntilTurnOf obj.id q) (cause := some effCause)
    | none => g

/-- Deal `n` damage to each `remaining` target permanent or player one at a
time, pausing across `Pending.chooseReplacement` before checking subsequent
targets. -/
partial def damageUpToOneAndPlayerLoop (g : Game) (controller : PlayerId)
    (spec : TargetSpec) (remaining : Array (Nat × Target)) (n : Nat)
    (srcName : String) (sourceId : Option ObjectId)
    (cause? : Option EventCause)
    (startEventIdx : Option Nat := none) : Game :=
  if let .chooseReplacement .. := g.pending then
    g.chainPendingReplacement
      (.finishPostStep (.damageUpToOneAndPlayerLoop controller spec remaining n srcName sourceId cause? startEventIdx))
  else
    let sIdx := startEventIdx.getD g.events.size
    let c := cause?.orElse (fun _ => g.currentBatch.bind (·.2))
    match remaining[0]? with
    | none =>
      g.applyAggregatedLifelinkSince sIdx (cause := c)
    | some (i, t) =>
      let rest := remaining.extract 1 remaining.size
      let src? :=
        (g.resolvingSpell.bind g.damageSourceById?).orElse (fun _ => sourceId.bind g.damageSourceById?)
      let g :=
        match t with
        | Target.permanent id =>
          if g.targetLegalAt controller spec i t sourceId then
            match g.findObject? id with
            | some o =>
              g.dealDamageFrom srcName o n (source := src?) (cause := c)
                (suppressLifelink := true)
            | none => g
          else g.illegalAbilityTarget t
        | Target.player pid =>
          if g.targetLegalAt controller spec i t sourceId then
            g.dealDamageToPlayer pid n (source := src?) (cause := c)
              (suppressLifelink := true)
          else g.illegalAbilityTarget t
        | _ => g
      if let .chooseReplacement .. := g.pending then
        g.chainPendingReplacement
          (.finishPostStep (.damageUpToOneAndPlayerLoop controller spec rest n srcName sourceId c (some sIdx)))
      else
        g.damageUpToOneAndPlayerLoop controller spec rest n srcName sourceId c (some sIdx)

/-- Exile all but the bottom card of each opponent's library, pausing across
`Pending.chooseReplacement` and logging per opponent only when at least one
card arrived in `.exile` (or the library already had at most one card). -/
partial def exileOpponentLibrariesLoop (g : Game) (remainingOpps : Array PlayerId)
    (curOpp : Option PlayerId := none) (curIds : Array ObjectId := #[])
    (movedAnyForCur : Bool := false)
    (pendingId : Option ObjectId := none) : Game := Id.run do
  if let .chooseReplacement .. := g.pending then
    return g.chainPendingReplacement
      (.finishPostStep (.exileOpponentLibrariesLoop remainingOpps curOpp curIds movedAnyForCur pendingId))
  let mut g := g
  let mut opps := remainingOpps
  let mut cOpp := curOpp
  let mut ids := curIds
  let mut anyMoved := movedAnyForCur
  if let some pid := pendingId then
    if (g.followMovedToZone? pid (· == .exile)).isSome then
      anyMoved := true
  while true do
    match cOpp with
    | none =>
      match opps[0]? with
      | none => return g
      | some pid =>
        opps := opps.extract 1 opps.size
        if g.stillInGame pid then
          let lib := (g.player pid).library
          cOpp := some pid
          ids := lib.extract 1 lib.size
          anyMoved := ids.isEmpty
    | some pid =>
      if !g.stillInGame pid then
        if anyMoved then
          g := g.logMsg s!"All but the bottom card of {(g.player pid).name}'s library are exiled"
        cOpp := none
      else
        match ids[0]? with
        | none =>
          if anyMoved then
            g := g.logMsg s!"All but the bottom card of {(g.player pid).name}'s library are exiled"
          cOpp := none
        | some cid =>
          ids := ids.extract 1 ids.size
          let (g', _) := g.move cid .exile none
          g := g'
          if let .chooseReplacement .. := g.pending then
            return g.chainPendingReplacement
              (.finishPostStep (.exileOpponentLibrariesLoop opps (some pid) ids anyMoved (some cid)))
          if (g.followMovedToZone? cid (· == .exile)).isSome then
            anyMoved := true
  return g

def destroyCreaturesByManaParity (g : Game) (sourceId : Option ObjectId) (even : Bool) : Game :=
  let preBf := g.battlefield
  let ids := (preBf.filter (fun o =>
    some o.id != sourceId && g.isCreature o &&
      ((g.objectManaValue o % 2 == 0) == even))).map (·.id)
  let quality := if even then "even" else "odd"
  let g := g.logMsg s!"Destroy each other creature with {quality} mana value"
  g.withBatch none fun g =>
    g.destroyPermanentsLoop ids (preBattlefield := some preBf)

def returnCreaturesNotOfType (g : Game) (chosen : CardSubtype) : Game :=
  g.withBatch none fun g =>
    g.foldBattlefield (fun o => g.isCreature o && !g.hasSubtype o chosen)
      (fun g o => g.returnToHand o.id o.owner)

def finishRevealPutCreaturesStep (g : Game) (p : PlayerId)
    (remaining put enteredFromIds : Array ObjectId)
    (cause : Option EventCause := none) : Game := Id.run do
  if let .chooseReplacement .. := g.pending then
    return g.chainPendingReplacement
      (.finishPostStep (.revealPutCreaturesStep p remaining put enteredFromIds cause))
  let mut g := g
  let mut entered := enteredFromIds
  for i in [0:remaining.size] do
    let id := remaining[i]!
    match g.findObject? id with
    | some o =>
      if put.contains id && g.isCreature o && o.zone == .library p then
        let (g', _) := g.putOntoBattlefield id p (cause := cause)
        g := g'
        entered := entered.push id
      else if o.zone == .library o.owner then
        let (g', _) := g.move id (.graveyard o.owner) none (cause := cause)
        g := g'
      if let .chooseReplacement .. := g.pending then
        let rem := remaining.extract (i + 1) remaining.size
        return g.chainPendingReplacement
          (.finishPostStep (.revealPutCreaturesStep p rem put entered cause))
    | none => pure ()
  for k in [0:entered.size] do
    let fromId := entered[k]!
    match g.followMovedToZone? fromId (· == .battlefield) with
    | some enteredObj =>
      g := g.logMsg s!"{(g.player p).name} puts {g.name enteredObj} onto the battlefield"
      g := g.afterPermanentEnters enteredObj
      if let .chooseReplacement .. := g.pending then
        let remEntered := entered.extract (k + 1) entered.size
        return g.chainPendingReplacement
          (.finishPostStep (.revealPutCreaturesStep p #[] put remEntered cause))
    | none => pure ()
  return g

def finishRevealPutCreatures (g : Game) (p : PlayerId) (looked put : Array ObjectId) : Game :=
  let (g0, cause?) : Game × Option EventCause :=
    if looked.isEmpty then (g, none)
    else
      let (g, c) := g.allocDelayedCause (some p)
      (g, some c)
  g0.withBatch cause? fun g =>
    g.finishRevealPutCreaturesStep p looked put #[] (cause := cause?)

end Game
end Mtg.Engine
