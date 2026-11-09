import Mtg.Engine.Game.LibrarySearch

/-!
# Resolution target helpers (CR 608.2b)

Re-checking target legality as an effect resolves, `applyPermanentAction`
for shared actions on permanents, beginning scry, mill (CR 701.17), and
damage to each matching creature.
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

/-- Apply `f` when the announced target is still legal for `kind` (CR 608.2b). -/
def withLegalKindTarget (g : Game) (controller : PlayerId) (kind : EffectTargetKind)
    (targets : Array Target) (f : Game → Target → Game)
    (sourceId : Option ObjectId := none) (missing : Option String := none) : Game :=
  g.withLegalTarget (g.legalTargetsForKind controller kind sourceId) targets f missing

/-- Apply `f` to a still-legal permanent target of `kind`. -/
def withLegalKindPermanent (g : Game) (controller : PlayerId) (kind : EffectTargetKind)
    (targets : Array Target) (f : Game → GameObject → Game)
    (sourceId : Option ObjectId := none) (missing : Option String := none) : Game :=
  g.withLegalPermanentTarget (g.legalTargetsForKind controller kind sourceId) targets f
    missing

/-- Apply `f` to a still-legal player target of `kind`. -/
def withLegalKindPlayer (g : Game) (controller : PlayerId) (kind : EffectTargetKind)
    (targets : Array Target) (f : Game → PlayerId → Game)
    (sourceId : Option ObjectId := none) (missing : Option String := none) : Game :=
  g.withLegalKindTarget controller kind targets (fun g tgt =>
    match tgt with
    | Target.player pid => f g pid
    | Target.permanent _ | Target.card _ => g.logMsg "The target is no longer legal")
    sourceId missing

/-- Apply `f` when the announced trigger target is still legal (CR 608.2b). -/
def withLegalTriggerTarget (g : Game) (controller : PlayerId) (ab : TriggeredAbility)
    (sourceId : Option ObjectId) (targets : Array Target)
    (f : Game → Target → Game) (noneMsg : String := "The target is no longer legal") : Game :=
  g.withLegalKindTarget controller ab.targetKind targets f sourceId (some noneMsg)

/-- Apply `f` to a still-legal permanent target of a triggered ability. -/
def withLegalTriggerPermanent (g : Game) (controller : PlayerId) (ab : TriggeredAbility)
    (sourceId : Option ObjectId) (targets : Array Target)
    (f : Game → GameObject → Game) (noneMsg : String := "The target is no longer legal") : Game :=
  g.withLegalKindPermanent controller ab.targetKind targets f sourceId (some noneMsg)

/-- Apply `f` to a still-legal player target of a triggered ability. -/
def withLegalTriggerPlayer (g : Game) (controller : PlayerId) (ab : TriggeredAbility)
    (sourceId : Option ObjectId) (targets : Array Target)
    (f : Game → PlayerId → Game) : Game :=
  g.withLegalTriggerTarget controller ab sourceId targets (fun g t =>
    match t with
    | Target.player pid => f g pid
    | _ => g.logMsg "The target is no longer legal")

/-- Deal `n` damage to a still-legal target of `kind`. -/
def applyDamageToKindTarget (g : Game) (controller : PlayerId) (kind : EffectTargetKind)
    (targets : Array Target) (n : Nat) (sourceId : Option ObjectId := none)
    (missing : Option String := none)
    (cause : Option EventCause := none) : Game :=
  g.withLegalKindTarget controller kind targets
    (fun g t => g.dealDamageToTarget t n (source := sourceId.bind g.damageSourceById?) (cause := cause))
    sourceId missing

/-- Sequential pause-safe loop for `exileCreaturesFromGraveyard`. -/
def exileCreaturesFromGraveyardLoop (g : Game) (controller : PlayerId)
    (ids : Array ObjectId) (cause : Option EventCause)
    (pendingFromId : Option ObjectId := none) : Game := Id.run do
  if let .chooseReplacement .. := g.pending then
    return g.chainPendingReplacement
      (.finishPostStep (.exileCreaturesFromGraveyardLoop controller ids cause pendingFromId))
  let mut g := g
  if let some fid := pendingFromId then
    if let some moved := g.followMovedToZone? fid (· == .exile) then
      g := g.createEffect (.playPermission moved.id {
        player := controller
        whileExiled := true
        anyMana := true }) (cause := cause)
      g := g.logMsg
        s!"{moved.name} is exiled. {(g.player controller).name} may cast it for as long as it remains exiled"
  for i in [0:ids.size] do
    let id := ids[i]!
    match g.findObject? id with
    | none => pure ()
    | some o =>
      let name := o.name
      let (g', _) := g.move id .exile none (cause := cause)
      g := g'
      if let .chooseReplacement .. := g.pending then
        let rem := ids.extract (i + 1) ids.size
        return g.chainPendingReplacement
          (.finishPostStep (.exileCreaturesFromGraveyardLoop controller rem cause (some id)))
      if let some moved := g.followMovedToZone? id (· == .exile) then
        g := g.createEffect (.playPermission moved.id {
          player := controller
          whileExiled := true
          anyMana := true }) (cause := cause)
        g := g.logMsg
          s!"{name} is exiled. {(g.player controller).name} may cast it for as long as it remains exiled"
  return g

/-- Exile creature cards from `fromPlayer`'s graveyard and grant `controller`
permission to cast them, spending mana as though it were any type (CR 610.1 / 701.18). -/
def exileCreaturesFromGraveyard (g : Game) (controller fromPlayer : PlayerId)
    (ty : CardType := .creature) : Game :=
  let ids :=
    (g.player fromPlayer).graveyard.filter (fun id =>
      match g.findObject? id with
      | some o => g.hasType o ty
      | none => false)
  if ids.isEmpty then g
  else
    let (g, cause) := g.allocDelayedCause (some controller)
    g.withBatch (some cause) fun g =>
      g.exileCreaturesFromGraveyardLoop controller ids (some cause)

/-- Put `o` on the top (`top`) or bottom of its owner's library, deferring the
log across `Pending.chooseReplacement` and emitting it only if `o` actually
arrives in `.library owner`. -/
def putOnOwnerLibrary (g : Game) (o : GameObject) (top : Bool) : Game :=
  let side := if top then "top" else "bottom"
  let name := o.name
  let owner := o.owner
  let pos : LibraryPosition := if top then .top else .bottom
  let (g, _) := g.move o.id (.library owner) none (libraryPosition := some pos)
  if let .chooseReplacement .. := g.pending then
    g.chainPendingReplacement (.finishPostStep (.logPutOnOwnerLibrary o.id owner name top))
  else if (g.followMovedToZone? o.id (· == .library owner)).isSome then
    g.logMsg s!"{(g.player owner).name} puts {name} on the {side} of their library"
  else g

/-- Apply a shared permanent action (spells, activated abilities, and triggers). -/
def applyPermanentAction (g : Game) (o : GameObject) (action : PermanentAction)
    (sourceId : Option ObjectId := none) : Game :=
  match action with
  | .pump pw tw => g.pumpPermanent o pw tw
  | .pumpAndTrample pw tw => g.pumpAndGrantTrample o pw tw
  | .destroy => g.destroyPermanent o
  | .plusOne n => g.addPlusOnePlusOneTo o n
  | .dealDamage n =>
    g.dealDamageToPermanent o n (source := sourceId.bind g.damageSourceEventById?)
  | .loseIndestructible =>
    let g := g.createEffect (.loseIndestructibleUntilEot o.id)
    g.logMsg s!"{g.name o} loses indestructible until end of turn"
  | .cantBeBlocked => g.grantCantBeBlockedThisTurn o
  | .grantKeywords k =>
    g.grantUntilEotLogged o k
  | .indestructibleCounter => g.addIndestructibleCounter o
  | .doubleStrikeCounter =>
    let cause := g.resolveOptionalCause none (fallbackSrc := sourceId) (fallbackCtrl := g.controllerOf o)
    g.putCountersDeferredLog o.id .doubleStrike 1 (g.controllerOf o) .gets (cause := some cause)
  | .burdenCounter => g.addBurdenCounter o
  | .tap => g.becomeTapped o
  | .untap =>
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
  | .becomeArtifactIndestructible =>
    let g := g.createEffects #[
      .additionalArtifactUntilEot o.id,
      .keywordsUntilEot o.id Keyword.indestructible]
    g.logMsg
      s!"{g.name o} becomes an artifact and gains indestructible until end of turn"
  | .becomePrepared => g.becomePrepared o
  | .tapAndStun =>
    -- Ruling 764: an already tapped creature still gets the stun counter.
    let cause := g.resolveOptionalCause none (fallbackSrc := sourceId) (fallbackCtrl := g.controllerOf o)
    g.withBatch (some cause) fun g =>
      let g := if o.status.tapped then g else g.becomeTapped o (cause := some cause)
      let cur := g.object! o.id
      g.putCountersDeferredLog cur.id .stun 1 (g.controllerOf cur) .isPutOn (cause := some cause)
  | .setBasePT pw tw =>
    let g := g.createEffect (.setBasePTUntilEot o.id (pw, tw))
    g.logMsg s!"{g.name o} has base power and toughness {pw}/{tw} until end of turn"
  | .putOnTopOfLibrary => g.putOnOwnerLibrary o true
  | .putOnBottomOfLibrary => g.putOnOwnerLibrary o false
  | .exile => (g.move o.id .exile none).1
  | .doublePowerAndToughness =>
    g.pumpPermanent o (g.power o) (g.toughness o)

def applyOnPermanent (g : Game) (controller : PlayerId) (kind : EffectTargetKind)
    (targets : Array Target) (action : PermanentAction)
    (sourceId : Option ObjectId := none) (missing : Option String := none) : Game :=
  match action with
  | .dealDamage n =>
    g.applyDamageToKindTarget controller kind targets n sourceId missing
  | _ =>
    g.withLegalKindPermanent controller kind targets (fun g o =>
      g.applyPermanentAction o action (sourceId := sourceId)) sourceId missing

/-- Start surveilling `n` during resolution (CR 701.25): look at the top
`n` cards, put any number into the graveyard and the rest back on top in any
order. -/
def beginSurveil (g : Game) (p : PlayerId) (n : Nat) : Game :=
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
  if !g.stillInGame p then
    return g
  let mut g := g
  if let some name := logCard then
    g := g.logMsg s!"{(g.player p).name} mills {name}"
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
        let name := o.name
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
  if !g.stillInGame p then
    return g
  let mut g := g
  let mut left := maxLeft
  if let some (cid, cname) := pendingCard then
    if (g.followMovedToZone? cid (· == .hand p)).isSome then
      g := g.logMsg
        (if playerPutsStyle then s!"{(g.player p).name} puts {cname} into their hand"
         else s!"{cname} is put into {(g.player p).name}'s hand")
  for i in [0:remainingIds.size] do
    let id := remainingIds[i]!
    match g.findObject? id with
    | some o =>
      if left > 0 && (!requirePublicZone || isPublicZone o.zone) then
        let name := o.name
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
recording `destroyedCountThisWay` (`countNote`), gaining life per destroyed
permanent (`obGainLifeFor`), or logging `logMsgAfter` once all finish. -/
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
    if countNote || obGainLifeFor.isSome then
      allCands.foldl (fun acc id =>
        if g.wasPermanentDestroyed id then acc + 1 else acc) 0
    else 0
  if countNote then
    g := g.change (.permanentsDestroyedThisWay destroyedCount)
  if let some pid := obGainLifeFor then
    if destroyedCount > 0 then
      g := g.gainLife pid destroyedCount (cause := cause)
  if let some msg := logMsgAfter then
    g := g.logMsg msg
  return g

/-- True when permanent `id` was actually exiled from the battlefield by the
effect since `startIdx` (excluding CR 800.4c control-loss departures). -/
def wasPermanentExiled (g : Game) (id : ObjectId) (startIdx : Nat := 0) : Bool :=
  Id.run do
    for i in [startIdx : g.events.size] do
      let idx := g.events.size - 1 - (i - startIdx)
      let e := g.events[idx]!
      match e.change with
      | .rules (.zone (.moved before _ .battlefield toZone _ _ _ _)) =>
        if before.id == some id then
          return toZone == .exile && e.cause? != some (.gameRule .playerLeftGame)
      | _ => pure ()
    return false

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

end Game
end Mtg.Engine
