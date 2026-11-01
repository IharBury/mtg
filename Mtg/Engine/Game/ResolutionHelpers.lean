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
    (fun g t => g.dealDamageToTarget t n (source := sourceId.bind g.findObject?) (cause := cause))
    sourceId missing

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
    g.withBatch (some cause) fun g => Id.run do
      let mut g := g
      for id in ids do
        match g.findObject? id with
        | none => pure ()
        | some o =>
          let name := o.name
          let (g', newId) := g.move id .exile none (cause := some cause)
          g := g'
          g := g.createEffect (.playPermission newId {
            player := controller
            whileExiled := true
            anyMana := true })
            (cause := some cause)
          g := g.logMsg
            s!"{name} is exiled. {(g.player controller).name} may cast it for as long as it remains exiled"
      return g

/-- Put `o` on the top (`top`) or bottom of its owner's library. -/
def putOnOwnerLibrary (g : Game) (o : GameObject) (top : Bool) : Game :=
  let side := if top then "top" else "bottom"
  let name := o.name
  let owner := o.owner
  let pos : LibraryPosition := if top then .top else .bottom
  let (g, _) := g.move o.id (.library owner) none (libraryPosition := some pos)
  g.logMsg s!"{(g.player owner).name} puts {name} on the {side} of their library"

/-- Apply a shared permanent action (spells, activated abilities, and triggers). -/
def applyPermanentAction (g : Game) (o : GameObject) (action : PermanentAction)
    (sourceId : Option ObjectId := none) : Game :=
  match action with
  | .pump pw tw => g.pumpPermanent o pw tw
  | .pumpAndTrample pw tw => g.pumpAndGrantTrample o pw tw
  | .destroy => g.destroyPermanent o
  | .plusOne n => g.addPlusOnePlusOneTo o n
  | .dealDamage n =>
    g.dealDamageToPermanent o n (source := (sourceId.bind g.findObject?).map g.snapshot)
  | .loseIndestructible =>
    let g := g.createEffect (.loseIndestructibleUntilEot o.id)
    g.logMsg s!"{g.name o} loses indestructible until end of turn"
  | .cantBeBlocked => g.grantCantBeBlockedThisTurn o
  | .grantKeywords k =>
    g.grantUntilEotLogged o k
  | .indestructibleCounter => g.addIndestructibleCounter o
  | .doubleStrikeCounter =>
    let cause := g.resolveOptionalCause none (fallbackSrc := sourceId) (fallbackCtrl := g.controllerOf o)
    let g := g.recordPutCounters o.id .doubleStrike 1 (byPlayer := g.controllerOf o)
      (cause := some cause)
    g.logMsg s!"{g.name o} gets a double strike counter"
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
    let g := if o.status.tapped then g else g.becomeTapped o
    let cur := g.object! o.id
    let cause := g.resolveOptionalCause none (fallbackSrc := sourceId) (fallbackCtrl := g.controllerOf cur)
    let g := g.recordPutCounters cur.id .stun 1 (byPlayer := g.controllerOf cur)
      (cause := some cause)
    g.logMsg s!"A stun counter is put on {g.name cur}"
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

/-- Put the top `n` cards of `p`'s library into their graveyard (CR 701.17). -/
def mill (g : Game) (p : PlayerId) (n : Nat) (cause : Option EventCause := none) : Game :=
  let defaultCause :=
    cause.orElse (fun _ =>
      if n == 0 || (g.player p).library.isEmpty then none
      else g.currentResolvingContext?.map fun (src, ctrl) =>
        .oneShotEffect none src (ctrl.orElse (fun _ => some p)))
  g.withBatch defaultCause fun g => Id.run do
    let pl := g.player p
    if n > 0 && pl.library.isEmpty then
      return g.logMsg s!"{pl.name} mills nothing (empty library)"
    let count := min n pl.library.size
    let tops := (pl.library.extract (pl.library.size - count) pl.library.size).reverse
    let mut g := g
    for top in tops do
      let name := (g.object! top).name
      let (g', _) := g.move top (.graveyard p) none (verb := some .mill) (actor := some p)
        (cause := cause)
      g := g'.logMsg s!"{(g'.player p).name} mills {name}"
    if count < n then
      g := g.logMsg s!"{(g.player p).name} mills nothing (empty library)"
    return g

/-- Mill `n`, then put matching milled cards from the graveyard into hand.
`maxPut` limits how many are returned (`none` means all matches). -/
def millThenPutFromGy (g : Game) (p : PlayerId) (n : Nat)
    (pred : GameObject → Bool) (maxPut : Option Nat := none) : Game :=
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
  let milled := tops.filterMap (fun id => (g.followMovedToZone? id (· == .graveyard p)).map (·.id))
  g.withBatch cause? fun g => Id.run do
    let mut g := g
    let mut left := maxPut.getD milled.size
    for id in milled do
      match g.findObject? id with
      | some o =>
        if left > 0 && o.zone == .graveyard p && pred o then
          let name := o.name
          let (g', _) := g.move id (.hand p) none (cause := cause?)
          g := g'.logMsg s!"{(g.player p).name} puts {name} into their hand"
          left := left - 1
      | none => pure ()
    return g

/-- Deal `n` damage to each still-matching creature in `remainingIds`, pausing
and chaining `.dealDamageToEachCreatureMatching` if a CR 616.1 choice opens. -/
def dealDamageToEachCreatureMatchingIds (g : Game) (remainingIds : Array ObjectId) (n : Nat)
    (onlyNonSubtype : Option CardSubtype := none)
    (exceptControllerTokens : Option PlayerId := none)
    (source : Option EventObject := none)
    (cause : Option EventCause := none) : Game := Id.run do
  if let .chooseReplacement .. := g.pending then
    return g.chainPendingReplacement
      (.dealDamageToEachCreatureMatching remainingIds n onlyNonSubtype exceptControllerTokens source cause)
  let mut g := g
  for i in [0:remainingIds.size] do
    let id := remainingIds[i]!
    match g.findObject? id with
    | some o =>
      if o.isOnBattlefield && g.isCreature o &&
          (onlyNonSubtype.all (fun s => !g.hasSubtype o s)) &&
          (exceptControllerTokens.all (fun p => !(o.printed.isToken && g.controlledBy o p))) then
        g := g.dealDamageToPermanent o n (source := source) (cause := cause)
        if let .chooseReplacement .. := g.pending then
          let rem := remainingIds.extract (i + 1) remainingIds.size
          if !rem.isEmpty then
            g := g.chainPendingReplacement
              (.dealDamageToEachCreatureMatching rem n onlyNonSubtype exceptControllerTokens source cause)
          return g
    | none => pure ()
  return g

/-- Deal `n` damage to each creature matching `pred`. -/
def dealDamageToEachCreatureMatching (g : Game) (n : Nat)
    (pred : GameObject → Bool := fun _ => true)
    (source : Option EventObject := none)
    (cause : Option EventCause := none) : Game :=
  let defaultCause :=
    cause.orElse (fun _ =>
      if n == 0 then none
      else g.currentResolvingContext?.map fun (src, ctrl) => .oneShotEffect none src ctrl)
  let ids := (g.battlefield.filter (fun o => g.isCreature o && pred o)).map (·.id)
  g.withBatch defaultCause fun g =>
    g.dealDamageToEachCreatureMatchingIds ids n (source := source) (cause := defaultCause)

/-- Deal `n` damage to each creature that is not `subtype`. -/
def dealDamageToEachNonDragon (g : Game) (n : Nat) (subtype : CardSubtype := .dragon)
    (source : Option EventObject := none)
    (cause : Option EventCause := none) : Game :=
  let defaultCause :=
    cause.orElse (fun _ =>
      if n == 0 then none
      else g.currentResolvingContext?.map fun (src, ctrl) => .oneShotEffect none src ctrl)
  let ids := (g.battlefield.filter (fun o => g.isCreature o && !g.hasSubtype o subtype)).map (·.id)
  g.withBatch defaultCause fun g =>
    g.dealDamageToEachCreatureMatchingIds ids n (onlyNonSubtype := some subtype)
      (source := source) (cause := defaultCause)

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

end Game
end Mtg.Engine
