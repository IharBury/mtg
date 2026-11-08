import Mtg.Engine.Game.FraAbilities
import Mtg.Engine.Game.FrcResolve

/-!
# Reality Fracture effect resolution

`applyFra` resolves former Reality Fracture steps of `Resolution` for
spells, activated abilities, and triggered abilities. Choices made while
one resolves leave a `Pending.fraChoice`; `FraChoices` finishes them.
-/

namespace Mtg.Engine
namespace Game

/-- Tap and put a stun counter on each still-legal target in `remaining`,
pausing and chaining `.finishPostStep .tapAndStunTargetsLoop` across CR 616.1
counter-replacement choices inside the caller's batch. -/
def tapAndStunTargetsLoop (g : Game) (controller : PlayerId) (kind : EffectTargetKind)
    (remaining : Array (Nat × Target)) (sourceId : Option ObjectId)
    (cause : Option EventCause) : Game := Id.run do
  let mut g := g
  for i in [0:remaining.size] do
    let (slotIdx, t) := remaining[i]!
    match t with
    | Target.permanent id =>
      if g.targetLegalAt controller kind slotIdx t sourceId then
        if let some o := g.findObject? id then
          let g' := if o.status.tapped then g else g.becomeTapped o (cause := cause)
          let cur := g'.object! o.id
          g := g'.putCountersDeferredLog cur.id .stun 1 (g'.controllerOf cur) .isPutOn (cause := cause)
          if let .chooseReplacement .. := g.pending then
            let rem := remaining.extract (i + 1) remaining.size
            if !rem.isEmpty then
              g := g.chainPendingReplacement
                (.finishPostStep (.tapAndStunTargetsLoop controller rem sourceId cause))
            return g
      else
        g := g.illegalAbilityTarget t
    | _ => pure ()
  return g

/-- Put `n` +1/+1 counters on each `remaining` target permanent using its slot
index `i`, pausing across `Pending.chooseReplacement` so subsequent target
legality checks do not run before an earlier replacement resolves. -/
partial def plusOneOnEachTargetLoop (g : Game) (controller : PlayerId)
    (kind : EffectTargetKind) (remaining : Array (Nat × Target)) (n : Nat)
    (sourceId : Option ObjectId) : Game :=
  match remaining[0]? with
  | none => g
  | some (i, t) =>
    let rest := remaining.extract 1 remaining.size
    let g :=
      match t with
      | Target.permanent id =>
        if g.targetLegalAt controller kind i t sourceId then
          match g.findObject? id with
          | some o => g.addPlusOnePlusOneTo o n
          | none => g
        else g.illegalAbilityTarget t
      | _ => g
    if rest.isEmpty then g
    else if let .chooseReplacement .. := g.pending then
      g.chainPendingReplacement
        (.finishPostStep (.plusOneOnEachTargetLoop controller kind rest n sourceId))
    else
      g.plusOneOnEachTargetLoop controller kind rest n sourceId

/-- Put `x` `.minusOneMinusOne` counters on each `remaining` target permanent using its slot
index `i`, pausing across `Pending.chooseReplacement` before checking subsequent
targets. -/
partial def minusOnesPerOpponentLoop (g : Game) (controller : PlayerId)
    (kind : EffectTargetKind) (remaining : Array (Nat × Target)) (x : Nat)
    (sourceId : Option ObjectId) : Game :=
  match remaining[0]? with
  | none => g
  | some (i, t) =>
    let rest := remaining.extract 1 remaining.size
    let g :=
      match t with
      | Target.permanent id =>
        if !g.targetLegalAt controller kind i t sourceId then
          g.illegalAbilityTarget t
        else
          match g.findObject? id with
          | some o =>
            let shielded :=
              match g.controllerOf o with
              | some c =>
                (g.permanentsOf c).any (fun src =>
                  (g.baseCard src).creaturesCantGetMinusCounters && g.retainsPrintedAbilities src)
              | none => false
            if x > 0 && !shielded then
              g.putCountersDeferredLog o.id .minusOneMinusOne x (some controller) .countArePutOn
            else g
          | none => g
      | _ => g
    if rest.isEmpty then g
    else if let .chooseReplacement .. := g.pending then
      g.chainPendingReplacement
        (.finishPostStep (.minusOnesPerOpponentLoop controller kind rest x sourceId))
    else
      g.minusOnesPerOpponentLoop controller kind rest x sourceId

/-- Log token-copy creation and run post-entry hooks for tokens created since
`startEventIdx` once `.copyTokenOfSourceIfNotToken`'s `createToken` completes. -/
def copyTokenOfSourceAfterCreate (g : Game) (controller : PlayerId)
    (cardName : String) (startEventIdx : Nat) : Game :=
  let created := g.tokensCreatedSince startEventIdx
  if created.isEmpty then g
  else
    let g := g.logMsg s!"{(g.player controller).name} creates a token copy of {cardName}"
    let (g, anyPrompt) :=
      created.foldl (fun (g, anyP) tid =>
        match g.findObject? tid with
        | some entered =>
          if entered.isOnBattlefield then
            let g := g.afterPermanentEntersInBatch entered
            let p :=
              match g.findObject? tid with
              | some cur => cur.isOnBattlefield && !g.enteringCausesNoTriggers cur
              | none => false
            (g, anyP || p)
          else (g, anyP)
        | none => (g, anyP)) (g, false)
    if anyPrompt && g.currentBatch.isNone then
      g.promptTriggerTargetsIfNeeded
    else g

/-- Deal `n` damage from `causeSrc` to each opponent in `remainingOpps`,
pausing across `Pending.chooseReplacement` and logging `"{name} deals {dealt} damage"`
only when unprevented damage `dealt > 0` was dealt (CR 615.6). -/
def causeDealsDamageToOpponentsLoop (g : Game) (remainingOpps : Array PlayerId)
    (n : Nat) (name : String) (causeSrc : Option EventObject)
    (cause : Option EventCause)
    (pendingDmg : Option (PlayerId × Nat) := none)
    (startEventIdx : Option Nat := none) : Game := Id.run do
  if let .chooseReplacement .. := g.pending then
    return g.chainPendingReplacement
      (.causeDealsDamageToOpponentsLoop remainingOpps n name causeSrc cause pendingDmg startEventIdx)
  let mut g := g
  let sIdx := startEventIdx.getD g.events.size
  let c := cause.orElse (fun _ => g.currentBatch.bind (·.2))
  if let some (_, startIdx) := pendingDmg then
    let dealt := g.damageDealtSince startIdx
    if dealt > 0 then
      g := g.logMsg s!"{name} deals {dealt} damage"
  for i in [0:remainingOpps.size] do
    let pid := remainingOpps[i]!
    if g.stillInGame pid then
      let startIdx := g.events.size
      g := g.dealDamageToPlayer pid n (sourceSnap := causeSrc) (cause := c)
        (suppressLifelink := true)
      if let .chooseReplacement .. := g.pending then
        let rem := remainingOpps.extract (i + 1) remainingOpps.size
        return g.chainPendingReplacement
          (.causeDealsDamageToOpponentsLoop rem n name causeSrc c (some (pid, startIdx)) (some sIdx))
      let dealt := g.damageDealtSince startIdx
      if dealt > 0 then
        g := g.logMsg s!"{name} deals {dealt} damage"
  g := g.applyAggregatedLifelinkSince sIdx (cause := c)
  return g

/-- Deal `n` damage from `srcName` / `source` to each still-eligible permanent in
`remainingIds`, pausing across `Pending.chooseReplacement` and aggregating
CR 702.15b lifelink life gain once after all recipients' damage has been dealt. -/
def dealDamageFromPermanentsLoop (g : Game) (remainingIds : Array ObjectId)
    (n : Nat) (srcName : String) (source : Option EventObject)
    (cause : Option EventCause) (startEventIdx : Option Nat := none)
    (note : PermanentDamageLoopNote := .none)
    (pendingTarget : Option (ObjectId × Nat × Nat) := none) : Game := Id.run do
  if let .chooseReplacement .. := g.pending then
    return g.chainPendingReplacement
      (.finishPostStep (.dealDamageFromPermanentsLoop remainingIds n srcName source cause startEventIdx note pendingTarget))
  let mut g := g
  let sIdx := startEventIdx.getD g.events.size
  let c := cause.orElse (fun _ => g.currentBatch.bind (·.2))
  let finishNote (game : Game) (oid : ObjectId) (lethal pIdx : Nat) : Game :=
    match note with
    | .excess =>
      let dealt := game.damageDealtToPermanentSince oid pIdx
      game.change (.excessDamageThisWay (dealt - lethal))
    | .markedPermanent =>
      let marked :=
        (game.findObject? oid).any (·.isOnBattlefield) &&
          game.damageDealtToPermanentSince oid pIdx > 0
      if marked then game.change (.permanentDealtDamageThisWay (some oid)) else game
    | _ => game
  if let some (oid, lethal, pIdx) := pendingTarget then
    g := finishNote g oid lethal pIdx
  for i in [0:remainingIds.size] do
    let oid := remainingIds[i]!
    match g.findObject? oid with
    | some o =>
      let eligible : Bool :=
        o.isOnBattlefield &&
          match note with
          | .oppCreatureOrPlaneswalker ctrl =>
            (g.isCreature o || g.isPlaneswalker o) &&
              (g.controllerOf o).any (g.isLivingOpponentOf ctrl ·)
          | _ => true
      if eligible then
        let lethal := if note == .excess then g.lethalDamageThreshold o else 0
        if note == .excess then
          g := g.change (.excessDamageThisWay 0)
        let pIdx := g.events.size
        g := g.dealDamageFrom srcName o (Int.ofNat n) (sourceSnap := source)
          (cause := c) (suppressLifelink := true)
        if let .chooseReplacement .. := g.pending then
          let rem := remainingIds.extract (i + 1) remainingIds.size
          let pend :=
            match note with
            | .excess | .markedPermanent => some (oid, lethal, pIdx)
            | _ => none
          return g.chainPendingReplacement
            (.finishPostStep (.dealDamageFromPermanentsLoop rem n srcName source c (some sIdx) note pend))
        g := finishNote g oid lethal pIdx
    | none => pure ()
  g := g.applyAggregatedLifelinkSince sIdx (cause := c)
  return g

/-- Reveal and move each searched card in `remainingIds` to `controller`'s hand
for `.fblthpSearch`, pausing across `Pending.chooseReplacement`. -/
def fblthpMoveToHandLoop (g : Game) (controller : PlayerId)
    (remainingIds : Array ObjectId) (cause : EventCause) : Game := Id.run do
  if let .chooseReplacement .. := g.pending then
    return g.chainPendingReplacement
      (.finishPostStep (.fblthpMoveToHandLoop controller remainingIds cause))
  let mut g := g
  for i in [0:remainingIds.size] do
    let id := remainingIds[i]!
    match g.findObject? id with
    | some o =>
      let name := o.name
      g := g.logMsg s!"{(g.player controller).name} reveals {name}"
      let (g', _) := g.move id (.hand controller) none (cause := some cause)
      g := g'
      if let .chooseReplacement .. := g.pending then
        let rem := remainingIds.extract (i + 1) remainingIds.size
        if !rem.isEmpty then
          g := g.chainPendingReplacement
            (.finishPostStep (.fblthpMoveToHandLoop controller rem cause))
        return g
    | none => pure ()
  return g

/-- Finish the post-exile return-tapped step of `.exileReturnBrieflyIfMvAtMost`
once the initial exile move (and any CR 616.1 replacement choice) completes,
following `fromId` to `.exile` under CR 614.6 before putting it onto `.battlefield`. -/
def finishExileReturnBrieflyAfterExile (g : Game) (controller : PlayerId) (fromId : ObjectId)
    (cardName : String) (returnable : Bool) (sourceId : Option ObjectId)
    (cause : EventCause) : Game :=
  match g.followMovedToZone? fromId (· == .exile) with
  | none => g
  | some moved =>
    let g := g.logMsg s!"{cardName} is exiled"
    if returnable then
      let (g, back) := g.putOntoBattlefield moved.id controller (tapped := true) (cause := some cause)
      if let .chooseReplacement .. := g.pending then
        g.chainPendingReplacement
          (.finishPostStep (.returnTappedWithEndStepExile controller moved.id sourceId cause))
      else
        let entered := g.object! back
        if entered.isOnBattlefield then
          let g := g.logMsg s!"{cardName} returns to the battlefield tapped under {(g.player controller).name}'s control"
          let src := (sourceId.bind g.findObject?).orElse (fun _ => some entered)
          let g := g.registerDelayedTrigger { controller, source := src, kind := .endStepExile back, cause }
          g.afterPermanentEnters entered
        else g
    else g

/-- Finish the post-move CR 610.3 link step of `.fra .exileUntilSourceLeaves`. -/
def finishFraExileUntilSourceLeaves (g : Game) (srcId fromId : ObjectId) : Game :=
  match g.followMovedToZone? fromId (· == .exile) with
  | none => g
  | some moved =>
    let g :=
      match g.findObject? srcId with
      | some src =>
        if src.isOnBattlefield then g.changeObject src.id (.pushLinkedExile moved.id)
        else g
      | none => g
    let srcName :=
      match g.findObject? srcId with
      | some src => g.name src
      | none => ((g.lastKnownBefore? srcId).map (fun (eo : EventObject) => eo.name)).getD "the source"
    g.logMsg s!"{moved.name} is exiled until {srcName} leaves the battlefield"

/-- Create an exiled card-copy and free-cast permission for an exiled card in
`uldarosCopiesLoop` (CR 707.12 / 608.3f). -/
private def makeUldarosExiledCopy (g : Game) (controller : PlayerId)
    (sourceId : Option ObjectId) (exObj : GameObject) (cause? : Option EventCause) : Game :=
  let g := g.logMsg s!"{exObj.name} is exiled"
  let printed := g.copiableValues exObj
  let copyId : ObjectId := ⟨g.nextObjectId⟩
  let copyTs := g.timestamp + 1
  let copyObj : GameObject := {
    id := copyId
    printed := { printed with
      isToken := false
      otherFace := printed.otherFace.map (fun f => { f with isToken := false }) }
    owner := controller
    controller := some controller
    zone := .exile
    timestamp := copyTs
    isCopy := true
  }
  let g := g.record (GameEvent.created g.turnNumber controller (g.snapshot copyObj)
    (cause := g.resolveOptionalCause cause? (fallbackSrc := sourceId) (fallbackCtrl := some controller)))
  g.createEffect (.playPermission copyId {
    player := controller
    whileExiled := true, withoutManaCost := true, ignoreTiming := true })
    (cause := cause?)

/-- Pause-safe inner loop for `.uldarosCopies` inside the active batch. -/
def uldarosCopiesLoop (g : Game) (controller : PlayerId)
    (sourceId : Option ObjectId) (ids : Array ObjectId)
    (cause? : Option EventCause) (pendingFromId : Option ObjectId := none) : Game := Id.run do
  if let .chooseReplacement .. := g.pending then
    return g.chainPendingReplacement
      (.finishPostStep (.uldarosCopiesLoop controller sourceId ids cause? pendingFromId))
  let mut g := g
  if let some fid := pendingFromId then
    if let some exObj := g.followMovedToZone? fid (· == .exile) then
      g := makeUldarosExiledCopy g controller sourceId exObj cause?
  for i in [0:ids.size] do
    let id := ids[i]!
    if (g.findObject? id).isSome then
      let (g', _) := g.move id .exile none (cause := cause?)
      g := g'
      if let .chooseReplacement .. := g.pending then
        let rem := ids.extract (i + 1) ids.size
        return g.chainPendingReplacement
          (.finishPostStep (.uldarosCopiesLoop controller sourceId rem cause? (some id)))
      if let some exObj := g.followMovedToZone? id (· == .exile) then
        g := makeUldarosExiledCopy g controller sourceId exObj cause?
  return g

/-- Offer `.castCopiesFree` on all exiled card-copies created under `cause?` once
`uldarosCopiesLoop`'s batch has closed. -/
def finishUldarosCopiesOffer (g : Game) (controller : PlayerId)
    (cause? : Option EventCause) : Game :=
  let copies : Array ObjectId :=
    match cause? with
    | none => #[]
    | some c =>
      g.events.filterMap fun e =>
        match e with
        | .rules _ (.zone (.created eo _)) ec _ =>
          if ec == c && eo.zone == .exile then
            eo.id.filter fun cid => (g.findObject? cid).any (fun o => o.zone == .exile && o.isCopy)
          else none
        | _ => none
  if copies.isEmpty then g
  else
    g.beginFraChoice controller (.castCopiesFree copies 6 copies.size)
      s!"{(g.player controller).name} may cast copies with total mana value 6 or less"

partial def applyFra (g : Game) (controller : PlayerId) (effect : Effect) (r : Resolution)
    (targets : Array Target) (sourceId : Option ObjectId)
    (lastKnownPower : Option Int := none) : Game :=
  let kind := effect.targetKind
  let illegal := some "The target is no longer legal"
  let srcName := g.fraSourceName sourceId
  let src? := (g.resolvingSpell.bind g.damageSourceById?).orElse (fun _ => sourceId.bind g.damageSourceById?)
  match r with
  | .frc e => g.applyFrc controller effect e targets sourceId (lastKnownPower := lastKnownPower)
  | .bounce =>
    g.withLegalKindTarget controller kind targets (fun g t =>
      match t with
      | Target.permanent id =>
        match g.findObject? id with
        | some o => g.returnToHand id o.owner
        | none => g
      | Target.card id =>
        match g.findObject? id with
        | some o =>
          if o.zone == .stack then
            if o.isCopy then
              (g.ceaseToExist o.id (cause := some (.stateBased .copyOutsideStackOrBf))).logMsg
                s!"The copy of {g.name o} ceases to exist (CR 704.5e)"
            else g.returnToHand id o.owner
          else g
        | none => g
      | Target.player _ => g) sourceId illegal
  | .exileTarget =>
    g.withLegalKindPermanent controller kind targets (fun g o =>
      let oName := g.name o
      let (g, _) := g.move o.id .exile none
      if let .chooseReplacement .. := g.pending then
        g.chainPendingReplacement (.finishPostStep (.logExiledIfInExile o.id s!"{oName} is exiled"))
      else if (g.followMovedToZone? o.id (· == .exile)).isSome then
        g.logMsg s!"{oName} is exiled"
      else g) sourceId illegal
  | .destroyDrawIfNotAttacking =>
    g.withLegalKindPermanent controller kind targets (fun g o =>
      let wasAttacking := o.status.attacking
      let ctrl := (g.controllerOf o).getD o.owner
      let g := g.destroyPermanent o
      if wasAttacking then g else g.draw ctrl 1) sourceId illegal
  | .damageEachPlayer n =>
    if n == 0 then g
    else
      g.dealDamageToPlayers g.apnapOrder n (source := src?)
        (cause := g.resolvingBatchCause controller sourceId)
  | .damageSourceAt index n =>
    match g.legalPermanentAt? controller kind targets index sourceId with
    | some o => g.dealDamageFrom srcName o n (source := src?)
    | none => g.logMsg "The target is no longer legal"
  | .plusOneAt index n =>
    match g.legalPermanentAt? controller kind targets index sourceId with
    | some o => g.addPlusOnePlusOneTo o n
    | none => g
  | .returnFromGyToBattlefield plusOnes =>
    g.withLegalKindTarget controller kind targets (fun g t =>
      match t with
      | Target.card id =>
        let (g, newId) := g.returnCardToBattlefield controller id plusOnes
        if let .chooseReplacement .. := g.pending then
          g.chainPendingReplacement (.finishPostStep (.returnedToBattlefield id false))
        else
          let entered := g.object! newId
          if entered.isOnBattlefield then g.afterPermanentEnters entered else g
      | _ => g) sourceId illegal
  | .returnFromGyToHand =>
    -- `none` so an “up to one” sequence with no target still continues.
    -- An announced illegal target is reported by `withLegalTarget`.
    g.withLegalKindTarget controller kind targets (fun g t =>
      match t with
      | Target.card id =>
        match g.findObject? id with
        | some o => g.returnToHand id o.owner
        | none => g
      | _ => g) sourceId none
  | .destroyAllNotChosenType =>
    let chosen := g.chooseCreatureTypeFor controller
    let g := g.logMsg s!"{(g.player controller).name} chooses {chosen}"
    let preBf := g.battlefield
    let doomed := (preBf.filter (fun o => g.isCreature o && !g.hasSubtype o chosen)).map (·.id)
    g.withBatch none fun g =>
      g.destroyPermanentsLoop doomed (preBattlefield := some preBf)
  | .searchPlaneswalkerToTop =>
    g.beginLibrarySearch controller (·.isPlaneswalker) "a planeswalker card" .topAfterShuffle
  | .plusOneOnEachTarget n =>
    let indexed := (List.range targets.size).toArray.map fun i => (i, targets[i]!)
    g.withBatch none fun g =>
      g.plusOneOnEachTargetLoop controller kind indexed n sourceId
  | .returnAllNonlandPermanentsFromGy =>
    let ids := (g.player controller).graveyard.filter (fun id =>
      (g.findObject? id).any (fun o =>
        g.isPermanentCard o && !g.isLand o))
    g.withBatch none fun g =>
      g.putToBattlefieldLoop controller ids
  | .drawMilledThisTurn =>
    g.withLegalKindPlayer controller kind targets (fun g pid =>
      g.draw controller (g.loggedMilled pid)) sourceId illegal
  | .exileAllCreaturesEmpower =>
    let startIdx := g.events.size
    let creatureIds := (g.battlefield.filter (g.isCreature ·)).map (·.id)
    let g := g.withBatch none fun g =>
      g.exilePermanentsLoop creatureIds (logExile := true)
    if let .chooseReplacement .. := g.pending then
      g.chainPendingReplacement
        (.finishPostStep (.empowerJaceExiledCount controller startIdx creatureIds))
    else
      let count := creatureIds.foldl (fun acc id =>
        if g.wasPermanentExiled id startIdx then acc + 1 else acc) 0
      g.empowerJace controller count
  | .drawGreatestPowerLoseLife =>
    let n := (g.greatestPowerAmongCreatures controller).toNat
    let before := g.loggedDraws controller
    let g := g.draw controller n
    if let .chooseReplacement .. := g.pending then
      g.chainPendingReplacement (.finishPostStep (.loseLifeForLoggedDraws controller before))
    else
      let drawn := g.loggedDraws controller - before
      g.loseLife controller drawn
  | .revealHandDiscardNonland permanentOnly =>
    g.withLegalKindPlayer controller kind targets (fun g pid =>
      g.beginRevealDiscard controller pid permanentOnly) sourceId illegal
  | .discardHand =>
    g.withBatch none fun g =>
      g.discardHandIdsLoop controller (g.player controller).hand (logEach := true)
  | .drawPerCreatureYouControl =>
    g.draw controller (g.creaturesControlledBy controller).size
  | .extrapolate =>
    let g := g.materializeSideboard controller
    let names := (g.outsideCards controller).foldl (fun acc o =>
      if acc.contains o.name then acc else acc.push o.name) (#[] : Array String)
    if names.size < 2 then
      g.logMsg s!"{(g.player controller).name} has no two cards with different names outside the game"
    else
      g.beginFraChoice controller .extrapolateReveal
        s!"{(g.player controller).name} may reveal two cards with different names from outside the game"
  | .sphinxsApproach =>
    match g.resolvingSpell.bind g.findObject? with
    | some spell =>
      if spell.zone == .stack && !spell.isCopy &&
          (g.sphinxsApproachesInGraveyard controller).size ≥ 4 then
        g.beginFraChoice controller (.sphinxsApproach spell.id)
          s!"{(g.player controller).name} may exile Sphinx's Approach and four cards named Sphinx's Approach"
      else g
    | none => g
  | .plusOneOnWizardTokensExceptRecent =>
    g.withBatch none fun g =>
      (g.permanentsOf controller).foldl (fun g o =>
        if !g.recentTokenIds.contains o.id && o.printed.isToken && g.hasSubtype o .wizard then
          g.addPlusOnePlusOneTo o 1
        else g) g
  | .damageEachOppCreatureAndPlaneswalker n =>
    let victimIds := (g.battlefield.filter (fun o =>
      (g.isCreature o || g.isPlaneswalker o) &&
        (g.controllerOf o).any (g.isLivingOpponentOf controller ·))).map (·.id)
    if n == 0 || victimIds.isEmpty then g
    else
      let batchCause := g.resolvingBatchCause controller sourceId
      let srcSnap := src?.map g.snapshotDamageSource
      if let .chooseReplacement .. := g.pending then
        g.dealDamageFromPermanentsLoop victimIds n srcName srcSnap batchCause
          (note := .oppCreatureOrPlaneswalker controller)
      else
        g.withBatch batchCause fun g =>
          g.dealDamageFromPermanentsLoop victimIds n srcName srcSnap batchCause
            (note := .oppCreatureOrPlaneswalker controller)
  | .loseAbilitiesAt index =>
    match g.legalPermanentAt? controller kind targets index sourceId with
    | none => g.logMsg "The target is no longer legal"
    | some o =>
      let nm := g.name o
      let g := g.createEffect (.losesAbilitiesUntilEot o.id)
      g.logMsg s!"{nm} loses all abilities until end of turn"
  | .powerDamageFromTo fromIdx toIdx =>
    match g.legalPermanentAt? controller kind targets toIdx sourceId with
    | none => g.logMsg "The target is no longer legal. No damage is dealt"
    | some victim =>
      match g.legalPermanentAt? controller kind targets fromIdx sourceId with
      | some striker =>
        g.dealDamageFrom (g.name striker) (g.object! victim.id) (max (g.power striker) 0)
          (source := some striker)
      | none => g.logMsg "The target is no longer legal. No damage is dealt"
  | .clashOfElements =>
    let sid := sourceId.orElse (fun _ => g.resolvingSpell)
    g.withLegalKindPermanent controller kind targets (fun g o =>
      g.beginFraChoice o.owner (.topOrBottomDamage o.id 2 sid)
        s!"{(g.player o.owner).name} may put {g.name o} on top of their library") sourceId illegal
  | .entrustTheSpark =>
    if (g.permanentsOf controller).any (g.isPlaneswalker ·) then
      g.beginFraChoice controller .maySacrificePlaneswalker
        s!"{(g.player controller).name} may sacrifice a planeswalker"
    else g.logMsg s!"{(g.player controller).name} controls no planeswalker to sacrifice"
  | .plusOnePerThreeGraveyardOnRecentIfFromGy =>
    let fromGy := g.resolvingSpell.any g.castFromGraveyard
    let counters := if fromGy then (g.player controller).graveyard.size / 3 else 0
    if counters == 0 then g
    else
      g.withBatch none fun g =>
        g.recentTokenIds.foldl (fun g id =>
          match g.findObject? id with
          | some o => if o.isOnBattlefield then g.addPlusOnePlusOneTo o counters else g
          | none => g) g
  | .grantHasteToRecentTokens =>
    g.withBatch none fun g =>
      g.recentTokenIds.foldl (fun g id =>
        match g.findObject? id with
        | some o => g.grantKeywordsUntilEot o Keyword.haste
        | none => g) g
  | .drawOneOrTwoIfNotFromHand =>
    let fromHand := g.resolvingSpell.any g.castFromHand
    g.draw controller (if fromHand then 1 else 2)
  | .destroyAt index =>
    match g.legalPermanentAt? controller kind targets index sourceId with
    | some o => g.destroyPermanent o
    | none => g.logMsg "The target is no longer legal"
  | .plusOneOnCreaturesOfPlayerAt index =>
    match targets[index]? with
    | some t@(Target.player pid) =>
      if g.targetLegalAt controller kind index t sourceId then
        g.withBatch none fun g =>
          (g.creaturesControlledBy pid).foldl (fun g o => g.addPlusOnePlusOneTo o 1) g
      else g.logMsg "The target is no longer legal"
    | _ => g.logMsg "The target is no longer legal"
  | .exileReturnBrieflyIfMvAtMost n =>
    g.withLegalKindPermanent controller kind targets (fun g o =>
      -- Ruling: the mana value is that of the permanent as it last existed
      -- on the battlefield.
      let mv := g.objectManaValue o
      let oName := g.name o
      let returnable := mv ≤ n && !o.printed.isToken
      let (g, cause) := g.allocDelayedCause (some controller) sourceId
      let (g, _) := g.move o.id .exile none (cause := some cause)
      if let .chooseReplacement .. := g.pending then
        g.chainPendingReplacement
          (.finishPostStep (.exileReturnBrieflyAfterExile controller o.id oName returnable sourceId cause))
      else
        g.finishExileReturnBrieflyAfterExile controller o.id oName returnable sourceId cause) sourceId illegal
  | .eachPlayerMayWheel n =>
    match g.apnapFrom.toList with
    | [] => g
    | p :: rest =>
      g.beginFraChoice p (.mayWheel n rest.toArray #[])
        s!"{(g.player p).name} may discard their hand and draw {n} cards"
  | .mountainsAddExtraRed =>
    let g := g.createEffect (.mountainExtraRedThisTurn controller)
    g.logMsg s!"Until end of turn, whenever {(g.player controller).name} taps a Mountain for mana, they add an additional \{R}"
  | .searchLandToGraveyard =>
    g.beginLibrarySearch controller (·.isLand) "a land card" .graveyard
  | .counterTarget =>
    g.withLegalKindTarget controller kind targets (fun g t =>
      match t with
      | Target.card id => g.counterStackSpell id
      | _ => g) sourceId illegal
  | .counterUnlessPays n =>
    g.withLegalKindTarget controller kind targets (fun g _ =>
      g.beginPayOrLetCounter targets n) sourceId illegal
  | .destroyTarget =>
    g.withLegalKindPermanent controller kind targets (fun g o => g.destroyPermanent o)
      sourceId illegal
  | .damageExileIfDies n =>
    g.withLegalKindPermanent controller kind targets (fun g o =>
      let g := g.createEffect (.exileIfDiesUntilEot o.id)
      g.dealDamageFrom srcName (g.object! o.id) n (source := src?)) sourceId illegal
  | .millMayPutPermanentGainLife n life =>
    let lib := (g.player controller).library
    let count := min n lib.size
    let preIds := (lib.extract (lib.size - count) lib.size).reverse
    let g := g.mill controller n
    if let .chooseReplacement .. := g.pending then
      g.chainPendingReplacement (.finishPostStep (.offerPutMilledPermanentOrGainLife controller preIds life))
    else
      let choices := preIds.filterMap fun id =>
        match g.followMilledPublic? id with
        | some o => if g.isPermanentCard o then some o.id else none
        | none => none
      if choices.isEmpty then g.gainLife controller life
      else
        g.beginFraChoice controller (.mayPutMilledPermanent choices life)
          s!"{(g.player controller).name} may put a permanent card milled this way into their hand"
  | .chooseTriggerModes _ => g
  | .untapAllLandsYouControl =>
    g.withBatch none fun g =>
      (g.permanentsOf controller).foldl (fun g o =>
        if g.isLand o && o.status.tapped then g.applyPermanentAction (g.object! o.id) .untap
        else g) g
  | .blink =>
    if targets.isEmpty then g
    else
      g.withLegalKindPermanent controller kind targets (fun g o =>
        g.flickerPermanents #[o.id] (logText := "is exiled and returns to the battlefield")) sourceId illegal
  | .mayMovePlusOneToEachOther =>
    match sourceId.bind g.findObject? with
    | some o =>
      if o.isOnBattlefield && o.status.plusOnePlusOne > 0 then
        g.beginFraChoice controller (.mayMovePlusOne o.id)
          s!"{(g.player controller).name} may remove a +1/+1 counter from {g.name o}"
      else g
    | none => g
  | .empowerJacePerCreature =>
    g.empowerJace controller (g.creaturesControlledBy controller).size
  | .tapEnchantedUnprepare =>
    let host? : Option GameObject :=
      match sourceId.bind g.findObject? with
      | some src => src.attachedTo.bind g.findObject? |>.filter (·.isOnBattlefield)
      | none =>
        ((sourceId.bind g.lastKnownBefore?).bind (·.attachedTo)).bind g.findObject?
          |>.filter (·.isOnBattlefield)
    match host? with
    | some host =>
      let g := if host.status.tapped then g else g.becomeTapped host
      g.unprepare (g.object! host.id)
    | none => g.logMsg "The Aura isn't attached to a creature"
  | .ownerPutsOnTopOrBottom =>
    if targets.isEmpty then g
    else
      g.withLegalKindPermanent controller kind targets (fun g o =>
        g.beginFraChoice o.owner (.topOrBottomDamage o.id 0)
          s!"{(g.player o.owner).name} puts {g.name o} on the top or bottom of their library")
        sourceId illegal
  | .drawTwoDiscardTwoStun =>
    let g := g.draw controller 2
    if let .chooseReplacement .. := g.pending then
      g.chainPendingReplacement (.finishPostStep (.beginDiscardThenStun controller sourceId))
    else
      let n := Nat.min 2 (g.player controller).hand.size
      if n == 0 then g
      else
        g.beginFraChoice controller (.discardThenStun n sourceId)
          s!"{(g.player controller).name} discards {n} card(s)"
  | .copyTokenOfSourceIfNotToken =>
    match sourceId with
    | none => g
    | some id =>
      let copiable? : Option (CardDef × Bool) :=
        match g.findObject? id with
        | some card => some (g.copiableValues card, card.printed.isToken)
        | none =>
          match g.lastKnownBefore? id with
          | some eo => some (eo.copiable.getD eo.toCardDef, eo.token)
          | none =>
            match g.followMovedToZone? id (fun | .graveyard _ => true | _ => false) with
            | some card => some (g.copiableValues card, card.printed.isToken)
            | none => none
      match copiable? with
      | some (base, false) =>
        let startEventIdx := g.events.size
        let g := g.change (.recentTokenIds #[])
        let (g, _) := g.createToken controller { base with isToken := true } (recordRecent := true)
        if let .chooseReplacement .. := g.pending then
          g.chainPendingReplacement
            (.finishPostStep (.copyTokenOfSourceAfterCreate controller base.name startEventIdx))
        else
          g.copyTokenOfSourceAfterCreate controller base.name startEventIdx
      | some (_, true) => g
      | none => g.logMsg "The card can't be found"
  | .returnSourceFromGy toHand tapped plusOnes =>
    match sourceId.bind g.findObject? with
    | some o =>
      if o.zone != .graveyard o.owner then g.logMsg s!"{o.name} is no longer in the graveyard"
      else if toHand then g.returnToHand o.id o.owner
      else
        let (g, newId) := g.returnCardToBattlefield controller o.id plusOnes (tapped := tapped)
        if let .chooseReplacement .. := g.pending then
          g.chainPendingReplacement (.finishPostStep (.returnedToBattlefield o.id false))
        else
          let entered := g.object! newId
          if entered.isOnBattlefield then g.afterPermanentEnters entered else g
    | none => g.logMsg "The card is no longer in the graveyard"
  | .mayPayThenDestroyPerOpponent n =>
    g.beginFraChoice controller (.mayPayThen n .reflexiveDestroyPerOpponent sourceId)
      s!"{(g.player controller).name} may pay \{{n}}"
  | .damageX =>
    let x := (sourceId.bind g.chosenXOf?).getD 0
    g.withLegalKindTarget controller kind targets (fun g t =>
      match t with
      | Target.player pid => g.dealDamageToPlayer pid x (source := src?)
      | Target.permanent id => g.dealDamageFrom srcName (g.object! id) x (source := src?)
      | Target.card _ => g) sourceId illegal
  | .creaturesGetPowerPerArtifact =>
    let n : Int := Int.ofNat ((g.permanentsOf controller).filter (g.isArtifact ·)).size
    g.withBatch none fun g =>
      (g.creaturesControlledBy controller).foldl (fun g o =>
        g.pumpPermanent (g.object! o.id) n 0) g
  | .plusOnesEqualToHandOnEachCreature =>
    let x := (g.player controller).hand.size
    if x == 0 then g
    else
      g.withBatch none fun g =>
        ((g.creaturesControlledBy controller).map (·.id)).foldl (fun g id =>
          match g.findObject? id with
          | some o => g.addPlusOnePlusOneTo o x
          | none => g) g
  | .searchCardThenDiscardRandom =>
    g.beginLibrarySearch controller (fun _ => true) "card" .handThenDiscardRandom
  | .grantFlashbackUntilEot =>
    g.withLegalKindTarget controller kind targets (fun g t =>
      match t with
      | Target.card id =>
        match g.findObject? id with
        | some o =>
          (g.createEffect (.flashbackUntilEot o.id)).logMsg
            s!"{o.name} gains flashback until end of turn"
        | none => g
      | _ => g) sourceId illegal
  | .mayDiscardThenDamage n =>
    if (g.player controller).hand.isEmpty then g
    else
      g.beginFraChoice controller (.mayDiscardThen (.reflexiveDamageAnyTarget n) sourceId)
        s!"{(g.player controller).name} may discard a card"
  | .maySearchLandsEqualDamage =>
    let n := ((lastKnownPower.orElse (fun _ => g.resolvingAbility.bind g.lastKnownPowerOf?)).getD 0).toNat
    if n == 0 then g
    else
      g.beginFraChoice controller (.mayThen (.searchLandsTapped n) sourceId)
        s!"{(g.player controller).name} may search for up to {n} land cards"
  | .maySearchBasicLandTapped =>
    g.beginFraChoice controller (.mayThen .searchBasicLandTapped sourceId)
      s!"{(g.player controller).name} may search for a basic land card"
  | .returnCauseTapped =>
    match (g.resolvingAbilityObject?.bind (·.fraCauseId)).bind
        (fun id => g.followMovedToZone? id (fun | .graveyard _ => true | _ => false)) with
    | some card =>
      if card.zone == .graveyard card.owner then
        let (g, newId) := g.putOntoBattlefield card.id card.owner (tapped := true)
        if let .chooseReplacement .. := g.pending then
          g.chainPendingReplacement (.finishPostStep (.returnedToBattlefieldTapped card.id false))
        else
          let entered := g.object! newId
          if entered.isOnBattlefield then
            (g.logMsg s!"{g.name entered} returns to the battlefield tapped").afterPermanentEnters entered
          else g
      else g.logMsg s!"{card.name} is no longer in the graveyard"
    | none => g.logMsg "The card is no longer in the graveyard"
  | .sacrificeSource =>
    match sourceId.bind g.findObject? with
    | some o =>
      if o.isOnBattlefield then g.sacrificeToGraveyard o s!"{(g.player controller).name} sacrifices {g.name o}"
      else g
    | none => g
  | .causeDealsDamageToEachOpponent n =>
    let causeObj := (g.resolvingAbilityObject?.bind (·.fraCauseId)).bind g.damageSourceById?
    let causeSnap := causeObj.map g.snapshotDamageSource
    let name := (causeObj.map g.name).getD "The creature"
    if n == 0 then g
    else
      let opps := g.apnapOrder.filter (g.isLivingOpponentOf controller ·)
      let batchCause := g.resolvingBatchCause controller sourceId
      if let .chooseReplacement .. := g.pending then
        g.causeDealsDamageToOpponentsLoop opps n name causeSnap batchCause
      else
        g.withBatch batchCause fun g =>
          g.causeDealsDamageToOpponentsLoop opps n name causeSnap batchCause
  | .exileFromHandUntilLeaves =>
    g.withLegalKindPlayer controller kind targets (fun g pid =>
      let g := g.revealHand pid
      if (g.revealedHandChoices pid false).isEmpty then
        g.logMsg s!"{(g.player pid).name} has no nonland card"
      else
        g.beginFraChoice controller (.exileFromRevealedHand pid sourceId)
          s!"{(g.player controller).name} chooses a nonland card to exile") sourceId illegal
  | .millThenReturnLandTapped n =>
    let g := g.mill controller n
    if let .chooseReplacement .. := g.pending then
      g.chainPendingReplacement (.finishPostStep (.reflexiveReturnLandTapped controller sourceId))
    else
      g.applyFra controller effect .reflexiveReturnLandTapped #[] sourceId
  | .maySacrificeLandForHeartwoods =>
    if (g.permanentsOf controller).any (g.isLand ·) then
      g.beginFraChoice controller (.maySacrificeThen #[.land] (.tappedHeartwoods 2) sourceId)
        s!"{(g.player controller).name} may sacrifice a land"
    else g
  | .uldarosCopies =>
    -- Exile the still-legal targets (one card per card type, no card twice).
    -- One card for each card type: each chosen card needs a type no earlier
    -- card used.
    let (ids, _) := targets.foldl (fun (acc : Array ObjectId × Array CardType) t =>
      let (ids, used) := acc
      match t with
      | Target.card id =>
        match g.findObject? id with
        | some o =>
          if ids.contains id || o.zone != .graveyard controller || g.isLand o then acc
          else
            match (g.types o).find? (fun ty => !used.contains ty) with
            | some ty => (ids.push id, used.push ty)
            | none => acc
        | none => acc
      | _ => acc) (#[], #[])
    let (g, cause?) : Game × Option EventCause :=
      if ids.isEmpty then (g, none)
      else
        let (g, c) := g.allocDelayedCause (some controller) sourceId
        (g, some c)
    let g := g.withBatch cause? fun g =>
      g.uldarosCopiesLoop controller sourceId ids cause?
    if let .chooseReplacement .. := g.pending then
      g.chainPendingReplacement
        (.finishPostStep (.finishUldarosCopiesOffer controller cause?))
    else
      g.finishUldarosCopiesOffer controller cause?
  | .exileCardFromGraveyard =>
    if targets.isEmpty then g
    else
      g.withLegalKindTarget controller kind targets (fun g t =>
        match t with
        | Target.card id =>
          let name := (g.object! id).name
          let (g, _) := g.move id .exile none
          if let .chooseReplacement .. := g.pending then
            g.chainPendingReplacement (.finishPostStep (.logExiledIfInExile id s!"{name} is exiled"))
          else if (g.followMovedToZone? id (· == .exile)).isSome then
            g.logMsg s!"{name} is exiled"
          else g
        | _ => g) sourceId illegal
  | .copyCauseSpell =>
    if !g.stillInGame controller then g
    else
      match g.fraCause? with
      | some spell =>
        if spell.zone != .stack then g.logMsg s!"{g.name spell} is no longer on the stack"
        else
          let cause := g.resolveOptionalCause (g.resolvingOneShotCause controller sourceId)
            (fallbackSrc := sourceId) (fallbackCtrl := some controller)
          let (g, copyId?) := g.copyStackSpellWithId spell controller (some cause)
          match copyId? with
          | none => g
          | some copyId =>
            let targeted := ((g.stackEntry? copyId).map (!·.targets.isEmpty)).getD false
            if !targeted then g
            else
              g.beginFraChoice controller (.newTargetsForCopies #[copyId])
                s!"{(g.player controller).name} may choose new targets for the copy"
      | none => g.logMsg "The spell is no longer on the stack"
  | .eyeOfJace =>
    let g := g.beginSurveil controller 1
    match g.pending with
    | .surveil .. => g.change (.fraAfterLook (some (controller, sourceId, .eyeOfJaceCheck)))
    | _ => g.applyFra controller effect .eyeOfJaceCheck targets sourceId
  | .eyeOfJaceCheck =>
    if (g.player controller).graveyard.size < 7 then g
    else
      let (g, cause?) : Game × Option EventCause :=
        match g.currentResolvingContext? with
        | some (src, ctrl) =>
          let (g, c) := g.allocDelayedCause (ctrl.orElse (fun _ => some controller)) (src.orElse (fun _ => sourceId))
          (g, some c)
        | none => (g, none)
      let g :=
        match sourceId.bind (fun id => (g.findObject? id).filter (·.isOnBattlefield)) with
        | some o =>
          g.sacrificeToGraveyard o s!"{(g.player controller).name} sacrifices {g.name o}" (cause := cause?)
        | none => g
      if let .chooseReplacement .. := g.pending then
        g.chainPendingReplacement (.finishPostStep (.drainOpponents controller 2 sourceId cause?))
      else
        g.drainOpponents controller 2 (sourceId.bind g.damageSourceById?) (cause := cause?)
  | .loyaltyOnEachPlaneswalkerYouControl => g.loyaltyOnEachPlaneswalkerOf controller
  | .causeGains k =>
    match g.fraCause? with
    | some o => if o.isOnBattlefield then g.grantKeywordsUntilEot o k else g
    | none => g
  | .untapSource =>
    match sourceId.bind g.findObject? with
    | some o => if o.isOnBattlefield && o.status.tapped then g.applyPermanentAction o .untap else g
    | none => g
  | .tapAndStunPerOpponent =>
    let pairs := (List.range targets.size).toArray.map fun i => (i, targets[i]!)
    let cause := g.resolvingBatchCause controller sourceId
    g.withBatch cause fun g =>
      g.tapAndStunTargetsLoop controller kind pairs sourceId (g.currentBatch.bind (·.2))
  | .damageCauseController n =>
    match g.fraCauseController? with
    | some pid => g.dealDamageToPlayer pid n (source := src?)
    | none => g
  | .removeUpToCounters n =>
    g.withLegalKindPermanent controller kind targets (fun g o =>
      g.removeUpToCountersFrom controller o n) sourceId illegal
  | .maySacrificeThenEdict =>
    if (g.permanentsOf controller).any (fun o => g.isCreature o || g.isPlaneswalker o) then
      g.beginFraChoice controller
        (.maySacrificeThen #[.creature, .planeswalker] .eachOpponentSacrificesCreature sourceId)
        s!"{(g.player controller).name} may sacrifice a creature or planeswalker"
    else g
  | .sourceGetsCausePower =>
    let x : Int :=
      match g.fraCause? with
      | some o => if o.isOnBattlefield then g.power o
                  else (g.resolvingAbilityObject?.bind (·.fraCausePower)).getD 0
      | none => (g.resolvingAbilityObject?.bind (·.fraCausePower)).getD 0
    match sourceId.bind g.findObject? with
    | some o => if o.isOnBattlefield then g.pumpPermanent o x 0 else g
    | none => g
  | .jiangYangguAlone =>
    if (g.player controller).hand.isEmpty then
      g.applyFra controller effect .drawThenCountersPerDiscard targets sourceId
    else
      g.beginFraChoice controller
        (.discardThen .drawThenCountersPerDiscard sourceId
          (g.resolvingAbilityObject?.bind (·.fraCauseId)))
        s!"{(g.player controller).name} discards a card"
  | .drawThenCountersPerDiscard =>
    let causeId? := g.resolvingAbilityObject?.bind (·.fraCauseId)
    let g := g.draw controller 1
    if let .chooseReplacement .. := g.pending then
      g.chainPendingReplacement (.finishPostStep (.addPlusOnesForLoggedDiscards controller causeId?))
    else
      let n := g.loggedDiscards controller
      match g.fraCause? with
      | some o => if o.isOnBattlefield && n > 0 then g.addPlusOnePlusOneTo o n else g
      | none => g
  | .kothGeomancer =>
    let isMtn :=
      match g.fraCause? with
      | some land => g.hasSubtype land .mountain
      | none =>
        match (g.resolvingAbilityObject?.bind (·.fraCauseId)).bind g.lastKnownBefore? with
        | some eo => eo.subtypes.contains .mountain || eo.changeling
        | none => false
    let g := g.dealDamageToEachOpponent controller 1 (source := src?)
    if !isMtn then g
    else if let .chooseReplacement .. := g.pending then
      g.chainPendingReplacement (.finishPostStep (.addRedManaIfPositive controller 1 sourceId))
    else
      g.addManaLogged controller #[.colored .red] (source := sourceId)
  | .fblthpSearch =>
    let x := (sourceId.bind g.chosenXOf?).getD 0
    let (pickedIds, _) := (g.player controller).library.foldl
      (fun (acc : Array ObjectId × Array String) id =>
        let (picked, names) := acc
        if names.size ≥ x then acc
        else
          match g.findObject? id with
          | some o =>
            if isBasicLandCard (g.baseCard o) && !names.contains (g.name o) then
              (picked.push id, names.push (g.name o))
            else acc
          | none => acc) (#[], #[])
    let (g, cause) := g.allocDelayedCause (some controller) sourceId
    let g := g.record (GameEvent.searched g.turnNumber controller controller pickedIds (cause := some cause))
    let g :=
      if pickedIds.isEmpty then g
      else g.record (GameEvent.revealed g.turnNumber controller pickedIds (cause := some cause))
    let g :=
      if pickedIds.isEmpty then g
      else
        g.withBatch (some cause) fun g =>
          g.fblthpMoveToHandLoop controller pickedIds cause
    if let .chooseReplacement .. := g.pending then
      g.chainPendingReplacement (.finishPostStep (.fblthpShuffleAfterHand controller))
    else
      g.shuffleThen controller .none
  | .untapAllTokensYouControl =>
    g.withBatch none fun g =>
      (g.permanentsOf controller).foldl (fun g o =>
        if o.printed.isToken && o.status.tapped then g.applyPermanentAction (g.object! o.id) .untap
        else g) g
  | .mayDiscardThenSearchEnchantment =>
    if (g.player controller).hand.isEmpty then g
    else
      g.beginFraChoice controller (.mayDiscardThen .searchEnchantmentToHand sourceId)
        s!"{(g.player controller).name} may discard a card"
  | .firstFightsSecond =>
    match g.legalPermanentAt? controller kind targets 0 sourceId,
        g.legalPermanentAt? controller kind targets 1 sourceId with
    | some a, some b => g.fightCreatures a b
    | _, _ => g
  | .minusOnesPerOpponent =>
    let x := (g.player controller).graveyard.foldl (fun acc id =>
      match g.findObject? id with
      | some o => Nat.max acc (g.objectManaValue o)
      | none => acc) 0
    let indexed := (List.range targets.size).toArray.map fun i => (i, targets[i]!)
    g.withBatch none fun g =>
      g.minusOnesPerOpponentLoop controller kind indexed x sourceId
  | .drawPerColorAmongOtherArtifacts =>
    let colors := (g.permanentsOf controller).foldl (fun (acc : ColorSet) o =>
      if g.isArtifact o && some o.id != sourceId then ColorSet.union acc (g.colors o)
      else acc) ColorSet.empty
    g.draw controller ((Color.all.filter colors.contains).length)
  | .untapUnblockable =>
    g.withLegalKindPermanent controller kind targets (fun g o =>
      let oid := o.id
      let g := g.applyPermanentAction o .untap
      if let .chooseReplacement .. := g.pending then
        g.chainPendingReplacement (.finishPostStep (.grantCantBeBlockedIfOnBattlefield oid))
      else
        match g.findObject? oid with
        | some cur => if cur.isOnBattlefield then g.applyPermanentAction cur .cantBeBlocked else g
        | none => g) sourceId illegal
  | .minusPowerPerGraveyard =>
    let n : Int := Int.ofNat (g.player controller).graveyard.size
    g.withLegalKindPermanent controller kind targets (fun g o => g.pumpPermanent o (-n) 0)
      sourceId illegal
  | .plusOneOnEachCreatureYouControl => g.plusOneOnEachCreatureOf controller
  | .plusOneOnSource n =>
    match sourceId.bind g.findObject? with
    | some o => if o.isOnBattlefield then g.addPlusOnePlusOneTo o n else g
    | none => g
  | .sourceFightsTarget =>
    if targets.isEmpty then g
    else
      match sourceId.bind g.findObject? with
      | some src =>
        g.withLegalKindPermanent controller kind targets (fun g o =>
          if src.isOnBattlefield then g.fightCreatures (g.object! src.id) o else g) sourceId illegal
      | none => g
  | .exileUntilSourceLeaves =>
    match sourceId.bind g.findObject? with
    | some src =>
      if !src.isOnBattlefield then g.logMsg s!"{g.name src} has left the battlefield"
      else
        g.withLegalKindPermanent controller kind targets (fun g o =>
          let (g, linkCause) := g.allocDelayedCause (some controller) sourceId
          let (g, _) := g.move o.id .exile none (cause := some linkCause)
          if let .chooseReplacement .. := g.pending then
            g.chainPendingReplacement
              (.finishPostStep (.finishFraExileUntilSourceLeaves src.id o.id))
          else
            g.finishFraExileUntilSourceLeaves src.id o.id) sourceId illegal
    | none => g
  | .destroyEachTarget =>
    let preBf := g.battlefield
    let (g, validIds) := (List.range targets.size).foldl (fun (acc : Game × Array ObjectId) i =>
      let (g, ids) := acc
      let t := targets[i]!
      match t with
      | Target.permanent id =>
        if g.targetLegalAt controller kind i t sourceId then (g, ids.push id)
        else (g.illegalAbilityTarget t, ids)
      | _ => (g, ids)) (g, #[])
    g.withBatch none fun g =>
      g.destroyPermanentsLoop validIds (preBattlefield := some preBf)
  | .damageAny n =>
    g.withLegalKindTarget controller kind targets (fun g t =>
      match t with
      | Target.player pid => g.dealDamageToPlayer pid n (source := src?)
      | Target.permanent id => g.dealDamageFrom srcName (g.object! id) n (source := src?)
      | Target.card _ => g) sourceId illegal
  | .returnFromGyToBattlefieldTapped =>
    g.withLegalKindTarget controller kind targets (fun g t =>
      match t with
      | Target.card id =>
        let (g, newId) := g.returnCardToBattlefield controller id 0 (tapped := true)
        if let .chooseReplacement .. := g.pending then
          g.chainPendingReplacement (.finishPostStep (.returnedToBattlefield id true))
        else
          let entered := g.object! newId
          if entered.isOnBattlefield then g.afterLandEnters entered else g
      | _ => g) sourceId illegal
  | .searchBasicLandTapped => g.resolveSearchBasicLandTapped controller
  | .searchLandsTapped n =>
    g.beginLibrarySearch controller (·.isLand) "a land card" (.battlefield true) (count := n)
  | .searchEnchantmentToHand =>
    g.resolveLibrarySearchToHand controller (·.isEnchantment) "enchantment card"
  | .tappedHeartwoods n => g.createKindTokens controller .heartwood n (tapped := true)
  | .eachOpponentSacrificesCreature =>
    g.beginSacrificeCreatures ((g.livingOpponents controller).map (·.id)) #[]
  | .reflexiveDamageAnyTarget n =>
    g.putReflexiveTrigger controller sourceId
      { targeting := .of .playerOrCreature, resolution := .damageAny n
        phrase := s!"This deals {n} damage to any target" }
  | .reflexiveDestroyPerOpponent =>
    g.putReflexiveTrigger controller sourceId
      { targeting := .of (g.perOpponentKind controller
          { noun := "up to one target creature or planeswalker that player controls"
            types := #[.creature, .planeswalker] })
        allowsZeroTargets := true
        resolution := .destroyEachTarget
        phrase := "For each opponent, destroy up to one target creature or planeswalker that player controls" }
  | .reflexiveReturnLandTapped =>
    g.putReflexiveTrigger controller sourceId
      { targeting := .of (.filtered { noun := "target land card from your graveyard"
                                      zone := .yourGraveyard, types := #[.land] })
        resolution := .returnFromGyToBattlefieldTapped
        phrase := "Return target land card from your graveyard to the battlefield tapped" }

  | .emrakulGrantMana
  | .nextSpellCantBeCountered
  | .identityEcho
  | .destroyDrawIfLegendaryEnchantment
  | .chooseKeyword _
  | .graveyardCardToLibraryBottom
  | .destroyAllCreatures
  | .ownerShufflesIntoLibrary
  | .grantCombatDamageDrawTwo
  | .sourceGetsPowerPerArtifact
  | .pumpPerArtifact
  | .plusOneOnEachWithPlusOne
  | .bounceEachTarget
  | .surveilReturnNoncreatureNonland
  | .addBlueNoncreatureOnly
  | .tapAndStunX
  | .emblemDrawOnCast
  | .empowerJacePerIsland
  | .attackersGetMinusFiveUntilYourTurn
  | .exileOpponentLibrariesButBottom
  | .minusFourMinusOneUntilYourTurn
  | .eachPlayerSacrificesThenBeast
  | .eachOpponentDiscardsTwoDrawPerShort
  | .damageEachCreatureExceptYourTokens _
  | .emblemCreaturesGetTwoTwo
  | .untapTargets
  | .attackersGetTwoTwoTrampleUntilYourTurn
  | .plusOnePerLand
  | .maySacrificeCreatureForBeast
  | .damageUpToOneAndPlayer _
  | .beastToken
  | .causeGetsPump _ _
  | .attackersOfPlayerGetTwoTwoTrample
  | .putCauseCountersOnSource
  | .mayMoveSourceCountersToTarget
  | .mayPayThenProliferate _ _
  | .proliferate _
  | .becomeArtifactCreatureUntilEot
  | .queueMshReflexive _ _
  | .mshReflexive _ _
  | .hawkeyeArrows _
  | .zemoBoastCopies
  | .copySourceSpellXTimes
  | .damageEqualSourcePower
  | .returnSourceToHand
  | .sarumanExileCopyMayCast
  | .extort =>
    g.applyFraAbility controller effect r targets sourceId
  | _ => g

end Game
end Mtg.Engine
