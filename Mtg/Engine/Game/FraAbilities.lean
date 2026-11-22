import Mtg.Engine.Game.FraHelpers

/-!
# Reality Fracture activated and loyalty abilities

Resolutions used by FRA activated abilities, loyalty abilities, and the
emblems and effects those create. `applyFra` delegates them here.
-/

namespace Mtg.Engine
namespace Game

/-- Ask `p` which of `options` the permanent `id` gains until end of turn. -/
def beginChooseKeyword (g : Game) (p : PlayerId) (id : ObjectId) (options : Array KeywordChoice) : Game :=
  match g.findObject? id with
  | some o =>
    if !o.isOnBattlefield then g
    else
      let names := String.intercalate ", " (options.toList.map KeywordChoice.name)
      g.beginFraChoice p (.chooseKeyword id options)
        s!"{(g.player p).name} chooses {names} for {g.name o}"
  | none => g

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
      g.createEffect (.fraEmblemUntilTurnOf obj.id q) (cause := some effCause)
    | none => g

/-- Ask the next player in `players` to sacrifice a creature for Garruk,
Veiled Butcher, or sacrifice the chosen creatures and finish. -/
def continueSacrificeEach (g : Game) (controller : PlayerId) (players : Array PlayerId)
    (chosen : Array ObjectId) : Game :=
  match (players.filter (fun p => !(g.creaturesControlledBy p).isEmpty)).toList with
  | p :: rest =>
    g.beginFraChoice p (.sacrificeCreatureEach controller rest.toArray chosen)
      s!"{(g.player p).name} sacrifices a creature"
  | [] =>
    let youSacrificed := chosen.any (fun id =>
      (g.findObject? id).any (fun o => o.isOnBattlefield && g.controlledBy o controller))
    let pairs := chosen.filterMap (fun id =>
      match g.findObject? id with
      | some o =>
        if o.isOnBattlefield then some ((g.controllerOf o).getD o.owner, id)
        else none
      | none => none)
    let preBf := g.battlefield
    g.withBatch none fun g =>
      g.sacrificePermanentsLoop pairs (preBattlefield := some preBf)
        (createBeastFor := if youSacrificed then some controller else none)

/-- Count nonland cards actually discarded by each opponent in `oppIds` since
`startIdx` (CR 701.9c: face-up nonland cards moved from that opponent's hand to
a different public zone with `.discard`) and draw `baseDraws + shortCount`
cards for `controller` (CR 101.4 / 603.2c / 614.6 / 701.9b–c). -/
def finishDiscardTwoDraws (g : Game) (controller : PlayerId) (baseDraws : Nat)
    (oppIds : Array PlayerId) (startIdx : Nat) : Game :=
  let nonlandDiscardedBy (opp : PlayerId) : Nat :=
    (g.events.extract startIdx g.events.size).foldl (fun acc e =>
      match e.change with
      | .rules (.zone (.moved _ after (.hand q) toZone .discard _ _ _)) =>
        if q == opp && toZone != .hand q && isPublicZone toZone &&
            !after.faceDown && !after.types.contains .land then
          acc + 1
        else acc
      | _ => acc) 0
  let shortCount := (oppIds.filter (fun opp => g.stillInGame opp && nonlandDiscardedBy opp < 2)).size
  let totalDraws := baseDraws + shortCount
  if g.stillInGame controller && totalDraws > 0 then
    g.draw controller totalDraws
  else g

/-- Collect each living opponent's two-card discard choice in APNAP order for
Garruk, Veiled Butcher, then discard all chosen cards simultaneously inside one
shared batch and draw a card for each opponent who didn't discard two nonland
cards (CR 101.4 / 603.2c / 614.6 / 701.9b–c). -/
partial def continueDiscardTwo (g : Game) (controller : PlayerId) (players : Array PlayerId)
    (draws : Nat) (chosen : Array (PlayerId × Array ObjectId) := #[]) : Game :=
  let living := players.filter g.stillInGame
  match living.toList with
  | [] =>
    let livingChosen := chosen.filter (fun (p, _) => g.stillInGame p)
    let oppIds := livingChosen.map Prod.fst
    let pairs := livingChosen.foldl (fun acc (p, ids) =>
      acc ++ ids.map (fun id => (p, id))) #[]
    let startIdx := g.events.size
    let g :=
      if pairs.isEmpty then g
      else
        g.withBatch none fun g =>
          g.discardMultiHandIdsLoop pairs (logEach := true)
    if let .chooseReplacement .. := g.pending then
      g.chainPendingReplacement
        (.finishPostStep (.finishDiscardTwoDraws controller draws oppIds startIdx))
    else
      g.finishDiscardTwoDraws controller draws oppIds startIdx
  | p :: rest =>
    let hand := (g.player p).hand
    if hand.size ≤ 2 then
      let g :=
        if hand.isEmpty then g.logMsg s!"{(g.player p).name} has no cards to discard" else g
      g.continueDiscardTwo controller rest.toArray draws (chosen.push (p, hand))
    else
      g.beginFraChoice p (.discardTwo controller rest.toArray draws chosen)
        s!"{(g.player p).name} discards two cards"

/-- Creatures attacking `p` directly (not a planeswalker). -/
def creaturesAttackingPlayer (g : Game) (p : PlayerId) : Array GameObject :=
  g.battlefield.filter (fun o =>
    g.isCreature o && o.status.attacking && o.status.attackingTarget == some (.player p))

/-- Run Hawkeye's Trick Arrows modes starting at `targetIdx`, pausing on
`Pending.chooseReplacement` so mode 2's choice or later modes do not clobber it. -/
def runHawkeyeArrows (g : Game) (controller : PlayerId) (modes : Array Nat)
    (targets : Array Target) (targetIdx : Nat) (sourceId : Option ObjectId) : Game := Id.run do
  let src := sourceId.bind g.damageSourceById?
  let illegal := some "The target is no longer legal"
  let mut g := g
  let mut idx := targetIdx
  for k in [0:modes.size] do
    let m := modes[k]!
    let slice := targets.extract idx (idx + 1)
    match m with
    | 0 =>
      g := g.withLegalSpecPermanent controller .creature slice (fun g o =>
        (g.createEffect (.cantBlockUntilEot o.id)).logMsg
          s!"{g.name o} can't block this turn") sourceId illegal
      idx := idx + 1
    | 1 =>
      g := g.withLegalSpecPlayer controller .player slice
        (fun g pid => g.dealDamageToPlayer pid 2 (source := src)) sourceId illegal
      idx := idx + 1
    | _ =>
      if (g.player controller).hand.isEmpty then
        g := g.draw controller 1
      else
        g := g.beginFraChoice controller .discardThenDraw
          s!"{(g.player controller).name} discards a card, then draws a card"
    if let .chooseReplacement .. := g.pending then
      let rem := modes.extract (k + 1) modes.size
      if !rem.isEmpty then
        g := g.chainPendingReplacement
          (.finishPostStep (.hawkeyeArrows controller rem targets idx sourceId))
      return g
  return g

/-- Finish `.sarumanExileCopyMayCast` after `fromId`'s exile move (and any
CR 616.1 replacement choice) completes, creating a card-copy and opening
`.mayCastCopy` only if `fromId` actually arrived in `.exile` (CR 614.6 / 707.12). -/
def finishSarumanExileCopyMayCast (g : Game) (controller : PlayerId) (fromId : ObjectId)
    (cause : EventCause) : Game :=
  match g.followMovedToZone? fromId (· == .exile) with
  | none => g
  | some card =>
    let name := g.name card
    let g := g.logMsg s!"{name} is exiled"
    if !g.stillInGame controller then g
    else
      let base := g.copiableValues card
      let copyId : ObjectId := ⟨g.nextObjectId⟩
      let copyTs := g.timestamp + 1
      let copyObj : GameObject := {
        id := copyId
        printed := { base with
          isToken := false
          otherFace := base.otherFace.map (fun f => { f with isToken := false }) }
        owner := controller
        controller := some controller
        zone := .exile
        timestamp := copyTs
        isCopy := true
      }
      let g := g.record (GameEvent.created g.turnNumber controller (g.snapshot copyObj)
        (cause := cause))
      g.beginFraChoice controller (.mayCastCopy copyId)
        s!"{(g.player controller).name} may cast the copy of {name} without paying its mana cost"

/-- Run the library-reveal, put-onto-battlefield, and bottoming tail of
`.identityEcho` once the target permanent's exile completes. -/
def finishIdentityEchoAfterExile (g : Game) (controller : PlayerId)
    (exiledId : ObjectId) (sourceId : Option ObjectId) (oName : String) : Game :=
  let g :=
    if (g.followMovedToZone? exiledId (· == .exile)).isSome then
      g.logMsg s!"{oName} is exiled"
    else g
  if !g.stillInGame controller then g
  else
  let lib := (g.player controller).library
  let (revealed, hit) := Id.run do
    let mut revealed : Array ObjectId := #[]
    for i in [0:lib.size] do
      let id := lib[lib.size - 1 - i]!
      let c := g.object! id
      if g.isCreature c || g.isPlaneswalker c then
        return (revealed, some id)
      revealed := revealed.push id
    return (revealed, none)
  let allRevealed := revealed ++ hit.toArray
  let (g, revealCause?) : Game × Option EventCause :=
    if !allRevealed.isEmpty then
      let (g, c) := g.allocDelayedCause (some controller) sourceId
      (g, some c)
    else (g, none)
  let g :=
    if allRevealed.isEmpty then g
    else g.record (GameEvent.revealed g.turnNumber controller allRevealed (cause := revealCause?))
  let g := allRevealed.foldl (fun g id =>
    g.logMsg s!"{(g.player controller).name} reveals {g.name (g.object! id)}") g
  match hit with
  | some id =>
    let (g, newId) := g.putOntoBattlefield id controller (cause := revealCause?)
    if let .chooseReplacement .. := g.pending then
      g.chainPendingReplacement
        (.finishPostStep (.enteredBattlefieldPutRestBottomRandom controller id revealed revealCause?))
    else
      let g :=
        match g.findObject? newId with
        | some entered =>
          if entered.isOnBattlefield then
            let g := g.logMsg s!"{g.name entered} enters the battlefield"
            g.afterPermanentEnters entered
          else g
        | none => g
      if revealed.isEmpty then g
      else
        g.requestOrderInto revealed (.library controller)
          s!"{(g.player controller).name} puts the rest on the bottom of their library in a random order"
          (cause := revealCause?)
  | none =>
    let g := g.logMsg "No creature or planeswalker card is revealed"
    if revealed.isEmpty then g
    else
      g.requestOrderInto revealed (.library controller)
        s!"{(g.player controller).name} puts the rest on the bottom of their library in a random order"
        (cause := revealCause?)

/-- Bounce each `remaining` target permanent one at a time, pausing across
`Pending.chooseReplacement` so subsequent target legality checks do not run
before an earlier replacement resolves. -/
partial def bounceEachTargetLoop (g : Game) (controller : PlayerId) (spec : TargetSpec)
    (remaining : Array (Nat × Target)) (sourceId : Option ObjectId) : Game :=
  match remaining[0]? with
  | none => g
  | some (i, t) =>
    let rest := remaining.extract 1 remaining.size
    let g :=
      match t with
      | Target.permanent id =>
        if g.targetLegalAt controller spec i t sourceId then
          match g.findObject? id with
          | some o => g.returnToHand id o.owner
          | none => g
        else g.illegalAbilityTarget t
      | _ => g
    if rest.isEmpty then g
    else if let .chooseReplacement .. := g.pending then
      g.chainPendingReplacement
        (.finishPostStep (.bounceEachTargetLoop controller spec rest sourceId))
    else
      g.bounceEachTargetLoop controller spec rest sourceId

/-- Untap each `remaining` target permanent one at a time, pausing across
`Pending.chooseReplacement` before checking subsequent targets. -/
partial def untapTargetsLoop (g : Game) (controller : PlayerId) (spec : TargetSpec)
    (remaining : Array (Nat × Target)) (sourceId : Option ObjectId) : Game :=
  match remaining[0]? with
  | none => g
  | some (i, t) =>
    let rest := remaining.extract 1 remaining.size
    let g :=
      match t with
      | Target.permanent id =>
        if g.targetLegalAt controller spec i t sourceId then
          match g.findObject? id with
          | some o => g.untapPermanentLogged o
          | none => g
        else g.illegalAbilityTarget t
      | _ => g
    if rest.isEmpty then g
    else if let .chooseReplacement .. := g.pending then
      g.chainPendingReplacement
        (.finishPostStep (.untapTargetsLoop controller spec rest sourceId))
    else
      g.untapTargetsLoop controller spec rest sourceId

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

end Game
end Mtg.Engine
