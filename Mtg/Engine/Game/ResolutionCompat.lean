import Mtg.Engine.Game.TriggerArgs
import Mtg.Engine.Game.CastExtras
import Mtg.Engine.Game.FraAbilities

/-!
# Transitional Resolution Loops & Helpers (CR 608 / 616.1)

Pause-safe resolution loops and helpers shared by `Interpreter.lean`,
`Decisions.lean`, `FraChoices.lean`, `TriggeredAbilities.lean`, and
`SpellResolution.lean` while Phase-9 `PostStep` / `FrcPostStep` continuations
remain active for legacy trigger resolutions.
-/

namespace Mtg.Engine
namespace Game

/-! ### Saga & Linked-Exile Helpers (CR 607.2a / 714.2) -/

/-- The source gains landfall: create a 1/1 green Elf. -/
def gainLandfallCreateElf (g : Game) (sourceId : Option ObjectId) : Game :=
  match sourceId.bind g.findObject? with
  | some src =>
    if !src.isOnBattlefield then g
    else
      let landfall : TriggeredAbility :=
        .onLandYouControlEntersCreateTokens TokenSpec.elf 1
      let g := g.createEffect (.grantedTriggered src.id landfall false)
      g.logMsg s!"{g.name src} gains landfall"
  | none => g

/-- Elves the controller controls get +P/+0 and vigilance until end of turn. -/
def elvesGetVigilance (g : Game) (controller : PlayerId) (power : Int) : Game :=
  g.forEachControlledCreature controller fun g o =>
    if g.hasSubtype o .elf then
      let g := g.pumpPermanent o power 0
      g.createEffect (.keywordsUntilEot o.id #[Keyword.vigilance])
        |>.logMsg s!"{g.name o} gets {signedStat power}/+0 and gains vigilance until end of turn"
    else g

/-- The announced creature gains hexproof while the source remains. -/
def grantHexproofWhileSource (g : Game) (controller : PlayerId)
    (sourceId : Option ObjectId) (targets : Array Target)
    (spec : TargetSpec) : Game :=
  match sourceId with
  | none => g
  | some sid =>
    g.withLegalSpecPermanent controller spec targets (fun g o =>
      let g := g.createEffect (.hexproofWhileSource o.id sid)
      g.logMsg s!"{g.name o} gains hexproof for as long as the Saga remains")
      sourceId (some "The target is no longer legal")

/-- Damage the announced creature would deal is prevented while the source remains. -/
def preventDamageWhileSource (g : Game) (controller : PlayerId)
    (sourceId : Option ObjectId) (targets : Array Target)
    (spec : TargetSpec) : Game :=
  match sourceId with
  | none => g
  | some sid =>
    g.withLegalSpecPermanent controller spec targets (fun g o =>
      let g := g.createEffect (.preventDamageWhileSource o.id sid)
      g.logMsg s!"damage that would be dealt by {g.name o} is prevented while the Saga remains")
      sourceId none

/-- Finish or run sequential exile-to-hand moves for `returnLinkedExileToHand`,
deferring `linkedExile` removal and the hand-arrival log across
`Pending.chooseReplacement` and checking `followMovedToZone?`. -/
def returnLinkedExileToHandLoop (g : Game) (srcId : ObjectId) (ids : Array ObjectId)
    (pendingItem : Option (ObjectId × PlayerId × String) := none) : Game := Id.run do
  if let .chooseReplacement .. := g.pending then
    return g.chainPendingReplacement (.returnLinkedExileToHandLoop srcId ids pendingItem)
  let mut g := g
  if let some (eid, owner, name) := pendingItem then
    if (g.followMovedToZone? eid (· != .exile)).isSome then
      g := g.pruneLinkedExileId srcId eid
    if (g.followMovedToZone? eid (· == .hand owner)).isSome then
      g := g.logMsg s!"{name} is put into {(g.player owner).name}'s hand"
  for i in [0:ids.size] do
    let eid := ids[i]!
    match g.findObject? eid with
    | none => pure ()
    | some card =>
      let owner := card.owner
      let name := g.name card
      let (g', _) := g.move eid (.hand owner) none
      g := g'
      if let .chooseReplacement .. := g.pending then
        let rem := ids.extract (i + 1) ids.size
        return g.chainPendingReplacement
          (.returnLinkedExileToHandLoop srcId rem (some (eid, owner, name)))
      if (g.followMovedToZone? eid (· != .exile)).isSome then
        g := g.pruneLinkedExileId srcId eid
      if (g.followMovedToZone? eid (· == .hand owner)).isSome then
        g := g.logMsg s!"{name} is put into {(g.player owner).name}'s hand"
  return g

/-- A card the source exiled returns to its owner's hand (CR 607.2a / 714.4,
including LKI when the Saga left the battlefield before its chapter resolved). -/
def returnLinkedExileToHand (g : Game) (sourceId : Option ObjectId) : Game :=
  match sourceId with
  | none => g.logMsg "The Saga is no longer in play"
  | some sid =>
    let allIds := g.allLinkedExilesOf sid
    match allIds.find? (fun eid => (g.findObject? eid).any (·.zone == .exile)) with
    | some eid => g.returnLinkedExileToHandLoop sid #[eid]
    | none =>
      if allIds.isEmpty then
        if (g.findObject? sid).isSome then g.logMsg "No card is exiled with this Saga"
        else g.logMsg "The Saga is no longer in play"
      else
        g.logMsg "The exiled card is no longer there"

/-- Whenever the controller attacks this turn, a creature they control
gets +1/+1 for each Plains they control. -/
def attackPumpPerPlains (g : Game) (controller : PlayerId) : Game :=
  let (g, cause) := g.allocDelayedCause (some controller)
  let src :=
    match g.currentResolvingContext? with
    | some (some sid, _) => g.damageSourceById? sid
    | _ => none
  g.registerDelayedTrigger { controller, source := src, kind := .attackPumpPerPlains, cause }
    |>.logMsg
      s!"Whenever {(g.player controller).name} attacks this turn, a creature they control gets +1/+1 for each Plains they control"

/-- Create the 6/6 Dragon token for `treasureThenDragon`, guarding CR 616.1
choices and prevented token creation. -/
def treasureThenDragonCreateDragon (g : Game) (controller : PlayerId) : Game :=
  g.withContinuationFrame fun g =>
    let g := g.change (.recentTokenIds #[])
    let (g, _) := g.createToken controller dragonToken (recordRecent := true)
    if let .chooseReplacement .. := g.pending then
      g.chainPendingReplacement (.finishPostStep .logAndEnterRecentTokens)
    else
      g.recentTokenIds.foldl (fun g tid =>
        match g.findObject? tid with
        | some entered =>
          if entered.isOnBattlefield then
            (g.logMsg s!"{g.name entered} enters the battlefield").afterPermanentEnters entered
          else g
        | none => g) g

/-- Finish `treasureThenDragon` once the Treasure token creation completes. -/
def treasureThenDragonAfterCreate (g : Game) (controller : PlayerId)
    (sourceId : Option ObjectId) : Game :=
  match sourceId.bind g.findObject? with
  | none => g
  | some src =>
    if !src.isOnBattlefield then g
    else if g.countSubtype controller .treasure < 4 then g
    else
      let name := g.name src
      let g := g.sacrificeToGraveyard src s!"{name} is sacrificed"
      if let .chooseReplacement .. := g.pending then
        g.chainPendingReplacement (.finishPostStep (.treasureThenDragonCreateDragon controller))
      else
        g.treasureThenDragonCreateDragon controller

/-- Create a Treasure. Then if the controller has four or more, sacrifice
the source and create a 6/6 red Dragon with flying. -/
def treasureThenDragon (g : Game) (controller : PlayerId)
    (sourceId : Option ObjectId) : Game :=
  let g := g.createTreasureTokens controller 1
  if let .chooseReplacement .. := g.pending then
    g.chainPendingReplacement (.finishPostStep (.treasureThenDragonAfterCreate controller sourceId))
  else
    g.treasureThenDragonAfterCreate controller sourceId

/-- Gain control of the announced creatures while the source remains
(CR 608.2b / 611.2b / 613.7). -/
def gainControlWhileSource (g : Game) (controller : PlayerId)
    (sourceId : Option ObjectId) (targets : Array Target)
    (maxTotalMv : Option Nat := none) : Game :=
  g.withSourceStillOnBattlefield sourceId (fun g src =>
    let legalIds : Array ObjectId := Id.run do
      let mut ids : Array ObjectId := #[]
      for t in targets do
        if let Target.permanent id := t then
          if !ids.contains id then
            if let some o := g.findObject? id then
              let mvOk := maxTotalMv.all (g.objectManaValue o ≤ ·)
              if o.isOnBattlefield && g.isCreature o &&
                  g.canBeTargetedBy controller o sourceId && mvOk then
                ids := ids.push id
      return ids
    let totalMv := legalIds.foldl (fun acc id =>
      match g.findObject? id with
      | some o => acc + g.objectManaValue o
      | none => acc) 0
    if !targets.isEmpty && (legalIds.isEmpty || !maxTotalMv.all (totalMv ≤ ·)) then
      g.logMsg "The target is no longer legal"
    else
      g.withBatch none fun g =>
        legalIds.foldl (fun (g : Game) id =>
          match g.findObject? id with
          | some o =>
            if !g.stillInGame controller then
              g.logMsg s!"{g.name o} does not change control (CR 800.4b)"
            else
              g.createEffect (.controlWhileSource o.id controller src.id)
                |>.logMsg s!"{(g.player controller).name} gains control of {g.name o}"
          | none => g) g)
    "The Super Hero Civil War has left the battlefield. You won't gain control."

/-- All CR 603.4 / 608.2a intervening-“if” conditions rechecked on trigger
resolution before pushing `resolutionFinish`. -/
def triggerInterveningHolds (g : Game) (controller : PlayerId)
    (ab : TriggeredAbility) (sourceId : Option ObjectId)
    (targets : Array Target := #[]) (_lastKnownPower : Option Int := none)
    (fraCauseId : Option ObjectId := none)
    (fraCauseStatus : Option Status := none) : Bool :=
  match ab.interveningIf? with
  | none => true
  | some cond =>
    let src := sourceId.bind g.damageSourceById?
    let cid? :=
      fraCauseId.orElse fun _ =>
        match targets[0]? with
        | some (Target.permanent id) | some (Target.card id) => some id
        | _ => none
    let cause :=
      match cid? with
      | none => none
      | some cid =>
        match g.damageSourceById? cid with
        | some o =>
          match fraCauseStatus with
          | some st =>
            if o.isOnBattlefield then some o else some { o with status := st }
          | none => some o
        | none => none
    g.evalTriggerCond controller src cause cond

/-! ### Explore, Polymorph, Fact-or-Fiction, and Post-Step Helpers -/

private def srcObjOnBf? (g : Game) (sourceId : Option ObjectId) : Option GameObject :=
  sourceId.bind fun id => (g.findObject? id).filter (·.isOnBattlefield)

def handDiscardBack (g : Game) (p : PlayerId) : Game :=
  if !g.stillInGame p then g
  else
    match (g.player p).hand.back? with
    | none => g.logMsg s!"{(g.player p).name} has no card to discard"
    | some id =>
      let card := g.object! id
      let destOwner := card.owner
      let name := g.name card
      let (g, _) := g.move id (.graveyard destOwner) none (verb := some .discard) (actor := some p)
      if let .chooseReplacement .. := g.pending then
        g.chainPendingReplacement (.finishFrcPostStep (.logHandDiscard p id destOwner name))
      else if (g.followMovedToZone? id (· == .graveyard destOwner)).isSome then
        g.logMsg s!"{(g.player p).name} discards {name}"
      else g

def destroyIdsMatching (g : Game) (ids : Array ObjectId)
    (pred : GameObject → Bool := fun _ => true) : Game :=
  let preBf := g.battlefield
  let validIds := ids.filter fun id =>
    match g.findObject? id with
    | some o => o.isOnBattlefield && pred o
    | none => false
  g.withBatch none fun g =>
    g.destroyPermanentsLoop validIds (preBattlefield := some preBf)

def makeFrcLoop (g : Game) (p : PlayerId) (k : TokenSpec) (remaining : Nat) (x : Nat)
    (extraCounters : CounterBag) (cause : Option EventCause)
    (copyCtx : CopyTokenContext := {}) : Game :=
  if remaining == 0 then g
  else if let .chooseReplacement .. := g.pending then
    g.chainPendingReplacement (.makeFrcLoop p k remaining x extraCounters cause copyCtx)
  else
    match k with
    | .copyOf ref mods =>
      let cands := g.resolveCopyTokenCandidates ref mods x copyCtx (controller := p)
      if cands.isEmpty then
        g.logMsg "no token is created (CR 111.5 / 111.12)"
      else if cands.size > 1 then
        let ids := cands.filterMap Prod.fst
        if ids.size > 1 then
          g.beginFraChoice p
            (.chooseTokenCopyObject ids mods remaining false false none extraCounters cause)
            s!"{(g.player p).name} chooses an object to copy"
        else
          (g.createToken p cands[0]!.2 (extraCounters := extraCounters)
            (recordRecent := true) (cause := cause) (count := remaining)).1
      else
        (g.createToken p cands[0]!.2 (extraCounters := extraCounters)
          (recordRecent := true) (cause := cause) (count := remaining)).1
    | _ =>
      match g.resolveTokenPrinted? k x copyCtx (controller := p) with
      | none => g.logMsg "no token is created (CR 111.5 / 111.12)"
      | some printed =>
        (g.createToken p printed (extraCounters := extraCounters)
          (recordRecent := true) (cause := cause) (count := remaining)).1

def makeTokenSpecBatched (g : Game) (p : PlayerId) (k : TokenSpec) (n : Nat := 1) (x : Nat := 0)
    (extraCounters : CounterBag := #[]) (cause : Option EventCause := none)
    (copyCtx : CopyTokenContext := {}) : Game :=
  if let .chooseReplacement .. := g.pending then
    if n == 0 || !g.stillInGame p then g
    else g.chainPendingReplacement (.makeFrcLoop p k n x extraCounters cause copyCtx)
  else if n == 0 || !g.stillInGame p then g.change (.recentTokenIds #[])
  else
    let g := g.change (.recentTokenIds #[])
    let batchCause := cause.orElse (fun _ => g.resolvingBatchCause p none)
    g.withBatch batchCause fun g =>
      g.makeFrcLoop p k n x extraCounters cause copyCtx

/-- Offer `p` the optional explore choice to put the revealed top card `cardId`
of their library into their graveyard (CR 701.44a / 701.44c). -/
def offerExploreMayGraveyard (g : Game) (p : PlayerId) (cardId : ObjectId) : Game :=
  if !g.stillInGame p then g
  else if (g.player p).library.back? != some cardId then g
  else
    let cName := (g.findObject? cardId).map g.name |>.getD "the revealed card"
    g.beginFraChoice p (.exploreMayGraveyard cardId)
      s!"{(g.player p).name} may put {cName} into their graveyard"

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

private def applyDackOnHits (g : Game) (controller : PlayerId) (hits : Array ObjectId)
    (cause : EventCause) : Game :=
  let g :=
    if hits.any (fun id => (g.followMovedToZone? id (· == Zone.battlefield)).isSome) then
      g.withBatch (some cause) fun g =>
        hits.foldl (fun g id =>
          match g.followMovedToZone? id (· == Zone.battlefield) with
          | some o =>
            g.record (GameEvent.designation g.turnNumber (g.snapshot o) (.goaded controller false) true (cause := cause))
          | none => g) g
    else g
  let opps := g.livingOpponents controller
  if opps.isEmpty || !hits.any (fun id => (g.followMovedToZone? id (· == Zone.battlefield)).isSome) then g
  else
    g.withBatch (some cause) fun g =>
      Id.run do
        let mut g := g
        let mut i := 0
        for id in hits do
          match opps[i]?, g.followMovedToZone? id (· == Zone.battlefield) with
          | some opp, some o =>
            g := g.changeControl o opp.id (cause := some cause)
            i := i + 1
          | _, _ => pure ()
        return g

def finishFrcRestBottom (g : Game) (p : PlayerId) (rest : Array ObjectId) (shuffle : Bool)
    (cause : Option EventCause := none) (dackTargets : Array ObjectId := #[]) : Game :=
  let g :=
    if dackTargets.isEmpty then g
    else g.applyDackOnHits p dackTargets (cause.getD (g.resolvingOrRuleCause p))
  g.restBottomCards p rest shuffle (cause := cause)

def handDiscardToBottomOf (g : Game) (controller : PlayerId) : Game :=
  if !g.stillInGame controller then g
  else
    match (g.player controller).hand.back? with
    | none => g
    | some id =>
      let card := g.object! id
      let destOwner := card.owner
      let name := g.name card
      let (g, _) := g.move id (.library destOwner) none (libraryPosition := some .bottom)
      if let .chooseReplacement .. := g.pending then
        g.chainPendingReplacement
          (.finishFrcPostStep (.logHandDiscardToBottom controller id destOwner name))
      else if (g.followMovedToZone? id (· == .library destOwner)).isSome then
        g.logMsg s!"{(g.player controller).name} puts {name} on the bottom of their library"
      else g

/-- Move `remainingIds` from `p`'s hand onto the top of `p`'s library one at a
time, pausing across `Pending.chooseReplacement` and logging the count of cards
that entered `.library p` (CR 614.6 / 616.1). -/
def putBackOnTopLoop (g : Game) (p : PlayerId) (remainingIds : Array ObjectId)
    (movedCount : Nat := 0) (pendingId : Option ObjectId := none) : Game := Id.run do
  if let .chooseReplacement .. := g.pending then
    return g.chainPendingReplacement
      (.finishFrcPostStep (.putBackOnTopLoop p remainingIds movedCount pendingId))
  let mut g := g
  let mut cnt := movedCount
  if let some pid := pendingId then
    if (g.followMovedToZone? pid (· == .library p)).isSome then
      cnt := cnt + 1
  if !g.stillInGame p then
    if cnt > 0 then
      g := g.logMsg s!"{(g.player p).name} puts {cnt} card(s) on top of their library"
    return g
  for i in [0:remainingIds.size] do
    let id := remainingIds[i]!
    match g.findObject? id with
    | some o =>
      if o.zone == .hand p then
        let (g', _) := g.move id (.library p) none
        g := g'
        if let .chooseReplacement .. := g.pending then
          let rem := remainingIds.extract (i + 1) remainingIds.size
          return g.chainPendingReplacement
            (.finishFrcPostStep (.putBackOnTopLoop p rem cnt (some id)))
        if (g.followMovedToZone? id (· == .library p)).isSome then
          cnt := cnt + 1
        if !g.stillInGame p then
          if cnt > 0 then
            g := g.logMsg s!"{(g.player p).name} puts {cnt} card(s) on top of their library"
          return g
    | none => pure ()
  if cnt > 0 || (remainingIds.isEmpty && pendingId.isNone && movedCount == 0) then
    g := g.logMsg s!"{(g.player p).name} puts {cnt} card(s) on top of their library"
  return g

/-- Offer `controller` up to one free cast (`withoutPaying := true`) from the
next milled player bucket in `buckets` whose milled cards include at least one
nonland card still in the public zone it entered (CR 109.5 / 118.9 / 400.7h /
608.2g / 701.17c; Ruling 942). -/
partial def urSphinxCastNext (g : Game) (controller : PlayerId)
    (buckets : Array (Array ObjectId)) : Game :=
  if !g.stillInGame controller || g.cantCastSpellsThisTurn controller ||
      g.splitSecondOnStack || g.combatLocksNonManaAbilities ||
      g.opponentsCantCastOnActiveTurn controller then
    g
  else
    let hit? := (List.range buckets.size).findSome? fun i =>
      let eligible :=
        (buckets[i]!.filterMap g.followMilledPublic?).filter (fun o => !g.isLand o) |>.map (·.id)
      if eligible.isEmpty then none
      else some (eligible, buckets.extract (i + 1) buckets.size)
    match hit? with
    | none => g
    | some (eligible, rest) =>
      let g := g.beginFraChoice controller (.mayCastCards eligible true false)
        s!"{(g.player controller).name} may cast a spell from among those cards without paying its mana cost"
      if rest.isEmpty then g
      else g.chainPendingReplacement (.finishFrcPostStep (.urSphinxCastNext controller rest))

/-- Move each card in `gyIds` into `controller`'s graveyard inside the active
`Fact or Fiction` graveyard batch. -/
partial def factOrFictionGyInnerLoop (g : Game) (controller : PlayerId)
    (gyIds : Array ObjectId) (pendingCard : Option ObjectId := none) : Game := Id.run do
  if let .chooseReplacement .. := g.pending then
    return g.chainPendingReplacement
      (.finishFrcPostStep (.factOrFictionGyInnerLoop controller gyIds pendingCard))
  let plName := (g.player controller).name
  let mut g := g
  if let some fromId := pendingCard then
    if let some moved := g.followMovedToZone? fromId (· == .graveyard controller) then
      g := g.logMsg s!"{g.name moved} goes to {plName}'s graveyard"
  if !g.stillInGame controller then
    return g
  for i in [0:gyIds.size] do
    let id := gyIds[i]!
    if let some _ := g.findObject? id then
      let (g', _) := g.move id (.graveyard controller) none
      g := g'
      if let .chooseReplacement .. := g.pending then
        let rem := gyIds.extract (i + 1) gyIds.size
        return g.chainPendingReplacement
          (.finishFrcPostStep (.factOrFictionGyInnerLoop controller rem (some id)))
      if let some moved := g.followMovedToZone? id (· == .graveyard controller) then
        g := g.logMsg s!"{g.name moved} goes to {plName}'s graveyard"
      if !g.stillInGame controller then
        return g
  return g

partial def factOrFictionGyLoop (g : Game) (controller : PlayerId)
    (gyIds : Array ObjectId) : Game :=
  if gyIds.isEmpty || !g.stillInGame controller then g
  else
    g.withBatch none fun g =>
      g.factOrFictionGyInnerLoop controller gyIds

partial def factOrFictionHandInnerLoop (g : Game) (controller : PlayerId)
    (handIds : Array ObjectId) (pendingCard : Option ObjectId := none) : Game := Id.run do
  if let .chooseReplacement .. := g.pending then
    return g.chainPendingReplacement
      (.finishFrcPostStep (.factOrFictionHandInnerLoop controller handIds pendingCard))
  let plName := (g.player controller).name
  let mut g := g
  if let some fromId := pendingCard then
    if let some moved := g.followMovedToZone? fromId (· == .hand controller) then
      g := g.logMsg s!"{g.name moved} goes to {plName}'s hand"
  if !g.stillInGame controller then
    return g
  for i in [0:handIds.size] do
    let id := handIds[i]!
    if let some _ := g.findObject? id then
      let (g', _) := g.move id (.hand controller) none
      g := g'
      if let .chooseReplacement .. := g.pending then
        let remHand := handIds.extract (i + 1) handIds.size
        return g.chainPendingReplacement
          (.finishFrcPostStep (.factOrFictionHandInnerLoop controller remHand (some id)))
      if let some moved := g.followMovedToZone? id (· == .hand controller) then
        g := g.logMsg s!"{g.name moved} goes to {plName}'s hand"
      if !g.stillInGame controller then
        return g
  return g

partial def factOrFictionHandLoop (g : Game) (controller : PlayerId)
    (handIds gyIds : Array ObjectId) : Game :=
  let g :=
    if handIds.isEmpty || !g.stillInGame controller then g
    else
      g.withBatch none fun g =>
        g.factOrFictionHandInnerLoop controller handIds
  if let .chooseReplacement .. := g.pending then
    if gyIds.isEmpty then g
    else g.chainPendingReplacement (.finishFrcPostStep (.factOrFictionGyLoop controller gyIds))
  else
    g.factOrFictionGyLoop controller gyIds

partial def tamiyoStunLoop (g : Game) (controller : PlayerId)
    (ids : Array ObjectId) : Game := Id.run do
  let mut g := g
  for i in [0:ids.size] do
    let id := ids[i]!
    if let some o := g.findObject? id then
      if o.isOnBattlefield && g.isCreature o then
        g := g.becomeTapped o
        let curBefore := g.object! o.id
        let before := curBefore.status.stun
        g := g.recordPutCounters o.id .stun 1 (byPlayer := some controller)
        if let .chooseReplacement .. := g.pending then
          let rem := ids.extract (i + 1) ids.size
          return g.chainPendingReplacement
            (.finishFrcPostStep (.tamiyoStunLoop controller o.id before rem))
        let curAfter := g.object! o.id
        if curAfter.status.stun > before then
          g := g.logMsg s!"{g.name curAfter} gets a stun counter"
  return g

/-- Create the Teferi's Protection spell-exile replacement effect once its
phase-out batch has completed (CR 608.2c / 614.6). -/
def teferiExileSpell (g : Game) : Game :=
  match g.resolvingSpell.bind g.findObject? with
  | some spell =>
    g.createEffect (.exileInstantSorceryInstead spell.id)
      |>.logMsg s!"{g.name spell} will be exiled"
  | none => g

/-- Resume a deferred `FrcPostStep` after a `Pending.chooseReplacement` pause. -/
partial def runFrcPostStep (g : Game) (step : FrcPostStep) : Game :=
  match step with
  | .teferiExileSpell =>
    g.teferiExileSpell
  | .putDrawnBackOnTop p count =>
    if !g.stillInGame p then g
    else
      let hand := (g.player p).hand
      let n := min count hand.size
      let back := hand.extract (hand.size - n) hand.size
      g.withBatch none fun g =>
        g.putBackOnTopLoop p back
  | .putBackOnTopLoop p remainingIds movedCount pendingId =>
    g.putBackOnTopLoop p remainingIds movedCount pendingId
  | .swordsGainLife targetId fallbackOwner fallbackPower =>
    let pw :=
      match g.findObject? targetId with
      | some cur => if cur.isOnBattlefield then (g.snapshotPower cur).toNat else fallbackPower
      | none => ((g.lastKnownBefore? targetId).bind (·.power)).map Int.toNat |>.getD fallbackPower
    g.gainLife fallbackOwner pw
  | .logHandDiscard p cardId destOwner cardName =>
    if (g.followMovedToZone? cardId (· == .graveyard destOwner)).isSome then
      g.logMsg s!"{(g.player p).name} discards {cardName}"
    else g
  | .logHandDiscardToBottom p cardId destOwner cardName =>
    if (g.followMovedToZone? cardId (· == .library destOwner)).isSome then
      g.logMsg s!"{(g.player p).name} puts {cardName} on the bottom of their library"
    else g
  | .logExploreLandToHand controller cardId destOwner cardName =>
    if (g.followMovedToZone? cardId (· == .hand destOwner)).isSome then
      let destDesc :=
        if destOwner == controller then "their hand"
        else s!"{(g.player destOwner).name}'s hand"
      g.logMsg s!"{(g.player controller).name} explores and puts {cardName} into {destDesc}"
    else g
  | .offerExploreMayGraveyard controller cardId =>
    g.offerExploreMayGraveyard controller cardId
  | .logExploreToGraveyard controller cardId destOwner cardName =>
    if (g.followMovedToZone? cardId (· == .graveyard destOwner)).isSome then
      let destDesc :=
        if destOwner == controller then "their graveyard"
        else s!"{(g.player destOwner).name}'s graveyard"
      g.logMsg s!"{(g.player controller).name} puts {cardName} into {destDesc}"
    else g
  | .offerMaySearchBasics owner => g.offerMaySearchBasics owner
  | .makeHumanToken owner => g.makeTokenSpecBatched owner .human11white
  | .grantControlledCreaturesIndestructible controller =>
    g.grantUntilEotToControlledCreatures controller #[Keyword.indestructible] "indestructible"
  | .destroyNonRecentCreaturesAtFive x =>
    if x >= 5 then
      g.destroyIdsMatching (g.battlefield.filter (g.isCreature ·) |>.map (·.id))
        (fun o => !g.recentTokenIds.contains o.id)
    else g
  | .makeMitesThenDestroyAtFive controller x =>
    let g := g.makeTokenSpecBatched controller .mite x
    if let .chooseReplacement .. := g.pending then
      if x >= 5 then
        g.chainPendingReplacement (.finishFrcPostStep (.destroyNonRecentCreaturesAtFive x))
      else g
    else g.runFrcPostStep (.destroyNonRecentCreaturesAtFive x)
  | .discardBackHandThenCreateSpirits controller x =>
    let hand := (g.player controller).hand
    let n := min x hand.size
    let ids := hand.extract (hand.size - n) hand.size
    let types := ids.foldl (fun acc id =>
      match g.findObject? id with
      | some o =>
        (g.types o).foldl (fun acc t =>
          let name := CardType.englishName t
          if acc.contains name then acc else acc.push name) acc
      | none => acc) (#[] : Array String)
    let g := g.withBatch none fun g =>
      g.discardHandIdsLoop controller ids (logEach := false)
    if let .chooseReplacement .. := g.pending then
      g.chainPendingReplacement (.finishFrcPostStep (.createSpiritTokens controller types.size))
    else
      g.createKindTokens controller .spirit types.size
  | .createSpiritTokens controller count => g.createKindTokens controller .spirit count
  | .incubateForExiledCount controller startIdx ids cause =>
    let count :=
      if ids.isEmpty then startIdx
      else ids.foldl (fun acc id => if g.wasPermanentExiled id startIdx then acc + 1 else acc) 0
    let extra : CounterBag :=
      if count > 0 then #[(.plusOnePlusOne, count)] else #[]
    g.withBatch cause fun g =>
      g.makeTokenSpecBatched controller .incubator 1 0 (extraCounters := extra) (cause := cause)
  | .polymorphRevealCreatures controller startIdx sourceId ids =>
    if !g.stillInGame controller then g
    else
      let count :=
        if ids.isEmpty then startIdx
        else ids.foldl (fun acc id => if g.wasPermanentExiled id startIdx then acc + 1 else acc) 0
      let (g, revealCause) := g.allocDelayedCause (some controller) sourceId
      let (g, hits, rest) := g.revealUntilCards controller (fun c => (g.baseCard c).isCreature) count (cause := some revealCause)
      let g := g.putHitsToBattlefield controller hits (cause := some revealCause)
      if let .chooseReplacement .. := g.pending then
        g.chainPendingReplacement (.finishFrcRestBottom controller rest true (some revealCause))
      else
        g.restBottomCards controller rest true (cause := some revealCause)
  | .registerSyntheticDestinyEndStep controller startIdx sourceId ids cause =>
    let count :=
      if ids.isEmpty then startIdx
      else ids.foldl (fun acc id => if g.wasPermanentExiled id startIdx then acc + 1 else acc) 0
    let src := sourceId.bind g.findObject?
    g.registerDelayedTrigger
      { controller, source := src, kind := .endStepSynthetic count
        cause := cause.getD (.gameRule .spellCast) }
      |>.logMsg "Those creatures return as revealed cards at the next end step"
  | .polymorphSingleTargetReveal owner controller sourceId =>
    if !g.stillInGame owner then g
    else
      let (g, revealCause) := g.allocDelayedCause (some controller) sourceId
      let (g, hits, rest) := g.revealUntilCards owner (fun c => (g.baseCard c).isCreature) 1 (cause := some revealCause)
      let g := g.putHitsToBattlefield owner hits (cause := some revealCause)
      if let .chooseReplacement .. := g.pending then
        g.chainPendingReplacement (.finishFrcRestBottom owner rest false (some revealCause))
      else
        g.restBottomCards owner rest false (cause := some revealCause)
  | .discardHandThenDrainAndDraw victim controller =>
    let g := g.handDiscardBack victim
    if let .chooseReplacement .. := g.pending then
      g.chainPendingReplacement (.finishFrcPostStep (.loseThreeDrawOneGainThree victim controller))
    else g.runFrcPostStep (.loseThreeDrawOneGainThree victim controller)
  | .loseThreeDrawOneGainThree victim controller =>
    let g := g.loseLife victim 3
    let g := g.draw controller 1
    g.gainLife controller 3
  | .optionalOncePolymorphReveal controller sourceId =>
    if !g.stillInGame controller then g
    else
      match g.srcObjOnBf? sourceId with
      | some src =>
        if g.optionalOnceUsedThisTurn src.id then g
        else
          let (g, rc) := g.allocDelayedCause (some controller) sourceId
          let g := g.record (GameEvent.optionalOnceActed g.turnNumber controller src.id (cause := some rc))
          let (g, hits, rest) := g.revealUntilCards controller (fun c => (g.baseCard c).isCreature) 1 (cause := some rc)
          let g := g.putHitsToBattlefield controller hits (cause := some rc)
          if let .chooseReplacement .. := g.pending then
            g.chainPendingReplacement (.finishFrcRestBottom controller rest false (some rc))
          else
            g.restBottomCards controller rest false (cause := some rc)
      | none => g
  | .handDiscardToBottom controller => g.handDiscardToBottomOf controller
  | .revealCreatureOrPlaneswalker controller sourceId =>
    if !g.stillInGame controller then g
    else
      let (g, revealCause) := g.allocDelayedCause (some controller) sourceId
      let (g, hits, rest) := g.revealUntilCards controller
        (fun c => let bc := g.baseCard c; bc.isCreature || bc.isPlaneswalker) 1 (cause := some revealCause)
      let g := g.putHitsToBattlefield controller hits (cause := some revealCause)
      if let .chooseReplacement .. := g.pending then
        g.chainPendingReplacement (.finishFrcRestBottom controller rest false (some revealCause))
      else
        g.restBottomCards controller rest false (cause := some revealCause)
  | .grantRecentTokensLifelinkHaste =>
    g.withBatch none fun g =>
      g.recentTokenIds.foldl (fun g tid =>
        match g.findObject? tid with
        | some tok =>
          if tok.isOnBattlefield then
            g.createEffect (.keywordsUntilEot tok.id #[Keyword.lifelink, Keyword.haste])
              |>.logMsg s!"{g.name tok} gains lifelink and haste until end of turn"
          else g
        | none => g) g
  | .discardHand controller => g.handDiscardBack controller
  | .currencyReturnCreateToken controller exiledId sourceId isLand =>
    if (g.followMovedToZone? exiledId (· != .exile)).isSome then
      let g := g.pruneLinkedExileId sourceId exiledId
      if isLand then g.makeTokenSpecBatched controller .treasure else g.makeTokenSpecBatched controller .rogue22black
    else g
  | .urSphinxCastNext controller buckets =>
    g.urSphinxCastNext controller buckets
  | .factOrFictionHandInnerLoop controller handIds pendingCard =>
    g.factOrFictionHandInnerLoop controller handIds pendingCard
  | .factOrFictionGyInnerLoop controller gyIds pendingCard =>
    g.factOrFictionGyInnerLoop controller gyIds pendingCard
  | .factOrFictionGyLoop controller gyIds =>
    g.factOrFictionGyLoop controller gyIds
  | .tamiyoStunLoop controller targetId beforeStun remainingIds =>
    let g :=
      match g.findObject? targetId with
      | some cur =>
        if cur.status.stun > beforeStun then g.logMsg s!"{g.name cur} gets a stun counter" else g
      | none => g
    if remainingIds.isEmpty then g else g.tamiyoStunLoop controller remainingIds

/-- Reveal creature cards exiled by Synthetic Destiny at the end step. -/
def applyOneDelayedSynthetic (g : Game) (who : PlayerId) (n : Nat) (cause : EventCause) : Game :=
  let (g, hits, rest) := g.revealUntilCards who (fun c => (g.baseCard c).isCreature) n (cause := some cause)
  let g := g.putHitsToBattlefield who hits (cause := some cause)
  if let .chooseReplacement .. := g.pending then
    g.chainPendingReplacement (.finishFrcRestBottom who rest true (some cause))
  else
    g.restBottomCards who rest true (cause := some cause)

/-! ### Multi-Target & Linked-Exile Continuation Loops -/

def tapAndStunTargetsLoop (g : Game) (controller : PlayerId) (spec : TargetSpec)
    (remaining : Array (Nat × Target)) (sourceId : Option ObjectId)
    (cause : Option EventCause) : Game := Id.run do
  let mut g := g
  for i in [0:remaining.size] do
    let (slotIdx, t) := remaining[i]!
    match t with
    | Target.permanent id =>
      if g.targetLegalAt controller spec slotIdx t sourceId then
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

partial def plusOneOnEachTargetLoop (g : Game) (controller : PlayerId)
    (spec : TargetSpec) (remaining : Array (Nat × Target)) (n : Nat)
    (sourceId : Option ObjectId) : Game :=
  match remaining[0]? with
  | none => g
  | some (i, t) =>
    let rest := remaining.extract 1 remaining.size
    let g :=
      match t with
      | Target.permanent id =>
        if g.targetLegalAt controller spec i t sourceId then
          match g.findObject? id with
          | some o => g.addPlusOnePlusOneTo o n
          | none => g
        else g.illegalAbilityTarget t
      | _ => g
    if rest.isEmpty then g
    else if let .chooseReplacement .. := g.pending then
      g.chainPendingReplacement
        (.finishPostStep (.plusOneOnEachTargetLoop controller spec rest n sourceId))
    else
      g.plusOneOnEachTargetLoop controller spec rest n sourceId

partial def minusOnesPerOpponentLoop (g : Game) (controller : PlayerId)
    (spec : TargetSpec) (remaining : Array (Nat × Target)) (x : Nat)
    (sourceId : Option ObjectId) : Game :=
  match remaining[0]? with
  | none => g
  | some (i, t) =>
    let rest := remaining.extract 1 remaining.size
    let g :=
      match t with
      | Target.permanent id =>
        if !g.targetLegalAt controller spec i t sourceId then
          g.illegalAbilityTarget t
        else
          match g.findObject? id with
          | some o =>
            let shielded :=
              g.battlefield.any fun src =>
                let env : EvalEnv := { controller := (g.controllerOf src).getD src.owner, sourceId := some src.id }
                (g.staticAbilities src).any fun ab =>
                  ab.anyRule fun cond? r =>
                    match r with
                    | .game (.cantHaveCountersPutOn sc kind?) =>
                      (kind?.isNone || kind? == some .minusOneMinusOne) &&
                        cond?.all (EvalExpr.evalCondition g env) &&
                        EvalExpr.evalObjectPred g env (.live o) sc.pred
                    | _ => false
            if x > 0 && !shielded then
              g.putCountersDeferredLog o.id .minusOneMinusOne x (some controller) .countArePutOn
            else g
          | none => g
      | _ => g
    if rest.isEmpty then g
    else if let .chooseReplacement .. := g.pending then
      g.chainPendingReplacement
        (.finishPostStep (.minusOnesPerOpponentLoop controller spec rest x sourceId))
    else
      g.minusOnesPerOpponentLoop controller spec rest x sourceId

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

def fblthpMoveToHandLoop (g : Game) (controller : PlayerId)
    (remainingIds : Array ObjectId) (cause : EventCause) : Game := Id.run do
  if let .chooseReplacement .. := g.pending then
    return g.chainPendingReplacement
      (.finishPostStep (.fblthpMoveToHandLoop controller remainingIds cause))
  if !g.stillInGame controller then
    return g
  let mut g := g
  for i in [0:remainingIds.size] do
    let id := remainingIds[i]!
    match g.findObject? id with
    | some o =>
      let name := g.name o
      g := g.logMsg s!"{(g.player controller).name} reveals {name}"
      let (g', _) := g.move id (.hand controller) none (cause := some cause)
      g := g'
      if let .chooseReplacement .. := g.pending then
        let rem := remainingIds.extract (i + 1) remainingIds.size
        if !rem.isEmpty then
          g := g.chainPendingReplacement
            (.finishPostStep (.fblthpMoveToHandLoop controller rem cause))
        return g
      if !g.stillInGame controller then
        return g
    | none => pure ()
  return g

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
    g.logMsg s!"{g.name moved} is exiled until {srcName} leaves the battlefield"

private def makeUldarosExiledCopy (g : Game) (controller : PlayerId)
    (sourceId : Option ObjectId) (exObj : GameObject) (cause? : Option EventCause) : Game :=
  let g := g.logMsg s!"{g.name exObj} is exiled"
  if !g.stillInGame controller then g
  else
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
  if !g.stillInGame controller then
    return g
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
      if !g.stillInGame controller then
        return g
  return g

def finishUldarosCopiesOffer (g : Game) (controller : PlayerId)
    (cause? : Option EventCause) : Game :=
  if !g.stillInGame controller then g
  else
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

/-! ### Shared Spell & Ability Resolution Helpers -/

def shuffleSourceIntoLibrary (g : Game) (sourceId : Option ObjectId)
    (after : AfterRandom := .none) : Game :=
  match sourceId.bind g.findObject? with
  | none => g.logMsg "The source is no longer in play"
  | some src =>
    let owner := src.owner
    let after :=
      match after with
      | .draw _ n => .draw owner n
      | other => other
    let (g, _) := g.move src.id (.library owner) none
      (verb := some .shuffleIntoLibrary) (libraryPosition := some .shuffledIn)
    g.shuffleThen owner after

def sacrificeGreatestManaValue (g : Game) (pid : PlayerId) : Game :=
  if !g.stillInGame pid then g
  else
    let candidates := (g.permanentsOf pid).filter (fun o =>
      g.isCreature o || g.isPlaneswalker o)
    let best := candidates.foldl (fun best o =>
      match best with
      | none => some o
      | some b =>
        let mo := g.objectManaValue o
        let mb := g.objectManaValue b
        if mo > mb || (mo == mb && o.timestamp ≥ b.timestamp) then some o else best) none
    match best with
    | none => g.logMsg s!"{(g.player pid).name} has no creature or planeswalker to sacrifice"
    | some o => g.sacrificeToGraveyard o s!"{(g.player pid).name} sacrifices {g.name o}"

def finishExileTopMayCastElseDamage (g : Game) (controller : PlayerId)
    (fromId : ObjectId) (n : Nat) (sid : Option ObjectId) : Game :=
  let src? := sid.bind g.damageSourceById?
  match g.followMovedToZone? fromId (· == .exile) with
  | some card =>
    let name := g.name card
    let g := g.logMsg s!"{(g.player controller).name} exiles {name}"
    if !g.stillInGame controller then g
    else if g.isLand card then
      g.dealDamageToEachOpponent controller n (source := src?)
    else
      (g.change (.pending (.mayCastExiledElseDamage controller card.id n sid))).logMsg
        s!"{(g.player controller).name} may cast {name}"
  | none =>
    if !g.stillInGame controller then g
    else g.dealDamageToEachOpponent controller n (source := src?)

partial def copyNontokenCreaturesStep (g : Game) (p : PlayerId)
    (snapshots : Array CardDef) (cause : Option EventCause := none) : Game :=
  if snapshots.isEmpty then g
  else if let .chooseReplacement .. := g.pending then
    g.chainPendingReplacement (.copyNontokenCreatures p snapshots cause)
  else if !g.stillInGame p then
    g.logMsg "no token is created (CR 800.4b)"
  else
    let baseCause :=
      cause.orElse (fun _ =>
        match g.currentBatch.bind (·.2) with
        | some bc => some bc
        | none => g.resolvingBatchCause p)
    let initialBatches : Array ProposedTokenBatch :=
      snapshots.map fun printed => {
        controller := p
        printed := printed
        count := 1
        cause := baseCause
      }
    let (batches, applied, choice?) := g.replaceTokenBatchesChoice initialBatches
    match choice? with
    | some (chooser, choices) =>
      g.promptChooseReplacement chooser choices (.copyNontokenCreatures p snapshots baseCause)
    | none =>
      let g := g.consumeReplacementOrder applied
      let expanded := batches.foldl (fun acc b =>
        Id.run do
          let mut acc := acc
          for _ in [0:b.count] do
            acc := acc.push { b with count := 1 }
          return acc) #[]
      if expanded.isEmpty then g
      else
        (g.createTokenBatches expanded (recordRecent := true) (cause := baseCause)).1

partial def exileHandDrawLoop (g : Game) (p : PlayerId) (ids : Array ObjectId)
    (cause : Option EventCause) (justMovedFrom : Option ObjectId := none) : Game :=
  let g :=
    match justMovedFrom.bind (fun fid => g.followMovedToZone? fid (· == .exile)) with
    | some moved =>
      if !g.stillInGame p then g
      else
        g.createEffect (.playPermission moved.id { player := p } (turnEnds := 2))
          (cause := cause)
    | none => g
  if let .chooseReplacement .. := g.pending then
    if ids.isEmpty then g
    else g.chainPendingReplacement (.finishPostStep (.exileHandDrawLoop p ids cause none))
  else if !g.stillInGame p then g
  else
    match ids[0]? with
    | none => g
    | some id =>
      let rem := ids.extract 1 ids.size
      match g.findObject? id with
      | none => g.exileHandDrawLoop p rem cause none
      | some _ =>
        let (g, _) := g.move id .exile none (cause := cause)
        if let .chooseReplacement .. := g.pending then
          g.chainPendingReplacement (.finishPostStep (.exileHandDrawLoop p rem cause (some id)))
        else
          g.exileHandDrawLoop p rem cause (some id)

def finishExileHandDrawPlayUntilNext (g : Game) (p : PlayerId) (n : Nat)
    (cause : Option EventCause) : Game :=
  if !g.stillInGame p then g
  else
    let g :=
      if n == 0 then g
      else g.logMsg s!"{(g.player p).name} may play the exiled cards until the end of their next turn"
    g.draw p n (cause := cause)

def exileHandDrawPlayUntilNext (g : Game) (p : PlayerId) : Game :=
  if !g.stillInGame p then g
  else
    let ids := (g.player p).hand
    let n := ids.size
    let (g, cause?) : Game × Option EventCause :=
      if ids.isEmpty then (g, none)
      else
        let (g, c) := g.allocDelayedCause (some p)
        (g, some c)
    let g := g.withBatch cause? fun g =>
      g.exileHandDrawLoop p ids cause? none
  if let .chooseReplacement .. := g.pending then
    g.chainPendingReplacement (.finishPostStep (.finishExileHandDrawPlayUntilNext p n cause?))
  else
    g.finishExileHandDrawPlayUntilNext p n cause?

def finishCopyNontokenCreaturesAfterEnter (g : Game) (startEventIdx : Nat) : Game :=
  let ids := g.tokensCreatedSince startEventIdx
  let (g, anyPrompt) :=
    ids.foldl (fun (g, anyP) id =>
      match g.findObject? id with
      | some o =>
        if o.isOnBattlefield then
          let g := g.afterPermanentEntersInBatch o
          let p :=
            match g.findObject? id with
            | some cur => cur.isOnBattlefield && !g.enteringCausesNoTriggers cur
            | none => false
          (g, anyP || p)
        else (g, anyP)
      | none => (g, anyP)) (g, false)
  if anyPrompt && g.currentBatch.isNone then
    g.promptTriggerTargetsIfNeeded
  else g

def copyNontokenCreaturesYouControl (g : Game) (p : PlayerId) : Game :=
  let startEventIdx := g.events.size
  let g := g.withBatch (g.resolvingBatchCause p) fun g =>
    let snapshots :=
      ((g.creaturesControlledBy p).filter (fun o => !o.printed.isToken)).map fun src =>
        let cv := g.copiableValues src
        { cv with
          supertypes := cv.supertypes.filter (· != .legendary)
          isToken := true }
    g.copyNontokenCreaturesStep p snapshots
  if let .chooseReplacement .. := g.pending then
    g.chainPendingReplacement (.finishPostStep (.copyNontokenCreaturesAfterEnter startEventIdx))
  else
    g.finishCopyNontokenCreaturesAfterEnter startEventIdx

def applyEvilsThrall (g : Game) (controller : PlayerId) (targets : Array Target)
    (sourceId : Option ObjectId := none) : Game :=
  g.withLegalSpecPermanent controller .creature targets (fun g o =>
    let mv := g.objectManaValue o
    let longer := (g.creaturesControlledBy controller).any (fun v =>
      g.hasSubtype v .villain && g.objectManaValue v > mv)
    let g :=
      if longer then
        g.changeControl o controller (turnEndsLeft := 2)
      else
        g.giveControlUntilEot o controller
    match g.findObject? o.id with
    | none => g
    | some o =>
      let g := g.untapPermanentLogged o (sourceId := sourceId)
      if let .chooseReplacement .. := g.pending then
        g.chainPendingReplacement (.finishPostStep (.evilsThrallGrantHaste o.id))
      else
        match g.findObject? o.id with
        | none => g
        | some o => g.grantUntilEotLogged o #[Keyword.haste]) sourceId
    (some "The target is no longer legal")

def finishMillMayPutPermanentGainLife (g : Game) (p : PlayerId)
    (preIds : Array ObjectId) (life : Nat) : Game :=
  if !g.stillInGame p then g
  else
    let permanents := preIds.filterMap (fun id =>
      match g.followMilledPublic? id with
      | some o => if g.isPermanentCard o then some o.id else none
      | none => none)
    if permanents.isEmpty then g.gainLife p life
    else
      g.beginFraChoice p (.mayTakeMilled permanents life)
        s!"{(g.player p).name} may put a permanent card from among the milled cards into their hand"

def millMayPutPermanentGainLife (g : Game) (p : PlayerId) (n life : Nat) : Game :=
  if !g.stillInGame p then g
  else
    let lib := (g.player p).library
    let count := min n lib.size
    let tops := (lib.extract (lib.size - count) lib.size).reverse
    let g := g.mill p n
    if let .chooseReplacement .. := g.pending then
      g.chainPendingReplacement (.finishPostStep (.millMayPutPermanentGainLife p tops life))
    else
      g.finishMillMayPutPermanentGainLife p tops life

def finishMillSubtypeOrEnchantment (g : Game) (p : PlayerId)
    (preIds : Array ObjectId) (subtype : CardSubtype) : Game :=
  if !g.stillInGame p then g
  else
    let eligible := preIds.filterMap (fun id =>
      match g.followMilledPublic? id with
      | some o =>
        if g.hasSubtype o subtype || g.isEnchantment o then some o.id else none
      | none => none)
    if eligible.isEmpty then
      g.logMsg s!"{(g.player p).name} has no {subtype} or enchantment card among the milled cards"
    else
      g.beginFraChoice p (.mayTakeMilled eligible 0)
        s!"{(g.player p).name} may put a {subtype} or enchantment card into their hand"

def millMayPutSubtypeOrEnchantment (g : Game) (p : PlayerId) (n : Nat) (subtype : CardSubtype) : Game :=
  if !g.stillInGame p then g
  else
    let lib := (g.player p).library
    let count := min n lib.size
    let tops := (lib.extract (lib.size - count) lib.size).reverse
    let g := g.mill p n
    if let .chooseReplacement .. := g.pending then
      g.chainPendingReplacement (.finishMillSubtypeOrEnchantment p tops subtype)
    else
      g.finishMillSubtypeOrEnchantment p tops subtype

def applyGainLifeSearchBasicPlusOne (g : Game) (controller : PlayerId)
    (targets : Array Target) (life : Nat)
    (sourceId : Option ObjectId := none) : Game :=
  let run (g : Game) : Game :=
    let player? := targets.findSome? (fun t =>
      match t with
      | Target.player pid => some pid
      | _ => none)
    let creature? := targets.findSome? (fun t =>
      match t with
      | Target.permanent id => some id
      | _ => none)
    let legalPlayer? :=
      match player? with
      | some pid =>
        if g.stillInGame pid && g.playerCanBeTargetedBy controller pid sourceId then
          some pid
        else none
      | none => none
    match legalPlayer? with
    | none =>
      let g := g.logMsg "The target is no longer legal"
      match creature? with
      | some cid => g.addPlusOneIfStillCreature cid controller sourceId
      | none => g
    | some pid =>
      let g :=
        match creature? with
        | none => g
        | some id =>
          match g.findObject? id with
          | some o =>
            if o.isOnBattlefield && g.isCreature o && g.canBeTargetedBy controller o sourceId then
              g.change (.plusOneAfterSearch (some (id, controller, sourceId)))
            else g.logMsg "The target is no longer legal"
          | none => g.logMsg "The target is no longer legal"
      let g := g.gainLife pid life
      if let .chooseReplacement .. := g.pending then
        g.chainPendingReplacement (.finishPostStep (.searchBasicLandTapped pid))
      else
        g.beginLibrarySearch pid isBasicLandCard "a basic land card" (.battlefield true)
  g.withContinuationFrame run

def mayDrawPerArtifact (g : Game) (p : PlayerId) (ty : CardType := .artifact) : Game :=
  if !g.stillInGame p then g
  else
    let n := ((g.permanentsOf p).filter (fun o => g.hasType o ty)).size
    if n == 0 then
      let what := if ty == .artifact then "artifacts" else ty.pluralName
      g.logMsg s!"{(g.player p).name} controls no {what}, so no cards are drawn"
    else
      g.beginFraChoice p (.mayDrawThenEachOpponentDraws n)
        s!"{(g.player p).name} may draw {n}"

def mayPutHeroOrDraw (g : Game) (p : PlayerId) (maxMv : Nat)
    (subtype : CardSubtype := .hero) : Game :=
  if !g.stillInGame p then g
  else
    let ids := (g.player p).hand.filter (fun id =>
      (g.findObject? id).any (fun o =>
        g.isCreature o && g.hasSubtype o subtype && g.objectManaValue o ≤ maxMv))
    if ids.isEmpty then g.draw p 1
    else
      g.beginFraChoice p (.mayPutHeroFromHandOrDraw ids)
        s!"{(g.player p).name} may put {indefinite subtype.englishName} {subtype} creature card onto the battlefield"

def grantTypeCostLessThisTurn (g : Game) (p : PlayerId) (ty : CardType) (n : Nat) : Game :=
  g.createEffect (.typeSpellCostLessThisTurn p ty n)
    |>.logMsg s!"{ty} spells {(g.player p).name} casts this turn cost \{{n}} less"

def grantSupertypeCostLessThisTurn (g : Game) (p : PlayerId) (s : Supertype) (n : Nat) : Game :=
  g.createEffect (.supertypeSpellCostLessThisTurn p s n)
    |>.logMsg s!"{s} spells {(g.player p).name} casts this turn cost \{{n}} less"

def returnChosenGraveyardCards (g : Game) (controller : PlayerId)
    (targets : Array Target) : Game :=
  let kinds : Array CardType := #[.artifact, .creature, .enchantment, .land]
  match g.resolvingModes with
  | some modes =>
    if modes.isEmpty then g
    else
      g.withBatch (g.resolvingBatchCause controller none) fun g =>
        Id.run do
          let mut g := g
          let mut toReturn : Array ObjectId := #[]
          let count := Nat.min targets.size modes.size
          for idx in [0:count] do
            let t := targets[idx]!
            let reqTy? := kinds[modes[idx]!]?
            match t, reqTy? with
            | Target.card id, some reqTy =>
              match g.findObject? id with
              | some o =>
                if o.zone == .graveyard controller && o.owner == controller &&
                    g.objectHasCardType o reqTy then
                  if !toReturn.contains o.id then
                    toReturn := toReturn.push o.id
                else
                  g := g.logMsg "The target is no longer legal"
              | none =>
                g := g.logMsg "The target is no longer legal"
            | _, _ =>
              g := g.logMsg "The target is no longer legal"
          for id in toReturn do
            g := g.returnToHand id controller
          return g
  | none =>
    g.withBatch (g.resolvingBatchCause controller none) fun g =>
      Id.run do
        let mut g := g
        let mut used : Array CardType := #[]
        let picked := targets.extract 0 2
        for idx in [0:picked.size] do
          let t := picked[idx]!
          match t with
          | Target.card id =>
            match g.findObject? id with
            | some o =>
              if o.zone == .graveyard controller && o.owner == controller then
                let avail := kinds.filter (fun ty =>
                  !used.contains ty && g.objectHasCardType o ty)
                let chosenTy? :=
                  match idx, picked[1]? with
                  | 0, some (Target.card id1) =>
                    match g.findObject? id1 with
                    | some o1 =>
                      if o1.zone == .graveyard controller && o1.owner == controller then
                        avail.find? (fun ty =>
                          kinds.any (fun ty2 => ty2 != ty && g.objectHasCardType o1 ty2)) <|> avail[0]?
                      else avail[0]?
                    | none => avail[0]?
                  | _, _ => avail[0]?
                match chosenTy? with
                | some ty =>
                  g := g.returnToHand o.id controller
                  used := used.push ty
                | none =>
                  g := g.logMsg s!"{g.name o} doesn't match a mode that is still available"
              else
                g := g.logMsg "The target is no longer legal"
            | none =>
              g := g.logMsg "The target is no longer legal"
          | _ =>
            g := g.logMsg "The target is no longer legal"
        return g

def plusOneAndDoubleStrike (g : Game) (sourceId : Option ObjectId) : Game :=
  g.withSourceOnBattlefield sourceId (fun g o =>
    g.withBatch none fun g =>
      let byP := g.controllerOf o
      let g := g.addPlusOnePlusOneTo o 1
      if let .chooseReplacement .. := g.pending then
        g.chainPendingReplacement
          (.finishPostStep (.putDoubleStrikeCounter o.id byP))
      else
        g.putCountersDeferredLog o.id .doubleStrike 1 byP .gets)
    "The source is no longer in play"

def plusOneThenFight (g : Game) (controller : PlayerId) (sourceId : Option ObjectId)
    (targets : Array Target) : Game :=
  let g :=
    g.withSourceOnBattlefield sourceId (fun g o => g.addPlusOnePlusOneTo o 1)
      "The source is no longer in play"
  match targets[0]? with
  | none => g
  | some _ =>
    if let .chooseReplacement .. := g.pending then
      g.chainPendingReplacement (.finishPostStep (.fightTargetOpponentCreature controller sourceId targets))
    else
      g.withLegalSpecPermanent controller .oppCreature targets (fun g tgt =>
        match sourceId.bind g.findObject? with
        | some src =>
          if src.isOnBattlefield && g.isCreature src then g.fightCreatures src tgt
          else g.logMsg "The source is no longer in play"
        | none => g.logMsg "The source is no longer in play") sourceId
        (some "The target is no longer legal")

def destroyCreaturesByManaParity (g : Game) (sourceId : Option ObjectId) (even : Bool) : Game :=
  let preBf := g.battlefield
  let ids := (preBf.filter (fun o =>
    some o.id != sourceId && g.isCreature o &&
      ((g.objectManaValue o % 2 == 0) == even))).map (·.id)
  let quality := if even then "even" else "odd"
  let g := g.logMsg s!"Destroy each other creature with {quality} mana value"
  g.withBatch none fun g =>
    g.destroyPermanentsLoop ids (preBattlefield := some preBf)

def revealTopDrawIfArtifact (g : Game) (p : PlayerId) : Game :=
  match (g.player p).library.back? with
  | none => g.logMsg s!"{(g.player p).name} has no cards in their library"
  | some id =>
    let o := g.object! id
    let g := g.record (GameEvent.revealed g.turnNumber p #[id]
      (cause := some (g.resolvingOrRuleCause p)))
    let g := g.logMsg s!"{(g.player p).name} reveals {g.name o}"
    if g.isArtifact o then g.draw p 1 else g

def returnGyCreatureThenPlusOne (g : Game) (controller : PlayerId)
    (sourceId : Option ObjectId) (targets : Array Target) (n : Nat) : Game :=
  let g :=
    match targets[0]? with
    | none => g
    | some (Target.card id) =>
      match g.findObject? id with
      | some o =>
        if o.zone == Zone.graveyard controller && g.isCreature o then
          g.returnToHand o.id o.owner
        else g.logMsg "The target is no longer legal"
      | none => g.logMsg "The target is no longer legal"
    | some _ => g.logMsg "The target is no longer legal"
  g.withSourceOnBattlefield sourceId (fun g o => g.addPlusOnePlusOneTo o n)
    "The source is no longer in play"

def returnFromGyFinalityAttach (g : Game) (controller : PlayerId)
    (sourceId : Option ObjectId) : Game :=
  match sourceId.bind g.findObject? with
  | none => g.logMsg "The card is no longer in the graveyard"
  | some o =>
    if o.zone != .graveyard o.owner then
      g.logMsg s!"{g.name o} is no longer in the graveyard"
    else
      let name := g.name o
      let (g, newId) := g.putOntoBattlefield o.id controller
        (extraEntersWith := #[(.finality, 1)])
      if let .chooseReplacement .. := g.pending then
        g.chainPendingReplacement (.finishPostStep (.enteredOfferAttachEquipment controller o.id))
      else
        let entered := g.object! newId
        if !entered.isOnBattlefield then g
        else
          let g := g.afterPermanentEnters entered
          if g.pending != .none then g
          else if (g.permanentsOf controller).any (fun eq => g.isEquipment eq) then
            g.change (.pending (.mayAttachEquipment controller newId))
              |>.logMsg s!"{(g.player controller).name} may attach an Equipment to {name}"
          else g

partial def finishProliferateEachKind (g : Game) (controller : PlayerId)
    (targetId : ObjectId) (remainingKinds : Array CounterKind)
    (hasPlusOne : Bool) (effCause : EventCause) : Game :=
  if hasPlusOne then
    let g :=
      match g.findObject? targetId with
      | some o => g.addPlusOnePlusOneTo o 1 (byPlayer := some controller) (cause := some effCause)
      | none => g
    if let .chooseReplacement .. := g.pending then
      g.chainPendingReplacement (.finishProliferateEachKind controller targetId remainingKinds false effCause)
    else
      g.finishProliferateEachKind controller targetId remainingKinds false effCause
  else
    match remainingKinds[0]? with
    | some kind =>
      let restKinds := remainingKinds.extract 1 remainingKinds.size
      let g := g.recordPutCounters targetId kind 1 (byPlayer := some controller) (cause := some effCause)
      if let .chooseReplacement .. := g.pending then
        g.chainPendingReplacement (.finishProliferateEachKind controller targetId restKinds false effCause)
      else
        g.finishProliferateEachKind controller targetId restKinds false effCause
    | none =>
      let g := g.syncImpendingNotACreature targetId (cause := some effCause)
      let oName := ((g.findObject? targetId).map g.name).getD "permanent"
      (g.record (GameEvent.proliferated g.turnNumber controller (permanents := #[targetId]) (cause := some effCause))).logMsg
        s!"{oName} gets another counter of each kind"

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
          g.record (GameEvent.proliferated g.turnNumber controller (players := #[pid]) (cause := some effCause))
        else g.logMsg s!"{pl.name} has no counters"
      | Target.card _ => g.logMsg "The target is no longer legal") sourceId
    (some "The target is no longer legal")

def finishVisionQuest (g : Game) (p : PlayerId) (id? : Option ObjectId)
    (x : Nat) (shuffle : Bool) : Game :=
  let g :=
    if shuffle then
      let foundFromLib :=
        match id? with
        | some id =>
          if (g.findObject? id).any (fun o =>
              o.zone == .library p && g.isArtifact o && g.isCreature o &&
                g.objectManaValue o ≤ x) then #[id]
          else #[]
        | none => #[]
      g.record (GameEvent.searched g.turnNumber p p foundFromLib
        (cause := some (g.resolvingOrRuleCause p)))
    else g
  match id? with
  | none =>
    let g := g.logMsg s!"{(g.player p).name} finds no artifact creature card"
    if shuffle then g.shuffleThen p .none else g
  | some id =>
    match g.findObject? id with
    | some o =>
      if (o.zone == .library p || o.zone == .graveyard p) &&
          g.isArtifact o && g.isCreature o &&
          g.objectManaValue o ≤ x then
        let (g, newId) := g.putOntoBattlefield id p
          (extraEntersWith := if x > 0 then #[(.plusOnePlusOne, x)] else #[])
        if let .chooseReplacement .. := g.pending then
          g.chainPendingReplacement (.finishPostStep (.putOntoBattlefieldHasteAtFour p id x shuffle))
        else
          let entered := g.object! newId
          let g :=
            if entered.isOnBattlefield then
              let name := g.name entered
              let g := g.afterPermanentEnters entered
              let g :=
                if x ≥ 4 then g.grantUntilEotLogged (g.object! newId) #[Keyword.haste] else g
              g.logMsg s!"{name} is put onto the battlefield"
            else g
          if shuffle then g.shuffleThen p .none else g
      else
        let g := g.logMsg "That card can't be found"
        if shuffle then g.shuffleThen p .none else g
    | none =>
      let g := g.logMsg "That card can't be found"
      if shuffle then g.shuffleThen p .none else g

def beginVisionQuest (g : Game) (p : PlayerId) (x : Nat) : Game :=
  if !g.stillInGame p then g
  else
    let ok (o : GameObject) : Bool :=
      g.isArtifact o && g.isCreature o && g.objectManaValue o ≤ x
    let lib := (g.player p).library.filter (fun id => (g.findObject? id).any ok)
    let gy := (g.player p).graveyard.filter (fun id => (g.findObject? id).any ok)
    if lib.isEmpty && gy.isEmpty then
      let g := g.record (GameEvent.searched g.turnNumber p p #[]
        (cause := some (g.resolvingOrRuleCause p)))
      (g.logMsg s!"{(g.player p).name} finds no artifact creature card").shuffleThen p .none
    else
      g.beginFraChoice p (.visionQuestZones lib gy x)
        s!"{(g.player p).name} may search their library and their graveyard"

def conniveTricksterTarget (g : Game) (controller : PlayerId) (id? : Option ObjectId)
    (sourceId : Option ObjectId := none) : Game :=
  if !g.stillInGame controller then g
  else
    match id? with
    | none => g
    | some id =>
      match g.findObject? id with
      | some o =>
        if o.isOnBattlefield && g.isCreature o && g.controlledBy o controller &&
            g.canBeTargetedBy controller o sourceId then
          g.applyConnive controller (some id)
        else g.logMsg "The target is no longer legal"
      | none => g.logMsg "The target is no longer legal"

def otherSpellsManaValue (g : Game) (p : PlayerId) : Nat :=
  let total := (g.loggedCastManaValues p).foldl (· + ·) 0
  let own :=
    match g.resolvingSpell.bind g.findObject? with
    | some spell =>
      if GameEvent.isUncastStackCopy g.events spell.id || g.controllerOf spell != some p then 0
      else g.objectManaValue spell
    | none => 0
  total - own

def battlefieldCreatureTypes (g : Game) : Array CardSubtype :=
  g.battlefield.foldl (fun acc o =>
    if !g.isCreature o then acc
    else
      (g.subtypes o).foldl (fun acc t =>
        if t.isCreatureType && !acc.contains t then acc.push t else acc) acc) #[]

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
    let g := g.beginFraChoice p (.chooseCards ids max purpose) msg
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

def resolveTapScryDraw (g : Game) (controller : PlayerId) (effect : Effect)
    (targets : Array Target) (scryN drawN : Nat)
    (sourceId : Option ObjectId := none)
    (fizzle : Game → Game := fun g => g.logMsg "The spell doesn't resolve") : Game :=
  if g.sequenceAllTargetsIllegal controller effect targets sourceId then
    fizzle g
  else
    let g := g.withLegalSpecPermanent controller effect.targetSpec targets
      (fun g o => g.becomeTapped o) sourceId
    g.scryThenDraw controller scryN drawN

/-- Ask `controller` whether to resolve `body` (or attach an Equipment). -/
def beginMay (g : Game) (controller : PlayerId) (effect : Effect)
    (targets : Array Target) (body : Instruction)
    (sourceId : Option ObjectId := none)
    (resCtx : SpellResolutionCtx := {}) : Game :=
  g.withContinuationFrame fun g =>
    match body with
    | .permanent (.attach _ _ true) =>
      g.withLegalSpecPermanent controller effect.targetSpec targets (fun g o =>
        ((g.clearMay).changes #[
          .pending (.mayAttachEquipment controller o.id sourceId),
          .mayResCtx resCtx]).logMsg
          s!"{(g.player controller).name} may attach an Equipment to {g.name o}") sourceId
    | _ =>
      let phrase := ToOracle.toOracle {} body
      let phrase := if phrase.startsWith "you " then (phrase.drop 4).toString else phrase
      let inner : Effect := { effect with body, resolution? := none }
      ((g.clearMay).changes #[
        .pending (.mayResolve controller),
        .mayEffect (some inner),
        .mayController controller,
        .mayTargets targets,
        .maySource sourceId,
        .mayResCtx resCtx]).logMsg
        s!"{(g.player controller).name} may {phrase}"

/-- Ask a player to choose between alternative `Instruction` branches (e.g., owner's
top-or-bottom library placement). -/
def beginSpellOr (g : Game) (controller : PlayerId) (effect : Effect)
    (targets : Array Target) (bs : List Instruction)
    (sourceId : Option ObjectId := none)
    (resCtx : SpellResolutionCtx := {}) (libraryTopBottom : Bool := false) : Game :=
  g.withContinuationFrame fun g =>
    let asEffect (b : Instruction) : Effect :=
      { effect with body := b, resolution? := none }
    let g := g.clearSpellOr
    if libraryTopBottom then
      match targets[0]? with
      | some (Target.permanent id) =>
        match g.findObject? id with
        | some o =>
          if o.isOnBattlefield && g.canBeTargetedBy controller o sourceId then
            (g.changes #[
              .pending (.chooseLibraryPlacement o.owner (some id)),
              .spellOr (bs.map asEffect).toArray,
              .spellOrController controller,
              .spellOrTargets targets,
              .spellOrLibrary true,
              .spellOrSource sourceId,
              .spellOrResCtx resCtx]).logMsg
              s!"{(g.player o.owner).name} chooses top or bottom of their library for {g.name o}"
          else g.logMsg "The target is no longer legal"
        | none => g.logMsg "The target is no longer legal"
      | _ => g.logMsg "The target is no longer legal"
    else
      let label := String.intercalate " or " (bs.map (ToOracle.toOracle {}))
      (g.changes #[
        .pending (.chooseLibraryPlacement controller none),
        .spellOr (bs.map asEffect).toArray,
        .spellOrController controller,
        .spellOrTargets targets,
        .spellOrLibrary false,
        .spellOrSource sourceId,
        .spellOrResCtx resCtx]).logMsg
        s!"{(g.player controller).name} chooses {label}"

partial def exileTopXOppPlayForLifeLoop (g : Game) (controller pid : PlayerId)
    (remaining : Nat) (cause : Option EventCause)
    (justMovedFrom : Option ObjectId := none) : Game :=
  let g :=
    match justMovedFrom with
    | none => g
    | some fid =>
      match g.followMovedToZone? fid (· == Zone.exile) with
      | some moved =>
        let g :=
          if g.stillInGame controller then
            g.createEffect (.playPermission moved.id {
              player := controller,
              payLifeEqualManaValue := true }) (cause := cause)
          else g
        g.logMsg s!"{(g.player controller).name} exiles {g.name moved}"
      | none => g
  if let .chooseReplacement .. := g.pending then
    g.chainPendingReplacement
      (.finishPostStep (.exileTopXOppPlayForLifeLoop controller pid remaining cause none))
  else if remaining == 0 || !g.stillInGame pid || !g.stillInGame controller then g
  else
    let pl := g.player pid
    if pl.library.isEmpty then
      let g := g.logMsg s!"{pl.name} has no cards in their library to exile"
      g.exileTopXOppPlayForLifeLoop controller pid (remaining - 1) cause none
    else
      let top := pl.library.back!
      let (g, _) := g.move top .exile none (cause := cause)
      if let .chooseReplacement .. := g.pending then
        g.chainPendingReplacement
          (.finishPostStep (.exileTopXOppPlayForLifeLoop controller pid (remaining - 1) cause (some top)))
      else
        g.exileTopXOppPlayForLifeLoop controller pid (remaining - 1) cause (some top)

partial def exileIdsUntilSourceLeavesLoop (g : Game) (sourceId : Option ObjectId)
    (ids : Array ObjectId) (cause : Option EventCause) : Game :=
  if let .chooseReplacement .. := g.pending then
    if ids.isEmpty then g
    else
      g.chainPendingReplacement
        (.finishPostStep (.exileIdsUntilSourceLeavesLoop sourceId ids cause))
  else
    match ids[0]? with
    | none => g
    | some oid =>
      let rem := ids.extract 1 ids.size
      let g :=
        match g.findObject? oid with
        | some o =>
          if o.isOnBattlefield then g.exileUntilSourceLeaves sourceId o (cause := cause) else g
        | none => g
      if let .chooseReplacement .. := g.pending then
        if rem.isEmpty then g
        else
          g.chainPendingReplacement
            (.finishPostStep (.exileIdsUntilSourceLeavesLoop sourceId rem cause))
      else
        g.exileIdsUntilSourceLeavesLoop sourceId rem cause

partial def exileThenReturnNextEndLoop (g : Game) (controller : PlayerId)
    (sourceId : Option ObjectId) (ids : Array ObjectId) (cause : EventCause)
    (justMovedFrom : Option ObjectId := none) (wasNontoken : Bool := false)
    (movedName : String := "") : Game :=
  let g :=
    match justMovedFrom with
    | none => g
    | some fid =>
      match g.followMovedToZone? fid (· == Zone.exile) with
      | some moved =>
        let src := (sourceId.bind g.findObject?).orElse (fun _ => some moved)
        let g :=
          if wasNontoken then
            g.registerDelayedTrigger
              { controller, source := src, kind := .endStepReturn moved.id, cause }
          else g
        g.logMsg s!"{movedName} is exiled until the beginning of the next end step"
      | none => g
  if let .chooseReplacement .. := g.pending then
    if ids.isEmpty then g
    else
      g.chainPendingReplacement
        (.finishPostStep (.exileThenReturnNextEndLoop controller sourceId ids cause))
  else
    match ids[0]? with
    | none => g
    | some id =>
      let rem := ids.extract 1 ids.size
      match g.findObject? id with
      | some o =>
        if o.isOnBattlefield then
          let name := g.name o
          let isNontoken := !o.printed.isToken
          let (g, _) := g.move o.id .exile none (cause := some cause)
          if let .chooseReplacement .. := g.pending then
            g.chainPendingReplacement
              (.finishPostStep (.exileThenReturnNextEndLoop controller sourceId rem cause (some o.id) isNontoken name))
          else
            g.exileThenReturnNextEndLoop controller sourceId rem cause (some o.id) isNontoken name
        else
          g.exileThenReturnNextEndLoop controller sourceId rem cause
      | none =>
        g.exileThenReturnNextEndLoop controller sourceId rem cause

partial def eaglesReturnCreaturesLoop (g : Game) (controller : PlayerId)
    (returnedCount : Nat) (sourceId : Option ObjectId) (remainingIds : Array ObjectId)
    (cause : Option EventCause) (targeted : Bool := true)
    (pendingReturn : Option (ObjectId × PlayerId × String) := none) : Game :=
  let (g, count) : Game × Nat :=
    match pendingReturn with
    | none => (g, returnedCount)
    | some (fromId, owner, name) =>
      if (g.followMovedToZone? fromId (· == .hand owner)).isSome then
        (g.logMsg s!"{name} is returned to {(g.player owner).name}'s hand", returnedCount + 1)
      else
        (g, returnedCount)
  if let .chooseReplacement .. := g.pending then
    g.chainPendingReplacement
      (.finishPostStep (.eaglesReturnCreaturesLoop controller count sourceId remainingIds cause targeted none))
  else
    match remainingIds[0]? with
    | none =>
      if count > 0 then
        let src := sourceId.bind g.damageSourceById?
        let g := g.registerDelayedTrigger
          { controller, source := src, kind := .eaglesBirds count
            cause := cause.getD (.gameRule .spellCast) }
        g.logMsg
          s!"At the beginning of the next upkeep, {count} Bird Soldier token(s) will be created"
      else g
    | some id =>
      let rem := remainingIds.extract 1 remainingIds.size
      match g.findObject? id with
      | none =>
        let g := if targeted then g.illegalAbilityTarget (Target.permanent id) else g
        g.eaglesReturnCreaturesLoop controller count sourceId rem cause targeted none
      | some o =>
        let ok :=
          o.isOnBattlefield && g.isCreature o && o.owner == controller &&
            (!targeted || g.canBeTargetedBy controller o sourceId)
        if ok then
          let name := g.name o
          let owner := o.owner
          let (g, _) := g.move o.id (.hand owner) none (cause := cause)
          if let .chooseReplacement .. := g.pending then
            g.chainPendingReplacement
              (.finishPostStep (.eaglesReturnCreaturesLoop controller count sourceId rem cause targeted (some (o.id, owner, name))))
          else
            g.eaglesReturnCreaturesLoop controller count sourceId rem cause targeted (some (o.id, owner, name))
        else
          let g := if targeted then g.illegalAbilityTarget (Target.permanent id) else g
          g.eaglesReturnCreaturesLoop controller count sourceId rem cause targeted none

partial def countersOnCreatureTargetsLoop (g : Game) (controller : PlayerId)
    (remaining : Array Target) (kind : CounterKind) (n : Nat)
    (sourceId : Option ObjectId) : Game :=
  match remaining[0]? with
  | none => g
  | some t =>
    let rest := remaining.extract 1 remaining.size
    let creatureLegal := g.legalTargetsForSpec controller .creature sourceId
    let g :=
      match t with
      | Target.permanent oid =>
        if creatureLegal.contains t then
          match g.findObject? oid with
          | some o => g.addCounters o kind n
          | none => g.logMsg "The target is no longer in play"
        else
          g.illegalAbilityTarget t
      | Target.card _ =>
        g.illegalAbilityTarget t
      | Target.player _ => g
    if rest.isEmpty then g
    else if let .chooseReplacement .. := g.pending then
      g.chainPendingReplacement
        (.finishPostStep (.countersOnCreatureTargetsLoop controller rest kind n sourceId))
    else
      g.countersOnCreatureTargetsLoop controller rest kind n sourceId

partial def targetPlayersGainLifeLoop (g : Game) (controller : PlayerId)
    (remaining : Array Target) (n : Nat) (sourceId : Option ObjectId)
    (cause : Option EventCause) : Game :=
  match remaining[0]? with
  | none => g
  | some t =>
    let rest := remaining.extract 1 remaining.size
    let playerLegal := g.legalTargetsForSpec controller .player sourceId
    let g :=
      match t with
      | Target.player pid =>
        if playerLegal.contains t then
          g.gainLife pid n (cause := cause)
        else
          g.illegalAbilityTarget t
      | _ => g
    if rest.isEmpty then g
    else if let .chooseReplacement .. := g.pending then
      g.chainPendingReplacement
        (.finishPostStep (.targetPlayersGainLifeLoop controller rest n sourceId cause))
    else
      g.targetPlayersGainLifeLoop controller rest n sourceId cause

def returnSourceFromGraveyard (g : Game) (sourceId : Option ObjectId)
    (controller : PlayerId) (tapped := false) (toHand := false) : Game :=
  match sourceId.bind g.findObject? with
  | none => g.logMsg "The ability's source is no longer in the graveyard"
  | some o =>
    if o.zone != .graveyard o.owner then
      g.logMsg s!"{g.name o} is no longer in the graveyard"
    else if toHand then
      g.returnToHand o.id o.owner
    else
      let name := g.name o
      let (g, newId) := g.putOntoBattlefield o.id controller (tapped := tapped)
      if let .chooseReplacement .. := g.pending then
        g.chainPendingReplacement
          (.finishPostStep (if tapped then .returnedToBattlefieldTapped o.id false else .returnedToBattlefield o.id false))
      else
        let entered := g.object! newId
        if entered.isOnBattlefield then
          let g := g.logMsg
            (if tapped then s!"{name} returns to the battlefield tapped"
             else s!"{name} returns to the battlefield")
          g.afterPermanentEnters entered
        else g

def cardHasLookType (g : Game) (o : GameObject) (t : CardSubtype) : Bool :=
  g.hasSubtype o t || (t == .equipment && g.isEquipment o)

def twoPlayersDrawSecond (g : Game) (controller second : PlayerId)
    (sourceId : Option ObjectId) (cause? : Option EventCause) : Game :=
  if g.playerCanBeTargetedBy controller second sourceId then
    g.draw second 1 (cause := cause?)
  else
    g.illegalAbilityTarget (Target.player second)

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
        g.beginFraChoice p (.orderLibraryBottom ids)
          s!"{(g.player p).name} puts the rest on the bottom of their library in any order"
      match cause with
      | some c => g.change (.stashedCause (some c))
      | none => g

def beginLookRevealToHand (g : Game) (p : PlayerId) (n : Nat)
    (ok : GameObject → Bool) (anyOrder : Bool) : Game :=
  if !g.stillInGame p then g
  else
    let looked := g.scryLookedIds p n
    let g := g.logLookAtTop p looked.size looked
    if looked.isEmpty then g
    else
      let eligible := looked.filter (fun id => (g.findObject? id).any ok)
      if eligible.isEmpty then
        if anyOrder then g.offerBottomAnyOrder p looked
        else g.putRestOnBottomRandom p looked
      else
        g.beginFraChoice p (.mayRevealToHand looked eligible anyOrder)
          s!"{(g.player p).name} may reveal a card from among them and put it into their hand"

def beginLookPutTypes (g : Game) (p : PlayerId) (n : Nat) (types : Array CardSubtype) : Game :=
  if !g.stillInGame p then g
  else
    let looked := g.scryLookedIds p n
    let g := g.logLookAtTop p looked.size looked
    if looked.isEmpty then g
    else
      let eligible := looked.filter (fun id =>
        (g.findObject? id).any (fun o => types.any (g.cardHasLookType o)))
      if eligible.isEmpty then g.putRestOnBottomRandom p looked
      else
        g.beginFraChoice p (.nickFuryPut looked eligible)
          s!"{(g.player p).name} may put a card from among them onto the battlefield"

def resolveArwenShare (g : Game) (arwenId : ObjectId) (targetId : Option ObjectId) : Game :=
  match targetId.bind g.findObject? with
  | none =>
    g.logMsg "The target is no longer legal. The ability does nothing."
  | some o =>
    if !o.isOnBattlefield || !g.isCreature o || o.id == arwenId then
      g.logMsg "The target is no longer legal. The ability does nothing."
    else
      let putCounters (g : Game) (oid : ObjectId) : Game :=
        match g.findObject? oid with
        | none => g
        | some x =>
          let g := g.addPlusOnePlusOneTo x 1
          g.addLifelinkCounter (g.object! x.id)
      let g := g.createEffect (.keywordsUntilEot o.id #[Keyword.indestructible])
      let g := g.logMsg s!"{g.name o} gains indestructible until end of turn"
      g.withBatch none fun g =>
        let g := putCounters g o.id
        putCounters g arwenId

def finishPlusOneAfterDiscards (g : Game) : Game :=
  match g.plusOneAfterDiscards with
  | none => g
  | some id =>
    let g := g.change (.plusOneAfterDiscards none)
    match g.findObject? id with
    | some o =>
      if o.isOnBattlefield then g.addPlusOnePlusOneTo o 1 else g
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

end Game
end Mtg.Engine
