import Mtg.Engine.Game.Pumps

/-!
# Searching the library (CR 701.23)

Finding cards in the library, search-to-battlefield and search-to-hand
resolutions, and exiling the top of the library for play. The player chooses
which cards to find (CR 701.23b).
-/

namespace Mtg.Engine
namespace Game

/-- Drop a leading "a " so logs read "finds no Forest card". -/
def searchNoun (kind : String) : String :=
  match kind.dropPrefix? "a " with
  | some rest => rest.toString
  | none => kind

/-- What still happens after the library is shuffled. -/
def searchAfter (p : PlayerId) : Option FraNext → AfterRandom
  | some (.gainLife n) => .gainLife p n
  | _ => .none

/-- Finish the post-untap log and ETB checks once a searched land's untap
replacement choice (e.g. stun counters, CR 122.1d / 616.1) finishes. -/
def finishSearchedUntap (g : Game) (_p : PlayerId) (landId : ObjectId) (_name : String) : Game :=
  match g.findObject? landId with
  | none => g
  | some cur =>
    let g :=
      if !cur.status.tapped then g.logMsg s!"{g.name cur} is untapped" else g
    match g.findObject? landId with
    | some cur =>
      if cur.isOnBattlefield then
        if g.isLand cur then g.afterLandEnters cur
        else g.afterPermanentEnters cur
      else g
    | none => g

/-- Finish the post-entry untap and ETB trigger checks of `placeSearched`. -/
def finishPlaceSearched (g : Game) (p : PlayerId) (fromId : ObjectId)
    (name : String) (tapped : Bool) (cause : Option EventCause := none) : Game :=
  match g.followMovedToZone? fromId (· == .battlefield) with
  | none => g
  | some entered =>
    let phrase := if tapped then " onto the battlefield tapped" else " onto the battlefield"
    let g := g.logMsg s!"{(g.player p).name} puts {name}{phrase}"
    let untapTriggered :=
      match g.untapSearchedIfLands with
      | some n =>
        let landCount := (g.permanentsOf p).foldl (fun acc (o : GameObject) =>
          if g.isLand o then acc + 1 else acc) 0
        tapped && g.isLand entered && landCount >= n
      | none => false
    if untapTriggered then
      let g := g.change (.untapSearchedIfLands none)
      let untapCause := g.resolveOptionalCause cause (fallbackCtrl := some p)
      let g := g.untapPermanent entered (logUntap := false) (cause := some untapCause)
      if let .chooseReplacement .. := g.pending then
        g.chainPendingReplacement (.finishSearchedUntap p entered.id name)
      else
        g.finishSearchedUntap p entered.id name
    else
      match g.findObject? entered.id with
      | some cur =>
        if cur.isOnBattlefield then
          if g.isLand cur then g.afterLandEnters cur
          else g.afterPermanentEnters cur
        else g
      | none => g

/-- Put `id` onto the battlefield under `p`. Lands can tap immediately. -/
def placeSearched (g : Game) (p : PlayerId) (id : ObjectId) (tapped : Bool)
    (cause : Option EventCause := none) :
    Game × Option ObjectId :=
  match g.findObject? id with
  | none => (g, none)
  | some o =>
    let name := o.name
    let (g, newId) := g.putOntoBattlefield id p (tapped := tapped)
      (cause := cause)
    if g.pending != .none then
      (g.chainPendingReplacement (.finishPlaceSearched p id name tapped cause), some id)
    else
      (g.finishPlaceSearched p id name tapped cause, some newId)

/-- Reveal `id` and put it into `p`'s hand. -/
def placeSearchedHand (g : Game) (p : PlayerId) (id : ObjectId)
    (cause : Option EventCause := none) : Game :=
  match g.findObject? id with
  | none => g
  | some o =>
    let name := o.name
    let revCause := some (cause.getD (g.resolvingOrRuleCause p))
    let g := g.record (GameEvent.revealed g.turnNumber p #[id] (cause := revCause))
    let (g, _) := g.move id (.hand p) none (cause := cause)
    let msg := s!"{(g.player p).name} reveals {name} and puts it into their hand"
    if let .chooseReplacement .. := g.pending then
      g.chainPendingReplacement (.logMessage msg)
    else if (g.followMovedToZone? id (· == .hand p)).isSome then
      g.logMsg msg
    else g

/-- Put `ids` into their owners' graveyards sequentially inside an open batch,
deferring each `"is put into ...'s graveyard"` log across `Pending.chooseReplacement`
and emitting it only if the card actually arrived in `.graveyard owner`. -/
def placeSearchedGraveyardLoop (g : Game) (ids : Array ObjectId)
    (cause : Option EventCause := none)
    (pendingLog : Option (ObjectId × PlayerId × String) := none) : Game := Id.run do
  if let .chooseReplacement .. := g.pending then
    return g.chainPendingReplacement (.placeSearchedGraveyardLoop ids cause pendingLog)
  let mut g := g
  if let some (fromId, owner, name) := pendingLog then
    if (g.followMovedToZone? fromId (· == .graveyard owner)).isSome then
      g := g.logMsg s!"{name} is put into {(g.player owner).name}'s graveyard"
  for i in [0:ids.size] do
    let id := ids[i]!
    match g.findObject? id with
    | none => pure ()
    | some o =>
      let name := o.name
      let owner := o.owner
      let (g', _) := g.move id (.graveyard owner) none (cause := cause)
      g := g'
      if let .chooseReplacement .. := g.pending then
        let rem := ids.extract (i + 1) ids.size
        return g.chainPendingReplacement
          (.placeSearchedGraveyardLoop rem cause (some (id, owner, name)))
      if (g.followMovedToZone? id (· == .graveyard owner)).isSome then
        g := g.logMsg s!"{name} is put into {(g.player owner).name}'s graveyard"
  return g

/-- Exile `ids` sequentially inside an open batch and link each card that
arrives in `.exile` to `source`'s CR 607.2a `leaveTriggerExile` list, pausing
across `Pending.chooseReplacement` via `.exileSearchedLinkedLoop`. -/
def exileSearchedLinkedLoop (g : Game) (p : PlayerId) (ids : Array ObjectId)
    (source : Option ObjectId) (cause : Option EventCause := none)
    (pendingFromId : Option ObjectId := none) : Game := Id.run do
  if let .chooseReplacement .. := g.pending then
    return g.chainPendingReplacement
      (.finishPostStep (.exileSearchedLinkedLoop p ids source cause pendingFromId))
  let mut g := g
  if let some fid := pendingFromId then
    if let some moved := g.followMovedToZone? fid (· == .exile) then
      if let some src := source.bind g.findObject? then
        g := g.changeObject src.id (.pushLeaveTriggerExile moved.id)
      g := g.logMsg s!"{(g.player p).name} exiles {moved.name}"
  for i in [0:ids.size] do
    let id := ids[i]!
    match g.findObject? id with
    | none => pure ()
    | some o =>
      let name := o.name
      let (g1, linkCause) : Game × EventCause :=
        match cause with
        | some c => (g, c)
        | none =>
          match g.currentResolvingContext? with
          | some _ => g.allocDelayedCause (some p) source
          | none => (g, .gameRule .spellCast)
      let (g2, _) := g1.move id .exile none (cause := some linkCause)
      g := g2
      if let .chooseReplacement .. := g.pending then
        let rem := ids.extract (i + 1) ids.size
        return g.chainPendingReplacement
          (.finishPostStep (.exileSearchedLinkedLoop p rem source (some linkCause) (some id)))
      if let some moved := g.followMovedToZone? id (· == .exile) then
        if let some src := source.bind g.findObject? then
          g := g.changeObject src.id (.pushLeaveTriggerExile moved.id)
        g := g.logMsg s!"{(g.player p).name} exiles {name}"
  return g

/-- Exile `id` and link the exiled card to `source` via CR 607.2a `leaveTriggerExile`. -/
def exileSearchedLinked (g : Game) (p : PlayerId) (id : ObjectId)
    (source : Option ObjectId) (cause : Option EventCause := none) : Game :=
  g.exileSearchedLinkedLoop p #[id] source cause

/-- Behold `subtype`. If you do, untap the land this search just found (CR 608.2c / 701.4). -/
def beholdAndMaybeUntap (g : Game) (p : PlayerId) (landId : ObjectId) (subtype : CardSubtype) : Game :=
  let instrCause (g : Game) (defaultCause : EventCause) : EventCause :=
    match g.currentResolvingContext? with
    | some (s, c) => .oneShotEffect none s (c.orElse (fun _ => some p))
    | none => defaultCause
  let g := g.beholdQuality p subtype (cause := some (instrCause g (.gameRule .spellCast)))
  if !g.qualityWasBeheld p subtype then g
  else
    match g.followMovedToZone? landId (· == .battlefield) with
    | some o =>
      if o.isOnBattlefield && o.status.tapped && !g.hostCantBecomeUntapped o then
        let untapCause := instrCause g (.turnBased .untapAll)
        g.untapPermanent o (cause := some untapCause)
      else g
    | none => g

/-- Run a search's post-shuffle action when the shuffle did not pause. -/
def applySearchAfter (g : Game) : Game :=
  let after := g.afterRandom
  let g := g.change (.afterRandom .none)
  match after with
  | .putOnTop p ids => g.putIdsOnTop p ids
  | .beholdUntap p landId subtype => g.beholdAndMaybeUntap p landId subtype
  | .plusOne id ctrl srcId => g.addPlusOneIfStillCreature id ctrl srcId
  | .discardRandom p =>
    let hand := (g.player p).hand
    if hand.isEmpty then g
    else if hand.size == 1 then g.discardFromHandRandomly p hand[0]!
    else g.changes #[.pending (.resolveRandom (.chooseObject hand)), .afterRandom (.discardRandom p)]
  | other => g.change (.afterRandom other)

/-- Shuffle, then run `onDone`. A random pause keeps `onDone` until the
host supplies the order. An as-enters or replacement choice already waiting
completes first and then runs the shuffle via `PendingReplacement.shuffleThen`. -/
def shuffleThen (g : Game) (p : PlayerId) (onDone : AfterRandom) : Game :=
  if g.pending != .none && g.pendingRandom?.isNone then
    g.chainPendingReplacement (.shuffleThen p onDone)
  else
    g.withContinuationFrame fun g =>
      let g := g.requestShuffle p onDone
      if g.pendingRandom?.isSome then g
      else
        let g := g.continueIfShuffled
        g.applySearchAfter

/-- The post-shuffle action, including a +1/+1 counter waiting on this search. -/
def searchDone (g : Game) (p : PlayerId) (after : Option FraNext) : Game × AfterRandom :=
  match g.plusOneAfterSearch with
  | some (id, ctrl, srcId) => (g.change (.plusOneAfterSearch none), .plusOne id ctrl srcId)
  | none => (g, searchAfter p after)

/-- Shuffle, then run the search's after-action. -/
def shuffleSearch (g : Game) (p : PlayerId) (after : Option FraNext) : Game :=
  let g := g.change (.untapSearchedIfLands none)
  let (g, done) := g.searchDone p after
  g.shuffleThen p done

/-- Put the waiting post-search counter when this search does not shuffle. -/
def applyWaitingPlusOne (g : Game) : Game :=
  match g.plusOneAfterSearch with
  | none => g
  | some (id, ctrl, srcId) =>
    addPlusOneIfStillCreature (g.change (.plusOneAfterSearch none)) id ctrl srcId

/-- Two-pass simultaneous battlefield placement for `placeSearchedBatch`:
first move every searched card in `remainingIds` onto `.battlefield` using
shared `preBf` (so co-entering permanents see each other's presence during
post-entry checks and share a single arrival `BatchId`), then run
`finishPlaceSearched` on each `entered` card. -/
def placeSearchedBatchCore (g : Game) (p : PlayerId) (remainingIds : Array ObjectId)
    (tapped : Bool) (cause : Option EventCause := none)
    (entered : Array (ObjectId × String) := #[])
    (preBattlefield : Option (Array GameObject) := none) : Game := Id.run do
  let preBf := preBattlefield.getD g.battlefield
  let mut g := g
  let mut entered := entered
  for i in [0:remainingIds.size] do
    let id := remainingIds[i]!
    match g.findObject? id with
    | none => pure ()
    | some o =>
      let name := o.name
      let (g', _) := g.putOntoBattlefield id p (tapped := tapped)
        (preBattlefield := some preBf) (cause := cause)
      g := g'
      entered := entered.push (id, name)
      if g.pending != .none then
        let rem := remainingIds.extract (i + 1) remainingIds.size
        return g.chainPendingReplacement
          (.placeSearchedBatch p rem tapped cause entered (some preBf))
  for i in [0:entered.size] do
    let (fromId, name) := entered[i]!
    g := g.finishPlaceSearched p fromId name tapped cause
    if g.pending != .none then
      let remEntered := entered.extract (i + 1) entered.size
      if !remEntered.isEmpty then
        g := g.chainPendingReplacement
          (.placeSearchedBatch p #[] tapped cause remEntered (some preBf))
      return g
  return g

/-- Place each searched card in `ids` onto the battlefield simultaneously in a
single `withBatch`, chaining `.placeSearchedBatch` if an earlier placement or
untap replacement pauses on `Pending.chooseReplacement`. -/
def placeSearchedBatch (g : Game) (p : PlayerId) (ids : Array ObjectId) (tapped : Bool)
    (cause : Option EventCause := none)
    (entered : Array (ObjectId × String) := #[])
    (preBattlefield : Option (Array GameObject) := none) : Game :=
  if preBattlefield.isSome then
    g.placeSearchedBatchCore p ids tapped cause entered preBattlefield
  else
    g.withBatch cause fun g =>
      g.placeSearchedBatchCore p ids tapped cause entered (some g.battlefield)

/-- Finish the post-`placeSearched` steps (moving remaining cards to hand,
shuffling, behold-untap, or waiting `+1/+1` counter) of `finishLibrarySearch`. -/
def finishSearchAfterPlace (g : Game) (p : PlayerId) (fromId : Option ObjectId)
    (dest : SearchDest) (after : Option FraNext) (fromLibrary : Bool)
    (handRest : Array ObjectId := #[]) (cause : Option EventCause := none) : Game :=
  match dest with
  | .battlefield _ =>
    g.shuffleSearch p after
  | .battlefieldTappedThenHand =>
    let g :=
      if handRest.isEmpty then g
      else g.withBatch cause fun g =>
        handRest.foldl (fun g id => g.placeSearchedHand p id (cause := cause)) g
    g.shuffleSearch p after
  | .battlefieldTappedBeholdUntap subtype =>
    match fromId.bind (fun fid => g.followMovedToZone? fid (· == .battlefield)) with
    | some o => g.shuffleThen p (.beholdUntap p o.id subtype)
    | none => g.shuffleSearch p after
  | .battlefieldFromHandOrLibrary =>
    if fromLibrary then g.shuffleSearch p after else g.applyWaitingPlusOne
  | _ => g.shuffleSearch p after

/-- Send the chosen cards to `dest`, shuffle, then do `after`. An empty `ids`
is "chooses not to find" (CR 701.23b). -/
def finishLibrarySearch (g : Game) (p : PlayerId) (ids : Array ObjectId)
    (dest : SearchDest) (after : Option FraNext) (kind : String) : Game :=
  let allocSearchStepCause (g : Game) (source : Option ObjectId := none) : Game × EventCause :=
    match g.currentResolvingContext? with
    | some _ => g.allocDelayedCause (some p) source
    | none => (g, .gameRule .spellCast)
  let noun := searchNoun kind
  if ids.isEmpty then
    let g := g.record (GameEvent.searched g.turnNumber p p #[] (cause := some (g.resolvingOrRuleCause p)))
    let g := g.logMsg s!"{(g.player p).name} chooses not to find a {noun}"
    match dest with
    | .handThenDiscardRandom => g.shuffleThen p (.discardRandom p)
    | _ => g.shuffleSearch p after
  else
    match dest with
    | .battlefield tapped =>
      let (g, cause) := allocSearchStepCause g
      let g := g.record (GameEvent.searched g.turnNumber p p ids (cause := some cause))
      let g := g.placeSearchedBatch p ids tapped (cause := some cause)
      if g.pending != .none then
        g.chainPendingReplacement (.finishSearchAfterPlace p none dest after true #[] (some cause))
      else
        g.finishSearchAfterPlace p none dest after true #[] (some cause)
    | .hand =>
      let (g, cause) := allocSearchStepCause g
      let g := g.record (GameEvent.searched g.turnNumber p p ids (cause := some cause))
      let g := g.withBatch (some cause) fun g =>
        ids.foldl (fun g id => g.placeSearchedHand p id (cause := some cause)) g
      g.shuffleSearch p after
    | .handThenDiscardRandom =>
      let (g, cause) := allocSearchStepCause g
      let g := g.record (GameEvent.searched g.turnNumber p p ids (cause := some cause))
      let g := g.withBatch (some cause) fun g =>
        ids.foldl (fun g id => g.placeSearchedHand p id (cause := some cause)) g
      g.shuffleThen p (.discardRandom p)
    | .graveyard =>
      let (g, cause) := allocSearchStepCause g
      let g := g.record (GameEvent.searched g.turnNumber p p ids (cause := some cause))
      let g := g.withBatch (some cause) fun g =>
        g.placeSearchedGraveyardLoop ids (cause := some cause)
      if g.pending != .none then
        g.chainPendingReplacement (.finishSearchAfterPlace p none dest after true #[] (some cause))
      else
        g.finishSearchAfterPlace p none dest after true #[] (some cause)
    | .topAfterShuffle =>
      let (g, cause) := allocSearchStepCause g
      let g := g.record (GameEvent.searched g.turnNumber p p ids (cause := some cause))
      let g := g.record (GameEvent.revealed g.turnNumber p ids (cause := some cause))
      let g := ids.foldl (fun g id =>
        match g.findObject? id with
        | some o => g.logMsg s!"{(g.player p).name} reveals {o.name}"
        | none => g) g
      g.shuffleThen p (.putOnTop p ids)
    | .exileLinked source =>
      let (g, linkCause) := allocSearchStepCause g source
      let g := g.record (GameEvent.searched g.turnNumber p p ids (cause := some linkCause))
      let g := g.withBatch (some linkCause) fun g =>
        g.exileSearchedLinkedLoop p ids source (cause := some linkCause)
      g.shuffleSearch p after
    | .battlefieldTappedThenHand =>
      let (g, cause) := allocSearchStepCause g
      let g := g.record (GameEvent.searched g.turnNumber p p ids (cause := some cause))
      let handRest := ids.extract 1 ids.size
      let g :=
        match ids[0]? with
        | some id => (g.placeSearched p id true (cause := some cause)).1
        | none => g
      if g.pending != .none then
        g.chainPendingReplacement
          (.finishSearchAfterPlace p ids[0]? dest after true handRest (some cause))
      else
        g.finishSearchAfterPlace p ids[0]? dest after true handRest (some cause)
    | .battlefieldTappedBeholdUntap _ =>
      match ids[0]? with
      | none => g.shuffleSearch p after
      | some id =>
        let (g, cause) := allocSearchStepCause g
        let g := g.record (GameEvent.searched g.turnNumber p p ids (cause := some cause))
        let (g, _) := g.placeSearched p id true (cause := some cause)
        if g.pending != .none then
          g.chainPendingReplacement
            (.finishSearchAfterPlace p (some id) dest after true #[] (some cause))
        else
          g.finishSearchAfterPlace p (some id) dest after true #[] (some cause)
    | .battlefieldFromHandOrLibrary =>
      let libIds := ids.filter (fun id =>
        (g.findObject? id).any (·.zone == .library p))
      let fromLibrary := !libIds.isEmpty
      let (g, cause) := allocSearchStepCause g
      let g :=
        if fromLibrary then
          g.record (GameEvent.searched g.turnNumber p p libIds (cause := some cause))
        else g
      let g := g.placeSearchedBatch p ids false (cause := some cause)
      if g.pending != .none then
        g.chainPendingReplacement
          (.finishSearchAfterPlace p none dest after fromLibrary #[] (some cause))
      else
        g.finishSearchAfterPlace p none dest after fromLibrary #[] (some cause)

/-- Search `p`'s library for up to `count` cards matching `pred` (CR 701.23).
The player chooses which, or none (CR 701.23b). `optional` may skip the
search entirely, and then the library is not shuffled. -/
def beginLibrarySearch (g : Game) (p : PlayerId) (pred : CardDef → Bool) (kind : String)
    (dest : SearchDest) (count : Nat := 1) (after : Option FraNext := none)
    (alsoHand : Bool := false) (optional : Bool := false) : Game :=
  if !g.stillInGame p then g
  else
    let keep (id : ObjectId) := (g.findObject? id).any (fun o => pred (g.baseCard o))
    let pl := g.player p
    let eligible := (if alsoHand then pl.hand.filter keep else #[]) ++ pl.library.filter keep
    if optional then
      (g.change (.pending (.fraChoice p (.maySearchLibrary eligible count dest after kind)))).logMsg
        s!"{pl.name} may search for {kind}"
    else if eligible.isEmpty then
      let g := g.record (GameEvent.searched g.turnNumber p p #[] (cause := some (g.resolvingOrRuleCause p)))
      let g := g.logMsg s!"{pl.name} finds no {searchNoun kind}"
      match dest with
      | .handThenDiscardRandom => g.shuffleThen p (.discardRandom p)
      | _ => g.shuffleSearch p after
    else
      (g.change (.pending (.fraChoice p (.searchLibrary eligible count dest after kind)))).logMsg
        s!"{pl.name} searches for {kind}"

/-- `p` may search for `count` basic land cards and put them onto the
battlefield tapped (Settle the Wreckage, Avengers Disassembled). Declining
does not shuffle. -/
def offerMaySearchBasics (g : Game) (p : PlayerId) (count : Nat := 1) : Game :=
  if count == 0 || !g.stillInGame p then g
  else
    let kind :=
      if count == 1 then "a basic land card"
      else s!"{count} basic land cards"
    g.beginLibrarySearch p isBasicLandCard kind (.battlefield true) count
      (optional := true)

/-- Search `p`'s library for a card matching `pred` and put it onto the
battlefield (tapped if `tapped`), then shuffle (CR 701.23). -/
def resolveSearchLibrary (g : Game) (p : PlayerId) (pred : CardDef → Bool)
    (tapped : Bool) (kind : String) : Game :=
  g.beginLibrarySearch p pred kind (.battlefield tapped)

/-- Search `p`'s library for a basic land card, put it onto the battlefield
tapped, then shuffle (CR 701.23). -/
def resolveSearchBasicLandTapped (g : Game) (p : PlayerId) : Game :=
  g.resolveSearchLibrary p isBasicLandCard true "a basic land card"

/-- Search `p`'s library for a Forest card, put it onto the battlefield, then
shuffle (CR 701.23 / 305.7). -/
def resolveSearchForest (g : Game) (p : PlayerId) : Game :=
  g.resolveSearchLibrary p isForestCard false "a Forest card"

/-- Search `p`'s library for a card matching `pred`, reveal it, put it into
their hand, then shuffle. -/
def resolveLibrarySearchToHand (g : Game) (p : PlayerId)
    (pred : CardDef → Bool) (kind : String) : Game :=
  g.beginLibrarySearch p pred kind .hand

/-- Search `p`'s library for a card with land type `landType`, reveal it, put
it into their hand, then shuffle (CR 701.23 / 702.29). -/
def resolveSearchLandTypeToHand (g : Game) (p : PlayerId) (landType : CardSubtype) : Game :=
  g.resolveLibrarySearchToHand p (fun c => c.hasSubtype landType) s!"{landType} card"

/-- Search `p`'s library for a basic land, put it into their hand, then shuffle. -/
def resolveSearchBasicLandToHand (g : Game) (p : PlayerId) : Game :=
  g.resolveLibrarySearchToHand p isBasicLandCard "basic land card"

/-- Exile the top card of `p`'s library and grant permission to play it until
the end of that player's next turn (CR 701.18). -/
def resolveExileTopPlayUntilEndOfNextTurn (g : Game) (p : PlayerId) : Game :=
  let pl := g.player p
  if pl.library.isEmpty then
    g.logMsg s!"{pl.name} has no cards in their library to exile"
  else
    let top := pl.library.back!
    let (g, cause) := g.allocDelayedCause (some p)
    let (g, _) := g.move top .exile none (cause := some cause)
    if let .chooseReplacement .. := g.pending then
      g.chainPendingReplacement
        (.finishPostStep (.grantPlayUntilEndOfNextTurn p top (some cause)))
    else
      match g.followMovedToZone? top (· == .exile) with
      | some moved =>
        let g := g.createEffect (.playPermission moved.id { player := p } (turnEnds := 2))
          (cause := some cause)
        g.logMsg
          s!"{pl.name} exiles {moved.name} and may play it until the end of their next turn"
      | none => g

end Game
end Mtg.Engine
