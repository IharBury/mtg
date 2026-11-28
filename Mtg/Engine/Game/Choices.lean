import Mtg.Engine.Game.Casting

/-!
# Resolution choices

Choices made while resolving: sacrifice choices, lifetime modal choices
(Alliance, Gollum), and card-specific helpers such as beholding a
quality, Riddles in the Dark, The Black Gate, and Gríma's exile.
-/

namespace Mtg.Engine
namespace Game

/-- Whether `sac` is a legal “another creature or artifact” sacrifice for `sourceId`. -/
def canSacrificeAsCreatureOrArtifact (g : Game) (p : PlayerId) (sourceId : ObjectId)
    (sac : GameObject) : Bool :=
  (g.sacrificeCreatureOrArtifactChoices p sourceId).any (·.id == sac.id)

/-- Modes in `all` that have not yet been chosen. -/
def unusedModes (chosen : Array Nat) (all : Array Nat := #[0, 1, 2]) : Array Nat :=
  all.filter (fun m => !chosen.contains m)

/-- Unused Alliance modes on `src` (0 = add GGG, 1 = +1/+1 each, 2 = scry 2
then draw). -/
def unusedAllianceModes (g : Game) (src : GameObject) : Array Nat :=
  unusedModes (g.modesChosenThisTurn src.id)

/-- Unused Gollum modes on `src` (0 = +1/+1, 1 = drain, 2 = draw). Modes last
for the object's lifetime (ruling 164). -/
def unusedGollumModes (g : Game) (src : GameObject) : Array Nat :=
  unusedModes (g.modesChosenEver src.id)

/-- Behold a quality: choose a matching permanent you control or reveal a
matching card from your hand. Later zone changes do not un-behold (117). -/
def beholdQuality (g : Game) (p : PlayerId) (quality : CardSubtype)
    (cause : Option EventCause := none) : Game :=
  if !g.stillInGame p then g
  else
    let hasPerm := (g.permanentsOf p).any (fun o => g.hasSubtype o quality)
    let handMatch? :=
      (g.player p).hand.find? (fun id =>
        match g.findObject? id with
        | some o => isDiscardableCard o && g.hasSubtype o quality
        | none => false)
    if hasPerm || handMatch?.isSome then
      let effCause := g.resolveOptionalCause cause (fallbackCtrl := some p)
      let g := g.withBatch (some effCause) fun g =>
        let g :=
          if !hasPerm then
            match handMatch? with
            | some hid => g.record (GameEvent.revealed g.turnNumber p #[hid] (cause := some effCause))
            | none => g
          else g
        g.record (GameEvent.beheld g.turnNumber p quality (cause := effCause))
      g.logMsg s!"{(g.player p).name} beholds a {quality}"
    else
      g.logMsg s!"{(g.player p).name} does not behold a {quality}"

/-- True when `p` has beheld `quality`, even if the card or permanent later left. -/
def qualityWasBeheld (g : Game) (p : PlayerId) (quality : CardSubtype) : Bool :=
  (g.beheldQualities p).contains quality

/-- The creature type `p` chooses for “choose a creature type”: the type most
common among creatures they control. -/
def chooseCreatureTypeFor (g : Game) (p : PlayerId) : CardSubtype :=
  let counts : Array (CardSubtype × Nat) :=
    (g.creaturesControlledBy p).foldl (fun acc o =>
      (g.subtypes o).foldl (fun acc t =>
        if !t.isCreatureType then acc
        else
          match acc.findIdx? (·.1 == t) with
          | some i => acc.modify i (fun (s, n) => (s, n + 1))
          | none => acc.push (t, 1)) acc) #[]
  (counts.foldl (fun best c =>
    match best with
    | none => some c
    | some b => if c.2 > b.2 then some c else best) none).map (·.1) |>.getD .human

/-- Distinct creature types currently on the battlefield. -/
def battlefieldCreatureTypes (g : Game) : Array CardSubtype :=
  g.battlefield.foldl (fun acc o =>
    if !g.isCreature o then acc
    else
      (g.subtypes o).foldl (fun acc t =>
        if t.isCreatureType && !acc.contains t then acc.push t else acc) acc) #[]

/-- Draw one card for each graveyard with seven or more cards. -/
def drawPerSevenCardGraveyard (g : Game) (p : PlayerId) : Game :=
  if !g.stillInGame p then g
  else
    let n := g.players.filter (fun pl =>
      (pl.graveyard.filter (fun id => (g.findObject? id).any isDiscardableCard)).size >= 7) |>.size
    if n == 0 then
      g.logMsg s!"{(g.player p).name} draws no cards (no graveyard has seven cards)"
    else
      g.draw p n

/-- Pause-safe loop discarding `ids` from `p`'s hand inside an open batch. -/
def discardHandIdsLoop (g : Game) (p : PlayerId) (ids : Array ObjectId)
    (logEach : Bool := false) (cause : Option EventCause := none)
    (fromEventIdx? : Option Nat := none) : Game := Id.run do
  let deferPfe := ids.size > 1 || fromEventIdx?.isSome
  let loopFromIdx := fromEventIdx?.getD g.events.size
  if g.sbaPaused then
    return g.chainPendingReplacement
      (.finishPostStep (.discardHandIdsLoop p ids logEach cause (if deferPfe then some loopFromIdx else none)))
  let preLoopStart := g
  let mkPreLoop : Unit → Game := fun _ =>
    match fromEventIdx? with
    | some idx => g.mkHistoricalGameAt idx
    | none => preLoopStart
  let mut g := g
  for i in [0:ids.size] do
    let id := ids[i]!
    match g.findObject? id with
    | none => pure ()
    | some o =>
      if o.zone == .hand p && isDiscardableCard o then
        let msg := s!"{(g.player p).name} discards {g.name o}"
        let owner := o.owner
        let (g', _) := g.move id (.graveyard owner) none (verb := some .discard)
          (actor := some p) (cause := cause) (deferPlayFromExileLogs := deferPfe)
        g := g'
        if g.sbaPaused then
          if logEach then
            g := g.chainPendingReplacement (.finishPostStep (.logDiscardIfInGraveyard id owner msg))
          let rem := ids.extract (i + 1) ids.size
          if !rem.isEmpty || deferPfe then
            g := g.chainPendingReplacement
              (.finishPostStep (.discardHandIdsLoop p rem logEach cause (if deferPfe then some loopFromIdx else none)))
          return g
        if logEach && (g.followMovedToZone? id (· == .graveyard owner)).isSome then
          g := g.logMsg msg
  return if deferPfe then emitExpiredPlayFromExileLogsLazy mkPreLoop g loopFromIdx else g

/-- Pause-safe loop discarding `(p, id)` pairs across multiple players inside a
single shared open batch (CR 101.4 / 603.2c / 701.9b). -/
def discardMultiHandIdsLoop (g : Game) (remaining : Array (PlayerId × ObjectId))
    (logEach : Bool := false) (cause : Option EventCause := none)
    (fromEventIdx? : Option Nat := none) : Game := Id.run do
  let deferPfe := remaining.size > 1 || fromEventIdx?.isSome
  let loopFromIdx := fromEventIdx?.getD g.events.size
  if g.sbaPaused then
    return g.chainPendingReplacement
      (.finishPostStep (.discardMultiHandIdsLoop remaining logEach cause (if deferPfe then some loopFromIdx else none)))
  let preLoopStart := g
  let mkPreLoop : Unit → Game := fun _ =>
    match fromEventIdx? with
    | some idx => g.mkHistoricalGameAt idx
    | none => preLoopStart
  let mut g := g
  for i in [0:remaining.size] do
    let (p, id) := remaining[i]!
    match g.findObject? id with
    | none => pure ()
    | some o =>
      if g.stillInGame p && o.zone == .hand p && isDiscardableCard o then
        let msg := s!"{(g.player p).name} discards {g.name o}"
        let owner := o.owner
        let (g', _) := g.move id (.graveyard owner) none (verb := some .discard)
          (actor := some p) (cause := cause) (deferPlayFromExileLogs := deferPfe)
        g := g'
        if g.sbaPaused then
          if logEach then
            g := g.chainPendingReplacement (.finishPostStep (.logDiscardIfInGraveyard id owner msg))
          let rem := remaining.extract (i + 1) remaining.size
          if !rem.isEmpty || deferPfe then
            g := g.chainPendingReplacement
              (.finishPostStep (.discardMultiHandIdsLoop rem logEach cause (if deferPfe then some loopFromIdx else none)))
          return g
        if logEach && (g.followMovedToZone? id (· == .graveyard owner)).isSome then
          g := g.logMsg msg
  return if deferPfe then emitExpiredPlayFromExileLogsLazy mkPreLoop g loopFromIdx else g

/-- Discard every card in `p`'s hand. Zero cards is a legal discard and is
logged (Sauron, the Dark Lord). -/
def discardEntireHand (g : Game) (p : PlayerId) (cause : Option EventCause := none) : Game :=
  if !g.stillInGame p then g
  else
    let ids := g.discardableHandIds p
    let preDiscards := g.loggedDiscards p
    let (g, cause?) : Game × Option EventCause :=
      match cause with
      | some c => (g, some c)
      | none =>
        if ids.isEmpty then (g, none)
        else
          match g.currentResolvingContext? with
          | some (src, ctrl) =>
            let (g, c) := g.allocDelayedCause (ctrl.orElse (fun _ => some p)) src
            (g, some c)
          | none => (g, none)
    let g := g.withBatch cause? fun g =>
      g.discardHandIdsLoop p ids (logEach := false) (cause := cause?)
    if g.sbaPaused then
      g.chainPendingReplacement (.finishPostStep (.logDiscardedCount p preDiscards))
    else
      let discarded := g.loggedDiscards p - preDiscards
      g.logMsg s!"{(g.player p).name} discards {discarded} card(s)"

/-- Discard the hand (zero cards is legal) and draw that many. The choice is
made during resolution; nothing happens between discard and draw. -/
def mayDiscardHandDrawThatMany (g : Game) (p : PlayerId) (doDiscard : Bool) : Game :=
  if !g.stillInGame p then g
  else if !doDiscard then
    g.logMsg s!"{(g.player p).name} does not discard their hand"
  else
    let n := (g.discardableHandIds p).size
    let g := g.discardEntireHand p
    if n == 0 then g
    else if g.sbaPaused then
      g.chainPendingReplacement (.finishPostStep (.wheelDrawThenOfferNext p n))
    else g.draw p n

/-- Discard the hand, then draw `n` cards. An empty hand is a legal discard
(Sauron, the Dark Lord). -/
def discardHandThenDraw (g : Game) (p : PlayerId) (n : Nat) : Game :=
  if !g.stillInGame p then g
  else
    let g := g.discardEntireHand p
    if n == 0 then g
    else if g.sbaPaused then
      g.chainPendingReplacement (.finishPostStep (.wheelDrawThenOfferNext p n))
    else g.draw p n

/-- Move or put each card in `remainingIds` onto the battlefield sequentially,
pausing on `Pending.chooseReplacement` (`PendingReplacement.putToBattlefieldLoop`)
and running `afterPermanentEnters` / `afterLandEnters` (plus optional haste,
entry log, or Food-artifact log) only after all cards have finished entering. -/
def putToBattlefieldLoop (g : Game) (controller : PlayerId)
    (remainingIds : Array ObjectId)
    (enteredFromIds : Array ObjectId := #[])
    (useCardOwner : Bool := false)
    (haste : Bool := false)
    (tapped : Bool := false)
    (isLandEnters : Bool := false)
    (onlyFoodArtifact : Bool := false)
    (entryLog : PutBattlefieldEntryLog := .none)
    (cause : Option EventCause := none)
    (preBattlefield : Option (Array GameObject) := none)
    (fromEventIdx? : Option Nat := none) : Game := Id.run do
  let deferPfe := remainingIds.size > 1 || fromEventIdx?.isSome
  let loopFromIdx := fromEventIdx?.getD g.events.size
  if g.sbaPaused then
    return g.chainPendingReplacement
      (.putToBattlefieldLoop controller remainingIds enteredFromIds
        useCardOwner haste tapped isLandEnters onlyFoodArtifact entryLog cause preBattlefield
        (if deferPfe then some loopFromIdx else none))
  let preLoopStart := g
  let mkPreLoop : Unit → Game := fun _ =>
    match fromEventIdx? with
    | some idx => g.mkHistoricalGameAt idx
    | none => preLoopStart
  let preBf := preBattlefield.getD g.battlefield
  let mut g := g
  let mut entered := enteredFromIds
  for i in [0:remainingIds.size] do
    let id := remainingIds[i]!
    match g.findObject? id with
    | none => pure ()
    | some o =>
      if onlyFoodArtifact && (o.zone != .graveyard o.owner || !isDiscardableCard o) then
        pure ()
      else
        let ctrl := if useCardOwner then o.owner else controller
        let (g', _) :=
          if onlyFoodArtifact then
            g.move id .battlefield (some ctrl)
              (summoningSick := true) (applyHope := false)
              (onlyFoodArtifact := true) (preBattlefield := some preBf) (cause := cause)
              (deferPlayFromExileLogs := deferPfe)
          else
            g.putOntoBattlefield id ctrl (tapped := tapped)
              (preBattlefield := some preBf) (cause := cause)
              (deferPlayFromExileLogs := deferPfe)
        g := g'
        entered := entered.push id
        if g.sbaPaused then
          let rem := remainingIds.extract (i + 1) remainingIds.size
          return g.chainPendingReplacement
            (.putToBattlefieldLoop controller rem entered
              useCardOwner haste tapped isLandEnters onlyFoodArtifact entryLog cause (some preBf)
              (if deferPfe then some loopFromIdx else none))
  if deferPfe then
    g := emitExpiredPlayFromExileLogsLazy mkPreLoop g loopFromIdx
  for j in [0:entered.size] do
    let fromId := entered[j]!
    match g.followMovedToZone? fromId (· == .battlefield) with
    | none => pure ()
    | some enteredObj =>
      match entryLog with
      | .none => pure ()
      | .enters => g := g.logMsg s!"{g.name enteredObj} enters the battlefield"
      | .entersTapped => g := g.logMsg s!"{g.name enteredObj} enters tapped"
      if haste then
        g := g.createEffect (.keywordsUntilEot enteredObj.id #[Keyword.haste]) (cause := cause)
      if onlyFoodArtifact then
        if let some cur := g.findObject? enteredObj.id then
          g := g.logMsg s!"{g.name cur} returns as a Food artifact"
      g :=
        if isLandEnters then g.afterLandEnters (g.object! enteredObj.id)
        else g.afterPermanentEnters (g.object! enteredObj.id)
      if g.sbaPaused then
        let remEntered := entered.extract (j + 1) entered.size
        if !remEntered.isEmpty then
          g := g.chainPendingReplacement
            (.putToBattlefieldLoop controller #[] remEntered
              useCardOwner haste tapped isLandEnters onlyFoodArtifact entryLog cause (some preBf) none)
        return g
  return g

/-- Put the returned cards onto the battlefield as Food artifacts only.
They keep name, mana cost, mana value, abilities, and legendary. -/
def supperForSpidersReturn (g : Game) (controller : PlayerId)
    (ids : Array ObjectId) : Game :=
  g.withBatch none fun g =>
    g.putToBattlefieldLoop controller ids (onlyFoodArtifact := true)

/-- Pause-safe loop for `exileTopPlayIfYouControlSubtype`. -/
def exileTopPlayIfYouControlSubtypeLoop (g : Game) (p : PlayerId)
    (subtype : CardSubtype) (remaining : Nat) (cause? : Option EventCause)
    (movedId? : Option ObjectId := none)
    (fromEventIdx? : Option Nat := none) : Game := Id.run do
  let deferPfe := remaining > 0 || fromEventIdx?.isSome
  let loopFromIdx := fromEventIdx?.getD g.events.size
  if g.sbaPaused then
    return g.chainPendingReplacement
      (.finishPostStep (.exileTopPlayIfYouControlSubtypeLoop p subtype remaining cause? movedId?
        (if deferPfe then some loopFromIdx else none)))
  let preLoopStart := g
  let mkPreLoop : Unit → Game := fun _ =>
    match fromEventIdx? with
    | some idx => g.mkHistoricalGameAt idx
    | none => preLoopStart
  let mut g := g
  if let some fid := movedId? then
    if let some moved := g.followMovedToZone? fid (· == .exile) then
      if g.stillInGame p then
        g := g.createEffect (.playPermission moved.id {
            player := p
            whileExiled := true
            requireSubtype := some subtype
            faceDown := true })
          (cause := cause?)
      g := g.logMsg s!"{(g.player p).name} exiles a card face down"
  if !g.stillInGame p then
    return if deferPfe then emitExpiredPlayFromExileLogsLazy mkPreLoop g loopFromIdx else g
  for i in [0:remaining] do
    if !g.stillInGame p then
      return if deferPfe then emitExpiredPlayFromExileLogsLazy mkPreLoop g loopFromIdx else g
    let pl := g.player p
    if pl.library.isEmpty then
      g := g.logMsg s!"{pl.name} has no cards in their library to exile"
    else
      let top := pl.library.back!
      let (g', _) := g.move top .exile none (cause := cause?) (deferPlayFromExileLogs := true)
      g := g'
      if g.sbaPaused then
        let rem := remaining - (i + 1)
        return g.chainPendingReplacement
          (.finishPostStep (.exileTopPlayIfYouControlSubtypeLoop p subtype rem cause? (some top) (some loopFromIdx)))
      if let some moved := g.followMovedToZone? top (· == .exile) then
        if g.stillInGame p then
          g := g.createEffect (.playPermission moved.id {
              player := p
              whileExiled := true
              requireSubtype := some subtype
              faceDown := true })
            (cause := cause?)
        g := g.logMsg s!"{pl.name} exiles a card face down"
  if deferPfe then
    g := emitExpiredPlayFromExileLogsLazy mkPreLoop g loopFromIdx
  return g

/-- Exile the top `n` cards face down. They may be played while exiled if you
control `subtype` (CR 610.1 / 701.18). Timing and costs are unchanged. -/
def exileTopPlayIfYouControlSubtype (g : Game) (p : PlayerId) (n : Nat)
    (subtype : CardSubtype) : Game :=
  if n == 0 || !g.stillInGame p then g
  else
    let (g0, cause?) : Game × Option EventCause :=
      if (g.player p).library.isEmpty then (g, none)
      else
        let (g, c) := g.allocDelayedCause (some p)
        (g, some c)
    g0.withBatch cause? fun g =>
      g.exileTopPlayIfYouControlSubtypeLoop p subtype n cause?

/-- Finish the direct-cast step of `grimaExileUntilInstantOrSorcery` once
moving `fromId` to `.stack` completes, then put `others` on the bottom of
`victim`'s library in a random order. -/
def finishGrimaDirectCast (g : Game) (controller victim : PlayerId)
    (fromId : ObjectId) (others : Array ObjectId)
    (cause : Option EventCause) : Game :=
  let g :=
    match g.followMovedToZone? fromId (· == .stack) with
    | some moved =>
      g.logMsg s!"{(g.player controller).name} casts {g.name moved} as the ability resolves"
    | none => g
  if !g.stillInGame victim then g
  else
    g.requestOrderInto others (.library victim)
      s!"{(g.player victim).name} puts the remaining exiled cards on the bottom of their library in a random order"
      (cause := cause)

/-- Pause-safe loop exiling cards from the top of `victim`'s library face up
until an instant or sorcery card is exiled (or the library is empty), following
each moved card via `followMovedToZone?` across `Pending.chooseReplacement`
pausing and then casting or bottoming the exiled cards. -/
partial def exileUntilInstantOrSorceryLoop (g : Game) (victim controller : PlayerId)
    (castTheCard : Bool) (cause : Option EventCause := none)
    (others : Array ObjectId := #[])
    (pendingFromId : Option ObjectId := none)
    (fromEventIdx? : Option Nat := none) : Game := Id.run do
  let loopFromIdx := fromEventIdx?.getD g.events.size
  if g.sbaPaused then
    return g.chainPendingReplacement
      (.finishPostStep (.exileUntilInstantOrSorceryLoop victim controller castTheCard cause others pendingFromId (some loopFromIdx)))
  let preLoopStart := g
  let mkPreLoop : Unit → Game := fun _ =>
    match fromEventIdx? with
    | some idx => g.mkHistoricalGameAt idx
    | none => preLoopStart
  let mut g := g
  let mut others := others
  let mut found : Option ObjectId := none
  let mut movedAny := fromEventIdx?.isSome
  if let some fid := pendingFromId then
    if let some moved := g.followMovedToZone? fid (· == .exile) then
      g := g.logMsg s!"{(g.player victim).name} exiles {g.name moved} face up"
      if g.isInstantOrSorcery moved then
        found := some moved.id
      else
        others := others.push moved.id
  while found.isNone && g.stillInGame victim && !(g.player victim).library.isEmpty do
    let top := (g.player victim).library.back!
    let name := g.name (g.object! top)
    let (g', _) := g.move top .exile none (cause := cause) (deferPlayFromExileLogs := true)
    g := g'
    movedAny := true
    if g.sbaPaused then
      return g.chainPendingReplacement
        (.finishPostStep (.exileUntilInstantOrSorceryLoop victim controller castTheCard cause others (some top) (some loopFromIdx)))
    if let some moved := g.followMovedToZone? top (· == .exile) then
      g := g.logMsg s!"{(g.player victim).name} exiles {name} face up"
      if g.isInstantOrSorcery moved then
        found := some moved.id
      else
        others := others.push moved.id
  if movedAny then
    g := emitExpiredPlayFromExileLogsLazy mkPreLoop g loopFromIdx
  match found with
  | none =>
    if !g.stillInGame victim then return g
    else
      return g.requestOrderInto others (.library victim)
        s!"{(g.player victim).name} randomizes the exiled cards; they become that player's library"
        (cause := cause)
  | some instId =>
    if castTheCard then
      let (g', _) := g.move instId .stack (some controller)
        (verb := some .cast) (actor := some controller) (cause := cause)
      if let .chooseReplacement .. := g'.pending then
        return g'.chainPendingReplacement
          (.finishPostStep (.finishGrimaDirectCast controller victim instId others cause))
      return g'.finishGrimaDirectCast controller victim instId others cause
    else if !g.stillInGame victim then return g
    else
      let (g', _) := g.move instId (.library victim) none (cause := cause)
      return g'.requestOrderInto others (.library victim)
        s!"{(g'.player victim).name} puts the remaining exiled cards on the bottom of their library in a random order"
        (cause := cause)

/-- Exile cards from `victim`'s library until an instant or sorcery, face up.
An empty library becomes that player's library again. The found card may be
cast as this ability resolves, ignoring timing. Uncast cards go on the bottom
in a random order. -/
def grimaExileUntilInstantOrSorcery (g : Game) (controller victim : PlayerId)
    (castTheCard : Bool) : Game :=
  if !g.stillInGame victim then g
  else
    let (g, cause) := g.allocDelayedCause (some controller)
    g.exileUntilInstantOrSorceryLoop victim controller castTheCard
      (cause := some cause)

/-- True when `p` can pay Saruman's ward (discard an enchantment, instant,
or sorcery card). -/
def canPaySarumanWard (g : Game) (p : PlayerId) : Bool :=
  (g.player p).hand.any (fun id =>
    match g.findObject? id with
    | some o => isDiscardableCard o && (g.isEnchantment o || g.isInstantOrSorcery o)
    | none => false)

/-- Legendary artifacts and creatures `p` may sacrifice to Sauron's ward. -/
def legendaryWardSacrificeChoices (g : Game) (p : PlayerId) : Array GameObject :=
  (g.permanentsOf p).filter (fun o =>
    g.isLegendary o && (g.isCreature o || g.isArtifact o))

/-- Pause-safe loop moving the chosen Riddles pile to `p`'s hand before moving
the other pile to the graveyard, deferring `.playFromExile` expiry logs across
the batch (CR 616.1 / 704.3). -/
def applyRiddlesToHandLoop (g : Game) (p : PlayerId)
    (remainingHand toGy : Array ObjectId)
    (fromEventIdx? : Option Nat := none) : Game :=
  if remainingHand.isEmpty && fromEventIdx?.isNone then
    if toGy.isEmpty then g
    else if g.sbaPaused || (match g.pending with | .chooseReplacement .. => true | _ => false) then
      g.chainPendingReplacement (.finishPostStep (.applyRiddlesToHandLoop p #[] toGy none))
    else
      g.withBatch none fun g =>
        g.moveCardsToGraveyardLoop toGy
  else if g.sbaPaused || (match g.pending with | .chooseReplacement .. => true | _ => false) then
    g.chainPendingReplacement
      (.finishPostStep (.applyRiddlesToHandLoop p remainingHand toGy fromEventIdx?))
  else
    let runHand (g : Game) : Game × Bool := Id.run do
      let mut g := g
      let startIdx := fromEventIdx?.getD g.events.size
      for i in [0:remainingHand.size] do
        let id := remainingHand[i]!
        g := (g.move id (.hand p) none (deferPlayFromExileLogs := true)).1
        if g.sbaPaused || (match g.pending with | .chooseReplacement .. => true | _ => false) then
          let rem := remainingHand.extract (i + 1) remainingHand.size
          return (g.chainPendingReplacement
            (.finishPostStep (.applyRiddlesToHandLoop p rem #[] (some startIdx))), true)
      g := emitExpiredPlayFromExileLogsLazy (fun _ => g.mkHistoricalGameAt startIdx) g startIdx
      return (g, false)
    match fromEventIdx? with
    | some _ =>
      let (g1, paused) := runHand g
      if paused || toGy.isEmpty then g1
      else g1.withBatch none fun g => g.moveCardsToGraveyardLoop toGy
    | none =>
      let (g1, paused) := g.withBatchReturn none fun g => runHand g
      if toGy.isEmpty then g1
      else if paused then
        g1.chainPendingReplacement (.finishPostStep (.applyRiddlesToHandLoop p #[] toGy none))
      else
        g1.withBatch none fun g =>
          g.moveCardsToGraveyardLoop toGy

/-- Move each card in `ids` sequentially into `.exile`, deferring `.playFromExile`
expiry logs across the batch and pausing via `PostStep.exileCardsLoop` on
`Pending.chooseReplacement` / `sbaPaused` (CR 616.1 / 704.3). -/
def exileCardsLoop (g : Game) (ids : Array ObjectId)
    (cause : Option EventCause := none)
    (fromEventIdx? : Option Nat := none) : Game :=
  if ids.isEmpty && fromEventIdx?.isNone then g
  else if g.sbaPaused || (match g.pending with | .chooseReplacement .. => true | _ => false) then
    g.chainPendingReplacement (.finishPostStep (.exileCardsLoop ids cause fromEventIdx?))
  else
    Id.run do
      let loopFromIdx := fromEventIdx?.getD g.events.size
      let mut g := g
      for i in [0:ids.size] do
        let id := ids[i]!
        if g.findObject? id |>.isSome then
          g := (g.move id .exile none (cause := cause)
            (deferPlayFromExileLogs := true)).1
          if g.sbaPaused || (match g.pending with | .chooseReplacement .. => true | _ => false) then
            let rem := ids.extract (i + 1) ids.size
            g := g.chainPendingReplacement
              (.finishPostStep (.exileCardsLoop rem cause (some loopFromIdx)))
            return g
      return emitExpiredPlayFromExileLogsLazy (fun _ => g.mkHistoricalGameAt loopFromIdx) g loopFromIdx

/-- Put one Riddles pile into `p`'s hand and the other into the graveyard.
The face-down pile is not revealed when it is the one that goes to hand. -/
def applyRiddlesPiles (g : Game) (p : PlayerId) (faceUp faceDown : Array ObjectId)
    (chooseFaceDown : Bool) (alreadyRevealed : Bool := false) : Game :=
  let g := g.logMsg
    s!"{(g.player p).name} separates {faceUp.size} face-up and {faceDown.size} face-down"
  let g :=
    if !alreadyRevealed && !faceUp.isEmpty then
      let g := g.record (GameEvent.revealed g.turnNumber p faceUp
        (cause := some (g.resolvingOrRuleCause p)))
      faceUp.foldl (fun acc id =>
        match acc.findObject? id with
        | some o => acc.logMsg s!"{(acc.player p).name} reveals {acc.name o}"
        | none => acc) g
    else g
  let toHand := if chooseFaceDown then faceDown else faceUp
  let toGy := if chooseFaceDown then faceUp else faceDown
  let g :=
    if chooseFaceDown then
      g.logMsg "The face-down pile is put into hand without being revealed"
    else
      g.logMsg "The face-up pile is put into hand"
  let outerCont? := g.pendingReplacement
  let g := if outerCont?.isSome then g.change (.pendingReplacement none) else g
  let g := g.applyRiddlesToHandLoop p toHand toGy
  match outerCont? with
  | some outer => g.chainPendingReplacement outer
  | none => g

/-- Split the top four library cards into a face-up pile and a face-down pile.
A 4/0 split is legal. The face-down pile is not revealed if it is put into
hand. -/
def riddlesInTheDark (g : Game) (p : PlayerId) (faceUpCount : Nat)
    (chooseFaceDown : Bool) : Game :=
  if !g.stillInGame p then g
  else
    let lib := (g.player p).library
    let n := min 4 lib.size
    let taken := lib.extract (lib.size - n) lib.size
    let g :=
      if !taken.isEmpty then
        g.record (GameEvent.lookedAt g.turnNumber p taken (cause := some (g.resolvingOrRuleCause p)))
      else g
    let faceUpN := min faceUpCount taken.size
    let faceUp := taken.extract (taken.size - faceUpN) taken.size
    let faceDown := taken.extract 0 (taken.size - faceUpN)
    g.applyRiddlesPiles p faceUp faceDown chooseFaceDown

/-- Linked activated abilities last only while the copier still has them. -/
def linkedAbilitiesStillLinked (stillHasThoseAbilities : Bool) : Bool :=
  stillHasThoseAbilities

/-- Treat a copied activated ability as referring to the copier's name. -/
def rewriteAbilityCardName (abilityText printedName copierName : String) : String :=
  abilityText.replace printedName copierName

/-- Must-attack-if-able may be declined when every legal attack would cost. -/
def mustAttackCanDeclineIfOnlyAttackCosts (onlyAttacksRequireCost : Bool) : Bool :=
  onlyAttacksRequireCost

/-- Ares and similar “attacks each combat if able” statics (MSH 130 / CR 508.1d). -/
def hasAttacksIfAble (g : Game) (o : GameObject) : Bool :=
  let selfEnv : EvalEnv := { controller := (g.controllerOf o).getD o.owner, sourceId := some o.id }
  let selfMust :=
    (g.staticAbilities o).any fun ab =>
      ab.anyRule fun cond? r =>
        match r with
        | .combat (.attacksEachCombatIfAble .self) => cond?.all (EvalExpr.evalCondition g selfEnv)
        | _ => false
  selfMust ||
    g.battlefield.any fun src =>
      let env : EvalEnv := { controller := (g.controllerOf src).getD src.owner, sourceId := some src.id }
      (g.staticAbilities src).any fun ab =>
        ab.anyRule fun cond? r =>
          match r with
          | .combat (.attacksEachCombatIfAble (.matching sc)) =>
            cond?.all (EvalExpr.evalCondition g env) &&
              EvalExpr.evalObjectPred g env (.live o) sc.pred
          | _ => false

/-- Every legal attack target (player or planeswalker) charges a cost to be attacked. -/
def everyAttackCosts (g : Game) (o : GameObject) : Bool :=
  match g.controllerOf o with
  | none => false
  | some p =>
    let opps := g.livingOpponents p
    !opps.isEmpty && opps.all (fun pl =>
      g.attackTaxPerCreature pl.id > 0 &&
        !(g.permanentsOf pl.id).any (fun pw =>
          g.isPlaneswalker pw && !(g.cantAttackJace p pw)))

/-- Whether `o` has at least one legal attack target (an opponent player or
opponent-controlled planeswalker) that does not charge an attack cost
(CR 508.1b,c,d / 506.4c). -/
def hasCostFreeLegalAttackTarget (g : Game) (o : GameObject) : Bool :=
  match g.controllerOf o with
  | none => false
  | some p =>
    let opps := g.livingOpponents p
    let flyer := g.hasFlying o
    opps.any fun pl =>
      (g.attackTaxPerCreature pl.id == 0 && !(flyer && g.leftoverFlyingRestriction pl.id)) ||
        (g.permanentsOf pl.id).any (fun pw =>
          g.isPlaneswalker pw && !(g.cantAttackJace p pw))

/-- True when `o` must attack this combat. Summoning sickness, being tapped,
having no legal attack target, or an unpaid attack cost means it does not have
to attack (CR 508.1d / MSH 130). -/
def mustAttackIfAble (g : Game) (o : GameObject) (attackRequiresCost := false) : Bool :=
  (g.hasAttacksIfAble o || o.status.goaded) && g.canAttack o &&
    g.hasCostFreeLegalAttackTarget o &&
    !mustAttackCanDeclineIfOnlyAttackCosts (attackRequiresCost || g.everyAttackCosts o)

/-- Failed Adventure from Bilbo's graveyard ability is exiled by Bilbo, not
as an Adventure, so it cannot be cast as a permanent later. -/
def exileFailedAdventureFromBilbo (g : Game) (id : ObjectId) : Game :=
  match g.findObject? id with
  | none => g
  | some o =>
    let name := g.name o
    let (g, _) := g.move id .exile none
    g.logMsg s!"{name} is exiled (Bilbo's replacement). It cannot be cast as a permanent"

/-- Create `remaining` token copies of `template` under `controller` with haste
and end-step sacrifice (Venser) as a two-pass simultaneous entry batch inside
`withBatch` (CR 603.6a / 603.10), pausing on `Pending.chooseReplacement`
(`PendingReplacement.copyPermanentTokens`) if token creation or ETB choices
require interactive CR 616.1 selection. -/
partial def createPermanentCopyTokens (g : Game) (controller : PlayerId) (template : CardDef)
    (remaining : Nat) (cause : Option EventCause := none)
    (priorRecentCount : Option Nat := none) (pushedFrame : Bool := false) : Game :=
  if g.sbaPaused then
    let baseCount := priorRecentCount.getD g.recentTokenIds.size
    g.chainPendingReplacement
      (.copyPermanentTokens controller template remaining cause baseCount pushedFrame)
  else
    let baseCount := priorRecentCount.getD g.recentTokenIds.size
    let pushed := pushedFrame || (remaining > 0 && g.continuations.isEmpty)
    let g := if !pushedFrame && pushed then g.change (.pushContinuationFrame {}) else g
    let g := g.withBatch cause fun g => Id.run do
      let batchCause := cause.orElse (fun _ => g.currentBatch.bind (·.2))
      let mut g := g
      if remaining > 0 then
        let (g', _) := g.createToken controller template (recordRecent := true)
          (cause := batchCause) (count := remaining)
        g := g'
        if g.sbaPaused then
          return g.chainPendingReplacement
            (.copyPermanentTokens controller template 0 batchCause baseCount pushed)
      let allIds := g.recentTokenIds
      let ids := allIds.extract baseCount allIds.size
      if !g.continuations.isEmpty && allIds.size > baseCount then
        g := g.change (.recentTokenIds (allIds.extract 0 baseCount))
      let mut anyEntered := false
      for tid in ids do
        if let some tok := g.findObject? tid then
          if tok.isOnBattlefield then
            anyEntered := true
            g := g.afterPermanentEntersInBatch tok
            if let some tok := g.findObject? tid then
              if tok.isOnBattlefield then
                g := g.createEffect (.keywordsUntilEot tok.id #[Keyword.haste]) (cause := batchCause)
                g := g.registerDelayedTrigger {
                  controller
                  source := some tok
                  kind := .endStepSacrifice tok.id
                  cause := batchCause.getD (.oneShotEffect none none (some controller))
                }
      if anyEntered || remaining == 0 then
        g := g.logMsg "The token copies gain haste and are sacrificed at the next end step"
      if pushed && g.continuations.back? == some {} then
        g := g.change .popContinuationFrame
      return g
    if g.sbaPaused then g
    else if g.currentBatch.isNone then g.promptTriggerTargetsIfNeeded
    else g

/-- Whether the source of a proposed activated ability or face-up action can
still pay its source-bound costs (CR 602.2b / 606.3–606.4 / 702.37e / 734.1). -/
def sourceStillPayable (g : Game) (prop : ProposedSpell) : Bool :=
  match prop.sourceId with
  | none =>
    (prop.sneakAttacker.all fun aid =>
      g.sneakPaid prop.spellId ||
        (g.canCastForSneak prop.caster &&
          (g.findObject? aid).any (fun a =>
            a.isOnBattlefield && g.isCreature a && g.controlledBy a prop.caster &&
              a.status.attacking && !a.status.blocked))) &&
    (prop.beamMeUpCreature.all fun cid =>
      GameEvent.beamMeUpPaid g.events prop.spellId ||
        (g.findObject? cid).any (fun c =>
          c.isOnBattlefield && g.isCreature c && g.controlledBy c prop.caster &&
            !g.cantBeBeamedUp c))
  | some sid =>
    let exileSource := prop.activation.any (·.cost.exileSourceFromBattlefield)
    let sacrificeOrExileSource :=
      prop.sacrificeSource || exileSource || prop.activation.any (·.cost.sacrificeSource)
    let sinceIdx := (g.targetProposalCheckpoint?.map (·.eventsSize)).getD 0
    let fromGyAb := prop.activation.any (·.isFromGraveyard)
    let fromHandAb := prop.discardSource || prop.activation.any (·.isFromHand)
    let needsBfSource :=
      prop.tapSource || sacrificeOrExileSource || prop.removePlusOneX ||
        prop.activation.any (·.needsBattlefieldSource)
    if (fromGyAb && fromHandAb) || ((fromGyAb || fromHandAb) && needsBfSource) then
      false
    else
    let forObj := some prop.spellId
    let hasUnpaidBfSourceCost := g.proposedNeedsBattlefieldSource prop sinceIdx
    let alreadySacrificedForCost :=
      prop.kind == .activatedAbility &&
        !sacrificeOrExileSource && !prop.discardSource &&
        !fromGyAb && !fromHandAb &&
        (g.sourceSacrificedForCost sid forObj sinceIdx ||
          (!hasUnpaidBfSourceCost && g.sourceRemovedByCostSince prop.caster sid sinceIdx))
    let alreadyDiscardedFromHandForCost :=
      prop.kind == .activatedAbility &&
        !sacrificeOrExileSource && !prop.discardSource &&
        !fromGyAb && !needsBfSource &&
        prop.activation.any (·.isFromHand) &&
        !prop.activation.any (·.cost.exileSourceFromHand) &&
        g.sourceDiscardedFromHandForCost sid forObj sinceIdx
    match g.findObject? sid with
    | none => alreadySacrificedForCost || alreadyDiscardedFromHandForCost
    | some src =>
      if prop.kind == .turnFaceUp then
        src.isOnBattlefield && g.controlledBy src prop.caster && src.status.faceDown &&
          (g.unmaskedCopiableValues src).morph.isSome
      else if (!src.isOnBattlefield && alreadySacrificedForCost) ||
          (src.zone != .hand src.owner && alreadyDiscardedFromHandForCost) then
        true
      else
      let chosenX := ((g.findObject? prop.spellId).bind (·.chosenX)).getD 0
      let loyaltyPayable :=
        match prop.activation.bind (·.cost.netLoyaltyDelta chosenX) with
        | none => true
        | some k =>
          prop.loyaltyPaid ||
            g.sourceCounterCostPaidFor sid forObj .loyalty (some .loyalty) sinceIdx ||
            (src.isOnBattlefield && g.controlledBy src prop.caster &&
              !g.loyaltyActivatedThisTurn src.id &&
              (k ≥ 0 || (src.status.loyaltyCounters : Int) ≥ -k))
      let removePlusOneXPayable :=
        !prop.removePlusOneX ||
          g.sourceCounterCostPaidFor sid forObj .removeCounters (some .plusOnePlusOne) sinceIdx ||
          (src.isOnBattlefield && g.controlledBy src prop.caster &&
           src.status.plusOnePlusOne ≥ ((g.findObject? prop.spellId).bind (·.chosenX)).getD 0)
      let removeStoryPayable :=
        !prop.activation.any (·.cost.removeStoryCounter) ||
          g.sourceCounterCostPaidFor sid forObj .removeCounters (some .story) sinceIdx ||
          (src.isOnBattlefield && g.controlledBy src prop.caster && src.status.story > 0)
      let removeIndestructiblePayable :=
        !prop.activation.any (·.cost.removeIndestructibleCounter) ||
          g.sourceCounterCostPaidFor sid forObj .removeCounters (some .indestructible) sinceIdx ||
          (src.isOnBattlefield && g.controlledBy src prop.caster &&
           src.status.indestructibleCounters > 0)
      loyaltyPayable && removePlusOneXPayable &&
      removeStoryPayable && removeIndestructiblePayable &&
      (!prop.activation.any (·.cost.putStunCounterOnSource) ||
        g.sourceCounterCostPaidFor sid forObj .putCounters (some .stun) sinceIdx ||
        (src.isOnBattlefield && g.controlledBy src prop.caster)) &&
      (((src.isOnBattlefield && (g.controlledBy src prop.caster || alreadySacrificedForCost)) &&
        !fromGyAb && !fromHandAb &&
        (!prop.tapSource || !src.status.tapped || g.sourceTappedForCost sid forObj sinceIdx)) ||
      (fromGyAb && !fromHandAb && !needsBfSource &&
        isDiscardableCard src &&
        src.zone == .graveyard src.owner && src.owner == prop.caster) ||
      (fromHandAb && !fromGyAb && !needsBfSource &&
        isDiscardableCard src &&
        src.zone == .hand src.owner && src.owner == prop.caster))

/-- Offer `p` the optional explore choice to put the revealed top card `cardId`
of their library into their graveyard (CR 701.44a / 701.44c). -/
def offerExploreMayGraveyard (g : Game) (p : PlayerId) (cardId : ObjectId) : Game :=
  if !g.stillInGame p then g
  else if (g.player p).library.back? != some cardId then g
  else
    let cName := (g.findObject? cardId).map g.name |>.getD "the revealed card"
    g.beginResolutionChoice p (.exploreMayGraveyard cardId)
      s!"{(g.player p).name} may put {cName} into their graveyard"

end Game
end Mtg.Engine
