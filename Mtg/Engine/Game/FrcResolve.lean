import Mtg.Engine.Game.FraHelpers

/-!
# Reality Fracture Commander resolutions

`applyFrc` performs `Resolution.frc`. Choices that already exist
(library search, random order) stay on those pendings.
-/

namespace Mtg.Engine
namespace Game

private def spellX (g : Game) : Nat :=
  let chosen := fun (id? : Option ObjectId) => id?.bind g.chosenXOf?
  (chosen g.resolvingSpell).getD ((chosen g.resolvingAbility).getD 0)

private def frcCause? (g : Game) : Option GameObject :=
  g.resolvingAbilityObject?.bind fun ab =>
    ab.fraCauseId.bind fun id => (g.findObject? id).filter (·.isOnBattlefield)

private def frcGraveyardCause? (g : Game) : Option GameObject :=
  g.resolvingAbilityObject?.bind fun ab =>
    ab.fraCauseId.bind fun id =>
      g.followMovedToZone? id (fun | .graveyard _ => true | _ => false)

private def knownN (g : Game) (lastKnownPower : Option Int := none) : Nat :=
  ((lastKnownPower.orElse (fun _ => g.resolvingAbility.bind g.lastKnownPowerOf?)).getD 0).toNat

private def srcObj? (g : Game) (sourceId : Option ObjectId) : Option GameObject :=
  sourceId.bind fun id => (g.findObject? id).filter (·.isOnBattlefield)

private def exileId (g : Game) (id : ObjectId)
    (cause : Option EventCause := none) : Game :=
  match g.findObject? id with
  | none => g
  | some o =>
    let name := g.name o
    let (g, _) := g.move id .exile none (cause := cause)
    if let .chooseReplacement .. := g.pending then
      g.chainPendingReplacement (.finishPostStep (.logExiledIfInExile id s!"{name} is exiled"))
    else if (g.followMovedToZone? id (· == .exile)).isSome then
      g.logMsg s!"{name} is exiled"
    else g

private def handDiscard (g : Game) (p : PlayerId) : Game :=
  match (g.player p).hand.back? with
  | none => g.logMsg s!"{(g.player p).name} has no card to discard"
  | some id =>
    let card := g.object! id
    let destOwner := card.owner
    let name := card.name
    let (g, _) := g.move id (.graveyard destOwner) none (verb := some .discard) (actor := some p)
    if let .chooseReplacement .. := g.pending then
      g.chainPendingReplacement (.finishFrcPostStep (.logHandDiscard p id destOwner name))
    else if (g.followMovedToZone? id (· == .graveyard destOwner)).isSome then
      g.logMsg s!"{(g.player p).name} discards {name}"
    else g

private def destroyIds (g : Game) (ids : Array ObjectId) (pred : GameObject → Bool := fun _ => true) : Game :=
  let preBf := g.battlefield
  let validIds := ids.filter fun id =>
    match g.findObject? id with
    | some o => o.isOnBattlefield && pred o
    | none => false
  g.withBatch none fun g =>
    g.destroyPermanentsLoop validIds (preBattlefield := some preBf)

private def creatureTokenOf (name : String) (subtypes : Array CardSubtype) (p t : Int)
    (color : Option Color := none) (keywords : Keywords := Keywords.none)
    (types : Array CardType := #[.creature]) (toxic : Nat := 0) (cantBlock : Bool := false) : CardDef :=
  { creatureToken name subtypes p t color keywords types with toxic, cantBlock }

private def frcPrinted (k : FrcToken) (x : Nat) : CardDef :=
  match k with
  | .citizen =>
    { creatureTokenOf "Citizen" #[.citizen] 1 1 with
      colorIndicator := some (ColorSet.ofList [.green, .white]) }
  | .warrior => creatureTokenOf "Warrior" #[.warrior] 1 1 (some .white)
  | .insect => creatureTokenOf "Insect" #[.insect] 2 1 (some .white) Keyword.flying
  | .myr =>
    creatureTokenOf "Myr" #[.myr] 1 1 (types := #[.artifact, .creature])
  | .kobold =>
    { creatureTokenOf "Kobolds of Kher Keep" #[.kobold] 0 1 (some .red) with name := "Kobolds of Kher Keep" }
  | .mite =>
    creatureTokenOf "Phyrexian Mite" #[.phyrexian, .mite] 1 1
      (types := #[.artifact, .creature]) (toxic := 1) (cantBlock := true)
  | .shark =>
    creatureTokenOf "Shark" #[.shark] (Int.ofNat x) (Int.ofNat x) (some .blue) Keyword.flying
  | .gingerbrute =>
    { creatureTokenOf "Gingerbrute" #[.food, .golem] 1 1
        (keywords := Keyword.haste) (types := #[.artifact, .creature]) with
      activatedAbilities := #[
        { effect := { resolution := .frc .gingerDash, phrase := "This token can't be blocked this turn except by creatures with haste." }
          cost := { mana := ManaCost.ofGeneric 1 } },
        { effect := Effect.gainLife 3
          cost := { mana := ManaCost.ofGeneric 2, tap := true, sacrificeSource := true } } ] }
  | .angel => creatureTokenOf "Angel" #[.angel] 4 4 (some .white) Keyword.flying
  | .human => creatureTokenOf "Human" #[.human] 1 1 (some .white)
  | .goblin => creatureTokenOf "Goblin" #[.goblin] 1 1 (some .red)
  | .map => {
      name := "Map"
      types := #[.artifact]
      isToken := true
      activatedAbilities := #[
        { effect := { resolution := .frc .explore, phrase := "You explore." }
          cost := { mana := ManaCost.ofGeneric 1, tap := true, sacrificeSource := true } } ] }
  | .treasure => treasureToken
  | .rogue => creatureTokenOf "Rogue" #[.rogue] 2 2 (some .black)
  | .incubator => {
      name := "Incubator"
      types := #[.artifact]
      subtypes := #["Incubator"]
      isToken := true
      otherFace := some {
        creatureTokenOf "Phyrexian" #[.phyrexian] 0 0 (types := #[.artifact, .creature]) with
        name := "Phyrexian" }
      activatedAbilities := #[
        { effect := { resolution := .frc .transformIncubator, phrase := "Transform this token." }
          cost := { mana := ManaCost.ofGeneric 2 } } ] }

def makeFrcLoop (g : Game) (p : PlayerId) (k : FrcToken) (remaining : Nat) (x : Nat)
    (extraCounters : CounterBag) (cause : Option EventCause) : Game :=
  if remaining == 0 then g
  else if let .chooseReplacement .. := g.pending then
    g.chainPendingReplacement (.makeFrcLoop p k remaining x extraCounters cause)
  else
    let printed := frcPrinted k x
    (g.createToken p printed (extraCounters := extraCounters)
      (recordRecent := true) (cause := cause) (count := remaining)).1

private def makeFrc (g : Game) (p : PlayerId) (k : FrcToken) (n : Nat := 1) (x : Nat := 0)
    (extraCounters : CounterBag := #[]) (cause : Option EventCause := none) : Game :=
  if let .chooseReplacement .. := g.pending then
    if n == 0 || !g.stillInGame p then g
    else g.chainPendingReplacement (.makeFrcLoop p k n x extraCounters cause)
  else if n == 0 || !g.stillInGame p then g.change (.recentTokenIds #[])
  else
    let g := g.change (.recentTokenIds #[])
    let batchCause := cause.orElse (fun _ => g.resolvingBatchCause p none)
    g.withBatch batchCause fun g =>
      g.makeFrcLoop p k n x extraCounters cause

private def revealUntil (g : Game) (p : PlayerId) (pred : CardDef → Bool) (limit : Nat)
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
      if pred (g.baseCard card) then hits := hits.push cid
      else rest := rest.push cid
    if !shown.isEmpty then
      g := g.record (GameEvent.revealed g.turnNumber p shown
        (cause := some (cause.getD (g.resolvingOrRuleCause p))))
    return (g, hits, rest)

private def putHits (g : Game) (p : PlayerId) (hits : Array ObjectId) (haste := false)
    (cause : Option EventCause := none) : Game :=
  g.withBatch cause fun g =>
    g.putToBattlefieldLoop p hits (haste := haste) (cause := cause)

private def restBottom (g : Game) (p : PlayerId) (rest : Array ObjectId) (shuffle : Bool)
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
  g.restBottom p rest shuffle (cause := cause)

private def handDiscardToBottomOf (g : Game) (controller : PlayerId) : Game :=
  match (g.player controller).hand.back? with
  | none => g
  | some id =>
    let card := g.object! id
    let destOwner := card.owner
    let name := card.name
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
    | none => pure ()
  if cnt > 0 || (remainingIds.isEmpty && pendingId.isNone && movedCount == 0) then
    g := g.logMsg s!"{(g.player p).name} puts {cnt} card(s) on top of their library"
  return g

private def historicCard (c : CardDef) : Bool :=
  c.isPermanentCard && (c.isArtifact || c.hasSupertype .legendary || c.hasSubtype .saga)

private def creatureOrWalker (c : CardDef) : Bool :=
  c.isCreature || c.isPlaneswalker

private def basicOf (kinds : Array CardSubtype) (c : CardDef) : Bool :=
  isBasicLandCard c && kinds.any fun k => c.hasSubtype k

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
`Fact or Fiction` graveyard batch, logging only once each zone change places the
card into `controller`'s graveyard. -/
partial def factOrFictionGyInnerLoop (g : Game) (controller : PlayerId)
    (gyIds : Array ObjectId) (pendingCard : Option ObjectId := none) : Game := Id.run do
  if let .chooseReplacement .. := g.pending then
    return g.chainPendingReplacement
      (.finishFrcPostStep (.factOrFictionGyInnerLoop controller gyIds pendingCard))
  let plName := (g.player controller).name
  let mut g := g
  if let some fromId := pendingCard then
    if let some moved := g.followMovedToZone? fromId (· == .graveyard controller) then
      g := g.logMsg s!"{moved.name} goes to {plName}'s graveyard"
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
        g := g.logMsg s!"{moved.name} goes to {plName}'s graveyard"
  return g

/-- Move `gyIds` to `controller`'s graveyard in one batch, pausing cleanly if any
zone move opens `Pending.chooseReplacement` (`Fact or Fiction`). -/
partial def factOrFictionGyLoop (g : Game) (controller : PlayerId)
    (gyIds : Array ObjectId) : Game :=
  if gyIds.isEmpty then g
  else
    g.withBatch none fun g =>
      g.factOrFictionGyInnerLoop controller gyIds

/-- Move each card in `handIds` into `controller`'s hand inside the active
`Fact or Fiction` hand batch, logging only once each zone change places the card
into `controller`'s hand. -/
partial def factOrFictionHandInnerLoop (g : Game) (controller : PlayerId)
    (handIds : Array ObjectId) (pendingCard : Option ObjectId := none) : Game := Id.run do
  if let .chooseReplacement .. := g.pending then
    return g.chainPendingReplacement
      (.finishFrcPostStep (.factOrFictionHandInnerLoop controller handIds pendingCard))
  let plName := (g.player controller).name
  let mut g := g
  if let some fromId := pendingCard then
    if let some moved := g.followMovedToZone? fromId (· == .hand controller) then
      g := g.logMsg s!"{moved.name} goes to {plName}'s hand"
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
        g := g.logMsg s!"{moved.name} goes to {plName}'s hand"
  return g

partial def factOrFictionHandLoop (g : Game) (controller : PlayerId)
    (handIds gyIds : Array ObjectId) : Game :=
  let g :=
    if handIds.isEmpty then g
    else
      g.withBatch none fun g =>
        g.factOrFictionHandInnerLoop controller handIds
  if let .chooseReplacement .. := g.pending then
    if gyIds.isEmpty then g
    else g.chainPendingReplacement (.finishFrcPostStep (.factOrFictionGyLoop controller gyIds))
  else
    g.factOrFictionGyLoop controller gyIds

/-- Tap each creature in `ids` still on the battlefield and put a stun counter
on it inside the enclosing batch, deferring the stun-counter log across
`Pending.chooseReplacement` (`Tamiyo, Upriser Crowned`). -/
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

def applyFrc (g : Game) (controller : PlayerId) (effect : Effect) (e : FrcEffect)
    (targets : Array Target) (sourceId : Option ObjectId)
    (lastKnownPower : Option Int := none) : Game :=
  let pl := g.player controller
  let nKnown := g.knownN lastKnownPower
  match e with
  | .drawPutOnTop drawN putN =>
    let g := g.draw controller drawN
    if let .chooseReplacement .. := g.pending then
      g.chainPendingReplacement (.finishFrcPostStep (.putDrawnBackOnTop controller putN))
    else
      let hand := (g.player controller).hand
      let n := min putN hand.size
      let back := hand.extract (hand.size - n) hand.size
      g.withBatch none fun g =>
        g.putBackOnTopLoop controller back
  | .exileTarget =>
    match targets[0]? with
    | some (Target.permanent id) => g.exileId id
    | some (Target.card id) => g.exileId id
    | _ => g.logMsg "Despark has no legal target"
  | .pathToExile =>
    match targets[0]? with
    | some (Target.permanent id) =>
      match g.findObject? id with
      | some o =>
        let owner := (g.controllerOf o).getD o.owner
        let g := g.exileId id
        if let .chooseReplacement .. := g.pending then
          g.chainPendingReplacement (.finishFrcPostStep (.offerMaySearchBasics owner))
        else
          g.offerMaySearchBasics owner
      | none => g
    | _ => g
  | .swords =>
    match targets[0]? with
    | some (Target.permanent id) =>
      match g.findObject? id with
      | some o =>
        let owner := (g.controllerOf o).getD o.owner
        let pw := (g.snapshotPower o).toNat
        let g := g.exileId id
        if let .chooseReplacement .. := g.pending then
          g.chainPendingReplacement (.finishFrcPostStep (.swordsGainLife id owner pw))
        else
          g.gainLife owner pw
      | none => g
    | _ => g
  | .stroke =>
    match targets[0]? with
    | some (Target.permanent id) =>
      match g.findObject? id with
      | some o =>
        let owner := (g.controllerOf o).getD o.owner
        let g := g.destroyPermanent o
        if let .chooseReplacement .. := g.pending then
          g.chainPendingReplacement (.finishFrcPostStep (.makeHumanToken owner))
        else
          g.makeFrc owner .human
      | none => g
    | _ => g
  | .grandCrescendo =>
    let g := g.makeFrc controller .citizen (g.spellX)
    if let .chooseReplacement .. := g.pending then
      g.chainPendingReplacement (.finishFrcPostStep (.grantControlledCreaturesIndestructible controller))
    else
      g.grantUntilEotToControlledCreatures controller Keyword.indestructible "indestructible"
  | .martialCoup =>
    let x := g.spellX
    let g := g.createKindTokens controller .soldier11white x
    if let .chooseReplacement .. := g.pending then
      if x >= 5 then
        g.chainPendingReplacement (.finishFrcPostStep (.destroyNonRecentCreaturesAtFive x))
      else g
    else if x >= 5 then
      g.destroyIds (g.battlefield.filter (g.isCreature ·) |>.map (·.id))
        (fun o => !g.recentTokenIds.contains o.id)
    else g
  | .whiteSuns =>
    let x := g.spellX
    let g := g.gainLife controller x
    if let .chooseReplacement .. := g.pending then
      g.chainPendingReplacement (.finishFrcPostStep (.makeMitesThenDestroyAtFive controller x))
    else
      let g := g.makeFrc controller .mite x
      if let .chooseReplacement .. := g.pending then
        if x >= 5 then
          g.chainPendingReplacement (.finishFrcPostStep (.destroyNonRecentCreaturesAtFive x))
        else g
      else if x >= 5 then
        g.destroyIds (g.battlefield.filter (g.isCreature ·) |>.map (·.id))
          (fun o => !g.recentTokenIds.contains o.id)
      else g
  | .occult =>
    let x := g.spellX
    let g := g.draw controller x
    if let .chooseReplacement .. := g.pending then
      g.chainPendingReplacement (.finishFrcPostStep (.discardBackHandThenCreateSpirits controller x))
    else
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
  | .sunfall =>
    let startIdx := g.events.size
    let ids := (g.battlefield.filter (g.isCreature ·)).map (·.id)
    let (g, exileCause) := g.allocDelayedCause (some controller) sourceId
    let g := g.withBatch (some exileCause) fun g =>
      g.exilePermanentsLoop ids (logExile := true) (cause := some exileCause)
    let (g, incubateCause) := g.allocDelayedCause (some controller) sourceId
    if let .chooseReplacement .. := g.pending then
      g.chainPendingReplacement
        (.finishFrcPostStep (.incubateForExiledCount controller startIdx ids (some incubateCause)))
    else
      let count := ids.foldl (fun acc id =>
        if g.wasPermanentExiled id startIdx then acc + 1 else acc) 0
      let extra : CounterBag :=
        if count > 0 then #[(.plusOnePlusOne, count)] else #[]
      g.withBatch (some incubateCause) fun g =>
        g.makeFrc controller .incubator 1 0
          (extraCounters := extra) (cause := some incubateCause)
  | .massPolymorph =>
    let startIdx := g.events.size
    let yours := (g.permanentsOf controller).filter (g.isCreature ·) |>.map (·.id)
    let (g, exileCause) := g.allocDelayedCause (some controller) sourceId
    let g := g.withBatch (some exileCause) fun g =>
      g.exilePermanentsLoop yours (logExile := true) (cause := some exileCause)
    if let .chooseReplacement .. := g.pending then
      g.chainPendingReplacement
        (.finishFrcPostStep (.polymorphRevealCreatures controller startIdx sourceId yours))
    else
      let count := yours.foldl (fun acc id =>
        if g.wasPermanentExiled id startIdx then acc + 1 else acc) 0
      let (g, revealCause) := g.allocDelayedCause (some controller) sourceId
      let (g, hits, rest) := g.revealUntil controller (·.isCreature) count (cause := some revealCause)
      let g := g.putHits controller hits (cause := some revealCause)
      if let .chooseReplacement .. := g.pending then
        g.chainPendingReplacement (.finishFrcRestBottom controller rest true (some revealCause))
      else
        g.restBottom controller rest true (cause := some revealCause)
  | .syntheticDestiny =>
    let startIdx := g.events.size
    let yours := (g.permanentsOf controller).filter (g.isCreature ·) |>.map (·.id)
    let (g, cause) := g.allocDelayedCause (some controller) sourceId
    let src := sourceId.bind g.findObject?
    let g := g.withBatch (some cause) fun g =>
      g.exilePermanentsLoop yours (logExile := true) (cause := some cause)
    if let .chooseReplacement .. := g.pending then
      g.chainPendingReplacement
        (.finishFrcPostStep (.registerSyntheticDestinyEndStep controller startIdx sourceId yours (some cause)))
    else
      let count := yours.foldl (fun acc id =>
        if g.wasPermanentExiled id startIdx then acc + 1 else acc) 0
      g.registerDelayedTrigger { controller, source := src, kind := .endStepSynthetic count, cause }
        |>.logMsg "Those creatures return as revealed cards at the next end step"
  | .searchBasics kinds untapAt =>
    let g := if untapAt == 0 then g else g.change (.untapSearchedIfLands (some untapAt))
    g.beginLibrarySearch controller (basicOf kinds) "a basic land card" (.battlefield true)
  | .proteus =>
    match targets[0]? with
    | some (Target.permanent id) =>
      match g.findObject? id with
      | some o =>
        let owner := (g.controllerOf o).getD o.owner
        let (g, putCause) := g.allocDelayedCause (some controller) sourceId
        let g := g.moveIdsInOrder #[id] (.library owner) (cause := some putCause)
        if let .chooseReplacement .. := g.pending then
          g.chainPendingReplacement
            (.finishFrcPostStep (.polymorphSingleTargetReveal owner controller sourceId))
        else
          let (g, revealCause) := g.allocDelayedCause (some controller) sourceId
          let (g, hits, rest) := g.revealUntil owner (·.isCreature) 1 (cause := some revealCause)
          let g := g.putHits owner hits (cause := some revealCause)
          if let .chooseReplacement .. := g.pending then
            g.chainPendingReplacement (.finishFrcRestBottom owner rest false (some revealCause))
          else
            g.restBottom owner rest false (cause := some revealCause)
      | none => g
    | _ => g
  | .animate p t flying first =>
    match g.srcObj? sourceId with
    | none => g
    | some o =>
      let kws :=
        Keywords.merge (if flying then Keyword.flying else Keywords.none)
          (if first then Keywords.none else Keywords.none)
      let g := g.setUntilEotForm o (Int.ofNat p, Int.ofNat t) kws
        s!"{g.name o} becomes a {p}/{t} until end of turn"
        (additionalCreature := true)
      if first then g.createEffect (.firstStrikeOnYourTurn o.id)
      else g
  | .mapToken => g.makeFrc controller .map
  | .archon =>
    match targets[0]? with
    | some (Target.player pid) =>
      let victim :=
        ((g.permanentsOf pid).find? (g.isCreature ·)).orElse
          (fun _ => (g.permanentsOf pid).find? (g.isPlaneswalker ·))
      let g :=
        match victim with
        | some o => g.sacrificeToGraveyard o s!"{(g.player pid).name} sacrifices {g.name o}"
        | none => g.logMsg s!"{(g.player pid).name} has no creature or planeswalker to sacrifice"
      if let .chooseReplacement .. := g.pending then
        g.chainPendingReplacement (.finishFrcPostStep (.discardHandThenDrainAndDraw pid controller))
      else
        let g := g.handDiscard pid
        if let .chooseReplacement .. := g.pending then
          g.chainPendingReplacement (.finishFrcPostStep (.loseThreeDrawOneGainThree pid controller))
        else
          let g := g.loseLife pid 3
          let g := g.draw controller 1
          g.gainLife controller 3
    | _ => g
  | .avacyn =>
    match g.frcGraveyardCause? with
    | some o =>
      if o.zone == .graveyard o.owner then
        let (g, cause) := g.allocDelayedCause (some controller) sourceId
        let src := (sourceId.bind g.findObject?).orElse (fun _ => some o)
        g.registerDelayedTrigger { controller, source := src, kind := .endStepGraveReturn o.id controller, cause }
          |>.logMsg s!"{g.name o} returns at the beginning of the next end step"
      else g
    | none => g
  | .dack =>
    let n := (g.livingOpponents controller).size
    let (g, cause) := g.allocDelayedCause (some controller) sourceId
    let (g, hits, rest) := g.revealUntil controller (·.isCreature) n (cause := some cause)
    let g := g.putHits controller hits (cause := some cause)
    if let .chooseReplacement .. := g.pending then
      g.chainPendingReplacement (.finishFrcRestBottom controller rest true (some cause) hits)
    else
      let g := g.applyDackOnHits controller hits cause
      g.restBottom controller rest true (cause := some cause)
  | .jhoira =>
    match targets[0]? with
    | some (Target.player pid) =>
      let (g, cause) := g.allocDelayedCause (some controller) sourceId
      let (g, hits, rest) := g.revealUntil pid historicCard 1 (cause := some cause)
      match hits[0]? with
      | some id =>
        match g.findObject? id with
        | some card =>
          let mv := g.objectManaValue card
          let g := g.putHits controller #[id] (cause := some cause)
          if let .chooseReplacement .. := g.pending then
            let g := g.chainPendingReplacement (.loseLifeAfterDraw controller mv (some cause))
            g.chainPendingReplacement (.finishFrcRestBottom pid rest false (some cause))
          else
            let g := g.loseLife controller mv (cause := some cause)
            g.restBottom pid rest false (cause := some cause)
        | none => g.restBottom pid rest false (cause := some cause)
      | none =>
        let g := g.logMsg s!"{(g.player pid).name} reveals no historic permanent"
        g.restBottom pid rest false (cause := some cause)
    | _ => g
  | .nissa =>
    let g := g.draw controller
    if let .chooseReplacement .. := g.pending then
      g.chainPendingReplacement (.finishFrcPostStep (.optionalOncePolymorphReveal controller sourceId))
    else
      match g.srcObj? sourceId with
      | some src =>
        if g.optionalOnceUsedThisTurn src.id then g
        else
          let (g, cause) := g.allocDelayedCause (some controller) sourceId
          let g := g.record (GameEvent.optionalOnceActed g.turnNumber controller src.id (cause := some cause))
          let (g, hits, rest) := g.revealUntil controller (·.isCreature) 1 (cause := some cause)
          let g := g.putHits controller hits (cause := some cause)
          if let .chooseReplacement .. := g.pending then
            g.chainPendingReplacement (.finishFrcRestBottom controller rest false (some cause))
          else
            g.restBottom controller rest false (cause := some cause)
      | none => g
  | .nivPay =>
    let n := nKnown
    if (g.player controller).life > Int.ofNat n && n > 0 then
      let before := (g.player controller).life
      let payCause : Option EventCause :=
        g.currentResolvingContext?.map fun (src, _) =>
          .costPayment .life controller
            (g.resolvingAbility.orElse (fun _ => sourceId.orElse (fun _ => src)))
      match g.payLifeCost controller n (cause := payCause) with
      | .ok g =>
        if (g.player controller).life < before then g.draw controller n else g
      | .error _ => g.logMsg s!"{pl.name} declines to pay {n} life"
    else g.logMsg s!"{pl.name} declines to pay {n} life"
  | .nivDrain =>
    g.eachOpponentLosesYouGain controller 1
  | .obEnter =>
    let preBf := g.battlefield
    let ids := preBf.filter (fun o =>
      g.isCreature o && o.status.tapped &&
        (g.controllerOf o).any (g.isLivingOpponentOf controller ·)) |>.map (·.id)
    g.withBatch none fun g =>
      g.destroyPermanentsLoop ids (obGainLifeFor := some controller) (preBattlefield := some preBf)
  | .obAngel =>
    if g.loggedLifeGained controller > 0 then g.makeFrc controller .angel
    else g
  | .omnathCc =>
    g.addMana controller .colorless 2 (source := sourceId)
      |>.logMsg (s!"{pl.name} adds " ++ "{C}{C}")
  | .elspethDestroy =>
    g.destroyIds (g.battlefield.filter (fun o => g.isCreature o && g.snapshotPower o >= 4) |>.map (·.id))
  | .elspethEmblem =>
    let (g, emb) := g.allocObject {
        name := "Elspeth emblem"
        types := #[.enchantment]
        grantTeamPlusTwoFlying := true
      } controller .command (some controller)
    g.logMsg s!"{pl.name} gets an emblem ({emb.name})"
  | .jacePlus =>
    let g := g.draw controller 2
    if let .chooseReplacement .. := g.pending then
      g.chainPendingReplacement (.finishFrcPostStep (.handDiscardToBottom controller))
    else
      g.handDiscardToBottomOf controller
  | .jaceMinus =>
    match targets[0]? with
    | some (Target.permanent id) =>
      let (g, exileCause) := g.allocDelayedCause (some controller) sourceId
      let g := g.exileId id (cause := some exileCause)
      if let .chooseReplacement .. := g.pending then
        g.chainPendingReplacement (.finishFrcPostStep (.revealCreatureOrPlaneswalker controller sourceId))
      else
        let (g, revealCause) := g.allocDelayedCause (some controller) sourceId
        let (g, hits, rest) := g.revealUntil controller creatureOrWalker 1 (cause := some revealCause)
        let g := g.putHits controller hits (cause := some revealCause)
        if let .chooseReplacement .. := g.pending then
          g.chainPendingReplacement (.finishFrcRestBottom controller rest false (some revealCause))
        else
          g.restBottom controller rest false (cause := some revealCause)
    | _ => g
  | .jaceTax =>
    if g.isOnActiveTeam controller || (g.player g.activePlayer).lost then g
    else
      let ap := g.activePlayer
      (g.changes #[
        .pending (.payOrLetCounter ap 2 none),
        .unlessPaysInstead (some { resolution := .frc .jaceTaxApply }),
        .unlessPaysController controller,
        .unlessPaysTargets #[.player ap],
        .unlessPaysSource sourceId,
        .unlessPaysDue false]).logMsg
        s!"{(g.player ap).name} may pay \{2} or their creatures can't attack Jaces {(g.player controller).name} controls this turn"
  | .jaceTaxApply =>
    match targets[0]? with
    | some (Target.player attacker) =>
      if (g.player attacker).lost then g
      else
        g.createEffect (.cantAttackJacesThisTurn attacker controller)
          |>.logMsg s!"{(g.player attacker).name}'s creatures can't attack Jaces {(g.player controller).name} controls this turn"
    | _ => g
  | .monarch =>
    let abObj? := g.resolvingAbilityObject?
    let heir :=
      ((abObj?.bind (·.fraCauseId)).bind g.followToBattlefield? |>.bind g.controllerOf).orElse
        (fun _ => abObj?.bind (·.fraCauseController))
        |>.getD controller
    if (g.player heir).lost || (g.player heir).leftTheGame || (g.player heir).isMonarch then g
    else
      let prev := (g.players.find? (·.isMonarch)).map (·.id)
      g.record (GameEvent.becameMonarch g.turnNumber heir prev
        (cause := some (g.resolvingOrRuleCause controller sourceId)))
        |>.logMsg s!"{(g.player heir).name} becomes the monarch"
  | .gingerbrute =>
    if (g.player controller).isMonarch then g.makeFrc controller .gingerbrute
    else g
  | .tamiyoStun =>
    let abIds := (g.resolvingAbilityObject?.map (·.fraCauseIds)).getD #[]
    let ids :=
      if !abIds.isEmpty then abIds
      else (g.frcCause?.map (fun o => #[o.id])).getD #[]
    g.withBatch none fun g =>
      g.tamiyoStunLoop controller ids
  | .teferi =>
    match targets[0]? with
    | some (Target.player pid) =>
      let g := g.createEffects
        #[.protectionFromEverything pid, .lifeCantChange pid]
      let g := g.logMsg s!"{(g.player pid).name} has protection from everything and their life total can't change"
      let targetsToPhase := (g.permanentsOf pid).filter (fun o => !g.isLand o)
      let phaseCause := g.resolvingOneShotCause controller sourceId
      let g := g.phaseOutPermanents targetsToPhase (cause := phaseCause)
      match g.resolvingSpell.bind g.findObject? with
      | some spell =>
        g.createEffect (.exileInstantSorceryInstead spell.id)
          |>.logMsg s!"{g.name spell} will be exiled"
      | none => g
    | _ => g
  | .urSphinx =>
    let n := nKnown
    let players := g.apnapPlayers
    let buckets := players.map fun pid =>
      let lib := (g.player pid).library
      let count := min n lib.size
      (lib.extract (lib.size - count) lib.size).reverse
    let g := g.withBatch none fun g =>
      players.foldl (fun g pid => g.mill pid n) g
    if let .chooseReplacement .. := g.pending then
      g.chainPendingReplacement
        (.finishFrcPostStep (.urSphinxCastNext controller buckets))
    else
      g.urSphinxCastNext controller buckets
  | .venserSpell =>
    match targets[0]? with
    | some t@(Target.card id) =>
      if !g.targetLegalAt controller effect.targetKind 0 t sourceId then
        g.illegalAbilityTarget t
      else
        match g.findObject? id with
        | some spell =>
          if spell.zone != .stack then
            g.illegalAbilityTarget t
          else
            let (g, cause) := g.allocDelayedCause (some controller) sourceId
            let (g, c1) := g.copyStackSpellWithId spell controller (some cause)
            let (g, c2) := g.copyStackSpellWithId spell controller (some cause)
            let copies := #[c1, c2].filterMap (·)
            let targeted := copies.any (fun cid => ((g.stackEntry? cid).map (!·.targets.isEmpty)).getD false)
            if copies.isEmpty || !targeted then g
            else
              g.beginFraChoice controller (.newTargetsForCopies copies)
                s!"{(g.player controller).name} may choose new targets for the copies"
        | none => g.illegalAbilityTarget t
    | _ => g
  | .venserPerm =>
    match targets[0]? with
    | some t@(Target.permanent id) =>
      let legal :=
        if effect.targetKind != .none then
          g.targetLegalAt controller effect.targetKind 0 t sourceId
        else
          (g.findObject? id).any (fun o =>
            o.isOnBattlefield && g.canBeTargetedBy controller o sourceId)
      if !legal then
        g.illegalAbilityTarget t
      else
        match g.findObject? id with
        | some src =>
          let template := g.copiableValues src
          let (g, cause) := g.allocDelayedCause (some controller) sourceId
          g.withBatch (some cause) fun g =>
            g.createPermanentCopyTokens controller template 2 (cause := some cause)
        | none => g.illegalAbilityTarget t
    | _ => g
  | .goblin =>
    let jeskai :=
      match g.srcObj? sourceId with
      | some src => src.status.chosenAnchor == some "Jeskai"
      | none => (sourceId.bind g.lastKnownBefore?).any (·.chosenAnchor == some "Jeskai")
    if !jeskai then g
    else
      let g := g.makeFrc controller .goblin
      if let .chooseReplacement .. := g.pending then
        g.chainPendingReplacement (.finishFrcPostStep .grantRecentTokensLifelinkHaste)
      else
        g.withBatch none fun g =>
          g.recentTokenIds.foldl (fun g tid =>
            match g.findObject? tid with
            | some tok =>
              if tok.isOnBattlefield then
                g.createEffect (.keywordsUntilEot tok.id (Keywords.merge Keyword.lifelink Keyword.haste))
                  |>.logMsg s!"{g.name tok} gains lifelink and haste until end of turn"
              else g
            | none => g) g
  | .spirit => g.createKindTokens controller .spirit 1
  | .story =>
    match g.srcObj? sourceId with
    | some o =>
      g.putCountersDeferredLog o.id .story 1 (some controller) .gets
    | none => g
  | .currencyExile =>
    match g.frcGraveyardCause? with
    | some card =>
      if card.zone == .graveyard card.owner then
        match g.srcObj? sourceId with
        | some src => g.exileSearchedLinked controller card.id (some src.id)
        | none => g.exileId card.id
      else g
    | none => g
  | .currencyLoot =>
    let g := g.draw controller
    if let .chooseReplacement .. := g.pending then
      g.chainPendingReplacement (.finishFrcPostStep (.discardHand controller))
    else
      g.handDiscard controller
  | .currencyReturn =>
    match sourceId with
    | none => g
    | some sid =>
      let allIds := g.allLinkedExilesOf sid
      match allIds.find? (fun id => (g.findObject? id).any (·.zone == .exile)) with
      | none =>
        match g.srcObj? sourceId with
        | some src => g.logMsg s!"{g.name src} has no exiled card"
        | none => g
      | some id =>
        match g.findObject? id with
        | none => g
        | some card =>
          let land := g.isLand card
          let (g, _) := g.move id (.graveyard card.owner) none
          if let .chooseReplacement .. := g.pending then
            g.chainPendingReplacement
              (.finishFrcPostStep (.currencyReturnCreateToken controller id sid land))
          else if (g.followMovedToZone? id (· != .exile)).isSome then
            let g := g.pruneLinkedExileId sid id
            if land then g.makeFrc controller .treasure else g.makeFrc controller .rogue
          else g
  | .despair =>
    g.withBatch (g.resolvingBatchCause controller sourceId) fun g =>
      g.forEachOpponent controller fun g pid =>
        g.loseLife pid (g.loggedLifeLost pid)
  | .dreadUpkeep =>
    let (g, cause?) : Game × Option EventCause :=
      match g.currentResolvingContext? with
      | some (src, ctrl) =>
        let (g, c) := g.allocDelayedCause (ctrl.orElse (fun _ => some controller)) (src.orElse (fun _ => sourceId))
        (g, some c)
      | none => (g, none)
    (g.loseLife controller 1 (cause := cause?)).amassZombies controller 1 (cause := cause?)
  | .dreadLink =>
    match g.frcCause? with
    | some o =>
      if o.isOnBattlefield then g.grantUntilEotLogged o Keyword.lifelink else g
    | none => g
  | .myr n => g.makeFrc controller .myr n
  | .drawPerArtifact =>
    let n := (g.permanentsOf controller).filter (g.isArtifact ·) |>.size
    g.draw controller n
  | .sharkCast =>
    let x :=
      match g.resolvingAbilityObject?.bind (·.fraCauseId) with
      | some id =>
        match (g.findObject? id).filter (·.zone == .stack) with
        | some spell => g.objectManaValue spell (includeLkiX := true)
        | none =>
          match g.lastKnownBefore? id with
          | some eo => eo.manaValue
          | none => 0
      | none => 0
    g.makeFrc controller .shark 1 x
  | .sharkCycle =>
    g.makeFrc controller .shark 1 nKnown
  | .skrelv =>
    let (g, cause?) : Game × Option EventCause :=
      match g.currentResolvingContext? with
      | some (src, ctrl) =>
        let (g, c) := g.allocDelayedCause (ctrl.orElse (fun _ => some controller)) (src.orElse (fun _ => sourceId))
        (g, some c)
      | none => (g, none)
    (g.loseLife controller 1 (cause := cause?)).makeFrc controller .mite (cause := cause?)
  | .insects => g.makeFrc controller .insect 2
  | .factOrFiction =>
    let lib := (g.player controller).library
    let n := min 5 lib.size
    let shown := (List.range n).foldl (fun acc i => acc.push lib[lib.size - 1 - i]!) #[]
    let revealCause := some (g.resolvingOrRuleCause controller sourceId)
    let g :=
      if shown.isEmpty then g
      else g.record (GameEvent.revealed g.turnNumber controller shown (cause := revealCause))
    let handN := (shown.size + 1) / 2
    let toHand := shown.extract 0 handN
    let toGy := shown.extract handN shown.size
    g.factOrFictionHandLoop controller toHand toGy
  | .pump n =>
    match g.srcObj? sourceId with
    | some o => g.pumpPermanent o n 0
    | none => g
  | .kobold => g.makeFrc controller .kobold
  | .warriorsX => g.makeFrc controller .warrior (g.spellX)
  | .citizensX => g.makeFrc controller .citizen (g.spellX)
  | .explore =>
    let lib := (g.player controller).library
    if lib.isEmpty then g.logMsg s!"{pl.name} explores (empty library)"
    else
      let top := lib.back!
      let card := g.object! top
      let g := g.record (GameEvent.revealed g.turnNumber controller #[top]
        (cause := some (g.resolvingOrRuleCause controller sourceId)))
      if g.isLand card then
        let cName := card.name
        let (g, _) := g.move top (.hand controller) none
        if let .chooseReplacement .. := g.pending then
          g.chainPendingReplacement
            (.finishFrcPostStep (.logExploreLandToHand controller top cName))
        else if (g.followMovedToZone? top (· == .hand controller)).isSome then
          g.logMsg s!"{pl.name} explores and puts {cName} into their hand"
        else g
      else
        let g := g.logMsg s!"{pl.name} puts {card.name} on top of their library"
        match g.srcObj? sourceId with
        | some o =>
          if g.isCreature o then
            (g.logMsg s!"{pl.name} explores").addPlusOnePlusOneTo o 1 (byPlayer := some controller)
          else g.logMsg s!"{pl.name} explores and leaves {card.name} on top"
        | none => g.logMsg s!"{pl.name} explores and leaves {card.name} on top"
  | .transformIncubator =>
    match g.srcObj? sourceId with
    | some o =>
      let counters := o.status.plusOnePlusOne
      let oName := g.name o
      let (g, transformCause) : Game × EventCause :=
        match g.currentResolvingContext? with
        | some (s, c) =>
          g.allocDelayedCause (c.orElse (fun _ => some controller)) (s.orElse (fun _ => some o.id))
        | none => (g, .gameRule .spellCast)
      let g := g.record
        (GameEvent.transformed g.turnNumber (g.snapshot o) (!o.status.transformed)
          (cause := transformCause))
      g.logMsg s!"{oName} transforms into a 0/0 Phyrexian with {counters} +1/+1 counters"
    | none => g
  | .turnFaceUp =>
    match g.srcObj? sourceId with
    | some o =>
      let g := g.record (GameEvent.turnedFaceUp g.turnNumber (g.snapshot o)
        (cause := g.resolveOptionalCause none (fallbackSrc := sourceId) (fallbackCtrl := some controller)))
      g.logMsg s!"{g.name (g.object! o.id)} is turned face up"
    | none => g
  | .gingerDash =>
    match g.srcObj? sourceId with
    | some o =>
      g.createEffect (.cantBeBlockedExceptByHasteUntilEot o.id)
        |>.logMsg s!"{g.name o} can't be blocked this turn except by creatures with haste"
    | none => g
  | .ward cost =>
    let abObj? := g.resolvingAbilityObject?
    let causeId? := abObj?.bind (·.fraCauseId)
    let payer? :=
      (abObj?.bind (·.fraCauseController)).orElse (fun _ =>
        causeId?.bind (fun cid => (g.stackEntry? cid).map (·.controller)))
    match causeId?, payer? with
    | some spellId, some payer =>
      match g.findObject? spellId with
      | some o =>
        if o.zone == .stack then
          let who := (g.player payer).name
          let msg :=
            match cost with
            | .genericMana n =>
              s!"{who} may pay \{{n}} or the spell is countered (ward)"
            | .discardEnchantmentInstantOrSorcery =>
              s!"{who} may discard an enchantment, instant, or sorcery card or the spell is countered (ward)"
            | .sacrificeLegendary =>
              s!"{who} may sacrifice a legendary artifact or creature or the spell is countered (ward)"
            | .discardOrPay n =>
              s!"{who} may discard a card or pay \{{n}} or the spell is countered (ward)"
            | .fivePoison =>
              s!"{who} may get five poison counters or the spell is countered (ward)"
            | .discardCard =>
              s!"{who} may discard a card or the spell is countered (ward)"
            | .sacrificePermanents n _ _ =>
              s!"{who} may sacrifice {n} permanents or the spell is countered (ward)"
          (g.change (.pending (.payWard payer spellId cost))).logMsg msg
        else g
      | none => g
    | _, _ => g

/-- Resume a deferred `FrcPostStep` after a `Pending.chooseReplacement` pause. -/
partial def runFrcPostStep (g : Game) (step : FrcPostStep) : Game :=
  match step with
  | .putDrawnBackOnTop p count =>
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
  | .logExploreLandToHand controller cardId cardName =>
    if (g.followMovedToZone? cardId (· == .hand controller)).isSome then
      g.logMsg s!"{(g.player controller).name} explores and puts {cardName} into their hand"
    else g
  | .offerMaySearchBasics owner => g.offerMaySearchBasics owner
  | .makeHumanToken owner => g.makeFrc owner .human
  | .grantControlledCreaturesIndestructible controller =>
    g.grantUntilEotToControlledCreatures controller Keyword.indestructible "indestructible"
  | .destroyNonRecentCreaturesAtFive x =>
    if x >= 5 then
      g.destroyIds (g.battlefield.filter (g.isCreature ·) |>.map (·.id))
        (fun o => !g.recentTokenIds.contains o.id)
    else g
  | .makeMitesThenDestroyAtFive controller x =>
    let g := g.makeFrc controller .mite x
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
      g.makeFrc controller .incubator 1 0 (extraCounters := extra) (cause := cause)
  | .polymorphRevealCreatures controller startIdx sourceId ids =>
    let count :=
      if ids.isEmpty then startIdx
      else ids.foldl (fun acc id => if g.wasPermanentExiled id startIdx then acc + 1 else acc) 0
    let (g, revealCause) := g.allocDelayedCause (some controller) sourceId
    let (g, hits, rest) := g.revealUntil controller (·.isCreature) count (cause := some revealCause)
    let g := g.putHits controller hits (cause := some revealCause)
    if let .chooseReplacement .. := g.pending then
      g.chainPendingReplacement (.finishFrcRestBottom controller rest true (some revealCause))
    else
      g.restBottom controller rest true (cause := some revealCause)
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
    let (g, revealCause) := g.allocDelayedCause (some controller) sourceId
    let (g, hits, rest) := g.revealUntil owner (·.isCreature) 1 (cause := some revealCause)
    let g := g.putHits owner hits (cause := some revealCause)
    if let .chooseReplacement .. := g.pending then
      g.chainPendingReplacement (.finishFrcRestBottom owner rest false (some revealCause))
    else
      g.restBottom owner rest false (cause := some revealCause)
  | .discardHandThenDrainAndDraw victim controller =>
    let g := g.handDiscard victim
    if let .chooseReplacement .. := g.pending then
      g.chainPendingReplacement (.finishFrcPostStep (.loseThreeDrawOneGainThree victim controller))
    else g.runFrcPostStep (.loseThreeDrawOneGainThree victim controller)
  | .loseThreeDrawOneGainThree victim controller =>
    let g := g.loseLife victim 3
    let g := g.draw controller 1
    g.gainLife controller 3
  | .optionalOncePolymorphReveal controller sourceId =>
    match g.srcObj? sourceId with
    | some src =>
      if g.optionalOnceUsedThisTurn src.id then g
      else
        let (g, rc) := g.allocDelayedCause (some controller) sourceId
        let g := g.record (GameEvent.optionalOnceActed g.turnNumber controller src.id (cause := some rc))
        let (g, hits, rest) := g.revealUntil controller (·.isCreature) 1 (cause := some rc)
        let g := g.putHits controller hits (cause := some rc)
        if let .chooseReplacement .. := g.pending then
          g.chainPendingReplacement (.finishFrcRestBottom controller rest false (some rc))
        else
          g.restBottom controller rest false (cause := some rc)
    | none => g
  | .handDiscardToBottom controller => g.handDiscardToBottomOf controller
  | .revealCreatureOrPlaneswalker controller sourceId =>
    let (g, revealCause) := g.allocDelayedCause (some controller) sourceId
    let (g, hits, rest) := g.revealUntil controller creatureOrWalker 1 (cause := some revealCause)
    let g := g.putHits controller hits (cause := some revealCause)
    if let .chooseReplacement .. := g.pending then
      g.chainPendingReplacement (.finishFrcRestBottom controller rest false (some revealCause))
    else
      g.restBottom controller rest false (cause := some revealCause)
  | .grantRecentTokensLifelinkHaste =>
    g.withBatch none fun g =>
      g.recentTokenIds.foldl (fun g tid =>
        match g.findObject? tid with
        | some tok =>
          if tok.isOnBattlefield then
            g.createEffect (.keywordsUntilEot tok.id (Keywords.merge Keyword.lifelink Keyword.haste))
              |>.logMsg s!"{g.name tok} gains lifelink and haste until end of turn"
          else g
        | none => g) g
  | .discardHand controller => g.handDiscard controller
  | .currencyReturnCreateToken controller exiledId sourceId isLand =>
    if (g.followMovedToZone? exiledId (· != .exile)).isSome then
      let g := g.pruneLinkedExileId sourceId exiledId
      if isLand then g.makeFrc controller .treasure else g.makeFrc controller .rogue
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
  let (g, hits, rest) := g.revealUntil who (·.isCreature) n (cause := some cause)
  let g := g.putHits who hits (cause := some cause)
  if let .chooseReplacement .. := g.pending then
    g.chainPendingReplacement (.finishFrcRestBottom who rest true (some cause))
  else
    g.restBottom who rest true (cause := some cause)

end Game
end Mtg.Engine
