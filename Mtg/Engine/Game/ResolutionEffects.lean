import Mtg.Engine.Game.ResolutionHelpers

/-!
# Named resolution effects

Card-specific resolution helpers: casting during resolution (CR 608.2g),
countering spells (CR 701.6), exile-until-source-leaves (CR 610.3),
named tokens, extort, reflexive triggers (CR 603.12), and copy effects
(CR 707).
-/

namespace Mtg.Engine
namespace Game

/-- Put Palantír's influence counter when `target` is still a legal opponent.
`none` means the ability does nothing further: no scry, draw, or mill.
`some none` means `recordPutCounters` paused on `Pending.chooseReplacement`.
`some (some increased)` means the counter put completed synchronously and
`increased` is whether the influence total went up. -/
def putPalantirInfluence (g : Game) (sourceId : ObjectId) (target : Option PlayerId) :
    Game × Option (Option Bool) :=
  let refuse :=
    (g.logMsg
      "The target is no longer legal. No influence counter, scry, draw, or mill.",
     none)
  match target with
  | none => refuse
  | some pid =>
    if !g.stillInGame pid then refuse
    else
      match g.findObject? sourceId with
      | none => refuse
      | some src =>
        let ctrl := g.you src
        if !src.isOnBattlefield || !g.isLivingOpponentOf ctrl pid ||
            !g.playerCanBeTargetedBy ctrl pid (some sourceId) then refuse
        else
          let before := src.status.influence
          let g := g.recordPutCounters src.id .influence 1 (byPlayer := g.controllerOf src)
          if let .chooseReplacement .. := g.pending then
            (g, some none)
          else
            let after := ((g.findObject? sourceId).map (·.status.influence)).getD before
            let g :=
              if after > before then g.logMsg s!"{g.name src} gets an influence counter" else g
            (g, some (some (after > before)))

/-- Palantír of Orthanc: an illegal target means no influence, scry, draw,
or mill. -/
def applyPalantir (g : Game) (sourceId : ObjectId) (target : Option PlayerId) : Game :=
  let before := ((g.findObject? sourceId).map (·.status.influence)).getD 0
  let (g, ok) := g.putPalantirInfluence sourceId target
  match ok with
  | none => g
  | some none =>
    g.chainPendingReplacement (.finishPostStep (.logInfluenceThenScryTwo sourceId before))
  | some (some _) =>
    match g.findObject? sourceId with
    | some src => g.beginScry (g.you src) 2
    | none => g

/-- Copy a spell on the stack, with its modes, targets, X, and paid optional
costs (CR 707.10), returning the new copy's `ObjectId` (if created). The copy
is not cast. -/
def copyStackSpellWithId (g : Game) (src : GameObject) (controller : PlayerId)
    (cause : Option EventCause := none) : Game × Option ObjectId :=
  let dispName := if src.status.faceDown then "face-down spell" else g.name src
  if !g.stillInGame controller then
    (g.logMsg s!"A copy of {dispName} is not created (CR 800.4d)", none)
  else
    let copyId : ObjectId := ⟨g.nextObjectId⟩
    let baseSnap := g.snapshot src
    let copySnap : EventObject :=
      if src.status.faceDown then
        let masked := g.copiableValues src
        { baseSnap with
          id := some copyId
          name := ""
          owner := controller
          controller := some controller
          zone := .stack
          isCopy := true
          isCommander := false
          printed := some masked
          copiable := some masked
          adventurerCard := none
          faceDown := true
        }
      else
        { baseSnap with
          id := some copyId
          owner := controller
          controller := some controller
          zone := .stack
          isCopy := true
          isCommander := false
        }
    let resolvedCause :=
      match cause with
      | some c => c
      | none =>
        g.resolveOptionalCause (g.resolvingOneShotCause controller (some src.id))
          (fallbackSrc := some src.id) (fallbackCtrl := some controller)
    let g := g.record (GameEvent.stackObjectCopied g.turnNumber src.id copySnap controller
      (cause := resolvedCause))
    (g.logMsg s!"A copy of {dispName} is created", some copyId)

/-- Copy a spell on the stack, with its modes, targets, X, and paid optional
costs (CR 707.10). The copy is not cast. -/
def copyStackSpell (g : Game) (src : GameObject) (controller : PlayerId)
    (cause : Option EventCause := none) : Game :=
  (g.copyStackSpellWithId src controller cause).1

/-- Why `id` cannot be cast from a pending Cosmic Cube look, if it cannot. -/
def mayCastFromLookedError (g : Game) (p : PlayerId) (ids : Array ObjectId)
    (maxMv : Int) (id : ObjectId) : Option String :=
  if !ids.contains id then
    some "That card is not among the cards you looked at"
  else if g.cantCastSpellsThisTurn p then
    some "You can't cast spells this turn (CR 101.2)"
  else if g.splitSecondOnStack then
    some "A spell with split second is on the stack (CR 702.61a)"
  else if g.combatLocksNonManaAbilities then
    some "During combat, players can't cast spells (Yuriko, Blade of the Mighty)"
  else if g.opponentsCantCastOnActiveTurn p then
    some "Opponents can't cast spells during that player's turn"
  else
    match g.findObject? id with
    | none => some "There is no card to cast"
    | some o =>
      let bc := g.baseCard o
      let tcs := g.evalLayer3 o
      if o.zone != .library p then
        some s!"{g.name o} is no longer among the cards you looked at"
      else if !isCastableObject o then
        some s!"{g.name o} can't be cast"
      else if g.isLand o then
        some "A land cannot be cast"
      else if g.spellNameForbidden bc.name then
        some s!"Spells named {bc.name} can't be cast"
      else if !g.graveyardCastThresholdMet p o.id bc then
        some s!"{bc.name} cannot be cast right now"
      else if (g.objectManaValue o : Int) > maxMv then
        some s!"{g.name o}'s mana value is greater than the greatest power among attacking creatures you control"
      else if g.isAura o && !bc.allowsZeroTargets &&
          (g.legalAuraTargets p bc (some o.id)).isEmpty then
        some s!"{g.name o} requires a target to enchant"
      -- CR 601.2b–c / 115.1 / 734.1: a spell that can't announce a legal target (kicked
      -- or not) or a choosable mode can't be cast from among the looked-at cards.
      else if isModalSpellFace bc &&
          !(effectiveSpellModes bc).any (fun e =>
            let m := if tcs.isEmpty then e else TextChange.applyEffect tcs e
            g.spellModeIsChoosable p m (some o.id)) &&
          !isReturnUpToTwoGyModal bc && !bc.allowsZeroTargets then
        some s!"{g.name o} has no legal target and can't be cast"
      else if !g.isAura o && !isModalSpellFace bc && bc.requiresTarget &&
          !bc.allowsZeroTargets && !g.castFaceHasLegalTarget p bc tcs (some o.id) then
        some s!"{g.name o} has no legal target and can't be cast"
      -- CR 601.2b / 601.2h: a mandatory sacrifice additional cost must be payable.
      else g.mandatorySacrificeError? p o.id bc (g.name o)

/-- Look at the top `n` cards and wait for the controller to choose whether
to cast one with mana value at most `maxMv` (Cosmic Cube; MSH 356). -/
def beginMayCastFromLooked (g : Game) (p : PlayerId) (n : Nat) (maxMv : Int) :
    Game :=
  if !g.stillInGame p then g
  else
    let lib := (g.player p).library
    let take := min n lib.size
    let ids := lib.extract (lib.size - take) lib.size
    if ids.isEmpty then
      g.logMsg "No cards to look at"
    else
      let g := g.record (GameEvent.lookedAt g.turnNumber p ids
        (cause := some (g.resolvingOrRuleCause p)))
      (g.change (.pending (.mayCastFromLooked p ids maxMv))).logMsg
        s!"{(g.player p).name} looks at the top {ids.size} cards. You may cast a spell from among them with mana value {maxMv} or less as this ability resolves"

/-- Put an artifact from hand onto the battlefield. A surrounding `.bind`
step observes the entered permanent from `g.events`. -/
def choosePutArtifactFromHand (g : Game) (p : PlayerId) (cardId : ObjectId) :
    Except String Game := do
  match g.pending with
  | .mayPutArtifactFromHand q hostId =>
    if p != q then
      throw s!"Only {(g.player q).name} may put an artifact onto the battlefield"
    let some o := g.findObject? cardId | throw "no such object"
    if o.zone != .hand p then
      throw s!"{g.name o} is not in your hand"
    if !isDiscardableCard o || !g.isArtifact o then
      throw s!"{g.name o} is not an artifact card"
    let name := g.name o
    let outerCont? := g.pendingReplacement
    let g := if outerCont?.isSome then g.change (.pendingReplacement none) else g
    let g := g.change (.pending .none)
    let (g, newId) := g.putOntoBattlefield cardId p
    let g :=
      if let .chooseReplacement .. := g.pending then
        g.chainPendingReplacement
          (.finishPostStep (.putArtifactOntoBattlefield p cardId hostId))
      else
        let entered := g.object! newId
        if entered.isOnBattlefield then
          let g := g.logMsg s!"{(g.player p).name} puts {name} onto the battlefield"
          g.afterPermanentEnters entered
        else g
    return g.reattachOuterCont outerCont?
  | _ => throw "Not time to put an artifact from your hand"

/-- Mill opponents without returning a reflexive-trigger flag, deferring across
any open `Pending.chooseReplacement` pause. -/
def millOpponentsOnly (g : Game) (opponents : Array PlayerId) (n : Nat)
    (cause : Option EventCause := none)
    (fromEventIdx? : Option Nat := none) : Game :=
  let loopFromIdx := fromEventIdx?.getD g.events.size
  if g.sbaPaused || (match g.pending with | .chooseReplacement .. => true | _ => false) then
    g.chainPendingReplacement (.finishPostStep (.millOpponentsOnly opponents n cause (some loopFromIdx)))
  else
    let preLoop :=
      match fromEventIdx? with
      | some idx => g.mkHistoricalGameAt idx
      | none => g
    g.withBatch cause fun g => Id.run do
      let mut g := g
      for i in [0:opponents.size] do
        let pid := opponents[i]!
        g := g.mill pid n (cause := cause) (deferPlayFromExileLogs := true)
        if g.sbaPaused || (match g.pending with | .chooseReplacement .. => true | _ => false) then
          let rem := opponents.extract (i + 1) opponents.size
          return g.chainPendingReplacement
            (.finishPostStep (.millOpponentsOnly rem n cause (some loopFromIdx)))
      return emitExpiredPlayFromExileLogs preLoop g loopFromIdx

/-- Put +1/+1 and lifelink until end of turn on a creature (Bard the Bowman). -/
def applyBardBowman (g : Game) (targetId : ObjectId) : Game :=
  match g.findObject? targetId with
  | none => g.logMsg "The target is no longer legal"
  | some o =>
    if !o.isOnBattlefield || !g.isCreature o then
      g.logMsg "The target is no longer legal"
    else
      let cause := g.currentResolvingContext?.map fun (src, ctrl) =>
        .oneShotEffect none src ctrl
      g.withBatch cause fun g =>
        let g := g.addPlusOnePlusOneTo o 1 (cause := cause)
        if let .chooseReplacement .. := g.pending then
          g.chainPendingReplacement
            (.finishPostStep (.grantLifelinkUntilEot o.id (g.currentBatch.bind (·.2))))
        else if let some cur := g.findObject? o.id then
          if cur.isOnBattlefield then
            let g := g.createEffect (.keywordsUntilEot cur.id #[Keyword.lifelink]) (cause := cause)
            g.logMsg s!"{g.name cur} gains lifelink until end of turn"
          else g
        else g

/-- Finish the post-move CR 610.3 link step of `exileUntilSourceLeaves` once
`g.move` to `.exile` completes. -/
def finishExileUntilSourceLeaves (g : Game) (sourceId : Option ObjectId)
    (fromId : ObjectId) : Game :=
  match g.followMovedWithOrigin? fromId (· == .exile) with
  | none => g
  | some (moved, fromZone) =>
    let g := g.changeObject moved.id (.returnToZone (some fromZone))
    let g :=
      match sourceId.bind g.findObject? with
      | some src => g.changeObject src.id (.pushLinkedExile moved.id)
      | none => g
    g.logMsg s!"{g.name moved} is exiled until the source leaves the battlefield"

/-- Exile `o` until `source` leaves the battlefield, linking the new exile id
and storing the exiling one-shot `EventCause` for the return (CR 610.3). -/
def exileUntilSourceLeaves (g : Game) (sourceId : Option ObjectId) (o : GameObject)
    (cause : Option EventCause := none)
    (deferPlayFromExileLogs : Bool := false) : Game :=
  let fallbackCtrl :=
    (sourceId.bind g.findObject?).bind (fun src => (g.controllerOf src).orElse (fun _ => some src.owner))
  let (g, linkCause) :=
    match cause with
    | some c => (g, c)
    | none => g.allocDelayedCause fallbackCtrl sourceId
  let (g, _) := g.move o.id .exile none (cause := some linkCause)
    (deferPlayFromExileLogs := deferPlayFromExileLogs)
  if let .chooseReplacement .. := g.pending then
    g.chainPendingReplacement (.finishPostStep (.finishExileUntilSourceLeaves sourceId o.id))
  else
    g.finishExileUntilSourceLeaves sourceId o.id

/-- Finish the post-move CR 607.2a link step of `exileForLeaveTrigger` once
`g.move` to `.exile` completes. -/
def finishExileForLeaveTrigger (g : Game) (sourceId : Option ObjectId)
    (fromId : ObjectId) : Game :=
  match g.followMovedToZone? fromId (· == .exile) with
  | none => g
  | some moved =>
    let g :=
      match sourceId.bind g.findObject? with
      | some src => g.changeObject src.id (.pushLeaveTriggerExile moved.id)
      | none => g
    g.logMsg s!"{g.name moved} is exiled"

/-- Exile `o` for a leave-the-battlefield trigger (Fiend Hunter). The card
does not return automatically when the source leaves. -/
def exileForLeaveTrigger (g : Game) (sourceId : Option ObjectId) (o : GameObject)
    (cause : Option EventCause := none) : Game :=
  let (g, _) := g.move o.id .exile none (cause := cause)
  if let .chooseReplacement .. := g.pending then
    g.chainPendingReplacement (.finishPostStep (.finishExileForLeaveTrigger sourceId o.id))
  else
    g.finishExileForLeaveTrigger sourceId o.id

/-- Return each exiled id in `remainingIds` simultaneously in two passes
(moving all cards to their destination zones before running `afterPermanentEnters`,
checking Aura attachment against pre-batch `preBattlefield` per CR 303.4f),
pausing on `Pending.chooseReplacement`. -/
def returnLinkedExileLoop (g : Game) (remainingIds : Array ObjectId)
    (cause : Option EventCause := none)
    (enteredFromIds : Array ObjectId := #[])
    (preBattlefield : Option (Array GameObject) := none)
    (pendingLog : Option (ObjectId × Zone) := none)
    (fromEventIdx? : Option Nat := none) : Game := Id.run do
  let deferPfe := remainingIds.size > 1 || fromEventIdx?.isSome
  let loopFromIdx := fromEventIdx?.getD g.events.size
  if let .chooseReplacement .. := g.pending then
    return g.chainPendingReplacement
      (.returnLinkedExileLoop remainingIds cause enteredFromIds preBattlefield pendingLog
        (if deferPfe then some loopFromIdx else none))
  let preLoop :=
    match fromEventIdx? with
    | some idx => g.mkHistoricalGameAt idx
    | none => g
  let preBf := preBattlefield.getD g.battlefield
  let mut g := g
  if let some (fromId, dest) := pendingLog then
    if let some moved := g.followMovedToZone? fromId (· == dest) then
      match dest with
      | .hand p =>
        g := g.logMsg s!"{g.name moved} returns to {(g.player p).name}'s hand"
      | .graveyard p =>
        g := g.logMsg s!"{g.name moved} returns to {(g.player p).name}'s graveyard"
      | _ => pure ()
  let mut entered := enteredFromIds
  for i in [0:remainingIds.size] do
    let id := remainingIds[i]!
    if let some o := g.findObject? id then
      if o.zone == .exile then
        let owner := o.owner
        match o.returnToZone with
        | some (.hand p) =>
          let (g', _) := g.move id (.hand p) none (cause := cause) (deferPlayFromExileLogs := deferPfe)
          if let .chooseReplacement .. := g'.pending then
            let rem := remainingIds.extract (i + 1) remainingIds.size
            return g'.chainPendingReplacement
              (.returnLinkedExileLoop rem cause entered (some preBf) (some (id, .hand p))
                (if deferPfe then some loopFromIdx else none))
          if let some moved := g'.followMovedToZone? id (· == .hand p) then
            g := g'.logMsg s!"{g'.name moved} returns to {(g'.player p).name}'s hand"
          else
            g := g'
        | some (.graveyard p) =>
          let (g', _) := g.move id (.graveyard p) none (cause := cause) (deferPlayFromExileLogs := deferPfe)
          if let .chooseReplacement .. := g'.pending then
            let rem := remainingIds.extract (i + 1) remainingIds.size
            return g'.chainPendingReplacement
              (.returnLinkedExileLoop rem cause entered (some preBf) (some (id, .graveyard p))
                (if deferPfe then some loopFromIdx else none))
          if let some moved := g'.followMovedToZone? id (· == .graveyard p) then
            g := g'.logMsg s!"{g'.name moved} returns to {(g'.player p).name}'s graveyard"
          else
            g := g'
        | _ =>
          let (g', _) := g.move id .battlefield (some owner)
            (preBattlefield := some preBf) (cause := cause) (deferPlayFromExileLogs := deferPfe)
          g := g'
          entered := entered.push id
          if let .chooseReplacement .. := g.pending then
            let rem := remainingIds.extract (i + 1) remainingIds.size
            return g.chainPendingReplacement
              (.returnLinkedExileLoop rem cause entered (some preBf) none
                (if deferPfe then some loopFromIdx else none))
  if deferPfe then
    g := emitExpiredPlayFromExileLogs preLoop g loopFromIdx
  for j in [0:entered.size] do
    let fromId := entered[j]!
    if let some enteredObj := g.followMovedToZone? fromId (· == .battlefield) then
      if let some hid := enteredObj.attachedTo then
        let hostName := (g.findObject? hid).map g.name |>.getD (toString hid)
        g := g.logMsg s!"{g.name enteredObj} returns attached to {hostName} (does not target)"
      else
        g := g.logMsg s!"{g.name enteredObj} returns to the battlefield"
      g := g.afterPermanentEnters (g.object! enteredObj.id)
      if let .chooseReplacement .. := g.pending then
        let remEntered := entered.extract (j + 1) entered.size
        if !remEntered.isEmpty then
          g := g.chainPendingReplacement
            (.returnLinkedExileLoop #[] cause remEntered (some preBf) none none)
        return g
  return g

/-- Return one exiled id to the battlefield under its owner. Auras attach
without targeting; if they cannot attach, they remain in exile. -/
def returnExiledId (g : Game) (id : ObjectId)
    (cause : Option EventCause := none) : Game :=
  g.returnLinkedExileLoop #[id] (cause := cause)

/-- Return cards linked-exiled by `source` (leave-trigger list first, then
until-leaves). -/
def returnLinkedExile (g : Game) (source : GameObject) : Game :=
  g.withBatch none fun g =>
    g.returnLinkedExileLoop (source.leaveTriggerExile ++ source.linkedExile)

/-- Named MSH token that carries extra rules text (backed by `TokenSpec`). -/
def theVoidToken : CardDef := (tokenPrinted? .theVoid).getD default

/-- Increment the source's plan counter if still on the battlefield, deferring
across any open `Pending.chooseReplacement` pause. -/
def incrementPlanSource (g : Game) (controller : PlayerId) (sourceId : Option ObjectId) : Game :=
  if let .chooseReplacement .. := g.pending then
    g.chainPendingReplacement (.finishPostStep (.incrementPlanSource controller sourceId))
  else
    match sourceId.bind g.findObject? with
    | some o =>
      if o.isOnBattlefield then
        let cause := g.resolveOptionalCause none (fallbackSrc := sourceId) (fallbackCtrl := some controller)
        g.withBatch (g.resolvingBatchCause controller sourceId) fun g =>
          g.recordPutCounters o.id .plan 1 (byPlayer := some controller) (cause := some cause)
      else
        g.logMsg s!"{g.name o} is no longer on the battlefield"
    | none =>
      g.logMsg "The ability's source is no longer in play"

/-- Current power of `sourceId` if it is still on the battlefield; otherwise
last-known power, falling back to the object's current power. -/
def sourcePowerAtResolution (g : Game) (sourceId : Option ObjectId)
    (lastKnownPower : Option Int := none) : Int :=
  let lkp := lastKnownPower.orElse (fun _ => sourceId.bind g.lastKnownPowerOf?)
  match sourceId.bind g.findObject? with
  | some o =>
    if o.isOnBattlefield then g.power o
    else lkp.getD (g.snapshotPower o)
  | none => lkp.getD (0 : Int)

/-- How many Equipment are attached to the source (CR 608.2h / 301.5c).
A source still on the battlefield uses its live Equipment attachments.
A source that has left the battlefield counts the Equipment unattached from it
in its battlefield-departure batch, falling back to `lastKnownPower` for
synthetic unit tests that invoke resolution directly without departure events. -/
def attachedEquipmentAtResolution (g : Game) (sourceId : Option ObjectId)
    (lastKnownPower : Option Int := none) : Nat :=
  let departedOrPhasedCount? (sid : ObjectId) : Option Nat :=
    (g.departedOrPhasedOutAttachments? sid).map fun atts =>
      (atts.filter (fun att => att.subtypes.contains .equipment)).size
  match sourceId with
  | some sid =>
    match g.findLiveSourceObject? sid with
    | some o =>
      if o.isOnBattlefield then g.attachedEquipmentCount o
      else (departedOrPhasedCount? sid).getD (lastKnownPower.getD (0 : Int)).toNat
    | none => (departedOrPhasedCount? sid).getD (lastKnownPower.getD (0 : Int)).toNat
  | none => (lastKnownPower.getD (0 : Int)).toNat

/-- Current P/T of `sourceId` if it is still on the battlefield; otherwise
last-known values, falling back to the object's current P/T. -/
def sourcePTAtResolution (g : Game) (sourceId : Option ObjectId)
    (lastKnownPower lastKnownToughness : Option Int := none) : Int × Int :=
  let lkp := lastKnownPower.orElse (fun _ => sourceId.bind g.lastKnownPowerOf?)
  let lkt := lastKnownToughness.orElse (fun _ => sourceId.bind g.lastKnownToughnessOf?)
  match sourceId.bind g.findObject? with
  | some src =>
    if src.isOnBattlefield then (g.power src, g.toughness src)
    else (lkp.getD (g.snapshotPower src), lkt.getD (g.snapshotToughness src))
  | none => (lkp.getD 0, lkt.getD 0)

/-- Top `count` cards of `p`'s library (last = current top). -/
def scryLookedIds (g : Game) (p : PlayerId) (count : Nat) : Array ObjectId :=
  let lib := (g.player p).library
  let n := min count lib.size
  lib.extract (lib.size - n) lib.size

/-- Record `PlayerEvent.lookedAt` when `looked` is non-empty and log that `p`
looks at the top `n` cards of their library. -/
def logLookAtTop (g : Game) (p : PlayerId) (n : Nat)
    (looked : Array ObjectId := #[]) (sourceId : Option ObjectId := none) : Game :=
  let g :=
    if looked.isEmpty then g
    else g.record (GameEvent.lookedAt g.turnNumber p looked
      (cause := some (g.resolvingOrRuleCause p sourceId)))
  g.logMsg s!"{(g.player p).name} looks at the top {n} cards"

/-- Pause-safe loop for `exileTopPlayThisTurn` / `exileTopForPlay`. -/
def exileTopForPlayLoop (g : Game) (fromPlayer caster : PlayerId)
    (remaining : Nat) (mayCastStyle : Bool) (cause? : Option EventCause)
    (pendingFromId : Option ObjectId := none)
    (fromEventIdx? : Option Nat := none) : Game := Id.run do
  let fmtMsg (g : Game) (ownerName cardName : String) : String :=
    if mayCastStyle then
      s!"{ownerName} exiles {cardName}; {(g.player caster).name} may cast it"
    else
      s!"{ownerName} exiles {cardName} and may play it this turn"
  if let .chooseReplacement .. := g.pending then
    return g.chainPendingReplacement
      (.finishPostStep (.exileTopForPlayLoop fromPlayer caster remaining mayCastStyle cause? pendingFromId fromEventIdx?))
  let loopFromIdx := fromEventIdx?.getD g.events.size
  let mut g := g
  if let some fid := pendingFromId then
    if let some moved := g.followMovedToZone? fid (· == .exile) then
      if g.stillInGame caster then
        g := g.createEffect (.playPermission moved.id { player := caster, landsAllowed := !mayCastStyle }) (cause := cause?)
      g := g.logMsg (fmtMsg g (g.player fromPlayer).name (g.name moved))
  if !g.stillInGame fromPlayer || !g.stillInGame caster then
    return emitExpiredPlayFromExileLogsLazy (fun _ => g.mkHistoricalGameAt loopFromIdx) g loopFromIdx
  for i in [0:remaining] do
    if !g.stillInGame fromPlayer || !g.stillInGame caster then
      return emitExpiredPlayFromExileLogsLazy (fun _ => g.mkHistoricalGameAt loopFromIdx) g loopFromIdx
    let pl := g.player fromPlayer
    if pl.library.isEmpty then
      g := g.logMsg s!"{pl.name} has no cards in their library to exile"
    else
      let top := pl.library.back!
      let cardName := g.name (g.object! top)
      let (g', _) := g.move top .exile none (cause := cause?) (deferPlayFromExileLogs := true)
      g := g'
      if let .chooseReplacement .. := g.pending then
        let rem := remaining - (i + 1)
        return g.chainPendingReplacement
          (.finishPostStep (.exileTopForPlayLoop fromPlayer caster rem mayCastStyle cause? (some top) (some loopFromIdx)))
      if let some moved := g.followMovedToZone? top (· == .exile) then
        if g.stillInGame caster then
          g := g.createEffect (.playPermission moved.id { player := caster, landsAllowed := !mayCastStyle }) (cause := cause?)
        g := g.logMsg (fmtMsg g pl.name cardName)
  return emitExpiredPlayFromExileLogsLazy (fun _ => g.mkHistoricalGameAt loopFromIdx) g loopFromIdx

/-- Exile the top `n` cards of `fromPlayer`'s library. `caster` may play
them this turn. `logAfter ownerName cardName` is the per-card message. -/
def exileTopForPlay (g : Game) (fromPlayer caster : PlayerId) (n : Nat)
    (logAfter : String → String → String) (mayCastStyle : Bool := false) : Game :=
  let _ := logAfter
  if !g.stillInGame fromPlayer || !g.stillInGame caster then g
  else
    let (g0, cause?) : Game × Option EventCause :=
      if n > 0 && !(g.player fromPlayer).library.isEmpty then
        let (g, c) := g.allocDelayedCause (some caster)
        (g, some c)
      else (g, none)
    g0.withBatch cause? fun g =>
      g.exileTopForPlayLoop fromPlayer caster n mayCastStyle cause?

/-- Exile the top `n` cards of `p`'s library. They may be played this turn. -/
def exileTopPlayThisTurn (g : Game) (p : PlayerId) (n : Nat) : Game :=
  g.exileTopForPlay p p n fun owner card =>
    s!"{owner} exiles {card} and may play it this turn"

/-- Extort is paid: each opponent loses 1 life and `controller` gains the
life actually lost in a single simultaneous event batch / cause (CR 702.101a /
608.2c / MSH 292). Extort does not target (MSH 296). -/
def extortDrain (g : Game) (controller : PlayerId) : Game :=
  let opps := g.livingOpponents controller
  let (g, cause?) : Game × Option EventCause :=
    match g.currentBatch.bind (·.2) with
    | some bc => (g, some bc)
    | none =>
      match g.resolvingBatchCause controller with
      | some rc => (g, some rc)
      | none =>
        if opps.isEmpty then (g, none)
        else
          let (g, c) := g.allocDelayedCause (some controller)
          (g, some c)
  let g :=
    g.withBatch cause? fun g =>
      let batchCause := cause?.orElse (fun _ => g.currentBatch.bind (·.2))
      let (g, lost) :=
        opps.foldl (fun (acc : Game × Nat) pl =>
          let before := (acc.1.player pl.id).life
          let g := acc.1.loseLife pl.id 1 (cause := batchCause)
          let after := (g.player pl.id).life
          let delta := if before > after then (before - after).toNat else 0
          (g, acc.2 + delta)) (g, 0)
      if lost == 0 then g
      else
        let c := batchCause.orElse (fun _ => g.currentBatch.bind (·.2))
        g.gainLife controller lost (cause := c)
  if let .chooseReplacement .. := g.pending then
    g.chainPendingReplacement (.logMessage "Extort is paid")
  else
    g.logMsg "Extort is paid"

/-- A stack object to stand for `sourceId` as an ability's source. -/
def abilitySourceFor (g : Game) (controller : PlayerId) (sourceId : Option ObjectId) : GameObject :=
  match sourceId with
  | some sid =>
    match g.findLiveSourceObject? sid with
    | some o => o
    | none =>
      match g.lastKnownBefore? sid with
      | some eo => damageSourceObjectFromLki eo
      | none =>
        { id := sid, printed := { name := "The ability", types := #[] }
          owner := controller, controller := some controller, zone := .battlefield }
  | none =>
    { id := noSourceSentinelId, printed := { name := "The ability", types := #[] }
      owner := controller, controller := some controller, zone := .battlefield }

/-- Queue a reflexive triggered ability (“When you do, …”) with `effect` via
`WaitingTrigger` + `recordReflexiveTrigger` (`TriggerQueueEvent.triggered`,
CR 603.3c–d / 603.12). Its targets are chosen when put on the stack. -/
def putReflexiveTrigger (g : Game) (controller : PlayerId) (sourceId : Option ObjectId)
    (effect : Effect) (deferToPriority : Bool := false)
    (causeIds : Array ObjectId := #[])
    (causeId : Option ObjectId := none)
    (lastKnownPower : Option Int := none)
    (lastKnownToughness : Option Int := none) : Game :=
  if !g.stillInGame controller then g
  else
    let src := g.abilitySourceFor controller sourceId
    let marker : TriggeredAbility := { word := .when, pattern := .thisEnters, effect }
    let eventCause := g.resolveOptionalCause none (fallbackSrc := sourceId) (fallbackCtrl := some controller)
    let wt : WaitingTrigger := {
      controller
      source := src
      ability := marker
      pattern := .thisEnters
      causeId := causeId
      causeIds := causeIds
      lastKnownPower := lastKnownPower
      lastKnownToughness := lastKnownToughness
      checked := true
      eventCause := eventCause
      abilityEffect := some effect
      isReflexive := true
    }
    let g := g.recordReflexiveTrigger wt
    if deferToPriority || g.resolvingAbility.isSome || g.resolvingSpell.isSome || g.currentBatch.isSome then g
    else g.putTriggerBatch #[wt]

/-- Offer to pay `cost` up to `maxTimes` times; when the player does, the
reflexive triggered ability `reflexive` triggers (CR 603.12). -/
def offerPayForReflexive (g : Game) (controller : PlayerId) (sourceId : Option ObjectId)
    (cost : Array ManaSymbol) (reflexive : Effect)
    (maxTimes : Nat := 1) : Game :=
  let shown := String.join (cost.toList.map toString)
  let times := if maxTimes > 1 then s!" up to {maxTimes} times" else ""
  g.beginResolutionChoice controller (.mayPayManaForReflexive cost maxTimes reflexive sourceId)
    s!"{(g.player controller).name} may pay {shown}{times}"

/-- Sacrifice the Plan if it is still on the battlefield. `gone` is logged
when the source left; `missing` when it was never found. -/
def sacrificePlanIfOnBattlefield (g : Game) (sourceId : Option ObjectId)
    (gone := fun (name : String) => s!"{name} is no longer on the battlefield")
    (missing := "The Plan is no longer on the battlefield") : Game :=
  match sourceId.bind g.findObject? with
  | some o =>
    if o.isOnBattlefield then g.sacrificeToGraveyard o "the Plan is completed"
    else g.logMsg (gone (g.name o))
  | none =>
    g.logMsg missing

/-- Ask `caster` to cast up to `casts` of the exiled nonland cards. -/
def offerExileCasts (g : Game) (caster : PlayerId) (spells : Array ObjectId)
    (casts : Nat) : Game :=
  if !g.stillInGame caster then g
  else
    g.beginResolutionChoice caster (.mayCastUpToFromExile spells casts)
      s!"{(g.player caster).name} may cast up to {casts} spells from among the exiled cards without paying their mana costs"

/-- Pause-safe loop for `exileTopMayCastUpTo`, running inside an open batch and
offering up to `casts` free spell casts once all moves complete. -/
def exileTopMayCastUpToLoop (g : Game) (fromPlayer caster : PlayerId)
    (remaining casts : Nat) (cause? : Option EventCause)
    (accIds : Array ObjectId := #[])
    (pendingFromId : Option ObjectId := none)
    (fromEventIdx? : Option Nat := none) : Game := Id.run do
  let loopFromIdx := fromEventIdx?.getD g.events.size
  if g.sbaPaused || (match g.pending with | .chooseReplacement .. => true | _ => false) then
    return g.chainPendingReplacement
      (.finishPostStep (.exileTopMayCastUpToLoop fromPlayer caster remaining casts cause? accIds pendingFromId (some loopFromIdx)))
  let preLoop :=
    match fromEventIdx? with
    | some idx => g.mkHistoricalGameAt idx
    | none => g
  let mut g := g
  let mut ids := accIds
  if let some fid := pendingFromId then
    if let some moved := g.followMovedToZone? fid (· == .exile) then
      ids := ids.push moved.id
      g := g.logMsg s!"{(g.player fromPlayer).name} exiles {g.name moved}"
  if !g.stillInGame fromPlayer then
    return emitExpiredPlayFromExileLogs preLoop g loopFromIdx
  for i in [0:remaining] do
    if !g.stillInGame fromPlayer then
      return emitExpiredPlayFromExileLogs preLoop g loopFromIdx
    let pl := g.player fromPlayer
    if pl.library.isEmpty then
      g := g.logMsg s!"{pl.name} has no cards in their library to exile"
    else
      let top := pl.library.back!
      let name := g.name (g.object! top)
      let (g', _) := g.move top .exile none (cause := cause?) (deferPlayFromExileLogs := true)
      g := g'
      if g.sbaPaused || (match g.pending with | .chooseReplacement .. => true | _ => false) then
        let rem := remaining - (i + 1)
        return g.chainPendingReplacement
          (.finishPostStep (.exileTopMayCastUpToLoop fromPlayer caster rem casts cause? ids (some top) (some loopFromIdx)))
      if let some moved := g.followMovedToZone? top (· == .exile) then
        ids := ids.push moved.id
        g := g.logMsg s!"{pl.name} exiles {name}"
  return emitExpiredPlayFromExileLogs preLoop g loopFromIdx

/-- Offer up to `casts` free casts from `ids` after `exileTopMayCastUpTo`'s
exile batch has closed. -/
def finishExileTopMayCastUpToOffer (g : Game) (caster : PlayerId)
    (ids : Array ObjectId) (casts : Nat) : Game :=
  let spells := ids.filter (fun id =>
    (g.findObject? id).any (fun o => o.zone == .exile && isCastableObject o && !g.isLand o))
  if spells.isEmpty || casts == 0 then g
  else g.offerExileCasts caster spells casts

/-- Exile the top `n` cards of `fromPlayer`'s library. `caster` may cast up
to `casts` nonland cards from among them without paying their mana costs. -/
def exileTopMayCastUpTo (g : Game) (fromPlayer caster : PlayerId) (n casts : Nat) : Game :=
  let (g0, cause?) : Game × Option EventCause :=
    if n > 0 && !(g.player fromPlayer).library.isEmpty then
      let (g, c) := g.allocDelayedCause (some caster)
      (g, some c)
    else (g, none)
  let preIds :=
    let lib := (g0.player fromPlayer).library
    let k := min n lib.size
    (lib.extract (lib.size - k) lib.size).reverse
  let g := g0.withBatch cause? fun g =>
    g.exileTopMayCastUpToLoop fromPlayer caster n casts cause?
  if let .chooseReplacement .. := g.pending then
    g.chainPendingReplacement
      (.finishPostStep (.offerMayCastUpToFromExile caster preIds casts))
  else
    let arrived := preIds.filterMap (fun pid => (g.followMovedToZone? pid (· == .exile)).map (·.id))
    g.finishExileTopMayCastUpToOffer caster arrived casts

/-- Apply one post-entry counter change to the permanent `id` (enters-with
effects and counters were already pre-seeded and recorded on arrival by
`Movement.move`, CR 122.6 / 614.1c). -/
def applyEnterMod (g : Game) (controller : PlayerId) (id : ObjectId)
    (mod : EnterMod)
    (cause : Option EventCause := none) : Game :=
  match g.findObject? id with
  | none => g
  | some o =>
    match mod with
    | .loseAllAbilities | .keywords _ | .additionalSubtype _ | .attacking => g
    | .counter .finality _ _ =>
      g.logMsg s!"{g.name o} gets a finality counter"
    | .counter .plusOnePlusOne _ true =>
      g.logMsg s!"{g.name o} enters with {plusOnePlusOneCountersPhrase o.status.plusOnePlusOne}"
    | .counter kind _ true =>
      g.logMsg s!"{g.name o} gets {kind.countersPhrase (o.status.counterCount kind)}"
    | .counter .plusOnePlusOne n false =>
      g.addPlusOnePlusOneTo o n (byPlayer := some controller) (cause := cause)
    | .counter kind n false =>
      g.addCounters o kind n (entersWith := false) (byPlayer := some controller) (cause := cause)

/-- Finish the post-entry modifications, logs, and enters-triggers for a card
that just entered the battlefield via `commitEnteringAttackItems`. Stops if an
`applyEnterMod` call opens `Pending.chooseReplacement` so the remaining mods and
`afterPermanentEnters` run only after the choice is resolved. Does nothing when
the card's entry was redirected off the battlefield. -/
def finishEnteringAttackCard (g : Game) (newId : ObjectId)
    (effectController : PlayerId) (cardName : String)
    (mods : List EnterMod)
    (logKind : EnteringAttackLog) (cause : Option EventCause := none) : Game :=
  match g.findObject? newId with
  | none => g
  | some cur =>
    if !cur.isOnBattlefield then g
    else
      match mods with
      | m :: rest =>
        let g := g.applyEnterMod effectController newId m (cause := cause)
        if let .chooseReplacement .. := g.pending then
          g.chainPendingReplacement
            (.finishEnteringAttackCard (some newId) effectController cardName rest logKind cause)
        else
          g.finishEnteringAttackCard newId effectController cardName rest logKind (cause := cause)
      | [] =>
        match logKind with
        | .putOntoBattlefield =>
          let entered := g.object! newId
          let g := g.logMsg s!"{g.name entered} is put onto the battlefield"
          g.afterPermanentEnters entered
        | .grimReaper =>
          let entered := g.object! newId
          let enteredName := g.name entered
          let g := g.logMsg s!"{enteredName} gets a finality counter"
          g.afterPermanentEnters entered |>.logMsg s!"{enteredName} enters tapped and attacking"
        | .ownerGraveyard loses =>
          let enteredName := g.name (g.object! newId)
          let g := g.afterPermanentEnters (g.object! newId)
          if loses then
            g.logMsg s!"{enteredName} returns, loses all abilities, and gains haste"
          else g

/-- Run post-entry modifications, logs, and `afterPermanentEnters` for all
cards that entered the battlefield simultaneously in `commitEnteringAttackItems`. -/
partial def finishEnteringAttackCards (g : Game)
    (postEntries : Array (ObjectId × PlayerId × String × List EnterMod × EnteringAttackLog))
    (cause : Option EventCause := none)
    (fromEventIdx? : Option Nat := none) : Game :=
  let g :=
    match fromEventIdx? with
    | some idx => emitExpiredPlayFromExileLogs (g.mkHistoricalGameAt idx) g idx
    | none => g
  match postEntries[0]? with
  | none => g
  | some (fromId, effectController, cardName, mods, logKind) =>
    let rest := postEntries.extract 1 postEntries.size
    match g.followMovedToZone? fromId (· == .battlefield) with
    | none => g.finishEnteringAttackCards rest cause none
    | some enteredObj =>
      let g := g.finishEnteringAttackCard enteredObj.id effectController cardName mods logKind (cause := cause)
      if rest.isEmpty then g
      else if g.pending != .none then
        g.chainPendingReplacement (.finishEnteringAttackCards rest cause none)
      else
        g.finishEnteringAttackCards rest cause none

/-- Create the tokens or put the cards in `chosen` onto the battlefield with
their chosen `AttackTarget`s in a single batch, moving all cards onto
`.battlefield` before running enters-with modifications and enters triggers
(CR 508.4 / 603.6a / ruling 181). -/
def commitEnteringAttackItems (g : Game)
    (chosen : Array (EnteringAttackItem × Option AttackTarget))
    (cause : Option EventCause := none)
    (resetRecent : Bool := true)
    (postEntries : Array (ObjectId × PlayerId × String × List EnterMod × EnteringAttackLog) := #[])
    (preBattlefield : Option (Array GameObject) := none)
    (fromEventIdx? : Option Nat := none) : Game :=
  let hasTokens := chosen.any (fun | (.token .., _) => true | _ => false)
  if hasTokens then
    match chosen[0]? with
    | some (EnteringAttackItem.token controller .., _) =>
      if !g.stillInGame controller then
        let g := if g.stagedAttackTokenBatches.isEmpty then g else g.change (.stagedAttackTokenBatches #[])
        let g := if resetRecent then g.change (.recentTokenIds #[]) else g
        g.logMsg "no token is created (CR 800.4b)"
      else
        let staged := g.stagedAttackTokenBatches
        let g := if staged.isEmpty then g else g.change (.stagedAttackTokenBatches #[])
        let g := if g.continuations.isEmpty && resetRecent then g.change (.pushContinuationFrame {}) else g
        let g := if resetRecent then g.change (.recentTokenIds #[]) else g
        let outerCont? := g.pendingReplacement
        let g := if outerCont?.isSome then g.change (.pendingReplacement none) else g
        let g :=
          if !staged.isEmpty then
            let n := min staged.size chosen.size
            let finalBatches : Array ProposedTokenBatch := (List.range n).toArray.map fun i =>
              let b := staged[i]!
              let atkTgt := chosen[i]!.2
              { b with
                attacking := atkTgt.isSome
                attackingTarget := atkTgt }
            let startEventIdx := g.events.size
            let g :=
              g.withBatch cause fun g =>
                (g.createTokenBatches finalBatches (recordRecent := true) (cause := cause)).1
            if let .chooseReplacement .. := g.pending then
              g.chainPendingReplacement (.finishPostStep (.logCreatedTokensSummary controller startEventIdx))
            else
              g.logCreatedTokensSummary controller startEventIdx
          else
            let initialBatches : Array ProposedTokenBatch := chosen.filterMap fun (item, atkTgt) =>
              match item with
              | .token ctrl kind tapped _ _ =>
                (g.resolveTokenPrinted? kind (controller := ctrl)).map fun printed => {
                  controller := ctrl
                  printed
                  count := 1
                  tapped := tapped
                  attacking := atkTgt.isSome
                  attackingTarget := atkTgt
                  cause := cause
                }
              | _ => none
            let (batches, applied, choice?) := g.replaceTokenBatchesChoice initialBatches
            match choice? with
            | some (chooser, choices) =>
              g.promptChooseReplacement chooser choices
                (.commitEnteringAttackItems chosen cause false)
            | none =>
              let g := g.consumeReplacementOrder applied
              let expanded := batches.foldl (fun acc b =>
                Id.run do
                  let mut acc := acc
                  for _ in [0:b.count] do
                    acc := acc.push { b with count := 1 }
                  return acc) #[]
              let startEventIdx := g.events.size
              let g :=
                g.withBatch cause fun g =>
                  (g.createTokenBatches expanded (recordRecent := true) (cause := cause)).1
              if let .chooseReplacement .. := g.pending then
                g.chainPendingReplacement (.finishPostStep (.logCreatedTokensSummary controller startEventIdx))
              else
                g.logCreatedTokensSummary controller startEventIdx
        match outerCont? with
        | some outer => g.chainPendingReplacement outer
        | none => g
    | _ => g
  else
    let outerCont? := g.pendingReplacement
    let g := if outerCont?.isSome then g.change (.pendingReplacement none) else g
    let deferPfe := chosen.size > 1 || fromEventIdx?.isSome
    let loopFromIdx := fromEventIdx?.getD g.events.size
    let g :=
      g.withBatch cause fun g => Id.run do
        let preBf := preBattlefield.getD g.battlefield
        let mut g := g
        let mut entries := postEntries
        for i in [0:chosen.size] do
          let (item, atkTgt) := chosen[i]!
          match item with
          | .token .. => pure ()
          | .card cardId enteringController effectController tapped returnedAsArtifact extraEntersWith mods logKind _ =>
            if let some o := g.findObject? cardId then
              let (g', _) := g.putOntoBattlefield o.id enteringController (tapped := tapped)
                (attacking := atkTgt.isSome) (attackingTarget := atkTgt)
                (returnedAsArtifact := returnedAsArtifact)
                (extraEntersWith := extraEntersWith)
                (enterMods := mods.toArray)
                (preBattlefield := some preBf)
                (cause := cause)
                (deferPlayFromExileLogs := deferPfe)
              g := g'
              entries := entries.push (o.id, effectController, g.name o, mods, logKind)
              if let .chooseReplacement .. := g.pending then
                let rem := chosen.extract (i + 1) chosen.size
                if !rem.isEmpty then
                  g := g.chainPendingReplacement
                    (.commitEnteringAttackItems rem cause false entries (some preBf)
                      (if deferPfe then some loopFromIdx else none))
                else
                  g := g.chainPendingReplacement
                    (.finishEnteringAttackCards entries cause (if deferPfe then some loopFromIdx else none))
                return g
        return g.finishEnteringAttackCards entries cause (if deferPfe then some loopFromIdx else none)
    let g :=
      match outerCont? with
      | some outer => g.chainPendingReplacement outer
      | none => g
    if g.currentBatch.isNone && g.pending == .none && g.pendingReplacement.isNone then
      g.promptTriggerTargetsIfNeeded
    else g

/-- Have each item's controller choose what it enters attacking when multiple
legal attack targets exist (`options.size > 1`), then create the tokens or put
the cards onto the battlefield already attacking their chosen targets (CR 508.4
/ ruling 181). When no item requires a choice, commits immediately. -/
def promptEnteringAttackItems (g : Game) (items : Array EnteringAttackItem)
    (cause : Option EventCause := none) : Game :=
  if items.isEmpty then g
  else
    let (rest, chosen) := advanceFixedEnteringAttackItems items #[]
    match rest[0]? with
    | some first =>
      let ctrl := first.controller
      let nm := g.enteringAttackItemName first
      g.beginResolutionChoice ctrl (.chooseEnteringAttackTarget rest chosen cause)
        s!"{(g.player ctrl).name} chooses what {nm} enters attacking"
    | none =>
      g.commitEnteringAttackItems chosen cause

/-- Return a graveyard creature tapped and attacking with a finality
counter (Grim Reaper). -/
def returnFromGyTappedAttackingFinality (g : Game) (controller : PlayerId)
    (cardId : ObjectId)
    (attackingTarget : Option AttackTarget := none) : Game :=
  match g.findObject? cardId with
  | none => g.logMsg "The target is no longer in the graveyard"
  | some o =>
    if !(isDiscardableCard o && g.isCreature o && o.zone == .graveyard controller) then
      g.logMsg "The target is no longer a creature card in your graveyard"
    else
      let options :=
        match attackingTarget.bind (fun tgt => g.resolveEnteringAttackTarget? controller true (some tgt)) with
        | some tgt => #[tgt]
        | none => g.legalEnteringAttackTargets controller
      let (g, c) := g.allocDelayedCause (some controller)
      let item := EnteringAttackItem.card o.id controller controller true false
        #[(.finality, 1)] [] .grimReaper options
      g.promptEnteringAttackItems #[item] (cause := some c)

/-- Whether a reflexive triggered ability is on the stack. -/
def hasModeledReflexiveOnStack (g : Game) : Bool :=
  g.stack.any (fun e =>
    ((g.findObject? e.objectId).map (·.isReflexive)).getD false)

/-- Merge subtype names without duplicates. -/
def mergeSubtypes (xs : Array String) (ys : Array CardSubtype) : Array String :=
  ys.foldl (fun acc y => if acc.any (· == y.englishName) then acc else acc.push y.englishName) xs

/-- `o` becomes a copy of `src`'s copiable values. The permanent does not
enter or leave the battlefield (MSH 322 / 326 / 329 / 330). Counters,
attachments, and status are unchanged. If `src` is already a copy, `o`
copies whatever `src` copied (MSH 194 / 198 / 199 / 201). -/
def becomeCopyOf (g : Game) (o : GameObject) (src : GameObject)
    (untilEot := false) (untilNextTurn := false)
    (untilSourceLeaves : Option ObjectId := none)
    (nextTurnOf : Option PlayerId := none)
    (exceptName : Option String := none)
    (addSupertypes : Array Supertype := #[])
    (removeSupertypes : Array Supertype := #[])
    (addTypes : Array CardType := #[])
    (addSubtypes : Array CardSubtype := #[])
    (setPT : Option (Int × Int) := none)
    (addVigilance := false) (replaceCreatureLine := false) : Game :=
  let origName := g.name o
  let printed0 := { g.copiableValues src with isToken := o.printed.isToken }
  let types :=
    if replaceCreatureLine then #[.creature]
    else
      addTypes.foldl
        (fun acc t => if acc.any (· == t) then acc else acc.push t)
        printed0.types
  let supertypes :=
    let kept := printed0.supertypes.filter (fun s => !removeSupertypes.any (· == s))
    addSupertypes.foldl
      (fun acc s => if acc.any (· == s) then acc else acc.push s)
      kept
  let printed : CardDef :=
    { printed0 with
      name := exceptName.getD printed0.name
      types
      subtypes :=
        if replaceCreatureLine then addSubtypes.map CardSubtype.englishName
        else mergeSubtypes printed0.subtypes addSubtypes
      supertypes
      power :=
        match setPT with
        | some (p, _) => some (.fixed p)
        | none => printed0.power
      toughness :=
        match setPT with
        | some (_, t) => some (.fixed t)
        | none => printed0.toughness
      keywords :=
        if addVigilance then KeywordAbility.add printed0.keywords Keyword.vigilance
        else printed0.keywords }
  let turnPlayer :=
    nextTurnOf.orElse (fun _ =>
      if untilNextTurn then (g.controllerOf o).orElse (fun _ => some o.owner) else none)
  let g := g.createEffect (.copy o.id printed untilEot untilNextTurn untilSourceLeaves turnPlayer)
  g.logMsg s!"{origName} becomes a copy of {printed0.name}"

/-- Copy an activated or triggered ability on the stack, returning the new
copy's `ObjectId` if created (CR 707.10 / 800.4d). The copy is not cast or
activated (MSH 34 / 40 / 66) and uses the same source and X
(MSH 47 / 302 / 303). -/
def copyStackAbilityWithId (g : Game) (src : GameObject) (controller : PlayerId) :
    Game × Option ObjectId :=
  if !g.stillInGame controller then
    (g.logMsg s!"A copy of {g.name src} is not created (CR 800.4d)", none)
  else
    let copyId : ObjectId := ⟨g.nextObjectId⟩
    let copySnap : EventObject := {
      (g.snapshot src) with
      id := some copyId
      owner := controller
      controller := some controller
      zone := .stack
      isCopy := true
      isCommander := false
    }
    let g := g.record (GameEvent.stackObjectCopied g.turnNumber src.id copySnap controller
      (cause := g.resolveOptionalCause (g.resolvingOneShotCause controller (some src.id))
        (fallbackSrc := some src.id) (fallbackCtrl := some controller)))
    (g.logMsg s!"A copy of {g.name src} is created", some copyId)

/-- Copy an activated or triggered ability on the stack. -/
def copyStackAbility (g : Game) (src : GameObject) (controller : PlayerId) : Game :=
  (g.copyStackAbilityWithId src controller).1

/-- Reveal `p`'s hand (Cloak and Dagger; MSH 132 / 225). -/
def revealHand (g : Game) (p : PlayerId) (recordEvent : Bool := true) : Game :=
  let hand := g.discardableHandIds p
  let g :=
    if recordEvent && !hand.isEmpty then
      g.record (GameEvent.revealed g.turnNumber p hand
        (cause := some (g.resolvingOrRuleCause p)))
    else g
  let names :=
    hand.foldl (fun acc id =>
      match g.findObject? id with
      | some o => if acc == "" then g.name o else s!"{acc}, {g.name o}"
      | none => acc) ""
  g.logMsg s!"{(g.player p).name} reveals their hand ({names})"

/-- Cards in `p`'s hand that a “reveal your hand, you choose” effect may pick. -/
def revealedHandChoices (g : Game) (p : PlayerId) (permanentOnly : Bool) : Array ObjectId :=
  (g.player p).hand.filter (fun id =>
    match g.findObject? id with
    | some o =>
      isDiscardableCard o && !g.isLand o && (!permanentOnly || g.isPermanentCard o)
    | none => false)

/-- `victim` reveals their hand and `chooser` picks a card for them to discard. -/
def beginRevealDiscard (g : Game) (chooser victim : PlayerId) (permanentOnly : Bool) : Game :=
  let g := g.revealHand victim
  if (g.revealedHandChoices victim permanentOnly).isEmpty then
    let what := if permanentOnly then "nonland permanent card" else "nonland card"
    g.logMsg s!"{(g.player victim).name} has no {what} to discard"
  else
    g.beginResolutionChoice chooser (.discardFromRevealedHand victim permanentOnly)
      s!"{(g.player chooser).name} chooses a card from {(g.player victim).name}'s hand"

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

/-- All CR 603.4 / 608.2a intervening-“if” conditions rechecked on trigger
resolution before pushing `resolutionFinish`. -/
def triggerInterveningHolds (g : Game) (controller : PlayerId)
    (ab : TriggeredAbility) (sourceId : Option ObjectId)
    (targets : Array Target := #[]) (_lastKnownPower : Option Int := none)
    (triggerCauseId : Option ObjectId := none)
    (triggerCauseStatus : Option Status := none) : Bool :=
  match ab.interveningIf? with
  | none => true
  | some cond =>
    let src := sourceId.bind g.damageSourceById?
    let cid? :=
      triggerCauseId.orElse fun _ =>
        match targets[0]? with
        | some (Target.permanent id) | some (Target.card id) => some id
        | _ => none
    let cause :=
      match cid? with
      | none => none
      | some cid =>
        match g.damageSourceById? cid with
        | some o =>
          match triggerCauseStatus with
          | some st =>
            if o.isOnBattlefield then some o else some { o with status := st }
          | none => some o
        | none => none
    g.evalTriggerCond controller src cause cond

/-- Reveal creature cards exiled by Synthetic Destiny at the end step. -/
def applyOneDelayedSynthetic (g : Game) (who : PlayerId) (n : Nat) (cause : EventCause) : Game :=
  let (g, hits, rest) := g.revealUntilCards who (fun c => (g.baseCard c).isCreature) n (cause := some cause)
  let g := g.putHitsToBattlefield who hits (cause := some cause)
  if let .chooseReplacement .. := g.pending then
    g.chainPendingReplacement (.shuffleThen who .none)
  else
    g.restBottomCards who rest true (cause := some cause)

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
      if (g.discardableHandIds controller).isEmpty then
        g := g.draw controller 1
      else
        g := g.beginResolutionChoice controller .discardThenDraw
          s!"{(g.player controller).name} discards a card, then draws a card"
    if let .chooseReplacement .. := g.pending then
      let rem := modes.extract (k + 1) modes.size
      if !rem.isEmpty then
        g := g.chainPendingReplacement
          (.finishPostStep (.hawkeyeArrows controller rem targets idx sourceId))
      return g
  return g

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
          isDiscardableCard o &&
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
      isDiscardableCard o && g.isArtifact o && g.isCreature o && g.objectManaValue o ≤ x
    let lib := (g.player p).library.filter (fun id => (g.findObject? id).any ok)
    let gy := (g.player p).graveyard.filter (fun id => (g.findObject? id).any ok)
    if lib.isEmpty && gy.isEmpty then
      let g := g.record (GameEvent.searched g.turnNumber p p #[]
        (cause := some (g.resolvingOrRuleCause p)))
      (g.logMsg s!"{(g.player p).name} finds no artifact creature card").shuffleThen p .none
    else
      g.beginResolutionChoice p (.visionQuestZones lib gy x)
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

end Game
end Mtg.Engine
