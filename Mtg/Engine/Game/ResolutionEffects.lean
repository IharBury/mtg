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
      -- CR 601.2b–c / 115.1 / 733.1: a spell that can't announce a legal target (kicked
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

/-- Put an artifact from hand onto the battlefield.
`.«if» (.atLeast (.count .putEquipment) (.fixed 1)) (.attach .putArtifact .notedHost)` attaches it when it is
Equipment. -/
def choosePutArtifactFromHand (g : Game) (p : PlayerId) (cardId : ObjectId) :
    Except String Game := do
  match g.pending with
  | .mayPutArtifactFromHand q hostId =>
    if p != q then
      throw s!"Only {(g.player q).name} may put an artifact onto the battlefield"
    let some o := g.findObject? cardId | throw "no such object"
    if o.zone != .hand p then
      throw s!"{g.name o} is not in your hand"
    if !g.isArtifact o then
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
          let g := g.afterPermanentEnters entered
          if let some hid := hostId then g.change (.putArtifactThisWay (some (newId, hid))) else g
        else g
    return match outerCont? with
      | some outer => g.chainPendingReplacement outer
      | none => g
  | _ => throw "Not time to put an artifact from your hand"

/-- True when at least one card was milled by a player in `opponents` in
`g.events[startIdx:]` (CR 701.17a / 701.17c, including zone-redirected mills). -/
def anyOpponentMilledSince (g : Game) (opponents : Array PlayerId) (startIdx : Nat) : Bool :=
  Id.run do
    for i in [startIdx : g.events.size] do
      match g.events[i]!.change with
      | .rules (.zone (.moved _ after (.library pid) toZone .mill _ _ _)) =>
        if opponents.contains pid && toZone != .library pid && after.owner == pid then
          return true
      | _ => pure ()
    return false

/-- Mill opponents without returning a reflexive-trigger flag, deferring across
any open `Pending.chooseReplacement` pause. -/
def millOpponentsOnly (g : Game) (opponents : Array PlayerId) (n : Nat)
    (cause : Option EventCause := none) : Game :=
  if let .chooseReplacement .. := g.pending then
    g.chainPendingReplacement (.finishPostStep (.millOpponentsOnly opponents n cause))
  else
    g.withBatch cause fun g =>
      opponents.foldl (fun acc pid => acc.mill pid n (cause := cause)) g

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
            let g := g.createEffect (.keywordsUntilEot cur.id Keyword.lifelink) (cause := cause)
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
    (cause : Option EventCause := none) : Game :=
  let fallbackCtrl :=
    (sourceId.bind g.findObject?).bind (fun src => (g.controllerOf src).orElse (fun _ => some src.owner))
  let (g, linkCause) :=
    match cause with
    | some c => (g, c)
    | none => g.allocDelayedCause fallbackCtrl sourceId
  let (g, _) := g.move o.id .exile none (cause := some linkCause)
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
    (pendingLog : Option (ObjectId × Zone) := none) : Game := Id.run do
  if let .chooseReplacement .. := g.pending then
    return g.chainPendingReplacement
      (.returnLinkedExileLoop remainingIds cause enteredFromIds preBattlefield pendingLog)
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
          let (g', _) := g.move id (.hand p) none (cause := cause)
          if let .chooseReplacement .. := g'.pending then
            let rem := remainingIds.extract (i + 1) remainingIds.size
            return g'.chainPendingReplacement
              (.returnLinkedExileLoop rem cause entered (some preBf) (some (id, .hand p)))
          if let some moved := g'.followMovedToZone? id (· == .hand p) then
            g := g'.logMsg s!"{g'.name moved} returns to {(g'.player p).name}'s hand"
          else
            g := g'
        | some (.graveyard p) =>
          let (g', _) := g.move id (.graveyard p) none (cause := cause)
          if let .chooseReplacement .. := g'.pending then
            let rem := remainingIds.extract (i + 1) remainingIds.size
            return g'.chainPendingReplacement
              (.returnLinkedExileLoop rem cause entered (some preBf) (some (id, .graveyard p)))
          if let some moved := g'.followMovedToZone? id (· == .graveyard p) then
            g := g'.logMsg s!"{g'.name moved} returns to {(g'.player p).name}'s graveyard"
          else
            g := g'
        | _ =>
          let (g', _) := g.move id .battlefield (some owner)
            (preBattlefield := some preBf) (cause := cause)
          g := g'
          entered := entered.push id
          if let .chooseReplacement .. := g.pending then
            let rem := remainingIds.extract (i + 1) remainingIds.size
            return g.chainPendingReplacement
              (.returnLinkedExileLoop rem cause entered (some preBf) none)
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
            (.returnLinkedExileLoop #[] cause remEntered (some preBf) none)
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

/-- Named MSH tokens that carry extra rules text. -/
def zabuToken : CardDef :=
  { (creatureToken "Zabu" #[.cat] 2 2 (some .green)) with
    supertypes := #[.legendary]
    triggeredAbilities := #[.onLandYouControlEntersPlusOnePlusOne] }

def redwingToken : CardDef :=
  { (creatureToken "Redwing" #[.bird, .scout] 1 1 (some .blue) Keyword.flying) with
    supertypes := #[.legendary]
    triggeredAbilities := #[.onAttackScry 1] }

def theVoidToken : CardDef :=
  { (creatureToken "The Void" #[.horror, .villain] 5 5 (some .black)
      ((Keyword.flying).merge Keyword.indestructible)) with
    supertypes := #[.legendary]
    staticAbilities := #[.attacksEachCombatIfAble] }

def galactusAttackTrigger : Effect := {
  targeting := .of (.filtered { noun := "target land", types := #[.land] })
  resolution := .onPermanent .destroy
  phrase := "Whenever Galactus attacks, destroy target land."
}

def galactusToken : CardDef :=
  { (creatureToken "Galactus" #[.elder, .alien] 16 16 (some .black)
      ((Keyword.flying).merge Keyword.trample)) with
    supertypes := #[.legendary]
    triggeredAbilities := #[.triggered .attack galactusAttackTrigger] }

def tigerGodToken : CardDef :=
  { (creatureToken "The Tiger God" #[.cat, .god] 4 4 (some .green)) with
    supertypes := #[.legendary]
    staticAbilities := #[.cantBeBlockedByMoreThan 1] }

def sturdyShieldToken : CardDef :=
  { name := "Sturdy Shield"
    types := #[.artifact]
    subtypes := #["Equipment"]
    staticAbilities := #[.equippedCreatureGets 1 2]
    activatedAbilities := #[
      { cost := { mana := ManaCost.ofGeneric 2 }
        effect := Effect.attachToTargetCreatureYouControl
        onlyAsSorcery := true }]
    isToken := true }

def createNamedToken (g : Game) (controller : PlayerId) (printed : CardDef) : Game :=
  let (g, _) := g.createToken controller printed
  g

/-- Run `f` if the source is still on the battlefield; otherwise log the same
`missing` message whether the source is gone or was never found. -/
def withSourceStillOnBattlefield (g : Game) (sourceId : Option ObjectId)
    (f : Game → GameObject → Game)
    (missing := "The source has left the battlefield. Nothing is exiled.") : Game :=
  g.withSourceOnBattlefield sourceId f missing (leftMsg := some missing)

/-- Increment the source's plan counter if still on the battlefield (setting
`skipTriggerSequenceRest` when absent), deferring across any open
`Pending.chooseReplacement` pause. -/
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
        g.change (.skipTriggerSequenceRest true)
          |>.logMsg s!"{g.name o} is no longer on the battlefield"
    | none =>
      g.change (.skipTriggerSequenceRest true)
        |>.logMsg "The ability's source is no longer in play"

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
  let departedCount? (sid : ObjectId) : Option Nat :=
    match g.events.findSomeRev? (fun e =>
      match e.change with
      | .rules (.zone (.moved before _ .battlefield _ _ _ _ _)) =>
        if before.id == some sid then some e.batch else none
      | _ => none) with
    | none => none
    | some depBatch =>
      some <| g.events.foldl (fun acc e =>
        if e.batch == depBatch && e.cause? == some (.gameRule .unattachOnHostLeave) then
          match e.change with
          | .rules (.permanent (.unattached att hostId)) =>
            if hostId == sid && att.subtypes.contains .equipment then acc + 1 else acc
          | _ => acc
        else acc) 0
  match sourceId with
  | some sid =>
    match g.findObject? sid with
    | some o =>
      if o.zone == .battlefield then g.attachedEquipmentCount o
      else (departedCount? sid).getD (lastKnownPower.getD (0 : Int)).toNat
    | none => (departedCount? sid).getD (lastKnownPower.getD (0 : Int)).toNat
  | none => (lastKnownPower.getD (0 : Int)).toNat

/-- `sourcePowerAtResolution` as a `Nat`. -/
def sourcePowerNatAtResolution (g : Game) (sourceId : Option ObjectId)
    (lastKnownPower : Option Int := none) : Nat :=
  (g.sourcePowerAtResolution sourceId lastKnownPower).toNat

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
    (pendingFromId : Option ObjectId := none) : Game := Id.run do
  let fmtMsg (g : Game) (ownerName cardName : String) : String :=
    if mayCastStyle then
      s!"{ownerName} exiles {cardName}; {(g.player caster).name} may cast it"
    else
      s!"{ownerName} exiles {cardName} and may play it this turn"
  if let .chooseReplacement .. := g.pending then
    return g.chainPendingReplacement
      (.finishPostStep (.exileTopForPlayLoop fromPlayer caster remaining mayCastStyle cause? pendingFromId))
  let mut g := g
  if let some fid := pendingFromId then
    if let some moved := g.followMovedToZone? fid (· == .exile) then
      if g.stillInGame caster then
        g := g.createEffect (.playPermission moved.id { player := caster }) (cause := cause?)
      g := g.logMsg (fmtMsg g (g.player fromPlayer).name (g.name moved))
  if !g.stillInGame fromPlayer || !g.stillInGame caster then
    return g
  for i in [0:remaining] do
    if !g.stillInGame fromPlayer || !g.stillInGame caster then
      return g
    let pl := g.player fromPlayer
    if pl.library.isEmpty then
      g := g.logMsg s!"{pl.name} has no cards in their library to exile"
    else
      let top := pl.library.back!
      let cardName := g.name (g.object! top)
      let (g', _) := g.move top .exile none (cause := cause?)
      g := g'
      if let .chooseReplacement .. := g.pending then
        let rem := remaining - (i + 1)
        return g.chainPendingReplacement
          (.finishPostStep (.exileTopForPlayLoop fromPlayer caster rem mayCastStyle cause? (some top)))
      if let some moved := g.followMovedToZone? top (· == .exile) then
        if g.stillInGame caster then
          g := g.createEffect (.playPermission moved.id { player := caster }) (cause := cause?)
        g := g.logMsg (fmtMsg g pl.name cardName)
  return g

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
    match g.findObject? sid with
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

/-- Queue `followup` as a reflexive triggered ability via `WaitingTrigger` +
`recordReflexiveTrigger` (`TriggerQueueEvent.triggered`, CR 603.3c–d / 603.12).
Flushes immediately only when invoked outside an active resolution/batch with
`deferToPriority == false`. -/
def queueFollowupReflexive (g : Game) (controller : PlayerId) (sourceId : Option ObjectId)
    (followup : TriggeredAbility.TriggerResolution)
    (deferToPriority : Bool := false) : Game :=
  if !g.stillInGame controller then g
  else
    let src := g.abilitySourceFor controller sourceId
    let effect : Effect := {
      resolution := .draw 0
      phrase := "when you do, that ability triggers" }
    let marker : TriggeredAbility := .triggered .enter effect {}
    let eventCause := g.resolveOptionalCause none (fallbackSrc := sourceId) (fallbackCtrl := some controller)
    let wt : WaitingTrigger := {
      controller
      source := src
      ability := marker
      event := .leaving
      checked := true
      eventCause := eventCause
      reflexiveResolution := some followup
    }
    let g := g.recordReflexiveTrigger wt
    if deferToPriority || g.resolvingAbility.isSome || g.resolvingSpell.isSome || g.currentBatch.isSome then g
    else g.putTriggerBatch #[wt]

/-- Queue a reflexive triggered ability (“When you do, …”) with `effect` via
`WaitingTrigger` + `recordReflexiveTrigger` (`TriggerQueueEvent.triggered`,
CR 603.3c–d / 603.12). Its targets are chosen when put on the stack. -/
def putReflexiveTrigger (g : Game) (controller : PlayerId) (sourceId : Option ObjectId)
    (effect : Effect) (deferToPriority : Bool := false)
    (causeIds : Array ObjectId := #[]) : Game :=
  if !g.stillInGame controller then g
  else
    let src := g.abilitySourceFor controller sourceId
    let marker : TriggeredAbility := .triggered .enter effect {}
    let eventCause := g.resolveOptionalCause none (fallbackSrc := sourceId) (fallbackCtrl := some controller)
    let wt : WaitingTrigger := {
      controller
      source := src
      ability := marker
      event := .entering
      causeIds := causeIds
      checked := true
      eventCause := eventCause
      abilityEffect := some effect
    }
    let g := g.recordReflexiveTrigger wt
    if deferToPriority || g.resolvingAbility.isSome || g.resolvingSpell.isSome || g.currentBatch.isSome then g
    else g.putTriggerBatch #[wt]

/-- The reflexive triggered ability `kind` of an MSH card, with its targets
(MSH 359–369). -/
def modeledReflexiveEffect (kind : TriggeredAbility.TriggerReflexiveKind) (paid : Nat) : Effect :=
  let base : Effect := { resolution := .mshReflexive kind paid }
  let creature (f : TargetFilter) : TargetFilter := { f with types := #[.creature] }
  match kind with
  | .grantIndestructible =>
    { base with
      targeting := .of (.filtered (creature
        { noun := "another target nonattacking creature you control", controller := .you
          another := true, nonattacking := true }))
      phrase := "Another target nonattacking creature you control gains indestructible until end of turn" }
  | .dealTwoDamage =>
    { base with targeting := .of .playerOrCreature, phrase := "This deals 2 damage to any target" }
  | .trickArrows => base
  | .indestructibleCounter =>
    { base with targeting := .of .creatureYouControl
                phrase := "Put an indestructible counter on target creature you control" }
  | .controlOpponent =>
    { base with targeting := .of .opponent
                phrase := "You control target opponent during their next turn" }
  | .exileTopFive =>
    { base with targeting := .of .opponent
                phrase := "Target opponent exiles the top five cards of their library" }
  | .returnAttacking =>
    { base with targeting := .of .creatureCardInYourGraveyard
                phrase := "Return target creature card from your graveyard to the battlefield tapped and attacking with a finality counter on it" }
  | .destroyOppNonland =>
    { base with targeting := .of .oppNonland
                phrase := "Destroy target nonland permanent an opponent controls" }
  | .countersDamage =>
    { base with
      targeting := .of (.filtered { noun := "any other target", zone := .anyTarget, another := true })
      phrase := "This deals damage equal to the number of +1/+1 counters on it to any other target" }
  | .hasteUnblockable =>
    { base with
      targeting := .of (.filtered (creature { noun := "target creature with haste", withHaste := true }))
      phrase := "Target creature with haste can't be blocked this turn except by creatures with haste" }
  | .divideSevenDamage =>
    { base with targeting := .of .playerOrCreature, dividedDamage := some (7, 2)
                phrase := "It deals 7 damage divided as you choose among one or two targets" }
  | .returnInstants =>
    { base with
      targeting := .of (.filtered
        { noun := "up to two target instant and/or sorcery cards from your graveyard"
          zone := .yourGraveyard, types := #[.instant, .sorcery] })
      maxTargets := 2, allowsZeroTargets := true
      phrase := "Return up to two target instant and/or sorcery cards from your graveyard to your hand" }
  | .plusOne =>
    { base with targeting := .of .creature, phrase := "Put a +1/+1 counter on target creature" }

/-- Put MSH reflexive ability `kind` on the stack; its targets are chosen now
(CR 603.12 / MSH 359–369). -/
def queueModeledReflexive (g : Game) (controller : PlayerId) (sourceId : Option ObjectId)
    (kind : TriggeredAbility.TriggerReflexiveKind) (paid : Nat := 0) : Game :=
  g.putReflexiveTrigger controller sourceId (modeledReflexiveEffect kind paid)

/-- Offer to pay `cost` up to `maxTimes` times; when the player does, MSH
reflexive ability `kind` triggers (MSH 359–369). -/
def offerPayForReflexive (g : Game) (controller : PlayerId) (sourceId : Option ObjectId)
    (cost : Array ManaSymbol) (kind : TriggeredAbility.TriggerReflexiveKind)
    (maxTimes : Nat := 1) : Game :=
  let shown := String.join (cost.toList.map toString)
  let times := if maxTimes > 1 then s!" up to {maxTimes} times" else ""
  g.beginFraChoice controller (.mayPayManaForReflexive cost maxTimes kind sourceId)
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
    g.beginFraChoice caster (.mayCastUpToFromExile spells casts)
      s!"{(g.player caster).name} may cast up to {casts} spells from among the exiled cards without paying their mana costs"

/-- Pause-safe loop for `exileTopMayCastUpTo`, running inside an open batch and
offering up to `casts` free spell casts once all moves complete. -/
def exileTopMayCastUpToLoop (g : Game) (fromPlayer caster : PlayerId)
    (remaining casts : Nat) (cause? : Option EventCause)
    (accIds : Array ObjectId := #[])
    (pendingFromId : Option ObjectId := none) : Game := Id.run do
  if let .chooseReplacement .. := g.pending then
    return g.chainPendingReplacement
      (.finishPostStep (.exileTopMayCastUpToLoop fromPlayer caster remaining casts cause? accIds pendingFromId))
  let mut g := g
  let mut ids := accIds
  if let some fid := pendingFromId then
    if let some moved := g.followMovedToZone? fid (· == .exile) then
      ids := ids.push moved.id
      g := g.logMsg s!"{(g.player fromPlayer).name} exiles {g.name moved}"
  if !g.stillInGame fromPlayer then
    return g
  for i in [0:remaining] do
    if !g.stillInGame fromPlayer then
      return g
    let pl := g.player fromPlayer
    if pl.library.isEmpty then
      g := g.logMsg s!"{pl.name} has no cards in their library to exile"
    else
      let top := pl.library.back!
      let name := g.name (g.object! top)
      let (g', _) := g.move top .exile none (cause := cause?)
      g := g'
      if let .chooseReplacement .. := g.pending then
        let rem := remaining - (i + 1)
        return g.chainPendingReplacement
          (.finishPostStep (.exileTopMayCastUpToLoop fromPlayer caster rem casts cause? ids (some top)))
      if let some moved := g.followMovedToZone? top (· == .exile) then
        ids := ids.push moved.id
        g := g.logMsg s!"{pl.name} exiles {name}"
  return g

/-- Offer up to `casts` free casts from `ids` after `exileTopMayCastUpTo`'s
exile batch has closed. -/
def finishExileTopMayCastUpToOffer (g : Game) (caster : PlayerId)
    (ids : Array ObjectId) (casts : Nat) : Game :=
  let spells := ids.filter (fun id =>
    (g.findObject? id).any (fun o => o.zone == .exile && !g.isLand o))
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

/-- True when `mods` strips abilities and grants haste, as Hellcat returns. -/
def losesAbilitiesAndHaste (mods : List TriggeredAbility.TriggerEnterWith) : Bool :=
  mods.any (· == .loseAllAbilities) &&
    mods.any (fun m =>
      match m with
      | .keywords k => k.haste
      | _ => false)

/-- Extra enters-with counters specified by `mods`. -/
def enterModsExtraCounters (mods : List TriggeredAbility.TriggerEnterWith) : CounterBag :=
  mods.foldl (fun acc m =>
    match m with
    | .counter .finality n _ => acc.add .finality n
    | .counter kind n true => acc.add kind n
    | _ => acc) #[]

/-- Legal attack targets specified by `mods` as the permanent enters under
`enteringController`'s control (CR 508.4), or `#[]` when `.attacking` is not
in `mods`. -/
def enterModsAttackOptions (g : Game) (enteringController : PlayerId)
    (mods : List TriggeredAbility.TriggerEnterWith) : Array AttackTarget :=
  if mods.any (· == .attacking) then
    g.legalEnteringAttackTargets enteringController
  else #[]

/-- Apply one post-entry counter change to the permanent `id` (enters-with
effects and counters were already pre-seeded and recorded on arrival by
`Movement.move`, CR 122.6 / 614.1c). -/
def applyEnterMod (g : Game) (controller : PlayerId) (id : ObjectId)
    (mod : TriggeredAbility.TriggerEnterWith)
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
    (mods : List TriggeredAbility.TriggerEnterWith)
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
    (postEntries : Array (ObjectId × PlayerId × String × List TriggeredAbility.TriggerEnterWith × EnteringAttackLog))
    (cause : Option EventCause := none) : Game :=
  match postEntries[0]? with
  | none => g
  | some (fromId, effectController, cardName, mods, logKind) =>
    let rest := postEntries.extract 1 postEntries.size
    match g.followMovedToZone? fromId (· == .battlefield) with
    | none => g.finishEnteringAttackCards rest cause
    | some enteredObj =>
      let g := g.finishEnteringAttackCard enteredObj.id effectController cardName mods logKind (cause := cause)
      if rest.isEmpty then g
      else if g.pending != .none then
        g.chainPendingReplacement (.finishEnteringAttackCards rest cause)
      else
        g.finishEnteringAttackCards rest cause

/-- Create the tokens or put the cards in `chosen` onto the battlefield with
their chosen `AttackTarget`s in a single batch, moving all cards onto
`.battlefield` before running enters-with modifications and enters triggers
(CR 508.4 / 603.6a / ruling 181). -/
def commitEnteringAttackItems (g : Game)
    (chosen : Array (EnteringAttackItem × Option AttackTarget))
    (cause : Option EventCause := none)
    (resetRecent : Bool := true)
    (postEntries : Array (ObjectId × PlayerId × String × List TriggeredAbility.TriggerEnterWith × EnteringAttackLog) := #[])
    (preBattlefield : Option (Array GameObject) := none) : Game :=
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
                some {
                  controller := ctrl
                  printed := tokenPrinted kind
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
              g := g'
              entries := entries.push (o.id, effectController, g.name o, mods, logKind)
              if let .chooseReplacement .. := g.pending then
                let rem := chosen.extract (i + 1) chosen.size
                if !rem.isEmpty then
                  g := g.chainPendingReplacement
                    (.commitEnteringAttackItems rem cause false entries (some preBf))
                else
                  g := g.chainPendingReplacement (.finishEnteringAttackCards entries cause)
                return g
        return g.finishEnteringAttackCards entries cause
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
      g.beginFraChoice ctrl (.chooseEnteringAttackTarget rest chosen cause)
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
    if !(g.isCreature o && o.zone == .graveyard controller) then
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

/-- Deal divided damage across `remaining` targets one at a time, pausing across
`Pending.chooseReplacement` so subsequent target legality checks do not run early,
and aggregating CR 702.15b lifelink life gain once after all targets' damage has
been dealt. -/
partial def divideSevenDamageLoop (g : Game) (controller : PlayerId) (kind : EffectTargetKind)
    (remaining : Array (Nat × Target)) (division : Array Nat)
    (sourceId : Option ObjectId) (startEventIdx : Option Nat := none) : Game :=
  if let .chooseReplacement .. := g.pending then
    g.chainPendingReplacement
      (.finishPostStep (.divideSevenDamageLoop controller kind remaining division sourceId startEventIdx))
  else if startEventIdx.isNone && g.currentBatch.isNone && !remaining.isEmpty then
    let sIdx := g.events.size
    g.withBatch (g.resolvingBatchCause controller sourceId) fun g =>
      g.divideSevenDamageLoop controller kind remaining division sourceId (some sIdx)
  else
    let sIdx := startEventIdx.getD g.events.size
    let batchCause :=
      (g.currentBatch.bind (·.2)).orElse (fun _ => g.resolvingBatchCause controller sourceId)
    match remaining[0]? with
    | none =>
      g.applyAggregatedLifelinkSince sIdx (cause := batchCause)
    | some (i, tgt) =>
      let rest := remaining.extract 1 remaining.size
      let legal := g.legalTargetsForKind controller kind sourceId
      let g :=
        if legal.contains tgt then
          g.dealDamageToTarget tgt (Int.ofNat (division[i]?.getD 0))
            (source := sourceId.bind g.damageSourceById?) (cause := batchCause)
            (suppressLifelink := true)
        else
          g.illegalAbilityTarget tgt
      if let .chooseReplacement .. := g.pending then
        g.chainPendingReplacement
          (.finishPostStep (.divideSevenDamageLoop controller kind rest division sourceId (some sIdx)))
      else
        g.divideSevenDamageLoop controller kind rest division sourceId (some sIdx)

/-- Return targeted graveyard instant cards to `controller`'s hand one at a time,
pausing across `Pending.chooseReplacement` before checking subsequent targets. -/
partial def returnInstantsLoop (g : Game) (controller : PlayerId) (kind : EffectTargetKind)
    (remaining : Array Target) (sourceId : Option ObjectId) : Game :=
  match remaining[0]? with
  | none => g
  | some tgt =>
    let rest := remaining.extract 1 remaining.size
    let legal := g.legalTargetsForKind controller kind sourceId
    let g :=
      match tgt with
      | Target.card id =>
        if legal.contains tgt then g.returnToHand id controller else g.illegalAbilityTarget tgt
      | _ => g
    if rest.isEmpty then g
    else if let .chooseReplacement .. := g.pending then
      g.chainPendingReplacement
        (.finishPostStep (.returnInstantsLoop controller kind rest sourceId))
    else
      g.returnInstantsLoop controller kind rest sourceId

/-- Resolve MSH reflexive ability `kind` with its announced targets. A target
that is no longer legal is skipped (MSH 125). -/
def resolveModeledReflexive (g : Game) (controller : PlayerId) (sourceId : Option ObjectId)
    (kind : TriggeredAbility.TriggerReflexiveKind) (paid : Nat)
    (targets : Array Target) (division : Array Nat := #[]) : Game :=
  let tkind := (modeledReflexiveEffect kind paid).targetKind
  let illegal := some "The target is no longer legal"
  match kind with
  | .grantIndestructible =>
    g.withLegalKindPermanent controller tkind targets
      (fun g o => g.grantUntilEotLogged o Keyword.indestructible) sourceId illegal
  | .dealTwoDamage =>
    g.withLegalKindTarget controller tkind targets
      (fun g tgt => g.dealDamageToTarget tgt 2 (source := sourceId.bind g.damageSourceById?)) sourceId illegal
  | .trickArrows => g
  | .indestructibleCounter =>
    g.withLegalKindPermanent controller tkind targets
      (fun g o => g.addIndestructibleCounter o) sourceId illegal
  | .controlOpponent =>
    g.withLegalKindPlayer controller tkind targets (fun g pid =>
      g.setPlayerControl controller pid (onNextTurn := true))
      sourceId illegal
  | .exileTopFive =>
    g.withLegalKindPlayer controller tkind targets
      (fun g pid => g.exileTopMayCastUpTo pid controller 5 2) sourceId illegal
  | .returnAttacking =>
    g.withLegalKindTarget controller tkind targets (fun g tgt =>
      match tgt with
      | Target.card id | Target.permanent id => g.returnFromGyTappedAttackingFinality controller id
      | _ => g) sourceId illegal
  | .destroyOppNonland =>
    g.withLegalKindPermanent controller tkind targets
      (fun g o => g.destroyPermanent o) sourceId illegal
  | .countersDamage =>
    let counters :=
      match sourceId.bind g.findObject? with
      | some o =>
        if o.isOnBattlefield then o.status.plusOnePlusOne
        else (sourceId.bind g.lastKnownCounterStatus?).map (·.plusOnePlusOne) |>.getD paid
      | none =>
        (sourceId.bind g.lastKnownCounterStatus?).map (·.plusOnePlusOne) |>.getD paid
    g.withLegalKindTarget controller tkind targets
      (fun g tgt => g.dealDamageToTarget tgt (Int.ofNat counters) (source := sourceId.bind g.damageSourceById?))
      sourceId illegal
  | .hasteUnblockable =>
    g.withLegalKindPermanent controller tkind targets
      (fun g o =>
        g.createEffect (.cantBeBlockedExceptByHasteUntilEot o.id)
          |>.logMsg s!"{g.name o} can't be blocked this turn except by creatures with haste")
      sourceId illegal
  | .divideSevenDamage =>
    if targets.isEmpty then g
    else
      let indexed := (List.range targets.size).toArray.map fun i => (i, targets[i]!)
      g.withBatch (g.resolvingBatchCause controller sourceId) fun g =>
        g.divideSevenDamageLoop controller tkind indexed division sourceId
  | .returnInstants =>
    g.withBatch none fun g =>
      g.returnInstantsLoop controller tkind targets sourceId
  | .plusOne =>
    g.withLegalKindPermanent controller tkind targets
      (fun g o => g.addPlusOnePlusOneTo o 1) sourceId illegal

/-- Whether an MSH reflexive ability is on the stack. -/
def hasModeledReflexiveOnStack (g : Game) : Bool :=
  g.stack.any (fun e =>
    match ((g.findObject? e.objectId).bind (·.abilityEffect)).map Effect.resolution with
    | some (Resolution.mshReflexive _ _) | some (Resolution.hawkeyeArrows _) => true
    | _ => false)

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
        | some (p, _) => some p
        | none => printed0.power
      toughness :=
        match setPT with
        | some (_, t) => some t
        | none => printed0.toughness
      keywords :=
        if addVigilance then Keywords.merge printed0.keywords Keyword.vigilance
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
  let hand := (g.player p).hand
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

/-- Exile `sourceId` in its own CR 608.2c batch at the end of `Worlds Within Worlds`. -/
def finishWorldsWithinWorldsExileSelf (g : Game) (sourceId : Option ObjectId) : Game :=
  match sourceId.bind g.findObject? with
  | some src =>
    if src.zone == .exile then g
    else
      g.withBatch none fun g =>
        let (g', _) := g.move src.id .exile none
        if let .chooseReplacement .. := g'.pending then
          g'.chainPendingReplacement (.finishPostStep (.logMovedToExile src.id))
        else if let some moved := g'.followMovedToZone? src.id (· == .exile) then
          g'.logMsg s!"{g'.name moved} is exiled"
        else g'
  | none => g

/-- Move each card in `remainingIds` from `.exile` to its owner's hand inside
the `Worlds Within Worlds` return batch, logging only once each zone change
actually places the card into its owner's hand. -/
def worldsReturnExiledLoop (g : Game) (remainingIds : Array ObjectId)
    (pendingCard : Option (ObjectId × PlayerId) := none) : Game := Id.run do
  if let .chooseReplacement .. := g.pending then
    return g.chainPendingReplacement
      (.finishPostStep (.worldsReturnExiledLoop remainingIds pendingCard))
  let mut g := g
  if let some (fromId, owner) := pendingCard then
    if let some moved := g.followMovedToZone? fromId (· == .hand owner) then
      g := g.logMsg s!"{g.name moved} is returned to its owner's hand"
  for i in [0:remainingIds.size] do
    let nid := remainingIds[i]!
    if let some o := g.findObject? nid then
      if o.zone == .exile then
        let owner := o.owner
        let (g', _) := g.move o.id (.hand owner) none
        g := g'
        if let .chooseReplacement .. := g.pending then
          let rem := remainingIds.extract (i + 1) remainingIds.size
          return g.chainPendingReplacement
            (.finishPostStep (.worldsReturnExiledLoop rem (some (o.id, owner))))
        if let some moved := g.followMovedToZone? o.id (· == .hand owner) then
          g := g.logMsg s!"{g.name moved} is returned to its owner's hand"
  return g

/-- Return exiled cards to their owners' hands and exile `sourceId` in separate
CR 608.2c batches at the end of `finishWorldsWithinWorlds`. -/
def finishWorldsWithinWorldsTail (g : Game) (exiled : Array ObjectId)
    (sourceId : Option ObjectId) : Game :=
  let g :=
    if exiled.isEmpty then g
    else
      g.withBatch none fun g =>
        g.worldsReturnExiledLoop exiled none
  if let .chooseReplacement .. := g.pending then
    g.chainPendingReplacement
      (.finishPostStep (.worldsWithinWorldsExileSelf sourceId))
  else
    g.finishWorldsWithinWorldsExileSelf sourceId

/-- Log arrival on the battlefield for chosen creature cards after
`putToBattlefieldLoop` finishes, then continue `finishWorldsWithinWorldsTail`. -/
def finishWorldsWithinWorldsAfterPut (g : Game) (exiled : Array ObjectId)
    (validChosen : Array (ObjectId × PlayerId × String))
    (sourceId : Option ObjectId) : Game :=
  let g := validChosen.foldl (fun g (cid, owner, name) =>
    if (g.followMovedToZone? cid (· == .battlefield)).isSome then
      g.logMsg s!"{(g.player owner).name} puts {name} onto the battlefield"
    else g) g
  g.finishWorldsWithinWorldsTail exiled sourceId

/-- After every player has chosen, the chosen creature cards enter together,
the exiled cards return to their owners' hands, and the spell is exiled, each
as its own sequential CR 608.2c verb batch. -/
def finishWorldsWithinWorlds (g : Game) (exiled chosen : Array ObjectId)
    (sourceId : Option ObjectId) : Game :=
  let validChosen : Array (ObjectId × PlayerId × String) :=
    chosen.filterMap fun id =>
      match g.findObject? id with
      | some o =>
        if o.zone == .hand o.owner && g.isCreature o then
          some (id, o.owner, g.name o)
        else none
      | none => none
  let validIds := validChosen.map (·.1)
  let g := g.withBatch none fun g =>
    g.putToBattlefieldLoop g.activePlayer validIds (useCardOwner := true)
  if let .chooseReplacement .. := g.pending then
    g.chainPendingReplacement
      (.finishPostStep (.worldsWithinWorldsAfterPut exiled validChosen sourceId))
  else
    g.finishWorldsWithinWorldsAfterPut exiled validChosen sourceId

/-- Ask the next player who has a creature card in hand, in the order given. -/
def offerWorldsCreatures (g : Game) (rest : List PlayerId)
    (exiled chosen : Array ObjectId) (sourceId : Option ObjectId) : Game :=
  match rest with
  | [] => g.finishWorldsWithinWorlds exiled chosen sourceId
  | pid :: more =>
    let eligible :=
      (g.player pid).hand.filter (fun id =>
        (g.findObject? id).any g.isCreature)
    if eligible.isEmpty then
      g.offerWorldsCreatures more exiled chosen sourceId
    else
      g.beginFraChoice pid (.worldsPutCreatures eligible more.toArray exiled chosen sourceId)
        s!"{(g.player pid).name} may put any number of creature cards from their hand onto the battlefield"

/-- Worlds Within Worlds (MSH 96 / ruling 449): exile creatures, then each
player may put any number of creature cards from hand. Those creatures enter
together, the exiled cards return to their owners' hands, then the spell
is exiled. -/
def applyWorldsWithinWorlds (g : Game) (controller : PlayerId)
    (sourceId : Option ObjectId) : Game :=
  let startIdx := g.events.size
  let creatureIds := (g.battlefield.filter (fun o => g.isCreature o)).map (·.id)
  let g := g.withBatch none fun g =>
    g.exilePermanentsLoop creatureIds (logExile := true)
  if let .chooseReplacement .. := g.pending then
    g.chainPendingReplacement
      (.finishPostStep (.offerWorldsCreatures controller startIdx creatureIds sourceId))
  else
    let exiled := creatureIds.filterMap fun id =>
      if g.wasPermanentExiled id startIdx then
        (g.followMovedToZone? id (· == .exile)).map (·.id)
      else none
    let order :=
      let apnap := g.apnapOrder
      if apnap.isEmpty then #[controller]
      else apnap
    g.offerWorldsCreatures order.toList exiled #[] sourceId

end Game
end Mtg.Engine
