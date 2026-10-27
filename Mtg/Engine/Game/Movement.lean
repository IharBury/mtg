import Mtg.Engine.Game.Attachments

/-!
# Zone changes (CR 400)

Exile-instead-of-dying replacement effects (CR 614.6), dying triggers,
`move` — the single zone-change routine — simultaneous moves to the
graveyard, and putting cards onto the battlefield (CR 611.3 / 603.6).
-/

namespace Mtg.Engine
namespace Game

/-- The copy of `srcId`'s prepare spell in exile, if any. -/
def preparedCopyOf? (g : Game) (srcId : ObjectId) : Option GameObject :=
  g.objects.find? (fun o =>
    o.zone == .exile && (o.playPermission.bind (·.prepareSource)) == some srcId)

/-- The exiled copy of `srcId`'s prepare spell ceases to exist. -/
def removePreparedCopy (g : Game) (srcId : ObjectId)
    (cause : Option EventCause := some (.stateBased .copyOutsideStackOrBf)) : Game :=
  match g.preparedCopyOf? srcId with
  | some c => (g.ceaseToExist c.id (cause := cause)).logMsg s!"The copy of {c.name} in exile ceases to exist"
  | none => g

/-- Create the exiled copy of `o`'s prepare spell and grant permission to cast
it while `o` remains prepared (ruling 742). -/
def createPreparedCopy (g : Game) (o : GameObject) (face : AdventureFace)
    (cause : Option EventCause := none) : Game :=
  let p := o.controller.getD o.owner
  let copyId : ObjectId := ⟨g.nextObjectId⟩
  let copyTs := g.timestamp + 1
  let copyObj : GameObject := {
    id := copyId
    printed := face.toCardDef
    owner := p
    zone := .exile
    timestamp := copyTs
  }
  let g := g.record (GameEvent.created g.turnNumber p (g.snapshot copyObj) (cause := cause))
  let g := g.createPrintedStaticEffects (g.object! copyId)
  g.createEffect (.playPermission copyId {
    player := p
    turnEndsRemaining := 0
    whileExiled := true
    prepareSource := some o.id }) (cause := cause)

/-- Ensure the exiled copy of `o`'s prepare spell exists when `o` enters
already prepared (CR 614.1c, ruling 742). -/
def ensurePreparedCopy (g : Game) (o : GameObject) : Game :=
  if !o.status.prepared || (g.preparedCopyOf? o.id).isSome then g
  else
    match o.printed.prepareFace with
    | none => g
    | some face =>
      let g := g.createPreparedCopy o face (cause := some (.gameRule .staticAbility))
      g.logMsg s!"{o.name} becomes prepared. A copy of {face.name} is exiled"

/-- `o` becomes prepared: its controller creates a copy of its prepare spell
in exile and may cast that copy while `o` stays prepared (ruling 742). A
creature without a prepare spell can't become prepared (ruling 747), and a
prepared creature can't become prepared again (ruling 743). Only the printed
prepare spell is copied, so copy exceptions on `o` don't apply (ruling 741). -/
def becomePrepared (g : Game) (o : GameObject) : Game :=
  match o.printed.prepareFace with
  | none => g.logMsg s!"{o.name} has no prepare spell and can't become prepared"
  | some face =>
    if o.status.prepared then g.logMsg s!"{o.name} is already prepared"
    else
      let g := g.createPreparedCopy o face
      let g := g.changeStatus o.id (.prepared true)
      g.logMsg s!"{o.name} becomes prepared. A copy of {face.name} is exiled"

/-- `o` stops being prepared and the copy of its prepare spell in exile
ceases to exist. Nothing happens if it isn't prepared (ruling 737). -/
def unprepare (g : Game) (o : GameObject) : Game :=
  if !o.status.prepared then g
  else
    let g := g.changeStatus o.id (.prepared false)
    (g.removePreparedCopy o.id).logMsg s!"{o.name} is no longer prepared"

/-- True when `o` replaces an opposing creature dying with exile. -/
def exilesOppDeath? (o : GameObject) : Bool :=
  o.printed.exileOppCreaturesInstead ||
    o.staticAbilities.any (fun
      | .exileOppDeathCreateWolf => true
      | .fra .exileOpponentsDyingCreatures => true
      | _ => false)

/-- True when `o` also creates a Wolf after that replacement (Head of the Hunt). -/
def createsWolfOnOppExileDeath? (o : GameObject) : Bool :=
  o.staticAbilities.any (fun
    | .exileOppDeathCreateWolf => true
    | _ => false)

/-- Permanents that exile opposing creatures that would die. Uses the SBA
snapshot when one is locked so a simultaneous death of the source still
applies (CR 614.4 / 614.6). -/
def deathReplacementObjects (g : Game) : Array GameObject :=
  match g.lockedDeathReplacements with
  | some xs => xs
  | none => g.battlefield.filter exilesOppDeath?

/-- Controller of a Head-of-the-Hunt-style replacement, if `dying` is an
opposing creature that would go to a graveyard. -/
def exileInsteadSource? (g : Game) (dying : GameObject) : Option GameObject :=
  g.deathReplacementObjects.find? (fun o =>
    o.id != dying.id &&
      match o.controller, dying.controller with
      | some p, some q => p != q
      | _, _ => false)

/-- Controller of a Head-of-the-Hunt-style replacement, if `dying` is an
opposing creature that would go to a graveyard. -/
def exileInsteadController? (g : Game) (dying : GameObject) : Option PlayerId :=
  (g.exileInsteadSource? dying).bind (·.controller)

/-- CR 614.6: if this death would be replaced with exile, the die event
never happens. -/
def wouldExileInsteadOfDying (g : Game) (dying : GameObject) : Bool :=
  dying.status.untilEotExileIfDies || (g.exileInsteadSource? dying).isSome

/-- `partial` because linked-exile returns recurse into `move` (CR 610.3). -/
partial def move (g : Game) (id : ObjectId) (dest : Zone)
    (controller : Option PlayerId := none)
    (tapped : Bool := false) (summoningSick : Bool := true)
    (attachedTo : Option ObjectId := none) (applyHope : Bool := true)
    (attacking : Bool := false) (attackingWhom : Option PlayerId := none)
    (attackingTarget : Option AttackTarget := none)
    (returnedAsArtifact : Bool := false) (onlyFoodArtifact : Bool := false)
    (nightBack : Bool := false) (wasCast : Option Bool := none)
    (extraEntersWith : CounterBag := #[])
    (verb : Option ZoneVerb := none) (actor : Option PlayerId := none)
    (libraryPosition : Option LibraryPosition := none)
    (cause : Option EventCause := none) : Game × ObjectId :=
  let old := g.object! id
  let isAttacking := attacking || attackingTarget.isSome
  let resolvedAttackTarget : Option AttackTarget :=
    if isAttacking then
      some (attackingTarget.getD (.player (attackingWhom.getD g.defendingPlayer)))
    else none
  -- Power and toughness as this permanent last existed on the battlefield
  -- (CR 113.7a). Captured before attachments and the zone list change.
  let lkiPower :=
    if old.zone == .battlefield then some (g.snapshotPower old) else none
  let lkiToughness :=
    if old.zone == .battlefield then some (g.snapshotToughness old) else none
  let beforeSnap := g.snapshot old
  let discarded :=
    match old.zone, dest with
    | .hand p, .graveyard q => p == q
    | _, _ => false
  let buildArrival (g : Game) (targetZone : Zone) (asOf : Nat) :
      GameObject × CounterBag × Nat × Bool × Bool :=
    let newId : ObjectId := ⟨g.nextObjectId⟩
    let ts := g.timestamp + 1
    let leavingPlay :=
      (old.zone == .battlefield || old.zone == .stack) &&
        targetZone != .battlefield && targetZone != .stack
    let printed :=
      if leavingPlay && old.status.transformed then
        match old.printed.otherFace with
        | some front =>
          { front with otherFace := some { old.printed with otherFace := none } }
        | none => old.printed
      else if targetZone == .battlefield && nightBack then
        match old.printed.otherFace with
        | some back =>
          { back with otherFace := some { old.printed with otherFace := none } }
        | none => old.printed
      else old.printed
    let faceDown := targetZone == .battlefield && old.zone == .stack && old.status.faceDown
    let fromStackTime :=
      if targetZone == .battlefield && old.zone == .stack then old.status.time else 0
    let entersTapped :=
      targetZone == .battlefield &&
        (tapped ||
          (!faceDown &&
            match controller with
            | some p => g.entersTapped p printed
            | none => false))
    let chosenCardType :=
      if targetZone == .battlefield && !faceDown && printed.asEntersChooseCardType then
        some CardType.creature
      else none
    let windcragMardu :=
      targetZone == .battlefield && !faceDown && printed.asEntersChooseMarduOrJeskai
    let prepared :=
      targetZone == .battlefield && !faceDown && printed.entersPrepared
    let impendingNotCreature :=
      old.zone == .stack && targetZone == .battlefield &&
        printed.impending.isSome && fromStackTime > 0
    let baseStatus : Status :=
      if targetZone == .battlefield then
        { faceDown := faceDown
          tapped := entersTapped
          summoningSick := summoningSick
          attacking := isAttacking
          attackingTarget := resolvedAttackTarget
          chosenCardType := chosenCardType
          windcragMardu := windcragMardu
          prepared := prepared
          transformed := nightBack
          cantTransform := nightBack
          returnedAsArtifact := returnedAsArtifact
          onlyFoodArtifact := onlyFoodArtifact
          notACreature := impendingNotCreature }
      else {}
    let candidate : GameObject := {
      id := newId
      printed
      owner := old.owner
      controller := controller
      lastController :=
        if old.zone == .battlefield then old.controller else old.lastController
      defaultController := if targetZone == .battlefield then controller else none
      zone := targetZone
      status := baseStatus
      timestamp := ts
      attachedTo := if targetZone == .battlefield then attachedTo else none
      chosenX := old.chosenX
      wasCast :=
        if targetZone == .battlefield then wasCast.getD (old.zone == .stack && !old.isCopy)
        else false
      lastKnownPower := lkiPower
      lastKnownToughness := lkiToughness
    }
    let entersWith : CounterBag :=
      if targetZone == .battlefield then
        g.computeEntersWithCounters candidate
          (fromStackTime := fromStackTime)
          (applyHope := applyHope)
          (asOf := asOf)
          (extraCounters := extraEntersWith)
      else #[]
    let weaverBonus : Nat :=
      if targetZone == .battlefield && applyHope then
        g.hopeCountersOnEnter candidate asOf
      else 0
    let fresh : GameObject :=
      if entersWith.isEmpty then candidate
      else
        { candidate with
          status :=
            { (candidate.status.withCounterBag entersWith) with
              gotPlusOneThisTurn := entersWith.count .plusOnePlusOne > 0 } }
    (fresh, entersWith, weaverBonus, impendingNotCreature, faceDown)
  let (proposedFresh, proposedEntersWith, _, _, _) := buildArrival g dest g.timestamp
  let gWithProposed : Game :=
    { g with objects := g.objects.map (fun (x : GameObject) => if x.id == id then proposedFresh else x) }
  let proposedAfterSnap := gWithProposed.snapshot proposedFresh
  -- The change that would happen. Replacements match it before it is recorded
  -- (CR 614.1). A replaced change never happens (CR 614.6).
  let proposed :=
    GameEvent.moved g.turnNumber beforeSnap old.zone dest (discarded := discarded)
      (after := some proposedAfterSnap) (verb := verb) (actor := actor)
      (entersWith := proposedEntersWith) (libraryPosition := libraryPosition) (cause := cause)
  -- Snapshot the replacement source before the object leaves so a
  -- simultaneous death of Head of the Hunt still applies (CR 614.6).
  let headSource :=
    if proposed.watches .wouldDie then g.exileInsteadSource? old else none
  let headExile := headSource.isSome
  let smiteExile :=
    proposed.watches .wouldEnterGraveyardFromBattlefield && old.status.untilEotExileIfDies
  let finalityExile :=
    proposed.watches .wouldEnterGraveyardFromBattlefield && old.status.finality > 0
  -- CR 702.34a: a spell cast with flashback is exiled whenever it would
  -- leave the stack for anywhere else.
  let flashbackExile :=
    proposed.watches .wouldLeaveStack && old.castFromGraveyard &&
      old.printed.flashback.isSome && !old.isCopy && dest != .exile
  -- Bilbo, Thief in the Night: an instant or sorcery cast this way is exiled
  -- instead of going to its owner's graveyard.
  let bilboExile :=
    proposed.watches .wouldEnterGraveyardFromStack && old.exileInstantSorceryInstead &&
      !old.isCopy
  let exileInstead := headExile || smiteExile || finalityExile || flashbackExile || bilboExile
  -- CR 614.6: the original move-to-graveyard event never happens.
  let dest := if exileInstead then Zone.exile else dest
  let finalDiscarded :=
    match old.zone, dest with
    | .hand p, .graveyard q => p == q
    | _, _ => false
  let (g, newId) :=
    g.withBatchReturn cause fun g =>
      let g :=
        if finalityExile then
          g.logMsg s!"A finality counter exiles {old.name} instead of putting it into a graveyard"
        else g
      let g :=
        if old.zone == .battlefield then g.unattachFrom id else g
      -- The copy of a prepare spell stays in exile only while its permanent is
      -- on the battlefield (ruling 742).
      let g :=
        if old.zone == .battlefield then g.removePreparedCopy id else g
      let asOf := g.timestamp
      let (fresh, entersWith, weaverBonus, impendingNotCreature, faceDown) :=
        buildArrival g dest asOf
      let newId := fresh.id
      let printed := fresh.printed
      let g :=
        if exileInstead then
          g.logMsg s!"{old.name} is exiled instead of dying (CR 614.6)"
        else g
      let gWithFresh : Game :=
        { g with objects := g.objects.map (fun (x : GameObject) => if x.id == id then fresh else x) }
      let afterSnap := gWithFresh.snapshot fresh
      let finalVerb : Option ZoneVerb :=
        if exileInstead then some .exile else verb
      let happened :=
        GameEvent.moved g.turnNumber beforeSnap old.zone dest
          (discarded := finalDiscarded)
          (after := some afterSnap)
          (verb := finalVerb)
          (actor := actor)
          (entersWith := entersWith)
          (libraryPosition := libraryPosition)
          (cause := cause)
      -- The object that arrives has a new id (CR 400.7). `applyZoneEvent` updates
      -- `g.objects`, zone lists, `nextObjectId`, and `timestamp`.
      let g := g.record happened
      let happenedCause :=
        (g.events.findSomeRev? fun e =>
          match e.change with
          | .rules _ => some e.cause
          | .engine _ => none).getD .unclassified
      let g : Game :=
        match (if dest == .battlefield then resolvedAttackTarget else none) with
        | some tgt =>
          g.record (GameEvent.becameAttacking g.turnNumber (g.object! newId).asEvent tgt
            (cause := some happenedCause))
        | none => g
      let g := g.expireEffectsOnLeavingObject old
      let g :=
        if old.zone == .battlefield then
          g.expireWhileSourceEffects old.id
        else g
      let g :=
        match g.findObject? newId with
        | some cur =>
          -- A permanent whose spell was cast for its impending cost enters with
          -- its time counters and isn't a creature while it has one (CR 702.176,
          -- rulings 967 / 970). The spell itself stays a creature spell, so the
          -- effect is created only now, on the permanent.
          let g : Game :=
            if impendingNotCreature then
              g.createEffect (.notACreature newId) (cause := some (.gameRule .impending))
            else g
          let g : Game :=
            if dest == Zone.battlefield && returnedAsArtifact then
              g.createEffect (.returnedAsArtifact newId) (cause := some happenedCause)
            else g
          let g : Game :=
            if dest == Zone.battlefield && onlyFoodArtifact then
              g.createEffect (.onlyFoodArtifact newId) (cause := some happenedCause)
            else g
          g.createPrintedStaticEffects cur
        | none => g
      -- Loki left: keep his pending copy effect under the same `EffectId`, now
      -- with his last known power (MSH 109).
      let g :=
        g.activeEffects.foldl (fun g (eid, (e : ContinuousEffect)) =>
          match e with
          | .pendingLokiCopy p (some id) _ =>
            if id == old.id then
              g.record (GameEvent.effectUpdated g.turnNumber eid
                (.pendingLokiCopy p none (old.lastKnownPower.getD old.power))
                (cause := some happenedCause))
            else g
          | _ => g) g
      let g :=
        if dest == .battlefield && !faceDown && printed.asEntersChooseCardType then
          g.logMsg s!"{fresh.name} chooses Creature"
        else g
      let g :=
        if weaverBonus > 0 then
          g.logMsg s!"{fresh.nameWithToken} enters with {weaverBonus} additional +1/+1 counter(s)"
        else g
      (g, newId)
  let g :=
    if old.zone == .battlefield && !old.linkedExile.isEmpty then
      Id.run do
        let mut g := g
        for exId in old.linkedExile do
          match g.findObject? exId with
          | some o =>
            if o.zone == .exile then
              let name := o.name
              let linkCause := g.linkedExileCause? o.id
              g := g.change (.setLinkedExileCause o.id none)
              match o.returnToZone with
              | some (.hand p) =>
                let (g', _) := g.move o.id (.hand p) none (cause := linkCause)
                g := g'
                g := g.logMsg s!"{name} returns to {(g.player p).name}'s hand"
              | some (.graveyard p) =>
                let (g', _) := g.move o.id (.graveyard p) none (cause := linkCause)
                g := g'
                g := g.logMsg s!"{name} returns to {(g.player p).name}'s graveyard"
              | _ =>
              if o.printed.isAura then
                match g.battlefield.find? (fun h => h.auraCanEnchant o.printed) with
                | none =>
                  g := g.logMsg
                    s!"{name} remains in exile (can't be attached legally; CR 614.6)"
                | some host =>
                  let hostId := host.id
                  let (g', _) := g.move o.id .battlefield (some o.owner)
                    (attachedTo := some hostId) (cause := linkCause)
                  g := g'
                  g := g.logMsg
                    s!"{name} returns attached to {host.name} (does not target)"
              else
                let sick := !o.printed.keywords.haste
                let (g', _) := g.move o.id .battlefield (some o.owner)
                  (summoningSick := sick) (cause := linkCause)
                g := g'
                g := g.logMsg s!"{name} returns to the battlefield"
          | none => pure ()
        return g
    else g
  -- Head of the Hunt: “When you do, create a Wolf” is a reflexive trigger.
  -- The exile replacement already happened (CR 614.6); the token waits for the stack.
  let g :=
    match headSource with
    | some src =>
      if createsWolfOnOppExileDeath? src then
        match src.controller with
        | some p =>
          let ab := TriggeredAbility.fra .fromEffect
            "When you do, create a 2/2 green Wolf creature token."
            (.createTokens .wolf 1)
          g.change (.pushWaitingTrigger {
              controller := p, source := src, ability := ab,
              event := .bolgSacrificedForReflexive, checked := true })
            |>.logMsg s!"{(g.player p).name}'s Wolf trigger is waiting to go on the stack"
        | none => g
      else g
    | none => g
  (g, newId)

/-- Move `o` to its owner's graveyard and log `reason`. Exile-if-dies
replacements are applied by `move` (CR 614.1 / 614.6). -/
def moveToOwnerGraveyard (g : Game) (o : GameObject) (reason : String)
    (verb : Option ZoneVerb := none) (actor : Option PlayerId := none)
    (cause : Option EventCause := none) : Game :=
  let reason :=
    if o.exileInstantSorceryInstead && o.printed.isInstantOrSorcery then
      s!"{o.name} is exiled"
    else reason
  let g := g.logMsg reason
  (g.move o.id (.graveyard o.owner) none (verb := verb) (actor := actor) (cause := cause)).1

/-- Move several objects to their owners' graveyards as one event.
Sources that also leave do not see “creature cards put into your
graveyard” (Robot Domination; MSH 138). -/
def moveSimultaneousToGraveyard (g : Game) (ids : Array ObjectId) : Game :=
  g.withBatch none fun g =>
    let objs := ids.filterMap g.findObject?
    objs.foldl (fun g o =>
      match g.findObject? o.id with
      | some o => g.moveToOwnerGraveyard o s!"{o.name} is put into its owner's graveyard"
      | none => g) g

/-- Put `id` onto the battlefield under `controller`, setting tap, sickness,
optional attachment, and as-enters counters and status inside the atomic zone
change (CR 611.3 / 614.1c / 614.12). -/
def putOntoBattlefield (g : Game) (id : ObjectId) (controller : PlayerId)
    (tapped := false) (summoningSick := true)
    (attachedTo : Option ObjectId := none) (applyHope := true)
    (attacking := false) (attackingWhom : Option PlayerId := none)
    (attackingTarget : Option AttackTarget := none)
    (returnedAsArtifact := false) (onlyFoodArtifact := false)
    (nightBack := false) (wasCast : Option Bool := none)
    (extraEntersWith : CounterBag := #[])
    (verb : Option ZoneVerb := none) (actor : Option PlayerId := none)
    (cause : Option EventCause := none) : Game × ObjectId :=
  if (g.player controller).lost then
    let name := (g.object! id).name
    (g.logMsg s!"{name} remains in its current zone (CR 800.4b)", id)
  else
    g.move id .battlefield (some controller)
      (tapped := tapped) (summoningSick := summoningSick)
      (attachedTo := attachedTo) (applyHope := applyHope)
      (attacking := attacking) (attackingWhom := attackingWhom)
      (attackingTarget := attackingTarget)
      (returnedAsArtifact := returnedAsArtifact) (onlyFoodArtifact := onlyFoodArtifact)
      (nightBack := nightBack) (wasCast := wasCast)
      (extraEntersWith := extraEntersWith)
      (verb := verb) (actor := actor) (cause := cause)

end Game
end Mtg.Engine
