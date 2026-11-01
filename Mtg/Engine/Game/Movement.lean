import Mtg.Engine.Game.Attachments

/-!
# Zone changes (CR 400)

Exile-instead-of-dying replacement effects (CR 614.6), dying triggers,
`move` — the single zone-change routine — simultaneous moves to the
graveyard, and putting cards onto the battlefield (CR 611.3 / 603.6).
-/

namespace Mtg.Engine
namespace Game

/-- The exiled copy of `srcId`'s prepare spell ceases to exist. -/
def removePreparedCopy (g : Game) (srcId : ObjectId)
    (cause : Option EventCause := some (.stateBased .copyOutsideStackOrBf)) : Game :=
  match g.preparedCopyOf? srcId with
  | some c => (g.ceaseToExist c.id (cause := cause)).logMsg s!"The copy of {c.name} in exile ceases to exist"
  | none => g

/-- `o` becomes prepared: its controller creates a copy of its prepare spell
in exile and may cast that copy while `o` stays prepared (ruling 742). A
creature without a prepare spell can't become prepared (ruling 747), and a
prepared creature can't become prepared again (ruling 743). Only the printed
prepare spell is copied, so copy exceptions on `o` don't apply (ruling 741). -/
def becomePrepared (g : Game) (o : GameObject) (cause : Option EventCause := none) : Game :=
  match (g.baseCard o).prepareFace with
  | none => g.logMsg s!"{o.name} has no prepare spell and can't become prepared"
  | some face =>
    if o.status.prepared then g.logMsg s!"{o.name} is already prepared"
    else
      let p := (g.controllerOf o).getD o.owner
      let srcFallback := (g.currentResolvingContext?.bind Prod.fst).orElse (fun _ => some o.id)
      let batchCause :=
        g.resolveOptionalCause cause (fallbackSrc := srcFallback) (fallbackCtrl := some p)
          (defaultCause := .gameRule .spellCast)
      let g := g.withBatch (some batchCause) fun g =>
        let g := g.createPreparedCopy o face (cause := cause)
        let prepCause :=
          g.resolveOptionalCause cause (fallbackSrc := srcFallback) (fallbackCtrl := some p)
            (defaultCause := .gameRule .spellCast)
        g.record (GameEvent.designation g.turnNumber (g.snapshot o) .prepared true (cause := prepCause))
      g.logMsg s!"{o.name} becomes prepared. A copy of {face.name} is exiled"

/-- `o` stops being prepared and the copy of its prepare spell in exile
ceases to exist. Nothing happens if it isn't prepared (ruling 737). -/
def unprepare (g : Game) (o : GameObject) (cause : Option EventCause := none) : Game :=
  if !o.status.prepared then g
  else
    let srcFallback := (g.currentResolvingContext?.bind Prod.fst).orElse (fun _ => some o.id)
    let resolvedCause :=
      g.resolveOptionalCause cause (fallbackSrc := srcFallback) (fallbackCtrl := g.controllerOf o)
        (defaultCause := .gameRule .spellCast)
    let g := g.record (GameEvent.designation g.turnNumber (g.snapshot o) .prepared false (cause := resolvedCause))
    (g.removePreparedCopy o.id).logMsg s!"{o.name} is no longer prepared"

/-- True when `o` replaces an opposing creature dying with exile. -/
def exilesOppDeath? (g : Game) (o : GameObject) : Bool :=
  ((g.baseCard o).exileOppCreaturesInstead && g.retainsPrintedAbilities o) ||
    (g.staticAbilities o).any (fun
      | .exileOppDeathCreateWolf => true
      | .fra .exileOpponentsDyingCreatures => true
      | _ => false)

/-- True when `o` also creates a Wolf after that replacement (Head of the Hunt). -/
def createsWolfOnOppExileDeath? (g : Game) (o : GameObject) : Bool :=
  (g.staticAbilities o).any (fun
    | .exileOppDeathCreateWolf => true
    | _ => false)

/-- Strip outer `.replaced` wrappers from `EventCause` to recover the underlying
one-shot or game-rule cause for non-replaced side effects of the same instruction. -/
private def unreplacedCause : EventCause → EventCause
  | .replaced _ orig => unreplacedCause orig
  | c => c

/-- Source of a Head-of-the-Hunt-style replacement, if `dying` is an opposing
creature that would go to a graveyard. Accepts an optional `preBattlefield`
snapshot so a simultaneous death of the source still applies (CR 614.4 / 614.6). -/
def exileInsteadSource? (g : Game) (dying : GameObject)
    (preBattlefield : Option (Array GameObject) := none) : Option GameObject :=
  let bf := preBattlefield.getD g.battlefield
  (bf.filter g.exilesOppDeath?).find? (fun o =>
    o.id != dying.id &&
      match g.controllerOf o, g.controllerOf dying with
      | some p, some q => p != q
      | _, _ => false)

/-- Result of running the CR 616.1 replacement loop on a proposed zone move. -/
structure ZoneMoveReplacementResult where
  dest : Zone
  exileInstead : Bool := false
  finalityExile : Bool := false
  headSource : Option GameObject := none
  applied : Array ReplacementId := #[]
  cause : Option EventCause := none
  choice? : Option (PlayerId × Array ReplacementId) := none
deriving Repr, Inhabited, BEq

/-- Pre-batch game state and object snapshot for `old` when an enclosing
simultaneous batch (`openBatch*`) already held `old` in `old.zone` before any
co-departing permanent or SBA mutation changed `g` (CR 603.10a / 608.2h / 704.8). -/
private def preBatchBoardFor (g : Game) (old : GameObject) : Game × GameObject :=
  if g.currentBatch.isSome && !g.openBatchObjects.isEmpty then
    let preG : Game :=
      { g with
        objects := g.openBatchObjects
        players := g.openBatchPlayers
        activeEffects := g.openBatchEffects }
    match preG.findObject? old.id with
    | some preOld =>
      if preOld.zone == old.zone then (preG, preOld) else (g, old)
    | none => (g, old)
  else (g, old)

/-- Run the CR 616.1 replacement loop for `old` moving from `old.zone` to
`initialDest` (CR 614.1a / 614.5 / 614.6 / 616.1). -/
def replaceZoneMove (g : Game) (old : GameObject) (beforeSnap : EventObject)
    (initialDest : Zone) (verb : Option ZoneVerb := none)
    (actor : Option PlayerId := none)
    (libraryPosition : Option LibraryPosition := none)
    (preBattlefield : Option (Array GameObject) := none)
    (applied : Array ReplacementId := #[])
    (cause : Option EventCause := none) : ZoneMoveReplacementResult := Id.run do
  let (board, boardOld) := preBatchBoardFor g old
  let mut curDest := initialDest
  let mut exileInstead := false
  let mut finalityExile := false
  let mut headSource : Option GameObject := none
  let mut curApplied := applied
  let mut curCause := cause
  let mut curOrder := g.replacementOrder
  let mut choice? : Option (PlayerId × Array ReplacementId) := none
  let oldCtrl := board.controllerOf boardOld
  let affected := oldCtrl.getD old.owner
  let bf := preBattlefield.getD board.battlefield
  let mut fuel := 32
  while fuel > 0 do
    fuel := fuel - 1
    let discarded :=
      verb == some .discard ||
        match old.zone, curDest with
        | .hand p, .graveyard q => p == q
        | _, _ => false
    let proposedCause := g.resolveOptionalCause curCause (fallbackCtrl := some affected)
    let proposed :=
      GameEvent.moved g.turnNumber beforeSnap old.zone curDest (discarded := discarded)
        (verb := verb) (actor := actor) (libraryPosition := libraryPosition) (cause := proposedCause)
    let mut specs : Array (ReplacementSpec × Option GameObject × Bool) := #[]
    -- CR 702.34a: flashback exiles the spell whenever it would leave the stack for anywhere else.
    let hasFlashback :=
      GameEvent.castWithFlashback g.events old.id || g.flashbackUntilEot old ||
        (g.castFromGraveyard old.id && !g.freeCastFromGraveyard old &&
          ((g.baseCard old).flashback.isSome || g.hasFlashbackPermission old))
    if proposed.watches .wouldLeaveStack && hasFlashback && !old.isCopy && curDest != .exile then
      specs := specs.push (
        { id := { kind := .flashbackExile, object := some old.id }
          source := some old.id
          controller := oldCtrl
          affectedPlayer := affected
          kind := .exileInsteadOfStackLeave (some old.id) }, none, false)
    -- Bilbo, Thief in the Night: instant/sorcery cast this way is exiled instead of going to graveyard.
    if proposed.watches .wouldEnterGraveyardFromStack && g.exileInstantSorceryInstead old &&
        g.isInstantOrSorcery old && !old.isCopy then
      specs := specs.push (
        { id := { kind := .exileInstantSorceryInstead, object := some old.id }
          source := some old.id
          controller := oldCtrl
          affectedPlayer := affected
          kind := .exileInsteadOfGraveyard (some old.id) false }, none, false)
    -- Until-EOT exile-if-dies replacement (Smite, etc.).
    if proposed.watches .wouldEnterGraveyardFromBattlefield && g.untilEotExileIfDies old then
      specs := specs.push (
        { id := { kind := .untilEotExileIfDies, object := some old.id }
          source := some old.id
          controller := oldCtrl
          affectedPlayer := affected
          kind := .exileInsteadOfGraveyard (some old.id) false }, none, false)
    -- Finality counter replacement (CR 122.1h).
    if proposed.watches .wouldEnterGraveyardFromBattlefield && old.status.finality > 0 then
      specs := specs.push (
        { id := { kind := .finalityCounterExile, object := some old.id }
          source := some old.id
          controller := oldCtrl
          affectedPlayer := affected
          kind := .exileInsteadOfGraveyard (some old.id) false }, none, true)
    -- Opposing creature death replacements (Head of the Hunt, Kalitas, etc.).
    if proposed.watches .wouldDie then
      for src in bf.filter board.exilesOppDeath? do
        if src.id != old.id then
          match board.controllerOf src, oldCtrl with
          | some p, some q =>
            if p != q then
              specs := specs.push (
                { id := { kind := .exileOppDeath, object := some src.id }
                  source := some src.id
                  controller := some p
                  affectedPlayer := affected
                  kind := .exileInsteadOfGraveyard (some old.id) (board.createsWolfOnOppExileDeath? src) },
                some src, false)
          | _, _ => pure ()
    -- Active `ContinuousEffect.replacement` effects for zone moves.
    for (_, eff) in g.activeEffects do
      match eff with
      | .replacement spec _ =>
        match spec.kind with
        | .exileInsteadOfStackLeave tid =>
          if (tid.isNone || tid == some old.id) && proposed.watches .wouldLeaveStack && curDest != .exile then
            specs := specs.push ({ spec with affectedPlayer := affected }, none, false)
        | .exileInsteadOfGraveyard tid wolf =>
          if spec.id.kind != .exileInstantSorceryInstead &&
              spec.id.kind != .untilEotExileIfDies &&
              (tid.isNone || tid == some old.id) &&
              (match curDest with | .graveyard _ => true | _ => false) && curDest != .exile then
            let srcObj := if wolf then spec.source.bind board.findObject? else none
            specs := specs.push ({ spec with affectedPlayer := affected }, srcObj, false)
        | _ => pure ()
      | _ => pure ()
    let candidates := specs.map (fun (s, _, _) => (ReplacementOrPrevention.replacement s).toCandidate)
    match g.selectNextReplacementStep candidates curApplied curOrder with
    | .none => fuel := 0
    | .needChoice chooser choices ord' =>
      curOrder := ord'
      choice? := some (chooser, choices)
      fuel := 0
    | .chosen chosen ord' =>
      curOrder := ord'
      match specs.find? (fun (s, _, _) => s.id == chosen.id) with
      | none => fuel := 0
      | some (spec, hSrc, isFinality) =>
        curApplied := curApplied.push chosen.id
        curCause := g.wrapReplacedCause chosen.id curCause (some affected)
        match spec.kind with
        | .exileInsteadOfStackLeave _ | .exileInsteadOfGraveyard .. =>
          curDest := .exile
          exileInstead := true
          if isFinality then finalityExile := true
          if hSrc.isSome then headSource := hSrc
        | _ => pure ()
  return {
    dest := curDest
    exileInstead := exileInstead
    finalityExile := finalityExile
    headSource := headSource
    applied := curApplied
    cause := curCause
    choice? := choice?
  }

mutual

/-- `partial` because linked-exile returns recurse into `move` (CR 610.3). -/
partial def move (g : Game) (id : ObjectId) (dest : Zone)
    (controller : Option PlayerId := none)
    (tapped : Bool := false) (summoningSick : Bool := true)
    (attachedTo : Option ObjectId := none) (applyHope : Bool := true)
    (attacking : Bool := false)
    (attackingTarget : Option AttackTarget := none)
    (returnedAsArtifact : Bool := false) (onlyFoodArtifact : Bool := false)
    (nightBack : Bool := false)
    (extraEntersWith : CounterBag := #[])
    (verb : Option ZoneVerb := none) (actor : Option PlayerId := none)
    (libraryPosition : Option LibraryPosition := none)
    (preBattlefield : Option (Array GameObject) := none)
    (isCopy : Option Bool := none)
    (overridePrinted : Option CardDef := none)
    (adventurerCard : Option CardDef := none)
    (faceDown? : Option Bool := none)
    (fromStackTime? : Option Nat := none)
    (enterMods : Array TriggeredAbility.TriggerEnterWith := #[])
    (cause : Option EventCause := none) : Game × ObjectId :=
  if let .chooseReplacement .. := g.pending then
    let old? := g.findObject? id
    let sacrificed := verb == some .sacrifice
    let discarded :=
      verb == some .discard ||
        match old? with
        | some o =>
          match o.zone, dest with
          | .hand p, .graveyard q => p == q
          | _, _ => false
        | none => false
    let faceDown :=
      faceDown?.getD (dest == .battlefield && old?.any (fun o => o.zone == .stack && o.status.faceDown))
    let fromStackTime :=
      fromStackTime?.getD
        (if dest == .battlefield then (old?.filter (·.zone == .stack)).map (·.status.time) |>.getD 0 else 0)
    let isAttacking := attacking || attackingTarget.isSome
    let resolvedAttackTarget : Option AttackTarget :=
      if isAttacking then some (attackingTarget.getD (.player g.defendingPlayer)) else none
    (g.chainPendingReplacement
      (.move id dest controller sacrificed discarded verb actor faceDown tapped
        isAttacking resolvedAttackTarget nightBack returnedAsArtifact onlyFoodArtifact
        extraEntersWith libraryPosition fromStackTime applyHope preBattlefield
        isCopy overridePrinted adventurerCard summoningSick attachedTo enterMods cause),
     id)
  else
  let old := g.object! id
  let (board, boardOld) := preBatchBoardFor g old
  let isAttacking := attacking || attackingTarget.isSome
  let resolvedAttackTarget : Option AttackTarget :=
    if isAttacking then
      some (attackingTarget.getD (.player g.defendingPlayer))
    else none
  let beforeSnap := board.snapshot boardOld
  let sourceCtrlTargets : Array ObjectId :=
    if old.zone != .battlefield || dest == .battlefield then #[]
    else
      let sourceCtrlIds := g.activeEffects.filterMap fun (eid, e) =>
        match e with
        | .layered _ (.control _) (.whileSourceOnBattlefield s)
        | .layered _ (.control _) (.untilSourceLeaves s) =>
          if s == old.id then some eid else none
        | _ => none
      if sourceCtrlIds.isEmpty then #[]
      else
        g.battlefield.filterMap fun pObj =>
          if pObj.id != old.id &&
              (g.appliedControlEffectIds pObj).any (fun eid => sourceCtrlIds.contains eid) then
            some pObj.id
          else none
  let buildArrival (g : Game) (targetZone : Zone) (asOf : Nat)
      (applied : Array ReplacementId := #[]) (curCause : Option EventCause := cause) :
      GameObject × CounterBag × Nat × Bool × Bool × Array ReplacementId × Option EventCause × Option (PlayerId × Array ReplacementId) × Option (CardDef × CardDef) :=
    let newId : ObjectId := ⟨g.nextObjectId⟩
    let ts := g.timestamp + 1
    let leavingPlay :=
      (old.zone == .battlefield || old.zone == .stack) &&
        targetZone != .battlefield && targetZone != .stack
    let printed :=
      match overridePrinted with
      | some p => p
      | none =>
        if old.zone == .stack && targetZone != .stack then
          match old.adventurerCard with
          | some advOrig => advOrig
          | none =>
            if leavingPlay && old.status.transformed then
              match old.printed.otherFace with
              | some front =>
                let keepToken := old.printed.isToken
                { front with
                  isToken := keepToken
                  otherFace := some { old.printed with isToken := keepToken, otherFace := none } }
              | none => old.printed
            else old.printed
        else if leavingPlay && old.status.transformed then
          match old.printed.otherFace with
          | some front =>
            let keepToken := old.printed.isToken
            { front with
              isToken := keepToken
              otherFace := some { old.printed with isToken := keepToken, otherFace := none } }
          | none => old.printed
        else old.printed
    let faceDown := faceDown?.getD (targetZone == .battlefield && old.zone == .stack && old.status.faceDown)
    let fromStackTime :=
      fromStackTime?.getD (if targetZone == .battlefield && old.zone == .stack then old.status.time else 0)
    let prepared :=
      targetZone == .battlefield && !faceDown && printed.entersPrepared
    let impendingNotCreature :=
      (old.zone == .stack || fromStackTime?.isSome) && targetZone == .battlefield &&
        printed.impending.isSome && fromStackTime > 0
    let baseStatus : Status :=
      if targetZone == .battlefield then
        { faceDown := faceDown
          tapped := tapped
          summoningSick := summoningSick
          attacking := isAttacking
          attackingTarget := resolvedAttackTarget
          prepared := prepared }
      else {}
    let candidate : GameObject := {
      id := newId
      printed
      owner := old.owner
      controller := controller
      defaultController := if targetZone == .battlefield then controller else none
      zone := targetZone
      status := baseStatus
      timestamp := ts
      isCopy := isCopy.getD (if targetZone == .stack then old.isCopy else false)
      isCommander := old.isCommander
      adventurerCard := if targetZone == .stack then adventurerCard.orElse (fun _ => old.adventurerCard) else none
      attachedTo := if targetZone == .battlefield then attachedTo else none
      chosenX := if targetZone == .stack then old.chosenX else none
    }
    if targetZone == .battlefield then
      let gForArrival : Game := Id.run do
        let mut g' := g
        if impendingNotCreature then
          g' := { g' with activeEffects := g'.activeEffects.push (⟨g'.nextEffectId⟩, .notACreature newId), nextEffectId := g'.nextEffectId + 1 }
        if returnedAsArtifact then
          g' := { g' with activeEffects := g'.activeEffects.push (⟨g'.nextEffectId⟩, .returnedAsArtifact newId), nextEffectId := g'.nextEffectId + 1 }
        if onlyFoodArtifact then
          g' := { g' with activeEffects := g'.activeEffects.push (⟨g'.nextEffectId⟩, .onlyFoodArtifact newId), nextEffectId := g'.nextEffectId + 1 }
        for m in enterMods do
          match m with
          | .loseAllAbilities =>
            g' := { g' with activeEffects := g'.activeEffects.push (⟨g'.nextEffectId⟩, .layered (.objects #[newId]) (.abilities {} .all) .indefinite), nextEffectId := g'.nextEffectId + 1 }
          | .keywords k =>
            g' := { g' with activeEffects := g'.activeEffects.push (⟨g'.nextEffectId⟩, .layered (.objects #[newId]) (.abilities { keywords := k } .none) .indefinite), nextEffectId := g'.nextEffectId + 1 }
          | .additionalSubtype subtype =>
            g' := { g' with activeEffects := g'.activeEffects.push (⟨g'.nextEffectId⟩, .additionalSubtype newId subtype (dedup := true)), nextEffectId := g'.nextEffectId + 1 }
          | _ => pure ()
        return g'
      let etb :=
        gForArrival.applyEtbReplacements candidate
          (fromStackTime := fromStackTime)
          (applyHope := applyHope)
          (asOf := asOf)
          (extraCounters := extraEntersWith)
          (leavingPlay := leavingPlay)
          (forceBackFace := nightBack)
          (applied := applied)
          (cause := curCause)
      (etb.candidate, etb.entersWith, etb.weaverBonus, impendingNotCreature, faceDown, etb.applied, etb.cause, etb.choice?, etb.tempCopyUntilEot)
    else
      (candidate, #[], 0, impendingNotCreature, faceDown, applied, curCause, none, none)
  -- Run the CR 616.1 replacement loop for leaving/destination replacements (CR 614.6).
  let origDest := dest
  let moveRep :=
    g.replaceZoneMove old beforeSnap dest (verb := verb) (actor := actor)
      (libraryPosition := libraryPosition) (preBattlefield := preBattlefield)
      (cause := cause)
  let dest := moveRep.dest
  let preCheckArrivalChoice? :=
    if moveRep.choice?.isNone && dest == .battlefield then
      let (_, _, _, _, _, _, _, ch?, _) := buildArrival g dest g.timestamp moveRep.applied moveRep.cause
      ch?
    else none
  match moveRep.choice?.orElse (fun _ => preCheckArrivalChoice?) with
  | some (chooser, choices) =>
    let sacrificed := verb == some .sacrifice
    let discarded :=
      verb == some .discard ||
        match old.zone, origDest with
        | .hand p, .graveyard q => p == q
        | _, _ => false
    let faceDown := faceDown?.getD (origDest == .battlefield && old.zone == .stack && old.status.faceDown)
    let fromStackTime := fromStackTime?.getD (if origDest == .battlefield && old.zone == .stack then old.status.time else 0)
    (g.promptChooseReplacement chooser choices
      (.move id origDest controller sacrificed discarded verb actor faceDown tapped
        isAttacking resolvedAttackTarget nightBack returnedAsArtifact onlyFoodArtifact
        extraEntersWith libraryPosition fromStackTime applyHope preBattlefield
        isCopy overridePrinted adventurerCard summoningSick attachedTo enterMods cause),
     id)
  | none =>
  let exileInstead := moveRep.exileInstead
  let finalityExile := moveRep.finalityExile
  let headSource := moveRep.headSource
  let finalDiscarded :=
    verb == some .discard ||
      match old.zone, origDest with
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
      let (fresh, entersWith, weaverBonus, impendingNotCreature, _faceDown, allApplied, finalCause, _, tempCopyUntilEot) :=
        buildArrival g dest asOf moveRep.applied moveRep.cause
      let g := g.consumeReplacementOrder allApplied
      let newId := fresh.id
      let g :=
        if exileInstead then
          g.logMsg s!"{old.name} is exiled instead of dying (CR 614.6)"
        else g
      let freshForSnap : GameObject :=
        match tempCopyUntilEot with
        | some (_, copyCard) => { fresh with printed := copyCard }
        | none => fresh
      let gWithFresh : Game := Id.run do
        let mut g' : Game :=
          { g with objects := g.objects.map (fun (x : GameObject) => if x.id == id then freshForSnap else x) }
        if dest == .battlefield then
          if let some (_, copyCard) := tempCopyUntilEot then
            g' := { g' with activeEffects := g'.activeEffects.push (⟨g'.nextEffectId⟩, .copy newId copyCard (untilEot := true)), nextEffectId := g'.nextEffectId + 1 }
          if impendingNotCreature then
            g' := { g' with activeEffects := g'.activeEffects.push (⟨g'.nextEffectId⟩, .notACreature newId), nextEffectId := g'.nextEffectId + 1 }
          if returnedAsArtifact then
            g' := { g' with activeEffects := g'.activeEffects.push (⟨g'.nextEffectId⟩, .returnedAsArtifact newId), nextEffectId := g'.nextEffectId + 1 }
          if onlyFoodArtifact then
            g' := { g' with activeEffects := g'.activeEffects.push (⟨g'.nextEffectId⟩, .onlyFoodArtifact newId), nextEffectId := g'.nextEffectId + 1 }
          for m in enterMods do
            match m with
            | .loseAllAbilities =>
              g' := { g' with activeEffects := g'.activeEffects.push (⟨g'.nextEffectId⟩, .layered (.objects #[newId]) (.abilities {} .all) .indefinite), nextEffectId := g'.nextEffectId + 1 }
            | .keywords k =>
              g' := { g' with activeEffects := g'.activeEffects.push (⟨g'.nextEffectId⟩, .layered (.objects #[newId]) (.abilities { keywords := k } .none) .indefinite), nextEffectId := g'.nextEffectId + 1 }
            | .additionalSubtype subtype =>
              if !g'.hasSubtype freshForSnap subtype then
                g' := { g' with activeEffects := g'.activeEffects.push (⟨g'.nextEffectId⟩, .additionalSubtype newId subtype (dedup := true)), nextEffectId := g'.nextEffectId + 1 }
            | _ => pure ()
        return g'
      let afterSnap : EventObject :=
        match tempCopyUntilEot with
        | some (origPrinted, _) =>
          { gWithFresh.snapshot freshForSnap with
            printed := some origPrinted
            isCopy := fresh.isCopy }
        | none => gWithFresh.snapshot freshForSnap
      let finalVerb : Option ZoneVerb :=
        if verb == some .sacrifice then some .sacrifice
        else if finalDiscarded || verb == some .discard then some .discard
        else if verb == some .mill then some .mill
        else if verb == some .destroy then some .destroy
        else if exileInstead then some .exile
        else verb
      let resolvedFinalCause :=
        g.resolveOptionalCause finalCause
          (fallbackCtrl := actor.orElse (fun _ =>
            controller.orElse (fun _ => (g.controllerOf old).orElse (fun _ => some old.owner))))
      let happened :=
        GameEvent.moved g.turnNumber beforeSnap old.zone dest
          (discarded := finalDiscarded)
          (after := some afterSnap)
          (verb := finalVerb)
          (actor := actor)
          (entersWith := entersWith)
          (libraryPosition := libraryPosition)
          (cause := resolvedFinalCause)
      -- The object that arrives has a new id (CR 400.7). `applyZoneEvent` updates
      -- `g.objects`, zone lists, `nextObjectId`, and `timestamp`.
      let g := g.record happened
      let happenedCause :=
        (g.events.findSomeRev? (·.cause?)).getD resolvedFinalCause
      let baseHappenedCause := unreplacedCause happenedCause
      let g : Game :=
        match (if dest == .battlefield then resolvedAttackTarget else none) with
        | some tgt =>
          g.record (GameEvent.becameAttacking g.turnNumber (g.snapshot (g.object! newId)) tgt
            (cause := baseHappenedCause))
        | none => g
      let g := g.expireEffectsOnLeavingObject old
      let g :=
        if old.zone == .battlefield then
          let g := g.expireWhileSourceEffects old.id
          sourceCtrlTargets.foldl (fun acc tid =>
            match acc.findObject? tid with
            | none => acc
            | some cur =>
              if !cur.isOnBattlefield || !(acc.appliedControlEffectIds cur).isEmpty then acc
              else
                let destP := (acc.controllerOf cur).getD (cur.defaultController.getD cur.owner)
                if (acc.player destP).lost then
                  let name := acc.name cur
                  let (acc, _) := acc.move tid .exile none (cause := some (.gameRule .playerLeftGame))
                  acc.logMsg s!"{name} is exiled (CR 800.4c)"
                else acc) g
        else g
      let g :=
        match g.findObject? newId with
        | some _ =>
          let g : Game :=
            match tempCopyUntilEot with
            | some (_, copyCard) =>
              if dest == Zone.battlefield then
                g.createEffect (.copy newId copyCard (untilEot := true)) (cause := some baseHappenedCause)
              else g
            | none => g
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
              g.createEffect (.returnedAsArtifact newId) (cause := some baseHappenedCause)
            else g
          let g : Game :=
            if dest == Zone.battlefield && onlyFoodArtifact then
              g.createEffect (.onlyFoodArtifact newId) (cause := some baseHappenedCause)
            else g
          if dest == Zone.battlefield then
            enterMods.foldl (fun acc m =>
              match m with
              | .loseAllAbilities =>
                acc.createEffect (.layered (.objects #[newId]) (.abilities {} .all) .indefinite)
                  (cause := some baseHappenedCause)
              | .keywords k =>
                acc.createEffect (.layered (.objects #[newId]) (.abilities { keywords := k } .none) .indefinite)
                  (cause := some baseHappenedCause)
              | .additionalSubtype subtype =>
                match acc.findObject? newId with
                | some cur =>
                  if acc.hasSubtype cur subtype then acc
                  else
                    acc.createEffect (.additionalSubtype newId subtype (dedup := true))
                      (cause := some baseHappenedCause)
                | none => acc
              | _ => acc) g
          else g
        | none => g
      let g :=
        if weaverBonus > 0 then
          g.logMsg s!"{freshForSnap.nameWithToken} enters with {weaverBonus} additional +1/+1 counter(s)"
        else g
      (g, newId)
  let g :=
    if old.zone == .battlefield && !old.linkedExile.isEmpty then
      g.returnLinkedExileMoves old.linkedExile
    else g
  -- Head of the Hunt: “When you do, create a Wolf” is a reflexive trigger.
  -- The exile replacement already happened (CR 614.6); the token waits for the stack.
  let g :=
    match headSource with
    | some src =>
      if g.createsWolfOnOppExileDeath? src then
        match g.controllerOf src with
        | some p =>
          if (g.player p).lost || (g.player p).leftTheGame then g
          else
            let ab := TriggeredAbility.fra .fromEffect
              "When you do, create a 2/2 green Wolf creature token."
              (.createTokens .wolf 1)
            g.recordReflexiveTrigger {
                controller := p, source := src, ability := ab,
                event := .bolgSacrificedForReflexive, checked := true }
              |>.logMsg s!"{(g.player p).name}'s Wolf trigger is waiting to go on the stack"
        | none => g
      else g
    | none => g
  (g, newId)

/-- Return CR 610.3 linked-exile cards sequentially, pausing via
`PendingReplacement.finishLinkedExileMove` if a return opens `Pending.chooseReplacement`. -/
partial def returnLinkedExileMoves (g : Game) (ids : Array ObjectId) : Game :=
  if ids.isEmpty then g
  else if let .chooseReplacement .. := g.pending then
    g.chainPendingReplacement
      (.finishLinkedExileMove (ids.map (fun eid => (eid, .exile, none, false, none))))
  else Id.run do
    let mut g := g
    for i in [0:ids.size] do
      let exId := ids[i]!
      match g.findObject? exId with
      | some o =>
        if o.zone == .exile then
          let name := o.name
          let linkCause := g.lastMoveCauseOf? o.id
          match o.returnToZone with
          | some (.hand p) =>
            let (g', _) := g.move o.id (.hand p) none (cause := linkCause)
            g := g'.logMsg s!"{name} returns to {(g'.player p).name}'s hand"
          | some (.graveyard p) =>
            let (g', _) := g.move o.id (.graveyard p) none (cause := linkCause)
            g := g'.logMsg s!"{name} returns to {(g'.player p).name}'s graveyard"
          | _ =>
            if g.isAura o then
              match g.battlefield.find? (fun h => g.auraObjCanEnchant h o) with
              | none =>
                g := g.logMsg s!"{name} remains in exile (can't be attached legally; CR 614.6)"
              | some host =>
                let hostId := host.id
                let hostName := g.name host
                let (g', _) := g.move o.id .battlefield (some o.owner)
                  (attachedTo := some hostId) (cause := linkCause)
                g := g'.logMsg s!"{name} returns attached to {hostName} (does not target)"
            else
              let (g', _) := g.move o.id .battlefield (some o.owner) (cause := linkCause)
              g := g'.logMsg s!"{name} returns to the battlefield"
          if let .chooseReplacement .. := g.pending then
            let rem := ids.extract (i + 1) ids.size
            if !rem.isEmpty then
              g := g.chainPendingReplacement
                (.finishLinkedExileMove (rem.map (fun eid => (eid, .exile, none, false, none))))
            return g
      | none => pure ()
    return g

end

/-- Move `o` to its owner's graveyard and log `reason`. Exile-if-dies
replacements are applied by `move` (CR 614.1 / 614.6). -/
def moveToOwnerGraveyard (g : Game) (o : GameObject) (reason : String)
    (verb : Option ZoneVerb := none) (actor : Option PlayerId := none)
    (preBattlefield : Option (Array GameObject) := none)
    (cause : Option EventCause := none) : Game :=
  let reason :=
    if g.exileInstantSorceryInstead o && g.isInstantOrSorcery o then
      s!"{o.name} is exiled"
    else reason
  let g := g.logMsg reason
  (g.move o.id (.graveyard o.owner) none (verb := verb) (actor := actor)
    (preBattlefield := preBattlefield) (cause := cause)).1

/-- Move several objects to their owners' graveyards as one event.
Sources that also leave do not see “creature cards put into your
graveyard” (Robot Domination; MSH 138). -/
def moveSimultaneousToGraveyard (g : Game) (ids : Array ObjectId)
    (preBattlefield : Option (Array GameObject) := none)
    (cause : Option EventCause := none) : Game :=
  g.withBatch cause fun g => Id.run do
    let preBf := preBattlefield.getD g.battlefield
    let batchCause := cause.orElse (fun _ => g.currentBatch.bind (·.2))
    let mut g := g
    for i in [0:ids.size] do
      let id := ids[i]!
      if let some o := g.findObject? id then
        g := g.moveToOwnerGraveyard o s!"{o.name} is put into its owner's graveyard"
          (preBattlefield := some preBf) (cause := batchCause)
        if let .chooseReplacement .. := g.pending then
          let rem := ids.extract (i + 1) ids.size
          if !rem.isEmpty then
            g := g.chainPendingReplacement
              (.moveSimultaneousToGraveyard rem (some preBf) batchCause)
          return g
    return g

/-- Put `id` onto the battlefield under `controller`, setting tap, sickness,
optional attachment, and as-enters counters and status inside the atomic zone
change (CR 611.3 / 614.1c / 614.12). -/
def putOntoBattlefield (g : Game) (id : ObjectId) (controller : PlayerId)
    (tapped := false) (summoningSick := true)
    (attachedTo : Option ObjectId := none) (applyHope := true)
    (attacking := false)
    (attackingTarget : Option AttackTarget := none)
    (returnedAsArtifact := false) (onlyFoodArtifact := false)
    (nightBack := false)
    (extraEntersWith : CounterBag := #[])
    (enterMods : Array TriggeredAbility.TriggerEnterWith := #[])
    (verb : Option ZoneVerb := none) (actor : Option PlayerId := none)
    (cause : Option EventCause := none) : Game × ObjectId :=
  if (g.player controller).lost then
    let name := (g.object! id).name
    (g.logMsg s!"{name} remains in its current zone (CR 800.4b)", id)
  else
    g.move id .battlefield (some controller)
      (tapped := tapped) (summoningSick := summoningSick)
      (attachedTo := attachedTo) (applyHope := applyHope)
      (attacking := attacking)
      (attackingTarget := attackingTarget)
      (returnedAsArtifact := returnedAsArtifact) (onlyFoodArtifact := onlyFoodArtifact)
      (nightBack := nightBack)
      (extraEntersWith := extraEntersWith)
      (enterMods := enterMods)
      (verb := verb) (actor := actor) (cause := cause)

/-- Counter a spell on the stack. `exile` puts a permanent spell into exile
and may grant a free cast (CR 701.5 / Thranduil's Decree). -/
def counterStackSpell (g : Game) (spellId : ObjectId) (exilePermanent := false)
    (grantFreeCast := false) (controller : Option PlayerId := none) : Game :=
  let ctrl := controller.orElse (fun _ => g.currentResolvingContext?.bind Prod.snd)
  match g.findObject? spellId with
  | none => g.logMsg "The spell is no longer on the stack"
  | some o =>
    if o.zone != .stack then
      g.logMsg s!"{o.name} is no longer on the stack"
    else if o.abilityEffect.isSome || o.triggeredAbility.isSome then
      let name := o.name
      let cause : Option EventCause :=
        some (match ctrl with
          | some c => g.resolvingOrRuleCause c
          | none => .gameRule .spellCast)
      let g := g.ceaseToExist o.id (cause := cause)
      g.logMsg s!"{name} is countered"
    else if ((g.baseCard o).cantBeCountered && g.retainsPrintedAbilities o) || g.uncounterableThisCast o then
      g.logMsg s!"{g.name o} can't be countered"
    else
      let dest :=
        if exilePermanent && g.isPermanentCard o then Zone.exile
        else Zone.graveyard o.owner
      let name := o.name
      let (g, cause) : Game × EventCause :=
        match g.currentResolvingContext? with
        | some _ => g.allocDelayedCause ctrl
        | none => (g, .gameRule .spellCast)
      let (g, newId) := g.move spellId dest none
        (verb := some .counter) (actor := ctrl) (cause := some cause)
      let g :=
        match ctrl with
        | some c =>
          if dest == Zone.exile && grantFreeCast then
            g.createEffect (.playPermission newId {
              player := c
              whileExiled := true
              withoutManaCost := true }) (cause := some cause)
          else g
        | none => g
      let destNote := if dest == Zone.exile then "exiled" else "countered"
      g.logMsg s!"{name} is {destNote}"

end Game
end Mtg.Engine
