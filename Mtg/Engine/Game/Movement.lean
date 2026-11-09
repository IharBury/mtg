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
  | some c =>
    let cName := g.name c
    (g.ceaseToExist c.id (cause := cause)).logMsg s!"The copy of {cName} in exile ceases to exist"
  | none => g

/-- `o` becomes prepared: its controller creates a copy of its prepare spell
in exile and may cast that copy while `o` stays prepared (ruling 742). A
creature without a prepare spell can't become prepared (ruling 747), and a
prepared creature can't become prepared again (ruling 743). Only the printed
prepare spell is copied, so copy exceptions on `o` don't apply (ruling 741). -/
def becomePrepared (g : Game) (o : GameObject) (cause : Option EventCause := none) : Game :=
  let oName := g.name o
  match (g.baseCard o).prepareFace with
  | none => g.logMsg s!"{oName} has no prepare spell and can't become prepared"
  | some face =>
    if o.status.prepared then g.logMsg s!"{oName} is already prepared"
    else
      let p := (g.controllerOf o).getD o.owner
      let srcFallback := (g.currentResolvingContext?.bind Prod.fst).orElse (fun _ => some o.id)
      let batchCause :=
        g.resolveOptionalCause cause (fallbackSrc := srcFallback) (fallbackCtrl := some p)
          (defaultCause := .gameRule .spellCast)
      let g := g.withBatchCore (some batchCause) fun g =>
        let g := g.createPreparedCopy o face (cause := cause)
        let prepCause :=
          g.resolveOptionalCause cause (fallbackSrc := srcFallback) (fallbackCtrl := some p)
            (defaultCause := .gameRule .spellCast)
        g.record (GameEvent.designation g.turnNumber (g.snapshot o) .prepared true (cause := prepCause))
      g.logMsg s!"{oName} becomes prepared. A copy of {face.name} is exiled"

/-- `o` stops being prepared and the copy of its prepare spell in exile
ceases to exist. Nothing happens if it isn't prepared (ruling 737). -/
def unprepare (g : Game) (o : GameObject) (cause : Option EventCause := none) : Game :=
  if !o.status.prepared then g
  else
    let oName := g.name o
    let srcFallback := (g.currentResolvingContext?.bind Prod.fst).orElse (fun _ => some o.id)
    let resolvedCause :=
      g.resolveOptionalCause cause (fallbackSrc := srcFallback) (fallbackCtrl := g.controllerOf o)
        (defaultCause := .gameRule .spellCast)
    let g := g.record (GameEvent.designation g.turnNumber (g.snapshot o) .prepared false (cause := resolvedCause))
    (g.removePreparedCopy o.id).logMsg s!"{oName} is no longer prepared"

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
        activeEffects := g.openBatchEffects
        stack := g.openBatchStack }
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
    -- CR 702.34a: flashback exiles the spell whenever it would leave the stack for anywhere
    -- else — but only a spell actually cast via Flashback (`castViaFlashback`), not any
    -- non-free graveyard cast (Bilbo's `mayCastFromGraveyard` is `CastWay.normal`).
    let hasFlashback := g.castViaFlashback old
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
            if p != q && !board.areTeammates p q then
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
      | .replacement spec d =>
        if g.durationActive d then
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
    let faceDown :=
      faceDown?.getD (dest == .battlefield && old?.any (fun o => o.zone == .stack && o.status.faceDown))
    let fromStackTime :=
      fromStackTime?.getD
        (if dest == .battlefield then (old?.filter (·.zone == .stack)).map (·.status.time) |>.getD 0 else 0)
    let enterCtrl := (controller.orElse (fun _ => old?.map (·.owner))).getD g.activePlayer
    let resolvedAttackTarget : Option AttackTarget :=
      if dest == .battlefield then g.resolveEnteringAttackTarget? enterCtrl attacking attackingTarget
      else none
    let isAttacking := resolvedAttackTarget.isSome
    (g.chainPendingReplacement
      (.move id dest controller verb actor faceDown tapped
        isAttacking resolvedAttackTarget nightBack returnedAsArtifact onlyFoodArtifact
        extraEntersWith libraryPosition fromStackTime applyHope preBattlefield
        isCopy overridePrinted adventurerCard summoningSick attachedTo enterMods cause),
     id)
  else
  match g.findObject? id with
  | none => (g, id)
  | some old =>
  -- CR 111.8: a token that has left the battlefield can't move to another zone
  -- or come back onto the battlefield.
  if old.printed.isToken && old.zone != .battlefield then
    (g, id)
  else
  let (g, (newId, headSource, didMove)) :=
    g.withBatchCoreReturn cause fun g =>
      let (board, boardOld) := preBatchBoardFor g old
      let enterCtrl := controller.getD old.owner
      let resolvedAttackTarget : Option AttackTarget :=
        if dest == .battlefield then g.resolveEnteringAttackTarget? enterCtrl attacking attackingTarget
        else none
      let isAttacking := resolvedAttackTarget.isSome
      let beforeSnap := board.snapshot boardOld
      let sourceCtrlTargets : Array ObjectId :=
        if old.zone != .battlefield || dest == .battlefield then #[]
        else
          let sourceCtrlIds := g.activeEffects.filterMap fun (eid, e) =>
            match e with
            | .layered _ (.control _) (.whileSourceOnBattlefield s)
            | .layered _ (.control _) (.untilSourceLeaves s)
            | .layered _ (.control _) (.whileSourceHasCounter s _) =>
              if s == old.id then some eid else none
            | _ => none
          if sourceCtrlIds.isEmpty then #[]
          else
            g.objects.filterMap fun pObj =>
              if pObj.isBattlefieldObject && pObj.id != old.id &&
                  (g.appliedControlEffectIds pObj).any (fun eid => sourceCtrlIds.contains eid) then
                some pObj.id
              else none
      let buildArrival (g : Game) (targetZone : Zone) (asOf : Nat)
          (applied : Array ReplacementId := #[]) (curCause : Option EventCause := cause) :
          GameObject × CounterBag × Nat × Bool × Bool × Array ReplacementId × Option EventCause × Option (PlayerId × Array ReplacementId) × Option (CardDef × CardDef) × Bool :=
        let newId : ObjectId := ⟨g.nextObjectId⟩
        let ts := g.timestamp + 1
        let leavingPlay :=
          (old.zone == .battlefield || old.zone == .stack) &&
            targetZone != .battlefield && targetZone != .stack
        let printed0 :=
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
        -- CR 608.3f / 707.10f: a resolving or entering copy of a permanent becomes
        -- a token as it enters the battlefield.
        let printed :=
          if (isCopy.getD old.isCopy) && targetZone == .battlefield && !printed0.isToken then
            { printed0 with
              isToken := true
              otherFace := printed0.otherFace.map fun f => { f with isToken := true } }
          else printed0
        let faceDown := faceDown?.getD (targetZone == .battlefield && old.zone == .stack && old.status.faceDown)
        let fromStackTime :=
          fromStackTime?.getD (if targetZone == .battlefield && old.zone == .stack then old.status.time else 0)
        let prepared :=
          targetZone == .battlefield && !faceDown && printed.entersPrepared
        let preImpendingNotCreature :=
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
          -- CR 704.5e / 707.10a / 707.12: preserve `isCopy` across any non-battlefield
          -- zone transition so countered/bounced copies moved again before SBAs run
          -- still cease to exist via `ceasedToExist`, while playable exiled card copies
          -- remain copies on `.exile → .stack` and become tokens on `.battlefield`.
          isCopy := isCopy.getD
            (if targetZone != .battlefield then old.isCopy else false)
          isCommander := old.isCommander
          adventurerCard := if targetZone == .stack then adventurerCard.orElse (fun _ => old.adventurerCard) else none
          attachedTo := if targetZone == .battlefield then attachedTo else none
          chosenX := if targetZone == .stack then old.chosenX else none
        }
        if targetZone == .battlefield then
          let gForArrival : Game := Id.run do
            let mut g' := g
            if preImpendingNotCreature then
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
              (nonCastBattlefield := old.zone != .stack || attachedTo.isNone)
              (preBattlefield := preBattlefield)
          let postImpendingNotCreature :=
            preImpendingNotCreature && (etb.choice?.isSome || etb.entersWith.count .time > 0)
          (etb.candidate, etb.entersWith, etb.weaverBonus, postImpendingNotCreature, faceDown, etb.applied, etb.cause, etb.choice?, etb.tempCopyUntilEot, etb.stayInOriginNoAuraHost)
        else
          (candidate, #[], 0, preImpendingNotCreature, faceDown, applied, curCause, none, none, false)
      -- Run the CR 616.1 replacement loop for leaving/destination replacements (CR 614.6).
      let origDest := dest
      let moveRep :=
        g.replaceZoneMove old beforeSnap dest (verb := verb) (actor := actor)
          (libraryPosition := libraryPosition) (preBattlefield := preBattlefield)
          (cause := cause)
      let dest := moveRep.dest
      let (preCheckArrivalChoice?, preCheckStayNoAuraHost, preCheckAllApplied) :=
        if moveRep.choice?.isNone && dest == .battlefield then
          let (_, _, _, _, _, app, _, ch?, _, stayNoHost) := buildArrival g dest g.timestamp moveRep.applied moveRep.cause
          (ch?, stayNoHost, app)
        else (none, false, moveRep.applied)
      match moveRep.choice?.orElse (fun _ => preCheckArrivalChoice?) with
      | some (chooser, choices) =>
        let faceDown := faceDown?.getD (origDest == .battlefield && old.zone == .stack && old.status.faceDown)
        let fromStackTime := fromStackTime?.getD (if origDest == .battlefield && old.zone == .stack then old.status.time else 0)
        (g.promptChooseReplacement chooser choices
          (.move id origDest controller verb actor faceDown tapped
            isAttacking resolvedAttackTarget nightBack returnedAsArtifact onlyFoodArtifact
            extraEntersWith libraryPosition fromStackTime applyHope preBattlefield
            isCopy overridePrinted adventurerCard summoningSick attachedTo enterMods cause),
         (id, none, false))
      | none =>
      if preCheckStayNoAuraHost then
        let g := g.consumeReplacementOrder preCheckAllApplied
        let oldName := g.name old
        if old.zone == .stack then
          if old.isCopy then
            (g.ceaseToExist old.id (cause := some (.stateBased .copyOutsideStackOrBf))
              |>.logMsg s!"{oldName} ceases to exist (can't be attached legally; CR 303.4g / 704.5e)",
             (old.id, none, false))
          else
            let (g', gyId) :=
              g.move old.id (.graveyard old.owner) none (verb := verb) (actor := actor) (cause := cause)
            let msg := s!"{oldName} goes to the graveyard (can't be attached legally; CR 303.4g)"
            -- CR 614.6: log only once the Aura actually reaches its owner's graveyard.
            if let .chooseReplacement .. := g'.pending then
              (g'.chainPendingReplacement
                  (.finishPostStep (.logDiscardIfInGraveyard old.id old.owner msg)),
                (gyId, none, false))
            else if (g'.followMovedToZone? old.id (· == .graveyard old.owner)).isSome then
              (g'.logMsg msg, (gyId, none, false))
            else
              (g', (gyId, none, false))
        else if old.zone == .exile then
          (g.logMsg s!"{oldName} remains in exile (can't be attached legally; CR 303.4f / CR 614.6)",
           (id, none, false))
        else
          (g.logMsg s!"{oldName} remains in its current zone (can't be attached legally; CR 303.4f)",
           (id, none, false))
      else
      let exileInstead := moveRep.exileInstead
      let finalityExile := moveRep.finalityExile
      let headSource := moveRep.headSource
      let finalDiscarded :=
        verb == some .discard ||
          match old.zone, origDest with
          | .hand p, .graveyard q => p == q
          | _, _ => false
      let oldName := g.name old
      let g :=
        if finalityExile then
          g.logMsg s!"A finality counter exiles {oldName} instead of putting it into a graveyard"
        else g
      let g :=
        if old.zone == .battlefield then g.unattachFrom id else g
      -- The copy of a prepare spell stays in exile only while its permanent is
      -- on the battlefield (ruling 742).
      let g :=
        if old.zone == .battlefield then g.removePreparedCopy id else g
      let asOf := g.timestamp
      let (fresh, entersWith, weaverBonus, impendingNotCreature, _faceDown, allApplied, finalCause, _, tempCopyUntilEot, _) :=
        buildArrival g dest asOf moveRep.applied moveRep.cause
      let g := g.consumeReplacementOrder allApplied
      let newId := fresh.id
      let g :=
        if exileInstead then
          -- CR 700.4: only a battlefield-to-graveyard move is "dying".
          if old.zone == .battlefield then
            g.logMsg s!"{oldName} is exiled instead of dying (CR 614.6)"
          else
            match origDest with
            | .graveyard _ =>
              g.logMsg s!"{oldName} is exiled instead of going to a graveyard (CR 614.6)"
            | _ =>
              -- CR 702.34a: a stack-leave replacement to a non-graveyard zone.
              g.logMsg s!"{oldName} is exiled instead of leaving the stack (CR 614.6)"
        else g
      let freshForSnap : GameObject :=
        match tempCopyUntilEot with
        | some (_, copyCard) =>
          let copyCard' := if fresh.printed.isToken then { copyCard with isToken := true } else copyCard
          { fresh with printed := copyCard' }
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
          Id.run do
            let mut acc := g
            for i in [0:sourceCtrlTargets.size] do
              let tid := sourceCtrlTargets[i]!
              if let some cur := acc.findObject? tid then
                if cur.isBattlefieldObject && (acc.appliedControlEffectIds cur).isEmpty then
                  let destP := (acc.controllerOf cur).getD (cur.defaultController.getD cur.owner)
                  if !acc.stillInGame destP then
                    let name := acc.name cur
                    let (acc', _) := acc.move tid .exile none (cause := some (.gameRule .playerLeftGame))
                    acc := acc'
                    if let .chooseReplacement .. := acc.pending then
                      let rem := (sourceCtrlTargets.extract (i + 1) sourceCtrlTargets.size).filterMap fun rid =>
                        (acc.findObject? rid).bind fun ro =>
                          if ro.isBattlefieldObject && (acc.appliedControlEffectIds ro).isEmpty then
                            let dp := (acc.controllerOf ro).getD (ro.defaultController.getD ro.owner)
                            if !acc.stillInGame dp then some (rid, s!"{acc.name ro} is exiled (CR 800.4c)") else none
                          else none
                      acc := acc.chainPendingReplacement
                        (.endControlExileLoop rem (some (.gameRule .playerLeftGame))
                          (some (tid, s!"{name} is exiled (CR 800.4c)")))
                      return acc
                    if !(acc.findObject? tid).any (·.isBattlefieldObject) then
                      acc := acc.logMsg s!"{name} is exiled (CR 800.4c)"
            return acc
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
          g.logMsg s!"{g.nameWithToken (g.object! newId)} enters with {weaverBonus} additional +1/+1 counter(s)"
        else g
      (g, (newId, headSource, true))
  if !didMove then (g, newId)
  else
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
          if !g.stillInGame p then g
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

/-- Emit the return log for a CR 610.3 `linkedExile` object once its zone change
has actually placed it in `dest`. -/
private partial def logLinkedExileReturn (g : Game) (fromId : ObjectId) (dest : Zone) : Game :=
  match g.followMovedToZone? fromId (· == dest) with
  | none => g
  | some moved =>
    match dest with
    | .hand p =>
      g.logMsg s!"{g.name moved} returns to {(g.player p).name}'s hand"
    | .graveyard p =>
      g.logMsg s!"{g.name moved} returns to {(g.player p).name}'s graveyard"
    | .battlefield =>
      match moved.attachedTo with
      | some hid =>
        let hostName := (g.findObject? hid).map g.name |>.getD (toString hid)
        g.logMsg s!"{g.name moved} returns attached to {hostName} (does not target)"
      | none =>
        g.logMsg s!"{g.name moved} returns to the battlefield"
    | _ => g

/-- Execute a batch of CR 610.3 linked-exile returns inside an open post-departure
batch, checking returning Auras against `preBattlefield` (CR 303.4f) and pausing
via `PendingReplacement.finishLinkedExileMove` if a return opens a choice. -/
partial def runLinkedExileBatch (g : Game) (ids : Array ObjectId)
    (preBattlefield : Option (Array GameObject) := none)
    (pendingLog : Option (ObjectId × Zone) := none)
    (enteredFromIds : Array ObjectId := #[]) : Game :=
  if ids.isEmpty && pendingLog.isNone && enteredFromIds.isEmpty then g
  else if match g.pending with | .chooseReplacement .. | .chooseLegend .. => true | _ => false then
    g.chainPendingReplacement (.finishLinkedExileMove ids preBattlefield pendingLog enteredFromIds)
  else Id.run do
    let preBf := preBattlefield.getD g.battlefield
    let mut g := g
    let mut entered := enteredFromIds
    if let some (fromId, dest) := pendingLog then
      g := logLinkedExileReturn g fromId dest
    for i in [0:ids.size] do
      let exId := ids[i]!
      match g.findObject? exId with
      | some o =>
        if o.zone == .exile then
          let name := g.name o
          let linkCause := g.lastMoveCauseOf? o.id
          let (g', movedDest?) : Game × Option Zone :=
            match o.returnToZone with
            | some (.hand p) =>
              if !g.stillInGame p then
                (g.logMsg s!"{name} remains in its current zone (CR 800.4a)", none)
              else
                let (g', _) := g.move o.id (.hand p) none (cause := linkCause)
                (g', some (.hand p))
            | some (.graveyard p) =>
              if !g.stillInGame p then
                (g.logMsg s!"{name} remains in its current zone (CR 800.4a)", none)
              else
                let (g', _) := g.move o.id (.graveyard p) none (cause := linkCause)
                (g', some (.graveyard p))
            | _ =>
              if !g.stillInGame o.owner then
                (g.logMsg s!"{name} remains in its current zone (CR 800.4b)", none)
              else
                let (g', _) :=
                  g.move o.id .battlefield (some o.owner) (preBattlefield := some preBf)
                    (cause := linkCause)
                let movedDest? :=
                  if (g'.followMovedToZone? o.id (· == .battlefield)).isSome ||
                      (match g'.pending with | .chooseReplacement .. => true | _ => false) then
                    some .battlefield
                  else none
                (g', movedDest?)
          g := g'
          if movedDest? == some .battlefield then
            entered := entered.push o.id
          if match g.pending with | .chooseReplacement .. | .chooseLegend .. => true | _ => false then
            let rem := ids.extract (i + 1) ids.size
            let logItem := movedDest?.map (fun d => (o.id, d))
            if !rem.isEmpty || logItem.isSome || !entered.isEmpty then
              g := g.chainPendingReplacement (.finishLinkedExileMove rem (some preBf) logItem entered)
            return g
          if let some dest := movedDest? then
            g := logLinkedExileReturn g o.id dest
      | none => pure ()
    for k in [0:entered.size] do
      let fromId := entered[k]!
      if let some enteredObj := g.followMovedToZone? fromId (· == .battlefield) then
        g := g.afterPermanentEntersInBatch enteredObj
        if match g.pending with | .chooseReplacement .. | .chooseLegend .. => true | _ => false then
          let remEntered := entered.extract (k + 1) entered.size
          if !remEntered.isEmpty then
            g := g.chainPendingReplacement (.finishLinkedExileMove #[] (some preBf) none remEntered)
          return g
    return g

/-- Flush any CR 610.3 `linkedExile` returns queued while an enclosing departure
batch was open once the outermost batch has closed. -/
partial def flushQueuedLinkedExile (g : Game) : Game :=
  if g.currentBatch.isSome || g.queuedLinkedExile.isEmpty then g
  else
    let ids := g.queuedLinkedExile
    let g := g.change .clearQueuedLinkedExile
    g.returnLinkedExileMoves ids

/-- Return CR 610.3 linked-exile cards in a separate post-departure batch once
any enclosing departure batch closes (CR 610.3 / 603.10), pausing via
`PendingReplacement.finishLinkedExileMove` if a choice is currently open. -/
partial def returnLinkedExileMoves (g : Game) (ids : Array ObjectId) : Game :=
  if ids.isEmpty then g
  else if g.currentBatch.isSome then
    g.change (.queueLinkedExile ids)
  else if match g.pending with | .chooseReplacement .. | .chooseLegend .. => true | _ => false then
    g.chainPendingReplacement (.finishLinkedExileMove ids none)
  else
    let g := g.withBatchCore none fun g => g.runLinkedExileBatch ids none
    g.flushQueuedLinkedExile

end

/-- Run `f` inside an event batch (`Core.withBatchCoreReturn`), then flush any
CR 610.3 `linkedExile` returns queued while the batch was open once the
outermost batch closes. -/
def withBatchReturn {α : Type} (g : Game) (cause : Option EventCause := none)
    (f : Game → Game × α) : Game × α :=
  let (g', res) := g.withBatchCoreReturn cause f
  (g'.flushQueuedLinkedExile, res)

/-- Run `f` inside an event batch and flush deferred CR 610.3 `linkedExile` returns. -/
def withBatch (g : Game) (cause : Option EventCause := none) (f : Game → Game) : Game :=
  (g.withBatchReturn cause (fun g => (f g, ()))).1

/-- Monadic `Except` variant of `withBatchReturn`. -/
def withBatchExcept {ε α : Type} (g : Game) (cause : Option EventCause := none)
    (f : Game → Except ε (Game × α)) : Except ε (Game × α) :=
  let (g', res) :=
    g.withBatchReturn cause fun g0 =>
      match f g0 with
      | .ok (g1, a) => (g1, Except.ok a)
      | .error err => (({} : Game), Except.error err)
  res.map (fun a => (g', a))

/-- Monadic `Except` variant of `withBatch`. -/
def withBatchM {ε : Type} (g : Game) (cause : Option EventCause := none)
    (f : Game → Except ε Game) : Except ε Game :=
  (g.withBatchExcept cause fun g0 => do return (← f g0, ())).map Prod.fst

/-- Reverse to the saved CR 733.1–733.2 proposal checkpoint, re-running batches
and flushing any CR 610.3 `linkedExile` returns from kept irreversible moves. -/
def reverseToProposalCheckpoint? (g : Game) : Except String Game :=
  g.reverseToProposalCheckpointCore? (fun g0 f => g0.withBatch none f)

/-- Close a paused batch (`Core.finishOpenBatch`) and flush any CR 610.3
`linkedExile` returns once the outermost batch closes. -/
def finishOpenBatchAndLinkedExile (g : Game) (batchId : BatchId) (startIdx : Nat) : Game :=
  (g.finishOpenBatch batchId startIdx).flushQueuedLinkedExile

/-- Emit the post-move log for `moveToOwnerGraveyard` once `fromId` finishes its
CR 616.1 replacement loop, suppressing false graveyard logs when redirected to
`.exile` or `.library` (CR 614.6). A sacrifice (`verb == some .sacrifice`) logs
only on arrival in `owner`'s graveyard (CR 614.6 / 701.21a). -/
def finishMoveToOwnerGraveyardLog (g : Game) (fromId : ObjectId) (fromZone : Zone)
    (owner : PlayerId) (cardName reason : String) (verb : Option ZoneVerb) : Game :=
  match g.followMovedToZone? fromId (fun _ => true) with
  | none => g
  | some arrived =>
    if arrived.zone == .graveyard owner then
      g.logMsg reason
    else if verb == some .sacrifice then g
    else
      let isFalseGraveyardLog :=
        (reason.splitOn "goes to the graveyard").length > 1 ||
          (reason.splitOn "into its owner's graveyard").length > 1 ||
          (reason.splitOn "into their graveyard").length > 1
      if isFalseGraveyardLog then
        if arrived.zone == .exile && fromZone == .stack then
          g.logMsg s!"{cardName} is exiled"
        else g
      else
        g.logMsg reason

/-- Move `o` to its owner's graveyard and log `reason` after replacement choices
resolve, suppressing false graveyard logs when redirected (CR 614.1 / 614.6). -/
def moveToOwnerGraveyard (g : Game) (o : GameObject) (reason : String)
    (verb : Option ZoneVerb := none) (actor : Option PlayerId := none)
    (preBattlefield : Option (Array GameObject) := none)
    (cause : Option EventCause := none) : Game :=
  let fromId := o.id
  let fromZone := o.zone
  let owner := o.owner
  let cardName := g.name o
  let (g, _) := g.move fromId (.graveyard owner) none (verb := verb) (actor := actor)
    (preBattlefield := preBattlefield) (cause := cause)
  if let .chooseReplacement .. := g.pending then
    g.chainPendingReplacement
      (.finishPostStep (.finishMoveToOwnerGraveyardLog fromId fromZone owner cardName reason verb))
  else
    g.finishMoveToOwnerGraveyardLog fromId fromZone owner cardName reason verb

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
        g := g.moveToOwnerGraveyard o s!"{g.name o} is put into its owner's graveyard"
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
    (preBattlefield : Option (Array GameObject) := none)
    (verb : Option ZoneVerb := none) (actor : Option PlayerId := none)
    (cause : Option EventCause := none) : Game × ObjectId :=
  if !g.stillInGame controller then
    let name := g.name (g.object! id)
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
      (preBattlefield := preBattlefield)
      (verb := verb) (actor := actor) (cause := cause)

/-- Complete the post-move permission and log step of `counterStackSpell` once
any CR 616.1 replacement choice on the stack-leave move has resolved. -/
def finishCounterStackSpell (g : Game) (spellId : ObjectId) (grantFreeCast : Bool)
    (ctrl : Option PlayerId) (cause : EventCause) (name : String) : Game :=
  let arrived? := g.followMovedToZone? spellId (· != .stack)
  let inExile := arrived?.any (·.zone == .exile)
  let g :=
    match ctrl, arrived? with
    | some c, some arrived =>
      if inExile && grantFreeCast then
        g.createEffect (.playPermission arrived.id {
          player := c
          whileExiled := true
          withoutManaCost := true }) (cause := some cause)
      else g
    | _, _ => g
  let destNote := if inExile then "exiled" else "countered"
  g.logMsg s!"{name} is {destNote}"

/-- Counter a spell on the stack (CR 701.6). `exilePermanent` puts a permanent
spell into exile and `grantFreeCast` may grant a free cast (CR 701.5 /
Thranduil's Decree). -/
def counterStackSpell (g : Game) (spellId : ObjectId) (exilePermanent := false)
    (grantFreeCast := false) (controller : Option PlayerId := none) : Game :=
  let ctrl := controller.orElse (fun _ => g.currentResolvingContext?.bind Prod.snd)
  if let .chooseReplacement .. := g.pending then
    g.chainPendingReplacement
      (.counterStackSpell spellId exilePermanent grantFreeCast ctrl none false "")
  else
  match g.findObject? spellId with
  | none => g.logMsg "The spell is no longer on the stack"
  | some o =>
    if o.zone != .stack then
      g.logMsg s!"{g.name o} is no longer on the stack"
    else if o.abilityEffect.isSome || o.triggeredAbility.isSome then
      let name := g.name o
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
      let name := g.name o
      let (g, cause) : Game × EventCause :=
        match g.currentResolvingContext? with
        | some _ => g.allocDelayedCause ctrl
        | none => (g, .gameRule .spellCast)
      let (g, _) := g.move spellId dest none
        (verb := some .counter) (actor := ctrl) (cause := some cause)
      if let .chooseReplacement .. := g.pending then
        g.chainPendingReplacement
          (.counterStackSpell spellId exilePermanent grantFreeCast ctrl (some cause) true name)
      else
        g.finishCounterStackSpell spellId grantFreeCast ctrl cause name

/-- Sacrifice `o` to its owner's graveyard (CR 701.21a). -/
def sacrificeToGraveyard (g : Game) (o : GameObject) (reason : String)
    (cause : Option EventCause := none)
    (preBattlefield : Option (Array GameObject) := none) : Game :=
  let actor := (g.controllerOf o).getD o.owner
  g.moveToOwnerGraveyard o reason (verb := some .sacrifice) (actor := some actor)
    (preBattlefield := preBattlefield) (cause := cause)

/-- First player in `players` who satisfies `pred`, plus those after them. -/
def nextActorWhere (_g : Game) (players : Array PlayerId) (pred : PlayerId → Bool) :
    Option (PlayerId × Array PlayerId) :=
  Id.run do
    for i in [0:players.size] do
      let p := players[i]!
      if pred p then
        return some (p, players.extract (i + 1) players.size)
    return none

/-- First player in `players` who controls a creature, plus those after them. -/
def nextActorWithCreatures (g : Game) (players : Array PlayerId) :
    Option (PlayerId × Array PlayerId) :=
  g.nextActorWhere players (fun p =>
    g.stillInGame p && !(g.creaturesControlledBy p).isEmpty)

/-- First player in `players` who has a card in hand, plus those after them. -/
def nextActorWithHandCard (g : Game) (players : Array PlayerId) :
    Option (PlayerId × Array PlayerId) :=
  g.nextActorWhere players (fun p =>
    g.stillInGame p && !(g.player p).hand.isEmpty)

/-- Sacrifice each `(actor, oid)` in `remaining` sequentially inside an open or
standalone batch, pausing on `Pending.chooseReplacement` and optionally creating
a 4/4 Beast token if `createBeastFor` is set. -/
def sacrificePermanentsLoop (g : Game) (remaining : Array (PlayerId × ObjectId))
    (preBattlefield : Option (Array GameObject) := none)
    (cause : Option EventCause := none)
    (createBeastFor : Option PlayerId := none)
    (passiveLog : Bool := false) : Game := Id.run do
  if let .chooseReplacement .. := g.pending then
    return g.chainPendingReplacement
      (.sacrificePermanentsLoop remaining preBattlefield cause createBeastFor passiveLog)
  let mut g := g
  let preBf := preBattlefield.getD g.battlefield
  for i in [0:remaining.size] do
    let (who, id) := remaining[i]!
    match g.findObject? id with
    | some o =>
      if o.isOnBattlefield then
        let msg :=
          if passiveLog then s!"{g.name o} is sacrificed"
          else s!"{(g.player who).name} sacrifices {g.name o}"
        g := g.sacrificeToGraveyard o msg
          (cause := cause) (preBattlefield := some preBf)
        if let .chooseReplacement .. := g.pending then
          let rem := remaining.extract (i + 1) remaining.size
          if !rem.isEmpty || createBeastFor.isSome then
            g := g.chainPendingReplacement
              (.sacrificePermanentsLoop rem (some preBf) cause createBeastFor passiveLog)
          return g
    | none => pure ()
  if let some ctrl := createBeastFor then
    g := g.createKindTokens ctrl .beast44trample 1 (cause := cause)
  return g

/-- Sacrifice the chosen creatures simultaneously. -/
def finishChosenSacrifices (g : Game) (chosen : Array ObjectId) : Game :=
  let pairs := chosen.filterMap (fun id =>
    match g.findObject? id with
    | some o =>
      if o.isOnBattlefield && g.isCreature o then
        some ((g.controllerOf o).getD o.owner, id)
      else none
    | none => none)
  let preBf := g.battlefield
  let g := if g.pending != .none then g.change (.pending .none) else g
  g.withBatch none fun g =>
    g.sacrificePermanentsLoop pairs (preBattlefield := some preBf)

/-- Log `msg` for each player in `ps`. -/
def logForPlayers (g : Game) (ps : Array PlayerId) (msg : PlayerId → String) : Game :=
  ps.foldl (fun g p => g.logMsg (msg p)) g

/-- Display name for an `EnteringAttackItem` in choice logs. -/
def enteringAttackItemName (g : Game) : EnteringAttackItem → String
  | .token _ kind _ _ tokenName => tokenName.getD (tokenPrinted kind).name
  | .card cardId .. =>
    match g.findObject? cardId with
    | some o => g.name o
    | none => "the creature"

/-- Advance `remaining` past any items whose attack target is already fixed
(`options.size <= 1`), appending `(item, item.options[0]?)` to `chosen`. -/
def advanceFixedEnteringAttackItems
    (remaining : Array EnteringAttackItem)
    (chosen : Array (EnteringAttackItem × Option AttackTarget)) :
    Array EnteringAttackItem × Array (EnteringAttackItem × Option AttackTarget) := Id.run do
  let mut idx := 0
  let mut acc := chosen
  while idx < remaining.size && remaining[idx]!.options.size <= 1 do
    let item := remaining[idx]!
    acc := acc.push (item, item.options[0]?)
    idx := idx + 1
  return (remaining.extract idx remaining.size, acc)

/-- Move each card in `ids` sequentially into its owner's graveyard, pausing
via `PendingReplacement.moveCardsToGraveyardLoop` if any card opens a CR 616.1
`Pending.chooseReplacement` choice. -/
def moveCardsToGraveyardLoop (g : Game) (ids : Array ObjectId)
    (cause : Option EventCause := none) : Game :=
  if ids.isEmpty then g
  else if let .chooseReplacement .. := g.pending then
    g.chainPendingReplacement (.moveCardsToGraveyardLoop ids cause)
  else
    Id.run do
      let mut g := g
      for i in [0:ids.size] do
        let id := ids[i]!
        if let some o := g.findObject? id then
          g := (g.move id (.graveyard o.owner) none (cause := cause)).1
          if let .chooseReplacement .. := g.pending then
            let rem := ids.extract (i + 1) ids.size
            if !rem.isEmpty then
              g := g.chainPendingReplacement (.moveCardsToGraveyardLoop rem cause)
            return g
      return g

end Game
end Mtg.Engine
