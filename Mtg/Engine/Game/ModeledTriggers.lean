import Mtg.Engine.Game.ResolutionEffects

/-!
# Modeled trigger resolution

`applyModeledTrigger` — resolving the shared-trigger payloads — leftover
rules-text effects, and boast, teamwork, and pay-or-counter helpers.
-/

namespace Mtg.Engine
namespace Game

/-- The lone attacking creature `p` controls, if exactly one creature on the
battlefield is attacking (CR 506.5). -/
def attackingAlone? (g : Game) (p : PlayerId) : Option GameObject :=
  let all := g.battlefield.filter (fun o => g.isCreature o && o.status.attacking)
  if all.size == 1 && g.controlledBy all[0]! p then some all[0]! else none

/-- Permanent this Aura or Equipment is attached to. -/
def attachedHost? (g : Game) (sourceId : Option ObjectId) : Option GameObject :=
  sourceId.bind g.findObject? |>.bind (fun src => src.attachedTo.bind g.findObject?)

/-- The spell that caused the resolving cast trigger, if still on the stack. -/
def castTriggerSpell? (g : Game) : Option GameObject :=
  ((g.resolvingAbility.bind g.findObject?).bind (·.fraCauseId)).bind
    (fun id => (g.findObject? id).filter (·.zone == .stack))

/-- Newest non-ability object on the stack (the spell that caused a cast trigger). -/
def lastStackSpell? (g : Game) : Option GameObject :=
  g.stack.foldl (fun acc e =>
    match g.findObject? e.objectId with
    | some o =>
      if o.triggeredAbility.isNone && o.abilityEffect.isNone then some o else acc
    | none => acc) none

/-- 1/1 blue Merfolk creature token (Namora / similar leftover cast triggers). -/
def merfolk11blueToken : CardDef :=
  creatureToken "Merfolk" #[.merfolk] 1 1 (some .blue)

/-- Ask the next player in `players` with a nontoken creature to choose one
to sacrifice; once all have chosen, sacrifice them together. -/
def continueNontokenSacrifices (g : Game) (players : Array PlayerId) (chosen : Array ObjectId) :
    Game :=
  let hasOne (p : PlayerId) := (g.permanentsOf p).any (fun o => g.isCreature o && !o.printed.isToken)
  match (players.filter hasOne).toList with
  | p :: rest =>
    (g.change (.pending (.fraChoice p (.sacrificeNontokenEach rest.toArray chosen)))).logMsg
      s!"{(g.player p).name} sacrifices a nontoken creature"
  | [] =>
    let pairs := chosen.filterMap (fun id =>
      match g.findObject? id with
      | some o =>
        if o.isOnBattlefield then
          some ((g.controllerOf o).getD o.owner, id)
        else none
      | none => none)
    let preBf := g.battlefield
    g.withBatch none fun g =>
      g.sacrificePermanentsLoop pairs (preBattlefield := some preBf)

/-- Let `controller` cast the exiled nonland with any type of mana until end of turn. -/
def grantWidowCast (g : Game) (controller : PlayerId) (exiled : Option ObjectId)
    (cause : Option EventCause := none) : Game :=
  match exiled.bind g.findObject? with
  | none => g.logMsg "No nonland card was exiled"
  | some o =>
    let cause := cause.orElse (fun _ => g.lastMoveCauseOf? o.id)
    g.createEffect (.playPermission o.id {
      player := controller
      anyMana := true }) (cause := cause)
      |>.logMsg s!"{(g.player controller).name} may cast {o.name} until end of turn"

/-- Finish Black Widow's combat-damage trigger once `exileLibraryUntilNonlandLoop`
stops on a nonland card or an empty library (CR 616.1). -/
def finishExileLibraryUntilNonland (g : Game) (controller : PlayerId)
    (sourceId : Option ObjectId) (nonland? : Option ObjectId)
    (cause : Option EventCause) : Game :=
  let onBf := (sourceId.bind g.findObject?).any (·.isOnBattlefield)
  if onBf then
    g.change (.pending (.fraChoice controller (.widowMayCounter sourceId nonland?)))
      |>.logMsg "You may put a +1/+1 counter on Black Widow"
  else
    g.grantWidowCast controller nonland? (cause := cause)

/-- Pause-safe loop exiling from `pid`'s library until a nonland card is exiled,
then finishing Black Widow's counter/cast prompt (CR 614.6 / 616.1). -/
partial def exileLibraryUntilNonlandLoop (g : Game) (pid controller : PlayerId)
    (sourceId : Option ObjectId) (cause : Option EventCause)
    (pendingFromId : Option ObjectId := none) : Game :=
  match pendingFromId with
  | some fid =>
    if let .chooseReplacement .. := g.pending then
      g.chainPendingReplacement
        (.finishPostStep (.exileLibraryUntilNonlandLoop pid controller sourceId cause (some fid)))
    else
      match g.followMovedToZone? fid (· == .exile) with
      | some o =>
        let g := g.logMsg s!"{(g.player pid).name} exiles {o.name}"
        if !g.isLand o then
          g.finishExileLibraryUntilNonland controller sourceId (some o.id) cause
        else
          g.exileLibraryUntilNonlandLoop pid controller sourceId cause none
      | none =>
        g.exileLibraryUntilNonlandLoop pid controller sourceId cause none
  | none =>
    if let .chooseReplacement .. := g.pending then
      g.chainPendingReplacement
        (.finishPostStep (.exileLibraryUntilNonlandLoop pid controller sourceId cause none))
    else
      match (g.player pid).library.back? with
      | none =>
        g.finishExileLibraryUntilNonland controller sourceId none cause
      | some id =>
        let (g, _) := g.move id .exile none (cause := cause)
        if let .chooseReplacement .. := g.pending then
          g.chainPendingReplacement
            (.finishPostStep (.exileLibraryUntilNonlandLoop pid controller sourceId cause (some id)))
        else
          g.exileLibraryUntilNonlandLoop pid controller sourceId cause (some id)

/-- Finish entering and animating token(s) recorded in `recentTokenIds` for
Ultron's artifact-copy trigger (MSH 547 / 574 / 656). -/
def finishArtifactCopyTokens (g : Game) : Game :=
  let ids := g.recentTokenIds
  let g := if g.continuations.isEmpty then g else g.change (.recentTokenIds #[])
  ids.foldl (fun g tid =>
    match g.findObject? tid with
    | none => g
    | some tok =>
      if !tok.isOnBattlefield then g
      else
        let g := g.afterPermanentEnters tok
        match g.findObject? tid with
        | none => g
        | some tok =>
          if !tok.isOnBattlefield || g.isCreature tok then g
          else
            let g := g.withBatch none fun g =>
              let g := g.createEffect
                (.layered (.objects #[tok.id]) (.types .add #[.creature] #[.robot, .villain] #[]) .indefinite)
              g.createEffect
                (.layered (.objects #[tok.id]) (.ptSet 2 2) .indefinite)
            g.logMsg s!"{g.name tok} becomes a 2/2 Robot Villain creature after it enters") g

/-- Copy the nontoken artifact that entered (using `lastKnownBefore?` LKI if it
has already left the battlefield; CR 608.2h / 707.12 / MSH 547 / 656), then make
a noncreature token a 2/2 Robot Villain after it enters (MSH 574). -/
def copyEnteredArtifact (g : Game) (controller : PlayerId) (artifactId : ObjectId) : Game :=
  if let .chooseReplacement .. := g.pending then
    g.chainPendingReplacement (.finishPostStep (.copyEnteredArtifact controller artifactId))
  else
  let copiableRes : Except String CardDef :=
    match g.findObject? artifactId with
    | some src =>
      if src.isOnBattlefield then
        if src.printed.isToken || !g.isArtifact src then
          .error "That permanent isn't a nontoken artifact"
        else
          .ok (g.copiableValues src)
      else
        match g.lastKnownBefore? artifactId with
        | some eo =>
          if eo.token || !eo.artifact then .error "That permanent isn't a nontoken artifact"
          else .ok (eo.copiable.getD eo.toCardDef)
        | none => .error "Ultron has nothing to copy"
    | none =>
      match g.lastKnownBefore? artifactId with
      | some eo =>
        if eo.token || !eo.artifact then .error "That permanent isn't a nontoken artifact"
        else .ok (eo.copiable.getD eo.toCardDef)
      | none => .error "Ultron has nothing to copy"
  match copiableRes with
  | .error msg => g.logMsg msg
  | .ok copiable =>
    let pushedFrame := g.continuations.isEmpty
    let g := if pushedFrame then g.change (.pushContinuationFrame {}) else g
    let g := g.change (.recentTokenIds #[])
    let (g, _) := g.createToken controller copiable (recordRecent := true)
    if let .chooseReplacement .. := g.pending then
      g.chainPendingReplacement .finishArtifactCopyToken
    else
      let g := g.finishArtifactCopyTokens
      if pushedFrame && g.pending == .none && g.pendingReplacement.isNone then
        g.change .popContinuationFrame
      else g

/-- Finish pumping Daredevil after `exileTopPlayThisTurn` completes (MSH 685). -/
def finishDaredevilExile (g : Game) (sourceId : Option ObjectId)
    (top? : Option ObjectId) : Game :=
  match top?.bind (fun fid => g.followMovedToZone? fid (· == .exile)) with
  | some moved =>
    if g.hasSubtype moved .hero then
      g.withSourceOnBattlefield sourceId (fun g src => g.pumpPermanent src 2 1)
        "Daredevil is no longer on the battlefield"
    else g
  | none => g

/-- Exile the top card of your library. A Hero card pumps Daredevil. The
exiled card may be played this turn either way (MSH 685). -/
def applyDaredevilExile (g : Game) (controller : PlayerId) (sourceId : Option ObjectId) : Game :=
  let top? := (g.player controller).library.back?
  let g := g.exileTopPlayThisTurn controller 1
  if let .chooseReplacement .. := g.pending then
    g.chainPendingReplacement (.finishPostStep (.finishDaredevilExile sourceId top?))
  else
    g.finishDaredevilExile sourceId top?

/-- The Vision's chosen mode that hasn't been chosen yet this turn.
0 double strike, 1 indestructible, 2 draw. -/
def applyVisionMode (g : Game) (controller : PlayerId) (sourceId : ObjectId) (mode : Nat) : Game :=
  let chosen := g.modesChosenThisTurn sourceId
  if chosen.contains mode || chosen.size >= 3 then
    g.logMsg "The Vision's ability is removed from the stack with no effect"
  else
    match (g.findObject? sourceId).filter (·.isOnBattlefield) with
    | none =>
      if mode == 2 then g.draw controller 1
      else g.logMsg "The Vision is no longer in play"
    | some src =>
      let g := g.record (GameEvent.triggerModeChosen g.turnNumber src.id mode)
      if mode == 0 then
        g.createEffect (.keywordsUntilEot src.id Keyword.doubleStrike)
      else if mode == 1 then
        g.createEffect (.keywordsUntilEot src.id Keyword.indestructible)
      else
        g.draw controller 1

/-- Commit staged multi-slot retarget choices on `spellId` after all slots have
been answered (CR 115.3 / 115.7d / MSH 722). -/
def commitStagedSpellTargets (g : Game) (spellId : ObjectId) (staged : Array Target) : Game :=
  if staged.isEmpty then g
  else
    match g.stack.findIdx? (fun e => e.objectId == spellId), g.findObject? spellId with
    | some i, some spell =>
      let e := g.stack[i]!
      if staged == e.targets then g
      else
        let kind := (g.targetingOf spell).kind
        if g.validTargetArrayForEntry e spell kind staged (allowUnchangedIllegal := true) then
          g.setStackEntryTargets spellId staged (dividedDamage := e.dividedDamage)
            |>.logMsg "A new target is chosen for the spell"
        else
          g.logMsg "That target stays unchanged"
    | _, _ => g.logMsg "The spell is no longer on the stack"

/-- Ask to change the spell's target at `index`, then the later slots, staging
choices across slots before committing (CR 115.3 / 115.7d). -/
def offerSpellRetarget (g : Game) (controller : PlayerId) (spellId : ObjectId)
    (index : Nat) (staged : Array Target := #[]) : Game :=
  match g.stackEntry? spellId with
  | none => g
  | some e =>
    if index < e.targets.size then
      let curStaged := if staged.isEmpty then e.targets else staged
      g.change (.pending (.fraChoice controller (.mayChangeSpellTarget spellId index curStaged)))
        |>.logMsg "You may choose a new target for the spell"
    else
      g.commitStagedSpellTargets spellId staged

/-- Stage one slot of a `mayChangeSpellTarget` prompt (`index`), validating
atomic slot legality now and cross-slot constraints on final commit (CR 115.3 /
115.7d / MSH 722). -/
def stageSpellTargetAt (g : Game) (spellId : ObjectId) (index : Nat)
    (neu : Target) (staged : Array Target) : Game × Array Target :=
  match g.stack.findIdx? (fun e => e.objectId == spellId), g.findObject? spellId with
  | some i, some spell =>
    let e := g.stack[i]!
    let base := if staged.isEmpty then e.targets else staged
    if index >= e.targets.size then
      (g.logMsg "That target stays unchanged", base)
    else
      let kind := (g.targetingOf spell).kind
      let selfSource := spell.sourceId.orElse (fun _ => if spell.zone == .stack then some spell.id else none)
      let totalSlots := e.targets.size + e.skippedOptionalSlots.size
      let slotIndices : Array Nat :=
        if e.skippedOptionalSlots.isEmpty then (List.range e.targets.size).toArray
        else ((List.range totalSlots).filter (fun s => !e.skippedOptionalSlots.contains s)).toArray
      let actualSlot := slotIndices[index]?.getD index
      if !(g.legalTargetsForAtomicKind e.controller (kind.slotKind actualSlot) selfSource).contains neu then
        (g.logMsg "That target stays unchanged", base)
      else
        let cand := base.set! index neu
        if index + 1 < e.targets.size then
          (g, cand)
        else if g.validTargetArrayForEntry e spell kind cand (allowUnchangedIllegal := true) then
          (g, cand)
        else
          (g.logMsg "That target stays unchanged", base)
  | _, _ => (g.logMsg "The spell is no longer on the stack", staged)

/-- Replace one target of a spell when the replacement is legal. An illegal
choice leaves that target unchanged (MSH 722). -/
def setSpellTargetAt (g : Game) (spellId : ObjectId) (index : Nat) (neu : Target) : Game :=
  match g.stack.findIdx? (fun e => e.objectId == spellId) with
  | none => g.logMsg "The spell is no longer on the stack"
  | some i =>
    let e := g.stack[i]!
    match g.findObject? spellId with
    | none => g.logMsg "The spell is no longer on the stack"
    | some spell =>
      if index < e.targets.size then
        let kind := (g.targetingOf spell).kind
        let cand := e.targets.set! index neu
        if cand != e.targets && g.validTargetArrayForEntry e spell kind cand (allowUnchangedIllegal := true) then
          g.setStackEntryTargets spellId cand (dividedDamage := e.dividedDamage)
            |>.logMsg "A new target is chosen for the spell"
        else
          g.logMsg "That target stays unchanged"
      else
        g.logMsg "That target stays unchanged"

/-- Mister Hyde's chosen mode. Mode 0 puts a +1/+1 counter on the source.
Mode 1 removes a counter from the chosen creature, then draws. -/
def applyHydeMode (g : Game) (controller : PlayerId) (sourceId : Option ObjectId)
    (mode : Nat) (targets : Array Target) : Game :=
  if mode == 0 then
    g.withSourceOnBattlefield sourceId (fun g o =>
      g.addPlusOnePlusOneTo o 1) "The source is no longer in play"
  else
    match targets[0]? with
    | some (Target.permanent id) =>
      match g.findObject? id with
      | some o =>
        if o.isOnBattlefield && g.isCreature o && g.controlledBy o controller && o.status.hasCounters then
          let kind? : Option CounterKind :=
            if o.status.plusOnePlusOne > 0 then some .plusOnePlusOne
            else if o.status.indestructibleCounters > 0 then some .indestructible
            else o.status.toCounterBag[0]?.map (·.1)
          match kind? with
          | some kind =>
            let nm := g.name o
            let before := o.status.counterCount kind
            let g := g.recordRemoveCounters o.id kind 1 (byPlayer := some controller)
              |>.logMsg s!"A counter is removed from {nm}"
            let removed : Bool :=
              match g.findObject? o.id with
              | some cur => decide (cur.status.counterCount kind < before)
              | none => true
            if removed then g.draw controller 1 else g
          | none => g
        else
          g.logMsg "You must remove a counter from a creature you control if you can"
      | none =>
        g.logMsg "You must remove a counter from a creature you control if you can"
    | _ =>
      if (g.permanentsOf controller).any (fun o =>
          g.isCreature o && o.status.hasCounters) then
        g.logMsg "You must remove a counter from a creature you control if you can"
      else g

/-- Draw one card for the controller of the creature the source enchants.
Nothing enchanted draws nothing. -/
def drawForEnchantedController (g : Game) (sourceId : Option ObjectId) : Game :=
  match g.attachedHost? sourceId with
  | some host =>
    match g.controllerOf host with
    | some pid => g.draw pid 1
    | none => g.draw host.owner 1
  | none =>
    g.logMsg "The enchanted creature has left. No card is drawn."

/-- Draw until `controller` has `n` cards in hand. A hand that already has
`n` draws nothing. -/
def drawUpToHandSize (g : Game) (controller : PlayerId) (n : Nat) : Game :=
  let cards := (g.player controller).hand.size
  if cards < n then g.draw controller (n - cards)
  else if n == 10 then
    g.logMsg "You already have ten or more cards in hand"
  else
    g.logMsg s!"You already have {n} or more cards in hand"

/-- Ask the controller to put a +1/+1 counter on the source, or to remove a
counter from a creature they control and draw. -/
def offerHydeChoice (g : Game) (controller : PlayerId) (sourceId : Option ObjectId) : Game :=
  g.change (.pending (.fraChoice controller (.hydeMode sourceId)))
    |>.logMsg s!"{(g.player controller).name} chooses one — 0 put a +1/+1 counter, 1 remove a counter and draw"

/-- Something becomes a copy, as `of` says. The source copies an announced
object until the controller's next turn and keeps the printed exception
name. Choosing none copies nothing. A missing source copies nothing.
`.noted` makes the enchanted creature a copy of the creature an earlier
step noted, until the source leaves. Nothing noted copies nothing.
`.cause` with no subtype creates a token copy of the nontoken artifact
that caused this. An announced permanent is used when one was chosen;
otherwise the recorded cause. The source need not still be on the
battlefield. Any other selector copies nothing. -/
def applyBecomeCopy (g : Game) (controller : PlayerId) (sourceId : Option ObjectId)
    (targets : Array Target) (of : TriggeredAbility.ObjectSelector) : Game :=
  match of with
  | .noted =>
    let copied := g.notedCopyObject
    let hostId := g.notedHostId
    let g := g.changes #[.notedCopyObject none, .notedHostId none]
    match copied, hostId with
    | some tgt, some hid =>
      match g.findObject? hid with
      | some host => g.becomeCopyOf host tgt (untilSourceLeaves := sourceId)
      | none => g
    | _, _ => g
  | .cause none =>
    let fromTarget :=
      match targets[0]? with
      | some (Target.permanent id) => some id
      | _ => none
    let causeId :=
      (g.resolvingAbility.bind g.findObject?).bind (·.fraCauseId)
    match fromTarget.orElse (fun _ => causeId) with
    | none => g.logMsg "Ultron has nothing to copy"
    | some id => g.copyEnteredArtifact controller id
  | .artifactEnchantmentOrLand =>
    g.withSourceOnBattlefield sourceId (fun g src =>
      match targets[0]? with
      | some (Target.permanent id) =>
        match g.findObject? id with
        | some tgt =>
          let ok := tgt.isOnBattlefield && !g.isAura tgt &&
            (g.isArtifact tgt || g.isEnchantment tgt || g.isLand tgt)
          if ok then
            g.becomeCopyOf src tgt (untilNextTurn := true) (nextTurnOf := some controller)
              (exceptName := some "Absorbing Man")
              (addSupertypes := #[.legendary]) (addTypes := #[.creature])
              (addSubtypes := #[.human, .villain])
              (setPT := some (4, 4)) (addVigilance := true)
          else g.logMsg "That permanent isn't an artifact, non-Aura enchantment, or land"
        | none => g.logMsg "The target is no longer legal"
      | _ => g.logMsg "Absorbing Man doesn't become a copy")
      "The source is no longer in play"
  | .creatureOrGraveyardCard =>
    g.withSourceOnBattlefield sourceId (fun g src =>
      match targets[0]? with
      | some (Target.permanent id) | some (Target.card id) =>
        match g.findObject? id with
        | some tgt =>
          let onBf := tgt.isOnBattlefield && g.isCreature tgt
          let inGy := tgt.zone == .graveyard tgt.owner && g.isCreature tgt
          if onBf || inGy then
            g.becomeCopyOf src tgt (untilNextTurn := true) (nextTurnOf := some controller)
              (exceptName := some "Taskmaster, Mercenary Mimic")
              (addSupertypes := #[.legendary]) (addTypes := #[.creature])
              (addSubtypes := #[.human, .mercenary, .villain])
              (replaceCreatureLine := true)
          else g.logMsg "That isn't a creature or a creature card in a graveyard"
        | none => g.logMsg "The target is no longer legal"
      | _ => g.logMsg "Taskmaster doesn't become a copy")
      "The source is no longer in play"
  | _ => g

/-- Exile the announced nonland the controller still controls, other than the
source, then return it under its owner's control. Choosing none does nothing.
An illegal target is reported. -/
def flickerChosenNonland (g : Game) (controller : PlayerId) (sourceId : Option ObjectId)
    (targets : Array Target) : Game :=
  match targets[0]? with
  | some (Target.permanent id) =>
    match g.findObject? id with
    | some o =>
      let other :=
        match sourceId with
        | some sid => o.id != sid
        | none => true
      if o.isOnBattlefield && g.controlledBy o controller && !g.isLand o && other then
        let (g, cause) := g.allocDelayedCause (some controller) sourceId
        g.flickerPermanents #[o.id] (logText := "is exiled, then returned") (cause := some cause)
      else g.logMsg "The target is no longer legal"
    | none => g.logMsg "The target is no longer legal"
  | _ => g

/-- Exile the announced nontoken artifact or creature, then return it
tapped under its owner's control. Choosing none does nothing.
A token, a permanent that is neither an artifact nor a creature, or a
missing target is not exiled. -/
def returnNontokenTapped (g : Game) (targets : Array Target) : Game :=
  match targets[0]? with
  | some (Target.permanent id) =>
    match g.findObject? id with
    | some o =>
      if o.isOnBattlefield && !o.printed.isToken &&
          (g.isArtifact o || g.isCreature o) then
        let (g, cause) := g.allocDelayedCause (g.controllerOf o)
        g.flickerPermanents #[o.id] (logText := "is exiled, then returned tapped")
          (tapped := true) (cause := some cause)
      else g.logMsg "The target is no longer legal"
    | none => g.logMsg "The target is no longer legal"
  | _ => g

/-- Put `o` onto the battlefield under its owner's control, then apply
`mods` before its enters abilities. -/
def enterFromOwnerGraveyard (g : Game) (controller : PlayerId) (o : GameObject)
    (mods : List TriggeredAbility.TriggerEnterWith) : Game :=
  let (g, cause) := g.allocDelayedCause (some controller)
  let options := g.enterModsAttackOptions o.owner mods
  let item := EnteringAttackItem.card o.id o.owner controller false false
    (enterModsExtraCounters mods) mods (.ownerGraveyard (losesAbilitiesAndHaste mods)) options
  g.promptEnteringAttackItems #[item] (cause := some cause)

/-- Return the source from its owner's graveyard under its owner's control.
Hellcat's return reports her by name when she has already left. -/
def returnSourceUnderOwner (g : Game) (controller : PlayerId)
    (sourceId : Option ObjectId) (mods : List TriggeredAbility.TriggerEnterWith) : Game :=
  let hellcat := losesAbilitiesAndHaste mods
  let missing :=
    if hellcat then "Hellcat is no longer in the graveyard"
    else "The ability's source is no longer in the graveyard"
  match sourceId.bind (fun id => g.followMovedToZone? id (fun | .graveyard _ => true | _ => false)) with
  | none => g.logMsg missing
  | some o =>
    if o.zone != .graveyard o.owner then g.logMsg missing
    else g.enterFromOwnerGraveyard controller o mods

/-- The announced card or permanent, or the recorded cause in a graveyard. -/
def announcedOrCauseGraveyardObj? (g : Game) (targets : Array Target) : Option GameObject :=
  match targets[0]? with
  | some (Target.card id) | some (Target.permanent id) => g.findObject? id
  | _ =>
    ((g.resolvingAbility.bind g.findObject?).bind (·.fraCauseId)).bind
      (fun id => g.followMovedToZone? id (fun | .graveyard _ => true | _ => false))

/-- Return the cause from its owner's graveyard under its owner's control.
`subtype`, when set, requires that subtype. A missing cause puts nothing. -/
def returnCauseUnderOwner (g : Game) (controller : PlayerId) (targets : Array Target)
    (subtype : Option CardSubtype) (mods : List TriggeredAbility.TriggerEnterWith) : Game :=
  match g.announcedOrCauseGraveyardObj? targets with
  | some o =>
    let ok :=
      match subtype with
      | none => true
      | some s => g.hasSubtype o s
    if o.zone == .graveyard o.owner && ok then
      g.enterFromOwnerGraveyard controller o mods
    else g
  | none => g

/-- The announced card, the recorded cause, or the last attacking creature
that died, if still in a graveyard. -/
def diedCardObj? (g : Game) (targets : Array Target) : Option GameObject :=
  let inGy : Zone → Bool := fun | .graveyard _ => true | _ => false
  let fromTarget :=
    match targets[0]? with
    | some (Target.card id) | some (Target.permanent id) => g.findObject? id
    | _ => none
  let fromCause :=
    ((g.resolvingAbility.bind g.findObject?).bind (·.fraCauseId)).bind
      (fun id => g.followMovedToZone? id inGy)
  let fromAttacker := g.loggedLastDiedAttacker.bind (fun id => g.followMovedToZone? id inGy)
  (fromTarget.orElse (fun _ => fromCause)).orElse (fun _ => fromAttacker)

/-- Return the card that caused this trigger to its owner's hand.
A token ceases to exist. A card that has left is reported. -/
def returnCauseToOwnerHand (g : Game) (targets : Array Target) : Game :=
  match g.diedCardObj? targets with
  | none => g.logMsg "The attacking creature is no longer in the graveyard"
  | some o =>
    if o.printed.isToken then
      g.logMsg s!"{o.name} ceases to exist"
    else if o.zone != .graveyard o.owner then
      g.logMsg "The attacking creature is no longer in the graveyard"
    else
      g.returnToHand o.id o.owner

/-- Exile and return the announced permanent when the source is harnessed.
A missing source does nothing. An unharnessed source is reported. -/
def resolveHarnessedFlicker (g : Game) (controller : PlayerId) (sourceId : Option ObjectId)
    (targets : Array Target) : Game :=
  match sourceId.bind g.findObject? with
  | some src =>
    if !src.status.harnessed then
      g.logMsg "The Mind Stone is not harnessed"
    else
      g.flickerChosenNonland controller sourceId targets
  | none => g

/-- You may exile the top card of your library. A Hero card gives the source
+2/+1 until end of turn, and the card may be played this turn (Daredevil). -/
def offerExileTopHeroPump (g : Game) (controller : PlayerId)
    (sourceId : Option ObjectId) : Game :=
  g.change (.pending (.fraChoice controller (.daredevilMayExile sourceId)))
    |>.logMsg "You may exile the top card of your library"

/-- You may pay 2 life. If you do, creatures you control assign combat damage
equal to their toughness this turn (The Kingpin of Crime). -/
def offerPay2LifeToughness (g : Game) (controller : PlayerId) : Game :=
  if g.canPayLife controller 2 then
    g.change (.pending (.fraChoice controller .kingpinMayPay2Life))
      |>.logMsg "You may pay 2 life"
  else
    g.logMsg "The Kingpin's cost wasn't paid"

/-- Look at the top `n` cards and you may cast one with mana value at most the
greatest power among attacking creatures you control (Cosmic Cube). -/
def offerLookSixCast (g : Game) (controller : PlayerId) (n : Nat := 6) : Game :=
  g.beginMayCastFromLooked controller n (g.greatestPowerAmongAttacking controller)

/-- Mana value of the spell that caused this cast trigger, including X.
A spell that has left uses the last-known power, then the newest spell on
the stack, then a mana value recorded this turn. -/
def castSpellManaValue (g : Game) (controller : PlayerId)
    (lastKnownPower : Option Int) : Nat :=
  match g.castTriggerSpell? with
  | some spell => g.objectManaValue spell (includeLkiX := true)
  | none =>
    match ((g.resolvingAbility.bind g.findObject?).bind (·.fraCauseId)).bind g.lastKnownBefore? with
    | some eo => eo.manaValue
    | none =>
      match lastKnownPower with
      | some p => p.toNat
      | none =>
        match g.lastStackSpell? with
        | some o => g.objectManaValue o (includeLkiX := true)
        | none =>
          match (g.loggedCastManaValues controller).back? with
          | some mv => mv
          | none => 0

/-- Blue mana symbols in the spell that caused this cast trigger. -/
def blueSymbolsInCastSpell (g : Game) (lastKnownPower : Option Int) : Nat :=
  match g.castTriggerSpell? with
  | some spell => (g.copiableValues spell).manaCost.symbolsIncludingColor .blue
  | none =>
    match ((g.resolvingAbility.bind g.findObject?).bind (·.fraCauseId)).bind g.lastKnownBefore? with
    | some eo => (eo.copiable.getD eo.toCardDef).manaCost.symbolsIncludingColor .blue
    | none =>
      match lastKnownPower with
      | some p => p.toNat
      | none =>
        match g.lastStackSpell? with
        | some o => (g.copiableValues o).manaCost.symbolsIncludingColor .blue
        | none => 0

/-- Create one 1/1 blue Merfolk for each blue mana symbol in the causing spell. -/
def createMerfolkForBlueSymbols (g : Game) (controller : PlayerId)
    (lastKnownPower : Option Int) : Game :=
  let n := g.blueSymbolsInCastSpell lastKnownPower
  if n == 0 then
    g.logMsg "No blue mana symbols. No Merfolk are created."
  else
    g.withBatch none fun g =>
      Id.run do
        let mut g := g
        for _ in [0:n] do
          let (g', _) := g.createToken controller merfolk11blueToken
          g := g'
        return g

/-- Ask for one Vision mode that has not been chosen this turn. The chosen
resolution is `TriggerResolution.visionModes`. -/
def offerVisionModes (g : Game) (controller : PlayerId) (ab : TriggeredAbility)
    (sourceId : Option ObjectId) (targets : Array Target := #[])
    (lastKnownPower : Option Int := none) (sourceName : String := "This creature") : Game :=
  match sourceId with
  | some sid =>
    if (g.findObject? sid).isNone && (g.lastKnownBefore? sid).isNone then
      g.logMsg "The Vision is no longer in play"
    else
      let chosen := g.modesChosenThisTurn sid
      let available :=
        #[0, 1, 2].filter (fun m => !chosen.contains m)
      if available.isEmpty then
        g.logMsg "The Vision's ability is removed from the stack with no effect"
      else
        g.changes #[
          .pending (.fraChoice controller (.visionMode sid available)),
          .chooseModesRest (some {
            controller
            ability := ab
            sourceId
            targets
            lastKnownPower
            sourceName
            modes := TriggeredAbility.TriggerResolution.visionModes
            how := .vision })]
          |>.logMsg "Choose one that hasn't been chosen this turn"
  | none =>
    g.logMsg "The Vision is no longer in play"

/-- The source gains Iron Fist's tap ability until end of turn. -/
def grantIronFistTap (g : Game) (sourceId : Option ObjectId) : Game :=
  g.withSourceOnBattlefield sourceId (fun g o =>
    g.createEffect (.ironFistTapUntilEot o.id)
      |>.logMsg s!"{o.name} gains a tap ability until end of turn")
    "The source is no longer in play"

/-- Until end of turn, the source's base power is the cards in hand. -/
def grantHandSizePower (g : Game) (sourceId : Option ObjectId) : Game :=
  g.withSourceOnBattlefield sourceId (fun g o =>
    g.createEffect (.cardsInHandPowerUntilEot o.id)
      |>.logMsg s!"{o.name}'s base power is the number of cards in your hand until end of turn")
    "The source is no longer in play"

/-- Grant `k` until end of turn to each creature the causing spell targets. -/
def grantKeywordsToSpellCreatureTargets (g : Game) (k : Keywords) : Game :=
  let ids :=
    match g.castTriggerSpell? with
    | none => #[]
    | some spell =>
      match g.stack.find? (fun (e : StackEntry) => e.objectId == spell.id) with
      | none => (#[] : Array ObjectId)
      | some e =>
        e.targets.filterMap (fun t =>
          match t with
          | Target.permanent id => some id
          | _ => none)
  g.withBatch none fun g =>
    ids.foldl (fun (g : Game) id =>
      match g.findObject? id with
      | some o =>
        if o.isOnBattlefield && g.isCreature o then
          g.grantUntilEotLogged o k
        else g
      | none => g) g

/-- Copy the spell that caused this trigger and ask for new targets if targeted
(CR 707.10c / 800.4d). -/
def copyCastTriggerSpell (g : Game) (controller : PlayerId) : Game :=
  match g.castTriggerSpell? with
  | some spell =>
    if spell.zone != .stack then g.logMsg s!"{spell.name} is no longer on the stack"
    else
      let (g, copyId?) := g.copyStackSpellWithId spell controller
      match copyId? with
      | some copyId =>
        if (g.stackEntry? copyId).any (!·.targets.isEmpty) then
          (g.change (.pending (.fraChoice controller (.newTargetsForCopies #[copyId])))).logMsg
            s!"{(g.player controller).name} may choose new targets for the copy"
        else g
      | none => g
  | none => g

/-- You may exile the discarded card recorded as the trigger's cause and play
it until the end of your next turn. -/
def offerMayExileDiscarded (g : Game) (controller : PlayerId) : Game :=
  let causeId? := (g.resolvingAbility.bind g.findObject?).bind (·.fraCauseId)
  let obj? :=
    causeId?.bind (fun cid => g.followMovedToZone? cid (· == Zone.graveyard controller))
  match obj? with
  | some o =>
    g.change (.pending (.fraChoice controller (.moonstoneMayExile o.id)))
      |>.logMsg s!"You may exile {o.name} from your graveyard"
  | none =>
    if causeId?.isSome then
      g.logMsg "The discarded card is no longer in your graveyard"
    else
      g.logMsg "No discarded card is in the graveyard"

/-- You may create a 0/4 Wall creature token with defender. -/
def offerMayCreateWall (g : Game) (controller : PlayerId) : Game :=
  g.change (.pending (.fraChoice controller (.mayCreateTokens .wall04defender 1)))
    |>.logMsg
      s!"{(g.player controller).name} may create a 0/4 Wall creature token with defender"

/-- Put a +1/+1 counter on each announced creature you control, up to the
life gained in that event (the trigger's last-known power). -/
def putPlusOnesUpToLastKnown (g : Game) (controller : PlayerId)
    (targets : Array Target) (lastKnownPower : Option Int)
    (sourceId : Option ObjectId := none) : Game :=
  let n := (lastKnownPower.getD 0).toNat
  g.withBatch none fun g =>
    (targets.extract 0 n).foldl (fun (g : Game) t =>
      match t with
      | Target.permanent id =>
        match g.findObject? id with
        | some o =>
          if o.isOnBattlefield && g.isCreature o && g.controlledBy o controller &&
              g.canBeTargetedBy controller o sourceId then
            g.addPlusOnePlusOneTo o 1
          else g.logMsg "The target is no longer legal"
        | none => g.logMsg "The target is no longer legal"
      | _ => g.logMsg "The target is no longer legal") g

/-- Finish registering `.endStepReturn` for `(.casting .exileFlicker)` after
`g.move` to `.exile` completes (CR 614.6 / 616.1). -/
def finishExileFlickerAfterExile (g : Game) (controller : PlayerId)
    (fromId : ObjectId) (cardName : String) (sourceId : Option ObjectId)
    (cause : EventCause) : Game :=
  match g.followMovedToZone? fromId (· == .exile) with
  | none => g
  | some moved =>
    let src := (sourceId.bind g.findObject?).orElse (fun _ => some moved)
    g.registerDelayedTrigger { controller, source := src, kind := .endStepReturn moved.id, cause }
      |>.logMsg s!"{cardName} is exiled until the beginning of the next end step"

/-- Resolve a modeled leftover trigger from its `SharedTrigger` constructor.
Effects are applied from that structured payload — not from Oracle text. -/
def applyModeledTrigger (g : Game) (controller : PlayerId) (t : TriggeredAbility)
    (sourceId : Option ObjectId) (targets : Array Target := #[])
    (sourceName : String := "This creature")
    (lastKnownPower : Option Int := none) : Game :=
  match t.shared with
  | (.step .copyAbsorbingMan) =>
    g.applyBecomeCopy controller sourceId targets .artifactEnchantmentOrLand
  | (.step .copyTaskmaster) =>
    g.applyBecomeCopy controller sourceId targets .creatureOrGraveyardCard
  | (.casting .mayPayHasteUnblockable) =>
    g.offerPayForReflexive controller sourceId #[.generic 1] .hasteUnblockable
  | (.youAttacking .exileTopHeroPump) =>
    g.offerExileTopHeroPump controller sourceId
  | (.youAttacking .pay2LifeToughness) =>
    g.offerPay2LifeToughness controller
  | (.death .attackingReturnHand) =>
    g.returnCauseToOwnerHand targets
  | (.death .villainReturnAsHero) =>
    g.returnCauseUnderOwner controller targets (some .villain)
      [.additionalSubtype .hero, .counter .finality]
  | (.casting .villainToken) =>
    g.createKindTokens controller .villain21menace 1
  | (.resource .plusOneCreateInsectOnce) =>
    g.createKindTokens controller .insect11green 1
  | (.resource .plusOneOnHeroesCreateWall) =>
    g.offerMayCreateWall controller
  | (.resource .secondDrawBecome66) =>
    g.withSourceOnBattlefield sourceId (fun g o =>
      g.createEffects
        #[.setBasePTUntilEot o.id (6, 6), .keywordsUntilEot o.id Keyword.trample]
        |>.logMsg s!"{o.name}'s base power and toughness become 6/6")
      "The source is no longer in play"
  | (.casting .visionModes) =>
    g.offerVisionModes controller t sourceId targets lastKnownPower sourceName
  | (.casting .ironFistTap) =>
    g.grantIronFistTap sourceId
  | (.casting .drawPowerEqualHand) =>
    let g := g.draw controller 1
    if let .chooseReplacement .. := g.pending then
      g.chainPendingReplacement (.finishPostStep (.grantHandSizePower sourceId))
    else
      g.grantHandSizePower sourceId
  | (.step .hydeChoose) =>
    let chosenMode? :=
      g.resolvingModes.bind (·[0]?) <|>
        (g.resolvingAbility.bind g.stackEntry?).bind (·.chosenMode)
    match chosenMode? with
    | none => g.offerHydeChoice controller sourceId
    | some mode => g.applyHydeMode controller sourceId mode targets
  | (.resource .drawIfAnotherHeroDamage) =>
    if (g.permanentsOf controller).any (fun o =>
        g.hasSubtype o .hero && some o.id != sourceId) then
      g.withLegalKindTarget controller .opponent targets (fun g tgt =>
        match tgt with
        | Target.player pid => g.dealDamageToPlayer pid 1 (source := sourceId.bind g.findObject?)
        | _ => g) sourceId none
    else
      g.logMsg "Human Torch's ability has no effect"
  | (.step .drawToTen) =>
    g.drawUpToHandSize controller 10
  | (.step .harnessedFlicker) =>
    g.resolveHarnessedFlicker controller sourceId targets
  | (.youAttacking .lookSixCast) =>
    g.offerLookSixCast controller
  | (.step .enchantedControllerDraws) =>
    g.drawForEnchantedController sourceId
  | (.death .hellcatReturn) =>
    g.returnSourceUnderOwner controller sourceId
      [.loseAllAbilities, .keywords Keyword.haste, .counter .plusOnePlusOne (asEnters := true)]
  | (.death .deathtouchOppSac) =>
    g.continueNontokenSacrifices ((g.livingOpponents controller).map (·.id)) #[]
  | (.casting .exileFlicker) =>
    let kind := EffectTargetKind.filtered {
      noun := "another target nonland, nontoken permanent"
      nonTypes := #[.land], nontoken := true, another := true }
    g.withLegalKindPermanent controller kind targets (fun g o =>
      let name := o.name
      let (g, cause) := g.allocDelayedCause (some controller) sourceId
      let (g, _) := g.move o.id .exile none (cause := some cause)
      if let .chooseReplacement .. := g.pending then
        g.chainPendingReplacement
          (.finishPostStep (.exileFlickerAfterExile controller o.id name sourceId cause))
      else
        g.finishExileFlickerAfterExile controller o.id name sourceId cause)
      sourceId (some "The target is no longer legal")
  | (.casting .damageEqualMv) =>
    let n := g.castSpellManaValue controller lastKnownPower
    g.applyDamageToKindTarget controller .playerOrCreature targets n sourceId none
  | (.casting .merfolkFromBlue) =>
    g.createMerfolkForBlueSymbols controller lastKnownPower
  | (.casting .plusOneEachOther) =>
    g.forEachControlledCreature controller (fun g o =>
      if some o.id != sourceId then g.addPlusOnePlusOneTo o 1 else g)
  | (.casting .plusOneThis) =>
    g.withSourceOnBattlefield sourceId (fun g o => g.addPlusOnePlusOneTo o 1)
      "The source is no longer in play"
  | (.casting .plusOneScry) =>
    let g :=
      g.withSourceOnBattlefield sourceId (fun g o => g.addPlusOnePlusOneTo o 1)
        "The source is no longer in play"
    if let .chooseReplacement .. := g.pending then
      g.chainPendingReplacement (.finishPostStep (.beginScryOne controller))
    else
      g.beginScry controller 1
  | (.casting .targetsGainFlying) =>
    g.grantKeywordsToSpellCreatureTargets Keyword.flying
  | (.casting .copyIfArtifactOrLand) =>
    let g := g.withSourceOnBattlefield sourceId (fun g o => g.addPlusOnePlusOneTo o 2)
      "The source is no longer in play"
    if let .chooseReplacement .. := g.pending then
      g.chainPendingReplacement (.finishPostStep (.copyCastTriggerSpell controller))
    else
      g.copyCastTriggerSpell controller
  | (.casting .tapCreatureOrLand) =>
    let kind := EffectTargetKind.filtered {
      noun := "target creature or land",
      types := #[.creature, .land] }
    g.withLegalKindPermanent controller kind targets
      (fun g o => g.applyPermanentAction o .tap) sourceId
      (some "The target is no longer legal")
  | (.resource .discardExilePlay) =>
    g.offerMayExileDiscarded controller
  | (.resource .secondDrawPlusOneTarget) =>
    g.withLegalKindPermanent controller .creature targets
      (fun g o => g.addPlusOnePlusOneTo o 1) sourceId
      (some "The target is no longer legal")
  | (.resource .secondDrawDrain) =>
    g.eachOpponentLosesYouGain controller 1
  | (.resource .gainLifePlusOnes) =>
    g.putPlusOnesUpToLastKnown controller targets lastKnownPower (sourceId := sourceId)
  | (.resource .plusOneOnThisOnce) =>
    g.withSourceOnBattlefield sourceId (fun g o => g.addPlusOnePlusOneTo o 1)
      "The source is no longer in play"
  | _ =>
    g.withSourceOnBattlefield sourceId (fun g _ => g)
      s!"{sourceName} resolves"

/-- Put the targeted creature into its owner's library, second from the top
or on the bottom (Trickster's Stratagem). -/
def applyOwnerPutsLibraryThenConnive (g : Game) (controller : PlayerId)
    (targets : Array Target) (putOnBottom := false)
    (sourceId : Option ObjectId := none) : Game :=
  let srcId := sourceId.orElse (fun _ => g.resolvingSpell)
  if !g.stillInGame controller then g
  else
    match targets[0]? with
    | some (Target.permanent id) =>
      match g.findObject? id with
      | some o =>
        if o.isOnBattlefield && g.canBeTargetedBy controller o srcId then
          let owner := o.owner
          if putOnBottom then
            let (g, _) := g.move id (.library owner) none (libraryPosition := some .bottom)
            g.logMsg s!"{o.name} is put on the bottom of {(g.player owner).name}'s library"
          else
            let (g, _) := g.move id (.library owner) none (libraryPosition := some (.fromTop 1))
            g.logMsg s!"{o.name} is put second from the top of {(g.player owner).name}'s library"
        else g.logMsg "The target is no longer legal"
      | none => g.logMsg "The target is no longer legal"
    | _ => g.logMsg "The target is no longer legal"

/-- Avengers Disassembled: if the land mode was chosen and that target is
illegal, the spell does not resolve — even the untargeted damage mode
(MSH 207). If the land is legal but indestructible, its controller still
searches. -/
def applyAvengersDisassembled (g : Game) (controller : PlayerId)
    (choseDamage choseLand : Bool) (landId : Option ObjectId)
    (sourceId : Option ObjectId := none) : Game :=
  let srcId := sourceId.orElse (fun _ => g.resolvingSpell)
  let landOk :=
    match landId.bind g.findObject? with
    | some o => o.isOnBattlefield && g.isLand o && g.canBeTargetedBy controller o srcId
    | none => false
  if choseLand && !landOk then
    g.logMsg "The target is no longer legal. Avengers Disassembled doesn't resolve."
  else
    let g :=
      if choseDamage then
        g.dealDamageToEachCreatureMatching 3
      else g
    if choseLand then
      if let .chooseReplacement .. := g.pending then
        g.chainPendingReplacement (.finishPostStep (.destroyTargetLandThenOfferSearchBasics controller srcId landId))
      else
        match landId.bind g.findObject? with
        | some o =>
          if o.isOnBattlefield && g.isLand o && g.canBeTargetedBy controller o srcId then
            let owner := o.owner
            let g := g.destroyPermanent o
            if let .chooseReplacement .. := g.pending then
              g.chainPendingReplacement (.finishPostStep (.offerMaySearchBasics owner))
            else
              g.offerMaySearchBasics owner
          else g
        | none => g
    else g

/-- Whether the resolving stack object paid its teamwork cost. -/
def resolvingTeamworkPaid (g : Game) : Bool :=
  g.spellPaidTeamwork

/-- `alt` if the resolving spell paid teamwork; otherwise `base`. -/
def teamworkAmount (g : Game) (base alt : Nat) : Nat :=
  if g.resolvingTeamworkPaid then alt else base

/-- Add `types` to `p`'s mana pool and log it (shared `.addMana` resolution). -/
def addManaLogged (g : Game) (p : PlayerId) (types : Array ManaType)
    (source : Option ObjectId := none) : Game :=
  let g := g.addManaUnits p (types.map fun t => { mana := t, source })
    (cause := g.resolvingOneShotCause p source)
  g.logMsg s!"{(g.player p).name} adds mana"

/-- Ask the target spell's controller to pay `{n}` or let it be countered. -/
def beginPayOrLetCounter (g : Game) (targets : Array Target) (n : Nat) : Game :=
  match targets[0]? with
  | some (Target.card id) =>
    match g.findObject? id with
    | some o =>
      let ctrl := o.controller.getD o.owner
      ((g.clearUnlessPays).change (.pending (.payOrLetCounter ctrl n (some id)))).logMsg
        s!"{(g.player ctrl).name} may pay \{{n}} or {o.name} is countered"
    | none => g.logMsg "The target is no longer legal"
  | _ => g.logMsg "The target is no longer legal"

/-- Ask the target's controller to pay `{n}`. If they do not, resolve `r`.
Countering uses the existing “pay or let the spell be countered” choice. -/
def beginUnlessPays (g : Game) (controller : PlayerId) (effect : Effect)
    (targets : Array Target) (r : SpellResolution) (n : Nat)
    (sourceId : Option ObjectId := none) : Game :=
  match r with
  | .counter => g.beginPayOrLetCounter targets n
  | _ =>
    let payer? : Option (PlayerId × Option ObjectId) :=
      match targets[0]? with
      | some (Target.card id) =>
        match g.findObject? id with
        | some o => some (o.controller.getD o.owner, some id)
        | none => none
      | some (Target.permanent id) =>
        match g.findObject? id with
        | some o =>
          if o.isOnBattlefield && !g.canBeTargetedBy controller o sourceId then none
          else (g.lastControllerOf? o).map (fun pid => (pid, none))
        | none => none
      | some (Target.player pid) =>
        if (g.player pid).lost || !g.playerCanBeTargetedBy controller pid sourceId then none
        else some (pid, none)
      | _ => none
    match payer? with
    | none => g.logMsg "The target is no longer legal"
    | some (payer, spellId?) =>
      let inner := { effect with resolution := Resolution.ofSpell r }
      (g.changes #[
        .pending (.payOrLetCounter payer n spellId?),
        .unlessPaysInstead (some inner),
        .unlessPaysController controller,
        .unlessPaysTargets targets,
        .unlessPaysSource sourceId,
        .unlessPaysDue false]).logMsg
        s!"{(g.player payer).name} may pay \{{n}} or {SpellResolution.toPhrase r effect.targeting.kind.noun}"

/-- Exile `o`, then immediately return it to the battlefield under its
owner's control. `clearExileFields` drops a play permission or linked exile
carried while exiled. With `land := false` the permanent returns summoning
sick unless it has haste and `afterPermanentEnters` runs; with `land := true`
it returns tapped when `tapped` is set and `afterLandEnters` runs. -/
def exileThenReturn (g : Game) (o : GameObject) (logText : String)
    (clearExileFields := false) (tapped := false) (land := false)
    (cause : Option EventCause := none) : Game :=
  g.flickerPermanents #[o.id] (logText := logText)
    (tapped := land && tapped) (clearExileFields := clearExileFields) (cause := cause)

end Game
end Mtg.Engine
