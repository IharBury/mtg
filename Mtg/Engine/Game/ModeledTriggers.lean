import Mtg.Engine.Game.ResolutionEffects

/-!
# Modeled trigger helpers

Supporting helpers for trigger resolution, boast, teamwork, and pay-or-counter
flows.
-/

namespace Mtg.Engine
namespace Game

/-- The lone attacking creature `p` controls, if exactly one creature on the
battlefield is attacking (CR 506.5). -/
def attackingAlone? (g : Game) (p : PlayerId) : Option GameObject :=
  let all := g.battlefield.filter (fun o => g.isCreature o && o.status.attacking)
  if all.size == 1 && g.controlledBy all[0]! p then some all[0]! else none

/-- Permanent this Aura or Equipment is attached to, falling back to LKI when
the source left the battlefield before its ability resolves (CR 608.2h). -/
def attachedHost? (g : Game) (sourceId : Option ObjectId) : Option GameObject :=
  match sourceId.bind g.findObject? with
  | some src => src.attachedTo.bind g.findObject? |>.filter (·.isOnBattlefield)
  | none =>
    ((sourceId.bind g.lastKnownBefore?).bind (·.attachedTo)).bind g.findObject?
      |>.filter (·.isOnBattlefield)

/-- The spell that caused the resolving cast trigger, if still on the stack. -/
def castTriggerSpell? (g : Game) : Option GameObject :=
  ((g.resolvingAbility.bind g.findObject?).bind (·.triggerCauseId)).bind
    (fun id => (g.findObject? id).filter (·.zone == .stack))

/-- Ask the next player in `players` with a nontoken creature to choose one
to sacrifice; once all have chosen, sacrifice them together. -/
def continueNontokenSacrifices (g : Game) (players : Array PlayerId) (chosen : Array ObjectId) :
    Game :=
  let hasOne (p : PlayerId) := (g.permanentsOf p).any (fun o => g.isCreature o && !o.printed.isToken)
  match (players.filter hasOne).toList with
  | p :: rest =>
    g.beginResolutionChoice p (.sacrificeNontokenEach rest.toArray chosen)
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
@[export mtg_game_grant_widow_cast]
def grantWidowCast (g : Game) (controller : PlayerId) (exiled : Option ObjectId)
    (cause : Option EventCause := none) : Game :=
  if !g.stillInGame controller then g
  else
    match exiled.bind g.findObject? with
    | none => g.logMsg "No nonland card was exiled"
    | some o =>
      let cause := cause.orElse (fun _ => g.lastMoveCauseOf? o.id)
      g.createEffect (.playPermission o.id {
        player := controller
        anyMana := true
        landsAllowed := false }) (cause := cause)
        |>.logMsg s!"{(g.player controller).name} may cast {g.name o} until end of turn"

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
        g.createEffect (.keywordsUntilEot src.id #[Keyword.doubleStrike])
      else if mode == 1 then
        g.createEffect (.keywordsUntilEot src.id #[Keyword.indestructible])
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
        let spec := g.targetSpecOf spell
        if g.validTargetArrayForEntry e spell spec staged (allowUnchangedIllegal := true) then
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
      g.beginResolutionChoice controller (.mayChangeSpellTarget spellId index curStaged)
        "You may choose a new target for the spell"
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
      let spec := g.targetSpecOf spell
      let selfSource := spell.sourceId.orElse (fun _ => if spell.zone == .stack then some spell.id else none)
      let selfStackId := if spell.zone == .stack then some spell.id else none
      let totalPos := e.targets.size + e.skippedOptionalSlots.size
      let posIndices : Array Nat :=
        if e.skippedOptionalSlots.isEmpty then (List.range e.targets.size).toArray
        else ((List.range totalPos).filter (fun s => !e.skippedOptionalSlots.contains s)).toArray
      let actualPos := posIndices[index]?.getD index
      if !(g.legalTargetsForSlot e.controller (spec.slotAtPos actualPos) selfSource selfStackId).contains neu then
        (g.logMsg "That target stays unchanged", base)
      else
        let cand := base.set! index neu
        if index + 1 < e.targets.size then
          (g, cand)
        else if g.validTargetArrayForEntry e spell spec cand (allowUnchangedIllegal := true) then
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
        let spec := g.targetSpecOf spell
        let cand := e.targets.set! index neu
        if cand != e.targets && g.validTargetArrayForEntry e spell spec cand (allowUnchangedIllegal := true) then
          g.setStackEntryTargets spellId cand (dividedDamage := e.dividedDamage)
            |>.logMsg "A new target is chosen for the spell"
        else
          g.logMsg "That target stays unchanged"
      else
        g.logMsg "That target stays unchanged"

/-- Ask the controller to put a +1/+1 counter on the source, or to remove a
counter from a creature they control and draw. -/
def offerHydeChoice (g : Game) (controller : PlayerId) (sourceId : Option ObjectId) : Game :=
  g.beginResolutionChoice controller (.hydeMode sourceId)
    s!"{(g.player controller).name} chooses one — 0 put a +1/+1 counter, 1 remove a counter and draw"

/-- You may exile the top card of your library. A Hero card gives the source
+2/+1 until end of turn, and the card may be played this turn (Daredevil). -/
def offerExileTopHeroPump (g : Game) (controller : PlayerId)
    (sourceId : Option ObjectId) : Game :=
  g.beginResolutionChoice controller (.daredevilMayExile sourceId)
    "You may exile the top card of your library"

/-- You may pay 2 life. If you do, creatures you control assign combat damage
equal to their toughness this turn (The Kingpin of Crime). -/
def offerPay2LifeToughness (g : Game) (controller : PlayerId) : Game :=
  if g.canPayLife controller 2 then
    g.beginResolutionChoice controller .kingpinMayPay2Life "You may pay 2 life"
  else
    g.logMsg "The Kingpin's cost wasn't paid"

/-- Copy the spell that caused this trigger and ask for new targets if targeted
(CR 707.10c / 800.4d). -/
def copyCastTriggerSpell (g : Game) (controller : PlayerId) : Game :=
  match g.castTriggerSpell? with
  | some spell =>
    if spell.zone != .stack then g.logMsg s!"{g.name spell} is no longer on the stack"
    else
      let (g, copyId?) := g.copyStackSpellWithId spell controller
      match copyId? with
      | some copyId =>
        if (g.stackEntry? copyId).any (!·.targets.isEmpty) then
          g.beginResolutionChoice controller (.newTargetsForCopies #[copyId])
            s!"{(g.player controller).name} may choose new targets for the copy"
        else g
      | none => g
  | none => g

/-- You may create a 0/4 Wall creature token with defender. -/
def offerMayCreateWall (g : Game) (controller : PlayerId) : Game :=
  g.beginResolutionChoice controller (.mayCreateTokens .wall04defender 1)
    s!"{(g.player controller).name} may create a 0/4 Wall creature token with defender"

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
          let name := g.name o
          let pos : LibraryPosition := if putOnBottom then .bottom else .fromTop 1
          let msg :=
            if putOnBottom then
              s!"{name} is put on the bottom of {(g.player owner).name}'s library"
            else
              s!"{name} is put second from the top of {(g.player owner).name}'s library"
          let (g, _) := g.move id (.library owner) none (libraryPosition := some pos)
          if let .chooseReplacement .. := g.pending then
            g.chainPendingReplacement
              (.finishPostStep (.logPutOnOwnerLibrary id owner name (!putOnBottom) (some msg)))
          else if (g.followMovedToZone? id (· == .library owner)).isSome then
            g.logMsg msg
          else g
        else g.logMsg "The target is no longer legal"
      | none => g.logMsg "The target is no longer legal"
    | _ => g.logMsg "The target is no longer legal"

/-- Add `types` to `p`'s mana pool and log it (shared `.addMana` resolution). -/
def addManaLogged (g : Game) (p : PlayerId) (types : Array ManaType)
    (source : Option ObjectId := none) : Game :=
  if !g.stillInGame p then g
  else
    let g := g.addManaUnits p (types.map fun t => { mana := t, source })
      (cause := g.resolvingOneShotCause p source)
    g.logMsg s!"{(g.player p).name} adds mana"

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
