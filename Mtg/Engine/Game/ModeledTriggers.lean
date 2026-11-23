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
    g.beginFraChoice p (.sacrificeNontokenEach rest.toArray chosen)
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
        anyMana := true }) (cause := cause)
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
        let spec := (g.targetingOf spell).spec
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
      g.beginFraChoice controller (.mayChangeSpellTarget spellId index curStaged)
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
      let spec := (g.targetingOf spell).spec
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
        let spec := (g.targetingOf spell).spec
        let cand := e.targets.set! index neu
        if cand != e.targets && g.validTargetArrayForEntry e spell spec cand (allowUnchangedIllegal := true) then
          g.setStackEntryTargets spellId cand (dividedDamage := e.dividedDamage)
            |>.logMsg "A new target is chosen for the spell"
        else
          g.logMsg "That target stays unchanged"
      else
        g.logMsg "That target stays unchanged"

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
  g.beginFraChoice controller (.hydeMode sourceId)
    s!"{(g.player controller).name} chooses one — 0 put a +1/+1 counter, 1 remove a counter and draw"

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
    (mods : List EnterMod) : Game :=
  let (g, cause) := g.allocDelayedCause (some controller)
  let options := g.enterModsAttackOptions o.owner mods
  let item := EnteringAttackItem.card o.id o.owner controller false false
    (enterModsExtraCounters mods) mods (.ownerGraveyard (losesAbilitiesAndHaste mods)) options
  g.promptEnteringAttackItems #[item] (cause := some cause)

/-- Return the source from its owner's graveyard under its owner's control.
Hellcat's return reports her by name when she has already left. -/
def returnSourceUnderOwner (g : Game) (controller : PlayerId)
    (sourceId : Option ObjectId) (mods : List EnterMod) : Game :=
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
    (subtype : Option CardSubtype) (mods : List EnterMod) : Game :=
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
      g.logMsg s!"{g.name o} ceases to exist"
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
  g.beginFraChoice controller (.daredevilMayExile sourceId)
    "You may exile the top card of your library"

/-- You may pay 2 life. If you do, creatures you control assign combat damage
equal to their toughness this turn (The Kingpin of Crime). -/
def offerPay2LifeToughness (g : Game) (controller : PlayerId) : Game :=
  if g.canPayLife controller 2 then
    g.beginFraChoice controller .kingpinMayPay2Life "You may pay 2 life"
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

/-- The source gains Iron Fist's tap ability until end of turn. -/
def grantIronFistTap (g : Game) (sourceId : Option ObjectId) : Game :=
  g.withSourceOnBattlefield sourceId (fun g o =>
    g.createEffect (.ironFistTapUntilEot o.id)
      |>.logMsg s!"{g.name o} gains a tap ability until end of turn")
    "The source is no longer in play"

/-- Until end of turn, the source's base power is the cards in hand. -/
def grantHandSizePower (g : Game) (sourceId : Option ObjectId) : Game :=
  g.withSourceOnBattlefield sourceId (fun g o =>
    g.createEffect (.cardsInHandPowerUntilEot o.id)
      |>.logMsg s!"{g.name o}'s base power is the number of cards in your hand until end of turn")
    "The source is no longer in play"

/-- Grant `k` until end of turn to each creature the causing spell targets. -/
def grantKeywordsToSpellCreatureTargets (g : Game) (k : Array KeywordAbility) : Game :=
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
    if spell.zone != .stack then g.logMsg s!"{g.name spell} is no longer on the stack"
    else
      let (g, copyId?) := g.copyStackSpellWithId spell controller
      match copyId? with
      | some copyId =>
        if (g.stackEntry? copyId).any (!·.targets.isEmpty) then
          g.beginFraChoice controller (.newTargetsForCopies #[copyId])
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
    g.beginFraChoice controller (.moonstoneMayExile o.id)
      s!"You may exile {g.name o} from your graveyard"
  | none =>
    if causeId?.isSome then
      g.logMsg "The discarded card is no longer in your graveyard"
    else
      g.logMsg "No discarded card is in the graveyard"

/-- You may create a 0/4 Wall creature token with defender. -/
def offerMayCreateWall (g : Game) (controller : PlayerId) : Game :=
  g.beginFraChoice controller (.mayCreateTokens .wall04defender 1)
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

/-- Whether the resolving stack object paid its teamwork cost. -/
def resolvingTeamworkPaid (g : Game) : Bool :=
  g.spellPaidTeamwork

/-- Add `types` to `p`'s mana pool and log it (shared `.addMana` resolution). -/
def addManaLogged (g : Game) (p : PlayerId) (types : Array ManaType)
    (source : Option ObjectId := none) : Game :=
  if !g.stillInGame p then g
  else
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
      (g.change (.pending (.payOrLetCounter ctrl n (some id)))).logMsg
        s!"{(g.player ctrl).name} may pay \{{n}} or {g.name o} is countered"
    | none => g.logMsg "The target is no longer legal"
  | _ => g.logMsg "The target is no longer legal"

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
