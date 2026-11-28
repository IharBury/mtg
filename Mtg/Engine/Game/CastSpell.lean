import Mtg.Engine.Game.Decisions

/-!
# The casting process (CR 601.2)

Entering the proposal window, `castSpell`, and announcing modes, a value
for `{X}` (CR 107.3a), targets, divided damage, and triggered-ability
targets.
-/

namespace Mtg.Engine
namespace Game

/-- After proposing a spell or activated ability, announce `{X}` and modes
(CR 107.3a / 601.2b), then additional costs, then targets (CR 601.2c), then
mana abilities (CR 601.2g). -/
def enterProposalWindow (g : Game) (p : PlayerId) (pl : Player) (prop : ProposedSpell)
    (needsMode needsTarget : Bool) (modeCitation : String)
    (needsAdditionalCost : Bool := false) (needsKicker : Bool := false)
    (needsGift : Bool := false) (needsTeamwork : Bool := false)
    (needsMorphFirst : Bool := false) : Game :=
  if needsMorphFirst then
    let g := g.changes #[.pending (.chooseKicker p), .proposedSpell (some prop)]
    g.logMsg s!"{pl.name} may kick the spell (CR 702.33 / 601.2b)"
  else if prop.cost.containsX then
    let g := g.changes #[.pending (.chooseX p), .proposedSpell (some prop)]
    g.logMsg s!"{pl.name} must choose a value for X (CR 107.3a / 601.2b)"
  else if needsMode then
    let g := g.changes #[.pending (.chooseMode p), .proposedSpell (some prop)]
    g.logMsg s!"{pl.name} must choose a mode ({modeCitation})"
  else if needsAdditionalCost then
    let g := g.changes #[.pending (.chooseAdditionalCost p), .proposedSpell (some prop)]
    g.logMsg s!"{pl.name} must choose an additional cost (CR 601.2b)"
  else if needsKicker then
    let g := g.changes #[.pending (.chooseKicker p), .proposedSpell (some prop)]
    g.logMsg s!"{pl.name} may kick the spell (CR 702.33 / 601.2b)"
  else if needsGift then
    let g := g.changes #[.pending (.chooseGift p), .proposedSpell (some prop)]
    g.logMsg s!"{pl.name} may promise a gift (CR 702.174 / 601.2b)"
  else if needsTeamwork then
    let g := g.changes #[.pending (.chooseTeamwork p), .proposedSpell (some prop)]
    g.logMsg s!"{pl.name} may pay a teamwork cost (CR 702.194 / 601.2b)"
  else if needsTarget then
    let g := g.changes #[.pending (.chooseTargets p), .proposedSpell (some prop)]
    g.logMsg s!"{pl.name} must choose a target (CR 601.2c)"
  else if prop.kind == .activatedAbility && !prop.cost.includesManaPayment && !prop.needsSacrificeOther then
    let g := g.change (.proposedSpell (some prop))
    match g.beginActivationPayment prop with
    | .ok g' => g'
    | .error _ => g.reverseProposedSpell (resumeContinuation := true)
  else
    let g := g.changes #[.pending (.activateManaAbilities p), .proposedSpell (some prop)]
    g.logMsg s!"{pl.name} may activate mana abilities (CR 601.2g)"

def castSpell (g : Game) (p : PlayerId) (id : ObjectId) (asAdventure : Bool := false)
    (sneakAttacker : Option ObjectId := none)
    (beamMeUpCreature : Option ObjectId := none) : Except String Game := do
  if !g.hasPriority p then
    throw "You don't have priority"
  if g.cantCastSpellsThisTurn p then
    throw "You can't cast spells this turn (CR 101.2)"
  if g.splitSecondOnStack then
    throw "A spell with split second is on the stack (CR 702.61a)"
  if g.combatLocksNonManaAbilities then
    throw "During combat, players can't cast spells (Yuriko, Blade of the Mighty)"
  if g.opponentsCantCastOnActiveTurn p then
    throw "Opponents can't cast spells during that player's turn"
  let some card := g.findObject? id | throw "no such object"
  if !g.mayPlay p card then
    throw (g.playZoneError p card)
  let bc := g.baseCard card
  if asAdventure then
    if bc.adventure.isNone then
      throw s!"{g.name card} has no Adventure"
    if g.adventureExileForbidsRecast card (some p) then
      throw "You may not cast that card as an Adventure this way (CR 716.3d)"
  let rawFace :=
    match asAdventure, bc.adventure with
    | true, some adv => adv.toCardDef
    | _, _ => bc
  let kwFace :=
    if asAdventure then rawFace
    else { bc with keywords := g.currentKeywords card }
  let pl := g.player p
  let sneakCost ← match sneakAttacker with
    | none => pure none
    | some a =>
      let some c := kwFace.sneakCost | throw s!"{rawFace.name} has no sneak cost"
      if !g.canCastForSneak p then
        throw "Sneak can be paid only during the declare blockers step on your turn"
      let some att := g.findObject? a | throw "no such object"
      if !(att.isOnBattlefield && g.isCreature att && g.controlledBy att p &&
          att.status.attacking && !att.status.blocked) then
        throw s!"{g.name att} is not an unblocked attacker you control"
      pure (some c)
  let beamMeUpCost ← match beamMeUpCreature with
    | none => pure none
    | some cid =>
      if card.zone != .graveyard p then
        throw "Beam me up can only be paid from your graveyard (CR 702.196a)"
      if !(rawFace.types.contains .instant || rawFace.types.contains .sorcery) then
        throw s!"{rawFace.name} must be an instant or sorcery to cast with beam me up (CR 702.196a)"
      let some _ := g.effectiveBeamMeUpCost? p card
        | throw s!"{rawFace.name} has no beam me up cost"
      let some crea := g.findObject? cid | throw "no such object"
      if !(crea.isOnBattlefield && g.isCreature crea && g.controlledBy crea p) then
        throw s!"{g.name crea} is not a creature you control"
      if g.cantBeBeamedUp crea then
        throw s!"{g.name crea} can't be beamed up (CR 702.196b)"
      let some bmuSpec := g.effectiveBeamMeUpCostFor? p card (some cid)
        | throw s!"{g.name crea} can't be beamed up to cast {rawFace.name} this way (CR 702.196b)"
      pure (some bmuSpec.mana)
  let allPerms :=
    g.playPermissionsFor p card ++
      (if card.zone == .exile && g.mayCastExiledBySource p card then
        #[{ player := p, anyMana := true }]
       else #[])
  let cleanPerms :=
    allPerms.filter fun pm =>
      !pm.withoutManaCost && !pm.payLifeEqualManaValue && pm.prepareSource.isNone
  let candPerms :=
    let p1 := if asAdventure then allPerms.filter (!·.fromAdventure) else allPerms
    let p2 :=
      if sneakCost.isSome then
        let nonAlt := p1.filter (fun pm => !pm.withoutManaCost && !pm.payLifeEqualManaValue)
        if nonAlt.isEmpty then p1 else nonAlt
      else p1
    let baseTimingOk := g.timingAllowsCast p rawFace (card? := some card) || sneakCost.isSome
    let p3 :=
      if !baseTimingOk && p2.any (·.ignoreTiming) then p2.filter (·.ignoreTiming) else p2
    let mv := if asAdventure then rawFace.manaValue else g.objectManaValue card
    let p4 :=
      let lifeOk := p3.filter (fun pm => !pm.payLifeEqualManaValue || g.canPayLife p mv)
      if lifeOk.isEmpty then p3 else lifeOk
    p4
  let mvForRank := if asAdventure then rawFace.manaValue else g.objectManaValue card
  let rankPerm (pm : PlayPermission) : Nat :=
    (if pm.withoutManaCost then 16 else 0) +
      (if pm.payLifeEqualManaValue && g.canPayLife p mvForRank then 8 else 0) +
      (if pm.anyMana then 4 else 0) +
      (if pm.ignoreTiming then 2 else 0) +
      (if !pm.fromAdventure then 1 else 0)
  let origPerm : Option PlayPermission :=
    if candPerms.isEmpty then
      none
    else
      candPerms.foldl (fun best? pm =>
        match best? with
        | none => some pm
        | some b => if rankPerm pm >= rankPerm b then some pm else some b) none
  let prepPerm :=
    origPerm <|>
      (if card.zone == .exile && allPerms.isEmpty && !g.mayCastExiledBySource p card then
        (g.playPermissionEntriesOf card.id).findSome? (fun (_, _, pm, _) =>
          if pm.prepareSource.isSome then some pm else none)
       else none)
  match prepPerm.bind (·.prepareSource) with
  | some src =>
    match g.findObject? src with
    | some perm =>
      if !perm.isOnBattlefield || !perm.status.prepared then
        throw s!"{g.name perm} is not prepared"
      if !g.controlledBy perm p then
        throw s!"Only {g.name perm}'s controller may cast this copy (ruling 744)"
    | none => throw "The prepared permanent is gone"
  | none => pure ()
  let fromGraveyard := card.zone == .graveyard card.owner
  let hadFlashbackPerm := fromGraveyard && beamMeUpCost.isNone && g.flashbackUntilEot card
  let isFlashbackCast := fromGraveyard && beamMeUpCost.isNone && (kwFace.flashback.isSome || hadFlashbackPerm)
  if fromGraveyard && !isFlashbackCast && beamMeUpCost.isNone &&
      !g.controlsStaticPlayFromZone p card .graveyard then
    throw s!"Cast {rawFace.name} from your graveyard with its beam me up cost (CR 702.196a)"
  if (sneakCost.isSome || beamMeUpCost.isSome) &&
      ((sneakCost.isSome && beamMeUpCost.isSome) || isFlashbackCast ||
        (origPerm.any (fun pm => pm.withoutManaCost || pm.payLifeEqualManaValue) &&
          !g.mayCastExiledBySource p card)) then
    throw "You can't apply more than one alternative cost to a spell (CR 118.9a)"
  let origPerm :=
    if sneakCost.isSome &&
        origPerm.any (fun pm => pm.withoutManaCost || pm.payLifeEqualManaValue) &&
        g.mayCastExiledBySource p card then
      some { player := p, anyMana := true }
    else origPerm
  let morphPermOk :=
    allPerms.isEmpty || !cleanPerms.isEmpty || g.mayCastExiledBySource p card
  let morphCandidateOk :=
    !asAdventure && sneakCost.isNone && beamMeUpCost.isNone && !isFlashbackCast && morphPermOk &&
      kwFace.morph.isSome && kwFace.kicker.isNone &&
      !fromGraveyard && g.canCastMorphFaceDown p card
  let origPerm :=
    if (origPerm.bind (·.prepareSource)).isSome && morphCandidateOk &&
        !(g.validateFrontFaceCast p card rawFace (sneakCost := sneakCost) (sneakAttacker := sneakAttacker) (origPermOverride := origPerm)).isOk then
      let morphClean :=
        cleanPerms.filter (fun pm => pm.ignoreTiming || g.timingAllowsCast p morphSpellFace)
      morphClean.foldl (fun best? pm =>
        match best? with
        | none => some pm
        | some b => if rankPerm pm >= rankPerm b then some pm else some b) none
    else origPerm
  let altCost :=
    sneakCost.isSome || beamMeUpCost.isSome || isFlashbackCast ||
      origPerm.any (fun pm => pm.withoutManaCost || pm.payLifeEqualManaValue)
  let hasMorphChoice :=
    morphCandidateOk && (origPerm.bind (·.prepareSource)).isNone
  if !hasMorphChoice then
    g.validateFrontFaceCast p card rawFace (sneakCost := sneakCost) (sneakAttacker := sneakAttacker) (origPermOverride := origPerm)
  -- CR 601.2a: propose the spell by moving it onto the stack. Modes and
  -- additional costs are announced at CR 601.2b, targets at CR 601.2c; mana
  -- is not required yet (CR 601.2g). CR 716.3: an adventurer card may be
  -- cast as its Adventure.
  let needsSacrifice := (g.mandatorySacrificeFilterFor? card rawFace).isSome
  let original := card
  let origSnap := g.snapshot original
  let fromTop :=
    original.zone == .library p && (g.player p).library.back? == some id
  let prepSrc := origPerm.bind (·.prepareSource)
  let g := g.change .saveProposalCheckpoint
  let (g, newId) := g.move id .stack (some p) (verb := some .cast) (actor := some p)
    (isCopy := if prepSrc.isSome then some true else none)
    (overridePrinted := if asAdventure then some rawFace else none)
    (adventurerCard := if asAdventure then some original.printed else none)
    (cause := some (.gameRule .spellCast))
  let some spellObj := (g.findObject? newId).filter (·.zone == .stack)
    | throw s!"{original.printed.name} cannot be moved to the stack"
  let g :=
    if hadFlashbackPerm then
      g.createEffect (.flashbackUntilEot newId) (cause := some (.gameRule .spellCast))
    else g
  -- CR 601.2a / 601.2f: the total cost is determined after the spell is on
  -- the stack (rulings 824 / 874).
  let casterCard := { original with controller := some p }
  let cost :=
    match sneakCost, beamMeUpCost with
    | some c, _ => g.playManaCost casterCard { rawFace with manaCost := c }
        (origPerm := origPerm)
        (flashback := some isFlashbackCast) (explicitAltCost := true)
        (useImplicitPermissions := false)
    | _, some c => g.playManaCost casterCard { rawFace with manaCost := c }
        (origPerm := origPerm)
        (flashback := some false) (explicitAltCost := true)
        (useImplicitPermissions := false)
    | none, none => g.playManaCost casterCard rawFace
        (origPerm := origPerm)
        (flashback := some isFlashbackCast) (explicitAltCost := false)
        (useImplicitPermissions := false)
  -- Casting the exiled copy of a prepare spell unprepares its permanent. The
  -- spell on the stack is a copy, so it isn't put into a graveyard later
  -- (CR 707.10 / 704.5e).
  let g :=
    match prepSrc with
    | some src =>
      match g.findObject? src with
      | some perm =>
        let permName := g.name perm
        (g.record (GameEvent.designation g.turnNumber (g.snapshot perm) .prepared false
          (cause := .gameRule .spellCast))).logMsg
          s!"{permName} is no longer prepared"
      | none => g
    | none => g
  let g := g.change (.castingFromTop (fromTop || g.castingFromTop))
  let g := g.putStackEntry p newId
  let way : CastWay :=
    if (origPerm.bind (·.prepareSource)).isSome then .alternative "prepare"
    else if asAdventure then .alternative "adventure"
    else if sneakAttacker.isSome then .alternative "sneak"
    else if beamMeUpCreature.isSome then .alternative "beam me up"
    else if isFlashbackCast then .alternative "flashback"
    else if origPerm.isSome then .alternative "permission"
    else .normal
  let g := g.record (GameEvent.proposed g.turnNumber newId p original.zone way)
  let needsMode := isModalSpellFace rawFace
  let spellObj := (g.findObject? newId).getD spellObj
  let needsTarget :=
    !needsMode &&
      ((g.currentSpellEffect spellObj).any (·.requiresTarget) || g.isAura spellObj)
  let needsAdditionalCostChoice := rawFace.announcesAdditionalCost
  let impPermOk :=
    match kwFace.impending, kwFace.kicker with
    | some (_, alt), none =>
      let impFace := { rawFace with manaCost := alt }
      !asAdventure && sneakCost.isNone && beamMeUpCost.isNone && !isFlashbackCast &&
        (origPerm.bind (·.prepareSource)).isNone &&
        (if !allPerms.isEmpty then
          cleanPerms.any (fun pm => pm.ignoreTiming || g.timingAllowsCast p impFace (excludeStackId := some newId) (card? := some spellObj))
         else
          g.timingAllowsCast p impFace (excludeStackId := some newId) (card? := some spellObj))
    | _, _ => false
  let needsKicker :=
    kwFace.kicker.isSome || hasMorphChoice || impPermOk
  let needsGift := kwFace.hasGift
  let needsTeamwork := kwFace.teamwork.isSome
  -- CR 702.34a: a flashback cost that includes discarding a card.
  let needsFlashbackDiscard := isFlashbackCast && kwFace.flashbackDiscard
  if needsFlashbackDiscard && (g.discardableHandIds p).isEmpty then
    throw s!"{rawFace.name}'s flashback cost requires discarding a card"
  -- CR 118.9 / 202.3 / 716.3a–b: "pay life equal to its mana value" (Inside Information)
  -- reads the spell on the stack, so an Adventure pays its Adventure's mana value.
  let lifeInstead :=
    match origPerm with
    | some perm =>
      if perm.payLifeEqualManaValue then
        match g.findObject? newId with
        | some spell => g.objectManaValue spell
        | none => g.objectManaValue original
      else 0
    | none => 0
  if !needsMode && !needsTarget && !cost.includesManaPayment && !cost.containsX &&
      lifeInstead == 0 && !needsSacrifice && !needsFlashbackDiscard &&
      !needsAdditionalCostChoice && !needsKicker && !needsGift && !needsTeamwork &&
      sneakAttacker.isNone && beamMeUpCreature.isNone then
    return (g.becomeCast p spellObj).resumeAfterBecomeCast
  let prop : ProposedSpell := {
    caster := p
    cost := cost
    spellId := newId
    original := original
    originalSnapshot := origSnap
    origPerm
    needsSacrificeOther := needsSacrifice
    needsDiscardCard := needsFlashbackDiscard
    payLife := lifeInstead
    sneakAttacker
    beamMeUpCreature
    alternativeCost := altCost
  }
  let g := g.logMsg s!"{pl.name} begins casting {rawFace.name}"
  return g.enterProposalWindow p pl prop needsMode needsTarget "CR 601.2b / 700.2"
    (needsAdditionalCost := needsAdditionalCostChoice)
    (needsKicker := needsKicker) (needsGift := needsGift)
    (needsTeamwork := needsTeamwork)
    (needsMorphFirst := hasMorphChoice)

/-- Announce the chosen mode for a modal spell or activated ability
(CR 601.2b / 700.2). -/
def announceMode (g : Game) (p : PlayerId) (mode : Nat) : Except String Game := do
  match g.pending with
  | .chooseMode caster =>
    if caster != p then
      throw s!"Only {(g.player caster).name} may choose a mode (CR 601.2b)"
    let some prop := g.proposedSpell
      | throw "No spell or ability is waiting for a mode (CR 601.2b)"
    match prop.kind with
    | .activatedAbility =>
      let some rawChosen := prop.abilityModes[mode]?
        | throw "No such mode (CR 601.2b)"
      let some _obj := g.findObject? prop.spellId | throw "The ability left the stack"
      if !g.sourceStillPayable prop then
        return (← g.reverseProposedSpell? (resumeContinuation := true))
      let chosen := g.expandEachOpponentEffect p rawChosen (some prop.spellId)
      if !g.modeIsChoosable p chosen prop.sourceId (stackSelfId := some prop.spellId) then
        throw "That mode requires a target (CR 700.2a)"
      let g := g.record (GameEvent.announced g.turnNumber prop.spellId (modes := #[mode]))
      let g := g.record (GameEvent.facedDilemma g.turnNumber p (source? := prop.sourceId))
      let g := g.changeObject prop.spellId (.abilityEffect (some chosen))
      let nextOverride :=
        if chosen.targetSpec != rawChosen.targetSpec then some chosen.targetSpec else none
      let g :=
        if prop.targetSpecOverride != nextOverride then
          g.change (.proposedSpell (some { prop with targetSpecOverride := nextOverride }))
        else g
      let g := g.logMsg
        s!"{(g.player p).name} chooses a mode: {rawChosen.toNotation} (CR 601.2b)"
      if chosen.requiresTarget then
        let g := g.change (.pending (.chooseTargets p))
        return g.logMsg s!"{(g.player p).name} must choose a target (CR 601.2c)"
      return g.afterTargetsChosen
    | .spell =>
      let some spell := g.findObject? prop.spellId | throw "The spell left the stack"
      let face := g.baseCard spell
      if !isModalSpellFace face then
        throw "That spell is not modal (CR 700.2)"
      let effModes := g.evalSpellModes p spell
      let some effect := effModes[mode]? | throw "No such mode (CR 700.2)"
      if !g.sourceStillPayable prop then
        return (← g.reverseProposedSpell? (resumeContinuation := true))
      if !g.spellModeIsChoosable p effect (some spell.id) then
        throw "That mode has no legal target (CR 700.2a)"
      let chosen := g.chosenModesOf spell
      if chosen.contains mode then
        throw "That mode was already chosen (CR 700.2)"
      let g := if chosen.isEmpty then g.setProposedMode mode else g.addProposedExtraMode mode
      -- CR 700.17: facing a dilemma occurs once per modal spell/ability when one or more modes are chosen.
      let g := if chosen.isEmpty then g.record (GameEvent.facedDilemma g.turnNumber p (source? := some spell.id)) else g
      let g := g.logMsg
        s!"{(g.player p).name} chooses mode {mode + 1} ({effect.toNotation}) (CR 601.2b)"
      let chosen := chosen.push mode
      let more := (List.range effModes.size).any (fun i =>
        !chosen.contains i && g.spellModeIsChoosable p effModes[i]! (some spell.id))
      if chosen.size < g.maxModesFor p face && more then
        let g := g.change (.pending (.chooseMode p))
        return g.logMsg s!"{(g.player p).name} may choose another mode, or decline (CR 700.2)"
      return g.afterModesChosen p
    | .turnFaceUp => throw "Not time to choose a mode (CR 601.2b)"
  | _ => throw "Not time to choose a mode (CR 601.2b)"

/-- Announce the value of `{X}` for a proposed spell or ability
(CR 107.3a / 601.2b). Substitutes `{X}` into the locked-in cost and
continues the proposal window. -/
def announceX (g : Game) (p : PlayerId) (x : Nat) : Except String Game := do
  match g.pending with
  | .chooseX caster =>
    if caster != p then
      throw s!"Only {(g.player caster).name} may choose a value for X (CR 601.2b)"
    let some prop := g.proposedSpell
      | throw "No spell or ability is waiting for X (CR 601.2b)"
    let some _obj := g.findObject? prop.spellId
      | throw "The spell or ability left the stack"
    if !g.sourceStillPayable prop then
      return (← g.reverseProposedSpell? (resumeContinuation := true))
    if prop.kind == .spell then
      if let some mx := prop.maxCastManaValue? then
        let stackFace := g.baseCard (g.object! prop.spellId)
        if (stackFace.manaCost.substituteX x).manaValue > mx then
          throw s!"The resulting spell's mana value can't exceed {mx} (CR 701.57a)"
    let g := g.record (GameEvent.announced g.turnNumber prop.spellId (x := some x))
    if prop.loyaltyX then
      let some src := prop.sourceId.bind g.findObject?
        | throw "The planeswalker left the battlefield"
      if let some k := prop.activation.bind (·.cost.netLoyaltyDelta x) then
        if k < 0 && (src.status.loyaltyCounters : Int) < -k then
          throw s!"{g.name src} doesn't have {-k} loyalty counters to remove (CR 606.4)"
    if prop.removePlusOneX then
      let some src := prop.sourceId.bind g.findObject?
        | throw "The source left the battlefield"
      if src.status.plusOnePlusOne < x then
        throw s!"{g.name src} doesn't have {x} +1/+1 counters to remove"
    let cost :=
      match prop.kind, prop.activation, prop.sourceId.bind g.findObject? with
      | .activatedAbility, some ab, src =>
        g.activationManaCost p ab (source := src) (chosenX := some x)
      | .spell, _, _ =>
        let spell := g.object! prop.spellId
        let preSpell := { spell with
          id := prop.original.id
          zone := prop.original.zone
          exiledBy := prop.original.exiledBy
          controller := some p }
        let baseFace := g.baseCard spell
        let kwFace := { baseFace with keywords := g.proposedSpellKeywords prop spell }
        let face :=
          match prop.sneakAttacker, kwFace.sneakCost, prop.beamMeUpCreature, g.effectiveBeamMeUpCost? p prop.original with
          | some _, some sc, _, _ => { baseFace with manaCost := sc }
          | _, _, some _, some bmu => { baseFace with manaCost := bmu.mana }
          | _, _, _, _ => baseFace
        g.playManaCost preSpell face (ManaCost.ofGeneric prop.additionalGeneric)
          (origPerm := prop.origPerm)
          (flashback := some (GameEvent.castWithFlashback g.events prop.spellId))
          (explicitAltCost := prop.sneakAttacker.isSome || prop.beamMeUpCreature.isSome)
          (useImplicitPermissions := false)
      | _, _, _ => prop.cost.substituteX x
    let extraChanges : Array ProposalChange :=
      if prop.kind == .spell && prop.origPerm.any (·.payLifeEqualManaValue) then
        #[.payLife (g.objectManaValue (g.object! prop.spellId))]
      else #[]
    let g := g.changeProposals (#[.cost cost] ++ extraChanges)
    let prop := g.proposedSpell.getD prop
    let g := g.logMsg
      s!"{(g.player p).name} chooses X = {x} (CR 107.3a / 601.2b)"
    let pl := g.player p
    match prop.kind with
    | .activatedAbility =>
      let needsMode :=
        match prop.activation with
        | some ab => ab.isModal
        | none => false
      let needsTarget :=
        match prop.activation with
        | some ab => (g.expandEachOpponentEffect p ab.effect).requiresTarget
        | none => false
      return g.enterProposalWindow p pl prop needsMode needsTarget "CR 601.2b"
    | .spell =>
      if prop.resolutionCast then
        let g' := (g.change (.pending .none)).beginResolutionCastTargets p prop
        return if g'.pending == .none && (g'.findObject? prop.spellId).any (·.zone == .stack) then
          g'.finishResolutionChoice
        else g'
      else
        let spell := g.object! prop.spellId
        let face := g.baseCard spell
        let kwFace := { face with keywords := g.proposedSpellKeywords prop spell }
        let modal := isModalSpellFace face
        let needsTarget :=
          !modal &&
            ((g.currentSpellEffect spell).any (·.requiresTarget) || g.isAura spell)
        return g.enterProposalWindow p pl prop modal
          needsTarget "CR 601.2b / 700.2"
          (needsAdditionalCost := face.announcesAdditionalCost)
          (needsKicker := !prop.kickerAnnounced &&
            (kwFace.kicker.isSome || g.proposalCanChooseMorph prop || g.proposalCanChooseImpending prop))
          (needsGift := kwFace.hasGift)
          (needsTeamwork := kwFace.teamwork.isSome)
    | .turnFaceUp =>
      throw "Not time to choose X (CR 601.2b)"
  | _ => throw "Not time to choose X (CR 601.2b)"

/-- Announce targets for the current instance of the word “target”
(CR 601.2c / 603.3d). Multiple targets of one instance (including a
“divided as you choose” division, CR 601.2d) are chosen together. Each
further instance is a later announcement. An omitted amount on a
divided-damage ability assigns all remaining damage to that one target. -/
def announceTargetChoices (g : Game) (p : PlayerId)
    (choices : Array (Target × Option Nat)) : Except String Game := do
  match g.pending with
  | .chooseTargets caster =>
    if caster != p then
      throw s!"Only {(g.player caster).name} may choose targets (CR 601.2c)"
    let some obj := g.objectAwaitingTargets | throw "No spell is waiting for a target (CR 601.2c)"
    if choices.isEmpty then
      throw "Choose a target (CR 601.2c)"
    match obj.triggeredAbility.bind TriggeredAbility.dividedDamage? with
    | some (total, maxTargets) =>
      let some e := g.stackEntry? obj.id | throw "The ability left the stack"
      if !e.targets.isEmpty || assignedDividedDamage e != 0 then
        throw "Those targets must be chosen at the same time (CR 601.2c)"
      if total == 0 then
        throw "All damage has already been divided (CR 601.2d)"
      let assignments : Array (Target × Nat) ←
        if choices.size == 1 && choices[0]!.2.isNone then
          pure #[(choices[0]!.1, total)]
        else if choices.any (fun c => c.2.isNone) then
          throw "Each target must be assigned a damage amount (CR 601.2d)"
        else
          pure (choices.map (fun c => (c.1, c.2.getD 0)))
      if assignments.size > maxTargets then
        throw s!"Cannot choose more than {maxTargets} targets (CR 601.2d)"
      let legal := g.legalProposedTargets p obj
      let mut assigned : Nat := 0
      let mut targets : Array Target := #[]
      let mut amounts : Array Nat := #[]
      for (t, n) in assignments do
        if !legal.contains t then
          throw "Illegal target (CR 601.2c)"
        if targets.contains t then
          throw "Illegal target (CR 601.2c)"
        if n == 0 then
          throw "Each target must be dealt at least 1 damage (CR 601.2d)"
        assigned := assigned + n
        targets := targets.push t
        amounts := amounts.push n
      if assigned > total then
        throw s!"Only {total} damage remains to divide (CR 601.2d)"
      if assigned < total then
        throw "Must assign all remaining damage among the chosen targets (CR 601.2d)"
      let mut g := g.setStackEntryTargets obj.id targets amounts
      for (t, n) in assignments do
        g := g.logMsg
          s!"{(g.player p).name} chooses {g.targetLogName t} to be dealt {n} damage (CR 601.2d)"
      return g.afterTriggerTargetsChosen
    | none =>
      if choices.any (fun c => c.2.isSome) then
        throw "That spell or ability does not divide damage (CR 601.2d)"
      let some e := g.stackEntry? obj.id | throw "The ability left the stack"
      let spec := g.targetSpecOf obj
      let (minN, maxN) := g.announcedTargetBounds obj
      let selfSource := obj.sourceId.orElse (fun _ => if obj.zone == .stack then some obj.id else none)
      if !spec.isMultiSlot then
        if !e.targets.isEmpty then
          throw "Those targets must be chosen at the same time (CR 601.2c)"
        if choices.size < minN then
          throw s!"Choose at least {minN} target(s) (CR 601.2c)"
        if choices.size > maxN then
          throw s!"Cannot choose more than {maxN} targets (CR 601.2c)"
        let legal := g.legalProposedTargets p obj
        let mut targets : Array Target := #[]
        for (t, _) in choices do
          if !legal.contains t then
            throw "Illegal target (CR 601.2c)"
          if targets.contains t then
            throw "Illegal target (CR 601.2c)"
          targets := targets.push t
        if let some slot := spec.slots[0]? then
          if let some gc := slot.groupConstraint? then
            if !g.satisfiesGroupConstraint p selfSource gc targets then
              throw "Illegal target (CR 601.2c)"
        let mut g := g.setStackEntryTargets obj.id targets
        for t in targets do
          g := g.logMsg
            s!"{(g.player p).name} chooses {g.targetLogName t} as a target (CR 601.2c)"
        if g.proposedSpell.any (·.spellId == obj.id) then
          return g.afterTargetsChosen
        return g.afterTriggerTargetsChosen
      let curPos := g.currentTargetSlot obj
      let (grpStart, grpEnd) := spec.instanceGroupBounds curPos
      if curPos != grpStart || choices.size > grpEnd - grpStart then
        throw "Choose each instance of the word \"target\" separately (CR 601.2c)"
      let trailingPos := (List.range grpEnd).drop (curPos + choices.size)
      if !trailingPos.all spec.isOptionalPos then
        let reqCount := ((List.range grpEnd).drop grpStart).filter (!spec.isOptionalPos ·) |>.length
        throw s!"Choose at least {reqCount} target(s) (CR 601.2c)"
      let mut gCheck := g
      let mut curTargets := e.targets
      for (t, _) in choices do
        let some curObj := gCheck.findObject? obj.id
          | throw "The ability left the stack"
        if !(gCheck.legalProposedTargets p curObj).contains t then
          throw "Illegal target (CR 601.2c)"
        curTargets := curTargets.push t
        gCheck := gCheck.setStackEntryTargets obj.id curTargets
      let mut g := g
      for posIdx in trailingPos do
        g := g.change (.stackEntry obj.id (.skipOptionalSlot posIdx))
      g := g.setStackEntryTargets obj.id curTargets
      for (t, _) in choices do
        g := g.logMsg
          s!"{(g.player p).name} chooses {g.targetLogName t} as a target (CR 601.2c)"
      if g.currentTargetSlot obj < spec.totalPositions then
        return (g.markTargetsAnnounced obj.id false).change (.pending (.chooseTargets p))
      if g.proposedSpell.any (·.spellId == obj.id) then
        return g.afterTargetsChosen
      return g.afterTriggerTargetsChosen
  | _ => throw "Not time to choose targets (CR 601.2c)"

/-- Announce one target of the current instance of the word “target”
(CR 601.2c / 603.3d). On a divided-damage ability this assigns all remaining
damage to that target (CR 601.2d). On “one or two target creatures” this
chooses that one creature and finishes the instance. -/
def announceTarget (g : Game) (p : PlayerId) (t : Target) : Except String Game :=
  g.announceTargetChoices p #[(t, none)]

/-- Announce every target of one instance of the word “target” together
(CR 601.2c), including “one or two target creatures”. -/
def announceTargets (g : Game) (p : PlayerId) (ts : Array Target) : Except String Game :=
  g.announceTargetChoices p (ts.map (fun t => (t, none)))

/-- Announce every target of one instance of the word “target” on a
“divided as you choose” effect (CR 601.2c / 601.2d). -/
def announceDividedDamage (g : Game) (p : PlayerId)
    (assignments : Array (Target × Nat)) : Except String Game :=
  g.announceTargetChoices p (assignments.map (fun (t, n) => (t, some n)))

end Game
end Mtg.Engine
