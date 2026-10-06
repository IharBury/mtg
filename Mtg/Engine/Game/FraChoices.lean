import Mtg.Engine.Game.Decisions

/-!
# Reality Fracture choices

Answers to `Pending.fraChoice`: cards or permanents chosen with
`Action.choosePermanents`, `Action.accept` / `Action.decline` for optional
actions, `Action.chooseTop` / `Action.chooseBottom` for library placement,
and `Action.chooseMode` for the modes of a modal triggered ability
(CR 603.3c / 700.2).
-/

namespace Mtg.Engine
namespace Game

/-- An answer to a `FraChoice`. -/
inductive FraAnswer where
  | accept
  | decline
  | objects (ids : Array ObjectId)
  | mode (idx : Nat)
  | name (name : String)
deriving Repr, BEq

/-- Clear the choice and let the game continue. -/
def finishFraChoice (g : Game) : Game :=
  if g.pending != .none then g
  else
    let g := g.promptTriggerTargetsIfNeeded
    if g.pending == .none then g.receivePriority g.activePlayer else g

/-- Combine the chosen modes of a modal triggered ability into one effect.
At most one chosen mode targets. -/
def combineTriggerModes (modes : Array Effect) (chosen : Array Nat) : Option Effect :=
  let picked := (chosen.qsort (· < ·)).filterMap (modes[·]?)
  match picked.toList with
  | [] => none
  | [e] => some e
  | es =>
    let targeted := es.find? (·.requiresTarget)
    let base := targeted.getD (es.head!)
    some { base with
      resolution := .sequence (es.map (·.resolution))
      phrase := String.intercalate ". " (es.map (·.phrase)) }

/-- Cast one of the copies of a pending “cast copies without paying their mana
costs” choice (Uldaros Theorix). X is 0 (ruling 806). -/
def castFreeCopy (g : Game) (p : PlayerId) (id : ObjectId) : Except String Game := do
  let .fraChoice q (.castCopiesFree ids budget castsLeft) := g.pending | throw "No copy may be cast now"
  if p != q then throw s!"Only {(g.player q).name} may cast the copies"
  if !ids.contains id then throw "That isn't one of the copies"
  let some card := g.findObject? id | throw "no such object"
  let face := card.printed
  let mv := g.objectManaValue card
  if mv > budget then
    throw s!"{face.name} has mana value {mv}; only {budget} is left"
  if face.isLand then throw "A land can't be cast"
  if !face.isModal && face.requiresTarget && (g.legalCastTargets p face).isEmpty &&
      !face.allowsZeroTargets then
    throw s!"{face.name} requires a target"
  let rest := ids.filter (· != id)
  let stackBefore := g.stack
  let pool := (g.player p).manaPool
  let (g, newId) := g.move id .stack (some p)
  let g := g.setObject { (g.object! newId) with isCopy := true }
  let g := g.putStackEntry p newId
  let g := { g with pending := .none, pendingFreeCopies := some (p, rest, budget - mv, castsLeft - 1) }
  let g := g.logMsg s!"{(g.player p).name} casts a copy of {face.name} without paying its mana cost"
  let prop : ProposedSpell := {
    caster := p, cost := ManaCost.empty, spellId := newId, original := card
    handBefore := (g.player p).hand, stackBefore, manaBefore := pool }
  if face.isModal then
    return { g with pending := .chooseMode p, proposedSpell := some prop }
  else if face.requiresTarget then
    return { g with pending := .chooseTargets p, proposedSpell := some prop }
  else
    return g.becomeCast p (g.object! newId)

/-- Hawkeye's Trick Arrows with the chosen modes, in printed order. -/
def hawkeyeArrowsEffect (modes : Array Nat) : Effect :=
  let sorted := modes.qsort (· < ·)
  let kinds := sorted.filterMap (fun m =>
    if m == 0 then some EffectTargetKind.creature
    else if m == 1 then some EffectTargetKind.player
    else none)
  let targeting : EffectTargeting :=
    match kinds.toList with
    | [k] => .of k
    | [a, b] => .of (.pair a b)
    | _ => .of .none
  let names := sorted.toList.map (fun m =>
    if m == 0 then "Net — Target creature can't block this turn"
    else if m == 1 then "Explosive — Hawkeye deals 2 damage to target player"
    else "Boomerang — Discard a card, then draw a card")
  { targeting, resolution := .fra (.hawkeyeArrows sorted.toList)
    phrase := String.intercalate ". " names }

/-- Reveal the face-up pile, then let an opponent choose which pile goes to hand. -/
def continueRiddlesSplit (g : Game) (controller : PlayerId)
    (faceUp faceDown : Array ObjectId) : Game :=
  let g :=
    faceUp.foldl (fun acc id =>
      match acc.findObject? id with
      | some o => acc.logMsg s!"{(acc.player controller).name} reveals {o.name}"
      | none => acc) g
  match (g.livingOpponents controller)[0]? with
  | some opp =>
    g.beginFraChoice opp.id (.riddlesChoosePile controller faceUp faceDown)
      s!"{opp.name} chooses which pile goes to {(g.player controller).name}'s hand"
  | none =>
    g.applyRiddlesPiles controller faceUp faceDown false

def answerFraChoice (g : Game) (p : PlayerId) (answer : FraAnswer) : Except String Game := do
  let .fraChoice q choice := g.pending | throw "Nothing to choose now"
  if p != q then
    throw s!"Only {(g.player q).name} may choose"
  let g := { g with pending := .none }
  match choice, answer with
  | .discardFromRevealedHand victim permanentOnly, .objects #[id] =>
    if !(g.revealedHandChoices victim permanentOnly).contains id then
      throw "That card can't be chosen"
    return (g.discardFromHand victim id (chooser := some p)).finishFraChoice
  | .discardFromRevealedHand .., _ => throw "Choose one card from the revealed hand"
  | .mayWheel n rest, .accept | .mayWheel n rest, .decline =>
    let g :=
      if answer == .accept then
        let hand := (g.player p).hand
        let g := hand.foldl (fun g id => g.discardFromHand p id) g
        g.draw p n
      else g.logMsg s!"{(g.player p).name} keeps their hand"
    match rest.toList with
    | [] => return g.finishFraChoice
    | next :: more =>
      return g.beginFraChoice next (.mayWheel n more.toArray)
        s!"{(g.player next).name} may discard their hand and draw {n} cards"
  | .mayWheel .., _ => throw "Answer accept or decline"
  | .maySacrificePlaneswalker, .objects #[id] =>
    let some pw := g.findObject? id | throw "no such object"
    if !pw.isOnBattlefield || !pw.controlledBy p || !pw.printed.isPlaneswalker then
      throw "Choose a planeswalker you control"
    let g := g.sacrificeToGraveyard pw s!"{(g.player p).name} sacrifices {pw.name}"
    let g := g.resolveSearchLibrary p (·.isPlaneswalker) false "planeswalker card"
    return g.finishFraChoice
  | .maySacrificePlaneswalker, .decline =>
    return (g.logMsg s!"{(g.player p).name} doesn't sacrifice a planeswalker").finishFraChoice
  | .maySacrificePlaneswalker, _ => throw "Choose a planeswalker to sacrifice, or decline"
  | .topOrBottomDamage id damage, .accept | .topOrBottomDamage id damage, .decline =>
    match g.findObject? id with
    | none => return g.finishFraChoice
    | some o =>
      if !o.isOnBattlefield then return g.finishFraChoice
      else
        let owner := o.owner
        let (g, newId) := g.move id (.library owner) none
        if answer == .accept then
          let g := g.logMsg s!"{(g.player owner).name} puts {o.name} on top of their library"
          return (g.dealDamageToPlayer owner damage).finishFraChoice
        else
          let g := g.modifyPlayer owner (fun pl =>
            { pl with library := #[newId] ++ pl.library.filter (· != newId) })
          let g := g.logMsg s!"{(g.player owner).name} puts {o.name} on the bottom of their library"
          return g.finishFraChoice
  | .topOrBottomDamage .., _ => throw "Choose top or bottom"
  | .sphinxsApproach _, .accept =>
    let approaches := g.sphinxsApproachesInGraveyard p
    if approaches.size < 5 then
      return (g.logMsg "There aren't five cards named Sphinx's Approach to exile").finishFraChoice
    let g := (approaches.extract 0 5).foldl (fun g id =>
      let (g, _) := g.move id .exile none
      g) g
    let g := g.logMsg s!"{(g.player p).name} exiles five cards named Sphinx's Approach"
    let g := g.resolveSearchLibrary p (fun c => c.isCreature && c.hasSubtype "Sphinx") false
      "Sphinx creature card"
    return g.finishFraChoice
  | .sphinxsApproach _, .decline => return g.finishFraChoice
  | .sphinxsApproach _, _ => throw "Answer accept or decline"
  | .extrapolateReveal, .objects #[a, b] =>
    let ok (id : ObjectId) := (g.findObject? id).any (·.zone == .outside p)
    if !ok a || !ok b then throw "Choose two cards you own from outside the game"
    if (g.object! a).name == (g.object! b).name then
      throw "The two cards must have different names"
    let g := g.logMsg s!"{(g.player p).name} reveals {(g.object! a).name} and {(g.object! b).name}"
    match (g.livingOpponents p)[0]? with
    | none => return g.finishFraChoice
    | some opp =>
      return g.beginFraChoice opp.id (.extrapolatePick p #[a, b])
        s!"{opp.name} chooses one of them"
  | .extrapolateReveal, .decline => return g.finishFraChoice
  | .extrapolateReveal, _ => throw "Choose two cards from outside the game, or decline"
  | .extrapolatePick revealer ids, .objects #[id] =>
    if !ids.contains id then throw "Choose one of the revealed cards"
    let name := (g.object! id).name
    let (g, _) := g.move id (.hand revealer) none
    let g := g.logMsg s!"{(g.player revealer).name} puts {name} into their hand"
    return g.finishFraChoice
  | .extrapolatePick .., _ => throw "Choose one of the revealed cards"
  | .mayPutMilledPermanent ids life, .objects #[id] =>
    if !ids.contains id then throw "Choose a permanent card milled this way"
    let g := g.returnToHand id p
    return (g.gainLife p life).finishFraChoice
  | .mayPutMilledPermanent _ life, .decline =>
    return (g.gainLife p life).finishFraChoice
  | .mayPutMilledPermanent .., _ => throw "Choose a milled permanent card, or decline"
  | .mayThen next sourceId, .accept =>
    return (g.applyFra p default next.toResolution #[] sourceId).finishFraChoice
  | .mayThen .., .decline => return g.finishFraChoice
  | .mayThen .., _ => throw "Answer accept or decline"
  | .mayPayThen n next sourceId, .accept =>
    if !(g.player p).manaPool.canPay (ManaCost.ofGeneric n) then
      throw s!"{(g.player p).name} cannot pay \{{n}}; add mana first"
    let g ← g.payCost p (ManaCost.ofGeneric n)
    let g := g.logMsg s!"{(g.player p).name} pays \{{n}}"
    return (g.applyFra p default next.toResolution #[] sourceId).finishFraChoice
  | .mayPayThen .., .decline => return g.finishFraChoice
  | .mayPayThen .., _ => throw "Pay or decline"
  | .mayDiscardThen next sourceId, .objects #[id] =>
    if !(g.player p).hand.contains id then throw "That card is not in your hand"
    let g := g.discardFromHand p id
    return (g.applyFra p default next.toResolution #[] sourceId).finishFraChoice
  | .mayDiscardThen .., .decline => return g.finishFraChoice
  | .mayDiscardThen .., _ => throw "Choose a card to discard, or decline"
  | .discardThen _ _ causeId, .objects #[id] =>
    if !(g.player p).hand.contains id then throw "That card is not in your hand"
    let g := g.discardFromHand p id
    let g := g.draw p 1
    let n := (g.player p).cardsDiscardedThisTurn
    let g :=
      match causeId.bind (fun c => g.findObject? (g.followMoved c)) with
      | some o => if o.isOnBattlefield && n > 0 then g.addPlusOnePlusOneTo o n else g
      | none => g
    return g.finishFraChoice
  | .discardThen .., _ => throw "Choose a card to discard"
  | .discardThenStun n sourceId, .objects ids =>
    let need := Nat.min n (g.player p).hand.size
    if ids.size != need || !ids.all ((g.player p).hand.contains ·) ||
        ids.toList.eraseDups.length != ids.size then
      throw s!"Choose {need} different cards from your hand"
    let nonland := (ids.filter (fun id => !(g.object! id).printed.isLand)).size
    let g := ids.foldl (fun g id => g.discardFromHand p id) g
    let g := { g with pending := .none }
    let g :=
      if nonland == 0 then g
      else
        g.putReflexiveTrigger p sourceId
          { targeting := .of (.filtered TargetFilter.creature), maxTargets := nonland
            allowsZeroTargets := true, resolution := .fra .tapAndStunPerOpponent
            phrase := "Tap up to that many target creatures and put a stun counter on each of them" }
    return g.finishFraChoice
  | .discardThenStun .., _ => throw "Choose the cards to discard"
  | .maySacrificeThen kind next sourceId, .objects #[id] =>
    let some o := g.findObject? id | throw "no such object"
    let ok :=
      o.isOnBattlefield && o.controlledBy p &&
        match kind with
        | .land => o.printed.isLand
        | .creatureOrPlaneswalker => o.isCreature || o.printed.isPlaneswalker
        | .creature => o.isCreature
    if !ok then throw s!"Can't sacrifice {o.name}"
    let g := g.sacrificeToGraveyard o s!"{(g.player p).name} sacrifices {o.name}"
    return (g.applyFra p default next.toResolution #[] sourceId).finishFraChoice
  | .maySacrificeThen .., .decline => return g.finishFraChoice
  | .maySacrificeThen .., _ => throw "Choose a permanent to sacrifice, or decline"
  | .mayMovePlusOne sourceId, .accept =>
    match g.findObject? sourceId with
    | some o =>
      if o.isOnBattlefield && o.status.plusOnePlusOne > 0 then
        let g := (g.setObject { o with status := { o.status with
          plusOnePlusOne := o.status.plusOnePlusOne - 1 } }).logMsg
          s!"A +1/+1 counter is removed from {o.name}"
        let g := (g.creaturesControlledBy p).foldl (fun g c =>
          if c.id == o.id then g else g.addPlusOnePlusOneTo (g.object! c.id) 1) g
        return g.finishFraChoice
      else return g.finishFraChoice
    | none => return g.finishFraChoice
  | .mayMovePlusOne _, .decline => return g.finishFraChoice
  | .mayMovePlusOne _, _ => throw "Answer accept or decline"
  | .exileFromRevealedHand victim sourceId, .objects #[id] =>
    if !(g.revealedHandChoices victim false).contains id then throw "Choose a nonland card"
    let name := (g.object! id).name
    let (g, ex) := g.move id .exile none
    let g := g.setObject { (g.object! ex) with exiledBy := sourceId }
    return (g.logMsg s!"{(g.player p).name} exiles {name} from {(g.player victim).name}'s hand").finishFraChoice
  | .exileFromRevealedHand .., _ => throw "Choose a nonland card from the revealed hand"
  | .castCopiesFree ids _ _, .decline =>
    let g := ids.foldl (fun g id =>
      if (g.findObject? id).any (·.zone == .exile) then g.ceaseToExist id else g) g
    return { g with pendingFreeCopies := none }.finishFraChoice
  | .castCopiesFree .., _ => throw "Cast a copy, or decline"
  | .allianceMode sourceId available, .mode idx =>
    if !available.contains idx then throw "That Alliance mode has already been chosen this turn"
    return (g.applyAllianceMode sourceId idx).finishFraChoice
  | .allianceMode .., _ => throw "Choose an Alliance mode"
  | .gollumMode sourceId available, .mode idx =>
    if !available.contains idx then throw "That mode has already been chosen"
    return (g.applyGollumMode sourceId idx).finishFraChoice
  | .gollumMode .., _ => throw "Choose a mode"
  | .triggerModes objId remaining chosen, .mode idx =>
    let some obj := g.findObject? objId | return g.finishFraChoice
    let modes := g.triggerModesOf obj
    let some e := modes[idx]? | throw "No such mode (CR 700.2)"
    if chosen.contains idx then throw "That mode was already chosen (CR 700.2)"
    if !g.triggerModeChoosable p obj e then
      throw "That mode has no legal target (CR 700.2d)"
    let g := g.logMsg s!"{(g.player p).name} chooses mode {idx + 1} ({e.phrase})"
    let chosen := chosen.push idx
    let left := remaining - 1
    let anyLeft := (List.range modes.size).any (fun i =>
      !chosen.contains i && (modes[i]?.any (g.triggerModeChoosable p obj)))
    if left > 0 && anyLeft then
      return { g with pending := .fraChoice p (.triggerModes objId left chosen) }
    match combineTriggerModes modes chosen with
    | none => return g.finishFraChoice
    | some eff =>
      let g := g.setObject { obj with abilityEffect := some eff }
      return g.finishFraChoice
  | .triggerModes .., _ => throw "Choose a mode"
  | .chooseKeyword id options, .mode idx =>
    let some code := options[idx]? | throw "No such choice"
    match g.findObject? id with
    | some o =>
      if o.isOnBattlefield then
        let g := g.logMsg s!"{(g.player p).name} chooses {fraKeywordName code}"
        return (g.grantKeywordsUntilEot o (fraKeywordOfCode code)).finishFraChoice
      else return g.finishFraChoice
    | none => return g.finishFraChoice
  | .chooseKeyword .., _ => throw "Choose one of the keywords"
  | .chooseColor id, .mode idx =>
    let some c := Color.all[idx]? | throw "Choose white, blue, black, red, or green (0-4)"
    match g.findObject? id with
    | some o =>
      let g := g.mapObjectStatus o (fun s => { s with chosenColor := some c })
      return (g.logMsg s!"{(g.player p).name} chooses {c.englishName} for {o.name}").finishFraChoice
    | none => return g.finishFraChoice
  | .chooseColor _, _ => throw "Choose a color"
  | .sacrificeCreatureEach controller rest chosen, .objects #[id] =>
    let some o := g.findObject? id | throw "no such object"
    if !o.isOnBattlefield || !o.isCreature || !o.controlledBy p then
      throw "Choose a creature you control"
    let g := g.logMsg s!"{(g.player p).name} chooses {o.name}"
    return (g.continueSacrificeEach controller rest (chosen.push id)).finishFraChoice
  | .sacrificeCreatureEach .., _ => throw "Choose a creature to sacrifice"
  | .discardTwo controller rest draws, .objects ids =>
    let hand := (g.player p).hand
    if ids.size != 2 || ids[0]! == ids[1]! || !ids.all hand.contains then
      throw "Choose two different cards from your hand"
    let nonland := (ids.filter (fun id => !(g.object! id).printed.isLand)).size
    let g := ids.foldl (fun g id => g.discardFromHand p id) g
    return (g.continueDiscardTwo controller rest (if nonland < 2 then draws + 1 else draws)).finishFraChoice
  | .discardTwo .., _ => throw "Choose two cards to discard"
  | .mayMoveAllCounters fromId toId, .accept =>
    match g.findObject? fromId, g.findObject? toId with
    | some src, some dst =>
      if !src.isOnBattlefield || !dst.isOnBattlefield then return g.finishFraChoice
      else
        let moved := src.status
        let g := g.setObject { src with status := src.status.withoutCounters }
        let dst := g.object! toId
        let g := g.setObject { dst with status := dst.status.addCountersExceptPlusOne moved }
        let g :=
          if moved.plusOnePlusOne > 0 then g.addPlusOnePlusOneTo (g.object! toId) moved.plusOnePlusOne
          else g
        return (g.logMsg s!"All counters move from {src.name} onto {dst.name}").finishFraChoice
    | _, _ => return g.finishFraChoice
  | .mayMoveAllCounters .., .decline => return g.finishFraChoice
  | .mayMoveAllCounters .., _ => throw "Answer accept or decline"
  | .chooseCardName id, .name nm =>
    if !g.isNonlandCardName nm then
      throw s!"{nm} isn't the name of a nonland card (CR 201.3)"
    match g.findObject? id with
    | some o =>
      let g := g.mapObjectStatus o (fun s => { s with chosenName := some nm })
      return (g.logMsg s!"{(g.player p).name} chooses {nm} for {o.name}").finishFraChoice
    | none => return g.finishFraChoice
  | .chooseCardName _, _ => throw "Name a nonland card"
  | .crew _ vehicleId n, .objects ids =>
    let some vehicle := g.findObject? vehicleId | throw "The Vehicle is gone"
    if ids.toList.eraseDups.length != ids.size then throw "Choose each creature once"
    let crew ← ids.mapM (fun id => do
      let some c := g.findObject? id | throw "no such object"
      if !c.isOnBattlefield || !c.isCreature || !c.controlledBy p || c.status.tapped || id == vehicleId then
        throw s!"{c.name} can't crew {vehicle.name}"
      pure c)
    let total := crew.foldl (fun acc c => acc + (g.power c).toNat) 0
    if total < n then throw s!"Total power {total} is less than {n}"
    let g := crew.foldl (fun g c => g.becomeTapped (g.object! c.id)) g
    let g := g.logMsg s!"{(g.player p).name} crews {vehicle.name}"
    return (g.becomeActivated p vehicle.name (some vehicleId)).finishFraChoice
  | .crew abilityId _ _, .decline =>
    let g := (g.removeFromZoneList abilityId .stack).ceaseToExist abilityId
    return (g.logMsg s!"{(g.player p).name} doesn't crew").receivePriority p
  | .crew .., _ => throw "Choose creatures to tap, or decline"
  | .costPicks sourceId picks _, .objects ids =>
    let some prop := g.proposedSpell | throw "No activation is being paid for"
    let some pick := picks[0]? | throw "No cost is left to pay"
    let g ← g.payCostPick p prop.spellId sourceId pick ids
    return (← g.continueCostPicks prop (picks.extract 1 picks.size) true).finishFraChoice
  | .costPicks _ _ false, .decline =>
    return g.reverseProposedSpell
  | .costPicks _ _ true, .decline =>
    throw "Part of the cost is already paid; the activation can't be cancelled"
  | .costPicks .., _ => throw "Choose what to pay the cost with, or decline to cancel"
  | .chooseCreatureType types, .mode idx =>
    let some t := types[idx]? | throw "No such creature type"
    let n := ((g.creaturesControlledBy p).filter (fun o => g.hasSubtype o t)).size
    let g := g.logMsg s!"{(g.player p).name} chooses {t}"
    return (g.createTreasureTokens p n).finishFraChoice
  | .chooseCreatureType _, .name t =>
    let n := ((g.creaturesControlledBy p).filter (fun o => g.hasSubtype o t)).size
    let g := g.logMsg s!"{(g.player p).name} chooses {t}"
    return (g.createTreasureTokens p n).finishFraChoice
  | .chooseCreatureType _, _ => throw "Choose a creature type"
  | .maySacrificeAnotherCreatureForPower sourceId, .objects #[id] =>
    let some o := g.findObject? id | throw "no such object"
    if o.id == sourceId || !o.isOnBattlefield || !o.controlledBy p || !o.isCreature then
      throw s!"Can't sacrifice {o.name}"
    let pw := (g.power o).toNat
    let g := g.sacrificeToGraveyard o s!"{(g.player p).name} sacrifices {o.name}"
    let g :=
      match g.findObject? sourceId with
      | some src => if src.isOnBattlefield then g.addPlusOnePlusOneTo src pw else g
      | none => g
    return g.finishFraChoice
  | .maySacrificeAnotherCreatureForPower _, .decline => return g.finishFraChoice
  | .maySacrificeAnotherCreatureForPower _, _ => throw "Choose a creature to sacrifice, or decline"
  | .maySacrificeAnotherForDrawTreasure sourceId, .objects #[id] =>
    let some o := g.findObject? id | throw "no such object"
    if o.id == sourceId || !o.isOnBattlefield || !o.controlledBy p ||
        !(o.isCreature || o.printed.isArtifact) then
      throw s!"Can't sacrifice {o.name}"
    let g := g.sacrificeToGraveyard o s!"{(g.player p).name} sacrifices {o.name}"
    return (g.applyFra p default .drawAndCreateTreasure #[] (some sourceId)).finishFraChoice
  | .maySacrificeAnotherForDrawTreasure _, .decline => return g.finishFraChoice
  | .maySacrificeAnotherForDrawTreasure _, _ => throw "Choose a creature or artifact to sacrifice, or decline"
  | .mayPaySymbolsThen symbols next sourceId, .accept =>
    let cost : ManaCost := { symbols := symbols }
    if !(g.player p).manaPool.canPay cost then
      throw s!"{(g.player p).name} cannot pay that cost; add mana first"
    let g ← g.payCost p cost
    return (g.applyFra p default next.toResolution #[] (some sourceId)).finishFraChoice
  | .mayPaySymbolsThen .., .decline => return g.finishFraChoice
  | .mayPaySymbolsThen .., _ => throw "Pay (accept), or decline"
  | .attachAnyEquipment hostId eligible, .objects ids =>
    if !ids.all (eligible.contains ·) || ids.toList.eraseDups.length != ids.size then
      throw "Choose Equipment you control"
    let some host := g.findObject? hostId | return g.finishFraChoice
    let mut g := g
    let mut attached : Nat := 0
    for id in ids do
      match g.findObject? id with
      | some eq =>
        if eq.attachedTo != some hostId && eq.isOnBattlefield then
          g := g.attachSourceTo eq (g.object! hostId)
          attached := attached + 1
      | none => pure ()
    if attached == 0 || !host.isOnBattlefield then
      return g.finishFraChoice
    let host := g.object! hostId
    let effect : Effect :=
      { targeting := .of .creature, allowsZeroTargets := true
        resolution := .fra .damageEqualSourcePower
        phrase := s!"{host.name} deals damage equal to its power to up to one target creature" }
    return (g.putReflexiveTrigger p (some hostId) effect).finishFraChoice
  | .attachAnyEquipment .., .decline => return g.finishFraChoice
  | .attachAnyEquipment .., _ => throw "Choose Equipment to attach, or decline"
  | .sacrificeLeastPower ids, .objects #[id] =>
    if !ids.contains id then throw "Choose a creature tied for the least power"
    return (g.sacrificeLeastPowerCreature p (some id)).finishFraChoice
  | .sacrificeLeastPower _, _ => throw "Choose a creature tied for the least power"
  | .mayPayPickThen pick next sourceId, .objects ids =>
    let g ← g.payCostPick p sourceId sourceId pick ids
    return (g.applyFra p default next.toResolution #[] (some sourceId)).finishFraChoice
  | .mayPayPickThen .., .decline => return g.finishFraChoice
  | .mayPayPickThen pick .., _ => throw s!"Choose what to {pick.phrase}, or decline"
  | .addManaColors left use, .mode idx =>
    let some c := Color.all[idx]? | throw "Choose white, blue, black, red, or green (0-4)"
    let g := g.modifyPlayer p (fun pl =>
      { pl with manaPool := pl.manaPool.add (.colored c) (fra := some use) })
    let g := g.logMsg s!"{(g.player p).name} adds {ManaType.colored c} ({use.label})"
    if left > 1 then return { g with pending := .fraChoice p (.addManaColors (left - 1) use) }
    return g.finishFraChoice
  | .addManaColors .., _ => throw "Choose a color for the mana"
  | .payLifeOrEnterTapped _ n, .accept =>
    let g ← g.payLifeCost p n
    return g.finishFraChoice
  | .payLifeOrEnterTapped id _, .decline =>
    match g.findObject? id with
    | some o =>
      let g := g.setObject { o with status := { o.status with tapped := true } }
      return (g.logMsg s!"{o.name} enters tapped").finishFraChoice
    | none => return g.finishFraChoice
  | .payLifeOrEnterTapped .., _ => throw "Pay the life (accept), or decline"
  | .mayPayExtort _, .accept =>
    let cost : ManaCost := { symbols := #[.hybrid .white .black] }
    if !(g.player p).manaPool.canPay cost then
      throw s!"{(g.player p).name} cannot pay \{W/B}; add mana first"
    let g ← g.payCost p cost
    return (g.extortDrain p).finishFraChoice
  | .mayPayExtort _, .decline => return (g.logMsg "Extort is not paid").finishFraChoice
  | .mayPayExtort _, _ => throw "Pay {W/B} (accept), or decline"
  | .mayDrawThenDiscard n k, .accept =>
    return g.drawThenBeginDiscard p n (discardRounds := k)
  | .mayDrawThenDiscard .., .decline => return g.finishFraChoice
  | .mayDrawThenDiscard .., _ => throw "Answer accept or decline"
  | .sacrificeNontokenEach rest chosen, .objects #[id] =>
    let some o := g.findObject? id | throw "no such object"
    if !o.isOnBattlefield || !o.isCreature || o.printed.isToken || !o.controlledBy p then
      throw "Choose a nontoken creature you control"
    return (g.continueNontokenSacrifices rest (chosen.push id)).finishFraChoice
  | .sacrificeNontokenEach .., _ => throw "Choose a nontoken creature to sacrifice"
  | .mayCreateTokens kind n, .accept => return (g.createKindTokens p kind n).finishFraChoice
  | .mayCreateTokens .., .decline => return g.finishFraChoice
  | .mayCreateTokens .., _ => throw "Answer accept or decline"
  | .mayBecomeBasePT id pw tw, .accept =>
    match g.findObject? id with
    | some o =>
      if o.isOnBattlefield then
        let g := g.setObject { o with status := { o.status with setBasePT := some (pw, tw) } }
        return (g.logMsg s!"{o.name}'s base power and toughness become {pw}/{tw} until end of turn").finishFraChoice
      else return g.finishFraChoice
    | none => return g.finishFraChoice
  | .mayBecomeBasePT .., .decline => return g.finishFraChoice
  | .mayBecomeBasePT .., _ => throw "Answer accept or decline"
  | .mayRevealToHand looked eligible anyOrder, .objects #[id] =>
    if !eligible.contains id then throw "Choose one of the eligible cards"
    let name := (g.object! id).name
    let (g, _) := g.move id (.hand p) none
    let g := g.logMsg s!"{(g.player p).name} reveals {name} and puts it into their hand"
    let rest := looked.filter (· != id)
    let g :=
      if anyOrder then g.offerBottomAnyOrder p rest
      else g.requestOrderInto rest (.library p)
        s!"{(g.player p).name} puts the rest on the bottom of their library in a random order"
    return g.finishFraChoice
  | .mayRevealToHand looked _ anyOrder, .decline =>
    let g :=
      if anyOrder then g.offerBottomAnyOrder p looked
      else g.requestOrderInto looked (.library p)
        s!"{(g.player p).name} puts the cards on the bottom of their library in a random order"
    return g.finishFraChoice
  | .mayRevealToHand .., _ => throw "Choose a card to reveal, or decline"
  | .nickFuryPut looked eligible, .objects #[id] =>
    if !eligible.contains id then throw "That card can't be put onto the battlefield"
    let rest := looked.filter (· != id)
    let g := g.enterFromNickFury p id
    let newId := g.followMoved id
    let g :=
      match g.findObject? newId with
      | some o =>
        if o.isOnBattlefield && o.printed.otherFace.isSome && !o.status.cantTransform then
          g.beginFraChoice p (.nickFuryMayTransform newId rest)
            s!"{(g.player p).name} may transform {o.name}"
        else g.putRestOnBottomRandom p rest
      | none => g.putRestOnBottomRandom p rest
    return g.finishFraChoice
  | .nickFuryPut looked _, .decline =>
    return (g.putRestOnBottomRandom p looked).finishFraChoice
  | .nickFuryPut .., _ => throw "Put a card onto the battlefield, or decline"
  | .nickFuryMayTransform id rest, .accept =>
    let g := g.applyAbilityEffect p Effect.transform #[] (some id)
    return (g.putRestOnBottomRandom p rest).finishFraChoice
  | .nickFuryMayTransform _ rest, .decline =>
    return (g.putRestOnBottomRandom p rest).finishFraChoice
  | .nickFuryMayTransform .., _ => throw "Transform it (accept), or decline"
  | .orderLibraryBottom ids, .objects ordered =>
    if ordered.size != ids.size || ordered.toList.eraseDups.length != ordered.size ||
        !ordered.all (ids.contains ·) then
      throw "Put every remaining card on the bottom, in the order you choose"
    return (g.moveIdsInOrder ordered (.library p)
      |>.logMsg s!"{(g.player p).name} puts the rest on the bottom of their library in the chosen order").finishFraChoice
  | .orderLibraryBottom ids, .decline =>
    return (g.moveIdsInOrder ids (.library p)
      |>.logMsg s!"{(g.player p).name} puts the rest on the bottom of their library in the chosen order").finishFraChoice
  | .orderLibraryBottom _, _ => throw "Choose the order for the bottom of your library"
  | .mayPayManaForReflexive cost maxTimes kind sourceId, .accept
  | .mayPayManaForReflexive cost maxTimes kind sourceId, .mode _ =>
    let times := match answer with | .mode n => n | _ => 1
    if times == 0 then return g.finishFraChoice
    if times > maxTimes then throw s!"Pay at most {maxTimes} times"
    let total : ManaCost := { symbols := (List.replicate times cost.toList).flatten.toArray }
    if !(g.player p).manaPool.canPay total then
      throw s!"{(g.player p).name} cannot pay {total}; add mana first"
    let g ← g.payCost p total
    let g := g.logMsg s!"{(g.player p).name} pays {total}"
    return (g.applyFra p default (.queueMshReflexive kind times) #[] sourceId).finishFraChoice
  | .mayPayManaForReflexive .., .decline =>
    return (g.logMsg "The cost isn't paid. The reflexive ability doesn't trigger.").finishFraChoice
  | .mayPayManaForReflexive .., _ => throw "Pay (accept, or a number of times), or decline"
  | .mayTapSourceThen next sourceId, .accept =>
    match g.findObject? sourceId with
    | some o =>
      if o.isOnBattlefield && !o.status.tapped then
        let g := g.becomeTapped o
        return (g.applyFra p default next.toResolution #[] (some sourceId)).finishFraChoice
      else throw s!"{o.name} can't be tapped"
    | none => throw "The source is gone"
  | .mayTapSourceThen .., .decline => return g.finishFraChoice
  | .mayTapSourceThen .., _ => throw "Answer accept or decline"
  | .hawkeyeModes left chosen sourceId, .mode idx =>
    if idx > 2 then throw "Choose Net (0), Explosive (1), or Boomerang (2)"
    if chosen.contains idx then throw "That mode was already chosen (CR 700.2)"
    let chosen := chosen.push idx
    if chosen.size < left && chosen.size < 3 then
      return { g with pending := .fraChoice p (.hawkeyeModes left chosen sourceId) }
    return (g.putReflexiveTrigger p sourceId (hawkeyeArrowsEffect chosen)).finishFraChoice
  | .hawkeyeModes _ chosen sourceId, .decline =>
    if chosen.isEmpty then return g.finishFraChoice
    return (g.putReflexiveTrigger p sourceId (hawkeyeArrowsEffect chosen)).finishFraChoice
  | .hawkeyeModes .., _ => throw "Choose a mode, or decline to stop"
  | .discardThenDraw, .objects #[id] =>
    if !(g.player p).hand.contains id then throw "That card is not in your hand"
    return ((g.discardFromHand p id).draw p 1).finishFraChoice
  | .discardThenDraw, _ => throw "Choose a card to discard"
  | .zemoBoastExile abilityId sourceId, .objects ids =>
    if ids.toList.eraseDups.length != ids.size then throw "Choose each card once"
    if !g.canPayZemoBoast p ids then
      throw "Choose black cards from your graveyard with fifteen or more black mana symbols among their mana costs"
    let (g, exiled) := ids.foldl (fun (acc : Game × Array ObjectId) id =>
      let (g, ex) := acc.1.move id .exile none
      (g, acc.2.push ex)) (g, #[])
    let g := g.logMsg s!"{(g.player p).name} exiles {exiled.size} card(s) from their graveyard"
    let g := match g.findObject? abilityId with
      | some ab => g.setObject { ab with boastExiled := exiled }
      | none => g
    let g := match g.findObject? sourceId with
      | some src => g.markBoastUsed src
      | none => g
    let name := ((g.findObject? sourceId).map (·.name)).getD "Baron Helmut Zemo"
    return (g.becomeActivated p name (some sourceId) (some ActivatedAbility.zemoBoastAbility)).finishFraChoice
  | .zemoBoastExile abilityId _, .decline =>
    let g := (g.removeFromZoneList abilityId .stack).ceaseToExist abilityId
    return (g.logMsg s!"{(g.player p).name} doesn't boast").receivePriority p
  | .zemoBoastExile .., _ => throw "Choose the cards to exile, or decline"
  | .mayCastCascade cardId others, .accept =>
    let g := g.castAsPartOfResolution p cardId
    let msg := s!"{(g.player p).name} puts the other exiled cards on the bottom of their library in a random order"
    let g :=
      if g.pending == .none then g.requestOrderInto others (.library p) msg
      else if g.norandom then g.moveIdsInOrder others (.library p) |>.logMsg msg
      else
        let (rng, ordered) := g.rng.shuffle others
        { g with rng := rng }.moveIdsInOrder ordered (.library p) |>.logMsg msg
    return g.finishFraChoice
  | .mayCastCascade cardId others, .decline =>
    return (g.requestOrderInto (others.push cardId) (.library p)
      s!"{(g.player p).name} puts the exiled cards on the bottom of their library in a random order").finishFraChoice
  | .mayCastCascade .., _ => throw "Cast it (accept), or decline"
  | .mayCastGrima cardId others victim, .accept =>
    let g := g.castAsPartOfResolution p cardId
    let landed := g.followMoved cardId
    let cast := (g.findObject? landed).any (·.zone == .stack)
    let uncast :=
      if cast then #[]
      else if (g.findObject? cardId).any (·.zone == .exile) then #[cardId]
      else if (g.findObject? landed).any (·.zone == .exile) then #[landed]
      else #[]
    let pile := others ++ uncast
    let msg :=
      s!"{(g.player victim).name} puts the exiled cards that weren't cast on the bottom of their library in a random order"
    let g :=
      if g.pending == .none then g.requestOrderInto pile (.library victim) msg
      else if g.norandom then g.moveIdsInOrder pile (.library victim) |>.logMsg msg
      else
        let (rng, ordered) := g.rng.shuffle pile
        { g with rng := rng }.moveIdsInOrder ordered (.library victim) |>.logMsg msg
    return g.finishFraChoice
  | .mayCastGrima cardId others victim, .decline =>
    return (g.requestOrderInto (others.push cardId) (.library victim)
      s!"{(g.player victim).name} puts the exiled cards on the bottom of their library in a random order").finishFraChoice
  | .mayCastGrima .., _ => throw "Cast it (accept), or decline"
  | .mayCastCopy copyId, .accept =>
    let g := g.castAsPartOfResolution p copyId
    let landed := g.followMoved copyId
    let onStack :=
      (g.findObject? landed).any (·.zone == .stack) ||
        (g.findObject? copyId).any (·.zone == .stack)
    if onStack then return g.finishFraChoice
    else
      let gone :=
        match g.findObject? copyId with
        | some o => if o.isCopy then (g.ceaseToExist o.id).logMsg s!"The copy of {o.name} ceases to exist" else g
        | none =>
          match g.findObject? landed with
          | some o => if o.isCopy then (g.ceaseToExist o.id).logMsg s!"The copy of {o.name} ceases to exist" else g
          | none => g
      return gone.finishFraChoice
  | .mayCastCopy copyId, .decline =>
    let g :=
      match g.findObject? copyId with
      | some o =>
        (g.ceaseToExist o.id).logMsg s!"The copy of {o.name} ceases to exist"
      | none => g
    return g.finishFraChoice
  | .mayCastCopy _, _ => throw "Cast the copy (accept), or decline"
  | .mayDiscardHandBalin sourceId, .accept =>
    let n := (g.player p).hand.size
    let g := g.mayDiscardHandDrawThatMany p true
    let g :=
      if !g.hasEnduringStory p || n == 0 then g
      else
        match sourceId.bind g.findObject? with
        | some src =>
          if src.isOnBattlefield then
            g.forEachOpponent p (fun g pid =>
              g.dealDamageToPlayer pid (n : Int) (source := some src))
          else g
        | none => g
    return g.finishFraChoice
  | .mayDiscardHandBalin _, .decline =>
    return (g.logMsg s!"{(g.player p).name} does not discard their hand").finishFraChoice
  | .mayDiscardHandBalin _, _ => throw "Discard your hand (accept), or decline"
  | .mayDiscardHandDrawFixed n, .accept =>
    return (g.discardHandThenDraw p n).finishFraChoice
  | .mayDiscardHandDrawFixed _, .decline =>
    return (g.logMsg s!"{(g.player p).name} does not discard their hand").finishFraChoice
  | .mayDiscardHandDrawFixed _, _ => throw "Discard your hand (accept), or decline"
  | .sacrificeDamager ids rest controller, .objects #[id] =>
    if !ids.contains id then throw "Choose a creature that dealt combat damage"
    let some o := g.findObject? id | throw "no such object"
    if !o.isOnBattlefield || !o.isCreature || !o.controlledBy p then
      throw s!"Can't sacrifice {o.name}"
    let g := g.sacrificeToGraveyard o s!"{(g.player p).name} sacrifices {o.name}"
    return (g.beginSacDamagers controller rest).finishFraChoice
  | .sacrificeDamager .., _ => throw "Choose a creature that dealt combat damage"
  | .mayCastInstantSorceryFromHand eligible, .objects #[id] =>
    if !eligible.contains id then throw "That card can't be cast this way"
    let some o := g.findObject? id | throw "no such object"
    if o.zone != .hand p || !o.printed.isInstantOrSorcery then
      throw s!"{o.name} is no longer an instant or sorcery in your hand"
    return (g.castAsPartOfResolution p id).finishFraChoice
  | .mayCastInstantSorceryFromHand _, .decline =>
    return (g.logMsg s!"{(g.player p).name} declines to cast a spell").finishFraChoice
  | .mayCastInstantSorceryFromHand _, _ => throw "Choose a spell to cast, or decline"
  | .mayCastUpToFromExile eligible left, .objects #[id] =>
    if left == 0 || !eligible.contains id then throw "That card can't be cast this way"
    let some o := g.findObject? id | throw "no such object"
    if o.zone != .exile || o.printed.isLand then
      throw s!"{o.name} can't be cast this way"
    let rest := eligible.filter (· != id)
    let g := g.castAsPartOfResolution p id
    let cast := (g.findObject? (g.followMoved id)).any (·.zone == .stack)
    if !cast || left <= 1 || rest.isEmpty then
      return { g with pendingMayCastFromExile := none }.finishFraChoice
    else if g.pending != .none then
      return { g with pendingMayCastFromExile := some (p, rest, left - 1) }.finishFraChoice
    else
      return { g with pending := .fraChoice p (.mayCastUpToFromExile rest (left - 1)) }
  | .mayCastUpToFromExile _ _, .decline =>
    return ({ g with pendingMayCastFromExile := none }
      |>.logMsg s!"{(g.player p).name} declines to cast a spell").finishFraChoice
  | .mayCastUpToFromExile .., _ => throw "Choose a spell to cast, or decline"
  | .hydeMode sourceId, .mode 0 =>
    return (g.applyHydeMode p (some sourceId) 0 #[]).finishFraChoice
  | .hydeMode sourceId, .mode 1 =>
    let ids :=
      ((g.creaturesControlledBy p).filter (·.status.hasCounters)).map (·.id)
    if ids.isEmpty then
      return (g.applyHydeMode p (some sourceId) 1 #[]).finishFraChoice
    else if ids.size == 1 then
      return (g.applyHydeMode p (some sourceId) 1 #[Target.permanent ids[0]!]).finishFraChoice
    else
      return { g with pending := .fraChoice p (.hydeRemoveCounter ids) }
  | .hydeMode _, _ => throw "Choose mode 0 or 1"
  | .hydeRemoveCounter ids, .objects #[id] =>
    if !ids.contains id then throw "Choose a creature with a counter"
    return (g.applyHydeMode p none 1 #[Target.permanent id]).finishFraChoice
  | .hydeRemoveCounter _, _ => throw "Choose a creature with a counter"
  | .widowMayCounter sourceId exiled, .accept =>
    match sourceId.bind g.findObject? with
    | some o =>
      if o.isOnBattlefield then
        return (g.addPlusOnePlusOneTo o 1).finishFraChoice
      else
        return (g.grantWidowCast p exiled).finishFraChoice
    | none =>
      return (g.grantWidowCast p exiled).finishFraChoice
  | .widowMayCounter _ exiled, .decline =>
    return (g.grantWidowCast p exiled).finishFraChoice
  | .widowMayCounter .., _ =>
    throw "Put a +1/+1 counter on Black Widow (accept), or decline"
  | .ultronMayPay artifactId, .accept =>
    let cost := ManaCost.ofGeneric 2
    if !(g.player p).manaPool.canPay cost then
      throw s!"{(g.player p).name} cannot pay {2}; add mana first, or decline"
    let g ← g.payCost p cost
    return (g.copyEnteredArtifact p artifactId).finishFraChoice
  | .ultronMayPay _, .decline =>
    return (g.logMsg s!"{(g.player p).name} doesn't pay {2}").finishFraChoice
  | .ultronMayPay _, _ => throw "Pay {2} (accept), or decline"
  | .visionMode sourceId available, .mode m =>
    if !available.contains m then throw "That mode was already chosen this turn"
    return (g.applyVisionMode p sourceId m).finishFraChoice
  | .visionMode .., _ => throw "Choose a mode that hasn't been chosen this turn"
  | .moonstoneMayExile cardId, .accept =>
    match g.findObject? cardId with
    | some o =>
      if o.zone != .graveyard p then throw s!"{o.name} is no longer in your graveyard"
      let name := o.name
      let (g, newId) := g.move o.id .exile none
      let o := g.object! newId
      return (g.setObject { o with
          playPermission := some { player := p, turnEndsRemaining := 2 } }
        |>.logMsg s!"{name} is exiled. {(g.player p).name} may play it until the end of their next turn").finishFraChoice
    | none => return g.finishFraChoice
  | .moonstoneMayExile _, .decline =>
    return (g.logMsg s!"{(g.player p).name} doesn't exile the discarded card").finishFraChoice
  | .moonstoneMayExile _, _ => throw "Exile the discarded card (accept), or decline"
  | .tricksterLibrary caster id connive, .accept | .tricksterLibrary caster id connive, .decline =>
    let onBottom :=
      match answer with
      | .decline => true
      | _ => false
    let g :=
      match g.findObject? id with
      | some o =>
        if o.isOnBattlefield && o.isCreature then
          g.applyOwnerPutsLibraryThenConnive caster #[Target.permanent id]
            (putOnBottom := onBottom)
        else g.logMsg "The target is no longer legal"
      | none => g.logMsg "The target is no longer legal"
    return (g.conniveTricksterTarget caster connive).finishFraChoice
  | .tricksterLibrary .., _ =>
    throw "Put the creature second from the top (choose top), or on the bottom (choose bottom)"
  | .mayTakeMilled ids life, .objects #[id] =>
    if !ids.contains id then throw "That card wasn't milled"
    let some o := g.findObject? id | throw "no such object"
    if o.zone != .graveyard p then throw s!"{o.name} is no longer in your graveyard"
    let g := g.returnToHand o.id p
    return (g.gainLife p life).finishFraChoice
  | .mayTakeMilled _ life, .decline =>
    return (g.gainLife p life).finishFraChoice
  | .mayTakeMilled .., _ => throw "Put a milled card into your hand, or decline"
  | .mayDrawThenEachOpponentDraws n, .accept =>
    let g := g.draw p n
    let g := g.forEachOpponent p (fun g opp => g.draw opp 1)
    return (g.logMsg s!"{(g.player p).name} draws, so each opponent draws a card").finishFraChoice
  | .mayDrawThenEachOpponentDraws _, .decline =>
    return (g.logMsg s!"{(g.player p).name} doesn't draw").finishFraChoice
  | .mayDrawThenEachOpponentDraws _, _ => throw "Draw (accept), or decline"
  | .mayPutHeroFromHandOrDraw ids, .objects #[id] =>
    if !ids.contains id then throw "That card can't be put onto the battlefield"
    let some o := g.findObject? id | throw "no such object"
    if o.zone != .hand p || !o.printed.isCreature || !g.hasSubtype o "Hero" then
      throw s!"{o.name} is not a Hero creature card in your hand"
    let (g, newId) := g.putOntoBattlefield id p
    return (g.afterPermanentEnters (g.object! newId)).finishFraChoice
  | .mayPutHeroFromHandOrDraw _, .decline =>
    return (g.draw p 1).finishFraChoice
  | .mayPutHeroFromHandOrDraw _, _ => throw "Put a Hero onto the battlefield, or decline to draw"
  | .oddOrEvenDestroy sourceId, .mode m =>
    if m > 1 then throw "Choose 0 for even or 1 for odd"
    return (g.destroyCreaturesByManaParity sourceId (m == 0)).finishFraChoice
  | .oddOrEvenDestroy _, _ => throw "Choose even (0) or odd (1)"
  | .visionQuestZones lib gy x, .accept =>
    return { g with pending := .fraChoice p (.visionQuestPick (lib ++ gy) x true) }
  | .visionQuestZones _ gy x, .decline =>
    if gy.isEmpty then
      return (g.logMsg s!"{(g.player p).name} finds no artifact creature card").finishFraChoice
    else
      return { g with pending := .fraChoice p (.visionQuestPick gy x false) }
  | .visionQuestZones .., _ => throw "Search your library as well (accept), or only your graveyard (decline)"
  | .visionQuestPick ids x shuffle, .objects #[id] =>
    if !ids.contains id then throw "That card can't be found"
    return (g.finishVisionQuest p (some id) x shuffle).finishFraChoice
  | .visionQuestPick _ x shuffle, .decline =>
    return (g.finishVisionQuest p none x shuffle).finishFraChoice
  | .visionQuestPick .., _ => throw "Choose an artifact creature, or decline to find nothing"
  | .kingpinMayPay2Life, .accept =>
    let g ← g.payLifeCost p 2
    return ({ g with assignCombatDamageEqualToughness := some p }
      |>.logMsg "Creatures you control assign combat damage equal to their toughness").finishFraChoice
  | .kingpinMayPay2Life, .decline =>
    return (g.logMsg "The Kingpin's cost wasn't paid").finishFraChoice
  | .kingpinMayPay2Life, _ => throw "Pay 2 life (accept), or decline"
  | .daredevilMayExile sourceId, .accept =>
    return (g.applyDaredevilExile p sourceId).finishFraChoice
  | .daredevilMayExile _, .decline =>
    return (g.logMsg s!"{(g.player p).name} doesn't exile the top card").finishFraChoice
  | .daredevilMayExile _, _ => throw "Exile the top card (accept), or decline"
  | .mayChangeSpellTarget spellId index, .objects #[id] =>
    let g := g.setSpellTargetAt spellId index (Target.permanent id)
    return (g.offerSpellRetarget p spellId (index + 1)).finishFraChoice
  | .mayChangeSpellTarget spellId index, .decline =>
    return (g.offerSpellRetarget p spellId (index + 1)).finishFraChoice
  | .mayChangeSpellTarget .., _ => throw "Choose a new target, or decline to keep it"
  | .sheHulkMayDamage amount target sourceId, .accept =>
    let g := { g with sheHulkDamageUsedThisTurn := true }
    let g :=
      g.withLegalKindTarget p .playerOrCreature #[target]
        (fun g tgt => g.dealDamageToTarget tgt amount) sourceId none
    return (g.logMsg "The Sensational She-Hulk deals damage (only once each turn)").finishFraChoice
  | .sheHulkMayDamage .., .decline =>
    return (g.logMsg s!"{(g.player p).name} declines to have The Sensational She-Hulk deal damage").finishFraChoice
  | .sheHulkMayDamage .., _ => throw "Have She-Hulk deal damage (accept), or decline"
  | .palantirMayDraw controller _, .accept =>
    return (g.draw controller 1).finishFraChoice
  | .palantirMayDraw controller sourceId, .decline =>
    let n :=
      match g.findObject? sourceId with
      | some src => src.status.influence
      | none => 0
    let before := (g.player controller).graveyard.size
    let g := g.mill controller n
    let gy := (g.player controller).graveyard
    let milled := gy.size - before
    let mv :=
      (gy.extract (gy.size - milled) gy.size).foldl (fun acc id =>
        acc + (g.object! id).printed.manaValue) 0
    return (g.loseLife p mv).finishFraChoice
  | .palantirMayDraw .., _ => throw "Have that player draw (accept), or decline"
  | .mayCastFromGraveyard eligible, .objects #[id] =>
    if !eligible.contains id then throw "That card can't be cast this way"
    let some o := g.findObject? id | throw "no such object"
    if o.zone != .graveyard o.owner then throw s!"{o.name} is no longer in the graveyard"
    if !(o.printed.isArtifact || o.printed.isInstantOrSorcery) then
      throw s!"{o.name} is not an artifact, instant, or sorcery"
    if !(g.player p).manaPool.canPay (g.playManaCost o o.printed) then
      throw s!"{o.name} cannot be cast; add mana first, or decline"
    return (g.castAsPartOfResolution p id (withoutManaCost := false)
      (exileInstantSorceryInstead := true)).finishFraChoice
  | .mayCastFromGraveyard _, .decline =>
    return (g.logMsg s!"{(g.player p).name} declines to cast a spell").finishFraChoice
  | .mayCastFromGraveyard _, _ => throw "Choose a card to cast, or decline"
  | .maySearchLibrary eligible count dest after kind, .accept =>
    if eligible.isEmpty then
      let g :=
        (g.logMsg s!"{(g.player p).name} finds no {searchNoun kind}").shuffleSearch p after
      return g.finishFraChoice
    else
      return { g with pending := .fraChoice p (.searchLibrary eligible count dest after kind) }
  | .maySearchLibrary .., .decline =>
    return (g.logMsg s!"{(g.player p).name} doesn't search their library").finishFraChoice
  | .maySearchLibrary .., _ => throw "Search (accept), or decline"
  | .searchLibrary eligible count dest after kind, .objects ids =>
    if ids.size > count then throw s!"Choose at most {count} card(s)"
    if ids.toList.eraseDups.length != ids.size then throw "Choose each card only once"
    if !ids.all (eligible.contains ·) then throw "That card can't be found"
    return (g.finishLibrarySearch p ids dest after kind).finishFraChoice
  | .searchLibrary _ _ dest after kind, .decline =>
    return (g.finishLibrarySearch p #[] dest after kind).finishFraChoice
  | .searchLibrary .., _ => throw "Choose cards from the search, or decline to find nothing"
  | .riddlesSplit looked, .objects ids =>
    if ids.toList.eraseDups.length != ids.size then throw "Choose each card only once"
    if !ids.all (looked.contains ·) then throw "That card isn't among the cards you looked at"
    let faceDown := looked.filter (!ids.contains ·)
    return (g.continueRiddlesSplit p ids faceDown).finishFraChoice
  | .riddlesSplit looked, .decline =>
    return (g.continueRiddlesSplit p #[] looked).finishFraChoice
  | .riddlesSplit _, _ => throw "Choose the face-up pile, or decline for all face-down"
  | .riddlesChoosePile controller faceUp faceDown, .accept =>
    return (g.applyRiddlesPiles controller faceUp faceDown false).finishFraChoice
  | .riddlesChoosePile controller faceUp faceDown, .decline =>
    return (g.applyRiddlesPiles controller faceUp faceDown true).finishFraChoice
  | .riddlesChoosePile .., _ => throw "Choose the face-up pile (accept) or the face-down pile (decline)"
  | .palisadeCreatureType types, .mode idx =>
    let some t := types[idx]? | throw "No such creature type"
    let g := g.logMsg s!"{(g.player p).name} chooses {t}"
    return (g.returnCreaturesNotOfType t).finishFraChoice
  | .palisadeCreatureType types, .name t =>
    if !types.contains t then throw "Choose an existing creature type"
    let g := g.logMsg s!"{(g.player p).name} chooses {t}"
    return (g.returnCreaturesNotOfType t).finishFraChoice
  | .palisadeCreatureType _, _ => throw "Choose a creature type"
  | .worldsPutCreatures eligible rest exiled chosen sourceId, .objects ids =>
    if ids.toList.eraseDups.length != ids.size then throw "Choose each card only once"
    if !ids.all (eligible.contains ·) then throw "That card isn't a creature card in your hand"
    let g := g.offerWorldsCreatures rest.toList exiled (chosen ++ ids) sourceId
    return g.finishFraChoice
  | .worldsPutCreatures _ rest exiled chosen sourceId, .decline =>
    let g := g.offerWorldsCreatures rest.toList exiled chosen sourceId
    return g.finishFraChoice
  | .worldsPutCreatures .., _ => throw "Choose creature cards from your hand, or decline"
  | .revealPutCreatures looked creatures anyNumber, .objects ids =>
    if ids.toList.eraseDups.length != ids.size then throw "Choose each card only once"
    if !ids.all (creatures.contains ·) then throw "That card isn't a revealed creature card"
    if !anyNumber && ids.size > 1 then throw "Choose at most one creature card"
    return (g.finishRevealPutCreatures p looked ids).finishFraChoice
  | .revealPutCreatures looked _ _, .decline =>
    return (g.finishRevealPutCreatures p looked #[]).finishFraChoice
  | .revealPutCreatures .., _ => throw "Choose creature cards to put onto the battlefield, or decline"
  | .chooseCards ids max purpose, .objects chosen =>
    if chosen.size > max then throw s!"Choose at most {max} card(s)"
    if chosen.toList.eraseDups.length != chosen.size then throw "Choose each card only once"
    if !chosen.all (ids.contains ·) then throw "That card can't be chosen"
    match purpose with
    | .toHand true =>
      if !ids.isEmpty && chosen.size != 1 then throw "Choose one card"
    | .amassArmy .. =>
      if chosen.size != 1 then throw "Choose one Army"
    | _ => pure ()
    return (g.finishChooseCards p chosen purpose).finishFraChoice
  | .chooseCards ids _ purpose, .decline =>
    match purpose with
    | .toHand true =>
      if !ids.isEmpty then throw "Choose one card"
    | .amassArmy .. => throw "Choose an Army"
    | _ => pure ()
    return (g.finishChooseCards p #[] purpose).finishFraChoice
  | .chooseCards .., _ => throw "Choose cards, or decline"
  | .blackGatePlayer creature players, .mode idx =>
    let some pid := players[idx]? | throw "No such player"
    return (g.applyBlackGateUnblockable creature pid).finishFraChoice
  | .blackGatePlayer .., _ => throw "Choose a player with the most life"
  | .newTargetsForCopies copies, .objects #[id] =>
    let some c := copies[0]? | return g.finishFraChoice
    let some obj := g.findObject? c | throw "The copy left the stack"
    let t := Target.permanent id
    if !(g.legalTargetsForKind p (g.targetingOf obj).kind (some c)).contains t then
      throw "Illegal target (CR 601.2c)"
    let g := g.setStackEntryTargets c #[t]
    let g := g.queueBecomesTargetTriggers p #[t]
    let g := g.foldPermanentTargets #[t] (fun g o =>
      if o.controller != some p && o.isOnBattlefield then
        (g.wardCostsOn o).foldl (fun g cost =>
          { g with wardQueue := g.wardQueue.push { player := p, spellId := c, cost } }) g
      else g)
    let g := g.logMsg s!"{(g.player p).name} chooses {g.targetLogName t} as the copy's new target"
    let rest := copies.extract 1 copies.size
    if rest.isEmpty then return g.promptNextWard.finishFraChoice
    return { g with pending := .fraChoice p (.newTargetsForCopies rest) }
  | .newTargetsForCopies copies, .decline =>
    let rest := copies.extract 1 copies.size
    if rest.isEmpty then return g.promptNextWard.finishFraChoice
    return { g with pending := .fraChoice p (.newTargetsForCopies rest) }
  | .newTargetsForCopies .., _ => throw "Choose a new target for the copy, or decline to keep it"
  | .entersCreatureType id, .name t =>
    if !isCreatureType t then throw s!"{t} is not a creature type"
    return (g.chooseCreatureTypeAsEnters id t).finishFraChoice
  | .entersCreatureType _, _ => throw "Name a creature type"
  | .entersOddEven id, .mode 0 =>
    return (g.chooseGollumParity id false).finishFraChoice
  | .entersOddEven id, .mode 1 =>
    return (g.chooseGollumParity id true).finishFraChoice
  | .entersOddEven _, _ => throw "Choose even (0) or odd (1)"
  | .mayBeginOnBattlefield ids, .accept =>
    let g ←
      match ids[0]? with
      | some id =>
        match g.findObject? id with
        | some o =>
          if o.zone != .hand o.owner then pure g
          else
            let name := o.name
            let (g, newId) := g.move id .battlefield (some o.owner)
            let g := g.logMsg s!"{name} begins the game on the battlefield"
            if g.pending != .none then pure g
            else pure (g.afterPermanentEnters (g.object! newId))
        | none => pure g
      | none => pure g
    if g.pending != .none then return g
    return (g.continueOpeningBegin (ids.extract 1 ids.size)).finishFraChoice
  | .mayBeginOnBattlefield ids, .decline =>
    let g :=
      match ids[0]? with
      | some id =>
        match g.findObject? id with
        | some o => g.logMsg s!"{(g.player o.owner).name} leaves {o.name} in their hand"
        | none => g
      | none => g
    return (g.continueOpeningBegin (ids.extract 1 ids.size)).finishFraChoice
  | .mayBeginOnBattlefield _, _ =>
    throw "Begin the game with it on the battlefield (accept), or decline"


/-- A legal default answer to `choice` for `p`: the first card or mode,
accepting only Sphinx's Approach and declining other optional actions. -/
def defaultFraAction (g : Game) (p : PlayerId) (choice : FraChoice) : Action :=
  match choice with
  | .discardFromRevealedHand victim permanentOnly =>
    .choosePermanents ((g.revealedHandChoices victim permanentOnly).extract 0 1)
  | .mayWheel .. => .decline
  | .maySacrificePlaneswalker => .decline
  | .topOrBottomDamage .. => .decline
  | .sphinxsApproach _ => .accept
  | .extrapolateReveal =>
    let picks := (g.outsideCards p).foldl (fun (acc : Array GameObject) o =>
      if acc.size < 2 && !acc.any (·.name == o.name) then acc.push o else acc) #[]
    .choosePermanents (picks.map (·.id))
  | .extrapolatePick _ ids => .choosePermanents (ids.extract 0 1)
  | .mayPutMilledPermanent ids _ => .choosePermanents (ids.extract 0 1)
  | .mayThen .. => .accept
  | .mayPayThen n .. =>
    if (g.player p).manaPool.canPay (ManaCost.ofGeneric n) then .accept else .decline
  | .mayDiscardThen .. => .decline
  | .discardThen .. => .choosePermanents ((g.player p).hand.extract 0 1)
  | .discardThenStun n _ => .choosePermanents ((g.player p).hand.extract 0 n)
  | .maySacrificeThen .. => .decline
  | .mayMovePlusOne _ => .decline
  | .exileFromRevealedHand victim _ =>
    .choosePermanents ((g.revealedHandChoices victim false).extract 0 1)
  | .castCopiesFree .. => .decline
  | .allianceMode _ available =>
    match available[0]? with
    | some m => .chooseMode m
    | none => .decline
  | .gollumMode _ available =>
    match available[0]? with
    | some m => .chooseMode m
    | none => .decline
  | .triggerModes objId _ chosen =>
    match g.findObject? objId with
    | none => .decline
    | some obj =>
      let modes := g.triggerModesOf obj
      match (List.range modes.size).find? (fun i =>
          !chosen.contains i && modes[i]?.any (g.triggerModeChoosable p obj)) with
      | some i => .chooseMode i
      | none => .decline
  | .chooseKeyword .. => .chooseMode 0
  | .chooseColor _ => .chooseMode 0
  | .sacrificeCreatureEach .. =>
    .choosePermanents (((g.creaturesControlledBy p).map (·.id)).extract 0 1)
  | .discardTwo .. => .choosePermanents ((g.player p).hand.extract 0 2)
  | .mayMoveAllCounters .. => .accept
  | .crew _ vehicleId n =>
    let cands := ((g.creaturesControlledBy p).filter (fun c => c.id != vehicleId && !c.status.tapped)).qsort
      (fun a b => g.power a > g.power b)
    let (picked, _) := cands.foldl (fun (acc : Array ObjectId × Nat) c =>
      if acc.2 ≥ n then acc else (acc.1.push c.id, acc.2 + (g.power c).toNat)) (#[], 0)
    .choosePermanents picked
  | .costPicks sourceId picks _ =>
    match picks[0]? with
    | some pick =>
      .choosePermanents ((g.costPickCandidates p sourceId pick).extract 0 pick.count)
    | none => .decline
  | .mayPayPickThen .. => .decline
  | .chooseCreatureType _ => .chooseMode 0
  | .maySacrificeAnotherCreatureForPower _ => .decline
  | .maySacrificeAnotherForDrawTreasure _ => .decline
  | .mayPaySymbolsThen symbols .. =>
    if (g.player p).manaPool.canPay { symbols := symbols } then .accept else .decline
  | .attachAnyEquipment _ eligible => .choosePermanents eligible
  | .sacrificeLeastPower ids => .choosePermanents (ids.extract 0 1)
  | .addManaColors .. => .chooseMode 0
  | .payLifeOrEnterTapped _ n => if (g.player p).life > (n : Int) then .accept else .decline
  | .mayPayExtort _ =>
    if (g.player p).manaPool.canPay { symbols := #[.hybrid .white .black] } then .accept else .decline
  | .mayDrawThenDiscard .. => .accept
  | .mayCreateTokens .. => .accept
  | .mayBecomeBasePT .. => .accept
  | .mayRevealToHand _ eligible _ =>
    if eligible.isEmpty then .decline else .choosePermanents (eligible.extract 0 1)
  | .nickFuryPut _ _ => .decline
  | .nickFuryMayTransform _ _ => .decline
  | .orderLibraryBottom ids => .choosePermanents ids
  | .chooseCards ids max purpose =>
    match purpose with
    | .amassArmy .. =>
      let best :=
        ids.foldl (fun best id =>
          match best, g.findObject? id with
          | none, _ => some id
          | some b, some o =>
            match g.findObject? b with
            | some prev => if o.timestamp ≥ prev.timestamp then some id else some b
            | none => some id
          | some b, none => some b) none
      match best with
      | some id => .choosePermanents #[id]
      | none => .decline
    | .toHand true =>
      if ids.isEmpty then .decline else .choosePermanents (ids.extract 0 1)
    | .toHand false => .choosePermanents (ids.extract 0 max)
    | .creaturesToBattlefield | .landsTappedGainLife _ => .choosePermanents ids
    | .keepDestroyRest =>
      let yours := ids.filter (fun id => (g.findObject? id).any (·.controlledBy p))
      let pick := if yours.isEmpty then ids else yours
      .choosePermanents (pick.extract 0 max)
  | .blackGatePlayer _ _ => .chooseMode 0
  | .sacrificeNontokenEach .. =>
    .choosePermanents (((g.creaturesControlledBy p).filter (!·.printed.isToken)).map (·.id) |>.extract 0 1)
  | .mayPayManaForReflexive cost _ _ _ =>
    if (g.player p).manaPool.canPay { symbols := cost } then .accept else .decline
  | .mayTapSourceThen .. => .accept
  | .hawkeyeModes _ chosen _ =>
    match [1, 0, 2].find? (!chosen.contains ·) with
    | some m => if m == 0 && (g.legalTargetsForKind p .creature none).isEmpty then .decline
      else .chooseMode m
    | none => .decline
  | .discardThenDraw => .choosePermanents ((g.player p).hand.extract 0 1)
  | .mayCastCascade .. => .accept
  | .mayCastGrima .. => .decline
  | .palantirMayDraw .. => .decline
  | .mayCastCopy _ => .decline
  | .mayDiscardHandBalin _ => .decline
  | .mayDiscardHandDrawFixed _ => .decline
  | .sacrificeDamager ids .. => .choosePermanents (ids.extract 0 1)
  | .mayCastInstantSorceryFromHand _ => .decline
  | .mayCastUpToFromExile _ _ => .decline
  | .hydeMode _ => .chooseMode 0
  | .hydeRemoveCounter ids => .choosePermanents (ids.extract 0 1)
  | .sheHulkMayDamage .. => .decline
  | .widowMayCounter .. => .decline
  | .ultronMayPay _ => .decline
  | .visionMode _ available =>
    match available[0]? with
    | some m => .chooseMode m
    | none => .decline
  | .moonstoneMayExile _ => .decline
  | .tricksterLibrary .. => .chooseTop
  | .mayTakeMilled _ _ => .decline
  | .mayDrawThenEachOpponentDraws _ => .decline
  | .mayPutHeroFromHandOrDraw _ => .decline
  | .oddOrEvenDestroy _ => .chooseMode 0
  | .visionQuestZones _ _ _ => .accept
  | .visionQuestPick ids _ _ =>
    match ids[0]? with
    | some id => .choosePermanents #[id]
    | none => .decline
  | .kingpinMayPay2Life => .decline
  | .daredevilMayExile _ => .decline
  | .mayChangeSpellTarget .. => .decline
  | .mayCastFromGraveyard eligible =>
    match eligible.find? (fun id =>
      (g.findObject? id).any (fun o =>
        (g.player p).manaPool.canPay (g.playManaCost o o.printed))) with
    | some id => .cast id
    | none => .decline
  | .maySearchLibrary eligible .. =>
    if eligible.isEmpty then .decline else .accept
  | .searchLibrary eligible count .. =>
    if eligible.isEmpty then .decline else .choosePermanents (eligible.extract 0 count)
  | .newTargetsForCopies _ => .decline
  | .riddlesSplit looked => .choosePermanents looked
  | .riddlesChoosePile .. => .accept
  | .palisadeCreatureType _ => .chooseMode 0
  | .worldsPutCreatures .. => .decline
  | .revealPutCreatures .. => .decline
  | .zemoBoastExile .. =>
    .choosePermanents ((g.player p).graveyard.filter (fun id =>
      (g.findObject? id).any (·.printed.colors.contains .black)))
  | .chooseCardName _ =>
    -- Name a nonland card an opponent owns, else any nonland card.
    let opp := g.objects.find? (fun o => o.owner != p && !o.printed.isLand)
    let any := g.knownCardFaces.find? (fun c => !c.isLand)
    .chooseName ((opp.map (·.name)).getD ((any.map (·.name)).getD ""))
  | .entersCreatureType _ =>
    let yours :=
      (g.permanentsOf p).foldl (fun acc o =>
        o.subtypes.foldl (fun acc s =>
          if isCreatureType s && !acc.contains s then acc.push s else acc) acc) #[]
    .chooseName (yours[0]?.getD "Human")
  | .entersOddEven _ => .chooseMode 0
  | .mayBeginOnBattlefield _ => .decline

end Game
end Mtg.Engine
