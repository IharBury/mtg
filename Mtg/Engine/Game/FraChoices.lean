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
  let .fraChoice q (.castCopiesFree ids budget) := g.pending | throw "No copy may be cast now"
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
  let g := { g with pending := .none, pendingFreeCopies := some (p, rest, budget - mv) }
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
  | .castCopiesFree ids _, .decline =>
    let g := ids.foldl (fun g id =>
      if (g.findObject? id).any (·.zone == .exile) then g.ceaseToExist id else g) g
    return { g with pendingFreeCopies := none }.finishFraChoice
  | .castCopiesFree .., _ => throw "Cast a copy, or decline"
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
  | .addManaColors .. => .chooseMode 0
  | .payLifeOrEnterTapped _ n => if (g.player p).life > (n : Int) then .accept else .decline
  | .mayPayExtort _ =>
    if (g.player p).manaPool.canPay { symbols := #[.hybrid .white .black] } then .accept else .decline
  | .mayPayManaForReflexive cost _ _ _ =>
    if (g.player p).manaPool.canPay { symbols := cost } then .accept else .decline
  | .mayTapSourceThen .. => .accept
  | .hawkeyeModes _ chosen _ =>
    match [1, 0, 2].find? (!chosen.contains ·) with
    | some m => if m == 0 && (g.legalTargetsForKind p .creature none).isEmpty then .decline
      else .chooseMode m
    | none => .decline
  | .discardThenDraw => .choosePermanents ((g.player p).hand.extract 0 1)
  | .chooseCardName _ =>
    -- Name a nonland card an opponent owns, else any nonland card.
    let opp := g.objects.find? (fun o => o.owner != p && !o.printed.isLand)
    let any := g.knownCardFaces.find? (fun c => !c.isLand)
    .chooseName ((opp.map (·.name)).getD ((any.map (·.name)).getD ""))

end Game
end Mtg.Engine
